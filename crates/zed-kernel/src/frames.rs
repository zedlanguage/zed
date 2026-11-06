//! Recursion on an explicit stack on the heap. A recursive analysis is written as `async`
//! functions, which the compiler turns into state machines; a call that may recurse returns a
//! [`Deep`], which, when awaited, hands the callee's machine to the loop in [`Stack::run`] and
//! suspends the caller. The loop keeps the suspended machines in a `Vec` and runs the top one, so
//! the thread's stack holds only the code between two such calls, whatever the depth, and the
//! depth is limited by the machine's memory alone. Nothing here depends on the depth.
//!
//! This is not asynchronous code: nothing waits, and one machine runs at a time, in the order
//! plain recursion would run them, so what a machine does between two calls happens in the same
//! order too. `async` is used because it writes each frame's resume points and saved locals,
//! which a hand-written machine would list by hand at each recursive call.
//!
//! The emptiness search of `types::empty` and zedc's preimage analysis (`store::preimage`) run
//! on it.

use std::cell::Cell;
use std::mem::ManuallyDrop;
use std::pin::Pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

/// A suspended call, whose answer goes where its [`Deep`] will read it.
type Frame<'m> = Pin<Box<dyn Future<Output = ()> + 'm>>;

/// The stack's link with the calls running on it.
pub struct Stack<'m> {
    /// The frame a suspended call asks to run next, from the poll that asks until the loop in
    /// [`Stack::run`] takes it. `ManuallyDrop` gives the type no destructor, so that a `Stack`
    /// may be borrowed for the `'m` its own frames hold: the slot is empty when the loop ends,
    /// and a frame left here by a panic is only not dropped.
    next: Cell<ManuallyDrop<Option<Frame<'m>>>>,
}

impl Default for Stack<'_> {
    fn default() -> Self {
        Stack {
            next: Cell::new(ManuallyDrop::new(None)),
        }
    }
}

/// A frame that writes the answer of the call `body()` makes to `out`. The frame takes the
/// function that makes the call rather than the call itself: an `async` block keeps a future it
/// captures apart from the same future once awaited, so a captured call made the frame twice
/// its callee's size (2,272 bytes for `back_in`'s 1,120).
fn frame<'m, V: 'm, F: Future<Output = V> + 'm>(
    body: impl FnOnce() -> F + 'm,
    out: &Rc<Cell<Option<V>>>,
) -> Frame<'m> {
    let out = out.clone();
    Box::pin(async move { out.set(Some(body().await)) })
}

impl<'m> Stack<'m> {
    /// A call whose answer is already known: awaiting it costs no frame.
    pub fn ready<V>(v: V) -> Deep<'m, V> {
        Deep {
            call: Err(Some(v)),
            out: None,
        }
    }

    /// The call `body()` makes, on a frame of its own, whatever calls it makes in turn.
    pub fn call<V: 'm, F: Future<Output = V> + 'm>(
        &'m self,
        body: impl FnOnce() -> F + 'm,
    ) -> Deep<'m, V> {
        let out = Rc::new(Cell::new(None));
        let f = frame(body, &out);
        Deep {
            call: Ok((self, Some(f))),
            out: Some(out),
        }
    }

    /// Runs `root` and the calls it makes to the end, each suspended caller on a `Vec`.
    pub fn run<V: 'm>(&'m self, root: impl Future<Output = V> + 'm) -> V {
        let out = Rc::new(Cell::new(None));
        let mut frames = vec![frame(|| root, &out)];
        let mut cx = Context::from_waker(Waker::noop());
        while let Some(top) = frames.last_mut() {
            match top.as_mut().poll(&mut cx) {
                Poll::Ready(()) => drop(frames.pop()),
                Poll::Pending => {
                    let next = ManuallyDrop::into_inner(self.next.take());
                    frames.push(next.expect("a frame suspends only in a Deep, which sets the next"))
                }
            }
        }
        out.take().expect("the root frame ran to its end")
    }
}

/// A call that may run on a frame of its own. It must be awaited where it is made, so that the
/// callee runs where the plain call would have.
pub struct Deep<'m, V> {
    /// The stack and the frame, until the frame is handed over; or the answer known at the call.
    call: Result<(&'m Stack<'m>, Option<Frame<'m>>), Option<V>>,
    /// Where the frame leaves its answer.
    out: Option<Rc<Cell<Option<V>>>>,
}

impl<V: Unpin> Future for Deep<'_, V> {
    type Output = V;

    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<V> {
        let this = self.get_mut();
        match &mut this.call {
            Err(v) => Poll::Ready(v.take().expect("an answer is read once")),
            Ok((stack, f)) => match f.take() {
                Some(f) => {
                    stack.next.set(ManuallyDrop::new(Some(f)));
                    Poll::Pending
                }
                None => {
                    let out = this.out.take().expect("an answer is read once");
                    Poll::Ready(
                        out.take()
                            .expect("a frame runs to its end before its caller"),
                    )
                }
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What the calls saw, in order.
    struct Trace<'m> {
        stack: Stack<'m>,
        seen: Cell<u64>,
    }

    impl<'m> Trace<'m> {
        /// `1 + ... + n`, each call on its own frame, numbering its work on the way in and out.
        fn sum(&'m self, n: u64) -> Deep<'m, u64> {
            if n == 0 {
                return Stack::ready(0);
            }
            self.stack.call(move || async move {
                self.seen
                    .set(self.seen.get().wrapping_mul(31).wrapping_add(n));
                let below = self.sum(n - 1).await;
                self.seen
                    .set(self.seen.get().wrapping_mul(31).wrapping_add(n));
                below + n
            })
        }
    }

    fn on_small_stack(f: impl FnOnce() + Send + 'static) {
        (std::thread::Builder::new().stack_size(64 << 10).spawn(f))
            .expect("a test thread")
            .join()
            .expect("the test passes on a 64 KiB stack");
    }

    /// The same numbers as [`Trace::sum`] on the thread's stack.
    fn plain(n: u64, seen: &mut u64) -> u64 {
        if n == 0 {
            return 0;
        }
        *seen = seen.wrapping_mul(31).wrapping_add(n);
        let below = plain(n - 1, seen);
        *seen = seen.wrapping_mul(31).wrapping_add(n);
        below + n
    }

    #[test]
    fn calls_run_in_the_order_of_plain_recursion() {
        let t = Trace {
            stack: Stack::default(),
            seen: Cell::new(0),
        };
        let mut seen = 0;
        assert_eq!(t.stack.run(t.sum(100)), plain(100, &mut seen));
        assert_eq!(t.seen.get(), seen);
    }

    #[test]
    fn a_million_calls_deep_need_no_more_of_the_threads_stack() {
        on_small_stack(|| {
            let t = Trace {
                stack: Stack::default(),
                seen: Cell::new(0),
            };
            assert_eq!(t.stack.run(t.sum(1_000_000)), 500_000_500_000);
        });
    }

    /// A call that keeps 4 KiB of its own across a call it makes.
    async fn wide(t: &Trace<'_>) -> u64 {
        let keep = [t.seen.get(); 512];
        Stack::<'_>::ready(0u64).await;
        keep.iter().sum()
    }

    #[test]
    fn a_frame_holds_its_call_once() {
        let t = Trace {
            stack: Stack::default(),
            seen: Cell::new(0),
        };
        let callee = size_of_val(&wide(&t));
        let f = frame(|| wide(&t), &Rc::new(Cell::new(None)));
        // The frame holds the call and the cell of its answer; a frame that kept the call
        // apart from the call awaited was twice the size.
        assert!(
            size_of_val(&*f) < callee + 64,
            "{} for {callee}",
            size_of_val(&*f)
        );
    }

    #[test]
    fn a_known_answer_needs_no_frame() {
        let t = Trace {
            stack: Stack::default(),
            seen: Cell::new(0),
        };
        assert_eq!(t.stack.run(t.sum(0)), 0);
        assert_eq!(t.seen.get(), 0);
    }
}
