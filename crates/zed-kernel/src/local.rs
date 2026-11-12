//! Reading a thread-local in line with the code that reads it.

use std::thread::{AccessError, LocalKey};

/// `key.with(f)`, compiled into its caller. std marks `LocalKey::try_with` inline but not
/// `LocalKey::with`, so each instance of `with` is compiled in one of the crate's code units
/// and called from the others, with `f` inside it: a call per read of a hot thread-local
/// (KERNEL-tls-inline). A read after the thread-local was dropped panics as `with` does.
#[inline]
pub(crate) fn with<T: 'static, R>(key: &'static LocalKey<T>, f: impl FnOnce(&T) -> R) -> R {
    match key.try_with(f) {
        Ok(r) => r,
        Err(e) => gone(e),
    }
}

#[cold]
#[inline(never)]
fn gone(e: AccessError) -> ! {
    panic!("cannot access a Thread Local Storage value during or after destruction: {e:?}")
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::sync::Mutex;

    thread_local! {
        static COUNT: Cell<u32> = const { Cell::new(0) };
        static LAZY: Vec<u32> = vec![1, 2, 3];
        static DROPPED: Reader = const { Reader };
    }

    /// The panic messages of the reads made while `DROPPED` is being dropped: by
    /// `LocalKey::with`, then by `super::with`.
    static MESSAGES: Mutex<Vec<String>> = Mutex::new(Vec::new());

    struct Reader;

    impl Drop for Reader {
        fn drop(&mut self) {
            let message = |e: Box<dyn std::any::Any + Send>| {
                e.downcast::<String>()
                    .map_or_else(|_| String::new(), |s| *s)
            };
            let read = |by_std: bool| {
                std::panic::catch_unwind(|| {
                    if by_std {
                        DROPPED.with(|_| ());
                    } else {
                        super::with(&DROPPED, |_| ());
                    }
                })
                .map_or_else(message, |()| "no panic".to_string())
            };
            let found = [read(true), read(false)];
            MESSAGES
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .extend(found);
        }
    }

    #[test]
    fn a_read_gives_the_value_and_keeps_writes() {
        super::with(&COUNT, |c| c.set(c.get() + 2));
        assert_eq!(super::with(&COUNT, Cell::get), 2);
        // A thread-local made on first use is made by the first read.
        assert_eq!(super::with(&LAZY, |v| v.iter().sum::<u32>()), 6);
    }

    #[test]
    fn a_read_while_the_value_is_dropped_panics_as_with_does() {
        std::thread::spawn(|| DROPPED.with(|_| ()))
            .join()
            .expect("the thread ends without a panic");
        let found = MESSAGES
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        assert_eq!(found.len(), 2, "{found:?}");
        assert!(
            found[0].starts_with("cannot access a Thread Local Storage value"),
            "{found:?}"
        );
        assert_eq!(found[0], found[1]);
    }
}
