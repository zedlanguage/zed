//! A message built in a fixed buffer, for code that may not allocate: the handlers of a limit's
//! signals (limits.rs, stack.rs) and the run's close of standard output (close.rs). In a module
//! of its own so that limits.rs, which calls close.rs at a stop, and close.rs, which builds its
//! message here, do not import each other (tests/steps/s_01f_import_graph).

/// A message built in a fixed buffer, for a handler that may not allocate; text past its end
/// is dropped.
pub(crate) struct Line {
    bytes: [u8; 512],
    len: usize,
}

impl Line {
    /// An empty line.
    pub(crate) const fn new() -> Line {
        Line {
            bytes: [0; 512],
            len: 0,
        }
    }

    /// The bytes written.
    pub(crate) fn bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl std::fmt::Write for Line {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        let n = s.len().min(self.bytes.len() - self.len);
        self.bytes[self.len..self.len + n].copy_from_slice(&s.as_bytes()[..n]);
        self.len += n;
        Ok(())
    }
}
