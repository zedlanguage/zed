//! Step L1.1: source loading. A file is UTF-8 in NFC, or it is rejected with a span; line
//! endings normalize to `\n`.

mod accepted;
mod places;
mod rejected;
