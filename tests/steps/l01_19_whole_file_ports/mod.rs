//! Step L1.19: whole-file ports. `main`'s header names the ports; each input is read once,
//! whole, each output written once when the wave ends, and a record of the inputs replays
//! the wave without the world.

mod bench;
mod blocking;
mod blocking_word;
mod combinations;
mod files;
mod line_ends;
mod lines;
mod main_args;
mod nonblocking;
mod outside;
mod ports;
mod replay;
mod scaling;
mod sharing;
mod signals;
mod writes;

pub(crate) use zed_tests::step_helpers::l01_19_whole_file_ports::{dir, run, zedc};
