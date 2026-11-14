//! Step L2.8d: the build constant. `build.target` names the target a build is for and
//! `build.options.<name>` whether it turns the option `<name>` on; the options are those the
//! manifest's entry `options` declares, and `--option <name>` turns one on.

mod bench;
mod branches;
mod combinations;
mod command;
mod reads;
mod scaling;
#[cfg(target_os = "linux")]
mod staged;
#[cfg(target_os = "linux")]
mod test_staged;

pub(crate) use branches::lowered;
