//! Step L2.1: the parser of the L2 forms. Structs with `import` fields and defaults, record
//! displays and `return` of one, the separator and body position telling a block from a
//! display, `with` updates, `T.m` methods and `this`, struct destructuring, the
//! tuple-destructuring parameter, and `type` declarations with the record and applied type
//! forms. Each form builds and formats; name resolution refuses it, naming the later step that
//! gives it meaning.

mod bench;
mod blocks;
mod body_positions;
mod formatting;
mod later;
mod methods;
mod name_values;
mod patterns;
mod scaling;
mod structs;
mod types;
mod updates;

use zed_tests::step_helpers::l02_01_parser_structs::{check, fmt, sx};
