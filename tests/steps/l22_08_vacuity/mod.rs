//! Step L22.8: the vacuity warning and the trivial-model report (DESIGN.md sec:theories item 3).
//!
//! Until L22 parses law members, this folder holds the study of plan row TRIVIAL-models-study:
//! the report as a prototype over a small term language (`trivial`), checked against brute force
//! (`brute`) on the theories of sec:theories (`corpus`) and on random small theories, at the
//! rule of low complexity (`scaling`), and on the shapes where deciding a model is NP-complete
//! (`hardness`).

mod bench;
mod brute;
mod corpus;
mod hardness;
mod scaling;
mod trivial;
