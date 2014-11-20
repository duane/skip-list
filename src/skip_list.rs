// the "link" crate attribute is currently required for rustdoc, but normally
// isn't needed.
#![crate_type = "lib"]
#![feature(box_syntax)]
#![feature(core)]
#![allow(dead_code)]

//! A couple of things built on skip lists.

/// The list module.
extern crate rand;
pub mod list;
