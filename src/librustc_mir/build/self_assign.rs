// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use build::{BlockAnd, BlockAndExtension, Builder, CFG};
use hair::LintLevel;
use rustc::middle::region;
use rustc::ty::{Ty, TyCtxt};
use rustc::hir;
use rustc::hir::def_id::LOCAL_CRATE;
use rustc::mir::*;
use syntax_pos::{Span};
use rustc_data_structures::indexed_vec::Idx;
use rustc_data_structures::fx::FxHashSet;

impl<'a, 'gcx, 'tcx> Builder<'a, 'gcx, 'tcx> {


    pub fn in_self_assign<F, R>(&mut self,
                                lhs: Place<'tcx>,
                                f: F)
                                -> (R, CaptureData<'tcx>)
        where F: FnOnce(&mut Builder<'a, 'gcx, 'tcx>) -> R
    {

        self.cfg.start_capture(lhs.clone());
        let result = f(self);
        let captures = self.cfg.end_capture(&lhs);

        (result, captures)
    }

    pub fn start_self_assign(&mut self, lhs: Place<'tcx>) {
        self.cfg.start_capture(lhs.clone())
    }

    pub fn stop_self_assign(&mut self, lhs: &Place<'tcx>) -> CaptureData<'tcx> {
        self.cfg.end_capture(lhs)
    }

}

impl<'tcx> CFG<'tcx> {


    fn start_capture(&mut self, orig_place: Place<'tcx>) {
        self.capture_stack.push(CaptureData::new(orig_place));
    }

    fn end_capture(&mut self, orig_place: &Place<'tcx>) -> CaptureData<'tcx> {
        let data = self.capture_stack.pop().unwrap();
        assert!(&data.orig_place == orig_place);

        data
    }

}

pub struct CaptureData<'tcx> {
    pub orig_place: Place<'tcx>,
    //pub reborrows: FxHashSet<Location>
}

impl<'tcx> CaptureData<'tcx> {

    fn new(orig_place: Place<'tcx>) -> CaptureData<'tcx> {
        CaptureData {
            orig_place
            //reborrows: FxHashSet()
        }
    }

}
