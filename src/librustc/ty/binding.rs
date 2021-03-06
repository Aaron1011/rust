use crate::hir::BindingAnnotation::*;
use crate::hir::BindingAnnotation;
use crate::hir::Mutability;

#[derive(Clone, PartialEq, RustcEncodable, RustcDecodable, Debug, Copy, HashStable)]
pub enum BindingMode {
    BindByReference(Mutability),
    BindByValue(Mutability),
}

CloneTypeFoldableAndLiftImpls! { BindingMode, }

impl BindingMode {
    pub fn convert(ba: BindingAnnotation) -> BindingMode {
        match ba {
            Unannotated => BindingMode::BindByValue(Mutability::Not),
            Mutable => BindingMode::BindByValue(Mutability::Mut),
            Ref => BindingMode::BindByReference(Mutability::Not),
            RefMut => BindingMode::BindByReference(Mutability::Mut),
        }
    }
}
