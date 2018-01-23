// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module contains the "cleaned" pieces of the AST, and the functions
//! that clean them.

pub use self::Type::*;
pub use self::Mutability::*;
pub use self::ItemEnum::*;
pub use self::TyParamBound::*;
pub use self::SelfTy::*;
pub use self::FunctionRetTy::*;
pub use self::Visibility::*;

use syntax::abi::Abi;
use syntax::ast;
use syntax::attr;
use syntax::codemap::Spanned;
use syntax::ptr::P;
use syntax::symbol::keywords;
use syntax_pos::{self, DUMMY_SP, Pos, FileName};

use rustc::middle::const_val::ConstVal;
use rustc::middle::privacy::AccessLevels;
use rustc::middle::resolve_lifetime as rl;
use rustc::middle::lang_items;
use rustc::hir::{self, HirVec};
use rustc::hir::def::{self, Def, CtorKind};
use rustc::hir::def_id::{CrateNum, DefId, DefIndex, CRATE_DEF_INDEX, LOCAL_CRATE, DefIndexAddressSpace};
use rustc::traits::{self, Reveal};
use rustc::ty::subst::{Substs, Kind};
use rustc::ty::{self, TyCtxt, Predicate, TraitPredicate, Region, RegionVid, Ty, AdtKind, ToPredicate};
use rustc::ty::subst::Subst;
use rustc::middle::stability;
use rustc::util::nodemap::{FxHashMap, FxHashSet};
use rustc_typeck::hir_ty_to_ty;
use rustc::infer::{InferCtxt, RegionObligation};
use rustc::infer::region_constraints::{RegionConstraintData, Constraint};
use rustc::traits::*;
use std::collections::hash_map::Entry;
use std::collections::VecDeque;
use std::iter;
use std::fmt;

use rustc_const_math::ConstInt;
use std::default::Default;
use std::{mem, slice, vec};
use std::iter::{FromIterator, once};
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;
use std::u32;

use core::{self, DocContext};
use doctree;
use visit_ast;
use html::item_type::ItemType;

pub mod inline;
pub mod cfg;
mod simplify;

use self::cfg::Cfg;

thread_local!(static MAX_DEF_ID: RefCell<FxHashMap<CrateNum, DefId>> = RefCell::new(FxHashMap()));

const FN_OUTPUT_NAME: &'static str = "Output";

// extract the stability index for a node from tcx, if possible
fn get_stability(cx: &DocContext, def_id: DefId) -> Option<Stability> {
    cx.tcx.lookup_stability(def_id).clean(cx)
}

fn get_deprecation(cx: &DocContext, def_id: DefId) -> Option<Deprecation> {
    cx.tcx.lookup_deprecation(def_id).clean(cx)
}

pub trait Clean<T> {
    fn clean(&self, cx: &DocContext) -> T;
}

impl<T: Clean<U>, U> Clean<Vec<U>> for [T] {
    fn clean(&self, cx: &DocContext) -> Vec<U> {
        self.iter().map(|x| x.clean(cx)).collect()
    }
}

impl<T: Clean<U>, U> Clean<U> for P<T> {
    fn clean(&self, cx: &DocContext) -> U {
        (**self).clean(cx)
    }
}

impl<T: Clean<U>, U> Clean<U> for Rc<T> {
    fn clean(&self, cx: &DocContext) -> U {
        (**self).clean(cx)
    }
}

impl<T: Clean<U>, U> Clean<Option<U>> for Option<T> {
    fn clean(&self, cx: &DocContext) -> Option<U> {
        self.as_ref().map(|v| v.clean(cx))
    }
}

impl<T, U> Clean<U> for ty::Binder<T> where T: Clean<U> {
    fn clean(&self, cx: &DocContext) -> U {
        self.0.clean(cx)
    }
}

impl<T: Clean<U>, U> Clean<Vec<U>> for P<[T]> {
    fn clean(&self, cx: &DocContext) -> Vec<U> {
        self.iter().map(|x| x.clean(cx)).collect()
    }
}

#[derive(Clone, Debug)]
pub struct Crate {
    pub name: String,
    pub version: Option<String>,
    pub src: FileName,
    pub module: Option<Item>,
    pub externs: Vec<(CrateNum, ExternalCrate)>,
    pub primitives: Vec<(DefId, PrimitiveType, Attributes)>,
    pub access_levels: Arc<AccessLevels<DefId>>,
    // These are later on moved into `CACHEKEY`, leaving the map empty.
    // Only here so that they can be filtered through the rustdoc passes.
    pub external_traits: FxHashMap<DefId, Trait>,
    pub masked_crates: FxHashSet<CrateNum>,
}

impl<'a, 'tcx> Clean<Crate> for visit_ast::RustdocVisitor<'a, 'tcx> {
    fn clean(&self, cx: &DocContext) -> Crate {
        use ::visit_lib::LibEmbargoVisitor;

        {
            let mut r = cx.renderinfo.borrow_mut();
            r.deref_trait_did = cx.tcx.lang_items().deref_trait();
            r.deref_mut_trait_did = cx.tcx.lang_items().deref_mut_trait();
            r.owned_box_did = cx.tcx.lang_items().owned_box();
        }

        let mut externs = Vec::new();
        for &cnum in cx.tcx.crates().iter() {
            externs.push((cnum, cnum.clean(cx)));
            // Analyze doc-reachability for extern items
            LibEmbargoVisitor::new(cx).visit_lib(cnum);
        }
        externs.sort_by(|&(a, _), &(b, _)| a.cmp(&b));

        // Clean the crate, translating the entire libsyntax AST to one that is
        // understood by rustdoc.
        let mut module = self.module.clean(cx);
        let mut masked_crates = FxHashSet();

        match module.inner {
            ModuleItem(ref module) => {
                for it in &module.items {
                    if it.is_extern_crate() && it.attrs.has_doc_flag("masked") {
                        masked_crates.insert(it.def_id.krate);
                    }
                }
            }
            _ => unreachable!(),
        }

        let ExternalCrate { name, src, primitives, .. } = LOCAL_CRATE.clean(cx);
        {
            let m = match module.inner {
                ModuleItem(ref mut m) => m,
                _ => unreachable!(),
            };
            m.items.extend(primitives.iter().map(|&(def_id, prim, ref attrs)| {
                Item {
                    source: Span::empty(),
                    name: Some(prim.to_url_str().to_string()),
                    attrs: attrs.clone(),
                    visibility: Some(Public),
                    stability: get_stability(cx, def_id),
                    deprecation: get_deprecation(cx, def_id),
                    def_id,
                    inner: PrimitiveItem(prim),
                }
            }));
        }

        let mut access_levels = cx.access_levels.borrow_mut();
        let mut external_traits = cx.external_traits.borrow_mut();

        Crate {
            name,
            version: None,
            src,
            module: Some(module),
            externs,
            primitives,
            access_levels: Arc::new(mem::replace(&mut access_levels, Default::default())),
            external_traits: mem::replace(&mut external_traits, Default::default()),
            masked_crates,
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct ExternalCrate {
    pub name: String,
    pub src: FileName,
    pub attrs: Attributes,
    pub primitives: Vec<(DefId, PrimitiveType, Attributes)>,
}

impl Clean<ExternalCrate> for CrateNum {
    fn clean(&self, cx: &DocContext) -> ExternalCrate {
        let root = DefId { krate: *self, index: CRATE_DEF_INDEX };
        let krate_span = cx.tcx.def_span(root);
        let krate_src = cx.sess().codemap().span_to_filename(krate_span);

        // Collect all inner modules which are tagged as implementations of
        // primitives.
        //
        // Note that this loop only searches the top-level items of the crate,
        // and this is intentional. If we were to search the entire crate for an
        // item tagged with `#[doc(primitive)]` then we would also have to
        // search the entirety of external modules for items tagged
        // `#[doc(primitive)]`, which is a pretty inefficient process (decoding
        // all that metadata unconditionally).
        //
        // In order to keep the metadata load under control, the
        // `#[doc(primitive)]` feature is explicitly designed to only allow the
        // primitive tags to show up as the top level items in a crate.
        //
        // Also note that this does not attempt to deal with modules tagged
        // duplicately for the same primitive. This is handled later on when
        // rendering by delegating everything to a hash map.
        let as_primitive = |def: Def| {
            if let Def::Mod(def_id) = def {
                let attrs = cx.tcx.get_attrs(def_id).clean(cx);
                let mut prim = None;
                for attr in attrs.lists("doc") {
                    if let Some(v) = attr.value_str() {
                        if attr.check_name("primitive") {
                            prim = PrimitiveType::from_str(&v.as_str());
                            if prim.is_some() {
                                break;
                            }
                            // FIXME: should warn on unknown primitives?
                        }
                    }
                }
                return prim.map(|p| (def_id, p, attrs));
            }
            None
        };
        let primitives = if root.is_local() {
            cx.tcx.hir.krate().module.item_ids.iter().filter_map(|&id| {
                let item = cx.tcx.hir.expect_item(id.id);
                match item.node {
                    hir::ItemMod(_) => {
                        as_primitive(Def::Mod(cx.tcx.hir.local_def_id(id.id)))
                    }
                    hir::ItemUse(ref path, hir::UseKind::Single)
                    if item.vis == hir::Visibility::Public => {
                        as_primitive(path.def).map(|(_, prim, attrs)| {
                            // Pretend the primitive is local.
                            (cx.tcx.hir.local_def_id(id.id), prim, attrs)
                        })
                    }
                    _ => None
                }
            }).collect()
        } else {
            cx.tcx.item_children(root).iter().map(|item| item.def)
              .filter_map(as_primitive).collect()
        };

        ExternalCrate {
            name: cx.tcx.crate_name(*self).to_string(),
            src: krate_src,
            attrs: cx.tcx.get_attrs(root).clean(cx),
            primitives,
        }
    }
}

/// Anything with a source location and set of attributes and, optionally, a
/// name. That is, anything that can be documented. This doesn't correspond
/// directly to the AST's concept of an item; it's a strict superset.
#[derive(Clone, RustcEncodable, RustcDecodable)]
pub struct Item {
    /// Stringified span
    pub source: Span,
    /// Not everything has a name. E.g., impls
    pub name: Option<String>,
    pub attrs: Attributes,
    pub inner: ItemEnum,
    pub visibility: Option<Visibility>,
    pub def_id: DefId,
    pub stability: Option<Stability>,
    pub deprecation: Option<Deprecation>,
}

impl fmt::Debug for Item {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {

        let fake = MAX_DEF_ID.with(|m| m.borrow().get(&self.def_id.krate).map(|id| self.def_id >= *id).unwrap_or(false));
        println!("Fake: {:?} {:?} {:?}", fake, self.def_id.index, MAX_DEF_ID.with(|m| m.borrow().values().map(|k| k.index.clone()).collect::<Vec<_>>()));
        let def_id: &fmt::Debug = if fake { &"**FAKE**" } else { &self.def_id };
        
        fmt.debug_struct("Item")
            .field("source", &self.source)
            .field("name", &self.name)
            .field("attrs", &self.attrs)
            .field("inner", &self.inner)
            .field("visibility", &self.visibility)
            .field("def_id", def_id)
            .field("stability", &self.stability)
            .field("deprecation", &self.deprecation)
            .finish()
    }
}

impl Item {
    /// Finds the `doc` attribute as a NameValue and returns the corresponding
    /// value found.
    pub fn doc_value<'a>(&'a self) -> Option<&'a str> {
        self.attrs.doc_value()
    }
    /// Finds all `doc` attributes as NameValues and returns their corresponding values, joined
    /// with newlines.
    pub fn collapsed_doc_value(&self) -> Option<String> {
        self.attrs.collapsed_doc_value()
    }
    pub fn is_crate(&self) -> bool {
        match self.inner {
            StrippedItem(box ModuleItem(Module { is_crate: true, ..})) |
            ModuleItem(Module { is_crate: true, ..}) => true,
            _ => false,
        }
    }
    pub fn is_mod(&self) -> bool {
        self.type_() == ItemType::Module
    }
    pub fn is_trait(&self) -> bool {
        self.type_() == ItemType::Trait
    }
    pub fn is_struct(&self) -> bool {
        self.type_() == ItemType::Struct
    }
    pub fn is_enum(&self) -> bool {
        self.type_() == ItemType::Enum
    }
    pub fn is_fn(&self) -> bool {
        self.type_() == ItemType::Function
    }
    pub fn is_associated_type(&self) -> bool {
        self.type_() == ItemType::AssociatedType
    }
    pub fn is_associated_const(&self) -> bool {
        self.type_() == ItemType::AssociatedConst
    }
    pub fn is_method(&self) -> bool {
        self.type_() == ItemType::Method
    }
    pub fn is_ty_method(&self) -> bool {
        self.type_() == ItemType::TyMethod
    }
    pub fn is_typedef(&self) -> bool {
        self.type_() == ItemType::Typedef
    }
    pub fn is_primitive(&self) -> bool {
        self.type_() == ItemType::Primitive
    }
    pub fn is_union(&self) -> bool {
        self.type_() == ItemType::Union
    }
    pub fn is_import(&self) -> bool {
        self.type_() == ItemType::Import
    }
    pub fn is_extern_crate(&self) -> bool {
        self.type_() == ItemType::ExternCrate
    }

    pub fn is_stripped(&self) -> bool {
        match self.inner { StrippedItem(..) => true, _ => false }
    }
    pub fn has_stripped_fields(&self) -> Option<bool> {
        match self.inner {
            StructItem(ref _struct) => Some(_struct.fields_stripped),
            UnionItem(ref union) => Some(union.fields_stripped),
            VariantItem(Variant { kind: VariantKind::Struct(ref vstruct)} ) => {
                Some(vstruct.fields_stripped)
            },
            _ => None,
        }
    }

    pub fn stability_class(&self) -> Option<String> {
        self.stability.as_ref().and_then(|ref s| {
            let mut classes = Vec::with_capacity(2);

            if s.level == stability::Unstable {
                classes.push("unstable");
            }

            if !s.deprecated_since.is_empty() {
                classes.push("deprecated");
            }

            if classes.len() != 0 {
                Some(classes.join(" "))
            } else {
                None
            }
        })
    }

    pub fn stable_since(&self) -> Option<&str> {
        self.stability.as_ref().map(|s| &s.since[..])
    }

    /// Returns a documentation-level item type from the item.
    pub fn type_(&self) -> ItemType {
        ItemType::from(self)
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub enum ItemEnum {
    ExternCrateItem(String, Option<String>),
    ImportItem(Import),
    StructItem(Struct),
    UnionItem(Union),
    EnumItem(Enum),
    FunctionItem(Function),
    ModuleItem(Module),
    TypedefItem(Typedef, bool /* is associated type */),
    StaticItem(Static),
    ConstantItem(Constant),
    TraitItem(Trait),
    ImplItem(Impl),
    /// A method signature only. Used for required methods in traits (ie,
    /// non-default-methods).
    TyMethodItem(TyMethod),
    /// A method with a body.
    MethodItem(Method),
    StructFieldItem(Type),
    VariantItem(Variant),
    /// `fn`s from an extern block
    ForeignFunctionItem(Function),
    /// `static`s from an extern block
    ForeignStaticItem(Static),
    /// `type`s from an extern block
    ForeignTypeItem,
    MacroItem(Macro),
    PrimitiveItem(PrimitiveType),
    AssociatedConstItem(Type, Option<String>),
    AssociatedTypeItem(Vec<TyParamBound>, Option<Type>),
    /// An item that has been stripped by a rustdoc pass
    StrippedItem(Box<ItemEnum>),
}

impl ItemEnum {
    pub fn generics(&self) -> Option<&Generics> {
        Some(match *self {
            ItemEnum::StructItem(ref s) => &s.generics,
            ItemEnum::EnumItem(ref e) => &e.generics,
            ItemEnum::FunctionItem(ref f) => &f.generics,
            ItemEnum::TypedefItem(ref t, _) => &t.generics,
            ItemEnum::TraitItem(ref t) => &t.generics,
            ItemEnum::ImplItem(ref i) => &i.generics,
            ItemEnum::TyMethodItem(ref i) => &i.generics,
            ItemEnum::MethodItem(ref i) => &i.generics,
            ItemEnum::ForeignFunctionItem(ref f) => &f.generics,
            _ => return None,
        })
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Module {
    pub items: Vec<Item>,
    pub is_crate: bool,
}

impl Clean<Item> for doctree::Module {
    fn clean(&self, cx: &DocContext) -> Item {
        let name = if self.name.is_some() {
            self.name.unwrap().clean(cx)
        } else {
            "".to_string()
        };

        let mut items: Vec<Item> = vec![];
        items.extend(self.extern_crates.iter().map(|x| x.clean(cx)));
        items.extend(self.imports.iter().flat_map(|x| x.clean(cx)));
        items.extend(self.structs.iter().flat_map(|x| x.clean(cx)));
        items.extend(self.unions.iter().flat_map(|x| x.clean(cx)));
        items.extend(self.enums.iter().flat_map(|x| x.clean(cx)));
        items.extend(self.fns.iter().map(|x| x.clean(cx)));
        items.extend(self.foreigns.iter().flat_map(|x| x.clean(cx)));
        items.extend(self.mods.iter().map(|x| x.clean(cx)));
        items.extend(self.typedefs.iter().map(|x| x.clean(cx)));
        items.extend(self.statics.iter().map(|x| x.clean(cx)));
        items.extend(self.constants.iter().map(|x| x.clean(cx)));
        items.extend(self.traits.iter().map(|x| x.clean(cx)));
        items.extend(self.impls.iter().flat_map(|x| x.clean(cx)));
        items.extend(self.macros.iter().map(|x| x.clean(cx)));

        // determine if we should display the inner contents or
        // the outer `mod` item for the source code.
        let whence = {
            let cm = cx.sess().codemap();
            let outer = cm.lookup_char_pos(self.where_outer.lo());
            let inner = cm.lookup_char_pos(self.where_inner.lo());
            if outer.file.start_pos == inner.file.start_pos {
                // mod foo { ... }
                self.where_outer
            } else {
                // mod foo; (and a separate FileMap for the contents)
                self.where_inner
            }
        };

        Item {
            name: Some(name),
            attrs: self.attrs.clean(cx),
            source: whence.clean(cx),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            inner: ModuleItem(Module {
               is_crate: self.is_crate,
               items,
            })
        }
    }
}

pub struct ListAttributesIter<'a> {
    attrs: slice::Iter<'a, ast::Attribute>,
    current_list: vec::IntoIter<ast::NestedMetaItem>,
    name: &'a str
}

impl<'a> Iterator for ListAttributesIter<'a> {
    type Item = ast::NestedMetaItem;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(nested) = self.current_list.next() {
            return Some(nested);
        }

        for attr in &mut self.attrs {
            if let Some(list) = attr.meta_item_list() {
                if attr.check_name(self.name) {
                    self.current_list = list.into_iter();
                    if let Some(nested) = self.current_list.next() {
                        return Some(nested);
                    }
                }
            }
        }

        None
    }
}

pub trait AttributesExt {
    /// Finds an attribute as List and returns the list of attributes nested inside.
    fn lists<'a>(&'a self, name: &'a str) -> ListAttributesIter<'a>;
}

impl AttributesExt for [ast::Attribute] {
    fn lists<'a>(&'a self, name: &'a str) -> ListAttributesIter<'a> {
        ListAttributesIter {
            attrs: self.iter(),
            current_list: Vec::new().into_iter(),
            name,
        }
    }
}

pub trait NestedAttributesExt {
    /// Returns whether the attribute list contains a specific `Word`
    fn has_word(self, word: &str) -> bool;
}

impl<I: IntoIterator<Item=ast::NestedMetaItem>> NestedAttributesExt for I {
    fn has_word(self, word: &str) -> bool {
        self.into_iter().any(|attr| attr.is_word() && attr.check_name(word))
    }
}

/// A portion of documentation, extracted from a `#[doc]` attribute.
///
/// Each variant contains the line number within the complete doc-comment where the fragment
/// starts, as well as the Span where the corresponding doc comment or attribute is located.
///
/// Included files are kept separate from inline doc comments so that proper line-number
/// information can be given when a doctest fails. Sugared doc comments and "raw" doc comments are
/// kept separate because of issue #42760.
#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub enum DocFragment {
    // FIXME #44229 (misdreavus): sugared and raw doc comments can be brought back together once
    // hoedown is completely removed from rustdoc.
    /// A doc fragment created from a `///` or `//!` doc comment.
    SugaredDoc(usize, syntax_pos::Span, String),
    /// A doc fragment created from a "raw" `#[doc=""]` attribute.
    RawDoc(usize, syntax_pos::Span, String),
    /// A doc fragment created from a `#[doc(include="filename")]` attribute. Contains both the
    /// given filename and the file contents.
    Include(usize, syntax_pos::Span, String, String),
}

impl DocFragment {
    pub fn as_str(&self) -> &str {
        match *self {
            DocFragment::SugaredDoc(_, _, ref s) => &s[..],
            DocFragment::RawDoc(_, _, ref s) => &s[..],
            DocFragment::Include(_, _, _, ref s) => &s[..],
        }
    }

    pub fn span(&self) -> syntax_pos::Span {
        match *self {
            DocFragment::SugaredDoc(_, span, _) |
                DocFragment::RawDoc(_, span, _) |
                DocFragment::Include(_, span, _, _) => span,
        }
    }
}

impl<'a> FromIterator<&'a DocFragment> for String {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a DocFragment>
    {
        iter.into_iter().fold(String::new(), |mut acc, frag| {
            if !acc.is_empty() {
                acc.push('\n');
            }
            match *frag {
                DocFragment::SugaredDoc(_, _, ref docs)
                    | DocFragment::RawDoc(_, _, ref docs)
                    | DocFragment::Include(_, _, _, ref docs) =>
                    acc.push_str(docs),
            }

            acc
        })
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Default, Hash)]
pub struct Attributes {
    pub doc_strings: Vec<DocFragment>,
    pub other_attrs: Vec<ast::Attribute>,
    pub cfg: Option<Rc<Cfg>>,
    pub span: Option<syntax_pos::Span>,
}

impl Attributes {
    /// Extracts the content from an attribute `#[doc(cfg(content))]`.
    fn extract_cfg(mi: &ast::MetaItem) -> Option<&ast::MetaItem> {
        use syntax::ast::NestedMetaItemKind::MetaItem;

        if let ast::MetaItemKind::List(ref nmis) = mi.node {
            if nmis.len() == 1 {
                if let MetaItem(ref cfg_mi) = nmis[0].node {
                    if cfg_mi.check_name("cfg") {
                        if let ast::MetaItemKind::List(ref cfg_nmis) = cfg_mi.node {
                            if cfg_nmis.len() == 1 {
                                if let MetaItem(ref content_mi) = cfg_nmis[0].node {
                                    return Some(content_mi);
                                }
                            }
                        }
                    }
                }
            }
        }

        None
    }

    /// Reads a `MetaItem` from within an attribute, looks for whether it is a
    /// `#[doc(include="file")]`, and returns the filename and contents of the file as loaded from
    /// its expansion.
    fn extract_include(mi: &ast::MetaItem)
        -> Option<(String, String)>
    {
        mi.meta_item_list().and_then(|list| {
            for meta in list {
                if meta.check_name("include") {
                    // the actual compiled `#[doc(include="filename")]` gets expanded to
                    // `#[doc(include(file="filename", contents="file contents")]` so we need to
                    // look for that instead
                    return meta.meta_item_list().and_then(|list| {
                        let mut filename: Option<String> = None;
                        let mut contents: Option<String> = None;

                        for it in list {
                            if it.check_name("file") {
                                if let Some(name) = it.value_str() {
                                    filename = Some(name.to_string());
                                }
                            } else if it.check_name("contents") {
                                if let Some(docs) = it.value_str() {
                                    contents = Some(docs.to_string());
                                }
                            }
                        }

                        if let (Some(filename), Some(contents)) = (filename, contents) {
                            Some((filename, contents))
                        } else {
                            None
                        }
                    });
                }
            }

            None
        })
    }

    pub fn has_doc_flag(&self, flag: &str) -> bool {
        for attr in &self.other_attrs {
            if !attr.check_name("doc") { continue; }

            if let Some(items) = attr.meta_item_list() {
                if items.iter().filter_map(|i| i.meta_item()).any(|it| it.check_name(flag)) {
                    return true;
                }
            }
        }

        false
    }

    pub fn from_ast(diagnostic: &::errors::Handler,
                    attrs: &[ast::Attribute]) -> Attributes {
        let mut doc_strings = vec![];
        let mut sp = None;
        let mut cfg = Cfg::True;
        let mut doc_line = 0;

        let other_attrs = attrs.iter().filter_map(|attr| {
            attr.with_desugared_doc(|attr| {
                if attr.check_name("doc") {
                    if let Some(mi) = attr.meta() {
                        if let Some(value) = mi.value_str() {
                            // Extracted #[doc = "..."]
                            let value = value.to_string();
                            let line = doc_line;
                            doc_line += value.lines().count();

                            if attr.is_sugared_doc {
                                doc_strings.push(DocFragment::SugaredDoc(line, attr.span, value));
                            } else {
                                doc_strings.push(DocFragment::RawDoc(line, attr.span, value));
                            }

                            if sp.is_none() {
                                sp = Some(attr.span);
                            }
                            return None;
                        } else if let Some(cfg_mi) = Attributes::extract_cfg(&mi) {
                            // Extracted #[doc(cfg(...))]
                            match Cfg::parse(cfg_mi) {
                                Ok(new_cfg) => cfg &= new_cfg,
                                Err(e) => diagnostic.span_err(e.span, e.msg),
                            }
                            return None;
                        } else if let Some((filename, contents)) = Attributes::extract_include(&mi)
                        {
                            let line = doc_line;
                            doc_line += contents.lines().count();
                            doc_strings.push(DocFragment::Include(line,
                                                                  attr.span,
                                                                  filename,
                                                                  contents));
                        }
                    }
                }
                Some(attr.clone())
            })
        }).collect();
        Attributes {
            doc_strings,
            other_attrs,
            cfg: if cfg == Cfg::True { None } else { Some(Rc::new(cfg)) },
            span: sp,
        }
    }

    /// Finds the `doc` attribute as a NameValue and returns the corresponding
    /// value found.
    pub fn doc_value<'a>(&'a self) -> Option<&'a str> {
        self.doc_strings.first().map(|s| s.as_str())
    }

    /// Finds all `doc` attributes as NameValues and returns their corresponding values, joined
    /// with newlines.
    pub fn collapsed_doc_value(&self) -> Option<String> {
        if !self.doc_strings.is_empty() {
            Some(self.doc_strings.iter().collect())
        } else {
            None
        }
    }
}

impl AttributesExt for Attributes {
    fn lists<'a>(&'a self, name: &'a str) -> ListAttributesIter<'a> {
        self.other_attrs.lists(name)
    }
}

impl Clean<Attributes> for [ast::Attribute] {
    fn clean(&self, cx: &DocContext) -> Attributes {
        Attributes::from_ast(cx.sess().diagnostic(), self)
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct TyParam {
    pub name: String,
    pub did: DefId,
    pub bounds: Vec<TyParamBound>,
    pub default: Option<Type>,
}

impl Clean<TyParam> for hir::TyParam {
    fn clean(&self, cx: &DocContext) -> TyParam {
        TyParam {
            name: self.name.clean(cx),
            did: cx.tcx.hir.local_def_id(self.id),
            bounds: self.bounds.clean(cx),
            default: self.default.clean(cx),
        }
    }
}

impl<'tcx> Clean<TyParam> for ty::TypeParameterDef {
    fn clean(&self, cx: &DocContext) -> TyParam {
        cx.renderinfo.borrow_mut().external_typarams.insert(self.def_id, self.name.clean(cx));
        TyParam {
            name: self.name.clean(cx),
            did: self.def_id,
            bounds: vec![], // these are filled in from the where-clauses
            default: if self.has_default {
                Some(cx.tcx.type_of(self.def_id).clean(cx))
            } else {
                None
            }
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub enum TyParamBound {
    RegionBound(Lifetime),
    TraitBound(PolyTrait, hir::TraitBoundModifier)
}

impl TyParamBound {
    fn maybe_sized(cx: &DocContext) -> TyParamBound {
        let did = cx.tcx.require_lang_item(lang_items::SizedTraitLangItem);
        let empty = cx.tcx.intern_substs(&[]);
        let path = external_path(cx, &cx.tcx.item_name(did),
            Some(did), false, vec![], empty);
        inline::record_extern_fqn(cx, did, TypeKind::Trait);
        TraitBound(PolyTrait {
            trait_: ResolvedPath {
                path,
                typarams: None,
                did,
                is_generic: false,
            },
            generic_params: Vec::new(),
        }, hir::TraitBoundModifier::Maybe)
    }

    fn is_sized_bound(&self, cx: &DocContext) -> bool {
        use rustc::hir::TraitBoundModifier as TBM;
        if let TyParamBound::TraitBound(PolyTrait { ref trait_, .. }, TBM::None) = *self {
            if trait_.def_id() == cx.tcx.lang_items().sized_trait() {
                return true;
            }
        }
        false
    }

    fn get_trait_type(&self) -> Option<Type> {

        if let TyParamBound::TraitBound(PolyTrait { ref trait_, .. }, _) = *self {
            return Some(trait_.clone());
        }
        None
    }
}

impl Clean<TyParamBound> for hir::TyParamBound {
    fn clean(&self, cx: &DocContext) -> TyParamBound {
        match *self {
            hir::RegionTyParamBound(lt) => RegionBound(lt.clean(cx)),
            hir::TraitTyParamBound(ref t, modifier) => TraitBound(t.clean(cx), modifier),
        }
    }
}

fn external_path_params(cx: &DocContext, trait_did: Option<DefId>, has_self: bool,
                        bindings: Vec<TypeBinding>, substs: &Substs) -> PathParameters {
    let lifetimes = substs.regions().filter_map(|v| v.clean(cx)).collect();
    let types = substs.types().skip(has_self as usize).collect::<Vec<_>>();

    match trait_did {
        // Attempt to sugar an external path like Fn<(A, B,), C> to Fn(A, B) -> C
        Some(did) if cx.tcx.lang_items().fn_trait_kind(did).is_some() => {
            assert_eq!(types.len(), 1);
            let inputs = match types[0].sty {
                ty::TyTuple(ref tys, _) => tys.iter().map(|t| t.clean(cx)).collect(),
                _ => {
                    return PathParameters::AngleBracketed {
                        lifetimes,
                        types: types.clean(cx),
                        bindings,
                    }
                }
            };
            let output = None;
            // FIXME(#20299) return type comes from a projection now
            // match types[1].sty {
            //     ty::TyTuple(ref v, _) if v.is_empty() => None, // -> ()
            //     _ => Some(types[1].clean(cx))
            // };
            PathParameters::Parenthesized {
                inputs,
                output,
            }
        },
        _ => {
            PathParameters::AngleBracketed {
                lifetimes,
                types: types.clean(cx),
                bindings,
            }
        }
    }
}

// trait_did should be set to a trait's DefId if called on a TraitRef, in order to sugar
// from Fn<(A, B,), C> to Fn(A, B) -> C
fn external_path(cx: &DocContext, name: &str, trait_did: Option<DefId>, has_self: bool,
                 bindings: Vec<TypeBinding>, substs: &Substs) -> Path {
    Path {
        global: false,
        def: Def::Err,
        segments: vec![PathSegment {
            name: name.to_string(),
            params: external_path_params(cx, trait_did, has_self, bindings, substs)
        }],
    }
}

impl<'tcx> Clean<TyParamBound> for ty::TraitRef<'tcx> {
    fn clean(&self, cx: &DocContext) -> TyParamBound {
        inline::record_extern_fqn(cx, self.def_id, TypeKind::Trait);
        let path = external_path(cx, &cx.tcx.item_name(self.def_id),
                                 Some(self.def_id), true, vec![], self.substs);

        debug!("ty::TraitRef\n  subst: {:?}\n", self.substs);

        // collect any late bound regions
        let mut late_bounds = vec![];
        for ty_s in self.input_types().skip(1) {
            if let ty::TyTuple(ts, _) = ty_s.sty {
                for &ty_s in ts {
                    if let ty::TyRef(ref reg, _) = ty_s.sty {
                        if let &ty::RegionKind::ReLateBound(..) = *reg {
                            debug!("  hit an ReLateBound {:?}", reg);
                            if let Some(lt) = reg.clean(cx) {
                                late_bounds.push(GenericParam::Lifetime(lt));
                            }
                        }
                    }
                }
            }
        }

        TraitBound(
            PolyTrait {
                trait_: ResolvedPath {
                    path,
                    typarams: None,
                    did: self.def_id,
                    is_generic: false,
                },
                generic_params: late_bounds,
            },
            hir::TraitBoundModifier::None
        )
    }
}

impl<'tcx> Clean<Option<Vec<TyParamBound>>> for Substs<'tcx> {
    fn clean(&self, cx: &DocContext) -> Option<Vec<TyParamBound>> {
        let mut v = Vec::new();
        v.extend(self.regions().filter_map(|r| r.clean(cx))
                     .map(RegionBound));
        v.extend(self.types().map(|t| TraitBound(PolyTrait {
            trait_: t.clean(cx),
            generic_params: Vec::new(),
        }, hir::TraitBoundModifier::None)));
        if !v.is_empty() {Some(v)} else {None}
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct Lifetime(String);

impl Lifetime {
    pub fn get_ref<'a>(&'a self) -> &'a str {
        let Lifetime(ref s) = *self;
        let s: &'a str = s;
        s
    }

    pub fn statik() -> Lifetime {
        Lifetime("'static".to_string())
    }
}

impl Clean<Lifetime> for hir::Lifetime {
    fn clean(&self, cx: &DocContext) -> Lifetime {
        if self.id != ast::DUMMY_NODE_ID {
            let hir_id = cx.tcx.hir.node_to_hir_id(self.id);
            let def = cx.tcx.named_region(hir_id);
            match def {
                Some(rl::Region::EarlyBound(_, node_id, _)) |
                Some(rl::Region::LateBound(_, node_id, _)) |
                Some(rl::Region::Free(_, node_id)) => {
                    if let Some(lt) = cx.lt_substs.borrow().get(&node_id).cloned() {
                        return lt;
                    }
                }
                _ => {}
            }
        }
        Lifetime(self.name.name().to_string())
    }
}

impl Clean<Lifetime> for hir::LifetimeDef {
    fn clean(&self, _: &DocContext) -> Lifetime {
        if self.bounds.len() > 0 {
            let mut s = format!("{}: {}",
                                self.lifetime.name.name(),
                                self.bounds[0].name.name());
            for bound in self.bounds.iter().skip(1) {
                s.push_str(&format!(" + {}", bound.name.name()));
            }
            Lifetime(s)
        } else {
            Lifetime(self.lifetime.name.name().to_string())
        }
    }
}

impl Clean<Lifetime> for ty::RegionParameterDef {
    fn clean(&self, _: &DocContext) -> Lifetime {
        Lifetime(self.name.to_string())
    }
}

impl Clean<Option<Lifetime>> for ty::RegionKind {
    fn clean(&self, cx: &DocContext) -> Option<Lifetime> {
        match *self {
            ty::ReStatic => Some(Lifetime::statik()),
            ty::ReLateBound(_, ty::BrNamed(_, name)) => Some(Lifetime(name.to_string())),
            ty::ReEarlyBound(ref data) => Some(Lifetime(data.name.clean(cx))),

            ty::ReLateBound(..) |
            ty::ReFree(..) |
            ty::ReScope(..) |
            ty::ReVar(..) |
            ty::ReSkolemized(..) |
            ty::ReEmpty |
            ty::ReClosureBound(_) |
            ty::ReErased => None
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub enum WherePredicate {
    BoundPredicate { ty: Type, bounds: Vec<TyParamBound> },
    RegionPredicate { lifetime: Lifetime, bounds: Vec<Lifetime>},
    EqPredicate { lhs: Type, rhs: Type },
}

impl Clean<WherePredicate> for hir::WherePredicate {
    fn clean(&self, cx: &DocContext) -> WherePredicate {
        match *self {
            hir::WherePredicate::BoundPredicate(ref wbp) => {
                WherePredicate::BoundPredicate {
                    ty: wbp.bounded_ty.clean(cx),
                    bounds: wbp.bounds.clean(cx)
                }
            }

            hir::WherePredicate::RegionPredicate(ref wrp) => {
                WherePredicate::RegionPredicate {
                    lifetime: wrp.lifetime.clean(cx),
                    bounds: wrp.bounds.clean(cx)
                }
            }

            hir::WherePredicate::EqPredicate(ref wrp) => {
                WherePredicate::EqPredicate {
                    lhs: wrp.lhs_ty.clean(cx),
                    rhs: wrp.rhs_ty.clean(cx)
                }
            }
        }
    }
}

impl<'a> Clean<WherePredicate> for ty::Predicate<'a> {
    fn clean(&self, cx: &DocContext) -> WherePredicate {
        use rustc::ty::Predicate;

        match *self {
            Predicate::Trait(ref pred) => pred.clean(cx),
            Predicate::Equate(ref pred) => pred.clean(cx),
            Predicate::Subtype(ref pred) => pred.clean(cx),
            Predicate::RegionOutlives(ref pred) => pred.clean(cx),
            Predicate::TypeOutlives(ref pred) => pred.clean(cx),
            Predicate::Projection(ref pred) => pred.clean(cx),
            Predicate::WellFormed(_) => panic!("not user writable"),
            Predicate::ObjectSafe(_) => panic!("not user writable"),
            Predicate::ClosureKind(..) => panic!("not user writable"),
            Predicate::ConstEvaluatable(..) => panic!("not user writable"),
        }
    }
}

impl<'a> Clean<WherePredicate> for ty::TraitPredicate<'a> {
    fn clean(&self, cx: &DocContext) -> WherePredicate {
        WherePredicate::BoundPredicate {
            ty: self.trait_ref.self_ty().clean(cx),
            bounds: vec![self.trait_ref.clean(cx)]
        }
    }
}

impl<'tcx> Clean<WherePredicate> for ty::EquatePredicate<'tcx> {
    fn clean(&self, cx: &DocContext) -> WherePredicate {
        let ty::EquatePredicate(ref lhs, ref rhs) = *self;
        WherePredicate::EqPredicate {
            lhs: lhs.clean(cx),
            rhs: rhs.clean(cx)
        }
    }
}

impl<'tcx> Clean<WherePredicate> for ty::SubtypePredicate<'tcx> {
    fn clean(&self, _cx: &DocContext) -> WherePredicate {
        panic!("subtype predicates are an internal rustc artifact \
                and should not be seen by rustdoc")
    }
}

impl<'tcx> Clean<WherePredicate> for ty::OutlivesPredicate<ty::Region<'tcx>, ty::Region<'tcx>> {
    fn clean(&self, cx: &DocContext) -> WherePredicate {
        let ty::OutlivesPredicate(ref a, ref b) = *self;
        WherePredicate::RegionPredicate {
            lifetime: a.clean(cx).unwrap(),
            bounds: vec![b.clean(cx).unwrap()]
        }
    }
}

impl<'tcx> Clean<WherePredicate> for ty::OutlivesPredicate<Ty<'tcx>, ty::Region<'tcx>> {
    fn clean(&self, cx: &DocContext) -> WherePredicate {
        let ty::OutlivesPredicate(ref ty, ref lt) = *self;

        WherePredicate::BoundPredicate {
            ty: ty.clean(cx),
            bounds: vec![TyParamBound::RegionBound(lt.clean(cx).unwrap())]
        }
    }
}

impl<'tcx> Clean<WherePredicate> for ty::ProjectionPredicate<'tcx> {
    fn clean(&self, cx: &DocContext) -> WherePredicate {
        WherePredicate::EqPredicate {
            lhs: self.projection_ty.clean(cx),
            rhs: self.ty.clean(cx)
        }
    }
}

impl<'tcx> Clean<Type> for ty::ProjectionTy<'tcx> {
    fn clean(&self, cx: &DocContext) -> Type {
        let trait_ = match self.trait_ref(cx.tcx).clean(cx) {
            TyParamBound::TraitBound(t, _) => t.trait_,
            TyParamBound::RegionBound(_) => {
                panic!("cleaning a trait got a region")
            }
        };
        Type::QPath {
            name: cx.tcx.associated_item(self.item_def_id).name.clean(cx),
            self_type: box self.self_ty().clean(cx),
            trait_: box trait_
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub enum GenericParam {
    Lifetime(Lifetime),
    Type(TyParam),
}

impl Clean<GenericParam> for hir::GenericParam {
    fn clean(&self, cx: &DocContext) -> GenericParam {
        match *self {
            hir::GenericParam::Lifetime(ref l) => GenericParam::Lifetime(l.clean(cx)),
            hir::GenericParam::Type(ref t) => GenericParam::Type(t.clean(cx)),
        }
    }
}

// maybe use a Generic enum and use Vec<Generic>?
#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Default, Hash)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub where_predicates: Vec<WherePredicate>,
}

impl Clean<Generics> for hir::Generics {
    fn clean(&self, cx: &DocContext) -> Generics {
        let mut g = Generics {
            params: self.params.clean(cx),
            where_predicates: self.where_clause.predicates.clean(cx)
        };

        // Some duplicates are generated for ?Sized bounds between type params and where
        // predicates. The point in here is to move the bounds definitions from type params
        // to where predicates when such cases occur.
        for where_pred in &mut g.where_predicates {
            match *where_pred {
                WherePredicate::BoundPredicate { ty: Generic(ref name), ref mut bounds } => {
                    if bounds.is_empty() {
                        for param in &mut g.params {
                            if let GenericParam::Type(ref mut type_param) = *param {
                                if &type_param.name == name {
                                    mem::swap(bounds, &mut type_param.bounds);
                                    break
                                }
                            }
                        }
                    }
                }
                _ => continue,
            }
        }
        g
    }
}

impl<'a, 'tcx> Clean<Generics> for (&'a ty::Generics,
                                    &'a ty::GenericPredicates<'tcx>) {
    fn clean(&self, cx: &DocContext) -> Generics {
        use self::WherePredicate as WP;

        let (gens, preds) = *self;

        // Bounds in the type_params and lifetimes fields are repeated in the
        // predicates field (see rustc_typeck::collect::ty_generics), so remove
        // them.
        let stripped_typarams = gens.types.iter().filter_map(|tp| {
            if tp.name == keywords::SelfType.name() {
                assert_eq!(tp.index, 0);
                None
            } else {
                Some(tp.clean(cx))
            }
        }).collect::<Vec<_>>();

        let mut where_predicates = preds.predicates.to_vec().clean(cx);

        // Type parameters and have a Sized bound by default unless removed with
        // ?Sized. Scan through the predicates and mark any type parameter with
        // a Sized bound, removing the bounds as we find them.
        //
        // Note that associated types also have a sized bound by default, but we
        // don't actually know the set of associated types right here so that's
        // handled in cleaning associated types
        let mut sized_params = FxHashSet();
        where_predicates.retain(|pred| {
            match *pred {
                WP::BoundPredicate { ty: Generic(ref g), ref bounds } => {
                    if bounds.iter().any(|b| b.is_sized_bound(cx)) {
                        sized_params.insert(g.clone());
                        false
                    } else {
                        true
                    }
                }
                _ => true,
            }
        });

        // Run through the type parameters again and insert a ?Sized
        // unbound for any we didn't find to be Sized.
        for tp in &stripped_typarams {
            if !sized_params.contains(&tp.name) {
                where_predicates.push(WP::BoundPredicate {
                    ty: Type::Generic(tp.name.clone()),
                    bounds: vec![TyParamBound::maybe_sized(cx)],
                })
            }
        }

        // It would be nice to collect all of the bounds on a type and recombine
        // them if possible, to avoid e.g. `where T: Foo, T: Bar, T: Sized, T: 'a`
        // and instead see `where T: Foo + Bar + Sized + 'a`

        Generics {
            params: gens.regions
                .clean(cx)
                .into_iter()
                .map(|lp| GenericParam::Lifetime(lp))
                .chain(
                    simplify::ty_params(stripped_typarams)
                        .into_iter()
                        .map(|tp| GenericParam::Type(tp))
                )
                .collect(),
            where_predicates: simplify::where_clauses(cx, where_predicates),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Method {
    pub generics: Generics,
    pub unsafety: hir::Unsafety,
    pub constness: hir::Constness,
    pub decl: FnDecl,
    pub abi: Abi,
}

impl<'a> Clean<Method> for (&'a hir::MethodSig, &'a hir::Generics, hir::BodyId) {
    fn clean(&self, cx: &DocContext) -> Method {
        Method {
            generics: self.1.clean(cx),
            unsafety: self.0.unsafety,
            constness: self.0.constness,
            decl: (&*self.0.decl, self.2).clean(cx),
            abi: self.0.abi
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct TyMethod {
    pub unsafety: hir::Unsafety,
    pub decl: FnDecl,
    pub generics: Generics,
    pub abi: Abi,
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Function {
    pub decl: FnDecl,
    pub generics: Generics,
    pub unsafety: hir::Unsafety,
    pub constness: hir::Constness,
    pub abi: Abi,
}

impl Clean<Item> for doctree::Function {
    fn clean(&self, cx: &DocContext) -> Item {
        Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            inner: FunctionItem(Function {
                decl: (&self.decl, self.body).clean(cx),
                generics: self.generics.clean(cx),
                unsafety: self.unsafety,
                constness: self.constness,
                abi: self.abi,
            }),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct FnDecl {
    pub inputs: Arguments,
    pub output: FunctionRetTy,
    pub variadic: bool,
    pub attrs: Attributes,
}

impl FnDecl {
    pub fn has_self(&self) -> bool {
        self.inputs.values.len() > 0 && self.inputs.values[0].name == "self"
    }

    pub fn self_type(&self) -> Option<SelfTy> {
        self.inputs.values.get(0).and_then(|v| v.to_self())
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct Arguments {
    pub values: Vec<Argument>,
}

impl<'a> Clean<Arguments> for (&'a [P<hir::Ty>], &'a [Spanned<ast::Name>]) {
    fn clean(&self, cx: &DocContext) -> Arguments {
        Arguments {
            values: self.0.iter().enumerate().map(|(i, ty)| {
                let mut name = self.1.get(i).map(|n| n.node.to_string())
                                            .unwrap_or(String::new());
                if name.is_empty() {
                    name = "_".to_string();
                }
                Argument {
                    name,
                    type_: ty.clean(cx),
                }
            }).collect()
        }
    }
}

impl<'a> Clean<Arguments> for (&'a [P<hir::Ty>], hir::BodyId) {
    fn clean(&self, cx: &DocContext) -> Arguments {
        let body = cx.tcx.hir.body(self.1);

        Arguments {
            values: self.0.iter().enumerate().map(|(i, ty)| {
                Argument {
                    name: name_from_pat(&body.arguments[i].pat),
                    type_: ty.clean(cx),
                }
            }).collect()
        }
    }
}

impl<'a, A: Copy> Clean<FnDecl> for (&'a hir::FnDecl, A)
    where (&'a [P<hir::Ty>], A): Clean<Arguments>
{
    fn clean(&self, cx: &DocContext) -> FnDecl {
        FnDecl {
            inputs: (&self.0.inputs[..], self.1).clean(cx),
            output: self.0.output.clean(cx),
            variadic: self.0.variadic,
            attrs: Attributes::default()
        }
    }
}

impl<'a, 'tcx> Clean<FnDecl> for (DefId, ty::PolyFnSig<'tcx>) {
    fn clean(&self, cx: &DocContext) -> FnDecl {
        let (did, sig) = *self;
        let mut names = if cx.tcx.hir.as_local_node_id(did).is_some() {
            vec![].into_iter()
        } else {
            cx.tcx.fn_arg_names(did).into_iter()
        }.peekable();
        FnDecl {
            output: Return(sig.skip_binder().output().clean(cx)),
            attrs: Attributes::default(),
            variadic: sig.skip_binder().variadic,
            inputs: Arguments {
                values: sig.skip_binder().inputs().iter().map(|t| {
                    Argument {
                        type_: t.clean(cx),
                        name: names.next().map_or("".to_string(), |name| name.to_string()),
                    }
                }).collect(),
            },
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct Argument {
    pub type_: Type,
    pub name: String,
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Debug)]
pub enum SelfTy {
    SelfValue,
    SelfBorrowed(Option<Lifetime>, Mutability),
    SelfExplicit(Type),
}

impl Argument {
    pub fn to_self(&self) -> Option<SelfTy> {
        if self.name != "self" {
            return None;
        }
        if self.type_.is_self_type() {
            return Some(SelfValue);
        }
        match self.type_ {
            BorrowedRef{ref lifetime, mutability, ref type_} if type_.is_self_type() => {
                Some(SelfBorrowed(lifetime.clone(), mutability))
            }
            _ => Some(SelfExplicit(self.type_.clone()))
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub enum FunctionRetTy {
    Return(Type),
    DefaultReturn,
}

impl Clean<FunctionRetTy> for hir::FunctionRetTy {
    fn clean(&self, cx: &DocContext) -> FunctionRetTy {
        match *self {
            hir::Return(ref typ) => Return(typ.clean(cx)),
            hir::DefaultReturn(..) => DefaultReturn,
        }
    }
}

impl GetDefId for FunctionRetTy {
    fn def_id(&self) -> Option<DefId> {
        match *self {
            Return(ref ty) => ty.def_id(),
            DefaultReturn => None,
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Trait {
    pub auto: bool,
    pub unsafety: hir::Unsafety,
    pub items: Vec<Item>,
    pub generics: Generics,
    pub bounds: Vec<TyParamBound>,
    pub is_spotlight: bool,
}

impl Clean<Item> for doctree::Trait {
    fn clean(&self, cx: &DocContext) -> Item {
        let attrs = self.attrs.clean(cx);
        let is_spotlight = attrs.has_doc_flag("spotlight");
        Item {
            name: Some(self.name.clean(cx)),
            attrs: attrs,
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: TraitItem(Trait {
                auto: self.auto,
                unsafety: self.unsafety,
                items: self.items.clean(cx),
                generics: self.generics.clean(cx),
                bounds: self.bounds.clean(cx),
                is_spotlight: is_spotlight,
            }),
        }
    }
}

impl Clean<Type> for hir::TraitRef {
    fn clean(&self, cx: &DocContext) -> Type {
        resolve_type(cx, self.path.clean(cx), self.ref_id)
    }
}

impl Clean<PolyTrait> for hir::PolyTraitRef {
    fn clean(&self, cx: &DocContext) -> PolyTrait {
        PolyTrait {
            trait_: self.trait_ref.clean(cx),
            generic_params: self.bound_generic_params.clean(cx)
        }
    }
}

impl Clean<Item> for hir::TraitItem {
    fn clean(&self, cx: &DocContext) -> Item {
        let inner = match self.node {
            hir::TraitItemKind::Const(ref ty, default) => {
                AssociatedConstItem(ty.clean(cx),
                                    default.map(|e| print_const_expr(cx, e)))
            }
            hir::TraitItemKind::Method(ref sig, hir::TraitMethod::Provided(body)) => {
                MethodItem((sig, &self.generics, body).clean(cx))
            }
            hir::TraitItemKind::Method(ref sig, hir::TraitMethod::Required(ref names)) => {
                TyMethodItem(TyMethod {
                    unsafety: sig.unsafety.clone(),
                    decl: (&*sig.decl, &names[..]).clean(cx),
                    generics: self.generics.clean(cx),
                    abi: sig.abi
                })
            }
            hir::TraitItemKind::Type(ref bounds, ref default) => {
                AssociatedTypeItem(bounds.clean(cx), default.clean(cx))
            }
        };
        Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.span.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: None,
            stability: get_stability(cx, cx.tcx.hir.local_def_id(self.id)),
            deprecation: get_deprecation(cx, cx.tcx.hir.local_def_id(self.id)),
            inner,
        }
    }
}

impl Clean<Item> for hir::ImplItem {
    fn clean(&self, cx: &DocContext) -> Item {
        let inner = match self.node {
            hir::ImplItemKind::Const(ref ty, expr) => {
                AssociatedConstItem(ty.clean(cx),
                                    Some(print_const_expr(cx, expr)))
            }
            hir::ImplItemKind::Method(ref sig, body) => {
                MethodItem((sig, &self.generics, body).clean(cx))
            }
            hir::ImplItemKind::Type(ref ty) => TypedefItem(Typedef {
                type_: ty.clean(cx),
                generics: Generics::default(),
            }, true),
        };
        Item {
            name: Some(self.name.clean(cx)),
            source: self.span.clean(cx),
            attrs: self.attrs.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: get_stability(cx, cx.tcx.hir.local_def_id(self.id)),
            deprecation: get_deprecation(cx, cx.tcx.hir.local_def_id(self.id)),
            inner,
        }
    }
}

impl<'tcx> Clean<Item> for ty::AssociatedItem {
    fn clean(&self, cx: &DocContext) -> Item {
        let inner = match self.kind {
            ty::AssociatedKind::Const => {
                let ty = cx.tcx.type_of(self.def_id);
                let default = if self.defaultness.has_value() {
                    Some(inline::print_inlined_const(cx, self.def_id))
                } else {
                    None
                };
                AssociatedConstItem(ty.clean(cx), default)
            }
            ty::AssociatedKind::Method => {
                let generics = (cx.tcx.generics_of(self.def_id),
                                &cx.tcx.predicates_of(self.def_id)).clean(cx);
                let sig = cx.tcx.fn_sig(self.def_id);
                let mut decl = (self.def_id, sig).clean(cx);

                if self.method_has_self_argument {
                    let self_ty = match self.container {
                        ty::ImplContainer(def_id) => {
                            cx.tcx.type_of(def_id)
                        }
                        ty::TraitContainer(_) => cx.tcx.mk_self_type()
                    };
                    let self_arg_ty = *sig.input(0).skip_binder();
                    if self_arg_ty == self_ty {
                        decl.inputs.values[0].type_ = Generic(String::from("Self"));
                    } else if let ty::TyRef(_, mt) = self_arg_ty.sty {
                        if mt.ty == self_ty {
                            match decl.inputs.values[0].type_ {
                                BorrowedRef{ref mut type_, ..} => {
                                    **type_ = Generic(String::from("Self"))
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                }

                let provided = match self.container {
                    ty::ImplContainer(_) => true,
                    ty::TraitContainer(_) => self.defaultness.has_value()
                };
                if provided {
                    let constness = if cx.tcx.is_const_fn(self.def_id) {
                        hir::Constness::Const
                    } else {
                        hir::Constness::NotConst
                    };
                    MethodItem(Method {
                        unsafety: sig.unsafety(),
                        generics,
                        decl,
                        abi: sig.abi(),
                        constness,
                    })
                } else {
                    TyMethodItem(TyMethod {
                        unsafety: sig.unsafety(),
                        generics,
                        decl,
                        abi: sig.abi(),
                    })
                }
            }
            ty::AssociatedKind::Type => {
                let my_name = self.name.clean(cx);

                if let ty::TraitContainer(did) = self.container {
                    // When loading a cross-crate associated type, the bounds for this type
                    // are actually located on the trait/impl itself, so we need to load
                    // all of the generics from there and then look for bounds that are
                    // applied to this associated type in question.
                    let predicates = cx.tcx.predicates_of(did);
                    let generics = (cx.tcx.generics_of(did), &predicates).clean(cx);
                    let mut bounds = generics.where_predicates.iter().filter_map(|pred| {
                        let (name, self_type, trait_, bounds) = match *pred {
                            WherePredicate::BoundPredicate {
                                ty: QPath { ref name, ref self_type, ref trait_ },
                                ref bounds
                            } => (name, self_type, trait_, bounds),
                            _ => return None,
                        };
                        if *name != my_name { return None }
                        match **trait_ {
                            ResolvedPath { did, .. } if did == self.container.id() => {}
                            _ => return None,
                        }
                        match **self_type {
                            Generic(ref s) if *s == "Self" => {}
                            _ => return None,
                        }
                        Some(bounds)
                    }).flat_map(|i| i.iter().cloned()).collect::<Vec<_>>();
                    // Our Sized/?Sized bound didn't get handled when creating the generics
                    // because we didn't actually get our whole set of bounds until just now
                    // (some of them may have come from the trait). If we do have a sized
                    // bound, we remove it, and if we don't then we add the `?Sized` bound
                    // at the end.
                    match bounds.iter().position(|b| b.is_sized_bound(cx)) {
                        Some(i) => { bounds.remove(i); }
                        None => bounds.push(TyParamBound::maybe_sized(cx)),
                    }

                    let ty = if self.defaultness.has_value() {
                        Some(cx.tcx.type_of(self.def_id))
                    } else {
                        None
                    };

                    AssociatedTypeItem(bounds, ty.clean(cx))
                } else {
                    TypedefItem(Typedef {
                        type_: cx.tcx.type_of(self.def_id).clean(cx),
                        generics: Generics {
                            params: Vec::new(),
                            where_predicates: Vec::new(),
                        },
                    }, true)
                }
            }
        };

        let visibility = match self.container {
            ty::ImplContainer(_) => self.vis.clean(cx),
            ty::TraitContainer(_) => None,
        };

        Item {
            name: Some(self.name.clean(cx)),
            visibility,
            stability: get_stability(cx, self.def_id),
            deprecation: get_deprecation(cx, self.def_id),
            def_id: self.def_id,
            attrs: inline::load_attrs(cx, self.def_id),
            source: cx.tcx.def_span(self.def_id).clean(cx),
            inner,
        }
    }
}

/// A trait reference, which may have higher ranked lifetimes.
#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct PolyTrait {
    pub trait_: Type,
    pub generic_params: Vec<GenericParam>,
}

/// A representation of a Type suitable for hyperlinking purposes. Ideally one can get the original
/// type out of the AST/TyCtxt given one of these, if more information is needed. Most importantly
/// it does not preserve mutability or boxes.
#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub enum Type {
    /// structs/enums/traits (most that'd be an hir::TyPath)
    ResolvedPath {
        path: Path,
        typarams: Option<Vec<TyParamBound>>,
        did: DefId,
        /// true if is a `T::Name` path for associated types
        is_generic: bool,
    },
    /// For parameterized types, so the consumer of the JSON don't go
    /// looking for types which don't exist anywhere.
    Generic(String),
    /// Primitives are the fixed-size numeric types (plus int/usize/float), char,
    /// arrays, slices, and tuples.
    Primitive(PrimitiveType),
    /// extern "ABI" fn
    BareFunction(Box<BareFunctionDecl>),
    Tuple(Vec<Type>),
    Slice(Box<Type>),
    Array(Box<Type>, String),
    Never,
    Unique(Box<Type>),
    RawPointer(Mutability, Box<Type>),
    BorrowedRef {
        lifetime: Option<Lifetime>,
        mutability: Mutability,
        type_: Box<Type>,
    },

    // <Type as Trait>::Name
    QPath {
        name: String,
        self_type: Box<Type>,
        trait_: Box<Type>
    },

    // _
    Infer,

    // impl TraitA+TraitB
    ImplTrait(Vec<TyParamBound>),
    // The '..' in 'impl Trait for ..'
    DotDot
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Hash, Copy, Debug)]
pub enum PrimitiveType {
    Isize, I8, I16, I32, I64, I128,
    Usize, U8, U16, U32, U64, U128,
    F32, F64,
    Char,
    Bool,
    Str,
    Slice,
    Array,
    Tuple,
    Unit,
    RawPointer,
    Reference,
    Fn,
    Never,
}

#[derive(Clone, RustcEncodable, RustcDecodable, Copy, Debug)]
pub enum TypeKind {
    Enum,
    Function,
    Module,
    Const,
    Static,
    Struct,
    Union,
    Trait,
    Variant,
    Typedef,
    Foreign,
}

pub trait GetDefId {
    fn def_id(&self) -> Option<DefId>;
}

impl<T: GetDefId> GetDefId for Option<T> {
    fn def_id(&self) -> Option<DefId> {
        self.as_ref().and_then(|d| d.def_id())
    }
}

impl Type {
    pub fn primitive_type(&self) -> Option<PrimitiveType> {
        match *self {
            Primitive(p) | BorrowedRef { type_: box Primitive(p), ..} => Some(p),
            Slice(..) | BorrowedRef { type_: box Slice(..), .. } => Some(PrimitiveType::Slice),
            Array(..) | BorrowedRef { type_: box Array(..), .. } => Some(PrimitiveType::Array),
            Tuple(ref tys) => if tys.is_empty() {
                Some(PrimitiveType::Unit)
            } else {
                Some(PrimitiveType::Tuple)
            },
            RawPointer(..) => Some(PrimitiveType::RawPointer),
            BorrowedRef { type_: box Generic(..), .. } => Some(PrimitiveType::Reference),
            BareFunction(..) => Some(PrimitiveType::Fn),
            Never => Some(PrimitiveType::Never),
            _ => None,
        }
    }

    pub fn is_generic(&self) -> bool {
        match *self {
            ResolvedPath { is_generic, .. } => is_generic,
            _ => false,
        }
    }

    pub fn is_self_type(&self) -> bool {
        match *self {
            Generic(ref name) => name == "Self",
            _ => false
        }
    }

    pub fn generics(&self) -> Option<&[Type]> {
        match *self {
            ResolvedPath { ref path, .. } => {
                path.segments.last().and_then(|seg| {
                    if let PathParameters::AngleBracketed { ref types, .. } = seg.params {
                        Some(&**types)
                    } else {
                        None
                    }
                })
            }
            _ => None,
        }
    }
}

impl GetDefId for Type {
    fn def_id(&self) -> Option<DefId> {
        match *self {
            ResolvedPath { did, .. } => Some(did),
            Primitive(p) => ::html::render::cache().primitive_locations.get(&p).cloned(),
            BorrowedRef { type_: box Generic(..), .. } =>
                Primitive(PrimitiveType::Reference).def_id(),
            BorrowedRef { ref type_, .. } => type_.def_id(),
            Tuple(ref tys) => if tys.is_empty() {
                Primitive(PrimitiveType::Unit).def_id()
            } else {
                Primitive(PrimitiveType::Tuple).def_id()
            },
            BareFunction(..) => Primitive(PrimitiveType::Fn).def_id(),
            Never => Primitive(PrimitiveType::Never).def_id(),
            Slice(..) => Primitive(PrimitiveType::Slice).def_id(),
            Array(..) => Primitive(PrimitiveType::Array).def_id(),
            RawPointer(..) => Primitive(PrimitiveType::RawPointer).def_id(),
            QPath { ref self_type, .. } => self_type.def_id(),
            _ => None,
        }
    }
}

impl PrimitiveType {
    fn from_str(s: &str) -> Option<PrimitiveType> {
        match s {
            "isize" => Some(PrimitiveType::Isize),
            "i8" => Some(PrimitiveType::I8),
            "i16" => Some(PrimitiveType::I16),
            "i32" => Some(PrimitiveType::I32),
            "i64" => Some(PrimitiveType::I64),
            "i128" => Some(PrimitiveType::I128),
            "usize" => Some(PrimitiveType::Usize),
            "u8" => Some(PrimitiveType::U8),
            "u16" => Some(PrimitiveType::U16),
            "u32" => Some(PrimitiveType::U32),
            "u64" => Some(PrimitiveType::U64),
            "u128" => Some(PrimitiveType::U128),
            "bool" => Some(PrimitiveType::Bool),
            "char" => Some(PrimitiveType::Char),
            "str" => Some(PrimitiveType::Str),
            "f32" => Some(PrimitiveType::F32),
            "f64" => Some(PrimitiveType::F64),
            "array" => Some(PrimitiveType::Array),
            "slice" => Some(PrimitiveType::Slice),
            "tuple" => Some(PrimitiveType::Tuple),
            "unit" => Some(PrimitiveType::Unit),
            "pointer" => Some(PrimitiveType::RawPointer),
            "reference" => Some(PrimitiveType::Reference),
            "fn" => Some(PrimitiveType::Fn),
            "never" => Some(PrimitiveType::Never),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        use self::PrimitiveType::*;
        match *self {
            Isize => "isize",
            I8 => "i8",
            I16 => "i16",
            I32 => "i32",
            I64 => "i64",
            I128 => "i128",
            Usize => "usize",
            U8 => "u8",
            U16 => "u16",
            U32 => "u32",
            U64 => "u64",
            U128 => "u128",
            F32 => "f32",
            F64 => "f64",
            Str => "str",
            Bool => "bool",
            Char => "char",
            Array => "array",
            Slice => "slice",
            Tuple => "tuple",
            Unit => "unit",
            RawPointer => "pointer",
            Reference => "reference",
            Fn => "fn",
            Never => "never",
        }
    }

    pub fn to_url_str(&self) -> &'static str {
        self.as_str()
    }
}

impl From<ast::IntTy> for PrimitiveType {
    fn from(int_ty: ast::IntTy) -> PrimitiveType {
        match int_ty {
            ast::IntTy::Isize => PrimitiveType::Isize,
            ast::IntTy::I8 => PrimitiveType::I8,
            ast::IntTy::I16 => PrimitiveType::I16,
            ast::IntTy::I32 => PrimitiveType::I32,
            ast::IntTy::I64 => PrimitiveType::I64,
            ast::IntTy::I128 => PrimitiveType::I128,
        }
    }
}

impl From<ast::UintTy> for PrimitiveType {
    fn from(uint_ty: ast::UintTy) -> PrimitiveType {
        match uint_ty {
            ast::UintTy::Usize => PrimitiveType::Usize,
            ast::UintTy::U8 => PrimitiveType::U8,
            ast::UintTy::U16 => PrimitiveType::U16,
            ast::UintTy::U32 => PrimitiveType::U32,
            ast::UintTy::U64 => PrimitiveType::U64,
            ast::UintTy::U128 => PrimitiveType::U128,
        }
    }
}

impl From<ast::FloatTy> for PrimitiveType {
    fn from(float_ty: ast::FloatTy) -> PrimitiveType {
        match float_ty {
            ast::FloatTy::F32 => PrimitiveType::F32,
            ast::FloatTy::F64 => PrimitiveType::F64,
        }
    }
}

impl Clean<Type> for hir::Ty {
    fn clean(&self, cx: &DocContext) -> Type {
        use rustc::hir::*;
        match self.node {
            TyNever => Never,
            TyPtr(ref m) => RawPointer(m.mutbl.clean(cx), box m.ty.clean(cx)),
            TyRptr(ref l, ref m) => {
                let lifetime = if l.is_elided() {
                    None
                } else {
                    Some(l.clean(cx))
                };
                BorrowedRef {lifetime: lifetime, mutability: m.mutbl.clean(cx),
                             type_: box m.ty.clean(cx)}
            }
            TySlice(ref ty) => Slice(box ty.clean(cx)),
            TyArray(ref ty, n) => {
                let def_id = cx.tcx.hir.body_owner_def_id(n);
                let param_env = cx.tcx.param_env(def_id);
                let substs = Substs::identity_for_item(cx.tcx, def_id);
                let n = cx.tcx.const_eval(param_env.and((def_id, substs))).unwrap();
                let n = if let ConstVal::Integral(ConstInt::Usize(n)) = n.val {
                    n.to_string()
                } else if let ConstVal::Unevaluated(def_id, _) = n.val {
                    if let Some(node_id) = cx.tcx.hir.as_local_node_id(def_id) {
                        print_const_expr(cx, cx.tcx.hir.body_owned_by(node_id))
                    } else {
                        inline::print_inlined_const(cx, def_id)
                    }
                } else {
                    format!("{:?}", n)
                };
                Array(box ty.clean(cx), n)
            },
            TyTup(ref tys) => Tuple(tys.clean(cx)),
            TyPath(hir::QPath::Resolved(None, ref path)) => {
                if let Some(new_ty) = cx.ty_substs.borrow().get(&path.def).cloned() {
                    return new_ty;
                }

                let mut alias = None;
                if let Def::TyAlias(def_id) = path.def {
                    // Substitute private type aliases
                    if let Some(node_id) = cx.tcx.hir.as_local_node_id(def_id) {
                        if !cx.access_levels.borrow().is_exported(def_id) {
                            alias = Some(&cx.tcx.hir.expect_item(node_id).node);
                        }
                    }
                };

                if let Some(&hir::ItemTy(ref ty, ref generics)) = alias {
                    let provided_params = &path.segments.last().unwrap();
                    let mut ty_substs = FxHashMap();
                    let mut lt_substs = FxHashMap();
                    provided_params.with_parameters(|provided_params| {
                        for (i, ty_param) in generics.ty_params().enumerate() {
                            let ty_param_def = Def::TyParam(cx.tcx.hir.local_def_id(ty_param.id));
                            if let Some(ty) = provided_params.types.get(i).cloned() {
                                ty_substs.insert(ty_param_def, ty.into_inner().clean(cx));
                            } else if let Some(default) = ty_param.default.clone() {
                                ty_substs.insert(ty_param_def, default.into_inner().clean(cx));
                            }
                        }

                        for (i, lt_param) in generics.lifetimes().enumerate() {
                            if let Some(lt) = provided_params.lifetimes.get(i).cloned() {
                                if !lt.is_elided() {
                                    let lt_def_id = cx.tcx.hir.local_def_id(lt_param.lifetime.id);
                                    lt_substs.insert(lt_def_id, lt.clean(cx));
                                }
                            }
                        }
                    });
                    return cx.enter_alias(ty_substs, lt_substs, || ty.clean(cx));
                }
                resolve_type(cx, path.clean(cx), self.id)
            }
            TyPath(hir::QPath::Resolved(Some(ref qself), ref p)) => {
                let mut segments: Vec<_> = p.segments.clone().into();
                segments.pop();
                let trait_path = hir::Path {
                    span: p.span,
                    def: Def::Trait(cx.tcx.associated_item(p.def.def_id()).container.id()),
                    segments: segments.into(),
                };
                Type::QPath {
                    name: p.segments.last().unwrap().name.clean(cx),
                    self_type: box qself.clean(cx),
                    trait_: box resolve_type(cx, trait_path.clean(cx), self.id)
                }
            }
            TyPath(hir::QPath::TypeRelative(ref qself, ref segment)) => {
                let mut def = Def::Err;
                let ty = hir_ty_to_ty(cx.tcx, self);
                if let ty::TyProjection(proj) = ty.sty {
                    def = Def::Trait(proj.trait_ref(cx.tcx).def_id);
                }
                let trait_path = hir::Path {
                    span: self.span,
                    def,
                    segments: vec![].into(),
                };
                Type::QPath {
                    name: segment.name.clean(cx),
                    self_type: box qself.clean(cx),
                    trait_: box resolve_type(cx, trait_path.clean(cx), self.id)
                }
            }
            TyTraitObject(ref bounds, ref lifetime) => {
                match bounds[0].clean(cx).trait_ {
                    ResolvedPath { path, typarams: None, did, is_generic } => {
                        let mut bounds: Vec<_> = bounds[1..].iter().map(|bound| {
                            TraitBound(bound.clean(cx), hir::TraitBoundModifier::None)
                        }).collect();
                        if !lifetime.is_elided() {
                            bounds.push(RegionBound(lifetime.clean(cx)));
                        }
                        ResolvedPath {
                            path,
                            typarams: Some(bounds),
                            did,
                            is_generic,
                        }
                    }
                    _ => Infer // shouldn't happen
                }
            }
            TyBareFn(ref barefn) => BareFunction(box barefn.clean(cx)),
            TyImplTraitExistential(ref exist_ty, ref _lts) => ImplTrait(exist_ty.bounds.clean(cx)),
            TyInfer | TyErr => Infer,
            TyTypeof(..) => panic!("Unimplemented type {:?}", self.node),
        }
    }
}

impl<'tcx> Clean<Type> for Ty<'tcx> {
    fn clean(&self, cx: &DocContext) -> Type {
        match self.sty {
            ty::TyNever => Never,
            ty::TyBool => Primitive(PrimitiveType::Bool),
            ty::TyChar => Primitive(PrimitiveType::Char),
            ty::TyInt(int_ty) => Primitive(int_ty.into()),
            ty::TyUint(uint_ty) => Primitive(uint_ty.into()),
            ty::TyFloat(float_ty) => Primitive(float_ty.into()),
            ty::TyStr => Primitive(PrimitiveType::Str),
            ty::TySlice(ty) => Slice(box ty.clean(cx)),
            ty::TyArray(ty, n) => {
                let mut n = cx.tcx.lift(&n).unwrap();
                if let ConstVal::Unevaluated(def_id, substs) = n.val {
                    let param_env = cx.tcx.param_env(def_id);
                    n = cx.tcx.const_eval(param_env.and((def_id, substs))).unwrap()
                };
                let n = if let ConstVal::Integral(ConstInt::Usize(n)) = n.val {
                    n.to_string()
                } else if let ConstVal::Unevaluated(def_id, _) = n.val {
                    if let Some(node_id) = cx.tcx.hir.as_local_node_id(def_id) {
                        print_const_expr(cx, cx.tcx.hir.body_owned_by(node_id))
                    } else {
                        inline::print_inlined_const(cx, def_id)
                    }
                } else {
                    format!("{:?}", n)
                };
                Array(box ty.clean(cx), n)
            }
            ty::TyRawPtr(mt) => RawPointer(mt.mutbl.clean(cx), box mt.ty.clean(cx)),
            ty::TyRef(r, mt) => BorrowedRef {
                lifetime: r.clean(cx),
                mutability: mt.mutbl.clean(cx),
                type_: box mt.ty.clean(cx),
            },
            ty::TyFnDef(..) |
            ty::TyFnPtr(_) => {
                let ty = cx.tcx.lift(self).unwrap();
                let sig = ty.fn_sig(cx.tcx);
                BareFunction(box BareFunctionDecl {
                    unsafety: sig.unsafety(),
                    generic_params: Vec::new(),
                    decl: (cx.tcx.hir.local_def_id(ast::CRATE_NODE_ID), sig).clean(cx),
                    abi: sig.abi(),
                })
            }
            ty::TyAdt(def, substs) => {
                let did = def.did;
                let kind = match def.adt_kind() {
                    AdtKind::Struct => TypeKind::Struct,
                    AdtKind::Union => TypeKind::Union,
                    AdtKind::Enum => TypeKind::Enum,
                };
                inline::record_extern_fqn(cx, did, kind);
                let path = external_path(cx, &cx.tcx.item_name(did),
                                         None, false, vec![], substs);
                ResolvedPath {
                    path,
                    typarams: None,
                    did,
                    is_generic: false,
                }
            }
            ty::TyForeign(did) => {
                inline::record_extern_fqn(cx, did, TypeKind::Foreign);
                let path = external_path(cx, &cx.tcx.item_name(did),
                                         None, false, vec![], Substs::empty());
                ResolvedPath {
                    path: path,
                    typarams: None,
                    did: did,
                    is_generic: false,
                }
            }
            ty::TyDynamic(ref obj, ref reg) => {
                if let Some(principal) = obj.principal() {
                    let did = principal.def_id();
                    inline::record_extern_fqn(cx, did, TypeKind::Trait);

                    let mut typarams = vec![];
                    reg.clean(cx).map(|b| typarams.push(RegionBound(b)));
                    for did in obj.auto_traits() {
                        let empty = cx.tcx.intern_substs(&[]);
                        let path = external_path(cx, &cx.tcx.item_name(did),
                            Some(did), false, vec![], empty);
                        inline::record_extern_fqn(cx, did, TypeKind::Trait);
                        let bound = TraitBound(PolyTrait {
                            trait_: ResolvedPath {
                                path,
                                typarams: None,
                                did,
                                is_generic: false,
                            },
                            generic_params: Vec::new(),
                        }, hir::TraitBoundModifier::None);
                        typarams.push(bound);
                    }

                    let mut bindings = vec![];
                    for ty::Binder(ref pb) in obj.projection_bounds() {
                        bindings.push(TypeBinding {
                            name: cx.tcx.associated_item(pb.item_def_id).name.clean(cx),
                            ty: pb.ty.clean(cx)
                        });
                    }

                    let path = external_path(cx, &cx.tcx.item_name(did), Some(did),
                        false, bindings, principal.0.substs);
                    ResolvedPath {
                        path,
                        typarams: Some(typarams),
                        did,
                        is_generic: false,
                    }
                } else {
                    Never
                }
            }
            ty::TyTuple(ref t, _) => Tuple(t.clean(cx)),

            ty::TyProjection(ref data) => data.clean(cx),

            ty::TyParam(ref p) => Generic(p.name.to_string()),

            ty::TyAnon(def_id, substs) => {
                // Grab the "TraitA + TraitB" from `impl TraitA + TraitB`,
                // by looking up the projections associated with the def_id.
                let predicates_of = cx.tcx.predicates_of(def_id);
                let substs = cx.tcx.lift(&substs).unwrap();
                let bounds = predicates_of.instantiate(cx.tcx, substs);
                ImplTrait(bounds.predicates.into_iter().filter_map(|predicate| {
                    predicate.to_opt_poly_trait_ref().clean(cx)
                }).collect())
            }

            ty::TyClosure(..) | ty::TyGenerator(..) => Tuple(vec![]), // FIXME(pcwalton)

            ty::TyInfer(..) => panic!("TyInfer"),
            ty::TyError => panic!("TyError"),
        }
    }
}

impl Clean<Item> for hir::StructField {
    fn clean(&self, cx: &DocContext) -> Item {
        Item {
            name: Some(self.name).clean(cx),
            attrs: self.attrs.clean(cx),
            source: self.span.clean(cx),
            visibility: self.vis.clean(cx),
            stability: get_stability(cx, cx.tcx.hir.local_def_id(self.id)),
            deprecation: get_deprecation(cx, cx.tcx.hir.local_def_id(self.id)),
            def_id: cx.tcx.hir.local_def_id(self.id),
            inner: StructFieldItem(self.ty.clean(cx)),
        }
    }
}

impl<'tcx> Clean<Item> for ty::FieldDef {
    fn clean(&self, cx: &DocContext) -> Item {
        Item {
            name: Some(self.name).clean(cx),
            attrs: cx.tcx.get_attrs(self.did).clean(cx),
            source: cx.tcx.def_span(self.did).clean(cx),
            visibility: self.vis.clean(cx),
            stability: get_stability(cx, self.did),
            deprecation: get_deprecation(cx, self.did),
            def_id: self.did,
            inner: StructFieldItem(cx.tcx.type_of(self.did).clean(cx)),
        }
    }
}

#[derive(Clone, PartialEq, Eq, RustcDecodable, RustcEncodable, Debug)]
pub enum Visibility {
    Public,
    Inherited,
}

impl Clean<Option<Visibility>> for hir::Visibility {
    fn clean(&self, _: &DocContext) -> Option<Visibility> {
        Some(if *self == hir::Visibility::Public { Public } else { Inherited })
    }
}

impl Clean<Option<Visibility>> for ty::Visibility {
    fn clean(&self, _: &DocContext) -> Option<Visibility> {
        Some(if *self == ty::Visibility::Public { Public } else { Inherited })
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Struct {
    pub struct_type: doctree::StructType,
    pub generics: Generics,
    pub fields: Vec<Item>,
    pub fields_stripped: bool,
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Union {
    pub struct_type: doctree::StructType,
    pub generics: Generics,
    pub fields: Vec<Item>,
    pub fields_stripped: bool,
}

impl Clean<Vec<Item>> for doctree::Struct {
    fn clean(&self, cx: &DocContext) -> Vec<Item> {
        let mut ret = get_auto_traits_with_node_id(cx, self.id);

        ret.push(Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: StructItem(Struct {
                struct_type: self.struct_type,
                generics: self.generics.clean(cx),
                fields: self.fields.clean(cx),
                fields_stripped: false,
            }),
        });

        ret
    }
}

impl Clean<Vec<Item>> for doctree::Union {
    fn clean(&self, cx: &DocContext) -> Vec<Item> {
        let mut ret = get_auto_traits_with_node_id(cx, self.id);

        ret.push(Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: UnionItem(Union {
                struct_type: self.struct_type,
                generics: self.generics.clean(cx),
                fields: self.fields.clean(cx),
                fields_stripped: false,
            }),
        });

        ret
    }
}

/// This is a more limited form of the standard Struct, different in that
/// it lacks the things most items have (name, id, parameterization). Found
/// only as a variant in an enum.
#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct VariantStruct {
    pub struct_type: doctree::StructType,
    pub fields: Vec<Item>,
    pub fields_stripped: bool,
}

impl Clean<VariantStruct> for ::rustc::hir::VariantData {
    fn clean(&self, cx: &DocContext) -> VariantStruct {
        VariantStruct {
            struct_type: doctree::struct_type_from_def(self),
            fields: self.fields().iter().map(|x| x.clean(cx)).collect(),
            fields_stripped: false,
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Enum {
    pub variants: Vec<Item>,
    pub generics: Generics,
    pub variants_stripped: bool,
}

impl Clean<Vec<Item>> for doctree::Enum {
    fn clean(&self, cx: &DocContext) -> Vec<Item> {
        let mut ret = get_auto_traits_with_node_id(cx, self.id);

        ret.push(Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: EnumItem(Enum {
                variants: self.variants.clean(cx),
                generics: self.generics.clean(cx),
                variants_stripped: false,
            }),
        });

        ret
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Variant {
    pub kind: VariantKind,
}

impl Clean<Item> for doctree::Variant {
    fn clean(&self, cx: &DocContext) -> Item {
        Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            visibility: None,
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.def.id()),
            inner: VariantItem(Variant {
                kind: self.def.clean(cx),
            }),
        }
    }
}

impl<'tcx> Clean<Item> for ty::VariantDef {
    fn clean(&self, cx: &DocContext) -> Item {
        let kind = match self.ctor_kind {
            CtorKind::Const => VariantKind::CLike,
            CtorKind::Fn => {
                VariantKind::Tuple(
                    self.fields.iter().map(|f| cx.tcx.type_of(f.did).clean(cx)).collect()
                )
            }
            CtorKind::Fictive => {
                VariantKind::Struct(VariantStruct {
                    struct_type: doctree::Plain,
                    fields_stripped: false,
                    fields: self.fields.iter().map(|field| {
                        Item {
                            source: cx.tcx.def_span(field.did).clean(cx),
                            name: Some(field.name.clean(cx)),
                            attrs: cx.tcx.get_attrs(field.did).clean(cx),
                            visibility: field.vis.clean(cx),
                            def_id: field.did,
                            stability: get_stability(cx, field.did),
                            deprecation: get_deprecation(cx, field.did),
                            inner: StructFieldItem(cx.tcx.type_of(field.did).clean(cx))
                        }
                    }).collect()
                })
            }
        };
        Item {
            name: Some(self.name.clean(cx)),
            attrs: inline::load_attrs(cx, self.did),
            source: cx.tcx.def_span(self.did).clean(cx),
            visibility: Some(Inherited),
            def_id: self.did,
            inner: VariantItem(Variant { kind: kind }),
            stability: get_stability(cx, self.did),
            deprecation: get_deprecation(cx, self.did),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub enum VariantKind {
    CLike,
    Tuple(Vec<Type>),
    Struct(VariantStruct),
}

impl Clean<VariantKind> for hir::VariantData {
    fn clean(&self, cx: &DocContext) -> VariantKind {
        if self.is_struct() {
            VariantKind::Struct(self.clean(cx))
        } else if self.is_unit() {
            VariantKind::CLike
        } else {
            VariantKind::Tuple(self.fields().iter().map(|x| x.ty.clean(cx)).collect())
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Span {
    pub filename: FileName,
    pub loline: usize,
    pub locol: usize,
    pub hiline: usize,
    pub hicol: usize,
}

impl Span {
    pub fn empty() -> Span {
        Span {
            filename: FileName::Anon,
            loline: 0, locol: 0,
            hiline: 0, hicol: 0,
        }
    }
}

impl Clean<Span> for syntax_pos::Span {
    fn clean(&self, cx: &DocContext) -> Span {
        if *self == DUMMY_SP {
            return Span::empty();
        }

        let cm = cx.sess().codemap();
        let filename = cm.span_to_filename(*self);
        let lo = cm.lookup_char_pos(self.lo());
        let hi = cm.lookup_char_pos(self.hi());
        Span {
            filename,
            loline: lo.line,
            locol: lo.col.to_usize(),
            hiline: hi.line,
            hicol: hi.col.to_usize(),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct Path {
    pub global: bool,
    pub def: Def,
    pub segments: Vec<PathSegment>,
}

impl Path {
    pub fn singleton(name: String) -> Path {
        Path {
            global: false,
            def: Def::Err,
            segments: vec![PathSegment {
                name,
                params: PathParameters::AngleBracketed {
                    lifetimes: Vec::new(),
                    types: Vec::new(),
                    bindings: Vec::new()
                }
            }]
        }
    }

    pub fn last_name(&self) -> &str {
        self.segments.last().unwrap().name.as_str()
    }
}

impl Clean<Path> for hir::Path {
    fn clean(&self, cx: &DocContext) -> Path {
        Path {
            global: self.is_global(),
            def: self.def,
            segments: if self.is_global() { &self.segments[1..] } else { &self.segments }.clean(cx),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub enum PathParameters {
    AngleBracketed {
        lifetimes: Vec<Lifetime>,
        types: Vec<Type>,
        bindings: Vec<TypeBinding>,
    },
    Parenthesized {
        inputs: Vec<Type>,
        output: Option<Type>,
    }
}

impl Clean<PathParameters> for hir::PathParameters {
    fn clean(&self, cx: &DocContext) -> PathParameters {
        if self.parenthesized {
            let output = self.bindings[0].ty.clean(cx);
            PathParameters::Parenthesized {
                inputs: self.inputs().clean(cx),
                output: if output != Type::Tuple(Vec::new()) { Some(output) } else { None }
            }
        } else {
            PathParameters::AngleBracketed {
                lifetimes: if self.lifetimes.iter().all(|lt| lt.is_elided()) {
                    vec![]
                } else {
                    self.lifetimes.clean(cx)
                },
                types: self.types.clean(cx),
                bindings: self.bindings.clean(cx),
            }
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct PathSegment {
    pub name: String,
    pub params: PathParameters,
}

impl Clean<PathSegment> for hir::PathSegment {
    fn clean(&self, cx: &DocContext) -> PathSegment {
        PathSegment {
            name: self.name.clean(cx),
            params: self.with_parameters(|parameters| parameters.clean(cx))
        }
    }
}

fn strip_type(ty: Type) -> Type {
    match ty {
        Type::ResolvedPath { path, typarams, did, is_generic } => {
            Type::ResolvedPath { path: strip_path(&path), typarams, did, is_generic }
        },
        Type::Tuple(inner_tys) => {
            Type::Tuple(inner_tys.iter().map(|t| strip_type(t.clone())).collect())
        },
        Type::Slice(inner_ty) => Type::Slice(Box::new(strip_type(*inner_ty))),
        Type::Array(inner_ty, s) => Type::Array(Box::new(strip_type(*inner_ty)), s),
        Type::Unique(inner_ty) => Type::Unique(Box::new(strip_type(*inner_ty))),
        Type::RawPointer(m, inner_ty) => Type::RawPointer(m, Box::new(strip_type(*inner_ty))),
        Type::BorrowedRef { lifetime, mutability, type_ } => {
            Type::BorrowedRef { lifetime, mutability, type_: Box::new(strip_type(*type_)) }
        },
        Type::QPath { name, self_type, trait_ } => {
            Type::QPath { name, self_type: Box::new(strip_type(*self_type)), trait_: Box::new(strip_type(*trait_)) }
        },
        _ => ty
    }
}

fn strip_path(path: &Path) -> Path {
    let segments = path.segments.iter().map(|s| {
        PathSegment {
            name: s.name.clone(),
            params: PathParameters::AngleBracketed { lifetimes: Vec::new(), types: Vec::new(), bindings: Vec::new() }
        }
    }).collect();

    Path {
        global: path.global,
        def: path.def.clone(),
        segments
    }
}

fn qpath_to_string(p: &hir::QPath) -> String {
    let segments = match *p {
        hir::QPath::Resolved(_, ref path) => &path.segments,
        hir::QPath::TypeRelative(_, ref segment) => return segment.name.to_string(),
    };

    let mut s = String::new();
    for (i, seg) in segments.iter().enumerate() {
        if i > 0 {
            s.push_str("::");
        }
        if seg.name != keywords::CrateRoot.name() {
            s.push_str(&*seg.name.as_str());
        }
    }
    s
}

impl Clean<String> for ast::Name {
    fn clean(&self, _: &DocContext) -> String {
        self.to_string()
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Typedef {
    pub type_: Type,
    pub generics: Generics,
}

impl Clean<Item> for doctree::Typedef {
    fn clean(&self, cx: &DocContext) -> Item {
        Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id.clone()),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: TypedefItem(Typedef {
                type_: self.ty.clean(cx),
                generics: self.gen.clean(cx),
            }, false),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Debug, Hash)]
pub struct BareFunctionDecl {
    pub unsafety: hir::Unsafety,
    pub generic_params: Vec<GenericParam>,
    pub decl: FnDecl,
    pub abi: Abi,
}

impl Clean<BareFunctionDecl> for hir::BareFnTy {
    fn clean(&self, cx: &DocContext) -> BareFunctionDecl {
        BareFunctionDecl {
            unsafety: self.unsafety,
            generic_params: self.generic_params.clean(cx),
            decl: (&*self.decl, &self.arg_names[..]).clean(cx),
            abi: self.abi,
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Static {
    pub type_: Type,
    pub mutability: Mutability,
    /// It's useful to have the value of a static documented, but I have no
    /// desire to represent expressions (that'd basically be all of the AST,
    /// which is huge!). So, have a string.
    pub expr: String,
}

impl Clean<Item> for doctree::Static {
    fn clean(&self, cx: &DocContext) -> Item {
        debug!("cleaning static {}: {:?}", self.name.clean(cx), self);
        Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: StaticItem(Static {
                type_: self.type_.clean(cx),
                mutability: self.mutability.clean(cx),
                expr: print_const_expr(cx, self.expr),
            }),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Constant {
    pub type_: Type,
    pub expr: String,
}

impl Clean<Item> for doctree::Constant {
    fn clean(&self, cx: &DocContext) -> Item {
        Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: ConstantItem(Constant {
                type_: self.type_.clean(cx),
                expr: print_const_expr(cx, self.expr),
            }),
        }
    }
}

#[derive(Debug, Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Copy, Hash)]
pub enum Mutability {
    Mutable,
    Immutable,
}

impl Clean<Mutability> for hir::Mutability {
    fn clean(&self, _: &DocContext) -> Mutability {
        match self {
            &hir::MutMutable => Mutable,
            &hir::MutImmutable => Immutable,
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, PartialEq, Eq, Copy, Debug, Hash)]
pub enum ImplPolarity {
    Positive,
    Negative,
}

impl Clean<ImplPolarity> for hir::ImplPolarity {
    fn clean(&self, _: &DocContext) -> ImplPolarity {
        match self {
            &hir::ImplPolarity::Positive => ImplPolarity::Positive,
            &hir::ImplPolarity::Negative => ImplPolarity::Negative,
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Impl {
    pub unsafety: hir::Unsafety,
    pub generics: Generics,
    pub provided_trait_methods: FxHashSet<String>,
    pub trait_: Option<Type>,
    pub for_: Type,
    pub items: Vec<Item>,
    pub polarity: Option<ImplPolarity>,
    pub synthetic: bool,
}

pub fn get_auto_traits_with_node_id(cx: &DocContext, id: ast::NodeId) -> Vec<Item> {
    let finder = AutoTraitFinder { cx };
    finder.get_with_node_id(id)
}

pub fn get_auto_traits_with_def_id(cx: &DocContext, id: DefId) -> Vec<Item> {

    let finder = AutoTraitFinder {
        cx,
    };

    finder.get_with_def_id(id)
}

impl Clean<Vec<Item>> for doctree::Impl {
    fn clean(&self, cx: &DocContext) -> Vec<Item> {
        let mut ret = Vec::new();
        let trait_ = self.trait_.clean(cx);
        let items = self.items.clean(cx);

        // If this impl block is an implementation of the Deref trait, then we
        // need to try inlining the target's inherent impl blocks as well.
        if trait_.def_id() == cx.tcx.lang_items().deref_trait() {
            build_deref_target_impls(cx, &items, &mut ret);
        }

        let provided = trait_.def_id().map(|did| {
            cx.tcx.provided_trait_methods(did)
                  .into_iter()
                  .map(|meth| meth.name.to_string())
                  .collect()
        }).unwrap_or(FxHashSet());

        ret.push(Item {
            name: None,
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            inner: ImplItem(Impl {
                unsafety: self.unsafety,
                generics: self.generics.clean(cx),
                provided_trait_methods: provided,
                trait_,
                for_: self.for_.clean(cx),
                items,
                polarity: Some(self.polarity.clean(cx)),
                synthetic: false
            })
        });
        ret
    }
}

fn build_deref_target_impls(cx: &DocContext,
                            items: &[Item],
                            ret: &mut Vec<Item>) {
    use self::PrimitiveType::*;
    let tcx = cx.tcx;

    for item in items {
        let target = match item.inner {
            TypedefItem(ref t, true) => &t.type_,
            _ => continue,
        };
        let primitive = match *target {
            ResolvedPath { did, .. } if did.is_local() => continue,
            ResolvedPath { did, .. } => {
                ret.extend(inline::build_impls(cx, did, true));
                continue
            }
            _ => match target.primitive_type() {
                Some(prim) => prim,
                None => continue,
            }
        };
        let did = match primitive {
            Isize => tcx.lang_items().isize_impl(),
            I8 => tcx.lang_items().i8_impl(),
            I16 => tcx.lang_items().i16_impl(),
            I32 => tcx.lang_items().i32_impl(),
            I64 => tcx.lang_items().i64_impl(),
            I128 => tcx.lang_items().i128_impl(),
            Usize => tcx.lang_items().usize_impl(),
            U8 => tcx.lang_items().u8_impl(),
            U16 => tcx.lang_items().u16_impl(),
            U32 => tcx.lang_items().u32_impl(),
            U64 => tcx.lang_items().u64_impl(),
            U128 => tcx.lang_items().u128_impl(),
            F32 => tcx.lang_items().f32_impl(),
            F64 => tcx.lang_items().f64_impl(),
            Char => tcx.lang_items().char_impl(),
            Bool => None,
            Str => tcx.lang_items().str_impl(),
            Slice => tcx.lang_items().slice_impl(),
            Array => tcx.lang_items().slice_impl(),
            Tuple => None,
            Unit => None,
            RawPointer => tcx.lang_items().const_ptr_impl(),
            Reference => None,
            Fn => None,
            Never => None,
        };
        if let Some(did) = did {
            if !did.is_local() {
                inline::build_impl(cx, did, ret);
            }
        }
    }
}

impl Clean<Item> for doctree::AutoImpl {
    fn clean(&self, cx: &DocContext) -> Item {
        debug!("Cleaning AutoImpl: {:?}", self);


        Item {
            name: None,
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: Some(Public),
            stability: None,
            deprecation: None,
            inner: ImplItem(Impl {
                unsafety: self.unsafety,
                generics: Default::default(),
                provided_trait_methods: FxHashSet(),
                trait_: Some(self.trait_.clean(cx)),
                for_: Type::DotDot,
                items: Vec::new(),
                polarity: None,
                synthetic: false
            })
        }
    }
}

impl Clean<Item> for doctree::ExternCrate {
    fn clean(&self, cx: &DocContext) -> Item {
        Item {
            name: None,
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: DefId { krate: self.cnum, index: CRATE_DEF_INDEX },
            visibility: self.vis.clean(cx),
            stability: None,
            deprecation: None,
            inner: ExternCrateItem(self.name.clean(cx), self.path.clone())
        }
    }
}

impl Clean<Vec<Item>> for doctree::Import {
    fn clean(&self, cx: &DocContext) -> Vec<Item> {
        // We consider inlining the documentation of `pub use` statements, but we
        // forcefully don't inline if this is not public or if the
        // #[doc(no_inline)] attribute is present.
        // Don't inline doc(hidden) imports so they can be stripped at a later stage.
        let denied = self.vis != hir::Public || self.attrs.iter().any(|a| {
            a.name().unwrap() == "doc" && match a.meta_item_list() {
                Some(l) => attr::list_contains_name(&l, "no_inline") ||
                           attr::list_contains_name(&l, "hidden"),
                None => false,
            }
        });
        let path = self.path.clean(cx);
        let inner = if self.glob {
            Import::Glob(resolve_use_source(cx, path))
        } else {
            let name = self.name;
            if !denied {
                if let Some(items) = inline::try_inline(cx, path.def, name) {
                    return items;
                }
            }
            Import::Simple(name.clean(cx), resolve_use_source(cx, path))
        };
        vec![Item {
            name: None,
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            def_id: cx.tcx.hir.local_def_id(ast::CRATE_NODE_ID),
            visibility: self.vis.clean(cx),
            stability: None,
            deprecation: None,
            inner: ImportItem(inner)
        }]
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub enum Import {
    // use source as str;
    Simple(String, ImportSource),
    // use source::*;
    Glob(ImportSource)
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct ImportSource {
    pub path: Path,
    pub did: Option<DefId>,
}

impl Clean<Vec<Item>> for hir::ForeignMod {
    fn clean(&self, cx: &DocContext) -> Vec<Item> {
        let mut items = self.items.clean(cx);
        for item in &mut items {
            if let ForeignFunctionItem(ref mut f) = item.inner {
                f.abi = self.abi;
            }
        }
        items
    }
}

impl Clean<Item> for hir::ForeignItem {
    fn clean(&self, cx: &DocContext) -> Item {
        let inner = match self.node {
            hir::ForeignItemFn(ref decl, ref names, ref generics) => {
                ForeignFunctionItem(Function {
                    decl: (&**decl, &names[..]).clean(cx),
                    generics: generics.clean(cx),
                    unsafety: hir::Unsafety::Unsafe,
                    abi: Abi::Rust,
                    constness: hir::Constness::NotConst,
                })
            }
            hir::ForeignItemStatic(ref ty, mutbl) => {
                ForeignStaticItem(Static {
                    type_: ty.clean(cx),
                    mutability: if mutbl {Mutable} else {Immutable},
                    expr: "".to_string(),
                })
            }
            hir::ForeignItemType => {
                ForeignTypeItem
            }
        };
        Item {
            name: Some(self.name.clean(cx)),
            attrs: self.attrs.clean(cx),
            source: self.span.clean(cx),
            def_id: cx.tcx.hir.local_def_id(self.id),
            visibility: self.vis.clean(cx),
            stability: get_stability(cx, cx.tcx.hir.local_def_id(self.id)),
            deprecation: get_deprecation(cx, cx.tcx.hir.local_def_id(self.id)),
            inner,
        }
    }
}

// Utilities

trait ToSource {
    fn to_src(&self, cx: &DocContext) -> String;
}

impl ToSource for syntax_pos::Span {
    fn to_src(&self, cx: &DocContext) -> String {
        debug!("converting span {:?} to snippet", self.clean(cx));
        let sn = match cx.sess().codemap().span_to_snippet(*self) {
            Ok(x) => x.to_string(),
            Err(_) => "".to_string()
        };
        debug!("got snippet {}", sn);
        sn
    }
}

fn name_from_pat(p: &hir::Pat) -> String {
    use rustc::hir::*;
    debug!("Trying to get a name from pattern: {:?}", p);

    match p.node {
        PatKind::Wild => "_".to_string(),
        PatKind::Binding(_, _, ref p, _) => p.node.to_string(),
        PatKind::TupleStruct(ref p, ..) | PatKind::Path(ref p) => qpath_to_string(p),
        PatKind::Struct(ref name, ref fields, etc) => {
            format!("{} {{ {}{} }}", qpath_to_string(name),
                fields.iter().map(|&Spanned { node: ref fp, .. }|
                                  format!("{}: {}", fp.name, name_from_pat(&*fp.pat)))
                             .collect::<Vec<String>>().join(", "),
                if etc { ", ..." } else { "" }
            )
        }
        PatKind::Tuple(ref elts, _) => format!("({})", elts.iter().map(|p| name_from_pat(&**p))
                                            .collect::<Vec<String>>().join(", ")),
        PatKind::Box(ref p) => name_from_pat(&**p),
        PatKind::Ref(ref p, _) => name_from_pat(&**p),
        PatKind::Lit(..) => {
            warn!("tried to get argument name from PatKind::Lit, \
                  which is silly in function arguments");
            "()".to_string()
        },
        PatKind::Range(..) => panic!("tried to get argument name from PatKind::Range, \
                              which is not allowed in function arguments"),
        PatKind::Slice(ref begin, ref mid, ref end) => {
            let begin = begin.iter().map(|p| name_from_pat(&**p));
            let mid = mid.as_ref().map(|p| format!("..{}", name_from_pat(&**p))).into_iter();
            let end = end.iter().map(|p| name_from_pat(&**p));
            format!("[{}]", begin.chain(mid).chain(end).collect::<Vec<_>>().join(", "))
        },
    }
}

fn print_const_expr(cx: &DocContext, body: hir::BodyId) -> String {
    cx.tcx.hir.node_to_pretty_string(body.node_id)
}

/// Given a type Path, resolve it to a Type using the TyCtxt
fn resolve_type(cx: &DocContext,
                path: Path,
                id: ast::NodeId) -> Type {
    if id == ast::DUMMY_NODE_ID {
        debug!("resolve_type({:?})", path);
    } else {
        debug!("resolve_type({:?},{:?})", path, id);
    }

    let is_generic = match path.def {
        Def::PrimTy(p) => match p {
            hir::TyStr => return Primitive(PrimitiveType::Str),
            hir::TyBool => return Primitive(PrimitiveType::Bool),
            hir::TyChar => return Primitive(PrimitiveType::Char),
            hir::TyInt(int_ty) => return Primitive(int_ty.into()),
            hir::TyUint(uint_ty) => return Primitive(uint_ty.into()),
            hir::TyFloat(float_ty) => return Primitive(float_ty.into()),
        },
        Def::SelfTy(..) if path.segments.len() == 1 => {
            return Generic(keywords::SelfType.name().to_string());
        }
        Def::TyParam(..) if path.segments.len() == 1 => {
            return Generic(format!("{:#}", path));
        }
        Def::SelfTy(..) | Def::TyParam(..) | Def::AssociatedTy(..) => true,
        _ => false,
    };
    let did = register_def(&*cx, path.def);
    ResolvedPath { path: path, typarams: None, did: did, is_generic: is_generic }
}

fn register_def(cx: &DocContext, def: Def) -> DefId {
    debug!("register_def({:?})", def);

    let (did, kind) = match def {
        Def::Fn(i) => (i, TypeKind::Function),
        Def::TyAlias(i) => (i, TypeKind::Typedef),
        Def::Enum(i) => (i, TypeKind::Enum),
        Def::Trait(i) => (i, TypeKind::Trait),
        Def::Struct(i) => (i, TypeKind::Struct),
        Def::Union(i) => (i, TypeKind::Union),
        Def::Mod(i) => (i, TypeKind::Module),
        Def::TyForeign(i) => (i, TypeKind::Foreign),
        Def::Static(i, _) => (i, TypeKind::Static),
        Def::Variant(i) => (cx.tcx.parent_def_id(i).unwrap(), TypeKind::Enum),
        Def::SelfTy(Some(def_id), _) => (def_id, TypeKind::Trait),
        Def::SelfTy(_, Some(impl_def_id)) => {
            return impl_def_id
        }
        _ => return def.def_id()
    };
    if did.is_local() { return did }
    inline::record_extern_fqn(cx, did, kind);
    if let TypeKind::Trait = kind {
        inline::record_extern_trait(cx, did);
    }
    did
}

fn resolve_use_source(cx: &DocContext, path: Path) -> ImportSource {
    ImportSource {
        did: if path.def == Def::Err {
            None
        } else {
            Some(register_def(cx, path.def))
        },
        path,
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Macro {
    pub source: String,
    pub imported_from: Option<String>,
}

impl Clean<Item> for doctree::Macro {
    fn clean(&self, cx: &DocContext) -> Item {
        let name = self.name.clean(cx);
        Item {
            name: Some(name.clone()),
            attrs: self.attrs.clean(cx),
            source: self.whence.clean(cx),
            visibility: Some(Public),
            stability: self.stab.clean(cx),
            deprecation: self.depr.clean(cx),
            def_id: self.def_id,
            inner: MacroItem(Macro {
                source: format!("macro_rules! {} {{\n{}}}",
                                name,
                                self.matchers.iter().map(|span| {
                                    format!("    {} => {{ ... }};\n", span.to_src(cx))
                                }).collect::<String>()),
                imported_from: self.imported_from.clean(cx),
            }),
        }
    }
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Stability {
    pub level: stability::StabilityLevel,
    pub feature: String,
    pub since: String,
    pub deprecated_since: String,
    pub deprecated_reason: String,
    pub unstable_reason: String,
    pub issue: Option<u32>
}

#[derive(Clone, RustcEncodable, RustcDecodable, Debug)]
pub struct Deprecation {
    pub since: String,
    pub note: String,
}

impl Clean<Stability> for attr::Stability {
    fn clean(&self, _: &DocContext) -> Stability {
        Stability {
            level: stability::StabilityLevel::from_attr_level(&self.level),
            feature: self.feature.to_string(),
            since: match self.level {
                attr::Stable {ref since} => since.to_string(),
                _ => "".to_string(),
            },
            deprecated_since: match self.rustc_depr {
                Some(attr::RustcDeprecation {ref since, ..}) => since.to_string(),
                _=> "".to_string(),
            },
            deprecated_reason: match self.rustc_depr {
                Some(ref depr) => depr.reason.to_string(),
                _ => "".to_string(),
            },
            unstable_reason: match self.level {
                attr::Unstable { reason: Some(ref reason), .. } => reason.to_string(),
                _ => "".to_string(),
            },
            issue: match self.level {
                attr::Unstable {issue, ..} => Some(issue),
                _ => None,
            }
        }
    }
}

impl<'a> Clean<Stability> for &'a attr::Stability {
    fn clean(&self, dc: &DocContext) -> Stability {
        (**self).clean(dc)
    }
}

impl Clean<Deprecation> for attr::Deprecation {
    fn clean(&self, _: &DocContext) -> Deprecation {
        Deprecation {
            since: self.since.as_ref().map_or("".to_string(), |s| s.to_string()),
            note: self.note.as_ref().map_or("".to_string(), |s| s.to_string()),
        }
    }
}

/// An equality constraint on an associated type, e.g. `A=Bar` in `Foo<A=Bar>`
#[derive(Clone, PartialEq, Eq, RustcDecodable, RustcEncodable, Debug, Hash)]
pub struct TypeBinding {
    pub name: String,
    pub ty: Type
}

impl Clean<TypeBinding> for hir::TypeBinding {
    fn clean(&self, cx: &DocContext) -> TypeBinding {
        TypeBinding {
            name: self.name.clean(cx),
            ty: self.ty.clean(cx)
        }
    }
}

struct AutoTraitFinder<'a, 'tcx: 'a> {
    cx: &'a core::DocContext<'a, 'tcx>,
}

impl<'a, 'tcx> AutoTraitFinder<'a, 'tcx> {

    pub fn get_with_def_id(&self, def_id: DefId) -> Vec<Item> {
        let ty = self.cx.tcx.type_of(def_id);

        let def_ctor: fn(DefId) -> Def = match ty.sty {
            ty::TyAdt(adt, _) => {
                match adt.adt_kind() {
                    AdtKind::Struct => Def::Struct,
                    AdtKind::Enum => Def::Enum,
                    AdtKind::Union => Def::Union
                }
            }
            _ => panic!("Unexpected type {:?}", def_id)
        };

        self.get_auto_trait_impls(def_id, def_ctor)
    }

    pub fn get_with_node_id(&self, id: ast::NodeId) -> Vec<Item> {
        let item = &self.cx.tcx.hir.expect_item(id).node;
        let did = self.cx.tcx.hir.local_def_id(id);


        let def_ctor = match *item {
            hir::ItemStruct(_, _) => Def::Struct,
            hir::ItemUnion(_, _) => Def::Union,
            hir::ItemEnum(_, _) => Def::Enum,
            _ => panic!("Unexpected type {:?} {:?}", item, id)
        };

        self.get_auto_trait_impls(did, def_ctor)
    }

    pub fn get_auto_trait_impls(&self, def_id: DefId, def_ctor: fn(DefId) -> Def) -> Vec<Item> {

        if self.cx.tcx.get_attrs(def_id).lists("doc").has_word("hidden") {
            debug!("get_auto_trait_impls(def_id={:?}, def_ctor={:?}): item has doc('hidden'), aborting", def_id, def_ctor);
            return Vec::new()
        }

        let tcx = self.cx.tcx;
        let generics = self.cx.tcx.generics_of(def_id);


        debug!("get_auto_trait_impls(def_id={:?}, def_ctor={:?}, generics={:?}", def_id, def_ctor, generics);
        let auto_traits: Vec<_> = self.cx.send_trait.and_then(|send_trait| self.get_auto_trait_impl_for(def_id, generics.clone(), def_ctor, send_trait)).into_iter()
              .chain(self.get_auto_trait_impl_for(def_id, generics.clone(), def_ctor, tcx.require_lang_item(lang_items::SyncTraitLangItem)).into_iter())
              //.chain(self.get_auto_trait_impl_for(item.id, def_id, generics.clone(), def_ctor, tcx.require_lang_item(lang_items::SizedTraitLangItem)).into_iter())
              .collect();

        
        debug!("get_auto_traits: type {:?} auto_traits {:?}", def_id, auto_traits);
        auto_traits
    }

    fn get_auto_trait_impl_for(&self, def_id: DefId, generics: ty::Generics, def_ctor: fn(DefId) -> Def, trait_def_id: DefId) -> Option<Item> {
        if !self.cx.generated_synthetics.borrow_mut().insert((def_id, trait_def_id)) {
            debug!("get_auto_trait_impl_for(def_id={:?}, generics={:?}, def_ctor={:?}, trait_def_id={:?}): already generated, aborting", def_id, generics, def_ctor, trait_def_id);
            return None;
        }
        
        let result = self.find_auto_trait_generics(def_id, trait_def_id, &generics);

        if result.is_auto() {
            let trait_ = hir::TraitRef {
                path: get_path_for_type(self.cx.tcx, trait_def_id, hir::def::Def::Trait),
                ref_id: ast::DUMMY_NODE_ID
            };

            let polarity;

            let new_generics = match result {
                AutoTraitResult::PositiveImpl(new_generics) => {
                    polarity = None;
                    new_generics
                },
                AutoTraitResult::NegativeImpl => {
                    polarity = Some(ImplPolarity::Negative);

                    // For negative impls, we use the generic params, but *not* the predicates,
                    // from the original type. Otherwise, the displayed impl appears to be a
                    // conditional negative impl, when it's really unconditional.
                    //
                    // For example, consider the struct Foo<T: Copy>(*mut T). Using
                    // the original predicates in our impl would cause us to generate
                    // `impl !Send for Foo<T: Copy>`, which makes it appear that Foo
                    // implements Send where T is not copy.
                    //
                    // Instead, we generate `impl !Send for Foo<T>`, which better
                    // expresses the fact that `Foo<T>` never implements `Send`,
                    // regardless of the choice of `T`.
                    let real_generics = (&generics, &Default::default());

                    // Clean the generics, but ignore the '?Sized' bounds generated
                    // by the `Clean` impl
                    let clean_generics = real_generics.clean(self.cx);

                    Generics {
                        params: clean_generics.params,
                        where_predicates: Vec::new()
                    }
                },
                _ => unreachable!()
            };

            let path = get_path_for_type(self.cx.tcx, def_id, def_ctor);
            let mut segments = path.segments.into_vec();
            let last = segments.pop().unwrap();
            segments.push(hir::PathSegment::new(last.name, self.generics_to_path_params(generics.clone(), def_id.krate), false));

            let new_path = hir::Path {
                span: path.span,
                def: path.def,
                segments: HirVec::from_vec(segments)
            };

            let ty = hir::Ty {
                id: ast::DUMMY_NODE_ID,
                node: hir::Ty_::TyPath(hir::QPath::Resolved(None, P(new_path))),
                span: DUMMY_SP,
                hir_id: hir::DUMMY_HIR_ID
            };

            return Some(Item {
                source: Span::empty(),
                name: None,
                attrs: Default::default(),
                visibility: None,
                def_id: self.next_def_id(def_id.krate),
                stability: None,
                deprecation: None,
                inner: ImplItem(Impl {
                    unsafety: hir::Unsafety::Normal,
                    generics: new_generics,
                    provided_trait_methods: FxHashSet(),
                    trait_: Some(trait_.clean(self.cx)),
                    for_: ty.clean(self.cx),
                    items: Vec::new(),
                    polarity,
                    synthetic: true
                })
            });
        }
        None
    }

    fn generics_to_path_params(&self, generics: ty::Generics, cnum: CrateNum) -> hir::PathParameters {
        let lifetimes = HirVec::from_vec(generics.regions.iter().map(|p| {
            let name = if p.name == "" {
                hir::LifetimeName::Static
            } else {
                hir::LifetimeName::Name(p.name)
            };

            hir::Lifetime {
                id: ast::DUMMY_NODE_ID,
                span: DUMMY_SP,
                name
            }
        }).collect());
        let types = HirVec::from_vec(generics.types.iter().map(|p| P(self.ty_param_to_ty(p.clone(), cnum))).collect());

        hir::PathParameters {
            lifetimes: lifetimes,
            types: types,
            bindings: HirVec::new(),
            parenthesized: false
        }
    }

    fn ty_param_to_ty(&self, param: ty::TypeParameterDef, cnum: CrateNum) -> hir::Ty {
        debug!("ty_param_to_ty({:?}) {:?}", param, param.def_id);
        hir::Ty {
            id: ast::DUMMY_NODE_ID,
            node: hir::Ty_::TyPath(hir::QPath::Resolved(None, P(hir::Path {
                span: DUMMY_SP,
                def: Def::TyParam(param.def_id),
                segments: HirVec::from_vec(vec![hir::PathSegment::from_name(param.name)])
            }))),
            span: DUMMY_SP,
            hir_id: hir::DUMMY_HIR_ID
        }
    }

    fn find_auto_trait_generics(&self, did: DefId, trait_did: DefId, generics: &ty::Generics) -> AutoTraitResult {
        let tcx = self.cx.tcx;
        let ty = self.cx.tcx.type_of(did);

        let orig_params = tcx.param_env(did);


        let trait_ref = ty::TraitRef {
            def_id: trait_did,
            substs: tcx.mk_substs_trait(ty, &[]),
        };

        let trait_pred = ty::Binder(trait_ref);

        let bail_out = tcx.infer_ctxt().enter(|infcx| {
            let mut selcx = SelectionContext::with_negative(&infcx, true);
            let result = selcx.select(&Obligation::new(ObligationCause::dummy(), orig_params, trait_pred.to_poly_trait_predicate()));
            match result {
                Ok(Some(Vtable::VtableImpl(_))) => {
                    debug!("find_auto_trait_generics(did={:?}, trait_did={:?}, generics={:?}): manual impl found, bailing out", did, trait_did, generics);
                    return true
                },
                _ => return false
            };
        });

        // If an explicit impl exists, it always takes priority over an auto impl
        if bail_out {
            return AutoTraitResult::ExplicitImpl;
        }


        return tcx.infer_ctxt().enter(|mut infcx| {
            let mut result: Result<Option<ty::ParamEnv>, Option<Predicate>> = Ok(Some(orig_params.clone()));
            let mut last_env = orig_params;


            // We process the param env two times. The first time, we stop and save any 
            println!("Creating user-displayable param env: {:?} {:?}", ty, trait_did);
            let new_env = match self.evaluate_predicates(&mut infcx, trait_did, ty, orig_params, true) {
                Some(e) => e,
                None => return AutoTraitResult::NegativeImpl
            };

            println!("Creating full param env: {:?} {:?}", ty, trait_did);

            let full_env = self.evaluate_predicates(&mut infcx, trait_did, ty, orig_params, false).unwrap_or_else(|| panic!("Failed to fully process: {:?} {:?} {:?}", ty, trait_did, orig_params));

            println!("Attempting to fulfill for {:?} {:?} {:?}", ty, trait_did, full_env);
            println!("Clearing cache");
            infcx.clear_caches();

            let mut fulfill = FulfillmentContext::new();
            fulfill.register_bound(&infcx, full_env, ty, trait_did, ObligationCause::misc(DUMMY_SP, ast::DUMMY_NODE_ID));
            fulfill.select_all_or_error(&infcx).unwrap_or_else(|e| panic!("Unable to fulfill trait {:?} for '{:?}': {:?}", trait_did, ty, e));

            let names_map: FxHashMap<String, Lifetime> = generics.regions.iter().map(|l|  {
                    (l.name.as_str().to_string(), l.clean(self.cx))
            }).collect();

            let body_ids: FxHashSet<_> = infcx.region_obligations.borrow().iter().map(|&(id, _)| id).collect();

            println!("Previous constraints: {:?} {:?}", ty, infcx.borrow_region_constraints().region_constraint_data().constraints);

            for id in body_ids {
                infcx.process_registered_region_obligations(&[], None, new_env.clone(), id);
            }

            let region_data = infcx.take_and_reset_region_constraints();

            println!("Handle lifetimes: {:?} {:?}", region_data.constraints, names_map);
            let lifetime_predicates = self.handle_lifetimes(&region_data, &names_map);

            let new_generics = self.param_env_to_generics(did, new_env, generics.clone(), lifetime_predicates);
            debug!("find_auto_trait_generics(ty={:?}, did={:?}): {:?}", ty, did, new_generics);
            return AutoTraitResult::PositiveImpl(new_generics);

        });

    }

    fn evaluate_nested_obligations<'b, 'c, 'd, 'cx, T: Iterator<Item = Obligation<'cx, ty::Predicate<'cx>>>>(&self, ty: ty::Ty, nested: T, computed_preds: &'b mut Vec<ty::Predicate<'cx>>, predicates: &'b mut VecDeque<ty::Binder<ty::TraitPredicate<'cx>>>, stop_at_param: bool, select: &mut traits::SelectionContext<'c, 'd, 'cx>) -> bool {
        let dummy_cause = ObligationCause::misc(DUMMY_SP, ast::DUMMY_NODE_ID);

        for (obligation, predicate) in nested.filter(|o| o.recursion_depth == 1).map(|o| (o.clone(), o.predicate.clone())) {
            match &predicate {
                &ty::Predicate::Trait(ref p) => {
                    let substs = &p.skip_binder().trait_ref.substs;
                    let final_preds = self.extra_preds(select.infcx().tcx, &predicate);

                    if stop_at_param {
                        if self.is_of_param(substs) {
                            println!("Final bound for {:?} {:?}", ty, final_preds);
                            computed_preds.extend(final_preds);
                        } else {
                            println!("More processing for {:?} {:?} {:?}", ty, predicate, substs);
                            predicates.push_back(p.clone());
                        }
                    } else {
                        println!("Computed and more processing for {:?} {:?}", ty, final_preds);
                        computed_preds.extend(final_preds);
                        predicates.push_back(p.clone());
                    }
                },
                &ty::Predicate::Projection(p) => {
                    // If the projection isn't all type vars, then
                    // we don't want to add it as a bound
                    if self.is_of_param(p.skip_binder().projection_ty.substs) || !stop_at_param {
                        println!("Final projection bound for {:?} {:?}", ty, p);
                        println!("Fake normalized: {:?}", traits::poly_project_and_unify_type(select, &obligation.with(p.clone())));
                        computed_preds.push(predicate);
                    } else {
                        match traits::poly_project_and_unify_type(select, &obligation.with(p.clone())) {
                            Err(e) => {
                                println!("Unable to unify predicate '{:?}' '{:?}', bailing out", ty, e);
                                return false
                            },
                            Ok(Some(v)) => {
                                println!("Recursing with: {:?} {:?}", ty, v);
                                if !self.evaluate_nested_obligations(ty, v.clone().iter().cloned(), computed_preds, predicates, stop_at_param, select) {
                                    return false;
                                }
                            },
                            Ok(None) => panic!("Unexpected result when selecting {:?} {:?}", ty, obligation)
                        }
                    }
                },
                &ty::Predicate::RegionOutlives(ref binder) => {
                    if let Err(e) = select.infcx().region_outlives_predicate(&dummy_cause, binder) {
                        println!("Unable to add outlives predicate {:?} {:?} {:?} bailing out", ty, binder, e);
                        return false
                    }
                },
                &ty::Predicate::TypeOutlives(ref binder) => {
                    match (binder.no_late_bound_regions(), binder.map_bound_ref(|pred| pred.0).no_late_bound_regions()) {
                        (None, Some(t_a)) => {
                            select.infcx().register_region_obligation(ast::DUMMY_NODE_ID, RegionObligation {
                                sup_type: t_a,
                                sub_region: select.infcx().tcx.types.re_static,
                                cause: dummy_cause.clone()
                            });
                        },
                        (Some(ty::OutlivesPredicate(t_a, r_b)), _) => {
                            select.infcx().register_region_obligation(
                                ast::DUMMY_NODE_ID,
                                RegionObligation {
                                    sup_type: t_a,
                                    sub_region: r_b,
                                    cause: dummy_cause.clone()
                                }
                            );
                        },
                        _ => {}
                    };
                },
                _ => panic!("Unexpected predicate {:?} {:?}", ty, predicate)
            };
        }
        return true
    }

    fn evaluate_predicates<'b, 'gcx, 'c>(&self, infcx: &mut InferCtxt<'b, 'tcx, 'c>, trait_did: DefId, ty: ty::Ty<'c>, param_env: ty::ParamEnv<'c>, stop_at_param: bool) -> Option<ty::ParamEnv<'c>> {
        let tcx = infcx.tcx;

        let mut select = traits::SelectionContext::new(&infcx);

        let mut already_visited = FxHashSet();
        let mut predicates = VecDeque::new();
        predicates.push_back(ty::Binder(ty::TraitPredicate { trait_ref: ty::TraitRef {
            def_id: trait_did,
            substs: infcx.tcx.mk_substs_trait(ty, &[]),
        }}));

        // Duplicates are fine, as they get removed later
        let mut computed_preds: Vec<_> = param_env.caller_bounds.iter().map(|p| p.clone()).collect();

        let mut new_env = param_env.clone();
        let dummy_cause = ObligationCause::misc(DUMMY_SP, ast::DUMMY_NODE_ID);

        while let Some(pred) = predicates.pop_front() {
            infcx.clear_caches();

            if !already_visited.insert(pred.clone()) {
                continue;
            }

            let result = select.select(&Obligation::new(dummy_cause.clone(), new_env, pred));
            println!("Selected: {:?} {:?} {:?}", ty, pred, result);

            match &result {
                &Ok(Some(ref vtable)) => {
                    let obligations: Box<Iterator<Item=Obligation<ty::Predicate>>> = match vtable {
                        /*&Vtable::VtableImpl(ref data) => {
                            //let impl_trait_ref = tcx.impl_trait_ref(impl_def_id).unwrap();
                            let impl_substs = infcx.fresh_substs_for_item(DUMMY_SP, data.impl_def_id);


                            let mut obligations = Vec::new();

                            for predicate in tcx.predicates_of(data.impl_def_id).predicates {
                                let normalized = infcx.resolve_type_vars_if_possible(&traits::normalize(&mut select, new_env, dummy_cause.clone(), &predicate.subst(tcx, impl_substs)));
                                let mut pred = normalized.value.clone();

                                println!("Normalized: {:?}", normalized);
                                println!("Orig: {:?}", predicate);

                                match predicate {
                                    ty::Predicate::Projection(_) => {
                                        match normalized.value {
                                            ty::Predicate::Trait(ty::Binder(p)) => {
                                                if p.input_types().all(|t| {
                                                    match p.self_ty().sty {
                                                        ty::TyInfer(ty::TyVar(_)) => true,
                                                        _ => false
                                                    }
                                                }) {
                                                    println!("Found unnormalizeable predicate {:?} {:?} {:?}", ty, predicate, normalized);
                                                    pred = predicate;
                                                }
                                            },
                                            _ => {}
                                        }
                                    },
                                    _ => {}
                                }

                                obligations.push(Obligation {
                                    cause: dummy_cause.clone(),
                                    recursion_depth: 1,
                                    param_env: new_env.clone(),
                                    predicate: pred
                                });

                            }

                            println!("Orig obligations: {:?}", data.nested);
                            println!("Computed obligations: {:?}", obligations);

                            Box::new(obligations.into_iter())
                        },*/
                        _ => Box::new(vtable.clone().nested_obligations().into_iter())

                    };

                    if !self.evaluate_nested_obligations(ty, obligations, &mut computed_preds, &mut predicates, stop_at_param, &mut select) {
                        println!("evaluate_nested_obligations({:?}, {:?}) returned false, aborting", ty, vtable);
                        return None
                    }
                },
                &Ok(None) => {
                    println!("Found Ok(None) when evaluating, nothing more to do {:?} {:?} {:?}", ty, result, pred);
                },
                &Err(SelectionError::Unimplemented) => {
                    if self.is_of_param(pred.skip_binder().trait_ref.substs) || !stop_at_param {
                        println!("Creating and reprocessing trait bound {:?} {:?}", ty, pred);
                        already_visited.remove(&pred);
                        computed_preds.push(ty::Predicate::Trait(pred.clone()));
                        predicates.push_back(pred);
                    } else {
                        println!("Unimplemented found, bailing: {:?} {:?} {:?}", ty, pred, pred.skip_binder().trait_ref.substs);
                        return None
                    }
                },
                _ => panic!("Unexpected error for '{:?}': {:?}", ty, result)
            };

            println!("Lifting predicates: {:?} {:?}", ty, computed_preds);
            new_env = ty::ParamEnv::new(tcx.mk_predicates(computed_preds.iter()), param_env.reveal);
        }

        println!("Succeeded with {:?} {:?}", ty, new_env);

        return Some(new_env);
    }

    fn extra_preds<'b, 'c, 'd>(&self, tcx: TyCtxt<'b, 'c, 'd>, outer_pred: &ty::Predicate<'d>) -> Vec<ty::Predicate<'d>> {
        let mut extra = vec![outer_pred.clone()];
        extra

        /*let sized_trait = self.cx.tcx.require_lang_item(lang_items::SizedTraitLangItem);

        match outer_pred {
            &ty::Predicate::Trait(ty::Binder(ty::TraitPredicate { trait_ref } )) => {
                let outer_ty = trait_ref.substs.type_at(0);
                match outer_ty.sty {
                    ty::TyProjection(left_hand_proj) => {

                        let item = tcx.associated_item(left_hand_proj.item_def_id);
                        let inner_trait = item.container.assert_trait();
                        let trait_preds = tcx.predicates_of(inner_trait);
                        let param_ty = left_hand_proj.substs.type_at(0);

                        let mut sized_bound = None;
                        for trait_pred in trait_preds.predicates.iter() {
                            match trait_pred {
                               & ty::Predicate::Trait(ty::Binder(inner_pred)) => {
                                    match inner_pred.input_types().next().unwrap().sty {
                                        ty::TyProjection(inner_project) => {
                                            if inner_project.item_def_id == left_hand_proj.item_def_id {
                                                println!("Found matching: {:?}", inner_project);
                                                if inner_pred.def_id() == sized_trait {
                                                    println!("Found sized bound");

                                                    let substs = tcx.mk_substs(iter::once(Kind::from(outer_ty)));

                                                    let modified_sized = ty::Binder(ty::TraitRef {
                                                        def_id: sized_trait,
                                                        substs
                                                    }).to_predicate();

                                                    println!("Modified sized: {:?}", modified_sized);
                                                    sized_bound = Some(modified_sized);
                                                    break;
                                                }
                                            }
                                        },
                                        _ => {}
                                    };
                                },
                                _ => {}
                            }
                        }

                        extra.extend(sized_bound.iter());
                        //println!("Associated items generics: {:?} {:?}", p, preds);
                        println!("Item new preds: {:?} {:?}", item, trait_preds);
                    },
                    _ => {}
                }
            },
            _ => {}
        };
        println!("Extra preds: {:?} {:?}", outer_pred, extra);
        extra*/
    }


    // If the substs contains something other than a type parameter,
    // (e.g. a Cell<Foo>), then the FulfillmentContext was unable to find 
    // a matching impl. In that case, we're done, since the only thing
    // that we can do is add bounds on type parameters.
    //
    // For example, consider the type 'struct MyStruct<T>(T)'.
    // Let's say that we want to determine when, if at all, it implements `Sync`
    //
    // The FulfillmentContext will tell us that it doesn't fulfill
    // the `Sync` bound, returning us an erroring obligation for the trait ref `T: Sync`.
    // That trait ref only contains TyParams, which means that it's possible
    // for MyStruct to implement `Sync` when `T: Sync`. In other words, if a user
    // creates a MyStruct<u8>, `MyStruct<u8>: Sync` because `u8: Sync`
    //
    // For a counter example, consider the type `struct OtherStruct<*const T>(T)`
    // This time, the FulfillmentContext will tell us that it can't find an impl
    // for the trait ref `*const T: Sync`. The fact that the TyParam is still enclosed in another
    // type (a TyRawPtr) means that `*const T: Sync` will *never* be true.
    // Otherwise, the FulfillmentContext would have found an impl for `*const T:
    // Sync`, and started processing the nested obligation `T: Sync`
    //
    //

    fn is_of_param(&self, substs: &Substs) -> bool {
        if substs.is_noop() {
            return false
        }

        return match substs.type_at(0).sty {
            ty::TyParam(_) => true,
            ty::TyProjection(p) => self.is_of_param(p.substs),
            _ => false,
        }
    }

    fn get_lifetime(&self, region: Region, names_map: &FxHashMap<String, Lifetime>) -> Lifetime {
        self.region_name(region).map(|name| names_map.get(&name).unwrap_or_else(|| panic!("Missing lifetime with name {:?} for {:?}", name, region)))
                           .unwrap_or(&Lifetime::statik()).clone()
    }

    fn region_name(&self, region: Region) -> Option<String> {
        match region {
            &ty::ReEarlyBound(r) => {
                Some(r.name.as_str().to_string())
            },
            _ => None
        }
    }

    fn handle_lifetimes(&self, regions: &RegionConstraintData, names_map: &FxHashMap<String, Lifetime>) -> Vec<WherePredicate> {
        // Our goal is to 'flatten' the list of constraints by eliminating
        // all intermediate RegionVids. At the end, all constraints should
        // be between Regions (aka region variables). This gives us the information
        // we need to create the Generics
        //
        let mut finished = Vec::new();

        // A map from RegionVids to a tuple
        // of two vecs. The first vec 
        let mut vid_map: FxHashMap<RegionTarget, RegionDeps> = FxHashMap();
        
        for constraint in regions.constraints.keys() {
            match constraint {
                &Constraint::VarSubVar(r1, r2) => {
                    {
                        let deps1 = vid_map.entry(RegionTarget::RegionVid(r1)).or_insert_with(|| Default::default());
                        deps1.larger.insert(RegionTarget::RegionVid(r2));
                    }

                    let deps2 = vid_map.entry(RegionTarget::RegionVid(r2)).or_insert_with(|| Default::default());
                    deps2.smaller.insert(RegionTarget::RegionVid(r1));
                },
                &Constraint::RegSubVar(region, vid) => {
                    let deps = vid_map.entry(RegionTarget::RegionVid(vid)).or_insert_with(|| Default::default());
                    deps.smaller.insert(RegionTarget::Region(region));
                },
                &Constraint::VarSubReg(vid, region) => {
                    let deps = vid_map.entry(RegionTarget::RegionVid(vid)).or_insert_with(|| Default::default());
                    deps.larger.insert(RegionTarget::Region(region));
                },
                &Constraint::RegSubReg(r1, r2) => {
                    // The constraint is already in the form that we want, so we're done with it
                    // Desired order is 'larger, smaller', so flip then
                    if self.region_name(r1) != self.region_name(r2) {
                        finished.push((r2, r1));
                    }
                }
            }
        }

        while !vid_map.is_empty() {
            let target = vid_map.keys().next().expect("Keys somehow empty").clone();
            let deps = vid_map.remove(&target).expect("Entry somehow missing");

            for smaller in deps.smaller.iter() {

                for larger in deps.larger.iter() {
                    match (smaller, larger) {
                        (&RegionTarget::Region(r1), &RegionTarget::Region(r2)) => {
                            if self.region_name(r1) != self.region_name(r2) {
                                finished.push((r2, r1)) // Larger, smaller
                            }
                        },
                        (&RegionTarget::RegionVid(_), &RegionTarget::Region(_)) => {
                            if let Entry::Occupied(v) = vid_map.entry(*smaller) {
                                let smaller_deps = v.into_mut();
                                smaller_deps.larger.insert(*larger);
                                smaller_deps.larger.remove(&target);
                            }
                        },
                        (&RegionTarget::Region(_), &RegionTarget::RegionVid(_)) => {
                            if let Entry::Occupied(v) = vid_map.entry(*larger) {
                                let deps = v.into_mut();
                                deps.smaller.insert(*smaller);
                                deps.smaller.remove(&target);
                            }
                                                    },
                        (&RegionTarget::RegionVid(_), &RegionTarget::RegionVid(_)) => {
                            if let Entry::Occupied(v) = vid_map.entry(*smaller) {
                                let smaller_deps = v.into_mut();
                                smaller_deps.larger.insert(*larger);
                                smaller_deps.larger.remove(&target);
                            }

                            if let Entry::Occupied(v) = vid_map.entry(*larger) {
                                let larger_deps = v.into_mut();
                                larger_deps.smaller.insert(*smaller);
                                larger_deps.smaller.remove(&target);
                            }
                        }
                    }
                }
            }
        }

        let mut finished_map = FxHashMap();

        for &(larger, smaller) in finished.iter() {
            let larger_name = self.region_name(larger).expect("Missing larger name");

            finished_map.entry(larger_name).or_insert_with(|| Vec::new()).push(smaller);
        }

        let lifetime_predicates = names_map.iter().flat_map(|(name, lifetime)| {
            let empty = Vec::new();
            let bounds: FxHashSet<Lifetime> = finished_map.get(name).unwrap_or(&empty).iter().map(|region| {
                self.get_lifetime(region, names_map)
            }).collect();

            if bounds.is_empty() {
                return None
            }
            Some(WherePredicate::RegionPredicate {
                lifetime: lifetime.clone(),
                bounds: bounds.into_iter().collect()
            })
        }).collect();

        lifetime_predicates
    }

    fn param_env_to_generics(&self, did: DefId, param_env: ty::ParamEnv, type_generics: ty::Generics, mut existing_predicates: Vec<WherePredicate>) -> Generics {

        debug!("param_env_to_generics(did={:?}, param_env={:?}, type_generics={:?}, existing_predicates={:?})", did, param_env, type_generics, existing_predicates);


        // The `Sized` trait must be handled specially, since we only only display it when
        // it is *not* required (i.e. '?Sized')
        let sized_trait = self.cx.tcx.require_lang_item(lang_items::SizedTraitLangItem);


        let orig_bounds: FxHashSet<_> = self.cx.tcx.param_env(did).caller_bounds.iter().collect();
        let test_where_predicates = param_env.caller_bounds.iter().filter(|p| {
            !orig_bounds.contains(p) || match p {
                &&ty::Predicate::Trait(pred) => pred.def_id() == sized_trait,
                _ => false
            }
        }).map(|p| p.clean(self.cx));
        
        let full_generics = (&type_generics, &self.cx.tcx.predicates_of(did));
        let Generics { params: mut generic_params, where_predicates: old_where_predicates } = full_generics.clean(self.cx);



        let mut old_where_predicates = FxHashSet::from_iter(old_where_predicates.into_iter());


        let mut has_sized = FxHashSet();
        let mut ty_to_bounds = FxHashMap();
        let mut lifetime_to_bounds = FxHashMap();
        let mut ty_to_traits: FxHashMap<Type, FxHashSet<Type>> = FxHashMap();

        let mut ty_to_fn: FxHashMap<Type, (Option<PolyTrait>, Option<Type>)> = FxHashMap();

        test_where_predicates.for_each(|p| match p {
            WherePredicate::BoundPredicate { ty, bounds } => {

                // Writing a projection trait bound of the form
                // <T as Trait>::Name : ?Sized
                // is illegal, because ?Sized bounds can only
                // be written in the (here, nonexistant) definition
                // of the type.
                // Therefore, we make sure that we never add a ?Sized
                // bound for projections
                match &ty {
                    &Type::QPath { .. } => {
                        has_sized.insert(ty.clone());
                    },
                    _ => {}
                }

                if bounds.is_empty() {
                   return;
                }

                let mut has_fn = false;
                let mut new_bounds: Vec<TyParamBound> = bounds.into_iter().flat_map(|b| {

                    if b.is_sized_bound(self.cx) {
                        has_sized.insert(ty.clone());
                        return None;
                    }

                    // If we've already added a projection bound for the same type, don't add
                    // this, as it would be a duplicate
                    if b.get_trait_type().and_then(|t| ty_to_traits.get(&ty).map(|bounds| bounds.contains(&strip_type(t.clone())))).unwrap_or(false) {
                        return None
                    }

                    // Handle any 'Fn/FnOnce/FnMut' bounds specially,
                    // as we want to combine them with any 'Output' qpaths
                    // later
                    match &b {
                        &TyParamBound::TraitBound(ref p, _) => {
                            if self.is_fn_ty(&self.cx.tcx, &p.trait_) {
                                let out = 
                                ty_to_fn.entry(ty.clone())
                                    .and_modify(|e| *e = (Some(p.clone()), e.1.clone()))
                                    .or_insert((Some(p.clone()), None));

                                return None
                            }
                        },
                        _ => {}
                    }

                    return Some(b);
                }).collect();


                ty_to_bounds.entry(ty.clone()).or_insert_with(|| FxHashSet()).extend(new_bounds);
            },
            WherePredicate::RegionPredicate { lifetime, bounds } => {
                lifetime_to_bounds.entry(lifetime).or_insert_with(|| FxHashSet()).extend(bounds);
            }
            WherePredicate::EqPredicate { lhs, rhs } => {
                match &lhs {
                    &Type::QPath { name: ref left_name, ref self_type, ref trait_ } => {
                        let ty = &*self_type;
                        match **trait_ {
                            Type::ResolvedPath { path: ref trait_path, ref typarams, ref did, ref is_generic } => {
                                let mut new_trait_path = trait_path.clone();

                                if self.is_fn_ty(&self.cx.tcx, trait_) && left_name == FN_OUTPUT_NAME {
                                    ty_to_fn.entry(*ty.clone())
                                        .and_modify(|e| *e = (e.0.clone(), Some(rhs.clone())))
                                        .or_insert((None, Some(rhs)));
                                    return;

                                    /*ty_to_bounds.entry(*ty.clone()).or_insert_with(|| FxHashMap()).push(PolyTrait {
                                        trait_: trait_.clone(),
                                        generic_params: typarams.map_or_else(|| Vec::new(), |v| v.flat_map(|b| {
                                            match b {
                                                TyParamBound::RegionBound(l) => GenericParam::Lifetime(l),
                                                TyParamBound::TraitBound(t, modifier) => GenericParam::Type(TyParam {
                                                    name: 
                                                }
                                            }
                                        }
                                    }*/
                                }

                                // TODO: NLL
                                {
                                    let params = &mut new_trait_path.segments.last_mut().unwrap().params;

                                    match params {
                                        &mut PathParameters::AngleBracketed { ref lifetimes, ref types, ref mut bindings } => {
                                            bindings.push(TypeBinding {
                                                name: left_name.clone(),
                                                ty: rhs
                                            });
                                        },
                                        &mut PathParameters::Parenthesized { ref inputs, ref output } => {

                                            existing_predicates.push(WherePredicate::EqPredicate { lhs: lhs.clone(), rhs });
                                            return // Don't touch things like <T as FnMut>::Output == K
                                        }

                                    }
                                }


                                let bounds = ty_to_bounds.entry(*ty.clone()).or_insert_with(|| FxHashSet());
                                
                                bounds.insert(TyParamBound::TraitBound(PolyTrait {
                                    trait_: Type::ResolvedPath { path: new_trait_path, typarams: typarams.clone(), did: did.clone(), is_generic: *is_generic },
                                    generic_params: Vec::new()

                                }, hir::TraitBoundModifier::None));

                                // Remove any existing 'plain' bound (e.g. 'T: Iterator`) so that
                                // we don't see a duplicate bound like `T: Iterator + Iterator<Item=u8>`
                                // on the docs page.
                                bounds.remove(&TyParamBound::TraitBound(PolyTrait { trait_: *trait_.clone(), generic_params: Vec::new() }, hir::TraitBoundModifier::None));
                                // Avoid creating any new duplicate bounds
                                ty_to_traits.entry(*ty.clone()).or_insert_with(|| FxHashSet()).insert(*trait_.clone());


                            },
                            _ => panic!("Unexpected trait {:?} for {:?}", trait_, did)
                        }
                    },
                    _ => panic!("Unexpected LHS {:?} for {:?}", lhs, did)
                }
            }
        });

        let final_predicates = ty_to_bounds.into_iter().flat_map(|(ty, mut bounds)| {
            println!("ty_to_fn: {:?} {:?}", ty, ty_to_fn);
            if let Some(data) = ty_to_fn.get(&ty) {
                let (poly_trait, output) = (data.0.as_ref().unwrap().clone(), data.1.as_ref().cloned());
                let new_ty = match &poly_trait.trait_ {
                    &Type::ResolvedPath { ref path, ref typarams, ref did, ref is_generic } => {
                        let mut new_path = path.clone();
                        let last_segment = new_path.segments.pop().unwrap();

                        let (old_input, old_output) = match last_segment.params {
                            PathParameters::AngleBracketed { types, .. } => (types, None),
                            PathParameters::Parenthesized { inputs, output, .. } => (inputs, output)
                        };

                        if old_output.is_some() && old_output != output {
                            panic!("Output mismatch for {:?} {:?} {:?}", ty, old_output, data.1);
                        }

                        let new_params = PathParameters::Parenthesized {
                            inputs: old_input,
                            output
                        };

                        new_path.segments.push(PathSegment {
                            name: last_segment.name,
                            params: new_params
                        });

                        Type::ResolvedPath {
                            path: new_path,
                            typarams: typarams.clone(),
                            did: did.clone(),
                            is_generic: *is_generic
                        }
                    },
                    _ => panic!("Unexpected data: {:?}, {:?}", ty, data)
                };
                bounds.insert(TyParamBound::TraitBound(PolyTrait {
                    trait_: new_ty,
                    generic_params: poly_trait.generic_params
                }, hir::TraitBoundModifier::None));
            }
            if bounds.is_empty() {
                return None
            }

            Some(WherePredicate::BoundPredicate { ty, bounds: bounds.into_iter().collect() })
        }).chain(lifetime_to_bounds.into_iter().filter(|&(_, ref bounds)| !bounds.is_empty()).map(|(lifetime, bounds)| {
            WherePredicate::RegionPredicate { lifetime, bounds : bounds.into_iter().collect() }
        }));

        existing_predicates.extend(final_predicates);

        println!("Has sized: {:?}", has_sized);

        for p in generic_params.iter_mut() {
            match p {
                &mut GenericParam::Type(ref mut ty) => {
                    // We never want something like 'impl<T=Foo>'
                    ty.default.take();

                    let generic_ty = Type::Generic(ty.name.clone());

                    if !has_sized.contains(&generic_ty) {
                        ty.bounds.insert(0, TyParamBound::maybe_sized(self.cx));
                    }
                },
                _ => {}
            }
        }



        Generics {
            params: generic_params,
            where_predicates: existing_predicates
        }

    }

    fn is_fn_ty(&self, tcx: &TyCtxt, ty: &Type) -> bool {
        match &ty {
            &&Type::ResolvedPath { ref did, .. } => {
                   *did == tcx.require_lang_item(lang_items::FnTraitLangItem)
                || *did == tcx.require_lang_item(lang_items::FnMutTraitLangItem)
                || *did == tcx.require_lang_item(lang_items::FnOnceTraitLangItem)

            },
            _ => false
        }
    }

    fn next_def_id(&self, crate_num: CrateNum) -> DefId {

        let start_def_id = {
            let next_id = if crate_num == LOCAL_CRATE {
                self.cx.tcx.hir.definitions().def_path_table().next_id(DefIndexAddressSpace::Low)
            } else {
                self.cx.cstore.def_path_table(crate_num).next_id(DefIndexAddressSpace::Low)
            };

            DefId {
                krate: crate_num,
                index: next_id
            }

        };

        let mut fake_ids = self.cx.fake_def_ids.borrow_mut();

        let def_id = fake_ids.entry(crate_num).or_insert(start_def_id).clone();
        fake_ids.insert(crate_num, DefId {
            krate: crate_num,
            index: DefIndex::from_array_index(def_id.index.as_array_index() + 1, def_id.index.address_space())
        });

        MAX_DEF_ID.with(|m| {
            m.borrow_mut().entry(def_id.krate.clone()).or_insert(start_def_id);
        });

        self.cx.all_fake_def_ids.borrow_mut().insert(def_id);

        def_id.clone()
    }
}


pub fn def_id_to_path(cx: &DocContext, did: DefId, name: Option<String>) -> Vec<String> {
    let crate_name = name.unwrap_or_else(|| cx.tcx.crate_name(did.krate).to_string());
    let relative = cx.tcx.def_path(did).data.into_iter().filter_map(|elem| {
        // extern blocks have an empty name
        let s = elem.data.to_string();
        if !s.is_empty() {
            Some(s)
        } else {
            None
        }
    });
    once(crate_name).chain(relative).collect()
}


// Start of code copied from rust-clippy

pub fn get_trait_def_id(tcx: &TyCtxt, path: &[&str], use_local: bool) -> Option<DefId> {
    return if use_local {
        path_to_def_local(tcx, path)
    } else {
        path_to_def(tcx, path)
    };
}

pub fn path_to_def_local(tcx: &TyCtxt, path: &[&str]) -> Option<DefId> {
    let krate = tcx.hir.krate();
    let mut items = krate.module.item_ids.clone();
    let mut path_it = path.iter().peekable();

    loop {
        let segment = match path_it.next() {
            Some(segment) => segment,
            None => return None,
        };

        for item_id in mem::replace(&mut items, HirVec::new()).iter() {
            let item = tcx.hir.expect_item(item_id.id);
            if item.name == *segment {
                if path_it.peek().is_none() {
                    return Some(tcx.hir.local_def_id(item_id.id))
                }

                items = match &item.node {
                    &hir::ItemMod(ref m) => m.item_ids.clone(),
                    _ => panic!("Unexpected item {:?} in path {:?} path")
                };
                break;
            }
        }
    }

}

pub fn path_to_def(tcx: &TyCtxt, path: &[&str]) -> Option<DefId> {
    let crates = tcx.crates();


    let krate = crates
        .iter()
        .find(|&&krate| tcx.crate_name(krate) == path[0]);

    if let Some(krate) = krate {
        let krate = DefId {
            krate: *krate,
            index: CRATE_DEF_INDEX,
        };
        let mut items = tcx.item_children(krate);
        let mut path_it = path.iter().skip(1).peekable();

        loop {
            let segment = match path_it.next() {
                Some(segment) => segment,
                None => return None,
            };

            for item in mem::replace(&mut items, Rc::new(vec![])).iter() {
                if item.ident.name == *segment {
                    if path_it.peek().is_none() {
                        return match item.def {
                            def::Def::Trait(did) => Some(did),
                            _ => None
                        }
                    }

                    items = tcx.item_children(item.def.def_id());
                    break;
                }
            }
        }
    } else {
        None
    }
}

fn get_path_for_type(tcx: TyCtxt, def_id: DefId, def_ctor: fn(DefId) -> Def) -> hir::Path {
    struct AbsolutePathBuffer {
        names: Vec<String>,
    }

    impl ty::item_path::ItemPathBuffer for AbsolutePathBuffer {
        fn root_mode(&self) -> &ty::item_path::RootMode {
            const ABSOLUTE: &'static ty::item_path::RootMode = &ty::item_path::RootMode::Absolute;
            ABSOLUTE
        }

        fn push(&mut self, text: &str) {
            self.names.push(text.to_owned());
        }
    }

    let mut apb = AbsolutePathBuffer { names: vec![] };

    tcx.push_item_path(&mut apb, def_id);

    hir::Path {
        span: DUMMY_SP,
        def: def_ctor(def_id),
        segments: hir::HirVec::from_vec(apb.names.iter().map(|s| hir::PathSegment {
            name: ast::Name::intern(&s),
            parameters: None,
            infer_types: false
        }).collect())
    }
}

// End of code copied from rust-clippy


#[derive(Eq, PartialEq, Hash, Copy, Clone, Debug)]
enum RegionTarget<'tcx> {
    Region(Region<'tcx>),
    RegionVid(RegionVid)
}

#[derive(Default, Debug)]
struct RegionDeps<'tcx> {
    larger: FxHashSet<RegionTarget<'tcx>>,
    smaller: FxHashSet<RegionTarget<'tcx>>
}

#[derive(Eq, PartialEq, Hash, Debug)]
enum SimpleBound {
    RegionBound(Lifetime),
    TraitBound(Vec<PathSegment>, Vec<SimpleBound>, Vec<GenericParam>, hir::TraitBoundModifier)
}

enum AutoTraitResult {
    ExplicitImpl,

    PositiveImpl(Generics),

    NegativeImpl,
}

impl AutoTraitResult {

    fn is_auto(&self) -> bool {
        match *self {
            AutoTraitResult::PositiveImpl(_) | AutoTraitResult::NegativeImpl => true,
            _ => false
        }
    }
}

impl From<TyParamBound> for SimpleBound {

    fn from(bound: TyParamBound) -> Self {
        match bound.clone() {
            TyParamBound::RegionBound(l) => SimpleBound::RegionBound(l),
            TyParamBound::TraitBound(t, mod_) => match t.trait_ {
                Type::ResolvedPath { path, typarams, .. } => {
                    SimpleBound::TraitBound(path.segments, typarams.map_or_else(|| Vec::new(), |v| v.iter().map(|p| SimpleBound::from(p.clone())).collect()), t.generic_params, mod_)
                },
                _ => panic!("Unexpected bound {:?}", bound)
            }
        }
    }
}
