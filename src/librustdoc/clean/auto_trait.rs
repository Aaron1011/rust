use super::*;


pub struct AutoTraitFinder<'a, 'tcx: 'a, 'rcx: 'a> {
    pub cx: &'a core::DocContext<'a, 'tcx, 'rcx>,
}

impl<'a, 'tcx, 'rcx> AutoTraitFinder<'a, 'tcx, 'rcx> {

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

        self.get_auto_trait_impls(def_id, def_ctor, None)
    }

    pub fn get_with_node_id(&self, id: ast::NodeId, name: String) -> Vec<Item> {
        let item = &self.cx.tcx.hir.expect_item(id).node;
        let did = self.cx.tcx.hir.local_def_id(id);


        let def_ctor = match *item {
            hir::ItemStruct(_, _) => Def::Struct,
            hir::ItemUnion(_, _) => Def::Union,
            hir::ItemEnum(_, _) => Def::Enum,
            _ => panic!("Unexpected type {:?} {:?}", item, id)
        };

        self.get_auto_trait_impls(did, def_ctor, Some(name))
    }

    pub fn get_auto_trait_impls(&self, def_id: DefId, def_ctor: fn(DefId) -> Def, name: Option<String>) -> Vec<Item> {

        if self.cx.tcx.get_attrs(def_id).lists("doc").has_word("hidden") {
            debug!("get_auto_trait_impls(def_id={:?}, def_ctor={:?}): item has doc('hidden'), aborting", def_id, def_ctor);
            return Vec::new()
        }

        let tcx = self.cx.tcx;
        let generics = self.cx.tcx.generics_of(def_id);


        debug!("get_auto_trait_impls(def_id={:?}, def_ctor={:?}, generics={:?}", def_id, def_ctor, generics);
        let auto_traits: Vec<_> = self.cx.send_trait.and_then(|send_trait| self.get_auto_trait_impl_for(def_id, name.clone(), generics.clone(), def_ctor, send_trait)).into_iter()
              .chain(self.get_auto_trait_impl_for(def_id, name.clone(), generics.clone(), def_ctor, tcx.require_lang_item(lang_items::SyncTraitLangItem)).into_iter())
              .collect();

        
        debug!("get_auto_traits: type {:?} auto_traits {:?}", def_id, auto_traits);
        auto_traits
    }

    fn get_auto_trait_impl_for(&self, def_id: DefId, name: Option<String>, generics: ty::Generics, def_ctor: fn(DefId) -> Def, trait_def_id: DefId) -> Option<Item> {
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

            let real_name = name.as_ref().map(|n| Symbol::from(n.as_str()));

            segments.push(hir::PathSegment::new(real_name.unwrap_or(last.name), self.generics_to_path_params(generics.clone(), def_id.krate), false));

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


            let mut fresh_preds = FxHashSet();

            let (new_env, user_env) = match self.evaluate_predicates(&mut infcx, did, trait_did, ty, orig_params.clone(), orig_params, &mut fresh_preds, false) {
                Some(e) => e,
                None => return AutoTraitResult::NegativeImpl
            };

            // We clear out fresh_preds before reprocessing because the entire
            // point of reprocessing is to prefer certain properly-expanded predicates
            // (usually nested obligations of projections) that didn't have their proper
            // lifetimes inferred the first time around, due to missing predicates
            //fresh_preds.clear();

            let (full_env, full_user_env) = self.evaluate_predicates(&mut infcx, did, trait_did, ty, new_env.clone(), user_env, &mut fresh_preds, true).unwrap_or_else(|| panic!("Failed to fully process: {:?} {:?} {:?}", ty, trait_did, orig_params));

            debug!("find_auto_trait_generics(did={:?}, trait_did={:?}, generics={:?}): fulfilling with {:?}", did, trait_did, generics, full_env);
            infcx.clear_caches();

            let mut fulfill = FulfillmentContext::new();
            fulfill.register_bound(&infcx, full_env, ty, trait_did, ObligationCause::misc(DUMMY_SP, ast::DUMMY_NODE_ID));
            fulfill.select_all_or_error(&infcx).unwrap_or_else(|e| panic!("Unable to fulfill trait {:?} for '{:?}': {:?}", trait_did, ty, e));


            let names_map: FxHashMap<String, Lifetime> = generics.regions.iter().map(|l|  {
                    (l.name.as_str().to_string(), l.clean(self.cx))
            }).collect();

            let body_ids: FxHashSet<_> = infcx.region_obligations.borrow().iter().map(|&(id, _)| id).collect();


            for id in body_ids {
                infcx.process_registered_region_obligations(&[], None, full_env.clone(), id);
            }

            let region_data = infcx.borrow_region_constraints().region_constraint_data().clone();

            let (lifetime_predicates, vid_to_region) = self.handle_lifetimes(&region_data, &names_map);

            debug!("find_auto_trait_generics(did={:?}, trait_did={:?}, generics={:?}): computed lifetime information '{:?}' '{:?}'", did, trait_did, generics, lifetime_predicates, vid_to_region);


            let new_generics = self.param_env_to_generics(infcx.tcx, did, full_user_env, generics.clone(), lifetime_predicates, vid_to_region);
            debug!("find_auto_trait_generics(did={:?}, trait_did={:?}, generics={:?}): finished with {:?}", did, trait_did, generics, new_generics);
            return AutoTraitResult::PositiveImpl(new_generics);

        });

    }

    fn clean_project<'c, 'd, 'cx>(&self, infcx: &InferCtxt<'c, 'd, 'cx>, p: ty::PolyProjectionPredicate<'cx>) -> ty::PolyProjectionPredicate<'cx> {
        p.map_bound(|proj| {
            ty::ProjectionPredicate {
                projection_ty: ty::ProjectionTy {
                    substs: infcx.freshen(proj.projection_ty.substs),
                    item_def_id: proj.projection_ty.item_def_id
                },
                ty: infcx.freshen(proj.ty)
            }
        })
    }

    fn clean_pred<'c, 'd, 'cx>(&self, infcx: &InferCtxt<'c, 'd, 'cx>, p: ty::Predicate<'cx>) -> ty::Predicate<'cx> {
        infcx.freshen(p)
    }


    fn evaluate_nested_obligations<'b, 'c, 'd, 'cx, T: Iterator<Item = Obligation<'cx, ty::Predicate<'cx>>>>(&self, ty: ty::Ty, nested: T,
                                                                                                             computed_preds: &'b mut FxHashSet<ty::Predicate<'cx>>,
                                                                                                             fresh_preds: &'b mut FxHashSet<ty::Predicate<'cx>>,
                                                                                                             predicates: &'b mut VecDeque<ty::PolyTraitPredicate<'cx>>,
                                                                                                             select: &mut traits::SelectionContext<'c, 'd, 'cx>,
                                                                                                             only_projections: bool) -> bool {
        let dummy_cause = ObligationCause::misc(DUMMY_SP, ast::DUMMY_NODE_ID);

        for (obligation, predicate) in nested.filter(|o| o.recursion_depth == 1).map(|o| (o.clone(), o.predicate.clone())) {
            let is_new_pred = fresh_preds.insert(self.clean_pred(select.infcx(), predicate.clone()));

            match &predicate {
                &ty::Predicate::Trait(ref p) => {
                    let substs = &p.skip_binder().trait_ref.substs;

                    if self.is_of_param(substs) && !only_projections && is_new_pred {
                        computed_preds.insert(predicate);
                    }
                    predicates.push_back(p.clone());

                },
                &ty::Predicate::Projection(p) => {
                    // If the projection isn't all type vars, then
                    // we don't want to add it as a bound
                    if self.is_of_param(p.skip_binder().projection_ty.substs) && is_new_pred {
                        computed_preds.insert(predicate);
                    } else {
                        match traits::poly_project_and_unify_type(select, &obligation.with(p.clone())) {
                            Err(e) => {
                                debug!("evaluate_nested_obligations: Unable to unify predicate '{:?}' '{:?}', bailing out", ty, e);
                                return false
                            },
                            Ok(Some(v)) => {
                                if !self.evaluate_nested_obligations(ty, v.clone().iter().cloned(), computed_preds, fresh_preds, predicates, select, only_projections) {
                                    return false;
                                }
                            },
                            Ok(None) => panic!("Unexpected result when selecting {:?} {:?}", ty, obligation)
                        }
                    }
                },
                &ty::Predicate::RegionOutlives(ref binder) => {
                    if let Err(e) = select.infcx().region_outlives_predicate(&dummy_cause, binder) {
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

    fn evaluate_predicates<'b, 'gcx, 'c>(&self, infcx: &mut InferCtxt<'b, 'tcx, 'c>, ty_did: DefId, trait_did: DefId, ty: ty::Ty<'c>, param_env: ty::ParamEnv<'c>, user_env: ty::ParamEnv<'c>,
                                         fresh_preds: &mut FxHashSet<ty::Predicate<'c>>,
                                         only_projections: bool) -> Option<(ty::ParamEnv<'c>, ty::ParamEnv<'c>)> {
        let tcx = infcx.tcx;

        let mut select = traits::SelectionContext::new(&infcx);

        let mut already_visited = FxHashSet();
        let mut predicates = VecDeque::new();
        predicates.push_back(ty::Binder(ty::TraitPredicate { trait_ref: ty::TraitRef {
            def_id: trait_did,
            substs: infcx.tcx.mk_substs_trait(ty, &[]),
        }}));

        let mut computed_preds: FxHashSet<_> = param_env.caller_bounds.iter().cloned().collect();
        let mut user_computed_preds: FxHashSet<_> = user_env.caller_bounds.iter().cloned().collect();
        
        let mut new_env = param_env.clone();
        let dummy_cause = ObligationCause::misc(DUMMY_SP, ast::DUMMY_NODE_ID);

        while let Some(pred) = predicates.pop_front() {
            infcx.clear_caches();

            if !already_visited.insert(pred.clone()) {
                continue;
            }

            let result = select.select(&Obligation::new(dummy_cause.clone(), new_env, pred));

            match &result {
                &Ok(Some(ref vtable)) => {

                    let obligations = vtable.clone().nested_obligations().into_iter();


                    if !self.evaluate_nested_obligations(ty, obligations, &mut user_computed_preds, fresh_preds, &mut predicates, &mut select, only_projections) {
                        return None
                    }
                },
                &Ok(None) => {
                },
                &Err(SelectionError::Unimplemented) => {
                    if self.is_of_param(pred.skip_binder().trait_ref.substs) /*|| !stop_at_param*/ {
                        already_visited.remove(&pred);
                        user_computed_preds.insert(ty::Predicate::Trait(pred.clone()));
                        predicates.push_back(pred);
                    } else {
                        debug!("evaluate_nested_obligations: Unimplemented found, bailing: {:?} {:?} {:?}", ty, pred, pred.skip_binder().trait_ref.substs);
                        return None
                    }
                },
                _ => panic!("Unexpected error for '{:?}': {:?}", ty, result)
            };

            computed_preds.extend(user_computed_preds.iter().cloned());
            let normalized_preds = traits::elaborate_predicates(tcx, computed_preds.clone().into_iter().collect());
            new_env = ty::ParamEnv::new(tcx.mk_predicates(normalized_preds), param_env.reveal);
        }

        let final_user_env = ty::ParamEnv::new(tcx.mk_predicates(user_computed_preds.into_iter()), user_env.reveal);
        debug!("evaluate_nested_obligations(ty_did={:?}, trait_did={:?}): succeeded with '{:?}' '{:?}'", ty_did, trait_did, new_env, final_user_env);

        return Some((new_env, final_user_env));
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

    fn map_vid_to_region<'cx>(&self, regions: &RegionConstraintData<'cx>) -> FxHashMap<ty::RegionVid, ty::Region<'cx>> {

        let mut vid_map: FxHashMap<RegionTarget<'cx>, RegionDeps<'cx>> = FxHashMap();
        let mut finished_map = FxHashMap();

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
                    {
                        let deps1 = vid_map.entry(RegionTarget::Region(region)).or_insert_with(|| Default::default());
                        deps1.larger.insert(RegionTarget::RegionVid(vid));
                    }

                    let deps2 = vid_map.entry(RegionTarget::RegionVid(vid)).or_insert_with(|| Default::default());
                    deps2.smaller.insert(RegionTarget::Region(region));
                },
                &Constraint::VarSubReg(vid, region) => {
                    finished_map.insert(vid, region);
                },
                &Constraint::RegSubReg(r1, r2) => {
                    {
                        let deps1 = vid_map.entry(RegionTarget::Region(r1)).or_insert_with(|| Default::default());
                        deps1.larger.insert(RegionTarget::Region(r2));
                    }

                    let deps2 = vid_map.entry(RegionTarget::Region(r2)).or_insert_with(|| Default::default());
                    deps2.smaller.insert(RegionTarget::Region(r1));
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
                        },
                        (&RegionTarget::RegionVid(v1), &RegionTarget::Region(r1)) => {
                            finished_map.insert(v1, r1);
                        },
                        (&RegionTarget::Region(r), &RegionTarget::RegionVid(v)) => {
                            // Do nothing - we don't care about regions that are smaller than vids
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
        finished_map
    }

    fn handle_lifetimes<'cx>(&self, regions: &RegionConstraintData<'cx>, names_map: &FxHashMap<String, Lifetime>) -> (Vec<WherePredicate>, FxHashMap<ty::RegionVid, ty::Region<'cx>>) {
        // Our goal is to 'flatten' the list of constraints by eliminating
        // all intermediate RegionVids. At the end, all constraints should
        // be between Regions (aka region variables). This gives us the information
        // we need to create the Generics
        //
        let mut finished = Vec::new();

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

        let vid_to_region = self.map_vid_to_region(regions);

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


        (lifetime_predicates, vid_to_region)
    }

    fn param_env_to_generics<'b, 'c, 'cx>(&self, tcx: TyCtxt<'b, 'c, 'cx>, did: DefId, param_env: ty::ParamEnv<'cx>, type_generics: ty::Generics, mut existing_predicates: Vec<WherePredicate>,
                                          vid_to_region: FxHashMap<ty::RegionVid, ty::Region<'cx>>) -> Generics {

        debug!("param_env_to_generics(did={:?}, param_env={:?}, type_generics={:?}, existing_predicates={:?})", did, param_env, type_generics, existing_predicates);


        // The `Sized` trait must be handled specially, since we only only display it when
        // it is *not* required (i.e. '?Sized')
        let sized_trait = self.cx.tcx.require_lang_item(lang_items::SizedTraitLangItem);



        let mut replacer = RegionReplacer {
            vid_to_region: &vid_to_region,
            tcx
        };

        let orig_bounds: FxHashSet<_> = self.cx.tcx.param_env(did).caller_bounds.iter().collect();
        let test_where_predicates = param_env.caller_bounds.iter().filter(|p| {
            !orig_bounds.contains(p) || match p {
                &&ty::Predicate::Trait(pred) => pred.def_id() == sized_trait,
                _ => false
            }
        }).map(|p| {
            let replaced = p.fold_with(&mut replacer);
            (replaced.clone(), replaced.clean(self.cx))
        });
        
        let full_generics = (&type_generics, &tcx.predicates_of(did));
        let Generics { params: mut generic_params, where_predicates: old_where_predicates } = full_generics.clean(self.cx);



        let mut old_where_predicates = FxHashSet::from_iter(old_where_predicates.into_iter());


        let mut has_sized = FxHashSet();
        let mut ty_to_bounds = FxHashMap();
        let mut lifetime_to_bounds = FxHashMap();
        let mut ty_to_traits: FxHashMap<Type, FxHashSet<Type>> = FxHashMap();

        let mut ty_to_fn: FxHashMap<Type, (Option<PolyTrait>, Option<Type>)> = FxHashMap();

        test_where_predicates.for_each(|(orig_p, p)| {

            
            match p {
                WherePredicate::BoundPredicate { ty, mut bounds } => {

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


                    let mut for_generics: FxHashSet<_> = orig_p.walk_tys().flat_map(|t| {
                        let mut regions = FxHashSet();
                        tcx.collect_regions(&t, &mut regions);

                        regions.into_iter().flat_map(|r| {
                            match r {
                                // We only care about late bound regions, as we need to add them
                                // to the 'for<>' section
                                &ty::ReLateBound(_, ty::BoundRegion::BrNamed(_, name)) => {
                                    Some(GenericParam::Lifetime(Lifetime(name.as_str().to_string())))
                                },
                                &ty::ReVar(_) | &ty::ReEarlyBound(_) => {
                                    None
                                },
                                _ => panic!("Unexpected region type {:?}", r)
                            }
                        })
                    }).collect();


                    assert!(bounds.len() == 1);
                    let mut b = bounds.pop().unwrap();

                    let mut has_fn = false;

                    if b.is_sized_bound(self.cx) {
                        has_sized.insert(ty.clone());

                    // If we've already added a projection bound for the same type, don't add
                    // this, as it would be a duplicate

                    } else if !b.get_trait_type().and_then(|t| ty_to_traits.get(&ty).map(|bounds| bounds.contains(&strip_type(t.clone())))).unwrap_or(false) {

                        // Handle any 'Fn/FnOnce/FnMut' bounds specially,
                        // as we want to combine them with any 'Output' qpaths
                        // later

                        let is_fn = match &mut b {
                            &mut TyParamBound::TraitBound(ref mut p, _) => {
                                // Add existing regions to clean_regions to ensure
                                // that we don't add duplicates
                                for_generics.extend(p.generic_params.clone());
                                p.generic_params = for_generics.into_iter().collect();
                                self.is_fn_ty(&tcx, &p.trait_)
                            },
                            _ => false
                        };

                        let poly_trait = b.get_poly_trait().unwrap();

                        if is_fn {
                            ty_to_fn.entry(ty.clone())
                                .and_modify(|e| *e = (Some(poly_trait.clone()), e.1.clone()))
                                .or_insert(((Some(poly_trait.clone())), None));

                            ty_to_bounds.entry(ty.clone()).or_insert_with(|| FxHashSet());

                        } else {
                            ty_to_bounds.entry(ty.clone()).or_insert_with(|| FxHashSet()).insert(b.clone());
                        }
                    }
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

                                    if self.is_fn_ty(&tcx, trait_) && left_name == FN_OUTPUT_NAME {
                                        ty_to_fn.entry(*ty.clone())
                                            .and_modify(|e| *e = (e.0.clone(), Some(rhs.clone())))
                                            .or_insert((None, Some(rhs)));
                                        return;
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
            };
        });

        let final_predicates = ty_to_bounds.into_iter().flat_map(|(ty, mut bounds)| {
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

struct RegionReplacer<'a, 'gcx: 'a+'tcx, 'tcx: 'a> {
    vid_to_region: &'a FxHashMap<ty::RegionVid, ty::Region<'tcx>>,
    tcx: TyCtxt<'a, 'gcx, 'tcx>
}

impl<'a, 'gcx, 'tcx> TypeFolder<'gcx, 'tcx> for RegionReplacer<'a, 'gcx, 'tcx> {

    fn tcx<'b>(&'b self) -> TyCtxt<'b, 'gcx, 'tcx> {
        self.tcx
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        (match r {
            &ty::ReVar(vid) => {
                self.vid_to_region.get(&vid).cloned()
            },
            _ => None
        }).unwrap_or_else(|| r.super_fold_with(self))
    }
}
