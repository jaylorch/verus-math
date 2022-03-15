use crate::attributes::{get_trigger, get_var_mode, get_verifier_attrs, parse_attrs, Attr};
use crate::context::BodyCtxt;
use crate::def::is_get_variant_fn_name;
use crate::erase::ResolvedCall;
use crate::rust_to_vir_base::{
    def_id_to_vir_path, def_to_path_ident, get_function_def, get_range, hack_get_def_name,
    ident_to_var, is_smt_arith, is_smt_equality, mid_ty_simplify, mid_ty_to_vir, mk_range,
    typ_of_node, typ_of_node_expect_mut_ref, typ_path_and_ident_to_vir_path,
};
use crate::util::{
    err_span_str, err_span_string, slice_vec_map_result, spanned_new, spanned_typed_new,
    unsupported_err_span, vec_map, vec_map_result,
};
use crate::{unsupported, unsupported_err, unsupported_err_unless, unsupported_unless};
use air::ast::{Binder, BinderX, Quant};
use air::ast_util::str_ident;
use rustc_ast::{Attribute, BorrowKind, Mutability};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    BinOpKind, BindingAnnotation, Block, Destination, Expr, ExprKind, Guard, Local, LoopSource,
    Node, Pat, PatKind, QPath, Stmt, StmtKind, UnOp,
};
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::{PredicateKind, TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    ArmX, BinaryOp, CallTarget, Constant, ExprX, FunX, HeaderExpr, HeaderExprX, Ident, IntRange,
    InvAtomicity, Mode, PatternX, SpannedTyped, StmtX, Stmts, Typ, TypX, UnaryOp, UnaryOpr, VarAt,
    VirErr,
};
use vir::ast_util::{ident_binder, path_as_rust_name};
use vir::def::positional_field_ident;

pub(crate) fn pat_to_var<'tcx>(pat: &Pat) -> String {
    let (_, name) = pat_to_mut_var(pat);
    name
}

pub(crate) fn pat_to_mut_var<'tcx>(pat: &Pat) -> (bool, String) {
    let Pat { hir_id: _, kind, span: _, default_binding_modes } = pat;
    unsupported_unless!(default_binding_modes, "default_binding_modes");
    match kind {
        PatKind::Binding(annotation, _id, ident, pat) => {
            let mutable = match annotation {
                BindingAnnotation::Unannotated => false,
                BindingAnnotation::Mutable => true,
                _ => {
                    unsupported!(format!("binding annotation {:?}", annotation))
                }
            };
            match pat {
                None => {}
                _ => {
                    unsupported!(format!("pattern {:?}", kind))
                }
            }
            (mutable, ident_to_var(ident))
        }
        _ => {
            unsupported!(format!("pattern {:?}", kind))
        }
    }
}

fn extract_array<'tcx>(expr: &'tcx Expr<'tcx>) -> Vec<&'tcx Expr<'tcx>> {
    match &expr.kind {
        ExprKind::Array(fields) => fields.iter().collect(),
        _ => vec![expr],
    }
}

fn extract_tuple<'tcx>(expr: &'tcx Expr<'tcx>) -> Vec<&'tcx Expr<'tcx>> {
    match &expr.kind {
        ExprKind::Tup(exprs) => exprs.iter().collect(),
        _ => vec![expr],
    }
}

fn get_ensures_arg<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    if matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
        expr_to_vir(bctx, expr, ExprModifier::REGULAR)
    } else {
        err_span_str(expr.span, "ensures needs a bool expression")
    }
}

fn closure_param_typs<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr<'tcx>) -> Vec<Typ> {
    let node_type = bctx.types.node_type(expr.hir_id);
    match node_type.kind() {
        TyKind::Closure(_def, substs) => {
            let sig = substs.as_closure().sig();
            let args: Vec<Typ> = sig
                .inputs()
                .skip_binder()
                .iter()
                .map(|t| mid_ty_to_vir(bctx.ctxt.tcx, t, false /* allow_mut_ref */))
                .collect();
            assert!(args.len() == 1);
            match &*args[0] {
                TypX::Tuple(typs) => (**typs).clone(),
                _ => panic!("expected tuple type"),
            }
        }
        _ => panic!("closure_param_types expected Closure type"),
    }
}

fn extract_ensures<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Result<HeaderExpr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let typs: Vec<Typ> = closure_param_typs(bctx, expr);
            let body = tcx.hir().body(*body_id);
            let xs: Vec<String> = body.params.iter().map(|param| pat_to_var(param.pat)).collect();
            let expr = &body.value;
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(bctx, e))?;
            if typs.len() == 1 && xs.len() == 1 {
                let id_typ = Some((Arc::new(xs[0].clone()), typs[0].clone()));
                Ok(Arc::new(HeaderExprX::Ensures(id_typ, Arc::new(args))))
            } else {
                err_span_str(expr.span, "expected 1 parameter in closure")
            }
        }
        _ => {
            let args = vec_map_result(&extract_array(expr), |e| get_ensures_arg(bctx, e))?;
            Ok(Arc::new(HeaderExprX::Ensures(None, Arc::new(args))))
        }
    }
}

fn extract_quant<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    quant: Quant,
    expr: &'tcx Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let body = tcx.hir().body(*body_id);
            let typs = closure_param_typs(bctx, expr);
            assert!(typs.len() == body.params.len());
            let binders: Vec<Binder<Typ>> = body
                .params
                .iter()
                .zip(typs)
                .map(|(x, t)| Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)), a: t }))
                .collect();
            let expr = &body.value;
            let mut vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut vir_expr)?;
            if header.require.len() + header.ensure.len() > 0 {
                return err_span_str(expr.span, "forall/ensures cannot have requires/ensures");
            }
            let typ = Arc::new(TypX::Bool);
            if !matches!(bctx.types.node_type(expr.hir_id).kind(), TyKind::Bool) {
                return err_span_str(expr.span, "forall/ensures needs a bool expression");
            }
            Ok(spanned_typed_new(span, &typ, ExprX::Quant(quant, Arc::new(binders), vir_expr)))
        }
        _ => err_span_str(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn extract_assert_forall_by<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    expr: &'tcx Expr<'tcx>,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let body = tcx.hir().body(*body_id);
            let typs = closure_param_typs(bctx, expr);
            assert!(body.params.len() == typs.len());
            let binders: Vec<Binder<Typ>> = body
                .params
                .iter()
                .zip(typs)
                .map(|(x, t)| Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)), a: t }))
                .collect();
            let expr = &body.value;
            let mut vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            let header = vir::headers::read_header(&mut vir_expr)?;
            if header.require.len() > 1 {
                return err_span_str(expr.span, "assert_forall_by can have at most one requires");
            }
            if header.ensure.len() != 1 {
                return err_span_str(expr.span, "assert_forall_by must have exactly one ensures");
            }
            if header.ensure_id_typ.is_some() {
                return err_span_str(expr.span, "ensures clause must be a bool");
            }
            let typ = Arc::new(TypX::Tuple(Arc::new(vec![])));
            let vars = Arc::new(binders);
            let require = if header.require.len() == 1 {
                header.require[0].clone()
            } else {
                spanned_typed_new(span, &Arc::new(TypX::Bool), ExprX::Const(Constant::Bool(true)))
            };
            let ensure = header.ensure[0].clone();
            let forallx = ExprX::Forall { vars, require, ensure, proof: vir_expr };
            Ok(spanned_typed_new(span, &typ, forallx))
        }
        _ => err_span_str(expr.span, "argument to forall/exists must be a closure"),
    }
}

fn extract_choose<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    expr: &'tcx Expr<'tcx>,
    tuple: bool,
    expr_typ: Typ,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    match &expr.kind {
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let closure_body = tcx.hir().body(*body_id);
            let mut params: Vec<Binder<Typ>> = Vec::new();
            let mut vars: Vec<vir::ast::Expr> = Vec::new();
            let typs = closure_param_typs(bctx, expr);
            assert!(closure_body.params.len() == typs.len());
            for (x, typ) in closure_body.params.iter().zip(typs) {
                let name = Arc::new(pat_to_var(x.pat));
                vars.push(spanned_typed_new(x.span, &typ, ExprX::Var(name.clone())));
                params.push(Arc::new(BinderX { name, a: typ }));
            }
            let typs = vec_map(&params, |p| p.a.clone());
            let cond_expr = &closure_body.value;
            let cond = expr_to_vir(bctx, cond_expr, ExprModifier::REGULAR)?;
            let body = if tuple {
                let typ = Arc::new(TypX::Tuple(Arc::new(typs)));
                if !vir::ast_util::types_equal(&typ, &expr_typ) {
                    return err_span_string(
                        expr.span,
                        format!(
                            "expected choose_tuple to have type {:?}, found type {:?}",
                            typ, expr_typ
                        ),
                    );
                }
                spanned_typed_new(span, &typ, ExprX::Tuple(Arc::new(vars)))
            } else {
                if params.len() != 1 {
                    return err_span_str(
                        expr.span,
                        "choose expects exactly one parameter (use choose_tuple for multiple parameters)",
                    );
                }
                vars[0].clone()
            };
            let params = Arc::new(params);
            Ok(spanned_typed_new(span, &body.clone().typ, ExprX::Choose { params, cond, body }))
        }
        _ => err_span_str(expr.span, "argument to choose must be a closure"),
    }
}

fn mk_clip<'tcx>(range: &IntRange, expr: &vir::ast::Expr) -> vir::ast::Expr {
    match range {
        IntRange::Int => expr.clone(),
        range => SpannedTyped::new(
            &expr.span,
            &Arc::new(TypX::Int(*range)),
            ExprX::Unary(UnaryOp::Clip(*range), expr.clone()),
        ),
    }
}

fn mk_ty_clip<'tcx>(typ: &Typ, expr: &vir::ast::Expr) -> vir::ast::Expr {
    mk_clip(&get_range(typ), expr)
}

pub(crate) fn expr_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let mut vir_expr = expr_to_vir_inner(bctx, expr, modifier)?;
    for group in get_trigger(bctx.ctxt.tcx.hir().attrs(expr.hir_id))? {
        vir_expr = vir_expr.new_x(ExprX::Unary(UnaryOp::Trigger(group), vir_expr.clone()));
    }
    Ok(vir_expr)
}

fn record_fun(
    ctxt: &crate::context::Context,
    span: Span,
    name: &vir::ast::Fun,
    is_spec: bool,
    is_compilable_operator: bool,
) {
    let mut erasure_info = ctxt.erasure_info.borrow_mut();
    let resolved_call = if is_spec {
        ResolvedCall::Spec
    } else if is_compilable_operator {
        ResolvedCall::CompilableOperator
    } else {
        ResolvedCall::Call(name.clone())
    };
    erasure_info.resolved_calls.push((span.data(), resolved_call));
}

fn get_fn_path<'tcx>(bctx: &BodyCtxt<'tcx>, expr: &Expr<'tcx>) -> Result<vir::ast::Fun, VirErr> {
    match &expr.kind {
        ExprKind::Path(qpath) => {
            let id = bctx.types.qpath_res(qpath, expr.hir_id).def_id();
            if let Some(_) =
                bctx.ctxt.tcx.impl_of_method(id).and_then(|ii| bctx.ctxt.tcx.trait_id_of_impl(ii))
            {
                unsupported_err!(expr.span, format!("Fn {:?}", id))
            } else {
                Ok(Arc::new(FunX { path: def_id_to_vir_path(bctx.ctxt.tcx, id), trait_path: None }))
            }
        }
        _ => unsupported_err!(expr.span, format!("{:?}", expr)),
    }
}

const BUILTIN_INV_LOCAL_BEGIN: &str = "crate::pervasive::invariants::open_local_invariant_begin";
const BUILTIN_INV_BEGIN: &str = "crate::pervasive::invariants::open_invariant_begin";
const BUILTIN_INV_END: &str = "crate::pervasive::invariants::open_invariant_end";

fn fn_call_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    f: DefId,
    node_substs: &[rustc_middle::ty::subst::GenericArg<'tcx>],
    fn_span: Span,
    args_slice: &'tcx [Expr<'tcx>],
    autoview_typ: Option<&Typ>,
) -> Result<vir::ast::Expr, VirErr> {
    let mut args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();

    let tcx = bctx.ctxt.tcx;
    let path = if let Some(autoview_typ) = autoview_typ {
        if let TypX::Datatype(type_path, _) = &**autoview_typ {
            // If the function call was originally Foo::X with autoview type Bar,
            // then use the function Bar::X instead.
            typ_path_and_ident_to_vir_path(type_path, def_to_path_ident(tcx, f))
        } else {
            panic!("autoview_typ must be Datatype");
        }
    } else {
        def_id_to_vir_path(tcx, f)
    };

    let is_get_variant = {
        match tcx.hir().get_if_local(f) {
            Some(rustc_hir::Node::ImplItem(
                impl_item @ rustc_hir::ImplItem {
                    kind: rustc_hir::ImplItemKind::Fn(..),
                    ident: fn_ident,
                    ..
                },
            )) => {
                let fn_attrs = bctx.ctxt.tcx.hir().attrs(impl_item.hir_id());
                let fn_vattrs = get_verifier_attrs(fn_attrs)?;
                if fn_vattrs.is_variant {
                    Some(is_get_variant_fn_name(fn_ident).expect("invalid is_variant function"))
                } else {
                    None
                }
            }
            _ => None,
        }
    };

    let f_name = path_as_rust_name(&def_id_to_vir_path(tcx, f));
    let is_admit = f_name == "builtin::admit";
    let is_requires = f_name == "builtin::requires";
    let is_ensures = f_name == "builtin::ensures";
    let is_invariant = f_name == "builtin::invariant";
    let is_decreases = f_name == "builtin::decreases";
    let is_opens_invariants_none = f_name == "builtin::opens_invariants_none";
    let is_opens_invariants_any = f_name == "builtin::opens_invariants_any";
    let is_opens_invariants = f_name == "builtin::opens_invariants";
    let is_opens_invariants_except = f_name == "builtin::opens_invariants_except";
    let is_forall = f_name == "builtin::forall";
    let is_exists = f_name == "builtin::exists";
    let is_choose = f_name == "builtin::choose";
    let is_choose_tuple = f_name == "builtin::choose_tuple";
    let is_equal = f_name == "builtin::equal";
    let is_hide = f_name == "builtin::hide";
    let is_extra_dependency = f_name == "builtin::extra_dependency";
    let is_reveal = f_name == "builtin::reveal";
    let is_reveal_fuel = f_name == "builtin::reveal_with_fuel";
    let is_implies = f_name == "builtin::imply";
    let is_assert_by = f_name == "builtin::assert_by";
    let is_assert_forall_by = f_name == "builtin::assert_forall_by";
    let is_assert_bit_vector = f_name == "builtin::assert_bit_vector";
    let is_old = f_name == "builtin::old";
    let is_eq = f_name == "core::cmp::PartialEq::eq";
    let is_ne = f_name == "core::cmp::PartialEq::ne";
    let is_le = f_name == "core::cmp::PartialOrd::le";
    let is_ge = f_name == "core::cmp::PartialOrd::ge";
    let is_lt = f_name == "core::cmp::PartialOrd::lt";
    let is_gt = f_name == "core::cmp::PartialOrd::gt";
    let is_add = f_name == "core::ops::arith::Add::add";
    let is_sub = f_name == "core::ops::arith::Sub::sub";
    let is_mul = f_name == "core::ops::arith::Mul::mul";
    let is_spec = is_admit
        || is_requires
        || is_ensures
        || is_invariant
        || is_decreases
        || is_opens_invariants_none
        || is_opens_invariants_any
        || is_opens_invariants
        || is_opens_invariants_except;
    let is_quant = is_forall || is_exists;
    let is_directive = is_extra_dependency || is_hide || is_reveal || is_reveal_fuel;
    let is_cmp = is_equal || is_eq || is_ne || is_le || is_ge || is_lt || is_gt;
    let is_arith_binary = is_add || is_sub || is_mul;

    if f_name == BUILTIN_INV_BEGIN || f_name == BUILTIN_INV_LOCAL_BEGIN || f_name == BUILTIN_INV_END
    {
        // `open_invariant_begin` and `open_invariant_end` calls should only appear
        // through use of the `open_invariant!` macro, which creates an invariant block.
        // Thus, they should end up being processed by `invariant_block_to_vir` before
        // we get here. Thus, for any well-formed use of an invariant block, we should
        // not reach this point.
        return err_span_string(
            expr.span,
            format!("{} should never be used except through open_invariant macro", f_name),
        );
    }

    if bctx.external_body
        && !is_requires
        && !is_ensures
        && !is_opens_invariants_none
        && !is_opens_invariants_any
        && !is_opens_invariants
        && !is_opens_invariants_except
        && !is_extra_dependency
    {
        return Ok(spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Bool),
            ExprX::Block(Arc::new(vec![]), None),
        ));
    }

    unsupported_err_unless!(
        bctx.ctxt
            .tcx
            .impl_of_method(f)
            .and_then(|method_def_id| bctx.ctxt.tcx.trait_id_of_impl(method_def_id))
            .is_none(),
        expr.span,
        "call of trait impl"
    );
    let name = Arc::new(FunX { path: path.clone(), trait_path: None });

    record_fun(
        &bctx.ctxt,
        fn_span,
        &name,
        is_spec
            || is_quant
            || is_directive
            || is_choose
            || is_choose_tuple
            || is_assert_by
            || is_assert_forall_by
            || is_assert_bit_vector
            || is_old
            || is_get_variant.is_some(),
        is_implies,
    );

    let len = args.len();
    let expr_typ = || typ_of_node(bctx, &expr.hir_id, false);
    let mk_expr = |x: ExprX| spanned_typed_new(expr.span, &expr_typ(), x);
    let mk_expr_span = |span: Span, x: ExprX| spanned_typed_new(span, &expr_typ(), x);

    if is_requires {
        unsupported_err_unless!(len == 1, expr.span, "expected requires", &args);
        let bctx = &BodyCtxt { external_body: false, ..bctx.clone() };
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "requires needs a bool expression");
            }
        }
        let vir_args = vec_map_result(&args, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
        let header = Arc::new(HeaderExprX::Requires(Arc::new(vir_args)));
        return Ok(mk_expr(ExprX::Header(header)));
    }
    if is_opens_invariants || is_opens_invariants_except {
        return err_span_str(
            expr.span,
            "'is_opens_invariants' and 'is_opens_invariants_except' are not yet implemented",
        );
    }
    if is_opens_invariants_none {
        let header = Arc::new(HeaderExprX::InvariantOpens(Arc::new(Vec::new())));
        return Ok(mk_expr(ExprX::Header(header)));
    }
    if is_opens_invariants_any {
        let header = Arc::new(HeaderExprX::InvariantOpensExcept(Arc::new(Vec::new())));
        return Ok(mk_expr(ExprX::Header(header)));
    }
    if is_ensures {
        unsupported_err_unless!(len == 1, expr.span, "expected ensures", &args);
        let bctx = &BodyCtxt { external_body: false, ..bctx.clone() };
        let header = extract_ensures(&bctx, args[0])?;
        let expr = mk_expr_span(args[0].span, ExprX::Header(header));
        // extract_ensures does most of the necessary work, so we can return at this point
        return Ok(expr);
    }
    if is_invariant {
        unsupported_err_unless!(len == 1, expr.span, "expected invariant", &args);
        args = extract_array(args[0]);
        for arg in &args {
            if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                return err_span_str(arg.span, "invariant needs a bool expression");
            }
        }
    }
    if is_decreases {
        unsupported_err_unless!(len == 1, expr.span, "expected decreases", &args);
        args = extract_tuple(args[0]);
    }
    if is_forall || is_exists {
        unsupported_err_unless!(len == 1, expr.span, "expected forall/exists", &args);
        let quant = if is_forall { Quant::Forall } else { Quant::Exists };
        return extract_quant(bctx, expr.span, quant, args[0]);
    }
    if is_choose {
        unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
        return extract_choose(bctx, expr.span, args[0], false, expr_typ());
    }
    if is_choose_tuple {
        unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
        return extract_choose(bctx, expr.span, args[0], true, expr_typ());
    }
    if is_old {
        if let ExprKind::Path(QPath::Resolved(None, rustc_hir::Path { res: Res::Local(id), .. })) =
            &args[0].kind
        {
            if let Node::Binding(pat) = tcx.hir().get(*id) {
                let typ = typ_of_node_expect_mut_ref(bctx, &expr.hir_id, args[0].span)?;
                return Ok(spanned_typed_new(
                    expr.span,
                    &typ,
                    ExprX::VarAt(Arc::new(pat_to_var(pat)), VarAt::Pre),
                ));
            }
        }
        return err_span_str(
            expr.span,
            "only a variable binding is allowed as the argument to old",
        );
    }

    if is_extra_dependency || is_hide || is_reveal {
        unsupported_err_unless!(len == 1, expr.span, "expected hide/reveal", &args);
        let x = get_fn_path(bctx, &args[0])?;
        if is_hide {
            let header = Arc::new(HeaderExprX::Hide(x));
            return Ok(mk_expr(ExprX::Header(header)));
        } else if is_extra_dependency {
            let header = Arc::new(HeaderExprX::ExtraDependency(x));
            return Ok(mk_expr(ExprX::Header(header)));
        } else {
            return Ok(mk_expr(ExprX::Fuel(x, 1)));
        }
    }
    if is_reveal_fuel {
        unsupported_err_unless!(len == 2, expr.span, "expected reveal_fuel", &args);
        let x = get_fn_path(bctx, &args[0])?;
        match &expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?.x {
            ExprX::Const(Constant::Nat(s)) => {
                let n = s.parse::<u32>().expect(&format!("internal error: parse {}", s));
                return Ok(mk_expr(ExprX::Fuel(x, n)));
            }
            _ => panic!("internal error: is_reveal_fuel"),
        }
    }
    if is_assert_by {
        unsupported_err_unless!(len == 2, expr.span, "expected assert_by", &args);
        let vars = Arc::new(vec![]);
        let require =
            spanned_typed_new(expr.span, &Arc::new(TypX::Bool), ExprX::Const(Constant::Bool(true)));
        let ensure = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        let proof = expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?;
        return Ok(mk_expr(ExprX::Forall { vars, require, ensure, proof }));
    }
    if is_assert_forall_by {
        unsupported_err_unless!(len == 1, expr.span, "expected assert_forall_by", &args);
        return extract_assert_forall_by(bctx, expr.span, args[0]);
    }

    if is_assert_bit_vector {
        let expr = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
        return Ok(mk_expr(ExprX::AssertBV(expr)));
    }

    let inputs: Box<dyn Iterator<Item = Option<_>>> = if let Some(f_local) = f.as_local() {
        let f_hir_id = bctx.ctxt.tcx.hir().local_def_id_to_hir_id(f_local);
        let inputs = get_function_def(bctx.ctxt.tcx, f_hir_id).0.decl.inputs;
        Box::new(inputs.iter().map(Some).into_iter())
    } else {
        Box::new(std::iter::repeat(None))
    };
    let mut vir_args = args
        .iter()
        .zip(inputs)
        .map(|(arg, param)| {
            let is_mut_ref_param = match param {
                Some(rustc_hir::Ty {
                    kind:
                        rustc_hir::TyKind::Rptr(
                            _,
                            rustc_hir::MutTy { mutbl: rustc_hir::Mutability::Mut, .. },
                        ),
                    ..
                }) => true,
                _ => false,
            };
            if is_mut_ref_param {
                let arg_x = match &arg.kind {
                    ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e) => e,
                    _ => arg,
                };
                let expr = expr_to_vir(bctx, arg_x, ExprModifier::ADDR_OF)?;
                Ok(spanned_typed_new(arg.span, &expr.typ.clone(), ExprX::Loc(expr)))
            } else {
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, ExprModifier::REGULAR)?)
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let self_path = if let Some(autoview_typ) = autoview_typ {
        // replace f(arg0, arg1, ..., argn) with f(arg0.view(), arg1, ..., argn)
        let typ_args = if let TypX::Datatype(_, args) = &**autoview_typ {
            args.clone()
        } else {
            panic!("autoview_typ must be Datatype")
        };

        let receiver = args.first().expect("receiver in method call");
        let self_path = match &(*typ_of_node(bctx, &receiver.hir_id, true)) {
            TypX::Datatype(path, _) => path.clone(),
            _ => panic!("unexpected receiver type"),
        };
        let view_path = typ_path_and_ident_to_vir_path(&self_path, Arc::new("view".to_string()));

        let fun = Arc::new(FunX { path: view_path, trait_path: None });
        let target = CallTarget::Static(fun, typ_args);
        let viewx = ExprX::Call(target, Arc::new(vec![vir_args[0].clone()]));
        vir_args[0] = spanned_typed_new(expr.span, autoview_typ, viewx);
        self_path
    } else {
        let mut self_path = path.clone();
        let self_path_mut = Arc::make_mut(&mut self_path);
        Arc::make_mut(&mut self_path_mut.segments).pop();
        self_path
    };

    match is_get_variant {
        Some((variant_name, None)) => {
            return Ok(mk_expr(ExprX::UnaryOpr(
                UnaryOpr::IsVariant { datatype: self_path, variant: str_ident(&variant_name) },
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            )));
        }
        Some((variant_name, Some(variant_field))) => {
            use crate::def::FieldName;
            let variant_name_ident = str_ident(&variant_name);
            return Ok(mk_expr(ExprX::UnaryOpr(
                UnaryOpr::Field {
                    datatype: self_path.clone(),
                    variant: variant_name_ident.clone(),
                    field: match variant_field {
                        FieldName::Unnamed(i) => positional_field_ident(i),
                        FieldName::Named(f) => str_ident(&f),
                    },
                },
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            )));
        }
        None => {}
    }

    let is_smt_binary = if is_equal {
        true
    } else if is_eq || is_ne {
        is_smt_equality(bctx, expr.span, &args[0].hir_id, &args[1].hir_id)
    } else if is_cmp || is_arith_binary || is_implies {
        is_smt_arith(bctx, &args[0].hir_id, &args[1].hir_id)
    } else {
        false
    };

    if is_invariant {
        let header = Arc::new(HeaderExprX::Invariant(Arc::new(vir_args)));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_decreases {
        let header = Arc::new(HeaderExprX::Decreases(Arc::new(vir_args)));
        Ok(mk_expr(ExprX::Header(header)))
    } else if is_admit {
        unsupported_err_unless!(len == 0, expr.span, "expected admit", args);
        Ok(mk_expr(ExprX::Admit))
    } else if is_smt_binary {
        unsupported_err_unless!(len == 2, expr.span, "expected binary op", args);
        let lhs = vir_args[0].clone();
        let rhs = vir_args[1].clone();
        let vop = if is_equal {
            BinaryOp::Eq(Mode::Spec)
        } else if is_eq {
            BinaryOp::Eq(Mode::Exec)
        } else if is_ne {
            BinaryOp::Ne
        } else if is_le {
            BinaryOp::Le
        } else if is_ge {
            BinaryOp::Ge
        } else if is_lt {
            BinaryOp::Lt
        } else if is_gt {
            BinaryOp::Gt
        } else if is_add {
            BinaryOp::Add
        } else if is_sub {
            BinaryOp::Sub
        } else if is_mul {
            BinaryOp::Mul
        } else if is_implies {
            BinaryOp::Implies
        } else {
            panic!("internal error")
        };
        let e = mk_expr(ExprX::Binary(vop, lhs, rhs));
        if is_arith_binary { Ok(mk_ty_clip(&expr_typ(), &e)) } else { Ok(e) }
    } else {
        // filter out the Fn type parameters
        let mut fn_params: Vec<Ident> = Vec::new();
        for (x, _) in tcx.predicates_of(f).predicates {
            if let PredicateKind::Trait(t) = x.kind().skip_binder() {
                let name = path_as_rust_name(&def_id_to_vir_path(tcx, t.trait_ref.def_id));
                if name == "core::ops::function::Fn" {
                    for s in t.trait_ref.substs {
                        if let GenericArgKind::Type(ty) = s.unpack() {
                            if let TypX::TypParam(x) = &*mid_ty_to_vir(tcx, ty, false) {
                                fn_params.push(x.clone());
                            }
                        }
                    }
                }
            }
        }
        // type arguments
        let mut typ_args: Vec<Typ> = Vec::new();
        for typ_arg in node_substs {
            match typ_arg.unpack() {
                GenericArgKind::Type(ty) => {
                    typ_args.push(mid_ty_to_vir(tcx, ty, false));
                }
                GenericArgKind::Lifetime(_) => {}
                _ => unsupported_err!(expr.span, format!("const type arguments"), expr),
            }
        }
        let target = CallTarget::Static(name, Arc::new(typ_args));
        Ok(spanned_typed_new(expr.span, &expr_typ(), ExprX::Call(target, Arc::new(vir_args))))
    }
}

fn datatype_of_path(mut path: vir::ast::Path, pop_constructor: bool) -> vir::ast::Path {
    // TODO is there a safer way to do this?
    let segments = Arc::get_mut(&mut Arc::get_mut(&mut path).unwrap().segments).unwrap();
    if pop_constructor {
        segments.pop(); // remove constructor
    }
    segments.pop(); // remove variant
    path
}

fn datatype_variant_of_res<'tcx>(
    tcx: TyCtxt<'tcx>,
    res: &Res,
    pop_constructor: bool,
) -> (vir::ast::Path, Ident) {
    let variant = tcx.expect_variant_res(*res);
    let vir_path = datatype_of_path(def_id_to_vir_path(tcx, res.def_id()), pop_constructor);
    let variant_name = str_ident(&variant.ident.as_str());
    (vir_path, variant_name)
}

pub(crate) fn expr_tuple_datatype_ctor_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    res: &Res,
    args_slice: &[Expr<'tcx>],
    fun_span: Span,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let expr_typ = typ_of_node(bctx, &expr.hir_id, false);
    let ctor_of = if let Res::Def(DefKind::Ctor(ctor_of, ctor_kind), _def_id) = res {
        unsupported_unless!(
            ctor_of == &rustc_hir::def::CtorOf::Variant
                || ctor_of == &rustc_hir::def::CtorOf::Struct,
            "non_variant_ctor_in_call_expr",
            expr
        );
        unsupported_unless!(
            ctor_kind == &rustc_hir::def::CtorKind::Fn
                || ctor_kind == &rustc_hir::def::CtorKind::Const,
            "non_fn_ctor_in_call_expr",
            expr
        );
        ctor_of
    } else {
        panic!("unexpected constructor in expr_tuple_datatype_ctor_to_vir")
    };
    let (vir_path, variant_name) =
        datatype_variant_of_res(tcx, res, ctor_of == &rustc_hir::def::CtorOf::Variant);
    let vir_fields = Arc::new(
        args_slice
            .iter()
            .enumerate()
            .map(|(i, e)| -> Result<_, VirErr> {
                let vir = expr_to_vir(bctx, e, modifier)?;
                Ok(ident_binder(&positional_field_ident(i), &vir))
            })
            .collect::<Result<Vec<_>, _>>()?,
    );
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    let resolved_call = ResolvedCall::Ctor(vir_path.clone(), variant_name.clone());
    erasure_info.resolved_calls.push((fun_span.data(), resolved_call));
    let exprx = ExprX::Ctor(vir_path, variant_name, vir_fields, None);
    Ok(spanned_typed_new(expr.span, &expr_typ, exprx))
}

pub(crate) fn pattern_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pat: &Pat<'tcx>,
) -> Result<vir::ast::Pattern, VirErr> {
    let tcx = bctx.ctxt.tcx;
    unsupported_err_unless!(pat.default_binding_modes, pat.span, "complex pattern");
    let pattern = match &pat.kind {
        PatKind::Wild => PatternX::Wildcard,
        PatKind::Binding(BindingAnnotation::Unannotated, _canonical, x, None) => {
            PatternX::Var { name: Arc::new(x.as_str().to_string()), mutable: false }
        }
        PatKind::Binding(BindingAnnotation::Mutable, _canonical, x, None) => {
            PatternX::Var { name: Arc::new(x.as_str().to_string()), mutable: true }
        }
        PatKind::Path(QPath::Resolved(
            None,
            rustc_hir::Path {
                res:
                    res @ Res::Def(
                        DefKind::Ctor(
                            rustc_hir::def::CtorOf::Variant,
                            rustc_hir::def::CtorKind::Const,
                        ),
                        _,
                    ),
                ..
            },
        )) => {
            let (vir_path, variant_name) = datatype_variant_of_res(tcx, res, true);
            PatternX::Constructor(vir_path, variant_name, Arc::new(vec![]))
        }
        PatKind::Tuple(pats, None) => {
            let mut patterns: Vec<vir::ast::Pattern> = Vec::new();
            for pat in pats.iter() {
                patterns.push(pattern_to_vir(bctx, pat)?);
            }
            PatternX::Tuple(Arc::new(patterns))
        }
        PatKind::TupleStruct(
            QPath::Resolved(
                None,
                rustc_hir::Path {
                    res:
                        res @ Res::Def(
                            DefKind::Ctor(
                                ctor_of @ (rustc_hir::def::CtorOf::Variant
                                | rustc_hir::def::CtorOf::Struct),
                                rustc_hir::def::CtorKind::Fn,
                            ),
                            _,
                        ),
                    ..
                },
            ),
            pats,
            None,
        ) => {
            let (vir_path, variant_name) =
                datatype_variant_of_res(tcx, res, *ctor_of == rustc_hir::def::CtorOf::Variant);
            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for (i, pat) in pats.iter().enumerate() {
                let pattern = pattern_to_vir(bctx, pat)?;
                let binder = ident_binder(&positional_field_ident(i), &pattern);
                binders.push(binder);
            }
            PatternX::Constructor(vir_path, variant_name, Arc::new(binders))
        }
        PatKind::Struct(
            QPath::Resolved(None, rustc_hir::Path { res: res @ Res::Def(DefKind::Variant, _), .. }),
            pats,
            _,
        ) => {
            let (vir_path, variant_name) = datatype_variant_of_res(tcx, res, false);
            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for fpat in pats.iter() {
                let pattern = pattern_to_vir(bctx, &fpat.pat)?;
                let binder = ident_binder(&str_ident(&fpat.ident.as_str()), &pattern);
                binders.push(binder);
            }
            PatternX::Constructor(vir_path, variant_name, Arc::new(binders))
        }
        PatKind::Struct(
            QPath::Resolved(None, rustc_hir::Path { res: res @ Res::Def(DefKind::Struct, _), .. }),
            pats,
            _,
        ) => {
            let vir_path = def_id_to_vir_path(tcx, res.def_id());
            let variant_name = vir_path.segments.last().expect("empty vir_path").clone();
            let mut binders: Vec<Binder<vir::ast::Pattern>> = Vec::new();
            for fpat in pats.iter() {
                let pattern = pattern_to_vir(bctx, &fpat.pat)?;
                let binder = ident_binder(&str_ident(&fpat.ident.as_str()), &pattern);
                binders.push(binder);
            }
            PatternX::Constructor(vir_path, variant_name, Arc::new(binders))
        }
        _ => return unsupported_err!(pat.span, "complex pattern", pat),
    };
    let pat_typ = typ_of_node(bctx, &pat.hir_id, false);
    let pattern = spanned_typed_new(pat.span, &pat_typ, pattern);
    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
    erasure_info.resolved_pats.push((pat.span.data(), pattern.clone()));
    Ok(pattern)
}

/// Check for the #[verifier(invariant_block)] attribute
pub fn attrs_is_invariant_block(attrs: &[Attribute]) -> Result<bool, VirErr> {
    let attrs_vec = parse_attrs(attrs)?;
    for attr in &attrs_vec {
        match attr {
            Attr::InvariantBlock => {
                return Ok(true);
            }
            _ => {}
        }
    }
    Ok(false)
}

/// Check for the #[verifier(invariant_block)] attribute on a block
fn is_invariant_block(bctx: &BodyCtxt, expr: &Expr) -> Result<bool, VirErr> {
    let attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
    attrs_is_invariant_block(attrs)
}

fn malformed_inv_block_err<'tcx>(expr: &Expr<'tcx>) -> Result<vir::ast::Expr, VirErr> {
    err_span_str(expr.span, "malformed invariant block; use 'open_invariant' macro instead")
}

fn invariant_block_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    // The open_invariant! macro produces code that looks like this
    //
    // #[verifier(invariant_block)] {
    //      let (guard, mut $inner) = open_invariant_begin($eexpr);
    //      $bblock
    //      open_invariant_end(guard, $inner);
    //  }
    //
    // We need to check that it really does have this form, including
    // that the identifiers `guard` and `inner` used in the last statement
    // are the same as in the first statement. This is what the giant
    // `match` statements below are for.
    //
    // We also need to "recover" the $inner, $eexpr, and $bblock for converstion to VIR.
    //
    // If the AST doesn't look exactly like we expect, print an error asking the user
    // to use the open_invariant! macro.

    let body = match &expr.kind {
        ExprKind::Block(body, _) => body,
        _ => panic!("invariant_block_to_vir called with non-Body expression"),
    };

    if body.stmts.len() != 3 || body.expr.is_some() {
        return malformed_inv_block_err(expr);
    }

    let open_stmt = &body.stmts[0];
    let mid_stmt = &body.stmts[1];
    let close_stmt = &body.stmts[body.stmts.len() - 1];

    let (guard_hir, inner_hir, inner_pat, inv_arg, atomicity) = match open_stmt.kind {
        StmtKind::Local(Local {
            pat:
                Pat {
                    kind:
                        PatKind::Tuple(
                            [
                                Pat {
                                    kind:
                                        PatKind::Binding(
                                            BindingAnnotation::Unannotated,
                                            guard_hir,
                                            _,
                                            None,
                                        ),
                                    default_binding_modes: true,
                                    ..
                                },
                                inner_pat @ Pat {
                                    kind:
                                        PatKind::Binding(BindingAnnotation::Mutable, inner_hir, _, None),
                                    default_binding_modes: true,
                                    ..
                                },
                            ],
                            None,
                        ),
                    ..
                },
            init:
                Some(Expr {
                    kind:
                        ExprKind::Call(
                            Expr {
                                kind:
                                    ExprKind::Path(QPath::Resolved(
                                        None,
                                        rustc_hir::Path {
                                            res: Res::Def(DefKind::Fn, fun_id), ..
                                        },
                                    )),
                                ..
                            },
                            [arg],
                        ),
                    ..
                }),
            ..
        }) => {
            let f_name = path_as_rust_name(&def_id_to_vir_path(bctx.ctxt.tcx, *fun_id));
            if f_name != BUILTIN_INV_BEGIN && f_name != BUILTIN_INV_LOCAL_BEGIN {
                return malformed_inv_block_err(expr);
            }
            let atomicity = if f_name == BUILTIN_INV_BEGIN {
                InvAtomicity::Atomic
            } else {
                InvAtomicity::NonAtomic
            };
            (guard_hir, inner_hir, inner_pat, arg, atomicity)
        }
        _ => {
            return malformed_inv_block_err(expr);
        }
    };

    match close_stmt.kind {
        StmtKind::Semi(Expr {
            kind:
                ExprKind::Call(
                    Expr {
                        kind:
                            ExprKind::Path(QPath::Resolved(
                                None,
                                rustc_hir::Path { res: Res::Def(_, fun_id), .. },
                            )),
                        ..
                    },
                    [
                        Expr {
                            kind:
                                ExprKind::Path(QPath::Resolved(
                                    None,
                                    rustc_hir::Path { res: Res::Local(hir_id1), .. },
                                )),
                            ..
                        },
                        Expr {
                            kind:
                                ExprKind::Path(QPath::Resolved(
                                    None,
                                    rustc_hir::Path { res: Res::Local(hir_id2), .. },
                                )),
                            ..
                        },
                    ],
                ),
            ..
        }) => {
            let f_name = path_as_rust_name(&def_id_to_vir_path(bctx.ctxt.tcx, *fun_id));
            if f_name != BUILTIN_INV_END {
                return malformed_inv_block_err(expr);
            }

            if hir_id1 != guard_hir || hir_id2 != inner_hir {
                return malformed_inv_block_err(expr);
            }
        }
        _ => {
            return malformed_inv_block_err(expr);
        }
    }

    let vir_body = match mid_stmt.kind {
        StmtKind::Expr(e @ Expr { kind: ExprKind::Block(body, _), .. }) => {
            assert!(!is_invariant_block(bctx, e)?);
            let vir_stmts: Stmts = Arc::new(
                slice_vec_map_result(body.stmts, |stmt| stmt_to_vir(bctx, stmt))?
                    .into_iter()
                    .flatten()
                    .collect(),
            );
            let vir_expr = body.expr.map(|expr| expr_to_vir(bctx, &expr, modifier)).transpose()?;
            let ty = typ_of_node(bctx, &e.hir_id, false);
            // NOTE: we use body.span here instead of e.span
            // body.span leads to better error messages
            // (e.g., the "Cannot show invariant holds at end of block" error)
            // (e.span or mid_stmt.span would expose macro internals)
            spanned_typed_new(body.span, &ty, ExprX::Block(vir_stmts, vir_expr))
        }
        _ => {
            return malformed_inv_block_err(expr);
        }
    };

    let vir_arg = expr_to_vir(bctx, &inv_arg, modifier)?;

    let name = Arc::new(pat_to_var(inner_pat));
    let inner_ty = typ_of_node(bctx, &inner_hir, false);
    let vir_binder = Arc::new(BinderX { name, a: inner_ty });

    let e = ExprX::OpenInvariant(vir_arg, vir_binder, vir_body, atomicity);
    Ok(spanned_typed_new(expr.span, &typ_of_node(bctx, &expr.hir_id, false), e))
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) struct ExprModifier {
    /// dereferencing a mutable reference
    deref_mut: bool,
    /// taking a mutable reference
    addr_of: bool,
}

impl ExprModifier {
    pub(crate) const REGULAR: Self = Self { deref_mut: false, addr_of: false };

    #[allow(dead_code)]
    pub(crate) const DEREF_MUT: Self = Self { deref_mut: true, addr_of: false };

    pub(crate) const ADDR_OF: Self = Self { deref_mut: false, addr_of: true };
}

fn is_expr_typ_mut_ref<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    modifier: ExprModifier,
) -> Result<ExprModifier, VirErr> {
    match bctx.types.node_type(expr.hir_id).kind() {
        TyKind::Ref(_, _tys, rustc_ast::Mutability::Not) => Ok(modifier),
        TyKind::Ref(_, _tys, rustc_ast::Mutability::Mut) => {
            Ok(ExprModifier { deref_mut: true, ..modifier })
        }
        _ => Ok(modifier),
    }
}

pub(crate) fn expr_to_vir_inner<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    current_modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let expr = expr.peel_drop_temps();

    if bctx.external_body {
        // we want just requires/ensures, not the whole body
        match &expr.kind {
            ExprKind::Block(..) | ExprKind::Call(..) => {}
            _ => {
                return Ok(spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Block(Arc::new(vec![]), None),
                ));
            }
        }
    }

    let tcx = bctx.ctxt.tcx;
    let tc = bctx.types;
    let expr_typ = || {
        if current_modifier.deref_mut {
            typ_of_node_expect_mut_ref(bctx, &expr.hir_id, expr.span)
                .expect("unexpected non-mut-ref type here")
        } else {
            typ_of_node(bctx, &expr.hir_id, false)
        }
    };
    let mk_expr = move |x: ExprX| spanned_typed_new(expr.span, &expr_typ(), x);

    let modifier = ExprModifier { deref_mut: false, ..current_modifier };

    let mk_lit_int = |in_negative_literal: bool, i: u128, typ: Typ| {
        let c = vir::ast::Constant::Nat(Arc::new(i.to_string()));
        let i_bump = if in_negative_literal { 1 } else { 0 };
        if let TypX::Int(range) = *typ {
            match range {
                IntRange::Int | IntRange::Nat => Ok(mk_expr(ExprX::Const(c))),
                IntRange::U(n) if n == 128 || (n < 128 && i < (1u128 << n)) => {
                    Ok(mk_expr(ExprX::Const(c)))
                }
                IntRange::I(n) if n - 1 < 128 && i < (1u128 << (n - 1)) + i_bump => {
                    Ok(mk_expr(ExprX::Const(c)))
                }
                IntRange::USize if i < (1u128 << vir::def::ARCH_SIZE_MIN_BITS) => {
                    Ok(mk_expr(ExprX::Const(c)))
                }
                IntRange::ISize if i < (1u128 << (vir::def::ARCH_SIZE_MIN_BITS - 1)) + i_bump => {
                    Ok(mk_expr(ExprX::Const(c)))
                }
                _ => {
                    // If we're not sure the constant fits in the range,
                    // be cautious and clip it
                    Ok(mk_clip(&range, &mk_expr(ExprX::Const(c))))
                }
            }
        } else {
            panic!("unexpected constant: {:?} {:?}", i, typ)
        }
    };

    match &expr.kind {
        ExprKind::Block(body, _) => {
            if is_invariant_block(bctx, expr)? {
                invariant_block_to_vir(bctx, expr, modifier)
            } else {
                let vir_stmts: Stmts = Arc::new(
                    slice_vec_map_result(body.stmts, |stmt| stmt_to_vir(bctx, stmt))?
                        .into_iter()
                        .flatten()
                        .collect(),
                );
                let vir_expr =
                    body.expr.map(|expr| expr_to_vir(bctx, &expr, modifier)).transpose()?;
                Ok(mk_expr(ExprX::Block(vir_stmts, vir_expr)))
            }
        }
        ExprKind::Call(fun, args_slice) => {
            let res = match &fun.kind {
                // a tuple-style datatype constructor
                ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: res @ Res::Def(DefKind::Ctor(_, _), _), .. },
                )) => Some(expr_tuple_datatype_ctor_to_vir(
                    bctx,
                    expr,
                    res,
                    *args_slice,
                    fun.span,
                    modifier,
                )),
                ExprKind::Path(qpath) => {
                    let def = bctx.types.qpath_res(&qpath, fun.hir_id);
                    match def {
                        // a statically resolved function
                        rustc_hir::def::Res::Def(_, def_id) => Some(fn_call_to_vir(
                            bctx,
                            expr,
                            def_id,
                            bctx.types.node_substs(fun.hir_id),
                            fun.span,
                            args_slice,
                            None,
                        )),
                        rustc_hir::def::Res::Local(_) => {
                            None // dynamically computed function, see below
                        }
                        _ => {
                            unsupported!(format!(
                                "function call {:?} {:?} {:?}",
                                def, expr, expr.span
                            ))
                        }
                    }
                }
                _ => {
                    None // dynamically computed function, see below
                }
            };
            match res {
                Some(res) => res,
                None => {
                    // a dynamically computed function
                    if bctx.external_body {
                        return Ok(mk_expr(ExprX::Block(Arc::new(vec![]), None)));
                    }
                    let vir_fun = expr_to_vir(bctx, fun, modifier)?;
                    let args: Vec<&'tcx Expr<'tcx>> = args_slice.iter().collect();
                    let vir_args = vec_map_result(&args, |arg| expr_to_vir(bctx, arg, modifier))?;
                    let expr_typ = typ_of_node(bctx, &expr.hir_id, false);
                    let target = CallTarget::FnSpec(vir_fun);
                    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                    // Only spec closures are currently supported:
                    erasure_info.resolved_calls.push((fun.span.data(), ResolvedCall::Spec));
                    Ok(spanned_typed_new(
                        expr.span,
                        &expr_typ,
                        ExprX::Call(target, Arc::new(vir_args)),
                    ))
                }
            }
        }
        ExprKind::Tup(exprs) => {
            let args: Result<Vec<vir::ast::Expr>, VirErr> =
                exprs.iter().map(|e| expr_to_vir(bctx, e, modifier)).collect();
            Ok(mk_expr(ExprX::Tuple(Arc::new(args?))))
        }
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Bool(b) => {
                let c = vir::ast::Constant::Bool(b);
                Ok(mk_expr(ExprX::Const(c)))
            }
            rustc_ast::LitKind::Int(i, _) => {
                mk_lit_int(false, i, typ_of_node(bctx, &expr.hir_id, false))
            }
            _ => {
                panic!("unexpected constant: {:?}", lit)
            }
        },
        ExprKind::Cast(source, _) => {
            Ok(mk_ty_clip(&expr_typ(), &expr_to_vir(bctx, source, modifier)?))
        }
        ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, e) => {
            expr_to_vir_inner(bctx, e, ExprModifier::REGULAR)
        }
        ExprKind::Box(e) => expr_to_vir_inner(bctx, e, ExprModifier::REGULAR),
        ExprKind::Unary(op, arg) => match op {
            UnOp::Not => {
                let not_op = match (tc.node_type(expr.hir_id)).kind() {
                    TyKind::Adt(_, _) | TyKind::Uint(_) | TyKind::Int(_) => UnaryOp::BitNot,
                    TyKind::Bool => UnaryOp::Not,
                    _ => panic!("Internal error on UnOp::Not translation"),
                };
                let varg = expr_to_vir(bctx, arg, modifier)?;
                Ok(mk_expr(ExprX::Unary(not_op, varg)))
            }
            UnOp::Neg => {
                let zero_const = vir::ast::Constant::Nat(Arc::new("0".to_string()));
                let zero = mk_expr(ExprX::Const(zero_const));
                let varg = if let ExprKind::Lit(rustc_span::source_map::Spanned {
                    node: rustc_ast::LitKind::Int(i, _),
                    ..
                }) = &arg.kind
                {
                    mk_lit_int(true, *i, typ_of_node(bctx, &expr.hir_id, false))?
                } else {
                    expr_to_vir(bctx, arg, modifier)?
                };
                Ok(mk_expr(ExprX::Binary(BinaryOp::Sub, zero, varg)))
            }
            UnOp::Deref => expr_to_vir_inner(bctx, arg, is_expr_typ_mut_ref(bctx, arg, modifier)?),
        },
        ExprKind::Binary(op, lhs, rhs) => {
            let vlhs = expr_to_vir(bctx, lhs, modifier)?;
            let vrhs = expr_to_vir(bctx, rhs, modifier)?;
            match op.node {
                BinOpKind::Eq | BinOpKind::Ne => unsupported_err_unless!(
                    is_smt_equality(bctx, expr.span, &lhs.hir_id, &rhs.hir_id),
                    expr.span,
                    "==/!= for non smt equality types"
                ),
                BinOpKind::Add
                | BinOpKind::Sub
                | BinOpKind::Mul
                | BinOpKind::Le
                | BinOpKind::Ge
                | BinOpKind::Lt
                | BinOpKind::Gt => unsupported_unless!(
                    is_smt_arith(bctx, &lhs.hir_id, &rhs.hir_id),
                    "cmp or arithmetic for non smt arithmetic types",
                    expr
                ),
                _ => (),
            }
            let vop = match op.node {
                BinOpKind::And => BinaryOp::And,
                BinOpKind::Or => BinaryOp::Or,
                BinOpKind::Eq => BinaryOp::Eq(Mode::Exec),
                BinOpKind::Ne => BinaryOp::Ne,
                BinOpKind::Le => BinaryOp::Le,
                BinOpKind::Ge => BinaryOp::Ge,
                BinOpKind::Lt => BinaryOp::Lt,
                BinOpKind::Gt => BinaryOp::Gt,
                BinOpKind::Add => BinaryOp::Add,
                BinOpKind::Sub => BinaryOp::Sub,
                BinOpKind::Mul => BinaryOp::Mul,
                BinOpKind::Div => BinaryOp::EuclideanDiv,
                BinOpKind::Rem => BinaryOp::EuclideanMod,
                BinOpKind::BitXor => BinaryOp::BitXor,
                BinOpKind::BitAnd => BinaryOp::BitAnd,
                BinOpKind::BitOr => BinaryOp::BitOr,
                BinOpKind::Shr => BinaryOp::Shr,
                BinOpKind::Shl => BinaryOp::Shl,
            };
            match op.node {
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul => {
                    let e = mk_expr(ExprX::Binary(vop, vlhs, vrhs));
                    Ok(mk_ty_clip(&expr_typ(), &e))
                }
                BinOpKind::Div | BinOpKind::Rem => {
                    // TODO: disallow divide-by-zero in executable code?
                    match mk_range(tc.node_type(expr.hir_id)) {
                        IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::USize => {
                            // Euclidean division
                            Ok(mk_expr(ExprX::Binary(vop, vlhs, vrhs)))
                        }
                        IntRange::I(_) | IntRange::ISize => {
                            // Non-Euclidean division, which will need more encoding
                            unsupported_err!(expr.span, "div/mod on signed finite-width integers")
                        }
                    }
                }
                _ => Ok(mk_expr(ExprX::Binary(vop, vlhs, vrhs))),
            }
        }
        ExprKind::AssignOp(
            rustc_span::source_map::Spanned { node: BinOpKind::Shr, .. },
            lhs,
            rhs,
        ) => {
            let vlhs = expr_to_vir(bctx, lhs, modifier)?;
            let vrhs = expr_to_vir(bctx, rhs, modifier)?;
            if matches!(*vlhs.typ, TypX::Bool) {
                let e = mk_expr(ExprX::Binary(BinaryOp::Implies, vlhs, vrhs));
                Ok(e)
            } else {
                unsupported_err!(expr.span, "assignment operators")
            }
        }
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(id) => match tcx.hir().get(id) {
                Node::Binding(pat) => Ok(mk_expr(if modifier.addr_of {
                    ExprX::VarLoc(Arc::new(pat_to_var(pat)))
                } else {
                    ExprX::Var(Arc::new(pat_to_var(pat)))
                })),
                node => unsupported_err!(expr.span, format!("Path {:?}", node)),
            },
            Res::Def(def_kind, id) => {
                match def_kind {
                    DefKind::Const => {
                        let path = def_id_to_vir_path(tcx, id);
                        let fun = FunX { path, trait_path: None };
                        Ok(mk_expr(ExprX::ConstVar(Arc::new(fun))))
                    }
                    DefKind::Fn => {
                        let name = hack_get_def_name(tcx, id); // TODO: proper handling of paths
                        Ok(mk_expr(ExprX::Var(Arc::new(name))))
                    }
                    DefKind::Ctor(_, _ctor_kind) => expr_tuple_datatype_ctor_to_vir(
                        bctx,
                        expr,
                        &path.res,
                        &[],
                        expr.span,
                        modifier,
                    ),
                    _ => {
                        unsupported_err!(expr.span, format!("Path {:?} kind {:?}", id, def_kind))
                    }
                }
            }
            res => unsupported_err!(expr.span, format!("Path {:?}", res)),
        },
        ExprKind::Assign(lhs, rhs, _) => {
            if let ExprKind::Field(_, _) = lhs.kind {
                unsupported_err!(expr.span, format!("field updates"), lhs);
            }
            let not_mut_init = if let ExprKind::Path(QPath::Resolved(
                None,
                rustc_hir::Path { res: Res::Local(id), .. },
            )) = lhs.kind
            {
                if let Node::Binding(pat) = tcx.hir().get(*id) {
                    let (mutable, _) = pat_to_mut_var(pat);
                    !mutable
                } else {
                    panic!("assignment to non-local");
                }
            } else {
                false
            };
            Ok(mk_expr(ExprX::Assign {
                not_mut_init,
                lhs: expr_to_vir(bctx, lhs, ExprModifier::ADDR_OF)?,
                rhs: expr_to_vir(bctx, rhs, modifier)?,
            }))
        }
        ExprKind::Field(lhs, name) => {
            let lhs_modifier = is_expr_typ_mut_ref(bctx, lhs, modifier)?;
            let vir_lhs = expr_to_vir(bctx, lhs, lhs_modifier)?;
            let lhs_ty = tc.node_type(lhs.hir_id);
            let lhs_ty = mid_ty_simplify(tcx, lhs_ty, true);
            let (datatype, variant_name, field_name) = if let Some(adt_def) = lhs_ty.ty_adt_def() {
                unsupported_err_unless!(
                    adt_def.variants.len() == 1,
                    expr.span,
                    "field_of_adt_with_multiple_variants",
                    expr
                );
                let datatype_path = def_id_to_vir_path(tcx, adt_def.did);
                let hir_def = bctx.ctxt.tcx.adt_def(adt_def.did);
                let variant = hir_def.variants.iter().next().unwrap();
                let variant_name = str_ident(&variant.ident.as_str());
                let field_name = match variant.ctor_kind {
                    rustc_hir::def::CtorKind::Fn => {
                        let field_idx = variant
                            .fields
                            .iter()
                            .position(|f| f.ident == *name)
                            .expect("positional field not found");
                        positional_field_ident(field_idx)
                    }
                    rustc_hir::def::CtorKind::Fictive => str_ident(&name.as_str()),
                    rustc_hir::def::CtorKind::Const => panic!("unexpected tuple constructor"),
                };
                (datatype_path, variant_name, field_name)
            } else {
                let lhs_typ = typ_of_node(bctx, &lhs.hir_id, false);
                if let TypX::Tuple(ts) = &*lhs_typ {
                    let field: usize =
                        str::parse(&name.as_str()).expect("integer index into tuple");
                    let field_opr = UnaryOpr::TupleField { tuple_arity: ts.len(), field };
                    let vir = mk_expr(ExprX::UnaryOpr(field_opr, vir_lhs));
                    let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
                    erasure_info.resolved_exprs.push((expr.span.data(), vir.clone()));
                    return Ok(vir);
                }
                unsupported_err!(expr.span, "field_of_non_adt", expr)
            };
            let field_type = expr_typ().clone();
            let vir = spanned_typed_new(
                expr.span,
                &field_type,
                ExprX::UnaryOpr(
                    UnaryOpr::Field { datatype, variant: variant_name, field: field_name },
                    vir_lhs,
                ),
            );
            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
            erasure_info.resolved_exprs.push((expr.span.data(), vir.clone()));
            Ok(vir)
        }
        ExprKind::If(cond, lhs, rhs) => {
            let cond = cond.peel_drop_temps();
            match cond.kind {
                ExprKind::Let(pat, expr, _let_span) => {
                    // if let
                    let vir_expr = expr_to_vir(bctx, expr, modifier)?;
                    let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
                    /* lhs */
                    {
                        let pattern = pattern_to_vir(bctx, pat)?;
                        let guard = mk_expr(ExprX::Const(Constant::Bool(true)));
                        let body = expr_to_vir(bctx, &lhs, modifier)?;
                        let vir_arm = ArmX { pattern, guard, body };
                        vir_arms.push(spanned_new(lhs.span, vir_arm));
                    }
                    /* rhs */
                    {
                        let pat_typ = typ_of_node(bctx, &pat.hir_id, false);
                        let pattern = spanned_typed_new(cond.span, &pat_typ, PatternX::Wildcard);
                        let guard = mk_expr(ExprX::Const(Constant::Bool(true)));
                        let body = if let Some(rhs) = rhs {
                            expr_to_vir(bctx, &rhs, modifier)?
                        } else {
                            mk_expr(ExprX::Block(Arc::new(Vec::new()), None))
                        };
                        let vir_arm = ArmX { pattern, guard, body };
                        vir_arms.push(spanned_new(lhs.span, vir_arm));
                    }
                    Ok(mk_expr(ExprX::Match(vir_expr, Arc::new(vir_arms))))
                }
                _ => {
                    let vir_cond = expr_to_vir(bctx, cond, modifier)?;
                    let vir_lhs = expr_to_vir(bctx, lhs, modifier)?;
                    let vir_rhs = rhs.map(|e| expr_to_vir(bctx, e, modifier)).transpose()?;
                    Ok(mk_expr(ExprX::If(vir_cond, vir_lhs, vir_rhs)))
                }
            }
        }
        ExprKind::Match(expr, arms, _match_source) => {
            let vir_expr = expr_to_vir(bctx, expr, modifier)?;
            let mut vir_arms: Vec<vir::ast::Arm> = Vec::new();
            for arm in arms.iter() {
                let pattern = pattern_to_vir(bctx, &arm.pat)?;
                let guard = match &arm.guard {
                    None => mk_expr(ExprX::Const(Constant::Bool(true))),
                    Some(Guard::If(guard)) => expr_to_vir(bctx, guard, modifier)?,
                    Some(Guard::IfLet(_, _)) => unsupported_err!(expr.span, "Guard IfLet"),
                };
                let body = expr_to_vir(bctx, &arm.body, modifier)?;
                let vir_arm = ArmX { pattern, guard, body };
                vir_arms.push(spanned_new(arm.span, vir_arm));
            }
            Ok(mk_expr(ExprX::Match(vir_expr, Arc::new(vir_arms))))
        }
        ExprKind::Loop(
            Block {
                stmts: [], expr: Some(Expr { kind: ExprKind::If(cond, body, other), .. }), ..
            },
            None,
            LoopSource::While,
            _span,
        ) => {
            if let Some(Expr {
                kind:
                    ExprKind::Block(
                        Block {
                            stmts:
                                [
                                    Stmt {
                                        kind:
                                            StmtKind::Expr(Expr {
                                                kind:
                                                    ExprKind::Break(
                                                        Destination { label: None, .. },
                                                        None,
                                                    ),
                                                ..
                                            }),
                                        ..
                                    },
                                ],
                            expr: None,
                            ..
                        },
                        None,
                    ),
                ..
            }) = other
            {
            } else {
                unsupported!("loop else", expr);
            }
            let cond = expr_to_vir(bctx, cond, modifier)?;
            let mut body = expr_to_vir(bctx, body, modifier)?;
            let header = vir::headers::read_header(&mut body)?;
            let invs = header.invariant;
            Ok(mk_expr(ExprX::While { cond, body, invs }))
        }
        ExprKind::Ret(expr) => {
            let expr = match expr {
                None => None,
                Some(expr) => Some(expr_to_vir(bctx, expr, modifier)?),
            };
            Ok(mk_expr(ExprX::Return(expr)))
        }
        ExprKind::Struct(qpath, fields, spread) => {
            let update = match spread {
                None => None,
                Some(update) => Some(expr_to_vir(bctx, update, modifier)?),
            };
            let (path, variant_name) = match qpath {
                QPath::Resolved(slf, path) => {
                    unsupported_unless!(
                        matches!(path.res, Res::Def(DefKind::Struct | DefKind::Variant, _)),
                        "non_struct_ctor",
                        path.res
                    );
                    unsupported_unless!(slf.is_none(), "self_in_struct_qpath");
                    let variant = tcx.expect_variant_res(path.res);
                    let mut vir_path = def_id_to_vir_path(tcx, path.res.def_id());
                    if let Res::Def(DefKind::Variant, _) = path.res {
                        Arc::get_mut(&mut Arc::get_mut(&mut vir_path).unwrap().segments)
                            .unwrap()
                            .pop()
                            .expect(format!("variant name in Struct ctor for {:?}", path).as_str());
                    }
                    let variant_name = str_ident(&variant.ident.as_str());
                    (vir_path, variant_name)
                }
                _ => panic!("unexpected qpath {:?}", qpath),
            };
            let vir_fields = Arc::new(
                fields
                    .iter()
                    .map(|f| -> Result<_, VirErr> {
                        let vir = expr_to_vir(bctx, f.expr, modifier)?;
                        Ok(ident_binder(&str_ident(&f.ident.as_str()), &vir))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            let mut erasure_info = bctx.ctxt.erasure_info.borrow_mut();
            let resolved_call = ResolvedCall::Ctor(path.clone(), variant_name.clone());
            erasure_info.resolved_calls.push((expr.span.data(), resolved_call));
            Ok(mk_expr(ExprX::Ctor(path, variant_name, vir_fields, update)))
        }
        ExprKind::MethodCall(_name_and_generics, _call_span_0, all_args, call_span_1) => {
            let fn_def_id = bctx
                .types
                .type_dependent_def_id(expr.hir_id)
                .expect("def id of the method definition");
            match tcx.hir().get_if_local(fn_def_id).expect("fn def for method in hir") {
                rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
                    kind: rustc_hir::ImplItemKind::Fn(..),
                    ..
                }) => {}
                _ => panic!("unexpected hir for method impl item"),
            }
            let autoview_typ = bctx.ctxt.autoviewed_call_typs.get(&expr.hir_id);
            fn_call_to_vir(
                bctx,
                expr,
                fn_def_id,
                bctx.types.node_substs(expr.hir_id),
                *call_span_1,
                all_args,
                autoview_typ,
            )
        }
        ExprKind::Closure(_, _fn_decl, body_id, _, _) => {
            let body = tcx.hir().body(*body_id);
            let typs = closure_param_typs(bctx, expr);
            assert!(typs.len() == body.params.len());
            let params: Vec<Binder<Typ>> = body
                .params
                .iter()
                .zip(typs.clone())
                .map(|(x, t)| Arc::new(BinderX { name: Arc::new(pat_to_var(x.pat)), a: t }))
                .collect();
            let body = expr_to_vir(bctx, &body.value, modifier)?;
            let typ = Arc::new(TypX::Lambda(Arc::new(typs), body.typ.clone()));
            Ok(spanned_typed_new(expr.span, &typ, ExprX::Closure(Arc::new(params), body)))
        }
        ExprKind::Index(tgt_expr, idx_expr) => {
            let tgt_vir = expr_to_vir(bctx, tgt_expr, modifier)?;
            if let TypX::Datatype(path, _dt_typs) = &*tgt_vir.typ {
                let tgt_index_path = {
                    let mut tp = path.clone();
                    Arc::make_mut(&mut Arc::make_mut(&mut tp).segments).push(str_ident("index"));
                    tp
                };
                let trait_def_id = bctx
                    .ctxt
                    .tcx
                    .lang_items()
                    .index_trait()
                    .expect("Index trait lang item should be defined");
                let trait_path = def_id_to_vir_path(bctx.ctxt.tcx, trait_def_id);
                let idx_vir = expr_to_vir(bctx, idx_expr, modifier)?;
                let target = CallTarget::Static(
                    Arc::new(FunX { path: tgt_index_path, trait_path: Some(trait_path) }),
                    Arc::new(vec![]),
                );
                Ok(mk_expr(ExprX::Call(target, Arc::new(vec![tgt_vir, idx_vir]))))
            } else {
                unsupported_err!(expr.span, format!("Index on non-datatype"), expr)
            }
        }
        _ => {
            unsupported_err!(expr.span, format!("expression"), expr)
        }
    }
}

pub(crate) fn let_stmt_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    pattern: &rustc_hir::Pat<'tcx>,
    initializer: &Option<&Expr<'tcx>>,
    attrs: &[Attribute],
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    let vir_pattern = pattern_to_vir(bctx, pattern)?;
    let mode = get_var_mode(bctx.mode, attrs);
    let init = initializer.map(|e| expr_to_vir(bctx, e, ExprModifier::REGULAR)).transpose()?;
    Ok(vec![spanned_new(pattern.span, StmtX::Decl { pattern: vir_pattern, mode, init })])
}

pub(crate) fn stmt_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    stmt: &Stmt<'tcx>,
) -> Result<Vec<vir::ast::Stmt>, VirErr> {
    if bctx.external_body {
        // we want just requires/ensures, not the whole body
        match &stmt.kind {
            StmtKind::Expr(..) | StmtKind::Semi(..) => {}
            _ => return Ok(vec![]),
        }
    }

    match &stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
            let vir_expr = expr_to_vir(bctx, expr, ExprModifier::REGULAR)?;
            Ok(vec![spanned_new(expr.span, StmtX::Expr(vir_expr))])
        }
        StmtKind::Local(Local { pat, init, .. }) => {
            let_stmt_to_vir(bctx, pat, init, bctx.ctxt.tcx.hir().attrs(stmt.hir_id))
        }
        _ => {
            unsupported_err!(stmt.span, "statement", stmt)
        }
    }
}
