use vstd::prelude::*;
use super::{RuntimePoint2, RuntimeLine2, RuntimeCircle2};
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::runtime::point2::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_rational::runtime_rational::copy_rational;
use verus_geometry::runtime::voronoi::sq_dist_2d_exec;
use verus_geometry::runtime::circle2::RuntimeCircle2;
use verus_geometry::runtime::line2::RuntimeLine2;
use crate::entities::*;
use crate::constraints::*;
use crate::construction::*;
use crate::construction_ext::*;
use crate::runtime::constraint::*;
use crate::runtime::construction::*;
use crate::runtime::solver::*;
use crate::runtime::locus::*;
use crate::locus::*;

type RationalModel = verus_rational::rational::Rational;

verus! {

///  Transfer conjuncts 9-12 from partial_resolved_map to execute_plan at a single step.
///  Extracted to isolate trigger pollution from the main replay loop.
proof fn lemma_transfer_step_conjuncts(
    ps: ConstructionPlan<RationalModel>,
    cs: Seq<Constraint<RationalModel>>,
    si: int,
    prm: ResolvedPoints<RationalModel>,
    exec_res: ResolvedPoints<RationalModel>,
)
    requires
        0 <= si < ps.len(),
        prm.dom() =~= exec_res.dom(),
        exec_res.dom() =~= execute_plan(ps.take(si)).dom(),
        !exec_res.dom().contains(step_target(ps[si])),
        forall|id: EntityId| exec_res.dom().contains(id)
            && !circle_targets(ps).contains(id)
            ==> prm[id] == exec_res[id],
        is_fully_independent_plan(ps, cs),
        forall|ci: int| 0 <= ci < cs.len() ==>
            constraint_well_formed(#[trigger] cs[ci]),
        //  Nondegeneracy for prm
        forall|ci: int| 0 <= ci < cs.len() ==>
            constraint_locus_nondegenerate(#[trigger] cs[ci], prm, step_target(ps[si])),
        //  Conjunct 9 for prm
        at_most_two_nontrivial_loci(step_target(ps[si]), cs, prm.dom()),
        //  Rational: loci satisfied against prm
        is_rational_step(ps[si]) ==>
            step_satisfies_all_constraint_loci(ps[si], cs, prm),
        //  Circle: geometry matches against prm
        !is_rational_step(ps[si]) ==>
            step_loci_match_geometry(ps[si], cs, prm),
    ensures
        at_most_two_nontrivial_loci(step_target(ps[si]), cs, exec_res.dom()),
        forall|ci: int| 0 <= ci < cs.len() ==>
            constraint_locus_nondegenerate(#[trigger] cs[ci], exec_res, step_target(ps[si])),
        is_rational_step(ps[si]) ==>
            step_satisfies_all_constraint_loci(ps[si], cs, exec_res),
        !is_rational_step(ps[si]) ==>
            step_loci_match_geometry(ps[si], cs, exec_res),
{
    let target = step_target(ps[si]);

    //  Conjunct 9: at_most_two_nontrivial_loci depends only on domain.
    //  prm.dom() =~= exec_res.dom(), so it's the same.

    //  Conjunct 12: nondegeneracy transfer.
    //  For Symmetric constraints: axis values agree via independence.
    assert forall|ci: int| 0 <= ci < cs.len()
    implies constraint_locus_nondegenerate(#[trigger] cs[ci], exec_res, target)
    by {
        match cs[ci] {
            Constraint::Symmetric { point, original, axis_a, axis_b } => {
                if target == point
                    && exec_res.dom().contains(axis_a)
                    && exec_res.dom().contains(axis_b) {
                    //  axis_a, axis_b are in constraint_entities and != target
                    //  (from constraint_well_formed: point != axis_a, point != axis_b)
                    //  By independence: they're non-circle targets
                    //  So prm[axis_a] == exec_res[axis_a], etc.
                    //  Trigger is_fully_independent_plan quantifier
                    //  Its triggers are ps[si] and cs[ci]
                    let _ = ps[si]; //  trigger
                    let _ = cs[ci]; //  trigger
                    assert(constraint_entities(cs[ci]).contains(axis_a));
                    assert(constraint_entities(cs[ci]).contains(target));
                    assert(axis_a != target);
                    assert(execute_plan(ps.take(si)).dom().contains(axis_a));
                    assert(!circle_targets(ps).contains(axis_a));
                    assert(prm[axis_a] == exec_res[axis_a]);
                    assert(axis_b != target);
                    assert(execute_plan(ps.take(si)).dom().contains(axis_b));
                    assert(!circle_targets(ps).contains(axis_b));
                    assert(prm[axis_b] == exec_res[axis_b]);
                }
            }
            _ => {}
        }
    }

    //  For conjuncts 10/11: prove locus_eqv per ci via congruence.
    //  Split: if constraint references target, use congruence; else locus is FullPlane.
    assert forall|ci: int| 0 <= ci < cs.len()
    implies locus_eqv(
        constraint_to_locus(#[trigger] cs[ci], prm, target),
        constraint_to_locus(cs[ci], exec_res, target))
    by {
        if constraint_entities(cs[ci]).contains(target) {
            //  By independence: all other entities in domain are non-circle targets
            let _ = ps[si]; //  trigger for is_fully_independent_plan
            let _ = cs[ci]; //  trigger for is_fully_independent_plan
            assert forall|e: EntityId|
                constraint_entities(cs[ci]).contains(e) && e != target
                && prm.dom().contains(e)
            implies prm[e].eqv(exec_res[e])
            by {
                assert(execute_plan(ps.take(si)).dom().contains(e));
                assert(!circle_targets(ps).contains(e));
                assert(prm[e] == exec_res[e]);
                Point2::<RationalModel>::axiom_eqv_reflexive(exec_res[e]);
            }
            lemma_constraint_to_locus_resolved_congruence(
                cs[ci], prm, exec_res, target);
        } else {
            //  Target not in constraint → both loci are FullPlane
            //  constraint_to_locus checks if target matches some entity
            //  in each branch; if not, returns FullPlane.
            //  Z3 can unfold this.
        }
    }

    //  Conjunct 10: rational step satisfaction transfer
    if is_rational_step(ps[si]) {
        assert forall|ci: int| 0 <= ci < cs.len()
        implies point_satisfies_locus(
            constraint_to_locus(#[trigger] cs[ci], exec_res, target),
            execute_step(ps[si]))
        by {
            lemma_point_satisfies_locus_eqv(
                constraint_to_locus(cs[ci], prm, target),
                constraint_to_locus(cs[ci], exec_res, target),
                execute_step(ps[si]),
            );
        }
    }

    //  Conjunct 11: circle step geometry transfer
    if !is_rational_step(ps[si]) {
        let target = step_target(ps[si]);
        match ps[si] {
            ConstructionStep::CircleLine { circle, line, .. } => {
                assert forall|ci: int| 0 <= ci < cs.len()
                    && locus_is_nontrivial(
                        constraint_to_locus(#[trigger] cs[ci], exec_res, target))
                implies
                    locus_eqv(constraint_to_locus(cs[ci], exec_res, target),
                        Locus2d::OnCircle(circle))
                    || locus_eqv(constraint_to_locus(cs[ci], exec_res, target),
                        Locus2d::OnLine(line))
                by {
                    let prm_locus = constraint_to_locus(cs[ci], prm, target);
                    let exec_locus = constraint_to_locus(cs[ci], exec_res, target);
                    if locus_is_nontrivial(prm_locus) {
                        if locus_eqv(prm_locus, Locus2d::OnCircle(circle)) {
                            lemma_locus_eqv_symmetric(prm_locus, exec_locus);
                            lemma_locus_eqv_transitive(exec_locus, prm_locus,
                                Locus2d::OnCircle(circle));
                        } else {
                            lemma_locus_eqv_symmetric(prm_locus, exec_locus);
                            lemma_locus_eqv_transitive(exec_locus, prm_locus,
                                Locus2d::OnLine(line));
                        }
                    }
                }
            }
            ConstructionStep::CircleCircle { circle1, circle2, .. } => {
                assert forall|ci: int| 0 <= ci < cs.len()
                    && locus_is_nontrivial(
                        constraint_to_locus(#[trigger] cs[ci], exec_res, target))
                implies
                    locus_eqv(constraint_to_locus(cs[ci], exec_res, target),
                        Locus2d::OnCircle(circle1))
                    || locus_eqv(constraint_to_locus(cs[ci], exec_res, target),
                        Locus2d::OnCircle(circle2))
                by {
                    let prm_locus = constraint_to_locus(cs[ci], prm, target);
                    let exec_locus = constraint_to_locus(cs[ci], exec_res, target);
                    if locus_is_nontrivial(prm_locus) {
                        if locus_eqv(prm_locus, Locus2d::OnCircle(circle1)) {
                            lemma_locus_eqv_symmetric(prm_locus, exec_locus);
                            lemma_locus_eqv_transitive(exec_locus, prm_locus,
                                Locus2d::OnCircle(circle1));
                        } else {
                            lemma_locus_eqv_symmetric(prm_locus, exec_locus);
                            lemma_locus_eqv_transitive(exec_locus, prm_locus,
                                Locus2d::OnCircle(circle2));
                        }
                    }
                }
            }
            _ => {} //  rational steps handled above
        }
    }
}

///  Prove loop invariants for si+1 after a step update.
///  Extracted to reduce rlimit in the main loop.
proof fn lemma_loop_step_update(
    ps: ConstructionPlan<RationalModel>,
    cs: Seq<Constraint<RationalModel>>,
    si: int,
    n_points: int,
    points_view_seq: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
    prm: ResolvedPoints<RationalModel>,
    exec_res: ResolvedPoints<RationalModel>,
    target: nat,
)
    requires
        0 <= si < ps.len(),
        n_points > 0,
        points_view_seq.len() == n_points,
        flags.len() == n_points,
        target == step_target(ps[si]),
        (target as int) < n_points,
        exec_res == execute_plan(ps.take(si)),
        //  prm domain matches exec_res (both exclude target)
        prm.dom() =~= exec_res.dom(),
        //  prm values agree with exec_res for non-circle targets
        forall|id: EntityId| exec_res.dom().contains(id)
            && !circle_targets(ps).contains(id)
            ==> prm[id] == exec_res[id],
        //  Flags just updated: flags[target] is true
        flags[target as int],
        //  All other flags unchanged from domain invariant
        forall|id: nat| (id as int) < n_points && id != target ==>
            (flags[id as int] <==> execute_plan(ps.take(si)).dom().contains(id)),
        //  Target was not in old domain
        !execute_plan(ps.take(si)).dom().contains(target),
        //  Old domain elements are bounded
        forall|id: EntityId| execute_plan(ps.take(si)).dom().contains(id) ==>
            (id as int) < n_points,
        //  Self-consistency of NEW flags
        forall|i: int| 0 <= i < n_points ==>
            (#[trigger] flags[i]) ==
            partial_resolved_map(points_view_seq, flags).dom().contains(i as nat),
        //  Value: non-circle targets match for current exec_res
        forall|id: EntityId|
            execute_plan(ps.take(si)).dom().contains(id)
            && !circle_targets(ps).contains(id)
            ==> points_view_seq[id as int] == execute_plan(ps.take(si))[id],
        //  For newly inserted target: rational step → point updated
        is_rational_step(ps[si]) ==>
            points_view_seq[target as int] == execute_step(ps[si]),
        //  Preconditions for transfer
        is_fully_independent_plan(ps, cs),
        forall|ci: int| 0 <= ci < cs.len() ==>
            constraint_well_formed(#[trigger] cs[ci]),
        //  Conjuncts established against prm
        at_most_two_nontrivial_loci(target, cs, prm.dom()),
        forall|ci: int| 0 <= ci < cs.len() ==>
            constraint_locus_nondegenerate(#[trigger] cs[ci], prm, target),
        is_rational_step(ps[si]) ==>
            step_satisfies_all_constraint_loci(ps[si], cs, prm),
        !is_rational_step(ps[si]) ==>
            step_loci_match_geometry(ps[si], cs, prm),
    ensures
        //  Domain invariant for si+1
        forall|id: nat| (id as int) < n_points ==>
            (flags[id as int] <==>
             execute_plan(ps.take(si + 1)).dom().contains(id)),
        forall|id: EntityId| #![trigger execute_plan(ps.take(si + 1)).dom().contains(id)]
            execute_plan(ps.take(si + 1)).dom().contains(id) ==>
            (id as int) < n_points,
        //  Value invariant for si+1
        forall|id: EntityId|
            execute_plan(ps.take(si + 1)).dom().contains(id)
            && !circle_targets(ps).contains(id)
            ==> points_view_seq[id as int] == execute_plan(ps.take(si + 1))[id],
        //  Conjuncts for step si
        at_most_two_nontrivial_loci(step_target(ps[si]), cs,
            execute_plan(ps.take(si)).dom()),
        forall|ci: int| 0 <= ci < cs.len() ==>
            constraint_locus_nondegenerate(#[trigger] cs[ci],
                execute_plan(ps.take(si)), step_target(ps[si])),
        is_rational_step(ps[si]) ==>
            step_satisfies_all_constraint_loci(ps[si], cs,
                execute_plan(ps.take(si))),
        !is_rational_step(ps[si]) ==>
            step_loci_match_geometry(ps[si], cs,
                execute_plan(ps.take(si))),
{
    lemma_execute_plan_take_step::<RationalModel>(ps, si);
    let new_exec_res = execute_plan(ps.take(si + 1));

    //  Domain invariant for si+1
    assert forall|id: nat| (id as int) < n_points implies
        (flags[id as int] <==> new_exec_res.dom().contains(id))
    by {
        if id == target { } else { }
    }

    assert forall|id: EntityId|
        new_exec_res.dom().contains(id) implies (id as int) < n_points
    by {
        if id == step_target(ps[si]) { } else { }
    }

    //  Value invariant update for si+1
    assert forall|id: EntityId|
        new_exec_res.dom().contains(id)
        && !circle_targets(ps).contains(id)
    implies
        points_view_seq[id as int] == new_exec_res[id]
    by {
        if id == step_target(ps[si]) {
            //  Rational: point updated to execute_step
            //  Circle: circle_targets.contains(target), vacuously true
        } else {
            //  Map.insert preserves others
        }
    }

    //  Transfer conjuncts from prm to exec_res
    //  prm.dom() =~= exec_res.dom() is a direct precondition
    assert(exec_res.dom() =~= execute_plan(ps.take(si)).dom());
    lemma_transfer_step_conjuncts(ps, cs, si, prm, exec_res);
}

///  Check that a point satisfies all loci at runtime.
fn check_point_satisfies_all_loci_exec(
    loci: &Vec<RuntimeLocus>,
    pt: &RuntimePoint2,
) -> (out: bool)
    requires
        pt.wf_spec(),
        forall|j: int| 0 <= j < loci@.len() ==>
            (#[trigger] loci@[j]).wf_spec(),
    ensures
        out ==> forall|k: int| 0 <= k < loci@.len() ==>
            point_satisfies_locus(
                (#[trigger] loci@[k]).spec_locus(), pt@),
{
    let mut ci: usize = 0;
    while ci < loci.len()
        invariant
            ci <= loci@.len(),
            pt.wf_spec(),
            forall|j: int| 0 <= j < loci@.len() ==>
                (#[trigger] loci@[j]).wf_spec(),
            forall|k: int| 0 <= k < ci ==>
                point_satisfies_locus(
                    (#[trigger] loci@[k]).spec_locus(), pt@),
        decreases loci@.len() - ci,
    {
        if !point_satisfies_locus_exec(&loci[ci], pt) {
            return false;
        }
        ci = ci + 1;
    }
    true
}

///  Check that all nontrivial loci match a circle or line (CircleLine geometry).
fn check_all_loci_match_circle_line_exec(
    loci: &Vec<RuntimeLocus>,
    circle: &RuntimeCircle2,
    line: &RuntimeLine2,
) -> (out: bool)
    requires
        circle.wf_spec(),
        line.wf_spec(),
        forall|j: int| 0 <= j < loci@.len() ==>
            (#[trigger] loci@[j]).wf_spec(),
    ensures
        out ==> forall|k: int| 0 <= k < loci@.len()
            && locus_is_nontrivial(
                (#[trigger] loci@[k]).spec_locus())
        ==> locus_eqv(loci@[k].spec_locus(),
                Locus2d::OnCircle(circle@))
            || locus_eqv(loci@[k].spec_locus(),
                Locus2d::OnLine(line@)),
{
    let mut ci: usize = 0;
    while ci < loci.len()
        invariant
            ci <= loci@.len(),
            circle.wf_spec(),
            line.wf_spec(),
            forall|j: int| 0 <= j < loci@.len() ==>
                (#[trigger] loci@[j]).wf_spec(),
            forall|k: int| 0 <= k < ci
                && locus_is_nontrivial(
                    (#[trigger] loci@[k]).spec_locus())
            ==> locus_eqv(loci@[k].spec_locus(),
                    Locus2d::OnCircle(circle@))
                || locus_eqv(loci@[k].spec_locus(),
                    Locus2d::OnLine(line@)),
        decreases loci@.len() - ci,
    {
        match &loci[ci] {
            RuntimeLocus::FullPlane => { }
            RuntimeLocus::OnCircle { circle: locus_circle } => {
                if !locus_circle.center.x.eq(&circle.center.x)
                    || !locus_circle.center.y.eq(&circle.center.y)
                    || !locus_circle.radius_sq.eq(&circle.radius_sq) {
                    return false;
                }
            }
            RuntimeLocus::OnLine { line: locus_line } => {
                if !locus_line.a.eq(&line.a)
                    || !locus_line.b.eq(&line.b)
                    || !locus_line.c.eq(&line.c) {
                    return false;
                }
            }
            RuntimeLocus::AtPoint { .. } => {
                return false;
            }
        }
        ci = ci + 1;
    }
    true
}

///  Check that all nontrivial loci match one of two circles (CircleCircle geometry).
fn check_all_loci_match_circle_circle_exec(
    loci: &Vec<RuntimeLocus>,
    c1: &RuntimeCircle2,
    c2: &RuntimeCircle2,
) -> (out: bool)
    requires
        c1.wf_spec(),
        c2.wf_spec(),
        forall|j: int| 0 <= j < loci@.len() ==>
            (#[trigger] loci@[j]).wf_spec(),
    ensures
        out ==> forall|k: int| 0 <= k < loci@.len()
            && locus_is_nontrivial(
                (#[trigger] loci@[k]).spec_locus())
        ==> locus_eqv(loci@[k].spec_locus(),
                Locus2d::OnCircle(c1@))
            || locus_eqv(loci@[k].spec_locus(),
                Locus2d::OnCircle(c2@)),
{
    let mut ci: usize = 0;
    while ci < loci.len()
        invariant
            ci <= loci@.len(),
            c1.wf_spec(),
            c2.wf_spec(),
            forall|j: int| 0 <= j < loci@.len() ==>
                (#[trigger] loci@[j]).wf_spec(),
            forall|k: int| 0 <= k < ci
                && locus_is_nontrivial(
                    (#[trigger] loci@[k]).spec_locus())
            ==> locus_eqv(loci@[k].spec_locus(),
                    Locus2d::OnCircle(c1@))
                || locus_eqv(loci@[k].spec_locus(),
                    Locus2d::OnCircle(c2@)),
        decreases loci@.len() - ci,
    {
        match &loci[ci] {
            RuntimeLocus::FullPlane => { }
            RuntimeLocus::OnCircle { circle: locus_circle } => {
                let match_c1 =
                    locus_circle.center.x.eq(&c1.center.x)
                    && locus_circle.center.y.eq(&c1.center.y)
                    && locus_circle.radius_sq.eq(&c1.radius_sq);
                let match_c2 =
                    locus_circle.center.x.eq(&c2.center.x)
                    && locus_circle.center.y.eq(&c2.center.y)
                    && locus_circle.radius_sq.eq(&c2.radius_sq);
                if !match_c1 && !match_c2 {
                    return false;
                }
            }
            _ => {
                return false;
            }
        }
        ci = ci + 1;
    }
    true
}

///  Check constraint_locus_nondegenerate for all constraints at a given step.
fn check_step_nondegeneracy_all_exec(
    constraints: &Vec<RuntimeConstraint>,
    points: &Vec<RuntimePoint2>,
    flags: &Vec<bool>,
    target: usize,
    n_points: usize,
) -> (out: bool)
    requires
        n_points == points@.len(),
        flags@.len() == n_points,
        all_points_wf(points@),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
        forall|i: int| 0 <= i < n_points as int ==>
            (#[trigger] flags@[i]) ==
            partial_resolved_map(points_view(points@), flags@)
                .dom().contains(i as nat),
    ensures
        out ==> {
            let prm = partial_resolved_map(points_view(points@), flags@);
            forall|ci: int| 0 <= ci < constraints@.len() ==>
                constraint_locus_nondegenerate(
                    runtime_constraint_model(#[trigger] constraints@[ci]),
                    prm, target as nat)
        }
{
    let ghost prm = partial_resolved_map(points_view(points@), flags@);
    let mut ci2: usize = 0;
    while ci2 < constraints.len()
        invariant
            ci2 <= constraints@.len(),
            n_points == points@.len(),
            flags@.len() == n_points,
            all_points_wf(points@),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
            forall|i: int| 0 <= i < n_points as int ==>
                (#[trigger] flags@[i]) ==
                partial_resolved_map(points_view(points@), flags@)
                    .dom().contains(i as nat),
            forall|k: int| 0 <= k < ci2 ==>
                constraint_locus_nondegenerate(
                    runtime_constraint_model(#[trigger] constraints@[k]),
                    prm, target as nat),
            prm == partial_resolved_map(points_view(points@), flags@),
        decreases constraints@.len() - ci2,
    {
        match &constraints[ci2] {
            RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
                if *point == target {
                    if flags[*axis_a] && flags[*axis_b] {
                        let d = sq_dist_2d_exec(&points[*axis_b], &points[*axis_a]);
                        let zero = RuntimeRational::from_int(0);
                        if d.eq(&zero) {
                            return false;
                        }
                        proof {
                            assert(prm[*axis_a as nat]
                                == points_view(points@)[*axis_a as int]);
                            assert(prm[*axis_b as nat]
                                == points_view(points@)[*axis_b as int]);
                            assert(prm[*axis_a as nat] == points@[*axis_a as int]@);
                            assert(prm[*axis_b as nat] == points@[*axis_b as int]@);
                        }
                    }
                }
            }
            _ => { }
        }
        proof {
            assert(constraint_locus_nondegenerate(
                runtime_constraint_model(constraints@[ci2 as int]),
                prm, target as nat));
        }
        ci2 = ci2 + 1;
    }
    true
}

///  Connect loci results to step_satisfies_all_constraint_loci for rational steps.
proof fn lemma_connect_rational_loci(
    loci: Seq<RuntimeLocus>,
    prm: ResolvedPoints<RationalModel>,
    cs: Seq<Constraint<RationalModel>>,
    ps: ConstructionPlan<RationalModel>,
    si: int,
    pt: Point2<RationalModel>,
)
    requires
        loci.len() == cs.len(),
        forall|k: int| 0 <= k < loci.len() ==>
            point_satisfies_locus(
                (#[trigger] loci[k]).spec_locus(), pt),
        forall|ci: int| 0 <= ci < cs.len() ==>
            loci[ci].spec_locus() == constraint_to_locus(
                #[trigger] cs[ci], prm, step_target(ps[si])),
        0 <= si < ps.len(),
        pt == execute_step(ps[si]),
    ensures
        step_satisfies_all_constraint_loci(ps[si], cs, prm),
{
    assert forall|ci2: int| 0 <= ci2 < cs.len()
    implies point_satisfies_locus(
        constraint_to_locus(#[trigger] cs[ci2], prm, step_target(ps[si])),
        execute_step(ps[si]))
    by {
        assert(loci[ci2].spec_locus() == constraint_to_locus(
            cs[ci2], prm, step_target(ps[si])));
    }
}

///  Process a single step of the replay loop. Checks conjuncts 9-12 for step si,
///  updates points/flags, and proves the loop invariant update.
///  Takes and returns owned Vecs to avoid &mut borrow limitations in Verus.
fn process_single_step(
    full_plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    points: Vec<RuntimePoint2>,
    flags: Vec<bool>,
    si: usize,
    n_points: usize,
    Ghost(ps): Ghost<ConstructionPlan<RationalModel>>,
    Ghost(cs): Ghost<Seq<Constraint<RationalModel>>>,
) -> (out: (bool, Vec<RuntimePoint2>, Vec<bool>))
    requires
        si < full_plan@.len(),
        points@.len() == n_points,
        flags@.len() == n_points,
        n_points > 0,
        all_points_wf(points@),
        //  Structural preconditions
        forall|i: int| 0 <= i < full_plan@.len() ==>
            (#[trigger] full_plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < full_plan@.len() ==>
            (step_target((#[trigger] full_plan@[i]).spec_step()) as int) < n_points,
        forall|i: int, j: int|
            0 <= i < full_plan@.len() && 0 <= j < full_plan@.len() && i != j ==>
            step_target((#[trigger] full_plan@[i]).spec_step())
                != step_target((#[trigger] full_plan@[j]).spec_step()),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
        forall|ci: int| 0 <= ci < constraints@.len() ==>
            constraint_well_formed(
                runtime_constraint_model(#[trigger] constraints@[ci])),
        forall|i: int| 0 <= i < full_plan@.len() ==>
            step_geometrically_valid((#[trigger] full_plan@[i]).spec_step()),
        is_fully_independent_plan(ps, cs),
        //  Identity
        ps.len() == full_plan@.len(),
        cs.len() == constraints@.len(),
        forall|j: int| 0 <= j < full_plan@.len() ==>
            (#[trigger] ps[j]) == full_plan@[j].spec_step(),
        forall|j: int| 0 <= j < constraints@.len() ==>
            (#[trigger] cs[j]) == runtime_constraint_model(constraints@[j]),
        //  Self-consistency
        forall|i: int| 0 <= i < n_points as int ==>
            (#[trigger] flags@[i]) ==
            partial_resolved_map(points_view(points@), flags@)
                .dom().contains(i as nat),
        //  Domain invariant at si
        forall|id: nat| (id as int) < n_points ==>
            (flags@[id as int] <==>
             execute_plan(ps.take(si as int)).dom().contains(id)),
        forall|id: EntityId|
            execute_plan(ps.take(si as int)).dom().contains(id) ==>
            (id as int) < n_points,
        //  Value invariant at si
        forall|id: EntityId|
            execute_plan(ps.take(si as int)).dom().contains(id)
            && !circle_targets(ps).contains(id)
            ==> points_view(points@)[id as int]
                == execute_plan(ps.take(si as int))[id],
    ensures
        ({
            let (ok, pts, flgs) = out;
            &&& pts@.len() == n_points
            &&& flgs@.len() == n_points
            &&& all_points_wf(pts@)
            //  Self-consistency maintained
            &&& forall|i: int| 0 <= i < n_points as int ==>
                (#[trigger] flgs@[i]) ==
                partial_resolved_map(points_view(pts@), flgs@)
                    .dom().contains(i as nat)
            //  On success: domain invariant at si+1
            &&& (ok ==> forall|id: nat| (id as int) < n_points ==>
                (flgs@[id as int] <==>
                 execute_plan(ps.take(si + 1)).dom().contains(id)))
            &&& (ok ==> forall|id: EntityId|
                #![trigger execute_plan(ps.take(si + 1)).dom().contains(id)]
                execute_plan(ps.take(si + 1)).dom().contains(id) ==>
                (id as int) < n_points)
            //  On success: value invariant at si+1
            &&& (ok ==> forall|id: EntityId|
                execute_plan(ps.take(si + 1)).dom().contains(id)
                && !circle_targets(ps).contains(id)
                ==> points_view(pts@)[id as int]
                    == execute_plan(ps.take(si + 1))[id])
            //  On success: conjuncts for step si
            &&& (ok ==> at_most_two_nontrivial_loci(step_target(ps[si as int]), cs,
                execute_plan(ps.take(si as int)).dom()))
            &&& (ok ==> forall|ci: int| 0 <= ci < cs.len() ==>
                constraint_locus_nondegenerate(#[trigger] cs[ci],
                    execute_plan(ps.take(si as int)), step_target(ps[si as int])))
            &&& (ok ==> is_rational_step(ps[si as int]) ==>
                step_satisfies_all_constraint_loci(ps[si as int], cs,
                    execute_plan(ps.take(si as int))))
            &&& (ok ==> !is_rational_step(ps[si as int]) ==>
                step_loci_match_geometry(ps[si as int], cs,
                    execute_plan(ps.take(si as int))))
        })
{
    let mut points = points;
    let mut flags = flags;
    let target = full_plan[si].target_id();
    let ghost prm = partial_resolved_map(points_view(points@), flags@);
    let ghost exec_res = execute_plan(ps.take(si as int));

    proof {
        assert(prm.dom() =~= exec_res.dom());
        assert forall|id: EntityId| exec_res.dom().contains(id)
            && !circle_targets(ps).contains(id)
        implies prm[id] == exec_res[id]
        by { }
    }

    //  === Conjunct 9: at_most_two_nontrivial_loci ===
    if !check_at_most_two_nontrivial_exec(target, constraints, &flags, n_points) {
        return (false, points, flags);
    }

    //  Bridge: check_at_most_two_nontrivial_exec ensures uses Seq::new/Set::new,
    //  but we need at_most_two_nontrivial_loci(target, cs, prm.dom()).
    proof {
        //  Connect cs to the Seq::new in the check's ensures
        assert(cs =~= Seq::new(constraints@.len() as nat,
            |i: int| runtime_constraint_model(constraints@[i])));
        //  Connect prm.dom() to the Set::new in the check's ensures
        assert(prm.dom() =~= Set::new(
            |id: nat| (id as int) < n_points && flags@[id as int]));
        assert(at_most_two_nontrivial_loci(target as nat, cs, prm.dom()));
    }

    //  === Conjunct 12: Symmetric nondegeneracy ===
    if !check_step_nondegeneracy_all_exec(constraints, &points, &flags, target, n_points) {
        return (false, points, flags);
    }

    //  Bridge: check_step_nondegeneracy_all_exec ensures uses prm at current state
    let ghost nondegen_fact: bool = forall|ci: int| 0 <= ci < cs.len() ==>
        constraint_locus_nondegenerate(#[trigger] cs[ci], prm, target as nat);
    proof {
        assert forall|ci: int| 0 <= ci < cs.len()
        implies constraint_locus_nondegenerate(#[trigger] cs[ci], prm, target as nat)
        by {
            assert(cs[ci] == runtime_constraint_model(constraints@[ci]));
        }
        assert(nondegen_fact);
    }

    //  === Collect loci ===
    let loci = collect_loci_exec(constraints, &points, &flags, target);

    //  === Conjuncts 10/11: check per step type ===
    match &full_plan[si] {
        RuntimeStepData::PointStep { target: _, x, y, .. } => {
            let pt = RuntimePoint2::new(copy_rational(x), copy_rational(y));
            if !check_point_satisfies_all_loci_exec(&loci, &pt) {
                return (false, points, flags);
            }
            proof {
                assert(pt@ == execute_step::<RationalModel>(ps[si as int]));
                lemma_connect_rational_loci(loci@, prm, cs, ps, si as int, pt@);
            }
            let mut swap_pt = pt;
            points.set_and_swap(target, &mut swap_pt);
        }
        RuntimeStepData::LineLine { target: _, l1, l2, .. } => {
            let pt = execute_line_line_step(l1, l2);
            if !check_point_satisfies_all_loci_exec(&loci, &pt) {
                return (false, points, flags);
            }
            proof {
                assert(pt@ == execute_step::<RationalModel>(ps[si as int]));
                lemma_connect_rational_loci(loci@, prm, cs, ps, si as int, pt@);
            }
            let mut swap_pt = pt;
            points.set_and_swap(target, &mut swap_pt);
        }
        RuntimeStepData::CircleLine { target: _, circle, line, .. } => {
            if !check_all_loci_match_circle_line_exec(&loci, circle, line) {
                return (false, points, flags);
            }
            proof {
                assert forall|ci2: int| 0 <= ci2 < cs.len()
                    && locus_is_nontrivial(
                        constraint_to_locus(#[trigger] cs[ci2], prm,
                            step_target(ps[si as int])))
                implies
                    locus_eqv(constraint_to_locus(cs[ci2], prm,
                        step_target(ps[si as int])),
                        Locus2d::OnCircle(circle@))
                    || locus_eqv(constraint_to_locus(cs[ci2], prm,
                        step_target(ps[si as int])),
                        Locus2d::OnLine(line@))
                by {
                    assert(loci@[ci2].spec_locus() == constraint_to_locus(
                        cs[ci2], prm, step_target(ps[si as int])));
                }
            }
        }
        RuntimeStepData::CircleCircle { target: _, c1, c2, .. } => {
            if !check_all_loci_match_circle_circle_exec(&loci, c1, c2) {
                return (false, points, flags);
            }
            proof {
                assert forall|ci2: int| 0 <= ci2 < cs.len()
                    && locus_is_nontrivial(
                        constraint_to_locus(#[trigger] cs[ci2], prm,
                            step_target(ps[si as int])))
                implies
                    locus_eqv(constraint_to_locus(cs[ci2], prm,
                        step_target(ps[si as int])),
                        Locus2d::OnCircle(c1@))
                    || locus_eqv(constraint_to_locus(cs[ci2], prm,
                        step_target(ps[si as int])),
                        Locus2d::OnCircle(c2@))
                by {
                    assert(loci@[ci2].spec_locus() == constraint_to_locus(
                        cs[ci2], prm, step_target(ps[si as int])));
                }
            }
        }
    }

    //  === Update flags ===
    let mut flag = true;
    flags.set_and_swap(target, &mut flag);

    proof {
        //  Self-consistency after flag update
        assert forall|i: int| 0 <= i < n_points as int implies
            (#[trigger] flags@[i]) ==
            partial_resolved_map(points_view(points@), flags@)
                .dom().contains(i as nat)
        by { }

        if is_rational_step(ps[si as int]) {
            assert(step_satisfies_all_constraint_loci(ps[si as int], cs, prm));
        }
        if !is_rational_step(ps[si as int]) {
            assert(step_loci_match_geometry(ps[si as int], cs, prm));
        }

        //  Prove target not in old domain (needed by lemma_loop_step_update)
        //  Requires distinct targets on ps
        assert forall|i: int, j: int|
            0 <= i < ps.len() && 0 <= j < ps.len() && i != j
        implies step_target(ps[i]) != step_target(ps[j])
        by {
            //  ps[i] == full_plan@[i].spec_step(), connect distinct targets
            assert(ps[i] == full_plan@[i].spec_step());
            assert(ps[j] == full_plan@[j].spec_step());
        }
        lemma_step_target_not_in_prefix::<RationalModel>(ps, si as int);

        //  Help Z3 connect post-mutation state to lemma preconditions
        assert(target as nat == step_target(ps[si as int]));
        assert((target as int) < n_points);
        assert(flags@[target as int]);
        assert(!execute_plan(ps.take(si as int)).dom().contains(target as nat));
        assert(points_view(points@).len() == n_points);

        //  Value: non-target entries preserved through set_and_swap
        assert forall|id: EntityId|
            execute_plan(ps.take(si as int)).dom().contains(id)
            && !circle_targets(ps).contains(id)
        implies
            points_view(points@)[id as int] == execute_plan(ps.take(si as int))[id]
        by {
            //  id in old domain => id != target (target not in old domain)
            //  set_and_swap only changed index target, so points@[id as int] unchanged
        }

        //  Rational step: point was updated at target
        if is_rational_step(ps[si as int]) {
            assert(points_view(points@)[target as int] ==
                execute_step::<RationalModel>(ps[si as int]));
        }

        //  Other flags unchanged
        assert forall|id: nat| (id as int) < n_points && id != target as nat
        implies
            (flags@[id as int] <==> execute_plan(ps.take(si as int)).dom().contains(id))
        by { }

        lemma_loop_step_update(
            ps, cs, si as int, n_points as int,
            points_view(points@), flags@,
            prm, exec_res, target as nat,
        );
    }
    (true, points, flags)
}

///  Recursive replay of the plan from step `si`, checking conjuncts 9-12 at each step.
///  Uses recursion instead of a while loop to avoid expensive loop invariant checking.
fn check_dynamic_conjuncts_recursive(
    full_plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    points: Vec<RuntimePoint2>,
    flags: Vec<bool>,
    si: usize,
    n_points: usize,
    Ghost(ps): Ghost<ConstructionPlan<RationalModel>>,
    Ghost(cs): Ghost<Seq<Constraint<RationalModel>>>,
) -> (out: bool)
    requires
        si <= full_plan@.len(),
        points@.len() == n_points,
        flags@.len() == n_points,
        n_points > 0,
        all_points_wf(points@),
        //  Forwarded preconditions
        forall|i: int| 0 <= i < full_plan@.len() ==>
            (#[trigger] full_plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < full_plan@.len() ==>
            (step_target((#[trigger] full_plan@[i]).spec_step()) as int) < n_points,
        forall|i: int, j: int|
            0 <= i < full_plan@.len() && 0 <= j < full_plan@.len() && i != j ==>
            step_target((#[trigger] full_plan@[i]).spec_step())
                != step_target((#[trigger] full_plan@[j]).spec_step()),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
        forall|ci: int| 0 <= ci < constraints@.len() ==>
            constraint_well_formed(
                runtime_constraint_model(#[trigger] constraints@[ci])),
        forall|i: int| 0 <= i < full_plan@.len() ==>
            step_geometrically_valid((#[trigger] full_plan@[i]).spec_step()),
        is_fully_independent_plan(ps, cs),
        //  Identity
        ps.len() == full_plan@.len(),
        cs.len() == constraints@.len(),
        forall|j: int| 0 <= j < full_plan@.len() ==>
            (#[trigger] ps[j]) == full_plan@[j].spec_step(),
        forall|j: int| 0 <= j < constraints@.len() ==>
            (#[trigger] cs[j]) == runtime_constraint_model(constraints@[j]),
        //  Self-consistency
        forall|i: int| 0 <= i < n_points as int ==>
            (#[trigger] flags@[i]) ==
            partial_resolved_map(points_view(points@), flags@)
                .dom().contains(i as nat),
        //  Domain invariant at si
        forall|id: nat| (id as int) < n_points ==>
            (flags@[id as int] <==>
             execute_plan(ps.take(si as int)).dom().contains(id)),
        forall|id: EntityId|
            execute_plan(ps.take(si as int)).dom().contains(id) ==>
            (id as int) < n_points,
        //  Value invariant at si
        forall|id: EntityId|
            execute_plan(ps.take(si as int)).dom().contains(id)
            && !circle_targets(ps).contains(id)
            ==> points_view(points@)[id as int]
                == execute_plan(ps.take(si as int))[id],
    ensures
        out ==> {
            &&& forall|j: int| #![trigger ps[j]]
                si <= j < ps.len() ==>
                at_most_two_nontrivial_loci(step_target(ps[j]), cs,
                    execute_plan(ps.take(j)).dom())
            &&& forall|j: int| #![trigger ps[j]]
                si <= j < ps.len() && is_rational_step(ps[j]) ==>
                step_satisfies_all_constraint_loci(ps[j], cs,
                    execute_plan(ps.take(j)))
            &&& forall|j: int| #![trigger ps[j]]
                si <= j < ps.len() && !is_rational_step(ps[j]) ==>
                step_loci_match_geometry(ps[j], cs,
                    execute_plan(ps.take(j)))
            &&& forall|j: int, ci: int|
                #![trigger ps[j], cs[ci]]
                si <= j < ps.len() && 0 <= ci < cs.len() ==>
                constraint_locus_nondegenerate(cs[ci],
                    execute_plan(ps.take(j)), step_target(ps[j]))
        }
    decreases full_plan@.len() - si,
{
    if si >= full_plan.len() {
        return true;
    }
    let r = process_single_step(
        full_plan, constraints, points, flags,
        si, n_points, Ghost(ps), Ghost(cs));
    let new_points = r.1;
    let new_flags = r.2;
    if !r.0 {
        return false;
    }
    let rest = check_dynamic_conjuncts_recursive(
        full_plan, constraints, new_points, new_flags,
        si + 1, n_points, Ghost(ps), Ghost(cs));
    proof {
        if rest {
            //  Step si's conjuncts come from process_single_step.
            //  Steps si+1..len come from the recursive call.
            //  Z3 hint: the recursive call covers si+1..len, and process_single_step covers si.
            assert(at_most_two_nontrivial_loci(step_target(ps[si as int]), cs,
                execute_plan(ps.take(si as int)).dom()));
        }
    }
    rest
}

///  Replay the full plan at runtime, checking conjuncts 9-12 at each step.
pub fn check_full_plan_dynamic_conjuncts_exec(
    full_plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    n_points: usize,
) -> (out: bool)
    requires
        n_points > 0,
        forall|i: int| 0 <= i < full_plan@.len() ==>
            (#[trigger] full_plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < full_plan@.len() ==>
            (step_target((#[trigger] full_plan@[i]).spec_step()) as int) < n_points,
        forall|i: int, j: int|
            0 <= i < full_plan@.len() && 0 <= j < full_plan@.len() && i != j ==>
            step_target((#[trigger] full_plan@[i]).spec_step())
                != step_target((#[trigger] full_plan@[j]).spec_step()),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
        forall|ci: int| 0 <= ci < constraints@.len() ==>
            constraint_well_formed(
                runtime_constraint_model(#[trigger] constraints@[ci])),
        forall|i: int| 0 <= i < full_plan@.len() ==>
            step_geometrically_valid((#[trigger] full_plan@[i]).spec_step()),
        is_fully_independent_plan(
            plan_to_spec(full_plan@), constraints_to_spec(constraints@)),
    ensures
        out ==> {
            let ps = plan_to_spec(full_plan@);
            let cs = constraints_to_spec(constraints@);
            &&& forall|si: int| #![trigger ps[si]]
                0 <= si < ps.len() ==>
                at_most_two_nontrivial_loci(step_target(ps[si]), cs,
                    execute_plan(ps.take(si)).dom())
            &&& forall|si: int| #![trigger ps[si]]
                0 <= si < ps.len() && is_rational_step(ps[si]) ==>
                step_satisfies_all_constraint_loci(ps[si], cs,
                    execute_plan(ps.take(si)))
            &&& forall|si: int| #![trigger ps[si]]
                0 <= si < ps.len() && !is_rational_step(ps[si]) ==>
                step_loci_match_geometry(ps[si], cs,
                    execute_plan(ps.take(si)))
            &&& forall|si: int, ci: int|
                #![trigger ps[si], cs[ci]]
                0 <= si < ps.len() && 0 <= ci < cs.len() ==>
                constraint_locus_nondegenerate(cs[ci],
                    execute_plan(ps.take(si)), step_target(ps[si]))
        }
{
    let ghost ps = plan_to_spec(full_plan@);
    let ghost cs = constraints_to_spec(constraints@);

    //  Initialize working state: all-zero points, all-false flags
    let mut points: Vec<RuntimePoint2> = Vec::new();
    let mut flags: Vec<bool> = Vec::new();
    let mut init_i: usize = 0;
    while init_i < n_points
        invariant
            init_i <= n_points,
            points@.len() == init_i,
            flags@.len() == init_i,
            all_points_wf(points@),
            forall|j: int| 0 <= j < init_i ==> !(#[trigger] flags@[j]),
        decreases n_points - init_i,
    {
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        points.push(RuntimePoint2::new(x, y));
        flags.push(false);
        init_i = init_i + 1;
    }

    proof {
        //  Self-consistency: all flags false → prm.dom() empty
        assert forall|i: int| 0 <= i < n_points as int implies
            (#[trigger] flags@[i]) ==
            partial_resolved_map(points_view(points@), flags@).dom().contains(i as nat)
        by { }

        //  Domain invariant at si=0: execute_plan(ps.take(0)) = Map::empty()
        assert(ps.take(0) =~= Seq::<ConstructionStep<RationalModel>>::empty());

        //  plan_to_spec / constraints_to_spec identity
        assert(ps.len() == full_plan@.len());
        assert forall|j: int| 0 <= j < full_plan@.len() implies
            (#[trigger] ps[j]) == full_plan@[j].spec_step()
        by { }
        assert(cs.len() == constraints@.len());
        assert forall|j: int| 0 <= j < constraints@.len() implies
            (#[trigger] cs[j]) == runtime_constraint_model(constraints@[j])
        by { }
    }

    check_dynamic_conjuncts_recursive(
        full_plan, constraints, points, flags,
        0, n_points, Ghost(ps), Ghost(cs))
}

} //  verus!
