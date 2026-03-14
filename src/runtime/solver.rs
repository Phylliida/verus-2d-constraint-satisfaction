use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::line_intersection::*;
use verus_geometry::runtime::point2::*;
use verus_geometry::runtime::line2::*;
use verus_geometry::runtime::circle2::*;
use verus_geometry::runtime::line_intersection::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use crate::entities::*;
use crate::constraints::*;
use crate::locus::*;
use crate::construction::*;
use crate::runtime::constraint::*;
use crate::runtime::locus::*;
use crate::runtime::construction::RuntimeStepData;

type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Runtime locus intersection
// ===========================================================================

/// Intersect two runtime loci to produce a construction step.
/// Mirrors spec-level `intersect_loci`.
/// Returns None if the intersection is underdetermined (FullPlane)
/// or the lines are parallel.
pub fn intersect_loci_exec(
    id: usize,
    l1: RuntimeLocus,
    l2: RuntimeLocus,
) -> (out: Option<RuntimeStepData>)
    requires
        l1.wf_spec(),
        l2.wf_spec(),
    ensures
        match out {
            Some(step) => step.wf_spec()
                && step.spec_step() == intersect_loci(
                    id as nat, l1.spec_locus(), l2.spec_locus(),
                ).unwrap(),
            #[allow(deprecated)]
            None => intersect_loci(
                id as nat, l1.spec_locus(), l2.spec_locus(),
            ).is_None(),
        },
{
    match (l1, l2) {
        // AtPoint overrides everything
        (RuntimeLocus::AtPoint { point }, _) => {
            let ghost spec_step = ConstructionStep::<RationalModel>::Determined {
                id: id as nat, position: point@,
            };
            Some(RuntimeStepData::Determined {
                x: point.x,
                y: point.y,
                model: Ghost(spec_step),
            })
        }
        (_, RuntimeLocus::AtPoint { point }) => {
            let ghost spec_step = ConstructionStep::<RationalModel>::Determined {
                id: id as nat, position: point@,
            };
            Some(RuntimeStepData::Determined {
                x: point.x,
                y: point.y,
                model: Ghost(spec_step),
            })
        }

        // Line-line
        (RuntimeLocus::OnLine { line: l1 }, RuntimeLocus::OnLine { line: l2 }) => {
            let det = line_det_exec(&l1, &l2);
            if det.is_zero() {
                None // Parallel or coincident lines
            } else {
                let ghost spec_step = ConstructionStep::<RationalModel>::LineLine {
                    id: id as nat, line1: l1@, line2: l2@,
                };
                Some(RuntimeStepData::LineLine {
                    l1, l2,
                    model: Ghost(spec_step),
                })
            }
        }

        // Circle-line
        (RuntimeLocus::OnCircle { circle }, RuntimeLocus::OnLine { line }) => {
            let ghost spec_step = ConstructionStep::<RationalModel>::CircleLine {
                id: id as nat, circle: circle@, line: line@, plus: true,
            };
            Some(RuntimeStepData::CircleLine {
                circle, line, plus: true,
                model: Ghost(spec_step),
            })
        }
        (RuntimeLocus::OnLine { line }, RuntimeLocus::OnCircle { circle }) => {
            let ghost spec_step = ConstructionStep::<RationalModel>::CircleLine {
                id: id as nat, circle: circle@, line: line@, plus: true,
            };
            Some(RuntimeStepData::CircleLine {
                circle, line, plus: true,
                model: Ghost(spec_step),
            })
        }

        // Circle-circle
        (RuntimeLocus::OnCircle { circle: c1 }, RuntimeLocus::OnCircle { circle: c2 }) => {
            let ghost spec_step = ConstructionStep::<RationalModel>::CircleCircle {
                id: id as nat, circle1: c1@, circle2: c2@, plus: true,
            };
            Some(RuntimeStepData::CircleCircle {
                c1, c2, plus: true,
                model: Ghost(spec_step),
            })
        }

        // FullPlane doesn't constrain
        (RuntimeLocus::FullPlane, _) => None,
        (_, RuntimeLocus::FullPlane) => None,
    }
}

// ===========================================================================
//  Greedy solver loop
// ===========================================================================

/// Collect loci for a target entity from all constraints.
/// Returns a Vec of RuntimeLocus values, one per constraint.
pub fn collect_loci_exec(
    constraints: &Vec<RuntimeConstraint>,
    points: &Vec<RuntimePoint2>,
    resolved_flags: &Vec<bool>,
    target: usize,
) -> (out: Vec<RuntimeLocus>)
    requires
        all_points_wf(points@),
        resolved_flags@.len() == points@.len(),
        (target as int) < points@.len(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) ==
            vec_to_resolved_map(points_view(points@)).dom().contains(i as nat),
    ensures
        out@.len() == constraints@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).spec_locus() == constraint_to_locus(
                runtime_constraint_model(constraints@[i]),
                vec_to_resolved_map(points_view(points@)),
                target as nat,
            ),
{
    let mut result: Vec<RuntimeLocus> = Vec::new();
    let mut ci: usize = 0;
    while ci < constraints.len()
        invariant
            0 <= ci <= constraints@.len(),
            result@.len() == ci as int,
            all_points_wf(points@),
            resolved_flags@.len() == points@.len(),
            (target as int) < points@.len(),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
            forall|i: int| 0 <= i < resolved_flags@.len() ==>
                (#[trigger] resolved_flags@[i]) ==
                vec_to_resolved_map(points_view(points@)).dom().contains(i as nat),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==>
                (#[trigger] result@[j]).spec_locus() == constraint_to_locus(
                    runtime_constraint_model(constraints@[j]),
                    vec_to_resolved_map(points_view(points@)),
                    target as nat,
                ),
        decreases constraints@.len() - ci,
    {
        let locus = constraint_to_locus_exec(&constraints[ci], points, resolved_flags, target);
        result.push(locus);
        ci = ci + 1;
    }
    result
}

/// Find two non-trivial loci and intersect them to produce a step.
/// Returns None if fewer than two non-trivial loci exist or intersection fails.
pub fn find_and_intersect_loci(
    target: usize,
    loci: Vec<RuntimeLocus>,
) -> (out: Option<RuntimeStepData>)
    requires
        forall|i: int| 0 <= i < loci@.len() ==> (#[trigger] loci@[i]).wf_spec(),
    ensures
        match out {
            Some(step) => step.wf_spec(),
            None => true,
        },
{
    // First pass: find first nontrivial locus
    let mut first_idx: usize = 0;
    let mut found_first = false;
    while first_idx < loci.len()
        invariant
            0 <= first_idx <= loci@.len(),
            !found_first,
            forall|j: int| 0 <= j < first_idx as int ==>
                !loci@[j].is_nontrivial(),
            forall|i: int| 0 <= i < loci@.len() ==> (#[trigger] loci@[i]).wf_spec(),
        decreases loci@.len() - first_idx,
    {
        match &loci[first_idx] {
            RuntimeLocus::FullPlane => {
                first_idx = first_idx + 1;
            }
            _ => {
                found_first = true;
                break;
            }
        }
    }

    if !found_first {
        return None;
    }

    // Second pass: find second nontrivial locus
    let mut second_idx: usize = first_idx + 1;
    let mut found_second = false;
    while second_idx < loci.len()
        invariant
            first_idx < second_idx && second_idx <= loci@.len(),
            !found_second,
            forall|j: int| first_idx < j < second_idx as int ==>
                !loci@[j].is_nontrivial(),
            forall|i: int| 0 <= i < loci@.len() ==> (#[trigger] loci@[i]).wf_spec(),
        decreases loci@.len() - second_idx,
    {
        match &loci[second_idx] {
            RuntimeLocus::FullPlane => {
                second_idx = second_idx + 1;
            }
            _ => {
                found_second = true;
                break;
            }
        }
    }

    if !found_second {
        // Only one nontrivial locus — check if it's AtPoint
        match &loci[first_idx] {
            RuntimeLocus::AtPoint { point } => {
                let ghost spec_step = ConstructionStep::<RationalModel>::Determined {
                    id: target as nat, position: point@,
                };
                return Some(RuntimeStepData::Determined {
                    x: copy_rational(&point.x),
                    y: copy_rational(&point.y),
                    model: Ghost(spec_step),
                });
            }
            _ => {
                return None;
            }
        }
    }

    // Extract the two loci by swapping out of the Vec
    // We need to consume them for intersect_loci_exec
    let mut loci_mut = loci;
    let mut dummy = RuntimeLocus::FullPlane;
    let mut dummy2 = RuntimeLocus::FullPlane;

    // Swap out the second first (to preserve indexing since second_idx > first_idx)
    loci_mut.set_and_swap(second_idx, &mut dummy);
    // Now dummy holds the second locus
    let l2 = dummy;

    // Swap out the first
    loci_mut.set_and_swap(first_idx, &mut dummy2);
    let l1 = dummy2;

    intersect_loci_exec(target, l1, l2)
}

} // verus!
