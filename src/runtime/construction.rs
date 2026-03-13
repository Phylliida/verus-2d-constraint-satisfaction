use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::line_intersection::*;
use verus_geometry::circle_line::*;
use verus_geometry::circle_circle::*;
use verus_geometry::runtime::point2::*;
use verus_geometry::runtime::line2::*;
use verus_geometry::runtime::circle2::*;
use verus_geometry::runtime::line_intersection::*;
use verus_geometry::runtime::circle_line::*;
use verus_geometry::runtime::circle_circle::*;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::runtime::RuntimeQExtRat;
use crate::construction::*;
use crate::entities::*;

use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Runtime construction step execution
// ===========================================================================

/// Execute a Fixed step: just wrap the given position.
pub fn execute_fixed_step(
    x: &RuntimeRational,
    y: &RuntimeRational,
) -> (out: RuntimePoint2)
    requires
        x.wf_spec(),
        y.wf_spec(),
    ensures
        out.wf_spec(),
        out@.x == x@,
        out@.y == y@,
{
    RuntimePoint2 {
        x: copy_rational(x),
        y: copy_rational(y),
        model: Ghost(Point2 { x: x@, y: y@ }),
    }
}

/// Execute a LineLine step.
pub fn execute_line_line_step(
    l1: &RuntimeLine2,
    l2: &RuntimeLine2,
) -> (out: RuntimePoint2)
    requires
        l1.wf_spec(),
        l2.wf_spec(),
        !line_det::<RationalModel>(l1@, l2@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == line_line_intersection_2d::<RationalModel>(l1@, l2@),
{
    line_line_intersection_2d_exec(l1, l2)
}

// ===========================================================================
//  Circle intersection step execution (quadratic extension coordinates)
// ===========================================================================

/// Runtime point in a quadratic extension field Q(sqrt(d)).
/// Stores (x, y) coordinates as RuntimeQExtRat<R>.
pub struct RuntimeQExtPoint2<R: Radicand<RationalModel>> {
    pub x: RuntimeQExtRat<R>,
    pub y: RuntimeQExtRat<R>,
    pub model: Ghost<Point2<SpecQuadExt<RationalModel, R>>>,
}

impl<R: Radicand<RationalModel>> View for RuntimeQExtPoint2<R> {
    type V = Point2<SpecQuadExt<RationalModel, R>>;

    open spec fn view(&self) -> Point2<SpecQuadExt<RationalModel, R>> {
        self.model@
    }
}

impl<R: Radicand<RationalModel>> RuntimeQExtPoint2<R> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
    }
}

/// Execute a CircleLine step: intersect a circle with a line.
/// Returns a point with coordinates in Q(sqrt(discriminant)).
/// R must encode the discriminant of the circle-line intersection.
pub fn execute_circle_line_step<R: PositiveRadicand<RationalModel>>(
    circle: &RuntimeCircle2,
    line: &RuntimeLine2,
    plus: bool,
) -> (out: RuntimeQExtPoint2<R>)
    where R: verus_quadratic_extension::runtime::RuntimeRadicand<R>
    requires
        circle.wf_spec(),
        line.wf_spec(),
        line2_nondegenerate(line@),
    ensures
        out.wf_spec(),
        out@ == cl_intersection_point::<RationalModel, R>(circle@, line@, plus),
{
    proof {
        lemma_cl_quad_a_positive::<RationalModel>(line@);
        RationalModel::axiom_lt_iff_le_and_not_eqv(
            RationalModel::from_int_spec(0),
            cl_quad_a::<RationalModel>(line@),
        );
        RationalModel::axiom_eqv_symmetric(
            RationalModel::from_int_spec(0),
            cl_quad_a::<RationalModel>(line@),
        );
    }
    let x = cl_intersection_x_exec::<R>(circle, line, plus);
    let y = cl_intersection_y_exec::<R>(circle, line, plus);
    let ghost model = cl_intersection_point::<RationalModel, R>(circle@, line@, plus);
    RuntimeQExtPoint2 { x, y, model: Ghost(model) }
}

/// Execute a CircleCircle step: intersect two circles.
/// Computes the radical axis and delegates to circle-line intersection.
pub fn execute_circle_circle_step<R: PositiveRadicand<RationalModel>>(
    c1: &RuntimeCircle2,
    c2: &RuntimeCircle2,
    plus: bool,
) -> (out: RuntimeQExtPoint2<R>)
    where R: verus_quadratic_extension::runtime::RuntimeRadicand<R>
    requires
        c1.wf_spec(),
        c2.wf_spec(),
        !c1@.center.eqv(c2@.center),
    ensures
        out.wf_spec(),
        out@ == cc_intersection_point::<RationalModel, R>(c1@, c2@, plus),
{
    let x = cc_intersection_x_exec::<R>(c1, c2, plus);
    let y = cc_intersection_y_exec::<R>(c1, c2, plus);
    let ghost model = cc_intersection_point::<RationalModel, R>(c1@, c2@, plus);
    RuntimeQExtPoint2 { x, y, model: Ghost(model) }
}

// ===========================================================================
//  Runtime plan types and executor
// ===========================================================================

/// Runtime data for a single construction step.
/// Each variant carries a ghost model linking it to the spec-level ConstructionStep.
/// The caller MUST provide a matching spec step — wf_spec checks correspondence.
pub enum RuntimeStepData {
    /// Fixed position.
    Fixed { x: RuntimeRational, y: RuntimeRational, model: Ghost<ConstructionStep<RationalModel>> },
    /// Intersection of two lines.
    LineLine { l1: RuntimeLine2, l2: RuntimeLine2, model: Ghost<ConstructionStep<RationalModel>> },
    /// Intersection of a circle and a line.
    CircleLine { circle: RuntimeCircle2, line: RuntimeLine2, plus: bool, model: Ghost<ConstructionStep<RationalModel>> },
    /// Intersection of two circles.
    CircleCircle { c1: RuntimeCircle2, c2: RuntimeCircle2, plus: bool, model: Ghost<ConstructionStep<RationalModel>> },
    /// Fully determined position.
    Determined { x: RuntimeRational, y: RuntimeRational, model: Ghost<ConstructionStep<RationalModel>> },
}

impl RuntimeStepData {
    /// The step data is well-formed: runtime fields match the ghost model,
    /// and all geometric preconditions for execution are met.
    pub open spec fn wf_spec(&self) -> bool {
        match self {
            RuntimeStepData::Fixed { x, y, model } =>
                x.wf_spec() && y.wf_spec() &&
                match model@ {
                    ConstructionStep::Fixed { position, .. } =>
                        x@ == position.x && y@ == position.y,
                    _ => false,
                },
            RuntimeStepData::LineLine { l1, l2, model } =>
                l1.wf_spec() && l2.wf_spec() &&
                !line_det::<RationalModel>(l1@, l2@).eqv(RationalModel::from_int_spec(0)) &&
                match model@ {
                    ConstructionStep::LineLine { line1, line2, .. } =>
                        l1@ == line1 && l2@ == line2,
                    _ => false,
                },
            RuntimeStepData::CircleLine { circle, line, plus, model } =>
                circle.wf_spec() && line.wf_spec() && line2_nondegenerate(line@) &&
                match model@ {
                    ConstructionStep::CircleLine { circle: c, line: l, plus: p, .. } =>
                        circle@ == c && line@ == l && *plus == p,
                    _ => false,
                },
            RuntimeStepData::CircleCircle { c1, c2, plus, model } =>
                c1.wf_spec() && c2.wf_spec() && !c1@.center.eqv(c2@.center) &&
                match model@ {
                    ConstructionStep::CircleCircle { circle1, circle2, plus: p, .. } =>
                        c1@ == circle1 && c2@ == circle2 && *plus == p,
                    _ => false,
                },
            RuntimeStepData::Determined { x, y, model } =>
                x.wf_spec() && y.wf_spec() &&
                match model@ {
                    ConstructionStep::Determined { position, .. } =>
                        x@ == position.x && y@ == position.y,
                    _ => false,
                },
        }
    }

    /// The spec-level construction step this runtime step corresponds to.
    pub open spec fn spec_step(&self) -> ConstructionStep<RationalModel> {
        match self {
            RuntimeStepData::Fixed { model, .. } => model@,
            RuntimeStepData::LineLine { model, .. } => model@,
            RuntimeStepData::CircleLine { model, .. } => model@,
            RuntimeStepData::CircleCircle { model, .. } => model@,
            RuntimeStepData::Determined { model, .. } => model@,
        }
    }
}

/// Runtime result of executing a construction step.
/// Tagged with the ghost entity ID so the caller can't mix up which
/// result corresponds to which entity.
pub enum RuntimeConstructionResult<R: Radicand<RationalModel>> {
    /// Result from Fixed, LineLine, or Determined steps (rational coordinates).
    RationalPoint { point: RuntimePoint2, entity_id: Ghost<EntityId> },
    /// Result from CircleLine or CircleCircle steps (quadratic extension coordinates).
    QExtPoint { point: RuntimeQExtPoint2<R>, entity_id: Ghost<EntityId> },
}

impl<R: Radicand<RationalModel>> RuntimeConstructionResult<R> {
    pub open spec fn wf_spec(&self) -> bool {
        match self {
            RuntimeConstructionResult::RationalPoint { point, .. } => point.wf_spec(),
            RuntimeConstructionResult::QExtPoint { point, .. } => point.wf_spec(),
        }
    }

    /// The entity ID this result is for.
    pub open spec fn entity_id(&self) -> EntityId {
        match self {
            RuntimeConstructionResult::RationalPoint { entity_id, .. } => entity_id@,
            RuntimeConstructionResult::QExtPoint { entity_id, .. } => entity_id@,
        }
    }

    /// For rational results, the spec-level point.
    /// Returns None for QExt results (different coordinate field).
    pub open spec fn rational_point(&self) -> Option<Point2<RationalModel>> {
        match self {
            RuntimeConstructionResult::RationalPoint { point, .. } => Some(point@),
            RuntimeConstructionResult::QExtPoint { .. } => None,
        }
    }

    /// For rational results, whether the computed point matches execute_step.
    /// Always true for QExt results (the correspondence is to cl/cc_intersection_point
    /// which lives in a different coordinate field).
    pub open spec fn matches_spec_step(&self, step: ConstructionStep<RationalModel>) -> bool {
        match self {
            RuntimeConstructionResult::RationalPoint { point, .. } =>
                point@ == execute_step(step),
            RuntimeConstructionResult::QExtPoint { .. } => true,
        }
    }
}

/// Execute a single runtime step, returning the computed point tagged with entity ID.
/// The ensures connects the output to the spec-level step:
/// - entity_id matches step_target of the spec model
/// - For rational steps (Fixed/LineLine/Determined), the output point == execute_step(spec_step)
pub fn execute_step_runtime<R: PositiveRadicand<RationalModel>>(
    step: &RuntimeStepData,
) -> (out: RuntimeConstructionResult<R>)
    where R: verus_quadratic_extension::runtime::RuntimeRadicand<R>
    requires step.wf_spec(),
    ensures
        out.wf_spec(),
        out.entity_id() == step_target(step.spec_step()),
        out.matches_spec_step(step.spec_step()),
{
    match step {
        RuntimeStepData::Fixed { x, y, model } => {
            let point = execute_fixed_step(x, y);
            let ghost eid = step_target(model@);
            RuntimeConstructionResult::RationalPoint { point, entity_id: Ghost(eid) }
        }
        RuntimeStepData::LineLine { l1, l2, model } => {
            let point = execute_line_line_step(l1, l2);
            let ghost eid = step_target(model@);
            RuntimeConstructionResult::RationalPoint { point, entity_id: Ghost(eid) }
        }
        RuntimeStepData::CircleLine { circle, line, plus, model } => {
            let point = execute_circle_line_step::<R>(circle, line, *plus);
            let ghost eid = step_target(model@);
            RuntimeConstructionResult::QExtPoint { point, entity_id: Ghost(eid) }
        }
        RuntimeStepData::CircleCircle { c1, c2, plus, model } => {
            let point = execute_circle_circle_step::<R>(c1, c2, *plus);
            let ghost eid = step_target(model@);
            RuntimeConstructionResult::QExtPoint { point, entity_id: Ghost(eid) }
        }
        RuntimeStepData::Determined { x, y, model } => {
            let point = execute_fixed_step(x, y);
            let ghost eid = step_target(model@);
            RuntimeConstructionResult::RationalPoint { point, entity_id: Ghost(eid) }
        }
    }
}

/// Execute a full construction plan: apply each step and collect results.
/// Each result is tagged with the entity ID from the spec-level plan.
/// If the spec-level steps have distinct targets, the output entity IDs are distinct.
pub fn execute_plan_runtime<R: PositiveRadicand<RationalModel>>(
    steps: &Vec<RuntimeStepData>,
) -> (out: Vec<RuntimeConstructionResult<R>>)
    where R: verus_quadratic_extension::runtime::RuntimeRadicand<R>
    requires
        forall|i: int| 0 <= i < steps@.len() ==> (#[trigger] steps@[i]).wf_spec(),
    ensures
        out@.len() == steps@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).entity_id() == step_target(steps@[i].spec_step()),
        forall|i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).matches_spec_step(steps@[i].spec_step()),
        // Distinct targets in → distinct entity IDs out
        forall|i: int, j: int|
            0 <= i < out@.len() && 0 <= j < out@.len() && i != j
            && step_target(steps@[i].spec_step()) != step_target(steps@[j].spec_step())
            ==> (#[trigger] out@[i]).entity_id() != (#[trigger] out@[j]).entity_id(),
{
    let mut results: Vec<RuntimeConstructionResult<R>> = Vec::new();
    let mut idx: usize = 0;
    while idx < steps.len()
        invariant
            0 <= idx <= steps@.len(),
            results@.len() == idx as int,
            forall|j: int| 0 <= j < results@.len() ==> (#[trigger] results@[j]).wf_spec(),
            forall|j: int| 0 <= j < results@.len() ==>
                (#[trigger] results@[j]).entity_id() == step_target(steps@[j].spec_step()),
            forall|j: int| 0 <= j < results@.len() ==>
                (#[trigger] results@[j]).matches_spec_step(steps@[j].spec_step()),
            forall|i: int| 0 <= i < steps@.len() ==> (#[trigger] steps@[i]).wf_spec(),
        decreases steps@.len() - idx,
    {
        let result = execute_step_runtime::<R>(&steps[idx]);
        results.push(result);
        idx = idx + 1;
    }
    results
}

} // verus!
