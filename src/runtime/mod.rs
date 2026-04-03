///  Concrete runtime type aliases for rational-valued geometry types.
///  These pin the generic RuntimePoint2<R, V> etc. to RuntimeRational/Rational.
pub type RuntimePoint2 = verus_geometry::runtime::point2::RuntimePoint2<
    verus_rational::runtime_rational::RuntimeRational,
    verus_rational::rational::Rational,
>;
pub type RuntimeLine2 = verus_geometry::runtime::line2::RuntimeLine2<
    verus_rational::runtime_rational::RuntimeRational,
    verus_rational::rational::Rational,
>;
pub type RuntimeCircle2 = verus_geometry::runtime::circle2::RuntimeCircle2<
    verus_rational::runtime_rational::RuntimeRational,
    verus_rational::rational::Rational,
>;

#[cfg(verus_keep_ghost)]
pub mod construction;
#[cfg(verus_keep_ghost)]
pub mod constraint;
#[cfg(verus_keep_ghost)]
pub mod locus;
#[cfg(verus_keep_ghost)]
pub mod solver;
#[cfg(verus_keep_ghost)]
pub mod ext_constraint;
#[cfg(verus_keep_ghost)]
pub mod pipeline_proofs;
#[cfg(verus_keep_ghost)]
pub mod abstract_plan;
#[cfg(verus_keep_ghost)]
pub mod dyn_field;
#[cfg(verus_keep_ghost)]
pub mod dyn_pipeline;
#[cfg(verus_keep_ghost)]
pub mod pipeline;
