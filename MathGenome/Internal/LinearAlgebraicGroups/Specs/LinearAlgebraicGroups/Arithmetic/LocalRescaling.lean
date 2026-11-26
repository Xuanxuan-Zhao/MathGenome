import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing

open MeasureTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalRescaling

open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open LocalQuotientMixing (MixingCases)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
  (RationalPoints pointTopology)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
  (RightInvariant)

/-- A conjugate of a closed nondiscrete subgroup of finite covolume
contains the entire rational conjugacy class of a single noncentral point. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AffineAlgebraicGroup F),
    IsAbsolutelyAlmostSimple J → MixingCases J →
    letI := pointTopology J.val.X
    ∀ (H : Subgroup (RationalPoints J.val.X)),
      IsClosed (H : Set (RationalPoints J.val.X)) → ¬ DiscreteTopology H →
      ∀ (ν : Measure (_root_.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport.RightCosets H))
        [IsFiniteMeasure ν],
        ν ≠ 0 → RightInvariant ν →
        ∃ x u : RationalPoints J.val.X,
          u ∉ Subgroup.center (RationalPoints J.val.X) ∧
          ∀ g : RationalPoints J.val.X, x * (g * u * g⁻¹) * x⁻¹ ∈ H

end LinearAlgebraicGroups.Specs.Arithmetic.LocalRescaling
