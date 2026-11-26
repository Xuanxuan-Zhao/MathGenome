import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

/-! Splitness and quasi-splitness for the rank-eight Clifford spin group. -/

namespace LinearAlgebraicGroups.Specs.Arithmetic.RankEightSpinStructure

open _root_.LinearAlgebraicGroups.Albert.SpinSpecification
  (IsSpinPointRepresentation ScalarClifford SchemePoints)
open scoped CategoryTheory.MonObj

universe u

set_option autoImplicit false

/-- The spin group of a hyperbolic form of rank eight is split reductive
and has a Borel subgroup over the ground field. -/
def HyperbolicSpinStructure : Prop :=
  ∀ {K : Type u} [Field K] (q : QuadraticForm K (Fin 8 → K))
    (H : AffineAlgebraicGroup K)
    (p : ∀ R : TestAlgebra K, SchemePoints H.val R →* (ScalarClifford q R)ˣ),
    LinearMap.ker q.polarBilin = ⊥ →
    IsSpinPointRepresentation q H.val p →
    q.Equivalent (OddSpinModels.hyperbolicForm (ULift.{u} (Fin 4)) K) →
    GeometricRadicals.IsSplitReductive H ∧ GeometricBorelConjugacy.IsQuasiSplit H

/-- Three hyperbolic planes and a regular anisotropic binary summand give
a quasi-split rank-eight spin group. -/
def BinaryKernelSpinStructure : Prop :=
  ∀ {K : Type u} [Field K] (q : QuadraticForm K (Fin 8 → K))
    (H : AffineAlgebraicGroup K)
    (p : ∀ R : TestAlgebra K, SchemePoints H.val R →* (ScalarClifford q R)ˣ),
    LinearMap.ker q.polarBilin = ⊥ →
    IsSpinPointRepresentation q H.val p →
    ∀ (q₀ : QuadraticForm K (Fin 2 → K)),
      LinearMap.ker q₀.polarBilin = ⊥ →
      ¬ IsotropicSpinGeneration.IsIsotropic q₀ →
      q.Equivalent ((OddSpinModels.hyperbolicForm (ULift.{u} (Fin 3)) K).prod q₀) →
      GeometricBorelConjugacy.IsQuasiSplit H

end LinearAlgebraicGroups.Specs.Arithmetic.RankEightSpinStructure
