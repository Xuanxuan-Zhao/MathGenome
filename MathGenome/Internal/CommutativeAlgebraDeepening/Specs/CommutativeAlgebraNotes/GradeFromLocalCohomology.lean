import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Noetherian.Defs

/-! The first nonzero degree of local cohomology detects grade (Theorem 2.1). -/

namespace Specs.CommutativeAlgebraNotes.GradeFromLocalCohomology

universe u

/-- The grade of an ideal on a finite module is the infimum of the nonzero local
cohomology degrees. An empty index type gives the value `⊤` in `ℕ∞`. -/
def gradeEqInfLocalCohomologyType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M],
    AdvCommAlg.Depth.grade I M =
      ⨅ q : {q : ℕ // Nontrivial ((IdealTorsion.localCohomology I (q : ℤ)).obj M)},
        (q.val : ℕ∞)

end Specs.CommutativeAlgebraNotes.GradeFromLocalCohomology
