import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PowerSeriesAndNoncompleteDVR
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PowerSeriesLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.NoncompleteDVRLocalCohomology

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.PowerSeriesAndNoncompleteDVR
open Specs.CommutativeAlgebraNotes.PowerSeriesLocalCohomology

universe u

private theorem inverseMonomial_finZero (k : Type u) [Field k] (a : Index 0) :
    inverseMonomial k 0 a = 1 := by
  have hexponent (n : ℕ) :
      Finsupp.equivFunOnFinite.symm (fun i : Fin 0 => n - (a i + 1)) = 0 := by
    ext i
    exact Fin.elim0 i
  have hproduct : fullProduct k 0 = 1 := Finset.prod_empty
  simp only [inverseMonomial, hexponent, MvPowerSeries.monomial_zero_one]
  calc
    fraction (fullProduct k 0) (Finset.univ.sup a + 1) 1 = Localization.mk 1 1 :=
      congrArg (Localization.mk 1) (Subtype.ext (by
        change fullProduct k 0 ^ (Finset.univ.sup a + 1) = 1
        rw [hproduct, one_pow]))
    _ = 1 := by rw [Localization.mk_one_eq_algebraMap, map_one]

/-- The two local cohomology computations of Example 4.10. -/
theorem powerSeriesAndNoncompleteDVR : LocalCohomologyExamples.{u} := by
  intro k _
  constructor
  · intro d
    obtain ⟨π, hsurj, hker, b, hb⟩ := PowerSeriesLocalCohomology.inverseMonomialBasis k d
    refine ⟨π, hsurj, hker, b, hb, ?_, PowerSeriesLocalCohomology.topIsInjectiveEnvelope k d⟩
    rintro rfl a
    rw [hb, inverseMonomial_finZero]
  · obtain ⟨hDVR, hmax, _, _, _⟩ := localLine_dvr k
    exact ⟨hDVR, hmax, localLine_not_isAdicComplete k, dvrLocalCohomologyFractionQuotient k,
      fun E => ⟨dvrLocalCohomologyResidueHull k E, dvrLocalCohomologyMatlisDual k E⟩⟩

end CommutativeAlgebraNotes
