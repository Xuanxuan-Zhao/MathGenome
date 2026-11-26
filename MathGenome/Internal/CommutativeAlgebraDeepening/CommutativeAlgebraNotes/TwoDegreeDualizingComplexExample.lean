import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.TwoDegreeDualizingComplexExample
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation
import Batteries.Tactic.OpenPrivate

namespace CommutativeAlgebraNotes.TwoDegreeDualizingComplexExample

open Specs.CommutativeAlgebraNotes.TwoDegreeDualizingComplexExample
open Specs.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation
open Specs.CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation (XQuotient toXQuotient)
open private mem_xLine_iff projectS_eq_zero_iff project_section from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation

universe u

private theorem supportTorsion (k : Type u) [Field k] (r : R k) :
    r ∈ Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsion
      (IsLocalRing.maximalIdeal (R k)) (R k) ↔ ∃ c : k, r = c • x k := by
  obtain ⟨hm, hx, hxy, hker, hy, _⟩ := TwoDegreeExampleCechCalculation.ringStructure k
  change r ∈ (IsLocalRing.maximalIdeal (R k)).primaryComponent (R k) ↔ _
  simp only [Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff,
    SetLike.coe_sort_coe, Subtype.forall, ← mem_xLine_iff k r]
  constructor
  · rintro ⟨n, hn⟩
    have hyₘ : y k ∈ IsLocalRing.maximalIdeal (R k) := by
      rw [hm]
      exact Ideal.subset_span (by simp)
    have hz : y k ^ n * r = 0 := hn _ (Ideal.pow_mem_pow hyₘ n)
    have hp := congrArg (project k) hz
    rw [map_mul, map_pow, hy, map_zero] at hp
    rw [← hker, RingHom.mem_ker]
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
  · intro hr
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hr
    refine ⟨1, ?_⟩
    intro a ha
    rw [pow_one, hm, Ideal.mem_span_pair] at ha
    obtain ⟨s, t, rfl⟩ := ha
    change (s * x k + t * y k) * (x k * b) = 0
    have hxx : x k * x k = 0 := by rwa [pow_two] at hx
    have hyx : y k * x k = 0 := (mul_comm _ _).trans hxy
    simp only [add_mul, ← mul_assoc]
    rw [mul_assoc s (x k) (x k), mul_assoc t (y k) (x k), hxx, hyx]
    simp

private theorem quotientPowerSeries (k : Type u) [Field k] :
    ∃ e : XQuotient k ≃+* A k, ∀ r : R k, e (toXQuotient k r) = project k r := by
  have hker : RingHom.ker (projectS k) = Ideal.span {SX k} := by
    ext s
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, projectS_eq_zero_iff k s]
  have hsurj : Function.Surjective (projectS k) :=
    fun a => ⟨sectionS k a, project_section k a⟩
  let e := (Ideal.quotEquivOfEq hker.symm).trans
    ((projectS k).quotientKerEquivOfSurjective hsurj)
  refine ⟨e, ?_⟩
  intro r
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj s

/-- The four cohomology identifications, with the actions of the example ring. -/
theorem cohomologyCalculation : Cohomology.{u} := by
  intro k _
  obtain ⟨hS, _, _, hd, _⟩ := TwoDegreeExampleDualizingCalculation.completeRegularCover k
  let _ := hS
  obtain ⟨J₀, _, _⟩ := RegularCoverDualizingModel.shiftedRingResolution_exists (S k) 2 hd
  obtain ⟨h₀, h₁⟩ := TwoDegreeExampleCechCalculation.localCohomologyCalculation k
  exact ⟨supportTorsion k, quotientPowerSeries k, h₀, h₁, ⟨J₀⟩,
    TwoDegreeExampleDualizingCalculation.dualizingCohomology k⟩

end CommutativeAlgebraNotes.TwoDegreeDualizingComplexExample
