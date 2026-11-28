import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.RootVectorReduction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.CoxeterDynamics
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.LinearCombination

/-! Reduction of a nonnegative integral Tits root along the cyclic sink schedule. -/

open scoped BigOperators Matrix

universe u v

namespace RepTheorySurvey.Quiver.RootVectorReduction

open Forms SimpleReflections SinkCycle CoxeterDynamics

open private titsForm_smul_vertexUnit from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.SimpleReflections
open private coxeterPrefix_preservesTitsForm coxeter_pow_preservesTitsForm
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.CoxeterDynamics

noncomputable abbrev vectorAtStep := @RootVectorReductionSpec.vectorAtStep

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q]

@[simp]
theorem vectorAtStep_zero (number : Q ≃ Fin (Fintype.card Q)) (d : DimensionVector Q) :
    vectorAtStep number 0 d = d := by
  simp only [vectorAtStep, RootVectorReductionSpec.vectorAtStep, Nat.zero_mod, Nat.zero_div,
    pow_zero, LinearEquiv.coe_one, id_eq]
  rfl

theorem vectorAtStep_mul_card (number : Q ≃ Fin (Fintype.card Q))
    (hcard : 0 < Fintype.card Q) (k : ℕ) (d : DimensionVector Q) :
    vectorAtStep number (Fintype.card Q * k) d = ((coxeter number ℤ) ^ k) d := by
  simp only [vectorAtStep, RootVectorReductionSpec.vectorAtStep, Nat.mul_mod_right,
    Nat.mul_div_cancel_left k hcard]
  rfl

theorem vectorAtStep_succ : RootVectorReductionSpec.VectorAtStepSucc.{u, v} := by
  intro Q _ _ number m i hi d
  have hcard : 0 < Fintype.card Q := Nat.zero_lt_of_lt i.isLt
  have hdecomp :
      m + 1 = Fintype.card Q * (m / Fintype.card Q) + (i.val + 1) := by
    rw [hi, ← Nat.add_assoc, Nat.div_add_mod]
  have hmod : (m + 1) % Fintype.card Q = (i.val + 1) % Fintype.card Q := by
    rw [hdecomp, Nat.mul_add_mod]
  have hdiv : (m + 1) / Fintype.card Q = m / Fintype.card Q + (i.val + 1) / Fintype.card Q := by
    rw [hdecomp, Nat.mul_add_div hcard]
  simp only [RootVectorReductionSpec.vectorAtStep]
  rw [hmod, hdiv, ← hi, ← coxeterPrefix_step number ℤ i]
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, Nat.add_zero]
  · rw [show i.val + 1 = Fintype.card Q from heq, Nat.mod_self, Nat.div_self hcard,
      pow_succ', LinearEquiv.mul_apply]
    rfl

variable [Fintype (RM03.Arrow Q)]

private theorem integralTitsForm_pos (hpos : PositiveDefinite Q)
    {d : DimensionVector Q} (hd : d ≠ 0) : 0 < titsForm d := by
  have hcast : (fun j => (d j : ℝ)) ≠ 0 := by
    intro hz
    apply hd
    funext j
    have hj : (d j : ℝ) = 0 := congrFun hz j
    exact_mod_cast hj
  have h := hpos _ hcast
  rw [real_titsForm_intCast] at h
  exact_mod_cast h

private theorem unitVector_of_negative_reflection
    (hacyc : ¬ RM03.HasOrientedCycle Q) (hpos : PositiveDefinite Q)
    (i : Q) (d : DimensionVector Q) (hd : ∀ j, 0 ≤ d j) (hq : titsForm d = 1)
    (hneg : simpleReflection ℤ i d i < 0) :
    d = unitVector i := by
  classical
  -- Subtracting the contribution at `i` sets that coordinate to zero.
  let z := (-d i) • vertexUnit ℤ i + d
  have hsplit : titsForm d = titsForm z + d i * (-simpleReflection ℤ i d i) := by
    have hpolar := titsForm_polarization hacyc ((-d i) • vertexUnit ℤ i) d
    rw [titsForm_smul_vertexUnit hacyc, smul_dotProduct, smul_eq_mul] at hpolar
    change titsForm z - (-d i) ^ 2 - titsForm d =
      (-d i) * (vertexUnit ℤ i ⬝ᵥ (polarizationMatrix ℤ *ᵥ d)) at hpolar
    have hreflect :
        simpleReflection ℤ i d i = d i - vertexUnit ℤ i ⬝ᵥ (polarizationMatrix ℤ *ᵥ d) := by
      simp [simpleReflection_apply, vertexUnit, SimpleReflectionsSpec.vertexUnit]
    rw [hreflect]
    linear_combination -hpolar
  have hsum : 0 ≤ ∑ j, (edgeMultiplicity i j : ℤ) * d j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Int.natCast_nonneg _) (hd j)
  have hdi : 1 ≤ d i := by
    have h := hneg
    rw [simpleReflection_apply_self hacyc] at h
    omega
  have hprod : d i ≤ d i * (-simpleReflection ℤ i d i) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show 1 ≤ -simpleReflection ℤ i d i by omega) (hd i)
  have hz : z = 0 := by
    by_contra hz
    have hzpos := integralTitsForm_pos hpos hz
    omega
  have hqz : titsForm z = 0 := by
    rw [hz]
    simp [titsForm, FormsSpec.titsForm, FormsSpec.eulerForm]
  have hone : d i = 1 := by omega
  funext j
  by_cases hj : j = i
  · subst j
    simpa [unitVector, FormsSpec.unitVector] using hone
  · have hzero := congrFun hz j
    simpa [z, vertexUnit, SimpleReflectionsSpec.vertexUnit, hj, unitVector,
      FormsSpec.unitVector] using hzero

theorem firstNegativeStep : RootVectorReductionSpec.FirstNegativeStep.{u, v} := by
  classical
  intro Q _ _ _ hacyc hpos number hnumber d hd hq
  have hdne : d ≠ 0 := by
    intro hz
    simp [hz, FormsSpec.titsForm, FormsSpec.eulerForm] at hq
  obtain ⟨pass, j, hj⟩ :=
    coxeter_negativeCoordinateIntegral hacyc hpos number hnumber d hdne hd
  have hcard : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨j⟩
  have hex : ∃ n : ℕ, ∃ j : Q, vectorAtStep number n d j < 0 := by
    refine ⟨Fintype.card Q * pass, j, ?_⟩
    rwa [vectorAtStep_mul_card number hcard]
  have hfirst := Nat.find_spec hex
  have hn : Nat.find hex ≠ 0 := by
    intro hz
    obtain ⟨j, hj⟩ := hfirst
    rw [hz, vectorAtStep_zero] at hj
    exact (not_lt_of_ge (hd j)) hj
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hbefore (k : ℕ) (hk : k ≤ m) (j : Q) : 0 ≤ vectorAtStep number k d j := by
    exact le_of_not_gt fun h => Nat.find_min hex (hm ▸ Nat.lt_succ_of_le hk) ⟨j, h⟩
  let i : Fin (Fintype.card Q) := ⟨m % Fintype.card Q, Nat.mod_lt m hcard⟩
  have hstep (l : Q) : vectorAtStep number (m + 1) d l =
      simpleReflection ℤ (number.symm i) (vectorAtStep number m d) l :=
    congrFun (vectorAtStep_succ number m i rfl d) l
  have hneg : vectorAtStep number (m + 1) d (number.symm i) < 0 := by
    obtain ⟨l, hl⟩ := hfirst
    rw [hm] at hl
    change vectorAtStep number (m + 1) d l < 0 at hl
    by_cases hli : l = number.symm i
    · exact hli ▸ hl
    · rw [hstep l, simpleReflection_apply_ne hli] at hl
      exact ((not_lt_of_ge (hbefore m le_rfl l)) hl).elim
  have hlevel : titsForm (vectorAtStep number m d) = 1 := by
    simp only [vectorAtStep, RootVectorReductionSpec.vectorAtStep,
      coxeterPrefix_preservesTitsForm hacyc, coxeter_pow_preservesTitsForm hacyc]
    exact hq
  refine ⟨m, i, rfl, hbefore, ?_, hneg⟩
  rw [hstep (number.symm i)] at hneg
  exact unitVector_of_negative_reflection hacyc hpos _ _ (hbefore m le_rfl) hlevel hneg

end RepTheorySurvey.Quiver.RootVectorReduction
