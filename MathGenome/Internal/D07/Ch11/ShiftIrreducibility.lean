import MathGenome.Internal.Specs.D07.Ch11.ShiftIrreducibility
import MathGenome.Internal.D07.Ch11.Eisenstein
import MathGenome.Internal.D07.Ch11.EvaluationUniversal
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! Affine changes of variable and the shifted Eisenstein quartic example. -/

universe u

namespace D07.Ch11.ShiftIrreducibility

open Polynomial
open Specs.D07.Ch11.ShiftIrreducibility

theorem inverseSubstitutions : InverseSubstitutions.{u} := by
  intro R _ u a f
  have h₁ : (C (u : R) * X + C a).comp
      (C (↑(u⁻¹) : R) * (X - C a)) = X := by
    simp [mul_comp, add_comp, ← mul_assoc, ← C_mul]
  have h₂ : (C (↑(u⁻¹) : R) * (X - C a)).comp
      (C (u : R) * X + C a) = X := by
    simp [mul_comp, sub_comp, ← mul_assoc, ← C_mul]
  exact ⟨by rw [comp_assoc, h₁, comp_X], by rw [comp_assoc, h₂, comp_X]⟩

theorem affineAutomorphism : AffineAutomorphism.{u} := by
  intro R _ u a
  let e : R[X] ≃+* R[X] :=
    { compRingHom (C (u : R) * X + C a) with
      invFun := fun f => f.comp (C (↑(u⁻¹) : R) * (X - C a))
      left_inv := fun f => (inverseSubstitutions R u a f).1
      right_inv := fun f => (inverseSubstitutions R u a f).2 }
  exact ⟨e, (fun _ => rfl), (fun _ => rfl), (fun _ => C_comp), X_comp⟩

theorem unitsAndFactorizations : UnitsAndFactorizations.{u} := by
  intro R _ u a
  obtain ⟨e, he, _, _, _⟩ := affineAutomorphism R u a
  constructor
  · intro f
    rw [← he]
    exact isUnit_map_iff e f
  · intro f g h
    rw [← he, ← he, ← he, ← map_mul]
    exact e.injective.eq_iff.symm

theorem affineIrreducibility : AffineIrreducibility.{u} := by
  intro R _ u a f
  obtain ⟨e, he, _, _, _⟩ := affineAutomorphism R u a
  rw [← he]
  exact MulEquiv.irreducible_iff e

theorem shiftIrreducibility : ShiftPreservesIrreducibility.{u} := by
  intro R _ a f
  simpa using affineIrreducibility R 1 a f

theorem shiftedQuarticExpansion : ShiftedQuarticExpansion.{u} := by
  intro R _
  ring

theorem shiftedQuarticEisenstein : ShiftedQuarticEisenstein := by
  let f : ℤ[X] := (X + 1) ^ 4 + 1
  have hm : f.Monic := by
    simpa [f] using
      (monic_X_pow_add_C (1 : ℤ) (by decide : (4 : ℕ) ≠ 0)).comp_X_add_C 1
  have hd : f.natDegree = 4 := by
    change (((X + C (1 : ℤ)) ^ 4) + 1).natDegree = 4
    rw [natDegree_add_one, natDegree_pow_X_add_C]
  have hc (i : ℕ) (hi : i < f.natDegree) : (2 : ℤ) ∣ f.coeff i := by
    rw [hd] at hi
    dsimp [f]
    rw [shiftedQuarticExpansion ℤ]
    interval_cases i <;>
      norm_num [coeff_add, coeff_mul, coeff_X_pow, coeff_X, Finset.sum_range_succ]
  have h0 : ¬(2 : ℤ) ^ 2 ∣ f.coeff 0 := by
    dsimp [f]
    rw [shiftedQuarticExpansion ℤ]
    norm_num [coeff_add, coeff_mul, coeff_X_pow, coeff_X, Finset.sum_range_succ]
  exact ⟨hm, hd, by rw [hm.leadingCoeff]; norm_num, hc, h0⟩

theorem shiftedQuarticIrreducible : ShiftedQuarticIrreducible := by
  obtain ⟨hm, hd, hl, hc, h0⟩ := shiftedQuarticEisenstein
  obtain ⟨_, hq⟩ := Eisenstein.integerCriterion 2 ((X + 1) ^ 4 + 1)
    (by decide) (Or.inl hm) (by rw [hd]; decide) hl hc h0
  simpa [ShiftedQuarticIrreducible] using hq

theorem quarticIrreducible : QuarticIrreducible := by
  apply (shiftIrreducibility ℚ 1 (X ^ 4 + 1)).mp
  simpa [ShiftedQuarticIrreducible] using shiftedQuarticIrreducible

end D07.Ch11.ShiftIrreducibility
