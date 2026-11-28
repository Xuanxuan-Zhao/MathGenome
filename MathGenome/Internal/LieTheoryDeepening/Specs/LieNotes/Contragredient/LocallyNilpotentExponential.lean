import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Basic.Complex.Basic

open scoped BigOperators

namespace LieNotes.Contragredient.LocallyNilpotentExponential

universe u

section Linear

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Every vector is annihilated by some power of the operator. -/
def LocallyNilpotent (D : Module.End ℂ V) : Prop :=
  ∀ x : V, ∃ n : ℕ, (D ^ n) x = 0

theorem LocallyNilpotent.neg {D : Module.End ℂ V} (hD : LocallyNilpotent D) :
    LocallyNilpotent (-D) := by
  intro x
  obtain ⟨n, hn⟩ := hD x
  exact ⟨n, by rw [neg_pow, Module.End.mul_apply, hn, map_zero]⟩

private noncomputable def partialExp (D : Module.End ℂ V) (n : ℕ) : Module.End ℂ V :=
  ∑ j ∈ Finset.range n, (j.factorial : ℂ)⁻¹ • D ^ j

private theorem partialExp_stable (D : Module.End ℂ V) {x : V} {m n : ℕ}
    (hx : (D ^ m) x = 0) (hmn : m ≤ n) :
    partialExp D n x = partialExp D m x := by
  rw [partialExp, partialExp, ← Finset.sum_range_add_sum_Ico _ hmn, LinearMap.add_apply]
  suffices (∑ j ∈ Finset.Ico m n, (j.factorial : ℂ)⁻¹ • D ^ j) x = 0 by
    rw [this, add_zero]
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  simp [Module.End.pow_map_zero_of_le (Finset.mem_Ico.mp hj).1 hx]

private noncomputable def expValue (D : Module.End ℂ V) (hD : LocallyNilpotent D) (x : V) : V :=
  partialExp D (Classical.choose (hD x)) x

private theorem expValue_eq (D : Module.End ℂ V) (hD : LocallyNilpotent D) {x : V} {n : ℕ}
    (hn : (D ^ n) x = 0) :
    expValue D hD x = partialExp D n x := by
  unfold expValue
  rcases le_total (Classical.choose (hD x)) n with h | h
  · exact (partialExp_stable D (Classical.choose_spec (hD x)) h).symm
  · exact partialExp_stable D hn h

/-- The pointwise finite exponential of a locally nilpotent complex endomorphism. -/
noncomputable def exp (D : Module.End ℂ V) (hD : LocallyNilpotent D) : Module.End ℂ V where
  toFun := expValue D hD
  map_add' x y := by
    obtain ⟨m, hm⟩ := hD x
    obtain ⟨n, hn⟩ := hD y
    have hx := Module.End.pow_map_zero_of_le (le_max_left m n) hm
    have hy := Module.End.pow_map_zero_of_le (le_max_right m n) hn
    have hxy : (D ^ max m n) (x + y) = 0 := by simp [map_add, hx, hy]
    simp only [expValue_eq D hD hxy, expValue_eq D hD hx, expValue_eq D hD hy, map_add]
  map_smul' a x := by
    obtain ⟨n, hn⟩ := hD x
    have hax : (D ^ n) (a • x) = 0 := by simp [hn]
    simp only [expValue_eq D hD hax, expValue_eq D hD hn, map_smul, RingHom.id_apply]

theorem exp_apply_of_pow_eq_zero (D : Module.End ℂ V) (hD : LocallyNilpotent D)
    {x : V} {n : ℕ} (hn : (D ^ n) x = 0) :
    exp D hD x = ∑ j ∈ Finset.range n, (j.factorial : ℂ)⁻¹ • (D ^ j) x := by
  change expValue D hD x = _
  simpa only [partialExp, LinearMap.sum_apply, LinearMap.smul_apply] using expValue_eq D hD hn

end Linear
end LieNotes.Contragredient.LocallyNilpotentExponential

namespace Specs.LieNotes.Contragredient.LocallyNilpotentExponential

open _root_.LieNotes.Contragredient.LocallyNilpotentExponential

universe u v

def expApplyExpected : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V]
    (D : Module.End ℂ V) (hD : LocallyNilpotent D) {x : V} {n : ℕ},
    (D ^ n) x = 0 →
      exp D hD x = ∑ j ∈ Finset.range n, (j.factorial : ℂ)⁻¹ • (D ^ j) x

def inverseExpected : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℂ V]
    (D : Module.End ℂ V) (hD : LocallyNilpotent D),
    exp (-D) hD.neg * exp D hD = 1 ∧ exp D hD * exp (-D) hD.neg = 1

def mapLieExpected : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (D : LieDerivation ℂ L L) (hD : LocallyNilpotent D.toLinearMap) (x y : L),
    exp D.toLinearMap hD ⁅x, y⁆ = ⁅exp D.toLinearMap hD x, exp D.toLinearMap hD y⁆

attribute [local instance 100] LieRing.ofAssociativeRing

def conjugationExpected : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (x : L)
    (had : LocallyNilpotent (LieAlgebra.ad ℂ L x))
    (hρ : LocallyNilpotent (ρ x)) (y : L),
    exp (ρ x) hρ * ρ y * exp (-(ρ x)) hρ.neg = ρ (exp (LieAlgebra.ad ℂ L x) had y)

end Specs.LieNotes.Contragredient.LocallyNilpotentExponential
