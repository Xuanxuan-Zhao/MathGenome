import MathGenome.Internal.Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity
import Mathlib.Algebra.Group.Units.Equiv

/-!
Class-function Frobenius reciprocity by finite reindexing. The independent
Specs supply the shared functions and their precise normalization. No results
about characters or Hom spaces enter the proof.
-/

noncomputable section
open scoped BigOperators Classical ComplexConjugate

namespace D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity

universe u

open Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity (extendZero)

abbrev IsClassFunction (G : Type u) [Group G] (f : G → ℂ) : Prop :=
  Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.IsClassFunction f

abbrev restrict (G : Type u) [Group G] (H : Subgroup G) (k : G → ℂ) : H → ℂ :=
  Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.restrict H k

abbrev pairing (G : Type u) [Fintype G] (f k : G → ℂ) : ℂ :=
  Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.pairing f k

abbrev induce (G : Type u) [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.induce H f

variable {G : Type u} [Group G]

theorem restriction_isClassFunction (G : Type u) [Group G] (H : Subgroup G)
    (k : G → ℂ) (hk : IsClassFunction G k) : IsClassFunction H (restrict G H k) := by
  intro a g
  exact hk a g

variable [Fintype G]

/-- Reindexing a finite group sum by conjugation. -/
lemma sum_conjugation (x : G) (F : G → ℂ) :
    (∑ g : G, F (x * g * x⁻¹)) = ∑ g : G, F g := by
  apply Fintype.sum_bijective (fun g : G => x * g * x⁻¹)
  · constructor
    · intro a b h
      exact mul_left_cancel (mul_right_cancel h)
    · intro g
      exact ⟨x⁻¹ * g * x, by simp [mul_assoc]⟩
  · intro g
    rfl

/-- Summing a zero extension is the same as summing over the subgroup. -/
lemma sum_extendZero (H : Subgroup G) (f : H → ℂ) :
    (∑ g : G, extendZero H f g) = ∑ h : H, f h := by
  symm
  apply Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.coe_injective
  · intro g hg
    have hnot : g ∉ H := by
      intro h
      exact hg ⟨⟨g, h⟩, rfl⟩
    simp [extendZero, hnot]
  · intro h
    simp [extendZero]

/-- Invariance follows by `x = a * y` and in fact does not need invariance of f. -/
lemma induce_conjugation (H : Subgroup G) (f : H → ℂ) (a g : G) :
    induce G H f (a * g * a⁻¹) = induce G H f g := by
  unfold induce Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.induce
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft a)
    (fun x : G => extendZero H f (x⁻¹ * (a * g * a⁻¹) * x))]
  apply Finset.sum_congr rfl
  intro x _
  simp [mul_inv_rev, mul_assoc]

theorem induction_isClassFunction (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (f : H → ℂ) (_hf : IsClassFunction H f) :
    IsClassFunction G (induce G H f) :=
  induce_conjugation H f

/-- The inner sum after interchanging the finite sums. -/
lemma sum_induction_integrand (H : Subgroup G) (f : H → ℂ) (k : G → ℂ)
    (hk : IsClassFunction G k) (x : G) :
    (∑ g : G, extendZero H f (x⁻¹ * g * x) * conj (k g)) =
      ∑ h : H, f h * conj (k h) := by
  calc
    _ = ∑ g : G, extendZero H f (x⁻¹ * g * x) * conj (k (x⁻¹ * g * x)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [show k (x⁻¹ * g * x) = k g by simpa using hk x⁻¹ g]
    _ = ∑ g : G, extendZero H f g * conj (k g) := by
      simpa using sum_conjugation x⁻¹ (fun g => extendZero H f g * conj (k g))
    _ = ∑ g : G, extendZero H (fun h => f h * conj (k h)) g := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : g ∈ H <;> simp [extendZero, hg]
    _ = _ := sum_extendZero H _

theorem reciprocity (G : Type u) [Group G] [Fintype G] (H : Subgroup G)
    (f : H → ℂ) (k : G → ℂ) (_hf : IsClassFunction H f) (hk : IsClassFunction G k) :
    pairing G (induce G H f) k = pairing H f (restrict G H k) := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold pairing induce restrict
    Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.pairing
    Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.induce
    Specs.D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity.restrict
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← mul_assoc, sum_induction_integrand H f k hk]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = ((Fintype.card G : ℂ)⁻¹ * Fintype.card G) *
        ((Fintype.card H : ℂ)⁻¹ * ∑ h : H, f h * conj (k h)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hG, one_mul]

end D07.Ch21.FrobeniusReciprocityClassFunctionReciprocity
