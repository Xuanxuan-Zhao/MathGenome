import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedLie
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.JacobsonPolynomials
import Batteries.Tactic.OpenPrivate

/-! Restricted powers on ordinary Lie algebras over fields of positive characteristic. -/

namespace LieNotes.SuperRestricted.RestrictedLie

open _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
open _root_.LieNotes.SuperRestricted.JacobsonPolynomials (jacobsonTerm sum_jacobsonTerm)

universe u v w

/-- The additional data of a restricted Lie algebra over `k` of characteristic `p`. -/
abbrev RestrictedPower := restrictedPowerValue.{u, v}

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
  {G : Type v} [LieRing G] [LieAlgebra k G]

/-- In the addition axiom the canonical correction is the sum of the `s_i(x,y)`. -/
theorem isRestrictedPower_iff (power : G → G) :
    isRestrictedPowerValue k p power ↔
      (∀ x, LieAlgebra.ad k G (power x) = LieAlgebra.ad k G x ^ p) ∧
      (∀ (a : k) x, power (a • x) = a ^ p • power x) ∧
      (∀ x y, power (x + y) = power x + power y +
        ∑ i ∈ Finset.Ico 1 p, jacobsonTerm k p i x y) := by
  simp only [sum_jacobsonTerm, isRestrictedPowerValue]

section Naturality

variable {H : Type w} [LieRing H] [LieAlgebra k H]

private theorem map_ad_pow_apply (f : G →ₗ⁅k⁆ H) (x y : G) (n : ℕ) :
    f ((LieAlgebra.ad k G x ^ n) y) = (LieAlgebra.ad k H (f x) ^ n) (f y) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieHom.map_lie, ih]

open private map_jacobsonCoeff from MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.JacobsonPolynomials in
private theorem map_jacobsonCorrection (f : G →ₗ⁅k⁆ H) (n : ℕ) (x y : G) :
    f (jacobsonCorrectionValue k n x y) = jacobsonCorrectionValue k n (f x) (f y) := by
  simp only [jacobsonCorrectionValue, map_sum, map_smul, map_jacobsonCoeff]

end Naturality

/-- A Lie subalgebra closed under the ambient restricted power carries its restriction. -/
def restrict (power : RestrictedPower k p G) (S : LieSubalgebra k G)
    (closed : ∀ x : S, power.val (x : G) ∈ S) : RestrictedPower k p S := by
  let op (x : S) : S := ⟨power.val (x : G), closed x⟩
  refine ⟨op, ?_⟩
  rcases power.property with ⟨hAd, hSmul, hAdd⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change S.incl (LieAlgebra.ad k S (op x) y) = S.incl ((LieAlgebra.ad k S x ^ p) y)
    rw [map_ad_pow_apply]
    exact DFunLike.congr_fun (hAd (x : G)) (y : G)
  · intro a x
    apply Subtype.ext
    exact hSmul a (x : G)
  · intro x y
    apply Subtype.ext
    change S.incl (op (x + y)) = S.incl (op x + op y + jacobsonCorrectionValue k p x y)
    rw [map_add, map_add, map_jacobsonCorrection]
    exact hAdd (x : G) (y : G)

@[simp]
theorem coe_restrict_apply (power : RestrictedPower k p G) (S : LieSubalgebra k G)
    (closed : ∀ x : S, power.val (x : G) ∈ S) (x : S) :
    ((restrict power S closed).val x : G) = power.val (x : G) :=
  rfl

theorem subalgebra_inherits :
    Specs.LieNotes.SuperRestricted.RestrictedLie.subalgebra_inheritsType.{u, v} := by
  intro k _ p _ _ G _ _ power S closed
  exact ⟨restrict power S closed, coe_restrict_apply power S closed⟩

end LieNotes.SuperRestricted.RestrictedLie
