import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Profinite.Topology
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! The additive rationals have trivial profinite completion. -/

namespace ALG02GroupTheory.Profinite

universe u

/-- Every homomorphism from the additive rationals to a finite group is trivial. -/
theorem rational_finiteHom_apply {H : Type u} [Group H] [Finite H]
    (f : Multiplicative ℚ →* H) (x : ℚ) : f (Multiplicative.ofAdd x) = 1 := by
  have hcard : (Nat.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  have hdiv : Nat.card H • (x / (Nat.card H : ℚ)) = x := by
    rw [nsmul_eq_mul, mul_div_cancel₀ x hcard]
  calc
    f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd (x / (Nat.card H : ℚ)) ^
        Nat.card H) := by rw [← ofAdd_nsmul, hdiv]
    _ = f (Multiplicative.ofAdd (x / (Nat.card H : ℚ))) ^ Nat.card H := map_pow _ _ _
    _ = 1 := pow_card_eq_one'

theorem rational_finiteQuotient_subsingleton
    (N : FiniteIndexNormalSubgroup (Multiplicative ℚ)) :
    Subsingleton (Multiplicative ℚ ⧸ N.toSubgroup) := by
  have eq_one (q : Multiplicative ℚ ⧸ N.toSubgroup) : q = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N.toSubgroup q
    exact rational_finiteHom_apply (QuotientGroup.mk' N.toSubgroup) x.toAdd
  exact ⟨fun q r => (eq_one q).trans (eq_one r).symm⟩

theorem rational_completion_subsingleton : Subsingleton (Completion (Multiplicative ℚ)) := by
  constructor
  intro a b
  apply (toCompatibleTuples (Multiplicative ℚ)).injective
  apply Subtype.ext
  funext N
  exact (rational_finiteQuotient_subsingleton N).elim _ _

theorem rational_denseRange_eta :
    DenseRange (eta (Multiplicative ℚ) : Multiplicative ℚ → Completion (Multiplicative ℚ)) :=
  denseRange_eta (Multiplicative ℚ)

end ALG02GroupTheory.Profinite
