import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.RationalArtinSchreier
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.ArtinSchreierConnecting
import Mathlib.FieldTheory.RatFunc.Degree

namespace GaloisFormalization.GH.RationalArtinSchreier

open Specs.GaloisFormalization.GH.RationalArtinSchreier
open Specs.GaloisFormalization.GH.ArtinSchreierCoefficients (quotientMap wp)

universe u v

attribute [local instance] ZMod.algebra

private theorem intDegree_pow {K : Type u} [Field K] {x : RatFunc K} (hx : x ≠ 0)
    (n : ℕ) : (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih,
      Nat.cast_succ, add_one_mul]

private theorem pow_sub_ne_X {K : Type u} [Field K] {p : ℕ} (hp : 2 ≤ p)
    (x : RatFunc K) : x ^ p - x ≠ RatFunc.X := by
  intro heq
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
  by_cases hx : x = 0
  · have hp0 : p ≠ 0 := by omega
    simp [hx, hp0, hX.symm] at heq
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hsum : x ^ p + -x = RatFunc.X := by simpa only [sub_eq_add_neg] using heq
  have hsum_ne : x ^ p + -x ≠ 0 := hsum.trans_ne hX
  have hforward := RatFunc.intDegree_add_le (neg_ne_zero.mpr hx) hsum_ne
  rw [hsum, RatFunc.intDegree_X, RatFunc.intDegree_neg, intDegree_pow hx] at hforward
  -- A sum of terms of nonpositive degree cannot have degree one.
  have hd : 1 ≤ x.intDegree := by
    by_contra! hd
    have hx_nonpos : x.intDegree ≤ 0 := by omega
    have hpow_nonpos := mul_nonpos_of_nonneg_of_nonpos hp0 hx_nonpos
    have hmax := max_le hpow_nonpos hx_nonpos
    omega

  have hreverse_eq : RatFunc.X + x = x ^ p := (sub_eq_iff_eq_add.mp heq).symm
  have hreverse_ne : RatFunc.X + x ≠ 0 := hreverse_eq.trans_ne (pow_ne_zero p hx)
  have hreverse := RatFunc.intDegree_add_le hx hreverse_ne
  rw [hreverse_eq, RatFunc.intDegree_X, intDegree_pow hx, max_eq_right hd] at hreverse
  -- The reverse sum gives degree at most that of x, but the power has larger degree.
  have hmul := mul_le_mul_of_nonneg_right hp2 (show 0 ≤ x.intDegree by omega)
  omega

/-- The Artin–Schreier quotient class of the rational-function indeterminate is nonzero. -/
theorem variableClassNonzero : VariableClassNonzero.{u} := by
  intro p k₀ _ _ _ _ h
  change (LinearMap.range (wp p (RatFunc k₀))).mkQ RatFunc.X = 0 at h
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at h
  obtain ⟨x, hx⟩ := h
  exact pow_sub_ne_X (Fact.out : p.Prime).two_le x hx

/-- The connecting isomorphism sends the indeterminate to a nonzero cohomology class. -/
theorem variableCohomologyClassNonzero : VariableCohomologyClassNonzero.{u,v} := by
  intro p k₀ S _ _ _ _ _ _ _
  dsimp only
  obtain ⟨connect, toCharacter, hCharacter, hRoot⟩ :=
    ArtinSchreierConnecting.artinSchreierConnecting p (RatFunc k₀) S
  refine ⟨connect, toCharacter, hCharacter, hRoot, ?_⟩
  intro h
  apply variableClassNonzero p k₀
  apply connect.injective
  exact h.trans connect.map_zero.symm

end GaloisFormalization.GH.RationalArtinSchreier
