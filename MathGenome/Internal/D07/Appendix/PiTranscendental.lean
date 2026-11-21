import MathGenome.Internal.Specs.D07.Appendix.PiTranscendental
import MathGenome.Internal.D07.Appendix.LindemannRelation
import MathGenome.Internal.D07.Appendix.PiTranscendentalSubsetSumRelation
import Mathlib.RingTheory.Algebraic.Integral

/-!
The final contradiction in the special Lindemann proof, paper.tex:7784–7820.
The upstream subset-sum construction retains repeated sums and descends the
whole root product to Q. Its vanishing exponential relation contradicts the
upstream special Lindemann theorem. Applying this to i*pi uses only Euler's
identity and closure of algebraic elements under multiplication. Finally,
algebraicity of the nonnegative square root would imply algebraicity of pi.
-/

namespace D07.Appendix.PiTranscendental

open Polynomial
open Specs.D07.Appendix.PiTranscendental
open Specs.D07.Appendix.PiTranscendentalSubsetSumRelation

/-- The two upstream results exclude Euler's value for any nonzero algebraic
argument; the list conversion preserves all subset-sum multiplicities. -/
theorem exp_ne_neg_one_of_algebraic {α : ℂ} (hn : α ≠ 0)
    (ha : IsAlgebraic ℚ α) : Complex.exp α ≠ -1 := by
  classical
  intro he
  obtain ⟨_, _, _, hk, _, hβ, _, hrel, P, hP⟩ :=
    PiTranscendentalSubsetSumRelation.subset_sum_relation α hn ha he
  have hlist : ∀ b ∈ (nonzeroSums (conjugates α)).toList, b ≠ 0 := by
    simpa only [Multiset.mem_toList] using hβ
  have hprod : P.map (algebraMap ℚ ℂ) =
      (((nonzeroSums (conjugates α)).toList).map (fun b => X - C b)).prod := by
    simpa only [Multiset.prod_map_toList, rootProduct] using hP
  have hne := LindemannRelation.special_relation
    (nonzeroSums (conjugates α)).toList P hlist hprod
    (zeroCount (conjugates α)) hk
  apply hne
  simpa only [Multiset.sum_map_toList] using hrel

theorem pi_transcendental : PiIsTranscendental := by
  intro hπ
  have hi : IsAlgebraic ℚ Complex.I := by
    apply IsAlgebraic.of_pow (n := 2) zero_lt_two
    simpa only [Complex.I_sq, Int.cast_neg, Int.cast_one] using
      (isAlgebraic_intCast (R := ℚ) (A := ℂ) (-1))
  have hπc : IsAlgebraic ℚ (Real.pi : ℂ) :=
    hπ.algHom (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  have ha : IsAlgebraic ℚ (Complex.I * (Real.pi : ℂ)) :=
    (hi.isIntegral.mul hπc.isIntegral).isAlgebraic
  have hn : Complex.I * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  apply exp_ne_neg_one_of_algebraic hn ha
  simpa only [mul_comm Complex.I] using Complex.exp_pi_mul_I

theorem sqrt_pi_transcendental : SqrtPiTranscendental := by
  intro hs
  apply pi_transcendental
  have hsq : IsAlgebraic ℚ ((Real.sqrt Real.pi) ^ 2) :=
    (hs.isIntegral.pow 2).isAlgebraic
  simpa only [Real.sq_sqrt Real.pi_pos.le] using hsq

end D07.Appendix.PiTranscendental
