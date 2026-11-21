import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Bolzano
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Subsequence
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-!
# Bolzano–Weierstrass for the canonical scalar fields

For the real case, enclose all terms in the compact interval `[-M,M]` and
use Mathlib's sequential compactness theorem. This replaces the manuscript's
bisection proof with the library's order-compactness proof; the upstream
epsilon/filter equivalence converts its conclusion to the manuscript's limit.

For the complex case, follow the manuscript: extract convergent real parts,
then convergent imaginary parts, preserve the first limit along the second
selection, and bound the complex error by the sum of the coordinate errors.
No complex completeness theorem is used in this argument.
-/

namespace SingleVariableAnalysis

theorem real_bolzano_weierstrass (a : ℕ → ℝ)
    (hbounded : ∃ M : ℝ, ∀ n, |a n| ≤ M) :
    ∃ L : ℝ, RealSubsequentialLimit a L := by
  obtain ⟨M, hM⟩ := hbounded
  have hin : ∀ n, a n ∈ Set.Icc (-M) M := fun n => abs_le.mp (hM n)
  obtain ⟨L, _, φ, hφ, hlimit⟩ := isCompact_Icc.tendsto_subseq hin
  exact ⟨L, φ, hφ, (realSequenceConverges_iff _ _).mpr hlimit⟩

theorem complex_bolzano_weierstrass (a : ℕ → ℂ)
    (hbounded : ∃ M : ℝ, ∀ n, ‖a n‖ ≤ M) :
    ∃ L : ℂ, ComplexSubsequentialLimit a L := by
  obtain ⟨M, hM⟩ := hbounded
  obtain ⟨u, φ, hφ, hu⟩ := real_bolzano_weierstrass (fun n => (a n).re)
    ⟨M, fun n => (Complex.abs_re_le_norm (a n)).trans (hM n)⟩
  obtain ⟨v, ψ, hψ, hv⟩ := real_bolzano_weierstrass (fun n => (a (φ n)).im)
    ⟨M, fun n => (Complex.abs_im_le_norm (a (φ n))).trans (hM (φ n))⟩
  have hu' := realSequenceConverges_comp ((fun n => (a n).re) ∘ φ) u ψ hψ hu
  refine ⟨⟨u, v⟩, φ ∘ ψ, hφ.comp hψ, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hu' (ε / 2) (half_pos hε)
  obtain ⟨P, hP⟩ := hv (ε / 2) (half_pos hε)
  refine ⟨max N P, ?_⟩
  intro n hn
  have hre := hN n ((le_max_left N P).trans hn)
  have him := hP n ((le_max_right N P).trans hn)
  have hnorm := Complex.norm_le_abs_re_add_abs_im (a (φ (ψ n)) - ⟨u, v⟩)
  change |(a (φ (ψ n))).re - u| < ε / 2 at hre
  change |(a (φ (ψ n))).im - v| < ε / 2 at him
  change ‖a (φ (ψ n)) - ⟨u, v⟩‖ < ε
  change ‖a (φ (ψ n)) - ⟨u, v⟩‖ ≤
    |(a (φ (ψ n))).re - u| + |(a (φ (ψ n))).im - v| at hnorm
  linarith

end SingleVariableAnalysis
