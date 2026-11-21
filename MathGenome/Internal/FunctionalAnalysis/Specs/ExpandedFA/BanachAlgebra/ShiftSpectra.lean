import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Independent statements for the sequence part of `fa2:p2:shifts`,
paper.tex 10006–10032. Native coordinate n is manuscript coordinate n+1.
The extended exponent p is finite and at least one, so this includes every
real exponent in [1,∞), including p=1, and does not include ℓ∞.
The operators are literal insertion/deletion of the first coordinate on the
accepted canonical scalar ℓᵖ space, with its existing norm and topology. -/
noncomputable section
open scoped ENNReal
namespace ExpandedFA.BanachAlgebra.ShiftSpectra
open ExpandedFA.P1.C01SequenceSpaces

abbrev Space (p : ℝ≥0∞) := SequenceLp ℂ p

instance (p : ℝ≥0∞) : Nontrivial (Space p) := by
  refine ⟨⟨lp.single p 0 (1 : ℂ), 0, ?_⟩⟩
  intro h
  have hh := congrArg (fun x : Space p => x 0) h
  simp at hh

def shiftSequence (x : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => x n

theorem exponent_pos (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp

private theorem forward_mem (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : Space p) :
    Memℓp (shiftSequence x) p := by
  apply memℓp_gen
  apply (summable_nat_add_iff 1).mp
  simpa only [shiftSequence] using (lp.memℓp x).summable (exponent_pos p hp)

private def forwardLinear (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Space p →ₗ[ℂ] Space p where
  toFun x := ⟨shiftSequence x, forward_mem p hp x⟩
  map_add' x y := by
    apply lp.ext; funext n
    change shiftSequence (⇑(x + y)) n = shiftSequence x n + shiftSequence y n
    cases n <;> simp [shiftSequence]
  map_smul' a x := by
    apply lp.ext; funext n
    cases n <;> simp [shiftSequence]

private theorem forward_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : Space p) :
    ‖forwardLinear p hp x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (exponent_pos p hp), lp.norm_eq_tsum_rpow (exponent_pos p hp)]
  congr 1
  change (∑' n, ‖shiftSequence x n‖ ^ p.toReal) = _
  rw [((forward_mem p hp x).summable (exponent_pos p hp)).tsum_eq_zero_add]
  simp [shiftSequence, Real.zero_rpow (exponent_pos p hp).ne']

def forwardIsometry (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Space p →ₗᵢ[ℂ] Space p :=
  ⟨forwardLinear p hp, forward_norm p hp⟩

private def backwardLinear (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Space p →ₗ[ℂ] Space p where
  toFun x := ⟨fun n => x (n + 1), memℓp_gen <|
    (summable_nat_add_iff 1).mpr ((lp.memℓp x).summable (exponent_pos p hp))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem backward_norm_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : Space p) :
    ‖backwardLinear p hp x‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_tsum_le (exponent_pos p hp) (norm_nonneg x)
  rw [lp.norm_rpow_eq_tsum (exponent_pos p hp)]
  change (∑' n, ‖x (n + 1)‖ ^ p.toReal) ≤ _
  rw [((lp.memℓp x).summable (exponent_pos p hp)).tsum_eq_zero_add]
  exact le_add_of_nonneg_left (by positivity)

namespace Spec

def ShiftType := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → Space p →L[ℂ] Space p

def ForwardValue : ShiftType := fun p _ hp => (forwardIsometry p hp).toContinuousLinearMap

def BackwardValue : ShiftType := fun p _ hp =>
  (backwardLinear p hp).mkContinuous 1 (by
    intro x; simpa using backward_norm_le p hp x)

def Coordinates : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : Space p),
  ForwardValue p hp x 0 = 0 ∧
    (∀ n, ForwardValue p hp x (n + 1) = x n) ∧
    (∀ n, BackwardValue p hp x n = x (n + 1))

def Norms : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
  ‖ForwardValue p hp‖ = 1 ∧ ‖BackwardValue p hp‖ = 1

def ForwardSpectrum : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
  Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue
    ℂ (Space p →L[ℂ] Space p) (ForwardValue p hp) = {z : ℂ | ‖z‖ ≤ 1}

def ForwardPointSpectrum : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
  Specs.ExpandedFA.BanachAlgebra.Conventions.PointSpectrumValue
    ℂ (Space p) (ForwardValue p hp) = ∅

def ForwardApproximateSpectrum : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
  Specs.ExpandedFA.BanachAlgebra.Conventions.ApproximatePointSpectrumValue
    ℂ (Space p) (ForwardValue p hp) = {z : ℂ | ‖z‖ = 1}

def BackwardSpectrum : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
  Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue
    ℂ (Space p →L[ℂ] Space p) (BackwardValue p hp) = {z : ℂ | ‖z‖ ≤ 1}

def BackwardPointSpectrum : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
  Specs.ExpandedFA.BanachAlgebra.Conventions.PointSpectrumValue
    ℂ (Space p) (BackwardValue p hp) = {z : ℂ | ‖z‖ < 1}

/-- The endpoint claim for the backward shift, with genuine unit vectors. -/
def BackwardEndpoints : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (z : ℂ), ‖z‖ = 1 → ∀ ε : ℝ, 0 < ε →
    ∃ x : Space p, ‖x‖ = 1 ∧ ‖BackwardValue p hp x - z • x‖ < ε

end Spec
end ExpandedFA.BanachAlgebra.ShiftSpectra
