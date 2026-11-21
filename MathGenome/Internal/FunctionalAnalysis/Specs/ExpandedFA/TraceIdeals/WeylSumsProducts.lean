import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.WeylProducts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Sum and shifted-product stage of `fa2:p2:weyl-inequalities`.
The manuscript's nonzero eigenvalues are counted with algebraic multiplicity.
Every finite prefix of an ordered full list, padded by zeros in the finite case,
satisfies the selection condition below. We prove the stronger statement for
any ordered selection; exhaustion of the nonzero spectrum is not needed.
There is no normality, separability, positive-rank or nonzero-space assumption.
-/
noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.WeylSumsProducts.Spec
open Filter
open scoped BigOperators ENNReal

/-- A reusable finite logarithmic-majorization bridge. `g 0 = 0` treats
logarithms of padded zeros by their value at minus infinity. Smoothness is only
required at positive arguments after logarithmic change of variables; this
covers powers (in particular the square) and `log (1 + r * x)` for `r ≥ 0`.
The right-hand list need not even be ordered. -/
def LogMajorizationBridge : Prop :=
  ∀ (n : ℕ) (x y : ℕ → ℝ),
    (∀ i < n, 0 ≤ x i) → (∀ i < n, 0 ≤ y i) →
    AntitoneOn x (Set.Iio n) →
    (∀ k ≤ n, (∏ i ∈ Finset.range k, x i) ≤ ∏ i ∈ Finset.range k, y i) →
    ∀ g : ℝ → ℝ, g 0 = 0 → (∀ t, 0 ≤ t → 0 ≤ g t) →
    Differentiable ℝ (fun t => g (Real.exp t)) →
    Monotone (fun t => g (Real.exp t)) →
    ConvexOn ℝ Set.univ (fun t => g (Real.exp t)) →
    (∑ i ∈ Finset.range n, g (x i)) ≤ ∑ i ∈ Finset.range n, g (y i)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Prefix admissibility uses the upstream actual generalized eigenspaces,
including their full algebraic multiplicities. This is a selection condition,
so the estimates also apply when some eigenvalues are omitted. -/
def AdmissibleEigenvalueSequence (T : H →L[ℂ] H) (ev : ℕ → ℂ) : Prop :=
  Antitone (fun j => ‖ev j‖) ∧
  ∀ n, WeylProducts.Spec.PaddedEigenvalueSelection T (fun i : Fin n => ev i.val)

variable [CompleteSpace H]

def WeylPowerSums : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℂ, AdmissibleEigenvalueSequence T ev →
    ∀ p : ℕ, 0 < p → ∀ n : ℕ,
      (∑ j ∈ Finset.range n, ‖ev j‖ ^ p) ≤
      ∑ j ∈ Finset.range n, (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p

/-- The extended nonnegative sums express the inequality even when the right
sum diverges. For `p = 1` this is the manuscript sum bound; `p = 2` is the
squared-eigenvalue bound used for Hilbert--Schmidt determinants. -/
def WeylExtendedSums : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℂ, AdmissibleEigenvalueSequence T ev →
    ∀ p : ℕ, 0 < p →
      (∑' j, ENNReal.ofReal (‖ev j‖ ^ p)) ≤
      ∑' j, ENNReal.ofReal ((CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p)

/-- Finite-valued specialization, including absolute summability on the left. -/
def WeylSummablePowers : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℂ, AdmissibleEigenvalueSequence T ev →
    ∀ p : ℕ, 0 < p →
    Summable (fun j => (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p) →
    Summable (fun j => ‖ev j‖ ^ p) ∧
      (∑' j, ‖ev j‖ ^ p) ≤
      ∑' j, (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p

def WeylFiniteShiftedProducts : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℂ, AdmissibleEigenvalueSequence T ev →
    ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ,
      (∏ j ∈ Finset.range n, (1 + r * ‖ev j‖)) ≤
      ∏ j ∈ Finset.range n, (1 + r * CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1))

/-- Infinite products mean limits of the displayed initial products. If the
right product has any finite real limit `P`, the left product converges and its
limit is at most `P`. All factors are at least one, including when `r = 0`.
Thus there is no nonzero-limit qualification to add. -/
def WeylInfiniteShiftedProducts : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℂ, AdmissibleEigenvalueSequence T ev →
    ∀ r : ℝ, 0 ≤ r → ∀ P : ℝ,
    Tendsto (fun n => ∏ j ∈ Finset.range n,
      (1 + r * CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1))) atTop (nhds P) →
    ∃ Q : ℝ, Tendsto (fun n => ∏ j ∈ Finset.range n, (1 + r * ‖ev j‖)) atTop (nhds Q) ∧ Q ≤ P

namespace Real

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Real eigenvalues with their full real generalized-eigenspace multiplicity.
Zeros are padding and do not consume multiplicity. -/
def AdmissibleEigenvalueSequence (T : H →L[ℝ] H) (ev : ℕ → ℝ) : Prop := by
  classical
  exact Antitone (fun j => ‖ev j‖) ∧ ∀ n,
    (∀ i : Fin n, ev i.val ≠ 0 → Module.End.HasEigenvalue T.toLinearMap (ev i.val)) ∧
    ∀ z : ℝ, z ≠ 0 →
      (Finset.univ.filter (fun i : Fin n => ev i.val = z)).card ≤
        Module.finrank ℝ (Module.End.maxGenEigenspace T.toLinearMap z)

variable [CompleteSpace H]

def WeylPowerSums : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℝ, AdmissibleEigenvalueSequence T ev →
    ∀ p : ℕ, 0 < p → ∀ n : ℕ,
      (∑ j ∈ Finset.range n, ‖ev j‖ ^ p) ≤
      ∑ j ∈ Finset.range n, (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p

/-- The extended nonnegative sums express the inequality even when the right
sum diverges. For `p = 1` this is the manuscript sum bound; `p = 2` is the
squared-eigenvalue bound used for Hilbert--Schmidt determinants. -/
def WeylExtendedSums : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℝ, AdmissibleEigenvalueSequence T ev →
    ∀ p : ℕ, 0 < p →
      (∑' j, ENNReal.ofReal (‖ev j‖ ^ p)) ≤
      ∑' j, ENNReal.ofReal ((CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p)

/-- Finite-valued specialization, including absolute summability on the left. -/
def WeylSummablePowers : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℝ, AdmissibleEigenvalueSequence T ev →
    ∀ p : ℕ, 0 < p →
    Summable (fun j => (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p) →
    Summable (fun j => ‖ev j‖ ^ p) ∧
      (∑' j, ‖ev j‖ ^ p) ≤
      ∑' j, (CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)) ^ p

def WeylFiniteShiftedProducts : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℝ, AdmissibleEigenvalueSequence T ev →
    ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ,
      (∏ j ∈ Finset.range n, (1 + r * ‖ev j‖)) ≤
      ∏ j ∈ Finset.range n, (1 + r * CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1))

/-- Infinite products mean limits of the displayed initial products. If the
right product has any finite real limit `P`, the left product converges and its
limit is at most `P`. All factors are at least one, including when `r = 0`.
Thus there is no nonzero-limit qualification to add. -/
def WeylInfiniteShiftedProducts : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℝ, AdmissibleEigenvalueSequence T ev →
    ∀ r : ℝ, 0 ≤ r → ∀ P : ℝ,
    Tendsto (fun n => ∏ j ∈ Finset.range n,
      (1 + r * CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1))) atTop (nhds P) →
    ∃ Q : ℝ, Tendsto (fun n => ∏ j ∈ Finset.range n, (1 + r * ‖ev j‖)) atTop (nhds Q) ∧ Q ≤ P

/-- Product bound for each prefix on the original real Hilbert space. -/
def WeylPrefixProducts : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ ev : ℕ → ℝ, AdmissibleEigenvalueSequence T ev → ∀ n : ℕ,
      (∏ j ∈ Finset.range n, ‖ev j‖) ≤
      ∏ j ∈ Finset.range n, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (j+1)

end Real

end ExpandedFA.TraceIdeals.WeylSumsProducts.Spec
