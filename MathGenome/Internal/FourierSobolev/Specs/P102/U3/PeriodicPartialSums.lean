import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugation

/-! Independent scope of paper.tex, Theorem p102:U3-04 (1186–1202).
All sums use the canonical probability-Haar coefficients and symmetric frequencies.
The conjugation conclusion refers to the very same operator as the prerequisite. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace P102.Periodic.PartialSums
open P102.Periodic.Expected P102.Periodic.Conjugation

abbrev Exponent := P102.U2.CZLpData.Exponent

variable (T : ℝ) [Fact (0 < T)]

abbrev Space (p : Exponent) := P102.Periodic.Conjugation.Space T p
abbrev Operator (p : Exponent) := Space T p →L[ℂ] Space T p
abbrev toSpace (p : Exponent) : C(Circle T, ℂ) →L[ℂ] Space T p :=
  ContinuousMap.toLp p.val (haar T) ℂ

/-- The complete conjugation conclusion uses exactly the upstream operator,
including its zero-frequency symbol and polynomial kernel identification. -/
abbrev ConjugationResult (p : Exponent) : Prop :=
  P102.Periodic.Conjugation.Result T p

/-- The actual finite Fourier sum as a continuous function. -/
def finiteSum (N : ℕ) (f : Circle T → ℂ) : C(Circle T, ℂ) :=
  ∑ n ∈ frequencies N, coefficient T f n • mode T n

/-- Both conclusions of the original theorem, together with a uniform bound and
explicit identification of the bounded partial-sum operators with the finite sums.
The conjugation result retains its polynomial action, zero mode, and all-input symbol. -/
def Result (p : Exponent) : Prop :=
  ConjugationResult T p ∧
  ∃ (S : ℕ → Operator T p) (C : ℝ≥0),
    (∀ N f, S N f = toSpace T p (finiteSum T N f)) ∧
    (∀ N, ‖S N‖ ≤ C) ∧
    (∀ f : Space T p, Tendsto (fun N => S N f) atTop (𝓝 f))

end P102.Periodic.PartialSums
namespace P102.Specs.U3.PeriodicPartialSums
open P102.Periodic.PartialSums

def full_theorem : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (p : Exponent), P102.Periodic.PartialSums.Result T p

end P102.Specs.U3.PeriodicPartialSums
