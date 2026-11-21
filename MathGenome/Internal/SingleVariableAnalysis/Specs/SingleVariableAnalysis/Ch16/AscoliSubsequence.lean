import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Equicontinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Complete

/-!
K03.16.ascoli, paper.tex:3842–3851: the subsequence assertion and its
countable-dense-set and uniform-Cauchy intermediate conclusions.
All domains carry the induced real metric. No nonemptiness is required.
The family predicates below are the upstream canonical epsilon predicates.
The family compactness characterization is a separate planned obligation.
-/
namespace Specs.SingleVariableAnalysis.Ch16.AscoliSubsequence
open scoped Topology

/-- Simultaneous extraction on any prescribed countable set, before using
 equicontinuity. The proper target hypothesis is instantiated with ℝ and ℂ. -/
def countableExtraction : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [ProperSpace E]
    (K : Set ℝ) (F : ℕ → C(K, E)) (D : Set K), D.Countable →
    Equicontinuity.uniformlyBoundedFamilyValue K (Set.range F) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : D → E,
      ∀ x : D, Filter.Tendsto (fun n => F (φ n) x.val) Filter.atTop (𝓝 (L x))

/-- Three errors through finitely many centers in the dense set. -/
def uniformCauchyFromDense : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] (K : Set ℝ) [CompactSpace K]
    (F : ℕ → C(K, E)) (D : Set K), Dense D →
    Equicontinuity.uniformlyEquicontinuousFamilyValue K (Set.range F) →
    (∀ x ∈ D, CauchySeq (fun n => F n x)) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ∀ x : K, ‖F n x - F m x‖ < ε

def realAscoliSubsequence : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)),
    Equicontinuity.uniformlyBoundedFamilyValue K (Set.range F) →
    Equicontinuity.pointwiseEquicontinuousFamilyValue K (Set.range F) →
    ∃ (D : Set K), D.Countable ∧ Dense D ∧
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      (∃ L : D → ℝ, ∀ x : D,
        Filter.Tendsto (fun n => F (φ n) x.val) Filter.atTop (𝓝 (L x))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x : K, |F (φ n) x - F (φ m) x| < ε) ∧
      ∃ f : C(K, ℝ),
        Ch12.Uniform.realUniformConvergesValue (fun n x => F (φ n) x) f ∧
        Filter.Tendsto (fun n => ‖F (φ n) - f‖) Filter.atTop (𝓝 0)

def complexAscoliSubsequence : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)),
    Equicontinuity.uniformlyBoundedFamilyValue K (Set.range F) →
    Equicontinuity.pointwiseEquicontinuousFamilyValue K (Set.range F) →
    ∃ (D : Set K), D.Countable ∧ Dense D ∧
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      (∃ L : D → ℂ, ∀ x : D,
        Filter.Tendsto (fun n => F (φ n) x.val) Filter.atTop (𝓝 (L x))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m ≥ N, ∀ n ≥ N, ∀ x : K, ‖F (φ n) x - F (φ m) x‖ < ε) ∧
      ∃ f : C(K, ℂ),
        Ch12.Uniform.complexUniformConvergesValue (fun n x => F (φ n) x) f ∧
        Filter.Tendsto (fun n => ‖F (φ n) - f‖) Filter.atTop (𝓝 0)

end Specs.SingleVariableAnalysis.Ch16.AscoliSubsequence
