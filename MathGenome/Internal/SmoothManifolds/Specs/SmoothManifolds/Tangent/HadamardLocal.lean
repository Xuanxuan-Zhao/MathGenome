import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models

/-! The local ambient smooth Hadamard lemma, including dimension zero. -/
namespace Specs.SmoothManifolds.Tangent.HadamardLocal

open _root_.SmoothManifolds.ModelData
open scoped BigOperators

/-- An arbitrary smooth function on an open Euclidean domain admits local smooth
coordinate factors with the prescribed actual ambient derivative at the center. -/
def smooth_hadamard_localType : Prop :=
  ∀ (n : ℕ) (U : Set (Euclidean n)) (a : Euclidean n) (F : Euclidean n → ℝ),
    IsOpen U → a ∈ U → ContDiffOn ℝ (⊤ : ℕ∞) F U →
    ∃ V : Set (Euclidean n), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∃ g : Fin n → Euclidean n → ℝ,
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (g i) V) ∧
        (∀ x ∈ V, F x - F a = ∑ i, (x i - a i) * g i x) ∧
        (∀ i, g i a = fderiv ℝ F a (Pi.single i 1))

end Specs.SmoothManifolds.Tangent.HadamardLocal
