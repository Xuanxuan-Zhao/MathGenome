import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLevelDecomposition

/-! Independent statement of paper.tex, `fa2:p4:hardy-grand-atomic`.
The standing assumptions of this chapter are d ≥ 1 and sufficiently large N.
The atomic space and atoms are the canonical upstream objects. -/
set_option autoImplicit false

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Specs.ExpandedFA.PartIV.HardyGrandAtomic
open _root_.ExpandedFA.Fourier
open _root_.ExpandedFA.PartIV.HardyMaximalSpec
open _root_.ExpandedFA.Hardy.AtomicHardySpaceSpec

/-- An absolutely convergent canonical atom series, its quantitative bound,
its identification with f, and the resulting cancellation. -/
def grandAtomicType : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d N : ℕ), 0 < d → AdmissibleOrder d N →
  ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜) (hf : Integrable f),
    (∫⁻ x, grand N f x) < ⊤ →
    ∃ h : HardyValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)),
      EmbeddingValue volume h = hf.toL1 f ∧
      ‖h‖ ≤ C * (∫⁻ x, grand N f x).toReal ∧
      (∃ (a : ℕ → AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d)))
          (b : ℕ → 𝕜),
        Summable (fun j => ‖b j‖) ∧
        (∑' j, ‖b j‖) ≤ C * (∫⁻ x, grand N f x).toReal ∧
        Summable (fun j => ‖b j • (a j).val‖) ∧
        HasSum (fun j => b j • (a j).val) (hf.toL1 f)) ∧
      (∫ x, f x) = 0

end Specs.ExpandedFA.PartIV.HardyGrandAtomic
