import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyPAtoms

/-!
The result `fa2:p4:hardy-decaying-molecule`, paper.tex:20607–20650.
The scalar field is real or complex. The radius parameter is positive, but
both the amplitude zero and Euclidean dimension zero are retained.
The affine normalization is f(x) = r⁻ᵈ g((x-c)/r). Thus its L² size is
A r⁻ᵈ/² and its tail is A r |x-c|⁻ᵈ⁻¹.
All equalities of functions in the conclusion are equalities almost everywhere;
the atomic series converges in the accepted L¹ space.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
universe v

namespace ExpandedFA.PartIV.HardyMoleculesSpec
open Hardy.HardyPAtomsSpec

/-- The source hypotheses, including cancellation; L¹ membership is a conclusion. -/
def IsMolecule {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : Point d → 𝕜) (c : Point d) (r A : ℝ) : Prop :=
  0 < r ∧ 0 ≤ A ∧ MemLp f 2 volume ∧
  (eLpNorm f 2 volume).toReal ≤ A * r ^ (-(d : ℝ) / 2) ∧
  (∫ x, f x) = 0 ∧
  ∀ᵐ x ∂volume, 2 * r ≤ ‖x - c‖ →
    ‖f x‖ ≤ A * r / ‖x - c‖ ^ (d + 1)

/-- Integrability, a Hardy lift with the genuine quotient norm, and an
absolutely summable sequence of the original infinity-atoms. -/
def Conclusion {d : ℕ} {𝕜 : Type v} [RCLike 𝕜]
    (f : Point d → 𝕜) (M : ℝ) : Prop :=
  ∃ hf : Integrable f volume, ∃ h : H1 d 𝕜,
    Hardy.AtomicHardySpaceSpec.EmbeddingValue volume h = hf.toL1 f ∧ ‖h‖ ≤ M ∧
    ∃ a : ℕ → InfinityAtom d 𝕜, ∃ b : ℕ → 𝕜,
      Summable (fun j => ‖b j‖) ∧
      HasSum (fun j => b j • (a j).val) (hf.toL1 f) ∧
      (∑' j, ‖b j‖) ≤ M

def Integrability : Prop :=
  ∀ (d : ℕ) {𝕜 : Type v} [RCLike 𝕜] (f : Point d → 𝕜)
    (c : Point d) (r A : ℝ), IsMolecule f c r A → Integrable f volume

/-- The unit-scale statement as printed in the source. -/
def UnitResult : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type v} [RCLike 𝕜] (f : Point d → 𝕜) (A : ℝ),
      IsMolecule f 0 1 A → Conclusion f (C * A)

/-- A single dimension bound works for every center, positive scale, amplitude,
and both scalar fields. -/
def MainResult : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ {𝕜 : Type v} [RCLike 𝕜] (f : Point d → 𝕜)
      (c : Point d) (r A : ℝ), IsMolecule f c r A → Conclusion f (C * A)

end ExpandedFA.PartIV.HardyMoleculesSpec
