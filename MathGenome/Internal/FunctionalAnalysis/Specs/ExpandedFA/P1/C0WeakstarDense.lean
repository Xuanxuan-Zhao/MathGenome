import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06DoubleAnnihilator

/-!
The unnumbered example at paper.tex:1244–1246. The scalar field is real or
complex and the dual is scalar-linear. The coefficient submodule below is
identified with the literal c₀ submodule of the shared ℓ∞ space by the bilinear
sequence-dual isometry. Weak-star closure uses precisely σ((ℓ¹)′, ℓ¹), and its
pullback to ℓ∞; norm closedness uses the original supremum/operator norms.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C0WeakstarDense
open C01SequenceSpaces

/-- Functionals on ℓ¹ whose unit-coordinate coefficients tend to zero. -/
def c0L1DualSubmodule (𝕜 : Type u) [RCLike 𝕜] :
    Submodule 𝕜 (SequenceLp 𝕜 1 →L[𝕜] 𝕜) where
  carrier := {f | Tendsto (fun n => f (lp.single 1 n (1 : 𝕜))) atTop (𝓝 0)}
  zero_mem' := by simp
  add_mem' hf hg := by simpa using hf.add hg
  smul_mem' a f hf := by simpa using hf.const_smul a

/-- The shared weak-star topology, formed after fixing the norm dual of ℓ¹. -/
abbrev l1WeakstarTopology (𝕜 : Type u) [RCLike 𝕜] :
    TopologicalSpace (SequenceLp 𝕜 1 →L[𝕜] 𝕜) :=
  C12DualPairSpec.DualPairTopologyValue 𝕜
    (SequenceLp 𝕜 1 →L[𝕜] 𝕜) (SequenceLp 𝕜 1)
    (topDualPairing 𝕜 (SequenceLp 𝕜 1)).flip

namespace Spec

/-- The series isometry and the exact image of the original c₀. -/
def CoordinateIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ U : SequenceLInfinity 𝕜 ≃ₗᵢ[𝕜] (SequenceLp 𝕜 1 →L[𝕜] 𝕜),
      (∀ a x, U a x = ∑' n, a n * x n) ∧
      (∀ f n, U.symm f n = f (lp.single 1 n (1 : 𝕜))) ∧
      (sequenceC0Submodule 𝕜).map U.toLinearEquiv.toLinearMap = c0L1DualSubmodule 𝕜

/-- Coordinate tests in c₀ kill every coordinate of a preannihilating ℓ¹ vector. -/
def PreannihilatorZero : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    C04Annihilators.Spec.PreannihilatorValue 𝕜 (SequenceLp 𝕜 1)
      (c0L1DualSubmodule 𝕜 : Set (SequenceLp 𝕜 1 →L[𝕜] 𝕜)) = ⊥

/-- Density both in the dual and in ℓ∞ with the topology transported by the
actual bilinear sequence-dual isometry. -/
def WeakStarDensity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    @closure (SequenceLp 𝕜 1 →L[𝕜] 𝕜) (l1WeakstarTopology 𝕜)
      (c0L1DualSubmodule 𝕜 : Set (SequenceLp 𝕜 1 →L[𝕜] 𝕜)) = Set.univ ∧
    ∃ U : SequenceLInfinity 𝕜 ≃ₗᵢ[𝕜] (SequenceLp 𝕜 1 →L[𝕜] 𝕜),
      (∀ a x, U a x = ∑' n, a n * x n) ∧
      @closure (SequenceLInfinity 𝕜)
        (TopologicalSpace.induced U (l1WeakstarTopology 𝕜))
        (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) = Set.univ

/-- Proper norm-closedness in the original sequence space and its isometric
image in the dual; no weak-star closedness is asserted here. -/
def NormClosedProper : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) ∧
      sequenceC0Submodule 𝕜 < ⊤) ∧
    (IsClosed (c0L1DualSubmodule 𝕜 : Set (SequenceLp 𝕜 1 →L[𝕜] 𝕜)) ∧
      c0L1DualSubmodule 𝕜 < ⊤)

end Spec
end ExpandedFA.P1.C0WeakstarDense
