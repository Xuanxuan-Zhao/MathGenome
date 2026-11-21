import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
Independent statements of paper.tex:1823–1834 (`fa2:p1:seminorm-model`).
The scalar field is real or complex and local convexity is real convexity.
Finite suprema of seminorms are pointwise maxima (with the empty supremum zero).
Thus the displayed bases include the whole space, and zero spaces and empty
separating families are allowed. No completeness or metrizability is assumed.
-/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1.SeminormModelSpec

def topologyType :=
  ∀ (𝕜 E ι : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E],
    (ι → Seminorm 𝕜 E) → TopologicalSpace E

/-- The canonical topology, defined using positive finite intersections of balls. -/
def topologyValue : topologyType := fun _ _ _ _ _ _ p =>
  (SeminormFamily.moduleFilterBasis p).topology

def Construction : Prop :=
  ∀ (𝕜 E ι : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (p : ι → Seminorm 𝕜 E),
    (∀ x : E, x ≠ 0 → ∃ i, p i x ≠ 0) →
    letI : TopologicalSpace E := topologyValue 𝕜 E ι p
    LCS 𝕜 E ∧ T2Space E ∧
      (𝓝 (0 : E)).HasBasis (fun sr : Finset ι × ℝ => 0 < sr.2)
        (fun sr => {x : E | ∀ i ∈ sr.1, p i x < sr.2}) ∧
      ∀ i, Continuous (p i)

/-- Among vector topologies the displayed zero-neighborhood basis uniquely
determines the canonical topology, even without separation. -/
def TopologyCharacterization : Prop :=
  ∀ (𝕜 E ι : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [t : TopologicalSpace E] [IsTopologicalAddGroup E] (p : ι → Seminorm 𝕜 E),
    (𝓝 (0 : E)).HasBasis (fun sr : Finset ι × ℝ => 0 < sr.2)
      (fun sr => {x : E | ∀ i ∈ sr.1, p i x < sr.2}) ↔
    t = topologyValue 𝕜 E ι p

/-- All continuous seminorms recover the given Hausdorff LCS topology and
separate points. The basis is stated explicitly as well as by topology equality. -/
def ContinuousSeminormsModel : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [t : TopologicalSpace E] [T2Space E],
    LCS 𝕜 E →
    let p : {q : Seminorm 𝕜 E // Continuous q} → Seminorm 𝕜 E := fun q => q.1
    t = topologyValue 𝕜 E _ p ∧
      (∀ x : E, x ≠ 0 → ∃ i, p i x ≠ 0) ∧
      (𝓝 (0 : E)).HasBasis
        (fun sr : Finset {q : Seminorm 𝕜 E // Continuous q} × ℝ => 0 < sr.2)
        (fun sr => {x : E | ∀ i ∈ sr.1, p i x < sr.2})

/-- The source's finite-maximum criterion, for arbitrary continuous target
seminorms and scalar-linear maps. The constant is strictly positive. -/
def LinearContinuity : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [Module ℝ E] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace E] [TopologicalSpace F] [T2Space E] [T2Space F],
    LCS 𝕜 E → LCS 𝕜 F → ∀ T : E →ₗ[𝕜] F,
      Continuous T ↔
        ∀ q : Seminorm 𝕜 F, Continuous q →
          ∃ s : Finset (Seminorm 𝕜 E), (∀ p ∈ s, Continuous p) ∧
            ∃ C : ℝ, 0 < C ∧ ∀ x : E, q (T x) ≤ C * (s.sup id) x

end ExpandedFA.P1.SeminormModelSpec
