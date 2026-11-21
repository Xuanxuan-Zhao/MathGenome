import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.CompactDefectClosedRange
import Mathlib.Topology.Algebra.Module.Complement

/-! Independent specifications for the stabilization and Riesz decomposition
clauses of paper.tex:10322–10377. The scalar field is real or complex;
compact closure is inside the original normed space, which need not be complete.
All subspaces carry their inherited norm topology. -/
namespace ExpandedFA.Fredholm.CompactDefectStabilizationSpec

universe u v

variable {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/-- The manuscript's `N_m`, including `N_0`. -/
def kernelChain (K : E →L[𝕂] E) (m : ℕ) : Submodule 𝕂 E :=
  LinearMap.ker ((ContinuousLinearMap.id 𝕂 E - K).toLinearMap ^ m)

/-- The manuscript's `R_m`, including `R_0`. -/
def rangeChain (K : E →L[𝕂] E) (m : ℕ) : Submodule 𝕂 E :=
  LinearMap.range ((ContinuousLinearMap.id 𝕂 E - K).toLinearMap ^ m)

def Chains : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    kernelChain K 0 = ⊥ ∧ rangeChain K 0 = ⊤ ∧
      Monotone (kernelChain K) ∧ Antitone (rangeChain K)

def Propagation : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E) (m : ℕ),
    (kernelChain K m = kernelChain K (m + 1) →
      ∀ n, m ≤ n → kernelChain K n = kernelChain K m) ∧
    (rangeChain K m = rangeChain K (m + 1) →
      ∀ n, m ≤ n → rangeChain K n = rangeChain K m)

def Stabilization : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    (∃ m : ℕ, ∀ n, m ≤ n → kernelChain K n = kernelChain K m) ∧
    (∃ m : ℕ, ∀ n, m ≤ n → rangeChain K n = rangeChain K m)

/-- The two stable subspaces, their bounded coordinates, and the actual
restrictions of `I-K`. The power witnessing nilpotence is the given `p`. -/
def Decomposition (K : E →L[𝕂] E) (p : ℕ) : Prop :=
  Submodule.IsTopCompl (kernelChain K p) (rangeChain K p) ∧
  IsClosed (kernelChain K p : Set E) ∧
  FiniteDimensional 𝕂 (kernelChain K p) ∧
  IsClosed (rangeChain K p : Set E) ∧
  (∃ (P : E →L[𝕂] kernelChain K p) (Q : E →L[𝕂] rangeChain K p),
    ∀ x, (P x : E) + (Q x : E) = x ∧
      ∀ (n : kernelChain K p) (r : rangeChain K p),
        (n : E) + (r : E) = x → n = P x ∧ r = Q x) ∧
  (∀ x ∈ kernelChain K p, (ContinuousLinearMap.id 𝕂 E - K) x ∈ kernelChain K p) ∧
  (∀ x ∈ rangeChain K p, (ContinuousLinearMap.id 𝕂 E - K) x ∈ rangeChain K p) ∧
  (∃ T : kernelChain K p →L[𝕂] kernelChain K p,
    (∀ x, (T x : E) = (ContinuousLinearMap.id 𝕂 E - K) x) ∧ T ^ p = 0) ∧
  (∃ e : rangeChain K p ≃L[𝕂] rangeChain K p,
    ∀ x, (e x : E) = (ContinuousLinearMap.id 𝕂 E - K) x)

/-- Every positive common stabilization index gives the full decomposition. -/
def AtCommonIndex : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    ∀ p : ℕ, 1 ≤ p →
      kernelChain K p = kernelChain K (p + 1) →
      rangeChain K p = rangeChain K (p + 1) → Decomposition K p

/-- A single positive cutoff works for all later exponents, both for
chain constancy and for the full bounded decomposition. -/
def FullConclusion (K : E →L[𝕂] E) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ ∀ r : ℕ, q ≤ r →
    kernelChain K r = kernelChain K q ∧
    rangeChain K r = rangeChain K q ∧ Decomposition K r

def FullTheorem : Prop :=
  ∀ {𝕂 : Type u} [RCLike 𝕂] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕂 E] (K : E →L[𝕂] E),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
    FullConclusion K

end ExpandedFA.Fredholm.CompactDefectStabilizationSpec
