import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statements for `fa2:p3:subspace-gap`, paper.tex:14216–14250.
The dual consists of continuous functionals linear over the original scalar field.
The supremum is over the closed unit ball, including zero in every subspace. -/
namespace ExpandedFA.Unbounded.OneSidedSubspaceGap.Spec

def GapType : Type _ :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    Submodule 𝕜 X → Submodule 𝕜 X → ℝ
noncomputable def gapValue : GapType := fun {_ X} _ _ _ M N =>
  sSup {r : ℝ | ∃ x : X, x ∈ M ∧ ‖x‖ ≤ 1 ∧ r = Metric.infDist x (N : Set X)}

def AnnihilatorType : Type _ :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    Submodule 𝕜 X → Submodule 𝕜 (X →L[𝕜] 𝕜)
def annihilatorValue : AnnihilatorType := fun {_ _} _ _ _ M =>
  { carrier := {f | ∀ x ∈ M, f x = 0}
    zero_mem' := by simp
    add_mem' := by intro f g hf hg x hx; simp [hf x hx, hg x hx]
    smul_mem' := by intro c f hf x hx; simp [hf x hx] }

def Bounds : Prop :=
  ∀ (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] (M N : Submodule 𝕜 X),
    IsClosed (M : Set X) → IsClosed (N : Set X) →
    0 ≤ gapValue M N ∧ gapValue M N ≤ 1

def AnnihilatorDuality : Prop :=
  ∀ (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] (M N : Submodule 𝕜 X),
    IsClosed (M : Set X) → IsClosed (N : Set X) →
    gapValue M N = gapValue (annihilatorValue N) (annihilatorValue M)

def TriangleEstimate : Prop :=
  ∀ (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] (M N L : Submodule 𝕜 X),
    IsClosed (M : Set X) → IsClosed (N : Set X) → IsClosed (L : Set X) →
    gapValue M L ≤ gapValue M N + gapValue N L + gapValue M N * gapValue N L

def ProperInclusion : Prop :=
  ∀ (𝕜 X : Type*) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [CompleteSpace X] (M N : Submodule 𝕜 X),
    IsClosed (M : Set X) → IsClosed (N : Set X) → N < M → gapValue M N = 1

end ExpandedFA.Unbounded.OneSidedSubspaceGap.Spec
