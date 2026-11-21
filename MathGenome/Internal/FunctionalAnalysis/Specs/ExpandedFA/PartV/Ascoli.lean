import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
Independent statement of paper.tex, `fa2:p5:ascoli` (21645–21665).

`C(X, 𝕜)` carries its canonical supremum norm. Relative compactness means
compactness of the closure in that norm topology. `Equicontinuous` uses
neighborhoods in the given topology on X, with one neighborhood working for
every member of the family. In particular, X need not be metrizable.
`RCLike` covers both real and complex scalars. No nonemptiness assumption is
made on X or on the family.
-/

universe u v
namespace ExpandedFA.PartV.Ascoli.Spec

/-- A family is relatively compact in the uniform norm exactly when it has
a common bound for all its values and is equicontinuous. -/
def ArzelaAscoli : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (A : Set C(X, 𝕜)),
    IsCompact (closure A) ↔
      (∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ A, ∀ x : X, ‖f x‖ ≤ M) ∧
        Equicontinuous (fun (f : A) (x : X) => (f : C(X, 𝕜)) x)

end ExpandedFA.PartV.Ascoli.Spec
