import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint

/-!
Independent statements for the discrete case of `fa2:p2:mean-ergodic`,
`paper.tex` 12556–12574. All closures are norm closures. A contraction means
operator norm at most one, and strong convergence means norm convergence on
each vector. Natural indices include zero, which does not affect the limit
as N tends to infinity (and hence eventually through positive integers).

The fixed space is the native closed submodule ker(I - T); its projector is
the shared ambient-valued orthogonal projector. Neither normality nor any
dimension or separability hypothesis is imposed, and H may be the zero space.
-/

noncomputable section
open scoped Topology

namespace ExpandedFA.Ergodic.DiscreteMeanErgodic.Spec
universe u v

/-- The kernel used throughout is exactly the space of fixed vectors. -/
def KernelFixedPoints : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) (x : H),
    x ∈ (1 - T).ker ↔ T x = x

/-- A contraction and its Hilbert adjoint have the same fixed space. -/
def FixedSpaces : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), ‖T‖ ≤ 1 →
    (1 - T).ker = (1 - Hilbert.Adjoint.Spec.AdjointValue 𝕜 H H T).ker

/-- The closure of the coboundary range is the orthogonal complement of Fix T. -/
def RangeClosure : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), ‖T‖ ≤ 1 →
    (1 - T).range.topologicalClosure = (1 - T).ker.orthogonal

/-- H is the orthogonal topological direct sum of Fix T and closure Ran(I - T),
including uniqueness of the two coordinates of each vector. -/
def OrthogonalDecomposition : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), ‖T‖ ≤ 1 →
    Submodule.IsTopCompl (1 - T).ker (1 - T).range.topologicalClosure ∧
      ∀ x : H, ∃! yz : (1 - T).ker × (1 - T).range.topologicalClosure,
        (yz.1 : H) + (yz.2 : H) = x

/-- Pointwise norm convergence of the actual operator-power Cesàro means to
the shared orthogonal projection onto ker(I - T). -/
def StrongConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H), ‖T‖ ≤ 1 → ∀ x : H,
    Filter.Tendsto
      (fun N : ℕ => (((N : 𝕜)⁻¹ • ∑ k ∈ Finset.range N, T ^ k) : H →L[𝕜] H) x)
      Filter.atTop
      (𝓝 (Hilbert.Conventions.Spec.OrthogonalProjectionValue 𝕜 H (1 - T).ker x))

end ExpandedFA.Ergodic.DiscreteMeanErgodic.Spec
