import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint

/-!
Independent statements of the closed-range equivalences and range identities
in `paper.tex` 7523–7549 (`fa2:p2:closed-range`). The minimum-modulus equality
is allocated to `ExpandedFA.Hilbert.ReducedMinimumModulus`.

The operators are bounded scalar-linear maps between arbitrary complete real
or complex Hilbert spaces. All ranges, kernels, norms, and orthogonals are
native ones; the adjoint is the shared Hilbert adjoint. Zero maps and zero
spaces are included, and there are no finite-dimensionality or separability
hypotheses.
-/

namespace ExpandedFA.Hilbert.ClosedRangeEquivalences.Spec
universe u v w

/-- Closed range is equivalent to a positive lower bound on the kernel complement. -/
def ClosedRangeIffLowerBound : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    IsClosed (T.range : Set K) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ x : H, x ∈ T.ker.orthogonal → c * ‖x‖ ≤ ‖T x‖

/-- Closedness of the range is invariant under the Hilbert adjoint. -/
def ClosedRangeAdjointIff : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    IsClosed (T.range : Set K) ↔
      IsClosed ((Adjoint.Spec.AdjointValue 𝕜 H K T).range : Set H)

/-- Under the equivalent conditions both range equalities hold without closures. -/
def ClosedRangeIdentities : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    IsClosed (T.range : Set K) →
      T.range = (Adjoint.Spec.AdjointValue 𝕜 H K T).ker.orthogonal ∧
      (Adjoint.Spec.AdjointValue 𝕜 H K T).range = T.ker.orthogonal

end ExpandedFA.Hilbert.ClosedRangeEquivalences.Spec
