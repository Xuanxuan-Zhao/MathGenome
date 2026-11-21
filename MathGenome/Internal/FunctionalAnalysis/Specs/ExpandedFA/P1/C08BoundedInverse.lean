import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C08OpenMapping

/-!
Independent statement of Corollary `fa2:p1:c08:bounded-inverse`, paper.tex
1590–1595. `CompleteSpace` is completeness in the given norm, as identified
by the shared Banach interface. The scalar field is real or complex.
The two inverse identities characterize the algebraic inverse; its boundedness
is a conclusion, expressed by its membership in the native operator space.
The estimate uses the actual image of the strict open unit ball and quantifies
over every positive radius with the required inclusion. Zero spaces are allowed.
-/

namespace ExpandedFA.P1.C08BoundedInverse.Spec

universe u v w

/-- A bounded bijection of Banach spaces has a bounded linear algebraic inverse,
with the sharp bound supplied by any admissible open-ball radius. -/
def BoundedInverse : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F), Function.Bijective T →
      ∃ S : F →L[𝕜] E,
        (∀ x : E, S (T x) = x) ∧ (∀ y : F, T (S y) = y) ∧
        ∀ c : ℝ, 0 < c →
          Metric.ball (0 : F) c ⊆ T '' Metric.ball (0 : E) 1 → ‖S‖ ≤ 1 / c

end ExpandedFA.P1.C08BoundedInverse.Spec
