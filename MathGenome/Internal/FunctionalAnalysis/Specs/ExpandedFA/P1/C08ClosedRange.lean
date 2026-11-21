import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.RCLike.Basic

/-!
Independent statements for `fa2:p1:c08:closed-range`, paper.tex 1659–1690.
The distance is to the entire kernel in the given norm. The final assertion
requires completeness only of the domain. Both scalar fields, zero spaces,
and the zero operator are allowed. `CompleteSpace` expresses completeness
in the given norm (the shared Chapter 1 Banach identification).
-/

namespace ExpandedFA.P1.C08ClosedRange.Spec

universe u v w

/-- The quotient norm is exactly the distance occurring in the source. -/
def KernelDistance : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    IsClosed (T.ker : Set E) ∧
      ∀ x : E, ‖T.ker.mkQ x‖ = Metric.infDist x (T.ker : Set E)

/-- The full, noninjective closed-range criterion. -/
def ClosedRangeDistance : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F),
    IsClosed (Set.range T) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x : E,
        Metric.infDist x (T.ker : Set E) ≤ C * ‖T x‖

/-- No completeness is needed to identify the injective kernel distance. -/
def InjectiveKernelDistance : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F), Function.Injective T → ∀ x : E,
      Metric.infDist x (T.ker : Set E) = ‖x‖

/-- The injective specialization preserves each specified constant. -/
def InjectiveDistanceEstimateSpecialization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F), Function.Injective T → ∀ C : ℝ,
      ((∀ x : E, Metric.infDist x (T.ker : Set E) ≤ C * ‖T x‖) ↔
        ∀ x : E, ‖x‖ ≤ C * ‖T x‖)

/-- For an injective operator between Banach spaces, closed range is
exactly boundedness below. -/
def InjectiveClosedRange : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F), Function.Injective T →
      (IsClosed (Set.range T) ↔
        ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * ‖T x‖)

/-- A lower bound gives a bounded two-sided inverse on the actual range,
with the same operator-norm bound; the target need not be complete. -/
def BoundedBelowClosedRange : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E]
    (T : E →L[𝕜] F) (C : ℝ),
    0 < C → (∀ x : E, ‖x‖ ≤ C * ‖T x‖) →
      Function.Injective T ∧ IsClosed (T.range : Set F) ∧
        ∃ S : T.range →L[𝕜] E, ‖S‖ ≤ C ∧
          (∀ x : E, S (T.rangeRestrict x) = x) ∧
          (∀ y : T.range, T (S y) = (y : F))

end ExpandedFA.P1.C08ClosedRange.Spec
