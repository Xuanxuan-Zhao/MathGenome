import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.RCLike.Basic

/-!
Independent formulation of `fa2:p5:projection-method`, paper.tex 22920–22948.
The discrete maps are constructed from the actual projections and the operator,
not supplied as assumed solution operators. They are extended by zero at
noninvertible stages; all assertions about solutions and error estimates are
on the specified invertible tail. No positive dimension is imposed.
-/

open Filter
open scoped Topology

noncomputable section

namespace ExpandedFA.PartV.ProjectionMethod

universe u v w

/-- The finite-dimensional trial and test spaces, with bounded projections. -/
structure Scheme (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] where
  trial : ℕ → Submodule 𝕜 X
  test : ℕ → Submodule 𝕜 Y
  finite_trial : ∀ n, FiniteDimensional 𝕜 (trial n)
  finite_test : ∀ n, FiniteDimensional 𝕜 (test n)
  equal_dimension : ∀ n, Module.finrank 𝕜 (trial n) = Module.finrank 𝕜 (test n)
  projection : ∀ n, Y →L[𝕜] test n
  projection_eq : ∀ n (y : test n), projection n y = y

attribute [instance] Scheme.finite_trial Scheme.finite_test

variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]

/-- The restricted projected equation operator `P_n A|X_n`. -/
def discreteMap (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ) :
    S.trial n →L[𝕜] S.test n :=
  ((S.projection n).comp A).comp (S.trial n).subtypeL

/-- Finite dimension makes the algebraic discrete inverse bounded. -/
def discreteEquiv (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ)
    (h : Function.Bijective (discreteMap S A n)) : S.trial n ≃L[𝕜] S.test n :=
  (LinearEquiv.ofBijective (discreteMap S A n).toLinearMap h).toContinuousLinearEquiv

/-- The data-to-solution map `(P_n A|X_n)⁻¹ P_n`, included into `X`.
Its value at noninvertible stages is irrelevant to the eventual theorem. -/
def dataMap (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ) : Y →L[𝕜] X := by
  classical
  exact if h : Function.Bijective (discreteMap S A n) then
    (S.trial n).subtypeL.comp
      ((discreteEquiv S A n h).symm.toContinuousLinearMap.comp (S.projection n))
  else 0

/-- Exact-data approximation `Q_n = (P_n A|X_n)⁻¹ P_n A`, included into `X`.
The inclusion preserves norms, as trial spaces carry the induced norm. -/
def exactMap (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ) : X →L[𝕜] X :=
  (dataMap S A n).comp A

/-- The supremum is taken over precisely the chosen eventual stages. Its
finiteness is required explicitly wherever it is used in an estimate. -/
def tailNormSup (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (N : ℕ) : ℝ :=
  sSup (Set.range fun n : {n : ℕ // N ≤ n} => ‖exactMap S A n‖)

namespace Spec

/-- Inclusion of the trial space preserves the operator norms occurring in
the source, whose operators are written with codomain `X_n`. -/
def NormIdentification : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ)
    (h : Function.Bijective (discreteMap S A n)),
    ‖dataMap S A n‖ =
      ‖(discreteEquiv S A n h).symm.toContinuousLinearMap.comp (S.projection n)‖ ∧
    ‖exactMap S A n‖ =
      ‖(discreteEquiv S A n h).symm.toContinuousLinearMap.comp
        ((S.projection n).comp A)‖

/-- Equal-dimensional zero stages have an invertible discrete equation and
zero solution operators. No singular value or positive-dimension hypothesis
is needed. -/
def ZeroDimensionalStages : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ),
    Module.finrank 𝕜 (S.trial n) = 0 →
      Function.Bijective (discreteMap S A n) ∧ dataMap S A n = 0 ∧ exactMap S A n = 0

/-- The constructed inverse gives the unique discrete solution for any data. -/
def DiscreteSolution : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ),
    Function.Bijective (discreteMap S A n) →
    ∀ f : Y, dataMap S A n f ∈ S.trial n ∧
      S.projection n (A (dataMap S A n f)) = S.projection n f ∧
      ∀ v : S.trial n, S.projection n (A v) = S.projection n f →
        (v : X) = dataMap S A n f

/-- Exact convergence is equivalent to a uniform norm bound on any tail on
which the discrete equations are invertible. -/
def ProjectionCriterion : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y),
    Function.Injective A →
    (∀ x : X, Tendsto (fun n => Metric.infDist x (S.trial n : Set X)) atTop (𝓝 0)) →
    ∀ N : ℕ, (∀ n, N ≤ n → Function.Bijective (discreteMap S A n)) →
      ((∀ x : X, Tendsto (fun n => exactMap S A n x) atTop (𝓝 x)) ↔
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n, N ≤ n → ‖exactMap S A n‖ ≤ M)

/-- The best-approximation estimate with any common norm bound. -/
def BestApproximation : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ),
    Function.Bijective (discreteMap S A n) →
    ∀ M : ℝ, 0 ≤ M → ‖exactMap S A n‖ ≤ M →
      ∀ x : X, ‖exactMap S A n x - x‖ ≤
        (1 + M) * Metric.infDist x (S.trial n : Set X)

/-- The manuscript's estimate with the actual supremum over the tail. -/
def SupremumBestApproximation : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (N : ℕ),
    (∀ n, N ≤ n → Function.Bijective (discreteMap S A n)) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ n, N ≤ n → ‖exactMap S A n‖ ≤ M) →
      0 ≤ tailNormSup S A N ∧
      ∀ n, N ≤ n → ∀ x : X, ‖exactMap S A n x - x‖ ≤
        (1 + tailNormSup S A N) * Metric.infDist x (S.trial n : Set X)

/-- Stability in the data norm is equivalent to bounded norms of the
data-to-solution maps themselves. Exact-data norms do not replace these. -/
def NoisyDataStability : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (N : ℕ),
    (∃ L : ℝ, 0 ≤ L ∧ ∀ n, N ≤ n → ‖dataMap S A n‖ ≤ L) ↔
      ∃ L : ℝ, 0 ≤ L ∧ ∀ n, N ≤ n → ∀ f g : Y,
        ‖dataMap S A n f - dataMap S A n g‖ ≤ L * ‖f - g‖

/-- The noise term uses an independent bound on `dataMap`, not on `exactMap`. -/
def NoisyErrorEstimate : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y]
    (S : Scheme 𝕜 X Y) (A : X →L[𝕜] Y) (n : ℕ),
    Function.Bijective (discreteMap S A n) →
    ∀ M L : ℝ, 0 ≤ M → ‖exactMap S A n‖ ≤ M →
      0 ≤ L → ‖dataMap S A n‖ ≤ L →
      ∀ (x : X) (f : Y), ‖dataMap S A n f - x‖ ≤
        (1 + M) * Metric.infDist x (S.trial n : Set X) + L * ‖f - A x‖

end Spec
end ExpandedFA.PartV.ProjectionMethod
