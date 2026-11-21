import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Independent specification of paper.tex, d13:02:bernoulli.

The interval is the shared `TimeInterval`, including any included endpoints.
Ambient representatives are compared only on this actual interval. The scalar
predicates below spell out the common differential solution condition for the
specified right hand sides; the bridge targets identify them with the shared
ODE solution predicate whenever that field is given. No value at zero or a
negative state is admitted by either positive-solution predicate.
-/

noncomputable section
open Set

namespace D13Unified

/-- Positive differential solutions on their actual time interval. -/
def PositiveBernoulliOn (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval)
    (x : ℝ → ℝ) : Prop :=
  ContinuousOn x I.carrier ∧ (∀ t ∈ I.carrier, 0 < x t) ∧
    ∀ t ∈ I.carrier,
      HasDerivWithinAt x (a t * x t + b t * (x t) ^ p) I.carrier t

/-- Positive solutions of the transformed linear equation. -/
def PositiveBernoulliLinearOn (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval)
    (u : ℝ → ℝ) : Prop :=
  ContinuousOn u I.carrier ∧ (∀ t ∈ I.carrier, 0 < u t) ∧
    ∀ t ∈ I.carrier,
      HasDerivWithinAt u ((1 - p) * a t * u t + (1 - p) * b t) I.carrier t

/-- Actual-domain functions, with no data outside the solution interval. -/
def PositiveBernoulliSolutions (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval) :=
  {v : I.carrier → ℝ // ∃ x : ℝ → ℝ,
    PositiveBernoulliOn a b p I x ∧ ∀ t : I.carrier, x t = v t}

def PositiveBernoulliLinearSolutions (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval) :=
  {v : I.carrier → ℝ // ∃ u : ℝ → ℝ,
    PositiveBernoulliLinearOn a b p I u ∧ ∀ t : I.carrier, u t = v t}

end D13Unified

namespace Specs.D13Unified.Ch02.Bernoulli
open _root_.D13Unified

/-- Both directions retain the entire interval and positivity; the displayed
inverse identities are on that interval, not on ambient representatives. -/
def reductionExpected : Prop :=
  ∀ (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval),
    ContinuousOn a I.carrier → ContinuousOn b I.carrier → p ≠ 1 →
    (∀ x, PositiveBernoulliOn a b p I x →
      PositiveBernoulliLinearOn a b p I (fun t => (x t) ^ (1 - p))) ∧
    (∀ u, PositiveBernoulliLinearOn a b p I u →
      PositiveBernoulliOn a b p I (fun t => (u t) ^ (1 / (1 - p)))) ∧
    (∀ x, PositiveBernoulliOn a b p I x →
      EqOn (fun t => ((x t) ^ (1 - p)) ^ (1 / (1 - p))) x I.carrier) ∧
    (∀ u, PositiveBernoulliLinearOn a b p I u →
      EqOn (fun t => ((u t) ^ (1 / (1 - p))) ^ (1 - p)) u I.carrier)

/-- A literal bijection between positive solutions as maps on their actual
interval, with the specified substitution and inverse. -/
def solutionBijectionExpected : Prop :=
  ∀ (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval),
    ContinuousOn a I.carrier → ContinuousOn b I.carrier → p ≠ 1 →
    ∃ e : PositiveBernoulliSolutions a b p I ≃ PositiveBernoulliLinearSolutions a b p I,
      (∀ x t, (e x).val t = (x.val t) ^ (1 - p)) ∧
      (∀ u t, (e.symm u).val t = (u.val t) ^ (1 / (1 - p)))

/-- Exact compatibility with the accepted common solution concept, for any
continuous ODE on an open domain whose values on the graph are the RHS. -/
def solutionBridgeExpected : Prop :=
  ∀ (F : ODE ℝ) (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval) (x : ℝ → ℝ),
    (∀ t ∈ I.carrier, (t, x t) ∈ F.domain) →
    (∀ t ∈ I.carrier, F.eval t (x t) = a t * x t + b t * (x t) ^ p) →
    (PositiveBernoulliOn a b p I x ↔
      Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F I x ∧
        ∀ t ∈ I.carrier, 0 < x t)

def linearSolutionBridgeExpected : Prop :=
  ∀ (F : ODE ℝ) (a b : ℝ → ℝ) (p : ℝ) (I : TimeInterval) (u : ℝ → ℝ),
    (∀ t ∈ I.carrier, (t, u t) ∈ F.domain) →
    (∀ t ∈ I.carrier, F.eval t (u t) = (1 - p) * a t * u t + (1 - p) * b t) →
    (PositiveBernoulliLinearOn a b p I u ↔
      Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F I u ∧
        ∀ t ∈ I.carrier, 0 < u t)

/-- On open intervals these differential predicates have precisely the C¹
regularity required of classical solutions; coefficients are merely continuous. -/
def classicalRegularityExpected : Prop :=
  ∀ (a b : ℝ → ℝ) (p : ℝ) (I : OpenTimeInterval),
    ContinuousOn a I.carrier → ContinuousOn b I.carrier →
    (∀ x, PositiveBernoulliOn a b p I.toTimeInterval x → ContDiffOn ℝ 1 x I.carrier) ∧
    (∀ u, PositiveBernoulliLinearOn a b p I.toTimeInterval u → ContDiffOn ℝ 1 u I.carrier)

/-- The common classical ODE notion on open intervals, with the original
field domain and graph membership retained. -/
def classicalSolutionBridgeExpected : Prop :=
  ∀ (F : ODE ℝ) (a b : ℝ → ℝ) (p : ℝ) (I : OpenTimeInterval) (x : ℝ → ℝ),
    (∀ t ∈ I.carrier, (t, x t) ∈ F.domain) →
    (∀ t ∈ I.carrier, F.eval t (x t) = a t * x t + b t * (x t) ^ p) →
    (PositiveBernoulliOn a b p I.toTimeInterval x ↔
      Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue F I x ∧
        ∀ t ∈ I.carrier, 0 < x t)

def linearClassicalSolutionBridgeExpected : Prop :=
  ∀ (F : ODE ℝ) (a b : ℝ → ℝ) (p : ℝ) (I : OpenTimeInterval) (u : ℝ → ℝ),
    (∀ t ∈ I.carrier, (t, u t) ∈ F.domain) →
    (∀ t ∈ I.carrier, F.eval t (u t) = (1 - p) * a t * u t + (1 - p) * b t) →
    (PositiveBernoulliLinearOn a b p I.toTimeInterval u ↔
      Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue F I u ∧
        ∀ t ∈ I.carrier, 0 < u t)

end Specs.D13Unified.Ch02.Bernoulli
