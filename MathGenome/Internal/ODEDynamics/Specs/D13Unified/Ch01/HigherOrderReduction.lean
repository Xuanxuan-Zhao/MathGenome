import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Independent formulation of paper.tex, d13:01:higher-order.
The order is `k + 1`, covering every positive order, including one when `k = 0`.
The state `E` may in particular be `Fin d → ℝ` for any finite `d`, with any norm;
the stronger normed-space generality does not require completeness.
Functions in the solution sets have the actual time interval as their source.
Their zero extensions are merely representatives for calculus on that interval.
-/

noncomputable section
open Set

namespace D13Unified.HigherOrder

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original continuous right hand side, with its actual open domain. -/
structure Equation (k : ℕ) where
  domain : Set (ℝ × (Fin (k + 1) → E))
  isOpen_domain : IsOpen domain
  field : domain → E
  continuous_field : Continuous field

variable {E}

/-- Canonical representative of a function on an actual time interval. -/
def representative (I : OpenTimeInterval) (y : I.carrier → E) (t : ℝ) : E := by
  classical
  exact if ht : t ∈ I.carrier then y ⟨t, ht⟩ else 0

/-- The derivative tuple `(y,y',…,y^(k))`, computed on the same interval. -/
def jet (I : OpenTimeInterval) (k : ℕ) (y : ℝ → E) (t : ℝ) (j : Fin (k + 1)) : E :=
  iteratedDerivWithin j.val y I.carrier t

namespace Equation

/-- Evaluation off the domain is immaterial: both solution predicates impose
membership in the domain at every time. -/
def eval {k : ℕ} (G : Equation E k) (t : ℝ) (X : Fin (k + 1) → E) : E := by
  classical
  exact if h : (t, X) ∈ G.domain then G.field ⟨(t, X), h⟩ else 0

/-- The companion system has the identical time-state domain. -/
def toODE {k : ℕ} (G : Equation E k) : ODE (Fin (k + 1) → E) where
  domain := G.domain
  isOpen_domain := G.isOpen_domain
  field := fun p j => if h : j.val < k then p.val.2 ⟨j.val + 1, Nat.succ_lt_succ h⟩
    else G.field p
  continuous_field := continuous_pi fun j => by
    by_cases h : j.val < k
    · simpa only [dite_eq_left h, Function.comp_def] using
        (continuous_apply (⟨j.val + 1, Nat.succ_lt_succ h⟩ : Fin (k + 1))).comp
          (continuous_snd.comp continuous_subtype_val)
    · simpa only [dite_eq_right h] using G.continuous_field

end Equation

/-- `C^(k+1)` solution of the original equation on its actual open interval. -/
def IsHigherSolution {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (y : I.carrier → E) : Prop :=
  ContDiffOn ℝ (k + 1 : ℕ) (representative I y) I.carrier ∧
  (∀ t ∈ I.carrier, (t, jet I k (representative I y) t) ∈ G.domain) ∧
  ∀ t ∈ I.carrier,
    iteratedDerivWithin (k + 1) (representative I y) I.carrier t =
      G.eval t (jet I k (representative I y) t)

/-- The ordinary shared C¹ solution predicate for the companion system. -/
def IsSystemSolution {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (Y : I.carrier → (Fin (k + 1) → E)) : Prop :=
  Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue G.toODE I
    (representative I Y)

abbrev HigherSolutions {k : ℕ} (G : Equation E k) (I : OpenTimeInterval) :=
  {y : I.carrier → E // IsHigherSolution G I y}

abbrev SystemSolutions {k : ℕ} (G : Equation E k) (I : OpenTimeInterval) :=
  {Y : I.carrier → (Fin (k + 1) → E) // IsSystemSolution G I Y}

end D13Unified.HigherOrder

namespace Specs.D13Unified.Ch01.HigherOrderReduction
open _root_.D13Unified _root_.D13Unified.HigherOrder

/-- Full reduction theorem: a bijection on the same actual interval, with the
prescribed forward and inverse maps, all converse regularity and derivative
coordinate identities, and equivalence of every vector initial condition. -/
def reductionExpected : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (G : Equation E k) (I : OpenTimeInterval),
  ∃ e : HigherSolutions G I ≃ SystemSolutions G I,
    (∀ (y : HigherSolutions G I) (t : I.carrier) (j : Fin (k + 1)),
      (e y).val t j = iteratedDerivWithin j.val (representative I y.val) I.carrier t) ∧
    (∀ (Y : SystemSolutions G I) (t : I.carrier),
      (e.symm Y).val t = Y.val t 0) ∧
    (∀ Y : SystemSolutions G I,
      ContDiffOn ℝ (k + 1 : ℕ) (representative I (fun t => Y.val t 0)) I.carrier ∧
      (∀ (t : I.carrier) (j : Fin (k + 1)),
        iteratedDerivWithin j.val (representative I (fun t => Y.val t 0)) I.carrier t =
          Y.val t j) ∧
      (∀ t : I.carrier,
        iteratedDerivWithin (k + 1) (representative I (fun t => Y.val t 0)) I.carrier t =
          G.eval t (Y.val t))) ∧
    (∀ (y : HigherSolutions G I) (s : I.carrier) (ξ : Fin (k + 1) → E),
      (∀ j : Fin (k + 1),
        iteratedDerivWithin j.val (representative I y.val) I.carrier s = ξ j) ↔
      (e y).val s = ξ)

end Specs.D13Unified.Ch01.HigherOrderReduction
