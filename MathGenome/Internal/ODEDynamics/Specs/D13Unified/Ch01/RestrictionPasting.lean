import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts

/-! Independent statements for paper.tex, Proposition d13:01:pasting.
The endpoint statement assumes continuity and the equation off the join only;
it does not assume either derivative at the join. No uniqueness is assumed.
-/
noncomputable section
open Set

namespace D13Unified

/-- The actual union interval of two intervals with a common point. -/
def TimeInterval.union (I J : TimeInterval) (h : (I.carrier ∩ J.carrier).Nonempty) :
    TimeInterval where
  carrier := I.carrier ∪ J.carrier
  nonempty := I.nonempty.mono subset_union_left
  ordConnected := by
    obtain ⟨s, hsI, hsJ⟩ := h
    apply ordConnected_of_uIcc_subset_left (x := s)
    intro t ht
    rcases ht with ht | ht
    · exact (I.ordConnected.uIcc_subset hsI ht).trans subset_union_left
    · exact (J.ordConnected.uIcc_subset hsJ ht).trans subset_union_right

/-- The agreed curve, choosing the first representative on its actual domain. -/
def pasteCurves {E : Type*} (A : Set ℝ) (x y : ℝ → E) : ℝ → E := by
  classical
  exact A.piecewise x y

end D13Unified

namespace Specs.D13Unified.Ch01.RestrictionPasting
open _root_.D13Unified
universe u

/-- Restriction retains continuity, graph membership and the relative derivative
on every nonempty subinterval, including any included endpoints. -/
def restrictionExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (I J : TimeInterval) (x : ℝ → E),
    J.carrier ⊆ I.carrier → SolutionConcepts.solutionOnValue F I x →
    SolutionConcepts.solutionOnValue F J x

/-- On open subintervals, restriction preserves the full classical C¹ predicate. -/
def classicalRestrictionExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (I J : OpenTimeInterval) (x : ℝ → E),
    J.carrier ⊆ I.carrier → SolutionConcepts.classicalSolutionOnValue F I x →
    SolutionConcepts.classicalSolutionOnValue F J x

/-- Compatible curves on arbitrary overlapping intervals produce a solution on
exactly their union, agreeing with each original on its entire domain. -/
def compatiblePastingExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (I J : TimeInterval) (x y : ℝ → E)
    (h : (I.carrier ∩ J.carrier).Nonempty),
    SolutionConcepts.solutionOnValue F I x →
    SolutionConcepts.solutionOnValue F J y →
    EqOn x y (I.carrier ∩ J.carrier) →
    let z := pasteCurves I.carrier x y
    SolutionConcepts.solutionOnValue F (I.union J h) z ∧
      EqOn z x I.carrier ∧ EqOn z y J.carrier

/-- For open intervals this includes C¹ regularity on the whole union. -/
def classicalPastingExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (I J : OpenTimeInterval) (x y : ℝ → E)
    (h : (I.carrier ∩ J.carrier).Nonempty),
    SolutionConcepts.classicalSolutionOnValue F I x →
    SolutionConcepts.classicalSolutionOnValue F J y →
    EqOn x y (I.carrier ∩ J.carrier) →
    SolutionConcepts.classicalSolutionOnValue F
      ⟨I.toTimeInterval.union J.toTimeInterval h, I.isOpen.union J.isOpen⟩
      (pasteCurves I.carrier x y)

/-- Left and right curves are continuous up to `s`, share the value `ξ`, and
satisfy the equation on their respective sides, with no derivative assumption
at `s`. Their actual domains can be bounded or unbounded, with either external
endpoint convention. The conclusion includes the derivative and equation at
`s` relative to the union, hence the ordinary derivative if `s` is interior.
Singleton or empty strict sides cause no exception. -/
def endpointPastingExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (L R : TimeInterval) (x y : ℝ → E) (s : ℝ) (ξ : E)
    (hsL : s ∈ L.carrier) (hsR : s ∈ R.carrier),
    L.carrier ⊆ Iic s → R.carrier ⊆ Ici s →
    ContinuousOn x L.carrier → ContinuousOn y R.carrier →
    (∀ t ∈ L.carrier, (t, x t) ∈ F.domain) →
    (∀ t ∈ R.carrier, (t, y t) ∈ F.domain) →
    x s = ξ → y s = ξ →
    (∀ t ∈ L.carrier, t < s →
      HasDerivWithinAt x (F.eval t (x t)) L.carrier t) →
    (∀ t ∈ R.carrier, s < t →
      HasDerivWithinAt y (F.eval t (y t)) R.carrier t) →
    let I := L.union R ⟨s, hsL, hsR⟩
    let z := pasteCurves L.carrier x y
    SolutionConcepts.ivpOnValue F I z s ξ ∧
      EqOn z x L.carrier ∧ EqOn z y R.carrier ∧
      HasDerivWithinAt z (F.eval s ξ) I.carrier s ∧
      (s ∈ interior I.carrier → HasDerivAt z (F.eval s ξ) s) ∧
      (∀ hI : IsOpen I.carrier,
        SolutionConcepts.classicalSolutionOnValue F ⟨I, hI⟩ z)

end Specs.D13Unified.Ch01.RestrictionPasting
