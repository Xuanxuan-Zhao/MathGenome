import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Equivalence

/-!
Independent specification of K03.02.equivalence_replacement,
paper.tex:457–463. One filter fixes the common domain and approach. The
upstream ratio definition includes eventual nonvanishing; the quotient law
needs no additional assumptions on the functions. Normed fields cover both
real and complex scalars. The counterexample uses all nonzero real approaches
to zero, rather than a selected sequence or a one-sided approach.
-/

namespace Specs.SingleVariableAnalysis.Ch02.EquivalenceReplacement

open Filter
universe u v

def scalarEquivalentMul : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f F g G : X → K),
    Equivalence.scalarEquivalentValue l f F →
    Equivalence.scalarEquivalentValue l g G →
    Equivalence.scalarEquivalentValue l (fun x => f x * g x) (fun x => F x * G x)

def scalarEquivalentDiv : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f F g G : X → K),
    Equivalence.scalarEquivalentValue l f F →
    Equivalence.scalarEquivalentValue l g G →
    (∀ᶠ x in l, g x ≠ 0 ∧ G x ≠ 0) ∧
    Equivalence.scalarEquivalentValue l (fun x => f x / g x) (fun x => F x / G x)

def realAddSqEquivalentSelf : Prop :=
  Equivalence.scalarEquivalentValue
    (RelativeLimit.puncturedDomainFilterValue (Set.univ : Set ℝ) 0)
    (fun x : ℝ => x + x ^ 2) (fun x => x)

def realSelfEquivalentAtZero : Prop :=
  Equivalence.scalarEquivalentValue
    (RelativeLimit.puncturedDomainFilterValue (Set.univ : Set ℝ) 0)
    (fun x : ℝ => x) (fun x => x)

def realSubtractionReplacementCounterexample : Prop :=
  (∀ x : ℝ, (x + x ^ 2) - x = x ^ 2 ∧ x - x = 0) ∧
    (¬ Equivalence.scalarEquivalentValue
      (RelativeLimit.puncturedDomainFilterValue (Set.univ : Set ℝ) 0)
      (fun x : ℝ => x ^ 2) (fun _ => 0)) ∧
    (¬ Equivalence.scalarEquivalentValue
      (RelativeLimit.puncturedDomainFilterValue (Set.univ : Set ℝ) 0)
      (fun x : ℝ => (x + x ^ 2) - x) (fun x => x - x))

end Specs.SingleVariableAnalysis.Ch02.EquivalenceReplacement
