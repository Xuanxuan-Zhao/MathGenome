import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
Independent specification of K03.02.equivalence, paper.tex:438–449.
The filter fixes the common domain and approach. Normed fields include the
canonical real and complex scalar fields. The denominator is eventually nonzero
in the definition itself, including in every comparison with Mathlib.
The explicit real-approach bridge retains the upstream nontriviality convention;
the metric punctured bridge also covers complex input domains.
-/

namespace Specs.SingleVariableAnalysis.Ch02.Equivalence

open Filter
open scoped Topology
open _root_.SingleVariableAnalysis
universe u v

def scalarEquivalentType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] →
    Filter X → (X → K) → (X → K) → Prop

def scalarEquivalentValue : scalarEquivalentType.{u,v} := fun l f g =>
  (∀ᶠ x in l, g x ≠ 0) ∧ Tendsto (fun x => f x / g x) l (𝓝 1)

def scalarEquivalentIffIsEquivalent : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarEquivalentValue l f g ↔
      (∀ᶠ x in l, g x ≠ 0) ∧ Asymptotics.IsEquivalent l f g

def scalarEquivalentIffLittleO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    (∀ᶠ x in l, g x ≠ 0) →
      (scalarEquivalentValue l f g ↔ BigO.scalarLittleOValue l (fun x => f x - g x) g)

def scalarEquivalentEventuallyNeZero : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarEquivalentValue l f g → ∀ᶠ x in l, f x ≠ 0

def scalarEquivalentIsBigO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarEquivalentValue l f g → BigO.scalarBigOValue l f g

def scalarEquivalentIsBigOReverse : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarEquivalentValue l f g → BigO.scalarBigOValue l g f

def scalarEquivalentSymm : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g : X → K),
    scalarEquivalentValue l f g → scalarEquivalentValue l g f

def scalarEquivalentTrans : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g h : X → K),
    scalarEquivalentValue l f g → scalarEquivalentValue l g h →
      scalarEquivalentValue l f h

def scalarEquivalentRefl : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f : X → K),
    (∀ᶠ x in l, f x ≠ 0) → scalarEquivalentValue l f f

def scalarEquivalentApproachIff : Prop :=
  ∀ {K : Type v} [NormedField K] (E : Set ℝ) (q : RealApproach) (f g : ℝ → K),
    OneSided.approachNontrivialValue E q →
      (scalarEquivalentValue (BigO.approachFilterValue E q) f g ↔
        OneSided.approachEventuallyValue E q (fun x => g x ≠ 0) ∧
        OneSided.finiteApproachLimitValue (fun x => f x / g x) E q 1)

def scalarEquivalentPuncturedIff : Prop :=
  ∀ {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (E : Set X) (a : X) (f g : X → K),
    scalarEquivalentValue (RelativeLimit.puncturedDomainFilterValue E a) f g ↔
      (∀ᶠ x in RelativeLimit.puncturedDomainFilterValue E a, g x ≠ 0) ∧
      RelativeLimit.relativePuncturedLimitValue (fun x => f x / g x) E a 1

end Specs.SingleVariableAnalysis.Ch02.Equivalence
