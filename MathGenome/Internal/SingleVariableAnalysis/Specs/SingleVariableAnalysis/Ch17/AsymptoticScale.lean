import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Independent specification of K03.17.asymptotic_scale (paper.tex:4306–4319).
The filter records the common domain and direction of approach. Nontriviality
is part of the scale predicate. Normed fields include both manuscript scalars,
with their usual absolute value or complex modulus.

The expansion predicates record the finite remainder assertion; when speaking
of an expansion in a scale, the scale predicate is supplied separately. One
coefficient sequence is fixed before quantifying over all finite orders.
There is no infinite sum in these definitions.
-/

namespace Specs.SingleVariableAnalysis.Ch17.AsymptoticScale

open Filter
open scoped Topology BigOperators
universe u v

def isScalarAsymptoticScaleType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] →
    Filter X → (ℕ → X → K) → Prop

def isScalarAsymptoticScaleValue : isScalarAsymptoticScaleType.{u,v} := fun l φ =>
  l.NeBot ∧ (∀ j, ∀ᶠ x in l, φ j x ≠ 0) ∧
    ∀ j, Ch02.BigO.scalarLittleOValue l (φ (j + 1)) (φ j)

def asymptoticPartialSumType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] →
    (ℕ → X → K) → (ℕ → K) → ℕ → X → K

def asymptoticPartialSumValue : asymptoticPartialSumType.{u,v} := fun φ a m x =>
  ∑ j ∈ Finset.range (m + 1), a j * φ j x

def hasScalarExpansionThroughType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] →
    Filter X → (ℕ → X → K) → (ℕ → K) → (X → K) → ℕ → Prop

def hasScalarExpansionThroughValue : hasScalarExpansionThroughType.{u,v} :=
  fun l φ a f m => Ch02.BigO.scalarLittleOValue l
    (fun x => f x - asymptoticPartialSumValue φ a m x) (φ m)

def hasScalarAsymptoticExpansionType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {K : Type v} → [NormedField K] →
    Filter X → (ℕ → X → K) → (ℕ → K) → (X → K) → Prop

def hasScalarAsymptoticExpansionValue : hasScalarAsymptoticExpansionType.{u,v} :=
  fun l φ a f => ∀ m, hasScalarExpansionThroughValue l φ a f m

def isScalarAsymptoticScaleIff : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (φ : ℕ → X → K),
    isScalarAsymptoticScaleValue l φ ↔
      l.NeBot ∧ (∀ j, ∀ᶠ x in l, φ j x ≠ 0) ∧
        ∀ j, Ch02.BigO.scalarLittleOValue l (φ (j + 1)) (φ j)

def isScalarAsymptoticScaleNeBot : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (φ : ℕ → X → K),
    isScalarAsymptoticScaleValue l φ → l.NeBot

def isScalarAsymptoticScaleEventuallyNeZero : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (φ : ℕ → X → K),
    isScalarAsymptoticScaleValue l φ → ∀ j, ∀ᶠ x in l, φ j x ≠ 0

def isScalarAsymptoticScaleLittleO : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (φ : ℕ → X → K),
    isScalarAsymptoticScaleValue l φ → ∀ {j k : ℕ}, j < k →
      Ch02.BigO.scalarLittleOValue l (φ k) (φ j)

def isScalarAsymptoticScaleRatioTendsto : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (φ : ℕ → X → K),
    isScalarAsymptoticScaleValue l φ → ∀ {j k : ℕ}, j < k →
      Tendsto (fun x => φ k x / φ j x) l (𝓝 0)

def asymptoticPartialSumZero : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K]
    (φ : ℕ → X → K) (a : ℕ → K) (x : X),
    asymptoticPartialSumValue φ a 0 x = a 0 * φ 0 x

def asymptoticPartialSumSucc : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K]
    (φ : ℕ → X → K) (a : ℕ → K) (m : ℕ) (x : X),
    asymptoticPartialSumValue φ a (m + 1) x =
      asymptoticPartialSumValue φ a m x + a (m + 1) * φ (m + 1) x

def hasScalarExpansionThroughIff : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) (a : ℕ → K) (f : X → K) (m : ℕ),
    hasScalarExpansionThroughValue l φ a f m ↔
      Ch02.BigO.scalarLittleOValue l
        (fun x => f x - ∑ j ∈ Finset.range (m + 1), a j * φ j x) (φ m)

def hasScalarAsymptoticExpansionIff : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) (a : ℕ → K) (f : X → K),
    hasScalarAsymptoticExpansionValue l φ a f ↔
      ∀ m, hasScalarExpansionThroughValue l φ a f m

def hasScalarAsymptoticExpansionThrough : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) (a : ℕ → K) (f : X → K),
    hasScalarAsymptoticExpansionValue l φ a f →
      ∀ m, hasScalarExpansionThroughValue l φ a f m

end Specs.SingleVariableAnalysis.Ch17.AsymptoticScale
