import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Independent Prop specifications for K03.03.continuity_algebra
(paper.tex:505–512). Scalars are exactly the canonical real and complex fields.
Finite families include empty families, and the metric source is unrestricted.
Continuity is the upstream unpunctured relative epsilon condition. Quotients
require nonvanishing at the base point, or are restricted to the nonzero locus.
Composition includes arbitrary metric intermediate and target spaces, with an
explicit image-in-domain condition. No accumulation or openness is required.
-/
namespace Specs.SingleVariableAnalysis.Ch03.ContinuityAlgebra

open Specs.SingleVariableAnalysis.Ch03.Continuity
open scoped BigOperators
universe u v w

def realRelativeContinuousAtLinearCombination : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (a : E) (s : Finset ι) (c : ι → ℝ) (f : ι → X → ℝ),
    (∀ i ∈ s, relativeContinuousAtValue (f i) E a) →
    relativeContinuousAtValue (fun x => ∑ i ∈ s, c i * f i x) E a

def realRelativeContinuousAtFinprod : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (a : E) (s : Finset ι) (f : ι → X → ℝ),
    (∀ i ∈ s, relativeContinuousAtValue (f i) E a) →
    relativeContinuousAtValue (fun x => ∏ i ∈ s, f i x) E a

def realRelativeContinuousAtDiv : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (a : E) (f g : X → ℝ),
    relativeContinuousAtValue f E a → relativeContinuousAtValue g E a → g a ≠ 0 →
    relativeContinuousAtValue (fun x => f x / g x) E a

def realRelativeContinuousLinearCombination : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (s : Finset ι) (c : ι → ℝ) (f : ι → X → ℝ),
    (∀ i ∈ s, relativeContinuousValue (f i) E) →
    relativeContinuousValue (fun x => ∑ i ∈ s, c i * f i x) E

def realRelativeContinuousFinprod : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (s : Finset ι) (f : ι → X → ℝ),
    (∀ i ∈ s, relativeContinuousValue (f i) E) →
    relativeContinuousValue (fun x => ∏ i ∈ s, f i x) E

def realRelativeContinuousDiv : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℝ),
    relativeContinuousValue f E → relativeContinuousValue g E →
    (∀ a ∈ E, g a ≠ 0) → relativeContinuousValue (fun x => f x / g x) E

def realRelativeContinuousDivOnNonzero : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℝ),
    relativeContinuousValue f E → relativeContinuousValue g E →
    relativeContinuousValue (fun x => f x / g x) (E ∩ {x | g x ≠ 0})

def complexRelativeContinuousAtLinearCombination : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (a : E) (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ),
    (∀ i ∈ s, relativeContinuousAtValue (f i) E a) →
    relativeContinuousAtValue (fun x => ∑ i ∈ s, c i * f i x) E a

def complexRelativeContinuousAtFinprod : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (a : E) (s : Finset ι) (f : ι → X → ℂ),
    (∀ i ∈ s, relativeContinuousAtValue (f i) E a) →
    relativeContinuousAtValue (fun x => ∏ i ∈ s, f i x) E a

def complexRelativeContinuousAtDiv : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (a : E) (f g : X → ℂ),
    relativeContinuousAtValue f E a → relativeContinuousAtValue g E a → g a ≠ 0 →
    relativeContinuousAtValue (fun x => f x / g x) E a

def complexRelativeContinuousLinearCombination : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ),
    (∀ i ∈ s, relativeContinuousValue (f i) E) →
    relativeContinuousValue (fun x => ∑ i ∈ s, c i * f i x) E

def complexRelativeContinuousFinprod : Prop :=
  ∀ {X : Type u} {ι : Type v} [MetricSpace X]
    (E : Set X) (s : Finset ι) (f : ι → X → ℂ),
    (∀ i ∈ s, relativeContinuousValue (f i) E) →
    relativeContinuousValue (fun x => ∏ i ∈ s, f i x) E

def complexRelativeContinuousDiv : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℂ),
    relativeContinuousValue f E → relativeContinuousValue g E →
    (∀ a ∈ E, g a ≠ 0) → relativeContinuousValue (fun x => f x / g x) E

def complexRelativeContinuousDivOnNonzero : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (f g : X → ℂ),
    relativeContinuousValue f E → relativeContinuousValue g E →
    relativeContinuousValue (fun x => f x / g x) (E ∩ {x | g x ≠ 0})

def relativeContinuousAtComp : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (E : Set X) (D : Set Y) (a : E) (f : X → Y) (g : Y → Z),
    Set.MapsTo f E D → relativeContinuousAtValue f E a →
    relativeContinuousAtValue g D (f a) →
    relativeContinuousAtValue (g ∘ f) E a

def relativeContinuousComp : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (E : Set X) (D : Set Y) (f : X → Y) (g : Y → Z),
    Set.MapsTo f E D → relativeContinuousValue f E → relativeContinuousValue g D →
    relativeContinuousValue (g ∘ f) E

end Specs.SingleVariableAnalysis.Ch03.ContinuityAlgebra
