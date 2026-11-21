import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SequenceLimit
import Mathlib.Topology.MetricSpace.Defs

/-!
Independent specification for paper.tex:361–376, K03.02.relative_limit.
The metric definitions specialize to the canonical real and complex spaces.
An ambient function is tested only on E, and never at the approach point.
No accumulation hypothesis is built into the definition of a limit.
-/

namespace Specs.SingleVariableAnalysis.Ch02.RelativeLimit

open scoped Topology
universe u v

def domainAccumulationType : Type (u + 1) :=
  {X : Type u} → [MetricSpace X] → Set X → X → Prop

def domainAccumulationValue : domainAccumulationType.{u} :=
  fun E a => ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, 0 < dist x a ∧ dist x a < δ

def puncturedDomainFilterType : Type (u + 1) :=
  {X : Type u} → [MetricSpace X] → Set X → X → Filter X

def puncturedDomainFilterValue : puncturedDomainFilterType.{u} :=
  fun E a => nhdsWithin a (E \ {a})

def relativePuncturedLimitType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [MetricSpace X] → [MetricSpace Y] →
    (X → Y) → Set X → X → Y → Prop

def relativePuncturedLimitValue : relativePuncturedLimitType.{u,v} :=
  fun f E a L => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ E, 0 < dist x a → dist x a < δ → dist (f x) L < ε

def domainAccumulationFilterIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (a : X),
    domainAccumulationValue E a ↔ (puncturedDomainFilterValue E a).NeBot

def relativePuncturedLimitFilterIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L : Y),
    relativePuncturedLimitValue f E a L ↔
      Filter.Tendsto f (puncturedDomainFilterValue E a) (𝓝 L)

def relativePuncturedLimitUnique : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L M : Y),
    domainAccumulationValue E a → relativePuncturedLimitValue f E a L →
      relativePuncturedLimitValue f E a M → L = M

def relativePuncturedLimitOfNotAccumulation : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X) (L : Y),
    ¬ domainAccumulationValue E a → relativePuncturedLimitValue f E a L

/-- Changing a value at a, or outside E, cannot change a punctured limit. -/
def relativePuncturedLimitCongr : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f g : X → Y) (E : Set X) (a : X) (L : Y),
    (∀ x ∈ E, x ≠ a → f x = g x) →
      (relativePuncturedLimitValue f E a L ↔ relativePuncturedLimitValue g E a L)

def realDomainAccumulationIff : Prop :=
  ∀ (E : Set ℝ) (a : ℝ), domainAccumulationValue E a ↔
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, 0 < |x - a| ∧ |x - a| < δ

def complexDomainAccumulationIff : Prop :=
  ∀ (E : Set ℂ) (a : ℂ), domainAccumulationValue E a ↔
    ∀ δ : ℝ, 0 < δ → ∃ x ∈ E, 0 < ‖x - a‖ ∧ ‖x - a‖ < δ

def realRealRelativeLimitIff : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a L : ℝ), relativePuncturedLimitValue f E a L ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, 0 < |x - a| → |x - a| < δ → |f x - L| < ε

def realComplexRelativeLimitIff : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ) (L : ℂ), relativePuncturedLimitValue f E a L ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, 0 < |x - a| → |x - a| < δ → ‖f x - L‖ < ε

def complexRealRelativeLimitIff : Prop :=
  ∀ (f : ℂ → ℝ) (E : Set ℂ) (a : ℂ) (L : ℝ), relativePuncturedLimitValue f E a L ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ → |f x - L| < ε

def complexComplexRelativeLimitIff : Prop :=
  ∀ (f : ℂ → ℂ) (E : Set ℂ) (a L : ℂ), relativePuncturedLimitValue f E a L ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, 0 < ‖x - a‖ → ‖x - a‖ < δ → ‖f x - L‖ < ε

/-- A nonempty domain suffices for the counterexample: its point is isolated. -/
def realVacuousNonuniqueness : Prop :=
  ¬ domainAccumulationValue ({0} : Set ℝ) 0 ∧
    relativePuncturedLimitValue (fun x : ℝ => x) {0} 0 0 ∧
    relativePuncturedLimitValue (fun x : ℝ => x) {0} 0 1 ∧ (0 : ℝ) ≠ 1

def complexVacuousNonuniqueness : Prop :=
  ¬ domainAccumulationValue ({0} : Set ℂ) 0 ∧
    relativePuncturedLimitValue (fun z : ℂ => z) {0} 0 0 ∧
    relativePuncturedLimitValue (fun z : ℂ => z) {0} 0 1 ∧ (0 : ℂ) ≠ 1

end Specs.SingleVariableAnalysis.Ch02.RelativeLimit
