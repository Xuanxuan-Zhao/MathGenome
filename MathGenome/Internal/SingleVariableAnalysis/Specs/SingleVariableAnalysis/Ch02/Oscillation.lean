import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.RelativeLimit
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Basic.ENNReal.Real

/-!
Independent specifications for K03.02.oscillation, paper.tex:419–437.
Distances specialize to absolute values in ℝ and modulus in ℂ. All suprema and
infima live in ℝ≥0∞, so unbounded images are allowed and the empty supremum is 0.
The local definitions use all strictly positive real radii, not a fixed radius.
-/
namespace Specs.SingleVariableAnalysis.Ch02.Oscillation

open Specs.SingleVariableAnalysis.Ch02.RelativeLimit
open scoped ENNReal
universe u v

def oscillationType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [MetricSpace Y] → (X → Y) → Set X → ℝ≥0∞

noncomputable def oscillationValue : oscillationType.{u,v} :=
  fun f A => sSup {r : ℝ≥0∞ | ∃ x ∈ A, ∃ y ∈ A,
    r = ENNReal.ofReal (dist (f x) (f y))}

def localOscillationType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [MetricSpace X] → [MetricSpace Y] →
    (X → Y) → Set X → X → ℝ≥0∞

noncomputable def puncturedOscillationValue : localOscillationType.{u,v} :=
  fun f E a => ⨅ δ : {r : ℝ // 0 < r},
    oscillationValue f {x | x ∈ E ∧ 0 < dist x a ∧ dist x a < δ.val}

noncomputable def localOscillationValue : localOscillationType.{u,v} :=
  fun f E a => ⨅ δ : {r : ℝ // 0 < r},
    oscillationValue f {x | x ∈ E ∧ dist x a < δ.val}

def oscillationEmpty : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f : X → Y),
    oscillationValue f ∅ = 0

def oscillationRealFormula : Prop :=
  ∀ {X : Type u} (f : X → ℝ) (A : Set X),
    oscillationValue f A = sSup {r : ℝ≥0∞ | ∃ x ∈ A, ∃ y ∈ A,
      r = ENNReal.ofReal |f x - f y|}

def oscillationComplexFormula : Prop :=
  ∀ {X : Type u} (f : X → ℂ) (A : Set X),
    oscillationValue f A = sSup {r : ℝ≥0∞ | ∃ x ∈ A, ∃ y ∈ A,
      r = ENNReal.ofReal ‖f x - f y‖}

def puncturedOscillationZeroIffCauchy : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X),
    puncturedOscillationValue f E a = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, 0 < dist x a → dist x a < δ →
          0 < dist y a → dist y a < δ → dist (f x) (f y) < ε

def realRealPuncturedOscillationZeroIffLimit : Prop :=
  ∀ (f : ℝ → ℝ) (E : Set ℝ) (a : ℝ), domainAccumulationValue E a →
    (puncturedOscillationValue f E a = 0 ↔
      ∃ L : ℝ, relativePuncturedLimitValue f E a L)

def realComplexPuncturedOscillationZeroIffLimit : Prop :=
  ∀ (f : ℝ → ℂ) (E : Set ℝ) (a : ℝ), domainAccumulationValue E a →
    (puncturedOscillationValue f E a = 0 ↔
      ∃ L : ℂ, relativePuncturedLimitValue f E a L)

def complexRealPuncturedOscillationZeroIffLimit : Prop :=
  ∀ (f : ℂ → ℝ) (E : Set ℂ) (a : ℂ), domainAccumulationValue E a →
    (puncturedOscillationValue f E a = 0 ↔
      ∃ L : ℝ, relativePuncturedLimitValue f E a L)

def complexComplexPuncturedOscillationZeroIffLimit : Prop :=
  ∀ (f : ℂ → ℂ) (E : Set ℂ) (a : ℂ), domainAccumulationValue E a →
    (puncturedOscillationValue f E a = 0 ↔
      ∃ L : ℂ, relativePuncturedLimitValue f E a L)

def localOscillationZeroIffContinuousWithinAt : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (a : X), a ∈ E →
    (localOscillationValue f E a = 0 ↔ ContinuousWithinAt f E a)

def spikeType : Type := ℝ → ℝ

noncomputable def spikeValue : spikeType := fun x => if x = 0 then 1 else 0

def spikeValues : Prop := spikeValue 0 = 1 ∧ ∀ x : ℝ, x ≠ 0 → spikeValue x = 0

def spikePuncturedOscillation : Prop :=
  puncturedOscillationValue spikeValue Set.univ 0 = 0

def spikeLocalOscillation : Prop :=
  localOscillationValue spikeValue Set.univ 0 = 1

end Specs.SingleVariableAnalysis.Ch02.Oscillation
