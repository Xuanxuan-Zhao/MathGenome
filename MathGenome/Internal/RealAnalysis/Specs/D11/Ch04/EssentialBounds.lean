import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.EssSup

/-!
Independent statements for paper.tex:1408–1439. The finite scalar absolute
value is represented by the norm, which is absolute value on `ℝ` and modulus
on `ℂ`. The statements hold more generally for every normed additive
commutative group and do not need measurability of the functions. In
particular they cover all measurable finite scalar functions in the source.

Admissible bounds are finite nonnegative real numbers. Their infimum is
taken after embedding them in `ℝ≥0∞`, so an empty class has infimum infinity.
The a.e. predicate is the upstream ordinary measurable-null-envelope
predicate, with no finiteness, completeness or sigma-finiteness assumptions.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

universe u v

namespace Specs.D11.Ch04.EssentialBounds

open Specs.D11.Ch04.AeCommonException

def admissibleBounds_type :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E],
    Measure α → (α → E) → Set ℝ≥0

def admissibleBounds_value : admissibleBounds_type.{u, v} := fun μ f =>
  {M | almostEverywhere_value μ (fun x => ‖f x‖ ≤ (M : ℝ))}

def essentialSupNorm_type :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E],
    Measure α → (α → E) → ℝ≥0∞

noncomputable def essentialSupNorm_value : essentialSupNorm_type.{u, v} := fun μ f =>
  sInf ((fun M : ℝ≥0 => (M : ℝ≥0∞)) '' admissibleBounds_value μ f)

def essentiallyBounded_type :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E],
    Measure α → (α → E) → Prop

def essentiallyBounded_value : essentiallyBounded_type.{u, v} := fun μ f =>
  essentialSupNorm_value μ f < ∞

def admissibleBounds_congr : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f g : α → E),
    aeEq_value μ f g → admissibleBounds_value μ f = admissibleBounds_value μ g

def essentialSupNorm_congr : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f g : α → E),
    aeEq_value μ f g → essentialSupNorm_value μ f = essentialSupNorm_value μ g

def essentialSupNorm_empty : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E),
    admissibleBounds_value μ f = ∅ → essentialSupNorm_value μ f = ∞

def essentialSupNorm_eq_native : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E),
    essentialSupNorm_value μ f = essSup (fun x => ‖f x‖ₑ) μ

def essential_bound_attained : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E),
    essentialSupNorm_value μ f < ∞ →
    almostEverywhere_value μ (fun x => ‖f x‖ ≤ (essentialSupNorm_value μ f).toReal)

def essentialSupNorm_eq_zero_iff : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E),
    essentialSupNorm_value μ f = 0 ↔ aeEq_value μ f (fun _ => 0)

def essentialSupNorm_mono : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f g : α → E),
    almostEverywhere_value μ (fun x => ‖f x‖ ≤ ‖g x‖) →
    essentialSupNorm_value μ f ≤ essentialSupNorm_value μ g

def essentialSupNorm_le_iff : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E) (M : ℝ≥0),
    essentialSupNorm_value μ f ≤ (M : ℝ≥0∞) ↔ M ∈ admissibleBounds_value μ f

def essentiallyBounded_iff : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E),
    essentiallyBounded_value μ f ↔ (admissibleBounds_value μ f).Nonempty

def essentialSupNorm_zero_measure : Prop :=
  ∀ {α : Type u} {E : Type v} [MeasurableSpace α] [NormedAddCommGroup E]
    (f : α → E), essentialSupNorm_value (0 : Measure α) f = 0

end Specs.D11.Ch04.EssentialBounds
