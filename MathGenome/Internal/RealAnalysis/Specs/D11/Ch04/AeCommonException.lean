import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Independent statements for paper.tex:1333–1357. Ordinary a.e. uses an
exceptional set in the original sigma-algebra. No function measurability,
completeness, finiteness or sigma-finiteness is assumed. The equality results
are stated for arbitrary codomains; in particular they apply to both scalar
fields. Unary, binary and countable-tuple operations cover scalar operations
wherever defined. The limit statement applies in any Hausdorff target, hence
in particular to real and complex pointwise limits.
-/

open Set MeasureTheory Filter
open scoped Topology

universe u v w z

namespace Specs.D11.Ch04.AeCommonException

open _root_.Specs.D11.Ch01.MeasureDefinitions

def almostEverywhere_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → (α → Prop) → Prop

def almostEverywhere_value : almostEverywhere_type.{u} := fun μ P =>
  ∃ N : Set _, measurableNull_value μ N ∧ ∀ x, x ∉ N → P x

def aeEq_type :=
  ∀ {α : Type u} {β : Type v} [MeasurableSpace α],
    Measure α → (α → β) → (α → β) → Prop

def aeEq_value : aeEq_type.{u, v} := fun μ f g =>
  almostEverywhere_value μ (fun x => f x = g x)

def almostEverywhere_iff_native : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (P : α → Prop),
    almostEverywhere_value μ P ↔ ∀ᵐ x ∂μ, P x

def almostEverywhere_iff_negligible : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (P : α → Prop),
    almostEverywhere_value μ P ↔ negligible_value μ {x | ¬ P x}

def almostEverywhere_of_forall : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (P : α → Prop),
    (∀ x, P x) → almostEverywhere_value μ P

def almostEverywhere_mono : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (P Q : α → Prop),
    almostEverywhere_value μ P → (∀ x, P x → Q x) → almostEverywhere_value μ Q

def aeEq_iff_native : Prop :=
  ∀ {α : Type u} {β : Type v} [MeasurableSpace α] (μ : Measure α) (f g : α → β),
    aeEq_value μ f g ↔ f =ᵐ[μ] g

def aeEq_refl : Prop :=
  ∀ {α : Type u} {β : Type v} [MeasurableSpace α] (μ : Measure α) (f : α → β),
    aeEq_value μ f f

def aeEq_symm : Prop :=
  ∀ {α : Type u} {β : Type v} [MeasurableSpace α] (μ : Measure α) (f g : α → β),
    aeEq_value μ f g → aeEq_value μ g f

def aeEq_trans : Prop :=
  ∀ {α : Type u} {β : Type v} [MeasurableSpace α] (μ : Measure α) (f g h : α → β),
    aeEq_value μ f g → aeEq_value μ g h → aeEq_value μ f h

def aeEq_equivalence : Prop :=
  ∀ {α : Type u} {β : Type v} [MeasurableSpace α] (μ : Measure α),
    Equivalence (aeEq_value (β := β) μ)

def common_exception : Prop :=
  ∀ {α : Type u} {ι : Type v} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (P : ι → α → Prop),
    (∀ i, almostEverywhere_value μ (P i)) →
    ∃ N : Set α, measurableNull_value μ N ∧ ∀ x, x ∉ N → ∀ i, P i x

def almostEverywhere_all_iff : Prop :=
  ∀ {α : Type u} {ι : Type v} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (P : ι → α → Prop),
    almostEverywhere_value μ (fun x => ∀ i, P i x) ↔
      ∀ i, almostEverywhere_value μ (P i)

def aeEq_unary : Prop :=
  ∀ {α : Type u} {β : Type v} {γ : Type w} [MeasurableSpace α]
    (μ : Measure α) (f g : α → β) (φ : β → γ),
    aeEq_value μ f g → aeEq_value μ (fun x => φ (f x)) (fun x => φ (g x))

def aeEq_binary : Prop :=
  ∀ {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} [MeasurableSpace α]
    (μ : Measure α) (f g : α → β) (h k : α → γ) (φ : β → γ → δ),
    aeEq_value μ f g → aeEq_value μ h k →
      aeEq_value μ (fun x => φ (f x) (h x)) (fun x => φ (g x) (k x))

def aeEq_countable_operation : Prop :=
  ∀ {α : Type u} {ι : Type v} {β : Type w} {γ : Type z}
    [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (f g : ι → α → β) (φ : (ι → β) → γ),
    (∀ i, aeEq_value μ (f i) (g i)) →
    aeEq_value μ (fun x => φ (fun i => f i x)) (fun x => φ (fun i => g i x))

def aeEq_pointwise_limit : Prop :=
  ∀ {α : Type u} {β : Type v} [MeasurableSpace α] [TopologicalSpace β] [T2Space β]
    (μ : Measure α) (f g : ℕ → α → β) (F G : α → β),
    (∀ n, aeEq_value μ (f n) (g n)) →
    almostEverywhere_value μ (fun x => Tendsto (fun n => f n x) atTop (𝓝 (F x))) →
    almostEverywhere_value μ (fun x => Tendsto (fun n => g n x) atTop (𝓝 (G x))) →
    aeEq_value μ F G

end Specs.D11.Ch04.AeCommonException
