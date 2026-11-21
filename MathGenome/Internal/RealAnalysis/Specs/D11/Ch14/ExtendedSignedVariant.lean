import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarInterfaces
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Extended signed measures retain the original measurable domain and may have
infinite variation. A Jordan pair is a mutually singular positive difference
with at least one finite total mass. Selection uses classical epsilon; its
existence and all properties of the selection are separate theorem obligations. -/

open Set MeasureTheory
open scoped ENNReal symmDiff
universe u
noncomputable section
namespace D11.Ch14.ExtendedSignedVariant
open D11.Ch01.MeasureDefinitions D11.Ch14.ScalarInterfaces

def PositiveSet {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (P : Set α) : Prop :=
  MeasurableSet P ∧ ∀ (A : Set α) (hA : MeasurableSet A), A ⊆ P → 0 ≤ ν.value ⟨A,hA⟩

def NegativeSet {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (N : Set α) : Prop :=
  MeasurableSet N ∧ ∀ (A : Set α) (hA : MeasurableSet A), A ⊆ N → ν.value ⟨A,hA⟩ ≤ 0

def IsJordanPair {α : Type u} [MeasurableSpace α]
    (ν : ExtendedSignedMeasure α) (μ η : Measure α) : Prop :=
  μ.MutuallySingular η ∧ (μ univ ≠ ⊤ ∨ η univ ≠ ⊤) ∧
    ∀ (E : Set α) (hE : MeasurableSet E),
      ν.value ⟨E,hE⟩ = (μ E : EReal) - (η E : EReal)

/-- Finite measurable partitions, including empty pieces and the empty partition. -/
def PartitionOf {α : Type u} [MeasurableSpace α] (E : Set α)
    {n : ℕ} (F : Fin n → MeasurableDomain α) : Prop :=
  Pairwise (fun i j => Disjoint (F i).1 (F j).1) ∧ (⋃ i, (F i).1) = E

end D11.Ch14.ExtendedSignedVariant

namespace Specs.D11.Ch14.ExtendedSignedVariant
open _root_.D11.Ch01.MeasureDefinitions _root_.D11.Ch14.ScalarInterfaces
open _root_.D11.Ch14.ExtendedSignedVariant

abbrev selectedPair_type := ∀ {α : Type u} [MeasurableSpace α],
  ExtendedSignedMeasure α → Measure α × Measure α
def selectedPair_value : selectedPair_type.{u} := fun ν =>
  Classical.epsilon (fun p : Measure _ × Measure _ => IsJordanPair ν p.1 p.2)
abbrev positivePart_type := ∀ {α : Type u} [MeasurableSpace α],
  ExtendedSignedMeasure α → Measure α
def positivePart_value : positivePart_type.{u} := fun ν => (selectedPair_value ν).1
def negativePart_value : positivePart_type.{u} := fun ν => (selectedPair_value ν).2
def variation_value : positivePart_type.{u} := fun ν => positivePart_value ν + negativePart_value ν
abbrev partitionVariation_type := ∀ {α : Type u} [MeasurableSpace α],
  ExtendedSignedMeasure α → Set α → ℝ≥0∞
def partitionVariation_value : partitionVariation_type.{u} := fun ν E =>
  ⨆ (n : ℕ) (F : Fin n → MeasurableDomain _) (_ : PartitionOf E F),
    ∑ i, ((ν.value (F i)).toENNReal + (-ν.value (F i)).toENNReal)

abbrev scalarIntegrable_type := ∀ {α : Type u} [MeasurableSpace α] {𝕜 : Type}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  ExtendedSignedMeasure α → (α → 𝕜) → Prop
def scalarIntegrable_value : scalarIntegrable_type.{u} := fun ν f =>
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value (variation_value ν) f
abbrev scalarIntegral_type := ∀ {α : Type u} [MeasurableSpace α] {𝕜 : Type}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (ν : ExtendedSignedMeasure α) (f : α → 𝕜), scalarIntegrable_value ν f → 𝕜
def scalarIntegral_value : scalarIntegral_type.{u} := fun ν f _ =>
  (∫ x, f x ∂positivePart_value ν) - (∫ x, f x ∂negativePart_value ν)
abbrev isSigmaFinite_type := ∀ {α : Type u} [MeasurableSpace α],
  ExtendedSignedMeasure α → Prop
def isSigmaFinite_value : isSigmaFinite_type.{u} := fun ν => SigmaFinite (variation_value ν)

def hahn_exists : Prop := ∀ {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α),
  ∃ P : Set α, PositiveSet ν P ∧ NegativeSet ν Pᶜ

def jordan_exists : Prop := ∀ {α : Type u} [MeasurableSpace α] (ν : ExtendedSignedMeasure α),
  ∃ μ η : Measure α, IsJordanPair ν μ η

def jordan_decomposition : Prop := ∀ {α : Type u} [MeasurableSpace α]
  (ν : ExtendedSignedMeasure α), IsJordanPair ν (positivePart_value ν) (negativePart_value ν)

def jordan_unique : Prop := ∀ {α : Type u} [MeasurableSpace α]
  (ν : ExtendedSignedMeasure α) (μ η : Measure α), IsJordanPair ν μ η →
    μ = positivePart_value ν ∧ η = negativePart_value ν

def jordan_hahn_formula : Prop := ∀ {α : Type u} [MeasurableSpace α]
  (ν : ExtendedSignedMeasure α) (P : Set α)
  (hP : PositiveSet ν P) (hN : NegativeSet ν Pᶜ)
  (E : Set α) (hE : MeasurableSet E),
  positivePart_value ν E = (ν.value ⟨E ∩ P,hE.inter hP.1⟩).toENNReal ∧
  negativePart_value ν E = (-ν.value ⟨E ∩ Pᶜ,hE.inter hN.1⟩).toENNReal

def partition_variation_identity : Prop := ∀ {α : Type u} [MeasurableSpace α]
  (ν : ExtendedSignedMeasure α) (E : Set α), MeasurableSet E →
  partitionVariation_value ν E = variation_value ν E

def hahn_unique : Prop := ∀ {α : Type u} [MeasurableSpace α]
  (ν : ExtendedSignedMeasure α) (P Q : Set α)
  (hP : PositiveSet ν P) (hN : NegativeSet ν Pᶜ)
  (hQ : PositiveSet ν Q) (hM : NegativeSet ν Qᶜ),
  (∀ (A : Set α) (hA : MeasurableSet A), A ⊆ P ∆ Q → ν.value ⟨A,hA⟩ = 0) ∧
    variation_value ν (P ∆ Q) = 0

def scalarIntegrable_iff : Prop := ∀ {α : Type u} [MeasurableSpace α] {𝕜 : Type}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (ν : ExtendedSignedMeasure α) (f : α → 𝕜),
  scalarIntegrable_value ν f ↔ Measurable f ∧ Integrable f (variation_value ν)

def parts_integrable : Prop := ∀ {α : Type u} [MeasurableSpace α] {𝕜 : Type}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (ν : ExtendedSignedMeasure α) (f : α → 𝕜), scalarIntegrable_value ν f →
  Integrable f (positivePart_value ν) ∧ Integrable f (negativePart_value ν)

def scalarIntegral_add : Prop := ∀ {α : Type u} [MeasurableSpace α] {𝕜 : Type}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (ν : ExtendedSignedMeasure α) (f g : α → 𝕜)
  (hf : scalarIntegrable_value ν f) (hg : scalarIntegrable_value ν g)
  (hfg : scalarIntegrable_value ν (fun x => f x + g x)),
  scalarIntegral_value ν (fun x => f x + g x) hfg =
    scalarIntegral_value ν f hf + scalarIntegral_value ν g hg

def scalarIntegral_const_mul : Prop := ∀ {α : Type u} [MeasurableSpace α] {𝕜 : Type}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (ν : ExtendedSignedMeasure α) (c : 𝕜) (f : α → 𝕜)
  (hf : scalarIntegrable_value ν f) (hcf : scalarIntegrable_value ν (fun x => c * f x)),
  scalarIntegral_value ν (fun x => c * f x) hcf = c * scalarIntegral_value ν f hf

def sigmaFinite_iff : Prop := ∀ {α : Type u} [MeasurableSpace α]
  (ν : ExtendedSignedMeasure α), isSigmaFinite_value ν ↔ SigmaFinite (variation_value ν)

end Specs.D11.Ch14.ExtendedSignedVariant
