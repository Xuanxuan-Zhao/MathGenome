import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Measure.PreVariation
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Data.EReal.Operations

/-!
The domain of source maps is exactly the original sigma-algebra. Native scalar
measures use zero outside that domain as a convention, with no measurability
claim. `partitionVariation_value` is only a supremum of finite partition costs;
no additivity, boundedness, or density is included in its definition.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v w

namespace D11.Ch14.ScalarInterfaces

open D11.Ch01.MeasureDefinitions

/-- Literal scalar-valued, countably additive map on the measurable sets.
`HasSum` includes convergence, rather than merely equality to a totalized sum. -/
structure SourceScalarMeasure (α : Type u) [MeasurableSpace α]
    (K : Type v) [NormedAddCommGroup K] where
  value : MeasurableDomain α → K
  empty : value ⟨∅, MeasurableSet.empty⟩ = 0
  iUnion (E : ℕ → MeasurableDomain α)
      (hd : Pairwise fun i j => Disjoint (E i).1 (E j).1) :
    HasSum (fun n => value (E n))
      (value ⟨⋃ n, (E n).1, MeasurableSet.iUnion fun n => (E n).2⟩)

/-- A defined extended sum: positive and negative sums may not both be infinite.
The difference below is therefore never an indeterminate infinity minus infinity.
Both nonnegative sums are the usual suprema of finite partial sums. -/
def DefinedExtendedSum (f : ℕ → EReal) (a : EReal) : Prop :=
  let p := ∑' n, (f n).toENNReal
  let q := ∑' n, (-f n).toENNReal
  (p ≠ ⊤ ∨ q ≠ ⊤) ∧ a = (p : EReal) - (q : EReal)

/-- Extended signed measures omit one of the two infinities on their entire
measurable domain, and every disjoint series has a defined extended sum. -/
structure ExtendedSignedMeasure (α : Type u) [MeasurableSpace α] where
  value : MeasurableDomain α → EReal
  empty : value ⟨∅, MeasurableSet.empty⟩ = 0
  omitsInfinity : (∀ E, value E ≠ ⊤) ∨ (∀ E, value E ≠ ⊥)
  iUnion (E : ℕ → MeasurableDomain α)
      (hd : Pairwise fun i j => Disjoint (E i).1 (E j).1) :
    DefinedExtendedSum (fun n => value (E n))
      (value ⟨⋃ n, (E n).1, MeasurableSet.iUnion fun n => (E n).2⟩)

end D11.Ch14.ScalarInterfaces

namespace Specs.D11.Ch14.ScalarInterfaces

open _root_.D11.Ch01.MeasureDefinitions _root_.D11.Ch14.ScalarInterfaces

abbrev scalarMeasure_type :=
  ∀ (α : Type u) [MeasurableSpace α] (K : Type v) [NormedAddCommGroup K], Type (max u v)
abbrev scalarMeasure_value : scalarMeasure_type.{u,v} := fun α _ K _ => VectorMeasure α K
abbrev signedMeasure_type := ∀ (α : Type u) [MeasurableSpace α], Type u
abbrev signedMeasure_value : signedMeasure_type.{u} := fun α _ => SignedMeasure α
abbrev complexMeasure_type := ∀ (α : Type u) [MeasurableSpace α], Type u
abbrev complexMeasure_value : complexMeasure_type.{u} := fun α _ => ComplexMeasure α
abbrev sourceScalarMeasure_type :=
  ∀ (α : Type u) [MeasurableSpace α] (K : Type v) [NormedAddCommGroup K], Type (max u v)
abbrev sourceScalarMeasure_value : sourceScalarMeasure_type.{u,v} :=
  fun α _ K _ => SourceScalarMeasure α K
abbrev extendedSignedMeasure_type := ∀ (α : Type u) [MeasurableSpace α], Type u
abbrev extendedSignedMeasure_value : extendedSignedMeasure_type.{u} :=
  fun α _ => ExtendedSignedMeasure α
abbrev definedExtendedSum_type := (ℕ → EReal) → EReal → Prop
abbrev definedExtendedSum_value : definedExtendedSum_type := DefinedExtendedSum

abbrev sourceOfScalar_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K],
    VectorMeasure α K → SourceScalarMeasure α K
noncomputable def sourceOfScalar_value : sourceOfScalar_type.{u,v} := fun ν =>
  { value := fun E => ν E.1
    empty := ν.empty
    iUnion := fun E hd => ν.m_iUnion (fun n => (E n).2) hd }

abbrev scalarOfSource_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K],
    SourceScalarMeasure α K → VectorMeasure α K
noncomputable def scalarOfSource_value : scalarOfSource_type.{u,v} := fun p => by
  classical
  exact
    { measureOf' := fun E => if h : MeasurableSet E then p.value ⟨E, h⟩ else 0
      empty' := by simpa only [dite_eq_left MeasurableSet.empty] using p.empty
      not_measurable' := fun _ h => by simp [h]
      m_iUnion' := fun _ hE hd => by
        simpa only [dite_eq_left (MeasurableSet.iUnion hE), dite_eq_left (hE _)] using
          p.iUnion (fun n => ⟨_, hE n⟩) hd }

def scalarOfSource_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (p : SourceScalarMeasure α K) (E : Set α) (hE : MeasurableSet E),
    scalarOfSource_value p E = p.value ⟨E, hE⟩
def scalar_correspondence : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (p : SourceScalarMeasure α K),
    ∃! ν : VectorMeasure α K, ∀ (E : Set α) (hE : MeasurableSet E), ν E = p.value ⟨E,hE⟩
def scalar_roundtrip : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K), scalarOfSource_value (sourceOfScalar_value ν) = ν
def source_roundtrip : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (p : SourceScalarMeasure α K), sourceOfScalar_value (scalarOfSource_value p) = p

def scalar_countable_additivity : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    {ι : Type w} [Countable ι] (ν : VectorMeasure α K) (E : ι → Set α),
    (∀ i, MeasurableSet (E i)) → Pairwise (fun i j => Disjoint (E i) (E j)) →
    HasSum (fun i => ν (E i)) (ν (⋃ i, E i))

abbrev realPart_type := ∀ {α : Type u} [MeasurableSpace α], ComplexMeasure α → SignedMeasure α
noncomputable def realPart_value : realPart_type.{u} := ComplexMeasure.re
abbrev imaginaryPart_type := realPart_type.{u}
noncomputable def imaginaryPart_value : imaginaryPart_type.{u} := ComplexMeasure.im
abbrev complexOfParts_type :=
  ∀ {α : Type u} [MeasurableSpace α], SignedMeasure α → SignedMeasure α → ComplexMeasure α
noncomputable def complexOfParts_value : complexOfParts_type.{u} := SignedMeasure.toComplexMeasure

def components_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) (E : Set α),
    realPart_value ν E = (ν E).re ∧ imaginaryPart_value ν E = (ν E).im
def complexOfParts_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (s t : SignedMeasure α) (E : Set α),
    complexOfParts_value s t E = (s E : ℂ) + Complex.I * (t E : ℂ)
def components_roundtrip : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α),
    complexOfParts_value (realPart_value ν) (imaginaryPart_value ν) = ν
def parts_roundtrip : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (s t : SignedMeasure α),
    realPart_value (complexOfParts_value s t) = s ∧
    imaginaryPart_value (complexOfParts_value s t) = t

/-- Arbitrary positive measures embed in the extended interface, even when
 their total mass is infinite. Only the finite positive embeddings below have
 scalar (real or complex) values. -/
abbrev positiveToExtended_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → ExtendedSignedMeasure α
noncomputable def positiveToExtended_value : positiveToExtended_type.{u} := fun μ =>
  { value := fun E => (μ E.1 : EReal)
    empty := by simp
    omitsInfinity := Or.inr (fun E => EReal.coe_ennreal_ne_bot _)
    iUnion := fun E hd => by
      have hneg : ∀ n, (-(μ (E n).1 : EReal)).toENNReal = 0 := fun n =>
        EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _))
      simp only [DefinedExtendedSum, EReal.toENNReal_coe, hneg, tsum_zero,
        ne_eq, ENNReal.zero_ne_top, not_false_eq_true, or_true, EReal.coe_ennreal_zero, sub_zero, true_and]
      exact congrArg (fun t : ℝ≥0∞ => (t : EReal))
        (measure_iUnion (μ := μ) hd fun n => (E n).2) }

def positiveToExtended_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) (E : MeasurableDomain α),
    (positiveToExtended_value μ).value E = (μ E.1 : EReal)
def positiveToExtended_injective : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ η : Measure α),
    positiveToExtended_value μ = positiveToExtended_value η → μ = η

abbrev positiveToSigned_type :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ], SignedMeasure α
noncomputable def positiveToSigned_value : positiveToSigned_type.{u} := Measure.toSignedMeasure
abbrev positiveToComplex_type :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ], ComplexMeasure α
noncomputable def positiveToComplex_value : positiveToComplex_type.{u} :=
  fun μ => complexOfParts_value (positiveToSigned_value μ) 0

def positive_embeddings_apply : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (E : Set α), MeasurableSet E →
    positiveToSigned_value μ E = (μ E).toReal ∧
    positiveToComplex_value μ E = ((μ E).toReal : ℂ)
def positiveToSigned_injective : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ η : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure η],
    positiveToSigned_value μ = positiveToSigned_value η → μ = η
def positiveToComplex_injective : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ η : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure η],
    positiveToComplex_value μ = positiveToComplex_value η → μ = η

abbrev positiveSet_type :=
  ∀ {α : Type u} [MeasurableSpace α], SignedMeasure α → Set α → Prop
def positiveSet_value : positiveSet_type.{u} :=
  fun ν E => MeasurableSet E ∧ ∀ A, MeasurableSet A → A ⊆ E → 0 ≤ ν A
abbrev negativeSet_type := positiveSet_type.{u}
def negativeSet_value : negativeSet_type.{u} :=
  fun ν E => MeasurableSet E ∧ ∀ A, MeasurableSet A → A ⊆ E → ν A ≤ 0

abbrev partitionVariation_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K],
    VectorMeasure α K → Set α → ℝ≥0∞
noncomputable def partitionVariation_value : partitionVariation_type.{u,v} :=
  fun ν => preVariationFun (fun E => ENNReal.ofReal ‖ν E‖)

def partitionVariation_formula : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (E : Set α) (hE : MeasurableSet E),
    partitionVariation_value ν E =
      ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
        ∑ A ∈ P.parts, ENNReal.ofReal ‖ν A‖
def partitionVariation_null_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    (ν : VectorMeasure α K) (E : Set α), MeasurableSet E →
    (partitionVariation_value ν E = 0 ↔
      ∀ A, MeasurableSet A → A ⊆ E → ν A = 0)

/-- One common singularity definition for raw variations and positive measures.
For positive measures the supplied cost is simply the measure itself. -/
abbrev singularCosts_type :=
  ∀ {α : Type u} [MeasurableSpace α], (Set α → ℝ≥0∞) → (Set α → ℝ≥0∞) → Prop
def singularCosts_value : singularCosts_type.{u} :=
  fun v w => ∃ A, MeasurableSet A ∧ v Aᶜ = 0 ∧ w A = 0
abbrev scalarSingular_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    {L : Type w} [NormedAddCommGroup L], VectorMeasure α K → VectorMeasure α L → Prop
def scalarSingular_value : scalarSingular_type.{u,v,w} :=
  fun ν η => singularCosts_value (partitionVariation_value ν) (partitionVariation_value η)
abbrev positiveSingular_type :=
  ∀ {α : Type u} [MeasurableSpace α], Measure α → Measure α → Prop
def positiveSingular_value : positiveSingular_type.{u} :=
  fun μ η => singularCosts_value μ η
abbrev scalarPositiveSingular_type :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K],
    VectorMeasure α K → Measure α → Prop
def scalarPositiveSingular_value : scalarPositiveSingular_type.{u,v} :=
  fun ν μ => singularCosts_value (partitionVariation_value ν) μ

def singularCosts_symm : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (v w : Set α → ℝ≥0∞),
    singularCosts_value v w → singularCosts_value w v

def singularCosts_partition_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (v w : Set α → ℝ≥0∞),
    singularCosts_value v w ↔ ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧
      Disjoint A B ∧ A ∪ B = univ ∧ v B = 0 ∧ w A = 0

def scalarSingular_concentration_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    {L : Type w} [NormedAddCommGroup L] (ν : VectorMeasure α K) (η : VectorMeasure α L),
    scalarSingular_value ν η ↔ ∃ A, MeasurableSet A ∧
      (∀ B, MeasurableSet B → B ⊆ Aᶜ → ν B = 0) ∧
      (∀ B, MeasurableSet B → B ⊆ A → η B = 0)
def positiveSingular_native_iff : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ η : Measure α),
    positiveSingular_value μ η ↔ μ.MutuallySingular η

def scalarSingular_symm : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    {L : Type w} [NormedAddCommGroup L] (ν : VectorMeasure α K) (η : VectorMeasure α L),
    scalarSingular_value ν η → scalarSingular_value η ν

def positiveSingular_symm : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ η : Measure α),
    positiveSingular_value μ η → positiveSingular_value η μ

end Specs.D11.Ch14.ScalarInterfaces
