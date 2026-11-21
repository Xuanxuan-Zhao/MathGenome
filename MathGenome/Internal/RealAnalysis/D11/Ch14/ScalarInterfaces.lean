import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarInterfaces

/-! Scalar-measure source/native equivalences and their common raw variation.
No total-variation measure theorem is assumed by these interfaces. -/

open Set MeasureTheory
open scoped ENNReal

universe u v w

namespace D11.Ch14.ScalarInterfaces

abbrev scalarMeasure (α : Type u) [MeasurableSpace α] (K : Type v)
    [NormedAddCommGroup K] := VectorMeasure α K
abbrev signedMeasure (α : Type u) [MeasurableSpace α] := SignedMeasure α
abbrev complexMeasure (α : Type u) [MeasurableSpace α] := ComplexMeasure α
abbrev sourceScalarMeasure (α : Type u) [MeasurableSpace α] (K : Type v)
    [NormedAddCommGroup K] := SourceScalarMeasure α K
abbrev extendedSignedMeasure (α : Type u) [MeasurableSpace α] := ExtendedSignedMeasure α
abbrev definedExtendedSum := DefinedExtendedSum

noncomputable def sourceOfScalar {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (ν : VectorMeasure α K) : SourceScalarMeasure α K where
  value E := ν E.1
  empty := ν.empty
  iUnion E hd := ν.m_iUnion (fun n => (E n).2) hd

noncomputable def scalarOfSource {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (p : SourceScalarMeasure α K) : VectorMeasure α K := by
  classical
  exact
    { measureOf' := fun E => if h : MeasurableSet E then p.value ⟨E, h⟩ else 0
      empty' := by simpa only [dite_eq_left MeasurableSet.empty] using p.empty
      not_measurable' := fun _ h => by simp [h]
      m_iUnion' := fun _ hE hd => by
        simpa only [dite_eq_left (MeasurableSet.iUnion hE), dite_eq_left (hE _)] using
          p.iUnion (fun n => ⟨_, hE n⟩) hd }

theorem scalarOfSource_apply {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (p : SourceScalarMeasure α K) (E : Set α)
    (hE : MeasurableSet E) : scalarOfSource p E = p.value ⟨E,hE⟩ := by
  classical
  exact dite_eq_left hE

@[ext] theorem SourceScalarMeasure.ext {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] {p q : SourceScalarMeasure α K}
    (h : ∀ E, p.value E = q.value E) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

theorem scalar_correspondence {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (p : SourceScalarMeasure α K) :
    ∃! ν : VectorMeasure α K, ∀ (E : Set α) (hE : MeasurableSet E), ν E = p.value ⟨E,hE⟩ := by
  refine ⟨scalarOfSource p, scalarOfSource_apply p, ?_⟩
  intro ν hν
  exact VectorMeasure.ext fun E hE => (hν E hE).trans (scalarOfSource_apply p E hE).symm

theorem scalar_roundtrip {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (ν : VectorMeasure α K) :
    scalarOfSource (sourceOfScalar ν) = ν :=
  VectorMeasure.ext fun E hE => scalarOfSource_apply _ E hE

theorem source_roundtrip {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (p : SourceScalarMeasure α K) :
    sourceOfScalar (scalarOfSource p) = p :=
  SourceScalarMeasure.ext fun E => scalarOfSource_apply p E.1 E.2

theorem scalar_countable_additivity {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] {ι : Type w} [Countable ι] (ν : VectorMeasure α K)
    (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    HasSum (fun i => ν (E i)) (ν (⋃ i, E i)) :=
  VectorMeasure.hasSum_of_disjoint_iUnion hE hd

noncomputable def realPart {α : Type u} [MeasurableSpace α] :
    ComplexMeasure α → SignedMeasure α := ComplexMeasure.re
noncomputable def imaginaryPart {α : Type u} [MeasurableSpace α] :
    ComplexMeasure α → SignedMeasure α := ComplexMeasure.im
noncomputable def complexOfParts {α : Type u} [MeasurableSpace α] :
    SignedMeasure α → SignedMeasure α → ComplexMeasure α := SignedMeasure.toComplexMeasure

theorem components_apply {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α)
    (E : Set α) : realPart ν E = (ν E).re ∧ imaginaryPart ν E = (ν E).im := ⟨rfl,rfl⟩

theorem complexOfParts_apply {α : Type u} [MeasurableSpace α] (s t : SignedMeasure α)
    (E : Set α) : complexOfParts s t E = (s E : ℂ) + Complex.I * (t E : ℂ) := by
  apply Complex.ext <;> simp [complexOfParts, SignedMeasure.toComplexMeasure_apply]

theorem components_roundtrip {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) :
    complexOfParts (realPart ν) (imaginaryPart ν) = ν := rfl

theorem parts_roundtrip {α : Type u} [MeasurableSpace α] (s t : SignedMeasure α) :
    realPart (complexOfParts s t) = s ∧ imaginaryPart (complexOfParts s t) = t := ⟨rfl,rfl⟩

/-- This positive embedding admits infinite total mass. -/
noncomputable def positiveToExtended {α : Type u} [MeasurableSpace α]
    (μ : Measure α) : ExtendedSignedMeasure α where
  value E := (μ E.1 : EReal)
  empty := by simp
  omitsInfinity := Or.inr (fun E => EReal.coe_ennreal_ne_bot _)
  iUnion E hd := by
    have hneg : ∀ n, (-(μ (E n).1 : EReal)).toENNReal = 0 := fun n =>
      EReal.toENNReal_of_nonpos (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _))
    simp only [DefinedExtendedSum, EReal.toENNReal_coe, hneg, tsum_zero,
      ne_eq, ENNReal.zero_ne_top, not_false_eq_true, or_true, EReal.coe_ennreal_zero, sub_zero, true_and]
    exact congrArg (fun t : ℝ≥0∞ => (t : EReal))
      (measure_iUnion (μ := μ) hd fun n => (E n).2)

theorem positiveToExtended_apply {α : Type u} [MeasurableSpace α] (μ : Measure α)
    (E : D11.Ch01.MeasureDefinitions.MeasurableDomain α) :
    (positiveToExtended μ).value E = (μ E.1 : EReal) := rfl

theorem positiveToExtended_injective {α : Type u} [MeasurableSpace α] (μ η : Measure α)
    (h : positiveToExtended μ = positiveToExtended η) : μ = η := by
  apply Measure.ext
  intro E hE
  apply EReal.coe_ennreal_injective
  exact congrArg (fun p => p.value ⟨E,hE⟩) h

noncomputable def positiveToSigned {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] : SignedMeasure α := μ.toSignedMeasure
noncomputable def positiveToComplex {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] : ComplexMeasure α := complexOfParts (positiveToSigned μ) 0

theorem positive_embeddings_apply {α : Type u} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (E : Set α) (hE : MeasurableSet E) :
    positiveToSigned μ E = (μ E).toReal ∧
    positiveToComplex μ E = ((μ E).toReal : ℂ) := by
  constructor
  · exact Measure.toSignedMeasure_apply_measurable hE
  · rw [positiveToComplex, complexOfParts_apply]
    simp [positiveToSigned, Measure.toSignedMeasure_apply_measurable hE, measureReal_def]

theorem positiveToSigned_injective {α : Type u} [MeasurableSpace α] (μ η : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : positiveToSigned μ = positiveToSigned η) : μ = η :=
  Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp h

theorem positiveToComplex_injective {α : Type u} [MeasurableSpace α] (μ η : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : positiveToComplex μ = positiveToComplex η) : μ = η := by
  apply positiveToSigned_injective μ η
  exact congrArg realPart h

def positiveSet {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) (E : Set α) : Prop :=
  MeasurableSet E ∧ ∀ A, MeasurableSet A → A ⊆ E → 0 ≤ ν A

def negativeSet {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) (E : Set α) : Prop :=
  MeasurableSet E ∧ ∀ A, MeasurableSet A → A ⊆ E → ν A ≤ 0

/-- The raw partition supremum. Empty pieces can be deleted at zero cost;
`Finpartition` records the remaining finite disjoint measurable pieces. -/
noncomputable def partitionVariation {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (ν : VectorMeasure α K) : Set α → ℝ≥0∞ :=
  preVariationFun (fun E => ENNReal.ofReal ‖ν E‖)

theorem partitionVariation_formula {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (ν : VectorMeasure α K) (E : Set α) (hE : MeasurableSet E) :
    partitionVariation ν E =
      ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
        ∑ A ∈ P.parts, ENNReal.ofReal ‖ν A‖ :=
  preVariationFun_apply _ hE

/-- A one-piece partition supplies this bound, without countable additivity of
variation or any bounded-variation premise. -/
theorem norm_le_partitionVariation {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (ν : VectorMeasure α K) (E : Set α) (hE : MeasurableSet E) :
    ENNReal.ofReal ‖ν E‖ ≤ partitionVariation ν E := by
  classical
  by_cases h : (⟨E,hE⟩ : Subtype MeasurableSet) = ⊥
  · have he : E = ∅ := congrArg Subtype.val h
    simp [he, partitionVariation, preVariation.empty]
  · have hP := preVariation.sum_le (fun E => ENNReal.ofReal ‖ν E‖) hE
      (Finpartition.indiscrete h)
    simpa [Finpartition.indiscrete, partitionVariation] using hP

theorem partitionVariation_null_iff {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (ν : VectorMeasure α K) (E : Set α) (hE : MeasurableSet E) :
    partitionVariation ν E = 0 ↔ ∀ A, MeasurableSet A → A ⊆ E → ν A = 0 := by
  classical
  constructor
  · intro h A hA hAE
    have hle : ENNReal.ofReal ‖ν A‖ ≤ 0 := calc
      ENNReal.ofReal ‖ν A‖ ≤ partitionVariation ν A := norm_le_partitionVariation ν A hA
      _ ≤ partitionVariation ν E := preVariation.mono _ hE hAE
      _ = 0 := h
    have hz : ‖ν A‖ = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp hle))
      (norm_nonneg _)
    exact norm_eq_zero.mp hz
  · intro h
    rw [partitionVariation_formula ν E hE]
    apply le_antisymm _ (bot_le)
    refine iSup_le fun P => ?_
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro A hA
    simp [h A.1 A.2 (P.le hA)]

def singularCosts {α : Type u} [MeasurableSpace α]
    (v w : Set α → ℝ≥0∞) : Prop :=
  ∃ A, MeasurableSet A ∧ v Aᶜ = 0 ∧ w A = 0

def scalarSingular {α : Type u} [MeasurableSpace α] {K : Type v} [NormedAddCommGroup K]
    {L : Type w} [NormedAddCommGroup L] (ν : VectorMeasure α K) (η : VectorMeasure α L) : Prop :=
  singularCosts (partitionVariation ν) (partitionVariation η)

def positiveSingular {α : Type u} [MeasurableSpace α] (μ η : Measure α) : Prop :=
  singularCosts μ η

def scalarPositiveSingular {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α) : Prop :=
  singularCosts (partitionVariation ν) μ

theorem singularCosts_symm {α : Type u} [MeasurableSpace α] (v w : Set α → ℝ≥0∞)
    (h : singularCosts v w) : singularCosts w v := by
  obtain ⟨A,hA,hv,hw⟩ := h
  exact ⟨Aᶜ,hA.compl,by simpa using hw,hv⟩

theorem singularCosts_partition_iff {α : Type u} [MeasurableSpace α]
    (v w : Set α → ℝ≥0∞) :
    singularCosts v w ↔ ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧
      Disjoint A B ∧ A ∪ B = univ ∧ v B = 0 ∧ w A = 0 := by
  constructor
  · rintro ⟨A,hA,hv,hw⟩
    exact ⟨A,Aᶜ,hA,hA.compl,disjoint_compl_right,union_compl_self A,hv,hw⟩
  · rintro ⟨A,B,hA,hB,hd,hu,hv,hw⟩
    have hBA : B = Aᶜ := by
      ext x
      constructor
      · intro hxB hxA
        exact Set.disjoint_left.mp hd hxA hxB
      · intro hxA
        have hx : x ∈ A ∪ B := by rw [hu]; trivial
        exact hx.resolve_left hxA
    exact ⟨A,hA,by simpa [← hBA] using hv,hw⟩

theorem scalarSingular_concentration_iff {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] {L : Type w} [NormedAddCommGroup L]
    (ν : VectorMeasure α K) (η : VectorMeasure α L) :
    scalarSingular ν η ↔ ∃ A, MeasurableSet A ∧
      (∀ B, MeasurableSet B → B ⊆ Aᶜ → ν B = 0) ∧
      (∀ B, MeasurableSet B → B ⊆ A → η B = 0) := by
  constructor
  · rintro ⟨A,hA,hν,hη⟩
    exact ⟨A,hA,(partitionVariation_null_iff ν Aᶜ hA.compl).mp hν,
      (partitionVariation_null_iff η A hA).mp hη⟩
  · rintro ⟨A,hA,hν,hη⟩
    exact ⟨A,hA,(partitionVariation_null_iff ν Aᶜ hA.compl).mpr hν,
      (partitionVariation_null_iff η A hA).mpr hη⟩

theorem positiveSingular_native_iff {α : Type u} [MeasurableSpace α] (μ η : Measure α) :
    positiveSingular μ η ↔ μ.MutuallySingular η := by
  constructor
  · rintro ⟨A,hA,hμ,hη⟩
    exact ⟨Aᶜ,hA.compl,hμ,by simpa using hη⟩
  · rintro ⟨A,hA,hμ,hη⟩
    exact ⟨Aᶜ,hA.compl,by simpa using hμ,hη⟩

theorem scalarSingular_symm {α : Type u} [MeasurableSpace α] {K : Type v}
    [NormedAddCommGroup K] {L : Type w} [NormedAddCommGroup L]
    (ν : VectorMeasure α K) (η : VectorMeasure α L) (h : scalarSingular ν η) :
    scalarSingular η ν := singularCosts_symm _ _ h

theorem positiveSingular_symm {α : Type u} [MeasurableSpace α] (μ η : Measure α)
    (h : positiveSingular μ η) : positiveSingular η μ := singularCosts_symm _ _ h

end D11.Ch14.ScalarInterfaces
