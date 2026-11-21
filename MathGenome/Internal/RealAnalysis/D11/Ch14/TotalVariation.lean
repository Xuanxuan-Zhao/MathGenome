import MathGenome.Internal.RealAnalysis.D11.Ch14.Jordan
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.TotalVariation

/-! Partition variation for arbitrary scalar measures, `paper.tex:4631–4669`.
Mathlib's positive-measure construction is identified with the shared raw
partition supremum. Its finiteness is then proved from Hahn–Jordan parts,
first for real measures and then for complex measures. No density or
functional-analytic boundedness principle is used.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v w

namespace D11.Ch14.TotalVariation

open D11.Ch14.ScalarInterfaces

noncomputable def totalVariation {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) : Measure α :=
  ν.variation

theorem totalVariation_apply {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    (E : Set α) (hE : MeasurableSet E) :
    totalVariation ν E = partitionVariation ν E := by
  simp only [totalVariation, partitionVariation, VectorMeasure.variation,
    preVariation, VectorMeasure.ennrealToMeasure_apply hE, ennrealPreVariation_apply,
    ← ofReal_norm]

theorem totalVariation_partition_formula {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    (E : Set α) (hE : MeasurableSet E) :
    totalVariation ν E =
      ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
        ∑ A ∈ P.parts, ENNReal.ofReal ‖ν A‖ := by
  rw [totalVariation_apply ν E hE, partitionVariation_formula ν E hE]

theorem partitionVariation_empty {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) :
    partitionVariation ν ∅ = 0 := by
  rw [← totalVariation_apply ν ∅ MeasurableSet.empty, measure_empty]

theorem partitionVariation_countable_additivity {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] {ι : Type w} [Countable ι]
    (ν : VectorMeasure α K) (E : ι → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    partitionVariation ν (⋃ i, E i) = ∑' i, partitionVariation ν (E i) := by
  simp_rw [← totalVariation_apply ν _ (MeasurableSet.iUnion hE),
    ← totalVariation_apply ν _ (hE _)]
  exact measure_iUnion hd hE

theorem norm_le_totalVariation {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (E : Set α) :
    ENNReal.ofReal ‖ν E‖ ≤ totalVariation ν E := by
  rw [ofReal_norm]
  exact ν.enorm_measure_le_variation E

theorem totalVariation_null_iff {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K)
    (E : Set α) (hE : MeasurableSet E) :
    totalVariation ν E = 0 ↔ ∀ A, MeasurableSet A → A ⊆ E → ν A = 0 := by
  rw [totalVariation_apply ν E hE]
  exact partitionVariation_null_iff ν E hE

theorem signed_totalVariation_eq_jordan {α : Type u} [MeasurableSpace α]
    (ν : SignedMeasure α) :
    totalVariation ν = Jordan.positivePart ν + Jordan.negativePart ν := by
  apply Measure.ext
  intro E hE
  rw [totalVariation_apply ν E hE, Measure.add_apply]
  exact Jordan.jordan_partition_variation ν E hE

theorem signed_finite {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) :
    IsFiniteMeasure (totalVariation ν) := by
  rw [signed_totalVariation_eq_jordan]
  infer_instance

/-- Pointwise complex norm bounds and Jordan finiteness give a finite
dominating measure before any complex finite-variation assumption. -/
theorem complex_variation_le_components {α : Type u} [MeasurableSpace α]
    (ν : ComplexMeasure α) :
    totalVariation ν ≤ totalVariation (realPart ν) + totalVariation (imaginaryPart ν) := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E _
  calc
    ‖ν E‖ₑ = ENNReal.ofReal ‖ν E‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (|(ν E).re| + |(ν E).im|) :=
      ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im _)
    _ = ENNReal.ofReal ‖realPart ν E‖ + ENNReal.ofReal ‖imaginaryPart ν E‖ := by
      rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      rfl
    _ ≤ totalVariation (realPart ν) E + totalVariation (imaginaryPart ν) E :=
      add_le_add (norm_le_totalVariation _ _) (norm_le_totalVariation _ _)
    _ = (totalVariation (realPart ν) + totalVariation (imaginaryPart ν)) E :=
      (Measure.add_apply _ _ _).symm

theorem complex_finite {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) :
    IsFiniteMeasure (totalVariation ν) := by
  letI := signed_finite (realPart ν)
  letI := signed_finite (imaginaryPart ν)
  exact isFiniteMeasure_of_le
    (totalVariation (realPart ν) + totalVariation (imaginaryPart ν))
    (complex_variation_le_components ν)

theorem signed_partitionVariation_lt_top {α : Type u} [MeasurableSpace α]
    (ν : SignedMeasure α) (E : Set α) (hE : MeasurableSet E) :
    partitionVariation ν E < ⊤ := by
  letI := signed_finite ν
  rw [← totalVariation_apply ν E hE]
  exact measure_lt_top _ _

theorem complex_partitionVariation_lt_top {α : Type u} [MeasurableSpace α]
    (ν : ComplexMeasure α) (E : Set α) (hE : MeasurableSet E) :
    partitionVariation ν E < ⊤ := by
  letI := complex_finite ν
  rw [← totalVariation_apply ν E hE]
  exact measure_lt_top _ _

theorem complex_four_positive {α : Type u} [MeasurableSpace α] (ν : ComplexMeasure α) :
    ∃ α₁ α₂ α₃ α₄ : Measure α,
      IsFiniteMeasure α₁ ∧ IsFiniteMeasure α₂ ∧
      IsFiniteMeasure α₃ ∧ IsFiniteMeasure α₄ ∧
      ∀ E : Set α, MeasurableSet E →
        ν E = ((α₁ E).toReal : ℂ) - ((α₂ E).toReal : ℂ) +
          Complex.I * (((α₃ E).toReal : ℂ) - ((α₄ E).toReal : ℂ)) := by
  refine ⟨Jordan.positivePart (realPart ν), Jordan.negativePart (realPart ν),
    Jordan.positivePart (imaginaryPart ν), Jordan.negativePart (imaginaryPart ν),
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro E hE
  have hr := (Jordan.jordan_decomposition (realPart ν)).2 E hE
  have hi := (Jordan.jordan_decomposition (imaginaryPart ν)).2 E hE
  change (ν E).re = _ at hr
  change (ν E).im = _ at hi
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, ← hr, ← hi, mul_comm Complex.I]
  exact (Complex.re_add_im _).symm

theorem source_signed_finite {α : Type u} [MeasurableSpace α]
    (p : SourceScalarMeasure α ℝ) :
    ∃ μ : Measure α, IsFiniteMeasure μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E),
        μ E = ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
          ∑ A ∈ P.parts, ENNReal.ofReal ‖p.value A‖ := by
  refine ⟨totalVariation (scalarOfSource p), signed_finite _, ?_⟩
  intro E hE
  rw [totalVariation_partition_formula _ E hE]
  simp_rw [scalarOfSource_apply p _ (Subtype.property _)]

theorem source_complex_finite {α : Type u} [MeasurableSpace α]
    (p : SourceScalarMeasure α ℂ) :
    ∃ μ : Measure α, IsFiniteMeasure μ ∧
      ∀ (E : Set α) (hE : MeasurableSet E),
        μ E = ⨆ (P : Finpartition (⟨E,hE⟩ : Subtype MeasurableSet)),
          ∑ A ∈ P.parts, ENNReal.ofReal ‖p.value A‖ := by
  refine ⟨totalVariation (scalarOfSource p), complex_finite _, ?_⟩
  intro E hE
  rw [totalVariation_partition_formula _ E hE]
  simp_rw [scalarOfSource_apply p _ (Subtype.property _)]

end D11.Ch14.TotalVariation
