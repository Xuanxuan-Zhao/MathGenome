import MathGenome.Internal.RealAnalysis.D11.Ch14.ScalarInterfaces
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-! Jordan decomposition for every real-valued signed measure.
The canonical parts are finite positive measures. The Hahn formulas apply
to any measurable supporting partition, and the variation identity uses
the raw partition supremum fixed by `ScalarInterfaces`. -/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch14.Jordan

open D11.Ch14.ScalarInterfaces

noncomputable def positivePart {α : Type u} [MeasurableSpace α]
    (ν : SignedMeasure α) : Measure α := ν.toJordanDecomposition.posPart

noncomputable def negativePart {α : Type u} [MeasurableSpace α]
    (ν : SignedMeasure α) : Measure α := ν.toJordanDecomposition.negPart

instance positivePart_finite {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) :
    IsFiniteMeasure (positivePart ν) := by
  unfold positivePart
  infer_instance

instance negativePart_finite {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) :
    IsFiniteMeasure (negativePart ν) := by
  unfold negativePart
  infer_instance

theorem jordan_finite {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) :
    IsFiniteMeasure (positivePart ν) ∧ IsFiniteMeasure (negativePart ν) :=
  ⟨inferInstance, inferInstance⟩

theorem jordan_decomposition {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α) :
    positiveSingular (positivePart ν) (negativePart ν) ∧
    ∀ E : Set α, MeasurableSet E →
      ν E = (positivePart ν E).toReal - (negativePart ν E).toReal := by
  refine ⟨(positiveSingular_native_iff _ _).mpr ν.toJordanDecomposition.mutuallySingular, ?_⟩
  intro E hE
  exact ν.apply_eq_posPart_real_sub_negPart_real hE

/-- Equality as scalar measures follows from equality on the original domain. -/
theorem signed_eq_of_difference {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (μ η : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : ∀ E : Set α, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal) :
    ν = μ.toSignedMeasure - η.toSignedMeasure := by
  apply VectorMeasure.ext
  intro E hE
  rw [Measure.toSignedMeasure_sub_apply hE]
  exact h E hE

theorem jordan_unique {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (μ η : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hs : positiveSingular μ η)
    (h : ∀ E : Set α, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal) :
    μ = positivePart ν ∧ η = negativePart ν := by
  let j : JordanDecomposition α :=
    { posPart := μ
      negPart := η
      mutuallySingular := (positiveSingular_native_iff μ η).mp hs }
  have hj : ν.toJordanDecomposition = j :=
    SignedMeasure.toJordanDecomposition_eq (signed_eq_of_difference ν μ η h)
  exact ⟨(congrArg JordanDecomposition.posPart hj).symm,
    (congrArg JordanDecomposition.negPart hj).symm⟩

/-- A Hahn partition gives a Jordan decomposition by restriction. Its equality
with the canonical one is obtained from uniqueness, without choosing the same
Hahn partition used internally by Mathlib. -/
theorem jordan_eq_of_hahn {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (P N : Set α) (hP : positiveSet ν P) (hN : negativeSet ν N)
    (hd : Disjoint P N) (hu : P ∪ N = univ) :
    ∃ (hp : 0 ≤[P] ν) (hn : ν ≤[N] 0),
      positivePart ν = ν.toMeasureOfZeroLE P hP.1 hp ∧
      negativePart ν = ν.toMeasureOfLEZero N hN.1 hn := by
  have hp : 0 ≤[P] ν := (VectorMeasure.restrict_le_restrict_iff 0 ν hP.1).mpr
    (fun A hA hAP => by simpa using hP.2 A hA hAP)
  have hn : ν ≤[N] 0 := (VectorMeasure.restrict_le_restrict_iff ν 0 hN.1).mpr
    (fun A hA hAN => by simpa using hN.2 A hA hAN)
  let μ := ν.toMeasureOfZeroLE P hP.1 hp
  let η := ν.toMeasureOfLEZero N hN.1 hn
  have hs : positiveSingular μ η := by
    refine ⟨Nᶜ, hN.1.compl, ?_, ?_⟩
    · simp only [compl_compl]
      rw [ν.toMeasureOfZeroLE_apply hp hP.1 hN.1]
      simp [hd.inter_eq]
    · rw [ν.toMeasureOfLEZero_apply hn hN.1 hN.1.compl]
      simp
  have heq : ∀ E : Set α, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal := by
    intro E hE
    change ν E = μ.real E - η.real E
    rw [ν.toMeasureOfZeroLE_real_apply hp hP.1 hE,
      ν.toMeasureOfLEZero_real_apply hn hN.1 hE, sub_neg_eq_add]
    have h := ν.of_union (hd.mono inter_subset_left inter_subset_left)
      (hP.1.inter hE) (hN.1.inter hE)
    simpa only [← Set.union_inter_distrib_right, hu, Set.univ_inter] using h
  obtain ⟨hμ,hη⟩ := jordan_unique ν μ η hs heq
  exact ⟨hp, hn, hμ.symm, hη.symm⟩

theorem jordan_hahn_formula {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (P N : Set α) (hP : positiveSet ν P) (hN : negativeSet ν N)
    (hd : Disjoint P N) (hu : P ∪ N = univ) (E : Set α) (hE : MeasurableSet E) :
    positivePart ν E = ENNReal.ofReal (ν (E ∩ P)) ∧
    negativePart ν E = ENNReal.ofReal (-ν (E ∩ N)) := by
  obtain ⟨hp,hn,hpos,hneg⟩ := jordan_eq_of_hahn ν P N hP hN hd hu
  constructor
  · rw [hpos, ν.toMeasureOfZeroLE_apply hp hP.1 hE]
    rw [Set.inter_comm E P, ENNReal.ofReal_eq_coe_nnreal]
  · rw [hneg, ν.toMeasureOfLEZero_apply hn hN.1 hE]
    rw [Set.inter_comm E N, ENNReal.ofReal_eq_coe_nnreal]

theorem jordan_minimal {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (μ η : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : ∀ E : Set α, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal) :
    positivePart ν ≤ μ ∧ negativePart ν ≤ η := by
  have heq := signed_eq_of_difference ν μ η h
  rw [positivePart, negativePart, heq, Measure.toJordanDecomposition_toSignedMeasure_sub]
  exact ⟨Measure.sub_le, Measure.sub_le⟩

theorem jordan_partition_variation {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (E : Set α) (hE : MeasurableSet E) :
    partitionVariation ν E = positivePart ν E + negativePart ν E := by
  calc
    partitionVariation ν E = ν.variation E := by
      simp only [partitionVariation, VectorMeasure.variation,
        preVariation, VectorMeasure.ennrealToMeasure_apply hE, ennrealPreVariation_apply,
        ← ofReal_norm]
    _ = ν.totalVariation E := by rw [ν.totalVariation_eq_variation]
    _ = positivePart ν E + negativePart ν E := by
      rw [SignedMeasure.totalVariation, Measure.add_apply]
      rfl

end D11.Ch14.Jordan
