import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.EuclideanProductCompletion
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductSigma
import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueCompletion

noncomputable section
open Set MeasureTheory MeasurableSpace
open D11.Ch03

namespace D11.Ch08.EuclideanProductCompletion

/-- Splitting Euclidean coordinates preserves the normalized Borel volume.
The intermediate product with its L² norm is isometric; forgetting that norm
is the canonical volume preserving map to the ordinary product. -/
theorem coordinates_measurePreserving (m n : ℕ) :
    MeasurePreserving (coordinates m n) := by
  exact (WithLp.volume_preserving_ofLp (Point m) (Point n)).comp
    ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin m ⊕ Fin n => ℝ)).measurePreserving.comp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).measurePreserving)

open Specs.D11.Ch08.EuclideanProductCompletion (borelProduct factorSpace factorProduct)
open D11.Ch03.LebesgueMeasures
open D11.Ch02.Completion

abbrev borelCoordinates (m n : ℕ) : Point (m + n) ≃ᵐ Point m × Point n :=
  (coordinates m n).toHomeomorph.toMeasurableEquiv

theorem borel_sigma : Specs.D11.Ch08.EuclideanProductCompletion.borel_sigma := by
  intro m n _ _
  rw [← borel_structure m, ← borel_structure n, ← borel_structure (m + n)]
  exact (borelCoordinates m n).symm.measurableEmbedding.comap_eq.symm

theorem borel_measure : Specs.D11.Ch08.EuclideanProductCompletion.borel_measure := by
  intro m n _ _
  exact ((coordinates_measurePreserving m n).symm (borelCoordinates m n)).map_eq

/-- Null measurability transports in both directions under the Borel
measure-preserving coordinate bijection. -/
theorem null_image_iff (m n : ℕ) [NeZero m] [NeZero n]
    (E : Set (Point m × Point n)) :
    NullMeasurableSet E (borelProduct m n) ↔
      NullMeasurableSet ((coordinates m n).symm '' E) (borelMeasure (m + n)) := by
  constructor
  · intro hE
    have h := hE.preimage (coordinates_measurePreserving m n).quasiMeasurePreserving
    rw [(coordinates m n).image_symm_eq_preimage]
    exact h
  · intro hE
    have h := hE.preimage ((coordinates_measurePreserving m n).symm
      (borelCoordinates m n)).quasiMeasurePreserving
    change NullMeasurableSet ((coordinates m n).symm ⁻¹' ((coordinates m n).symm '' E))
      (borelProduct m n) at h
    simpa only [(coordinates m n).symm.injective.preimage_image] using h

theorem borel_completion_space :
    Specs.D11.Ch08.EuclideanProductCompletion.borel_completion_space := by
  intro m n _ _
  rw [LebesgueCompletion.completion_space]
  apply MeasurableSpace.ext
  intro E
  change NullMeasurableSet E (borelProduct m n) ↔
    ∃ F, NullMeasurableSet F (borelMeasure (m + n)) ∧
      (coordinates m n).symm ⁻¹' F = E
  constructor
  · intro hE
    exact ⟨(coordinates m n).symm '' E, (null_image_iff m n E).mp hE,
      (coordinates m n).symm.injective.preimage_image E⟩
  · rintro ⟨F, hF, rfl⟩
    exact hF.preimage ((coordinates_measurePreserving m n).symm
      (borelCoordinates m n)).quasiMeasurePreserving

theorem borel_completion_value :
    Specs.D11.Ch08.EuclideanProductCompletion.borel_completion_value := by
  intro m n _ _ E hE
  have hIm : MeasurableSet[lebesgueSpace (m + n)] ((coordinates m n).symm '' E) := by
    change MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value (m + n)] _
    rw [LebesgueCompletion.completion_space]
    exact (null_image_iff m n E).mp hE
  rw [LebesgueCompletion.completion_value (m + n) _ hIm]
  change (borelProduct m n) E = volume ((coordinates m n).symm '' E)
  rw [(coordinates m n).image_symm_eq_preimage]
  exact ((coordinates_measurePreserving m n).measure_preimage_emb
    (borelCoordinates m n).measurableEmbedding E).symm

/-- Completing any intermediate extension inside a completion gives back
that completion. The measure comparison uses sandwiches, including infinite
endpoint masses. -/
theorem completion_between {α : Type*} {a b : MeasurableSpace α}
    (μ : @Measure α a) (ν : @Measure α b)
    (hab : a ≤ b) (hbc : b ≤ completedSpace (m := a) μ)
    (hν : ∀ E, MeasurableSet[b] E → ν E = μ E) :
    completedSpace (m := b) ν = completedSpace (m := a) μ ∧
      ∀ E, MeasurableSet[completedSpace (m := b) ν] E → ν E = μ E := by
  have h₁ := minimality (m := a) μ (completedSpace (m := b) ν)
    (completedMeasure (m := b) ν)
    (hab.trans (extends_original (m := b) ν).1) (completed_complete (m := b) ν)
    (fun E hE => hν E (hab E hE))
  have h₂ := minimality (m := b) ν (completedSpace (m := a) μ)
    (completedMeasure (m := a) μ) hbc (completed_complete (m := a) μ)
    (fun E hE => (hν E hE).symm)
  exact ⟨le_antisymm h₂.1 h₁.1, fun E hE => (h₂.2 E hE).symm⟩

/-- Every rectangle from the completed factors is null measurable for the
Borel product. Generation then gives the whole intermediate product space. -/
theorem factorSpace_le_completion (m n : ℕ) [NeZero m] [NeZero n] :
    factorSpace m n ≤ completedSpace (borelProduct m n) := by
  change (lebesgueSpace m).prod (lebesgueSpace n) ≤ _
  rw [D11.Ch08.ProductSigma.generated_rectangles]
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨A, hA, B, hB, rfl⟩
  have hA' : NullMeasurableSet A (borelMeasure m) := by
    change MeasurableSet[Specs.D11.Ch02.Completion.completedSpace_value
      (Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value m)] A
    rwa [← LebesgueCompletion.completion_space m]
  have hB' : NullMeasurableSet B (borelMeasure n) := by
    change MeasurableSet[Specs.D11.Ch02.Completion.completedSpace_value
      (Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value n)] B
    rwa [← LebesgueCompletion.completion_space n]
  exact hA'.prod hB'

theorem borel_le_factorSpace (m n : ℕ) [NeZero m] [NeZero n] :
    (inferInstance : MeasurableSpace (Point m × Point n)) ≤ factorSpace m n := by
  exact sup_le_sup (MeasurableSpace.comap_mono (native_borel_le m))
    (MeasurableSpace.comap_mono (native_borel_le n))

theorem factor_product_inclusions :
    Specs.D11.Ch08.EuclideanProductCompletion.factor_product_inclusions := by
  intro m n _ _
  refine ⟨?_, ?_⟩
  · rw [← borel_structure m, ← borel_structure n]
    exact borel_le_factorSpace m n
  · rw [← borel_completion_space m n]
    exact factorSpace_le_completion m n

/-- Rectangle values identify the intermediate product with the restriction
of the completed Borel product, and hence give agreement on its whole domain. -/
theorem factor_product_agreement (m n : ℕ) [NeZero m] [NeZero n]
    (E : Set (Point m × Point n)) (hE : MeasurableSet[factorSpace m n] E) :
    factorProduct m n E = borelProduct m n E := by
  let h := factorSpace_le_completion m n
  let η : @Measure (Point m × Point n) (factorSpace m n) :=
    (completedMeasure (borelProduct m n)).trim h
  have hrect (A : Set (Point m)) (B : Set (Point n)) :
      borelProduct m n (A ×ˢ B) = borelMeasure m A * borelMeasure n B := by
    let : SigmaFinite (Specs.D11.Ch03.LebesgueMeasures.borelMeasure_value n) :=
      borel_sigmaFinite n
    exact Measure.prod_prod A B
  have hη : factorProduct m n = η := by
    let : MeasurableSpace (Point m) := Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value m
    let : MeasurableSpace (Point n) := Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value n
    let : @SigmaFinite (Point m) (Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value m)
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value m) := lebesgue_sigmaFinite m
    let : @SigmaFinite (Point n) (Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value n)
      (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value n) := lebesgue_sigmaFinite n
    apply Measure.prod_eq
    intro A B hA hB
    rw [show η (A ×ˢ B) = borelProduct m n (A ×ˢ B) from
      trim_measurableSet_eq h (hA.prod hB), hrect]
    have hAv := (lebesgue_apply m A hA).trans (native_outer_agreement m A).symm
    have hBv := (lebesgue_apply n B hB).trans (native_outer_agreement n B).symm
    exact congrArg₂ (· * ·) hAv.symm hBv.symm
  rw [hη]
  exact trim_measurableSet_eq h hE

theorem factor_product_restriction :
    Specs.D11.Ch08.EuclideanProductCompletion.factor_product_restriction := by
  intro m n _ _ E hE
  exact (factor_product_agreement m n E hE).trans
    (borel_completion_value m n E (factorSpace_le_completion m n E hE))

theorem factor_completion_space :
    Specs.D11.Ch08.EuclideanProductCompletion.factor_completion_space := by
  intro m n _ _
  exact (completion_between (borelProduct m n) (factorProduct m n)
    (borel_le_factorSpace m n) (factorSpace_le_completion m n)
    (factor_product_agreement m n)).1.trans (borel_completion_space m n)

theorem factor_completion_value :
    Specs.D11.Ch08.EuclideanProductCompletion.factor_completion_value := by
  intro m n _ _ E hE
  have h := completion_between (borelProduct m n) (factorProduct m n)
    (borel_le_factorSpace m n) (factorSpace_le_completion m n)
    (factor_product_agreement m n)
  have hE' : MeasurableSet[completedSpace (borelProduct m n)] E := by
    rw [← h.1]
    exact hE
  exact (h.2 E hE).trans (borel_completion_value m n E hE')

end D11.Ch08.EuclideanProductCompletion
