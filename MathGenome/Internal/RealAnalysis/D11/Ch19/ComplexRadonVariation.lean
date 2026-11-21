import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonSigmaFiniteInner
import MathGenome.Internal.RealAnalysis.D11.Ch14.VariationInequalities
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.ComplexRadonVariation

/-! Finite signed/complex Radon measures (paper.tex:5585–5594).
All measures use precisely the shared Borel sigma-algebra. Regularity under
finite domination is proved by transferring compact-approximation errors;
finite sums then give the variation equivalences. The scalar measures, Jordan
parts, total variation, and variation norm are the shared Chapter 14 objects. -/
namespace D11.Ch19

open Set MeasureTheory
open Ch14.ScalarInterfaces Ch14.Jordan Ch14.TotalVariation
open Ch14.VariationInequalities Ch18
open scoped ENNReal
universe u

local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X
local instance {X : Type u} [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

def isSignedRadon (ν : @SignedMeasure X (borel X)) : Prop :=
  isRadon (positivePart ν) ∧ isRadon (negativePart ν)

def isComplexRadon (ν : @ComplexMeasure X (borel X)) : Prop :=
  isSignedRadon (realPart ν) ∧ isSignedRadon (imaginaryPart ν)

/-- A positive measure dominated by a finite Radon measure is Radon. -/
theorem finite_radon_of_le (μ η : @Measure X (borel X))
    [IsFiniteMeasure μ] (hμ : isRadon μ) (hη : η ≤ μ) : isRadon η := by
  let : IsFiniteMeasure η := isFiniteMeasure_of_le μ hη
  let : Measure.Regular μ := (isRadon_iff_regular μ).mp hμ
  let : Measure.InnerRegular η := by
    constructor
    intro E hE r hr
    let ε := η E - r
    have hε : ε ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hr)
    obtain ⟨K, hKE, hK, hμK⟩ :=
      hE.exists_isCompact_sdiff_lt (μ := μ) (measure_ne_top μ E) hε
    refine ⟨K, hKE, hK, ?_⟩
    by_contra h
    have hKr : η K ≤ r := le_of_not_gt h
    have hrfin : r ≠ ∞ := ne_top_of_lt hr
    have herr : η (E \ K) < ε := (hη _).trans_lt hμK
    have htotal : η E < η E := calc
      η E ≤ η K + η (E \ K) := tsub_le_iff_left.mp le_measure_sdiff
      _ ≤ r + η (E \ K) := add_le_add hKr le_rfl
      _ < r + ε := ENNReal.add_lt_add_left hrfin herr
      _ = η E := add_tsub_cancel_of_le hr.le
    exact (lt_irrefl _ htotal)
  exact (isRadon_iff_regular η).mpr inferInstance

/-- Finite sums preserve Radon regularity without countability of the space. -/
theorem finite_radon_add (μ η : @Measure X (borel X))
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : isRadon μ) (hη : isRadon η) : isRadon (μ + η) := by
  let : Measure.Regular μ := (isRadon_iff_regular μ).mp hμ
  let : Measure.Regular η := (isRadon_iff_regular η).mp hη
  exact (isRadon_iff_regular (μ + η)).mpr inferInstance

/-- The definition by Jordan parts is equivalent to Radon total variation. -/
theorem signedRadon_iff_variation (ν : @SignedMeasure X (borel X)) :
    isSignedRadon ν ↔ isRadon (totalVariation ν) := by
  rw [signed_totalVariation_eq_jordan]
  constructor
  · exact fun h => finite_radon_add _ _ h.1 h.2
  · intro h
    exact ⟨finite_radon_of_le _ _ h (Measure.le_add_right le_rfl),
      finite_radon_of_le _ _ h (Measure.le_add_left le_rfl)⟩

omit [T2Space X] [LocallyCompactSpace X] in
/-- Each component variation is dominated by the complex variation. -/
theorem realPart_variation_le (ν : @ComplexMeasure X (borel X)) :
    totalVariation (realPart ν) ≤ totalVariation ν := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E _
  calc
    ‖realPart ν E‖ₑ = ENNReal.ofReal |(ν E).re| := by rw [← ofReal_norm]; rfl
    _ ≤ ENNReal.ofReal ‖ν E‖ := ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
    _ ≤ totalVariation ν E := norm_le_totalVariation ν E

omit [T2Space X] [LocallyCompactSpace X] in
theorem imaginaryPart_variation_le (ν : @ComplexMeasure X (borel X)) :
    totalVariation (imaginaryPart ν) ≤ totalVariation ν := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E _
  calc
    ‖imaginaryPart ν E‖ₑ = ENNReal.ofReal |(ν E).im| := by rw [← ofReal_norm]; rfl
    _ ≤ ENNReal.ofReal ‖ν E‖ := ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)
    _ ≤ totalVariation ν E := norm_le_totalVariation ν E

/-- The definition by the real and imaginary Jordan parts is equivalent to
Radon regularity of the partition-defined complex total variation. -/
theorem complexRadon_iff_variation (ν : @ComplexMeasure X (borel X)) :
    isComplexRadon ν ↔ isRadon (totalVariation ν) := by
  have := signed_finite (realPart ν)
  have := signed_finite (imaginaryPart ν)
  have := complex_finite ν
  constructor
  · intro h
    have hr := (signedRadon_iff_variation (realPart ν)).mp h.1
    have hi := (signedRadon_iff_variation (imaginaryPart ν)).mp h.2
    exact finite_radon_of_le _ _ (finite_radon_add _ _ hr hi)
      (complex_variation_le_components ν)
  · intro h
    exact ⟨(signedRadon_iff_variation _).mpr
      (finite_radon_of_le _ _ h (realPart_variation_le ν)),
      (signedRadon_iff_variation _).mpr
      (finite_radon_of_le _ _ h (imaginaryPart_variation_le ν))⟩

variable {Y : Type u} [TopologicalSpace Y]

theorem signed_norm_mass (ν : @SignedMeasure Y (borel Y)) :
    ENNReal.ofReal (variationNorm ν) = totalVariation ν univ := by
  let := signed_finite ν
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem complex_norm_mass (ν : @ComplexMeasure Y (borel Y)) :
    ENNReal.ofReal (variationNorm ν) = totalVariation ν univ := by
  let := complex_finite ν
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem signed_norm_eq_zero_iff (ν : @SignedMeasure Y (borel Y)) :
    variationNorm ν = 0 ↔ ν = 0 := by
  let := signed_finite ν
  exact variationNorm_eq_zero_iff ν

theorem complex_norm_eq_zero_iff (ν : @ComplexMeasure Y (borel Y)) :
    variationNorm ν = 0 ↔ ν = 0 := by
  let := complex_finite ν
  exact variationNorm_eq_zero_iff ν

end D11.Ch19
