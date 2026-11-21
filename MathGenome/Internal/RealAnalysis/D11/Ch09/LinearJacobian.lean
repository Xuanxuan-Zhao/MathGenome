import MathGenome.Internal.RealAnalysis.D11.Ch03.TranslationDilation
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.LinearJacobian

/-! Linear change of variables for the completed Lebesgue measure.
The all-subset Haar formula transfers to the covering outer measure. Its
positive finite determinant factor preserves the full splitting test.
Transport is then applied on this completed measurable space itself. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 400000
namespace D11.Ch09.LinearJacobian
open D11.Ch03 D11.Ch03.LebesgueMeasures
open D11.Ch05.NonnegativeIntegral D11.Ch06.ScalarIntegral

/-- Native Haar normalization agrees with the covering construction on all sets. -/
theorem outer_linear (n : ℕ) [NeZero n] (T : Point n ≃ₗ[ℝ] Point n)
    (E : Set (Point n)) :
    OuterVolume.outerVolume n (T '' E) =
      ENNReal.ofReal |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| *
        OuterVolume.outerVolume n E := by
  change Specs.D11.Ch03.LebesgueMeasures.coveringOuter n (T '' E) =
    ENNReal.ofReal |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| *
      Specs.D11.Ch03.LebesgueMeasures.coveringOuter n E
  rw [← native_outer_agreement, ← native_outer_agreement]
  exact Measure.addHaar_image_linearMap volume (T : Point n →ₗ[ℝ] Point n) E

theorem outer_preimage (n : ℕ) [NeZero n] (T : Point n ≃ₗ[ℝ] Point n)
    (E : Set (Point n)) :
    Specs.D11.Ch03.LebesgueMeasures.coveringOuter n (T ⁻¹' E) =
      ENNReal.ofReal |(LinearMap.det (T : Point n →ₗ[ℝ] Point n))⁻¹| *
        Specs.D11.Ch03.LebesgueMeasures.coveringOuter n E := by
  rw [← native_outer_agreement, ← native_outer_agreement]
  exact Measure.addHaar_preimage_linearMap volume (LinearEquiv.isUnit_det' T).ne_zero E

theorem lebesgue_image_iff : Specs.D11.Ch09.LinearJacobian.lebesgue_image_iff := by
  intro n _ T E
  change (OuterVolume.outerVolume n).IsCaratheodory (T '' E) ↔
    (OuterVolume.outerVolume n).IsCaratheodory E
  exact D11.Ch03.TranslationDilation.caratheodory_image_iff
    (OuterVolume.outerVolume n) T.toEquiv _
    (ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' T).ne_zero)))
    ENNReal.ofReal_ne_top (outer_linear n T) E

theorem lebesgue_image_measure : Specs.D11.Ch09.LinearJacobian.lebesgue_image_measure := by
  intro n _ T E hE
  have hTE := (lebesgue_image_iff n T E).mpr hE
  refine ⟨hTE, ?_⟩
  rw [lebesgue_apply n _ hTE, lebesgue_apply n _ hE]
  exact outer_linear n T E

/-- The linear equivalence with the full Lebesgue structures on both sides. -/
abbrev completedEquiv (n : ℕ) [NeZero n] (T : Point n ≃ₗ[ℝ] Point n) :
    @MeasurableEquiv (Point n) (Point n) (lebesgueSpace n) (lebesgueSpace n) := by
  let : MeasurableSpace (Point n) := lebesgueSpace n
  refine { toEquiv := T.toEquiv, measurable_toFun := ?_, measurable_invFun := ?_ }
  · intro E hE
    rw [← T.toEquiv.image_symm_eq_preimage E]
    exact (lebesgue_image_iff n T.symm E).mpr hE
  · intro E hE
    rw [← T.toEquiv.image_eq_preimage_symm E]
    exact (lebesgue_image_iff n T E).mpr hE

theorem completed_measurable (n : ℕ) [NeZero n] (T : Point n ≃ₗ[ℝ] Point n) :
    @Measurable (Point n) (Point n) (lebesgueSpace n) (lebesgueSpace n) T := by
  let : MeasurableSpace (Point n) := lebesgueSpace n
  exact (completedEquiv n T).measurable

/-- Transport of completed Lebesgue measure, with the inverse Jacobian. -/
theorem map_lebesgue (n : ℕ) [NeZero n] (T : Point n ≃ₗ[ℝ] Point n) :
    @Measure.map (Point n) (Point n) (lebesgueSpace n) (lebesgueSpace n)
      T (lebesgue n) =
      ENNReal.ofReal |(LinearMap.det (T : Point n →ₗ[ℝ] Point n))⁻¹| • lebesgue n := by
  let : MeasurableSpace (Point n) := lebesgueSpace n
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (completed_measurable n T) hE, Measure.smul_apply,
    smul_eq_mul]
  have hpre : MeasurableSet[lebesgueSpace n] (T ⁻¹' E) :=
    (completed_measurable n T) hE
  calc
    lebesgue n (T ⁻¹' E) =
        Specs.D11.Ch03.LebesgueMeasures.coveringOuter n (T ⁻¹' E) :=
      lebesgue_apply n _ hpre
    _ = ENNReal.ofReal |(LinearMap.det (T : Point n →ₗ[ℝ] Point n))⁻¹| *
        Specs.D11.Ch03.LebesgueMeasures.coveringOuter n E := outer_preimage n T E
    _ = _ := congrArg (_ * ·) (lebesgue_apply n E hE).symm

/-- The forward determinant cancels the inverse determinant even for infinite mass. -/
theorem scaled_map_lebesgue (n : ℕ) [NeZero n] (T : Point n ≃ₗ[ℝ] Point n) :
    letI : MeasurableSpace (Point n) := lebesgueSpace n
    Measure.map T
        (ENNReal.ofReal |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| • lebesgue n) =
      lebesgue n := by
  let : MeasurableSpace (Point n) := lebesgueSpace n
  rw [Measure.map_smul (hf := (completed_measurable n T).aemeasurable),
    map_lebesgue, smul_smul]
  have hd := (LinearEquiv.isUnit_det' T).ne_zero
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hd, abs_one,
    ENNReal.ofReal_one, one_smul]

theorem nonnegative_jacobian : Specs.D11.Ch09.LinearJacobian.nonnegative_jacobian := by
  intro n _ T
  let : MeasurableSpace (Point n) := lebesgueSpace n
  intro h hh
  change nonnegativeIntegral (lebesgue n) _ = nonnegativeIntegral (lebesgue n) h
  simp only [integral_eq_lintegral]
  let c := ENNReal.ofReal |LinearMap.det (T : Point n →ₗ[ℝ] Point n)|
  calc
    (∫⁻ x, c * h (T x) ∂lebesgue n) = c * ∫⁻ x, h (T x) ∂lebesgue n :=
      lintegral_const_mul c (hh.comp (completed_measurable n T))
    _ = ∫⁻ x, h (T x) ∂(c • lebesgue n) := by
      simpa only [smul_eq_mul] using
        (lintegral_smul_measure (μ := lebesgue n) c (fun x => h (T x))).symm
    _ = ∫⁻ y, h y ∂Measure.map T (c • lebesgue n) :=
      (lintegral_map hh (completed_measurable n T)).symm
    _ = _ := by rw [scaled_map_lebesgue]

theorem scalar_integrable_iff : Specs.D11.Ch09.LinearJacobian.scalar_integrable_iff := by
  intro n _ T 𝕜 _ _ _
  let : MeasurableSpace (Point n) := lebesgueSpace n
  intro h
  change scalarIntegrable (lebesgue n) h ↔ scalarIntegrable (lebesgue n) (h ∘ T)
  rw [scalarIntegrable_iff, scalarIntegrable_iff]
  have hm : Measurable h ↔ Measurable (h ∘ T) :=
    (completedEquiv n T).measurable_comp_iff.symm
  apply and_congr hm
  have hi := integrable_map_equiv (μ := lebesgue n) (completedEquiv n T) h
  change Integrable h (Measure.map T (lebesgue n)) ↔ Integrable (h ∘ T) (lebesgue n) at hi
  rw [map_lebesgue] at hi
  exact (integrable_smul_measure
    (ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr
      (inv_ne_zero (LinearEquiv.isUnit_det' T).ne_zero)))) ENNReal.ofReal_ne_top).symm.trans hi

theorem scalar_jacobian : Specs.D11.Ch09.LinearJacobian.scalar_jacobian := by
  intro n _ T 𝕜 _ _ _
  let : MeasurableSpace (Point n) := lebesgueSpace n
  intro h hh
  have hc : scalarIntegrable (lebesgue n) (h ∘ T) :=
    (scalar_integrable_iff n T 𝕜 h).mp hh
  have hci := (scalarIntegrable_iff (lebesgue n) (h ∘ T)).mp hc
  have hw : scalarIntegrable (lebesgue n)
      (fun x => |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| • h (T x)) := by
    apply (scalarIntegrable_iff _ _).mpr
    constructor
    · exact hci.1.const_smul (|LinearMap.det (T : Point n →ₗ[ℝ] Point n)| : ℝ)
    · exact Integrable.smul (|LinearMap.det (T : Point n →ₗ[ℝ] Point n)| : ℝ) hci.2
  refine ⟨hw, ?_⟩
  change (∫ x, |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| • h (T x) ∂lebesgue n) =
    ∫ y, h y ∂lebesgue n
  rw [integral_smul]
  have heq := integral_map (μ :=
      ENNReal.ofReal |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| • lebesgue n)
    (completed_measurable n T).aemeasurable
    hh.1.aestronglyMeasurable
  rw [scaled_map_lebesgue, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at heq
  exact heq.symm

end D11.Ch09.LinearJacobian
