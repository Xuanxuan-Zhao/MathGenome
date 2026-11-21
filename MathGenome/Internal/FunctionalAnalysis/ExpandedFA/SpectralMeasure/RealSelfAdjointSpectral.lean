import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealSelfAdjointSpectral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.NormalSpectralTests
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.RealDefinitions
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace ExpandedFA.SpectralMeasure.RealSelfAdjointSpectral
universe u v
open TraceIdeals.RealComplexification
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma operator_injective : Function.Injective (operator (H := H) (K := H)) := by
  intro A B h
  ext x
  exact congrArg (fun T : Space H →L[ℂ] Space H => (T (inclusion x)).1) h

@[simp] lemma operator_one : operator (1 : H →L[ℝ] H) = 1 := operator_id

@[simp] lemma operator_mul (A B : H →L[ℝ] H) :
    operator (A * B) = operator A * operator B := operator_comp A B

@[simp] lemma operator_star (A : H →L[ℝ] H) : operator (star A) = star (operator A) :=
  (operator_adjoint A).symm

lemma operator_normal (N : H →L[ℝ] H) (hN : IsStarNormal N) : IsStarNormal (operator N) := by
  constructor
  change star (operator N) * operator N = operator N * star (operator N)
  rw [← operator_star, ← operator_mul, ← operator_mul]
  exact congrArg operator hN.star_comm_self.eq

lemma operator_selfAdjoint_iff (N : H →L[ℝ] H) :
    IsSelfAdjoint (operator N) ↔ IsSelfAdjoint N := by
  change star (operator N) = operator N ↔ star N = N
  rw [← operator_star]
  exact operator_injective.eq_iff

lemma operator_unitary_iff (N : H →L[ℝ] H) :
    operator N ∈ unitary (Space H →L[ℂ] Space H) ↔ star N * N = 1 ∧ N * star N = 1 := by
  rw [Unitary.mem_iff]
  simp only [← operator_star, ← operator_mul, ← operator_one, operator_injective.eq_iff]

theorem selfAdjoint_iff_real_spectrum : Spec.SelfAdjointSpectrum.{v} := by
  intro H _ _ _ N hN
  rw [← operator_selfAdjoint_iff]
  exact NormalSpectralTests.selfAdjoint_iff_real_spectrum (Space H) (operator N)
    (operator_normal N hN)

theorem orthogonal_iff_circle_spectrum : Spec.OrthogonalSpectrum.{v} := by
  intro H _ _ _ N hN
  rw [← operator_unitary_iff]
  exact NormalSpectralTests.unitary_iff_circle_spectrum (Space H) (operator N)
    (operator_normal N hN)

lemma eigenvector_inclusion_iff (N : H →L[ℝ] H) (r : ℝ) (x : H) :
    operator N (inclusion x) = (r : ℂ) • inclusion x ↔ N x = r • x := by
  rw [operator_inclusion]
  have hs : inclusion (r • x) = (r : ℂ) • inclusion x := by
    rw [inclusion_apply, inclusion_apply,
      Hilbert.PreHilbertCompactSpectral.Spec.Complexification.csmul]
    change (r • x, (0 : H)) = _
    simp [Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair]
  rw [← hs]
  exact inclusion.injective.eq_iff

theorem real_eigenprojection : Spec.RealEigenprojection.{v} := by
  intro H _ _ _ N hN E hE r
  rw [NormalSpectralTests.eigenprojection (Space H) (operator N) (operator_normal N hN) E hE]
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change operator N (inclusion x) - (r : ℂ) • inclusion x = 0
      exact sub_eq_zero.mpr ((eigenvector_inclusion_iff N r x).mpr hx)
    · exact ((coordinates H).2.1 (inclusion x)).mpr ⟨x, rfl⟩
  · rintro ⟨hp, hfix⟩
    obtain ⟨x, rfl⟩ := ((coordinates H).2.1 p).mp hfix
    refine ⟨x, ?_, rfl⟩
    apply (eigenvector_inclusion_iff N r x).mp
    exact sub_eq_zero.mp hp

@[simp] lemma operator_sub (A B : H →L[ℝ] H) :
    operator (A - B) = operator A - operator B := by ext p; rfl

lemma operator_shift (A : H →L[ℝ] H) (r : ℝ) :
    operator (r • (1 : H →L[ℝ] H) - A) =
      (r : ℂ) • (1 : Space H →L[ℂ] Space H) - operator A := by
  rw [operator_sub, operator_real_smul, operator_one]

theorem real_spectrum_identification : Spec.RealSpectrumIdentification.{v} := by
  intro H _ _ _ A r
  have hreal : r ∉ spectrum ℝ A ↔ ∃ B : H →L[ℝ] H,
      (r • (1 : H →L[ℝ] H) - A).comp B = 1 ∧
      B.comp (r • (1 : H →L[ℝ] H) - A) = 1 := by
    rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_exists]
    rfl
  refine ⟨hreal, ?_⟩
  apply not_iff_not.mp
  rw [hreal, spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_exists]
  have h := (invertibility H (r • (1 : H →L[ℝ] H) - A)).1
  change (∃ B : H →L[ℝ] H, (r • (1 : H →L[ℝ] H) - A) * B = 1 ∧
    B * (r • (1 : H →L[ℝ] H) - A) = 1) ↔
    ∃ C : Space H →L[ℂ] Space H,
      operator (r • (1 : H →L[ℝ] H) - A) * C = 1 ∧
      C * operator (r • (1 : H →L[ℝ] H) - A) = 1 at h
  rw [operator_shift] at h
  exact h

theorem spectrum_geometry : Spec.SpectrumGeometry.{v} := by
  intro H _ _ _ A
  refine ⟨spectrum.isClosed A, ?_⟩
  intro r hr
  have h := spectrum.norm_le_norm_mul_of_mem hr
  have h1 : ‖(1 : H →L[ℝ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hh : |r| ≤ ‖A‖ * ‖(1 : H →L[ℝ] H)‖ := by
    simpa only [Real.norm_eq_abs] using h
  have hn : |r| ≤ ‖A‖ := by
    exact hh.trans
      ((mul_le_mul_of_nonneg_left h1 (norm_nonneg A)).trans (by simp))
  exact abs_le.mp hn

/-- This part needs only the bounded realization interface and Hausdorff limits. -/
theorem realization_independence : Spec.RealizationIndependence.{u, v} := by
  intro S H _ _ _ _ E C D f
  obtain ⟨a, ha⟩ := C.simple_approximation f
  exact tendsto_nhds_unique (C.integral_uniform_limit f a ha) (D.integral_uniform_limit f a ha)

theorem realization_regularity : Spec.RealizationRegularity.{v} := by
  intro H _ _ _ E C
  constructor
  · intro x
    letI := C.scalar_finite x
    infer_instance
  · intro x y
    letI : IsFiniteMeasure (C.coefficient x y).variation :=
      ⟨(C.variation_bound x y).trans_lt ENNReal.ofReal_lt_top⟩
    infer_instance

lemma restriction_inclusion (T : Space H →L[ℂ] Space H)
    (hT : ∀ x : H, conjugation (T (inclusion x)) = T (inclusion x)) (x : H) :
    inclusion (realInverse T x) = T (inclusion x) := by
  obtain ⟨y, hy⟩ := ((coordinates H).2.1 (T (inclusion x))).mp (hT x)
  change inclusion (T (inclusion x)).1 = T (inclusion x)
  rw [← hy]
  rfl

/-- Actual restriction of a fixed-real invariant complex PVM to the original H. -/
def descendPVM {S : Type u} [MeasurableSpace S] (E : ProjectionValuedMeasure S (Space H))
    (hE : ∀ B : Set S, MeasurableSet B → ∀ x : H,
      conjugation (E B (inclusion x)) = E B (inclusion x)) :
    RealProjectionValuedMeasure S H where
  toFun B := realInverse (E B)
  univ := by ext x; rw [E.univ]; rfl
  selfAdjoint B hB x y := by
    apply Complex.ofReal_injective
    rw [← inner_inclusion, ← inner_inclusion,
      restriction_inclusion _ (hE B hB) x, restriction_inclusion _ (hE B hB) y]
    exact E.inner_left B hB _ _
  inter B C hB hC := by
    ext x
    apply inclusion.injective
    change inclusion (realInverse (E B) (realInverse (E C) x)) =
      inclusion (realInverse (E (B ∩ C)) x)
    rw [restriction_inclusion _ (hE B hB), restriction_inclusion _ (hE C hC),
      restriction_inclusion _ (hE (B ∩ C) (hB.inter hC))]
    exact congrArg (fun T : Space H →L[ℂ] Space H => T (inclusion x)) (E.inter B C hB hC)
  countablyAdditive B hB hd x := by
    exact (E.iUnion B hB hd (inclusion x)).mapL realPart

theorem pvm_descent : Spec.PVMDescent.{u, v} := by
  intro S H _ _ _ _ E hE
  refine ⟨descendPVM E hE, ?_⟩
  intro B hB x
  exact restriction_inclusion (E B) (hE B hB) x

section BoundedIntegral
variable {S : Type u} [MeasurableSpace S] (E : RealProjectionValuedMeasure S H)
  (C : RealBoundedRealization E)
include C

lemma projection_add_complement (B : Set S) (hB : MeasurableSet B) : E B + E Bᶜ = 1 := by
  rw [← C.integral_indicator B hB, ← C.integral_indicator Bᶜ hB.compl, ← C.integral_add]
  have hh : RealBoundedFunction.add (.indicator B hB) (.indicator Bᶜ hB.compl) =
      RealBoundedFunction.const 1 := by
    apply RealBoundedFunction.ext
    intro s
    by_cases hs : s ∈ B <;> simp [RealBoundedFunction.add, RealBoundedFunction.indicator,
      RealBoundedFunction.const, hs]
  rw [hh, C.integral_const]
  simp

lemma integral_eq_on_support {K : Set S} (hK : MeasurableSet K) (hnull : E Kᶜ = 0)
    (f g : RealBoundedFunction S) (hfg : ∀ s ∈ K, f s = g s) : C.integral f = C.integral g := by
  have hEK : E K = 1 := by simpa [hnull] using projection_add_complement E C K hK
  have hi (a : RealBoundedFunction S) :
      C.integral (.mul a (.indicator K hK)) = C.integral a := by
    rw [C.integral_mul, C.integral_indicator, hEK, mul_one]
  rw [← hi f, ← hi g]
  congr 1
  apply RealBoundedFunction.ext
  intro s
  by_cases hs : s ∈ K
  · simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, hs, hfg s hs]
  · simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, hs]

lemma projection_eq_on_support {K : Set S} (hK : MeasurableSet K) (hnull : E Kᶜ = 0)
    {B D : Set S} (hB : MeasurableSet B) (hD : MeasurableSet D)
    (heq : ∀ s ∈ K, s ∈ B ↔ s ∈ D) : E B = E D := by
  rw [← C.integral_indicator B hB, ← C.integral_indicator D hD]
  apply integral_eq_on_support E C hK hnull
  intro s hs
  by_cases hb : s ∈ B
  · have hd := (heq s hs).mp hb
    simp [RealBoundedFunction.indicator, hb, hd]
  · have hd : s ∉ D := fun hd => hb ((heq s hs).mpr hd)
    simp [RealBoundedFunction.indicator, hb, hd]

lemma integral_apply_eq_zero_iff (f : RealBoundedFunction S) (x : H) :
    C.integral f x = 0 ↔ ∀ᵐ s ∂C.scalar x, f s = 0 := by
  letI := C.scalar_finite x
  obtain ⟨D, hD, hf⟩ := f.bounded
  have hi : Integrable (fun s => |f s| ^ 2) (C.scalar x) := by
    apply Integrable.of_bound ((f.measurable.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
      (D ^ 2)
    exact Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf s) 2)
  have hz := integral_eq_zero_iff_of_nonneg (fun s => sq_nonneg |f s|) hi
  rw [← C.norm_square f x] at hz
  simpa only [sq_eq_zero_iff, norm_eq_zero, abs_eq_zero, Filter.EventuallyEq,
    Pi.zero_apply] using hz

lemma range_zeroSet_eq_ker (f : RealBoundedFunction S) :
    LinearMap.range (E {s | f s = 0}).toLinearMap =
      LinearMap.ker (C.integral f).toLinearMap := by
  let B := {s | f s = 0}
  have hB : MeasurableSet B := f.measurable (measurableSet_singleton 0)
  have hz : C.integral (.const 0) = 0 := by rw [C.integral_const, zero_smul]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change C.integral f (E B y) = 0
    have he : RealBoundedFunction.mul f (.indicator B hB) = .const 0 := by
      apply RealBoundedFunction.ext
      intro s
      by_cases hs : s ∈ B
      · simp [RealBoundedFunction.mul, RealBoundedFunction.indicator,
          RealBoundedFunction.const, hs, show f s = 0 from hs]
      · simp [RealBoundedFunction.mul, RealBoundedFunction.indicator,
          RealBoundedFunction.const, hs]
    have hh := C.integral_mul f (.indicator B hB)
    rw [he, hz, C.integral_indicator] at hh
    exact congrArg (fun T : H →L[ℝ] H => T y) hh.symm
  · intro hx
    have hae := (integral_apply_eq_zero_iff E C f x).mp hx
    have hm : C.scalar x Bᶜ = 0 := ae_iff.mp hae
    have hn : E Bᶜ x = 0 := by
      rw [C.scalar_apply x Bᶜ hB.compl, ENNReal.ofReal_eq_zero] at hm
      exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖E Bᶜ x‖, norm_nonneg (E Bᶜ x)])
    refine ⟨x, ?_⟩
    have hh := congrArg (fun T : H →L[ℝ] H => T x) (projection_add_complement E C B hB)
    simpa [hn] using hh
end BoundedIntegral

lemma clippedCoordinate_eq_self (R : ℝ) (hR : 0 ≤ R) {t : ℝ} (ht : t ∈ Icc (-R) R) :
    clippedCoordinate R hR t = t := by
  change max (-R) (min R t) = t
  rw [min_eq_right ht.2, max_eq_right ht.1]

lemma resolves_radius_bound (A : H →L[ℝ] H) (E : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) (R : ℝ) (hR : 0 ≤ R) (h : Resolves A E C R hR) :
    ‖A‖ ≤ R := by
  rw [← h.2]
  apply C.integral_bound _ R hR
  intro t
  change |max (-R) (min R t)| ≤ R
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clippedCoordinate_on_spectrum (A : H →L[ℝ] H) (R : ℝ) (hR : 0 ≤ R)
    (hAR : ‖A‖ ≤ R) {t : ℝ} (ht : t ∈ spectrum ℝ A) :
    clippedCoordinate R hR t = t := by
  obtain ⟨hl, hu⟩ := (spectrum_geometry H A).2 ht
  exact clippedCoordinate_eq_self R hR ⟨(neg_le_neg hAR).trans hl, hu.trans hAR⟩

theorem singleton_range (A : H →L[ℝ] H) (E : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) (hE : Resolves A E C ‖A‖ (norm_nonneg A)) (r : ℝ) :
    LinearMap.range (E {r}).toLinearMap =
      LinearMap.ker (A - r • (1 : H →L[ℝ] H)).toLinearMap := by
  let f := RealBoundedFunction.add (clippedCoordinate ‖A‖ (norm_nonneg A))
    (.const (-r))
  have hf : C.integral f = A - r • (1 : H →L[ℝ] H) := by
    simp only [f, C.integral_add, hE.2, C.integral_const, neg_smul, sub_eq_add_neg]
  have hB : MeasurableSet {t | f t = 0} := f.measurable (measurableSet_singleton 0)
  have hproj : E {t | f t = 0} = E {r} := by
    apply projection_eq_on_support E C (spectrum.isClosed A).measurableSet hE.1 hB
      (measurableSet_singleton r)
    intro t ht
    have ht' := (spectrum_geometry H A).2 ht
    change clippedCoordinate ‖A‖ (norm_nonneg A) t + -r = 0 ↔ t = r
    rw [clippedCoordinate_eq_self _ _ ht', ← sub_eq_add_neg, sub_eq_zero]
  rw [← hproj, range_zeroSet_eq_ker E C f, hf]

theorem singleton_eigenprojection : Spec.SingletonRange.{v} := by
  intro H _ _ _ A E C hE r
  exact singleton_range A E C hE r

/-- A reciprocal with a positive cutoff is a globally bounded Borel symbol. -/
def cutoffReciprocal (r ε : ℝ) (hε : 0 < ε) : RealBoundedFunction ℝ where
  toFun t := if ε ≤ |r - t| then (r - t)⁻¹ else 0
  measurable := ((measurable_const.sub measurable_id).inv).ite
    (measurableSet_le measurable_const ((continuous_const.sub continuous_id).abs.measurable))
    measurable_const
  bounded := by
    refine ⟨ε⁻¹, le_of_lt (inv_pos.mpr hε), fun t => ?_⟩
    split_ifs with ht
    · rw [abs_inv]
      simpa only [one_div] using one_div_le_one_div_of_le hε ht
    · simp [le_of_lt (inv_pos.mpr hε)]

/-- A zero spectral projection on a neighborhood gives a bounded two-sided
inverse. This uses the clipped coordinate only on the proved spectral support. -/
theorem resolvent_of_zero_neighborhood (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (R : ℝ) (hR : 0 ≤ R) (hE : Resolves A E C R hR)
    (r ε : ℝ) (hε : 0 < ε) (U : Set ℝ) (hU : MeasurableSet U)
    (hball : Metric.ball r ε ⊆ U) (hzero : E U = 0) :
    r ∉ spectrum ℝ A := by
  let a := RealBoundedFunction.add (.const r)
    (.smul (-1) (clippedCoordinate R hR))
  let b := RealBoundedFunction.mul (cutoffReciprocal r ε hε) (.indicator Uᶜ hU.compl)
  have ha : C.integral a = r • (1 : H →L[ℝ] H) - A := by
    simp [a, C.integral_add, C.integral_const, C.integral_smul, hE.2, sub_eq_add_neg]
  have hcomp : E Uᶜ = 1 := by
    simpa [hzero] using projection_add_complement E C U hU
  have hab : C.integral (.mul a b) = 1 := by
    rw [← hcomp, ← C.integral_indicator Uᶜ hU.compl]
    apply integral_eq_on_support E C (spectrum.isClosed A).measurableSet hE.1
    intro t ht
    have hf := clippedCoordinate_on_spectrum A R hR
      (resolves_radius_bound A E C R hR hE) ht
    by_cases htu : t ∈ U
    · simp [a, b, RealBoundedFunction.mul, RealBoundedFunction.add,
        RealBoundedFunction.smul, RealBoundedFunction.const, RealBoundedFunction.indicator, htu]
    · have hdist : ε ≤ |r - t| := by
        by_contra hn
        apply htu
        apply hball
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
        exact lt_of_not_ge hn
      have hne : r - t ≠ 0 := by
        intro he
        rw [he, abs_zero] at hdist
        linarith
      simp [a, b, RealBoundedFunction.mul, RealBoundedFunction.add,
        RealBoundedFunction.smul, RealBoundedFunction.const, RealBoundedFunction.indicator,
        cutoffReciprocal, hf, htu, hdist, ← sub_eq_add_neg, hne]
  have hba : C.integral (.mul b a) = 1 := by
    have heq : RealBoundedFunction.mul b a = .mul a b := by
      apply RealBoundedFunction.ext
      intro t
      exact mul_comm _ _
    rw [heq, hab]
  rw [C.integral_mul, ha] at hab
  rw [C.integral_mul, ha] at hba
  exact ((real_spectrum_identification H A r).1).mpr ⟨C.integral b, hab, hba⟩

/-- Full spectral support follows from resolving data, for every permitted
radius and without a separability or nonzero-space hypothesis. -/
theorem full_support (A : H →L[ℝ] H) (E : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) (R : ℝ) (hR : 0 ≤ R)
    (hE : Resolves A E C R hR) (U : Set ℝ) (hU : IsOpen U)
    (hmeet : (U ∩ spectrum ℝ A).Nonempty) : E U ≠ 0 := by
  intro hz
  obtain ⟨r, hru, hrs⟩ := hmeet
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU r hru
  exact resolvent_of_zero_neighborhood A E C R hR hE r ε hε U
    hU.measurableSet hball hz hrs

/-- Clipping as a continuous map into its compact bounding interval. -/
def clipToInterval (R : ℝ) (hR : 0 ≤ R) : C(ℝ, Icc (-R) R) where
  toFun t := ⟨clippedCoordinate R hR t, by
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩⟩
  continuous_toFun := (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

/-- Every continuous function on the bounding interval gives a globally
bounded Borel symbol by clipping its argument. -/
def intervalSymbol (R : ℝ) (hR : 0 ≤ R) (f : C(Icc (-R) R, ℝ)) :
    RealBoundedFunction ℝ where
  toFun t := f (clipToInterval R hR t)
  measurable := f.continuous.measurable.comp (clipToInterval R hR).continuous.measurable
  bounded := ⟨‖f‖, norm_nonneg _, fun t => by simpa only [Real.norm_eq_abs] using (f.norm_coe_le_norm (clipToInterval R hR t))⟩

/-- The continuous part of a real bounded realization on a compact interval. -/
def intervalIntegral (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (R : ℝ) (hR : 0 ≤ R) : C(Icc (-R) R, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H) where
  toFun f := C.integral (intervalSymbol R hR f)
  map_one' := by
    have he : intervalSymbol R hR 1 = .const 1 := RealBoundedFunction.ext (fun _ => rfl)
    rw [he, C.integral_const, one_smul]
  map_mul' f g := by
    have he : intervalSymbol R hR (f * g) =
        .mul (intervalSymbol R hR f) (intervalSymbol R hR g) :=
      RealBoundedFunction.ext (fun _ => rfl)
    rw [he, C.integral_mul]
  map_zero' := by
    have he : intervalSymbol R hR 0 = .const 0 := RealBoundedFunction.ext (fun _ => rfl)
    rw [he, C.integral_const, zero_smul]
  map_add' f g := by
    have he : intervalSymbol R hR (f + g) =
        .add (intervalSymbol R hR f) (intervalSymbol R hR g) :=
      RealBoundedFunction.ext (fun _ => rfl)
    rw [he, C.integral_add]
  commutes' c := by
    have he : intervalSymbol R hR (algebraMap ℝ C(Icc (-R) R, ℝ) c) = .const c :=
      RealBoundedFunction.ext (fun _ => rfl)
    rw [he, C.integral_const, Algebra.algebraMap_eq_smul_one]
  map_star' f := by
    have he : intervalSymbol R hR (star f) = intervalSymbol R hR f :=
      RealBoundedFunction.ext (fun _ => rfl)
    rw [he, C.integral_star]

theorem intervalIntegral_continuous (E : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) (R : ℝ) (hR : 0 ≤ R) :
    Continuous (intervalIntegral E C R hR) := by
  exact ((intervalIntegral E C R hR).toLinearMap.mkContinuous 1 (fun f => by
    change ‖C.integral (intervalSymbol R hR f)‖ ≤ 1 * ‖f‖
    rw [one_mul]
    apply C.integral_bound _ _ (norm_nonneg f)
    intro t
    change |f (clipToInterval R hR t)| ≤ ‖f‖
    simpa only [Real.norm_eq_abs] using (f.norm_coe_le_norm (clipToInterval R hR t)))).continuous

lemma resolves_coordinate_at_norm (A : H →L[ℝ] H)
    (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
    (R : ℝ) (hR : 0 ≤ R) (hE : Resolves A E C R hR) :
    C.integral (clippedCoordinate ‖A‖ (norm_nonneg A)) = A := by
  calc
    _ = C.integral (clippedCoordinate R hR) := ?_
    _ = A := hE.2
  apply integral_eq_on_support E C (spectrum.isClosed A).measurableSet hE.1
  intro t ht
  rw [clippedCoordinate_on_spectrum A ‖A‖ (norm_nonneg A) le_rfl ht,
    clippedCoordinate_on_spectrum A R hR (resolves_radius_bound A E C R hR hE) ht]

/-- Supported resolving pairs have the same integral on continuous functions
of the compact clipped coordinate, regardless of their original radii. -/
theorem resolving_interval_integrals_eq (A : H →L[ℝ] H)
    (E F : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) (D : RealBoundedRealization F)
    (R Q : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hE : Resolves A E C R hR) (hF : Resolves A F D Q hQ) :
    intervalIntegral E C ‖A‖ (norm_nonneg A) =
      intervalIntegral F D ‖A‖ (norm_nonneg A) := by
  apply ContinuousMap.UniqueHom.eq_of_continuous_of_map_id
    (Icc (-‖A‖) ‖A‖) _ _
    (intervalIntegral_continuous E C _ _) (intervalIntegral_continuous F D _ _)
  change C.integral (intervalSymbol _ _ _) = D.integral (intervalSymbol _ _ _)
  have he : intervalSymbol ‖A‖ (norm_nonneg A)
      (ContinuousMap.restrict (Icc (-‖A‖) ‖A‖) (ContinuousMap.id ℝ)) =
      clippedCoordinate ‖A‖ (norm_nonneg A) := RealBoundedFunction.ext (fun _ => rfl)
  rw [he, resolves_coordinate_at_norm A E C R hR hE,
    resolves_coordinate_at_norm A F D Q hQ hF]

/-- Uniqueness of the actual real PVM, on all Borel sets and for arbitrary
nonnegative clipping bounds. -/
theorem resolving_pvm_unique (A : H →L[ℝ] H)
    (E F : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) (D : RealBoundedRealization F)
    (R Q : ℝ) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hE : Resolves A E C R hR) (hF : Resolves A F D Q hQ)
    (B : Set ℝ) (hB : MeasurableSet B) : E B = F B := by
  have hcont := resolving_interval_integrals_eq A E F C D R Q hR hQ hE hF
  have hcoeff : ∀ x y, C.coefficient x y = D.coefficient x y := by
    intro x y
    have hrad (G : RealProjectionValuedMeasure ℝ H) (L : RealBoundedRealization G) :
        FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon (L.coefficient x y) := by
      refine ⟨(L.variation_bound x y).trans_lt ENNReal.ofReal_lt_top, ?_⟩
      exact (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
        ((realization_regularity H G L).2 x y)
    apply FunctionSpaces.ScalarRieszMarkov.scalarIntegral_injective _ _ (hrad E C) (hrad F D)
    intro f
    let g : RealBoundedFunction ℝ :=
      ⟨f, f.continuous.measurable, ‖f‖, norm_nonneg _, fun t => by
        have hh := f.toBCF.norm_coe_le_norm t
        change ‖f t‖ ≤ ‖f‖ at hh
        simpa only [Real.norm_eq_abs] using hh⟩
    let fI : C(Icc (-‖A‖) ‖A‖, ℝ) := f.toContinuousMap.restrict _
    have heq (G : RealProjectionValuedMeasure ℝ H) (L : RealBoundedRealization G)
        (hs : G (spectrum ℝ A)ᶜ = 0) :
        L.integral g = intervalIntegral G L ‖A‖ (norm_nonneg A) fI := by
      apply integral_eq_on_support G L (spectrum.isClosed A).measurableSet hs
      intro t ht
      change f t = f (clippedCoordinate ‖A‖ (norm_nonneg A) t)
      rw [clippedCoordinate_on_spectrum A ‖A‖ (norm_nonneg A) le_rfl ht]
    have hi : C.integral g = D.integral g := by rw [heq E C hE.1, heq F D hF.1, hcont]
    have hh := congrArg (fun T : H →L[ℝ] H => ⟪x, T y⟫_ℝ) hi
    rw [C.coefficient_integral, D.coefficient_integral] at hh
    exact hh
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [← C.coefficient_apply x y B hB, ← D.coefficient_apply x y B hB, hcoeff x y]

section Conjugation
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

@[simp] lemma conjugation_involutive (p : Space H) : conjugation (conjugation p) = p :=
  (coordinates H).2.2.1 p

lemma conjugation_complex_smul (a : ℂ) (p : Space H) :
    conjugation (a • p) = star a • conjugation p := (coordinates H).2.2.2.1 a p

/-- Conjugation of a single complex-linear operator. -/
def conjugateEnd (T : Space H →L[ℂ] Space H) : Space H →L[ℂ] Space H :=
  ({ toFun p := conjugation (T (conjugation p))
     map_add' p q := by simp only [map_add]
     map_smul' a p := by
       simp only [RingHom.id_apply, conjugation_complex_smul, map_smul, star_star]
     } : Space H →ₗ[ℂ] Space H).mkContinuous ‖T‖ (fun p => by
       simpa only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometry.norm_map] using
         T.le_opNorm (conjugation p))

set_option maxHeartbeats 800000 in
/-- Conjugation is real-linear and continuous on the complex operator space. -/
def conjugateOperator : (Space H →L[ℂ] Space H) →L[ℝ] (Space H →L[ℂ] Space H) := by
  refine ({ toFun := conjugateEnd (H := H)
            map_add' T U := by
              ext p
              change conjugation ((T + U) (conjugation p)) =
                conjugation (T (conjugation p)) + conjugation (U (conjugation p))
              simp only [ContinuousLinearMap.add_apply, map_add]
            map_smul' (r : ℝ) T := by
              ext p
              simp only [conjugateEnd, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
                AddHom.coe_mk, smul_apply, RingHom.id_apply]
              change conjugation ((r : ℂ) • T (conjugation p)) =
                (r : ℂ) • conjugation (T (conjugation p))
              rw [conjugation_complex_smul]
              simp
            } : (Space H →L[ℂ] Space H) →ₗ[ℝ] (Space H →L[ℂ] Space H)).mkContinuous 1 ?_
  intro T
  change ‖conjugateEnd T‖ ≤ 1 * ‖T‖
  apply ContinuousLinearMap.opNorm_le_bound (conjugateEnd T) (by positivity : 0 ≤ 1 * ‖T‖)
  intro p
  change ‖conjugation (T (conjugation p))‖ ≤ (1 * ‖T‖) * ‖p‖
  simpa only [one_mul, LinearIsometry.norm_map] using T.le_opNorm (conjugation p)

@[simp] lemma conjugateOperator_apply (T : Space H →L[ℂ] Space H) (p : Space H) :
    conjugateOperator T p = conjugation (T (conjugation p)) := rfl

@[simp] lemma conjugateOperator_one : conjugateOperator (1 : Space H →L[ℂ] Space H) = 1 := by
  ext p
  exact conjugation_involutive p

lemma conjugateOperator_mul (T U : Space H →L[ℂ] Space H) :
    conjugateOperator (T * U) = conjugateOperator T * conjugateOperator U := by
  ext p
  simp only [ContinuousLinearMap.mul_apply, conjugateOperator_apply, conjugation_involutive]

lemma inner_conjugation (p q : Space H) :
    ⟪conjugation p, conjugation q⟫_ℂ = star ⟪p, q⟫_ℂ := by
  change Hilbert.PreHilbertCompactSpectral.Spec.Complexification.ip H
    (Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair H p.1 (-p.2))
    (Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair H q.1 (-q.2)) =
    star (Hilbert.PreHilbertCompactSpectral.Spec.Complexification.ip H p q)
  apply Complex.ext <;>
    simp [Hilbert.PreHilbertCompactSpectral.Spec.Complexification.ip,
      Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair] <;> ring

/-- Conjugating a complex PVM gives an actual complex PVM. -/
def conjugatePVM {S : Type u} [MeasurableSpace S]
    (E : ProjectionValuedMeasure S (Space H)) : ProjectionValuedMeasure S (Space H) where
  toFun B := conjugateOperator (E B)
  univ := by rw [E.univ, conjugateOperator_one]
  selfAdjoint B hB := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    change ⟪star (conjugateOperator (E B)) x, y⟫_ℂ =
      ⟪conjugateOperator (E B) x, y⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    change ⟪x, conjugation (E B (conjugation y))⟫_ℂ =
      ⟪conjugation (E B (conjugation x)), y⟫_ℂ
    rw [← conjugation_involutive x, inner_conjugation]
    rw [← E.inner_left B hB]
    rw [← inner_conjugation, conjugation_involutive]
    simp only [conjugation_involutive]
  inter B D hB hD := by
    rw [← conjugateOperator_mul, E.inter B D hB hD]
  iUnion B hB hd x := by
    exact (E.iUnion B hB hd (conjugation x)).mapL conjugation.toContinuousLinearMap

lemma bounded_complex_of_real {S : Type u} [MeasurableSpace S] (f : RealBoundedFunction S) :
    SpectralMeasure.Spec.IsBoundedMeasurable (fun s => (f s : ℂ)) := by
  obtain ⟨D, _, hf⟩ := f.bounded
  exact ⟨Complex.continuous_ofReal.measurable.comp f.measurable, D,
    fun s => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf s⟩

lemma uniform_complex_floorApprox {S : Type u} [MeasurableSpace S]
    (f : RealBoundedFunction S) :
    TendstoUniformly (fun n s => ((f.floorApprox n).map Complex.ofReal) s)
      (fun s => (f s : ℂ)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp f.tendstoUniformly_floorApprox ε hε] with n hn
  intro s
  simpa only [SimpleFunc.map_apply, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
    using hn s

section IntegralDescent
variable {S : Type u} [MeasurableSpace S]

lemma descended_simple_integral_inclusion
    (E : ProjectionValuedMeasure S (Space H)) (F : RealProjectionValuedMeasure S H)
    (hEF : ∀ B, MeasurableSet B → ∀ x : H, inclusion (F B x) = E B (inclusion x))
    (a : SimpleFunc S ℝ) (x : H) :
    inclusion (realSimpleSpectralIntegral F a x) =
      E.simpleIntegral (a.map Complex.ofReal) (inclusion x) := by
  classical
  rw [E.simpleIntegral_map_of_zero a Complex.ofReal (by simp)]
  simp only [realSimpleSpectralIntegral, sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hEF _ (a.measurableSet_fiber c)]
  exact RCLike.real_smul_eq_coe_smul c _

lemma descended_integral_inclusion
    (E : ProjectionValuedMeasure S (Space H)) (F : RealProjectionValuedMeasure S H)
    (hEF : ∀ B, MeasurableSet B → ∀ x : H, inclusion (F B x) = E B (inclusion x))
    (C : RealBoundedRealization F) (f : RealBoundedFunction S) (x : H) :
    inclusion (C.integral f x) = E.spectralIntegral (fun s => (f s : ℂ)) (inclusion x) := by
  have hreal := C.integral_uniform_limit f f.floorApprox f.tendstoUniformly_floorApprox
  have hreal_x := ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto _).comp hreal
  have hinc := inclusion.continuous.tendsto _ |>.comp hreal_x
  have hcplx := E.spectralIntegral_tendsto _ (bounded_complex_of_real f)
    (fun n => (f.floorApprox n).map Complex.ofReal) (uniform_complex_floorApprox f)
  have hcplx_x := ((ContinuousLinearMap.apply ℂ (Space H) (inclusion x)).continuous.tendsto _).comp hcplx
  change Tendsto (fun n => inclusion (realSimpleSpectralIntegral F (f.floorApprox n) x))
    atTop (𝓝 (inclusion (C.integral f x))) at hinc
  simp_rw [descended_simple_integral_inclusion E F hEF] at hinc
  exact tendsto_nhds_unique hinc hcplx_x

lemma descended_integral_eq_realInverse
    (E : ProjectionValuedMeasure S (Space H)) (F : RealProjectionValuedMeasure S H)
    (hEF : ∀ B, MeasurableSet B → ∀ x : H, inclusion (F B x) = E B (inclusion x))
    (C : RealBoundedRealization F) (f : RealBoundedFunction S) :
    C.integral f = realInverse (E.spectralIntegral (fun s => (f s : ℂ))) := by
  ext x
  exact congrArg (fun p : Space H => p.1) (descended_integral_inclusion E F hEF C f x)

end IntegralDescent

lemma conjugate_simpleIntegral {S : Type u} [MeasurableSpace S]
    (E : ProjectionValuedMeasure S (Space H)) (a : SimpleFunc S ℝ) :
    conjugateOperator (E.simpleIntegral (a.map Complex.ofReal)) =
      (conjugatePVM E).simpleIntegral (a.map Complex.ofReal) := by
  rw [E.simpleIntegral_map_of_zero a Complex.ofReal (by simp),
    (conjugatePVM E).simpleIntegral_map_of_zero a Complex.ofReal (by simp), map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ext p
  change conjugation ((c : ℂ) • E (a ⁻¹' {c}) (conjugation p)) =
    (c : ℂ) • conjugation (E (a ⁻¹' {c}) (conjugation p))
  rw [conjugation_complex_smul]
  simp

/-- Real bounded symbols commute with conjugation of the PVM. -/
lemma conjugate_spectralIntegral {S : Type u} [MeasurableSpace S]
    (E : ProjectionValuedMeasure S (Space H)) (f : RealBoundedFunction S) :
    conjugateOperator (E.spectralIntegral (fun s => (f s : ℂ))) =
      (conjugatePVM E).spectralIntegral (fun s => (f s : ℂ)) := by
  have h := E.spectralIntegral_tendsto _ (bounded_complex_of_real f)
    (fun n => (f.floorApprox n).map Complex.ofReal) (uniform_complex_floorApprox f)
  have hκ := conjugateOperator.continuous.tendsto _ |>.comp h
  have hF := (conjugatePVM E).spectralIntegral_tendsto _ (bounded_complex_of_real f)
    (fun n => (f.floorApprox n).map Complex.ofReal) (uniform_complex_floorApprox f)
  change Tendsto (fun n => conjugateOperator
      (E.simpleIntegral ((f.floorApprox n).map Complex.ofReal)))
    atTop (𝓝 (conjugateOperator (E.spectralIntegral (fun s => (f s : ℂ))))) at hκ
  simp_rw [conjugate_simpleIntegral] at hκ
  exact tendsto_nhds_unique hκ hF

/-- On a real self-adjoint complexification the actual spectral coordinate
is the real part, hence is an admissible bounded real symbol. -/
def spectralRealCoordinate (A : H →L[ℝ] H) :
    RealBoundedFunction (spectrum ℂ (operator A)) where
  toFun z := (z : ℂ).re
  measurable := Complex.continuous_re.measurable.comp measurable_subtype_coe
  bounded := by
    refine ⟨‖operator A‖, norm_nonneg _, fun z => (Complex.abs_re_le_norm _).trans ?_⟩
    exact (spectrum.norm_le_norm_mul_of_mem z.property).trans
      ((mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (norm_nonneg (operator A))).trans (by simp))

lemma spectral_coordinate_real (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (z : spectrum ℂ (operator A)) : ((z : ℂ).re : ℂ) = (z : ℂ) := by
  have hs := (selfAdjoint_iff_real_spectrum H A hA.isStarNormal).mp hA z z.property
  exact Complex.ext (by simp) (by simpa using hs.symm)

lemma resolves_of_coordinate {K : Type u} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [CompactSpace K] [T2Space K] [TopologicalSpace.MetrizableSpace K]
    (E : ProjectionValuedMeasure K (Space H)) (f : C(K, ℂ))
    (T : Space H →L[ℂ] Space H) (hT : E.spectralIntegral f = T) :
    ∃ μ : Space H → Space H → ComplexMeasure K,
      (∀ x y, FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon (μ x y)) ∧
      (∀ x y B, MeasurableSet B → μ x y B = ⟪x, E B y⟫_ℂ) ∧
      (∀ x y, Integrable (f : K → ℂ) (μ x y).variation ∧
        ⟪x, T y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral (μ x y) f) := by
  refine ⟨E.coefficientMeasure, ?_, E.coefficientMeasure_apply, ?_⟩
  · intro x y
    refine ⟨measure_lt_top _ _, ?_⟩
    exact (FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr inferInstance
  · intro x y
    refine ⟨?_, ?_⟩
    · apply Integrable.of_bound f.continuous.stronglyMeasurable.aestronglyMeasurable ‖f‖
      exact Eventually.of_forall (fun t => f.norm_coe_le_norm t)
    · rw [← hT, E.spectralIntegral_coefficient f (NormalPVM.continuous_bounded f)]
      rfl

/-- The complex spectral PVM of a real self-adjoint operator is invariant
under its canonical conjugation. No invariance certificate is assumed. -/
theorem spectral_conjugation_covariance (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator A)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator A) E) :
    ∀ B, MeasurableSet B → ∀ p : Space H,
      conjugation (E B p) = E B (conjugation p) := by
  have hcoord : (fun z : spectrum ℂ (operator A) => (z : ℂ)) =
      (fun z => (spectralRealCoordinate A z : ℂ)) := by
    funext z
    exact (spectral_coordinate_real A hA z).symm
  have hint : E.spectralIntegral (fun z : spectrum ℂ (operator A) => (z : ℂ)) = operator A :=
    NormalPVM.continuousIntegral_coordinate E hE
  have hconj : conjugateOperator (operator A) = operator A := by
    ext p
    change (A p.1, -(A (-p.2))) = (A p.1, A p.2)
    simp
  have hFint : (conjugatePVM E).spectralIntegral
      (fun z : spectrum ℂ (operator A) => (z : ℂ)) = operator A := by
    rw [hcoord, ← conjugate_spectralIntegral, ← hcoord, hint, hconj]
  have hF : NormalPVM.Spec.Resolves (operator A) (conjugatePVM E) := by
    exact resolves_of_coordinate (conjugatePVM E)
      ((ContinuousMap.id ℂ).restrict (spectrum ℂ (operator A))) (operator A) hFint
  obtain ⟨G, hG, huniq⟩ := NormalPVM.normal_spectral_theorem (Space H) (operator A)
    (operator_normal A hA.isStarNormal)
  intro B hB p
  have heq : (conjugatePVM E) B = E B := (huniq _ hF B hB).trans (huniq _ hE B hB).symm
  have hh := congrArg (fun T : Space H →L[ℂ] Space H => T (conjugation p)) heq
  simpa only [conjugatePVM, conjugateOperator_apply, conjugation_involutive] using hh

end Conjugation

section RealSpectralConstruction
universe w
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

/-- Image of an actual complex PVM under a measurable map. -/
def mapPVM {S : Type u} {T : Type w} [MeasurableSpace S] [MeasurableSpace T]
    (E : ProjectionValuedMeasure S (Space H)) (g : S → T) (hg : Measurable g) :
    ProjectionValuedMeasure T (Space H) where
  toFun B := E (g ⁻¹' B)
  univ := by simpa using E.univ
  selfAdjoint B hB := E.selfAdjoint _ (hg hB)
  inter B C hB hC := by simpa using E.inter (g ⁻¹' B) (g ⁻¹' C) (hg hB) (hg hC)
  iUnion B hB hd x := by
    simpa only [Set.preimage_iUnion] using E.iUnion (fun n => g ⁻¹' B n)
      (fun n => hg (hB n)) (fun i j hij => (hd hij).preimage g) x

lemma simpleIntegral_mapPVM {S : Type u} {T : Type w} [MeasurableSpace S] [MeasurableSpace T]
    (E : ProjectionValuedMeasure S (Space H)) (g : S → T) (hg : Measurable g)
    (a : SimpleFunc T ℂ) :
    (mapPVM E g hg).simpleIntegral a = E.simpleIntegral (a.comp g hg) := by
  classical
  change (∑ c ∈ a.range, c • E (g ⁻¹' (a ⁻¹' {c}))) =
    ∑ c ∈ (a.comp g hg).range, c • E ((a.comp g hg) ⁻¹' {c})
  symm
  apply Finset.sum_subset (a.range_comp_subset_range hg)
  intro c hc hcn
  have hempty : (a.comp g hg) ⁻¹' {c} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    apply hcn
    have hsc : (a.comp g hg) s = c := hs
    exact hsc ▸ (a.comp g hg).mem_range_self s
  change c • E ((a.comp g hg) ⁻¹' {c}) = 0
  rw [hempty, E.map_empty, smul_zero]

lemma spectralIntegral_mapPVM {S : Type u} {T : Type w} [MeasurableSpace S] [MeasurableSpace T]
    (E : ProjectionValuedMeasure S (Space H)) (g : S → T) (hg : Measurable g)
    (f : T → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    (mapPVM E g hg).spectralIntegral f = E.spectralIntegral (f ∘ g) := by
  obtain ⟨a, ha⟩ := exists_uniform_simple_approx f hf
  have hfg : SpectralMeasure.Spec.IsBoundedMeasurable (f ∘ g) := by
    obtain ⟨hfmeas, D, hD⟩ := hf
    exact ⟨hfmeas.comp hg, D, fun s => hD (g s)⟩
  have hm := (mapPVM E g hg).spectralIntegral_tendsto f hf a ha
  have he := E.spectralIntegral_tendsto (f ∘ g) hfg (fun n => (a n).comp g hg) (ha.comp g)
  simp_rw [simpleIntegral_mapPVM] at hm
  exact tendsto_nhds_unique hm he

/-- Spectral PVM on the whole real line, before real restriction. -/
def realLineComplexPVM (A : H →L[ℝ] H)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator A)) (Space H)) :
    ProjectionValuedMeasure ℝ (Space H) :=
  mapPVM E (fun z => (z : ℂ).re)
    (Complex.continuous_re.measurable.comp measurable_subtype_coe)

lemma realLineComplexPVM_fixed (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator A)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator A) E) :
    ∀ B : Set ℝ, MeasurableSet B → ∀ x : H,
      conjugation (realLineComplexPVM A E B (inclusion x)) =
        realLineComplexPVM A E B (inclusion x) := by
  intro B hB x
  have hmeas : MeasurableSet ((fun z : spectrum ℂ (operator A) => (z : ℂ).re) ⁻¹' B) :=
    (Complex.continuous_re.measurable.comp measurable_subtype_coe) hB
  change conjugation (E _ (inclusion x)) = E _ (inclusion x)
  rw [spectral_conjugation_covariance A hA E hE _ hmeas]
  exact congrArg (E _) (((coordinates H).2.1 (inclusion x)).mpr ⟨x, rfl⟩)

/-- Actual real projection values on the original Hilbert space. -/
def realSpectralPVM (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator A)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator A) E) : RealProjectionValuedMeasure ℝ H :=
  descendPVM (realLineComplexPVM A E) (realLineComplexPVM_fixed A hA E hE)

lemma realSpectralPVM_inclusion (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator A)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator A) E) (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    inclusion (realSpectralPVM A hA E hE B x) = realLineComplexPVM A E B (inclusion x) :=
  restriction_inclusion _ (realLineComplexPVM_fixed A hA E hE B hB) x

lemma realSpectralPVM_support (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator A)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator A) E) :
    realSpectralPVM A hA E hE (spectrum ℝ A)ᶜ = 0 := by
  have hempty : (fun z : spectrum ℂ (operator A) => (z : ℂ).re) ⁻¹' (spectrum ℝ A)ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    apply hz
    have hzreal := spectral_coordinate_real A hA z
    exact ((real_spectrum_identification H A (z : ℂ).re).2).mpr (hzreal.symm ▸ z.property)
  ext x
  change realInverse (E _) x = 0
  rw [hempty, E.map_empty]
  rfl

lemma realLineComplexPVM_coordinate (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (E : ProjectionValuedMeasure (spectrum ℂ (operator A)) (Space H))
    (hE : NormalPVM.Spec.Resolves (operator A) E) :
    (realLineComplexPVM A E).spectralIntegral
      (fun t => (clippedCoordinate ‖A‖ (norm_nonneg A) t : ℂ)) = operator A := by
  rw [realLineComplexPVM, spectralIntegral_mapPVM _ _ _ _
    (bounded_complex_of_real (clippedCoordinate ‖A‖ (norm_nonneg A)))]
  have hcoord : (fun z : spectrum ℂ (operator A) =>
      (clippedCoordinate ‖A‖ (norm_nonneg A) (z : ℂ).re : ℂ)) =
      (fun z : spectrum ℂ (operator A) => (z : ℂ)) := by
    funext z
    have hzreal := spectral_coordinate_real A hA z
    have hz : (z : ℂ).re ∈ spectrum ℝ A :=
      ((real_spectrum_identification H A (z : ℂ).re).2).mpr (hzreal.symm ▸ z.property)
    rw [clippedCoordinate_on_spectrum A ‖A‖ (norm_nonneg A) le_rfl hz]
    exact hzreal
  change E.spectralIntegral (fun z : spectrum ℂ (operator A) =>
    (clippedCoordinate ‖A‖ (norm_nonneg A) (z : ℂ).re : ℂ)) = operator A
  rw [hcoord]
  exact NormalPVM.continuousIntegral_coordinate E hE

/-- Existence of a supported resolving pair with a globally bounded coordinate. -/
theorem real_resolving_pair_exists (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) :
    ∃ (F : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization F),
      Resolves A F C ‖A‖ (norm_nonneg A) := by
  obtain ⟨E, hE, _⟩ := NormalPVM.normal_spectral_theorem (Space H) (operator A)
    (operator_normal A hA.isStarNormal)
  let F := realSpectralPVM A hA E hE
  let C := F.boundedRealization
  refine ⟨F, C, realSpectralPVM_support A hA E hE, ?_⟩
  ext x
  apply inclusion.injective
  have h := descended_integral_inclusion (realLineComplexPVM A E) F
    (realSpectralPVM_inclusion A hA E hE) C (clippedCoordinate ‖A‖ (norm_nonneg A)) x
  rw [realLineComplexPVM_coordinate A hA E hE] at h
  exact h.trans (operator_inclusion A x)

theorem spectral_resolution : Spec.SpectralResolution.{v} := by
  intro H _ _ _ A hA
  obtain ⟨E, C, hE⟩ := real_resolving_pair_exists A hA
  obtain ⟨hclosed, hbounded⟩ := spectrum_geometry H A
  obtain ⟨hscalar, hcoefficient⟩ := realization_regularity H E C
  refine ⟨E, C, hE, hclosed, hbounded, ?_, hscalar, hcoefficient, ?_, ?_⟩
  · exact full_support A E C ‖A‖ (norm_nonneg A) hE
  · exact singleton_range A E C hE
  · intro F D R hR hF B hB
    exact resolving_pvm_unique A F E D C R ‖A‖ hR (norm_nonneg A) hF hE B hB

end RealSpectralConstruction

end ExpandedFA.SpectralMeasure.RealSelfAdjointSpectral
