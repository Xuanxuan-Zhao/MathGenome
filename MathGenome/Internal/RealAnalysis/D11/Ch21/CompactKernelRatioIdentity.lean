import MathGenome.Internal.RealAnalysis.D11.Ch21.CompactTranslateIntegralContinuity
import MathGenome.Internal.RealAnalysis.D11.Ch21.HaarTranslationIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch18.CcTensorApproximation
import MathGenome.Internal.RealAnalysis.D11.Ch08.Fubini
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactKernelRatioIdentity
import Mathlib.Tactic.FinCases

namespace D11.Ch21.CompactKernelRatioIdentity
open Set MeasureTheory
open scoped Pointwise
open Specs.D11.Ch21.CompactKernelRatioIdentity (mass kernels)
universe u
noncomputable section
local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G
local instance {G : Type u} [TopologicalSpace G] : BorelSpace G := ⟨rfl⟩
variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

theorem denominator_properties :
    Specs.D11.Ch21.CompactKernelRatioIdentity.denominator_properties := by
  intro G _ _ _ _ _ ν hν g hg hne
  exact ⟨CompactTranslateIntegralContinuity.continuous_translate_integral ν hν.2.1 g,
    fun x => CompactTranslateIntegralContinuity.haar_translate_integral_pos ν
      (Or.inl hν) g hg hne x⟩

/-- Dividing by the positive continuous translate integral preserves Cc. -/
private def quotient (ν : @Measure G (borel G)) (hν : isLeftHaarMeasure ν)
    (f g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) (hne : g ≠ 0) :
    CompactlySupportedContinuousMap G ℝ where
  toFun x := f x / mass ν g x
  continuous_toFun := f.continuous.div
    (denominator_properties ν hν g hg hne).1
    (fun x => (denominator_properties ν hν g hg hne).2 x |>.2.ne')
  hasCompactSupport' := f.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (by
    apply closure_mono
    intro x hx
    exact fun h => hx (by simp [h]))

private lemma kernel_continuous (ν : @Measure G (borel G)) (hν : isLeftHaarMeasure ν)
    (f g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) (hne : g ≠ 0)
    (i : Fin 3) : Continuous (kernels ν f g i) := by
  have hB := (denominator_properties ν hν g hg hne).1
  have hBn := fun x => ((denominator_properties ν hν g hg hne).2 x).2.ne'
  fin_cases i
  · exact ((f.continuous.comp continuous_fst).mul
      (g.continuous.comp (continuous_snd.mul continuous_fst))).div
      (hB.comp continuous_fst) (fun p => hBn _)
  · exact ((f.continuous.comp (continuous_snd.inv.mul continuous_fst)).mul
      (g.continuous.comp continuous_fst)).div
      (hB.comp (continuous_snd.inv.mul continuous_fst)) (fun p => hBn _)
  · exact ((f.continuous.comp continuous_snd.inv).mul
      (g.continuous.comp continuous_fst)).div
      (hB.comp continuous_snd.inv) (fun p => hBn _)

/-- The precise common compact rectangle from the manuscript. -/
private lemma kernel_support (ν : @Measure G (borel G))
    (f g : CompactlySupportedContinuousMap G ℝ) (i : Fin 3) :
    tsupport (kernels ν f g i) ⊆
      (tsupport f ∪ tsupport g) ×ˢ (tsupport g * (tsupport f)⁻¹ ∪ (tsupport f)⁻¹) := by
  apply closure_minimal _
    ((f.hasCompactSupport.union g.hasCompactSupport).prod
      ((g.hasCompactSupport.mul f.hasCompactSupport.inv).union f.hasCompactSupport.inv)).isClosed
  rintro ⟨x,y⟩ hp
  fin_cases i
  · have hn : f x * g (y * x) ≠ 0 := by
      intro h
      exact hp (by simp [kernels, h])
    have hx := subset_tsupport f (left_ne_zero_of_mul hn)
    have hz := subset_tsupport g (right_ne_zero_of_mul hn)
    exact ⟨Or.inl hx, Or.inl ⟨y*x, hz, x⁻¹, by simpa, by simp⟩⟩
  · have hn : f (y⁻¹*x) * g x ≠ 0 := by
      intro h
      exact hp (by simp [kernels, h])
    have hx := subset_tsupport g (right_ne_zero_of_mul hn)
    have hz := subset_tsupport f (left_ne_zero_of_mul hn)
    exact ⟨Or.inr hx, Or.inl ⟨x, hx, (y⁻¹*x)⁻¹, by simpa,
      by simp [mul_inv_rev]⟩⟩
  · have hn : f y⁻¹ * g x ≠ 0 := by
      intro h
      exact hp (by simp [kernels, h])
    exact ⟨Or.inr (subset_tsupport g (right_ne_zero_of_mul hn)),
      Or.inr (by simpa using subset_tsupport f (left_ne_zero_of_mul hn))⟩

private def kernelCc (ν : @Measure G (borel G)) (hν : isLeftHaarMeasure ν)
    (f g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) (hne : g ≠ 0)
    (i : Fin 3) : CompactlySupportedContinuousMap (G × G) ℝ where
  toFun := kernels ν f g i
  continuous_toFun := kernel_continuous ν hν f g hg hne i
  hasCompactSupport' := ((f.hasCompactSupport.union g.hasCompactSupport).prod
      ((g.hasCompactSupport.mul f.hasCompactSupport.inv).union f.hasCompactSupport.inv)).of_isClosed_subset
    (isClosed_tsupport _) (kernel_support ν f g i)

theorem kernel_control : Specs.D11.Ch21.CompactKernelRatioIdentity.kernel_control := by
  intro G _ _ _ _ _ μ ν hμ hν g hg hne f
  let S := tsupport f ∪ tsupport g
  let T := tsupport g * (tsupport f)⁻¹ ∪ (tsupport f)⁻¹
  have hS : IsCompact S := f.hasCompactSupport.union g.hasCompactSupport
  have hT : IsCompact T := (g.hasCompactSupport.mul f.hasCompactSupport.inv).union
    f.hasCompactSupport.inv
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hμ.2.1.1
  let : IsFiniteMeasureOnCompacts ν := (D11.Ch18.compactFinite_iff ν).mp hν.2.1.1
  have hμS := hS.measure_lt_top (μ := μ)
  have hνT := hT.measure_lt_top (μ := ν)
  letI : Fact (μ S < ⊤) := ⟨hμS⟩
  letI : Fact (ν T < ⊤) := ⟨hνT⟩
  refine ⟨hS, hT, hμS, hνT, ?_⟩
  intro i
  have hm := D11.Ch18.CcTensorApproximation.product_borel_measurable G G ℝ
    (kernelCc ν hν f g hg hne i)
  refine ⟨hm, kernel_support ν f g i, ?_⟩
  have hb := (kernel_continuous ν hν f g hg hne i).bounded_above_of_compact_support
    (kernelCc ν hν f g hg hne i).hasCompactSupport
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- Each section of a Cc product function is integrable, even for measures
which are only finite on compact sets. -/
private lemma section_integrable (F : CompactlySupportedContinuousMap (G × G) ℝ)
    (μ : @Measure G (borel G)) [IsFiniteMeasureOnCompacts μ] (y : G) :
    D11.Ch06.ScalarIntegral.scalarIntegrable μ (fun x => F (x,y)) := by
  have hc : Continuous (fun x => F (x,y)) :=
    F.continuous.comp (continuous_id.prodMk continuous_const)
  have hk : IsCompact (Prod.fst '' tsupport F) := F.hasCompactSupport.image continuous_fst
  have hs : HasCompactSupport (fun x => F (x,y)) := by
    apply HasCompactSupport.intro' hk hk.isClosed
    intro x hx
    contrapose! hx
    exact ⟨(x,y), subset_tsupport F hx, rfl⟩
  exact (D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mpr
    ⟨hc.measurable, hc.integrable_of_hasCompactSupport hs⟩

/-- Haar changes of variables are used on the original, unrestricted measure. -/
private lemma translated_section (μ : @Measure G (borel G)) (hμ : isLeftHaarMeasure μ)
    (F : CompactlySupportedContinuousMap (G × G) ℝ) (y a : G) :
    (∫ x, F (a⁻¹*x,y) ∂μ) = ∫ x, F (x,y) ∂μ := by
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hμ.2.1.1
  exact (HaarTranslationIntegral.scalar_translation μ hμ a _
    (section_integrable F μ y)).choose_spec

theorem ratio_identity : Specs.D11.Ch21.CompactKernelRatioIdentity.ratio_identity := by
  intro G _ _ _ _ _ μ ν hμ hν g hg hne f
  let : IsFiniteMeasureOnCompacts μ := (D11.Ch18.compactFinite_iff μ).mp hμ.2.1.1
  let : IsFiniteMeasureOnCompacts ν := (D11.Ch18.compactFinite_iff ν).mp hν.2.1.1
  let q := quotient ν hν f g hg hne
  have hqcont : Continuous (fun y : G => f y⁻¹ / mass ν g y⁻¹) :=
    q.continuous.comp continuous_inv
  have hqcomp : HasCompactSupport (fun y : G => f y⁻¹ / mass ν g y⁻¹) :=
    q.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)
  refine ⟨(D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mpr
      ⟨f.continuous.measurable, f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport⟩,
    (D11.Ch06.ScalarIntegral.scalarIntegrable_iff μ _).mpr
      ⟨g.continuous.measurable, g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport⟩,
    (D11.Ch06.ScalarIntegral.scalarIntegrable_iff ν _).mpr
      ⟨hqcont.measurable, hqcont.integrable_of_hasCompactSupport hqcomp⟩, ?_⟩
  let H := kernelCc ν hν f g hg hne
  have swap (i : Fin 3) :
      (∫ x, ∫ y, H i (x,y) ∂ν ∂μ) = ∫ y, ∫ x, H i (x,y) ∂μ ∂ν :=
    integral_integral_swap_of_hasCompactSupport (f := fun x y => H i (x,y))
      (H i).continuous (H i).hasCompactSupport
  -- The library swap theorem restricts to compact support projections before
  -- invoking finite-measure Fubini. `kernel_control` additionally records one
  -- common finite rectangle and ordinary-product measurability for all three.
  have first (x : G) : (∫ y, H 0 (x,y) ∂ν) = f x := by
    change (∫ y, f x * g (y*x) / mass ν g x ∂ν) = f x
    rw [integral_div, integral_const_mul]
    change f x * mass ν g x / mass ν g x = f x
    rw [mul_div_assoc, div_self ((denominator_properties ν hν g hg hne).2 x).2.ne', mul_one]
  have change_x (y : G) : (∫ x, H 0 (x,y) ∂μ) = ∫ x, H 1 (x,y) ∂μ := by
    have he := translated_section μ hμ (H 0) y y
    simpa [H, kernelCc, kernels, mul_assoc] using he.symm
  have change_y (x : G) : (∫ y, H 1 (x,y) ∂ν) = ∫ y, H 2 (x,y) ∂ν := by
    let F : CompactlySupportedContinuousMap (G × G) ℝ :=
      ⟨⟨fun p => H 1 (p.2,p.1), (H 1).continuous.comp continuous_swap⟩,
        (H 1).hasCompactSupport.comp_homeomorph (Homeomorph.prodComm G G)⟩
    have he := translated_section ν hν F x x⁻¹
    simpa [F, H, kernelCc, kernels, mul_inv_rev, mul_assoc] using he.symm
  calc
    (∫ x, f x ∂μ) = ∫ x, ∫ y, H 0 (x,y) ∂ν ∂μ := by simp_rw [first]
    _ = ∫ y, ∫ x, H 0 (x,y) ∂μ ∂ν := swap 0
    _ = ∫ y, ∫ x, H 1 (x,y) ∂μ ∂ν := by simp_rw [change_x]
    _ = ∫ x, ∫ y, H 1 (x,y) ∂ν ∂μ := (swap 1).symm
    _ = ∫ x, ∫ y, H 2 (x,y) ∂ν ∂μ := by simp_rw [change_y]
    _ = ∫ y, ∫ x, H 2 (x,y) ∂μ ∂ν := swap 2
    _ = (∫ x, g x ∂μ) * (∫ y, f y⁻¹ / mass ν g y⁻¹ ∂ν) := by
      change (∫ y, ∫ x, f y⁻¹ * g x / mass ν g y⁻¹ ∂μ ∂ν) = _
      simp_rw [mul_div_right_comm, integral_const_mul, integral_mul_const]
      exact mul_comm _ _

end
end D11.Ch21.CompactKernelRatioIdentity
