import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.DifferentiableCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.HolderSpaces
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open Set Filter
open scoped Topology

namespace ExpandedFA.Supplements
namespace DifferentiableCompleteness
open HolderSpacesSpec

variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} (hab : a < b)

/-- A continuous auxiliary representative; all derivative claims below are within Icc. -/
def clipped (f : C(Interval a b, 𝕜)) (x : ℝ) : 𝕜 :=
  f (Set.projIcc a b hab.le x)

lemma clipped_continuous (f : C(Interval a b, 𝕜)) : Continuous (clipped hab f) :=
  f.continuous.comp continuous_projIcc

@[simp] lemma clipped_apply (f : C(Interval a b, 𝕜)) (x : Interval a b) :
    clipped hab f x = f x := by simp [clipped, Set.projIcc_of_mem]

lemma clipped_eq_extend (f : C(Interval a b, 𝕜)) :
    EqOn (clipped hab f) (intervalExtend f) (Icc a b) := by
  intro x hx
  simpa only [intervalExtend, dite_eq_left hx] using (clipped_apply hab f ⟨x, hx⟩)

/-- Integration over any fixed subinterval is a bounded linear observable. -/
def integralEvaluation (x : ℝ) : C(Interval a b, 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in a..x, clipped hab f t
      map_add' := by
        intro f g
        exact intervalIntegral.integral_add
          ((clipped_continuous hab f).intervalIntegrable _ _)
          ((clipped_continuous hab g).intervalIntegrable _ _)
      map_smul' := by intro c f; exact intervalIntegral.integral_smul c _ }
    |x - a| (by
      intro f
      change ‖∫ t in a..x, clipped hab f t‖ ≤ |x - a| * ‖f‖
      simpa only [clipped, mul_comm] using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (fun t _ => ContinuousMap.norm_coe_le_norm f (Set.projIcc a b hab.le t))))

/-- FTC for a pair of continuous interval functions related by interval differentiation. -/
lemma integral_eq_sub (f g : C(Interval a b, 𝕜))
    (hd : ∀ x ∈ Icc a b,
      HasDerivWithinAt (intervalExtend f) (intervalExtend g x) (Icc a b) x)
    (x : Interval a b) :
    integralEvaluation hab x g = f x - f ⟨a, le_rfl, hab.le⟩ := by
  change (∫ t in a..(x : ℝ), clipped hab g t) = _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.property.1
    ((clipped_continuous hab f).continuousOn : ContinuousOn (clipped hab f) (Icc a x))
    (fun t ht => ?_) ((clipped_continuous hab g).intervalIntegrable _ _)
  · simpa only [clipped_apply, show clipped hab f a = f ⟨a, le_rfl, hab.le⟩ from clipped_apply hab f ⟨a, le_rfl, hab.le⟩] using h
  have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.le.trans x.property.2⟩
  have hdf := (hd t htI).congr_of_mem (clipped_eq_extend hab f) htI
  rw [← clipped_eq_extend hab g htI] at hdf
  exact hdf.hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le x.property.2))

/-- Closedness of the interval derivative relation under uniform limits. -/
lemma hasDerivWithinAt_of_limits (hab : a < b)
    (f g : ℕ → C(Interval a b, 𝕜)) (F G : C(Interval a b, 𝕜))
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G))
    (hd : ∀ n x, x ∈ Icc a b →
      HasDerivWithinAt (intervalExtend (f n)) (intervalExtend (g n) x) (Icc a b) x) :
    ∀ x ∈ Icc a b,
      HasDerivWithinAt (intervalExtend F) (intervalExtend G x) (Icc a b) x := by
  have heq (x : Interval a b) :
      integralEvaluation hab x G = F x - F ⟨a, le_rfl, hab.le⟩ := by
    apply tendsto_nhds_unique ((integralEvaluation hab x).continuous.tendsto G |>.comp hg)
    have hfx := (continuous_eval_const x).tendsto F |>.comp hf
    have hfa := (continuous_eval_const (⟨a, le_rfl, hab.le⟩ : Interval a b)).tendsto F |>.comp hf
    convert hfx.sub hfa using 1
    funext n
    exact integral_eq_sub hab (f n) (g n) (hd n) x
  intro x hx
  have hdint := (intervalIntegral.integral_hasDerivAt_right (a := a) (b := x)
    ((clipped_continuous hab G).intervalIntegrable _ _)
    ((clipped_continuous hab G).stronglyMeasurableAtFilter _ _)
    (clipped_continuous hab G).continuousAt).hasDerivWithinAt (s := Icc a b)
  have h := hdint.const_add (F ⟨a, le_rfl, hab.le⟩)
  rw [clipped_eq_extend hab G hx] at h
  apply h.congr_of_mem _ hx
  intro t ht
  have he := heq ⟨t, ht⟩
  change _ = _ at he
  simp only [intervalExtend, dite_eq_left ht]
  change F ⟨t, ht⟩ = F ⟨a, le_rfl, hab.le⟩ + integralEvaluation hab t G
  rw [he]
  abel

/-- The zeroth coordinate and a compatible finite chain of derivatives determine a C^m function. -/
lemma exists_of_derivative_chain {m : ℕ} (g : Fin (m + 1) → C(Interval a b, 𝕜))
    (hd : ∀ (j : Fin m) x, x ∈ Icc a b →
      HasDerivWithinAt (intervalExtend (g j.castSucc))
        (intervalExtend (g j.succ) x) (Icc a b) x) :
    ∃ f : HolderSpacesSpec.Cm 𝕜 m hab, ∀ j, HolderSpacesSpec.Cm.derivative f j = g j := by
  have hit : ∀ j (hj : j ≤ m),
      EqOn (iteratedDerivWithin j (intervalExtend (g 0)) (Icc a b))
        (intervalExtend (g ⟨j, Nat.lt_succ_of_le hj⟩)) (Icc a b) := by
    intro j
    induction j with
    | zero => intro hj; exact fun _ _ => rfl
    | succ j ih =>
      intro hj x hx
      rw [iteratedDerivWithin_succ]
      have hjm : j < m := Nat.lt_of_succ_le hj
      rw [derivWithin_congr (ih (Nat.le_of_succ_le hj)) (ih (Nat.le_of_succ_le hj) hx)]
      exact (hd ⟨j, hjm⟩ x hx).derivWithin ((uniqueDiffOn_Icc hab) x hx)
  have hc (f : C(Interval a b, 𝕜)) : ContinuousOn (intervalExtend f) (Icc a b) :=
    (clipped_continuous hab f).continuousOn.congr (clipped_eq_extend hab f).symm
  have hreg : ContDiffOn ℝ m (intervalExtend (g 0)) (Icc a b) := by
    apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (uniqueDiffOn_Icc hab)).mpr
    constructor
    · intro j hj
      exact (hc _).congr (hit j hj)
    · intro j hj x hx
      exact ((hd ⟨j, hj⟩ x hx).congr_of_mem (hit j hj.le) hx).differentiableWithinAt
  let f : HolderSpacesSpec.Cm 𝕜 m hab := ⟨g 0, hreg⟩
  refine ⟨f, ?_⟩
  intro j
  ext x
  change iteratedDerivWithin j.val (intervalExtend (g 0)) (Icc a b) x = g j x
  rw [hit j.val (Nat.le_of_lt_succ j.isLt) x.property]
  exact intervalExtend_apply _ x

/-- Every derivative coordinate is contractive for the specified sum norm. -/
def derivativeMap (m : ℕ) (j : Fin (m + 1)) :
    HolderSpacesSpec.Cm 𝕜 m hab →L[𝕜] C(Interval a b, 𝕜) :=
  LinearMap.mkContinuous
    { toFun := fun f => HolderSpacesSpec.Cm.derivative f j
      map_add' := fun f g => HolderSpacesSpec.Cm.derivative_add f g j
      map_smul' := fun c f => HolderSpacesSpec.Cm.derivative_smul c f j }
    1 (by
      intro f
      change ‖HolderSpacesSpec.Cm.derivative f j‖ ≤ 1 * ‖f‖
      rw [one_mul, HolderSpacesSpec.Cm.norm_eq]
      exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ j))

/-- Adjacent coordinates of the canonical jet are interval derivatives. -/
lemma derivative_chain {m : ℕ} (f : HolderSpacesSpec.Cm 𝕜 m hab) (j : Fin m) :
    ∀ x ∈ Icc a b,
      HasDerivWithinAt (intervalExtend (HolderSpacesSpec.Cm.derivative f j.castSucc))
        (intervalExtend (HolderSpacesSpec.Cm.derivative f j.succ) x) (Icc a b) x := by
  intro x hx
  have hd := (f.property.differentiableOn_iteratedDerivWithin
    (m := j.val) (by exact_mod_cast j.isLt) (uniqueDiffOn_Icc hab) x hx).hasDerivWithinAt
  rw [← iteratedDerivWithin_succ] at hd
  have he : EqOn (intervalExtend (HolderSpacesSpec.Cm.derivative f j.castSucc))
      (iteratedDerivWithin j.val (intervalExtend f.val) (Icc a b)) (Icc a b) := by
    intro y hy
    simp [intervalExtend, HolderSpacesSpec.Cm.derivative, hy]
  convert hd.congr_of_mem he hx using 1
  simp [intervalExtend, HolderSpacesSpec.Cm.derivative, hx]

/-- Completeness follows by taking uniform limits of all coordinates of the jet. -/
theorem completeSpace (m : ℕ) : CompleteSpace (HolderSpacesSpec.Cm 𝕜 m hab) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hC (j : Fin (m + 1)) :
      CauchySeq (fun n => HolderSpacesSpec.Cm.derivative (u n) j) := by
    change CauchySeq ((derivativeMap (𝕜 := 𝕜) hab m j) ∘ u)
    exact (derivativeMap (𝕜 := 𝕜) hab m j).uniformContinuous.comp_cauchySeq hu
  choose g hg using fun j => cauchySeq_tendsto_of_complete (hC j)
  have hd (j : Fin m) : ∀ x ∈ Icc a b,
      HasDerivWithinAt (intervalExtend (g j.castSucc))
        (intervalExtend (g j.succ) x) (Icc a b) x := by
    apply hasDerivWithinAt_of_limits hab _ _ _ _ (hg j.castSucc) (hg j.succ)
    exact fun n => derivative_chain hab (u n) j
  obtain ⟨f, hf⟩ := exists_of_derivative_chain hab g hd
  refine ⟨f, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht (j : Fin (m + 1)) :
      Tendsto (fun n => ‖HolderSpacesSpec.Cm.derivative (u n) j - g j‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hg j)
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => ht j)
  have heq (n : ℕ) : ‖u n - f‖ =
      ∑ j : Fin (m + 1), ‖HolderSpacesSpec.Cm.derivative (u n) j - g j‖ := by
    rw [HolderSpacesSpec.Cm.norm_eq]
    apply Finset.sum_congr rfl
    intro j _
    change ‖derivativeMap hab m j (u n - f)‖ = _
    rw [map_sub]
    change ‖HolderSpacesSpec.Cm.derivative (u n) j - HolderSpacesSpec.Cm.derivative f j‖ = _
    rw [hf j]
  simpa only [← heq, Finset.sum_const_zero] using hsum

end DifferentiableCompleteness

/-- The differentiable completeness clause of paper.tex:5804–5805. -/
theorem cm_complete : DifferentiableCompletenessSpec.CmComplete := by
  intro 𝕜 _ m a b hab
  exact DifferentiableCompleteness.completeSpace hab m

instance cmCompleteSpace (𝕜 : Type*) [RCLike 𝕜] (m : ℕ) {a b : ℝ} (hab : a < b) :
    CompleteSpace (HolderSpacesSpec.Cm 𝕜 m hab) :=
  cm_complete 𝕜 m a b hab

end ExpandedFA.Supplements
