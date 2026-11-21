import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Topology

namespace ExpandedFA.SingularIntegrals.StandardConvolution

/-- The manuscript's standard convolution operator, with its actual distribution
kernel and Euclidean C¹ kernel estimates. -/
abbrev standardConvolutionSetting :
    Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator.settingType :=
  StandardConvolutionOperator

@[simp] theorem testL2_coe {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (φ : Tests 𝕜 d) :
    (testL2 φ : Space d → 𝕜) =ᵐ[volume] φ := MemLp.coeFn_toLp _

/-- Moving a test away from its support moves its reflected test away from zero. -/
theorem zero_not_mem_reflected_support {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 d) (x : Space d) (hx : x ∉ tsupport φ) :
    (0 : Space d) ∉ tsupport (reflectedTest φ x) := by
  have hs : tsupport (reflectedTest φ x) ⊆
      (fun y : Space d => x - y) ⁻¹' tsupport φ :=
    tsupport_comp_subset_preimage φ (Homeomorph.subLeft x).continuous
  intro h
  exact hx (by simpa using hs h)

/-- Off the support, the distributional convolution is the ordinary integral. -/
theorem distribution_off_support {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (φ : Tests 𝕜 d)
    (x : Space d) (hx : x ∉ tsupport φ) :
    T.distribution (reflectedTest φ x) = kernelIntegral T.kernel.function φ x := by
  rw [T.agrees_off_zero _ (zero_not_mem_reflected_support φ x hx)]
  simpa [kernelIntegral, reflectedTest, sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y => T.kernel.function y * φ (x - y)) volume x).symm

/-- The first, smooth-input part of the source's approximation argument. -/
theorem smooth_off_support_representation :
    Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator.smoothRepresentationType := by
  intro 𝕜 _ d T φ
  filter_upwards [T.kernel_action φ] with x hx hxs
  exact hx.trans (distribution_off_support T φ x hxs)

/-- A compact set disjoint from x sees a bounded continuous kernel translate. -/
theorem StandardKernel.continuousOn_translate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : StandardKernel 𝕜 d) (S : Set (Space d)) (x : Space d) (hx : x ∉ S) :
    ContinuousOn (fun y => k.function (x - y)) S := by
  apply k.contDiff.continuousOn.comp (continuous_const.sub continuous_id).continuousOn
  intro y hy
  change x - y ≠ 0
  exact sub_ne_zero.mpr (fun h => hx (h ▸ hy))

/-- Absolute integrability uses compactness away from the singularity. It holds
for every L¹ input supported almost everywhere on the compact set. -/
theorem off_support_absolute_integrability :
    Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator.absoluteIntegrabilityType := by
  intro 𝕜 _ d k f S hS hf hs x hx
  have hc := k.continuousOn_translate S x hx
  obtain ⟨C, hC⟩ := hS.bddAbove_image hc.norm
  have hi : IntegrableOn (fun y => k.function (x - y) * f y) S :=
    hf.integrableOn.bdd_mul (hc.aestronglyMeasurable hS.measurableSet)
      ((ae_restrict_mem hS.measurableSet).mono fun y hy => hC (mem_image_of_mem _ hy))
  have heq : (fun y => k.function (x - y) * f y) =ᵐ[volume]
      S.indicator (fun y => k.function (x - y) * f y) := by
    filter_upwards [hs] with y hy
    by_cases h : y ∈ S
    · simp [h]
    · simp [h, hy h]
  exact (hi.integrable_indicator hS.measurableSet).congr heq.symm

/-- Subtracting any fixed kernel value is legitimate once the input has zero
integral. This is a pointwise algebraic consequence of absolute integrability. -/
theorem zero_mean_kernel_difference {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : StandardKernel 𝕜 d) (f : Space d → 𝕜) (S : Set (Space d))
    (hS : IsCompact S) (hf : Integrable f) (hs : SupportedAE f S)
    (hm : (∫ y, f y) = 0) (c x : Space d) (hx : x ∉ S) :
    Integrable (fun y => (k.function (x - y) - k.function (x - c)) * f y) ∧
    kernelIntegral k.function f x =
      ∫ y, (k.function (x - y) - k.function (x - c)) * f y := by
  have hi : Integrable (fun y => k.function (x - y) * f y) :=
    off_support_absolute_integrability 𝕜 d k f S hS hf hs x hx
  have hj : Integrable (fun y => k.function (x - c) * f y) :=
    hf.const_mul (k.function (x - c))
  constructor
  · convert hi.sub hj using 1
    ext y
    exact sub_mul _ _ _
  · simp only [sub_mul, integral_sub hi hj, integral_const_mul, hm, mul_zero, sub_zero,
      kernelIntegral]

/-- Multiplication by a fixed test is a bounded map on L². -/
def testMultiplier {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (χ : Tests 𝕜 d) :
    L2 𝕜 d →L[𝕜] L2 𝕜 d :=
  (ContinuousLinearMap.mul 𝕜 𝕜).holderL volume ⊤ 2 2 (χ.memLp_top.toLp χ)

theorem testMultiplier_coe {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (χ : Tests 𝕜 d) (f : L2 𝕜 d) :
    (testMultiplier χ f : Space d → 𝕜) =ᵐ[volume] fun y => χ y * f y := by
  filter_upwards [(ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder (r := 2)
    (χ.memLp_top.toLp χ) f, χ.memLp_top.coeFn_toLp] with y hy hχ
  simpa [testMultiplier, ContinuousLinearMap.holderL_apply_apply, hχ] using hy

/-- Multiplying by a cutoff removes the singularity, producing an L² weight. -/
theorem StandardKernel.cutoff_memLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (k : StandardKernel 𝕜 d) (χ : Tests 𝕜 d) (x : Space d)
    (hx : x ∉ tsupport χ) : MemLp (fun y => k.function (x - y) * χ y) 2 := by
  have hc : ContinuousOn (fun y => k.function (x - y) * χ y) ({x}ᶜ) :=
    (k.continuousOn_translate {x}ᶜ x (by simp)).mul χ.continuous.continuousOn
  have hs : tsupport (fun y => k.function (x - y) * χ y) ⊆ {x}ᶜ := by
    intro y hy
    exact fun h => hx (mem_singleton_iff.mp h ▸ tsupport_mul_subset_right hy)
  exact (hc.continuous_of_tsupport_subset isClosed_singleton.isOpen_compl hs).memLp_of_hasCompactSupport
    χ.hasCompactSupport.mul_left

/-- A fixed cutoff gives the nonsmooth representation everywhere outside its
support. L² convergence is passed through T and through a continuous L² pairing. -/
theorem off_support_of_cutoff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : StandardConvolutionOperator 𝕜 d) (f : Space d → 𝕜) (S : Set (Space d))
    (h2 : MemLp f 2) (hs : SupportedAE f S) (χ : Tests 𝕜 d)
    (hχ : EqOn χ 1 S) :
    ∀ᵐ x ∂volume, x ∉ tsupport χ →
      T.operator (h2.toLp f) x = kernelIntegral T.kernel.function f x := by
  have hd := Lp.dense_hasCompactSupport_contDiff (F := 𝕜)
    (μ := (volume : Measure (Space d))) (p := 2) (by norm_num)
  obtain ⟨u, hu, hul⟩ := mem_closure_iff_seq_limit.mp (hd (h2.toLp f))
  choose g hg hgcompact hgsmooth using hu
  let φ : ℕ → Tests 𝕜 d := fun n =>
    { toFun := fun y => χ y * g n y
      contDiff' := χ.contDiff.mul (hgsmooth n)
      hasCompactSupport' := χ.hasCompactSupport.mul_right
      tsupport_subset' := subset_univ _ }
  have hφ (n : ℕ) : testMultiplier χ (u n) = testL2 (φ n) := by
    apply Lp.ext
    filter_upwards [testMultiplier_coe χ (u n), testL2_coe (φ n), hg n] with y hy hz hu
    calc
      _ = χ y * u n y := hy
      _ = χ y * g n y := congrArg (fun a => χ y * a) hu
      _ = _ := hz.symm
  have hχf : testMultiplier χ (h2.toLp f) = h2.toLp f := by
    apply Lp.ext
    filter_upwards [testMultiplier_coe χ (h2.toLp f), h2.coeFn_toLp, hs] with y hy hz hsy
    rw [hy]
    by_cases h : y ∈ S
    · simp [hχ h]
    · simp [hz, hsy h]
  have hlim : Tendsto (fun n => T.operator (testL2 (φ n))) atTop
      (𝓝 (T.operator (h2.toLp f))) := by
    have ht : Tendsto (fun n => T.operator (testMultiplier χ (u n))) atTop
        (𝓝 (T.operator (testMultiplier χ (h2.toLp f)))) :=
      (T.operator.continuous.tendsto _).comp
        ((testMultiplier χ).continuous.tendsto _ |>.comp hul)
    simpa only [hφ, hχf] using ht
  obtain ⟨j, hj, hjlim⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂volume, ∀ n, x ∉ tsupport χ →
      T.operator (testL2 (φ n)) x = kernelIntegral T.kernel.function (φ n) x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [smooth_off_support_representation 𝕜 d T (φ n)] with x hx hxc
    apply hx
    exact fun h => hxc (tsupport_mul_subset_left h)
  filter_upwards [hjlim, hrep] with x hxl hxr hx
  have hw := T.kernel.cutoff_memLp χ x hx
  let P : L2 𝕜 d →L[𝕜] 𝕜 :=
    (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing volume 2 2 (hw.toLp _)
  have hP (n : ℕ) : P (u n) = kernelIntegral T.kernel.function (φ n) x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, hg n] with y hy hu
    simp [hy, hu, φ, mul_assoc]
  have hPf : P (h2.toLp f) = kernelIntegral T.kernel.function f x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, h2.coeFn_toLp, hs] with y hy hz hsy
    simp only [hy, hz]
    by_cases h : y ∈ S
    · simp [hχ h]
    · simp [hsy h]
  have hp := (P.continuous.tendsto _).comp (hul.comp hj.tendsto_atTop)
  rw [hPf] at hp
  have hvalues : (fun n => T.operator (testL2 (φ (j n))) x) = fun n => P (u (j n)) := by
    funext n
    exact (hxr (j n) hx).trans (hP (j n)).symm
  rw [hvalues] at hxl
  exact tendsto_nhds_unique hxl hp

/-- Every compact support admits a smooth cutoff equal to one on it and
vanishing near any prescribed point outside it. -/
theorem cutoff_away_point {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (S : Set (Space d)) (hS : IsCompact S) (x : Space d) (hx : x ∉ S) :
    ∃ χ : Tests 𝕜 d, EqOn χ 1 S ∧ x ∉ tsupport χ := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball (0 : Space d)
  let U : Set (Space d) := ({x}ᶜ) ∩ Metric.ball 0 R
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.inter Metric.isOpen_ball
  have hSU : S ⊆ U := fun y hy => ⟨by simpa using ne_of_mem_of_not_mem hy hx, hR hy⟩
  obtain ⟨V, hVo, hSV, hVU⟩ := normal_exists_closure_subset hS.isClosed hU hSU
  have hK : IsCompact (closure V) :=
    (isCompact_closedBall (0 : Space d) R).of_isClosed_subset isClosed_closure
      (fun y hy => Metric.ball_subset_closedBall (hVU hy).2)
  have hSV' : S ⊆ interior (closure V) :=
    hSV.trans (hVo.subset_interior_closure)
  obtain ⟨a, haone, hazero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (modelWithCornersSelf ℝ (Space d))
      (n := ⊤) hS.isClosed hSV'
  have ha : ContDiff ℝ ∞ (a : Space d → ℝ) := contMDiff_iff_contDiff.mp a.contMDiff
  have hac : HasCompactSupport (a : Space d → ℝ) :=
    hK.of_isClosed_subset isClosed_closure
      (closure_minimal (fun y hy => by
        by_contra h
        exact hy (hazero y h)) isClosed_closure)
  let χ : Tests 𝕜 d :=
    { toFun := fun y => (a y : 𝕜)
      contDiff' := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp ha
      hasCompactSupport' := hac.comp_left (by simp)
      tsupport_subset' := subset_univ _ }
  refine ⟨χ, ?_, ?_⟩
  · intro y hy
    change (a y : 𝕜) = 1
    rw [haone.self_of_nhdsSet y hy]
    simp
  · have ht : tsupport χ ⊆ closure V := by
      apply closure_minimal _ isClosed_closure
      intro y hy
      by_contra h
      apply hy
      change (a y : 𝕜) = 0
      rw [hazero y h]
      simp
    exact fun h => (hVU (ht h)).1 (by simp)

/-- The complete off-support formula, including arbitrary almost everywhere
compact supports. Countably many cutoff complements cover the entire exterior. -/
theorem off_support_representation :
    Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator.offSupportRepresentationType := by
  intro 𝕜 _ d T f S hS _hf h2 hs
  choose χ hχ hχaway using fun x : ↥(Sᶜ) =>
    cutoff_away_point (𝕜 := 𝕜) S hS x.val x.property
  let U : ↥(Sᶜ) → Set (Space d) := fun i => (tsupport (χ i))ᶜ
  have hcover : Sᶜ ⊆ ⋃ i, U i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hχaway ⟨x, hx⟩⟩
  obtain ⟨c, hc, hcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof Sᶜ).elim_countable_subcover U
      (fun i => (isClosed_tsupport (χ i)).isOpen_compl) hcover
  let : Countable c := hc.to_subtype
  have hall : ∀ᵐ x ∂volume, ∀ i : c, x ∈ U i.val →
      T.operator (h2.toLp f) x = kernelIntegral T.kernel.function f x :=
    ae_all_iff.mpr fun i => off_support_of_cutoff T f S h2 hs (χ i.val) (hχ i.val)
  filter_upwards [hall] with x hx hxs
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcov hxs)
  exact hx ⟨i, hi⟩ hxi

/-- The zero-mean representation used in the Calderón–Zygmund bad-cube estimate. -/
theorem cancellation_representation :
    Specs.ExpandedFA.SingularIntegrals.StandardConvolutionOperator.cancellationRepresentationType := by
  intro 𝕜 _ d T f S hS hf h2 hs hm c
  filter_upwards [off_support_representation 𝕜 d T f S hS hf h2 hs] with x hx hxs
  obtain ⟨hi, heq⟩ := zero_mean_kernel_difference T.kernel f S hS hf hs hm c x hxs
  exact ⟨hi, (hx hxs).trans heq⟩

end ExpandedFA.SingularIntegrals.StandardConvolution
