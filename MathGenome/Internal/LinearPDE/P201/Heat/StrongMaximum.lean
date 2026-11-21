import MathGenome.Internal.LinearPDE.P201.Heat.HeatBallMeanValue
import MathGenome.Internal.LinearPDE.P201Specs.Heat.StrongMaximum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace P201.Heat
open P201Specs.Heat (SpaceTime spaceTimeMeasure heatCylinder openHeatCylinder)

/-- A heat ball small enough stays inside the spatial domain and above time zero,
including its closure, even when its top time is the final time. -/
lemma exists_heatBall_closure_in_cylinder {n : ℕ} (hn : 1 ≤ n)
    {Ω : Set (P201Specs.Space n)} (hΩ : IsOpen Ω) {T : ℝ}
    {z₀ : SpaceTime n} (hz₀ : z₀ ∈ heatCylinder Ω T) :
    ∃ r > 0, closure (heatBall n r z₀) ⊆ heatCylinder Ω T := by
  have hopen : IsOpen (Ω ×ˢ Ioi (0 : ℝ)) := hΩ.prod isOpen_Ioi
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z₀ ⟨hz₀.1, hz₀.2.1⟩
  obtain ⟨δ, hδ, hshrink⟩ := heatBall_shrinking hn z₀ (half_pos hε)
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  have hsmall := hshrink r hr (by dsimp [r]; linarith)
  have hcl : closure (heatBall n r z₀) ⊆ closedBall z₀ (ε / 2) :=
    closure_minimal (hsmall.trans ball_subset_closedBall) isClosed_closedBall
  have ht := closure_minimal (heatBall_subset_compact_product hn hr z₀)
    ((isClosed_closedBall).prod isClosed_Icc)
  refine ⟨r, hr, fun z hz => ?_⟩
  have hz' := hball ((closedBall_subset_ball (by linarith : ε / 2 < ε)) (hcl hz))
  exact ⟨hz'.1, hz'.2, (ht hz).2.2.trans hz₀.2.2⟩

/-- Interior classical regularity supplies the one-sided mean value formula. -/
lemma caloric_cylinder_meanValue {n : ℕ} (hn : 1 ≤ n)
    {Ω : Set (P201Specs.Space n)} {T : ℝ} {u : SpaceTime n → ℝ}
    (huc : ContinuousOn u (heatCylinder Ω T))
    (hu : IsClassicalCaloricOn u (openHeatCylinder Ω T))
    {r : ℝ} (hr : 0 < r) {z₀ : SpaceTime n} (ht : z₀.2 ≤ T)
    (hc : closure (heatBall n r z₀) ⊆ heatCylinder Ω T) :
    HeatBallMeanValueIdentity u r z₀ := by
  apply heatBallMeanValueOneSided n hn r hr z₀ u (huc.mono hc)
  apply IsClassicalCaloricOn.mono hu
  intro z hz
  exact ⟨(hc hz.1).1, (hc hz.1).2.1, hz.2.trans_le ht⟩

/-- Affine rays directed strictly into the past enter every heat ball at their top. -/
lemma backward_ray_mem_heatBall {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) (v : P201Specs.Space n) :
    ∃ δ > 0, ∀ τ : ℝ, 0 < τ → τ < δ →
      (z₀.1 + τ • v, z₀.2 - τ) ∈ heatBall n r z₀ := by
  let a : ℝ := r ^ 2 / (4 * Real.pi * Real.exp 1)
  let b : ℝ := 1 / (‖v‖ ^ 2 + 1)
  refine ⟨min a b, lt_min (by dsimp [a]; positivity) (by dsimp [b]; positivity), ?_⟩
  intro τ hτ hτδ
  have hτa : τ < a := hτδ.trans_le (min_le_left _ _)
  have hτb : τ < b := hτδ.trans_le (min_le_right _ _)
  have hlog : 1 < Real.log (r ^ 2 / (4 * Real.pi * τ)) := by
    rw [← Real.log_exp 1]
    apply Real.log_lt_log (Real.exp_pos _)
    apply (lt_div_iff₀ (by positivity : 0 < 4 * Real.pi * τ)).mpr
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * Real.pi * Real.exp 1)).mp hτa
    nlinarith
  have hb : τ * (‖v‖ ^ 2 + 1) < 1 := (lt_div_iff₀ (by positivity)).mp hτb
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [heatBall_mem_iff_norm_sq hr]
  refine ⟨by dsimp; linarith, ?_⟩
  simp only [sub_sub_cancel, sub_add_cancel_left, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  have hmul := mul_lt_mul_of_pos_left hlog (by positivity : 0 < 2 * (n : ℝ) * τ)
  nlinarith [sq_nonneg ‖v‖]

/-- At a maximum, positivity of the mean-value density forces constancy on
its whole heat ball. The exceptional spatial axis has product measure zero. -/
lemma eqOn_heatBall_of_meanValue_maximum {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) {z₀ : SpaceTime n} {u : SpaceTime n → ℝ} {M : ℝ}
    (hu : ContinuousOn u (closure (heatBall n r z₀)))
    (hmean : HeatBallMeanValueIdentity u r z₀)
    (hbound : ∀ z ∈ heatBall n r z₀, u z ≤ M) (hmax : u z₀ = M) :
    EqOn u (fun _ => M) (heatBall n r z₀) := by
  have hd : Module.finrank ℝ (P201Specs.Space n) = n := by simp [P201Specs.Space]
  have : Nontrivial (P201Specs.Space n) :=
    Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank ℝ (P201Specs.Space n))
  let μ := (spaceTimeMeasure n).restrict (heatBall n r z₀)
  have hmem : ∀ᵐ z ∂μ, z ∈ heatBall n r z₀ :=
    ae_restrict_mem (heatBall_measurableSet n r z₀)
  have hw := heatBallWeightIntegrable n hn r hr z₀
  have huc := hu.mono subset_closure
  obtain ⟨B, hB⟩ := heatBall_bounded_of_continuousOn_closure hn hr z₀ hu
  have huB : ∀ᵐ z ∂μ, ‖u z‖ ≤ B := hmem.mono (fun z hz => hB z hz)
  have hi : Integrable (fun z => u z * heatBallWeight n r z₀ z) μ :=
    hw.bdd_mul (huc.aestronglyMeasurable (heatBall_measurableSet n r z₀)) huB
  have hgi : Integrable (fun z => (M - u z) * heatBallWeight n r z₀ z) μ := by
    apply Integrable.congr ((hw.const_mul M).sub hi)
    filter_upwards [] with z
    exact (sub_mul M (u z) (heatBallWeight n r z₀ z)).symm
  have hnonneg : 0 ≤ᵐ[μ] (fun z => (M - u z) * heatBallWeight n r z₀ z) := by
    filter_upwards [hmem] with z hz
    exact mul_nonneg (sub_nonneg.mpr (hbound z hz))
      (heatBallWeightNonnegative n r hr z₀ z)
  have hzero : ∫ z, (M - u z) * heatBallWeight n r z₀ z ∂μ = 0 := by
    simp only [sub_mul]
    rw [integral_sub (hw.const_mul M) hi, integral_const_mul,
      heatBallWeightMass n hn r hr z₀, mul_one,
      ← (meanValueIdentity_iff_weighted u r z₀).mp hmean, hmax, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hgi).mp hzero
  have haxis : ∀ᵐ z ∂spaceTimeMeasure n, z.1 ≠ z₀.1 :=
    Measure.quasiMeasurePreserving_fst.ae ((P201Specs.spatialMeasure n).ae_ne z₀.1)
  have hueq : u =ᵐ[μ] (fun _ => M) := by
    filter_upwards [hae, hmem, ae_restrict_of_ae haxis] with z hz hzm hzx
    have hpos : 0 < heatBallWeight n r z₀ z := by
      unfold heatBallWeight P201Specs.Heat.heatBallWeight
      have hx : 0 < ‖z₀.1 - z.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx.symm)
      have ht : 0 < z₀.2 - z.2 := sub_pos.mpr hzm.1
      positivity
    have := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hpos)
    exact (sub_eq_zero.mp this).symm
  exact Measure.eqOn_open_of_ae_eq hueq (heatBallOpen n r z₀) huc continuousOn_const

/-- A local heat-ball maximum propagates along an entire straight segment with
strictly decreasing time, by continuous induction on the segment parameter. -/
lemma maximum_propagates_on_segment {n : ℕ} (hn : 1 ≤ n)
    {Ω : Set (P201Specs.Space n)} {T : ℝ} {u : SpaceTime n → ℝ} {M : ℝ}
    (huc : ContinuousOn u (heatCylinder Ω T))
    (hlocal : ∀ z ∈ heatCylinder Ω T, u z = M →
      ∃ r > 0, EqOn u (fun _ => M) (heatBall n r z))
    {x y : P201Specs.Space n} (hseg : segment ℝ x y ⊆ Ω)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ T)
    (hmax : u (x, t) = M) : u (y, s) = M := by
  let γ : ℝ → SpaceTime n := fun a => (AffineMap.lineMap x y a, (1-a)*t + a*s)
  have hγ : Continuous γ := by dsimp [γ, AffineMap.lineMap_apply_module]; fun_prop
  have hγmem : MapsTo γ (Icc 0 1) (heatCylinder Ω T) := by
    intro a ha
    refine ⟨hseg (lineMap_mem_segment ℝ x y ha), ?_, ?_⟩
    · dsimp [γ]
      nlinarith [ha.1, ha.2]
    · dsimp [γ]
      nlinarith [ha.1, ha.2]
  have hcomp : ContinuousOn (u ∘ γ) (Icc 0 1) := huc.comp hγ.continuousOn hγmem
  let A : Set ℝ := {a | u (γ a) = M}
  have hclosed : IsClosed (A ∩ Icc 0 1) := by
    have hc := hcomp.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := M))
    convert hc using 1
    ext a
    simp only [A, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
      Function.comp_apply, and_comm]
  have hstart : (0 : ℝ) ∈ A := by simpa [A, γ] using hmax
  have hstep : ∀ a ∈ A ∩ Ico 0 1, A ∈ 𝓝[>] a := by
    intro a ha
    have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.2.1, ha.2.2.le⟩
    obtain ⟨r, hr, heq⟩ := hlocal (γ a) (hγmem ha') ha.1
    let v : P201Specs.Space n := (t-s)⁻¹ • (y-x)
    obtain ⟨δ, hδ, hball⟩ := backward_ray_mem_heatBall hn hr (γ a) v
    have htime : 0 < t-s := sub_pos.mpr hst
    have hI : Ioo a (a + δ / (t-s)) ⊆ A := by
      intro b hb
      have hτ : 0 < (b-a)*(t-s) := mul_pos (sub_pos.mpr hb.1) htime
      have hτδ : (b-a)*(t-s) < δ := by
        apply (lt_div_iff₀ htime).mp
        linarith [hb.2]
      have he := heq (hball ((b-a)*(t-s)) hτ hτδ)
      have hray : ((γ a).1 + ((b-a)*(t-s)) • v,
          (γ a).2 - (b-a)*(t-s)) = γ b := by
        apply Prod.ext
        · dsimp [γ, v]
          rw [smul_smul, mul_assoc, mul_inv_cancel₀ htime.ne', mul_one]
          simp only [AffineMap.lineMap_apply_module']
          module
        · dsimp [γ]
          ring
      rwa [hray] at he
    exact mem_of_superset (Ioo_mem_nhdsGT (lt_add_of_pos_right a (div_pos hδ htime))) hI
  have hfull := hclosed.Icc_subset_of_forall_mem_nhdsWithin hstart hstep
  have hend := hfull (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [A, γ] using hend

/-- The geometric and topological propagation argument. No boundedness of the
spatial domain or information on its boundary is used. -/
lemma maximum_from_local_heatBalls {n : ℕ} (hn : 1 ≤ n)
    {Ω : Set (P201Specs.Space n)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {T : ℝ} {u : SpaceTime n → ℝ} {M : ℝ}
    (huc : ContinuousOn u (heatCylinder Ω T))
    (hlocal : ∀ z ∈ heatCylinder Ω T, u z = M →
      ∃ r > 0, EqOn u (fun _ => M) (heatBall n r z))
    {x₀ : P201Specs.Space n} (hx₀ : x₀ ∈ Ω) {t₀ : ℝ}
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hmax : u (x₀, t₀) = M) :
    ∀ x ∈ Ω, ∀ t : ℝ, 0 < t → t ≤ t₀ → u (x, t) = M := by
  let P : P201Specs.Space n → P201Specs.Space n → Prop := fun x y =>
    ∀ s t : ℝ, 0 < s → s < t → t ≤ T → u (x,t) = M → u (y,s) = M
  have htrans : ∀ x y z, x ∈ Ω → y ∈ Ω → z ∈ Ω →
      P x y → P y z → P x z := by
    intro x y z _ _ _ hxy hyz s t hs hst ht he
    have hmid : s < (s+t)/2 ∧ (s+t)/2 < t := by constructor <;> linarith
    exact hyz s ((s+t)/2) hs hmid.1 (hmid.2.le.trans ht)
      (hxy ((s+t)/2) t (by linarith) hmid.2 ht he)
  have hnear : ∀ x ∈ Ω, ∀ᶠ y in 𝓝[Ω] x, P x y ∧ P y x := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
    have hnb : ball x ε ∈ 𝓝[Ω] x :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hε)
    filter_upwards [hnb] with y hy
    have hxball : x ∈ ball x ε := mem_ball_self hε
    have hxy : segment ℝ x y ⊆ Ω :=
      ((convex_ball x ε).segment_subset hxball hy).trans hεΩ
    have hyx : segment ℝ y x ⊆ Ω := by simpa only [segment_symm] using hxy
    exact ⟨fun s t hs hst ht hm => maximum_propagates_on_segment hn huc hlocal hxy hs hst ht hm,
      fun s t hs hst ht hm => maximum_propagates_on_segment hn huc hlocal hyx hs hst ht hm⟩
  intro x hx
  have hrel : P x₀ x := hconn.induction₂' P hnear htrans hx₀ hx
  have hpast : EqOn (fun t => u (x,t)) (fun _ => M) (Ioo 0 t₀) := by
    intro t ht
    exact hrel t t₀ ht.1 ht.2 ht₀T hmax
  have hslice : ContinuousOn (fun t => u (x,t)) (Ioc 0 t₀) := by
    apply huc.comp (show ContinuousOn (fun t : ℝ => (x,t)) (Ioc 0 t₀) by fun_prop)
    intro t ht
    exact ⟨hx, ht.1, ht.2.trans ht₀T⟩
  have hall := hpast.of_subset_closure hslice continuousOn_const Ioo_subset_Ioc_self
    (by rw [closure_Ioo ht₀.ne]; exact Ioc_subset_Icc_self)
  intro t ht htt₀
  exact hall ⟨ht, htt₀⟩

/-- Analytic assembly: a normalized heat-ball mean value property and continuity
imply the strong maximum principle. -/
lemma maximum_from_cylinder_meanValue {n : ℕ} (hn : 1 ≤ n)
    {Ω : Set (P201Specs.Space n)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {T : ℝ} {u : SpaceTime n → ℝ}
    (huc : ContinuousOn u (heatCylinder Ω T))
    (hmean : ∀ r : ℝ, 0 < r → ∀ z₀ ∈ heatCylinder Ω T,
      closure (heatBall n r z₀) ⊆ heatCylinder Ω T → HeatBallMeanValueIdentity u r z₀)
    {M : ℝ} (hbound : ∀ z ∈ heatCylinder Ω T, u z ≤ M)
    {x₀ : P201Specs.Space n} (hx₀ : x₀ ∈ Ω) {t₀ : ℝ}
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hmax : u (x₀,t₀) = M) :
    ∀ x ∈ Ω, ∀ t : ℝ, 0 < t → t ≤ t₀ → u (x,t) = M := by
  apply maximum_from_local_heatBalls hn hΩ hconn huc ?_ hx₀ ht₀ ht₀T hmax
  intro z hz hm
  obtain ⟨r, hr, hc⟩ := exists_heatBall_closure_in_cylinder hn hΩ hz
  exact ⟨r, hr, eqOn_heatBall_of_meanValue_maximum hn hr (huc.mono hc)
    (hmean r hr z hz hc) (fun w hw => hbound w (hc (subset_closure hw))) hm⟩

/-- Strong maximum principle, including the attained time slice. -/
theorem strongMaximum : P201Specs.Heat.strongMaximumStatement := by
  intro n hn Ω hΩ hconn T _ u huc hu M hbound x₀ hx₀ t₀ ht₀ ht₀T hmax
  apply maximum_from_cylinder_meanValue hn hΩ hconn.isPreconnected huc ?_
    hbound hx₀ ht₀ ht₀T hmax
  intro r hr z hz hc
  exact caloric_cylinder_meanValue hn huc hu hr hz.2.2 hc

/-- Strong minimum principle by sign change in the mean-value formula. -/
theorem strongMinimum : P201Specs.Heat.strongMinimumStatement := by
  intro n hn Ω hΩ hconn T _ u huc hu m hbound x₀ hx₀ t₀ ht₀ ht₀T hmin
  have hmean : ∀ r : ℝ, 0 < r → ∀ z₀ ∈ heatCylinder Ω T,
      closure (heatBall n r z₀) ⊆ heatCylinder Ω T →
      HeatBallMeanValueIdentity (fun z => -u z) r z₀ := by
    intro r hr z₀ hz₀ hc
    apply (meanValueIdentity_iff_weighted _ r z₀).mpr
    have he := (meanValueIdentity_iff_weighted u r z₀).mp
      (caloric_cylinder_meanValue hn huc hu hr hz₀.2.2 hc)
    simpa only [neg_mul, integral_neg] using congrArg Neg.neg he
  have hneg := maximum_from_cylinder_meanValue hn hΩ hconn.isPreconnected huc.neg hmean
    (M := -m) (fun z hz => neg_le_neg (hbound z hz)) hx₀ ht₀ ht₀T
    (show -u (x₀,t₀) = -m by rw [hmin])
  intro x hx t ht htt₀
  exact neg_injective (hneg x hx t ht htt₀)

end P201.Heat
