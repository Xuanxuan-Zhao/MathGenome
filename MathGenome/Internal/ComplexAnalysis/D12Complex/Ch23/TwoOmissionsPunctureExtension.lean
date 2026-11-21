import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.TwoOmissionsPunctureExtension
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.OmittedValueNormality
import Mathlib.Analysis.Complex.AbsMax
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SingularityGrowth
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
Two omitted finite values exclude an essential isolated singularity.
We rescale the punctured disk, apply omitted-value normality, and transfer
bounds on a fixed compact circle to shrinking circles. The maximum principle
on closed annuli fills the intervening punctured neighborhood. In the infinity
case the same argument at every positive tolerance proves that the reciprocal
tends to zero. The canonical growth classification then supplies a pole of
finite positive order.
-/
noncomputable section
open Set Filter Metric
open scoped Topology

namespace D12Complex.TwoOmissionsPunctureExtension



lemma puncturedDisk_open (a : ℂ) (R : ℝ) : IsOpen (puncturedDisk a R) := by
  have he : puncturedDisk a R = ball a R \ {a} := by
    ext z
    simp [puncturedDisk, norm_pos_iff, sub_ne_zero, and_comm, dist_eq_norm]
  rw [he]
  exact isOpen_ball.sdiff isClosed_singleton

lemma puncturedDisk_domain (R : ℝ) (hR : 0 < R) : IsDomain (puncturedDisk 0 R) := by
  have hs : IsPreconnected (sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1
  have hp : IsPreconnected (Ioo (0 : ℝ) R ×ˢ sphere (0 : ℂ) 1) :=
    isPreconnected_Ioo.prod hs
  have him : (fun p : ℝ × ℂ => p.1 • p.2) ''
      (Ioo 0 R ×ˢ sphere (0 : ℂ) 1) = puncturedDisk 0 R := by
    ext z
    constructor
    · rintro ⟨⟨r, w⟩, ⟨hr, hw⟩, rfl⟩
      have hn : ‖w‖ = 1 := by simpa using hw
      change 0 < ‖r • w - (0 : ℂ)‖ ∧ ‖r • w - (0 : ℂ)‖ < R
      rw [sub_zero, norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr.1]
      exact hr
    · intro hz
      have hz' : 0 < ‖z‖ ∧ ‖z‖ < R := by simpa [puncturedDisk] using hz
      refine ⟨(‖z‖, ‖z‖⁻¹ • z), ⟨hz', ?_⟩, ?_⟩
      · simp [inv_mul_cancel₀ hz'.1.ne']
      · change ‖z‖ • ((‖z‖⁻¹ : ℝ) • z) = z
        rw [smul_smul, mul_inv_cancel₀ hz'.1.ne', one_smul]
  refine ⟨?_, puncturedDisk_open 0 R, ?_⟩
  · refine ⟨(R/2 : ℝ), ?_⟩
    change 0 < ‖((R/2 : ℝ) : ℂ) - 0‖ ∧ ‖((R/2 : ℝ) : ℂ) - 0‖ < R
    rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hR)]
    exact ⟨half_pos hR, half_lt_self hR⟩
  · rw [← him]
    exact hp.image _ (by fun_prop)

lemma rescale_mem (a : ℂ) (R : ℝ) {z : ℂ} (hz : z ∈ puncturedDisk 0 R)
    (n : ℕ) : a + z / (n + 1 : ℂ) ∈ puncturedDisk a R := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hn1 : 1 ≤ (n + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnorm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    norm_cast
  have hz' : 0 < ‖z‖ ∧ ‖z‖ < R := by simpa [puncturedDisk] using hz
  simp only [puncturedDisk, mem_ofPred_eq, add_sub_cancel_left, norm_div, hnorm]
  exact ⟨div_pos hz'.1 hn, (div_le_self (norm_nonneg _) hn1).trans_lt hz'.2⟩

lemma rescale_holomorphic (a : ℂ) (R : ℝ) {f : ℂ → ℂ}
    (hf : HolomorphicOn (puncturedDisk a R) f) (n : ℕ) :
    HolomorphicOn (puncturedDisk 0 R) (fun z => f (a + z / (n + 1 : ℂ))) := by
  refine ⟨puncturedDisk_open 0 R, fun z hz => ?_⟩
  exact (hf.2 _ (rescale_mem a R hz n)).comp z
    ((differentiableAt_const a).add (differentiableAt_id.div_const _))

lemma rescale_sphere_inverse (a : ℂ) (r : ℝ) (n : ℕ) {z : ℂ}
    (hz : z ∈ sphere a (r / (n + 1 : ℝ))) :
    (z - a) * (n + 1 : ℂ) ∈ sphere (0 : ℂ) r ∧
      a + ((z - a) * (n + 1 : ℂ)) / (n + 1 : ℂ) = z := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hnr : (n + 1 : ℝ) ≠ 0 := by positivity
  have hnorm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by norm_cast
  constructor
  · rw [mem_sphere_iff_norm] at hz ⊢
    rw [sub_zero, norm_mul, hnorm, hz, div_mul_cancel₀ r hnr]
  · field_simp
    ring

lemma rescale_sphere_bound (a : ℂ) (r M : ℝ) (n : ℕ) {f : ℂ → ℂ}
    (hb : ∀ z ∈ sphere (0 : ℂ) r, ‖f (a + z / (n + 1 : ℂ))‖ ≤ M) :
    ∀ z ∈ sphere a (r / (n + 1 : ℝ)), ‖f z‖ ≤ M := by
  intro z hz
  obtain ⟨hmem, heq⟩ := rescale_sphere_inverse a r n hz
  simpa [heq] using hb _ hmem

lemma shrinking_radii_pos {r : ℝ} (hr : 0 < r) (φ : ℕ → ℕ) (n : ℕ) :
    0 < r / (φ n + 1 : ℝ) := by positivity

lemma shrinking_radii_tendsto {r : ℝ} (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun n => r / (φ n + 1 : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (φ n + 1 : ℝ)) atTop atTop :=
    by
      apply Filter.Tendsto.atTop_add
      · exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
      · exact tendsto_const_nhds
  simpa using tendsto_const_nhds.div_atTop hn

lemma sphere_subset_puncturedDisk {a : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    sphere a r ⊆ puncturedDisk a R := by
  intro z hz
  have he : ‖z - a‖ = r := mem_sphere_iff_norm.mp hz
  exact ⟨he.symm ▸ hr, he.symm ▸ hrR⟩

lemma shrinking_radii_strictAnti {r : ℝ} (hr : 0 < r)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    StrictAnti (fun n => r / (φ n + 1 : ℝ)) := by
  intro m n hmn
  apply div_lt_div_of_pos_left hr (by positivity)
  exact_mod_cast Nat.succ_lt_succ (hφ hmn)

lemma shrinking_radii_le {r : ℝ} (hr : 0 ≤ r) (φ : ℕ → ℕ) (n : ℕ) :
    r / (φ n + 1 : ℝ) ≤ r := by
  apply div_le_self hr
  linarith [Nat.cast_nonneg (α := ℝ) (φ n)]

lemma rescale_omits {a : ℂ} {R : ℝ} {f : ℂ → ℂ} {c : ℂ}
    (hf : ∀ z ∈ puncturedDisk a R, f z ≠ c) (n : ℕ) :
    ∀ z ∈ puncturedDisk 0 R, f (a + z / (n + 1 : ℂ)) ≠ c := by
  intro z hz
  exact hf _ (rescale_mem a R hz n)




lemma norm_le_on_closed_annulus {f : ℂ → ℂ} {a : ℂ} {R ri ro M : ℝ}
    (hd : ∀ z, 0 < ‖z-a‖ → ‖z-a‖ < R → DifferentiableAt ℂ f z)
    (hri : 0 < ri) (hro : ro < R)
    (hbi : ∀ z ∈ sphere a ri, ‖f z‖ ≤ M)
    (hbo : ∀ z ∈ sphere a ro, ‖f z‖ ≤ M)
    {z : ℂ} (hiz : ri ≤ ‖z-a‖) (hoz : ‖z-a‖ ≤ ro) : ‖f z‖ ≤ M := by
  let S := closedBall a ro ∩ (ball a ri)ᶜ
  have hSc : IsClosed S := isClosed_closedBall.inter isOpen_ball.isClosed_compl
  have hSsub : S ⊆ {w : ℂ | 0 < ‖w-a‖ ∧ ‖w-a‖ < R} := by
    intro w hw
    have hi : ri ≤ ‖w-a‖ := by simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hw.2
    have ho : ‖w-a‖ ≤ ro := mem_closedBall_iff_norm.mp hw.1
    exact ⟨hri.trans_le hi, ho.trans_lt hro⟩
  have hdiff : DiffContOnCl ℂ f S := by
    refine ⟨fun w hw => (hd w (hSsub hw).1 (hSsub hw).2).differentiableWithinAt, ?_⟩
    rw [hSc.closure_eq]
    exact fun w hw => (hd w (hSsub hw).1 (hSsub hw).2).continuousAt.continuousWithinAt
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_closedBall.subset inter_subset_left) hdiff
  · intro w hw
    rcases frontier_inter_subset (closedBall a ro) (ball a ri)ᶜ hw with hw | hw
    · exact hbo w (frontier_closedBall_subset_sphere hw.1)
    · exact hbi w (frontier_ball_subset_sphere (by simpa only [frontier_compl] using hw.2))
  · apply subset_closure
    exact ⟨mem_closedBall_iff_norm.mpr hoz,
      by simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hiz⟩

lemma bounded_on_puncturedDisk_of_shrinking_spheres {f : ℂ → ℂ} {a : ℂ} {R M : ℝ}
    (hd : ∀ z, 0 < ‖z-a‖ → ‖z-a‖ < R → DifferentiableAt ℂ f z)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n ∧ r n < R)
    (ht : Tendsto r atTop (𝓝 0))
    (hb : ∀ n z, z ∈ sphere a (r n) → ‖f z‖ ≤ M) :
    ∀ z, 0 < ‖z-a‖ → ‖z-a‖ < r 0 → ‖f z‖ ≤ M := by
  intro z hz hz0
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const hz).exists
  exact norm_le_on_closed_annulus hd (hr n).1 (hr 0).2 (hb n) (hb 0) hn.le hz0.le

lemma eventually_bounded_of_shrinking_spheres {f : ℂ → ℂ} {a : ℂ} {R M : ℝ}
    (hd : ∀ z, 0 < ‖z-a‖ → ‖z-a‖ < R → DifferentiableAt ℂ f z)
    (r : ℕ → ℝ) (hr : ∀ᶠ n in atTop, 0 < r n ∧ r n < R)
    (ht : Tendsto r atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, ∀ z ∈ sphere a (r n), ‖f z‖ ≤ M) :
    ∀ᶠ z in 𝓝[≠] a, ‖f z‖ ≤ M := by
  obtain ⟨N, hNr, hNb⟩ := (hr.and hb).exists
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hNr.1), self_mem_nhdsWithin] with z hz hza
  have hzpos : 0 < ‖z-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  obtain ⟨n, ⟨hnr, hnb⟩, hn⟩ := ((hr.and hb).and (ht.eventually_lt_const hzpos)).exists
  exact norm_le_on_closed_annulus hd hnr.1 hNr.2 hnb hNb hn.le
    (mem_ball_iff_norm.mp hz).le

lemma removable_of_shrinking_spheres {f : ℂ → ℂ} {a : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : D12Complex.HolomorphicOn (D12Complex.puncturedDisk a R) f)
    (r : ℕ → ℝ) (hr : ∀ᶠ n in atTop, 0 < r n ∧ r n < R)
    (ht : Tendsto r atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, ∀ z ∈ sphere a (r n), ‖f z‖ ≤ M) :
    D12Complex.RemovableSingularityAt f a := by
  exact D12Complex.SingularityGrowth.removable_of_bounded ⟨R, hR, hf⟩
    ⟨M, eventually_bounded_of_shrinking_spheres (fun z hz hzR => hf.2 z ⟨hz, hzR⟩) r hr ht hb⟩

lemma tendsto_zero_of_shrinking_spheres {f : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hf : D12Complex.HolomorphicOn (D12Complex.puncturedDisk a R) f)
    (r : ℕ → ℝ) (hr : ∀ᶠ n in atTop, 0 < r n ∧ r n < R)
    (ht : Tendsto r atTop (𝓝 0))
    (hsmall : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ sphere a (r n), ‖f z‖ ≤ ε) :
    Tendsto f (𝓝[≠] a) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hb := eventually_bounded_of_shrinking_spheres
    (fun z hz hzR => hf.2 z ⟨hz, hzR⟩) r hr ht (hsmall (ε / 2) (by positivity))
  filter_upwards [hb] with z hz
  simpa only [dist_zero_right] using hz.trans_lt (half_lt_self hε)



lemma pole_of_reciprocal_tendsto_zero {f : ℂ → ℂ} {a : ℂ}
    (hi : IsolatedSingularityAt f a)
    (hne : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0)
    (hinv : Tendsto (fun z => (f z)⁻¹) (𝓝[≠] a) (𝓝 0)) :
    PoleAt f a := by
  apply (SingularityGrowth.pole_iff f a hi).mp
  apply tendsto_norm_atTop_iff_cobounded.mpr
  have hne' : ∀ᶠ z in 𝓝[≠] a, (f z)⁻¹ ∈ ({0} : Set ℂ)ᶜ := by
    filter_upwards [hne] with z hz
    exact inv_ne_zero hz
  have h0 : Tendsto (fun z => (f z)⁻¹) (𝓝[≠] a) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hinv, hne'⟩
  simpa only [Function.comp_def, inv_inv] using tendsto_inv₀_nhdsNE_zero.comp h0

lemma removable_of_affine {f : ℂ → ℂ} {a u c : ℂ}
    (hi : IsolatedSingularityAt f a)
    (hr : RemovableSingularityAt (fun z => (f z-u)/c) a) (hc : c ≠ 0) :
    RemovableSingularityAt f a := by
  obtain ⟨L, hL⟩ := (SingularityGrowth.removable_iff_limit hr.1).mp hr
  apply (SingularityGrowth.removable_iff_limit hi).mpr
  refine ⟨L*c+u, ?_⟩
  have h := (hL.mul_const c).add_const u
  simpa only [div_mul_cancel₀ _ hc, sub_add_cancel] using h

lemma pole_of_affine {f : ℂ → ℂ} {a u c : ℂ}
    (hi : IsolatedSingularityAt f a)
    (hp : PoleAt (fun z => (f z-u)/c) a) (hc : c ≠ 0) :
    PoleAt f a := by
  have hi' : IsolatedSingularityAt (fun z => (f z-u)/c) a := by
    obtain ⟨m, hm⟩ := hp
    exact hm.2.1
  have hh := (SingularityGrowth.pole_iff _ _ hi').mpr hp
  have ht := tendsto_norm_atTop_iff_cobounded.mp hh
  have h := (tendsto_add_const_cobounded u).comp
    ((Filter.tendsto_mul_right_cobounded hc).comp ht)
  apply (SingularityGrowth.pole_iff f a hi).mp
  apply tendsto_norm_atTop_iff_cobounded.mpr
  simpa only [Function.comp_def, div_mul_cancel₀ _ hc, sub_add_cancel] using h



lemma norm_inv_lt_of_chordal_infty {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : Chordal.chordal sphereInfty (sphereFinite z) < ε / (1+ε)) :
    ‖z⁻¹‖ < ε := by
  by_cases hz : z = 0
  · simpa [hz] using hε
  have hx : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hs : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := by positivity
  have hsle : Real.sqrt (1 + ‖z‖ ^ 2) ≤ 1 + ‖z‖ := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [norm_nonneg z]
  change 1 / Real.sqrt (1 + ‖z‖ ^ 2) < ε / (1 + ε) at h
  have hprod := (div_lt_div_iff₀ hs (by positivity : 0 < 1+ε)).mp h
  by_contra hfail
  have hge : ε ≤ 1 / ‖z‖ := by simpa only [norm_inv, one_div] using le_of_not_gt hfail
  have hmul : ε * ‖z‖ ≤ 1 := (le_div_iff₀ hx).mp hge
  have := mul_le_mul_of_nonneg_left hsle hε.le
  nlinarith

lemma reciprocal_uniform_of_spherical_infty {Ω K : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hlim : SphericalLimits.SphericalLocallyUniformOn
      (fun n z => sphereFinite (F n z)) (fun _ => sphereInfty) Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun n z => (F n z)⁻¹) (fun _ => 0) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim K hK hKΩ (ε/(1+ε)) (by positivity)] with n hn
  intro z hz
  simpa only [dist_zero_left] using norm_inv_lt_of_chordal_infty hε (hn z hz)




lemma eventually_bounded_on_compact {Ω K : Set ℂ} {F : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hh : HolomorphicOn Ω h)
    (hlim : TendstoLocallyUniformlyOn F h atTop Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, ‖F n z‖ ≤ M := by
  have hc : ContinuousOn (fun z => ‖h z‖) K := fun z hz =>
    (hh.2 z (hKΩ hz)).continuousAt.norm.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlim.mono hKΩ)
  refine ⟨M + 1, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with n hn
  intro z hz
  have hn' : ‖F n z - h z‖ < 1 := by
    simpa [dist_eq_norm, norm_sub_rev] using hn z hz
  calc
    ‖F n z‖ ≤ ‖F n z - h z‖ + ‖h z‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + M := add_le_add hn'.le (hM (mem_image_of_mem _ hz))
    _ = M + 1 := add_comm _ _


/-- Normality on the rescaled punctured disk yields either a bounded function
or a reciprocal tending to zero at the original puncture. -/
theorem zero_one_puncture_extension :
    Specs.D12Complex.Ch23.TwoOmissionsPunctureExtension.zero_one_puncture_extension_type := by
  intro a R f hR hf hzero hone
  let Ω := puncturedDisk (0 : ℂ) R
  let F : ℕ → ℂ → ℂ := fun n z => f (a + z / (n + 1 : ℂ))
  have hΩ : IsDomain Ω := puncturedDisk_domain R hR
  have hF : ∀ n, HolomorphicOn Ω (F n) := fun n => rescale_holomorphic a R hf n
  have hF0 : ∀ n z, z ∈ Ω → F n z ≠ 0 := rescale_omits hzero
  have hF1 : ∀ n z, z ∈ Ω → F n z ≠ 1 := rescale_omits hone
  obtain ⟨φ, hφ, hlim⟩ := OmittedValueNormality.subsequence Ω F hΩ hF hF0 hF1
  let r : ℕ → ℝ := fun n => (R / 2) / (φ n + 1 : ℝ)
  have hr : ∀ᶠ n in atTop, 0 < r n ∧ r n < R := by
    exact Eventually.of_forall fun n =>
      ⟨shrinking_radii_pos (half_pos hR) φ n,
       (shrinking_radii_le (half_pos hR).le φ n).trans_lt (half_lt_self hR)⟩
  have ht : Tendsto r atTop (𝓝 0) := shrinking_radii_tendsto φ hφ
  have hK : sphere (0 : ℂ) (R / 2) ⊆ Ω :=
    sphere_subset_puncturedDisk (half_pos hR) (half_lt_self hR)
  rcases hlim with ⟨h, hh, hord, _⟩ | hinfty
  · obtain ⟨M, hM⟩ := eventually_bounded_on_compact hh hord
      (isCompact_sphere (0 : ℂ) (R / 2)) hK
    left
    apply removable_of_shrinking_spheres hR hf r hr ht
    filter_upwards [hM] with n hn
    exact rescale_sphere_bound a (R / 2) M (φ n) hn
  · have hu := reciprocal_uniform_of_spherical_infty hinfty
      (isCompact_sphere (0 : ℂ) (R / 2)) hK
    have hi : HolomorphicOn (puncturedDisk a R) (fun z => (f z)⁻¹) :=
      OmittedValueNormality.holomorphic_inverse hf hzero
    have hz : Tendsto (fun z => (f z)⁻¹) (𝓝[≠] a) (𝓝 0) := by
      apply tendsto_zero_of_shrinking_spheres hi r hr ht
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with n hn
      apply rescale_sphere_bound a (R / 2) ε (φ n)
      intro z hzs
      exact (by simpa only [dist_zero_left] using hn z hzs :
        ‖(F (φ n) z)⁻¹‖ < ε).le
    right
    apply pole_of_reciprocal_tendsto_zero ⟨R, hR, hf⟩ _ hz
    filter_upwards [SingularityGrowth.puncturedDisk_mem (a := a) hR] with z hzp
    exact hzero z hzp

/-- Normalize the two distinct omitted values, and transfer each possible
extension back to the original function. -/
theorem two_omissions_puncture_extension :
    Specs.D12Complex.Ch23.TwoOmissionsPunctureExtension.two_omissions_puncture_extension_type := by
  intro a R f u v hR hf huv hu hv
  have hc : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  let g : ℂ → ℂ := fun z => (f z - u) / (v - u)
  have hg : HolomorphicOn (puncturedDisk a R) g :=
    ⟨hf.1, fun z hz => ((hf.2 z hz).sub_const u).div_const (v-u)⟩
  have hg0 : ∀ z ∈ puncturedDisk a R, g z ≠ 0 := by
    intro z hz
    exact div_ne_zero (sub_ne_zero.mpr (hu z hz)) hc
  have hg1 : ∀ z ∈ puncturedDisk a R, g z ≠ 1 := by
    intro z hz he
    have he' : f z - u = v - u := (div_eq_one_iff_eq hc).mp he
    apply hv z hz
    simpa only [sub_add_cancel] using congrArg (fun w : ℂ => w + u) he'
  rcases zero_one_puncture_extension a R g hR hg hg0 hg1 with hrem | hpole
  · exact Or.inl (removable_of_affine ⟨R, hR, hf⟩ hrem hc)
  · exact Or.inr (pole_of_affine ⟨R, hR, hf⟩ hpole hc)

/-- The result applies to the canonical essential-singularity predicate. -/
theorem not_essential_of_two_omissions :
    Specs.D12Complex.Ch23.TwoOmissionsPunctureExtension.not_essential_of_two_omissions_type := by
  intro a R f u v hR hf huv hu hv he
  rcases two_omissions_puncture_extension a R f u v hR hf huv hu hv with hrem | hpole
  · exact he.2.1 hrem
  · exact he.2.2 hpole

end D12Complex.TwoOmissionsPunctureExtension
