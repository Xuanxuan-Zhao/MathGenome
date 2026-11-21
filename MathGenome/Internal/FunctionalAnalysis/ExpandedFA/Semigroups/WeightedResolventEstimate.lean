import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.WeightedResolventEstimate
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff ComplexInnerProductSpace Topology

namespace ExpandedFA.Semigroups.WeightedResolvent
open Unbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Agreement with the Bochner integral transform in arbitrary Hilbert spaces.
The vector-valued fundamental lemma avoids any global separability assumption. -/
theorem hilbert_integral_agreement : Spec.HilbertIntegralAgreement := by
  intro H _ _ _ f h1 h2
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h1
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (Lp.fourierTransformₗᵢ ℝ H (h2.toLp f))).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : SchwartzMap ℝ ℂ := hs'.toSchwartzMap hg'
  have hd := congrArg (fun u : TemperedDistribution ℝ H => u φ)
    (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  have hp : (∫ x, (𝓕 φ) x • (h2.toLp f) x) = ∫ x, (𝓕 φ) x • f x := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  have hpair : (∫ x, φ x • (𝓕 f) x) = ∫ x, (𝓕 φ) x • f x := by
    simpa only [SchwartzMap.fourier_coe, flip_innerₗ] using!
      (VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner φ.integrable h1).symm
  calc
    (∫ x, g x • (Lp.fourierTransformₗᵢ ℝ H (h2.toLp f)) x) =
        ∫ x, φ x • (Lp.fourierTransformₗᵢ ℝ H (h2.toLp f)) x := by
          simp [φ]
    _ = ∫ x, (𝓕 φ) x • (h2.toLp f) x := hd.symm
    _ = ∫ x, (𝓕 φ) x • f x := hp
    _ = ∫ x, φ x • (𝓕 f) x := hpair.symm
    _ = ∫ x, g x • (𝓕 f) x := by simp [φ]
  all_goals rfl

/-- The native Hilbert-valued Plancherel isometry preserves the energy integral. -/
lemma l2_integral_norm_sq (f : Lp H 2 (volume : Measure ℝ)) :
    (∫ s, ‖(Lp.fourierTransformₗᵢ ℝ H f) s‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
  have h := (Lp.fourierTransformₗᵢ ℝ H).inner_map_map f f
  have hnorm (g : Lp H 2 (volume : Measure ℝ)) :
      (inner ℂ g g).re = ∫ t, ‖g t‖ ^ 2 := by
    change RCLike.re (inner ℂ g g) = _
    rw [L2.inner_def, ← integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) g g)]
    simp only [inner_self_eq_norm_sq]
  simpa only [hnorm] using congrArg Complex.re h

theorem hilbert_integral_plancherel : Spec.HilbertIntegralPlancherel := by
  intro H _ _ _ f h1 h2
  have ha := hilbert_integral_agreement f h1 h2
  refine ⟨(memLp_congr_ae ha).mp (Lp.memLp _), ?_⟩
  calc
    (∫ s, ‖𝓕 f s‖ ^ 2) =
        ∫ s, ‖(Lp.fourierTransformₗᵢ ℝ H (h2.toLp f)) s‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ha] with s hs
      rw [hs]
    _ = ∫ t, ‖(h2.toLp f) t‖ ^ 2 := l2_integral_norm_sq _
    _ = ∫ t, ‖f t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with t ht
      rw [ht]

/-- A closed operator commutes with the Bochner integral of an integrable graph.
Both coordinates are integrated in the ambient Hilbert space. -/
theorem integral_graph : Spec.IntegralGraph := by
  intro H _ _ _ G hG w hD hw hGw
  let S := G.graph
  have : IsClosed (S : Set (H × H)) := hG
  have hi := hw.prodMk hGw
  have hq : S.mkQL (∫ t, (w t, G ⟨w t, hD t⟩)) = 0 := by
    rw [← S.mkQL.integral_comp_comm hi]
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro t
    change S.mkQ (w t, G ⟨w t, hD t⟩) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr
      (G.mem_graph_iff.mpr ⟨⟨w t, hD t⟩, rfl, rfl⟩)
  have hm : (∫ t, (w t, G ⟨w t, hD t⟩)) ∈ S :=
    (Submodule.Quotient.mk_eq_zero S).mp hq
  rw [integral_pair hw hGw] at hm
  rcases G.mem_graph_iff.mp hm with ⟨x, hx, hy⟩
  change (x : H) = ∫ t, w t at hx
  refine ⟨hx ▸ x.property, ?_⟩
  have he : (⟨∫ t, w t, hx ▸ x.property⟩ : G.domain) = x := Subtype.ext hx.symm
  rw [he]
  exact hy

theorem fourier_graph : Spec.FourierGraph := by
  intro H _ _ _ G hG w hD hw hGw s
  let a (t : ℝ) : ℂ := Real.fourierChar (-inner ℝ t s)
  let u (t : ℝ) : H := a t • w t
  have hDu : ∀ t, u t ∈ G.domain := fun t => G.domain.smul_mem (a t) (hD t)
  have hmap (t : ℝ) : G ⟨u t, hDu t⟩ = a t • G ⟨w t, hD t⟩ := by
    exact G.map_smul (a t) ⟨w t, hD t⟩
  have hu : Integrable u := by
    simpa only [u, a, Circle.smul_def] using
      (Real.fourierIntegral_convergent_iff s).mpr hw
  have hGu : Integrable (fun t => G ⟨u t, hDu t⟩) := by
    simp_rw [hmap]
    simpa only [a, Circle.smul_def] using
      (Real.fourierIntegral_convergent_iff s).mpr hGw
  have hi := integral_graph G hG u hDu hu hGu
  simp_rw [hmap] at hi
  exact hi

theorem resolvent_lower_bound : Spec.ResolventLowerBound := by
  intro H _ _ _ G ξ d hb τ x
  rcases hb with ⟨hd, hb⟩
  rcases hb τ with ⟨hρ, hnorm⟩
  let R := Unbounded.OperatorDomainsSpec.resolventValue (ξ + Complex.I * τ) G
  have hinv : R ((ξ + Complex.I * τ : ℂ) • (x : H) - G x) = (x : H) := by
    change Unbounded.OperatorDomainsSpec.resolventValue _ _ _ = _
    change Nonempty (Unbounded.ResolventInverse G (ξ + Complex.I * τ)) at hρ
    rw [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left hρ]
    exact hρ.some.left_inverse x
  have h := R.le_opNorm ((ξ + Complex.I * τ : ℂ) • (x : H) - G x)
  rw [hinv] at h
  have h' : ‖(x : H)‖ ≤ (1 / d) * ‖(ξ + Complex.I * τ : ℂ) • (x : H) - G x‖ :=
    h.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  calc
    d * ‖(x : H)‖ ≤ d * ((1 / d) * ‖(ξ + Complex.I * τ : ℂ) • (x : H) - G x‖) :=
      mul_le_mul_of_nonneg_left h' hd.le
    _ = _ := by field_simp

theorem fourier_coercivity : Spec.FourierCoercivity := by
  intro H _ _ _ G ξ d hb f r hf1 hf2 hr1 hr2 hid
  obtain ⟨hFf, hPf⟩ := hilbert_integral_plancherel f hf1 hf2
  obtain ⟨hFr, hPr⟩ := hilbert_integral_plancherel r hr1 hr2
  have hp (s : ℝ) : d ^ 2 * ‖𝓕 f s‖ ^ 2 ≤ ‖𝓕 r s‖ ^ 2 := by
    obtain ⟨hD, hid⟩ := hid s
    have hl := resolvent_lower_bound G ξ d hb (2 * Real.pi * s) ⟨𝓕 f s, hD⟩
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hl
    rw [← hid] at hl
    have hn : 0 ≤ d * ‖𝓕 f s‖ := mul_nonneg hb.1.le (norm_nonneg _)
    have hs := mul_self_le_mul_self hn hl
    nlinarith
  have hi : d ^ 2 * (∫ s, ‖𝓕 f s‖ ^ 2) ≤ ∫ s, ‖𝓕 r s‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono ((hFf.integrable_norm_pow (by norm_num)).const_mul _)
      (hFr.integrable_norm_pow (by norm_num)) hp
  rwa [hPf, hPr] at hi

/-- The squared L² norm after conjugation is precisely the source's weight. -/
theorem weighted_energy (ξ : ℝ) (w : ℝ → H) :
    (∫ t, ‖weighted ξ w t‖ ^ 2) = energy ξ w := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [weighted, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-ξ * t) = -2 * ξ * t by ring, mul_comm]

/-- Local square integrability on bounded intervals implies local Bochner
integrability, without a separability hypothesis on the target. -/
lemma locallyIntegrable_of_local_memLp {f : ℝ → H}
    (hf : ∀ a b : ℝ, MemLp f 2 (volume.restrict (Set.Icc a b))) :
    LocallyIntegrable f := by
  intro x
  refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (hf (x - 1) (x + 1)).integrable (by norm_num)

/-- The weak derivative vanishes off the closed support of its primitive. -/
lemma LocalW12.derivative_zero_off_support {w dw : ℝ → H} (hw : LocalW12 w dw) :
    ∀ᵐ t, t ∉ tsupport w → dw t = 0 := by
  have hd := locallyIntegrable_of_local_memLp hw.2.1
  apply (isClosed_tsupport w).isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hd.locallyIntegrableOn _)
  intro φ hφ hsφ hsub
  have hz : (∫ t, deriv φ t • w t) = 0 := by
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro t
    change deriv φ t • w t = 0
    by_cases ht : t ∈ tsupport φ
    · rw [image_eq_zero_of_notMem_tsupport (hsub ht), smul_zero]
    · rw [deriv_of_notMem_tsupport ht, zero_smul]
  have hh := hw.2.2 φ hφ hsφ
  rw [hz] at hh
  exact neg_eq_zero.mp hh.symm

/-- Continuous scalar multipliers preserve square integrability on a compact interval. -/
lemma memLp_smul_on_Icc {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 H]
    {a : ℝ → 𝕜} (ha : Continuous a) {f : ℝ → H} {l u : ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc l u))) :
    MemLp (fun t => a t • f t) 2 (volume.restrict (Set.Icc l u)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := l) (b := u)).bddAbove_image ha.norm.continuousOn
  have hb : MemLp a ⊤ (volume.restrict (Set.Icc l u)) :=
    memLp_top_of_bound ha.aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hC (Set.mem_image_of_mem _ ht))
  exact hb.smul hf

/-- A function locally in L² and zero almost everywhere off a compact set is globally in L². -/
lemma memLp_of_local_memLp_ae_zero {f : ℝ → H}
    (hf : ∀ a b : ℝ, MemLp f 2 (volume.restrict (Set.Icc a b)))
    {K : Set ℝ} (hK : IsCompact K) (hz : ∀ᵐ t, t ∉ K → f t = 0) : MemLp f 2 := by
  obtain ⟨l, hl⟩ := hK.bddBelow
  obtain ⟨u, hu⟩ := hK.bddAbove
  have hfi := (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr (hf l u)
  apply hfi.ae_eq
  filter_upwards [hz] with t ht
  by_cases h : t ∈ Set.Icc l u
  · simp [h]
  · have htK : t ∉ K := fun hK => h ⟨hl hK, hu hK⟩
    simp [h, ht htK]

lemma LocalW12.memLp_compact {w dw : ℝ → H} (hw : LocalW12 w dw)
    (hs : HasCompactSupport w) : MemLp w 2 ∧ MemLp dw 2 := by
  refine ⟨memLp_of_local_memLp_ae_zero hw.1 hs ?_,
    memLp_of_local_memLp_ae_zero hw.2.1 hs hw.derivative_zero_off_support⟩
  exact Filter.Eventually.of_forall (fun t ht => image_eq_zero_of_notMem_tsupport ht)

/-- Multiplication of a local L² function by a continuous compactly supported scalar
produces a global L² function. -/
lemma memLp_smul_compact {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 H]
    {a : ℝ → 𝕜} (ha : Continuous a) (hs : HasCompactSupport a) {f : ℝ → H}
    (hf : ∀ l u : ℝ, MemLp f 2 (volume.restrict (Set.Icc l u))) :
    MemLp (fun t => a t • f t) 2 := by
  apply memLp_of_local_memLp_ae_zero (fun l u => memLp_smul_on_Icc ha (hf l u)) hs
  exact Filter.Eventually.of_forall (fun t ht => by
    rw [image_eq_zero_of_notMem_tsupport ht, zero_smul])

/-- The weak Leibniz rule for multiplication by a smooth real scalar. -/
lemma LocalW12.smul {w dw : ℝ → H} (hw : LocalW12 w dw)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) :
    LocalW12 (fun t => a t • w t)
      (fun t => deriv a t • w t + a t • dw t) := by
  have hda : ContDiff ℝ ∞ (deriv a) := ha.deriv'
  refine ⟨fun l u => memLp_smul_on_Icc ha.continuous (hw.1 l u),
    ⟨fun l u => (memLp_smul_on_Icc hda.continuous (hw.1 l u)).add
      (memLp_smul_on_Icc ha.continuous (hw.2.1 l u)), ?_⟩⟩
  intro φ hφ hsφ
  have hwI := locallyIntegrable_of_local_memLp hw.1
  have hdI := locallyIntegrable_of_local_memLp hw.2.1
  have hφd : ContDiff ℝ ∞ (deriv φ) := hφ.deriv'
  have h1 := hwI.integrable_smul_left_of_hasCompactSupport
    (hφd.continuous.mul ha.continuous) (hsφ.deriv.mul_right (f' := a))
  have h2 := hwI.integrable_smul_left_of_hasCompactSupport
    (hφ.continuous.mul hda.continuous) (hsφ.mul_right (f' := deriv a))
  have h3 := hdI.integrable_smul_left_of_hasCompactSupport
    (hφ.continuous.mul ha.continuous) (hsφ.mul_right (f' := a))
  simp only [Pi.mul_apply] at h1 h2 h3
  have hh := hw.2.2 (fun t => φ t * a t) (hφ.mul ha) (hsφ.mul_right (f' := a))
  have he (t : ℝ) : deriv (fun t => φ t * a t) t =
      deriv φ t * a t + φ t * deriv a t :=
    deriv_mul (hφ.differentiable (by simp) t) (ha.differentiable (by simp) t)
  simp_rw [he, add_smul] at hh
  rw [integral_add h1 h2] at hh
  have hR : (∫ t, φ t • (deriv a t • w t + a t • dw t)) =
      (∫ t, (φ t * deriv a t) • w t) + ∫ t, (φ t * a t) • dw t := by
    simp_rw [smul_add, smul_smul]
    exact integral_add h2 h3
  rw [hR]
  simp_rw [smul_smul]
  exact eq_neg_iff_add_eq_zero.mpr (by
    rw [← add_assoc, hh, neg_add_cancel])

/-- The local weak derivative identity also holds for complex-valued tests. -/
lemma LocalW12.test_complex {w dw : ℝ → H} (hw : LocalW12 w dw)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hsφ : HasCompactSupport φ) :
    (∫ t, deriv φ t • w t) = -(∫ t, φ t • dw t) := by
  have hr : ContDiff ℝ ∞ (fun t => (φ t).re) := Complex.reCLM.contDiff.comp hφ
  have hi : ContDiff ℝ ∞ (fun t => (φ t).im) := Complex.imCLM.contDiff.comp hφ
  have hsr : HasCompactSupport (fun t => (φ t).re) := hsφ.comp_left rfl
  have hsi : HasCompactSupport (fun t => (φ t).im) := hsφ.comp_left rfl
  have hdr (t : ℝ) : deriv (fun t => (φ t).re) t = (deriv φ t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((hφ.differentiable (by simp) t).hasDerivAt)).deriv
  have hdi (t : ℝ) : deriv (fun t => (φ t).im) t = (deriv φ t).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      ((hφ.differentiable (by simp) t).hasDerivAt)).deriv
  have hR := hw.2.2 _ hr hsr
  have hI := hw.2.2 _ hi hsi
  simp_rw [hdr] at hR
  simp_rw [hdi] at hI
  have hdR := (locallyIntegrable_of_local_memLp hw.1).integrable_smul_left_of_hasCompactSupport
    (hr.deriv' (n := ∞)).continuous hsr.deriv
  have hdI := (locallyIntegrable_of_local_memLp hw.1).integrable_smul_left_of_hasCompactSupport
    (hi.deriv' (n := ∞)).continuous hsi.deriv
  simp_rw [hdr] at hdR
  simp_rw [hdi] at hdI
  have hfR := (locallyIntegrable_of_local_memLp hw.2.1).integrable_smul_left_of_hasCompactSupport
    hr.continuous hsr
  have hfI := (locallyIntegrable_of_local_memLp hw.2.1).integrable_smul_left_of_hasCompactSupport
    hi.continuous hsi
  have hc (z : ℂ) (x : H) : z • x = z.re • x + Complex.I • (z.im • x) := by
    calc
      z • x = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • x := by rw [Complex.re_add_im]
      _ = _ := by
        rw [add_smul, mul_comm (z.im : ℂ) Complex.I, mul_smul,
          RCLike.real_smul_eq_coe_smul (K := ℂ) z.re x,
          RCLike.real_smul_eq_coe_smul (K := ℂ) z.im x]
        rfl
  have hsplit (a : ℝ → ℂ) (f : ℝ → H)
      (hR : Integrable (fun t => (a t).re • f t))
      (hI : Integrable (fun t => (a t).im • f t)) :
      (∫ t, a t • f t) = (∫ t, (a t).re • f t) +
        Complex.I • (∫ t, (a t).im • f t) := by
    calc
      _ = ∫ t, (a t).re • f t + Complex.I • ((a t).im • f t) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun t => hc (a t) (f t)))
      _ = _ := by
        have hIs : Integrable (fun t => Complex.I • ((a t).im • f t)) := hI.smul Complex.I
        rw [integral_add hR hIs, integral_smul]
  rw [hsplit _ _ hdR hdI, hsplit _ _ hfR hfI, hR, hI]
  simp [add_comm]

set_option maxHeartbeats 800000 in
/-- With a compactly supported primitive, the weak identity may be tested
against any smooth coefficient, by inserting a bump equal to one near the support. -/
lemma LocalW12.test_smooth_compact {w dw : ℝ → H} (hw : LocalW12 w dw)
    (hs : HasCompactSupport w) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    (∫ t, deriv φ t • w t) = -(∫ t, φ t • dw t) := by
  obtain ⟨R, hR, hsub⟩ := hs.isBounded.subset_ball_lt 0 (0 : ℝ)
  let χ : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, lt_add_one R⟩
  let ψ : ℝ → ℂ := fun t => (χ t : ℂ) * φ t
  have hψ : ContDiff ℝ ∞ ψ :=
    (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hφ
  have hsχ : HasCompactSupport (fun t => (χ t : ℂ)) :=
    χ.hasCompactSupport.comp_left (g := Complex.ofReal) rfl
  have hsψ : HasCompactSupport ψ := hsχ.mul_right (f' := φ)
  have htest := hw.test_complex hψ hsψ
  have hL : (∫ t, deriv ψ t • w t) = ∫ t, deriv φ t • w t := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ tsupport w
    · have he : ψ =ᶠ[𝓝 t] φ := by
        filter_upwards [χ.eventuallyEq_one_of_mem_ball (hsub ht)] with y hy
        simp [ψ, hy]
      change deriv ψ t • w t = deriv φ t • w t
      rw [he.deriv_eq]
    · simp only [image_eq_zero_of_notMem_tsupport ht, smul_zero]
  have hR : (∫ t, ψ t • dw t) = ∫ t, φ t • dw t := by
    apply integral_congr_ae
    filter_upwards [hw.derivative_zero_off_support] with t ht
    by_cases hm : t ∈ tsupport w
    · have hone : χ t = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hsub hm))
      simp [ψ, hone]
    · simp [ht hm]
  rwa [hL, hR] at htest

/-- Fourier differentiation for compactly supported weak W¹,² curves.
The derivative is the given weak derivative, not a classical pointwise derivative. -/
lemma LocalW12.fourier_derivative {w dw : ℝ → H} (hw : LocalW12 w dw)
    (hs : HasCompactSupport w) (s : ℝ) :
    𝓕 dw s = (2 * Real.pi * Complex.I * s : ℂ) • 𝓕 w s := by
  let a : ℝ → ℂ := fun t => Real.fourierChar (-t * s)
  have ha : ContDiff ℝ ∞ a := by
    simp only [a, Real.fourierChar_apply]
    exact Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp (by fun_prop :
        ContDiff ℝ ∞ (fun t : ℝ => 2 * Real.pi * (-t * s)))).mul contDiff_const)
  have hda (t : ℝ) : deriv a t =
      -(2 * Real.pi * Complex.I * s : ℂ) * a t := by
    have hl : HasDerivAt (fun y : ℝ => -y * s) (-s) t := by
      convert ((hasDerivAt_id t).neg).mul_const s using 1 <;> simp
    have h := (Real.hasDerivAt_fourierChar (-t * s)).scomp t hl
    change deriv ((fun x : ℝ => (Real.fourierChar x : ℂ)) ∘
      (fun y : ℝ => -y * s)) t = _
    rw [h.deriv]
    simp only [Complex.real_smul, Complex.ofReal_neg, a]
    ring
  have h := hw.test_smooth_compact hs ha
  simp_rw [hda, mul_smul] at h
  rw [integral_smul] at h
  have hF (f : ℝ → H) : (∫ t, a t • f t) = 𝓕 f s := by
    simp only [a, Real.fourier_eq, real_inner_comm, RCLike.inner_apply,
      conj_trivial, mul_neg, Circle.smul_def, neg_mul, mul_comm]
  rw [hF, hF] at h
  simpa only [neg_smul, neg_inj] using h.symm

/-- Integrability follows from local integrability and almost everywhere compact support. -/
lemma integrable_of_locallyIntegrable_ae_zero {f : ℝ → H}
    (hf : LocallyIntegrable f) {K : Set ℝ} (hK : IsCompact K)
    (hz : ∀ᵐ t, t ∉ K → f t = 0) : Integrable f := by
  have hi : Integrable (K.indicator f) :=
    (integrable_indicator_iff hK.measurableSet).mpr (hf.integrableOn_isCompact hK)
  apply hi.congr
  filter_upwards [hz] with t ht
  by_cases h : t ∈ K <;> simp [h, ht]

lemma LocalW12.integrable_compact {w dw : ℝ → H} (hw : LocalW12 w dw)
    (hs : HasCompactSupport w) : Integrable w ∧ Integrable dw := by
  refine ⟨integrable_of_locallyIntegrable_ae_zero
      (locallyIntegrable_of_local_memLp hw.1) hs ?_,
    integrable_of_locallyIntegrable_ae_zero
      (locallyIntegrable_of_local_memLp hw.2.1) hs hw.derivative_zero_off_support⟩
  exact Filter.Eventually.of_forall (fun t ht => image_eq_zero_of_notMem_tsupport ht)

/-- Conjugation of a weakly differentiable curve by the exponential weight. -/
lemma LocalW12.weighted {w dw : ℝ → H} (hw : LocalW12 w dw) (ξ : ℝ) :
    LocalW12 (weighted ξ w)
      (fun t => weighted ξ dw t - ξ • weighted ξ w t) := by
  have ha : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-ξ * t)) := by fun_prop
  have hd (t : ℝ) : deriv (fun t : ℝ => Real.exp (-ξ * t)) t =
      -ξ * Real.exp (-ξ * t) := by
    simpa [mul_comm] using ((((hasDerivAt_id t).const_mul (-ξ)).exp).deriv)
  have hm := hw.smul ha
  have he : (fun t => deriv (fun t : ℝ => Real.exp (-ξ * t)) t • w t +
      Real.exp (-ξ * t) • dw t) =
      (fun t => WeightedResolvent.weighted ξ dw t -
        ξ • WeightedResolvent.weighted ξ w t) := by
    funext t
    rw [hd]
    simp [WeightedResolvent.weighted, mul_smul, sub_eq_add_neg, add_comm]
  rw [he] at hm
  exact hm

lemma fourier_sub_integrable {f g : ℝ → H} (hf : Integrable f) (hg : Integrable g)
    (s : ℝ) : 𝓕 (fun t => f t - g t) s = 𝓕 f s - 𝓕 g s := by
  simp only [Real.fourier_eq]
  simp_rw [smul_sub]
  rw [integral_sub]
  · exact (Real.fourierIntegral_convergent_iff s).mpr hf
  · exact (Real.fourierIntegral_convergent_iff s).mpr hg

lemma weighted_ae_zero {f : ℝ → H} {K : Set ℝ}
    (hz : ∀ᵐ t, t ∉ K → f t = 0) (ξ : ℝ) :
    ∀ᵐ t, t ∉ K → weighted ξ f t = 0 := by
  filter_upwards [hz] with t ht
  intro h
  simp [weighted, ht h]

lemma weighted_compact_data {f : ℝ → H}
    (hf : ∀ a b : ℝ, MemLp f 2 (volume.restrict (Set.Icc a b)))
    {K : Set ℝ} (hK : IsCompact K) (hz : ∀ᵐ t, t ∉ K → f t = 0) (ξ : ℝ) :
    Integrable (weighted ξ f) ∧ MemLp (weighted ξ f) 2 := by
  have hlocal (a b : ℝ) : MemLp (weighted ξ f) 2 (volume.restrict (Set.Icc a b)) :=
    memLp_smul_on_Icc (by fun_prop : Continuous (fun t : ℝ => Real.exp (-ξ * t))) (hf a b)
  exact ⟨integrable_of_locallyIntegrable_ae_zero
    (locallyIntegrable_of_local_memLp hlocal) hK (weighted_ae_zero hz ξ),
    memLp_of_local_memLp_ae_zero hlocal hK (weighted_ae_zero hz ξ)⟩

theorem compact_estimate : Spec.CompactEstimate := by
  intro H _ _ _ G hGc _ ξ d hb w dw hD hw hs hGw
  let g : ℝ → H := fun t => G ⟨w t, hD t⟩
  have hwzero : ∀ᵐ t, t ∉ tsupport w → w t = 0 :=
    Filter.Eventually.of_forall (fun t ht => image_eq_zero_of_notMem_tsupport ht)
  have hgzero : ∀ᵐ t, t ∉ tsupport w → g t = 0 := by
    apply Filter.Eventually.of_forall
    intro t ht
    have hz : (⟨w t, hD t⟩ : G.domain) = 0 := by
      apply Subtype.ext
      change w t = 0
      exact image_eq_zero_of_notMem_tsupport ht
    dsimp only [g]
    rw [hz, G.map_zero]
  have hgLocal (a b : ℝ) : MemLp g 2 (volume.restrict (Set.Icc a b)) :=
    hGw.mono_measure Measure.restrict_le_self
  obtain ⟨hvI, hv2⟩ := weighted_compact_data hw.1 hs hwzero ξ
  obtain ⟨hdI, hd2⟩ := weighted_compact_data hw.2.1 hs hw.derivative_zero_off_support ξ
  obtain ⟨hgI, hg2⟩ := weighted_compact_data hgLocal hs hgzero ξ
  have hr : weighted ξ (residual G w dw hD) =
      (fun t => weighted ξ dw t - weighted ξ g t) := by
    funext t
    exact smul_sub _ _ _
  have hrI : Integrable (weighted ξ (residual G w dw hD)) := by
    rw [hr]
    exact hdI.sub hgI
  have hr2 : MemLp (weighted ξ (residual G w dw hD)) 2 := by
    rw [hr]
    exact hd2.sub hg2
  have hDv (t : ℝ) : weighted ξ w t ∈ G.domain := by
    dsimp only [weighted]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact G.domain.smul_mem _ (hD t)
  have hGv (t : ℝ) : G ⟨weighted ξ w t, hDv t⟩ = weighted ξ g t := by
    dsimp only [weighted, g]
    convert G.map_smul (Real.exp (-ξ * t) : ℂ) ⟨w t, hD t⟩ using 1
  have hGvI : Integrable (fun t => G ⟨weighted ξ w t, hDv t⟩) := by
    simpa only [hGv] using hgI
  have hvw := hw.weighted ξ
  have hsv : HasCompactSupport (weighted ξ w) := hs.smul_left
  have hfourier (s : ℝ) : ∃ h : 𝓕 (weighted ξ w) s ∈ G.domain,
      𝓕 (weighted ξ (residual G w dw hD)) s =
        (ξ + Complex.I * (2 * Real.pi * s) : ℂ) • 𝓕 (weighted ξ w) s -
          G ⟨𝓕 (weighted ξ w) s, h⟩ := by
    obtain ⟨h, hG⟩ := fourier_graph G hGc (weighted ξ w) hDv hvI hGvI s
    simp_rw [hGv] at hG
    refine ⟨h, ?_⟩
    have hFd := hvw.fourier_derivative hsv s
    rw [fourier_sub_integrable (g := fun t => ξ • weighted ξ w t) hdI (hvI.smul ξ) s] at hFd
    have hFs : 𝓕 (fun t => ξ • weighted ξ w t) s = ξ • 𝓕 (weighted ξ w) s := by
      simp only [Real.fourier_eq]
      simp_rw [smul_comm _ ξ, integral_smul]
    rw [hFs] at hFd
    rw [hr, fourier_sub_integrable hdI hgI s, ← hG]
    rw [sub_eq_iff_eq_add.mp hFd]
    rw [add_smul]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    module
  have h := fourier_coercivity G ξ d hb (weighted ξ w)
    (weighted ξ (residual G w dw hD)) hvI hv2 hrI hr2 hfourier
  rwa [weighted_energy, weighted_energy] at h


lemma smul_mem_domain_real (G : Operator ℂ H H) (a : ℝ) {x : H}
    (hx : x ∈ G.domain) : a • x ∈ G.domain := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact G.domain.smul_mem (a : ℂ) hx

lemma operator_smul_real (G : Operator ℂ H H) (a : ℝ) (x : G.domain)
    (h : a • (x : H) ∈ G.domain) : G ⟨a • (x : H), h⟩ = a • G x := by
  have he : (⟨a • (x : H), h⟩ : G.domain) = (a : ℂ) • x := by
    apply Subtype.ext
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) a (x : H)).symm
  rw [he, G.map_smul]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) a (G x)

lemma cutoff_residual (G : Operator ℂ H H) (w dw : ℝ → H)
    (hD : ∀ t, w t ∈ G.domain) (a : ℝ → ℝ)
    (hDa : ∀ t, a t • w t ∈ G.domain) (t : ℝ) :
    residual G (fun t => a t • w t)
      (fun t => deriv a t • w t + a t • dw t) hDa t =
      a t • residual G w dw hD t + deriv a t • w t := by
  simp only [residual, operator_smul_real G (a t) ⟨w t, hD t⟩ (hDa t), smul_sub]
  abel

lemma weighted_smul (ξ : ℝ) (a : ℝ → ℝ) (w : ℝ → H) (t : ℝ) :
    weighted ξ (fun t => a t • w t) t = a t • weighted ξ w t := by
  exact smul_comm _ _ _

lemma weighted_add (ξ : ℝ) (w v : ℝ → H) (t : ℝ) :
    weighted ξ (fun t => w t + v t) t = weighted ξ w t + weighted ξ v t := by
  exact smul_add _ _ _

lemma cutoff_graph_memLp (G : Operator ℂ H H) (w : ℝ → H)
    (hD : ∀ t, w t ∈ G.domain) (hG : Continuous (fun t => G ⟨w t, hD t⟩))
    (a : ℝ → ℝ) (ha : Continuous a) (hsa : HasCompactSupport a)
    (hDa : ∀ t, a t • w t ∈ G.domain) :
    MemLp (fun t => G ⟨a t • w t, hDa t⟩) 2 := by
  have he : (fun t => G ⟨a t • w t, hDa t⟩) =
      (fun t => a t • G ⟨w t, hD t⟩) := by
    funext t
    exact operator_smul_real G (a t) ⟨w t, hD t⟩ (hDa t)
  rw [he]
  exact (ha.smul hG).memLp_of_hasCompactSupport (hsa.smul_right)


def cutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
def cutoffSeq (n : ℕ) (t : ℝ) : ℝ := cutoffBump (t / ((n : ℝ) + 1))

lemma cutoffSeq_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoffSeq n) := by
  exact cutoffBump.contDiff.comp (contDiff_id.div_const _)

lemma cutoffSeq_compact (n : ℕ) : HasCompactSupport (cutoffSeq n) := by
  change HasCompactSupport (fun t : ℝ => cutoffBump (t / ((n : ℝ) + 1)))
  simpa only [div_eq_inv_mul, smul_eq_mul] using
    cutoffBump.hasCompactSupport.comp_smul (inv_ne_zero (by positivity : (n : ℝ) + 1 ≠ 0))

lemma cutoffSeq_norm (n : ℕ) (t : ℝ) : ‖cutoffSeq n t‖ ≤ 1 := by
  change ‖cutoffBump (t / ((n : ℝ) + 1))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg cutoffBump.nonneg]
  exact cutoffBump.le_one

lemma cutoffSeq_deriv (n : ℕ) (t : ℝ) :
    deriv (cutoffSeq n) t = deriv cutoffBump (t / ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
  have hs : ContDiff ℝ ∞ (cutoffBump : ℝ → ℝ) := cutoffBump.contDiff
  have hb := (hs.differentiable (by simp) (t / ((n : ℝ) + 1))).hasDerivAt
  have hc := (hb.comp t ((hasDerivAt_id t).div_const ((n : ℝ) + 1))).deriv
  change deriv (fun t : ℝ => cutoffBump (t / ((n : ℝ) + 1))) t = _
  convert hc using 1 <;> simp [div_eq_mul_inv, Function.comp_def]

lemma cutoffSeq_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, ‖deriv (cutoffSeq n) t‖ ≤ C := by
  have hs : ContDiff ℝ ∞ (cutoffBump : ℝ → ℝ) := cutoffBump.contDiff
  have hd : ContDiff ℝ ∞ (deriv (cutoffBump : ℝ → ℝ)) := hs.deriv'
  obtain ⟨C, hC⟩ := hd.continuous.bounded_above_of_compact_support
    cutoffBump.hasCompactSupport.deriv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, hC0, fun n t => ?_⟩
  rw [cutoffSeq_deriv, norm_div, Real.norm_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  exact (div_le_iff₀ (by positivity)).mpr (by
    calc
      ‖deriv cutoffBump (t / ((n : ℝ) + 1))‖ ≤ C := hC _
      _ ≤ C * ((n : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) n])

lemma cutoffSeq_deriv_bound_scaled :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, ‖deriv (cutoffSeq n) t‖ ≤ C / ((n : ℝ) + 1) := by
  have hs : ContDiff ℝ ∞ (cutoffBump : ℝ → ℝ) := cutoffBump.contDiff
  have hd : ContDiff ℝ ∞ (deriv (cutoffBump : ℝ → ℝ)) := hs.deriv'
  obtain ⟨C, hC⟩ := hd.continuous.bounded_above_of_compact_support
    cutoffBump.hasCompactSupport.deriv
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun n t => ?_⟩
  rw [cutoffSeq_deriv, norm_div, Real.norm_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
  exact div_le_div_of_nonneg_right (hC _) (by positivity)

lemma cutoffSeq_eventually_one (t : ℝ) : ∀ᶠ n in atTop, cutoffSeq n t = 1 := by
  have ht : ∀ᶠ n : ℕ in atTop, |t| < (n : ℝ) + 1 := by
    exact (tendsto_natCast_atTop_atTop.eventually_gt_atTop (|t| : ℝ)).mono
      (fun n hn => by linarith)
  filter_upwards [ht] with n hn
  apply cutoffBump.one_of_mem_closedBall
  change dist (t / ((n : ℝ) + 1)) 0 ≤ 1
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
  exact (div_le_one (by positivity)).mpr hn.le

lemma cutoffSeq_eventually_deriv_zero (t : ℝ) : ∀ᶠ n in atTop, deriv (cutoffSeq n) t = 0 := by
  have ht : ∀ᶠ n : ℕ in atTop, |t| < (n : ℝ) + 1 := by
    exact (tendsto_natCast_atTop_atTop.eventually_gt_atTop (|t| : ℝ)).mono
      (fun n hn => by linarith)
  filter_upwards [ht] with n hn
  rw [cutoffSeq_deriv]
  have hi : t / ((n : ℝ) + 1) ∈ Metric.ball (0 : ℝ) cutoffBump.rIn := by
    change dist (t / ((n : ℝ) + 1)) 0 < 1
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
    exact (div_lt_one (by positivity)).mpr hn
  have hz := cutoffBump.eventuallyEq_one_of_mem_ball hi
  have hd : deriv cutoffBump (t / ((n : ℝ) + 1)) = 0 := by
    rw [hz.deriv_eq]
    simp
  rw [hd, zero_div]

lemma cutoffSeq_tendsto_one (t : ℝ) : Tendsto (fun n => cutoffSeq n t) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [cutoffSeq_eventually_one t] with n hn using hn.symm)

lemma cutoffSeq_deriv_tendsto_zero (t : ℝ) :
    Tendsto (fun n => deriv (cutoffSeq n) t) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [cutoffSeq_eventually_deriv_zero t] with n hn using hn.symm)


lemma tendsto_integral_norm_sq_smul_add
    {a b : ℕ → ℝ → ℝ} {f r : ℝ → H} {C : ℝ}
    (hf : MemLp f 2) (hr : MemLp r 2)
    (ha : ∀ n, Continuous (a n)) (hb : ∀ n, Continuous (b n))
    (hC : 0 ≤ C) (ha_bound : ∀ n t, |a n t| ≤ 1)
    (hb_bound : ∀ n t, |b n t| ≤ C)
    (ha_lim : ∀ t, Tendsto (fun n => a n t) atTop (𝓝 1))
    (hb_lim : ∀ t, Tendsto (fun n => b n t) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, ‖a n t • r t + b n t • f t‖ ^ 2)
      atTop (𝓝 (∫ t, ‖r t‖ ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t => 2 * ‖r t‖ ^ 2 + (2 * C ^ 2) * ‖f t‖ ^ 2)
  · intro n
    exact (((ha n).aestronglyMeasurable.smul hr.aestronglyMeasurable).add
      ((hb n).aestronglyMeasurable.smul hf.aestronglyMeasurable)).norm.pow 2
  · exact ((hr.integrable_norm_pow (by norm_num)).const_mul 2).add
      ((hf.integrable_norm_pow (by norm_num)).const_mul _)
  · intro n
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : ‖a n t • r t‖ ≤ ‖r t‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (ha_bound n t) (norm_nonneg _)).trans_eq
        (one_mul _)
    have h2 : ‖b n t • f t‖ ≤ C * ‖f t‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb_bound n t) (norm_nonneg _)
    have hs : ‖a n t • r t + b n t • f t‖ ≤ ‖r t‖ + C * ‖f t‖ :=
      (norm_add_le _ _).trans (add_le_add h1 h2)
    have hs0 : 0 ≤ ‖r t‖ + C * ‖f t‖ := by positivity
    have hp := mul_self_le_mul_self (norm_nonneg _) hs
    nlinarith [sq_nonneg (‖r t‖ - C * ‖f t‖)]
  · apply Eventually.of_forall
    intro t
    simpa only [one_smul, zero_smul, add_zero] using
      (((ha_lim t).smul_const (r t)).add ((hb_lim t).smul_const (f t))).norm.pow 2

lemma tendsto_integral_norm_sq_smul
    {a : ℕ → ℝ → ℝ} {f : ℝ → H}
    (hf : MemLp f 2) (ha : ∀ n, Continuous (a n))
    (ha_bound : ∀ n t, |a n t| ≤ 1)
    (ha_lim : ∀ t, Tendsto (fun n => a n t) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t, ‖a n t • f t‖ ^ 2)
      atTop (𝓝 (∫ t, ‖f t‖ ^ 2)) := by
  simpa using tendsto_integral_norm_sq_smul_add (f := f) (r := f) hf hf ha
    (fun _ => continuous_const) (C := 0) le_rfl ha_bound
    (fun _ _ => by simp) ha_lim (fun _ => tendsto_const_nhds)


lemma norm_sq_integral_le_of_cutoff
    {a b : ℕ → ℝ → ℝ} {f r : ℝ → H} {C d : ℝ}
    (hf : MemLp f 2) (hr : MemLp r 2)
    (ha : ∀ n, Continuous (a n)) (hb : ∀ n, Continuous (b n))
    (hC : 0 ≤ C) (ha_bound : ∀ n t, |a n t| ≤ 1)
    (hb_bound : ∀ n t, |b n t| ≤ C)
    (ha_lim : ∀ t, Tendsto (fun n => a n t) atTop (𝓝 1))
    (hb_lim : ∀ t, Tendsto (fun n => b n t) atTop (𝓝 0))
    (hest : ∀ n, d ^ 2 * (∫ t, ‖a n t • f t‖ ^ 2) ≤
      ∫ t, ‖a n t • r t + b n t • f t‖ ^ 2) :
    d ^ 2 * (∫ t, ‖f t‖ ^ 2) ≤ ∫ t, ‖r t‖ ^ 2 := by
  exact le_of_tendsto_of_tendsto'
    ((tendsto_integral_norm_sq_smul hf ha ha_bound ha_lim).const_mul _)
    (tendsto_integral_norm_sq_smul_add hf hr ha hb hC ha_bound hb_bound ha_lim hb_lim)
    hest


/-- Smooth graph cutoffs extend the estimate to curves with both weighted
L² norms finite. The derivative is the same local weak derivative as above. -/
theorem cutoff_estimate : Spec.CutoffEstimate := by
  intro H _ _ _ G hGc hDense ξ d hb w dw hD hw _ hGw hw2 hr2
  obtain ⟨C, hC, hCb⟩ := cutoffSeq_deriv_bound
  have hest (n : ℕ) :
      d ^ 2 * (∫ t, ‖cutoffSeq n t • weighted ξ w t‖ ^ 2) ≤
        ∫ t, ‖cutoffSeq n t • weighted ξ (residual G w dw hD) t +
          deriv (cutoffSeq n) t • weighted ξ w t‖ ^ 2 := by
    let hDn (t : ℝ) : cutoffSeq n t • w t ∈ G.domain :=
      smul_mem_domain_real G (cutoffSeq n t) (hD t)
    have hn := compact_estimate G hGc hDense ξ d hb
      (fun t => cutoffSeq n t • w t)
      (fun t => deriv (cutoffSeq n) t • w t + cutoffSeq n t • dw t) hDn
      (hw.smul (cutoffSeq_smooth n)) (cutoffSeq_compact n).smul_right
      (cutoff_graph_memLp G w hD hGw (cutoffSeq n)
        (cutoffSeq_smooth n).continuous (cutoffSeq_compact n) hDn)
    rw [← weighted_energy, ← weighted_energy] at hn
    have hleft : weighted ξ (fun t => cutoffSeq n t • w t) =
        fun t => cutoffSeq n t • weighted ξ w t := by
      funext t
      exact weighted_smul ξ (cutoffSeq n) w t
    have hright : weighted ξ (residual G (fun t => cutoffSeq n t • w t)
        (fun t => deriv (cutoffSeq n) t • w t + cutoffSeq n t • dw t) hDn) =
        fun t => cutoffSeq n t • weighted ξ (residual G w dw hD) t +
          deriv (cutoffSeq n) t • weighted ξ w t := by
      funext t
      rw [weighted, cutoff_residual]
      rw [smul_add, smul_comm (Real.exp (-ξ * t)) (cutoffSeq n t),
        smul_comm (Real.exp (-ξ * t)) (deriv (cutoffSeq n) t)]
      rfl
    rwa [hleft, hright] at hn
  have h := norm_sq_integral_le_of_cutoff hw2 hr2
    (fun n => (cutoffSeq_smooth n).continuous)
    (fun n => ((cutoffSeq_smooth n).deriv' (n := ∞)).continuous)
    hC (fun n t => by simpa only [Real.norm_eq_abs] using cutoffSeq_norm n t)
    (fun n t => by simpa only [Real.norm_eq_abs] using hCb n t)
    cutoffSeq_tendsto_one cutoffSeq_deriv_tendsto_zero hest
  rwa [weighted_energy, weighted_energy] at h

end ExpandedFA.Semigroups.WeightedResolvent
