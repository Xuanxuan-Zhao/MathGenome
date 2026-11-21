import MathGenome.Internal.LinearPDE.P201Specs.Potential.GreenCompactC2
import MathGenome.Internal.LinearPDE.P201.Potential.GreenConstruction
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open Set MeasureTheory Metric Filter
open scoped ContDiff Topology Convolution
namespace P201.GreenCompactC2
open P201Specs

theorem green_integrable {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) {x : Space n} (hx : x ∈ Ω)
    (g : Space n → ℝ) (hg : P201Specs.GreenConstruction.IsGreenFunction Ω x g) :
    IntegrableOn g (Ω : Set _) volume := by
  obtain ⟨r, hr, hball⟩ := P201.GreenConstruction.exists_collar_radius Ω hx
  have hsmall : closedBall x r ⊆ (Ω : Set _) :=
    (closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hball
  have hnear : IntegrableOn g (closedBall x r) volume :=
    hg.1.integrableOn_compact_subset hsmall (isCompact_closedBall x r)
  let K := closure (Ω : Set _) \ ball x r
  have hK : IsCompact K := hb.isCompact_closure.diff isOpen_ball
  have hsub : K ⊆ closure (Ω : Set _) \ {x} := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    simp only [mem_singleton_iff]
    intro he
    subst y
    exact hy.2 (mem_ball_self hr)
  have hfar : IntegrableOn g K volume := (hg.2.2.2.2.1.mono hsub).integrableOn_compact hK
  apply (integrableOn_union.mpr ⟨hnear, hfar⟩).mono_set
  intro y hy
  by_cases hyr : y ∈ closedBall x r
  · exact Or.inl hyr
  · exact Or.inr ⟨subset_closure hy, fun hyb => hyr (ball_subset_closedBall hyb)⟩

/-- In particular every continuous forcing has a genuine Green volume integral. -/
theorem green_mul_continuous_integrable {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) {x : Space n} (hx : x ∈ Ω)
    (g : Space n → ℝ) (hg : P201Specs.GreenConstruction.IsGreenFunction Ω x g)
    (f : Space n → ℝ) (hf : ContinuousOn f (closure (Ω : Set _))) :
    IntegrableOn (fun y => g y * f y) (Ω : Set _) volume :=
  (green_integrable Ω hb hx g hg).mul_continuousOn_of_subset hf
    Ω.isOpen.measurableSet hb.isCompact_closure subset_closure


/-- A finite C² jet at each closure point bounds the interior Laplacian
locally. This does not require unique differentiability at boundary points. -/
theorem laplacian_locally_bounded_on_closure {n : ℕ} (Ω : Domain n)
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 2 u (closure (Ω : Set _)))
    (z : Space n) (hz : z ∈ closure (Ω : Set _)) :
    ∃ U ∈ 𝓝 z, ∃ C : ℝ, ∀ y ∈ U ∩ (Ω : Set _), ‖P201Specs.laplacian u y‖ ≤ C := by
  obtain ⟨t, ht, p, hp⟩ := contDiffWithinAt_nat.mp (hu z hz)
  rw [insert_eq_of_mem hz] at ht
  obtain ⟨V, hVz, hVt⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp ht
  obtain ⟨V', hV'V, hV'o, hzV'⟩ := _root_.mem_nhds_iff.mp hVz
  have hzt : z ∈ t := hVt ⟨hV'V hzV', hz⟩
  let q : Space n → ℝ := fun y => ∑ i : Fin n,
    p y 2 ![coordinate n i, coordinate n i]
  have hq : ContinuousWithinAt q t z := by
    apply ContinuousOn.continuousWithinAt (s := t) _ hzt
    apply continuousOn_finsetSum
    intro i _
    exact (continuous_eval_const _).comp_continuousOn (hp.cont 2 (by norm_num))
  have hqb : ∀ᶠ y in 𝓝[t] z, ‖q y‖ < ‖q z‖ + 1 :=
    hq.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨W, hWz, hWb⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hqb
  refine ⟨V' ∩ W, inter_mem (hV'o.mem_nhds hzV') hWz, ‖q z‖ + 1, ?_⟩
  intro y hy
  have hyV : y ∈ V' := hy.1.1
  have hyΩ : y ∈ Ω := hy.2
  have hsub : V' ∩ (Ω : Set _) ⊆ t := by
    intro a ha
    exact hVt ⟨hV'V ha.1, subset_closure ha.2⟩
  have hT := hp.mono hsub
  have hOpen : IsOpen (V' ∩ (Ω : Set _)) := hV'o.inter Ω.isOpen
  have he : p y 2 = iteratedFDeriv ℝ 2 u y := by
    rw [hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (by norm_num)
      hOpen.uniqueDiffOn ⟨hyV, hyΩ⟩]
    exact iteratedFDerivWithin_eq_iteratedFDeriv hOpen.uniqueDiffOn
      ((hu.mono subset_closure).contDiffAt (Ω.isOpen.mem_nhds hyΩ)) ⟨hyV, hyΩ⟩
  have hl : P201Specs.laplacian u y = q y := by
    rw [P201.MeanValues.laplacian_bridge u y
      ((hu.mono subset_closure).contDiffAt (Ω.isOpen.mem_nhds hyΩ)),
      InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
        (EuclideanSpace.basisFun (Fin n) ℝ)]
    simp only [q, he]
    rfl
  rw [hl]
  exact (hWb ⟨hy.1.2, hsub ⟨hyV, hyΩ⟩⟩).le

/-- Compactness turns the local jet bounds into a uniform bound on Ω. -/
theorem laplacian_bounded_on_bounded_domain {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n)))
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 2 u (closure (Ω : Set _))) :
    ∃ C : ℝ, ∀ y ∈ (Ω : Set _), ‖P201Specs.laplacian u y‖ ≤ C := by
  choose U hU C hC using laplacian_locally_bounded_on_closure Ω u hu
  obtain ⟨T, hT⟩ := hb.isCompact_closure.elim_nhds_subcover' U hU
  let B : {z : Space n // z ∈ closure (Ω : Set (Space n))} → ℝ :=
    fun z => max (C z.val z.property) 0
  refine ⟨∑ z ∈ T, B z, ?_⟩
  intro y hy
  obtain ⟨z, hzT, hyz⟩ := mem_iUnion₂.mp (hT (subset_closure hy))
  have hsum : B z ≤ ∑ a ∈ T, B a :=
    Finset.single_le_sum (f := B) (s := T) (a := z)
      (fun a _ => le_max_right _ _) hzT
  exact (hC z z.2 y ⟨hyz, hy⟩).trans ((le_max_left _ _).trans hsum)


/-- The volume term exists for closure-C² data; boundary regularity is
unnecessary for this integrability assertion itself. -/
theorem volume_integrability : P201Specs.GreenCompactC2.VolumeIntegrabilityStatement := by
  intro m Ω hb _ x hx g hg u hu
  obtain ⟨C, hC⟩ := laplacian_bounded_on_bounded_domain Ω hb u hu
  apply (green_integrable Ω hb hx g hg).mul_bdd (c := C)
    ((P201.MeanValues.laplacian_continuousOn Ω u (hu.mono subset_closure)).neg.aestronglyMeasurable
      Ω.isOpen.measurableSet)
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
  simpa only [Pi.neg_apply, norm_neg] using hC y hy

/-- The coordinate convention in the shared interface is precisely two
successive ordinary directional derivatives. -/
theorem laplacian_eq_sum_coordinate {n : ℕ} (f : Space n → ℝ) :
    P201Specs.laplacian f = fun x => ∑ i : Fin n,
      fderiv ℝ (fun y => fderiv ℝ f y (coordinate n i)) x (coordinate n i) := by
  funext x
  apply Finset.sum_congr rfl
  intro i _
  simp [P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_cons,
    P102.U4.partialWord]

/-- Differentiation cannot enlarge the support. -/
theorem tsupport_laplacian_subset {n : ℕ} (f : Space n → ℝ) :
    tsupport (P201Specs.laplacian f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hxf
  apply hx
  rw [laplacian_eq_sum_coordinate]
  apply Finset.sum_eq_zero
  intro i _
  have hx' : x ∉ tsupport (fun y => fderiv ℝ f y (coordinate n i)) :=
    fun h => hxf (tsupport_fderiv_apply_subset ℝ _ h)
  rw [fderiv_of_notMem_tsupport ℝ hx']
  rfl

theorem laplacian_hasCompactSupport {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (P201Specs.laplacian f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset f)

theorem laplacian_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (P201Specs.laplacian f) := by
  exact continuousOn_univ.mp
    (P201.MeanValues.laplacian_continuousOn (⊤ : Domain n) f hf.contDiffOn)

/-- Compact support strictly inside Ω allows local integrability of g to
control the whole ambient product. -/
theorem green_mul_compact_continuous_integrable {n : ℕ} (Ω : Domain n)
    (g f : Space n → ℝ) (hg : LocallyIntegrableOn g (Ω : Set _) volume)
    (hf : Continuous f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ (Ω : Set _)) :
    Integrable (fun y => g y * f y) volume := by
  have hI := (hg.integrableOn_compact_subset hs hc).mul_continuousOn hf.continuousOn hc
  apply (integrableOn_iff_integrable_of_support_subset (s := tsupport f) ?_).mp hI
  intro y hy
  by_contra hyf
  exact hy (by simp [image_eq_zero_of_notMem_tsupport hyf])

/-- The smooth test identity is a direct consequence of the upstream
normalized distributional equation, including its minus sign. -/
theorem compact_smooth {n : ℕ} (Ω : Domain n) (x : Space n)
    (g : Space n → ℝ) (hg : P201Specs.GreenConstruction.IsGreenFunction Ω x g)
    (φ : Test ℝ Ω) :
    (∫ y, g y * (-P201Specs.laplacian φ y)) = φ x := by
  have h := congrArg (fun T : Distribution ℝ Ω => T φ) hg.2.1
  change -(distributionLaplacian (regularDistribution Ω g) φ) = φ x at h
  rw [P201.GreenConstruction.regular_laplacian_pairing Ω g hg.1 φ] at h
  rw [show (fun y => g y * (-P201Specs.laplacian φ y)) =
    (fun y => -(g y * P201Specs.laplacian φ y)) by funext y; ring, integral_neg]
  exact h

/-- Transfer one coordinate derivative to the compact C¹ factor of a
convolution. -/
theorem coordinate_convolution {n : ℕ} (ρ f : Space n → ℝ)
    (hρ : LocallyIntegrable ρ volume) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (v : Space n) :
    (fun x => fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x v) =
      ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun x => fderiv ℝ f x v) := by
  funext x
  rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hρ hf x).fderiv]
  exact convolution_precompR_apply _ hρ (hc.fderiv ℝ) (hf.continuous_fderiv one_ne_zero) x v

/-- Two derivative transfers identify the actual canonical Laplacian of
a mollification. Only C², rather than smoothness, is used for f. -/
theorem laplacian_convolution {n : ℕ} (ρ f : Space n → ℝ)
    (hρ : LocallyIntegrable ρ volume) (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 2 f) :
    P201Specs.laplacian (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) =
      ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (P201Specs.laplacian f) := by
  have hdf (i : Fin n) : ContDiff ℝ 1 (fun x => fderiv ℝ f x (coordinate n i)) :=
    (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  funext x
  rw [laplacian_eq_sum_coordinate]
  calc
    _ = ∑ i : Fin n, (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y => fderiv ℝ (fun z => fderiv ℝ f z (coordinate n i)) y (coordinate n i))) x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coordinate_convolution ρ f hρ hc (hf.of_le (by norm_num))]
      exact congrFun (coordinate_convolution ρ _ hρ (hc.fderiv_apply ℝ _)
        (hdf i) (coordinate n i)) x
    _ = _ := by
      rw [laplacian_eq_sum_coordinate]
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [integral_finsetSum]
      intro i _
      exact (hc.fderiv_apply ℝ (coordinate n i)).fderiv_apply ℝ (coordinate n i)
        |>.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hρ
          ((hdf i).continuous_fderiv one_ne_zero |>.clm_apply continuous_const) x

/-- A small convolution stays in a fixed compact neighborhood of the
original support. -/
theorem tsupport_convolution_subset_cthickening {n : ℕ} (ρ f : Space n → ℝ)
    (δ : ℝ) (hρ : Function.support ρ ⊆ closedBall 0 δ) :
    tsupport (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) ⊆ cthickening δ (tsupport f) := by
  apply closure_minimal _ isClosed_cthickening
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset_swap
    (ContinuousLinearMap.lsmul ℝ ℝ) hy
  apply mem_cthickening_of_dist_le (a + b) a δ (tsupport f) (subset_tsupport _ ha)
  simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hρ hb

/-- The full compact C² Green identity, proved by smoothing within a fixed
compact subset of Ω and dominated convergence against the locally L¹ row. -/
theorem compact_c2 : P201Specs.GreenCompactC2.CompactC2Statement := by
  intro n _ Ω x _ g hg φ hφ hc hs
  have hL := laplacian_continuous hφ
  have hcL := laplacian_hasCompactSupport hc
  have hI : Integrable (fun y => g y * (-P201Specs.laplacian φ y)) volume :=
    green_mul_compact_continuous_integrable Ω g _ hg.1 hL.neg hcL.neg
      (by change tsupport (-P201Specs.laplacian φ) ⊆ _; rw [tsupport_neg]; exact (tsupport_laplacian_subset φ).trans hs)
  refine ⟨hI.integrableOn, ?_⟩
  obtain ⟨δ, hδ, hδΩ⟩ := hc.exists_cthickening_subset_open Ω.isOpen hs
  let K := cthickening δ (tsupport φ)
  have hK : IsCompact K := hc.cthickening
  have hKΩ : K ⊆ (Ω : Set _) := hδΩ
  have hφK : tsupport φ ⊆ K := self_subset_cthickening _
  let r : ℕ → ℝ := fun k => δ / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hrδ (k : ℕ) : r k ≤ δ := by
    dsimp [r]
    exact div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) k])
  let ρ : ℕ → ContDiffBump (0 : Space n) := fun k =>
    ⟨r k / 2, r k, half_pos (hr k), half_lt_self (hr k)⟩
  have hrt : Tendsto (fun k => (ρ k).rOut) atTop (𝓝 0) := by
    simpa [ρ, r, div_eq_mul_inv] using
      (tendsto_const_nhds (x := δ)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let ψ : ℕ → Space n → ℝ := fun k =>
    (ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] φ
  have hψ (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ψ k) :=
    (ρ k).hasCompactSupport_normed.contDiff_convolution_left _ (ρ k).contDiff_normed
      hφ.continuous.locallyIntegrable
  have hcψ (k : ℕ) : HasCompactSupport (ψ k) :=
    (ρ k).hasCompactSupport_normed.convolution _ hc
  have hsψ (k : ℕ) : tsupport (ψ k) ⊆ K := by
    apply tsupport_convolution_subset_cthickening
    intro y hy
    rw [(ρ k).support_normed_eq] at hy
    exact ball_subset_closedBall (ball_subset_ball (hrδ k) hy)
  let ψtest (k : ℕ) : Test ℝ Ω :=
    ⟨ψ k, hψ k, hcψ k, (hsψ k).trans hKΩ⟩
  have hψL (k : ℕ) : P201Specs.laplacian (ψ k) =
      (ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (P201Specs.laplacian φ) :=
    laplacian_convolution _ _ (ρ k).integrable_normed.locallyIntegrable hc hφ
  have hψlim (y : Space n) : Tendsto (fun k => ψ k y) atTop (𝓝 (φ y)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hrt hφ.continuous y
  have hψLlim (y : Space n) :
      Tendsto (fun k => P201Specs.laplacian (ψ k) y) atTop (𝓝 (P201Specs.laplacian φ y)) := by
    have heq : (fun k => P201Specs.laplacian (ψ k) y) =
        (fun k => ((ρ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
          (P201Specs.laplacian φ)) y) :=
      funext (fun k => congrFun (hψL k) y)
    rw [heq]
    exact ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := (volume : Measure (Space n))) hrt hL y
  obtain ⟨C, hC⟩ := hL.bounded_above_of_compact_support hcL
  have hψbound (k : ℕ) (y : Space n) : ‖P201Specs.laplacian (ψ k) y‖ ≤ 3 * C := by
    have hdist : dist (P201Specs.laplacian (ψ k) y) (P201Specs.laplacian φ y) ≤ 2 * C := by
      rw [hψL]
      apply ContDiffBump.dist_normed_convolution_le hL.aestronglyMeasurable
      intro z _
      calc
        dist (P201Specs.laplacian φ z) (P201Specs.laplacian φ y) ≤ ‖P201Specs.laplacian φ z‖ + ‖P201Specs.laplacian φ y‖ :=
          dist_le_norm_add_norm _ _
        _ ≤ 2 * C := by linarith [hC z, hC y]
    have hb := norm_le_norm_add_const_of_dist_le hdist
    linarith [hC y]
  have hsourceI (k : ℕ) : Integrable (fun y => g y * (-P201Specs.laplacian (ψ k) y)) volume := by
    apply green_mul_compact_continuous_integrable Ω g _ hg.1
      (laplacian_continuous ((hψ k).of_le (by simp))).neg
      (laplacian_hasCompactSupport (hcψ k)).neg
    rw [tsupport_neg]
    exact (tsupport_laplacian_subset _).trans ((hsψ k).trans hKΩ)
  have hzero (f : Space n → ℝ) (hfs : tsupport f ⊆ K) (y : Space n) (hy : y ∉ K) :
      g y * (-P201Specs.laplacian f y) = 0 := by
    have hyL : y ∉ tsupport (P201Specs.laplacian f) :=
      fun h => hy (hfs (tsupport_laplacian_subset f h))
    simp [image_eq_zero_of_notMem_tsupport hyL]
  have heval (k : ℕ) : (∫ y in K, g y * (-P201Specs.laplacian (ψ k) y)) = ψ k x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero _ (hsψ k))]
    exact compact_smooth Ω x g hg (ψtest k)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict K) (F := fun k y => g y * (-P201Specs.laplacian (ψ k) y))
    (f := fun y => g y * (-P201Specs.laplacian φ y)) (fun y => ‖g y‖ * (3 * C))
    (fun k => (hsourceI k).aestronglyMeasurable.restrict)
    ((hg.1.integrableOn_compact_subset hKΩ hK).norm.mul_const (3*C))
    (fun k => Eventually.of_forall fun y => by
      rw [norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_left (hψbound k y) (norm_nonneg _))
    (Eventually.of_forall fun y => tendsto_const_nhds.mul (hψLlim y).neg)
  have he : (∫ y in K, g y * (-P201Specs.laplacian φ y)) = φ x := by
    apply tendsto_nhds_unique hlim
    simpa only [heval] using hψlim x
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero φ hφK)] at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact he
  · intro y hy
    have hyL : y ∉ tsupport (P201Specs.laplacian φ) :=
      fun h => hy (hs (tsupport_laplacian_subset φ h))
    simp [image_eq_zero_of_notMem_tsupport hyL]

end P201.GreenCompactC2
