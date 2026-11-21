import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.HartmanGrobman
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.BoundedNonlinearConjugacy
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.Cutoff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch20.HartmanGrobman
open D13Unified.Ch07 D13Unified.Ch20.Green
open D13Unified.Ch20.BoundedNonlinearConjugacy
open Specs.D13Unified.Ch07.MatrixExponential

variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Pointwise continuous, uniformly bounded families may be passed through
both improper Green integrals. No uniform convergence on all time is used. -/
lemma green_parameter_continuous {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α)
    (g : X → (ℝ →ᵇ E)) (hg : ∀ s, Continuous (fun x => g x s))
    (M : ℝ) (hM : ∀ x, ‖g x‖ ≤ M) (t : ℝ) :
    Continuous (fun x => greenValue b A (g x) t) := by
  have hK : 0 ≤ K := le_trans zero_le_one h.1
  have hs : Continuous (fun x => ∫ s in Iic t, kernel b A true (g x) t s) := by
    apply continuous_of_dominated
      (bound := fun s => (K*M*Real.exp (-α*t))*Real.exp (α*s))
    · intro x
      exact (kernel_continuous b A true (g x) t).aestronglyMeasurable
    · intro x
      filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
      rw [← stable_majorant_eq]
      exact (stable_kernel_bound b A h (g x) t s hs).trans (by
        gcongr; exact hM x)
    · exact (integrableOn_exp_mul_Iic h.2.1 t).const_mul _
    · apply ae_of_all
      intro s
      exact (matrixOperatorEquiv b
        (exponentialValue A (t-s) * Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A true)).continuous.comp (hg s)
  have hu : Continuous (fun x => ∫ s in Ioi t, kernel b A false (g x) t s) := by
    apply continuous_of_dominated
      (bound := fun s => (K*M*Real.exp (α*t))*Real.exp (-α*s))
    · intro x
      exact (kernel_continuous b A false (g x) t).aestronglyMeasurable
    · intro x
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [← unstable_majorant_eq]
      exact (unstable_kernel_bound b A h (g x) t s hs.le).trans (by
        gcongr; exact hM x)
    · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr h.2.1) t).const_mul _
    · apply ae_of_all
      intro s
      exact (matrixOperatorEquiv b
        (exponentialValue A (t-s) * Specs.D13Unified.Ch20.Dichotomy.projectionMatrix A false)).continuous.comp (hg s)
  exact hs.sub hu

/-- The same integrable exponential used for dominated convergence gives
uniformly small tails, independently of the parameter and forcing. -/
theorem green_tails : Specs.D13Unified.Ch20.HartmanGrobman.tailsExpected := by
  intro n E _ _ _ _ _ b A K α h M t R hR g hM
  have hK : 0 ≤ K := le_trans zero_le_one h.1
  have hs : ‖∫ s in Iic (t-R), kernel b A true g t s‖ ≤
      (K/α)*M*Real.exp (-α*R) := by
    have hmaj := (integrableOn_exp_mul_Iic h.2.1 (t-R)).const_mul
      (K*M*Real.exp (-α*t))
    have hi : (∫ s in Iic (t-R), (K*M*Real.exp (-α*t))*Real.exp (α*s)) =
        (K/α)*M*Real.exp (-α*R) := by
      rw [integral_const_mul, integral_exp_mul_Iic h.2.1]
      calc
        _ = (K/α)*M*(Real.exp (-α*t)*Real.exp (α*(t-R))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 3; ring
    rw [← hi]
    apply norm_integral_le_of_norm_le hmaj
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
    rw [← stable_majorant_eq]
    exact (stable_kernel_bound b A h g t s (by change s ≤ t-R at hs; linarith)).trans (by
      gcongr)
  have hu : ‖∫ s in Ioi (t+R), kernel b A false g t s‖ ≤
      (K/α)*M*Real.exp (-α*R) := by
    have hmaj := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr h.2.1) (t+R)).const_mul
      (K*M*Real.exp (α*t))
    have hi : (∫ s in Ioi (t+R), (K*M*Real.exp (α*t))*Real.exp (-α*s)) =
        (K/α)*M*Real.exp (-α*R) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr h.2.1)]
      calc
        _ = (K/α)*M*(Real.exp (α*t)*Real.exp (-α*(t+R))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 3; ring
    rw [← hi]
    apply norm_integral_le_of_norm_le hmaj
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [← unstable_majorant_eq]
    exact (unstable_kernel_bound b A h g t s (by change t+R < s at hs; linarith)).trans (by
      gcongr)
  calc
    _ ≤ (K/α)*M*Real.exp (-α*R) + (K/α)*M*Real.exp (-α*R) := add_le_add hs hu
    _ = _ := by ring

/-- Joint continuity gives uniform dependence on each compact time set.
This applies both to the linear orbits and the complete nonlinear flow. -/
lemma compact_time_convergence (γ : ℝ → E → E)
    (hγ : Continuous (Function.uncurry γ)) (x : E) (J : Set ℝ) (hJ : IsCompact J) :
    TendstoUniformlyOn (fun y t => γ t y) (fun t => γ t x) (𝓝 x) J := by
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  apply Continuous.tendstoUniformly
  exact hγ.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

lemma linear_orbit_compact_convergence (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (x : E) (J : Set ℝ) (hJ : IsCompact J) :
    TendstoUniformlyOn (fun y t => evolution b A t y) (fun t => evolution b A t x) (𝓝 x) J :=
  compact_time_convergence _
    (((evolution_continuous b A).comp continuous_fst).clm_apply continuous_snd) x J hJ

/-- The Green contraction at a given linear initial state. -/
def picardOperator (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (x : E) (z : ℝ →ᵇ E) : ℝ →ᵇ E :=
  greenMap b A hA h (forcing r (linearOrbit b A x) z)

lemma picardOperator_sub_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (L : ℝ≥0) (hr : LipschitzWith L r) (x : E) (z w : ℝ →ᵇ E) :
    ‖picardOperator b A hA h r x z - picardOperator b A hA h r x w‖ ≤
      ((2*K/α)*(L : ℝ))*‖z-w‖ := by
  have hC : 0 ≤ 2*K/α := by positivity [h.1, h.2.1]
  unfold picardOperator
  rw [← greenMap_sub]
  calc
    _ ≤ (2*K/α)*‖forcing r (linearOrbit b A x) z - forcing r (linearOrbit b A x) w‖ :=
      greenMap_bound b A hA h _
    _ ≤ (2*K/α)*((L : ℝ)*‖z-w‖) := mul_le_mul_of_nonneg_left
      (forcing_sub_bound r L hr _ z w) hC
    _ = _ := by ring

/-- Each finite Picard iterate is pointwise continuous in the initial state.
The norm of the forcing is bounded by ‖r‖ independently of state and iterate. -/
lemma picard_iterate_continuous (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (j : ℕ) (t : ℝ) :
    Continuous (fun x => (picardOperator b A hA h r x)^[j] 0 t) := by
  induction j generalizing t with
  | zero => simpa using (continuous_const : Continuous (fun _ : E => (0 : E)))
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    apply green_parameter_continuous b A h
      (fun x => forcing r (linearOrbit b A x) ((picardOperator b A hA h r x)^[j] 0))
      _ ‖r‖ (fun _ => forcing_bound _ _ _) t
    intro s
    exact r.continuous.comp ((evolution b A s).continuous.add (ih s))

/-- Uniform contraction error permits a uniform limit in the STATE variable,
without demanding global uniform dependence of the linear orbit in time. -/
lemma correction_parameter_continuous (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (hA : IsHyperbolic A) {K α : ℝ} (h : DichotomyBounds b A K α)
    (r : E →ᵇ E) (L : ℝ≥0) (hr : LipschitzWith L r)
    (hq : (2*K/α)*(L : ℝ) < 1) (z : E → (ℝ →ᵇ E))
    (hz : ∀ x, IsCorrection b A r x (z x))
    (hb : ∀ x, ‖z x‖ ≤ (2*K/α)*‖r‖) (t : ℝ) :
    Continuous (fun x => z x t) := by
  let q : ℝ := (2*K/α)*(L : ℝ)
  let M : ℝ := (2*K/α)*‖r‖
  have hq0 : 0 ≤ q := by dsimp [q]; positivity [h.1, h.2.1]
  have hfixed (x : E) : picardOperator b A hA h r x (z x) = z x :=
    (correction_iff_fixed b A hA h r x (z x)).mp (hz x)
  have herr (j : ℕ) (x : E) :
      ‖(picardOperator b A hA h r x)^[j] 0 - z x‖ ≤ q^j*M := by
    induction j with
    | zero => simpa [M] using hb x
    | succ j ih =>
      rw [Function.iterate_succ_apply', ← hfixed x]
      calc
        _ ≤ q * ‖(picardOperator b A hA h r x)^[j] 0 - z x‖ :=
          picardOperator_sub_bound b A hA h r L hr x _ _
        _ ≤ q * (q^j*M) := mul_le_mul_of_nonneg_left ih hq0
        _ = q^(j+1)*M := by ring
  have hlim : Tendsto (fun j : ℕ => q^j*M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const M
  have hu : TendstoUniformly
      (fun j x => (picardOperator b A hA h r x)^[j] 0 t) (fun x => z x t) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with j hj x
    rw [dist_eq_norm, norm_sub_rev]
    exact ((((picardOperator b A hA h r x)^[j] 0 - z x).norm_coe_le_norm t).trans (herr j x)).trans_lt hj
  exact hu.continuous (Filter.Eventually.frequently (Eventually.of_forall (fun j => picard_iterate_continuous b A hA h r j t)))

/-- Continuity upgrades the previously constructed bijection to a homeomorphism.
Finite Picard iterates and dominated convergence prove forward continuity;
the explicit Green formula proves continuity of the inverse. -/
theorem complete_conjugacy :
    Specs.D13Unified.Ch20.HartmanGrobman.completeConjugacyExpected := by
  intro n E _ _ _ _ _ b A hA K α h r L hrC hr0 hr hq φ hφc hφ0 hφ
  obtain ⟨z, e, hzc, hzb, he, he0, hshift, hconj, hinv⟩ :=
    bounded_conjugacy b A hA K α h r L hrC hr0 hr hq φ hφ0 hφ
  have hec : Continuous (e : E → E) := by
    have hc := correction_parameter_continuous b A hA h r L hr hq z
      (fun x => (hzc x).1) hzb 0
    exact (continuous_id.add hc).congr (fun x => (he x).symm)
  let g : E → (ℝ →ᵇ E) := fun y => r.compContinuous
    ⟨fun t => φ t y, hφc.comp (continuous_id.prodMk continuous_const)⟩
  have hginv (y : E) : e.symm y = y - greenValue b A (g y) 0 := by
    obtain ⟨k, hk, heq⟩ := hinv y
    have hkg : k = g y := BoundedContinuousFunction.ext hk
    rwa [hkg] at heq
  have heic : Continuous (e.symm : E → E) := by
    have hc := green_parameter_continuous b A h g
      (fun t => r.continuous.comp (hφc.comp (continuous_const.prodMk continuous_id)))
      ‖r‖ (fun _ => BoundedContinuousFunction.norm_compContinuous_le _ _) 0
    exact (continuous_id.sub hc).congr (fun y => (hginv y).symm)
  let H : E ≃ₜ E := ⟨e, hec, heic⟩
  have hzformula (t : ℝ) (x : E) :
      z x t = φ t (e x) - evolution b A t x := by
    have h1 := he (evolution b A t x)
    have h2 := hconj t x
    have h3 := hshift x t 0
    change z (evolution b A t x) 0 = z x (0+t) at h3
    rw [zero_add] at h3
    change e (evolution b A t x) = evolution b A t x + z (evolution b A t x) 0 at h1
    change e (evolution b A t x) = φ t (e x) at h2
    rw [h3, h2] at h1
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact h1.symm)
  have hzcJoint : Continuous (fun q : ℝ × E => z q.2 q.1) := by
    have h1 : Continuous (fun q : ℝ × E => φ q.1 (e q.2)) :=
      hφc.comp (continuous_fst.prodMk (hec.comp continuous_snd))
    have h2 : Continuous (fun q : ℝ × E => evolution b A q.1 q.2) :=
      ((evolution_continuous b A).comp continuous_fst).clm_apply continuous_snd
    exact (h1.sub h2).congr (fun q => (hzformula q.1 q.2).symm)
  refine ⟨z, H, hzc, hzb, he, he0, hconj, hzcJoint, ?_, hinv⟩
  intro x J hJ
  exact compact_time_convergence (fun t x => z x t) hzcJoint x J hJ

omit [FiniteDimensional ℝ E] in
/-- Uniqueness on any interval, with an arbitrary starting time and no
finite-endpoint restriction on the interval. -/
lemma trajectories_eqOn_interval (v : E → E) (L : ℝ≥0) (hv : LipschitzWith L v)
    {J : Set ℝ} (hJ : OrdConnected J) (s : ℝ) (hs : s ∈ J)
    (y w : ℝ → E) (hy : ∀ t ∈ J, HasDerivAt y (v (y t)) t)
    (hw : ∀ t ∈ J, HasDerivAt w (v (w t)) t) (hinit : y s = w s) :
    EqOn y w J := by
  intro t ht
  rcases le_total s t with hpos | hneg
  · have hsub : Icc s t ⊆ J := hJ.out hs ht
    exact ODE_solution_unique (fun _ => hv)
      (HasDerivAt.continuousOn (fun q hq => hy q (hsub hq)))
      (fun q hq => (hy q (hsub (Ico_subset_Icc_self hq))).hasDerivWithinAt)
      (HasDerivAt.continuousOn (fun q hq => hw q (hsub hq)))
      (fun q hq => (hw q (hsub (Ico_subset_Icc_self hq))).hasDerivWithinAt)
      hinit ⟨hpos, le_rfl⟩
  · have hsub : Icc t s ⊆ J := hJ.out ht hs
    exact ODE_solution_unique_of_mem_Icc_left (s := fun _ => univ)
      (fun _ _ => hv.lipschitzOnWith)
      (HasDerivAt.continuousOn (fun q hq => hy q (hsub hq)))
      (fun q hq => (hy q (hsub (Ioc_subset_Icc_self hq))).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
      (HasDerivAt.continuousOn (fun q hq => hw q (hsub hq)))
      (fun q hq => (hw q (hsub (Ioc_subset_Icc_self hq))).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hinit ⟨le_rfl, hneg⟩

/-- Hartman--Grobman for the original C¹ germ at an arbitrary hyperbolic
zero. The complete extension is used only to construct the homeomorphism;
all original trajectory comparisons retain their actual neighborhoods. -/
theorem local_conjugacy : Specs.D13Unified.Ch20.HartmanGrobman.localConjugacyExpected := by
  intro n E _ _ _ _ _ b A U f p hU hp hf hfp hder hA
  let B : E →L[ℝ] E := matrixOperatorEquiv b A
  let U₀ : Set E := (fun x => p+x) ⁻¹' U
  let f₀ : E → E := fun x => f (p+x)
  have hU₀ : IsOpen U₀ := hU.preimage (continuous_const.add continuous_id)
  have h0 : (0 : E) ∈ U₀ := by simpa [U₀] using hp
  have hf₀ : ContDiffOn ℝ 1 f₀ U₀ :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx => hx)
  have hf₀0 : f₀ 0 = 0 := by simpa [f₀] using hfp
  have hd₀ : HasFDerivAt f₀ B 0 := by
    have hd : HasFDerivAt f B (p+(0 : E)) := by simpa [B] using hder
    simpa [f₀, Function.comp_def] using hd.comp 0 ((hasFDerivAt_id (0 : E)).const_add p)
  obtain ⟨K, α, hK, hα, hdich⟩ := exponential_dichotomy b A hA
  have h : DichotomyBounds b A K α := ⟨hK, hα, hdich⟩
  let C : ℝ := 2*K/α
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := 1/(2*C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : (2*K/α)*δ < 1 := by
    change C*δ < 1
    have heq : C*δ = 1/2 := by dsimp [δ]; field_simp
    rw [heq]; norm_num
  obtain ⟨r₀, hr, hrc, hr0, _, hrlip, ⟨V₀, hV₀, hV₀0, hV₀U, hlocal⟩, _, hflow⟩ :=
    Cutoff.cutoff U₀ f₀ B 1 hU₀ h0 le_rfl hf₀ hf₀0 hd₀ δ hδ
  obtain ⟨M, hM⟩ := hr.continuous.bounded_above_of_compact_support hrc
  let r : E →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup r₀ hr.continuous M hM
  let L : ℝ≥0 := ⟨δ, hδ.le⟩
  have hrL : LipschitzWith L r := lipschitzWith_iff_norm_sub_le.mpr hrlip
  obtain ⟨φ, hφc, hφ0, _, hφ⟩ := hflow
  obtain ⟨z, e, _, _, _, he0, hconj, _, _, _⟩ :=
    complete_conjugacy b A hA K α h r L hr hr0 hrL hsmall φ hφc hφ0 hφ
  let H : E ≃ₜ E := e.trans (Homeomorph.addLeft p)
  let W : Set E := (fun y => y-p) ⁻¹' V₀
  let V : Set E := H ⁻¹' W
  have hW : IsOpen W := hV₀.preimage (continuous_id.sub continuous_const)
  have hpW : p ∈ W := by simpa [W] using hV₀0
  have hHU : W ⊆ U := by
    intro y hy
    have := hV₀U hy
    simpa [U₀] using this
  have hH0 : H 0 = p := by simp [H, he0]
  have htrack (t : ℝ) (x : E) : H (evolution b A t x) = p+φ t (e x) := by
    change p+e (evolution b A t x) = _
    congr 1
    exact hconj t x
  have himage : H '' V = W := image_preimage_eq _ H.surjective
  refine ⟨H, V, W, hW.preimage H.continuous, hW, ?_, hpW, hHU, hH0, himage, ?_, ?_⟩
  · change H 0 ∈ W
    rwa [hH0]
  · intro x _ s J _ hJ t ht
    have hw : H (evolution b A (t-s) x) ∈ W := hJ t ht
    refine ⟨hw, ?_⟩
    have hm : φ (t-s) (e x) ∈ V₀ := by simpa [W, htrack (t-s) x] using hw
    have heq := hlocal _ hm
    change B (φ (t-s) (e x)) + r (φ (t-s) (e x)) = f (p+φ (t-s) (e x)) at heq
    have hdshift := (hφ (e x) (t-s)).scomp t ((hasDerivAt_id t).sub_const s)
    have hd : HasDerivAt (fun q => p+φ (q-s) (e x))
        (B (φ (t-s) (e x))+r (φ (t-s) (e x))) t := by
      simpa only [r, BoundedContinuousFunction.coe_ofNormedAddCommGroup, Function.comp_def, id_eq, one_smul] using hdshift.const_add p
    rw [heq] at hd
    have heqfun : (fun q => H (matrixOperatorEquiv b (exponentialValue A (q-s)) x)) =
        fun q => p+φ (q-s) (e x) := funext (fun q => htrack (q-s) x)
    rw [heqfun, show H (matrixOperatorEquiv b (exponentialValue A (t-s)) x) =
      p+φ (t-s) (e x) from htrack (t-s) x]
    exact hd
  · intro J _ hJ s hs y hy hyd t ht _
    let w : ℝ → E := fun q => y q-p
    have hw (q : ℝ) (hq : q ∈ J) : HasDerivAt w (B (w q)+r (w q)) q := by
      have heq := hlocal (w q) (hy q hq)
      change B (w q)+r (w q) = f (p+w q) at heq
      have hd := (hyd q hq).sub_const p
      change HasDerivAt w (f (y q)) q at hd
      rw [heq]
      have hpw : p+w q = y q := by dsimp [w]; abel
      rw [hpw]
      exact hd
    have hinit : e (H.symm (y s)) = w s := by
      have hh := H.apply_symm_apply (y s)
      change p+e (H.symm (y s)) = y s at hh
      dsimp [w]
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh)
    have hφshift (q : ℝ) : HasDerivAt (fun a => φ (a-s) (e (H.symm (y s))))
        (B (φ (q-s) (e (H.symm (y s))))+r (φ (q-s) (e (H.symm (y s))))) q := by
      simpa only [r, BoundedContinuousFunction.coe_ofNormedAddCommGroup, Function.comp_def, id_eq, one_smul] using
        (hφ (e (H.symm (y s))) (q-s)).scomp q ((hasDerivAt_id q).sub_const s)
    have heq := trajectories_eqOn_interval (fun x => B x+r x)
      (‖B‖₊ + L) (B.lipschitzWith.add hrL) hJ s hs
      (fun q => φ (q-s) (e (H.symm (y s)))) w
      (fun q _ => hφshift q) hw (by rw [sub_self, hφ0, hinit]) ht
    change φ (t-s) (e (H.symm (y s))) = w t at heq
    change H (evolution b A (t-s) (H.symm (y s))) = _
    rw [htrack, heq]
    dsimp [w]; abel

end D13Unified.Ch20.HartmanGrobman
