import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.ClassicalWave
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.EvenWave
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.SmoothCone
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Classical Cauchy solutions from the accepted velocity propagators.
The constructions use compact parameter integrals, and uniqueness uses only
local cone estimates. No global energy or growth condition is imposed. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace P201.ClassicalWave
open P201Specs P201Specs.ClassicalWave

/-- Restriction of a half-space classical solution to any compact backward cone. -/
theorem IsClassicalWave.toLocal {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {u v f : ℝ → Space n → 𝕜}
    (h : IsClassicalWave c u v f) (a : Space n) (R T : ℝ) :
    P201Specs.SmoothCone.IsLocalSmoothWave c a R T u v f := by
  have hsub : P201Specs.SmoothCone.timeSlab T ⊆ Ici 0 ×ˢ (univ : Set (Space n)) :=
    fun z hz => ⟨hz.1.1, mem_univ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (h.displacement_regular z ⟨hz.1.1, mem_univ _⟩).mono hsub
  · intro z hz
    exact (h.velocity_regular z ⟨hz.1.1, mem_univ _⟩).mono hsub
  · exact h.forcing_continuous.mono (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  · intro s hs x _
    exact (h.displacement_derivative s hs.1 x).mono (fun _ hy => hy.1)
  · intro s hs x _
    exact (h.wave_equation s hs.1 x).mono (fun _ hy => hy.1)

/-- Global uniqueness follows by choosing a different finite cone for each
point. The comparison functions need only local C² regularity. -/
theorem classical_uniqueness : UniquenessStatement := by
  intro n hn 𝕜 _ c hc u₁ v₁ u₂ v₂ f h₁ h₂ hg hh t ht x
  have hR : 0 < c * t + 1 := by positivity
  have hT : t < (c * t + 1) / c := (lt_div_iff₀ hc).mpr (by nlinarith)
  exact P201.SmoothCone.localUniqueness 𝕜 hn c x (c * t + 1) t
    u₁ v₁ f u₂ v₂ f hc hR ht hT (IsClassicalWave.toLocal h₁ _ _ _) (IsClassicalWave.toLocal h₂ _ _ _)
    (fun y _ => hg y) (fun y _ => hh y) (fun _ _ _ _ => rfl)
    t ⟨ht, le_rfl⟩ x (by simp [P201Specs.SmoothCone.coneBall])

/-- The canonical one-dimensional coordinate turns the spatial directional
derivative into the ordinary real derivative. -/
theorem line_directional {𝕜 : Type} [RCLike 𝕜] {h : Space 1 → 𝕜}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x : Space 1) :
    P201.OddWave.directional h (coordinate 1 0) x =
      deriv (fun y => h (P102.Trace.Ordinary.lineIsometry y)) (x 0) := by
  have he : P102.Trace.Ordinary.lineIsometry (x 0) = x :=
    P102.Trace.Ordinary.lineIsometry.apply_symm_apply x
  have hd := (hh.differentiable (by simp) (P102.Trace.Ordinary.lineIsometry (x 0))).hasFDerivAt.comp_hasDerivAt (x 0)
    (P102.Trace.Ordinary.lineIsometry.toContinuousLinearEquiv.toContinuousLinearMap.hasDerivAt)
  have hv : (P102.Trace.Ordinary.lineIsometry.toContinuousLinearEquiv.toContinuousLinearMap)
      (1 : ℝ) = coordinate 1 0 := by
    ext i
    fin_cases i
    change (P102.Trace.Ordinary.linePoint (1 : ℝ)) 0 = (coordinate 1 0) 0
    simp [P102.Trace.Ordinary.linePoint, coordinate, P201Specs.coordinate, P102.U4.coordinateVector]
  simpa only [he, hv, P201.OddWave.directional, Function.comp_def] using hd.deriv.symm

/-- In dimension one the shared coordinate-sum Laplacian is the second real
derivative, with the same Euclidean coordinate as in the integral formula. -/
theorem laplacian_line {𝕜 : Type} [RCLike 𝕜] {h : Space 1 → 𝕜}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x : Space 1) :
    laplacian h x = deriv (deriv (fun y => h (P102.Trace.Ordinary.lineIsometry y))) (x 0) := by
  rw [P201.OddWave.laplacian_eq_sum_directional]
  simp only [Fin.sum_univ_one]
  rw [line_directional (P201.OddWave.directional_contDiff hh _) x]
  congr 1
  funext y
  rw [line_directional hh]
  rfl

/-- Joint smoothness of the time derivative of a jointly smooth function. -/
theorem time_derivative_contDiff {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : ℝ → Space n → 𝕜}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space n => deriv (fun s => u s p.2) p.1) := by
  have hd := P201.OddWave.contDiff_radial_deriv
    (F := fun x t => u t x) (hu.comp (contDiff_snd.prodMk contDiff_fst))
  exact hd.comp (contDiff_snd.prodMk contDiff_fst)

/-- The spatial Laplacian commutes with the time derivative on smooth fields. -/
theorem laplacian_time_derivative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : ℝ → Space n → 𝕜}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u)) (t : ℝ) (x : Space n) :
    laplacian (fun y => deriv (fun s => u s y) t) x =
      deriv (fun s => laplacian (u s) x) t := by
  have hswap : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ => u p.2 p.1) :=
    hu.comp (contDiff_snd.prodMk contDiff_fst)
  exact P201.OddWave.laplacian_radial_deriv hswap x t

/-- A globally smooth solution is classical on the half-space, with genuine
one-sided endpoint derivatives. -/
theorem classical_of_smooth {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {u f : ℝ → Space n → 𝕜}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    (hf : Continuous (Function.uncurry f))
    (hpde : ∀ t x, deriv (deriv (fun s => u s x)) t =
      c ^ 2 • laplacian (u t) x + f t x) :
    IsClassicalWave c u (fun t x => deriv (fun s => u s x) t) f := by
  have hd := time_derivative_contDiff hu
  refine ⟨(hu.of_le (by simp)).contDiffOn, (hd.of_le (by simp)).contDiffOn,
    hf.continuousOn, ?_, ?_⟩
  · intro t _ x
    exact ((hu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt.hasDerivWithinAt
  · intro t _ x
    rw [← hpde t x]
    exact ((hd.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt.hasDerivWithinAt


/-- Differentiating a smooth wave produces another wave. -/
theorem time_derivative_wave {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {u : ℝ → Space n → 𝕜}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    (hpde : ∀ t x, deriv (deriv (fun s => u s x)) t = c ^ 2 • laplacian (u t) x)
    (t : ℝ) (x : Space n) :
    deriv (deriv (fun s => deriv (fun q => u q x) s)) t =
      c ^ 2 • laplacian (fun y => deriv (fun s => u s y) t) x := by
  have he : deriv (deriv (fun s => u s x)) = fun s => c ^ 2 • laplacian (u s) x :=
    funext fun s => hpde s x
  rw [he, deriv_fun_const_smul_field, laplacian_time_derivative hu]

/-- Integration over a fixed compact interval preserves smooth parameter
regularity, with no bound on the integrand outside compact sets. -/
theorem contDiff_fixed_interval {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [ProperSpace H] [FiniteDimensional ℝ H] {𝕜 : Type} [RCLike 𝕜]
    {F : H → ℝ → 𝕜} (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => ∫ s in a..b, F p s) := by
  let μ : Measure ℝ := volume.restrict (uIoc a b)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, uIoc]⟩
  have hμ : ∀ᵐ s ∂μ, s ∈ uIcc a b := by
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with s hs
    exact Ioc_subset_Icc_self hs
  have hi := P201.OddWave.contDiff_integral_compact (μ := μ) isCompact_uIcc hμ hF
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc] using
    hi.const_smul (if a ≤ b then (1 : ℝ) else -1)

/-- Rescaling to the fixed interval [0,1] proves smoothness with a moving
upper endpoint, including the zero-length interval. -/
theorem contDiff_variable_interval {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [ProperSpace H] [FiniteDimensional ℝ H] {𝕜 : Type} [RCLike 𝕜]
    {F : H → ℝ → 𝕜} (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : H × ℝ => ∫ s in (0 : ℝ)..p.2, F p.1 s) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : (H × ℝ) × ℝ => F p.1.1 (p.1.2 * p.2)) :=
    hF.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd))
  have hi := contDiff_fixed_interval (F := fun (p : H × ℝ) s => F p.1 (p.2 * s)) hG 0 1
  have he (p : H × ℝ) :
      p.2 • (∫ s in (0 : ℝ)..1, F p.1 (p.2 * s)) = ∫ s in (0 : ℝ)..p.2, F p.1 s := by
    simpa only [mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (F p.1) p.2 (a := 0) (b := 1)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun p : H × ℝ =>
      p.2 • (∫ s in (0 : ℝ)..1, F p.1 (p.2 * s))) := contDiff_snd.smul hi
  simpa only [he] using hsm

/-- Parameter differentiation under an arbitrary finite interval. -/
theorem deriv_fixed_interval {𝕜 : Type} [RCLike 𝕜] {F : ℝ → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) (a b t : ℝ) :
    deriv (fun p => ∫ s in a..b, F p s) t =
      ∫ s in a..b, deriv (fun p => F p s) t := by
  let μ : Measure ℝ := volume.restrict (uIoc a b)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, uIoc]⟩
  have hμ : ∀ᵐ s ∂μ, s ∈ uIcc a b := by
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with s hs
    exact Ioc_subset_Icc_self hs
  have hd := P201.OddWave.hasFDerivAt_integral_compact (μ := μ) isCompact_uIcc hμ hF t
  have hi : Integrable (fun s => fderiv ℝ (fun p => F p s) t) μ :=
    P201.OddWave.integrable_of_continuous_compact isCompact_uIcc hμ
      ((P201.OddWave.contDiff_parameter_fderiv hF).continuous.comp
        (continuous_const.prodMk continuous_id))
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [deriv_fun_const_smul_field]
  congr 1
  change (fderiv ℝ (fun p => ∫ s, F p s ∂μ) t) 1 = _
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  rfl

/-- Leibniz's rule for a smooth kernel and a moving upper endpoint. -/
theorem deriv_variable_interval {𝕜 : Type} [RCLike 𝕜] {F : ℝ → ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) (t : ℝ) :
    deriv (fun p => ∫ s in (0 : ℝ)..p, F p s) t =
      (∫ s in (0 : ℝ)..t, deriv (fun p => F p s) t) + F t t := by
  let J : ℝ × ℝ → 𝕜 := fun p => ∫ s in (0 : ℝ)..p.2, F p.1 s
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J := contDiff_variable_interval hF
  have hd := (hJ.differentiable (by simp) (t, t)).hasFDerivAt
  have hl := hd.comp_hasDerivAt (f := fun s => (s, t)) t ((hasDerivAt_id t).prodMk (hasDerivAt_const t t))
  have hr := hd.comp_hasDerivAt (f := fun s => (t, s)) t ((hasDerivAt_const t t).prodMk (hasDerivAt_id t))
  have hb := hd.comp_hasDerivAt (f := fun s => (s, s)) t ((hasDerivAt_id t).prodMk (hasDerivAt_id t))
  have hc : Continuous (F t) := hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hright : deriv (fun b => ∫ s in (0 : ℝ)..b, F t s) t = F t t :=
    intervalIntegral.deriv_integral_right (hc.intervalIntegrable _ _)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  calc
    _ = fderiv ℝ J (t, t) (1, 1) := hb.deriv
    _ = fderiv ℝ J (t, t) (1, 0) + fderiv ℝ J (t, t) (0, 1) := by
      rw [← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    _ = deriv (fun p => ∫ s in (0 : ℝ)..t, F p s) t +
        deriv (fun b => ∫ s in (0 : ℝ)..b, F t s) t := by rw [← hl.deriv, ← hr.deriv]; rfl
    _ = _ := by rw [deriv_fixed_interval hF, hright]

/-- Spatial differentiation under a finite interval integral. -/
theorem directional_fixed_interval {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {F : Space n → ℝ → 𝕜} (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F))
    (a b : ℝ) (v x : Space n) :
    P201.OddWave.directional (fun p => ∫ s in a..b, F p s) v x =
      ∫ s in a..b, P201.OddWave.directional (fun p => F p s) v x := by
  let μ : Measure ℝ := volume.restrict (uIoc a b)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, uIoc]⟩
  have hμ : ∀ᵐ s ∂μ, s ∈ uIcc a b := by
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with s hs
    exact Ioc_subset_Icc_self hs
  have hd := P201.OddWave.hasFDerivAt_integral_compact (μ := μ) isCompact_uIcc hμ hF x
  have hi : Integrable (fun s => fderiv ℝ (fun p => F p s) x) μ :=
    P201.OddWave.integrable_of_continuous_compact isCompact_uIcc hμ
      ((P201.OddWave.contDiff_parameter_fderiv hF).continuous.comp
        (continuous_const.prodMk continuous_id))
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [P201.OddWave.directional_const_smul]
  congr 1
  change (fderiv ℝ (fun p => ∫ s, F p s ∂μ) x) v = _
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  rfl

/-- The actual coordinate-sum Laplacian commutes with a smooth finite integral. -/
theorem laplacian_fixed_interval {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {F : Space n → ℝ → 𝕜} (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F))
    (a b : ℝ) (x : Space n) :
    laplacian (fun p => ∫ s in a..b, F p s) x = ∫ s in a..b, laplacian (fun p => F p s) x := by
  have hd (v : Space n) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Space n × ℝ => P201.OddWave.directional (fun y => F y p.2) v p.1) :=
    (P201.OddWave.contDiff_parameter_fderiv hF).clm_apply contDiff_const
  have hi (i : Fin n) : IntervalIntegrable (fun s => P201.OddWave.directional
      (P201.OddWave.directional (fun p => F p s) (coordinate n i)) (coordinate n i) x) volume a b := by
    have hc : Continuous (fun s => P201.OddWave.directional
        (P201.OddWave.directional (fun p => F p s) (coordinate n i)) (coordinate n i) x) :=
      (P201.OddWave.contDiff_parameter_fderiv
        (F := fun y s => P201.OddWave.directional (fun p => F p s) (coordinate n i) y)
        (hd (coordinate n i))).continuous.clm_apply continuous_const |>.comp
          (continuous_const.prodMk continuous_id)
    exact hc.intervalIntegrable _ _
  rw [P201.OddWave.laplacian_eq_sum_directional]
  calc
    _ = ∑ i : Fin n, ∫ s in a..b, P201.OddWave.directional
        (P201.OddWave.directional (fun p => F p s) (coordinate n i)) (coordinate n i) x := by
      apply Finset.sum_congr rfl
      intro i _
      have he : P201.OddWave.directional (fun p => ∫ s in a..b, F p s) (coordinate n i) =
          fun y => ∫ s in a..b, P201.OddWave.directional (fun p => F p s) (coordinate n i) y :=
        funext fun y => directional_fixed_interval hF a b (coordinate n i) y
      rw [he]
      exact directional_fixed_interval
        (F := fun y s => P201.OddWave.directional (fun p => F p s) (coordinate n i) y)
        (hd (coordinate n i)) a b (coordinate n i) x
    _ = ∫ s in a..b, ∑ i : Fin n, P201.OddWave.directional
        (P201.OddWave.directional (fun p => F p s) (coordinate n i)) (coordinate n i) x := by
      rw [intervalIntegral.integral_finsetSum]
      intro i _
      exact hi i
    _ = _ := by simp_rw [P201.OddWave.laplacian_eq_sum_directional]

/-- Smooth dependence of a spherical mean on an additional data parameter. -/
theorem sphericalMean_parameter_contDiff {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : ℝ → Space n → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × Space n) × ℝ =>
      P201Specs.OddWave.sphericalMean (f p.1.1) p.1.2 p.2) := by
  have hi := P201.OddWave.contDiff_integral_compact (μ := P201Specs.unitSurface n)
    (isCompact_sphere (0 : Space n) 1) (P201.MeanValues.unitSurface_ae_mem n)
    (F := fun p : (ℝ × Space n) × ℝ => fun θ : Space n =>
      f p.1.1 (p.1.2 + p.2 • θ))
    (hf.comp (contDiff_fst.fst.fst.prodMk
      (contDiff_fst.fst.snd.add (contDiff_fst.snd.smul contDiff_snd))))
  exact hi.const_smul ((P201Specs.omega n)⁻¹)

/-- The regular radial extension also preserves smooth dependence on the data
parameter, including at time zero. -/
theorem velocityOdd_parameter_contDiff {𝕜 : Type} [RCLike 𝕜] (m : ℕ)
    {c : ℝ} (hc : c ≠ 0) {f : ℝ → Space (2 * m + 3) → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × Space (2 * m + 3) =>
      P201Specs.OddWave.velocityOdd c (f p.1.1) p.1.2 p.2) := by
  have hs := sphericalMean_parameter_contDiff hf
  have hsr (s : ℝ) (x : Space (2 * m + 3)) :
      ContDiff ℝ (⊤ : ℕ∞) (P201Specs.OddWave.sphericalMean (f s) x) :=
    hs.comp ((contDiff_const.prodMk contDiff_const).prodMk contDiff_id)
  simp_rw [P201.OddWave.velocityOdd_eq_regularRadial m hc _ (hsr _)]
  exact ((P201.OddWave.regularRadial_joint_contDiff m
    (F := fun (p : ℝ × Space (2 * m + 3)) r => P201Specs.OddWave.sphericalMean (f p.1) p.2 r) hs).comp
    ((contDiff_fst.fst.prodMk contDiff_snd).prodMk
      (contDiff_const.mul contDiff_fst.snd))).const_smul _

/-- Parameter regularity for every odd dimension at least three. -/
theorem velocityOdd_parameter_contDiff_of_odd {n : ℕ} (hn : 3 ≤ n) (ho : Odd n)
    {𝕜 : Type} [RCLike 𝕜] {c : ℝ} (hc : c ≠ 0) {f : ℝ → Space n → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × Space n =>
      P201Specs.OddWave.velocityOdd c (f p.1.1) p.1.2 p.2) := by
  obtain ⟨k, hk⟩ := ho
  have he : n = 2 * (k - 1) + 3 := by omega
  clear hk
  subst n
  exact velocityOdd_parameter_contDiff (k - 1) hc hf

/-- Descent gives smooth data-parameter dependence in even dimension directly
from the defined lift. -/
theorem velocityEven_parameter_contDiff {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    {𝕜 : Type} [RCLike 𝕜] {c : ℝ} (hc : c ≠ 0) {f : ℝ → Space n → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × Space n =>
      P201Specs.EvenWave.velocityEven c (f p.1.1) p.1.2 p.2) := by
  have hl : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Space (n + 1) => f p.1 (P201Specs.EvenWave.projection n p.2)) :=
    hf.comp (contDiff_fst.prodMk ((P201Specs.EvenWave.projection n).contDiff.comp contDiff_snd))
  have hodd : Odd (n + 1) := he.add_odd odd_one
  have hs := velocityOdd_parameter_contDiff_of_odd (by omega : 3 ≤ n + 1) hodd hc
    (f := fun s => P201Specs.EvenWave.lift (f s)) hl
  exact hs.comp (contDiff_fst.prodMk
    ((P201Specs.EvenWave.inclusion n).contDiff.comp contDiff_snd))

/-- Joint smoothness of the velocity propagator for a smooth time-indexed
family of spatial data. This supplies the parameter regularity needed by Duhamel. -/
theorem velocity_parameter_contDiff {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] {c : ℝ} (hc : c ≠ 0) {f : ℝ → Space n → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × Space n =>
      velocity c (f p.1.1) p.1.2 p.2) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      have hfl : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ =>
          f p.1 (P102.Trace.Ordinary.lineIsometry p.2)) :=
        hf.comp (contDiff_fst.prodMk
          (P102.Trace.Ordinary.lineIsometry.toContinuousLinearEquiv.contDiff.comp contDiff_snd))
      have hi := contDiff_variable_interval (F := fun s y => f s
        (P102.Trace.Ordinary.lineIsometry y)) hfl
      have hx : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space 1 => x 0) :=
        P102.Trace.Ordinary.lineIsometry.symm.toContinuousLinearEquiv.contDiff
      have he (s t : ℝ) (x : Space 1) : velocity c (f s) t x =
          (2 * c)⁻¹ • ((∫ y in (0 : ℝ)..(x 0 + c * t), f s (P102.Trace.Ordinary.lineIsometry y)) -
            ∫ y in (0 : ℝ)..(x 0 - c * t), f s (P102.Trace.Ordinary.lineIsometry y)) :=
        P201.OddWave.velocityOne_eq_primitive
          (hfl.continuous.comp (continuous_const.prodMk continuous_id)) c t (x 0)
      simp_rw [he]
      exact ((hi.comp (contDiff_fst.fst.prodMk
        ((hx.comp contDiff_snd).add (contDiff_const.mul contDiff_fst.snd)))).sub
        (hi.comp (contDiff_fst.fst.prodMk
          ((hx.comp contDiff_snd).sub (contDiff_const.mul contDiff_fst.snd))))).const_smul _
    | succ k =>
      by_cases ho : Odd (k + 2)
      · have hthree : 3 ≤ k + 2 := by obtain ⟨j, hj⟩ := ho; omega
        simpa only [velocity, ite_eq_left ho] using
          velocityOdd_parameter_contDiff_of_odd hthree ho hc hf
      · simpa only [velocity, ite_eq_right ho] using
          velocityEven_parameter_contDiff (by omega : 2 ≤ k + 2) (Nat.not_odd_iff_even.mp ho) hc hf

/-- Iterated differentiation in the first variable preserves joint smoothness. -/
theorem iteratedDeriv_parameter_contDiff {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {𝕜 : Type} [RCLike 𝕜] {F : ℝ → A → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × A => iteratedDeriv j (fun t => F t p.2) p.1) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simp_rw [iteratedDeriv_succ]
    exact (P201.OddWave.contDiff_parameter_fderiv
      (F := fun t a => iteratedDeriv j (fun q => F q a) t) ih).clm_apply contDiff_const

/-- A compactly carried integral commutes with every finite time derivative. -/
theorem iteratedDeriv_integral_compact {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
    {𝕜 : Type} [RCLike 𝕜] {μ : Measure A} [IsFiniteMeasure μ]
    {K : Set A} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ, a ∈ K) {F : ℝ → A → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F)) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun q => ∫ a, F q a ∂μ) t =
      ∫ a, iteratedDeriv j (fun q => F q a) t ∂μ := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    have he : iteratedDeriv j (fun q => ∫ a, F q a ∂μ) =
        fun q => ∫ a, iteratedDeriv j (fun r => F r a) q ∂μ := funext ih
    rw [iteratedDeriv_succ, he]
    have hG := iteratedDeriv_parameter_contDiff hF j
    have hd := P201.OddWave.hasFDerivAt_integral_compact hK hμ
      (F := fun q a => iteratedDeriv j (fun r => F r a) q) hG t
    have hi : Integrable (fun a => fderiv ℝ
        (fun q => iteratedDeriv j (fun r => F r a) q) t) μ :=
      P201.OddWave.integrable_of_continuous_compact hK hμ
        ((P201.OddWave.contDiff_parameter_fderiv
          (F := fun q a => iteratedDeriv j (fun r => F r a) q) hG).continuous.comp
          (continuous_const.prodMk continuous_id))
    change (fderiv ℝ (fun q => ∫ a, iteratedDeriv j (fun r => F r a) q ∂μ) t) 1 = _
    rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
    simp only [iteratedDeriv_succ, deriv]

/-- Derivatives along an affine line are the spatial Fréchet jets evaluated
repeatedly on the line's direction. -/
theorem iteratedDeriv_affine_line {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (j : ℕ) (x θ : Space n) (r : ℝ) :
    iteratedDeriv j (fun s => h (x + s • θ)) r =
      iteratedFDeriv ℝ j h (x + r • θ) (fun _ => θ) := by
  let L : ℝ →L[ℝ] Space n := (ContinuousLinearMap.id ℝ ℝ).smulRight θ
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun y => h (x + y)) :=
    hh.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have he : (fun s => h (x + s • θ)) = (fun y => h (x + y)) ∘ L := rfl
  rw [he, L.iteratedFDeriv_comp_right ht r (by simp), iteratedFDeriv_comp_add_left]
  simp [L]

/-- All radial derivatives of a mean are actual integrals of the spatial jets. -/
theorem iteratedDeriv_sphericalMean {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {h : Space n → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (j : ℕ) (x : Space n) (r : ℝ) :
    iteratedDeriv j (P201Specs.OddWave.sphericalMean h x) r =
      (omega n)⁻¹ • ∫ θ, iteratedFDeriv ℝ j h (x + r • θ) (fun _ => θ)
        ∂P201Specs.unitSurface n := by
  change iteratedDeriv j (fun s => (omega n)⁻¹ •
    ∫ θ, h (x + s • θ) ∂P201Specs.unitSurface n) r = _
  rw [iteratedDeriv_fun_const_smul_field]
  rw [iteratedDeriv_integral_compact (isCompact_sphere (0 : Space n) 1)
    (P201.MeanValues.unitSurface_ae_mem n)
    (F := fun s θ => h (x + s • θ))
    (hh.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd)))]
  simp_rw [iteratedDeriv_affine_line hh]

/-- Equality of spatial jets on a sphere gives exactly the same-order radial
jets of the normalized spherical means. -/
theorem sphericalMean_jets_equal {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {g h : Space n → 𝕜} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {k : ℕ} {x : Space n} {r : ℝ} (hr : 0 < r)
    (hjets : SphereJetsEqual k x r g h) (j : ℕ) (hj : j ≤ k) :
    iteratedDeriv j (P201Specs.OddWave.sphericalMean g x) r =
      iteratedDeriv j (P201Specs.OddWave.sphericalMean h x) r := by
  rw [iteratedDeriv_sphericalMean hg, iteratedDeriv_sphericalMean hh]
  congr 1
  apply integral_congr_ae
  filter_upwards [P201.MeanValues.unitSurface_ae_mem n] with θ hθ
  have hθn : ‖θ‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hθ
  have hmem : x + r • θ ∈ Metric.sphere x r := by
    simp only [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, hθn, mul_one]
  rw [hjets j hj _ hmem]

/-- Multiplication by a common smooth scalar preserves equality of finite jets. -/
theorem iteratedDeriv_smul_congr {𝕜 : Type} [RCLike 𝕜] {a : ℝ → ℝ} {F G : ℝ → 𝕜}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (j : ℕ) (r : ℝ)
    (he : ∀ i ≤ j, iteratedDeriv i F r = iteratedDeriv i G r) :
    iteratedDeriv j (fun s => a s • F s) r = iteratedDeriv j (fun s => a s • G s) r := by
  have hf := iteratedDerivWithin_smul (mem_univ r) uniqueDiffOn_univ
    ((ha.of_le (show (j : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)).contDiffAt.contDiffWithinAt)
    ((hF.of_le (show (j : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)).contDiffAt.contDiffWithinAt)
  have hg := iteratedDerivWithin_smul (mem_univ r) uniqueDiffOn_univ
    ((ha.of_le (show (j : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)).contDiffAt.contDiffWithinAt)
    ((hG.of_le (show (j : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)).contDiffAt.contDiffWithinAt)
  simp only [iteratedDerivWithin_univ] at hf hg
  change iteratedDeriv j (a • F) r = iteratedDeriv j (a • G) r
  rw [hf, hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [he (j - i) (Nat.sub_le _ _)]

/-- The radial extension is a differential operator of order m: its j-th jet
uses only the input jets through order j+m. -/
theorem regularRadial_jets_congr {𝕜 : Type} [RCLike 𝕜] (m j : ℕ) {F G : ℝ → 𝕜}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (r : ℝ)
    (he : ∀ i ≤ j + m, iteratedDeriv i F r = iteratedDeriv i G r) :
    iteratedDeriv j (P201Specs.OddWave.regularRadial m F) r =
      iteratedDeriv j (P201Specs.OddWave.regularRadial m G) r := by
  induction m generalizing F G with
  | zero =>
    exact iteratedDeriv_smul_congr contDiff_id hF hG j r (by simpa using he)
  | succ m ih =>
    change iteratedDeriv j (P201Specs.OddWave.regularRadial m
        (fun s => ((2 * m + 3 : ℕ) : ℝ) • F s + s • deriv F s)) r =
      iteratedDeriv j (P201Specs.OddWave.regularRadial m
        (fun s => ((2 * m + 3 : ℕ) : ℝ) • G s + s • deriv G s)) r
    have hFd : ContDiff ℝ (⊤ : ℕ∞) (deriv F) := hF.deriv'
    have hGd : ContDiff ℝ (⊤ : ℕ∞) (deriv G) := hG.deriv'
    apply ih ((hF.const_smul _).add (contDiff_id.smul hFd))
      ((hG.const_smul _).add (contDiff_id.smul hGd))
    intro i hi
    rw [iteratedDeriv_fun_add ((hF.const_smul _).contDiffAt.of_le (by simp))
        ((contDiff_id.smul hFd).contDiffAt.of_le (by simp)),
      iteratedDeriv_fun_add ((hG.const_smul _).contDiffAt.of_le (by simp))
        ((contDiff_id.smul hGd).contDiffAt.of_le (by simp)),
      iteratedDeriv_fun_const_smul_field, iteratedDeriv_fun_const_smul_field,
      he i (by omega)]
    congr 1
    apply iteratedDeriv_smul_congr contDiff_id hFd hGd i r
    intro l hl
    rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
    exact he (l + 1) (by omega)

/-- The common velocity agrees with the smooth regular radial expression in
odd dimensions, including at t=0. -/
theorem velocity_odd_regular {𝕜 : Type} [RCLike 𝕜] (m : ℕ) {c : ℝ} (hc : c ≠ 0)
    {h : Space (2 * m + 3) → 𝕜} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (t : ℝ) (x : Space (2 * m + 3)) :
    velocity c h t x = (c * (Nat.doubleFactorial (2 * m + 1) : ℝ))⁻¹ •
      P201Specs.OddWave.regularRadial m (P201Specs.OddWave.sphericalMean h x) (c * t) := by
  have ho : Odd (2 * m + 3) := ⟨m + 1, by omega⟩
  have hs (y : Space (2 * m + 3)) :
      ContDiff ℝ (⊤ : ℕ∞) (P201Specs.OddWave.sphericalMean h y) :=
    (P201.OddWave.sphericalMean_contDiff hh).comp (contDiff_const.prodMk contDiff_id)
  simpa only [velocity, ite_eq_left ho] using
    P201.OddWave.velocityOdd_eq_regularRadial m hc h hs t x

/-- The k-th time derivative of the odd velocity uses spatial sphere jets only
through order k+m. -/
theorem velocity_odd_jets_equal {𝕜 : Type} [RCLike 𝕜] (m k : ℕ) {c : ℝ} (hc : 0 < c)
    {g h : Space (2 * m + 3) → 𝕜} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t : ℝ) (x : Space (2 * m + 3)) (ht : 0 < t)
    (hj : SphereJetsEqual (k + m) x (c * t) g h) :
    iteratedDeriv k (fun s => velocity c g s x) t =
      iteratedDeriv k (fun s => velocity c h s x) t := by
  have hFg : ContDiff ℝ (⊤ : ℕ∞) (P201Specs.OddWave.sphericalMean g x) :=
    (P201.OddWave.sphericalMean_contDiff hg).comp (contDiff_const.prodMk contDiff_id)
  have hFh : ContDiff ℝ (⊤ : ℕ∞) (P201Specs.OddWave.sphericalMean h x) :=
    (P201.OddWave.sphericalMean_contDiff hh).comp (contDiff_const.prodMk contDiff_id)
  have he := regularRadial_jets_congr m k hFg hFh (c * t)
    (fun i hi => sphericalMean_jets_equal hg hh (mul_pos hc ht) hj i hi)
  simp_rw [velocity_odd_regular m hc.ne' hg, velocity_odd_regular m hc.ne' hh,
    iteratedDeriv_fun_const_smul_field]
  have hRg := P201.OddWave.regularRadial_contDiff m hFg
  have hRh := P201.OddWave.regularRadial_contDiff m hFh
  have hcg := iteratedDeriv_comp_const_smul (hRg.of_le (show (k : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)) c
  have hch := iteratedDeriv_comp_const_smul (hRh.of_le (show (k : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)) c
  rw [hcg, hch]
  exact congrArg (fun z => (c * (Nat.doubleFactorial (2 * m + 1) : ℝ))⁻¹ • (c ^ k • z)) he

/-- The dimension-independent velocity has the full smooth wave and initial-jet
properties in every positive dimension. -/
theorem velocity_regularity : VelocityRegularityStatement := by
  intro n hn 𝕜 _ c hc h hh
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      have hl : ContDiff ℝ (⊤ : ℕ∞) (fun y => h (P102.Trace.Ordinary.lineIsometry y)) :=
        hh.comp P102.Trace.Ordinary.lineIsometry.toContinuousLinearEquiv.contDiff
      obtain ⟨hr, hp, hi⟩ := P201.OddWave.velocity_one c hc _ hl
      have hx : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space 1 => x 0) :=
        P102.Trace.Ordinary.lineIsometry.symm.toContinuousLinearEquiv.contDiff
      have hs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space 1 => velocity c h p.1 p.2) :=
        hr.comp (contDiff_fst.prodMk (hx.comp contDiff_snd))
      refine ⟨hs, ?_, ?_⟩
      · intro t x
        have hslice : ContDiff ℝ (⊤ : ℕ∞) (velocity c h t) :=
          hs.comp (contDiff_const.prodMk contDiff_id)
        have hlap := laplacian_line hslice x
        change laplacian (velocity c h t) x =
          deriv (deriv (fun y => P201Specs.OddWave.velocityOne c
            (fun z => h (P102.Trace.Ordinary.lineIsometry z)) t y)) (x 0) at hlap
        exact (hp t (x 0)).trans (congrArg (fun z => c ^ 2 • z) hlap.symm)
      · intro x
        have hxid : P102.Trace.Ordinary.lineIsometry (x 0) = x :=
          P102.Trace.Ordinary.lineIsometry.apply_symm_apply x
        simpa only [velocity, hxid] using hi (x 0)
    | succ k =>
      by_cases ho : Odd (k + 2)
      · have hthree : 3 ≤ k + 2 := by
          rcases ho with ⟨j, hj⟩
          omega
        simpa only [Function.uncurry_def, velocity, ite_eq_left ho] using P201.OddWave.velocity_odd hthree ho c hc h hh
      · simpa only [Function.uncurry_def, velocity, ite_eq_right ho] using
          P201.EvenWave.velocity_even (by omega : 2 ≤ k + 2) (Nat.not_odd_iff_even.mp ho) c hc h hh

/-- All three formulas retain their original coefficients and probability means. -/
theorem velocity_formulas : VelocityFormulasStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro 𝕜 _ c h t x
    rfl
  · intro n hn ho 𝕜 _ c h t x ht
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
    have hnk : n = k + 2 := hk.trans (Nat.add_comm _ _)
    clear hk
    subst n
    simp only [velocity, ite_eq_left ho, P201Specs.OddWave.velocityOdd, ite_eq_right ht]
  · intro n hn he 𝕜 _ c hc h t x ht
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    have hnk : n = k + 2 := hk.trans (Nat.add_comm _ _)
    clear hk
    subst n
    have hno : ¬Odd (k + 2) := Nat.not_odd_iff_even.mpr he
    simpa only [velocity, ite_eq_right hno] using
      (P201.EvenWave.velocity_even_formula (n := k + 2) (by omega) he c hc h t x).1 ht

/-- Smooth homogeneous Cauchy solution in every positive dimension. -/
theorem homogeneous_solution : HomogeneousStatement := by
  intro n hn 𝕜 _ c hc g h hg hh
  obtain ⟨hgs, hgp, hgi⟩ :=
    velocity_regularity hn c hc g hg
  obtain ⟨hhs, hhp, hhi⟩ :=
    velocity_regularity hn c hc h hh
  have hdgs := time_derivative_contDiff hgs
  have hdu := time_derivative_contDiff (u := fun t x => deriv (fun s => velocity c g s x) t) hdgs
  have hdh := time_derivative_contDiff hhs
  have hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (homogeneous c g h)) := hdgs.add hhs
  have hdeq (t : ℝ) (x : Space n) :
      deriv (fun s => homogeneous c g h s x) t =
        deriv (deriv (fun s => velocity c g s x)) t + deriv (fun s => velocity c h s x) t := by
    exact deriv_add
      ((hdgs.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
      ((hhs.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
  have hpde (t : ℝ) (x : Space n) :
      deriv (deriv (fun s => homogeneous c g h s x)) t =
        c ^ 2 • laplacian (homogeneous c g h t) x + (0 : 𝕜) := by
    have he : deriv (fun s => homogeneous c g h s x) = fun s =>
        deriv (deriv (fun s => velocity c g s x)) s + deriv (fun s => velocity c h s x) s :=
      funext fun s => hdeq s x
    have hdtg : DifferentiableAt ℝ (deriv (deriv (fun s => velocity c g s x))) t :=
      (hdu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t
    have hdth : DifferentiableAt ℝ (deriv (fun s => velocity c h s x)) t :=
      (hdh.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t
    rw [he, deriv_fun_add hdtg hdth, time_derivative_wave hgs hgp, hhp]
    have hsg : ContDiff ℝ (⊤ : ℕ∞) (fun y => deriv (fun s => velocity c g s y) t) :=
      hdgs.comp (contDiff_const.prodMk contDiff_id)
    have hsh : ContDiff ℝ (⊤ : ℕ∞) (velocity c h t) :=
      hhs.comp (contDiff_const.prodMk contDiff_id)
    change _ = c ^ 2 • laplacian (fun y => deriv (fun s => velocity c g s y) t +
      velocity c h t y) x + 0
    rw [P201.OddWave.laplacian_add_smooth hsg hsh, smul_add, add_zero]
  refine ⟨hu, hpde, ?_, classical_of_smooth hu continuous_const hpde⟩
  intro x
  constructor
  · change deriv (fun s => velocity c g s x) 0 + velocity c h 0 x = g x
    rw [(hgi x).2.1, (hhi x).1, add_zero]
  · rw [hdeq, (hgi x).2.2, (hhi x).2.1, zero_add]

/-- The Duhamel term is smooth and solves the forced equation with zero
initial displacement and velocity. The only surviving endpoint term is f(t,x). -/
theorem duhamel_solution {n : ℕ} (hn : 1 ≤ n)
    {𝕜 : Type} [RCLike 𝕜] (c : ℝ) (hc : 0 < c) (f : ℝ → Space n → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    SmoothCauchyResult c (fun _ => 0) (fun _ => 0) f (duhamel c f) := by
  have hfs (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (f s) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hreg (s : ℝ) := velocity_regularity
    hn c hc (f s) (hfs s)
  have hV := velocity_parameter_contDiff hn hc.ne' hf
  have hVs : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × Space n) × ℝ =>
      velocity c (f p.1.1) p.2 p.1.2) :=
    hV.comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
  have hVd := P201.OddWave.contDiff_radial_deriv
    (F := fun (p : ℝ × Space n) r => velocity c (f p.1) r p.2) hVs
  have hK : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × Space n) × ℝ =>
      velocity c (f p.2) (p.1.1 - p.2) p.1.2) :=
    hV.comp ((contDiff_snd.prodMk (contDiff_fst.fst.sub contDiff_snd)).prodMk contDiff_fst.snd)
  have hKd : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × Space n) × ℝ =>
      deriv (fun r => velocity c (f p.2) r p.1.2) (p.1.1 - p.2)) :=
    hVd.comp ((contDiff_snd.prodMk contDiff_fst.snd).prodMk (contDiff_fst.fst.sub contDiff_snd))
  have hI := contDiff_variable_interval
    (F := fun (p : ℝ × Space n) s => velocity c (f s) (p.1 - s) p.2) hK
  have hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (duhamel c f)) :=
    hI.comp (contDiff_id.prodMk contDiff_fst)
  have hd (t : ℝ) (x : Space n) : deriv (fun r => duhamel c f r x) t =
      ∫ s in (0 : ℝ)..t, deriv (fun r => velocity c (f s) r x) (t - s) := by
    have hx : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => velocity c (f p.2) (p.1 - p.2) x) :=
      hK.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
    change deriv (fun r => ∫ s in (0 : ℝ)..r, velocity c (f s) (r - s) x) t = _
    rw [deriv_variable_interval (F := fun r s => velocity c (f s) (r - s) x) hx]
    simp only [sub_self, ((hreg t).2.2 x).1, add_zero]
    congr 1
    funext s
    exact deriv_comp_sub_const (fun r => velocity c (f s) r x) s t
  have hpde (t : ℝ) (x : Space n) :
      deriv (deriv (fun s => duhamel c f s x)) t =
        c ^ 2 • laplacian (duhamel c f t) x + f t x := by
    have he : deriv (fun r => duhamel c f r x) = fun r =>
        ∫ s in (0 : ℝ)..r, deriv (fun q => velocity c (f s) q x) (r - s) := funext fun r => hd r x
    have hx : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ =>
        deriv (fun r => velocity c (f p.2) r x) (p.1 - p.2)) :=
      hKd.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
    rw [he, deriv_variable_interval
      (F := fun r s => deriv (fun q => velocity c (f s) q x) (r - s)) hx]
    simp only [deriv_comp_sub_const, sub_self, ((hreg t).2.2 x).2.1]
    have hsp : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space n × ℝ =>
        velocity c (f p.2) (t - p.2) p.1) :=
      hK.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    simp_rw [(hreg _).2.1]
    rw [intervalIntegral.integral_smul, ← laplacian_fixed_interval
      (F := fun y s => velocity c (f s) (t - s) y) hsp]
    rfl
  refine ⟨hu, hpde, ?_, classical_of_smooth hu hf.continuous hpde⟩
  intro x
  constructor
  · simp [duhamel]
  · rw [hd]
    simp

/-- Full smooth forced Cauchy formula, with no growth or support hypothesis. -/
theorem forced_solution : ForcedStatement := by
  intro n hn 𝕜 _ c hc g h f hg hh hf
  obtain ⟨hH, hHp, hHi, _⟩ := homogeneous_solution
    hn c hc g h hg hh
  obtain ⟨hD, hDp, hDi, _⟩ := duhamel_solution
    hn c hc f hf
  have hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (forced c g h f)) := hH.add hD
  have hdtH := time_derivative_contDiff hH
  have hdtD := time_derivative_contDiff hD
  have hd (t : ℝ) (x : Space n) : deriv (fun r => forced c g h f r x) t =
      deriv (fun r => homogeneous c g h r x) t + deriv (fun r => duhamel c f r x) t := by
    exact deriv_add
      ((hH.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
      ((hD.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
  have hpde (t : ℝ) (x : Space n) :
      deriv (deriv (fun r => forced c g h f r x)) t =
        c ^ 2 • laplacian (forced c g h f t) x + f t x := by
    have he : deriv (fun r => forced c g h f r x) = fun r =>
        deriv (fun q => homogeneous c g h q x) r + deriv (fun q => duhamel c f q x) r := funext fun r => hd r x
    have hdh : DifferentiableAt ℝ (deriv (fun r => homogeneous c g h r x)) t :=
      (hdtH.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t
    have hdd : DifferentiableAt ℝ (deriv (fun r => duhamel c f r x)) t :=
      (hdtD.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t
    rw [he, deriv_fun_add hdh hdd, hHp, hDp, add_zero]
    have hhs : ContDiff ℝ (⊤ : ℕ∞) (homogeneous c g h t) :=
      hH.comp (contDiff_const.prodMk contDiff_id)
    have hds : ContDiff ℝ (⊤ : ℕ∞) (duhamel c f t) :=
      hD.comp (contDiff_const.prodMk contDiff_id)
    change _ = c ^ 2 • laplacian (fun y => homogeneous c g h t y + duhamel c f t y) x + f t x
    rw [P201.OddWave.laplacian_add_smooth hhs hds, smul_add, add_assoc]
  refine ⟨hu, hpde, ?_, classical_of_smooth hu hf.continuous hpde⟩
  intro x
  constructor
  · change homogeneous c g h 0 x + duhamel c f 0 x = g x
    rw [(hHi x).1, (hDi x).1, add_zero]
  · rw [hd, (hHi x).2, (hDi x).2, add_zero]

/-- Huygens with the precise displacement and velocity jet orders from the
source in every odd dimension n=2m+3. -/
theorem huygens : HuygensStatement := by
  intro m 𝕜 _ c hc g₁ h₁ g₂ h₂ hg₁ hh₁ hg₂ hh₂ t x ht hgj hhj
  have hg : iteratedDeriv 1 (fun s => velocity c g₁ s x) t =
      iteratedDeriv 1 (fun s => velocity c g₂ s x) t :=
    velocity_odd_jets_equal m 1 hc hg₁ hg₂ t x ht (by simpa [Nat.add_comm] using hgj)
  have hh : iteratedDeriv 0 (fun s => velocity c h₁ s x) t =
      iteratedDeriv 0 (fun s => velocity c h₂ s x) t :=
    velocity_odd_jets_equal m 0 hc hh₁ hh₂ t x ht (by simpa using hhj)
  simpa only [iteratedDeriv_one, iteratedDeriv_zero, homogeneous] using congrArg₂ (· + ·) hg hh

/-- Uniqueness for the complete classical half-space comparison class. -/
theorem uniqueness : UniquenessStatement := classical_uniqueness

end P201.ClassicalWave
