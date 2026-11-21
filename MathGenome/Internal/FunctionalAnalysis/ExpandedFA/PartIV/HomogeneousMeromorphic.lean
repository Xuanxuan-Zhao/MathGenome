import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HomogeneousMeromorphic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The meromorphic tempered-distribution family of a smooth homogeneous kernel.
The source coordinate jets are identified with genuine Fréchet derivatives.
Taylor subtraction, logarithmic domination and rapid decay yield continuous
weakly analytic remainders with locally uniform Schwartz bounds; exact polar
integration gives the overlap identity. Gluing proves the residue and dilation
formulas, including the separate zero-dimensional case. -/

open MeasureTheory
open scoped SchwartzMap ContDiff Topology

noncomputable section

namespace ExpandedFA.PartIV.HomogeneousMeromorphic

open ExpandedFA.Fourier

variable {d : ℕ}

@[simp] theorem mem_indices (α : MultiIndex d) (m : ℕ) :
    α ∈ indices d m ↔ order α = m := by
  classical
  simp only [indices, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : α i ≤ order α :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

@[simp] theorem multiFactorial_ne_zero (α : MultiIndex d) : multiFactorial α ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _

@[simp] theorem evaluation_apply (x : Euclidean d) (φ : Schwartz ℂ d) :
    evaluation x φ = φ x := rfl

@[simp] theorem jet_apply (α : MultiIndex d) (φ : Schwartz ℂ d) :
    jet α φ = partialDerivative α φ 0 := rfl

@[simp] theorem deltaDerivative_apply (α : MultiIndex d) (φ : Schwartz ℂ d) :
    deltaDerivative α φ = (-1 : ℂ) ^ order α * jet α φ := rfl

/-- Both distributional signs cancel, giving the Taylor coefficient without
conjugation. Continuity holds because both sides are continuous linear maps. -/
theorem residue_eq_taylorCoefficient (k : Euclidean d → ℂ) (m : ℕ) :
    residue k m = taylorCoefficient k m := by
  classical
  ext φ
  simp only [residue, taylorCoefficient, sum_apply,
    smul_apply, smul_eq_mul, deltaDerivative_apply]
  apply Finset.sum_congr rfl
  intro α hα
  rw [(mem_indices α m).mp hα]
  have hs : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← mul_pow]
    simp
  calc
    (-1 : ℂ) ^ m / (multiFactorial α : ℂ) * moment k α *
        ((-1 : ℂ) ^ m * jet α φ) =
      ((-1 : ℂ) ^ m * (-1 : ℂ) ^ m) *
        (moment k α / (multiFactorial α : ℂ) * jet α φ) := by ring
    _ = _ := by rw [hs, one_mul]

theorem residue_formula :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.residueFormulaType := by
  intro d k m φ
  rw [residue_eq_taylorCoefficient]
  simp [taylorCoefficient, smul_eq_mul]

theorem test_dilation_formula :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.testDilationFormulaType := by
  intro d a ha φ x
  rfl

theorem dilation_formula :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.dilationFormulaType := by
  intro d a ha u φ
  rfl

theorem kernel_scaling :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.kernelScalingType := by
  intro d k lam z hk a ha x
  by_cases hx : x = 0
  · simp [kernelWeight, hx]
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  simp only [kernelWeight, ite_eq_right hx, ite_eq_right hax, norm_smul, Real.norm_eq_abs,
    abs_of_pos ha, Complex.ofReal_mul]
  rw [hk.2 a ha x hx, Complex.mul_cpow_ofReal_nonneg ha.le (norm_nonneg x)]
  have hp : (a : ℂ) ^ lam * (a : ℂ) ^ (z - lam) = (a : ℂ) ^ z := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
    congr 1
    ring
  calc
    (a : ℂ) ^ lam * k x * ((a : ℂ) ^ (z - lam) * (‖x‖ : ℂ) ^ (z - lam)) =
      ((a : ℂ) ^ lam * (a : ℂ) ^ (z - lam)) *
        (k x * (‖x‖ : ℂ) ^ (z - lam)) := by ring
    _ = _ := by rw [hp]

/-- The change of variables is valid for the raw integrals at every parameter.
It will apply to the initial family after its integrability is established. -/
theorem initial_dilation :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.initialDilationType := by
  intro d k lam z hk a ha φ
  let f : Euclidean d → ℂ := fun x => kernelWeight k lam z x * φ (a⁻¹ • x)
  have hchange := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Euclidean d)) f a (hR := ha.le)
  have hdim : Module.finrank ℝ (Euclidean d) = d := by simp [Euclidean]
  rw [hdim] at hchange
  have hf : (fun x => f (a • x)) = fun x =>
      (a : ℂ) ^ z * (kernelWeight k lam z x * φ x) := by
    funext x
    dsimp [f]
    rw [kernel_scaling d k lam z hk a ha x, inv_smul_smul₀ ha.ne']
    ring
  rw [hf, integral_const_mul] at hchange
  change ((a : ℂ) ^ d)⁻¹ * (∫ x, f x) = _
  convert! hchange.symm using 1
  simp only [RCLike.real_smul_eq_coe_mul, map_inv₀, map_pow, RCLike.algebraMap_eq_ofReal]
  with_reducible_and_instances rfl

theorem kernel_continuousOn_sphere (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) :
    ContinuousOn k (Metric.sphere (0 : Euclidean d) 1) := by
  apply hk.1.continuousOn.mono
  intro x hx
  exact ne_zero_of_mem_unit_sphere ⟨x, hx⟩

instance surfaceMeasure_finite (d : ℕ) : IsFiniteMeasure (surfaceMeasure d) := by
  dsimp [surfaceMeasure]
  infer_instance

/-- The spherical moments in the residue formula are genuine integrals. -/
theorem moment_integrable (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (α : MultiIndex d) :
    Integrable (fun θ : UnitSphere d => k θ * (multiMonomial α θ : ℂ))
      (surfaceMeasure d) := by
  have hc : Continuous (fun θ : UnitSphere d => k θ) :=
    (kernel_continuousOn_sphere k lam hk).comp_continuous continuous_subtype_val
      (fun θ => θ.property)
  have hm : Continuous (fun θ : UnitSphere d => (multiMonomial α θ : ℂ)) := by
    unfold multiMonomial
    fun_prop
  exact (hc.mul hm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A single angular bound works for every complex parameter. This is the
radial majorant used in the near-zero and rapid-decay estimates. -/
theorem kernel_norm_bound (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (x : Euclidean d), x ≠ 0 →
      ‖kernelWeight k lam z x‖ ≤ C * ‖x‖ ^ z.re := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euclidean d) 1).exists_bound_of_continuousOn
    (kernel_continuousOn_sphere k lam hk)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z x hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let θ : Euclidean d := ‖x‖⁻¹ • x
  have hnorm : ‖θ‖ = 1 := by
    simp [θ, norm_smul, inv_mul_cancel₀ hpos.ne']
  have hθ : θ ∈ Metric.sphere (0 : Euclidean d) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm
  have hθne : θ ≠ 0 := ne_zero_of_mem_unit_sphere ⟨θ, hθ⟩
  have hscale : ‖x‖ • θ = x := smul_inv_smul₀ hpos.ne' x
  have hangular : ‖kernelWeight k lam z θ‖ ≤ max C 0 := by
    simpa [kernelWeight, hθne, hnorm] using (hC θ hθ).trans (le_max_left C 0)
  calc
    ‖kernelWeight k lam z x‖ = ‖kernelWeight k lam z (‖x‖ • θ)‖ := by rw [hscale]
    _ = ‖(‖x‖ : ℂ) ^ z‖ * ‖kernelWeight k lam z θ‖ := by
      rw [kernel_scaling d k lam z hk ‖x‖ hpos θ, norm_mul]
    _ = ‖x‖ ^ z.re * ‖kernelWeight k lam z θ‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    _ ≤ ‖x‖ ^ z.re * max C 0 :=
      mul_le_mul_of_nonneg_left hangular (Real.rpow_nonneg (norm_nonneg x) _)
    _ = _ := by ring

theorem kernel_measurable (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) : Measurable (kernelWeight k lam z) := by
  have hp : ContinuousOn (fun x : Euclidean d => (‖x‖ : ℂ) ^ (z - lam)) {0}ᶜ := by
    intro x hx
    have hx' : x ≠ 0 := hx
    apply ContinuousAt.continuousWithinAt
    apply (continuousAt_cpow_const (b := z - lam) ?_).comp
      (Complex.continuous_ofReal.comp continuous_norm).continuousAt
    exact Or.inl (by simpa using norm_pos_iff.mpr hx')
  apply measurable_of_continuousOn_compl_singleton 0
  apply (hk.1.continuousOn.mul hp).congr
  intro x hx
  simp [kernelWeight, show x ≠ 0 from hx]

/-- Rapid Schwartz decay controls the exterior integral at every parameter. -/
theorem outer_integrable (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ := by
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  obtain ⟨n, hn⟩ := exists_nat_ge z.re
  have hmeas : AEStronglyMeasurable (outerIntegrand k lam z φ)
      (volume : Measure (Euclidean d)) :=
    ((kernel_measurable k lam z hk).mul φ.continuous.measurable).aestronglyMeasurable
  apply Integrable.mono' ((φ.integrable_pow_mul volume n).const_mul C).integrableOn hmeas.restrict
  filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
  have hnorm : 1 < ‖x‖ := by
    simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hxne : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hnorm)
  change ‖kernelWeight k lam z x * φ x‖ ≤ C * (‖x‖ ^ n * ‖φ x‖)
  rw [norm_mul]
  calc
    ‖kernelWeight k lam z x‖ * ‖φ x‖ ≤ (C * ‖x‖ ^ z.re) * ‖φ x‖ :=
      mul_le_mul_of_nonneg_right (hbound z x hxne) (norm_nonneg _)
    _ ≤ C * (‖x‖ ^ n * ‖φ x‖) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hC
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hnorm.le hn

/-- Near zero the half-plane condition is exactly the power-integrability
threshold. The radius two also covers the closed unit ball used for subtraction. -/
theorem initial_integrable_positive_dimension (hd : 0 < d) (k : Euclidean d → ℂ)
    (lam z : ℂ) (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0)
    (φ : Schwartz ℂ d) : Integrable (fun x => kernelWeight k lam z x * φ x) := by
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  have hmeas : AEStronglyMeasurable (fun x => kernelWeight k lam z x * φ x)
      (volume : Measure (Euclidean d)) :=
    ((kernel_measurable k lam z hk).mul φ.continuous.measurable).aestronglyMeasurable
  have hdim : Module.finrank ℝ (Euclidean d) = d := by simp [Euclidean]
  have hα : -z.re < Module.finrank ℝ (Euclidean d) := by
    rw [hdim]
    dsimp [halfPlane] at hz
    simp only [Nat.cast_zero, sub_zero] at hz
    linarith
  have hnear : IntegrableOn (fun x => kernelWeight k lam z x * φ x)
      (Metric.ball 0 2) := by
    apply integrableOn_ball_of_norm_le_rpow (by rw [hdim]; omega) hα
      (C := C * SchwartzMap.seminorm ℂ 0 0 φ) (r := 2) ?_ hmeas
    apply Filter.Eventually.of_forall
    intro x
    rw [neg_neg, norm_mul]
    by_cases hx : x = 0
    · rw [hx]
      simp only [kernelWeight, ite_true, norm_zero, zero_mul]
      positivity
    calc
      ‖kernelWeight k lam z x‖ * ‖φ x‖ ≤
          (C * ‖x‖ ^ z.re) * SchwartzMap.seminorm ℂ 0 0 φ := by
        exact mul_le_mul (hbound z x hx) (SchwartzMap.norm_le_seminorm ℂ φ x)
          (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg x) _))
      _ = _ := by ring
  have hin : IntegrableOn (fun x => kernelWeight k lam z x * φ x)
      (Metric.closedBall 0 1) :=
    hnear.mono_set (Metric.closedBall_subset_ball (by norm_num))
  have htotal := hin.union (outer_integrable k lam z hk φ)
  simpa only [Set.union_compl_self, integrableOn_univ] using htotal


@[simp] theorem pole_re (d m : ℕ) : (pole d m).re = -(d : ℝ) - (m : ℝ) := by
  simp [pole]

theorem pole_injective (d : ℕ) : Function.Injective (pole d) := by
  intro m n h
  have h' := congrArg Complex.re h
  simp only [pole_re] at h'
  have : (m : ℝ) = (n : ℝ) := by linarith
  exact_mod_cast this

theorem halfPlane_mono {N M : ℕ} (h : N ≤ M) : halfPlane d N ⊆ halfPlane d M := by
  intro z hz
  have h' : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
  dsimp [halfPlane] at *
  linarith

theorem halfPlane_zero_subset_regularSet : halfPlane d 0 ⊆ regularSet d := by
  intro z hz m heq
  have hre := congrArg Complex.re heq
  simp only [pole_re] at hre
  dsimp [halfPlane] at hz
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  norm_num at hz
  linarith

theorem mem_some_halfPlane (z : ℂ) : ∃ N : ℕ, z ∈ halfPlane d N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-(d : ℝ) - z.re)
  exact ⟨N, by dsimp [halfPlane]; linarith⟩

theorem schwartzBound_nonneg (M : ℕ) (φ : Schwartz ℂ d) : 0 ≤ schwartzBound M φ := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

theorem locallyUniformBound_zero (U : Set ℂ) :
    LocallyUniformBound (fun _ => (0 : Tempered ℂ d)) U := by
  intro z hz
  exact ⟨Set.univ, Filter.univ_mem, 0, le_rfl, 0, by simp⟩

/-- The finite polar sum is analytic away from its explicitly listed poles. -/
theorem analyticAt_polarPart (k : Euclidean d → ℂ) (N : ℕ) (z : ℂ)
    (hz : ∀ m < N, z ≠ pole d m) (φ : Schwartz ℂ d) :
    AnalyticAt ℂ (fun w => polarPart k N w φ) z := by
  simp only [polarPart, sum_apply, smul_apply, smul_eq_mul]
  apply Finset.analyticAt_fun_sum
  intro m hm
  exact ((analyticAt_id.sub analyticAt_const).inv
    (sub_ne_zero.mpr (hz m (Finset.mem_range.mp hm)))).mul analyticAt_const

theorem analyticOnNhd_polarPart (k : Euclidean d → ℂ) (N : ℕ) (φ : Schwartz ℂ d) :
    AnalyticOnNhd ℂ (fun w => polarPart k N w φ) (regularSet d) := by
  intro z hz
  exact analyticAt_polarPart k N z (fun m _ => hz m) φ

@[simp] theorem surfaceMeasure_zero_dimension : surfaceMeasure 0 = 0 := by
  apply (Measure.toSphere_eq_zero_iff_finrank (volume : Measure (Euclidean 0))).mpr
  simp [Euclidean]

@[simp] theorem moment_zero_dimension (k : Euclidean 0 → ℂ) (α : MultiIndex 0) :
    moment k α = 0 := by
  simp [moment]

@[simp] theorem taylorCoefficient_zero_dimension (k : Euclidean 0 → ℂ) (m : ℕ) :
    taylorCoefficient k m = 0 := by
  ext φ
  simp [taylorCoefficient, smul_eq_mul]

@[simp] theorem residue_zero_dimension (k : Euclidean 0 → ℂ) (m : ℕ) :
    residue k m = 0 := by
  rw [residue_eq_taylorCoefficient]
  exact taylorCoefficient_zero_dimension k m

@[simp] theorem kernelWeight_zero_dimension (k : Euclidean 0 → ℂ) (lam z : ℂ)
    (x : Euclidean 0) : kernelWeight k lam z x = 0 := by
  have hx : x = 0 := Subsingleton.elim _ _
  simp [kernelWeight, hx]

/-- The empty punctured space gives the zero family, including all analytic
and Schwartz-continuity clauses. No positive-dimension hypothesis is imposed. -/
theorem zero_dimension :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.zeroDimensionType := by
  intro k lam
  refine ⟨fun _ => 0, fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz φ
    simp [initialPairing]
  · intro N z hz φ
    simp [IntegrableOn, innerIntegrand, outerIntegrand, taylorRemainder]
  · intro N
    exact ⟨fun φ z hz => analyticAt_const, locallyUniformBound_zero _⟩
  · intro N z hz hr
    ext φ
    simp [polarPart, smul_eq_mul]
  · exact fun φ z hz => analyticAt_const
  · intro m
    refine ⟨Set.univ, fun _ => 0, Filter.univ_mem,
      fun φ z hz => analyticAt_const, locallyUniformBound_zero _, ?_⟩
    intro z hz hne
    ext φ
    simp [smul_eq_mul]
  · intro a ha z hz
    ext φ
    simp [dilation, smul_eq_mul]

theorem initial_integrable :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.initialIntegrableType := by
  intro d k lam z hk hz φ
  cases d with
  | zero => simp
  | succ n => exact initial_integrable_positive_dimension (Nat.succ_pos _) k lam z hk hz φ



/-! Taylor estimates and weak parameter analyticity. -/

open ExpandedFA.Fourier
variable {d : ℕ}

/-- The parameter derivative adds precisely one real logarithmic weight. -/
theorem kernelWeight_hasDerivAt (k : Euclidean d → ℂ) (lam z : ℂ)
    (x : Euclidean d) :
    HasDerivAt (fun w : ℂ => kernelWeight k lam w x)
      (kernelWeight k lam z x * (Real.log ‖x‖ : ℂ)) z := by
  by_cases hx : x = 0
  · simp only [hx, kernelWeight, ite_true, norm_zero, Real.log_zero, Complex.ofReal_zero,
      mul_zero]
    exact hasDerivAt_const z 0
  have hnorm : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have h := (((hasDerivAt_id z).sub_const lam).const_cpow (Or.inl hnorm)).const_mul (k x)
  convert! h using 1 <;>
    simp only [kernelWeight, ite_eq_right hx, Complex.ofReal_log (norm_nonneg x),
      mul_one, mul_assoc, id_eq]

theorem outerIntegrand_hasDerivAt (k : Euclidean d → ℂ) (lam z : ℂ)
    (φ : Schwartz ℂ d) (x : Euclidean d) :
    HasDerivAt (fun w : ℂ => outerIntegrand k lam w φ x)
      (outerIntegrand k lam z φ x * (Real.log ‖x‖ : ℂ)) z := by
  convert (kernelWeight_hasDerivAt k lam z x).mul_const (φ x) using 1 <;>
    simp only [outerIntegrand] <;> ring

theorem outer_derivative_bound (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (z₀ : ℂ) (φ : Schwartz ℂ d) :
    ∃ B : Euclidean d → ℝ,
      IntegrableOn B (Metric.closedBall 0 1)ᶜ ∧
      ∀ x ∈ (Metric.closedBall (0 : Euclidean d) 1)ᶜ,
        ∀ z ∈ Metric.ball z₀ 1,
          ‖outerIntegrand k lam z φ x * (Real.log ‖x‖ : ℂ)‖ ≤ B x := by
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  obtain ⟨n, hn⟩ := exists_nat_ge (z₀.re + 1)
  refine ⟨fun x => C * (‖x‖ ^ (n + 1) * ‖φ x‖),
    ((φ.integrable_pow_mul volume (n + 1)).const_mul C).integrableOn, ?_⟩
  intro x hx z hz
  have hnorm : 1 < ‖x‖ := by
    simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hxne : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hnorm)
  have hrez : z.re ≤ (n : ℝ) := by
    have hdist : ‖z - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hreal : z.re - z₀.re ≤ ‖z - z₀‖ := by
      simpa only [Complex.sub_re] using Complex.re_le_norm (z - z₀)
    linarith
  have hp : ‖x‖ ^ z.re ≤ ‖x‖ ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hnorm.le hrez
  have hl : ‖(Real.log ‖x‖ : ℂ)‖ ≤ ‖x‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hnorm.le)]
    exact Real.log_le_self (norm_nonneg _)
  simp only [norm_mul, outerIntegrand]
  calc
    ‖kernelWeight k lam z x‖ * ‖φ x‖ * ‖(Real.log ‖x‖ : ℂ)‖ ≤
        (C * ‖x‖ ^ n) * ‖φ x‖ * ‖x‖ := by
      gcongr
      exact (hbound z x hxne).trans (mul_le_mul_of_nonneg_left hp hC)
    _ = _ := by rw [pow_succ]; ring

/-- Rapid decay permits complex parameter differentiation of the exterior
integral on a neighborhood of every parameter. -/
theorem outer_pairing_differentiable (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    Differentiable ℂ (fun z : ℂ =>
      ∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ, outerIntegrand k lam z φ x) := by
  intro z₀
  obtain ⟨B, hB, hbound⟩ := outer_derivative_bound k lam hk z₀ φ
  let μ : Measure (Euclidean d) := volume.restrict (Metric.closedBall 0 1)ᶜ
  have hF (z : ℂ) : AEStronglyMeasurable (outerIntegrand k lam z φ) μ :=
    (((kernel_measurable k lam z hk).mul φ.continuous.measurable).aestronglyMeasurable).restrict
  have hlog : AEStronglyMeasurable (fun x : Euclidean d => (Real.log ‖x‖ : ℂ)) μ :=
    (Complex.continuous_ofReal.measurable.comp
      (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable
  have hB' : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball z₀ 1,
      ‖outerIntegrand k lam z φ x * (Real.log ‖x‖ : ℂ)‖ ≤ B x := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
    exact hbound x hx
  have hdiff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun w : ℂ => outerIntegrand k lam w φ x)
        (outerIntegrand k lam z φ x * (Real.log ‖x‖ : ℂ)) z :=
    Filter.Eventually.of_forall (fun x z _ => outerIntegrand_hasDerivAt k lam z φ x)
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ zero_lt_one) (Filter.Eventually.of_forall hF)
    (outer_integrable k lam z₀ hk φ) ((hF z₀).mul hlog) hB' hB hdiff
  exact hd.differentiableAt

/-- The exterior part of the continuation is entire for every Schwartz test. -/
theorem outer_pairing_analytic (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ, outerIntegrand k lam z φ x)
        Set.univ :=
  fun z _ => (outer_pairing_differentiable k lam hk φ).analyticAt z


open ExpandedFA.Fourier
variable {d : ℕ}

theorem order_eq_zero_iff (α : MultiIndex d) : order α = 0 ↔ α = 0 := by
  classical
  constructor
  · intro h
    ext i
    have hi : α i ≤ order α :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [h] using hi
  · rintro rfl
    simp [order]

@[simp] theorem indices_zero (d : ℕ) : indices d 0 = {0} := by
  classical
  ext α
  simp [mem_indices, order_eq_zero_iff]

@[simp] theorem derivativeWord_zero : derivativeWord (0 : MultiIndex d) = [] := by
  simp [derivativeWord]

@[simp] theorem taylorPolynomial_zero (φ : Schwartz ℂ d) (x : Euclidean d) :
    taylorPolynomial 0 φ x = 0 := by simp [taylorPolynomial]

@[simp] theorem taylorPolynomial_one (φ : Schwartz ℂ d) (x : Euclidean d) :
    taylorPolynomial 1 φ x = φ 0 := by
  simp [taylorPolynomial, multiFactorial, multiMonomial, jet_apply,
    partialDerivative, wordDerivative]

/-- The first subtraction estimate uses the actual first Schwartz seminorm. -/
theorem taylorRemainder_one_bound (φ : Schwartz ℂ d) (x : Euclidean d) :
    ‖φ x - taylorPolynomial 1 φ x‖ ≤ SchwartzMap.seminorm ℂ 0 1 φ * ‖x‖ := by
  rw [taylorPolynomial_one]
  have hb : ∀ y : Euclidean d, ‖fderiv ℝ φ y‖ ≤ SchwartzMap.seminorm ℂ 0 1 φ := by
    intro y
    simpa [norm_iteratedFDeriv_one] using
      SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ 1 y
  simpa using (convex_univ : Convex ℝ (Set.univ : Set (Euclidean d))).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => φ.differentiableAt) (fun y _ => hb y) (Set.mem_univ 0) (Set.mem_univ x)

theorem wordDerivative_eq_iteratedLineDerivOp (w : List (Fin d)) (φ : Schwartz ℂ d) :
    wordDerivative w φ =
      LineDeriv.iteratedLineDerivOp (fun i : Fin w.length => basisVector (w.get i)) φ := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [wordDerivative, ContinuousLinearMap.comp_apply, ih,
      LineDeriv.iteratedLineDerivOp_succ_left]
    rfl

/-- An explicit bridge from the fixed coordinate-word definition to the genuine
Fréchet derivative; no formal jet certificate is assumed. -/
theorem wordDerivative_apply_eq_iteratedFDeriv (w : List (Fin d))
    (φ : Schwartz ℂ d) (x : Euclidean d) :
    wordDerivative w φ x =
      iteratedFDeriv ℝ w.length φ x (fun i : Fin w.length => basisVector (w.get i)) := by
  rw [wordDerivative_eq_iteratedLineDerivOp,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]

theorem derivativeWord_length (α : MultiIndex d) : (derivativeWord α).length = order α := by
  simp [derivativeWord, List.length_flatten, List.sum_ofFn, order]

theorem norm_wordDerivative_le_seminorm (w : List (Fin d))
    (φ : Schwartz ℂ d) (x : Euclidean d) :
    ‖wordDerivative w φ x‖ ≤ SchwartzMap.seminorm ℂ 0 w.length φ := by
  rw [wordDerivative_apply_eq_iteratedFDeriv]
  calc
    _ ≤ ‖iteratedFDeriv ℝ w.length φ x‖ *
        ∏ i : Fin w.length, ‖basisVector (w.get i)‖ :=
      (iteratedFDeriv ℝ w.length φ x).le_opNorm _
    _ = ‖iteratedFDeriv ℝ w.length φ x‖ := by simp [basisVector, PiLp.norm_single]
    _ ≤ _ := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ w.length x

theorem norm_partialDerivative_le_seminorm (α : MultiIndex d)
    (φ : Schwartz ℂ d) (x : Euclidean d) :
    ‖partialDerivative α φ x‖ ≤ SchwartzMap.seminorm ℂ 0 (order α) φ := by
  simpa [partialDerivative, derivativeWord_length] using
    norm_wordDerivative_le_seminorm (derivativeWord α) φ x

@[simp] theorem norm_jet_le_seminorm (α : MultiIndex d) (φ : Schwartz ℂ d) :
    ‖jet α φ‖ ≤ SchwartzMap.seminorm ℂ 0 (order α) φ :=
  norm_partialDerivative_le_seminorm α φ 0

/-- Polynomial subtraction preserves measurability at every order. -/
theorem continuous_taylorPolynomial (N : ℕ) (φ : Schwartz ℂ d) :
    Continuous (taylorPolynomial N φ) := by
  unfold taylorPolynomial multiMonomial
  fun_prop

theorem inner_measurable (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ) (z : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    Measurable (innerIntegrand k lam N z φ) :=
  (kernel_measurable k lam z hk).mul
    (φ.continuous.sub (continuous_taylorPolynomial N φ)).measurable

/-- First-order Taylor cancellation genuinely enlarges the local integrability
half-plane by one, including dimension zero. -/
theorem inner_integrable_one (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 1) (φ : Schwartz ℂ d) :
    IntegrableOn (innerIntegrand k lam 1 z φ) (Metric.closedBall 0 1) := by
  by_cases hd : d = 0
  · subst d
    simp [IntegrableOn, innerIntegrand]
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  have hdim : Module.finrank ℝ (Euclidean d) = d := by simp [Euclidean]
  have hα : -(z.re + 1) < Module.finrank ℝ (Euclidean d) := by
    rw [hdim]
    dsimp [halfPlane] at hz
    norm_num at hz
    linarith
  have hmeas : AEStronglyMeasurable (innerIntegrand k lam 1 z φ)
      (volume : Measure (Euclidean d)) := (inner_measurable k lam 1 z hk φ).aestronglyMeasurable
  have hnear : IntegrableOn (innerIntegrand k lam 1 z φ) (Metric.ball 0 2) := by
    apply integrableOn_ball_of_norm_le_rpow (by rw [hdim]; omega) hα
      (C := C * SchwartzMap.seminorm ℂ 0 1 φ) (r := 2) ?_ hmeas
    apply Filter.Eventually.of_forall
    intro x
    rw [neg_neg]
    change ‖kernelWeight k lam z x * (φ x - taylorPolynomial 1 φ x)‖ ≤ _
    by_cases hx : x = 0
    · rw [hx]
      simp only [kernelWeight, ite_true, zero_mul, norm_zero]
      positivity
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    calc
      _ ≤ (C * ‖x‖ ^ z.re) * (SchwartzMap.seminorm ℂ 0 1 φ * ‖x‖) := by
        rw [norm_mul]
        exact mul_le_mul (hbound z x hx) (taylorRemainder_one_bound φ x)
          (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg x) _))
      _ = (C * SchwartzMap.seminorm ℂ 0 1 φ) * ‖x‖ ^ (z.re + 1) := by
        rw [Real.rpow_add hxpos, Real.rpow_one]
        ring
  exact hnear.mono_set (Metric.closedBall_subset_ball (by norm_num))

/-- The Taylor estimate at every order for the genuine multilinear Taylor
polynomial. Converting this polynomial to the fixed multi-index polynomial is
a separate combinatorial identity. -/
theorem frechetTaylorRemainder_bound (n : ℕ) (φ : Schwartz ℂ d) (x : Euclidean d) :
    ‖φ x - ∑ m ∈ Finset.range (n + 1),
        (m.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ m φ 0 (fun _ => x)‖ ≤
      (n.factorial : ℝ)⁻¹ * SchwartzMap.seminorm ℂ 0 (n + 1) φ * ‖x‖ ^ (n + 1) := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := (φ : Euclidean d → ℂ)) (x := 0) (y := x) (n := n)
    (fun t ht => (φ.smooth (n + 1)).contDiffAt)
  simp only [zero_add] at ht
  rw [← sub_eq_iff_eq_add'] at ht
  rw [ht, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  have hb : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n •
      iteratedFDeriv ℝ (n + 1) φ (t • x) (fun _ => x)‖ ≤
      SchwartzMap.seminorm ℂ 0 (n + 1) φ * ‖x‖ ^ (n + 1) := by
    suffices hpoint : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖(1 - t) ^ n • iteratedFDeriv ℝ (n + 1) φ (t • x) (fun _ => x)‖ ≤
          SchwartzMap.seminorm ℂ 0 (n + 1) φ * ‖x‖ ^ (n + 1) by
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self (by simpa using ht)
    have hfac : |1 - t| ^ n ≤ 1 := by
      apply pow_le_one₀ (abs_nonneg _)
      rw [abs_le]
      constructor <;> linarith [ht'.1, ht'.2]
    calc
      _ = |1 - t| ^ n * ‖iteratedFDeriv ℝ (n + 1) φ (t • x) (fun _ => x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_pow]
      _ ≤ 1 * (SchwartzMap.seminorm ℂ 0 (n + 1) φ * ‖x‖ ^ (n + 1)) := by
        apply mul_le_mul hfac
        · calc
            _ ≤ ‖iteratedFDeriv ℝ (n + 1) φ (t • x)‖ * ∏ _ : Fin (n + 1), ‖x‖ :=
              (iteratedFDeriv ℝ (n + 1) φ (t • x)).le_opNorm _
            _ ≤ _ := by
              simp only [Finset.prod_const, Finset.card_fin]
              gcongr
              exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ (n + 1) (t • x)
        · exact norm_nonneg _
        · positivity
      _ = _ := one_mul _
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)


/-- The integrable radial majorant used after Taylor cancellation. -/
theorem radial_power_integrable (hd : 0 < d) (q : ℝ) (hq : -(d : ℝ) < q) :
    IntegrableOn (fun x : Euclidean d => ‖x‖ ^ q) (Metric.closedBall 0 1) := by
  have hdim : Module.finrank ℝ (Euclidean d) = d := by simp [Euclidean]
  have hmeas : Measurable (fun x : Euclidean d => ‖x‖ ^ q) := measurable_norm.pow_const q
  have hnear : IntegrableOn (fun x : Euclidean d => ‖x‖ ^ q) (Metric.ball 0 2) := by
    apply integrableOn_ball_of_norm_le_rpow (by rw [hdim]; omega)
      (α := -q) (C := 1) (by rw [hdim]; linarith) ?_ hmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) q),
        neg_neg, one_mul, le_refl]
  exact hnear.mono_set (Metric.closedBall_subset_ball (by norm_num))

/-- An explicit Taylor estimate, once proved at order N, gives the full larger
integrability half-plane. The estimate here is a hypothesis of this helper only. -/
theorem inner_integrable_of_taylor_bound (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ x : Euclidean d,
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * ‖x‖ ^ N)
    (z : ℂ) (hz : z ∈ halfPlane d N) :
    IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1) := by
  by_cases hd : d = 0
  · subst d
    simp [IntegrableOn, innerIntegrand]
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  have hq : -(d : ℝ) < z.re + N := by
    dsimp [halfPlane] at hz
    linarith
  apply Integrable.mono' (((radial_power_integrable (Nat.pos_of_ne_zero hd)
    (z.re + N) hq).const_mul (C * A)))
    (inner_measurable k lam N z hk φ).aestronglyMeasurable.restrict
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x = 0
  · subst x
    simp only [innerIntegrand, kernelWeight, ite_true, zero_mul, norm_zero]
    positivity
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  change ‖kernelWeight k lam z x * (φ x - taylorPolynomial N φ x)‖ ≤ _
  calc
    _ ≤ (C * ‖x‖ ^ z.re) * (A * ‖x‖ ^ N) := by
      rw [norm_mul]
      exact mul_le_mul (hbound z x hx) (hTaylor x) (norm_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg x) _))
    _ = (C * A) * ‖x‖ ^ (z.re + N) := by
      rw [Real.rpow_add hxpos, Real.rpow_natCast]
      ring

theorem innerIntegrand_hasDerivAt (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ)
    (z : ℂ) (φ : Schwartz ℂ d) (x : Euclidean d) :
    HasDerivAt (fun w : ℂ => innerIntegrand k lam N w φ x)
      (innerIntegrand k lam N z φ x * (Real.log ‖x‖ : ℂ)) z := by
  convert (kernelWeight_hasDerivAt k lam z x).mul_const
      (φ x - taylorPolynomial N φ x) using 1 <;>
    simp only [innerIntegrand] <;> ring


/-- Reserving a third of the distance to the boundary absorbs the logarithm
introduced by differentiating with respect to the complex parameter. -/
theorem inner_derivative_bound_of_taylor_bound (hd : 0 < d)
    (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ) (hk : SmoothHomogeneous k lam)
    (φ : Schwartz ℂ d) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ x : Euclidean d,
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * ‖x‖ ^ N)
    (z₀ : ℂ) (hz₀ : z₀ ∈ halfPlane d N) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : Euclidean d → ℝ,
      IntegrableOn B (Metric.closedBall 0 1) ∧
      ∀ x ∈ Metric.closedBall (0 : Euclidean d) 1,
        ∀ z ∈ Metric.ball z₀ ε,
          ‖innerIntegrand k lam N z φ x * (Real.log ‖x‖ : ℂ)‖ ≤ B x := by
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  let ε : ℝ := (z₀.re + (d : ℝ) + (N : ℝ)) / 3
  have hε : 0 < ε := by dsimp [halfPlane] at hz₀; dsimp [ε]; linarith
  have hq : -(d : ℝ) < z₀.re + N - 2 * ε := by
    dsimp [halfPlane] at hz₀; dsimp [ε]; linarith
  refine ⟨ε, hε, fun x => (C * A / ε) * ‖x‖ ^ (z₀.re + N - 2 * ε),
    (radial_power_integrable hd _ hq).const_mul _, ?_⟩
  intro x hx z hz
  by_cases hxne : x = 0
  · subst x
    simp only [innerIntegrand, kernelWeight, ite_true, zero_mul, norm_zero]
    positivity
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  have hnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hrez : z₀.re - ε ≤ z.re := by
    have hdist : ‖z - z₀‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hreal : z₀.re - z.re ≤ ‖z - z₀‖ := by
      simpa only [Complex.sub_re, norm_sub_rev] using Complex.re_le_norm (z₀ - z)
    linarith
  have hp : ‖x‖ ^ (z.re + N) ≤ ‖x‖ ^ (z₀.re + N - ε) :=
    Real.rpow_le_rpow_of_exponent_ge hxpos hnorm (by linarith)
  have hl : ‖(Real.log ‖x‖ : ℂ)‖ ≤ ‖x‖ ^ (-ε) / ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos (norm_nonneg x) hnorm)]
    have hh := Real.neg_rpow_div_le_log (norm_nonneg x) hε
    rw [neg_div] at hh
    linarith only [hh]
  calc
    ‖innerIntegrand k lam N z φ x * (Real.log ‖x‖ : ℂ)‖ ≤
        ((C * A) * ‖x‖ ^ (z.re + N)) * (‖x‖ ^ (-ε) / ε) := by
      simp only [norm_mul, innerIntegrand]
      apply mul_le_mul _ hl (norm_nonneg _) (by positivity)
      calc
        _ ≤ (C * ‖x‖ ^ z.re) * (A * ‖x‖ ^ N) := by
          exact mul_le_mul (hbound z x hxne) (hTaylor x) (norm_nonneg _)
            (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg x) _))
        _ = _ := by rw [Real.rpow_add hxpos, Real.rpow_natCast]; ring
    _ ≤ ((C * A) * ‖x‖ ^ (z₀.re + N - ε)) * (‖x‖ ^ (-ε) / ε) := by
      gcongr
    _ = (C * A / ε) * ‖x‖ ^ (z₀.re + N - 2 * ε) := by
      rw [show z₀.re + (N : ℝ) - 2 * ε = (z₀.re + N - ε) + -ε by ring,
        Real.rpow_add hxpos]
      ring


/-- A proved Taylor growth bound justifies weak holomorphy by dominated complex
parameter differentiation. All logarithmic domination is established above. -/
theorem inner_pairing_analytic_of_taylor_bound (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ x : Euclidean d,
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * ‖x‖ ^ N) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∫ x in Metric.closedBall (0 : Euclidean d) 1, innerIntegrand k lam N z φ x)
        (halfPlane d N) := by
  by_cases hd : d = 0
  · subst d
    intro z hz
    simpa only [innerIntegrand, kernelWeight_zero_dimension, zero_mul, integral_zero] using
      (analyticAt_const (𝕜 := ℂ) (v := (0 : ℂ)) (x := z))
  apply DifferentiableOn.analyticOnNhd ?_
    (isOpen_lt continuous_const Complex.continuous_re)
  intro z₀ hz₀
  obtain ⟨ε, hε, B, hB, hbound⟩ := inner_derivative_bound_of_taylor_bound
    (Nat.pos_of_ne_zero hd) k lam N hk φ A hA hTaylor z₀ hz₀
  let μ : Measure (Euclidean d) := volume.restrict (Metric.closedBall 0 1)
  have hF (z : ℂ) : AEStronglyMeasurable (innerIntegrand k lam N z φ) μ :=
    (inner_measurable k lam N z hk φ).aestronglyMeasurable.restrict
  have hlog : AEStronglyMeasurable (fun x : Euclidean d => (Real.log ‖x‖ : ℂ)) μ :=
    (Complex.continuous_ofReal.measurable.comp
      (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable
  have hB' : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball z₀ ε,
      ‖innerIntegrand k lam N z φ x * (Real.log ‖x‖ : ℂ)‖ ≤ B x := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact hbound x hx
  have hdiff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball z₀ ε,
      HasDerivAt (fun w : ℂ => innerIntegrand k lam N w φ x)
        (innerIntegrand k lam N z φ x * (Real.log ‖x‖ : ℂ)) z :=
    Filter.Eventually.of_forall (fun x z _ => innerIntegrand_hasDerivAt k lam N z φ x)
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ hε) (Filter.Eventually.of_forall hF)
    (inner_integrable_of_taylor_bound k lam N hk φ A hA hTaylor z₀ hz₀)
    ((hF z₀).mul hlog) hB' hB hdiff
  exact hderiv.differentiableAt.differentiableWithinAt

theorem taylorRemainder_analytic_of_taylor_bound (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ x : Euclidean d,
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * ‖x‖ ^ N) :
    AnalyticOnNhd ℂ (fun z => taylorRemainder k lam N z φ) (halfPlane d N) := by
  intro z hz
  exact (inner_pairing_analytic_of_taylor_bound k lam N hk φ A hA hTaylor z hz).add
    (outer_pairing_analytic k lam hk φ z (Set.mem_univ z))

/-- Before any subtraction, the integral is weakly holomorphic in its initial
half-plane. -/
theorem taylorRemainder_zero_analytic (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    AnalyticOnNhd ℂ (fun z => taylorRemainder k lam 0 z φ) (halfPlane d 0) := by
  apply taylorRemainder_analytic_of_taylor_bound k lam 0 hk φ
    (SchwartzMap.seminorm ℂ 0 0 φ) (apply_nonneg _ _)
  intro x
  simpa using SchwartzMap.norm_le_seminorm ℂ φ x

/-- Actual first-order cancellation gives weak holomorphy on Re z > -d-1. -/
theorem taylorRemainder_one_analytic (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    AnalyticOnNhd ℂ (fun z => taylorRemainder k lam 1 z φ) (halfPlane d 1) := by
  apply taylorRemainder_analytic_of_taylor_bound k lam 1 hk φ
    (SchwartzMap.seminorm ℂ 0 1 φ) (apply_nonneg _ _)
  intro x
  simpa only [pow_one] using taylorRemainder_one_bound φ x



/-! Continuous initial distributions with local Schwartz bounds. -/

open ExpandedFA.Fourier
variable {d : ℕ}

lemma kernel_integrableOn_unitBall (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0) :
    IntegrableOn (kernelWeight k lam z) (Metric.closedBall 0 1) := by
  cases d with
  | zero =>
    have hzero : kernelWeight k lam z = 0 := by ext x; simp
    rw [hzero]
    exact integrable_zero _ _ _
  | succ d =>
    obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
    have hdim : Module.finrank ℝ (Euclidean (d+1)) = d+1 := by simp [Euclidean]
    have hα : -z.re < Module.finrank ℝ (Euclidean (d+1)) := by
      rw [hdim]
      dsimp [halfPlane] at hz
      simp only [Nat.cast_zero, sub_zero] at hz
      linarith
    have hnear : IntegrableOn (kernelWeight k lam z) (Metric.ball 0 2) := by
      apply integrableOn_ball_of_norm_le_rpow (by rw [hdim]; omega) hα
        (C := C) (r := 2) ?_ (kernel_measurable k lam z hk).aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro x
      rw [neg_neg]
      by_cases hx : x = 0
      · simp only [hx, kernelWeight, ite_true, norm_zero]
        positivity
      exact hbound z x hx
    exact hnear.mono_set (Metric.closedBall_subset_ball (by norm_num))

lemma initialPairing_add (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0)
    (φ ψ : Schwartz ℂ d) :
    initialPairing k lam z (φ + ψ) = initialPairing k lam z φ + initialPairing k lam z ψ := by
  simp only [initialPairing, add_apply, mul_add]
  exact integral_add (initial_integrable d k lam z hk hz φ)
    (initial_integrable d k lam z hk hz ψ)

lemma initialPairing_smul (k : Euclidean d → ℂ) (lam z : ℂ) (a : ℂ)
    (φ : Schwartz ℂ d) : initialPairing k lam z (a • φ) = a * initialPairing k lam z φ := by
  simp only [initialPairing, smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (kernelWeight k lam z _) a]
  exact integral_const_mul a _

lemma kernel_norm_mono_on_unitBall (k : Euclidean d → ℂ) (lam z w : ℂ)
    (hzw : w.re ≤ z.re) (x : Euclidean d) (hx : ‖x‖ ≤ 1) :
    ‖kernelWeight k lam z x‖ ≤ ‖kernelWeight k lam w x‖ := by
  by_cases hx0 : x = 0
  · simp [kernelWeight, hx0]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  simp only [kernelWeight, ite_eq_right hx0, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.sub_re]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_ge hp hx (by linarith)

lemma initialPairing_bound_sup_strip (k : Euclidean d → ℂ) (lam β : ℂ)
    (hk : SmoothHomogeneous k lam) (hβ : β ∈ halfPlane d 0) (n : ℕ) :
    ∃ (M : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ z : ℂ, β.re ≤ z.re → z.re ≤ n → ∀ φ : Schwartz ℂ d,
      ‖initialPairing k lam z φ‖ ≤
        A * (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ := by
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  let μ : Measure (Euclidean d) := volume
  let p : ℕ := μ.integrablePower
  let D : ℝ := 2 ^ p * ∫ x : Euclidean d, (1 + ‖x‖) ^ (-(p : ℝ))
  let A : ℝ := ∫ x in Metric.closedBall (0 : Euclidean d) 1, ‖kernelWeight k lam β x‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨n + p, A + C * D * 2, by positivity, ?_⟩
  intro z hlo hn φ
  have hz : z ∈ halfPlane d 0 := by
    dsimp [halfPlane] at hβ ⊢
    exact hβ.trans_le hlo
  let S := (Finset.Iic (n+p, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ
  have hS0 : SchwartzMap.seminorm ℂ 0 0 φ ≤ S := by
    exact Seminorm.le_def.mp (Finset.le_sup (b := (0,0)) (s := Finset.Iic (n+p, 0)) (f := schwartzSeminormFamily ℂ (Euclidean d) ℂ)
      (Finset.mem_Iic.mpr (by exact ⟨Nat.zero_le _, le_rfl⟩))) φ
  have hSn : SchwartzMap.seminorm ℂ (n+p) 0 φ ≤ S := by
    exact Seminorm.le_def.mp (Finset.le_sup (b := (n+p, 0)) (s := Finset.Iic (n+p, 0)) (f := schwartzSeminormFamily ℂ (Euclidean d) ℂ)
      (Finset.mem_Iic.mpr le_rfl)) φ
  have hker := kernel_integrableOn_unitBall k lam β hk hβ
  have hin := (initial_integrable d k lam z hk hz φ).integrableOn
      (s := Metric.closedBall 0 1)
  have hnear : ‖∫ x in Metric.closedBall (0 : Euclidean d) 1,
      kernelWeight k lam z x * φ x‖ ≤ A * S := by
    calc
      _ ≤ ∫ x in Metric.closedBall (0 : Euclidean d) 1,
          ‖kernelWeight k lam z x * φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in Metric.closedBall (0 : Euclidean d) 1,
          ‖kernelWeight k lam β x‖ * S := by
        apply integral_mono_ae hin.norm (hker.norm.mul_const S)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        change ‖kernelWeight k lam z x * φ x‖ ≤ ‖kernelWeight k lam β x‖ * S
        rw [norm_mul]
        apply mul_le_mul (kernel_norm_mono_on_unitBall k lam z β hlo x (by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hx))
          ((SchwartzMap.norm_le_seminorm ℂ φ x).trans hS0) (norm_nonneg _) (norm_nonneg _)
      _ = A * S := by rw [integral_mul_const]
  have htail := outer_integrable k lam z hk φ
  have houter : ‖∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ,
      kernelWeight k lam z x * φ x‖ ≤ C * D * (2 * S) := by
    calc
      _ ≤ ∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ,
          ‖kernelWeight k lam z x * φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ,
          C * (‖x‖ ^ n * ‖φ x‖) := by
        apply integral_mono_ae htail.norm
          (((φ.integrable_pow_mul volume n).const_mul C).integrableOn)
        filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
        have hnorm : 1 < ‖x‖ := by
          simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
        have hxne : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hnorm)
        change ‖kernelWeight k lam z x * φ x‖ ≤ C * (‖x‖ ^ n * ‖φ x‖)
        rw [norm_mul]
        calc
          ‖kernelWeight k lam z x‖ * ‖φ x‖ ≤ (C * ‖x‖ ^ z.re) * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right (hbound z x hxne) (norm_nonneg _)
          _ ≤ C * (‖x‖ ^ n * ‖φ x‖) := by
            rw [← mul_assoc]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le hnorm.le hn
      _ ≤ ∫ x : Euclidean d, C * (‖x‖ ^ n * ‖φ x‖) := by
        apply integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun x => by positivity)
          ((φ.integrable_pow_mul volume n).const_mul C)
      _ = C * ∫ x : Euclidean d, ‖x‖ ^ n * ‖φ x‖ := integral_const_mul _ _
      _ ≤ C * (D * (SchwartzMap.seminorm ℂ 0 0 φ +
          SchwartzMap.seminorm ℂ (n+p) 0 φ)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa [D, p, μ] using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ volume φ n 0
      _ ≤ C * D * (2 * S) := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        linarith
  have hsplit := integral_add_compl (s := Metric.closedBall (0 : Euclidean d) 1)
    (f := fun x => kernelWeight k lam z x * φ x)
    measurableSet_closedBall (initial_integrable d k lam z hk hz φ)
  unfold initialPairing
  rw [← hsplit]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ A * S + C * D * (2 * S) := add_le_add hnear houter
    _ = (A + C * D * 2) * S := by ring

lemma initialPairing_bound_sup (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0) :
    ∃ (M : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ φ : Schwartz ℂ d,
      ‖initialPairing k lam z φ‖ ≤
        A * (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ := by
  obtain ⟨n, hn⟩ := exists_nat_ge z.re
  obtain ⟨M, A, hA, h⟩ := initialPairing_bound_sup_strip k lam z hk hz n
  exact ⟨M, A, hA, h z le_rfl hn⟩

def initialTempered (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0) : Tempered ℂ d :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (initialPairing k lam z)
    (initialPairing_add k lam z hk hz)
    (fun a φ => initialPairing_smul k lam z a φ)
    (by
      obtain ⟨M, C, hC, h⟩ := initialPairing_bound_sup k lam z hk hz
      exact ⟨Finset.Iic (M, 0), C, hC, h⟩)

@[simp] theorem initialTempered_apply (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0) (φ : Schwartz ℂ d) :
    initialTempered k lam z hk hz φ = initialPairing k lam z φ := rfl

lemma seminorm_le_schwartzBound {M i j : ℕ} (hi : i ≤ M) (hj : j ≤ M)
    (φ : Schwartz ℂ d) : SchwartzMap.seminorm ℂ i j φ ≤ schwartzBound M φ := by
  unfold schwartzBound
  have hj' := Finset.single_le_sum (f := fun j => SchwartzMap.seminorm ℂ i j φ)
    (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hi' := Finset.single_le_sum
    (f := fun i => ∑ j ∈ Finset.range (M+1), SchwartzMap.seminorm ℂ i j φ)
    (fun i _ => Finset.sum_nonneg fun j _ => apply_nonneg _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact hj'.trans hi'

lemma sup_seminorm_le_schwartzBound (M : ℕ) (φ : Schwartz ℂ d) :
    (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ ≤
      schwartzBound M φ := by
  rw [Seminorm.finset_sup_apply]
  change _ ≤ ((⟨schwartzBound M φ, schwartzBound_nonneg M φ⟩ : NNReal) : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro ij hij
  have hij' := Finset.mem_Iic.mp hij
  exact seminorm_le_schwartzBound hij'.1 (hij'.2.trans (Nat.zero_le M)) φ

lemma initialPairing_bound (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∃ M : ℕ, ∀ φ : Schwartz ℂ d,
      ‖initialPairing k lam z φ‖ ≤ C * schwartzBound M φ := by
  obtain ⟨M, C, hC, h⟩ := initialPairing_bound_sup k lam z hk hz
  exact ⟨C, hC, M, fun φ => (h φ).trans
    (mul_le_mul_of_nonneg_left (sup_seminorm_le_schwartzBound M φ) hC)⟩

def initialFamily (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (z : ℂ) : Tempered ℂ d := by
  classical
  exact if hz : z ∈ halfPlane d 0 then initialTempered k lam z hk hz else 0

@[simp] lemma initialFamily_apply_of_mem (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0) (φ : Schwartz ℂ d) :
    initialFamily k lam hk z φ = initialPairing k lam z φ := by
  simp only [initialFamily, dite_eq_left hz, initialTempered_apply]

lemma initialFamily_locallyUniformBound (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) :
    LocallyUniformBound (initialFamily k lam hk) (halfPlane d 0) := by
  intro z₀ hz₀
  let b : ℝ := (z₀.re - (d : ℝ)) / 2
  let β : ℂ := b
  have hb : -(d : ℝ) < b := by
    dsimp [halfPlane] at hz₀
    norm_num at hz₀
    dsimp [b]
    linarith
  have hbz₀ : β.re < z₀.re := by
    change b < z₀.re
    dsimp [halfPlane] at hz₀
    norm_num at hz₀
    dsimp [b]
    linarith
  have hβ : β ∈ halfPlane d 0 := by
    simpa [halfPlane, β] using hb
  obtain ⟨n, hn⟩ := exists_nat_gt z₀.re
  obtain ⟨M, C, hC, h⟩ := initialPairing_bound_sup_strip k lam β hk hβ n
  let V : Set ℂ := {z | β.re < z.re ∧ z.re < (n : ℝ)}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV : V ∈ nhds z₀ := hVopen.mem_nhds ⟨hbz₀, hn⟩
  refine ⟨V, hV, C, hC, M, ?_⟩
  intro z hz φ
  have hz' : z ∈ halfPlane d 0 := by
    simpa only [halfPlane, Set.mem_ofPred_eq, Nat.cast_zero, sub_zero] using
      hb.trans hz.1
  rw [initialFamily_apply_of_mem k lam z hk hz']
  exact (h z hz.1.le hz.2.le φ).trans
    (mul_le_mul_of_nonneg_left (sup_seminorm_le_schwartzBound M φ) hC)



/-! Meromorphic assembly from explicit analytic remainder data. -/

open ExpandedFA.Fourier
variable {d : ℕ}

theorem tempered_has_schwartzBound (u : Tempered ℂ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ,
      ∀ φ : Schwartz ℂ d, ‖u φ‖ ≤ C * schwartzBound M φ := by
  classical
  let q : Seminorm ℂ (Schwartz ℂ d) := (normSeminorm ℂ ℂ).comp u.toLinearMap
  have hq : Continuous q := u.continuous.norm
  obtain ⟨s, C, hC, hs⟩ := Seminorm.bound_sum_of_continuous
    (schwartz_withSeminorms ℂ (Euclidean d) ℂ) q hq
  let M : ℕ := s.sup fun p => max p.1 p.2
  refine ⟨C, C.coe_nonneg, M, ?_⟩
  intro φ
  have hsub : s ⊆ (Finset.range (M+1)) ×ˢ (Finset.range (M+1)) := by
    intro p hp
    have hm : max p.1 p.2 ≤ M := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
    simpa only [Finset.mem_product, Finset.mem_range] using
      And.intro (Nat.lt_succ_of_le ((le_max_left _ _).trans hm))
        (Nat.lt_succ_of_le ((le_max_right _ _).trans hm))
  have hsum : (∑ p ∈ s, schwartzSeminormFamily ℂ (Euclidean d) ℂ p φ) ≤
      schwartzBound M φ := by
    calc
      _ ≤ ∑ p ∈ (Finset.range (M+1)) ×ˢ (Finset.range (M+1)),
          schwartzSeminormFamily ℂ (Euclidean d) ℂ p φ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => apply_nonneg _ _)
      _ = _ := by simp [schwartzBound, Finset.sum_product, schwartzSeminormFamily]
  calc
    ‖u φ‖ = q φ := rfl
    _ ≤ (C • ∑ p ∈ s, schwartzSeminormFamily ℂ (Euclidean d) ℂ p) φ := hs φ
    _ = (C : ℝ) * (∑ p ∈ s, schwartzSeminormFamily ℂ (Euclidean d) ℂ p φ) := by
      simp [NNReal.smul_def]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum C.coe_nonneg


theorem schwartzBound_mono {M N : ℕ} (h : M ≤ N) (φ : Schwartz ℂ d) :
    schwartzBound M φ ≤ schwartzBound N φ := by
  apply le_trans (Finset.sum_le_sum fun i hi =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ h))
      (fun _ _ _ => apply_nonneg _ _))
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ h))
    (fun _ _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _)

theorem locallyUniformBound_const (u : Tempered ℂ d) (U : Set ℂ) :
    LocallyUniformBound (fun _ => u) U := by
  obtain ⟨C, hC, M, hbound⟩ := tempered_has_schwartzBound u
  intro z hz
  exact ⟨Set.univ, Filter.univ_mem, C, hC, M, fun _ _ => hbound⟩

theorem LocallyUniformBound.add {E F : ℂ → Tempered ℂ d} {U : Set ℂ}
    (hE : LocallyUniformBound E U) (hF : LocallyUniformBound F U) :
    LocallyUniformBound (fun z => E z + F z) U := by
  intro z hz
  obtain ⟨V, hV, C, hC, M, hE⟩ := hE z hz
  obtain ⟨W, hW, D, hD, N, hF⟩ := hF z hz
  refine ⟨V ∩ W, Filter.inter_mem hV hW, C + D, add_nonneg hC hD, max M N, ?_⟩
  intro w hw φ
  calc
    ‖(E w + F w) φ‖ ≤ ‖E w φ‖ + ‖F w φ‖ := norm_add_le _ _
    _ ≤ C * schwartzBound M φ + D * schwartzBound N φ := add_le_add (hE w hw.1 φ) (hF w hw.2 φ)
    _ ≤ C * schwartzBound (max M N) φ + D * schwartzBound (max M N) φ :=
      add_le_add (mul_le_mul_of_nonneg_left (schwartzBound_mono (le_max_left _ _) φ) hC)
        (mul_le_mul_of_nonneg_left (schwartzBound_mono (le_max_right _ _) φ) hD)
    _ = _ := by ring

theorem LocallyUniformBound.mono {E : ℂ → Tempered ℂ d} {U V : Set ℂ}
    (hE : LocallyUniformBound E U) (hVU : V ⊆ U) : LocallyUniformBound E V :=
  fun z hz => hE z (hVU hz)

theorem LocallyUniformBound.smul {E : ℂ → Tempered ℂ d} {U : Set ℂ}
    (hE : LocallyUniformBound E U) (f : ℂ → ℂ)
    (hf : ∀ z ∈ U, ContinuousAt f z) :
    LocallyUniformBound (fun z => f z • E z) U := by
  intro z hz
  obtain ⟨V, hV, C, hC, M, hE⟩ := hE z hz
  have hfbound : {w | ‖f w‖ < ‖f z‖ + 1} ∈ nhds z :=
    (hf z hz).norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨V ∩ {w | ‖f w‖ < ‖f z‖ + 1}, Filter.inter_mem hV hfbound,
    (‖f z‖ + 1) * C, mul_nonneg (by positivity) hC, M, ?_⟩
  intro w hw φ
  change ‖f w * E w φ‖ ≤ _
  rw [norm_mul]
  calc
    ‖f w‖ * ‖E w φ‖ ≤ (‖f z‖+1) * (C * schwartzBound M φ) :=
      mul_le_mul hw.2.le (hE w hw.1 φ) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- An exact next-order Taylor subtraction identity suffices to glue all charts.
The analytic/integral estimates used to obtain the maps are separate obligations. -/
theorem glue_from_remainder_overlap (k : Euclidean d → ℂ)
    (E : ℕ → ℂ → Tempered ℂ d)
    (hoverlap : ∀ N z, z ∈ halfPlane d N →
      E N z = (z - pole d N)⁻¹ • taylorCoefficient k N + E (N+1) z) :
    ∃ I : ℂ → Tempered ℂ d,
      ∀ N z, z ∈ halfPlane d N → I z = polarPart k N z + E N z := by
  classical
  let F := fun N z => polarPart k N z + E N z
  have hnext (N : ℕ) (z : ℂ) (hz : z ∈ halfPlane d N) : F N z = F (N+1) z := by
    simp only [F, polarPart, Finset.sum_range_succ, hoverlap N z hz]
    abel
  have hle {N M : ℕ} (h : N ≤ M) (z : ℂ) (hz : z ∈ halfPlane d N) : F N z = F M z := by
    induction M, h using Nat.le_induction with
    | base => rfl
    | succ M hNM ih =>
      exact ih.trans (hnext M z (halfPlane_mono hNM hz))
  let I : ℂ → Tempered ℂ d := fun z => F (Nat.find (mem_some_halfPlane (d := d) z)) z
  refine ⟨I, ?_⟩
  intro N z hz
  dsimp [I]
  rcases le_total (Nat.find (mem_some_halfPlane (d := d) z)) N with h | h
  · exact hle h z (Nat.find_spec (mem_some_halfPlane (d := d) z))
  · exact (hle h z hz).symm

theorem isOpen_halfPlane (d N : ℕ) : IsOpen (halfPlane d N) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem analytic_glued_family (k : Euclidean d → ℂ)
    (I : ℂ → Tempered ℂ d) (E : ℕ → ℂ → Tempered ℂ d)
    (hformula : ∀ N z, z ∈ halfPlane d N →
      I z = polarPart k N z + E N z)
    (hE : ∀ N φ, AnalyticOnNhd ℂ (fun z => E N z φ) (halfPlane d N)) :
    ∀ φ, AnalyticOnNhd ℂ (fun z => I z φ) (regularSet d) := by
  intro φ z hz
  obtain ⟨N, hNz⟩ := mem_some_halfPlane (d := d) z
  have hF := (analyticAt_polarPart k N z (fun m hm => hz m) φ).add (hE N φ z hNz)
  apply hF.congr
  filter_upwards [(isOpen_halfPlane d N).mem_nhds hNz] with w hw
  exact congrArg (fun u : Tempered ℂ d => u φ) (hformula N w hw).symm


theorem LocallyUniformBound.sum {ι : Type*} (s : Finset ι)
    {E : ι → ℂ → Tempered ℂ d} {U : Set ℂ}
    (hE : ∀ i ∈ s, LocallyUniformBound (E i) U) :
    LocallyUniformBound (fun z => ∑ i ∈ s, E i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locallyUniformBound_zero (d := d) U
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hE i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hE j (Finset.mem_insert_of_mem hj)))

theorem locallyUniformBound_polarPart (k : Euclidean d → ℂ) (N : ℕ) (U : Set ℂ)
    (hU : ∀ z ∈ U, ∀ m < N, z ≠ pole d m) :
    LocallyUniformBound (polarPart k N) U := by
  apply LocallyUniformBound.sum (Finset.range N)
  intro m hm
  apply (locallyUniformBound_const (taylorCoefficient k m) U).smul
  intro z hz
  exact ((continuousAt_id.sub continuousAt_const).inv₀
    (sub_ne_zero.mpr (hU z hz m (Finset.mem_range.mp hm))))

/-- The Laurent chart and its locally uniform Schwartz bound follow from the
analytic remainder estimates and the exact overlapping chart formula. -/
theorem laurent_glued_family (k : Euclidean d → ℂ)
    (I : ℂ → Tempered ℂ d) (E : ℕ → ℂ → Tempered ℂ d)
    (hformula : ∀ N z, z ∈ halfPlane d N →
      I z = polarPart k N z + E N z)
    (hE : ∀ N, (∀ φ, AnalyticOnNhd ℂ (fun z => E N z φ) (halfPlane d N)) ∧
      LocallyUniformBound (E N) (halfPlane d N)) :
    ∀ m, ∃ (V : Set ℂ) (H : ℂ → Tempered ℂ d),
      V ∈ nhds (pole d m) ∧
      (∀ φ, AnalyticOnNhd ℂ (fun z => H z φ) V) ∧
      LocallyUniformBound H V ∧
      ∀ z ∈ V, z ≠ pole d m → I z = (z - pole d m)⁻¹ • residue k m + H z := by
  intro m
  let V : Set ℂ := {z | z ∈ halfPlane d (m+1) ∧ ∀ j < m, z ≠ pole d j}
  let H : ℂ → Tempered ℂ d := fun z => polarPart k m z + E (m+1) z
  have hp : pole d m ∈ halfPlane d (m+1) := by
    dsimp [halfPlane]
    rw [pole_re]
    push_cast
    linarith
  have hV : V ∈ nhds (pole d m) := by
    apply Filter.inter_mem ((isOpen_halfPlane d (m+1)).mem_nhds hp)
    change ∀ᶠ z in nhds (pole d m), ∀ j < m, z ≠ pole d j
    simp only [← Finset.mem_range]
    apply (Finset.eventually_all (Finset.range m)).mpr
    intro j hj
    apply eventually_ne_nhds
    intro h
    have : m = j := pole_injective d h
    exact (ne_of_gt (Finset.mem_range.mp hj)) this
  refine ⟨V, H, hV, ?_, ?_, ?_⟩
  · intro φ z hz
    exact (analyticAt_polarPart k m z hz.2 φ).add ((hE (m+1)).1 φ z hz.1)
  · exact (locallyUniformBound_polarPart k m V (fun _ hz => hz.2)).add
      ((hE (m+1)).2.mono (fun _ hz => hz.1))
  · intro z hz hne
    rw [hformula (m+1) z hz.1, residue_eq_taylorCoefficient]
    dsimp [H]
    simp only [polarPart, Finset.sum_range_succ]
    abel



theorem isConnected_regularSet (d : ℕ) : IsConnected (regularSet d) := by
  have hset : regularSet d = (Set.range (pole d))ᶜ := by
    ext z
    simp [regularSet, Set.mem_range, eq_comm]
  rw [hset]
  exact (Set.countable_range (pole d)).isConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex])

theorem analyticAt_const_cpow (a : ℂ) (ha : a ≠ 0) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => a ^ w) z := by
  simp only [Complex.cpow_def_of_ne_zero ha]
  exact (analyticAt_const.mul analyticAt_id).cexp

/-- Weak analytic continuation of the initial change-of-variables identity.
Connectedness follows directly from the countability of the complex pole set. -/
theorem dilation_glued_family (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (I : ℂ → Tempered ℂ d)
    (hinit : ∀ z ∈ halfPlane d 0, ∀ φ : Schwartz ℂ d,
      I z φ = initialPairing k lam z φ)
    (hI : ∀ φ, AnalyticOnNhd ℂ (fun z => I z φ) (regularSet d)) :
    ∀ (a : ℝ) (ha : 0 < a) z, z ∈ regularSet d →
      dilation a ha (I z) = (a : ℂ) ^ z • I z := by
  intro a ha z hz
  ext φ
  have hf : AnalyticOnNhd ℂ
      (fun w => ((a : ℂ) ^ d)⁻¹ * I w (testDilation a ha φ)) (regularSet d) := by
    intro w hw
    exact analyticAt_const.mul (hI (testDilation a ha φ) w hw)
  have hg : AnalyticOnNhd ℂ (fun w => (a : ℂ) ^ w * I w φ) (regularSet d) := by
    intro w hw
    exact (analyticAt_const_cpow a (Complex.ofReal_ne_zero.mpr ha.ne') w).mul (hI φ w hw)
  have hhalf : (1 : ℂ) ∈ halfPlane d 0 := by
    dsimp [halfPlane]
    simp only [Nat.cast_zero, sub_zero]
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hevent : (fun w => ((a : ℂ) ^ d)⁻¹ * I w (testDilation a ha φ)) =ᶠ[nhds 1]
      (fun w => (a : ℂ) ^ w * I w φ) := by
    filter_upwards [(isOpen_halfPlane d 0).mem_nhds hhalf] with w hw
    rw [hinit w hw _, hinit w hw _]
    exact initial_dilation d k lam w hk a ha φ
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (isConnected_regularSet d).isPreconnected
    (halfPlane_zero_subset_regularSet hhalf) hevent hz



theorem taylorRemainder_zero (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (hz : z ∈ halfPlane d 0) (φ : Schwartz ℂ d) :
    taylorRemainder k lam 0 z φ = initialPairing k lam z φ := by
  simpa only [taylorRemainder, initialPairing, innerIntegrand, outerIntegrand,
    taylorPolynomial_zero, sub_zero] using
    integral_add_compl measurableSet_closedBall (initial_integrable d k lam z hk hz φ)

/-- This assembly theorem isolates exactly the still-required analytic Taylor
integral construction. It is conditional on those three displayed obligations. -/
theorem construction_of_remainder_data (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (E : ℕ → ℂ → Tempered ℂ d)
    (hintegral : ∀ N z, z ∈ halfPlane d N → ∀ φ : Schwartz ℂ d,
      IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1) ∧
      IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ ∧
      E N z φ = taylorRemainder k lam N z φ)
    (hanalytic : ∀ N, (∀ φ : Schwartz ℂ d,
      AnalyticOnNhd ℂ (fun z => E N z φ) (halfPlane d N)) ∧
      LocallyUniformBound (E N) (halfPlane d N))
    (hoverlap : ∀ N z, z ∈ halfPlane d N →
      E N z = (z - pole d N)⁻¹ • taylorCoefficient k N + E (N+1) z) :
    Construction k lam := by
  obtain ⟨I, hformula⟩ := glue_from_remainder_overlap k E hoverlap
  have hinit : ∀ z ∈ halfPlane d 0, ∀ φ : Schwartz ℂ d,
      I z φ = initialPairing k lam z φ := by
    intro z hz φ
    calc
      I z φ = E 0 z φ := by rw [hformula 0 z hz]; simp [polarPart]
      _ = taylorRemainder k lam 0 z φ := (hintegral 0 z hz φ).2.2
      _ = initialPairing k lam z φ := taylorRemainder_zero k lam z hk hz φ
  have hIanalytic := analytic_glued_family k I E hformula (fun N => (hanalytic N).1)
  refine ⟨I, E, ?_, hintegral, hanalytic, ?_, hIanalytic,
    laurent_glued_family k I E hformula hanalytic, dilation_glued_family k lam hk I hinit hIanalytic⟩
  · intro z hz φ
    exact ⟨initial_integrable d k lam z hk hz φ, hinit z hz φ⟩
  · intro N z hz _
    exact hformula N z hz



open ExpandedFA.Fourier
variable {d : ℕ}

theorem initialPairing_analytic (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    AnalyticOnNhd ℂ (fun z => initialPairing k lam z φ) (halfPlane d 0) := by
  intro z hz
  apply (taylorRemainder_zero_analytic k lam hk φ z hz).congr
  filter_upwards [(isOpen_halfPlane d 0).mem_nhds hz] with w hw
  exact taylorRemainder_zero k lam w hk hw φ

theorem initialFamily_analytic (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (φ : Schwartz ℂ d) :
    AnalyticOnNhd ℂ (fun z => initialFamily k lam hk z φ) (halfPlane d 0) := by
  intro z hz
  apply (initialPairing_analytic k lam hk φ z hz).congr
  filter_upwards [(isOpen_halfPlane d 0).mem_nhds hz] with w hw
  exact (initialFamily_apply_of_mem k lam w hk hw φ).symm

/-- The initial half-plane family is constructed in the genuine continuous
Schwartz dual, with weak analyticity and finite locally uniform seminorm bounds. -/
theorem construct_initial_family (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) :
    ∃ J : ℂ → Tempered ℂ d,
      (∀ z ∈ halfPlane d 0, ∀ φ : Schwartz ℂ d,
        Integrable (fun x => kernelWeight k lam z x * φ x) ∧
          J z φ = initialPairing k lam z φ) ∧
      (∀ φ : Schwartz ℂ d, AnalyticOnNhd ℂ (fun z => J z φ) (halfPlane d 0)) ∧
      LocallyUniformBound J (halfPlane d 0) := by
  refine ⟨initialFamily k lam hk, ?_, initialFamily_analytic k lam hk,
    initialFamily_locallyUniformBound k lam hk⟩
  intro z hz φ
  exact ⟨initial_integrable d k lam z hk hz φ, initialFamily_apply_of_mem k lam z hk hz φ⟩





open ExpandedFA.Fourier
variable {d : ℕ}

theorem lineDerivOpCLM_commute (v w : Euclidean d) :
    Commute (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) v)
      (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) w) := by
  ext φ x
  change fderiv ℝ (fun y => fderiv ℝ φ y w) x v =
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w
  have hdf : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((φ.smooth 2).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) |>.differentiableAt
  rw [fderiv_clm_apply hdf (differentiableAt_const w),
      fderiv_clm_apply hdf (differentiableAt_const v)]
  simpa using ((φ.smooth 2).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq v w
theorem euclidean_coordinate_expansion (x : Euclidean d) :
    ∑ i, x i • basisVector i = x := by
  ext j
  simp [basisVector, Pi.single_apply]

theorem lineDerivOpCLM_eq_sum (x : Euclidean d) :
    LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) x =
      ∑ i : Fin d, (x i : ℂ) • LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) := by
  ext φ y
  simp only [sum_apply, smul_apply]
  change fderiv ℝ φ y x = ∑ i : Fin d, (x i : ℂ) • fderiv ℝ φ y (basisVector i)
  conv_lhs => rw [← euclidean_coordinate_expansion x, map_sum]
  simp [RCLike.real_smul_eq_coe_mul]

theorem wordDerivative_eq_prod (w : List (Fin d)) :
    wordDerivative w =
      (w.map (fun i => LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i))).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [wordDerivative, List.map_cons, List.prod_cons, ih]
    rfl

theorem partialDerivative_eq_prod (α : MultiIndex d) :
    partialDerivative α =
      (List.ofFn (fun i : Fin d =>
        (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)) ^ α i)).prod := by
  rw [partialDerivative, wordDerivative_eq_prod]
  simp [derivativeWord, List.map_flatten, List.map_ofFn, List.prod_flatten, Function.comp_def]

theorem directional_power_apply (n : ℕ) (v : Euclidean d) (φ : Schwartz ℂ d) (y : Euclidean d) :
    (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) v ^ n) φ y =
      iteratedFDeriv ℝ n φ y (fun _ => v) := by
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp]
  exact congrArg (fun f : Schwartz ℂ d => f y)
    (congrFun (FunLike.coe_pow_eq_iterate (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) v) n) φ)

private theorem list_prod_scalar_operators
    (l : List (ℂ × (Schwartz ℂ d →L[ℂ] Schwartz ℂ d))) :
    (l.map (fun p => p.1 • p.2)).prod =
      (l.map Prod.fst).prod • (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih, smul_smul, mul_comm]

private theorem noncommProd_eq_ofFn
    (f : Fin d → (Schwartz ℂ d →L[ℂ] Schwartz ℂ d))
    (hf : ((Finset.univ : Finset (Fin d)) : Set (Fin d)).Pairwise (Function.onFun Commute f)) :
    Finset.univ.noncommProd f hf = (List.ofFn f).prod := by
  have h := Finset.noncommProd_toFinset (List.finRange d) f
    (by simpa using hf) (List.nodup_finRange d)
  simpa [← List.ofFn_eq_map] using h

theorem scaled_derivative_prod (α : MultiIndex d) (x : Euclidean d) :
    (List.ofFn fun i : Fin d =>
      ((x i : ℂ) • LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i)) ^ α i).prod =
      (multiMonomial α x : ℂ) • partialDerivative α := by
  simp_rw [smul_pow]
  rw [partialDerivative_eq_prod]
  have h := list_prod_scalar_operators (d := d) (List.ofFn fun i : Fin d =>
    (((x i : ℂ) ^ α i), LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) ^ α i))
  simpa [List.map_ofFn, Function.comp_def, List.prod_ofFn, multiMonomial, map_prod, map_pow] using h

theorem indices_eq_piAntidiag (n : ℕ) : indices d n = Finset.univ.piAntidiag n := by
  classical
  ext α
  simp [mem_indices, Finset.mem_piAntidiag, order]

theorem directional_power_eq_multinomial (n : ℕ) (x : Euclidean d) :
    LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) x ^ n =
      ∑ α ∈ indices d n, (Nat.multinomial Finset.univ α : ℂ) •
        ((multiMonomial α x : ℂ) • partialDerivative α) := by
  classical
  rw [lineDerivOpCLM_eq_sum]
  have hcomm : ((Finset.univ : Finset (Fin d)) : Set (Fin d)).Pairwise
      (Function.onFun Commute (fun i : Fin d =>
        (x i : ℂ) • LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i))) := by
    intro i hi j hj hij
    exact ((lineDerivOpCLM_commute (basisVector i) (basisVector j)).smul_left
      (x i : ℂ)).smul_right (x j : ℂ)
  rw [Finset.sum_pow_eq_sum_piAntidiag_of_commute Finset.univ _ hcomm n,
    ← indices_eq_piAntidiag]
  apply Finset.sum_congr rfl
  intro α hα
  rw [noncommProd_eq_ofFn, scaled_derivative_prod]
  simp only [Algebra.smul_def, map_natCast]

theorem multinomial_div_factorial (α : MultiIndex d) :
    ((order α).factorial : ℂ)⁻¹ * (Nat.multinomial Finset.univ α : ℂ) =
      (multiFactorial α : ℂ)⁻¹ := by
  have h := Nat.multinomial_spec Finset.univ α
  change multiFactorial α * Nat.multinomial Finset.univ α = (order α).factorial at h
  have hc : (multiFactorial α : ℂ) * (Nat.multinomial Finset.univ α : ℂ) =
      ((order α).factorial : ℂ) := by exact_mod_cast h
  have hf : (multiFactorial α : ℂ) ≠ 0 := by exact_mod_cast multiFactorial_ne_zero α
  have hn : ((order α).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (order α)
  apply (mul_left_inj' hf).mp
  rw [inv_mul_cancel₀ hf]
  calc
    _ = ((order α).factorial : ℂ)⁻¹ *
        ((multiFactorial α : ℂ) * (Nat.multinomial Finset.univ α : ℂ)) := by ring
    _ = 1 := by rw [hc, inv_mul_cancel₀ hn]

theorem taylorPolynomial_eq_frechet (N : ℕ) (φ : Schwartz ℂ d) (x : Euclidean d) :
    taylorPolynomial N φ x = ∑ m ∈ Finset.range N,
      (m.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ m φ 0 (fun _ => x) := by
  classical
  unfold taylorPolynomial
  apply Finset.sum_congr rfl
  intro m hm
  rw [← directional_power_apply, directional_power_eq_multinomial]
  simp only [sum_apply, smul_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul,
    map_inv₀, map_natCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have ha := (mem_indices α m).mp hα
  have hc := multinomial_div_factorial α
  rw [ha] at hc
  change jet α φ / (multiFactorial α : ℂ) * (multiMonomial α x : ℂ) = _
  calc
    _ = ((m.factorial : ℂ)⁻¹ * (Nat.multinomial Finset.univ α : ℂ)) *
        ((multiMonomial α x : ℂ) * partialDerivative α φ 0) := by
      rw [hc]
      change _ = (multiFactorial α : ℂ)⁻¹ * ((multiMonomial α x : ℂ) * jet α φ)
      ring
    _ = _ := by ring

/-- The source's all-orders Taylor cancellation estimate, with an explicit
constant and one genuine Schwartz derivative seminorm. -/
theorem taylorRemainder_bound (N : ℕ) (φ : Schwartz ℂ d) (x : Euclidean d) :
    ‖φ x - taylorPolynomial N φ x‖ ≤
      ((N - 1).factorial : ℝ)⁻¹ * SchwartzMap.seminorm ℂ 0 N φ * ‖x‖ ^ N := by
  cases N with
  | zero => simpa using SchwartzMap.norm_le_seminorm ℂ φ x
  | succ n =>
    rw [taylorPolynomial_eq_frechet]
    simpa using frechetTaylorRemainder_bound n φ x




open ExpandedFA.Fourier
variable {d : ℕ}

lemma taylorPolynomial_add (N : ℕ) (φ ψ : Schwartz ℂ d) (x : Euclidean d) :
    taylorPolynomial N (φ + ψ) x = taylorPolynomial N φ x + taylorPolynomial N ψ x := by
  simp only [taylorPolynomial, map_add, add_div, add_mul, Finset.sum_add_distrib]

lemma taylorPolynomial_smul (N : ℕ) (a : ℂ) (φ : Schwartz ℂ d) (x : Euclidean d) :
    taylorPolynomial N (a • φ) x = a * taylorPolynomial N φ x := by
  simp only [taylorPolynomial, map_smul, smul_eq_mul, mul_div_assoc, mul_assoc,
    Finset.mul_sum]

lemma taylorRemainder_add_of_integrable (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ)
    (z : ℂ) (hk : SmoothHomogeneous k lam) (φ ψ : Schwartz ℂ d)
    (hφ : IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1))
    (hψ : IntegrableOn (innerIntegrand k lam N z ψ) (Metric.closedBall 0 1)) :
    taylorRemainder k lam N z (φ + ψ) = taylorRemainder k lam N z φ +
      taylorRemainder k lam N z ψ := by
  have hin : innerIntegrand k lam N z (φ + ψ) =
      innerIntegrand k lam N z φ + innerIntegrand k lam N z ψ := by
    ext x
    simp only [innerIntegrand, add_apply, taylorPolynomial_add, Pi.add_apply]
    ring
  have hout : outerIntegrand k lam z (φ + ψ) =
      outerIntegrand k lam z φ + outerIntegrand k lam z ψ := by
    ext x
    simp only [outerIntegrand, add_apply, mul_add, Pi.add_apply]
  simp only [taylorRemainder, hin, hout, Pi.add_apply, integral_add hφ hψ,
    integral_add (outer_integrable k lam z hk φ) (outer_integrable k lam z hk ψ)]
  ring

lemma taylorRemainder_smul (k : Euclidean d → ℂ) (lam : ℂ) (N : ℕ)
    (z a : ℂ) (φ : Schwartz ℂ d) :
    taylorRemainder k lam N z (a • φ) = a * taylorRemainder k lam N z φ := by
  have hin : innerIntegrand k lam N z (a • φ) =
      fun x => a * innerIntegrand k lam N z φ x := by
    ext x
    simp only [innerIntegrand, smul_apply, smul_eq_mul, taylorPolynomial_smul]
    ring
  have hout : outerIntegrand k lam z (a • φ) =
      fun x => a * outerIntegrand k lam z φ x := by
    ext x
    simp only [outerIntegrand, smul_apply, smul_eq_mul]
    ring
  simp only [taylorRemainder, hin, hout, integral_const_mul, mul_add]

lemma taylorRemainder_bound_sup_strip (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N)
    (b : ℝ) (hb : -(d : ℝ) - N < b) (n : ℕ) :
    ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ n →
      ∀ φ : Schwartz ℂ d, ‖taylorRemainder k lam N z φ‖ ≤
        B * (Finset.Iic (M, M)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ := by
  by_cases hd : d = 0
  · subst d
    exact ⟨0, 0, le_rfl, fun z _ _ φ => by simp [taylorRemainder, innerIntegrand, outerIntegrand]⟩
  obtain ⟨C, hC, hbound⟩ := kernel_norm_bound k lam hk
  let μ : Measure (Euclidean d) := volume
  let p : ℕ := μ.integrablePower
  let D : ℝ := 2 ^ p * ∫ x : Euclidean d, (1 + ‖x‖) ^ (-(p : ℝ))
  let R : ℝ := ∫ x in Metric.closedBall (0 : Euclidean d) 1, ‖x‖ ^ (b + N)
  have hR : 0 ≤ R := integral_nonneg fun _ => by positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hradial := radial_power_integrable (Nat.pos_of_ne_zero hd) (b+N) (by linarith)
  let M : ℕ := max (n+p) J
  refine ⟨M, C * A * R + C * D * 2, by positivity, ?_⟩
  intro z hlo hhi φ
  have hz : z ∈ halfPlane d N := by dsimp [halfPlane]; linarith
  let S := (Finset.Iic (M, M)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ
  have hs (i j : ℕ) (hi : i ≤ M) (hj : j ≤ M) : SchwartzMap.seminorm ℂ i j φ ≤ S := by
    exact Seminorm.le_def.mp (Finset.le_sup (b := (i,j)) (s := Finset.Iic (M,M))
      (f := schwartzSeminormFamily ℂ (Euclidean d) ℂ) (Finset.mem_Iic.mpr ⟨hi,hj⟩)) φ
  have hSJ := hs 0 J (Nat.zero_le _) (le_max_right _ _)
  have hS0 := hs 0 0 (Nat.zero_le _) (Nat.zero_le _)
  have hSn := hs (n+p) 0 (le_max_left _ _) (Nat.zero_le _)
  have hin := inner_integrable_of_taylor_bound k lam N hk φ
    (A * SchwartzMap.seminorm ℂ 0 J φ) (mul_nonneg hA (apply_nonneg _ _))
    (hTaylor φ) z hz
  have hnear : ‖∫ x in Metric.closedBall (0 : Euclidean d) 1,
      innerIntegrand k lam N z φ x‖ ≤ C * A * R * S := by
    calc
      _ ≤ ∫ x in Metric.closedBall (0 : Euclidean d) 1,
          ‖innerIntegrand k lam N z φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in Metric.closedBall (0 : Euclidean d) 1,
          (C * A * S) * ‖x‖ ^ (b + N) := by
        apply integral_mono_ae hin.norm (hradial.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        have hnorm : ‖x‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hx
        by_cases hx0 : x = 0
        · subst x
          simp only [innerIntegrand, kernelWeight, ite_true, zero_mul, norm_zero]
          positivity
        have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        have hexp : ‖x‖ ^ (z.re + N) ≤ ‖x‖ ^ (b + N) :=
          Real.rpow_le_rpow_of_exponent_ge hp hnorm (by linarith)
        calc
          ‖innerIntegrand k lam N z φ x‖ ≤
              (C * ‖x‖ ^ z.re) * (A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N) := by
            change ‖kernelWeight k lam z x * (φ x - taylorPolynomial N φ x)‖ ≤ _
            rw [norm_mul]
            exact mul_le_mul (hbound z x hx0) (hTaylor φ x) (norm_nonneg _)
              (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg x) _))
          _ = C * A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ (z.re+N) := by
            rw [Real.rpow_add hp, Real.rpow_natCast]
            ring
          _ ≤ (C * A * S) * ‖x‖ ^ (b+N) := by gcongr
      _ = C * A * R * S := by rw [integral_const_mul]; dsimp [R]; ring
  have htail := outer_integrable k lam z hk φ
  have houter : ‖∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ,
      outerIntegrand k lam z φ x‖ ≤ C * D * (2 * S) := by
    calc
      _ ≤ ∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ,
          ‖outerIntegrand k lam z φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in (Metric.closedBall (0 : Euclidean d) 1)ᶜ,
          C * (‖x‖ ^ n * ‖φ x‖) := by
        apply integral_mono_ae htail.norm
          (((φ.integrable_pow_mul volume n).const_mul C).integrableOn)
        filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with x hx
        have hnorm : 1 < ‖x‖ := by
          simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
        have hxne : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hnorm)
        change ‖kernelWeight k lam z x * φ x‖ ≤ C * (‖x‖ ^ n * ‖φ x‖)
        rw [norm_mul]
        calc
          ‖kernelWeight k lam z x‖ * ‖φ x‖ ≤ (C * ‖x‖ ^ z.re) * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right (hbound z x hxne) (norm_nonneg _)
          _ ≤ C * (‖x‖ ^ n * ‖φ x‖) := by
            rw [← mul_assoc]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le hnorm.le hhi
      _ ≤ ∫ x : Euclidean d, C * (‖x‖ ^ n * ‖φ x‖) := by
        apply integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun x => by positivity)
          ((φ.integrable_pow_mul volume n).const_mul C)
      _ = C * ∫ x : Euclidean d, ‖x‖ ^ n * ‖φ x‖ := integral_const_mul _ _
      _ ≤ C * (D * (SchwartzMap.seminorm ℂ 0 0 φ +
          SchwartzMap.seminorm ℂ (n+p) 0 φ)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa [D, p, μ] using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ volume φ n 0
      _ ≤ C * D * (2 * S) := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        linarith
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ C * A * R * S + C * D * (2 * S) := add_le_add hnear houter
    _ = (C * A * R + C * D * 2) * S := by ring

lemma taylorRemainder_bound_sup_of_taylor_bound
    (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N)
    (z : ℂ) (hz : z ∈ halfPlane d N) :
    ∃ (s : Finset (ℕ × ℕ)) (B : ℝ), 0 ≤ B ∧ ∀ φ : Schwartz ℂ d,
      ‖taylorRemainder k lam N z φ‖ ≤ B * s.sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ := by
  obtain ⟨n, hn⟩ := exists_nat_ge z.re
  obtain ⟨M, B, hB, h⟩ := taylorRemainder_bound_sup_strip k lam N J hk A hA hTaylor
    z.re hz n
  exact ⟨Finset.Iic (M,M), B, hB, h z le_rfl hn⟩

def remainderTemperedOfBound (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N)
    (z : ℂ) (hz : z ∈ halfPlane d N) : Tempered ℂ d :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (taylorRemainder k lam N z)
    (fun φ ψ => taylorRemainder_add_of_integrable k lam N z hk φ ψ
      (inner_integrable_of_taylor_bound k lam N hk φ (A * SchwartzMap.seminorm ℂ 0 J φ)
        (mul_nonneg hA (apply_nonneg _ _)) (hTaylor φ) z hz)
      (inner_integrable_of_taylor_bound k lam N hk ψ (A * SchwartzMap.seminorm ℂ 0 J ψ)
        (mul_nonneg hA (apply_nonneg _ _)) (hTaylor ψ) z hz))
    (fun a φ => taylorRemainder_smul k lam N z a φ)
    (taylorRemainder_bound_sup_of_taylor_bound k lam N J hk A hA hTaylor z hz)

@[simp] theorem remainderTemperedOfBound_apply
    (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N)
    (z : ℂ) (hz : z ∈ halfPlane d N) (φ : Schwartz ℂ d) :
    remainderTemperedOfBound k lam N J hk A hA hTaylor z hz φ =
      taylorRemainder k lam N z φ := rfl

def remainderFamilyOfBound (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N)
    (z : ℂ) : Tempered ℂ d := by
  classical
  exact if hz : z ∈ halfPlane d N then
    remainderTemperedOfBound k lam N J hk A hA hTaylor z hz else 0

@[simp] theorem remainderFamilyOfBound_apply_of_mem
    (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N)
    (z : ℂ) (hz : z ∈ halfPlane d N) (φ : Schwartz ℂ d) :
    remainderFamilyOfBound k lam N J hk A hA hTaylor z φ =
      taylorRemainder k lam N z φ := by
  simp only [remainderFamilyOfBound, dite_eq_left hz, remainderTemperedOfBound_apply]

lemma square_sup_seminorm_le_schwartzBound (M : ℕ) (φ : Schwartz ℂ d) :
    (Finset.Iic (M,M)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ) φ ≤ schwartzBound M φ := by
  rw [Seminorm.finset_sup_apply]
  change _ ≤ ((⟨schwartzBound M φ, schwartzBound_nonneg M φ⟩ : NNReal) : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro ij hij
  have hij' := Finset.mem_Iic.mp hij
  exact seminorm_le_schwartzBound hij'.1 hij'.2 φ

lemma remainderFamilyOfBound_locallyUniformBound
    (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N) :
    LocallyUniformBound (remainderFamilyOfBound k lam N J hk A hA hTaylor) (halfPlane d N) := by
  intro z₀ hz₀
  let b : ℝ := (z₀.re - (d : ℝ) - N) / 2
  have hb : -(d : ℝ) - N < b := by
    dsimp [halfPlane] at hz₀
    dsimp [b]
    linarith
  have hbz₀ : b < z₀.re := by
    dsimp [halfPlane] at hz₀
    dsimp [b]
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt z₀.re
  obtain ⟨M, C, hC, h⟩ := taylorRemainder_bound_sup_strip k lam N J hk A hA hTaylor b hb n
  let V : Set ℂ := {z | b < z.re ∧ z.re < (n : ℝ)}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV : V ∈ nhds z₀ := hVopen.mem_nhds ⟨hbz₀, hn⟩
  refine ⟨V, hV, C, hC, M, ?_⟩
  intro z hz φ
  have hz' : z ∈ halfPlane d N := hb.trans hz.1
  rw [remainderFamilyOfBound_apply_of_mem k lam N J hk A hA hTaylor z hz']
  exact (h z hz.1.le hz.2.le φ).trans
    (mul_le_mul_of_nonneg_left (square_sup_seminorm_le_schwartzBound M φ) hC)

lemma remainderFamilyOfBound_analytic
    (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N)
    (φ : Schwartz ℂ d) :
    AnalyticOnNhd ℂ (fun z => remainderFamilyOfBound k lam N J hk A hA hTaylor z φ)
      (halfPlane d N) := by
  intro z hz
  apply (taylorRemainder_analytic_of_taylor_bound k lam N hk φ
    (A * SchwartzMap.seminorm ℂ 0 J φ) (mul_nonneg hA (apply_nonneg _ _))
    (hTaylor φ) z hz).congr
  filter_upwards [(isOpen_halfPlane d N).mem_nhds hz] with w hw
  exact (remainderFamilyOfBound_apply_of_mem k lam N J hk A hA hTaylor w hw φ).symm

/-- A proved uniform Taylor estimate constructs the full continuous Schwartz
remainder family at the stated order, including its weak analytic and locally
uniform continuity clauses. -/
theorem construct_remainder_family_of_taylor_bound
    (k : Euclidean d → ℂ) (lam : ℂ) (N J : ℕ)
    (hk : SmoothHomogeneous k lam) (A : ℝ) (hA : 0 ≤ A)
    (hTaylor : ∀ (φ : Schwartz ℂ d) (x : Euclidean d),
      ‖φ x - taylorPolynomial N φ x‖ ≤ A * SchwartzMap.seminorm ℂ 0 J φ * ‖x‖ ^ N) :
    ∃ E : ℂ → Tempered ℂ d,
      (∀ z ∈ halfPlane d N, ∀ φ : Schwartz ℂ d,
        IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1) ∧
        IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ ∧
        E z φ = taylorRemainder k lam N z φ) ∧
      (∀ φ : Schwartz ℂ d,
        AnalyticOnNhd ℂ (fun z => E z φ) (halfPlane d N)) ∧
      LocallyUniformBound E (halfPlane d N) := by
  refine ⟨remainderFamilyOfBound k lam N J hk A hA hTaylor, ?_,
    remainderFamilyOfBound_analytic k lam N J hk A hA hTaylor,
    remainderFamilyOfBound_locallyUniformBound k lam N J hk A hA hTaylor⟩
  intro z hz φ
  exact ⟨inner_integrable_of_taylor_bound k lam N hk φ
      (A * SchwartzMap.seminorm ℂ 0 J φ) (mul_nonneg hA (apply_nonneg _ _))
      (hTaylor φ) z hz, outer_integrable k lam z hk φ,
    remainderFamilyOfBound_apply_of_mem k lam N J hk A hA hTaylor z hz φ⟩




open ExpandedFA.Fourier
variable {d : ℕ}

/-- Polar change of variables as a product integral, without Fubini hypotheses. -/
theorem integral_polar_product (hd : 0 < d) (f : Euclidean d → ℂ) :
    (∫ x, f x) =
      ∫ p : UnitSphere d × Set.Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂(surfaceMeasure d).prod (Measure.volumeIoiPow (d-1)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdim : Module.finrank ℝ (Euclidean d) = d := by simp [Euclidean]
  calc
    (∫ x, f x) = ∫ x : ({0}ᶜ : Set (Euclidean d)), f x.1 ∂volume.comap (Subtype.val : ({0}ᶜ : Set (Euclidean d)) → Euclidean d) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = ∫ p : UnitSphere d × Set.Ioi (0 : ℝ),
        f (((homeomorphUnitSphereProd (Euclidean d)).symm p : ({0}ᶜ : Set (Euclidean d))) : Euclidean d)
          ∂(surfaceMeasure d).prod (Measure.volumeIoiPow (d-1)) := by
      convert! (volume : Measure (Euclidean d)).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd (Euclidean d)).symm p : ({0}ᶜ : Set (Euclidean d))) : Euclidean d)) using 1
      · simp
      · rw [hdim]
        rfl
    _ = _ := by simp only [homeomorphUnitSphereProd_symm_apply_coe]


/-- The radial complex-power integral with the exact Euclidean Jacobian. -/
theorem radial_cpow_integral (n : ℕ) (w : ℂ) (hw : -1 < w.re + n) :
    (∫ r : Set.Ioi (0 : ℝ), if r.1 ≤ 1 then (r.1 : ℂ)^w else 0
      ∂Measure.volumeIoiPow n) = (w + (n : ℂ) + 1)⁻¹ := by
  have hzero : w + (n : ℂ) + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at this
    linarith
  calc
    _ = ∫ r : Set.Ioi (0 : ℝ),
        Real.toNNReal (r.1 ^ n) • (if r.1 ≤ 1 then (r.1 : ℂ)^w else 0)
        ∂volume.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) := by
      unfold Measure.volumeIoiPow
      simp only [ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]
      exact (measurable_subtype_coe.pow_const n).real_toNNReal
    _ = ∫ r in Set.Ioi (0 : ℝ), Real.toNNReal (r^n) •
        (if r ≤ 1 then (r : ℂ)^w else 0) :=
      by
        convert! integral_subtype_comap measurableSet_Ioi
          (fun r : ℝ => Real.toNNReal (r^n) • (if r ≤ 1 then (r : ℂ)^w else 0)) using 1
    _ = ∫ r in Set.Ioi (0 : ℝ), (Set.Iic (1 : ℝ)).indicator
        (fun r => (r : ℂ) ^ (w + (n : ℂ))) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hrpos : 0 < r := hr
      by_cases hr1 : r ≤ 1
      · simp only [Set.indicator_apply, Set.mem_Iic, hr1, ↓reduceIte, NNReal.smul_def,
          Real.coe_toNNReal _ (pow_nonneg hrpos.le n), Complex.real_smul]
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hrpos.ne'),
          Complex.cpow_natCast, ← Complex.ofReal_pow]
        ring
      · simp [hr1]
    _ = ∫ r in Set.Ioc (0 : ℝ) 1, (r : ℂ) ^ (w + (n : ℂ)) := by
      rw [setIntegral_indicator measurableSet_Iic]
      rfl
    _ = ∫ r : ℝ in 0..1, (r : ℂ) ^ (w + (n : ℂ)) :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = _ := by
      rw [integral_cpow (Or.inl (by simpa using hw))]
      simp [Complex.zero_cpow hzero, one_div]


/-- Integrate a complex homogeneous function on the unit ball. The sphere
measure is the unnormalized `volume.toSphere` from the source definition. -/
theorem homogeneous_ball_integral (hd : 0 < d) (f : Euclidean d → ℂ) (w : ℂ)
    (hf : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 → f (a • x) = (a : ℂ)^w * f x)
    (hw : -(d : ℝ) < w.re) :
    (∫ x in Metric.closedBall (0 : Euclidean d) 1, f x) =
      (w + (d : ℂ))⁻¹ * ∫ θ : UnitSphere d, f θ ∂surfaceMeasure d := by
  have hdn : (d-1) + 1 = d := Nat.sub_add_cancel hd
  have hdnR : ((d-1 : ℕ) : ℝ) + 1 = d := by exact_mod_cast hdn
  have hdnC : ((d-1 : ℕ) : ℂ) + 1 = d := by exact_mod_cast hdn
  rw [← integral_indicator measurableSet_closedBall, integral_polar_product hd]
  have hfun : (fun p : UnitSphere d × Set.Ioi (0 : ℝ) =>
      (Metric.closedBall (0 : Euclidean d) 1).indicator f (p.2.1 • p.1.1)) =
      (fun p : UnitSphere d × Set.Ioi (0 : ℝ) =>
        f p.1 * (if p.2.1 ≤ 1 then (p.2.1 : ℂ)^w else 0)) := by
    funext p
    have hθ : ‖(p.1 : Euclidean d)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using p.1.2
    have hpos : 0 < p.2.1 := p.2.2
    have hmem : p.2.1 • (p.1 : Euclidean d) ∈ Metric.closedBall (0 : Euclidean d) 1 ↔ p.2.1 ≤ 1 := by
      simp [Metric.mem_closedBall, norm_smul, abs_of_pos hpos, hθ]
    by_cases hr : p.2.1 ≤ 1
    · rw [Set.indicator_of_mem (hmem.mpr hr), ite_eq_left hr,
        hf p.2 hpos p.1 (ne_zero_of_mem_unit_sphere p.1)]
      ring
    · rw [Set.indicator_of_notMem (not_iff_not.mpr hmem |>.mpr hr), ite_eq_right hr, mul_zero]
  rw [hfun]
  calc
    _ = (∫ θ : UnitSphere d, f θ ∂surfaceMeasure d) *
        (∫ r : Set.Ioi (0 : ℝ), if r.1 ≤ 1 then (r.1 : ℂ)^w else 0
          ∂Measure.volumeIoiPow (d-1)) := by
      convert! integral_prod_mul (μ := surfaceMeasure d) (ν := Measure.volumeIoiPow (d-1))
        (fun θ : UnitSphere d => f θ)
        (fun r : Set.Ioi (0 : ℝ) => if r.1 ≤ 1 then (r.1 : ℂ)^w else 0) using 1
    _ = _ := by
      rw [radial_cpow_integral (d-1) w (by linarith)]
      rw [add_assoc, hdnC, mul_comm]


theorem multiMonomial_smul (α : MultiIndex d) (a : ℝ) (x : Euclidean d) :
    multiMonomial α (a • x) = a ^ order α * multiMonomial α x := by
  simp only [multiMonomial, PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

def taylorLayer (m : ℕ) (φ : Schwartz ℂ d) (x : Euclidean d) : ℂ :=
  ∑ α ∈ indices d m, jet α φ / (multiFactorial α : ℂ) * (multiMonomial α x : ℂ)

theorem taylorLayer_smul (m : ℕ) (φ : Schwartz ℂ d) (a : ℝ) (x : Euclidean d) :
    taylorLayer m φ (a • x) = (a : ℂ) ^ m * taylorLayer m φ x := by
  classical
  unfold taylorLayer
  simp only [multiMonomial_smul, Complex.ofReal_mul, Complex.ofReal_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [(mem_indices α m).mp hα]
  ring

/-- Angular integration of one actual coordinate Taylor layer. -/
theorem taylorLayer_sphere_integral (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (m : ℕ) (φ : Schwartz ℂ d) :
    (∫ θ : UnitSphere d, k θ * taylorLayer m φ θ ∂surfaceMeasure d) =
      taylorCoefficient k m φ := by
  classical
  have hfun : (fun θ : UnitSphere d => k θ * taylorLayer m φ θ) =
      (fun θ : UnitSphere d => ∑ α ∈ indices d m,
        (jet α φ / (multiFactorial α : ℂ)) * (k θ * (multiMonomial α θ : ℂ))) := by
    funext θ
    simp only [taylorLayer, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    ring
  rw [hfun, integral_finsetSum]
  · simp only [integral_const_mul, moment, taylorCoefficient, sum_apply,
      smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro α hα
    ring
  · intro α hα
    exact (moment_integrable k lam hk α).const_mul _

/-- The exact polar denominator in one Taylor layer, before distributional gluing. -/
theorem taylorLayer_ball_integral (hd : 0 < d) (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (m : ℕ) (hz : z ∈ halfPlane d m)
    (φ : Schwartz ℂ d) :
    (∫ x in Metric.closedBall (0 : Euclidean d) 1,
      kernelWeight k lam z x * taylorLayer m φ x) =
      (z - pole d m)⁻¹ * taylorCoefficient k m φ := by
  have hhom : ∀ (a : ℝ), 0 < a → ∀ x : Euclidean d, x ≠ 0 →
      kernelWeight k lam z (a • x) * taylorLayer m φ (a • x) =
      (a : ℂ) ^ (z + (m : ℂ)) * (kernelWeight k lam z x * taylorLayer m φ x) := by
    intro a ha x hx
    rw [kernel_scaling d k lam z hk a ha x, taylorLayer_smul,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'), Complex.cpow_natCast]
    ring
  have hthreshold : -(d : ℝ) < (z + (m : ℂ)).re := by
    dsimp [halfPlane] at hz
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  rw [homogeneous_ball_integral hd _ (z + (m : ℂ)) hhom hthreshold]
  have hsphere : (fun θ : UnitSphere d => kernelWeight k lam z θ * taylorLayer m φ θ) =
      fun θ : UnitSphere d => k θ * taylorLayer m φ θ := by
    funext θ
    have hθ : ‖(θ : Euclidean d)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.2
    simp [kernelWeight, ne_zero_of_mem_unit_sphere θ, hθ]
  rw [hsphere, taylorLayer_sphere_integral k lam hk]
  congr 2
  simp only [pole]
  ring


@[simp] theorem taylorPolynomial_succ (N : ℕ) (φ : Schwartz ℂ d) (x : Euclidean d) :
    taylorPolynomial (N+1) φ x = taylorPolynomial N φ x + taylorLayer N φ x := by
  classical
  simp [taylorPolynomial, taylorLayer, Finset.sum_range_succ]

/-- The exact adjacent remainder identity follows from the genuine polar
calculation as soon as the two inner integrals are integrable. -/
theorem taylorRemainder_step (hd : 0 < d) (k : Euclidean d → ℂ) (lam z : ℂ)
    (hk : SmoothHomogeneous k lam) (N : ℕ) (hz : z ∈ halfPlane d N)
    (φ : Schwartz ℂ d)
    (hN : IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1))
    (hN1 : IntegrableOn (innerIntegrand k lam (N+1) z φ) (Metric.closedBall 0 1)) :
    taylorRemainder k lam N z φ =
      (z - pole d N)⁻¹ * taylorCoefficient k N φ + taylorRemainder k lam (N+1) z φ := by
  have hdiff : (∫ x in Metric.closedBall (0 : Euclidean d) 1, innerIntegrand k lam N z φ x) -
      (∫ x in Metric.closedBall (0 : Euclidean d) 1, innerIntegrand k lam (N+1) z φ x) =
      (z - pole d N)⁻¹ * taylorCoefficient k N φ := by
    rw [← integral_sub hN hN1]
    rw [← taylorLayer_ball_integral hd k lam z hk N hz φ]
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    simp only [innerIntegrand, taylorPolynomial_succ]
    ring
  unfold taylorRemainder
  rw [← hdiff]
  ring


/-- Once the Taylor remainder integrals form locally uniformly bounded weakly
analytic continuous functionals, every gluing and dilation clause follows. -/
theorem construction_of_integral_remainders (hd : 0 < d) (k : Euclidean d → ℂ) (lam : ℂ)
    (hk : SmoothHomogeneous k lam) (E : ℕ → ℂ → Tempered ℂ d)
    (hintegral : ∀ N z, z ∈ halfPlane d N → ∀ φ : Schwartz ℂ d,
      IntegrableOn (innerIntegrand k lam N z φ) (Metric.closedBall 0 1) ∧
      IntegrableOn (outerIntegrand k lam z φ) (Metric.closedBall 0 1)ᶜ ∧
      E N z φ = taylorRemainder k lam N z φ)
    (hanalytic : ∀ N, (∀ φ : Schwartz ℂ d,
      AnalyticOnNhd ℂ (fun z => E N z φ) (halfPlane d N)) ∧
      LocallyUniformBound (E N) (halfPlane d N)) :
    Construction k lam := by
  apply construction_of_remainder_data k lam hk E hintegral hanalytic
  intro N z hz
  have hz1 : z ∈ halfPlane d (N+1) := halfPlane_mono (Nat.le_succ N) hz
  ext φ
  have hN := hintegral N z hz φ
  have hN1 := hintegral (N+1) z hz1 φ
  change E N z φ = (z - pole d N)⁻¹ * taylorCoefficient k N φ + E (N+1) z φ
  rw [hN.2.2, hN1.2.2]
  exact taylorRemainder_step hd k lam z hk N hz φ hN.1 hN1.1


/-- Construct the meromorphic tempered-distribution family from the original
smooth homogeneous kernel. Taylor's theorem proves the required estimates;
polar integration proves compatibility, and analytic gluing yields the family. -/
theorem construct_family :
    Specs.ExpandedFA.PartIV.HomogeneousMeromorphic.constructionType := by
  intro d k lam hk
  by_cases hd : d = 0
  · subst d
    exact zero_dimension k lam
  have hexists (N : ℕ) := construct_remainder_family_of_taylor_bound k lam N N hk
    (((N - 1).factorial : ℝ)⁻¹) (by positivity)
    (fun φ x => taylorRemainder_bound N φ x)
  choose E hE using hexists
  exact construction_of_integral_remainders (Nat.pos_of_ne_zero hd) k lam hk E
    (fun N => (hE N).1) (fun N => (hE N).2)

end ExpandedFA.PartIV.HomogeneousMeromorphic
