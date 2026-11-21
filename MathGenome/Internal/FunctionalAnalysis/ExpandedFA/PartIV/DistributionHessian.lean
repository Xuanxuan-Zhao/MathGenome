import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DistributionHessian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PositiveDistributions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionLimits
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Convex.Deriv

open Set TopologicalSpace MeasureTheory Filter
open scoped Distributions ContDiff Topology Matrix CompactlySupported

namespace ExpandedFA.PartIV.DistributionHessian
open ExpandedFA.Distributions ExpandedFA.PartIV.PositiveDistributions

variable {d : ℕ} {Ω : Opens (Domain d)}

/-- Every continuous function on the open subspace has an ambient
representative of precisely the regularity required in the main statement. -/
theorem exists_continuousOn_representative (f : Ω → ℝ) (hf : Continuous f) :
    ∃ g : Domain d → ℝ, ContinuousOn g Ω ∧ ∀ x : Ω, g x.val = f x := by
  let g : Domain d → ℝ := Subtype.val.extend f 0
  have he : (fun x : Ω => g x.val) = f :=
    Function.extend_comp Subtype.val_injective f 0
  refine ⟨g, ?_, fun x => congrFun he x⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun x : Ω => g x.val)
  rw [he]
  exact hf

/-- Different extensions off Ω give the same regular distribution. -/
theorem functionDistribution_congr (f g : Domain d → ℝ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) (hfg : EqOn f g Ω) :
    functionDistribution (Ω := Ω) f = functionDistribution (Ω := Ω) g := by
  ext φ
  change regularDistribution volume f φ = regularDistribution volume g φ
  rw [regularDistribution_apply volume f (hf.locallyIntegrableOn Ω.isOpen.measurableSet),
    regularDistribution_apply volume g (hg.locallyIntegrableOn Ω.isOpen.measurableSet)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change f x * φ x = g x * φ x
  by_cases hx : x ∈ Ω
  · rw [hfg hx]
  · simp [φ.zero_on_compl hx]

/-- For real distributions the upstream scalar-field-independent definition
of positivity is exactly nonnegativity on nonnegative real tests. -/
theorem isPositive_iff (u : ScalarDistribution ℝ Ω) :
    IsPositive u ↔ ∀ φ : Tests ℝ Ω, (∀ x, 0 ≤ φ x) → 0 ≤ u φ := by
  have hr (φ : Tests ℝ Ω) : realTest φ = φ := by ext x; rfl
  constructor
  · intro hu φ hφ
    obtain ⟨r, hr0, heq⟩ := hu φ hφ
    rw [hr] at heq
    change u φ = r at heq
    rw [heq]
    exact hr0
  · intro hu φ hφ
    exact ⟨u φ, hu φ hφ, by rw [hr]; rfl⟩

theorem coordinate_sum (a : Domain d) :
    (∑ i, a i • coordinateVector i) = a := by
  classical
  ext j
  simp [coordinateVector, Pi.single_apply]

/-- Differentiation in an arbitrary direction is the coordinate combination
as an equality of continuous operators on the original LF space. -/
theorem lineDeriv_eq_sum (a : Domain d) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a : Tests ℝ Ω →L[ℝ] Tests ℝ Ω) =
      ∑ i, a i • TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (coordinateVector i) := by
  ext φ x
  have hev (v : Domain d) :
      TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ x = fderiv ℝ φ x v := by
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
  simp only [sum_apply, smul_apply, hev]
  conv_lhs => rw [← coordinate_sum a]
  simp only [map_sum, map_smul, smul_eq_mul]

@[simp] theorem hessianEntry_apply (u : ScalarDistribution ℝ Ω) (i j : Fin d)
    (φ : Tests ℝ Ω) : hessianEntry u i j φ = u (testPartialCLM [i, j] φ) := by
  simp [hessianEntry, Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue]

@[simp] theorem directionalSecond_apply (u : ScalarDistribution ℝ Ω) (a : Domain d)
    (φ : Tests ℝ Ω) :
    directionalSecond u a φ = ∑ i, ∑ j, a i * a j * hessianEntry u i j φ := by
  simp [directionalSecond, smul_eq_mul]

theorem direction_formula :
    Specs.ExpandedFA.PartIV.DistributionHessian.directionFormulaType := by
  intro d Ω u a
  ext φ
  simp only [directionalSecond_apply, hessianEntry_apply, ContinuousLinearMap.comp_apply]
  rw [lineDeriv_eq_sum a]
  simp only [sum_apply, smul_apply, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  simp only [testPartialCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem testPartial_two_apply (i j : Fin d) (φ : Tests ℝ Ω) (x : Domain d) :
    testPartialCLM [i, j] φ x =
      iteratedFDeriv ℝ 2 φ x ![coordinateVector i, coordinateVector j] := by
  have h := partialFunction_ofFn 2 ![i, j] φ φ.contDiff x
  rw [testPartial_formula ℝ d Ω [i, j] φ]
  have he : (fun k : Fin 2 => coordinateVector (![i, j] k)) =
      ![coordinateVector i, coordinateVector j] := by
    ext k
    fin_cases k <;> rfl
  simpa [List.ofFn_succ, he] using h

theorem hessianEntry_symmetric (u : ScalarDistribution ℝ Ω) (i j : Fin d) :
    hessianEntry u i j = hessianEntry u j i := by
  ext φ
  simp only [hessianEntry_apply]
  congr 1
  ext x
  rw [testPartial_two_apply, testPartial_two_apply]
  exact (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons

theorem pairedHessian_isHermitian (u : ScalarDistribution ℝ Ω) (φ : Tests ℝ Ω) :
    (pairedHessian u φ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
  intro i j
  exact congrArg (fun v : ScalarDistribution ℝ Ω => v φ) (hessianEntry_symmetric u j i)

theorem pairedHessian_quadratic (u : ScalarDistribution ℝ Ω) (φ : Tests ℝ Ω)
    (a : Domain d) :
    star a ⬝ᵥ (pairedHessian u φ *ᵥ a) = directionalSecond u a φ := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, directionalSecond_apply, pairedHessian]
  congr 1
  ext i
  congr 1
  ext j
  ring

theorem matrix_meaning :
    Specs.ExpandedFA.PartIV.DistributionHessian.matrixMeaningType := by
  intro d Ω u
  constructor
  · intro hu φ hφ
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (pairedHessian_isHermitian u φ)
    intro a
    rw [pairedHessian_quadratic]
    exact (isPositive_iff _).mp (hu a) φ hφ
  · intro hu a
    apply (isPositive_iff _).mpr
    intro φ hφ
    rw [← pairedHessian_quadratic]
    exact (hu φ hφ).dotProduct_mulVec_nonneg a

theorem hessian_pairing : Specs.ExpandedFA.PartIV.DistributionHessian.pairingType := by
  intro d Ω f hf a φ
  rw [direction_formula, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact regularDistribution_apply volume f (hf.locallyIntegrableOn Ω.isOpen.measurableSet) _

theorem one_dimensional_direction {Ω : Opens (Domain 1)} (u : ScalarDistribution ℝ Ω) (a : Domain 1) :
    directionalSecond u a = (a 0 * a 0) • hessianEntry u 0 0 := by
  simp [directionalSecond]

theorem one_dimensional_bridge :
    Specs.ExpandedFA.PartIV.DistributionHessian.oneDimensionalBridgeType := by
  intro Ω u
  rw [← positivity_iff_unique_measure ℝ 1 Ω (hessianEntry u 0 0)]
  constructor
  · intro hu
    have h := hu (fun _ => 1)
    simpa [one_dimensional_direction] using h
  · intro hu a
    apply (isPositive_iff _).mpr
    intro φ hφ
    rw [one_dimensional_direction]
    exact mul_nonneg (mul_self_nonneg _) ((isPositive_iff _).mp hu φ hφ)

/-- The elementary compact-support estimate needed to pass from local uniform
convergence of densities to distribution convergence. -/
theorem functionDistribution_pairing_bound (f g : Domain d → ℝ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) (φ : Tests ℝ Ω)
    (M : ℝ) (hM : ∀ x ∈ tsupport φ, ‖f x - g x‖ ≤ M) :
    ‖functionDistribution f φ - functionDistribution g φ‖ ≤ M * ∫ x, ‖φ x‖ := by
  have hfLI := hf.locallyIntegrableOn (μ := volume) Ω.isOpen.measurableSet
  have hgLI := hg.locallyIntegrableOn (μ := volume) Ω.isOpen.measurableSet
  have hfi : Integrable (fun x => f x * φ x) := by
    simpa [smul_eq_mul, mul_comm] using φ.integrable_smul hfLI
  have hgi : Integrable (fun x => g x * φ x) := by
    simpa [smul_eq_mul, mul_comm] using φ.integrable_smul hgLI
  have hφi : Integrable (fun x => ‖φ x‖) :=
    (φ.integrable (locallyIntegrableOn_const (1 : ℝ))).norm
  rw [show functionDistribution (Ω := Ω) f = regularDistribution volume f from rfl,
    show functionDistribution (Ω := Ω) g = regularDistribution volume g from rfl,
    regularDistribution_apply volume f hfLI, regularDistribution_apply volume g hgLI,
    ← integral_sub hfi hgi, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hφi.const_mul M)
  apply Eventually.of_forall
  intro x
  rw [← sub_mul, norm_mul]
  by_cases hx : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, mul_zero]

theorem density_limit : Specs.ExpandedFA.PartIV.DistributionHessian.densityLimitType := by
  intro d Ω f g hf hg hfg φ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := ∫ x, ‖φ x‖
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let K : Compacts (Domain d) := ⟨tsupport φ, φ.hasCompactSupport⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hfg K φ.tsupport_subset) δ hδ]
    with n hn
  rw [dist_eq_norm]
  apply (functionDistribution_pairing_bound (f n) g (hf n) hg φ δ ?_).trans_lt
  · calc
      δ * C < δ * (C + 1) := mul_lt_mul_of_pos_left (lt_add_one C) hδ
      _ = ε := div_mul_cancel₀ ε (by positivity)
  · intro x hx
    simpa only [dist_eq_norm, norm_sub_rev] using (hn x hx).le

/-- Every fixed directional second derivative passes to a weak limit simply
by testing the original distributions against a twice differentiated test. -/
theorem directionalSecond_converges (u : ℕ → ScalarDistribution ℝ Ω)
    (v : ScalarDistribution ℝ Ω) (hu : DistributionConverges u v) (a : Domain d) :
    DistributionConverges (fun n => directionalSecond (u n) a) (directionalSecond v a) := by
  intro φ
  simpa only [direction_formula d Ω, ContinuousLinearMap.comp_apply] using
    hu (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a φ))

/-- Positivity is closed under weak limits, so the forward mollification
argument needs only convergence of each individual test pairing. -/
theorem isPositive_of_distributionConverges (u : ℕ → ScalarDistribution ℝ Ω)
    (v : ScalarDistribution ℝ Ω) (hu : ∀ n, IsPositive (u n))
    (hv : DistributionConverges u v) : IsPositive v := by
  apply (isPositive_iff _).mpr
  intro φ hφ
  exact ge_of_tendsto (hv φ) (Eventually.of_forall fun n => (isPositive_iff _).mp (hu n) φ hφ)

/-- A compactly supported continuous localization of a density.  The cutoff
is only applied inside Ω; extending by zero is continuous because its support
is compactly contained in Ω. -/
theorem exists_compact_localization (f : Domain d → ℝ) (hf : ContinuousOn f Ω)
    (K : Set (Domain d)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ F : Domain d → ℝ, Continuous F ∧ HasCompactSupport F ∧ EqOn F f K := by
  obtain ⟨χ, _, _, hχ⟩ := exists_cutoff K hK hKΩ
  let g : C_c(Ω, ℝ) :=
    ⟨⟨fun x => χ x.val * f x.val,
      (χ.continuous.comp continuous_subtype_val).mul
        (continuousOn_iff_continuous_domRestrict.mp hf)⟩,
      (testToCc χ).hasCompactSupport.mul_right⟩
  let F : Domain d → ℝ := Subtype.val.extend g 0
  refine ⟨F, HasCompactSupport.continuous_extend_zero Ω.isOpen g.continuous
    g.hasCompactSupport, g.hasCompactSupport.extend_zero continuous_subtype_val, ?_⟩
  intro x hx
  have he := congrFun (Function.extend_comp Subtype.val_injective g 0) ⟨x, hKΩ hx⟩
  change F x = χ x * f x at he
  rw [he, hχ x hx, one_mul]

open scoped Convolution in
/-- Differentiating a smooth compact kernel commutes with convolution, in
one fixed direction. The density is only required to be locally integrable. -/
theorem fderiv_convolution_direction (F ρ : Domain d → ℝ)
    (hF : LocallyIntegrable F volume) (hρc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ ∞ ρ) (a x : Domain d) :
    fderiv ℝ (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x a =
      (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun y => fderiv ℝ ρ y a)) x := by
  rw [(hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hF (hρ.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply _ hF (hρc.fderiv ℝ)
    (hρ.continuous_fderiv (by simp)) x a

open scoped Convolution in
/-- The twice differentiated convolution is the convolution with the actual
twice differentiated kernel. -/
theorem fderiv_convolution_second (F ρ : Domain d → ℝ)
    (hF : LocallyIntegrable F volume) (hρc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ ∞ ρ) (a x : Domain d) :
    fderiv ℝ (fun z => fderiv ℝ
      (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) z a) x a =
      (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun y => fderiv ℝ (fun z => fderiv ℝ ρ z a) y a)) x := by
  have he : (fun z => fderiv ℝ (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) z a) =
      F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun z => fderiv ℝ ρ z a) := by
    funext z
    exact fderiv_convolution_direction F ρ hF hρc hρ a z
  rw [he]
  apply fderiv_convolution_direction _ _ hF
  · exact hρc.fderiv_apply ℝ a
  · exact (hρ.fderiv_right (by simp)).clm_apply contDiff_const

/-- First derivative of a reflected translate. -/
theorem fderiv_reflect_translate (ρ : Domain d → ℝ) (hρ : Differentiable ℝ ρ)
    (x y a : Domain d) :
    fderiv ℝ (fun z => ρ (x - z)) y a = -fderiv ℝ ρ (x - y) a := by
  change fderiv ℝ (ρ ∘ (fun z => x - z)) y a = _
  rw [fderiv_comp y (hρ _) (by fun_prop)]
  rw [show fderiv ℝ (fun z : Domain d => x - z) y =
    -ContinuousLinearMap.id ℝ _ from ((hasFDerivAt_id y).const_sub x).fderiv]
  simp

/-- The two reflection signs cancel for the second derivative. -/
theorem fderiv_reflect_translate_second (ρ : Domain d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (x y a : Domain d) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => ρ (x - w)) z a) y a =
      fderiv ℝ (fun z => fderiv ℝ ρ z a) (x - y) a := by
  have he : (fun z => fderiv ℝ (fun w => ρ (x - w)) z a) =
      -(fun z => (fun w => fderiv ℝ ρ w a) (x - z)) := by
    funext z
    exact fderiv_reflect_translate ρ (hρ.differentiable (by simp)) x z a
  rw [he, fderiv_neg, neg_apply,
    fderiv_reflect_translate (fun w => fderiv ℝ ρ w a)
      ((show ContDiff ℝ ∞ (fun w => fderiv ℝ ρ w a) from
        (hρ.fderiv_right (by simp)).clm_apply contDiff_const).differentiable (by simp)),
    neg_neg]

/-- The familiar smooth Hessian criterion, obtained on each segment from
the one-variable second derivative criterion. -/
theorem convexOn_of_second_nonneg {S : Set (Domain d)} (hS : Convex ℝ S)
    (F : Domain d → ℝ) (hF : ContDiff ℝ ∞ F)
    (hsec : ∀ x ∈ S, ∀ a : Domain d,
      0 ≤ fderiv ℝ (fun z => fderiv ℝ F z a) x a) : ConvexOn ℝ S F := by
  refine ⟨hS, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  let a := y - x
  let p : ℝ → Domain d := fun t => t • a + x
  have hp (t : ℝ) : HasDerivAt p a t := by
    simpa [p] using ((hasDerivAt_id t).smul_const a).add_const x
  have h1 (t : ℝ) : HasDerivAt (fun s => F (p s)) (fderiv ℝ F (p t) a) t :=
    (hF.differentiable (by simp) (p t)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hH : ContDiff ℝ ∞ (fun z => fderiv ℝ F z a) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have h2 (t : ℝ) : HasDerivAt (fun s => fderiv ℝ F (p s) a)
      (fderiv ℝ (fun z => fderiv ℝ F z a) (p t) a) t :=
    (hH.differentiable (by simp) (p t)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ S := by
    have he : p t = (1 - t) • x + t • y := by dsimp [p, a]; module
    rw [he]
    exact hS hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => F (p t)) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      ((hF.continuous.comp (by fun_prop)).continuousOn)
      (fun t _ => (h1 t).hasDerivWithinAt)
      (fun t _ => (h2 t).hasDerivWithinAt)
      (fun t ht => hsec (p t) (hmem t (interior_subset ht)) a)
  have hi := hconv.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hα hβ hαβ
  have hpx : p 0 = x := by simp [p]
  have hpy : p 1 = y := by simp [p, a]
  have hpβ : p (α * 0 + β * 1) = α • x + β • y := by
    dsimp [p, a]
    have he : α = 1 - β := by linarith
    rw [he]
    module
  simpa only [smul_eq_mul, hpβ, hpx, hpy] using hi

theorem lineDeriv_twice_apply (φ : Tests ℝ Ω) (a x : Domain d) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a φ)) x =
      fderiv ℝ (fun z => fderiv ℝ φ z a) x a := by
  have he : ∀ ψ : Tests ℝ Ω, ∀ z : Domain d,
      TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a ψ z = fderiv ℝ ψ z a := by
    intro ψ z
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
  rw [he]
  congr 2

open scoped Convolution in
/-- A positive distributional Hessian makes every admissible local
mollification have nonnegative second directional derivatives. The support
and agreement conditions explicitly ensure that no value outside Ω is used. -/
theorem convolution_second_nonneg_of_positive (f F ρ : Domain d → ℝ)
    (hf : ContinuousOn f Ω) (hF : LocallyIntegrable F volume)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ ∞ ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hu : ∀ a : Domain d, IsPositive (directionalSecond (functionDistribution (Ω := Ω) f) a))
    (x a : Domain d) (hs : tsupport (fun y => ρ (x - y)) ⊆ Ω)
    (heq : EqOn F f (tsupport (fun y => ρ (x - y)))) :
    0 ≤ fderiv ℝ (fun z => fderiv ℝ
      (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) z a) x a := by
  let ψ : Tests ℝ Ω := ⟨fun y => ρ (x - y), hρ.comp (by fun_prop),
    hρc.comp_homeomorph (Homeomorph.subLeft x), hs⟩
  let Dψ := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a ψ)
  have hval (y : Domain d) : Dψ y =
      fderiv ℝ (fun z => fderiv ℝ ρ z a) (x - y) a := by
    rw [lineDeriv_twice_apply]
    exact fderiv_reflect_translate_second ρ hρ x y a
  rw [fderiv_convolution_second F ρ hF hρc hρ a x, convolution_def]
  change 0 ≤ ∫ y, F y * fderiv ℝ (fun z => fderiv ℝ ρ z a) (x - y) a
  have hp := (isPositive_iff _).mp (hu a) ψ (fun y => hρ0 _)
  rw [hessian_pairing d Ω f hf a ψ] at hp
  change 0 ≤ ∫ y, f y * Dψ y at hp
  convert hp using 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [← hval y]
  by_cases hy : y ∈ tsupport ψ
  · rw [heq hy]
  · have hz : Dψ y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hyD
      have hts : tsupport Dψ ⊆ tsupport ψ :=
        (tsupport_fderiv_apply_subset ℝ a).trans (tsupport_fderiv_apply_subset ℝ a)
      exact hy (hts hyD)
    rw [hz, mul_zero, mul_zero]

/-- A concrete sequence of nonnegative smooth mass-one kernels with radii
shrinking to zero. This construction also works in dimension zero. -/
noncomputable def shrinkingBump (d n : ℕ) : ContDiffBump (0 : Domain d) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

theorem shrinkingBump_radius (d : ℕ) :
    Tendsto (fun n => (shrinkingBump d n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

open scoped Convolution in
/-- Smooth compactly supported kernels recover every continuous density at
all points, without any global integrability assumption. -/
theorem shrinkingBump_converges (F : Domain d → ℝ) (hF : Continuous F) (x : Domain d) :
    Tendsto (fun n => (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      (shrinkingBump d n).normed volume) x) atTop (𝓝 (F x)) := by
  have hs (n : ℕ) :
      F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (shrinkingBump d n).normed volume =
      (shrinkingBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F := by
    funext z
    rw [convolution_eq_swap, convolution_def]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    exact mul_comm _ _
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (shrinkingBump_radius d) hF x
  exact ht.congr (fun n => congrFun (hs n).symm x)

/-- A translated kernel with sufficiently small radius remains in the
closed thickening of the compact set around which we localize. -/
theorem translated_bump_support {S : Set (Domain d)} {δ : ℝ} {x : Domain d}
    (hx : x ∈ S) (b : ContDiffBump (0 : Domain d)) (hb : b.rOut ≤ δ) :
    tsupport (fun y => b.normed volume (x - y)) ⊆ Metric.cthickening δ S := by
  change tsupport (b.normed volume ∘ (Homeomorph.subLeft x)) ⊆ _
  rw [tsupport_comp_eq_preimage, b.tsupport_normed_eq]
  intro y hy
  apply Metric.mem_cthickening_of_dist_le y x δ S hx
  have hnorm : ‖x - y‖ ≤ b.rOut := by simpa using hy
  simpa only [dist_eq_norm, norm_sub_rev] using hnorm.trans hb

open scoped Convolution in
/-- Reverse analytic implication of the source theorem. A separate
localization is chosen around each segment, so unbounded domains and
segments close to the boundary require no extra assumptions. -/
theorem convexOn_of_positive_hessian (f : Domain d → ℝ)
    (hΩ : Convex ℝ (Ω : Set (Domain d))) (hf : ContinuousOn f Ω)
    (hu : ∀ a : Domain d,
      IsPositive (directionalSecond (functionDistribution (Ω := Ω) f) a)) :
    ConvexOn ℝ (Ω : Set (Domain d)) f := by
  refine ⟨hΩ, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  let S : Set (Domain d) := segment ℝ x y
  have hSc : IsCompact S := by
    rw [show S = (AffineMap.lineMap x y) '' Icc (0 : ℝ) 1 from segment_eq_image_lineMap ℝ x y]
    exact isCompact_Icc.image (by fun_prop)
  have hSΩ : S ⊆ Ω := hΩ.segment_subset hx hy
  obtain ⟨δ, hδ, hKΩ⟩ := hSc.exists_cthickening_subset_open Ω.isOpen hSΩ
  obtain ⟨F, hFc, _, hFf⟩ := exists_compact_localization f hf
    (Metric.cthickening δ S) hSc.cthickening hKΩ
  let G : ℕ → Domain d → ℝ := fun n =>
    F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (shrinkingBump d n).normed volume
  have hG (z : Domain d) : Tendsto (fun n => G n z) atTop (𝓝 (F z)) :=
    shrinkingBump_converges F hFc z
  have hconv : ∀ᶠ n in atTop, ConvexOn ℝ S (G n) := by
    filter_upwards [(shrinkingBump_radius d).eventually (eventually_le_nhds hδ)] with n hn
    apply convexOn_of_second_nonneg (convex_segment _ _) (G n)
    · exact (shrinkingBump d n).hasCompactSupport_normed.contDiff_convolution_right
        _ hFc.locallyIntegrable (shrinkingBump d n).contDiff_normed
    · intro z hz a
      have hs := translated_bump_support hz (shrinkingBump d n) hn
      exact convolution_second_nonneg_of_positive f F _ hf hFc.locallyIntegrable
        (shrinkingBump d n).hasCompactSupport_normed (shrinkingBump d n).contDiff_normed
        (shrinkingBump d n).nonneg_normed hu z a (hs.trans hKΩ)
        (fun w hw => hFf (hs hw))
  have hlim : F (α • x + β • y) ≤ α • F x + β • F y := by
    apply le_of_tendsto_of_tendsto (hG _) ((hG x).const_mul α |>.add ((hG y).const_mul β))
    filter_upwards [hconv] with n hn
    exact hn.2 (left_mem_segment ℝ x y) (right_mem_segment ℝ x y) hα hβ hαβ
  have hSF : EqOn F f S := fun z hz => hFf (Metric.self_subset_cthickening S hz)
  rw [hSF (left_mem_segment ℝ x y), hSF (right_mem_segment ℝ x y),
    hSF (show α • x + β • y ∈ S from ⟨α, β, hα, hβ, hαβ, rfl⟩)] at hlim
  exact hlim

/-- The second derivative of a smooth convex function is nonnegative in
every direction, using only convexity on the indicated open neighborhood. -/
theorem second_nonneg_of_convexOn {U : Set (Domain d)} (hU : IsOpen U)
    (F : Domain d → ℝ) (hF : ContDiff ℝ ∞ F) (hc : ConvexOn ℝ U F)
    (x : Domain d) (hx : x ∈ U) (a : Domain d) :
    0 ≤ fderiv ℝ (fun z => fderiv ℝ F z a) x a := by
  let p : ℝ →ᵃ[ℝ] Domain d := AffineMap.lineMap x (x + a)
  have hp (t : ℝ) : HasDerivAt p a t := by
    simpa [p] using (AffineMap.hasDerivAt_lineMap (a := x) (b := x + a) (x := t))
  have h1 (t : ℝ) : HasDerivAt (F ∘ p) (fderiv ℝ F (p t) a) t :=
    (hF.differentiable (by simp) (p t)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hH : ContDiff ℝ ∞ (fun z => fderiv ℝ F z a) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have h2 (t : ℝ) : HasDerivAt (fun s => fderiv ℝ F (p s) a)
      (fderiv ℝ (fun z => fderiv ℝ F z a) (p t) a) t :=
    (hH.differentiable (by simp) (p t)).hasFDerivAt.comp_hasDerivAt t (hp t)
  have hm := (hc.comp_affineMap p).monotoneOn_deriv
    (fun t _ => (h1 t).differentiableAt)
  have hm' : MonotoneOn (fun t => fderiv ℝ F (p t) a) (p ⁻¹' U) := by
    intro t ht s hs hts
    simpa only [(h1 t).deriv, (h1 s).deriv] using hm ht hs hts
  have hn := hm'.derivWithin_nonneg (x := 0)
  have hnhds : p ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    (hU.preimage (by fun_prop)).mem_nhds (by simpa [p] using hx)
  rw [derivWithin_of_mem_nhds hnhds, (h2 0).deriv] at hn
  simpa [p] using hn

open scoped Convolution in
/-- Forward analytic implication. Convolution against the reflected given
test is a smooth convex function near zero. Its second derivative at zero
is exactly the required distribution pairing. This avoids differentiating
the original continuous convex density or imposing boundary regularity. -/
theorem positive_hessian_of_convexOn (f : Domain d → ℝ)
    (hf : ContinuousOn f Ω) (hc : ConvexOn ℝ (Ω : Set (Domain d)) f) :
    ∀ a : Domain d, IsPositive (directionalSecond (functionDistribution (Ω := Ω) f) a) := by
  intro a
  apply (isPositive_iff _).mpr
  intro φ hφ
  obtain ⟨δ, hδ, hKΩ⟩ := φ.hasCompactSupport.exists_cthickening_subset_open
    Ω.isOpen φ.tsupport_subset
  let K := Metric.cthickening δ (tsupport φ)
  obtain ⟨F, hFc, _, hFf⟩ := exists_compact_localization f hf K
    φ.hasCompactSupport.cthickening hKΩ
  have hloc (z : Domain d) (hz : z ∈ Metric.ball (0 : Domain d) δ)
      (y : Domain d) (hy : y ∈ tsupport φ) : z + y ∈ K := by
    apply Metric.mem_cthickening_of_dist_le (z + y) y δ (tsupport φ) hy
    have hz' : ‖z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    simpa [dist_eq_norm] using hz'.le
  let ρ : Domain d → ℝ := fun y => φ (-y)
  have hρc : HasCompactSupport ρ := φ.hasCompactSupport.comp_homeomorph
    (Homeomorph.neg (Domain d))
  have hρ : ContDiff ℝ ∞ ρ := φ.contDiff.comp (by fun_prop)
  let G : Domain d → ℝ := F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ
  have hGs : ContDiff ℝ ∞ G := hρc.contDiff_convolution_right _ hFc.locallyIntegrable hρ
  have hGval (z : Domain d) : G z = ∫ y, F (z + y) * φ y := by
    dsimp only [G]
    rw [convolution_eq_swap, ← integral_neg_eq_self]
    simp [ρ]
  have hint (z : Domain d) : Integrable (fun y => F (z + y) * φ y) volume :=
    ((hFc.comp (by fun_prop)).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  have hconv : ConvexOn ℝ (Metric.ball (0 : Domain d) δ) G := by
    have hi : ConvexOn ℝ (Metric.ball (0 : Domain d) δ)
        (fun z => ∫ y, F (z + y) * φ y) := by
      apply integral_convexOn_of_integrand_ae (convex_ball _ _)
      · apply Eventually.of_forall
        intro y
        by_cases hy : y ∈ tsupport φ
        · have ht := (hc.translate_left y).subset
            (show Metric.ball (0 : Domain d) δ ⊆ (fun z => y + z) ⁻¹' (Ω : Set (Domain d)) from
              fun z hz => by
                change y + z ∈ Ω
                rw [add_comm]
                exact hKΩ (hloc z hz y hy)) (convex_ball _ _)
          have htF : ConvexOn ℝ (Metric.ball (0 : Domain d) δ) (fun z => F (z + y)) :=
            ht.congr (fun z hz => (hFf (hloc z hz y hy)).symm)
          simpa only [smul_eq_mul, mul_comm] using ConvexOn.smul (hφ y) htF
        · simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]
          exact convexOn_const _ (convex_ball _ _)
      · intro z _
        exact hint z
    exact hi.congr (fun z _ => (hGval z).symm)
  have hn := second_nonneg_of_convexOn Metric.isOpen_ball G hGs hconv
    0 (Metric.mem_ball_self hδ) a
  change 0 ≤ fderiv ℝ (fun z => fderiv ℝ
    (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) z a) 0 a at hn
  rw [fderiv_convolution_second F ρ hFc.locallyIntegrable hρc hρ a 0, convolution_def] at hn
  let Dφ := TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ a φ)
  have hval (y : Domain d) :
      fderiv ℝ (fun z => fderiv ℝ ρ z a) (0 - y) a = Dφ y := by
    rw [lineDeriv_twice_apply]
    simpa only [ρ, zero_sub, neg_neg] using
      fderiv_reflect_translate_second φ φ.contDiff 0 (0 - y) a
  change 0 ≤ ∫ y, F y * fderiv ℝ (fun z => fderiv ℝ ρ z a) (0 - y) a at hn
  simp_rw [hval] at hn
  rw [hessian_pairing d Ω f hf a φ]
  change 0 ≤ ∫ y, f y * Dφ y
  convert hn using 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  by_cases hy : y ∈ tsupport φ
  · rw [hFf (Metric.self_subset_cthickening (tsupport φ) hy)]
  · have hz : Dφ y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hyD
      have hts : tsupport Dφ ⊆ tsupport φ :=
        (tsupport_fderiv_apply_subset ℝ a).trans (tsupport_fderiv_apply_subset ℝ a)
      exact hy (hts hyD)
    rw [hz, mul_zero, mul_zero]

/-- The full source equivalence, with continuity only on the open convex
domain and including empty domains and dimension zero. -/
theorem convexity : Specs.ExpandedFA.PartIV.DistributionHessian.convexityType := by
  intro d Ω f hΩ hf
  exact ⟨positive_hessian_of_convexOn f hf, convexOn_of_positive_hessian f hΩ hf⟩

/-- The complete one-dimensional assertion, with a unique locally finite
Radon measure and no finite-total-mass restriction. -/
theorem one_dimensional_convexity :
    Specs.ExpandedFA.PartIV.DistributionHessian.oneDimensionalConvexityType := by
  intro Ω f hΩ hf
  exact (convexity 1 Ω f hΩ hf).trans
    (one_dimensional_bridge Ω (functionDistribution f))

end ExpandedFA.PartIV.DistributionHessian
