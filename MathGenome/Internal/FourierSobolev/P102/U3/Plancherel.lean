import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Plancherel
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

namespace P102.U3.Plancherel
variable (V H : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The shared canonical Plancherel transform, reusing Mathlib's extension. -/
def fourierL2 : Lp (α := V) H 2 volume ≃ₗᵢ[ℂ] Lp (α := V) H 2 volume :=
  Lp.fourierTransformₗᵢ V H

theorem schwartz_extension : P102.Specs.U3.Plancherel.schwartzExtension_type V H := by
  intro f
  exact ⟨SchwartzMap.toLp_fourier_eq f, SchwartzMap.toLp_fourierInv_eq f⟩

theorem inner_preservation : P102.Specs.U3.Plancherel.innerPreservation_type V H := by
  intro f g
  exact (fourierL2 V H).inner_map_map f g

variable {V H}

/-- Fubini transposition for a scalar Schwartz test and an H-valued L¹ input. -/
theorem integral_fourier_smul (φ : SchwartzMap V ℂ) (f : V → H) (hf : Integrable f) :
    (∫ x, (𝓕 φ) x • f x) = ∫ x, φ x • 𝓕 f x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ V) Real.continuous_fourierChar continuous_inner φ.integrable hf)

/-- The L² and integral transforms have identical compact smooth test pairings.
This proves compatibility without countability assumptions on H. -/
theorem fourier_ae_integral (f : Lp (α := V) H 2 volume) (hf : Integrable (f : V → H)) :
    (𝓕 f : Lp (α := V) H 2 volume) =ᵐ[volume] 𝓕 (f : V → H) := by
  have hc : Continuous (𝓕 (f : V → H)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 f : Lp (α := V) H 2 volume)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hgc
  let φ : SchwartzMap V ℂ :=
    SchwartzMap.postcompCLM Complex.ofRealCLM (hgc.toSchwartzMap hg)
  have hφ (x : V) : φ x = (g x : ℂ) := rfl
  have heq := congrArg (fun T : TemperedDistribution V H => T φ)
    (Lp.fourier_toTemperedDistribution_eq f)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at heq
  calc
    (∫ x, g x • (𝓕 f : Lp (α := V) H 2 volume) x)
        = ∫ x, φ x • (𝓕 f : Lp (α := V) H 2 volume) x := by
          simp only [hφ, Complex.coe_smul]
    _ = ∫ x, (𝓕 φ) x • f x := heq.symm
    _ = ∫ x, φ x • 𝓕 (f : V → H) x := integral_fourier_smul φ _ hf
    _ = ∫ x, g x • 𝓕 (f : V → H) x := by
      simp only [hφ, Complex.coe_smul]

theorem integral_compatibility :
    P102.Specs.U3.Plancherel.integralCompatibility_type V H := by
  intro f hf h1
  have h1' : Integrable (hf.toLp : V → H) := h1.congr hf.coeFn_toLp.symm
  exact (fourier_ae_integral hf.toLp h1').trans
    (Filter.Eventually.of_forall (Real.fourier_congr_ae hf.coeFn_toLp))

/-- Positive-sign Fubini transposition. -/
theorem integral_fourierInv_smul (φ : SchwartzMap V ℂ) (f : V → H) (hf : Integrable f) :
    (∫ x, (𝓕⁻ φ) x • f x) = ∫ x, φ x • 𝓕⁻ f x := by
  have hflip : (-innerₗ V).flip = -innerₗ V := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (L := -innerₗ V) Real.continuous_fourierChar continuous_inner.neg φ.integrable hf
  rw [hflip] at h
  rw [SchwartzMap.fourierInv_coe]
  exact h

/-- Almost-everywhere compatibility for the positive-sign inverse. -/
theorem fourierInv_ae_integral (f : Lp (α := V) H 2 volume)
    (hf : Integrable (f : V → H)) :
    (𝓕⁻ f : Lp (α := V) H 2 volume) =ᵐ[volume] 𝓕⁻ (f : V → H) := by
  have hc : Continuous (𝓕⁻ (f : V → H)) := by
    have hF : Continuous (𝓕 (f : V → H)) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf
    have heq : 𝓕⁻ (f : V → H) = fun x => 𝓕 (f : V → H) (-x) :=
      funext (Real.fourierInv_eq_fourier_neg _)
    rw [heq]
    exact hF.comp continuous_neg
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ f : Lp (α := V) H 2 volume)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hgc
  let φ : SchwartzMap V ℂ :=
    SchwartzMap.postcompCLM Complex.ofRealCLM (hgc.toSchwartzMap hg)
  have hφ (x : V) : φ x = (g x : ℂ) := rfl
  have heq := congrArg (fun T : TemperedDistribution V H => T φ)
    (Lp.fourierInv_toTemperedDistribution_eq f)
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at heq
  calc
    (∫ x, g x • (𝓕⁻ f : Lp (α := V) H 2 volume) x)
        = ∫ x, φ x • (𝓕⁻ f : Lp (α := V) H 2 volume) x := by
          simp only [hφ, Complex.coe_smul]
    _ = ∫ x, (𝓕⁻ φ) x • f x := heq.symm
    _ = ∫ x, φ x • 𝓕⁻ (f : V → H) x := integral_fourierInv_smul φ _ hf
    _ = ∫ x, g x • 𝓕⁻ (f : V → H) x := by
      simp only [hφ, Complex.coe_smul]

theorem inverse_compatibility :
    P102.Specs.U3.Plancherel.inverseCompatibility_type V H := by
  refine ⟨fun _ => rfl, ?_⟩
  intro f hf h1
  have h1' : Integrable (hf.toLp : V → H) := h1.congr hf.coeFn_toLp.symm
  exact (fourierInv_ae_integral hf.toLp h1').trans
    (Filter.Eventually.of_forall (Real.fourierInv_congr_ae hf.coeFn_toLp))

/-- The rank-one Schwartz classes; their algebraic span consists of finite-rank
Schwartz inputs. -/
def rankOneClasses : Set (Lp (α := V) H 2 volume) :=
  {f | ∃ (φ : SchwartzMap V ℂ) (h : H),
    f = (P102.Specs.U3.Plancherel.tensor V H φ h).toLp 2}

/-- Finite-rank Schwartz classes are dense even for a nonseparable Hilbert target.
An orthogonal vector has zero compact smooth vector-valued test integrals, hence
vanishes a.e. The test-integral uniqueness theorem handles strong measurability
without interchanging an uncountable family of null sets. -/
theorem dense_rankOne_span :
    Dense (Submodule.span ℂ (rankOneClasses (V := V) (H := H)) :
      Set (Lp (α := V) H 2 volume)) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hloc := (Lp.memLp f).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
  intro g hg hgc
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℂ
    (fun x => g x • f x)
    (hloc.integrable_smul_left_of_hasCompactSupport hg.continuous hgc)
  intro h
  let φ : SchwartzMap V ℂ :=
    SchwartzMap.postcompCLM Complex.ofRealCLM (hgc.toSchwartzMap hg)
  let ψ := P102.Specs.U3.Plancherel.tensor V H φ h
  have hψ : ψ.toLp 2 volume ∈ Submodule.span ℂ (rankOneClasses (V := V) (H := H)) :=
    Submodule.subset_span ⟨φ, h, rfl⟩
  have hz := (Submodule.mem_orthogonal _ f).mp hf _ hψ
  rw [L2.inner_def] at hz
  convert hz using 1
  apply integral_congr_ae
  filter_upwards [ψ.coeFn_toLp 2] with x hx
  rw [hx]
  change ⟪h, g x • f x⟫ = ⟪(g x : ℂ) • h, f x⟫
  simp only [Complex.coe_smul, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

/-- Agreement on rank-one inputs determines the continuous extension uniquely. -/
theorem uniqueness : P102.Specs.U3.Plancherel.uniqueness_type V H := by
  intro A hA
  have heq : A.toContinuousLinearEquiv.toContinuousLinearMap =
      (fourierL2 V H).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on dense_rankOne_span
    rintro f ⟨φ, h, rfl⟩
    exact (hA φ h).trans (SchwartzMap.toLp_fourier_eq _).symm
  apply LinearIsometryEquiv.ext
  intro f
  exact congrArg (fun T : Lp (α := V) H 2 volume →L[ℂ] Lp (α := V) H 2 volume => T f) heq

end P102.U3.Plancherel
