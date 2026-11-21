import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PoissonSummation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.PoissonSummation

noncomputable section
open MeasureTheory TopologicalSpace
open scoped FourierTransform

namespace P102.U3.PoissonSummation
open P102.Specs.U3

variable {d : ℕ}

/-- Dilation on the shared Euclidean model. -/
def dilation (T : ℝ) (hT : T ≠ 0) : Euclidean d ≃ₗ[ℝ] Euclidean d :=
  LinearEquiv.smulOfNeZero ℝ (Euclidean d) T hT

@[simp] theorem dilation_apply (T : ℝ) (hT : T ≠ 0) (x : Euclidean d) :
    dilation T hT x = T • x := rfl

@[simp] theorem dilation_symm_apply (T : ℝ) (hT : T ≠ 0) (x : Euclidean d) :
    (dilation T hT).symm x = T⁻¹ • x := rfl

/-- Pullback by a nonzero scalar preserves Schwartz functions. -/
def dilate (T : ℝ) (hT : T ≠ 0) (φ : Test d) : Test d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dilation T hT).toContinuousLinearEquiv φ

@[simp] theorem dilate_apply (T : ℝ) (hT : T ≠ 0) (φ : Test d) (x : Euclidean d) :
    dilate T hT φ x = φ (T • x) := rfl

/-- The volume Jacobian of scalar dilation, including dimension zero. -/
theorem dilation_det (T : ℝ) (hT : T ≠ 0) :
    LinearMap.det (dilation (d := d) T hT).toLinearMap = T ^ d := by
  have heq : (dilation (d := d) T hT).toLinearMap = T • LinearMap.id := by
    ext x; rfl
  rw [heq, LinearMap.det_smul]
  simp

/-- The adjoint of the inverse dilation is the inverse dilation. -/
theorem dilation_inverse_adjoint (T : ℝ) (hT : T ≠ 0) (x : Euclidean d) :
    (dilation T hT).symm.toLinearMap.adjoint x = T⁻¹ • x := by
  have heq : (dilation (d := d) T hT).symm.toLinearMap = T⁻¹ • LinearMap.id := by
    ext y; rfl
  simp [heq, map_smul]

/-- The exact Fourier scaling formula with the standard-volume Jacobian. -/
theorem fourier_dilate (T : ℝ) (hT : 0 < T) (φ : Test d) (ξ : Euclidean d) :
    fourierValue d (dilate T hT.ne' φ) ξ =
      ((T ^ d)⁻¹ : ℝ) • fourierValue d φ (T⁻¹ • ξ) := by
  have h := ExpandedFA.PartIV.FourierChange.fourier_comp_linearEquiv
    (dilation T hT.ne') (φ : Euclidean d → ℂ) ξ
  rw [dilation_det, dilation_inverse_adjoint, abs_of_pos (pow_pos hT d)] at h
  exact h

end P102.U3.PoissonSummation

namespace P102.U3.PoissonSummation
open P102.Specs.U3
variable {d : ℕ}

/-- A summable majorant on each compact set, indexed by ordinary integer vectors. -/
theorem spatial_majorant (T : ℝ) (hT : 0 < T) (φ : Test d)
    (K : Compacts (Euclidean d)) :
    ∃ b : (Fin d → ℤ) → ℝ, Summable b ∧
      ∀ k (x : Euclidean d), x ∈ K → ‖spatialTerm T φ k x‖ ≤ b k := by
  let g := dilate T hT.ne' φ
  let K' := K.map (fun x : Euclidean d => T⁻¹ • x) (by fun_prop)
  let e := SchwartzMap.PoissonSummation.Standard.equivIntVec (d := d)
  let b := fun k : Fin d → ℤ =>
    ‖(SchwartzMap.PoissonSummation.Standard.translate g (e k)).restrict K'‖
  refine ⟨b, ?_, ?_⟩
  · exact (SchwartzMap.PoissonSummation.Standard.summable_norm_translate_restrict g K').comp_injective
      e.injective
  · intro k x hx
    have hx' : T⁻¹ • x ∈ K' := ⟨x, hx, rfl⟩
    have h := ContinuousMap.norm_coe_le_norm
      ((SchwartzMap.PoissonSummation.Standard.translate g (e k)).restrict K')
      ⟨T⁻¹ • x, hx'⟩
    change ‖g (T⁻¹ • x + (e k : Euclidean d))‖ ≤ b k at h
    simpa [b, g, spatialTerm, SchwartzMap.PoissonSummation.Standard.translate,
      e, SchwartzMap.PoissonSummation.Standard.intVec, latticePoint,
      smul_add, smul_smul, hT.ne'] using h

/-- Absolute convergence of the periodization at every point. -/
theorem spatial_absolute (T : ℝ) (hT : 0 < T) (φ : Test d) (x : Euclidean d) :
    Summable (fun k : Fin d → ℤ => ‖spatialTerm T φ k x‖) := by
  obtain ⟨b, hb, hbound⟩ := spatial_majorant T hT φ ⟨{x}, isCompact_singleton⟩
  exact hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbound k x (Set.mem_singleton x))

/-- Compact uniform convergence of finite-subset partial sums. -/
theorem spatial_locally_uniform (T : ℝ) (hT : 0 < T) (φ : Test d) :
    TendstoLocallyUniformly
      (fun s : Finset (Fin d → ℤ) => fun x => ∑ k ∈ s, spatialTerm T φ k x)
      (fun x => ∑' k : Fin d → ℤ, spatialTerm T φ k x) Filter.atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨b, hb, hbound⟩ := spatial_majorant T hT φ ⟨K, hK⟩
  exact tendstoUniformlyOn_tsum hb hbound

/-- Absolute summability of the dual-lattice samples of the Fourier transform. -/
theorem fourier_samples_absolute (T : ℝ) (hT : 0 < T) (φ : Test d) :
    Summable (fun m : Fin d → ℤ => ‖fourierValue d φ (T⁻¹ • latticePoint m)‖) := by
  exact ExpandedFA.PartIV.PoissonSummation.summable_integerPoint
    (dilate T⁻¹ (inv_ne_zero hT.ne') (fourierValue d φ))

@[simp] theorem norm_fourierTerm (T : ℝ) (φ : Test d) (m : Fin d → ℤ) (x : Euclidean d) :
    ‖fourierTerm T φ m x‖ = ‖fourierValue d φ (T⁻¹ • latticePoint m)‖ := by
  rw [fourierTerm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Absolute convergence of the Fourier series at every point. -/
theorem fourier_absolute (T : ℝ) (hT : 0 < T) (φ : Test d) (x : Euclidean d) :
    Summable (fun m : Fin d → ℤ => ‖fourierTerm T φ m x‖) := by
  simpa only [norm_fourierTerm] using fourier_samples_absolute T hT φ

/-- The Fourier series converges uniformly on the whole Euclidean space. -/
theorem fourier_uniform (T : ℝ) (hT : 0 < T) (φ : Test d) :
    TendstoUniformly
      (fun s : Finset (Fin d → ℤ) => fun x => ∑ m ∈ s, fourierTerm T φ m x)
      (fun x => ∑' m : Fin d → ℤ, fourierTerm T φ m x) Filter.atTop := by
  exact tendstoUniformly_tsum (fourier_samples_absolute T hT φ)
    (fun m x => (norm_fourierTerm T φ m x).le)

/-- The library product-torus formula in the shared coordinate and Fourier conventions. -/
theorem unit_poisson (φ : Test d) (x : Euclidean d) :
    (∑' k : Fin d → ℤ, φ (x + latticePoint k)) =
      ∑' m : Fin d → ℤ, fourierTerm 1 φ m x := by
  have h := SchwartzMap.PoissonSummation.Standard.poissonSummation_standard φ x
  have he := (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := d)).tsum_eq
    (fun ℓ => φ (x + (ℓ : Euclidean d)))
  rw [← he] at h
  convert h using 1
  · rfl
  · apply tsum_congr
    intro m
    simp only [fourierTerm, inv_one, one_smul, div_one]
    congr 1
    congr 1
    rw [real_inner_comm]
    simp only [PiLp.inner_apply, RCLike.wInner, latticePoint,
      SchwartzMap.PoissonSummation.Standard.intVec, Pi.one_apply, one_smul]
    push_cast
    ring

/-- Scalar dilation of the dual-lattice summands, including their phases. -/
theorem fourierTerm_dilate (T : ℝ) (hT : 0 < T) (φ : Test d)
    (m : Fin d → ℤ) (x : Euclidean d) :
    fourierTerm 1 (dilate T hT.ne' φ) m (T⁻¹ • x) =
      ((T ^ d)⁻¹ : ℝ) • fourierTerm T φ m x := by
  simp only [fourierTerm, inv_one, one_smul, div_one]
  rw [fourier_dilate T hT, smul_mul_assoc]
  congr 2
  rw [inner_smul_right]
  push_cast
  ring

/-- Poisson summation on Tℤ^d, obtained from the product-torus formula by dilation. -/
theorem poisson_identity (T : ℝ) (hT : 0 < T) (φ : Test d) (x : Euclidean d) :
    (∑' k : Fin d → ℤ, spatialTerm T φ k x) =
      ((T ^ d)⁻¹ : ℝ) • (∑' m : Fin d → ℤ, fourierTerm T φ m x) := by
  calc
    (∑' k : Fin d → ℤ, spatialTerm T φ k x) =
        ∑' k : Fin d → ℤ, dilate T hT.ne' φ (T⁻¹ • x + latticePoint k) := by
      apply tsum_congr
      intro k
      simp [spatialTerm, smul_add, smul_smul, hT.ne']
    _ = ∑' m : Fin d → ℤ, fourierTerm 1 (dilate T hT.ne' φ) m (T⁻¹ • x) :=
      unit_poisson _ _
    _ = ∑' m : Fin d → ℤ, ((T ^ d)⁻¹ : ℝ) • fourierTerm T φ m x :=
      tsum_congr (fun m => fourierTerm_dilate T hT φ m x)
    _ = _ := tsum_const_smul'' _

/-- The complete cubical-lattice theorem, with all its convergence assertions. -/
theorem poisson_summation : P102.Specs.U3.PoissonSummation.poissonSummation_type := by
  intro d φ T hT
  exact ⟨spatial_absolute T hT φ, fourier_absolute T hT φ,
    spatial_locally_uniform T hT φ, (fourier_uniform T hT φ).tendstoLocallyUniformly,
    fourier_uniform T hT φ, poisson_identity T hT φ⟩

end P102.U3.PoissonSummation
