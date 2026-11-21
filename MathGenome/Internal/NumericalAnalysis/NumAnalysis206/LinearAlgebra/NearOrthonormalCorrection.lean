import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.NearOrthonormalCorrection
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.NearOrthonormalCorrection

/-- Scalar estimate for the positive square root on the Gram spectrum. -/
theorem sqrt_sub_one_bound {η μ : ℝ} (_hη0 : 0 ≤ η) (hη1 : η < 1)
    (hμ : |μ - 1| ≤ η) :
    0 < Real.sqrt μ ∧
      |Real.sqrt μ - 1| ≤ η / (1 + Real.sqrt (1 - η)) := by
  have hlow : 1 - η ≤ μ := by have := (abs_le.mp hμ).1; linarith
  have hpos : 0 < μ := by linarith
  have hs := Real.sq_sqrt hpos.le
  have ht := Real.sqrt_nonneg (1 - η)
  have hst : Real.sqrt (1 - η) ≤ Real.sqrt μ := Real.sqrt_le_sqrt hlow
  have hd : 0 < 1 + Real.sqrt (1 - η) := by positivity
  refine ⟨Real.sqrt_pos.mpr hpos, (le_div_iff₀ hd).mpr ?_⟩
  rcases le_total (Real.sqrt μ) 1 with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := (abs_le.mp hμ).1
    have hp := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hst)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := (abs_le.mp hμ).2
    have hp := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hst)
    nlinarith

/-- A diagonal map between orthonormal families has the expected norm bound. -/
theorem norm_le_of_basis_action {K E F ι : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E]
    [NormedAddCommGroup F] [InnerProductSpace K F] [Fintype ι]
    (e : OrthonormalBasis ι K E) (f : ι → F) (hf : Orthonormal K f)
    (L : E →ₗ[K] F) (c : ι → K) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ i, L (e i) = c i • f i) (hc : ∀ i, ‖c i‖ ≤ C) (x : E) :
    ‖L x‖ ≤ C * ‖x‖ := by
  classical
  have hexp : L x = ∑ i, (e.repr x i * c i) • f i := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, hL, smul_smul]
  have hnorm : ‖L x‖ ^ 2 = ∑ i, ‖e.repr x i * c i‖ ^ 2 := by
    rw [hexp, InnerProductSpace.norm_sq_eq_re_inner (𝕜 := K), hf.inner_sum,
      map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  rw [hnorm, mul_pow]
  calc
    ∑ i, ‖e.repr x i * c i‖ ^ 2
        ≤ ∑ i, C ^ 2 * ‖e.repr x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hc i)) (sq_nonneg _)
    _ = C ^ 2 * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, e.repr.norm_map]

/-- Normalizing the images of a Gram eigenbasis constructs an isometry.
No positive-dimensional-space hypothesis is needed. -/
theorem exists_isometry_of_gram_defect {K E F : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    [NormedAddCommGroup F] [InnerProductSpace K F] [FiniteDimensional K F]
    (T : E →ₗ[K] F) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hdef : ‖(T.adjoint.comp T - LinearMap.id).toContinuousLinearMap‖ ≤ η) :
    ∃ U : E →ₗᵢ[K] F,
      ‖(T - U.toLinearMap).toContinuousLinearMap‖ ≤
        η / (1 + Real.sqrt (1 - η)) := by
  classical
  let G : E →ₗ[K] E := T.adjoint.comp T
  have hG : G.IsSymmetric := T.isSymmetric_adjoint_comp_self
  let e := hG.eigenvectorBasis rfl
  let μ := hG.eigenvalues rfl
  have he : ∀ i, T.adjoint (T (e i)) = (μ i : K) • e i := by
    intro i
    exact hG.apply_eigenvectorBasis rfl i
  have hμ : ∀ i, |μ i - 1| ≤ η := by
    intro i
    have ha : (G - (LinearMap.id : E →ₗ[K] E)) (e i) = ((μ i - 1 : ℝ) : K) • e i := by
      simp only [LinearMap.sub_apply, LinearMap.id_apply]
      rw [show G (e i) = (μ i : K) • e i from he i,
        RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
    have hb := (G - (LinearMap.id : E →ₗ[K] E)).toContinuousLinearMap.le_opNorm (e i)
    change ‖(G - (LinearMap.id : E →ₗ[K] E)) (e i)‖ ≤ _ at hb
    rw [ha, norm_smul, RCLike.norm_ofReal, e.orthonormal.norm_eq_one, mul_one,
      mul_one] at hb
    exact hb.trans hdef
  let s := fun i => Real.sqrt (μ i)
  have hs : ∀ i, 0 < s i := fun i => (sqrt_sub_one_bound hη0 hη1 (hμ i)).1
  have hsq : ∀ i, s i ^ 2 = μ i := by
    intro i
    apply Real.sq_sqrt
    have := (abs_le.mp (hμ i)).1
    linarith
  let f := fun i => (s i : K)⁻¹ • T (e i)
  have hf : Orthonormal K f := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : inner K (T (e i)) (T (e j)) =
        (μ j : K) * (if i = j then 1 else 0) := by
      rw [← LinearMap.adjoint_inner_right, he, inner_smul_right, e.inner_eq_ite]
    simp only [f, inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_ofReal]
    rw [hij]
    by_cases h : i = j
    · subst j
      have hn : (s i : K) ≠ 0 := by exact_mod_cast (hs i).ne'
      rw [← hsq i]
      simp only [ite_true, mul_one, RCLike.ofReal_pow]
      field_simp
    · simp [h]
  let L := e.toBasis.constr K f
  have hL : ∀ i, L (e i) = f i := fun i => e.toBasis.constr_basis K f i
  have hLf : Orthonormal K (L ∘ e.toBasis) := by
    simpa only [Function.comp_def, OrthonormalBasis.coe_toBasis, hL] using hf
  let U := L.isometryOfOrthonormal e.orthonormal hLf
  refine ⟨U, ?_⟩
  let C := η / (1 + Real.sqrt (1 - η))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hTf : ∀ i, T (e i) = (s i : K) • f i := by
    intro i
    dsimp only [f]
    rw [smul_smul, mul_inv_cancel₀, one_smul]
    exact_mod_cast (hs i).ne'
  apply norm_le_of_basis_action e f hf (T - U.toLinearMap)
    (fun i => ((s i - 1 : ℝ) : K)) C hC ?_ ?_ x
  · intro i
    change T (e i) - L (e i) = _
    rw [hL, hTf, RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
  · intro i
    rw [RCLike.norm_ofReal]
    exact (sqrt_sub_one_bound hη0 hη1 (hμ i)).2

/-- The orthonormal correction in the proof of W33, over either real or
complex scalars, including the empty-column case. -/
theorem exists_correction :
    Specs.NumAnalysis206.NearOrthonormalCorrection.exists_correction := by
  intro K _ m n Qhat _ η hη0 hη1 hdef
  have htransport :
      (MatrixDefinitions.adjoint Qhat * Qhat - 1).toEuclideanLin =
        Qhat.toEuclideanLin.adjoint.comp Qhat.toEuclideanLin - LinearMap.id := by
    rw [map_sub, MatrixData.toEuclidean_mul, MatrixData.toEuclidean_adjoint,
      Matrix.toLpLin_one]
  change ‖(MatrixDefinitions.adjoint Qhat * Qhat - 1).toEuclideanLin.toContinuousLinearMap‖
    ≤ η at hdef
  rw [htransport] at hdef
  obtain ⟨U, hU⟩ := exists_isometry_of_gram_defect Qhat.toEuclideanLin η hη0 hη1 hdef
  let Qtilde : MatrixDefinitions.Mat K m n := Matrix.toEuclideanLin.symm U.toLinearMap
  have hQt : Qtilde.toEuclideanLin = U.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  refine ⟨Qtilde, ?_, ?_⟩
  · apply Matrix.toEuclideanLin.injective
    rw [MatrixData.toEuclidean_mul, MatrixData.toEuclidean_adjoint, hQt,
      Matrix.toLpLin_one]
    exact U.adjoint_comp_self'
  · change ‖(Qhat - Qtilde).toEuclideanLin.toContinuousLinearMap‖ ≤ _
    rwa [map_sub, hQt]

end NumAnalysis206.NearOrthonormalCorrection
