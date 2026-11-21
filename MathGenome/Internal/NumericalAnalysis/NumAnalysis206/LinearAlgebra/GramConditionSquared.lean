import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.GramConditionSquared
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.SvdPseudoinverse
import MathGenome.Internal.D05.M14.Penrose.Projections

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.GramConditionSquared
open MatrixDefinitions

abbrev conditionNumber : Specs.NumAnalysis206.GramConditionSquared.conditionNumber_type :=
  @MatrixConditionDefinitions.conditionNumber
abbrev squareConditionNumber : Specs.NumAnalysis206.GramConditionSquared.squareConditionNumber_type :=
  @MatrixConditionDefinitions.squareConditionNumber

/-- The largest singular coefficient of A⁺ is the reciprocal of the last
positive singular coefficient of A. Bessel gives the upper bound; the last
left singular vector attains it. -/
theorem pseudoinverse_norm {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (T : V →ₗ[ℝ] W) (hr : 0 < Module.finrank ℝ T.range) :
    ‖(D05.pseudoinverse T).toContinuousLinearMap‖ =
      (T.singularValues (Module.finrank ℝ T.range - 1))⁻¹ := by
  classical
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  let r := Module.finrank ℝ T.range
  let e := fun i : Fin r => d.domainBasis (Fin.castLE T.finrank_range_le i)
  let f := fun i : Fin r => d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)
  have he : D05.orthonormalFamily (F := ℝ) e :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib e).mpr
      (d.domainBasis.orthonormal.comp _ (Fin.castLE_injective _))
  have hf : D05.orthonormalFamily (F := ℝ) f :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib f).mpr
      (d.codomainBasis.orthonormal.comp _ (Fin.castLE_injective _))
  have hlast : r - 1 < r := by dsimp [r]; omega
  have hs : 0 < T.singularValues (r - 1) :=
    T.singularValues_pos_iff_lt_finrank_range.mpr hlast
  have hexp (w : W) : ‖D05.pseudoinverse T w‖ ^ 2 =
      ∑ i : Fin r, (T.singularValues i)⁻¹ ^ 2 * ‖D05.firstInner (F := ℝ) w (f i)‖ ^ 2 := by
    calc
      _ = ‖∑ i : Fin r,
          ((T.singularValues i)⁻¹ * D05.firstInner (F := ℝ) w (f i)) • e i‖ ^ 2 := by
        rw [D05.M14.SvdPseudoinverse.pseudoinverse_formula T d w]
        rfl
      _ = ∑ i : Fin r, ‖(T.singularValues i)⁻¹ * D05.firstInner (F := ℝ) w (f i)‖ ^ 2 :=
        D05.M12.FourierParseval.norm_sq_finite_sum e he Finset.univ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, norm_inv, Real.norm_eq_abs,
          abs_of_nonneg (T.singularValues_nonneg i), mul_pow]
  have hbound (w : W) : ‖D05.pseudoinverse T w‖ ≤ (T.singularValues (r - 1))⁻¹ * ‖w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg _))).mp
    rw [mul_pow, hexp]
    calc
      _ ≤ ∑ i : Fin r, (T.singularValues (r - 1))⁻¹ ^ 2 * ‖D05.firstInner (F := ℝ) w (f i)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply (sq_le_sq₀ (inv_nonneg.mpr (T.singularValues_nonneg i)) (inv_nonneg.mpr hs.le)).mpr
        have hi : (i : ℕ) ≤ r - 1 := by omega
        simpa only [one_div] using
          one_div_le_one_div_of_le hs (T.singularValues_antitone hi)
      _ = (T.singularValues (r - 1))⁻¹ ^ 2 * ∑ i : Fin r, ‖D05.firstInner (F := ℝ) w (f i)‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (D05.M12.FourierParseval.bessel_finite_family f hf w) (sq_nonneg _)
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hs.le) hbound
  · let j : Fin r := ⟨r - 1, hlast⟩
    have hact : D05.pseudoinverse T (f j) = (T.singularValues j)⁻¹ • e j := by
      rw [D05.M14.SvdPseudoinverse.pseudoinverse_formula T d]
      simp [f, e, D05.firstInner, orthonormal_iff_ite.mp d.codomainBasis.orthonormal]
    have hn : ‖D05.pseudoinverse T (f j)‖ = (T.singularValues (r - 1))⁻¹ := by
      rw [hact, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (T.singularValues_nonneg j), d.domainBasis.orthonormal.norm_eq_one, mul_one]
    have hb := (D05.pseudoinverse T).toContinuousLinearMap.le_opNorm (f j)
    have hfn : ‖f j‖ = 1 := d.codomainBasis.orthonormal.norm_eq_one _
    rw [hfn, mul_one] at hb
    simpa only [LinearMap.coe_toContinuousLinearMap', hn] using hb

/-- The C*-identity for the actual Euclidean operator norm. -/
theorem operatorNorm_adjoint_mul_self {m n : ℕ} (A : Mat ℝ m n) :
    operatorNorm (adjoint A * A) = operatorNorm A ^ 2 := by
  change ‖(adjoint A * A).toEuclideanLin.toContinuousLinearMap‖ =
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ^ 2
  rw [MatrixData.toEuclidean_mul, MatrixData.toEuclidean_adjoint]
  have hcomp : ((LinearMap.adjoint A.toEuclideanLin).comp A.toEuclideanLin).toContinuousLinearMap =
      (LinearMap.adjoint A.toEuclideanLin).toContinuousLinearMap.comp
        A.toEuclideanLin.toContinuousLinearMap := by ext x; rfl
  rw [hcomp, LinearMap.adjoint_toContinuousLinearMap,
    ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

/-- The inverse of the Gram matrix is A⁺(A⁺)* for full column rank. -/
theorem gram_inverse {m n : ℕ} (A : Mat ℝ m n) (hA : FullColumnRank A) :
    (adjoint A * A)⁻¹ = pseudoinverse A * adjoint (pseudoinverse A) := by
  have hinj := (MatrixData.fullColumnRank_iff_injective A).mp hA
  have hl : pseudoinverse A * A = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [MatrixData.toEuclidean_mul, MatrixData.pseudoinverse_transport]
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLpLin_one, LinearMap.id_apply]
    change D05.pseudoinverse A.toEuclideanLin (A.toEuclideanLin x) = x
    apply hinj
    exact LinearMap.congr_fun
      (D05.M14.Penrose.Projections.map_pseudoinverse_map A.toEuclideanLin) x
  have hs : adjoint (A * pseudoinverse A) = A * pseudoinverse A := by
    apply Matrix.toEuclideanLin.injective
    rw [MatrixData.toEuclidean_adjoint, MatrixData.toEuclidean_mul, MatrixData.pseudoinverse_transport]
    exact D05.M14.Penrose.Projections.map_comp_pseudoinverse_adjoint A.toEuclideanLin
  have hl' : adjoint A * adjoint (pseudoinverse A) = 1 := by
    simpa only [MatrixDefinitions.adjoint, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_one] using congrArg adjoint hl
  have hr : (adjoint A * A) * (pseudoinverse A * adjoint (pseudoinverse A)) = 1 := by
    calc
      _ = adjoint A * (A * pseudoinverse A) * adjoint (pseudoinverse A) := by
        simp only [Matrix.mul_assoc]
      _ = adjoint A * adjoint (A * pseudoinverse A) * adjoint (pseudoinverse A) := by rw [hs]
      _ = (adjoint A * adjoint (pseudoinverse A)) *
          (adjoint A * adjoint (pseudoinverse A)) := by
        simp only [MatrixDefinitions.adjoint, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hl', Matrix.one_mul]
  exact Matrix.inv_eq_right_inv hr

/-- The norm identity implies the squared condition formula, without selecting
an SVD or imposing a positive dimension. -/
theorem gram_square {m n : ℕ} (A : Mat ℝ m n) (hA : FullColumnRank A) :
    squareConditionNumber (adjoint A * A) = conditionNumber A ^ 2 := by
  change operatorNorm (adjoint A * A) * operatorNorm ((adjoint A * A)⁻¹) =
    (operatorNorm A * operatorNorm (pseudoinverse A)) ^ 2
  rw [operatorNorm_adjoint_mul_self, gram_inverse A hA]
  have hp := operatorNorm_adjoint_mul_self (adjoint (pseudoinverse A))
  change operatorNorm (pseudoinverse A * adjoint (pseudoinverse A)) =
    operatorNorm (adjoint (pseudoinverse A)) ^ 2 at hp
  rw [MatrixData.operatorNorm_adjoint (pseudoinverse A)] at hp
  rw [hp, mul_pow]

/-- W31: full column rank makes the last domain singular value positive;
the norm condition number is the ratio of the extreme singular values, and
passing to the Gram matrix squares it. -/
theorem gram_condition_squared : Specs.NumAnalysis206.GramConditionSquared.gram_condition_squared := by
  intro m n A hn hA
  have hinj := (MatrixData.fullColumnRank_iff_injective A).mp hA
  have hrank : Module.finrank ℝ A.toEuclideanLin.range = n :=
    (LinearMap.finrank_range_of_inj hinj).trans (finrank_euclideanSpace_fin (𝕜 := ℝ))
  have hpos : 0 < singularValue A n := by
    change 0 < A.toEuclideanLin.singularValues (n - 1)
    apply A.toEuclideanLin.singularValues_pos_iff_lt_finrank_range.mpr
    rw [hrank]
    omega
  have hmin : operatorNorm (pseudoinverse A) = (singularValue A n)⁻¹ := by
    change ‖(pseudoinverse A).toEuclideanLin.toContinuousLinearMap‖ =
      (A.toEuclideanLin.singularValues (n - 1))⁻¹
    rw [MatrixData.pseudoinverse_transport]
    have hr : 0 < Module.finrank ℝ A.toEuclideanLin.range := by rw [hrank]; exact hn
    simpa only [hrank] using pseudoinverse_norm A.toEuclideanLin hr
  have hmax : operatorNorm A = singularValue A 1 := by
    calc
      _ = D05.operatorNorm A.toEuclideanLin := MatrixData.operatorNorm_eq_D05 A
      _ = A.toEuclideanLin.singularValues 0 := D05.M14.OperatorNorm.eq_first_singularValue A.toEuclideanLin
      _ = _ := rfl
  refine ⟨hpos, ?_, gram_square A hA⟩
  change operatorNorm A * operatorNorm (pseudoinverse A) = _
  rw [hmax, hmin, div_eq_mul_inv]

end NumAnalysis206.GramConditionSquared
