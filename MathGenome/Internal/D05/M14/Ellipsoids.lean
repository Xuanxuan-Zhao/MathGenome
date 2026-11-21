import MathGenome.Internal.Specs.D05.M14.Ellipsoids
import MathGenome.Internal.D05.M14.Svd
import MathGenome.Internal.D05.M14.Svd.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! K05.14.ellipsoids. Parseval converts the SVD coordinate formula into
`energy (T v) = ‖v‖²`. Taking the explicit inverse preimage proves both set
equalities. Every positive-axis ellipsoid is first realized by a diagonal
linear equivalence; applying the ball theorem to its composite with T gives
the general image theorem. The real measure argument uses the independent
Haar-measure change-of-variables theorem and the full-list determinant bridge.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set
open D05.Ellipsoids

namespace D05.M14.Ellipsoids

section Geometry
variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
lemma repr_sum {n : ℕ} (b : OrthonormalBasis (Fin n) F V) (y : Fin n → F)
    (j : Fin n) : b.repr (∑ i, y i • b i) j = y j := by
  classical
  simp [Pi.single_apply]

omit [FiniteDimensional F V] in
lemma energy_sum {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) (y : Fin n → F) :
    energy b a (∑ i, y i • b i) = ∑ i, ‖y i‖ ^ 2 / a i ^ 2 := by
  simp only [energy, repr_sum]

end Geometry

theorem coordinate_description : Specs.D05.M14.Ellipsoids.coordinate_description := by
  intro F V _ _ _ _ n b a
  constructor
  · ext v
    constructor
    · intro hv
      exact ⟨fun i => b.repr v i, (b.sum_repr v).symm, hv⟩
    · rintro ⟨y, rfl, hy⟩
      simpa only [closedEllipsoid, mem_ofPred_eq, energy_sum] using hy
  · ext v
    constructor
    · intro hv
      exact ⟨fun i => b.repr v i, (b.sum_repr v).symm, hv⟩
    · rintro ⟨y, rfl, hy⟩
      simpa only [openEllipsoid, mem_ofPred_eq, energy_sum] using hy

theorem positive_axes : Specs.D05.M14.Ellipsoids.positive_axes := by
  intro F V _ _ _ _ T i
  apply (D05.M14.SingularValues.positive_iff T.toLinearMap i.val).mpr
  rw [LinearMap.finrank_range_of_inj T.injective]
  exact i.isLt

section Geometry
variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

lemma svd_action (T : V ≃ₗ[F] V) (d : D05.SingularValueDecomposition T.toLinearMap)
    (i : Fin (Module.finrank F V)) :
    T (d.domainBasis i) = (T.toLinearMap.singularValues i : F) • d.codomainBasis i := by
  have hr : Module.finrank F (LinearMap.range T.toLinearMap) = Module.finrank F V :=
    LinearMap.finrank_range_of_inj T.injective
  let k : Fin (Module.finrank F (LinearMap.range T.toLinearMap)) :=
    ⟨i.val, by rw [hr]; exact i.isLt⟩
  have h₁ : Fin.castLE T.toLinearMap.finrank_range_le k = i := Fin.ext rfl
  have h := d.positive_action k
  rw [h₁] at h
  exact h

lemma svd_coordinates (T : V ≃ₗ[F] V) (d : D05.SingularValueDecomposition T.toLinearMap)
    (v : V) (i : Fin (Module.finrank F V)) :
    d.codomainBasis.repr (T v) i =
      (T.toLinearMap.singularValues i : F) * d.domainBasis.repr v i := by
  classical
  conv_lhs => rw [← d.domainBasis.sum_repr v]
  simp [svd_action, RCLike.real_smul_eq_coe_mul, Pi.single_apply, mul_comm]

lemma energy_image (T : V ≃ₗ[F] V) (d : D05.SingularValueDecomposition T.toLinearMap)
    (v : V) :
    energy d.codomainBasis (fun i => T.toLinearMap.singularValues i) (T v) = ‖v‖ ^ 2 := by
  unfold energy
  calc
    _ = ∑ i : Fin (Module.finrank F V), ‖d.domainBasis.repr v i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [svd_coordinates, norm_mul, RCLike.norm_ofReal,
        abs_of_pos (positive_axes T i), mul_pow]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (ne_of_gt (positive_axes T i)))
    _ = ‖v‖ ^ 2 := by
      simpa only [OrthonormalBasis.repr_apply_apply] using
        d.domainBasis.sum_sq_norm_inner_right v

lemma sq_norm_le_one (v : V) : ‖v‖ ^ 2 ≤ 1 ↔ ‖v‖ ≤ 1 := by
  simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg v) (zero_le_one : (0 : ℝ) ≤ 1))

lemma sq_norm_lt_one (v : V) : ‖v‖ ^ 2 < 1 ↔ ‖v‖ < 1 := by
  simpa only [one_pow] using (sq_lt_sq₀ (norm_nonneg v) (zero_le_one : (0 : ℝ) ≤ 1))

omit [FiniteDimensional F V] in
lemma ball_images_of_energy {n : ℕ} (T : V ≃ₗ[F] V)
    (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ)
    (h : ∀ v, energy b a (T v) = ‖v‖ ^ 2) :
    T '' {v : V | ‖v‖ ≤ 1} = closedEllipsoid b a ∧
    T '' {v : V | ‖v‖ < 1} = openEllipsoid b a := by
  constructor
  · ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change energy b a (T v) ≤ 1
      rw [h]
      exact (sq_norm_le_one v).mpr hv
    · intro hw
      refine ⟨T.symm w, ?_, T.apply_symm_apply w⟩
      apply (sq_norm_le_one _).mp
      rw [← h, T.apply_symm_apply]
      exact hw
  · ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change energy b a (T v) < 1
      rw [h]
      exact (sq_norm_lt_one v).mpr hv
    · intro hw
      refine ⟨T.symm w, ?_, T.apply_symm_apply w⟩
      apply (sq_norm_lt_one _).mp
      rw [← h, T.apply_symm_apply]
      exact hw

end Geometry

theorem svd_ball_images : Specs.D05.M14.Ellipsoids.svd_ball_images := by
  intro F V _ _ _ _ T d
  exact ball_images_of_energy T _ _ (energy_image T d)

theorem exists_ball_images : Specs.D05.M14.Ellipsoids.exists_ball_images := by
  intro F V _ _ _ _ T
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T.toLinearMap
  exact ⟨d, positive_axes T, svd_ball_images T d⟩

theorem bijective_ball_images : Specs.D05.M14.Ellipsoids.bijective_ball_images := by
  intro F V _ _ _ _ T hT
  exact exists_ball_images (LinearEquiv.ofBijective T hT)

section Geometry
variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

/-- The positive diagonal map is an equivalence by coordinatewise inversion. -/
def diagonalEquiv {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) : V ≃ₗ[F] V :=
  b.toBasis.equivFun.trans ((LinearEquiv.piCongrRight fun i =>
    LinearEquiv.smulOfNeZero F F (a i : F) (by exact_mod_cast ne_of_gt (ha i))).trans
      b.toBasis.equivFun.symm)

omit [FiniteDimensional F V] in
lemma diagonal_coordinates {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (v : V) (i : Fin n) :
    b.repr (diagonalEquiv b a ha v) i = (a i : F) * b.repr v i := by
  change b.toBasis.equivFun (diagonalEquiv b a ha v) i =
    (a i : F) * b.toBasis.equivFun v i
  simp [diagonalEquiv, LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit,
    smul_eq_mul]

omit [FiniteDimensional F V] in
lemma diagonal_action {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (i : Fin n) :
    diagonalEquiv b a ha (b i) = (a i : F) • b i := by
  classical
  apply b.repr.injective
  ext j
  rw [diagonal_coordinates]
  by_cases h : i = j <;> simp [h, RCLike.real_smul_eq_coe_mul]

omit [FiniteDimensional F V] in
lemma diagonal_energy {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (v : V) :
    energy b a (diagonalEquiv b a ha v) = ‖v‖ ^ 2 := by
  unfold energy
  calc
    _ = ∑ i : Fin n, ‖b.repr v i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [diagonal_coordinates, norm_mul, RCLike.norm_ofReal, abs_of_pos (ha i), mul_pow]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (ne_of_gt (ha i)))
    _ = ‖v‖ ^ 2 := by
      simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_norm_inner_right v

end Geometry

theorem diagonal_realization : Specs.D05.M14.Ellipsoids.diagonal_realization := by
  intro F V _ _ _ _ n b a ha
  exact ⟨diagonalEquiv b a ha, diagonal_action b a ha,
    ball_images_of_energy _ b a (diagonal_energy b a ha)⟩

theorem image_ellipsoid : Specs.D05.M14.Ellipsoids.image_ellipsoid := by
  intro F V _ _ _ _ T n b a ha
  obtain ⟨S, _, hSc, hSo⟩ := diagonal_realization b a ha
  obtain ⟨d, hp, hTc, hTo⟩ := exists_ball_images (S.trans T)
  refine ⟨d.codomainBasis, fun i => (S.trans T).toLinearMap.singularValues i, hp, ?_, ?_⟩
  · rw [← hSc, image_image]
    exact hTc
  · rw [← hSo, image_image]
    exact hTo

theorem translated_image : Specs.D05.M14.Ellipsoids.translated_image := by
  intro F V _ _ _ _ T c E
  simp only [image_image, map_add]

theorem translated_ellipsoid : Specs.D05.M14.Ellipsoids.translated_ellipsoid := by
  intro F V _ _ _ _ T c n b a ha
  obtain ⟨f, s, hp, hc, ho⟩ := image_ellipsoid T b a ha
  refine ⟨f, s, hp, ?_, ?_⟩
  · rw [translated_image T c _, hc]
  · rw [translated_image T c _, ho]

section Geometry
variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

omit [FiniteDimensional F V] in
lemma energy_axis {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) (i : Fin n) (z : F) :
    energy b a (z • b i) = ‖z‖ ^ 2 / a i ^ 2 := by
  classical
  simp [energy, apply_ite, ite_pow, ite_div]

omit [FiniteDimensional F V] in
lemma continuous_energy {n : ℕ} (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ) :
    Continuous (energy b a) := by
  unfold energy
  apply continuous_finsetSum
  intro i _
  have hc : Continuous (fun v : V => b.repr v i) := by
    simp only [OrthonormalBasis.repr_apply_apply]
    exact continuous_const.inner continuous_id
  exact (hc.norm.pow 2).div_const _

end Geometry

theorem axis_sections : Specs.D05.M14.Ellipsoids.axis_sections := by
  intro F V _ _ _ _ n b a ha i z
  change (energy b a (z • b i) ≤ 1 ↔ ‖z‖ ≤ a i) ∧
    (energy b a (z • b i) < 1 ↔ ‖z‖ < a i)
  rw [energy_axis, div_le_one₀ (sq_pos_of_pos (ha i)), div_lt_one₀ (sq_pos_of_pos (ha i))]
  exact ⟨sq_le_sq₀ (norm_nonneg z) (le_of_lt (ha i)),
    sq_lt_sq₀ (norm_nonneg z) (le_of_lt (ha i))⟩

theorem ellipsoid_topology : Specs.D05.M14.Ellipsoids.ellipsoid_topology := by
  intro F V _ _ _ _ n b a
  exact ⟨isClosed_le (continuous_energy b a) continuous_const,
    isOpen_lt (continuous_energy b a) continuous_const⟩

theorem real_volume_scaling : Specs.D05.M14.Ellipsoids.real_volume_scaling := by
  intro V _ _ _ _ _ T E hE
  have hd : (D05.singularValues T.toLinearMap).prod = |T.toLinearMap.det| := by
    simpa only [Real.norm_eq_abs] using
      (D05.M14.Svd.Determinant.norm_det_eq_prod T.toLinearMap).symm
  refine ⟨?_, ?_, hd⟩
  · have hi : T '' E = T.symm ⁻¹' E := T.toEquiv.image_eq_preimage_symm E
    rw [hi]
    exact hE.preimage (MeasureTheory.Measure.LinearMap.quasiMeasurePreserving volume
      T.symm.toLinearMap T.symm.isUnit_det'.ne_zero)
  · change volume (T.toLinearMap '' E) = _
    rw [hd]
    exact Measure.addHaar_image_linearMap volume T.toLinearMap E

theorem real_ball_volumes : Specs.D05.M14.Ellipsoids.real_ball_volumes := by
  intro V _ _ _ _ _ T
  have hc : IsClosed {v : V | ‖v‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  have ho : IsOpen {v : V | ‖v‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hTc := (T.toContinuousLinearEquiv.toHomeomorph.isClosedMap _ hc).measurableSet
  have hTo := (T.toContinuousLinearEquiv.toHomeomorph.isOpenMap _ ho).measurableSet
  exact ⟨hc.measurableSet, ho.measurableSet, hTc, hTo,
    (real_volume_scaling T _ hc.measurableSet.nullMeasurableSet).2.1,
    (real_volume_scaling T _ ho.measurableSet.nullMeasurableSet).2.1⟩

theorem zero_dimension : Specs.D05.M14.Ellipsoids.zero_dimension := by
  intro F V _ _ _ _ hn T b a
  have : Subsingleton V := Module.finrank_zero_iff.mp hn
  have hz : ∀ v : V, v = 0 := fun v => Subsingleton.elim _ _
  have he : ∀ v : V, energy b a v = 0 := by
    intro v
    unfold energy
    have : IsEmpty (Fin (Module.finrank F V)) := by rw [hn]; infer_instance
    exact Finset.sum_eq_zero fun i _ => isEmptyElim i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext v
    simp [hz v]
  · ext v
    simp [hz v]
  · ext v
    simp [closedEllipsoid, he, hz v]
  · ext v
    simp [openEllipsoid, he, hz v]
  · rw [(D05.M14.SingularValues.empty_domain T.toLinearMap hn).1]
    rfl

theorem zero_real_volume : Specs.D05.M14.Ellipsoids.zero_real_volume := by
  intro V _ _ _ _ _ hn
  have : Subsingleton V := Module.finrank_zero_iff.mp hn
  let b := stdOrthonormalBasis ℝ V
  have hp : parallelepiped b = ({0} : Set V) := by
    ext v
    have hv : v = 0 := Subsingleton.elim _ _
    simp only [hv, mem_singleton_iff, iff_true]
    rw [mem_parallelepiped_iff]
    exact ⟨0, by simp, by simp⟩
  have hvol : (volume : Measure V).completion ({0} : Set V) = 1 := by
    change volume ({0} : Set V) = 1
    rw [← hp]
    exact b.volume_parallelepiped
  refine ⟨hvol, ?_, ?_⟩
  · have hball : {v : V | ‖v‖ ≤ 1} = ({0} : Set V) := by
      ext v
      simp [show v = 0 from Subsingleton.elim _ _]
    change volume {v : V | ‖v‖ ≤ 1} = 1
    rw [hball]
    exact hvol
  · have hball : {v : V | ‖v‖ < 1} = ({0} : Set V) := by
      ext v
      simp [show v = 0 from Subsingleton.elim _ _]
    change volume {v : V | ‖v‖ < 1} = 1
    rw [hball]
    exact hvol

end D05.M14.Ellipsoids
