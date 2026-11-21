import MathGenome.Internal.Specs.D05.M14.OperatorNorm.SvdBound
import MathGenome.Internal.D05.M14.Svd
import MathGenome.Internal.D05.M12.FourierParseval

/-! The SVD squared-coefficient estimate and the closed-ball supremum.
The proof uses only finite orthonormal sums and Bessel's inequality. -/

noncomputable section
namespace D05.M14.OperatorNorm.SvdBound
open scoped BigOperators

theorem norm_sq_expansion : Specs.D05.M14.OperatorNorm.SvdBound.norm_sq_expansion := by
  intro F V W _ _ _ _ _ _ _ T d v
  classical
  let f := fun i : Fin (Module.finrank F (LinearMap.range T)) =>
    d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)
  have hf : D05.orthonormalFamily (F := F) f :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib f).mpr
      (d.codomainBasis.orthonormal.comp _ (Fin.castLE_injective _))
  calc
    ‖T v‖ ^ 2 = ‖∑ i : Fin (Module.finrank F (LinearMap.range T)),
        ((T.singularValues i : F) *
          D05.firstInner v (d.domainBasis (Fin.castLE T.finrank_range_le i))) • f i‖ ^ 2 := by
      rw [D05.M14.Svd.expansion T d v]
    _ = ∑ i : Fin (Module.finrank F (LinearMap.range T)),
        ‖(T.singularValues i : F) *
          D05.firstInner v (d.domainBasis (Fin.castLE T.finrank_range_le i))‖ ^ 2 :=
      D05.M12.FourierParseval.norm_sq_finite_sum f hf Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (T.singularValues_nonneg i), mul_pow]

theorem norm_sq_le : Specs.D05.M14.OperatorNorm.SvdBound.norm_sq_le := by
  intro F V W _ _ _ _ _ _ _ T d v
  classical
  let e := fun i : Fin (Module.finrank F (LinearMap.range T)) =>
    d.domainBasis (Fin.castLE T.finrank_range_le i)
  have he : D05.orthonormalFamily (F := F) e :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib e).mpr
      (d.domainBasis.orthonormal.comp _ (Fin.castLE_injective _))
  calc
    ‖T v‖ ^ 2 = ∑ i : Fin (Module.finrank F (LinearMap.range T)),
        T.singularValues i ^ 2 * ‖D05.firstInner (F := F) v (e i)‖ ^ 2 :=
      norm_sq_expansion T d v
    _ ≤ ∑ i : Fin (Module.finrank F (LinearMap.range T)),
        T.singularValues 0 ^ 2 * ‖D05.firstInner (F := F) v (e i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact (sq_le_sq₀ (T.singularValues_nonneg i) (T.singularValues_nonneg 0)).mpr
        (T.singularValues_antitone (Nat.zero_le _))
    _ = T.singularValues 0 ^ 2 *
        ∑ i : Fin (Module.finrank F (LinearMap.range T)),
          ‖D05.firstInner (F := F) v (e i)‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ T.singularValues 0 ^ 2 * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (D05.M12.FourierParseval.bessel_finite_family e he v) (sq_nonneg _)

theorem norm_le : Specs.D05.M14.OperatorNorm.SvdBound.norm_le := by
  intro F V W _ _ _ _ _ _ _ T v
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (T.singularValues_nonneg 0)
    (norm_nonneg v))).mp
  rw [mul_pow]
  exact norm_sq_le T d v

theorem attains_first : Specs.D05.M14.OperatorNorm.SvdBound.attains_first := by
  intro F V W _ _ _ _ _ _ _ T d hr
  dsimp only
  have he := d.domainBasis.orthonormal.norm_eq_one
    (Fin.castLE T.finrank_range_le ⟨0, hr⟩)
  have hf := d.codomainBasis.orthonormal.norm_eq_one
    (Fin.castLE (Submodule.finrank_le _) ⟨0, hr⟩)
  have hT : ‖T (d.domainBasis (Fin.castLE T.finrank_range_le ⟨0, hr⟩))‖ =
      T.singularValues 0 := by
    rw [d.positive_action ⟨0, hr⟩, norm_smul, hf, mul_one, RCLike.norm_ofReal,
      abs_of_nonneg (T.singularValues_nonneg 0)]
  exact ⟨he, hT, by rw [hT, he, one_pow, mul_one]⟩

theorem rank_zero_outputs : Specs.D05.M14.OperatorNorm.SvdBound.rank_zero_outputs := by
  intro F V W _ _ _ _ _ _ _ T
  constructor
  · intro hr
    have hT : T = 0 := by
      rwa [← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero]
    exact ⟨hT, fun v => by rw [hT]; rfl⟩
  · rintro ⟨rfl, h⟩
    simp

/-- Every image norm on the closed unit ball is at most the first singular
value, using the zero-padded sequence also when the rank is zero. -/
private theorem unit_ball_upper {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) :
    ∀ a ∈ ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}), a ≤ T.singularValues 0 := by
  rintro a ⟨v, hv, rfl⟩
  calc
    ‖T v‖ ≤ T.singularValues 0 * ‖v‖ := norm_le T v
    _ ≤ T.singularValues 0 * 1 :=
      mul_le_mul_of_nonneg_left hv (T.singularValues_nonneg 0)
    _ = T.singularValues 0 := mul_one _

theorem unit_ball_bounded : Specs.D05.M14.OperatorNorm.SvdBound.unit_ball_bounded := by
  intro F V W _ _ _ _ _ _ _ T
  exact ⟨⟨0, 0, by simp, by simp⟩, T.singularValues 0, unit_ball_upper T⟩

theorem unit_ball_isLUB : Specs.D05.M14.OperatorNorm.SvdBound.unit_ball_isLUB := by
  intro F V W _ _ _ _ _ _ _ T
  refine ⟨unit_ball_upper T, ?_⟩
  intro a ha
  by_cases hr : 0 < Module.finrank F (LinearMap.range T)
  · obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
    obtain ⟨he, hT, hs⟩ := attains_first T d hr
    exact ha ⟨d.domainBasis (Fin.castLE T.finrank_range_le ⟨0, hr⟩), he.le, hT⟩
  · have hz : T.singularValues 0 = 0 :=
      T.singularValues_eq_zero_iff_le_finrank_range.mpr (Nat.le_of_not_gt hr)
    rw [hz]
    exact ha ⟨0, by simp, by simp⟩

theorem unit_ball_supremum : Specs.D05.M14.OperatorNorm.SvdBound.unit_ball_supremum := by
  intro F V W _ _ _ _ _ _ _ T
  have hsup := (unit_ball_isLUB T).csSup_eq (unit_ball_bounded T).1
  refine ⟨hsup, ?_, ?_⟩
  · intro hT
    apply T.singularValues_pos_iff_lt_finrank_range.mpr
    by_contra hr
    exact hT ((rank_zero_outputs T).mp (Nat.eq_zero_of_not_pos hr)).1
  · intro hT
    rw [hsup, hT]
    simp

theorem zero_domain : Specs.D05.M14.OperatorNorm.SvdBound.zero_domain := by
  intro F V W _ _ _ _ _ _ _ T hn
  have hr : Module.finrank F (LinearMap.range T) = 0 :=
    Nat.eq_zero_of_le_zero (hn ▸ T.finrank_range_le)
  obtain ⟨hT, hv⟩ := (rank_zero_outputs T).mp hr
  refine ⟨hT, hv, ?_, (unit_ball_supremum T).2.2 hT⟩
  have hz : T.singularValues 0 = 0 := by rw [hT]; simp
  simpa only [hz] using unit_ball_isLUB T

end D05.M14.OperatorNorm.SvdBound
