import MathGenome.Internal.Specs.D05.M14.OperatorNorm
import MathGenome.Internal.D05.M14.OperatorNorm.SvdBound

/-! Operator norm from the closed unit ball, its largest-singular-value formula,
and its norm laws. The bridge to continuous maps uses only finite-dimensional
continuity and does not change the definition or add a hypothesis. -/

noncomputable section
namespace D05.M14.OperatorNorm

/-- The same closed-ball supremum as the independent specification. -/
abbrev operatorNorm : Specs.D05.M14.OperatorNorm.operatorNorm_type := fun T => D05.operatorNorm T

theorem definition_eq : Specs.D05.M14.OperatorNorm.definition_eq := by
  intro F V W _ _ _ _ _ _ _ T
  rfl

theorem eq_first_singularValue : Specs.D05.M14.OperatorNorm.eq_first_singularValue := by
  intro F V W _ _ _ _ _ _ _ T
  exact (SvdBound.unit_ball_supremum T).1

theorem unit_ball_supremum : Specs.D05.M14.OperatorNorm.unit_ball_supremum := by
  intro F V W _ _ _ _ _ _ _ T
  obtain ⟨hne, hbdd⟩ := SvdBound.unit_ball_bounded T
  refine ⟨hne, hbdd, ?_⟩
  rw [eq_first_singularValue]
  exact SvdBound.unit_ball_isLUB T

theorem nonzero_attains : Specs.D05.M14.OperatorNorm.nonzero_attains := by
  intro F V W _ _ _ _ _ _ _ T hT
  have hr : 0 < Module.finrank F T.range := by
    by_contra h
    exact hT ((SvdBound.rank_zero_outputs T).mp (Nat.eq_zero_of_not_pos h)).1
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  obtain ⟨he, hTe, _⟩ := SvdBound.attains_first T d hr
  exact ⟨(SvdBound.unit_ball_supremum T).2.1 hT, eq_first_singularValue T,
    d.domainBasis (Fin.castLE T.finrank_range_le ⟨0, hr⟩), he,
    hTe.trans (eq_first_singularValue T).symm⟩

theorem zero_map : Specs.D05.M14.OperatorNorm.zero_map := by
  intro F V W _ _ _ _ _ _ _
  rw [eq_first_singularValue]
  simp

theorem zero_domain : Specs.D05.M14.OperatorNorm.zero_domain := by
  intro F V W _ _ _ _ _ _ _ T hn
  have hT := (SvdBound.zero_domain T hn).1
  exact ⟨hT, by rw [hT]; exact zero_map⟩

/-- The set in the paper is exactly the closed ball used by the library.
This theorem holds even if the domain is the zero space. -/
theorem eq_continuous_opNorm : Specs.D05.M14.OperatorNorm.eq_continuous_opNorm := by
  intro F V W _ _ _ _ _ _ _ T
  simpa only [D05.operatorNorm, Metric.closedBall, dist_zero_right,
    LinearMap.coe_toContinuousLinearMap'] using
    T.toContinuousLinearMap.sSup_unitClosedBall_eq_norm

theorem apply_le : Specs.D05.M14.OperatorNorm.apply_le := by
  intro F V W _ _ _ _ _ _ _ T v
  rw [eq_first_singularValue]
  exact SvdBound.norm_le T v

theorem adjoint_eq : Specs.D05.M14.OperatorNorm.adjoint_eq := by
  intro F V W _ _ _ _ _ _ _ T
  let := FiniteDimensional.complete F V
  let := FiniteDimensional.complete F W
  rw [eq_continuous_opNorm, eq_continuous_opNorm, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem nonneg : Specs.D05.M14.OperatorNorm.nonneg := by
  intro F V W _ _ _ _ _ _ _ T
  rw [eq_continuous_opNorm]
  exact norm_nonneg _

theorem eq_zero_iff : Specs.D05.M14.OperatorNorm.eq_zero_iff := by
  intro F V W _ _ _ _ _ _ _ T
  rw [eq_continuous_opNorm, norm_eq_zero]
  exact LinearMap.toContinuousLinearMap.map_eq_zero_iff

theorem smul : Specs.D05.M14.OperatorNorm.smul := by
  intro F V W _ _ _ _ _ _ _ a T
  rw [eq_continuous_opNorm, eq_continuous_opNorm, map_smul, norm_smul]

theorem add_le : Specs.D05.M14.OperatorNorm.add_le := by
  intro F V W _ _ _ _ _ _ _ S T
  rw [eq_continuous_opNorm, eq_continuous_opNorm, eq_continuous_opNorm, map_add]
  exact norm_add_le _ _

theorem norm_axioms : Specs.D05.M14.OperatorNorm.norm_axioms := by
  intro F V W _ _ _ _ _ _ _
  exact ⟨nonneg, eq_zero_iff, smul, add_le⟩

theorem comp_le : Specs.D05.M14.OperatorNorm.comp_le := by
  intro F V W _ _ _ _ _ _ _ X _ _ _ S T
  rw [eq_continuous_opNorm, eq_continuous_opNorm, eq_continuous_opNorm]
  have he : (S.comp T).toContinuousLinearMap =
      S.toContinuousLinearMap.comp T.toContinuousLinearMap := by ext v; rfl
  rw [he]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end D05.M14.OperatorNorm
