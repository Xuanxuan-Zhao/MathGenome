import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.QuotientFactorization

/-! The distance-quotient seminorm is definite exactly for closed subspaces.
The canonical linear projection is a contraction, maps each strict ball onto
the strict ball of the same radius, and is open. Algebraic and bounded
factorizations are supplied by the accepted upstream factorization theorem.
-/

noncomputable section

namespace ExpandedFA.P1.C02QuotientMap

theorem distance_representative_independent : Spec.RepresentativeIndependence := by
  intro 𝕜 E _ _ _ M x y hxy
  have hx := C02QuotientNorm.distanceSeminorm_mk 𝕜 E M x
  have hy := C02QuotientNorm.distanceSeminorm_mk 𝕜 E M y
  constructor
  · rw [← hx.1, ← hy.1, hxy]
  · rw [← hx.2.1, ← hy.2.1, hxy]

theorem quotient_seminorm_axioms : Spec.QuotientSeminormAxioms := by
  intro 𝕜 E _ _ _ M
  exact C01Norm.canonical_seminorm_axioms 𝕜 (E ⧸ M)

theorem quotient_null_cosets : Spec.NullCosets := by
  intro 𝕜 E _ _ _ M x
  exact QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure

theorem quotient_norm_iff_closed : Spec.QuotientNormIffClosed := by
  intro 𝕜 E _ _ _ M
  constructor
  · intro h
    apply isClosed_of_closure_subset
    intro x hx
    have hz := (quotient_null_cosets 𝕜 E M x).mpr hx
    have hq := (h.2 (M.mkQ x)).mp hz
    exact (Submodule.Quotient.mk_eq_zero M).mp hq
  · intro hM
    let : IsClosed (M : Set E) := hM
    exact C01Norm.canonical_norm_axioms 𝕜 (E ⧸ M)

theorem quotient_projection_properties : Spec.ProjectionProperties := by
  intro 𝕜 E _ _ _ M
  refine ⟨M.mkQ.map_add, M.mkQ.map_smul, M.mkQ_surjective,
    Submodule.Quotient.norm_mk_le M, ?_, M.continuous_mkQ⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (M.mkQ x) (M.mkQ y) = ‖M.mkQ x - M.mkQ y‖ := dist_eq_norm _ _
    _ = ‖M.mkQ (x - y)‖ := congrArg norm (M.mkQ.map_sub x y).symm
    _ ≤ ‖x - y‖ := Submodule.Quotient.norm_mk_le M (x - y)
    _ = ((1 : NNReal) : ℝ) * dist x y := by rw [dist_eq_norm, NNReal.coe_one, one_mul]

theorem quotient_ball_image : Spec.BallImage := by
  intro 𝕜 E _ _ _ M x r
  change M.mkQ '' Metric.ball x r = Metric.ball (M.mkQ x) r
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball_iff_norm] at hy ⊢
    calc
      ‖M.mkQ y - M.mkQ x‖ = ‖M.mkQ (y - x)‖ :=
        congrArg norm (M.mkQ.map_sub y x).symm
      _ ≤ ‖y - x‖ := Submodule.Quotient.norm_mk_le M (y - x)
      _ < r := hy
  · intro hz
    have hn : ‖z - M.mkQ x‖ < r := mem_ball_iff_norm.mp hz
    obtain ⟨y, hy, hnorm⟩ :=
      Submodule.Quotient.norm_mk_lt (z - M.mkQ x) (sub_pos.mpr hn)
    change M.mkQ y = z - M.mkQ x at hy
    refine ⟨x + y, ?_, ?_⟩
    · rw [mem_ball_iff_norm, add_sub_cancel_left]
      simpa only [add_sub_cancel] using hnorm
    · rw [map_add, hy, add_comm, sub_add_cancel]

theorem quotient_projection_open : Spec.OpenProjection := by
  intro 𝕜 E _ _ _ M
  exact M.isOpenMap_mkQ

theorem quotient_algebraic_factorization : Spec.AlgebraicFactorization :=
  QuotientFactorization.quotient_algebraic_factorization

theorem quotient_bounded_factorization : Spec.BoundedFactorization :=
  QuotientFactorization.quotient_bounded_factorization

end ExpandedFA.P1.C02QuotientMap
