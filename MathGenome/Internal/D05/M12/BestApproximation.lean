import MathGenome.Internal.Specs.D05.M12.BestApproximation
import MathGenome.Internal.D05.M12.Projection
import MathGenome.Internal.D05.M12.NormLaws

/-! K05.12.best_approximation: the unique nearest point in a
finite-dimensional subspace of an arbitrary real or complex inner-product space. -/

namespace D05.M12.BestApproximation

theorem error_identity : Specs.D05.M12.BestApproximation.error_identity := by
  intro F V _ _ _ U _ v u hu
  have hc := (Projection.component_characterization U v
    (D05.orthogonalProjection U v)).mp rfl
  have ho : D05.firstInner (F := F) (v - D05.orthogonalProjection U v)
      (D05.orthogonalProjection U v - u) = 0 :=
    U.inner_right_of_mem_orthogonal (U.sub_mem hc.1 hu) hc.2
  simpa only [sub_add_sub_cancel] using
    NormLaws.firstInner_pythagoras _ _ ho

theorem distance_le : Specs.D05.M12.BestApproximation.distance_le := by
  intro F V _ _ _ U _ v u hu
  have hs := error_identity U v u hu
  have ha := norm_nonneg (v - D05.orthogonalProjection U v)
  have hb := norm_nonneg (v - u)
  nlinarith [sq_nonneg ‖D05.orthogonalProjection U v - u‖]

theorem distance_eq_iff : Specs.D05.M12.BestApproximation.distance_eq_iff := by
  intro F V _ _ _ U _ v u hu
  constructor
  · intro he
    have hs := error_identity U v u hu
    have hsq : ‖D05.orthogonalProjection U v - u‖ ^ 2 = 0 := by
      rw [he] at hs
      linarith
    have hz : ‖D05.orthogonalProjection U v - u‖ = 0 := sq_eq_zero_iff.mp hsq
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · rintro rfl
    rfl

theorem minimizer_iff : Specs.D05.M12.BestApproximation.minimizer_iff := by
  intro F V _ _ _ U _ v u
  have hc := (Projection.component_characterization U v
    (D05.orthogonalProjection U v)).mp rfl
  constructor
  · rintro ⟨hu, hmin⟩
    apply (distance_eq_iff U v u hu).mp
    exact le_antisymm (hmin _ hc.1) (distance_le U v u hu)
  · rintro rfl
    exact ⟨hc.1, fun w hw => distance_le U v w hw⟩

theorem exists_unique_minimizer :
    Specs.D05.M12.BestApproximation.exists_unique_minimizer := by
  intro F V _ _ _ U _ v
  refine ⟨D05.orthogonalProjection U v, (minimizer_iff U v _).mpr rfl, ?_⟩
  intro u hu
  exact (minimizer_iff U v u).mp hu

end D05.M12.BestApproximation
