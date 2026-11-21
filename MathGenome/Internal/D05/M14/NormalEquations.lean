import MathGenome.Internal.Specs.D05.M14.NormalEquations
import MathGenome.Internal.D05.M13.AdjointKernel
import MathGenome.Internal.D05.M14.LeastSquares
import MathGenome.Internal.D05.M03.EqualDimension

/-! K05.14.normal_equations: normal equations, invertibility of T†T,
and the unique minimizer (T†T)⁻¹T†w for an injective map.
All constructions and statements include zero-dimensional spaces. -/

noncomputable section

namespace D05.M14.NormalEquations

theorem minimizer_iff_normal_equation :
    Specs.D05.M14.NormalEquations.minimizer_iff_normal_equation := by
  intro F V W _ _ _ _ _ _ _ T w v
  rw [D05.M14.LeastSquares.minimizer_iff_projection]
  have hc := D05.M12.Projection.component_characterization T.range w (T v)
  have hr : T v ∈ T.range := ⟨v, rfl⟩
  have hk : LinearMap.adjoint T (T v - w) = 0 ↔
      T v - w ∈ T.range.orthogonal := by
    change T v - w ∈ (LinearMap.adjoint T).ker ↔ _
    rw [D05.M13.AdjointKernel.ker_adjoint]
  rw [hk]
  constructor
  · intro h
    have ho := (hc.mp h.symm).2
    simpa only [neg_sub] using T.range.orthogonal.neg_mem ho
  · intro ho
    apply (hc.mpr ⟨hr, ?_⟩).symm
    simpa only [neg_sub] using T.range.orthogonal.neg_mem ho

theorem gram_isUnit_iff_injective :
    Specs.D05.M14.NormalEquations.gram_isUnit_iff_injective := by
  intro F V W _ _ _ _ _ _ _ T
  rw [LinearMap.isUnit_iff_ker_eq_bot,
    D05.M13.AdjointKernel.ker_adjoint_comp_self, LinearMap.ker_eq_bot]

theorem gram_inverse_identities :
    Specs.D05.M14.NormalEquations.gram_inverse_identities := by
  intro F V W _ _ _ _ _ _ _ T hT
  have hunit := (gram_isUnit_iff_injective T).mpr hT
  exact ⟨Ring.inverse_mul_cancel _ hunit, Ring.mul_inverse_cancel _ hunit⟩

theorem minimizer_iff_inverse_formula :
    Specs.D05.M14.NormalEquations.minimizer_iff_inverse_formula := by
  intro F V W _ _ _ _ _ _ _ T hT w v
  rw [minimizer_iff_normal_equation, map_sub, sub_eq_zero]
  obtain ⟨hleft, hright⟩ := gram_inverse_identities T hT
  have hl (x : V) :
      Ring.inverse ((LinearMap.adjoint T).comp T) (LinearMap.adjoint T (T x)) = x :=
    LinearMap.congr_fun hleft x
  have hr (x : V) :
      LinearMap.adjoint T (T (Ring.inverse ((LinearMap.adjoint T).comp T) x)) = x :=
    LinearMap.congr_fun hright x
  constructor
  · intro hv
    rw [← hv, hl]
  · intro hv
    rw [hv, hr]

theorem exists_unique_injective_minimizer :
    Specs.D05.M14.NormalEquations.exists_unique_injective_minimizer := by
  intro F V W _ _ _ _ _ _ _ T hT w
  refine ⟨Ring.inverse ((LinearMap.adjoint T).comp T) (LinearMap.adjoint T w),
    (minimizer_iff_inverse_formula T hT w _).mpr rfl, ?_⟩
  intro v hv
  exact (minimizer_iff_inverse_formula T hT w v).mp hv

end D05.M14.NormalEquations
