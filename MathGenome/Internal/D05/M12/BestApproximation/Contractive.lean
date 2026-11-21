import MathGenome.Internal.Specs.D05.M12.BestApproximation.Contractive
import MathGenome.Internal.D05.M06.Projection
import MathGenome.Internal.D05.M12.BestApproximation.Conditional
import MathGenome.Internal.D05.M12.NormLaws

/-! Contractive algebraic idempotents on arbitrary real or complex
inner-product spaces are precisely orthogonal projections. -/

namespace D05.M12.BestApproximation.Contractive

/-- Apply the conditional nearest-point criterion to the entire kernel:
contractivity makes zero a nearest point to each image vector. -/
theorem contractive_iff_range_orthogonal_kernel :
    Specs.D05.M12.BestApproximation.Contractive.contractive_iff_range_orthogonal_kernel := by
  intro F V _ _ _ P hP
  constructor
  · intro hc u hu
    have hfix : P u = u := (M06.Projection.range_iff_fixed P hP u).mp hu
    have hmin : ∀ z ∈ LinearMap.ker P, ‖u - (0 : V)‖ ≤ ‖u - z‖ := by
      intro z hz
      have hz' : P z = 0 := LinearMap.mem_ker.mp hz
      simpa only [map_sub, hfix, hz', sub_zero] using hc (u - z)
    have horth := (Conditional.minimizes_iff_firstInner_eq_zero
      (LinearMap.ker P) u 0 (Submodule.zero_mem _)).mp hmin
    simpa only [sub_zero] using horth
  · intro ho x
    obtain ⟨hr, hk, hx⟩ := M06.Projection.decomposition_formula P hP x
    have hp := NormLaws.firstInner_pythagoras (F := F) (P x) (x - P x)
      (ho (P x) hr (x - P x) hk)
    rw [← hx] at hp
    nlinarith [sq_nonneg ‖x - P x‖, norm_nonneg (P x), norm_nonneg x]

/-- The image/kernel decomposition becomes orthogonal, with no dimension
or completeness restriction. -/
theorem orthogonal_decomposition :
    Specs.D05.M12.BestApproximation.Contractive.orthogonal_decomposition := by
  intro F V _ _ _ P hP hc
  have ho := (contractive_iff_range_orthogonal_kernel P hP).mp hc
  have hk : LinearMap.ker P ≤ (LinearMap.range P).orthogonal := by
    intro z hz u hu
    exact inner_eq_zero_symm.mp (ho u hu z hz)
  have heq : LinearMap.ker P = (LinearMap.range P).orthogonal := by
    apply le_antisymm hk
    intro x hx
    obtain ⟨hr, hker, _⟩ := M06.Projection.decomposition_formula P hP x
    have hperp : P x ∈ (LinearMap.range P).orthogonal := by
      have := (LinearMap.range P).orthogonal.sub_mem hx (hk hker)
      simpa only [sub_sub_cancel] using this
    have hzero : P x = 0 := by
      have hmem : P x ∈ LinearMap.range P ⊓ (LinearMap.range P).orthogonal := ⟨hr, hperp⟩
      rw [Submodule.inf_orthogonal_eq_bot] at hmem
      exact hmem
    exact LinearMap.mem_ker.mpr hzero
  refine ⟨heq, ?_⟩
  intro x
  obtain ⟨hr, hker, hx⟩ := M06.Projection.decomposition_formula P hP x
  exact ⟨hr, hk hker, hx⟩

/-- Construct the projection-existence instance from P itself and use the
uniqueness characterization of Mathlib's canonical orthogonal projection. -/
theorem eq_starProjection :
    Specs.D05.M12.BestApproximation.Contractive.eq_starProjection := by
  intro F V _ _ _ P hP hc
  have hd := (orthogonal_decomposition P hP hc).2
  letI h : (LinearMap.range P).HasOrthogonalProjection :=
    ⟨fun x => ⟨P x, (hd x).1, (hd x).2.1⟩⟩
  refine ⟨h, ?_⟩
  apply LinearMap.ext
  intro x
  exact (Submodule.eq_starProjection_of_mem_orthogonal (hd x).1 (hd x).2.1).symm

end D05.M12.BestApproximation.Contractive
