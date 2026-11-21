import Mathlib.LinearAlgebra.Basis.VectorSpace
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Density.Action

universe u v

namespace RM03.Density

/-- A single scalar interpolates arbitrary values on a finite tuple that is linearly
independent for the evaluation action of the endomorphism ring. -/
theorem interpolate (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] (n : ℕ) (x y : Fin n → M)
    (hx : LinearIndependent (Module.End R M) x) :
    ∃ r : R, ∀ i : Fin n, r • x i = y i := by
  classical
  let basis := Module.Basis.span hx
  obtain ⟨f, hf⟩ := (basis.constr ℕ y).exists_extend
  have hfx (i : Fin n) : f (x i) = y i := by
    have hi := LinearMap.congr_fun hf (basis i)
    rw [basis.constr_basis] at hi
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype, basis,
      Module.Basis.coe_span_apply] using hi
  obtain ⟨r, hr⟩ := jacobson_density (f : RightEnd R M) (Finset.univ.image x)
  refine ⟨r, fun i ↦ ?_⟩
  exact (hr (x i) (Finset.mem_image_of_mem x (Finset.mem_univ i))).symm.trans (hfx i)

end RM03.Density
