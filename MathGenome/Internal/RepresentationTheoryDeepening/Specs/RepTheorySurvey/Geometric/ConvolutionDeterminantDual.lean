import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Grassmannian

namespace RepTheorySurvey.Geometric.ConvolutionDeterminantDualSpecs

universe u v

/-- A volume form on a free rank-two module identifies the Grassmannian quotient
with the dual of the tautological line on every affine test ring. -/
def DeterminantDual : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (c : M ≃ₗ[R] (Fin 2 → R)) (L : Module.Grassmannian R M 1),
    let S := L.toSubmodule
    ∃ e : (M ⧸ S) ≃ₗ[R] Module.Dual R S,
      ∀ (x : S) (y : M), e (S.mkQ y) x =
        c x.val 0 * c y 1 - c x.val 1 * c y 0

end RepTheorySurvey.Geometric.ConvolutionDeterminantDualSpecs
