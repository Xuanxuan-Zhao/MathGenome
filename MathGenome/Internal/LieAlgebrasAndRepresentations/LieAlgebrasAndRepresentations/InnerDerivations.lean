import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ActionsDerivationsSemidirect
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.InnerDerivations
import Mathlib.Algebra.Lie.Derivation.Killing

/-! LA-B07, inner derivations. The upstream semisimplicity hypothesis is
vanishing solvable radical. In characteristic zero it gives a nondegenerate
Killing form, so Mathlib's theorem for Killing Lie algebras supplies existence.
The zero center gives injectivity and thus uniqueness. -/

universe u v
namespace LieAlgebrasAndRepresentations

variable (k : Type u) (L : Type v) [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

theorem adjoint_bijective (h : IsSemisimple k L) :
    Function.Bijective (adjoint k L) := by
  have : LieAlgebra.HasTrivialRadical k L := ⟨h⟩
  refine ⟨LieDerivation.injective_ad_of_center_eq_bot
    (semisimple_center_eq_bot k L h), ?_⟩
  intro D
  exact LieDerivation.IsKilling.exists_eq_ad D

theorem derivation_inner_unique (h : IsSemisimple k L) (D : LieDerivation k L L) :
    ∃! x : L, adjoint k L x = D := by
  obtain ⟨x, hx⟩ := (adjoint_bijective k L h).surjective D
  exact ⟨x, hx, fun y hy => (adjoint_bijective k L h).injective (hy.trans hx.symm)⟩

theorem adjoint_isomorphism (h : IsSemisimple k L) :
    ∃ e : L ≃ₗ⁅k⁆ LieDerivation k L L, e.toLieHom = adjoint k L := by
  exact ⟨LieEquiv.ofBijective (adjoint k L) (adjoint_bijective k L h), rfl⟩

end LieAlgebrasAndRepresentations
