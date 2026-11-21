import MathGenome.Internal.D07.Ch21.GroupAlgebra
import MathGenome.Internal.D07.Ch21.RegularDecomposition
import MathGenome.Internal.Specs.D07.Ch21.CharacterCompletenessGroupAlgebraProduct
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace D07.Ch21.CharacterCompletenessGroupAlgebraProduct

universe u r v
noncomputable section

open Specs.D07.Ch21.RegularDecomposition
open Specs.D07.Ch21.CharacterCompletenessGroupAlgebraProduct

/-- Simultaneous action on the chosen irreducible representation spaces. -/
def actionMap : ActionMapType.{u,r,v} := actionMapValue

/-- The upstream column map is faithful because vanishing on every
irreducible summand annihilates the regular module. Evaluating left
multiplication at its unit then recovers the group algebra element.
Equality of the simultaneous actions implies equality of all their
columns, so that same argument proves injectivity here. -/
theorem action_map_injective : ActionMapInjective.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hc
  haveI : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (RegularDecomposition.irreducible_finite G (V i) (ρ i) (hi i)).1
  let b (i : I) := Module.finBasis ℂ (V i)
  intro a a' haa'
  apply RegularDecomposition.fourierColumns_injective ρ b hc
  funext p
  exact congrArg (fun f => f p.1 (b p.1 p.2)) haa'

theorem product_dimension : ProductDimension.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  haveI : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (RegularDecomposition.irreducible_finite G (V i) (ρ i) (hi i)).1
  refine ⟨(GroupAlgebra.dimension G).2, ?_⟩
  rw [Module.finrank_pi_fintype]
  simp only [Module.End, Module.finrank_linearMap, ← pow_two]
  exact (RegularDecomposition.square_sum G I V ρ hi hne hc).symm

/-- Injectivity between the two finite spaces of equal dimension proves
surjectivity. No associative-algebra classification theorem is used. -/
theorem action_map_surjective : ActionMapSurjective.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  haveI : ∀ i, FiniteDimensional ℂ (V i) := fun i =>
    (RegularDecomposition.irreducible_finite G (V i) (ρ i) (hi i)).1
  haveI := (GroupAlgebra.dimension G).1
  have hd := product_dimension G I V ρ hi hne hc
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (actionMapValue G I V ρ).toLinearMap) (hd.1.trans hd.2.symm)).mp
      (action_map_injective G I V ρ hi hc)

theorem group_algebra_product : GroupAlgebraProduct.{u,r,v} := by
  intro G _ _ I _ V _ _ ρ hi hne hc
  exact ⟨AlgEquiv.ofBijective (actionMapValue G I V ρ)
    ⟨action_map_injective G I V ρ hi hc,
      action_map_surjective G I V ρ hi hne hc⟩, rfl⟩

end
end D07.Ch21.CharacterCompletenessGroupAlgebraProduct
