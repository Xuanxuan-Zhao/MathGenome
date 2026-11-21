import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.PBWSpecialization
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Enveloping
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWGraded

/-! LA A05: specialization of the shared free-module PBW theorems to fields.
All maps and filtrations use the actual enveloping quotient from LA A04.
No finite-dimensionality or characteristic-zero hypothesis is used.
-/
namespace LieAlgebrasAndRepresentations.PBW
open _root_.Shared.Lie _root_.Shared.Lie.PBW _root_.Shared.Lie.PBW.Graded
universe u v w

theorem orderedBasis_spec :
    Specs.LieAlgebrasAndRepresentations.PBW.orderedBasisExpected.{u,v,w} := by
  intro k g ι _ _ _ _ b
  refine ⟨orderedBasis b, orderedBasis_apply b, ?_, ?_⟩
  · simp
  · intro i
    simp

theorem inclusionInjective_spec :
    Specs.LieAlgebrasAndRepresentations.PBW.inclusionInjectiveExpected.{u,v,w} := by
  intro k g ι _ _ _ _ b
  change Function.Injective (Enveloping.canonicalLieMap k g)
  exact Shared.Lie.PBW.inclusionInjective_spec k g ι b

theorem filteredBasis_spec :
    Specs.LieAlgebrasAndRepresentations.PBW.filteredBasisExpected.{u,v,w} := by
  intro k g ι _ _ _ _ b m
  exact filtration_eq_boundedSpan b m

theorem graded_spec :
    Specs.LieAlgebrasAndRepresentations.PBW.gradedExpected.{u,v,w} := by
  intro k g ι _ _ _ _ b
  refine ⟨filtration_properties k g, ?_⟩
  letI : Fact (Specs.Shared.Lie.filtrationType k g) := ⟨filtration_properties k g⟩
  let e : SymmetricAlgebra k g ≃ₐ[k] Associated k g :=
    AlgEquiv.ofBijective (canonicalMap (k := k) (g := g)) (canonicalMap_bijective_of_basis b)
  refine ⟨e, rfl, ?_, ?_, gradedBasis b, ?_⟩
  · exact canonicalMap_generator
  · exact canonicalMap_degree b
  · intro l
    exact ⟨gradedBasis_apply b l, (canonicalMap_orderedWord b l).trans (gradedBasis_apply b l).symm⟩

end LieAlgebrasAndRepresentations.PBW
