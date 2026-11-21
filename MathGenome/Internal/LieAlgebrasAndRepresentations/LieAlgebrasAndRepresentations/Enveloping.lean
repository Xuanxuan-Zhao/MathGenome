import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Enveloping
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping

/-! LA A04: construction, universal bijection, and the module correspondence.
All constructions use the shared canonical quotient, before any use of PBW. -/
namespace LieAlgebrasAndRepresentations.Enveloping
open _root_.Shared.Lie
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w w'

def envelopingAlgebra (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] : Type (max u v) := U k g

def canonicalLieMap (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] := inclusion k g

def quotientMap (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] := tensorQuotient k g

def universalEquiv (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (A : Type w) [Ring A] [Algebra k A] :=
  (UniversalEnvelopingAlgebra.lift k : (g →ₗ⁅k⁆ A) ≃ (U k g →ₐ[k] A))

def representationsEquiv (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g] (M : Type w) [AddCommGroup M] [Module k M] := representationEquiv k g M

theorem quotient_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.quotientExpected.{u,v} := by
  intro k g _ _ _
  exact Shared.Lie.quotient k g

theorem universal_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.universalExpected.{u,v,w} := by
  intro k g _ _ _
  exact Shared.Lie.universal k g

theorem universalEquiv_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.universalLawsExpected.{u,v,w} := by
  intro k g _ _ _ A _ _
  exact ⟨UniversalEnvelopingAlgebra.lift_ι_apply k, fun _ => rfl⟩

theorem moduleStructures_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.moduleStructuresExpected.{u,v,w} := by
  intro k g _ _ _
  exact Shared.Lie.module_structures k g

theorem underlyingTower_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.underlyingTowerExpected.{u,v,w} := by
  intro k g _ _ _
  exact Shared.Lie.underlying_tower k g

theorem moduleRestriction_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.moduleRestrictionExpected.{u,v,w} := by
  intro k g _ _ _
  exact Shared.Lie.module_restriction k g

theorem lieExtension_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.lieExtensionExpected.{u,v,w} := by
  intro k g _ _ _
  exact Shared.Lie.lie_extension k g

theorem lieRoundtrip_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.lieRoundtripExpected.{u,v,w} := by
  intro k g _ _ _
  exact Shared.Lie.lie_roundtrip k g

theorem moduleRoundtrip_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.moduleRoundtripExpected.{u,v,w} := by
  intro k g _ _ _
  exact Shared.Lie.module_roundtrip k g

theorem morphism_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.morphismExpected.{u,v,w,w'} := by
  intro k g _ _ _
  exact Shared.Lie.morphism_correspondence k g

theorem morphismEquiv_spec : Specs.LieAlgebrasAndRepresentations.Enveloping.morphismEquivExpected.{u,v,w,w'} := by
  intro k g _ _ _
  exact Shared.Lie.morphism_equivalence k g

end LieAlgebrasAndRepresentations.Enveloping
