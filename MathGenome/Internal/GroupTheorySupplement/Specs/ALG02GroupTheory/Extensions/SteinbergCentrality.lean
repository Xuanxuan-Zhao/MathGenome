import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.Central
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.StableSteinberg

/-! The central extension and perfectness statements for the stable Steinberg map. -/

namespace Specs.ALG02GroupTheory.Extensions.SteinbergCentrality

open _root_.ALG02GroupTheory.Extensions.StableSteinberg.Spec

universe u

def ExtensionType :=
  ∀ (R : Type u) [Ring R], GroupExtension (K₂ R) (Steinberg R) (Elementary R)

private theorem canonicalMapSurjective {R : Type u} [Ring R] :
    Function.Surjective (toElementary (R := R)) := by
  let inclusion := (ElementarySubgroup R).subtype
  let image := (toElementary (R := R)).range.map inclusion
  have h : ElementarySubgroup R ≤ image := by
    change Subgroup.closure (Set.range transvection) ≤ image
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    refine ⟨elementary g, ⟨generator g, ?_⟩, rfl⟩
    exact PresentedGroup.toGroup.of (killsRelators elementary_satisfiesRelations)
  intro y
  obtain ⟨z, ⟨x, hx⟩, hz⟩ := h y.property
  exact ⟨x, hx.trans (Subtype.ext hz)⟩

/-- The exact sequence with the actual kernel inclusion and canonical projection. -/
noncomputable def extensionValue : ExtensionType.{u} := fun R _ =>
  { inl := (K₂ R).subtype
    rightHom := toElementary
    inl_injective := (K₂ R).subtype_injective
    range_inl_eq_ker_rightHom := Subgroup.range_subtype _
    rightHom_surjective := canonicalMapSurjective }

def KernelLeCenter : Prop :=
  ∀ (R : Type u) [Ring R], K₂ R ≤ Subgroup.center (Steinberg R)

def ExtensionCentral : Prop :=
  ∀ (R : Type u) [Ring R], isCentralExtensionValue (extensionValue R)

def KernelAbelian : Prop :=
  ∀ (R : Type u) [Ring R], IsMulCommutative (K₂ R)

def SteinbergPerfect : Prop :=
  ∀ (R : Type u) [Ring R], isPerfectValue (Steinberg R)

def ElementaryPerfect : Prop :=
  ∀ (R : Type u) [Ring R], isPerfectValue (Elementary R)

end Specs.ALG02GroupTheory.Extensions.SteinbergCentrality
