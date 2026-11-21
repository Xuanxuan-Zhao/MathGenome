import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.AlgebraRepresentations
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.RingHom

namespace RM03.Quivers.AlgebraRepresentations

open scoped MonoidAlgebra

variable {k A V W : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Restrict the evaluation action of the endomorphism ring along the representation. -/
def moduleOfRepresentation (ρ : A →ₐ[k] Module.End k V) : CompatibleModule k A V where
  module := Module.compHom V ρ.toRingHom
  scalar c z := by
    change ρ (algebraMap k A c) z = c • z
    rw [ρ.commutes, Module.algebraMap_end_apply]

@[simp] theorem moduleOfRepresentation_act (ρ : A →ₐ[k] Module.End k V) (a : A) (z : V) :
    (moduleOfRepresentation ρ).act a z = ρ a z := rfl

/-- Regard each scalar in the algebra as the linear map given by its action. -/
def CompatibleModule.toRepresentation (M : CompatibleModule k A V) : A →ₐ[k] Module.End k V :=
  letI := M.module
  letI := IsScalarTower.of_algebraMap_smul M.scalar
  Algebra.lsmul k k V

@[simp] theorem CompatibleModule.toRepresentation_apply (M : CompatibleModule k A V)
    (a : A) (z : V) : M.toRepresentation a z = M.act a z := rfl

@[ext] theorem CompatibleModule.ext {M N : CompatibleModule k A V}
    (h : ∀ a z, M.act a z = N.act a z) : M = N := by
  have hModule : M.module = N.module := Module.ext' _ _ h
  cases M
  cases N
  cases hModule
  rfl

/-- Algebra representations and compatible actions on the same vector space. -/
def representationEquiv : (A →ₐ[k] Module.End k V) ≃ CompatibleModule k A V where
  toFun := moduleOfRepresentation
  invFun := CompatibleModule.toRepresentation
  left_inv _ := AlgHom.ext fun _ => LinearMap.ext fun _ => rfl
  right_inv _ := CompatibleModule.ext fun _ _ => rfl

theorem correspondence : Specs.correspondenceType := by
  intro k A V _ _ _ _ _
  exact ⟨representationEquiv, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- A scalar-preserving additive map gives an algebra-linear map with the same values. -/
theorem moduleLinear_iff (M : CompatibleModule k A V) (N : CompatibleModule k A W)
    (f : V →ₗ[k] W) :
    IsModuleLinear M N f ↔ ∀ a z, f (M.act a z) = N.act a (f z) := by
  let := M.module
  let := N.module
  change (∃ F : V →ₗ[A] W, ∀ z, F z = f z) ↔
    ∀ (a : A) (z : V), f (a • z) = a • f z
  constructor
  · rintro ⟨F, hF⟩ a z
    simpa only [hF] using F.map_smul a z
  · intro hf
    exact ⟨{ toFun := f, map_add' := f.map_add, map_smul' := hf }, fun _ => rfl⟩

theorem intertwinesIffModuleLinear : Specs.intertwinesIffModuleLinearType := by
  intro k A V W _ _ _ _ _ _ _ ρ σ M N hM hN f
  rw [moduleLinear_iff]
  simp only [hM, hN]

/-- The linear extension of a group representation to the group algebra. -/
noncomputable def groupAlgebraRepresentation {G : Type*} [Group G]
    (ρ : G →* (V ≃ₗ[k] V)) : k[G] →ₐ[k] Module.End k V :=
  MonoidAlgebra.lift k (Module.End k V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ)

theorem groupAlgebraExtension : Specs.groupAlgebraExtensionType := by
  intro k G V _ _ _ _ ρ
  refine ⟨groupAlgebraRepresentation ρ, moduleOfRepresentation (groupAlgebraRepresentation ρ),
    fun _ _ => rfl, ?_, ?_⟩
  · intro a z
    simp only [moduleOfRepresentation_act, groupAlgebraRepresentation, MonoidAlgebra.lift_apply,
      Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  · intro g z
    rw [moduleOfRepresentation_act, groupAlgebraRepresentation, MonoidAlgebra.lift_of]
    rfl

end RM03.Quivers.AlgebraRepresentations
