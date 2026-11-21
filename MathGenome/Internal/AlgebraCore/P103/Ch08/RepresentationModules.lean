import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules

noncomputable section
namespace P103.Ch08
open scoped MonoidAlgebra
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Extend a representation to its unital group algebra module, on V itself. -/
def extendRepresentation (ρ : Representation k G V) : CompatibleModule k G V :=
  representationModule k G V ρ

theorem groupAlgebra_basisProduct : Specs.basisProduct (k := k) (G := G) := by
  intro g h
  simp [MonoidAlgebra.single_mul_single]

/-- The automorphism and endomorphism definitions agree, including on zero spaces. -/
def automorphismEquiv : (G →* (V ≃ₗ[k] V)) ≃ Representation k G V where
  toFun ρ :=
    { toFun := fun g => (ρ g).toLinearMap
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp }
  invFun ρ :=
    { toFun := fun g =>
        { toLinearMap := ρ g
          invFun := ρ g⁻¹
          left_inv := ρ.inv_self_apply g
          right_inv := ρ.self_inv_apply g }
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp }
  left_inv ρ := by ext; rfl
  right_inv ρ := rfl

theorem automorphism_correspondence : Specs.automorphismCorrespondence
    (k := k) (G := G) (V := V) := by
  exact ⟨automorphismEquiv, by intros; rfl, by intros; rfl⟩

@[simp] theorem representationModule_act (ρ : Representation k G V) (a : k[G]) (v : V) :
    (representationModule k G V ρ).act a v = ρ.asAlgebraHom a v := rfl

@[simp] theorem compatibleModule_representation_apply (M : CompatibleModule k G V) (g : G) (v : V) :
    M.representation g v = M.act (MonoidAlgebra.single g 1) v := rfl

theorem compatibleModule_asAlgebraHom (M : CompatibleModule k G V) (a : k[G]) (v : V) :
    M.representation.asAlgebraHom a v = M.act a v := by
  let := M.module
  let : IsScalarTower k k[G] V := IsScalarTower.of_algebraMap_smul M.scalar
  change ((MonoidAlgebra.lift k (Module.End k V) G)
    ((MonoidAlgebra.lift k (Module.End k V) G).symm (Algebra.lsmul k k V))) a v = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem representationModule_representation (ρ : Representation k G V) :
    (representationModule k G V ρ).representation = ρ := by
  ext g v
  simp

theorem CompatibleModule.ext_act {M N : CompatibleModule k G V}
    (h : ∀ a v, M.act a v = N.act a v) : M = N := by
  have e : M.module = N.module := Module.ext' _ _ h
  cases M
  cases N
  cases e
  rfl

theorem compatibleModule_roundtrip (M : CompatibleModule k G V) :
    representationModule k G V M.representation = M := by
  apply CompatibleModule.ext_act
  intro a v
  exact compatibleModule_asAlgebraHom M a v

/-- The correspondence takes values in genuine unital module structures on V. -/
def representationModuleEquiv : Representation k G V ≃ CompatibleModule k G V where
  toFun := extendRepresentation
  invFun := CompatibleModule.representation
  left_inv := representationModule_representation
  right_inv := compatibleModule_roundtrip

theorem representationModule_sum (ρ : Representation k G V) (a : k[G]) (v : V) :
    (representationModule k G V ρ).act a v = a.coeff.sum (fun g c => c • ρ g v) := by
  simp only [representationModule_act, Representation.asAlgebraHom_def,
    MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

theorem module_correspondence : Specs.moduleCorrespondence (k := k) (G := G) (V := V) := by
  exact ⟨representationModuleEquiv, fun _ => rfl, fun _ => rfl,
    representationModule_sum, compatibleModule_representation_apply⟩

variable {W : Type*} [AddCommGroup W] [Module k W]

theorem intertwiner_correspondence (ρ : Representation k G V) (σ : Representation k G W) :
    Specs.intertwinerCorrespondence ρ σ := by
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).toEquiv, ?_, ?_⟩
  · intros; rfl
  · intros; rfl

theorem subspace_correspondence (ρ : Representation k G V) :
    Specs.subspaceCorrespondence ρ := by
  exact ⟨Subrepresentation.subrepresentationSubmoduleOrderIso, fun _ _ => Iff.rfl⟩

theorem restriction_compatibility (ρ : Representation k G V) :
    Specs.restrictionCompatibility ρ := by
  intro U a v
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [representationModule_act]
  | add a b ha hb =>
    simp only [representationModule_act, map_add, LinearMap.add_apply,
      Submodule.coe_add] at *
    rw [ha, hb]
  | single g c =>
    simp only [representationModule_act, Representation.asAlgebraHom_single,
      LinearMap.smul_apply]
    rfl

theorem quotient_compatibility (ρ : Representation k G V) :
    Specs.quotientCompatibility ρ := by
  intro U
  constructor
  · intros; rfl
  · intro a v
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [representationModule_act]
    | add a b ha hb =>
      simp only [representationModule_act, map_add, LinearMap.add_apply] at *
      rw [ha, hb, Submodule.Quotient.mk_add]
    | single g c =>
      simp only [representationModule_act, Representation.asAlgebraHom_single,
        LinearMap.smul_apply]
      rfl

theorem kernelImage_compatibility (ρ : Representation k G V) (σ : Representation k G W) :
    Specs.kernelImageCompatibility ρ σ := by
  intro f
  constructor <;> rfl

theorem irreducible_convention (ρ : Representation k G V) :
    Specs.irreducibleConvention ρ := Iff.rfl

end P103.Ch08
