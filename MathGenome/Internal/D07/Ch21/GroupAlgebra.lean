import MathGenome.Internal.D07.Ch17.Definition
import MathGenome.Internal.D07.Ch17.SubrepresentationsQuotients
import MathGenome.Internal.D07.Ch17.IntertwinersEquivalence
import MathGenome.Internal.Specs.D07.Ch21.GroupAlgebra

/-!
The complex group algebra, its universal property, and its modules.
All action formulas use the original complex scalar structure. In particular,
there is no nontriviality or finite-dimensionality condition on the module.
-/
namespace D07.Ch21.GroupAlgebra

universe u v w

open Specs.D07.Ch21.GroupAlgebra

noncomputable section

theorem basis_description : BasisDescription.{u} := by
  intro G _ _
  refine ⟨MonoidAlgebra.basis G ℂ, fun _ => rfl, fun _ => rfl, ?_⟩
  intro a
  exact (MonoidAlgebra.basis G ℂ).sum_repr a |>.symm

theorem algebra_laws : AlgebraLaws.{u} := by
  intro G _ _
  refine ⟨MonoidAlgebra.single_mul_single, rfl, ?_, mul_assoc, add_mul, mul_add,
    ?_, ?_⟩
  · exact one_ne_zero
  · intro c a b
    exact ⟨smul_mul_assoc c a b, mul_smul_comm c a b⟩
  · intro c a
    exact ⟨rfl, Algebra.commutes c a⟩

theorem dimension : Dimension.{u} := by
  intro G _ _
  exact ⟨Module.Finite.of_basis (MonoidAlgebra.basis G ℂ),
    Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ)⟩

theorem extension_unique : ExtensionUnique.{u,v} := by
  intro G V _ _ _ _ ρ
  refine ⟨ρ.asAlgebraHom, ρ.asAlgebraHom_single_one, ?_⟩
  intro F hF
  apply (MonoidAlgebra.lift ℂ (Module.End ℂ V) G).symm.injective
  exact MonoidHom.ext fun g => (hF g).trans (ρ.asAlgebraHom_single_one g).symm

theorem extension_formula : ExtensionFormula.{u,v} := by
  intro G V _ _ _ _ ρ
  have formula (a : MonoidAlgebra ℂ G) :
      ρ.asAlgebraHom a = ∑ g : G, a.coeff g • ρ g := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
    exact Finsupp.sum_fintype _ _ (by intro g; simp)
  refine ⟨formula, ?_, ?_⟩
  · intro a x
    simp only [formula, LinearMap.sum_apply, LinearMap.smul_apply]
  · intro a b
    rw [map_mul, formula a, formula b]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, ← map_mul]
    exact Finset.sum_comm

/-- A module with its specified complex scalars gives the required scalar tower. -/
private theorem compatibleScalarTower {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] (m : CompatibleModule G V) :
    letI := m.module
    IsScalarTower ℂ (MonoidAlgebra ℂ G) V := by
  letI := m.module
  exact ⟨fun c a x => by
    rw [Algebra.smul_def, mul_smul, m.scalar_eq]⟩

/-- Regard the action of a compatible unital module as a representation. -/
private def representationOfModule {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] (m : CompatibleModule G V) : Representation ℂ G V :=
  letI := m.module
  letI := compatibleScalarTower m
  Representation.ofModule' V

private theorem representationOfModule_apply {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] (m : CompatibleModule G V) (g : G) (x : V) :
    representationOfModule m g x = m.act (MonoidAlgebra.single g 1) x := rfl

private theorem extension_representationOfModule {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] (m : CompatibleModule G V) (a : MonoidAlgebra ℂ G)
    (x : V) : (representationOfModule m).asAlgebraHom a x = m.act a x := by
  letI := m.module
  letI := compatibleScalarTower m
  change (MonoidAlgebra.lift ℂ (Module.End ℂ V) G
    ((MonoidAlgebra.lift ℂ (Module.End ℂ V) G).symm (Algebra.lsmul ℂ ℂ V))) a x = _
  rw [Equiv.apply_symm_apply]
  rfl

private def moduleOfRepresentation {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : CompatibleModule G V where
  module := Module.compHom V ρ.asAlgebraHom.toRingHom
  scalar_eq := by
    intro c x
    change ρ.asAlgebraHom (algebraMap ℂ (MonoidAlgebra ℂ G) c) x = c • x
    rw [AlgHom.commutes]
    rfl

private theorem moduleOfRepresentation_act {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (a : MonoidAlgebra ℂ G) (x : V) :
    (moduleOfRepresentation ρ).act a x = ρ.asAlgebraHom a x := rfl

theorem module_correspondence : ModuleCorrespondence.{u,v} := by
  intro G V _ _ _ _
  let e : Representation ℂ G V ≃ CompatibleModule G V := {
    toFun := moduleOfRepresentation
    invFun := representationOfModule
    left_inv := fun ρ => by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro x
      rw [representationOfModule_apply, moduleOfRepresentation_act,
        Representation.asAlgebraHom_single_one]
    right_inv := fun m => by
      have hm : (moduleOfRepresentation (representationOfModule m)).module = m.module := by
        apply Module.ext'
        exact extension_representationOfModule m
      exact CompatibleModule.ext hm
  }
  refine ⟨e, moduleOfRepresentation_act, representationOfModule_apply, ?_⟩
  intro m g x
  simpa only [representationOfModule_apply] using
    ⟨(representationOfModule m).self_inv_apply g x,
      (representationOfModule m).inv_self_apply g x⟩

theorem invariant_iff_algebra_stable : InvariantIffAlgebraStable.{u,v} := by
  intro G V _ _ _ _ ρ U
  constructor
  · intro h a x hx
    rw [(extension_formula G V ρ).2.1]
    exact U.sum_mem (fun g _ => U.smul_mem _ (h g x hx))
  · intro h g x hx
    simpa using h (MonoidAlgebra.single g 1) x hx

theorem submodule_correspondence : SubmoduleCorrespondence.{u,v} := by
  intro G V _ _ _ _ ρ U
  constructor
  · intro h
    have stable := (invariant_iff_algebra_stable G V ρ U).mp h
    let W : Submodule (MonoidAlgebra ℂ G) ρ.asModule := {
      carrier := {x | ρ.asModuleEquiv x ∈ U}
      zero_mem' := U.zero_mem
      add_mem' := fun hx hy => U.add_mem hx hy
      smul_mem' := fun a x hx => by
        rw [Set.mem_ofPred_eq, Representation.asModuleEquiv_map_smul]
        exact stable a _ hx
    }
    refine ⟨W, fun _ => Iff.rfl, ?_⟩
    intro W' hW'
    exact Submodule.ext fun x => hW' x
  · rintro ⟨W, hW, _⟩
    intro g x hx
    have hxW : ρ.asModuleEquiv.symm x ∈ W := (hW _).mpr (by simpa using hx)
    have hmem := W.smul_mem (MonoidAlgebra.single g 1) hxW
    have := (hW _).mp hmem
    simpa only [Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single_one, LinearEquiv.apply_symm_apply] using this

theorem equivariant_iff_algebra_linear : EquivariantIffAlgebraLinear.{u,v,w} := by
  intro G V W _ _ _ _ _ _ ρ σ T
  constructor
  · intro h a x
    simp only [(extension_formula G V ρ).2.1, (extension_formula G W σ).2.1,
      map_sum, map_smul, h.isIntertwining]
  · intro h
    exact ⟨fun g x => by simpa using h (MonoidAlgebra.single g 1) x⟩

theorem module_map_correspondence : ModuleMapCorrespondence.{u,v,w} := by
  intro G V W _ _ _ _ _ _ ρ σ T
  constructor
  · intro h
    let f : ρ.IntertwiningMap σ := ⟨T, fun g => LinearMap.ext (h.isIntertwining g)⟩
    refine ⟨Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f,
      fun _ => rfl, ?_⟩
    intro f' hf'
    apply LinearMap.ext
    intro x
    apply σ.asModuleEquiv.injective
    exact hf' x
  · rintro ⟨f, hf, _⟩
    apply (equivariant_iff_algebra_linear G V W ρ σ T).mpr
    intro a x
    have hsmul := congrArg (fun y => σ.asModuleEquiv y)
      (f.map_smul a (ρ.asModuleEquiv.symm x))
    simpa only [Representation.asModuleEquiv_map_smul, hf,
      LinearEquiv.apply_symm_apply] using hsmul

theorem trivial_group_algebra : TrivialGroupAlgebra.{u} := by
  intro G _ _ _
  exact ⟨MonoidAlgebra.uniqueAlgEquiv ℂ G, fun _ => rfl,
    MonoidAlgebra.uniqueAlgEquiv_symm_apply ℂ G⟩

end
end D07.Ch21.GroupAlgebra
