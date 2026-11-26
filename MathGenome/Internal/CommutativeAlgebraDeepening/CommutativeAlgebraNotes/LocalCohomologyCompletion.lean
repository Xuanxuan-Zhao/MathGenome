import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedTorsion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyBaseChange
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedNoetherian

open CategoryTheory
open scoped ChangeOfRings TensorProduct

namespace CommutativeAlgebraNotes

universe u v

open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion IsPowerTorsion)
open Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion
  (CompletionComparison FiniteTensorComparison FiniteCompletionComparison finiteModules)
open CompletionOfTorsionModules
  (completionModule completionTensorEquiv completionTensorEquiv_tmul)

local notation "𝔪[" R "]" => IsLocalRing.maximalIdeal R

/-- A functor with maximal-ideal power-torsion values, with its canonical completed action. -/
noncomputable abbrev completedAction {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (F : ModuleCat.{v} R ⥤ ModuleCat.{v} R)
    (h : ∀ M, IsPowerTorsion R (F.obj M)) : ModuleCat.{v} R ⥤ ModuleCat.{v} (Completion R) :=
  Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion.completedAction F h

/-- The adic completion of modules and linear maps. -/
noncomputable abbrev adicCompletionFunctor (R : Type u) [CommRing R] [IsLocalRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (Completion R) :=
  Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion.adicCompletionFunctor R

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "S" => Completion R
local notation "ι" => algebraMap R S
private noncomputable abbrev completionExtension : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  ModuleCat.extendScalars ι

local notation "E" => completionExtension (R := R)

/-- The tensor used by extension of scalars with its left factor expressed
using the canonical algebra structure of the completion. -/
private noncomputable def extensionTensorEquiv (M : ModuleCat.{u} R) :
    ↥((E).obj M) ≃ₗ[S] S ⊗[R] M := by
  letI : IsScalarTower R S ↥((ModuleCat.restrictScalars ι).obj (ModuleCat.of S S)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e : ↥((ModuleCat.restrictScalars ι).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
    LinearEquiv.refl S S
  exact TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R M)

omit [IsNoetherianRing R] in
private theorem extensionTensorEquiv_tmul (M : ModuleCat.{u} R) (s : S) (x : M) :
    extensionTensorEquiv M (s ⊗ₜ[R, ι] x) = s ⊗ₜ[R] x :=
  rfl

/-- On power-torsion values, tensor extension is identified with the action on
the original module by tensor multiplication, naturally in the input. -/
private noncomputable def torsionTensorIso (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    (h : ∀ M, IsPowerTorsion R (F.obj M)) : F ⋙ E ≅ completedAction F h := by
  let e (M : ModuleCat.{u} R) : (F ⋙ E).obj M ≅ (completedAction F h).obj M :=
    letI := completionModule (h M)
    ((extensionTensorEquiv (F.obj M)).trans (completionTensorEquiv (h M))).toModuleIso
  have he (M : ModuleCat.{u} R) (x : F.obj M) :
      (e M).hom ((1 : S) ⊗ₜ[R, ι] x) = x := by
    let := completionModule (h M)
    change (completionTensorEquiv (h M))
      (extensionTensorEquiv (F.obj M) ((1 : S) ⊗ₜ[R, ι] x)) = x
    rw [extensionTensorEquiv_tmul, completionTensorEquiv_tmul, one_smul]
  refine NatIso.ofComponents e ?_
  intro M N f
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (e N).hom ((1 : S) ⊗ₜ[R, ι] F.map f x) =
    F.map f ((e M).hom ((1 : S) ⊗ₜ[R, ι] x))
  exact (he N _).trans (congrArg (F.map f) (he M x)).symm

end

/-- Local cohomology over a Noetherian local ring, with the canonical completed
action, agrees naturally with local cohomology of the scalar extension. -/
theorem localCohomologyCompletion : CompletionComparison.{u} := by
  intro R _ _ _ q
  let I := 𝔪[R]
  let S := Completion R
  let f := algebraMap R S
  have h (M : ModuleCat.{u} R) : IsPowerTorsion R ((localCohomology I q).obj M) := by
    intro x
    exact (mem_idealTorsion I x).mpr (localCohomology_isPowerTorsion I q M x)
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let := P103.Ch07.CompletedNoetherian.completed_noetherian R I
  obtain ⟨baseChange⟩ := localCohomologyFlatBaseChange f hf I q
  refine ⟨h, ⟨?_⟩⟩
  simpa only [AdicCompletion.maximalIdeal_eq_map] using
    (torsionTensorIso (localCohomology I q) h).symm ≪≫ baseChange

/-- For finite modules, the tensor model of completion is canonically
isomorphic to the adic completion. -/
theorem finiteTensorCompletion : FiniteTensorComparison.{u} := by
  intro R _ _ _
  let I := 𝔪[R]
  let S := Completion R
  let f := algebraMap R S
  let E := ModuleCat.extendScalars.{u, u, u} f
  let e (M : (finiteModules R).FullSubcategory) :
      ((finiteModules R).ι ⋙ E).obj M ≅ ((finiteModules R).ι ⋙ adicCompletionFunctor R).obj M :=
    letI : Module.Finite R M.obj := M.property
    ((extensionTensorEquiv M.obj).trans
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M.obj)).toModuleIso
  have he (M : (finiteModules R).FullSubcategory) (s : S) (x : M.obj) :
      (e M).hom (s ⊗ₜ[R, f] x) = s • AdicCompletion.of I M.obj x := by
    let := M.property
    change AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M.obj
      (extensionTensorEquiv M.obj (s ⊗ₜ[R, f] x)) = _
    rw [extensionTensorEquiv_tmul, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
      AdicCompletion.ofTensorProduct_tmul]
  refine ⟨NatIso.ofComponents e ?_, he⟩
  intro M N g
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (e N).hom ((1 : S) ⊗ₜ[R, f] g.hom x) =
    AdicCompletion.map I g.hom.hom ((e M).hom ((1 : S) ⊗ₜ[R, f] x))
  have hN : (e N).hom ((1 : S) ⊗ₜ[R, f] g.hom x) =
      AdicCompletion.of I N.obj (g.hom x) := (he N 1 _).trans (one_smul _ _)
  have hM : (e M).hom ((1 : S) ⊗ₜ[R, f] x) =
      AdicCompletion.of I M.obj x := (he M 1 x).trans (one_smul _ _)
  exact hN.trans ((AdicCompletion.map_of I g.hom.hom x).symm.trans
    (congrArg (fun y : AdicCompletion I M.obj => AdicCompletion.map I g.hom.hom y) hM.symm))

/-- The comparison for a finite coefficient module uses its actual
maximal-ideal-adic completion. -/
theorem localCohomologyFiniteCompletion : FiniteCompletionComparison.{u} := by
  intro R _ _ _ q
  obtain ⟨h, ⟨comparison⟩⟩ := localCohomologyCompletion (R := R) q
  obtain ⟨tensorCompletion, _⟩ := finiteTensorCompletion (R := R)
  exact ⟨h, ⟨Functor.isoWhiskerLeft (finiteModules R).ι comparison ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight tensorCompletion _ ≪≫ Functor.associator _ _ _⟩⟩

end CommutativeAlgebraNotes
