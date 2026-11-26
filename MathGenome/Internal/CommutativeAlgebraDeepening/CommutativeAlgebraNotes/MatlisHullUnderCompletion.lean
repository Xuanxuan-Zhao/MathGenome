import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveHullTruncations
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedNoetherian

/-! Restriction of the residue-field injective hull along maximal-ideal completion. -/

noncomputable section

namespace CommutativeAlgebraNotes.MatlisHullUnderCompletion

open IsLocalRing
open AdvCommAlg.Gorenstein
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion IsPowerTorsion)
open scoped TensorProduct

universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "S" => Completion R

/-- The residue-field isomorphism induced by the completion map. -/
abbrev completionResidueEquiv (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ResidueField R ≃ₐ[R] ResidueField (Completion R) :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.completionResidueEquiv R

@[simp]
theorem completionResidueEquiv_residue (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (r : R) :
    completionResidueEquiv R (residue R r) = residue (Completion R) (algebraMap R (Completion R) r) :=
  rfl

/-- The original ring acts via its algebra map to the completion. -/
abbrev restrictedHullModule (E : ResidueFieldEnvelope S) : Module R E.carrier :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.restrictedHullModule E

attribute [local instance] restrictedHullModule

theorem restrictedHullScalarTower (E : ResidueFieldEnvelope S) :
    IsScalarTower R S E.carrier :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.restrictedHullScalarTower E

attribute [local instance] restrictedHullScalarTower

/-- The original residue field maps into the completed hull via the residue-field isomorphism. -/
abbrev restrictedHullInclusion (E : ResidueFieldEnvelope S) :
    ResidueField R →ₗ[R] E.carrier :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.restrictedHullInclusion E

section Comparisons

variable {T : Type v} [AddCommGroup T] [Module R T] [Module (Completion R) T]
  [IsScalarTower R (Completion R) T]
variable {U : Type w} [AddCommGroup U] [Module R U] [Module (Completion R) U]
  [IsScalarTower R (Completion R) U]

/-- For power-torsion modules, restriction preserves the entire submodule lattice. -/
abbrev powerTorsionSubmoduleEquiv (hT : IsPowerTorsion R T) :
    Submodule S T ≃o Submodule R T :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.powerTorsionSubmoduleEquiv hT

@[simp]
theorem powerTorsionSubmoduleEquiv_apply (hT : IsPowerTorsion R T) (P : Submodule S T) :
    powerTorsionSubmoduleEquiv hT P = P.restrictScalars R :=
  rfl

theorem powerTorsion_artinian_iff (hT : IsPowerTorsion R T) :
    IsArtinian R T ↔ IsArtinian S T := by
  let e := (powerTorsionSubmoduleEquiv hT).toRelIsoLT
  exact ⟨RelHomClass.wellFounded e, RelHomClass.wellFounded e.symm⟩

/-- Restriction identifies completed-linear and original-linear maps from a power-torsion module. -/
abbrev powerTorsionHomEquiv (hT : IsPowerTorsion R T) :
    (T →ₗ[S] U) ≃ₗ[S] (T →ₗ[R] U) :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.powerTorsionHomEquiv hT

@[simp]
theorem powerTorsionHomEquiv_symm_apply (hT : IsPowerTorsion R T) (f : T →ₗ[R] U) (x : T) :
    (powerTorsionHomEquiv hT).symm f x = f x :=
  rfl

end Comparisons

/-- The extension-restriction Hom adjunction with the completed hull as codomain. -/
abbrev completedHullHomAdjunction (E : ResidueFieldEnvelope S)
    (X : Type v) [AddCommGroup X] [Module R X] :
    (X →ₗ[R] E.carrier) ≃ₗ[S] MatlisDualModule E (S ⊗[R] X) :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.completedHullHomAdjunction E X

@[simp]
theorem completedHullHomAdjunction_tmul (E : ResidueFieldEnvelope S)
    {X : Type v} [AddCommGroup X] [Module R X] (f : X →ₗ[R] E.carrier) (s : S) (x : X) :
    completedHullHomAdjunction E X f (s ⊗ₜ[R] x) = s • f x :=
  rfl

theorem restrictedHull_injective (E : ResidueFieldEnvelope S) :
    Module.Injective R E.carrier := by
  let : Module.Injective S E.carrier := E.isEnvelope.injectiveModule
  refine ⟨?_⟩
  intro X Y _ _ _ _ f hf g
  have hbase : Function.Injective (f.baseChange S) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) f hf
  obtain ⟨g', hg⟩ := Module.Injective.out (f.baseChange S) hbase
    (completedHullHomAdjunction E X g)
  refine ⟨(completedHullHomAdjunction E Y).symm g', fun x => ?_⟩
  change g' (1 ⊗ₜ[R] f x) = g x
  simpa only [LinearMap.baseChange_tmul, completedHullHomAdjunction_tmul, one_smul] using
      hg ((1 : S) ⊗ₜ[R] x)

theorem restrictedHull_powerTorsion (E : ResidueFieldEnvelope S) :
    IsPowerTorsion R E.carrier := by
  let : IsNoetherianRing S := P103.Ch07.CompletedNoetherian.completed_noetherian R (maximalIdeal R)
  apply CompletionOfTorsionModules.powerTorsion_restrictScalars
  intro x
  obtain ⟨n, hn, hx⟩ := exists_mem_hullTruncation E x
  refine (mem_idealTorsion (maximalIdeal S) x).2 ⟨n, hn, fun a ha => ?_⟩
  exact (Submodule.mem_torsionBySet_iff (↑(maximalIdeal S ^ n) : Set S) x).mp hx ⟨a, ha⟩

/-- Completing the restricted action recovers the original action of the completed ring. -/
theorem restrictedHull_completionModule (E : ResidueFieldEnvelope S)
    (h : IsPowerTorsion R E.carrier) :
    CompletionOfTorsionModules.completionModule h = E.module :=
  (CompletionOfTorsionModules.completionModule_unique h E.module (fun _ _ => rfl)).symm

/-- The restricted inclusion still exhibits an injective envelope of the residue field. -/
theorem restrictedHull_isEnvelope (E : ResidueFieldEnvelope S) :
    IsInjectiveEnvelope (restrictedHullInclusion E) := by
  refine ⟨E.isEnvelope.injective.comp (completionResidueEquiv R).injective,
    restrictedHull_injective E, ?_⟩
  let e := powerTorsionSubmoduleEquiv (restrictedHull_powerTorsion E)
  intro P hP
  have hP' : e.symm P ≠ ⊥ := by
    intro he
    apply hP
    calc
      P = e (e.symm P) := (e.apply_symm_apply P).symm
      _ = ⊥ := by rw [he, map_bot]
  have hrange : e (LinearMap.range E.inclusion) = LinearMap.range (restrictedHullInclusion E) := by
    ext x
    change (∃ y, E.inclusion y = x) ↔ ∃ z, E.inclusion (completionResidueEquiv R z) = x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := (completionResidueEquiv R).surjective y
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨completionResidueEquiv R z, rfl⟩
  rw [← hrange, ← e.apply_symm_apply P, ← map_inf, ← map_bot e]
  exact fun he => E.isEnvelope.essential _ hP' (e.injective he)

/-- The completed hull, regarded as a residue-field envelope over the original ring. -/
abbrev restrictResidueFieldEnvelope (E : ResidueFieldEnvelope S) : ResidueFieldEnvelope R where
  carrier := E.carrier
  addCommGroup := E.addCommGroup
  module := restrictedHullModule E
  inclusion := restrictedHullInclusion E
  isEnvelope := restrictedHull_isEnvelope E

/-- The two Matlis duals of a power-torsion module agree as modules over the completion. -/
abbrev completedMatlisDualEquiv (E : ResidueFieldEnvelope S)
    {T : Type v} [AddCommGroup T] [Module R T] (hT : IsPowerTorsion R T) :
    letI := CompletionOfTorsionModules.completionModule hT
    MatlisDualModule (restrictResidueFieldEnvelope E) T ≃ₗ[S] MatlisDualModule E T :=
  Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion.completedMatlisDualEquiv E hT

@[simp]
theorem completedMatlisDualEquiv_apply (E : ResidueFieldEnvelope S)
    {T : Type v} [AddCommGroup T] [Module R T] (hT : IsPowerTorsion R T)
    (f : MatlisDualModule (restrictResidueFieldEnvelope E) T) (x : T) :
    completedMatlisDualEquiv E hT f x = f x :=
  rfl

theorem completedMatlisDualEquiv_naturality (E : ResidueFieldEnvelope S)
    {T : Type v} [AddCommGroup T] [Module R T] (hT : IsPowerTorsion R T)
    {U : Type w} [AddCommGroup U] [Module R U] (hU : IsPowerTorsion R U)
    (g : T →ₗ[R] U) (f : MatlisDualModule (restrictResidueFieldEnvelope E) U) :
    letI := CompletionOfTorsionModules.completionModule hT
    letI := CompletionOfTorsionModules.completionModule hU
    completedMatlisDualEquiv E hT (matlisDualMap (restrictResidueFieldEnvelope E) g f) =
      matlisDualMap E (CompletionOfTorsionModules.completionLinearMap hT hU g)
        (completedMatlisDualEquiv E hU f) := by
  let := CompletionOfTorsionModules.completionModule hT
  let := CompletionOfTorsionModules.completionModule hU
  exact LinearMap.ext fun _ => rfl

end CommutativeAlgebraNotes.MatlisHullUnderCompletion
