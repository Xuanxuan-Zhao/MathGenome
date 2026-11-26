import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor

/-! The residue-field hull and scalar restriction along maximal-ideal completion. -/

noncomputable section

namespace Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion

open IsLocalRing
open CompletionOfTorsionModules
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs
open _root_.AdvCommAlg.Gorenstein
open scoped TensorProduct

universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "S" => Completion R
local notation "𝔪" => maximalIdeal R

/-- The canonical isomorphism of residue fields induced by the completion map. -/
def completionResidueEquiv (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ResidueField R ≃ₐ[R] ResidueField (Completion R) := by
  let f := IsScalarTower.toAlgHom R (ResidueField R) (ResidueField (Completion R))
  have hf : (f : ResidueField R → ResidueField (Completion R)) =
      ResidueField.map (algebraMap R (Completion R)) := by
    funext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    rfl
  exact AlgEquiv.ofBijective f (hf.symm ▸ AdicCompletion.residueField_map_bijective R)

def completionResidueEquivType :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    ResidueField R ≃ₐ[R] ResidueField (Completion R)

def completionResidueEquivResidueType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (r : R),
    completionResidueEquiv R (residue R r) = residue (Completion R) (algebraMap R (Completion R) r)

/-- The original ring acts on the hull via its map to the completion. -/
abbrev restrictedHullModule (E : residueFieldEnvelopeValue S) : Module R E.carrier :=
  Module.compHom E.carrier (algebraMap R S)

def restrictedHullModuleType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)), Module R E.carrier

attribute [local instance] restrictedHullModule

theorem restrictedHullScalarTower (E : residueFieldEnvelopeValue S) :
    IsScalarTower R S E.carrier :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] restrictedHullScalarTower

/-- The inclusion of the original residue field into the restricted hull. -/
def restrictedHullInclusion (E : residueFieldEnvelopeValue S) :
    ResidueField R →ₗ[R] E.carrier :=
  (E.inclusion.restrictScalars R).comp (completionResidueEquiv R).toLinearEquiv.toLinearMap

def restrictedHullInclusionType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)), ResidueField R →ₗ[R] E.carrier

def restrictedHullInjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)), Module.Injective R E.carrier

def restrictedHullIsEnvelopeType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)), IsInjectiveEnvelope (restrictedHullInclusion E)

def restrictedHullPowerTorsionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)), IsPowerTorsion R E.carrier

def restrictedHullCompletionModuleType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)) (h : IsPowerTorsion R E.carrier),
    completionModule h = E.module

section Comparisons

variable {T : Type v} [AddCommGroup T] [Module R T] [Module (Completion R) T] [IsScalarTower R (Completion R) T]
variable {U : Type w} [AddCommGroup U] [Module R U] [Module (Completion R) U] [IsScalarTower R (Completion R) U]

/-- The representative of a completed scalar modulo an annihilating power acts identically. -/
private theorem smul_eq_representative {x : T} {n : ℕ} (hx : ∀ a ∈ 𝔪 ^ n, a • x = 0) (s : S) :
    s • x = representative s n • x := by
  let r := representative s n
  let act := LinearMap.toSpanSingleton S T x
  have hle : (𝔪 ^ n).map (algebraMap R S) ≤ act.ker :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => by
      change algebraMap R S a • x = 0
      rw [algebraMap_smul]
      exact hx a ha
  have hdiff : s - algebraMap R S r ∈ (𝔪 ^ n).map (algebraMap R S) := by
    rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map, ← ker_eval]
    change AdicCompletion.evalₐ 𝔪 n (s - algebraMap R S r) = 0
    rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    change AdicCompletion.evalₐ 𝔪 n s - Ideal.Quotient.mk (𝔪 ^ n) r = 0
    rw [mk_representative s n, sub_self]
  have hz := hle hdiff
  change (s - algebraMap R S r) • x = 0 at hz
  simpa only [sub_smul, algebraMap_smul, sub_eq_zero] using hz

/-- Restriction of scalars is an order isomorphism on submodules of a power-torsion module. -/
def powerTorsionSubmoduleEquiv (hT : IsPowerTorsion R T) : Submodule S T ≃o Submodule R T where
  toFun := Submodule.restrictScalars R
  invFun P :=
    { carrier := P
      zero_mem' := P.zero_mem
      add_mem' := P.add_mem
      smul_mem' := fun s x hx => by
        obtain ⟨n, hn⟩ := exists_killing_power hT x
        rw [smul_eq_representative hn s]
        exact P.smul_mem _ hx }
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl
  map_rel_iff' := Iff.rfl

set_option linter.checkUnivs false in
def powerTorsionSubmoduleEquivType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] [Module (Completion R) T]
    [IsScalarTower R (Completion R) T], IsPowerTorsion R T → Submodule (Completion R) T ≃o Submodule R T

def powerTorsionArtinianIffType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] [Module (Completion R) T]
    [IsScalarTower R (Completion R) T], IsPowerTorsion R T → (IsArtinian R T ↔ IsArtinian (Completion R) T)

/-- Restriction of scalars on maps from a power-torsion module, linear over the completion. -/
def powerTorsionHomEquiv (hT : IsPowerTorsion R T) : (T →ₗ[S] U) ≃ₗ[S] (T →ₗ[R] U) where
  toFun f := f.restrictScalars R
  invFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun s x => by
        change f (s • x) = s • f x
        obtain ⟨n, hx⟩ := exists_killing_power hT x
        have hy : ∀ a ∈ 𝔪 ^ n, a • f x = 0 := by
          intro a ha
          rw [← f.map_smul, hx a ha, map_zero]
        rw [smul_eq_representative hx s, smul_eq_representative hy s, f.map_smul] }
  left_inv _ := LinearMap.ext fun _ => rfl
  right_inv _ := LinearMap.ext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl

set_option linter.checkUnivs false in
def powerTorsionHomEquivType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {T : Type v} [AddCommGroup T] [Module R T] [Module (Completion R) T]
    [IsScalarTower R (Completion R) T]
    {U : Type w} [AddCommGroup U] [Module R U] [Module (Completion R) U]
    [IsScalarTower R (Completion R) U],
    IsPowerTorsion R T → (T →ₗ[Completion R] U) ≃ₗ[Completion R] (T →ₗ[R] U)

end Comparisons

/-- Comparing the two Matlis duals of an original power-torsion module. -/
def completedMatlisDualEquiv (E : residueFieldEnvelopeValue S)
    {T : Type v} [AddCommGroup T] [Module R T] (hT : IsPowerTorsion R T) :
    letI := completionModule hT
    (T →ₗ[R] E.carrier) ≃ₗ[S] matlisDualModuleValue E T := by
  letI := completionModule hT
  letI := completionScalarTower hT
  exact (powerTorsionHomEquiv hT).symm

set_option linter.checkUnivs false in
def completedMatlisDualEquivType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R))
    {T : Type v} [AddCommGroup T] [Module R T] (hT : IsPowerTorsion R T),
    letI := completionModule hT
    (T →ₗ[R] E.carrier) ≃ₗ[Completion R] matlisDualModuleValue E T

def completedMatlisDualEquivApplyType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R))
    {T : Type v} [AddCommGroup T] [Module R T] (hT : IsPowerTorsion R T)
    (f : T →ₗ[R] E.carrier) (x : T), completedMatlisDualEquiv E hT f x = f x

def completedMatlisDualEquivNaturalityType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R))
    {T : Type v} [AddCommGroup T] [Module R T] (hT : IsPowerTorsion R T)
    {U : Type w} [AddCommGroup U] [Module R U] (hU : IsPowerTorsion R U)
    (g : T →ₗ[R] U) (f : U →ₗ[R] E.carrier),
    letI := completionModule hT
    letI := completionModule hU
    letI := completionScalarTower hT
    letI := completionScalarTower hU
    completedMatlisDualEquiv E hT (f.comp g) =
      (completedMatlisDualEquiv E hU f).comp ((powerTorsionHomEquiv hT).symm g)

/-- The extension-restriction Hom adjunction with the hull as codomain. -/
def completedHullHomAdjunction (E : residueFieldEnvelopeValue S)
    (X : Type v) [AddCommGroup X] [Module R X] :
    (X →ₗ[R] E.carrier) ≃ₗ[S] matlisDualModuleValue E (S ⊗[R] X) :=
  LinearMap.liftBaseChangeEquiv S

set_option linter.checkUnivs false in
def completedHullHomAdjunctionType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R)) (X : Type v) [AddCommGroup X] [Module R X],
    (X →ₗ[R] E.carrier) ≃ₗ[Completion R] matlisDualModuleValue E (Completion R ⊗[R] X)

def completedHullHomAdjunctionTmulType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue (Completion R))
    {X : Type v} [AddCommGroup X] [Module R X]
    (f : X →ₗ[R] E.carrier) (s : Completion R) (x : X),
    completedHullHomAdjunction E X f (s ⊗ₜ[R] x) = s • f x

end Specs.CommutativeAlgebraNotes.MatlisHullUnderCompletion
