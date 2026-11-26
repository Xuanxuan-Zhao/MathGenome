import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.InjectiveEnvelope
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Type
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! The common residue-field hull and dual used in Chapters 3 and 4. -/

noncomputable section

open CategoryTheory Opposite

namespace CommutativeAlgebraNotes.MatlisDualFunctorSpecs

universe u v w

def residueFieldEnvelopeType :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], Type (u + 1)

abbrev residueFieldEnvelopeValue (R : Type u) [CommRing R] [IsLocalRing R] :=
  AdvCommAlg.Gorenstein.InjectiveEnvelope R (IsLocalRing.ResidueField R)

variable {R : Type u} [CommRing R] [IsLocalRing R]

def residueFieldEnvelopeExists : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], Nonempty (residueFieldEnvelopeValue R)

def residueFieldEnvelopeEssential : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (N : Submodule R E.carrier), N ≠ ⊥ → N ⊓ LinearMap.range E.inclusion ≠ ⊥

def residueFieldEnvelopeEquiv : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E F : residueFieldEnvelopeValue R),
    ∃ e : E.carrier ≃ₗ[R] F.carrier, e.toLinearMap.comp E.inclusion = F.inclusion

set_option linter.checkUnivs false in
def matlisDualModuleType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (_ : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X], Type (max u v)

abbrev matlisDualModuleValue (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X] :=
  X →ₗ[R] E.carrier

set_option linter.checkUnivs false in
def matlisDualMapType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y],
    (X →ₗ[R] Y) → matlisDualModuleValue E Y →ₗ[R] matlisDualModuleValue E X

def matlisDualMapValue (E : residueFieldEnvelopeValue R)
    {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) : matlisDualModuleValue E Y →ₗ[R] matlisDualModuleValue E X :=
  LinearMap.lcomp R E.carrier f

def matlisDualType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R], residueFieldEnvelopeValue R →
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R

def matlisDualValue (E : residueFieldEnvelopeValue R) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj X := ModuleCat.of R (matlisDualModuleValue E X.unop)
  map f := ModuleCat.ofHom (matlisDualMapValue E f.unop.hom)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

def matlisDualAdditive : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R),
    (matlisDualValue E).Additive

def matlisDualLinear : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R),
    (matlisDualValue E).Linear R

def matlisDualScalar : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {X : Type v} [AddCommGroup X] [Module R X] (r : R) (f : matlisDualModuleValue E X),
    r • f = matlisDualMapValue E (LinearMap.lsmul R X r) f

set_option linter.checkUnivs false in
def matlisEvaluationType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X],
    X →ₗ[R] matlisDualModuleValue E (matlisDualModuleValue E X)

def matlisEvaluationValue (E : residueFieldEnvelopeValue R)
    (X : Type v) [AddCommGroup X] [Module R X] :
    X →ₗ[R] matlisDualModuleValue E (matlisDualModuleValue E X) :=
  LinearMap.applyₗ

def matlisBidualEvaluationType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R),
    𝟭 (ModuleCat.{u} R) ⟶ (matlisDualValue E).rightOp ⋙ matlisDualValue E

def matlisBidualEvaluationValue (E : residueFieldEnvelopeValue R) :
    𝟭 (ModuleCat.{u} R) ⟶ (matlisDualValue E).rightOp ⋙ matlisDualValue E where
  app X := ModuleCat.ofHom (matlisEvaluationValue E X)
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

def matlisDualIsoType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] {E F : residueFieldEnvelopeValue R},
    (E.carrier ≃ₗ[R] F.carrier) → (matlisDualValue E ≅ matlisDualValue F)

def matlisDualIsoValue {E F : residueFieldEnvelopeValue R}
    (e : E.carrier ≃ₗ[R] F.carrier) : matlisDualValue E ≅ matlisDualValue F :=
  NatIso.ofComponents (fun X =>
    (e.congrRight : matlisDualModuleValue E X.unop ≃ₗ[R]
      matlisDualModuleValue F X.unop).toModuleIso)
    (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

def memSocleIff : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Type u} [AddCommGroup X] [Module R X] (x : X),
    x ∈ AdvCommAlg.Depth.Socle R X ↔ ∀ r ∈ IsLocalRing.maximalIdeal R, r • x = 0

def residueSmulSocle : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Type u} [AddCommGroup X] [Module R X] (r : R) (x : AdvCommAlg.Depth.Socle R X),
    IsLocalRing.residue R r • x = r • x

end CommutativeAlgebraNotes.MatlisDualFunctorSpecs
