import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtExactSequences
import Mathlib.LinearAlgebra.Prod

/-! Classification and naturality in paper.tex 2837–2887 (Baer addition has
its own goal). All modules are left modules over an arbitrary unital ring.
A common adequate universe is used for the quotients and projective terms.
There are no finiteness, commutativity, or nonzero-ring assumptions. -/
namespace P103.Specs.Ch11.ExtensionClassification
open CategoryTheory
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Horseshoe
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtExactSequences
noncomputable section
universe u v
variable {R : Type u} [Ring R]

/-- Both endpoint maps are part of an extension's data. -/
structure ExtensionData (A B : ModuleCat.{v} R) where
  middle : ModuleCat.{v} R
  i : B →ₗ[R] middle
  p : middle →ₗ[R] A

def ExtensionData.IsShortExact {A B : ModuleCat.{v} R} (E : ExtensionData A B) : Prop :=
  Function.Injective E.i ∧ Function.Exact E.i E.p ∧ Function.Surjective E.p

abbrev Extension (A B : ModuleCat.{v} R) :=
  {E : ExtensionData A B // E.IsShortExact}

namespace Extension
variable {A B : ModuleCat.{v} R}
abbrev middle (E : Extension A B) := E.val.middle
abbrev i (E : Extension A B) := E.val.i
abbrev p (E : Extension A B) := E.val.p
abbrev injective (E : Extension A B) := E.property.1
abbrev exact (E : Extension A B) := E.property.2.1
abbrev surjective (E : Extension A B) := E.property.2.2

def Equivalent (E F : Extension A B) : Prop :=
  ∃ e : E.middle ≃ₗ[R] F.middle,
    e.toLinearMap.comp E.i = F.i ∧ F.p.comp e.toLinearMap = E.p

instance extensionSetoid : Setoid (Extension A B) where
  r := Equivalent
  iseqv := ⟨fun E => ⟨LinearEquiv.refl R _, by ext; rfl, by ext; rfl⟩,
    by
      rintro E F ⟨e, hi, hp⟩
      refine ⟨e.symm, ?_, ?_⟩
      · ext b
        apply e.injective
        simpa using (LinearMap.congr_fun hi b).symm
      · ext y
        simpa using (LinearMap.congr_fun hp (e.symm y)).symm,
    by
      rintro E F G ⟨e, hei, hep⟩ ⟨f, hfi, hfp⟩
      refine ⟨e.trans f, ?_, ?_⟩
      · ext b
        change f (e (E.i b)) = G.i b
        have he : e (E.i b) = F.i b := LinearMap.congr_fun hei b
        have hf : f (F.i b) = G.i b := LinearMap.congr_fun hfi b
        rw [he, hf]
      · ext x
        change G.p (f (e x)) = E.p x
        have hf : G.p (f (e x)) = F.p (e x) := LinearMap.congr_fun hfp (e x)
        exact hf.trans (LinearMap.congr_fun hep x)⟩

def IsSplit (E : Extension A B) : Prop :=
  ∃ s : A →ₗ[R] E.middle, E.p.comp s = LinearMap.id
end Extension

abbrev ExtensionClasses (A B : ModuleCat.{v} R) := Quotient (Extension.extensionSetoid (A := A) (B := B))

def extensionClass {A B : ModuleCat.{v} R} (E : Extension A B) : ExtensionClasses A B :=
  Quotient.mk _ E

/-- A presentation retains its actual kernel map, not merely an abstract K. -/
structure Presentation (A : ModuleCat.{v} R) where
  K : ModuleCat.{v} R
  P : ModuleCat.{v} R
  j : K →ₗ[R] P
  ε : P →ₗ[R] A
  injective : Function.Injective j
  exact : Function.Exact j ε
  surjective : Function.Surjective ε
  projective : Module.Projective R P

variable {A B : ModuleCat.{v} R}

def restriction (S : Presentation A) (B : ModuleCat.{v} R) :
    (S.P →ₗ[R] B) →ₗ[ℤ] (S.K →ₗ[R] B) :=
  (P103.HomTensorExactness.pre S.j).toIntLinearMap

abbrev PresentationCoker (S : Presentation A) (B : ModuleCat.{v} R) :=
  (S.K →ₗ[R] B) ⧸ LinearMap.range (restriction S B)

/-- Relation with the sign used in the source's pushout formula. -/
def graphRelation (S : Presentation A) (φ : S.K →ₗ[R] B) :
    S.K →ₗ[R] B × S.P := φ.prod (-S.j)

abbrev GraphModule (S : Presentation A) (φ : S.K →ₗ[R] B) :=
  (B × S.P) ⧸ LinearMap.range (graphRelation S φ)

def graphData (S : Presentation A) (φ : S.K →ₗ[R] B) : ExtensionData A B where
  middle := ModuleCat.of R (GraphModule S φ)
  i := (LinearMap.range (graphRelation S φ)).mkQ.comp (LinearMap.inl R B S.P)
  p := (LinearMap.range (graphRelation S φ)).liftQ
    (S.ε.comp (LinearMap.snd R B S.P)) (by
      rintro _ ⟨k, rfl⟩
      change S.ε (-S.j k) = 0
      rw [map_neg, (S.exact (S.j k)).mpr ⟨k, rfl⟩, neg_zero])

/-- Restricting a lift determines φ uniquely through the embedded B. -/
def IsLiftRepresentative (S : Presentation A) (E : Extension A B)
    (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B) : Prop :=
  E.p.comp l = S.ε ∧ E.i.comp φ = l.comp S.j

/-- A coefficient pushout is the actual quotient (B' × E)/im(β,-i). -/
def pushoutRelation {B' : ModuleCat.{v} R} (E : Extension A B) (β : B ⟶ B') :
    B →ₗ[R] B' × E.middle := β.hom.prod (-E.i)

abbrev PushoutModule {B' : ModuleCat.{v} R} (E : Extension A B) (β : B ⟶ B') :=
  (B' × E.middle) ⧸ LinearMap.range (pushoutRelation E β)

def pushoutData {B' : ModuleCat.{v} R} (E : Extension A B) (β : B ⟶ B') :
    ExtensionData A B' where
  middle := ModuleCat.of R (PushoutModule E β)
  i := (LinearMap.range (pushoutRelation E β)).mkQ.comp (LinearMap.inl R B' E.middle)
  p := (LinearMap.range (pushoutRelation E β)).liftQ
    (E.p.comp (LinearMap.snd R B' E.middle)) (by
      rintro _ ⟨b, rfl⟩
      change E.p (-E.i b) = 0
      rw [map_neg, (E.exact (E.i b)).mpr ⟨b, rfl⟩, neg_zero])

/-- The pullback consists of pairs (e,a') with p(e)=α(a'). -/
def pullbackSubmodule {A' : ModuleCat.{v} R} (E : Extension A B) (α : A' ⟶ A) :
    Submodule R (E.middle × A') :=
  LinearMap.ker ((E.p.comp (LinearMap.fst R E.middle A')) -
    (α.hom.comp (LinearMap.snd R E.middle A')))

def pullbackData {A' : ModuleCat.{v} R} (E : Extension A B) (α : A' ⟶ A) :
    ExtensionData A' B where
  middle := ModuleCat.of R (pullbackSubmodule E α)
  i := (E.i.prod (0 : B →ₗ[R] A')).codRestrict _ (by
    intro b
    change E.p (E.i b) - α.hom 0 = 0
    rw [(E.exact (E.i b)).mpr ⟨b, rfl⟩, map_zero, sub_zero])
  p := (LinearMap.snd R E.middle A').comp (pullbackSubmodule E α).subtype

/-- A specified value in Ext is the positive second connecting image of 1_A,
for every connector having the upstream defining formula. -/
def RepresentsConnector {A B : ModuleCat.{v} R} (Q : LeftResolution R A)
    (e : ExtensionClasses A B ≃ ExtWith Q B 1) : Prop :=
  ∀ (E : Extension A B)
    (δ : ExtWith Q A 0 →ₗ[ℤ] ExtWith Q B 1),
    SecondConnecting Q (ModuleCat.ofHom E.i) (ModuleCat.ofHom E.p) 0 δ →
      e (extensionClass E) = δ (homClass Q A LinearMap.id)

/-- Fix the presentation isomorphism by the negative of the positive first
connector. Precomposition reverses the short exact sequence: the horseshoe
upper-right block has the negative sign. This normalization agrees with the
positive second connector and the source cocycle φ d₁. -/
def IsPresentationEquiv (S : Presentation A) (Q : LeftResolution R A)
    (e : PresentationCoker S B ≃ₗ[ℤ] ExtWith Q B 1) : Prop :=
  ∀ (L : LeftResolution R S.K), L.IsProjective →
    ∀ (H : ProjectiveData S.j S.ε L Q)
      (δ : ExtWith L B 0 →ₗ[ℤ] ExtWith Q B 1),
      FirstConnecting (i := ModuleCat.ofHom S.j) (p := ModuleCat.ofHom S.ε) H B 0 δ →
      ∀ φ : S.K →ₗ[R] B, e (Submodule.Quotient.mk φ) = -δ (homClass L B φ)

def maps_are_isomorphismsType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ModuleCat.{v} R) (E F : Extension A B)
    (f : E.middle →ₗ[R] F.middle),
    f.comp E.i = F.i → F.p.comp f = E.p →
      Function.Bijective f ∧ Extension.Equivalent E F

def lift_representativesType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ModuleCat.{v} R) (S : Presentation A)
    (E : Extension A B),
    (∃ (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B), IsLiftRepresentative S E l φ) ∧
    ∀ (l l' : S.P →ₗ[R] E.middle) (φ φ' : S.K →ₗ[R] B),
      IsLiftRepresentative S E l φ → IsLiftRepresentative S E l' φ' →
      ∃ ψ : S.P →ₗ[R] B, φ' - φ = ψ.comp S.j

def graph_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ModuleCat.{v} R) (S : Presentation A)
    (φ : S.K →ₗ[R] B), (graphData S φ).IsShortExact

def graph_equivalenceType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ModuleCat.{v} R) (S : Presentation A)
    (φ φ' : S.K →ₗ[R] B) (ψ : S.P →ₗ[R] B), φ' = φ + ψ.comp S.j →
    ∃ e : GraphModule S φ ≃ₗ[R] GraphModule S φ',
      (∀ b p, e (Submodule.Quotient.mk (b,p)) = Submodule.Quotient.mk (b - ψ p,p)) ∧
      e.toLinearMap.comp (graphData S φ).i = (graphData S φ').i ∧
      (graphData S φ').p.comp e.toLinearMap = (graphData S φ).p

/-- Complete bijection, its normalization, its projective-presentation
representatives, its inverse and the split criterion. The theorem asserts
existence of every required certificate; no classification is assumed. -/
def ClassificationOver (R : Type u) [Ring R] : Prop :=
  ∀ (A B : ModuleCat.{max u v} R) (Q : LeftResolution R A), Q.IsProjective →
    ∃ e : ExtensionClasses A B ≃ ExtWith Q B 1,
      RepresentsConnector Q e ∧
      (∀ E : Extension A B, e (extensionClass E) = 0 ↔ E.IsSplit) ∧
      ∀ S : Presentation A,
      ∃ c : PresentationCoker S B ≃ₗ[ℤ] ExtWith Q B 1,
        IsPresentationEquiv S Q c ∧
        (∀ (E : Extension A B) (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B),
          IsLiftRepresentative S E l φ → e (extensionClass E) = c (Submodule.Quotient.mk φ)) ∧
        ∀ φ : S.K →ₗ[R] B,
          ∃ h : (graphData S φ).IsShortExact,
            e.symm (c (Submodule.Quotient.mk φ)) = extensionClass ⟨graphData S φ, h⟩

def classificationType : Prop := ∀ (R : Type u) [Ring R], ClassificationOver.{u,v} R

/-- Pushout and pullback maps on classes, prescribed on the actual modules
above, and agreeing with the two canonical Ext actions. -/
def NaturalityOver (R : Type u) [Ring R] : Prop :=
  ∀ (A A' B B' : ModuleCat.{max u v} R)
    (Q : LeftResolution R A) (Q' : LeftResolution R A')
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (T : ExtMaps.{u,max u v,max u v} R 1)
    (e : ExtensionClasses A B ≃ ExtWith Q B 1)
    (ep : ExtensionClasses A B' ≃ ExtWith Q B' 1)
    (er : ExtensionClasses A' B ≃ ExtWith Q' B 1),
    RepresentsConnector Q e → RepresentsConnector Q ep → RepresentsConnector Q' er →
    ∀ (β : B ⟶ B') (α : A' ⟶ A),
    (∃ push : ExtensionClasses A B → ExtensionClasses A B',
      (∀ E : Extension A B, ∃ h : (pushoutData E β).IsShortExact,
        push (extensionClass E) = extensionClass ⟨pushoutData E β, h⟩) ∧
      ∀ x, ep (push x) = T.map ⟨Q,hQ⟩ ⟨Q,hQ⟩ (𝟙 A) β (e x)) ∧
    (∃ pull : ExtensionClasses A B → ExtensionClasses A' B,
      (∀ E : Extension A B, ∃ h : (pullbackData E α).IsShortExact,
        pull (extensionClass E) = extensionClass ⟨pullbackData E α, h⟩) ∧
      ∀ x, er (pull x) = T.map ⟨Q,hQ⟩ ⟨Q',hQ'⟩ α (𝟙 B) (e x))

def naturalityType : Prop := ∀ (R : Type u) [Ring R], NaturalityOver.{u,v} R

/-- Same-side right modules, with Ext computed over the opposite ring. -/
def right_classificationType : Prop :=
  ∀ (R : Type u) [Ring R], ClassificationOver.{u,v} Rᵐᵒᵖ ∧ NaturalityOver.{u,v} Rᵐᵒᵖ

end
end P103.Specs.Ch11.ExtensionClassification
