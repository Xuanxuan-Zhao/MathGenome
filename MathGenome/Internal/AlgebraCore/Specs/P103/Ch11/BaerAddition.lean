import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtensionClassification

/-! Baer addition from paper.tex 2837–2845 and 2887–2893.
Products below are the finite direct sums. All rings are arbitrary unital rings;
right modules are included by replacing R with its opposite. -/
namespace P103.Specs.Ch11.BaerAddition
open CategoryTheory
open P103.Specs.Ch11.ExtensionClassification
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
universe u v
variable {R : Type u} [Ring R]
variable {A B : ModuleCat.{v} R}

def directSumData (E F : Extension A B) :
    ExtensionData (ModuleCat.of R (A × A)) (ModuleCat.of R (B × B)) where
  middle := ModuleCat.of R (E.middle × F.middle)
  i := (E.i.comp (LinearMap.fst R B B)).prod (F.i.comp (LinearMap.snd R B B))
  p := (E.p.comp (LinearMap.fst R E.middle F.middle)).prod
    (F.p.comp (LinearMap.snd R E.middle F.middle))

def diagonal (A : ModuleCat.{v} R) : A ⟶ ModuleCat.of R (A × A) :=
  ModuleCat.ofHom (LinearMap.id.prod LinearMap.id)

def addition (B : ModuleCat.{v} R) : ModuleCat.of R (B × B) ⟶ B :=
  ModuleCat.ofHom ((LinearMap.fst R B B) + (LinearMap.snd R B B))

/-- The actual direct sum, diagonal pullback, and addition pushout, rather
than an operation specified only by its image in Ext. -/
def IsBaerSum (E F G : Extension A B) : Prop :=
  ∃ h : (directSumData E F).IsShortExact,
  ∃ k : (pullbackData ⟨directSumData E F, h⟩ (diagonal A)).IsShortExact,
    G.val = pushoutData ⟨pullbackData ⟨directSumData E F, h⟩ (diagonal A), k⟩ (addition B)

def baer_exactType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ModuleCat.{v} R) (E F : Extension A B),
    ∃ G : Extension A B, IsBaerSum E F G

def representativesType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ModuleCat.{v} R) (S : Presentation A)
    (E F G : Extension A B) (l : S.P →ₗ[R] E.middle) (l' : S.P →ₗ[R] F.middle)
    (φ φ' : S.K →ₗ[R] B),
    IsLiftRepresentative S E l φ → IsLiftRepresentative S F l' φ' →
    IsBaerSum E F G → ∃ L : S.P →ₗ[R] G.middle,
      IsLiftRepresentative S G L (φ + φ')

/-- The group law is required to equal every actual Baer construction.
Consequently it descends from representatives and is independent of choices. -/
def GroupOver (R : Type u) [Ring R] : Prop :=
  ∀ (A B : ModuleCat.{max u v} R) (Q : LeftResolution R A), Q.IsProjective →
  ∃ g : AddCommGroup (ExtensionClasses A B),
  letI := g
  ∃ e : ExtensionClasses A B ≃+ ExtWith Q B 1,
    RepresentsConnector Q e.toEquiv ∧
    (∀ E F G : Extension A B, IsBaerSum E F G →
      extensionClass G = extensionClass E + extensionClass F) ∧
    (∀ E : Extension A B, extensionClass E = 0 ↔ E.IsSplit) ∧
    ∀ S : Presentation A,
    ∃ c : PresentationCoker S B ≃ₗ[ℤ] ExtWith Q B 1,
      IsPresentationEquiv S Q c ∧
      ∀ (E : Extension A B) (l : S.P →ₗ[R] E.middle) (φ : S.K →ₗ[R] B),
        IsLiftRepresentative S E l φ →
        e (extensionClass E) = c (Submodule.Quotient.mk φ)

def group_classificationType : Prop := ∀ (R : Type u) [Ring R], GroupOver.{u,v} R

/-- Replacing either extension by an equivalent one does not change the sum class. -/
def well_definedType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ModuleCat.{max u v} R)
    (E E' F F' G G' : Extension A B),
    Extension.Equivalent E E' → Extension.Equivalent F F' →
    IsBaerSum E F G → IsBaerSum E' F' G' → Extension.Equivalent G G'

/-- Pushout and pullback on classes are additive and agree with the two Ext
actions, for every normalized classification. -/
def additive_naturalityType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' B B' : ModuleCat.{max u v} R)
    (Q : LeftResolution R A) (Q' : LeftResolution R A')
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (T : ExtMaps.{u,max u v,max u v} R 1)
    (g : AddCommGroup (ExtensionClasses A B))
    (gp : AddCommGroup (ExtensionClasses A B'))
    (gr : AddCommGroup (ExtensionClasses A' B)),
    letI := g; letI := gp; letI := gr
    ∀ (e : ExtensionClasses A B ≃+ ExtWith Q B 1)
      (ep : ExtensionClasses A B' ≃+ ExtWith Q B' 1)
      (er : ExtensionClasses A' B ≃+ ExtWith Q' B 1),
    RepresentsConnector Q e.toEquiv → RepresentsConnector Q ep.toEquiv →
    RepresentsConnector Q' er.toEquiv → ∀ (β : B ⟶ B') (α : A' ⟶ A),
    (∃ push : ExtensionClasses A B →+ ExtensionClasses A B',
      (∀ E : Extension A B, ∃ h : (pushoutData E β).IsShortExact,
        push (extensionClass E) = extensionClass ⟨pushoutData E β, h⟩) ∧
      ∀ x, ep (push x) = T.map ⟨Q,hQ⟩ ⟨Q,hQ⟩ (𝟙 A) β (e x)) ∧
    (∃ pull : ExtensionClasses A B →+ ExtensionClasses A' B,
      (∀ E : Extension A B, ∃ h : (pullbackData E α).IsShortExact,
        pull (extensionClass E) = extensionClass ⟨pullbackData E α, h⟩) ∧
      ∀ x, er (pull x) = T.map ⟨Q,hQ⟩ ⟨Q',hQ'⟩ α (𝟙 B) (e x))

def right_group_classificationType : Prop :=
  ∀ (R : Type u) [Ring R], GroupOver.{u,v} Rᵐᵒᵖ
end
end P103.Specs.Ch11.BaerAddition
