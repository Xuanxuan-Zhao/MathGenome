import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Resolution
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! Independent specifications for the exterior Koszul resolution in cochain degrees. -/

noncomputable section

namespace Specs.DerivedFormalization.KoszulCochainResolution

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ComplexShape (embeddingDownNat)
open _root_.AdvCommAlg.Koszul

universe u

variable {A : Type u} [CommRing A]

def cochainType := ∀ {A : Type u} [CommRing A], List A → Cochains.compValue.{u} A

def cochainValue (a : List A) : Cochains.compValue.{u} A :=
  (listComplex a).extend embeddingDownNat

def termIsoType := ∀ {A : Type u} [CommRing A] (a : List A) (n : ℕ),
  (cochainValue a).X (-(n : ℤ)) ≅ ModuleCat.of A (⋀[A]^n (Fin a.length → A))

def termIsoValue (a : List A) (n : ℕ) :
    (cochainValue a).X (-(n : ℤ)) ≅ ModuleCat.of A (⋀[A]^n (Fin a.length → A)) :=
  (listComplex a).extendXIso embeddingDownNat (i := n) rfl

def stalkIsoType := ∀ {A : Type u} [CommRing A] (M : ModuleCat.{u} A),
  ((ChainComplex.single₀ (ModuleCat A)).obj M).extend embeddingDownNat ≅
    (Cochains.stalkValue A).obj M

def stalkIsoValue (M : ModuleCat.{u} A) :
    ((ChainComplex.single₀ (ModuleCat A)).obj M).extend embeddingDownNat ≅
      (Cochains.stalkValue A).obj M :=
  extendSingleIso embeddingDownNat M 0 0 rfl

def augmentationType := ∀ {A : Type u} [CommRing A] (a : List A),
  cochainValue a ⟶ (Cochains.stalkValue A).obj (ModuleCat.of A (A ⧸ listIdeal a))

def augmentationValue (a : List A) :
    cochainValue a ⟶ (Cochains.stalkValue A).obj (ModuleCat.of A (A ⧸ listIdeal a)) :=
  extendMap (augmentation a) embeddingDownNat ≫ (stalkIsoValue _).hom

def homologyIsoType := ∀ {A : Type u} [CommRing A] (a : List A) (n : ℕ),
  (cochainValue a).homology (-(n : ℤ)) ≅ (listComplex a).homology n

def homologyIsoValue (a : List A) (n : ℕ) :
    (cochainValue a).homology (-(n : ℤ)) ≅ (listComplex a).homology n :=
  (listComplex a).extendHomologyIso embeddingDownNat (j := n) rfl

def differentialType : Prop := ∀ {A : Type u} [CommRing A] (a : List A) (p q : ℕ),
  (cochainValue a).d (-(p : ℤ)) (-(q : ℤ)) ≫ (termIsoValue a q).hom =
    (termIsoValue a p).hom ≫ (listComplex a).d p q

def signedWedgeType : Prop := ∀ {A : Type u} [CommRing A] (a : List A) (n : ℕ)
    (x : Fin (n + 1) → (Fin a.length → A)),
  (termIsoValue a n).hom
      ((cochainValue a).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        ((termIsoValue a (n + 1)).inv (exteriorPower.ιMulti A (n + 1) x))) =
    ∑ i : Fin (n + 1), (-1 : A)^i.val •
      (listForm a (x i) • exteriorPower.ιMulti A n (x ∘ i.succAbove))

def generatorDifferentialType : Prop := ∀ {A : Type u} [CommRing A] (a : List A)
    (i : Fin a.length),
  exteriorPower.zeroEquiv A (Fin a.length → A)
    ((termIsoValue a 0).hom
      ((cochainValue a).d (-1) 0
        ((termIsoValue a 1).inv (exteriorPower.ιMulti A 1
          (fun _ => Pi.basisFun A (Fin a.length) i))))) = a.get i

def augmentationZeroType : Prop := ∀ {A : Type u} [CommRing A] (a : List A),
  (augmentationValue a).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a))).hom =
    (termIsoValue a 0).hom ≫
      ModuleCat.ofHom ((listIdeal a).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin a.length → A)).toLinearMap)

def augmentationHomologyType : Prop := ∀ {A : Type u} [CommRing A] (a : List A) (n : ℕ),
  homologyMap (augmentationValue a) (-(n : ℤ)) =
    (homologyIsoValue a n).hom ≫ homologyMap (augmentation a) n ≫
      (extendHomologyIso
        ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A (A ⧸ listIdeal a)))
        embeddingDownNat (j := n) rfl).inv ≫
      homologyMap (stalkIsoValue (ModuleCat.of A (A ⧸ listIdeal a))).hom (-(n : ℤ))

def finiteFreeResolutionType : Prop :=
  ∀ {A : Type u} [CommRing A] (a : List A), RingTheory.Sequence.IsRegular A a →
    QuasiIso (augmentationValue a) ∧
    (∀ i : ℤ, Epi ((augmentationValue a).f i)) ∧
    (∀ i : ℤ, Module.Free A ((cochainValue a).X i) ∧ Module.Finite A ((cochainValue a).X i)) ∧
    (∀ i : ℤ, i ∉ Set.Icc (-(a.length : ℤ)) 0 → IsZero ((cochainValue a).X i))

end Specs.DerivedFormalization.KoszulCochainResolution
