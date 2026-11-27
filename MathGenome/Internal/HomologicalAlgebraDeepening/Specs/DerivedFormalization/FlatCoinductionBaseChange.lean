import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedCoinduction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedScalarExtension
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.TensorProduct.Maps

/-!
Flat base change for finite affine coinduction (U16).
The three original rings have independent universes. The four module categories
have a common universe containing the tensor-product algebra.
-/

namespace Specs.DerivedFormalization.FlatCoinductionBaseChange

open CategoryTheory CategoryTheory.Limits
open Cochains (compValue derivedValue qValue)
open DerivedRestriction (derivedRestrictScalarsValue)
open DerivedCoinduction (Coinduction)
open DerivedScalarExtension (Extension)
open TensorProduct

universe u w z v

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (A : Type u) (B : Type w) (S : Type z) [CommRing A] [CommRing B] [CommRing S]
  [Algebra A B] [Algebra A S]

abbrev changedRing := S ⊗[A] B

abbrev bottomMap : S →+* changedRing A B S := Algebra.TensorProduct.includeLeftRingHom

abbrev rightMap : B →+* changedRing A B S :=
  Algebra.TensorProduct.includeRight.toRingHom

abbrev extend {R : Type u} {T : Type w} [CommRing R] [CommRing T] (g : R →+* T) :=
  ModuleCat.extendScalars.{u,w,max w v} g

abbrev restrict {R : Type u} {T : Type w} [CommRing R] [CommRing T] (g : R →+* T) :=
  ModuleCat.restrictScalars.{v} g

instance extendAdditive {R : Type u} {T : Type w} [CommRing R] [CommRing T] (g : R →+* T) :
    (extend.{u,w,v} g).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{v,u,w} g).left_adjoint_additive

abbrev extendC {R : Type u} {T : Type w} [CommRing R] [CommRing T] (g : R →+* T) :
    compValue.{max w v} R ⥤ compValue.{max w v} T :=
  (extend.{u,w,v} g).mapHomologicalComplex (.up ℤ)

abbrev extendD {R : Type u} {T : Type w} [CommRing R] [CommRing T] (g : R →+* T)
    [PreservesFiniteLimits (extend.{u,w,v} g)] :
    derivedValue.{max w v} R ⥤ derivedValue.{max w v} T :=
  (extend.{u,w,v} g).mapDerivedCategory

abbrev extendFactors {R : Type u} {T : Type w} [CommRing R] [CommRing T] (g : R →+* T)
    [PreservesFiniteLimits (extend.{u,w,v} g)] :
    qValue.{max w v} R ⋙ extendD.{u,w,v} g ≅ extendC.{u,w,v} g ⋙ qValue T :=
  (extend.{u,w,v} g).mapDerivedCategoryFactors

/-- Localize the ordinary extension--restriction adjunction when extension is exact. -/
def flatExtensionAdjunction {R : Type u} {T : Type w} [CommRing R] [CommRing T]
    (g : R →+* T) [PreservesFiniteLimits (extend.{u,w,v} g)] :
    extendD.{u,w,v} g ⊣ derivedRestrictScalarsValue.{max w v} g := by
  let L := extendC.{u,w,v} g
  let U := DerivedRestriction.restrictScalarsComplexValue.{max w v} g
  let L' := extendD.{u,w,v} g
  let U' := derivedRestrictScalarsValue.{max w v} g
  letI : CatCommSq L (qValue R) (qValue T) L' := ⟨(extendFactors.{u,w,v} g).symm⟩
  letI : CatCommSq U (qValue T) (qValue R) U' :=
    ⟨(DerivedRestriction.derivedRestrictScalarsFactorsValue g).symm⟩
  exact (ScalarExtensionTransport.cochainAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{v,u,w} g)).localization
    (qValue R) (HomologicalComplex.quasiIso (ModuleCat.{max w v} R) (.up ℤ))
    (qValue T) (HomologicalComplex.quasiIso (ModuleCat.{max w v} T) (.up ℤ)) L' U'

/-- The restriction square before localization. -/
abbrev RestrictionSquare :=
  extend.{_,_,max u w z v} (rightMap A B S) ⋙ restrict (bottomMap A B S) ≅
    restrict (algebraMap A B) ⋙ extend.{_,_,max u w z v} (algebraMap A S)

/-- The pure tensor in extension of scalars along a specified ring map. -/
abbrev pure {R : Type u} {T : Type w} [CommRing R] [CommRing T] (g : R →+* T)
    {M : ModuleCat.{v} R} (t : T) (m : M) : (ModuleCat.extendScalars.{u,w,v} g).obj M :=
  @TensorProduct.tmul R _ _ _ _ _ (Module.compHom _ g) _ t m

/-- The inverse of the restriction comparison sends a pure tensor to the
same pure tensor with the scalar included in the tensor-product algebra. -/
def TensorFormula (e : RestrictionSquare.{u,w,z,v} A B S) : Prop :=
  ∀ (M : ModuleCat.{max u w z v} B) (s : S) (m : M),
    e.inv.app M (pure (algebraMap A S) s (m :
      (restrict.{_,_,max u w z v} (algebraMap A B)).obj M)) =
      (pure (rightMap A B S) (bottomMap A B S s) m :
        (restrict.{_,_,max u w z v} (bottomMap A B S)).obj
          ((extend.{_,_,max u w z v} (rightMap A B S)).obj M))

variable [PreservesFiniteLimits (extend.{_,_,max u w z v} (algebraMap A S))]
  [PreservesFiniteLimits (extend.{_,_,max u w z v} (rightMap A B S))]

/-- The model computation for the composite through the changed algebra. -/
def factorsRight :
    qValue.{max u w z v} B ⋙
        (extendD.{_,_,max u w z v} (rightMap A B S) ⋙ derivedRestrictScalarsValue (bottomMap A B S)) ≅
      (extendC.{_,_,max u w z v} (rightMap A B S) ⋙
        (restrict.{_,_,max u w z v} (bottomMap A B S)).mapHomologicalComplex (.up ℤ)) ⋙ qValue S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extendFactors.{w,max w z,max u w z v} (rightMap A B S)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((restrict.{_,_,max u w z v} (bottomMap A B S)).mapDerivedCategoryFactors) ≪≫
    (Functor.associator _ _ _).symm

/-- The model computation for the composite through restriction over the original ring. -/
def factorsLeft :
    qValue.{max u w z v} B ⋙
        (derivedRestrictScalarsValue (algebraMap A B) ⋙ extendD.{_,_,max u w z v} (algebraMap A S)) ≅
      ((restrict.{_,_,max u w z v} (algebraMap A B)).mapHomologicalComplex (.up ℤ) ⋙
        extendC.{_,_,max u w z v} (algebraMap A S)) ⋙ qValue S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((restrict.{_,_,max u w z v} (algebraMap A B)).mapDerivedCategoryFactors) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (extendFactors.{u,z,max u w z v} (algebraMap A S)) ≪≫
    (Functor.associator _ _ _).symm

/-- Localization of the very same restriction comparison. -/
def derivedSquare (e : RestrictionSquare.{u,w,z,v} A B S) :
    extendD.{_,_,max u w z v} (rightMap A B S) ⋙ derivedRestrictScalarsValue (bottomMap A B S) ≅
      derivedRestrictScalarsValue (algebraMap A B) ⋙ extendD.{_,_,max u w z v} (algebraMap A S) := by
  let W := HomologicalComplex.quasiIso (ModuleCat.{max u w z v} B) (.up ℤ)
  exact @Localization.liftNatIso _ _ _ _ (qValue B) W _ _ _ _ _ _ _
    ⟨factorsRight.{u,w,z,v} A B S⟩ ⟨factorsLeft.{u,w,z,v} A B S⟩
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) _)

variable (e : RestrictionSquare.{u,w,z,v} A B S)
  (G : Coinduction.{max u w z v} (algebraMap A B))
  (G' : Coinduction.{max u w z v} (bottomMap A B S))

/-- The right mate of a derived restriction square, using the original coinduction counit. -/
def squareMate
    {L : derivedValue.{max u w z v} A ⥤ derivedValue.{max u w z v} S}
    {L' : derivedValue.{max u w z v} B ⥤ derivedValue.{max u w z v} (changedRing A B S)}
    (σ : L' ⋙ derivedRestrictScalarsValue (bottomMap A B S) ≅
      derivedRestrictScalarsValue (algebraMap A B) ⋙ L) :
    G.functor ⋙ L' ⟶ L ⋙ G'.functor where
  app Y :=
    G'.adjunction.homEquiv _ _
      (σ.hom.app (G.functor.obj Y) ≫ L.map (G.adjunction.counit.app Y))
  naturality Y Z k := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← G'.adjunction.homEquiv_naturality_left, ← G'.adjunction.homEquiv_naturality_right]
    congr 1
    have h := σ.hom.naturality (G.functor.map k)
    dsimp only [Functor.comp_map] at h
    rw [← Category.assoc, h]
    have hc := G.adjunction.counit.naturality k
    dsimp only [Functor.comp_map] at hc
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hc]
    rfl

/-- The canonical comparison for the two degreewise flat extensions. -/
def comparison :
    G.functor ⋙ extendD.{_,_,max u w z v} (rightMap A B S) ⟶
      extendD.{_,_,max u w z v} (algebraMap A S) ⋙ G'.functor :=
  squareMate.{u,w,z,v} A B S G G' (derivedSquare.{u,w,z,v} A B S e)

/-- The mate intertwines the coinduction counits via the given square. -/
def SquareTrace
    {L : derivedValue.{max u w z v} A ⥤ derivedValue.{max u w z v} S}
    {L' : derivedValue.{max u w z v} B ⥤ derivedValue.{max u w z v} (changedRing A B S)}
    (σ : L' ⋙ derivedRestrictScalarsValue (bottomMap A B S) ≅
      derivedRestrictScalarsValue (algebraMap A B) ⋙ L) : Prop :=
  ∀ Y : derivedValue.{max u w z v} A,
    (derivedRestrictScalarsValue (bottomMap A B S)).map
        ((squareMate.{u,w,z,v} A B S G G' σ).app Y) ≫
      G'.adjunction.counit.app (L.obj Y) =
    σ.hom.app (G.functor.obj Y) ≫ L.map (G.adjunction.counit.app Y)

/-- The trace identity for the mate of the localized ordinary square. -/
def TraceCompatibility : Prop :=
  SquareTrace.{u,w,z,v} A B S G G' (derivedSquare.{u,w,z,v} A B S e)

/-- Flat scalar extension on both vertical sides, the ordinary restriction
identification on pure tensors, and invertibility of the canonical mate on D⁺. -/
def BaseChange : Prop :=
  ∀ (A : Type u) (B : Type w) (S : Type z) [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [IsNoetherianRing A]
    [Module.Finite A B] [Module.Flat A S]
    (G : Coinduction.{max u w z v} (algebraMap A B))
    (G' : Coinduction.{max u w z v} (bottomMap A B S)),
    ∃ (_h : PreservesFiniteLimits (extend.{_,_,max u w z v} (algebraMap A S)))
      (_h' : PreservesFiniteLimits (extend.{_,_,max u w z v} (rightMap A B S)))
      (e : RestrictionSquare.{u,w,z,v} A B S),
      TensorFormula.{u,w,z,v} A B S e ∧ TraceCompatibility.{u,w,z,v} A B S e G G' ∧
        let incl : DerivedCategory.Plus (ModuleCat.{max u w z v} A) ⥤ derivedValue.{max u w z v} A :=
          DerivedCategory.Plus.ι
        ∃ iso : incl ⋙ (G.functor ⋙ extendD.{_,_,max u w z v} (rightMap A B S)) ≅
            incl ⋙ (extendD.{_,_,max u w z v} (algebraMap A S) ⋙ G'.functor),
          iso.hom = Functor.whiskerLeft incl (comparison.{u,w,z,v} A B S e G G')

/-- Carry the localized restriction square along two comparisons of left extensions. -/
def replaceExtensions
    {L : derivedValue.{max u w z v} A ⥤ derivedValue.{max u w z v} S}
    {L' : derivedValue.{max u w z v} B ⥤ derivedValue.{max u w z v} (changedRing A B S)}
    (α : extendD.{_,_,max u w z v} (algebraMap A S) ≅ L)
    (β : extendD.{_,_,max u w z v} (rightMap A B S) ≅ L') :
    L' ⋙ derivedRestrictScalarsValue (bottomMap A B S) ≅
      derivedRestrictScalarsValue (algebraMap A B) ⋙ L :=
  Functor.isoWhiskerRight β.symm _ ≪≫ derivedSquare.{u,w,z,v} A B S e ≪≫
    Functor.isoWhiskerLeft _ α

/-- The same square, canonical mate, and trace for the U09 extensions on the original rings. -/
def BaseChangeOnExtensions : Prop :=
  ∀ (A : Type u) (B : Type w) (S : Type z) [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [IsNoetherianRing A]
    [Module.Finite A B] [Module.Flat A S]
    (G : Coinduction.{max u w z v} (algebraMap A B))
    (G' : Coinduction.{max u w z v} (bottomMap A B S))
    {S₀ D₀ : Type (max u w z v)} [CommRing S₀] [CommRing D₀]
    (dS : S ≃+* S₀) (dD : changedRing A B S ≃+* D₀)
    (L : Extension dS (algebraMap A S)) (L' : Extension dD (rightMap A B S)),
    ∃ (_h : PreservesFiniteLimits (extend.{_,_,max u w z v} (algebraMap A S)))
      (_h' : PreservesFiniteLimits (extend.{_,_,max u w z v} (rightMap A B S)))
      (e : RestrictionSquare.{u,w,z,v} A B S),
      TensorFormula.{u,w,z,v} A B S e ∧
        let α := (flatExtensionAdjunction.{u,z,max u w z v} (algebraMap A S)).leftAdjointUniq L.adj
        let β := (flatExtensionAdjunction.{w,max w z,max u w z v} (rightMap A B S)).leftAdjointUniq L'.adj
        let σ := replaceExtensions.{u,w,z,v} A B S e α β
        SquareTrace.{u,w,z,v} A B S G G' σ ∧
          let incl : DerivedCategory.Plus (ModuleCat.{max u w z v} A) ⥤ derivedValue.{max u w z v} A :=
            DerivedCategory.Plus.ι
          ∃ iso : incl ⋙ (G.functor ⋙ L'.derived) ≅ incl ⋙ (L.derived ⋙ G'.functor),
            iso.hom = Functor.whiskerLeft incl (squareMate.{u,w,z,v} A B S G G' σ)

end

end Specs.DerivedFormalization.FlatCoinductionBaseChange
