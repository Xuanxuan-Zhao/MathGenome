import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MiddleExtension

noncomputable section

open CategoryTheory

universe u

namespace RepTheorySurvey.Geometric.Analytic.DerivedPullbackPasting.Expected

open IntersectionComplex (boundedBelowPullbackComposition pullbackSquare)

/-- Identity comparison for the actual derived inverse image. -/
def IdentityType :=
  ∀ X : TopCat.{u}, derivedInverseImage (𝟙 X) ≅ 𝟭 (Derived X)

/-- Localize the canonical left adjoint comparison, then identify the derived identity. -/
def identityValue : IdentityType.{u} := fun X => by
  let inverse := inverseImage (𝟙 X)
  let comparison : inverse ≅ 𝟭 (Sheaves X) :=
    (inverseDirectAdjunction (𝟙 X)).leftAdjointUniq Adjunction.id
  let localized : inverse.mapDerivedCategory ≅ (𝟭 (Sheaves X)).mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaves X) (.up ℤ)) _ _ _ _
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex comparison _) DerivedCategory.Q)
  exact localized ≪≫ Functor.mapDerivedCategoryIdIso (Sheaves X)

/-- The derived pullback square is the composition comparison across the equality of maps. -/
def SquareType :=
  ∀ {U X V Y : TopCat.{u}} {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V},
    j ≫ e = v ≫ k →
      (derivedInverseImage e ⋙ derivedInverseImage j ≅
        derivedInverseImage k ⋙ derivedInverseImage v)

def squareValue : SquareType.{u} := fun {_U _X _V _Y j k e v} h =>
  (derivedInverseImageComposition j e).symm ≪≫
    eqToIso (congrArg (fun f => derivedInverseImage f) h) ≪≫
    derivedInverseImageComposition v k

def CompositionLeftUnit : Prop :=
  ∀ {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Derived Y),
    (derivedInverseImageComposition (𝟙 X) f).hom.app F ≫
        (identityValue X).hom.app ((derivedInverseImage f).obj F) =
      eqToHom (congrArg (fun g => (derivedInverseImage g).obj F) (Category.id_comp f))

def CompositionRightUnit : Prop :=
  ∀ {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Derived Y),
    (derivedInverseImageComposition f (𝟙 Y)).hom.app F ≫
        (derivedInverseImage f).map ((identityValue Y).hom.app F) =
      eqToHom (congrArg (fun g => (derivedInverseImage g).obj F) (Category.comp_id f))

def CompositionAssociativity : Prop :=
  ∀ {W X Y Z : TopCat.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (F : Derived Z),
    (derivedInverseImageComposition (f ≫ g) h).hom.app F ≫
        (derivedInverseImageComposition f g).hom.app ((derivedInverseImage h).obj F) =
      eqToHom (congrArg (fun t => (derivedInverseImage t).obj F) (Category.assoc f g h)) ≫
        (derivedInverseImageComposition f (g ≫ h)).hom.app F ≫
        (derivedInverseImage f).map ((derivedInverseImageComposition g h).hom.app F)

-- Use the shift comparison of the induced exact functor on the derived category.
local instance {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (derivedInverseImage f).CommShift ℤ :=
  inferInstanceAs ((inverseImage f).mapDerivedCategory.CommShift ℤ)

def IdentityCommShift : Prop :=
  ∀ X : TopCat.{u}, NatTrans.CommShift (identityValue X).hom ℤ

def CompositionCommShift : Prop :=
  ∀ {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    NatTrans.CommShift (derivedInverseImageComposition f g).hom ℤ

def PullbackIdentityMap : Prop :=
  ∀ {Y X : TopCat.{u}} {f g : Y ⟶ X} {F : Derived X}
    (α : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F),
    pullbackMorphism (𝟙 Y) (Category.id_comp f) (Category.id_comp g) α = α

def PullbackIdentityMorphism : Prop :=
  ∀ {W Y X : TopCat.{u}} (k : W ⟶ Y) {f : Y ⟶ X} {f' : W ⟶ X}
    (hf : k ≫ f = f') (F : Derived X),
    pullbackMorphism k hf hf (𝟙 ((derivedInverseImage f).obj F)) =
      𝟙 ((derivedInverseImage f').obj F)

def PullbackComposition : Prop :=
  ∀ {W Y X : TopCat.{u}} (k : W ⟶ Y) {f g h : Y ⟶ X} {f' g' h' : W ⟶ X}
    (hf : k ≫ f = f') (hg : k ≫ g = g') (hh : k ≫ h = h') {F : Derived X}
    (α : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F)
    (β : (derivedInverseImage g).obj F ⟶ (derivedInverseImage h).obj F),
    pullbackMorphism k hf hh (α ≫ β) =
      pullbackMorphism k hf hg α ≫ pullbackMorphism k hg hh β

/-- A commuting square over a map of coefficient complexes remains commuting after pullback. -/
def PullbackNaturality : Prop :=
  ∀ {W Y X : TopCat.{u}} (k : W ⟶ Y) {f g : Y ⟶ X} {f' g' : W ⟶ X}
    (hf : k ≫ f = f') (hg : k ≫ g = g') {F G : Derived X} (a : F ⟶ G)
    (α : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F)
    (β : (derivedInverseImage f).obj G ⟶ (derivedInverseImage g).obj G),
    (derivedInverseImage f).map a ≫ β = α ≫ (derivedInverseImage g).map a →
      (derivedInverseImage f').map a ≫ pullbackMorphism k hf hg β =
        pullbackMorphism k hf hg α ≫ (derivedInverseImage g').map a

def PullbackSuccessive : Prop :=
  ∀ {V W Y X : TopCat.{u}} (l : V ⟶ W) (k : W ⟶ Y)
    {f g : Y ⟶ X} {f' g' : W ⟶ X} {f'' g'' : V ⟶ X}
    (hf : k ≫ f = f') (hg : k ≫ g = g') (hf' : l ≫ f' = f'') (hg' : l ≫ g' = g'')
    {F : Derived X} (α : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F),
    pullbackMorphism l hf' hg' (pullbackMorphism k hf hg α) =
      pullbackMorphism (l ≫ k)
        ((Category.assoc l k f).trans ((congrArg (l ≫ ·) hf).trans hf'))
        ((Category.assoc l k g).trans ((congrArg (l ≫ ·) hg).trans hg')) α

def PullbackShift : Prop :=
  ∀ {W Y X : TopCat.{u}} (k : W ⟶ Y) {f g : Y ⟶ X} {f' g' : W ⟶ X}
    (hf : k ≫ f = f') (hg : k ≫ g = g') {F : Derived X} (n : ℤ)
    (α : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F),
    pullbackMorphism (F := (shiftFunctor (Derived X) n).obj F) k hf hg
        (((derivedInverseImage f).commShiftIso n).hom.app F ≫
          (shiftFunctor (Derived Y) n).map α ≫
          ((derivedInverseImage g).commShiftIso n).inv.app F) =
      ((derivedInverseImage f').commShiftIso n).hom.app F ≫
        (shiftFunctor (Derived W) n).map (pullbackMorphism k hf hg α) ≫
        ((derivedInverseImage g').commShiftIso n).inv.app F

private theorem horizontalCommutes {U X A V Y B : TopCat.{u}}
    {j : U ⟶ X} {j' : X ⟶ A} {k : V ⟶ Y} {k' : Y ⟶ B}
    {v : U ⟶ V} {e : X ⟶ Y} {e' : A ⟶ B}
    (h : j ≫ e = v ≫ k) (h' : j' ≫ e' = e ≫ k') :
    (j ≫ j') ≫ e' = v ≫ (k ≫ k') := by
  rw [Category.assoc, h', ← Category.assoc, h, Category.assoc]

private theorem verticalCommutes {U X V Y A B : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {m : A ⟶ B}
    {v : U ⟶ V} {e : X ⟶ Y} {v' : V ⟶ A} {e' : Y ⟶ B}
    (h : j ≫ e = v ≫ k) (h' : k ≫ e' = v' ≫ m) :
    j ≫ (e ≫ e') = (v ≫ v') ≫ m := by
  rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]

def SquareHorizontalPasting : Prop :=
  ∀ {U X A V Y B : TopCat.{u}}
    {j : U ⟶ X} {j' : X ⟶ A} {k : V ⟶ Y} {k' : Y ⟶ B}
    {v : U ⟶ V} {e : X ⟶ Y} {e' : A ⟶ B}
    (h : j ≫ e = v ≫ k) (h' : j' ≫ e' = e ≫ k') (F : Derived B),
    (squareValue (horizontalCommutes h h')).hom.app F =
      (derivedInverseImageComposition j j').hom.app ((derivedInverseImage e').obj F) ≫
        (derivedInverseImage j).map ((squareValue h').hom.app F) ≫
        (squareValue h).hom.app ((derivedInverseImage k').obj F) ≫
        (derivedInverseImage v).map ((derivedInverseImageComposition k k').inv.app F)

def SquareVerticalPasting : Prop :=
  ∀ {U X V Y A B : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {m : A ⟶ B}
    {v : U ⟶ V} {e : X ⟶ Y} {v' : V ⟶ A} {e' : Y ⟶ B}
    (h : j ≫ e = v ≫ k) (h' : k ≫ e' = v' ≫ m) (F : Derived B),
    (squareValue (verticalCommutes h h')).hom.app F =
      (derivedInverseImage j).map ((derivedInverseImageComposition e e').hom.app F) ≫
        (squareValue h).hom.app ((derivedInverseImage e').obj F) ≫
        (derivedInverseImage v).map ((squareValue h').hom.app F) ≫
        (derivedInverseImageComposition v v').inv.app ((derivedInverseImage m).obj F)

/-- The accepted bounded-below square has the same components under the full inclusion. -/
def SquareBoundedBelowCompatibility : Prop :=
  ∀ {U X V Y : TopCat.{u}} {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (h : j ≫ e = v ≫ k) (F : BoundedBelow Y),
    ((pullbackSquare h).hom.app F).hom = (squareValue h).hom.app F.obj

def BoundedBelowSquareHorizontalPasting : Prop :=
  ∀ {U X A V Y B : TopCat.{u}}
    {j : U ⟶ X} {j' : X ⟶ A} {k : V ⟶ Y} {k' : Y ⟶ B}
    {v : U ⟶ V} {e : X ⟶ Y} {e' : A ⟶ B}
    (h : j ≫ e = v ≫ k) (h' : j' ≫ e' = e ≫ k') (F : BoundedBelow B),
    (pullbackSquare (horizontalCommutes h h')).hom.app F =
      (boundedBelowPullbackComposition j j').hom.app ((boundedBelowInverseImage e').obj F) ≫
        (boundedBelowInverseImage j).map ((pullbackSquare h').hom.app F) ≫
        (pullbackSquare h).hom.app ((boundedBelowInverseImage k').obj F) ≫
        (boundedBelowInverseImage v).map ((boundedBelowPullbackComposition k k').inv.app F)

def BoundedBelowSquareVerticalPasting : Prop :=
  ∀ {U X V Y A B : TopCat.{u}}
    {j : U ⟶ X} {k : V ⟶ Y} {m : A ⟶ B}
    {v : U ⟶ V} {e : X ⟶ Y} {v' : V ⟶ A} {e' : Y ⟶ B}
    (h : j ≫ e = v ≫ k) (h' : k ≫ e' = v' ≫ m) (F : BoundedBelow B),
    (pullbackSquare (verticalCommutes h h')).hom.app F =
      (boundedBelowInverseImage j).map ((boundedBelowPullbackComposition e e').hom.app F) ≫
        (pullbackSquare h).hom.app ((boundedBelowInverseImage e').obj F) ≫
        (boundedBelowInverseImage v).map ((pullbackSquare h').hom.app F) ≫
        (boundedBelowPullbackComposition v v').inv.app ((boundedBelowInverseImage m).obj F)

end RepTheorySurvey.Geometric.Analytic.DerivedPullbackPasting.Expected
