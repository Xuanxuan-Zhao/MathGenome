import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u

namespace RepTheorySurvey.Geometric.ClosedSupportPullbackPastingSpecs

open Analytic Analytic.IntersectionComplex
open Analytic.DerivedPullbackPasting.Expected (squareValue)

set_option allowUnsafeReducibility true in
attribute [local reducible] Analytic.DerivedPullbackPasting.Expected.SquareType

/-- Compare the inverse image along a specified composite with the two successive inverse images. -/
def pullbackComparisonAt {W X Y : TopCat.{u}} (s : W ⟶ X) (t : X ⟶ Y)
    {u : W ⟶ Y} (h : s ≫ t = u) (F : BoundedBelow Y) :
    (boundedBelowInverseImage u).obj F ≅
      (boundedBelowInverseImage s).obj ((boundedBelowInverseImage t).obj F) :=
  eqToIso (congrArg (fun f => (boundedBelowInverseImage f).obj F) h.symm) ≪≫
    (boundedBelowPullbackComposition s t).app F

/-- Express an arrow on a restricted complex as an arrow between pullbacks along composites. -/
def flatten {W X Y : TopCat.{u}} (t : X ⟶ Y) {e p : W ⟶ X} {G : Derived Y}
    (r : (derivedInverseImage e).obj ((derivedInverseImage t).obj G) ⟶
      (derivedInverseImage p).obj ((derivedInverseImage t).obj G)) :
    (derivedInverseImage (e ≫ t)).obj G ⟶ (derivedInverseImage (p ≫ t)).obj G :=
  (derivedInverseImageComposition e t).hom.app G ≫ r ≫
    (derivedInverseImageComposition p t).inv.app G

/-- The transposed comparison of two arrows over a pair of commuting inverse-image squares. -/
def SquareRestriction {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F)
    (α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F) : Prop :=
  (derivedInverseImage j).map α ≫ (squareValue hp).hom.app G ≫
    (derivedInverseImage q).map ε =
      (squareValue he).hom.app G ≫ (derivedInverseImage v).map ε ≫ β

/-- Paste two squares along their common parameter-to-coefficient map. -/
theorem horizontalSquare {U X Z V Y W : TopCat.{u}}
    {j : U ⟶ X} {j' : X ⟶ Z} {i : V ⟶ Y} {i' : Y ⟶ W}
    {v : U ⟶ V} {e : X ⟶ Y} {e' : Z ⟶ W}
    (h : j ≫ e = v ≫ i) (h' : j' ≫ e' = e ≫ i') :
    (j ≫ j') ≫ e' = v ≫ (i ≫ i') := by
  rw [Category.assoc, h', ← Category.assoc, h, Category.assoc]

namespace Expected

def PullbackComparisonAtType :=
  ∀ {W X Y : TopCat.{u}} (s : W ⟶ X) (t : X ⟶ Y)
    {f : W ⟶ Y}, s ≫ t = f → ∀ F : BoundedBelow Y,
    (boundedBelowInverseImage f).obj F ≅
      (boundedBelowInverseImage s).obj ((boundedBelowInverseImage t).obj F)

def FlattenType :=
  ∀ {W X Y : TopCat.{u}} (t : X ⟶ Y) {e p : W ⟶ X} {G : Derived Y},
    ((derivedInverseImage e).obj ((derivedInverseImage t).obj G) ⟶
      (derivedInverseImage p).obj ((derivedInverseImage t).obj G)) →
    ((derivedInverseImage (e ≫ t)).obj G ⟶ (derivedInverseImage (p ≫ t)).obj G)

def SquareRestrictionType :=
  ∀ {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U}, j ≫ e = v ≫ i → j ≫ p = q ≫ i →
    ∀ {G : Derived X} {F : Derived U}, ((derivedInverseImage i).obj G ⟶ F) →
    ((derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G) →
    ((derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F) → Prop

/-- The comparison with a specified composite is the same after forgetting the bound. -/
def PullbackComparisonAtUnderlying : Prop :=
  ∀ {W X Y : TopCat.{u}} (s : W ⟶ X) (t : X ⟶ Y)
    {f : W ⟶ Y} (h : s ≫ t = f) (F : BoundedBelow Y),
    (DerivedCategory.Plus.ι (C := Sheaves W)).mapIso (pullbackComparisonAt s t h F) =
      eqToIso (congrArg (fun g => (derivedInverseImage g).obj F.obj) h.symm) ≪≫
        (derivedInverseImageComposition s t).app F.obj

/-- Vertical pasting for the canonical direct-image mates, with specified identifications of both composites. -/
def MateVerticalPasting : Prop :=
  ∀ {U₀ X₀ U₁ X₁ U₂ X₂ : TopCat.{u}}
    {j₀ : U₀ ⟶ X₀} {j₁ : U₁ ⟶ X₁} {j₂ : U₂ ⟶ X₂}
    {e₁ : X₁ ⟶ X₀} {e₂ : X₂ ⟶ X₁} {v₁ : U₁ ⟶ U₀} {v₂ : U₂ ⟶ U₁}
    (h₁ : j₁ ≫ e₁ = v₁ ≫ j₀) (h₂ : j₂ ≫ e₂ = v₂ ≫ j₁)
    {e : X₂ ⟶ X₀} {v : U₂ ⟶ U₀}
    (he : e₂ ≫ e₁ = e) (hv : v₂ ≫ v₁ = v) (h : j₂ ≫ e = v ≫ j₀)
    (a₀ : boundedBelowInverseImage j₀ ⊣ derivedDirectImage j₀)
    (a₁ : boundedBelowInverseImage j₁ ⊣ derivedDirectImage j₁)
    (a₂ : boundedBelowInverseImage j₂ ⊣ derivedDirectImage j₂) (F : BoundedBelow U₀),
    directImageComparison h a₂ a₀ F =
      (pullbackComparisonAt e₂ e₁ he ((derivedDirectImage j₀).obj F)).hom ≫
        (boundedBelowInverseImage e₂).map (directImageComparison h₁ a₁ a₀ F) ≫
        directImageComparison h₂ a₂ a₁ ((boundedBelowInverseImage v₁).obj F) ≫
        (derivedDirectImage j₂).map (pullbackComparisonAt v₂ v₁ hv F).inv

/-- Pasting the naturality square of the direct-image mate with a compatible map into its source. -/
def MateNaturality : Prop :=
  ∀ {U X V Y : TopCat.{u}}
    {j : U ⟶ X} {i : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ i)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage i ⊣ derivedDirectImage i) {F G : BoundedBelow V} (q : F ⟶ G)
    {P Q : BoundedBelow Y} (f : P ⟶ Q)
    (cF : P ⟶ (derivedDirectImage i).obj F) (cG : Q ⟶ (derivedDirectImage i).obj G)
    (_hc : f ≫ cG = cF ≫ (derivedDirectImage i).map q),
    (boundedBelowInverseImage e).map f ≫
      ((boundedBelowInverseImage e).map cG ≫ directImageComparison h a b G) =
    ((boundedBelowInverseImage e).map cF ≫ directImageComparison h a b F) ≫
      (derivedDirectImage j).map ((boundedBelowInverseImage v).map q)

/-- Conjugating by the inverse-image composition comparisons is injective on arrows. -/
def FlattenInjective : Prop :=
  ∀ {W X Y : TopCat.{u}} (t : X ⟶ Y) (e p : W ⟶ X)
    (G : Derived Y), Function.Injective
      (flatten t : ((derivedInverseImage e).obj ((derivedInverseImage t).obj G) ⟶
        (derivedInverseImage p).obj ((derivedInverseImage t).obj G)) → _)

/-- Transposing a restricted arrow along a pair of squares commutes with conjugation by composition. -/
def SquareRestrictionFlatten : Prop :=
  ∀ {U X V Y U' X' : TopCat.{u}}
    {j : U ⟶ X} {j' : U' ⟶ X'} {i : V ⟶ Y} {t : X ⟶ Y} {v : U ⟶ V}
    {e p : X' ⟶ X} {s q : U' ⟶ U}
    (h : j ≫ t = v ≫ i) (he : j' ≫ e = s ≫ j) (hp : j' ≫ p = q ≫ j)
    (he' : j' ≫ (e ≫ t) = (s ≫ v) ≫ i) (hp' : j' ≫ (p ≫ t) = (q ≫ v) ≫ i)
    {G : Derived Y} {F : Derived V} (ε : (derivedInverseImage i).obj G ⟶ F)
    (α : (derivedInverseImage e).obj ((derivedInverseImage t).obj G) ⟶
      (derivedInverseImage p).obj ((derivedInverseImage t).obj G))
    (β : (derivedInverseImage s).obj ((derivedInverseImage v).obj F) ⟶
      (derivedInverseImage q).obj ((derivedInverseImage v).obj F)),
    SquareRestriction he' hp' ε (flatten t α) (flatten v β) ↔
      SquareRestriction he hp ((squareValue h).hom.app G ≫ (derivedInverseImage v).map ε) α β

/-- Conjugation by composition commutes with changing the parameter space across two commuting squares. -/
def FlattenPullback : Prop :=
  ∀ {W X W' X' Y : TopCat.{u}}
    {r' : W' ⟶ W} {r : X' ⟶ X} {e p : W ⟶ X} {e' p' : W' ⟶ X'}
    {t : X ⟶ Y} {t' : X' ⟶ Y} (he : r' ≫ e = e' ≫ r) (hp : r' ≫ p = p' ≫ r)
    (ht : r ≫ t = t')
    (he' : r' ≫ (e ≫ t) = e' ≫ t') (hp' : r' ≫ (p ≫ t) = p' ≫ t')
    {F : Derived Y} (α : (derivedInverseImage e).obj ((derivedInverseImage t).obj F) ⟶
      (derivedInverseImage p).obj ((derivedInverseImage t).obj F)),
    let c := eqToIso (congrArg (fun f => (derivedInverseImage f).obj F) ht.symm) ≪≫
      (derivedInverseImageComposition r t).app F
    let a := (derivedInverseImage e').map c.hom ≫
      (squareValue he).inv.app ((derivedInverseImage t).obj F) ≫
      (derivedInverseImage r').map α ≫
      (squareValue hp).hom.app ((derivedInverseImage t).obj F) ≫ (derivedInverseImage p').map c.inv
    flatten t' a = pullbackMorphism r' he' hp' (flatten t α)

/-- The same change of parameter expressed directly by the pullback of the restricted coefficient arrow. -/
def FlattenRestriction : Prop :=
  ∀ {W X W' X' Y : TopCat.{u}}
    {r' : W' ⟶ W} {r : X' ⟶ X} {e p : W ⟶ X} {e' p' : W' ⟶ X'}
    {t : X ⟶ Y} {t' : X' ⟶ Y} (he : r' ≫ e = e' ≫ r) (hp : r' ≫ p = p' ≫ r)
    (ht : r ≫ t = t')
    (he' : r' ≫ (e ≫ t) = e' ≫ t') (hp' : r' ≫ (p ≫ t) = p' ≫ t')
    {F : Derived Y} (α : (derivedInverseImage e).obj ((derivedInverseImage t).obj F) ⟶
      (derivedInverseImage p).obj ((derivedInverseImage t).obj F)),
    let c := eqToIso (congrArg (fun f => (derivedInverseImage f).obj F) ht.symm) ≪≫
      (derivedInverseImageComposition r t).app F
    flatten t' ((derivedInverseImage e').map c.hom ≫
      (derivedInverseImageComposition e' r).inv.app ((derivedInverseImage t).obj F) ≫
      pullbackMorphism r' he hp α ≫
      (derivedInverseImageComposition p' r).hom.app ((derivedInverseImage t).obj F) ≫
      (derivedInverseImage p').map c.inv) =
        pullbackMorphism r' he' hp' (flatten t α)
/-- The transposed square equation expressed using pullback along the composite maps. -/
def SquareRestrictionPullbackForm : Prop :=
  ∀ {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F)
    (α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F),
    SquareRestriction he hp ε α β ↔
      pullbackMorphism j he hp α ≫
        (derivedInverseImageComposition q i).hom.app G ≫ (derivedInverseImage q).map ε =
      (derivedInverseImageComposition v i).hom.app G ≫ (derivedInverseImage v).map ε ≫ β

/-- A transposed comparison persists under compatible changes of both parameter spaces. -/
def SquareRestrictionParameterChange : Prop :=
  ∀ {U X V W V' W' : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W} {j' : V' ⟶ W'}
    (k : W' ⟶ W) (l : V' ⟶ V) (_hl : j' ≫ k = l ≫ j)
    {e p : W ⟶ X} {v q : V ⟶ U} {e' p' : W' ⟶ X} {v' q' : V' ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (hke : k ≫ e = e') (hkp : k ≫ p = p') (hlv : l ≫ v = v') (hlq : l ≫ q = q')
    (he' : j' ≫ e' = v' ≫ i) (hp' : j' ≫ p' = q' ≫ i)
    {G : Derived X} {F : Derived U} {ε : (derivedInverseImage i).obj G ⟶ F}
    {α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G}
    {β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F},
    SquareRestriction he hp ε α β →
      SquareRestriction he' hp' ε (pullbackMorphism k hke hkp α) (pullbackMorphism l hlv hlq β)

/-- Paste the transposed comparison equations using the composite coefficient map. -/
def SquareRestrictionHorizontalPasting : Prop :=
  ∀ {U X Z V Y W : TopCat.{u}}
    {j : U ⟶ X} {j' : X ⟶ Z} {i : V ⟶ Y} {i' : Y ⟶ W}
    {v q : U ⟶ V} {e p : X ⟶ Y} {e' p' : Z ⟶ W}
    (h : j ≫ e = v ≫ i) (k : j ≫ p = q ≫ i)
    (h' : j' ≫ e' = e ≫ i') (k' : j' ≫ p' = p ≫ i')
    {G : Derived W} {F : Derived Y} {K : Derived V}
    (ε : (derivedInverseImage i').obj G ⟶ F) (η : (derivedInverseImage i).obj F ⟶ K)
    {α : (derivedInverseImage e').obj G ⟶ (derivedInverseImage p').obj G}
    {β : (derivedInverseImage e).obj F ⟶ (derivedInverseImage p).obj F}
    {γ : (derivedInverseImage v).obj K ⟶ (derivedInverseImage q).obj K}
    (_hr : SquareRestriction h' k' ε α β) (_hs : SquareRestriction h k η β γ),
    SquareRestriction (horizontalSquare h h') (horizontalSquare k k')
      ((derivedInverseImageComposition i i').hom.app G ≫ (derivedInverseImage i).map ε ≫ η)
      α γ
/-- Compatible maps of the coefficient complexes give the same two composites through the
transposed comparison. -/
def SquareRestrictionNaturality : Prop :=
  ∀ {U X V W : TopCat.{u}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G G' : Derived X} {F F' : Derived U} (c : G ⟶ G') (d : F ⟶ F')
    {ε : (derivedInverseImage i).obj G ⟶ F} {ε' : (derivedInverseImage i).obj G' ⟶ F'}
    (_hc : (derivedInverseImage i).map c ≫ ε' = ε ≫ d)
    {α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G}
    {α' : (derivedInverseImage e).obj G' ⟶ (derivedInverseImage p).obj G'}
    {β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F}
    {β' : (derivedInverseImage v).obj F' ⟶ (derivedInverseImage q).obj F'}
    (_hd : (derivedInverseImage v).map d ≫ β' = β ≫ (derivedInverseImage q).map d)
    (_h : SquareRestriction he hp ε α β) (_h' : SquareRestriction he hp ε' α' β'),
    (derivedInverseImage j).map ((derivedInverseImage e).map c ≫ α') ≫
        ((squareValue hp).hom.app G' ≫ (derivedInverseImage q).map ε') =
      (derivedInverseImage j).map (α ≫ (derivedInverseImage p).map c) ≫
        ((squareValue hp).hom.app G' ≫ (derivedInverseImage q).map ε')

end Expected
end RepTheorySurvey.Geometric.ClosedSupportPullbackPastingSpecs
