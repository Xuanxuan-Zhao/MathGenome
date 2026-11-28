import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.ClosedSupportBaseChangeSpecs

open Analytic Analytic.IntersectionComplex LocalSheaf
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open EquivariantIntersectionComplexesSpecs (Intertwines)

/-- The equation on the intersection after transposing through the parameter adjunction.
The coefficient arrow here is the pullback of the comparison followed by the support counit. -/
def SquareRestriction {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F)
    (α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F) : Prop :=
  (derivedInverseImage j).map α ≫ (squareValue hp).hom.app G ≫
    (derivedInverseImage q).map ε =
      (squareValue he).hom.app G ≫ (derivedInverseImage v).map ε ≫ β

/-- Commutation with the two actual mates for a coefficient comparison into a right adjoint. -/
def MateCommutes {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    {R : BoundedBelow U ⥤ BoundedBelow X} (b : boundedBelowInverseImage i ⊣ R)
    {F : BoundedBelow U} {G : BoundedBelow X} (c : G ⟶ R.obj F)
    (α : (derivedInverseImage e).obj G.obj ⟶ (derivedInverseImage p).obj G.obj)
    (β : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj) : Prop :=
  α ≫ ((boundedBelowInverseImage p).map c ≫ adjointSquareMap (pullbackSquare hp) a b F).hom =
    ((boundedBelowInverseImage e).map c ≫ adjointSquareMap (pullbackSquare he) a b F).hom ≫
      ((derivedDirectImage j).map (ObjectProperty.homMk β)).hom

/-- The transport equation using the action and projection mates at every common jet. -/
def AgreesWithMates {J : JetSystem.{0}} {U V : TopCat.{0}}
    {C : JetAction J U} {E : JetAction J V} {F : BoundedBelow U} {G : Derived V}
    {j : U ⟶ V} (h : Intertwines C E j) (a : DerivedAdjunctions.{0})
    (α : C.Equivariance F.obj) (β : E.Equivariance G)
    (c : G ⟶ ((derivedDirectImage j).obj F).obj) : Prop :=
  ∀ (k : ℕ) (hu : C.cutoff ≤ k) (hv : E.cutoff ≤ k),
    let H := J.group k
    let jH := parameterInclusion H j
    let bcA := directImageComparison (h k hu hv) (a jH) (a j) F
    let bcP := directImageComparison (projectionSquare H j) (a jH) (a j) F
    (β.datum k hv).iso.hom ≫ (derivedInverseImage (AnalyticAction.projection H V)).map c ≫
        bcP.hom =
      (derivedInverseImage (E.action k hv).act).map c ≫ bcA.hom ≫
        ((derivedDirectImage jH).map (ObjectProperty.homMk (α.datum k hu).iso.hom)).hom

/-- Invertibility of the two actual mates at every common jet. -/
def MatesAreIso {J : JetSystem.{0}} {U V : TopCat.{0}}
    {C : JetAction J U} {E : JetAction J V} {j : U ⟶ V}
    (h : Intertwines C E j) (a : DerivedAdjunctions.{0}) (F : BoundedBelow U) : Prop :=
  ∀ (k : ℕ) (hu : C.cutoff ≤ k) (hv : E.cutoff ≤ k),
    let H := J.group k
    let jH := parameterInclusion H j
    IsIso (directImageComparison (h k hu hv) (a jH) (a j) F) ∧
      IsIso (directImageComparison (projectionSquare H j) (a jH) (a j) F)

namespace Expected

/-- The actual bounded-below mate of a closed support square is invertible.
The range condition includes the case of an empty intersection. -/
def ClosedBaseChange : Prop :=
  ∀ {U X V Y : TopCat.{0}} {j : U ⟶ X} {i : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (_hi : IsClosedEmbedding i) (_hj : IsClosedEmbedding j) (h : j ≫ e = v ≫ i),
    Set.range j = e ⁻¹' Set.range i →
    ∀ (a : DerivedAdjunctions.{0}) (F : BoundedBelow V),
      IsIso (directImageComparison h (a j) (a i) F)

/-- Inverse image along a closed embedding is bijective on the indicated derived Hom set
as soon as the target complex has cohomology supported on the image. -/
def SupportedRestrictionBijective : Prop :=
  ∀ {U X : TopCat.{0}} {j : U ⟶ X} (_ : IsClosedEmbedding j)
    (_a : DerivedAdjunctions.{0}) (F G : BoundedBelow X),
    DerivedSupportedOn (Set.range j) G →
      Function.Bijective ((derivedInverseImage j).map : (F.obj ⟶ G.obj) → _)

/-- Transposition of the action and projection mate equation, with any chosen right adjoint
to inverse image on the support. The two squares can be arbitrary commuting squares. -/
def MateEquationIff : Prop :=
  ∀ {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    {R : BoundedBelow U ⥤ BoundedBelow X} (b : boundedBelowInverseImage i ⊣ R)
    {F : BoundedBelow U} {G : BoundedBelow X} (c : G ⟶ R.obj F)
    (α : (derivedInverseImage e).obj G.obj ⟶ (derivedInverseImage p).obj G.obj)
    (β : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj),
    MateCommutes he hp a b c α β ↔
      SquareRestriction he hp ((boundedBelowInverseImage i).map c ≫ b.counit.app F).hom α β

/-- The same transposition with the actual derived direct image on the support. -/
def DerivedDirectImageMateEquationIff : Prop :=
  ∀ {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (a : DerivedAdjunctions.{0})
    {F : BoundedBelow U} {G : BoundedBelow X} (c : G ⟶ (derivedDirectImage i).obj F)
    (α : (derivedInverseImage e).obj G.obj ⟶ (derivedInverseImage p).obj G.obj)
    (β : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj),
    MateCommutes he hp (a j) (a i) c α β ↔
      SquareRestriction he hp ((boundedBelowInverseImage i).map c ≫ (a i).counit.app F).hom α β

/-- The two mate isomorphisms for an equivariant closed embedding. -/
def ActionProjectionMatesAreIso : Prop :=
  ∀ {U V : TopCat.{0}} {J : JetSystem.{0}} {j : U ⟶ V}
    {C : JetAction J U} {E : JetAction J V}
    (_ : IsClosedEmbedding j) (h : Intertwines C E j)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow U),
    MatesAreIso h a F

/-- Lift the datum on a closed intersection to the actual restriction of the closed
direct image, with the canonical ordinary comparison and both jet mates. -/
def StageDatum : Prop :=
  ∀ {U X V Y : TopCat.{0}} {i : V ⟶ Y} {j : U ⟶ X}
    {e : X ⟶ Y} {v : U ⟶ V} {J : JetSystem.{0}} {C : JetAction J U} {E : JetAction J X}
    (_hi : IsClosedEmbedding i) (_hj : IsClosedEmbedding j)
    (hs : j ≫ e = v ≫ i) (_hr : Set.range j = e ⁻¹' Set.range i)
    (h : Intertwines C E j) (_ : C.cutoff ≤ E.cutoff)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow V)
    (α : C.Equivariance ((boundedBelowInverseImage v).obj F).obj),
    let G := (boundedBelowInverseImage e).obj ((derivedDirectImage i).obj F)
    let K := (boundedBelowInverseImage v).obj F
    let c := directImageComparison hs (a j) (a i) F
    ∃ β : E.Equivariance G.obj,
      IsIso c ∧ MatesAreIso h a K ∧ AgreesWithMates h a α β c.hom

end Expected
end RepTheorySurvey.Geometric.ClosedSupportBaseChangeSpecs
