import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Group.ULift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u v w

namespace LinearAlgebraicGroups
namespace Specs
namespace Fppf

noncomputable section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w})

/-- A sheaf of sets with a right action on sections, compatible with restriction. -/
structure RightAction where
  sheaf : Sheaf J (Type w)
  act : ∀ {U : C}, sheaf.obj.obj (op U) → G.obj (op U) → sheaf.obj.obj (op U)
  act_one : ∀ {U : C} (x : sheaf.obj.obj (op U)), act x 1 = x
  act_mul : ∀ {U : C} (x : sheaf.obj.obj (op U)) (g h : G.obj (op U)),
    act (act x g) h = act x (g * h)
  map_act : ∀ {U V : C} (f : V ⟶ U) (x : sheaf.obj.obj (op U)) (g : G.obj (op U)),
    sheaf.obj.map f.op (act x g) = act (sheaf.obj.map f.op x) (G.map f.op g)

variable {J G}

abbrev RightAction.Section (P : RightAction J G) (U : C) := P.sheaf.obj.obj (op U)

abbrev RightAction.res (P : RightAction J G) {U V : C} (f : V ⟶ U) :
    P.Section U → P.Section V := P.sheaf.obj.map f.op

/-- Isomorphisms of sheaves respecting the right action. -/
structure RightActionIso (P Q : RightAction J G) where
  iso : P.sheaf ≅ Q.sheaf
  equivariant : ∀ {U : C} (x : P.Section U) (g : G.obj (op U)),
    iso.hom.hom.app (op U) (P.act x g) = Q.act (iso.hom.hom.app (op U) x) g

/-- The sieve of maps along which a section exists. -/
def RightAction.sectionSieve (P : RightAction J G) (U : C) : Sieve U where
  arrows V _ := Nonempty (P.Section V)
  downward_closed := fun ⟨x⟩ f ↦ ⟨P.res f x⟩

/-- A right action is a torsor when it has local sections and any two sections differ by
a unique group element. The latter condition also applies on objects with no sections. -/
def IsTorsor (P : RightAction J G) : Prop :=
  (∀ (U : C) (x : P.Section U), Function.Bijective (P.act x)) ∧
  ∀ U : C, P.sectionSieve U ∈ J U

/-- The right translation action on the group sheaf. -/
def regularAction (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) : RightAction J G where
  sheaf := ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 hG⟩
  act := fun {U} (x : G.obj (op U)) g ↦ x * g
  act_one := mul_one
  act_mul := mul_assoc
  map_act f x g := map_mul (G.map f.op).hom x g

/-- Restriction to the slice along a morphism of base objects. -/
def restrict {X Y : C} (f : X ⟶ Y) {K : (Over Y)ᵒᵖ ⥤ GrpCat.{w}}
    (P : RightAction (J.over Y) K) : RightAction (J.over X) ((Over.map f).op ⋙ K) where
  sheaf := (J.overMapPullback (Type w) f).obj P.sheaf
  act := P.act
  act_one := P.act_one
  act_mul := P.act_mul
  map_act g := P.map_act ((Over.map f).map g)

def RestrictType (J : GrothendieckTopology C) := ∀ {X Y : C} (f : X ⟶ Y) {K : (Over Y)ᵒᵖ ⥤ GrpCat.{w}},
    RightAction (J.over Y) K → RightAction (J.over X) ((Over.map f).op ⋙ K)

def RestrictTorsor (J : GrothendieckTopology C) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) {K : (Over Y)ᵒᵖ ⥤ GrpCat.{w}}
    (P : RightAction (J.over Y) K), IsTorsor P → IsTorsor (restrict f P)

/-- Pull back a sheaf action from a site to the slice over one test object. -/
def onSlice (P : RightAction J G) (U : C) :
    RightAction (J.over U) ((Over.forget U).op ⋙ G) where
  sheaf := (J.overPullback (Type w) U).obj P.sheaf
  act := P.act
  act_one := P.act_one
  act_mul := P.act_mul
  map_act f := P.map_act f.left

lemma groupSheafOnSlice (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) (U : C) :
    Presieve.IsSheaf (J.over U) (((Over.forget U).op ⋙ G) ⋙ forget GrpCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((J.overPullback (Type w) U).obj (regularAction hG).sheaf).property

/-- Local triviality means equivariant isomorphism with right translation on a covering sieve. -/
def LocallyTrivial (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) (P : RightAction J G) : Prop :=
  ∀ U : C, ∃ R ∈ J U, ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, R f →
    Nonempty (RightActionIso (regularAction (groupSheafOnSlice hG V)) (onSlice P V))

def TorsorIffLocallyTrivial (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) : Prop :=
  ∀ (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) (P : RightAction J G),
    IsTorsor P ↔ LocallyTrivial hG P

def SectionTrivialization (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) :=
  ∀ (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) (P : RightAction J G)
    (U : C) (x : P.Section U), IsTorsor P →
    {e : RightActionIso (regularAction (groupSheafOnSlice hG U)) (onSlice P U) //
      ∀ (W : Over U) (g : G.obj (op W.left)),
        e.iso.hom.hom.app (op W) g = P.act (P.res W.hom x) g}

/-- A right fppf action over a k-scheme uses the group of maps to the k-group scheme
from the underlying test k-scheme. The two slice topologies are induced from the big site. -/
abbrev schemeTopology (k : Type u) [Field k] : GrothendieckTopology (SchemeOver k) :=
  Scheme.fppfTopology.over (Spec (CommRingCat.of k))

abbrev torsorTopology {k : Type u} [Field k] (S : SchemeOver k) :
    GrothendieckTopology (Over S) := (schemeTopology k).over S

def liftGroups : GrpCat.{v} ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (ULift.{w} A)
  map f := GrpCat.ofHom {
    toFun := fun x ↦ ⟨f x.down⟩
    map_one' := by apply ULift.ext; exact map_one f.hom
    map_mul' x y := by apply ULift.ext; exact map_mul f.hom x.down y.down }
  map_id := by intros; apply GrpCat.ext; intro x; rfl
  map_comp := by intros; apply GrpCat.ext; intro x; rfl

def groupSections {k : Type u} [Field k] (S : SchemeOver k) (H : GroupScheme k) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u+1} :=
  (Over.forget S).op ⋙ (yonedaGrp.obj H ⋙ liftGroups.{u,u+1})

abbrev SchemeAction {k : Type u} [Field k] (S : SchemeOver k) (H : GroupScheme k) :=
  RightAction (torsorTopology S) (groupSections S H)

abbrev Torsor (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) :=
  {P : RightAction J G // IsTorsor P}

abbrev FppfTorsor {k : Type u} [Field k] (S : SchemeOver k) (H : GroupScheme k) :=
  Torsor (torsorTopology S) (groupSections S H)

def GroupSectionsSheaf : Prop :=
  ∀ {k : Type u} [Field k] (S : SchemeOver k) (H : GroupScheme k),
    Presieve.IsSheaf (torsorTopology S) (groupSections S H ⋙ forget GrpCat)

section Represented

variable {k : Type u} [Field k] {S : SchemeOver k} {H : GroupScheme k}

/-- The big fppf sheaf represented by an object of the slice. -/
abbrev representedSheaf (X : Over S) : Sheaf (torsorTopology S) (Type (u + 1)) :=
  (torsorTopology S).uliftYoneda.{u+1}.obj X

/-- The source of a scheme action, with structure map through its first factor. -/
abbrev actionSource (X : Over S) (H : GroupScheme k) : Over S :=
  Over.mk (prod.fst ≫ X.hom : X.left ⨯ H.X ⟶ S)

/-- A pair of maps into the factors, viewed as a map over the base. -/
def actionPair {X T : Over S} (x : T ⟶ X) (g : T.left ⟶ H.X) :
    T ⟶ actionSource X H :=
  Over.homMk (prod.lift x.left g) (by simp)

/-- Right actions on a scheme over S. The axioms are expressed on all test
schemes over S, which is equivalent by Yoneda to the action diagrams. -/
structure SchemeRightAction (X : Over S) (H : GroupScheme k) where
  action : actionSource X H ⟶ X
  one : ∀ {T : Over S} (x : T ⟶ X),
    actionPair x ((1 : (groupSections S H).obj (op T)).down) ≫ action = x
  mul : ∀ {T : Over S} (x : T ⟶ X) (g h : (groupSections S H).obj (op T)),
    actionPair (actionPair x g.down ≫ action) h.down ≫ action =
      actionPair x (g * h).down ≫ action

set_option backward.isDefEq.respectTransparency false in
/-- The induced right action on the representable fppf sheaf. -/
def representedAction {X : Over S} (a : SchemeRightAction X H) : SchemeAction S H where
  sheaf := representedSheaf X
  act x g := ⟨actionPair x.down g.down ≫ a.action⟩
  act_one x := ULift.ext (a.one x.down)
  act_mul x g h := ULift.ext (a.mul x.down g h)
  map_act f x g := by
    apply ULift.ext
    change f ≫ actionPair x.down g.down ≫ a.action =
      actionPair (f ≫ x.down) (f.left ≫ g.down) ≫ a.action
    rw [← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · change (f.left ≫ prod.lift x.down.left g.down) ≫ prod.fst = _
      simp only [Category.assoc, prod.lift_fst, actionPair, Over.homMk_left,
        Over.comp_left]
    · change (f.left ≫ prod.lift x.down.left g.down) ≫ prod.snd = _
      simp only [Category.assoc, prod.lift_snd, actionPair, Over.homMk_left,
        Over.comp_left]

/-- The morphism `(x,h) ↦ (x,xh)` into the fiber product over S. -/
def comparison {X : Over S} (a : SchemeRightAction X H) :
    X.left ⨯ H.X ⟶ pullback X.hom X.hom :=
  pullback.lift prod.fst a.action.left (Over.w a.action).symm

/-- A single morphism is fppf if it is faithfully flat and locally of finite presentation. -/
def IsFppf {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p

def RepresentedTorsorCriterion : Prop :=
  ∀ {k : Type u} [Field k] {S : SchemeOver k} {H : GroupScheme k}
    (_hH : LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom)
    {X : Over S} (a : SchemeRightAction X H),
    IsTorsor (representedAction a) ↔ IsFppf X.hom.left ∧ IsIso (comparison a)

/-- Every right action on a representable sheaf comes from a scheme action
on the representing object. The given representation respects that action. -/
def RepresentSheafAction : Prop :=
  ∀ {k : Type u} [Field k] {S : SchemeOver k} {H : GroupScheme k}
    (P : SchemeAction S H) (X : Over S) (e : representedSheaf X ≅ P.sheaf),
    ∃ (a : SchemeRightAction X H) (e' : RightActionIso (representedAction a) P), e'.iso = e

end Represented

section Classes

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}

def RightActionIso.refl (P : RightAction J G) : RightActionIso P P :=
  ⟨Iso.refl _, fun _ _ ↦ rfl⟩

def RightActionIso.symm {P Q : RightAction J G} (e : RightActionIso P Q) :
    RightActionIso Q P := by
  refine ⟨e.iso.symm, ?_⟩
  intro U x g
  let i := (sheafToPresheaf J (Type w)).mapIso e.iso
  let j := (evaluation _ _).obj (op U) |>.mapIso i
  apply j.toEquiv.injective
  change j.hom (j.inv (Q.act x g)) = j.hom (P.act (j.inv x) g)
  rw [j.inv_hom_id_apply]
  change Q.act x g = e.iso.hom.hom.app (op U) (P.act (j.inv x) g)
  rw [e.equivariant]
  change Q.act x g = Q.act (j.hom (j.inv x)) g
  rw [j.inv_hom_id_apply]

def RightActionIso.trans {P Q R : RightAction J G} (e : RightActionIso P Q)
    (d : RightActionIso Q R) : RightActionIso P R := by
  refine ⟨e.iso ≪≫ d.iso, ?_⟩
  intro U x g
  change d.iso.hom.hom.app (op U) (e.iso.hom.hom.app (op U) (P.act x g)) =
    R.act (d.iso.hom.hom.app (op U) (e.iso.hom.hom.app (op U) x)) g
  rw [e.equivariant, d.equivariant]

/-- The translation action of the group is a torsor. -/
def regularTorsor (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) : Torsor J G :=
  ⟨regularAction hG, fun U x ↦ by
    change (G.obj (op U) : Type w) at x
    exact (Equiv.mulLeft x).bijective, fun U ↦ by
    apply J.superset_covering _ (J.top_mem U)
    exact fun V _ _ ↦ ⟨(1 : G.obj (op V))⟩⟩

/-- Classes of right torsors modulo equivariant isomorphism. -/
def torsorSetoid (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) : Setoid (Torsor J G) where
  r P Q := Nonempty (RightActionIso P.1 Q.1)
  iseqv := ⟨fun P ↦ ⟨.refl P.1⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨d⟩ ↦ ⟨e.trans d⟩⟩

/-- A trivialization by the translates of a section of the terminal object. -/
def GlobalSectionTrivialization (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) : Prop :=
  ∀ (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) (P : Torsor J G)
    (T : C) (hT : IsTerminal T) (x : P.1.Section T),
    ∃ e : RightActionIso (regularAction hG) P.1,
      ∀ (U : C) (g : G.obj (op U)), e.iso.hom.hom.app (op U) g = P.1.act (P.1.res (hT.from U) x) g

section Field

variable (k : Type u) [Field k]

abbrev fieldBase : SchemeOver k := Over.mk (𝟙 (Spec (CommRingCat.of k)))

/-- The test object `Spec k` over `Spec k`. -/
abbrev fieldTest : Over (fieldBase k) := Over.mk (𝟙 (fieldBase k))

/-- The fppf cohomology set classifying right H-torsors over the field. -/
def H1fppf (H : GroupScheme k) : Type (u + 2) :=
  Quotient (torsorSetoid (torsorTopology (fieldBase k)) (groupSections (fieldBase k) H))

def H1fppfType := ∀ (k : Type u) [Field k], GroupScheme k → Type (u + 2)

variable {k}

/-- The neutral element is the class of the product torsor. -/
def neutralClass {H : GroupScheme k}
    (hG : Presieve.IsSheaf (torsorTopology (fieldBase k))
      (groupSections (fieldBase k) H ⋙ forget GrpCat)) : H1fppf k H :=
  Quotient.mk _ (regularTorsor hG)

def NeutralClassType :=
  ∀ {k : Type u} [Field k] {H : GroupScheme k},
    Presieve.IsSheaf (torsorTopology (fieldBase k))
      (groupSections (fieldBase k) H ⋙ forget GrpCat) → H1fppf k H

def RationalPointCriterion : Prop :=
  ∀ {k : Type u} [Field k] {H : GroupScheme k}
    (hG : Presieve.IsSheaf (torsorTopology (fieldBase k))
      (groupSections (fieldBase k) H ⋙ forget GrpCat)) (P : FppfTorsor (fieldBase k) H),
    (Quotient.mk _ P : H1fppf k H) = neutralClass hG ↔ Nonempty (P.1.Section (fieldTest k))

end Field
end Classes

section ContractedProduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G K : Cᵒᵖ ⥤ GrpCat.{w}} (φ : G ⟶ K) (P : RightAction J G)

/-- The orbit relation `(p,b) · g = (p·g, φ(g)⁻¹ b)`, written without inverses
in its defining equation for the second coordinate. -/
def contractedRelation (U : C) : Setoid (P.Section U × K.obj (op U)) where
  r p q := ∃ g : G.obj (op U), P.act p.1 g = q.1 ∧ φ.app (op U) g * q.2 = p.2
  iseqv := by
    constructor
    · intro p
      exact ⟨1, P.act_one _, by simp⟩
    · rintro p q ⟨g, hg, hb⟩
      refine ⟨g⁻¹, ?_, ?_⟩
      · rw [← hg, P.act_mul, mul_inv_cancel, P.act_one]
      · rw [← hb, map_inv, inv_mul_cancel_left]
    · rintro p q r ⟨g,hg,hb⟩ ⟨g',hg',hb'⟩
      exact ⟨g * g', by rw [← P.act_mul, hg, hg'],
        by rw [map_mul, mul_assoc, hb', hb]⟩

/-- The presheaf quotient used to form the contracted product. -/
def contractedPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := Quotient (contractedRelation φ P U.unop)
  map f := ↾(Quotient.map
    (fun p ↦ (P.sheaf.obj.map f p.1, K.map f p.2)) (by
      rintro p q ⟨g, hg, hb⟩
      refine ⟨G.map f g, ?_, ?_⟩
      · change P.act (P.sheaf.obj.map f.unop.op p.1) (G.map f.unop.op g) =
          P.sheaf.obj.map f.unop.op q.1
        rw [← P.map_act, hg]
      · change φ.app _ (G.map f g) * K.map f q.2 = K.map f p.2
        rw [NatTrans.naturality_apply φ f g, ← map_mul, hb]))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro p
    refine Quotient.inductionOn p ?_
    intro x
    change Quotient.mk _ (P.sheaf.obj.map (𝟙 U) x.1, K.map (𝟙 U) x.2) = Quotient.mk _ x
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    refine Quotient.inductionOn p ?_
    intro x
    change Quotient.mk _ (P.sheaf.obj.map (f ≫ g) x.1, K.map (f ≫ g) x.2) =
      Quotient.mk _ (P.sheaf.obj.map g (P.sheaf.obj.map f x.1), K.map g (K.map f x.2))
    simp [Functor.map_comp]

/-- The section of the quotient presheaf represented by a pair. -/
def contractedPair {U : C} (p : P.Section U) (b : K.obj (op U)) :
    (contractedPresheaf φ P).obj (op U) := Quotient.mk _ (p,b)

variable (J)

/-- The contracted product is the sheafification of the presheaf of orbits. -/
def contractedProduct [HasWeakSheafify J (Type w)] :
    Sheaf J (Type w) := (presheafToSheaf J (Type w)).obj (contractedPresheaf φ P)

set_option linter.checkUnivs false in
def ContractedProductType :=
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {G K : Cᵒᵖ ⥤ GrpCat.{w}}
    (_ : G ⟶ K) (_ : RightAction J G) [HasWeakSheafify J (Type w)], Sheaf J (Type w)

variable {J}

/-- Action and torsor properties of extension of structure group, with its
action specified on the images of all pairs in the presheaf quotient. -/
def ExtensionOfStructureGroup (J : GrothendieckTopology C) [HasSheafify J (Type w)]
    [J.WEqualsLocallyBijective (Type w)] : Prop :=
  ∀ {G K : Cᵒᵖ ⥤ GrpCat.{w}} (φ : G ⟶ K)
    (_hK : Presieve.IsSheaf J (K ⋙ forget GrpCat)) (P : Torsor J G),
    ∃ (Q : Torsor J K) (e : Q.1.sheaf ≅ contractedProduct J φ P.1),
      ∀ (U : C) (p : P.1.Section U) (b c : K.obj (op U)),
        e.hom.hom.app (op U) (Q.1.act (e.inv.hom.app (op U)
          ((toSheafify J (contractedPresheaf φ P.1)).app (op U) (contractedPair φ P.1 p b))) c) =
            (toSheafify J (contractedPresheaf φ P.1)).app (op U) (contractedPair φ P.1 p (b * c))

end ContractedProduct

section SchemeInterfaces

variable {k : Type u} [Field k] {S T : SchemeOver k} {H : GroupScheme k}

def FppfTorsorType :=
  ∀ {k : Type u} [Field k], SchemeOver k → GroupScheme k → Type (u + 2)

def SchemeRightActionType :=
  ∀ {k : Type u} [Field k] {S : SchemeOver k}, Over S → GroupScheme k → Type u

def RepresentedActionType :=
  ∀ {k : Type u} [Field k] {S : SchemeOver k} {H : GroupScheme k} {X : Over S},
    SchemeRightAction X H → SchemeAction S H

def ComparisonType :=
  ∀ {k : Type u} [Field k] {S : SchemeOver k} {H : GroupScheme k} {X : Over S},
    SchemeRightAction X H → (X.left ⨯ H.X ⟶ pullback X.hom X.hom)

/-- Base change on the big slice site by restriction of test schemes. -/
def schemeBaseChange (f : T ⟶ S) (P : SchemeAction S H) : SchemeAction T H :=
  restrict f P

def SchemeBaseChangeType :=
  ∀ {k : Type u} [Field k] {S T : SchemeOver k} {H : GroupScheme k},
    (T ⟶ S) → SchemeAction S H → SchemeAction T H

def SchemeBaseChangePreservesTorsors : Prop :=
  ∀ {k : Type u} [Field k] {S T : SchemeOver k} {H : GroupScheme k}
    (f : T ⟶ S) (P : SchemeAction S H), IsTorsor P → IsTorsor (schemeBaseChange f P)

/-- Over the field a point of a represented torsor is a k-morphism from Spec k. -/
def RepresentedRationalPointCriterion : Prop :=
  ∀ {k : Type u} [Field k] {H : GroupScheme k}
    (hG : Presieve.IsSheaf (torsorTopology (fieldBase k))
      (groupSections (fieldBase k) H ⋙ forget GrpCat))
    {X : Over (fieldBase k)} (a : SchemeRightAction X H) (ha : IsTorsor (representedAction a)),
    (Quotient.mk _ (⟨representedAction a, ha⟩ : FppfTorsor (fieldBase k) H) : H1fppf k H) =
      neutralClass hG ↔ Nonempty (fieldBase k ⟶ X.left)

end SchemeInterfaces

def LocalSectionTrivialization {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}) : Prop :=
  Nonempty (SectionTrivialization J G)

section GenericTypes

set_option linter.checkUnivs false in
def BaseChangeActionType :=
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C), RestrictType.{u,v,w} J

def BaseChangePreservesTorsors : Prop :=
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C), RestrictTorsor.{u,v,w} J

def TorsorLocalTriviality : Prop :=
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}),
    TorsorIffLocallyTrivial J G

def TrivializationOnSlice : Prop :=
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}),
    LocalSectionTrivialization J G

def TrivializationAtGlobalSection : Prop :=
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w}),
    GlobalSectionTrivialization J G

def ContractedExtension : Prop :=
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J (Type w)]
    [J.WEqualsLocallyBijective (Type w)], ExtensionOfStructureGroup J

def schemeRightActionValue : SchemeRightActionType.{u} := @SchemeRightAction

end GenericTypes

section SchemeExtension

variable {k : Type u} [Field k] (S : SchemeOver k) {H K : GroupScheme k}

/-- A homomorphism of k-group schemes induces a homomorphism on the big fppf site. -/
def groupSectionsMap (f : H ⟶ K) : groupSections S H ⟶ groupSections S K :=
  Functor.whiskerLeft (Over.forget S).op (Functor.whiskerRight (yonedaGrp.map f) liftGroups.{u,u+1})

def GroupSectionsMapType :=
  ∀ {k : Type u} [Field k] (S : SchemeOver k) {H K : GroupScheme k},
    (H ⟶ K) → (groupSections S H ⟶ groupSections S K)

/-- The extension on the fppf site has underlying sheaf the contracted product.
Sections represented by pairs have the right translation action on the second coordinate. -/
def IsStructureGroupExtension (f : H ⟶ K) (P : FppfTorsor S H) (Q : FppfTorsor S K) : Prop :=
  ∃ e : Q.1.sheaf ≅ contractedProduct (torsorTopology S) (groupSectionsMap S f) P.1,
    ∀ (U : Over S) (p : P.1.Section U) (b c : (groupSections S K).obj (op U)),
      e.hom.hom.app (op U) (Q.1.act (e.inv.hom.app (op U)
        ((toSheafify (torsorTopology S) (contractedPresheaf (groupSectionsMap S f) P.1)).app (op U)
          (contractedPair (groupSectionsMap S f) P.1 p b))) c) =
      (toSheafify (torsorTopology S) (contractedPresheaf (groupSectionsMap S f) P.1)).app (op U)
        (contractedPair (groupSectionsMap S f) P.1 p (b * c))

def SchemeContractedExtension : Prop :=
  ∀ {k : Type u} [Field k] (S : SchemeOver k) {H K : GroupScheme k}
    (f : H ⟶ K) (P : FppfTorsor S H), ∃ Q : FppfTorsor S K, IsStructureGroupExtension S f P Q

end SchemeExtension

/-- Equivariant isomorphism preserves the torsor condition. -/
def TorsorInvariantUnderIso : Prop :=
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}
    {P Q : RightAction J G}, RightActionIso P Q → (IsTorsor P ↔ IsTorsor Q)

/-- Restricting a representable sheaf represents the scheme-theoretic base change. -/
def RepresentedBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {S T : SchemeOver k} (f : T ⟶ S) (X : Over S),
    Nonempty (((schemeTopology k).overMapPullback (Type (u + 1)) f).obj (representedSheaf X) ≅
      representedSheaf ((Over.pullback f).obj X))

end
end Fppf
end Specs
end LinearAlgebraicGroups
