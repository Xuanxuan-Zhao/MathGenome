import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Topology.LocallyConstant.Algebra

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.AutomorphismSequence

open Pinning (AttachedDatum BasedRootDatum PinnedGroup PinnedIso SimpleRoot)
open RootGroups (AdditiveLine)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Fppf (schemeTopology IsFppf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- Sections of the group pulled back to a test scheme. -/
abbrev relativePoints (G : GroupScheme k) (S : SchemeOver k) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ yonedaGrp.obj G

/-- Base change is restriction along the functor of slices. -/
abbrev restrictIso {G H : GroupScheme k} {S T : SchemeOver k} (a : T ⟶ S)
    (i : relativePoints G S ≅ relativePoints H S) :
    relativePoints G T ≅ relativePoints H T :=
  Functor.isoWhiskerLeft (Over.map a).op i

/-- The group of automorphisms of the scalar extension on the big slice site.
By Yoneda this is the group of automorphisms of the base-changed group scheme. -/
abbrev RelativeAut (G : GroupScheme k) (S : SchemeOver k) := Aut (relativePoints G S)

def restrictAut {G : GroupScheme k} {S T : SchemeOver k} (a : T ⟶ S) :
    RelativeAut G S →* RelativeAut G T where
  toFun f := Aut.of (restrictIso a f.asIso)
  map_one' := by apply Aut.ext; apply Iso.ext; rfl
  map_mul' f g := by apply Aut.ext; apply Iso.ext; rfl

/-- The presheaf of all relative group automorphisms. -/
def automorphisms (G : GroupScheme k) : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1} where
  obj S := GrpCat.of (RelativeAut G S.unop)
  map a := GrpCat.ofHom (restrictAut a.unop)
  map_id S := by
    apply GrpCat.ext
    intro f
    apply Aut.ext
    apply Iso.ext
    exact ConcreteCategory.congr_hom
      ((presheafHom (yonedaGrp.obj G) (yonedaGrp.obj G)).map_id S) f.asIso.hom
  map_comp a b := by
    apply GrpCat.ext
    intro f
    apply Aut.ext
    apply Iso.ext
    exact ConcreteCategory.congr_hom
      ((presheafHom (yonedaGrp.obj G) (yonedaGrp.obj G)).map_comp a b) f.asIso.hom

/-- The constant étale group, evaluated as locally constant functions to a discrete group. -/
def constantGroup (D : Type u) [Group D] : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1} where
  obj S := GrpCat.of (ULift.{u+1} (LocallyConstant S.unop.left D))
  map a := GrpCat.ofHom
    { toFun := fun x ↦ ⟨x.down.comap ⟨a.unop.left, a.unop.left.continuous⟩⟩
      map_one' := by rfl
      map_mul' _ _ := by rfl }
  map_id S := by
    apply GrpCat.ext
    intro x
    apply ULift.ext
    apply LocallyConstant.ext
    intro t
    rfl
  map_comp a b := by
    apply GrpCat.ext
    intro x
    apply ULift.ext
    apply LocallyConstant.ext
    intro t
    rfl

/-- The underlying scheme of the constant group, with one copy of the base for each label. -/
def constantScheme (D : Type u) : SchemeOver k :=
  Over.mk (Limits.Sigma.desc (fun _ : D => 𝟙 (Spec (CommRingCat.of k))))

abbrev groupSections (G : GroupScheme k) : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1} :=
  yonedaGrp.obj G ⋙ Fppf.liftGroups.{u,u+1}

/-- Sectionwise lift of a ground-field group-scheme isomorphism. -/
abbrev scalarAut {G : GroupScheme k} (f : Aut G) (S : SchemeOver k) : RelativeAut G S :=
  Functor.mapAut G (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op) f

/-- Conjugation by a section, with multiplication in automorphism groups in
function-composition order. -/
def innerAut {G : GroupScheme k} {S : SchemeOver k} (g : S ⟶ G.X) :
    RelativeAut G S :=
  Aut.of
    { hom :=
        { app := fun U ↦ GrpCat.ofHom ((MulAut.conj (U.unop.hom ≫ g)).toMonoidHom)
          naturality := by
            intro U V f
            apply GrpCat.ext
            intro x
            change U.unop.left ⟶ G.X at x
            change (V.unop.hom ≫ g) * (f.unop.left ≫ x) * (V.unop.hom ≫ g)⁻¹ =
              f.unop.left ≫ ((U.unop.hom ≫ g) * x * (U.unop.hom ≫ g)⁻¹)
            simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, Over.w] }
      inv :=
        { app := fun U ↦ GrpCat.ofHom ((MulAut.conj ((U.unop.hom ≫ g)⁻¹)).toMonoidHom)
          naturality := by
            intro U V f
            apply GrpCat.ext
            intro x
            change U.unop.left ⟶ G.X at x
            change (V.unop.hom ≫ g)⁻¹ * (f.unop.left ≫ x) * ((V.unop.hom ≫ g)⁻¹)⁻¹ =
              f.unop.left ≫ ((U.unop.hom ≫ g)⁻¹ * x * ((U.unop.hom ≫ g)⁻¹)⁻¹)
            simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, Over.w] }
      hom_inv_id := by ext U x; simp [MulAut.conj_apply, mul_assoc]
      inv_hom_id := by ext U x; simp [MulAut.conj_apply, mul_assoc] }

/-- The central quotient is represented by the fppf quotient by the full scheme centre. -/
structure AdjointQuotient (G : AffineAlgebraicGroup k) where
  centre : ClosedSubgroup G.val
  isCentre : RepresentsSubgroup centre (fun _ z ↦ Centralizes (𝟙 G.val) z)
  quotient : AffineAlgebraicGroup k
  projection : G.val ⟶ quotient.val
  fppf : IsFppf projection.hom.hom.left
  kernel : IsSchemeKernel projection centre

abbrev IsGroupSheaf (F : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}) :=
  Presieve.IsSheaf (schemeTopology k) (F ⋙ forget GrpCat)

/-- Exact as fppf sheaves, with the indicated conjugation on every section
coming from the original group. The quotient need only be locally surjective. -/
structure ExactSequence (G : AffineAlgebraicGroup k) (Q : AdjointQuotient G)
    (O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}) where
  autSheaf : IsGroupSheaf (automorphisms G.val)
  outerSheaf : IsGroupSheaf O
  inner : groupSections Q.quotient.val ⟶ automorphisms G.val
  outer : automorphisms G.val ⟶ O
  onLift : ∀ (S : SchemeOver k) (g : S ⟶ G.val.X),
    inner.app (op S) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g
  innerInjective : ∀ S, Function.Injective (inner.app S)
  exact : ∀ S (f : (automorphisms G.val).obj S), outer.app S f = 1 ↔ f ∈ (inner.app S).hom.range
  outerLocallySurjective : Presheaf.IsLocallySurjective (schemeTopology k) outer

/-- A local aligned automorphism preserves the Borel and torus, whose
specified restrictions are compatible with the subgroup inclusions. -/
structure Aligned {A : AdditiveLine k} (P : PinnedGroup A) {S : SchemeOver k}
    (f : RelativeAut P.pair.G.val S) where
  torus : RelativeAut P.pair.T.group S
  borel : RelativeAut P.pair.B.group S
  torus_comm : Functor.whiskerLeft (Over.forget S).op (yonedaGrp.map P.pair.T.inclusion) ≫ f.asIso.hom =
    torus.asIso.hom ≫ Functor.whiskerLeft (Over.forget S).op (yonedaGrp.map P.pair.T.inclusion)
  borel_comm : Functor.whiskerLeft (Over.forget S).op (yonedaGrp.map P.pair.B.inclusion) ≫ f.asIso.hom =
    borel.asIso.hom ≫ Functor.whiskerLeft (Over.forget S).op (yonedaGrp.map P.pair.B.inclusion)

/-- Equalities on arbitrary scheme-valued points test the scalar-extended character and
cocharacter actions. -/
def HasLatticeAction {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {S : SchemeOver k} {f : RelativeAut P.pair.G.val S}
    (a : Aligned P f) (d : Aut D.toBased) : Prop :=
  (∀ (χ : CharacterDescent.Character P.pair.T.group) (U : Over S)
    (t : U.left ⟶ P.pair.T.group.X),
    let χ' : CharacterDescent.Character P.pair.T.group :=
      Additive.toMul (d.asIso.hom.val.weightEquiv (Additive.ofMul χ))
    chrApply a.torus.asIso.inv U t ≫ χ.hom.hom = t ≫ χ'.hom.hom) ∧
  (∀ (c : CharacterDescent.Cocharacter P.pair.T.group) (U : Over S)
    (t : U.left ⟶ (specGroup (groupAlgebra k IntegerCharacters)).X),
    let c' : CharacterDescent.Cocharacter P.pair.T.group :=
      Additive.toMul (d.asIso.hom.val.coweightEquiv (Additive.ofMul c))
    chrApply a.torus.asIso.inv U (t ≫ c.hom.hom) = t ≫ c'.hom.hom)
where
  chrApply {H : GroupScheme k} {S : SchemeOver k}
      (b : relativePoints H S ⟶ relativePoints H S) (U : Over S) (t : U.left ⟶ H.X) :
      U.left ⟶ H.X := (b.app (op U)).hom t

/-- Based automorphisms and their unique pinned lifts over the field, with the
two lattice actions computed by the lifted isomorphism. -/
def PinnedLifts : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A),
    ∃ (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P),
      ∀ d : Aut D.toBased,
        let f : PinnedIso P P := (l d).asIso.hom
        (∀ χ : CharacterDescent.Character P.pair.T.group,
          d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
            Additive.ofMul (Pinning.transportCharacter f.torus χ)) ∧
        (∀ c : CharacterDescent.Cocharacter P.pair.T.group,
          d.asIso.hom.val.coweightEquiv (Additive.ofMul c) =
            Additive.ofMul (c ≫ f.torus.inv))


/-- Restrict the witnesses that an automorphism preserves the two subgroups. -/
def Aligned.restrict {A : AdditiveLine k} {P : PinnedGroup A} {S T : SchemeOver k}
    {f : RelativeAut P.pair.G.val S} (b : T ⟶ S) (a : Aligned P f) :
    Aligned P (restrictAut b f) where
  torus := restrictAut b a.torus
  borel := restrictAut b a.borel
  torus_comm := by
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun n => n.app ((Over.map b).op.obj U)) a.torus_comm) x
  borel_comm := by
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun n => n.app ((Over.map b).op.obj U)) a.borel_comm) x

/-- Forget the pinning, retaining its compatible maps on the group scheme. -/
def forgetPinning {A : AdditiveLine k} : PinnedGroup A ⥤ GroupScheme k where
  obj P := P.pair.G.val
  map f := f.group.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The torus in the adjoint group obtained as the image of the pinned torus.
The simple root characters factor through this image. -/
structure AdjointTorus {A : AdditiveLine k} (P : PinnedGroup A)
    (Q : AdjointQuotient P.pair.G) where
  subgroup : ClosedSubgroup Q.quotient.val
  projection : P.pair.T.group ⟶ subgroup.group
  fppf : IsFppf projection.hom.hom.left
  comm : projection ≫ subgroup.inclusion = P.pair.T.inclusion ≫ Q.projection
  character : (α : SimpleRoot P.pair) → CharacterDescent.Character subgroup.group
  pullsBack : ∀ α, projection ≫ character α = α.val.val
  simpleBasis : ∀ (S : SchemeOver k),
    Function.Bijective (fun t : S ⟶ subgroup.group.X =>
      fun α => t ≫ (character α).hom.hom)

/-- Scaling by the adjoint torus on a simple root is read on the corresponding
character. For an aligned automorphism inducing the identity of the datum, a
unique point of that torus gives the automorphism by conjugation on the whole group. -/
def CorrectsSimpleCoordinates {A : AdditiveLine k} {P : PinnedGroup A}
    {Q : AdjointQuotient P.pair.G}
    {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} (E : ExactSequence P.pair.G Q O)
    (T : AdjointTorus P Q) {S : SchemeOver k} (f : RelativeAut P.pair.G.val S) : Prop :=
  ∃! t : S ⟶ T.subgroup.group.X,
    f = E.inner.app (op S) ⟨t ≫ T.subgroup.inclusion.hom.hom⟩

/-- Every relative automorphism can be made to preserve the pinned Borel pair
by conjugation on an fppf covering sieve. -/
def alignmentSieve {A : AdditiveLine k} (P : PinnedGroup A) {S : SchemeOver k}
    (f : RelativeAut P.pair.G.val S) : Sieve S where
  arrows U b := ∃ g : U ⟶ P.pair.G.val.X, Nonempty (Aligned P (innerAut g * restrictAut b f))
  downward_closed := by
    rintro U V b ⟨g, ⟨a⟩⟩ v
    refine ⟨v ≫ g, ?_⟩
    have hc : restrictAut v (innerAut g) = innerAut (v ≫ g) := by
      apply Aut.ext
      apply Iso.ext
      apply NatTrans.ext
      funext W
      apply GrpCat.ext
      intro x
      change W.unop.left ⟶ P.pair.G.val.X at x
      change (W.unop.hom ≫ v ≫ g) * x * (W.unop.hom ≫ v ≫ g)⁻¹ =
        (W.unop.hom ≫ (v ≫ g)) * x * (W.unop.hom ≫ (v ≫ g))⁻¹
      rfl
    have hr : restrictAut v (restrictAut b f) = restrictAut (v ≫ b) f :=
      (ConcreteCategory.congr_hom ((automorphisms P.pair.G.val).map_comp b.op v.op) f).symm
    have h := a.restrict v
    rw [map_mul, hc, hr] at h
    exact ⟨h⟩

/-- The split automorphism sequence, for the fixed pinning and its actual
based datum. The section is specified on constant sections by field lifts. -/
structure SplitSequence {A : AdditiveLine k} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P)
    (Q : AdjointQuotient P.pair.G) extends
    ExactSequence P.pair.G Q (constantGroup (Aut D.toBased)) where
  outerRepresentation : ∃ H : GroupScheme k, H.X = constantScheme (Aut D.toBased) ∧
    Etale H.X.hom ∧ Nonempty (groupSections H ≅ constantGroup (Aut D.toBased))
  sectionMap : constantGroup (Aut D.toBased) ⟶ automorphisms P.pair.G.val
  rightInverse : sectionMap ≫ toExactSequence.outer = 𝟙 _
  sectionOnConstants : ∀ (S : SchemeOver k) (d : Aut D.toBased),
    sectionMap.app (op S) ⟨LocallyConstant.const _ d⟩ =
      scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S
  localAlignment : ∀ (S : SchemeOver k) (f : RelativeAut P.pair.G.val S),
    alignmentSieve P f ∈ schemeTopology k S
  latticeAction : ∀ (S : SchemeOver k) (f : RelativeAut P.pair.G.val S) (a : Aligned P f)
    (d : Aut D.toBased), toExactSequence.outer.app (op S) f = ⟨LocallyConstant.const _ d⟩ →
      HasLatticeAction D a d
  adjointTorus : AdjointTorus P Q
  correctsSimpleCoordinates : ∀ (S : SchemeOver k) (f : RelativeAut P.pair.G.val S),
    Nonempty (Aligned P f) → toExactSequence.outer.app (op S) f = 1 →
      CorrectsSimpleCoordinates toExactSequence adjointTorus f

/-- Restriction of a presheaf to the big slice site over a test scheme. -/
abbrev onSlice (S : SchemeOver k) (F : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}) :=
  (Over.forget S).op ⋙ F

/-- Identify the two automorphism sequences on a slice where the form is
trivialized. The three identifications compare the stated maps and act by
transport of automorphisms and of sections of the central quotient. -/
structure SequenceComparison {G H : AffineAlgebraicGroup k}
    {QG : AdjointQuotient G} {QH : AdjointQuotient H}
    {OG OH : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}
    (E : ExactSequence G QG OG) (F : ExactSequence H QH OH)
    {S : SchemeOver k} (i : relativePoints G.val S ≅ relativePoints H.val S) where
  adjointIso : onSlice S (groupSections QG.quotient.val) ≅ onSlice S (groupSections QH.quotient.val)
  outerIso : onSlice S OG ≅ onSlice S OH
  adjointOnLifts : ∀ (U : Over S) (g : U.left ⟶ G.val.X),
    adjointIso.hom.app (op U) ⟨g ≫ QG.projection.hom.hom⟩ =
      ⟨(i.hom.app (op U)).hom g ≫ QH.projection.hom.hom⟩
  innerComm : ∀ (U : Over S) (q : (groupSections QG.quotient.val).obj (op U.left)),
    Aut.autMulEquivOfIso (restrictIso U.hom i) (E.inner.app (op U.left) q) =
      F.inner.app (op U.left) (adjointIso.hom.app (op U) q)
  outerComm : ∀ (U : Over S) (f : RelativeAut G.val U.left),
    outerIso.hom.app (op U) (E.outer.app (op U.left) f) =
      F.outer.app (op U.left) (Aut.autMulEquivOfIso (restrictIso U.hom i) f)

/-- A separable form, specified with the same scalar extension of group
schemes used in the classification of forms. -/
def IsSeparableForm (G H : AffineAlgebraicGroup k) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : IsSepClosure k K),
    Nonempty ((groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val)

/-- The sequence for each form is the descent of the split sequence.
Comparison with any trivialization gives conjugation on automorphisms, and
determines the descent maps on the adjoint group and outer sheaf uniquely. -/
def Twists {G : AffineAlgebraicGroup k} {QG : AdjointQuotient G}
    {OG : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} (E : ExactSequence G QG OG) : Prop :=
  ∀ H : AffineAlgebraicGroup k, IsSeparableForm G H →
    ∃ (QH : AdjointQuotient H) (OH : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1})
      (F : ExactSequence H QH OH),
      (∃ (S : SchemeOver k), IsFppf S.hom ∧
        Nonempty (relativePoints G.val S ≅ relativePoints H.val S)) ∧
      ∀ (S : SchemeOver k) (i : relativePoints G.val S ≅ relativePoints H.val S),
        Nonempty (SequenceComparison E F i) ∧ Subsingleton (SequenceComparison E F i)

def Statement : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A),
    ∃ (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P)
      (Q : AdjointQuotient P.pair.G) (E : SplitSequence P D l Q),
      (∀ d : Aut D.toBased,
        let f : PinnedIso P P := (l d).asIso.hom
        (∀ χ : CharacterDescent.Character P.pair.T.group,
          d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
            Additive.ofMul (Pinning.transportCharacter f.torus χ)) ∧
        (∀ c : CharacterDescent.Cocharacter P.pair.T.group,
          d.asIso.hom.val.coweightEquiv (Additive.ofMul c) =
            Additive.ofMul (c ≫ f.torus.inv))) ∧
      Twists E.toExactSequence

end

end LinearAlgebraicGroups.Specs.AutomorphismSequence
