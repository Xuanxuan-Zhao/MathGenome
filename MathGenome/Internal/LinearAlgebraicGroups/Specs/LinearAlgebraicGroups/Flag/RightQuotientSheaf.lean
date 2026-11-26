import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.GroupTheory.Coset.Basic

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]

/-- The big fppf site of schemes over the field. -/
abbrev fppfOver (k : Type u) [Field k] : GrothendieckTopology (SchemeOver k) :=
  Scheme.fppfTopology.over (Spec (CommRingCat.of k))

/-- The representable sheaf, lifted to the universe used by big-site sheafification. -/
abbrev schemeFppfSheaf (X : SchemeOver k) : Sheaf (fppfOver k) (Type (u + 1)) :=
  (fppfOver k).uliftYoneda.{u + 1, u, u + 1}.obj X

abbrev SubgroupSections {G : GroupScheme k} (H : ClosedSubgroup G) (T : SchemeOver k) :
    Subgroup (T ⟶ G.X) :=
  (((yonedaGrp.map H.inclusion).app (op T)).hom).range

/-- The quotient type records the cosets `gH(T)` for the right action of `H(T)`. -/
abbrev RightCosets {G : GroupScheme k} (H : ClosedSubgroup G) (T : SchemeOver k) :=
  (T ⟶ G.X) ⧸ SubgroupSections H T

/-- Image of a coset under a group homomorphism carrying one subgroup into the other. -/
def mapCosets {A B : Type u} [Group A] [Group B] {S : Subgroup A} {U : Subgroup B}
    (f : A →* B) (hf : S ≤ U.comap f) : A ⧸ S → B ⧸ U :=
  Quotient.map f (fun {a b} h ↦
    QuotientGroup.leftRel_apply.mpr (by
      rw [← map_inv, ← map_mul]
      exact hf (QuotientGroup.leftRel_apply.mp h)))

/-- Cosets on the big site. At `testSpec.obj (op R)` these are the cosets on `R`-points. -/
def rightCosetPresheaf {G : GroupScheme k} (H : ClosedSubgroup G) :
    (SchemeOver k)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ULift.{u + 1} (RightCosets H T.unop)
  map {T U} f := ↾fun x ↦ ⟨mapCosets ((yonedaGrp.obj G).map f).hom
    (by
      rintro _ ⟨h, rfl⟩
      refine ⟨f.unop ≫ h, ?_⟩
      change (f.unop ≫ h) ≫ H.inclusion.hom.hom = f.unop ≫ h ≫ H.inclusion.hom.hom
      exact Category.assoc _ _ _) x.down⟩
  map_id T := by
    ext ⟨x⟩
    induction x using QuotientGroup.induction_on with
    | H g => change QuotientGroup.mk (s := SubgroupSections H T.unop) ((𝟙 T).unop ≫ g) = QuotientGroup.mk g
             simp
  map_comp f g := by
    ext ⟨x⟩
    induction x using QuotientGroup.induction_on with
    | H a => change QuotientGroup.mk (s := SubgroupSections H _) ((f ≫ g).unop ≫ a) =
                QuotientGroup.mk (g.unop ≫ f.unop ≫ a)
             simp

/-- The pointwise projection before sheafification. -/
def rightCosetProjection {G : GroupScheme k} (H : ClosedSubgroup G) :
    (schemeFppfSheaf G.X).obj ⟶ rightCosetPresheaf H where
  app _ := ↾fun g ↦ ⟨QuotientGroup.mk g.down⟩

/-- The fppf sheaf associated to the presheaf of cosets. -/
def rightQuotientSheaf {G : GroupScheme k} (H : ClosedSubgroup G) :
    Sheaf (fppfOver k) (Type (u + 1)) :=
  (presheafToSheaf (fppfOver k) _).obj (rightCosetPresheaf H)

/-- The quotient projection as a morphism of fppf sheaves. -/
def rightQuotientProjection {G : GroupScheme k} (H : ClosedSubgroup G) :
    schemeFppfSheaf G.X ⟶ rightQuotientSheaf H :=
  ⟨rightCosetProjection H ≫ toSheafify (fppfOver k) (rightCosetPresheaf H)⟩

abbrev projectSection {G : GroupScheme k} (H : ClosedSubgroup G) {T : SchemeOver k}
    (g : T ⟶ G.X) : (rightQuotientSheaf H).obj.obj (op T) :=
  (rightQuotientProjection H).hom.app (op T) ⟨g⟩

/-- The constant singleton sheaf. -/
abbrev pointFppfSheaf (k : Type u) [Field k] : Sheaf (fppfOver k) (Type (u + 1)) :=
  ⟨(Functor.const _).obj PUnit, Presheaf.isSheaf_of_isTerminal _ Limits.Types.isTerminalPUnit⟩

/-- The identity coset defines the distinguished section. -/
def rightQuotientBasePoint {G : GroupScheme k} (H : ClosedSubgroup G) :
    pointFppfSheaf k ⟶ rightQuotientSheaf H where
  hom :=
    { app := fun _ ↦ ↾fun _ ↦ projectSection H 1
      naturality := fun X Y f ↦ by
        ext
        let e : ULift.{u + 1} (X.unop ⟶ G.X) := ⟨1⟩
        have h := (rightQuotientProjection H).hom.naturality_apply f e
        exact (h.symm.trans (by
          change projectSection H (f.unop ≫ 1) = projectSection H 1
          rw [MonObj.comp_one])).symm }

/-- A compatible pair of group-scheme morphisms acts on the coset presheaves. -/
def rightCosetMap {G G' : GroupScheme k} {H : ClosedSubgroup G} {H' : ClosedSubgroup G'}
    (f : G ⟶ G') (h : H.group ⟶ H'.group)
    (comm : H.inclusion ≫ f = h ≫ H'.inclusion) :
    rightCosetPresheaf H ⟶ rightCosetPresheaf H' where
  app T := ↾fun x ↦ ⟨mapCosets ((yonedaGrp.map f).app T).hom
    (by
      rintro _ ⟨a, rfl⟩
      change (T.unop ⟶ H.group.X) at a
      refine ⟨a ≫ h.hom.hom, ?_⟩
      change (a ≫ h.hom.hom) ≫ H'.inclusion.hom.hom =
        (a ≫ H.inclusion.hom.hom) ≫ f.hom.hom
      have e := congrArg (fun p : H.group ⟶ G' ↦ p.hom.hom) comm.symm
      change h.hom.hom ≫ H'.inclusion.hom.hom = H.inclusion.hom.hom ≫ f.hom.hom at e
      rw [Category.assoc, Category.assoc, e]) x.down⟩
  naturality T U b := by
    ext ⟨x⟩
    induction x using QuotientGroup.induction_on with
    | H a => change ULift.up (QuotientGroup.mk (s := SubgroupSections H' _)
                  ((b.unop ≫ a) ≫ f.hom.hom)) =
                ULift.up (QuotientGroup.mk (b.unop ≫ a ≫ f.hom.hom))
             rw [Category.assoc]

/-- The induced map of quotient sheaves. Taking `f` to be the identity covers subgroup
inclusions in a fixed ambient group. -/
def rightQuotientMap {G G' : GroupScheme k} {H : ClosedSubgroup G} {H' : ClosedSubgroup G'}
    (f : G ⟶ G') (h : H.group ⟶ H'.group)
    (comm : H.inclusion ≫ f = h ≫ H'.inclusion) :
    rightQuotientSheaf H ⟶ rightQuotientSheaf H' :=
  (presheafToSheaf (fppfOver k) _).map (rightCosetMap f h comm)

/-- Left translation of a coset by a point of the ambient group. -/
def translateCoset {G : GroupScheme k} {H : ClosedSubgroup G} {T : SchemeOver k}
    (g : T ⟶ G.X) : RightCosets H T → RightCosets H T :=
  Quotient.map (g * ·) (fun {a b} h ↦ QuotientGroup.leftRel_apply.mpr (by
    simpa [mul_assoc] using QuotientGroup.leftRel_apply.mp h))

/-- Left translation on the presheaf of cosets. -/
def rightCosetAction {G : GroupScheme k} (H : ClosedSubgroup G) :
    (schemeFppfSheaf G.X).obj ⊗ rightCosetPresheaf H ⟶ rightCosetPresheaf H where
  app T := ↾fun p ↦ ⟨translateCoset (H := H) (T := T.unop) p.1.down p.2.down⟩
  naturality T U f := by
    ext ⟨⟨g⟩, ⟨x⟩⟩
    induction x using QuotientGroup.induction_on with
    | H a =>
      let g' : T.unop ⟶ G.X := g
      change ULift.up (QuotientGroup.mk (s := SubgroupSections H _) ((f.unop ≫ g') * (f.unop ≫ a))) =
        ULift.up (QuotientGroup.mk (f.unop ≫ (g' * a)))
      rw [MonObj.comp_mul]

/-- Sheafification preserves binary products, which extends left translation to the quotient. -/
def rightQuotientAction {G : GroupScheme k} (H : ClosedSubgroup G) :
    (schemeFppfSheaf G.X).obj ⊗ (rightQuotientSheaf H).obj ⟶ (rightQuotientSheaf H).obj :=
  let J := fppfOver k
  let A := schemeFppfSheaf G.X
  let C := rightCosetPresheaf H
  lift (fst _ _ ≫ toSheafify J A.obj) (snd _ _) ≫
    (prodComparisonIso (sheafification J _) A.obj C).inv ≫
    sheafifyMap J (rightCosetAction H)

abbrev actOnSection {G : GroupScheme k} (H : ClosedSubgroup G) {T : SchemeOver k}
    (g : T ⟶ G.X) (x : (rightQuotientSheaf H).obj.obj (op T)) :
    (rightQuotientSheaf H).obj.obj (op T) :=
  (rightQuotientAction H).app (op T) (ULift.up g, x)

abbrev RightCosetPresheafType :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k}, ClosedSubgroup G →
    (SchemeOver k)ᵒᵖ ⥤ Type (u + 1)

abbrev RightQuotientSheafType :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k}, ClosedSubgroup G →
    Sheaf (fppfOver k) (Type (u + 1))

abbrev RightQuotientProjectionType :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G),
    schemeFppfSheaf G.X ⟶ rightQuotientSheaf H

abbrev RightQuotientBasePointType :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G),
    pointFppfSheaf k ⟶ rightQuotientSheaf H

abbrev RightQuotientMapType :=
  ∀ {k : Type u} [Field k] {G G' : GroupScheme k}
    {H : ClosedSubgroup G} {H' : ClosedSubgroup G'}
    (f : G ⟶ G') (h : H.group ⟶ H'.group),
    H.inclusion ≫ f = h ≫ H'.inclusion → (rightQuotientSheaf H ⟶ rightQuotientSheaf H')

abbrev RightQuotientActionType :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G),
    (schemeFppfSheaf G.X).obj ⊗ (rightQuotientSheaf H).obj ⟶ (rightQuotientSheaf H).obj

/-- Every section of the quotient has fppf local lifts to the ambient group. -/
def RightQuotientLocalLifts : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G),
    Presheaf.IsLocallySurjective (fppfOver k) (rightQuotientProjection H).hom

/-- Membership in the subgroup descends from any covering sieve. -/
def SubgroupMembershipDescent : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G)
    {T : SchemeOver k} (g : T ⟶ G.X) (S : Sieve T), S ∈ fppfOver k T →
    (∀ ⦃U : SchemeOver k⦄ (f : U ⟶ T), S f → f ≫ g ∈ SubgroupSections H U) →
    g ∈ SubgroupSections H T

/-- Two sections of the ambient group have the same image exactly when their difference
factors through the given subgroup scheme. -/
def RightQuotientProjectionEquality : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G)
    {T : SchemeOver k} (g g' : T ⟶ G.X),
    projectSection H g = projectSection H g' ↔
      ∃ h : T ⟶ H.group.X, h ≫ H.inclusion.hom.hom = g⁻¹ * g'

def RightQuotientActionOnLifts : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G)
    {T : SchemeOver k} (a b : T ⟶ G.X),
    actOnSection H a (projectSection H b) = projectSection H (a * b)

def RightQuotientActionLaws : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G)
    {T : SchemeOver k} (x : (rightQuotientSheaf H).obj.obj (op T)),
    actOnSection H 1 x = x ∧
      ∀ a b : T ⟶ G.X, actOnSection H (a * b) x = actOnSection H a (actOnSection H b x)

def RightQuotientMapOnLifts : Prop :=
  ∀ {k : Type u} [Field k] {G G' : GroupScheme k}
    {H : ClosedSubgroup G} {H' : ClosedSubgroup G'}
    (f : G ⟶ G') (h : H.group ⟶ H'.group) (comm : H.inclusion ≫ f = h ≫ H'.inclusion)
    {T : SchemeOver k} (g : T ⟶ G.X),
    (rightQuotientMap f h comm).hom.app (op T) (projectSection H g) =
      projectSection H' (g ≫ f.hom.hom)

/-- Restricting the big-site quotient to spectra of test algebras gives the
sheafification of the affine coset presheaf, with the same unit map. -/
def AffineRightQuotientComparison : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G),
    let F := testSpec k
    let J := fppfOver k
    let K := F.inducedTopology J
    let P := rightCosetPresheaf H
    ∃ e : sheafify K (F.op ⋙ P) ≅ F.op ⋙ (rightQuotientSheaf H).obj,
      toSheafify K (F.op ⋙ P) ≫ e.hom = F.op.whiskerLeft (toSheafify J P)

/-- Sections over an affine test scheme admit lifts on a covering sieve of affine test schemes. -/
def AffineRightQuotientLocalLifts : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (H : ClosedSubgroup G),
    let F := testSpec k
    Presheaf.IsLocallySurjective (F.inducedTopology (fppfOver k))
      (F.op.whiskerLeft (rightQuotientProjection H).hom)

end

end LinearAlgebraicGroups.Specs
