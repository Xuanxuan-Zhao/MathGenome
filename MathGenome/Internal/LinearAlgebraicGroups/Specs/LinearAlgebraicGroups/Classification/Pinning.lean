import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts
import Mathlib.CategoryTheory.Groupoid
import Mathlib.LinearAlgebra.RootSystem.Base

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Pinning

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (adjointWeightVectors)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open OrderedRootProducts (RootSubgroupFamily)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

variable {k : Type u} [Field k]

/-- The reductive group, split maximal torus, and Borel over the ground field. -/
structure SplitBorelPair (k : Type u) [Field k] where
  G : AffineAlgebraicGroup k
  reductive : IsReductive G
  T : ClosedSubgroup G.val
  split : IsSplitTorus T.group
  maximal : IsGeometricallyMaximal T
  B : ClosedSubgroup G.val
  borel : IsKBorel B
  containsTorus : IsSubgroupOf T B

/-- Simplicity in the positive system of the specified Borel. The character
lattice is written multiplicatively here. -/
def IsSimple (P : SplitBorelPair k) (α : Root P.T) : Prop :=
  α ∈ subgroupRoots P.T P.B ∧
    ∀ β ∈ subgroupRoots P.T P.B, ∀ δ ∈ subgroupRoots P.T P.B,
      α.val ≠ β.val * δ.val

abbrev SimpleRoot (P : SplitBorelPair k) := {α : Root P.T // IsSimple P α}

/-- An equivariant group-scheme coordinate on a specified root subgroup. -/
abbrev RootCoordinate {G : GroupScheme k} (A : AdditiveLine k) (T U : ClosedSubgroup G)
    (α : Character T.group) :=
  {x : A.group ≅ U.group // HasScalarAction T α (x.hom ≫ U.inclusion)}

/-- A pinning chooses one coordinate for each simple root. -/
def Pinning (A : AdditiveLine k) (P : SplitBorelPair k) (U : RootSubgroupFamily P.T) :=
  ∀ α : SimpleRoot P, RootCoordinate A P.T (U α.val).val α.val.val

def PinningType :=
  ∀ {k : Type u} [Field k], AdditiveLine k → (P : SplitBorelPair k) →
    RootSubgroupFamily P.T → Type u

/-- The equivalent choice of a nonzero vector in each simple root line. -/
abbrev RootVector {G : GroupScheme k} (T : ClosedSubgroup G) (α : Character T.group) :=
  {v : Lie k G // v ∈ adjointWeightVectors T α ∧ v ≠ 0}

def SimpleRootVectors (P : SplitBorelPair k) :=
  ∀ α : SimpleRoot P, RootVector P.T α.val.val

/-- Differentiation sends a coordinate to its value on the standard
infinitesimal parameter ε. Multiplying the parameter by a unit multiplies
the tangent vector by that same unit. -/
def CoordinateVectors : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k) (P : SplitBorelPair k)
    (α : Root P.T) (U : ClosedSubgroup P.G.val), IsRootSubgroup P.T U α.val →
    ∃ e : RootCoordinate A P.T U α.val ≃ RootVector P.T α.val,
      (∀ x, (e x).val.toMul.val =
        rootPoint (x.val.hom ≫ U.inclusion) (CommAlgCat.of k (DualNumber k)) DualNumber.eps) ∧
      (∀ (x : RootCoordinate A P.T U α.val) (c : kˣ),
        ∃! y : RootCoordinate A P.T U α.val,
          (∀ (R : TestAlgebra k) (a : R),
            rootPoint (y.val.hom ≫ U.inclusion) R a =
              rootPoint (x.val.hom ≫ U.inclusion) R (algebraMap k R (c : k) * a)) ∧
          (e y).val = scalePointKernel P.G.val (c : k) (e x).val)

/-- Two coordinates on the same root group differ by a unique scalar. -/
def CoordinateChanges : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (A : AdditiveLine k)
    (T U : ClosedSubgroup G) (α : Character T.group) (x y : RootCoordinate A T U α),
    ∃! c : kˣ, ∀ (R : TestAlgebra k) (a : R),
      rootPoint (y.val.hom ≫ U.inclusion) R a =
        rootPoint (x.val.hom ≫ U.inclusion) R (algebraMap k R (c : k) * a)

/-- Differentiation identifies pinnings with simple root vectors and
intertwines independently chosen unit scalings at the simple roots. -/
def PinningVectors : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k) (P : SplitBorelPair k)
    (U : RootSubgroupFamily P.T),
    ∃ e : Pinning A P U ≃ SimpleRootVectors P,
      (∀ x α, (e x α).val.toMul.val =
        rootPoint ((x α).val.hom ≫ (U α.val).val.inclusion)
          (CommAlgCat.of k (DualNumber k)) DualNumber.eps) ∧
      (∀ (x : Pinning A P U) (c : SimpleRoot P → kˣ),
        ∃! y : Pinning A P U,
          (∀ (α : SimpleRoot P) (R : TestAlgebra k) (a : R),
            rootPoint ((y α).val.hom ≫ (U α.val).val.inclusion) R a =
              rootPoint ((x α).val.hom ≫ (U α.val).val.inclusion) R
                (algebraMap k R (c α : k) * a)) ∧
          (∀ α, (e y α).val = scalePointKernel P.G.val (c α : k) (e x α).val))

/-- Every standard additive line can be used to pin any split Borel pair. -/
def PinningsExist : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k) (P : SplitBorelPair k),
    ∃ U : RootSubgroupFamily P.T, Nonempty (Pinning A P U)

/-- The standard additive line exists over every field. -/
def AdditiveLineExists : Prop :=
  ∀ (k : Type u) [Field k], Nonempty (AdditiveLine k)

/-- The pinning is extra structure on the split Borel pair. Root subgroups
are specified as ambient closed subgroups, which gives access to their
inclusion maps and their parametrizations. -/
structure PinnedGroup (A : AdditiveLine k) where
  pair : SplitBorelPair k
  roots : RootSubgroupFamily pair.T
  pin : Pinning A pair roots

/-- Transport of a character in the covariant direction of a torus isomorphism. -/
def transportCharacter {S T : GroupScheme k} (f : S ≅ T) (χ : Character S) : Character T :=
  f.inv ≫ χ

/-- The pinning records the character and its labelled map into the group. -/
def pinGraph {A : AdditiveLine k} (P : PinnedGroup A) :
    Set (Character P.pair.T.group × (A.group ⟶ P.pair.G.val)) :=
  Set.range fun α : SimpleRoot P.pair =>
    (α.val.val, (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion)

/-- Isomorphisms preserve the torus, the Borel, and all labelled coordinates. -/
@[ext]
structure PinnedIso {A : AdditiveLine k} (P Q : PinnedGroup A) where
  group : P.pair.G.val ≅ Q.pair.G.val
  torus : P.pair.T.group ≅ Q.pair.T.group
  borel : P.pair.B.group ≅ Q.pair.B.group
  torus_comm : P.pair.T.inclusion ≫ group.hom = torus.hom ≫ Q.pair.T.inclusion
  borel_comm : P.pair.B.inclusion ≫ group.hom = borel.hom ≫ Q.pair.B.inclusion
  pin_comm : (fun z => (transportCharacter torus z.1, z.2 ≫ group.hom)) '' pinGraph P =
    pinGraph Q

namespace PinnedIso

variable {A : AdditiveLine k} {P Q R : PinnedGroup A}

/-- The identity of a pinned group. -/
def refl (P : PinnedGroup A) : PinnedIso P P where
  group := Iso.refl _
  torus := Iso.refl _
  borel := Iso.refl _
  torus_comm := by simp
  borel_comm := by simp
  pin_comm := by simp [transportCharacter]

/-- Composition preserves the torus and Borel and transports the labels in order. -/
def trans (f : PinnedIso P Q) (g : PinnedIso Q R) : PinnedIso P R where
  group := f.group ≪≫ g.group
  torus := f.torus ≪≫ g.torus
  borel := f.borel ≪≫ g.borel
  torus_comm := by
    change _ ≫ (f.group.hom ≫ g.group.hom) =
      (f.torus.hom ≫ g.torus.hom) ≫ _
    rw [← Category.assoc, f.torus_comm, Category.assoc, g.torus_comm, Category.assoc]
  borel_comm := by
    change _ ≫ (f.group.hom ≫ g.group.hom) =
      (f.borel.hom ≫ g.borel.hom) ≫ _
    rw [← Category.assoc, f.borel_comm, Category.assoc, g.borel_comm, Category.assoc]
  pin_comm := by
    have h := congrArg (Set.image (fun z : Character Q.pair.T.group ×
      (A.group ⟶ Q.pair.G.val) => (transportCharacter g.torus z.1, z.2 ≫ g.group.hom)))
      f.pin_comm
    rw [Set.image_image, g.pin_comm] at h
    simpa only [Function.comp_apply, transportCharacter, Iso.trans_inv, Iso.trans_hom,
      Category.assoc] using h

/-- The inverse transports the same labelled coordinates in the other direction. -/
def symm (f : PinnedIso P Q) : PinnedIso Q P where
  group := f.group.symm
  torus := f.torus.symm
  borel := f.borel.symm
  torus_comm := by
    change _ ≫ f.group.inv = f.torus.inv ≫ _
    apply (cancel_mono f.group.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, f.torus_comm, Iso.inv_hom_id_assoc]
  borel_comm := by
    change _ ≫ f.group.inv = f.borel.inv ≫ _
    apply (cancel_mono f.group.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, f.borel_comm, Iso.inv_hom_id_assoc]
  pin_comm := by
    rw [← f.pin_comm, Set.image_image]
    simp [transportCharacter, Category.assoc]

end PinnedIso

/-- Split pinned connected reductive groups with pinning-preserving isomorphisms. -/
instance pinnedGroupoid (A : AdditiveLine k) : Groupoid (PinnedGroup A) where
  Hom := PinnedIso
  id := PinnedIso.refl
  comp := PinnedIso.trans
  inv := PinnedIso.symm
  id_comp _ := by apply PinnedIso.ext <;> apply Iso.ext <;> simp [PinnedIso.refl, PinnedIso.trans]
  comp_id _ := by apply PinnedIso.ext <;> apply Iso.ext <;> simp [PinnedIso.refl, PinnedIso.trans]
  assoc _ _ _ := by apply PinnedIso.ext <;> apply Iso.ext <;> simp [PinnedIso.trans]
  inv_comp _ := by
    apply PinnedIso.ext <;> apply Iso.ext <;> simp [PinnedIso.refl, PinnedIso.trans, PinnedIso.symm]
  comp_inv _ := by
    apply PinnedIso.ext <;> apply Iso.ext <;> simp [PinnedIso.refl, PinnedIso.trans, PinnedIso.symm]

/-- A finite based reduced integral root datum. The two lattices retain
their full ranks even if the root set is empty or does not span them. -/
structure BasedRootDatum where
  I : Type u
  X : Type u
  Y : Type u
  [addX : AddCommGroup X]
  [addY : AddCommGroup Y]
  finiteRoots : Finite I
  freeX : Module.Free ℤ X
  freeY : Module.Free ℤ Y
  finiteX : Module.Finite ℤ X
  finiteY : Module.Finite ℤ Y
  datum : RootDatum I X Y
  reduced : datum.IsReduced
  base : datum.Base

attribute [instance] BasedRootDatum.addX BasedRootDatum.addY

/-- Both lattices, the paired root and coroot indices, and the specified
base are preserved by an isomorphism. -/
abbrev BasedIso (P Q : BasedRootDatum.{u}) :=
  {e : P.datum.Equiv Q.datum // e.indexEquiv '' (P.base.support : Set P.I) = Q.base.support}

/-- The groupoid of finite based reduced root data and based isomorphisms. -/
instance basedRootDatumGroupoid : Groupoid.{u} BasedRootDatum.{u} where
  Hom := BasedIso
  id P := ⟨RootPairing.Equiv.id P.datum, by simp⟩
  comp f g := ⟨g.val.comp f.val, by
    change (g.val.indexEquiv ∘ f.val.indexEquiv) '' _ = _
    calc
      _ = g.val.indexEquiv '' (f.val.indexEquiv '' _) := (Set.image_image _ _ _).symm
      _ = _ := by rw [f.property, g.property]⟩
  inv f := ⟨f.val.symm _ _, by
    change f.val.indexEquiv.symm '' _ = _
    calc
      _ = f.val.indexEquiv.symm '' (f.val.indexEquiv '' _) :=
        congrArg (Set.image f.val.indexEquiv.symm) f.property.symm
      _ = _ := by rw [Set.image_image]; simp⟩
  id_comp _ := by apply Subtype.ext; exact RootPairing.Equiv.id_comp _ _ _
  comp_id _ := by apply Subtype.ext; exact RootPairing.Equiv.comp_id _ _ _
  assoc _ _ _ := by apply Subtype.ext; exact (RootPairing.Equiv.comp_assoc _ _ _).symm
  inv_comp f := by
    apply Subtype.ext
    apply RootPairing.Equiv.ext
    · ext x
      exact f.val.weightEquiv.apply_symm_apply x
    · ext x
      exact f.val.coweightEquiv.symm_apply_apply x
    · ext x
      exact f.val.indexEquiv.apply_symm_apply x
  comp_inv f := by
    apply Subtype.ext
    apply RootPairing.Equiv.ext
    · ext x
      exact f.val.weightEquiv.symm_apply_apply x
    · ext x
      exact f.val.coweightEquiv.apply_symm_apply x
    · ext x
      exact f.val.indexEquiv.symm_apply_apply x

def PinnedGroupoidType :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k), Groupoid.{u} (PinnedGroup A)

def BasedRootDatumGroupoidType := Groupoid.{u} BasedRootDatum.{u}

/-- A presentation of the actual based datum of a split Borel pair. -/
structure AttachedDatum (P : SplitBorelPair k) where
  comm : IsCommMonObj P.T.group.X
  datum : @Datum _ _ P.G P.T comm
  base : datum.rootDatum.Base
  simple_iff : ∀ α, α ∈ base.support ↔ IsSimple P α

/-- Forget the presentation, keeping the two actual lattices and the base. -/
def AttachedDatum.toBased {P : SplitBorelPair k} (D : AttachedDatum P) : BasedRootDatum.{u} :=
  letI := D.comm
  { I := Root P.T
    X := Additive (Character P.T.group)
    Y := Additive (Cocharacter P.T.group)
    finiteRoots := D.datum.finiteRoots
    freeX := D.datum.freeCharacters
    freeY := D.datum.freeCocharacters
    finiteX := D.datum.finiteCharacters
    finiteY := D.datum.finiteCocharacters
    datum := D.datum.rootDatum
    reduced := D.datum.reduced
    base := D.base }

def DatumExists : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k), Nonempty (AttachedDatum P)

/-- The groupoid functor uses the actual datum of each pair and the inverse
pullback on its character lattice. The transpose, roots, coroots, and bases
are then part of its maps in the based root datum groupoid. -/
def BasedDatumFunctorExists : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k),
    ∃ (D : ∀ P : PinnedGroup A, AttachedDatum P.pair)
      (F : PinnedGroup A ⥤ BasedRootDatum.{u}),
      ∃ hObj : ∀ P, F.obj P = (D P).toBased,
        ∀ (P Q : PinnedGroup A) (f : P ⟶ Q),
          let e : BasedIso (D P).toBased (D Q).toBased :=
            (hObj P) ▸ (hObj Q) ▸ F.map f
          (∀ χ : Character P.pair.T.group, e.val.weightEquiv (Additive.ofMul χ) =
            Additive.ofMul (transportCharacter f.torus χ)) ∧
          (∀ c : Cocharacter Q.pair.T.group, e.val.coweightEquiv (Additive.ofMul c) =
            Additive.ofMul (c ≫ f.torus.inv))

end

end LinearAlgebraicGroups.Specs.Pinning
