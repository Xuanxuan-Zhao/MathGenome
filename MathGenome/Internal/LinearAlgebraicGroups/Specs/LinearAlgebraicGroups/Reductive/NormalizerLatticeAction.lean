import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.LocallyConstant.Algebra

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.NormalizerLatticeAction

open CharacterDescent (Character)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open GeometricBorelConjugacy (IsBorel)
open GeometricRadicals (IsMaximalTorus IsSplitTorus IsTorus)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)

noncomputable section

variable {k : Type u} [Field k]

/-- The characters along a weight basis for the restriction of a faithful representation.
The diagonal matrix equation tests the restriction on every commutative test algebra. -/
def FaithfulWeights {G S : GroupScheme k} (i : S ⟶ G) (weights : Set (Character S)) : Prop :=
  ∃ (n : ℕ) (L : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj L.val ≅
      StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (m : (groupPointsFunctor k).obj (specGroup (groupAlgebra k IntegerCharacters)) ≅
      StandardGroups.multiplicativePoints k)
    (f : G ⟶ L.val) (χ : ULift.{u} (Fin n) → Character S),
    IsClosedImmersion f.hom.hom.left ∧ Set.range χ = weights ∧
    Subgroup.closure weights = ⊤ ∧
    ∀ (R : TestAlgebra k) (t : Points S.X R),
      (e.hom.app R (t ≫ (i ≫ f).hom.hom) : Matrix.GeneralLinearGroup _ R).val =
        Matrix.diagonal (fun a ↦
          (m.hom.app R (t ≫ (χ a).hom.hom) : Rˣ).val)

/-- A constant group scheme has locally constant point families with values in its
label group, naturally on schemes over the field. The distinguished sections
correspond to the constant families. -/
structure ConstantGroup (Q : GroupScheme k) (W : Type u) [Group W] where
  sectionPoint : W →* (𝟙_ (SchemeOver k) ⟶ Q.X)
  families : ∀ Y : SchemeOver k, (Y ⟶ Q.X) ≃* LocallyConstant Y.left W
  naturality : ∀ {X Y : SchemeOver k} (f : X ⟶ Y) (y : Y ⟶ Q.X),
    families X (f ≫ y) = LocallyConstant.comap ⟨f.left, f.left.continuous⟩ (families Y y)
  constant : ∀ (Y : SchemeOver k) (w : W),
    families Y (toUnit Y ≫ sectionPoint w) = LocallyConstant.const Y.left w

/-- Over a splitting field the quotient is constant and its labels are a finite
subgroup of the automorphisms of the character lattice. Each label determines
conjugation on the entire corresponding family, including over nonreduced bases.
The action on characters is pullback by inverse conjugation, a left action. -/
structure SplitImage {G S N Q : GroupScheme k}
    (i : S ⟶ G) (v : N ⟶ G) (q : N ⟶ Q) where
  labels : Subgroup (MulAut (Character S))
  finite : Finite labels
  constantGroup : ConstantGroup Q labels
  weights : Set (Character S)
  faithfulWeights : FaithfulWeights i weights
  permutesWeights : ∀ w : labels, Set.MapsTo (w.val : Character S → Character S) weights weights
  conjugation : labels → (S ≅ S)
  characterAction : ∀ (w : labels) (χ : Character S), w.val χ = (conjugation w).inv ≫ χ
  conjugates : ∀ (Y : SchemeOver k) (n : Y ⟶ N.X) (w : labels),
    n ≫ q.hom.hom = toUnit Y ≫ constantGroup.sectionPoint w →
    conjugateFamily i (n ≫ v.hom.hom) = fst S.X Y ≫ ((conjugation w).hom ≫ i).hom.hom

/-- In each geometric fibre, left translation by a representative identifies
the centralizer with the fibre as a scheme. -/
def GeometricFibres {C N Q : GroupScheme k} (j : C ⟶ N) (q : N ⟶ Q) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    let F := groupBaseChange k K
    let C' := F.obj C
    let N' := F.obj N
    let Q' := F.obj Q
    let q' := (F.map q).hom.hom
    ∀ w : 𝟙_ (SchemeOver K) ⟶ Q'.X,
      ∃ n : 𝟙_ (SchemeOver K) ⟶ N'.X, n ≫ q' = w ∧
        IsPullback ((toUnit C'.X ≫ n) * (F.map j).hom.hom) (toUnit C'.X) q' w

/-- The conjugation action of the normalizer has scheme kernel the centralizer.
Its image represents the right fppf quotient and is finite étale. Its
description by the character lattice applies over every splitting field. -/
def QuotientByCentralizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ S : ClosedSubgroup G.val, IsTorus S.group →
    ∃ (N C : ClosedSubgroup G.val)
      (j : C.group ⟶ N.group) (hj : IsClosedImmersion j.hom.hom.left)
      (Q : AffineAlgebraicGroup k) (q : N.group ⟶ Q.val),
      RepresentsSubgroup N (fun _ g ↦ Normalizes S.inclusion g) ∧
      RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g) ∧
      j ≫ N.inclusion = C.inclusion ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) ⟨_, j, hj⟩ q ∧
      IsFinite Q.val.X.hom ∧ Etale Q.val.X.hom ∧
      GeometricFibres j q ∧
      (IsSplitTorus S.group → Nonempty (SplitImage S.inclusion N.inclusion q)) ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        let F := groupBaseChange k K
        IsSplitTorus (F.obj S.group) →
          Nonempty (SplitImage (F.map S.inclusion) (F.map N.inclusion) (F.map q))

/-- A geometric point is fixed if the entire orbit map of the torus is constant. -/
def IsFixedPoint {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (T : ClosedSubgroup G) (x : 𝟙_ (SchemeOver k) ⟶ X) : Prop :=
  lift T.inclusion.hom.hom (toUnit T.group.X ≫ x) ≫ a.smul = toUnit T.group.X ≫ x

/-- For a Borel containing a maximal torus, the geometric fixed points of the
right quotient are finite and are exactly the images of normalizer points.
Two such representatives have the same image precisely when they differ
on the right by a point of the centralizer. The left normalizer action is
transitive on the fixed points. -/
def BorelQuotientFixedPoints : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ (T B : ClosedSubgroup G.val), IsMaximalTorus T → IsBorel B → IsSubgroupOf T B →
    ∀ (N : ClosedSubgroup G.val),
      RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g) →
    ∀ P : QuotientEmbedding.Presentation B,
    ∃ a : ModObj G.val.X P.scheme,
      lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ P.projection) ≫ a.smul =
        μ[G.val.X] ≫ P.projection ∧
      Set.Finite {x : 𝟙_ (SchemeOver k) ⟶ P.scheme | IsFixedPoint a T x} ∧
      (∀ x : 𝟙_ (SchemeOver k) ⟶ P.scheme,
        IsFixedPoint a T x ↔
          ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X, n ≫ N.inclusion.hom.hom ≫ P.projection = x) ∧
      (∀ n₁ n₂ : 𝟙_ (SchemeOver k) ⟶ N.group.X,
        (n₁ ≫ N.inclusion.hom.hom ≫ P.projection =
          n₂ ≫ N.inclusion.hom.hom ≫ P.projection) ↔
          Centralizes T.inclusion ((n₂⁻¹ * n₁) ≫ N.inclusion.hom.hom)) ∧
      ∀ x y : 𝟙_ (SchemeOver k) ⟶ P.scheme,
        IsFixedPoint a T x → IsFixedPoint a T y →
        ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X,
          lift (n ≫ N.inclusion.hom.hom) x ≫ a.smul = y

/-- A normal torus in a smooth connected affine algebraic group is central
as a subgroup scheme. -/
def NormalTorusCentral : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T : ClosedSubgroup G.val, IsTorus T.group → IsNormalSubgroup T.inclusion →
      ∀ (Y : SchemeOver k) (g : Y ⟶ G.val.X), Centralizes T.inclusion g

end

end LinearAlgebraicGroups.Specs.NormalizerLatticeAction
