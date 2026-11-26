import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Mathlib.LinearAlgebra.RootSystem.Base

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.CellHomomorphism

open AbstractPairing (Datum Root)
open AdjointRepresentation (GroupPoints)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open OrderedRootProducts (Enumerates RootSubgroupFamily product rootCellMap)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine CorootReflection HasScalarAction rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

variable {k : Type u} [Field k]

/-- The root coordinates identify the standard additive line with the actual root
subgroups. The coordinates at the simple roots are the pinning. -/
structure Coordinates {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (D : Datum T) (A : AdditiveLine k) where
  groups : RootSubgroupFamily T
  parametrization : ∀ α, A.group ≅ (groups α).val.group
  scalarAction : ∀ α, HasScalarAction T α.val ((parametrization α).hom ≫ (groups α).val.inclusion)
  opposite : Root T → Root T
  opposite_eq : ∀ α, (opposite α).val = α.val⁻¹
  reflection : ∀ α,
    CorootReflection T α.val ((parametrization α).hom ≫ (groups α).val.inclusion)
      ((parametrization (opposite α)).hom ≫ (groups (opposite α)).val.inclusion)
  coroot_eq : ∀ α, (reflection α).coroot = Additive.toMul (D.rootDatum.coroot α)

abbrev Coordinates.root {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} {A : AdditiveLine k}
    (X : Coordinates D A) (α : Root T) : A.group ⟶ G.val :=
  (X.parametrization α).hom ≫ (X.groups α).val.inclusion

/-- Pullback on the actual character lattices. -/
def pullbackCharacters {T S : GroupScheme k} (τ : T ⟶ S) : Character S →* Character T where
  toFun χ := τ ≫ χ
  map_one' := by simp
  map_mul' χ ψ := by
    apply Grp.hom_ext
    exact MonObj.comp_mul τ.hom.hom χ.hom.hom ψ.hom.hom

/-- A correction in the signed commutator relation at the root
`α ^ i * β ^ j`. Both exponents are strictly positive. -/
structure CommutatorTerm {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (α β : Root T) where
  root : Root T
  i : ℕ
  j : ℕ
  i_pos : 0 < i
  j_pos : 0 < j
  root_eq : root.val = α.val ^ i * β.val ^ j
  coefficient : k

variable {G H : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} {S : ClosedSubgroup H.val}
    [IsCommMonObj T.group.X] [IsCommMonObj S.group.X]
    {D : Datum T} {E : Datum S} {A : AdditiveLine k}

/-- For every ordered pair of distinct, nonopposite roots, the two commutator
words have the same ordered terms and coefficients. Roots of either sign are
included here. Linked opposite coordinates are covered by the coroot words. -/
def SameSignedCommutators (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) : Prop :=
  ∀ α β, α ≠ β → β.val ≠ α.val⁻¹ →
    ∃ L : List (CommutatorTerm α β),
      ∀ (R : TestAlgebra k) (x y : R),
        let a := rootPoint (X.root α) R x
        let b := rootPoint (X.root β) R y
        let a' := rootPoint (Y.root (d α)) R x
        let b' := rootPoint (Y.root (d β)) R y
        (a * b * a⁻¹ * b⁻¹ =
          (L.map fun t ↦ rootPoint (X.root t.root) R
            (algebraMap k R t.coefficient * x ^ t.i * y ^ t.j)).prod) ∧
        (a' * b' * a'⁻¹ * b'⁻¹ =
          (L.map fun t ↦ rootPoint (Y.root (d t.root)) R
            (algebraMap k R t.coefficient * x ^ t.i * y ^ t.j)).prod)

/-- Translate the product of corresponding root factors in list order. -/
def rootFactorsIso (X : Coordinates D A) (Y : Coordinates E A) (d : Root T ≃ Root S) :
    (l : List (Root T)) →
      product (fun α ↦ (X.groups α).val.group.X) l ≅
        product (fun β ↦ (Y.groups β).val.group.X) (l.map d)
  | [] => Iso.refl _
  | α :: l =>
    (Grp.forget (SchemeOver k)).mapIso
        ((X.parametrization α).symm ≪≫ Y.parametrization (d α)) ⊗ᵢ
      rootFactorsIso X Y d l

/-- The prescribed map in the open coordinates, including the original torus
morphism. The two lists are the orders for the negative and positive roots. -/
def cellCoordinatesMap (X : Coordinates D A) (Y : Coordinates E A) (d : Root T ≃ Root S)
    (τ : T.group ⟶ S.group) (negative positive : List (Root T)) :
    (product (fun α ↦ (X.groups α).val.group.X) negative ⊗
      (T.group.X ⊗ product (fun α ↦ (X.groups α).val.group.X) positive)) ⟶
      (product (fun β ↦ (Y.groups β).val.group.X) (negative.map d) ⊗
        (S.group.X ⊗ product (fun β ↦ (Y.groups β).val.group.X) (positive.map d))) :=
  (rootFactorsIso X Y d negative).hom ⊗ₘ
    (τ.hom.hom ⊗ₘ (rootFactorsIso X Y d positive).hom)

/-- The required restrictions as scheme morphisms, including the prescribed
coordinates on all simple pinned factors. -/
def Matches (X : Coordinates D A) (Y : Coordinates E A)
    (d : Root T ≃ Root S) (τ : T.group ⟶ S.group) (f : G.val ⟶ H.val) : Prop :=
  T.inclusion ≫ f = τ ≫ S.inclusion ∧
    ∀ α, X.root α ≫ f = Y.root (d α)

/-- A finite-index based torus map with compatible coroots and signed commutator
relations extends uniquely over the group. The kernel represents the same
scheme functor as the finite torus kernel. All field characteristics are allowed. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k), IsReductive G → IsReductive H →
    ∀ (T : ClosedSubgroup G.val) (S : ClosedSubgroup H.val),
      IsSplitTorus T.group → IsSplitTorus S.group →
      IsGeometricallyMaximal T → IsGeometricallyMaximal S →
    ∀ (B : ClosedSubgroup G.val) (C : ClosedSubgroup H.val),
      IsKBorel B → IsKBorel C → IsSubgroupOf T B → IsSubgroupOf S C →
    ∀ (hT : IsCommMonObj T.group.X) (hS : IsCommMonObj S.group.X),
      letI := hT
      letI := hS
      ∀ (D : Datum T) (E : Datum S) (b : D.rootDatum.Base) (c : E.rootDatum.Base),
        (∀ α, b.IsPos α ↔ α ∈ subgroupRoots T B) →
        (∀ β, c.IsPos β ↔ β ∈ subgroupRoots S C) →
      ∀ (A : AdditiveLine k) (X : Coordinates D A) (Y : Coordinates E A)
        (d : Root T ≃ Root S) (τ : T.group ⟶ S.group),
        Function.Injective (pullbackCharacters τ) →
        Finite (Character T.group ⧸ (pullbackCharacters τ).range) →
        (∀ α, τ ≫ (d α).val = α.val) →
        (∀ α, Additive.toMul (D.rootDatum.coroot α) ≫ τ =
          Additive.toMul (E.rootDatum.coroot (d α))) →
        (∀ α, b.IsPos α ↔ c.IsPos (d α)) →
        (∀ α, α ∈ b.support ↔ d α ∈ c.support) →
        SameSignedCommutators X Y d →
        ∃! f : G.val ⟶ H.val,
          Matches X Y d τ f ∧
          IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
          (∃ N : ClosedSubgroup T.group,
            IsFinite N.group.X.hom ∧ IsSchemeKernel τ N ∧
            ∃ hi : IsClosedImmersion (N.inclusion ≫ T.inclusion).hom.hom.left,
              let NG : ClosedSubgroup G.val := ⟨N.group, N.inclusion ≫ T.inclusion, hi⟩
              IsSchemeKernel f NG ∧ Centralizes (𝟙 G.val) NG.inclusion.hom.hom) ∧
          (∀ negative positive : List (Root T),
            Enumerates negative {α | ¬ b.IsPos α} →
            Enumerates positive {α | b.IsPos α} →
            let m := rootCellMap T X.groups negative positive
            let m' := rootCellMap S Y.groups (negative.map d) (positive.map d)
            let j := cellCoordinatesMap X Y d τ negative positive
            IsOpenImmersion m.left ∧ IsOpenImmersion m'.left ∧
              IsPullback m j f.hom.hom m') ∧
          (IsIso τ → IsIso f)

end

end LinearAlgebraicGroups.Specs.CellHomomorphism
