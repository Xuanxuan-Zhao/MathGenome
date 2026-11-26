import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.FiniteWordClosure
import Mathlib.AlgebraicGeometry.Geometrically.Connected

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Reductive.DerivedSubgroup

noncomputable section

open Specs.SchemeDerivedGroup (commutatorMap IsDerivedSubgroup FactorsThrough
  IsCommutative RepresentsQuotient)
open Specs.FiniteWordClosure (power)

variable {k : Type u} [Field k]

/-- The product of the commutators of `n` ordered pairs of elements. -/
def commutatorProduct (G : GroupScheme k) :
    (n : ℕ) → power (G.X ⊗ G.X) n ⟶ G.X
  | 0 => 1
  | n + 1 =>
    (fst _ _ ≫ commutatorMap (𝟙 G) (𝟙 G)) *
      (snd _ _ ≫ commutatorProduct G n)

def CommutatorProductType :=
  ∀ {k : Type u} [Field k] (G : GroupScheme k) (n : ℕ),
    power (G.X ⊗ G.X) n ⟶ G.X

/-- The canonical derived subgroup is the scheme-theoretic image of a finite
commutator product. The kernel defining that image pulls back under scalar extension. -/
def FiniteCommutatorProductImage : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (D : ClosedSubgroup G.val),
    IsDerivedSubgroup D → Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    ∃ (n : ℕ) (w : power (G.val.X ⊗ G.val.X) n ⟶ D.group.X),
      0 < n ∧ IsSchemeTheoreticallyDominant w.left ∧
      w ≫ D.inclusion.hom.hom = commutatorProduct G.val n ∧
      RingHom.ker (coordinateMap (commutatorProduct G.val n)).toRingHom =
        RingHom.ker (coordinateMap D.inclusion.hom.hom).toRingHom ∧
      ∀ (K : Type u) [Field K] [Algebra k K],
        (((baseChange k K).map (commutatorProduct G.val n)).left).ker =
          (commutatorProduct G.val n).left.ker.comap
            (pullback.fst G.val.X.hom (fieldSpecMap k K))

def DerivedSubgroupGeometry : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (D : ClosedSubgroup G.val),
    IsDerivedSubgroup D → Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    Smooth D.group.X.hom ∧ GeometricallyConnected D.group.X.hom

def DerivedSubgroupBaseChange : Prop :=
  ∀ {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (D : ClosedSubgroup G.val),
    IsDerivedSubgroup D → Smooth G.val.X.hom → GeometricallyConnected G.val.X.hom →
    let F := groupBaseChange k K
    ∃ h : IsClosedImmersion (F.map D.inclusion).hom.hom.left,
      IsDerivedSubgroup (⟨F.obj D.group, F.map D.inclusion, h⟩ : ClosedSubgroup (F.obj G.val)) ∧
      ∀ E : ClosedSubgroup (F.obj G.val), IsDerivedSubgroup E →
        ∃ e : F.obj D.group ≅ E.group, e.hom ≫ E.inclusion = F.map D.inclusion

def CommutativeQuotientIff : Prop :=
  ∀ {k : Type u} [Field k] {G Q : GroupScheme k} (N : ClosedSubgroup G) (q : G ⟶ Q),
    IsSchemeKernel q N → RepresentsQuotient N q →
    (IsCommutative Q ↔ FactorsThrough N (commutatorMap (𝟙 G) (𝟙 G)))

end

end LinearAlgebraicGroups.Specs.Reductive.DerivedSubgroup
