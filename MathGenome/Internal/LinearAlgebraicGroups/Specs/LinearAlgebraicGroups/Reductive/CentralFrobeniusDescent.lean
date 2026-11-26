import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import Mathlib.AlgebraicGeometry.Morphisms.Finite

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.CentralFrobeniusDescent

open AdjointRepresentation (GroupPoints constants dualMap scale)
open CharacterDescent (Character)
open DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive IsTorus)
open Unipotent (IsFppfGroupQuotient)

noncomputable section

variable {k : Type u} [Field k]

/-- Centrality of an inclusion as a morphism of group schemes. -/
def IsCentral {S G : GroupScheme k} (i : S ⟶ G) : Prop :=
  ∀ (Y : SchemeOver k) (g : Y ⟶ G.X), Centralizes i g

/-- The first relative Frobenius kernel, using a Hopf presentation of the
source and the relative Frobenius pullback on that presentation. -/
def IsFirstFrobeniusKernel (p : ℕ) [Fact p.Prime] [CharP k p]
    {S : GroupScheme k} (N : ClosedSubgroup S) : Prop :=
  ∃ (A : HopfAlgebraCategory k) (e : S ≅ specGroup A)
    (f : RelativeFrobenius.twistCoordinates k p A ⟶ A),
    RelativeFrobenius.PullbackFormula k p A f ∧
    IsSchemeKernel (e.hom ≫ specGroupMap f) N

/-- The descended subgroup becomes the first Frobenius kernel of the given
geometric torus, with the comparison respecting the inclusions. -/
def DescendsTorusFrobeniusKernel (p : ℕ) [Fact p.Prime] [CharP k p]
    {G : AffineAlgebraicGroup k} (T : ClosedSubgroup (GeometricGroup G).val)
    (E : ClosedSubgroup G.val) : Prop :=
  let K := AlgebraicClosure k
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  ∃ (N : ClosedSubgroup T.group) (e : (groupBaseChange k K).obj E.group ≅ N.group),
    IsFirstFrobeniusKernel p N ∧
    e.hom ≫ N.inclusion ≫ T.inclusion = (groupBaseChange k K).map E.inclusion

/-- Evaluate the group-scheme character by the generator of the coordinate
Hopf algebra of the multiplicative group. -/
def characterValue {S : GroupScheme k} (χ : Character S)
    {R : TestAlgebra k} (t : GroupPoints S R) : R :=
  let A := CommAlgCat.of k (groupAlgebra k IntegerCharacters)
  let f : A ⟶ R :=
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (X := op R) (Y := op A) (t ≫ χ.hom.hom)).unop
  f.hom (MonoidAlgebra.of k _ integerGenerator)

/-- A character occurs in the adjoint tangent representation if it has a
nonzero tangent eigenvector, with the equation tested on all algebras. -/
def IsAdjointWeight {S G : GroupScheme k} (i : S ⟶ G) (χ : Character S) : Prop :=
  ∃ x : Lie k G, x ≠ 0 ∧
    ∀ (R : TestAlgebra k) (t : GroupPoints S R),
      let a : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
      let xR : GroupPoints G (CommAlgCat.of k (DualNumber R)) :=
        mapPoints (dualMap a) x.toMul.val
      let g := ((groupPointsFunctor k).map i).app R t
      let c := (((groupPointsFunctor k).obj G).map (constants R)).hom g
      c * xR * c⁻¹ = mapPoints (scale R (characterValue χ t)) xR

/-- Divisibility in the character lattice, written in the multiplicative
notation for morphisms to the multiplicative group. -/
def IsCharacterPower {S : GroupScheme k} (n : ℕ) (χ : Character S) : Prop :=
  ∃ ψ : Character S, ψ ^ n = χ

/-- Each torus in the quotient lifts over the very extension field over
which that torus is given. The map onto it is faithfully flat. -/
def LiftsTori {G G₁ : GroupScheme k} (q : G ⟶ G₁) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    let F := groupBaseChange k K
    ∀ S₁ : ClosedSubgroup (F.obj G₁), IsTorus S₁.group →
      ∃ (S : ClosedSubgroup (F.obj G)) (f : S.group ⟶ S₁.group),
        IsTorus S.group ∧ S.inclusion ≫ F.map q = f ≫ S₁.inclusion ∧
        Flat f.hom.hom.left ∧ Surjective f.hom.hom.left

/-- Character and weight comparison for the restriction of the geometric
quotient to the given torus. -/
def ComparesWeights (p : ℕ) {G G₁ : GroupScheme k}
    (T : ClosedSubgroup G) (T₁ : ClosedSubgroup G₁) (f : T.group ⟶ T₁.group) : Prop :=
  Function.Injective (fun χ : Character T₁.group ↦ f ≫ χ) ∧
    (∀ χ : Character T.group, (∃ ψ : Character T₁.group, f ≫ ψ = χ) ↔
      IsCharacterPower p χ) ∧
    (∀ χ : Character T₁.group, χ ≠ 1 →
      (IsAdjointWeight T₁.inclusion χ ↔ IsAdjointWeight T.inclusion (f ≫ χ))) ∧
    ∀ χ : Character T₁.group, χ ≠ 1 → IsAdjointWeight T₁.inclusion χ →
      ∀ n : ℕ, IsCharacterPower (p ^ (n + 1)) (f ≫ χ) ↔ IsCharacterPower (p ^ n) χ

/-- Central Frobenius reduction in characteristic p, with the geometric
image torus and the character comparison attached to a single quotient. -/
def CentralFrobeniusReduction : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k), Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T : ClosedSubgroup (GeometricGroup G).val, IsMaximalTorus T →
      ¬ IsCentral T.inclusion → ¬ SemisimpleLieCentralizer.HasGeometricNoncentralSemisimple G →
      (∃ χ : Character T.group, χ ≠ 1 ∧ IsAdjointWeight T.inclusion χ) ∧
      (∀ χ : Character T.group, χ ≠ 1 → IsAdjointWeight T.inclusion χ → IsCharacterPower p χ) ∧
      ∃ (E : ClosedSubgroup G.val) (G₁ : AffineAlgebraicGroup k) (q : G.val ⟶ G₁.val),
        IsCentral E.inclusion ∧ DescendsTorusFrobeniusKernel p T E ∧
        IsFinite E.group.X.hom ∧ IsFppfGroupQuotient (G := G) (Q := G₁) E q ∧
        IsFinite q.hom.hom.left ∧ Smooth G₁.val.X.hom ∧ ConnectedSpace G₁.val.X.left ∧
        LiftsTori q ∧ (IsReductive G → IsReductive G₁) ∧
        ∃ (T₁ : ClosedSubgroup (GeometricGroup G₁).val) (f : T.group ⟶ T₁.group),
          IsMaximalTorus T₁ ∧
          T.inclusion ≫ (groupBaseChange k (AlgebraicClosure k)).map q = f ≫ T₁.inclusion ∧
          Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧ ComparesWeights p T T₁ f

end

end LinearAlgebraicGroups.Specs.CentralFrobeniusDescent
