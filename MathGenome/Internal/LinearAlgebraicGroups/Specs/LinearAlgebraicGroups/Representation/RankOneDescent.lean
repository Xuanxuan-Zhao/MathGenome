import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.TypeAOneLattices
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.RankOneDescent

open AbstractPairing (IsAttachedCoroot Root)
open BorelsAndChambers (subgroupRoots)
open CentralIsogenies (IsCentralIsogeny IsTorusRestriction characterPullback)
open CentralTorus (IsSchemeCentre)
open CharacterDescent (Character)
open CharacterPairing (powerMorphism)
open DiagonalizableGroups (groupAlgebra IntegerCharacters rootsOfUnityPoints)
open FlagLineBundle (OppositeBorelPair)
open GeneralLinearCentralIsogeny (pointMap)
open GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsUnipotentRadical)
open InducedNonvanishing (Dominant)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open RootWeightAction (Representation act weightSpace)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleClassification (SocleModel)
open SmoothnessAndIsogenies (rootsOfUnityCoordinates)
open SpecialLinearDatum (DiagonalTorus LatticeIdentification RootIdentification UpperTriangularBorel)
open StandardGroups (multiplicativePoints)
open TypeAOneLattices (ScalarQuotient RatioTorus DualGenerators firstIndex lastIndex)
open Unipotent (closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k] {G S M : AffineAlgebraicGroup k}
variable {g : MatrixPoints G 2} {s : SpecialMatrixPoints S 2}
variable {a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k}

abbrev SplitLine (k : Type u) [Field k] := specGroup (groupAlgebra k IntegerCharacters.{u})

/-- The chosen Borel of the matrix special linear group and its opposite. -/
structure MatrixBorels (s : SpecialMatrixPoints S 2) where
  diagonal : DiagonalTorus s
  lattice : LatticeIdentification diagonal
  roots : RootIdentification diagonal lattice
  upper : UpperTriangularBorel diagonal lattice roots
  lower : ClosedSubgroup S.val
  lowerBorel : IsKBorel lower
  diagonalInLower : IsSubgroupOf diagonal.subgroup lower
  opposite : OpenCell.AreOpposite diagonal.subgroup upper.limits.parabolic lower

abbrev MatrixBorels.pair (B : MatrixBorels s) : OppositeBorelPair S where
  torus := B.diagonal.subgroup
  positive := B.upper.limits.parabolic
  negative := B.lower
  reductive := B.upper.reductive
  split := B.diagonal.split
  maximal := B.upper.maximal
  positiveBorel := B.upper.isBorel
  negativeBorel := B.lowerBorel
  inPositive := B.upper.containsTorus
  inNegative := B.diagonalInLower
  opposite := B.opposite

/-- A descent is a representation on the same vector space whose pullback
is the given representation as a natural homomorphism of group functors. -/
def Descends {I : Type u} [Fintype I] [DecidableEq I]
    (f : S.val ⟶ G.val) (ρ : Representation S.val I) : Prop :=
  ∃ σ : Representation G.val I, (groupPointsFunctor k).map f ≫ σ = ρ

/-- The universal coordinate of the square-root group. -/
abbrev squareRootGenerator (k : Type u) [Field k] :
    MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod 2))) :=
  MonoidAlgebra.single ⟨Multiplicative.ofAdd 1⟩ 1

/-- The matrix SL₂/PGL₂ example with its actual torus, Borel, kernel and
finite-dimensional simple socles over the ground field. -/
def MatrixExample (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k) : Prop :=
  ∃ (Q : ScalarQuotient g s a) (B : MatrixBorels s)
      (U : RatioTorus Q) (Upos : ClosedSubgroup B.pair.positive.group)
      (eS : SplitLine k ≅ B.pair.torus.group) (eP : SplitLine k ≅ U.subgroup.group)
      (p : B.pair.torus.group ⟶ U.subgroup.group)
      (N : ClosedSubgroup S.val) (eN : N.group ≅ specGroup (rootsOfUnityCoordinates k 2))
      (r : (groupPointsFunctor k).obj N.group ≅ rootsOfUnityPoints k 2),
      IsCentralIsogeny Q.map ∧ IsTorusRestriction Q.map p ∧
      IsUnipotentRadical (closedSubgroupAlgebraicGroup B.pair.positive) Upos ∧
      DualGenerators eS ∧ DualGenerators eP ∧
      (∀ (R : TestAlgebra k) (t : Rˣ),
        (s.hom.app R (pointMap B.pair.torus.inclusion R (cocharacterPoint eS.hom R t))).val =
          Matrix.diagonal (fun i => ((if i = firstIndex then t else t⁻¹ : Rˣ) : R))) ∧
      (∀ (R : TestAlgebra k) (t : Rˣ),
        a.hom.app R (pointMap U.coordinate.hom R (cocharacterPoint eP.hom R t)) = t) ∧
      (∀ (j : ℤ), characterPullback p (eP.inv ≫ powerMorphism j) =
        eS.inv ≫ powerMorphism (2 * j)) ∧
      (∃ α : Root B.pair.torus, subgroupRoots B.pair.torus B.pair.positive = {α} ∧
        α.val = eS.inv ≫ powerMorphism 2 ∧ IsAttachedCoroot B.pair.torus α eS.hom) ∧
      IsSchemeKernel Q.map N ∧ IsSchemeCentre N ∧
      (∀ (R : TestAlgebra k) (x : Points N.group.X R),
        Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R x)) =
          Matrix.GeneralLinearGroup.scalar (Unipotent.Index.{u} 2) (r.hom.app R x).val) ∧
      (let A := MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod 2)))
       let R := CommAlgCat.of k A
       ∃ x : Points N.group.X R,
         (pointMap eN.hom R x).left = 𝟙 _ ∧
         ((r.hom.app R x).val : A) = squareRootGenerator k ∧
         ∀ m : ℤ, Odd m → (((r.hom.app R x).val ^ m : Aˣ) : A) ≠ 1) ∧
      (∀ [CharP k 2], Subsingleton (Points N.group.X (CommAlgCat.of k (AlgebraicClosure k)))) ∧
      ∀ m : ℤ, let χ := eS.inv ≫ powerMorphism m
        (Dominant B.pair χ ↔ 0 ≤ m) ∧
        (0 ≤ m → Nonempty (SocleModel B.pair Upos χ)) ∧
        ∀ L : SocleModel B.pair Upos χ,
          (∀ j : ℤ, weightSpace L.socleAction B.pair.torus (eS.inv ≫ powerMorphism j) ≠ ⊥ →
            Even (m - j)) ∧
          (∀ (R : TestAlgebra k) (x : Points N.group.X R) (v : L.J → R),
            act L.socleAction R (pointMap N.inclusion R x) v =
              (↑((r.hom.app R x).val ^ m) : R) • v) ∧
          (Descends Q.map L.socleAction ↔ Even m)

/-- The result applies in any natural presentation of the standard matrix groups. -/
def Statement : Prop :=
  ∀ (k : Type u) [Field k] (G S M : AffineAlgebraicGroup k)
    (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k),
    MatrixExample g s a

/-- The standard matrix groups supply the example over every field. -/
def OverEveryField : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (G S M : AffineAlgebraicGroup k) (g : MatrixPoints G 2) (s : SpecialMatrixPoints S 2)
      (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k),
      MatrixExample g s a

end LinearAlgebraicGroups.Specs.RankOneDescent
