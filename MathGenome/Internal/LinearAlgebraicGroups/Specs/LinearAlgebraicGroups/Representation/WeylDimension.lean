import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylCharacter
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum

open AlgebraicGeometry CategoryTheory
open scoped BigOperators CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.WeylDimension

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open EquivariantAffineModules (eChar)
open FlagLineBundle (OppositeBorelPair)
open FormalCharacters (formalCharacter)
open GeneralLinearStructure (SpecialMatrixPoints)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsUnipotentRadical)
open InducedNonvanishing (Dominant)
open PrimitiveLine (IsSimple)
open RootWeightAction (Representation)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleClassification (SocleModel)
open SpecialLinearDatum (DiagonalTorus LatticeIdentification RootIdentification UpperTriangularBorel)
open Unipotent (closedSubgroupAlgebraicGroup)
open WeylCharacter (SatisfiesFormula)
open WeylDenominator (positiveRoots rho)
open WeylModules (IsDual oppositeWeight)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The product over positive coroots. The same factor of two occurs in the
numerator and denominator because the half-weight lattice uses doubled coordinates. -/
def dimensionProduct {P : OppositeBorelPair G} [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) [Finite (Root P.torus)] (χ : Character P.torus.group) : ℚ :=
  let S := subgroupRoots P.torus P.positive
  let r := rho D.rootDatum S
  ∏ α ∈ positiveRoots S,
    (D.rootDatum.toLinearMap (2 • Additive.ofMul χ + r) (D.rootDatum.coroot α) : ℚ) /
      (D.rootDatum.toLinearMap r (D.rootDatum.coroot α) : ℚ)

/-- The common Weyl character and dimension formulas, including their application
to the simple socle whenever induction is simple and in characteristic zero. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∃ comm : IsCommMonObj P.torus.group.X, letI := comm
    ∃ (D : Datum P.torus) (e : DatumAndWeyl.Identification D)
      (hRoots : Finite (Root P.torus)) (hW : Finite D.rootDatum.weylGroup)
      (b : D.rootDatum.Base) (w₀ : D.rootDatum.weylGroup),
      letI := hRoots
      letI := hW
      DominantOrder.IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b ∧
      (∀ w, SimpleRoots.wordLength D.rootDatum b w ≤ SimpleRoots.wordLength D.rootDatum b w₀) ∧
      ∀ χ : Character P.torus.group, Dominant P χ →
        let χ' := oppositeWeight e w₀ χ
        let d := dimensionProduct D χ
        Dominant P χ' ∧
        (∃ (_ : SocleModel P U χ) (S' : SocleModel P U χ')
          (Δ : Representation G.val S'.I), IsDual S'.inducedAction Δ) ∧
        ∀ S : SocleModel P U χ,
          SatisfiesFormula D b χ (formalCharacter P.torus S.inducedAction) ∧
          (Module.finrank k (S.I → k) : ℚ) = d ∧
          (∀ (S' : SocleModel P U χ') (Δ : Representation G.val S'.I),
            IsDual S'.inducedAction Δ →
            formalCharacter P.torus Δ = formalCharacter P.torus S.inducedAction ∧
            (Module.finrank k (S'.I → k) : ℚ) = d) ∧
          (IsSimple S.inducedAction →
            SatisfiesFormula D b χ (formalCharacter P.torus S.socleAction) ∧
            (Module.finrank k (S.J → k) : ℚ) = d) ∧
          (CharZero k →
            SatisfiesFormula D b χ (formalCharacter P.torus S.socleAction) ∧
            (Module.finrank k (S.J → k) : ℚ) = d)

/-- An opposite to the actual upper triangular Borel of matrix SL₂. -/
structure MatrixOpposite {s : SpecialMatrixPoints G 2} {T : DiagonalTorus s}
    {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) where
  negative : ClosedSubgroup G.val
  isBorel : IsKBorel negative
  containsTorus : IsSubgroupOf T.subgroup negative
  opposite : OpenCell.AreOpposite T.subgroup B.limits.parabolic negative

abbrev MatrixOpposite.pair {s : SpecialMatrixPoints G 2} {T : DiagonalTorus s}
    {L : LatticeIdentification T} {M : RootIdentification T L}
    {B : UpperTriangularBorel T L M} (Q : MatrixOpposite B) : OppositeBorelPair G :=
  ⟨T.subgroup, B.limits.parabolic, Q.negative, B.reductive, T.split, B.maximal,
    B.isBorel, Q.isBorel, B.containsTorus, Q.containsTorus, Q.opposite⟩

/-- The character extracting the first diagonal entry on the determinant-one torus. -/
def firstDiagonalCharacter {s : SpecialMatrixPoints G 2} {T : DiagonalTorus s}
    (L : LatticeIdentification T) : Character T.subgroup.group :=
  Additive.toMul (L.characters.symm ((Submodule.span ℤ
    ({(1 : Fin 2 → ℤ)} : Set (Fin 2 → ℤ))).mkQ (SpecialLinearDatum.coordinate 2 0)))

/-- On actual matrix SL₂, an induced module of highest weight m has the
rank-one character and dimension m+1, over every field. -/
def SpecialLinearRankOne : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (s : SpecialMatrixPoints G 2),
    ∃ (T : DiagonalTorus s) (L : LatticeIdentification T) (M : RootIdentification T L)
      (B : UpperTriangularBorel T L M) (Q : MatrixOpposite B)
      (U : ClosedSubgroup Q.pair.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup Q.pair.positive) U ∧
      ∀ m : ℕ,
        let x := firstDiagonalCharacter L
        Dominant Q.pair (x ^ m) ∧ Nonempty (SocleModel Q.pair U (x ^ m)) ∧
        ∀ V : SocleModel Q.pair U (x ^ m),
          formalCharacter T.subgroup V.inducedAction =
            ∑ i ∈ Finset.range (m + 1), eChar (x ^ ((m : ℤ) - 2 * (i : ℤ))) ∧
          Module.finrank k (V.I → k) = m + 1

end

end LinearAlgebraicGroups.Specs.WeylDimension
