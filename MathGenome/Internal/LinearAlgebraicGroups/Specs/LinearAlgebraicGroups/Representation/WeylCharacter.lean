import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagEulerAndVanishing
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylModules

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.WeylCharacter

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open EquivariantAffineModules (CharacterRing)
open FlagEulerCharacteristic (halfWeightDomain includeCharacters)
open FlagLineBundle (OppositeBorelPair)
open FormalCharacters (formalCharacter)
open GeometricRadicals (IsUnipotentRadical)
open InducedNonvanishing (Dominant)
open PrimitiveLine (IsSimple)
open SimpleClassification (SocleModel)
open Unipotent (closedSubgroupAlgebraicGroup)
open WeylDenominator (GroupRing alternant rho)
open WeylModules (IsDual oppositeWeight)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- A character given by the Weyl quotient in the fraction field of the
half-weight group ring, using the exponent convention of E10. -/
def SatisfiesFormula {P : OppositeBorelPair G} [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) [Finite (Root P.torus)] [Finite D.rootDatum.weylGroup]
    (b : D.rootDatum.Base) (χ : Character P.torus.group) (c : CharacterRing P.torus.group) :
    Prop :=
  letI := D.freeCharacters
  letI := halfWeightDomain P.torus.group
  let r := rho D.rootDatum (subgroupRoots P.torus P.positive)
  let A := GroupRing (Additive (Character P.torus.group))
  let j := algebraMap A (FractionRing A)
  j (alternant D.rootDatum b r) ≠ 0 ∧
    j (includeCharacters P.torus.group c) =
      j (alternant D.rootDatum b (2 • Additive.ofMul χ + r)) /
        j (alternant D.rootDatum b r)

/-- The induced and Weyl modules in every characteristic have the same
integral formal character, given by the Weyl formula. The formula also
gives the character of the simple socle when the induced module is simple,
and in particular over a field of characteristic zero. -/
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
        Dominant P χ' ∧
        (∃ (_ : SocleModel P U χ) (S' : SocleModel P U χ')
          (Δ : RootWeightAction.Representation G.val S'.I), IsDual S'.inducedAction Δ) ∧
        ∀ S : SocleModel P U χ,
          SatisfiesFormula D b χ (formalCharacter P.torus S.inducedAction) ∧
          (∀ (S' : SocleModel P U χ') (Δ : RootWeightAction.Representation G.val S'.I),
            IsDual S'.inducedAction Δ →
            formalCharacter P.torus Δ = formalCharacter P.torus S.inducedAction) ∧
          (IsSimple S.inducedAction → SatisfiesFormula D b χ (formalCharacter P.torus S.socleAction)) ∧
          (CharZero k → SatisfiesFormula D b χ (formalCharacter P.torus S.socleAction))

end

end LinearAlgebraicGroups.Specs.WeylCharacter
