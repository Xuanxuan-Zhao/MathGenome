import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.FieldTheory.SeparableClosure

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalRootGroupDescent

open AbstractPairing (Root)
open CharacterDescent (Character)
open GeometricRadicals (IsMaximalTorus IsReductive)
open Pinning (SplitBorelPair)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open RootGroups (AdditiveLine IsRootSubgroup Proportional HasScalarAction)

noncomputable section

variable {F : Type u} [Field F]

local notation "Fsep" => SeparableClosure F

/-- The rational torus inclusion and its identification with the torus of the
marked split pair over the separable closure. -/
structure MarkedTori (G : AffineAlgebraicGroup F) where
  S : ClosedSubgroup G.val
  maximalSplit : IsMaximalSplitTorus S
  T : ClosedSubgroup G.val
  maximalTorus : IsMaximalTorus T
  intoTorus : S.group ⟶ T.group
  intoTorus_eq : intoTorus ≫ T.inclusion = S.inclusion
  P : SplitBorelPair Fsep
  ambient : P.G.val ≅ (groupBaseChange F Fsep).obj G.val
  torus : (groupBaseChange F Fsep).obj T.group ≅ P.T.group
  torus_eq : torus.hom ≫ P.T.inclusion ≫ ambient.hom =
    (groupBaseChange F Fsep).map T.inclusion

variable {G : AffineAlgebraicGroup F}

abbrev MarkedTori.splitInAbsolute (A : MarkedTori G) :
    (groupBaseChange F Fsep).obj A.S.group ⟶ A.P.T.group :=
  (groupBaseChange F Fsep).map A.intoTorus ≫ A.torus.hom

abbrev MarkedTori.restrict (A : MarkedTori G) (χ : Character A.P.T.group) :
    Character ((groupBaseChange F Fsep).obj A.S.group) :=
  A.splitInAbsolute ≫ χ

/-- The only absolute roots restricting to the given nonzero rational line
are the indicated root and its opposite. -/
def HasSingletonRootLine (A : MarkedTori G) (α : Root A.P.T) : Prop :=
  A.restrict α.val ≠ 1 ∧
    ∀ β : Root A.P.T, A.restrict β.val ≠ 1 →
      Proportional (A.restrict α.val) (A.restrict β.val) →
        β.val = α.val ∨ β.val = α.val⁻¹

/-- One of the two isolated absolute root groups descends as a split additive
closed subgroup, with its inclusion after scalar extension. -/
def RootGroupDescent : Prop :=
  ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F), IsReductive G →
    ∀ (A : MarkedTori G) (α : Root A.P.T), HasSingletonRootLine A α →
      ∀ (U : ClosedSubgroup A.P.G.val), IsRootSubgroup A.P.T U α.val →
        ∀ (L : AdditiveLine (SeparableClosure F)) (x : L.group ≅ U.group),
          HasScalarAction A.P.T α.val (x.hom ≫ U.inclusion) →
            ∃ (U₀ : ClosedSubgroup G.val) (L₀ : AdditiveLine F)
              (_ : L₀.group ≅ U₀.group) (s : (groupBaseChange F (SeparableClosure F)).obj U₀.group ≅ U.group),
                s.hom ≫ U.inclusion ≫ A.ambient.hom =
                  (groupBaseChange F (SeparableClosure F)).map U₀.inclusion

end

end LinearAlgebraicGroups.Specs.ExceptionalRootGroupDescent
