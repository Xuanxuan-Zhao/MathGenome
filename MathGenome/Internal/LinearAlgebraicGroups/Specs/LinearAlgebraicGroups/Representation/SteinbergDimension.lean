import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification
import Mathlib.Algebra.BigOperators.Finprod

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SteinbergDimension

open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open SimpleClassification (SocleModel)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The integral weight that is half the sum of the roots positive for the
marked Borel. Characters are written additively in the lattice equation. -/
def IsHalfPositiveRootSum (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (ρ : Character P.torus.group) : Prop :=
  (2 : ℤ) • Additive.ofMul ρ =
    ∑ᶠ α : subgroupRoots P.torus P.positive, Additive.ofMul α.val.val

/-- On the simply connected semisimple group the half-sum is integral. -/
def HalfSumExists : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {G : AffineAlgebraicGroup k},
    IsSemisimple G → GeometricallySimplyConnected G →
    ∀ P : OppositeBorelPair G, ∀ [IsCommMonObj P.torus.group.X],
      ∃ ρ : Character P.torus.group, IsHalfPositiveRootSum P ρ

/-- Dimension of the simple module of highest weight `(p^r - 1)ρ`.
`SocleModel` realizes the actual simple socle of the induced representation. -/
def Dimension : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    1 ≤ r →
    ∀ {G : AffineAlgebraicGroup k}, IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X],
    ∀ (ρ : Character P.torus.group), IsHalfPositiveRootSum P ρ →
    ∀ (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ S : SocleModel P U (Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)),
      Module.finrank k S.socle = (p ^ r) ^ (subgroupRoots P.torus P.positive).ncard

end LinearAlgebraicGroups.Specs.SteinbergDimension
