import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelPositivity
import Mathlib.LinearAlgebra.RootSystem.Base

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.DominantOrder

open AbstractPairing (Datum Root)
open BorelsAndChambers (IsPositiveSystem)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)

section Lattices

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing I ℤ X Y)

/-- The base has the specified positive roots. -/
def IsBaseFor (S : Set I) (b : P.Base) : Prop :=
  ∀ i, b.IsPos i ↔ i ∈ S

/-- A character is dominant when it pairs nonnegatively with every simple coroot. -/
def IsDominant (b : P.Base) (weight : X) : Prop :=
  ∀ i ∈ b.support, 0 ≤ P.toLinearMap weight (P.coroot i)

/-- The dominant characters in the full character lattice. -/
abbrev DominantWeights (b : P.Base) := {weight : X // IsDominant P b weight}

/-- The dominance comparison is defined by nonnegative integral combinations of simple roots. -/
def DominanceLE (b : P.Base) (lower upper : X) : Prop :=
  ∃ c : b.support → ℕ, upper - lower = ∑ i : b.support, c i • P.root i.val

/-- Strict dominance requires distinct weights. -/
def DominanceLT (b : P.Base) (lower upper : X) : Prop :=
  DominanceLE P b lower upper ∧ lower ≠ upper

/-- The integral cocharacter given by the sum of the positive coroots. -/
noncomputable def twoRhoCoroot [Finite I] (S : Set I) : Y := by
  classical
  letI := Fintype.ofFinite I
  exact ∑ i ∈ Finset.univ.filter (· ∈ S), P.coroot i

/-- The consequences of dominance for a chosen positive system and its base. -/
structure Laws [Finite I] (S : Set I) (b : P.Base) : Prop where
  orbitRepresentative : ∀ weight : X, ∃! representative : X,
    IsDominant P b representative ∧ ∃ w : P.weylGroup, w.val.weightEquiv weight = representative
  nonnegative : ∀ weight : X, IsDominant P b weight →
    0 ≤ P.toLinearMap weight (twoRhoCoroot P S)
  simplePairing : ∀ i ∈ b.support, P.toLinearMap (P.root i) (twoRhoCoroot P S) = 2
  strictlyIncreasing : ∀ lower upper : X, IsDominant P b lower → IsDominant P b upper →
    DominanceLT P b lower upper →
      P.toLinearMap lower (twoRhoCoroot P S) < P.toLinearMap upper (twoRhoCoroot P S)
  wellFounded : WellFounded
    (fun lower upper : DominantWeights P b ↦ DominanceLT P b lower.val upper.val)
  rootless : IsEmpty I → ∀ lower upper : X, ¬ DominanceLT P b lower upper

end Lattices

/-- The dominant order for every positive system of the split reductive pair, in its
actual character and cocharacter lattices. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ D : Datum T, Nonempty (DatumAndWeyl.Identification D) ∧
          letI := D.finiteRoots
          ∀ S : Set (Root T), IsPositiveSystem T S →
            (∃ b : D.rootDatum.Base, IsBaseFor D.rootDatum S b) ∧
            ∀ b : D.rootDatum.Base, IsBaseFor D.rootDatum S b → Laws D.rootDatum S b

end LinearAlgebraicGroups.Specs.DominantOrder
