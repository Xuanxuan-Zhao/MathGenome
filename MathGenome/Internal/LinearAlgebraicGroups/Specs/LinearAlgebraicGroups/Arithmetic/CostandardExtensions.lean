import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylModules
import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.CostandardExtensions

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsSemisimple IsUnipotentRadical)
open InducedNonvanishing (Dominant)
open PrimitiveLine (IsEquivariant)
open RootWeightAction (Representation)
open SimpleClassification (SocleModel)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (closedSubgroupAlgebraicGroup)
open WeylModules (IsDual oppositeWeight)

variable {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
variable {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Vanishing of Yoneda Ext¹ in finite-dimensional rational representations.
The maps in the extension and the splitting are equivariant as scheme actions. -/
def ExtensionsSplit (quotient : Representation H.val I) (submodule : Representation H.val J) :
    Prop :=
  ∀ {M : Type u} [Fintype M] [DecidableEq M] (middle : Representation H.val M)
    (i : (J → k) →ₗ[k] (M → k)) (q : (M → k) →ₗ[k] (I → k)),
    IsEquivariant submodule middle i → IsEquivariant middle quotient q →
    Function.Injective i → Function.Exact i q → Function.Surjective q →
    ∃ r : (M → k) →ₗ[k] (J → k),
      IsEquivariant middle submodule r ∧ r.comp i = LinearMap.id

/-- The Weyl module is the dual of the induced module at the opposite weight.
Each induced action in a socle model is the left translation action on the
regular functions with the specified opposite Borel covariance. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : AffineAlgebraicGroup k), IsSemisimple H → GeometricallySimplyConnected H →
    ∀ (P : OppositeBorelPair H) (U : ClosedSubgroup P.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
      ∃ comm : IsCommMonObj P.torus.group.X, letI := comm
      ∃ (D : Datum P.torus) (e : DatumAndWeyl.Identification D) (b : D.rootDatum.Base)
        (w₀ : D.rootDatum.weylGroup),
        (∀ α : Root P.torus, b.IsPos α ↔ α ∈ subgroupRoots P.torus P.positive) ∧
        (∀ w, SimpleRoots.wordLength D.rootDatum b w ≤ SimpleRoots.wordLength D.rootDatum b w₀) ∧
        ∀ lam mu : Character P.torus.group, Dominant P lam → Dominant P mu →
          (∃ (S : SocleModel P U (oppositeWeight e w₀ lam)) (_N : SocleModel P U mu)
            (Δ : Representation H.val S.I), IsDual S.inducedAction Δ) ∧
          ∀ (S : SocleModel P U (oppositeWeight e w₀ lam)) (N : SocleModel P U mu)
            (Δ : Representation H.val S.I),
            IsDual S.inducedAction Δ → ExtensionsSplit Δ N.inducedAction

end LinearAlgebraicGroups.Specs.CostandardExtensions
