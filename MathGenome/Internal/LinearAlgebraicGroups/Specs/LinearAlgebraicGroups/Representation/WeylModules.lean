import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace LinearAlgebraicGroups.Specs.WeylModules

open AbstractPairing (Datum Root)
open AdjointRepresentation (GroupPoints)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open FlagLineBundle (OppositeBorelPair)
open GeometricRadicals (IsUnipotentRadical)
open InducedNonvanishing (Dominant)
open PrimitiveLine (IsEquivariant IsStable)
open RootWeightAction (Representation weightSpace DominanceLE)
open SimpleClassification (SocleModel)
open Unipotent (closedSubgroupAlgebraicGroup)

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : AffineAlgebraicGroup k}

/-- The matrix of the dual action in the basis dual to the given basis. -/
def IsDual (ρ σ : Representation G.val I) : Prop :=
  ∀ (R : TestAlgebra k) (g : GroupPoints G.val R),
    (σ.app R g : Matrix.GeneralLinearGroup I R).val =
      (((ρ.app R g : Matrix.GeneralLinearGroup I R)⁻¹).val).transpose

/-- An isomorphism of rational representations. -/
def Isomorphic (ρ : Representation G.val I) (σ : Representation G.val J) : Prop :=
  Nonempty {f : (I → k) ≃ₗ[k] (J → k) // IsEquivariant ρ σ f.toLinearMap}

/-- An equivariant quotient whose kernel contains every proper rational submodule. -/
def HasHead (ρ : Representation G.val I) (σ : Representation G.val J) : Prop :=
  ∃ p : (I → k) →ₗ[k] (J → k), IsEquivariant ρ σ p ∧ Function.Surjective p ∧
    LinearMap.ker p ≠ ⊤ ∧
    ∀ N : Submodule k (I → k), IsStable ρ N → N ≠ ⊤ → N ≤ LinearMap.ker p

/-- The indicated weight is greatest in the dominance order and its space is a line. -/
def HighestWeightLine (P : OppositeBorelPair G) (ρ : Representation G.val I)
    (χ : Character P.torus.group) : Prop :=
  Module.finrank k (weightSpace ρ P.torus χ) = 1 ∧
    ∀ ψ, weightSpace ρ P.torus ψ ≠ ⊥ → DominanceLE P.torus P.positive ψ χ

/-- Opposition on the actual character lattice, in multiplicative notation. -/
def oppositeWeight {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (e : DatumAndWeyl.Identification D) (w : D.rootDatum.weylGroup)
    (χ : Character T.group) : Character T.group :=
  ((e.labelEquiv w).val χ)⁻¹

/-- The Weyl module is the contragredient of the induced module at the
opposite weight. Both the induced socle and the Weyl head realize the
simple module of the original highest weight. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∃ comm : IsCommMonObj P.torus.group.X, letI := comm
    ∃ (D : Datum P.torus) (e : DatumAndWeyl.Identification D) (b : D.rootDatum.Base)
      (w₀ : D.rootDatum.weylGroup),
      (∀ α : Root P.torus, b.IsPos α ↔ α ∈ subgroupRoots P.torus P.positive) ∧
      (∀ w, SimpleRoots.wordLength D.rootDatum b w ≤ SimpleRoots.wordLength D.rootDatum b w₀) ∧
      ∀ χ : Character P.torus.group, Dominant P χ →
        let χ' := oppositeWeight e w₀ χ
        Dominant P χ' ∧
        ∃ (S : SocleModel P U χ) (S' : SocleModel P U χ')
          (Δ : Representation G.val S'.I) (Ldual : Representation G.val S.J),
          IsDual S'.inducedAction Δ ∧ IsDual S.socleAction Ldual ∧
          HasHead Δ S.socleAction ∧ Isomorphic Ldual S'.socleAction ∧
          HighestWeightLine P S.inducedAction χ ∧ HighestWeightLine P S.socleAction χ ∧
          HighestWeightLine P Δ χ ∧
          (CharZero k → Isomorphic Δ S.socleAction ∧ Isomorphic S.socleAction S.inducedAction)

end LinearAlgebraicGroups.Specs.WeylModules
