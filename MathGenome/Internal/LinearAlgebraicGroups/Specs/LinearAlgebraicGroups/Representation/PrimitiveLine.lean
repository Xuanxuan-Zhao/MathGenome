import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.CyclicHighestWeight

universe u

namespace LinearAlgebraicGroups.Specs.PrimitiveLine

open CategoryTheory
open AbstractPairing (Datum)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CyclicHighestWeight (orbitSpan)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open RootWeightAction (Representation act extendVector weightSpace IsPrimitive DominanceLE IsDominant)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open scoped CategoryTheory.MonObj

noncomputable section

variable {k I J : Type u} [Field k] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {G : AffineAlgebraicGroup k}

/-- One contraction of the orbit of a vector over a test algebra. -/
def orbitCoefficient (ρ : Representation G.val I) (R : TestAlgebra k)
    (g : GroupPoints G.val R) (ℓ : R →ₗ[k] k) (v : I → k) : I → k :=
  fun i ↦ ℓ (act ρ R g (extendVector R v) i)

/-- A rational submodule contains the coefficients of the orbit of each of its vectors. -/
def IsStable (ρ : Representation G.val I) (M : Submodule k (I → k)) : Prop :=
  ∀ v ∈ M, orbitSpan ρ (𝟙 G.val.X) v ≤ M

/-- A simple rational module is nonzero and has only the two trivial submodules. -/
def IsSimple (ρ : Representation G.val I) : Prop :=
  (⊤ : Submodule k (I → k)) ≠ ⊥ ∧
    ∀ M : Submodule k (I → k), IsStable ρ M → M = ⊥ ∨ M = ⊤

/-- Equivariance tested on all coefficients over all commutative test algebras. -/
def IsEquivariant (ρ : Representation G.val I) (σ : Representation G.val J)
    (F : (I → k) →ₗ[k] (J → k)) : Prop :=
  ∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (ℓ : R →ₗ[k] k) (v : I → k),
    F (orbitCoefficient ρ R g ℓ v) = orbitCoefficient σ R g ℓ (F v)

/-- Cyclic highest-weight modules and the primitive lines of simple rational modules. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsSubgroupOf T B →
      ∃ comm : IsCommMonObj T.group.X, letI := comm
      ∃ (D : Datum T) (U : ClosedSubgroup B.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U ∧
      (∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I)
        (lam : Character T.group) (v : I → k), IsPrimitive ρ T B U lam v →
        orbitSpan ρ (𝟙 G.val.X) v = ⊤ →
        weightSpace ρ T lam = Submodule.span k {v} ∧
        (∀ mu : Character T.group, weightSpace ρ T mu ≠ ⊥ → mu ≠ lam →
          DominanceLE T B mu lam ∧ ¬ DominanceLE T B lam mu) ∧
        IsDominant D B lam ∧
        let M := ⨆ W : {W : Submodule k (I → k) // IsStable ρ W ∧ W ≠ ⊤}, W.val
        IsStable ρ M ∧ M ≠ ⊤ ∧ ∀ W : Submodule k (I → k),
          IsStable ρ W → W ≠ ⊤ → W ≤ M) ∧
      (∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I), IsSimple ρ →
        ∃ (lam : Character T.group) (v : I → k), IsPrimitive ρ T B U lam v ∧
          ∀ (mu : Character T.group) (w : I → k), IsPrimitive ρ T B U mu w →
            mu = lam ∧ w ∈ Submodule.span k {v}) ∧
      (∀ {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
        (ρ : Representation G.val I) (σ : Representation G.val J),
        IsSimple ρ → IsSimple σ →
        ∀ (lam : Character T.group) (v : I → k) (w : J → k),
          IsPrimitive ρ T B U lam v → IsPrimitive σ T B U lam w →
          ∃ F : (I → k) ≃ₗ[k] (J → k), IsEquivariant ρ σ F.toLinearMap)

end

end LinearAlgebraicGroups.Specs.PrimitiveLine
