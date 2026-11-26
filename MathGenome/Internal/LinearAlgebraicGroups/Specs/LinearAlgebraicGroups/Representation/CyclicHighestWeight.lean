import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RootWeightAction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations

open CategoryTheory WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.CyclicHighestWeight

open AbstractPairing (Datum)
open RootWeightAction (Representation act extendVector weightSpace IsPrimitive DominanceLE IsDominant)
open CharacterDescent (Character)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k}

/-- The coefficient span of a restricted orbit, extracted by linear
functionals on the coordinates of its algebra-valued points. -/
def orbitSpan (ρ : Representation G.val I) {X : SchemeOver k} (f : X ⟶ G.val.X)
    (v : I → k) : Submodule k (I → k) :=
  ⨆ (R : TestAlgebra k) (x : Points X R),
    Submodule.span k (Set.range fun ℓ : R →ₗ[k] k ↦
      fun i ↦ ℓ (act ρ R (x ≫ f) (extendVector R v) i))

/-- Contraction against all linear functionals on the coordinate coalgebra
gives the span of the vector coefficients of the coaction. -/
def coactionSpan {A : HopfAlgebraCategory k}
    (δ : RightComodule k A (I → k)) (v : I → k) : Submodule k (I → k) :=
  Submodule.span k (Set.range fun ℓ : A →ₗ[k] k ↦
    TensorProduct.rid k (I → k) (ℓ.lTensor (I → k) (δ.coaction v)))

/-- A coaction realizing the orbit matrices in the given basis over the
coordinate Hopf algebra. -/
def IsOrbitCoaction {A : HopfAlgebraCategory k}
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ρ : Representation G.val I) (δ : RightComodule k A (I → k)) : Prop :=
  ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (v : I → k) (i : I),
    LinearAlgebraicGroups.RationalRepresentations.tensorCoordinate
        (Pi.basisFun k I) i (LinearAlgebraicGroups.RationalRepresentations.evaluate A δ a v) =
      act ρ R (e.hom.app R (toConv a)) (extendVector R v) i

/-- The orbit span agrees with the coaction coefficient span and is the
smallest rational submodule containing the vector. -/
def CoactionComparison : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I] (G : AffineAlgebraicGroup k)
    (ρ : Representation G.val I) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val),
    ∃ δ : RightComodule k A (I → k), IsOrbitCoaction e ρ δ ∧
      ∀ v : I → k,
        let W := orbitSpan ρ (𝟙 G.val.X) v
        W = coactionSpan δ v ∧ v ∈ W ∧ δ.IsSubcomodule W ∧
          ∀ M : Submodule k (I → k), δ.IsSubcomodule M → v ∈ M → W ≤ M

/-- For a primitive vector in a finite-dimensional rational representation,
the opposite radical computes the full cyclic span. When the vector generates
the representation, its weight space is its line, all other weights are
strictly lower, and its weight is dominant. -/
def HighestWeight : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsSubgroupOf T B →
      ∃ comm : IsCommMonObj T.group.X, letI := comm
      ∃ D : Datum T,
      ∀ (U : ClosedSubgroup B.group), IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U →
      ∀ {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation G.val I)
        (lam : Character T.group) (v : I → k), IsPrimitive ρ T B U lam v →
        (∀ (Bneg : ClosedSubgroup G.val), IsKBorel Bneg → IsSubgroupOf T Bneg →
          OpenCell.AreOpposite T B Bneg →
          ∀ Uneg : ClosedSubgroup Bneg.group,
            IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Uneg →
            orbitSpan ρ (𝟙 G.val.X) v =
              orbitSpan ρ (Uneg.inclusion ≫ Bneg.inclusion).hom.hom v) ∧
        (orbitSpan ρ (𝟙 G.val.X) v = ⊤ →
          weightSpace ρ T lam = Submodule.span k {v} ∧
          (∀ mu : Character T.group, mu ≠ lam → weightSpace ρ T mu ≠ ⊥ →
            DominanceLE T B mu lam) ∧ IsDominant D B lam)

def Statement : Prop := CoactionComparison.{u} ∧ HighestWeight.{u}

end

end LinearAlgebraicGroups.Specs.CyclicHighestWeight
