import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FiniteDistributions
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification

open CategoryTheory AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RestrictedCyclicity

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open RootGroups (AdditiveLine CorootReflection rootPoint)
open RootWeightAction (Representation act extendVector fixedSpace weightSpace SimpleRoot)
open FlagLineBundle (OppositeBorelPair)
open AbstractPairing (IsAttachedCoroot)
open InducedNonvanishing (Dominant)
open SimpleClassification (SocleModel)
open GeometricRadicals (IsUnipotentRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.FiniteDistributions (Dist FrobeniusFormula pair twistCoordinates)

noncomputable section

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]

/-- The coordinate polynomials of the root orbit, obtained at the universal
point of the affine line. -/
def orbitPolynomial {G : GroupScheme k} (ρ : Representation G I)
    {A : AdditiveLine k} (x : A.group ⟶ G) (v : I → k) : I → Polynomial k :=
  let R := CommAlgCat.of k (Polynomial k)
  act ρ R (rootPoint x R Polynomial.X) (extendVector R v)

/-- In matched rank-one coordinates the orbit under the negative root has
degree at most the highest weight's coroot pairing. The coefficient at that
degree is the stated signed Weyl translate. -/
def OppositeRootPolynomial : Prop :=
  ∀ {k I : Type u} [Field k] [Infinite k] [Fintype I] [DecidableEq I]
    {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (α χ : Character T.group) (ρ : Representation G.val I)
    {A : AdditiveLine k} {xpos xneg : A.group ⟶ G.val}
    (D : CorootReflection T α xpos xneg) (v : I → k),
    v ∈ fixedSpace ρ xpos → v ∈ weightSpace ρ T χ →
    ∀ m : ℕ, pairing T.group χ D.coroot = (m : ℤ) →
      (∀ i, (orbitPolynomial ρ xneg v i).natDegree ≤ m) ∧
      (fun i ↦ (orbitPolynomial ρ xneg v i).coeff m) =
        (-1 : k) ^ m • act ρ (CommAlgCat.of k k)
          (CategoryTheory.CartesianMonoidalCategory.toUnit _ ≫ D.representative) v

/-- The highest vector of the simple socle generates on the actual scheme
kernel of the iterated relative Frobenius. The action is contraction of the
socle coaction after the coordinate quotient to that kernel. -/
def Cyclicity : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p],
    0 < r →
    ∀ {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ (χ : Character P.torus.group), Dominant P χ →
    (∀ (α : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group),
      IsAttachedCoroot P.torus α.val c → pairing P.torus.group χ c < (↑(p ^ r) : ℤ)) →
    ∀ (S : SocleModel P U χ) (F : twistCoordinates k p r S.A ⟶ S.A),
      FrobeniusFormula k p r S.A F →
      ∀ h : (kernelIdeal F).IsHopfIdeal k,
        letI := h
        let Q := hopfQuotient S.A (kernelIdeal F)
        let q := hopfQuotientMap S.A (kernelIdeal F)
        ∀ w : S.socle, ∃ δ : Dist k Q,
          pair δ (q.hom.toAlgHom.toLinearMap.lTensor S.socle
            (S.socleCoaction.coaction S.highestVector)) = w

end

end LinearAlgebraicGroups.Specs.RestrictedCyclicity
