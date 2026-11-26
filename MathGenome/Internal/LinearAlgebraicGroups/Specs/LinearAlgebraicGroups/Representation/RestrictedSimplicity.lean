import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RestrictedCyclicity

open CategoryTheory WithConv

universe u

namespace LinearAlgebraicGroups.Specs.RestrictedSimplicity

open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open RootWeightAction (SimpleRoot)
open FlagLineBundle (OppositeBorelPair)
open AbstractPairing (IsAttachedCoroot)
open InducedNonvanishing (Dominant)
open SimpleClassification (SocleModel)
open GeometricRadicals (IsUnipotentRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.FiniteDistributions (FrobeniusFormula twistCoordinates)

noncomputable section

/-- The restriction of a simple highest-weight representation at a
(p^r)-restricted dominant weight to the scheme kernel of iterated relative
Frobenius is simple. The restricted coaction uses the Hopf quotient defining
that kernel. The bound concerns the simple coroots of the chosen positive
Borel and places no bound on weights of the central torus. -/
def Simplicity : Prop :=
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
            ∃ δ : RightComodule k Q S.socle,
              δ.coaction = q.hom.toAlgHom.toLinearMap.lTensor S.socle ∘ₗ
                S.socleCoaction.coaction ∧
              (⊤ : Submodule k S.socle) ≠ ⊥ ∧
              ∀ W : Submodule k S.socle, δ.IsSubcomodule W → W = ⊥ ∨ W = ⊤

end

end LinearAlgebraicGroups.Specs.RestrictedSimplicity
