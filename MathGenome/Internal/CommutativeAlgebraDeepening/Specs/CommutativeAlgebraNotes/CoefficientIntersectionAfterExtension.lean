import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings

namespace Specs.CommutativeAlgebraNotes.CoefficientIntersectionAfterExtension

open FrobeniusCoefficientDefinitions PBases FiniteCoefficientSubrings

universe u v w

/-- The composita of the embedded coefficient fraction fields with the subfield
of (p)-th powers have intersection equal to that subfield. -/
def FractionSubfieldCompositumIntersection : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k), isPBasis p (frobeniusSubfield k p) le_rfl a →
    ∀ (r s : ℕ),
      let S := CoefficientTowerBase k r s
      let K := FractionRing S
      ∀ (F : Type w) [Field F] [Algebra K F] [Module.Finite K F],
        letI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
        (⨅ J : Finset ι, frobeniusSubfield F p ⊔
          (fractionSubfield (coefficientSubring (p := p) a J r s)).map (algebraMap K F)) =
          frobeniusSubfield F p

/-- Lemma 5.4. A p-basis of the coefficient field provides a single family that
works for every finite extension of the ambient fraction field. -/
def FiniteCoefficientApproximations : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (r s : ℕ),
    let S := CoefficientTowerBase k r s
    let K := FractionRing S
    ∃ E : Set k,
      let a : E → k := Subtype.val
      let S_J := fun J : Finset E => coefficientSubring (p := p) a J r s
      let K_J := fun J => fractionSubfield (S_J J)
      isPBasis p (frobeniusSubfield k p) le_rfl a ∧
      (∀ J, Module.Finite (S_J J) S ∧ Module.Free (S_J J) S ∧
        (frobenius S p).range ≤ S_J J) ∧
      (Set.range K_J).Nonempty ∧ Directed (· ≥ ·) K_J ∧
      ∀ (F : Type w) [Field F] [Algebra K F] [Module.Finite K F],
        letI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
        (⨅ J, frobeniusSubfield F p ⊔ (K_J J).map (algebraMap K F)) =
          frobeniusSubfield F p

end Specs.CommutativeAlgebraNotes.CoefficientIntersectionAfterExtension
