import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HilbertSamuelPolynomial
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions

/-! Independent statements of the full dimension conclusion in Theorem 7.6,
`paper.tex:1247–1278`. The shared length functions use the original ideal
powers on M, and dimension is that of R/Ann(M). No faithfulness, positive
colength ideal, or infinite residue field is assumed. -/
namespace Specs.P103.HilbertSamuelDimension

universe u v
open _root_.P103.HilbertSamuelPolynomial
open _root_.P103.Specs.Ch06.DimensionConventions

/-- The cumulative Hilbert–Samuel polynomial has exact degree dim(M). -/
def quotientDegreeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
    ∀ d : ℕ, moduleDimensionValue R M = (d : WithBot ℕ∞) →
    ∃ p : Polynomial ℚ, EventuallyPolynomial (quotientLength Q M) p ∧
      p ≠ 0 ∧ p.natDegree = d

/-- For positive dimension the layers have exact degree d-1. -/
def positiveLayersType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
    ∀ d : ℕ, moduleDimensionValue R M = (d : WithBot ℕ∞) → 0 < d →
    ∃ p : Polynomial ℚ, EventuallyPolynomial (layerLength Q M) p ∧
      p ≠ 0 ∧ p.natDegree = d - 1

/-- In dimension zero the actual layers eventually vanish, and the quotient
lengths eventually equal a strictly positive constant. -/
def zeroDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (Q : Ideal R), Q ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (M ⧸ (Q • (⊤ : Submodule R M))) →
    moduleDimensionValue R M = 0 →
    ∃ c : ℕ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      layerLength Q M n = 0 ∧ quotientLength Q M n = c

end Specs.P103.HilbertSamuelDimension
