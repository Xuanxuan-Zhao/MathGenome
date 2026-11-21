import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.FiniteColength

/-! The parameter-count and quotient-dimension assertions of Theorem 6.2,
paper.tex:1056–1063. Dimension is computed after quotienting by the
annihilator, without a faithfulness hypothesis. A tuple may be empty. -/
namespace P103.Specs.Ch06.SystemsParameters

universe u v
open P103.Specs.Ch06.DimensionConventions IsLocalRing

/-- The dimension is a natural number, is attained as a parameter count,
and is a lower bound for every finite-colength tuple in the maximal ideal. -/
def parameter_countType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    ∃ d : ℕ, moduleDimensionValue R M = (d : WithBot ℕ∞) ∧
      (∃ x : Fin d → R, (∀ i, x i ∈ maximalIdeal R) ∧
        IsFiniteLength R (M ⧸ (Ideal.span (Set.range x) • (⊤ : Submodule R M)))) ∧
      (∀ (r : ℕ) (x : Fin r → R), (∀ i, x i ∈ maximalIdeal R) →
        IsFiniteLength R (M ⧸ (Ideal.span (Set.range x) • (⊤ : Submodule R M))) → d ≤ r)

/-- In dimension zero the empty tuple suffices, so M itself has finite length. -/
def dimension_zero_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    moduleDimensionValue R M = 0 ↔ IsFiniteLength R M

/-- The quotient is nonzero, both dimensions are finite naturals, and
`d ≤ 1 + e` includes d = 0 without truncated subtraction. -/
def quotient_dimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ maximalIdeal R →
    let N := M ⧸ (Ideal.span ({x} : Set R) • (⊤ : Submodule R M))
    Nontrivial N ∧ ∃ d e : ℕ,
      moduleDimensionValue R M = (d : WithBot ℕ∞) ∧
      moduleDimensionValue R N = (e : WithBot ℕ∞) ∧ d ≤ 1 + e

end P103.Specs.Ch06.SystemsParameters
