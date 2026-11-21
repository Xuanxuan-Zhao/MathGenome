import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.BallSchauderSolvability

/-!
The initially C² interior assertion of classical Schauder regularity,
paper.tex:2139–2144 and 2321–2335. The functions and coefficients are real,
and L has positive principal part. There is no sign condition on c.
These statements do not assume Hölder continuity of the second derivatives.
-/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.SchauderRegularity
open NewtonHessian PoissonSchauder VariableSchauder

/-- Symmetric principal coefficients with a positive lower ellipticity
bound on a neighborhood of each point. Neither a global lower bound nor
global bounds on any coefficient are imposed by this local condition. -/
def LocallyUniformlyEllipticOn {n : ℕ}
    (a : Space n → Matrix (Fin n) (Fin n) ℝ) (Ω : Domain n) : Prop :=
  ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (Ω : Set (Space n)) ∧
    ∃ ell : ℝ, 0 < ell ∧ UniformlyEllipticOn ell a (ball x r)

/-- Qualitative interior regularity for every initially only C² solution,
including dimension one and open sets with multiple components. -/
def LocalRegularityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ (Ω : Domain n)
      (a : Space n → Matrix (Fin n) (Fin n) ℝ)
      (b : Space n → Space n) (c u f : Space n → ℝ),
      LocallyUniformlyEllipticOn a Ω → CoefficientsHolderLoc α a b c Ω →
      ContDiffOn ℝ 2 u Ω → IsHolderLoc α f Ω →
      (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) →
      IsC2HolderLocOn α u Ω

/-- The original nested-domain estimate, now for initially only C²
solutions. The constant is chosen before the coefficients, u and f, with
the same dependence and the same norms as the a priori estimate. -/
def InteriorEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ Ω Ω' Ω'' : Domain n, Bornology.IsBounded (Ω' : Set (Space n)) →
      closure (Ω' : Set (Space n)) ⊆ (Ω'' : Set (Space n)) → Ω'' ≤ Ω →
      ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
            (b : Space n → Space n) (c : Space n → ℝ),
            UniformlyEllipticOn ell a Ω → CoefficientsHolderLoc α a b c Ω →
            CoefficientsHolderOn α a b c Ω'' → coefficientNormOn α a b c Ω'' ≤ K →
            ∀ u f : Space n → ℝ, ContDiffOn ℝ 2 u Ω → IsHolderLoc α f Ω →
              (∀ x ∈ Ω, nondivergenceOperator a b c u x = f x) →
              IsBoundedOn u Ω'' → IsHolderOn α f Ω'' →
              IsC2HolderOn α u Ω' ∧
              c2HolderNormOn α u Ω' ≤
                C * (supNormOn u Ω'' + holderNormOn α f Ω'')

end P201Specs.Elliptic.SchauderRegularity
