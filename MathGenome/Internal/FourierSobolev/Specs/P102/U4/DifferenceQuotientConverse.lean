import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DifferenceQuotientEstimate
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace

/-! Independent scope of U4-05 (paper.tex:1454–1468).
All functions are ambient representatives and all domain hypotheses are restricted
measure hypotheses. The converse is strictly interior in p. The two other clauses
retain their original local L¹ and finite p ≥ 1 scopes. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
namespace P102.U4.DifferenceQuotient

/-- The usual meaning of V relatively compact in Ω. -/
def RelativelyCompactIn {d : ℕ} (V Ω : Opens (Space d)) : Prop :=
  IsCompact (closure (V : Set (Space d))) ∧
    closure (V : Set (Space d)) ⊆ (Ω : Set (Space d))

/-- Local Lp on an arbitrary open set, with no boundary integrability required. -/
def LocallyMemLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) (u : Space d → 𝕜) : Prop :=
  ∀ V : Opens (Space d), RelativelyCompactIn V Ω →
    MemLp u p (volume.restrict (V : Set (Space d)))

/-- A finite, uniform bound for sufficiently small nonzero increments in one
coordinate direction. Increments of either sign stay inside Ω. The constant is
an NNReal, so finite and nonnegative; no derivative is assumed. -/
def HasBound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω V : Opens (Space d)) (j : Fin d) (p : ℝ≥0∞)
    (u : Space d → 𝕜) (C : ℝ≥0) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
    (∀ x ∈ (V : Set (Space d)), x + h • coordinateVector d j ∈ (Ω : Set (Space d))) ∧
    MemLp (quotient u j h) p (volume.restrict (V : Set (Space d))) ∧
    eLpNorm (quotient u j h) p (volume.restrict (V : Set (Space d))) ≤ C

/-- Uniform bounds may depend on the relatively compact open set. -/
def LocallyBounded {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (j : Fin d) (p : ℝ≥0∞) (u : Space d → 𝕜) : Prop :=
  ∀ V : Opens (Space d), RelativelyCompactIn V Ω → ∃ C : ℝ≥0, HasBound Ω V j p u C

/-- An increasing open exhaustion by relatively compact subsets. -/
def IsExhaustion {d : ℕ} (Ω : Opens (Space d)) (V : ℕ → Opens (Space d)) : Prop :=
  Monotone V ∧ (∀ n, RelativelyCompactIn (V n) Ω) ∧
    (⋃ n, (V n : Set (Space d))) = (Ω : Set (Space d))

end DifferenceQuotient
namespace DifferenceQuotientConverseExpected
open DifferenceQuotient

/-- One derivative works on all relatively compact opens and obeys every
admissible quotient bound, not only an arbitrarily selected family of constants. -/
def LocalConverse : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d) (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (j : Fin d) (p : ℝ≥0∞), 1 < p → p ≠ ∞ →
    ∀ u : Space d → 𝕜, LocallyMemLp Ω p u → LocallyBounded Ω j p u →
    ∃ v : Space d → 𝕜,
      LocallyIntegrableOn v Ω volume ∧ LocallyMemLp Ω p v ∧
      distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v ∧
      ∀ (V : Opens (Space d)) (C : ℝ≥0), RelativelyCompactIn V Ω →
        HasBound Ω V j p u C →
        eLpNorm v p (volume.restrict (V : Set (Space d))) ≤ C

/-- A common quotient bound along any increasing exhaustion yields the global
Lp derivative bound. Global Lp of u itself is not required. -/
def GlobalConverse : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d) (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (j : Fin d) (p : ℝ≥0∞), 1 < p → p ≠ ∞ →
    ∀ (u : Space d → 𝕜) (V : ℕ → Opens (Space d)) (C : ℝ≥0),
      LocallyMemLp Ω p u → IsExhaustion Ω V → (∀ n, HasBound Ω (V n) j p u C) →
      ∃ v : Space d → 𝕜,
        LocallyIntegrableOn v Ω volume ∧
        MemLp v p (volume.restrict (Ω : Set (Space d))) ∧
        distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v ∧
        eLpNorm v p (volume.restrict (Ω : Set (Space d))) ≤ C

/-- All clauses of the original theorem, including the distinct endpoint scopes.
The forward estimate assumes local L¹ of u and v and Lp on the neighborhood
only for the derivative v, as specified by DifferenceQuotientExpected.Estimate. -/
def FullTheorem : Prop :=
  ACLExpected.Characterization ∧ DifferenceQuotientExpected.Estimate ∧
    LocalConverse ∧ GlobalConverse

end DifferenceQuotientConverseExpected
end P102.U4
