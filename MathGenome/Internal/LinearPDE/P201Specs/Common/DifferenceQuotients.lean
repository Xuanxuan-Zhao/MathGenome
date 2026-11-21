import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DifferenceQuotientConverse

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal
namespace P201Specs

abbrev differenceQuotientType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  (Space n → 𝕜) → Fin n → ℝ → Space n → 𝕜

/-- Quotients are used only at nonzero steps and where both arguments are admissible.
Ambient representatives are harmless: conclusions use restricted measures. -/
abbrev differenceQuotient : differenceQuotientType :=
  @P102.U4.DifferenceQuotient.quotient

/-- The exact directional segment condition, without a full ball neighborhood. -/
def AdmissibleSegments {n : ℕ} (U V : Domain n) (j : Fin n) (h : ℝ) : Prop :=
  ∀ x ∈ (U : Set (Space n)), ∀ t ∈ Icc (0 : ℝ) 1,
    x + (t * h) • coordinate n j ∈ (V : Set (Space n))

/-- Whole-space identity for arbitrary factors whenever the two product
integrals exist. This also covers nonsmooth compactly supported weak tests. -/
def discreteIntegrationByPartsWholeSpaceStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (w ψ : Space n → 𝕜) (j : Fin n) (h : ℝ), h ≠ 0 →
    Integrable (fun x => w x * ψ x) volume →
    Integrable (fun x => w x * ψ (x - h • coordinate n j)) volume →
    (∫ x, differenceQuotient w j h x * ψ x) =
      -(∫ x, w x * differenceQuotient ψ j (-h) x)

/-- Discrete integration by parts on an open domain. Compactness of the test
support and its translate makes the stipulated boundary separation precise.
Taking Ω = ⊤ gives the whole-space identity. -/
def discreteIntegrationByPartsStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (w : Space n → 𝕜) (ψ : Test 𝕜 Ω) (j : Fin n) (h : ℝ),
    h ≠ 0 → LocallyIntegrableOn w Ω volume →
    (∀ x ∈ tsupport ψ, x + h • coordinate n j ∈ (Ω : Set (Space n))) →
    (∫ x in Ω, differenceQuotient w j h x * ψ x) =
      -(∫ x in Ω, w x * differenceQuotient (ψ : Space n → 𝕜) j (-h) x)

/-- The forward estimate includes p=1. The derivative is the actual coordinate
entry of the distribution-defined W^{1,p} object, not an assumed certificate.
The eLpNorm inequality, together with MemLp, is the Lp norm inequality. -/
def differenceQuotientEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω V U : Domain n) (j : Fin n) (h : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)], p ≠ ∞ → h ≠ 0 →
    P102.U4.DifferenceQuotient.RelativelyCompactIn U V →
    P102.U4.DifferenceQuotient.RelativelyCompactIn V Ω →
    AdmissibleSegments U V j h → ∀ w : W 𝕜 V 1 p,
    MemLp (differenceQuotient (P102.U4.sobolevUnderlying w) j h) p (domainMeasure U) ∧
      eLpNorm (differenceQuotient (P102.U4.sobolevUnderlying w) j h) p (domainMeasure U) ≤
        eLpNorm (P102.U4.sobolevDerivative w ⟨{j}, by simp⟩) p (domainMeasure V)

/-- The converse is restricted to 1<p<∞ and retains the same common bound.
Only the j-th derivative on U is asserted. -/
def differenceQuotientConverseStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω V U : Domain n) (j : Fin n) (p : ℝ≥0∞), 1 < p → p ≠ ∞ →
    P102.U4.DifferenceQuotient.RelativelyCompactIn U V →
    P102.U4.DifferenceQuotient.RelativelyCompactIn V Ω →
    ∀ (w : Lp 𝕜 V p) (C : ℝ≥0),
    (∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
      MemLp (differenceQuotient w j h) p (domainMeasure U) ∧
      eLpNorm (differenceQuotient w j h) p (domainMeasure U) ≤ C) →
    ∃ g : Lp 𝕜 U p,
      distributionDerivative {j} (regularDistribution U w) = regularDistribution U g ∧
      eLpNorm g p (domainMeasure U) ≤ C

end P201Specs
