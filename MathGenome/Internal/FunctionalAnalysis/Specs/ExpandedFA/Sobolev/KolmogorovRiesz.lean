import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.LpTranslationContinuity
import Mathlib.Analysis.RCLike.Basic

/-!
Independent specification of the Kolmogorov--Riesz clauses of
paper.tex:17857--17882. The Rellich clauses of the same source theorem belong
to the separate goal `ops_rellich`.

The exponent includes 1 and excludes infinity. Scalars may be real or complex.
The finite product norm on `Fin d → ℝ` can be used in the tail and translation
conditions: all norms in finite dimension give the same conditions. There is
no positive-dimension assumption.

The uniform translation condition is expressed by its epsilon/delta meaning,
including the empty-family case. On a bounded family it is equivalent to the
displayed convergence of the supremum of translation differences in the paper.
Restriction takes values in Lᵖ for the restricted measure, with its usual norm;
it is not an assertion of compactness in a weaker topology.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal Topology
universe u

namespace ExpandedFA.Sobolev.KolmogorovRieszSpec

abbrev Space (E : Type*) [NormedAddCommGroup E] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p
    (volume : Measure (Fin d → ℝ))

def LpRestrictType :=
  ∀ {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) (s : Set X),
    Lp E p μ → Lp E p (μ.restrict s)

/-- Restrict the a.e. class, not a chosen pointwise modification of its values. -/
def LpRestrictValue : LpRestrictType :=
  fun _p _ _μ s f => ((Lp.memLp f).restrict s).toLp f

/-- Uniformly small Lᵖ tails, outside a sufficiently large closed ball. -/
def UniformLpTails {E : Type*} [NormedAddCommGroup E] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set (Space E d p)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ f ∈ A,
    ‖LpRestrictValue p volume (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ f‖ < ε

/-- Uniform translation continuity; τ_h f(x)=f(x-h) is the accepted convention.
Changing h to -h gives the convention f(x+h) in the manuscript. -/
def UniformTranslationContinuous {E : Type*} [NormedAddCommGroup E] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Set (Space E d p)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : Fin d → ℝ, ‖h‖ < δ →
    ∀ f ∈ A,
      ‖Distributions.LpTranslationContinuitySpec.LpTranslationValue p h f - f‖ < ε

def CompactImpliesUniformConditions : Prop :=
  ∀ {𝕜 : Type*} [RCLike 𝕜] (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (A : Set (Space 𝕜 d p)), IsCompact (closure A) →
    UniformLpTails p A ∧ UniformTranslationContinuous p A

/-- Full global equivalence for bounded families, with relative norm compactness. -/
def KolmogorovRiesz : Prop :=
  ∀ {𝕜 : Type*} [RCLike 𝕜] (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (A : Set (Space 𝕜 d p)), Bornology.IsBounded A →
    (IsCompact (closure A) ↔ UniformLpTails p A ∧ UniformTranslationContinuous p A)

/-- No tightness is assumed for the local assertion. The same original bounded
family and its global translation modulus suffice for every bounded measurable set. -/
def LocalCompactness : Prop :=
  ∀ {𝕜 : Type*} [RCLike 𝕜] (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (A : Set (Space 𝕜 d p)), Bornology.IsBounded A →
    UniformTranslationContinuous p A →
    ∀ s : Set (Fin d → ℝ), MeasurableSet s → Bornology.IsBounded s →
      IsCompact (closure (LpRestrictValue p volume s '' A))

/-- Assembly of the global equivalence from the local compactness theorem. -/
def GlobalAssembly : Prop := LocalCompactness.{u} → KolmogorovRiesz.{u}

end ExpandedFA.Sobolev.KolmogorovRieszSpec
