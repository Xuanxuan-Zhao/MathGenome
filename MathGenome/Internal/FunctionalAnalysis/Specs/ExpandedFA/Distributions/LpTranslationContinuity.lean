import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Independent specification for the translation and C_c density clauses of
paper.tex:17287–17320 (`fa2:p4:approximate-identity`). The coordinate space
`Fin d → ℝ` has its usual finite product topology and product Lebesgue measure.
All natural dimensions, including zero, are allowed. Exponents are extended
nonnegative reals with `1 ≤ p` and `p ≠ ∞`, so p = 1 is included.

Density is stated for the accepted strongly measurable a.e. quotient. The
codomain may be any real normed space, hence in particular either scalar field
of the manuscript, and no separability hypothesis is imposed on it.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology
universe u

namespace ExpandedFA.Distributions.LpTranslationContinuitySpec

/-- Translation on the a.e. quotient, with convention τ_h f(x) = f(x-h). -/
def LpTranslationType :=
  ∀ {E : Type u} [NormedAddCommGroup E] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)], (Fin d → ℝ) →
    FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p (volume : Measure (Fin d → ℝ)) →
    FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p (volume : Measure (Fin d → ℝ))

def LpTranslationValue : LpTranslationType.{u} :=
  fun p _ h f => Lp.compMeasurePreserving (p := p) (fun x => x - h)
    (measurePreserving_sub_right volume h) f

/-- Compactly supported continuous representatives form a norm dense subset. -/
def CompactlySupportedContinuousDense : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞),
    Dense {f : FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p
        (volume : Measure (Fin d → ℝ)) |
      ∃ g : (Fin d → ℝ) → E, Continuous g ∧ HasCompactSupport g ∧ f =ᵐ[volume] g}

/-- The definition really acts on representatives by x ↦ x-h. -/
def LpTranslationRepresentative : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : Fin d → ℝ)
    (f : FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p volume),
    LpTranslationValue p h f =ᵐ[volume] fun x => f (x - h)

/-- Translation preserves the Lᵖ distance; this also holds at p = ∞. -/
def LpTranslationIsometry : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : Fin d → ℝ),
    Isometry (LpTranslationValue (E := E) p h)

/-- For each Lᵖ vector, its orbit under translations is norm continuous. -/
def LpTranslationContinuous : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (f : FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p
      (volume : Measure (Fin d → ℝ))),
    Continuous (fun h => LpTranslationValue p h f)

/-- The usual explicit statement ‖τ_h f - f‖ₚ → 0 as h → 0. -/
def LpTranslationNormTendstoZero : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp : p ≠ ∞)
    (f : FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p
      (volume : Measure (Fin d → ℝ))),
    Tendsto (fun h => ‖LpTranslationValue p h f - f‖) (𝓝 0) (𝓝 0)

end ExpandedFA.Distributions.LpTranslationContinuitySpec
