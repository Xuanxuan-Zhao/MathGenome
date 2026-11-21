import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls

/-!
Independent statements for paper.tex:5228–5236. The index type can be empty;
the ENNReal supremum then equals zero. The condition includes the shared
measurable-representative L1 predicate. In particular every set integral
appearing in the condition is an integral of an integrable restriction.
No finiteness, atomlessness, completeness or sigma-finiteness is assumed.

The quantitative estimates test all measurable subsets of A. Thus the two
real sign subsets, and the four real/imaginary sign subsets, may depend on f.
Their common bound gives factors two and four respectively.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch17.FollandUIConvention
open Specs.D11.Ch17.UniformControls
open Specs.D11.Ch06.ScalarIntegral

def signedIntegralSup_type :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    Measure X → (ι → X → 𝕜) → Set X → ℝ≥0∞

def signedIntegralSup_value : signedIntegralSup_type.{u,v} := fun μ F A =>
  ⨆ i, ENNReal.ofReal ‖∫ x in A, F i x ∂μ‖

def signedSmall_type :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
    Measure X → (ι → X → 𝕜) → Prop

def signedSmall_value : signedSmall_type.{u,v} := fun μ F =>
  integrableFamily_value μ F ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ A : Set _, MeasurableSet A → μ A < ENNReal.ofReal δ →
      signedIntegralSup_value μ F A < ENNReal.ofReal ε

def signedIntegralSup_le_absolute : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜),
    integrableFamily_value μ F → ∀ A : Set X,
      signedIntegralSup_value μ F A ≤ integralSup_value μ F A

def real_two_piece_estimate : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ),
    scalarIntegrable_value μ f → ∀ (A : Set X), MeasurableSet A → ∀ c : ℝ,
      (∀ B : Set X, MeasurableSet B → B ⊆ A → ‖∫ x in B, f x ∂μ‖ ≤ c) →
      absoluteIntegral_value μ f A ≤ ENNReal.ofReal (2 * c)

/-- RCLike includes the complex four-piece estimate, as well as real scalars. -/
def four_piece_estimate : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ (A : Set X), MeasurableSet A → ∀ c : ℝ,
      (∀ B : Set X, MeasurableSet B → B ⊆ A → ‖∫ x in B, f x ∂μ‖ ≤ c) →
      absoluteIntegral_value μ f A ≤ ENNReal.ofReal (4 * c)

def signedSmall_iff_uiSmall : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜),
    signedSmall_value μ F ↔ uiSmall_value μ F

end Specs.D11.Ch17.FollandUIConvention
