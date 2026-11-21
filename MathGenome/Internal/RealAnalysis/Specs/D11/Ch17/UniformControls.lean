import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
Independent specifications for paper.tex:5196–5217. Families have an arbitrary
index type: a set of representatives is indexed by its subtype. Repetitions do
not affect the suprema, and an empty index type has supremum zero in ENNReal.
All four predicates include individual ordinary measurable integrability; none
adds a uniform norm bound to small-set control. Epsilon and delta are positive
real numbers, compared to the extended integral and measure via `ofReal`.

Finite-p controls apply these very same predicates to the real functions
`‖f‖ ^ p`. The original representatives remain measurable, and `1 ≤ p` is
explicit. There is no assumption of atomlessness, completeness, sigma-finiteness
or finite total measure. No implementation module is imported here.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch17.UniformControls

def absoluteIntegral_type := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (X → 𝕜) → Set X → ℝ≥0∞
def absoluteIntegral_value : absoluteIntegral_type.{u} := fun μ f A =>
  Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value (μ.restrict A)
    (fun x => ENNReal.ofReal ‖f x‖)

def integralSup_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Set X → ℝ≥0∞
def integralSup_value : integralSup_type.{u,v} := fun μ F A => ⨆ i, absoluteIntegral_value μ (F i) A

def amplitudeSup_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → ℝ → ℝ≥0∞
def amplitudeSup_value : amplitudeSup_type.{u,v} := fun μ F R =>
  ⨆ i, absoluteIntegral_value μ (F i) {x | R < ‖F i x‖}

def integrableFamily_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop
def integrableFamily_value : integrableFamily_type.{u,v} := fun μ F =>
  ∀ i, Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value μ (F i)

def uiSmall_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop
def uiSmall_value : uiSmall_type.{u,v} := fun μ F =>
  integrableFamily_value μ F ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ A : Set _, MeasurableSet A → μ A < ENNReal.ofReal δ →
      integralSup_value μ F A < ENNReal.ofReal ε

def spatialTails_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop
def spatialTails_value : spatialTails_type.{u,v} := fun μ F =>
  integrableFamily_value μ F ∧ ∀ ε : ℝ, 0 < ε →
    ∃ E : Set _, MeasurableSet E ∧ μ E < ∞ ∧
      integralSup_value μ F Eᶜ < ENNReal.ofReal ε

def uiTail_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop
def uiTail_value : uiTail_type.{u,v} := fun μ F =>
  integrableFamily_value μ F ∧
    Tendsto (amplitudeSup_value μ F) atTop (𝓝 0)

def uniformL1Bound_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → (ι → X → 𝕜) → Prop
def uniformL1Bound_value : uniformL1Bound_type.{u,v} := fun μ F =>
  integrableFamily_value μ F ∧ integralSup_value μ F univ < ∞

def powerFamily_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], ℝ → (ι → X → 𝕜) → (ι → X → ℝ)
def powerFamily_value : powerFamily_type.{u,v} := fun p F i x => ‖F i x‖ ^ p

def lpFamily_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop
def lpFamily_value : lpFamily_type.{u,v} := fun μ p F =>
  1 ≤ p ∧ ∀ i, F i ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p

def lpUiSmall_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop
def lpUiSmall_value : lpUiSmall_type.{u,v} := fun μ p F =>
  lpFamily_value μ p F ∧ uiSmall_value μ (powerFamily_value p F)

def lpSpatialTails_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop
def lpSpatialTails_value : lpSpatialTails_type.{u,v} := fun μ p F =>
  lpFamily_value μ p F ∧ spatialTails_value μ (powerFamily_value p F)

def lpUiTail_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop
def lpUiTail_value : lpUiTail_type.{u,v} := fun μ p F =>
  lpFamily_value μ p F ∧ uiTail_value μ (powerFamily_value p F)

def lpUniformL1Bound_type := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜], Measure X → ℝ → (ι → X → 𝕜) → Prop
def lpUniformL1Bound_value : lpUniformL1Bound_type.{u,v} := fun μ p F =>
  lpFamily_value μ p F ∧ uniformL1Bound_value μ (powerFamily_value p F)

def absoluteIntegral_formula : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜) (A : Set X),
  absoluteIntegral_value μ f A = ∫⁻ x in A, ENNReal.ofReal ‖f x‖ ∂μ

def absoluteIntegral_eq_L1Norm : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
  absoluteIntegral_value μ f univ = Specs.D11.Ch10.LpDefinition.powerNorm_value μ 1 f

def absoluteIntegral_congr_ae : Prop := ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜) (A : Set X),
  f =ᵐ[μ] g → absoluteIntegral_value μ f A = absoluteIntegral_value μ g A

def integralSup_congr_ae : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, F i =ᵐ[μ] G i) → ∀ A : Set X,
  integralSup_value μ F A = integralSup_value μ G A

def amplitudeSup_congr_ae : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, F i =ᵐ[μ] G i) → ∀ R : ℝ,
  amplitudeSup_value μ F R = amplitudeSup_value μ G R

def integrableFamily_congr_ae : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) →
  (integrableFamily_value μ F ↔ integrableFamily_value μ G)

def controls_congr_ae : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) →
  (uiSmall_value μ F ↔ uiSmall_value μ G) ∧
  (spatialTails_value μ F ↔ spatialTails_value μ G) ∧
  (uiTail_value μ F ↔ uiTail_value μ G) ∧
  (uniformL1Bound_value μ F ↔ uniformL1Bound_value μ G)

def powerFamily_measurable : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → ∀ i, Measurable (powerFamily_value p F i)

def absoluteIntegral_powerFamily : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F : ι → X → 𝕜) (i : ι) (A : Set X),
  absoluteIntegral_value μ (powerFamily_value p F i) A =
    Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value (μ.restrict A)
      (fun x => ENNReal.ofReal (‖F i x‖ ^ p))

def lpFamily_iff : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F : ι → X → 𝕜),
  lpFamily_value μ p F ↔
    1 ≤ p ∧ (∀ i, Measurable (F i)) ∧
      integrableFamily_value μ (powerFamily_value p F)

def lpFamily_congr_ae : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) → (lpFamily_value μ p F ↔ lpFamily_value μ p G)

def lpControls_congr_ae : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (F G : ι → X → 𝕜),
  (∀ i, Measurable (F i)) → (∀ i, Measurable (G i)) →
  (∀ i, F i =ᵐ[μ] G i) →
  (lpUiSmall_value μ p F ↔ lpUiSmall_value μ p G) ∧
  (lpSpatialTails_value μ p F ↔ lpSpatialTails_value μ p G) ∧
  (lpUiTail_value μ p F ↔ lpUiTail_value μ p G) ∧
  (lpUniformL1Bound_value μ p F ↔ lpUniformL1Bound_value μ p G)

def empty_suprema : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) [IsEmpty ι] (F : ι → X → 𝕜),
  (∀ A : Set X, integralSup_value μ F A = 0) ∧
  (∀ R : ℝ, amplitudeSup_value μ F R = 0)

def empty_controls : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) [IsEmpty ι] (F : ι → X → 𝕜),
  uiSmall_value μ F ∧ spatialTails_value μ F ∧ uiTail_value μ F ∧
    uniformL1Bound_value μ F

def empty_lpControls : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) [IsEmpty ι] (p : ℝ) (F : ι → X → 𝕜), 1 ≤ p →
  lpUiSmall_value μ p F ∧ lpSpatialTails_value μ p F ∧
    lpUiTail_value μ p F ∧ lpUniformL1Bound_value μ p F

/-- The separate bound is literally a finite supremum of the shared L1 norms. -/
def uniformL1Bound_iff_normBound : Prop := ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜),
  uniformL1Bound_value μ F ↔ integrableFamily_value μ F ∧
    (⨆ i, Specs.D11.Ch10.LpDefinition.powerNorm_value μ 1 (F i)) < ∞

end Specs.D11.Ch17.UniformControls
