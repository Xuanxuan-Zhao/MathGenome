import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.Jordan
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.TotalVariation

/-! Scalar integration, paper.tex:4692–4709. The public integral is defined
only on measurable functions with finite absolute integral against variation.
For an alternative positive decomposition, its component integrals must exist
before their difference can be compared. No mutual singularity is required
of an alternative decomposition. Complex multiplication uses no conjugation. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch14.ScalarIntegration

abbrev signedIntegrable_type :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜], SignedMeasure X → (X → 𝕜) → Prop

def signedIntegrable_value : signedIntegrable_type.{u} := fun ν f =>
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
    (Specs.D11.Ch14.TotalVariation.totalVariation_value ν) f

abbrev complexIntegrable_type :=
  ∀ {X : Type u} [MeasurableSpace X], ComplexMeasure X → (X → ℂ) → Prop

def complexIntegrable_value : complexIntegrable_type.{u} := fun ν f =>
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
    (Specs.D11.Ch14.TotalVariation.totalVariation_value ν) f

abbrev signedIntegral_type :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (ν : SignedMeasure X) (f : X → 𝕜),
    signedIntegrable_value ν f → 𝕜

def signedIntegral_value : signedIntegral_type.{u} := fun ν f _ =>
  (∫ x, f x ∂(Specs.D11.Ch14.Jordan.positivePart_value ν)) -
  (∫ x, f x ∂(Specs.D11.Ch14.Jordan.negativePart_value ν))

abbrev complexIntegral_type :=
  ∀ {X : Type u} [MeasurableSpace X] (ν : ComplexMeasure X) (f : X → ℂ),
    complexIntegrable_value ν f → ℂ

def complexIntegral_value : complexIntegral_type.{u} := fun ν f _ =>
  ((∫ x, f x ∂(Specs.D11.Ch14.Jordan.positivePart_value ν.re)) -
    (∫ x, f x ∂(Specs.D11.Ch14.Jordan.negativePart_value ν.re))) +
  Complex.I * ((∫ x, f x ∂(Specs.D11.Ch14.Jordan.positivePart_value ν.im)) -
    (∫ x, f x ∂(Specs.D11.Ch14.Jordan.negativePart_value ν.im)))

def signedIntegrable_iff : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (f : X → 𝕜),
    signedIntegrable_value ν f ↔ Measurable f ∧ Integrable f (Specs.D11.Ch14.TotalVariation.totalVariation_value ν)

def complexIntegrable_iff : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (f : X → ℂ),
    complexIntegrable_value ν f ↔ Measurable f ∧ Integrable f (Specs.D11.Ch14.TotalVariation.totalVariation_value ν)

def signed_parts_integrable : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable_value ν f),
    Integrable f (Specs.D11.Ch14.Jordan.positivePart_value ν) ∧ Integrable f (Specs.D11.Ch14.Jordan.negativePart_value ν)

def complex_parts_integrable : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable_value ν f),
    signedIntegrable_value ν.re f ∧ signedIntegrable_value ν.im f

def signed_decomposition_independent : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable_value ν f) (μ η : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hν : ∀ E, MeasurableSet E → ν E = (μ E).toReal - (η E).toReal)
    (hμ : Integrable f μ) (hη : Integrable f η),
    signedIntegral_value ν f hf = (∫ x, f x ∂μ) - (∫ x, f x ∂η)

def signedIntegrable_add : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) {f g : X → 𝕜}
    (hf : signedIntegrable_value ν f) (hg : signedIntegrable_value ν g),
    signedIntegrable_value ν (fun x => f x + g x)

def signedIntegrable_const_mul : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (c : 𝕜) {f : X → 𝕜}
    (hf : signedIntegrable_value ν f),
    signedIntegrable_value ν (fun x => c * f x)

def signedIntegral_add : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (f g : X → 𝕜)
    (hf : signedIntegrable_value ν f) (hg : signedIntegrable_value ν g)
    (hfg : signedIntegrable_value ν (fun x => f x + g x)),
    signedIntegral_value ν (fun x => f x + g x) hfg =
      signedIntegral_value ν f hf + signedIntegral_value ν g hg

def signedIntegral_const_mul : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (c : 𝕜) (f : X → 𝕜)
    (hf : signedIntegrable_value ν f) (hcf : signedIntegrable_value ν (fun x => c * f x)),
    signedIntegral_value ν (fun x => c * f x) hcf = c * signedIntegral_value ν f hf

def signedIntegrable_add_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν η : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable_value ν f) (hg : signedIntegrable_value η f),
    signedIntegrable_value (ν + η) f

def signedIntegral_add_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν η : SignedMeasure X) (f : X → 𝕜)
    (hf : signedIntegrable_value ν f) (hg : signedIntegrable_value η f)
    (hfg : signedIntegrable_value (ν + η) f),
    signedIntegral_value (ν + η) f hfg = signedIntegral_value ν f hf + signedIntegral_value η f hg

def signedIntegrable_smul_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (c : ℝ) (f : X → 𝕜)
    (hf : signedIntegrable_value ν f),
    signedIntegrable_value (c • ν) f

def signedIntegral_smul_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (c : ℝ) (f : X → 𝕜)
    (hf : signedIntegrable_value ν f) (hcf : signedIntegrable_value (c • ν) f),
    signedIntegral_value (c • ν) f hcf = c • signedIntegral_value ν f hf

def complex_decomposition_independent : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable_value ν f) (μ₁ μ₂ μ₃ μ₄ : Measure X)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (hν : ∀ E, MeasurableSet E → ν E =
      ((μ₁ E).toReal : ℂ) - ((μ₂ E).toReal : ℂ) +
      Complex.I * (((μ₃ E).toReal : ℂ) - ((μ₄ E).toReal : ℂ)))
    (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂)
    (h₃ : Integrable f μ₃) (h₄ : Integrable f μ₄),
    complexIntegral_value ν f hf = ((∫ x, f x ∂μ₁) - (∫ x, f x ∂μ₂)) +
      Complex.I * ((∫ x, f x ∂μ₃) - (∫ x, f x ∂μ₄))

def complexIntegrable_add : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) {f g : X → ℂ}
    (hf : complexIntegrable_value ν f) (hg : complexIntegrable_value ν g),
    complexIntegrable_value ν (fun x => f x + g x)

def complexIntegrable_const_mul : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (c : ℂ) {f : X → ℂ}
    (hf : complexIntegrable_value ν f),
    complexIntegrable_value ν (fun x => c * f x)

def complexIntegral_add : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (f g : X → ℂ)
    (hf : complexIntegrable_value ν f) (hg : complexIntegrable_value ν g)
    (hfg : complexIntegrable_value ν (fun x => f x + g x)),
    complexIntegral_value ν (fun x => f x + g x) hfg =
      complexIntegral_value ν f hf + complexIntegral_value ν g hg

def complexIntegral_const_mul : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (c : ℂ) (f : X → ℂ)
    (hf : complexIntegrable_value ν f) (hcf : complexIntegrable_value ν (fun x => c * f x)),
    complexIntegral_value ν (fun x => c * f x) hcf = c * complexIntegral_value ν f hf

def complexIntegrable_add_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν η : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable_value ν f) (hg : complexIntegrable_value η f),
    complexIntegrable_value (ν + η) f

def complexIntegral_add_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν η : ComplexMeasure X) (f : X → ℂ)
    (hf : complexIntegrable_value ν f) (hg : complexIntegrable_value η f)
    (hfg : complexIntegrable_value (ν + η) f),
    complexIntegral_value (ν + η) f hfg = complexIntegral_value ν f hf + complexIntegral_value η f hg

def complexIntegrable_smul_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (c : ℂ) (f : X → ℂ)
    (hf : complexIntegrable_value ν f),
    complexIntegrable_value (c • ν) f

def complexIntegral_smul_measure : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (c : ℂ) (f : X → ℂ)
    (hf : complexIntegrable_value ν f) (hcf : complexIntegrable_value (c • ν) f),
    complexIntegral_value (c • ν) f hcf = c * complexIntegral_value ν f hf

def signedIntegrable_simple : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (s : SimpleFunc X 𝕜),
    signedIntegrable_value ν s

def complexIntegrable_simple : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (s : SimpleFunc X ℂ),
    complexIntegrable_value ν s

def signedIntegral_simple : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (s : SimpleFunc X 𝕜)
    (hs : signedIntegrable_value ν s),
    signedIntegral_value ν s hs = ∑ c ∈ s.range, ν (s ⁻¹' {c}) • c

def complexIntegral_simple : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (s : SimpleFunc X ℂ)
    (hs : complexIntegrable_value ν s),
    complexIntegral_value ν s hs = ∑ c ∈ s.range, c * ν (s ⁻¹' {c})

def signedIntegrable_indicator : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : 𝕜),
    signedIntegrable_value ν (E.indicator (fun _ => c))

def complexIntegrable_indicator : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : ℂ),
    complexIntegrable_value ν (E.indicator (fun _ => c))

def signedIntegral_indicator_const : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (ν : SignedMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : 𝕜) (hf : signedIntegrable_value ν (E.indicator (fun _ => c))),
    signedIntegral_value ν (E.indicator (fun _ => c)) hf = ν E • c

def complexIntegral_indicator_const : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (E : Set X)
    (hE : MeasurableSet E) (c : ℂ) (hf : complexIntegrable_value ν (E.indicator (fun _ => c))),
    complexIntegral_value ν (E.indicator (fun _ => c)) hf = c * ν E

def signedIntegral_indicator : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : SignedMeasure X) (E : Set X)
    (hE : MeasurableSet E) (hf : signedIntegrable_value ν (E.indicator (fun _ => (1 : ℝ)))),
    signedIntegral_value ν (E.indicator (fun _ => (1 : ℝ))) hf = ν E

def complexIntegral_indicator : Prop :=
  ∀ {X : Type u} [MeasurableSpace X]
    (ν : ComplexMeasure X) (E : Set X)
    (hE : MeasurableSet E) (hf : complexIntegrable_value ν (E.indicator (fun _ => (1 : ℂ)))),
    complexIntegral_value ν (E.indicator (fun _ => (1 : ℂ))) hf = ν E

end Specs.D11.Ch14.ScalarIntegration
