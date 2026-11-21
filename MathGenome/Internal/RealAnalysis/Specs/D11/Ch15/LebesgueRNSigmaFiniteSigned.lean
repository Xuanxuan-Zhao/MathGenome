import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ExtendedSignedVariant

/-! The extended-signed corollary of paper.tex:5023–5049, on the original
sigma-algebra. `ENNReal.ofReal (f x)` and `ENNReal.ofReal (-f x)` are the
nonnegative positive and negative parts. Their integrals are extended
nonnegative integrals, not totalized real Bochner integrals. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch15.LebesgueRNSigmaFiniteSigned
open D11.Ch14.ScalarInterfaces

/-- Restriction preserves the measurable domain and defined countable sums. -/
def restrict {X : Type u} [MeasurableSpace X] (ν : ExtendedSignedMeasure X)
    (Z : Set X) (hZ : MeasurableSet Z) : ExtendedSignedMeasure X where
  value E := ν.value ⟨E.1 ∩ Z, E.2.inter hZ⟩
  empty := by simpa only [empty_inter] using ν.empty
  omitsInfinity := ν.omitsInfinity.imp (fun h E => h _) (fun h E => h _)
  iUnion E hd := by
    have h := ν.iUnion (fun n => ⟨(E n).1 ∩ Z, (E n).2.inter hZ⟩)
      (fun i j hij => (hd hij).mono inter_subset_left inter_subset_left)
    simpa only [iUnion_inter] using h

end D11.Ch15.LebesgueRNSigmaFiniteSigned

namespace Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned
open _root_.D11.Ch14.ScalarInterfaces
open Ch14.ExtendedSignedVariant
open _root_.D11.Ch15.LebesgueRNSigmaFiniteSigned

/-- Both possible opposing infinite sums are explicitly excluded. -/
def DefinedAdd {X : Type u} [MeasurableSpace X]
    (a s : ExtendedSignedMeasure X) : Prop :=
  ∀ E, (a.value E ≠ ⊤ ∨ s.value E ≠ ⊥) ∧
    (a.value E ≠ ⊥ ∨ s.value E ≠ ⊤)

def Decomposition {X : Type u} [MeasurableSpace X]
    (ν : ExtendedSignedMeasure X) (μ : Measure X)
    (a s : ExtendedSignedMeasure X) : Prop :=
  SigmaFinite (variation_value a) ∧ SigmaFinite (variation_value s) ∧
  DefinedAdd a s ∧ (∀ E, ν.value E = a.value E + s.value E) ∧
  variation_value a ≪ μ ∧ Ch14.ScalarInterfaces.positiveSingular_value (variation_value s) μ

def Density {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (a : ExtendedSignedMeasure X) (f : X → ℝ) : Prop :=
  Measurable f ∧
  ((∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ ∨
    (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) ≠ ⊤) ∧
  ∀ E, ∀ hE : MeasurableSet E,
    a.value ⟨E, hE⟩ = ((∫⁻ x in E, ENNReal.ofReal (f x) ∂μ) : EReal) -
      ((∫⁻ x in E, ENNReal.ofReal (-f x) ∂μ) : EReal)

/-- Existence with restrictions to a common measurable reference-null set. -/
def decomposition_exists : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : ExtendedSignedMeasure X) [SigmaFinite (variation_value ν)],
    ∃ Z : Set X, ∃ hZ : MeasurableSet Z, μ Z = 0 ∧
      Decomposition ν μ (restrict ν Zᶜ hZ.compl) (restrict ν Z hZ)

def decomposition_unique : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (ν a s a' s' : ExtendedSignedMeasure X),
    Decomposition ν μ a s → Decomposition ν μ a' s' → a = a' ∧ s = s'

/-- Real-valued measurable representatives are finite at every point. -/
def density_exists : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (a : ExtendedSignedMeasure X) [SigmaFinite (variation_value a)],
    variation_value a ≪ μ → ∃ f : X → ℝ, Density μ a f

def density_unique : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (a : ExtendedSignedMeasure X) [SigmaFinite (variation_value a)] (f g : X → ℝ),
    Density μ a f → Density μ a g → f =ᵐ[μ] g

/-- The variation identity also records why finite-variation restrictions
have an honest L¹ density. -/
def density_variation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (a : ExtendedSignedMeasure X) (f : X → ℝ), Density μ a f →
    ∀ E, MeasurableSet E → variation_value a E = ∫⁻ x in E, ENNReal.ofReal |f x| ∂μ

def density_local_integrable : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (a : ExtendedSignedMeasure X) (f : X → ℝ), Density μ a f →
    ∀ E, MeasurableSet E → variation_value a E < ⊤ → Integrable (E.indicator f) μ

def ac_singular_part_zero : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (ν a s : ExtendedSignedMeasure X), Decomposition ν μ a s →
    variation_value ν ≪ μ → ∀ E, s.value E = 0

/-- The complete source corollary, with all conclusions for the same parts
and density. The real representative is finite everywhere, hence a.e. -/
def lebesgue_rn_sigmafinite_signed : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (ν : ExtendedSignedMeasure X) [SigmaFinite (variation_value ν)],
    ∃ a s : ExtendedSignedMeasure X, Decomposition ν μ a s ∧
      (∀ a' s', Decomposition ν μ a' s' → a' = a ∧ s' = s) ∧
      ∃ f : X → ℝ, Density μ a f ∧
        (∀ g, Density μ a g → f =ᵐ[μ] g) ∧
        (∀ E, MeasurableSet E → variation_value a E < ⊤ → Integrable (E.indicator f) μ) ∧
        (variation_value ν ≪ μ → ∀ E, s.value E = 0)

end Specs.D11.Ch15.LebesgueRNSigmaFiniteSigned
