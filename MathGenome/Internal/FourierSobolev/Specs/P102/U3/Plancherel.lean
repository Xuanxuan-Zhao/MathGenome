import Mathlib.Analysis.Fourier.LpSpace

/-! Independent specification of paper.tex:1078–1089. The domain has its standard
volume; no positivity of its dimension or separability of the Hilbert target is
assumed. The function Fourier instances below use the negative and positive
exponential signs, respectively. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

namespace P102.Specs.U3.Plancherel

section Pointwise
variable (V H : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev fourierL2_type := Lp (α := V) H 2 ≃ₗᵢ[ℂ] Lp (α := V) H 2

def fourierL2_value : fourierL2_type V H := Lp.fourierTransformₗᵢ V H

/-- A rank-one Schwartz function, φ(x)h. Finite sums are the finite-rank
Schwartz inputs used in the manuscript's extension argument. -/
def tensor (φ : SchwartzMap V ℂ) (h : H) : SchwartzMap V H :=
  SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight h) φ

def schwartzExtension_type : Prop :=
  ∀ f : SchwartzMap V H,
    fourierL2_value V H (f.toLp 2) = (𝓕 f).toLp 2 ∧
    (fourierL2_value V H).symm (f.toLp 2) = (𝓕⁻ f).toLp 2

def innerPreservation_type : Prop :=
  ∀ f g : Lp (α := V) H 2,
    ⟪fourierL2_value V H f, fourierL2_value V H g⟫ = ⟪f, g⟫

/-- Uniqueness already follows from agreement on the rank-one inputs. -/
def uniqueness_type : Prop :=
  ∀ A : fourierL2_type V H,
    (∀ (φ : SchwartzMap V ℂ) (h : H),
      A ((tensor V H φ h).toLp 2) = (𝓕 (tensor V H φ h)).toLp 2) →
    A = fourierL2_value V H

/-- Compatibility for arbitrary representatives in L¹∩L². -/
def integralCompatibility_type : Prop :=
  ∀ (f : V → H) (hf : MemLp f 2), Integrable f →
    (fourierL2_value V H hf.toLp : V → H) =ᵐ[volume] 𝓕 f

/-- The inverse is the positive-sign action, also on all of L¹∩L². -/
def inverseCompatibility_type : Prop :=
  (∀ f : Lp (α := V) H 2, (fourierL2_value V H).symm f = 𝓕⁻ f) ∧
  (∀ (f : V → H) (hf : MemLp f 2), Integrable f →
    ((fourierL2_value V H).symm hf.toLp : V → H) =ᵐ[volume] 𝓕⁻ f)

end Pointwise

universe u v

/-- Fully quantified declaration types for independent binding checks. -/
def canonicalType :=
  ∀ (V : Type u) (H : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  fourierL2_type V H

def schwartzExtensionStatement : Prop :=
  ∀ (V : Type u) (H : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  schwartzExtension_type V H

def innerPreservationStatement : Prop :=
  ∀ (V : Type u) (H : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  innerPreservation_type V H

def uniquenessStatement : Prop :=
  ∀ (V : Type u) (H : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  uniqueness_type V H

def integralCompatibilityStatement : Prop :=
  ∀ (V : Type u) (H : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  integralCompatibility_type V H

def inverseCompatibilityStatement : Prop :=
  ∀ (V : Type u) (H : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  inverseCompatibility_type V H

end P102.Specs.U3.Plancherel
