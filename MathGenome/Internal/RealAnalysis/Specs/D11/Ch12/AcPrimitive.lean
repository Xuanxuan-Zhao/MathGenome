import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.BvDefinition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Independent specification of paper.tex:4023–4047. `IntegrableOn` uses
almost everywhere strong measurability, so the densities include all Lebesgue
integrable representatives, rather than only Borel measurable functions.
The primitive and all its values are defined before any asserted regularity.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch12.AcPrimitive

abbrev primitive_type := ∀ {𝕂 : Type*} [RCLike 𝕂], (ℝ → 𝕂) → 𝕂 → ℝ → ℝ → 𝕂

def primitive_value : primitive_type := fun f c a x => c + ∫ t in a..x, f t

/-- All initial integrals are licensed by L1, and the formula holds at
both endpoints as well as every interior point. -/
def primitive_formula : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {a b : ℝ} (f : ℝ → 𝕂) (c : 𝕂),
    a < b → IntegrableOn f (Icc a b) → ∀ x ∈ Icc a b,
    IntervalIntegrable f volume a x ∧ primitive_value f c a x = c + ∫ t in a..x, f t

/-- The original finite-family AC condition, including shared endpoints. -/
def primitive_ac : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {a b : ℝ} (f : ℝ → 𝕂) (c : 𝕂),
    a < b → IntegrableOn f (Icc a b) →
    Specs.D11.Ch12.absolutelyContinuousOnIntervalValue (primitive_value f c a) a b

/-- Classical differentiation at almost every interior point. -/
def primitive_derivative : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {a b : ℝ} (f : ℝ → 𝕂) (c : 𝕂),
    a < b → IntegrableOn f (Icc a b) →
    ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt (primitive_value f c a) (f x) x

/-- A Borel measurable derivative, explicitly zero on its null set of
nondifferentiability in the interior, equal to the density almost everywhere.
`deriv` is the usual totalized classical derivative, zero where it does not exist. -/
def primitive_measurable_derivative : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
    {a b : ℝ} (f : ℝ → 𝕂) (c : 𝕂), a < b → IntegrableOn f (Icc a b) →
    let F := primitive_value f c a
    ∃ N : Set ℝ, MeasurableSet N ∧ volume N = 0 ∧ N ⊆ Ioo a b ∧
      Measurable (deriv F) ∧ (∀ x ∈ N, deriv F x = 0) ∧
      (∀ x ∈ Ioo a b \ N, HasDerivAt F (deriv F x) x) ∧
      deriv F =ᵐ[volume.restrict (Icc a b)] f ∧ IntegrableOn (deriv F) (Icc a b)

/-- Sharp classical partition variation, including the complex case. -/
def primitive_variation : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {a b : ℝ} (f : ℝ → 𝕂) (c : 𝕂),
    a < b → IntegrableOn f (Icc a b) →
    Specs.D11.Ch12.variation_value (primitive_value f c a) a b =
      ENNReal.ofReal (∫ t in a..b, ‖f t‖)

/-- Independence holds at every point of the interval, including endpoints. -/
def primitive_representative_independent : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] {a b : ℝ} (f g : ℝ → 𝕂) (c : 𝕂),
    a < b → IntegrableOn f (Icc a b) → IntegrableOn g (Icc a b) →
    f =ᵐ[volume.restrict (Icc a b)] g →
    ∀ x ∈ Icc a b, primitive_value f c a x = primitive_value g c a x

end Specs.D11.Ch12.AcPrimitive
