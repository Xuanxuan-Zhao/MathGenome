import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Area and change of variables in d12:10-05, paper.tex:2364–2375.

`volume` on ℂ is the standard plane Lebesgue measure (the real-coordinate
identification preserves volume). `NullMeasurableSet E volume` means precisely
that E is measurable for its completion, and `AEMeasurable` represents
measurability for that completion. Integrals against the Borel measure of such
functions agree with the completed integrals. Thus E is not restricted to Borel
sets. Total functions represent functions on the indicated image; no condition
is imposed outside it. `IntegrableOn` includes measurability and finiteness of
the absolute integral, for both real and complex scalars.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Specs.D12Complex.Ch10.ConformalArea
open _root_.D12Complex

def real_jacobian_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f →
    ∀ z ∈ Ω, (fderiv ℝ f z).det = ‖deriv f z‖ ^ 2

def image_nullMeasurable_type : Prop :=
  ∀ (Ω E : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f → InjOn f Ω →
    NullMeasurableSet E volume → E ⊆ Ω → NullMeasurableSet (f '' E) volume

def area_type : Prop :=
  ∀ (Ω E : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f → InjOn f Ω →
    NullMeasurableSet E volume → E ⊆ Ω →
    volume (f '' E) = ∫⁻ z in E, ENNReal.ofReal (‖deriv f z‖ ^ 2)

def measurable_composition_type : Prop :=
  ∀ (Ω E : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f → InjOn f Ω →
    NullMeasurableSet E volume → E ⊆ Ω → ∀ h : ℂ → ℝ≥0∞,
    AEMeasurable h (volume.restrict (f '' Ω)) →
    AEMeasurable (fun z => h (f z)) (volume.restrict E) ∧
    AEMeasurable (fun z => h (f z) * ENNReal.ofReal (‖deriv f z‖ ^ 2))
      (volume.restrict E)

def lintegral_changeOfVariables_type : Prop :=
  ∀ (Ω E : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f → InjOn f Ω →
    NullMeasurableSet E volume → E ⊆ Ω → ∀ h : ℂ → ℝ≥0∞,
    AEMeasurable h (volume.restrict (f '' Ω)) →
    (∫⁻ w in f '' E, h w) =
      ∫⁻ z in E, h (f z) * ENNReal.ofReal (‖deriv f z‖ ^ 2)

def integral_real_changeOfVariables_type : Prop :=
  ∀ (Ω E : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f → InjOn f Ω →
    NullMeasurableSet E volume → E ⊆ Ω → ∀ h : ℂ → ℝ,
    IntegrableOn h (f '' E) →
    IntegrableOn (fun z => h (f z) * ‖deriv f z‖ ^ 2) E ∧
    (∫ w in f '' E, h w) = ∫ z in E, h (f z) * ‖deriv f z‖ ^ 2

def integral_complex_changeOfVariables_type : Prop :=
  ∀ (Ω E : Set ℂ) (f : ℂ → ℂ), HolomorphicOn Ω f → InjOn f Ω →
    NullMeasurableSet E volume → E ⊆ Ω → ∀ h : ℂ → ℂ,
    IntegrableOn h (f '' E) →
    IntegrableOn (fun z => h (f z) * (‖deriv f z‖ ^ 2 : ℝ)) E ∧
    (∫ w in f '' E, h w) = ∫ z in E, h (f z) * (‖deriv f z‖ ^ 2 : ℝ)

end Specs.D12Complex.Ch10.ConformalArea
