import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

open MeasureTheory Set
open scoped ENNReal

namespace Specs.D12Complex.Ch04.CountableFiberTransport

/-- The original source occurrences, including every partition piece. -/
abbrev sourceSet_type := (ℕ → Set ℝ) → Set ℝ
def sourceSet_value : sourceSet_type := fun P => ⋃ n, P n

abbrev fiber_type := (ℝ → ℂ) → (ℕ → Set ℝ) → ℂ → Set ℝ
def fiber_value : fiber_type := fun f P z => {t | t ∈ sourceSet_value P ∧ f t = z}

/-- All premises concern individual pieces and their actual image measures. -/
structure TransportHyp (f : ℝ → ℂ) (μ : Measure ℝ) (ν : Measure ℂ)
    (P : ℕ → Set ℝ) : Prop where
  measurableSet : ∀ n, MeasurableSet (P n)
  disjoint : Pairwise (fun i j => Disjoint (P i) (P j))
  continuousOn : ∀ n, ContinuousOn f (P n)
  injOn : ∀ n, Set.InjOn f (P n)
  measurableSet_image : ∀ n, MeasurableSet (f '' P n)
  map_eq : ∀ n, Measure.map f (μ.restrict (P n)) = ν.restrict (f '' P n)

/-- Extended, nonnegative transport counts the actual fiber, with no finiteness premise. -/
def unsigned_transport_type : Prop :=
  ∀ (f : ℝ → ℂ) (μ : Measure ℝ) (ν : Measure ℂ) (P : ℕ → Set ℝ),
    TransportHyp f μ ν P → ∀ h : ℝ → ℝ≥0∞,
    AEMeasurable h (μ.restrict (sourceSet_value P)) →
    AEMeasurable (fun z => ∑' t : fiber_value f P z, h t) ν ∧
    (∫⁻ z, ∑' t : fiber_value f P z, h t ∂ν) =
      ∫⁻ t in sourceSet_value P, h t ∂μ

/-- Absolute convergence, integrability and signed transport, for the same actual fibers. -/
def signed_transport_type : Prop :=
  ∀ (f : ℝ → ℂ) (μ : Measure ℝ) (ν : Measure ℂ) (P : ℕ → Set ℝ),
    TransportHyp f μ ν P → ∀ h : ℝ → ℂ,
    Integrable h (μ.restrict (sourceSet_value P)) →
    (∀ᵐ z ∂ν, (∑' t : fiber_value f P z, ENNReal.ofReal ‖h t‖) < ∞ ∧
      Summable (fun t : fiber_value f P z => h t)) ∧
    Integrable (fun z => ∑' t : fiber_value f P z, h t) ν ∧
    (∫ z, ∑' t : fiber_value f P z, h t ∂ν) =
      ∫ t in sourceSet_value P, h t ∂μ

end Specs.D12Complex.Ch04.CountableFiberTransport
