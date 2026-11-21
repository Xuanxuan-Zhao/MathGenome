import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.Complex.Basic

/-! The real and complex forms of paper.tex, `fa2:p5:markov-kernel`.
Operators are algebraic scalar-linear maps: boundedness is not assumed.
Complex positivity means preservation of nonnegative real-valued functions.
Oscillation is the diameter of the real range (equivalently maximum minus
minimum on the nonempty compact domain). All measures have the Borel structure.
The strictly positive scalar kernel is real-valued in both scalar cases. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
universe u
namespace ExpandedFA.PartV.MarkovKernel.Spec

variable {K : Type u} [TopologicalSpace K]

def RealMarkov (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ)) : Prop :=
  (∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x) ∧ P 1 = 1

def ComplexMarkov (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ)) : Prop :=
  (∀ f, (∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re) →
    ∀ x, (P f x).im = 0 ∧ 0 ≤ (P f x).re) ∧ P 1 = 1

variable [MeasurableSpace K]

def RealInvariant (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ)) (μ : Measure K) : Prop :=
  IsProbabilityMeasure μ ∧ μ.Regular ∧ ∀ f : C(K, ℝ), ∫ x, P f x ∂μ = ∫ x, f x ∂μ

def ComplexInvariant (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ)) (μ : Measure K) : Prop :=
  IsProbabilityMeasure μ ∧ μ.Regular ∧ ∀ f : C(K, ℂ), ∫ x, P f x ∂μ = ∫ x, f x ∂μ

/-- The usual real oscillation, also meaningful for constant functions. -/
def oscillation (f : C(K, ℝ)) : ℝ := Metric.diam (range f)

/-- No continuity assumption on the algebraic positive unital operator. -/
def RealExistence : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ)),
    RealMarkov P → ∃ μ : Measure K, RealInvariant P μ

def ComplexExistence : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ)),
    ComplexMarkov P → ∃ μ : Measure K, ComplexInvariant P μ

/-- The full quantitative strict-kernel conclusion. The estimate includes n=0
and epsilon=1; in the latter case the first iterate is already constant. -/
def RealStrictKernel : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (P : C(K, ℝ) →ₗ[ℝ] C(K, ℝ)),
    RealMarkov P → ∀ (ν : Measure K) [IsProbabilityMeasure ν]
      (k : C(K × K, ℝ)) (ε : ℝ), 0 < ε → (∀ x y, ε ≤ k (x, y)) →
      (∀ f x, P f x = ∫ y, k (x, y) * f y ∂ν) →
      ∃ μ : Measure K, RealInvariant P μ ∧
        (∀ η : Measure K, RealInvariant P η → η = μ) ∧
        ε ≤ 1 ∧
        (∀ (f : C(K, ℝ)) (n : ℕ),
          oscillation ((P : C(K, ℝ) → C(K, ℝ))^[n] f) ≤
            (1 - ε)^n * oscillation f) ∧
        (∀ (f : C(K, ℝ)) (n : ℕ),
          ‖(P : C(K, ℝ) → C(K, ℝ))^[n] f - ContinuousMap.const K (∫ x, f x ∂μ)‖ ≤
            (1 - ε)^n * oscillation f) ∧
        (∀ f : C(K, ℝ), Tendsto (fun n => (P : C(K, ℝ) → C(K, ℝ))^[n] f)
          atTop (𝓝 (ContinuousMap.const K (∫ x, f x ∂μ)))) ∧
        (ε = 1 → ∀ f : C(K, ℝ), P f = ContinuousMap.const K (∫ x, f x ∂μ))

/-- The complex iterates converge in supremum norm. The estimate applies the
real oscillation bound to the real and imaginary components, without any
self-adjointness premise. -/
def ComplexStrictKernel : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (P : C(K, ℂ) →ₗ[ℂ] C(K, ℂ)),
    ComplexMarkov P → ∀ (ν : Measure K) [IsProbabilityMeasure ν]
      (k : C(K × K, ℝ)) (ε : ℝ), 0 < ε → (∀ x y, ε ≤ k (x, y)) →
      (∀ f x, P f x = ∫ y, (k (x, y) : ℂ) * f y ∂ν) →
      ∃ μ : Measure K, ComplexInvariant P μ ∧
        (∀ η : Measure K, ComplexInvariant P η → η = μ) ∧ ε ≤ 1 ∧
        (∀ (f : C(K, ℂ)) (n : ℕ),
          oscillation ⟨fun x => (((P : C(K, ℂ) → C(K, ℂ))^[n] f) x).re,
              Complex.continuous_re.comp ((P : C(K, ℂ) → C(K, ℂ))^[n] f).continuous⟩ ≤
            (1 - ε)^n * oscillation ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩ ∧
          oscillation ⟨fun x => (((P : C(K, ℂ) → C(K, ℂ))^[n] f) x).im,
              Complex.continuous_im.comp ((P : C(K, ℂ) → C(K, ℂ))^[n] f).continuous⟩ ≤
            (1 - ε)^n * oscillation ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩) ∧
        (∀ (f : C(K, ℂ)) (n : ℕ),
          ‖(P : C(K, ℂ) → C(K, ℂ))^[n] f - ContinuousMap.const K (∫ x, f x ∂μ)‖ ≤
            (1 - ε)^n * (oscillation ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩ +
              oscillation ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩)) ∧
        (∀ f : C(K, ℂ), Tendsto (fun n => (P : C(K, ℂ) → C(K, ℂ))^[n] f)
          atTop (𝓝 (ContinuousMap.const K (∫ x, f x ∂μ)))) ∧
        (ε = 1 → ∀ f : C(K, ℂ), P f = ContinuousMap.const K (∫ x, f x ∂μ))

end ExpandedFA.PartV.MarkovKernel.Spec
