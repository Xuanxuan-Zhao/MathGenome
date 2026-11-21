import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Fourier uniqueness and absolutely summable inversion, with probability Haar measure.
The pointwise conclusion is restricted to continuity points of the supplied representative.
Uniform convergence is the net over all finite sets of integer frequencies. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace P102.Periodic.Expected.Uniqueness

def zeroStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ),
  Integrable f (haar T) → (∀ k, coefficient T f k = 0) → f =ᵐ[haar T] 0

def aeEqualityStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f g : Circle T → ℂ),
  Integrable f (haar T) → Integrable g (haar T) →
  (∀ k, coefficient T f k = coefficient T g k) → f =ᵐ[haar T] g

def classEqualityStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f g : L1 T),
  (∀ k, coefficientL1 T f k = coefficientL1 T g k) ↔ f = g

def inversionStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ),
  Integrable f (haar T) → Summable (fun k : ℤ => ‖coefficient T f k‖) →
  ∃ g : C(Circle T, ℂ),
    (∀ x, Summable (fun k : ℤ => ‖coefficient T f k * mode T k x‖)) ∧
    (∀ x, HasSum (fun k : ℤ => coefficient T f k * mode T k x) (g x)) ∧
    TendstoUniformly (fun s : Finset ℤ => fun x => ∑ k ∈ s,
      coefficient T f k * mode T k x) g atTop ∧
    (∀ k, coefficient T g k = coefficient T f k) ∧
    f =ᵐ[haar T] g ∧
    (∀ x, ContinuousAt f x → g x = f x)

/-- This also applies to any other continuous representative of the same L¹ class. -/
def continuityPointStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)]
  (f : Circle T → ℂ) (g : C(Circle T, ℂ)),
  f =ᵐ[haar T] g → ∀ x, ContinuousAt f x → g x = f x

end P102.Periodic.Expected.Uniqueness
