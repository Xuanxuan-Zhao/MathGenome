import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.DominatedEulerLagrange
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

namespace VariationalNotes.Sobolev.EulerLagrange

/-- Regularity in Theorems 8.13--8.14, with one common exceptional set in
all fiber variables. Base sections are a.e. measurable for restricted Lebesgue
measure, including Lebesgue measurable sections that are not Borel measurable.
No extra regularity in the base variable is imposed on
the derivatives: measurability of the directional derivative follows from
differentiating measurable energy slices, as in the dominated theorem. -/
def SobolevIntegrandRegularity {d m : ℕ} (Ω : Opens (Domain d))
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d) : Prop :=
  (∀ y : Vector m × Gradient m d,
    AEMeasurable (fun x => F x y.1 y.2) (domainMeasure Ω)) ∧
  HasContinuousFiberDerivative Ω F Fs FZ

/-- The actual Sobolev test pairing; both entries are canonical Lp representatives. -/
def sobolevWeakDensity {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d)
    (u w : W1p Ω m p) (x : Domain d) : ℝ :=
  ⟪Fs x (value Ω m p u x) (gradient Ω m p u x), value Ω m p w x⟫_ℝ +
  frobenius (FZ x (value Ω m p u x) (gradient Ω m p u x)) (gradient Ω m p w x)

/-- Finiteness at one prescribed-boundary competitor. -/
def FiniteReference {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (F : Domain d → Vector m → Gradient m d → ℝ) (u₀ : W1p Ω m p) : Prop :=
  ∃ v ∈ affineClass Ω m p u₀, ∃ r : ℝ, energy Ω m p F v = r

/-- The strong conclusion includes both global finiteness on the affine class
and integrability of every full Sobolev first variation. -/
def AllTestsConclusion {d m : ℕ} {Ω : Opens (Domain d)} {p : Exponent}
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d)
    (u₀ : W1p Ω m p) : Prop :=
  (∀ v ∈ affineClass Ω m p u₀, ∃ r : ℝ, energy Ω m p F v = r) ∧
  ∀ u ∈ affineClass Ω m p u₀,
    IsLocalMinOn (energy Ω m p F) (affineClass Ω m p u₀) u →
    ∀ w : W1pZero Ω m p,
      Integrable (sobolevWeakDensity Fs FZ u w) (domainMeasure Ω) ∧
      (∫ x, sobolevWeakDensity Fs FZ u w x ∂domainMeasure Ω) = 0

namespace SobolevExpected

/-- Theorem 8.14 for 1 < p < ∞, with the exact conjugate exponent. -/
def PowerGrowth : Prop :=
  ∀ {d m : ℕ} (_hd : 1 ≤ d) (_hm : 1 ≤ m) (Ω : Opens (Domain d))
    (_hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent),
    1 < p.real →
    ∀ (F : Domain d → Vector m → Gradient m d → ℝ)
      (Fs : Domain d → Vector m → Gradient m d → Vector m)
      (FZ : Domain d → Vector m → Gradient m d → Gradient m d),
    SobolevIntegrandRegularity Ω F Fs FZ →
    (∃ (b : Domain d → ℝ) (C : ℝ), 0 ≤ C ∧
      MemLp b (ENNReal.ofReal (p.real / (p.real - 1))) (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ s Z,
        ‖Fs x s Z‖ + ‖FZ x s Z‖ ≤ b x + C * (‖s‖ ^ (p.real - 1) + ‖Z‖ ^ (p.real - 1))) →
    ∀ u₀ : W1p Ω m p, FiniteReference F u₀ → AllTestsConclusion F Fs FZ u₀

/-- The endpoint has a common essentially bounded coefficient, with no
power-growth substitution at exponent zero. -/
def BoundedGrowth : Prop :=
  ∀ {d m : ℕ} (_hd : 1 ≤ d) (_hm : 1 ≤ m) (Ω : Opens (Domain d))
    (_hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent),
    p.real = 1 →
    ∀ (F : Domain d → Vector m → Gradient m d → ℝ)
      (Fs : Domain d → Vector m → Gradient m d → Vector m)
      (FZ : Domain d → Vector m → Gradient m d → Gradient m d),
    SobolevIntegrandRegularity Ω F Fs FZ →
    (∃ b : Domain d → ℝ, MemLp b ⊤ (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ s Z, ‖Fs x s Z‖ + ‖FZ x s Z‖ ≤ b x) →
    ∀ u₀ : W1p Ω m p, FiniteReference F u₀ → AllTestsConclusion F Fs FZ u₀

/-- The weaker p-growth statement has only smooth tests and assumes finiteness
at the minimizer. It asserts no finiteness at other competitors. -/
def SmoothTestsGrowth : Prop :=
  ∀ {d m : ℕ} (_hd : 1 ≤ d) (_hm : 1 ≤ m) (Ω : Opens (Domain d))
    (_hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (p : Exponent)
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d),
    SobolevIntegrandRegularity Ω F Fs FZ →
    (∃ (b : Domain d → ℝ) (C : ℝ), 0 ≤ C ∧ Integrable b (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ s Z,
        ‖Fs x s Z‖ + ‖FZ x s Z‖ ≤ b x + C * (‖s‖ ^ p.real + ‖Z‖ ^ p.real)) →
    ∀ (u₀ u : W1p Ω m p), u ∈ affineClass Ω m p u₀ →
    (∃ r : ℝ, energy Ω m p F u = r) →
    IsLocalMinOn (energy Ω m p F) (affineClass Ω m p u₀) u →
    ∀ φ : VectorTest Ω m,
      Integrable (weakDensity
        (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
        (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ) (domainMeasure Ω) ∧
      (∫ x, weakDensity
        (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
        (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ x ∂domainMeasure Ω) = 0

end SobolevExpected
end VariationalNotes.Sobolev.EulerLagrange
