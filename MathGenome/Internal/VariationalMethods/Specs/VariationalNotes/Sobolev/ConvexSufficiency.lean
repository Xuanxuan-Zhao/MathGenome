import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.SobolevEulerLagrange

/-! Independent statements of paper.tex, prop:weak-el-sufficient (4285–4304).
The stationary identity is imposed on the entire zero-boundary Sobolev space.
The two growth regimes retain exactly the all-tests hypotheses. In particular,
`SobolevIntegrandRegularity` uses a.e. measurable base sections for restricted
Lebesgue measure, and continuous first derivatives outside one common null set. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace VariationalNotes.Sobolev.ConvexSufficiencyExpected
open EulerLagrange

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
    (∀ᵐ x ∂domainMeasure Ω,
      ConvexOn ℝ univ (fun y : Vector m × Gradient m d => F x y.1 y.2)) →
    ∀ u₀ : W1p Ω m p, FiniteReference F u₀ →
    ∀ u ∈ affineClass Ω m p u₀,
    (∀ w : W1pZero Ω m p,
      (∫ x, sobolevWeakDensity Fs FZ u w x ∂domainMeasure Ω) = 0) →
    ∀ v ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F v

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
    (∀ᵐ x ∂domainMeasure Ω,
      ConvexOn ℝ univ (fun y : Vector m × Gradient m d => F x y.1 y.2)) →
    ∀ u₀ : W1p Ω m p, FiniteReference F u₀ →
    ∀ u ∈ affineClass Ω m p u₀,
    (∀ w : W1pZero Ω m p,
      (∫ x, sobolevWeakDensity Fs FZ u w x ∂domainMeasure Ω) = 0) →
    ∀ v ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F v

/-- Uniqueness for the gradient-only power energy, with its original exponent.
No finiteness hypothesis is needed: the Lp gradient makes this energy finite. -/
def PowerUniqueness : Prop :=
  ∀ {d m : ℕ}, 1 ≤ d → 1 ≤ m →
  ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  ∀ (p : Exponent), 1 < p.real → ∀ u₀ : W1p Ω m p,
  ∀ u ∈ affineClass Ω m p u₀,
    (∀ w ∈ affineClass Ω m p u₀,
      energy Ω m p (fun _ _ Z => ‖Z‖ ^ p.real) u ≤
        energy Ω m p (fun _ _ Z => ‖Z‖ ^ p.real) w) →
  ∀ v ∈ affineClass Ω m p u₀,
    (∀ w ∈ affineClass Ω m p u₀,
      energy Ω m p (fun _ _ Z => ‖Z‖ ^ p.real) v ≤
        energy Ω m p (fun _ _ Z => ‖Z‖ ^ p.real) w) → u = v

end VariationalNotes.Sobolev.ConvexSufficiencyExpected
