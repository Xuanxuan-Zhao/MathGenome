import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.ArclengthFactorization

/-! The length assertion of paper.tex:2364–2375 (D12.10.05).
Length is the supremum of Euclidean chord sums, with multiplicity from the
parametrization. The input is weak holomorphy; no derivative regularity or
chain-rule certificate is assumed. Compactness of the trace follows from AC
on the compact interval. The rectifiable statement uses an AC arc-length
factor, and makes no derivative assertion about the original parametrization.
-/
noncomputable section
open Set MeasureTheory
namespace Specs.D12Complex.Ch10.ConformalLength
open _root_.D12Complex _root_.D12Complex.Stieltjes

def ac_comp_type : Prop :=
  ∀ {Ω : Set ℂ} {f : ℂ → ℂ}, HolomorphicOn Ω f →
    ∀ {a b : ℝ}, a ≤ b → ∀ γ : ℝ → ℂ,
      AbsolutelyContinuousOnInterval γ a b → MapsTo γ (Icc a b) Ω →
      AbsolutelyContinuousOnInterval (f ∘ γ) a b

def ac_chain_rule_type : Prop :=
  ∀ {Ω : Set ℂ} {f : ℂ → ℂ}, HolomorphicOn Ω f →
    ∀ {a b : ℝ}, a ≤ b → ∀ γ : ℝ → ℂ,
      AbsolutelyContinuousOnInterval γ a b → MapsTo γ (Icc a b) Ω →
      ∀ᵐ t ∂volume.restrict (Icc a b),
        HasDerivAt (f ∘ γ) (deriv f (γ t) * deriv γ t) t

def ac_length_type : Prop :=
  ∀ {Ω : Set ℂ} {f : ℂ → ℂ}, HolomorphicOn Ω f →
    ∀ {a b : ℝ}, a ≤ b → ∀ γ : ℝ → ℂ,
      AbsolutelyContinuousOnInterval γ a b → MapsTo γ (Icc a b) Ω →
      AbsolutelyContinuousOnInterval (f ∘ γ) a b ∧
      totalVariation (f ∘ γ) a b < ⊤ ∧
      IntervalIntegrable (fun t => ‖deriv f (γ t)‖ * ‖deriv γ t‖) volume a b ∧
      (totalVariation (f ∘ γ) a b).toReal =
        ∫ t in a..b, ‖deriv f (γ t)‖ * ‖deriv γ t‖

def degenerate_length_type : Prop :=
  ∀ (f : ℂ → ℂ) (γ : ℝ → ℂ) (a : ℝ),
    totalVariation (f ∘ γ) a a = 0 ∧
    (∫ t in a..a, ‖deriv f (γ t)‖ * ‖deriv γ t‖) = 0

def rectifiable_length_type : Prop :=
  ∀ {Ω : Set ℂ} {f : ℂ → ℂ}, HolomorphicOn Ω f →
    ∀ γ : ComplexPath, Rectifiable γ → γ.trace ⊆ Ω →
    ∃ σ : ℝ → ℂ,
      LipschitzOnWith 1 σ (Icc 0 (polygonalLength γ).toReal) ∧
      (∀ t ∈ Icc γ.a γ.b,
        γ t = σ (Specs.D12Complex.Ch03.ArclengthFactorization.accumulated_value γ t)) ∧
      σ '' Icc 0 (polygonalLength γ).toReal = γ.trace ∧
      totalVariation σ 0 (polygonalLength γ).toReal = polygonalLength γ ∧
      AbsolutelyContinuousOnInterval (f ∘ σ) 0 (polygonalLength γ).toReal ∧
      totalVariation (f ∘ γ) γ.a γ.b < ⊤ ∧
      IntervalIntegrable (fun v => ‖deriv f (σ v)‖ * ‖deriv σ v‖)
        volume 0 (polygonalLength γ).toReal ∧
      (totalVariation (f ∘ γ) γ.a γ.b).toReal =
        ∫ v in (0 : ℝ)..(polygonalLength γ).toReal,
          ‖deriv f (σ v)‖ * ‖deriv σ v‖

end Specs.D12Complex.Ch10.ConformalLength
