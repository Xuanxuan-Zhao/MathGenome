import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularExhaustion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.ChosenPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The selected power chart of the actual polar sector, including its vertex.
No harmonic estimate or analytic boundary regularity is assumed here. -/
noncomputable section
open Set Metric
namespace D12Complex.SectorPowerChart

def P (θ : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else Complex.I * principalPower ((Real.pi / θ : ℝ) : ℂ)
    (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * z)

def Q (θ : ℝ) (w : ℂ) : ℂ :=
  if w = 0 then 0 else Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
    principalPower ((θ / Real.pi : ℝ) : ℂ) (-Complex.I * w)

end D12Complex.SectorPowerChart
namespace Specs.D12Complex.Ch14.SectorPowerChart
open _root_.D12Complex _root_.D12Complex.SectorPowerChart

def P_type := ℝ → ℂ → ℂ
def P_value : P_type := fun θ z => if z = 0 then 0 else
  Complex.I * principalPower ((Real.pi / θ : ℝ) : ℂ)
    (Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * z)
def Q_type := ℝ → ℂ → ℂ
def Q_value : Q_type := fun θ w => if w = 0 then 0 else
  Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
    principalPower ((θ / Real.pi : ℝ) : ℂ) (-Complex.I * w)

def zero_values_type : Prop := ∀ θ : ℝ, P θ 0 = 0 ∧ Q θ 0 = 0

def power_norm_type : Prop := ∀ (θ : ℝ), 0 < θ → ∀ z : ℂ,
  ‖P θ z‖ = ‖z‖ ^ (Real.pi / θ)
def inverse_norm_type : Prop := ∀ (θ : ℝ), 0 < θ → ∀ w : ℂ,
  ‖Q θ w‖ = ‖w‖ ^ (θ / Real.pi)

def branch_domains_type : Prop := ∀ (θ : ℝ), 0 < θ → θ < 2 * Real.pi →
  (∀ z ∈ CircularExhaustion.sector θ,
    let v := Complex.exp (-((θ / 2 : ℝ) : ℂ) * Complex.I) * z
    v ∈ PrincipalSlitPlane ∧ -(θ / 2) < v.arg ∧ v.arg < θ / 2) ∧
  (∀ w : ℂ, 0 ≤ w.im → w ≠ 0 →
    -Complex.I * w ∈ PrincipalSlitPlane ∧
      -(Real.pi / 2) ≤ (-Complex.I * w).arg ∧
      (-Complex.I * w).arg ≤ Real.pi / 2)

/-- The inverse at diameter points includes the vertex. -/
def inverse_laws_type : Prop := ∀ (θ : ℝ), 0 < θ → θ < 2 * Real.pi →
  (∀ z ∈ CircularExhaustion.sector θ, Q θ (P θ z) = z) ∧
  (∀ w : ℂ, 0 ≤ w.im → P θ (Q θ w) = w)

def biholomorphic_type : Prop := ∀ (θ R : ℝ), 0 < θ → θ < 2 * Real.pi → 0 < R →
  BiholomorphicPair (CircularExhaustion.sector θ ∩ ball 0 R)
    {w : ℂ | ‖w‖ < R ^ (Real.pi / θ) ∧ 0 < w.im} (P θ) (Q θ)

def differential_norm_type : Prop := ∀ (θ : ℝ), 0 < θ → θ < 2 * Real.pi →
  ∀ z ∈ CircularExhaustion.sector θ,
    ‖fderiv ℝ (P θ) z‖ = (Real.pi / θ) * ‖z‖ ^ (Real.pi / θ - 1)

def inverse_continuous_type : Prop := ∀ (θ R : ℝ), 0 < θ → θ < 2 * Real.pi → 0 < R →
  ContinuousOn (Q θ) {w : ℂ | ‖w‖ < R ^ (Real.pi / θ) ∧ 0 ≤ w.im}

def inverse_mapsTo_closure_type : Prop := ∀ (θ R : ℝ),
  0 < θ → θ < 2 * Real.pi → 0 < R →
  MapsTo (Q θ) {w : ℂ | ‖w‖ < R ^ (Real.pi / θ) ∧ 0 ≤ w.im}
    (closure (CircularExhaustion.sector θ) ∩ ball 0 R)

def diameter_frontier_type : Prop := ∀ (θ R : ℝ),
  0 < θ → θ < 2 * Real.pi → 0 < R → ∀ w : ℂ,
  w.im = 0 → ‖w‖ < R ^ (Real.pi / θ) → Q θ w ∈ frontier (CircularExhaustion.sector θ)

end Specs.D12Complex.Ch14.SectorPowerChart
