import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.ChosenPowers
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statements for paper.tex:1561–1608. The argument is principal;
the slit-plane condition excludes both zero and the negative ray, including at
α = 1/2. Boundary conditions concern interior limits only. -/

open Set Filter
open scoped Topology

noncomputable section

namespace D12Complex.SectorPhragmenLindelof.Definitions

def sector (α : ℝ) : Set ℂ :=
  {z | z ∈ Complex.slitPlane ∧ |z.arg| < Real.pi / (2 * α)}

def affineSector (α : ℝ) (a b : ℂ) : Set ℂ :=
  (fun z => b + a * z) '' sector α

def criticalExample (α : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (D12Complex.principalPower (α : ℂ) z)

end D12Complex.SectorPhragmenLindelof.Definitions

namespace Specs.D12Complex.Ch06.SectorPhragmenLindelof
open _root_.D12Complex _root_.D12Complex.SectorPhragmenLindelof.Definitions

def sector_type := ℝ → Set ℂ
def sector_value : sector_type :=
  fun α => {z | z ∈ Complex.slitPlane ∧ |z.arg| < Real.pi / (2 * α)}

def affineSector_type := ℝ → ℂ → ℂ → Set ℂ
def affineSector_value : affineSector_type :=
  fun α a b => (fun z => b + a * z) '' sector α

def criticalExample_type := ℝ → ℂ → ℂ
def criticalExample_value : criticalExample_type :=
  fun α z => Complex.exp (principalPower (α : ℂ) z)

def sector_polar_type : Prop :=
  ∀ (α : ℝ), 1 / 2 ≤ α → ∀ z : ℂ,
    z ∈ sector α ↔ ∃ (r θ : ℝ), 0 < r ∧ |θ| < Real.pi / (2 * α) ∧
      -Real.pi < θ ∧ θ < Real.pi ∧ z = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

def norm_le_type : Prop :=
  ∀ (α : ℝ) (f : ℂ → ℂ) (M A B β R : ℝ),
    1 / 2 ≤ α → HolomorphicOn (sector α) f → 0 ≤ M →
    (∀ ξ ∈ frontier (sector α), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[sector α] ξ, ‖f z‖ < M + ε) →
    0 < A → 0 ≤ B → 0 ≤ β → β < α →
    (∀ z ∈ sector α, R ≤ ‖z‖ → ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ β)) →
    ∀ z ∈ sector α, ‖f z‖ ≤ M

/-- The growth condition in the original sector coordinate is explicit. -/
def norm_le_affine_type : Prop :=
  ∀ (α : ℝ) (a b : ℂ) (f : ℂ → ℂ) (M A B β R : ℝ),
    1 / 2 ≤ α → a ≠ 0 → HolomorphicOn (affineSector α a b) f → 0 ≤ M →
    (∀ ξ ∈ frontier (affineSector α a b), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ w in 𝓝[affineSector α a b] ξ, ‖f w‖ < M + ε) →
    0 < A → 0 ≤ B → 0 ≤ β → β < α →
    (∀ w ∈ affineSector α a b, R ≤ ‖(w - b) / a‖ →
      ‖f w‖ ≤ A * Real.exp (B * ‖(w - b) / a‖ ^ β)) →
    ∀ w ∈ affineSector α a b, ‖f w‖ ≤ M

def sharpness_type : Prop :=
  ∀ (α : ℝ), 1 / 2 ≤ α →
    HolomorphicOn (sector α) (criticalExample α) ∧
    (∀ ξ ∈ frontier (sector α),
      Tendsto (fun z => ‖criticalExample α z‖) (𝓝[sector α] ξ) (𝓝 1)) ∧
    (∀ z ∈ sector α, ‖criticalExample α z‖ ≤ Real.exp (‖z‖ ^ α)) ∧
    (∀ r : ℝ, 0 < r → (r : ℂ) ∈ sector α) ∧
    Tendsto (fun r : ℝ => ‖criticalExample α (r : ℂ)‖) atTop atTop

end Specs.D12Complex.Ch06.SectorPhragmenLindelof
