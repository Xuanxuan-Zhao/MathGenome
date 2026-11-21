import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassSeries
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.CanonicalFactors

/-! D12.22.08: the regularized zeta series and the genus-two sigma product.
All sums and products use the unordered finite-subset filter. Values chosen at
poles are immaterial to the explicitly punctured meromorphic identities. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Specs.D12Complex.Ch22.ZetaSigmaConvergence

abbrev lattice := Specs.D12Complex.Ch22.LatticeGeometry.lattice
abbrev NonzeroLattice (ω₁ ω₂ : ℂ) := {l : lattice ω₁ ω₂ // l ≠ 0}
abbrev factor := Specs.D12Complex.Ch16.CanonicalFactors.factor_value
abbrev weierstrassP := Specs.D12Complex.Ch22.WeierstrassSeries.weierstrassP

def zetaTerm (l z : ℂ) : ℂ := 1 / (z - l) + 1 / l + z / l ^ 2

def zeta (ω₁ ω₂ z : ℂ) : ℂ :=
  1 / z + ∑' l : NonzeroLattice ω₁ ω₂, zetaTerm (l.1 : ℂ) z

def sigma (ω₁ ω₂ z : ℂ) : ℂ :=
  z * ∏' l : NonzeroLattice ω₁ ω₂, factor 2 (z / (l.1 : ℂ))

def zeta_type := ℂ → ℂ → ℂ → ℂ
def sigma_type := ℂ → ℂ → ℂ → ℂ

def factor_two_type : Prop := ∀ w : ℂ,
  factor 2 w = (1 - w) * Complex.exp (w + w ^ 2 / 2)

def zeta_normal_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ K : Set ℂ, IsCompact K → K ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ →
      ∃ u : NonzeroLattice ω₁ ω₂ → ℝ, Summable u ∧
        ∀ l, ∀ z ∈ K, ‖zetaTerm (l.1 : ℂ) z‖ ≤ u l

def zeta_locallyUniform_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    HasSumLocallyUniformlyOn
      (fun (l : NonzeroLattice ω₁ ω₂) z => zetaTerm (l.1 : ℂ) z)
      (fun z => ∑' l : NonzeroLattice ω₁ ω₂, zetaTerm (l.1 : ℂ) z)
      (lattice ω₁ ω₂ : Set ℂ)ᶜ

def sigma_normal_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ K : Set ℂ, IsCompact K →
      ∃ u : NonzeroLattice ω₁ ω₂ → ℝ, Summable u ∧
        ∀ l, ∀ z ∈ K, ‖factor 2 (z / (l.1 : ℂ)) - 1‖ ≤ u l

def sigma_locallyUniform_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    HasProdLocallyUniformly
      (fun (l : NonzeroLattice ω₁ ω₂) z => factor 2 (z / (l.1 : ℂ)))
      (fun z => ∏' l : NonzeroLattice ω₁ ω₂, factor 2 (z / (l.1 : ℂ)))

def zeta_holomorphic_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    _root_.D12Complex.HolomorphicOn (lattice ω₁ ω₂ : Set ℂ)ᶜ (zeta ω₁ ω₂)

def zeta_meromorphic_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → Meromorphic (zeta ω₁ ω₂)

/-- Exactly the residue-one simple principal part at every lattice point. -/
def zeta_principal_part_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ a ∈ lattice ω₁ ω₂, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      zeta ω₁ ω₂ =ᶠ[𝓝[≠] a] (fun z => 1 / (z - a) + g z)

def zeta_pole_order_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ a ∈ lattice ω₁ ω₂, meromorphicOrderAt (zeta ω₁ ω₂) a = -1

def sigma_entire_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    _root_.D12Complex.HolomorphicOn univ (sigma ω₁ ω₂)

def sigma_zero_iff_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ z : ℂ, sigma ω₁ ω₂ z = 0 ↔ z ∈ lattice ω₁ ω₂

def sigma_simple_zero_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ a ∈ lattice ω₁ ω₂, analyticOrderAt (sigma ω₁ ω₂) a = 1

def zeta_odd_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → Function.Odd (zeta ω₁ ω₂)

def sigma_odd_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → Function.Odd (sigma ω₁ ω₂)

def zeta_derivative_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ z ∉ lattice ω₁ ω₂, HasDerivAt (zeta ω₁ ω₂) (-weierstrassP ω₁ ω₂ z) z

def sigma_logDeriv_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ z ∉ lattice ω₁ ω₂, deriv (sigma ω₁ ω₂) z / sigma ω₁ ω₂ z = zeta ω₁ ω₂ z

/-- Equality of meromorphic germs also at lattice points. -/
def meromorphic_identities_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    Meromorphic (deriv (zeta ω₁ ω₂)) ∧
    Meromorphic (fun z => deriv (sigma ω₁ ω₂) z / sigma ω₁ ω₂ z) ∧
    ∀ a : ℂ,
      (deriv (zeta ω₁ ω₂) =ᶠ[𝓝[≠] a] (fun z => -weierstrassP ω₁ ω₂ z)) ∧
      ((fun z => deriv (sigma ω₁ ω₂) z / sigma ω₁ ω₂ z) =ᶠ[𝓝[≠] a] zeta ω₁ ω₂)

end Specs.D12Complex.Ch22.ZetaSigmaConvergence
