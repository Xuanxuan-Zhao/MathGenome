import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassPeriods
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassSeries

/-! Parity and the complete period lattice of the canonical regularized ℘.
The `PeriodPair` used below has exactly the given generators and integer span.
Mathlib proves its parity by reindexing the convergent regularized sum, and
its derivative's periodicity by translation of the convergent inverse-cube sum.
Its proof of ℘ periodicity then uses equality of derivatives and parity at
the nonlattice half-generators. We use these results for the same series,
and state the conclusions as germ equalities, including at poles.

For the converse, a germ period identifies the order at τ with the order at
zero, namely -2. If τ were outside the lattice, ℘ would be analytic there
and would have nonnegative order, a contradiction. -/
noncomputable section
open Filter
open scoped Topology

namespace D12Complex.Ch22.WeierstrassPeriods

open WeierstrassSeries (periodPair)

theorem even : Specs.D12Complex.Ch22.WeierstrassPeriods.even_type := by
  intro ω₁ ω₂ h₁ h₂ a
  exact Filter.Eventually.of_forall (periodPair h₁ h₂).weierstrassP_neg

theorem derivative_odd : Specs.D12Complex.Ch22.WeierstrassPeriods.derivative_odd_type := by
  intro ω₁ ω₂ h₁ h₂ a
  let L := periodPair h₁ h₂
  change (fun z => deriv L.weierstrassP (-z)) =ᶠ[𝓝[≠] a]
    (fun z => -deriv L.weierstrassP z)
  rw [L.deriv_weierstrassP]
  exact Filter.Eventually.of_forall L.derivWeierstrassP_neg

theorem periodic : Specs.D12Complex.Ch22.WeierstrassPeriods.periodic_type := by
  intro ω₁ ω₂ h₁ h₂ τ hτ a
  exact Filter.Eventually.of_forall (fun z =>
    (periodPair h₁ h₂).weierstrassP_add_coe z ⟨τ, hτ⟩)

theorem derivative_periodic :
    Specs.D12Complex.Ch22.WeierstrassPeriods.derivative_periodic_type := by
  intro ω₁ ω₂ h₁ h₂ τ hτ a
  let L := periodPair h₁ h₂
  change (fun z => deriv L.weierstrassP (z + τ)) =ᶠ[𝓝[≠] a] deriv L.weierstrassP
  rw [L.deriv_weierstrassP]
  exact Filter.Eventually.of_forall (fun z => L.derivWeierstrassP_add_coe z ⟨τ, hτ⟩)

theorem period_iff : Specs.D12Complex.Ch22.WeierstrassPeriods.period_iff_type := by
  intro ω₁ ω₂ h₁ h₂ τ
  constructor
  · intro hper
    let L := periodPair h₁ h₂
    have ho := meromorphicOrderAt_congr (hper 0)
    change meromorphicOrderAt (L.weierstrassP ∘ (· + τ)) 0 =
      meromorphicOrderAt L.weierstrassP 0 at ho
    rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add,
      L.order_weierstrassP 0 (zero_mem _)] at ho
    by_contra hτ
    have ha := (L.analyticOnNhd_weierstrassP τ hτ).meromorphicOrderAt_nonneg
    rw [ho] at ha
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-2 : ℤ) : WithTop ℤ) at ha
    have : (0 : ℤ) ≤ -2 := WithTop.coe_le_coe.mp ha
    norm_num at this
  · intro hτ
    exact periodic ω₁ ω₂ h₁ h₂ τ hτ

end D12Complex.Ch22.WeierstrassPeriods
