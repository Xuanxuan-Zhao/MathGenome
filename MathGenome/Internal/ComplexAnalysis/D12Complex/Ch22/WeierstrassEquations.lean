import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassEquations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassSeries
import Mathlib.Tactic.LinearCombination

/-! The differential equations of the canonical regularized Weierstrass series.
The first equation is the library relation for precisely the same period pair.
For the second, differentiating gives a product with ℘'. Its order at zero is
-3, so its meromorphic germ is nonzero everywhere on the connected plane.
Cancellation on punctured neighborhoods and continuity handle critical points.
The final germ identities also include the lattice poles. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Ch22.WeierstrassEquations

open WeierstrassSeries (periodPair lattice weierstrassP)

abbrev g₂ := Specs.D12Complex.Ch22.WeierstrassEquations.g₂
abbrev g₃ := Specs.D12Complex.Ch22.WeierstrassEquations.g₃

/-- The zero summand contributes zero, so the library Eisenstein sum is
exactly the sum over the nonzero vectors of the given lattice. -/
theorem eisenstein_sum_eq {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) {n : ℕ} (hn : 2 < n) :
    (periodPair h₁ h₂).G n =
      ∑' l : {l : lattice ω₁ ω₂ // l ≠ 0}, 1 / (l.1 : ℂ) ^ n := by
  classical
  let L := periodPair h₁ h₂
  have hs := (L.hasSum_sumInvPow 0 hn).summable
  simp only [sub_zero] at hs
  have h := hs.sum_add_tsum_compl (s := ({0} : Finset L.lattice))
  have he : (({0} : Finset L.lattice) : Set L.lattice)ᶜ = {l | l ≠ 0} := by
    ext l; simp
  rw [he] at h
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_trans (by decide : 0 < 2) hn)
  simp only [Finset.sum_singleton, Submodule.coe_zero, zero_pow hn0, inv_zero, zero_add] at h
  change (∑' l : L.lattice, ((l : ℂ) ^ n)⁻¹) = _
  convert h.symm using 1
  simp only [one_div]
  rfl

theorem periodPair_g₂ {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) : (periodPair h₁ h₂).g₂ = g₂ ω₁ ω₂ := by
  rw [PeriodPair.g₂, eisenstein_sum_eq h₁ h₂ (by decide)]
  rfl

theorem periodPair_g₃ {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) : (periodPair h₁ h₂).g₃ = g₃ ω₁ ω₂ := by
  rw [PeriodPair.g₃, eisenstein_sum_eq h₁ h₂ (by decide)]
  rfl

theorem absolute_convergence :
    Specs.D12Complex.Ch22.WeierstrassEquations.absolute_convergence_type := by
  intro ω₁ ω₂ h₁ h₂
  constructor
  · have h := LatticeGeometry.power_summable ω₁ ω₂ h₁ h₂ 4 (by norm_num)
    simpa [one_div, norm_inv, norm_pow, Real.rpow_neg, Real.rpow_ofNat] using h
  · have h := LatticeGeometry.power_summable ω₁ ω₂ h₁ h₂ 6 (by norm_num)
    simpa [one_div, norm_inv, norm_pow, Real.rpow_neg, Real.rpow_ofNat] using h

theorem meromorphic_derivatives :
    Specs.D12Complex.Ch22.WeierstrassEquations.meromorphic_derivatives_type := by
  intro ω₁ ω₂ h₁ h₂
  have h := (WeierstrassSeries.meromorphic ω₁ ω₂ h₁ h₂).deriv
  exact ⟨h, h.deriv⟩

theorem first_equation : Specs.D12Complex.Ch22.WeierstrassEquations.first_equation_type := by
  intro ω₁ ω₂ h₁ h₂ z hz
  have h := (periodPair h₁ h₂).derivWeierstrassP_sq z hz
  rw [← (periodPair h₁ h₂).deriv_weierstrassP,
    WeierstrassSeries.periodPair_weierstrassP, periodPair_g₂, periodPair_g₃] at h
  exact h

/-- Differentiate the first equation before cancellation. This identity also
holds at the critical points off the lattice. -/
theorem differentiated_equation (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv L.weierstrassP z *
      (deriv (deriv L.weierstrassP) z - 6 * L.weierstrassP z ^ 2 + L.g₂ / 2) = 0 := by
  have ha := L.analyticOnNhd_weierstrassP z hz
  have hp := ha.differentiableAt.hasDerivAt
  have hq := ha.deriv.differentiableAt.hasDerivAt
  have he : (fun w => deriv L.weierstrassP w ^ 2) =ᶠ[𝓝 z]
      (fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    simpa only [L.deriv_weierstrassP] using L.derivWeierstrassP_sq w hw
  have hd := (hq.pow 2).congr_of_eventuallyEq he.symm
  have hr := ((hp.pow 3).const_mul 4 |>.sub (hp.const_mul L.g₂)).sub_const L.g₃
  have hd' := hd.unique hr
  dsimp at hd'
  linear_combination hd' / 2

/-- A pole of order two gives a derivative pole of order three. The identity
principle for meromorphic orders then excludes the zero germ at every point. -/
theorem derivative_eventually_ne_zero (L : PeriodPair) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, deriv L.weierstrassP z ≠ 0 := by
  have ho : meromorphicOrderAt (deriv L.weierstrassP) 0 = ((-3 : ℤ) : WithTop ℤ) := by
    simpa using meromorphicOrderAt_deriv_eq_sub_one
      (f := L.weierstrassP) (n := -2) (by norm_num) (L.order_weierstrassP 0 (zero_mem _))
  have hm := L.meromorphic_weierstrassP.deriv
  have hfin := (hm.meromorphicOn (s := Set.univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ 0) (mem_univ a) (by rw [ho]; simp)
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm a)).mp hfin

/-- The second equation holds at critical points too, by continuity. -/
theorem second_equation_periodPair (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (deriv L.weierstrassP) z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have ha := L.analyticOnNhd_weierstrassP z hz
  have he : deriv (deriv L.weierstrassP) =ᶠ[𝓝[≠] z]
      (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) := by
    filter_upwards [derivative_eventually_ne_zero L z,
      eventually_nhdsWithin_of_eventually_nhds
        (L.isClosed_lattice.isOpen_compl.mem_nhds hz)] with w hw hwL
    have h := (mul_eq_zero.mp (differentiated_equation L hwL)).resolve_left hw
    linear_combination h
  exact tendsto_nhds_unique
    (ha.deriv.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (((ha.continuousAt.pow 2).const_mul 6 |>.sub continuousAt_const).tendsto.mono_left
      nhdsWithin_le_nhds |>.congr' he.symm)

theorem second_equation : Specs.D12Complex.Ch22.WeierstrassEquations.second_equation_type := by
  intro ω₁ ω₂ h₁ h₂ z hz
  have h := second_equation_periodPair (periodPair h₁ h₂) hz
  rw [WeierstrassSeries.periodPair_weierstrassP, periodPair_g₂] at h
  exact h

/-- Every punctured neighborhood can be shrunk to miss all lattice points. -/
theorem eventually_notMem_lattice (L : PeriodPair) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, z ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (L.compl_lattice_sdiff_singleton_mem_nhds a)] with z hz hza
  simp_all

theorem first_equation_germ :
    Specs.D12Complex.Ch22.WeierstrassEquations.first_equation_germ_type := by
  intro ω₁ ω₂ h₁ h₂ a
  filter_upwards [eventually_notMem_lattice (periodPair h₁ h₂) a] with z hz
  exact first_equation ω₁ ω₂ h₁ h₂ z hz

theorem second_equation_germ :
    Specs.D12Complex.Ch22.WeierstrassEquations.second_equation_germ_type := by
  intro ω₁ ω₂ h₁ h₂ a
  filter_upwards [eventually_notMem_lattice (periodPair h₁ h₂) a] with z hz
  exact second_equation ω₁ ω₂ h₁ h₂ z hz

end D12Complex.Ch22.WeierstrassEquations
