import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.EulerProducts
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.Multiplicativity
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace P203.EulerProducts

open P203Specs P203Specs.EulerProducts Filter
open scoped Topology

theorem primeCutoff : P203Specs.EulerProducts.PrimeCutoff := by
  intro y p
  rw [primesAtMost, Nat.mem_primesBelow]
  constructor
  · rintro ⟨hbound, hp⟩
    refine ⟨hp, ?_⟩
    have hy : 0 ≤ y := by
      by_contra h
      have : ⌊y⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge h)
      rw [this] at hbound
      have := hp.two_le
      omega
    exact (Nat.le_floor_iff hy).mp (by omega)
  · rintro ⟨hp, hpy⟩
    exact ⟨by have := (Nat.le_floor_iff (le_trans (Nat.cast_nonneg p) hpy)).mpr hpy
              omega, hp⟩

theorem norm_dirichletTerm (f : PositiveFunction ℂ) (s : ℝ) (n : ℕ+) :
    ‖dirichletTerm f s n‖ = absoluteTerm f s n := by
  simp [dirichletTerm, absoluteTerm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

theorem absoluteConvergence : P203Specs.EulerProducts.AbsoluteConvergence := by
  intro f s h
  have hn : Summable (fun n => ‖dirichletTerm f s n‖) := by
    simpa only [norm_dirichletTerm] using h
  exact ⟨hn, hn.of_norm⟩

noncomputable def weighted (f : PositiveFunction ℂ) (s : ℝ) : ArithmeticFunction ℂ :=
  zeroExtend (dirichletTerm f s)

theorem weighted_apply (f : PositiveFunction ℂ) (s : ℝ) (n : ℕ+) :
    weighted f s n = dirichletTerm f s n := by
  exact Convolution.zeroExtend_apply _ _

theorem weighted_norm_summable (f : PositiveFunction ℂ) (s : ℝ)
    (h : Summable (absoluteTerm f s)) : Summable (fun n : ℕ => ‖weighted f s n‖) := by
  apply summable_pnat_iff_summable_nat.mp
  simpa only [weighted_apply, norm_dirichletTerm] using h

theorem tsum_weighted (f : PositiveFunction ℂ) (s : ℝ) :
    (∑' n : ℕ, weighted f s n) = ∑' n : ℕ+, dirichletTerm f s n := by
  rw [← tsum_pnat_eq_tsum_of_eq_zero ((weighted f s).map_zero)]
  apply tsum_congr
  exact weighted_apply f s

theorem weighted_prime_pow (f : PositiveFunction ℂ) (s : ℝ)
    {p : ℕ} (hp : p.Prime) (j : ℕ) : weighted f s (p ^ j) = localTerm f s p j := by
  unfold weighted
  rw [Convolution.zeroExtend_apply_pos _ (pow_pos hp.pos j)]
  unfold dirichletTerm localTerm
  rw [Convolution.zeroExtend_apply_pos _ (pow_pos hp.pos j)]
  change f ⟨p ^ j, pow_pos hp.pos j⟩ / (((p ^ j : ℕ) : ℝ) ^ s : ℝ) =
    f ⟨p ^ j, pow_pos hp.pos j⟩ / ((p : ℝ) ^ ((j : ℝ) * s) : ℝ)
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]

theorem localAbsoluteConvergence : P203Specs.EulerProducts.LocalAbsoluteConvergence := by
  intro f s h p hp
  have H := (weighted_norm_summable f s h).comp_injective (Nat.pow_right_injective hp.one_lt)
  change Summable (fun j : ℕ => ‖weighted f s (p ^ j)‖) at H
  have Hlocal : Summable (fun j => ‖localTerm f s p j‖) := by
    simpa only [weighted_prime_pow f s hp] using H
  exact ⟨Hlocal, Hlocal.of_norm⟩

/-- Multiplying by n^(-s) preserves multiplicativity for every real s. -/
theorem weighted_multiplicative (f : PositiveFunction ℂ) (s : ℝ)
    (hf : P203Specs.Multiplicativity.IsMultiplicative f) :
    (weighted f s).IsMultiplicative := by
  apply (Multiplicativity.multiplicativityBridge ℂ _).mp
  constructor
  · simp [dirichletTerm, hf.1]
  · intro a b hab
    simp only [dirichletTerm, hf.2 a b hab, PNat.mul_coe, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg (a : ℕ)) (Nat.cast_nonneg (b : ℕ)),
      Complex.ofReal_mul, mul_div_mul_comm]

/-- Change from the library's strict natural cutoff to the source's real inclusive cutoff. -/
theorem tendsto_real_cutoff {R : Type*} [CommMonoid R] [TopologicalSpace R]
    (g : ℕ → R) (a : R)
    (h : Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, g p) atTop (𝓝 a)) :
    Tendsto (fun y : ℝ => ∏ p ∈ primesAtMost y, g p) atTop (𝓝 a) := by
  exact h.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)

theorem eulerProduct : P203Specs.EulerProducts.EulerProduct := by
  intro f s hf h
  have H := tendsto_real_cutoff (fun p => ∑' j, weighted f s (p ^ j))
    (∑' n, weighted f s n)
    ((weighted_multiplicative f s hf).eulerProduct (weighted_norm_summable f s h))
  rw [tsum_weighted] at H
  convert H using 1
  funext y
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro j
  exact (weighted_prime_pow f s ((primeCutoff y p).mp hp).1 j).symm

theorem zetaSeriesConvergence : P203Specs.EulerProducts.ZetaSeriesConvergence := by
  intro s hs
  exact (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).comp_injective
    PNat.coe_injective

/-- For s>1 the real zeta summand is a completely multiplicative map, including at zero. -/
noncomputable def zetaSummand (s : ℝ) (hs : 1 < s) : ℕ →*₀ ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_zero' := by simp [Real.zero_rpow (by linarith : -s ≠ 0)]
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem zetaEulerProduct : P203Specs.EulerProducts.ZetaEulerProduct := by
  intro s hs
  have hn : Summable (fun n : ℕ => ‖zetaSummand s hs n‖) := by
    simpa only [zetaSummand, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      using (Real.summable_nat_rpow.mpr (by linarith : -s < -1))
  have H := EulerProduct.eulerProduct_completely_multiplicative hn
  have ht : (∑' n : ℕ, zetaSummand s hs n) =
      ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (-s) := by
    rw [← tsum_pnat_eq_tsum_of_eq_zero (zetaSummand s hs).map_zero]
    rfl
  rw [ht] at H
  exact tendsto_real_cutoff _ _ H

end P203.EulerProducts
