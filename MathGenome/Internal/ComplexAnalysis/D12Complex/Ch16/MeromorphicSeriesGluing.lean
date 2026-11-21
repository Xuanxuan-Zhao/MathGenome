import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.MeromorphicSeriesGluing
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicLimits
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.MeromorphicSeriesGluing
open D12Complex.Ch15

/-- Interior nesting in a compatible exhaustion implies monotonicity. -/
theorem exhaustion_monotone {Ω : Set ℂ} {K : ℕ → Set ℂ}
    (hK : IsCompatibleExhaustion Ω K) : Monotone K :=
  monotone_nat_of_le_succ fun n => (hK.2.1 n).trans interior_subset

/-- Each point is in the interior of a stage, even if some stages are empty. -/
theorem exists_mem_interior_stage {Ω : Set ℂ} {K : ℕ → Set ℂ}
    (hK : IsCompatibleExhaustion Ω K) {z : ℂ} (hz : z ∈ Ω) :
    ∃ m, z ∈ interior (K m) := by
  obtain ⟨N, hN⟩ := hK.2.2 {z} (isCompact_singleton) (singleton_subset_iff.mpr hz)
  exact ⟨N + 1, hK.2.1 N (hN N le_rfl (mem_singleton z))⟩

/-- The eventually bounded series converges uniformly on each compact subset.
No continuity of the finitely many early terms is needed. -/
theorem locallyUniform_sum {Ω : Set ℂ} {K : ℕ → Set ℂ}
    {t : ℕ → ℂ → ℂ} {b : ℕ → ℝ} (hΩ : IsOpen Ω)
    (hK : IsCompatibleExhaustion Ω K) (hb : Summable b)
    (hbound : ∀ n z, z ∈ K n → ‖t n z‖ ≤ b n) :
    TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, t n z)
      (fun z => ∑' n, t n z) atTop Ω := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mpr
  intro S hSΩ hS
  obtain ⟨N, hN⟩ := hK.2.2 S hS hSΩ
  apply tendstoUniformlyOn_tsum_nat_eventually hb
  filter_upwards [eventually_ge_atTop N] with n hn z hz
  exact hbound n z (hN n hn hz)

/-- A tail starting at `m` is a uniformly convergent series of holomorphic
functions throughout the interior of stage `m`. -/
theorem holomorphic_tsum_tail {Ω : Set ℂ} {K : ℕ → Set ℂ}
    {t : ℕ → ℂ → ℂ} {b : ℕ → ℝ} (hK : IsCompatibleExhaustion Ω K)
    (hb : Summable b) (ht : ∀ n, HolomorphicOn (interior (K n)) (t n))
    (hbound : ∀ n z, z ∈ K n → ‖t n z‖ ≤ b n) (m : ℕ) :
    HolomorphicOn (interior (K m)) (fun z => ∑' n, t (n + m) z) := by
  have hmono := exhaustion_monotone hK
  have hbshift : Summable (fun n => b (n + m)) := (summable_nat_add_iff m).mpr hb
  have hlim := tendstoUniformlyOn_tsum_nat hbshift
    (s := interior (K m)) (f := fun n z => t (n + m) z)
    (fun n z hz => hbound (n + m) z (hmono (Nat.le_add_left m n) (interior_subset hz)))
  apply HolomorphicLimits.holomorphic_limit (interior (K m))
    (fun N z => ∑ n ∈ Finset.range N, t (n + m) z)
    (fun z => ∑' n, t (n + m) z) isOpen_interior _ hlim.tendstoLocallyUniformlyOn
  intro N
  refine ⟨isOpen_interior, fun z hz => ?_⟩
  exact DifferentiableAt.fun_sum fun n _ =>
    (ht (n + m)).2 z (interior_mono (hmono (Nat.le_add_left m n)) hz)

/-- Full gluing theorem for the normally controlled meromorphic series. -/
theorem meromorphic_series_gluing :
    Specs.D12Complex.Ch16.MeromorphicSeriesGluing.meromorphic_series_gluing_type := by
  intro Ω K t b hΩ _hzero hK hb _hbnonneg hmero hhol hbound
  have hsummable : ∀ z ∈ Ω, Summable (fun n => t n z) := by
    intro z hz
    obtain ⟨N, hN⟩ := hK.2.2 {z} isCompact_singleton (singleton_subset_iff.mpr hz)
    apply hb.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hbound n z (hN n hn (mem_singleton z))
  have htail : ∀ m, HolomorphicOn (interior (K m))
      (fun z => (∑' n, t n z) - ∑ n ∈ Finset.range m, t n z) := by
    intro m
    have ht := holomorphic_tsum_tail hK hb hhol hbound m
    refine ⟨isOpen_interior, fun z hz => (ht.2 z hz).congr_of_eventuallyEq ?_⟩
    filter_upwards [isOpen_interior.mem_nhds hz] with w hw
    have hwΩ := (hK.1 m).2.1 (interior_subset hw)
    exact sub_eq_iff_eq_add.mpr
      (((hsummable w hwΩ).sum_add_tsum_nat_add m).symm.trans (add_comm _ _))
  refine ⟨fun z => ∑' n, t n z, ?_, locallyUniform_sum hΩ hK hb hbound, htail⟩
  intro z hz
  obtain ⟨m, hm⟩ := exists_mem_interior_stage hK hz
  have hhead : MeromorphicAt (fun w => ∑ n ∈ Finset.range m, t n w) z :=
    MeromorphicAt.fun_sum fun n _ => hmero n z hz
  have hrem : AnalyticAt ℂ
      (fun w => (∑' n, t n w) - ∑ n ∈ Finset.range m, t n w) z :=
    (DifferentiableOn.analyticOnNhd (fun w hw => ((htail m).2 w hw).differentiableWithinAt)
      isOpen_interior) z hm
  convert hhead.add hrem.meromorphicAt using 1
  ext w
  simp only [Pi.add_apply, sub_eq_add_neg, add_left_comm, add_neg_cancel, add_zero]

end D12Complex.MeromorphicSeriesGluing
