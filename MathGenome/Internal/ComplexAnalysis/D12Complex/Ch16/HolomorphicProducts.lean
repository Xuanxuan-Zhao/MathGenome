import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.HolomorphicProducts
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

noncomputable section
open Set Metric Filter
open scoped Topology
namespace D12Complex.HolomorphicProducts

abbrev NormalProductCondition :=
  Specs.D12Complex.Ch16.HolomorphicProducts.NormalProductCondition_value

lemma norm_sub_one_le_sup {Ω K : Set ℂ} {u : ℕ → ℂ → ℂ}
    (hu : ∀ n, HolomorphicOn Ω (u n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (n : ℕ) {z : ℂ} (hz : z ∈ K) :
    ‖u n z - 1‖ ≤ sSup ((fun w => ‖u n w - 1‖) '' K) := by
  have hc : ContinuousOn (fun w => ‖u n w - 1‖) K :=
    fun w hw => ((hu n).2 w (hKΩ hw)).continuousAt.sub continuousAt_const |>.norm
      |>.continuousWithinAt
  exact le_csSup (hK.bddAbove_image hc) (mem_image_of_mem _ hz)

lemma hasProdUniformlyOn_compact {Ω : Set ℂ} {u : ℕ → ℂ → ℂ}
    (hu : ∀ n, HolomorphicOn Ω (u n)) (hn : NormalProductCondition Ω u)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    HasProdUniformlyOn u (fun z => ∏' k, u k z) K := by
  have h := Summable.hasProdUniformlyOn_nat_one_add hK (hn K hK hKΩ)
    (f := fun n z => u n z - 1)
    (Eventually.of_forall fun n z hz => norm_sub_one_le_sup hu hK hKΩ n hz)
    (fun n z hz => (((hu n).2 z (hKΩ hz)).continuousAt.sub continuousAt_const).continuousWithinAt)
  simpa only [add_sub_cancel] using h

lemma hasProdLocallyUniformlyOn_of_normal {Ω : Set ℂ} {u : ℕ → ℂ → ℂ}
    (hΩ : IsOpen Ω) (hu : ∀ n, HolomorphicOn Ω (u n))
    (hn : NormalProductCondition Ω u) :
    HasProdLocallyUniformlyOn u (fun z => ∏' k, u k z) Ω := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hΩ
  intro K hKΩ hK
  exact hasProdUniformlyOn_compact hu hn hK hKΩ

lemma holomorphic_partial_product {Ω : Set ℂ} {u : ℕ → ℂ → ℂ}
    (hΩ : IsOpen Ω) (hu : ∀ n, HolomorphicOn Ω (u n)) (n : ℕ) :
    HolomorphicOn Ω (fun z => ∏ k ∈ Finset.range n, u k z) := by
  refine ⟨hΩ, fun z hz => ?_⟩
  exact DifferentiableAt.fun_finsetProd (fun k _ => (hu k).2 z hz)

theorem holomorphic_product_limit :
    Specs.D12Complex.Ch16.HolomorphicProducts.holomorphic_product_limit_type := by
  intro Ω u hΩ hu hn
  have h := (hasProdLocallyUniformlyOn_of_normal hΩ hu hn).tendstoLocallyUniformlyOn_finsetRange
  exact ⟨h, HolomorphicLimits.holomorphic_limit Ω _ _ hΩ
    (holomorphic_partial_product hΩ hu) h⟩

lemma normal_shift {Ω : Set ℂ} {u : ℕ → ℂ → ℂ}
    (hn : NormalProductCondition Ω u) (N : ℕ) :
    NormalProductCondition Ω (fun k => u (k + N)) := by
  intro K hK hKΩ
  exact (summable_nat_add_iff N).mpr (hn K hK hKΩ)

theorem holomorphic_tail_limit :
    Specs.D12Complex.Ch16.HolomorphicProducts.holomorphic_tail_limit_type := by
  intro Ω u hΩ hu hn N
  exact holomorphic_product_limit Ω (fun k => u (k + N)) hΩ
    (fun k => hu (k + N)) (normal_shift hn N)

lemma summable_norm_at {Ω : Set ℂ} {u : ℕ → ℂ → ℂ}
    (hn : NormalProductCondition Ω u) {z : ℂ} (hz : z ∈ Ω) :
    Summable (fun n => ‖u n z - 1‖) := by
  simpa only [Set.image_singleton, csSup_singleton] using
    hn {z} isCompact_singleton (singleton_subset_iff.mpr hz)

/-- Absolute summability of deviations preserves nonvanishing when every factor is nonzero. -/
lemma tprod_ne_zero_of_all_ne_zero {u : ℕ → ℂ} (hu : ∀ n, u n ≠ 0)
    (hn : Summable (fun n => ‖u n - 1‖)) : (∏' n, u n) ≠ 0 := by
  simpa only [add_sub_cancel] using
    tprod_one_add_ne_zero_of_summable
      (f := fun n => u n - 1) (by simpa only [add_sub_cancel] using hu) hn

theorem tail_nonvanishing_on_compact :
    Specs.D12Complex.Ch16.HolomorphicProducts.tail_nonvanishing_on_compact_type := by
  intro Ω u hΩ hu hn K hK hKΩ
  have he : ∀ᶠ n in atTop,
      sSup ((fun z => ‖u n z - 1‖) '' K) < (1 / 2 : ℝ) :=
    (hn K hK hKΩ).tendsto_atTop_zero.eventually
      (Iio_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  have hne : ∀ n, N ≤ n → ∀ z ∈ K, u n z ≠ 0 := by
    intro n hn z hz heq
    have hlt := (norm_sub_one_le_sup hu hK hKΩ n hz).trans_lt (hN n hn)
    norm_num [heq] at hlt
  refine ⟨N, fun M hM z hz => ⟨fun n hn => hne n (hM.trans hn) z hz, ?_⟩⟩
  exact tprod_ne_zero_of_all_ne_zero (fun k => hne (k + M) (by omega) z hz)
    ((summable_nat_add_iff M).mpr (summable_norm_at hn (hKΩ hz)))

theorem product_prefix_tail :
    Specs.D12Complex.Ch16.HolomorphicProducts.product_prefix_tail_type := by
  intro Ω u hΩ hu hn N z hz
  have h := hasProdLocallyUniformlyOn_of_normal hΩ (fun k => hu (k + N))
    (normal_shift hn N)
  exact (h.hasProd hz).multipliable.prod_mul_tprod_nat_mul'.symm

lemma analyticAt_of_holomorphic {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) {a : ℂ} (ha : a ∈ Ω) : AnalyticAt ℂ f a :=
  (LocalZeroFactorization.holomorphicNear_iff_analyticAt f a).mp ⟨Ω, ha, hf⟩

lemma order_partial_product (u : ℕ → ℂ → ℂ) (a : ℂ)
    (hu : ∀ n, AnalyticAt ℂ (u n) a) (N : ℕ) :
    analyticOrderAt (fun z => ∏ k ∈ Finset.range N, u k z) a =
      ∑ k ∈ Finset.range N, analyticOrderAt (u k) a := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty]
      exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero
  | succ N ih =>
      have heq : (fun z => ∏ k ∈ Finset.range (N + 1), u k z) =
          (fun z => ∏ k ∈ Finset.range N, u k z) * u N := by
        funext z
        exact Finset.prod_range_succ _ _
      rw [heq, analyticOrderAt_mul
        ((Finset.range N).analyticAt_fun_prod (fun k _ => hu k)) (hu N),
        ih, Finset.sum_range_succ]

theorem product_order_on_component :
    Specs.D12Complex.Ch16.HolomorphicProducts.product_order_on_component_type := by
  intro Ω u hΩ hu hn a ha hcomponent
  have hau : ∀ n, AnalyticAt ℂ (u n) a :=
    fun n => analyticAt_of_holomorphic (hu n) ha
  have hfinite : ∀ n, analyticOrderAt (u n) a ≠ ⊤ := by
    intro n htop
    have han : AnalyticOnNhd ℂ (u n) (connectedComponentIn Ω a) :=
      fun z hz => analyticAt_of_holomorphic (hu n) (connectedComponentIn_subset Ω a hz)
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_connectedComponentIn (mem_connectedComponentIn ha)
      (analyticOrderAt_eq_top.mp htop)
    obtain ⟨z, hz, hzne⟩ := hcomponent n
    exact hzne (hzero hz)
  obtain ⟨N, hN⟩ := tail_nonvanishing_on_compact Ω u hΩ hu hn {a}
    isCompact_singleton (singleton_subset_iff.mpr ha)
  have htail := hN N le_rfl a (mem_singleton a)
  have hta := analyticAt_of_holomorphic
    (holomorphic_tail_limit Ω u hΩ hu hn N).2 ha
  have htailorder : analyticOrderAt (fun z => ∏' k, u (k + N) z) a = 0 :=
    hta.analyticOrderAt_eq_zero.mpr htail.2
  have heq : (fun z => ∏' k, u k z) =ᶠ[𝓝 a]
      (fun z => (∏ k ∈ Finset.range N, u k z) * (∏' k, u (k + N) z)) :=
    eventually_of_mem (hΩ.mem_nhds ha) (fun z hz => product_prefix_tail Ω u hΩ hu hn N z hz)
  have horder : analyticOrderAt (fun z => ∏' k, u k z) a =
      ∑ k ∈ Finset.range N, analyticOrderAt (u k) a := by
    rw [analyticOrderAt_congr heq]
    change analyticOrderAt ((fun z => ∏ k ∈ Finset.range N, u k z) *
      (fun z => ∏' k, u (k + N) z)) a = _
    rw [analyticOrderAt_mul ((Finset.range N).analyticAt_fun_prod (fun k _ => hau k)) hta,
      htailorder, add_zero, order_partial_product u a hau N]
  refine ⟨hfinite, N, fun n hn => (hau n).analyticOrderAt_eq_zero.mpr (htail.1 n hn),
    horder, ?_⟩
  rw [horder]
  exact WithTop.sum_ne_top.mpr (fun n _ => hfinite n)

theorem product_order_sum_on_component :
    Specs.D12Complex.Ch16.HolomorphicProducts.product_order_sum_on_component_type := by
  intro Ω u hΩ hu hn a ha hcomponent
  obtain ⟨_, N, hN, horder, hfinite⟩ := product_order_on_component Ω u hΩ hu hn a ha hcomponent
  refine ⟨(Finset.range N).finite_toSet.subset ?_, ?_, hfinite⟩
  · intro n hn
    exact Finset.mem_range.mpr (by by_contra h; exact hn (hN n (by omega)))
  · rw [horder]
    exact (tsum_eq_sum (s := Finset.range N) (fun n hn => hN n (by simpa using hn))).symm

theorem product_eq_zero_iff :
    Specs.D12Complex.Ch16.HolomorphicProducts.product_eq_zero_iff_type := by
  intro Ω u hn z hz
  constructor
  · intro hzero
    by_contra h
    have hne : ∀ n, u n z ≠ 0 := fun n hn => h ⟨n, hn⟩
    exact tprod_ne_zero_of_all_ne_zero hne (summable_norm_at hn hz) hzero
  · rintro ⟨n, hn⟩
    exact (hasProd_zero_of_exists_eq_zero ⟨n, hn⟩).tprod_eq

theorem product_zero_of_zero_factor :
    Specs.D12Complex.Ch16.HolomorphicProducts.product_zero_of_zero_factor_type := by
  intro u S n hn z hz
  exact (hasProd_zero_of_exists_eq_zero ⟨n, hn z hz⟩).tprod_eq

end D12Complex.HolomorphicProducts
