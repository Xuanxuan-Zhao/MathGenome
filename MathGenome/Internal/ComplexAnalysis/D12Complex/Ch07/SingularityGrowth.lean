import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SingularityGrowth
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
open Set Metric Filter Asymptotics
open scoped Topology

namespace D12Complex.SingularityGrowth

lemma puncturedDisk_mem {a : ℂ} {r : ℝ} (hr : 0 < r) :
    puncturedDisk a r ∈ 𝓝[≠] a := by
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hr), self_mem_nhdsWithin] with z hz hza
  exact ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), mem_ball_iff_norm.mp hz⟩

lemma isolated_differentiable {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) :
    ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ f z := by
  obtain ⟨r, hr, hf⟩ := hi
  filter_upwards [puncturedDisk_mem (a := a) hr] with z hz
  exact hf.2 z hz

/-- Local analytic extensions and the canonical full-disk definition coincide. -/
lemma removable_iff_analytic_extension {f : ℂ → ℂ} {a : ℂ}
    (hi : IsolatedSingularityAt f a) :
    RemovableSingularityAt f a ↔ ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g := by
  constructor
  · rintro ⟨_, r, hr, g, hg, heq⟩
    refine ⟨g, (LocalZeroFactorization.holomorphicNear_iff_analyticAt g a).mp
      ⟨ball a r, mem_ball_self hr, hg⟩, ?_⟩
    filter_upwards [puncturedDisk_mem (a := a) hr] with z hz
    exact heq z hz
  · rintro ⟨g, hg, heq⟩
    have hd := (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)
    have heq' : ∀ᶠ z in 𝓝 a, z ≠ a → f z = g z := eventually_nhdsWithin_iff.mp heq
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hd.and heq')
    refine ⟨hi, r, hr, g, ⟨isOpen_ball, fun z hz => (hball (mem_ball.mp hz)).1⟩, ?_⟩
    intro z hz
    exact (hball (by simpa [dist_eq_norm] using hz.2)).2
      (sub_ne_zero.mp (norm_pos_iff.mp hz.1))

lemma removable_iff_limit {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) :
    RemovableSingularityAt f a ↔ ∃ L : ℂ, Tendsto f (𝓝[≠] a) (𝓝 L) := by
  rw [removable_iff_analytic_extension hi]
  constructor
  · rintro ⟨g, hg, heq⟩
    exact ⟨g a, hg.continuousAt.continuousWithinAt.tendsto.congr' heq.symm⟩
  · rintro ⟨L, hL⟩
    let g := Function.update f a L
    have hfg : f =ᶠ[𝓝[≠] a] g := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp [g, Function.update_of_ne hz]
    have hgc : ContinuousAt g a := by
      rw [continuousAt_iff_punctured_nhds]
      simpa [g] using hL.congr' hfg
    have hgd : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ g z := by
      filter_upwards [isolated_differentiable hi, self_mem_nhdsWithin] with z hz hza
      exact hz.congr_of_eventuallyEq (by
        filter_upwards [eventually_ne_nhds hza] with w hw
        simp [g, Function.update_of_ne hw])
    exact ⟨g, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc, hfg⟩

lemma removable_of_bounded {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a)
    (hb : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] a, ‖f z‖ ≤ C) : RemovableSingularityAt f a := by
  apply (removable_iff_limit hi).mpr
  refine ⟨limUnder (𝓝[≠] a) f,
    Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
      (isolated_differentiable hi) ?_⟩
  obtain ⟨C, hC⟩ := hb
  exact ⟨C + ‖f a‖, hC.mono (fun z hz => (norm_sub_le _ _).trans (add_le_add hz le_rfl))⟩

lemma removable_iff_order_nonneg {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a)
    (hf : MeromorphicAt f a) :
    RemovableSingularityAt f a ↔ 0 ≤ meromorphicOrderAt f a := by
  rw [removable_iff_analytic_extension hi, hf.meromorphicOrderAt_nonneg_iff]

/-- The exact pole order is the negative meromorphic order. -/
lemma poleOfOrder_iff_order {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hi : IsolatedSingularityAt f a) (hm : 1 ≤ m) :
    PoleOfOrderAt f a m ↔ MeromorphicAt f a ∧ meromorphicOrderAt f a = (-(m : ℤ) : ℤ) := by
  constructor
  · rintro ⟨_, _, r, hr, g, hg, hga, heq⟩
    have hgan : AnalyticAt ℂ g a := (LocalZeroFactorization.holomorphicNear_iff_analyticAt g a).mp
      ⟨ball a r, mem_ball_self hr, hg⟩
    have he : f =ᶠ[𝓝[≠] a] (fun z => (z-a)^(-(m : ℤ)) • g z) := by
      filter_upwards [puncturedDisk_mem hr] with z hz
      simpa [zpow_neg, zpow_natCast, smul_eq_mul] using heq z hz
    have hf : MeromorphicAt f a := MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
      ⟨-(m : ℤ), g, hgan, he⟩
    exact ⟨hf, (meromorphicOrderAt_eq_int_iff hf).mpr ⟨g, hgan, hga, he⟩⟩
  · rintro ⟨hf, ho⟩
    obtain ⟨g, hg, hga, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
    have hd := Complex.analyticAt_iff_eventually_differentiableAt.mp hg
    have heq' : ∀ᶠ z in 𝓝 a, z ≠ a → f z = ((z-a)^m)⁻¹ * g z := by
      simpa [zpow_neg, zpow_natCast, smul_eq_mul] using eventually_nhdsWithin_iff.mp heq
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hd.and heq')
    refine ⟨hm, hi, r, hr, g, ⟨isOpen_ball, fun z hz => (hball (mem_ball.mp hz)).1⟩, hga, ?_⟩
    intro z hz
    exact (hball (by simpa [dist_eq_norm] using hz.2)).2
      (sub_ne_zero.mp (norm_pos_iff.mp hz.1))


lemma meromorphic_of_removable {f : ℂ → ℂ} {a : ℂ} (hr : RemovableSingularityAt f a) :
    MeromorphicAt f a := by
  obtain ⟨g, hg, heq⟩ := (removable_iff_analytic_extension hr.1).mp hr
  exact hg.meromorphicAt.congr heq.symm

lemma atMost_iff_order {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) (m : ℕ) :
    (RemovableSingularityAt f a ∨ ∃ k : ℕ, k ≤ m ∧ PoleOfOrderAt f a k) ↔
      MeromorphicAt f a ∧ (-(m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f a := by
  constructor
  · rintro (hr | ⟨k, hkm, hk⟩)
    · have hf := meromorphic_of_removable hr
      refine ⟨hf, le_trans ?_ ((removable_iff_order_nonneg hi hf).mp hr)⟩
      exact_mod_cast (by omega : -(m : ℤ) ≤ 0)
    · obtain ⟨hf, ho⟩ := (poleOfOrder_iff_order hi hk.1).mp hk
      refine ⟨hf, ?_⟩
      rw [ho]
      exact_mod_cast (by omega : -(m : ℤ) ≤ -(k : ℤ))
  · rintro ⟨hf, hb⟩
    by_cases hnonneg : 0 ≤ meromorphicOrderAt f a
    · exact Or.inl ((removable_iff_order_nonneg hi hf).mpr hnonneg)
    · have hneg : meromorphicOrderAt f a < 0 := lt_of_not_ge hnonneg
      cases ho : meromorphicOrderAt f a with
      | top => simp [ho] at hneg
      | coe n =>
        have hn : n < 0 := by simpa [ho] using hneg
        have hnm : -(m : ℤ) ≤ n := by
          rw [ho] at hb
          exact_mod_cast hb
        let k := (-n).toNat
        have hk : 1 ≤ k := by dsimp [k]; omega
        have hkn : -(k : ℤ) = n := by dsimp [k]; omega
        refine Or.inr ⟨k, by dsimp [k]; omega, (poleOfOrder_iff_order hi hk).mpr ⟨hf, ?_⟩⟩
        simpa [hkn] using ho

lemma weighted_isolated {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) (m : ℕ) :
    IsolatedSingularityAt (fun z => (z-a)^m * f z) a := by
  obtain ⟨r, hr, hf⟩ := hi
  exact ⟨r, hr, hf.1, fun z hz =>
    ((differentiableAt_id.sub_const a).pow m).mul (hf.2 z hz)⟩

lemma meromorphic_of_weighted_removable {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hr : RemovableSingularityAt (fun z => (z-a)^m * f z) a) : MeromorphicAt f a := by
  obtain ⟨g, hg, heq⟩ := (removable_iff_analytic_extension hr.1).mp hr
  apply MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
  refine ⟨-(m : ℤ), g, hg, ?_⟩
  filter_upwards [heq, self_mem_nhdsWithin] with z hz hza
  simp only [smul_eq_mul, zpow_neg, zpow_natCast]
  rw [← hz, inv_mul_cancel_left₀ (pow_ne_zero m (sub_ne_zero.mpr hza))]

lemma weighted_order {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (m : ℕ) :
    meromorphicOrderAt (fun z => (z-a)^m * f z) a = (m : WithTop ℤ) + meromorphicOrderAt f a := by
  change meromorphicOrderAt ((fun z => (z-a)^m) * f) a = _
  rw [meromorphicOrderAt_mul (by fun_prop) hf]
  have hp : meromorphicOrderAt (fun z : ℂ => (z-a)^m) a = (m : WithTop ℤ) := by
    simpa only [Pi.pow_def] using (meromorphicOrderAt_pow_id_sub_const (x := a) (n := m))
  rw [hp]

lemma bounded_weighted_iff {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) (m : ℕ) :
    ((fun z => (z-a)^m * f z) =O[𝓝[≠] a] (fun _ => (1 : ℂ))) ↔
      MeromorphicAt f a ∧ 0 ≤ (m : WithTop ℤ) + meromorphicOrderAt f a := by
  constructor
  · intro hb
    have hr := removable_of_bounded (weighted_isolated hi m) ((isBigO_one_iff ℂ).mp hb)
    have hf := meromorphic_of_weighted_removable hr
    refine ⟨hf, ?_⟩
    rw [← weighted_order hf m]
    exact (removable_iff_order_nonneg (weighted_isolated hi m) (by fun_prop)).mp hr
  · rintro ⟨hf, ho⟩
    have hF : MeromorphicAt (fun z => (z-a)^m * f z) a := by fun_prop
    rw [← weighted_order hf m] at ho
    obtain ⟨L, hL⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hF ho
    exact hL.isBigO_one ℂ

lemma nonneg_add_iff (m : ℕ) (o : WithTop ℤ) :
    0 ≤ (m : WithTop ℤ) + o ↔ (-(m : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => simp
  | coe n =>
    norm_cast
    omega

lemma pow_eventually_ne (a : ℂ) (m : ℕ) : ∀ᶠ z in 𝓝[≠] a, (z-a)^m ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact pow_ne_zero m (sub_ne_zero.mpr hz)

theorem bigO_iff : Specs.D12Complex.Ch07.SingularityGrowth.bigO_iff_type := by
  intro f a hi m
  rw [atMost_iff_order hi m]
  have hb := isBigO_mul_iff_isBigO_div (g := f) (h := fun _ => (1 : ℂ)) (pow_eventually_ne a m)
  simp only [one_div] at hb
  rw [← hb, bounded_weighted_iff hi m, nonneg_add_iff]


lemma zero_limit_weighted_iff {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) (m : ℕ) :
    Tendsto (fun z => (z-a)^m * f z) (𝓝[≠] a) (𝓝 0) ↔
      MeromorphicAt f a ∧ 0 < (m : WithTop ℤ) + meromorphicOrderAt f a := by
  constructor
  · intro h
    have hf := ((bounded_weighted_iff hi m).mp (h.isBigO_one ℂ)).1
    have hF : MeromorphicAt (fun z => (z-a)^m * f z) a := by fun_prop
    refine ⟨hf, ?_⟩
    rw [← weighted_order hf m]
    exact (tendsto_zero_iff_meromorphicOrderAt_pos hF).mp h
  · rintro ⟨hf, ho⟩
    rw [← weighted_order hf m] at ho
    exact tendsto_zero_of_meromorphicOrderAt_pos ho

lemma pos_add_iff (m : ℕ) (hm : 1 ≤ m) (o : WithTop ℤ) :
    0 < (m : WithTop ℤ) + o ↔ (-((m-1 : ℕ) : ℤ) : WithTop ℤ) ≤ o := by
  cases o with
  | top => simp
  | coe n =>
    norm_cast
    omega

theorem littleO_iff : Specs.D12Complex.Ch07.SingularityGrowth.littleO_iff_type := by
  intro f a hi m hm
  rw [atMost_iff_order hi (m-1)]
  have hb := isLittleO_mul_iff_isLittleO_div (g := f) (h := fun _ => (1 : ℂ))
    (pow_eventually_ne a m)
  simp only [one_div] at hb
  rw [← hb, isLittleO_one_iff ℂ, zero_limit_weighted_iff hi m, pos_add_iff m hm]

theorem finiteLimit_iff : Specs.D12Complex.Ch07.SingularityGrowth.finiteLimit_iff_type := by
  intro f a hi
  exact (removable_iff_limit hi).symm

theorem extension_value : Specs.D12Complex.Ch07.SingularityGrowth.extension_value_type := by
  intro f g a L r hr hg heq hL
  have he : f =ᶠ[𝓝[≠] a] g := by
    filter_upwards [puncturedDisk_mem (a := a) hr] with z hz
    exact heq z hz
  exact tendsto_nhds_unique
    ((hg.2 a (mem_ball_self hr)).continuousAt.continuousWithinAt.tendsto.congr' he.symm) hL

theorem bounded_removable : Specs.D12Complex.Ch07.SingularityGrowth.bounded_removable_type := by
  intro f a hi hb
  exact removable_of_bounded hi hb

theorem mul_tendsto_zero_removable :
    Specs.D12Complex.Ch07.SingularityGrowth.mul_tendsto_zero_removable_type := by
  intro f a hi h
  have ho : f =o[𝓝[≠] a] (fun z => ((z-a)^1)⁻¹) := by
    have he := isLittleO_mul_iff_isLittleO_div (g := f) (h := fun _ => (1 : ℂ))
      (pow_eventually_ne a 1)
    simp only [one_div] at he
    apply he.mp
    simpa only [pow_one] using (isLittleO_one_iff ℂ).mpr h
  rcases (littleO_iff f a hi 1 le_rfl).mp ho with hr | ⟨k, hk, hp⟩
  · exact hr
  · have := hp.1
    omega

lemma isolated_of_eventually_differentiable {f : ℂ → ℂ} {a : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ f z) : IsolatedSingularityAt f a := by
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hd)
  refine ⟨r, hr, ?_, ?_⟩
  · exact (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).inter
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
  · intro z hz
    exact hb (by simpa [dist_eq_norm] using hz.2)
      (sub_ne_zero.mp (norm_pos_iff.mp hz.1))

lemma pole_iff_order_neg {f : ℂ → ℂ} {a : ℂ} (hi : IsolatedSingularityAt f a) :
    PoleAt f a ↔ MeromorphicAt f a ∧ meromorphicOrderAt f a < 0 := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨hf, ho⟩ := (poleOfOrder_iff_order hi hm.1).mp hm
    refine ⟨hf, ?_⟩
    rw [ho]
    exact_mod_cast (by have := hm.1; omega : -(m : ℤ) < 0)
  · rintro ⟨hf, hn⟩
    cases ho : meromorphicOrderAt f a with
    | top => simp [ho] at hn
    | coe n =>
      have hn' : n < 0 := by simpa [ho] using hn
      let m := (-n).toNat
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmn : -(m : ℤ) = n := by dsimp [m]; omega
      exact ⟨m, (poleOfOrder_iff_order hi hm).mpr ⟨hf, by simpa [hmn] using ho⟩⟩

theorem pole_iff : Specs.D12Complex.Ch07.SingularityGrowth.pole_iff_type := by
  intro f a hi
  rw [pole_iff_order_neg hi]
  constructor
  · intro h
    have hfc : Tendsto f (𝓝[≠] a) (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.mp h
    have hinv : Tendsto (fun z => (f z)⁻¹) (𝓝[≠] a) (𝓝 0) :=
      tendsto_inv₀_cobounded.comp hfc
    have hne : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := by
      filter_upwards [h.eventually_gt_atTop 0] with z hz
      exact norm_pos_iff.mp hz
    have hdi : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ (fun z => (f z)⁻¹) z := by
      filter_upwards [isolated_differentiable hi, hne] with z hz hn
      exact hz.inv hn
    have hri := (removable_iff_limit (isolated_of_eventually_differentiable hdi)).mpr ⟨0, hinv⟩
    have hf : MeromorphicAt f a := by
      simpa only [Pi.inv_def, inv_inv] using (meromorphic_of_removable hri).inv
    exact ⟨hf, (tendsto_cobounded_iff_meromorphicOrderAt_neg hf).mp hfc⟩
  · rintro ⟨_, ho⟩
    exact tendsto_norm_atTop_iff_cobounded.mpr (tendsto_cobounded_of_meromorphicOrderAt_neg ho)

end D12Complex.SingularityGrowth
