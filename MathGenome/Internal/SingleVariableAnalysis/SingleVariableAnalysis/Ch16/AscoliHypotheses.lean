import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.AscoliHypotheses
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.Equicontinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! The three explicit counterexamples of K03.16.ascoli_hypotheses. -/
namespace SingleVariableAnalysis.AscoliHypotheses

open scoped Topology
open Specs.SingleVariableAnalysis.Ch16.AscoliHypotheses

/-- Constants have zero oscillation for every radius, uniformly in the index. -/
theorem constants_equicontinuous : constantsEquicontinuous := by
  intro K _ _
  constructor
  · intro x ε hε
    exact ⟨1, zero_lt_one, fun y _ f hf => by
      obtain ⟨n, rfl⟩ := hf
      simpa [constants] using hε⟩
  · intro ε hε
    exact ⟨1, zero_lt_one, fun x y _ f hf => by
      obtain ⟨n, rfl⟩ := hf
      simpa [constants] using hε⟩

/-- Every evaluation of the constant sequence is unbounded. -/
theorem constants_unbounded : constantsUnbounded := by
  intro K _ hK
  have hu : ∀ x : K, ∀ M : ℝ, ∃ n : ℕ, M < |constants K n x| := by
    intro x M
    obtain ⟨n, hn⟩ := exists_nat_gt M
    refine ⟨n, ?_⟩
    simpa [constants, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)] using
      (lt_add_of_lt_of_nonneg hn zero_le_one)
  have hp : ¬ PointwiseBoundedFamily K (Set.range (constants K)) := by
    intro h
    obtain ⟨x, hx⟩ := hK
    let y : K := ⟨x, hx⟩
    obtain ⟨M, _, hM⟩ := h y
    obtain ⟨n, hn⟩ := hu y M
    have hb : |constants K n y| ≤ M := by
      simpa only [Real.norm_eq_abs] using (hM (constants K n) ⟨n, rfl⟩)
    exact (not_lt_of_ge hb) hn
  refine ⟨hu, hp, ?_⟩
  intro h
  apply hp
  obtain ⟨M, hM, hb⟩ := h
  exact fun x => ⟨M, hM, fun f hf => hb f hf x⟩

/-- Even a single fixed point prevents uniform convergence of a subsequence. -/
theorem constants_no_uniform_subsequence : constantsNoUniformSubsequence := by
  intro K _ hK k hk f h
  obtain ⟨x, hx⟩ := hK
  let y : K := ⟨x, hx⟩
  obtain ⟨N, hN⟩ := h 1 zero_lt_one
  obtain ⟨m, hm⟩ := exists_nat_gt (f y + 1)
  let j := max N m
  have hj : m ≤ k j := (le_max_right N m).trans (hk.id_le j)
  have hcast : (m : ℝ) ≤ k j := by exact_mod_cast hj
  have he := hN j (le_max_left _ _) y
  change |(k j + 1 : ℝ) - f y| < 1 at he
  have := (abs_lt.mp he).2
  linarith

lemma peak_pos (n : ℕ) : 0 < peak n := by
  unfold peak
  exact div_pos Real.pi_pos (by positivity)

lemma peak_mem (n : ℕ) : peak n ∈ sineDomain := by
  refine ⟨(peak_pos n).le, ?_⟩
  unfold peak
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n + 1 : ℝ))).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [Real.pi_pos]

lemma sine_peak_value (n : ℕ) : Real.sin ((n + 1 : ℝ) * peak n) = 1 := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have he : (n + 1 : ℝ) * peak n = Real.pi / 2 := by
    unfold peak
    field_simp
  rw [he, Real.sin_pi_div_two]

/-- A quantitative tail bound for the points π/(2(n+1)). -/
lemma peak_small (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, peak n < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / (2 * δ))
  refine ⟨N, fun n hn => ?_⟩
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : Real.pi / (2 * δ) < (n + 1 : ℝ) := by linarith
  have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * δ)).mp hlt
  unfold peak
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (n + 1 : ℝ))).mpr
  nlinarith

/-- These points lie in the interval, tend to zero, and attain sine value one. -/
theorem sine_peaks : sinePeaks := by
  constructor
  · intro n
    exact ⟨peak_mem n, sine_peak_value n, by simp⟩
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := peak_small ε hε
    refine ⟨N, fun n hn => ?_⟩
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (peak_pos n)] using hN n hn

/-- The common bound is exactly the usual sine bound one. -/
theorem sines_bounded : sinesBounded := by
  have hb : ∀ n : ℕ, ∀ x : sineDomain, |sines n x| ≤ 1 :=
    fun n x => Real.abs_sin_le_one _
  refine ⟨hb, 1, zero_le_one, ?_⟩
  intro f hf x
  obtain ⟨n, rfl⟩ := hf
  simpa only [Real.norm_eq_abs] using hb n x

/-- No radius at zero controls all the sine functions. -/
theorem sines_not_equicontinuous : sinesNotEquicontinuous := by
  have hz : (0 : ℝ) ∈ sineDomain := ⟨le_rfl, by positivity⟩
  have hnot : ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : sineDomain, |y.val| < δ → ∀ n : ℕ,
        |sines n y - Real.sin 0| < ε) := by
    intro h
    obtain ⟨δ, hδ, hd⟩ := h 1 zero_lt_one
    obtain ⟨N, hN⟩ := peak_small δ hδ
    let y : sineDomain := ⟨peak N, peak_mem N⟩
    have he := hd y (by simpa [y, abs_of_pos (peak_pos N)] using hN N le_rfl) N
    change |Real.sin ((N + 1 : ℝ) * peak N) - Real.sin 0| < 1 at he
    simp [sine_peak_value] at he
  refine ⟨hnot, ?_⟩
  intro h
  apply hnot
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := h ⟨0, hz⟩ ε hε
  refine ⟨δ, hδ, fun y hy n => ?_⟩
  have he := hd y (by simpa [Subtype.dist_eq, Real.dist_eq] using hy)
    (sines n) ⟨n, rfl⟩
  simpa [Real.norm_eq_abs, sines] using he

/-- Three errors below 1/4 contradict the unit oscillation at a moving peak. -/
theorem sines_no_uniform_subsequence : sinesNoUniformSubsequence := by
  intro k hk f h
  have hf : Continuous f := realUniformLimit_continuous
    (fun j x => sines (k j) x) f (fun j => (sines (k j)).continuous) h
  let z : sineDomain := ⟨0, le_rfl, by positivity⟩
  obtain ⟨N, hN⟩ := h (1 / 4) (by norm_num)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hf.continuousAt (1 / 4) (by norm_num)
  obtain ⟨M, hM⟩ := peak_small δ hδ
  let j := max N M
  have hj : M ≤ k j := (le_max_right N M).trans (hk.id_le j)
  let y : sineDomain := ⟨peak (k j), peak_mem (k j)⟩
  have hy : dist y z < δ := by
    simpa [y, z, Subtype.dist_eq, Real.dist_eq, abs_of_pos (peak_pos (k j))] using hM (k j) hj
  have h0 := hN j (le_max_left N M) z
  have h1 := hN j (le_max_left N M) y
  have h2 := hd hy
  change |Real.sin ((k j + 1 : ℝ) * 0) - f z| < 1 / 4 at h0
  change |Real.sin ((k j + 1 : ℝ) * peak (k j)) - f y| < 1 / 4 at h1
  simp only [mul_zero, Real.sin_zero, zero_sub, abs_neg] at h0
  rw [sine_peak_value] at h1
  rw [Real.dist_eq] at h2
  have h0' := (abs_lt.mp h0).2
  have h1' := (abs_lt.mp h1).2
  have h2' := (abs_lt.mp h2).2
  linarith

/-- Real projection preserves uniform convergence of a real-valued embedding. -/
lemma uniform_real_of_complex_embedding {X : Type*} (F : ℕ → X → ℝ) (f : X → ℂ)
    (h : ComplexUniformConverges (fun n x => (F n x : ℂ)) f) :
    RealUniformConverges F (fun x => (f x).re) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have he := Complex.abs_re_le_norm ((F n x : ℂ) - f x)
  simp only [Complex.sub_re, Complex.ofReal_re] at he
  exact he.trans_lt (hN n hn x)

/-- The constant counterexample also applies in the complex scalar space. -/
theorem complex_constants_counterexample : complexConstantsCounterexample := by
  intro K hK hne
  have hp : PointwiseEquicontinuousFamily K (Set.range (complexConstants K)) := by
    intro x ε hε
    exact ⟨1, zero_lt_one, fun y _ f hf => by
      obtain ⟨n, rfl⟩ := hf
      simpa [complexConstants, constants] using hε⟩
  have hu : ∀ x : K, ∀ M : ℝ, ∃ n : ℕ, M < ‖complexConstants K n x‖ := by
    simpa only [complexConstants, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs]
      using (constants_unbounded K hK hne).1
  have hn : ¬ PointwiseBoundedFamily K (Set.range (complexConstants K)) := by
    intro h
    obtain ⟨x, hx⟩ := hne
    let y : K := ⟨x, hx⟩
    obtain ⟨M, _, hM⟩ := h y
    obtain ⟨n, hn⟩ := hu y M
    exact (not_lt_of_ge (hM (complexConstants K n) ⟨n, rfl⟩)) hn
  refine ⟨hp, ?_, hu, hn, ?_, ?_⟩
  · intro ε hε
    exact ⟨1, zero_lt_one, fun x y _ f hf => by
      obtain ⟨n, rfl⟩ := hf
      simpa [complexConstants, constants] using hε⟩
  · intro h
    obtain ⟨M, hM, hb⟩ := h
    exact hn (fun x => ⟨M, hM, fun f hf => hb f hf x⟩)
  · intro k hk f h
    exact constants_no_uniform_subsequence K hK hne k hk (fun x => (f x).re)
      (uniform_real_of_complex_embedding _ f h)

/-- The sine counterexample also applies in the complex scalar space. -/
theorem complex_sines_counterexample : complexSinesCounterexample := by
  have hb : ∀ n : ℕ, ∀ x : sineDomain, ‖complexSines n x‖ ≤ 1 := by
    simpa only [complexSines, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs]
      using sines_bounded.1
  have hnot : ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y : sineDomain, |y.val| < δ → ∀ n : ℕ, ‖complexSines n y‖ < ε) := by
    simpa only [complexSines, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs,
      Real.sin_zero, sub_zero] using sines_not_equicontinuous.1
  refine ⟨hb, ?_, hnot, ?_, ?_⟩
  · refine ⟨1, zero_le_one, fun f hf x => ?_⟩
    obtain ⟨n, rfl⟩ := hf
    exact hb n x
  · intro h
    apply sines_not_equicontinuous.2
    intro x ε hε
    obtain ⟨δ, hδ, hd⟩ := h x ε hε
    refine ⟨δ, hδ, fun y hy f hf => ?_⟩
    obtain ⟨n, rfl⟩ := hf
    have he := hd y hy (complexSines n) ⟨n, rfl⟩
    simpa only [complexSines, ContinuousMap.coe_mk, ← Complex.ofReal_sub,
      Complex.norm_real] using he
  · intro k hk f h
    exact sines_no_uniform_subsequence k hk (fun x => (f x).re)
      (uniform_real_of_complex_embedding _ f h)

/-- Singleton balls are compact neighborhoods, and a finite half-ball cover fails. -/
theorem discrete_counterexample : discreteCounterexample := by
  have hd : ∀ m n : DiscreteNat, dist m n = if m = n then 0 else 1 := fun _ _ => rfl
  have hs : ∀ n : DiscreteNat, ({n} : Set DiscreteNat) ∈ 𝓝 n := by
    intro n
    apply Metric.mem_nhds_iff.mpr
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro m hm
    have he : m = n := by
      by_contra hne
      have : (1 : ℝ) < 1 / 2 := by simpa [Metric.mem_ball, hd, hne] using hm
      norm_num at this
    simpa using he
  have hc : LocallyCompactSpace DiscreteNat := by
    refine ⟨fun n s hsn => ⟨{n}, hs n, ?_, isCompact_singleton⟩⟩
    exact Set.singleton_subset_iff.mpr (mem_of_mem_nhds hsn)
  have hb : Bornology.IsBounded (Set.univ : Set DiscreteNat) := by
    apply Metric.isBounded_iff.mpr
    refine ⟨1, fun x _ y _ => ?_⟩
    rw [hd]
    split_ifs <;> norm_num
  have hn : ∀ t : Finset DiscreteNat, ∃ n : DiscreteNat, ∀ m ∈ t, n ∉ Metric.ball m (1 / 2) := by
    intro t
    obtain ⟨n, hn⟩ := t.finite_toSet.exists_notMem
    refine ⟨n, fun m hm hnm => ?_⟩
    have hne : n ≠ m := fun h => hn (h ▸ hm)
    have : (1 : ℝ) < 1 / 2 := by simpa [Metric.mem_ball, hd, hne] using hnm
    norm_num at this
  refine ⟨hd, fun n => ⟨isCompact_singleton, hs n⟩, hc, hb, hn, ?_⟩
  intro ht
  obtain ⟨t, htf, hcover⟩ := Metric.totallyBounded_iff.mp ht (1 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := hn htf.toFinset
  have he := hcover (Set.mem_univ n)
  obtain ⟨m, hm, hnm⟩ := Set.mem_iUnion₂.mp he
  exact hn m (by simpa using hm) hnm

end SingleVariableAnalysis.AscoliHypotheses
