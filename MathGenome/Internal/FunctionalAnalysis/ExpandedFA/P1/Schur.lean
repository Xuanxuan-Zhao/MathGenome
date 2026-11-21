import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Schur
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

noncomputable section
open Filter
open scoped Topology ENNReal
universe u v
namespace ExpandedFA.P1.Schur
open C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The standard partial sums of the unit vectors in c₀. -/
def c0PartialSums (n : ℕ) : SequenceC0 𝕜 :=
  ∑ j ∈ Finset.range n, c0Coordinate 𝕜 j

@[simp] theorem c0PartialSums_apply (n j : ℕ) :
    (c0PartialSums (𝕜 := 𝕜) n).val j = if j < n then 1 else 0 := by
  classical
  simp only [c0PartialSums, Submodule.coe_sum, lp.coeFn_sum, Finset.sum_apply,
    c0Coordinate_apply]
  simp

theorem c0PartialSums_weakCauchy : WeakCauchy 𝕜 (c0PartialSums (𝕜 := 𝕜)) := by
  intro f
  let a := c0DualCoefficients f
  have hf (n : ℕ) : f (c0PartialSums n) = ∑ j ∈ Finset.range n, a j := by
    change f.toLinearMap (∑ j ∈ Finset.range n, c0Coordinate 𝕜 j) = _
    rw [map_sum]
    rfl
  simp_rw [hf]
  have hs : Summable (fun j => ‖a j‖) := by
    simpa using (lp.memℓp a).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)
  exact hs.of_norm.hasSum.tendsto_sum_nat.cauchySeq

/-- Coordinate evaluations on the literal c₀ subspace. -/
def c0Evaluation (j : ℕ) : SequenceC0 𝕜 →L[𝕜] 𝕜 :=
  (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ j).comp (sequenceC0Submodule 𝕜).subtypeL

theorem c0_not_weak_sequentially_complete : Spec.C0NotWeakSequentiallyComplete.{u} := by
  intro 𝕜 _ h
  obtain ⟨l, hl⟩ := h (c0PartialSums (𝕜 := 𝕜)) c0PartialSums_weakCauchy
  have hone (j : ℕ) : l.val j = 1 := by
    have hj := hl (c0Evaluation j)
    have ht : Tendsto (fun n => c0Evaluation (𝕜 := 𝕜) j (c0PartialSums n)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop j] with n hn
      change 1 = (c0PartialSums n).val j
      simp [hn]
    exact tendsto_nhds_unique hj ht
  have hzero : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 0) := by
    have hp := l.property
    change Tendsto (fun j => l.val j) atTop (𝓝 0) at hp
    simpa only [hone] using hp
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hzero)

/-- The continuous monomials on the closed unit interval. -/
def powerFunction (n : ℕ) : C(Set.Icc (0 : ℝ) 1, 𝕜) :=
  ⟨fun t => RCLike.ofReal (t.val ^ n),
    RCLike.continuous_ofReal.comp (continuous_subtype_val.pow n)⟩

lemma powerDifference_nonneg (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    0 ≤ t.val ^ n - t.val ^ (n + 1) := by
  rw [pow_succ]
  have h := pow_nonneg t.property.1 n
  nlinarith [t.property.2]

lemma powerDifference_norm (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    ‖powerFunction (𝕜 := 𝕜) n t - powerFunction (𝕜 := 𝕜) (n + 1) t‖ =
      t.val ^ n - t.val ^ (n + 1) := by
  change ‖RCLike.ofReal (t.val ^ n) - RCLike.ofReal (t.val ^ (n+1))‖ = _
  rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, abs_of_nonneg (powerDifference_nonneg n t)]

/-- Positive telescoping differences give an absolutely summable scalar series
for every continuous functional, including complex linear functionals. -/
lemma powerFunction_functional_summable
    (f : C(Set.Icc (0 : ℝ) 1, 𝕜) →L[𝕜] 𝕜) :
    Summable (fun n => ‖f (powerFunction n - powerFunction (n + 1))‖) := by
  apply summable_of_sum_range_le (fun _ => norm_nonneg _) (c := ‖f‖)
  intro N
  let d : ℕ → C(Set.Icc (0 : ℝ) 1, 𝕜) :=
    fun n => powerFunction n - powerFunction (n+1)
  let g : C(Set.Icc (0 : ℝ) 1, 𝕜) :=
    ∑ n ∈ Finset.range N, c0DualPhase (f (d n)) • d n
  have hg : ‖g‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro t
    calc
      ‖g t‖ ≤ ∑ n ∈ Finset.range N, ‖(c0DualPhase (f (d n)) • d n) t‖ := by
        simpa only [g, ContinuousMap.sum_apply] using
          norm_sum_le (Finset.range N) (fun n => (c0DualPhase (f (d n)) • d n) t)
      _ ≤ ∑ n ∈ Finset.range N, (t.val ^ n - t.val ^ (n+1)) := by
        apply Finset.sum_le_sum
        intro n hn
        change ‖c0DualPhase (f (d n)) * d n t‖ ≤ _
        rw [norm_mul]
        change ‖c0DualPhase (f (d n))‖ * ‖powerFunction (𝕜 := 𝕜) n t - powerFunction (n+1) t‖ ≤ _
        rw [powerDifference_norm]
        exact mul_le_of_le_one_left (powerDifference_nonneg n t) (c0DualPhase_norm_le _)
      _ = 1 - t.val ^ N := by rw [Finset.sum_range_sub']; simp
      _ ≤ 1 := by linarith [pow_nonneg t.property.1 N]
  have hfg : f g = RCLike.ofReal (∑ n ∈ Finset.range N, ‖f (d n)‖) := by
    simp only [g, map_sum, map_smul, smul_eq_mul]
    simp_rw [mul_comm (c0DualPhase _) _, mul_c0DualPhase]

  have hf := (f.le_opNorm g).trans (mul_le_of_le_one_right (norm_nonneg _) hg)
  rw [hfg, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hf
  exact hf

theorem powerFunction_weakCauchy : WeakCauchy 𝕜 (powerFunction (𝕜 := 𝕜)) := by
  intro f
  have hs := (powerFunction_functional_summable f).of_norm.hasSum.tendsto_sum_nat
  have ht := (tendsto_const_nhds (x := f (powerFunction 0))).sub hs
  have heq (N : ℕ) :
      f (powerFunction (𝕜 := 𝕜) N) =
        f (powerFunction 0) - ∑ n ∈ Finset.range N, f (powerFunction n - powerFunction (n+1)) := by
    simp_rw [map_sub]
    rw [Finset.sum_range_sub']
    abel
  simp_rw [← heq] at ht
  exact ht.cauchySeq

theorem continuous_not_weak_sequentially_complete :
    Spec.ContinuousNotWeakSequentiallyComplete.{u} := by
  intro 𝕜 _ h
  obtain ⟨g, hg⟩ := h (powerFunction (𝕜 := 𝕜)) powerFunction_weakCauchy
  have hzero (t : Set.Icc (0 : ℝ) 1) (ht : t.val < 1) : g t = 0 := by
    have hgt := hg (ContinuousMap.evalCLM 𝕜 t)
    have hp : Tendsto (fun n => powerFunction (𝕜 := 𝕜) n t) atTop (𝓝 0) := by
      change Tendsto (fun n => (RCLike.ofReal (t.val ^ n) : 𝕜)) atTop (𝓝 0)
      simpa only [Function.comp_def, RCLike.ofRealCLM_apply, map_zero] using
        ((RCLike.ofRealCLM (K := 𝕜)).continuous.tendsto 0).comp
          (tendsto_pow_atTop_nhds_zero_of_lt_one t.property.1 ht)
    exact tendsto_nhds_unique hgt hp
  let one : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have hone : g one = 1 := by
    have hg1 := hg (ContinuousMap.evalCLM 𝕜 one)
    have hp : Tendsto (fun n => powerFunction (𝕜 := 𝕜) n one) atTop (𝓝 1) := by
      simp [powerFunction, one]
    exact tendsto_nhds_unique hg1 hp
  let t : ℕ → Set.Icc (0 : ℝ) 1 := fun n =>
    ⟨1 - 1 / ((n : ℝ) + 1), by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      constructor
      · have hh : 1 / ((n : ℝ) + 1) ≤ 1 := by
          apply (div_le_one (by positivity)).mpr
          linarith
        linarith
      · have hh : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
        linarith⟩
  have ht : Tendsto t atTop (𝓝 one) := by
    apply tendsto_subtype_rng.mpr
    simpa [one, t] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hgz : Tendsto (fun n => g (t n)) atTop (𝓝 0) := by
    have heq (n : ℕ) : g (t n) = 0 := by
      apply hzero
      change 1 - 1 / ((n : ℝ) + 1) < 1
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    simp_rw [heq]
    exact tendsto_const_nhds
  have hg1 := (g.continuous.tendsto one).comp ht
  rw [hone] at hg1
  exact one_ne_zero (tendsto_nhds_unique hg1 hgz)

/-- Choose one late vector whose mass is concentrated on a fresh finite block. -/
lemma exists_block_approx (x : ℕ → SequenceLp 𝕜 1)
    (hc : ∀ j, Tendsto (fun n => x n j) atTop (𝓝 0))
    {δ ε : ℝ} (hε : 0 < ε) (hb : ∀ N, ∃ n ≥ N, δ ≤ ‖x n‖) (m N : ℕ) :
    ∃ n M, N ≤ n ∧ m < M ∧ δ ≤ ‖x n‖ ∧
      ‖x n - ∑ j ∈ Finset.Ico m M, lp.single 1 j (x n j)‖ < ε := by
  have hh : Tendsto (fun n => ∑ j ∈ Finset.range m, lp.single 1 j (x n j))
      atTop (𝓝 (0 : SequenceLp 𝕜 1)) := by
    have h (j : ℕ) :=
      ((lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) 1 j).continuous.tendsto 0).comp (hc j)
    simpa using tendsto_finsetSum (Finset.range m) (fun j _ => h j)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hh (ε/2) (half_pos hε)
  obtain ⟨n, hn, hbn⟩ := hb (max N K)
  have hhead : ‖∑ j ∈ Finset.range m, lp.single 1 j (x n j)‖ < ε/2 := by
    simpa using hK n (le_trans (le_max_right _ _) hn)
  have ht := (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) (x n)).tendsto_sum_nat
  obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  let M := max L (m+1)
  have hmM : m ≤ M := by dsimp [M]; omega
  have htail : ‖x n - ∑ j ∈ Finset.range M, lp.single 1 j (x n j)‖ < ε/2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hL M (le_max_left _ _)
  refine ⟨n, M, le_trans (le_max_left _ _) hn, by dsimp [M]; omega, hbn, ?_⟩
  rw [Finset.sum_Ico_eq_sub _ hmM]
  have heq : x n - ((∑ j ∈ Finset.range M, lp.single 1 j (x n j)) -
      ∑ j ∈ Finset.range m, lp.single 1 j (x n j)) =
      (x n - ∑ j ∈ Finset.range M, lp.single 1 j (x n j)) +
      ∑ j ∈ Finset.range m, lp.single 1 j (x n j) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- A single bounded bilinear test separates all the selected blocks. -/
lemma block_test (x : ℕ → SequenceLp 𝕜 1) (σ m : ℕ → ℕ) (hm : StrictMono m) :
    ∃ f : SequenceLp 𝕜 1 →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧
      ∀ k, ‖f (∑ j ∈ Finset.Ico (m k) (m (k+1)), lp.single 1 j (x (σ k) j))‖ =
        ‖∑ j ∈ Finset.Ico (m k) (m (k+1)), lp.single 1 j (x (σ k) j)‖ := by
  classical
  have huniq (k l j : ℕ)
      (hk : j ∈ Finset.Ico (m k) (m (k+1)))
      (hl : j ∈ Finset.Ico (m l) (m (l+1))) : k = l := by
    simp only [Finset.mem_Ico] at hk hl
    rcases lt_trichotomy k l with h | h | h
    · have hle : m (k+1) ≤ m l := hm.monotone (by omega)
      omega
    · exact h
    · have hle : m (l+1) ≤ m k := hm.monotone (by omega)
      omega
  let b : ℕ → 𝕜 := fun j => if h : ∃ k, j ∈ Finset.Ico (m k) (m (k+1)) then
    c0DualPhase (x (σ (Classical.choose h)) j) else 0
  have hb (j : ℕ) : ‖b j‖ ≤ 1 := by
    dsimp [b]
    split_ifs
    · exact c0DualPhase_norm_le _
    · simp
  have hb_on (k j : ℕ) (hj : j ∈ Finset.Ico (m k) (m (k+1))) :
      b j = c0DualPhase (x (σ k) j) := by
    have hex : ∃ l, j ∈ Finset.Ico (m l) (m (l+1)) := ⟨k, hj⟩
    dsimp [b]
    rw [dite_eq_left hex]
    rw [huniq (Classical.choose hex) k j (Classical.choose_spec hex) hj]
  let a : SequenceLInfinity 𝕜 := ⟨b, memℓp_infty ⟨1, by
    rintro _ ⟨j, rfl⟩
    exact hb j⟩⟩
  have ha : ‖a‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one hb
  refine ⟨l1Pairing a, (norm_l1Pairing a).trans_le ha, ?_⟩
  intro k
  have hs (j : ℕ) (z : 𝕜) : l1Pairing a (lp.single 1 j z) = a j * z := by
    rw [l1Pairing_apply, tsum_eq_single j]
    · simp
    · intro l hl
      rw [lp.single_apply_ne _ _ _ hl, mul_zero]
  have heq : l1Pairing a (∑ j ∈ Finset.Ico (m k) (m (k+1)), lp.single 1 j (x (σ k) j)) =
      RCLike.ofReal (∑ j ∈ Finset.Ico (m k) (m (k+1)), ‖x (σ k) j‖) := by
    rw [map_sum]
    calc
      _ = ∑ j ∈ Finset.Ico (m k) (m (k+1)), RCLike.ofReal ‖x (σ k) j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hs]
        change b j * x (σ k) j = RCLike.ofReal ‖x (σ k) j‖
        rw [hb_on k j hj, mul_comm, mul_c0DualPhase]
      _ = _ := by simp
  rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  have hn := lp.norm_sum_single (E := fun _ : ℕ => 𝕜) (p := 1)
    (by simp : 0 < (1 : ℝ≥0∞).toReal) (fun j => x (σ k) j)
    (Finset.Ico (m k) (m (k+1)))
  simpa using hn.symm

/-- The gliding-hump argument, with a phase-cancelling bounded test in both
scalar fields. No boundedness or completeness is added to weak nullity. -/
theorem schur_null (x : ℕ → SequenceLp 𝕜 1) (hx : WeakConverges 𝕜 x 0) :
    Tendsto x atTop (𝓝 0) := by
  by_contra h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  obtain ⟨δ, hδ, hb⟩ := h
  simp only [dist_zero_right] at hb
  have hc (j : ℕ) : Tendsto (fun n => x n j) atTop (𝓝 0) := by
    have hj := hx (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 1 j)
    change Tendsto (fun n => x n j) atTop (𝓝 ((0 : SequenceLp 𝕜 1) j)) at hj
    simpa using hj
  have hs (m k : ℕ) := exists_block_approx x hc (by positivity : 0 < δ/4) hb m k
  choose n M hn hM hbad herr using hs
  let m : ℕ → ℕ := fun k => Nat.rec 0 (fun i mi => M mi i) k
  have hmstep (k : ℕ) : m k < m (k+1) := hM (m k) k
  have hm : StrictMono m := strictMono_nat_of_lt_succ hmstep
  let σ : ℕ → ℕ := fun k => n (m k) k
  have hσ : Tendsto σ atTop atTop := tendsto_atTop_mono (fun k => hn (m k) k) tendsto_id
  obtain ⟨f, hf, hfy⟩ := block_test x σ m hm
  have hsmall := (hx f).norm.comp hσ
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hsmall (δ/2) (half_pos hδ)
  let y : SequenceLp 𝕜 1 :=
    ∑ j ∈ Finset.Ico (m K) (m (K+1)), lp.single 1 j (x (σ K) j)
  have he : ‖x (σ K) - y‖ < δ/4 := herr (m K) K
  have hnorm : ‖y‖ = ‖f y‖ := (hfy K).symm
  have hbound : ‖f (x (σ K) - y)‖ ≤ ‖x (σ K) - y‖ :=
    (f.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hf)
  have htriangle : ‖y‖ ≤ ‖f (x (σ K))‖ + ‖x (σ K) - y‖ := by
    rw [hnorm]
    calc
      ‖f y‖ ≤ ‖f (x (σ K))‖ + ‖f (x (σ K)) - f y‖ := by
        simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub' (f y) (f (x (σ K)))
      _ ≤ _ := by rw [← map_sub]; exact add_le_add le_rfl hbound
  have htotal := norm_le_norm_sub_add (x (σ K)) y
  have hbK : δ ≤ ‖x (σ K)‖ := hbad (m K) K
  have hfK : ‖f (x (σ K))‖ < δ/2 := by
    simpa using hK K le_rfl
  linarith

theorem schur_property : Spec.SchurProperty.{u} := by
  intro 𝕜 _ x l hx
  have hz : WeakConverges 𝕜 (fun n => x n - l) 0 := by
    intro f
    simpa only [map_sub, map_zero, sub_self] using
      (hx f).sub (tendsto_const_nhds (x := f l))
  have ht := (schur_null (fun n => x n - l) hz).add_const l
  simpa only [sub_add_cancel, zero_add] using ht

/-- A weakly Cauchy ℓ¹ sequence is norm Cauchy: otherwise two late terms
produce a weakly null sequence with norms bounded away from zero. -/
theorem l1_weakCauchy_normCauchy (x : ℕ → SequenceLp 𝕜 1)
    (hx : WeakCauchy 𝕜 x) : CauchySeq x := by
  by_contra h
  rw [Metric.cauchySeq_iff] at h
  push Not at h
  obtain ⟨δ, hδ, hb⟩ := h
  choose p hp q hq hdist using hb
  have hz : WeakConverges 𝕜 (fun k => x (p k) - x (q k)) 0 := by
    intro f
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hx f) ε hε
    refine ⟨N, fun k hk => ?_⟩
    simpa only [map_sub, map_zero, dist_zero_right, dist_eq_norm, sub_zero] using
      hN (p k) (hk.trans (hp k)) (q k) (hk.trans (hq k))
  have ht := schur_null (fun k => x (p k) - x (q k)) hz
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht δ hδ
  have hlt : ‖x (p N) - x (q N)‖ < δ := by simpa using hN N le_rfl
  have hge : δ ≤ ‖x (p N) - x (q N)‖ := by simpa only [dist_eq_norm] using hdist N
  exact (not_lt_of_ge hge) hlt

theorem l1_weak_sequentially_complete : Spec.L1WeakSequentialCompleteness.{u} := by
  intro 𝕜 _ x hx
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (l1_weakCauchy_normCauchy x hx)
  exact ⟨l, fun f => (f.continuous.tendsto l).comp hl⟩

end ExpandedFA.P1.Schur
