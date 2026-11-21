import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesBlockLemma
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesBlockObjects
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module

/-! James's convex-block lemma (paper.tex:3559–3659).
The proof establishes the seminorm and series estimates, recursively chooses
near-minimizing blocks with nested tail sequences, and combines their two-sided
bounds with the error budget to obtain every strict prefix estimate. -/

universe u
namespace ExpandedFA.P1.JamesBlockLemma
open Set Filter
open scoped Topology BigOperators
open JamesBlockObjects

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma bounded_of_unitBall {A : Set E} (hA : A ⊆ Metric.closedBall (0 : E) 1) :
    Bornology.IsBounded A := Metric.isBounded_closedBall.subset hA

lemma normOn_nonneg {A : Set E} (hA : A.Nonempty)
    (hb : Bornology.IsBounded A) (h : E →L[ℝ] ℝ) : 0 ≤ normOn A h := by
  obtain ⟨x, hx⟩ := hA
  exact (abs_nonneg (h x)).trans ((normOn_isLUB A ⟨x, hx⟩ hb h).1 ⟨x, hx, rfl⟩)

lemma abs_apply_le_normOn {A : Set E} (hA : A.Nonempty)
    (hb : Bornology.IsBounded A) (h : E →L[ℝ] ℝ) {x : E} (hx : x ∈ A) :
    |h x| ≤ normOn A h := (normOn_isLUB A hA hb h).1 ⟨x, hx, rfl⟩

lemma normOn_le {A : Set E} (hA : A.Nonempty)
    (hb : Bornology.IsBounded A) (h : E →L[ℝ] ℝ) {r : ℝ}
    (hr : ∀ x ∈ A, |h x| ≤ r) : normOn A h ≤ r := by
  apply (normOn_isLUB A hA hb h).2
  rintro _ ⟨x, hx, rfl⟩
  exact hr x hx

lemma normOn_le_norm {A : Set E} (hA : A.Nonempty)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1) (h : E →L[ℝ] ℝ) :
    normOn A h ≤ ‖h‖ := by
  apply normOn_le hA (bounded_of_unitBall hAb)
  intro x hx
  exact (h.le_opNorm x).trans (by
    have hx' : ‖x‖ ≤ 1 := by simpa using hAb hx
    nlinarith [norm_nonneg h])

lemma normOn_zero {A : Set E} (hA : A.Nonempty) (hb : Bornology.IsBounded A) :
    normOn A (0 : E →L[ℝ] ℝ) = 0 := by
  apply le_antisymm _ (normOn_nonneg hA hb 0)
  exact normOn_le hA hb 0 (by simp)

lemma normOn_add_le {A : Set E} (hA : A.Nonempty) (hb : Bornology.IsBounded A)
    (h k : E →L[ℝ] ℝ) : normOn A (h + k) ≤ normOn A h + normOn A k := by
  apply normOn_le hA hb
  intro x hx
  exact (abs_add_le (h x) (k x)).trans
    (add_le_add (abs_apply_le_normOn hA hb h hx) (abs_apply_le_normOn hA hb k hx))

lemma normOn_smul {A : Set E} (hA : A.Nonempty) (hb : Bornology.IsBounded A)
    (r : ℝ) (h : E →L[ℝ] ℝ) : normOn A (r • h) = |r| * normOn A h := by
  have hle (r : ℝ) (h : E →L[ℝ] ℝ) :
      normOn A (r • h) ≤ |r| * normOn A h := by
    apply normOn_le hA hb
    intro x hx
    simpa only [smul_apply, smul_eq_mul, abs_mul] using
      mul_le_mul_of_nonneg_left (abs_apply_le_normOn hA hb h hx) (abs_nonneg r)
  apply le_antisymm (hle r h)
  by_cases hr : r = 0
  · simp [hr, normOn_zero hA hb]
  · have hh := hle r⁻¹ (r • h)
    rw [inv_smul_smul₀ hr, abs_inv] at hh
    have hpos : 0 < |r| := abs_pos.mpr hr
    calc
      |r| * normOn A h = normOn A h * |r| := mul_comm _ _
      _ ≤ normOn A (r • h) :=
        (le_div_iff₀ hpos).mp (by simpa only [div_eq_inv_mul] using hh)

lemma normOn_lipschitz {A : Set E} (hA : A.Nonempty)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1) (h k : E →L[ℝ] ℝ) :
    |normOn A h - normOn A k| ≤ ‖h - k‖ := by
  have hb := bounded_of_unitBall hAb
  have h₁ := normOn_add_le hA hb (h - k) k
  have h₂ := normOn_add_le hA hb (k - h) h
  have he₁ := normOn_le_norm hA hAb (h - k)
  have he₂ := normOn_le_norm hA hAb (k - h)
  rw [sub_add_cancel] at h₁ h₂
  rw [norm_sub_rev] at he₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma continuous_normOn {A : Set E} (hA : A.Nonempty)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1) : Continuous (normOn A) := by
  apply LipschitzWith.continuous (K := 1)
  rw [lipschitzWith_iff_dist_le_mul]
  intro h k
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs] using
    normOn_lipschitz hA hAb h k

lemma L_norm_le_one {g : ℕ → E →L[ℝ] ℝ} (hg : ∀ n, ‖g n‖ ≤ 1)
    {w : E →L[ℝ] ℝ} (hw : w ∈ L g) : ‖w‖ ≤ 1 := by
  have hb : JamesBlockObjects.Spec.BoundedSequence g := ⟨1, hg⟩
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have hu (x : E) : w x ≤ ‖x‖ := by
    apply (hw x).trans
    apply limsup_le_of_le (eval_bddBelow hb x).isCoboundedUnder_le
    exact Eventually.of_forall (fun n => by simpa using (eval_bounds hg x n).2)
  rw [one_mul, Real.norm_eq_abs, abs_le]
  have hl := hu (-x)
  rw [map_neg, norm_neg] at hl
  exact ⟨by linarith, hu x⟩

lemma weighted_summable {β : ℕ → ℝ} (hβ : Summable β) (hβ0 : ∀ n, 0 ≤ β n)
    {g : ℕ → E →L[ℝ] ℝ} (hg : ∀ n, ‖g n‖ ≤ 1) :
    Summable (fun n => β n • g n) := by
  apply hβ.of_norm_bounded
  intro n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ0 n)]
  exact mul_le_of_le_one_right (hβ0 n) (hg n)

lemma weighted_sub_summable {β : ℕ → ℝ} (hβ : Summable β) (hβ0 : ∀ n, 0 ≤ β n)
    {g : ℕ → E →L[ℝ] ℝ} (hg : ∀ n, ‖g n‖ ≤ 1) (w : E →L[ℝ] ℝ) :
    Summable (fun n => β n • (g n - w)) := by
  simpa only [smul_sub] using
    (weighted_summable hβ hβ0 hg).sub (hβ.smul_const w)

lemma tailMass_eq {β : ℕ → ℝ} (hβ : HasSum β 1) (n : ℕ) :
    Spec.tailMass β n = 1 - ∑ j ∈ Finset.range n, β j := by
  have h := hβ.summable.sum_add_tsum_nat_add n
  rw [hβ.tsum_eq] at h
  exact eq_sub_of_add_eq' h

lemma tailMass_zero {β : ℕ → ℝ} (hβ : HasSum β 1) : Spec.tailMass β 0 = 1 := by
  simp [tailMass_eq hβ]

lemma tailMass_step {β : ℕ → ℝ} (hβ : HasSum β 1) (n : ℕ) :
    Spec.tailMass β n = β n + Spec.tailMass β (n + 1) := by
  rw [tailMass_eq hβ, tailMass_eq hβ, Finset.sum_range_succ]
  ring

lemma tailMass_pos {β : ℕ → ℝ} (hβ : Summable β) (hβ0 : ∀ n, 0 < β n) (n : ℕ) :
    0 < Spec.tailMass β n := by
  have ht : Summable (fun k => β (k + n)) := hβ.comp_injective (add_left_injective n)
  exact (hβ0 n).trans_le (by
    simpa only [Spec.tailMass, zero_add] using ht.le_tsum 0 (fun k _ => (hβ0 (k + n)).le))

lemma tailMass_tendsto_zero {β : ℕ → ℝ} (hβ : HasSum β 1) :
    Tendsto (Spec.tailMass β) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hβ.tendsto_sum_nat
  simpa only [sub_self, ← tailMass_eq hβ] using h

noncomputable abbrev partialSum := @Spec.partialSum E _ _
noncomputable abbrev approximation := @Spec.approximation E _ _

lemma approximation_eq {β : ℕ → ℝ} (hβ : HasSum β 1)
    (g : ℕ → E →L[ℝ] ℝ) (w : E →L[ℝ] ℝ) (n : ℕ) :
    approximation β g w n = partialSum β g w n + Spec.tailMass β n • (g n - w) := by
  simp only [approximation, partialSum, Spec.approximation, Spec.partialSum, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    tailMass_eq hβ]
  module

lemma prefix_step (β : ℕ → ℝ) (g : ℕ → E →L[ℝ] ℝ) (w : E →L[ℝ] ℝ) (n : ℕ) :
    partialSum β g w (n + 1) = partialSum β g w n + β n • (g n - w) := by
  exact Finset.sum_range_succ _ n

lemma prefix_recurrence {β : ℕ → ℝ} (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (g : ℕ → E →L[ℝ] ℝ) (w : E →L[ℝ] ℝ) (n : ℕ) :
    partialSum β g w (n + 1) =
      (β n / Spec.tailMass β n) • approximation β g w n +
        (Spec.tailMass β (n + 1) / Spec.tailMass β n) • partialSum β g w n := by
  rw [approximation_eq hβ, smul_add, smul_smul, prefix_step]
  have ht := ne_of_gt (tailMass_pos hβ.summable hβ0 n)
  have hm : β n / Spec.tailMass β n * Spec.tailMass β n = β n :=
    div_mul_cancel₀ _ ht
  rw [hm]
  have hs : β n / Spec.tailMass β n +
      Spec.tailMass β (n + 1) / Spec.tailMass β n = 1 := by
    rw [← add_div, ← tailMass_step hβ, div_self ht]
  calc
    _ = (β n / Spec.tailMass β n +
        Spec.tailMass β (n + 1) / Spec.tailMass β n) • partialSum β g w n +
        β n • (g n - w) := by rw [hs, one_smul]
    _ = _ := by rw [add_smul]; abel


/-- Iterating the prefix recurrence gives the weighted bound before the
strict error-budget estimate is used. -/
lemma prefix_norm_bound {A : Set E} (hA : A.Nonempty) (hb : Bornology.IsBounded A)
    {β : ℕ → ℝ} (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (g : ℕ → E →L[ℝ] ℝ) (w : E →L[ℝ] ℝ) (n : ℕ) :
    normOn A (partialSum β g w n) ≤ Spec.tailMass β n *
      ∑ k ∈ Finset.range n,
        β k * normOn A (approximation β g w k) /
          (Spec.tailMass β k * Spec.tailMass β (k + 1)) := by
  induction n with
  | zero => simp [partialSum, Spec.partialSum, normOn_zero hA hb]
  | succ n ih =>
    have ht := tailMass_pos hβ.summable hβ0 n
    have ht' := tailMass_pos hβ.summable hβ0 (n + 1)
    rw [prefix_recurrence hβ hβ0]
    calc
      _ ≤ normOn A ((β n / Spec.tailMass β n) • approximation β g w n) +
          normOn A ((Spec.tailMass β (n + 1) / Spec.tailMass β n) • partialSum β g w n) :=
        normOn_add_le hA hb _ _
      _ = (β n / Spec.tailMass β n) * normOn A (approximation β g w n) +
          (Spec.tailMass β (n + 1) / Spec.tailMass β n) * normOn A (partialSum β g w n) := by
        rw [normOn_smul hA hb, normOn_smul hA hb,
          abs_of_pos (div_pos (hβ0 n) ht), abs_of_pos (div_pos ht' ht)]
      _ ≤ (β n / Spec.tailMass β n) * normOn A (approximation β g w n) +
          (Spec.tailMass β (n + 1) / Spec.tailMass β n) *
            (Spec.tailMass β n * ∑ k ∈ Finset.range n,
              β k * normOn A (approximation β g w k) /
                (Spec.tailMass β k * Spec.tailMass β (k + 1))) := by
        gcongr
      _ = _ := by
        rw [Finset.sum_range_succ]
        field_simp [ht.ne', ht'.ne']
        ring

lemma reciprocal_tail_sum {β : ℕ → ℝ} (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, β k / (Spec.tailMass β k * Spec.tailMass β (k + 1))) =
      1 / Spec.tailMass β n - 1 := by
  induction n with
  | zero => simp [tailMass_zero hβ]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have ht := ne_of_gt (tailMass_pos hβ.summable hβ0 n)
    have ht' := ne_of_gt (tailMass_pos hβ.summable hβ0 (n + 1))
    have hs := tailMass_step hβ n
    field_simp [ht, ht']
    nlinarith

/-- The strict prefix bound follows from the *total* error budget. This is
why norm convergence alone would not suffice in the source proof. -/
theorem strict_prefix_bound {A : Set E} (hA : A.Nonempty) (hb : Bornology.IsBounded A)
    {β : ℕ → ℝ} (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (g : ℕ → E →L[ℝ] ℝ) (w : E →L[ℝ] ℝ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n)
    (hεsum : Summable (fun n => β n * ε n /
      (Spec.tailMass β n * Spec.tailMass β (n + 1))))
    {θ a : ℝ} (ha : 0 < a)
    (hbudget : (∑' n, β n * ε n /
      (Spec.tailMass β n * Spec.tailMass β (n + 1))) < 1 - θ)
    (hupper : ∀ n, normOn A (approximation β g w n) ≤ a * (1 + ε n))
    (n : ℕ) : normOn A (partialSum β g w n) < a * (1 - θ * Spec.tailMass β n) := by
  have ht := tailMass_pos hβ.summable hβ0 n
  have hsum := hεsum.sum_le_tsum (Finset.range n) (fun k _ => by
    exact div_nonneg (mul_nonneg (hβ0 k).le (hε k))
      (mul_nonneg (tailMass_pos hβ.summable hβ0 k).le
        (tailMass_pos hβ.summable hβ0 (k + 1)).le))
  have hsmall : (∑ k ∈ Finset.range n,
      β k * ε k / (Spec.tailMass β k * Spec.tailMass β (k + 1))) < 1 - θ :=
    hsum.trans_lt hbudget
  have hcomp : (∑ k ∈ Finset.range n,
      β k * normOn A (approximation β g w k) /
        (Spec.tailMass β k * Spec.tailMass β (k + 1))) ≤
      a * (1 / Spec.tailMass β n - 1 +
        ∑ k ∈ Finset.range n,
          β k * ε k / (Spec.tailMass β k * Spec.tailMass β (k + 1))) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n,
          β k * (a * (1 + ε k)) /
            (Spec.tailMass β k * Spec.tailMass β (k + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hupper k) (hβ0 k).le)
          (mul_nonneg (tailMass_pos hβ.summable hβ0 k).le
            (tailMass_pos hβ.summable hβ0 (k + 1)).le)
      _ = _ := by
        rw [← reciprocal_tail_sum hβ hβ0 n, mul_add, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  calc
    _ ≤ Spec.tailMass β n * _ := prefix_norm_bound hA hb hβ hβ0 g w n
    _ ≤ Spec.tailMass β n * (a * (1 / Spec.tailMass β n - 1 +
        ∑ k ∈ Finset.range n,
          β k * ε k / (Spec.tailMass β k * Spec.tailMass β (k + 1)))) :=
      mul_le_mul_of_nonneg_left hcomp ht.le
    _ < Spec.tailMass β n * (a * (1 / Spec.tailMass β n - 1 + (1 - θ))) := by
      gcongr
    _ = _ := by
      field_simp [ht.ne']
      ring


/-- Positive errors can be chosen to tend to zero with the required weighted
budget, even when the positive weights have arbitrarily small tails. -/
theorem exists_errors {β : ℕ → ℝ} (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    {θ : ℝ} (hθ : θ < 1) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      Summable (fun n => β n * ε n /
        (Spec.tailMass β n * Spec.tailMass β (n + 1))) ∧
      (∑' n, β n * ε n /
        (Spec.tailMass β n * Spec.tailMass β (n + 1))) < 1 - θ := by
  obtain ⟨δ, hδ0, c, hδ, hc⟩ := posSumOfEncodable (half_pos (sub_pos.mpr hθ)) ℕ
  let ε : ℕ → ℝ := fun n => min (δ n)
    (δ n * (Spec.tailMass β n * Spec.tailMass β (n + 1)) / β n)
  have hε0 (n : ℕ) : 0 < ε n := by
    exact lt_min (hδ0 n) (div_pos (mul_pos (hδ0 n)
      (mul_pos (tailMass_pos hβ.summable hβ0 n)
        (tailMass_pos hβ.summable hβ0 (n + 1)))) (hβ0 n))
  have hq0 (n : ℕ) : 0 ≤ β n * ε n /
      (Spec.tailMass β n * Spec.tailMass β (n + 1)) := by
    exact div_nonneg (mul_nonneg (hβ0 n).le (hε0 n).le)
      (mul_nonneg (tailMass_pos hβ.summable hβ0 n).le
        (tailMass_pos hβ.summable hβ0 (n + 1)).le)
  have hqle (n : ℕ) : β n * ε n /
      (Spec.tailMass β n * Spec.tailMass β (n + 1)) ≤ δ n := by
    apply (div_le_iff₀ (mul_pos (tailMass_pos hβ.summable hβ0 n)
      (tailMass_pos hβ.summable hβ0 (n + 1)))).2
    have hm := (le_div_iff₀ (hβ0 n)).mp (min_le_right (δ n)
      (δ n * (Spec.tailMass β n * Spec.tailMass β (n + 1)) / β n))
    exact (mul_comm (β n) (ε n)).trans_le hm
  have hqs : Summable (fun n => β n * ε n /
      (Spec.tailMass β n * Spec.tailMass β (n + 1))) :=
    Summable.of_nonneg_of_le hq0 hqle hδ.summable
  refine ⟨ε, hε0, ?_, hqs, ?_⟩
  · exact squeeze_zero (fun n => (hε0 n).le) (fun n => min_le_left _ _)
      hδ.summable.tendsto_atTop_zero
  · exact (hqs.tsum_le_tsum hqle hδ.summable).trans_lt
      (hδ.tsum_eq ▸ hc.trans_lt (half_lt_self (sub_pos.mpr hθ)))

lemma approximation_tendsto {β : ℕ → ℝ} (hβ : HasSum β 1) (hβ0 : ∀ n, 0 ≤ β n)
    {g : ℕ → E →L[ℝ] ℝ} (hg : ∀ n, ‖g n‖ ≤ 1) (w : E →L[ℝ] ℝ) :
    Tendsto (approximation β g w) atTop (𝓝 (∑' j, β j • (g j - w))) := by
  have hs := weighted_summable hβ.summable hβ0 hg
  have ht : Tendsto (fun n => Spec.tailMass β n • g n) atTop (𝓝 0) :=
    (tailMass_tendsto_zero hβ).zero_smul_isBoundedUnder_le
      ⟨1, show ∀ᶠ n : ℕ in atTop, ‖g n‖ ≤ 1 from Eventually.of_forall hg⟩
  have hlim := (hs.hasSum.tendsto_sum_nat.add ht).sub_const w
  have heq : (∑' j, β j • (g j - w)) = (∑' j, β j • g j) - w := by
    simp_rw [smul_sub]
    rw [hs.tsum_sub (hβ.summable.smul_const w), hβ.summable.tsum_smul_const,
      hβ.tsum_eq, one_smul]
  rw [heq]
  change Tendsto (fun n => (∑ j ∈ Finset.range n, β j • g j) +
    Spec.tailMass β n • g n - w) atTop (𝓝 _)
  simpa only [add_zero] using hlim

/-- Complete analytic assembly: the recursive controls imply precisely the
original conclusion, including a common limit for every `w ∈ L(g)` and the
strict inequality for every nonempty prefix. No completeness of `E` is used. -/
theorem controls_conclusion {A : Set E} (hA : A.Nonempty)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1) {θ : ℝ} (hθ : 0 < θ)
    {β : ℕ → ℝ} (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hεsum : Summable (fun n => β n * ε n /
      (Spec.tailMass β n * Spec.tailMass β (n + 1))))
    (hbudget : (∑' n, β n * ε n /
      (Spec.tailMass β n * Spec.tailMass β (n + 1))) < 1 - θ)
    {g : ℕ → E →L[ℝ] ℝ} {α : ℕ → ℝ} (hcontrols : Spec.BlockControls A θ β ε g α) :
    Spec.BlockConclusion A θ β := by
  obtain ⟨hg, hαmono, hαbound, hcontrol⟩ := hcontrols
  have hbα : BddAbove (range α) := ⟨2, by rintro _ ⟨n, rfl⟩; exact (hαbound n).2⟩
  let a : ℝ := sSup (range α)
  have haLUB : IsLUB (range α) a := isLUB_csSup (range_nonempty α) hbα
  have hαle (n : ℕ) : α n ≤ a := haLUB.1 (mem_range_self n)
  have hθa : θ ≤ a := (hαbound 0).1.trans (hαle 0)
  have ha2 : a ≤ 2 := haLUB.2 (by rintro _ ⟨n, rfl⟩; exact (hαbound n).2)
  have hαlim : Tendsto α atTop (𝓝 a) := tendsto_atTop_isLUB hαmono haLUB
  refine ⟨g, a, hg, hθa, ha2, ?_⟩
  intro w hw
  have hs := weighted_sub_summable hβ.summable (fun n => (hβ0 n).le) hg w
  have hnormlim := (continuous_normOn hA hAb).tendsto
    (∑' j, β j • (g j - w)) |>.comp
      (approximation_tendsto hβ (fun n => (hβ0 n).le) hg w)
  have hlowerlim : Tendsto (fun n => α n * (1 - ε n)) atTop (𝓝 a) := by
    simpa using hαlim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hεlim)
  have hupperlim : Tendsto (fun n => α n * (1 + ε n)) atTop (𝓝 a) := by
    simpa using hαlim.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hεlim)
  have heq : normOn A (∑' j, β j • (g j - w)) = a := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' hnormlim hupperlim
        (fun n => (hcontrol w hw n).2.le)
    · exact le_of_tendsto_of_tendsto' hlowerlim hnormlim
        (fun n => (hcontrol w hw n).1.le)
  refine ⟨hs, heq, ?_⟩
  intro n
  apply strict_prefix_bound hA (bounded_of_unitBall hAb) hβ hβ0 g w hε hεsum
    (hθ.trans_le hθa) hbudget (n := n + 1)
  intro k
  exact (hcontrol w hw k).2.le.trans
    (mul_le_mul_of_nonneg_right (hαle k) (by linarith [hε k]))


/-- A balanced set has positively norming points for every strict lower bound
on its absolute seminorm. -/
lemma exists_eval_gt {A : Set E} (hA : A.Nonempty) (hb : Bornology.IsBounded A)
    (hbal : Balanced ℝ A) (h : E →L[ℝ] ℝ) {r : ℝ} (hr : r < normOn A h) :
    ∃ x ∈ A, r < h x := by
  have hlu := normOn_isLUB A hA hb h
  obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := (lt_csSup_iff hlu.bddAbove (hA.image _)).mp hr
  by_cases hx0 : 0 ≤ h x
  · exact ⟨x, hx, by simpa only [abs_of_nonneg hx0] using hxr⟩
  · exact ⟨-x, hbal.neg_mem_iff.mpr hx, by
      simpa only [map_neg, abs_of_neg (lt_of_not_ge hx0)] using hxr⟩

/-- A scalar liminf can be selected by a genuine increasing subsequence. -/
lemma exists_liminf_subsequence {z : ℕ → E →L[ℝ] ℝ}
    (hz : JamesBlockObjects.Spec.BoundedSequence z) (x : E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => z (φ n) x) atTop (𝓝 (liminf (fun n => z n x) atTop)) := by
  obtain ⟨ψ, hψ, hψtop⟩ := exists_seq_tendsto_liminf
    (eval_bddAbove hz x).isCoboundedUnder_ge (eval_bddBelow hz x)
  obtain ⟨ρ, hρ, hψρ⟩ := strictMono_subseq_of_tendsto_atTop hψtop
  exact ⟨ψ ∘ ρ, hψρ, hψ.comp hρ.tendsto_atTop⟩

lemma V_refl (s : ℕ → E →L[ℝ] ℝ) : s ∈ V s := by
  intro n
  exact subset_convexHull ℝ _ ⟨n, by simp, rfl⟩

lemma tailHull_subset {s v : ℕ → E →L[ℝ] ℝ} (hv : v ∈ V s)
    {n m : ℕ} (hnm : n ≤ m) :
    convexHull ℝ (v '' Ici m) ⊆ convexHull ℝ (s '' Ici n) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨j, hj, rfl⟩
  exact convexHull_mono (image_mono (Ici_subset_Ici.mpr (hnm.trans hj))) (hv j)

lemma unit_of_tailHull {s : ℕ → E →L[ℝ] ℝ} (hs : ∀ n, ‖s n‖ ≤ 1)
    {n : ℕ} {g : E →L[ℝ] ℝ} (hg : g ∈ convexHull ℝ (s '' Ici n)) : ‖g‖ ≤ 1 := by
  have h : g ∈ Metric.closedBall (0 : E →L[ℝ] ℝ) 1 := by
    apply convexHull_min _ (convex_closedBall _ _) hg
    rintro _ ⟨j, _, rfl⟩
    simpa using hs j
  simpa using h

lemma V_unit {s v : ℕ → E →L[ℝ] ℝ} (hs : ∀ n, ‖s n‖ ≤ 1) (hv : v ∈ V s) :
    ∀ n, ‖v n‖ ≤ 1 := fun n => unit_of_tailHull hs (hv n)

/-- The supremum over the nonempty limsup-dominated dual set. -/
noncomputable def supNorm (A : Set E) (F : E →L[ℝ] ℝ)
    (s : ℕ → E →L[ℝ] ℝ) : ℝ := sSup ((fun w => normOn A (F - w)) '' L s)

lemma supNorm_isLUB {A : Set E} (hA : A.Nonempty)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1) {F : E →L[ℝ] ℝ} (hF : ‖F‖ ≤ 1)
    {s : ℕ → E →L[ℝ] ℝ} (hs : ∀ n, ‖s n‖ ≤ 1) :
    IsLUB ((fun w => normOn A (F - w)) '' L s) (supNorm A F s) := by
  refine isLUB_csSup ((L_nonempty s ⟨1, hs⟩).image _) ?_
  refine ⟨2, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact (normOn_le_norm hA hAb (F - w)).trans
    ((norm_sub_le F w).trans (by linarith [L_norm_le_one hs hw]))

section Selection
variable (A : Set E) (θ : ℝ) (β : ℕ → ℝ)

/-- An intermediate sequence and prefix, together with the invariants needed
for the next minimization. This is an internal proof structure, not a hypothesis
of the original convex-block lemma. -/
structure Stage (n : ℕ) where
  seq : ℕ → E →L[ℝ] ℝ
  acc : E →L[ℝ] ℝ
  unit : ∀ j, ‖seq j‖ ≤ 1
  good : ∀ q ∈ convexHull ℝ (seq '' Ici n),
    ‖acc + Spec.tailMass β n • q‖ ≤ 1 ∧
      ∀ w ∈ L seq, θ ≤ normOn A (acc + Spec.tailMass β n • q - w)

noncomputable def Stage.candidates {n : ℕ} (s : Stage A θ β n) : Set ℝ :=
  {r | ∃ q ∈ convexHull ℝ (s.seq '' Ici n), ∃ v ∈ V s.seq,
    r = supNorm A (s.acc + Spec.tailMass β n • q) v}

noncomputable def Stage.level {n : ℕ} (s : Stage A θ β n) : ℝ := sInf s.candidates

variable {A θ β}

lemma Stage.candidates_nonempty {n : ℕ} (s : Stage A θ β n) : s.candidates.Nonempty := by
  exact ⟨_, s.seq n, subset_convexHull ℝ _ ⟨n, by simp, rfl⟩,
    s.seq, V_refl s.seq, rfl⟩

lemma Stage.candidate_bounds (hA : A.Nonempty) (hAb : A ⊆ Metric.closedBall (0 : E) 1)
    {n : ℕ} (s : Stage A θ β n) {r : ℝ} (hr : r ∈ s.candidates) : θ ≤ r ∧ r ≤ 2 := by
  obtain ⟨q, hq, v, hv, rfl⟩ := hr
  have hlub := supNorm_isLUB hA hAb (s.good q hq).1 (V_unit s.unit hv)
  constructor
  · obtain ⟨w, hw⟩ := L_nonempty v ⟨1, V_unit s.unit hv⟩
    exact ((s.good q hq).2 w (L_monotone s.seq v ⟨1, s.unit⟩ hv hw)).trans
      (hlub.1 ⟨w, hw, rfl⟩)
  · apply hlub.2
    rintro _ ⟨w, hw, rfl⟩
    exact (normOn_le_norm hA hAb _).trans
      ((norm_sub_le _ w).trans (by
        linarith [(s.good q hq).1, L_norm_le_one (V_unit s.unit hv) hw]))

lemma Stage.level_isGLB (hA : A.Nonempty) (hAb : A ⊆ Metric.closedBall (0 : E) 1)
    {n : ℕ} (s : Stage A θ β n) : IsGLB s.candidates s.level := by
  refine isGLB_csInf s.candidates_nonempty ?_
  exact ⟨θ, fun r hr => (s.candidate_bounds hA hAb hr).1⟩

lemma Stage.level_bounds (hA : A.Nonempty) (hAb : A ⊆ Metric.closedBall (0 : E) 1)
    {n : ℕ} (s : Stage A θ β n) : θ ≤ s.level ∧ s.level ≤ 2 := by
  have hglb := s.level_isGLB hA hAb
  constructor
  · exact hglb.2 (fun r hr => (s.candidate_bounds hA hAb hr).1)
  · obtain ⟨r, hr⟩ := s.candidates_nonempty
    exact (hglb.1 hr).trans (s.candidate_bounds hA hAb hr).2


lemma Stage.mix_mem {n : ℕ} (s : Stage A θ β n)
    (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    {g : E →L[ℝ] ℝ} (hg : g ∈ convexHull ℝ (s.seq '' Ici n))
    {v : ℕ → E →L[ℝ] ℝ} (hv : v ∈ V s.seq)
    {q : E →L[ℝ] ℝ} (hq : q ∈ convexHull ℝ (v '' Ici (n + 1))) :
    (β n / Spec.tailMass β n) • g +
      (Spec.tailMass β (n + 1) / Spec.tailMass β n) • q ∈
        convexHull ℝ (s.seq '' Ici n) := by
  have ht := tailMass_pos hβ.summable hβ0 n
  have ht' := tailMass_pos hβ.summable hβ0 (n + 1)
  apply convex_convexHull ℝ _ hg (tailHull_subset hv (Nat.le_succ n) hq)
    (div_nonneg (hβ0 n).le ht.le) (div_nonneg ht'.le ht.le)
  rw [← add_div, ← tailMass_step hβ, div_self ht.ne']

lemma mix_eq (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (P g q : E →L[ℝ] ℝ) (n : ℕ) :
    P + Spec.tailMass β n • ((β n / Spec.tailMass β n) • g +
      (Spec.tailMass β (n + 1) / Spec.tailMass β n) • q) =
        (P + β n • g) + Spec.tailMass β (n + 1) • q := by
  rw [smul_add, smul_smul, smul_smul,
    mul_div_cancel₀ _ (tailMass_pos hβ.summable hβ0 n).ne',
    mul_div_cancel₀ _ (tailMass_pos hβ.summable hβ0 n).ne']
  abel

noncomputable def Stage.advance {n : ℕ} (s : Stage A θ β n)
    (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (g : E →L[ℝ] ℝ) (hg : g ∈ convexHull ℝ (s.seq '' Ici n))
    (v : ℕ → E →L[ℝ] ℝ) (hv : v ∈ V s.seq) : Stage A θ β (n + 1) where
  seq := v
  acc := s.acc + β n • g
  unit := V_unit s.unit hv
  good := by
    intro q hq
    have hgood := s.good _ (s.mix_mem hβ hβ0 hg hv hq)
    rw [mix_eq hβ hβ0] at hgood
    exact ⟨hgood.1, fun w hw =>
      hgood.2 w (L_monotone s.seq v ⟨1, s.unit⟩ hv hw)⟩

lemma Stage.level_le_advance (hA : A.Nonempty)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1)
    {n : ℕ} (s : Stage A θ β n) (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (g : E →L[ℝ] ℝ) (hg : g ∈ convexHull ℝ (s.seq '' Ici n))
    (v : ℕ → E →L[ℝ] ℝ) (hv : v ∈ V s.seq) :
    s.level ≤ (s.advance hβ hβ0 g hg v hv).level := by
  apply ((s.advance hβ hβ0 g hg v hv).level_isGLB hA hAb).2
  rintro r ⟨q, hq, z, hz, rfl⟩
  apply (s.level_isGLB hA hAb).1
  refine ⟨_, s.mix_mem hβ hβ0 hg hv hq, z,
    V_transitive s.seq v hv hz, ?_⟩
  rw [mix_eq hβ hβ0]
  rfl

/-- One complete choice step, retaining the selected near-minimizer and the
new tail sequence on which its bounds hold for every dominated functional. -/
structure Step {n : ℕ} (s : Stage A θ β n) (ε : ℝ) where
  g : E →L[ℝ] ℝ
  mem : g ∈ convexHull ℝ (s.seq '' Ici n)
  nextSeq : ℕ → E →L[ℝ] ℝ
  tail : nextSeq ∈ V s.seq
  control : ∀ w ∈ L nextSeq,
    s.level * (1 - ε) < normOn A (s.acc + Spec.tailMass β n • g - w) ∧
    normOn A (s.acc + Spec.tailMass β n • g - w) < s.level * (1 + ε)

lemma exists_step (hA : A.Nonempty) (hbal : Balanced ℝ A)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1) (hθ : 0 < θ)
    {n : ℕ} (s : Stage A θ β n) {ε : ℝ} (hε : 0 < ε) : Nonempty (Step s ε) := by
  have ha : 0 < s.level := hθ.trans_le (s.level_bounds hA hAb).1
  obtain ⟨r, hr, hrlt⟩ := exists_lt_of_csInf_lt s.candidates_nonempty
    (show s.level < s.level * (1 + ε) by nlinarith)
  obtain ⟨g, hg, z, hz, rfl⟩ := hr
  have hlu := supNorm_isLUB hA hAb (s.good g hg).1 (V_unit s.unit hz)
  have hlow : s.level * (1 - ε) < supNorm A (s.acc + Spec.tailMass β n • g) z := by
    have hmin := (s.level_isGLB hA hAb).1 ⟨g, hg, z, hz, rfl⟩
    nlinarith
  obtain ⟨_, ⟨w₀, hw₀, rfl⟩, hnorm⟩ :=
    (lt_csSup_iff hlu.bddAbove ((L_nonempty z ⟨1, V_unit s.unit hz⟩).image _)).mp hlow
  obtain ⟨x, hx, hpos⟩ := exists_eval_gt hA (bounded_of_unitBall hAb) hbal _ hnorm
  obtain ⟨φ, hφ, hφlim⟩ := exists_liminf_subsequence ⟨1, V_unit s.unit hz⟩ x
  let v := z ∘ φ
  have hvz : v ∈ V z := subsequence_mem_V z φ hφ
  have hv : v ∈ V s.seq := V_transitive s.seq z hz hvz
  refine ⟨⟨g, hg, v, hv, ?_⟩⟩
  intro w hw
  have hwz : w ∈ L z := L_monotone z v ⟨1, V_unit s.unit hz⟩ hvz hw
  have hwx : w x ≤ w₀ x := by
    have hu := hw x
    change w x ≤ limsup (fun j => z (φ j) x) atTop at hu
    rw [hφlim.limsup_eq] at hu
    exact hu.trans (L_bounds z ⟨1, V_unit s.unit hz⟩ w₀ hw₀ x).1
  constructor
  · have htransfer : s.level * (1 - ε) < (s.acc + Spec.tailMass β n • g - w) x := by
      simp only [sub_apply] at hpos ⊢
      linarith
    exact htransfer.trans_le ((le_abs_self _).trans
      (abs_apply_le_normOn hA (bounded_of_unitBall hAb) _ hx))
  · exact (hlu.1 ⟨w, hwz, rfl⟩).trans_lt hrlt


/-- A finite exceptional prefix does not affect limsup domination. -/
lemma L_subset_of_eventual_tailHull {s g : ℕ → E →L[ℝ] ℝ}
    (hs : ∀ n, ‖s n‖ ≤ 1) {N : ℕ}
    (hmem : ∀ j ≥ N, g j ∈ convexHull ℝ (s '' Ici j)) : L g ⊆ L s := by
  classical
  let v : ℕ → E →L[ℝ] ℝ := fun j => if N ≤ j then g j else s j
  have hv : v ∈ V s := by
    intro j
    dsimp [v]
    split_ifs with h
    · exact hmem j h
    · exact subset_convexHull ℝ _ ⟨j, by simp, rfl⟩
  intro w hw
  apply L_monotone s v ⟨1, hs⟩ hv
  intro x
  have heq : (fun j => v j x) =ᶠ[atTop] (fun j => g j x) :=
    eventually_atTop.2 ⟨N, fun j hj => by simp [v, hj]⟩
  rw [limsup_congr heq]
  exact hw x

/-- Recursively select the blocks and transfer each chosen bound to `L(g)`.
This is the existence step of the manuscript proof, before the limit and
strict-prefix arguments. -/
theorem exists_controls (hA : A.Nonempty) (hbal : Balanced ℝ A)
    (hAb : A ⊆ Metric.closedBall (0 : E) 1) (hθ : 0 < θ)
    (f : ℕ → E →L[ℝ] ℝ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hsep : ∀ h ∈ convexHull ℝ (range f), ∀ w ∈ L f, θ ≤ normOn A (h - w))
    (hβ : HasSum β 1) (hβ0 : ∀ n, 0 < β n)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ (g : ℕ → E →L[ℝ] ℝ) (α : ℕ → ℝ), Spec.BlockControls A θ β ε g α := by
  classical
  let s₀ : Stage A θ β 0 :=
    { seq := f
      acc := 0
      unit := hf
      good := by
        intro q hq
        rw [tailMass_zero hβ, one_smul, zero_add]
        exact ⟨unit_of_tailHull hf hq, hsep q
          (convexHull_mono (image_subset_range _ _) hq)⟩ }
  let pick : (n : ℕ) → (s : Stage A θ β n) → Step s (ε n) :=
    fun n s => Classical.choice (exists_step hA hbal hAb hθ s (hε n))
  let S : (n : ℕ) → Stage A θ β n :=
    fun n => Nat.rec s₀ (fun n s =>
      s.advance hβ hβ0 (pick n s).g (pick n s).mem
        (pick n s).nextSeq (pick n s).tail) n
  let T (n : ℕ) := pick n (S n)
  let g : ℕ → E →L[ℝ] ℝ := fun n => (T n).g
  let α : ℕ → ℝ := fun n => (S n).level
  have hSstep (n : ℕ) : S (n + 1) =
      (S n).advance hβ hβ0 (T n).g (T n).mem (T n).nextSeq (T n).tail := rfl
  have hStail (n : ℕ) : (S (n + 1)).seq ∈ V (S n).seq := (T n).tail
  have hSacc (n : ℕ) : (S n).acc = ∑ j ∈ Finset.range n, β j • g j := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (S n).acc + β n • g n = _
      rw [ih, Finset.sum_range_succ]
  have hnest (n j : ℕ) (hnj : n ≤ j) : (S j).seq ∈ V (S n).seq := by
    induction j, hnj using Nat.le_induction with
    | base => exact V_refl _
    | succ j hj ih => exact V_transitive (S n).seq (S j).seq ih (hStail j)
  have hgmem (n j : ℕ) (hnj : n ≤ j) : g j ∈ convexHull ℝ ((S n).seq '' Ici j) :=
    tailHull_subset (hnest n j hnj) le_rfl (T j).mem
  have hL (n : ℕ) : L g ⊆ L (S n).seq :=
    L_subset_of_eventual_tailHull (S n).unit (hgmem n)
  refine ⟨g, α, ?_, ?_, ?_, ?_⟩
  · exact fun n => unit_of_tailHull (S n).unit (T n).mem
  · apply monotone_nat_of_le_succ
    intro n
    exact (S n).level_le_advance hA hAb hβ hβ0
      (T n).g (T n).mem (T n).nextSeq (T n).tail
  · exact fun n => (S n).level_bounds hA hAb
  · intro w hw n
    have hh := (T n).control w (hL (n + 1) hw)
    rw [hSacc] at hh
    exact hh

end Selection

/-- James's convex-block lemma, with norm convergence of all displayed series
and the strict tail estimate for every nonempty finite prefix. -/
theorem james_block_lemma : Spec.JamesBlockLemma.{u} := by
  intro E _ _ A hA hbal hAb θ hθ hθ1 f hf hsep β hβ0 hβ
  obtain ⟨ε, hε, hεlim, hεsum, hbudget⟩ := exists_errors hβ hβ0 hθ1
  obtain ⟨g, α, hcontrols⟩ := exists_controls hA hbal hAb hθ f hf hsep hβ hβ0 ε hε
  exact controls_conclusion hA hAb hθ hβ hβ0 (fun n => (hε n).le) hεlim
    hεsum hbudget hcontrols

end ExpandedFA.P1.JamesBlockLemma
