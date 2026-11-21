import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.BoundedSectionVariationalInequality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.StampacchiaEnergyStability
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Positivity

/-! Bounded-section existence for a bounded linear monotone operator.
We use coercive regularizations. Comparing two regularized solutions gives
strong Cauchy convergence from boundedness of their distances to the test
point; thus the weak subsequence and Minty steps can be avoided. -/
noncomputable section
open Filter
open scoped InnerProductSpace Topology
namespace ExpandedFA.Geometry.BoundedSectionVariationalInequality
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A bounded coercive operator satisfies the real variational inequality. -/
theorem coercive_operator_exists [CompleteSpace H] (B : H →L[ℝ] H)
    (α : ℝ) (hα : 0 < α) (hB : ∀ x, α * ‖x‖ ^ 2 ≤ ⟪B x, x⟫_ℝ)
    (f : H) (K : Set H) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) :
    ∃ x ∈ K, ∀ v ∈ K, 0 ≤ ⟪B x - f, v - x⟫_ℝ := by
  let a : H →L[ℝ] H →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ H H ℝ).flip B).comp (innerSL ℝ)
  have ha (x y : H) : a x y = ⟪x, B y⟫_ℝ := rfl
  obtain ⟨x, hx, _⟩ :=
    ExpandedFA.Hilbert.StampacchiaEnergyStability.stampacchia_exists_unique
      ℝ H a ‖a‖ α ⟨a.opNorm_nonneg, a.le_opNorm₂⟩
      ⟨hα, fun x => by simpa only [ha, RCLike.re_to_real, real_inner_comm] using hB x⟩
      f K hne hclosed hconvex
  refine ⟨x, hx.1, fun v hv => ?_⟩
  have h := hx.2 v hv
  simp only [ha, RCLike.re_to_real] at h
  rw [inner_sub_left, real_inner_comm (v - x) (B x), real_inner_comm (v - x) f]
  linarith

/-- Comparing Tikhonov regularizations bounds the squared distance by the
increase of the squared distance to the regularization center. -/
theorem regularized_distance_bound (A : H →L[ℝ] H)
    (hmono : ∀ x y, 0 ≤ ⟪A x - A y, x - y⟫_ℝ)
    (f v₀ x y : H) (ε η : ℝ) (hη : 0 < η) (hεη : η < ε)
    (hx : 0 ≤ ⟪A x - f + ε • (x - v₀), y - x⟫_ℝ)
    (hy : 0 ≤ ⟪A y - f + η • (y - v₀), x - y⟫_ℝ) :
    ‖x - y‖ ^ 2 ≤ ‖y - v₀‖ ^ 2 - ‖x - v₀‖ ^ 2 := by
  have hi :
      (ε + η) * ‖x - y‖ ^ 2 ≤
        (ε - η) * (‖y - v₀‖ ^ 2 - ‖x - v₀‖ ^ 2) := by
    have hm : ⟪A y - f, x - y⟫_ℝ ≤ ⟪A x - f, x - y⟫_ℝ := by
      have h := hmono x y
      simp only [inner_sub_left] at h ⊢
      linarith
    have heq : y - x = -(x - y) := by abel
    rw [heq, inner_add_left, inner_neg_right, inner_neg_right,
      real_inner_smul_left] at hx
    rw [inner_add_left, real_inner_smul_left] at hy
    have hreg : ε * ⟪x - v₀, x - y⟫_ℝ ≤ η * ⟪y - v₀, x - y⟫_ℝ := by
      linarith
    have he : x - y = (x - v₀) - (y - v₀) := by abel
    have h1 : ⟪x - v₀, x - y⟫_ℝ = ‖x - v₀‖ ^ 2 - ⟪x - v₀, y - v₀⟫_ℝ := by
      rw [he, inner_sub_right, real_inner_self_eq_norm_sq]
    have h2 : ⟪y - v₀, x - y⟫_ℝ = ⟪x - v₀, y - v₀⟫_ℝ - ‖y - v₀‖ ^ 2 := by
      rw [he, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
    rw [h1, h2] at hreg
    have hd := norm_sub_sq_real (x - v₀) (y - v₀)
    rw [← he] at hd
    nlinarith
  have hsum : 0 < ε + η := by linarith
  have hdiff : 0 ≤ ‖y - v₀‖ ^ 2 - ‖x - v₀‖ ^ 2 := by
    have := mul_nonneg hsum.le (sq_nonneg ‖x - y‖)
    nlinarith
  have hmul : (ε + η) * ‖x - y‖ ^ 2 ≤
      (ε + η) * (‖y - v₀‖ ^ 2 - ‖x - v₀‖ ^ 2) := by
    nlinarith [mul_nonneg hη.le hdiff]
  exact (mul_le_mul_iff_right₀ hsum).mp hmul

/-- Positive regularization is solvable without any coercivity of A itself. -/
theorem regularized_exists [CompleteSpace H] (A : H →L[ℝ] H)
    (hmono : ∀ x y, 0 ≤ ⟪A x - A y, x - y⟫_ℝ)
    (f v₀ : H) (K : Set H) (hne : K.Nonempty) (hclosed : IsClosed K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ K, ∀ v ∈ K, 0 ≤ ⟪A x - f + ε • (x - v₀), v - x⟫_ℝ := by
  let B := A + ε • ContinuousLinearMap.id ℝ H
  have hB (x : H) : ε * ‖x‖ ^ 2 ≤ ⟪B x, x⟫_ℝ := by
    have hm := hmono x 0
    simp only [map_zero, sub_zero] at hm
    simp only [B, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    linarith
  obtain ⟨x, hx, hvar⟩ := coercive_operator_exists B ε hε hB (f + ε • v₀)
    K hne hclosed hconvex
  refine ⟨x, hx, fun v hv => ?_⟩
  have hid : B x - (f + ε • v₀) = A x - f + ε • (x - v₀) := by
    simp only [B, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_sub]
    abel
  simpa only [hid] using hvar v hv

omit [InnerProductSpace ℝ H] in
/-- A square-distance control by increments of a bounded real sequence gives
norm Cauchy convergence. -/
theorem cauchySeq_of_square_distance_control (x : ℕ → H) (v₀ : H)
    (hcontrol : ∀ m n : ℕ, m < n →
      ‖x m - x n‖ ^ 2 ≤ ‖x n - v₀‖ ^ 2 - ‖x m - v₀‖ ^ 2)
    (hbounded : BddAbove (Set.range fun n => ‖x n - v₀‖ ^ 2)) : CauchySeq x := by
  let q : ℕ → ℝ := fun n => ‖x n - v₀‖ ^ 2
  have hmono : Monotone q := by
    intro m n hmn
    rcases lt_or_eq_of_le hmn with hlt | rfl
    · have hc := hcontrol m n hlt
      have hn := sq_nonneg ‖x m - x n‖
      dsimp [q]
      linarith
    · exact le_rfl
  have hq : CauchySeq q := (tendsto_atTop_ciSup hmono hbounded).cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro δ hδ
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hq (δ ^ 2) (sq_pos_of_pos hδ)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hordered (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) (hij : i ≤ j) :
      dist (x i) (x j) < δ := by
    rcases lt_or_eq_of_le hij with hlt | rfl
    · have hc := hcontrol i j hlt
      have hs := hN j hj i hi
      rw [Real.dist_eq] at hs
      have hle := le_abs_self (q j - q i)
      dsimp [q] at hs hle
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (x i - x j)]
    · simpa only [dist_self] using hδ
  rcases le_total m n with hmn | hnm
  · exact hordered m n hm hn hmn
  · rw [dist_comm]
    exact hordered n m hn hm hnm

/-- Testing the regularized inequality at its center puts the solution in
exactly the bounded section of the hypothesis. -/
theorem regularized_mem_section (A : H →L[ℝ] H) (f v₀ x : H)
    (K : Set H) (hx : x ∈ K) (ε : ℝ) (hε : 0 ≤ ε)
    (hvar : 0 ≤ ⟪A x - f + ε • (x - v₀), v₀ - x⟫_ℝ) :
    x ∈ Spec.sectionSet A f K v₀ := by
  refine ⟨hx, ?_⟩
  have heq : v₀ - x = -(x - v₀) := by abel
  have hi : ⟪x - v₀, v₀ - x⟫_ℝ = -‖x - v₀‖ ^ 2 := by
    rw [heq, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [inner_add_left, real_inner_smul_left, hi] at hvar
  have := mul_nonneg hε (sq_nonneg ‖x - v₀‖)
  nlinarith

/-- Bounded-section existence, without a strict monotonicity hypothesis. -/
theorem bounded_section_exists : Spec.Existence.{u} := by
  classical
  intro H _ _ _ A hmono K hne hclosed hconvex f hsection
  obtain ⟨v₀, hv₀, hb⟩ := hsection
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlt (m n : ℕ) (hmn : m < n) : ε n < ε m := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · exact_mod_cast Nat.add_lt_add_right hmn 1
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose x hx hvar using fun n =>
    regularized_exists A hmono f v₀ K hne hclosed hconvex (ε n) (hε n)
  have hxsection (n : ℕ) : x n ∈ Spec.sectionSet A f K v₀ :=
    regularized_mem_section A f v₀ (x n) K (hx n) (ε n) (hε n).le (hvar n v₀ hv₀)
  have hcontrol (m n : ℕ) (hmn : m < n) :
      ‖x m - x n‖ ^ 2 ≤ ‖x n - v₀‖ ^ 2 - ‖x m - v₀‖ ^ 2 :=
    regularized_distance_bound A hmono f v₀ (x m) (x n) (ε m) (ε n)
      (hε n) (hεlt m n hmn) (hvar m (x n) (hx n)) (hvar n (x m) (hx m))
  obtain ⟨R, hR, hnorm⟩ := hb.exists_pos_norm_le
  have hbounded : BddAbove (Set.range fun n => ‖x n - v₀‖ ^ 2) := by
    refine ⟨(R + ‖v₀‖) ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hn := hnorm (x n) (hxsection n)
    have hsub := norm_sub_le (x n) v₀
    nlinarith [norm_nonneg (x n - v₀), norm_nonneg v₀]
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_square_distance_control x v₀ hcontrol hbounded)
  refine ⟨u, hclosed.mem_of_tendsto hu (Eventually.of_forall hx), fun v hv => ?_⟩
  have hreg : Tendsto (fun n => ε n • (x n - v₀)) atTop (𝓝 (0 : H)) := by
    simpa only [zero_smul] using hεlim.smul (hu.sub_const v₀)
  have hlim : Tendsto
      (fun n => ⟪A (x n) - f + ε n • (x n - v₀), v - x n⟫_ℝ)
      atTop (𝓝 ⟪A u - f, v - u⟫_ℝ) := by
    simpa only [Function.comp_apply, add_zero] using
      (((A.continuous.tendsto u).comp hu).sub_const f |>.add hreg).inner
        (tendsto_const_nhds.sub hu)
  exact ge_of_tendsto' hlim (fun n => hvar n v hv)

/-- A bounded feasible set has a bounded section at any feasible point. -/
theorem bounded_set_section : Spec.BoundedSetSection.{u} := by
  intro H _ _ A f K hne hb
  obtain ⟨v₀, hv₀⟩ := hne
  exact ⟨v₀, hv₀, hb.subset (fun _ hx => hx.1)⟩

/-- Coercivity bounds the section, even if the feasible set is unbounded. -/
theorem coercive_section : Spec.CoerciveSection.{u} := by
  intro H _ _ A α hα hcoerc f K hne
  obtain ⟨v₀, hv₀⟩ := hne
  refine ⟨v₀, hv₀, isBounded_iff_forall_norm_le.mpr ?_⟩
  refine ⟨‖f - A v₀‖ / α + ‖v₀‖, fun x hx => ?_⟩
  have hs := hx.2
  have heq : v₀ - x = -(x - v₀) := by abel
  rw [heq, inner_neg_right] at hs
  have hc := hcoerc (x - v₀)
  have hi : ⟪A (x - v₀), x - v₀⟫_ℝ =
      ⟪A x - f, x - v₀⟫_ℝ + ⟪f - A v₀, x - v₀⟫_ℝ := by
    rw [map_sub]
    simp only [inner_sub_left]
    ring
  rw [hi] at hc
  have hcs := real_inner_le_norm (f - A v₀) (x - v₀)
  have hbound : ‖x - v₀‖ ≤ ‖f - A v₀‖ / α := by
    apply (le_div_iff₀ hα).mpr
    by_cases hz : ‖x - v₀‖ = 0
    · simp only [hz, zero_mul]
      exact norm_nonneg _
    · have hp : 0 < ‖x - v₀‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  have hn := norm_add_le (x - v₀) v₀
  rw [sub_add_cancel] at hn
  linarith

end ExpandedFA.Geometry.BoundedSectionVariationalInequality
