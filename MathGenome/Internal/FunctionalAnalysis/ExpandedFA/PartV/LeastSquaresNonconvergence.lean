import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.LeastSquaresNonconvergence
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-! An exact-data counterexample to convergence of unregularized least
squares (`fa2:p5:least-squares-nonconvergence`). Compactness is proved by
finite-rank truncations. Projection onto each finite-dimensional image gives
the unique minimizer; its normal equations yield the explicit error bound.
All constructions use the same zero-indexed real or complex ℓ² space. -/

noncomputable section
set_option maxHeartbeats 1000000
universe u
namespace ExpandedFA.PartV.LeastSquaresNonconvergence
open Filter
open scoped Topology InnerProductSpace ENNReal
open Spec

lemma q_pos (j : ℕ) : 0 < q j := by unfold q; positivity
lemma q_le_one (j : ℕ) : q j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
lemma q_tendsto : Tendsto q atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

@[simp] lemma eigenvalue_zero : eigenvalue 0 = 0 := by simp [eigenvalue]
@[simp] lemma eigenvalue_one : eigenvalue 1 = 1 := by simp [eigenvalue]
lemma eigenvalue_pos {j : ℕ} (hj : 0 < j) : 0 < eigenvalue j := by
  unfold eigenvalue
  split_ifs <;> first | positivity | exact q_pos _ | omega
lemma eigenvalue_nonneg (j : ℕ) : 0 ≤ eigenvalue j := by
  rcases j with _ | j
  · simp
  · exact (eigenvalue_pos (Nat.succ_pos _)).le
lemma eigenvalue_le_one (j : ℕ) : eigenvalue j ≤ 1 := by
  unfold eigenvalue
  split_ifs <;> try norm_num
  all_goals exact q_le_one _

lemma eigenvalue_le_q_half (j : ℕ) : eigenvalue j ≤ q (j / 2) := by
  unfold eigenvalue
  split_ifs with h0 h1 he
  · exact (q_pos _).le
  · subst j; norm_num [q]
  · unfold q
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    nlinarith [Nat.zero_le (j / 2), Nat.le_mul_self (j / 2)]
  · rfl

lemma eigenvalue_tendsto : Tendsto eigenvalue atTop (𝓝 0) := by
  apply squeeze_zero eigenvalue_nonneg eigenvalue_le_q_half
  exact q_tendsto.comp (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))

lemma eigenvalue_even (k : ℕ) (hk : 1 ≤ k) : eigenvalue (2*k) = q (k^2) := by
  have h0 : 2*k ≠ 0 := by omega
  have h1 : 2*k ≠ 1 := by omega
  simp [eigenvalue, h0, h1]
lemma eigenvalue_odd (k : ℕ) (hk : 1 ≤ k) : eigenvalue (2*k+1) = q k := by
  have h0 : 2*k+1 ≠ 0 := by omega
  have h1 : 2*k+1 ≠ 1 := by omega
  simp only [eigenvalue, ite_eq_right h0, ite_eq_right h1]
  have hm : (2*k+1) % 2 ≠ 0 := by omega
  rw [ite_eq_right hm, show (2*k+1)/2 = k by omega]

section Construction
variable (𝕜 : Type u) [RCLike 𝕜]

lemma profile_mem : Memℓp (fun j : ℕ => (q j : 𝕜)) 2 := by
  apply memℓp_gen
  have h : Summable (fun j : ℕ => (1/4 : ℝ)^j) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  convert h using 1
  ext j
  simp only [RCLike.norm_ofReal, abs_of_pos (q_pos j), ENNReal.toReal_ofNat,
    Real.rpow_two]
  unfold q
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num

def profile : Space 𝕜 := ⟨_, profile_mem 𝕜⟩
@[simp] lemma profile_apply (j : ℕ) : profile 𝕜 j = (q j : 𝕜) := rfl

/-- The coordinate definition is the actual norm-convergent basis series
in the manuscript, with the zeroth basis vector separated out. -/
lemma profile_series :
    HasSum (fun j : ℕ => (lp.single 2 (j+1) (q (j+1) : 𝕜) : Space 𝕜))
      (profile 𝕜 - lp.single 2 0 1) := by
  have h := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (profile 𝕜)
  have ht := (hasSum_nat_add_iff' 1).mpr h
  simpa only [profile_apply, Finset.sum_range_one, q, pow_zero,
    div_pow, one_pow, one_div_one, RCLike.ofReal_one] using ht

lemma diagonal_coordinate_bound (x : Space 𝕜) (j : ℕ) :
    ‖(eigenvalue j : 𝕜) * x j‖ ≤ ‖x j‖ := by
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (eigenvalue_nonneg j)]
  exact mul_le_of_le_one_left (norm_nonneg _) (eigenvalue_le_one j)

def diagonal : Space 𝕜 →L[𝕜] Space 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => (eigenvalue j : 𝕜) * x j,
        (lp.memℓp x).mono' (diagonal_coordinate_bound 𝕜 x)⟩
      map_add' := fun x y => lp.ext (by funext j; exact mul_add _ _ _)
      map_smul' := fun c x => lp.ext (by funext j; exact mul_left_comm _ _ _) }
    1 (fun x => by
      simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (diagonal_coordinate_bound 𝕜 x))
@[simp] lemma diagonal_apply (x : Space 𝕜) (j : ℕ) :
    diagonal 𝕜 x j = (eigenvalue j : 𝕜) * x j := rfl

/-- The truncations retain zero through N-1. -/
def cut (N : ℕ) : Space 𝕜 →L[𝕜] Space 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => if j < N then x j else 0,
        (lp.memℓp x).mono' (fun j => by split_ifs <;> simp)⟩
      map_add' := fun x y => lp.ext (by
        funext j
        change (if j < N then x j + y j else 0) =
          (if j < N then x j else 0) + (if j < N then y j else 0)
        split_ifs <;> simp)
      map_smul' := fun c x => lp.ext (by
        funext j
        change (if j < N then c * x j else 0) = c * (if j < N then x j else 0)
        split_ifs <;> simp) }
    1 (fun x => by
      simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (show ∀ j, ‖if j < N then x j else 0‖ ≤ ‖x j‖ from
          fun j => by split_ifs <;> simp))
@[simp] lemma cut_apply (N : ℕ) (x : Space 𝕜) (j : ℕ) :
    cut 𝕜 N x j = if j < N then x j else 0 := rfl

lemma cut_finite_rank (N : ℕ) : FiniteDimensional 𝕜 (cut 𝕜 N).range := by
  let F : (cut 𝕜 N).range →ₗ[𝕜] (Fin N → 𝕜) :=
    { toFun := fun x i => x.val i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective F
  intro x y h
  apply Subtype.ext
  apply lp.ext
  funext j
  by_cases hj : j < N
  · exact congrFun h ⟨j, hj⟩
  · obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    have hx := congrArg (fun z : Space 𝕜 => z j) ha
    have hy := congrArg (fun z : Space 𝕜 => z j) hb
    change (if j < N then a j else 0) = x.val j at hx
    change (if j < N then b j else 0) = y.val j at hy
    rw [ite_eq_right hj] at hx hy
    exact hx.symm.trans hy

lemma cut_compact (N : ℕ) : IsCompactOperator (cut 𝕜 N) := by
  let := cut_finite_rank 𝕜 N
  have h : IsCompactOperator (cut 𝕜 N).rangeRestrict :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact h.continuous_comp continuous_subtype_val

lemma diagonal_tail_bound (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ j, N ≤ j → eigenvalue j ≤ ε) (x : Space 𝕜) :
    ‖(diagonal 𝕜 - (diagonal 𝕜).comp (cut 𝕜 N)) x‖ ≤ ε * ‖x‖ := by
  have hb : ‖(diagonal 𝕜 - (diagonal 𝕜).comp (cut 𝕜 N)) x‖ ≤ ‖ε • x‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    change ‖(eigenvalue j : 𝕜) * x j -
      (eigenvalue j : 𝕜) * (if j < N then x j else 0)‖ ≤ ‖ε • x j‖
    by_cases hj : j < N
    · simp [hj]
    · simp only [hj, ite_false, mul_zero, sub_zero, norm_mul,
        RCLike.norm_ofReal, abs_of_nonneg (eigenvalue_nonneg j),
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
      exact mul_le_mul_of_nonneg_right (h j (by omega)) (norm_nonneg _)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε] using hb

lemma diagonal_compact : IsCompactOperator (diagonal 𝕜) := by
  have hc (N : ℕ) : IsCompactOperator ((diagonal 𝕜).comp (cut 𝕜 N)) :=
    by
      simpa only [ContinuousLinearMap.coe_comp] using
        (cut_compact 𝕜 N).clm_comp (diagonal 𝕜)
  have ht : Tendsto (fun N => (diagonal 𝕜).comp (cut 𝕜 N)) atTop (𝓝 (diagonal 𝕜)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp eigenvalue_tendsto) (ε/2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (diagonal_tail_bound 𝕜 n (ε/2) (by positivity) ?_)) (by linarith)
    intro j hj
    have h := hN j (hn.trans hj)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (eigenvalue_nonneg j)] using h.le
  exact isClosed_setOfPred_isCompactOperator.mem_of_tendsto ht (Eventually.of_forall hc)

/-- The zeroth coordinate functional gives the manuscript's rank-one term. -/
def rankOne : Space 𝕜 →L[𝕜] Space 𝕜 :=
  (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 0).smulRight (profile 𝕜)

def operator : Space 𝕜 →L[𝕜] Space 𝕜 := diagonal 𝕜 + rankOne 𝕜

@[simp] lemma operator_apply (x : Space 𝕜) :
    operator 𝕜 x = diagonal 𝕜 x + x 0 • profile 𝕜 := rfl
/-- Evaluation at zero agrees with the stipulated inner product convention. -/
lemma operator_inner_formula (x : Space 𝕜) :
    operator 𝕜 x = diagonal 𝕜 x + ⟪(lp.single 2 0 1 : Space 𝕜), x⟫_𝕜 • profile 𝕜 := by
  rw [lp.inner_single_left]
  simpa only [RCLike.inner_apply, map_one, mul_one] using operator_apply 𝕜 x

@[simp] lemma operator_coordinate (x : Space 𝕜) (j : ℕ) :
    operator 𝕜 x j = (eigenvalue j : 𝕜) * x j + x 0 * (q j : 𝕜) := rfl
@[simp] lemma operator_zero_coordinate (x : Space 𝕜) : operator 𝕜 x 0 = x 0 := by
  rw [operator_coordinate, eigenvalue_zero]
  simp [q]

lemma rankOne_compact : IsCompactOperator (rankOne 𝕜) := by
  have h : IsCompactOperator (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 0) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact h.clm_comp ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (profile 𝕜))

lemma operator_compact : IsCompactOperator (operator 𝕜) :=
  (diagonal_compact 𝕜).add (rankOne_compact 𝕜)

lemma operator_injective : Function.Injective (operator 𝕜) := by
  intro x y h
  have h0 : x 0 = y 0 := by
    simpa only [operator_zero_coordinate] using congrArg (fun z : Space 𝕜 => z 0) h
  apply lp.ext
  funext j
  by_cases hj : j = 0
  · simpa [hj] using h0
  · have hh := congrArg (fun z : Space 𝕜 => z j) h
    simp only [operator_coordinate, h0, add_left_inj] at hh
    exact mul_left_cancel₀ (show (eigenvalue j : 𝕜) ≠ 0 from
      RCLike.ofReal_ne_zero.mpr (ne_of_gt (eigenvalue_pos (by omega)))) hh

lemma operator_single_positive (j : ℕ) (hj : 0 < j) (a : 𝕜) :
    operator 𝕜 (lp.single 2 j a) = lp.single 2 j ((eigenvalue j : 𝕜) * a) := by
  apply lp.ext
  funext m
  rw [operator_coordinate]
  have h0 : (lp.single 2 j a : Space 𝕜) 0 = 0 := lp.single_apply_ne _ _ _ (by omega)
  rw [h0, zero_mul, add_zero]
  by_cases hm : m = j
  · subst m; simp
  · rw [lp.single_apply_ne _ _ _ hm, lp.single_apply_ne _ _ _ hm, mul_zero]

lemma operator_e0 : operator 𝕜 (lp.single 2 0 1) = profile 𝕜 := by
  apply lp.ext
  funext j
  rw [operator_coordinate]
  by_cases hj : j = 0
  · subst j; simp [q]
  · rw [lp.single_apply_ne _ _ _ hj]
    simp

lemma operator_denseRange : DenseRange (operator 𝕜) := by
  change Dense ((operator 𝕜).range : Set (Space 𝕜))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro y hy
  change y = 0
  have hpos (j : ℕ) (hj : 0 < j) : y j = 0 := by
    have he : (lp.single 2 j 1 : Space 𝕜) ∈ (operator 𝕜).range := by
      refine ⟨lp.single 2 j ((eigenvalue j : 𝕜)⁻¹), ?_⟩
      change operator 𝕜 _ = _
      rw [operator_single_positive 𝕜 j hj, mul_inv_cancel₀
        (RCLike.ofReal_ne_zero.mpr (ne_of_gt (eigenvalue_pos hj)))]
    have h := (Submodule.mem_orthogonal _ _).mp hy _ he
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, one_mul, mul_one] using h
  have hys : y = lp.single 2 0 (y 0) := by
    apply lp.ext
    funext j
    by_cases hj : j = 0
    · subst j; simp
    · rw [hpos j (by omega), lp.single_apply_ne _ _ _ hj]
  have he : profile 𝕜 ∈ (operator 𝕜).range := ⟨lp.single 2 0 1, operator_e0 𝕜⟩
  have h := (Submodule.mem_orthogonal _ _).mp hy _ he
  rw [hys, lp.inner_single_right] at h
  have h0 : y 0 = 0 := by simpa [profile_apply, q, RCLike.inner_apply] using h
  rw [hys, h0, lp.single_zero]

theorem operator_construction : Spec.OperatorConstruction.{u} := by
  intro 𝕜 _
  exact ⟨profile 𝕜, diagonal 𝕜, operator 𝕜, profile_apply 𝕜,
    diagonal_apply 𝕜, operator_apply 𝕜, diagonal_compact 𝕜,
    operator_compact 𝕜, operator_injective 𝕜, operator_denseRange 𝕜⟩

lemma single_mem_trials (n j : ℕ) (hj : j ≤ n) (a : 𝕜) :
    (lp.single 2 j a : Space 𝕜) ∈ trials 𝕜 n := by
  have h : (lp.single 2 j 1 : Space 𝕜) ∈ trials 𝕜 n :=
    Submodule.subset_span ⟨j, hj, rfl⟩
  simpa only [← lp.single_smul, smul_eq_mul, mul_one] using
    (trials 𝕜 n).smul_mem a h

lemma trials_finite (n : ℕ) : FiniteDimensional 𝕜 (trials 𝕜 n) := by
  apply FiniteDimensional.span_of_finite
  exact (Set.finite_Iic n).image _

lemma trials_mono : Monotone (trials 𝕜) := by
  intro m n hmn
  apply Submodule.span_mono
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans hmn, rfl⟩

lemma mem_trials_iff (n : ℕ) (x : Space 𝕜) :
    x ∈ trials 𝕜 n ↔ ∀ j, n < j → x j = 0 := by
  constructor
  · intro hx j hj
    apply Submodule.span_induction (p := fun x _ => x j = 0) _ _ _ _ hx
    · rintro _ ⟨i, hi, rfl⟩
      change i ≤ n at hi
      exact lp.single_apply_ne _ _ _ (by omega)
    · rfl
    · intro a b _ _ ha hb
      change a j + b j = 0
      rw [ha, hb, add_zero]
    · intro c a _ ha
      change c * a j = 0
      rw [ha, mul_zero]
  · intro hx
    have heq : x = ∑ j ∈ Finset.range (n+1), lp.single 2 j (x j) := by
      apply lp.ext
      funext j
      simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
      by_cases hj : j ≤ n
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hbj
          exact Pi.single_eq_of_ne (Ne.symm hbj) _
        · intro hn
          exact False.elim (hn (Finset.mem_range.mpr (by omega)))
      · rw [hx j (by omega)]
        symm
        apply Finset.sum_eq_zero
        intro i hi
        exact Pi.single_eq_of_ne (by have := Finset.mem_range.mp hi; omega) _
    rw [heq]
    apply Submodule.sum_mem
    intro j hj
    exact single_mem_trials 𝕜 n j (by have := Finset.mem_range.mp hj; omega) _

lemma cut_eq_sum (N : ℕ) (x : Space 𝕜) :
    cut 𝕜 N x = ∑ j ∈ Finset.range N, lp.single 2 j (x j) := by
  apply lp.ext
  funext j
  simp only [cut_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  by_cases hj : j < N
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; exact Pi.single_eq_of_ne (Ne.symm hbj) _
    · intro h; exact False.elim (h (Finset.mem_range.mpr hj))
  · rw [ite_eq_right hj]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact Pi.single_eq_of_ne (by have := Finset.mem_range.mp hi; omega) _

lemma cut_tendsto (x : Space 𝕜) : Tendsto (fun N => cut 𝕜 N x) atTop (𝓝 x) := by
  simp_rw [cut_eq_sum]
  exact (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat

lemma trials_dense : Dense (⋃ n, (trials 𝕜 n : Set (Space 𝕜))) := by
  intro x
  apply mem_closure_of_tendsto (cut_tendsto 𝕜 x)
  apply Eventually.of_forall
  intro n
  apply Set.mem_iUnion.mpr
  refine ⟨n, (mem_trials_iff 𝕜 n _).mpr ?_⟩
  intro j hj
  rw [cut_apply, ite_eq_right (by omega)]

end Construction

theorem trial_properties : Spec.TrialProperties.{u} := by
  intro 𝕜 _
  exact ⟨trials_finite 𝕜, trials_mono 𝕜, trials_dense 𝕜⟩

section Minimizers
variable (𝕜 : Type u) [RCLike 𝕜]

/-- The finite-dimensional image space, where nearest-point projection is
available even though the full operator has nonclosed range. -/
def trialImage (n : ℕ) : Submodule 𝕜 (Space 𝕜) :=
  (trials 𝕜 n).map (operator 𝕜).toLinearMap

instance trialImage_finite (n : ℕ) : FiniteDimensional 𝕜 (trialImage 𝕜 n) := by
  let := trials_finite 𝕜 n
  exact Module.Finite.map _ _

lemma minimizer_iff_orthogonal (T : Space 𝕜 →L[𝕜] Space 𝕜) (f x : Space 𝕜) (n : ℕ) :
    IsMinimizer T f n x ↔
      x ∈ trials 𝕜 n ∧ ∀ y ∈ trials 𝕜 n, ⟪T x - f, T y⟫_𝕜 = 0 := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    have him : T x ∈ ((trials 𝕜 n).map T.toLinearMap) := ⟨x, hx, rfl⟩
    have heq : ‖f - T x‖ = ⨅ y : ((trials 𝕜 n).map T.toLinearMap), ‖f - y‖ := by
      apply le_antisymm
      · apply le_ciInf
        rintro ⟨z, y, hy, rfl⟩
        simpa only [ContinuousLinearMap.coe_coe, norm_sub_rev] using hmin y hy
      · exact ciInf_le (show BddBelow (Set.range
          (fun w : (trials 𝕜 n).map T.toLinearMap => ‖f - w‖)) from
            ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩) ⟨T x, him⟩
    have ho := ((((trials 𝕜 n).map T.toLinearMap)).norm_eq_iInf_iff_inner_eq_zero him).mp heq
    intro y hy
    have hh := ho _ ⟨y, hy, rfl⟩
    simpa only [ContinuousLinearMap.coe_coe, ← neg_sub (f), inner_neg_left, neg_eq_zero] using hh
  · rintro ⟨hx, ho⟩
    refine ⟨hx, fun y hy => ?_⟩
    have him : T x ∈ ((trials 𝕜 n).map T.toLinearMap) := ⟨x, hx, rfl⟩
    have heq := ((((trials 𝕜 n).map T.toLinearMap)).norm_eq_iInf_iff_inner_eq_zero him).mpr (by
      rintro _ ⟨z, hz, rfl⟩
      have hh := ho z hz
      simpa only [ContinuousLinearMap.coe_coe, ← neg_sub (T x), inner_neg_left, neg_eq_zero] using hh)
    have hle : ‖f - T x‖ ≤ ‖f - T y‖ := by
      rw [heq]
      exact ciInf_le (show BddBelow (Set.range
        (fun w : (trials 𝕜 n).map T.toLinearMap => ‖f - w‖)) from
          ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩) ⟨T y, y, hy, rfl⟩
    simpa only [norm_sub_rev] using hle

lemma projection_preimage (n : ℕ) (f : Space 𝕜) :
    ∃ x ∈ trials 𝕜 n, operator 𝕜 x = (trialImage 𝕜 n).starProjection f := by
  exact (Submodule.mem_map).mp ((trialImage 𝕜 n).starProjection_apply_mem f)

def approximant (n : ℕ) : Space 𝕜 :=
  Classical.choose (projection_preimage 𝕜 n (operator 𝕜 (profile 𝕜)))

lemma approximant_mem (n : ℕ) : approximant 𝕜 n ∈ trials 𝕜 n :=
  (Classical.choose_spec (projection_preimage 𝕜 n (operator 𝕜 (profile 𝕜)))).1

lemma approximant_image (n : ℕ) : operator 𝕜 (approximant 𝕜 n) =
    (trialImage 𝕜 n).starProjection (operator 𝕜 (profile 𝕜)) :=
  (Classical.choose_spec (projection_preimage 𝕜 n (operator 𝕜 (profile 𝕜)))).2

lemma approximant_minimizer (n : ℕ) :
    IsMinimizer (operator 𝕜) (operator 𝕜 (profile 𝕜)) n (approximant 𝕜 n) := by
  apply (minimizer_iff_orthogonal 𝕜 (operator 𝕜) _ _ _).mpr
  refine ⟨approximant_mem 𝕜 n, fun y hy => ?_⟩
  rw [approximant_image]
  have hh := (trialImage 𝕜 n).starProjection_inner_eq_zero
    (operator 𝕜 (profile 𝕜)) (operator 𝕜 y) ⟨y, hy, rfl⟩
  simpa only [← neg_sub ((trialImage 𝕜 n).starProjection _), inner_neg_left,
    neg_eq_zero] using hh

lemma minimizer_unique (T : Space 𝕜 →L[𝕜] Space 𝕜) (hT : Function.Injective T)
    (f : Space 𝕜) (n : ℕ) (x y : Space 𝕜)
    (hx : IsMinimizer T f n x) (hy : IsMinimizer T f n y) : x = y := by
  obtain ⟨hx, hxo⟩ := (minimizer_iff_orthogonal 𝕜 T _ _ _).mp hx
  obtain ⟨hy, hyo⟩ := (minimizer_iff_orthogonal 𝕜 T _ _ _).mp hy
  have hm := (trials 𝕜 n).sub_mem hx hy
  have hh : ⟪T (x-y), T (x-y)⟫_𝕜 = 0 := by
    have h : T (x-y) = (T x - f) - (T y - f) := by rw [map_sub]; abel
    rw [h, inner_sub_left, ← h, hxo _ hm, hyo _ hm, sub_self]
  have hzero : T (x-y) = 0 := inner_self_eq_zero.mp hh
  apply sub_eq_zero.mp
  apply hT
  simpa only [map_zero] using hzero

lemma approximant_unique (n : ℕ) (y : Space 𝕜)
    (hy : IsMinimizer (operator 𝕜) (operator 𝕜 (profile 𝕜)) n y) :
    y = approximant 𝕜 n :=
  minimizer_unique 𝕜 (operator 𝕜) (operator_injective 𝕜) _ n _ _ hy
    (approximant_minimizer 𝕜 n)

lemma cut_mem_trials (n : ℕ) (x : Space 𝕜) : cut 𝕜 (n+1) x ∈ trials 𝕜 n := by
  apply (mem_trials_iff 𝕜 n _).mpr
  intro j hj
  rw [cut_apply, ite_eq_right (by omega)]

lemma residual_tendsto :
    Tendsto (fun n => ‖operator 𝕜 (approximant 𝕜 n) - operator 𝕜 (profile 𝕜)‖)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun n => cut 𝕜 (n+1) (profile 𝕜)) atTop (𝓝 (profile 𝕜)) :=
    (cut_tendsto 𝕜 (profile 𝕜)).comp (tendsto_add_atTop_nat 1)
  have hS := (operator 𝕜).continuous.tendsto (profile 𝕜) |>.comp hc
  have hlim := (hS.sub (tendsto_const_nhds (x := operator 𝕜 (profile 𝕜)))).norm
  simp only [sub_self, norm_zero] at hlim
  apply squeeze_zero (fun n => norm_nonneg _) _ hlim
  intro n
  exact (approximant_minimizer 𝕜 n).2 _ (cut_mem_trials 𝕜 n _)

lemma normal_positive (n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    (eigenvalue j : 𝕜) * (approximant 𝕜 n j - profile 𝕜 j) =
      (1 - approximant 𝕜 n 0) * profile 𝕜 j := by
  have hh := ((minimizer_iff_orthogonal 𝕜 (operator 𝕜) _ _ _).mp
    (approximant_minimizer 𝕜 n)).2 _ (single_mem_trials 𝕜 n j hjn 1)
  rw [inner_eq_zero_symm, operator_single_positive 𝕜 j hj, mul_one,
    lp.inner_single_left, RCLike.inner_apply, RCLike.conj_ofReal] at hh
  have hj0 : (eigenvalue j : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (ne_of_gt (eigenvalue_pos hj))
  have hr := (mul_eq_zero.mp hh).resolve_right hj0
  change operator 𝕜 (approximant 𝕜 n) j - operator 𝕜 (profile 𝕜) j = 0 at hr
  simp only [operator_coordinate, profile_apply] at hr ⊢
  have hq : (q 0 : 𝕜) = 1 := by norm_num [q]
  rw [hq, one_mul] at hr
  linear_combination hr

/-- The actual residual vector, for the solvable datum Sg. -/
def residual (n : ℕ) : Space 𝕜 := operator 𝕜 (approximant 𝕜 n) - operator 𝕜 (profile 𝕜)

lemma residual_zero (n : ℕ) : residual 𝕜 n 0 = approximant 𝕜 n 0 - 1 := by
  change operator 𝕜 (approximant 𝕜 n) 0 - operator 𝕜 (profile 𝕜) 0 = _
  rw [operator_zero_coordinate, operator_zero_coordinate]
  norm_num [profile_apply, q]

lemma residual_inside (n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) : residual 𝕜 n j = 0 := by
  have hh := normal_positive 𝕜 n j hj hjn
  change operator 𝕜 (approximant 𝕜 n) j - operator 𝕜 (profile 𝕜) j = 0
  simp only [operator_coordinate, profile_apply] at hh ⊢
  have hq : (q 0 : 𝕜) = 1 := by norm_num [q]
  rw [hq, one_mul]
  linear_combination hh

lemma residual_outside (n j : ℕ) (hj : n < j) :
    residual 𝕜 n j = (approximant 𝕜 n 0 - 1) * (q j : 𝕜) -
      (eigenvalue j : 𝕜) * (q j : 𝕜) := by
  have hx := (mem_trials_iff 𝕜 n _).mp (approximant_mem 𝕜 n) j hj
  change operator 𝕜 (approximant 𝕜 n) j - operator 𝕜 (profile 𝕜) j = _
  rw [operator_coordinate, operator_coordinate, hx, profile_apply, profile_apply]
  norm_num [q]
  ring

lemma profile_inner_residual (n : ℕ) : ⟪profile 𝕜, residual 𝕜 n⟫_𝕜 = 0 := by
  have h := ((minimizer_iff_orthogonal 𝕜 (operator 𝕜) _ _ _).mp
    (approximant_minimizer 𝕜 n)).2 _ (single_mem_trials 𝕜 n 0 (Nat.zero_le _) 1)
  rw [operator_e0, inner_eq_zero_symm] at h
  exact h

end Minimizers

lemma q_square_summable : Summable (fun j => q j ^ 2) := by
  have h := (lp.memℓp (profile ℝ)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [profile_apply, RCLike.norm_ofReal, abs_of_pos (q_pos _),
    ENNReal.toReal_ofNat, Real.rpow_two] using h

lemma weighted_square_summable : Summable (fun j => eigenvalue j * q j ^ 2) := by
  exact Summable.of_nonneg_of_le (fun j => mul_nonneg (eigenvalue_nonneg j) (sq_nonneg _))
    (fun j => mul_le_of_le_one_left (sq_nonneg _) (eigenvalue_le_one j)) q_square_summable

lemma tailSquare_summable (n : ℕ) : Summable (fun j : {j : ℕ // n < j} => q j.val ^ 2) :=
  q_square_summable.subtype _
lemma tailWeighted_summable (n : ℕ) :
    Summable (fun j : {j : ℕ // n < j} => eigenvalue j.val * q j.val ^ 2) :=
  weighted_square_summable.subtype _

/-- A convenient tail form of the ordinary finite-prefix identity. Keeping
this lemma independent of lp avoids unfolding its dependent function coercion
inside a simplification under subtype sums. -/
lemma sum_prefix_add_tail {𝕜 : Type u} [RCLike 𝕜] (F : ℕ → 𝕜)
    (hF : Summable F) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), F j) + (∑' j : {j : ℕ // n < j}, F j.val) =
      ∑' j, F j := by
  have h := hF.sum_add_tsum_subtype_compl (Finset.range (n+1))
  have htail : (∑' j : {j : ℕ // j ∉ Finset.range (n+1)}, F j.val) =
      ∑' j : {j : ℕ // n < j}, F j.val :=
    tsum_congr_subtype F (fun j => by simp only [Finset.mem_range, not_lt, Nat.succ_le_iff])
  rw [htail] at h
  exact h

section NormalZero
variable (𝕜 : Type u) [RCLike 𝕜]

lemma inner_tail_formula (n : ℕ) (j : {j : ℕ // n < j}) :
    ⟪profile 𝕜 j.val, residual 𝕜 n j.val⟫_𝕜 =
      (approximant 𝕜 n 0 - 1) * ((q j.val ^ 2 : ℝ) : 𝕜) -
        ((eigenvalue j.val * q j.val ^ 2 : ℝ) : 𝕜) := by
  rw [profile_apply, residual_outside 𝕜 n j.val j.property]
  simp only [RCLike.inner_apply, RCLike.conj_ofReal, RCLike.ofReal_mul, RCLike.ofReal_pow]
  ring

lemma inner_prefix_formula (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), ⟪profile 𝕜 j, residual 𝕜 n j⟫_𝕜) =
      approximant 𝕜 n 0 - 1 := by
  rw [Finset.sum_eq_single 0]
  · rw [profile_apply, residual_zero]
    norm_num [q, RCLike.inner_apply]
  · intro j hj hj0
    rw [residual_inside 𝕜 n j (by omega) (by have := Finset.mem_range.mp hj; omega)]
    simp
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

lemma normal_zero (n : ℕ) :
    (approximant 𝕜 n 0 - 1) * ((1 + tailSquare n : ℝ) : 𝕜) =
      (tailWeighted n : 𝕜) := by
  have hseries : Summable (fun j : ℕ => ⟪profile 𝕜 j, residual 𝕜 n j⟫_𝕜) :=
    lp.summable_inner (𝕜 := 𝕜) (profile 𝕜) (residual 𝕜 n)
  have hs := sum_prefix_add_tail _ hseries n
  rw [← lp.inner_eq_tsum, profile_inner_residual, inner_prefix_formula] at hs
  have htail : (∑' j : {j : ℕ // n < j}, ⟪profile 𝕜 j.val, residual 𝕜 n j.val⟫_𝕜) =
      (approximant 𝕜 n 0 - 1) * (tailSquare n : 𝕜) - (tailWeighted n : 𝕜) := by
    simp_rw [inner_tail_formula]
    have hq := ((RCLike.hasSum_ofReal 𝕜).mpr (tailSquare_summable n).hasSum)
    have hw := ((RCLike.hasSum_ofReal 𝕜).mpr (tailWeighted_summable n).hasSum)
    exact ((hq.mul_left (approximant 𝕜 n 0 - 1)).sub hw).tsum_eq
  rw [htail] at hs
  simp only [RCLike.ofReal_add, RCLike.ofReal_one]
  linear_combination hs

end NormalZero

lemma tailSquare_nonneg (n : ℕ) : 0 ≤ tailSquare n :=
  tsum_nonneg (fun _ => sq_nonneg _)
lemma tailWeighted_nonneg (n : ℕ) : 0 ≤ tailWeighted n :=
  tsum_nonneg (fun _j => mul_nonneg (eigenvalue_nonneg _) (sq_nonneg _))

lemma tailWeighted_ge_next (n : ℕ) :
    eigenvalue (n+1) * q (n+1) ^ 2 ≤ tailWeighted n := by
  exact (tailWeighted_summable n).le_tsum ⟨n+1, by omega⟩
    (fun j _ => mul_nonneg (eigenvalue_nonneg _) (sq_nonneg _))

section ErrorBound
variable (𝕜 : Type u) [RCLike 𝕜]

lemma profile_norm_square : ‖profile 𝕜‖ ^ 2 = ∑' j, q j ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (profile 𝕜)
  simpa only [profile_apply, RCLike.norm_ofReal, abs_of_pos (q_pos _),
    ENNReal.toReal_ofNat, Real.rpow_two] using h

lemma tailSquare_le_norm (n : ℕ) : tailSquare n ≤ ‖profile 𝕜‖ ^ 2 := by
  have h := sum_prefix_add_tail _ q_square_summable n
  rw [profile_norm_square]
  change (∑' j : {j : ℕ // n < j}, q j.val ^ 2) ≤ _
  linarith [Finset.sum_nonneg (s := Finset.range (n+1)) (fun j _ => sq_nonneg (q j))]

lemma zero_correction (n : ℕ) :
    approximant 𝕜 n 0 - 1 = ((tailWeighted n / (1 + tailSquare n) : ℝ) : 𝕜) := by
  have hden : 0 < 1 + tailSquare n := by linarith [tailSquare_nonneg n]
  rw [RCLike.ofReal_div]
  apply (eq_div_iff (RCLike.ofReal_ne_zero.mpr hden.ne')).mpr
  exact normal_zero 𝕜 n

lemma correction_lower (n : ℕ) :
    eigenvalue (n+1) * q (n+1) ^ 2 / (1 + ‖profile 𝕜‖ ^ 2) ≤
      tailWeighted n / (1 + tailSquare n) := by
  have hden : 0 < 1 + tailSquare n := by linarith [tailSquare_nonneg n]
  calc
    eigenvalue (n+1) * q (n+1)^2 / (1 + ‖profile 𝕜‖^2) ≤
        tailWeighted n / (1 + ‖profile 𝕜‖^2) := by
      gcongr
      exact tailWeighted_ge_next n
    _ ≤ tailWeighted n / (1 + tailSquare n) :=
      div_le_div_of_nonneg_left (tailWeighted_nonneg n) hden
        (by linarith [tailSquare_le_norm 𝕜 n])

lemma coordinate_error (n : ℕ) (hn : 0 < n) :
    ‖approximant 𝕜 n n - profile 𝕜 n‖ =
      (tailWeighted n / (1 + tailSquare n)) * q n / eigenvalue n := by
  have he := normal_positive 𝕜 n n hn le_rfl
  have hc : 1 - approximant 𝕜 n 0 =
      -((tailWeighted n / (1 + tailSquare n) : ℝ) : 𝕜) := by
    rw [← zero_correction]; ring
  rw [hc, profile_apply] at he
  have hh := congrArg norm he
  have hcorr : 0 ≤ tailWeighted n / (1 + tailSquare n) :=
    div_nonneg (tailWeighted_nonneg n) (by linarith [tailSquare_nonneg n])
  simp only [norm_mul, norm_neg, RCLike.norm_ofReal,
    abs_of_pos (eigenvalue_pos hn), abs_of_pos (q_pos n), abs_of_nonneg hcorr] at hh
  rw [profile_apply]
  apply (eq_div_iff (eigenvalue_pos hn).ne').mpr
  nlinarith only [hh]

lemma error_lower_bound (n : ℕ) (hn : 0 < n) :
    eigenvalue (n+1) * q (n+1) ^ 2 * q n /
      ((1 + ‖profile 𝕜‖ ^ 2) * eigenvalue n) ≤ ‖approximant 𝕜 n - profile 𝕜‖ := by
  calc
    eigenvalue (n+1) * q (n+1) ^ 2 * q n /
        ((1 + ‖profile 𝕜‖ ^ 2) * eigenvalue n) =
      (eigenvalue (n+1) * q (n+1) ^ 2 / (1 + ‖profile 𝕜‖ ^ 2)) * q n /
        eigenvalue n := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ (tailWeighted n / (1 + tailSquare n)) * q n / eigenvalue n := by
      apply div_le_div_of_nonneg_right _ (eigenvalue_pos hn).le
      exact mul_le_mul_of_nonneg_right (correction_lower 𝕜 n) (q_pos n).le
    _ = ‖approximant 𝕜 n n - profile 𝕜 n‖ := (coordinate_error 𝕜 n hn).symm
    _ ≤ ‖approximant 𝕜 n - profile 𝕜‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (approximant 𝕜 n - profile 𝕜) n

end ErrorBound

lemma q_eq_zpow (j : ℕ) : q j = (2 : ℝ) ^ (-(j : ℤ)) := by
  simp [q, one_div, inv_pow]

lemma even_lower_factor (k : ℕ) (hk : 1 ≤ k) :
    eigenvalue (2*k+1) * q (2*k+1)^2 * q (2*k) / eigenvalue (2*k) =
      (2 : ℝ) ^ ((k : ℤ)^2 - 7*(k : ℤ)-2) := by
  rw [eigenvalue_odd k hk, eigenvalue_even k hk]
  simp only [q_eq_zpow]
  have hz : (2 : ℝ) ≠ 0 := by norm_num
  rw [← zpow_natCast _ 2, ← zpow_mul, ← zpow_add₀ hz, ← zpow_add₀ hz, ← zpow_sub₀ hz]
  congr 1
  push_cast
  ring

section Divergence
variable (𝕜 : Type u) [RCLike 𝕜]

lemma even_error_lower (k : ℕ) (hk : 1 ≤ k) :
    (1 / (1 + ‖profile 𝕜‖^2)) * (2 : ℝ) ^ ((k : ℤ)^2 - 7*(k : ℤ)-2) ≤
      ‖approximant 𝕜 (2*k) - profile 𝕜‖ := by
  rw [← even_lower_factor k hk]
  calc
    (1 / (1 + ‖profile 𝕜‖^2)) *
        (eigenvalue (2*k+1) * q (2*k+1)^2 * q (2*k) / eigenvalue (2*k)) =
      eigenvalue (2*k+1) * q (2*k+1)^2 * q (2*k) /
        ((1 + ‖profile 𝕜‖^2) * eigenvalue (2*k)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ ‖approximant 𝕜 (2*k) - profile 𝕜‖ := error_lower_bound 𝕜 _ (by omega)

lemma even_error_tendsto :
    Tendsto (fun k => ‖approximant 𝕜 (2*k) - profile 𝕜‖) atTop atTop := by
  have hc : 0 < 1 / (1 + ‖profile 𝕜‖^2) := by positivity
  have ht : Tendsto (fun k : ℕ => (1 / (1 + ‖profile 𝕜‖^2)) * (2 : ℝ)^k)
      atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (9 : ℕ)] with k hk
  have hkz : (9 : ℤ) ≤ k := by exact_mod_cast hk
  have he : (k : ℤ) ≤ (k : ℤ)^2 - 7*(k : ℤ)-2 := by nlinarith
  calc
    (1 / (1 + ‖profile 𝕜‖^2)) * (2 : ℝ)^k ≤
        (1 / (1 + ‖profile 𝕜‖^2)) * (2 : ℝ)^((k : ℤ)^2 - 7*(k : ℤ)-2) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      rw [← zpow_natCast]
      exact zpow_le_zpow_right₀ (by norm_num) he
    _ ≤ ‖approximant 𝕜 (2*k) - profile 𝕜‖ := even_error_lower 𝕜 k (by omega)

end Divergence

/-- The manuscript's compact, injective dense-range exact-data example over
both allowed scalar fields. -/
theorem least_squares_nonconvergence : Spec.LeastSquaresNonconvergence.{u} := by
  intro 𝕜 _
  refine ⟨profile 𝕜, diagonal 𝕜, operator 𝕜, approximant 𝕜,
    profile_apply 𝕜, diagonal_apply 𝕜, operator_apply 𝕜, operator_compact 𝕜,
    operator_injective 𝕜, operator_denseRange 𝕜, ?_, residual_tendsto 𝕜,
    normal_positive 𝕜, normal_zero 𝕜, error_lower_bound 𝕜, ?_, even_error_tendsto 𝕜⟩
  · intro n
    exact ⟨approximant_minimizer 𝕜 n, approximant_unique 𝕜 n⟩
  · exact ⟨1 / (1 + ‖profile 𝕜‖^2), by positivity, even_error_lower 𝕜⟩

end ExpandedFA.PartV.LeastSquaresNonconvergence
