import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CompactContinuity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.NormEquivalence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology Asymptotics
open scoped BigOperators
namespace D04
open Specs.D04.C01.NormEquivalence.Model

private theorem seminorm_sum_le {n : ℕ} (N : Seminorm ℝ (E n))
    (s : Finset (Fin n)) (v : Fin n → E n) : N (∑ i ∈ s, v i) ≤ ∑ i ∈ s, N (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (map_add_le_add N (v i) (∑ j ∈ s, v j)).trans (add_le_add le_rfl ih)

private theorem seminorm_upper {n : ℕ} (N : Seminorm ℝ (E n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, N x ≤ C * ‖x‖ := by
  let C : ℝ := 1 + ∑ i, N (standardBasis n i)
  have hsum : 0 ≤ ∑ i, N (standardBasis n i) :=
    Finset.sum_nonneg fun i _ => apply_nonneg N _
  refine ⟨C, by dsimp [C]; positivity, fun x => ?_⟩
  have hx : x = ∑ i, x i • standardBasis n i := by
    ext j
    simp [standardBasis_apply]
  calc
    N x = N (∑ i, x i • standardBasis n i) := congrArg N hx
    _ ≤ ∑ i, N (x i • standardBasis n i) := seminorm_sum_le N Finset.univ _
    _ = ∑ i, ‖x i‖ * N (standardBasis n i) := by simp only [map_smul_eq_mul]
    _ ≤ ∑ i, ‖x‖ * N (standardBasis n i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (apply_nonneg N _)
    _ = (∑ i, N (standardBasis n i)) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg x)

private theorem seminorm_continuous {n : ℕ} (N : Seminorm ℝ (E n)) : Continuous N := by
  obtain ⟨C, hC, hb⟩ := seminorm_upper N
  have hl : LipschitzWith ⟨C, hC.le⟩ N := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖N x - N y‖ ≤ C * ‖x - y‖
    exact
      (N.norm_sub_map_le_sub x y).trans (hb (x - y))
  exact hl.continuous

/-- Every definite real seminorm is bounded above and below by positive
multiples of the Euclidean norm. -/
theorem norm_equivalence {n : ℕ} (N : Seminorm ℝ (E n)) (hN : IsNorm N) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ N x ∧ N x ≤ C * ‖x‖ := by
  obtain ⟨C, hC, hupper⟩ := seminorm_upper N
  have hcompact : Compact {x : E n | ‖x‖ = 1} := by
    apply (compact_iff_closed_bounded _).mpr
    refine ⟨(closed_iff_isClosed _).mpr (isClosed_eq continuous_norm continuous_const),
      1, fun x hx => hx.le⟩
  obtain ⟨c, hc, hmin⟩ := ((compact_iff_isCompact _).mp hcompact).exists_forall_le'
    (seminorm_continuous N).continuousOn (a := 0) (by
      intro x hx
      apply lt_of_le_of_ne (apply_nonneg N x)
      intro hz
      have hx0 := hN x hz.symm
      simp [hx0] at hx)
  refine ⟨c, C, hc, hC, fun x => ⟨?_, hupper x⟩⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, hn.ne']
  have hb := hmin (‖x‖⁻¹ • x) hu
  rw [map_smul_eq_mul, norm_inv, Real.norm_of_nonneg (norm_nonneg x)] at hb
  calc
    c * ‖x‖ ≤ (‖x‖⁻¹ * N x) * ‖x‖ := mul_le_mul_of_nonneg_right hb hn.le
    _ = N x := by field_simp

theorem norm_equivalence_zero (N : Seminorm ℝ (E 0)) (x : E 0) :
    1 * ‖x‖ ≤ N x ∧ N x ≤ 1 * ‖x‖ := by
  rw [vector_dimension_zero x]
  simp

private theorem normTopology_isOpen_iff {n : ℕ} (N : Seminorm ℝ (E n)) (U : Set (E n)) :
    IsOpen[normTopology N] U ↔
      ∀ a ∈ U, ∃ ε > 0, ∀ b, N (b - a) < ε → b ∈ U := by
  have hd (x y : E n) :
      @dist _ N.toAddGroupSeminorm.toSeminormedAddCommGroup.toPseudoMetricSpace.toDist x y =
        N (x - y) := by
    change N (-x + y) = N (x - y)
    calc
      N (-x + y) = N (-(x - y)) := by congr 1; abel
      _ = N (x - y) := map_neg_eq_map N _
  have hm := @Metric.isOpen_iff (E n)
    N.toAddGroupSeminorm.toSeminormedAddCommGroup.toPseudoMetricSpace U
  change @IsOpen _ (normTopology N) U ↔ _ at hm
  simpa only [Set.subset_def, Metric.mem_ball, hd] using hm

theorem norm_topology_eq {n : ℕ} (N : Seminorm ℝ (E n)) (hN : IsNorm N) :
    normTopology N = (inferInstance : TopologicalSpace (E n)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := norm_equivalence N hN
  apply TopologicalSpace.ext
  funext U
  apply propext
  rw [normTopology_isOpen_iff, ← open_iff_isOpen]
  constructor
  · intro h a ha
    obtain ⟨ε, hε, hεU⟩ := h a ha
    refine ⟨ε / C, div_pos hε hC, fun b hb' => ?_⟩
    apply hεU b
    have ht : C * ‖b - a‖ < ε := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp hb'
    exact (hb (b - a)).2.trans_lt ht
  · intro h a ha
    obtain ⟨ε, hε, hεU⟩ := h a ha
    refine ⟨c * ε, mul_pos hc hε, fun b hb' => ?_⟩
    apply hεU
    change ‖b - a‖ < ε
    nlinarith [(hb (b - a)).1]

theorem norm_tendsto_iff {n : ℕ} (N : Seminorm ℝ (E n)) (hN : IsNorm N)
    {α : Type} (l : Filter α) (f : α → E n) (a : E n) :
    Tendsto f l (@nhds _ (normTopology N) a) ↔ Tendsto f l (𝓝 a) := by
  rw [norm_topology_eq N hN]

theorem norm_compact_iff {n : ℕ} (N : Seminorm ℝ (E n)) (hN : IsNorm N)
    (K : Set (E n)) : @IsCompact _ (normTopology N) K ↔ Compact K := by
  rw [norm_topology_eq N hN, compact_iff_isCompact]

private theorem seminorm_isBigO {n : ℕ} (N : Seminorm ℝ (E n))
    {α : Type} (l : Filter α) (r : α → E n) : (fun x => N (r x)) =O[l] r := by
  obtain ⟨C, _, hb⟩ := seminorm_upper N
  apply IsBigO.of_bound C
  exact Eventually.of_forall fun x => by simpa only [Real.norm_of_nonneg (apply_nonneg N _)] using hb (r x)

private theorem isBigO_seminorm {n : ℕ} (N : Seminorm ℝ (E n)) (hN : IsNorm N)
    {α : Type} (l : Filter α) (r : α → E n) : r =O[l] (fun x => N (r x)) := by
  obtain ⟨c, _, hc, _, hb⟩ := norm_equivalence N hN
  apply IsBigO.of_bound c⁻¹
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (apply_nonneg N _)]
  calc
    ‖r x‖ = c⁻¹ * (c * ‖r x‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ c⁻¹ * N (r x) := mul_le_mul_of_nonneg_left (hb (r x)).1 (inv_nonneg.mpr hc.le)

theorem norm_littleO_iff {n m : ℕ} (N : Seminorm ℝ (E n)) (M : Seminorm ℝ (E m))
    (hN : IsNorm N) (hM : IsNorm M) (l : Filter (E n)) (r : E n → E m) (k : ℕ) :
    (fun h => M (r h)) =o[l] (fun h => (N h) ^ k) ↔
      r =o[l] (fun h => ‖h‖ ^ k) := by
  have h₁ : (fun h : E n => (N h) ^ k) =O[l] (fun h => ‖h‖ ^ k) :=
    ((seminorm_isBigO N l id).norm_right).pow k
  have h₂ : (fun h : E n => ‖h‖ ^ k) =O[l] (fun h => (N h) ^ k) :=
    ((isBigO_seminorm N hN l id).norm_left).pow k
  constructor
  · intro h
    exact (isBigO_seminorm M hM l r).trans_isLittleO (h.trans_isBigO h₁)
  · intro h
    exact (seminorm_isBigO M l r).trans_isLittleO (h.trans_isBigO h₂)

theorem norm_derivative_remainder_iff {n m : ℕ}
    (N : Seminorm ℝ (E n)) (M : Seminorm ℝ (E m)) (hN : IsNorm N) (hM : IsNorm M)
    (f : E n → E m) (a : E n) (A : E n →ₗ[ℝ] E m) (k : ℕ) :
    (fun h => M (f (a + h) - f a - A h))
      =o[@nhdsWithin _ (normTopology N) 0 {0}ᶜ] (fun h => (N h) ^ k) ↔
    (fun h => f (a + h) - f a - A h) =o[𝓝[≠] 0] (fun h => ‖h‖ ^ k) := by
  rw [norm_topology_eq N hN]
  exact norm_littleO_iff N M hN hM _ _ k

end D04
