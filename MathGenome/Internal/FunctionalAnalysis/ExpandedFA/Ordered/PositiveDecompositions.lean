import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ordered.PositiveDecompositions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded positive decompositions

The generating-cone assertion of `fa2:p2:positive-automatic-continuity`.
Baire supplies a ball in the closure of a set of bounded positive differences.
Approximating two points of this ball and subtracting gives a decomposition
whose error is at most half the original norm. Iterating this construction
produces two absolutely convergent positive series. Their sums remain in the
closed cone and their difference is the original vector.
-/

open Set Metric Filter Topology Function Finset

universe u

namespace ExpandedFA.Ordered.PositiveDecompositions

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The bounded differences whose closures form the Baire cover. -/
private def boundedDifferences (P : ConvexCone ℝ X) (r : ℝ) : Set X :=
  {x | ∃ y ∈ P, ∃ z ∈ P, x = y - z ∧ ‖y‖ ≤ r ∧ ‖z‖ ≤ r}

/-- Baire gives uniformly bounded approximate positive decompositions. -/
theorem exists_approx_positive_decomposition
    (P : ConvexCone ℝ X) (hzero : (0 : X) ∈ P)
    (hgen : ∀ x : X, ∃ y ∈ P, ∃ z ∈ P, x = y - z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∃ y ∈ P, ∃ z ∈ P,
      ‖x - (y - z)‖ ≤ (1 / 2 : ℝ) * ‖x‖ ∧
      ‖y‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖ := by
  have hcover : (⋃ n : ℕ, closure (boundedDifferences P n)) = univ := by
    apply Subset.antisymm (subset_univ _)
    intro x _
    obtain ⟨y, hy, z, hz, hx⟩ := hgen x
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖y‖ ‖z‖)
    exact mem_iUnion.mpr ⟨n, subset_closure
      ⟨y, hy, z, hz, hx, (le_max_left _ _).trans hn.le,
        (le_max_right _ _).trans hn.le⟩⟩
  obtain ⟨n, a, ha⟩ :=
    ExpandedFA.P1.C07Baire.exists_nonempty_interior_of_closed_cover
      (fun n : ℕ => closure (boundedDifferences P n))
      (fun _ => isClosed_closure) hcover
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  refine ⟨4 * (n : ℝ) / ε, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    exact ⟨0, hzero, 0, hzero, by simp⟩
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let t : ℝ := ε / (2 * ‖x‖)
  have ht : 0 < t := div_pos hε (by positivity)
  have htnorm : t * ‖x‖ = ε / 2 := by dsimp [t]; field_simp
  have hax : a + t • x ∈ ball a ε := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    rw [htnorm]
    linarith
  have haa : a ∈ ball a ε := by simpa using hε
  obtain ⟨b₁, hb₁, hd₁⟩ :=
    Metric.mem_closure_iff.mp (hball hax) (ε / 8) (by positivity)
  obtain ⟨b₂, hb₂, hd₂⟩ :=
    Metric.mem_closure_iff.mp (hball haa) (ε / 8) (by positivity)
  obtain ⟨y₁, hy₁, z₁, hz₁, hb₁eq, hny₁, hnz₁⟩ := hb₁
  obtain ⟨y₂, hy₂, z₂, hz₂, hb₂eq, hny₂, hnz₂⟩ := hb₂
  let y := t⁻¹ • (y₁ + z₂)
  let z := t⁻¹ • (z₁ + y₂)
  have hy : y ∈ P := P.smul_mem (inv_pos.mpr ht) (P.add_mem hy₁ hz₂)
  have hz : z ∈ P := P.smul_mem (inv_pos.mpr ht) (P.add_mem hz₁ hy₂)
  have herr : ‖t • x - (b₁ - b₂)‖ ≤ ε / 4 := by
    have heq : t • x - (b₁ - b₂) = (a + t • x - b₁) - (a - b₂) := by abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by
      rw [← dist_eq_norm, ← dist_eq_norm]
      linarith)
  have hdiff : y - z = t⁻¹ • (b₁ - b₂) := by
    dsimp [y, z]
    rw [← smul_sub, hb₁eq, hb₂eq]
    congr 1
    abel
  have hscale : x - (y - z) = t⁻¹ • (t • x - (b₁ - b₂)) := by
    simp only [hdiff, smul_sub, inv_smul_smul₀ ht.ne']
  refine ⟨y, hy, z, hz, ?_, ?_, ?_⟩
  · rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    calc
      t⁻¹ * ‖t • x - (b₁ - b₂)‖ ≤ t⁻¹ * (ε / 4) := by gcongr
      _ = (1 / 2 : ℝ) * ‖x‖ := by dsimp [t]; field_simp; ring
  · calc
      ‖y‖ = t⁻¹ * ‖y₁ + z₂‖ := by
        change ‖t⁻¹ • (y₁ + z₂)‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      _ ≤ t⁻¹ * ((n : ℝ) + n) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hny₁ hnz₂)
      _ = 4 * (n : ℝ) / ε * ‖x‖ := by dsimp [t]; field_simp; ring
  · calc
      ‖z‖ = t⁻¹ * ‖z₁ + y₂‖ := by
        change ‖t⁻¹ • (z₁ + y₂)‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      _ ≤ t⁻¹ * ((n : ℝ) + n) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hnz₁ hny₂)
      _ = 4 * (n : ℝ) / ε * ‖x‖ := by dsimp [t]; field_simp; ring

omit [NormedSpace ℝ X] in
/-- Geometrically small corrections have a bounded norm sum. -/
private theorem norm_tsum_le_of_geometric_bound
    {u : ℕ → X} {M : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * M) :
    Summable u ∧ ‖∑' n, u n‖ ≤ 2 * M := by
  have hs : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hu
      (summable_geometric_two.mul_right M)
  refine ⟨hs.of_norm, ?_⟩
  calc
    ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * M :=
      hs.tsum_le_tsum hu (summable_geometric_two.mul_right M)
    _ = 2 * M := by rw [tsum_mul_right, tsum_geometric_two]

omit [CompleteSpace X] in
/-- Closedness keeps the sum of an absolutely convergent positive series in the cone. -/
private theorem tsum_mem_cone (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    (hzero : (0 : X) ∈ P) {u : ℕ → X} (hu : Summable u)
    (hmem : ∀ n, u n ∈ P) : (∑' n, u n) ∈ P := by
  apply hP.mem_of_tendsto hu.hasSum.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    rw [sum_range_succ]
    exact P.add_mem ih (hmem n)

/-- Uniformly bounded positive decompositions for every closed generating cone
in a real Banach space, including the zero space. -/
theorem exists_bounded_positive_decompositions
    (P : ConvexCone ℝ X) (hP : IsClosed (P : Set X))
    (hgen : ∀ x : X, ∃ y ∈ P, ∃ z ∈ P, x = y - z) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : X, ∃ y ∈ P, ∃ z ∈ P,
      x = y - z ∧ ‖y‖ ≤ C * ‖x‖ ∧ ‖z‖ ≤ C * ‖x‖ := by
  classical
  have hzero : (0 : X) ∈ P := by
    obtain ⟨y, hy, _⟩ := hgen 0
    exact ConvexCone.Pointed.of_nonempty_of_isClosed ⟨y, hy⟩ hP
  obtain ⟨C, hC, happrox⟩ := exists_approx_positive_decomposition P hzero hgen
  choose f hf g hg herr hfn hgn using happrox
  let r : X → X := fun x => x - (f x - g x)
  have hr : ∀ x, ‖r x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := herr
  refine ⟨2 * C + 1, by positivity, fun x => ?_⟩
  have hrn : ∀ n : ℕ, ‖r^[n] x‖ ≤ (1 / 2 : ℝ) ^ n * ‖x‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ']
      exact (hr _).trans (by rw [pow_succ', mul_assoc]; gcongr)
  let u : ℕ → X := fun n => f (r^[n] x)
  let v : ℕ → X := fun n => g (r^[n] x)
  have hun : ∀ n, ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖x‖) := by
    intro n
    calc
      ‖u n‖ ≤ C * ‖r^[n] x‖ := hfn _
      _ ≤ C * ((1 / 2 : ℝ) ^ n * ‖x‖) := by gcongr; exact hrn n
      _ = (1 / 2 : ℝ) ^ n * (C * ‖x‖) := by ring
  have hvn : ∀ n, ‖v n‖ ≤ (1 / 2 : ℝ) ^ n * (C * ‖x‖) := by
    intro n
    calc
      ‖v n‖ ≤ C * ‖r^[n] x‖ := hgn _
      _ ≤ C * ((1 / 2 : ℝ) ^ n * ‖x‖) := by gcongr; exact hrn n
      _ = (1 / 2 : ℝ) ^ n * (C * ‖x‖) := by ring
  obtain ⟨hu, hubound⟩ := norm_tsum_le_of_geometric_bound hun
  obtain ⟨hv, hvbound⟩ := norm_tsum_le_of_geometric_bound hvn
  have hpartial : ∀ n : ℕ, (∑ i ∈ range n, (u i - v i)) = x - r^[n] x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, iterate_succ_apply']
      change x - r^[n] x + (f (r^[n] x) - g (r^[n] x)) =
        x - (r^[n] x - (f (r^[n] x) - g (r^[n] x)))
      abel
  have hres : Tendsto (fun n => r^[n] x) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hrn ?_
    rw [← zero_mul ‖x‖]
    exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul
      tendsto_const_nhds
  have hlim := (hu.hasSum.sub hv.hasSum).tendsto_sum_nat
  simp only [hpartial] at hlim
  have heq : (∑' n, u n) - (∑' n, v n) = x := by
    simpa using tendsto_nhds_unique hlim (tendsto_const_nhds.sub hres)
  refine ⟨∑' n, u n, tsum_mem_cone P hP hzero hu (fun n => hf _),
    ∑' n, v n, tsum_mem_cone P hP hzero hv (fun n => hg _), heq.symm, ?_, ?_⟩
  · exact hubound.trans (by nlinarith [norm_nonneg x])
  · exact hvbound.trans (by nlinarith [norm_nonneg x])

end ExpandedFA.Ordered.PositiveDecompositions
