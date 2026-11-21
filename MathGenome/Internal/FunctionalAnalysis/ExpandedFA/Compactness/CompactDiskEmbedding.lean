import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.CompactDiskEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.NullSequenceDisks
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Pairing

namespace ExpandedFA.Compactness
universe u v
noncomputable section
open Set Filter
open scoped Topology Pointwise
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E

/-- A null sequence can be enlarged to decay more slowly, with coefficients
in the real unit interval. -/
theorem exists_slow_null_sequence (z : ℕ → E) (hz : Tendsto z atTop (𝓝 0)) :
    ∃ (w : ℕ → E) (c : ℕ → ℝ), Tendsto w atTop (𝓝 0) ∧
      Tendsto c atTop (𝓝 0) ∧ (∀ n, 0 ≤ c n) ∧ (∀ n, c n ≤ 1) ∧
      ∀ n, z n = c n • w n := by
  let a : ℕ → ℝ := fun n => Real.sqrt ‖z n‖
  let v : ℕ → E := fun n => (a n)⁻¹ • z n
  have ha : Tendsto a atTop (𝓝 0) := by
    have hn : Tendsto (fun n => ‖z n‖) atTop (𝓝 (0 : ℝ)) := by simpa using hz.norm
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn
  have he (n : ℕ) : ‖v n‖ = a n := by
    dsimp [v, a]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    by_cases h : ‖z n‖ = 0
    · simp [h]
    · rw [inv_mul_eq_div]
      apply (div_eq_iff (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)))).mpr
      nlinarith [Real.sq_sqrt (norm_nonneg (z n))]
  have hv : Tendsto v atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [he] using ha
  let w : ℕ → E := fun n => if a n ≤ 1 then v n else z n
  let c : ℕ → ℝ := fun n => min 1 (a n)
  have hw : Tendsto w atTop (𝓝 0) := by
    apply hv.congr'
    filter_upwards [ha.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    simp [w, hn.le]
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa [c] using (tendsto_const_nhds (x := (1 : ℝ))).min ha
  refine ⟨w, c, hw, hc, fun n => le_min zero_le_one (Real.sqrt_nonneg _),
    fun n => min_le_left _ _, ?_⟩
  intro n
  by_cases hn : a n ≤ 1
  · simp only [c, w, hn, ite_true, min_eq_right hn]
    by_cases h : a n = 0
    · have hz0 : z n = 0 := norm_eq_zero.mp
        ((Real.sqrt_eq_zero'.mp h).antisymm (norm_nonneg _))
      simp [hz0, h]
    · simp [v, smul_smul, h]
  · simp [c, w, hn, min_eq_left (le_of_not_ge hn)]

/-- The null-sequence disk lies in every closed absolutely convex set
containing its generators. -/
theorem nullSequenceDisk_minimal {C : Set E} (hclosed : IsClosed C)
    (hb : Balanced 𝕜 C) (hv : Convex ℝ C) (z : ℕ → E)
    (hz : range z ⊆ C) : nullSequenceDisk (𝕜 := 𝕜) z ⊆ C := by
  apply closure_minimal _ hclosed
  apply convexHull_min _ hv
  exact hb.balancedHull_subset_of_subset hz

/-- Enumerate finite levels tending uniformly to zero, padding with zeros.
The pairing index permits empty levels and does not repeat their nonzero
entries infinitely often. -/
theorem exists_null_sequence_covering_finite_levels (F : ℕ → Finset E)
    (hF : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F n, ‖x‖ < ε) :
    ∃ z : ℕ → E, Tendsto z atTop (𝓝 0) ∧ ∀ n, (F n : Set E) ⊆ range z := by
  classical
  let e (n : ℕ) := (F n).equivFin
  let v : ℕ × ℕ → E := fun p =>
    if h : p.2 < (F p.1).card then
      ((e p.1).symm ⟨p.2, h⟩).val else 0
  let z : ℕ → E := fun k => v k.unpair
  refine ⟨z, Metric.tendsto_atTop.mpr ?_, ?_⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := hF ε hε
    let T := (Finset.range N).biUnion fun n =>
      (Finset.range (F n).card).image (Nat.pair n)
    refine ⟨T.sup id + 1, fun k hk => ?_⟩
    rw [dist_zero_right]
    dsimp only [z, v]
    split_ifs with h
    · have hn : N ≤ k.unpair.1 := by
        by_contra hn
        have hkT : k ∈ T := by
          apply Finset.mem_biUnion.mpr
          refine ⟨k.unpair.1, Finset.mem_range.mpr (by omega), ?_⟩
          exact Finset.mem_image.mpr
            ⟨k.unpair.2, Finset.mem_range.mpr h, Nat.pair_unpair k⟩
        have hle : k ≤ T.sup id := Finset.le_sup (f := id) hkT
        omega
      exact hN _ hn _ ((e k.unpair.1).symm ⟨k.unpair.2, h⟩).property
    · simpa using hε
  · intro n x hx
    let j := e n ⟨x, hx⟩
    refine ⟨Nat.pair n j.val, ?_⟩
    change v (Nat.unpair (Nat.pair n j.val)) = x
    rw [Nat.unpair_pair]
    dsimp only [v]
    simp only [j.isLt, dite_true]
    exact congrArg Subtype.val ((e n).symm_apply_apply ⟨x, hx⟩)

/-- A finite positive combination with coefficient sum at most one stays
in a balanced convex disk. -/
theorem disk_sum_mem {C : Set E} (hb : Balanced ℝ C) (hv : Convex ℝ C)
    (h0 : (0 : E) ∈ C) (r : ℕ → ℝ) (y : ℕ → E)
    (hr : ∀ n, 0 ≤ r n) (hy : ∀ n, y n ∈ C) (n : ℕ)
    (hs : ∑ j ∈ Finset.range n, r j ≤ 1) :
    (∑ j ∈ Finset.range n, r j • y j) ∈ C := by
  have hsum (m : ℕ) :
      (∑ j ∈ Finset.range m, r j • y j) ∈ (∑ j ∈ Finset.range m, r j) • C := by
    induction m with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact ⟨0, h0, by simp⟩
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        hv.add_smul (Finset.sum_nonneg (fun j _ => hr j)) (hr m)]
      exact Set.add_mem_add ih ⟨y m, hy m, rfl⟩
  have h := hb.smul_mono (a := ∑ j ∈ Finset.range n, r j) (b := (1 : ℝ))
    (by simpa [Real.norm_of_nonneg (Finset.sum_nonneg (fun j _ => hr j))] using hs) (hsum n)
  simpa using h

/-- Every null-sequence disk has a larger null-sequence disk in whose
Minkowski space the entire original disk is compact. -/
theorem nullSequenceDisk_compact_in_larger [CompleteSpace E]
    (z : ℕ → E) (hz : Tendsto z atTop (𝓝 0)) :
    ∃ w : ℕ → E, Tendsto w atTop (𝓝 0) ∧
      nullSequenceDisk (𝕜 := 𝕜) z ⊆ nullSequenceDisk (𝕜 := 𝕜) w ∧
      CompactDiskEmbeddingSpec.CompactDiskRealization (𝕜 := 𝕜)
        (nullSequenceDisk (𝕜 := 𝕜) w) (nullSequenceDisk (𝕜 := 𝕜) z) := by
  obtain ⟨w, c, hw, hc, hc0, hc1, hzw⟩ := exists_slow_null_sequence (𝕜 := 𝕜) z hz
  obtain ⟨G, nG, sG, cG, i, hi, hic, hball, hrange, hgauge, hspan⟩ :=
    (nullSequenceDisk_banach (𝕜 := 𝕜) w hw).2
  let := nG
  let := sG
  let := cG
  let : NormedSpace ℝ G := NormedSpace.restrictScalars ℝ 𝕜 G
  let : IsScalarTower ℝ 𝕜 G := IsScalarTower.restrictScalars ℝ 𝕜 G
  have hwmem (n : ℕ) : w n ∈ i '' Metric.closedBall (0 : G) 1 := by
    rw [hball]
    apply subset_closure
    apply subset_convexHull
    exact subset_balancedHull 𝕜 (mem_range_self n)
  choose y hy hyi using hwmem
  let v : ℕ → G := fun n => c n • y n
  have hv : Tendsto v atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ hc
    intro n
    dsimp [v]
    rw [norm_smul, Real.norm_of_nonneg (hc0 n)]
    have h := hy n
    rw [Metric.mem_closedBall, dist_zero_right] at h
    nlinarith [hc0 n]
  have hiv (n : ℕ) : i (v n) = z n := by
    dsimp [v]
    change (i.restrictScalars ℝ) (c n • y n) = z n
    rw [map_smul]
    change c n • i (y n) = z n
    rw [hyi n, ← hzw n]
  let A := nullSequenceDisk (𝕜 := 𝕜) v
  have hA : IsCompact A := isCompact_nullSequenceDisk v hv
  have hAb : Balanced 𝕜 A :=
    (balanced_real_convexHull (balancedHull.balanced (𝕜 := 𝕜) (range v))).closure
  have hAv : Convex ℝ A := (convex_convexHull ℝ _).closure
  have hIA : IsCompact (i '' A) := hA.image i.continuous
  have hIAb : Balanced 𝕜 (i '' A) := by
    apply balanced_iff_smul_mem.mpr
    intro a ha x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨a • b, hAb.smul_mem ha hb, i.map_smul a b⟩
  have hIAv : Convex ℝ (i '' A) := hAv.linear_image (i.restrictScalars ℝ).toLinearMap
  have hzA : nullSequenceDisk (𝕜 := 𝕜) z ⊆ i '' A := by
    apply nullSequenceDisk_minimal hIA.isClosed hIAb hIAv
    rintro _ ⟨n, rfl⟩
    refine ⟨v n, ?_, hiv n⟩
    apply subset_closure
    apply subset_convexHull
    exact subset_balancedHull 𝕜 (mem_range_self n)
  have hpre : IsCompact (i ⁻¹' nullSequenceDisk (𝕜 := 𝕜) z) := by
    apply hA.of_isClosed_subset (isClosed_closure.preimage i.continuous)
    intro x hx
    obtain ⟨a, ha, he⟩ := hzA hx
    exact hi he ▸ ha
  have hzg : nullSequenceDisk (𝕜 := 𝕜) z ⊆ nullSequenceDisk (𝕜 := 𝕜) w := by
    apply nullSequenceDisk_minimal isClosed_closure
      ((balanced_real_convexHull (balancedHull.balanced (𝕜 := 𝕜) (range w))).closure)
      ((convex_convexHull ℝ _).closure)
    rintro _ ⟨n, rfl⟩
    rw [hzw n]
    have hmem : w n ∈ nullSequenceDisk (𝕜 := 𝕜) w := by
      apply subset_closure
      apply subset_convexHull
      exact subset_balancedHull 𝕜 (mem_range_self n)
    exact (balanced_real
      ((balanced_real_convexHull (balancedHull.balanced (𝕜 := 𝕜) (range w))).closure)).smul_mem
      (by simpa [Real.norm_of_nonneg (hc0 n)] using hc1 n) hmem
  exact ⟨w, hw, hzg, G, nG, sG, cG, i, hi, hic, hball, hrange, hgauge, hspan, hpre⟩

/-- Grothendieck's compactness principle, over the original real or
complex scalar field. Only completeness of the ambient Banach space is used
later; the finite-net construction itself works for normed spaces. -/
theorem exists_null_sequence_disk_covering (K : Set E) (hK : IsCompact K) :
    ∃ z : ℕ → E, Tendsto z atTop (𝓝 0) ∧ K ⊆ nullSequenceDisk (𝕜 := 𝕜) z := by
  classical
  have hnet (n : ℕ) := Metric.totallyBounded_iff.mp hK.totallyBounded
    ((1 / 4 : ℝ) ^ n) (pow_pos (by norm_num) n)
  choose T hT hcover using hnet
  have happ : ∀ n (x : K), ∃ y ∈ T n, dist (x : E) y < (1 / 4 : ℝ) ^ n := by
    intro n x
    obtain ⟨y, hy, hd⟩ := mem_iUnion₂.mp (hcover n x.property)
    exact ⟨y, hy, hd⟩
  choose a ha hdist using happ
  have hfa (n : ℕ) : (range (a n)).Finite :=
    (hT n).subset (by rintro y ⟨x, rfl⟩; exact ha n x)
  let S : ℕ → Set E
    | 0 => range (fun x : K => (2 : ℝ) • a 0 x)
    | n+1 => range (fun x : K => (2 : ℝ) ^ (n+2) • (a (n+1) x - a n x))
  have hSfinite : ∀ n, (S n).Finite := by
    intro n
    cases n with
    | zero =>
      apply ((hfa 0).image (fun y => (2 : ℝ) • y)).subset
      rintro y ⟨x, rfl⟩
      exact ⟨a 0 x, mem_range_self x, rfl⟩
    | succ n =>
      apply (((hfa (n+1)).prod (hfa n)).image
        (fun p : E × E => (2 : ℝ) ^ (n+2) • (p.1 - p.2))).subset
      rintro y ⟨x, rfl⟩
      exact ⟨(a (n+1) x, a n x), ⟨mem_range_self x, mem_range_self x⟩, rfl⟩
  have hinc (n : ℕ) (x : K) :
      ‖(2 : ℝ) ^ (n+2) • (a (n+1) x - a n x)‖ ≤ 5 * (1 / 2 : ℝ) ^ n := by
    have hd : ‖a (n+1) x - a n x‖ ≤
        (1 / 4 : ℝ) ^ (n+1) + (1 / 4 : ℝ) ^ n := by
      calc
        _ = dist (a (n+1) x) (a n x) := (dist_eq_norm _ _).symm
        _ ≤ dist (a (n+1) x) (x : E) + dist (x : E) (a n x) := dist_triangle _ _ _
        _ ≤ _ := add_le_add (by simpa [dist_comm] using (hdist (n+1) x).le)
          (hdist n x).le
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by norm_num) _)]
    calc
      _ ≤ (2 : ℝ) ^ (n+2) * ((1 / 4 : ℝ) ^ (n+1) + (1 / 4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hd (pow_nonneg (by norm_num) _)
      _ = 5 * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by
        rw [pow_add, pow_succ]
        ring
      _ = _ := by rw [← mul_pow]; norm_num
  let F (n : ℕ) := (hSfinite n).toFinset
  have hF : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ y ∈ F n, ‖y‖ < ε := by
    intro ε hε
    have ht : Tendsto (fun n : ℕ => 5 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)).const_mul 5
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (ht.eventually (gt_mem_nhds hε))
    refine ⟨N+1, ?_⟩
    intro n hn y hy
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hyS : y ∈ S (m+1) := by simpa [F] using hy
    obtain ⟨x, rfl⟩ := hyS
    exact (hinc m x).trans_lt (hN m (by omega))
  obtain ⟨z, hz, hFz⟩ := exists_null_sequence_covering_finite_levels F hF
  let C := nullSequenceDisk (𝕜 := 𝕜) z
  have hS (n : ℕ) : S n ⊆ C := by
    intro y hy
    apply subset_closure
    apply subset_convexHull
    exact subset_balancedHull 𝕜 (hFz n (by simpa [F] using hy))
  have h0 : (0 : E) ∈ C := by
    apply subset_closure
    apply subset_convexHull
    exact (balancedHull.balanced (𝕜 := 𝕜) (range z)).zero_mem
      ((range_nonempty z).mono (subset_balancedHull 𝕜))
  have hb : Balanced ℝ C := balanced_real
    ((balanced_real_convexHull (balancedHull.balanced (𝕜 := 𝕜) (range z))).closure)
  have hv : Convex ℝ C := (convex_convexHull ℝ _).closure
  refine ⟨z, hz, ?_⟩
  intro x hx
  let xK : K := ⟨x, hx⟩
  let u : ℕ → E
    | 0 => a 0 xK
    | n+1 => a (n+1) xK - a n xK
  let b : ℕ → E := fun n => (2 : ℝ) ^ (n+1) • u n
  have hbmem (n : ℕ) : b n ∈ C := by
    cases n with
    | zero => apply hS 0; exact ⟨xK, by simp [b, u]⟩
    | succ n => apply hS (n+1); exact ⟨xK, rfl⟩
  have hcoef (n : ℕ) :
      (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j+1)) ≤ 1 := by
    calc
      _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ, mul_comm]
      _ ≤ (1 / 2 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (by norm_num)
      _ = 1 := by norm_num
  have humem (n : ℕ) : (∑ j ∈ Finset.range n, u j) ∈ C := by
    have he (j : ℕ) : (1 / 2 : ℝ) ^ (j+1) • b j = u j := by
      dsimp [b]
      rw [smul_smul, ← mul_pow]
      norm_num
    simpa only [he] using disk_sum_mem (𝕜 := 𝕜) hb hv h0
      (fun j => (1 / 2 : ℝ) ^ (j+1)) b (fun _ => by positivity) hbmem n (hcoef n)
  have hsum (n : ℕ) : (∑ j ∈ Finset.range (n+1), u j) = a n xK := by
    rw [Finset.sum_range_succ']
    change (∑ j ∈ Finset.range n, (a (j+1) xK - a j xK)) + a 0 xK = _
    rw [Finset.sum_range_sub (fun j => a j xK)]
    abel
  have hamem (n : ℕ) : a n xK ∈ C := hsum n ▸ humem (n+1)
  have hax : Tendsto (fun n => a n xK) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1/4 by norm_num) (by norm_num)
    apply squeeze_zero (fun _ => dist_nonneg) _ ht
    intro n
    simpa [xK, dist_comm] using (hdist n xK).le
  exact isClosed_closure.mem_of_tendsto hax (Eventually.of_forall hamem)

/-- Every compact set admits a compact disk embedding that is compact for
the full Minkowski norm on the disk span. -/
theorem compactDiskEmbedding : CompactDiskEmbeddingSpec.CompactDiskEmbeddingTheorem := by
  intro 𝕜 _ E _ _ _ K hK
  obtain ⟨z, hz, hKz⟩ := exists_null_sequence_disk_covering (𝕜 := 𝕜) K hK
  obtain ⟨w, hw, hzw, G, nG, sG, cG, i, hi, hic, hball, hrange, hgauge, hspan, hpre⟩ :=
    nullSequenceDisk_compact_in_larger (𝕜 := 𝕜) z hz
  let := nG
  let := sG
  let := cG
  refine ⟨w, hw, hKz.trans hzw, isCompact_nullSequenceDisk w hw,
    G, nG, sG, cG, i, hi, hic, hball, hrange, hgauge, hspan, ?_⟩
  exact hpre.of_isClosed_subset (hK.isClosed.preimage i.continuous) (preimage_mono hKz)

end
end ExpandedFA.Compactness
