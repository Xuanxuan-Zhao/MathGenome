import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ToeplitzSummability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness

noncomputable section
open Filter
open scoped Topology ENNReal
universe u

namespace ExpandedFA.PartV.ToeplitzSummability

open ExpandedFA.P1.C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The literal bounded sequence associated with any convergent sequence. -/
def ofConvergent (x : ℕ → 𝕜) {l : 𝕜} (hx : Tendsto x atTop (𝓝 l)) :
    SequenceConvergent 𝕜 :=
  ⟨⟨x, memℓp_infty hx.norm.bddAbove_range⟩, l, hx⟩

/-- A summable scalar row, with the standard ℓ¹ norm. -/
def ofSummableRow (a : ℕ → 𝕜) (ha : Summable (fun k => ‖a k‖)) :
    SequenceLp 𝕜 1 :=
  ⟨a, by exact memℓp_gen (by simpa using ha)⟩

theorem row_functional : Spec.RowFunctional.{u} := by
  intro 𝕜 _ a ha
  obtain ⟨L, hL, hn⟩ := convergent_pairing 𝕜 (ofSummableRow a ha) 0
  exact ⟨L, fun x => by simpa [ofSummableRow] using (hL x).2,
    by simpa [ofSummableRow] using hn⟩

theorem absolute_rows : Spec.AbsoluteRows.{u} := by
  intro 𝕜 _ A hA x l hx n
  have h := (discrete_holder 𝕜 1 ∞ (by simp)
    (ofSummableRow (A n) (hA n)) (ofConvergent x hx).val).1
  exact ⟨h, h.of_norm.hasSum⟩

/-- Uniform approximation preserves the scalar Cauchy property. Hence c is
closed in ℓ∞, without presupposing its completeness. -/
theorem convergentSubmodule_isClosed :
    IsClosed (convergentSubmodule 𝕜 : Set (SequenceLInfinity 𝕜)) := by
  apply isClosed_of_closure_subset
  intro x hx
  have hc : CauchySeq (fun k => x k) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨y, ⟨l, hy⟩, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hy.cauchySeq (ε / 3) (by positivity)
    have hcoord (k : ℕ) : dist (x k) (y k) ≤ dist x y := by
      simpa only [dist_eq_norm, lp.coeFn_sub, Pi.sub_apply] using
        lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (x - y) k
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      dist (x m) (x n) ≤ dist (x m) (y m) + dist (y m) (y n) + dist (y n) (x n) :=
        dist_triangle4 _ _ _ _
      _ ≤ dist x y + dist (y m) (y n) + dist x y := by
        gcongr
        · exact hcoord m
        · simpa only [dist_comm] using hcoord n
      _ < ε := by linarith [hN m hm n hn]
  exact cauchySeq_tendsto_of_complete hc

instance convergent_completeSpace : CompleteSpace (SequenceConvergent 𝕜) :=
  convergentSubmodule_isClosed.completeSpace_coe

/-- Coordinate and constant tests give two conditions. Banach–Steinhaus on
the complete space c gives the third, using the exact row norms. -/
theorem toeplitz_necessary (A : ℕ → ℕ → 𝕜)
    (hA : ∀ n, Summable (fun k => ‖A n k‖)) (hreg : Regular A) :
    ToeplitzConditions A := by
  classical
  choose L hL hn using fun n => row_functional 𝕜 (A n) (hA n)
  have hb (x : SequenceConvergent 𝕜) : ∃ C : ℝ, ∀ n, ‖L n x‖ ≤ C := by
    have ht : Tendsto (fun n => L n x) atTop (𝓝 (sequenceLimit x)) := by
      have ht := hreg (fun k => x.val k) (sequenceLimit x) (tendsto_sequenceLimit x)
      change Tendsto (fun n => ∑' k, A n k * x.val k) atTop (𝓝 (sequenceLimit x)) at ht
      simpa only [hL] using ht
    obtain ⟨C, hC⟩ := ht.norm.bddAbove_range
    exact ⟨C, fun n => hC (Set.mem_range_self n)⟩
  obtain ⟨C, hC0, hC⟩ := ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness
    𝕜 (SequenceConvergent 𝕜) 𝕜 ℕ L hb
  refine ⟨⟨C, hC0, fun n => by simpa only [hn] using hC n⟩, ?_, ?_⟩
  · intro k
    have ht : Tendsto (matrixTransform A (fun j => (c0Coordinate 𝕜 k).val j))
        atTop (𝓝 0) :=
      hreg (fun j => (c0Coordinate 𝕜 k).val j) 0 (c0Coordinate 𝕜 k).property
    change Tendsto (fun n => ∑' j, A n j * (c0Coordinate 𝕜 k).val j) atTop (𝓝 0) at ht
    simpa [c0Coordinate_apply, mul_ite, eq_comm] using ht
  · have ht : Tendsto (matrixTransform A (fun _ => 1)) atTop (𝓝 1) :=
      hreg (fun _ => 1) 1 tendsto_const_nhds
    change Tendsto (fun n => ∑' k, A n k * 1) atTop (𝓝 1) at ht
    simpa using ht

set_option maxHeartbeats 800000 in
/-- A uniformly bounded family of ℓ¹ rows whose columns tend to zero
annihilates every null sequence. The finite head tends to zero and the
infinite tail is controlled by the common absolute row bound. -/
theorem transform_null (A : ℕ → ℕ → 𝕜)
    (hA : ∀ n, Summable (fun k => ‖A n k‖))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n, (∑' k, ‖A n k‖) ≤ C)
    (hcol : ∀ k, Tendsto (fun n => A n k) atTop (𝓝 0))
    (x : ℕ → 𝕜) (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (matrixTransform A x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx δ hδ
  have hhead : Tendsto (fun n => ∑ k ∈ Finset.range N, A n k * x k)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range N)
      (fun k _ => (hcol k).mul_const (x k))
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hhead (ε / 2) (by positivity)
  refine ⟨M, fun n hn => ?_⟩
  have habs : Summable (fun k => ‖A n k * x k‖) :=
    (absolute_rows 𝕜 A hA x 0 hx n).1
  have htail : Summable (fun k => ‖A n (k + N)‖) :=
    (summable_nat_add_iff N).mpr (hA n)
  have htail_bound : (∑' k, ‖A n (k + N)‖) ≤ C := by
    have heq := (hA n).sum_add_tsum_nat_add N
    have hpos : 0 ≤ ∑ k ∈ Finset.range N, ‖A n k‖ := by positivity
    linarith [hC n]
  have htail_norm : ‖∑' k, A n (k + N) * x (k + N)‖ ≤ C * δ := by
    calc
      ‖∑' k, A n (k + N) * x (k + N)‖ ≤
          ∑' k, ‖A n (k + N) * x (k + N)‖ :=
        norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr habs)
      _ ≤ ∑' k, ‖A n (k + N)‖ * δ := by
        apply Summable.tsum_le_tsum _ ((summable_nat_add_iff N).mpr habs)
          (htail.mul_right δ)
        intro k
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [dist_zero_right] using (hN (k + N) (Nat.le_add_left N k)).le
      _ = (∑' k, ‖A n (k + N)‖) * δ := tsum_mul_right
      _ ≤ C * δ := mul_le_mul_of_nonneg_right htail_bound hδ.le
  have hδC : C * δ < ε / 2 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (C + 1))).mpr
    nlinarith
  rw [dist_zero_right, matrixTransform,
    ← habs.of_norm.sum_add_tsum_nat_add N]
  exact (norm_add_le _ _).trans_lt (by
    have hh := hM n hn
    rw [dist_zero_right] at hh
    linarith)

/-- Subtract the limiting constant, apply the null-sequence estimate, and
restore the constant using convergence of the full infinite row sums. -/
theorem toeplitz_sufficient (A : ℕ → ℕ → 𝕜)
    (hA : ∀ n, Summable (fun k => ‖A n k‖)) (hcond : ToeplitzConditions A) :
    Regular A := by
  rcases hcond with ⟨⟨C, hC0, hC⟩, hcol, hsum⟩
  intro x l hx
  have hx0 : Tendsto (fun k => x k - l) atTop (𝓝 0) := by
    simpa using hx.sub (tendsto_const_nhds (x := l))
  have hz := transform_null A hA hC0 hC hcol (fun k => x k - l) hx0
  have heq (n : ℕ) : matrixTransform A (fun k => x k - l) n +
      (∑' k, A n k) * l = matrixTransform A x n := by
    have ha := (hA n).of_norm
    have hzero : Summable (fun k => A n k * (x k - l)) :=
      (absolute_rows 𝕜 A hA (fun k => x k - l) 0 hx0 n).1.of_norm
    dsimp only [matrixTransform]
    rw [← ha.tsum_mul_right l, ← hzero.tsum_add (ha.mul_right l)]
    apply tsum_congr
    intro k
    ring
  simpa only [heq, zero_add, one_mul] using hz.add (hsum.mul_const l)

theorem silverman_toeplitz : Spec.SilvermanToeplitz.{u} := by
  intro 𝕜 _ A hA
  exact ⟨toeplitz_necessary A hA, toeplitz_sufficient A hA⟩

end ExpandedFA.PartV.ToeplitzSummability
