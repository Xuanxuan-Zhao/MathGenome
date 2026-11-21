import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.IndexJump
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexOperationsHomotopy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexProperties
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations
import Mathlib.Analysis.Convex.PathConnected

noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch13.IndexJump
open D12Complex

/-- The one-term cycle of a closed path, with its original traversal. -/
def closedCycle (γ : PiecewiseC1Path) (hγ : γ.IsClosed) : IntegralCycle :=
  ⟨Finsupp.single γ 1, by
    intro δ hδ
    have : δ = γ := by simpa only [Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton] using hδ
    subst δ
    exact hγ⟩

@[simp] theorem closedCycle_trace (γ : PiecewiseC1Path) (hγ : γ.IsClosed) :
    (closedCycle γ hγ).trace = γ.trace :=
  IndexOperationsHomotopy.single_trace γ

@[simp] theorem closedCycle_index (γ : PiecewiseC1Path) (hγ : γ.IsClosed) (p : ℂ) :
    (closedCycle γ hγ).index p = γ.index p := rfl

theorem path_index_integer (γ : PiecewiseC1Path) (hγ : γ.IsClosed)
    (p : ℂ) (hp : p ∉ γ.trace) : ∃ n : ℤ, γ.index p = (n : ℂ) := by
  simpa using IndexProperties.cycle_index_integer (closedCycle γ hγ) p (by simpa using hp)

theorem integerIndex_cast (γ : PiecewiseC1Path) (hγ : γ.IsClosed)
    (p : ℂ) (hp : p ∉ γ.trace) : (integerIndex γ p : ℂ) = γ.index p := by
  have h := path_index_integer γ hγ p hp
  rw [integerIndex, dite_eq_left h]
  exact (Classical.choose_spec h).symm

theorem index_bridge : Specs.D13Unified.Ch13.IndexJump.index_bridge_type := by
  intro γ hγ p hp
  exact ⟨integerIndex_cast γ hγ p hp,
    IndexOperationsHomotopy.path_index_eq_integral γ p hp⟩

theorem index_locally_constant :
    Specs.D13Unified.Ch13.IndexJump.index_locally_constant_type := by
  intro γ hγ p hp
  have h := IndexProperties.cycle_index_locally_constant (closedCycle γ hγ) p
    (by simpa using hp)
  simp only [closedCycle_trace, closedCycle_index] at h
  filter_upwards [h] with q hq
  refine ⟨hq.1, ?_⟩
  apply Int.cast_injective (α := ℂ)
  rw [integerIndex_cast γ hγ q hq.1, integerIndex_cast γ hγ p hp, hq.2]

/-- Every cyclic parameter value is on the original trace. -/
theorem cutTraversal_mem_trace (γ : PiecewiseC1Path) (s : ℝ)
    (hs : s ∈ Icc γ.path.a γ.path.b) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) :
    cutTraversal γ s t ∈ γ.trace := by
  unfold cutTraversal
  split_ifs with h
  · refine ⟨s + (γ.path.b - s) * t, ⟨?_, ?_⟩, rfl⟩
    · nlinarith [hs.1, mul_nonneg (sub_nonneg.mpr hs.2) ht.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h)]
  · refine ⟨γ.path.a + (s - γ.path.a) * (t - 1), ⟨?_, ?_⟩, rfl⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) (by linarith : 0 ≤ t - 1)]
    · nlinarith [hs.2, mul_nonneg (sub_nonneg.mpr hs.1) (by linarith [ht.2] : 0 ≤ 2 - t)]

/-- A cyclic cut covers the full original trace, including its identified
endpoints. Closedness is used exactly at the seam. -/
theorem trace_mem_cutTraversal (γ : PiecewiseC1Path) (hγ : γ.IsClosed) (s : ℝ)
    (_hs : s ∈ Icc γ.path.a γ.path.b) {z : ℂ} (hz : z ∈ γ.trace) :
    ∃ t ∈ Icc (0 : ℝ) 2, cutTraversal γ s t = z := by
  obtain ⟨u, hu, rfl⟩ := hz
  by_cases he : u = s
  · refine ⟨0, by norm_num, ?_⟩
    simp [cutTraversal, he]
  by_cases hsu : s ≤ u
  · have hd : 0 < γ.path.b - s := by
      have : s < u := lt_of_le_of_ne hsu (Ne.symm he)
      linarith [hu.2]
    have h0 : 0 ≤ (u - s) / (γ.path.b - s) := div_nonneg (by linarith) hd.le
    have h1 : (u - s) / (γ.path.b - s) ≤ 1 :=
      (div_le_one hd).mpr (by linarith [hu.2])
    refine ⟨(u - s) / (γ.path.b - s), ⟨h0, h1.trans (by norm_num)⟩, ?_⟩
    rw [cutTraversal, ite_eq_left h1]
    congr 1
    field_simp
    ring
  · by_cases hua : u = γ.path.a
    · refine ⟨1, by norm_num, ?_⟩
      simp only [cutTraversal, le_refl, ite_true, mul_one, add_sub_cancel]
      rw [hua]
      exact hγ
    · have hd : 0 < s - γ.path.a := by linarith [hu.1]
      have h0 : 0 < (u - γ.path.a) / (s - γ.path.a) :=
        div_pos (by have := lt_of_le_of_ne hu.1 (Ne.symm hua); linarith) hd
      have h1 : (u - γ.path.a) / (s - γ.path.a) ≤ 1 :=
        (div_le_one hd).mpr (by linarith)
      refine ⟨1 + (u - γ.path.a) / (s - γ.path.a), ⟨by linarith, by linarith⟩, ?_⟩
      rw [cutTraversal, ite_eq_right (by linarith)]
      congr 1
      field_simp
      ring

/-- Geometry alone proves avoidance on both open sides. -/
theorem SingleStraightArc.not_mem_trace {γ : PiecewiseC1Path} (hγ : γ.IsClosed)
    {o c η : ℂ} {r : ℝ} (A : SingleStraightArc γ o r c η) {p : ℂ}
    (hp : ‖p - o‖ < r) (hi : ((p - c) / η).im ≠ 0) : p ∉ γ.trace := by
  intro hpt
  obtain ⟨t, ht, heq⟩ := trace_mem_cutTraversal γ hγ A.cut A.cut_mem hpt
  by_cases htf : t ≤ A.finish
  · have he := A.arc_eq t ⟨ht.1, htf⟩
    have hη : η ≠ 0 := by
      intro h
      simpa [h] using A.direction_unit
    have hp' : p = c + (A.coordinate t : ℂ) * η := heq.symm.trans he
    apply hi
    rw [hp', add_sub_cancel_left, mul_div_cancel_right₀ _ hη]
    exact Complex.ofReal_im _
  · have hb := A.rest_outside t ⟨le_of_not_ge htf, ht.2⟩
    rw [heq] at hb
    exact (not_lt_of_ge hb) hp

theorem leftSide_convex (o c η : ℂ) (r : ℝ) : Convex ℝ (leftSide o r c η) := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · have h := (convex_ball o r) (by simpa [Metric.mem_ball, dist_eq_norm] using hp.1)
      (by simpa [Metric.mem_ball, dist_eq_norm] using hq.1) ha hb hab
    simpa [Metric.mem_ball, dist_eq_norm] using h
  · rw [IndexComputations.affine_coordinate_combination c η p q a b hab]
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hq.2
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hp.2)
        (mul_nonneg hb hq.2.le)

theorem rightSide_convex (o c η : ℂ) (r : ℝ) : Convex ℝ (rightSide o r c η) := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · have h := (convex_ball o r) (by simpa [Metric.mem_ball, dist_eq_norm] using hp.1)
      (by simpa [Metric.mem_ball, dist_eq_norm] using hq.1) ha hb hab
    simpa [Metric.mem_ball, dist_eq_norm] using h
  · rw [IndexComputations.affine_coordinate_combination c η p q a b hab]
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hq.2
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg
        (lt_of_le_of_ne ha (Ne.symm ha0)) hp.2) (mul_nonpos_of_nonneg_of_nonpos hb hq.2.le)

/-- Constancy on a preconnected subset of the complement, without identifying
any connected components of that complement. -/
theorem index_constant_on (γ : PiecewiseC1Path) (hγ : γ.IsClosed)
    {S : Set ℂ} (hS : IsPreconnected S) (havoid : ∀ p ∈ S, p ∉ γ.trace)
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) : γ.index p = γ.index q := by
  have hd : IsDiscrete (Set.range ((↑) : ℤ → ℂ)) :=
    Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
  apply hS.constant_of_mapsTo hd
    ((IndexProperties.chain_index_continuousOn (Finsupp.single γ 1)).mono
      (by intro z hz; simpa using havoid z hz)) _ hp hq
  intro z hz
  obtain ⟨n, hn⟩ := path_index_integer γ hγ z (havoid z hz)
  exact ⟨n, hn.symm⟩

/-- Cutting a loop changes its parameter origin but preserves its trace and
all contour integrals. This is established from actual interval restrictions. -/
theorem cut_path_exists (γ : PiecewiseC1Path) (hγ : γ.IsClosed) (s : ℝ)
    (hs : s ∈ Icc γ.path.a γ.path.b) :
    ∃ δ : PiecewiseC1Path, δ.path.a = 0 ∧ δ.path.b = 2 ∧
      EqOn δ (cutTraversal γ s) (Icc 0 2) ∧ δ.trace = γ.trace ∧ δ.IsClosed ∧
      ∀ f : ℂ → ℂ, ContinuousOn f γ.trace → δ.integral f = γ.integral f := by
  obtain ⟨head, ha, hb, hh⟩ := PiecewiseC1Path.exists_restriction γ γ.path.a s
    le_rfl hs.1 hs.2
  obtain ⟨tail, ta, tb, ht⟩ := PiecewiseC1Path.exists_restriction γ s γ.path.b
    hs.1 hs.2 le_rfl
  have hval : tail.path.target = head.path.source := by
    change tail tail.path.b = head head.path.a
    rw [tb, ha, ht ⟨hs.2, le_rfl⟩, hh ⟨le_rfl, hs.1⟩]
    exact hγ
  obtain ⟨δ, da, db, hd1, hd2⟩ := PiecewiseC1Path.exists_concatenation tail head hval
  simp only [ta, tb, ha, hb] at hd1 hd2
  have hrep : EqOn δ (cutTraversal γ s) (Icc 0 2) := by
    intro t htime
    unfold cutTraversal
    split_ifs with h
    · rw [hd1 ⟨htime.1, h⟩]
      exact ht ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) htime.1],
        by nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h)]⟩
    · rw [hd2 ⟨by linarith, htime.2⟩]
      exact hh ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) (by linarith : 0 ≤ t - 1)],
        by nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) (by linarith [htime.2] : 0 ≤ 2 - t)]⟩
  have htrace : δ.trace = γ.trace := by
    apply Subset.antisymm
    · rintro z ⟨t, htime, rfl⟩
      rw [da, db] at htime
      rw [hrep htime]
      exact cutTraversal_mem_trace γ s hs t htime
    · intro z hz
      obtain ⟨t, htime, heq⟩ := trace_mem_cutTraversal γ hγ s hs hz
      exact ⟨t, by simpa only [da, db] using htime, (hrep htime).trans heq⟩
  refine ⟨δ, da, db, hrep, htrace, ?_, ?_⟩
  · change δ δ.path.b = δ δ.path.a
    rw [da, db, hrep (by norm_num : (2 : ℝ) ∈ Icc 0 2),
      hrep (by norm_num : (0 : ℝ) ∈ Icc 0 2)]
    simp only [cutTraversal, show ¬ (2 : ℝ) ≤ 1 by norm_num, ite_false,
      show (0 : ℝ) ≤ 1 by norm_num, ite_true, mul_zero, add_zero]
    congr 1
    ring
  · intro f hf
    have hhf : ContinuousOn f head.trace := hf.mono (by
      rintro z ⟨t, htime, rfl⟩
      rw [ha, hb] at htime
      exact ⟨t, ⟨htime.1, htime.2.trans hs.2⟩, (hh htime).symm⟩)
    have htf : ContinuousOn f tail.trace := hf.mono (by
      rintro z ⟨t, htime, rfl⟩
      rw [ta, tb] at htime
      exact ⟨t, ⟨hs.1.trans htime.1, htime.2⟩, (ht htime).symm⟩)
    have hsum := PiecewiseC1Path.integral_subdivision γ head tail s f hs ha hb ta tb
      (by simpa only [ha, hb] using hh) (by simpa only [ta, tb] using ht) hf
    have hcat := PiecewiseC1Path.integral_concatenation tail head δ 1
      tail.path.a (tail.path.b - tail.path.a)
      (head.path.a - (head.path.b - head.path.a)) (head.path.b - head.path.a) f
      (by simp only [da, db]; norm_num) (sub_nonneg.mpr tail.path.ordered)
      (sub_nonneg.mpr head.path.ordered) hval
      (by rw [da]; ring) (by ring) (by ring) (by rw [db]; ring)
      (by simpa only [da, ta, tb] using hd1)
      (by
        intro t htime
        rw [db] at htime
        change δ t = head (head.path.a - (head.path.b - head.path.a) +
          (head.path.b - head.path.a) * t)
        rw [hd2 htime]
        apply congrArg (head : ℝ → ℂ)
        rw [ha, hb]
        ring) htf hhf
    rw [hcat, hsum, add_comm]

/-- A single monotone traversal of a segment has the same contour integral
as its affine unit-interval parametrization, even when its speed vanishes. -/
theorem monotone_straight_integral (α β : PiecewiseC1Path) (c η : ℂ)
    (hη : η ≠ 0) (x : ℝ → ℝ) (x₀ x₁ : ℝ) (hx : x₀ < x₁)
    (hc : ContinuousOn x (Icc α.path.a α.path.b))
    (hm : MonotoneOn x (Icc α.path.a α.path.b))
    (h0 : x α.path.a = x₀) (h1 : x α.path.b = x₁)
    (hα : ∀ t ∈ Icc α.path.a α.path.b, α t = c + (x t : ℂ) * η)
    (ba : β.path.a = 0) (bb : β.path.b = 1)
    (hβ : ∀ t ∈ Icc (0 : ℝ) 1, β t = c + ((x₀ + (x₁ - x₀) * t : ℝ) : ℂ) * η)
    (f : ℂ → ℂ) (hf : ContinuousOn f β.trace) : α.integral f = β.integral f := by
  let φ : ℝ → ℝ := fun t => (x t - x₀) / (x₁ - x₀)
  have hd : 0 < x₁ - x₀ := sub_pos.mpr hx
  have hφc : ContinuousOn φ (Icc α.path.a α.path.b) :=
    (hc.sub continuousOn_const).div_const _
  have hφm : MonotoneOn φ (Icc α.path.a α.path.b) := by
    intro u hu v hv huv
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hm hu hv huv) x₀) hd.le
  have hφ0 : φ α.path.a = 0 := by simp [φ, h0]
  have hφ1 : φ α.path.b = 1 := by simp [φ, h1, hd.ne']
  have hmaps : MapsTo φ (Icc α.path.a α.path.b) (Icc β.path.a β.path.b) := by
    intro t ht
    rw [ba, bb]
    exact ⟨hφ0 ▸ hφm (left_mem_Icc.mpr α.path.ordered) ht ht.1,
      hφ1 ▸ hφm ht (right_mem_Icc.mpr α.path.ordered) ht.2⟩
  have hsurj : SurjOn φ (Icc α.path.a α.path.b) (Icc β.path.a β.path.b) := by
    rw [ba, bb, ← hφ0, ← hφ1]
    exact intermediate_value_Icc α.path.ordered hφc
  have hxcoord : EqOn x (fun t => ((α t - c) / η).re) (Icc α.path.a α.path.b) := by
    intro t ht
    change x t = ((α t - c) / η).re
    rw [hα t ht, add_sub_cancel_left, mul_div_cancel_right₀ _ hη]
    exact (Complex.ofReal_re _).symm
  have hpieces : ∃ (n : ℕ) (node : Fin (n + 1) → ℝ), StrictMono node ∧
      node 0 = α.path.a ∧ node (Fin.last n) = α.path.b ∧
      ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)) := by
    let P := α.partition
    refine ⟨P.count, P.node, P.strictMono, P.first, P.last, ?_⟩
    intro i
    have hg : ContDiffOn ℝ 1 (fun t => ((α t - c) / η).re) (P.pieceSet i) :=
      Complex.reCLM.contDiff.comp_contDiffOn (((P.smooth i).sub contDiffOn_const).div_const η)
    have hxC : ContDiffOn ℝ 1 x (P.pieceSet i) :=
      hg.congr (fun t ht => hxcoord (P.piece_subset i ht))
    exact (hxC.sub contDiffOn_const).div_const _
  apply PiecewiseC1Path.integral_monotone_parameter β α φ f hφc hφm hmaps hsurj hpieces
    _ hf
  intro t ht
  have hpt : φ t ∈ Icc (0 : ℝ) 1 := by simpa only [ba, bb] using hmaps ht
  change α t = β (φ t)
  rw [hα t ht, hβ (φ t) hpt]
  congr 2
  apply Complex.ofReal_inj.mpr
  dsimp [φ]
  field_simp
  ring

theorem path_index_continuousAt (γ : PiecewiseC1Path) (p : ℂ) (hp : p ∉ γ.trace) :
    ContinuousAt γ.index p := by
  have hopen : IsOpen γ.traceᶜ := γ.path.trace_compact.isClosed.isOpen_compl
  have hc : ContinuousOn γ.index γ.traceᶜ := by
    change ContinuousOn (IntegralChain.index (Finsupp.single γ (1 : ℤ))) γ.traceᶜ
    simpa only [IndexOperationsHomotopy.single_trace] using
      IndexProperties.chain_index_continuousOn (Finsupp.single γ 1)
  exact hc.continuousAt (hopen.mem_nhds hp)

/-- Additivity across an actual interval cut, for the canonical path index. -/
theorem index_subdivision (γ α β : PiecewiseC1Path) (s : ℝ)
    (hs : s ∈ Icc γ.path.a γ.path.b)
    (ha : α.path.a = γ.path.a) (hb : α.path.b = s)
    (ba : β.path.a = s) (bb : β.path.b = γ.path.b)
    (hα : EqOn α γ (Icc α.path.a α.path.b))
    (hβ : EqOn β γ (Icc β.path.a β.path.b))
    (z : ℂ) (hz : z ∉ γ.trace) : γ.index z = α.index z + β.index z := by
  have hαz : z ∉ α.trace := by
    rintro ⟨t, ht, he⟩
    apply hz
    refine ⟨t, ?_, (hα ht).symm.trans he⟩
    rw [ha, hb] at ht
    exact ⟨ht.1, ht.2.trans hs.2⟩
  have hβz : z ∉ β.trace := by
    rintro ⟨t, ht, he⟩
    apply hz
    refine ⟨t, ?_, (hβ ht).symm.trans he⟩
    rw [ba, bb] at ht
    exact ⟨hs.1.trans ht.1, ht.2⟩
  rw [IndexOperationsHomotopy.path_index_eq_integral γ z hz,
    IndexOperationsHomotopy.path_index_eq_integral α z hαz,
    IndexOperationsHomotopy.path_index_eq_integral β z hβz,
    PiecewiseC1Path.integral_subdivision γ α β s _ hs ha hb ba bb hα hβ
      (IndexOperationsHomotopy.reciprocal_continuousOn γ z hz), mul_add]

/-- The two open sides each have a single index value. -/
theorem SingleStraightArc.left_index_eq {γ : PiecewiseC1Path} (hγ : γ.IsClosed)
    {o c η : ℂ} {r : ℝ} (A : SingleStraightArc γ o r c η)
    {p q : ℂ} (hp : p ∈ leftSide o r c η) (hq : q ∈ leftSide o r c η) :
    γ.index p = γ.index q :=
  index_constant_on γ hγ (leftSide_convex o c η r).isPreconnected
    (fun _ hz => A.not_mem_trace hγ hz.1 (ne_of_gt hz.2)) hp hq

theorem SingleStraightArc.right_index_eq {γ : PiecewiseC1Path} (hγ : γ.IsClosed)
    {o c η : ℂ} {r : ℝ} (A : SingleStraightArc γ o r c η)
    {p q : ℂ} (hp : p ∈ rightSide o r c η) (hq : q ∈ rightSide o r c η) :
    γ.index p = γ.index q :=
  index_constant_on γ hγ (rightSide_convex o c η r).isPreconnected
    (fun _ hz => A.not_mem_trace hγ hz.1 (ne_of_lt hz.2)) hp hq

/-- Subtracting a concrete half-disc leaves a remainder continuous across the
chord. The cancellation uses equality of actual contour integrals. -/
theorem local_comparison (γ : PiecewiseC1Path) (hγ : γ.IsClosed)
    (o c η : ℂ) (r : ℝ) (A : SingleStraightArc γ o r c η) :
    ∃ (ρ : ℝ) (R : ℂ → ℂ), 0 < ρ ∧ ContinuousAt R c ∧
      ∀ z : ℂ, ‖z - c‖ < ρ →
        (0 < ((z - c) / η).im → γ.index z = 1 + R z) ∧
        (((z - c) / η).im < 0 → γ.index z = R z) := by
  have hη : η ≠ 0 := by intro h; simpa [h] using A.direction_unit
  obtain ⟨δ, da, db, hδ, htrace, hclosed, hintegral⟩ :=
    cut_path_exists γ hγ A.cut A.cut_mem
  obtain ⟨α, aa, ab, hα⟩ := PiecewiseC1Path.exists_restriction δ 0 A.finish
    (by rw [da]) A.finish_pos.le (by rw [db]; exact A.finish_lt.le)
  obtain ⟨β, ba, bb, hβ⟩ := PiecewiseC1Path.exists_restriction δ A.finish 2
    (by rw [da]; exact A.finish_pos.le) A.finish_lt.le (by rw [db])
  let x₀ := A.coordinate 0
  let x₁ := A.coordinate A.finish
  let μ : ℝ := (x₀ + x₁) / 2
  let rad : ℝ := (x₁ - x₀) / 2
  let m : ℂ := c + (μ : ℂ) * η
  have hx : x₀ < x₁ := by dsimp [x₀, x₁]; linarith [A.first_neg, A.last_pos]
  have hrad : 0 < rad := by dsimp [rad]; linarith
  have hμ : |μ| < rad := by
    rw [abs_lt]
    dsimp [μ, rad, x₀, x₁]
    constructor <;> linarith [A.first_neg, A.last_pos]
  have hcm : ‖c - m‖ < rad := by
    have he : c - m = -(μ : ℂ) * η := by dsimp [m]; ring
    rw [he, norm_mul, norm_neg, A.direction_unit, mul_one]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hμ
  have coord_m (z : ℂ) : ((z - m) / η).im = ((z - c) / η).im := by
    simp [m, sub_add_eq_sub_sub, sub_div, mul_div_cancel_right₀ _ hη]
  obtain ⟨H, hH⟩ := IndexComputations.half_disk_boundary_exists m η rad A.direction_unit hrad
  obtain ⟨D, haD, hbD, hD⟩ := PiecewiseC1Path.exists_restriction H 0 1
    (by rw [hH.1]) (by norm_num) (by rw [hH.2.1]; norm_num)
  obtain ⟨S, haS, hbS, hS⟩ := PiecewiseC1Path.exists_restriction H 1 2
    (by rw [hH.1]; norm_num) (by norm_num) (by rw [hH.2.1])
  have hDline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      D t = c + ((x₀ + (x₁ - x₀) * t : ℝ) : ℂ) * η := by
    rw [hD ht, hH.2.2.1 t ht]
    dsimp [m, μ, rad]
    push_cast
    ring
  have hαline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) A.finish) :
      α t = c + (A.coordinate t : ℂ) * η := by
    rw [hα ht, hδ ⟨ht.1, ht.2.trans A.finish_lt.le⟩]
    exact A.arc_eq t ht
  have hβc : c ∉ β.trace := by
    rintro ⟨t, ht, he⟩
    rw [ba, bb] at ht
    have hout := A.rest_outside t ht
    rw [← hδ ⟨A.finish_pos.le.trans ht.1, ht.2⟩, ← hβ ht, he] at hout
    exact (not_lt_of_ge hout) A.centre_on_chord
  have hSc : c ∉ S.trace := by
    rintro ⟨t, ht, he⟩
    rw [haS, hbS] at ht
    have hnorm : ‖S t - m‖ = rad := by
      rw [hS ht, hH.2.2.2 t ht, add_sub_cancel_left]
      simp [Complex.norm_exp, A.direction_unit, abs_of_pos hrad]
    rw [he] at hnorm
    exact (ne_of_lt hcm) hnorm
  have hnear : ∀ᶠ z in 𝓝 c,
      z ∉ β.trace ∧ z ∉ S.trace ∧ ‖z - o‖ < r ∧ ‖z - m‖ < rad := by
    have h1 := β.path.trace_compact.isClosed.isOpen_compl.mem_nhds hβc
    have h2 := S.path.trace_compact.isClosed.isOpen_compl.mem_nhds hSc
    have h3 : ∀ᶠ z in 𝓝 c, ‖z - o‖ < r := by
      have hcball : c ∈ Metric.ball o r := by
        simpa only [Metric.mem_ball, dist_eq_norm] using A.centre_on_chord
      filter_upwards [Metric.isOpen_ball.mem_nhds hcball] with z hz
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have h4 : ∀ᶠ z in 𝓝 c, ‖z - m‖ < rad := by
      have hcball : c ∈ Metric.ball m rad := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hcm
      filter_upwards [Metric.isOpen_ball.mem_nhds hcball] with z hz
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
    exact ⟨hz1, hz2, hz3, hz4⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨ρ, fun z => β.index z - S.index z, hρ,
    (path_index_continuousAt β c hβc).sub (path_index_continuousAt S c hSc), ?_⟩
  intro z hz
  have hzb := hball (by simpa only [dist_eq_norm] using hz)
  have hcompare (hi : ((z - c) / η).im ≠ 0) :
      γ.index z = H.index z + (β.index z - S.index z) := by
    have hγz : z ∉ γ.trace := A.not_mem_trace hγ hzb.2.2.1 hi
    have hδz : z ∉ δ.trace := by simpa only [htrace] using hγz
    have hHz : z ∉ H.trace := by
      intro hzH
      have hcH := IndexComputations.half_disk_trace_coordinates H A.direction_unit hrad hH z hzH
      rcases hcH.2 with hnorm | him
      · exact (ne_of_lt hzb.2.2.2) hnorm
      · exact hi ((coord_m z).symm.trans him)
    have hDz : z ∉ D.trace := by
      rintro ⟨t, ht, he⟩
      apply hHz
      rw [haD, hbD] at ht
      refine ⟨t, ?_, (hD ht).symm.trans he⟩
      simpa only [hH.1, hH.2.1] using
        (show t ∈ Icc (0 : ℝ) 2 from ⟨ht.1, ht.2.trans (by norm_num)⟩)
    have hαz : z ∉ α.trace := by
      rintro ⟨t, ht, he⟩
      apply hδz
      rw [aa, ab] at ht
      exact ⟨t, by simpa only [da, db] using
        (show t ∈ Icc (0 : ℝ) 2 from ⟨ht.1, ht.2.trans A.finish_lt.le⟩), (hα ht).symm.trans he⟩
    have hequal : α.index z = D.index z := by
      rw [IndexOperationsHomotopy.path_index_eq_integral α z hαz,
        IndexOperationsHomotopy.path_index_eq_integral D z hDz]
      congr 1
      apply monotone_straight_integral α D c η hη A.coordinate x₀ x₁ hx
      · simpa only [aa, ab] using A.coordinate_continuous
      · simpa only [aa, ab] using A.coordinate_monotone
      · rw [aa]
      · rw [ab]
      · simpa only [aa, ab] using hαline
      · exact haD
      · exact hbD
      · exact hDline
      · exact IndexOperationsHomotopy.reciprocal_continuousOn D z hDz
    have heδ : δ.index z = γ.index z := by
      rw [IndexOperationsHomotopy.path_index_eq_integral δ z hδz,
        IndexOperationsHomotopy.path_index_eq_integral γ z hγz,
        hintegral _ (IndexOperationsHomotopy.reciprocal_continuousOn γ z hγz)]
    rw [← heδ, index_subdivision δ α β A.finish
      (by simpa only [da, db] using ⟨A.finish_pos.le, A.finish_lt.le⟩)
      (aa.trans da.symm) ab ba (bb.trans db.symm)
      (by simpa only [aa, ab] using hα) (by simpa only [ba, bb] using hβ) z hδz,
      index_subdivision H D S 1 (by simp only [hH.1, hH.2.1]; norm_num)
      (haD.trans hH.1.symm) hbD haS (hbS.trans hH.2.1.symm)
      (by simpa only [haD, hbD] using hD) (by simpa only [haS, hbS] using hS) z hHz,
      hequal]
    ring
  constructor
  · intro hi
    rw [hcompare (ne_of_gt hi), IndexComputations.half_disk_index_interior H m η z rad
      A.direction_unit hrad hH ⟨hzb.2.2.2, by rwa [coord_m]⟩]
  · intro hi
    rw [hcompare (ne_of_lt hi), IndexComputations.half_disk_index_exterior H m η z rad
      A.direction_unit hrad hH (Or.inr (by rwa [coord_m])), zero_add]

/-- The continuous remainder has the same limit from both sides. Constancy
on the two half-discs then makes their index difference exactly one. -/
theorem complex_index_jump (γ : PiecewiseC1Path) (hγ : γ.IsClosed)
    (o c η : ℂ) (r : ℝ) (A : SingleStraightArc γ o r c η)
    (p q : ℂ) (hp : p ∈ leftSide o r c η) (hq : q ∈ rightSide o r c η) :
    γ.index p = γ.index q + 1 := by
  obtain ⟨ρ, R, hρ, hR, hcomp⟩ := local_comparison γ hγ o c η r A
  have hη : η ≠ 0 := by intro h; simpa [h] using A.direction_unit
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let u : ℕ → ℂ := fun n => c + (e n : ℂ) * Complex.I * η
  let v : ℕ → ℂ := fun n => c - (e n : ℂ) * Complex.I * η
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have heC : Tendsto (fun n => (e n : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp he
  have hsmall : Tendsto (fun n => (e n : ℂ) * Complex.I * η) atTop (𝓝 0) := by
    simpa only [zero_mul] using (heC.mul_const Complex.I).mul_const η
  have hu : Tendsto u atTop (𝓝 c) := by
    simpa only [add_zero] using tendsto_const_nhds.add hsmall
  have hv : Tendsto v atTop (𝓝 c) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  have hui (n : ℕ) : ((u n - c) / η).im = e n := by
    simp [u, mul_div_cancel_right₀ _ hη]
  have hvi (n : ℕ) : ((v n - c) / η).im = -e n := by
    simp [v, sub_sub_cancel_left, neg_div, mul_div_cancel_right₀ _ hη]
  have huo : ∀ᶠ n in atTop, u n ∈ leftSide o r c η := by
    have hnear : ∀ᶠ z in 𝓝 c, ‖z - o‖ < r := by
      have hcball : c ∈ Metric.ball o r := by
        simpa only [Metric.mem_ball, dist_eq_norm] using A.centre_on_chord
      filter_upwards [Metric.isOpen_ball.mem_nhds hcball] with z hz
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    filter_upwards [hu.eventually hnear] with n hn
    exact ⟨hn, by rw [hui]; exact hepos n⟩
  have hvo : ∀ᶠ n in atTop, v n ∈ rightSide o r c η := by
    have hnear : ∀ᶠ z in 𝓝 c, ‖z - o‖ < r := by
      have hcball : c ∈ Metric.ball o r := by
        simpa only [Metric.mem_ball, dist_eq_norm] using A.centre_on_chord
      filter_upwards [Metric.isOpen_ball.mem_nhds hcball] with z hz
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    filter_upwards [hv.eventually hnear] with n hn
    exact ⟨hn, by rw [hvi]; exact neg_neg_of_pos (hepos n)⟩
  have huρ : ∀ᶠ n in atTop, ‖u n - c‖ < ρ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hu.eventually (Metric.ball_mem_nhds c hρ)
  have hvρ : ∀ᶠ n in atTop, ‖v n - c‖ < ρ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hv.eventually (Metric.ball_mem_nhds c hρ)
  have hueq : ∀ᶠ n in atTop, R (u n) = γ.index p - 1 := by
    filter_upwards [huo, huρ] with n hnu hnρ
    have hc := (hcomp (u n) hnρ).1 (by rw [hui]; exact hepos n)
    have hconst := A.left_index_eq hγ hp hnu
    rw [← hconst] at hc
    exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hc.symm)
  have hveq : ∀ᶠ n in atTop, R (v n) = γ.index q := by
    filter_upwards [hvo, hvρ] with n hnv hnρ
    have hc := (hcomp (v n) hnρ).2 (by rw [hvi]; exact neg_neg_of_pos (hepos n))
    exact hc.symm.trans (A.right_index_eq hγ hnv hq)
  have hleft : R c = γ.index p - 1 :=
    tendsto_nhds_unique (hR.tendsto.comp hu) (tendsto_const_nhds.congr' (hueq.mono fun _ hn => hn.symm))
  have hright : R c = γ.index q :=
    tendsto_nhds_unique (hR.tendsto.comp hv) (tendsto_const_nhds.congr' (hveq.mono fun _ hn => hn.symm))
  calc
    γ.index p = (γ.index p - 1) + 1 := by ring
    _ = R c + 1 := by rw [← hleft]
    _ = γ.index q + 1 := by rw [hright]

theorem index_jump : Specs.D13Unified.Ch13.IndexJump.index_jump_type := by
  intro γ hγ o r c η A p hp q hq
  have hpoff := A.not_mem_trace hγ hp.1 (ne_of_gt hp.2)
  have hqoff := A.not_mem_trace hγ hq.1 (ne_of_lt hq.2)
  refine ⟨hpoff, hqoff, ?_⟩
  apply Int.cast_injective (α := ℂ)
  push_cast
  rw [integerIndex_cast γ hγ p hpoff, integerIndex_cast γ hγ q hqoff]
  exact complex_index_jump γ hγ o c η r A p q hp hq

theorem reversal_closed (γ δ : PiecewiseC1Path) (hγ : γ.IsClosed)
    (ha : δ.path.a = γ.path.a) (hb : δ.path.b = γ.path.b)
    (he : EqOn δ (fun t => γ (γ.path.a + γ.path.b - t)) (Icc δ.path.a δ.path.b)) :
    δ.IsClosed := by
  change δ δ.path.b = δ δ.path.a
  rw [he (right_mem_Icc.mpr δ.path.ordered), he (left_mem_Icc.mpr δ.path.ordered), ha, hb]
  change γ γ.path.b = γ γ.path.a at hγ
  simpa only [add_sub_cancel_right, add_sub_cancel_left] using hγ.symm

theorem integerIndex_reversal (γ δ : PiecewiseC1Path) (hγ : γ.IsClosed)
    (ha : δ.path.a = γ.path.a) (hb : δ.path.b = γ.path.b)
    (he : EqOn δ (fun t => γ (γ.path.a + γ.path.b - t)) (Icc δ.path.a δ.path.b))
    (p : ℂ) (hp : p ∉ γ.trace) : integerIndex δ p = -integerIndex γ p := by
  have hδ := reversal_closed γ δ hγ ha hb he
  have hpoff := IndexOperationsHomotopy.reversal_avoids γ δ p ha hb he hp
  apply Int.cast_injective (α := ℂ)
  rw [integerIndex_cast δ hδ p hpoff, Int.cast_neg, integerIndex_cast γ hγ p hp]
  exact IndexOperationsHomotopy.path_index_reversal γ δ p ha hb he hp

theorem index_jump_reversal : Specs.D13Unified.Ch13.IndexJump.index_jump_reversal_type := by
  intro γ δ hγ ha hb he o r c η A p hp q hq
  obtain ⟨hpoff, hqoff, hjump⟩ := index_jump γ hγ o r c η A p hp q hq
  refine ⟨IndexOperationsHomotopy.reversal_avoids γ δ p ha hb he hpoff,
    IndexOperationsHomotopy.reversal_avoids γ δ q ha hb he hqoff, ?_⟩
  rw [integerIndex_reversal γ δ hγ ha hb he p hpoff,
    integerIndex_reversal γ δ hγ ha hb he q hqoff, hjump]
  ring

end D13Unified.Ch13.IndexJump
