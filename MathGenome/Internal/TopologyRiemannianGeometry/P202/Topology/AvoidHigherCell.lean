import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.AvoidHigherCell
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Set Metric Topology
open scoped ContDiff
open P202.Cellular
universe u

namespace P202.Topology

/-- Smooth approximation on a compact set, with a strict uniform error bound. -/
theorem smoothApproxOnCompact {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} (hK : IsCompact K) (f : C(E, F)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, dist (g x) (f x) < ε := by
  have hu : UniformContinuousOn f (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε)
  obtain ⟨g, hg, hgf⟩ :=
    f.continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ)
  refine ⟨g, hg, fun x hx => (hgf x (ε / 2) ?_).trans_lt (half_lt_self hε)⟩
  intro y hy
  rw [mem_ball, lt_min_iff] at hy
  exact (hfδ y (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le)
    x (self_subset_cthickening _ hx) hy.2).le

/-- Lower-dimensional smooth maps miss a point in every nonempty target ball. -/
theorem smoothMapMissesPoint {n k : ℕ} (hnk : n < k)
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)}
    (hg : ContDiff ℝ ∞ g) {r : ℝ} (hr : 0 < r) :
    ∃ p : EuclideanSpace ℝ (Fin k), ‖p‖ < r ∧ p ∉ range g := by
  have hd := (hg.differentiable (by simp)).dense_compl_range_of_finrank_lt_finrank
    (by simpa only [finrank_euclideanSpace_fin] using hnk)
  obtain ⟨p, hpg, hp⟩ := hd.exists_mem_open (U := ball (0 : EuclideanSpace ℝ (Fin k)) r) isOpen_ball (nonempty_ball.mpr hr)
  exact ⟨p, by simpa only [mem_ball, dist_zero_right] using hp, hpg⟩

/-- Extend cell coordinates from a closed part of the disk to its ambient space. -/
theorem extendDiskCoordinates {n k : ℕ} {A : Set (Disk n)} (hA : IsClosed A)
    (c : C(A, EuclideanSpace ℝ (Fin k))) :
    ∃ F : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin k)),
      ∀ x : A, F x.1.1 = c x := by
  let : TietzeExtension (EuclideanSpace ℝ (Fin k)) :=
    TietzeExtension.of_homeo (EuclideanSpace.equiv (Fin k) ℝ).toHomeomorph
  have he : IsClosedEmbedding (fun x : A => x.1.1) :=
    isClosed_closedBall.isClosedEmbedding_subtypeVal.comp hA.isClosedEmbedding_subtypeVal
  obtain ⟨F, hF⟩ := c.exists_extension he
  exact ⟨F, fun x => DFunLike.congr_fun hF x⟩

private def cellCutoff {E : Type*} [NormedAddCommGroup E] (a : E) : ℝ :=
  max 0 (min 1 (2 - ‖a‖))

private theorem cellCutoff_bounds {E : Type*} [NormedAddCommGroup E] (a : E) :
    0 ≤ cellCutoff a ∧ cellCutoff a ≤ 1 := by
  unfold cellCutoff
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem cellCutoff_one {E : Type*} [NormedAddCommGroup E] {a : E}
    (ha : ‖a‖ ≤ 1) : cellCutoff a = 1 := by
  simp [cellCutoff, min_eq_left (show (1 : ℝ) ≤ 2 - ‖a‖ by linarith)]

private theorem cellCutoff_zero {E : Type*} [NormedAddCommGroup E] {a : E}
    (ha : 2 ≤ ‖a‖) : cellCutoff a = 0 := by
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))

private def cellBlend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (t : Interval) : E := a + ((t : ℝ) * cellCutoff a) • (b - a)

private theorem cellBlend_dist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (t : Interval) : dist (cellBlend a b t) a ≤ dist b a := by
  have hc := cellCutoff_bounds a
  have hn : 0 ≤ (t : ℝ) * cellCutoff a := mul_nonneg t.2.1 hc.1
  have hl : (t : ℝ) * cellCutoff a ≤ 1 := by nlinarith [t.2.1, t.2.2]
  simp only [dist_eq_norm, cellBlend, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hn]
  exact mul_le_of_le_one_left (norm_nonneg _) hl

/-- The source's open higher cell lemma, for arbitrary Hausdorff targets. -/
theorem avoidHigherCell : P202Specs.Topology.AvoidHigherCell.avoidHigherCell := by
  classical
  intro Z _ _ n k hnk U hU e f
  let j : EuclideanSpace ℝ (Fin k) → Z := fun y => (e y : Z)
  have hj : Continuous j := continuous_subtype_val.comp e.continuous
  have hji : Function.Injective j := Subtype.val_injective.comp e.injective
  have hjo : IsOpenMap j := hU.isOpenMap_subtype_val.comp e.isOpenMap
  let S : Set Z := j '' closedBall 0 3
  have hS : IsClosed S := ((isCompact_closedBall _ _).image hj).isClosed
  let A : Set (Disk n) := f ⁻¹' S
  have hA : IsClosed A := hS.preimage f.continuous
  have hAU : ∀ x ∈ A, f x ∈ U := by
    intro x hx
    obtain ⟨y, _, hy⟩ := hx
    rw [← hy]
    exact (e y).2
  let cU : C(A, U) :=
    ⟨fun x => ⟨f x.1, hAU x.1 x.2⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let c : C(A, EuclideanSpace ℝ (Fin k)) :=
    (e.symm : C(U, EuclideanSpace ℝ (Fin k))).comp cU
  have hcj : ∀ x : A, j (c x) = f x.1 := by
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply (cU x))
  obtain ⟨F, hF⟩ := extendDiskCoordinates hA c
  have hFj : ∀ x (hx : x ∈ A), j (F x.1) = f x := by
    intro x hx
    rw [hF ⟨x, hx⟩]
    exact hcj ⟨x, hx⟩
  obtain ⟨G, hG, hGF⟩ := smoothApproxOnCompact (isCompact_closedBall 0 1) F
    (ε := 1 / 2) (by norm_num)
  obtain ⟨p, hp, hpG⟩ := smoothMapMissesPoint hnk hG (r := 1 / 2) (by norm_num)
  let Q : Set (Disk n × Interval) := Prod.fst ⁻¹' A
  have hQ : IsClosed Q := hA.preimage continuous_fst
  let B : Set (Disk n × Interval) :=
    (fun z => f z.1) ⁻¹' (j '' ball 0 2)
  have hB : IsOpen B := (hjo _ isOpen_ball).preimage
    (f.continuous.comp continuous_fst)
  have hBQ : B ⊆ Q := by
    intro z hz
    obtain ⟨y, hy, heq⟩ := hz
    exact ⟨y, closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 3)
      (ball_subset_closedBall hy), heq⟩
  have hBi : B ⊆ interior Q := interior_maximal hBQ hB
  let b : Disk n × Interval → EuclideanSpace ℝ (Fin k) :=
    fun z => cellBlend (F z.1.1) (G z.1.1) z.2
  have hb : Continuous b := by
    dsimp [b, cellBlend, cellCutoff]
    fun_prop
  have hb_frontier : ∀ z ∈ frontier Q, j (b z) = f z.1 := by
    intro z hz
    have hzA : z.1 ∈ A := hQ.frontier_subset hz
    have hn : 2 ≤ ‖F z.1.1‖ := by
      by_contra hnot
      have hzB : z ∈ B := ⟨F z.1.1, by
        simpa only [mem_ball, dist_zero_right] using (lt_of_not_ge hnot), hFj z.1 hzA⟩
      exact hz.2 (hBi hzB)
    simp only [b, cellBlend, cellCutoff_zero hn, mul_zero, zero_smul, add_zero]
    exact hFj z.1 hzA
  let h : Disk n × Interval → Z := fun z => if z ∈ Q then j (b z) else f z.1
  have hh : Continuous h := (hj.comp hb).if hb_frontier (f.continuous.comp continuous_fst)
  let H : C(Disk n × Interval, Z) := ⟨h, hh⟩
  let g : C(Disk n, Z) := H.comp ⟨fun x => (x, 1), by fun_prop⟩
  refine ⟨g, H, e p, ?_, fun _ => rfl, ?_, ?_⟩
  · intro x
    change h (x, 0) = f x
    by_cases hx : x ∈ A
    · simp only [h, Q, mem_preimage, hx, ↓reduceIte, b, cellBlend,
        Set.Icc.coe_zero, zero_mul, zero_smul, add_zero]
      exact hFj x hx
    · simp [h, Q, hx]
  · intro x t hx
    have hn : (x, t) ∉ Q := fun hq => hx (hAU x hq)
    change h (x, t) = f x
    simp [h, hn]
  · intro x heq
    change h (x, 1) = j p at heq
    by_cases hx : x ∈ A
    · have hbp : cellBlend (F x.1) (G x.1) 1 = p := by
        apply hji
        simpa only [h, Q, mem_preimage, hx, ↓reduceIte, b] using heq
      have herr : dist p (F x.1) < 1 / 2 := by
        rw [← hbp]
        exact (cellBlend_dist _ _ _).trans_lt (hGF x.1 x.2)
      have hsmall : ‖F x.1‖ ≤ 1 := by
        have hnorm := norm_sub_norm_le (F x.1) p
        have herr' : ‖F x.1 - p‖ < 1 / 2 := by
          simpa only [dist_eq_norm, norm_sub_rev] using herr
        linarith
      have he : cellBlend (F x.1) (G x.1) 1 = G x.1 := by
        simp [cellBlend, cellCutoff_one hsmall]
      exact hpG ⟨x.1, he.symm.trans hbp⟩
    · have he : f x = j p := by simpa [h, Q, hx] using heq
      apply hx
      exact ⟨p, by simpa only [mem_closedBall, dist_zero_right] using
        (show ‖p‖ ≤ (3 : ℝ) by linarith), he.symm⟩

end P202.Topology
