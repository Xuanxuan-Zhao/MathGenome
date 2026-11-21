import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Continuity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The contraction construction in `K03.15.cantor_function`, paper.tex:3630–3644.

The three closed pieces glue because of the endpoint conditions. The pointwise
bound gives the supremum contraction, identified here with the norm on continuous
maps from [0,1]. Iterated contraction gives a geometric increment bound and hence
a Cauchy sequence in that complete space (Mathlib's
`cauchySeq_of_le_geometric`, `cauchySeq_tendsto_of_complete`). Its uniform limit
agrees pointwise with the independently defined `limUnder`. Continuity uses the
upstream uniform-limit theorem. Order and endpoint values pass to pointwise
limits, and the three affine branch identities give the fixed-point equation.
No behavior outside [0,1] is asserted or needed.
-/
namespace SingleVariableAnalysis

open Set Filter
open scoped Topology

noncomputable def cantorStaircaseStep :=
  Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
noncomputable def cantorStaircaseIterate :=
  Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.iterate
noncomputable def cantorStaircase :=
  Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.limit
noncomputable def staircaseSupDistance :=
  Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.supDistance

private theorem left_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : x ≤ 1/3) :
    3*x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1]

private theorem right_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (h : 2/3 ≤ x) :
    3*x-2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.2]

private theorem step_left (h : ℝ → ℝ) {x : ℝ} (hx : x ≤ 1/3) :
    cantorStaircaseStep h x = h (3*x)/2 := by
  unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
  rw [ite_eq_left hx]

private theorem step_middle (h : ℝ → ℝ) (h1 : h 1 = 1)
    {x : ℝ} (hx : x ∈ Icc (1/3 : ℝ) (2/3)) :
    cantorStaircaseStep h x = 1/2 := by
  by_cases hl : x ≤ 1/3
  · have he : x = 1/3 := by linarith [hx.1]
    rw [step_left h hl, he]
    norm_num [h1]
  · unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
    rw [ite_eq_right hl, ite_eq_left hx.2]

private theorem step_right (h : ℝ → ℝ) (h0 : h 0 = 0)
    {x : ℝ} (hx : 2/3 ≤ x) :
    cantorStaircaseStep h x = 1/2 + h (3*x-2)/2 := by
  have hl : ¬ x ≤ 1/3 := by linarith
  by_cases hm : x ≤ 2/3
  · have he : x = 2/3 := by linarith
    subst x
    norm_num [cantorStaircaseStep,
      Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step, h0]
  · unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
    rw [ite_eq_right hl, ite_eq_right hm]

theorem cantorStaircaseStep_continuousOn (h : ℝ → ℝ)
    (hc : ContinuousOn h (Icc 0 1)) (h0 : h 0 = 0) (h1 : h 1 = 1) :
    ContinuousOn (cantorStaircaseStep h) (Icc 0 1) := by
  have hl : ContinuousOn (cantorStaircaseStep h) (Icc (0 : ℝ) (1/3)) := by
    have hh := (hc.comp (continuous_const.mul continuous_id).continuousOn
      (show MapsTo (fun x : ℝ => 3*x) (Icc 0 (1/3)) (Icc 0 1) from
        fun x hx => left_mem ⟨hx.1, by linarith [hx.2]⟩ hx.2)).div_const 2
    exact hh.congr (fun x hx => step_left h hx.2)
  have hm : ContinuousOn (cantorStaircaseStep h) (Icc (1/3 : ℝ) (2/3)) :=
    continuousOn_const.congr (fun x hx => step_middle h h1 hx)
  have hr : ContinuousOn (cantorStaircaseStep h) (Icc (2/3 : ℝ) 1) := by
    have hh := (continuousOn_const (c := (1/2 : ℝ))).add
      ((hc.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
        (show MapsTo (fun x : ℝ => 3*x-2) (Icc (2/3) 1) (Icc 0 1) from
          fun x hx => right_mem ⟨by linarith [hx.1], hx.2⟩ hx.1)).div_const 2)
    exact hh.congr (fun x hx => step_right h h0 hx.1)
  have hu : Icc (0 : ℝ) (1/3) ∪ Icc (1/3) (2/3) ∪ Icc (2/3) 1 = Icc 0 1 := by
    ext x
    simp only [mem_union, mem_Icc]
    constructor
    · rintro ((h | h) | h) <;> constructor <;> linarith [h.1, h.2]
    · intro hx
      by_cases h : x ≤ 1/3
      · exact Or.inl (Or.inl ⟨hx.1, h⟩)
      · by_cases h' : x ≤ 2/3
        · exact Or.inl (Or.inr ⟨by linarith, h'⟩)
        · exact Or.inr ⟨by linarith, hx.2⟩
  rw [← hu]
  exact (hl.union_of_isClosed hm isClosed_Icc isClosed_Icc).union_of_isClosed hr
    (isClosed_Icc.union isClosed_Icc) isClosed_Icc

theorem cantorStaircaseStep_endpoints (h : ℝ → ℝ) (h0 : h 0 = 0) (h1 : h 1 = 1) :
    cantorStaircaseStep h 0 = 0 ∧ cantorStaircaseStep h 1 = 1 := by
  norm_num [cantorStaircaseStep,
    Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step, h0, h1]

theorem cantorStaircaseStep_monotoneOn (h : ℝ → ℝ)
    (h0 : h 0 = 0) (h1 : h 1 = 1) (hm : MonotoneOn h (Icc 0 1)) :
    MonotoneOn (cantorStaircaseStep h) (Icc 0 1) := by
  have hb : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ h x ∧ h x ≤ 1 := by
    intro x hx
    constructor
    · simpa [h0] using hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hx hx.1
    · simpa [h1] using hm hx (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hx.2
  intro x hx y hy hxy
  unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
  split_ifs with hxl hyl hym hxm hyl hym hyl hym
  all_goals first
    | have hh := hm (left_mem hx (by assumption)) (left_mem hy (by assumption))
        (by linarith); linarith
    | have hh := hm (right_mem hx (by linarith)) (right_mem hy (by linarith))
        (by linarith); linarith
    | have hh := hb (3*x) (left_mem hx (by assumption))
      have hh' := hb (3*y-2) (right_mem hy (by linarith))
      linarith [hh.2, hh'.1]
    | have hh := hb (3*x) (left_mem hx (by assumption)); linarith [hh.2]
    | have hh := hb (3*y-2) (right_mem hy (by linarith)); linarith [hh.1]
    | linarith

/-- The uniform bound form of the contraction, which needs no regularity. -/
theorem cantorStaircaseStep_bound (h g : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, |h x - g x| ≤ r) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      |cantorStaircaseStep h x - cantorStaircaseStep g x| ≤ r/2 := by
  intro x hx
  unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
  split_ifs with hl hm
  · have hh := hb (3*x) (left_mem hx hl)
    calc
      |h (3*x)/2 - g (3*x)/2| = |h (3*x) - g (3*x)|/2 := by
        rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ r/2 := div_le_div_of_nonneg_right hh (by norm_num)
  · simpa using (show (0 : ℝ) ≤ r/2 by positivity)
  · have hh := hb (3*x-2) (right_mem hx (by linarith))
    calc
      |1/2 + h (3*x-2)/2 - (1/2 + g (3*x-2)/2)| = |h (3*x-2) - g (3*x-2)|/2 := by
        rw [add_sub_add_left_eq_sub, ← sub_div, abs_div,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ r/2 := div_le_div_of_nonneg_right hh (by norm_num)

private def intervalMap (h : ℝ → ℝ) (hc : ContinuousOn h (Icc 0 1)) :
    C(Icc (0 : ℝ) 1, ℝ) := ⟨fun x => h x, hc.domRestrict⟩

private theorem supDistance_eq_norm (h g : ℝ → ℝ)
    (hc : ContinuousOn h (Icc 0 1)) (gc : ContinuousOn g (Icc 0 1)) :
    staircaseSupDistance h g = ‖intervalMap h hc - intervalMap g gc‖ := by
  let f := intervalMap h hc - intervalMap g gc
  have hb : BddAbove ((fun x => |h x - g x|) '' Icc (0 : ℝ) 1) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (show ‖f ⟨x,hx⟩‖ ≤ ‖f‖ from ContinuousMap.norm_coe_le_norm f ⟨x,hx⟩)
  have hn : ((fun x => |h x - g x|) '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨|h 0-g 0|, 0, by norm_num, rfl⟩
  have hnonneg : 0 ≤ staircaseSupDistance h g :=
    (abs_nonneg (h 0-g 0)).trans (le_csSup hb (mem_image_of_mem _ (by norm_num)))
  apply le_antisymm
  · apply csSup_le hn
    rintro _ ⟨x,hx,rfl⟩
    exact (show ‖f ⟨x,hx⟩‖ ≤ ‖f‖ from ContinuousMap.norm_coe_le_norm f ⟨x,hx⟩)
  · apply (ContinuousMap.norm_le _ hnonneg).mpr
    intro x
    exact le_csSup hb (mem_image_of_mem _ x.property)

theorem cantorStaircaseStep_contraction (h g : ℝ → ℝ)
    (hc : ContinuousOn h (Icc 0 1)) (h0 : h 0 = 0) (h1 : h 1 = 1)
    (gc : ContinuousOn g (Icc 0 1)) (g0 : g 0 = 0) (g1 : g 1 = 1) :
    staircaseSupDistance (cantorStaircaseStep h) (cantorStaircaseStep g) ≤
      (1/2) * staircaseSupDistance h g := by
  rw [supDistance_eq_norm _ _ (cantorStaircaseStep_continuousOn h hc h0 h1)
    (cantorStaircaseStep_continuousOn g gc g0 g1), supDistance_eq_norm h g hc gc]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  have hh := cantorStaircaseStep_bound h g
    (norm_nonneg (intervalMap h hc - intervalMap g gc))
    (fun y hy => (show ‖(intervalMap h hc - intervalMap g gc) ⟨y,hy⟩‖ ≤
      ‖intervalMap h hc - intervalMap g gc‖ from ContinuousMap.norm_coe_le_norm _ _))
    x x.property
  change |cantorStaircaseStep h x - cantorStaircaseStep g x| ≤
    (1/2) * ‖intervalMap h hc - intervalMap g gc‖
  linarith [hh]

theorem cantorStaircaseStep_preserves (h : ℝ → ℝ)
    (hc : ContinuousOn h (Icc 0 1)) (h0 : h 0 = 0) (h1 : h 1 = 1) :
    ContinuousOn (cantorStaircaseStep h) (Icc 0 1) ∧
    cantorStaircaseStep h 0 = 0 ∧ cantorStaircaseStep h 1 = 1 ∧
    (MonotoneOn h (Icc 0 1) → MonotoneOn (cantorStaircaseStep h) (Icc 0 1)) :=
  ⟨cantorStaircaseStep_continuousOn h hc h0 h1,
   (cantorStaircaseStep_endpoints h h0 h1).1,
   (cantorStaircaseStep_endpoints h h0 h1).2,
   cantorStaircaseStep_monotoneOn h h0 h1⟩

theorem cantorStaircaseIterate_equations : cantorStaircaseIterate 0 = id ∧
    ∀ n, cantorStaircaseIterate (n+1) = cantorStaircaseStep (cantorStaircaseIterate n) :=
  ⟨rfl, fun _ => rfl⟩

theorem cantorStaircaseIterate_properties (n : ℕ) :
    ContinuousOn (cantorStaircaseIterate n) (Icc 0 1) ∧
    cantorStaircaseIterate n 0 = 0 ∧ cantorStaircaseIterate n 1 = 1 ∧
    MonotoneOn (cantorStaircaseIterate n) (Icc 0 1) := by
  induction n with
  | zero => exact ⟨continuousOn_id, rfl, rfl, fun _ _ _ _ h => h⟩
  | succ n ih =>
    exact ⟨cantorStaircaseStep_continuousOn _ ih.1 ih.2.1 ih.2.2.1,
      (cantorStaircaseStep_endpoints _ ih.2.1 ih.2.2.1).1,
      (cantorStaircaseStep_endpoints _ ih.2.1 ih.2.2.1).2,
      cantorStaircaseStep_monotoneOn _ ih.2.1 ih.2.2.1 ih.2.2.2⟩

theorem cantorStaircaseIterate_geometricIncrement (n : ℕ) :
    staircaseSupDistance (cantorStaircaseIterate (n+1)) (cantorStaircaseIterate n) ≤
      (1/2 : ℝ)^n * staircaseSupDistance (cantorStaircaseIterate 1) (cantorStaircaseIterate 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := cantorStaircaseIterate_properties n
    have hs := cantorStaircaseIterate_properties (n+1)
    calc
      staircaseSupDistance (cantorStaircaseIterate (n+1+1)) (cantorStaircaseIterate (n+1)) ≤
          (1/2) * staircaseSupDistance (cantorStaircaseIterate (n+1)) (cantorStaircaseIterate n) :=
        cantorStaircaseStep_contraction _ _ hs.1 hs.2.1 hs.2.2.1 hn.1 hn.2.1 hn.2.2.1
      _ ≤ (1/2) * ((1/2 : ℝ)^n *
          staircaseSupDistance (cantorStaircaseIterate 1) (cantorStaircaseIterate 0)) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1/2 : ℝ)^(n+1) *
          staircaseSupDistance (cantorStaircaseIterate 1) (cantorStaircaseIterate 0) := by
        rw [pow_succ]; ring

private noncomputable def approximant (n : ℕ) : C(Icc (0 : ℝ) 1, ℝ) :=
  intervalMap (cantorStaircaseIterate n) (cantorStaircaseIterate_properties n).1

private theorem approximant_cauchy : CauchySeq approximant := by
  apply cauchySeq_of_le_geometric (1/2 : ℝ)
    (staircaseSupDistance (cantorStaircaseIterate 1) (cantorStaircaseIterate 0)) (by norm_num)
  intro n
  rw [dist_comm, dist_eq_norm]
  change ‖intervalMap (cantorStaircaseIterate (n+1)) _ -
    intervalMap (cantorStaircaseIterate n) _‖ ≤ _
  rw [← supDistance_eq_norm]
  simpa only [mul_comm] using cantorStaircaseIterate_geometricIncrement n

theorem cantorStaircase_uniformConvergence :
    RealUniformConverges (fun n (x : Icc (0 : ℝ) 1) => cantorStaircaseIterate n x)
      (fun x => cantorStaircase x) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete approximant_cauchy
  have hp (x : Icc (0 : ℝ) 1) :
      Tendsto (fun n => cantorStaircaseIterate n x) atTop (𝓝 (g x)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hg ε hε
    exact ⟨N, fun n hn => lt_of_le_of_lt
      (ContinuousMap.dist_apply_le_dist (f := approximant n) (g := g) x) (hN n hn)⟩
  have he (x : Icc (0 : ℝ) 1) : cantorStaircase x = g x := (hp x).limUnder_eq
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hg ε hε
  refine ⟨N, ?_⟩
  intro n hn x
  change |cantorStaircaseIterate n x - cantorStaircase x| < ε
  rw [he x]
  exact lt_of_le_of_lt
    (show |cantorStaircaseIterate n x - g x| ≤ dist (approximant n) g from
      ContinuousMap.dist_apply_le_dist (f := approximant n) (g := g) x) (hN n hn)

theorem cantorStaircase_pointwise {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => cantorStaircaseIterate n x) atTop (𝓝 (cantorStaircase x)) :=
  ((realUniformConverges_iff _ _).mp cantorStaircase_uniformConvergence).tendsto_at ⟨x,hx⟩

theorem cantorStaircase_limitProperties :
    ContinuousOn cantorStaircase (Icc 0 1) ∧ MonotoneOn cantorStaircase (Icc 0 1) ∧
    cantorStaircase 0 = 0 ∧ cantorStaircase 1 = 1 ∧
    MapsTo cantorStaircase (Icc 0 1) (Icc 0 1) := by
  have hc : ContinuousOn cantorStaircase (Icc 0 1) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (realUniformLimit_continuous _ _
        (fun n => (cantorStaircaseIterate_properties n).1.domRestrict)
        cantorStaircase_uniformConvergence)
  have hm : MonotoneOn cantorStaircase (Icc 0 1) := by
    intro x hx y hy hxy
    exact le_of_tendsto_of_tendsto' (cantorStaircase_pointwise hx)
      (cantorStaircase_pointwise hy) (fun n => (cantorStaircaseIterate_properties n).2.2.2 hx hy hxy)
  have h0 : cantorStaircase 0 = 0 := by
    apply tendsto_nhds_unique (cantorStaircase_pointwise (by norm_num : (0 : ℝ) ∈ Icc 0 1))
    simpa only [(cantorStaircaseIterate_properties _).2.1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have h1 : cantorStaircase 1 = 1 := by
    apply tendsto_nhds_unique (cantorStaircase_pointwise (by norm_num : (1 : ℝ) ∈ Icc 0 1))
    simpa only [(cantorStaircaseIterate_properties _).2.2.1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  refine ⟨hc, hm, h0, h1, ?_⟩
  intro x hx
  constructor
  · rw [← h0]
    exact hm (by norm_num) hx hx.1
  · rw [← h1]
    exact hm hx (by norm_num) hx.2

theorem cantorStaircase_fixedPoint :
    ∀ x ∈ Icc (0 : ℝ) 1, cantorStaircase x = cantorStaircaseStep cantorStaircase x := by
  intro x hx
  have hs : Tendsto (fun n => cantorStaircaseIterate (n+1) x) atTop
      (𝓝 (cantorStaircase x)) :=
    (cantorStaircase_pointwise hx).comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n => cantorStaircaseStep (cantorStaircaseIterate n) x) atTop
      (𝓝 (cantorStaircaseStep cantorStaircase x)) := by
    unfold cantorStaircaseStep Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit.step
    split_ifs with hl hm
    · exact (cantorStaircase_pointwise (left_mem hx hl)).div_const 2
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds.add
        ((cantorStaircase_pointwise (right_mem hx (by linarith))).div_const 2)
  exact tendsto_nhds_unique hs ht

end SingleVariableAnalysis
