import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.TrianglePrimitiveCriterion
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology

/-! The canonical objects live in the independent Spec for reuse by downstream
Specs. These candidate-owned exports verify their exact type/value bindings,
following the shared foundations' export convention. -/
namespace D12Complex.TrianglePrimitiveCriterion

abbrev segmentPath : Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.segmentPath_type :=
  _root_.D12Complex.segmentPath

abbrev segmentIntegral : Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.segmentIntegral_type :=
  _root_.D12Complex.segmentIntegral

abbrev triangleBoundaryIntegral :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.triangleBoundaryIntegral_type :=
  _root_.D12Complex.triangleBoundaryIntegral

abbrev ZeroTriangleIntegrals :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.ZeroTriangleIntegrals_type :=
  _root_.D12Complex.ZeroTriangleIntegrals

abbrev radialPrimitive : Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.radialPrimitive_type :=
  _root_.D12Complex.radialPrimitive

end D12Complex.TrianglePrimitiveCriterion

namespace D12Complex

theorem segmentPath_trace :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.segmentPath_trace_type := by
  intro a b
  exact (segment_eq_image_lineMap ℝ a b).symm

theorem segmentIntegral_formula :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.segmentIntegral_formula_type := by
  intro f a b hf
  have hfc : ContinuousOn f (segmentPath a b).trace := by rwa [segmentPath_trace]
  rw [segmentIntegral, PiecewiseC1Path.integral,
    C1Partition.integral_eq_intervalIntegral _ _ f hfc]
  change (∫ t in (0 : ℝ)..1,
    f (AffineMap.lineMap a b t) * deriv (AffineMap.lineMap a b : ℝ → ℂ) t) = _
  simp only [AffineMap.hasDerivAt_lineMap.deriv]

theorem segmentIntegral_reverse :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.segmentIntegral_reverse_type := by
  intro f a b hf
  apply PiecewiseC1Path.integral_reversal (segmentPath a b) (segmentPath b a) f rfl rfl
  · intro t ht
    change AffineMap.lineMap b a t = AffineMap.lineMap a b (0 + 1 - t)
    simp [AffineMap.lineMap_apply_one_sub]
  · rwa [segmentPath_trace]

/-- Affine parameter change on one supporting line, including zero duration. -/
theorem segmentIntegral_lineMap (f : ℂ → ℂ) (a b : ℂ) (s t : ℝ)
    (hf : ContinuousOn f (segment ℝ (AffineMap.lineMap a b s) (AffineMap.lineMap a b t))) :
    segmentIntegral f (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) =
      ∫ u in s..t, f (AffineMap.lineMap a b u) * (b - a) := by
  have hm (u : ℝ) :
      AffineMap.lineMap (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) u =
      AffineMap.lineMap a b ((t - s) * u + s) := by
    simp only [AffineMap.lineMap_apply_module', Complex.real_smul,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  have hd : AffineMap.lineMap a b t - AffineMap.lineMap a b s = (t - s) • (b - a) := by
    simp only [AffineMap.lineMap_apply_module', Complex.real_smul, Complex.ofReal_sub]
    ring
  rw [segmentIntegral_formula _ _ _ hf]
  calc
    _ = ∫ u in (0 : ℝ)..1, (t - s) •
        (f (AffineMap.lineMap a b ((t - s) * u + s)) * (b - a)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      rw [hm u, hd, mul_smul_comm]
    _ = (t - s) • ∫ u in (0 : ℝ)..1,
        f (AffineMap.lineMap a b ((t - s) * u + s)) * (b - a) :=
      intervalIntegral.integral_smul _ _
    _ = _ := by
      simpa using intervalIntegral.smul_integral_comp_mul_add
        (fun u => f (AffineMap.lineMap a b u) * (b - a)) (t - s) s
        (a := 0) (b := 1)

theorem segmentIntegral_subsegment_add :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.segmentIntegral_subsegment_add_type := by
  intro f a b c hc hf
  obtain ⟨t, ht, rfl⟩ := (segment_eq_image_lineMap ℝ a b ▸ hc)
  have hc := lineMap_mem_segment ℝ a b ht
  have hleft : ContinuousOn f (segment ℝ a (AffineMap.lineMap a b t)) :=
    hf.mono ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hc)
  have hright : ContinuousOn f (segment ℝ (AffineMap.lineMap a b t) b) :=
    hf.mono ((convex_segment a b).segment_subset hc (right_mem_segment ℝ a b))
  have hl := segmentIntegral_lineMap f a b 0 t (by simpa using hleft)
  have hr := segmentIntegral_lineMap f a b t 1 (by simpa using hright)
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at hl hr
  rw [hl, hr, segmentIntegral_formula f a b hf]
  have hint : IntervalIntegrable (fun u => f (AffineMap.lineMap a b u) * (b - a))
      volume 0 1 :=
    ((hf.comp AffineMap.lineMap_continuous.continuousOn
      (fun u hu => lineMap_mem_segment ℝ a b hu)).mul continuousOn_const).intervalIntegrable_of_Icc
      zero_le_one
  exact intervalIntegral.integral_add_adjacent_intervals
    (hint.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl ht.2))
    (hint.mono_set (by
      rw [uIcc_of_le ht.2, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc ht.1 le_rfl))

theorem triangleBoundaryIntegral_degenerate :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.triangleBoundaryIntegral_degenerate_type := by
  intro f a b c hc hf
  rw [triangleBoundaryIntegral, segmentIntegral_subsegment_add f a b c hc hf,
    segmentIntegral_reverse f a b hf, add_neg_cancel]

/-- Reversal and subdivision cancel every ordering of a collinear triangle. -/
theorem triangleBoundaryIntegral_collinear :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.triangleBoundaryIntegral_collinear_type := by
  intro f a b c hc hf
  rcases hc.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact triangleBoundaryIntegral_degenerate f a c b h.mem_segment
      (hf.mono (segment_subset_convexHull (by simp) (by simp)))
  · have hz := triangleBoundaryIntegral_degenerate f b a c h.mem_segment
      (hf.mono (segment_subset_convexHull (by simp) (by simp)))
    dsimp [triangleBoundaryIntegral] at hz ⊢
    calc
      _ = segmentIntegral f b c + segmentIntegral f c a + segmentIntegral f a b := by abel
      _ = 0 := hz
  · have hz := triangleBoundaryIntegral_degenerate f c b a h.mem_segment
      (hf.mono (segment_subset_convexHull (by simp) (by simp)))
    dsimp [triangleBoundaryIntegral] at hz ⊢
    calc
      _ = segmentIntegral f c a + segmentIntegral f a b + segmentIntegral f b c := by abel
      _ = 0 := hz

theorem zeroTriangleIntegrals_iff_noncollinear :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.zeroTriangleIntegrals_iff_noncollinear_type := by
  intro Ω f hf
  constructor
  · intro h a b c _ hs; exact h a b c hs
  · intro h a b c hs
    by_cases hc : Collinear ℝ ({a, b, c} : Set ℂ)
    · exact triangleBoundaryIntegral_collinear f a b c hc (hf.mono hs)
    · exact h a b c hc hs

/-- The exact bridge to Mathlib's integral of the multiplication 1-form. -/
theorem segmentIntegral_eq_curveIntegral (f : ℂ → ℂ) (a b : ℂ)
    (hf : ContinuousOn f (segment ℝ a b)) :
    segmentIntegral f a b = curveIntegral (fun z => f z • (1 : ℂ →L[ℂ] ℂ))
      (Path.segment a b) := by
  rw [segmentIntegral_formula f a b hf, curveIntegral_segment]
  simp only [smul_apply, one_apply_eq_self, smul_eq_mul]

/-- A compact segment in an open set has a convex tubular neighborhood in it.
This is the geometry needed for star-shaped sets, which need not be convex. -/
theorem eventually_triangle_subset {Ω : Set ℂ} (hΩ : IsOpen Ω) (a z : ℂ)
    (hs : segment ℝ a z ⊆ Ω) :
    ∀ᶠ w in 𝓝 z, convexHull ℝ {a, z, w} ⊆ Ω := by
  have hcompact : IsCompact (segment ℝ a z) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨δ, hδ, hsub⟩ := hcompact.exists_thickening_subset_open hΩ hs
  filter_upwards [ball_mem_nhds z hδ] with w hw
  apply Subset.trans (convexHull_min ?_ ((convex_segment a z).thickening δ)) hsub
  have hself := self_subset_thickening hδ (segment ℝ a z)
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨hself (left_mem_segment ℝ a z), hself (right_mem_segment ℝ a z),
    ball_subset_thickening (right_mem_segment ℝ a z) δ hw⟩

/-- Continuity alone gives the derivative of the integral at its source. -/
theorem hasDerivAt_segmentIntegral_source {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : ContinuousOn f Ω) {z : ℂ} (hz : z ∈ Ω) :
    HasDerivAt (segmentIntegral f z) (f z) z := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun w => f w • (1 : ℂ →L[ℂ] ℂ)
  have hω : ∀ᶠ w in 𝓝 z, ContinuousAt ω w := by
    filter_upwards [hΩ.mem_nhds hz] with w hw
    exact (hf.continuousAt (hΩ.mem_nhds hw)).smul continuousAt_const
  have hd := (HasFDerivAt.curveIntegral_segment_source' hω).hasDerivAt
  have heq : segmentIntegral f z =ᶠ[𝓝 z]
      (fun w => curveIntegral ω (Path.segment z w)) := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
    filter_upwards [ball_mem_nhds z hr] with w hw
    apply segmentIntegral_eq_curveIntegral
    exact hf.mono (((convex_ball z r).segment_subset (mem_ball_self hr) hw).trans hball)
  simpa [ω] using hd.congr_of_eventuallyEq heq

theorem triangle_primitive_criterion :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.triangle_primitive_criterion_type := by
  intro Ω a f hΩ ha hstar hf htri
  have hd : ∀ z ∈ Ω, HasDerivAt (radialPrimitive f a) (f z) z := by
    intro z hz
    have heq : radialPrimitive f a =ᶠ[𝓝 z]
        (fun w => radialPrimitive f a z + segmentIntegral f z w) := by
      filter_upwards [eventually_triangle_subset hΩ a z (hstar.segment_subset hz),
        hΩ.mem_nhds hz] with w hw hwΩ
      have hzero := htri a z w hw
      have hr := segmentIntegral_reverse f a w (hf.mono (hstar.segment_subset hwΩ))
      dsimp [triangleBoundaryIntegral] at hzero
      dsimp [radialPrimitive]
      rw [hr] at hzero
      exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hzero)).symm
    exact ((hasDerivAt_segmentIntegral_source hΩ hf hz).const_add _).congr_of_eventuallyEq heq
  exact ⟨⟨hΩ, fun z hz => (hd z hz).differentiableAt⟩, hd⟩

theorem convex_triangle_primitive_criterion :
    Specs.D12Complex.Ch03.TrianglePrimitiveCriterion.convex_triangle_primitive_criterion_type := by
  intro Ω a f hΩ ha hc hf ht
  exact triangle_primitive_criterion Ω a f hΩ ha (hc.starConvex ha) hf ht

end D12Complex
