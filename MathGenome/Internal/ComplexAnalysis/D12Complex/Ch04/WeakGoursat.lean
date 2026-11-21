import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WeakGoursat
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Tactic.Abel

/-! Weak Goursat (paper.tex:827–857).

The real-variable Poincaré lemma supplies a primitive on the closed convex
triangle from `DifferentiableOn ℂ f` alone. Its hypotheses impose no
continuity on the derivative. The endpoint formula below identifies the
resulting integral with the project's partition-defined contour integral.
Two triangle equations then cancel along the diagonal of a parallelogram.
-/

noncomputable section
open Set MeasureTheory

namespace D12Complex.WeakGoursat

/-- The directed affine segment, including coincident endpoints. -/
def segmentPath (a b : ℂ) : PiecewiseC1Path :=
  ⟨⟨0, 1, zero_le_one, fun t => a + t • (b - a),
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn⟩,
    ⟨C1Partition.single _
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn⟩⟩

/-- Closed real convex hull of the three vertices. -/
def closedTriangle (a b c : ℂ) : Set ℂ := convexHull ℝ {a, b, c}

def triangleBoundaryIntegral (a b c : ℂ) (f : ℂ → ℂ) : ℂ :=
  (segmentPath a b).integral f + (segmentPath b c).integral f +
    (segmentPath c a).integral f

/-- Closed parallelograms include rectangles and zero sides. -/
def closedParallelogram (a u v : ℂ) : Set ℂ :=
  convexHull ℝ {a, a + u, a + u + v, a + v}

def parallelogramBoundaryIntegral (a u v : ℂ) (f : ℂ → ℂ) : ℂ :=
  (segmentPath a (a + u)).integral f +
    (segmentPath (a + u) (a + u + v)).integral f +
    (segmentPath (a + u + v) (a + v)).integral f +
    (segmentPath (a + v) a).integral f

theorem segmentPath_mapsTo {s : Set ℂ} (hs : Convex ℝ s) {a b : ℂ}
    (ha : a ∈ s) (hb : b ∈ s) : MapsTo (segmentPath a b) (Icc 0 1) s := by
  intro t ht
  exact hs.add_smul_sub_mem ha hb ht

theorem segmentPath_hasDerivAt (a b : ℂ) (t : ℝ) :
    HasDerivAt (segmentPath a b) (b - a) t := by
  change HasDerivAt (fun t : ℝ => a + t • (b - a)) (b - a) t
  convert ((hasDerivAt_id t).smul_const (b - a)).const_add a using 1 <;> simp

theorem segment_integral_eq_sub {s : Set ℂ} (hs : Convex ℝ s)
    {F f : ℂ → ℂ} (hF : ∀ z ∈ s, HasDerivWithinAt F (f z) s z)
    (hf : ContinuousOn f s) {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) :
    (segmentPath a b).integral f = F b - F a := by
  have hm := segmentPath_mapsTo hs ha hb
  have hc : ContinuousOn f (segmentPath a b).trace := by
    exact hf.mono (by rintro z ⟨t, ht, rfl⟩; exact hm ht)
  rw [PiecewiseC1Path.integral_congr_representative (segmentPath a b)
    (segmentPath a b) f hc (fun _ _ => rfl)]
  have hd (t : ℝ) : deriv (segmentPath a b) t = b - a :=
    (segmentPath_hasDerivAt a b t).deriv
  simp_rw [hd]
  have hcomp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (F ∘ segmentPath a b)
        (f (segmentPath a b t) * (b - a)) (Icc 0 1) t := by
    simpa only [smul_eq_mul, mul_comm] using
      (hF _ (hm ht)).scomp t (segmentPath_hasDerivAt a b t).hasDerivWithinAt hm
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (show ContinuousOn (F ∘ segmentPath a b) (Icc 0 1) from
      fun t ht => (hcomp t ht).continuousWithinAt)
    (fun t ht => (hcomp t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))
    ((hf.comp (segmentPath a b).path.continuousOn hm).mul_const (b - a)
      |>.intervalIntegrable_of_Icc zero_le_one)
  simpa [segmentPath, PiecewiseC1Path.path, Function.comp_def] using heq

/-- Reversing a side reverses its integral, for any function continuous on
the containing convex set. -/
theorem segment_integral_reverse {s : Set ℂ} (hs : Convex ℝ s)
    {f : ℂ → ℂ} (hf : ContinuousOn f s) {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) :
    (segmentPath b a).integral f = -(segmentPath a b).integral f := by
  apply PiecewiseC1Path.integral_reversal (segmentPath a b) (segmentPath b a) f rfl rfl
  · intro t ht
    change b + t • (a - b) = a + (0 + 1 - t) • (b - a)
    simp only [zero_add, sub_smul, one_smul, smul_sub]
    abel
  · exact hf.mono (by rintro z ⟨t, ht, rfl⟩; exact segmentPath_mapsTo hs ha hb ht)

/-- Weak Goursat on a real convex hull; repeated or collinear vertices
require no separate analytic assumption. -/
theorem goursat_triangle : Specs.D12Complex.Ch04.WeakGoursat.goursat_triangle_type := by
  intro a b c Ω f hf hT
  change triangleBoundaryIntegral a b c f = 0
  have hs : Convex ℝ (closedTriangle a b c) := convex_convexHull ℝ _
  have ha : a ∈ closedTriangle a b c := subset_convexHull ℝ _ (by simp)
  have hb : b ∈ closedTriangle a b c := subset_convexHull ℝ _ (by simp)
  have hc : c ∈ closedTriangle a b c := subset_convexHull ℝ _ (by simp)
  have hd : DifferentiableOn ℂ f (closedTriangle a b c) :=
    fun z hz => (hf.2 z (hT hz)).differentiableWithinAt
  obtain ⟨F, hF⟩ := hs.exists_forall_hasDerivWithinAt hd
  unfold triangleBoundaryIntegral
  rw [segment_integral_eq_sub hs hF hd.continuousOn ha hb,
    segment_integral_eq_sub hs hF hd.continuousOn hb hc,
    segment_integral_eq_sub hs hF hd.continuousOn hc ha]
  abel

/-- Two triangles, with the common diagonal traversed in opposite directions. -/
theorem goursat_parallelogram :
    Specs.D12Complex.Ch04.WeakGoursat.goursat_parallelogram_type := by
  intro a u v Ω f hf hP
  change parallelogramBoundaryIntegral a u v f = 0
  have h₁ : closedTriangle a (a + u) (a + u + v) ⊆ closedParallelogram a u v := by
    apply convexHull_mono
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz ⊢
    tauto
  have h₂ : closedTriangle a (a + u + v) (a + v) ⊆ closedParallelogram a u v := by
    apply convexHull_mono
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz ⊢
    tauto
  have ht₁ := goursat_triangle a (a + u) (a + u + v) Ω f hf (h₁.trans hP)
  have ht₂ := goursat_triangle a (a + u + v) (a + v) Ω f hf (h₂.trans hP)
  have hs : Convex ℝ (closedParallelogram a u v) := convex_convexHull ℝ _
  have ha : a ∈ closedParallelogram a u v := subset_convexHull ℝ _ (by simp)
  have hc : a + u + v ∈ closedParallelogram a u v := subset_convexHull ℝ _ (by simp)
  have hcont : ContinuousOn f (closedParallelogram a u v) :=
    fun z hz => (hf.2 z (hP hz)).continuousAt.continuousWithinAt
  have hr := segment_integral_reverse hs hcont ha hc
  change triangleBoundaryIntegral a (a + u) (a + u + v) f = 0 at ht₁
  change triangleBoundaryIntegral a (a + u + v) (a + v) f = 0 at ht₂
  unfold triangleBoundaryIntegral at ht₁ ht₂
  rw [hr] at ht₁
  unfold parallelogramBoundaryIntegral
  linear_combination ht₁ + ht₂

theorem goursat_rectangle : Specs.D12Complex.Ch04.WeakGoursat.goursat_rectangle_type := by
  intro a e w h Ω f hf hR
  exact goursat_parallelogram a ((w : ℂ) * e) ((h : ℂ) * Complex.I * e) Ω f hf hR

end D12Complex.WeakGoursat
