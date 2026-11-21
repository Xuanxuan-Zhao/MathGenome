import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitiveConstruction
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PolygonalConnectivity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace D12Complex.PrimitiveConstruction

/-- A straight segment with its actual affine parametrization. -/
def segmentPath (z w : ℂ) : PiecewiseC1Path :=
  let γ : ComplexPath := ⟨0, 1, zero_le_one, fun t => z + (t : ℂ) * (w - z),
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn⟩
  ⟨γ, ⟨C1Partition.single γ
    ((contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).contDiffOn)⟩⟩

@[simp] theorem segmentPath_source (z w : ℂ) : (segmentPath z w).path.source = z := by
  simp [segmentPath, PiecewiseC1Path.path, ComplexPath.source]

@[simp] theorem segmentPath_target (z w : ℂ) : (segmentPath z w).path.target = w := by
  simp [segmentPath, PiecewiseC1Path.path, ComplexPath.target]

theorem segmentPath_trace_subset (z w : ℂ) :
    (segmentPath z w).trace ⊆ segment ℝ z w := by
  rintro v ⟨t, ht, rfl⟩
  change z + (t : ℂ) * (w - z) ∈ segment ℝ z w
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply]; ring

/-- Concatenation, together with endpoint, trace, and integral laws. -/
theorem concatenate_in {Ω : Set ℂ} (γ η : PiecewiseC1Path)
    (hγ : γ.trace ⊆ Ω) (hη : η.trace ⊆ Ω)
    (hc : γ.path.target = η.path.source) (f : ℂ → ℂ) (hf : ContinuousOn f Ω) :
    ∃ δ : PiecewiseC1Path, δ.trace ⊆ Ω ∧ δ.path.source = γ.path.source ∧
      δ.path.target = η.path.target ∧ δ.integral f = γ.integral f + η.integral f := by
  obtain ⟨δ, ha, hb, h₁, h₂, hi⟩ :=
    PiecewiseC1Path.concatenation γ η f hc (hf.mono hγ) (hf.mono hη)
  refine ⟨δ, ?_, ?_, ?_, hi⟩
  · rintro v ⟨t, ht, rfl⟩
    rw [ha, hb] at ht
    by_cases ht1 : t ≤ 1
    · rw [h₁ ⟨ht.1, ht1⟩]
      apply hγ
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩ <;>
        nlinarith [γ.path.ordered, mul_nonneg (sub_nonneg.mpr γ.path.ordered) ht.1,
          mul_nonneg (sub_nonneg.mpr γ.path.ordered) (sub_nonneg.mpr ht1)]
    · rw [h₂ ⟨le_of_not_ge ht1, ht.2⟩]
      apply hη
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩ <;>
        nlinarith [η.path.ordered, mul_nonneg (sub_nonneg.mpr η.path.ordered)
          (sub_nonneg.mpr (le_of_not_ge ht1)),
          mul_nonneg (sub_nonneg.mpr η.path.ordered) (sub_nonneg.mpr ht.2)]
  · change δ δ.path.a = γ γ.path.a
    rw [ha, h₁ (by norm_num)]
    simp
  · change δ δ.path.b = η η.path.b
    rw [hb, h₂ (by norm_num)]
    apply congrArg η.path.toFun
    ring

/-- Promote each edge of a finite vertex list to a smooth path. -/
theorem path_of_vertices (Ω : Set ℂ) (a : ℂ) (ha : a ∈ Ω) (l : List ℂ)
    (hl : (a :: l).IsChain (fun x y => segment ℝ x y ⊆ Ω)) :
    ∃ γ : PiecewiseC1Path, γ.trace ⊆ Ω ∧ γ.path.source = a ∧
      γ.path.target = (a :: l).getLast (List.cons_ne_nil _ _) := by
  induction l generalizing a with
  | nil =>
    refine ⟨PiecewiseC1Path.const 0 0 le_rfl a, ?_, rfl, rfl⟩
    rintro v ⟨t, ht, rfl⟩
    exact ha
  | cons b l ih =>
    have hab : segment ℝ a b ⊆ Ω := (List.isChain_cons_cons.mp hl).1
    have hb : b ∈ Ω := hab (right_mem_segment ℝ a b)
    obtain ⟨γ, hγ, hs, ht⟩ := ih b hb (List.isChain_cons_cons.mp hl).2
    obtain ⟨δ, hδ, hds, hdt, _⟩ := concatenate_in (segmentPath a b) γ
      ((segmentPath_trace_subset a b).trans hab) hγ (by simpa using hs.symm)
      (fun _ => 0) continuousOn_const
    exact ⟨δ, hδ, hds.trans (segmentPath_source a b), by simpa using hdt.trans ht⟩

/-- Polygonal connectivity supplies canonical piecewise C1 paths, not just continuous paths. -/
theorem exists_path_in (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (a : ℂ) (ha : a ∈ Ω) (b : ℂ) (hb : b ∈ Ω) :
    ∃ γ : PiecewiseC1Path, γ.trace ⊆ Ω ∧ γ.path.source = a ∧ γ.path.target = b := by
  obtain ⟨l, hl, ht⟩ := polygonal_connectivity Ω hΩ hc a ha b hb
  obtain ⟨γ, hγ, hs, he⟩ := path_of_vertices Ω a ha l hl
  exact ⟨γ, hγ, hs, he.trans ht⟩

/-- The real derivative of the affine segment is its displacement. -/
theorem segment_deriv (z w : ℂ) (t : ℝ) :
    deriv (fun s : ℝ => z + (s : ℂ) * (w - z)) t = w - z := by
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - z)).const_add z |>.deriv

/-- Canonical contour integration along the segment is the ordinary parameter integral. -/
theorem segment_integral (z w : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (segmentPath z w).trace) :
    (segmentPath z w).integral f =
      (w - z) * ∫ t : ℝ in 0..1, f (z + (t : ℂ) * (w - z)) := by
  rw [PiecewiseC1Path.integral_congr_representative (segmentPath z w)
    (fun t : ℝ => z + (t : ℂ) * (w - z)) f hf (by intro t ht; rfl)]
  change (∫ t : ℝ in 0..1, f (z + (t : ℂ) * (w - z)) *
    deriv (fun s : ℝ => z + (s : ℂ) * (w - z)) t) = _
  simp_rw [segment_deriv, mul_comm (f _)]
  rw [intervalIntegral.integral_const_mul]

/-- Small affine displacements remain within a ball about their source. -/
theorem segment_norm_le (z h : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(z + (t : ℂ) * h) - z‖ ≤ ‖h‖ := by
  simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg h) ht.2

/-- Choose a path from a fixed basepoint inside the domain and integrate along it.
The value outside the domain is irrelevant and is set to zero. -/
def potential (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  open Classical in
  if hz : z ∈ Ω then
    (Classical.choose (exists_path_in Ω hΩ.2.1 hΩ.2.2 a ha z hz)).integral f
  else 0

/-- Independence identifies the chosen value with the integral of every admissible path. -/
theorem potential_eq_integral (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (f : ℂ → ℂ)
    (hind : ∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
      γ.path.source = η.path.source → γ.path.target = η.path.target →
      γ.integral f = η.integral f)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (hs : γ.path.source = a) :
    potential Ω hΩ a ha f γ.path.target = γ.integral f := by
  have ht : γ.path.target ∈ Ω := hγ ⟨γ.path.b, ⟨γ.path.ordered, le_rfl⟩, rfl⟩
  simp only [potential, dite_eq_left ht]
  have hc := Classical.choose_spec (exists_path_in Ω hΩ.2.1 hΩ.2.2 a ha γ.path.target ht)
  exact hind _ γ hc.1 hγ (hc.2.1.trans hs.symm) hc.2.2

/-- The normalized path-integral potential vanishes at the basepoint. -/
theorem potential_basepoint (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (f : ℂ → ℂ)
    (hind : ∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
      γ.path.source = η.path.source → γ.path.target = η.path.target →
      γ.integral f = η.integral f) : potential Ω hΩ a ha f a = 0 := by
  have he := potential_eq_integral Ω hΩ a ha f hind
    (PiecewiseC1Path.const 0 0 le_rfl a) (by rintro v ⟨t, ht, rfl⟩; exact ha) rfl
  exact he.trans (PiecewiseC1Path.const_integral 0 0 le_rfl a f)

/-- Endpoint independence gives the small-segment increment identity. -/
theorem potential_increment (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (f : ℂ → ℂ) (hf : ContinuousOn f Ω)
    (hind : ∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
      γ.path.source = η.path.source → γ.path.target = η.path.target →
      γ.integral f = η.integral f)
    (z : ℂ) (hz : z ∈ Ω) (h : ℂ) (hseg : (segmentPath z (z + h)).trace ⊆ Ω) :
    potential Ω hΩ a ha f (z + h) - potential Ω hΩ a ha f z =
      h * ∫ t : ℝ in 0..1, f (z + (t : ℂ) * h) := by
  obtain ⟨γ, hγ, hs, ht⟩ := exists_path_in Ω hΩ.2.1 hΩ.2.2 a ha z hz
  obtain ⟨δ, hδ, hds, hdt, hi⟩ := concatenate_in γ (segmentPath z (z + h)) hγ hseg
    (by simpa using ht) f hf
  have he := potential_eq_integral Ω hΩ a ha f hind δ hδ (hds.trans hs)
  have heγ := potential_eq_integral Ω hΩ a ha f hind γ hγ hs
  rw [hdt, segmentPath_target] at he
  rw [ht] at heγ
  rw [he, heγ, hi, add_sub_cancel_left, segment_integral _ _ f (hf.mono hseg)]
  simp

/-- The difference quotient tends to f(z), using only continuity of f. -/
theorem potential_hasDerivAt (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (f : ℂ → ℂ) (hf : ContinuousOn f Ω)
    (hind : ∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
      γ.path.source = η.path.source → γ.path.target = η.path.target →
      γ.integral f = η.integral f)
    (z : ℂ) (hz : z ∈ Ω) : HasDerivAt (potential Ω hΩ a ha f) (f z) z := by
  apply (hasComplexDerivativeAt_iff _ _ _).mp
  intro ε hε
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ.2.1 z hz
  obtain ⟨d, hd, hfd⟩ := (Metric.continuousWithinAt_iff.mp (hf z hz)) (ε / 2)
    (by linarith)
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro h _ hpos hsmall
  have hnorm : ‖h‖ < min r d := by simpa using hsmall
  have hh : h ≠ 0 := norm_pos_iff.mp (by simpa using hpos)
  have hmap : ∀ t ∈ Icc (0 : ℝ) 1, z + (t : ℂ) * h ∈ Ω := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (segment_norm_le z h ht) (lt_of_lt_of_le hnorm (min_le_left _ _))
  have hseg : (segmentPath z (z + h)).trace ⊆ Ω := by
    rintro v ⟨t, ht, rfl⟩
    change z + (t : ℂ) * (z + h - z) ∈ Ω
    simpa using hmap t ht
  have hi : IntervalIntegrable (fun t : ℝ => f (z + (t : ℂ) * h)) volume 0 1 := by
    exact (hf.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      hmap).intervalIntegrable_of_Icc zero_le_one
  have hbound : ‖∫ t : ℝ in 0..1, (f (z + (t : ℂ) * h) - f z)‖ ≤ ε / 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := ε / 2)
      (f := fun t : ℝ => f (z + (t : ℂ) * h) - f z) ?_
    · simpa using hb
    · intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 :=
        ⟨le_of_lt (by simpa using ht.1), by simpa using ht.2⟩
      apply le_of_lt
      have := hfd (hmap t ht')
        (by simpa only [dist_eq_norm] using
          (lt_of_le_of_lt (segment_norm_le z h ht')
            (lt_of_lt_of_le hnorm (min_le_right _ _))))
      simpa only [dist_eq_norm] using this
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const] at hbound
  have havg : ‖(∫ t : ℝ in 0..1, f (z + (t : ℂ) * h)) - f z‖ < ε := by
    have hb : ‖(∫ t : ℝ in 0..1, f (z + (t : ℂ) * h)) - f z‖ ≤ ε / 2 := by
      simpa using hbound
    exact lt_of_le_of_lt hb (by linarith)
  simpa only [potential_increment Ω hΩ a ha f hf hind z hz h hseg,
    mul_div_cancel_left₀ _ hh] using havg

/-- The normalized path integral is a holomorphic primitive, with the path formula
for every canonical piecewise C1 path on its own compact parameter interval. -/
theorem construction : Specs.D12Complex.Ch03.PrimitiveConstruction.construction_type := by
  intro Ω f hΩ hf hind a ha
  refine ⟨potential Ω hΩ a ha f, ⟨hΩ.2.1, ?_⟩, ?_,
    potential_basepoint Ω hΩ a ha f hind, ?_⟩
  · intro z hz
    exact (potential_hasDerivAt Ω hΩ a ha f hf hind z hz).differentiableAt
  · intro z hz
    exact (potential_hasDerivAt Ω hΩ a ha f hf hind z hz).deriv
  · intro γ hγ hs
    exact potential_eq_integral Ω hΩ a ha f hind γ hγ hs

/-- In particular, a continuous function with endpoint-independent integrals
has a holomorphic primitive on the domain. -/
theorem exists_primitive : Specs.D12Complex.Ch03.PrimitiveConstruction.exists_primitive_type := by
  intro Ω f hΩ hf hind
  obtain ⟨a, ha⟩ := hΩ.1
  obtain ⟨F, hF, hd, _, _⟩ := construction Ω f hΩ hf hind a ha
  exact ⟨F, hF, hd⟩

end D12Complex.PrimitiveConstruction
