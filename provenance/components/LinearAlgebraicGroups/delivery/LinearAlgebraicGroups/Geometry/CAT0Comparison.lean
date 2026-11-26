import LinearAlgebraicGroups.Geometry.CAT0Spaces
import Mathlib.Topology.Subpath
import Mathlib.Tactic.Module

/-! Squared distance and midpoint comparisons in CAT(0) spaces. -/

open Set unitInterval

noncomputable section

namespace LinearAlgebraicGroups.Geometry

variable {X : Type*} [MetricSpace X]

private abbrev mid : I := ⟨1 / 2, by norm_num⟩

/-- Squared distance from a fixed point satisfies the CAT(0) segment estimate. -/
def SquaredDistanceComparison (X : Type*) [MetricSpace X] : Prop :=
  ∀ (z : X) {a b : X} (p : GeodesicSegment a b) (t : I),
    dist z (p.val t) ^ 2 ≤
      (1 - (t : ℝ)) * dist z a ^ 2 + (t : ℝ) * dist z b ^ 2 -
        (t : ℝ) * (1 - (t : ℝ)) * dist a b ^ 2

/-- The squared distance estimate at segment midpoints. -/
def MidpointComparison (X : Type*) [MetricSpace X] : Prop :=
  ∀ (z : X) {a b : X} (p : GeodesicSegment a b),
    dist z (p.val mid) ^ 2 ≤
      (dist z a ^ 2 + dist z b ^ 2) / 2 - dist a b ^ 2 / 4

namespace GeodesicSegment

theorem dist_source {a b : X} (p : GeodesicSegment a b) (t : I) :
    dist a (p.val t) = (t : ℝ) * dist a b := by
  have h := p.prop 0 t
  simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (neg_nonpos.mpr t.2.1)] using h

theorem dist_target {a b : X} (p : GeodesicSegment a b) (t : I) :
    dist (p.val t) b = (1 - (t : ℝ)) * dist a b := by
  have h := p.prop t 1
  simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.2.2), neg_sub] using h

def subpath {a b : X} (p : GeodesicSegment a b) (s t : I) :
    GeodesicSegment (p.val s) (p.val t) := by
  refine ⟨p.val.subpath s t, ?_⟩
  intro u v
  change dist (p.val (Icc.convexComb s t u)) (p.val (Icc.convexComb s t v)) = _
  rw [p.prop, p.prop s t]
  simp only [Subtype.dist_eq, Real.dist_eq, Icc.coe_convexComb]
  rw [show (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * (t : ℝ) -
      ((1 - (v : ℝ)) * (s : ℝ) + (v : ℝ) * (t : ℝ)) =
      ((u : ℝ) - (v : ℝ)) * ((t : ℝ) - (s : ℝ)) by ring, abs_mul, abs_sub_comm (t : ℝ), mul_assoc]

def reverse {a b : X} (p : GeodesicSegment a b) : GeodesicSegment b a := by
  refine ⟨p.val.symm, ?_⟩
  intro s t
  change dist (p.val (σ s)) (p.val (σ t)) = _
  rw [p.prop, dist_comm b a]
  congr 1
  simp only [Subtype.dist_eq, Real.dist_eq, coe_symm_eq]
  rw [show 1 - (s : ℝ) - (1 - (t : ℝ)) = (t : ℝ) - (s : ℝ) by ring, abs_sub_comm]

def mapIsometry {Y : Type*} [MetricSpace Y] {f : X → Y} (hf : Isometry f)
    {a b : X} (p : GeodesicSegment a b) : GeodesicSegment (f a) (f b) := by
  refine ⟨p.val.map hf.continuous, ?_⟩
  intro s t
  change dist (f (p.val s)) (f (p.val t)) = _
  rw [hf.dist_eq, hf.dist_eq, p.prop]

end GeodesicSegment

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem affine_dist_sq (z a b : E) (t : ℝ) :
    dist z ((1 - t) • a + t • b) ^ 2 =
      (1 - t) * dist z a ^ 2 + t * dist z b ^ 2 - t * (1 - t) * dist a b ^ 2 := by
  simp only [dist_eq_norm]
  rw [show z - ((1 - t) • a + t • b) = (1 - t) • (z - a) + t • (z - b) by module,
      norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right]
  rw [show a - b = (z - b) - (z - a) by abel, norm_sub_sq_real (z - b) (z - a), real_inner_comm (z - b) (z - a)]
  ring

private theorem affine_dist (a b : E) (s t : ℝ) :
    dist ((1 - s) • a + s • b) ((1 - t) • a + t • b) = |s - t| * dist a b := by
  simp only [dist_eq_norm]
  rw [show (1 - s) • a + s • b - ((1 - t) • a + t • b) = (t - s) • (a - b) by module,
      norm_smul, Real.norm_eq_abs, abs_sub_comm]

end InnerProductSpace

private def triangleSides {a b c : X}
    (p : GeodesicSegment a b) (q : GeodesicSegment b c) (r : GeodesicSegment c a) :
    ∀ i : Fin 3, GeodesicSegment (![a, b, c] i) (![a, b, c] (i + 1)) := by
  exact Fin.cases p (Fin.cases q (Fin.cases r (fun i => Fin.elim0 i)))

theorem CAT0.squaredDistanceComparison (h : CAT0 X) : SquaredDistanceComparison X := by
  intro z a b p t
  obtain ⟨q⟩ := h.1.2 b z
  obtain ⟨r⟩ := h.1.2 z a
  let v : Fin 3 → X := ![a, b, z]
  obtain ⟨w, hw⟩ := exists_comparisonTriangle v
  have hcmp := h.2 v (triangleSides p q r) w hw 0 2 t 0
  change dist (p.val t) (r.val 0) ≤
    dist ((1 - (t : ℝ)) • w 0 + (t : ℝ) • w 1)
      ((1 - ((0 : I) : ℝ)) • w 2 + ((0 : I) : ℝ) • w 0) at hcmp
  simp only [Path.source, show ((0 : I) : ℝ) = 0 from rfl, sub_zero, one_smul, zero_smul, add_zero] at hcmp
  have hsq := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr hcmp
  rw [dist_comm (p.val t) z, dist_comm _ (w 2), affine_dist_sq,
    hw 2 0, hw 2 1, hw 0 1] at hsq
  exact hsq

theorem SquaredDistanceComparison.midpointComparison (h : SquaredDistanceComparison X) :
    MidpointComparison X := by
  intro z a b p
  have ht := h z p mid
  change _ ≤ (1 - (1 / 2 : ℝ)) * _ + (1 / 2 : ℝ) * _ -
    (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) * _ at ht
  linarith only [ht]

theorem MidpointComparison.squaredDistanceComparison (h : MidpointComparison X) :
    SquaredDistanceComparison X := by
  intro z a b p t
  -- Subtract the quadratic on the right-hand side to obtain a midpoint-convex gap.
  let f : I → ℝ := fun s => dist z (p.val s) ^ 2 -
    ((1 - (s : ℝ)) * dist z a ^ 2 + (s : ℝ) * dist z b ^ 2 -
      (s : ℝ) * (1 - (s : ℝ)) * dist a b ^ 2)
  have hf : Continuous f := by unfold f; fun_prop
  have hzero : f 0 = 0 := by simp [f]
  have hone : f 1 = 0 := by simp [f]
  have hconv : ∀ s u : I, f (Icc.convexComb s u mid) ≤ (f s + f u) / 2 := by
    intro s u
    have hm := h z (p.subpath s u)
    change dist z (p.val (Icc.convexComb s u mid)) ^ 2 ≤ _ at hm
    rw [p.prop, Subtype.dist_eq, Real.dist_eq, mul_pow, sq_abs] at hm
    simp only [f, Icc.coe_convexComb]
    nlinarith only [hm]
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMaxOn
    (univ_nonempty : (univ : Set I).Nonempty) hf.continuousOn
  have hmax (s : I) : f s ≤ f m := hm (mem_univ s)
  -- A maximizing point is the midpoint of a subinterval with one original endpoint.
  have hnonpos : f m ≤ 0 := by
    rcases le_or_gt (m : ℝ) (1 / 2) with hleft | hright
    · let u : I := ⟨2 * (m : ℝ), ⟨by linarith [m.2.1], by linarith⟩⟩
      have heq : Icc.convexComb 0 u mid = m := by
        apply Subtype.ext
        change (1 - 1 / 2 : ℝ) * 0 + (1 / 2) * (2 * (m : ℝ)) = (m : ℝ)
        ring
      have hmid := hconv 0 u
      rw [heq, hzero] at hmid
      linarith only [hmid, hmax u]
    · let s : I := ⟨2 * (m : ℝ) - 1, ⟨by linarith, by linarith [m.2.2]⟩⟩
      have heq : Icc.convexComb s 1 mid = m := by
        apply Subtype.ext
        change (1 - 1 / 2 : ℝ) * (2 * (m : ℝ) - 1) + (1 / 2) * 1 = (m : ℝ)
        ring
      have hmid := hconv s 1
      rw [heq, hone] at hmid
      linarith only [hmid, hmax s]
  exact sub_nonpos.mp ((hmax t).trans hnonpos)


private theorem adjacentComparison (h : SquaredDistanceComparison X)
    {a b c : X} (p : GeodesicSegment a b) (q : GeodesicSegment b c)
    (A B C : EuclideanPlane)
    (hab : dist A B = dist a b) (hac : dist A C = dist a c)
    (hbc : dist B C = dist b c) (s t : I) :
    dist (p.val s) (q.val t) ≤
      dist ((1 - (s : ℝ)) • A + (s : ℝ) • B) ((1 - (t : ℝ)) • B + (t : ℝ) • C) := by
  let P := (1 - (s : ℝ)) • A + (s : ℝ) • B
  have hpC : dist (p.val s) c ^ 2 ≤ dist P C ^ 2 := by
    rw [dist_comm (p.val s) c, dist_comm P C]
    dsimp only [P]
    rw [affine_dist_sq, dist_comm C A, dist_comm C B, hab, hac, hbc,
      dist_comm a c, dist_comm b c]
    exact h c p s
  have hpB : dist (p.val s) b = dist P B := by
    rw [p.dist_target]
    have heq := affine_dist A B (s : ℝ) 1
    simpa [P, hab, abs_of_nonpos (sub_nonpos.mpr s.2.2), neg_sub] using heq.symm
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  change _ ≤ dist P ((1 - (t : ℝ)) • B + (t : ℝ) • C) ^ 2
  rw [affine_dist_sq, hbc, ← hpB]
  exact (h (p.val s) q t).trans
    (sub_le_sub_right (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpC t.2.1)) _)

theorem SquaredDistanceComparison.cat0 (h : SquaredDistanceComparison X)
    (hg : IsGeodesicSpace X) : CAT0 X := by
  refine ⟨hg, ?_⟩
  intro v side w hw i j s t
  have adjacent (k : Fin 3) (s t : I) :=
    adjacentComparison h (side k) (side (k + 1))
      (w k) (w (k + 1)) (w (k + 1 + 1))
      (hw k (k + 1)) (hw k (k + 1 + 1)) (hw (k + 1) (k + 1 + 1)) s t
  by_cases heq : i = j
  · subst j
    rw [(side i).prop, affine_dist, hw, Subtype.dist_eq, Real.dist_eq]
  · by_cases hj : j = i + 1
    · subst j
      exact adjacent i s t
    · have hi : i = j + 1 := by
        fin_cases i <;> fin_cases j <;> first
          | decide
          | exact (heq (by decide)).elim
          | exact (hj (by decide)).elim
      subst i
      rw [dist_comm]
      exact (adjacent j t s).trans_eq (dist_comm _ _)

theorem cat0_iff_squaredDistanceComparison (hg : IsGeodesicSpace X) :
    CAT0 X ↔ SquaredDistanceComparison X :=
  ⟨CAT0.squaredDistanceComparison, fun h => h.cat0 hg⟩

theorem cat0_iff_midpointComparison (hg : IsGeodesicSpace X) :
    CAT0 X ↔ MidpointComparison X :=
  ⟨fun h => h.squaredDistanceComparison.midpointComparison,
    fun h => h.squaredDistanceComparison.cat0 hg⟩

theorem CAT0.uniquelyGeodesic (h : CAT0 X) : IsUniquelyGeodesic X := by
  refine ⟨h.1, fun a b => ⟨fun p q => ?_⟩⟩
  apply Subtype.ext
  ext t
  apply dist_eq_zero.mp
  have hsq := h.squaredDistanceComparison (p.val t) q t
  rw [dist_comm (p.val t) a, p.dist_source, p.dist_target] at hsq
  have hr : (1 - (t : ℝ)) * ((t : ℝ) * dist a b) ^ 2 +
      (t : ℝ) * ((1 - (t : ℝ)) * dist a b) ^ 2 -
        (t : ℝ) * (1 - (t : ℝ)) * dist a b ^ 2 = 0 := by ring
  rw [hr] at hsq
  nlinarith only [hsq, dist_nonneg (x := p.val t) (y := q.val t)]

private theorem distAlongSegmentsSameSource (h : SquaredDistanceComparison X)
    {a b c : X} (p : GeodesicSegment a b) (q : GeodesicSegment a c) (t : I) :
    dist (p.val t) (q.val t) ≤ (t : ℝ) * dist b c := by
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg t.2.1 dist_nonneg)).mp
  have h₁ := h c p t
  have h₂ := h (p.val t) q t
  rw [dist_comm (p.val t) a, p.dist_source, dist_comm (p.val t) c] at h₂
  have h₃ := mul_le_mul_of_nonneg_left h₁ t.2.1
  rw [dist_comm c a, dist_comm c b] at h₃
  nlinarith only [h₂, h₃]

theorem CAT0.distAlongSegments (h : CAT0 X)
    {a b c d : X} (p : GeodesicSegment a b) (q : GeodesicSegment c d) (t : I) :
    dist (p.val t) (q.val t) ≤ (1 - (t : ℝ)) * dist a c + (t : ℝ) * dist b d := by
  obtain ⟨r⟩ := h.1.2 a d
  have h₁ := distAlongSegmentsSameSource h.squaredDistanceComparison p r t
  have h₂ := distAlongSegmentsSameSource h.squaredDistanceComparison r.reverse q.reverse (σ t)
  change dist (r.val (σ (σ t))) (q.val (σ (σ t))) ≤ (σ t : ℝ) * dist a c at h₂
  rw [symm_symm, coe_symm_eq] at h₂
  calc
    _ ≤ dist (p.val t) (r.val t) + dist (r.val t) (q.val t) := dist_triangle _ _ _
    _ ≤ _ := by linarith only [h₁, h₂]

theorem CAT0.quadrilateral (h : CAT0 X) (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  obtain ⟨p⟩ := h.1.2 a c
  have hmid := h.squaredDistanceComparison.midpointComparison
  have hb := hmid b p
  have hd := hmid d p
  rw [dist_comm b a] at hb
  rw [dist_comm d c] at hd
  have htri := dist_triangle b (p.val mid) d
  rw [dist_comm (p.val mid) d] at htri
  have hsq := (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr htri
  nlinarith only [hb, hd, hsq, sq_nonneg (dist b (p.val mid) - dist d (p.val mid))]

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def affineSegment (a b : E) : GeodesicSegment a b := by
  refine ⟨{ toFun := fun t : I => (1 - (t : ℝ)) • a + (t : ℝ) • b
            continuous_toFun := by fun_prop
            source' := by simp
            target' := by simp }, ?_⟩
  intro s t
  exact affine_dist a b (s : ℝ) (t : ℝ)

theorem cat0_of_realInnerProductSpace : CAT0 E := by
  apply SquaredDistanceComparison.cat0 _ ⟨⟨0⟩, fun a b => ⟨affineSegment a b⟩⟩
  intro z a b p t
  have h : p.val t = (1 - (t : ℝ)) • a + (t : ℝ) • b := by
    apply dist_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [affine_dist_sq, dist_comm (p.val t) a, p.dist_source, p.dist_target]
    ring
  rw [h, affine_dist_sq]

end InnerProductSpace

theorem euclidean_cat0 (n : ℕ) : CAT0 (EuclideanSpace ℝ (Fin n)) :=
  cat0_of_realInnerProductSpace

/-- A metric tree in the zero-slim triangle characterization. -/
def IsMetricTree (X : Type*) [MetricSpace X] : Prop :=
  IsGeodesicSpace X ∧
    ∀ {a b c : X} (p : GeodesicSegment a b) (q : GeodesicSegment a c)
      (r : GeodesicSegment b c) (t : I),
      p.val t ∈ range q.val ∪ range r.val

private theorem midpointEstimateOfAdditive
    (A B L R : ℝ) (hAB : A = R + L / 2) (hB : |R - L / 2| ≤ B) (hn : 0 ≤ B) :
    R ^ 2 ≤ (A ^ 2 + B ^ 2) / 2 - L ^ 2 / 4 := by
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).mpr hB
  rw [sq_abs] at hs
  rw [hAB]
  nlinarith only [hs]

theorem IsMetricTree.cat0 (h : IsMetricTree X) : CAT0 X := by
  apply (cat0_iff_midpointComparison h.1).mpr
  intro z a b p
  obtain ⟨q⟩ := h.1.2 a z
  obtain ⟨r⟩ := h.1.2 b z
  let m := p.val mid
  have ha : dist a m = dist a b / 2 := by
    rw [p.dist_source]
    change (1 / 2 : ℝ) * dist a b = dist a b / 2
    ring
  have hb : dist b m = dist a b / 2 := by
    rw [dist_comm b m, p.dist_target]
    change (1 - 1 / 2 : ℝ) * dist a b = dist a b / 2
    ring
  change dist z m ^ 2 ≤ _
  rcases h.2 p q r mid with ⟨u, hu⟩ | ⟨u, hu⟩
  · have hadd : dist z a = dist z m + dist a b / 2 := by
      change q.val u = m at hu
      rw [← ha, ← hu, dist_comm z a, dist_comm z (q.val u), q.dist_source, q.dist_target]
      ring
    apply midpointEstimateOfAdditive _ _ _ _ hadd _ dist_nonneg
    rw [← hb]
    exact abs_dist_sub_le z b m
  · have hadd : dist z b = dist z m + dist a b / 2 := by
      change r.val u = m at hu
      rw [← hb, ← hu, dist_comm z b, dist_comm z (r.val u), r.dist_source, r.dist_target]
      ring
    rw [add_comm (dist z a ^ 2)]
    apply midpointEstimateOfAdditive _ _ _ _ hadd _ dist_nonneg
    rw [← ha]
    exact abs_dist_sub_le z a m

theorem isClosed_minset (g : X ≃ᵢ X) : IsClosed (minset g) :=
  isClosed_eq (continuous_id.dist g.isometry.continuous) continuous_const

theorem CAT0.geodesicConvex_minset (h : CAT0 X) (g : X ≃ᵢ X) :
    GeodesicConvex (minset g) := by
  intro a b ha hb p t
  change dist a (g a) = translationLength g at ha
  change dist b (g b) = translationLength g at hb
  change dist (p.val t) (g (p.val t)) = translationLength g
  have hu := h.distAlongSegments p (p.mapIsometry g.isometry) t
  change dist (p.val t) (g (p.val t)) ≤ _ at hu
  rw [ha, hb] at hu
  refine le_antisymm (by linarith only [hu]) ?_
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact dist_nonneg⟩ _

theorem isClosed_commonMinset {ι : Type*} (f : ι → X ≃ᵢ X) :
    IsClosed (commonMinset f) :=
  isClosed_iInter fun i => isClosed_minset (f i)

theorem CAT0.geodesicConvex_commonMinset {ι : Type*} (h : CAT0 X) (f : ι → X ≃ᵢ X) :
    GeodesicConvex (commonMinset f) := by
  intro a b ha hb p t
  simp only [commonMinset, mem_iInter] at ha hb ⊢
  exact fun i => h.geodesicConvex_minset (f i) (ha i) (hb i) p t

theorem CAT0.convexSubtype (h : CAT0 X) {C : Set X} (hn : C.Nonempty)
    (hc : GeodesicConvex C) : CAT0 C := by
  have hg : IsGeodesicSpace C := by
    refine ⟨hn.to_subtype, fun a b => ?_⟩
    obtain ⟨p⟩ := h.1.2 (a : X) (b : X)
    let q : Path a b :=
      { toFun := fun t => ⟨p.val t, hc a.prop b.prop p t⟩
        continuous_toFun := p.val.continuous.subtype_mk _
        source' := Subtype.ext p.val.source
        target' := Subtype.ext p.val.target }
    exact ⟨⟨q, p.prop⟩⟩
  apply (cat0_iff_squaredDistanceComparison hg).mpr
  intro z a b p t
  exact h.squaredDistanceComparison (z : X) (p.mapIsometry isometry_subtype_coe) t

theorem CAT0.closedConvexSubtype [CompleteSpace X] (h : CAT0 X) {C : Set X}
    (hn : C.Nonempty) (hclosed : IsClosed C) (hc : GeodesicConvex C) :
    CAT0 C ∧ CompleteSpace C :=
  ⟨h.convexSubtype hn hc, hclosed.completeSpace_coe⟩

end LinearAlgebraicGroups.Geometry
