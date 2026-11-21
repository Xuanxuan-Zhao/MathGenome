import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.DiskFillingCorrection
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.HigherHomotopy
import Mathlib.Analysis.Convex.GaugeRescale

namespace P202.Topology
open P202Specs.Topology
open scoped unitInterval _root_.Topology
universe u v
noncomputable section
set_option maxHeartbeats 800000

namespace DiskCube

private abbrev ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev coordinates (n : ℕ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
private def box (n : ℕ) : Set (ambient n) :=
  (coordinates n) ⁻¹' Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)

private theorem box_closed (n : ℕ) : IsClosed (box n) :=
  (isClosed_set_pi (fun _ _ => isClosed_Icc)).preimage (coordinates n).continuous

private theorem box_interior (n : ℕ) :
    interior (box n) = (coordinates n) ⁻¹' Set.univ.pi (fun _ => Set.Ioo (0 : ℝ) 1) := by
  change interior ((coordinates n).toHomeomorph ⁻¹' _) = _
  rw [← (coordinates n).toHomeomorph.preimage_interior,
    interior_pi_set Set.finite_univ]
  simp only [interior_Icc]
  rfl

private theorem box_frontier (n : ℕ) (z : ambient n) (hz : z ∈ box n) :
    z ∈ frontier (box n) ↔ ∃ i, z i = 0 ∨ z i = 1 := by
  classical
  rw [frontier, (box_closed n).closure_eq, Set.mem_sdiff, and_iff_right hz, box_interior]
  change (¬ ∀ i, i ∈ (Set.univ : Set (Fin n)) → z i ∈ Set.Ioo (0 : ℝ) 1) ↔ _
  simp only [Set.mem_univ, true_implies, Set.mem_Ioo, not_forall]
  constructor
  · rintro ⟨i, hi⟩
    have hzi : z i ∈ Set.Icc (0 : ℝ) 1 := hz i (Set.mem_univ _)
    exact ⟨i, by rcases le_or_gt (z i) 0 with h | h
                 · exact Or.inl (le_antisymm h hzi.1)
                 · exact Or.inr (le_antisymm hzi.2 (le_of_not_gt (fun h' => hi ⟨h, h'⟩)))⟩
  · rintro ⟨i, hi | hi⟩ <;> exact ⟨i, by simp [hi]⟩

private def cubeToBox (n : ℕ) : UnitCube n ≃ₜ box n where
  toFun z := ⟨WithLp.toLp 2 (fun i => (z i : ℝ)), fun i _ => (z i).property⟩
  invFun z i := ⟨z.val i, z.property i (Set.mem_univ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp _ _).comp (continuous_pi (fun i =>
      (continuous_apply i).subtype_val))
  continuous_invFun := continuous_pi (fun i =>
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) i).comp continuous_subtype_val).subtype_mk _)

/-- The literal Euclidean disk and the cube are homeomorphic as pairs.
This uses only convex subsets of the Euclidean source. -/
theorem exists_pair_homeomorph (n : ℕ) :
    ∃ e : UnitCube n ≃ₜ ClosedDisk n,
      ∀ z, z ∈ CubeBoundary n ↔ e z ∈ DiskBoundary n := by
  have hc : Convex ℝ (box n) :=
    (convex_pi (fun _ _ => convex_Icc (0 : ℝ) 1)).linear_preimage (coordinates n).toLinearMap
  have hne : (interior (box n)).Nonempty := by
    refine ⟨WithLp.toLp 2 (fun _ => (1 / 2 : ℝ)), ?_⟩
    rw [box_interior]
    intro i _
    norm_num
  have hcompact : IsCompact (box n) :=
    (coordinates n).toHomeomorph.isCompact_preimage.mpr (isCompact_univ_pi (fun _ => isCompact_Icc))
  obtain ⟨h, _, hball, hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hcompact.isBounded
  rw [(box_closed n).closure_eq] at hball
  let ed : box n ≃ₜ ClosedDisk n := h.subtype (fun z => by
    change z ∈ box n ↔ ‖h z‖ ≤ 1
    rw [← mem_closedBall_zero_iff, ← hball]
    exact h.injective.mem_set_image.symm)
  refine ⟨(cubeToBox n).trans ed, fun z => ?_⟩
  have heq : (h ((cubeToBox n) z)) ∈ Metric.sphere (0 : ambient n) 1 ↔
      ((cubeToBox n) z).val ∈ frontier (box n) := by
    rw [← hfront]
    exact h.injective.mem_set_image
  change (∃ i, z i = 0 ∨ z i = 1) ↔ ‖h ((cubeToBox n) z)‖ = 1
  rw [← mem_sphere_zero_iff_norm, heq,
    box_frontier n _ ((cubeToBox n) z).property]
  constructor <;> rintro ⟨i, hi⟩ <;> refine ⟨i, ?_⟩
  · rcases hi with hi | hi
    · exact Or.inl (congrArg Subtype.val hi)
    · exact Or.inr (congrArg Subtype.val hi)
  · rcases hi with hi | hi
    · exact Or.inl (Subtype.ext hi)
    · exact Or.inr (Subtype.ext hi)

/-- Surjectivity supplies an actual disk representative and a homotopy fixing
its entire boundary, when that boundary has one fixed value. -/
theorem basedDiskLift {Y : Type u} [TopologicalSpace Y] (A : Set Y) (n : ℕ)
    (x : A)
    (hs : Function.Surjective (higherInduced n
      (⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩ : PointedMap A Y x x.val)))
    (f : C(ClosedDisk (n + 1), Y))
    (hf : ∀ z ∈ DiskBoundary (n + 1), f z = x.val) :
    ∃ g : C(ClosedDisk (n + 1), A),
      (∀ z ∈ DiskBoundary (n + 1), g z = x) ∧
      Nonempty (f.HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp g) (DiskBoundary (n + 1))) := by
  obtain ⟨e, he⟩ := exists_pair_homeomorph (n + 1)
  let a : CubeMap (n + 1) x.val :=
    ⟨f.comp ⟨e, e.continuous⟩, fun z hz => hf (e z) ((he z).mp hz)⟩
  obtain ⟨q, hq⟩ := hs (cubeClass a)
  obtain ⟨b, rfl⟩ := cubeClass_surjective q
  let incl : PointedMap A Y x x.val := ⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩
  have hh : cubeClass (cubeMap incl b) = cubeClass a := hq
  obtain ⟨H⟩ := (higherClassEquality (n + 1) Y x.val _ _).mp hh.symm
  let g : C(ClosedDisk (n + 1), A) := b.val.comp ⟨e.symm, e.symm.continuous⟩
  refine ⟨g, ?_, ⟨?_⟩⟩
  · intro z hz
    exact GenLoop.boundary b (e.symm z) ((he _).mpr (by simpa using hz))
  · refine {
      toFun := fun p => H (p.1, e.symm p.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
      map_zero_left := fun z => ?_
      map_one_left := fun z => H.apply_one (e.symm z)
      prop' := fun t z hz => ?_ }
    · exact (H.apply_zero (e.symm z)).trans (congrArg f (e.apply_symm_apply z))
    · exact (H.eq_fst t ((he _).mpr (by simpa using hz))).trans
        (congrArg f (e.apply_symm_apply z))

end DiskCube

namespace DiskCollar

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def center (n : ℕ) : ClosedDisk n := ⟨0, by simp⟩

/-- Radial projection onto the literal closed Euclidean unit disk. -/
def project {n : ℕ} (z : E n) : ClosedDisk n :=
  ⟨(max 1 ‖z‖)⁻¹ • z, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact (inv_mul_le_one₀ (by positivity)).mpr (le_max_right _ _)⟩

theorem continuous_project {n : ℕ} : Continuous (@project n) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.max continuous_norm).inv₀ (fun _ => by positivity)).smul continuous_id

theorem project_of_norm_le {n : ℕ} {z : E n} (hz : ‖z‖ ≤ 1) :
    (project z).val = z := by
  simp [project, max_eq_left hz]

@[simp] theorem project_zero (n : ℕ) : project (0 : E n) = center n := by
  apply Subtype.ext
  simp [project, center]

@[simp] theorem project_coe {n : ℕ} (z : ClosedDisk n) : project z.val = z :=
  Subtype.ext (project_of_norm_le z.property)

/-- Continuous global versions of dilation and annular radial coordinates.
The cutoff in the denominator is immaterial outside radius one-quarter. -/
def dilate {n : ℕ} (c : ℝ) (z : ClosedDisk n) : ClosedDisk n := project (c • z.val)
def ray {n : ℕ} (c : ℝ) (z : ClosedDisk n) : ClosedDisk n :=
  dilate (c / max (1 / 4) ‖z.val‖) z

theorem continuous_dilate {n : ℕ} :
    Continuous (fun p : ℝ × ClosedDisk n => dilate p.1 p.2) :=
  continuous_project.comp (continuous_fst.smul continuous_snd.subtype_val)

theorem continuous_ray {n : ℕ} :
    Continuous (fun p : ℝ × ClosedDisk n => ray p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ClosedDisk n => p.1 / max (1 / 4) ‖p.2.val‖) :=
    continuous_fst.div (continuous_const.max continuous_snd.subtype_val.norm)
      (fun _ => by positivity)
  exact continuous_project.comp (hc.smul continuous_snd.subtype_val)

theorem dilate_boundary {n : ℕ} {c : ℝ} {z : ClosedDisk n}
    (hc : 0 ≤ c) (hz : c * ‖z.val‖ = 1) : dilate c z ∈ DiskBoundary n := by
  change ‖(project (c • z.val)).val‖ = 1
  have hn : ‖c • z.val‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, hz]
  rw [project_of_norm_le hn.le, hn]

theorem ray_eq_dilate {n : ℕ} (c : ℝ) (z : ClosedDisk n) (hz : 1 / 4 ≤ ‖z.val‖) :
    ray c z = dilate (c / ‖z.val‖) z := by
  unfold ray
  rw [max_eq_right hz]

@[simp] theorem ray_zero {n : ℕ} (z : ClosedDisk n) : ray 0 z = center n := by
  simp [ray, dilate]

theorem ray_boundary {n : ℕ} {z : ClosedDisk n} (hz : z ∈ DiskBoundary n) : ray 1 z = z := by
  change ‖z.val‖ = 1 at hz
  norm_num [ray, dilate, hz]

variable {Y : Type u} [TopologicalSpace Y] {n : ℕ}

/-- Attach the reverse of the radial contraction of the given filling. -/
def normalize (f g : C(ClosedDisk n, Y))
    (hg : ∀ z ∈ DiskBoundary n, f z = g z) : C(ClosedDisk n, Y) where
  toFun z := if ‖z.val‖ ≤ 1 / 2 then f (dilate 2 z)
    else g (ray (2 - 2 * ‖z.val‖) z)
  continuous_toFun := by
    apply continuous_if_le continuous_subtype_val.norm continuous_const
    · exact (f.continuous.comp ((continuous_dilate (n := n)).comp
        (continuous_const.prodMk continuous_id))).continuousOn
    · exact (g.continuous.comp ((continuous_ray (n := n)).comp
        ((continuous_const.sub (continuous_subtype_val.norm.const_mul 2)).prodMk continuous_id))).continuousOn
    · intro z hz
      have he : ray (2 - 2 * ‖z.val‖) z = dilate 2 z := by
        rw [ray_eq_dilate _ _ (by linarith)]
        congr 1
        rw [hz]
        norm_num
      rw [he]
      exact hg _ (dilate_boundary (by norm_num) (by linarith))

theorem normalize_boundary (f g : C(ClosedDisk n, Y))
    (hg : ∀ z ∈ DiskBoundary n, f z = g z) {z : ClosedDisk n} (hz : z ∈ DiskBoundary n) :
    normalize f g hg z = g (center n) := by
  change ‖z.val‖ = 1 at hz
  norm_num [normalize, hz]

/-- Restore a prescribed varying boundary around a constant-boundary disk. -/
def restore (g a : C(ClosedDisk n, Y))
    (ha : ∀ z ∈ DiskBoundary n, a z = g (center n)) : C(ClosedDisk n, Y) where
  toFun z := if ‖z.val‖ ≤ 1 / 2 then a (dilate 2 z)
    else g (ray (2 * ‖z.val‖ - 1) z)
  continuous_toFun := by
    apply continuous_if_le continuous_subtype_val.norm continuous_const
    · exact (a.continuous.comp ((continuous_dilate (n := n)).comp
        (continuous_const.prodMk continuous_id))).continuousOn
    · exact (g.continuous.comp ((continuous_ray (n := n)).comp
        ((continuous_subtype_val.norm.const_mul 2).sub continuous_const |>.prodMk continuous_id))).continuousOn
    · intro z hz
      have he : 2 * ‖z.val‖ - 1 = 0 := by linarith
      rw [he, ray_zero]
      exact ha _ (dilate_boundary (by norm_num) (by linarith))

theorem restore_boundary (g a : C(ClosedDisk n, Y))
    (ha : ∀ z ∈ DiskBoundary n, a z = g (center n)) {z : ClosedDisk n} (hz : z ∈ DiskBoundary n) :
    restore g a ha z = g z := by
  have hnorm : ‖z.val‖ = 1 := hz
  have hnot : ¬ ‖z.val‖ ≤ 1 / 2 := by rw [hnorm]; norm_num
  change (if _ then _ else _) = _
  rw [ite_eq_right hnot]
  have he : 2 * ‖z.val‖ - 1 = 1 := by rw [hnorm]; norm_num
  rw [he, ray_boundary hz]

/-- Restoration sends a homotopy at the constant boundary to one at the
original, generally varying, boundary. -/
def restoreHomotopy (g a b : C(ClosedDisk n, Y))
    (ha : ∀ z ∈ DiskBoundary n, a z = g (center n))
    (hb : ∀ z ∈ DiskBoundary n, b z = g (center n))
    (H : a.HomotopyRel b (DiskBoundary n)) :
    (restore g a ha).HomotopyRel (restore g b hb) (DiskBoundary n) where
  toFun p := if ‖p.2.val‖ ≤ 1 / 2 then H (p.1, dilate 2 p.2)
    else g (ray (2 * ‖p.2.val‖ - 1) p.2)
  continuous_toFun := by
    apply continuous_if_le continuous_snd.subtype_val.norm continuous_const
    · exact (H.continuous.comp (continuous_fst.prodMk
        ((continuous_dilate (n := n)).comp (continuous_const.prodMk continuous_snd)))).continuousOn
    · exact (g.continuous.comp ((continuous_ray (n := n)).comp
        ((continuous_snd.subtype_val.norm.const_mul 2).sub continuous_const |>.prodMk continuous_snd))).continuousOn
    · intro p hp
      have he : 2 * ‖p.2.val‖ - 1 = 0 := by linarith
      rw [he, ray_zero]
      exact (H.eq_fst p.1 (dilate_boundary (by norm_num) (by linarith))).trans
        (ha _ (dilate_boundary (by norm_num) (by linarith)))
  map_zero_left z := by
    change (if _ then _ else _) = (if _ then _ else _)
    split_ifs
    · exact H.apply_zero _
    · rfl
  map_one_left z := by
    change (if _ then _ else _) = (if _ then _ else _)
    split_ifs
    · exact H.apply_one _
    · rfl
  prop' t z hz := by
    have hnorm : ‖z.val‖ = 1 := hz
    have hnot : ¬ ‖z.val‖ ≤ 1 / 2 := by rw [hnorm]; norm_num
    change (if _ then _ else _) = _
    rw [ite_eq_right hnot, restore_boundary _ _ _ hz]
    have he : 2 * ‖z.val‖ - 1 = 1 := by rw [hnorm]; norm_num
    rw [he, ray_boundary hz]

@[simp] theorem dilate_one (z : ClosedDisk n) : dilate 1 z = z := by
  simp [dilate]

theorem dilate_val {c : ℝ} {z : ClosedDisk n} (hc : 0 ≤ c) (hz : c * ‖z.val‖ ≤ 1) :
    (dilate c z).val = c • z.val := by
  apply project_of_norm_le
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] using hz

theorem dilate_norm {c : ℝ} {z : ClosedDisk n} (hc : 0 ≤ c) (hz : c * ‖z.val‖ ≤ 1) :
    ‖(dilate c z).val‖ = c * ‖z.val‖ := by
  rw [dilate_val hc hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

theorem dilate_dilate {c d : ℝ} {z : ClosedDisk n} (hd : 0 ≤ d) (hz : d * ‖z.val‖ ≤ 1) :
    dilate c (dilate d z) = dilate (c * d) z := by
  change project (c • (dilate d z).val) = project ((c * d) • z.val)
  rw [dilate_val hd hz, smul_smul]

theorem ray_dilate_two (c : ℝ) (z : ClosedDisk n)
    (hlo : 1 / 4 ≤ ‖z.val‖) (hhi : ‖z.val‖ ≤ 1 / 2) :
    ray c (dilate 2 z) = ray c z := by
  have hr : 0 < ‖z.val‖ := by linarith
  have hd : 2 * ‖z.val‖ ≤ 1 := by linarith
  have hn := dilate_norm (z := z) (c := 2) (by norm_num) hd
  rw [ray_eq_dilate _ _ (by rw [hn]; linarith), ray_eq_dilate _ _ hlo, hn,
    dilate_dilate (by norm_num) hd]
  congr 1
  field_simp

private def innerRadius (s : unitInterval) : ℝ := 1 - 3 * s / 4
private def middleRadius (s : unitInterval) : ℝ := 1 - s / 2

private theorem innerRadius_ge (s : unitInterval) : 1 / 4 ≤ innerRadius s := by
  have := s.property.2
  unfold innerRadius
  linarith

private theorem innerRadius_le_middle (s : unitInterval) : innerRadius s ≤ middleRadius s := by
  have := s.property.1
  unfold innerRadius middleRadius
  linarith

/-- The two radial collars run out and back through the given filling.
This homotopy opens them with a positive inner radius at every time. -/
private def cancellationMap (f g : C(ClosedDisk n, Y))
    (hg : ∀ z ∈ DiskBoundary n, f z = g z) : C(unitInterval × ClosedDisk n, Y) where
  toFun p := if ‖p.2.val‖ ≤ innerRadius p.1 then
      f (dilate (innerRadius p.1)⁻¹ p.2)
    else if ‖p.2.val‖ ≤ middleRadius p.1 then
      g (ray (5 - 3 * p.1 - 4 * ‖p.2.val‖) p.2)
    else g (ray (2 * ‖p.2.val‖ - 1) p.2)
  continuous_toFun := by
    have hi : Continuous (fun p : unitInterval × ClosedDisk n => innerRadius p.1) := by
      unfold innerRadius
      fun_prop
    have hm : Continuous (fun p : unitInterval × ClosedDisk n => middleRadius p.1) := by
      unfold middleRadius
      fun_prop
    have hinv : Continuous (fun p : unitInterval × ClosedDisk n => (innerRadius p.1)⁻¹) :=
      hi.inv₀ (fun p => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (innerRadius_ge p.1)))
    have hfirst : Continuous (fun p : unitInterval × ClosedDisk n =>
        f (dilate (innerRadius p.1)⁻¹ p.2)) :=
      f.continuous.comp (continuous_project.comp (hinv.smul continuous_snd.subtype_val))
    have hcsecond : Continuous (fun p : unitInterval × ClosedDisk n =>
        5 - 3 * (p.1 : ℝ) - 4 * ‖p.2.val‖) := by fun_prop
    have hcthird : Continuous (fun p : unitInterval × ClosedDisk n =>
        2 * ‖p.2.val‖ - 1) := by fun_prop
    have hpsecond : Continuous (fun p : unitInterval × ClosedDisk n =>
        (5 - 3 * (p.1 : ℝ) - 4 * ‖p.2.val‖, p.2)) := hcsecond.prodMk continuous_snd
    have hpthird : Continuous (fun p : unitInterval × ClosedDisk n =>
        (2 * ‖p.2.val‖ - 1, p.2)) := hcthird.prodMk continuous_snd
    have hasecond := (continuous_ray (n := n)).comp hpsecond
    have hathird := (continuous_ray (n := n)).comp hpthird
    have hsecond : Continuous (fun p : unitInterval × ClosedDisk n =>
        g (ray (5 - 3 * (p.1 : ℝ) - 4 * ‖p.2.val‖) p.2)) := g.continuous.comp hasecond
    have hthird : Continuous (fun p : unitInterval × ClosedDisk n =>
        g (ray (2 * ‖p.2.val‖ - 1) p.2)) := g.continuous.comp hathird
    have houter : Continuous (fun p : unitInterval × ClosedDisk n =>
        if ‖p.2.val‖ ≤ middleRadius p.1 then
          g (ray (5 - 3 * p.1 - 4 * ‖p.2.val‖) p.2)
        else g (ray (2 * ‖p.2.val‖ - 1) p.2)) := by
      apply continuous_if_le continuous_snd.subtype_val.norm hm hsecond.continuousOn hthird.continuousOn
      intro p hp
      congr 2
      unfold middleRadius at hp
      linarith
    apply continuous_if_le continuous_snd.subtype_val.norm hi hfirst.continuousOn houter.continuousOn
    intro p hp
    have hr : 0 < ‖p.2.val‖ := lt_of_lt_of_le (by norm_num) ((innerRadius_ge p.1).trans_eq hp.symm)
    have hl : ‖p.2.val‖ ≤ middleRadius p.1 := hp ▸ innerRadius_le_middle p.1
    rw [ite_eq_left hl]
    have he : 5 - 3 * (p.1 : ℝ) - 4 * ‖p.2.val‖ = 1 := by
      unfold innerRadius at hp
      linarith
    rw [he, ray_eq_dilate _ _ ((innerRadius_ge p.1).trans_eq hp.symm), hp]
    change f (dilate _ _) = g (dilate _ _)
    rw [one_div]
    apply hg
    exact dilate_boundary (inv_nonneg.mpr (le_of_lt (hp ▸ hr))) (by
      rw [hp]
      exact inv_mul_cancel₀ (ne_of_gt (hp ▸ hr)))

private theorem cancellation_zero (f g : C(ClosedDisk n, Y))
    (hg : ∀ z ∈ DiskBoundary n, f z = g z) (z : ClosedDisk n) :
    cancellationMap f g hg (0, z) = f z := by
  change (if ‖z.val‖ ≤ innerRadius 0 then _ else _) = _
  have hi : innerRadius 0 = 1 := by norm_num [innerRadius]
  rw [hi, ite_eq_left z.property, inv_one, dilate_one]

private theorem cancellation_one (f g : C(ClosedDisk n, Y))
    (hg : ∀ z ∈ DiskBoundary n, f z = g z) (z : ClosedDisk n) :
    cancellationMap f g hg (1, z) =
      restore g (normalize f g hg) (fun z hz => normalize_boundary f g hg hz) z := by
  have hformula : cancellationMap f g hg (1, z) =
      if ‖z.val‖ ≤ 1 / 4 then f (dilate 4 z)
      else if ‖z.val‖ ≤ 1 / 2 then g (ray (2 - 4 * ‖z.val‖) z)
      else g (ray (2 * ‖z.val‖ - 1) z) := by
    change (if ‖z.val‖ ≤ innerRadius 1 then f (dilate (innerRadius 1)⁻¹ z)
      else if ‖z.val‖ ≤ middleRadius 1 then g (ray (5 - 3 * (1 : unitInterval) - 4 * ‖z.val‖) z)
      else g (ray (2 * ‖z.val‖ - 1) z)) = _
    norm_num [innerRadius, middleRadius]
  rw [hformula]
  change _ = if ‖z.val‖ ≤ 1 / 2 then normalize f g hg (dilate 2 z) else _
  by_cases hs : ‖z.val‖ ≤ 1 / 4
  · have hm : ‖z.val‖ ≤ 1 / 2 := by linarith
    have hd : 2 * ‖z.val‖ ≤ 1 := by linarith
    have hn := dilate_norm (z := z) (c := 2) (by norm_num) hd
    rw [ite_eq_left hs, ite_eq_left hm]
    change _ = if ‖(dilate 2 z).val‖ ≤ 1 / 2 then _ else _
    rw [hn, ite_eq_left (by linarith : 2 * ‖z.val‖ ≤ 1 / 2),
      dilate_dilate (by norm_num) hd]
    norm_num
  · rw [ite_eq_right hs]
    by_cases hm : ‖z.val‖ ≤ 1 / 2
    · have hd : 2 * ‖z.val‖ ≤ 1 := by linarith
      have hn := dilate_norm (z := z) (c := 2) (by norm_num) hd
      rw [ite_eq_left hm, ite_eq_left hm]
      change _ = if ‖(dilate 2 z).val‖ ≤ 1 / 2 then _ else _
      rw [hn, ite_eq_right (by linarith : ¬ 2 * ‖z.val‖ ≤ 1 / 2),
        ray_dilate_two _ _ (by linarith) hm]
      congr 2
      ring
    · rw [ite_eq_right hm, ite_eq_right hm]

/-- Normalization followed by restoration is homotopic to the original disk,
fixing every point of its original boundary. -/
def cancellation (f g : C(ClosedDisk n, Y))
    (hg : ∀ z ∈ DiskBoundary n, f z = g z) :
    f.HomotopyRel (restore g (normalize f g hg)
      (fun z hz => normalize_boundary f g hg hz)) (DiskBoundary n) where
  toContinuousMap := cancellationMap f g hg
  map_zero_left := cancellation_zero f g hg
  map_one_left := cancellation_one f g hg
  prop' t z hz := by
    have hnorm : ‖z.val‖ = 1 := hz
    change (if ‖z.val‖ ≤ innerRadius t then _ else _) = f z
    split_ifs with hi hm
    · have ht : t = 0 := by
        apply Subtype.ext
        change (t : ℝ) = 0
        have := t.property.1
        unfold innerRadius at hi
        rw [hnorm] at hi
        linarith
      subst t
      norm_num [innerRadius]
    · have hr : ‖z.val‖ ≤ innerRadius t := by
        have ht := t.property.1
        unfold innerRadius middleRadius at *
        rw [hnorm] at *
        linarith
      exact (hi hr).elim
    · have he : 2 * ‖z.val‖ - 1 = 1 := by rw [hnorm]; norm_num
      rw [he, ray_boundary hz]
      exact (hg z hz).symm

end DiskCollar


/-- Correct an already given filling using only surjectivity in the disk's
own positive dimension. No restrictions are imposed on the target pair. -/
theorem diskFillingCorrection : ExpectedDiskFillingCorrection.fillingCorrection.{u} := by
  intro Y _ A n hs f g hg
  let incl : C(A, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let gy : C(ClosedDisk (n + 2), Y) := incl.comp g
  have hfg : ∀ z ∈ DiskBoundary (n + 2), f.val z = gy z := fun z hz => (hg z hz).symm
  let a := DiskCollar.normalize f.val gy hfg
  have ha : ∀ z ∈ DiskBoundary (n + 2), a z = (g (DiskCollar.center (n + 2))).val :=
    fun z hz => DiskCollar.normalize_boundary f.val gy hfg hz
  obtain ⟨b, hb, ⟨K⟩⟩ := DiskCube.basedDiskLift A (n + 1) (g (DiskCollar.center (n + 2)))
    (hs _) a ha
  let g' := DiskCollar.restore g b hb
  have hby : ∀ z ∈ DiskBoundary (n + 2), (incl.comp b) z = gy (DiskCollar.center (n + 2)) :=
    fun z hz => congrArg Subtype.val (hb z hz)
  let H := DiskCollar.restoreHomotopy gy a (incl.comp b) ha hby K
  have he : DiskCollar.restore gy (incl.comp b) hby = incl.comp g' := by
    ext z
    change (if ‖z.val‖ ≤ 1 / 2 then (b (DiskCollar.dilate 2 z)).val
      else (g (DiskCollar.ray (2 * ‖z.val‖ - 1) z)).val) =
      (if ‖z.val‖ ≤ 1 / 2 then b (DiskCollar.dilate 2 z)
      else g (DiskCollar.ray (2 * ‖z.val‖ - 1) z)).val
    split_ifs <;> rfl
  exact ⟨g', ⟨((DiskCollar.cancellation f.val gy hfg).trans H).cast rfl he⟩⟩

end
end P202.Topology
