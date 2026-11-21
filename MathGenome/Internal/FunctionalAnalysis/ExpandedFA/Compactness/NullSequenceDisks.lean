import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.NullSequenceDisks
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy

namespace ExpandedFA.Compactness
universe u v
noncomputable section
open Set Filter
open scoped Topology Pointwise
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E

def nullSequenceDisk (z : ℕ → E) : Set E :=
  NullSequenceDisksSpec.ClosedDiskValue (𝕜 := 𝕜) z

/-- Scalar-balanced hulls of relatively compact sets are totally bounded. -/
theorem totallyBounded_balancedHull_of_isCompact {K : Set E} (hK : IsCompact K) :
    TotallyBounded (balancedHull 𝕜 K) := by
  let : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  have hc := (isCompact_closedBall (0 : 𝕜) 1).prod hK
  have hi := hc.image (continuous_fst.smul continuous_snd :
    Continuous (fun p : 𝕜 × E => p.1 • p.2))
  apply hi.totallyBounded.subset
  rintro x hx
  obtain ⟨a, ha, y, hy, rfl⟩ := mem_balancedHull_iff.mp hx
  exact ⟨(a,y), ⟨by simpa using ha, hy⟩, rfl⟩

/-- A null sequence has a compact closed absolutely convex hull. -/
theorem isCompact_nullSequenceDisk [CompleteSpace E] (z : ℕ → E)
    (hz : Tendsto z atTop (𝓝 0)) : IsCompact (nullSequenceDisk (𝕜 := 𝕜) z) := by
  have ht : TotallyBounded (balancedHull 𝕜 (range z)) :=
    (totallyBounded_balancedHull_of_isCompact (𝕜 := 𝕜) hz.isCompact_insert_range).subset
      (balancedHull_mono (subset_insert 0 (range z)))
  exact ht.convexHull.closure.isCompact_of_isClosed isClosed_closure

/-- Balancedness is preserved by the real convex hull, including for
complex scalars. -/
theorem balanced_real_convexHull {C : Set E} (hC : Balanced 𝕜 C) :
    Balanced 𝕜 (convexHull ℝ C) := by
  intro a ha
  let f : E →ₗ[ℝ] E := DistribSMul.toLinearMap ℝ E a
  change f '' convexHull ℝ C ⊆ convexHull ℝ C
  rw [f.image_convexHull]
  exact convexHull_mono (hC a ha)

/-- A complex balanced set is balanced under the restricted real action. -/
theorem balanced_real {C : Set E} (hC : Balanced 𝕜 C) : Balanced ℝ C := by
  intro a ha x hx
  obtain ⟨y, hy, rfl⟩ := hx
  change a • y ∈ C
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  exact hC.smul_mem (by simpa using ha) hy

/-- The span of a disk consists of positive real dilations of that disk. -/
theorem disk_span_exists_pos {C : Set E} (hC : Balanced 𝕜 C)
    (hv : Convex ℝ C) (h0 : (0 : E) ∈ C) {x : E}
    (hx : x ∈ Submodule.span 𝕜 C) : ∃ r : ℝ, 0 < r ∧ x ∈ r • C := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simpa using h0⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨r, hr, hxr⟩ := ihx
    obtain ⟨s, hs, hys⟩ := ihy
    refine ⟨r+s, add_pos hr hs, ?_⟩
    rw [hv.add_smul hr.le hs.le]
    exact Set.add_mem_add hxr hys
  | smul a x hx ih =>
    obtain ⟨r, hr, y, hy, rfl⟩ := ih
    by_cases ha : a = 0
    · exact ⟨1, one_pos, by simpa [ha] using h0⟩
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hay : a • y ∈ (‖a‖ : ℝ) • C := by
      have he : (fun z : E => (‖a‖ : ℝ) • z) = (fun z : E => (‖a‖ : 𝕜) • z) :=
        funext (RCLike.real_smul_eq_coe_smul (K := 𝕜) _)
      rw [← image_smul, he, image_smul]
      exact hC.smul_mono (by simp) ⟨y, hy, rfl⟩
    refine ⟨r * ‖a‖, mul_pos hr ha', ?_⟩
    rw [mul_smul, smul_comm a r y]
    exact smul_mem_smul_set hay

/-- The gauge on the span's pullback disk is the ambient Minkowski functional. -/
theorem gauge_preimage_span (C : Set E) (x : Submodule.span 𝕜 C) :
    gauge (Subtype.val ⁻¹' C : Set (Submodule.span 𝕜 C)) x = gauge C (x : E) := by
  simp only [gauge_def', mem_preimage, Submodule.coe_smul_of_tower]

/-- Every disk is absorbing in its algebraic span; no interior in E is required. -/
theorem disk_absorbent_span {C : Set E} (hb : Balanced 𝕜 C)
    (hv : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    Absorbent ℝ (Subtype.val ⁻¹' C : Set (Submodule.span 𝕜 C)) := by
  intro x
  obtain ⟨r, hr, hxr⟩ := disk_span_exists_pos hb hv h0 x.property
  apply Absorbs.of_norm
  refine ⟨r, fun a ha => ?_⟩
  rw [singleton_subset_iff]
  have ha0 : a ≠ 0 := by
    intro he
    simp [he] at ha
    linarith
  rw [mem_smul_set_iff_inv_smul_mem₀ ha0]
  change a⁻¹ • (x : E) ∈ C
  rw [← mem_smul_set_iff_inv_smul_mem₀ ha0]
  exact (balanced_real hb).smul_mono (by simpa [Real.norm_of_nonneg hr.le] using ha) hxr

/-- Integer dilations give the same span, with positive indices only. -/
theorem disk_span_eq_iUnion {C : Set E} (hb : Balanced 𝕜 C)
    (hv : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    (Submodule.span 𝕜 C : Set E) = ⋃ (n : ℕ) (_ : 1 ≤ n), (n : ℝ) • C := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hxr⟩ := disk_span_exists_pos hb hv h0 hx
    obtain ⟨n, hn⟩ := exists_nat_ge r
    apply mem_iUnion₂.mpr
    refine ⟨n+1, by omega, ?_⟩
    apply (balanced_real hb).smul_mono (b := ((n+1 : ℕ) : ℝ)) _ hxr
    simp only [Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg (Nat.cast_nonneg (n+1))]
    exact hn.trans (by exact_mod_cast Nat.le_succ n)
  · intro hx
    obtain ⟨n, hn, y, hy, rfl⟩ := mem_iUnion₂.mp hx
    change (n : ℝ) • y ∈ Submodule.span 𝕜 C
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

/-- A closed bounded disk has its Minkowski norm on the full span. -/
theorem compact_disk_gauge_core {C : Set E} (hc : IsCompact C)
    (hb : Balanced 𝕜 C) (hv : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    let S := Submodule.span 𝕜 C
    let : Norm S := ⟨fun x => gauge C (x : E)⟩
    ∃ _core : NormedSpace.Core 𝕜 S,
      (∀ x : S, gauge C (x : E) ≤ 1 ↔ (x : E) ∈ C) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x : S, ‖(x : E)‖ ≤ R * gauge C (x : E) := by
  let S := Submodule.span 𝕜 C
  let D : Set S := Subtype.val ⁻¹' C
  have ha : Absorbent ℝ D := disk_absorbent_span hb hv h0
  have hbD : Balanced 𝕜 D := by
    apply balanced_iff_smul_mem.mpr
    intro a ha x hx
    exact hb.smul_mem ha hx
  have hvD : Convex ℝ D := hv.linear_preimage (S.subtype.restrictScalars ℝ)
  have h0D : (0 : S) ∈ D := h0
  have hclosed : IsClosed D := hc.isClosed.preimage continuous_subtype_val
  have hbounded : Bornology.IsBounded D := by
    rw [← Bornology.isBounded_image_subtype_val]
    exact hc.isBounded.subset (image_preimage_subset _ _)
  have hsep : ∀ x : S, gauge C (x : E) = 0 ↔ x = 0 := by
    intro x
    rw [← gauge_preimage_span C x]
    exact gauge_eq_zero ha (NormedSpace.isVonNBounded_of_isBounded ℝ hbounded)
  have hunit : ∀ x : S, gauge C (x : E) ≤ 1 ↔ (x : E) ∈ C := by
    intro x
    rw [← gauge_preimage_span C x]
    constructor
    · intro hx
      have hxD := mem_closure_of_gauge_le_one hvD h0D ha hx
      rw [hclosed.closure_eq] at hxD
      exact hxD
    · intro hx
      exact gauge_le_one_of_mem (show x ∈ D from hx)
  obtain ⟨R, hR, hCR⟩ := hc.isBounded.exists_pos_norm_le
  have hbound : ∀ x : S, ‖(x : E)‖ ≤ R * gauge C (x : E) := by
    intro x
    have hg : ‖x‖ / R ≤ gauge D x :=
      le_gauge_of_subset_closedBall ha hR.le (fun y hy => by
        rw [Metric.mem_closedBall, dist_zero_right]
        change ‖(y : E)‖ ≤ R
        exact hCR y.val hy)
    rw [gauge_preimage_span] at hg
    exact (div_le_iff₀ hR).mp hg |>.trans_eq (mul_comm _ _)
  let : Norm S := ⟨fun x => gauge C (x : E)⟩
  have core : NormedSpace.Core 𝕜 S := {
    norm_nonneg := fun x => gauge_nonneg _
    norm_smul := fun a x => gauge_smul hb a (x : E)
    norm_triangle := fun x y => by
      change gauge C ((x : E) + (y : E)) ≤ gauge C (x : E) + gauge C (y : E)
      have hg := gauge_add_le hvD ha x y
      rw [gauge_preimage_span (𝕜 := 𝕜) C (x+y), gauge_preimage_span (𝕜 := 𝕜) C x,
        gauge_preimage_span (𝕜 := 𝕜) C y] at hg
      exact hg
    norm_eq_zero_iff := hsep }
  exact ⟨core, hunit, R, hR, hbound⟩

/-- A bounded injective map into a Banach space whose unit-ball image is
closed makes its domain complete. Closedness of the image of every ball
allows passing the Cauchy estimates through the ambient limit. -/
theorem completeSpace_of_closed_unitBall_image [CompleteSpace E]
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (i : G →L[ℝ] E) (hi : Function.Injective i)
    (hc : IsClosed (i '' Metric.closedBall (0 : G) 1)) : CompleteSpace G := by
  have hclosed (r : ℝ) (hr : 0 < r) :
      IsClosed (i '' Metric.closedBall (0 : G) r) := by
    have he : i '' Metric.closedBall (0 : G) r =
        r • (i '' Metric.closedBall (0 : G) 1) := by
      calc
        _ = i '' (r • Metric.closedBall (0 : G) 1) := by
          rw [smul_unitClosedBall, Real.norm_of_nonneg hr.le]
        _ = _ := by simp only [← image_smul, image_image, map_smul]
    rw [he]
    exact hc.smul₀ r
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (i.uniformContinuous.comp_cauchySeq hu)
  have htail (r : ℝ) (hr : 0 < r) :
      ∃ N : ℕ, ∀ n ≥ N, x - i (u n) ∈ i '' Metric.closedBall (0 : G) r := by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu r hr
    refine ⟨N, fun n hn => ?_⟩
    apply (hclosed r hr).mem_of_tendsto (hx.sub_const (i (u n)))
    filter_upwards [eventually_ge_atTop N] with m hm
    refine ⟨u m - u n, ?_, by simp⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] using (hN m hm n hn).le
  obtain ⟨N, hN⟩ := htail 1 one_pos
  obtain ⟨v, hv, hiv⟩ := hN N le_rfl
  let y := v + u N
  have hiy : i y = x := by
    dsimp [y]
    rw [map_add, hiv]
    abel
  refine ⟨y, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨M, hM⟩ := htail (ε / 2) (half_pos hε)
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨w, hw, hiw⟩ := hM n hn
  have hwy : w = y - u n := hi (by rw [map_sub, hiy]; exact hiw)
  rw [hwy, Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at hw
  exact (dist_comm _ _).trans_le hw |>.trans_lt (half_lt_self hε)

/-- The algebraic disk span, kept as a distinct type so that the gauge
norm cannot accidentally inherit the ambient subspace norm. -/
def DiskSpace (C : Set E) := ↥(Submodule.span 𝕜 C)

instance diskSpaceAddCommGroup (C : Set E) : AddCommGroup (DiskSpace (𝕜 := 𝕜) C) :=
  inferInstanceAs (AddCommGroup (Submodule.span 𝕜 C))

instance diskSpaceModule (C : Set E) : Module 𝕜 (DiskSpace (𝕜 := 𝕜) C) :=
  inferInstanceAs (Module 𝕜 (Submodule.span 𝕜 C))

/-- Algebraic inclusion of the entire disk span. -/
def diskSpaceInclusion (C : Set E) : DiskSpace (𝕜 := 𝕜) C →ₗ[𝕜] E :=
  (Submodule.span 𝕜 C).subtype

/-- Every compact disk, with its original Minkowski functional on its
algebraic span, is a Banach disk. -/
theorem banachDisk_of_isCompact [CompleteSpace E] {C : Set E}
    (hc : IsCompact C) (hb : Balanced 𝕜 C) (hv : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    NullSequenceDisksSpec.BanachDisk (𝕜 := 𝕜) C := by
  let G := DiskSpace (𝕜 := 𝕜) C
  let j : G →ₗ[𝕜] E := diskSpaceInclusion C
  obtain ⟨core, hunit, R, hR, hbound⟩ := compact_disk_gauge_core hc hb hv h0
  let : Norm G := ⟨fun x => gauge C (j x)⟩
  have coreG : NormedSpace.Core 𝕜 G := core
  let : NormedAddCommGroup G := NormedAddCommGroup.ofCore coreG
  let : NormedSpace 𝕜 G := NormedSpace.ofCore coreG
  let i : G →L[𝕜] E := j.mkContinuous R hbound
  have hi : Function.Injective i := Subtype.val_injective
  have hball : i '' Metric.closedBall (0 : G) 1 = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      change gauge C (j y) ≤ 1 at hy
      exact (hunit y).mp hy
    · intro hx
      let y : G := ⟨x, Submodule.subset_span hx⟩
      refine ⟨y, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hunit y).mpr hx
  let : NormedSpace ℝ G := NormedSpace.restrictScalars ℝ 𝕜 G
  let : IsScalarTower ℝ 𝕜 G := IsScalarTower.restrictScalars ℝ 𝕜 G
  let : CompleteSpace G :=
    completeSpace_of_closed_unitBall_image (𝕜 := 𝕜) (i.restrictScalars ℝ) hi (by
      change IsClosed (i '' Metric.closedBall (0 : G) 1)
      rw [hball]
      exact hc.isClosed)
  have hic : IsCompactOperator i := by
    apply (isCompactOperator_iff_isCompact_closure_image_closedBall i.toLinearMap zero_lt_one).mpr
    change IsCompact (closure (i '' Metric.closedBall (0 : G) 1))
    rw [hball, hc.isClosed.closure_eq]
    exact hc
  exact ⟨G, inferInstance, inferInstance, inferInstance, i, hi, hic, hball,
    Submodule.range_subtype _, fun _ => rfl, disk_span_eq_iUnion hb hv h0⟩

/-- Full null-sequence disk theorem, retaining real and complex scalars
and the possibly trivial disk. -/
theorem nullSequenceDisk_banach : NullSequenceDisksSpec.NullSequenceDiskTheorem := by
  intro 𝕜 _ E _ _ _ z hz
  let C := nullSequenceDisk (𝕜 := 𝕜) z
  have hc : IsCompact C := isCompact_nullSequenceDisk z hz
  have hb : Balanced 𝕜 C :=
    (balanced_real_convexHull (balancedHull.balanced (𝕜 := 𝕜) (range z))).closure
  have hv : Convex ℝ C := (convex_convexHull ℝ _).closure
  have h0 : (0 : E) ∈ C := by
    apply subset_closure
    apply subset_convexHull
    exact (balancedHull.balanced (𝕜 := 𝕜) (range z)).zero_mem
      ((range_nonempty z).mono (subset_balancedHull 𝕜))
  exact ⟨hc, banachDisk_of_isCompact hc hb hv h0⟩

end
end ExpandedFA.Compactness
