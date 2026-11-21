import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HomotopyExtension
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Topology
open P202.Cellular
universe u v

namespace P202.Topology
namespace HomotopyExtension

/-- A version of the ray parameter with no singularity at the disk centre. -/
def rayScale (n : ℕ) (p : Disk n × Interval) : ℝ :=
  2 / max (2 - (p.2 : ℝ)) (2 * ‖p.1.1‖)

lemma disk_norm_le (n : ℕ) (x : Disk n) : ‖x.1‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using x.2

lemma ray_denom_pos (n : ℕ) (p : Disk n × Interval) :
    0 < max (2 - (p.2 : ℝ)) (2 * ‖p.1.1‖) := by
  have := p.2.2.2
  exact lt_of_lt_of_le (by linarith : 0 < 2 - (p.2 : ℝ)) (le_max_left _ _)

lemma rayScale_pos (n : ℕ) (p : Disk n × Interval) : 0 < rayScale n p :=
  div_pos (by norm_num) (ray_denom_pos n p)

lemma rayScale_mul (n : ℕ) (p : Disk n × Interval) :
    rayScale n p * max (2 - (p.2 : ℝ)) (2 * ‖p.1.1‖) = 2 := by
  exact div_mul_cancel₀ _ (ne_of_gt (ray_denom_pos n p))

lemma rayScale_bounds (n : ℕ) (p : Disk n × Interval) :
    rayScale n p * ‖p.1.1‖ ≤ 1 ∧
      0 ≤ 2 - rayScale n p * (2 - (p.2 : ℝ)) ∧
      2 - rayScale n p * (2 - (p.2 : ℝ)) ≤ 1 := by
  have hp := rayScale_pos n p
  have he := rayScale_mul n p
  have hn := disk_norm_le n p.1
  have ht0 := p.2.2.1
  have ht1 := p.2.2.2
  have hleft := mul_le_mul_of_nonneg_left (le_max_left
    (2 - (p.2 : ℝ)) (2 * ‖p.1.1‖)) hp.le
  have hright := mul_le_mul_of_nonneg_left (le_max_right
    (2 - (p.2 : ℝ)) (2 * ‖p.1.1‖)) hp.le
  have hmax : max (2 - (p.2 : ℝ)) (2 * ‖p.1.1‖) ≤ 2 :=
    max_le (by linarith) (by linarith)
  have hscale : 1 ≤ rayScale n p := by
    have := mul_le_mul_of_nonneg_left hmax hp.le
    nlinarith
  constructor
  · nlinarith
  constructor
  · linarith
  · nlinarith

/-- Retraction of the disk cylinder onto its bottom and side, valid also for
`n = 0` (where the side is empty). -/
def cylinderRetract (n : ℕ) : C(Disk n × Interval, Disk n × Interval) where
  toFun p := (⟨rayScale n p • p.1.1, by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (rayScale_pos n p)] using (rayScale_bounds n p).1⟩,
    ⟨2 - rayScale n p * (2 - (p.2 : ℝ)), (rayScale_bounds n p).2⟩)
  continuous_toFun := by
    have hs : Continuous (rayScale n) := by
      unfold rayScale
      exact continuous_const.div
        ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).max
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst).norm))
        (fun p => ne_of_gt (ray_denom_pos n p))
    exact (hs.smul (continuous_subtype_val.comp continuous_fst)).subtype_mk _ |>.prodMk
      ((continuous_const.sub (hs.mul
        (continuous_const.sub (continuous_subtype_val.comp continuous_snd)))).subtype_mk _)

lemma cylinderRetract_mem (n : ℕ) (p : Disk n × Interval) :
    (cylinderRetract n p).2 = 0 ∨ ‖(cylinderRetract n p).1.1‖ = 1 := by
  rcases le_total (2 * ‖p.1.1‖) (2 - (p.2 : ℝ)) with h | h
  · left
    apply Subtype.ext
    change 2 - rayScale n p * (2 - (p.2 : ℝ)) = 0
    have := rayScale_mul n p
    rw [max_eq_left h] at this
    linarith
  · right
    change ‖rayScale n p • p.1.1‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (rayScale_pos n p)]
    have := rayScale_mul n p
    rw [max_eq_right h] at this
    nlinarith

lemma cylinderRetract_fixed (n : ℕ) (p : Disk n × Interval)
    (hp : p.2 = 0 ∨ ‖p.1.1‖ = 1) : cylinderRetract n p = p := by
  have hs : rayScale n p = 1 := by
    unfold rayScale
    rcases hp with h | h
    · have ht : (p.2 : ℝ) = 0 := congrArg Subtype.val h
      rw [ht, sub_zero, max_eq_left (by nlinarith [disk_norm_le n p.1])]
      norm_num
    · rw [h, mul_one, max_eq_right (by linarith [p.2.2.1])]
      norm_num
  apply Prod.ext
  · apply Subtype.ext
    change rayScale n p • p.1.1 = p.1.1
    rw [hs, one_smul]
  · apply Subtype.ext
    change 2 - rayScale n p * (2 - (p.2 : ℝ)) = (p.2 : ℝ)
    rw [hs]
    ring


/-- The bottom together with the boundary cylinder, with its subspace topology. -/
abbrev CylinderBoundary (n : ℕ) :=
  {p : Disk n × Interval // p.2 = 0 ∨ ‖p.1.1‖ = 1}

def cylinderFaceProjection (n : ℕ) :
    C(Disk n ⊕ (Sphere n × Interval), CylinderBoundary n) where
  toFun := Sum.elim (fun x => ⟨(x, 0), Or.inl rfl⟩)
    (fun p => ⟨(boundaryInclusion n p.1, p.2), Or.inr (by
      simpa only [boundaryInclusion, Metric.mem_sphere, dist_zero_right] using p.1.2)⟩)
  continuous_toFun := continuous_sum_dom.mpr ⟨
    (continuous_id.prodMk continuous_const).subtype_mk _,
    (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
      continuous_snd).subtype_mk _⟩

lemma cylinderFaceProjection_quotient (n : ℕ) :
    IsQuotientMap (cylinderFaceProjection n) := by
  apply IsQuotientMap.of_surjective_continuous _ (cylinderFaceProjection n).continuous
  rintro ⟨⟨x,t⟩, hp⟩
  rcases hp with ht | hx
  · change t = 0 at ht
    subst t
    exact ⟨Sum.inl x, rfl⟩
  · let z : Sphere n := ⟨x.1, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
    exact ⟨Sum.inr (z,t), rfl⟩

/-- Extending a map on the bottom and a compatible homotopy on the side.
No nonemptiness or separation hypothesis on `Y` is needed. -/
lemma diskHomotopyExtension {Y : Type v} [TopologicalSpace Y] (n : ℕ)
    (f : C(Disk n, Y)) (b : C(Sphere n × Interval, Y))
    (hb : ∀ z, b (z, 0) = f (boundaryInclusion n z)) :
    ∃ F : C(Disk n × Interval, Y),
      (∀ x, F (x, 0) = f x) ∧
      (∀ z t, F (boundaryInclusion n z, t) = b (z, t)) := by
  let g : C(Disk n ⊕ (Sphere n × Interval), Y) :=
    ⟨Sum.elim f b, continuous_sum_dom.mpr ⟨f.continuous, b.continuous⟩⟩
  have hg : Function.FactorsThrough g (cylinderFaceProjection n) := by
    intro p q hpq
    have he : (cylinderFaceProjection n p).1 = (cylinderFaceProjection n q).1 :=
      congrArg Subtype.val hpq
    cases p with
    | inl x =>
      cases q with
      | inl y =>
        have : x = y := congrArg Prod.fst he
        exact congrArg f this
      | inr z =>
        have hx : x = boundaryInclusion n z.1 := congrArg Prod.fst he
        have ht : z.2 = 0 := (congrArg Prod.snd he).symm
        change f x = b z
        rw [hx, show z = (z.1, 0) from Prod.ext rfl ht]
        exact (hb z.1).symm
    | inr z =>
      cases q with
      | inl x =>
        have hx : boundaryInclusion n z.1 = x := congrArg Prod.fst he
        have ht : z.2 = 0 := congrArg Prod.snd he
        change b z = f x
        rw [← hx, show z = (z.1, 0) from Prod.ext rfl ht]
        exact hb z.1
      | inr w =>
        have hx : z.1 = w.1 := Subtype.ext (congrArg (fun p => p.1.1) he)
        have ht : z.2 = w.2 := congrArg (fun p : Disk n × Interval => p.2) he
        exact congrArg b (Prod.ext hx ht)
  let k := (cylinderFaceProjection_quotient n).lift g hg
  have hk (p) : k (cylinderFaceProjection n p) = g p :=
    congrArg (fun m : C(_, Y) => m p)
      ((cylinderFaceProjection_quotient n).lift_comp g hg)
  let r : C(Disk n × Interval, CylinderBoundary n) :=
    ⟨fun p => ⟨cylinderRetract n p, cylinderRetract_mem n p⟩,
      (cylinderRetract n).continuous.subtype_mk _⟩
  refine ⟨k.comp r, ?_, ?_⟩
  · intro x
    have hr : r (x, 0) = cylinderFaceProjection n (Sum.inl x) :=
      Subtype.ext (cylinderRetract_fixed n (x, 0) (Or.inl rfl))
    change k (r (x, 0)) = f x
    rw [hr]
    exact hk (Sum.inl x)
  · intro z t
    have hz : ‖z.1‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2
    have hr : r (boundaryInclusion n z, t) = cylinderFaceProjection n (Sum.inr (z,t)) :=
      Subtype.ext (cylinderRetract_fixed n _ (Or.inr hz))
    change k (r (boundaryInclusion n z, t)) = b (z,t)
    rw [hr]
    exact hk (Sum.inr (z,t))


section Skeleta
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

lemma selected_of_openCell_mem (A : Subcomplex X) {n : ℕ} (c : Cell X n)
    {x : X} (hx : x ∈ openCell X n c) (ha : x ∈ A.carrier) : c ∈ A.cells n := by
  rcases mem_iUnion.mp ha with ⟨m, hm⟩
  rcases mem_iUnion.mp hm with ⟨d, hd⟩
  have he : (⟨n,c⟩ : Σ k, Cell X k) = ⟨m,d.1⟩ :=
    CWStructure.disjoint_interiors.elim_set (mem_univ _) (mem_univ _) x hx hd
  cases he
  exact d.2

lemma selected_disk_mem
    (hc : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) {n : ℕ} (c : Cell X n) (ha : c ∈ A.cells n) (x : Disk n) :
    characteristic X n c x ∈ A.carrier := by
  apply A.contains_closures n c ha
  rw [hc n c]
  exact ⟨x, rfl⟩

lemma disk_point_alternative {n : ℕ} (x : Disk n) :
    (∃ z : Sphere n, boundaryInclusion n z = x) ∨
      ∃ z : OpenDisk n, interiorInclusion n z = x := by
  rcases lt_or_eq_of_le (disk_norm_le n x) with h | h
  · right
    exact ⟨⟨x.1, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩, rfl⟩
  · left
    exact ⟨⟨x.1, by simpa only [Metric.mem_sphere, dist_zero_right] using h⟩, rfl⟩

/-- The old skeleton has no points when no cell dimensions are allowed. -/
lemma skeletonLT_zero : skeletonLT X 0 = ∅ := by
  simp [skeletonLT]

lemma skeletonLT_mono {m n : ℕ} (h : m ≤ n) : skeletonLT X m ⊆ skeletonLT X n := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨k,hk⟩
  rcases mem_iUnion.mp hk with ⟨hkm,hk⟩
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨lt_of_lt_of_le hkm h,hk⟩⟩

lemma mem_some_skeleton (x : X) : ∃ n, x ∈ skeletonLT X n := by
  have hx : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
    rw [CWStructure.cover]
    exact mem_univ x
  rcases mem_iUnion.mp hx with ⟨n,hn⟩
  exact ⟨n+1,mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨Nat.lt_succ_self n,hn⟩⟩⟩

variable {Y : Type v} [TopologicalSpace Y]
variable (A : Subcomplex X) (f : C(X,Y)) (h : C(A × Interval,Y))

/-- The inductive data retains agreement with the prescribed homotopy at
all points of `A` already in the skeleton, including attaching-map images. -/
structure Stage (n : ℕ) where
  map : C(skeletonLT X n, C(Interval,Y))
  start : ∀ x, map x 0 = f x.1
  agree : ∀ (x : skeletonLT X n) (ha : x.1 ∈ A.carrier) t,
    map x t = h (⟨x.1,ha⟩,t)

def initialStage : Stage A f h 0 where
  map := ⟨fun x => False.elim (by simpa only [skeletonLT_zero, mem_empty_iff_false] using x.2),
    by
      rw [continuous_iff_continuousAt]
      intro x
      exact False.elim (by simpa only [skeletonLT_zero, mem_empty_iff_false] using x.2)⟩
  start x := False.elim (by simpa only [skeletonLT_zero, mem_empty_iff_false] using x.2)
  agree x := False.elim (by simpa only [skeletonLT_zero, mem_empty_iff_false] using x.2)


lemma cellStageExtension
    (hc : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (hh : ∀ a : A, h (a,0) = f a.1) {n : ℕ} (s : Stage A f h n) (c : Cell X n) :
    ∃ g : C(Disk n, C(Interval,Y)),
      (∀ x, g x 0 = f (characteristic X n c x)) ∧
      (∀ z, g (boundaryInclusion n z) = s.map (attachingMap n c z)) ∧
      (∀ (x : Disk n) (ha : characteristic X n c x ∈ A.carrier) t,
        g x t = h (⟨characteristic X n c x,ha⟩,t)) := by
  classical
  by_cases hsel : c ∈ A.cells n
  · let a : C(Disk n, A) :=
      ⟨fun x => ⟨characteristic X n c x, selected_disk_mem hc A c hsel x⟩,
        (characteristic X n c).continuous.subtype_mk _⟩
    refine ⟨h.curry.comp a, ?_, ?_, ?_⟩
    · intro x
      exact hh (a x)
    · intro z
      ext t
      exact (s.agree (attachingMap n c z) (a (boundaryInclusion n z)).2 t).symm
    · intro x ha t
      rfl
  · let b : C(Sphere n × Interval, Y) := (s.map.comp (attachingMap n c)).uncurry
    obtain ⟨F, hF0, hFb⟩ := diskHomotopyExtension n (f.comp (characteristic X n c)) b
      (fun z => s.start (attachingMap n c z))
    refine ⟨F.curry, hF0, ?_, ?_⟩
    · intro z
      ext t
      exact hFb z t
    · intro x ha t
      rcases disk_point_alternative x with ⟨z,rfl⟩ | ⟨z,rfl⟩
      · exact (hFb z t).trans (s.agree (attachingMap n c z) ha t)
      · exact False.elim (hsel (selected_of_openCell_mem A c ⟨z,rfl⟩ ha))

lemma nextStage_exists
    (hc : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (hp : P202Specs.Topology.CellStructures.attachmentPushout.{u,v})
    (hh : ∀ a : A, h (a,0) = f a.1) {n : ℕ} (s : Stage A f h n) :
    ∃ s' : Stage A f h (n+1),
      ∀ x, s'.map (oldSkeletonInclusion X n x) = s.map x := by
  classical
  choose g hg0 hgb hga using cellStageExtension A f h hc hh s
  obtain ⟨k, hk, _⟩ := hp n s.map g (fun c z => hgb c z)
  have hk0 : ∀ x, k x 0 = f x.1 := by
    intro x
    obtain ⟨p,rfl⟩ := (CWStructure.attachment_quotient n).surjective x
    cases p with
    | inl x =>
      change k (oldSkeletonInclusion X n x) 0 = f x.1
      rw [hk.1 x]
      exact s.start x
    | inr p =>
      rcases p with ⟨c,z⟩
      change k (diskToSkeleton X CWStructure.boundary_lands n c z) 0 =
        f (characteristic X n c z)
      rw [hk.2 c z]
      exact hg0 c z
  have hka : ∀ (x : skeletonLT X (n+1)) (ha : x.1 ∈ A.carrier) t,
      k x t = h (⟨x.1,ha⟩,t) := by
    intro x
    obtain ⟨p,rfl⟩ := (CWStructure.attachment_quotient n).surjective x
    cases p with
    | inl x =>
      intro ha t
      change k (oldSkeletonInclusion X n x) t = h (⟨x.1,ha⟩,t)
      rw [hk.1 x]
      exact s.agree x ha t
    | inr p =>
      rcases p with ⟨c,z⟩
      intro ha t
      change k (diskToSkeleton X CWStructure.boundary_lands n c z) t =
        h (⟨characteristic X n c z,ha⟩,t)
      rw [hk.2 c z]
      exact hga c z ha t
  exact ⟨⟨k,hk0,hka⟩,hk.1⟩


/-- Compatible extensions over all finite skeleta give a map on the whole
space. Continuity is tested on disks, so no bound on dimension is used. -/
lemma extendOverAllSkeleta
    (hc : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (hp : P202Specs.Topology.CellStructures.attachmentPushout.{u,v})
    (ht : P202Specs.Topology.CellStructures.continuityTest.{u,v})
    (hh : ∀ a : A, h (a,0) = f a.1) :
    ∃ H : C(X × Interval,Y), (∀ x, H (x,0) = f x) ∧
      (∀ (a : A) t, H (a.1,t) = h (a,t)) := by
  classical
  let next (n : ℕ) (s : Stage A f h n) : Stage A f h (n+1) :=
    Classical.choose (nextStage_exists A f h hc hp hh s)
  let S : (n : ℕ) → Stage A f h n :=
    Nat.rec (initialStage A f h) (fun n s => next n s)
  have step (n : ℕ) (x : skeletonLT X n) :
      (S (n+1)).map (oldSkeletonInclusion X n x) = (S n).map x :=
    Classical.choose_spec (nextStage_exists A f h hc hp hh (S n)) x
  have compat (m n : ℕ) (hmn : m ≤ n) (x : skeletonLT X m) :
      (S n).map ⟨x.1, skeletonLT_mono hmn x.2⟩ = (S m).map x := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      exact (step n ⟨x.1,skeletonLT_mono hmn x.2⟩).trans ih
  let level (x : X) : ℕ := Classical.choose (mem_some_skeleton x)
  have level_mem (x : X) : x ∈ skeletonLT X (level x) :=
    Classical.choose_spec (mem_some_skeleton x)
  let F (x : X) : C(Interval,Y) := (S (level x)).map ⟨x,level_mem x⟩
  have F_eq (n : ℕ) (x : skeletonLT X n) : F x.1 = (S n).map x := by
    exact (compat (level x.1) (max (level x.1) n) (le_max_left _ _)
      ⟨x.1,level_mem x.1⟩).symm.trans
      (compat n (max (level x.1) n) (le_max_right _ _) x)
  have hF : Continuous F := by
    apply (ht F).mpr
    intro n c
    have hd : Continuous (diskToSkeleton X CWStructure.boundary_lands n c) :=
      (characteristic X n c).continuous.subtype_mk _
    exact ((S (n+1)).map.continuous.comp hd).congr
      (fun x => (F_eq (n+1) (diskToSkeleton X CWStructure.boundary_lands n c x)).symm)
  let H : C(X × Interval,Y) := (⟨F,hF⟩ : C(X,C(Interval,Y))).uncurry
  refine ⟨H, ?_, ?_⟩
  · intro x
    exact (S (level x)).start ⟨x,level_mem x⟩
  · intro a t
    exact (S (level a.1)).agree ⟨a.1,level_mem a.1⟩ a.2 t

end Skeleta

end HomotopyExtension
/-- Homotopy extension in the time-first convention, obtained from the
skeletal construction for arbitrary source and target universes. -/
theorem HomotopyExtension.extendHomotopy
    : P202Specs.Topology.HomotopyExtension.cwHomotopyExtension.{u,v} := by
  intro X Y _ _ _ A f g h
  let h' : C(A × Interval, Y) :=
    ⟨fun p => h (p.2, p.1), h.continuous.comp continuous_swap⟩
  obtain ⟨K, hK0, hKA⟩ := HomotopyExtension.extendOverAllSkeleta A f h'
    closureOpenCell attachmentPushout continuityTest (fun a => h.apply_zero a)
  let F : C(X, Y) := ⟨fun x => K (x, 1),
    K.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let H : ContinuousMap.Homotopy f F :=
    { toFun := fun p => K (p.2, p.1)
      continuous_toFun := K.continuous.comp continuous_swap
      map_zero_left := hK0
      map_one_left := fun _ => rfl }
  exact ⟨F, H, fun t a => hKA a t⟩

/-- Homotopy extension for every CW pair and arbitrary topological target. -/
theorem cwHomotopyExtension :
    P202Specs.Topology.HomotopyExtension.cwHomotopyExtension.{u,v} :=
  HomotopyExtension.extendHomotopy.{u,v}

/-- The equal-universe instance of the full homotopy extension theorem. -/
theorem cwHomotopyExtensionSelf :
    P202Specs.Topology.HomotopyExtension.cwHomotopyExtensionSelf.{u} :=
  cwHomotopyExtension.{u,u}

end P202.Topology
