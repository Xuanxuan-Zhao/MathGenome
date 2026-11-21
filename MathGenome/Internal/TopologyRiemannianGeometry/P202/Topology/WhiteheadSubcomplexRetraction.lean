import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.WhiteheadSubcomplexRetraction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.WhiteheadDiskReplacement
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The inclusion case of Whitehead's theorem.
The supplied cell-structure and disk-replacement implementations are reused.
Compatible homotopies are built directly on the skeleta, and their union is
continuous on every characteristic disk times the full closed interval.
-/

noncomputable section
open Set Topology
open scoped unitInterval
universe u v

namespace P202.Topology
open P202.Cellular

variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- The characteristic disks form a quotient presentation, directly from
coverage and the closed-set weak-topology axiom. -/
theorem characteristicDiskQuotient : IsQuotientMap (diskProjection X) := by
  apply isQuotientMap_iff_isClosed.mpr
  constructor
  · intro x
    have hx : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
      rw [CWStructure.cover]
      trivial
    rcases mem_iUnion.mp hx with ⟨n, hn⟩
    rcases mem_iUnion.mp hn with ⟨c, z, rfl⟩
    exact ⟨⟨n, c, interiorInclusion n z⟩, rfl⟩
  · intro S
    rw [CWStructure.weak_topology]
    constructor
    · intro h
      exact isClosed_sigma_iff.mpr fun n =>
        isClosed_sigma_iff.mpr fun c => h n c
    · intro h n c
      exact (isClosed_sigma_iff.mp (isClosed_sigma_iff.mp h n)) c

/-- Currying in the compact interval proves the characteristic-disk test
for the ordinary product topology, without a finiteness condition on X. -/
theorem continuous_on_characteristic_products {Z : Type v} [TopologicalSpace Z]
    (H : X × Interval → Z)
    (h : ∀ n (c : Cell X n), Continuous (H ∘ Prod.map (characteristic X n c) id)) :
    Continuous H := by
  apply (characteristicDiskQuotient (X := X)).continuous_lift_prod_left
  apply ContinuousMap.continuous_uncurry_of_continuous
    (⟨fun p => (⟨fun t => H (diskProjection X p, t), by
      rcases p with ⟨n, c, z⟩
      exact (h n c).comp (continuous_const.prodMk continuous_id)⟩ : C(Interval, Z)), by
      apply continuous_sigma
      intro n
      apply continuous_sigma
      intro c
      exact (ContinuousMap.curry ⟨_, h n c⟩).continuous⟩ : C(DiskSum X, C(Interval, Z)))

/-- Whole characteristic disks lie in the next skeleton, including n = 0. -/
theorem characteristic_mem_skeletonLT (n : ℕ) (c : Cell X n) (z : Disk n) :
    characteristic X n c z ∈ skeletonLT X (n + 1) :=
  (diskToSkeleton X CWStructure.boundary_lands n c z).property

/-- A compatible family of homotopies which is unchanged on old skeleta
has a continuous union on X × I. This includes the terminal time: on each
whole characteristic cylinder the union equals one finite-stage map. -/
theorem exists_stabilized_skeletal_homotopy (A : Subcomplex X)
    (F : ℕ → C(X × Interval, X))
    (hzero : ∀ n x, F n (x, 0) = x)
    (hfix : ∀ n (a : A) t, F n (a.val, t) = a.val)
    (hstable : ∀ n m, n ≤ m → ∀ x ∈ skeletonLT X n, ∀ t,
      F m (x, t) = F n (x, t))
    (hend : ∀ n x, x ∈ skeletonLT X n → F n (x, 1) ∈ A.carrier) :
    ∃ (r : C(X, A)) (H : C(X × Interval, X)),
      (∀ a : A, r a.val = a) ∧
      (∀ x, H (x, 0) = x) ∧
      (∀ x, H (x, 1) = (r x).val) ∧
      (∀ (a : A) t, H (a.val, t) = a.val) := by
  classical
  have covered (x : X) : ∃ n, x ∈ skeletonLT X n := by
    obtain ⟨⟨n, c, z⟩, rfl⟩ := (characteristicDiskQuotient (X := X)).surjective x
    exact ⟨n + 1, characteristic_mem_skeletonLT n c z⟩
  let rank : X → ℕ := fun x => Nat.find (covered x)
  have hrank (x : X) : x ∈ skeletonLT X (rank x) := Nat.find_spec (covered x)
  let Hfun : X × Interval → X := fun p => F (rank p.1) p
  have heq (n : ℕ) (x : X) (hx : x ∈ skeletonLT X n) (t : Interval) :
      Hfun (x, t) = F n (x, t) := by
    change F (rank x) (x, t) = F n (x, t)
    rcases le_total (rank x) n with h | h
    · exact (hstable (rank x) n h x (hrank x) t).symm
    · exact hstable n (rank x) h x hx t
  have hc : Continuous Hfun := by
    apply continuous_on_characteristic_products
    intro n c
    have he : Hfun ∘ Prod.map (characteristic X n c) id =
        (F (n + 1)) ∘ Prod.map (characteristic X n c) id := by
      funext p
      exact heq (n + 1) _ (characteristic_mem_skeletonLT n c p.1) p.2
    rw [he]
    exact (F (n + 1)).continuous.comp ((characteristic X n c).continuous.prodMap continuous_id)
  let H : C(X × Interval, X) := ⟨Hfun, hc⟩
  have hmem (x : X) : H (x, 1) ∈ A.carrier := hend (rank x) x (hrank x)
  let r : C(X, A) := ⟨fun x => ⟨H (x, 1), hmem x⟩,
    (H.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩
  refine ⟨r, H, ?_, ?_, fun _ => rfl, ?_⟩
  · intro a
    apply Subtype.ext
    exact hfix (rank a.val) a 1
  · intro x
    exact hzero (rank x) x
  · intro a t
    exact hfix (rank a.val) a t

/-- Membership in the carrier determines selection of an open cell. -/
theorem selected_of_mem_openCell (A : Subcomplex X) {n : ℕ} {c : Cell X n}
    {x : X} (hx : x ∈ openCell X n c) (ha : x ∈ A.carrier) : c ∈ A.cells n := by
  rcases mem_iUnion.mp ha with ⟨m, hm⟩
  rcases mem_iUnion.mp hm with ⟨d, hd⟩
  have he : (⟨n, c⟩ : Σ k, Cell X k) = ⟨m, d.val⟩ :=
    CWStructure.disjoint_interiors.elim_set (mem_univ _) (mem_univ _) x hx hd
  have : (⟨m, d.val⟩ : Σ k, Cell X k).2 ∈ A.cells (⟨m, d.val⟩ : Σ k, Cell X k).1 := d.property
  rw [← he] at this
  exact this

/-- Every point of a selected characteristic disk belongs to the subcomplex. -/
theorem selected_characteristic_mem
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) {n : ℕ} {c : Cell X n} (hc : c ∈ A.cells n) (z : Disk n) :
    characteristic X n c z ∈ A.carrier := by
  apply A.contains_closures n c hc
  rw [hclosure n c]
  exact ⟨z, rfl⟩

/-- Closedness of subcomplexes derived from the frozen CW axioms. It is
needed to paste the homotopy on A and on a finite-dimensional skeleton. -/
theorem subcomplex_isClosed
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) : IsClosed A.carrier := by
  have level : ∀ n : ℕ, IsClosed ((Subtype.val : skeletonLT X n → X) ⁻¹' A.carrier) := by
    intro n
    induction n with
    | zero =>
      have hempty : (Subtype.val : skeletonLT X 0 → X) ⁻¹' A.carrier = ∅ := by
        ext x
        have hx := x.property
        simp [skeletonLT] at hx
      rw [hempty]
      exact isClosed_empty
    | succ n ih =>
      apply (CWStructure.attachment_quotient n).isClosed_preimage.mp
      apply isClosed_sum_iff.mpr
      constructor
      · exact ih
      · apply isClosed_sigma_iff.mpr
        intro c
        change IsClosed ((characteristic X n c) ⁻¹' A.carrier)
        by_cases hc : c ∈ A.cells n
        · have he : (characteristic X n c) ⁻¹' A.carrier = univ := by
            ext z
            simp only [mem_preimage, mem_univ, iff_true]
            exact selected_characteristic_mem hclosure A hc z
          rw [he]
          exact isClosed_univ
        · have hside : IsClosed ((attachingMap n c) ⁻¹'
              ((Subtype.val : skeletonLT X n → X) ⁻¹' A.carrier)) :=
            ih.preimage (attachingMap n c).continuous
          have hmap : IsClosedMap (boundaryInclusion n) :=
            Metric.isClosed_sphere.isClosedMap_inclusion Metric.sphere_subset_closedBall
          have he : (characteristic X n c) ⁻¹' A.carrier =
              boundaryInclusion n '' ((attachingMap n c) ⁻¹'
                ((Subtype.val : skeletonLT X n → X) ⁻¹' A.carrier)) := by
            ext z
            constructor
            · intro hz
              have hle : ‖z.val‖ ≤ 1 := by
                simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
              have heq : ‖z.val‖ = 1 := by
                by_contra hn
                have hlt : ‖z.val‖ < 1 := lt_of_le_of_ne hle hn
                have hcell : characteristic X n c z ∈ openCell X n c := by
                  refine ⟨⟨z.val, ?_⟩, rfl⟩
                  simpa only [Metric.mem_ball, dist_zero_right] using hlt
                exact hc (selected_of_mem_openCell A hcell hz)
              refine ⟨⟨z.val, ?_⟩, hz, ?_⟩
              · simpa only [Metric.mem_sphere, dist_zero_right] using heq
              · rfl
            · rintro ⟨z, hz, rfl⟩
              exact hz
          rw [he]
          exact hmap _ hside
  apply (CWStructure.weak_topology A.carrier).mpr
  intro n c
  have hc : Continuous (diskToSkeleton X CWStructure.boundary_lands n c) :=
    (characteristic X n c).continuous.subtype_mk _
  exact (level (n + 1)).preimage hc

/-- The union of a subcomplex and the cells below n is again a subcomplex. -/
def skeletalUnion
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) (n : ℕ) : Subcomplex X where
  cells m := A.cells m ∪ { _c | m < n }
  contains_closures m c hc := by
    rcases hc with hc | hc
    · intro x hx
      have ha := A.contains_closures m c hc hx
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hk with ⟨d, hd⟩
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨d.val, Or.inl d.property⟩, hd⟩⟩
    · intro x hx
      rw [hclosure m c] at hx
      rcases hx with ⟨z, rfl⟩
      have hs := skeletonLT_mono (X := X) (Nat.succ_le_of_lt hc)
        (characteristic_mem_skeletonLT m c z)
      rcases mem_iUnion.mp hs with ⟨k, hk⟩
      rcases mem_iUnion.mp hk with ⟨hkn, hk⟩
      rcases mem_iUnion.mp hk with ⟨d, hd⟩
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨d, Or.inr hkn⟩, hd⟩⟩

theorem skeletalUnion_carrier
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) (n : ℕ) :
    (skeletalUnion hclosure A n).carrier = A.carrier ∪ skeletonLT X n := by
  ext x
  constructor
  · rintro hx
    rcases mem_iUnion.mp hx with ⟨m, hm⟩
    rcases mem_iUnion.mp hm with ⟨c, hc⟩
    rcases c.property with h | h
    · exact Or.inl (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨c.val, h⟩, hc⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨h, mem_iUnion.mpr ⟨c.val, hc⟩⟩⟩)
  · rintro (ha | hs)
    · rcases mem_iUnion.mp ha with ⟨m, hm⟩
      rcases mem_iUnion.mp hm with ⟨c, hc⟩
      exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨c.val, Or.inl c.property⟩, hc⟩⟩
    · rcases mem_iUnion.mp hs with ⟨m, hm⟩
      rcases mem_iUnion.mp hm with ⟨hmn, hm⟩
      rcases mem_iUnion.mp hm with ⟨c, hc⟩
      exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨c, Or.inr hmn⟩, hc⟩⟩

/-- The two upstream Euclidean disk models have identical points and
induced topologies; only the predicates used to present them differ. -/
def cellularDiskHomeomorph (n : ℕ) : Disk n ≃ₜ P202Specs.Topology.ClosedDisk n where
  toFun z := ⟨z.val, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  invFun z := ⟨z.val, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- Apply disk replacement to an actual characteristic disk, keeping its
entire boundary fixed. This includes the empty zero-dimensional boundary. -/
theorem characteristic_disk_compression
    (hdisk : P202Specs.Topology.ExpectedDiskReplacement.diskReplacement.{u})
    (A : Subcomplex X) (hweak : P202Specs.Topology.IsWeakHomotopyEquivalenceInclusion A.carrier)
    (n : ℕ) (f : C(Disk n, X))
    (hb : ∀ z : Sphere n, f (boundaryInclusion n z) ∈ A.carrier) :
    ∃ (g : C(Disk n, A)) (K : C(Disk n × Interval, X)),
      (∀ z, K (z, 0) = f z) ∧
      (∀ z, K (z, 1) = (g z).val) ∧
      (∀ (z : Sphere n) t, K (boundaryInclusion n z, t) = f (boundaryInclusion n z)) := by
  let e := cellularDiskHomeomorph n
  let f' : P202Specs.Topology.RelativeDiskMap n A.carrier :=
    ⟨f.comp ⟨e.symm, e.symm.continuous⟩, by
      intro z hz
      exact hb ⟨z.val, by
        simpa only [Metric.mem_sphere, dist_zero_right] using (show ‖z.val‖ = 1 from hz)⟩⟩
  obtain ⟨g, ⟨K⟩⟩ := hdisk X A.carrier hweak n f'
  refine ⟨g.comp ⟨e, e.continuous⟩, ⟨fun p => K (p.2, e p.1),
    K.continuous.comp (continuous_snd.prodMk (e.continuous.comp continuous_fst))⟩,
    ?_, ?_, ?_⟩
  · intro z
    exact K.apply_zero (e z)
  · intro z
    exact K.apply_one (e z)
  · intro z t
    apply K.eq_fst
    change ‖z.val‖ = 1
    simpa only [Metric.mem_sphere, dist_zero_right] using z.property

/-- Pasting maps defined on two closed subspaces, retaining their values
on both pieces. -/
theorem exists_closed_pasting {D : Type*} {Z : Type*}
    [TopologicalSpace D] [TopologicalSpace Z] (S T : Set D)
    (hS : IsClosed S) (hT : IsClosed T) (f : C(S, Z)) (g : C(T, Z))
    (hag : ∀ x (hs : x ∈ S) (ht : x ∈ T), f ⟨x, hs⟩ = g ⟨x, ht⟩) :
    ∃ F : C(↥(S ∪ T), Z),
      (∀ x (hs : x ∈ S), F ⟨x, Or.inl hs⟩ = f ⟨x, hs⟩) ∧
      (∀ x (ht : x ∈ T), F ⟨x, Or.inr ht⟩ = g ⟨x, ht⟩) := by
  classical
  let F : ↥(S ∪ T) → Z := fun x => if h : x.val ∈ S then f ⟨x.val, h⟩
    else g ⟨x.val, x.property.resolve_left h⟩
  have hf : ∀ x (hs : x ∈ S), F ⟨x, Or.inl hs⟩ = f ⟨x, hs⟩ := by
    intro x hs
    simp [F, hs]
  have hg : ∀ x (ht : x ∈ T), F ⟨x, Or.inr ht⟩ = g ⟨x, ht⟩ := by
    intro x ht
    dsimp [F]
    split_ifs with hs
    · exact hag x hs ht
    · rfl
  let S' : Set ↥(S ∪ T) := Subtype.val ⁻¹' S
  let T' : Set ↥(S ∪ T) := Subtype.val ⁻¹' T
  have hcS : ContinuousOn F S' := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : S'.domRestrict F = fun x : S' => f ⟨x.val.val, x.property⟩ := by
      funext x
      exact hf x.val.val x.property
    rw [he]
    exact f.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  have hcT : ContinuousOn F T' := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : T'.domRestrict F = fun x : T' => g ⟨x.val.val, x.property⟩ := by
      funext x
      exact hg x.val.val x.property
    rw [he]
    exact g.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  have hcover : S' ∪ T' = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    exact x.property
  have hc := hcS.union_of_isClosed hcT
    (hS.preimage continuous_subtype_val) (hT.preimage continuous_subtype_val)
  rw [hcover, continuousOn_univ] at hc
  exact ⟨⟨F, hc⟩, hf, hg⟩

/-- Ray parameter for the retraction of a disk cylinder onto its bottom
and side. The max in the denominator avoids division by the radius at 0. -/
def diskCylinderScale (n : ℕ) (p : Disk n × Interval) : ℝ :=
  2 / max (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖)

theorem diskCylinderScale_properties (n : ℕ) (p : Disk n × Interval) :
    1 ≤ diskCylinderScale n p ∧ 0 ≤ diskCylinderScale n p ∧
    diskCylinderScale n p * ‖p.1.val‖ ≤ 1 ∧
    0 ≤ 2 - diskCylinderScale n p * (2 - (p.2 : ℝ)) ∧
    2 - diskCylinderScale n p * (2 - (p.2 : ℝ)) ≤ 1 ∧
    (2 - diskCylinderScale n p * (2 - (p.2 : ℝ)) = 0 ∨
      diskCylinderScale n p * ‖p.1.val‖ = 1) := by
  have ht0 := p.2.property.1
  have ht1 := p.2.property.2
  have hr : ‖p.1.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using p.1.property
  have hd1 : 1 ≤ max (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖) :=
    le_trans (by linarith) (le_max_left _ _)
  have hd2 : max (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖) ≤ 2 :=
    max_le (by linarith) (by linarith)
  have hdpos : 0 < max (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖) := by linarith
  have ha : 1 ≤ diskCylinderScale n p := by
    dsimp [diskCylinderScale]
    exact (le_div_iff₀ hdpos).mpr (by simpa using hd2)
  have ha0 : 0 ≤ diskCylinderScale n p := by linarith
  have he : diskCylinderScale n p * max (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖) = 2 :=
    div_mul_cancel₀ _ (ne_of_gt hdpos)
  have hb := le_max_left (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖)
  have hc := le_max_right (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖)
  refine ⟨ha, ha0, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hc ha0]
  · nlinarith [mul_le_mul_of_nonneg_left hb ha0]
  · nlinarith [mul_le_mul_of_nonneg_right ha (show 0 ≤ 2 - (p.2 : ℝ) by linarith)]
  · rcases le_total (2 * ‖p.1.val‖) (2 - (p.2 : ℝ)) with h | h
    · rw [max_eq_left h] at he
      exact Or.inl (by linarith)
    · rw [max_eq_right h] at he
      exact Or.inr (by linarith)

def diskCylinderRay (n : ℕ) : C(Disk n × Interval, Disk n × Interval) where
  toFun p :=
    (⟨diskCylinderScale n p • p.1.val, by
      have hp := diskCylinderScale_properties n p
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hp.2.1] using hp.2.2.1⟩,
    ⟨2 - diskCylinderScale n p * (2 - (p.2 : ℝ)),
      (diskCylinderScale_properties n p).2.2.2.1,
      (diskCylinderScale_properties n p).2.2.2.2.1⟩)
  continuous_toFun := by
    have hc : Continuous (diskCylinderScale n) := by
      apply Continuous.div continuous_const
      · exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd)).max
          (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).norm))
      · intro p
        have h := p.2.property.2
        have : 1 ≤ max (2 - (p.2 : ℝ)) (2 * ‖p.1.val‖) :=
          le_trans (by linarith) (le_max_left _ _)
        linarith
    exact (hc.smul (continuous_subtype_val.comp continuous_fst)).subtype_mk _ |>.prodMk
      ((continuous_const.sub (hc.mul (continuous_const.sub
        (continuous_subtype_val.comp continuous_snd)))).subtype_mk _)

def diskCylinderBottom (n : ℕ) : Set (Disk n × Interval) := {p | p.2 = 0}
def diskCylinderSide (n : ℕ) : Set (Disk n × Interval) := {p | ‖p.1.val‖ = 1}

theorem diskCylinderRay_mem (n : ℕ) (p : Disk n × Interval) :
    diskCylinderRay n p ∈ diskCylinderBottom n ∪ diskCylinderSide n := by
  rcases (diskCylinderScale_properties n p).2.2.2.2.2 with h | h
  · left
    exact Subtype.ext h
  · right
    change ‖diskCylinderScale n p • p.1.val‖ = 1
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (diskCylinderScale_properties n p).2.1]
    exact h

theorem diskCylinderRay_fixed (n : ℕ) (p : Disk n × Interval)
    (hp : p ∈ diskCylinderBottom n ∪ diskCylinderSide n) : diskCylinderRay n p = p := by
  have hscale : diskCylinderScale n p = 1 := by
    rcases hp with hp | hp
    · have ht : (p.2 : ℝ) = 0 := congrArg Subtype.val hp
      have hr : ‖p.1.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using p.1.property
      dsimp [diskCylinderScale]
      rw [ht, sub_zero, max_eq_left (by linarith)]
      norm_num
    · have ht := p.2.property.1
      change ‖p.1.val‖ = 1 at hp
      dsimp [diskCylinderScale]
      rw [hp, max_eq_right (by linarith)]
      norm_num
  apply Prod.ext
  · apply Subtype.ext
    change diskCylinderScale n p • p.1.val = p.1.val
    rw [hscale, one_smul]
  · apply Subtype.ext
    change 2 - diskCylinderScale n p * (2 - (p.2 : ℝ)) = (p.2 : ℝ)
    rw [hscale]
    ring

/-- Elementary homotopy extension for a disk and its boundary, proved by
the source's ray retraction. No CW structure on the disk is assumed. -/
theorem diskCylinderExtension {Z : Type*} [TopologicalSpace Z]
    (n : ℕ) (f : C(Disk n, Z)) (h : C(Sphere n × Interval, Z))
    (hzero : ∀ z, h (z, 0) = f (boundaryInclusion n z)) :
    ∃ H : C(Disk n × Interval, Z),
      (∀ z, H (z, 0) = f z) ∧
      (∀ z t, H (boundaryInclusion n z, t) = h (z, t)) := by
  have hbottom : IsClosed (diskCylinderBottom n) := isClosed_eq continuous_snd continuous_const
  have hside : IsClosed (diskCylinderSide n) :=
    isClosed_eq (continuous_subtype_val.comp continuous_fst).norm continuous_const
  let fbottom : C(diskCylinderBottom n, Z) :=
    ⟨fun p => f p.val.1, f.continuous.comp (continuous_fst.comp continuous_subtype_val)⟩
  let fside : C(diskCylinderSide n, Z) :=
    ⟨fun p => h (⟨p.val.1.val, by
        simpa only [Metric.mem_sphere, dist_zero_right] using (show ‖p.val.1.val‖ = 1 from p.property)⟩, p.val.2),
      h.continuous.comp (((continuous_subtype_val.comp (continuous_fst.comp
        continuous_subtype_val)).subtype_mk (fun p => by
          simpa only [Function.comp_apply, Metric.mem_sphere, dist_zero_right]
            using (show ‖p.val.1.val‖ = 1 from p.property))).prodMk
        (continuous_snd.comp continuous_subtype_val))⟩
  obtain ⟨w, hw0, hws⟩ := exists_closed_pasting (diskCylinderBottom n) (diskCylinderSide n)
    hbottom hside fbottom fside (by
      intro p hp0 hps
      change f p.1 = h (_, p.2)
      change p.2 = 0 at hp0
      rw [hp0, hzero]
      rfl)
  let r : C(Disk n × Interval, ↥(diskCylinderBottom n ∪ diskCylinderSide n)) :=
    ⟨fun p => ⟨diskCylinderRay n p, diskCylinderRay_mem n p⟩,
      (diskCylinderRay n).continuous.subtype_mk _⟩
  refine ⟨w.comp r, ?_, ?_⟩
  · intro z
    change w ⟨diskCylinderRay n (z, 0), _⟩ = f z
    have he := diskCylinderRay_fixed n (z, 0) (Or.inl rfl)
    simpa [he, fbottom] using hw0 (z, 0) rfl
  · intro z t
    have hz : (boundaryInclusion n z, t) ∈ diskCylinderSide n := by
      change ‖z.val‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property
    change w ⟨diskCylinderRay n (boundaryInclusion n z, t), _⟩ = h (z, t)
    have he := diskCylinderRay_fixed n (boundaryInclusion n z, t) (Or.inr hz)
    calc
      w ⟨diskCylinderRay n (boundaryInclusion n z, t), _⟩ =
          w ⟨(boundaryInclusion n z, t), Or.inr hz⟩ := congrArg w (Subtype.ext he)
      _ = h (z, t) := hws (boundaryInclusion n z, t) hz

theorem openCell_not_mem_lower_skeleton (n : ℕ) (c : Cell X n)
    {x : X} (hx : x ∈ openCell X n c) : x ∉ skeletonLT X n := by
  intro hs
  rcases mem_iUnion.mp hs with ⟨m, hm⟩
  rcases mem_iUnion.mp hm with ⟨hmn, hm⟩
  rcases mem_iUnion.mp hm with ⟨d, hd⟩
  have he : (⟨n, c⟩ : Σ k, Cell X k) = ⟨m, d⟩ :=
    CWStructure.disjoint_interiors.elim_set (mem_univ _) (mem_univ _) x hx hd
  have hn := congrArg Sigma.fst he
  change n = m at hn
  omega

/-- Descent across one actual skeletal attachment, at arbitrary target
universe. Boundary identifications may be noninjective. -/
theorem exists_attachment_pasting {Z : Type v} [TopologicalSpace Z]
    (n : ℕ) (f : C(skeletonLT X n, Z)) (g : ∀ _c : Cell X n, C(Disk n, Z))
    (hag : ∀ c z, g c (boundaryInclusion n z) = f (attachingMap n c z)) :
    ∃ h : C(skeletonLT X (n + 1), Z),
      (∀ x, h (oldSkeletonInclusion X n x) = f x) ∧
      (∀ c z, h (diskToSkeleton X CWStructure.boundary_lands n c z) = g c z) := by
  let q := attachmentProjection X CWStructure.boundary_lands n
  let w : (skeletonLT X n ⊕ (Σ _c : Cell X n, Disk n)) → Z :=
    Sum.elim f (fun p => g p.1 p.2)
  have hc : Continuous w := continuous_sumElim.mpr
    ⟨f.continuous, continuous_sigma fun c => (g c).continuous⟩
  have hold (p) (x : skeletonLT X n) (he : q p = oldSkeletonInclusion X n x) :
      w p = f x := by
    cases p with
    | inl y =>
      have hy : y = x := Subtype.ext (congrArg (fun a : skeletonLT X (n + 1) => a.val) he)
      cases hy
      rfl
    | inr p =>
      rcases p with ⟨c, z⟩
      have hle : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      have hz : ‖z.val‖ = 1 := by
        by_contra hz
        have hi : characteristic X n c z ∈ openCell X n c := by
          refine ⟨⟨z.val, ?_⟩, rfl⟩
          simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hle hz
        apply openCell_not_mem_lower_skeleton n c hi
        have he' := congrArg Subtype.val he
        change characteristic X n c z = x.val at he'
        rw [he']
        exact x.property
      let b : Sphere n := ⟨z.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
      have he' : attachingMap n c b = x := Subtype.ext (congrArg (fun a : skeletonLT X (n + 1) => a.val) he)
      change g c z = f x
      exact (hag c b).trans (congrArg f he')
  have hfib : ∀ p p', q p = q p' → w p = w p' := by
    intro p p' he
    cases p with
    | inl x => exact (hold p' x he.symm).symm
    | inr p =>
      rcases p with ⟨c, z⟩
      have hle : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      rcases lt_or_eq_of_le hle with hz | hz
      · have hi : characteristic X n c z ∈ openCell X n c := by
          refine ⟨⟨z.val, ?_⟩, rfl⟩
          simpa only [Metric.mem_ball, dist_zero_right] using hz
        have hn := openCell_not_mem_lower_skeleton n c hi
        cases p' with
        | inl x =>
          exfalso
          apply hn
          have he' := congrArg Subtype.val he
          change characteristic X n c z = x.val at he'
          exact he' ▸ x.property
        | inr p' =>
          rcases p' with ⟨d, z'⟩
          have he' := congrArg Subtype.val he
          change characteristic X n c z = characteristic X n d z' at he'
          have hle' : ‖z'.val‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using z'.property
          have hz' : ‖z'.val‖ < 1 := by
            rcases lt_or_eq_of_le hle' with h | h
            · exact h
            · exfalso
              apply hn
              rw [he']
              exact CWStructure.boundary_lands n d (mem_univ
                (⟨z'.val, by simpa only [Metric.mem_sphere, dist_zero_right] using h⟩ : Sphere n))
          let a : OpenDisk n := ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
          let a' : OpenDisk n := ⟨z'.val, by simpa only [Metric.mem_ball, dist_zero_right] using hz'⟩
          have hi' : characteristic X n c z ∈ openCell X n d := ⟨a', he'.symm⟩
          have hcd : (⟨n, c⟩ : Σ k, Cell X k) = ⟨n, d⟩ :=
            CWStructure.disjoint_interiors.elim_set (mem_univ _) (mem_univ _) _ hi hi'
          have hd : c = d := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hcd
          subst d
          have ha : a = a' := (CWStructure.interior_embedding n c).injective he'
          have hzze : z = z' := Subtype.ext (congrArg (fun a : OpenDisk n => a.val) ha)
          cases hzze
          rfl
      · let b : Sphere n := ⟨z.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
        let x := attachingMap n c b
        have hp : q (Sum.inr ⟨c, z⟩) = oldSkeletonInclusion X n x := rfl
        exact (hold _ x hp).trans (hold p' x (he.symm.trans hp)).symm
  obtain ⟨h, ⟨hhc, hhe⟩, _⟩ := D10Topology.Ch03.quotient_descent q
    ((D10Topology.Ch03.quotientMap_iff_mathlib q).mpr (CWStructure.attachment_quotient n)) w hc hfib
  exact ⟨⟨h, hhc⟩, fun x => congrFun hhe (Sum.inl x),
    fun c z => congrFun hhe (Sum.inr ⟨c, z⟩)⟩

/-- Extend a boundary homotopy which has stopped by time a, then compress
the disk during [a,b]. The old boundary homotopy keeps its original timing. -/
theorem timed_disk_compression
    (hdisk : P202Specs.Topology.ExpectedDiskReplacement.diskReplacement.{u})
    (A : Subcomplex X) (hweak : P202Specs.Topology.IsWeakHomotopyEquivalenceInclusion A.carrier)
    (n : ℕ) (a b : Interval) (hab : a < b) (f : C(Disk n, X))
    (h : C(Sphere n × Interval, X))
    (hzero : ∀ z, h (z, 0) = f (boundaryInclusion n z))
    (hstop : ∀ z t, a ≤ t → h (z, t) = h (z, 1))
    (hend : ∀ z, h (z, 1) ∈ A.carrier) :
    ∃ H : C(Disk n × Interval, X),
      (∀ z, H (z, 0) = f z) ∧
      (∀ z t, H (boundaryInclusion n z, t) = h (z, t)) ∧
      (∀ z, H (z, 1) ∈ A.carrier) ∧
      (∀ z t, b ≤ t → H (z, t) = H (z, 1)) := by
  classical
  obtain ⟨E, hE0, hEs⟩ := diskCylinderExtension n f h hzero
  let f' : C(Disk n, X) := ⟨fun z => E (z, a),
    E.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hf'b : ∀ z : Sphere n, f' (boundaryInclusion n z) ∈ A.carrier := by
    intro z
    change E (boundaryInclusion n z, a) ∈ A.carrier
    rw [hEs, hstop z a le_rfl]
    exact hend z
  obtain ⟨g, K, hK0, hK1, hKs⟩ := characteristic_disk_compression hdisk A hweak n f' hf'b
  let s : Interval → Interval := fun t =>
    Set.projIcc 0 1 zero_le_one (((t : ℝ) - a) / ((b : ℝ) - a))
  have hs : Continuous s := continuous_projIcc.comp
    (((continuous_subtype_val.sub continuous_const).div_const ((b : ℝ) - a)))
  have hsa : s a = 0 := by
    dsimp [s]
    simp
  have hsb (t : Interval) (ht : b ≤ t) : s t = 1 := by
    apply projIcc_eq_one.mpr
    apply (le_div_iff₀ (sub_pos.mpr (show (a : ℝ) < b from hab))).mpr
    change (b : ℝ) ≤ t at ht
    linarith
  have hs1 : s 1 = 1 := hsb 1 b.property.2
  let Hfun : Disk n × Interval → X := fun p =>
    if p.2 ≤ a then E p else K (p.1, s p.2)
  have hc : Continuous Hfun := by
    apply continuous_if_le continuous_snd continuous_const E.continuous.continuousOn
      (K.continuous.comp (continuous_fst.prodMk (hs.comp continuous_snd))).continuousOn
    intro p hp
    rcases p with ⟨z, t⟩
    change t = a at hp
    change E (z, t) = K (z, s t)
    subst t
    rw [hsa, hK0]
    rfl
  have hH0 (z : Disk n) : Hfun (z, 0) = f z := by
    simp only [Hfun, show (0 : Interval) ≤ a from a.property.1, ↓reduceIte]
    exact hE0 z
  have hH1 (z : Disk n) : Hfun (z, 1) = (g z).val := by
    have ha1 : ¬(1 : Interval) ≤ a := not_le.mpr (lt_of_lt_of_le hab b.property.2)
    simp only [Hfun, ha1, ↓reduceIte, hs1, hK1]
  refine ⟨⟨Hfun, hc⟩, hH0, ?_, ?_, ?_⟩
  · intro z t
    dsimp [Hfun]
    split_ifs with ht
    · exact hEs z t
    · rw [hKs]
      change E (boundaryInclusion n z, a) = h (z, t)
      rw [hEs, hstop z a le_rfl, hstop z t (le_of_lt (lt_of_not_ge ht))]
  · intro z
    change Hfun (z, 1) ∈ A.carrier
    rw [hH1]
    exact (g z).property
  · intro z t ht
    change Hfun (z, t) = Hfun (z, 1)
    rw [hH1]
    have hat : ¬t ≤ a := not_le.mpr (lt_of_lt_of_le hab ht)
    simp only [Hfun, hat, ↓reduceIte, hsb t ht, hK1]

/-- The terminal times of the finite skeletal constructions. -/
def skeletalTime (n : ℕ) : Interval :=
  ⟨1 - (1 / 2 : ℝ) ^ n,
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)),
    sub_le_self _ (pow_nonneg (by norm_num) _)⟩

@[simp] theorem skeletalTime_zero : skeletalTime 0 = 0 := by
  apply Subtype.ext
  norm_num [skeletalTime]

theorem skeletalTime_lt_succ (n : ℕ) : skeletalTime n < skeletalTime (n + 1) := by
  change 1 - (1 / 2 : ℝ) ^ n < 1 - (1 / 2 : ℝ) ^ (n + 1)
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

/-- A finite stage of the deformation, defined on the actual skeleton
subspace and already stationary near time one. -/
structure SkeletalCompressionStage (A : Subcomplex X) (n : ℕ) where
  homotopy : C(skeletonLT X n × Interval, X)
  initial : ∀ x, homotopy (x, 0) = x.val
  fixed : ∀ x, x.val ∈ A.carrier → ∀ t, homotopy (x, t) = x.val
  terminal : ∀ x, homotopy (x, 1) ∈ A.carrier
  stationary : ∀ x t, skeletalTime n ≤ t → homotopy (x, t) = homotopy (x, 1)

/-- Extend one stage over every cell of the next dimension. The extension
agrees with the entire old homotopy, including its timing. -/
theorem skeletalCompressionStage_step
    (hdisk : P202Specs.Topology.ExpectedDiskReplacement.diskReplacement.{u})
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) (hweak : P202Specs.Topology.IsWeakHomotopyEquivalenceInclusion A.carrier)
    (n : ℕ) (S : SkeletalCompressionStage A n) :
    ∃ S' : SkeletalCompressionStage A (n + 1), ∀ x t,
      S'.homotopy (oldSkeletonInclusion X n x, t) = S.homotopy (x, t) := by
  classical
  have cells : ∀ c : Cell X n, ∃ K : C(Disk n × Interval, X),
      (∀ z, K (z, 0) = characteristic X n c z) ∧
      (∀ z t, K (boundaryInclusion n z, t) = S.homotopy (attachingMap n c z, t)) ∧
      (∀ z, K (z, 1) ∈ A.carrier) ∧
      (∀ z t, skeletalTime (n + 1) ≤ t → K (z, t) = K (z, 1)) ∧
      (c ∈ A.cells n → ∀ z t, K (z, t) = characteristic X n c z) := by
    intro c
    by_cases hc : c ∈ A.cells n
    · refine ⟨⟨fun p => characteristic X n c p.1,
        (characteristic X n c).continuous.comp continuous_fst⟩,
        fun _ => rfl, ?_, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
      · intro z t
        symm
        apply S.fixed
        exact selected_characteristic_mem hclosure A hc (boundaryInclusion n z)
      · intro z
        exact selected_characteristic_mem hclosure A hc z
    · let hb : C(Sphere n × Interval, X) :=
        S.homotopy.comp ((attachingMap n c).prodMap (ContinuousMap.id _))
      obtain ⟨K, hK0, hKs, hK1, hKstop⟩ := timed_disk_compression hdisk A hweak n
        (skeletalTime n) (skeletalTime (n + 1)) (skeletalTime_lt_succ n)
        (characteristic X n c) hb (fun z => S.initial (attachingMap n c z))
        (fun z t ht => S.stationary (attachingMap n c z) t ht)
        (fun z => S.terminal (attachingMap n c z))
      exact ⟨K, hK0, hKs, hK1, hKstop, fun h => (hc h).elim⟩
  let K : ∀ c : Cell X n, C(Disk n × Interval, X) := fun c => (cells c).choose
  have hK c := (cells c).choose_spec
  obtain ⟨G, hGold, hGcell⟩ := exists_attachment_pasting n S.homotopy.curry
    (fun c => (K c).curry) (by
      intro c z
      ext t
      exact (hK c).2.1 z t)
  let H : C(skeletonLT X (n + 1) × Interval, X) := G.uncurry
  have hold (x : skeletonLT X n) (t : Interval) :
      H (oldSkeletonInclusion X n x, t) = S.homotopy (x, t) :=
    congrArg (fun h : C(Interval, X) => h t) (hGold x)
  have hcell (c : Cell X n) (z : Disk n) (t : Interval) :
      H (diskToSkeleton X CWStructure.boundary_lands n c z, t) = K c (z, t) :=
    congrArg (fun h : C(Interval, X) => h t) (hGcell c z)
  have hinitial : ∀ x, H (x, 0) = x.val := by
    intro x
    obtain ⟨p, rfl⟩ := (CWStructure.attachment_quotient n).surjective x
    cases p with
    | inl y => exact (hold y 0).trans (S.initial y)
    | inr p => exact (hcell p.1 p.2 0).trans ((hK p.1).1 p.2)
  have hterminal : ∀ x, H (x, 1) ∈ A.carrier := by
    intro x
    obtain ⟨p, rfl⟩ := (CWStructure.attachment_quotient n).surjective x
    cases p with
    | inl y =>
      change H (oldSkeletonInclusion X n y, 1) ∈ A.carrier
      rw [hold]
      exact S.terminal y
    | inr p =>
      change H (diskToSkeleton X CWStructure.boundary_lands n p.1 p.2, 1) ∈ A.carrier
      rw [hcell]
      exact (hK p.1).2.2.1 p.2
  have hstationary : ∀ x t, skeletalTime (n + 1) ≤ t → H (x, t) = H (x, 1) := by
    intro x t ht
    obtain ⟨p, rfl⟩ := (CWStructure.attachment_quotient n).surjective x
    cases p with
    | inl y =>
      change H (oldSkeletonInclusion X n y, t) = H (oldSkeletonInclusion X n y, 1)
      rw [hold, hold]
      exact S.stationary y t ((skeletalTime_lt_succ n).le.trans ht)
    | inr p =>
      change H (diskToSkeleton X CWStructure.boundary_lands n p.1 p.2, t) =
        H (diskToSkeleton X CWStructure.boundary_lands n p.1 p.2, 1)
      rw [hcell, hcell]
      exact (hK p.1).2.2.2.1 p.2 t ht
  have hfixed : ∀ x, x.val ∈ A.carrier → ∀ t, H (x, t) = x.val := by
    intro x hx t
    obtain ⟨p, rfl⟩ := (CWStructure.attachment_quotient n).surjective x
    cases p with
    | inl y => exact (hold y t).trans (S.fixed y hx t)
    | inr p =>
      rcases p with ⟨c, z⟩
      change H (diskToSkeleton X CWStructure.boundary_lands n c z, t) = characteristic X n c z
      rw [hcell]
      have hle : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      rcases lt_or_eq_of_le hle with hz | hz
      · have hi : characteristic X n c z ∈ openCell X n c := by
          refine ⟨⟨z.val, ?_⟩, rfl⟩
          simpa only [Metric.mem_ball, dist_zero_right] using hz
        exact (hK c).2.2.2.2 (selected_of_mem_openCell A hi hx) z t
      · let b : Sphere n := ⟨z.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
        exact ((hK c).2.1 b t).trans (S.fixed (attachingMap n c b) hx t)
  exact ⟨⟨H, hinitial, hfixed, hterminal, hstationary⟩, hold⟩

/-- The empty initial skeleton has its unique homotopy. -/
def skeletalCompressionStage_zero (A : Subcomplex X) : SkeletalCompressionStage A 0 where
  homotopy := ⟨fun p => p.1.val, continuous_subtype_val.comp continuous_fst⟩
  initial _ := rfl
  fixed _ _ _ := rfl
  terminal x := by
    have hx := x.property
    simp [skeletonLT] at hx
  stationary _ _ _ := rfl

/-- Compatible homotopies on all actual skeleta. -/
def skeletalCompressionStages
    (hdisk : P202Specs.Topology.ExpectedDiskReplacement.diskReplacement.{u})
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) (hweak : P202Specs.Topology.IsWeakHomotopyEquivalenceInclusion A.carrier) :
    ∀ n, SkeletalCompressionStage A n :=
  fun n => Nat.rec (skeletalCompressionStage_zero A)
    (fun n S => (skeletalCompressionStage_step hdisk hclosure A hweak n S).choose) n

theorem skeletalCompressionStages_compatible
    (hdisk : P202Specs.Topology.ExpectedDiskReplacement.diskReplacement.{u})
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u})
    (A : Subcomplex X) (hweak : P202Specs.Topology.IsWeakHomotopyEquivalenceInclusion A.carrier)
    (n : ℕ) (x : skeletonLT X n) (t : Interval) :
    (skeletalCompressionStages hdisk hclosure A hweak (n + 1)).homotopy
        (oldSkeletonInclusion X n x, t) =
      (skeletalCompressionStages hdisk hclosure A hweak n).homotopy (x, t) :=
  (skeletalCompressionStage_step hdisk hclosure A hweak n
    (skeletalCompressionStages hdisk hclosure A hweak n)).choose_spec x t

/-- Pass from compatible finite skeletal homotopies to a strong
 deformation retraction. The equality on each whole characteristic cylinder
 proves continuity at time one, as well as at all intermediate times. -/
theorem deformationRetraction_of_skeletalStages
    (A : Subcomplex X) (S : ∀ n, SkeletalCompressionStage A n)
    (hcompatible : ∀ n (x : skeletonLT X n) t,
      (S (n + 1)).homotopy (oldSkeletonInclusion X n x, t) = (S n).homotopy (x, t)) :
    ∃ (r : C(X, A)) (H : C(X × Interval, X)),
      (∀ a : A, r a.val = a) ∧
      (∀ x, H (x, 0) = x) ∧
      (∀ x, H (x, 1) = (r x).val) ∧
      (∀ (a : A) t, H (a.val, t) = a.val) := by
  classical
  have stable (n m : ℕ) (hnm : n ≤ m) (x : X) (hx : x ∈ skeletonLT X n) (t : Interval) :
      (S m).homotopy (⟨x, skeletonLT_mono hnm hx⟩, t) = (S n).homotopy (⟨x, hx⟩, t) := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      exact (hcompatible m ⟨x, skeletonLT_mono hnm hx⟩ t).trans ih
  have covered (x : X) : ∃ n, x ∈ skeletonLT X n := by
    obtain ⟨⟨n, c, z⟩, rfl⟩ := (characteristicDiskQuotient (X := X)).surjective x
    exact ⟨n + 1, characteristic_mem_skeletonLT n c z⟩
  let rank : X → ℕ := fun x => Nat.find (covered x)
  have hrank (x : X) : x ∈ skeletonLT X (rank x) := Nat.find_spec (covered x)
  let Hfun : X × Interval → X := fun p => (S (rank p.1)).homotopy (⟨p.1, hrank p.1⟩, p.2)
  have heq (n : ℕ) (x : X) (hx : x ∈ skeletonLT X n) (t : Interval) :
      Hfun (x, t) = (S n).homotopy (⟨x, hx⟩, t) := by
    change (S (rank x)).homotopy _ = _
    rcases le_total (rank x) n with h | h
    · exact (stable (rank x) n h x (hrank x) t).symm
    · exact stable n (rank x) h x hx t
  have hc : Continuous Hfun := by
    apply continuous_on_characteristic_products
    intro n c
    have he : Hfun ∘ Prod.map (characteristic X n c) id =
        (S (n + 1)).homotopy ∘
          Prod.map (diskToSkeleton X CWStructure.boundary_lands n c) id := by
      funext p
      exact heq (n + 1) _ (characteristic_mem_skeletonLT n c p.1) p.2
    rw [he]
    exact (S (n + 1)).homotopy.continuous.comp
      (((characteristic X n c).continuous.subtype_mk _).prodMap continuous_id)
  let H : C(X × Interval, X) := ⟨Hfun, hc⟩
  let r : C(X, A) := ⟨fun x => ⟨H (x, 1), (S (rank x)).terminal ⟨x, hrank x⟩⟩,
    (H.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩
  refine ⟨r, H, ?_, ?_, fun _ => rfl, ?_⟩
  · intro a
    apply Subtype.ext
    exact (S (rank a.val)).fixed ⟨a.val, hrank a.val⟩ a.property 1
  · intro x
    exact (S (rank x)).initial ⟨x, hrank x⟩
  · intro a t
    exact (S (rank a.val)).fixed ⟨a.val, hrank a.val⟩ a.property t

/-- Cellwise disk compression suffices for the full inclusion conclusion.
All geometric homotopy extension and pasting used above has been proved
independently, so no same-universe specialization of a conditional premise
with two independent universe parameters is needed. -/
theorem whiteheadSubcomplexRetraction_of_diskReplacement
    (hdisk : P202Specs.Topology.ExpectedDiskReplacement.diskReplacement.{u})
    (hclosure : P202Specs.Topology.CellStructures.closureOpenCell.{u}) :
    P202Specs.Topology.WhiteheadSubcomplexRetraction.strongDeformationRetraction.{u} := by
  intro X _ _ A hweak
  exact deformationRetraction_of_skeletalStages A
    (skeletalCompressionStages hdisk hclosure A hweak)
    (skeletalCompressionStages_compatible hdisk hclosure A hweak)

/-- A weak homotopy equivalence given by a CW subcomplex inclusion is a
strong deformation retraction, also for disconnected and infinite complexes. -/
theorem whiteheadSubcomplexRetraction :
    P202Specs.Topology.WhiteheadSubcomplexRetraction.strongDeformationRetraction.{u} :=
  whiteheadSubcomplexRetraction_of_diskReplacement diskReplacement closureOpenCell

end P202.Topology
