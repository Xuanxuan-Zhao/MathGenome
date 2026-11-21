import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellularApproximation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.HomotopyExtension
import Mathlib.Analysis.Convex.GaugeRescale
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.AvoidHigherCell
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max

noncomputable section
open Set Topology
open P202.Cellular
universe u v w

namespace P202.Topology.CellularApproximation

variable {X : Type u} [TopologicalSpace X] [CWStructure X]

lemma skeleton_mono {m n : ℤ} (hmn : m ≤ n) : skeleton X m ⊆ skeleton X n := by
  intro x hx
  simp only [skeleton, mem_iUnion] at hx ⊢
  obtain ⟨k, hk, c, hx⟩ := hx
  exact ⟨k, hk.trans hmn, c, hx⟩

lemma closedCell_subset_skeletonLT (n : ℕ) (c : Cell X n) :
    closedCell X n c ⊆ skeletonLT X (n + 1) := by
  rintro x ⟨z, rfl⟩
  exact (diskToSkeleton X CWStructure.boundary_lands n c z).2

/-- Adjoin the cells of dimensions less than `n` to a subcomplex. -/
def withSkeletonLT (A : Subcomplex X) (n : ℕ) : Subcomplex X where
  cells m := {c | c ∈ A.cells m ∨ m < n}
  contains_closures := by
    intro m c hc x hx
    rcases hc with ha | hm
    · obtain ⟨k, hd⟩ := mem_iUnion.mp (A.contains_closures m c ha hx)
      obtain ⟨d, hd⟩ := mem_iUnion.mp hd
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨d.1, Or.inl d.2⟩, hd⟩⟩
    · rw [P202.Topology.closureOpenCell m c] at hx
      have hs := P202.Topology.skeletonLT_mono (X := X) (Nat.succ_le_of_lt hm)
        (closedCell_subset_skeletonLT m c hx)
      obtain ⟨k, hk⟩ := mem_iUnion.mp hs
      obtain ⟨hkn, hk⟩ := mem_iUnion.mp hk
      obtain ⟨d, hd⟩ := mem_iUnion.mp hk
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨d, Or.inr hkn⟩, hd⟩⟩

lemma withSkeletonLT_carrier (A : Subcomplex X) (n : ℕ) :
    (withSkeletonLT A n).carrier = A.carrier ∪ skeletonLT X n := by
  ext x
  simp only [Subcomplex.carrier, withSkeletonLT, skeletonLT, mem_union, mem_iUnion,
    Subtype.exists, mem_ofPred_eq]
  constructor
  · rintro ⟨m, c, hc, hx⟩
    exact hc.elim (fun h => Or.inl ⟨m, c, h, hx⟩) (fun h => Or.inr ⟨m, h, c, hx⟩)
  · rintro (⟨m, c, hc, hx⟩ | ⟨m, hm, c, hx⟩)
    · exact ⟨m, c, Or.inl hc, hx⟩
    · exact ⟨m, c, Or.inr hm, hx⟩

lemma selected_disk_mem (A : Subcomplex X) {n : ℕ} (c : Cell X n)
    (hc : c ∈ A.cells n) (z : Disk n) : characteristic X n c z ∈ A.carrier :=
  HomotopyExtension.selected_disk_mem P202.Topology.closureOpenCell A c hc z

/-- Projection from the selected characteristic disks to a subcomplex. -/
def subcomplexProjection (A : Subcomplex X) :
    (Σ n, Σ c : A.cells n, Disk n) → A :=
  fun p => ⟨characteristic X p.1 p.2.1.1 p.2.2,
    selected_disk_mem A p.2.1.1 p.2.1.2 p.2.2⟩

lemma subcomplexProjection_surjective (A : Subcomplex X) :
    Function.Surjective (subcomplexProjection A) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  obtain ⟨c, p, hp⟩ := mem_iUnion.mp hn
  exact ⟨⟨n, c, interiorInclusion n p⟩, Subtype.ext hp⟩

/-- The actual subspace topology is the quotient topology of the selected
disks. This is derived from the upstream subcomplex weak-topology theorem. -/
lemma subcomplexProjection_quotient (A : Subcomplex X) :
    IsQuotientMap (subcomplexProjection A) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨subcomplexProjection_surjective A, ?_⟩
  intro S
  let B : Set X := Subtype.val '' S
  have hBA : B ⊆ A.carrier := by rintro _ ⟨a, _, rfl⟩; exact a.2
  have hSB : (Subtype.val : A → X) ⁻¹' B = S :=
    preimage_image_eq _ Subtype.val_injective
  rw [← hSB, P202.Topology.subcomplexWeakTopology A B hBA]
  simp only [isClosed_sigma_iff]
  constructor
  · intro h n c
    exact h n c.1 c.2
  · intro h n c hc
    exact h n ⟨c, hc⟩

/-- Descend compatible maps on the selected disks. Targets need no separation
axioms, and the target universe is independent of the source universe. -/
lemma subcomplexDescent {Z : Type w} [TopologicalSpace Z] (A : Subcomplex X)
    (f : (Σ n, Σ c : A.cells n, Disk n) → Z) (hf : Continuous f)
    (hfib : ∀ p q, subcomplexProjection A p = subcomplexProjection A q → f p = f q) :
    ∃ g : C(A, Z), ∀ p, g (subcomplexProjection A p) = f p := by
  obtain ⟨g, ⟨hg, hgf⟩, _⟩ := D10Topology.Ch03.quotient_descent
    (subcomplexProjection A)
    ((P202.Topology.quotientAdapter _).mpr (subcomplexProjection_quotient A)) f hf hfib
  exact ⟨⟨g, hg⟩, congrFun hgf⟩

variable {Y : Type v} [TopologicalSpace Y]

lemma interior_lift_of_not_old {n : ℕ} (c : Cell X n) (x : Disk n)
    (hx : characteristic X n c x ∉ skeletonLT X n) :
    ∃ z : OpenDisk n, interiorInclusion n z = x := by
  rcases HomotopyExtension.disk_point_alternative x with ⟨z, rfl⟩ | h
  · exact False.elim (hx (CWStructure.boundary_lands n c (mem_univ z)))
  · exact h

lemma disk_fibre_unique {n : ℕ} (c d : Cell X n) (x z : Disk n)
    (heq : characteristic X n c x = characteristic X n d z)
    (hx : characteristic X n c x ∉ skeletonLT X n) : c = d ∧ x = z := by
  obtain ⟨a, rfl⟩ := interior_lift_of_not_old c x hx
  obtain ⟨b, rfl⟩ := interior_lift_of_not_old d z (by simpa only [← heq] using hx)
  have hcd : (⟨n, c⟩ : Σ m, Cell X m) = ⟨n, d⟩ :=
    CWStructure.disjoint_interiors.elim_set (mem_univ _) (mem_univ _)
      (interiorMap X n c a) ⟨a, rfl⟩ ⟨b, heq.symm⟩
  have hc : c = d := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hcd
  subst d
  exact ⟨rfl, congrArg (interiorInclusion n) ((CWStructure.interior_embedding n c).injective heq)⟩

/-- Paste simultaneous homotopies on all `n`-cells onto the subcomplex
`A ∪ Xⁿ`. The only overlap requirement is stationarity on `A ∪ Xⁿ⁻¹`.
Neither the collection of cells nor the dimension of `A` is bounded. -/
lemma pasteCellHomotopies (A : Subcomplex X) (n : ℕ) (f : C(X, Y))
    (h : ∀ c : Cell X n, C(Disk n, C(Interval, Y)))
    (hfixed : ∀ c z, characteristic X n c z ∈ A.carrier ∪ skeletonLT X n →
      h c z = ContinuousMap.const Interval (f (characteristic X n c z))) :
    ∃ g : C(withSkeletonLT A (n + 1), C(Interval, Y)),
      (∀ (x : withSkeletonLT A (n + 1)), x.1 ∈ A.carrier ∪ skeletonLT X n →
        g x = ContinuousMap.const Interval (f x.1)) ∧
      ∀ c z, g (subcomplexProjection (withSkeletonLT A (n + 1))
        ⟨n, ⟨c, Or.inr (Nat.lt_succ_self n)⟩, z⟩) = h c z := by
  classical
  let O := A.carrier ∪ skeletonLT X n
  let P (x : X) := ∃ c : Cell X n, ∃ z : Disk n, characteristic X n c z = x
  let F (x : X) : C(Interval, Y) :=
    if hx : x ∈ O then ContinuousMap.const Interval (f x)
    else if hp : P x then h hp.choose hp.choose_spec.choose
    else ContinuousMap.const Interval (f x)
  have Fold (x : X) (hx : x ∈ O) : F x = ContinuousMap.const Interval (f x) := by
    simp only [F, dite_eq_left hx]
  have Fnew (c : Cell X n) (z : Disk n) : F (characteristic X n c z) = h c z := by
    by_cases hx : characteristic X n c z ∈ O
    · exact (Fold _ hx).trans (hfixed c z hx).symm
    · have hp : P (characteristic X n c z) := ⟨c, z, rfl⟩
      simp only [F, dite_eq_right hx, dite_eq_left hp]
      obtain ⟨hc, hz⟩ := disk_fibre_unique hp.choose c hp.choose_spec.choose z
        hp.choose_spec.choose_spec (fun hs => hx (Or.inr (by
          rw [hp.choose_spec.choose_spec] at hs
          exact hs)))
      exact congrArg₂ (fun c z => h c z) hc hz
  let B := withSkeletonLT A (n + 1)
  have Fold_disk (m : ℕ) (c : B.cells m) (hm : m ≠ n) (z : Disk m) :
      characteristic X m c.1 z ∈ O := by
    rcases c.2 with ha | hmn
    · exact Or.inl (selected_disk_mem A c.1 ha z)
    · have hmn' : m < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hmn) hm
      exact Or.inr (P202.Topology.skeletonLT_mono (Nat.succ_le_of_lt hmn')
        (closedCell_subset_skeletonLT m c.1 ⟨z, rfl⟩))
  have hF : Continuous (fun x : B => F x.1) := by
    apply (subcomplexProjection_quotient B).continuous_iff.mpr
    rw [continuous_sigma_iff]
    intro m
    rw [continuous_sigma_iff]
    intro c
    by_cases hm : m = n
    · subst m
      exact (h c.1).continuous.congr (fun z => (Fnew c.1 z).symm)
    · exact (ContinuousMap.continuous_const'.comp
        (f.continuous.comp (characteristic X m c.1).continuous)).congr
        (fun z => (Fold _ (Fold_disk m c hm z)).symm)
  exact ⟨⟨_, hF⟩, fun x hx => Fold x.1 hx, Fnew⟩

/-- One source dimension of cellular approximation. Local disk homotopies
extend to a global homotopy stationary on `A ∪ Xⁿ⁻¹`, by the proved CW HEP.
Relative disk compression supplies the local input. -/
lemma extendCellHomotopies (A : Subcomplex X) (n : ℕ) (f : C(X, Y))
    (h : ∀ c : Cell X n, C(Disk n, C(Interval, Y)))
    (hzero : ∀ c z, h c z 0 = f (characteristic X n c z))
    (hfixed : ∀ c z, characteristic X n c z ∈ A.carrier ∪ skeletonLT X n →
      h c z = ContinuousMap.const Interval (f (characteristic X n c z))) :
    ∃ F : C(X, Y), ∃ H : f.HomotopyRel F (A.carrier ∪ skeletonLT X n),
      ∀ c z t, H (t, characteristic X n c z) = h c z t := by
  obtain ⟨g, gold, gnew⟩ := pasteCellHomotopies A n f h hfixed
  let B := withSkeletonLT A (n + 1)
  have gzero (x : B) : g x 0 = f x.1 := by
    by_cases hx : x.1 ∈ A.carrier ∪ skeletonLT X n
    · rw [gold x hx]; rfl
    · have hxB : x.1 ∈ A.carrier ∪ skeletonLT X (n + 1) :=
        (congrArg (fun S : Set X => x.1 ∈ S) (withSkeletonLT_carrier A (n + 1))).mp x.2
      rcases hxB with ha | hs
      · exact False.elim (hx (Or.inl ha))
      · obtain ⟨m, hm⟩ := mem_iUnion.mp hs
        obtain ⟨hmn, hm⟩ := mem_iUnion.mp hm
        obtain ⟨c, z, hz⟩ := mem_iUnion.mp hm
        have hmn' : m = n := by
          apply le_antisymm (Nat.le_of_lt_succ hmn)
          apply le_of_not_gt
          intro hm
          exact hx (Or.inr (mem_iUnion.mpr ⟨m, mem_iUnion.mpr
            ⟨hm, mem_iUnion.mpr ⟨c, ⟨z, hz⟩⟩⟩⟩))
        subst m
        have heq : subcomplexProjection B
            ⟨n, ⟨c, Or.inr (Nat.lt_succ_self n)⟩, interiorInclusion n z⟩ = x :=
          Subtype.ext hz
        rw [← heq, gnew]
        exact hzero c (interiorInclusion n z)
  let gend : C(B, Y) := ⟨fun x => g x 1,
    (continuous_eval_const 1).comp g.continuous⟩
  let b : (f.comp (P202Specs.Topology.HomotopyExtension.subcomplexInclusion B)).Homotopy gend :=
    { toFun := fun p => g p.2 p.1
      continuous_toFun := g.uncurry.continuous.comp continuous_swap
      map_zero_left := gzero
      map_one_left := fun _ => rfl }
  obtain ⟨F, H, hH⟩ := P202.Topology.cwHomotopyExtension X Y B f gend b
  have fixed (t : Interval) (x : X) (hx : x ∈ A.carrier ∪ skeletonLT X n) :
      H (t, x) = f x := by
    have hB : x ∈ B.carrier := by
      rw [withSkeletonLT_carrier]
      exact hx.elim Or.inl (fun hs => Or.inr
        (P202.Topology.skeletonLT_mono (Nat.le_succ n) hs))
    rw [hH t ⟨x, hB⟩]
    change g ⟨x, hB⟩ t = f x
    rw [gold _ hx]; rfl
  refine ⟨F, { H with prop' := fun t x hx => fixed t x hx }, ?_⟩
  intro c z t
  have hc : characteristic X n c z ∈ B.carrier :=
    selected_disk_mem B c (Or.inr (Nat.lt_succ_self n)) z
  change H (t, characteristic X n c z) = _
  rw [hH t ⟨_, hc⟩]
  change g (subcomplexProjection B ⟨n, ⟨c, Or.inr (Nat.lt_succ_self n)⟩, z⟩) t = _
  rw [gnew]

/-- The dimension convention agrees with absence of higher cells. -/
lemma hasDimensionLE_iff (n : ℕ) :
    HasDimensionLE X n ↔ ∀ m, n < m → IsEmpty (Cell X m) := by
  constructor
  · intro h m hnm
    refine ⟨fun c => ?_⟩
    let z : OpenDisk m := ⟨0, by simp⟩
    have hx : interiorMap X m c z ∈ skeleton X (n : ℤ) := by rw [h]; trivial
    have hx' : interiorMap X m c z ∈ skeletonLT X m := by
      rw [P202.Topology.skeletonIndexing n] at hx
      exact P202.Topology.skeletonLT_mono (Nat.succ_le_of_lt hnm) hx
    exact Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT m c) ⟨z, rfl⟩ hx'
  · intro h
    apply eq_univ_of_forall
    intro x
    obtain ⟨m, hm⟩ := mem_iUnion.mp (show x ∈ ⋃ (m : ℕ) (c : Cell X m), openCell X m c by
      rw [CWStructure.cover]; trivial)
    obtain ⟨c, hc⟩ := mem_iUnion.mp hm
    have hmn : m ≤ n := le_of_not_gt (fun hnm => (h m hnm).false c)
    exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨by exact_mod_cast hmn,
      mem_iUnion.mpr ⟨c, hc⟩⟩⟩

variable [CWStructure Y]

/-- Given the relative disk-compression lemma, one whole source dimension can
be treated simultaneously. This includes `n = 0`: its boundary is empty and
the old skeleton is empty. The conclusion fixes the full prescribed `A`. -/
lemma skeletalStep_of_diskCompression
    (compress : ∀ (n : ℕ) (f : C(Disk n, Y)),
      (∀ z : Sphere n, f (boundaryInclusion n z) ∈ skeletonLT Y n) →
      ∃ h : C(Disk n × Interval, Y),
        (∀ z, h (z, 0) = f z) ∧
        (∀ z t, h (boundaryInclusion n z, t) = f (boundaryInclusion n z)) ∧
        ∀ z, h (z, 1) ∈ skeletonLT Y (n + 1))
    (A : Subcomplex X) (n : ℕ) (f : C(X, Y))
    (hA : IsCellularOn f A) (hold : MapsTo f (skeletonLT X n) (skeletonLT Y n)) :
    ∃ F : C(X, Y), ∃ H : f.HomotopyRel F (A.carrier ∪ skeletonLT X n),
      MapsTo F (skeletonLT X (n + 1)) (skeletonLT Y (n + 1)) := by
  classical
  have local_exists (c : Cell X n) :
      ∃ h : C(Disk n, C(Interval, Y)),
        (∀ z, h z 0 = f (characteristic X n c z)) ∧
        (∀ z, characteristic X n c z ∈ A.carrier ∪ skeletonLT X n →
          h z = ContinuousMap.const Interval (f (characteristic X n c z))) ∧
        ∀ z, h z 1 ∈ skeletonLT Y (n + 1) := by
    by_cases hc : c ∈ A.cells n
    · let h : C(Disk n, C(Interval, Y)) :=
        (ContinuousMap.const' : C(Y, C(Interval, Y))).comp (f.comp (characteristic X n c))
      refine ⟨h, fun _ => rfl, fun _ _ => rfl, ?_⟩
      intro z
      have hmem := hA n ⟨selected_disk_mem A c hc z, by
        rw [P202.Topology.skeletonIndexing n]
        exact closedCell_subset_skeletonLT n c ⟨z, rfl⟩⟩
      rwa [P202.Topology.skeletonIndexing n] at hmem
    · obtain ⟨k, hk0, hkb, hk1⟩ := compress n (f.comp (characteristic X n c))
        (fun z => hold (CWStructure.boundary_lands n c (mem_univ z)))
      refine ⟨k.curry, hk0, ?_, hk1⟩
      intro z hz
      rcases HomotopyExtension.disk_point_alternative z with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · ext t
        exact hkb w t
      · rcases hz with ha | hs
        · exact False.elim (hc (HomotopyExtension.selected_of_openCell_mem A c ⟨w, rfl⟩ ha))
        · exact False.elim ((Set.disjoint_left.mp
            (P202.Topology.openCellDisjointSkeletonLT n c)) ⟨w, rfl⟩ hs)
  choose h hz hf he using local_exists
  obtain ⟨F, H, hH⟩ := extendCellHomotopies A n f h hz hf
  refine ⟨F, H, ?_⟩
  intro x hx
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  obtain ⟨hmn, hm⟩ := mem_iUnion.mp hm
  obtain ⟨c, z, rfl⟩ := mem_iUnion.mp hm
  by_cases hm : m = n
  · subst m
    change F (characteristic X n c (interiorInclusion n z)) ∈ _
    rw [← H.apply_one, hH]
    exact he c (interiorInclusion n z)
  · have hmn' : m < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hmn) hm
    have hs : interiorMap X m c z ∈ skeletonLT X n :=
      mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn', mem_iUnion.mpr ⟨c, ⟨z, rfl⟩⟩⟩⟩
    rw [← H.apply_one, H.eq_fst 1 (Or.inr hs)]
    exact P202.Topology.skeletonLT_mono (Nat.le_succ n) (hold hs)

lemma cellular_range_subset_skeleton (n : ℕ) (f : C(X, Y))
    (hf : IsCellular f) (hdim : HasDimensionLE X n) :
    range f ⊆ skeleton Y (n : ℤ) := by
  rintro _ ⟨x, rfl⟩
  exact hf n (by rw [hdim]; trivial)

/-- The finite-dimensional relative consequence reduces to the full relative
approximation theorem. -/
lemma mapIntoSkeleton_of_cellularApproximation
    (h : P202Specs.Topology.CellularApproximation.cellularApproximation.{u,v}) :
    P202Specs.Topology.CellularApproximation.mapIntoSkeleton.{u,v} := by
  intro X Y _ _ _ _ n A f hdim hf
  obtain ⟨g, hg, H⟩ := h A f hf
  exact ⟨g, cellular_range_subset_skeleton n g hg hdim, H⟩

/-- Assembly from relative disk compression and a stationary telescope. -/
lemma cellularApproximation_of_diskCompression_of_telescope
    (compress : ∀ (n : ℕ) (f : C(Disk n, Y)),
      (∀ z : Sphere n, f (boundaryInclusion n z) ∈ skeletonLT Y n) →
      ∃ h : C(Disk n × Interval, Y),
        (∀ z, h (z, 0) = f z) ∧
        (∀ z t, h (boundaryInclusion n z, t) = f (boundaryInclusion n z)) ∧
        ∀ z, h (z, 1) ∈ skeletonLT Y (n + 1))
    (telescope : ∀ (S : Set X) (f : ℕ → C(X, Y))
      (h : ∀ n, (f n).HomotopyRel (f (n + 1)) (S ∪ skeletonLT X n)),
      ∃ F : C(X, Y), Nonempty ((f 0).HomotopyRel F S) ∧
        ∀ n x, x ∈ skeletonLT X n → F x = f n x)
    (A : Subcomplex X) (f : C(X, Y)) (hA : IsCellularOn f A) :
    ∃ g : C(X, Y), IsCellular g ∧ Nonempty (f.HomotopyRel g A.carrier) := by
  classical
  let Stage (n : ℕ) := {g : C(X, Y) // IsCellularOn g A ∧
    MapsTo g (skeletonLT X n) (skeletonLT Y n)}
  have step (n : ℕ) (s : Stage n) :
      ∃ s' : Stage (n + 1),
        Nonempty (s.1.HomotopyRel s'.1 (A.carrier ∪ skeletonLT X n)) := by
    obtain ⟨g, H, hg⟩ := skeletalStep_of_diskCompression compress A n s.1 s.2.1 s.2.2
    have hAg : IsCellularOn g A := by
      intro k x hx
      have heq : g x = s.1 x := (H.fst_eq_snd (Or.inl hx.1)).symm
      rw [heq]
      exact s.2.1 k hx
    exact ⟨⟨g, hAg, hg⟩, ⟨H⟩⟩
  let initial : Stage 0 := ⟨f, hA, by
    intro x hx
    simp [skeletonLT] at hx⟩
  let stages : ∀ n, Stage n := Nat.rec initial (fun n s => (step n s).choose)
  let h : ∀ n, (stages n).1.HomotopyRel (stages (n + 1)).1
      (A.carrier ∪ skeletonLT X n) :=
    fun n => Classical.choice (step n (stages n)).choose_spec
  obtain ⟨g, H, hg⟩ := telescope A.carrier (fun n => (stages n).1) h
  refine ⟨g, ?_, H⟩
  intro n x hx
  rw [P202.Topology.skeletonIndexing n] at hx ⊢
  rw [hg (n + 1) x hx]
  exact (stages (n + 1)).2.2 hx

/-- Right-associated finite concatenation: the first stage occupies half the
interval, the next a quarter, and the final map fills the remaining tail. -/
def finiteConcatenation (f : ℕ → C(X, Y))
    (h : ∀ n, (f n).Homotopy (f (n + 1))) : ∀ n, (f 0).Homotopy (f n)
  | 0 => ContinuousMap.Homotopy.refl (f 0)
  | n + 1 => (h 0).trans
      (finiteConcatenation (fun k => f (k + 1)) (fun k => h (k + 1)) n)

lemma finiteConcatenation_succ_agrees (f : ℕ → C(X, Y))
    (h : ∀ n, (f n).Homotopy (f (n + 1))) (n : ℕ) (x : X)
    (hx : ∀ t, h n (t, x) = f n x) (t : Interval) :
    finiteConcatenation f h (n + 1) (t, x) = finiteConcatenation f h n (t, x) := by
  induction n generalizing f t with
  | zero =>
    simp only [finiteConcatenation, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact hx _
    · exact ((h 0).apply_one x).symm.trans (hx 1)
  | succ n ih =>
    change ((h 0).trans (finiteConcatenation (fun k => f (k + 1))
      (fun k => h (k + 1)) (n + 1))) (t, x) =
      ((h 0).trans (finiteConcatenation (fun k => f (k + 1))
      (fun k => h (k + 1)) n)) (t, x)
    simp only [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · rfl
    · exact ih (fun k => f (k + 1)) (fun k => h (k + 1)) hx _

lemma finiteConcatenation_agrees (f : ℕ → C(X, Y))
    (h : ∀ n, (f n).Homotopy (f (n + 1))) {n m : ℕ} (hnm : n ≤ m) (x : X)
    (hx : ∀ k, n ≤ k → ∀ t, h k (t, x) = f k x) (t : Interval) :
    finiteConcatenation f h m (t, x) = finiteConcatenation f h n (t, x) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    exact (finiteConcatenation_succ_agrees f h m x (hx m hnm) t).trans ih

lemma finiteConcatenation_fixed (f : ℕ → C(X, Y))
    (h : ∀ n, (f n).Homotopy (f (n + 1))) (x : X)
    (hx : ∀ k t, h k (t, x) = f k x) (n : ℕ) (t : Interval) :
    finiteConcatenation f h n (t, x) = f 0 x :=
  finiteConcatenation_agrees f h (Nat.zero_le n) x (fun k _ => hx k) t

lemma exists_skeletonLT (x : X) : ∃ n, x ∈ skeletonLT X n := by
  have hx : x ∈ ⋃ (m : ℕ) (c : Cell X m), openCell X m c := by
    rw [CWStructure.cover]; trivial
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  exact ⟨m + 1, mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨Nat.lt_succ_self m, hm⟩⟩⟩

/-- Assemble a sequence of homotopies that eventually fix every skeleton.
The construction is equal to a finite continuous concatenation on each whole
characteristic disk, including at the terminal time. The ordinary product
weak-topology theorem therefore proves continuity of the assembled homotopy.
No bound on the dimension or number of cells is used. -/
lemma stationaryTelescope (S : Set X) (f : ℕ → C(X, Y))
    (h : ∀ n, (f n).HomotopyRel (f (n + 1)) (S ∪ skeletonLT X n)) :
    ∃ F : C(X, Y), Nonempty ((f 0).HomotopyRel F S) ∧
      ∀ n x, x ∈ skeletonLT X n → F x = f n x := by
  classical
  let r (x : X) : ℕ := Nat.find (exists_skeletonLT x)
  have hr (x : X) : x ∈ skeletonLT X (r x) := Nat.find_spec (exists_skeletonLT x)
  let p (n : ℕ) := finiteConcatenation f (fun k => (h k).toHomotopy) n
  let G (t : Interval) (x : X) : Y := p (r x) (t, x)
  have agree {n m : ℕ} (hnm : n ≤ m) (x : X) (hx : x ∈ skeletonLT X n)
      (t : Interval) : p m (t, x) = p n (t, x) := by
    apply finiteConcatenation_agrees f _ hnm x
    intro k hnk s
    exact (h k).eq_fst s (Or.inr (P202.Topology.skeletonLT_mono hnk hx))
  have local_eq (n : ℕ) (x : X) (hx : x ∈ skeletonLT X n) (t : Interval) :
      G t x = p n (t, x) := by
    exact (agree (Nat.find_min' (exists_skeletonLT x) hx) x (hr x) t).symm
  have hG : Continuous (fun z : X × Interval => G z.2 z.1) := by
    apply (P202.Topology.homotopyContinuityTest _).mpr
    intro n c
    have heq : (fun z : Disk n × Interval =>
        G z.2 (characteristic X n c z.1)) =
        fun z => p (n + 1) (z.2, characteristic X n c z.1) := by
      funext z
      exact local_eq (n + 1) _ (closedCell_subset_skeletonLT n c ⟨z.1, rfl⟩) z.2
    change Continuous (fun z : Disk n × Interval => G z.2 (characteristic X n c z.1))
    rw [heq]
    exact (p (n + 1)).continuous.comp
      (continuous_snd.prodMk ((characteristic X n c).continuous.comp continuous_fst))
  let M : C(Interval × X, Y) := ⟨fun z => G z.1 z.2, hG.comp continuous_swap⟩
  let F : C(X, Y) := M.comp ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩
  have zero (x : X) : M (0, x) = f 0 x := (p (r x)).apply_zero x
  refine ⟨F, ⟨{ toContinuousMap := M
                map_zero_left := zero
                map_one_left := fun _ => rfl
                prop' := ?_ }⟩, ?_⟩
  · intro t x hx
    exact finiteConcatenation_fixed f (fun k => (h k).toHomotopy) x
      (fun k s => (h k).eq_fst s (Or.inl hx)) (r x) t
  · intro n x hx
    exact (local_eq n x hx 1).trans ((p n).apply_one x)

/-- Combine relative disk compression with the stationary telescope. -/
lemma cellularApproximation_of_diskCompression
    (compress : ∀ (n : ℕ) (f : C(Disk n, Y)),
      (∀ z : Sphere n, f (boundaryInclusion n z) ∈ skeletonLT Y n) →
      ∃ h : C(Disk n × Interval, Y),
        (∀ z, h (z, 0) = f z) ∧
        (∀ z t, h (boundaryInclusion n z, t) = f (boundaryInclusion n z)) ∧
        ∀ z, h (z, 1) ∈ skeletonLT Y (n + 1))
    (A : Subcomplex X) (f : C(X, Y)) (hA : IsCellularOn f A) :
    ∃ g : C(X, Y), IsCellular g ∧ Nonempty (f.HomotopyRel g A.carrier) :=
  cellularApproximation_of_diskCompression_of_telescope compress stationaryTelescope A f hA

/-- A vertex, with its actual singleton carrier, is a subcomplex. -/
lemma exists_vertexSubcomplex (x₀ : X) (hx₀ : x₀ ∈ skeleton X 0) :
    ∃ A : Subcomplex X, A.carrier = {x₀} := by
  classical
  have hvertex : ∃ c : Cell X 0, openCell X 0 c = {x₀} := by
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx₀
    obtain ⟨hn0, hn⟩ := mem_iUnion.mp hn
    have hn' : n = 0 := by exact_mod_cast (Nat.le_zero.mp (by exact_mod_cast hn0))
    subst n
    obtain ⟨c, z, hz⟩ := mem_iUnion.mp hn
    refine ⟨c, ?_⟩
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subsingleton.elim w z, hz]
      exact mem_singleton x₀
    · intro hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨z, hz⟩
  obtain ⟨c₀, hc₀⟩ := hvertex
  let A : Subcomplex X :=
    { cells := fun n => {c | openCell X n c ⊆ {x₀}}
      contains_closures := by
        intro n c hc x hx
        have heq : x = x₀ := (closure_minimal hc isClosed_singleton hx)
        subst x
        exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr
          ⟨⟨c₀, hc₀.subset⟩, hc₀.symm ▸ mem_singleton x₀⟩⟩ }
  refine ⟨A, Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hn
    exact c.2 hc
  · intro x hx
    exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨⟨c₀, hc₀.subset⟩, hc₀.symm ▸ hx⟩⟩

lemma basedCellularApproximation_of_cellularApproximation
    (h : P202Specs.Topology.CellularApproximation.cellularApproximation.{u,v}) :
    P202Specs.Topology.CellularApproximation.basedCellularApproximation.{u,v} := by
  intro X Y _ _ _ _ f x₀ y₀ hx₀ hy₀ hf₀
  obtain ⟨A, hA⟩ := exists_vertexSubcomplex x₀ hx₀
  have hcell : IsCellularOn f A := by
    intro n x hx
    have hxx : x = x₀ := by simpa only [hA, mem_singleton_iff] using hx.1
    rw [hxx, hf₀]
    exact skeleton_mono (by exact_mod_cast Nat.zero_le n) hy₀
  obtain ⟨g, hg, ⟨H⟩⟩ := h A f hcell
  have hg₀ : g x₀ = y₀ := by
    rw [← H.fst_eq_snd (hA.symm ▸ mem_singleton x₀), hf₀]
  exact ⟨g, hg, hg₀, hA ▸ ⟨H⟩⟩

lemma basedMapIntoSkeleton_of_basedCellularApproximation
    (h : P202Specs.Topology.CellularApproximation.basedCellularApproximation.{u,v}) :
    P202Specs.Topology.CellularApproximation.basedMapIntoSkeleton.{u,v} := by
  intro X Y _ _ _ _ n f x₀ y₀ hdim hx₀ hy₀ hf₀
  obtain ⟨g, hg, hg₀, H⟩ := h f x₀ y₀ hx₀ hy₀ hf₀
  exact ⟨g, cellular_range_subset_skeleton n g hg hdim, hg₀, H⟩

lemma basedHomotopyIntoSkeleton_of_homotopyIntoSkeleton
    (h : P202Specs.Topology.CellularApproximation.homotopyIntoSkeleton.{u,v}) :
    P202Specs.Topology.CellularApproximation.basedHomotopyIntoSkeleton.{u,v} := by
  intro X Y _ _ _ _ n f₀ f₁ H x₀ y₀ hdim hf₀ hf₁ hx₀ hbase
  obtain ⟨A, hA⟩ := exists_vertexSubcomplex x₀ hx₀
  have hzero : f₀ x₀ = y₀ := (H.apply_zero x₀).symm.trans (hbase 0)
  have hfix (t : Interval) (a : A) : H (t, a.1) = f₀ a.1 := by
    have ha : a.1 = x₀ := by simpa only [hA, mem_singleton_iff] using a.2
    rw [ha, hbase, hzero]
  obtain ⟨K, hK, hrange, hHK⟩ := h n A f₀ f₁ H hdim hf₀ hf₁ hfix
  refine ⟨K, ?_, hrange, ?_⟩
  · intro t
    exact (hK t ⟨x₀, hA.symm ▸ mem_singleton x₀⟩).trans hzero
  · simpa only [cylinderRelativeSet, hA, mem_singleton_iff] using hHK

/-- Radial deformation away from an arbitrary interior point of a disk.
The gauge of the translated unit ball gives the ray's intersection with the
sphere without a quadratic formula. The sphere is fixed throughout. -/
lemma puncturedDiskDeformation (k : ℕ) (p : OpenDisk k) :
    ∃ R : C({x : Disk k // x.1 ≠ p.1} × Interval, Disk k),
      (∀ x, R (x, 0) = x.1) ∧
      (∀ x t, ‖x.1.1‖ = 1 → R (x, t) = x.1) ∧
      ∀ x, ‖(R (x, 1)).1‖ = 1 := by
  let s : Set (EuclideanSpace ℝ (Fin k)) := Metric.ball (-p.1) 1
  have hp : ‖p.1‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using p.2
  have hs₀ : s ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin k)) := by
    apply Metric.isOpen_ball.mem_nhds
    change ‖(0 : EuclideanSpace ℝ (Fin k)) - (-p.1)‖ < 1
    simpa only [zero_sub, neg_neg] using hp
  have hsc : Convex ℝ s := convex_ball _ _
  have hsa : Absorbent ℝ s := absorbent_nhds_zero hs₀
  have hsb : Bornology.IsVonNBounded ℝ s :=
    NormedSpace.isVonNBounded_of_isBounded ℝ Metric.isBounded_ball
  let Q := {x : Disk k // x.1 ≠ p.1}
  let a (x : Q) : EuclideanSpace ℝ (Fin k) := x.1.1 - p.1
  have ha : Continuous a :=
    (continuous_subtype_val.comp continuous_subtype_val).sub continuous_const
  have hane (x : Q) : a x ≠ 0 := sub_ne_zero.mpr x.2
  have hgpos (x : Q) : 0 < gauge s (a x) := (gauge_pos hsa hsb).mpr (hane x)
  let q (x : Q) : EuclideanSpace ℝ (Fin k) := (gauge s (a x))⁻¹ • a x
  have hq : Continuous q :=
    (((continuous_gauge hsc hs₀).comp ha).inv₀ (fun x => (hgpos x).ne')).smul ha
  have hqg (x : Q) : gauge s (q x) = 1 := by
    change gauge s ((gauge s (a x))⁻¹ • a x) = 1
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr (hgpos x).le), smul_eq_mul]
    exact inv_mul_cancel₀ (hgpos x).ne'
  have hqnorm (x : Q) : ‖p.1 + q x‖ = 1 := by
    have hx := (gauge_eq_one_iff_mem_frontier hsc hs₀).mp (hqg x)
    rw [show frontier s = Metric.sphere (-p.1) 1 from frontier_ball _ one_ne_zero]
      at hx
    change ‖q x - (-p.1)‖ = 1 at hx
    simpa only [sub_neg_eq_add, add_comm] using hx
  have hqfixed (x : Q) (hx : ‖x.1.1‖ = 1) : p.1 + q x = x.1.1 := by
    have hg : gauge s (a x) = 1 := by
      apply (gauge_eq_one_iff_mem_frontier hsc hs₀).mpr
      rw [show frontier s = Metric.sphere (-p.1) 1 from frontier_ball _ one_ne_zero]
      change ‖(x.1.1 - p.1) - (-p.1)‖ = 1
      simpa only [sub_neg_eq_add, sub_add_cancel] using hx
    simp only [q, hg, inv_one, one_smul, a, add_sub_cancel]
  let R : C(Q × Interval, Disk k) :=
    { toFun z := ⟨(1 - (z.2 : ℝ)) • z.1.1.1 + (z.2 : ℝ) • (p.1 + q z.1), by
        apply (convex_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) z.1.1.2
          (show p.1 + q z.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 by
            simpa only [Metric.mem_closedBall, dist_zero_right, hqnorm] using le_refl (1 : ℝ))
          (sub_nonneg.mpr z.2.2.2) z.2.2.1 (sub_add_cancel 1 (z.2 : ℝ))⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
          (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))).add
          ((continuous_subtype_val.comp continuous_snd).smul
            (continuous_const.add (hq.comp continuous_fst))) }
  refine ⟨R, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    simp [R]
  · intro x t hx
    apply Subtype.ext
    change (1 - (t : ℝ)) • x.1.1 + (t : ℝ) • (p.1 + q x) = x.1.1
    rw [hqfixed x hx, ← add_smul, sub_add_cancel, one_smul]
  · intro x
    simpa [R] using hqnorm x

/-- Closed disks of the selected cells cover a subcomplex. -/
lemma subcomplex_eq_closedCellUnion (A : Subcomplex X) :
    A.carrier = ⋃ d ∈ {d : Σ n, Cell X n | d.2 ∈ A.cells d.1}, closedCell X d.1 d.2 := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨c, z, rfl⟩ := mem_iUnion.mp hn
    exact mem_iUnion.mpr ⟨⟨n, c.1⟩, mem_iUnion.mpr ⟨c.2,
      ⟨interiorInclusion n z, rfl⟩⟩⟩
  · intro x hx
    obtain ⟨⟨n, c⟩, hd⟩ := mem_iUnion.mp hx
    obtain ⟨hc, z, rfl⟩ := mem_iUnion.mp hd
    exact selected_disk_mem A c hc z

lemma finiteSubcomplex_isCompact (A : Subcomplex X) (hA : A.IsFinite) :
    IsCompact A.carrier := by
  rw [subcomplex_eq_closedCellUnion]
  apply hA.isCompact_biUnion
  intro d _
  letI : CompactSpace (Disk d.1) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact isCompact_range (characteristic X d.1 d.2).continuous

lemma cellIndex_unique {d e : Σ n, Cell X n} {x : X}
    (hd : x ∈ openCell X d.1 d.2) (he : x ∈ openCell X e.1 e.2) : d = e :=
  CWStructure.disjoint_interiors.elim_set (mem_univ d) (mem_univ e) x hd he

lemma closedCell_subset_openCell_union_skeletonLT (n : ℕ) (c : Cell X n) :
    closedCell X n c ⊆ openCell X n c ∪ skeletonLT X n := by
  rintro _ ⟨z, rfl⟩
  rcases HomotopyExtension.disk_point_alternative z with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact Or.inr (CWStructure.boundary_lands n c (mem_univ w))
  · exact Or.inl ⟨w, rfl⟩

/-- Remove one cell of top dimension from a subcomplex. -/
def withoutTopCell (A : Subcomplex X) (k : ℕ) (c : Cell X k)
    (htop : ∀ m, (A.cells m).Nonempty → m ≤ k) : Subcomplex X where
  cells m := {d | d ∈ A.cells m ∧ (⟨m, d⟩ : Σ n, Cell X n) ≠ ⟨k, c⟩}
  contains_closures := by
    intro m d hd x hx
    have hA := A.contains_closures m d hd.1 hx
    have hnot : x ∉ openCell X k c := by
      intro hxc
      rw [P202.Topology.closureOpenCell m d] at hx
      rcases closedCell_subset_openCell_union_skeletonLT m d hx with hxd | hxs
      · exact hd.2 (cellIndex_unique hxd hxc)
      · exact (Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT k c)) hxc
          (P202.Topology.skeletonLT_mono (htop m ⟨d, hd.1⟩) hxs)
    obtain ⟨n, hn⟩ := mem_iUnion.mp hA
    obtain ⟨e, he⟩ := mem_iUnion.mp hn
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨e.1, e.2, by
      intro heq
      have hmem : x ∈ openCell X k c := by
        cases heq
        exact he
      exact hnot hmem⟩, he⟩⟩

lemma withoutTopCell_carrier (A : Subcomplex X) (k : ℕ) (c : Cell X k)
    (htop : ∀ m, (A.cells m).Nonempty → m ≤ k) :
    (withoutTopCell A k c htop).carrier = A.carrier \ openCell X k c := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨d, hd⟩ := mem_iUnion.mp hn
    exact ⟨mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨d.1, d.2.1⟩, hd⟩⟩,
      fun hc => d.2.2 (cellIndex_unique hd hc)⟩
  · rintro ⟨hx, hc⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨d, hd⟩ := mem_iUnion.mp hn
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨d.1, d.2, ?_⟩, hd⟩⟩
    intro heq
    apply hc
    cases heq
    exact hd

lemma withoutTopCell_isFinite (A : Subcomplex X) (hA : A.IsFinite)
    (k : ℕ) (c : Cell X k) (htop : ∀ m, (A.cells m).Nonempty → m ≤ k) :
    (withoutTopCell A k c htop).IsFinite :=
  hA.subset (fun _ hd => hd.1)

/-- Restricting a disjoint union to an open subset distributes over its summands. -/
def sigmaOpenRestriction {ι : Type u} {D : ι → Type v}
    [∀ i, TopologicalSpace (D i)] (s : Set (Σ i, D i)) (hs : IsOpen s) :
    (Σ i, {x : D i // (⟨i,x⟩ : Σ i, D i) ∈ s}) ≃ₜ s where
  toFun z := ⟨⟨z.1,z.2.1⟩,z.2.2⟩
  invFun z := ⟨z.1.1,⟨z.1.2,z.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_sigma fun i =>
    (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    rintro ⟨⟨i,x⟩,hx⟩
    have he : IsOpenEmbedding
        (fun y : {x : D i // (⟨i,x⟩ : Σ i, D i) ∈ s} =>
          (⟨⟨i,y.1⟩,y.2⟩ : s)) :=
      IsOpenEmbedding.sigmaMk.restrict (fun _ h => h) (hs.preimage continuous_sigmaMk)
    apply (he.continuousAt_iff (x := ⟨x,hx⟩)).mp
    exact continuous_sigmaMk.continuousAt

def sigmaHomeomorph {ι : Type u} {D E : ι → Type v}
    [∀ i, TopologicalSpace (D i)] [∀ i, TopologicalSpace (E i)]
    (e : ∀ i, D i ≃ₜ E i) : (Σ i, D i) ≃ₜ (Σ i, E i) where
  toEquiv := Equiv.sigmaCongrRight (fun i => (e i).toEquiv)
  continuous_toFun := continuous_sigma fun i => continuous_sigmaMk.comp (e i).continuous
  continuous_invFun := continuous_sigma fun i => continuous_sigmaMk.comp (e i).symm.continuous

variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- The selected characteristic disks, restricted off a point, still form a quotient. -/
lemma puncturedSubcomplexProjection_quotient (A : Subcomplex X) (a : X) :
    IsQuotientMap (fun z : (Σ n, Σ c : A.cells n,
      {x : Disk n // characteristic X n c.1 x ≠ a}) =>
      (⟨subcomplexProjection A ⟨z.1,z.2.1,z.2.2.1⟩,z.2.2.2⟩ :
        {x : A // x.1 ≠ a})) := by
  let s : Set A := {x | x.1 ≠ a}
  have hs : IsOpen s := isOpen_ne.preimage continuous_subtype_val
  let q := subcomplexProjection A
  have hq := (subcomplexProjection_quotient A).restrictPreimage_isOpen hs
  let e₁ := sigmaOpenRestriction (q ⁻¹' s) (hs.preimage (subcomplexProjection_quotient A).continuous)
  let e₂ : (Σ n, Σ c : A.cells n, {x : Disk n // characteristic X n c.1 x ≠ a}) ≃ₜ
      (Σ n, {z : (Σ c : A.cells n, Disk n) // (⟨n,z⟩ : _) ∈ q ⁻¹' s}) :=
    sigmaHomeomorph (fun n => sigmaOpenRestriction
      {z : (Σ c : A.cells n, Disk n) | characteristic X n z.1.1 z.2 ≠ a}
      (isOpen_ne.preimage (continuous_sigma fun c => (characteristic X n c.1).continuous)))
  exact hq.comp (e₁.isQuotientMap.comp e₂.isQuotientMap)

/-- The punctured top-cell deformation descends through all boundary identifications. -/
lemma puncturedSubcomplexDeformation (A : Subcomplex X) (k : ℕ) (c : Cell X k)
    (hc : c ∈ A.cells k) (htop : ∀ m, (A.cells m).Nonempty → m ≤ k)
    (p : OpenDisk k) :
    ∃ R : C({a : A // a.1 ≠ interiorMap X k c p} × Interval, A),
      (∀ a, R (a, 0) = a.1) ∧
      (∀ a t, a.1.1 ∉ openCell X k c → R (a, t) = a.1) ∧
      ∀ a, (R (a, 1)).1 ∈ (withoutTopCell A k c htop).carrier := by
  classical
  let a₀ := interiorMap X k c p
  let Q := {a : A // a.1 ≠ a₀}
  let L := {z : Disk k // z.1 ≠ p.1}
  obtain ⟨r, rzero, rfixed, rend⟩ := puncturedDiskDeformation k p
  let J : C(Disk k, A) := ⟨fun z => ⟨characteristic X k c z, selected_disk_mem A c hc z⟩,
    (characteristic X k c).continuous.subtype_mk _⟩
  let H : C(L × Interval, A) := J.comp r
  have Hzero (z : L) : H (z,0) = J z.1 := congrArg J (rzero z)
  have Hfixed (z : L) (t : Interval) (hz : ‖z.1.1‖ = 1) : H (z,t) = J z.1 :=
    congrArg J (rfixed z t hz)
  have Hnot (z : L) : (H (z,1)).1 ∉ openCell X k c := by
    have hz := rend z
    let w : Sphere k := ⟨(r (z,1)).1, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
    have hs : (H (z,1)).1 ∈ skeletonLT X k :=
      CWStructure.boundary_lands k c (mem_univ w)
    exact fun he => (Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT k c)) he hs
  let lift (z : Disk k) (hz : characteristic X k c z ≠ a₀) : L :=
    ⟨z, fun he => hz (congrArg (characteristic X k c) (Subtype.ext he))⟩
  let G (a : Q) : C(Interval, A) :=
    if ha : a.1.1 ∈ openCell X k c then
      H.curry (lift (interiorInclusion k ((cellHomeomorph k c).symm ⟨a.1.1,ha⟩)) (by
        have hval := congrArg Subtype.val ((cellHomeomorph k c).apply_symm_apply ⟨a.1.1,ha⟩)
        exact fun he => a.2 (hval.symm.trans he)))
    else ContinuousMap.const Interval a.1
  have Gtop (z : Disk k) (hz : characteristic X k c z ≠ a₀) :
      G ⟨J z,hz⟩ = H.curry (lift z hz) := by
    by_cases ha : characteristic X k c z ∈ openCell X k c
    · simp only [G, J, ContinuousMap.coe_mk, dite_eq_left ha]
      have hval := congrArg Subtype.val ((cellHomeomorph k c).apply_symm_apply
        ⟨characteristic X k c z,ha⟩)
      have heq : interiorInclusion k ((cellHomeomorph k c).symm
          ⟨characteristic X k c z,ha⟩) = z :=
        (disk_fibre_unique c c _ _ hval (fun hs =>
          (Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT k c))
            (mem_range_self ((cellHomeomorph k c).symm ⟨characteristic X k c z,ha⟩)) hs)).2
      exact congrArg H.curry (show lift (interiorInclusion k ((cellHomeomorph k c).symm
        ⟨characteristic X k c z,ha⟩)) _ = lift z hz from Subtype.ext heq)
    · simp only [G, J, ContinuousMap.coe_mk, dite_eq_right ha]
      have hzboundary : ‖z.1‖ = 1 := by
        rcases HomotopyExtension.disk_point_alternative z with ⟨w,rfl⟩ | ⟨w,rfl⟩
        · simpa only [boundaryInclusion, Metric.mem_sphere, dist_zero_right] using w.2
        · exact False.elim (ha ⟨w,rfl⟩)
      ext t
      exact congrArg Subtype.val (Hfixed (lift z hz) t hzboundary).symm
  have Gcont : Continuous G := by
    apply (puncturedSubcomplexProjection_quotient A a₀).continuous_iff.mpr
    apply continuous_sigma
    intro n
    apply continuous_sigma
    intro d
    by_cases heq : (⟨n,d.1⟩ : Σ m, Cell X m) = ⟨k,c⟩
    · obtain ⟨d,hd⟩ := d
      cases heq
      let j : {z : Disk k // characteristic X k d z ≠ a₀} → L := fun z => lift z.1 z.2
      have hj : Continuous j := continuous_subtype_val.subtype_mk _
      exact (H.curry.continuous.comp hj).congr (fun z => (Gtop z.1 z.2).symm)
    · have hnot (z : Disk n) : characteristic X n d.1 z ∉ openCell X k c := by
        intro hz
        rcases closedCell_subset_openCell_union_skeletonLT n d.1 ⟨z,rfl⟩ with hcell | hs
        · exact heq (cellIndex_unique hcell hz)
        · exact (Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT k c)) hz
            (P202.Topology.skeletonLT_mono (htop n ⟨d.1,d.2⟩) hs)
      exact ((ContinuousMap.continuous_const' : Continuous
        (ContinuousMap.const Interval : A → C(Interval,A))).comp
        (((characteristic X n d.1).continuous.comp continuous_subtype_val).subtype_mk
          (fun z => selected_disk_mem A d.1 d.2 z.1))).congr
        (fun z => by simp only [Function.comp_def, G, subcomplexProjection, dite_eq_right (hnot z.1)])
  let R : C(Q × Interval,A) := (⟨G,Gcont⟩ : C(Q,C(Interval,A))).uncurry
  refine ⟨R, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a.1.1 ∈ openCell X k c
    · obtain ⟨w,hw⟩ := ha
      have hz : characteristic X k c (interiorInclusion k w) ≠ a₀ := by
        intro he
        exact a.2 (hw.symm.trans he)
      have heq : (⟨J (interiorInclusion k w),hz⟩ : Q) = a := Subtype.ext (Subtype.ext hw)
      change G a 0 = a.1
      rw [← heq,Gtop]
      exact Hzero (lift (interiorInclusion k w) hz)
    · change G a 0 = a.1
      simp only [G,dite_eq_right ha,ContinuousMap.const_apply]
  · intro a t ha
    change G a t = a.1
    simp only [G,dite_eq_right ha,ContinuousMap.const_apply]
  · intro a
    rw [withoutTopCell_carrier]
    refine ⟨(R (a,1)).2,?_⟩
    by_cases ha : a.1.1 ∈ openCell X k c
    · obtain ⟨w,hw⟩ := ha
      have hz : characteristic X k c (interiorInclusion k w) ≠ a₀ := by
        intro he
        exact a.2 (hw.symm.trans he)
      have heq : (⟨J (interiorInclusion k w),hz⟩ : Q) = a := Subtype.ext (Subtype.ext hw)
      change (G a 1).1 ∉ _
      rw [← heq,Gtop]
      exact Hnot (lift (interiorInclusion k w) hz)
    · change (G a 1).1 ∉ _
      simpa only [G,dite_eq_right ha,ContinuousMap.const_apply] using ha


lemma topOpenCell_isOpen (A : Subcomplex X) (k : ℕ) (c : Cell X k)
    (htop : ∀ m, (A.cells m).Nonempty → m ≤ k) :
    IsOpen ((Subtype.val : A → X) ⁻¹' openCell X k c) := by
  have hc := (P202.Topology.subcomplexClosed (withoutTopCell A k c htop)).preimage
    (continuous_subtype_val : Continuous (Subtype.val : A → X))
  have heq : ((Subtype.val : A → X) ⁻¹' (withoutTopCell A k c htop).carrier) =
      ((Subtype.val : A → X) ⁻¹' openCell X k c)ᶜ := by
    ext x
    rw [withoutTopCell_carrier]
    simp only [mem_preimage, mem_sdiff, x.2, true_and, mem_compl_iff]
  rw [heq] at hc
  simpa only [compl_compl] using hc.isOpen_compl

def topCellChart (A : Subcomplex X) (k : ℕ) (c : Cell X k) (hc : c ∈ A.cells k) :
    EuclideanSpace ℝ (Fin k) ≃ₜ ((Subtype.val : A → X) ⁻¹' openCell X k c) := by
  have hmem (z : openCell X k c) : z.1 ∈ A.carrier :=
    mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨c, hc⟩, z.2⟩⟩
  let e : openCell X k c ≃ₜ ((Subtype.val : A → X) ⁻¹' openCell X k c) :=
    { toFun := fun z => ⟨⟨z.1, hmem z⟩, z.2⟩
      invFun := fun z => ⟨z.1.1, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk hmem).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact (Homeomorph.unitBall : EuclideanSpace ℝ (Fin k) ≃ₜ OpenDisk k).trans ((cellHomeomorph k c).trans e)

lemma avoidTopCell (A : Subcomplex X) (n k : ℕ) (hnk : n < k)
    (c : Cell X k) (hc : c ∈ A.cells k)
    (htop : ∀ m, (A.cells m).Nonempty → m ≤ k) (f : C(Disk n, A)) :
    ∃ (g : C(Disk n, A)) (H : C(Disk n × Interval, A)) (p : OpenDisk k),
      (∀ z, H (z, 0) = f z) ∧ (∀ z, H (z, 1) = g z) ∧
      (∀ z t, (f z).1 ∉ openCell X k c → H (z, t) = f z) ∧
      ∀ z, (g z).1 ≠ interiorMap X k c p := by
  let U : Set A := (Subtype.val : A → X) ⁻¹' openCell X k c
  obtain ⟨g, H, p, hzero, hone, hfix, hmiss⟩ := P202.Topology.avoidHigherCell
    n k hnk U (topOpenCell_isOpen A k c htop) (topCellChart A k c hc) f
  let q : OpenDisk k := (cellHomeomorph k c).symm ⟨p.1.1, p.2⟩
  refine ⟨g, H, q, hzero, hone, hfix, ?_⟩
  intro z heq
  apply hmiss z
  apply Subtype.ext
  exact heq.trans (congrArg Subtype.val ((cellHomeomorph k c).apply_symm_apply ⟨p.1.1, p.2⟩))

lemma removeTopCell_of_deformation (A : Subcomplex X) (n k : ℕ) (hnk : n < k)
    (c : Cell X k) (hc : c ∈ A.cells k)
    (htop : ∀ m, (A.cells m).Nonempty → m ≤ k)
    (deform : ∀ p : OpenDisk k,
      ∃ R : C({a : A // a.1 ≠ interiorMap X k c p} × Interval, A),
        (∀ a, R (a, 0) = a.1) ∧
        (∀ a t, a.1.1 ∉ openCell X k c → R (a, t) = a.1) ∧
        ∀ a, (R (a, 1)).1 ∈ (withoutTopCell A k c htop).carrier)
    (f : C(Disk n, A))
    (hb : ∀ z : Sphere n, (f (boundaryInclusion n z)).1 ∈ skeletonLT X n) :
    ∃ H : C(Disk n × Interval, A),
      (∀ z, H (z, 0) = f z) ∧
      (∀ z t, H (boundaryInclusion n z, t) = f (boundaryInclusion n z)) ∧
      ∀ z, (H (z, 1)).1 ∈ (withoutTopCell A k c htop).carrier := by
  obtain ⟨g, H, p, hzero, hone, hfix, hmiss⟩ := avoidTopCell A n k hnk c hc htop f
  have hbnot (z : Sphere n) : (f (boundaryInclusion n z)).1 ∉ openCell X k c := by
    intro hx
    exact (Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT k c)) hx
      (P202.Topology.skeletonLT_mono hnk.le (hb z))
  have hgb (z : Sphere n) : g (boundaryInclusion n z) = f (boundaryInclusion n z) :=
    (hone _).symm.trans (hfix _ 1 (hbnot z))
  obtain ⟨R, hRzero, hRfix, hRend⟩ := deform p
  let lift : C(Disk n, {a : A // a.1 ≠ interiorMap X k c p}) :=
    ⟨fun z => ⟨g z, hmiss z⟩, g.continuous.subtype_mk _⟩
  let K : C(Disk n × Interval, A) := R.comp (lift.prodMap (ContinuousMap.id Interval))
  let e : C(Disk n, A) :=
    ⟨fun z => K (z, 1), K.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let S : Set (Disk n) := range (boundaryInclusion n)
  let H₀ : f.HomotopyRel g S :=
    { toFun := fun z => H (z.2, z.1)
      continuous_toFun := H.continuous.comp continuous_swap
      map_zero_left := hzero
      map_one_left := hone
      prop' := by
        intro t z hz
        obtain ⟨w, rfl⟩ := hz
        exact hfix _ t (hbnot w) }
  let H₁ : g.HomotopyRel e S :=
    { toFun := fun z => K (z.2, z.1)
      continuous_toFun := K.continuous.comp continuous_swap
      map_zero_left := fun z => hRzero (lift z)
      map_one_left := fun _ => rfl
      prop' := by
        intro t z hz
        obtain ⟨w, rfl⟩ := hz
        apply hRfix
        change (g (boundaryInclusion n w)).1 ∉ openCell X k c
        rw [hgb w]
        exact hbnot w }
  let J := H₀.trans H₁
  refine ⟨⟨fun z => J (z.2, z.1), J.continuous.comp continuous_swap⟩,
    J.apply_zero, ?_, ?_⟩
  · intro z t
    exact J.eq_fst t ⟨z, rfl⟩
  · intro z
    change (J (1, z)).1 ∈ (withoutTopCell A k c htop).carrier
    rw [show J (1, z) = e z from J.apply_one z]
    exact hRend (lift z)

/-- A selected disk meeting the interior of a maximal cell has that cell's label. -/
lemma topCell_disk_index (A : Subcomplex X) (k : ℕ) (c : Cell X k)
    (htop : ∀ m, (A.cells m).Nonempty → m ≤ k)
    {n : ℕ} (d : Cell X n) (hd : d ∈ A.cells n)
    (z : Disk n) (w : OpenDisk k)
    (h : characteristic X n d z = interiorMap X k c w) :
    (⟨n, d⟩ : Σ m, Cell X m) = ⟨k, c⟩ := by
  have hw : interiorMap X k c w ∈ openCell X k c := ⟨w, rfl⟩
  rcases closedCell_subset_openCell_union_skeletonLT n d ⟨z, h⟩ with hz | hz
  · exact cellIndex_unique hz hw
  · exact False.elim ((Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT k c))
      hw (P202.Topology.skeletonLT_mono (htop n ⟨d, hd⟩) hz))

/-- The sole disk coordinate above an interior point is its interior coordinate. -/
lemma topCell_disk_coordinate (k : ℕ) (c : Cell X k) (z : Disk k) (w : OpenDisk k)
    (h : characteristic X k c z = interiorMap X k c w) :
    z = interiorInclusion k w := by
  have hnold : characteristic X k c z ∉ skeletonLT X k := by
    rw [h]
    exact Set.disjoint_left.mp (P202.Topology.openCellDisjointSkeletonLT k c) ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := interior_lift_of_not_old c z hnold
  have huw : u = w := (CWStructure.interior_embedding k c).injective (by
    change characteristic X k c (interiorInclusion k u) = interiorMap X k c w
    rw [hu, h])
  exact hu.symm.trans (congrArg (interiorInclusion k) huw)


section

lemma finiteSubcomplex_exists_topCell (A : Subcomplex Y) (hA : A.IsFinite)
    (d : Σ k, Cell Y k) (hd : d.2 ∈ A.cells d.1) :
    ∃ (k : ℕ) (c : Cell Y k), c ∈ A.cells k ∧ d.1 ≤ k ∧
      ∀ m, (A.cells m).Nonempty → m ≤ k := by
  let T : Set (Σ k, Cell Y k) := {e | e.2 ∈ A.cells e.1}
  obtain ⟨e, he, hmax⟩ := hA.toFinset.exists_max_image Sigma.fst
    ⟨d, hA.mem_toFinset.mpr hd⟩
  refine ⟨e.1, e.2, hA.mem_toFinset.mp he, hmax d (hA.mem_toFinset.mpr hd), ?_⟩
  rintro m ⟨c, hc⟩
  exact hmax ⟨m, c⟩ (hA.mem_toFinset.mpr hc)

lemma withoutTopCell_ncard_lt (A : Subcomplex Y) (hA : A.IsFinite)
    (k : ℕ) (c : Cell Y k) (hc : c ∈ A.cells k)
    (htop : ∀ m, (A.cells m).Nonempty → m ≤ k) :
    {d : Σ m, Cell Y m | d.2 ∈ (withoutTopCell A k c htop).cells d.1}.ncard <
      {d : Σ m, Cell Y m | d.2 ∈ A.cells d.1}.ncard := by
  have heq : {d : Σ m, Cell Y m | d.2 ∈ (withoutTopCell A k c htop).cells d.1} =
      {d : Σ m, Cell Y m | d.2 ∈ A.cells d.1} \ {⟨k, c⟩} := by
    ext d
    simp only [withoutTopCell, mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
  rw [heq]
  exact Set.ncard_sdiff_singleton_lt_of_mem hc hA

/-- Finite cell deletion assembles relative disk compression. -/
lemma diskCompression_of_removeTopCell
    (remove : ∀ (A : Subcomplex Y) (_hA : A.IsFinite) (n k : ℕ) (hnk : n < k)
      (c : Cell Y k) (_hc : c ∈ A.cells k)
      (htop : ∀ m, (A.cells m).Nonempty → m ≤ k) (f : C(Disk n, A)),
      (∀ z : Sphere n, (f (boundaryInclusion n z)).1 ∈ skeletonLT Y n) →
      ∃ H : C(Disk n × Interval, A),
        (∀ z, H (z, 0) = f z) ∧
        (∀ z t, H (boundaryInclusion n z, t) = f (boundaryInclusion n z)) ∧
        ∀ z, (H (z, 1)).1 ∈ (withoutTopCell A k c htop).carrier) :
    ∀ (n : ℕ) (f : C(Disk n, Y)),
      (∀ z : Sphere n, f (boundaryInclusion n z) ∈ skeletonLT Y n) →
      ∃ h : C(Disk n × Interval, Y),
        (∀ z, h (z, 0) = f z) ∧
        (∀ z t, h (boundaryInclusion n z, t) = f (boundaryInclusion n z)) ∧
        ∀ z, h (z, 1) ∈ skeletonLT Y (n + 1) := by
  classical
  intro n f hb
  have go : ∀ M : ℕ, ∀ (A : Subcomplex Y) (hA : A.IsFinite)
      (f : C(Disk n, Y)), range f ⊆ A.carrier →
      (∀ z : Sphere n, f (boundaryInclusion n z) ∈ skeletonLT Y n) →
      {d : Σ m, Cell Y m | d.2 ∈ A.cells d.1}.ncard = M →
      ∃ g : C(Disk n, Y), range g ⊆ skeletonLT Y (n + 1) ∧
        Nonempty (f.HomotopyRel g (range (boundaryInclusion n))) := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
      intro A hA f hf hb hM
      by_cases hhigh : ∃ d : Σ m, Cell Y m, d.2 ∈ A.cells d.1 ∧ n < d.1
      · obtain ⟨d, hd, hnd⟩ := hhigh
        obtain ⟨k, c, hc, hdk, htop⟩ := finiteSubcomplex_exists_topCell A hA d hd
        let fA : C(Disk n, A) :=
          ⟨fun z => ⟨f z, hf (mem_range_self z)⟩, f.continuous.subtype_mk _⟩
        obtain ⟨H, hH₀, hHfix, hH₁⟩ := remove A hA n k (hnd.trans_le hdk) c hc htop fA hb
        let g : C(Disk n, Y) :=
          ⟨fun z => (H (z, 1)).1,
            continuous_subtype_val.comp (H.continuous.comp
              (continuous_id.prodMk continuous_const))⟩
        let K : f.HomotopyRel g (range (boundaryInclusion n)) :=
          { toFun z := (H (z.2, z.1)).1
            continuous_toFun := continuous_subtype_val.comp (H.continuous.comp continuous_swap)
            map_zero_left z := congrArg Subtype.val (hH₀ z)
            map_one_left z := rfl
            prop' := by
              intro t z hz
              obtain ⟨w, rfl⟩ := hz
              exact congrArg Subtype.val (hHfix w t) }
        let B := withoutTopCell A k c htop
        have hB : B.IsFinite := withoutTopCell_isFinite A hA k c htop
        have hBg : range g ⊆ B.carrier := by
          rintro _ ⟨z, rfl⟩
          exact hH₁ z
        have hgb (z : Sphere n) : g (boundaryInclusion n z) ∈ skeletonLT Y n := by
          rw [← K.fst_eq_snd (mem_range_self z)]
          exact hb z
        have hlt : {d : Σ m, Cell Y m | d.2 ∈ B.cells d.1}.ncard < M := by
          rw [← hM]
          exact withoutTopCell_ncard_lt A hA k c hc htop
        obtain ⟨q, hq, ⟨L⟩⟩ := ih _ hlt B hB g hBg hgb rfl
        exact ⟨q, hq, ⟨K.trans L⟩⟩
      · refine ⟨f, ?_, ⟨ContinuousMap.HomotopyRel.refl f _⟩⟩
        intro y hy
        obtain ⟨m, hm⟩ := mem_iUnion.mp (hf hy)
        obtain ⟨c, hc⟩ := mem_iUnion.mp hm
        have hmn : m < n + 1 := by
          apply Nat.lt_succ_of_le
          exact le_of_not_gt (fun hnm => hhigh ⟨⟨m, c.1⟩, c.2, hnm⟩)
        exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn, mem_iUnion.mpr ⟨c.1, hc⟩⟩⟩
  letI : CompactSpace (Disk n) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨A, hA, hf⟩ := P202.Topology.compactImageFiniteSupport f
  obtain ⟨g, hg, ⟨H⟩⟩ := go _ A hA f hf hb rfl
  let K : C(Disk n × Interval, Y) :=
    ⟨fun z => H (z.2, z.1), H.continuous.comp continuous_swap⟩
  exact ⟨K, fun z => H.apply_zero z,
    fun z t => H.eq_fst t (mem_range_self z), fun z => (H.apply_one z) ▸ hg (mem_range_self z)⟩

end


/-- Relative compression of a source disk into the corresponding target skeleton. -/
lemma diskCompression (n : ℕ) (f : C(Disk n, Y))
    (hb : ∀ z : Sphere n, f (boundaryInclusion n z) ∈ skeletonLT Y n) :
    ∃ h : C(Disk n × Interval, Y),
      (∀ z, h (z, 0) = f z) ∧
      (∀ z t, h (boundaryInclusion n z, t) = f (boundaryInclusion n z)) ∧
      ∀ z, h (z, 1) ∈ skeletonLT Y (n + 1) := by
  exact diskCompression_of_removeTopCell (fun A _ n k hnk c hc htop f hb =>
    removeTopCell_of_deformation A n k hnk c hc htop
      (fun p => puncturedSubcomplexDeformation A k c hc htop p) f hb) n f hb

end P202.Topology.CellularApproximation

namespace P202.Topology

/-- Cellular approximation for arbitrary CW pairs and independent source and target universes. -/
theorem cellularApproximation :
    P202Specs.Topology.CellularApproximation.cellularApproximation.{u,v} := by
  intro X Y _ _ _ _ A f hA
  exact CellularApproximation.cellularApproximation_of_diskCompression
    CellularApproximation.diskCompression A f hA

theorem mapIntoSkeleton :
    P202Specs.Topology.CellularApproximation.mapIntoSkeleton.{u,v} :=
  CellularApproximation.mapIntoSkeleton_of_cellularApproximation cellularApproximation

theorem basedCellularApproximation :
    P202Specs.Topology.CellularApproximation.basedCellularApproximation.{u,v} :=
  CellularApproximation.basedCellularApproximation_of_cellularApproximation cellularApproximation

theorem basedMapIntoSkeleton :
    P202Specs.Topology.CellularApproximation.basedMapIntoSkeleton.{u,v} :=
  CellularApproximation.basedMapIntoSkeleton_of_basedCellularApproximation basedCellularApproximation

end P202.Topology

noncomputable section
open Set Topology P202.Cellular
namespace P202.Topology.CellularApproximation.Cylinder
variable {X : Type u} [TopologicalSpace X] [CWStructure X]

/-- Closedness in the ordinary product cylinder is detected on the products
of the interval with every characteristic disk. -/
lemma cylinderClosedTest (B : Set (Interval × X)) :
    IsClosed B ↔ ∀ n (c : Cell X n),
      IsClosed ((fun z : Interval × Disk n => (z.1, characteristic X n c z.2)) ⁻¹' B) := by
  constructor
  · intro h n c
    exact h.preimage (continuous_fst.prodMk ((characteristic X n c).continuous.comp continuous_snd))
  · intro h
    have hq := P202.Topology.quotientProductInterval (diskProjection X)
      P202.Topology.characteristicProjectionQuotient
    have hq' := (Homeomorph.prodComm X Interval).isQuotientMap.comp hq
    apply hq'.isCoinducing.isClosed_preimage.mp
    let e := Homeomorph.sigmaProdDistrib (X := fun n => Σ _ : Cell X n, Disk n)
      (Y := Interval)
    apply e.symm.isClosed_preimage.mp
    apply isClosed_sigma_iff.mpr
    intro n
    let e' := Homeomorph.sigmaProdDistrib (X := fun _ : Cell X n => Disk n)
      (Y := Interval)
    apply e'.symm.isClosed_preimage.mp
    apply isClosed_sigma_iff.mpr
    intro c
    exact (h n c).preimage continuous_swap

lemma cylinderWeakTopologyOfPrisms [CellStructure (Interval × X)]
    (e : ∀ n, Disk (n + 1) ≃ₜ (Interval × Disk n))
    (prism : ∀ n, Cell X n → Cell (Interval × X) (n + 1))
    (hp : ∀ n (c : Cell X n) z,
      characteristic (Interval × X) (n + 1) (prism n c) z =
        ((e n z).1, characteristic X n c (e n z).2)) :
    ∀ B : Set (Interval × X), IsClosed B ↔ ∀ n (c : Cell (Interval × X) n),
      IsClosed (characteristic (Interval × X) n c ⁻¹' B) := by
  intro B
  constructor
  · intro h n c
    exact h.preimage (characteristic (Interval × X) n c).continuous
  · intro h
    apply (cylinderClosedTest B).mpr
    intro n c
    apply (e n).isClosed_preimage.mp
    have heq : (e n) ⁻¹' ((fun z : Interval × Disk n =>
        (z.1, characteristic X n c z.2)) ⁻¹' B) =
        characteristic (Interval × X) (n + 1) (prism n c) ⁻¹' B := by
      ext z
      simp only [mem_preimage, hp]
    rw [heq]
    exact h (n + 1) (prism n c)

lemma cylinderClosureFinite [CellStructure (Interval × X)]
    (h0 h1 : ∀ n, Cell X n → Cell (Interval × X) n)
    (prism : ∀ n, Cell X n → Cell (Interval × X) (n + 1))
    (hop0 : ∀ n (c : Cell X n), openCell (Interval × X) n (h0 n c) =
      {0} ×ˢ openCell X n c)
    (hop1 : ∀ n (c : Cell X n), openCell (Interval × X) n (h1 n c) =
      {1} ×ˢ openCell X n c)
    (hopp : ∀ n (c : Cell X n), openCell (Interval × X) (n + 1) (prism n c) =
      {t : Interval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} ×ˢ openCell X n c)
    (hclosed : ∀ n (c : Cell (Interval × X) n), ∃ (m : ℕ) (d : Cell X m),
      closedCell (Interval × X) n c ⊆ univ ×ˢ closedCell X m d) :
    ∀ n (c : Cell (Interval × X) n), ∃ F : Finset (Σ m, Cell (Interval × X) m),
      closedCell (Interval × X) n c ⊆ ⋃ d ∈ F, openCell (Interval × X) d.1 d.2 := by
  classical
  intro n c
  obtain ⟨m, d, hcd⟩ := hclosed n c
  obtain ⟨F, hF⟩ := CWStructure.closure_finite m d
  let G : Finset (Σ m, Cell (Interval × X) m) :=
    F.biUnion (fun e => {⟨e.1, h0 e.1 e.2⟩, ⟨e.1, h1 e.1 e.2⟩,
      ⟨e.1 + 1, prism e.1 e.2⟩})
  refine ⟨G, ?_⟩
  intro z hz
  obtain ⟨e, he⟩ := mem_iUnion.mp (hF (hcd hz).2)
  obtain ⟨heF, hez⟩ := mem_iUnion.mp he
  have h0G : (⟨e.1, h0 e.1 e.2⟩ : Σ m, Cell (Interval × X) m) ∈ G := by
    apply Finset.mem_biUnion.mpr
    exact ⟨e, heF, by simp⟩
  have h1G : (⟨e.1, h1 e.1 e.2⟩ : Σ m, Cell (Interval × X) m) ∈ G := by
    apply Finset.mem_biUnion.mpr
    exact ⟨e, heF, by simp⟩
  have hpG : (⟨e.1 + 1, prism e.1 e.2⟩ : Σ m, Cell (Interval × X) m) ∈ G := by
    apply Finset.mem_biUnion.mpr
    exact ⟨e, heF, by simp⟩
  by_cases ht0 : z.1 = 0
  · refine mem_iUnion.mpr ⟨⟨e.1, h0 e.1 e.2⟩, mem_iUnion.mpr ⟨h0G, ?_⟩⟩
    rw [hop0]
    exact ⟨ht0, hez⟩
  · by_cases ht1 : z.1 = 1
    · refine mem_iUnion.mpr ⟨⟨e.1, h1 e.1 e.2⟩, mem_iUnion.mpr ⟨h1G, ?_⟩⟩
      rw [hop1]
      exact ⟨ht1, hez⟩
    · refine mem_iUnion.mpr ⟨⟨e.1 + 1, prism e.1 e.2⟩, mem_iUnion.mpr ⟨hpG, ?_⟩⟩
      rw [hopp]
      refine ⟨⟨?_, ?_⟩, hez⟩
      · exact lt_of_le_of_ne z.1.2.1 (fun h => ht0 (Subtype.ext h.symm))
      · exact lt_of_le_of_ne z.1.2.2 (fun h => ht1 (Subtype.ext h))

/-- A closed union of whole open cells is a subcomplex. -/
lemma exists_subcomplex_of_closed_cellUnion {Z : Type u} [TopologicalSpace Z]
    [CWStructure Z] (R : Set Z) (hR : IsClosed R)
    (hU : ∀ z ∈ R, ∃ (n : ℕ) (c : Cell Z n), z ∈ openCell Z n c ∧ openCell Z n c ⊆ R) :
    ∃ B : Subcomplex Z, B.carrier = R := by
  let B : Subcomplex Z :=
    { cells n := {c | openCell Z n c ⊆ R}
      contains_closures := by
        intro n c hc z hz
        have hzR : z ∈ R := closure_minimal hc hR hz
        obtain ⟨m, d, hzd, hdR⟩ := hU z hzR
        exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨⟨d, hdR⟩, hzd⟩⟩ }
  refine ⟨B, Subset.antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    obtain ⟨c, hc⟩ := mem_iUnion.mp hn
    exact c.2 hc
  · intro z hz
    obtain ⟨n, c, hzc, hcR⟩ := hU z hz
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨c, hcR⟩, hzc⟩⟩

lemma exists_cylinderRelativeSubcomplex [CWStructure (Interval × X)]
    (h0 h1 : ∀ n, Cell X n → Cell (Interval × X) n)
    (prism : ∀ n, Cell X n → Cell (Interval × X) (n + 1))
    (hop0 : ∀ n (c : Cell X n), openCell (Interval × X) n (h0 n c) =
      {0} ×ˢ openCell X n c)
    (hop1 : ∀ n (c : Cell X n), openCell (Interval × X) n (h1 n c) =
      {1} ×ˢ openCell X n c)
    (hopp : ∀ n (c : Cell X n), openCell (Interval × X) (n + 1) (prism n c) =
      {t : Interval | 0 < (t : ℝ) ∧ (t : ℝ) < 1} ×ˢ openCell X n c)
    (A : Subcomplex X) :
    ∃ B : Subcomplex (Interval × X), B.carrier = cylinderRelativeSet A := by
  have hR : IsClosed (cylinderRelativeSet A) := by
    have h0 : IsClosed {p : Interval × X | p.1 = 0} :=
      isClosed_eq continuous_fst continuous_const
    have h1 : IsClosed {p : Interval × X | p.1 = 1} :=
      isClosed_eq continuous_fst continuous_const
    have hA := (P202.Topology.subcomplexClosed A).preimage (continuous_snd :
      Continuous (Prod.snd : Interval × X → X))
    exact h0.union (h1.union hA)
  apply exists_subcomplex_of_closed_cellUnion (cylinderRelativeSet A) hR
  intro z hz
  have hsource : ∃ (n : ℕ) (c : Cell X n), z.2 ∈ openCell X n c := by
    have hzX : z.2 ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
      rw [CWStructure.cover]; trivial
    simpa only [mem_iUnion] using hzX
  by_cases ht0 : z.1 = 0
  · obtain ⟨n, c, hzc⟩ := hsource
    refine ⟨n, h0 n c, ?_, ?_⟩
    · rw [hop0]; exact ⟨ht0, hzc⟩
    · intro w hw
      rw [hop0] at hw
      exact Or.inl hw.1
  · by_cases ht1 : z.1 = 1
    · obtain ⟨n, c, hzc⟩ := hsource
      refine ⟨n, h1 n c, ?_, ?_⟩
      · rw [hop1]; exact ⟨ht1, hzc⟩
      · intro w hw
        rw [hop1] at hw
        exact Or.inr (Or.inl hw.1)
    · have hzA : z.2 ∈ A.carrier := hz.resolve_left ht0 |>.resolve_left ht1
      obtain ⟨n, hn⟩ := mem_iUnion.mp hzA
      obtain ⟨c, hzc⟩ := mem_iUnion.mp hn
      refine ⟨n + 1, prism n c.1, ?_, ?_⟩
      · rw [hopp]
        refine ⟨⟨?_, ?_⟩, hzc⟩
        · exact lt_of_le_of_ne z.1.2.1 (fun h => ht0 (Subtype.ext h.symm))
        · exact lt_of_le_of_ne z.1.2.2 (fun h => ht1 (Subtype.ext h))
      · intro w hw
        rw [hopp] at hw
        exact Or.inr (Or.inr (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨c, hw.2⟩⟩))

end P202.Topology.CellularApproximation.Cylinder


noncomputable section
open Set Topology
open P202.Cellular

namespace P202.Topology.CellularApproximation.Cylinder

lemma exists_disk_prism_ambient (n : ℕ) :
    ∃ e : EuclideanSpace ℝ (Fin (n+1)) ≃ₜ (ℝ × EuclideanSpace ℝ (Fin n)),
      e '' Metric.ball 0 1 = Metric.ball 0 1 ∧
      e '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  let L : EuclideanSpace ℝ (Fin (n+1)) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, Nat.add_comm])
  let S := L '' Metric.closedBall 0 1
  have hSc : Convex ℝ S := (convex_closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1).linear_image L.toLinearMap
  have hSk : IsCompact S := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (n+1))) 1).image L.continuous
  have hi : interior S = L '' Metric.ball 0 1 := by
    change interior (L.toHomeomorph '' Metric.closedBall 0 1) = _
    rw [← L.toHomeomorph.image_interior, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    rfl
  obtain ⟨h, ho, hc, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hSc
    (by rw [hi]; exact (Metric.nonempty_ball.mpr (by norm_num)).image _) hSk.isBounded
  refine ⟨L.toHomeomorph.trans h, ?_, ?_⟩
  · change (h ∘ L) '' Metric.ball 0 1 = _
    calc
      _ = h '' (L '' Metric.ball 0 1) := (image_image _ _ _).symm
      _ = _ := by rw [← hi, ho]
  · change (h ∘ L) '' Metric.closedBall 0 1 = _
    calc
      _ = h '' S := (image_image _ _ _).symm
      _ = _ := by rw [← hSk.isClosed.closure_eq, hc]

def closedUnitIntervalHomeomorph : (Metric.closedBall (0 : ℝ) 1) ≃ₜ Interval where
  toFun x := ⟨(x.1 + 1) / 2, by
    have hx : |x.1| ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using x.2
    rcases abs_le.mp hx with ⟨hl, hu⟩
    constructor <;> linarith⟩
  invFun t := ⟨2 * (t : ℝ) - 1, by
    have ht₀ := t.2.1
    have ht₁ := t.2.2
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    constructor <;> linarith⟩
  left_inv x := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def diskPrismOfAmbient (n : ℕ)
    (e : EuclideanSpace ℝ (Fin (n+1)) ≃ₜ (ℝ × EuclideanSpace ℝ (Fin n)))
    (he : e '' Metric.closedBall 0 1 = Metric.closedBall 0 1) :
    Disk (n+1) ≃ₜ (Interval × Disk n) :=
  (e.image _).trans ((Homeomorph.setCongr he).trans
    ((Homeomorph.setCongr (closedBall_prod_same 0 0 1).symm).trans
      ((Homeomorph.Set.prod _ _).trans
        (closedUnitIntervalHomeomorph.prodCongr (Homeomorph.refl _)))))

lemma diskPrismOfAmbient_interior (n : ℕ)
    (e : EuclideanSpace ℝ (Fin (n+1)) ≃ₜ (ℝ × EuclideanSpace ℝ (Fin n)))
    (he : e '' Metric.closedBall 0 1 = Metric.closedBall 0 1)
    (ho : e '' Metric.ball 0 1 = Metric.ball 0 1) (z : Disk (n+1)) :
    ‖z.1‖ < 1 ↔
      0 < ((diskPrismOfAmbient n e he z).1 : ℝ) ∧
      ((diskPrismOfAmbient n e he z).1 : ℝ) < 1 ∧
      ‖(diskPrismOfAmbient n e he z).2.1‖ < 1 := by
  have hmem : z.1 ∈ Metric.ball 0 1 ↔ e z.1 ∈ Metric.ball 0 1 := by
    rw [← ho, e.injective.mem_set_image]
  have hv₁ : ((diskPrismOfAmbient n e he z).1 : ℝ) = ((e z.1).1 + 1) / 2 := rfl
  have hv₂ : (diskPrismOfAmbient n e he z).2.1 = (e z.1).2 := rfl
  rw [hv₁, hv₂]
  simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
    max_lt_iff, abs_lt] at hmem
  rw [hmem]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨by linarith, by linarith, hc⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨by linarith, by linarith⟩, hc⟩

def prismHomeomorph (n : ℕ) : Disk (n+1) ≃ₜ (Interval × Disk n) :=
  diskPrismOfAmbient n (exists_disk_prism_ambient n).choose
    (exists_disk_prism_ambient n).choose_spec.2

lemma prismHomeomorph_interior (n : ℕ) (z : Disk (n+1)) :
    ‖z.1‖ < 1 ↔ 0 < ((prismHomeomorph n z).1 : ℝ) ∧
      ((prismHomeomorph n z).1 : ℝ) < 1 ∧ ‖(prismHomeomorph n z).2.1‖ < 1 :=
  diskPrismOfAmbient_interior n _ _ (exists_disk_prism_ambient n).choose_spec.1 z

variable (X : Type u) [TopologicalSpace X] [CWStructure X]

inductive CylinderCell : ℕ → Type u
  | horizontal (n : ℕ) (b : Bool) (c : Cell X n) : CylinderCell n
  | prism (n : ℕ) (c : Cell X n) : CylinderCell (n+1)

def endpoint (b : Bool) : Interval := if b then 1 else 0

def cylinderCharacteristic : (n : ℕ) → CylinderCell X n → C(Disk n, Interval × X)
  | _, .horizontal n b c => ⟨fun z => (endpoint b, characteristic X n c z),
      continuous_const.prodMk (characteristic X n c).continuous⟩
  | _, .prism n c =>
      ⟨fun z => ((prismHomeomorph n z).1, characteristic X n c (prismHomeomorph n z).2),
       ((prismHomeomorph n).continuous.fst).prodMk
         ((characteristic X n c).continuous.comp (prismHomeomorph n).continuous.snd)⟩

@[instance_reducible] def cylinderCellStructure : CellStructure (Interval × X) where
  Cell := CylinderCell X
  characteristic := cylinderCharacteristic X

local instance : CellStructure (Interval × X) := cylinderCellStructure X

lemma openCell_horizontal (n : ℕ) (b : Bool) (c : Cell X n) :
    openCell (Interval × X) n (CylinderCell.horizontal n b c) = {endpoint b} ×ˢ openCell X n c := by
  ext ⟨t, x⟩
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨congrArg Prod.fst hz |>.symm, ⟨z, congrArg Prod.snd hz⟩⟩
  · rintro ⟨ht, z, rfl⟩
    exact ⟨z, Prod.ext (mem_singleton_iff.mp ht).symm rfl⟩

lemma openCell_prism (n : ℕ) (c : Cell X n) :
    openCell (Interval × X) (n+1) (CylinderCell.prism n c) =
      Ioo (0 : Interval) 1 ×ˢ openCell X n c := by
  ext ⟨t, x⟩
  constructor
  · rintro ⟨z, hz⟩
    have hi := (prismHomeomorph_interior n (interiorInclusion (n+1) z)).mp
      (show ‖z.1‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using z.2)
    have ht : (prismHomeomorph n (interiorInclusion (n+1) z)).1 = t := congrArg Prod.fst hz
    have hx : characteristic X n c (prismHomeomorph n (interiorInclusion (n+1) z)).2 = x :=
      congrArg Prod.snd hz
    refine ⟨?_, ?_⟩
    · rw [← ht]
      exact ⟨hi.1, hi.2.1⟩
    · exact ⟨⟨(prismHomeomorph n (interiorInclusion (n+1) z)).2.1,
          by simpa only [Metric.mem_ball, dist_zero_right] using hi.2.2⟩, hx⟩
  · rintro ⟨ht, z, rfl⟩
    let p : Interval × Disk n := (t, interiorInclusion n z)
    have hp := (prismHomeomorph_interior n ((prismHomeomorph n).symm p)).mpr
      (by rw [Homeomorph.apply_symm_apply]
          exact ⟨ht.1, ht.2, by change ‖z.1‖ < 1; simpa only [Metric.mem_ball, dist_zero_right] using z.2⟩)
    let w : OpenDisk (n+1) := ⟨((prismHomeomorph n).symm p).1,
      by simpa only [Metric.mem_ball, dist_zero_right] using hp⟩
    refine ⟨w, ?_⟩
    change ((prismHomeomorph n (interiorInclusion (n+1) w)).1,
      characteristic X n c (prismHomeomorph n (interiorInclusion (n+1) w)).2) = _
    have hw : interiorInclusion (n+1) w = (prismHomeomorph n).symm p := rfl
    rw [hw, Homeomorph.apply_symm_apply]
    rfl

lemma closedCell_horizontal (n : ℕ) (b : Bool) (c : Cell X n) :
    closedCell (Interval × X) n (CylinderCell.horizontal n b c) =
      {endpoint b} ×ˢ closedCell X n c := by
  ext ⟨t, x⟩
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨(congrArg Prod.fst hz).symm, ⟨z, congrArg Prod.snd hz⟩⟩
  · rintro ⟨ht, z, rfl⟩
    exact ⟨z, Prod.ext (mem_singleton_iff.mp ht).symm rfl⟩

lemma closedCell_prism (n : ℕ) (c : Cell X n) :
    closedCell (Interval × X) (n+1) (CylinderCell.prism n c) =
      univ ×ˢ closedCell X n c := by
  ext ⟨t, x⟩
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨mem_univ t, ⟨(prismHomeomorph n z).2, congrArg Prod.snd hz⟩⟩
  · rintro ⟨_, z, rfl⟩
    refine ⟨(prismHomeomorph n).symm (t, z), ?_⟩
    change ((prismHomeomorph n ((prismHomeomorph n).symm (t,z))).1,
      characteristic X n c (prismHomeomorph n ((prismHomeomorph n).symm (t,z))).2) = _
    rw [Homeomorph.apply_symm_apply]

def prismInteriorParameter (n : ℕ) : OpenDisk (n+1) → Interval × OpenDisk n :=
  fun z => ((prismHomeomorph n (interiorInclusion (n+1) z)).1,
    ⟨(prismHomeomorph n (interiorInclusion (n+1) z)).2.1, by
      have hi := (prismHomeomorph_interior n (interiorInclusion (n+1) z)).mp
        (by change ‖z.1‖ < 1; simpa only [Metric.mem_ball, dist_zero_right] using z.2)
      simpa only [Metric.mem_ball, dist_zero_right] using hi.2.2⟩)

lemma interiorInclusion_embedding (n : ℕ) : IsEmbedding (interiorInclusion n) :=
  IsEmbedding.subtypeVal.codRestrict _ _

lemma prismInteriorParameter_continuous (n : ℕ) : Continuous (prismInteriorParameter n) := by
  have h := (prismHomeomorph n).continuous.comp (interiorInclusion_embedding n.succ).continuous
  exact h.fst.prodMk ((continuous_subtype_val.comp h.snd).subtype_mk _)

lemma prismInteriorParameter_embedding (n : ℕ) : IsEmbedding (prismInteriorParameter n) := by
  let g : Interval × OpenDisk n → Interval × Disk n := Prod.map id (interiorInclusion n)
  apply IsEmbedding.of_comp (prismInteriorParameter_continuous n)
    (show Continuous g from continuous_fst.prodMk ((interiorInclusion_embedding n).continuous.comp continuous_snd))
  exact (prismHomeomorph n).isEmbedding.comp (interiorInclusion_embedding (n+1))

lemma cylinder_interior_embedding :
    ∀ n (c : Cell (Interval × X) n), IsEmbedding (interiorMap (Interval × X) n c) := by
  intro n c
  change CylinderCell X n at c
  cases c with
  | horizontal n b c =>
      apply IsEmbedding.of_comp
        (show Continuous (interiorMap (Interval × X) n (CylinderCell.horizontal n b c)) from
          continuous_const.prodMk (CWStructure.interior_embedding n c).continuous)
        continuous_snd
      exact CWStructure.interior_embedding n c
  | prism n c =>
      exact ((IsEmbedding.id).prodMap (CWStructure.interior_embedding n c)).comp
        (prismInteriorParameter_embedding n)

lemma endpoint_injective : Function.Injective endpoint := by
  intro b d h
  cases b <;> cases d <;> simp_all [endpoint]

lemma cylinder_cell_unique {d e : Σ n, Cell (Interval × X) n} {p : Interval × X}
    (hd : p ∈ openCell (Interval × X) d.1 d.2)
    (he : p ∈ openCell (Interval × X) e.1 e.2) : d = e := by
  rcases d with ⟨n, d⟩
  rcases e with ⟨m, e⟩
  change CylinderCell X n at d
  change CylinderCell X m at e
  cases d with
  | horizontal n b c =>
      rw [openCell_horizontal] at hd
      cases e with
      | horizontal m b' c' =>
          rw [openCell_horizontal] at he
          have hb : b = b' := endpoint_injective
            ((mem_singleton_iff.mp hd.1).symm.trans (mem_singleton_iff.mp he.1))
          have hc : (⟨n,c⟩ : Σ n, Cell X n) = ⟨m,c'⟩ := cellIndex_unique hd.2 he.2
          subst b'
          exact congrArg (fun d : Σ n, Cell X n =>
            (⟨d.1, CylinderCell.horizontal d.1 b d.2⟩ : Σ n, Cell (Interval × X) n)) hc
      | prism m c' =>
          rw [openCell_prism] at he
          have hp := mem_singleton_iff.mp hd.1
          have ht := he.1
          rw [hp] at ht
          cases b <;> simp [endpoint] at ht
  | prism n c =>
      rw [openCell_prism] at hd
      cases e with
      | horizontal m b' c' =>
          rw [openCell_horizontal] at he
          have hp := mem_singleton_iff.mp he.1
          have ht := hd.1
          rw [hp] at ht
          cases b' <;> simp [endpoint] at ht
      | prism m c' =>
          rw [openCell_prism] at he
          have hc : (⟨n,c⟩ : Σ n, Cell X n) = ⟨m,c'⟩ := cellIndex_unique hd.2 he.2
          exact congrArg (fun d : Σ n, Cell X n =>
            (⟨d.1+1, CylinderCell.prism d.1 d.2⟩ : Σ n, Cell (Interval × X) n)) hc

lemma cylinder_disjoint : (univ : Set (Σ n, Cell (Interval × X) n)).PairwiseDisjoint
    (fun c => openCell (Interval × X) c.1 c.2) := by
  intro d _ e _ hne
  apply Set.disjoint_left.mpr
  exact fun p hd he => hne (cylinder_cell_unique X hd he)

lemma interval_cases (t : Interval) : t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : Interval) 1 := by
  by_cases h0 : t = 0
  · exact Or.inl h0
  by_cases h1 : t = 1
  · exact Or.inr (Or.inl h1)
  exact Or.inr (Or.inr ⟨lt_of_le_of_ne (show (0 : Interval) ≤ t from t.2.1) (Ne.symm h0),
    lt_of_le_of_ne (show t ≤ (1 : Interval) from t.2.2) h1⟩)

lemma cylinder_cover : ⋃ (n : ℕ) (c : Cell (Interval × X) n),
    openCell (Interval × X) n c = univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hp : p.2 ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c :=
    by rw [CWStructure.cover]; exact mem_univ _
  obtain ⟨n,c,hc⟩ := by simpa only [mem_iUnion] using hp
  rcases interval_cases p.1 with h | h | h
  · refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨CylinderCell.horizontal n false c, ?_⟩⟩
    rw [openCell_horizontal]
    exact ⟨h, hc⟩
  · refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨CylinderCell.horizontal n true c, ?_⟩⟩
    rw [openCell_horizontal]
    exact ⟨h, hc⟩
  · refine mem_iUnion.mpr ⟨n+1, mem_iUnion.mpr ⟨CylinderCell.prism n c, ?_⟩⟩
    rw [openCell_prism]
    exact ⟨h, hc⟩

lemma cylinder_skeleton (k : ℤ) : skeleton (Interval × X) k =
    ({0,1} ×ˢ skeleton X k) ∪ (univ ×ˢ skeleton X (k-1)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, hn, c, hc⟩ := by simpa only [skeleton, mem_iUnion] using hp
    change CylinderCell X n at c
    cases c with
    | horizontal n b c =>
        rw [openCell_horizontal] at hc
        apply Or.inl
        refine ⟨?_, mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, mem_iUnion.mpr ⟨c, hc.2⟩⟩⟩⟩
        have ht := mem_singleton_iff.mp hc.1
        cases b <;> simp_all [endpoint]
    | prism n c =>
        rw [openCell_prism] at hc
        apply Or.inr
        refine ⟨mem_univ _, mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨?_, mem_iUnion.mpr ⟨c, hc.2⟩⟩⟩⟩
        omega
  · intro hp
    rcases hp with ⟨ht,hx⟩ | ⟨_,hx⟩
    · obtain ⟨n, hn, c, hc⟩ := by simpa only [skeleton, mem_iUnion] using hx
      rcases (show p.1 = 0 ∨ p.1 = 1 by simpa only [mem_insert_iff, mem_singleton_iff] using ht) with h | h
      · refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn,
          mem_iUnion.mpr ⟨CylinderCell.horizontal n false c, ?_⟩⟩⟩
        rw [openCell_horizontal]
        exact ⟨h,hc⟩
      · refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn,
          mem_iUnion.mpr ⟨CylinderCell.horizontal n true c, ?_⟩⟩⟩
        rw [openCell_horizontal]
        exact ⟨h,hc⟩
    · obtain ⟨n, hn, c, hc⟩ := by simpa only [skeleton, mem_iUnion] using hx
      rcases interval_cases p.1 with h | h | h
      · refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨by omega,
          mem_iUnion.mpr ⟨CylinderCell.horizontal n false c, ?_⟩⟩⟩
        rw [openCell_horizontal]
        exact ⟨h,hc⟩
      · refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨by omega,
          mem_iUnion.mpr ⟨CylinderCell.horizontal n true c, ?_⟩⟩⟩
        rw [openCell_horizontal]
        exact ⟨h,hc⟩
      · refine mem_iUnion.mpr ⟨n+1, mem_iUnion.mpr ⟨by omega,
          mem_iUnion.mpr ⟨CylinderCell.prism n c, ?_⟩⟩⟩
        rw [openCell_prism]
        exact ⟨h,hc⟩

lemma skeletonLT_as_skeleton {Z : Type u} [TopologicalSpace Z] [CellStructure Z] (n : ℕ) :
    skeletonLT Z n = skeleton Z ((n : ℤ)-1) := by
  ext z
  simp only [skeletonLT, skeleton, mem_iUnion]
  constructor
  · rintro ⟨m,hm,c,hc⟩
    exact ⟨m,by omega,c,hc⟩
  · rintro ⟨m,hm,c,hc⟩
    exact ⟨m,by omega,c,hc⟩

lemma cylinder_boundary_lands : ∀ n (c : Cell (Interval × X) n),
    MapsTo (boundaryMap (Interval × X) n c) univ (skeletonLT (Interval × X) n) := by
  intro n c z _
  change CylinderCell X n at c
  cases c with
  | horizontal n b c =>
      have hz : boundaryMap X n c z ∈ skeletonLT X n := CWStructure.boundary_lands n c (mem_univ z)
      rw [skeletonLT_as_skeleton] at hz ⊢
      rw [cylinder_skeleton]
      apply Or.inl
      refine ⟨?_, hz⟩
      change endpoint b ∈ ({0,1} : Set Interval)
      cases b <;> simp [endpoint]
  | prism n c =>
      let p := prismHomeomorph n (boundaryInclusion (n+1) z)
      have hnz : ‖(boundaryInclusion (n+1) z).1‖ = 1 := by
        simpa only [boundaryInclusion, Metric.mem_sphere, dist_zero_right] using z.2
      have hnp : ¬ (0 < (p.1 : ℝ) ∧ (p.1 : ℝ) < 1 ∧ ‖p.2.1‖ < 1) := by
        intro h
        have hn := (prismHomeomorph_interior n (boundaryInclusion (n+1) z)).mpr h
        linarith
      rw [skeletonLT_as_skeleton, cylinder_skeleton]
      change (p.1, characteristic X n c p.2) ∈ _
      rcases interval_cases p.1 with h | h | h
      · apply Or.inl
        refine ⟨by simp [h], ?_⟩
        have hz := (diskToSkeleton X CWStructure.boundary_lands n c p.2).2
        change characteristic X n c p.2 ∈ skeletonLT X (n+1) at hz
        rw [skeletonLT_as_skeleton] at hz
        simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hz
      · apply Or.inl
        refine ⟨by simp [h], ?_⟩
        have hz := (diskToSkeleton X CWStructure.boundary_lands n c p.2).2
        change characteristic X n c p.2 ∈ skeletonLT X (n+1) at hz
        rw [skeletonLT_as_skeleton] at hz
        simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hz
      · have hp : ‖p.2.1‖ = 1 := le_antisymm
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.2)
          (le_of_not_gt (fun hh => hnp ⟨h.1,h.2,hh⟩))
        let q : Sphere n := ⟨p.2.1, by simpa only [Metric.mem_sphere, dist_zero_right] using hp⟩
        have hz := CWStructure.boundary_lands n c (mem_univ q)
        rw [skeletonLT_as_skeleton] at hz
        apply Or.inr
        refine ⟨mem_univ _, ?_⟩
        have hq : boundaryInclusion n q = p.2 := Subtype.ext rfl
        change characteristic X n c (boundaryInclusion n q) ∈ _ at hz
        rw [hq] at hz
        simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hz

end P202.Topology.CellularApproximation.Cylinder


noncomputable section
open Set Topology P202.Cellular
namespace P202.Topology.CellularApproximation.Cylinder
variable (X : Type u) [TopologicalSpace X] [CWStructure X]
local instance : CellStructure (Interval × X) := cylinderCellStructure X

lemma cylinder_closed_subset : ∀ n (c : Cell (Interval × X) n),
    ∃ (m : ℕ) (d : Cell X m),
      closedCell (Interval × X) n c ⊆ univ ×ˢ closedCell X m d := by
  intro n c
  change CylinderCell X n at c
  cases c with
  | horizontal n b c =>
      refine ⟨n,c,?_⟩
      rw [closedCell_horizontal]
      exact Set.prod_mono (subset_univ _) Subset.rfl
  | prism n c =>
      exact ⟨n,c,(closedCell_prism X n c).subset⟩

@[instance_reducible] def cylinderCWStructure : CWStructure (Interval × X) :=
  P202.Topology.cwStructureOfWeak (cylinder_interior_embedding X) (cylinder_disjoint X)
    (cylinder_cover X) (cylinder_boundary_lands X)
    (cylinderClosureFinite
      (fun n c => CylinderCell.horizontal n false c)
      (fun n c => CylinderCell.horizontal n true c)
      (fun n c => CylinderCell.prism n c)
      (fun n c => openCell_horizontal X n false c)
      (fun n c => openCell_horizontal X n true c)
      (fun n c => openCell_prism X n c)
      (cylinder_closed_subset X))
    (cylinderWeakTopologyOfPrisms prismHomeomorph (fun n c => CylinderCell.prism n c)
      (by intros; rfl))

local instance : CWStructure (Interval × X) := cylinderCWStructure X

lemma cylinderCW_skeleton (k : ℤ) : skeleton (Interval × X) k =
    ({0,1} ×ˢ skeleton X k) ∪ (univ ×ˢ skeleton X (k-1)) :=
  cylinder_skeleton X k

lemma cylinderCW_relativeSubcomplex (A : Subcomplex X) :
    ∃ B : Subcomplex (Interval × X), B.carrier = cylinderRelativeSet A :=
  exists_cylinderRelativeSubcomplex
    (fun n c => CylinderCell.horizontal n false c)
    (fun n c => CylinderCell.horizontal n true c)
    (fun n c => CylinderCell.prism n c)
    (fun n c => openCell_horizontal X n false c)
    (fun n c => openCell_horizontal X n true c)
    (fun n c => openCell_prism X n c) A

end P202.Topology.CellularApproximation.Cylinder

namespace P202.Topology.CellularApproximation
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CWStructure X] [CWStructure Y]

lemma homotopyIntoSkeleton_forCylinder
    (approx : P202Specs.Topology.CellularApproximation.cellularApproximation.{u,v})
    [CWStructure (Interval × X)]
    (hsk : ∀ k : ℤ, skeleton (Interval × X) k =
      ({0, 1} ×ˢ skeleton X k) ∪ (univ ×ˢ skeleton X (k - 1)))
    (n : ℕ) (A : Subcomplex X) (B : Subcomplex (Interval × X))
    (hB : B.carrier = cylinderRelativeSet A)
    (f₀ f₁ : C(X, Y)) (H : f₀.Homotopy f₁)
    (hdim : HasDimensionLE X n) (hf₀ : IsCellular f₀) (hf₁ : IsCellular f₁)
    (hfix : ∀ t (a : A), H (t, a.1) = f₀ a.1) :
    ∃ K : f₀.Homotopy f₁,
      (∀ t (a : A), K (t, a.1) = f₀ a.1) ∧
      range K ⊆ skeleton Y ((n + 1 : ℕ) : ℤ) ∧
      Nonempty (H.toContinuousMap.HomotopyRel K.toContinuousMap (cylinderRelativeSet A)) := by
  have hproj (m : ℕ) (p : Interval × X) (hp : p ∈ skeleton (Interval × X) (m : ℤ)) :
      p.2 ∈ skeleton X (m : ℤ) := by
    rw [hsk] at hp
    rcases hp with hp | hp
    · exact hp.2
    · exact skeleton_mono (by omega : (m : ℤ) - 1 ≤ m) hp.2
  have hcyl : HasDimensionLE (Interval × X) (n + 1) := by
    apply eq_univ_of_forall
    intro p
    rw [hsk]
    refine Or.inr ⟨mem_univ _, ?_⟩
    have hp : p.2 ∈ skeleton X (n : ℤ) := hdim ▸ mem_univ _
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hp
  have hcell : IsCellularOn H.toContinuousMap B := by
    intro m p hp
    have hx := hproj m p hp.2
    have hz : p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ A.carrier := by
      simpa only [hB, cylinderRelativeSet, mem_ofPred_eq] using hp.1
    rcases hz with ht | ht | hxA
    · obtain ⟨t, x⟩ := p
      simp only at ht hx ⊢
      subst t
      change H (0, x) ∈ _
      rw [H.apply_zero]
      exact hf₀ m hx
    · obtain ⟨t, x⟩ := p
      simp only at ht hx ⊢
      subst t
      change H (1, x) ∈ _
      rw [H.apply_one]
      exact hf₁ m hx
    · change H (p.1, p.2) ∈ _
      rw [hfix p.1 ⟨p.2, hxA⟩]
      exact hf₀ m hx
  obtain ⟨g, hg, ⟨G⟩⟩ := approx B H.toContinuousMap hcell
  have hG (p : Interval × X) (hp : p ∈ cylinderRelativeSet A) : g p = H p := by
    exact (G.fst_eq_snd (hB.symm ▸ hp)).symm
  let K : f₀.Homotopy f₁ :=
    { toContinuousMap := g
      map_zero_left x := (hG (0, x) (Or.inl rfl)).trans (H.apply_zero x)
      map_one_left x := (hG (1, x) (Or.inr (Or.inl rfl))).trans (H.apply_one x) }
  refine ⟨K, ?_, ?_, ?_⟩
  · intro t a
    exact (hG (t, a.1) (Or.inr (Or.inr a.2))).trans (hfix t a)
  · exact cellular_range_subset_skeleton (n + 1) g hg hcyl
  · simpa only [hB] using (show Nonempty (H.toContinuousMap.HomotopyRel g B.carrier) from ⟨G⟩)

end P202.Topology.CellularApproximation


namespace P202.Topology

/-- Move a homotopy into the next skeleton while fixing both ends and the specified subcomplex. -/
theorem homotopyIntoSkeleton :
    P202Specs.Topology.CellularApproximation.homotopyIntoSkeleton.{u,v} := by
  intro X Y _ _ _ _ n A f₀ f₁ H hdim hf₀ hf₁ hfix
  letI := CellularApproximation.Cylinder.cylinderCWStructure X
  obtain ⟨B,hB⟩ := CellularApproximation.Cylinder.cylinderCW_relativeSubcomplex X A
  exact CellularApproximation.homotopyIntoSkeleton_forCylinder cellularApproximation
    (CellularApproximation.Cylinder.cylinderCW_skeleton X) n A B hB f₀ f₁ H hdim hf₀ hf₁ hfix

theorem basedHomotopyIntoSkeleton :
    P202Specs.Topology.CellularApproximation.basedHomotopyIntoSkeleton.{u,v} :=
  CellularApproximation.basedHomotopyIntoSkeleton_of_homotopyIntoSkeleton homotopyIntoSkeleton

end P202.Topology
