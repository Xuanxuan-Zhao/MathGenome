import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SmoothSurfaceDouble
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Piecewise
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Atlases
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.Collar

set_option autoImplicit false
noncomputable section
open Set Topology Filter
open scoped ContDiff
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.BoundaryData SmoothManifolds.CollarData
open P202Specs.SmoothSurfaceDouble
universe u
namespace P202.SmoothSurfaceDouble
open private SmoothManifolds.euclideanInteriorChart
  SmoothManifolds.euclideanInteriorChart_val SmoothManifolds.euclideanInteriorChart_source
  from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
variable {M : Type u} [TopologicalSpace M]

omit [TopologicalSpace M] in
theorem copy_eq_iff (B : Set M) (s t : Bool) (x y : M) :
    copy B s x = copy B t y ↔ x = y ∧ (s = t ∨ x ∈ B) := Quotient.eq

theorem copy_injective (B : Set M) (s : Bool) : Function.Injective (copy B s) := by
  intro x y h
  exact ((copy_eq_iff B s s x y).mp h).1

theorem continuous_copy (B : Set M) (s : Bool) : Continuous (copy B s) :=
  continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)

theorem continuous_fold (B : Set M) : Continuous (fold B) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact continuous_snd

theorem copy_mem_side (B : Set M) (s t : Bool) (x : M) :
    copy B t x ∈ side B s ↔ t = s ∧ x ∉ B := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨rfl, h⟩ := (copy_eq_iff B s t y x).mp hxy
    exact ⟨h.elim Eq.symm (fun hB => False.elim (hy hB)), hy⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, hx, rfl⟩

theorem isOpen_side (B : Set M) (hB : IsClosed B) (s : Bool) : IsOpen (side B s) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  have h : IsOpen ({s} ×ˢ Bᶜ : Set (Bool × M)) :=
    (isOpen_discrete _).prod hB.isOpen_compl
  convert h using 1
  ext x
  exact copy_mem_side B s x.1 x.2

theorem disjoint_side (B : Set M) {s t : Bool} (hst : s ≠ t) :
    Disjoint (side B s) (side B t) := by
  apply Set.disjoint_left.mpr
  intro q hs ht
  induction q using Quotient.inductionOn with
  | h x =>
    have hxs := ((copy_mem_side B s x.1 x.2).mp hs).1
    have hxt := ((copy_mem_side B t x.1 x.2).mp ht).1
    exact hst (hxs.symm.trans hxt)

theorem double_t2 [T2Space M] (B : Set M) (hB : IsClosed B) : T2Space (Double B) := by
  constructor
  intro a b hab
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
      by_cases hxy : x.2 = y.2
      · have hsign : x.1 ≠ y.1 := by
          intro hs
          exact hab (Quotient.sound ⟨hxy, Or.inl hs⟩)
        have hxB : x.2 ∉ B := by
          intro hx
          exact hab (Quotient.sound ⟨hxy, Or.inr hx⟩)
        have hyB : y.2 ∉ B := hxy ▸ hxB
        exact ⟨side B x.1, side B y.1, isOpen_side B hB x.1,
          isOpen_side B hB y.1, (copy_mem_side B x.1 x.1 x.2).mpr ⟨rfl, hxB⟩,
          (copy_mem_side B y.1 y.1 y.2).mpr ⟨rfl, hyB⟩, disjoint_side B hsign⟩
      · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hxy
        exact ⟨fold B ⁻¹' U, fold B ⁻¹' V,
          hU.preimage (continuous_fold B), hV.preimage (continuous_fold B),
          hx, hy, hUV.preimage _⟩

theorem double_compact [CompactSpace M] (B : Set M) : CompactSpace (Double B) := inferInstance

theorem copy_closedEmbedding [T2Space M] [CompactSpace M]
    (B : Set M) (hB : IsClosed B) (s : Bool) : IsClosedEmbedding (copy B s) := by
  let := double_t2 B hB
  exact (continuous_copy B s).isClosedEmbedding (copy_injective B s)


omit [TopologicalSpace M] in
@[simp] theorem fold_copy (B : Set M) (s : Bool) (x : M) :
    fold B (copy B s x) = x := rfl

@[simp] theorem copy_eq_self_iff (B : Set M) (s t : Bool) (x : M) :
    copy B s x = copy B t x ↔ s = t ∨ x ∈ B := by
  simp [copy_eq_iff]

omit [TopologicalSpace M] in
theorem copies_cover (B : Set M) :
    range (copy B false) ∪ range (copy B true) = univ := by
  apply eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    rcases x with ⟨s,x⟩
    cases s
    · exact Or.inl ⟨x,rfl⟩
    · exact Or.inr ⟨x,rfl⟩

theorem copy_boundary_eq (B : Set M) (s t : Bool) (x : B) :
    copy B s x.val = copy B t x.val :=
  (copy_eq_self_iff B s t x.val).mpr (Or.inr x.property)

@[simp] theorem copy_mem_seam (B : Set M) (s : Bool) (x : M) :
    copy B s x ∈ seam B ↔ x ∈ B := by
  constructor
  · rintro ⟨y,hy,h⟩
    exact ((copy_eq_iff B false s y x).mp h).1 ▸ hy
  · intro hx
    exact ⟨x,hx,copy_boundary_eq B false s ⟨x,hx⟩⟩

theorem copies_intersect (B : Set M) :
    range (copy B false) ∩ range (copy B true) = seam B := by
  ext q
  constructor
  · rintro ⟨⟨x,rfl⟩,⟨y,hy⟩⟩
    have h := (copy_eq_iff B true false y x).mp hy
    have hx : x ∈ B := h.1 ▸ h.2.resolve_left (by decide)
    exact (copy_mem_seam B false x).mpr hx
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,rfl⟩,⟨x,copy_boundary_eq B true false ⟨x,hx⟩⟩⟩

@[simp] theorem preimage_seam (B : Set M) (s : Bool) :
    copy B s ⁻¹' seam B = B := by
  ext x
  exact copy_mem_seam B s x

omit [TopologicalSpace M] in
theorem seam_eq_range (B : Set M) : seam B = range (seamMap B) := by
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,rfl⟩

theorem seam_eq_preimage (B : Set M) : seam B = fold B ⁻¹' B := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => exact copy_mem_seam B x.1 x.2

theorem isClosed_seam (B : Set M) (hB : IsClosed B) : IsClosed (seam B) := by
  rw [seam_eq_preimage]
  exact hB.preimage (continuous_fold B)

theorem seamMap_closedEmbedding [T2Space M] [CompactSpace M]
    (B : Set M) (hB : IsClosed B) : IsClosedEmbedding (seamMap B) :=
  (copy_closedEmbedding B hB false).comp hB.isClosedEmbedding_subtypeVal

/-- No assumptions about connectedness, nonemptiness or boundary model. -/
theorem surface_topology : Expected.topology.{u} := by
  intro kind M _ _ S
  let := S.topologicalManifold.hausdorff
  have hB := SmoothManifolds.isClosed_intrinsicBoundary S
  exact ⟨double_t2 _ hB, double_compact _, fun s => copy_closedEmbedding _ hB s,
    copies_cover _, copies_intersect _⟩

/-- The induced boundary is already compact and has finitely many components;
this does not require a circle classification or any finite interval cutting. -/
theorem boundary_finite_components {kind : ModelKind} [CompactSpace M]
    (S : SmoothManifold 2 kind M)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) :
    CompactSpace (intrinsicBoundary S) ∧
      Finite (ConnectedComponents (intrinsicBoundary S)) := by
  let := isCompact_iff_compactSpace.mp (SmoothManifolds.isClosed_intrinsicBoundary S).isCompact
  let := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace B.topologicalManifold
  exact ⟨inferInstance, inferInstance⟩

section SignedCollarTopology
variable {kind : ModelKind} {S : SmoothManifold 2 kind M}

/-- A collar meets the intrinsic boundary exactly at time zero. -/
theorem collar_mem_boundary_iff (C : SmoothCollar S) (q : intrinsicBoundary S)
    (t : CollarTime) : (C.toHomeomorph (q,t)).val ∈ intrinsicBoundary S ↔ t.val = 0 := by
  constructor
  · intro hx
    let r : intrinsicBoundary S := ⟨(C.toHomeomorph (q,t)).val,hx⟩
    have h : C.toHomeomorph (r,timeZero) = C.toHomeomorph (q,t) :=
      Subtype.ext (C.zero_section r)
    exact (congrArg (fun z : CollarSource S => z.2.val) (C.toHomeomorph.injective h)).symm
  · intro ht
    have htime : t = timeZero := Subtype.ext ht
    rw [htime, C.zero_section]
    exact q.property

def absoluteTime (t : SignedTime) : CollarTime :=
  ⟨|t.val|, abs_nonneg _, abs_lt.mpr t.property⟩

@[simp] theorem absoluteTime_signedTime (s : Bool) (t : CollarTime) :
    absoluteTime (signedTime s t) = t := by
  apply Subtype.ext
  cases s <;> simp [absoluteTime, signedTime, sign, abs_of_nonneg t.property.1]

theorem continuous_absoluteTime : Continuous absoluteTime :=
  (continuous_subtype_val.abs).subtype_mk _

/-- The actual folded collar, with its given open-subspace topology. -/
def bicollarForward (C : SmoothCollar S) (x : intrinsicBoundary S × SignedTime) :
    (fold (intrinsicBoundary S) ⁻¹' C.neighborhood) :=
  ⟨if 0 ≤ x.2.val then
    copy (intrinsicBoundary S) true (C.toHomeomorph (x.1,absoluteTime x.2)).val
  else copy (intrinsicBoundary S) false (C.toHomeomorph (x.1,absoluteTime x.2)).val,
    by split <;> exact (C.toHomeomorph _).property⟩

theorem bicollarForward_signedTime (C : SmoothCollar S) (s : Bool)
    (q : intrinsicBoundary S) (t : CollarTime) :
    (bicollarForward C (q,signedTime s t)).val =
      copy (intrinsicBoundary S) s (C.toHomeomorph (q,t)).val := by
  simp only [bicollarForward, absoluteTime_signedTime]
  cases s
  · by_cases ht : t.val = 0
    · have htime : t = timeZero := Subtype.ext ht
      subst t
      simp only [signedTime, sign, Bool.false_eq_true, ↓reduceIte, timeZero, mul_zero,
        le_refl]
      change copy (intrinsicBoundary S) true (C.toHomeomorph (q,timeZero)).val =
        copy (intrinsicBoundary S) false (C.toHomeomorph (q,timeZero)).val
      rw [C.zero_section]
      exact copy_boundary_eq _ true false q
    · have hn : ¬ 0 ≤ (signedTime false t).val := by
        simpa [signedTime, sign] using (neg_neg_of_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)))
      simp only [hn, ↓reduceIte]
  · have hp : 0 ≤ (signedTime true t).val := by simpa [signedTime,sign] using t.property.1
    simp only [hp, ↓reduceIte]

theorem continuous_bicollarForward (C : SmoothCollar S) : Continuous (bicollarForward C) := by
  apply Continuous.subtype_mk
  let f : intrinsicBoundary S × SignedTime → M :=
    fun x => (C.toHomeomorph (x.1,absoluteTime x.2)).val
  have hf : Continuous f := continuous_subtype_val.comp
    (C.toHomeomorph.continuous.comp
      (continuous_fst.prodMk (continuous_absoluteTime.comp continuous_snd)))
  apply (continuous_copy _ true |>.comp hf).if ?_ (continuous_copy _ false |>.comp hf)
  intro x hx
  have hz : x.2.val = 0 :=
    (frontier_le_subset_eq continuous_const
      (continuous_subtype_val.comp continuous_snd) hx).symm
  have htime : absoluteTime x.2 = timeZero := Subtype.ext (by simp [absoluteTime,hz,timeZero])
  dsimp [f]
  rw [htime,C.zero_section]
  exact copy_boundary_eq _ true false x.1

/-- Construct the bicollar by descent of the signed inverse coordinates through
an open restriction of the actual quotient map. This also handles the empty
boundary: all domains involved are then empty. -/
theorem exists_signedCollar (C : SmoothCollar S) : Nonempty (SignedCollar C) := by
  classical
  let B := intrinsicBoundary S
  let U : Set (Double B) := fold B ⁻¹' C.neighborhood
  have hU : IsOpen U := C.isOpen_neighborhood.preimage (continuous_fold B)
  let π : Bool × M → Double B := Quotient.mk (doubleSetoid B)
  let r : (π ⁻¹' U) → U := U.restrictPreimage π
  have hr : IsQuotientMap r := isQuotientMap_quotient_mk'.restrictPreimage_isOpen hU
  let n : (π ⁻¹' U) → C.neighborhood := fun a => ⟨a.val.2,a.property⟩
  have hn : Continuous n := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  let g : (π ⁻¹' U) → B × SignedTime := fun a =>
    let z := C.toHomeomorph.symm (n a)
    (z.1,signedTime a.val.1 z.2)
  have hg : Continuous g := by
    apply Continuous.prodMk
    · exact continuous_fst.comp (C.toHomeomorph.symm.continuous.comp hn)
    · apply Continuous.subtype_mk
      exact ((continuous_of_discreteTopology : Continuous sign).comp
        (continuous_fst.comp continuous_subtype_val)).mul
        (continuous_subtype_val.comp (continuous_snd.comp
          (C.toHomeomorph.symm.continuous.comp hn)))
  have hfactor : g.FactorsThrough r := by
    intro a b hab
    have h := (copy_eq_iff B a.val.1 b.val.1 a.val.2 b.val.2).mp
      (congrArg Subtype.val hab)
    have hnb : n a = n b := Subtype.ext h.1
    dsimp [g]
    rw [hnb]
    rcases h.2 with hs | hx
    · rw [hs]
    · have hz : (C.toHomeomorph.symm (n b)).2.val = 0 := by
        apply (collar_mem_boundary_iff C _ _).mp
        rw [C.toHomeomorph.apply_symm_apply]
        change b.val.2 ∈ B
        exact h.1 ▸ hx
      apply Prod.ext
      · rfl
      apply Subtype.ext
      simp only [signedTime,hz,mul_zero]
  let inv : U → B × SignedTime := fun y => g (Function.surjInv hr.surjective y)
  have hinvr (a : π ⁻¹' U) : inv (r a) = g a :=
    hfactor (Function.surjInv_eq hr.surjective (r a))
  have hinv : Continuous inv := hr.continuous_iff.mpr (by
    convert hg using 1
    funext a
    exact hinvr a)
  have hright (a : π ⁻¹' U) : bicollarForward C (g a) = r a := by
    apply Subtype.ext
    dsimp only [g]
    rw [bicollarForward_signedTime,C.toHomeomorph.apply_symm_apply]
    rfl
  have hleft (x : B × SignedTime) : inv (bicollarForward C x) = x := by
    let s : Bool := decide (0 ≤ x.2.val)
    let a : π ⁻¹' U := ⟨(s,(C.toHomeomorph (x.1,absoluteTime x.2)).val),
      (C.toHomeomorph _).property⟩
    have ha : r a = bicollarForward C x := by
      apply Subtype.ext
      change copy B (decide (0 ≤ x.2.val)) _ =
        if 0 ≤ x.2.val then copy B true _ else copy B false _
      by_cases hx : 0 ≤ x.2.val <;> simp [hx]
    rw [← ha,hinvr]
    change ( (C.toHomeomorph.symm (C.toHomeomorph (x.1,absoluteTime x.2))).1,
      signedTime s (C.toHomeomorph.symm (C.toHomeomorph (x.1,absoluteTime x.2))).2) = x
    rw [C.toHomeomorph.symm_apply_apply]
    apply Prod.ext
    · rfl
    apply Subtype.ext
    by_cases hx : 0 ≤ x.2.val
    · simp [s,signedTime,sign,absoluteTime,hx,abs_of_nonneg hx]
    · simp [s,signedTime,sign,absoluteTime,hx,abs_of_neg (lt_of_not_ge hx)]
  have hright' : Function.RightInverse inv (bicollarForward C) := by
    intro y
    obtain ⟨a,rfl⟩ := hr.surjective y
    rw [hinvr,hright]
  let h : (B × SignedTime) ≃ₜ U := {
    toEquiv := {
      toFun := bicollarForward C
      invFun := inv
      left_inv := hleft
      right_inv := hright' }
    continuous_toFun := continuous_bicollarForward C
    continuous_invFun := hinv }
  exact ⟨{ homeomorph := h, copy_time := bicollarForward_signedTime C }⟩

end SignedCollarTopology
/-- Each open side has precisely the topology of the original interior. -/
def interiorCopyHomeomorph (B : Set M) (s : Bool) : (Bᶜ : Set M) ≃ₜ side B s := by
  let f : (Bᶜ : Set M) → side B s := fun x => ⟨copy B s x.val, x.val, x.property, rfl⟩
  have hfold (q : side B s) : fold B q.val ∉ B := by
    obtain ⟨x,hx,heq⟩ := q.property
    rw [← heq,fold_copy]
    exact hx
  let g : side B s → (Bᶜ : Set M) := fun q => ⟨fold B q.val,hfold q⟩
  refine {
    toEquiv := {
      toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_ }
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro x
    rfl
  · intro q
    apply Subtype.ext
    obtain ⟨x,hx,heq⟩ := q.property
    change copy B s (fold B q.val) = q.val
    rw [← heq,fold_copy]
  · exact ((continuous_copy B s).comp continuous_subtype_val).subtype_mk _
  · exact ((continuous_fold B).comp continuous_subtype_val).subtype_mk _

/-- Second countability follows from three actual open subsets: the bicollar
and the two interiors. No openness of the global quotient map is presumed. -/
theorem surface_secondCountable {kind : ModelKind}
    (S : SmoothManifold 2 kind M) (C : SmoothCollar S) (H : SignedCollar C) :
    SecondCountableTopology (SurfaceDouble S) := by
  let := S.topologicalManifold.secondCountable
  let B := intrinsicBoundary S
  let U : Option Bool → Set (Double B) := fun i => match i with
    | none => fold B ⁻¹' C.neighborhood
    | some s => side B s
  have hopen : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none => exact C.isOpen_neighborhood.preimage (continuous_fold B)
    | some s => exact isOpen_side B (SmoothManifolds.isClosed_intrinsicBoundary S) s
  let : ∀ i, SecondCountableTopology (U i) := by
    intro i
    cases i with
    | none => exact H.homeomorph.symm.secondCountableTopology
    | some s => exact (interiorCopyHomeomorph B s).symm.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover hopen
  apply eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    by_cases hx : x.2 ∈ B
    · apply mem_iUnion.mpr
      exact ⟨none,C.boundary_subset hx⟩
    · apply mem_iUnion.mpr
      exact ⟨some x.1,x.2,hx,rfl⟩

@[simp] theorem copy_mem_copy_range (B : Set M) (s t : Bool) (x : M) :
    copy B s x ∈ range (copy B t) ↔ s = t ∨ x ∈ B := by
  constructor
  · rintro ⟨y,hy⟩
    have h := (copy_eq_iff B s t x y).mp hy.symm
    exact h.2
  · intro h
    exact ⟨x,(copy_eq_self_iff B t s x).mpr
      (h.elim (fun hs => Or.inl hs.symm) Or.inr)⟩

@[simp] theorem signedTime_decide_absoluteTime (t : SignedTime) :
    signedTime (decide (0 ≤ t.val)) (absoluteTime t) = t := by
  apply Subtype.ext
  by_cases ht : 0 ≤ t.val
  · simp [signedTime,sign,absoluteTime,ht,abs_of_nonneg ht]
  · simp [signedTime,sign,absoluteTime,ht,abs_of_neg (lt_of_not_ge ht)]

/-- The formula for every signed bicollar is forced by its copy-time formula. -/
theorem signedCollar_eq_forward {kind : ModelKind} {S : SmoothManifold 2 kind M}
    (C : SmoothCollar S) (H : SignedCollar C) (q : intrinsicBoundary S) (t : SignedTime) :
    H.homeomorph (q,t) = bicollarForward C (q,t) := by
  have h := H.copy_time (decide (0 ≤ t.val)) q (absoluteTime t)
  rw [signedTime_decide_absoluteTime] at h
  apply Subtype.ext
  rw [h]
  change copy (intrinsicBoundary S) (decide (0 ≤ t.val)) _ =
    if 0 ≤ t.val then copy (intrinsicBoundary S) true _ else copy (intrinsicBoundary S) false _
  by_cases ht : 0 ≤ t.val <;> simp [ht]

/-- The precise local side and seam equations before choosing any boundary chart. -/
theorem signedCollar_sides {kind : ModelKind} {S : SmoothManifold 2 kind M}
    (C : SmoothCollar S) (H : SignedCollar C) (q : intrinsicBoundary S) (t : SignedTime) :
    ((H.homeomorph (q,t)).val ∈ range (copy (intrinsicBoundary S) true) ↔ 0 ≤ t.val) ∧
    ((H.homeomorph (q,t)).val ∈ range (copy (intrinsicBoundary S) false) ↔ t.val ≤ 0) ∧
    ((H.homeomorph (q,t)).val ∈ seam (intrinsicBoundary S) ↔ t.val = 0) := by
  rw [signedCollar_eq_forward]
  by_cases ht : 0 ≤ t.val
  · simp only [bicollarForward,ht,↓reduceIte,copy_mem_copy_range,copy_mem_seam,
      collar_mem_boundary_iff]
    simp [absoluteTime,le_antisymm_iff,ht]
  · have hn : t.val < 0 := lt_of_not_ge ht
    simp only [bicollarForward,ht,↓reduceIte,copy_mem_copy_range,copy_mem_seam,
      collar_mem_boundary_iff]
    simp [absoluteTime,abs_eq_zero,hn.le,hn.ne]

/-- The topological bicollar and induced boundary are unconditional outputs,
independently of the smooth atlas constructed below. -/
theorem collar_topology : Expected.collarTopology.{u} := by
  intro kind M _ _ S
  obtain ⟨C⟩ := SmoothManifolds.Collars.collar_exists S
  obtain ⟨H⟩ := exists_signedCollar C
  obtain ⟨B,hBS,hB⟩ := SmoothManifolds.exists_boundary_smoothManifold S
  obtain ⟨hcompact,hfinite⟩ := boundary_finite_components S B
  let := S.topologicalManifold.hausdorff
  exact ⟨C,H,surface_secondCountable S C H,signedCollar_sides C H,
    B,hBS,hB,hcompact,hfinite,
    seamMap_closedEmbedding _ (SmoothManifolds.isClosed_intrinsicBoundary S)⟩

/-- Restricting the source of one smooth chart preserves compatibility. -/
theorem compatible_restrict_left {n : ℕ} {kind : ModelKind} {r : ℕ∞}
    {c d : ModelChart n kind M} (h : ContDiffCompatible r c d) (U : Set M) :
    ContDiffCompatible r (c.restr U) d := by
  constructor
  · exact SmoothManifolds.contDiffOnModel_mono h.1 (fun x hx => ⟨hx.1.1,hx.2⟩)
  · exact SmoothManifolds.contDiffOnModel_mono h.2 (fun x hx => ⟨hx.1,hx.2.1⟩)

/-- Maximality admits all source restrictions; it does not identify an ambient
chart with an original half-space chart. -/
theorem restricted_chart_mem {n : ℕ} {kind : ModelKind}
    (S : SmoothManifold n kind M) (c : ModelChart n kind M)
    (hc : c ∈ S.smoothStructure.val) (U : Set M) :
    c.restr U ∈ S.smoothStructure.val := by
  have heq := S.smoothStructure.property.2 _
    (SmoothManifolds.maximalExtension_isContDiffAtlas S.smoothStructure.property.1)
    (SmoothManifolds.subset_maximalExtension S.smoothStructure.property.1)
  have hm : c.restr U ∈ maximalExtension (⊤ : ℕ∞) S.smoothStructure.val := by
    intro d hd
    exact compatible_restrict_left (S.smoothStructure.property.1.2 c hc d hd) U
  change c.restr U ∈ SmoothManifolds.maximalExtension (⊤ : ℕ∞) S.smoothStructure.val at hm
  exact heq ▸ hm

/-- Every original chart has an ambient-chart refinement as soon as the double
atlas is constructed. Continuity of the canonical fold supplies the open set. -/
theorem ambient_chart_refinement {kind : ModelKind} (S : SmoothManifold 2 kind M)
    (D : SmoothManifold 2 .euclidean (SurfaceDouble S)) (s : Bool)
    (e : ModelChart 2 kind M) (_he : e ∈ S.smoothStructure.val) (p : M)
    (hp : p ∈ e.source) :
    ∃ d ∈ D.smoothStructure.val, copy (intrinsicBoundary S) s p ∈ d.source ∧
      copy (intrinsicBoundary S) s ⁻¹' d.source ⊆ e.source := by
  let U : Set (SurfaceDouble S) := fold (intrinsicBoundary S) ⁻¹' e.source
  have hU : IsOpen U := e.open_source.preimage (continuous_fold _)
  obtain ⟨c,hc,hpc⟩ := D.smoothStructure.property.1.1 (copy (intrinsicBoundary S) s p)
  refine ⟨c.restr U,restricted_chart_mem D c hc U,?_,?_⟩
  · rw [c.restr_source' U hU]
    exact ⟨hpc,hp⟩
  · intro x hx
    rw [c.restr_source' U hU] at hx
    exact hx.2

section SignedCharts
local instance (n : ℕ) : Inhabited (ModelSpace n .euclidean) := ⟨⟨0, mem_univ _⟩⟩
variable {kind : ModelKind} {S : SmoothManifold 2 kind M}

/-- Appending a real time coordinate, with the existing Euclidean topology. -/
def snocModelHomeomorph :
    (ModelSpace 1 .euclidean × ℝ) ≃ₜ ModelSpace 2 .euclidean where
  toFun x := ⟨Fin.snoc (α := fun _ : Fin 2 => ℝ) x.1.val x.2, mem_univ _⟩
  invFun z := (⟨Fin.init z.val, mem_univ _⟩, z.val (Fin.last 1))
  left_inv := by
    intro x
    apply Prod.ext
    · apply Subtype.ext
      change Fin.init (Fin.snoc (α := fun _ : Fin 2 => ℝ) x.1.val x.2) = x.1.val
      simp only [Fin.init_snoc]
    · change Fin.snoc (α := fun _ : Fin 2 => ℝ) x.1.val x.2 (Fin.last 1) = x.2
      simp only [Fin.snoc_last]
  right_inv := by intro z; apply Subtype.ext; exact Fin.snoc_init_self _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (continuous_snd : Continuous (fun x : ModelSpace 1 .euclidean × ℝ => x.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply j).comp
          ((continuous_subtype_val : Continuous (Subtype.val : ModelSpace 1 .euclidean → Euclidean 1)).comp
            (continuous_fst : Continuous (fun x : ModelSpace 1 .euclidean × ℝ => x.1)))
  continuous_invFun :=
    ((continuous_pi fun i => (continuous_apply i.castSucc).comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_apply (Fin.last 1)).comp continuous_subtype_val)

/-- The ordinary coordinate on the open signed time interval. -/
def signedTimeChart : OpenPartialHomeomorph SignedTime ℝ :=
  (⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ).openPartialHomeomorphSubtypeCoe
    ⟨⟨0, by norm_num⟩⟩

/-- Product coordinates before inclusion into the quotient. -/
def signedProductChart (b : ModelChart 1 .euclidean (intrinsicBoundary S)) :
    OpenPartialHomeomorph (intrinsicBoundary S × SignedTime) (ModelSpace 2 .euclidean) :=
  (b.prod signedTimeChart).transHomeomorph snocModelHomeomorph

@[simp] theorem signedProductChart_apply
    (b : ModelChart 1 .euclidean (intrinsicBoundary S))
    (q : intrinsicBoundary S) (t : SignedTime) :
    (signedProductChart b (q,t)).val = Fin.snoc (α := fun _ : Fin 2 => ℝ) (b q).val t.val := by
  change Fin.snoc (α := fun _ : Fin 2 => ℝ) (b q).val (signedTimeChart t) = _
  congr 1

@[simp] theorem signedProductChart_source
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) :
    (signedProductChart b).source = b.source ×ˢ (univ : Set SignedTime) := rfl

@[simp] theorem signedProductChart_target
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) :
    (signedProductChart b).target = {z : ModelSpace 2 .euclidean |
      (⟨Fin.init z.val, mem_univ _⟩ : ModelSpace 1 .euclidean) ∈ b.target ∧
      z.val (Fin.last 1) ∈ Ioo (-1 : ℝ) 1} := by
  change snocModelHomeomorph.symm ⁻¹' (b.target ×ˢ signedTimeChart.target) = _
  rw [signedTimeChart, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  rfl

/-- The bicollar is an open embedding into the actual quotient topology. -/
theorem signedCollar_isOpenEmbedding (C : SmoothCollar S) (H : SignedCollar C) :
    IsOpenEmbedding (fun x => (H.homeomorph x).val) :=
  (C.isOpen_neighborhood.preimage (continuous_fold _)).isOpenEmbedding_subtypeVal.comp
    H.homeomorph.isOpenEmbedding

/-- An actual signed chart on the quotient, including its total inverse. -/
def signedChart (C : SmoothCollar S) (H : SignedCollar C)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) :
    ModelChart 2 .euclidean (SurfaceDouble S) :=
  (signedProductChart b).lift_openEmbedding (signedCollar_isOpenEmbedding C H)

@[simp] theorem signedChart_source (C : SmoothCollar S) (H : SignedCollar C)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) :
    (signedChart C H b).source = Subtype.val ''
      (H.homeomorph '' (b.source ×ˢ (univ : Set SignedTime))) := by
  simp only [signedChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    signedProductChart_source, image_image, Function.comp_def]

@[simp] theorem signedChart_target (C : SmoothCollar S) (H : SignedCollar C)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) :
    (signedChart C H b).target = {z : ModelSpace 2 .euclidean |
      (⟨Fin.init z.val, mem_univ _⟩ : ModelSpace 1 .euclidean) ∈ b.target ∧
      z.val (Fin.last 1) ∈ Ioo (-1 : ℝ) 1} := by
  exact signedProductChart_target b

@[simp] theorem signedChart_apply (C : SmoothCollar S) (H : SignedCollar C)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S))
    (q : intrinsicBoundary S) (t : SignedTime) :
    (signedChart C H b (H.homeomorph (q,t)).val).val = Fin.snoc (α := fun _ : Fin 2 => ℝ) (b q).val t.val := by
  rw [signedChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact signedProductChart_apply b q t

/-- Both sides and the seam are precisely the signed coordinate half-planes. -/
theorem signedChart_sides (C : SmoothCollar S) (H : SignedCollar C)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S))
    (z : SurfaceDouble S) (hz : z ∈ (signedChart C H b).source) :
    (z ∈ range (copy (intrinsicBoundary S) true) ↔
      0 ≤ (signedChart C H b z).val (Fin.last 1)) ∧
    (z ∈ range (copy (intrinsicBoundary S) false) ↔
      (signedChart C H b z).val (Fin.last 1) ≤ 0) ∧
    (z ∈ seam (intrinsicBoundary S) ↔
      (signedChart C H b z).val (Fin.last 1) = 0) := by
  rw [signedChart_source] at hz
  obtain ⟨_,⟨⟨q,t⟩,_,rfl⟩,rfl⟩ := hz
  simpa only [signedChart_apply, Fin.snoc_last] using signedCollar_sides C H q t

/-- Lifted signed-chart transitions equal the product transitions as actual
partial homeomorphisms, not just pointwise formulas at seam points. -/
theorem signedChart_transition (C : SmoothCollar S) (H : SignedCollar C)
    (b c : ModelChart 1 .euclidean (intrinsicBoundary S)) :
    (signedChart C H b).symm.trans (signedChart C H c) =
      (signedProductChart b).symm.trans (signedProductChart c) :=
  OpenPartialHomeomorph.lift_openEmbedding_trans _ _ _

/-- A smooth boundary transition extends smoothly with an unchanged time
coordinate. The extension is defined on an ambient open cylinder across zero. -/
theorem signedProductChart_transition_smooth {r : ℕ∞}
    (b c : ModelChart 1 .euclidean (intrinsicBoundary S))
    (h : ContDiffOnModel r (b.symm.trans c) (b.symm.trans c).source) :
    ContDiffOnModel r ((signedProductChart b).symm.trans (signedProductChart c))
      ((signedProductChart b).symm.trans (signedProductChart c)).source := by
  intro z hz
  let z₀ : ModelSpace 1 .euclidean := ⟨Fin.init z.val, mem_univ _⟩
  have hz₀ : z₀ ∈ (b.symm.trans c).source := by
    exact ⟨hz.1.1, hz.2.1⟩
  obtain ⟨U,hU,hzU,F,hF,heq⟩ := h z₀ hz₀
  have hinit : ContDiff ℝ r (Fin.init : Euclidean 2 → Euclidean 1) :=
    contDiff_pi.mpr fun i => contDiff_apply ℝ _ i.castSucc
  let V : Set (Euclidean 2) := Fin.init ⁻¹' U
  let G : Euclidean 2 → Euclidean 2 := fun y =>
    Fin.snoc (α := fun _ : Fin 2 => ℝ) (F (Fin.init y)) (y (Fin.last 1))
  refine ⟨V,hU.preimage hinit.continuous,hzU,G,?_,?_⟩
  · have hcomp : ContDiffOn ℝ r (fun y : Euclidean 2 => F (Fin.init y)) V :=
      hF.comp hinit.contDiffOn (fun y hy => hy)
    apply contDiffOn_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [G,Fin.snoc_last] using
        (contDiff_apply ℝ _ (Fin.last 1) : ContDiff ℝ r (fun y : Euclidean 2 => y (Fin.last 1))).contDiffOn
    · simpa only [G,V,Fin.snoc_castSucc,Function.comp_def] using
        (contDiffOn_pi.mp hcomp j)
  · intro y hy hyV
    have hy₀ : (⟨Fin.init y.val, mem_univ _⟩ : ModelSpace 1 .euclidean) ∈
        (b.symm.trans c).source := ⟨hy.1.1,hy.2.1⟩
    have ht : (signedTimeChart.symm (y.val (Fin.last 1))).val = y.val (Fin.last 1) :=
      signedTimeChart.right_inv hy.1.2
    change Fin.snoc (α := fun _ : Fin 2 => ℝ) (F (Fin.init y.val))
      (y.val (Fin.last 1)) =
        Fin.snoc (α := fun _ : Fin 2 => ℝ)
          (c (b.symm ⟨Fin.init y.val, mem_univ _⟩)).val
          (signedTimeChart.symm (y.val (Fin.last 1))).val
    rw [ht,heq _ hy₀ hyV]
    rfl

/-- Pairwise smooth compatibility of all signed charts, including at the seam. -/
theorem signedChart_compatible (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (c : ModelChart 1 .euclidean (intrinsicBoundary S)) (hc : c ∈ B.smoothStructure.val) :
    ContDiffCompatible (⊤ : ℕ∞) (signedChart C H b) (signedChart C H c) := by
  have hbc := B.smoothStructure.property.1.2 b hb c hc
  constructor
  · change ContDiffOnModel _ ((signedChart C H b).symm.trans (signedChart C H c)) _
    rw [signedChart_transition]
    exact signedProductChart_transition_smooth b c hbc.1
  · have hi : ((signedChart C H b).symm.trans (signedChart C H c)).symm =
        (signedChart C H c).symm.trans (signedChart C H b) := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    change ContDiffOnModel _ _ _
    rw [← OpenPartialHomeomorph.symm_source,hi,signedChart_transition]
    exact signedProductChart_transition_smooth c b
      (B.smoothStructure.property.1.2 c hc b hb).1

/-- Interior points have ambient interior coordinates in every original chart. -/
theorem interior_coordinates (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (x : M) (hx : x ∈ e.source) (hxb : x ∉ intrinsicBoundary S) :
    (e x).val ∈ interior (modelSet 2 kind) := by
  by_contra h
  exact hxb ((SmoothManifolds.intrinsicBoundary_iff_chart S e he x hx).mpr
    ((SmoothManifolds.mem_modelFace_iff_not_mem_interior (e x)).mpr h))

/-- The actual interior copy is open in the quotient without compactness. -/
theorem interiorCopy_isOpenEmbedding (S : SmoothManifold 2 kind M) (s : Bool) :
    IsOpenEmbedding (fun x : ↥((intrinsicBoundary S)ᶜ : Set M) =>
      copy (intrinsicBoundary S) s x.val) :=
  (isOpen_side _ (SmoothManifolds.isClosed_intrinsicBoundary S) s).isOpenEmbedding_subtypeVal.comp
    (interiorCopyHomeomorph (intrinsicBoundary S) s).isOpenEmbedding

/-- Transport an original interior chart to the labelled open side, using
P104's actual change from either original model to the Euclidean model. -/
def interiorChart (S : SmoothManifold 2 kind M) (s : Bool)
    (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M)) (e : ModelChart 2 kind M) :
    ModelChart 2 .euclidean (SurfaceDouble S) :=
  ((SmoothManifolds.euclideanInteriorChart e).subtypeRestr
    (s := ⟨(intrinsicBoundary S)ᶜ, (SmoothManifolds.isClosed_intrinsicBoundary S).isOpen_compl⟩)
      hne).lift_openEmbedding (interiorCopy_isOpenEmbedding S s)

@[simp] theorem interiorChart_apply (S : SmoothManifold 2 kind M) (s : Bool)
    (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M)) (e : ModelChart 2 kind M)
    (x : M) (hx : x ∉ intrinsicBoundary S) :
    (interiorChart S s hne e (copy (intrinsicBoundary S) s x)).val = (e x).val := by
  change (interiorChart S s hne e
    ((fun y : ↥((intrinsicBoundary S)ᶜ : Set M) => copy (intrinsicBoundary S) s y.val) ⟨x,hx⟩)).val = _
  rw [interiorChart,OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

@[simp] theorem interiorChart_source (S : SmoothManifold 2 kind M) (s : Bool)
    (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M)) (e : ModelChart 2 kind M)
    (he : e ∈ S.smoothStructure.val) :
    (interiorChart S s hne e).source =
      copy (intrinsicBoundary S) s '' (e.source ∩ (intrinsicBoundary S)ᶜ) := by
  rw [interiorChart,OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.subtypeRestr_source,SmoothManifolds.euclideanInteriorChart_source]
  ext z
  constructor
  · rintro ⟨x,⟨hx,_⟩,rfl⟩
    exact ⟨x.val,⟨hx,x.property⟩,rfl⟩
  · rintro ⟨x,⟨hx,hxb⟩,rfl⟩
    exact ⟨⟨x,hxb⟩,⟨hx,interior_coordinates e he x hx hxb⟩,rfl⟩

/-- Equality of input and output germs preserves a coordinate extension. -/
theorem localCoordinateExtension_congr {X : Type*} [TopologicalSpace X]
    {n m : ℕ} {r : ℕ∞} {ι ι' : X → Euclidean n} {f f' : X → Euclidean m}
    {x : X} (h : LocalCoordinateExtension r ι f x)
    (hι : ι =ᶠ[𝓝 x] ι') (hf : f =ᶠ[𝓝 x] f') :
    LocalCoordinateExtension r ι' f' x := by
  obtain ⟨U,hU,hx,F,hF,heq⟩ := h
  refine ⟨U,hU,hι.eq_of_nhds ▸ hx,F,hF,?_⟩
  filter_upwards [hι,heq,hf] with y hy he hyf
  rw [← hy,he,hyf]

/-- The coordinates of an interior chart are the original coordinates after
folding on its whole open source. -/
theorem interiorChart_eq_fold (S : SmoothManifold 2 kind M) (s : Bool)
    (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M)) (e : ModelChart 2 kind M)
    (he : e ∈ S.smoothStructure.val) (z : SurfaceDouble S)
    (hz : z ∈ (interiorChart S s hne e).source) :
    (interiorChart S s hne e z).val = (e (fold (intrinsicBoundary S) z)).val := by
  rw [interiorChart_source S s hne e he] at hz
  obtain ⟨x,⟨_,hx⟩,rfl⟩ := hz
  exact interiorChart_apply S s hne e x hx

theorem interiorChart_fold_mem (S : SmoothManifold 2 kind M) (s : Bool)
    (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M)) (e : ModelChart 2 kind M)
    (he : e ∈ S.smoothStructure.val) (z : SurfaceDouble S)
    (hz : z ∈ (interiorChart S s hne e).source) :
    fold (intrinsicBoundary S) z ∈ e.source := by
  rw [interiorChart_source S s hne e he] at hz
  obtain ⟨x,⟨hx,_⟩,rfl⟩ := hz
  exact hx

/-- All pairs of interior charts are smoothly compatible. -/
theorem interiorChart_compatible (S : SmoothManifold 2 kind M) (s t : Bool)
    (hs ht : Nonempty ((intrinsicBoundary S)ᶜ : Set M))
    (e f : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hf : f ∈ S.smoothStructure.val) :
    ContDiffCompatible (⊤ : ℕ∞) (interiorChart S s hs e) (interiorChart S t ht f) := by
  have germ : ∀ (s t : Bool) (hs ht : Nonempty ((intrinsicBoundary S)ᶜ : Set M))
      (e f : ModelChart 2 kind M), e ∈ S.smoothStructure.val → f ∈ S.smoothStructure.val →
      ∀ z, z ∈ (interiorChart S s hs e).source → z ∈ (interiorChart S t ht f).source →
      ChartContDiffAt (⊤ : ℕ∞) (interiorChart S s hs e) (interiorChart S t ht f) id z := by
    intro s t hs ht e f he hf z hz hz'
    have h := SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 e he f hf)
      (interiorChart_fold_mem S s hs e he z hz) (interiorChart_fold_mem S t ht f hf z hz')
    have hp := SmoothManifolds.LocalCoordinateExtension.precomp h
      (continuous_fold (intrinsicBoundary S)).continuousAt rfl
    apply localCoordinateExtension_congr hp
    · filter_upwards [(interiorChart S s hs e).open_source.mem_nhds hz] with y hy
      exact (interiorChart_eq_fold S s hs e he y hy).symm
    · filter_upwards [(interiorChart S t ht f).open_source.mem_nhds hz'] with y hy
      exact (interiorChart_eq_fold S t ht f hf y hy).symm
  exact SmoothManifolds.contDiffCompatible_of_germs (germ s t hs ht e f he hf)
    (germ t s ht hs f e hf he)

/-- Signed collar charts and both labelled interior chart families. -/
def doubleChartAtlas (S : SmoothManifold 2 kind M) (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) :
    Set (ModelChart 2 .euclidean (SurfaceDouble S)) :=
  {d | (∃ b ∈ B.smoothStructure.val, d = signedChart C H b) ∨
    ∃ s hne e, e ∈ S.smoothStructure.val ∧ d = interiorChart S s hne e}

/-- These charts cover the whole quotient, including an empty surface or seam. -/
theorem doubleChartAtlas_covers (S : SmoothManifold 2 kind M) (C : SmoothCollar S)
    (H : SignedCollar C) (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) :
    IsAtlas (doubleChartAtlas S C H B) := by
  intro z
  induction z using Quotient.inductionOn with
  | h a =>
    by_cases hx : a.2 ∈ intrinsicBoundary S
    · let q : intrinsicBoundary S := ⟨a.2,hx⟩
      obtain ⟨b,hb,hqb⟩ := B.smoothStructure.property.1.1 q
      refine ⟨signedChart C H b,Or.inl ⟨b,hb,rfl⟩,?_⟩
      rw [signedChart_source]
      refine ⟨H.homeomorph (q,signedTime a.1 timeZero),
        mem_image_of_mem H.homeomorph ⟨hqb,mem_univ _⟩,?_⟩
      rw [H.copy_time,C.zero_section]
      rfl
    · obtain ⟨e,he,hxe⟩ := S.smoothStructure.property.1.1 a.2
      let hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M) := ⟨⟨a.2,hx⟩⟩
      refine ⟨interiorChart S a.1 hne e,Or.inr ⟨a.1,hne,e,he,rfl⟩,?_⟩
      rw [interiorChart_source S a.1 hne e he]
      exact mem_image_of_mem _ ⟨hxe,hx⟩

/-- The quotient is a boundaryless topological surface with its fixed quotient
topology, before passing to the maximal smooth atlas below. -/
theorem exists_topologicalDouble (S : SmoothManifold 2 kind M) (C : SmoothCollar S)
    (H : SignedCollar C) (B : SmoothManifold 1 .euclidean (intrinsicBoundary S)) :
    Nonempty (TopologicalManifold 2 .euclidean (SurfaceDouble S)) := by
  let := S.topologicalManifold.hausdorff
  exact ⟨⟨double_t2 _ (SmoothManifolds.isClosed_intrinsicBoundary S),
    surface_secondCountable S C H, doubleChartAtlas S C H B,
    doubleChartAtlas_covers S C H B⟩⟩


/-- A smooth ambient function of the coordinates of an atlas chart is smooth
on the open coordinate domain where its ambient extension is smooth. -/
theorem smooth_coordinate_extension {n m : ℕ} {kind : ModelKind}
    (S : SmoothManifold n kind M) (d : ModelChart n kind M)
    (hd : d ∈ S.smoothStructure.val) (V : Set (Euclidean n)) (hV : IsOpen V)
    (F : Euclidean n → Euclidean m) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V)
    (x : M) (hx : x ∈ d.source) (hxV : (d x).val ∈ V) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun z => F (d z).val) x := by
  have hcont : ContinuousAt (fun z => (d z).val) x :=
    continuous_subtype_val.continuousAt.comp (d.continuousAt hx)
  have hFc : ContinuousAt F ((d x).val) :=
    hF.continuousOn.continuousAt (hV.mem_nhds hxV)
  refine ⟨hFc.comp (f := fun z : M => (d z).val) hcont, ?_⟩
  intro e he hxe
  have hg : LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (d z).val)
      (fun z => F (d z).val) x :=
    ⟨V,hV,hxV,F,hF,Eventually.of_forall (fun _ => rfl)⟩
  exact SmoothManifolds.LocalCoordinateExtension.comp hg
    (SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 e he d hd) hxe hx)

/-- Smoothness of the seam is induced by the given boundary inclusion and
one of the smooth canonical copies. -/
theorem seam_smooth_from_copy {kind : ModelKind}
    (S : SmoothManifold 2 kind M)
    (D : SmoothManifold 2 .euclidean (SurfaceDouble S))
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hB : IsSmoothMap B S Subtype.val)
    (hcopy : IsSmoothMap S D (copy (intrinsicBoundary S) false)) :
    IsSmoothMap B D (seamMap (intrinsicBoundary S)) := by
  exact SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞)
    B.smoothStructure.val S.smoothStructure.val D.smoothStructure.val
    S.smoothStructure.property.1.1 Subtype.val (copy (intrinsicBoundary S) false)
    hB hcopy


def reflectTime (s : Bool) (v : Euclidean 2) : Euclidean 2 :=
  Fin.snoc (α := fun _ : Fin 2 => ℝ) (Fin.init v) (sign s * v (Fin.last 1))

theorem reflectTime_contDiff (s : Bool) : ContDiff ℝ (⊤ : ℕ∞) (reflectTime s) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [reflectTime,Fin.snoc_last] using
      (contDiff_const.mul (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) (Fin.last 1)))
  · simpa only [reflectTime,Fin.snoc_castSucc,Fin.init] using
      (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) j.castSucc)

theorem localCoordinateExtension_reflectTime {X : Type*} [TopologicalSpace X]
    {ι f : X → Euclidean 2} {x : X}
    (s : Bool) (h : LocalCoordinateExtension (⊤ : ℕ∞) ι f x) :
    LocalCoordinateExtension (⊤ : ℕ∞) ι (reflectTime s ∘ f) x := by
  obtain ⟨U,hU,hx,F,hF,heq⟩ := h
  exact ⟨U,hU,hx,reflectTime s ∘ F,(reflectTime_contDiff s).comp_contDiffOn hF,
    heq.fun_comp (reflectTime s)⟩

theorem signedChart_copy_collar (C : SmoothCollar S) (H : SignedCollar C)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) (s : Bool) (y : C.neighborhood) :
    (signedChart C H b (copy (intrinsicBoundary S) s y.val)).val =
      Fin.snoc (α := fun _ : Fin 2 => ℝ) (b (C.toHomeomorph.symm y).1).val
        (sign s * (C.toHomeomorph.symm y).2.val) := by
  let k := C.toHomeomorph.symm y
  have hp := H.copy_time s k.1 k.2
  rw [C.toHomeomorph.apply_symm_apply] at hp
  rw [← hp,signedChart_apply]
  rfl

theorem copy_signedChart_germ (C : SmoothCollar S) (H : SignedCollar C)
    (e d : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (s : Bool) (y : C.neighborhood) (hy : y.val ∈ d.source)
    (hye : (C.toHomeomorph.symm y).1.val ∈ e.source) :
    ChartContDiffAt (⊤ : ℕ∞) d (signedChart C H b)
      (copy (intrinsicBoundary S) s) y.val := by
  have h := localCoordinateExtension_reflectTime s (C.smooth_inverse d e hd he y hy hye)
  have h' : LocalCoordinateExtension (⊤ : ℕ∞)
      (fun z : C.neighborhood => (d z.val).val)
      (fun z => (signedChart C H b (copy (intrinsicBoundary S) s z.val)).val) y := by
    apply SmoothManifolds.LocalCoordinateExtension.congr h
    have hevent : ∀ᶠ z : C.neighborhood in 𝓝 y,
        (C.toHomeomorph.symm z).1.val ∈ e.source :=
      ((continuous_subtype_val.comp continuous_fst).comp C.toHomeomorph.symm.continuous).continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds hye)
    filter_upwards [hevent] with z hz
    rw [signedChart_copy_collar]
    change reflectTime s (collarCoordinates e (C.toHomeomorph.symm z)) = _
    rw [SmoothManifolds.Collars.collarCoordinates_eq_face hb hz]
    simp only [reflectTime, Fin.init_snoc, Fin.snoc_last]
  exact (SmoothManifolds.localCoordinateExtension_open_subtype_iff C.isOpen_neighborhood
    (fun z => (d z).val)
    (fun z => (signedChart C H b (copy (intrinsicBoundary S) s z)).val) y).mp h'

theorem copy_smooth_from_generators (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hB : ∀ e ∈ S.smoothStructure.val,
      Nonempty {q : intrinsicBoundary S // q.val ∈ e.source} →
      ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S e b)
    (D : SmoothManifold 2 .euclidean (SurfaceDouble S))
    (hgen : doubleChartAtlas S C H B ⊆ D.smoothStructure.val) (s : Bool) :
    IsSmoothMap S D (copy (intrinsicBoundary S) s) := by
  intro x
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞)
    S.smoothStructure.val D.smoothStructure.val
    S.smoothStructure.property.1 D.smoothStructure.property.1 _ x).mpr
  obtain ⟨e,he,hxe⟩ := S.smoothStructure.property.1.1 x
  refine ⟨(continuous_copy _ s).continuousAt,e,he,?_⟩
  by_cases hx : x ∈ intrinsicBoundary S
  · let q : intrinsicBoundary S := ⟨x,hx⟩
    obtain ⟨b,hb,hface⟩ := hB e he ⟨⟨q,hxe⟩⟩
    have hqb : q ∈ b.source := by rw [hface.1]; exact hxe
    let y : C.neighborhood := ⟨x,C.boundary_subset hx⟩
    have hk : C.toHomeomorph.symm y = (q,timeZero) := by
      apply C.toHomeomorph.injective
      rw [C.toHomeomorph.apply_symm_apply]
      apply Subtype.ext
      exact (C.zero_section q).symm
    refine ⟨signedChart C H b,hgen (Or.inl ⟨b,hb,rfl⟩),hxe,?_,?_⟩
    · rw [signedChart_source]
      refine ⟨H.homeomorph (q,signedTime s timeZero),
        mem_image_of_mem H.homeomorph ⟨hqb,mem_univ _⟩,?_⟩
      rw [H.copy_time,C.zero_section]
    · exact copy_signedChart_germ C H e e he he b hface s y hxe (by rw [hk]; exact hxe)
  · let hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M) := ⟨⟨x,hx⟩⟩
    let d := interiorChart S s hne e
    refine ⟨d,hgen (Or.inr ⟨s,hne,e,he,rfl⟩),hxe,?_,?_⟩
    · rw [interiorChart_source S s hne e he]
      exact mem_image_of_mem _ ⟨hxe,hx⟩
    · apply SmoothManifolds.LocalCoordinateExtension.congr
        (SmoothManifolds.LocalCoordinateExtension.self (⊤ : ℕ∞) (fun z => (e z).val) x)
      filter_upwards [(SmoothManifolds.isClosed_intrinsicBoundary S).isOpen_compl.mem_nhds hx] with z hz
      exact (interiorChart_apply S s hne e z hz).symm


theorem collar_inverse_neighborhood (C : SmoothCollar S) (y : C.neighborhood)
    {W : Set (CollarSource S)} (hW : W ∈ 𝓝 (C.toHomeomorph.symm y)) :
    ∃ V : Set M, IsOpen V ∧ y.val ∈ V ∧
      ∃ hVN : V ⊆ C.neighborhood,
        ∀ x (hx : x ∈ V), C.toHomeomorph.symm ⟨x,hVN hx⟩ ∈ W := by
  obtain ⟨O,hOW,hO,hyO⟩ := mem_nhds_iff.mp hW
  let V : Set M := Subtype.val '' (C.toHomeomorph '' O)
  have hV : IsOpen V :=
    C.isOpen_neighborhood.isOpenEmbedding_subtypeVal.isOpenMap _
      (C.toHomeomorph.isOpenMap O hO)
  have hyV : y.val ∈ V := by
    refine ⟨y,?_,rfl⟩
    exact ⟨C.toHomeomorph.symm y,hyO,C.toHomeomorph.apply_symm_apply y⟩
  have hVN : V ⊆ C.neighborhood := by
    rintro x ⟨z,_,rfl⟩
    exact z.property
  refine ⟨V,hV,hyV,hVN,?_⟩
  intro x hx
  obtain ⟨z,⟨a,ha,har⟩,hxr⟩ := (show x ∈ V from hx)
  have heq : (⟨x,hVN hx⟩ : C.neighborhood) = C.toHomeomorph a := by
    apply Subtype.ext
    exact hxr.symm.trans (congrArg Subtype.val har.symm)
  rw [heq,C.toHomeomorph.symm_apply_apply]
  exact hOW ha


theorem signed_charts_from_generators (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (D : SmoothManifold 2 .euclidean (SurfaceDouble S))
    (hcharts : ∀ b ∈ B.smoothStructure.val, signedChart C H b ∈ D.smoothStructure.val) :
    ∀ b ∈ B.smoothStructure.val,
      ∃ d ∈ D.smoothStructure.val,
        d.source = Subtype.val ''
          (H.homeomorph '' (b.source ×ˢ (univ : Set SignedTime))) ∧
        d.target = {z : ModelSpace 2 .euclidean |
          (⟨Fin.init z.val, mem_univ _⟩ : ModelSpace 1 .euclidean) ∈ b.target ∧
          z.val (Fin.last 1) ∈ Ioo (-1 : ℝ) 1} ∧
        (∀ q ∈ b.source, ∀ t : SignedTime,
          (d (H.homeomorph (q,t)).val).val = Fin.snoc (b q).val t.val) ∧
        (∀ z ∈ d.source,
          (z ∈ range (copy (intrinsicBoundary S) true) ↔ 0 ≤ (d z).val (Fin.last 1)) ∧
          (z ∈ range (copy (intrinsicBoundary S) false) ↔ (d z).val (Fin.last 1) ≤ 0) ∧
          (z ∈ seam (intrinsicBoundary S) ↔ (d z).val (Fin.last 1) = 0)) := by
  intro b hb
  refine ⟨signedChart C H b,hcharts b hb,signedChart_source C H b,
    signedChart_target C H b,?_,?_⟩
  · intro q _ t
    exact signedChart_apply C H b q t
  · intro z hz
    exact signedChart_sides C H b z hz



theorem localCoordinateExtension_of_precomp_openEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n m : ℕ} {r : ℕ∞} {f : X → Y} (hf : IsOpenEmbedding f)
    {ι : Y → Euclidean n} {g : Y → Euclidean m} {x : X}
    (h : LocalCoordinateExtension r (ι ∘ f) (g ∘ f) x) :
    LocalCoordinateExtension r ι g (f x) := by
  obtain ⟨U,hU,hx,F,hF,he⟩ := h
  refine ⟨U,hU,hx,F,hF,?_⟩
  change {y | F (ι y) = g y} ∈ 𝓝 (f x)
  rw [← hf.map_nhds_eq x]
  exact he

theorem reflectTime_involutive (s : Bool) : Function.Involutive (reflectTime s) := by
  intro z
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [reflectTime,Fin.snoc_last]
    cases s <;> simp [sign]
  · simp [reflectTime, Fin.init]

section Mixed

def signedToCollar (x : intrinsicBoundary S × SignedTime) : CollarSource S :=
  (x.1,absoluteTime x.2)

theorem continuous_signedToCollar : Continuous (signedToCollar (S := S)) :=
  continuous_fst.prodMk (continuous_absoluteTime.comp continuous_snd)

@[simp] theorem fold_signedCollar (C : SmoothCollar S) (H : SignedCollar C)
    (x : intrinsicBoundary S × SignedTime) :
    fold (intrinsicBoundary S) (H.homeomorph x).val =
      (C.toHomeomorph (signedToCollar x)).val := by
  rw [signedCollar_eq_forward]
  dsimp only [bicollarForward,signedToCollar]
  split <;> rfl

theorem collarCoordinates_face {a : ModelChart 2 kind M}
    {b : ModelChart 1 .euclidean (intrinsicBoundary S)} (hab : IsFaceRestriction S a b)
    (x : intrinsicBoundary S × SignedTime) (hx : x.1 ∈ b.source) :
    collarCoordinates a (signedToCollar x) =
      Fin.snoc (α := fun _ : Fin 2 => ℝ) (b x.1).val |x.2.val| := by
  apply congrArg₂ (Fin.snoc (α := fun _ : Fin 2 => ℝ)) ?_ rfl
  funext i
  exact (hab.2.2 _ hx i).symm

theorem reflectTime_absoluteSignedCoordinates
    (s : Bool) (b : ModelChart 1 .euclidean (intrinsicBoundary S))
    (x : intrinsicBoundary S × SignedTime)
    (hx : sign s * x.2.val = |x.2.val|) :
    reflectTime s (Fin.snoc (α := fun _ : Fin 2 => ℝ) (b x.1).val x.2.val) =
      Fin.snoc (α := fun _ : Fin 2 => ℝ) (b x.1).val |x.2.val| := by
  simp only [reflectTime,Fin.init_snoc,Fin.snoc_last,hx]

theorem interiorChart_not_seam (S : SmoothManifold 2 kind M) (s : Bool)
    (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M)) (e : ModelChart 2 kind M)
    (he : e ∈ S.smoothStructure.val) (z : SurfaceDouble S)
    (hz : z ∈ (interiorChart S s hne e).source) : z ∉ seam (intrinsicBoundary S) := by
  rw [interiorChart_source S s hne e he] at hz
  obtain ⟨y,⟨hy,hyb⟩,rfl⟩ := hz
  intro hys
  exact hyb ((copy_mem_seam _ _ _).mp hys)

theorem sign_eq_abs_near_interior (C : SmoothCollar S) (H : SignedCollar C)
    (s : Bool) (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (x : intrinsicBoundary S × SignedTime)
    (hx : (H.homeomorph x).val ∈ (interiorChart S s hne e).source) :
    ∀ᶠ y in 𝓝 x, sign s * y.2.val = |y.2.val| := by
  have hn : x.2.val ≠ 0 := by
    intro ht
    exact interiorChart_not_seam S s hne e he _ hx
      ((signedCollar_sides C H x.1 x.2).2.2.mpr ht)
  have hr : (H.homeomorph x).val ∈ range (copy (intrinsicBoundary S) s) := by
    rw [interiorChart_source S s hne e he] at hx
    obtain ⟨y,hy,hyr⟩ := hx
    exact ⟨y,hyr⟩
  have htcont : Continuous (fun y : intrinsicBoundary S × SignedTime => y.2.val) :=
    continuous_subtype_val.comp continuous_snd
  cases s
  · have hxt : x.2.val < 0 := lt_of_le_of_ne
      ((signedCollar_sides C H x.1 x.2).2.1.mp hr) hn
    have hnear := htcont.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hxt)
    filter_upwards [hnear] with y hy
    change y.2.val < 0 at hy
    simp only [sign,Bool.false_eq_true,↓reduceIte,neg_one_mul,abs_of_neg hy]
  · have hxt : 0 < x.2.val := lt_of_le_of_ne
      ((signedCollar_sides C H x.1 x.2).1.mp hr) (Ne.symm hn)
    have hnear := htcont.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hxt)
    filter_upwards [hnear] with y hy
    change 0 < y.2.val at hy
    simp only [sign,↓reduceIte,one_mul,abs_of_pos hy]

theorem signedChart_interior_germs_face (C : SmoothCollar S) (H : SignedCollar C)
    (s : Bool) (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M))
    (e a : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (ha : a ∈ S.smoothStructure.val)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) (hab : IsFaceRestriction S a b)
    (x : intrinsicBoundary S × SignedTime) (hxb : x.1 ∈ b.source)
    (hxe : (H.homeomorph x).val ∈ (interiorChart S s hne e).source) :
    ChartContDiffAt (⊤ : ℕ∞) (signedChart C H b) (interiorChart S s hne e) id
      (H.homeomorph x).val ∧
    ChartContDiffAt (⊤ : ℕ∞) (interiorChart S s hne e) (signedChart C H b) id
      (H.homeomorph x).val := by
  let j : intrinsicBoundary S × SignedTime → Euclidean 2 := fun y =>
    (signedChart C H b (H.homeomorph y).val).val
  let k : intrinsicBoundary S × SignedTime → Euclidean 2 :=
    fun y => collarCoordinates a (signedToCollar y)
  let o : intrinsicBoundary S × SignedTime → Euclidean 2 := fun y =>
    (e (C.toHomeomorph (signedToCollar y)).val).val
  have hnearB : ∀ᶠ y in 𝓝 x, y.1 ∈ b.source :=
    continuous_fst.continuousAt.preimage_mem_nhds (b.open_source.mem_nhds hxb)
  have hjk : (reflectTime s ∘ j) =ᶠ[𝓝 x] k := by
    filter_upwards [hnearB,sign_eq_abs_near_interior C H s hne e he x hxe] with y hyB hys
    dsimp only [j,k,Function.comp_def]
    rw [signedChart_apply,collarCoordinates_face hab y hyB]
    exact reflectTime_absoluteSignedCoordinates s b y hys
  have hkj : (reflectTime s ∘ k) =ᶠ[𝓝 x] j := by
    filter_upwards [hjk] with y hy
    change reflectTime s (k y) = j y
    rw [← hy]
    exact reflectTime_involutive s (j y)
  have hJK : LocalCoordinateExtension (⊤ : ℕ∞) j k x :=
    (SmoothManifolds.LocalCoordinateExtension.congr (localCoordinateExtension_reflectTime s
      (SmoothManifolds.LocalCoordinateExtension.self (⊤ : ℕ∞) j x)) hjk)
  have hKJ : LocalCoordinateExtension (⊤ : ℕ∞) k j x :=
    (SmoothManifolds.LocalCoordinateExtension.congr (localCoordinateExtension_reflectTime s
      (SmoothManifolds.LocalCoordinateExtension.self (⊤ : ℕ∞) k x)) hkj)
  have hxa : x.1.val ∈ a.source := by rw [hab.1] at hxb; exact hxb
  have hxe' : (C.toHomeomorph (signedToCollar x)).val ∈ e.source := by
    rw [← fold_signedCollar C H x]
    exact interiorChart_fold_mem S s hne e he _ hxe
  have hKO : LocalCoordinateExtension (⊤ : ℕ∞) k o x :=
    SmoothManifolds.LocalCoordinateExtension.precomp
      (C.smooth_forward a e ha he (signedToCollar x) hxa hxe')
      continuous_signedToCollar.continuousAt rfl
  let f : intrinsicBoundary S × SignedTime → C.neighborhood :=
    C.toHomeomorph ∘ signedToCollar
  have hf : Continuous f := C.toHomeomorph.continuous.comp continuous_signedToCollar
  have hOK₀ := SmoothManifolds.LocalCoordinateExtension.precomp
      (C.smooth_inverse e a he ha (f x) hxe' (by
        simpa only [f,Function.comp_def,C.toHomeomorph.symm_apply_apply,signedToCollar] using hxa))
      hf.continuousAt rfl
  have hOK : LocalCoordinateExtension (⊤ : ℕ∞) o k x := by
    dsimp only [f,Function.comp_def] at hOK₀
    simpa only [C.toHomeomorph.symm_apply_apply] using hOK₀
  have hnearE : ∀ᶠ y in 𝓝 x, (H.homeomorph y).val ∈ (interiorChart S s hne e).source :=
    (signedCollar_isOpenEmbedding C H).continuous.continuousAt.preimage_mem_nhds
      ((interiorChart S s hne e).open_source.mem_nhds hxe)
  have ho : o =ᶠ[𝓝 x] (fun y => (interiorChart S s hne e (H.homeomorph y).val).val) := by
    filter_upwards [hnearE] with y hy
    dsimp only [o]
    rw [← fold_signedCollar C H y]
    exact (interiorChart_eq_fold S s hne e he _ hy).symm
  constructor
  · apply localCoordinateExtension_of_precomp_openEmbedding (signedCollar_isOpenEmbedding C H)
    exact SmoothManifolds.LocalCoordinateExtension.congr
      (SmoothManifolds.LocalCoordinateExtension.comp hKO hJK) ho
  · apply localCoordinateExtension_of_precomp_openEmbedding (signedCollar_isOpenEmbedding C H)
    exact localCoordinateExtension_congr
      (SmoothManifolds.LocalCoordinateExtension.comp hKJ hOK) ho (EventuallyEq.refl _ _)

theorem signedChart_interiorChart_germs (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hB : ∀ a ∈ S.smoothStructure.val,
      Nonempty {q : intrinsicBoundary S // q.val ∈ a.source} →
      ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S a b)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (s : Bool) (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (z : SurfaceDouble S) (hzb : z ∈ (signedChart C H b).source)
    (hze : z ∈ (interiorChart S s hne e).source) :
    ChartContDiffAt (⊤ : ℕ∞) (signedChart C H b) (interiorChart S s hne e) id z ∧
    ChartContDiffAt (⊤ : ℕ∞) (interiorChart S s hne e) (signedChart C H b) id z := by
  rw [signedChart_source] at hzb
  obtain ⟨_,⟨x,hxb,rfl⟩,rfl⟩ := hzb
  obtain ⟨a,ha,hxa⟩ := S.smoothStructure.property.1.1 x.1.val
  obtain ⟨b₀,hb₀,hface⟩ := hB a ha ⟨⟨x.1,hxa⟩⟩
  have hxb₀ : x.1 ∈ b₀.source := by rw [hface.1]; exact hxa
  have hzb : (H.homeomorph x).val ∈ (signedChart C H b).source := by
    rw [signedChart_source]
    exact ⟨H.homeomorph x,mem_image_of_mem H.homeomorph hxb,rfl⟩
  have hzb₀ : (H.homeomorph x).val ∈ (signedChart C H b₀).source := by
    rw [signedChart_source]
    exact ⟨H.homeomorph x,mem_image_of_mem H.homeomorph ⟨hxb₀,mem_univ _⟩,rfl⟩
  have h := signedChart_interior_germs_face C H s hne e a he ha b₀ hface x hxb₀ hze
  exact ⟨SmoothManifolds.LocalCoordinateExtension.comp h.1
      (SmoothManifolds.chartContDiffAt_of_compatible
        (signedChart_compatible C H B b hb b₀ hb₀) hzb hzb₀),
    SmoothManifolds.LocalCoordinateExtension.comp
      (SmoothManifolds.chartContDiffAt_of_compatible
        (signedChart_compatible C H B b₀ hb₀ b hb) hzb₀ hzb) h.2⟩

/-- Mixed signed and interior charts are compatible using the actual smooth collar.
The overlap has nonzero signed time, so the absolute-time fold has a locally
constant sign and its coordinate expression is a smooth linear reflection. -/
theorem signedChart_interiorChart_compatible (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hB : ∀ a ∈ S.smoothStructure.val,
      Nonempty {q : intrinsicBoundary S // q.val ∈ a.source} →
      ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S a b)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) (hb : b ∈ B.smoothStructure.val)
    (s : Bool) (hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M))
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val) :
    ContDiffCompatible (⊤ : ℕ∞) (signedChart C H b) (interiorChart S s hne e) := by
  apply SmoothManifolds.contDiffCompatible_of_germs
  · intro z hzb hze
    exact (signedChart_interiorChart_germs C H B hB b hb s hne e he z hzb hze).1
  · intro z hze hzb
    exact (signedChart_interiorChart_germs C H B hB b hb s hne e he z hzb hze).2

end Mixed


theorem reflectTime_signedCoordinates {kind : ModelKind} {S : SmoothManifold 2 kind M}
    (s : Bool) (e : ModelChart 2 kind M)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S)) (hb : IsFaceRestriction S e b)
    (q : intrinsicBoundary S) (hq : q ∈ b.source) (t : CollarTime) :
    reflectTime s (Fin.snoc (α := fun _ : Fin 2 => ℝ) (b q).val
      (signedTime s t).val) = collarCoordinates e (q,t) := by
  have hqe : q.val ∈ e.source := by rw [hb.1] at hq; exact hq
  rw [SmoothManifolds.Collars.collarCoordinates_eq_face hb hqe]
  simp only [reflectTime,Fin.init_snoc,Fin.snoc_last,signedTime]
  cases s <;> simp [sign]

theorem inverse_coordinate_extensions_interior {kind : ModelKind}
    (S : SmoothManifold 2 kind M)
    (D : SmoothManifold 2 .euclidean (SurfaceDouble S)) (s : Bool)
    (hcharts : ∀ hne e, e ∈ S.smoothStructure.val →
      interiorChart S s hne e ∈ D.smoothStructure.val)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hpb : p ∉ intrinsicBoundary S) :
    ∃ U : Set (SurfaceDouble S), IsOpen U ∧ copy (intrinsicBoundary S) s p ∈ U ∧
      copy (intrinsicBoundary S) s ⁻¹' U ⊆ e.source ∧
      ∃ F : SurfaceDouble S → Euclidean 2,
        (∀ z ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
          D.smoothStructure.val F z) ∧
        ∀ x, copy (intrinsicBoundary S) s x ∈ U →
          F (copy (intrinsicBoundary S) s x) = (e x).val := by
  let hne : Nonempty ((intrinsicBoundary S)ᶜ : Set M) := ⟨⟨p,hpb⟩⟩
  let d := interiorChart S s hne e
  refine ⟨d.source,d.open_source,?_,?_,fun z => (d z).val,?_,?_⟩
  · rw [interiorChart_source S s hne e he]
    exact mem_image_of_mem _ ⟨hp,hpb⟩
  · intro x hx
    exact interiorChart_fold_mem S s hne e he _ hx
  · intro z hz
    exact smooth_coordinate_extension D d (hcharts hne e he) univ isOpen_univ id contDiffOn_id z hz (mem_univ _)
  · intro x hx
    exact interiorChart_eq_fold S s hne e he _ hx



/-- The collar charts and both interior families form a smooth atlas. -/
theorem doubleChartAtlas_isContDiffAtlas (S : SmoothManifold 2 kind M)
    (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hB : ∀ e ∈ S.smoothStructure.val,
      Nonempty {q : intrinsicBoundary S // q.val ∈ e.source} →
      ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S e b) :
    IsContDiffAtlas (⊤ : ℕ∞) (doubleChartAtlas S C H B) := by
  refine ⟨doubleChartAtlas_covers S C H B, ?_⟩
  intro c hc d hd
  rcases hc with ⟨b,hb,rfl⟩ | ⟨s,hs,e,he,rfl⟩
  · rcases hd with ⟨b',hb',rfl⟩ | ⟨t,ht,f,hf,rfl⟩
    · exact signedChart_compatible C H B b hb b' hb'
    · exact signedChart_interiorChart_compatible C H B hB b hb t ht f hf
  · rcases hd with ⟨b',hb',rfl⟩ | ⟨t,ht,f,hf,rfl⟩
    · exact SmoothManifolds.contDiffCompatible_symm
        (signedChart_interiorChart_compatible C H B hB b' hb' s hs e he)
    · exact interiorChart_compatible S s t hs ht e f he hf

/-- The maximal smooth extension is built on the already fixed quotient topology. -/
def doubleSmoothManifold (S : SmoothManifold 2 kind M) (C : SmoothCollar S)
    (H : SignedCollar C) (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hA : IsContDiffAtlas (⊤ : ℕ∞) (doubleChartAtlas S C H B)) :
    SmoothManifold 2 .euclidean (SurfaceDouble S) where
  topologicalManifold := {
    hausdorff := by
      let := S.topologicalManifold.hausdorff
      exact double_t2 _ (SmoothManifolds.isClosed_intrinsicBoundary S)
    secondCountable := surface_secondCountable S C H
    atlas := doubleChartAtlas S C H B
    covers := hA.1 }
  smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) (doubleChartAtlas S C H B),
    SmoothManifolds.maximalExtension_isMaximal hA⟩

theorem doubleSmoothManifold_generators (S : SmoothManifold 2 kind M) (C : SmoothCollar S)
    (H : SignedCollar C) (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hA : IsContDiffAtlas (⊤ : ℕ∞) (doubleChartAtlas S C H B)) :
    doubleChartAtlas S C H B ⊆ (doubleSmoothManifold S C H B hA).smoothStructure.val :=
  SmoothManifolds.subset_maximalExtension hA

/-- Assemble the topological, induced-boundary and smooth-copy conclusions;
the remaining input is the independently proved coordinate-extension clause. -/
theorem smoothDouble_of_coordinate_extensions [CompactSpace M]
    (S : SmoothManifold 2 kind M) (C : SmoothCollar S) (H : SignedCollar C)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hBS : IsSmoothMap B S Subtype.val)
    (hB : ∀ e ∈ S.smoothStructure.val,
      Nonempty {q : intrinsicBoundary S // q.val ∈ e.source} →
      ∃ b ∈ B.smoothStructure.val, IsFaceRestriction S e b)
    (D : SmoothManifold 2 .euclidean (SurfaceDouble S))
    (hgen : doubleChartAtlas S C H B ⊆ D.smoothStructure.val)
    (hinv : ∀ s e, e ∈ S.smoothStructure.val → ∀ p ∈ e.source,
      ∃ U : Set (SurfaceDouble S), IsOpen U ∧ copy (intrinsicBoundary S) s p ∈ U ∧
        copy (intrinsicBoundary S) s ⁻¹' U ⊆ e.source ∧
        ∃ F : SurfaceDouble S → Euclidean 2,
          (∀ z ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
            D.smoothStructure.val F z) ∧
          ∀ x, copy (intrinsicBoundary S) s x ∈ U →
            F (copy (intrinsicBoundary S) s x) = (e x).val) :
    Nonempty (SmoothDouble S) := by
  let := S.topologicalManifold.hausdorff
  have hclosed := SmoothManifolds.isClosed_intrinsicBoundary S
  obtain ⟨hcompact,hfinite⟩ := boundary_finite_components S B
  have hcopy := copy_smooth_from_generators C H B hB D hgen
  refine ⟨{
    hausdorff := double_t2 _ hclosed
    compact := double_compact _
    secondCountable := surface_secondCountable S C H
    copy_closedEmbedding := copy_closedEmbedding _ hclosed
    copies_cover := copies_cover _
    copies_intersect := copies_intersect _
    collar := C
    bicollar := H
    manifold := D
    no_boundary := SmoothManifolds.intrinsicBoundary_euclidean D
    copy_smooth := hcopy
    boundary := B
    boundary_inclusion_smooth := hBS
    boundary_induced := hB
    seam_compact := hcompact
    seam_finite_components := hfinite
    seam_closedEmbedding := seamMap_closedEmbedding _ hclosed
    seam_smooth := seam_smooth_from_copy S D B hBS (hcopy false)
    signed_charts := ?_
    chart_refinement := ambient_chart_refinement S D
    inverse_coordinate_extensions := hinv }⟩
  intro b hb
  exact ⟨signedChart C H b,hgen (Or.inl ⟨b,hb,rfl⟩),
    signedChart_source C H b,signedChart_target C H b,
    fun q _ t => signedChart_apply C H b q t,signedChart_sides C H b⟩

theorem inverse_coordinate_extensions_seam {kind : ModelKind}
    (S : SmoothManifold 2 kind M)
    (D : SmoothManifold 2 .euclidean (SurfaceDouble S))
    (C : SmoothCollar S) (H : SignedCollar C) (s : Bool)
    (e : ModelChart 2 kind M) (he : e ∈ S.smoothStructure.val)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S))
    (hface : IsFaceRestriction S e b)
    (hd : signedChart C H b ∈ D.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (hpb : p ∈ intrinsicBoundary S) :
    ∃ U : Set (SurfaceDouble S), IsOpen U ∧ copy (intrinsicBoundary S) s p ∈ U ∧
      copy (intrinsicBoundary S) s ⁻¹' U ⊆ e.source ∧
      ∃ F : SurfaceDouble S → Euclidean 2,
        (∀ z ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
          D.smoothStructure.val F z) ∧
        ∀ x, copy (intrinsicBoundary S) s x ∈ U →
          F (copy (intrinsicBoundary S) s x) = (e x).val := by
  let q : intrinsicBoundary S := ⟨p,hpb⟩
  have hqb : q ∈ b.source := by rw [hface.1]; exact hp
  have hpC : (C.toHomeomorph (q,timeZero)).val ∈ e.source := by
    rw [C.zero_section]; exact hp
  obtain ⟨V,hV,hqV,F,hF,heq⟩ := C.smooth_forward e e he he (q,timeZero) hp hpC
  let W : Set (CollarSource S) :=
    {a | F (collarCoordinates e a) = (e (C.toHomeomorph a).val).val}
  have hW : W ∈ 𝓝 (C.toHomeomorph.symm (C.toHomeomorph (q,timeZero))) := by
    rw [C.toHomeomorph.symm_apply_apply]
    exact heq
  obtain ⟨V₀,hV₀,hpV₀,hV₀N,hV₀W⟩ := collar_inverse_neighborhood C
    (C.toHomeomorph (q,timeZero)) hW
  have hpV₀' : p ∈ V₀ := by simpa only [C.zero_section] using hpV₀
  let d := signedChart C H b
  let R : Set (Euclidean 2) := reflectTime s ⁻¹' V
  have hR : IsOpen R := hV.preimage (reflectTime_contDiff s).continuous
  let Q : Set (SurfaceDouble S) := d.source ∩ (fun z => (d z).val) ⁻¹' R
  have hQ : IsOpen Q := d.isOpen_inter_preimage (hR.preimage continuous_subtype_val)
  let U : Set (SurfaceDouble S) := fold (intrinsicBoundary S) ⁻¹' (V₀ ∩ e.source) ∩ Q
  have hU : IsOpen U := (hV₀.inter e.open_source).preimage (continuous_fold _) |>.inter hQ
  have hqp : (H.homeomorph (q,signedTime s timeZero)).val =
      copy (intrinsicBoundary S) s p := by
    rw [H.copy_time,C.zero_section]
  have hpd : copy (intrinsicBoundary S) s p ∈ d.source := by
    rw [signedChart_source]
    exact ⟨H.homeomorph (q,signedTime s timeZero),
      mem_image_of_mem H.homeomorph ⟨hqb,mem_univ _⟩,hqp⟩
  have hpR : (d (copy (intrinsicBoundary S) s p)).val ∈ R := by
    change reflectTime s (d (copy (intrinsicBoundary S) s p)).val ∈ V
    rw [← hqp,signedChart_apply,reflectTime_signedCoordinates s e b hface q hqb timeZero]
    exact hqV
  let G : Euclidean 2 → Euclidean 2 := F ∘ reflectTime s
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G R :=
    hF.comp (reflectTime_contDiff s).contDiffOn (fun _ hz => hz)
  refine ⟨U,hU,⟨⟨hpV₀',hp⟩,hpd,hpR⟩,?_,fun z => G (d z).val,?_,?_⟩
  · intro x hx
    exact hx.1.2
  · intro z hz
    exact smooth_coordinate_extension D d hd R hR G hG z hz.2.1 hz.2.2
  · intro x hx
    let y : C.neighborhood := ⟨x,hV₀N hx.1.1⟩
    let k := C.toHomeomorph.symm y
    have hkW : k ∈ W := hV₀W x hx.1.1
    have hcopy : (H.homeomorph (k.1,signedTime s k.2)).val =
        copy (intrinsicBoundary S) s x := by
      rw [H.copy_time]
      change copy (intrinsicBoundary S) s (C.toHomeomorph (C.toHomeomorph.symm y)).val = _
      rw [C.toHomeomorph.apply_symm_apply]
    have hkb : k.1 ∈ b.source := by
      have hsource := hx.2.1
      change copy (intrinsicBoundary S) s x ∈ (signedChart C H b).source at hsource
      rw [← hcopy,signedChart_source] at hsource
      obtain ⟨a,ha,heqa⟩ := hsource
      have hae : a = H.homeomorph (k.1,signedTime s k.2) := Subtype.ext heqa
      rw [hae] at ha
      obtain ⟨v,hv,heqv⟩ := ha
      have hvk := H.homeomorph.injective heqv
      rw [hvk] at hv
      exact hv.1
    change F (reflectTime s (signedChart C H b (copy (intrinsicBoundary S) s x)).val) = _
    rw [signedChart_copy_collar C H b s y]
    change F (reflectTime s (Fin.snoc (α := fun _ : Fin 2 => ℝ)
      (b k.1).val (signedTime s k.2).val)) = _
    rw [reflectTime_signedCoordinates s e b hface k.1 hkb k.2]
    change F (collarCoordinates e k) = _
    rw [hkW]
    dsimp [k]
    rw [C.toHomeomorph.apply_symm_apply]


end SignedCharts

/-- The canonical labelled double of every compact smooth surface, built from
an actual smooth collar and the induced boundary atlas. -/
theorem construction : Expected.construction.{u} := by
  intro kind M _ _ S
  obtain ⟨C⟩ := SmoothManifolds.Collars.collar_exists S
  obtain ⟨H⟩ := exists_signedCollar C
  obtain ⟨B,hBS,hB⟩ := SmoothManifolds.exists_boundary_smoothManifold S
  let hA := doubleChartAtlas_isContDiffAtlas S C H B hB
  let D := doubleSmoothManifold S C H B hA
  have hgen : doubleChartAtlas S C H B ⊆ D.smoothStructure.val :=
    doubleSmoothManifold_generators S C H B hA
  apply smoothDouble_of_coordinate_extensions S C H B hBS hB D hgen
  intro s e he p hp
  by_cases hpb : p ∈ intrinsicBoundary S
  · obtain ⟨b,hb,hface⟩ := hB e he ⟨⟨⟨p,hpb⟩,hp⟩⟩
    exact inverse_coordinate_extensions_seam S D C H s e he b hface
      (hgen (Or.inl ⟨b,hb,rfl⟩)) p hp hpb
  · exact inverse_coordinate_extensions_interior S D s
      (fun hne e he => hgen (Or.inr ⟨s,hne,e,he,rfl⟩)) e he p hp hpb


/-- The seam has the standard inclusion and the exact zero slice in the
constructed double's actual smooth charts. -/
theorem seam_standard_coordinates {kind : ModelKind} {S : SmoothManifold 2 kind M}
    (D : SmoothDouble S)
    (b : ModelChart 1 .euclidean (intrinsicBoundary S))
    (hb : b ∈ D.boundary.smoothStructure.val) :
    ∃ d ∈ D.manifold.smoothStructure.val,
      (∀ q ∈ b.source, seamMap (intrinsicBoundary S) q ∈ d.source ∧
        (d (seamMap (intrinsicBoundary S) q)).val = Fin.snoc (b q).val 0) ∧
      ∀ z ∈ d.source,
        z ∈ seam (intrinsicBoundary S) ↔ (d z).val (Fin.last 1) = 0 := by
  obtain ⟨d,hd,hsource,_,hcoords,hsides⟩ := D.signed_charts b hb
  refine ⟨d,hd,?_,fun z hz => (hsides z hz).2.2⟩
  intro q hq
  let t := signedTime false timeZero
  have ht : t.val = 0 := by simp [t,signedTime,timeZero,sign]
  have hqD : (D.bicollar.homeomorph (q,t)).val = seamMap (intrinsicBoundary S) q := by
    rw [D.bicollar.copy_time,D.collar.zero_section]
    rfl
  constructor
  · rw [← hqD,hsource]
    exact ⟨D.bicollar.homeomorph (q,t),mem_image_of_mem D.bicollar.homeomorph ⟨hq,mem_univ _⟩,rfl⟩
  · rw [← hqD,hcoords q hq t,ht]

end P202.SmoothSurfaceDouble
