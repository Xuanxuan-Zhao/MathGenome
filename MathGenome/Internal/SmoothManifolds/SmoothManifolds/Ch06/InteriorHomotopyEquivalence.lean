import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.InteriorHomotopyEquivalence
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.Collar
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Boundary
import Mathlib.Tactic.FunProp

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.Collar
namespace SmoothManifolds.InteriorHomotopies
open ModelData AtlasData MapData BoundaryData CollarData InteriorHomotopyData PartitionData
open Set Filter
open scoped Topology ContDiff
universe u v

section General
variable {n m : ℕ} {a b : ModelKind} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- A smooth ambient formula is a local extension along any coordinates. -/
theorem extension_of_contDiff {k l : ℕ} (ι : X → Euclidean k)
    (F : Euclidean k → Euclidean l) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : X) :
    LocalCoordinateExtension (⊤ : ℕ∞) ι (F ∘ ι) x :=
  ⟨univ, isOpen_univ, mem_univ _, F, hF.contDiffOn,
    Eventually.of_forall (fun _ => rfl)⟩

/-- Slicing at either endpoint retains the ambient extension, rather than
merely a one-sided derivative. -/
theorem smoothHomotopy_slice {A : Set (ModelChart n a X)}
    {B : Set (ModelChart m b Y)} {H : HomotopyTime × X → Y}
    (hH : SmoothHomotopy A B H) (s : HomotopyTime) :
    ManifoldSmooth A B (fun x => H (s, x)) := by
  intro x
  refine ⟨hH.1.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt, ?_⟩
  intro e he d hd hx hHx
  have h := LocalCoordinateExtension.precomp
    (hH.2 e he d hd (s, x) hx hHx)
    (continuous_const.prodMk continuous_id).continuousAt rfl
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Euclidean n => (Fin.cons s.val z : Euclidean (n + 1))) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : Euclidean n => s.val))
    · simpa using (contDiff_apply ℝ (fun _ : Fin n => ℝ) j)
  exact h.comp (extension_of_contDiff (fun y => (e y).val) _ hc x)

/-- A map into an open subspace is smooth whenever its ambient value is. -/
theorem smooth_codRestrict {A : Set (ModelChart n a X)}
    {B : Set (ModelChart m b Y)} {s : Set Y} (hs : IsOpen s)
    (f : X → s) (hf : ManifoldSmooth A B (fun x => (f x).val)) :
    ManifoldSmooth A (openSubsetAtlas B s hs) f := by
  intro x
  refine ⟨tendsto_subtype_rng.mpr (hf x).1, ?_⟩
  rintro e he _ ⟨hne, d, hd, rfl⟩ hx hfx
  exact (hf x).2 e he d hd hx (by simpa using hfx)

/-- Inclusion with the restricted atlas is smooth, including for an empty
open subspace. -/
theorem smooth_open_inclusion (A : Set (ModelChart n a X))
    (hA : IsContDiffAtlas (⊤ : ℕ∞) A) (s : Set X) (hs : IsOpen s) :
    ManifoldSmooth (openSubsetAtlas A s hs) A Subtype.val := by
  intro x
  refine ⟨continuousAt_subtype_val, ?_⟩
  rintro _ ⟨hne, e, he, rfl⟩ d hd hx hdx
  exact LocalCoordinateExtension.precomp
    (chartContDiffAt_of_compatible (hA.2 e he d hd) (by simpa using hx) hdx)
    continuousAt_subtype_val rfl

/-- Restrict a smooth homotopy to an invariant open subspace. Both source and
target use the actual restricted charts. -/
theorem smoothHomotopy_restrict {A : Set (ModelChart n a X)}
    {H : HomotopyTime × X → X} (hH : SmoothHomotopy A A H)
    (s : Set X) (hs : IsOpen s)
    (hpres : ∀ (t : HomotopyTime) (x : s), H (t, x.val) ∈ s) :
    SmoothHomotopy (openSubsetAtlas A s hs) (openSubsetAtlas A s hs)
      (fun z : HomotopyTime × s => ⟨H (z.1, z.2.val), hpres z.1 z.2⟩) := by
  have hc : Continuous (fun z : HomotopyTime × s => (z.1, z.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  refine ⟨(hH.1.comp hc).subtype_mk _, ?_⟩
  rintro _ ⟨hne, e, he, rfl⟩ _ ⟨hne', d, hd, rfl⟩ z hz hHz
  exact LocalCoordinateExtension.precomp
    (hH.2 e he d hd (z.1, z.2.val) (by simpa using hz) (by simpa using hHz))
    hc.continuousAt rfl

/-- Transfer local extensions out of an open embedded source. -/
theorem extension_of_openEmbedding {Z : Type*} [TopologicalSpace Z]
    {k l : ℕ} {h : Z → X} (hh : Topology.IsOpenEmbedding h)
    (ι : X → Euclidean k) (f : X → Euclidean l) (z : Z)
    (hf : LocalCoordinateExtension (⊤ : ℕ∞) (ι ∘ h) (f ∘ h) z) :
    LocalCoordinateExtension (⊤ : ℕ∞) ι f (h z) := by
  obtain ⟨U, hU, hzU, F, hF, heq⟩ := hf
  refine ⟨U, hU, hzU, F, hF, ?_⟩
  rw [← hh.map_nhds_eq z]
  exact heq

/-- Two local extensions can be combined by any globally smooth operation. -/
theorem extension_combine {k l p q : ℕ} {ι : X → Euclidean k}
    {f : X → Euclidean l} {g : X → Euclidean p} {x : X}
    (hf : LocalCoordinateExtension (⊤ : ℕ∞) ι f x)
    (hg : LocalCoordinateExtension (⊤ : ℕ∞) ι g x)
    (F : Euclidean l × Euclidean p → Euclidean q)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    LocalCoordinateExtension (⊤ : ℕ∞) ι (fun y => F (f y, g y)) x := by
  obtain ⟨U, hU, hxU, f', hf', hef⟩ := hf
  obtain ⟨V, hV, hxV, g', hg', heg⟩ := hg
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    fun z => F (f' z, g' z), ?_, ?_⟩
  · exact hF.comp_contDiffOn ((hf'.mono inter_subset_left).prodMk
      (hg'.mono inter_subset_right))
  · filter_upwards [hef, heg] with y hyf hyg
    simp only [hyf, hyg]

end General

/-- The ambient deformation supplies both smooth homotopy-inverse identities. -/
theorem equivalence_of_deformation {n : ℕ} {kind : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n kind M)
    (H : HomotopyTime × M → M)
    (hH : SmoothHomotopy S.smoothStructure.val S.smoothStructure.val H)
    (hzero : ∀ x, H (InteriorHomotopyData.timeZero, x) = x)
    (hone : ∀ x, H (timeOne, x) ∈ manifoldInterior S)
    (hpres : ∀ (s : HomotopyTime) (x : manifoldInterior S),
      H (s, x.val) ∈ manifoldInterior S) : Nonempty (InteriorHomotopyEquivalence S) := by
  let r : M → manifoldInterior S := fun x => ⟨H (timeOne, x), hone x⟩
  have hI := isOpen_manifoldInterior S
  exact ⟨{
    isOpen_interior := hI
    inverse := r
    smooth_inverse := smooth_codRestrict hI r (smoothHomotopy_slice hH timeOne)
    smooth_inclusion := smooth_open_inclusion _ S.smoothStructure.property.1 _ hI
    homotopy := H
    smooth_homotopy := hH
    homotopy_zero := hzero
    homotopy_one := fun _ => rfl
    preserves_interior := hpres
    smooth_restricted_homotopy := smoothHomotopy_restrict hH _ hI hpres }⟩

section CollarConstruction
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- The scalar collar displacement, with a strict bound below the far end. -/
noncomputable def pushedTime (s : HomotopyTime) (t : CollarTime) (l : ℝ) (hl : l ∈ Icc (0 : ℝ) 1) :
    CollarTime :=
  ⟨t.val + s.val * (1 - t.val) * (l / 4), by
    have hs := s.property
    have ht := t.property
    constructor
    · exact add_nonneg ht.1 (mul_nonneg
        (mul_nonneg hs.1 (sub_nonneg.mpr ht.2.le)) (div_nonneg hl.1 (by norm_num)))
    · have hsl : s.val * l ≤ 1 := by
        calc
          s.val * l ≤ 1 * l := mul_le_mul_of_nonneg_right hs.2 hl.1
          _ ≤ 1 := by simpa using hl.2
      have hpos : 0 < 1 - t.val := sub_pos.mpr ht.2
      nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hsl)]⟩

@[simp] theorem pushedTime_zero (t : CollarTime) (l : ℝ) (hl : l ∈ Icc (0 : ℝ) 1) :
    pushedTime InteriorHomotopyData.timeZero t l hl = t := by
  apply Subtype.ext
  simp [pushedTime, InteriorHomotopyData.timeZero]

@[simp] theorem pushedTime_of_zero (s : HomotopyTime) (t : CollarTime)
    (hl : (0 : ℝ) ∈ Icc (0 : ℝ) 1) : pushedTime s t 0 hl = t := by
  apply Subtype.ext
  simp [pushedTime]

/-- The collar's entire zero section is precisely the intrinsic boundary.
This uses the homeomorphism and the full boundary coverage, without any
unstated global coordinate on M. -/
theorem collar_mem_boundary_iff (C : SmoothCollar S) (a : CollarSource S) :
    (C.toHomeomorph a).val ∈ intrinsicBoundary S ↔ a.2.val = 0 := by
  constructor
  · intro ha
    let q : intrinsicBoundary S := ⟨(C.toHomeomorph a).val, ha⟩
    have heq : C.toHomeomorph a = C.toHomeomorph (q, CollarData.timeZero) := by
      apply Subtype.ext
      exact (C.zero_section q).symm
    have heq' := congrArg (fun z : CollarSource S => z.2.val)
      (C.toHomeomorph.injective heq)
    exact heq'
  · intro ht
    have heq : a.2 = CollarData.timeZero := Subtype.ext ht
    have hz := C.zero_section a.1
    rw [← heq] at hz
    rw [hz]
    exact a.1.property

/-- The formula on the open collar neighborhood. -/
noncomputable def collarDeformation (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) : HomotopyTime × C.neighborhood → M :=
  fun z => (C.toHomeomorph
    ((C.toHomeomorph.symm z.2).1,
      pushedTime z.1 (C.toHomeomorph.symm z.2).2 (χ z.2.val) (hχ z.2.val))).val

/-- The displaced point in the actual collar source. -/
noncomputable def collarLift (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) : HomotopyTime × C.neighborhood → CollarSource S :=
  fun z => ((C.toHomeomorph.symm z.2).1,
    pushedTime z.1 (C.toHomeomorph.symm z.2).2 (χ z.2.val) (hχ z.2.val))

theorem continuous_collarLift (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hcχ : Continuous χ) :
    Continuous (collarLift C χ hχ) := by
  have hA : Continuous (fun z : HomotopyTime × C.neighborhood => C.toHomeomorph.symm z.2) :=
    C.toHomeomorph.symm.continuous.comp continuous_snd
  have ht : Continuous (fun z : HomotopyTime × C.neighborhood =>
      (C.toHomeomorph.symm z.2).2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp hA)
  have hl : Continuous (fun z : HomotopyTime × C.neighborhood => χ z.2.val) :=
    hcχ.comp (continuous_subtype_val.comp continuous_snd)
  have hs : Continuous (fun z : HomotopyTime × C.neighborhood => z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  exact (continuous_fst.comp hA).prodMk
    ((ht.add ((hs.mul (continuous_const.sub ht)).mul (hl.div_const 4))).subtype_mk _)

theorem continuous_collarDeformation (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hcχ : Continuous χ) :
    Continuous (collarDeformation C χ hχ) :=
  continuous_subtype_val.comp (C.toHomeomorph.continuous.comp
    (continuous_collarLift C χ hχ hcχ))

/-- Extend the supported collar displacement by the identity. -/
noncomputable def collarDeformationGlobal (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) : HomotopyTime × M → M :=
  fun z => by
    classical
    exact if hx : z.2 ∈ C.neighborhood then collarDeformation C χ hχ (z.1, ⟨z.2, hx⟩)
      else z.2

@[simp] theorem collarDeformationGlobal_on (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (s : HomotopyTime) (x : C.neighborhood) :
    collarDeformationGlobal C χ hχ (s, x.val) = collarDeformation C χ hχ (s, x) := by
  simp [collarDeformationGlobal, x.property]

@[simp] theorem collarDeformationGlobal_zero (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (x : M) :
    collarDeformationGlobal C χ hχ (InteriorHomotopyData.timeZero, x) = x := by
  classical
  by_cases hx : x ∈ C.neighborhood
  · simp only [collarDeformationGlobal, dite_eq_left hx, collarDeformation, pushedTime_zero]
    exact congrArg Subtype.val (C.toHomeomorph.apply_symm_apply ⟨x, hx⟩)
  · simp [collarDeformationGlobal, hx]

@[simp] theorem collarDeformationGlobal_of_cutoff_zero (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (s : HomotopyTime) (x : M) (hxχ : χ x = 0) :
    collarDeformationGlobal C χ hχ (s, x) = x := by
  classical
  by_cases hx : x ∈ C.neighborhood
  · simp only [collarDeformationGlobal, dite_eq_left hx, collarDeformation, hxχ,
      pushedTime_of_zero]
    exact congrArg Subtype.val (C.toHomeomorph.apply_symm_apply ⟨x, hx⟩)
  · simp [collarDeformationGlobal, hx]

/-- The displacement never carries an interior point back to the zero section. -/
theorem collarDeformationGlobal_preserves_interior (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (s : HomotopyTime)
    (x : manifoldInterior S) :
    collarDeformationGlobal C χ hχ (s, x.val) ∈ manifoldInterior S := by
  classical
  have hxint : x.val ∉ intrinsicBoundary S := by
    simpa only [← compl_intrinsicBoundary S, mem_compl_iff] using x.property
  apply (show (collarDeformationGlobal C χ hχ (s, x.val) ∈ (intrinsicBoundary S)ᶜ) ↔
      collarDeformationGlobal C χ hχ (s, x.val) ∈ manifoldInterior S from
    Set.ext_iff.mp (compl_intrinsicBoundary S) _).mp
  change collarDeformationGlobal C χ hχ (s, x.val) ∉ intrinsicBoundary S
  by_cases hx : x.val ∈ C.neighborhood
  · let a := C.toHomeomorph.symm ⟨x.val, hx⟩
    have ha : a.2.val ≠ 0 := by
      intro hz
      have hb := (collar_mem_boundary_iff C a).mpr hz
      exact hxint (by simpa [a] using hb)
    have hapos : 0 < a.2.val := lt_of_le_of_ne a.2.property.1 (Ne.symm ha)
    simp only [collarDeformationGlobal, dite_eq_left hx, collarDeformation]
    rw [collar_mem_boundary_iff]
    change a.2.val + s.val * (1 - a.2.val) * (χ x.val / 4) ≠ 0
    have hnonneg : 0 ≤ s.val * (1 - a.2.val) * (χ x.val / 4) :=
      mul_nonneg (mul_nonneg s.property.1 (sub_nonneg.mpr a.2.property.2.le))
        (div_nonneg (hχ x.val).1 (by norm_num))
    linarith
  · simpa [collarDeformationGlobal, hx] using hxint

/-- At the final time even the original boundary has entered the interior. -/
theorem collarDeformationGlobal_one_interior (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hboundary : ∀ x ∈ intrinsicBoundary S, χ x = 1) (x : M) :
    collarDeformationGlobal C χ hχ (timeOne, x) ∈ manifoldInterior S := by
  classical
  by_cases hb : x ∈ intrinsicBoundary S
  · have hx := C.boundary_subset hb
    let a := C.toHomeomorph.symm ⟨x, hx⟩
    have ha : a.2.val = 0 := (collar_mem_boundary_iff C a).mp (by simpa [a] using hb)
    rw [← compl_intrinsicBoundary S]
    change collarDeformationGlobal C χ hχ (timeOne, x) ∉ intrinsicBoundary S
    simp only [collarDeformationGlobal, dite_eq_left hx, collarDeformation]
    rw [collar_mem_boundary_iff]
    change a.2.val + (1 : ℝ) * (1 - a.2.val) * (χ x / 4) ≠ 0
    rw [ha, hboundary x hb]
    norm_num
  · exact collarDeformationGlobal_preserves_interior C χ hχ timeOne
      ⟨x, by rw [← compl_intrinsicBoundary S]; exact hb⟩

/-- The polynomial coordinate update has an ambient smooth extension, even
when time or the original manifold point lies on a face. -/
noncomputable def updateCollarCoordinates (k : ℕ) :
    Euclidean (k + 1) × Euclidean 2 → Euclidean (k + 1) :=
  fun p => Fin.snoc (fun i => p.1 i.castSucc)
    (p.1 (Fin.last k) + p.2 0 * (1 - p.1 (Fin.last k)) * (p.2 1 / 4))

theorem contDiff_updateCollarCoordinates (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (updateCollarCoordinates k) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [updateCollarCoordinates, Fin.snoc_last]
    fun_prop
  · simp only [updateCollarCoordinates, Fin.snoc_castSucc]
    fun_prop

/-- The forward collar source coordinates change by the stated polynomial. -/
theorem collarCoordinates_lift (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (e : ModelChart n kind M)
    (z : HomotopyTime × C.neighborhood) :
    collarCoordinates e (collarLift C χ hχ z) =
      updateCollarCoordinates (n - 1)
        (collarCoordinates e (C.toHomeomorph.symm z.2),
          Fin.cons z.1.val (fun _ : Fin 1 => χ z.2.val)) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [collarCoordinates, collarLift, updateCollarCoordinates, pushedTime]
  · simp [collarCoordinates, collarLift, updateCollarCoordinates]

/-- Local smoothness of the collar formula, in the original M chart and time
coordinates. No smooth structure on a corner product is assumed. -/
theorem collarDeformation_extension (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hsχ : ScalarSmooth S.smoothStructure.val χ)
    (d f : ModelChart n kind M) (hd : d ∈ S.smoothStructure.val)
    (hf : f ∈ S.smoothStructure.val) (z : HomotopyTime × C.neighborhood)
    (hz : z.2.val ∈ d.source) (hHz : collarDeformation C χ hχ z ∈ f.source) :
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun w : HomotopyTime × C.neighborhood => Fin.cons w.1.val (d w.2.val).val)
      (fun w => (f (collarDeformation C χ hχ w)).val) z := by
  let ι : HomotopyTime × C.neighborhood → Euclidean (n + 1) :=
    fun w => Fin.cons w.1.val (d w.2.val).val
  obtain ⟨e, he, hqe⟩ := S.smoothStructure.property.1.1 (C.toHomeomorph.symm z.2).1.val
  have htail : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : Euclidean (n + 1) => (fun i : Fin n => v i.succ)) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ _ i.succ)
  have hproj : LocalCoordinateExtension (⊤ : ℕ∞) ι
      (fun w => (d w.2.val).val) z := by
    simpa [ι, Function.comp_def] using extension_of_contDiff ι _ htail z
  have hinv := LocalCoordinateExtension.precomp
    (C.smooth_inverse d e hd he z.2 hz hqe) continuous_snd.continuousAt rfl
  have hcoords := hinv.comp hproj
  have hχM := (hsχ z.2.val).2 d hd hz
  have hχU := LocalCoordinateExtension.precomp hχM
    (continuous_subtype_val.comp continuous_snd).continuousAt rfl
  have hweight := hχU.comp hproj
  have htime : LocalCoordinateExtension (⊤ : ℕ∞) ι
      (fun w (_ : Fin 1) => w.1.val) z := by
    have hcd : ContDiff ℝ (⊤ : ℕ∞)
        (fun v : Euclidean (n + 1) => (fun _ : Fin 1 => v 0)) := by fun_prop
    simpa [ι, Function.comp_def] using extension_of_contDiff ι _ hcd z
  have hpair := extension_combine htime hweight
    (fun p : Euclidean 1 × Euclidean 1 => (Fin.cons (p.1 0) p.2 : Euclidean 2))
    (by
      apply contDiff_pi.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ] <;>
        fun_prop)
  have hup := extension_combine hcoords hpair _ (contDiff_updateCollarCoordinates (n - 1))
  have hnew : LocalCoordinateExtension (⊤ : ℕ∞) ι
      (fun w => collarCoordinates e (collarLift C χ hχ w)) z := by
    simpa only [collarCoordinates_lift, Function.comp_def] using hup
  have hcχ : Continuous χ := continuous_iff_continuousAt.mpr
    (fun x => ((scalarContDiffAt_iff _ _ _ _).mp (hsχ x)).1)
  have hforward := LocalCoordinateExtension.precomp
    (C.smooth_forward e f he hf (collarLift C χ hχ z) hqe hHz)
    (continuous_collarLift C χ hχ hcχ).continuousAt rfl
  exact hforward.comp hnew

/-- Outside a closed support the global formula agrees with the identity on
an actual neighborhood. This is the gluing step at the edge of the collar. -/
theorem collarDeformationGlobal_eventually_identity (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hsupp : sectionSupport χ ⊆ C.neighborhood) (z : HomotopyTime × M)
    (hz : z.2 ∉ C.neighborhood) :
    collarDeformationGlobal C χ hχ =ᶠ[𝓝 z] Prod.snd := by
  have hclosed : IsClosed (sectionSupport χ) := isClosed_closure
  have hx : z.2 ∉ sectionSupport χ := fun h => hz (hsupp h)
  have hzero : ∀ᶠ y in 𝓝 z.2, χ y = 0 := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
    exact Function.notMem_support.mp (fun h => hy (subset_closure h))
  filter_upwards [continuous_snd.continuousAt.eventually hzero] with w hw
  exact collarDeformationGlobal_of_cutoff_zero C χ hχ w.1 w.2 hw

/-- The two formulas glue smoothly because the cutoff has closed support in
the collar, rather than merely vanishing pointwise outside it. -/
theorem smooth_collarDeformationGlobal (C : SmoothCollar S) (χ : M → ℝ)
    (hχ : ∀ x, χ x ∈ Icc (0 : ℝ) 1) (hsχ : ScalarSmooth S.smoothStructure.val χ)
    (hsupp : sectionSupport χ ⊆ C.neighborhood) :
    SmoothHomotopy S.smoothStructure.val S.smoothStructure.val
      (collarDeformationGlobal C χ hχ) := by
  have hcχ : Continuous χ := continuous_iff_continuousAt.mpr
    (fun x => ((scalarContDiffAt_iff _ _ _ _).mp (hsχ x)).1)
  let j : HomotopyTime × C.neighborhood → HomotopyTime × M :=
    fun w => (w.1, w.2.val)
  have hj : Topology.IsOpenEmbedding j :=
    Topology.IsOpenEmbedding.id.prodMap C.isOpen_neighborhood.isOpenEmbedding_subtypeVal
  have heq : collarDeformationGlobal C χ hχ ∘ j = collarDeformation C χ hχ := by
    funext w
    exact collarDeformationGlobal_on C χ hχ w.1 w.2
  constructor
  · apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.2 ∈ C.neighborhood
    · have hc : ContinuousAt (collarDeformationGlobal C χ hχ ∘ j)
          (z.1, ⟨z.2, hz⟩) := by
        rw [heq]
        exact (continuous_collarDeformation C χ hχ hcχ).continuousAt
      exact hj.continuousAt_iff.mp hc
    · exact continuousAt_snd.congr
        (collarDeformationGlobal_eventually_identity C χ hχ hsupp z hz).symm
  · intro e he d hd z hz hHz
    by_cases hx : z.2 ∈ C.neighborhood
    · apply extension_of_openEmbedding hj
        (fun w : HomotopyTime × M => Fin.cons w.1.val (e w.2).val)
        (fun w => (d (collarDeformationGlobal C χ hχ w)).val) (z.1, ⟨z.2, hx⟩)
      simpa only [Function.comp_def, j, collarDeformationGlobal_on] using
        collarDeformation_extension C χ hχ hsχ e d he hd (z.1, ⟨z.2, hx⟩) hz
          (by
            rw [← collarDeformationGlobal_on C χ hχ z.1 ⟨z.2, hx⟩]
            exact hHz)
    · have hevent := collarDeformationGlobal_eventually_identity C χ hχ hsupp z hx
      have hdz : z.2 ∈ d.source := by rw [← hevent.eq_of_nhds]; exact hHz
      have hcoords := LocalCoordinateExtension.precomp
        (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd) hz hdz)
        continuous_snd.continuousAt rfl
      have htail : ContDiff ℝ (⊤ : ℕ∞)
          (fun v : Euclidean (n + 1) => (fun i : Fin n => v i.succ)) :=
        contDiff_pi.mpr (fun i => contDiff_apply ℝ _ i.succ)
      have hproj : LocalCoordinateExtension (⊤ : ℕ∞)
          (fun w : HomotopyTime × M => Fin.cons w.1.val (e w.2).val)
          (fun w => (e w.2).val) z := by
        simpa [Function.comp_def] using
          extension_of_contDiff (fun w : HomotopyTime × M => Fin.cons w.1.val (e w.2).val)
            _ htail z
      exact (hcoords.comp hproj).congr (hevent.fun_comp (fun y => (d y).val)).symm

end CollarConstruction

/-- Conditional draft: the only premise is the complete, universe-polymorphic
collar existence statement supplied by the owner. The original closed target
is intentionally not declared here. -/
theorem interior_inclusion_homotopy_equivalence_conditional
    (hcollar : Specs.SmoothManifolds.Ch06.Collar.collar_existsType.{u}) :
    Specs.SmoothManifolds.Ch06.InteriorHomotopyEquivalence.interior_inclusion_homotopy_equivalenceType.{u} := by
  intro n kind M _ S
  obtain ⟨C⟩ := hcollar S
  obtain ⟨χ, hsχ, hbχ, ⟨V, hV, hBV, hχV⟩, hsupp⟩ :=
    exists_smooth_cutoff S (intrinsicBoundary S) C.neighborhood
      (isClosed_intrinsicBoundary S) C.isOpen_neighborhood C.boundary_subset
  apply equivalence_of_deformation S (collarDeformationGlobal C χ hbχ)
    (smooth_collarDeformationGlobal C χ hbχ hsχ hsupp)
  · exact collarDeformationGlobal_zero C χ hbχ
  · exact collarDeformationGlobal_one_interior C χ hbχ
      (fun x hx => hχV (hBV hx))
  · exact collarDeformationGlobal_preserves_interior C χ hbχ


end SmoothManifolds.InteriorHomotopies

universe v8_closure_7b6c43a418edec3d_u0
theorem _root_.«SmoothManifolds».«InteriorHomotopies».«interior_inclusion_homotopy_equivalence» : _root_.«Specs».«SmoothManifolds».«Ch06».«InteriorHomotopyEquivalence».«interior_inclusion_homotopy_equivalenceType».{v8_closure_7b6c43a418edec3d_u0} :=
  @_root_.«SmoothManifolds».«InteriorHomotopies».«interior_inclusion_homotopy_equivalence_conditional».{v8_closure_7b6c43a418edec3d_u0} (@_root_.«SmoothManifolds».«Collars».«collar_exists».{v8_closure_7b6c43a418edec3d_u0})
