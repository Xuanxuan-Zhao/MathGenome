import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SubmersionSections
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorConstantRank

set_option autoImplicit false
namespace SmoothManifolds.SubmersionSections
open ModelData AtlasData MapData BoundaryData MapClassData InteriorRankData Set Filter
open scoped Topology ContDiff
universe u v

/-- Insertion of zero in the unused coordinates of a projection chart. -/
noncomputable def coordinateInclusion (m n : ℕ) : E n →L[ℝ] E m :=
  LinearMap.toContinuousLinearMap {
    toFun := normalProjection n m n
    map_add' := by
      intro x y
      ext i
      by_cases hi : i.val < n <;> simp [normalProjection, hi]
    map_smul' := by
      intro t x
      ext i
      by_cases hi : i.val < n <;> simp [normalProjection, hi] }

@[simp] theorem coordinateInclusion_zero (m n : ℕ) : coordinateInclusion m n 0 = 0 :=
  map_zero _

theorem projection_inclusion {m n : ℕ} (h : n ≤ m) (z : E n) :
    normalProjection m n n (coordinateInclusion m n z) = z := by
  ext i
  simp [normalProjection, coordinateInclusion, lt_of_lt_of_le i.isLt h]

/-- Smoothness in compatible coordinates implies smoothness in the original
maximal atlases. The Euclidean map is allowed to change dimension. -/
theorem smoothAt_of_compatible {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (c : OpenPartialHomeomorph M (E m)) (d : OpenPartialHomeomorph N (E n))
    (hc : CompatibleCoordinates ⊤ S c) (hd : CompatibleCoordinates ⊤ T d)
    (f : M → N) (x : M) (hfx : ContinuousAt f x)
    (hx : x ∈ c.source) (hfd : f x ∈ d.source)
    (H : E m → E n) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (heq : (fun y => H (c y)) =ᶠ[𝓝 x] (fun y => d (f y))) :
    ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f x := by
  obtain ⟨e, he, A, hA, hAi, hcsub, hcval, hct, hciv⟩ := hc
  obtain ⟨g, hg, B, hB, hBi, hdsub, hdval, hdt, hdiv⟩ := hd
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _
    (InteriorInverse.smoothAtlas_contDiff S ⊤)
    (InteriorInverse.smoothAtlas_contDiff T ⊤) f x).mpr
  refine ⟨hfx, e, he, g, hg, (hcsub hx).1, (hdsub hfd).1, ?_⟩
  let F := H ∘ A
  let V := A.source ∩ F ⁻¹' B.target
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F A.source := hH.comp_contDiffOn hA
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage A.open_source B.open_target
  have hxV : (e x).val ∈ V := by
    refine ⟨(hcval x hx).1, ?_⟩
    change H (A (e x).val) ∈ B.target
    rw [← (hcval x hx).2, heq.eq_of_nhds]
    exact hdt (d.map_source hfd)
  refine ⟨V, hV, hxV, B.symm ∘ F,
    hBi.comp (hF.mono inter_subset_left) (fun _ hz => hz.2), ?_⟩
  filter_upwards [c.open_source.mem_nhds hx,
    hfx.preimage_mem_nhds (d.open_source.mem_nhds hfd), heq] with y hy hyf hyeq
  change B.symm (H (A (e y).val)) = (g (f y)).val
  rw [← (hcval y hy).2, hyeq]
  exact (hdiv (d (f y)) (d.map_source hyf)).symm.trans
    (congrArg (fun z => (g z).val) (d.left_inv hyf))

/-- A centered projection normal form gives an actual smooth local section. -/
theorem section_of_normalForm {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (q : M → N) (x : M) (hnm : n ≤ m) (hn : NormalForm ⊤ S T q x n) :
    ∃ U : Set N, IsOpen U ∧ q x ∈ U ∧
      ∃ s : N → M, ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val s U ∧
        (∀ y ∈ U, q (s y) = y) ∧ s (q x) = x := by
  obtain ⟨c, d, hc, hd, hx, hcx, hqx, hdqx, hmap, hproj⟩ := hn
  let J := coordinateInclusion m n
  let U := d.source ∩ (fun y => J (d y)) ⁻¹' c.target
  have hU : IsOpen U :=
    (J.continuous.comp_continuousOn d.continuousOn).isOpen_inter_preimage
      d.open_source c.open_target
  have hqxU : q x ∈ U := by
    refine ⟨hqx, ?_⟩
    change J (d (q x)) ∈ c.target
    rw [hdqx, map_zero, ← hcx]
    exact c.map_source hx
  let s : N → M := fun y => c.symm (J (d y))
  have hs (y : N) (hy : y ∈ U) : s y ∈ c.source := c.map_target hy.2
  have hsmooth : ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val s U := by
    intro y hy
    have hdcont : ContinuousAt (fun z : N => J (d z)) y :=
      J.continuous.continuousAt.comp (d.continuousAt hy.1)
    have hscont : ContinuousAt s y :=
      ContinuousAt.comp (f := fun z : N => J (d z)) (x := y)
        (c.symm.continuousAt hy.2) hdcont
    apply smoothAt_of_compatible T S d c hd hc s y hscont hy.1 (hs y hy)
      J J.contDiff
    filter_upwards [hU.mem_nhds hy] with z hz
    exact (c.right_inv hz.2).symm
  refine ⟨U, hU, hqxU, s, hsmooth, ?_, ?_⟩
  · intro y hy
    apply d.injOn (hmap (hs y hy)) hy.1
    exact (hproj (J (d y)) hy.2).trans (projection_inclusion hnm (d y))
  · change c.symm (J (d (q x))) = x
    rw [hdqx, map_zero, ← hcx, c.left_inv hx]

/-- A smooth submersion between boundaryless manifolds has a section through
any prescribed source point. -/
theorem local_section :
    Specs.SmoothManifolds.Ch03.SubmersionSections.local_sectionType.{u,v} := by
  intro m n a b M N _ _ S T q hS hT hq hsub x
  have hxi : x ∈ manifoldInterior S := by
    rw [← compl_intrinsicBoundary S]
    change x ∉ BoundaryData.intrinsicBoundary S
    rw [hS]
    exact notMem_empty x
  have hqxi : q x ∈ manifoldInterior T := by
    rw [← compl_intrinsicBoundary T]
    change q x ∉ BoundaryData.intrinsicBoundary T
    rw [hT]
    exact notMem_empty (q x)
  obtain ⟨hnm, hn, _⟩ := InteriorConstantRank.interior_submersion
    ⊤ (by simp) S T q hq x hxi hqxi (hsub x)
  exact section_of_normalForm S T q x hnm hn

/-- Local sections through every point imply that a submersion is open. -/
theorem isOpenMap :
    Specs.SmoothManifolds.Ch03.SubmersionSections.isOpenMapType.{u,v} := by
  intro m n a b M N _ _ S T q hS hT hq hsub V hV
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨U, hU, hqx, s, hs, hsec, hbase⟩ := local_section S T q hS hT hq hsub x
  have hpre : s ⁻¹' V ∈ 𝓝 (q x) := (hs (q x) hqx).1.preimage_mem_nhds
    (hbase.symm ▸ hV.mem_nhds hx)
  apply Filter.mem_of_superset (inter_mem (hU.mem_nhds hqx) hpre)
  intro z hz
  exact ⟨s z, hz.2, hsec z hz.1⟩

end SmoothManifolds.SubmersionSections
