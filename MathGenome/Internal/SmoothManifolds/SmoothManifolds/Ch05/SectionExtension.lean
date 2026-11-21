import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.SectionExtension
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SubmanifoldExtension

namespace SmoothManifolds.SectionExtension
open ModelData AtlasData MapData BundleData FrameData SectionExtensionData
  MapClassData Bundle Set Filter
open scoped Topology
universe u v w z
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- Zero totalization supplies only junk values outside the open domain. -/
noncomputable def totalSection {V : Set M} (t : (q : V) → E q.val) (p : M) : E p := by
  classical
  exact if h : p ∈ V then t ⟨p, h⟩ else 0

@[simp] theorem totalSection_of_mem {V : Set M} (t : (q : V) → E q.val)
    (p : M) (hp : p ∈ V) : totalSection t p = t ⟨p, hp⟩ := by
  simp [totalSection, hp]

theorem totalSection_smooth {V : Set M} (hV : IsOpen V) (t : (q : V) → E q.val)
    (ht : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val V hV)
      B.totalManifold.smoothStructure.val
      (fun q => (⟨q.val, t q⟩ : TotalSpace (Euclidean r) E))) :
    ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, totalSection t p⟩ : TotalSpace (Euclidean r) E)) V := by
  apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ _ V hV).mpr
  have heq : (fun x : V => (⟨x.val, totalSection t x.val⟩ : TotalSpace (Euclidean r) E)) =
      (fun x : V => (⟨x.val, t x⟩ : TotalSpace (Euclidean r) E)) := by
    funext x
    simp only [totalSection_of_mem t _ x.property]
  rw [heq]
  exact ht

/-- Bundle coordinates reduce section smoothness to vector smoothness. -/
theorem coordinates_smoothAt {s : (p : M) → E p} {p : M} (i : ι)
    (hi : p ∈ B.baseSet i)
    (hs : ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E)) p) :
    VectorSmoothAt S.smoothStructure.val
      (fun q => ((B.trivialization i) ⟨q, s q⟩).2) p := by
  exact FrameData.VectorSmoothAt.comp
    (g := fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E))
    (f := fun q : TotalSpace (Euclidean r) E => ((B.trivialization i) q).2)
    B.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt B i ⟨p, s p⟩ hi) hs

theorem smoothAt_of_coordinates {s : (p : M) → E p} {p : M} (i : ι)
    (hi : p ∈ B.baseSet i)
    (hs : VectorSmoothAt S.smoothStructure.val
      (fun q => ((B.trivialization i) ⟨q, s q⟩).2) p) :
    ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E)) p := by
  exact Frames.smoothAt_from_trivialization B S.smoothStructure.property.1 i hi
    (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p) hs
    (fun _ => rfl) Filter.EventuallyEq.rfl

theorem smoothSection_zero : SmoothSection B (fun _ => 0) := B.zero_smooth

/-- Eventual equality is enough for the smoothness of a section germ. -/
theorem section_smoothAt_congr {s t : (p : M) → E p} {p : M}
    (hs : ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E)) p)
    (he : ∀ᶠ q in 𝓝 p, s q = t q) :
    ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, t p⟩ : TotalSpace (Euclidean r) E)) p := by
  obtain ⟨i, hi⟩ := B.covers p
  apply smoothAt_of_coordinates B i hi
  apply (coordinates_smoothAt B i hi hs).congr
  exact he.mono (fun q hq => by dsimp only; rw [hq])

theorem section_add_smoothAt {s t : (p : M) → E p} {p : M}
    (hs : ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E)) p)
    (ht : ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, t p⟩ : TotalSpace (Euclidean r) E)) p) :
    ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p + t p⟩ : TotalSpace (Euclidean r) E)) p := by
  obtain ⟨i, hi⟩ := B.covers p
  apply smoothAt_of_coordinates B i hi
  have hsum := ((coordinates_smoothAt B i hi hs).prod
    (coordinates_smoothAt B i hi ht)).postcomp (contDiff_fst.add contDiff_snd)
  apply hsum.congr
  have hopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
    (B.trivialization i).open_baseSet
  filter_upwards [hopen.mem_nhds hi] with q hq
  exact (B.fiberCoordinates i q hq).map_add (s q) (t q) |>.symm

theorem section_smul_smoothAt {s : (p : M) → E p} {f : M → ℝ} {p : M}
    (hf : PartitionData.ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p)
    (hs : ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E)) p) :
    ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, f p • s p⟩ : TotalSpace (Euclidean r) E)) p := by
  obtain ⟨i, hi⟩ := B.covers p
  apply smoothAt_of_coordinates B i hi
  have hf' : VectorSmoothAt S.smoothStructure.val f p :=
    (scalarContDiffAt_iff _ _ _ _).mp hf
  have hsmul := (hf'.prod (coordinates_smoothAt B i hi hs)).postcomp
    (contDiff_fst.smul contDiff_snd)
  apply hsmul.congr
  have hopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
    (B.trivialization i).open_baseSet
  filter_upwards [hopen.mem_nhds hi] with q hq
  exact (B.fiberCoordinates i q hq).map_smul (f q) (s q) |>.symm

/-- Closed support of the weight makes extension by zero smooth. -/
theorem weighted_section_smooth {s : (p : M) → E p} {f : M → ℝ} {V : Set M}
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f)
    (hs : ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun p => (⟨p, s p⟩ : TotalSpace (Euclidean r) E)) V)
    (hsub : sectionSupport f ⊆ V) : SmoothSection B (fun p => f p • s p) := by
  intro p
  by_cases hp : p ∈ sectionSupport f
  · exact section_smul_smoothAt B (hf p) (hs p (hsub hp))
  · apply section_smoothAt_congr B (smoothSection_zero B p)
    filter_upwards [isClosed_closure.compl_mem_nhds hp] with q hq
    have hz : f q = 0 := Function.notMem_support.mp (fun h => hq (subset_closure h))
    simp [hz]

/-- Finite fiberwise sums are smooth. -/
theorem section_finset_sum_smooth {J : Type*} (F : Finset J) (s : J → (p : M) → E p)
    (hs : ∀ j ∈ F, SmoothSection B (s j)) :
    SmoothSection B (fun p => ∑ j ∈ F, s j p) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using smoothSection_zero B
  | @insert j F hj ih =>
    have ht := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    intro p
    simpa [hj] using section_add_smoothAt B (hs j (Finset.mem_insert_self _ _) p) (ht p)

/-- Local finiteness turns a fiberwise finsum into a fixed finite sum locally. -/
theorem section_finsum_smooth {J : Type*} (s : J → (p : M) → E p)
    (hs : ∀ j, SmoothSection B (s j))
    (hlf : LocallyFinite (fun j => sectionSupport (s j))) :
    SmoothSection B (fun p => ∑ᶠ j, s j p) := by
  classical
  intro p
  obtain ⟨V, hV, hfin⟩ := hlf p
  apply section_smoothAt_congr B
    (section_finset_sum_smooth B hfin.toFinset s (fun j _ => hs j) p)
  filter_upwards [hV] with q hq
  symm
  apply finsum_eq_sum_of_support_subset
  intro j hj
  exact hfin.mem_toFinset.mpr ⟨q, subset_closure hj, hq⟩

/-- Patch actual local sections and the zero section on the complement.
The support bound uses a closed, locally finite union of weight supports. -/
theorem supported_extension :
    Specs.SmoothManifolds.Ch05.SectionExtension.supported_extensionType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B A U hA hU hAU s hs
  classical
  choose V hV hpV hVU t ht heq using hs
  let W : Option A → Set M
    | none => Aᶜ
    | some p => V p
  have hW : ∀ i, IsOpen (W i) := by
    intro i
    cases i with
    | none => exact hA.isOpen_compl
    | some p => exact hV p
  have hcover : ∀ p : M, ∃ i, p ∈ W i := by
    intro p
    by_cases hp : p ∈ A
    · exact ⟨some ⟨p, hp⟩, hpV ⟨p, hp⟩⟩
    · exact ⟨none, hp⟩
  obtain ⟨ρ, ⟨hsm, _, hlf, hsum⟩, hsub⟩ := exists_smooth_partition S W hW hcover
  let J : Option A → (p : M) → E p
    | none => fun _ => 0
    | some p => totalSection (t p)
  have hJ : ∀ i, ManifoldSmoothOn S.smoothStructure.val
      B.totalManifold.smoothStructure.val
      (fun p => (⟨p, J i p⟩ : TotalSpace (Euclidean r) E)) (W i) := by
    intro i
    cases i with
    | none => exact fun p _ => B.zero_smooth p
    | some p => exact totalSection_smooth B (hV p) (t p) (ht p)
  let G : (p : M) → E p := fun p => ∑ᶠ i, ρ i p • J i p
  have hterm (i : Option A) : SmoothSection B (fun p => ρ i p • J i p) :=
    weighted_section_smooth B (hsm i) (hJ i) (hsub i)
  have htermsupp (i : Option A) :
      sectionSupport (fun p => ρ i p • J i p) ⊆ sectionSupport (ρ i) := by
    apply closure_mono
    intro p hp
    by_contra hz
    exact hp (by simp [show ρ i p = 0 from not_ne_iff.mp hz])
  refine ⟨G, section_finsum_smooth B _ hterm (hlf.subset htermsupp), ?_, ?_⟩
  · intro p
    have hv (i : Option A) : ρ i p.val • J i p.val = ρ i p.val • s p := by
      by_cases hz : ρ i p.val = 0
      · simp [hz]
      have hi := hsub i (subset_closure hz)
      cases i with
      | none => exact False.elim (hi p.property)
      | some q => rw [show J (some q) p.val = s p from
          (totalSection_of_mem (t q) p.val hi).trans (heq q p hi)]
    change (∑ᶠ i, ρ i p.val • J i p.val) = s p
    simp_rw [hv]
    rw [← finsum_smul, hsum p.val, one_smul]
  · let C : Set M := ⋃ p : A, sectionSupport (ρ (some p))
    have hC : IsClosed C :=
      (hlf.comp_injective (Option.some_injective A)).isClosed_iUnion (fun _ => isClosed_closure)
    have hCU : C ⊆ U := by
      intro p hp
      obtain ⟨q, hq⟩ := mem_iUnion.mp hp
      exact hVU q (hsub (some q) hq)
    apply Subset.trans (closure_minimal (t := C) ?_ hC) hCU
    intro p hp
    by_contra hpC
    apply hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    cases i with
    | none => simp [J]
    | some q =>
      have hz : ρ (some q) p = 0 := Function.notMem_support.mp
        (fun h => hpC (mem_iUnion.mpr ⟨q, subset_closure h⟩))
      simp [hz]

/-- The unrestricted extension is the supported theorem with U = M. -/
theorem closed_extension :
    Specs.SmoothManifolds.Ch05.SectionExtension.closed_extensionType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B A hA s hs
  obtain ⟨t, ht, heq, _⟩ := supported_extension B A univ hA isOpen_univ (subset_univ A) s hs
  exact ⟨t, ht, heq⟩

/-- A cutoff of a local frame member is smooth after zero extension. -/
theorem frame_member_extension :
    Specs.SmoothManifolds.Ch05.SectionExtension.frame_member_extensionType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B U hU b p j
  obtain ⟨χ, hχ, _, hχ1, hχU, _⟩ := exists_local_bump S p.val U hU p.property
  let t : (q : M) → E q := fun q => χ q • totalSection (b.section_ j) q
  have ht : SmoothSection B t := weighted_section_smooth B hχ
    (totalSection_smooth B hU _ (b.smooth j)) hχU
  have hsupp : sectionSupport t ⊆ U := by
    apply Subset.trans (closure_mono ?_) hχU
    intro q hq
    by_contra hz
    exact hq (by simp [t, show χ q = 0 from not_ne_iff.mp hz])
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hχ1
  refine ⟨t, ht, hsupp, V ∩ U, hV.inter hU, ⟨hpV, p.property⟩,
    inter_subset_right, ?_⟩
  intro q hq
  change χ q.val • totalSection (b.section_ j) q.val = b.section_ j q
  rw [totalSection_of_mem _ _ q.property]
  change χ q.val • b.section_ j q = b.section_ j q
  rw [show χ q.val = 1 from hVsub hq.1, one_smul]

/-- Transport of the value of a dependent section along a base equality. -/
theorem transport_section (t : (p : M) → E p) {x y : M} (h : x = y) :
    h ▸ t x = t y := by
  cases h
  rfl

/-- The same identity for a section along a map. -/
theorem transport_along_map {N : Type*} {f : N → M} (s : (q : N) → E (f q))
    {x y : N} (h : x = y) : (congrArg f h) ▸ s x = s y := by
  cases h
  rfl

/-- Local extension along an embedding is performed in a bundle
trivialization, using the ambient Euclidean extension theorem for coefficients. -/
theorem embedded_local_extension :
    Specs.SmoothManifolds.Ch05.SectionExtension.embedded_local_extensionType.{u,v,w,z} := by
  intro n r a M _ S ι E _ _ _ B m b N _ T f hf s hs p
  classical
  obtain ⟨i, hi⟩ := B.covers (f p)
  have hopen : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸
    (B.trivialization i).open_baseSet
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf.1 x).1)
  let c : N → Euclidean r := fun x => ((B.trivialization i) ⟨f x, s x⟩).2
  have hc : ∀ x, f x ∈ B.baseSet i → VectorSmoothAt T.smoothStructure.val c x := by
    intro x hx
    exact FrameData.VectorSmoothAt.comp
      (g := fun q => (⟨f q, s q⟩ : TotalSpace (Euclidean r) E))
      (f := fun q : TotalSpace (Euclidean r) E => ((B.trivialization i) q).2)
      B.totalManifold.smoothStructure.property.1.1
      (Frames.trivializationCoordinates_smoothAt B i ⟨f x, s x⟩ hx) (hs x)
  obtain ⟨χ, hχ, _, hχ1, hχsub, _⟩ :=
    exists_local_bump T p (f ⁻¹' B.baseSet i) (hopen.preimage hfcont) hi
  let g : N → Euclidean r := fun x j => χ x * c x j
  have hg : ∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val g x := by
    intro x
    apply (manifoldContDiffToEuclideanAt_iff_coordinates _ _ _ x).mpr
    intro j
    apply scalarContDiff_mul_of_support_subset hχ (V := f ⁻¹' B.baseSet i) ?_ hχsub x
    intro y hy
    exact (scalarContDiffAt_iff _ _ _ _).mpr
      (show VectorSmoothAt T.smoothStructure.val (fun x => c x j) y from
        (hc y hy).postcomp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℝ) j).contDiff)
  obtain ⟨W, hW, hfpW, G, hG, heq⟩ :=
    SubmanifoldExtension.local_extension T S f hf g hg p
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp hχ1
  obtain ⟨H, hH⟩ := hf.2.2.2
  have hEmb : Topology.IsEmbedding f := by
    have hHf : (fun x => (H x).val) = f := funext hH
    rw [← hHf]
    exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  obtain ⟨D, hD, hpre⟩ := hEmb.isInducing.isOpen_iff.mp hO
  have hfpD : f p ∈ D := by
    change p ∈ f ⁻¹' D
    rw [hpre]
    exact hpO
  let L : Set M := (W ∩ D) ∩ B.baseSet i
  have hL : IsOpen L := (hW.inter hD).inter hopen
  let t : (q : M) → E q := fun q => (B.trivialization i).symm q (G q)
  have ht : ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun q => (⟨q, t q⟩ : TotalSpace (Euclidean r) E)) L := by
    intro q hq
    apply Frames.smoothAt_from_trivialization B S.smoothStructure.property.1 i hq.2
      (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 q)
      (show VectorSmoothAt S.smoothStructure.val G q from hG q hq.1.1)
      (fun _ => rfl)
    filter_upwards [hopen.mem_nhds hq.2] with y hy
    change (B.fiberCoordinates i y hy) ((B.fiberCoordinates i y hy).symm (G y)) = G y
    exact LinearEquiv.apply_symm_apply _ _
  refine ⟨L, hL, ⟨⟨hfpW, hfpD⟩, hi⟩, fun q => t q.val,
    (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ _ L hL).mp ht, ?_⟩
  intro q hq
  apply (B.fiberCoordinates i (f q) hq.2).injective
  change (B.fiberCoordinates i (f q) hq.2)
    ((B.fiberCoordinates i (f q) hq.2).symm (G (f q))) = c q
  rw [LinearEquiv.apply_symm_apply, heq q hq.1.1]
  have hqO : q ∈ O := by
    rw [← hpre]
    exact hq.1.2
  change (fun j => χ q * c q j) = c q
  funext j
  rw [show χ q = 1 from hOsub hqO, one_mul]

/-- Closed embedded images reduce to the closed-set extension theorem.
Transport is only in the actual fibers over equal base points. -/
theorem embedded_supported_extension :
    Specs.SmoothManifolds.Ch05.SectionExtension.embedded_supported_extensionType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B m b N _ T f hf hclosed U hU hsub s hs
  classical
  let source : range f → N := fun q => Classical.choose q.property
  have hsource : ∀ q : range f, f (source q) = q.val :=
    fun q => Classical.choose_spec q.property
  let sA : (q : range f) → E q.val := fun q => (hsource q) ▸ s (source q)
  have hsA : LocallyExtendable B (range f) U sA := by
    intro q
    obtain ⟨V, hV, hqV, t, ht, heq⟩ :=
      embedded_local_extension B T f hf s hs (source q)
    have hqV' : q.val ∈ V := hsource q ▸ hqV
    let W : Set M := V ∩ U
    have hW : IsOpen W := hV.inter hU
    let t0 := totalSection t
    have ht0 := totalSection_smooth B hV t ht
    refine ⟨W, hW, ⟨hqV', hsub q.property⟩, inter_subset_right,
      fun x => t0 x.val, ?_, ?_⟩
    · apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
        B.totalManifold.smoothStructure.val
        (fun x => (⟨x, t0 x⟩ : TotalSpace (Euclidean r) E)) W hW).mp
      intro x hx
      exact ht0 x hx.1
    · intro x hx
      change totalSection t x.val = (hsource x) ▸ s (source x)
      have hxe : totalSection t (f (source x)) = s (source x) := by
        rw [totalSection_of_mem t _ (show f (source x) ∈ V from (hsource x).symm ▸ hx.1)]
        exact heq (source x) ((hsource x).symm ▸ hx.1)
      calc
        totalSection t x.val = (hsource x) ▸ totalSection t (f (source x)) :=
          (transport_section (totalSection t) (hsource x)).symm
        _ = (hsource x) ▸ s (source x) :=
          congrArg (fun v => (hsource x) ▸ v) hxe
  obtain ⟨t, ht, heq, hsupp⟩ := supported_extension B (range f) U hclosed hU hsub sA hsA
  refine ⟨t, ht, ?_, hsupp⟩
  intro p
  let q : range f := ⟨f p, mem_range_self p⟩
  have hsp : source q = p := hf.2.1 (hsource q)
  have hval := heq q
  dsimp only [sA] at hval
  have hcast : ((hsource q) ▸ s (source q) : E q.val) = s p := by
    exact transport_along_map s hsp
  exact hval.trans hcast


/-- Specialize the general embedding result to the actual inclusion map. -/
theorem submanifold_supported_extension :
    Specs.SmoothManifolds.Ch05.SectionExtension.submanifold_supported_extensionType.{u,v,w} := by
  intro n r a M _ S ι E _ _ _ B m b A T hf hA U hU hAU s hs
  apply embedded_supported_extension B T Subtype.val hf
    (Subtype.range_val.symm ▸ hA) U hU (Subtype.range_val.symm ▸ hAU) s hs

end SmoothManifolds.SectionExtension
