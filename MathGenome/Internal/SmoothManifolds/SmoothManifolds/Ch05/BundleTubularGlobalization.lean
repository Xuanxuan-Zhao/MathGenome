import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleTubularGlobalization
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.InjectiveShrinking

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace SmoothManifolds.BundleTubularGlobalization
open ModelData AtlasData MapData BundleData Bundle Set Topology Filter
open scoped Topology
universe u v w z

/-- Compact-parameter radial shrinking, independent of any choice of metric
or uniform radius. This applies to a bundle scaling action once its continuity
has been established. -/
theorem radial_shrinking {X : Type u} [TopologicalSpace X]
    (scale : ℝ → X → X)
    (hscale : Continuous (fun z : ℝ × X => scale z.1 z.2))
    (hone : ∀ z, scale 1 z = z)
    (hmul : ∀ s t z, scale s (scale t z) = scale (s*t) z)
    (Z V : Set X) (hV : IsOpen V) (hZV : Z ⊆ V)
    (hfix : ∀ z ∈ Z, ∀ t : ℝ, scale t z = z) :
    ∃ U : Set X, IsOpen U ∧ U ⊆ V ∧ Z ⊆ U ∧
      ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, scale t z ∈ U := by
  let U : Set X := {z | ∀ t ∈ Icc (0 : ℝ) 1, scale t z ∈ V}
  let f : Icc (0 : ℝ) 1 × X → X := fun z => scale z.1.val z.2
  have hf : Continuous f := hscale.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hbad : IsClosed (Prod.snd '' (f ⁻¹' Vᶜ)) :=
    isClosedMap_snd_of_compactSpace _ (hV.isClosed_compl.preimage hf)
  have hU : IsOpen U := by
    have heq : U = (Prod.snd '' (f ⁻¹' Vᶜ))ᶜ := by
      ext z
      constructor
      · intro hz hb
        obtain ⟨⟨t, y⟩, hy, hyz⟩ := hb
        change y = z at hyz
        subst y
        exact hy (hz t.val t.property)
      · intro hz t ht
        by_contra hv
        exact hz ⟨(⟨t, ht⟩, z), hv, rfl⟩
    rw [heq]
    exact hbad.isOpen_compl
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [hone] using hz 1 ⟨zero_le_one, le_rfl⟩
  · intro z hz t ht
    rw [hfix z hz t]
    exact hZV hz
  · intro z hz t ht s hs
    rw [hmul]
    exact hz (s*t) ⟨mul_nonneg hs.1 ht.1,
      (mul_le_mul_of_nonneg_right hs.2 ht.1).trans (by simpa using ht.2)⟩

/-- Joint continuity of scalar multiplication follows from the specified
smooth bundle parametrizations, rather than from a separately assumed topology
on the fibers. -/
theorem bundle_scale_continuous
    {d r : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    {T : SmoothManifold d a X} {ι : Type v} {E : X → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle T r ι E) :
    Continuous (fun z : ℝ × Bundle.TotalSpace (Euclidean r) E =>
      (⟨z.2.proj, z.1 • z.2.snd⟩ : Bundle.TotalSpace (Euclidean r) E)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨i, hi⟩ := B.covers z.2.proj
  let e := B.trivialization i
  have hi' : z.2.proj ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hi
  have hp : Continuous (Bundle.TotalSpace.proj : Bundle.TotalSpace (Euclidean r) E → X) :=
    continuous_iff_continuousAt.mpr (fun y => (B.projection_smooth y).1)
  let g : ℝ × Bundle.TotalSpace (Euclidean r) E → X × (ℝ × Euclidean r) :=
    fun y => (y.2.proj, y.1, (e y.2).2)
  have hg : ContinuousAt g z :=
    (hp.continuousAt.comp continuousAt_snd).prodMk
      (continuousAt_fst.prodMk
        ((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.mpr hi')).snd.comp continuousAt_snd))
  have hcont := ((B.smul_smooth i (g z) hi).1).comp hg
  apply hcont.congr_of_eventuallyEq
  have hbase : ∀ᶠ y : ℝ × Bundle.TotalSpace (Euclidean r) E in 𝓝 z,
      y.2.proj ∈ e.baseSet :=
    (hp.comp continuous_snd).continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hi')
  filter_upwards [hbase] with y hy
  change (⟨y.2.proj, y.1 • y.2.snd⟩ :
    Bundle.TotalSpace (Euclidean r) E) = ⟨y.2.proj, y.1 • e.symm y.2.proj (e y.2).2⟩
  rw [e.symm_apply_apply_mk hy]

/-- A locally compact embedded subspace of a Hausdorff space is locally closed. -/
theorem embedding_range_locallyClosed {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace X] [T2Space Y]
    {f : X → Y} (hf : IsEmbedding f) : IsLocallyClosed (range f) := by
  apply isLocallyClosed_iff_isLocallyClosedAt.mpr
  rintro _ ⟨x, rfl⟩
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨U, hU, hpre⟩ := hf.isInducing.isOpen_iff.mp (isOpen_interior (s := K))
  have hxU : f x ∈ U := by
    change x ∈ f ⁻¹' U
    rw [hpre]
    exact mem_interior_iff_mem_nhds.mpr hxK
  apply isLocallyClosedAt_iff_exists_isClosed_eventuallyEqSet.mpr
  refine ⟨f '' K, (hK.image hf.continuous).isClosed, ?_⟩
  filter_upwards [hU.mem_nhds hxU] with y hy
  apply propext
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, interior_subset (show z ∈ interior K by rw [← hpre]; exact hy), rfl⟩
  · rintro ⟨z, _, rfl⟩
    exact ⟨z, rfl⟩

/-- Restrict the target of a smooth germ to an open set containing its values. -/
theorem smoothAt_codRestrict {m n : ℕ} {a b : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set (ModelChart m a X)} {B : Set (ModelChart n b Y)}
    {U : Set Y} (hU : IsOpen U) {f : X → U} {x : X}
    (hf : ManifoldSmoothAt A B (fun y => (f y).val) x) :
    ManifoldSmoothAt A (openSubsetAtlas B U hU) f x := by
  refine ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hf.1, ?_⟩
  rintro e he _ ⟨hne, d, hd, rfl⟩ hx hfx
  exact hf.2 e he d hd hx
    (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hfx)

/-- Restrict the source of a smooth germ along an open inclusion. -/
theorem smoothAt_domRestrict {m n : ℕ} {a b : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set (ModelChart m a X)} {B : Set (ModelChart n b Y)}
    {U : Set X} (hU : IsOpen U) {f : X → Y} {x : U}
    (hf : ManifoldSmoothAt A B f x.val) :
    ManifoldSmoothAt (openSubsetAtlas A U hU) B (fun y : U => f y.val) x := by
  refine ⟨hf.1.comp continuousAt_subtype_val, ?_⟩
  rintro _ ⟨hne, e, he, rfl⟩ d hd hx hfx
  exact LocalCoordinateExtension.precomp
    (hf.2 e he d hd
      (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx) hfx)
    continuousAt_subtype_val rfl

/-- Local homeomorphisms carry open subsets of their locus to open sets. -/
theorem open_image_of_local_inverses {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (F : X → Y) (O : Set X)
    (hl : ∀ x ∈ O, ∃ e : OpenPartialHomeomorph X Y,
      x ∈ e.source ∧ EqOn e F e.source)
    {U : Set X} (hU : IsOpen U) (hUO : U ⊆ O) : IsOpen (F '' U) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, he⟩ := hl x (hUO hx)
  refine ⟨e '' (e.source ∩ U), ?_, e.isOpen_image_source_inter hU, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz.2, (he hz.1).symm⟩
  · exact ⟨x, ⟨hxe, hx⟩, he hxe⟩

/-- An embedded zero section admits a neighborhood where F is injective.
The map F is only required to be continuous on its open domain. -/
theorem injective_near_zero
    {d r n : ℕ} {P : Type u} {M : Type v}
    [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold d .euclidean P) (S : SmoothManifold n .euclidean M)
    {ι : Type w} {E : P → Type z}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle T r ι E) (i : P → M)
    (O : Set (TotalSpace (Euclidean r) E)) (F : TotalSpace (Euclidean r) E → M)
    (hi : IsEmbedding i) (hO : IsOpen O)
    (hzO : ∀ p, (⟨p, 0⟩ : TotalSpace (Euclidean r) E) ∈ O)
    (hzero : ∀ p, F (⟨p, 0⟩ : TotalSpace (Euclidean r) E) = i p)
    (hF : Continuous (fun x : O => F x.val))
    (hl : ∀ x ∈ O, ∃ e : OpenPartialHomeomorph (TotalSpace (Euclidean r) E) M,
      x ∈ e.source ∧ EqOn e F e.source) :
    ∃ V : Set (TotalSpace (Euclidean r) E), IsOpen V ∧ V ⊆ O ∧
      (∀ p, (⟨p, 0⟩ : TotalSpace (Euclidean r) E) ∈ V) ∧ InjOn F V := by
  letI := SmoothManifolds.TopologicalManifold.locallyCompactSpace T.topologicalManifold
  letI := S.topologicalManifold.hausdorff
  let zero : P → O := fun p => ⟨⟨p, 0⟩, hzO p⟩
  let f : O → M := fun x => F x.val
  have hp : Continuous (fun x : O => x.val.proj) :=
    (continuous_iff_continuousAt.mpr fun x => (B.projection_smooth x).1).comp
      continuous_subtype_val
  have hz : IsEmbedding zero :=
    Function.LeftInverse.isEmbedding (fun p => rfl) hp
      ((continuous_iff_continuousAt.mpr fun p => (B.zero_smooth p).1).subtype_mk _)
  have he : IsEmbedding (fun x : range zero => f x.val) := by
    have heq : (fun x : range zero => f x.val) = i ∘ hz.toHomeomorph.symm := by
      funext x
      rcases x with ⟨x, p, rfl⟩
      simpa [f, zero] using hzero p
    rw [heq]
    exact hi.comp hz.toHomeomorph.symm.isEmbedding
  have him : f '' range zero = range i := by
    ext y
    constructor
    · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, (hzero p).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨zero p, ⟨p, rfl⟩, hzero p⟩
  have hc : IsLocallyClosed (f '' range zero) := by
    rw [him]
    exact embedding_range_locallyClosed hi
  have hlocal : ∀ x ∈ range zero, ∃ U : Set O, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
    intro x hx
    obtain ⟨e, hxe, he⟩ := hl x.val x.property
    refine ⟨Subtype.val ⁻¹' e.source, e.open_source.preimage continuous_subtype_val, hxe, ?_⟩
    intro y hy z hz hyz
    apply Subtype.ext
    apply e.injOn hy hz
    exact (he hy).trans (hyz.trans (he hz).symm)
  obtain ⟨U, hU, hzU, hUi⟩ := injective_shrinking S.topologicalManifold f
    (range zero) hF he hc hlocal
  refine ⟨Subtype.val '' U, hO.isOpenMap_subtype_val U hU, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact x.property
  · intro p
    exact ⟨zero p, hzU ⟨p, rfl⟩, rfl⟩
  · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hab
    exact congrArg Subtype.val (hUi ha hb hab)

/-- The globalization and radial shrinking step of the abstract tubular theorem. -/
theorem bundle_tubular_globalization :
    Specs.SmoothManifolds.Ch05.BundleTubularGlobalization.bundle_tubular_globalizationType.{u,v,w,z} := by
  classical
  intro d r n P M _ _ T S ι E _ _ _ B i O F hi hO hzO hzero hFs hl
  have hl' : ∀ x ∈ O, ∃ e : OpenPartialHomeomorph (TotalSpace (Euclidean r) E) M,
      x ∈ e.source ∧ EqOn e F e.source := by
    intro x hx
    obtain ⟨e, hxe, _, he, _⟩ := hl x hx
    exact ⟨e, hxe, he⟩
  have hFO : Continuous (fun x : O => F x.val) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hFs x.val x.property).1.comp continuousAt_subtype_val
  obtain ⟨A, hA, hAO, hzA, hAi⟩ := injective_near_zero T S B i O F hi hO hzO hzero hFO hl'
  let scale : ℝ → TotalSpace (Euclidean r) E → TotalSpace (Euclidean r) E :=
    fun t x => ⟨x.proj, t • x.snd⟩
  obtain ⟨V, hV, hVA, hzV, hstar⟩ := radial_shrinking scale (bundle_scale_continuous B)
    (by intro x; simp [scale])
    (by intro s t x; dsimp [scale]; rw [mul_smul])
    (range (fun p : P => (⟨p, 0⟩ : TotalSpace (Euclidean r) E))) A hA
    (by rintro _ ⟨p, rfl⟩; exact hzA p)
    (by rintro _ ⟨p, rfl⟩ t; simp [scale])
  have hVO : V ⊆ O := hVA.trans hAO
  have hVi : InjOn F V := hAi.mono hVA
  let W : Set M := F '' V
  have hW : IsOpen W := open_image_of_local_inverses F O hl' hV hVO
  let f : V → W := fun x => ⟨F x.val, ⟨x.val, x.property, rfl⟩⟩
  have hfs : ManifoldSmooth (openSubsetAtlas B.totalManifold.smoothStructure.val V hV)
      (openSubsetAtlas S.smoothStructure.val W hW) f := by
    intro x
    exact smoothAt_codRestrict hW (smoothAt_domRestrict hV (hFs x.val (hVO x.property)))
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hVi x.property y.property (congrArg Subtype.val hxy))
    · rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hfo : IsOpenMap f := by
    intro U hU
    have hU' : IsOpen ((Subtype.val : V → TotalSpace (Euclidean r) E) '' U) :=
      hV.isOpenMap_subtype_val U hU
    have hUO : (Subtype.val : V → TotalSpace (Euclidean r) E) '' U ⊆ O := by
      rintro _ ⟨x, hx, rfl⟩
      exact hVO x.property
    have heq : f '' U = (Subtype.val : W → M) ⁻¹'
        (F '' ((Subtype.val : V → TotalSpace (Euclidean r) E) '' U)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
    rw [heq]
    exact (open_image_of_local_inverses F O hl' hU' hUO).preimage continuous_subtype_val
  let h : V ≃ₜ W := IsHomeomorph.homeomorph f
    ⟨continuous_iff_continuousAt.mpr (fun x => (hfs x).1), hfo, hbij⟩
  have hval : ∀ x : V, (h x).val = F x.val := fun x => rfl
  have hinv : ∀ y : W, F (h.symm y).val = y.val := by
    intro y
    exact (hval (h.symm y)).symm.trans (congrArg Subtype.val (h.apply_symm_apply y))
  refine ⟨V, W, hV, hW, h, hVO, (fun p => hzV ⟨p, rfl⟩), ?_, hval, hfs, ?_, hstar⟩
  · rintro _ ⟨p, rfl⟩
    exact ⟨⟨p, 0⟩, hzV ⟨p, rfl⟩, hzero p⟩
  · intro y
    obtain ⟨e, hxe, heO, heF, heInv⟩ := hl (h.symm y).val (hVO (h.symm y).property)
    have hey : e (h.symm y).val = y.val := (heF hxe).trans (hinv y)
    have hyt : y.val ∈ e.target := hey ▸ e.map_source hxe
    apply smoothAt_codRestrict hV
    have hsm := smoothAt_domRestrict hW (heInv y.val hyt)
    apply manifoldContDiffAt_congr hsm
    have hn : ∀ᶠ q : W in 𝓝 y, (h.symm q).val ∈ e.source :=
      (continuous_subtype_val.comp h.symm.continuous).continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds hxe)
    filter_upwards [hn] with q hq
    have heq : e (h.symm q).val = q.val := (heF hq).trans (hinv q)
    rw [← heq, e.left_inv hq]

end SmoothManifolds.BundleTubularGlobalization
