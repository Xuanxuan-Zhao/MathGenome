import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.FreeProperSlices
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SliceStructures
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorConstantRank

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SmoothManifolds.FreeProperSlices
open ModelData AtlasData MapData ProductData BoundaryData MapClassData FreeProperSliceData
open TangentData DifferentialData InteriorRankData
open Set Filter
open scoped Topology
universe u v

/-- The product witnesses in the action data add no existence assumption. -/
theorem boundarylessProduct_nonempty {d n : ℕ} {a b : ModelKind}
    {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (hA : intrinsicBoundary A = ∅) (hB : intrinsicBoundary B = ∅) :
    Nonempty (BoundarylessProduct A B) := by
  obtain ⟨E, F, hAE, hEA, hBF, hFB, C, P, _, hP, _⟩ :=
    exists_product_boundaryless A B hA hB
  exact ⟨⟨E, F, hAE, hEA, hBF, hFB, C, P, hP⟩⟩

/-- Freeness makes each orbit map injective already as a map of sets. -/
theorem orbit_map_injective {G : Type u} {M : Type v}
    [Group G] [MulAction G M] (hfree : FreeAction G M) (p : M) :
    Function.Injective (fun g : G => g • p) := by
  intro g h heq
  change g • p = h • p at heq
  have he : h⁻¹ * g = 1 := hfree _ p (by rw [mul_smul, heq, inv_smul_smul])
  simpa using congrArg (fun k => h * k) he

/-- Properness of the action implies properness of each orbit map. This uses
the compact set {p} × K, with no compactness assumption on the group. -/
theorem orbit_map_isProperMap {G : Type u} {M : Type v}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [T2Space M] [LocallyCompactSpace M]
    (hcont : Continuous (fun z : G × M => z.1 • z.2))
    (hproper : IsProper (actionTransport (G := G) (M := M))) (p : M) :
    IsProperMap (fun g : G => g • p) := by
  refine isProperMap_iff_isCompact_preimage.mpr
    ⟨hcont.comp (continuous_id.prodMk continuous_const), ?_⟩
  intro K hK
  have hC := hproper ({p} ×ˢ K) (isCompact_singleton.prod hK)
  convert hC.image (continuous_fst : Continuous (Prod.fst : G × M → G)) using 1
  ext g
  constructor
  · intro hg
    exact ⟨(g, p), ⟨mem_singleton p, hg⟩, rfl⟩
  · rintro ⟨⟨h, x⟩, hx, rfl⟩
    have hxp : x = p := hx.1
    have hmem : h • x ∈ K := hx.2
    change h • p ∈ K
    rwa [hxp] at hmem

/-- Properness closes the image of the part of the action map outside W.
The complement of that image is a neighborhood of (p,p), by freeness. -/
theorem small_transporters :
    Specs.SmoothManifolds.Ch08.FreeProperSlices.small_transportersType.{u,v} := by
  intro G M _ _ _ _ _ _ hcont hfree hproper p W hW h1
  have hc : Continuous (actionTransport (G := G) (M := M)) :=
    continuous_snd.prodMk hcont
  have hp : IsProperMap (actionTransport (G := G) (M := M)) :=
    isProperMap_iff_isCompact_preimage.mpr ⟨hc, fun K hK => hproper K hK⟩
  let C : Set (M × M) := actionTransport '' ((Wᶜ) ×ˢ (univ : Set M))
  have hC : IsClosed C := hp.isClosedMap _ (hW.isClosed_compl.prod isClosed_univ)
  have hpp : (p, p) ∈ Cᶜ := by
    rintro ⟨⟨g, x⟩, ⟨hg, _⟩, heq⟩
    have hx : x = p := congrArg Prod.fst heq
    have hgp : g • p = p := by simpa [actionTransport, hx] using congrArg Prod.snd heq
    exact hg (hfree g p hgp ▸ h1)
  obtain ⟨U₁, U₂, hU₁, hp₁, hU₂, hp₂, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hC.isOpen_compl.mem_nhds hpp)
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hp₁, hp₂⟩, ?_⟩
  intro g x y hx hy hxy
  by_contra hg
  have hnot : (x, y) ∉ C := hsub (show (x, y) ∈ U₁ ×ˢ U₂ from ⟨hx.1, hy.2⟩)
  apply hnot
  exact ⟨(g, x), ⟨hg, mem_univ x⟩, by simp [actionTransport, hxy]⟩

/-- For the restricted slice, a group element carrying one slice point to
another must be the identity; both points must coincide. -/
theorem no_transport_of_local_injective {G : Type u} {M : Type v}
    [Group G] [MulAction G M] (W : Set G) (s₁ U : Set M) (h1 : (1 : G) ∈ W)
    (hsmall : ∀ (g : G) (x y : M), x ∈ U → y ∈ U → g • x = y → g ∈ W)
    (hinj : Set.InjOn (fun z : G × M => z.1 • z.2) (W ×ˢ s₁))
    (g : G) (x y : M) (hx : x ∈ s₁ ∩ U) (hy : y ∈ s₁ ∩ U) (hxy : g • x = y) :
    g = 1 ∧ x = y := by
  have heq : (g, x) = (1, y) :=
    hinj ⟨hsmall g x y hx.2 hy.2 hxy, hx.1⟩ ⟨h1, hy.1⟩ (by simpa using hxy)
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

/-- Unique intersection with every orbit gives uniqueness of both product
coordinates, by applying the no-transporter condition to g'⁻¹g. -/
theorem action_product_bijective {G : Type u} {M : Type v}
    [Group G] [MulAction G M] (s : Set M)
    (hsep : ∀ (g : G) (x y : M), x ∈ s → y ∈ s → g • x = y → g = 1 ∧ x = y) :
    Function.Bijective (fun z : G × s =>
      (⟨z.1 • z.2.val, ⟨z.1, z.2.val, z.2.property, rfl⟩⟩ : saturation (G := G) s)) := by
  constructor
  · rintro ⟨g, x⟩ ⟨h, y⟩ heq
    have hv : g • x.val = h • y.val := congrArg Subtype.val heq
    have hxy : (h⁻¹ * g) • x.val = y.val := by
      rw [mul_smul, hv, inv_smul_smul]
    obtain ⟨hgh, hxy'⟩ := hsep (h⁻¹ * g) x.val y.val x.property y.property hxy
    have hgh' : g = h := by simpa using congrArg (fun k => h * k) hgh
    exact Prod.ext hgh' (Subtype.ext hxy')
  · rintro ⟨y, g, x, hx, hxy⟩
    exact ⟨(g, ⟨x, hx⟩), Subtype.ext hxy⟩

/-- Orbit representatives are unique even if the group element is not recorded. -/
theorem orbit_intersection_unique {G : Type u} {M : Type v}
    [Group G] [MulAction G M] (s : Set M)
    (hsep : ∀ (g : G) (x y : M), x ∈ s → y ∈ s → g • x = y → g = 1 ∧ x = y)
    (y : M) (hy : y ∈ saturation (G := G) s) :
    ∃! x : s, ∃ g : G, g • x.val = y := by
  obtain ⟨g, x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ⟨g, hxy⟩, ?_⟩
  rintro z ⟨h, hzy⟩
  have hz : (g⁻¹ * h) • z.val = x := by
    rw [mul_smul, hzy, ← hxy, inv_smul_smul]
  exact Subtype.ext (hsep _ _ _ z.property hx hz).2

/-- The full properness/freeness shrinking step of the source proof. -/
theorem shrink_slice : Specs.SmoothManifolds.Ch08.FreeProperSlices.shrink_sliceType.{u,v} := by
  intro G M _ _ _ _ _ _ hcont hfree hproper p W s₁ hW h1 hp hinj
  obtain ⟨U, hU, hpU, hsmall⟩ := small_transporters hcont hfree hproper p W hW h1
  have hsep := no_transport_of_local_injective W s₁ U h1 hsmall hinj
  exact ⟨U, hU, hpU, ⟨hp, hpU⟩, hsep,
    action_product_bijective (s₁ ∩ U) hsep, orbit_intersection_unique (s₁ ∩ U) hsep⟩

/-- Translate a product chart at the identity to every point of G × s.
No compactness of either factor is used. -/
theorem localHomeomorph_of_product_chart {G : Type u} {M : Type v}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [SeparatelyContinuousMul G] [ContinuousConstSMul G M]
    (s : Set M) (W : Set G) (h1 : (1 : G) ∈ W)
    (h : OpenPartialHomeomorph (G × s) M) (hsource : h.source = W ×ˢ univ)
    (heq : EqOn h (fun z : G × s => z.1 • z.2.val) h.source) :
    IsLocalHomeomorph (fun z : G × s => z.1 • z.2.val) := by
  apply IsLocalHomeomorph.mk
  rintro ⟨g, x⟩
  let L : (G × s) ≃ₜ (G × s) :=
    (Homeomorph.mulLeft g⁻¹).prodCongr (Homeomorph.refl s)
  let e := (L.transOpenPartialHomeomorph h).transHomeomorph (Homeomorph.smul g)
  have hx : (g, x) ∈ e.source := by
    change (g⁻¹ * g, x) ∈ h.source
    rw [hsource]
    exact ⟨by simpa using h1, mem_univ x⟩
  refine ⟨e, hx, ?_⟩
  intro z hz
  change z.1 • z.2.val = g • h (g⁻¹ * z.1, z.2)
  have hz' : (g⁻¹ * z.1, z.2) ∈ h.source := hz
  rw [heq hz']
  simp [mul_smul]

/-- Openness and the actual homeomorphism once the slice has no transporters. -/
theorem homeomorph_of_separated_slice {G : Type u} {M : Type v}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (s : Set M)
    (hsep : ∀ (g : G) (x y : M), x ∈ s → y ∈ s → g • x = y → g = 1 ∧ x = y)
    (hloc : IsLocalHomeomorph (fun z : G × s => z.1 • z.2.val)) :
    IsOpen (saturation (G := G) s) ∧
      ∃ H : (G × s) ≃ₜ saturation (G := G) s, ∀ z, (H z).val = z.1 • z.2.val := by
  have hr : (fun z : G × s => z.1 • z.2.val) '' univ = saturation (G := G) s := by
    ext y
    constructor
    · rintro ⟨⟨g, x⟩, _, rfl⟩
      exact ⟨g, x.val, x.property, rfl⟩
    · rintro ⟨g, x, hx, rfl⟩
      exact ⟨(g, ⟨x, hx⟩), mem_univ _, rfl⟩
  refine ⟨hr ▸ hloc.isOpenMap _ isOpen_univ, ?_⟩
  let f : G × s → saturation (G := G) s :=
    fun z => ⟨z.1 • z.2.val, ⟨z.1, z.2.val, z.2.property, rfl⟩⟩
  have hc : Continuous f := hloc.continuous.subtype_mk _
  have ho : IsOpenMap f := hloc.isOpenMap.subtype_mk _
  exact ⟨(Equiv.ofBijective f (action_product_bijective s hsep)).toHomeomorphOfContinuousOpen hc ho,
    fun _ => rfl⟩

/-- Properness, local injectivity and translations yield the global topological
product over an open saturated neighborhood of the entire orbit. -/
theorem topological_trivialization :
    Specs.SmoothManifolds.Ch08.FreeProperSlices.topological_trivializationType.{u,v} := by
  intro G M _ _ _ _ _ _ _ _ hcont hfree hproper p W s₁ hW h1 hp h hsource heq
  have hinj : Set.InjOn (fun z : G × M => z.1 • z.2) (W ×ˢ s₁) := by
    rintro ⟨g, x⟩ hx ⟨k, y⟩ hy hxy
    have hx' : (g, (⟨x, hx.2⟩ : s₁)) ∈ h.source := hsource ▸ ⟨hx.1, mem_univ _⟩
    have hy' : (k, (⟨y, hy.2⟩ : s₁)) ∈ h.source := hsource ▸ ⟨hy.1, mem_univ _⟩
    have he := h.injOn hx' hy' ((heq hx').trans (hxy.trans (heq hy').symm))
    exact Prod.ext (congrArg (fun z : G × s₁ => z.1) he)
      (congrArg (fun z : G × s₁ => z.2.val) he)
  obtain ⟨U, hU, hpU, hsmall⟩ := small_transporters hcont hfree hproper p W hW h1
  have hsep := no_transport_of_local_injective W s₁ U h1 hsmall hinj
  have hloc₁ := localHomeomorph_of_product_chart s₁ W h1 h hsource heq
  have hinc : Topology.IsOpenEmbedding (Set.inclusion (s := s₁ ∩ U) inter_subset_left) := by
    apply Topology.IsOpenEmbedding.inclusion
    convert hU.preimage (continuous_subtype_val : Continuous (Subtype.val : s₁ → M)) using 1
    ext x
    simp
  have hincP := (Homeomorph.refl G).isOpenEmbedding.prodMap hinc
  have hloc : IsLocalHomeomorph (fun z : G × ↥(s₁ ∩ U) => z.1 • z.2.val) :=
    hloc₁.comp hincP.isLocalHomeomorph
  obtain ⟨hopen, H, hH⟩ := homeomorph_of_separated_slice (s₁ ∩ U) hsep hloc
  exact ⟨U, hU, hpU, ⟨hp, hpU⟩, hopen, ⟨H, hH⟩,
    orbit_intersection_unique (s₁ ∩ U) hsep⟩

/-- The topological group and continuous action hypotheses used in the
globalization are consequences of the original smooth hypotheses. -/
theorem smoothLieAction_topological {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M} (H : SmoothLieAction A B) :
    IsTopologicalGroup G ∧ ContinuousSMul G M := by
  exact ⟨{
    continuous_mul := continuous_iff_continuousAt.mpr (fun z => (H.smooth_mul z).1)
    continuous_inv := continuous_iff_continuousAt.mpr (fun g => (H.smooth_inv g).1) },
    ⟨continuous_iff_continuousAt.mpr (fun z => (H.smooth_action z).1)⟩⟩

/-- The shrinking lemma applies directly to the original manifold data,
without adding a topological properness or continuity hypothesis. -/
theorem small_transporters_of_smooth {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (H : SmoothLieAction A B) (hfree : FreeAction G M)
    (hproper : IsProper (actionTransport (G := G) (M := M)))
    (p : M) (W : Set G) (hW : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ (g : G) (x y : M), x ∈ U → y ∈ U → g • x = y → g ∈ W := by
  let _ : T2Space M := B.topologicalManifold.hausdorff
  let _ : LocallyCompactSpace M :=
    _root_.SmoothManifolds.TopologicalManifold.locallyCompactSpace B.topologicalManifold
  exact small_transporters (continuous_iff_continuousAt.mpr
    (fun z => (H.smooth_action z).1)) hfree hproper p W hW h1

/-- Composition in the shared smooth-map interface. -/
theorem smooth_comp {l m n : ℕ} {a b c : ModelKind} {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : SmoothManifold l a X} {B : SmoothManifold m b Y} {C : SmoothManifold n c Z}
    {f : X → Y} {g : Y → Z} (hf : IsSmoothMap A B f) (hg : IsSmoothMap B C g) :
    IsSmoothMap A C (g ∘ f) :=
  manifoldContDiff_comp _ _ _ _ B.smoothStructure.property.1.1 f g hf hg

/-- Constant maps satisfy the local ambient-extension convention. -/
theorem smooth_const {m n : ℕ} {a b : ModelKind} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : SmoothManifold m a X) (B : SmoothManifold n b Y) (y : Y) :
    IsSmoothMap A B (fun _ => y) := by
  intro x
  refine ⟨continuousAt_const, ?_⟩
  intro e he d hd hx hy
  exact ⟨univ, isOpen_univ, mem_univ _, fun _ => (d y).val,
    contDiff_const.contDiffOn, Filter.Eventually.of_forall (fun _ => rfl)⟩

/-- Pairing into any of the selected boundaryless product structures. -/
theorem smooth_pair {l m n : ℕ} {a b c : ModelKind} {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : SmoothManifold l a X} {B : SmoothManifold m b Y} {C : SmoothManifold n c Z}
    (P : BoundarylessProduct B C) {f : X → Y} {g : X → Z}
    (hf : IsSmoothMap A B f) (hg : IsSmoothMap A C g) :
    IsSmoothMap A P.manifold (fun x => (f x, g x)) :=
  (differential_pair P.left P.right A P.coordinates P.manifold P.atlas_eq f g
    (smooth_comp (f := f) (g := id) hf P.left_to)
    (smooth_comp (f := g) (g := id) hg P.right_to)).1

/-- Replace the factor presentations without changing the selected product
manifold. The four identities express equality of the smooth structures. -/
def rebase_boundarylessProduct {d n : ℕ} {a b a' b' : ModelKind}
    {G M : Type u} [TopologicalSpace G] [TopologicalSpace M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (P : BoundarylessProduct A B) (A' : SmoothManifold d a' G)
    (B' : SmoothManifold n b' M)
    (hAA' : IsSmoothMap A A' id) (hA'A : IsSmoothMap A' A id)
    (hBB' : IsSmoothMap B B' id) (hB'B : IsSmoothMap B' B id) :
    BoundarylessProduct A' B' where
  left := P.left
  right := P.right
  left_to := smooth_comp hA'A P.left_to
  left_from := smooth_comp P.left_from hAA'
  right_to := smooth_comp hB'B P.right_to
  right_from := smooth_comp P.right_from hBB'
  coordinates := P.coordinates
  manifold := P.manifold
  atlas_eq := P.atlas_eq

/-- The given action also has the compatible Euclidean presentations supplied
by its ordinary boundaryless product data. No new smoothness is assumed. -/
def smoothLieAction_euclidean {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) :
    SmoothLieAction H.actionProduct.left H.actionProduct.right where
  group_boundary := intrinsicBoundary_euclidean _
  space_boundary := intrinsicBoundary_euclidean _
  groupProduct := rebase_boundarylessProduct H.groupProduct
    H.actionProduct.left H.actionProduct.left
    H.actionProduct.left_to H.actionProduct.left_from
    H.actionProduct.left_to H.actionProduct.left_from
  actionProduct := rebase_boundarylessProduct H.actionProduct
    H.actionProduct.left H.actionProduct.right
    H.actionProduct.left_to H.actionProduct.left_from
    H.actionProduct.right_to H.actionProduct.right_from
  smooth_mul := smooth_comp H.smooth_mul H.actionProduct.left_to
  smooth_inv := smooth_comp (f := fun g : G => g⁻¹) (g := id)
    (smooth_comp (f := id) (g := fun g : G => g⁻¹)
      H.actionProduct.left_from H.smooth_inv) H.actionProduct.left_to
  smooth_action := smooth_comp H.smooth_action H.actionProduct.right_to

/-- The orbit map is smooth with respect to the original smooth structures. -/
theorem smooth_orbit_map {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (p : M) : IsSmoothMap A B (fun g : G => g • p) :=
  smooth_comp (smooth_pair H.actionProduct
    (manifoldContDiff_id _ _ A.smoothStructure.property.1) (smooth_const A B p)) H.smooth_action

/-- Every left translation is smooth, directly from smooth multiplication. -/
theorem smooth_mulLeft {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (g : G) : IsSmoothMap A A (fun h : G => g * h) :=
  smooth_comp (g := fun z : G × G => z.1 * z.2)
    (smooth_pair H.groupProduct (smooth_const A A g)
      (manifoldContDiff_id _ _ A.smoothStructure.property.1)) H.smooth_mul

/-- Each fixed group element acts by a smooth map. -/
theorem smooth_smul {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (g : G) : IsSmoothMap B B (fun p : M => g • p) :=
  smooth_comp (g := fun z : G × M => z.1 • z.2)
    (smooth_pair H.actionProduct (smooth_const B A g)
      (manifoldContDiff_id _ _ B.smoothStructure.property.1)) H.smooth_action

/-- Left translation with its actual inverse is a diffeomorphism. -/
def mulLeft_diffeomorph {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (g : G) :
    Diffeomorph A.smoothStructure.val A.smoothStructure.val where
  toEquiv := Equiv.mulLeft g
  contDiff_toFun := smooth_mulLeft H g
  contDiff_invFun := smooth_mulLeft H g⁻¹

/-- The inverse action is action by the inverse group element. -/
def smul_diffeomorph {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (g : G) :
    Diffeomorph B.smoothStructure.val B.smoothStructure.val where
  toEquiv := MulAction.toPerm g
  contDiff_toFun := smooth_smul H g
  contDiff_invFun := smooth_smul H g⁻¹

/-- Precomposition with a diffeomorphism preserves rank, by the intrinsic
chain rule and a linear isomorphism of the differential images. -/
theorem rankAt_precomp_diffeomorph {l m n : ℕ} {a b c : ModelKind} {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold l a X) (B : SmoothManifold m b Y) (C : SmoothManifold n c Z)
    (h : Diffeomorph A.smoothStructure.val B.smoothStructure.val)
    (f : Y → Z) (hf : IsSmoothMap B C f) (p : X) :
    rankAt A C (f ∘ h.toEquiv) p = rankAt B C f (h.toEquiv p) := by
  obtain ⟨E, hE⟩ := differential_diffeomorph A B h p
  obtain ⟨L, hL, _⟩ := differential_exists B C f hf (h.toEquiv p)
  have hcomp := differential_comp A B C h.toEquiv f h.contDiff_toFun hf p
    E.toLinearMap L hE hL
  have h₁ := (MapClasses.smooth_tangent_invariants A C _
    (smooth_comp h.contDiff_toFun hf) p _ hcomp).1
  have h₂ := (MapClasses.smooth_tangent_invariants B C f hf _ L hL).1
  rw [h₁, h₂]
  exact (MapClasses.linear_invariants
    (V := TangentSpace A p) (V' := TangentSpace B (h.toEquiv p))
    (W := TangentSpace C (f (h.toEquiv p)))
    (W' := TangentSpace C (f (h.toEquiv p)))
    E (LinearEquiv.refl ℝ (TangentSpace C (f (h.toEquiv p))))
    (L.comp E.toLinearMap) L (fun _ => rfl)).1

/-- Postcomposition with a diffeomorphism preserves rank. -/
theorem rankAt_postcomp_diffeomorph {l m n : ℕ} {a b c : ModelKind} {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold l a X) (B : SmoothManifold m b Y) (C : SmoothManifold n c Z)
    (f : X → Y) (hf : IsSmoothMap A B f)
    (h : Diffeomorph B.smoothStructure.val C.smoothStructure.val) (p : X) :
    rankAt A C (h.toEquiv ∘ f) p = rankAt A B f p := by
  obtain ⟨E, hE⟩ := differential_diffeomorph B C h (f p)
  obtain ⟨L, hL, _⟩ := differential_exists A B f hf p
  have hcomp := differential_comp A B C f h.toEquiv hf h.contDiff_toFun p
    L E.toLinearMap hL hE
  have h₁ := (MapClasses.smooth_tangent_invariants A C _
    (smooth_comp hf h.contDiff_toFun) p _ hcomp).1
  have h₂ := (MapClasses.smooth_tangent_invariants A B f hf p L hL).1
  rw [h₁, h₂]
  exact (MapClasses.linear_invariants
    (V := TangentSpace A p) (V' := TangentSpace A p)
    (W := TangentSpace B (f p)) (W' := TangentSpace C (h.toEquiv (f p)))
    (LinearEquiv.refl ℝ (TangentSpace A p)) E L
    (E.toLinearMap.comp L) (fun _ => rfl)).1.symm

/-- Equivariance makes the rank of an orbit map constant on the whole group.
Neither properness nor freeness is needed for this step. -/
theorem orbit_rank_constant {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (p : M) (g : G) :
    rankAt A B (fun k : G => k • p) g = rankAt A B (fun k : G => k • p) 1 := by
  let f : G → M := fun k => k • p
  have hf := smooth_orbit_map H p
  have hpre := rankAt_precomp_diffeomorph A A B (mulLeft_diffeomorph H g) f hf 1
  have hpost := rankAt_postcomp_diffeomorph A B B f hf (smul_diffeomorph H g) 1
  have heq : f ∘ (mulLeft_diffeomorph H g).toEquiv =
      (smul_diffeomorph H g).toEquiv ∘ f := by
    funext k
    exact mul_smul g k p
  rw [heq] at hpre
  simpa [mulLeft_diffeomorph] using hpre.symm.trans hpost

/-- An injective map cannot have a constant-rank normal form with an unused
source coordinate: a short coordinate line would map to a single point. -/
theorem normalForm_rank_eq_dimension {m n : ℕ} {a b : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : SmoothManifold m a X) (B : SmoothManifold n b Y) (f : X → Y)
    (p : X) (k : ℕ) (hkm : k ≤ m) (hinj : Function.Injective f)
    (hn : NormalForm (⊤ : ℕ∞) A B f p k) : k = m := by
  classical
  obtain ⟨c, d, _, _, hp, hcp, _, _, hmaps, hform⟩ := hn
  by_contra hne
  have hlt : k < m := lt_of_le_of_ne hkm hne
  let i : Fin m := ⟨k, hlt⟩
  let v : E m := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  have h0 : (0 : E m) ∈ c.target := hcp ▸ c.map_source hp
  have hnh : {t : ℝ | t • v ∈ c.target} ∈ 𝓝 (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    exact hc.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds (show (0 : ℝ) • v ∈ c.target by simpa using h0))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnh
  have ht : (ε / 2) • v ∈ c.target := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  have hproj : normalProjection m n k ((ε / 2) • v) = normalProjection m n k 0 := by
    ext j
    simp only [normalProjection, PiLp.toLp_apply]
    split_ifs with hj
    · have hi : (⟨j.val, hj.2⟩ : Fin m) ≠ i := by
        intro he
        have hh := congrArg Fin.val he
        dsimp [i] at hh
        omega
      simp [v, hi, PiLp.smul_apply]
    · rfl
  have hxy : c.symm ((ε / 2) • v) = c.symm 0 :=
    hinj (d.injOn (hmaps (c.map_target ht)) (hmaps (c.map_target h0))
      ((hform _ ht).trans (hproj.trans (hform _ h0).symm)))
  have hv0 : (ε / 2) • v = 0 :=
    (c.right_inv ht).symm.trans ((congrArg c hxy).trans (c.right_inv h0))
  have hval := congrArg (fun z : E m => z i) hv0
  have hzero : ε / 2 = 0 := by simpa [v] using hval
  linarith

/-- A full-rank linear map from a finite-dimensional space is injective. -/
theorem injective_of_finrank_range_eq {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [Module.Finite ℝ V] (L : V →ₗ[ℝ] W)
    (hL : Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ V) :
    Function.Injective L := by
  have h := L.finrank_range_add_finrank_ker
  rw [hL] at h
  have hz : Module.finrank ℝ (LinearMap.ker L) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

/-- A smooth injective map of locally constant rank is an immersion at each
interior point. This uses normal form rather than any false general claim
that smooth injective maps must be immersions. -/
theorem immersion_of_injective_constant_rank {m n : ℕ} {a b : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : SmoothManifold m a X) (B : SmoothManifold n b Y) (f : X → Y)
    (hf : IsSmoothMap A B f) (hinj : Function.Injective f)
    (p : X) (hp : p ∈ manifoldInterior A) (hfp : f p ∈ manifoldInterior B)
    (hk : ∃ W : Set X, IsOpen W ∧ p ∈ W ∧
      ∀ x ∈ W, rankAt A B f x = rankAt A B f p) :
    m ≤ n ∧ IsImmersionAt A B f p := by
  obtain ⟨_, hkmn, hn⟩ := InteriorConstantRank.interior_constant_rank
    (⊤ : ℕ∞) (by simp) A B f hf p hp hfp (rankAt A B f p) hk
  have hrank : rankAt A B f p = m :=
    normalForm_rank_eq_dimension A B f p _ (le_trans hkmn (min_le_left _ _)) hinj hn
  refine ⟨by omega, ?_⟩
  obtain ⟨e, he, hpe⟩ := A.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd⟩ := B.smoothStructure.property.1.1 (f p)
  have hf1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf
  have h := MapClasses.chart_invariants A B f hf1 p e d he hd hpe hpd
  apply h.2.1.mpr
  apply injective_of_finrank_range_eq (FiniteRegularityData.chartDerivative e d f p).toLinearMap
  simpa only [ModelData.Euclidean, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
    Nat.mul_one] using h.1.symm.trans hrank

/-- Freeness and equivariance imply that every orbit map is an immersion.
Properness is unnecessary for this infinitesimal conclusion. -/
theorem free_orbit_immersion {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (hfree : FreeAction G M) (p : M) (g : G) :
    d ≤ n ∧ IsImmersionAt A B (fun k : G => k • p) g := by
  apply immersion_of_injective_constant_rank A B _ (smooth_orbit_map H p)
    (orbit_map_injective hfree p) g
  · exact SliceStructures.interior_of_boundary_empty A H.group_boundary g
  · exact SliceStructures.interior_of_boundary_empty B H.space_boundary (g • p)
  · exact ⟨univ, isOpen_univ, mem_univ _, fun x _ =>
      (orbit_rank_constant H p x).trans (orbit_rank_constant H p g).symm⟩

/-- Existence, uniqueness and injectivity of the actual germ-derivation orbit
differential, together with the dimension bound in the original hypotheses. -/
theorem orbit_differential_injective :
    Specs.SmoothManifolds.Ch08.FreeProperSlices.orbit_differential_injectiveType.{u} := by
  intro d n a b G M _ _ _ _ hM A B H hfree
  constructor
  · intro p
    obtain ⟨L, hL, huniq⟩ := differential_exists A B (fun g : G => g • p)
      (smooth_orbit_map H p) 1
    exact ⟨L, hL,
      (MapClasses.smooth_tangent_invariants A B _ (smooth_orbit_map H p) 1 L hL).2.1.mp
        (free_orbit_immersion H hfree p 1).2, huniq⟩
  · exact (free_orbit_immersion H hfree (Classical.choice hM) 1).1

theorem action_coordinate_data {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (hfree : FreeAction G M) (p : M)
    (eG : ModelChart d .euclidean G) (heG : eG ∈ H.actionProduct.left.smoothStructure.val)
    (h1 : (1 : G) ∈ eG.source)
    (c : ModelChart n .euclidean M) (hc : c ∈ H.actionProduct.right.smoothStructure.val)
    (hp : p ∈ c.source) :
    let E := InteriorInverse.ambientChart eG
    let C := InteriorInverse.ambientChart c
    let f : Euclidean d × Euclidean n → Euclidean n :=
      fun z => C (E.symm z.1 • C.symm z.2)
    ∃ U : Set (Euclidean d × Euclidean n),
      IsOpen U ∧ (E 1,C p) ∈ U ∧ U ⊆ E.target ×ˢ C.target ∧
      MapsTo (fun z => E.symm z.1 • C.symm z.2) U C.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      (∀ᶠ x in 𝓝 (C p), f (E 1,x) = x) ∧
      Function.Injective ((fderiv ℝ f (E 1,C p)).comp (ContinuousLinearMap.inl ℝ _ _)) := by
  dsimp only
  let E := InteriorInverse.ambientChart eG
  let C := InteriorInverse.ambientChart c
  let f : Euclidean d × Euclidean n → Euclidean n :=
    fun z => C (E.symm z.1 • C.symm z.2)
  have h1E : (1 : G) ∈ E.source := ⟨h1,by change (eG 1).val ∈ interior (modelSet d .euclidean); simp only [ModelData.modelSet,interior_univ,mem_univ]⟩
  have hpC : p ∈ C.source := ⟨hp,by change (c p).val ∈ interior (modelSet n .euclidean); simp only [ModelData.modelSet,interior_univ,mem_univ]⟩
  let z₀ := (E 1,C p)
  let P : Euclidean d × Euclidean n → G × M := fun z => (E.symm z.1,C.symm z.2)
  have hP : ContinuousAt P z₀ :=
    (E.symm.continuousAt (E.map_source h1E)).comp_of_eq continuous_fst.continuousAt rfl |>.prodMk
      ((C.symm.continuousAt (C.map_source hpC)).comp_of_eq continuous_snd.continuousAt rfl)
  have hPz : P z₀ = (1,p) := by simp [P,z₀,E.left_inv h1E,C.left_inv hpC]
  have hact : IsSmoothMap H.actionProduct.manifold H.actionProduct.right
      (fun z : G × M => z.1 • z.2) :=
    smooth_comp H.smooth_action H.actionProduct.right_to
  let q := productChart H.actionProduct.coordinates eG c
  have hq : q ∈ H.actionProduct.manifold.smoothStructure.val := by
    rw [H.actionProduct.atlas_eq]
    exact subset_maximalExtension
      (productAtlas_isContDiffAtlas _ _ _ _ H.actionProduct.left.smoothStructure.property.1
        H.actionProduct.right.smoothStructure.property.1) ⟨eG,heG,c,hc,rfl⟩
  have hzq : (1,p) ∈ q.source := by rw [productChart_source]; exact ⟨h1,hp⟩
  obtain ⟨O,hO,hzO,g,hg,heq⟩ := (hact (1,p)).2 q hq c hc hzq (by simpa using hp)
  let T := H.actionProduct.coordinates.linearEquiv
  let O' := T ⁻¹' O
  have hO' : IsOpen O' := hO.preimage T.continuous
  have hzO' : z₀ ∈ O' := hzO
  let F : Euclidean d × Euclidean n → Euclidean n := fun z => g (T z)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F O' :=
    hg.comp T.contDiff.contDiffOn (fun _ hz => hz)
  have heqP : ∀ᶠ z in 𝓝 z₀, g ((q (P z)).val) = (c ((P z).1 • (P z).2)).val := by
    apply heq.comp_tendsto
    have hh : Tendsto P (𝓝 z₀) (𝓝 (P z₀)) := hP
    rwa [hPz] at hh
  have htar : ∀ᶠ z in 𝓝 z₀, z ∈ E.target ×ˢ C.target :=
    (E.open_target.prod C.open_target).mem_nhds ⟨E.map_source h1E,C.map_source hpC⟩
  have hac : ContinuousAt (fun z => E.symm z.1 • C.symm z.2) z₀ := by
    have hh := (hact (1,p)).1
    rw [← hPz] at hh
    exact hh.comp hP
  have hacz : E.symm z₀.1 • C.symm z₀.2 = p := by simp [z₀,E.left_inv h1E,C.left_inv hpC]
  have hactar : ∀ᶠ z in 𝓝 z₀, E.symm z.1 • C.symm z.2 ∈ C.source := by
    apply hac.preimage_mem_nhds
    rw [hacz]
    exact C.open_source.mem_nhds hpC
  have hev : ∀ᶠ z in 𝓝 z₀,
      z ∈ O' ∧ z ∈ E.target ×ˢ C.target ∧
      E.symm z.1 • C.symm z.2 ∈ C.source ∧ F z = f z := by
    filter_upwards [hO'.mem_nhds hzO',htar,hactar,heqP] with z hzO hzT hzA hzEq
    refine ⟨hzO,hzT,hzA,?_⟩
    have hqP : (q (P z)).val = T z := by
      change T (E (E.symm z.1),C (C.symm z.2)) = T z
      rw [E.right_inv hzT.1,C.right_inv hzT.2]
    rw [hqP] at hzEq
    exact hzEq
  obtain ⟨U,hUsub,hU,hzU⟩ := mem_nhds_iff.mp hev
  have hUf : ContDiffOn ℝ (⊤ : ℕ∞) f U :=
    (hF.mono (fun _ hz => (hUsub hz).1)).congr (fun z hz => (hUsub hz).2.2.2.symm)
  refine ⟨U,hU,hzU,fun _ hz => (hUsub hz).2.1,
    fun _ hz => (hUsub hz).2.2.1,hUf,?_,?_⟩
  · filter_upwards [C.open_target.mem_nhds (C.map_source hpC)] with x hx
    change C (E.symm (E 1) • C.symm x) = x
    rw [E.left_inv h1E,one_smul,C.right_inv hx]
  · have hdF := (hUf.contDiffAt (hU.mem_nhds hzU)).differentiableAt
      (by simp)
    change DifferentiableAt ℝ f (E 1,C p) at hdF
    have hpart := hdF.hasFDerivAt.comp (E 1) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (E 1) (C p))
    have heqOrbit : (fun g : G => f (E g,C p)) =ᶠ[𝓝 (1 : G)]
        (fun g => (c (g • p)).val) := by
      filter_upwards [E.open_source.mem_nhds h1E] with g hg
      change C (E.symm (E g) • C.symm (C p)) = _
      rw [E.left_inv hg,C.left_inv hpC]
      rfl
    have hder : FiniteRegularityData.chartDerivative eG c (fun g : G => g • p) 1 =
        (fderiv ℝ f z₀).comp (ContinuousLinearMap.inl ℝ _ _) :=
      FiniteRegularity.coordinateDerivative_eq eG _ 1 h1 _
        ⟨fun x => f (x,C p),hpart,heqOrbit⟩
    have horb := free_orbit_immersion (smoothLieAction_euclidean H) hfree p 1
    have hsm := manifoldContDiff_of_le ⊤ 1 _ _ _ le_top
      (smooth_orbit_map (smoothLieAction_euclidean H) p)
    rw [← hder]
    exact (MapClasses.chart_invariants H.actionProduct.left H.actionProduct.right _ hsm
      1 eG c heG hc h1 (by simpa using hp)).2.1.mp horb.2


/-- Proper, free orbits carry exactly the subspace topology of their images.
This complements the immersion theorem; injectivity alone would not suffice. -/
theorem orbit_map_isClosedEmbedding {G : Type u} {M : Type v}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [T2Space M] [LocallyCompactSpace M]
    (hcont : Continuous (fun z : G × M => z.1 • z.2))
    (hfree : FreeAction G M)
    (hproper : IsProper (actionTransport (G := G) (M := M))) (p : M) :
    Topology.IsClosedEmbedding (fun g : G => g • p) := by
  have hp := orbit_map_isProperMap hcont hproper p
  exact Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨hp.continuous, orbit_map_injective hfree p, hp.isClosedMap⟩

/-- Every orbit of a smooth free proper action is a smooth embedding of G.
The range topology in this assertion is the actual ambient subspace topology. -/
theorem orbit_map_smooth_embedding {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (H : SmoothLieAction A B) (hfree : FreeAction G M)
    (hproper : IsProper (actionTransport (G := G) (M := M))) (p : M) :
    IsSmoothEmbedding A B (fun g : G => g • p) := by
  let _ : T2Space M := B.topologicalManifold.hausdorff
  let _ : LocallyCompactSpace M :=
    _root_.SmoothManifolds.TopologicalManifold.locallyCompactSpace B.topologicalManifold
  have hc : Continuous (fun z : G × M => z.1 • z.2) :=
    continuous_iff_continuousAt.mpr (fun z => (H.smooth_action z).1)
  have he := orbit_map_isClosedEmbedding hc hfree hproper p
  exact ⟨smooth_orbit_map H p, orbit_map_injective hfree p,
    fun g => (free_orbit_immersion H hfree p g).2,
    ⟨he.isEmbedding.toHomeomorph, fun _ => rfl⟩⟩

/-- A compatible ambient coordinate plane carries the induced boundaryless
embedded manifold structure, with its actual subspace topology. -/
theorem coordinate_plane_manifold {k n : ℕ} {b : ModelKind}
    {M : Type u} [TopologicalSpace M] (B : SmoothManifold n b M)
    (c : ModelChart n .euclidean M) (hc : SliceData.CompatibleChart B c)
    (hkn : k ≤ n) :
    let s := c.source ∩ (fun x => (c x).val) ⁻¹' SliceData.coordinateSlice k n .euclidean
    ∃ S : SmoothManifold k .euclidean s,
      IsSmoothEmbedding S B Subtype.val ∧ intrinsicBoundary S = ∅ := by
  classical
  let s := c.source ∩ (fun x => (c x).val) ⁻¹' SliceData.coordinateSlice k n .euclidean
  have hslice : SliceData.IsSliceChart s k .euclidean c := by
    refine ⟨hkn, by simp, ?_⟩
    ext z
    constructor
    · rintro ⟨x, ⟨hx, _⟩, rfl⟩
      exact ⟨c.map_source hx.1, hx.2⟩
    · rintro ⟨hz, hzplane⟩
      refine ⟨c.symm z, ⟨⟨c.map_target hz, ?_⟩, c.map_target hz⟩, c.right_inv hz⟩
      change (c (c.symm z)).val ∈ SliceData.coordinateSlice k n .euclidean
      rwa [c.right_inv hz]
  have hcharts : SliceData.HasSliceCharts B s k .euclidean :=
    ⟨hkn, fun p hp => ⟨.euclidean, Or.inl rfl, c, hc, hp.1, hslice⟩⟩
  obtain ⟨S, hS, _⟩ := SliceStructures.exists_slice_manifold B s hcharts
  exact ⟨S, hS, intrinsicBoundary_euclidean S⟩

/-- A smooth Euclidean coordinate change preserves compatibility with the
original maximal atlas, including for mixed global model kinds. -/
theorem compatibleChart_after_change {n : ℕ} {b : ModelKind}
    {N : Type u} [TopologicalSpace N] (B : SmoothManifold n b N)
    (c : ModelChart n .euclidean N) (hc : SliceData.CompatibleChart B c)
    (d : ModelChart n .euclidean N)
    (h : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h h.source)
    (hhi : ContDiffOn ℝ (⊤ : ℕ∞) h.symm h.target)
    (hsub : d.source ⊆ c.source)
    (hform : ∀ y ∈ d.source, (c y).val ∈ h.source ∧ (d y).val = h (c y).val) :
    SliceData.CompatibleChart B d := by
  intro e he p hp hpe
  have hpc := hsub hp
  have hcd : ChartContDiffAt ⊤ c d id p := by
    refine ⟨h.source, h.open_source, (hform p hp).1, h, hh, ?_⟩
    filter_upwards [d.open_source.mem_nhds hp] with y hy
    exact (hform y hy).2.symm
  have hdc : ChartContDiffAt ⊤ d c id p := by
    have hdt : (d p).val ∈ h.target := by
      rw [(hform p hp).2]
      exact h.map_source (hform p hp).1
    refine ⟨h.target, h.open_target, hdt, h.symm, hhi, ?_⟩
    filter_upwards [d.open_source.mem_nhds hp] with y hy
    rw [(hform y hy).2, h.left_inv (hform y hy).1]
    rfl
  exact ⟨LocalCoordinateExtension.comp (hc e he p hpc hpe).1 hdc,
    LocalCoordinateExtension.comp hcd (hc e he p hpc hpe).2⟩

/-- Postcompose a Euclidean model chart by a homeomorphism of its ambient
Euclidean coordinates. -/
noncomputable def euclideanChart_postcomp {n : ℕ} {N : Type u} [TopologicalSpace N]
    (c : ModelChart n .euclidean N) (h : Euclidean n ≃ₜ Euclidean n) :
    ModelChart n .euclidean N :=
  c.transHomeomorph (((Homeomorph.Set.univ (Euclidean n)).trans h).trans
    (Homeomorph.Set.univ (Euclidean n)).symm)

@[simp] theorem euclideanChart_postcomp_source {n : ℕ} {N : Type u}
    [TopologicalSpace N] (c : ModelChart n .euclidean N)
    (h : Euclidean n ≃ₜ Euclidean n) :
    (euclideanChart_postcomp c h).source = c.source := rfl

@[simp] theorem euclideanChart_postcomp_val {n : ℕ} {N : Type u}
    [TopologicalSpace N] (c : ModelChart n .euclidean N)
    (h : Euclidean n ≃ₜ Euclidean n) (x : N) :
    (euclideanChart_postcomp c h x).val = h (c x).val := rfl

/-- A global smooth coordinate homeomorphism and its smooth inverse preserve
compatibility with the ambient smooth structure. -/
theorem compatibleChart_postcomp {n : ℕ} {b : ModelKind}
    {N : Type u} [TopologicalSpace N] (B : SmoothManifold n b N)
    (c : ModelChart n .euclidean N) (hc : SliceData.CompatibleChart B c)
    (h : Euclidean n ≃ₜ Euclidean n)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhi : ContDiff ℝ (⊤ : ℕ∞) h.symm) :
    SliceData.CompatibleChart B (euclideanChart_postcomp c h) := by
  exact compatibleChart_after_change B c hc _ h.toOpenPartialHomeomorph
    hh.contDiffOn hhi.contDiffOn (fun _ hx => hx)
    (fun _ _ => ⟨mem_univ _, rfl⟩)
/-- A complementary affine coordinate plane inherits an embedded boundaryless
manifold and a single compatible chart with the prescribed parametrization. -/
theorem complementary_affine_slice {d k : ℕ} {b : ModelKind}
    {M : Type u} [TopologicalSpace M] (B : SmoothManifold (k+d) b M)
    (c : ModelChart (k+d) .euclidean M) (hc : SliceData.CompatibleChart B c)
    (p : M) (hp : p ∈ c.source)
    (E : (Euclidean d × Euclidean k) ≃L[ℝ] Euclidean (k+d)) :
    ∃ (s : Set M) (hpS : p ∈ s) (S : SmoothManifold k .euclidean s),
      IsSmoothEmbedding S B Subtype.val ∧ intrinsicBoundary S = ∅ ∧
      ∃ e : ModelChart k .euclidean s,
        SliceData.CompatibleChart S e ∧ e.source = univ ∧
        (e ⟨p,hpS⟩).val = 0 ∧
        ∀ x : s, x.val ∈ c.source ∧
          (c x.val).val = (c p).val + E (0,(e x).val) := by
  classical
  let F : Euclidean (k+d) ≃L[ℝ] Euclidean (k+d) :=
    (E.symm.trans (ContinuousLinearEquiv.prodComm ℝ (Euclidean d) (Euclidean k))).trans
      (appendCoordinates k d)
  let H : Euclidean (k+d) ≃ₜ Euclidean (k+d) :=
    (Homeomorph.subRight (c p).val).trans F.toHomeomorph
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    F.contDiff.comp (contDiff_id.sub contDiff_const)
  have hHi : ContDiff ℝ (⊤ : ℕ∞) H.symm := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z => F.symm z + (c p).val)
    exact F.symm.contDiff.add contDiff_const
  let q := euclideanChart_postcomp c H
  have hq : SliceData.CompatibleChart B q := compatibleChart_postcomp B c hc H hH hHi
  have hpq : p ∈ q.source := hp
  have hqp : (q p).val = 0 := by
    change F ((c p).val - (c p).val) = 0
    simp
  let s := q.source ∩ (fun x => (q x).val) ⁻¹' SliceData.coordinateSlice k (k+d) .euclidean
  have hps : p ∈ s := by
    refine ⟨hpq, ?_⟩
    change (q p).val ∈ SliceData.coordinateSlice k (k+d) .euclidean
    rw [hqp]
    exact ⟨0, mem_univ _, by funext i; simp [SliceData.sliceEmbedding]⟩
  have hslice : SliceData.IsSliceChart s k .euclidean q := by
    refine ⟨Nat.le_add_right k d, by simp, ?_⟩
    ext z
    constructor
    · rintro ⟨x, ⟨hx, _⟩, rfl⟩
      exact ⟨q.map_source hx.1, hx.2⟩
    · rintro ⟨hz,hzplane⟩
      refine ⟨q.symm z, ⟨⟨q.map_target hz, ?_⟩, q.map_target hz⟩, q.right_inv hz⟩
      change (q (q.symm z)).val ∈ SliceData.coordinateSlice k (k+d) .euclidean
      rwa [q.right_inv hz]
  have hcharts : SliceData.HasSliceCharts B s k .euclidean :=
    ⟨Nat.le_add_right k d, fun x hx => ⟨.euclidean, Or.inl rfl, q, hq, hx.1, hslice⟩⟩
  obtain ⟨S,hSB,hS⟩ := SliceStructures.exists_slice_manifold B s hcharts
  let hne : Nonempty {x : s // x.val ∈ q.source} := ⟨⟨⟨p,hps⟩,hpq⟩⟩
  let e := SliceStructures.restrictedSliceChart q hslice hne
  have he : SliceData.CompatibleChart S e :=
    SliceStructures.sliceRestriction_compatible B s hcharts S hS q hq hslice hne
  have hrestr := SliceStructures.restrictedSliceChart_isSliceRestriction q hslice hne
  have heform (x : s) : (e x).val = SliceData.sliceProjection hslice.1 (q x.val).val :=
    hrestr.2.2 x x.property.1
  have hFinv (v : Euclidean k) : F.symm (appendCoordinates k d (v,0)) = E (0,v) := by
    change E ((ContinuousLinearEquiv.prodComm ℝ (Euclidean d) (Euclidean k)).symm
      ((appendCoordinates k d).symm (appendCoordinates k d (v,0)))) = E (0,v)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  refine ⟨s,hps,S,hSB,intrinsicBoundary_euclidean S,e,he,?_,?_,?_⟩
  · ext x
    exact iff_true_intro x.property.1
  · rw [heform, hqp]
    rfl
  · intro x
    refine ⟨x.property.1, ?_⟩
    have hplane := (SliceStructures.slice_coordinates q hslice x x.property.1).2
    rw [← heform] at hplane
    have hparam : F ((c x.val).val - (c p).val) =
        appendCoordinates k d ((e x).val,0) := by
      change (q x.val).val = _
      rw [SliceStructures.appendCoordinates_zero]
      exact hplane.symm
    have hdiff : (c x.val).val - (c p).val = E (0,(e x).val) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply,hFinv] using congrArg F.symm hparam
    exact (sub_eq_iff_eq_add.mp hdiff).trans (add_comm _ _)
/-- Dimension-reindexed form of the complementary affine-plane construction. -/
theorem complementary_affine_slice_of_dimension {d k n : ℕ} {b : ModelKind}
    {M : Type u} [TopologicalSpace M] (hdim : k+d = n)
    (B : SmoothManifold n b M)
    (c : ModelChart n .euclidean M) (hc : SliceData.CompatibleChart B c)
    (p : M) (hp : p ∈ c.source)
    (E : (Euclidean d × Euclidean k) ≃L[ℝ] Euclidean n) :
    ∃ (s : Set M) (hpS : p ∈ s) (S : SmoothManifold k .euclidean s),
      IsSmoothEmbedding S B Subtype.val ∧ intrinsicBoundary S = ∅ ∧
      ∃ e : ModelChart k .euclidean s,
        SliceData.CompatibleChart S e ∧ e.source = univ ∧
        (e ⟨p,hpS⟩).val = 0 ∧
        ∀ x : s, x.val ∈ c.source ∧
          (c x.val).val = (c p).val + E (0,(e x).val) := by
  subst n
  exact complementary_affine_slice B c hc p hp E

/-- Transport a transverse Euclidean inverse chart to an actual embedded
slice in the ambient manifold, retaining exact inverse coordinate data. -/
theorem local_affine_product_chart {d n : ℕ} {b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (B : SmoothManifold n b M) (hdn : d ≤ n)
    (cg : ModelChart d .euclidean G) (hpG : (1 : G) ∈ cg.source)
    (c : ModelChart n .euclidean M) (hc : SliceData.CompatibleChart B c)
    (p : M) (hp : p ∈ c.source)
    (U : Set (Euclidean d × Euclidean n))
    (hUaction : MapsTo (fun z => (InteriorInverse.ambientChart cg).symm z.1 •
      (InteriorInverse.ambientChart c).symm z.2) U (InteriorInverse.ambientChart c).source)
    (E : (Euclidean d × Euclidean (n-d)) ≃L[ℝ] Euclidean n)
    (W : Set (Euclidean d)) (V : Set (Euclidean (n-d)))
    (hW : IsOpen W) (h1W : (cg 1).val ∈ W) (hV : IsOpen V) (h0V : (0 : Euclidean (n-d)) ∈ V)
    (j : OpenPartialHomeomorph (Euclidean d × Euclidean (n-d)) (Euclidean n))
    (hjsource : j.source = W ×ˢ V)
    (hparam : MapsTo (fun z => (z.1,(c p).val + E (0,z.2))) j.source U)
    (hjeq : EqOn j (fun z => (InteriorInverse.ambientChart c)
      ((InteriorInverse.ambientChart cg).symm z.1 •
        (InteriorInverse.ambientChart c).symm ((c p).val + E (0,z.2)))) j.source) :
    ∃ (s : Set M) (hpS : p ∈ s) (S : SmoothManifold (n-d) .euclidean s),
      IsSmoothEmbedding S B Subtype.val ∧
      ∃ (e : ModelChart (n-d) .euclidean s) (Wg : Set G),
        SliceData.CompatibleChart S e ∧ e.source = univ ∧
        IsOpen Wg ∧ (1 : G) ∈ Wg ∧
        ∃ h : OpenPartialHomeomorph (G × s) M,
          h.source = Wg ×ˢ univ ∧
          EqOn h (fun z => z.1 • z.2.val) h.source ∧
          ∀ y ∈ h.target,
            y ∈ c.source ∧ (h.symm y).1 ∈ cg.source ∧ (h.symm y).2 ∈ e.source ∧
            (c y).val ∈ j.target ∧
            ((cg (h.symm y).1).val,(e (h.symm y).2).val) = j.symm (c y).val := by
  classical
  let C := InteriorInverse.ambientChart c
  let Gc := InteriorInverse.ambientChart cg
  have hCsource : C.source = c.source := by
    simp [C, InteriorInverse.ambientChart_source, ModelData.modelSet]
  have hGsource : Gc.source = cg.source := by
    simp [Gc, InteriorInverse.ambientChart_source, ModelData.modelSet]
  let r : M → Euclidean (n-d) := fun x => (E.symm (C x - C p)).2
  have hr : ContinuousOn r C.source :=
    continuous_snd.comp_continuousOn
      (E.symm.continuous.comp_continuousOn (C.continuousOn.sub continuousOn_const))
  let Uv := C.source ∩ r ⁻¹' V
  have hUv : IsOpen Uv := hr.isOpen_inter_preimage C.open_source hV
  have hpUv : p ∈ Uv := ⟨hCsource.symm ▸ hp, by simpa [r] using h0V⟩
  let c' := c.restrOpen Uv hUv
  have hc' : SliceData.CompatibleChart B c' :=
    SliceStructures.compatibleChart_restrOpen B c hc Uv hUv
  obtain ⟨s,hps,S,hSB,_,e,he,hesource,hep,hcoords⟩ :=
    complementary_affine_slice_of_dimension (Nat.sub_add_cancel hdn) B c' hc' p
      ⟨hp,hpUv⟩ E
  have hxC (x : s) : x.val ∈ C.source := (hcoords x).1.2.1
  have hxparam (x : s) : C x.val = C p + E (0,(e x).val) := (hcoords x).2
  have hxV (x : s) : (e x).val ∈ V := by
    have hx : r x.val ∈ V := (hcoords x).1.2.2
    simpa [r,hxparam] using hx
  let Ec := InteriorInverse.ambientChart e
  have hEsource : Ec.source = univ := by
    simp [Ec, InteriorInverse.ambientChart_source, ModelData.modelSet, hesource]
  let P := Gc.prod Ec
  let h := (P.trans j).trans C.symm
  let Wg := Gc.source ∩ Gc ⁻¹' W
  have hWg : IsOpen Wg := Gc.isOpen_inter_preimage hW
  have h1Wg : (1 : G) ∈ Wg := ⟨hGsource.symm ▸ hpG,h1W⟩
  have hdata (z : G × s) (hg : z.1 ∈ Gc.source) (hw : Gc z.1 ∈ W) :
      z ∈ P.source ∧ P z ∈ j.source ∧ z.1 • z.2.val ∈ C.source ∧
        j (P z) = C (z.1 • z.2.val) := by
    have hez : z.2 ∈ Ec.source := hEsource.symm ▸ mem_univ _
    have hzP : z ∈ P.source := ⟨hg,hez⟩
    have hzj : P z ∈ j.source := by
      rw [hjsource]
      exact ⟨hw,hxV z.2⟩
    have hu := hparam hzj
    have hspace : C.symm (C p + E (0,(e z.2).val)) = z.2.val := by
      rw [← hxparam]
      exact C.left_inv (hxC z.2)
    have hact : z.1 • z.2.val ∈ C.source := by
      have hh := hUaction hu
      change Gc.symm (Gc z.1) • C.symm (C p + E (0,(e z.2).val)) ∈ C.source at hh
      rwa [Gc.left_inv hg,hspace] at hh
    refine ⟨hzP,hzj,hact,?_⟩
    have hh := hjeq hzj
    change j (P z) = C (Gc.symm (Gc z.1) • C.symm (C p + E (0,(e z.2).val))) at hh
    rwa [Gc.left_inv hg,hspace] at hh
  have hsource : h.source = Wg ×ˢ univ := by
    ext z
    constructor
    · intro hz
      change (z ∈ P.source ∧ P z ∈ j.source) ∧ j (P z) ∈ C.target at hz
      have hzj : P z ∈ W ×ˢ V := hjsource ▸ hz.1.2
      exact ⟨⟨hz.1.1.1,hzj.1⟩,mem_univ _⟩
    · rintro ⟨⟨hg,hw⟩,_⟩
      obtain ⟨hzP,hzj,hact,heq⟩ := hdata z hg hw
      change (z ∈ P.source ∧ P z ∈ j.source) ∧ j (P z) ∈ C.target
      exact ⟨⟨hzP,hzj⟩,heq.symm ▸ C.map_source hact⟩
  have haction : EqOn h (fun z : G × s => z.1 • z.2.val) h.source := by
    intro z hz
    have hzw : z ∈ Wg ×ˢ univ := hsource ▸ hz
    have hd := hdata z hzw.1.1 hzw.1.2
    change C.symm (j (P z)) = _
    rw [hd.2.2.2,C.left_inv hd.2.2.1]
  refine ⟨s,hps,S,hSB,e,Wg,he,hesource,hWg,h1Wg,h,hsource,haction,?_⟩
  intro y hy
  have hymap : h.symm y ∈ Wg ×ˢ univ := hsource ▸ h.map_target hy
  have hyC : y ∈ C.source := hy.1
  have hyj : C y ∈ j.target := hy.2.1
  have hyP : j.symm (C y) ∈ P.target := hy.2.2
  refine ⟨hCsource ▸ hyC,hGsource ▸ hymap.1.1,hesource.symm ▸ mem_univ _,hyj,?_⟩
  exact P.right_inv hyP
/-- Smoothness into a canonically restricted open target is tested after
its inclusion in the ambient manifold. -/
theorem smooth_to_open_subset {m n : ℕ} {a b : ModelKind} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : SmoothManifold m a X) (B : SmoothManifold n b Y)
    (s : Set Y) (hs : IsOpen s) (R : SmoothManifold n b s)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas B.smoothStructure.val s hs))
    (f : X → s) (hf : IsSmoothMap A B (fun x => (f x).val)) :
    IsSmoothMap A R f := by
  intro p
  obtain ⟨e, he, hp⟩ := A.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := B.smoothStructure.property.1.1 (f p).val
  let c := d.subtypeRestr (s := ⟨s, hs⟩) ⟨f p⟩
  have hc : c ∈ R.smoothStructure.val := by
    rw [hR]
    apply subset_maximalExtension
      (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ B.smoothStructure.property.1 s hs)
    exact ⟨⟨f p⟩, d, hd, rfl⟩
  apply (manifoldContDiffAt_iff_oneChart _ _ _ A.smoothStructure.property.1
    R.smoothStructure.property.1 f p).mpr
  refine ⟨tendsto_subtype_rng.mpr (hf p).1, e, he, c, hc, hp, ?_, ?_⟩
  · simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hfp
  · exact (hf p).2 e he d hd hp hfp

/-- Smooth local inverses globalize to the actual action-independent
smooth bijection onto the open range. The range has its subspace topology
and its canonical restricted atlas. -/
theorem diffeomorph_onto_open_range {m n : ℕ} {a b : ModelKind} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : SmoothManifold m a X) (B : SmoothManifold n b Y) (f : X → Y)
    (hf : IsSmoothMap A B f) (hinj : Function.Injective f)
    (hloc : ∀ x : X, ∃ h : OpenPartialHomeomorph X Y,
      x ∈ h.source ∧ EqOn h f h.source ∧
      ManifoldContDiffOn (⊤ : ℕ∞) B.smoothStructure.val A.smoothStructure.val
        h.symm h.target) :
    ∃ (ho : IsOpen (range f)) (R : SmoothManifold n b (range f)),
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas B.smoothStructure.val (range f) ho) ∧
      ∃ D : Diffeomorph A.smoothStructure.val R.smoothStructure.val,
        ∀ x, (D.toEquiv x).val = f x := by
  have hlocal : IsLocalHomeomorph f := by
    apply IsLocalHomeomorph.mk
    intro x
    obtain ⟨h, hx, heq, _⟩ := hloc x
    exact ⟨h, hx, heq.symm⟩
  have ho : IsOpen (range f) := by
    simpa only [image_univ] using hlocal.isOpenMap univ isOpen_univ
  obtain ⟨R, _, hR, hinc⟩ := exists_openSubset_smoothManifold B (range f) ho
  let f' : X → range f := fun x => ⟨f x, ⟨x, rfl⟩⟩
  have hf' : IsSmoothMap A R f' := smooth_to_open_subset A B _ ho R hR f' hf
  have hbij : Function.Bijective f' := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  let e : X ≃ range f := Equiv.ofBijective f' hbij
  have he : ∀ x, (e x).val = f x := fun _ => rfl
  have hinv : IsSmoothMap R A e.symm := by
    intro y
    let x := e.symm y
    have hxy : f x = y.val := by
      change f (e.symm y) = y.val
      rw [← he, e.apply_symm_apply]
    obtain ⟨h, hx, heq, hsm⟩ := hloc x
    have hy : y.val ∈ h.target := by
      rw [← hxy, ← heq hx]
      exact h.map_source hx
    have hi := manifoldContDiffAt_comp B.smoothStructure.property.1.1
      (hinc y) (hsm y.val hy)
    apply manifoldContDiffAt_congr hi
    filter_upwards [(hinc y).1.preimage_mem_nhds (h.open_target.mem_nhds hy)] with z hz
    apply hinj
    have hfi : f (h.symm z.val) = z.val :=
      (heq (h.map_target hz)).symm.trans (h.right_inv hz)
    exact hfi.trans (by rw [← he, e.apply_symm_apply])
  exact ⟨ho, R, hR, ⟨⟨e, hf', hinv⟩, he⟩⟩

/-- Smooth maps on factors induce a smooth map on any of the chosen compatible
boundaryless products. -/
theorem smooth_product_map {d n l k : ℕ} {a b c e : ModelKind}
    {X Y Z T : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace T]
    {A : SmoothManifold d a X} {B : SmoothManifold n b Y}
    {C : SmoothManifold l c Z} {D : SmoothManifold k e T}
    (P : BoundarylessProduct A B) (Q : BoundarylessProduct C D)
    (f : X → Z) (g : Y → T) (hf : IsSmoothMap A C f) (hg : IsSmoothMap B D g) :
    IsSmoothMap P.manifold Q.manifold (fun z => (f z.1, g z.2)) := by
  have hproj := differential_product P.left P.right P.coordinates P.manifold P.atlas_eq
  have hfst : IsSmoothMap P.manifold A Prod.fst :=
    smooth_comp (f := Prod.fst) (g := id) hproj.1 P.left_from
  have hsnd : IsSmoothMap P.manifold B Prod.snd :=
    smooth_comp (f := Prod.snd) (g := id) hproj.2.1 P.right_from
  exact smooth_pair Q (smooth_comp hfst hf) (smooth_comp hsnd hg)

/-- An adapted ambient chart straightens the entire orbit near p. This is
obtained from the established embedding, rather than assumed as input. -/
theorem orbit_adapted_chart {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (H : SmoothLieAction A B) (hfree : FreeAction G M)
    (hproper : IsProper (actionTransport (G := G) (M := M))) (p : M) :
    ∃ c : ModelChart n .euclidean M, SliceData.CompatibleChart B c ∧ p ∈ c.source ∧
      SliceData.IsSliceChart (range (fun g : G => g • p)) d .euclidean c := by
  simpa only [one_smul] using
    SliceStructures.interior_slice A B (fun g : G => g • p) H.space_boundary
      (orbit_map_smooth_embedding A B H hfree hproper p) 1
      (SliceStructures.interior_of_boundary_empty A H.group_boundary 1)

/-- Smoothness of the action restricted to a smooth embedded slice, with the
original selected product smooth structures. -/
theorem smooth_restricted_action {d n k : ℕ} {a b c : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (s : Set M) (S : SmoothManifold k c s)
    (Q : BoundarylessProduct A S) (hi : IsSmoothMap S B Subtype.val) :
    IsSmoothMap Q.manifold B (fun z : G × s => z.1 • z.2.val) :=
  smooth_comp (g := fun z : G × M => z.1 • z.2)
    (smooth_product_map Q H.actionProduct id Subtype.val
      (manifoldContDiff_id _ _ A.smoothStructure.property.1) hi) H.smooth_action

/-- The smooth local inverse at the identity translates to every point of the
product. All smoothness assertions use the actual product and slice atlases. -/
theorem smooth_local_inverses_of_product_chart {d n k : ℕ} {a b c : ModelKind}
    {G M : Type u} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (s : Set M) (S : SmoothManifold k c s)
    (Q : BoundarylessProduct A S) (W : Set G) (h1 : (1 : G) ∈ W)
    (h : OpenPartialHomeomorph (G × s) M) (hsource : h.source = W ×ˢ univ)
    (heq : EqOn h (fun z : G × s => z.1 • z.2.val) h.source)
    (hsm : ManifoldContDiffOn (⊤ : ℕ∞) B.smoothStructure.val
      Q.manifold.smoothStructure.val h.symm h.target) :
    ∀ z : G × s, ∃ e : OpenPartialHomeomorph (G × s) M,
      z ∈ e.source ∧ EqOn e (fun z : G × s => z.1 • z.2.val) e.source ∧
      ManifoldContDiffOn (⊤ : ℕ∞) B.smoothStructure.val
        Q.manifold.smoothStructure.val e.symm e.target := by
  obtain ⟨hG, hM⟩ := smoothLieAction_topological H
  letI := hG
  letI := hM
  rintro ⟨g, x⟩
  let L : (G × s) ≃ₜ (G × s) :=
    (Homeomorph.mulLeft g⁻¹).prodCongr (Homeomorph.refl s)
  let e := (L.transOpenPartialHomeomorph h).transHomeomorph (Homeomorph.smul g)
  have hx : (g, x) ∈ e.source := by
    change (g⁻¹ * g, x) ∈ h.source
    rw [hsource]
    exact ⟨by simpa using h1, mem_univ x⟩
  refine ⟨e, hx, ?_, ?_⟩
  · intro z hz
    change g • h (g⁻¹ * z.1, z.2) = z.1 • z.2.val
    have hz' : (g⁻¹ * z.1, z.2) ∈ h.source := hz
    rw [heq hz']
    simp [mul_smul]
  · intro y hy
    have hyh : g⁻¹ • y ∈ h.target := hy
    have hL : IsSmoothMap Q.manifold Q.manifold
        (fun z : G × s => ((g⁻¹)⁻¹ * z.1, z.2)) :=
      smooth_product_map Q Q (fun k : G => (g⁻¹)⁻¹ * k) id
        (smooth_mulLeft H (g⁻¹)⁻¹) (manifoldContDiff_id _ _ S.smoothStructure.property.1)
    exact manifoldContDiffAt_comp Q.manifold.smoothStructure.property.1.1
      (manifoldContDiffAt_comp B.smoothStructure.property.1.1
        ((smooth_smul H g⁻¹) y) (hsm (g⁻¹ • y) hyh))
      (hL (h.symm (g⁻¹ • y)))

/-- A separated slice with a smooth local product chart has the full smooth
trivialization onto its open saturation, with the actual action as forward map.
This lemma proves the globalization; it does not assume the parent slice exists. -/
theorem smooth_trivialization_of_separated_product_chart
    {d n k : ℕ} {a b c : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (s : Set M) (S : SmoothManifold k c s)
    (Q : BoundarylessProduct A S) (hi : IsSmoothMap S B Subtype.val)
    (hsep : ∀ (g : G) (x y : M), x ∈ s → y ∈ s → g • x = y → g = 1 ∧ x = y)
    (W : Set G) (h1 : (1 : G) ∈ W)
    (h : OpenPartialHomeomorph (G × s) M) (hsource : h.source = W ×ˢ univ)
    (heq : EqOn h (fun z : G × s => z.1 • z.2.val) h.source)
    (hsm : ManifoldContDiffOn (⊤ : ℕ∞) B.smoothStructure.val
      Q.manifold.smoothStructure.val h.symm h.target) :
    ∃ (ho : IsOpen (saturation (G := G) s))
      (R : SmoothManifold n b (saturation (G := G) s)),
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas B.smoothStructure.val (saturation (G := G) s) ho) ∧
      ∃ D : Diffeomorph Q.manifold.smoothStructure.val R.smoothStructure.val,
        ∀ z : G × s, (D.toEquiv z).val = z.1 • z.2.val := by
  have hinj : Function.Injective (fun z : G × s => z.1 • z.2.val) := by
    intro x y hxy
    exact (action_product_bijective s hsep).1 (Subtype.ext hxy)
  have hr : range (fun z : G × s => z.1 • z.2.val) = saturation (G := G) s := by
    ext y
    constructor
    · rintro ⟨⟨g, x⟩, rfl⟩
      exact ⟨g, x.val, x.property, rfl⟩
    · rintro ⟨g, x, hx, rfl⟩
      exact ⟨(g, ⟨x, hx⟩), rfl⟩
  have hglobal := diffeomorph_onto_open_range Q.manifold B _
    (smooth_restricted_action H s S Q hi) hinj
    (smooth_local_inverses_of_product_chart H s S Q W h1 h hsource heq hsm)
  rwa [hr] at hglobal

-- The differential of a map on a product is determined by its two restrictions.
theorem product_derivative_eq {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : E × F → H) (a : E) (b : F) (D : E × F →L[ℝ] H)
    (hd : HasFDerivAt f D (a,b)) (A : E →L[ℝ] H) (B : F →L[ℝ] H)
    (ha : HasFDerivAt (fun x => f (x,b)) A a)
    (hb : HasFDerivAt (fun y => f (a,y)) B b) :
    D = A.comp (ContinuousLinearMap.fst ℝ E F) +
      B.comp (ContinuousLinearMap.snd ℝ E F) := by
  have hA := (hd.comp a (hasFDerivAt_prodMk_left a b)).unique ha
  have hB := (hd.comp b (hasFDerivAt_prodMk_right a b)).unique hb
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = (z.1,0) + (0,z.2) := by simp
  conv_lhs => rw [hz]
  rw [map_add]
  change D (z.1, 0) + D (0,z.2) = A z.1 + B z.2
  exact congrArg₂ (· + ·) (congrArg (fun L : E →L[ℝ] H => L z.1) hA)
    (congrArg (fun L : F →L[ℝ] H => L z.2) hB)

-- This is the Euclidean core of constructing a transverse local action slice.
theorem transverse_derivative {m n : ℕ}
    (f : Euclidean m × Euclidean n → Euclidean n)
    (a : Euclidean m) (p : Euclidean n)
    (D : Euclidean m × Euclidean n →L[ℝ] Euclidean n)
    (hd : HasFDerivAt f D (a,p))
    (hid : HasFDerivAt (fun x => f (a,x)) (ContinuousLinearMap.id ℝ _) p)
    (hinj : Function.Injective (D.comp (ContinuousLinearMap.inl ℝ _ _))) :
    m ≤ n ∧ ∃ E : (Euclidean m × Euclidean (n-m)) ≃L[ℝ] Euclidean n,
      (∀ x, E (x,0) = (D.comp (ContinuousLinearMap.inl ℝ _ _)) x) ∧
      let C := E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)
      HasFDerivAt (fun z : Euclidean m × Euclidean (n-m) => f (z.1, p + C z.2))
        E.toContinuousLinearMap (a,0) := by
  let L := D.comp (ContinuousLinearMap.inl ℝ _ _)
  obtain ⟨hmn,E,hE⟩ := BoundaryImmersion.complementary_coordinates L hinj
  refine ⟨hmn,E,hE,?_⟩
  dsimp only
  let C := E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)
  have hright : D.comp (ContinuousLinearMap.inr ℝ _ _) = ContinuousLinearMap.id ℝ _ :=
    (hd.comp p (hasFDerivAt_prodMk_right a p)).unique hid
  have hlin : D.comp ((ContinuousLinearMap.fst ℝ _ _).prod
      (C.comp (ContinuousLinearMap.snd ℝ _ _))) = E.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    change D (z.1,C z.2) = E z
    have hz : (z.1,C z.2) = (z.1,0) + (0,C z.2) := by simp
    rw [hz,map_add]
    change L z.1 + (D.comp (ContinuousLinearMap.inr ℝ _ _)) (C z.2) = E z
    rw [hright,ContinuousLinearMap.id_apply,← hE]
    change E (z.1,0) + E (0,z.2) = E z
    rw [← map_add]
    simp
  have hparam : HasFDerivAt (fun z : Euclidean m × Euclidean (n-m) => (z.1,p+C z.2))
      ((ContinuousLinearMap.fst ℝ _ _).prod (C.comp (ContinuousLinearMap.snd ℝ _ _)))
      (a,0) :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (a,0))).prodMk
      ((C.hasFDerivAt.comp (a,0) (hasFDerivAt_snd (𝕜 := ℝ) (p := (a,0)))).const_add p)
  have hbase : (fun z : Euclidean m × Euclidean (n-m) => (z.1,p+C z.2)) (a,0) = (a,p) := by simp
  have hh := (hbase.symm ▸ hd).comp (a,0) hparam
  rw [hlin] at hh
  exact hh

/-- An inverse-function theorem with a rectangular source in a product domain. -/
theorem product_inverse {m l n : ℕ}
    (F : Euclidean m × Euclidean l → Euclidean n)
    (U : Set (Euclidean m × Euclidean l)) (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) (a : Euclidean m) (b : Euclidean l)
    (hab : (a,b) ∈ U)
    (E : (Euclidean m × Euclidean l) ≃L[ℝ] Euclidean n)
    (hd : HasFDerivAt F E.toContinuousLinearMap (a,b)) :
    ∃ (W : Set (Euclidean m)) (V : Set (Euclidean l)),
      IsOpen W ∧ a ∈ W ∧ IsOpen V ∧ b ∈ V ∧
      ∃ h : OpenPartialHomeomorph (Euclidean m × Euclidean l) (Euclidean n),
        h.source = W ×ˢ V ∧ h.source ⊆ U ∧ EqOn h F h.source ∧
        ContDiffOn ℝ (⊤ : ℕ∞) h h.source ∧
        ContDiffOn ℝ (⊤ : ℕ∞) h.symm h.target := by
  let G : Euclidean n → Euclidean n := fun z => F (E.symm z)
  let O := E.symm ⁻¹' U
  have hO : IsOpen O := hU.preimage E.symm.continuous
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G O :=
    hF.comp E.symm.contDiff.contDiffOn (fun _ hz => hz)
  have hz : E (a,b) ∈ O := by simpa [O] using hab
  have hlin : E.toContinuousLinearMap.comp E.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
    apply ContinuousLinearMap.ext
    intro z
    exact E.apply_symm_apply z
  have hDG : HasFDerivAt G (ContinuousLinearMap.id ℝ _) (E (a,b)) := by
    have hh := (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hd :
      HasFDerivAt F E.toContinuousLinearMap (E.symm (E (a,b)))).comp
        (E (a,b)) E.symm.hasFDerivAt
    rwa [hlin] at hh
  obtain ⟨j,hzj,hj,hji⟩ := InteriorInverse.euclidean_inverse ⊤ le_top G O hO hG
    (E (a,b)) hz (ContinuousLinearMap.id ℝ _) hDG Function.bijective_id
  let j' := j.restrOpen O hO
  let h₀ := E.toHomeomorph.transOpenPartialHomeomorph j'
  have habh : (a,b) ∈ h₀.source := ⟨hzj,hz⟩
  obtain ⟨W,V,hW,ha,hV,hb,hWV⟩ := mem_nhds_prod_iff'.mp
    (h₀.open_source.mem_nhds habh)
  let h := h₀.restrOpen (W ×ˢ V) (hW.prod hV)
  have hsource : h.source = W ×ˢ V := inter_eq_right.mpr hWV
  have heq : EqOn h F h.source := by
    intro z hz
    change j (E z) = F z
    rw [hj]
    exact congrArg F (E.symm_apply_apply z)
  have hsub : h.source ⊆ U := by
    intro z hz
    have hh : E z ∈ O := hz.1.2
    simpa only [O,mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hh
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) h h.source :=
    (hF.mono hsub).congr heq
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) h.symm h.target := by
    intro y hy
    have hyj : y ∈ j.target := hy.1.1
    exact E.symm.contDiff.contDiffAt.comp_contDiffWithinAt y ((hji y hyj).mono
      (fun z hz => hz.1.1))
  exact ⟨W,V,hW,ha,hV,hb,h,hsource,hsub,heq,hf,hi⟩

/-- A smooth local action which is the identity in the space variable at the
base group parameter has a transverse affine-plane product chart. -/
theorem transverse_inverse {m n : ℕ}
    (f : Euclidean m × Euclidean n → Euclidean n)
    (U : Set (Euclidean m × Euclidean n)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (a : Euclidean m) (p : Euclidean n) (hap : (a,p) ∈ U)
    (D : Euclidean m × Euclidean n →L[ℝ] Euclidean n)
    (hd : HasFDerivAt f D (a,p))
    (hid : ∀ᶠ x in 𝓝 p, f (a,x) = x)
    (hinj : Function.Injective (D.comp (ContinuousLinearMap.inl ℝ _ _))) :
    m ≤ n ∧ ∃ E : (Euclidean m × Euclidean (n-m)) ≃L[ℝ] Euclidean n,
      (∀ x, E (x,0) = (D.comp (ContinuousLinearMap.inl ℝ _ _)) x) ∧
      let C := E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)
      ∃ (W : Set (Euclidean m)) (V : Set (Euclidean (n-m))),
        IsOpen W ∧ a ∈ W ∧ IsOpen V ∧ (0 : Euclidean (n-m)) ∈ V ∧
        ∃ h : OpenPartialHomeomorph (Euclidean m × Euclidean (n-m)) (Euclidean n),
          h.source = W ×ˢ V ∧
          MapsTo (fun z => (z.1,p+C z.2)) h.source U ∧
          EqOn h (fun z => f (z.1,p+C z.2)) h.source ∧
          h (a,0) = p ∧
          ContDiffOn ℝ (⊤ : ℕ∞) h h.source ∧
          ContDiffOn ℝ (⊤ : ℕ∞) h.symm h.target := by
  have hi : HasFDerivAt (fun x => f (a,x)) (ContinuousLinearMap.id ℝ _) p :=
    (hasFDerivAt_id p).congr_of_eventuallyEq hid
  obtain ⟨hmn,E,hE,hder⟩ := transverse_derivative f a p D hd hi hinj
  refine ⟨hmn,E,hE,?_⟩
  dsimp only
  let C := E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)
  let P : Euclidean m × Euclidean (n-m) → Euclidean m × Euclidean n :=
    fun z => (z.1,p+C z.2)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P :=
    contDiff_fst.prodMk (contDiff_const.add (C.contDiff.comp contDiff_snd))
  let O := P ⁻¹' U
  have hO : IsOpen O := hU.preimage hP.continuous
  have hbase : (a,(0 : Euclidean (n-m))) ∈ O := by
    change (a,p+C 0) ∈ U
    simpa using hap
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => f (z.1,p+C z.2)) O :=
    hf.comp hP.contDiffOn (fun _ hz => hz)
  obtain ⟨W,V,hW,ha,hV,h0,h,hsource,hsub,heq,hfor,hinv⟩ :=
    product_inverse _ O hO hF a 0 hbase E hder
  refine ⟨W,V,hW,ha,hV,h0,h,hsource,hsub,heq,?_,hfor,hinv⟩
  have hab : (a,(0 : Euclidean (n-m))) ∈ h.source := by
    rw [hsource]
    exact ⟨ha,h0⟩
  have hip : f (a,p) = p := Filter.EventuallyEq.eq_of_nhds hid
  exact (by simpa using heq hab : h (a,0) = f (a,p)).trans hip


/-- The local geometric data give the full requested slice as soon as its
points cannot be transported to one another. Properness is used separately
to arrange this condition by shrinking. -/
theorem globalSlice_of_separated_localProductSlice
    {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (p : M) (L : LocalProductSlice A B p)
    (hsep : ∀ (g : G) (x y : M), x ∈ L.carrier → y ∈ L.carrier →
      g • x = y → g = 1 ∧ x = y) : Nonempty (GlobalSlice A B p) := by
  obtain ⟨ho, R, hR, D, hD⟩ := smooth_trivialization_of_separated_product_chart
    H L.carrier L.slice L.product L.embedding.1 hsep
    L.identityNeighborhood L.one_mem L.chart L.chart_source L.chart_action L.smooth_inverse
  exact ⟨{
    carrier := L.carrier
    contains := L.contains
    slice := L.slice
    boundary_empty := intrinsicBoundary_euclidean L.slice
    embedding := L.embedding
    saturated_open := ho
    product := L.product
    neighborhood := R
    neighborhood_atlas := hR
    trivialization := D
    action_eq := hD
    orbit_unique := orbit_intersection_unique L.carrier hsep }⟩

open SliceData

/-- Smoothness into an immersed subspace can be tested in the ambient manifold. -/
theorem smooth_factor_through_immersion_at {l k n : ℕ} {a b c : ModelKind}
    {X N : Type u} [TopologicalSpace X] [TopologicalSpace N]
    (A : SmoothManifold l a X) (B : SmoothManifold n b N) (s : Set N)
    (S : SmoothManifold k c s) (hB : intrinsicBoundary B = ∅)
    (hi : IsSmoothMap S B Subtype.val) (himm : IsImmersion S B Subtype.val)
    (f : X → s) (p : X)
    (hf : ManifoldContDiffAt ⊤ A.smoothStructure.val B.smoothStructure.val
      (fun x => (f x).val) p) :
    ManifoldContDiffAt ⊤ A.smoothStructure.val S.smoothStructure.val f p := by
  have hcont : ContinuousAt f p := tendsto_subtype_rng.mpr hf.1
  obtain ⟨hkn, e, he, hp, d, hd, hpd, V, hV, hpV, hVe, hform⟩ :=
    SliceStructures.immersion_coordinates S B Subtype.val hi (f p) (himm (f p))
      (SliceStructures.interior_of_boundary_empty B hB (f p).val)
  obtain ⟨j, hj, hpj⟩ := A.smoothStructure.property.1.1 p
  obtain ⟨q, hq, hpq⟩ := B.smoothStructure.property.1.1 (f p).val
  have hqd : LocalCoordinateExtension ⊤ (fun x => (q (f x).val).val)
      (fun x => (d (f x).val).val) p :=
    LocalCoordinateExtension.precomp (hd q hq (f p).val hpd hpq).2 hf.1 rfl
  have hjd : ChartContDiffAt ⊤ j d (fun x => (f x).val) p :=
    hqd.comp (hf.2 j hj q hq hpj hpq)
  have hde : LocalCoordinateExtension ⊤ (fun x => (d (f x).val).val)
      (fun x => (e (f x)).val) p := by
    refine ⟨univ, isOpen_univ, mem_univ _, sliceProjection hkn,
      (SliceStructures.contDiff_sliceProjection hkn).contDiffOn, ?_⟩
    filter_upwards [hcont.preimage_mem_nhds (hV.mem_nhds hpV)] with x hx
    rw [(hform (f x) hx).2, SliceStructures.sliceProjection_embedding]
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ A.smoothStructure.property.1
    S.smoothStructure.property.1 f p).mpr
  exact ⟨hcont, j, hj, e, he, hpj, hp, hde.comp hjd⟩

/-- The selected product atlas has the expected pointwise pairing property. -/
theorem smooth_pair_at {l m n : ℕ} {a b c : ModelKind}
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold l a X) {B : SmoothManifold m b Y} {C : SmoothManifold n c Z}
    (P : BoundarylessProduct B C) {f : X → Y} {g : X → Z} (p : X)
    (hf : ManifoldContDiffAt ⊤ A.smoothStructure.val B.smoothStructure.val f p)
    (hg : ManifoldContDiffAt ⊤ A.smoothStructure.val C.smoothStructure.val g p) :
    ManifoldContDiffAt ⊤ A.smoothStructure.val P.manifold.smoothStructure.val
      (fun x => (f x, g x)) p := by
  have hf' := manifoldContDiffAt_comp B.smoothStructure.property.1.1 hf (P.left_to (f p))
  have hg' := manifoldContDiffAt_comp C.smoothStructure.property.1.1 hg (P.right_to (g p))
  obtain ⟨e, he, hep⟩ := A.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hdp⟩ := P.left.smoothStructure.property.1.1 (f p)
  obtain ⟨j, hj, hjp⟩ := P.right.smoothStructure.property.1.1 (g p)
  apply (manifoldContDiffAt_iff_oneChart _ _ _ A.smoothStructure.property.1
    P.manifold.smoothStructure.property.1 _ p).mpr
  have hprod : productChart P.coordinates d j ∈ P.manifold.smoothStructure.val := by
    rw [P.atlas_eq]
    exact subset_maximalExtension
      (productAtlas_isContDiffAtlas P.coordinates ⊤ _ _ P.left.smoothStructure.property.1
        P.right.smoothStructure.property.1) ⟨d, hd, j, hj, rfl⟩
  refine ⟨hf.1.prodMk hg.1, e, he, productChart P.coordinates d j, hprod,
    hep, ?_, ?_⟩
  · simpa only [productChart_source, Set.mem_prod] using And.intro hdp hjp
  obtain ⟨V, hV, hpV, F, hF, heF⟩ := hf'.2 e he d hd hep hdp
  obtain ⟨W, hW, hpW, G, hG, heG⟩ := hg'.2 e he j hj hep hjp
  refine ⟨V ∩ W, hV.inter hW, ⟨hpV, hpW⟩,
    fun z => P.coordinates.linearEquiv (F z, G z),
    P.coordinates.linearEquiv.contDiff.contDiffOn.comp
      ((hF.mono inter_subset_left).prodMk (hG.mono inter_subset_right))
      (mapsTo_univ _ _), ?_⟩
  filter_upwards [heF, heG] with q hqF hqG
  simp only [productChart_val, Function.comp_apply, id_eq] at hqF hqG ⊢
  rw [hqF, hqG]

/-- Cutting an ambient slice chart by an open set cuts out that same open part of the slice. -/
theorem sliceChart_inter_restrOpen {k n : ℕ} {M : Type u} [TopologicalSpace M]
    (s U : Set M) (hU : IsOpen U) (c : ModelChart n .euclidean M)
    (hc : IsSliceChart s k .euclidean c) :
    IsSliceChart (s ∩ U) k .euclidean (c.restrOpen U hU) := by
  refine ⟨hc.1, hc.2.1, ?_⟩
  ext z
  constructor
  · rintro ⟨x, ⟨⟨hxs, hxU⟩, hxc, _⟩, rfl⟩
    exact ⟨(c.restrOpen U hU).map_source ⟨hxc, hxU⟩,
      (hc.2.2 ▸ show c x ∈ c '' (s ∩ c.source) from ⟨x, ⟨hxs,hxc⟩, rfl⟩).2⟩
  · rintro ⟨hz, hplane⟩
    have hz' : z ∈ c.target := hz.1
    have hmem : z ∈ c '' (s ∩ c.source) := by rw [hc.2.2]; exact ⟨hz', hplane⟩
    obtain ⟨x, ⟨hxs, hxc⟩, hxz⟩ := hmem
    refine ⟨x, ⟨⟨hxs, ?_⟩, hxc, ?_⟩, hxz⟩
    · have := hz.2
      change c.symm z ∈ U at this
      rwa [← hxz, c.left_inv hxc] at this
    · have := hz.2
      change c.symm z ∈ U at this
      rwa [← hxz, c.left_inv hxc] at this

/-- An open ambient cut of a boundaryless embedded manifold remains a boundaryless embedded manifold. -/
theorem embedded_manifold_inter_open {k n : ℕ} {b : ModelKind}
    {M : Type u} [TopologicalSpace M] (B : SmoothManifold n b M)
    (hB : intrinsicBoundary B = ∅) (s U : Set M) (hU : IsOpen U)
    (S : SmoothManifold k .euclidean s) (hS : IsSmoothEmbedding S B Subtype.val)
    (p : M) (hp : p ∈ s ∩ U) :
    ∃ R : SmoothManifold k .euclidean ↥(s ∩ U), IsSmoothEmbedding R B Subtype.val := by
  have hrange : range (Subtype.val : s → M) = s := by ext; simp
  have hs' (x : s) : ∃ c : ModelChart n .euclidean M,
      CompatibleChart B c ∧ x.val ∈ c.source ∧ IsSliceChart s k .euclidean c := by
    simpa only [hrange] using SliceStructures.interior_slice S B Subtype.val hB hS x
      (SliceStructures.interior_of_boundary_empty S (intrinsicBoundary_euclidean S) x)
  obtain ⟨c, _, _, hc⟩ := hs' ⟨p, hp.1⟩
  have hcharts : HasSliceCharts B (s ∩ U) k .euclidean := by
    refine ⟨hc.1, ?_⟩
    intro x hx
    obtain ⟨d, hd, hxd, hs⟩ := hs' ⟨x, hx.1⟩
    refine ⟨.euclidean, Or.inl rfl, d.restrOpen U hU,
      SliceStructures.compatibleChart_restrOpen B d hd U hU, ⟨hxd,hx.2⟩,
      sliceChart_inter_restrOpen s U hU d hs⟩
  obtain ⟨R, hR, _⟩ := SliceStructures.exists_slice_manifold B (s ∩ U) hcharts
  exact ⟨R, hR⟩

/-- An open ambient cut restricts a smooth local action product chart, preserving its identity neighborhood. -/
theorem restrict_localProductSlice {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M} {p : M}
    (H : SmoothLieAction A B) (L : LocalProductSlice A B p)
    (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ L' : LocalProductSlice A B p,
      L'.carrier = L.carrier ∩ U ∧ L'.identityNeighborhood = L.identityNeighborhood := by
  classical
  let s := L.carrier ∩ U
  have hp : p ∈ s := ⟨L.contains, hpU⟩
  obtain ⟨S, hS⟩ := embedded_manifold_inter_open B H.space_boundary L.carrier U hU
    L.slice L.embedding p hp
  obtain ⟨Q⟩ := boundarylessProduct_nonempty A S H.group_boundary (intrinsicBoundary_euclidean S)
  let i : s → L.carrier := Set.inclusion inter_subset_left
  have hi : Topology.IsOpenEmbedding i := by
    apply Topology.IsOpenEmbedding.inclusion
    convert hU.preimage (continuous_subtype_val : Continuous (Subtype.val : L.carrier → M)) using 1
    ext x
    simp [s]
  let j : G × s → G × L.carrier := fun z => (z.1, i z.2)
  have hj : Topology.IsOpenEmbedding j := (Homeomorph.refl G).isOpenEmbedding.prodMap hi
  letI : Nonempty (G × s) := ⟨(1, ⟨p, hp⟩)⟩
  let J := hj.toOpenPartialHomeomorph j
  let h := J.trans L.chart
  have hsource : h.source = L.identityNeighborhood ×ˢ univ := by
    ext z
    simp only [h, OpenPartialHomeomorph.trans_source, J,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply,
      Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage, L.chart_source,
      Set.mem_prod, and_true, j]
  have haction : EqOn h (fun z : G × s => z.1 • z.2.val) h.source := by
    intro z hz
    change L.chart (j z) = _
    exact L.chart_action hz.2
  have htarget : h.target ⊆ L.chart.target := fun y hy => hy.1
  have hinverse : ∀ y ∈ h.target, j (h.symm y) = L.chart.symm y := by
    intro y hy
    exact J.right_inv hy.2
  have hproj := differential_product L.product.left L.product.right L.product.coordinates
    L.product.manifold L.product.atlas_eq
  have hfst : IsSmoothMap L.product.manifold A Prod.fst :=
    smooth_comp (f := Prod.fst) (g := id) hproj.1 L.product.left_from
  have hsnd : IsSmoothMap L.product.manifold B
      (fun z : G × L.carrier => z.2.val) :=
    smooth_comp (f := Prod.snd) (g := Subtype.val)
      (smooth_comp (f := Prod.snd) (g := id) hproj.2.1 L.product.right_from) L.embedding.1
  have hsm : ManifoldContDiffOn ⊤ B.smoothStructure.val Q.manifold.smoothStructure.val
      h.symm h.target := by
    intro y hy
    have hold := L.smooth_inverse y (htarget hy)
    have heq : (fun z => j (h.symm z)) =ᶠ[𝓝 y] L.chart.symm := by
      filter_upwards [h.open_target.mem_nhds hy] with z hz
      exact hinverse z hz
    have hf := manifoldContDiffAt_comp L.product.manifold.smoothStructure.property.1.1
      hold (hfst (L.chart.symm y))
    have hf' : ManifoldContDiffAt ⊤ B.smoothStructure.val A.smoothStructure.val
        (fun z => (h.symm z).1) y := by
      apply manifoldContDiffAt_congr hf
      filter_upwards [heq] with z hz
      exact (congrArg Prod.fst hz).symm
    have hs := manifoldContDiffAt_comp L.product.manifold.smoothStructure.property.1.1
      hold (hsnd (L.chart.symm y))
    have hs' : ManifoldContDiffAt ⊤ B.smoothStructure.val B.smoothStructure.val
        (fun z => (h.symm z).2.val) y := by
      apply manifoldContDiffAt_congr hs
      filter_upwards [heq] with z hz
      exact (congrArg (fun w : G × L.carrier => w.2.val) hz).symm
    have hs'' := smooth_factor_through_immersion_at B B s S H.space_boundary
      hS.1 hS.2.2.1 (fun z => (h.symm z).2) y hs'
    exact smooth_pair_at B Q y hf' hs''
  exact ⟨⟨s, hp, S, hS, Q, L.identityNeighborhood, L.neighborhood_open,
    L.one_mem, h, hsource, haction, hsm⟩, rfl, rfl⟩

/-- Properness shrinks the local transverse product into the complete smooth
slice over an open saturated neighborhood of the original orbit. -/
theorem globalSlice_of_localProductSlice
    {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (hfree : FreeAction G M)
    (hproper : IsProper (actionTransport (G := G) (M := M)))
    (p : M) (L : LocalProductSlice A B p) : Nonempty (GlobalSlice A B p) := by
  have hinj : Set.InjOn (fun z : G × M => z.1 • z.2)
      (L.identityNeighborhood ×ˢ L.carrier) := by
    rintro ⟨g, x⟩ hx ⟨k, y⟩ hy hxy
    have hx' : (g, (⟨x, hx.2⟩ : L.carrier)) ∈ L.chart.source :=
      L.chart_source ▸ ⟨hx.1, mem_univ _⟩
    have hy' : (k, (⟨y, hy.2⟩ : L.carrier)) ∈ L.chart.source :=
      L.chart_source ▸ ⟨hy.1, mem_univ _⟩
    have he := L.chart.injOn hx' hy'
      ((L.chart_action hx').trans (hxy.trans (L.chart_action hy').symm))
    exact Prod.ext (congrArg (fun z : G × L.carrier => z.1) he)
      (congrArg (fun z : G × L.carrier => z.2.val) he)
  obtain ⟨U, hU, hpU, hsmall⟩ := small_transporters_of_smooth A B H hfree hproper
    p L.identityNeighborhood L.neighborhood_open L.one_mem
  have hsep := no_transport_of_local_injective L.identityNeighborhood L.carrier U
    L.one_mem hsmall hinj
  obtain ⟨L', hcarrier, _⟩ := restrict_localProductSlice H L U hU hpU
  apply globalSlice_of_separated_localProductSlice H p L'
  simpa only [hcarrier] using hsep

/-- Postcomposition by a diffeomorphism preserves immersion. -/
theorem immersion_postcomp_diffeomorph {l m n : ℕ} {a b c : ModelKind} {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold l a X) (B : SmoothManifold m b Y) (C : SmoothManifold n c Z)
    (f : X → Y) (hf : IsSmoothMap A B f) (hi : IsImmersion A B f)
    (h : Diffeomorph B.smoothStructure.val C.smoothStructure.val) :
    IsImmersion A C (h.toEquiv ∘ f) := by
  intro p
  obtain ⟨E, hE⟩ := differential_diffeomorph B C h (f p)
  obtain ⟨L, hL, _⟩ := differential_exists A B f hf p
  have hcomp := differential_comp A B C f h.toEquiv hf h.contDiff_toFun p
    L E.toLinearMap hL hE
  have hLinj := (MapClasses.smooth_tangent_invariants A B f hf p L hL).2.1.mp (hi p)
  exact (MapClasses.smooth_tangent_invariants A C _ (smooth_comp hf h.contDiff_toFun)
    p _ hcomp).2.1.mpr (E.injective.comp hLinj)

/-- Return a local product slice from compatible Euclidean presentations to
its original manifold presentations. The geometric chart is unchanged. -/
theorem localProductSlice_of_euclidean {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M} {p : M}
    (H : SmoothLieAction A B)
    (L : LocalProductSlice H.actionProduct.left H.actionProduct.right p) :
    Nonempty (LocalProductSlice A B p) := by
  let D : Diffeomorph H.actionProduct.right.smoothStructure.val B.smoothStructure.val :=
    ⟨Equiv.refl M, H.actionProduct.right_from, H.actionProduct.right_to⟩
  have hi : IsSmoothEmbedding L.slice B Subtype.val := by
    refine ⟨smooth_comp (f := Subtype.val) (g := id) L.embedding.1
      H.actionProduct.right_from, L.embedding.2.1, ?_, L.embedding.2.2.2⟩
    exact immersion_postcomp_diffeomorph L.slice H.actionProduct.right B
      Subtype.val L.embedding.1 L.embedding.2.2.1 D
  let Q := rebase_boundarylessProduct L.product A L.slice
    H.actionProduct.left_from H.actionProduct.left_to
    (manifoldContDiff_id _ _ L.slice.smoothStructure.property.1)
    (manifoldContDiff_id _ _ L.slice.smoothStructure.property.1)
  have hsm : ManifoldContDiffOn ⊤ B.smoothStructure.val Q.manifold.smoothStructure.val
      L.chart.symm L.chart.target := by
    intro y hy
    exact manifoldContDiffAt_comp H.actionProduct.right.smoothStructure.property.1.1
      (H.actionProduct.right_to y) (L.smooth_inverse y hy)
  exact ⟨⟨L.carrier, L.contains, L.slice, hi, Q, L.identityNeighborhood,
    L.neighborhood_open, L.one_mem, L.chart, L.chart_source, L.chart_action, hsm⟩⟩

/-- Smooth compatible coordinates can be used in the all-charts definition,
even when their model differs from the original uniform model. -/
theorem smoothAt_of_compatible_coordinates {m n : ℕ} {a b : ModelKind}
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : SmoothManifold m a X) (B : SmoothManifold n b Y)
    (c : ModelChart m .euclidean X) (hc : CompatibleChart A c)
    (e : ModelChart n .euclidean Y) (he : CompatibleChart B e)
    (f : X → Y) (x : X) (hx : x ∈ c.source) (hfx : f x ∈ e.source)
    (hcont : ContinuousAt f x) (hcoord : ChartContDiffAt ⊤ c e f x) :
    ManifoldContDiffAt ⊤ A.smoothStructure.val B.smoothStructure.val f x := by
  refine ⟨hcont, ?_⟩
  intro j hj q hq hxj hfxq
  have hleft := (hc j hj x hx hxj).2
  have hright := LocalCoordinateExtension.precomp
    (he q hq (f x) hfx hfxq).1 hcont rfl
  exact LocalCoordinateExtension.comp hright (LocalCoordinateExtension.comp hcoord hleft)

/-- A local product inverse is smooth when its two compatible coordinate
components are the components of one Euclidean smooth inverse. -/
theorem smooth_inverse_of_compatible_product_coordinates
    {d k n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M)
    (s : Set M) (S : SmoothManifold k .euclidean s)
    (Q : BoundarylessProduct A S)
    (eG : ModelChart d .euclidean G) (heG : CompatibleChart A eG)
    (eS : ModelChart k .euclidean s) (heS : CompatibleChart S eS)
    (c : ModelChart n .euclidean M) (hc : CompatibleChart B c)
    (h : OpenPartialHomeomorph (G × s) M)
    (j : OpenPartialHomeomorph (Euclidean d × Euclidean k) (Euclidean n))
    (hj : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target)
    (hcoord : ∀ y ∈ h.target,
      y ∈ c.source ∧ (h.symm y).1 ∈ eG.source ∧ (h.symm y).2 ∈ eS.source ∧
      (c y).val ∈ j.target ∧
      ((eG (h.symm y).1).val, (eS (h.symm y).2).val) = j.symm (c y).val) :
    ManifoldContDiffOn ⊤ B.smoothStructure.val Q.manifold.smoothStructure.val
      h.symm h.target := by
  intro y hy
  obtain ⟨hyc, hyG, hyS, hyj, hxy⟩ := hcoord y hy
  have hfirst : ChartContDiffAt ⊤ c eG (fun z => (h.symm z).1) y := by
    refine ⟨j.target, j.open_target, hyj,
      fun z => (j.symm z).1, contDiff_fst.comp_contDiffOn hj, ?_⟩
    filter_upwards [h.open_target.mem_nhds hy] with z hz
    exact (congrArg Prod.fst (hcoord z hz).2.2.2.2).symm
  have hsecond : ChartContDiffAt ⊤ c eS (fun z => (h.symm z).2) y := by
    refine ⟨j.target, j.open_target, hyj,
      fun z => (j.symm z).2, contDiff_snd.comp_contDiffOn hj, ?_⟩
    filter_upwards [h.open_target.mem_nhds hy] with z hz
    exact (congrArg Prod.snd (hcoord z hz).2.2.2.2).symm
  have hf := smoothAt_of_compatible_coordinates B A c hc eG heG
    (fun z => (h.symm z).1) y hyc hyG
    (continuous_fst.continuousAt.comp (h.symm.continuousAt hy)) hfirst
  have hs := smoothAt_of_compatible_coordinates B S c hc eS heS
    (fun z => (h.symm z).2) y hyc hyS
    (continuous_snd.continuousAt.comp (h.symm.continuousAt hy)) hsecond
  exact smooth_pair_at B Q y hf hs

/-- Every chart in a compatible Euclidean presentation is a compatible chart
for the original smooth structure. -/
theorem compatibleChart_of_smooth_identity {n : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M]
    (A : SmoothManifold n a M) (E : SmoothManifold n .euclidean M)
    (hAE : IsSmoothMap A E id) (hEA : IsSmoothMap E A id)
    (e : ModelChart n .euclidean M) (he : e ∈ E.smoothStructure.val) :
    CompatibleChart A e := by
  intro j hj p hp hpj
  exact ⟨(hEA p).2 e he j hj hp hpj, (hAE p).2 j hj e he hpj hp⟩

/-- The transported transverse chart supplies the full local geometric
product data, including its smooth inverse in the original smooth structures. -/
theorem localProductSlice_of_transverse_chart {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (hdn : d ≤ n)
    (cg : ModelChart d .euclidean G) (hpG : (1 : G) ∈ cg.source)
    (hcG : SliceData.CompatibleChart A cg)
    (c : ModelChart n .euclidean M) (hc : SliceData.CompatibleChart B c)
    (p : M) (hp : p ∈ c.source)
    (U : Set (Euclidean d × Euclidean n))
    (hUaction : MapsTo (fun z => (InteriorInverse.ambientChart cg).symm z.1 •
      (InteriorInverse.ambientChart c).symm z.2) U (InteriorInverse.ambientChart c).source)
    (E : (Euclidean d × Euclidean (n-d)) ≃L[ℝ] Euclidean n)
    (W : Set (Euclidean d)) (V : Set (Euclidean (n-d)))
    (hW : IsOpen W) (h1W : (cg 1).val ∈ W) (hV : IsOpen V) (h0V : (0 : Euclidean (n-d)) ∈ V)
    (j : OpenPartialHomeomorph (Euclidean d × Euclidean (n-d)) (Euclidean n))
    (hjsource : j.source = W ×ˢ V)
    (hparam : MapsTo (fun z => (z.1,(c p).val + E (0,z.2))) j.source U)
    (hjeq : EqOn j (fun z => (InteriorInverse.ambientChart c)
      ((InteriorInverse.ambientChart cg).symm z.1 •
        (InteriorInverse.ambientChart c).symm ((c p).val + E (0,z.2)))) j.source)
    (hji : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target) :
    Nonempty (LocalProductSlice A B p) := by
  obtain ⟨s,hps,S,hSB,e,Wg,he,hesource,hWg,h1Wg,h,hsource,haction,hcoords⟩ :=
    local_affine_product_chart B hdn cg hpG c hc p hp U hUaction
      E W V hW h1W hV h0V j hjsource hparam hjeq
  obtain ⟨Q⟩ := boundarylessProduct_nonempty A S H.group_boundary (intrinsicBoundary_euclidean S)
  have hinv := smooth_inverse_of_compatible_product_coordinates A B s S Q cg hcG
    e he c hc h j hji hcoords
  exact ⟨⟨s,hps,S,hSB,Q,Wg,hWg,h1Wg,h,hsource,haction,hinv⟩⟩

/-- Every free smooth action has a smooth transverse local product through every point. -/
theorem localProductSlice_exists {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    {A : SmoothManifold d a G} {B : SmoothManifold n b M}
    (H : SmoothLieAction A B) (hfree : FreeAction G M) (p : M) :
    Nonempty (LocalProductSlice A B p) := by
  obtain ⟨eG, heG, h1⟩ := H.actionProduct.left.smoothStructure.property.1.1 (1 : G)
  obtain ⟨c, hc, hp⟩ := H.actionProduct.right.smoothStructure.property.1.1 p
  have hcG : CompatibleChart A eG := compatibleChart_of_smooth_identity A H.actionProduct.left
    H.actionProduct.left_to H.actionProduct.left_from eG heG
  have hcM : CompatibleChart B c := compatibleChart_of_smooth_identity B H.actionProduct.right
    H.actionProduct.right_to H.actionProduct.right_from c hc
  let E := InteriorInverse.ambientChart eG
  let C := InteriorInverse.ambientChart c
  let f : Euclidean d × Euclidean n → Euclidean n :=
    fun z => C (E.symm z.1 • C.symm z.2)
  obtain ⟨U, hU, hbase, hUtarget, hUaction, hf, hid, hinj⟩ :=
    action_coordinate_data H hfree p eG heG h1 c hc hp
  have hdf : HasFDerivAt f (fderiv ℝ f (E 1,C p)) (E 1,C p) :=
    ((hf.contDiffAt (hU.mem_nhds hbase)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨hdn, T, hT, W, V, hW, h1W, hV, h0V, j, hjsource, hparam, hjeq,
      hjbase, hj, hji⟩ :=
    transverse_inverse f U hU hf (E 1) (C p) hbase (fderiv ℝ f (E 1,C p))
      hdf hid hinj
  exact localProductSlice_of_transverse_chart H hdn eG h1 hcG c hcM p hp
    U hUaction T W V hW h1W hV h0V j hjsource hparam hjeq hji

/-- Free proper actions have boundaryless transverse slices whose action maps
are diffeomorphisms onto open saturated neighborhoods. The orbit differential
is uniquely determined and injective, and the group dimension is at most n. -/
theorem free_proper_slices :
    Specs.SmoothManifolds.Ch08.FreeProperSlices.free_proper_slicesType.{u} := by
  intro d n a b G M _ _ _ _ _ A B H hfree hproper
  have horbit := orbit_differential_injective A B H hfree
  refine ⟨horbit.1, horbit.2, ?_⟩
  intro p
  obtain ⟨L⟩ := localProductSlice_exists H hfree p
  exact globalSlice_of_localProductSlice H hfree hproper p L

end SmoothManifolds.FreeProperSlices
