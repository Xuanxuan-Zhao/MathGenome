import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.TransversePreimage
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.RegularLevels
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryRegularLevels
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Basic

/-! M04.06: transverse inverse images, including ordinary boundary.
Local defining submersions reduce the structure theorem to boundary regular
fibers; compatible embedded pieces glue on the exact inverse-image subspace. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SmoothManifolds.TransversePreimage
open ModelData AtlasData MapData BoundaryData MapClassData TangentData DifferentialData
  BoundaryRegularLevelData TransversePreimageData SliceData Set Filter
open scoped Topology BoundaryConeData ContDiff
universe u v w

/-- The quotient by the tangent of S makes transversality a surjectivity test. -/
theorem quotient_comp_surjective {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W) (Q : Submodule ℝ W) (h : LinearMap.range L ⊔ Q = ⊤) :
    Function.Surjective (Q.mkQ.comp L) := by
  apply LinearMap.range_eq_top.mp
  rw [LinearMap.range_comp]
  exact (Q.map_mkQ_eq_top _).mpr (by simpa only [sup_comm] using h)

/-- A transverse inverse image of a linear subspace has the expected codimension. -/
theorem finrank_comap_of_transverse {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (L : V →ₗ[ℝ] W) (Q : Submodule ℝ W) (h : LinearMap.range L ⊔ Q = ⊤) :
    Module.finrank ℝ (Q.comap L) =
      Module.finrank ℝ V - (Module.finrank ℝ W - Module.finrank ℝ Q) := by
  have hsurj := quotient_comp_surjective L Q h
  have hker : LinearMap.ker (Q.mkQ.comp L) = Q.comap L := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hd := LinearMap.finrank_range_add_finrank_ker (Q.mkQ.comp L)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    Submodule.finrank_quotient] at hd
  omega

/-- The same quotient surjectivity forces the ambient codimension bound. -/
theorem codimension_le_of_transverse {V W Z : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] [FiniteDimensional ℝ Z]
    (L : V →ₗ[ℝ] W) (I : Z →ₗ[ℝ] W) (hI : Function.Injective I)
    (h : LinearMap.range L ⊔ LinearMap.range I = ⊤) :
    Module.finrank ℝ W - Module.finrank ℝ Z ≤ Module.finrank ℝ V := by
  have hd := LinearMap.finrank_le_finrank_of_surjective
    (quotient_comp_surjective L (LinearMap.range I) h)
  rwa [Submodule.finrank_quotient, LinearMap.finrank_range_of_inj hI] at hd

/-- A surjective normal map kills the tangent of the target submanifold.
Transversality then makes the composite differential surjective. -/
theorem surjective_comp_of_transverse {V W Z H : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z] [AddCommGroup H] [Module ℝ H]
    (L : V →ₗ[ℝ] W) (I : Z →ₗ[ℝ] W) (G : W →ₗ[ℝ] H)
    (hG : Function.Surjective G) (hGI : G.comp I = 0)
    (ht : LinearMap.range L ⊔ LinearMap.range I = ⊤) :
    Function.Surjective (G.comp L) := by
  have hh := congrArg (Submodule.map G) ht
  rw [Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp,
    hGI, LinearMap.range_zero, sup_bot_eq, Submodule.map_top,
    LinearMap.range_eq_top.mpr hG] at hh
  exact LinearMap.range_eq_top.mp hh

/-- A map that is constant has zero full differential, including at a face. -/
theorem isDifferential_zero_of_constant {m n : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (p : M) (y : N) (hc : ∀ x, f x = y) :
    IsDifferential S T f p 0 := by
  intro v h k r _hr hk
  have hkeq : k = algebraMap ℝ (SmoothGerm S p) (r y) := by
    apply Subtype.ext
    rw [← hk]
    change Germ.ofFun (r ∘ f) = Germ.ofFun (fun _ : M => r y)
    congr 1
    funext x
    exact congrArg r (hc x)
  change (0 : ℝ) = v.val k
  rw [hkeq, derivation_kills_constants]

/-- Transversality makes a composite with a defining submersion regular.
Only constancy on the embedded subspace is used in this pointwise assertion. -/
theorem submersion_comp_of_transverseAt {m n k l : ℕ} {a b c d : ModelKind}
    {M N Q : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (E : SmoothManifold l d Q)
    (f : M → N) (g : N → Q)
    (he : IsSmoothEmbedding R T Subtype.val) (hf : IsSmoothMap S T f)
    (hg : IsSmoothMap T E g) (y : Q) (hzero : ∀ q : s, g q.val = y)
    (p : M) (hp : f p ∈ s) (ht : IsTransverseAt S T R f p hp)
    (hsub : IsSubmersionAt T E g (f p)) : IsSubmersionAt S E (g ∘ f) p := by
  obtain ⟨L, hL, _⟩ := differential_exists S T f hf p
  obtain ⟨I, hI, _⟩ := differential_exists R T Subtype.val he.1 ⟨f p, hp⟩
  obtain ⟨G, hG, _⟩ := differential_exists T E g hg (f p)
  have hGs : Function.Surjective G :=
    (MapClasses.smooth_tangent_invariants T E g hg (f p) G hG).2.2.mp hsub
  have hgi : IsSmoothMap R E (g ∘ Subtype.val) :=
    manifoldContDiff_comp ⊤ _ _ _ T.smoothStructure.property.1.1 Subtype.val g he.1 hg
  have hGI := differential_comp R T E Subtype.val g he.1 hg ⟨f p, hp⟩ I G hI hG
  obtain ⟨D, _, huniq⟩ := differential_exists R E (g ∘ Subtype.val) hgi ⟨f p, hp⟩
  have hGIz : G.comp I = 0 := (huniq _ hGI).trans
    (huniq _ (isDifferential_zero_of_constant R E (g ∘ Subtype.val) ⟨f p, hp⟩ y hzero)).symm
  have hgf : IsSmoothMap S E (g ∘ f) :=
    manifoldContDiff_comp ⊤ _ _ _ T.smoothStructure.property.1.1 f g hf hg
  have hGL := differential_comp S T E f g hf hg p L G hL hG
  exact (MapClasses.smooth_tangent_invariants S E (g ∘ f) hgf p (G.comp L) hGL).2.2.mpr
    (surjective_comp_of_transverse L I G hGs hGIz (ht L I hL hI))

/-- For a submanifold presented as a regular fiber, the two transversality
hypotheses give the two distinct regular-value hypotheses of the boundary
regular-level theorem. In particular the boundary hypothesis is retained. -/
theorem regular_values_of_transverse_defining_submersion
    {m n k l : ℕ} {a b c d : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (E : SmoothManifold l d Q)
    (f : M → N) (g : N → Q)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (he : IsSmoothEmbedding R T Subtype.val) (hf : IsSmoothMap S T f)
    (hg : IsSmoothMap T E g) (hB : IsNaturalBoundaryStructure S B)
    (y : Q) (hzero : ∀ x, g x = y ↔ x ∈ s) (hsub : IsSubmersion T E g)
    (ht : IsTransverse S T R f)
    (hbt : IsTransverse B T R (fun p => f p.val)) :
    IsRegularValue S E (g ∘ f) y ∧
      IsRegularValue B E (fun p => g (f p.val)) y := by
  have hconst : ∀ q : s, g q.val = y := fun q => (hzero q.val).mpr q.property
  have hbf : IsSmoothMap B T (fun p => f p.val) :=
    manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1 Subtype.val f hB.1 hf
  constructor
  · intro p hp
    have hps : f p ∈ s := (hzero (f p)).mp hp
    exact submersion_comp_of_transverseAt S T s R E f g he hf hg y hconst
      p hps (ht p hps) (hsub (f p))
  · intro p hp
    have hps : f p.val ∈ s := (hzero (f p.val)).mp hp
    exact submersion_comp_of_transverseAt B T s R E (fun q => f q.val) g he hbf hg
      y hconst p hps (hbt p hps) (hsub (f p.val))

/-- An immersion has a smooth local left inverse in ambient coordinates,
even when the ambient manifold has boundary. The Euclidean straightening
need not preserve the ambient half-space. -/
theorem immersion_coordinate_retraction {k n : ℕ} {a b : ModelKind}
    {Q : Type u} {N : Type v} [TopologicalSpace Q] [TopologicalSpace N]
    (R : SmoothManifold k a Q) (T : SmoothManifold n b N) (i : Q → N)
    (hi : IsSmoothMap R T i) (q : Q) (himm : IsImmersionAt R T i q)
    (e : ModelChart k a Q) (d : ModelChart n b N)
    (he : e ∈ R.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hqe : q ∈ e.source) (hqd : i q ∈ d.source) :
    LocalCoordinateExtension ⊤ (fun x => (d (i x)).val) (fun x => (e x).val) q := by
  obtain ⟨U, hU, hqU, g, hg, heq⟩ := (hi q).2 e he d hd hqe hqd
  have hder := ((hg.contDiffAt (hU.mem_nhds hqU)).differentiableAt
    (by simp : ((⊤ : ℕ∞) : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hJ : FiniteRegularityData.chartDerivative e d i q = fderiv ℝ g (e q).val :=
    FiniteRegularity.coordinateDerivative_eq e _ q hqe _ ⟨g, hder, heq⟩
  have hinj : Function.Injective (fderiv ℝ g (e q).val) := by
    rw [← hJ]
    exact (MapClasses.chart_invariants R T i
      (manifoldContDiff_of_le ⊤ 1 _ _ i le_top hi) q e d he hd hqe hqd).2.1.mp himm
  obtain ⟨_, h, hhs, _, O, hO, hqO, hform⟩ :=
    BoundaryImmersion.euclidean_immersion ⊤ le_top g U hU hg (e q).val hqU _ hder hinj
  have hbase : g (e q).val = (d (i q)).val := heq.eq_of_nhds
  refine ⟨h.source, h.open_source, (by change (d (i q)).val ∈ h.source; rw [← hbase]; exact (hform _ hqO).1),
    (fun z => (h z).1), contDiff_fst.comp_contDiffOn hhs, ?_⟩
  have hecont : ContinuousAt (fun x => (e x).val) q :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hqe)
  filter_upwards [hecont.preimage_mem_nhds (hO.mem_nhds hqO), heq] with x hx heqx
  rw [← heqx, (hform _ hx).2]

/-- Smoothness into an immersed manifold follows from ambient smoothness
and continuity into its given topology. This includes ambient boundary points. -/
theorem smooth_factor_of_immersion {l k n : ℕ} {a b c : ModelKind}
    {P : Type u} {Q : Type v} {N : Type w}
    [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace N]
    (A : SmoothManifold l a P) (R : SmoothManifold k b Q)
    (T : SmoothManifold n c N) (i : Q → N)
    (hi : IsSmoothMap R T i) (himm : IsImmersion R T i)
    (g : P → Q) (hgc : Continuous g) (hg : IsSmoothMap A T (i ∘ g)) :
    IsSmoothMap A R g := by
  intro p
  obtain ⟨e, he, hpe⟩ := R.smoothStructure.property.1.1 (g p)
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (i (g p))
  obtain ⟨c, hc, hpc⟩ := A.smoothStructure.property.1.1 p
  have hret := immersion_coordinate_retraction R T i hi (g p) (himm (g p))
    e d he hd hpe hpd
  have hretg := LocalCoordinateExtension.precomp hret hgc.continuousAt rfl
  apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ A.smoothStructure.property.1
    R.smoothStructure.property.1 g p).mpr
  exact ⟨hgc.continuousAt, c, hc, e, he, hpc, hpe,
    LocalCoordinateExtension.comp hretg ((hg p).2 c hc d hd hpc hpd)⟩

/-- A local embedded piece over an open part of a fixed ambient subspace.
The boundary condition is relative to the ambient intrinsic boundary. -/
structure EmbeddedPiece {m : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m b M) (s : Set M)
    (k : ℕ) (a : ModelKind) where
  domain : Set s
  open_domain : IsOpen domain
  manifold : SmoothManifold k a domain
  embedding : IsSmoothEmbedding manifold S (fun x => x.val.val)
  boundary : intrinsicBoundary manifold = (fun x => x.val.val) ⁻¹' intrinsicBoundary S

local instance modelSpaceNonempty (k : ℕ) (a : ModelKind) : Nonempty (ModelSpace k a) :=
  ⟨⟨0, by cases a <;> cases k <;> simp [ModelData.modelSet, ModelData.halfSpaceSet]⟩⟩

/-- Extend a chart from an open piece to a chart on the whole subspace. -/
noncomputable def pieceChart {m k : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold m b M} {s : Set M}
    (P : EmbeddedPiece S s k a) (c : ModelChart k a P.domain) : ModelChart k a s :=
  c.lift_openEmbedding P.open_domain.isOpenEmbedding_subtypeVal

@[simp] theorem pieceChart_apply {m k : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold m b M} {s : Set M}
    (P : EmbeddedPiece S s k a) (c : ModelChart k a P.domain) (x : P.domain) :
    pieceChart P c x.val = c x := by
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

@[simp] theorem pieceChart_source {m k : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold m b M} {s : Set M}
    (P : EmbeddedPiece S s k a) (c : ModelChart k a P.domain) :
    (pieceChart P c).source = Subtype.val '' c.source := rfl

/-- Each extended chart has a smooth inclusion and a smooth ambient
coordinate retraction, with no boundarylessness assumption on the ambient. -/
theorem pieceChart_inclusion_retraction {m k : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold m b M} {s : Set M}
    (P : EmbeddedPiece S s k a) (c : ModelChart k a P.domain)
    (hc : c ∈ P.manifold.smoothStructure.val) (p : s) (hp : p ∈ (pieceChart P c).source)
    (d : ModelChart m b M) (hd : d ∈ S.smoothStructure.val) (hpd : p.val ∈ d.source) :
    ChartContDiffAt ⊤ (pieceChart P c) d Subtype.val p ∧
    LocalCoordinateExtension ⊤ (fun x : s => (d x.val).val)
      (fun x => (pieceChart P c x).val) p := by
  obtain ⟨q, hqc, rfl⟩ := hp
  have hfor := (P.embedding.1 q).2 c hc d hd hqc hpd
  have hback := immersion_coordinate_retraction P.manifold S (fun x => x.val.val)
    P.embedding.1 q (P.embedding.2.2.1 q) c d hc hd hqc hpd
  constructor
  · apply (localCoordinateExtension_open_subtype_iff P.open_domain
      (fun x : s => (pieceChart P c x).val) (fun x => (d x.val).val) q).mp
    simpa only [MapData.ChartContDiffAt, Function.comp_def, pieceChart_apply] using hfor
  · apply (localCoordinateExtension_open_subtype_iff P.open_domain
      (fun x : s => (d x.val).val) (fun x => (pieceChart P c x).val) q).mp
    simpa only [Function.comp_def, pieceChart_apply] using hback

/-- The atlas consists of all charts supplied by local embedded pieces. -/
def embeddedPieceAtlas {m : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m b M) (s : Set M)
    (k : ℕ) (a : ModelKind) : Set (ModelChart k a s) :=
  {e | ∃ P : EmbeddedPiece S s k a,
    ∃ c ∈ P.manifold.smoothStructure.val, e = pieceChart P c}

/-- Smooth retractions through a common ambient chart give compatibility
of charts coming from different local pieces. -/
theorem embeddedPieceAtlas_transition {m k : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m b M) (s : Set M)
    (e e' : ModelChart k a s) (he : e ∈ embeddedPieceAtlas S s k a)
    (he' : e' ∈ embeddedPieceAtlas S s k a)
    (p : s) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    ChartContDiffAt ⊤ e e' id p := by
  obtain ⟨P, c, hc, rfl⟩ := he
  obtain ⟨P', c', hc', rfl⟩ := he'
  obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1 p.val
  exact LocalCoordinateExtension.comp
    (pieceChart_inclusion_retraction P' c' hc' p hp' d hd hpd).2
    (pieceChart_inclusion_retraction P c hc p hp d hd hpd).1

/-- Compatible local embedded pieces glue on the actual ambient subspace.
This also glues their intrinsic-boundary equality, and allows an empty cover
when the subspace is empty. -/
theorem exists_embedded_of_local_pieces {m k : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m b M) (s : Set M)
    (hcover : ∀ p : s, ∃ P : EmbeddedPiece S s k a, p ∈ P.domain) :
    ∃ R : SmoothManifold k a s,
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S := by
  letI := S.topologicalManifold.hausdorff
  letI := S.topologicalManifold.secondCountable
  let A := embeddedPieceAtlas S s k a
  have hAcover : IsAtlas A := by
    intro p
    obtain ⟨P, hp⟩ := hcover p
    obtain ⟨c, hc, hpc⟩ := P.manifold.smoothStructure.property.1.1 ⟨p, hp⟩
    exact ⟨pieceChart P c, ⟨P, c, hc, rfl⟩, ⟨⟨p, hp⟩, hpc, rfl⟩⟩
  have hA : IsContDiffAtlas ⊤ A := by
    refine ⟨hAcover, ?_⟩
    intro e he e' he'
    exact contDiffCompatible_of_germs
      (embeddedPieceAtlas_transition S s e e' he he')
      (embeddedPieceAtlas_transition S s e' e he' he)
  let R : SmoothManifold k a s := {
    topologicalManifold := ⟨inferInstance, inferInstance, A, hAcover⟩
    smoothStructure := ⟨maximalExtension ⊤ A, maximalExtension_isMaximal hA⟩ }
  have hmem : ∀ e ∈ A, e ∈ R.smoothStructure.val := subset_maximalExtension hA
  have hf : IsSmoothMap R S Subtype.val := by
    intro p
    obtain ⟨e, he, hp⟩ := hAcover p
    obtain ⟨P, c, hc, rfl⟩ := he
    obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1 p.val
    apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ R.smoothStructure.property.1
      S.smoothStructure.property.1 Subtype.val p).mpr
    exact ⟨continuousAt_subtype_val, pieceChart P c, hmem _ ⟨P, c, hc, rfl⟩,
      d, hd, hp, hpd, (pieceChart_inclusion_retraction P c hc p hp d hd hpd).1⟩
  refine ⟨R, ⟨hf, Subtype.val_injective, ?_,
    ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩⟩, ?_⟩
  · intro p
    obtain ⟨e, he, hp⟩ := hAcover p
    obtain ⟨P, c, hc, rfl⟩ := he
    obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1 p.val
    exact SliceStructures.immersion_of_coordinate_retraction R S Subtype.val hf p
      (pieceChart P c) d (hmem _ ⟨P, c, hc, rfl⟩) hd hp hpd
      (pieceChart_inclusion_retraction P c hc p hp d hd hpd).2
  · ext p
    obtain ⟨P, hp⟩ := hcover p
    let q : P.domain := ⟨p, hp⟩
    obtain ⟨c, hc, hqc⟩ := P.manifold.smoothStructure.property.1.1 q
    have hpc : p ∈ (pieceChart P c).source := ⟨q, hqc, rfl⟩
    rw [intrinsicBoundary_iff_chart R (pieceChart P c) (hmem _ ⟨P, c, hc, rfl⟩) p hpc]
    have hface := intrinsicBoundary_iff_chart P.manifold c hc q hqc
    have hval : pieceChart P c p = c q := pieceChart_apply P c q
    rw [hval, ← hface, P.boundary]
    rfl

/-- A map into an embedded subspace is smooth when its ambient map is smooth. -/
theorem smooth_subtype_of_smooth_ambient {d n k : ℕ} {a b c : ModelKind}
    {P N : Type u} [TopologicalSpace P] [TopologicalSpace N]
    (A : SmoothManifold d a P) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s)
    (_hT : intrinsicBoundary T = ∅) (hR : IsSmoothEmbedding R T Subtype.val)
    (g : P → s) (hg : IsSmoothMap A T (fun x => (g x).val)) :
    IsSmoothMap A R g := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr
    (fun p => tendsto_subtype_rng.mpr (hg p).1)
  exact smooth_factor_of_immersion A R T Subtype.val hR.1 hR.2.2.1 g hgc hg

/-- The natural face atlas makes boundary inclusion an embedding of full
rank m-1. This uses actual face charts, rather than assuming that arbitrary
smooth boundary inclusions have the required rank. -/
theorem natural_boundary_embedding {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m a M)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) : IsSmoothEmbedding B S Subtype.val := by
  refine ⟨hB.1, Subtype.val_injective, ?_,
    ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩⟩
  intro p
  cases m with
  | zero =>
    have hp := p.property
    simpa only [intrinsicBoundary_zero, mem_empty_iff_false] using hp
  | succ r =>
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
    obtain ⟨e, he, hface⟩ := hB.2 c hc ⟨⟨p, hpc⟩⟩
    have hpe : p ∈ e.source := by rw [hface.1]; exact hpc
    apply SliceStructures.immersion_of_coordinate_retraction B S Subtype.val hB.1 p e c
      he hc hpe hpc
    refine ⟨univ, isOpen_univ, mem_univ _, (fun (z : Euclidean (r + 1)) (i : Fin r) => z i.castSucc), ?_, ?_⟩
    · exact (contDiff_pi.mpr (fun (i : Fin r) => contDiff_apply ℝ (fun _ : Fin (r + 1) => ℝ)
        i.castSucc)).contDiffOn
    · filter_upwards [e.open_source.mem_nhds hpe] with q hq
      funext i
      exact (hface.2.2 q hq i).symm

/-- An open subset has its embedded restricted structure and exactly the
inherited intrinsic boundary, also when the subset or its boundary is empty. -/
theorem open_subset_embedded {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m a M) (s : Set M) (hs : IsOpen s) :
    ∃ R : SmoothManifold m a s,
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S := by
  obtain ⟨R, _, hR, hf⟩ := exists_openSubset_smoothManifold S s hs
  have hA := openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 s hs
  have hcharts (p : s) (c : ModelChart m a M) (hc : c ∈ S.smoothStructure.val) :
      c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩ ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension hA ⟨⟨p⟩, c, hc, rfl⟩
  refine ⟨R, ⟨hf, Subtype.val_injective, ?_,
    ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩⟩, ?_⟩
  · intro p
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
    let d := c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩
    exact SliceStructures.immersion_of_coordinate_retraction R S Subtype.val hf p d c
      (hcharts p c hc) hc (by simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hpc)
      hpc (LocalCoordinateExtension.self ⊤ (fun x : s => (c x.val).val) p)
  · ext p
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
    let d := c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩
    have hpd : p ∈ d.source := by
      simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hpc
    rw [intrinsicBoundary_iff_chart R d (hcharts p c hc) p hpd]
    exact (intrinsicBoundary_iff_chart S c hc p.val hpc).symm

/-- A boundaryless embedded submanifold of codimension zero is open. This
uses local defining maps, and includes the vacuous case when its dimension
exceeds that of the ambient manifold and the subspace is empty. -/
theorem embedded_codimension_zero_open {n k : ℕ} {b c : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold n b N) (s : Set N)
    (R : SmoothManifold k c s) (hT : intrinsicBoundary T = ∅)
    (hR : intrinsicBoundary R = ∅) (he : IsSmoothEmbedding R T Subtype.val)
    (hcodim : n - k = 0) : IsOpen s := by
  apply isOpen_iff_forall_mem_open.mpr
  intro p hp
  obtain ⟨_, U, hU, hpU, A, _, E, _, g, _, _, hzero⟩ :=
    RegularLevels.local_defining_submersion T R Subtype.val hT hR he ⟨p, hp⟩
  refine ⟨U, ?_, hU, hpU⟩
  intro x hx
  have hg : g ⟨x, hx⟩ = 0 := by
    haveI : Subsingleton (Euclidean (n - k)) := by
      rw [hcodim]
      infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨q, hq⟩ := (hzero ⟨x, hx⟩).mpr hg
  have hqx : q.val = x := hq
  rw [← hqx]
  exact q.property

/-- The complete structure conclusion in codimension zero, with the inherited
boundary. No transversality hypothesis is needed in this special case. -/
theorem codimension_zero_preimage_structure {m n k : ℕ} {a b c : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (f : M → N)
    (hT : intrinsicBoundary T = ∅) (hR : intrinsicBoundary R = ∅)
    (he : IsSmoothEmbedding R T Subtype.val) (hf : IsSmoothMap S T f)
    (hcodim : n - k = 0) :
    ∃ P : SmoothManifold (m - (n - k)) a (f ⁻¹' s),
      IsSmoothEmbedding P S Subtype.val ∧
      intrinsicBoundary P = Subtype.val ⁻¹' intrinsicBoundary S ∧
      ((f ⁻¹' s).Nonempty → (m - (n - k)) + (n - k) = m) := by
  have hopen := (embedded_codimension_zero_open T s R hT hR he hcodim).preimage
    (RegularLevels.smoothMap_continuous S T f hf)
  obtain ⟨P, hP, hb⟩ := open_subset_embedded S (f ⁻¹' s) hopen
  rw [hcodim]
  exact ⟨P, hP, hb, fun _ => rfl⟩

/-- At a point in S, transversality implies codim S ≤ dim M. -/
theorem transverseAt_codimension_le {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    {s : Set N} (R : SmoothManifold k c s) (f : M → N)
    (he : IsSmoothEmbedding R T Subtype.val) (hf : IsSmoothMap S T f)
    (p : M) (hp : f p ∈ s) (ht : IsTransverseAt S T R f p hp) : n - k ≤ m := by
  obtain ⟨L, hL, _⟩ := differential_exists S T f hf p
  obtain ⟨I, hI, _⟩ := differential_exists R T Subtype.val he.1 ⟨f p, hp⟩
  have hinj := (MapClasses.smooth_tangent_invariants R T Subtype.val he.1
    ⟨f p, hp⟩ I hI).2.1.mp (he.2.2.1 ⟨f p, hp⟩)
  letI := (tangent_dimension S p).1
  letI := (tangent_dimension T (f p)).1
  letI := (tangent_dimension R ⟨f p, hp⟩).1
  have hd := codimension_le_of_transverse
    (V := TangentSpace S p) (W := TangentSpace T (f p))
    (Z := TangentSpace R ⟨f p, hp⟩) L I hinj (ht L I hL hI)
  simpa only [(tangent_dimension S p).2, (tangent_dimension T (f p)).2,
    (tangent_dimension R ⟨f p, hp⟩).2] using hd

/-- Dimension and emptiness follow separately on M and on its natural boundary. -/
theorem transverse_preimage_dimension_proof :
    Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_dimensionType.{u} := by
  intro m n k a b c M N _ _ S T s R f B _hT _hR he hf hB ht hbt
  have hd : (f ⁻¹' s).Nonempty → n - k ≤ m := by
    rintro ⟨p, hp⟩
    exact transverseAt_codimension_le S T R f he hf p hp (ht p hp)
  refine ⟨hd, ?_, ?_⟩
  · intro hdim
    exact eq_empty_iff_forall_notMem.mpr (fun p hp => (not_le_of_gt hdim) (hd ⟨p, hp⟩))
  · rintro ⟨p, hp, hpb⟩
    have hm : 0 < m := by
      by_contra h
      have hz : m = 0 := by omega
      subst m
      simpa only [intrinsicBoundary_zero, mem_empty_iff_false] using hpb
    have hbf : IsSmoothMap B T (fun q => f q.val) :=
      manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1
        Subtype.val f hB.1 hf
    exact ⟨hm, transverseAt_codimension_le B T R (fun q => f q.val) he hbf
      ⟨p, hpb⟩ hp (hbt ⟨p, hpb⟩ hp)⟩

/-- The chain rule gives inclusion in the tangent inverse image. The quotient
rank-nullity formula and the expected dimension then give equality. -/
theorem transverse_preimage_tangent_proof :
    Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u} := by
  intro m n k a b c d M N _ _ S T s R f hT _hR he hf ht P hP p L I K hL hI hK
  have hKi : Function.Injective K :=
    (MapClasses.smooth_tangent_invariants P S Subtype.val hP.1 p K hK).2.1.mp
      (hP.2.2.1 p)
  have hIi : Function.Injective I :=
    (MapClasses.smooth_tangent_invariants R T Subtype.val he.1
      ⟨f p.val, p.property⟩ I hI).2.1.mp (he.2.2.1 ⟨f p.val, p.property⟩)
  let g : (f ⁻¹' s) → s := fun x => ⟨f x.val, x.property⟩
  have hfg : IsSmoothMap P T (f ∘ Subtype.val) :=
    manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1 Subtype.val f hP.1 hf
  have hg : IsSmoothMap P R g := smooth_subtype_of_smooth_ambient P T s R hT he g hfg
  obtain ⟨J, hJ, _⟩ := differential_exists P R g hg p
  have hIJ := differential_comp P R T g Subtype.val hg he.1 p J I hJ hI
  have hLK := differential_comp P S T Subtype.val f hP.1 hf p K L hK hL
  obtain ⟨D, _hD, huniq⟩ := differential_exists P T (f ∘ Subtype.val) hfg p
  have hcomm : I.comp J = L.comp K := (huniq _ hIJ).trans (huniq _ hLK).symm
  have hle : LinearMap.range K ≤ (LinearMap.range I).comap L := by
    rintro _ ⟨v, rfl⟩
    exact ⟨J v, DFunLike.congr_fun hcomm v⟩
  letI := (tangent_dimension S p.val).1
  letI := (tangent_dimension T (f p.val)).1
  letI := (tangent_dimension R ⟨f p.val, p.property⟩).1
  letI := (tangent_dimension P p).1
  have hdim := finrank_comap_of_transverse
    (V := TangentSpace S p.val) (W := TangentSpace T (f p.val))
    L (LinearMap.range I) (ht p.val p.property L I hL hI)
  simp only [(tangent_dimension S p.val).2, (tangent_dimension T (f p.val)).2,
    LinearMap.finrank_range_of_inj hIi, (tangent_dimension R ⟨f p.val, p.property⟩).2] at hdim
  have hdimK : Module.finrank ℝ (LinearMap.range K) = m - (n - k) :=
    (LinearMap.finrank_range_of_inj hKi).trans (tangent_dimension P p).2
  exact ⟨hKi, Submodule.eq_of_le_of_finrank_eq (K := ℝ)
    (V := TangentSpace S p.val) hle (hdimK.trans hdim.symm)⟩

/-- The empty inverse image has the required embedded structure in every
expected dimension, without a dimension inequality or transversality assumption. -/
theorem empty_preimage_structure {m n k : ℕ} {a : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (s : Set N) (f : M → N)
    (hempty : f ⁻¹' s = ∅) :
    ∃ P : SmoothManifold (m - (n - k)) a (f ⁻¹' s),
      IsSmoothEmbedding P S Subtype.val ∧
      intrinsicBoundary P = Subtype.val ⁻¹' intrinsicBoundary S ∧
      ((f ⁻¹' s).Nonempty → (m - (n - k)) + (n - k) = m) := by
  rw [hempty]
  obtain ⟨P, hP, _⟩ := SliceStructures.empty_slice_structure (a := a) S (m - (n - k))
  refine ⟨P, hP, ?_, ?_⟩
  · ext p
    exact p.property.elim
  · rintro ⟨p, hp⟩
    exact hp.elim

theorem same_dimension_immersion_differential_bijective {m : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold m b N) (f : M → N)
    (hf : IsSmoothMap S T f) (p : M) (hi : IsImmersionAt S T f p)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : IsDifferential S T f p L) : Function.Bijective L := by
  have hinj := (MapClasses.smooth_tangent_invariants S T f hf p L hL).2.1.mp hi
  letI := (tangent_dimension S p).1
  letI := (tangent_dimension T (f p)).1
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [(tangent_dimension S p).2, (tangent_dimension T (f p)).2]

/-- Restricting the source along an equal-dimensional immersion preserves
transversality, since its full differential is onto. -/
theorem transverse_precomp_of_immersion {m n k : ℕ} {a a' b c : ModelKind}
    {M X N : Type u} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace N]
    (S : SmoothManifold m a M) (A : SmoothManifold m a' X)
    (T : SmoothManifold n b N) {s : Set N} (R : SmoothManifold k c s)
    (j : X → M) (f : M → N)
    (hj : IsSmoothMap A S j) (hji : IsImmersion A S j)
    (hf : IsSmoothMap S T f) (ht : IsTransverse S T R f) :
    IsTransverse A T R (f ∘ j) := by
  intro p hp K I hK hI
  obtain ⟨J, hJ, _⟩ := differential_exists A S j hj p
  obtain ⟨L, hL, _⟩ := differential_exists S T f hf (j p)
  have hJs := (same_dimension_immersion_differential_bijective A S j hj p (hji p) J hJ).2
  have hfs : IsSmoothMap A T (f ∘ j) :=
    manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1 j f hj hf
  obtain ⟨D, _, hu⟩ := differential_exists A T (f ∘ j) hfs p
  have hcomp : K = L.comp J := (hu _ hK).trans
    (hu _ (differential_comp A S T j f hj hf p J L hJ hL)).symm
  rw [hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hJs, Submodule.map_top]
  exact ht (j p) hp L I hL hI

/-- Lift transversality through immersions which identify the full target
and submanifold tangent spaces. -/
theorem transverse_lift_of_immersions {m n k : ℕ} {a b b' c c' : ModelKind}
    {M N Y : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Y]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (A : SmoothManifold n b' Y) {s : Set N} (R : SmoothManifold k c s)
    {t : Set Y} (C : SmoothManifold k c' t)
    (h : Y → N) (hmem : ∀ q : t, h q.val ∈ s) (f : M → Y)
    (hh : IsSmoothMap A T h) (hhi : IsImmersion A T h)
    (hj : IsSmoothMap C R (fun q => ⟨h q.val, hmem q⟩))
    (hji : IsImmersion C R (fun q => ⟨h q.val, hmem q⟩))
    (he : IsSmoothMap R T Subtype.val) (hc : IsSmoothMap C A Subtype.val)
    (hf : IsSmoothMap S A f)
    (ht : IsTransverse S T R (h ∘ f)) : IsTransverse S A C f := by
  intro p hp L I hL hI
  obtain ⟨H, hH, _⟩ := differential_exists A T h hh (f p)
  let q : t := ⟨f p, hp⟩
  let j : t → s := fun q => ⟨h q.val, hmem q⟩
  obtain ⟨J, hJ, _⟩ := differential_exists C R j hj q
  have hJsurj := (same_dimension_immersion_differential_bijective C R j hj q (hji q) J hJ).2
  obtain ⟨G, hG, _⟩ := differential_exists R T Subtype.val he (j q)
  have hHI := differential_comp C A T Subtype.val h hc hh q I H hI hH
  have hGJ := differential_comp C R T j Subtype.val hj he q J G hJ hG
  have hgjs : IsSmoothMap C T (h ∘ Subtype.val) :=
    manifoldContDiff_comp ⊤ _ _ _ R.smoothStructure.property.1.1 j Subtype.val hj he
  obtain ⟨D, _, hu⟩ := differential_exists C T (h ∘ Subtype.val) hgjs q
  have heq : H.comp I = G.comp J := (hu _ hHI).trans (hu _ hGJ).symm
  have hHL := differential_comp S A T f h hf hh p L H hL hH
  have hsurjH := (same_dimension_immersion_differential_bijective A T h hh (f p) (hhi _) H hH)
  have htrans : LinearMap.range (H.comp L) ⊔ LinearMap.range (H.comp I) = ⊤ := by
    rw [heq, LinearMap.range_comp J G, LinearMap.range_eq_top.mpr hJsurj, Submodule.map_top]
    exact ht p (hmem q) (H.comp L) G hHL hG
  apply (Submodule.map_injective_of_injective hsurjH.1)
  rw [Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp,
    Submodule.map_top, LinearMap.range_eq_top.mpr hsurjH.2]
  exact htrans


/-- Restriction to an open submanifold induces a smooth full-rank map on its
natural boundary atlases. The hypotheses also work for any same-dimensional
embedded subspace whose intrinsic boundary is inherited. -/
theorem natural_boundary_restriction_immersion {m : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M) (V : Set M) (A : SmoothManifold m a V)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (BA : SmoothManifold (m - 1) .euclidean (intrinsicBoundary A))
    (he : IsSmoothEmbedding A S Subtype.val)
    (hB : IsNaturalBoundaryStructure S B)
    (hBA : IsNaturalBoundaryStructure A BA)
    (hb : ∀ q : intrinsicBoundary A, q.val.val ∈ intrinsicBoundary S) :
    let j : intrinsicBoundary A → intrinsicBoundary S := fun q => ⟨q.val.val, hb q⟩
    IsSmoothMap BA B j ∧ IsImmersion BA B j := by
  dsimp only
  let j : intrinsicBoundary A → intrinsicBoundary S := fun q => ⟨q.val.val, hb q⟩
  have hbe := natural_boundary_embedding S B hB
  have hbae := natural_boundary_embedding A BA hBA
  have hc : Continuous j := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hja : IsSmoothMap BA S (Subtype.val ∘ j) := by
    exact manifoldContDiff_comp ⊤ _ _ _ A.smoothStructure.property.1.1
      Subtype.val Subtype.val hBA.1 he.1
  have hjs : IsSmoothMap BA B j :=
    smooth_factor_of_immersion BA B S Subtype.val hB.1 hbe.2.2.1 j hc hja
  refine ⟨hjs, ?_⟩
  intro p
  obtain ⟨J, hJ, _⟩ := differential_exists BA B j hjs p
  obtain ⟨I, hI, _⟩ := differential_exists B S Subtype.val hB.1 (j p)
  obtain ⟨D, hD, _⟩ := differential_exists BA A Subtype.val hBA.1 p
  obtain ⟨K, hK, _⟩ := differential_exists A S Subtype.val he.1 p.val
  have hDI := differential_comp BA B S j Subtype.val hjs hB.1 p J I hJ hI
  have hDK := differential_comp BA A S Subtype.val Subtype.val hBA.1 he.1 p D K hD hK
  have hDinj := (MapClasses.smooth_tangent_invariants BA A Subtype.val hBA.1 p D hD).2.1.mp
    (hbae.2.2.1 p)
  have hKinj := (MapClasses.smooth_tangent_invariants A S Subtype.val he.1 p.val K hK).2.1.mp
    (he.2.2.1 p.val)
  have hJinj : Function.Injective J := by
    intro x y hxy
    apply hDinj
    apply hKinj
    have hcxy := congrArg I hxy
    obtain ⟨Q, _, huniq⟩ := differential_exists BA S (fun q => q.val.val) hja p
    have heq : I.comp J = K.comp D := (huniq _ hDI).trans (huniq _ hDK).symm
    change (K.comp D) x = (K.comp D) y
    rw [← heq]
    exact hcxy
  exact (MapClasses.smooth_tangent_invariants BA B j hjs p J hJ).2.1.mpr hJinj
/-- Transport a manifold to any homeomorphic space with its given topology. -/
theorem exists_manifold_diffeomorph {k : ℕ} {a : ModelKind}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : SmoothManifold k a X) (h : X ≃ₜ Y) :
    ∃ Q : SmoothManifold k a Y,
      ∃ d : Diffeomorph R.smoothStructure.val Q.smoothStructure.val,
        d.toEquiv = h.toEquiv := by
  letI := R.topologicalManifold.hausdorff
  letI := R.topologicalManifold.secondCountable
  letI : T2Space Y := h.t2Space
  letI : SecondCountableTopology Y := h.symm.secondCountableTopology
  let C := transportAtlas h R.smoothStructure.val
  have hR := R.smoothStructure.property.1
  have hC : IsContDiffAtlas ⊤ C := transportAtlas_isContDiffAtlas ⊤ _ h hR
  let Q : SmoothManifold k a Y := {
    topologicalManifold := ⟨inferInstance, inferInstance, C, hC.1⟩
    smoothStructure := ⟨maximalExtension ⊤ C, maximalExtension_isMaximal hC⟩ }
  have hRext : maximalExtension ⊤ R.smoothStructure.val = R.smoothStructure.val :=
    R.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas hR)
      (subset_maximalExtension hR)
  have hh := transportAtlas_maps ⊤ R.smoothStructure.val h hR
  have hf : IsSmoothMap R Q h := by
    change ManifoldContDiff (⊤ : ℕ∞) R.smoothStructure.val (maximalExtension ⊤ C) h
    simpa only [hRext, IsSmoothMap, Q, ManifoldSmooth] using
      (manifoldContDiff_maximalExtension_iff ⊤ R.smoothStructure.val C hR hC h).mpr hh.1
  have hb : IsSmoothMap Q R h.symm := by
    change ManifoldContDiff (⊤ : ℕ∞) (maximalExtension ⊤ C) R.smoothStructure.val h.symm
    simpa only [hRext, IsSmoothMap, Q, ManifoldSmooth] using
      (manifoldContDiff_maximalExtension_iff ⊤ C R.smoothStructure.val hC hR h.symm).mpr hh.2
  exact ⟨Q, ⟨h.toEquiv, hf, hb⟩, rfl⟩

/-- An embedded manifold and its intrinsic boundary transport through a
homeomorphism of its underlying space. -/
theorem transport_embedded {k m : ℕ} {a b : ModelKind}
    {X Y M : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    (R : SmoothManifold k a X) (S : SmoothManifold m b M)
    (i : X → M) (he : IsSmoothEmbedding R S i) (h : X ≃ₜ Y) :
    ∃ Q : SmoothManifold k a Y,
      IsSmoothEmbedding Q S (i ∘ h.symm) ∧
      intrinsicBoundary Q = h.symm ⁻¹' intrinsicBoundary R := by
  obtain ⟨Q, d, hd⟩ := exists_manifold_diffeomorph R h
  have hf : IsSmoothMap R Q h := by
    change ManifoldContDiff ⊤ _ _ h.toEquiv
    rw [← hd]
    exact d.contDiff_toFun
  have hb : IsSmoothMap Q R h.symm := by
    change ManifoldContDiff ⊤ _ _ h.toEquiv.symm
    rw [← hd]
    exact d.contDiff_invFun
  let di : Diffeomorph Q.smoothStructure.val R.smoothStructure.val :=
    ⟨h.toEquiv.symm, hb, hf⟩
  have hs : IsSmoothMap Q S (i ∘ h.symm) :=
    manifoldContDiff_comp ⊤ _ _ _ R.smoothStructure.property.1.1 h.symm i hb he.1
  refine ⟨Q, ⟨hs, he.2.1.comp h.symm.injective, ?_, ?_⟩, ?_⟩
  · intro p
    obtain ⟨D, hD⟩ := differential_diffeomorph Q R di p
    obtain ⟨I, hI, _⟩ := differential_exists R S i he.1 (h.symm p)
    have hIinj := (MapClasses.smooth_tangent_invariants R S i he.1
      (h.symm p) I hI).2.1.mp (he.2.2.1 (h.symm p))
    have hID : IsDifferential Q S (i ∘ h.symm) p (I.comp D.toLinearMap) :=
      differential_comp Q R S h.symm i hb he.1 p D.toLinearMap I hD hI
    exact (MapClasses.smooth_tangent_invariants Q S (i ∘ h.symm) hs p
      (I.comp D.toLinearMap) hID).2.1.mpr (hIinj.comp D.injective)
  · have ht := (SliceStructures.isEmbedding_of_range_homeomorph he.2.2.2).comp
      h.symm.isEmbedding
    exact ⟨ht.toHomeomorph, fun _ => rfl⟩
  · ext p
    exact (diffeomorph_boundary_iff Q R di p).symm

/-- Composition of smooth embeddings, for the accepted subspace-topology
embedding convention. -/
theorem smoothEmbedding_comp {k n m : ℕ} {a b c : ModelKind}
    {X Y M : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    (R : SmoothManifold k a X) (T : SmoothManifold n b Y)
    (S : SmoothManifold m c M) (f : X → Y) (g : Y → M)
    (hf : IsSmoothEmbedding R T f) (hg : IsSmoothEmbedding T S g) :
    IsSmoothEmbedding R S (g ∘ f) := by
  have hs : IsSmoothMap R S (g ∘ f) :=
    manifoldContDiff_comp ⊤ _ _ _ T.smoothStructure.property.1.1 f g hf.1 hg.1
  refine ⟨hs, hg.2.1.comp hf.2.1, ?_, ?_⟩
  · intro p
    obtain ⟨F, hF, _⟩ := differential_exists R T f hf.1 p
    obtain ⟨G, hG, _⟩ := differential_exists T S g hg.1 (f p)
    have hFi := (MapClasses.smooth_tangent_invariants R T f hf.1 p F hF).2.1.mp
      (hf.2.2.1 p)
    have hGi := (MapClasses.smooth_tangent_invariants T S g hg.1 (f p) G hG).2.1.mp
      (hg.2.2.1 (f p))
    have hGF := differential_comp R T S f g hf.1 hg.1 p F G hF hG
    exact (MapClasses.smooth_tangent_invariants R S (g ∘ f) hs p
      (G.comp F) hGF).2.1.mpr (hGi.comp hFi)
  · have ht := (SliceStructures.isEmbedding_of_range_homeomorph hg.2.2.2).comp
      (SliceStructures.isEmbedding_of_range_homeomorph hf.2.2.2)
    exact ⟨ht.toHomeomorph, fun _ => rfl⟩

/-- A regular fiber over an open ambient neighborhood is an open embedded
piece of the prescribed ambient subspace, after identifying the exact sets. -/
theorem exists_piece_of_local_fiber {m k : ℕ} {a b : ModelKind}
    {M : Type u} {Q : Type v} [TopologicalSpace M] [TopologicalSpace Q]
    (S : SmoothManifold m b M) (s V : Set M) (hV : IsOpen V)
    (A : SmoothManifold m b V) (hA : IsSmoothEmbedding A S Subtype.val)
    (hAb : intrinsicBoundary A = Subtype.val ⁻¹' intrinsicBoundary S)
    (F : V → Q) (y : Q) (hz : ∀ x : V, F x = y ↔ x.val ∈ s)
    (R : SmoothManifold k a (F ⁻¹' {y}))
    (hR : IsSmoothEmbedding R A Subtype.val)
    (hRb : intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary A) :
    ∃ P : EmbeddedPiece S s k a, P.domain = {x : s | x.val ∈ V} := by
  let D : Set s := {x | x.val ∈ V}
  have hD : IsOpen D := hV.preimage continuous_subtype_val
  let H : (F ⁻¹' {y}) ≃ₜ D := {
    toFun := fun x => ⟨⟨x.val.val, (hz x.val).mp x.property⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val, x.property⟩, (hz ⟨x.val.val, x.property⟩).mpr x.val.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have he : IsSmoothEmbedding R S (fun x => x.val.val) :=
    smoothEmbedding_comp R A S Subtype.val Subtype.val hR hA
  obtain ⟨P, hP, hb⟩ := transport_embedded R S (fun x => x.val.val) he H
  have hP' : IsSmoothEmbedding P S (fun x => x.val.val) := by
    change IsSmoothEmbedding P S ((fun x : F ⁻¹' {y} => x.val.val) ∘ H.symm)
    exact hP
  have hb' : intrinsicBoundary P = (fun x => x.val.val) ⁻¹' intrinsicBoundary S := by
    rw [hb, hRb, hAb]
    rfl
  exact ⟨⟨D, hD, P, hP', hb'⟩, rfl⟩

/-- An embedded map factors as an embedding through an embedded subspace. -/
theorem embedding_into_subspace {k n l : ℕ} {a b c : ModelKind}
    {X N : Type u} [TopologicalSpace X] [TopologicalSpace N]
    (C : SmoothManifold k c X) (T : SmoothManifold n b N) (U : Set N)
    (A : SmoothManifold l a U) (hA : IsSmoothEmbedding A T Subtype.val)
    (i : X → U) (hci : Continuous i)
    (he : IsSmoothEmbedding C T (fun x => (i x).val)) :
    IsSmoothEmbedding C A i := by
  have hi : IsSmoothMap C A i := smooth_factor_of_immersion C A T Subtype.val
    hA.1 hA.2.2.1 i hci he.1
  have htop : Topology.IsEmbedding (fun x => (i x).val) := by
    obtain ⟨e, heq⟩ := he.2.2.2
    have hfun : (fun x => (i x).val) = Subtype.val ∘ e := funext (fun x => (heq x).symm)
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp e.isEmbedding
  have hitop : Topology.IsEmbedding i := Topology.IsEmbedding.subtypeVal.of_comp_iff.mp htop
  refine ⟨hi, hitop.injective, ?_, ⟨hitop.toHomeomorph, fun _ => rfl⟩⟩
  intro x
  obtain ⟨L, hL, _⟩ := differential_exists C A i hi x
  obtain ⟨J, hJ, _⟩ := differential_exists A T Subtype.val hA.1 (i x)
  have hcomp := differential_comp C A T i Subtype.val hi hA.1 x L J hL hJ
  have hcompinj : Function.Injective (J.comp L) :=
    (MapClasses.smooth_tangent_invariants C T (fun x => (i x).val) he.1 x
      (J.comp L) hcomp).2.1.mp (he.2.2.1 x)
  exact (MapClasses.smooth_tangent_invariants C A i hi x L hL).2.1.mpr
    (fun v w hvw => hcompinj (congrArg J hvw))

/-- The inverse image of an open set supports the smooth restricted map. -/
theorem smooth_restriction {m n : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (f : M → N) (hf : IsSmoothMap S T f) (U : Set N)
    (A : SmoothManifold n b U) (hA : IsSmoothEmbedding A T Subtype.val)
    (D : SmoothManifold m a (f ⁻¹' U))
    (hD : IsSmoothEmbedding D S Subtype.val) :
    IsSmoothMap D A (fun x => (⟨f x.val, x.property⟩ : U)) := by
  apply smooth_factor_of_immersion D A T Subtype.val hA.1 hA.2.2.1
    (fun x => (⟨f x.val, x.property⟩ : U))
  · exact Continuous.subtype_mk
      ((RegularLevels.smoothMap_continuous S T f hf).comp continuous_subtype_val) _
  · exact manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1 Subtype.val f hD.1 hf

/-- The two orders of taking the ambient and submanifold restrictions agree. -/
def targetOpenHomeomorph {N : Type u} [TopologicalSpace N] (s U : Set N) :
    {q : s | q.val ∈ U} ≃ₜ {x : U | x.val ∈ s} where
  toFun q := ⟨⟨q.val.val, q.property⟩, q.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop


/-- Restrict an embedded target submanifold over an ambient open subset. -/
theorem local_target_restriction {n k : ℕ} {b c : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold n b N) (s U : Set N)
    (R : SmoothManifold k c s) (he : IsSmoothEmbedding R T Subtype.val)
    (hU : IsOpen U) (A : SmoothManifold n b U)
    (hA : IsSmoothEmbedding A T Subtype.val) :
    ∃ C : SmoothManifold k c {x : U | x.val ∈ s},
      IsSmoothEmbedding C A Subtype.val ∧
      IsSmoothEmbedding C R (fun x => (⟨x.val.val, x.property⟩ : s)) := by
  let W : Set s := Subtype.val ⁻¹' U
  obtain ⟨D, hD, _⟩ := open_subset_embedded R W (hU.preimage continuous_subtype_val)
  obtain ⟨C, hC, _⟩ := transport_embedded D R Subtype.val hD (targetOpenHomeomorph s U)
  change IsSmoothEmbedding C R (fun x => (⟨x.val.val, x.property⟩ : s)) at hC
  have hCT : IsSmoothEmbedding C T (fun x => x.val.val) :=
    smoothEmbedding_comp C R T (fun x => (⟨x.val.val, x.property⟩ : s)) Subtype.val hC he
  have hCA : IsSmoothEmbedding C A Subtype.val :=
    embedding_into_subspace C T U A hA Subtype.val continuous_subtype_val hCT
  exact ⟨C, hCA, hC⟩

/-- Ambient transversality gives both regularities on local open restrictions. -/
theorem local_regular_values {m n k l : ℕ} {a b c d : ModelKind}
    {M N Q : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (he : IsSmoothEmbedding R T Subtype.val) (hf : IsSmoothMap S T f)
    (hB : IsNaturalBoundaryStructure S B)
    (ht : IsTransverse S T R f) (hbt : IsTransverse B T R (fun q => f q.val))
    (U : Set N) (A : SmoothManifold n b U) (hA : IsSmoothEmbedding A T Subtype.val)
    (D : SmoothManifold m a (f ⁻¹' U)) (hD : IsSmoothEmbedding D S Subtype.val)
    (C : SmoothManifold k c {x : U | x.val ∈ s})
    (hCA : IsSmoothEmbedding C A Subtype.val)
    (hCR : IsSmoothEmbedding C R (fun x => (⟨x.val.val, x.property⟩ : s)))
    (BD : SmoothManifold (m - 1) .euclidean (intrinsicBoundary D))
    (hBD : IsNaturalBoundaryStructure D BD)
    (hb : ∀ q : intrinsicBoundary D, q.val.val ∈ intrinsicBoundary S)
    (hj : IsSmoothMap BD B (fun q => (⟨q.val.val, hb q⟩ : intrinsicBoundary S)))
    (hji : IsImmersion BD B (fun q => (⟨q.val.val, hb q⟩ : intrinsicBoundary S)))
    (E : SmoothManifold l d Q) (g : U → Q)
    (hg : IsSmoothMap A E g) (y : Q)
    (hzero : ∀ x : U, g x = y ↔ x.val ∈ s) (hsub : IsSubmersion A E g) :
    IsRegularValue D E (fun x => g ⟨f x.val, x.property⟩) y ∧
    IsRegularValue BD E (fun q => g ⟨f q.val.val, q.val.property⟩) y := by
  let F : (f ⁻¹' U) → U := fun x => ⟨f x.val, x.property⟩
  have hF : IsSmoothMap D A F := smooth_restriction S T f hf U A hA D hD
  have htransD : IsTransverse D T R (f ∘ Subtype.val) :=
    transverse_precomp_of_immersion S D T R Subtype.val f hD.1 hD.2.2.1 hf ht
  have htransA : IsTransverse D A C F :=
    transverse_lift_of_immersions D T A R C Subtype.val (fun q => q.property) F
      hA.1 hA.2.2.1 hCR.1 hCR.2.2.1 he.1 hCA.1 hF htransD
  have hbf : IsSmoothMap B T (fun q => f q.val) :=
    manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1 Subtype.val f hB.1 hf
  have htransBD : IsTransverse BD T R (fun q => f q.val.val) :=
    transverse_precomp_of_immersion B BD T R
      (fun q => (⟨q.val.val, hb q⟩ : intrinsicBoundary S))
      (fun q => f q.val) hj hji hbf hbt
  have hFB : IsSmoothMap BD A (fun q => F q.val) :=
    manifoldContDiff_comp ⊤ _ _ _ D.smoothStructure.property.1.1 Subtype.val F hBD.1 hF
  have htransBDA : IsTransverse BD A C (fun q => F q.val) :=
    transverse_lift_of_immersions BD T A R C Subtype.val (fun q => q.property)
      (fun q => F q.val) hA.1 hA.2.2.1 hCR.1 hCR.2.2.1 he.1 hCA.1 hFB htransBD
  exact regular_values_of_transverse_defining_submersion D A
    {x : U | x.val ∈ s} C E F g BD hCA hF hg hBD y hzero hsub htransA htransBDA

/-- Postcomposition with a smooth diffeomorphism preserves submersion at a
point. Its chart-level proof supports source and targets in different universes. -/
theorem submersionAt_postcomp_diffeomorph {d l n : ℕ} {a b c : ModelKind}
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold d a X) (B : SmoothManifold l b Y) (C : SmoothManifold n c Z)
    (h : Diffeomorph B.smoothStructure.val C.smoothStructure.val)
    (g : X → Y) (hg : IsSmoothMap A B g)
    (p : X) (hsub : IsSubmersionAt A B g p) :
    IsSubmersionAt A C (h.toEquiv ∘ g) p := by
  have hs : IsSmoothMap A C (h.toEquiv ∘ g) := manifoldContDiff_comp ⊤ _ _ _
    B.smoothStructure.property.1.1 g h.toEquiv hg h.contDiff_toFun
  obtain ⟨e, he, hpe⟩ := A.smoothStructure.property.1.1 p
  obtain ⟨f, hf, hpf⟩ := B.smoothStructure.property.1.1 (g p)
  obtain ⟨k, hk, hpk⟩ := C.smoothStructure.property.1.1 (h.toEquiv (g p))
  have hfwd := (h.contDiff_toFun (g p)).2 f hf k hk hpf hpk
  have hinv := (h.contDiff_invFun (h.toEquiv (g p))).2 k hk f hf hpk
    (by simpa only [Equiv.symm_apply_apply] using hpf)
  have hcomp := FiniteRegularity.chartDerivative_comp ⊤ (by simp) k f k
    h.toEquiv.symm h.toEquiv (h.toEquiv (g p)) hpk (h.contDiff_invFun _).1 hinv
    (by simpa only [Equiv.symm_apply_apply] using hfwd)
  have hid : h.toEquiv ∘ h.toEquiv.symm = id := by
    funext x
    exact h.toEquiv.apply_symm_apply x
  rw [hid, FiniteRegularity.chartDerivative_id k _ hpk] at hcomp
  simp only [Equiv.symm_apply_apply] at hcomp
  have hsurjh : Function.Surjective (FiniteRegularityData.chartDerivative f k h.toEquiv (g p)) := by
    intro z
    refine ⟨FiniteRegularityData.chartDerivative k f h.toEquiv.symm (h.toEquiv (g p)) z, ?_⟩
    exact (congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L z) hcomp).symm
  have hG := MapClasses.chart_invariants A B g
    (manifoldContDiff_of_le ⊤ 1 _ _ g (by simp) hg) p e f he hf hpe hpf
  have hJ := FiniteRegularity.chartDerivative_comp ⊤ (by simp) e f k
    g h.toEquiv p hpe (hg p).1 ((hg p).2 e he f hf hpe hpf) hfwd
  have hResult := MapClasses.chart_invariants A C (h.toEquiv ∘ g)
    (manifoldContDiff_of_le ⊤ 1 _ _ _ (by simp) hs) p e k he hk hpe hpk
  apply hResult.2.2.mpr
  rw [hJ]
  exact hsurjh.comp (hG.2.2.mp hsub)

/-- Regular values transport to diffeomorphic targets, including across
universes; no global submersion assumption is required. -/
theorem regularValue_postcomp_diffeomorph {d l n : ℕ} {a b c : ModelKind}
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold d a X) (B : SmoothManifold l b Y) (C : SmoothManifold n c Z)
    (h : Diffeomorph B.smoothStructure.val C.smoothStructure.val)
    (g : X → Y) (hg : IsSmoothMap A B g)
    (y : Y) (hreg : IsRegularValue A B g y) :
    IsRegularValue A C (h.toEquiv ∘ g) (h.toEquiv y) := by
  intro p hp
  apply submersionAt_postcomp_diffeomorph A B C h g hg p
  apply hreg
  exact h.toEquiv.injective hp

/-- The exact restricted atlas returned by the defining-submersion theorem
has an embedded ambient inclusion and inherits the ambient boundary. -/
theorem open_subset_embedded_of_atlas_eq {m : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m a M)
    (s : Set M) (hs : IsOpen s) (A : SmoothManifold m a s)
    (hA : A.smoothStructure.val = maximalExtension ⊤
      (openSubsetAtlas S.smoothStructure.val s hs)) :
    IsSmoothEmbedding A S Subtype.val ∧
      intrinsicBoundary A = Subtype.val ⁻¹' intrinsicBoundary S := by
  obtain ⟨R, _, hR, hfR⟩ := exists_openSubset_smoothManifold S s hs
  have hf : IsSmoothMap A S Subtype.val := by
    change ManifoldContDiff ⊤ A.smoothStructure.val S.smoothStructure.val Subtype.val
    rw [hA, ← hR]
    exact hfR
  have hC := openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 s hs
  have hcharts (p : s) (c : ModelChart m a M) (hc : c ∈ S.smoothStructure.val) :
      c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩ ∈ A.smoothStructure.val := by
    rw [hA]
    exact subset_maximalExtension hC ⟨⟨p⟩, c, hc, rfl⟩
  refine ⟨⟨hf, Subtype.val_injective, ?_,
    ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩⟩, ?_⟩
  · intro p
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
    let d := c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩
    exact SliceStructures.immersion_of_coordinate_retraction A S Subtype.val hf p d c
      (hcharts p c hc) hc (by simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hpc)
      hpc (LocalCoordinateExtension.self ⊤ (fun x : s => (c x.val).val) p)
  · ext p
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
    let d := c.subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩
    have hpd : p ∈ d.source := by
      simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hpc
    rw [intrinsicBoundary_iff_chart A d (hcharts p c hc) p hpd]
    exact (intrinsicBoundary_iff_chart S c hc p.val hpc).symm
/-- Local boundary regular fibers give an embedded preimage piece at every point. -/
theorem exists_local_transverse_piece
    (hnatural : Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.natural_boundary_existsType.{u})
    (hregular : Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.regular_fiber_structureType.{u,v})
    {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (hT : intrinsicBoundary T = ∅) (hR : intrinsicBoundary R = ∅)
    (he : IsSmoothEmbedding R T Subtype.val) (hf : IsSmoothMap S T f)
    (hB : IsNaturalBoundaryStructure S B)
    (ht : IsTransverse S T R f) (hbt : IsTransverse B T R (fun q => f q.val))
    (p : f ⁻¹' s) :
    ∃ P : EmbeddedPiece S (f ⁻¹' s) (m - (n - k)) a, p ∈ P.domain := by
  obtain ⟨_, U, hU, hpU, A, hAeq, E, _hE, g, hg, hsub, hzero⟩ :=
    RegularLevels.local_defining_submersion T R Subtype.val hT hR he ⟨f p.val, p.property⟩
  have hzero' : ∀ x : U, g x = 0 ↔ x.val ∈ s := by
    intro x
    rw [← hzero x]
    simp only [Set.mem_range, Subtype.exists, exists_prop, exists_eq_right]
  obtain ⟨hA, _⟩ := open_subset_embedded_of_atlas_eq T U hU A hAeq
  let V : Set M := f ⁻¹' U
  have hV : IsOpen V := hU.preimage (RegularLevels.smoothMap_continuous S T f hf)
  obtain ⟨D, hD, hDb⟩ := open_subset_embedded S V hV
  obtain ⟨C, hCA, hCR⟩ := local_target_restriction T s U R he hU A hA
  obtain ⟨BD, hBD⟩ := hnatural D
  have hb : ∀ q : intrinsicBoundary D, q.val.val ∈ intrinsicBoundary S := by
    intro q
    exact (Set.ext_iff.mp hDb q.val).mp q.property
  obtain ⟨hj, hji⟩ := natural_boundary_restriction_immersion S V D B BD hD hB hBD hb
  obtain ⟨Eu, du, _hdu⟩ := exists_manifold_diffeomorph E
    (Homeomorph.ulift : ULift.{u} (Euclidean (n - k)) ≃ₜ Euclidean (n - k)).symm
  let gu : U → ULift.{u} (Euclidean (n - k)) := du.toEquiv ∘ g
  let yu : ULift.{u} (Euclidean (n - k)) := du.toEquiv 0
  have hgu : IsSmoothMap A Eu gu :=
    manifoldContDiff_comp ⊤ _ _ _ E.smoothStructure.property.1.1 g du.toEquiv hg du.contDiff_toFun
  have hsubu : IsSubmersion A Eu gu :=
    fun x => submersionAt_postcomp_diffeomorph A E Eu du g hg x (hsub x)
  have hzerou : ∀ x : U, gu x = yu ↔ x.val ∈ s := by
    intro x
    exact (du.toEquiv.injective.eq_iff).trans (hzero' x)
  obtain ⟨hreg, hregb⟩ := local_regular_values S T s R f B he hf hB ht hbt U A hA D hD
    C hCA hCR BD hBD hb hj hji Eu gu hgu yu hzerou hsubu
  let F : V → ULift.{u} (Euclidean (n - k)) := fun x => gu ⟨f x.val, x.property⟩
  have hF : IsSmoothMap D Eu F :=
    manifoldContDiff_comp ⊤ _ _ _ A.smoothStructure.property.1.1
      (fun x : V => (⟨f x.val, x.property⟩ : U)) gu
      (smooth_restriction S T f hf U A hA D hD) hgu
  obtain ⟨Ev, dv, _hdv⟩ := exists_manifold_diffeomorph Eu
    ((Homeomorph.ulift : ULift.{u} (Euclidean (n - k)) ≃ₜ Euclidean (n - k)).trans
      (Homeomorph.ulift : ULift.{v} (Euclidean (n - k)) ≃ₜ Euclidean (n - k)).symm)
  let Fv : V → ULift.{v} (Euclidean (n - k)) := dv.toEquiv ∘ F
  have hFv : IsSmoothMap D Ev Fv :=
    manifoldContDiff_comp ⊤ _ _ _ Eu.smoothStructure.property.1.1 F dv.toEquiv hF dv.contDiff_toFun
  have hregv : IsRegularValue D Ev Fv (dv.toEquiv yu) :=
    regularValue_postcomp_diffeomorph D Eu Ev dv F hF yu hreg
  have hFb : IsSmoothMap BD Eu (fun q => F q.val) :=
    manifoldContDiff_comp ⊤ _ _ _ D.smoothStructure.property.1.1 Subtype.val F hBD.1 hF
  have hregvb : IsRegularValue BD Ev (fun q => Fv q.val) (dv.toEquiv yu) :=
    regularValue_postcomp_diffeomorph BD Eu Ev dv (fun q => F q.val) hFb yu hregb
  obtain ⟨Z, hZ, hZb, _⟩ := hregular D Ev Fv BD hBD
    (intrinsicBoundary_euclidean Ev) hFv (dv.toEquiv yu) hregv hregvb
  have hz : ∀ x : V, Fv x = dv.toEquiv yu ↔ x.val ∈ f ⁻¹' s := by
    intro x
    exact (dv.toEquiv.injective.eq_iff).trans (hzerou ⟨f x.val, x.property⟩)
  obtain ⟨P, hP⟩ := exists_piece_of_local_fiber S (f ⁻¹' s) V hV D hD hDb
    Fv (dv.toEquiv yu) hz Z hZ hZb
  refine ⟨P, ?_⟩
  rw [hP]
  exact hpU

/-- Transverse inverse images inherit an embedded structure and exactly the
ambient intrinsic boundary. Empty inverse images and codimension zero are included. -/
theorem transverse_preimage_structure :
    Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_structureType.{u} := by
  intro m n k a b c M N _ _ S T s R f B hT hR he hf hB ht hbt
  have hcover := exists_local_transverse_piece.{u,u}
    BoundaryRegularLevels.natural_boundary_exists
    BoundaryRegularLevels.regular_fiber_structure
    S T s R f B hT hR he hf hB ht hbt
  obtain ⟨P, hP, hb⟩ := exists_embedded_of_local_pieces S (f ⁻¹' s) hcover
  refine ⟨P, hP, hb, ?_⟩
  intro hne
  have hd := (transverse_preimage_dimension_proof S T s R f B hT hR he hf hB ht hbt).1 hne
  omega

/-- The codimension bound is conditional on nonemptiness, and is stronger
at points of the intrinsic boundary. -/
theorem transverse_preimage_dimension :
    Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_dimensionType.{u} :=
  transverse_preimage_dimension_proof

/-- The inclusion differential identifies the full tangent space with the
inverse image of the target submanifold tangent space, also at boundary points. -/
theorem transverse_preimage_tangent :
    Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u} :=
  transverse_preimage_tangent_proof

end SmoothManifolds.TransversePreimage
