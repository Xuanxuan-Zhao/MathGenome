import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.TubularLocalGeometry
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.MetricSplittings
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.ProperWhitney
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.EuclideanTubular
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.EmbeddedComparison
import Batteries.Tactic.OpenPrivate

/-! The local geometric part of M05.08, using the actual quotient normal
bundle, a constructed smooth splitting, and an ambient tubular retraction. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace SmoothManifolds.TubularLocalGeometry
open ModelData AtlasData MapData BundleData BundleOperationsData TangentData
  QuotientData ConstantRankData Bundle Set Filter
open scoped Topology
universe u v w

/-- A smooth quotient by the image of an injective bundle morphism has
an actual smooth right inverse. Keeping the fiber modules abstract also avoids
unfolding the internal representation of derivation tangent spaces. -/
theorem quotient_rightInverse
    {d l r : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    {T : SmoothManifold d a X} {ι κ : Type u} {V E : X → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean l) V)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (A : SmoothVectorBundle T l ι V) (B : SmoothVectorBundle T r κ E)
    (D : SmoothBundleMorphism A B) (hD : ∀ p, Function.Injective (D.linearMap p))
    (Q : SmoothQuotient.{u,u,u,u,u} B (fun p => (D.linearMap p).range) l) :
    letI := Q.topology
    ∃ t : SmoothBundleMorphism Q.bundle B,
      ∀ p v, QuotientData.quotientProjection (fun p => (D.linearMap p).range) p (t.linearMap p v) = v := by
  letI := Q.topology
  let K : (p : X) → Submodule ℝ (E p) := fun p => (D.linearMap p).range
  let q : SmoothBundleMorphism B Q.bundle :=
    ⟨QuotientData.quotientProjection (E := E) K, Q.projection_smooth⟩
  obtain ⟨t, ht, _⟩ := MetricSplittings.shortExact_splitting A B Q.bundle D q hD
    (fun p => (K p).mkQ_surjective) (fun p => (Submodule.ker_mkQ (K p)).symm)
  exact ⟨t, fun p v => LinearMap.congr_fun (ht p) v⟩

/-- Smooth right inverse on the actual normal quotient. In particular no
chosen metric or assumed lift is needed. -/
theorem normal_lift_exists
    {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
    {i : P → M} (N : NormalBundle T S i) :
    letI := N.ambientRealization.space.topology
    letI := N.pullback.space.topology
    letI := N.quotient.topology
    ∃ t : SmoothBundleMorphism N.quotient.bundle N.pullback.space.bundle,
      ∀ p v, (LinearMap.range (N.differential p)).mkQ (t.linearMap p v) = v := by
  letI := N.ambientRealization.space.topology
  letI := N.sourceRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  let d : SmoothBundleMorphism N.sourceRealization.space.bundle N.pullback.space.bundle :=
    ⟨N.differential, N.differential_smooth⟩
  exact quotient_rightInverse N.sourceRealization.space.bundle
    N.pullback.space.bundle d N.injective N.quotient

/-- A family of quotient right inverses supplies the complementary linear
summands, including fibers of dimension zero. -/
theorem quotient_sum_bijective {X : Type u} {V E : X → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (d : (p : X) → V p →ₗ[ℝ] E p) (hd : ∀ p, Function.Injective (d p))
    (t : (p : X) → QuotientFiber (E := E) (fun p => (d p).range) p →ₗ[ℝ] E p)
    (ht : ∀ p v, QuotientData.quotientProjection (E := E) (fun p => (d p).range) p (t p v) = v) :
    ∀ p, Function.Bijective ((d p).coprod (t p)) := by
  intro p
  apply MetricSplittings.split_coprod_bijective (d p) (d p).range.mkQ (t p)
    (hd p) (Submodule.ker_mkQ _).symm
  apply LinearMap.ext
  exact ht p

/-- Smooth maps on an open subtype can be totalized using any available
fallback, without requiring an inhabited target. This applies to `i ∘ proj`
when constructing the tubular map. -/
theorem totalize_smooth_on
    {d e : ℕ} {a b : ModelKind} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set (ModelChart d a X)) (B : Set (ModelChart e b Y))
    (U : Set X) (hU : IsOpen U) (g : U → Y) (fallback : X → Y)
    (hg : ManifoldSmooth (openSubsetAtlas A U hU) B g) :
    ∃ F : X → Y, (∀ x : U, F x.val = g x) ∧ ManifoldSmoothOn A B F U := by
  classical
  let F : X → Y := fun x => if h : x ∈ U then g ⟨x, h⟩ else fallback x
  have hF : ∀ x : U, F x.val = g x := by
    intro x
    simp only [F, dite_eq_left x.property]
  refine ⟨F, hF, ?_⟩
  apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) A B F U hU).mpr
  have heq : (fun x : U => F x.val) = g := funext hF
  rw [heq]
  exact hg

/-- A map between open subsets is smooth with their restricted atlases if
its underlying map is smooth on the source. Both subtypes use their actual
subspace topologies. -/
theorem smooth_open_subtype_map
    {d e : ℕ} {a b : ModelKind} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set (ModelChart d a X)) (B : Set (ModelChart e b Y))
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (f : X → Y) (hUV : MapsTo f U V) (hf : ManifoldSmoothOn A B f U) :
    ManifoldSmooth (openSubsetAtlas A U hU) (openSubsetAtlas B V hV)
      (fun x : U => (⟨f x.val, hUV x.property⟩ : V)) := by
  intro x
  refine ⟨tendsto_subtype_rng.mpr ((hf x.val x.property).1.comp continuousAt_subtype_val), ?_⟩
  rintro _ ⟨hne, c, hc, rfl⟩ _ ⟨hne', d, hd, rfl⟩ hxc hfxd
  apply LocalCoordinateExtension.precomp (h := (Subtype.val : U → X))
    ((hf x.val x.property).2 c hc d hd
      (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hxc)
      (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hfxd))
    continuousAt_subtype_val rfl

/-- Taking the union of local inverse sources gives an open domain on which
every point, and not only each point of the zero section, has a local inverse.
All hypotheses here are proof-internal; existence of those inverses at zero
remains the analytic step of the main theorem. -/
theorem local_inverse_locus
    {d e : ℕ} {a b : ModelKind} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set (ModelChart d a X)) (B : Set (ModelChart e b Y))
    (f : X → Y) (U Z : Set X)
    (hf : ManifoldSmoothOn A B f U)
    (hloc : ∀ x ∈ Z, ∃ h : OpenPartialHomeomorph X Y,
      x ∈ h.source ∧ h.source ⊆ U ∧ EqOn h f h.source ∧
      ManifoldSmoothOn B A h.symm h.target) :
    ∃ O : Set X, IsOpen O ∧ Z ⊆ O ∧ O ⊆ U ∧ ManifoldSmoothOn A B f O ∧
      ∀ x ∈ O, ∃ h : OpenPartialHomeomorph X Y,
        x ∈ h.source ∧ h.source ⊆ O ∧ EqOn h f h.source ∧
        ManifoldSmoothOn B A h.symm h.target := by
  let O : Set X := {x | ∃ h : OpenPartialHomeomorph X Y,
    x ∈ h.source ∧ h.source ⊆ U ∧ EqOn h f h.source ∧
    ManifoldSmoothOn B A h.symm h.target}
  have hO : IsOpen O := isOpen_iff_mem_nhds.mpr (by
    rintro x ⟨h, hx, hU, heq, hi⟩
    exact mem_of_superset (h.open_source.mem_nhds hx)
      (fun y hy => ⟨h, hy, hU, heq, hi⟩))
  have hOU : O ⊆ U := by
    rintro x ⟨h, hx, hU, _, _⟩
    exact hU hx
  refine ⟨O, hO, hloc, hOU, (fun x hx => hf x (hOU hx)), ?_⟩
  rintro x ⟨h, hx, hU, heq, hi⟩
  exact ⟨h, hx, (fun y hy => ⟨h, hy, hU, heq, hi⟩), heq, hi⟩

open private transportManifold from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.QuotientBundles

/-- Smoothness in Euclidean-valued coordinates agrees with smoothness into
any standard Euclidean manifold structure containing its identity chart. -/
theorem smoothEuclidean_to_smoothMap
    {n q : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n a X) (f : X → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : EmbeddedData.euclideanChart q ∈ T.smoothStructure.val)
    (hf : GoodProjectionData.IsSmoothEuclidean S f) : IsSmoothMap S T f := by
  intro p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 T.smoothStructure.property.1 f p).mpr
  exact ⟨(hf p).1, e, he, EmbeddedData.euclideanChart q, hT, hp,
    mem_univ _, (hf p).2 e he hp⟩

/-- Transport of a Euclidean immersion across a homeomorphism uses the
transported atlas, so its coordinate derivatives remain the same. -/
theorem euclideanImmersion_transport
    {n q : ℕ} {a : ModelKind} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n a X) (h : X ≃ₜ Y) (f : X → Euclidean q)
    (hf : GoodProjectionData.IsEuclideanImmersion S f) :
    GoodProjectionData.IsEuclideanImmersion (transportManifold S h)
      (fun y => f (h.symm y)) := by
  constructor
  · intro y
    refine ⟨(hf.1 (h.symm y)).1.comp h.symm.continuous.continuousAt, ?_⟩
    rintro _ ⟨e, he, rfl⟩ hye
    exact LocalCoordinateExtension.precomp
      ((hf.1 (h.symm y)).2 e he ((mem_transportedChart_source h e y).mp hye))
      h.symm.continuous.continuousAt rfl
  · rintro _ ⟨e, he, rfl⟩ y hye
    have hp := (mem_transportedChart_source h e y).mp hye
    obtain ⟨U, hU, hpU, F, hF, heq⟩ := (hf.1 (h.symm y)).2 e he hp
    have hD := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
    have hd₁ := FiniteRegularity.coordinateDerivative_eq e f (h.symm y) hp _
      ⟨F, hD, heq⟩
    have hd₂ := FiniteRegularity.coordinateDerivative_eq
      (h.symm.toOpenPartialHomeomorph.trans e) (fun y => f (h.symm y)) y hye _
      ⟨F, hD, heq.comp_tendsto h.symm.continuous.continuousAt⟩
    rw [hd₂, ← hd₁]
    exact hf.2 e he (h.symm y) hp

/-- Euclidean coordinate injectivity gives the project's full immersion
condition, using its actual coordinate-tangent differential. -/
theorem euclideanImmersion_isImmersion
    {n q : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n a X) (f : X → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : EmbeddedData.euclideanChart q ∈ T.smoothStructure.val)
    (hf : GoodProjectionData.IsEuclideanImmersion S f) :
    MapClassData.IsImmersion S T f := by
  have hs := smoothEuclidean_to_smoothMap S f T hT hf.1
  have hs₁ := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hs
  intro p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  exact (MapClasses.chart_invariants S T f hs₁ p e (EmbeddedData.euclideanChart q)
    he hT hp (mem_univ _)).2.1.mpr (hf.2 e he p hp)

/-- An arbitrary-universe boundaryless manifold embedded in Euclidean space
has a smooth tubular retraction. The Type-0 Euclidean tubular theorem is
applied only to the actual image subtype, then transported back. -/
theorem euclidean_retraction_of_embedding
    {n q : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X) (j : X → Euclidean q)
    (hj : GoodProjectionData.IsEuclideanImmersion S j)
    (h : X ≃ₜ range j) (hh : ∀ p, (h p).val = j p)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : EmbeddedData.euclideanChart q ∈ T.smoothStructure.val) :
    ∃ (W : Set (Euclidean q)) (hW : IsOpen W) (r : W → X),
      range j ⊆ W ∧
      ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
        S.smoothStructure.val r ∧
      ∀ p (hp : j p ∈ W), r ⟨j p, hp⟩ = p := by
  let R := transportManifold S h
  have hval : (fun y : range j => j (h.symm y)) = Subtype.val := by
    funext y
    rw [← hh, h.apply_symm_apply]
  have him := euclideanImmersion_transport S h j hj
  rw [hval] at him
  have hinc : MapClassData.IsSmoothEmbedding R T (Subtype.val : range j → Euclidean q) := by
    exact ⟨smoothEuclidean_to_smoothMap R _ T hT him.1, Subtype.val_injective,
      euclideanImmersion_isImmersion R _ T hT him,
      Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩
  obtain ⟨N, _, V, W, hV, hW, e, he⟩ := EuclideanTubular.euclidean_tubular R T hT
    (Subtype.val : range j → Euclidean q) hinc
  obtain ⟨r₀, _, hr₀, _, hrzero, _⟩ := he.2.2.2.2.2.2
  have hmaps := (transportAtlas_maps (⊤ : ℕ∞) S.smoothStructure.val h
    S.smoothStructure.property.1).2
  refine ⟨W, hW, fun y => h.symm (r₀ y), ?_, ?_, ?_⟩
  · intro y hy
    exact he.2.2.2.1 ⟨⟨y, hy⟩, rfl⟩
  · exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ R.smoothStructure.property.1.1
      r₀ h.symm hr₀ hmaps
  · intro p hp
    have hrp := hrzero (h p) (by simpa only [hh] using hp)
    change h.symm (r₀ ⟨j p, hp⟩) = p
    have heqp : (⟨j p, hp⟩ : W) = ⟨(h p).val, by simpa only [hh] using hp⟩ :=
      Subtype.ext (hh p).symm
    rw [heqp, hrp, h.symm_apply_apply]

/-- Proper Whitney and the retraction bridge supply the ambient data used
in the abstract tubular construction, in every universe and dimension. -/
theorem exists_euclidean_retraction
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X) :
    ∃ (j : X → Euclidean (2 * n + 1))
      (T : SmoothManifold (2 * n + 1) .euclidean (Euclidean (2 * n + 1)))
      (W : Set (Euclidean (2 * n + 1))) (hW : IsOpen W) (r : W → X),
      GoodProjectionData.IsEuclideanImmersion S j ∧
      EmbeddedData.euclideanChart (2 * n + 1) ∈ T.smoothStructure.val ∧
      range j ⊆ W ∧
      ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
        S.smoothStructure.val r ∧
      ∀ p (hp : j p ∈ W), r ⟨j p, hp⟩ = p := by
  obtain ⟨j, hj, _, _, h, hh⟩ := ProperWhitney.exists_proper_embedding S
  obtain ⟨T, hT⟩ := standardEuclidean_exists (2 * n + 1)
  obtain ⟨W, hW, r, hjW, hr, hz⟩ := euclidean_retraction_of_embedding S j hj h hh T hT
  exact ⟨j, T, W, hW, r, hj, hT, hjW, hr, hz⟩

/-- The inverse function theorem applies to a map smooth only on an open
set. Its local inverse is returned on the original total types, and its source
stays in the supplied open set. -/
theorem local_inverse_on_open_of_bijective_chartDerivative
    {m n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold m .euclidean X) (T : SmoothManifold n .euclidean Y)
    (f : X → Y) (U : Set X) (hU : IsOpen U)
    (hf : ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val f U)
    (p : X) (hpU : p ∈ U)
    (c : ModelChart m .euclidean X) (d : ModelChart n .euclidean Y)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ c.source) (hfp : f p ∈ d.source)
    (hbij : Function.Bijective (FiniteRegularityData.chartDerivative c d f p)) :
    ∃ e : OpenPartialHomeomorph X Y,
      p ∈ e.source ∧ e.source ⊆ U ∧ EqOn e f e.source ∧
      ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val e.symm e.target := by
  let pU : U := ⟨p, hpU⟩
  let inc := (⟨U, hU⟩ : TopologicalSpace.Opens X).openPartialHomeomorphSubtypeCoe ⟨pU⟩
  let cU := c.subtypeRestr (s := ⟨U, hU⟩) ⟨pU⟩
  obtain ⟨R, _, hR, hi⟩ := exists_openSubset_smoothManifold S U hU
  have hA := openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 U hU
  have hcU : cU ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension hA ⟨⟨pU⟩, c, hc, rfl⟩
  have hpU' : pU ∈ cU.source := by
    simpa only [cU, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hp
  have hrestrict : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      T.smoothStructure.val (fun x : U => f x.val) :=
    (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f U hU).mp hf
  have hfr : IsSmoothMap R T (fun x : U => f x.val) := by
    intro x
    obtain ⟨a, ha, hxa⟩ := hA.1 x
    obtain ⟨b, hb, hfxb⟩ := T.smoothStructure.property.1.1 (f x.val)
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      R.smoothStructure.property.1 T.smoothStructure.property.1 _ x).mpr
    refine ⟨(hrestrict x).1, a, ?_, b, hb, hxa, hfxb,
      (hrestrict x).2 a ha b hb hxa hfxb⟩
    rw [hR]
    exact subset_maximalExtension hA ha
  have hder : FiniteRegularityData.chartDerivative cU d (fun x : U => f x.val) pU =
      FiniteRegularityData.chartDerivative c d f p := by
    obtain ⟨F, hF, heq⟩ := FiniteRegularity.chartDerivative_exists (⊤ : ℕ∞) (by simp)
      c d f p ((hf p hpU).2 c hc d hd hp hfp)
    exact FiniteRegularity.coordinateDerivative_eq cU _ pU hpU' _
      ⟨F, hF, heq.comp_tendsto continuousAt_subtype_val⟩
  obtain ⟨j, hpj, heq, hjinv⟩ := EuclideanTubular.local_inverse_of_bijective_chartDerivative
    R T (fun x : U => f x.val) hfr pU cU d hcU hd hpU' hfp (hder ▸ hbij)
  let e := inc.symm.trans j
  have hincp : inc.symm p = pU := inc.left_inv (mem_univ pU)
  have hincU : inc.target = U := by
    simp only [inc, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    rfl
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change p ∈ inc.target ∧ inc.symm p ∈ j.source
    exact ⟨by rwa [hincU], by rwa [hincp]⟩
  · intro x hx
    exact hincU ▸ hx.1
  · intro x hx
    change j (inc.symm x) = f x
    exact (heq (x := inc.symm x) hx.2).trans (congrArg f (inc.right_inv hx.1))
  · intro y hy
    have hcomp := manifoldContDiffAt_comp R.smoothStructure.property.1.1
      (hjinv y hy.1) (hi (j.symm y))
    exact hcomp

/-- Once a candidate tubular map has invertible actual chart derivatives
along its zero section, the inverse-function and open-locus steps give the
entire local tubular conclusion. This is a reduction lemma, not an assumption
in the main theorem. -/
theorem localTubularMap_of_bijective_derivatives
    {m n r : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} (S : SmoothManifold n .euclidean M)
    (i : P → M) {ι : Type u} {V : P → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) V)]
    (B : SmoothVectorBundle T r ι V)
    (U : Set (Bundle.TotalSpace (Euclidean r) V)) (hU : IsOpen U)
    (F : Bundle.TotalSpace (Euclidean r) V → M)
    (hzero : ∀ p, (⟨p, 0⟩ : Bundle.TotalSpace (Euclidean r) V) ∈ U)
    (hFzero : ∀ p, F ⟨p, 0⟩ = i p)
    (hF : ManifoldSmoothOn B.totalManifold.smoothStructure.val S.smoothStructure.val F U)
    (hderiv : ∀ p, ∃ (c : ModelChart (m + r)
        (ProductData.productKind m .euclidean r .euclidean)
        (Bundle.TotalSpace (Euclidean r) V)) (d : ModelChart n .euclidean M),
      c ∈ B.totalManifold.smoothStructure.val ∧ d ∈ S.smoothStructure.val ∧
      (⟨p, 0⟩ : Bundle.TotalSpace (Euclidean r) V) ∈ c.source ∧ F ⟨p, 0⟩ ∈ d.source ∧
      Function.Bijective (FiniteRegularityData.chartDerivative c d F ⟨p, 0⟩)) :
    Specs.SmoothManifolds.Ch05.TubularLocalGeometry.LocalTubularMap S i B := by
  let Z : Set (Bundle.TotalSpace (Euclidean r) V) := range (fun p => ⟨p, 0⟩)
  have hloc : ∀ x ∈ Z, ∃ e : OpenPartialHomeomorph (Bundle.TotalSpace (Euclidean r) V) M,
      x ∈ e.source ∧ e.source ⊆ U ∧ EqOn e F e.source ∧
      ManifoldSmoothOn S.smoothStructure.val B.totalManifold.smoothStructure.val
        e.symm e.target := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨c, d, hc, hd, hp, hfp, hbij⟩ := hderiv p
    exact local_inverse_on_open_of_bijective_chartDerivative B.totalManifold S F U hU hF
      ⟨p, 0⟩ (hzero p) c d hc hd hp hfp hbij
  obtain ⟨O, hO, hZO, _, hFO, hinv⟩ := local_inverse_locus
    B.totalManifold.smoothStructure.val S.smoothStructure.val F U Z hF hloc
  exact ⟨O, F, hO, fun p => hZO ⟨p, rfl⟩, hFzero, hFO, hinv⟩

/-- A smooth Euclidean-valued map has a smooth fiberwise linear differential
on any of the canonical tangent realizations, also when the source is in a
larger universe. The formula uses the actual source tangent coordinates. -/
theorem exists_smooth_euclidean_differential
    {n q : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n a X) (BS : TangentBundleData.TangentBundleStructure S)
    (f : X → Euclidean q) (hf : GoodProjectionData.IsSmoothEuclidean S f) :
    letI := BS.topology
    ∃ D : (p : X) → TangentSpace S p →ₗ[ℝ] Euclidean q,
      GoodProjectionData.IsSmoothEuclidean BS.manifold (fun z => D z.1 z.2) ∧
      ∀ (p : X) (e : ModelChart n a X) (he : e ∈ S.smoothStructure.val)
        (hp : p ∈ e.source) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n),
        DifferentialData.IsChartCoordinates S p e E → ∀ v,
        D p v = FiniteRegularityData.coordinateDerivative e f p (E v) := by
  letI := BS.topology
  obtain ⟨T, hT⟩ := standardEuclidean_exists q
  let h : Euclidean q ≃ₜ ULift.{u} (Euclidean q) := Homeomorph.ulift.symm
  let R := transportManifold T h
  let fU : X → ULift.{u} (Euclidean q) := fun p => h (f p)
  let dU : ModelChart q .euclidean (ULift.{u} (Euclidean q)) :=
    h.symm.toOpenPartialHomeomorph.trans (EmbeddedData.euclideanChart q)
  have hdU : dU ∈ R.smoothStructure.val := ⟨EmbeddedData.euclideanChart q, hT, rfl⟩
  have hdp : ∀ p, fU p ∈ dU.source := fun _ => ⟨mem_univ _, mem_univ _⟩
  have hfu : IsSmoothMap S R fU := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    T.smoothStructure.property.1.1 f h (smoothEuclidean_to_smoothMap S f T hT hf)
    (transportAtlas_maps (⊤ : ℕ∞) T.smoothStructure.val h T.smoothStructure.property.1).1
  have hex := fun p => (differential_exists S R fU hfu p).exists
  choose L hL using hex
  obtain ⟨BT⟩ := TangentBundle.exists_bundle R
  letI := BT.topology
  let D : (p : X) → TangentSpace S p →ₗ[ℝ] Euclidean q := fun p =>
    (BT.fiberCoordinates.equiv dU hdU (fU p) (hdp p)).toLinearMap.comp (L p)
  have hm := TangentBundle.map_smooth S R BS BT fU hfu L hL
  have hcoeff : (fun z : TangentBundleData.TotalSpace S => D z.1 z.2) =
      (fun z => TangentBundle.chartFiber BT dU hdU
        (TangentBundleData.totalMap S R fU L z)) := by
    funext z
    exact (TangentBundle.chartFiber_eq R BT dU hdU
      (TangentBundleData.totalMap S R fU L z) (hdp z.1)).symm
  refine ⟨D, ?_, ?_⟩
  · rw [hcoeff]
    intro z
    exact TangentBundle.chartFiber_smoothAt R BT BS.manifold
      (TangentBundleData.totalMap S R fU L) z dU hdU (hdp z.1) (hm z)
  · intro p e he hp E hE v
    have hJ := FiniteRegularity.smooth_jacobian_coordinateDerivative S R fU hfu p
      (L p) (hL p) e dU he hdU hp (hdp p) E
      (BT.fiberCoordinates.equiv dU hdU (fU p) (hdp p)) hE
      (BT.fiberCoordinates.isCoordinates dU hdU (fU p) (hdp p)) v
    exact hJ

/-- Smooth Euclidean-valued maps can be pulled back by smooth maps between
manifolds of independently chosen universes. -/
theorem smoothEuclidean_comp
    {k n q : ℕ} {a b : ModelKind} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (R : SmoothManifold k a X) (S : SmoothManifold n b Y)
    (f : X → Y) (g : Y → Euclidean q)
    (hf : IsSmoothMap R S f) (hg : GoodProjectionData.IsSmoothEuclidean S g) :
    GoodProjectionData.IsSmoothEuclidean R (fun x => g (f x)) := by
  intro x
  refine ⟨(hg (f x)).1.comp (hf x).1, ?_⟩
  intro e he hxe
  obtain ⟨d, hd, hfd⟩ := S.smoothStructure.property.1.1 (f x)
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp ((hg (f x)).2 d hd hfd) (hf x).1 rfl)
    ((hf x).2 e he d hd hxe hfd)

/-- Addition preserves smooth Euclidean-valued maps with the manuscript's
local-extension convention. -/
theorem smoothEuclidean_add
    {n q : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n a X) (f g : X → Euclidean q)
    (hf : GoodProjectionData.IsSmoothEuclidean S f)
    (hg : GoodProjectionData.IsSmoothEuclidean S g) :
    GoodProjectionData.IsSmoothEuclidean S (fun x => f x + g x) := by
  intro x
  refine ⟨(hf x).1.add (hg x).1, ?_⟩
  intro e he hxe
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := (hf x).2 e he hxe
  obtain ⟨V, hV, hxV, G, hG, heG⟩ := (hg x).2 e he hxe
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun z => F z + G z,
    (hF.mono inter_subset_left).add (hG.mono inter_subset_right), ?_⟩
  filter_upwards [heF, heG] with y hyF hyG
  rw [hyF, hyG]

/-- The normal lift followed by the pullback and realization bridges is a
smooth map to the original intrinsic ambient tangent total space. -/
theorem normal_lift_to_tangent_smooth
    {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
    {i : P → M} (N : NormalBundle T S i) :
    letI := N.ambientRealization.space.topology
    letI := N.pullback.space.topology
    letI := N.quotient.topology
    ∀ t : SmoothBundleMorphism N.quotient.bundle N.pullback.space.bundle,
    letI := N.ambientTangent.topology
    IsSmoothMap N.quotient.bundle.totalManifold N.ambientTangent.manifold
      (fun z => (⟨i z.proj, t.linearMap z.proj z.snd⟩ : TangentBundleData.TotalSpace S)) := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  intro t
  letI := N.ambientTangent.topology
  have ht := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    N.pullback.space.bundle.totalManifold.smoothStructure.property.1.1
    _ _ t.smooth N.pullback.canonical_smooth
  exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    N.ambientRealization.space.bundle.totalManifold.smoothStructure.property.1.1
    _ _ ht N.ambientRealization.smooth_to_original

/-- The ambient addition formula is smooth on the actual quotient total
space. Both the quotient lift and its passage to the intrinsic tangent bundle
use the prescribed bundle structures. -/
theorem normal_addition_smooth
    {m n q : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
    {i : P → M} (N : NormalBundle T S i) (hi : IsSmoothMap T S i)
    (j : M → Euclidean q) (hj : GoodProjectionData.IsSmoothEuclidean S j)
    (D : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean q)
    (hD : letI := N.ambientTangent.topology
      GoodProjectionData.IsSmoothEuclidean N.ambientTangent.manifold
        (fun z => D z.1 z.2)) :
    letI := N.ambientRealization.space.topology
    letI := N.pullback.space.topology
    letI := N.quotient.topology
    ∀ t : SmoothBundleMorphism N.quotient.bundle N.pullback.space.bundle,
      GoodProjectionData.IsSmoothEuclidean N.quotient.bundle.totalManifold
        (fun z => j (i z.proj) + D (i z.proj) (t.linearMap z.proj z.snd)) := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  letI := N.ambientTangent.topology
  intro t
  have hib := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    T.smoothStructure.property.1.1 _ _ N.quotient.bundle.projection_smooth hi
  exact smoothEuclidean_add N.quotient.bundle.totalManifold _ _
    (smoothEuclidean_comp N.quotient.bundle.totalManifold S _ j hib hj)
    (smoothEuclidean_comp N.quotient.bundle.totalManifold N.ambientTangent.manifold
      _ (fun z => D z.1 z.2) (normal_lift_to_tangent_smooth N t) hD)

/-- Compose a smooth map with a smooth map on an open subset of its target,
and totalize the result using any fallback. The formula is retained everywhere
in the preimage, without assuming either space nonempty. -/
theorem smooth_open_composition_totalization
    {k n l : ℕ} {a b c : ModelKind} {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (A : SmoothManifold k a X) (B : SmoothManifold n b Y) (C : SmoothManifold l c Z)
    (f : X → Y) (hf : IsSmoothMap A B f)
    (W : Set Y) (hW : IsOpen W) (g : W → Z)
    (hg : ManifoldSmooth (openSubsetAtlas B.smoothStructure.val W hW)
      C.smoothStructure.val g) (fallback : X → Z) :
    ∃ F : X → Z,
      ManifoldSmoothOn A.smoothStructure.val C.smoothStructure.val F (f ⁻¹' W) ∧
      ∀ x (hx : f x ∈ W), F x = g ⟨f x, hx⟩ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).1
  have hU : IsOpen (f ⁻¹' W) := hW.preimage hc
  let g₀ : (f ⁻¹' W) → W := fun x => ⟨f x.val, x.property⟩
  have hg₀ : ManifoldSmooth (openSubsetAtlas A.smoothStructure.val (f ⁻¹' W) hU)
      (openSubsetAtlas B.smoothStructure.val W hW) g₀ :=
    smooth_open_subtype_map A.smoothStructure.val B.smoothStructure.val
      (f ⁻¹' W) W hU hW f (fun _ hx => hx) (fun x _ => hf x)
  have hgcomp := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ B.smoothStructure.property.1 W hW).1
    g₀ g hg₀ hg
  obtain ⟨F, heq, hF⟩ := totalize_smooth_on A.smoothStructure.val C.smoothStructure.val
    (f ⁻¹' W) hU (g ∘ g₀) fallback hgcomp
  exact ⟨F, hF, fun x hx => heq ⟨x, hx⟩⟩

/-- The smooth candidate with its actual retraction formula, before proving
local invertibility. Factoring this proposition keeps its bundle fibers abstract
during elaboration of the normal-quotient specialization. -/
def RetractionCandidate
    {m n q r : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} (S : SmoothManifold n .euclidean M)
    (i : P → M) {ι : Type u} {V : P → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) V)]
    (B : SmoothVectorBundle T r ι V)
    (A : Bundle.TotalSpace (Euclidean r) V → Euclidean q)
    (W : Set (Euclidean q)) (retract : W → M) : Prop :=
  ∃ F : Bundle.TotalSpace (Euclidean r) V → M,
    IsOpen (A ⁻¹' W) ∧ (∀ p, A ⟨p, 0⟩ ∈ W) ∧ (∀ p, F ⟨p, 0⟩ = i p) ∧
    ManifoldSmoothOn B.totalManifold.smoothStructure.val
      S.smoothStructure.val F (A ⁻¹' W) ∧
    ∀ z (hz : A z ∈ W), F z = retract ⟨A z, hz⟩

/-- The retraction formula gives a smooth total map on its precise open
preimage and has the correct values on the zero section. This lemma retains
the addition formula; local invertibility is a separate derivative obligation. -/
theorem normal_retraction_candidate
    {m n q : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
    {i : P → M} (N : NormalBundle T S i) (hi : IsSmoothMap T S i)
    (j : M → Euclidean q) (hj : GoodProjectionData.IsSmoothEuclidean S j)
    (D : (p : M) → TangentSpace S p →ₗ[ℝ] Euclidean q)
    (hD : letI := N.ambientTangent.topology
      GoodProjectionData.IsSmoothEuclidean N.ambientTangent.manifold
        (fun z => D z.1 z.2))
    (R : SmoothManifold q .euclidean (Euclidean q))
    (hR : EmbeddedData.euclideanChart q ∈ R.smoothStructure.val)
    (W : Set (Euclidean q)) (hW : IsOpen W) (r : W → M)
    (hjW : range j ⊆ W)
    (hr : ManifoldSmooth (openSubsetAtlas R.smoothStructure.val W hW)
      S.smoothStructure.val r)
    (hrzero : ∀ p (hp : j p ∈ W), r ⟨j p, hp⟩ = p) :
    letI := N.ambientRealization.space.topology
    letI := N.pullback.space.topology
    letI := N.quotient.topology
    ∀ t : SmoothBundleMorphism N.quotient.bundle N.pullback.space.bundle,
      let A := fun z => j (i z.proj) + D (i z.proj) (t.linearMap z.proj z.snd)
      RetractionCandidate S i N.quotient.bundle A W r := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  intro t A
  have hA := normal_addition_smooth N hi j hj D hD t
  have hAs := smoothEuclidean_to_smoothMap N.quotient.bundle.totalManifold A R hR hA
  have hzero : ∀ p, A ⟨p, 0⟩ = j (i p) := by
    intro p
    change j (i p) + D (i p) (t.linearMap p 0) = j (i p)
    rw [map_zero, map_zero, add_zero]
  have hzeroW : ∀ p, A ⟨p, 0⟩ ∈ W := by
    intro p
    rw [hzero p]
    exact hjW ⟨i p, rfl⟩
  obtain ⟨F, hF, heq⟩ := smooth_open_composition_totalization
    N.quotient.bundle.totalManifold R S A hAs W hW r hr (fun z => i z.proj)
  refine ⟨F, hW.preimage (continuous_iff_continuousAt.mpr fun z => (hA z).1),
    hzeroW, ?_, hF, heq⟩
  intro p
  rw [heq ⟨p, 0⟩ (hzeroW p)]
  exact (congrArg r (Subtype.ext (hzero p))).trans (hrzero (i p) (hjW ⟨i p, rfl⟩))

/-- In coordinates, a smooth retraction has derivative inverse to the
embedding differential on tangent vectors. The coordinate representative and
its derivative are obtained from smoothness, rather than assumed. -/
theorem retraction_coordinate_left_inverse
    {n q : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X)
    (j : X → Euclidean q) (hj : GoodProjectionData.IsSmoothEuclidean S j)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : EmbeddedData.euclideanChart q ∈ T.smoothStructure.val)
    (W : Set (Euclidean q)) (hW : IsOpen W) (r : W → X)
    (hjW : range j ⊆ W)
    (hr : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      S.smoothStructure.val r)
    (hrzero : ∀ x (hx : j x ∈ W), r ⟨j x, hx⟩ = x)
    (p : X) (d : ModelChart n .euclidean X)
    (hd : d ∈ S.smoothStructure.val) (hp : p ∈ d.source)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (D : TangentSpace S p →ₗ[ℝ] Euclidean q)
    (hD : ∀ v, D v = FiniteRegularityData.coordinateDerivative d j p (E v)) :
    ∃ (U : Set (Euclidean q)) (H : Euclidean q → Euclidean n),
      IsOpen U ∧ j p ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) H U ∧
      ((fun y : W => H y.val) =ᶠ[𝓝 (⟨j p, hjW ⟨p, rfl⟩⟩ : W)]
        (fun y => (d (r y)).val)) ∧
      ∀ v, fderiv ℝ H (j p) (D v) = E v := by
  let jp : W := ⟨j p, hjW ⟨p, rfl⟩⟩
  let c := (EmbeddedData.euclideanChart q).subtypeRestr (s := ⟨W, hW⟩) ⟨jp⟩
  have hc : c ∈ openSubsetAtlas T.smoothStructure.val W hW :=
    ⟨⟨jp⟩, EmbeddedData.euclideanChart q, hT, rfl⟩
  have hjpc : jp ∈ c.source := by
    simp only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    exact mem_univ _
  have hjpd : r jp ∈ d.source := by simpa only [jp, hrzero] using hp
  obtain ⟨U, hU, hjU, H, hH, heH⟩ := (hr jp).2 c hc d hd hjpc hjpd
  have hHder : HasFDerivAt H (fderiv ℝ H (j p)) (j p) :=
    ((hH.contDiffAt (hU.mem_nhds hjU)).differentiableAt (by simp)).hasFDerivAt
  let jW : X → W := fun x => ⟨j x, hjW ⟨x, rfl⟩⟩
  have hjWcont : ContinuousAt jW p := tendsto_subtype_rng.mpr (hj p).1
  have heHp : (fun x => H (j x)) =ᶠ[𝓝 p] (fun x => (d x).val) := by
    have ht := heH.comp_tendsto hjWcont
    filter_upwards [ht] with x hx
    change H (j x) = (d (r (jW x))).val at hx
    simpa only [jW, hrzero] using hx
  obtain ⟨V, hV, hpV, F, hF, heF⟩ := (hj p).2 d hd hp
  let J := fderiv ℝ F (d p).val
  have hFder : HasFDerivAt F J (d p).val :=
    ((hF.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)).hasFDerivAt
  have hJ : FiniteRegularityData.coordinateDerivative d j p = J :=
    FiniteRegularity.coordinateDerivative_eq d j p hp J ⟨F, hFder, heF⟩
  have hcomp : FiniteRegularityData.coordinateDerivative d (fun x => (d x).val) p =
      (fderiv ℝ H (j p)).comp J := by
    apply FiniteRegularity.coordinateDerivative_eq d _ p hp
    refine ⟨H ∘ F, ?_, ?_⟩
    · have hbase : F (d p).val = j p := heF.eq_of_nhds
      have hH' : HasFDerivAt H (fderiv ℝ H (j p)) (F (d p).val) := by
        rw [hbase]
        exact hHder
      exact hH'.comp (d p).val hFder
    · exact (heF.fun_comp H).trans heHp
  have hid : (fderiv ℝ H (j p)).comp J = ContinuousLinearMap.id ℝ (Euclidean n) :=
    hcomp.symm.trans (FiniteRegularity.chartDerivative_id d p hp)
  refine ⟨U, H, hU, hjU, hH, heH, ?_⟩
  intro v
  rw [hD v, hJ]
  exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L (E v)) hid

/-- At fiber zero a bundle chart identifies a derivative with its horizontal
and vertical blocks. Horizontal differentiation uses the zero section, while
vertical differentiation uses the actual fiber-linear trivialization. -/
theorem bundle_derivative_at_zero
    {m r q : ℕ} {P : Type u} [TopologicalSpace P]
    {T : SmoothManifold m .euclidean P} {ι : Type v} {V : P → Type w}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) V)]
    (B : SmoothVectorBundle T r ι V)
    (A : Bundle.TotalSpace (Euclidean r) V → Euclidean q) (f : P → Euclidean q)
    (p : P) (k : ι) (hpk : p ∈ B.baseSet k)
    (c : ModelChart m .euclidean P) (hc : c ∈ T.smoothStructure.val)
    (hpc : p ∈ c.source)
    (hA : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
      B.totalManifold.smoothStructure.val A ⟨p, 0⟩)
    (hzero : ∀ x, A ⟨x, 0⟩ = f x)
    (Q : Euclidean r →L[ℝ] Euclidean q)
    (hvert : HasFDerivAt
      (fun v => A ⟨p, (B.fiberCoordinates k p hpk).symm v⟩) Q 0) :
    let b := bundleChart B.coordinates (B.trivialization k) c
    ∃ L : Euclidean (m + r) →L[ℝ] Euclidean q,
      FiniteRegularityData.HasCoordinateDerivative b A ⟨p, 0⟩ L ∧
      L.comp B.coordinates.linearEquiv.toContinuousLinearMap =
        (FiniteRegularityData.coordinateDerivative c f p).coprod Q := by
  intro b
  let e := B.trivialization k
  have hpE : p ∈ e.baseSet := (B.trivialization_baseSet k).symm ▸ hpk
  have hzb : (⟨p, 0⟩ : Bundle.TotalSpace (Euclidean r) V) ∈ b.source :=
    (mem_bundleChart_source _ _ _ _).mpr ⟨hpE, hpc⟩
  have hzbcoords (x : P) (hx : x ∈ B.baseSet k) :
      (b ⟨x, 0⟩).val = B.coordinates.linearEquiv ((c x).val, 0) := by
    rw [bundleChart_val B.coordinates e c ⟨x, 0⟩
      ((B.trivialization_baseSet k).symm ▸ hx)]
    change B.coordinates.linearEquiv ((c x).val, B.fiberCoordinates k x hx 0) = _
    rw [map_zero]
  obtain ⟨U, hU, hzU, F, hF, heF⟩ := hA.2 b (B.chart_mem k c hc) hzb
  let L := fderiv ℝ F (b ⟨p, 0⟩).val
  have hFd : HasFDerivAt F L (b ⟨p, 0⟩).val :=
    ((hF.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)).hasFDerivAt
  have hL : FiniteRegularityData.HasCoordinateDerivative b A ⟨p, 0⟩ L := ⟨F, hFd, heF⟩
  rw [hzbcoords p hpk] at hFd
  let C := B.coordinates.linearEquiv.toContinuousLinearMap
  let Ch := C.comp (ContinuousLinearMap.inl ℝ (Euclidean m) (Euclidean r))
  let Cv := C.comp (ContinuousLinearMap.inr ℝ (Euclidean m) (Euclidean r))
  have hhor : FiniteRegularityData.HasCoordinateDerivative c f p (L.comp Ch) := by
    refine ⟨fun x => F (Ch x), hFd.comp (c p).val Ch.hasFDerivAt, ?_⟩
    have hbopen := (B.trivialization k).open_baseSet
    rw [B.trivialization_baseSet k] at hbopen
    filter_upwards [heF.comp_tendsto (B.zero_smooth p).1,
      hbopen.mem_nhds hpk] with x hxF hxk
    change F (b ⟨x, 0⟩).val = A ⟨x, 0⟩ at hxF
    rw [hzbcoords x hxk, hzero x] at hxF
    exact hxF
  have hCh : FiniteRegularityData.coordinateDerivative c f p = L.comp Ch :=
    FiniteRegularity.coordinateDerivative_eq c f p hpc _ hhor
  let vmap : Euclidean r → Bundle.TotalSpace (Euclidean r) V :=
    fun v => ⟨p, (B.fiberCoordinates k p hpk).symm v⟩
  have hvcont : Continuous vmap := by
    exact e.continuousOn_symm.comp_continuous
      (show Continuous (fun v : Euclidean r => (p, v)) from continuous_const.prodMk continuous_id)
      (fun _ => ⟨hpE, mem_univ _⟩)
  have hvzero : vmap 0 = ⟨p, 0⟩ := by simp only [vmap, map_zero]
  have hvcoord (v : Euclidean r) :
      (b (vmap v)).val = B.coordinates.linearEquiv ((c p).val, v) := by
    rw [bundleChart_val B.coordinates e c (vmap v) hpE]
    change B.coordinates.linearEquiv ((c p).val,
      B.fiberCoordinates k p hpk ((B.fiberCoordinates k p hpk).symm v)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hevert : (fun v => F (C ((c p).val, v))) =ᶠ[𝓝 (0 : Euclidean r)]
      (fun v => A (vmap v)) := by
    have hvt := hvcont.tendsto 0
    rw [hvzero] at hvt
    have ht := heF.comp_tendsto hvt
    filter_upwards [ht] with v hv
    change F (b (vmap v)).val = A (vmap v) at hv
    rwa [hvcoord v] at hv
  have hCv : HasFDerivAt (fun v : Euclidean r => C ((c p).val, v)) Cv 0 := by
    convert C.hasFDerivAt.comp (0 : Euclidean r)
      ((hasFDerivAt_const (c p).val (0 : Euclidean r)).prodMk (hasFDerivAt_id 0)) using 1 <;>
      ext v i <;> simp [Cv]
  have hvert' : L.comp Cv = Q :=
    ((hFd.comp 0 hCv).congr_of_eventuallyEq hevert.symm).unique hvert
  refine ⟨L, hL, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  rcases z with ⟨x, v⟩
  change L (C (x, v)) = _
  have hsplit : C (x, v) = Ch x + Cv v := by
    change C (x, v) = C (x, 0) + C (0, v)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [hsplit, map_add]
  change (L.comp Ch) x + (L.comp Cv) v = _
  rw [← hCh, hvert']
  rfl

/-- Target chart coordinates of a smooth map are smooth as a Euclidean-valued
map near any point mapping into the chart. -/
theorem smoothAt_target_chart
    {k n : ℕ} {a b : ModelKind} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set (ModelChart k a X)) (B : Set (ModelChart n b Y))
    (f : X → Y) (p : X) (hf : ManifoldSmoothAt A B f p)
    (d : ModelChart n b Y) (hd : d ∈ B) (hp : f p ∈ d.source) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) A (fun x => (d (f x)).val) p := by
  refine ⟨continuous_subtype_val.continuousAt.comp
    ((d.continuousAt hp).comp hf.1), ?_⟩
  intro c hc hpc
  exact hf.2 c hc d hd hpc hp

/-- For the actual quotient normal bundle, the differential of the inclusion
and a quotient lift give a bijective horizontal/vertical derivative in the
specified bundle and manifold coordinates. -/
theorem normal_coprod_bijective_coordinates
    {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
    {i : P → M} (N : NormalBundle T S i) (hi : IsSmoothMap T S i) :
    letI := N.ambientRealization.space.topology
    letI := N.pullback.space.topology
    letI := N.quotient.topology
    ∀ (t : SmoothBundleMorphism N.quotient.bundle N.pullback.space.bundle)
      (ht : ∀ p v, (N.differential p).range.mkQ (t.linearMap p v) = v)
      (p : P) (c : ModelChart m .euclidean P) (d : ModelChart n .euclidean M)
      (hc : c ∈ T.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
      (hp : p ∈ c.source) (hip : i p ∈ d.source)
      (k : P) (hpk : p ∈ N.quotient.bundle.baseSet k)
      (K : Euclidean (n - m) →L[ℝ] Euclidean n),
      (∀ v, K v = N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip
        (t.linearMap p ((N.quotient.bundle.fiberCoordinates k p hpk).symm v))) →
      Function.Bijective ((FiniteRegularityData.chartDerivative c d i p).coprod K) := by
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  intro t ht p c d hc hd hp hip k hpk K hK
  let C := N.sourceTangent.fiberCoordinates.equiv c hc p hp
  let E := N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip
  let Q := N.quotient.bundle.fiberCoordinates k p hpk
  have hsum : Function.Bijective ((N.differential p).coprod (t.linearMap p)) :=
    @quotient_sum_bijective P (TangentSpace T) (fun p => TangentSpace S (i p))
      (fun p => inferInstance) (fun p => inferInstance)
      (fun p => inferInstance) (fun p => inferInstance)
      N.differential N.injective t.linearMap ht p
  have hJ : ∀ w, FiniteRegularityData.chartDerivative c d i p w =
      E (N.differential p (C.symm w)) := by
    intro w
    have hj := FiniteRegularity.smooth_jacobian_coordinateDerivative T S i hi p
      (N.differential p) (N.isDifferential p) c d hc hd hp hip C E
      (N.sourceTangent.fiberCoordinates.isCoordinates c hc p hp)
      (N.ambientTangent.fiberCoordinates.isCoordinates d hd (i p) hip) (C.symm w)
    simpa only [LinearEquiv.apply_symm_apply] using hj.symm
  let J := FiniteRegularityData.chartDerivative c d i p
  have hform (z : Euclidean m × Euclidean (n - m)) :
      (J.coprod K) z =
        E (((N.differential p).coprod (t.linearMap p)) (C.symm z.1, Q.symm z.2)) := by
    rw [ContinuousLinearMap.coprod_apply, LinearMap.coprod_apply, map_add]
    exact congrArg₂ (fun x y : Euclidean n => x + y) (hJ z.1) (hK z.2)
  constructor
  · intro x y hxy
    have hxy' := E.injective ((hform x).symm.trans (hxy.trans (hform y)))
    have hpre := hsum.1 hxy'
    apply Prod.ext
    · exact C.symm.injective (congrArg Prod.fst hpre)
    · exact Q.symm.injective (congrArg Prod.snd hpre)
  · intro y
    obtain ⟨⟨a, b⟩, hab⟩ := hsum.2 (E.symm y)
    refine ⟨(C a, Q b), ?_⟩
    rw [hform, C.symm_apply_apply, Q.symm_apply_apply, hab, E.apply_symm_apply]


/-- Differentiate a totalized retraction formula along a curve that stays in
the retraction domain near the point. -/
theorem retraction_curve_hasFDerivAt
    {E G K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    {Y : Type u} {Z : Type v}
    (A : Y → E) (F : Y → Z) (d : Z → G)
    (W : Set E) (hW : IsOpen W) (r : W → Z)
    (heq : ∀ y (hy : A y ∈ W), F y = r ⟨A y, hy⟩)
    (γ : K → Y) (x : K) (hx : A (γ x) ∈ W)
    (L : K →L[ℝ] E) (hL : HasFDerivAt (fun v => A (γ v)) L x)
    (H : E → G) (J : E →L[ℝ] G)
    (hH : HasFDerivAt H J (A (γ x)))
    (heH : (fun y : W => H y.val) =ᶠ[𝓝 (⟨A (γ x), hx⟩ : W)]
      (fun y => d (r y))) :
    HasFDerivAt (fun v => d (F (γ v))) (J.comp L) x := by
  classical
  let a : W := ⟨A (γ x), hx⟩
  let γW : K → W := fun v => if h : A (γ v) ∈ W then ⟨A (γ v), h⟩ else a
  have hmem : ∀ᶠ v in 𝓝 x, A (γ v) ∈ W :=
    hL.continuousAt.preimage_mem_nhds (hW.mem_nhds hx)
  have hγW : Tendsto γW (𝓝 x) (𝓝 a) := by
    apply tendsto_subtype_rng.mpr
    apply hL.continuousAt.tendsto.congr'
    filter_upwards [hmem] with v hv
    simp only [γW, dite_eq_left hv]
  have hecurve : (fun v => H (A (γ v))) =ᶠ[𝓝 x] (fun v => d (F (γ v))) := by
    have ht := heH.comp_tendsto hγW
    filter_upwards [hmem, ht] with v hv hhv
    change H (γW v).val = d (r (γW v)) at hhv
    simp only [γW, dite_eq_left hv] at hhv
    rw [heq (γ v) hv]
    exact hhv
  exact (hH.comp x hL).congr_of_eventuallyEq hecurve.symm


/-- The preceding derivative formula along an affine ambient curve. -/
theorem retraction_affine_curve_hasFDerivAt
    {E G K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    {Y : Type u} {Z : Type v}
    (A : Y → E) (F : Y → Z) (d : Z → G)
    (W : Set E) (hW : IsOpen W) (r : W → Z)
    (heq : ∀ y (hy : A y ∈ W), F y = r ⟨A y, hy⟩)
    (γ : K → Y) (c : E) (hc : c ∈ W)
    (L : K →L[ℝ] E) (hAγ : ∀ v, A (γ v) = c + L v)
    (H : E → G) (J : E →L[ℝ] G)
    (hH : HasFDerivAt H J c)
    (heH : (fun y : W => H y.val) =ᶠ[𝓝 (⟨c, hc⟩ : W)]
      (fun y => d (r y))) :
    HasFDerivAt (fun v => d (F (γ v))) (J.comp L) 0 := by
  have hA0 : A (γ 0) = c := by simp only [hAγ, map_zero, add_zero]
  apply retraction_curve_hasFDerivAt A F d W hW r heq γ 0 (hA0 ▸ hc) L
    (show HasFDerivAt (fun v => A (γ v)) L 0 from ?_) H J
    (hA0.symm ▸ hH) (by simpa only [hA0] using heH)
  convert (hasFDerivAt_const c (0 : K)).add L.hasFDerivAt using 1
  · exact funext hAγ
  · simp only [zero_add]


/-- A retraction left inverse sends the derivative of a lifted linear curve
back to its intrinsic coordinate vector. -/
theorem retraction_linear_curve_hasFDerivAt
    {E G K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
    {U : Type w} [AddCommGroup U] [Module ℝ U]
    {Y : Type u} {Z : Type v}
    (A : Y → E) (F : Y → Z) (d : Z → G)
    (W : Set E) (hW : IsOpen W) (r : W → Z)
    (heq : ∀ y (hy : A y ∈ W), F y = r ⟨A y, hy⟩)
    (γ : K → Y) (c : E) (hc : c ∈ W)
    (D : U →ₗ[ℝ] E) (C : U →ₗ[ℝ] G) (t : K →ₗ[ℝ] U)
    (hAγ : ∀ v, A (γ v) = c + D (t v))
    (H : E → G) (J : E →L[ℝ] G)
    (hH : HasFDerivAt H J c)
    (heH : (fun y : W => H y.val) =ᶠ[𝓝 (⟨c, hc⟩ : W)]
      (fun y => d (r y)))
    (hJD : ∀ v, J (D v) = C v) :
    HasFDerivAt (fun v => d (F (γ v)))
      (C.comp t).toContinuousLinearMap 0 := by
  have hder := retraction_affine_curve_hasFDerivAt A F d W hW r heq γ c hc
    (D.comp t).toContinuousLinearMap hAγ H J hH heH
  have heqder : J.comp (D.comp t).toContinuousLinearMap =
      (C.comp t).toContinuousLinearMap := by
    ext v
    exact hJD (t v)
  rw [heqder] at hder
  exact hder

/-- Retraction coordinates differentiate the vertical affine addition formula
on any abstract fiber. The output is the actual coordinate image of the lift. -/
theorem retraction_vertical_derivative
    {n q rnk : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M)
    (j : M → Euclidean q) (hj : GoodProjectionData.IsSmoothEuclidean S j)
    (R : SmoothManifold q .euclidean (Euclidean q))
    (hR : EmbeddedData.euclideanChart q ∈ R.smoothStructure.val)
    (W : Set (Euclidean q)) (hW : IsOpen W) (r : W → M)
    (hjW : range j ⊆ W)
    (hr : ManifoldSmooth (openSubsetAtlas R.smoothStructure.val W hW)
      S.smoothStructure.val r)
    (hrzero : ∀ x (hx : j x ∈ W), r ⟨j x, hx⟩ = x)
    (p : M) (d : ModelChart n .euclidean M)
    (hd : d ∈ S.smoothStructure.val) (hp : p ∈ d.source)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (D : TangentSpace S p →ₗ[ℝ] Euclidean q)
    (hD : ∀ v, D v = FiniteRegularityData.coordinateDerivative d j p (E v))
    {Y : Type v} {V : Type w} [AddCommGroup V] [Module ℝ V]
    (C : V ≃ₗ[ℝ] Euclidean rnk) (t : V →ₗ[ℝ] TangentSpace S p)
    (A : Y → Euclidean q) (F : Y → M)
    (heq : ∀ y (hy : A y ∈ W), F y = r ⟨A y, hy⟩)
    (γ : Euclidean rnk → Y)
    (hAγ : ∀ v, A (γ v) = j p + D (t (C.symm v))) :
    ∃ K : Euclidean rnk →L[ℝ] Euclidean n,
      HasFDerivAt (fun v => (d (F (γ v))).val) K 0 ∧
      ∀ v, K v = E (t (C.symm v)) := by
  obtain ⟨U, H, hU, hjU, hH, heH, hleft⟩ :=
    retraction_coordinate_left_inverse S j hj R hR W hW r hjW hr hrzero
      p d hd hp E D hD
  let K : Euclidean rnk →L[ℝ] Euclidean n :=
    (E.toLinearMap.comp (t.comp C.symm.toLinearMap)).toContinuousLinearMap
  have hHder : HasFDerivAt H (fderiv ℝ H (j p)) (j p) :=
    ((hH.contDiffAt (hU.mem_nhds hjU)).differentiableAt (by simp)).hasFDerivAt
  refine ⟨K, ?_, fun _ => rfl⟩
  exact retraction_linear_curve_hasFDerivAt (U := TangentSpace S p)
    (E := Euclidean q) (G := Euclidean n) (K := Euclidean rnk) A F (fun y => (d y).val)
    W hW r heq γ (j p) (hjW ⟨p, rfl⟩) D E.toLinearMap
    (t.comp C.symm.toLinearMap) hAγ H (fderiv ℝ H (j p)) hHder heH hleft


/-- Fiberwise derivative tests at zero suffice for a local tubular map. The
horizontal block is the derivative of the prescribed map on the zero section. -/
theorem localTubularMap_of_fiber_derivatives
    {m n r : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} (S : SmoothManifold n .euclidean M)
    (i : P → M) {ι : Type u} {V : P → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) V)]
    (B : SmoothVectorBundle T r ι V)
    (U : Set (Bundle.TotalSpace (Euclidean r) V)) (hU : IsOpen U)
    (F : Bundle.TotalSpace (Euclidean r) V → M)
    (hzero : ∀ p, (⟨p, 0⟩ : Bundle.TotalSpace (Euclidean r) V) ∈ U)
    (hFzero : ∀ p, F ⟨p, 0⟩ = i p)
    (hF : ManifoldSmoothOn B.totalManifold.smoothStructure.val S.smoothStructure.val F U)
    (hvertical : ∀ p, ∃ (k : ι) (hpk : p ∈ B.baseSet k)
        (c : ModelChart m .euclidean P) (d : ModelChart n .euclidean M)
        (K : Euclidean r →L[ℝ] Euclidean n),
      c ∈ T.smoothStructure.val ∧ d ∈ S.smoothStructure.val ∧
      p ∈ c.source ∧ i p ∈ d.source ∧
      HasFDerivAt (fun v =>
        (d (F ⟨p, (B.fiberCoordinates k p hpk).symm v⟩)).val) K 0 ∧
      Function.Bijective ((FiniteRegularityData.chartDerivative c d i p).coprod K)) :
    Specs.SmoothManifolds.Ch05.TubularLocalGeometry.LocalTubularMap S i B := by
  apply localTubularMap_of_bijective_derivatives S i B U hU F hzero hFzero hF
  intro p
  obtain ⟨k, hpk, c, d, K, hc, hd, hpc, hipd, hK, hbij⟩ := hvertical p
  let b := bundleChart B.coordinates (B.trivialization k) c
  have hzb : (⟨p, 0⟩ : Bundle.TotalSpace (Euclidean r) V) ∈ b.source :=
    (mem_bundleChart_source _ _ _ _).mpr
      ⟨(B.trivialization_baseSet k).symm ▸ hpk, hpc⟩
  have hFpd : F ⟨p, 0⟩ ∈ d.source := by rwa [hFzero p]
  have hg := smoothAt_target_chart _ _ F ⟨p, 0⟩ (hF ⟨p, 0⟩ (hzero p)) d hd hFpd
  obtain ⟨L, hL, hblocks⟩ := bundle_derivative_at_zero B
    (fun z => (d (F z)).val) (fun x => (d (i x)).val) p k hpk c hc hpc hg
    (fun x => congrArg (fun y => (d y).val) (hFzero x)) K hK
  have hder : FiniteRegularityData.chartDerivative b d F ⟨p, 0⟩ = L :=
    FiniteRegularity.coordinateDerivative_eq b _ ⟨p, 0⟩ hzb L hL
  refine ⟨b, d, B.chart_mem k c hc, hd, hzb, hFpd, ?_⟩
  rw [hder]
  apply (Function.Bijective.of_comp_iff L B.coordinates.linearEquiv.bijective).mp
  change Function.Bijective (L.comp B.coordinates.linearEquiv.toContinuousLinearMap)
  rw [hblocks]
  exact hbij

/-- Local tubular geometry on the prescribed quotient normal bundle. The
ambient retraction and the smooth complementary lift are constructed from the
original data; no metric, lift, or local-inverse certificate is assumed. -/
theorem tubular_local_geometry :
    Specs.SmoothManifolds.Ch05.TubularLocalGeometry.tubular_local_geometryType.{u} := by
  intro m n P M _ _ T S i hi N
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  obtain ⟨t, ht⟩ := normal_lift_exists N
  obtain ⟨j, R, W, hW, r, hj, hR, hjW, hr, hrzero⟩ := exists_euclidean_retraction S
  obtain ⟨D, hD, hDcoords⟩ :=
    exists_smooth_euclidean_differential S N.ambientTangent j hj.1
  let A := fun z : Bundle.TotalSpace (Euclidean (n - m))
      (QuotientFiber (E := fun p : P => TangentSpace S (i p))
        (fun p => (N.differential p).range)) => j (i z.proj) + D (i z.proj) (t.linearMap z.proj z.snd)
  obtain ⟨F, hU, hzero, hFzero, hF, heq⟩ :=
    normal_retraction_candidate N hi.1 j hj.1 D hD R hR W hW r hjW hr hrzero t
  apply localTubularMap_of_fiber_derivatives S i N.quotient.bundle
    (A ⁻¹' W) hU F hzero hFzero hF
  intro p
  obtain ⟨k, hpk⟩ := N.quotient.bundle.covers p
  obtain ⟨c, hc, hpc⟩ := T.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hip⟩ := S.smoothStructure.property.1.1 (i p)
  let E := N.ambientTangent.fiberCoordinates.equiv d hd (i p) hip
  have hDcoord : ∀ v, D (i p) v =
      FiniteRegularityData.coordinateDerivative d j (i p) (E v) :=
    hDcoords (i p) d hd hip E
      (N.ambientTangent.fiberCoordinates.isCoordinates d hd (i p) hip)
  obtain ⟨K, hK, heK⟩ := retraction_vertical_derivative S j hj.1 R hR W hW r
    hjW hr hrzero (i p) d hd hip E (D (i p)) hDcoord
    (N.quotient.bundle.fiberCoordinates k p hpk) (t.linearMap p) A F heq
    (fun v => ⟨p, (N.quotient.bundle.fiberCoordinates k p hpk).symm v⟩)
    (fun _ => rfl)
  refine ⟨k, hpk, c, d, K, hc, hd, hpc, hip, hK, ?_⟩
  exact normal_coprod_bijective_coordinates N hi.1 t ht p c d hc hd hpc hip k hpk K heK


end SmoothManifolds.TubularLocalGeometry
