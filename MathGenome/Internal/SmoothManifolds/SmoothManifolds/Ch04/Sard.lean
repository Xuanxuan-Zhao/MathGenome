import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.Sard
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.EuclideanSard
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology

namespace SmoothManifolds.Sard
open ModelData AtlasData MapData MapClassData SardData FiniteRegularityData Set Filter MeasureTheory
open scoped Topology ContDiff
universe u v

abbrev NullInCharts := @SardData.NullInCharts
abbrev IsNull := @SardData.IsNull
abbrev criticalValues := @SardData.criticalValues

/-- Empty products of Lebesgue measures are counting measure on the point. -/
theorem coordinate_volume_zero_eq_count :
    Specs.SmoothManifolds.Ch04.Sard.coordinate_volume_zero_eq_countType := by
  change (volume : Measure (Euclidean 0)) = Measure.count
  rw [Measure.volume_pi_eq_dirac (0 : Euclidean 0), Subsingleton.count_eq_dirac (0 : Euclidean 0)]

/-- Local ambient extensions preserve null coordinate images in equal dimension.
No regularity of the set being measured is required. -/
lemma locally_null_image_of_extension {n : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] (e : ModelChart n a X) (g : X → Euclidean n)
    (s : Set X) (p : X) (hp : p ∈ e.source)
    (hext : LocalCoordinateExtension (⊤ : ℕ∞) (fun x => (e x).val) g p)
    (hnull : volume ((fun x => (e x).val) '' (s ∩ e.source)) = 0) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ volume (g '' (s ∩ V)) = 0 := by
  obtain ⟨U, hU, hpU, F, hF, heq⟩ := hext
  have hnhds : ∀ᶠ x in 𝓝 p,
      x ∈ e.source ∧ (e x).val ∈ U ∧ F (e x).val = g x := by
    filter_upwards [e.open_source.mem_nhds hp,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
        (hU.mem_nhds hpU), heq] with x hx hxU hxF
    exact ⟨hx, hxU, hxF⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnhds
  refine ⟨V, hV, hpV, ?_⟩
  have hsub : (fun x => (e x).val) '' (s ∩ V) ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hVsub hx.2).2.1
  have hdiff : DifferentiableOn ℝ F ((fun x => (e x).val) '' (s ∩ V)) := by
    intro x hx
    exact ((hF.contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt (by simp)).differentiableWithinAt
  have hz : volume ((fun x => (e x).val) '' (s ∩ V)) = 0 :=
    measure_mono_null (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx.1, (hVsub hx.2).1⟩, rfl⟩) hnull
  have hFn := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hz
  apply measure_mono_null _ hFn
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨(e x).val, ⟨x, hx, rfl⟩, (hVsub hx.2).2.2⟩

/-- A chart with smooth transitions from a covering family preserves nullity. -/
lemma chart_null_of_cover {n : ℕ} {a b : ModelKind} {X : Type u}
    [TopologicalSpace X] [SecondCountableTopology X]
    (A : Set (ModelChart n a X)) (hA : IsAtlas A)
    (s : Set X) (hs : NullInCharts A s) (d : ModelChart n b X)
    (hd : ∀ e ∈ A, ∀ p ∈ e.source, p ∈ d.source →
      ChartContDiffAt (⊤ : ℕ∞) e d id p) :
    volume ((fun y => (d y).val) '' (s ∩ d.source)) = 0 := by
  apply Ch04.SardVanishingLayer.image_null_of_locally_image_null
  rintro p ⟨hps, hpd⟩
  obtain ⟨e, he, hpe⟩ := hA p
  apply locally_null_image_of_extension e _ (s ∩ d.source) p hpe
    (hd e he p hpe hpd)
  exact measure_mono_null (image_mono (by
    rintro x ⟨⟨hx, _⟩, hxe⟩
    exact ⟨hx, hxe⟩)) (hs e he)

theorem compatible_chart_null :
    Specs.SmoothManifolds.Ch04.Sard.compatible_chart_nullType.{v} := by
  intro n a b N _ T s hs e he
  let := T.topologicalManifold.secondCountable
  exact chart_null_of_cover T.smoothStructure.val T.smoothStructure.property.1.1 s hs e he

theorem nullInCharts_iff :
    Specs.SmoothManifolds.Ch04.Sard.nullInCharts_iffType.{v} := by
  intro n a N _ T A hA hcompat s
  let := T.topologicalManifold.secondCountable
  constructor
  · intro hs d hd
    exact chart_null_of_cover A hA s hs d (fun e he p hpe hpd =>
      chartContDiffAt_of_compatible (hcompat e he d hd) hpe hpd)
  · intro hs e he
    apply compatible_chart_null T s hs e
    intro d hd p hpd hpe
    exact chartContDiffAt_of_compatible
      ⟨(hcompat e he d hd).2, (hcompat e he d hd).1⟩ hpd hpe

/-- On one sufficiently small manifold neighborhood, the same smooth extension
represents both the coordinate map and its full derivative at every point. -/
lemma local_extension_derivative {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (e : ModelChart m a M) (d : ModelChart n b N) (f : M → N) (p : M)
    (hp : p ∈ e.source) (hext : ChartContDiffAt (⊤ : ℕ∞) e d f p) :
    ∃ (V : Set M) (U : Set (Euclidean m)) (F : Euclidean m → Euclidean n),
      IsOpen V ∧ p ∈ V ∧ IsOpen U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ q ∈ V, q ∈ e.source ∧ (e q).val ∈ U ∧
        F (e q).val = (d (f q)).val ∧
        chartDerivative e d f q = fderiv ℝ F (e q).val := by
  obtain ⟨U, hU, hpU, F, hF, heq⟩ := hext
  have hnhds : ∀ᶠ q in 𝓝 p,
      q ∈ e.source ∧ (e q).val ∈ U ∧
        (fun x => F (e x).val) =ᶠ[𝓝 q] (fun x => (d (f x)).val) := by
    filter_upwards [e.open_source.mem_nhds hp,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
        (hU.mem_nhds hpU), heq.eventuallyEq_nhds] with q hq hqU hqF
    exact ⟨hq, hqU, hqF⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnhds
  refine ⟨V, U, F, hV, hpV, hU, hF, ?_⟩
  intro q hq
  obtain ⟨hqe, hqU, hqF⟩ := hVsub hq
  refine ⟨hqe, hqU, hqF.eq_of_nhds, ?_⟩
  exact FiniteRegularity.coordinateDerivative_eq e _ q hqe _
    ⟨F, ((hF.contDiffAt (hU.mem_nhds hqU)).differentiableAt (by simp)).hasFDerivAt, hqF⟩

/-- Euclidean Sard transfers to each target chart, including source faces. -/
theorem sard : Specs.SmoothManifolds.Ch04.Sard.sardType.{u,v} := by
  intro m n a b M N _ _ S T f hf d hd
  let := S.topologicalManifold.secondCountable
  have hf1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf
  have hnull : volume ((fun p => (d (f p)).val) ''
      {p | ¬ IsSubmersionAt S T f p ∧ f p ∈ d.source}) = 0 := by
    apply Ch04.SardVanishingLayer.image_null_of_locally_image_null
    rintro p ⟨hpcrit, hpd⟩
    obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨V, U, F, hV, hpV, hU, hF, hrep⟩ :=
      local_extension_derivative e d f p hpe ((hf p).2 e he d hd hpe hpd)
    refine ⟨V, hV, hpV, ?_⟩
    apply measure_mono_null _ (Ch04.euclidean_sard m n U F hU hF)
    rintro _ ⟨q, ⟨⟨hqcrit, hqd⟩, hqV⟩, rfl⟩
    obtain ⟨hqe, hqU, hqF, hqD⟩ := hrep q hqV
    refine ⟨(e q).val, ⟨hqU, ?_⟩, hqF⟩
    rw [← hqD]
    exact fun hsurj => hqcrit ((MapClasses.chart_invariants S T f hf1 q e d
      he hd hqe hqd).2.2.mpr hsurj)
  apply measure_mono_null _ hnull
  rintro _ ⟨y, ⟨⟨p, hpcrit, rfl⟩, hpd⟩, rfl⟩
  exact ⟨p, ⟨hpcrit, hpd⟩, rfl⟩

/-- A full differential from fewer source coordinates cannot be onto. -/
lemma not_submersion_of_dimension_lt {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (hmn : m < n) (p : M) :
    ¬ IsSubmersionAt S T f p := by
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f p)
  intro hp
  have hsurj := (MapClasses.chart_invariants S T f
    (manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf) p e d he hd hpe hpd).2.2.mp hp
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := (chartDerivative e d f p).toLinearMap) hsurj
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  omega

theorem image_null_of_dimension_lt :
    Specs.SmoothManifolds.Ch04.Sard.image_null_of_dimension_ltType.{u,v} := by
  intro m n a b M N _ _ S T f hf hmn
  have heq : criticalValues S T f = Set.range f := by
    ext y
    constructor
    · rintro ⟨p, _, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, not_submersion_of_dimension_lt S T f hf hmn p, rfl⟩
  rw [← heq]
  exact sard S T f hf

theorem criticalValues_target_zero :
    Specs.SmoothManifolds.Ch04.Sard.criticalValues_target_zeroType.{u,v} := by
  intro m a b M N _ _ S T f hf
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro y ⟨p, hp, rfl⟩
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f p)
  apply hp
  apply (MapClasses.chart_invariants S T f
    (manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf) p e d he hd hpe hpd).2.2.mpr
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Both ordinary models have ambient interior, including the one-point model. -/
lemma model_interior_nonempty (n : ℕ) (a : ModelKind) :
    (interior (modelSet n a)).Nonempty := by
  cases a with
  | euclidean => simp [ModelData.modelSet]
  | halfSpace =>
    cases n with
    | zero => simp [ModelData.modelSet, ModelData.halfSpaceSet]
    | succ n =>
      have hi : interior (modelSet (n + 1) .halfSpace) =
          {z : Euclidean (n + 1) | 0 < z (Fin.last n)} := by
        change interior ((fun z : Euclidean (n + 1) => z (Fin.last n)) ⁻¹' Ici 0) = _
        rw [← (isOpenMap_eval (Fin.last n)).preimage_interior_eq_interior_preimage
          (continuous_apply (Fin.last n)), interior_Ici]
        rfl
      rw [hi]
      exact ⟨fun _ => 1, by change (0 : ℝ) < 1; norm_num⟩

/-- Every nonempty relatively open model set has positive ambient volume.
This also proves that a relative neighborhood of a face cannot be null. -/
lemma model_open_volume_pos {n : ℕ} {a : ModelKind}
    {s : Set (ModelSpace n a)} (hs : IsOpen s) (hne : s.Nonempty) :
    0 < volume (Subtype.val '' s : Set (Euclidean n)) := by
  obtain ⟨U, hU, hUs⟩ := hs.image_val
  obtain ⟨x, hx⟩ := hne
  have hxU : x.val ∈ U := (hUs ▸ (mem_image_of_mem Subtype.val hx)).1
  have hxcl : x.val ∈ closure (interior (modelSet n a)) := by
    rw [(convex_modelSet n a).closure_interior_eq_closure_of_nonempty_interior
      (model_interior_nonempty n a), (isClosed_modelSet n a).closure_eq]
    exact x.property
  have hne' : (U ∩ interior (modelSet n a)).Nonempty :=
    mem_closure_iff.mp hxcl U hU hxU
  have hpos := (hU.inter isOpen_interior).measure_pos volume hne'
  exact hpos.trans_le (measure_mono (by
    rw [hUs]
    exact inter_subset_inter_right U interior_subset))

/-- Null sets have dense complement in every manifold, including at faces. -/
lemma null_complement_dense {n : ℕ} {a : ModelKind} {N : Type v}
    [TopologicalSpace N] (T : SmoothManifold n a N) (s : Set N)
    (hs : IsNull T s) : Dense sᶜ := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hne
  by_contra h
  have hsub : U ⊆ s := by
    intro y hy
    by_contra hys
    exact h ⟨y, hy, hys⟩
  obtain ⟨p, hp⟩ := hne
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 p
  let W : Set (ModelSpace n a) := d.target ∩ d.symm ⁻¹' U
  have hW : IsOpen W := d.symm.isOpen_inter_preimage hU
  have hneW : W.Nonempty := ⟨d p, d.map_source hpd, by
    change d.symm (d p) ∈ U
    rwa [d.left_inv hpd]⟩
  have hpos := model_open_volume_pos hW hneW
  have hz : volume (Subtype.val '' W : Set (Euclidean n)) = 0 := by
    apply measure_mono_null _ (hs d hd)
    rintro _ ⟨z, ⟨hz, hzU⟩, rfl⟩
    refine ⟨d.symm z, ⟨hsub hzU, d.map_target hz⟩, ?_⟩
    simp only [d.right_inv hz]
  rw [hz] at hpos
  exact (lt_irrefl _ hpos)

theorem regularValues_dense :
    Specs.SmoothManifolds.Ch04.Sard.regularValues_denseType.{u,v} := by
  intro m n a b M N _ _ S T f hf _hn
  have heq : {y | IsRegularValue S T f y} = (criticalValues S T f)ᶜ := by
    classical
    ext y
    constructor
    · intro hy ⟨p, hp, hpy⟩
      exact hp (hy p hpy)
    · intro hy p hpy
      by_contra hp
      exact hy ⟨p, hp, hpy⟩
  rw [heq]
  exact null_complement_dense T _ (sard S T f hf)

end SmoothManifolds.Sard
