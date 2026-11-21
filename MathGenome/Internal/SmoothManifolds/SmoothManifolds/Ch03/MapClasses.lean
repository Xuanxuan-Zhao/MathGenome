import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.FiniteRegularity

namespace SmoothManifolds.MapClasses
open ModelData AtlasData MapData FiniteRegularityData MapClassData Set
universe u v

/-- A commuting square of vector-space isomorphisms preserves all three
linear invariants. The range equivalence explicitly identifies the images. -/
theorem linear_invariants {V W V' W' : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']
    (E : V ≃ₗ[ℝ] V') (D : W ≃ₗ[ℝ] W')
    (L : V →ₗ[ℝ] W) (J : V' →ₗ[ℝ] W') (h : ∀ v, D (L v) = J (E v)) :
    Module.finrank ℝ (LinearMap.range L) = Module.finrank ℝ (LinearMap.range J) ∧
    (Function.Injective L ↔ Function.Injective J) ∧
    (Function.Surjective L ↔ Function.Surjective J) := by
  have himage : (LinearMap.range L).map D.toLinearMap = LinearMap.range J := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨E x, (h x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨L (E.symm x), ⟨E.symm x, rfl⟩, ?_⟩
      simpa only [LinearEquiv.coe_coe, h, LinearEquiv.apply_symm_apply]
  refine ⟨(D.ofSubmodules _ _ himage).finrank_eq, ?_, ?_⟩
  · constructor
    · intro hL x y hxy
      apply E.symm.injective
      apply hL
      apply D.injective
      simpa only [h, LinearEquiv.apply_symm_apply] using hxy
    · intro hJ x y hxy
      apply E.injective
      apply hJ
      rw [← h, ← h, hxy]
  · constructor
    · intro hL y
      obtain ⟨x, hx⟩ := hL (D.symm y)
      refine ⟨E x, ?_⟩
      rw [← h, hx, D.apply_symm_apply]
    · intro hJ y
      obtain ⟨x, hx⟩ := hJ (D y)
      refine ⟨E.symm x, D.injective ?_⟩
      simpa only [h, LinearEquiv.apply_symm_apply] using hx

/-- The given smooth atlas is also a C¹ atlas. -/
theorem smoothAtlas_contDiff_one {m : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold m a M) :
    IsContDiffAtlas 1 S.smoothStructure.val := by
  refine ⟨S.smoothStructure.property.1.1, ?_⟩
  intro e he d hd
  have h := S.smoothStructure.property.1.2 e he d hd
  have lower : ∀ (f : ModelSpace m a → ModelSpace m a) (s : Set (ModelSpace m a)),
      ContDiffOnModel (⊤ : ℕ∞) f s → ContDiffOnModel 1 f s := by
    intro f s hf x hx
    obtain ⟨U, hU, hxU, F, hF, heF⟩ := hf x hx
    refine ⟨U, hU, hxU, F, hF.of_le (by simp), heF⟩
  exact ⟨lower _ _ h.1, lower _ _ h.2⟩

section Maps
variable {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]

/-- Tangent coordinates identify the actual image of any differential with
its Jacobian image; they are isomorphisms even on the boundary. -/
theorem differential_chart_invariants
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N) (p : M)
    (F : FiberModel S.smoothStructure.val p)
    (G : FiberModel T.smoothStructure.val (f p))
    (e : ModelChart m a M) (d : ModelChart n b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ e.source) (hfp : f p ∈ d.source) :
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∀ (L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p)),
    IsCoordinateDifferential f p F G L →
    Module.finrank ℝ (LinearMap.range L) =
      Module.finrank ℝ (LinearMap.range (chartDerivative e d f p).toLinearMap) ∧
    (Function.Injective L ↔ Function.Injective (chartDerivative e d f p)) ∧
    (Function.Surjective L ↔ Function.Surjective (chartDerivative e d f p)) := by
  letI := F.group; letI := F.module; letI := G.group; letI := G.module
  intro L hL
  exact linear_invariants (F.coordinates e he hp) (G.coordinates d hd hfp)
    L (chartDerivative e d f p).toLinearMap (hL e d he hd hp hfp)

/-- This witness is constructed by the upstream quotient and differential
existence theorems; it is never assumed as part of manifold data. -/
theorem exists_differential_model
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f) (p : M) :
    ∃ (F : FiberModel S.smoothStructure.val p)
      (G : FiberModel T.smoothStructure.val (f p)),
    letI := F.group; letI := F.module; letI := G.group; letI := G.module
    ∃ L : CoordinateTangent S.smoothStructure.val p →ₗ[ℝ]
      CoordinateTangent T.smoothStructure.val (f p), IsCoordinateDifferential f p F G L := by
  obtain ⟨F⟩ := FiniteRegularity.fiberModel_exists 1 (by rfl) _ (smoothAtlas_contDiff_one S) p
  obtain ⟨G⟩ := FiniteRegularity.fiberModel_exists 1 (by rfl) _ (smoothAtlas_contDiff_one T) (f p)
  letI := F.group; letI := F.module; letI := G.group; letI := G.module
  obtain ⟨L, hL, _⟩ := FiniteRegularity.coordinateDifferential_exists 1 (by rfl)
    _ _ (smoothAtlas_contDiff_one S) (smoothAtlas_contDiff_one T) f hf p F G
  exact ⟨F, G, L, hL⟩

/-- Every possible image dimension is the rank of any legitimate Jacobian. -/
theorem hasRankAt_iff_chart
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f)
    (p : M) (e : ModelChart m a M) (d : ModelChart n b N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ e.source) (hfp : f p ∈ d.source) (k : ℕ) :
    HasRankAt S T f p k ↔
      Module.finrank ℝ (LinearMap.range (chartDerivative e d f p).toLinearMap) = k := by
  constructor
  · rintro ⟨F, G, L, hL, hk⟩
    exact (differential_chart_invariants S T f p F G e d he hd hp hfp L hL).1.symm.trans hk
  · intro hk
    obtain ⟨F, G, L, hL⟩ := exists_differential_model S T f hf p
    exact ⟨F, G, L, hL,
      (differential_chart_invariants S T f p F G e d he hd hp hfp L hL).1.trans hk⟩

theorem rank_exists_unique :
    Specs.SmoothManifolds.Ch03.MapClasses.rank_exists_uniqueType.{u,v} := by
  intro m n a b M N _ _ S T f hf p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  have h := hasRankAt_iff_chart S T f hf p e d he hd hp hfp
  exact ⟨_, (h _).mpr rfl, fun k hk => ((h k).mp hk).symm⟩

theorem chart_invariants :
    Specs.SmoothManifolds.Ch03.MapClasses.chart_invariantsType.{u,v} := by
  classical
  intro m n a b M N _ _ S T f hf p e d he hd hp hfp
  have hrank := hasRankAt_iff_chart S T f hf p e d he hd hp hfp
  obtain ⟨k, hk, _⟩ := rank_exists_unique S T f hf p
  have hex : ∃ k, HasRankAt S T f p k := ⟨k, hk⟩
  have hr : rankAt S T f p =
      Module.finrank ℝ (LinearMap.range (chartDerivative e d f p).toLinearMap) := by
    unfold MapClassData.rankAt
    rw [dite_eq_left hex]
    exact ((hrank _).mp (Nat.find_spec hex)).symm
  refine ⟨hr, ?_, ?_⟩
  · constructor
    · rintro ⟨_, F, G, L, hL, hinj⟩
      exact (differential_chart_invariants S T f p F G e d he hd hp hfp L hL).2.1.mp hinj
    · intro hinj
      obtain ⟨F, G, L, hL⟩ := exists_differential_model S T f hf p
      exact ⟨hf p, F, G, L, hL,
        (differential_chart_invariants S T f p F G e d he hd hp hfp L hL).2.1.mpr hinj⟩
  · constructor
    · rintro ⟨_, F, G, L, hL, hsurj⟩
      exact (differential_chart_invariants S T f p F G e d he hd hp hfp L hL).2.2.mp hsurj
    · intro hsurj
      obtain ⟨F, G, L, hL⟩ := exists_differential_model S T f hf p
      exact ⟨hf p, F, G, L, hL,
        (differential_chart_invariants S T f p F G e d he hd hp hfp L hL).2.2.mpr hsurj⟩

theorem full_tangent_invariants :
    Specs.SmoothManifolds.Ch03.MapClasses.full_tangent_invariantsType.{u,v} := by
  intro m n a b M N _ _ S T f hf p F G
  letI := F.group; letI := F.module; letI := G.group; letI := G.module
  intro L hL
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  have h := chart_invariants S T f hf p e d he hd hp hfp
  have h' := differential_chart_invariants S T f p F G e d he hd hp hfp L hL
  exact ⟨h.1.trans h'.1.symm, h.2.1.trans h'.2.1.symm, h.2.2.trans h'.2.2.symm⟩

theorem chart_change_invariants :
    Specs.SmoothManifolds.Ch03.MapClasses.chart_change_invariantsType.{u,v} := by
  intro m n a b M N _ _ S T f hf p e e' d d' he he' hd hd' hp hp' hfp hfp'
  have h := chart_invariants S T f hf p e d he hd hp hfp
  have h' := chart_invariants S T f hf p e' d' he' hd' hp' hfp'
  exact ⟨h.1.symm.trans h'.1, h.2.1.symm.trans h'.2.1, h.2.2.symm.trans h'.2.2⟩

theorem regularValue_empty_fiber :
    Specs.SmoothManifolds.Ch03.MapClasses.regularValue_empty_fiberType.{u,v} := by
  intro m n a b M N _ _ S T f y hy p hp
  exact (hy ⟨p, hp⟩).elim

end Maps

/-- For smooth maps, the same quantities are those of the germ-derivation
model of Chapter 2, under its established coordinate comparison. -/
theorem smooth_tangent_invariants :
    Specs.SmoothManifolds.Ch03.MapClasses.smooth_tangent_invariantsType.{u} := by
  intro m n a b M N _ _ S T f hf p L hL
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨E, hE⟩ := FiniteRegularity.exists_smooth_chart_coordinates S p e he hp
  obtain ⟨D, hD⟩ := FiniteRegularity.exists_smooth_chart_coordinates T (f p) d hd hfp
  have hsquare : ∀ v, D (L v) = (chartDerivative e d f p).toLinearMap (E v) :=
    FiniteRegularity.smooth_jacobian_coordinateDerivative S T f hf p L hL
      e d he hd hp hfp E D hE hD
  have hlin := linear_invariants (V := TangentData.TangentSpace S p)
    (W := TangentData.TangentSpace T (f p)) E D L
    (chartDerivative e d f p).toLinearMap hsquare
  have hf1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf
  have h := chart_invariants S T f hf1 p e d he hd hp hfp
  exact ⟨h.1.trans hlin.1.symm, h.2.1.trans hlin.2.1.symm, h.2.2.trans hlin.2.2.symm⟩

theorem embedded_is_immersed :
    Specs.SmoothManifolds.Ch03.MapClasses.embedded_is_immersedType.{v} := by
  intro n b N _ T s k a h
  obtain ⟨t, S, hsmooth, _, himm, _⟩ := h
  exact ⟨t, S, hsmooth, himm⟩

abbrev HasRankAt := @MapClassData.HasRankAt
noncomputable abbrev rankAt := @MapClassData.rankAt
abbrev IsImmersionAt := @MapClassData.IsImmersionAt
abbrev IsSubmersionAt := @MapClassData.IsSubmersionAt
abbrev IsImmersion := @MapClassData.IsImmersion
abbrev IsSubmersion := @MapClassData.IsSubmersion
abbrev IsSmoothEmbedding := @MapClassData.IsSmoothEmbedding
abbrev IsRegularValue := @MapClassData.IsRegularValue
abbrev IsProper := @MapClassData.IsProper
abbrev IsImmersedSubmanifold := @MapClassData.IsImmersedSubmanifold
abbrev IsEmbeddedSubmanifold := @MapClassData.IsEmbeddedSubmanifold

end SmoothManifolds.MapClasses
