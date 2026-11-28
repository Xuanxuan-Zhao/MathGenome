import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ShortWindowTopology
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

namespace RepTheorySurvey.Geometric.ShortWindowTopology

open LatticeModelSpecs BoundedLatticeSpecs ShortWindowTopologySpecs
open Topology

noncomputable section

private abbrev Upper (a : ℤ) := (scalarLattice 2 a).val

private theorem comap_subtype_inclusion {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (U V P : Submodule R M) (h : U ≤ V) :
    (P.comap V.subtype).comap (Submodule.inclusion h) = P.comap U.subtype :=
  Submodule.ext fun _ ↦ Iff.rfl

private theorem lower_comap (m : ℕ) :
    (windowLower 2 (-(m : ℤ)) (2 * m)).comap (upperInclusion m) = windowLower 2 0 m :=
  calc
    _ = (Upper (-(m : ℤ) + ((2 * m : ℕ) : ℤ))).comap (Upper 0).subtype :=
      @comap_subtype_inclusion O (Coordinates 2) _ _ _ (Upper 0) (Upper (-(m : ℤ)))
        _ (standard_le_symmetricUpper m)
    _ = _ := congrArg (fun a : ℤ ↦ (Upper a).comap (Upper 0).subtype)
      ((boundedExponent m).trans (zero_add (m : ℤ)).symm)

private def windowEmbedding (m : ℕ) : Window 2 0 m →ₗ[O] BoundedWindow 2 m :=
  @Submodule.mapQ O (Upper 0 : Type) inferInstance inferInstance inferInstance (windowLower 2 0 m)
    O (Upper (-(m : ℤ)) : Type) inferInstance inferInstance inferInstance
    (RingHom.id O) (windowLower 2 (-(m : ℤ)) (2 * m)) (upperInclusion m) (lower_comap m).ge

private theorem windowEmbedding_quotient (m : ℕ) (x : Upper 0) :
    windowEmbedding m (windowQuotient 0 m x) =
      windowQuotient (-(m : ℤ)) (2 * m) (upperInclusion m x) := rfl

private abbrev windowEmbeddingComplex (m : ℕ) :
    Window 2 0 m →ₗ[ℂ] BoundedWindow 2 m :=
  (windowEmbedding m).restrictScalars ℂ

private theorem windowQuotient_surjective (a : ℤ) (m : ℕ) :
    Function.Surjective (windowQuotient a m) :=
  @Submodule.mkQ_surjective O (Upper a : Type)
    inferInstance inferInstance inferInstance (windowLower 2 a m)

private theorem windowEmbedding_range (m : ℕ) :
    (windowEmbeddingComplex m).range = standardSupport m := by
  ext z
  change (∃ w, windowEmbedding m w = z) ↔
    ∃ x : Upper (-(m : ℤ)), x.val ∈ Upper 0 ∧ windowQuotient (-(m : ℤ)) (2 * m) x = z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := windowQuotient_surjective 0 m w
    exact ⟨upperInclusion m x, x.property, (windowEmbedding_quotient m x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨windowQuotient 0 m ⟨x.val, hx⟩, windowEmbedding_quotient m _⟩

private theorem windowEmbedding_operator (m : ℕ) (w : Window 2 0 m) :
    windowEmbeddingComplex m (windowOperator 2 0 m w) =
      windowOperator 2 (-(m : ℤ)) (2 * m) (windowEmbeddingComplex m w) := by
  change windowEmbedding m (t • w) = t • windowEmbedding m w
  exact (windowEmbedding m).map_smul t w

private theorem latticeSubspace_map_windowEmbedding {m : ℕ} {L : GL2Lattice}
    (hL : L.val ≤ Upper 0) :
    (latticeSubspace 0 m L).map (windowEmbeddingComplex m) =
      latticeSubspace (-(m : ℤ)) (2 * m) L := by
  ext z
  change (∃ w, w ∈ latticeSubspace 0 m L ∧ windowEmbedding m w = z) ↔
    ∃ y : Upper (-(m : ℤ)), y.val ∈ L.val ∧ windowQuotient (-(m : ℤ)) (2 * m) y = z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ∃ x : Upper 0, x.val ∈ L.val ∧ windowQuotient 0 m x = w at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨upperInclusion m x, hx, (windowEmbedding_quotient m x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    let x : Upper 0 := ⟨y.val, hL hy⟩
    exact ⟨windowQuotient 0 m x, ⟨x, hy, rfl⟩, windowEmbedding_quotient m x⟩

private theorem upperInclusion_shiftedCoordinates (m : ℕ) (x : Fin 2 → O) :
    upperInclusion m (shiftedCoordinates 2 0 x) =
      shiftedCoordinates 2 (-(m : ℤ)) (t ^ m • x) := by
  apply Subtype.ext
  change shiftedInclusion 2 0 x = shiftedInclusion 2 (-(m : ℤ)) (t ^ m • x)
  simpa only [neg_add_cancel] using shiftedInclusion_add_nat 2 (-(m : ℤ)) m x

set_option backward.isDefEq.respectTransparency false in
private theorem windowCoordinates_quotient (a : ℤ) (m : ℕ) (x : Fin 2 → O)
    (i : Fin 2) (j : Fin m) :
    windowCoordinates 2 a m (windowQuotient a m (shiftedCoordinates 2 a x)) (i, j) =
      PowerSeries.coeff j.val (x i) := by
  change jetCoefficients m
    (jetReduction m ((shiftedCoordinates 2 a).symm (shiftedCoordinates 2 a x) i)) j = _
  rw [LinearEquiv.symm_apply_apply, jetCoefficients_reduce]

private theorem windowCoordinates_embedding_quotient (m : ℕ) (x : Fin 2 → O)
    (i : Fin 2) (j : Fin (2 * m)) :
    windowCoordinates 2 (-(m : ℤ)) (2 * m)
      (windowEmbedding m (windowQuotient 0 m (shiftedCoordinates 2 0 x))) (i, j) =
        PowerSeries.coeff j.val (t ^ m * x i) := by
  rw [windowEmbedding_quotient, upperInclusion_shiftedCoordinates, windowCoordinates_quotient]
  rfl

private theorem windowEmbedding_coordinate_zero (m : ℕ) (w : Window 2 0 m)
    (i : Fin 2) (j : Fin (2 * m)) (hj : j.val < m) :
    windowCoordinates 2 (-(m : ℤ)) (2 * m) (windowEmbedding m w) (i, j) = 0 := by
  obtain ⟨x, rfl⟩ := ((windowQuotient_surjective 0 m).comp (shiftedCoordinates 2 0).surjective) w
  change windowCoordinates 2 (-(m : ℤ)) (2 * m)
    (windowEmbedding m (windowQuotient 0 m (shiftedCoordinates 2 0 x))) (i, j) = 0
  rw [windowCoordinates_embedding_quotient, PowerSeries.coeff_X_pow_mul',
    ite_eq_right (Nat.not_le_of_lt hj)]

private theorem windowEmbedding_coordinate_shift (m : ℕ) (w : Window 2 0 m)
    (ij : Fin 2 × Fin m) :
    windowCoordinates 2 (-(m : ℤ)) (2 * m) (windowEmbedding m w) (windowIndexEmbedding m ij) =
      windowCoordinates 2 0 m w ij := by
  obtain ⟨x, rfl⟩ := ((windowQuotient_surjective 0 m).comp (shiftedCoordinates 2 0).surjective) w
  obtain ⟨i, j⟩ := ij
  change windowCoordinates 2 (-(m : ℤ)) (2 * m)
    (windowEmbedding m (windowQuotient 0 m (shiftedCoordinates 2 0 x)))
      (i, (windowIndexEmbedding m (i, j)).2) =
    windowCoordinates 2 0 m (windowQuotient 0 m (shiftedCoordinates 2 0 x)) (i, j)
  rw [windowCoordinates_embedding_quotient, windowCoordinates_quotient]
  change PowerSeries.coeff (m + j.val) (t ^ m * x i) = _
  rw [Nat.add_comm m j.val, PowerSeries.coeff_X_pow_mul]

private theorem windowEmbedding_injective (m : ℕ) : Function.Injective (windowEmbedding m) := by
  intro u v huv
  apply (windowCoordinates 2 0 m).injective
  funext ij
  rw [← windowEmbedding_coordinate_shift m u ij, ← windowEmbedding_coordinate_shift m v ij, huv]

theorem windowLinearComparison : WindowLinearComparison := by
  intro m _
  exact ⟨windowEmbedding m, windowEmbedding_quotient m, windowEmbedding_injective m,
    windowEmbedding_range m, windowEmbedding_operator m,
    fun L ↦ latticeSubspace_map_windowEmbedding L.property.2,
    windowEmbedding_coordinate_zero m, windowEmbedding_coordinate_shift m⟩

open Set

/-- Closed sets in a bounded stage have closed image in the union, as tested in
each other stage via the common stage at the maximum of the two bounds. -/
private theorem closedEmbedding_into_union {X : Type} {B : ℕ → Type}
    [∀ n, TopologicalSpace (B n)] (ι : ∀ n, B n → X)
    (hinj : ∀ n, Function.Injective (ι n))
    (j : ∀ {n m : ℕ}, n ≤ m → B n → B m)
    (hclosed : ∀ n m (h : n ≤ m), IsClosedEmbedding (j h))
    (hcomm : ∀ n m (h : n ≤ m) x, ι m (j h x) = ι n x) (n : ℕ) :
    @IsClosedEmbedding _ _ inferInstance
      (⨆ k : ℕ, TopologicalSpace.coinduced (ι k) inferInstance) (ι n) := by
  let : TopologicalSpace X := ⨆ k : ℕ, TopologicalSpace.coinduced (ι k) inferInstance
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_iSup_rng (i := n) continuous_coinduced_rng) (hinj n) ?_
  intro S hS
  rw [isClosed_iSup_iff]
  intro m
  rw [isClosed_coinduced]
  let k := max n m
  let f := j (le_max_left n m)
  let g := j (le_max_right n m)
  have hpreimage : ι m ⁻¹' (ι n '' S) = g ⁻¹' (f '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      exact ⟨y, hy, hinj k (by rwa [hcomm, hcomm])⟩
    · rintro ⟨y, hy, heq⟩
      exact ⟨y, hy, by simpa only [f, g, hcomm] using congrArg (ι k) heq⟩
  rw [hpreimage]
  exact ((hclosed n k (le_max_left n m)).isClosedMap _ hS).preimage
    (hclosed m k (le_max_right n m)).continuous

set_option maxHeartbeats 1000000 in
private theorem boundedVal_closedEmbedding (n : ℕ) :
    @IsClosedEmbedding (BoundedLattice 2 n) GL2Lattice
      (boundedAnalyticTopology 2 n) (latticeAnalyticTopology 2) Subtype.val :=
  @closedEmbedding_into_union GL2Lattice (BoundedLattice 2) (boundedAnalyticTopology 2)
    (fun _ ↦ Subtype.val)
    (fun _ ↦ Subtype.val_injective) (fun h ↦ boundedInclusion h)
    (BoundedLattices.boundedInclusionTopology 2) (fun _ _ _ _ ↦ rfl) n

private theorem boundedPoint_embedding (m : ℕ) :
    IsEmbedding (boundedPoint (r := 2) (N := m)) :=
  IsEmbedding.induced (BoundedLattices.boundedStageComparison 2 m).1.injective

private theorem shortAsBounded_embedding (m : ℕ) :
    IsEmbedding (shortAsBounded (m := m)) :=
  (boundedVal_closedEmbedding m).isEmbedding.of_comp_iff.mp
    (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : ShortLattice m → GL2Lattice))

private theorem windowQuotient_eq {a : ℤ} {n : ℕ} (x y : Upper a) :
    windowQuotient a n x = windowQuotient a n y ↔ x - y ∈ windowLower 2 a n :=
  @Submodule.Quotient.eq O (Upper a : Type) inferInstance inferInstance inferInstance
    (windowLower 2 a n) x y

private theorem boundedSubspace_le_support {m : ℕ} (L : BoundedLattice 2 m) :
    boundedSubspace L ≤ standardSupport m ↔ L.val.val ≤ Upper 0 := by
  constructor
  · intro h x hx
    let u : Upper (-(m : ℤ)) := ⟨x, L.property.2 hx⟩
    have hu : windowQuotient (-(m : ℤ)) (2 * m) u ∈ boundedSubspace L := ⟨u, hx, rfl⟩
    have hmem := h hu
    change ∃ y : Upper (-(m : ℤ)), y.val ∈ Upper 0 ∧
      windowQuotient (-(m : ℤ)) (2 * m) y = windowQuotient (-(m : ℤ)) (2 * m) u at hmem
    obtain ⟨y, hy, hqy⟩ := hmem
    have hdiff := (windowQuotient_eq u y).mp hqy.symm
    change x - y.val ∈ Upper (-(m : ℤ) + ((2 * m : ℕ) : ℤ)) at hdiff
    have hlower : Upper (-(m : ℤ) + ((2 * m : ℕ) : ℤ)) ≤ Upper 0 :=
      (congrArg Upper (boundedExponent m)).le.trans
        (diagonalLattice_le (fun _ ↦ Int.natCast_nonneg m))
    have hsum := (Upper 0).add_mem (hlower hdiff) hy
    rwa [sub_add_cancel] at hsum
  · intro h z hz
    change ∃ y : Upper (-(m : ℤ)), y.val ∈ L.val.val ∧
      windowQuotient (-(m : ℤ)) (2 * m) y = z at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, h hy, rfl⟩

private theorem boundedSubspace_finrank {m : ℕ} {L : BoundedLattice 2 m}
    (hL : L.val.val ≤ Upper 0) :
    Module.finrank ℂ (boundedSubspace L) = Module.finrank ℂ (latticeSubspace 0 m L.val) := by
  have heq := latticeSubspace_map_windowEmbedding (m := m) hL
  change (latticeSubspace 0 m L.val).map (windowEmbeddingComplex m) = boundedSubspace L at heq
  rw [← heq]
  exact ((latticeSubspace 0 m L.val).equivMapOfInjective
    (windowEmbeddingComplex m) (windowEmbedding_injective m)).finrank_eq.symm

private theorem boundedPoint_subspace {m : ℕ} (L : BoundedLattice 2 m) :
    windowStageSubspace (boundedPoint L) = boundedSubspace L :=
  (BoundedLattices.boundedStageComparison 2 m).2 L

private theorem stageSubspace_finrank {m : ℕ} (p : BoundedStage 2 m) :
    Module.finrank ℂ (windowStageSubspace p) = p.1.val :=
  grassmannianSubspace_finrank _ _ _

private def supportedToStage (m : ℕ) (p : SupportedStablePoints m) : BoundedStage 2 m :=
  ⟨symmetricDimension m, p.val⟩

private theorem supportedToStage_embedding (m : ℕ) : IsEmbedding (supportedToStage m) := by
  let : ∀ d : WindowDimension 2 (-(m : ℤ)) (2 * m), TopologicalSpace
      (StablePoints (windowBasis 2 (-(m : ℤ)) (2 * m)) (windowDimension_le d)
        (windowOperator 2 (-(m : ℤ)) (2 * m))) :=
    fun d ↦ stablePointsTopology _ (windowDimension_le d) _
  exact IsEmbedding.sigmaMk.comp IsEmbedding.subtypeVal

private theorem mem_range_supportedToStage {m : ℕ} (p : BoundedStage 2 m) :
    p ∈ range (supportedToStage m) ↔
      p.1 = symmetricDimension m ∧ windowStageSubspace p ≤ standardSupport m := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨rfl, q.property⟩
  · rcases p with ⟨d, p⟩
    rintro ⟨h, hp⟩
    change d = symmetricDimension m at h
    subst d
    exact ⟨⟨p, hp⟩, rfl⟩

private theorem boundedPoint_mem_range_iff {m : ℕ} (L : BoundedLattice 2 m) :
    boundedPoint L ∈ range (supportedToStage m) ↔
      L.val.val ≤ Upper 0 ∧ Module.finrank ℂ (latticeSubspace 0 m L.val) = m := by
  rw [mem_range_supportedToStage, boundedPoint_subspace, boundedSubspace_le_support]
  have hrank : Module.finrank ℂ (boundedSubspace L) = (boundedPoint L).1.val :=
    (congrArg (fun P : Submodule ℂ (BoundedWindow 2 m) ↦ Module.finrank ℂ P)
      (boundedPoint_subspace L)).symm.trans (stageSubspace_finrank (boundedPoint L))
  constructor
  · rintro ⟨hd, hL⟩
    refine ⟨hL, ?_⟩
    rw [← boundedSubspace_finrank hL, hrank, hd]
    rfl
  · rintro ⟨hL, hd⟩
    refine ⟨Fin.ext ?_, hL⟩
    rw [← hrank, boundedSubspace_finrank hL, hd]
    rfl

theorem shortWindowHomeomorphism : ShortWindowHomeomorphism := by
  intro m _
  classical
  have hpoint (L : ShortLattice m) : boundedPoint (shortAsBounded L) ∈ range (supportedToStage m) :=
    (boundedPoint_mem_range_iff (shortAsBounded L)).mpr L.property.2
  choose f hf using hpoint
  have hemb : IsEmbedding f := by
    apply (supportedToStage_embedding m).of_comp_iff.mp
    have hcomp : supportedToStage m ∘ f = boundedPoint ∘ shortAsBounded (m := m) := funext hf
    rw [hcomp]
    exact (boundedPoint_embedding m).comp (shortAsBounded_embedding m)
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨L, hL⟩ :=
      (BoundedLattices.boundedStageComparison 2 m).1.surjective (supportedToStage m p)
    have h : boundedPoint L ∈ range (supportedToStage m) := ⟨p, hL.symm⟩
    let L' : ShortLattice m := ⟨L.val, L.property.1, (boundedPoint_mem_range_iff L).mp h⟩
    have hbound : shortAsBounded L' = L := Subtype.ext rfl
    refine ⟨L', (supportedToStage_embedding m).injective ?_⟩
    rw [hf, hbound, hL]
  let e := hemb.toHomeomorphOfSurjective hsurj
  refine ⟨e, hf, fun L ↦ ?_⟩
  change windowStageSubspace (supportedToStage m (f L)) = boundedSubspace (shortAsBounded L)
  rw [hf, boundedPoint_subspace]

end

end RepTheorySurvey.Geometric.ShortWindowTopology
