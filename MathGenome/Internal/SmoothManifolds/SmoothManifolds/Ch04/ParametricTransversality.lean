import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.ParametricTransversality
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.Sard
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryRegularLevels

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.TransversePreimage
/-! Conditional work for M04.07. The transverse-preimage implementation is
intentionally not imported. Its three full propositions are explicit premises
of the public conditional helpers below. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false
namespace SmoothManifolds.ParametricTransversality
open ModelData AtlasData MapData BoundaryData MapClassData ProductData
  BoundaryRegularLevelData TransversePreimageData SardData
  ParametricTransversalityData TangentData DifferentialData Set Filter
open scoped Topology
universe u

/-- The corrected projection argument, expressed without choosing a quotient.
The tangent image J is exactly the inverse image of the target tangent H. -/
theorem projection_surjective_iff
    {X Y Z V : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup Z] [Module ℝ Z] [AddCommGroup V] [Module ℝ V]
    (L : (X × Y) →ₗ[ℝ] Z) (H : Submodule ℝ Z) (J : V →ₗ[ℝ] (X × Y))
    (hJ : LinearMap.range J = H.comap L)
    (hL : LinearMap.range L ⊔ H = ⊤) :
    Function.Surjective ((LinearMap.fst ℝ X Y).comp J) ↔
      LinearMap.range (L.comp (LinearMap.inr ℝ X Y)) ⊔ H = ⊤ := by
  constructor
  · intro hproj
    apply top_unique
    intro z _
    have hz : z ∈ LinearMap.range L ⊔ H := hL ▸ Submodule.mem_top
    obtain ⟨l, ⟨⟨x,y⟩, rfl⟩, h, hh, heq⟩ := Submodule.mem_sup.mp hz
    obtain ⟨v, hv⟩ := hproj x
    have hJv : L (J v) ∈ H := by
      change J v ∈ H.comap L
      rw [← hJ]
      exact LinearMap.mem_range_self J v
    refine Submodule.mem_sup.mpr
      ⟨L (0, y - (J v).2), ⟨y - (J v).2, rfl⟩,
        L (J v) + h, H.add_mem hJv hh, ?_⟩
    change (J v).1 = x at hv
    rw [← add_assoc, ← map_add]
    have hp : (0, y - (J v).2) + J v = (x,y) := by
      apply Prod.ext <;> simp [hv]
    rw [hp]
    exact heq
  · intro hslice x
    have hx : L (x,0) ∈ LinearMap.range (L.comp (LinearMap.inr ℝ X Y)) ⊔ H :=
      hslice ▸ Submodule.mem_top
    obtain ⟨_, ⟨y, rfl⟩, h, hh, heq⟩ := Submodule.mem_sup.mp hx
    have hxy : (x, -y) ∈ H.comap L := by
      change L (x,-y) ∈ H
      have he : L (x,-y) = h := by
        have hp : (x,-y) = (x,0) - (0,y) := by ext <;> simp
        rw [hp, map_sub, ← heq]
        change L (0,y) + h - L (0,y) = h
        abel
      rwa [he]
    rw [← hJ] at hxy
    obtain ⟨v, hv⟩ := hxy
    exact ⟨v, congrArg Prod.fst hv⟩

/-- Chart-null sets in dimension zero are empty, since their chart coordinates
carry counting measure. This does not require measurability of the null set. -/
theorem null_zero_iff_empty {a : ModelKind} {P : Type u} [TopologicalSpace P]
    (A : SmoothManifold 0 a P) (s : Set P) : IsNull A s ↔ s = ∅ := by
  constructor
  · intro hs
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨d, hd, hpd⟩ := A.smoothStructure.property.1.1 p
    have hz := hs d hd
    rw [Sard.coordinate_volume_zero_eq_count] at hz
    have hmem : (d p).val ∈ (fun y => (d y).val) '' (s ∩ d.source) :=
      ⟨p, ⟨hp, hpd⟩, rfl⟩
    have hsingle := MeasureTheory.measure_mono_null (singleton_subset_iff.mpr hmem) hz
    simp at hsingle
  · rintro rfl
    intro d hd
    simp

/-- Nullity is stable under a finite union with no measurable-set hypotheses. -/
theorem null_union {r : ℕ} {a : ModelKind} {P : Type u} [TopologicalSpace P]
    (A : SmoothManifold r a P) {s t : Set P}
    (hs : IsNull A s) (ht : IsNull A t) : IsNull A (s ∪ t) := by
  intro d hd
  rw [union_inter_distrib_right, image_union]
  exact MeasureTheory.measure_union_null (hs d hd) (ht d hd)

/-- Constant maps satisfy the same local ambient extension convention at faces. -/
theorem smooth_constant {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (y : N) :
    IsSmoothMap S T (fun _ => y) := by
  intro p
  refine ⟨continuousAt_const, ?_⟩
  intro e he d hd hp hyp
  exact ⟨univ, isOpen_univ, mem_univ _, fun _ => (d y).val,
    contDiffOn_const, Eventually.of_forall (fun _ => rfl)⟩

/-- A slice of a smooth product family is smooth, including at boundary points. -/
theorem smooth_slice {r m : ℕ} {a b q : ModelKind} {P M : Type u}
    [TopologicalSpace P] [TopologicalSpace M]
    (A : SmoothManifold r a P) (S : SmoothManifold m b M)
    (C : ProductCoordinates r a m b q)
    (Q : SmoothManifold (r + m) q (P × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C A.smoothStructure.val S.smoothStructure.val)) (p : P) :
    IsSmoothMap S Q (fun x => (p,x)) :=
  (differential_pair A S S C Q hQ (fun _ => p) id (smooth_constant S A p)
    (manifoldContDiff_id _ _ S.smoothStructure.property.1)).1



/-- Product boundary points are exactly the points in the boundary factor.
This works for every actual linear coordinate identification of the model. -/
theorem product_boundary_iff {r m : ℕ} {b q : ModelKind} {P M : Type u}
    [TopologicalSpace P] [TopologicalSpace M]
    (A : SmoothManifold r .euclidean P) (S : SmoothManifold m b M)
    (C : ProductCoordinates r .euclidean m b q)
    (Q : SmoothManifold (r + m) q (P × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C A.smoothStructure.val S.smoothStructure.val)) (z : P × M) :
    z ∈ intrinsicBoundary Q ↔ z.2 ∈ intrinsicBoundary S := by
  obtain ⟨e, he, hze⟩ := A.smoothStructure.property.1.1 z.1
  obtain ⟨d, hd, hzd⟩ := S.smoothStructure.property.1.1 z.2
  have hA := productAtlas_isContDiffAtlas C (⊤ : ℕ∞) _ _
    A.smoothStructure.property.1 S.smoothStructure.property.1
  have hchart : productChart C e d ∈ Q.smoothStructure.val := by
    rw [hQ]
    exact subset_maximalExtension hA ⟨e,he,d,hd,rfl⟩
  have hzchart : z ∈ (productChart C e d).source := by
    rw [productChart_source]; exact ⟨hze,hzd⟩
  rw [intrinsicBoundary_iff_chart Q _ hchart z hzchart,
    mem_modelFace_iff_not_mem_interior,
    intrinsicBoundary_iff_chart S d hd z.2 hzd,
    mem_modelFace_iff_not_mem_interior]
  have hset : C.linearEquiv ⁻¹' modelSet (r+m) q =
      (univ : Set (Euclidean r)) ×ˢ modelSet m b := by
    ext w
    simpa [modelSet, ModelData.modelSet] using C.mem_model w
  have h := C.linearEquiv.toHomeomorph.preimage_interior (modelSet (r+m) q)
  change C.linearEquiv ⁻¹' interior (modelSet (r+m) q) =
    interior (C.linearEquiv ⁻¹' modelSet (r+m) q) at h
  rw [hset, interior_prod_eq, interior_univ] at h
  have hz := Set.ext_iff.mp h ((e z.1).val, (d z.2).val)
  simpa only [productChart_val, mem_preimage, mem_prod, mem_univ, true_and] using
    not_congr hz

/-- At a regular value of the restricted parameter projection, the slice is
transverse. The proof uses the full tangent, even at a source boundary point. -/
theorem slice_transverse_of_regular_projection
    (hTangent : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u})
    {r m n k : ℕ} {a b c d q w : ModelKind} {P M N : Type u}
    [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace N]
    (A : SmoothManifold r a P) (S : SmoothManifold m b M)
    (T : SmoothManifold n c N) (s : Set N) (R : SmoothManifold k d s)
    (C : ProductCoordinates r a m b q)
    (Q : SmoothManifold (r+m) q (P × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C A.smoothStructure.val S.smoothStructure.val))
    (F : P × M → N) (hT : intrinsicBoundary T = ∅)
    (hR : intrinsicBoundary R = ∅) (hi : IsSmoothEmbedding R T Subtype.val)
    (hF : IsSmoothMap Q T F) (ht : IsTransverse Q T R F)
    (W : SmoothManifold (r+m-(n-k)) w (F ⁻¹' s))
    (hW : IsSmoothEmbedding W Q Subtype.val) (a₀ : P)
    (ha : IsRegularValue W A (fun z => z.val.1) a₀) :
    IsTransverse S T R (fun x => F (a₀,x)) := by
  intro x hx D I hD hI
  let z : F ⁻¹' s := ⟨(a₀,x), hx⟩
  obtain ⟨hfst, hsnd, hprod⟩ := differential_product A S C Q hQ
  obtain ⟨E, hEf, hEs⟩ := hprod z.val
  obtain ⟨L, hL, _⟩ := differential_exists Q T F hF z.val
  obtain ⟨K, hK, _⟩ := differential_exists W Q Subtype.val hW.1 z
  have hKr := (hTangent Q T s R F hT hR hi hF ht W hW z L I K hL hI hK).2
  have hπ := differential_comp W Q A Subtype.val Prod.fst hW.1 hfst z K
    ((LinearMap.fst ℝ _ _).comp E.toLinearMap) hK hEf
  have hπsmooth : IsSmoothMap W A (fun z => z.val.1) :=
    manifoldContDiff_comp _ _ _ _ Q.smoothStructure.property.1.1 _ _ hW.1 hfst
  have hπsurj : Function.Surjective
      (((LinearMap.fst ℝ _ _).comp E.toLinearMap).comp K) :=
    (MapClasses.smooth_tangent_invariants W A _ hπsmooth z _ hπ).2.2.mp (ha z rfl)
  have hj := smooth_slice A S C Q hQ a₀
  obtain ⟨Kj, hKj, _⟩ := differential_exists S Q (fun x => (a₀,x)) hj x
  have hpair := (differential_pair A S S C Q hQ (fun _ => a₀) id
    (smooth_constant S A a₀) (manifoldContDiff_id _ _ S.smoothStructure.property.1)).2
    x 0 LinearMap.id Kj E
    (BoundaryRegularLevels.constant_differential S A (fun _ => a₀) x (fun _ => rfl))
    (differential_id S x) hKj hEf hEs
  have hcomp := differential_comp S Q T (fun x => (a₀,x)) F hj hF x Kj L hKj hL
  have hs : IsSmoothMap S T (fun x => F (a₀,x)) :=
    manifoldContDiff_comp _ _ _ _ Q.smoothStructure.property.1.1 _ _ hj hF
  have hLD : L.comp Kj = D := (differential_exists S T _ hs x).unique hcomp hD
  apply top_unique
  intro t _
  have hfull := ht z.val hx L I hL hI
  have htmem : t ∈ LinearMap.range L ⊔ LinearMap.range I := hfull ▸ Submodule.mem_top
  obtain ⟨_,⟨v,rfl⟩,_,⟨vI,rfl⟩,heq⟩ := Submodule.mem_sup.mp htmem
  obtain ⟨vW,hproj⟩ := hπsurj (E v).1
  have hKW : L (K vW) ∈ LinearMap.range I := by
    change K vW ∈ (LinearMap.range I).comap L
    rw [← hKr]
    exact LinearMap.mem_range_self K vW
  obtain ⟨wI,hwI⟩ := hKW
  let vS := (E (v - K vW)).2
  have hsplit : Kj vS = v - K vW := by
    apply E.injective
    have hp := LinearMap.congr_fun hpair vS
    change E (Kj vS) = (0,vS) at hp
    rw [hp]
    apply Prod.ext
    · change (0 : TangentSpace A a₀) = (E (v - K vW)).1
      rw [map_sub E]
      change 0 = (E v).1 - (E (K vW)).1
      change (E (K vW)).1 = (E v).1 at hproj
      rw [hproj]
      exact (sub_self ((E v).1)).symm
    · rfl
  refine Submodule.mem_sup.mpr ⟨D vS,⟨vS,rfl⟩,I (wI+vI),⟨wI+vI,rfl⟩,?_⟩
  rw [← hLD]
  change L (Kj vS) + I (wI + vI) = t
  rw [hsplit,map_sub L,map_add I,hwI,← heq]
  abel




/-- Sard applied to the projection of the transverse inverse image. This core
lemma is valid with ordinary boundary; its boundary hypothesis is intrinsic. -/
theorem null_bad_slices
    (hDimension : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_dimensionType.{u})
    (hStructure : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_structureType.{u})
    (hTangent : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u})
    {r m n k : ℕ} {a b c d q : ModelKind} {P M N : Type u}
    [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace N]
    (A : SmoothManifold r a P) (S : SmoothManifold m b M)
    (T : SmoothManifold n c N) (s : Set N) (R : SmoothManifold k d s)
    (C : ProductCoordinates r a m b q)
    (Q : SmoothManifold (r+m) q (P × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C A.smoothStructure.val S.smoothStructure.val))
    (F : P × M → N) (hT : intrinsicBoundary T = ∅)
    (hR : intrinsicBoundary R = ∅) (hi : IsSmoothEmbedding R T Subtype.val)
    (hF : IsSmoothMap Q T F) (ht : IsTransverse Q T R F)
    (BQ : SmoothManifold (r+m-1) .euclidean (intrinsicBoundary Q))
    (hBQ : IsNaturalBoundaryStructure Q BQ)
    (htB : IsTransverse BQ T R (fun z => F z.val)) :
    ∃ bad : Set P, IsNull A bad ∧
      ∀ a₀, a₀ ∉ bad → IsTransverse S T R (fun x => F (a₀,x)) := by
  obtain ⟨W, hW, hboundary, hdim⟩ := hStructure Q T s R F BQ hT hR hi hF hBQ ht htB
  have hfst := (differential_product A S C Q hQ).1
  have hπ : IsSmoothMap W A (fun z => z.val.1) :=
    manifoldContDiff_comp _ _ _ _ Q.smoothStructure.property.1.1 _ _ hW.1 hfst
  refine ⟨criticalValues W A (fun z => z.val.1), Sard.sard W A _ hπ, ?_⟩
  intro a₀ ha
  apply slice_transverse_of_regular_projection hTangent A S T s R C Q hQ F
    hT hR hi hF ht W hW a₀
  intro z hza
  by_contra hz
  exact ha ⟨z,hz,hza⟩

/-- Smooth identity coordinates in equal dimension carry chart-null sets to
chart-null sets. Applied to the Euclidean representation of a parameter space. -/
theorem null_of_smooth_identity {r : ℕ} {a b : ModelKind} {P : Type u}
    [TopologicalSpace P] (A : SmoothManifold r a P) (E : SmoothManifold r b P)
    (hEA : IsSmoothMap E A id) (s : Set P) (hs : IsNull E s) : IsNull A s := by
  intro d hd
  apply Sard.compatible_chart_null E s hs d
  intro e he p hpe hpd
  exact (hEA p).2 e he d hd hpe hpd

/-- The inclusion P × ∂M → P × M is smooth for the actual product atlases. -/
theorem smooth_boundary_product_inclusion
    {r m : ℕ} {a b q : ModelKind} {P M : Type u}
    [TopologicalSpace P] [TopologicalSpace M]
    (A : SmoothManifold r a P) (S : SmoothManifold m b M)
    (B : SmoothManifold (m-1) .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B)
    (C : ProductCoordinates r a m b q) (Q : SmoothManifold (r+m) q (P × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C A.smoothStructure.val S.smoothStructure.val))
    (CB : ProductCoordinates r a (m-1) .euclidean a)
    (QB : SmoothManifold (r+(m-1)) a (P × intrinsicBoundary S))
    (hQB : QB.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas CB A.smoothStructure.val B.smoothStructure.val)) :
    IsSmoothMap QB Q (fun z => (z.1,z.2.val)) := by
  obtain ⟨hfst,hsnd,_⟩ := differential_product A B CB QB hQB
  have hs : IsSmoothMap QB S (fun z => z.2.val) :=
    manifoldContDiff_comp _ _ _ _ B.smoothStructure.property.1.1 _ _ hsnd hB.1
  exact (differential_pair A S QB C Q hQ _ _ hfst hs).1


/-- Boundary-family transversality implies transversality on the intrinsic
boundary of the product. Only the inclusion of tangent images is needed. -/
theorem transverse_product_boundary
    {r m n k : ℕ} {b c d q : ModelKind} {P M N : Type u}
    [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace N]
    (A : SmoothManifold r .euclidean P) (S : SmoothManifold m b M)
    (T : SmoothManifold n c N) (s : Set N) (R : SmoothManifold k d s)
    (B : SmoothManifold (m-1) .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B)
    (C : ProductCoordinates r .euclidean m b q) (Q : SmoothManifold (r+m) q (P × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C A.smoothStructure.val S.smoothStructure.val))
    (CB : ProductCoordinates r .euclidean (m-1) .euclidean .euclidean)
    (QB : SmoothManifold (r+(m-1)) .euclidean (P × intrinsicBoundary S))
    (hQB : QB.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas CB A.smoothStructure.val B.smoothStructure.val))
    (BQ : SmoothManifold (r+m-1) .euclidean (intrinsicBoundary Q))
    (hBQ : IsNaturalBoundaryStructure Q BQ)
    (F : P × M → N) (hF : IsSmoothMap Q T F)
    (htB : IsTransverse QB T R (fun z => F (z.1,z.2.val))) :
    IsTransverse BQ T R (fun z => F z.val) := by
  let j : P × intrinsicBoundary S → P × M := fun z => (z.1,z.2.val)
  have hj : IsSmoothMap QB Q j :=
    smooth_boundary_product_inclusion A S B hB C Q hQ CB QB hQB
  have hface : ∀ z, j z ∈ intrinsicBoundary Q := fun z =>
    (product_boundary_iff A S C Q hQ (j z)).mpr z.2.property
  have hFBQ : IsSmoothMap BQ T (fun z => F z.val) :=
    manifoldContDiff_comp _ _ _ _ Q.smoothStructure.property.1.1 _ _ hBQ.1 hF
  intro z hz D I hD hI
  let zB : P × intrinsicBoundary S :=
    (z.val.1, ⟨z.val.2, (product_boundary_iff A S C Q hQ z.val).mp z.property⟩)
  obtain ⟨L,hL,_⟩ := differential_exists Q T F hF z.val
  obtain ⟨K,hK,_⟩ := differential_exists BQ Q Subtype.val hBQ.1 z
  obtain ⟨J,hJ,_⟩ := differential_exists QB Q j hj zB
  have hrange : LinearMap.range J ≤ LinearMap.range K :=
    BoundaryRegularLevels.range_le_boundary_tangent Q BQ hBQ QB j hj hface zB K J hK hJ
  have hLK : IsDifferential BQ T (fun z => F z.val) z (L.comp K) :=
    differential_comp BQ Q T Subtype.val F hBQ.1 hF z K L hK hL
  have heq : L.comp K = D := (differential_exists BQ T _ hFBQ z).unique hLK hD
  have hLJ : IsDifferential QB T (fun z => F (z.1,z.2.val)) zB (L.comp J) :=
    differential_comp QB Q T j F hj hF zB J L hJ hL
  have htrans := htB zB hz (L.comp J) I hLJ hI
  have hle : LinearMap.range (L.comp J) ≤ LinearMap.range D := by
    rintro v ⟨v,rfl⟩
    obtain ⟨w,hw⟩ := hrange (LinearMap.mem_range_self J v)
    refine ⟨w,?_⟩
    rw [← heq]
    change L (K w) = L (J v)
    rw [hw]
  exact top_unique (htrans ▸ sup_le_sup_right hle _)

/-- Conditional M04.07, with exactly the frozen three premises in contract order.
This is a draft derivation; the original closed theorem is deliberately absent. -/
theorem parametric_transversality_conditional
    (hDimension : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_dimensionType.{u})
    (hStructure : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_structureType.{u})
    (hTangent : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u}) :
    Specs.SmoothManifolds.Ch04.ParametricTransversality.parametric_transversalityType.{u} := by
  intro r m n k a b c d q P M N _ _ _ A E S T s R B C Q CB QB F
    hA hAE hEA hB hQ hQB hT hR hi hF ht htB
  obtain ⟨BQ,hBQ⟩ := BoundaryRegularLevels.natural_boundary_exists Q
  have htBQ := transverse_product_boundary E S T s R B hB C Q hQ CB QB hQB BQ hBQ F hF htB
  obtain ⟨bad₁,hbad₁,hgood₁⟩ := null_bad_slices hDimension hStructure hTangent
    E S T s R C Q hQ F hT hR hi hF ht BQ hBQ htBQ
  have hj := smooth_boundary_product_inclusion E S B hB C Q hQ CB QB hQB
  have hFB : IsSmoothMap QB T (fun z => F (z.1,z.2.val)) :=
    manifoldContDiff_comp _ _ _ _ Q.smoothStructure.property.1.1 _ _ hj hF
  obtain ⟨BQB,hBQB⟩ := BoundaryRegularLevels.natural_boundary_exists QB
  have hempty : IsTransverse BQB T R (fun z => F (z.val.1,z.val.2.val)) := by
    intro z
    exact ((Set.ext_iff.mp (intrinsicBoundary_euclidean QB) z.val).mp z.property).elim
  obtain ⟨bad₂,hbad₂,hgood₂⟩ := null_bad_slices hDimension hStructure hTangent
    E B T s R CB QB hQB (fun z => F (z.1,z.2.val)) hT hR hi hFB htB BQB hBQB hempty
  have hbad : IsNull A (bad₁ ∪ bad₂) :=
    null_of_smooth_identity A E hEA _ (null_union E hbad₁ hbad₂)
  refine ⟨bad₁ ∪ bad₂,hbad,?_,?_⟩
  · intro hr
    subst r
    exact (null_zero_iff_empty A _).mp hbad
  · intro p hp
    exact ⟨hgood₁ p (fun h => hp (Or.inl h)),hgood₂ p (fun h => hp (Or.inr h))⟩



@[simp] theorem liftedEuclideanChart_source (n : ℕ) :
    (liftedEuclideanChart.{u} n).source = univ := rfl

@[simp] theorem liftedEuclideanChart_val (n : ℕ) (x : ULift.{u} (Euclidean n)) :
    ((liftedEuclideanChart n) x).val = x.down := rfl

/-- The lifted target is precisely ordinary Euclidean space: the canonical
homeomorphism down/up is smooth in both directions in the stipulated atlases.
This checks the target representation used in the translation statement. -/
theorem standardEuclidean_lift_diffeomorph {n : ℕ}
    (T : SmoothManifold n .euclidean (Euclidean n))
    (TL : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (hT : euclideanChart n ∈ T.smoothStructure.val)
    (hTL : liftedEuclideanChart n ∈ TL.smoothStructure.val) :
    ∃ h : Diffeomorph TL.smoothStructure.val T.smoothStructure.val,
      (∀ x, h.toEquiv x = x.down) ∧ (∀ x, h.toEquiv.symm x = ULift.up.{u} x) := by
  refine ⟨⟨Homeomorph.ulift.toEquiv,?_,?_⟩,fun _ => rfl,fun _ => rfl⟩
  · intro p
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      TL.smoothStructure.property.1 T.smoothStructure.property.1 _ p).mpr
    exact ⟨Homeomorph.ulift.continuous.continuousAt,liftedEuclideanChart n,hTL,
      euclideanChart n,hT,by simp,mem_univ _,
      LocalCoordinateExtension.self (⊤ : ℕ∞) (fun x : ULift.{u} (Euclidean n) => x.down) p⟩
  · intro p
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      T.smoothStructure.property.1 TL.smoothStructure.property.1 _ p).mpr
    exact ⟨Homeomorph.ulift.symm.continuous.continuousAt,euclideanChart n,hT,
      liftedEuclideanChart n,hTL,mem_univ _,by simp,
      LocalCoordinateExtension.self (⊤ : ℕ∞) (id : Euclidean n → Euclidean n) p⟩

/-- Transversality follows from a surjective full differential, independently
of the tangent space of the submanifold. -/
theorem transverse_of_submersion {m n k : ℕ} {a b c : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (s : Set N) (R : SmoothManifold k c s) (f : M → N)
    (hf : IsSmoothMap S T f) (hsub : ∀ x, IsSubmersionAt S T f x) :
    IsTransverse S T R f := by
  intro x hx L I hL hI
  have hLsurj := (MapClasses.smooth_tangent_invariants S T f hf x L hL).2.2.mp (hsub x)
  rw [LinearMap.range_eq_top.mpr hLsurj, top_sup_eq]

/-- A translation family has smooth local representatives whose derivative
is onto. The parameter block of the displayed derivative is the identity. -/
theorem translation_family_local
    {m n : ℕ} {a q : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M)
    (T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (hstd : liftedEuclideanChart n ∈ T.smoothStructure.val)
    (C : ProductCoordinates n .euclidean m a q)
    (Q : SmoothManifold (n+m) q (ULift.{u} (Euclidean n) × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C T.smoothStructure.val S.smoothStructure.val))
    (f : M → ULift.{u} (Euclidean n)) (hf : IsSmoothMap S T f)
    (z : ULift.{u} (Euclidean n) × M) :
    ∃ e ∈ Q.smoothStructure.val, z ∈ e.source ∧
    ∃ (U : Set (Euclidean (n+m))) (H : Euclidean (n+m) → Euclidean n)
      (D : Euclidean (n+m) →L[ℝ] Euclidean n),
      IsOpen U ∧ (e z).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) H U ∧
      (fun w => H (e w).val) =ᶠ[𝓝 z] (fun w => (f w.2).down + w.1.down) ∧
      HasFDerivAt H D (e z).val ∧ Function.Surjective D := by
  obtain ⟨d,hd,hzd⟩ := S.smoothStructure.property.1.1 z.2
  let e₀ := liftedEuclideanChart.{u} n
  obtain ⟨V,hV,hzdV,G,hG,heq⟩ :=
    (hf z.2).2 d hd e₀ hstd hzd (by simp [e₀])
  let e := productChart C e₀ d
  have hA := productAtlas_isContDiffAtlas C (⊤ : ℕ∞) _ _
    T.smoothStructure.property.1 S.smoothStructure.property.1
  have he : e ∈ Q.smoothStructure.val := by
    rw [hQ]; exact subset_maximalExtension hA ⟨e₀,hstd,d,hd,rfl⟩
  have hze : z ∈ e.source := by
    rw [productChart_source]; exact ⟨by simp [e₀],hzd⟩
  let fstC : Euclidean (n+m) →L[ℝ] Euclidean n :=
    (ContinuousLinearMap.fst ℝ _ _).comp C.linearEquiv.symm.toContinuousLinearMap
  let sndC : Euclidean (n+m) →L[ℝ] Euclidean m :=
    (ContinuousLinearMap.snd ℝ _ _).comp C.linearEquiv.symm.toContinuousLinearMap
  have hfstC (w) : fstC ((e w).val) = w.1.down := by
    simp [fstC,e,e₀,productChart_val]
  have hsndC (w) : sndC ((e w).val) = (d w.2).val := by
    simp [sndC,e,productChart_val]
  let U := sndC ⁻¹' V
  let H := fun t => G (sndC t) + fstC t
  let D := (fderiv ℝ G (d z.2).val).comp sndC + fstC
  have hU : IsOpen U := hV.preimage sndC.continuous
  have hzU : (e z).val ∈ U := by change sndC ((e z).val) ∈ V; rwa [hsndC]
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H U :=
    (hG.comp sndC.contDiff.contDiffOn (fun _ h => h)).add fstC.contDiff.contDiffOn
  have hrep : (fun w => H (e w).val) =ᶠ[𝓝 z]
      (fun w => (f w.2).down + w.1.down) := by
    have heq' := heq.comp_tendsto (continuous_snd.continuousAt : ContinuousAt Prod.snd z)
    filter_upwards [heq'] with w hw
    change G (d w.2).val = (f w.2).down at hw
    change G (sndC ((e w).val)) + fstC ((e w).val) = _
    rw [hsndC,hfstC,hw]
  have hGD : HasFDerivAt G (fderiv ℝ G (d z.2).val) (d z.2).val :=
    ((hG.contDiffAt (hV.mem_nhds hzdV)).differentiableAt (by simp)).hasFDerivAt
  have hHD : HasFDerivAt H D (e z).val := by
    have hGD' : HasFDerivAt G (fderiv ℝ G (d z.2).val) (sndC (e z).val) := by
      rwa [hsndC]
    exact (hGD'.comp _ sndC.hasFDerivAt).add fstC.hasFDerivAt
  refine ⟨e,he,hze,U,H,D,hU,hzU,hH,hrep,hHD,?_⟩
  intro y
  refine ⟨C.linearEquiv (y,0),?_⟩
  simp [D,fstC,sndC]

/-- Smoothness and submersivity of the translation family, without conditions
on the source boundary. The same result applies to its boundary restriction. -/
theorem translation_family_submersion
    {m n : ℕ} {a q : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M)
    (T : SmoothManifold n .euclidean (ULift.{u} (Euclidean n)))
    (hstd : liftedEuclideanChart n ∈ T.smoothStructure.val)
    (C : ProductCoordinates n .euclidean m a q)
    (Q : SmoothManifold (n+m) q (ULift.{u} (Euclidean n) × M))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C T.smoothStructure.val S.smoothStructure.val))
    (f : M → ULift.{u} (Euclidean n)) (hf : IsSmoothMap S T f) :
    IsSmoothMap Q T (fun z => ULift.up.{u} ((f z.2).down + z.1.down)) ∧
      ∀ z, IsSubmersionAt Q T (fun z => ULift.up.{u} ((f z.2).down + z.1.down)) z := by
  let F : ULift.{u} (Euclidean n) × M → ULift.{u} (Euclidean n) :=
    fun z => ULift.up ((f z.2).down + z.1.down)
  have hc : Continuous F := Homeomorph.ulift.symm.continuous.comp
    ((Homeomorph.ulift.continuous.comp
      ((RegularLevels.smoothMap_continuous S T f hf).comp continuous_snd)).add
      (Homeomorph.ulift.continuous.comp continuous_fst))
  have hF : IsSmoothMap Q T F := by
    intro z
    obtain ⟨e,he,hze,U,H,D,hU,hzU,hH,hrep,hD,hDs⟩ :=
      translation_family_local S T hstd C Q hQ f hf z
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      Q.smoothStructure.property.1 T.smoothStructure.property.1 F z).mpr
    exact ⟨hc.continuousAt,e,he,liftedEuclideanChart n,hstd,hze,by simp,
      U,hU,hzU,H,hH,hrep⟩
  refine ⟨hF,?_⟩
  intro z
  obtain ⟨e,he,hze,U,H,D,hU,hzU,hH,hrep,hD,hDs⟩ :=
    translation_family_local S T hstd C Q hQ f hf z
  have heq : FiniteRegularityData.chartDerivative e (liftedEuclideanChart n) F z = D :=
    FiniteRegularity.coordinateDerivative_eq e _ z hze D ⟨H,hD,hrep⟩
  apply (MapClasses.chart_invariants Q T F
    (manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ F (by simp) hF)
    z e (liftedEuclideanChart n) he hstd hze (by simp)).2.2.mpr
  rwa [heq]



/-- The translation example of paper.tex:1261, under the exact three frozen
premises. The closed original theorem is reserved for dependency closure. -/
theorem translation_perturbation_conditional
    (hDimension : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_dimensionType.{u})
    (hStructure : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_structureType.{u})
    (hTangent : Specs.SmoothManifolds.Ch04.TransversePreimage.transverse_preimage_tangentType.{u}) :
    Specs.SmoothManifolds.Ch04.ParametricTransversality.translation_perturbationType.{u} := by
  intro m n k a c M _ S T s R B f hstd hR hi hB hf ε hε
  obtain ⟨C,Q,_,hQ⟩ := exists_ordinaryProduct_smoothManifold T S (Or.inl rfl)
  obtain ⟨CB⟩ := exists_euclidean_productCoordinates n (m-1)
  obtain ⟨QB,_,hQB⟩ := exists_product_smoothManifold T B CB
  have hsub := translation_family_submersion S T hstd C Q hQ f hf
  have ht := transverse_of_submersion Q T s R _ hsub.1 hsub.2
  have hfB : IsSmoothMap B T (fun x => f x.val) :=
    manifoldContDiff_comp _ _ _ _ S.smoothStructure.property.1.1 _ _ hB.1 hf
  have hsubB := translation_family_submersion B T hstd CB QB hQB _ hfB
  have htB := transverse_of_submersion QB T s R _ hsubB.1 hsubB.2
  have hid := manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1
  obtain ⟨bad,hbad,hzero,hgood⟩ := parametric_transversality_conditional
    hDimension hStructure hTangent T T S T s R B C Q CB QB _
    (intrinsicBoundary_euclidean T) hid hid hB hQ hQB
    (intrinsicBoundary_euclidean T) hR hi hsub.1 ht htB
  let U : Set (ULift.{u} (Euclidean n)) :=
    ULift.down ⁻¹' Metric.ball (0 : Euclidean n) ε
  have hU : IsOpen U := Metric.isOpen_ball.preimage Homeomorph.ulift.continuous
  have hUn : U.Nonempty := ⟨ULift.up 0, by simpa [U,Metric.mem_ball] using hε⟩
  obtain ⟨p,hpU,hpbad⟩ :=
    dense_iff_inter_open.mp (Sard.null_complement_dense T bad hbad) U hU hUn
  have hp := hgood p hpbad
  have hj := smooth_slice T S C Q hQ p
  have hfs : IsSmoothMap S T (fun x => ULift.up.{u} ((f x).down + p.down)) :=
    manifoldContDiff_comp _ _ _ _ Q.smoothStructure.property.1.1 _ _ hj hsub.1
  refine ⟨p.down,?_,hfs,hp.1,hp.2,?_,?_,?_⟩
  · simpa [U,Metric.mem_ball,dist_zero_right] using hpU
  · exact Homeomorph.ulift.symm.continuous.comp
      ((Homeomorph.ulift.continuous.comp
        ((RegularLevels.smoothMap_continuous S T f hf).comp continuous_snd)).add
        (continuous_fst.smul continuous_const))
  · intro x; simp
  · intro x; simp

end SmoothManifolds.ParametricTransversality

universe v8_closure_12cad59f1d41d936_u0
theorem _root_.«SmoothManifolds».«ParametricTransversality».«parametric_transversality» : _root_.«Specs».«SmoothManifolds».«Ch04».«ParametricTransversality».«parametric_transversalityType».{v8_closure_12cad59f1d41d936_u0} :=
  @_root_.«SmoothManifolds».«ParametricTransversality».«parametric_transversality_conditional».{v8_closure_12cad59f1d41d936_u0} (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_dimension».{v8_closure_12cad59f1d41d936_u0}) (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_structure».{v8_closure_12cad59f1d41d936_u0}) (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_tangent».{v8_closure_12cad59f1d41d936_u0})
theorem _root_.«SmoothManifolds».«ParametricTransversality».«translation_perturbation» : _root_.«Specs».«SmoothManifolds».«Ch04».«ParametricTransversality».«translation_perturbationType».{v8_closure_12cad59f1d41d936_u0} :=
  @_root_.«SmoothManifolds».«ParametricTransversality».«translation_perturbation_conditional».{v8_closure_12cad59f1d41d936_u0} (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_dimension».{v8_closure_12cad59f1d41d936_u0}) (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_structure».{v8_closure_12cad59f1d41d936_u0}) (@_root_.«SmoothManifolds».«TransversePreimage».«transverse_preimage_tangent».{v8_closure_12cad59f1d41d936_u0})
