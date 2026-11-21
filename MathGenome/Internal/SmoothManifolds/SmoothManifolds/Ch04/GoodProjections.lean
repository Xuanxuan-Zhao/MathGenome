import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.GoodProjections
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.FiniteRegularity
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.Sard
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.RealProjectiveSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

namespace SmoothManifolds.GoodProjections
open ModelData AtlasData MapData FiniteRegularityData GoodProjectionData
  ProjectiveData SphereTorusData Set Filter
open scoped BigOperators Topology ContDiff
universe u

@[simp] theorem directionSubmodule_projection {d : ℕ} (x : Sphere d) :
    directionSubmodule (projectiveProjection x) = Submodule.span ℝ {x.val} := rfl

@[simp] theorem projection_apply_representative {d : ℕ} (x : Sphere d)
    (z : Euclidean (d + 1)) :
    projection (projectiveProjection x) z = z - (∑ i, x.val i * z i) • x.val := rfl

/-- The definition uses the ordinary orthogonal projection along the represented
line, not merely some map preserving injectivity. -/
theorem projection_eq_zero_iff {d : ℕ} (L : RealProjectiveSpace d)
    (z : Euclidean (d + 1)) :
    projection L z = 0 ↔ z ∈ directionSubmodule L := by
  induction L using Quotient.inductionOn with
  | h x =>
    change projection (projectiveProjection x) z = 0 ↔
      z ∈ directionSubmodule (projectiveProjection x)
    rw [projection_apply_representative, directionSubmodule_projection, sub_eq_zero,
      Submodule.mem_span_singleton]
    constructor
    · intro h
      exact ⟨_, h.symm⟩
    · rintro ⟨c, rfl⟩
      have hx : ∑ i, x.val i * x.val i = 1 := by
        simpa only [squareSum, pow_two] using x.property
      have heq : ∑ i, x.val i * (c • x.val) i = c := by
        simp only [Pi.smul_apply, smul_eq_mul]
        simp_rw [← mul_assoc, mul_comm (x.val _) c, mul_assoc]
        rw [← Finset.mul_sum, hx, mul_one]
      rw [heq]

/-- The range lies in the canonical orthogonal-complement model. -/
theorem projection_orthogonal {d : ℕ} (x : Sphere d) (z : Euclidean (d + 1)) :
    ∑ i, x.val i * projection (projectiveProjection x) z i = 0 := by
  rw [projection_apply_representative]
  have hx : ∑ i, x.val i * x.val i = 1 := by
    simpa only [squareSum, pow_two] using x.property
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  simp_rw [← mul_assoc, mul_comm (x.val _) (∑ i, x.val i * z i), mul_assoc]
  rw [← Finset.mul_sum, hx, mul_one, sub_self]

theorem projection_fixed_of_orthogonal {d : ℕ} (x : Sphere d)
    (z : Euclidean (d + 1)) (hz : ∑ i, x.val i * z i = 0) :
    projection (projectiveProjection x) z = z := by
  rw [projection_apply_representative, hz, zero_smul, sub_zero]

theorem projection_idempotent {d : ℕ} (L : RealProjectiveSpace d)
    (z : Euclidean (d + 1)) : projection L (projection L z) = projection L z := by
  induction L using Quotient.inductionOn with
  | h x => exact projection_fixed_of_orthogonal x _ (projection_orthogonal x z)

/-- The kernel is exactly the line along which projection is performed. -/
theorem projection_ker {d : ℕ} (L : RealProjectiveSpace d) :
    LinearMap.ker (projectionLinear L) = directionSubmodule L := by
  ext z
  exact projection_eq_zero_iff L z

theorem directionSubmodule_finrank {d : ℕ} (L : RealProjectiveSpace d) :
    Module.finrank ℝ (directionSubmodule L) = 1 := by
  induction L using Quotient.inductionOn with
  | h x =>
    apply finrank_span_singleton
    intro hx
    have hsum := x.property
    simp [hx, squareSum] at hsum

/-- In an ambient space of dimension d+1, the canonical projection target has
exactly dimension d, so its use does not retain an unwanted ambient direction. -/
theorem projectionSpace_finrank {d : ℕ} (L : RealProjectiveSpace d) :
    Module.finrank ℝ (ProjectionSpace L) = d := by
  have hdim := (projectionLinear L).finrank_range_add_finrank_ker
  rw [projection_ker, directionSubmodule_finrank] at hdim
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  change Module.finrank ℝ (LinearMap.range (projectionLinear L)) = d
  omega

/-- Both inclusions in the characterization of the orthogonal-complement
model: every projected vector is perpendicular, and all such vectors occur. -/
theorem projectionSpace_mem_iff {d : ℕ} (x : Sphere d) (z : Euclidean (d + 1)) :
    z ∈ ProjectionSpace (projectiveProjection x) ↔ ∑ i, x.val i * z i = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact projection_orthogonal x w
  · intro hz
    exact ⟨z, projection_fixed_of_orthogonal x z hz⟩

theorem projectedMap_injective_iff {d : ℕ} {M : Type u}
    (L : RealProjectiveSpace d) (e : M → Euclidean (d + 1)) :
    Function.Injective (projectedMap L e) ↔
      Function.Injective (fun p => projection L (e p)) := by
  constructor
  · intro h p q hpq
    exact h (Subtype.ext hpq)
  · intro h p q hpq
    exact h (congrArg Subtype.val hpq)

/-- Secant avoidance is exactly what is needed to preserve injectivity. -/
theorem projection_injective_iff {d : ℕ} {M : Type u}
    (e : M → Euclidean (d + 1)) (he : Function.Injective e)
    (L : RealProjectiveSpace d) :
    Function.Injective (fun p => projection L (e p)) ↔ L ∉ secantDirections e := by
  constructor
  · intro hi ⟨p, p', hpp', _, hL⟩
    apply hpp'
    apply hi
    exact sub_eq_zero.mp (by
      rw [← (projection L).map_sub]
      exact (projection_eq_zero_iff L _).mpr hL)
  · intro hL p p' hpp'
    by_contra hne
    apply hL
    refine ⟨p, p', hne, sub_ne_zero.mpr (fun h => hne (he h)), ?_⟩
    apply (projection_eq_zero_iff L _).mp
    rw [(projection L).map_sub]
    exact sub_eq_zero.mpr hpp'

/-- Composition with a continuous linear map preserves the local extension
convention, including at the source boundary. -/
theorem smoothEuclidean_postcomp {n q r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (f : M → Euclidean q)
    (hf : IsSmoothEuclidean S f) (P : Euclidean q →L[ℝ] Euclidean r) :
    IsSmoothEuclidean S (fun p => P (f p)) := by
  intro p
  refine ⟨P.continuous.continuousAt.comp (hf p).1, ?_⟩
  intro c hc hp
  obtain ⟨U, hU, hpU, F, hF, hEq⟩ := (hf p).2 c hc hp
  exact ⟨U, hU, hpU, P ∘ F, P.contDiff.comp_contDiffOn hF, hEq.fun_comp P⟩

/-- The projection has smooth local extensions taking values in its actual
orthogonal-complement codomain, including over a boundary face. -/
theorem projectedMap_local_extension {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean (d + 1))
    (he : IsSmoothEuclidean S e) (L : RealProjectiveSpace d)
    (p : M) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hp : p ∈ c.source) :
    ContinuousAt (projectedMap L e) p ∧
    ∃ U : Set (Euclidean n), IsOpen U ∧ (c p).val ∈ U ∧
      ∃ F : Euclidean n → ProjectionSpace L, ContDiffOn ℝ ∞ F U ∧
        (fun x => F (c x).val) =ᶠ[𝓝 p] projectedMap L e := by
  let P : Euclidean (d + 1) →L[ℝ] ProjectionSpace L :=
    (projectionLinear L).rangeRestrict.toContinuousLinearMap
  have hP : (fun x => P (e x)) = projectedMap L e := rfl
  constructor
  · rw [← hP]
    exact P.continuous.continuousAt.comp (he p).1
  · obtain ⟨U, hU, hpU, F, hF, hEq⟩ := (he p).2 c hc hp
    exact ⟨U, hU, hpU, P ∘ F, P.contDiff.comp_contDiffOn hF, hEq.fun_comp P⟩

/-- The derivative of an ambient linear postcomposition is the actual composite
of derivatives, rather than a separate derivative certificate. -/
theorem coordinateDerivative_postcomp {n q r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (c : ModelChart n a M) (f : M → Euclidean q)
    (p : M) (hp : p ∈ c.source)
    (hf : LocalCoordinateExtension (⊤ : ℕ∞) (fun x => (c x).val) f p)
    (P : Euclidean q →L[ℝ] Euclidean r) :
    coordinateDerivative c (fun x => P (f x)) p = P.comp (coordinateDerivative c f p) := by
  obtain ⟨U, hU, hpU, F, hF, hEq⟩ := hf
  have hD := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have hcoord := FiniteRegularity.coordinateDerivative_eq c f p hp _ ⟨F, hD, hEq⟩
  rw [hcoord]
  exact FiniteRegularity.coordinateDerivative_eq c _ p hp _
    ⟨P ∘ F, P.hasFDerivAt.comp _ hD, hEq.fun_comp P⟩

/-- Avoiding the tangent directions preserves precisely full derivative
injectivity. The test uses all source charts and no restriction on M. -/
theorem projection_immersion_iff {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean (d + 1))
    (he : IsEuclideanImmersion S e) (L : RealProjectiveSpace d) :
    IsEuclideanImmersion S (fun p => projection L (e p)) ↔ L ∉ tangentDirections S e := by
  constructor
  · intro himm ⟨c, hc, p, hp, v, hv, hL⟩
    apply hv
    have hz : v = 0 := (himm.2 c hc p hp) (by
      rw [map_zero, coordinateDerivative_postcomp c e p hp ((he.1 p).2 c hc hp)]
      exact (projection_eq_zero_iff L _).mpr hL)
    rw [hz, map_zero]
  · intro hL
    refine ⟨smoothEuclidean_postcomp S e he.1 _, ?_⟩
    intro c hc p hp v w hvw
    apply he.2 c hc p hp
    have hd : coordinateDerivative c e p (v - w) = 0 := by
      by_contra hne
      apply hL
      refine ⟨c, hc, p, hp, v - w, hne, ?_⟩
      apply (projection_eq_zero_iff L _).mp
      rw [map_sub, map_sub]
      rw [coordinateDerivative_postcomp c e p hp ((he.1 p).2 c hc hp)] at hvw
      exact sub_eq_zero.mpr hvw
    exact sub_eq_zero.mp (by rwa [map_sub] at hd)

theorem tangentDirections_zero :
    Specs.SmoothManifolds.Ch04.GoodProjections.tangentDirections_zeroType.{u} := by
  intro d a M _ S e
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro L ⟨c, hc, p, hp, v, hv, hL⟩
  exact hv (by rw [Subsingleton.elim v 0, map_zero])

/-- The affine chart insertion has linear part given by insertion of zero. -/
def insertOneAffine {d : ℕ} (i : Fin (d + 1)) :
    Euclidean d →ᵃ[ℝ] Euclidean (d + 1) where
  toFun := insertOne i
  linear := {
    toFun := fun y => i.insertNth (0 : ℝ) y
    map_add' := by
      intro y z
      ext j
      obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j <;> simp
    map_smul' := by
      intro c y
      ext j
      obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j <;> simp }
  map_vadd' := by
    intro y z
    ext j
    obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j <;>
      simp [insertOne, vadd_eq_add]

/-- A proper vector subspace cannot contain the whole affine chart x_i = 1. -/
theorem affineChart_comap_ne_top {d : ℕ} (i : Fin (d + 1))
    (V : Submodule ℝ (Euclidean (d + 1))) (hV : V ≠ ⊤) :
    V.toAffineSubspace.comap (insertOneAffine i) ≠ ⊤ := by
  intro h
  have hall : ∀ y : Euclidean d, insertOne i y ∈ V := by
    intro y
    have hy : y ∈ V.toAffineSubspace.comap (insertOneAffine i) := by rw [h]; trivial
    exact hy
  apply hV
  apply top_unique
  intro z _
  have heq : z = z i • insertOne i 0 +
      (insertOne i (i.removeNth z) - insertOne i 0) := by
    ext j
    obtain rfl | ⟨k, rfl⟩ := i.eq_self_or_eq_succAbove j <;>
      simp [insertOne]
  rw [heq]
  exact V.add_mem (V.smul_mem _ (hall 0)) (V.sub_mem (hall _) (hall 0))

/-- All ratio coordinates of a represented line in V belong to the associated
proper affine subspace of the projective chart. -/
theorem insertOne_ratios_mem {d : ℕ} (i : Fin (d + 1))
    (V : Submodule ℝ (Euclidean (d + 1))) (L : RealProjectiveSpace d)
    (hL : L ∈ projectiveSubspace V) (hi : L ∈ projectiveLocus i) :
    insertOne i (projectiveRatios i L) ∈ V := by
  induction L using Quotient.inductionOn with
  | h x =>
    change directionSubmodule (projectiveProjection x) ≤ V at hL
    change projectiveProjection x ∈ projectiveLocus i at hi
    change insertOne i (projectiveRatios i (projectiveProjection x)) ∈ V
    have hx := (Projective.projection_mem_locus i x).mp hi
    have hv : x.val ∈ V := hL (Submodule.mem_span_singleton_self _)
    convert V.smul_mem (x.val i)⁻¹ hv using 1
    ext j
    rw [Projective.insertOne_ratios i x hx]
    simp [div_eq_mul_inv, mul_comm]

/-- Projective linear subspaces of a proper vector subspace are null, including
in projective dimension zero (where that projectivization is empty). -/
theorem projectiveSubspace_null {d : ℕ}
    (V : Submodule ℝ (Euclidean (d + 1))) (hV : V ≠ ⊤) :
    SardData.IsNull (Projective.projectiveManifold d) (projectiveSubspace V) := by
  apply (Sard.nullInCharts_iff (Projective.projectiveManifold d) (projectiveAtlas d)
    (Projective.projectiveAtlas_isContDiffAtlas d).1 ?_ (projectiveSubspace V)).mp
  · rintro c ⟨i, hc⟩
    have hz := MeasureTheory.Measure.addHaar_affineSubspace MeasureTheory.volume
      (V.toAffineSubspace.comap (insertOneAffine i)) (affineChart_comap_ne_top i V hV)
    apply MeasureTheory.measure_mono_null _ hz
    rintro _ ⟨L, ⟨hL, hLc⟩, rfl⟩
    change insertOne i (c L).val ∈ V
    rw [hc.2.2.1 L hLc]
    exact insertOne_ratios_mem i V L hL (hc.1 ▸ hLc)
  · intro c hc k hk
    exact ⟨(hk c hc).2, (hk c hc).1⟩

/-- Finite unions of chart-null sets remain chart-null without measurability. -/
theorem null_union {d : ℕ} {s t : Set (RealProjectiveSpace d)}
    (hs : SardData.IsNull (Projective.projectiveManifold d) s)
    (ht : SardData.IsNull (Projective.projectiveManifold d) t) :
    SardData.IsNull (Projective.projectiveManifold d) (s ∪ t) := by
  intro c hc
  rw [Set.union_inter_distrib_right, Set.image_union]
  exact MeasureTheory.measure_union_null (hs c hc) (ht c hc)

/-- Assembly from the two substantive small-dimensional image estimates. -/
theorem injective_immersion_dense_of_null {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean (d + 1))
    (he : IsEuclideanImmersion S e) (hi : Function.Injective e)
    (hs : SardData.IsNull (Projective.projectiveManifold d) (secantDirections e))
    (ht : SardData.IsNull (Projective.projectiveManifold d) (tangentDirections S e))
    (V : Submodule ℝ (Euclidean (d + 1))) (hV : V ≠ ⊤) :
    Dense {L : RealProjectiveSpace d | L ∉ projectiveSubspace V ∧
      Function.Injective (projectedMap L e) ∧
      IsEuclideanImmersion S (fun p => (projectedMap L e p).val)} := by
  have hdense := Sard.null_complement_dense (Projective.projectiveManifold d) _
    (null_union (projectiveSubspace_null V hV) (null_union hs ht))
  apply hdense.mono
  intro L hL
  have hLV : L ∉ projectiveSubspace V := fun h => hL (Or.inl h)
  have hLs : L ∉ secantDirections e := fun h => hL (Or.inr (Or.inl h))
  have hLt : L ∉ tangentDirections S e := fun h => hL (Or.inr (Or.inr h))
  exact ⟨hLV, (projectedMap_injective_iff L e).mpr ((projection_injective_iff e hi L).mpr hLs),
    (projection_immersion_iff S e he L).mpr hLt⟩

theorem immersion_dense_of_null {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean (d + 1))
    (he : IsEuclideanImmersion S e)
    (ht : SardData.IsNull (Projective.projectiveManifold d) (tangentDirections S e))
    (V : Submodule ℝ (Euclidean (d + 1))) (hV : V ≠ ⊤) :
    Dense {L : RealProjectiveSpace d | L ∉ projectiveSubspace V ∧
      IsEuclideanImmersion S (fun p => (projectedMap L e p).val)} := by
  have hdense := Sard.null_complement_dense (Projective.projectiveManifold d) _
    (null_union (projectiveSubspace_null V hV) ht)
  apply hdense.mono
  intro L hL
  exact ⟨fun h => hL (Or.inl h),
    (projection_immersion_iff S e he L).mpr (fun h => hL (Or.inr h))⟩

/-- The affine ratio coordinates of a nonzero vector on a represented line. -/
theorem ratios_of_mem_direction {d : ℕ} (i : Fin (d + 1))
    (L : RealProjectiveSpace d) (z : Euclidean (d + 1))
    (hz : z ≠ 0) (hL : z ∈ directionSubmodule L) (hi : L ∈ projectiveLocus i) :
    z i ≠ 0 ∧ projectiveRatios i L = (fun j => z (i.succAbove j) / z i) := by
  induction L using Quotient.inductionOn with
  | h x =>
    change z ∈ Submodule.span ℝ {x.val} at hL
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hL
    have hc0 : c ≠ 0 := by
      intro h
      apply hz
      rw [← hc, h, zero_smul]
    have hxi : x.val i ≠ 0 := (Projective.projection_mem_locus i x).mp hi
    rw [← hc]
    constructor
    · exact mul_ne_zero hc0 hxi
    · ext j
      change x.val (i.succAbove j) / x.val i =
        (c * x.val (i.succAbove j)) / (c * x.val i)
      rw [mul_div_mul_left _ _ hc0]

/-- Smooth images from a smaller-dimensional Euclidean open domain are null. -/
theorem euclidean_image_null {m d : ℕ} (U : Set (Euclidean m))
    (F : Euclidean m → Euclidean d) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hmd : m < d) :
    MeasureTheory.volume (F '' U) = 0 := by
  apply MeasureTheory.measure_mono_null _ (Ch04.euclidean_sard m d U F hU hF)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ⟨hx, ?_⟩, rfl⟩
  intro hsurj
  have hdim := LinearMap.finrank_le_finrank_of_surjective
    (f := (fderiv ℝ F x).toLinearMap) hsurj
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- A single smooth Euclidean extension represents a manifold map on one open
neighborhood. No extension of the manifold itself is assumed. -/
theorem localEuclidean_extension {n q : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean q)
    (he : IsSmoothEuclidean S e) (p : M) :
    ∃ (c : ModelChart n a M) (W : Set M) (U : Set (Euclidean n))
      (F : Euclidean n → Euclidean q),
      IsOpen W ∧ p ∈ W ∧ IsOpen U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ x ∈ W, (c x).val ∈ U ∧ F (c x).val = e x := by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, hEq⟩ := (he p).2 c hc hpc
  have hnhds : ∀ᶠ x in 𝓝 p, (c x).val ∈ U ∧ F (c x).val = e x := by
    filter_upwards [
      (continuous_subtype_val.continuousAt.comp (c.continuousAt hpc)).preimage_mem_nhds
        (hU.mem_nhds hpU), hEq] with x hx hxe
    exact ⟨hx, hxe⟩
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hnhds
  exact ⟨c, W, U, F, hW, hpW, hU, hF, fun x hx => hWsub hx⟩

/-- Taking ratios of a smooth difference has null image in the dimension range
needed for secants. This is an assertion on ambient open Euclidean sets. -/
theorem difference_ratios_image_null {n m d : ℕ} (i : Fin (d + 1))
    (F : Euclidean n → Euclidean (d + 1)) (G : Euclidean m → Euclidean (d + 1))
    (U : Set (Euclidean n)) (V : Set (Euclidean m))
    (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G V) (hd : n + m < d) :
    MeasureTheory.volume ((fun z : Euclidean n × Euclidean m =>
      fun j : Fin d => (F z.1 (i.succAbove j) - G z.2 (i.succAbove j)) /
        (F z.1 i - G z.2 i)) ''
      {z | z.1 ∈ U ∧ z.2 ∈ V ∧ F z.1 i - G z.2 i ≠ 0}) = 0 := by
  let C := appendCoordinates n m
  let D : Set (Euclidean n × Euclidean m) := U ×ˢ V
  let H : Euclidean n × Euclidean m → Euclidean (d + 1) := fun z => F z.1 - G z.2
  have hH : ContDiffOn ℝ ∞ H D :=
    (hF.comp contDiff_fst.contDiffOn (fun _ hz => hz.1)).sub
      (hG.comp contDiff_snd.contDiffOn (fun _ hz => hz.2))
  let O : Set (Euclidean n × Euclidean m) := D ∩ {z | H z i ≠ 0}
  have hO : IsOpen O :=
    ((continuous_apply i).comp_continuousOn hH.continuousOn).isOpen_inter_preimage (hU.prod hV) isOpen_compl_singleton
  let R : Euclidean n × Euclidean m → Euclidean d := fun z j => H z (i.succAbove j) / H z i
  have hR : ContDiffOn ℝ ∞ R O := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro j
    have hHz := hH.contDiffAt ((hU.prod hV).mem_nhds hz.1)
    exact (contDiffAt_pi.mp hHz (i.succAbove j)).div (contDiffAt_pi.mp hHz i) hz.2
  have hnull := euclidean_image_null (C.symm ⁻¹' O) (R ∘ C.symm)
    (hO.preimage C.symm.continuous)
    (hR.comp C.symm.contDiff.contDiffOn (fun _ hz => hz)) hd
  apply MeasureTheory.measure_mono_null _ hnull
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨C z, ?_, ?_⟩
  · change C.symm (C z) ∈ O
    rw [C.symm_apply_apply]
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
  · simp only [Function.comp_apply, C.symm_apply_apply]
    rfl

/-- The local extension proof works on M × M only as a topological space.
In particular it never incorrectly treats two boundary factors as an ordinary
smooth manifold. -/
theorem secant_ratios_image_null {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean (d + 1))
    (he : IsSmoothEuclidean S e) (i : Fin (d + 1)) (hd : 2 * n < d) :
    MeasureTheory.volume ((fun z : M × M =>
      fun j : Fin d => (e z.1 (i.succAbove j) - e z.2 (i.succAbove j)) /
        (e z.1 i - e z.2 i)) '' {z | e z.1 i - e z.2 i ≠ 0}) = 0 := by
  let := S.topologicalManifold.secondCountable
  apply Ch04.SardVanishingLayer.image_null_of_locally_image_null
  intro p hp
  obtain ⟨c, W, U, F, hW, hpW, hU, hF, hFe⟩ := localEuclidean_extension S e he p.1
  obtain ⟨c', W', V, G, hW', hpW', hV, hG, hGe⟩ := localEuclidean_extension S e he p.2
  refine ⟨W ×ˢ W', hW.prod hW', ⟨hpW, hpW'⟩, ?_⟩
  apply MeasureTheory.measure_mono_null _
    (difference_ratios_image_null i F G U V hU hV hF hG (by omega))
  rintro _ ⟨z, ⟨hz, hzW, hzW'⟩, rfl⟩
  obtain ⟨hzU, hFz⟩ := hFe z.1 hzW
  obtain ⟨hzV, hGz⟩ := hGe z.2 hzW'
  refine ⟨((c z.1).val, (c' z.2).val), ⟨hzU, hzV, ?_⟩, ?_⟩
  · change e z.1 i - e z.2 i ≠ 0 at hz
    simpa only [hFz, hGz] using hz
  · simp only [hFz, hGz]

theorem secantDirections_null {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean (d + 1))
    (he : IsSmoothEuclidean S e) (hd : 2 * n + 1 < d + 1) :
    SardData.IsNull (Projective.projectiveManifold d) (secantDirections e) := by
  apply (Sard.nullInCharts_iff (Projective.projectiveManifold d) (projectiveAtlas d)
    (Projective.projectiveAtlas_isContDiffAtlas d).1 ?_ (secantDirections e)).mp
  · rintro c ⟨i, hc⟩
    apply MeasureTheory.measure_mono_null _ (secant_ratios_image_null S e he i (by omega))
    rintro _ ⟨L, ⟨⟨p, p', hpp', hne, hline⟩, hLc⟩, rfl⟩
    obtain ⟨hzi, hratio⟩ := ratios_of_mem_direction i L (e p - e p') hne hline (hc.1 ▸ hLc)
    refine ⟨(p, p'), hzi, ?_⟩
    change (fun j => (e p (i.succAbove j) - e p' (i.succAbove j)) /
      (e p i - e p' i)) = (c L).val
    rw [hc.2.2.1 L hLc, hratio]
    rfl
  · intro c hc k hk
    exact ⟨(hk c hc).2, (hk c hc).1⟩

/-- A full coordinate derivative transforms by the actual transition Jacobian. -/
theorem coordinateDerivative_change_source {n q : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean q)
    (he : IsSmoothEuclidean S e) (c c' : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hc' : c' ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hp' : p ∈ c'.source) :
    coordinateDerivative c' e p =
      (coordinateDerivative c e p).comp (chartDerivative c' c id p) := by
  obtain ⟨U, hU, hpU, F, hF, hEq⟩ := (he p).2 c hc hp
  have hDF := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have hext := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 c' hc' c hc) hp' hp
  obtain ⟨G, hDG, hGe⟩ := FiniteRegularity.chartDerivative_exists (⊤ : ℕ∞) (by simp)
    c' c id p hext
  rw [FiniteRegularity.coordinateDerivative_eq c e p hp _ ⟨F, hDF, hEq⟩]
  apply FiniteRegularity.coordinateDerivative_eq c' e p hp'
  refine ⟨F ∘ G, ?_, (hGe.fun_comp F).trans hEq⟩
  have hb : G (c' p).val = (c p).val := hGe.eq_of_nhds
  have hDF' : HasFDerivAt F (fderiv ℝ F (c p).val) (G (c' p).val) := by
    simpa only [hb] using hDF
  exact hDF'.comp _ hDG

/-- Local extension data valid at every point of one open chart neighborhood. -/
theorem localEuclidean_extension_derivative {n q : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean q)
    (he : IsSmoothEuclidean S e) (p : M) :
    ∃ (c : ModelChart n a M) (W : Set M) (U : Set (Euclidean n))
      (F : Euclidean n → Euclidean q),
      c ∈ S.smoothStructure.val ∧ IsOpen W ∧ p ∈ W ∧ IsOpen U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ x ∈ W, x ∈ c.source ∧ (c x).val ∈ U ∧
        coordinateDerivative c e x = fderiv ℝ F (c x).val := by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, hEq⟩ := (he p).2 c hc hpc
  have hnhds : ∀ᶠ x in 𝓝 p, x ∈ c.source ∧ (c x).val ∈ U ∧
      (fun y => F (c y).val) =ᶠ[𝓝 x] e := by
    filter_upwards [c.open_source.mem_nhds hpc,
      (continuous_subtype_val.continuousAt.comp (c.continuousAt hpc)).preimage_mem_nhds
        (hU.mem_nhds hpU), hEq.eventuallyEq_nhds] with x hx hxU hxEq
    exact ⟨hx, hxU, hxEq⟩
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hnhds
  refine ⟨c, W, U, F, hc, hW, hpW, hU, hF, ?_⟩
  intro x hx
  obtain ⟨hxc, hxU, hxEq⟩ := hWsub hx
  exact ⟨hxc, hxU, FiniteRegularity.coordinateDerivative_eq c e x hxc _
    ⟨F, ((hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt, hxEq⟩⟩

/-- A family of sets is null if the union over a sufficiently small open base
neighborhood is null at every point of a second countable base. -/
theorem null_iUnion_of_locally_null {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace Y] (μ : MeasureTheory.Measure Y)
    (s : X → Set Y)
    (h : ∀ p, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ μ (⋃ x ∈ W, s x) = 0) :
    μ (⋃ x, s x) = 0 := by
  classical
  choose W hWo hpW hW using h
  obtain ⟨t, ht, hcover⟩ := isLindelof_univ.elim_countable_subcover W hWo (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hpW x⟩)
  apply MeasureTheory.measure_mono_null _
    ((MeasureTheory.measure_biUnion_null_iff ht).mpr (fun x _ => hW x))
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp hy
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  exact mem_iUnion₂.mpr ⟨z, hz, mem_iUnion₂.mpr ⟨x, hxz, hx⟩⟩

/-- Product-source version of the low-dimensional image estimate. -/
theorem product_image_null {n m d : ℕ} (O : Set (Euclidean n × Euclidean m))
    (R : Euclidean n × Euclidean m → Euclidean d)
    (hO : IsOpen O) (hR : ContDiffOn ℝ ∞ R O) (hd : n + m < d) :
    MeasureTheory.volume (R '' O) = 0 := by
  let C := appendCoordinates n m
  have hnull := euclidean_image_null (C.symm ⁻¹' O) (R ∘ C.symm)
    (hO.preimage C.symm.continuous)
    (hR.comp C.symm.contDiff.contDiffOn (fun _ hz => hz)) hd
  apply MeasureTheory.measure_mono_null _ hnull
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨C z, ?_, ?_⟩
  · simpa only [Set.mem_preimage, C.symm_apply_apply] using hz
  · simp only [Function.comp_apply, C.symm_apply_apply]

/-- Fixing one nonzero tangent coordinate to one removes radial redundancy.
This has source dimension (k+1)+k = 2n-1, including at boundary points. -/
theorem normalized_tangent_ratios_image_null {k d : ℕ}
    (i : Fin (d + 1)) (j : Fin (k + 1))
    (F : Euclidean (k + 1) → Euclidean (d + 1))
    (U : Set (Euclidean (k + 1))) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hd : 2 * (k + 1) < d + 1) :
    MeasureTheory.volume ((fun z : Euclidean (k + 1) × Euclidean k =>
      fun l : Fin d => (fderiv ℝ F z.1 (insertOne j z.2)) (i.succAbove l) /
        (fderiv ℝ F z.1 (insertOne j z.2)) i) ''
      {z | z.1 ∈ U ∧ (fderiv ℝ F z.1 (insertOne j z.2)) i ≠ 0}) = 0 := by
  let D : Set (Euclidean (k + 1) × Euclidean k) := U ×ˢ univ
  let H : Euclidean (k + 1) × Euclidean k → Euclidean (d + 1) :=
    fun z => fderiv ℝ F z.1 (insertOne j z.2)
  have hDF : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hH : ContDiffOn ℝ ∞ H D :=
    (hDF.comp contDiff_fst.contDiffOn (fun _ hz => hz.1)).clm_apply
      ((Projective.contDiff_insertOne j).comp contDiff_snd).contDiffOn
  let O : Set (Euclidean (k + 1) × Euclidean k) := D ∩ {z | H z i ≠ 0}
  have hO : IsOpen O :=
    ((continuous_apply i).comp_continuousOn hH.continuousOn).isOpen_inter_preimage
      (hU.prod isOpen_univ) isOpen_compl_singleton
  let R : Euclidean (k + 1) × Euclidean k → Euclidean d :=
    fun z l => H z (i.succAbove l) / H z i
  have hR : ContDiffOn ℝ ∞ R O := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_pi.mpr
    intro l
    have hHz := hH.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz.1)
    exact (contDiffAt_pi.mp hHz (i.succAbove l)).div (contDiffAt_pi.mp hHz i) hz.2
  apply MeasureTheory.measure_mono_null _ (product_image_null O R hO hR (by omega))
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨⟨hz.1, mem_univ _⟩, hz.2⟩, rfl⟩

/-- Tangent directions at one base point, using the shared full differential. -/
def tangentDirectionsAt {n d : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (e : M → Euclidean (d + 1)) (p : M) :
    Set (RealProjectiveSpace d) :=
  {L | ∃ c ∈ S.smoothStructure.val, p ∈ c.source ∧ ∃ v : Euclidean n,
    coordinateDerivative c e p v ≠ 0 ∧
      coordinateDerivative c e p v ∈ directionSubmodule L}

/-- Over an open neighborhood admitting one ambient extension, all tangent
ratio images are covered by the finitely many affine normalizations v_j = 1. -/
theorem local_tangent_ratios_null {k d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (k + 1) a M)
    (e : M → Euclidean (d + 1)) (he : IsSmoothEuclidean S e)
    (i : Fin (d + 1)) (hd : 2 * (k + 1) < d + 1)
    (c : ModelChart (k + 1) a M) (hc : c ∈ S.smoothStructure.val)
    (W : Set M) (U : Set (Euclidean (k + 1)))
    (F : Euclidean (k + 1) → Euclidean (d + 1)) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hrep : ∀ p ∈ W, p ∈ c.source ∧ (c p).val ∈ U ∧
      coordinateDerivative c e p = fderiv ℝ F (c p).val) :
    MeasureTheory.volume (⋃ p ∈ W,
      projectiveRatios i '' (tangentDirectionsAt S e p ∩ projectiveLocus i)) = 0 := by
  let R (j : Fin (k + 1)) (z : Euclidean (k + 1) × Euclidean k) : Euclidean d :=
    fun l => (fderiv ℝ F z.1 (insertOne j z.2)) (i.succAbove l) /
      (fderiv ℝ F z.1 (insertOne j z.2)) i
  let O (j : Fin (k + 1)) : Set (Euclidean (k + 1) × Euclidean k) :=
    {z | z.1 ∈ U ∧ (fderiv ℝ F z.1 (insertOne j z.2)) i ≠ 0}
  have hnull : MeasureTheory.volume (⋃ j, R j '' O j) = 0 :=
    MeasureTheory.measure_iUnion_null (fun j =>
      normalized_tangent_ratios_image_null i j F U hU hF hd)
  apply MeasureTheory.measure_mono_null _ hnull
  intro y hy
  obtain ⟨p, hpW, L, ⟨⟨c', hc', hp', v, hv, hvL⟩, hLi⟩, rfl⟩ :=
    mem_iUnion₂.mp hy
  obtain ⟨hpc, hpU, hpD⟩ := hrep p hpW
  let w : Euclidean (k + 1) := chartDerivative c' c id p v
  have hvec : coordinateDerivative c' e p v = coordinateDerivative c e p w := by
    rw [coordinateDerivative_change_source S e he c c' hc hc' p hpc hp']
    rfl
  rw [hvec] at hv hvL
  obtain ⟨hzi, hratio⟩ := ratios_of_mem_direction i L _ hv hvL hLi
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra! h
    apply hv
    have hw : w = 0 := funext h
    rw [hw, map_zero]
  let w' : Euclidean (k + 1) := (w j)⁻¹ • w
  let b : Euclidean k := j.removeNth w'
  have hwj : w' j = 1 := by simp [w', hj]
  have hins : insertOne j b = w' := by
    simpa only [insertOne, b, ← hwj] using Fin.insertNth_self_removeNth j w'
  have hnorm : fderiv ℝ F (c p).val (insertOne j b) =
      (w j)⁻¹ • coordinateDerivative c e p w := by
    rw [hins, ← hpD]
    exact map_smul _ _ _
  apply mem_iUnion.mpr
  refine ⟨j, ((c p).val, b), ⟨hpU, ?_⟩, ?_⟩
  · change (fderiv ℝ F (c p).val (insertOne j b)) i ≠ 0
    rw [hnorm]
    exact mul_ne_zero (inv_ne_zero hj) hzi
  · change (fun l => (fderiv ℝ F (c p).val (insertOne j b)) (i.succAbove l) /
        (fderiv ℝ F (c p).val (insertOne j b)) i) = projectiveRatios i L
    rw [hnorm, hratio]
    ext l
    exact mul_div_mul_left _ _ (inv_ne_zero hj)

/-- Tangent directions have null image in projective space as soon as q > 2n.
The n = 0 case is empty; positive n uses affine fibre normalizations instead
of choosing a bundle metric or assuming a sphere-bundle construction. -/
theorem tangentDirections_null {n d : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (e : M → Euclidean (d + 1))
    (he : IsSmoothEuclidean S e) (hd : 2 * n < d + 1) :
    SardData.IsNull (Projective.projectiveManifold d) (tangentDirections S e) := by
  cases n with
  | zero =>
    rw [tangentDirections_zero S e]
    intro c hc
    simp
  | succ k =>
    let := S.topologicalManifold.secondCountable
    apply (Sard.nullInCharts_iff (Projective.projectiveManifold d) (projectiveAtlas d)
      (Projective.projectiveAtlas_isContDiffAtlas d).1 ?_ (tangentDirections S e)).mp
    · rintro c ⟨i, hc⟩
      have hz : MeasureTheory.volume (⋃ p,
          projectiveRatios i '' (tangentDirectionsAt S e p ∩ projectiveLocus i)) = 0 := by
        apply null_iUnion_of_locally_null
        intro p
        obtain ⟨c', W, U, F, hc', hW, hpW, hU, hF, hrep⟩ :=
          localEuclidean_extension_derivative S e he p
        exact ⟨W, hW, hpW, local_tangent_ratios_null S e he i hd c' hc' W U F hU hF hrep⟩
      apply MeasureTheory.measure_mono_null _ hz
      rintro _ ⟨L, ⟨⟨c', hc', p, hp, v, hv, hvL⟩, hLc⟩, rfl⟩
      apply mem_iUnion.mpr
      refine ⟨p, L, ⟨⟨c', hc', hp, v, hv, hvL⟩, hc.1 ▸ hLc⟩, ?_⟩
      exact (hc.2.2.1 L hLc).symm
    · intro c hc k hk
      exact ⟨(hk c hc).2, (hk c hc).1⟩

theorem injective_immersion_directions_dense :
    Specs.SmoothManifolds.Ch04.GoodProjections.injective_immersion_directions_denseType.{u} := by
  intro n d a M _ S e he hi hd V hV
  exact injective_immersion_dense_of_null S e he hi (secantDirections_null S e he.1 hd)
    (tangentDirections_null S e he.1 (by omega)) V hV

theorem immersion_directions_dense :
    Specs.SmoothManifolds.Ch04.GoodProjections.immersion_directions_denseType.{u} := by
  intro n d a M _ S e he hd V hV
  exact immersion_dense_of_null S e he (tangentDirections_null S e he.1 hd) V hV

end SmoothManifolds.GoodProjections
