import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.MetricVolume
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Sign.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorAlgebra

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Equivalences
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SmoothManifolds.MetricVolumeResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData
  MapData BundleData BundleMetricData OrientationData ExteriorData FrameData MetricVolumeData Module Set
universe u v

section Algebra
variable {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- Top wedges in a fixed basis are their determinant times the basis wedge. -/
theorem wedge_basis_expansion (b : Basis (Fin n) ℝ V) (v : Fin n → V) :
    exteriorPower.ιMulti ℝ n v = b.det v • exteriorPower.ιMulti ℝ n b := by
  let f : AlternatingMap ℝ V (⋀[ℝ]^n V) (Fin n) := exteriorPower.ιMulti ℝ n
  let g : AlternatingMap ℝ V (⋀[ℝ]^n V) (Fin n) :=
    (LinearMap.toSpanSingleton ℝ (⋀[ℝ]^n V) (f b)).compAlternatingMap b.det
  have h : f = g := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i
      (Finite.injective_iff_bijective.mp hi)
    change f (b ∘ σ) = g (b ∘ σ)
    simp [g, AlternatingMap.map_perm, Module.Basis.det_self]
  exact DFunLike.congr_fun h v

/-- Every top exterior vector is synthesized from its determinant coefficient. -/
theorem determinant_expansion (b : Basis (Fin n) ℝ V) (v : ⋀[ℝ]^n V) :
    v = exteriorPower.alternatingMapLinearEquiv b.det v • exteriorPower.ιMulti ℝ n b := by
  let f : (⋀[ℝ]^n V) →ₗ[ℝ] (⋀[ℝ]^n V) :=
    (LinearMap.toSpanSingleton ℝ (⋀[ℝ]^n V) (exteriorPower.ιMulti ℝ n b)).comp
      (exteriorPower.alternatingMapLinearEquiv b.det)
  have h : LinearMap.id = f := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change exteriorPower.ιMulti ℝ n w = _
    simpa only [f, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] using wedge_basis_expansion b w
  exact DFunLike.congr_fun h v

/-- Evaluation of absolute-homogeneous functions on a basis determinant is the
canonical scalar trivialization of the density line. -/
def densityEvaluationEquiv (b : Basis (Fin n) ℝ V) :
    densitySubmodule (⋀[ℝ]^n V) ≃ₗ[ℝ] ℝ where
  toFun ρ := ρ.val (exteriorPower.ιMulti ℝ n b)
  invFun t := ⟨fun v => t * |exteriorPower.alternatingMapLinearEquiv b.det v|, by
    intro r v
    simp only [map_smul, smul_eq_mul, abs_mul]
    ring⟩
  left_inv ρ := by
    apply Subtype.ext
    funext v
    change ρ.val (exteriorPower.ιMulti ℝ n b) *
      |exteriorPower.alternatingMapLinearEquiv b.det v| = ρ.val v
    conv_rhs => rw [determinant_expansion b v]
    rw [ρ.property]
    ring
  right_inv t := by
    simp only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self, abs_one, mul_one]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


theorem bilinear_gram_posDef (B : LinearMap.BilinForm ℝ V)
    (hs : ∀ x y, B x y = B y x) (hp : ∀ x : V, x ≠ 0 → 0 < B x x)
    (b : Basis (Fin n) ℝ V) :
    (Matrix.of (fun i j => B (b i) (b j))).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact hs (b j) (b i)
  · intro x hx
    have hne : ∑ i, x i • b i ≠ 0 := by
      rw [← b.equivFun_symm_apply]
      intro hz
      apply hx
      have he := congrArg b.equivFun hz
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using he
    have h := hp _ hne
    have hf : B (∑ i, x i • b i) (∑ i, x i • b i) =
        ∑ i, ∑ j, x i * B (b i) (b j) * x j := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hf] at h
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using h



end Algebra

section Coordinates
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

def coordinateBasis (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) : Basis (Fin n) ℝ (TangentSpace S p.val) :=
  (Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p.val p.property).symm

theorem coordinate_expansion (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) (v : DeterminantLine S p.val) :
    v = determinantCoefficient K c hc p v • OrientationData.coordinateVector K c hc p := by
  simpa only [coordinateBasis, Module.Basis.coe_map, Function.comp_def,
    determinantCoefficient, OrientationData.coordinateVector] using
    determinant_expansion (coordinateBasis K c hc p) v

@[simp] theorem coefficient_coordinateVector (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    determinantCoefficient K c hc p (OrientationData.coordinateVector K c hc p) = 1 := by
  unfold determinantCoefficient OrientationData.coordinateVector
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simpa only [Module.Basis.coe_map, Function.comp_def] using
    (@Module.Basis.det_self ℝ _ (TangentSpace S p.val) inferInstance inferInstance (Fin n) _ _
      ((Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p.val p.property).symm))


theorem coordinateVector_ne_zero (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    OrientationData.coordinateVector K c hc p ≠ 0 := by
  intro h
  have := coefficient_coordinateVector K c hc p
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem densityCoefficient_bijective (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    Function.Bijective (densityCoefficient K c hc p) := by
  let e : DensityLine S p.val ≃ₗ[ℝ] ℝ := densityEvaluationEquiv (coordinateBasis K c hc p)
  have he : (e : DensityLine S p.val → ℝ) =
      (fun ρ : DensityLine S p.val => ρ.val (OrientationData.coordinateVector K c hc p)) := by
    funext ρ
    simp only [e, densityEvaluationEquiv, coordinateBasis, Module.Basis.coe_map, Function.comp_def,
      densityCoefficient, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk,
      OrientationData.coordinateVector]
  have hbij : Function.Bijective (e : DensityLine S p.val → ℝ) := e.bijective
  rw [he] at hbij
  exact hbij


theorem density_finrank (K : FiberCoordinates S) (p : M) :
    Module.finrank ℝ (DensityLine S p) = 1 := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  simpa using (densityEvaluationEquiv (coordinateBasis K c hc ⟨p, hp⟩)).finrank_eq

theorem coordinateVector_transition (K : FiberCoordinates S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) :
    OrientationData.coordinateVector K d hd ⟨p.val, p.property.2⟩ =
      transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩ •
        OrientationData.coordinateVector K c hc ⟨p.val, p.property.1⟩ := by
  let b := coordinateBasis K c hc ⟨p.val, p.property.1⟩
  let w := coordinateBasis K d hd ⟨p.val, p.property.2⟩
  have h : b.det w = transitionDeterminant K d c hd hc
      ⟨p.val, p.property.2, p.property.1⟩ := by
    unfold transitionDeterminant
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
    apply congrArg Matrix.det
    ext i j
    simp [b, w, coordinateBasis,
      Module.Basis.toMatrix_apply]
  have he := wedge_basis_expansion b w
  rw [h] at he
  simpa only [b, w, coordinateBasis, Module.Basis.coe_map, Function.comp_def,
    OrientationData.coordinateVector] using he

theorem density_transition (K : FiberCoordinates S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) (ρ : DensityLine S p.val) :
    densityCoefficient K d hd ⟨p.val, p.property.2⟩ ρ =
      |transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩| *
        densityCoefficient K c hc ⟨p.val, p.property.1⟩ ρ := by
  change ρ.val _ = _ * ρ.val _
  rw [coordinateVector_transition K c d hc hd p, ρ.property]

@[simp] theorem coordinateTopForm_pairing (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    pairing p.val (coordinateTopForm K c hc p) (OrientationData.coordinateVector K c hc p) = 1 := by
  unfold pairing coordinateTopForm OrientationData.coordinateVector
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  have h : Matrix.of (fun i j => CovectorData.coordinateCovector K c hc p.val p.property j
      ((K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) i))) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [CovectorData.coordinateCovector, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h, Matrix.det_one]

theorem topForm_expansion (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (α : Fiber (TangentSpace S p.val) n) :
    α = pairing p.val α (OrientationData.coordinateVector K c hc p) •
      coordinateTopForm K c hc p := by
  letI := Module.Free.of_basis (coordinateBasis K c hc p)
  letI := Module.Finite.of_basis (coordinateBasis K c hc p)
  apply (exteriorPower.bijective_pairingDual ℝ (TangentSpace S p.val) n).injective
  apply LinearMap.ext
  intro v
  have he := coordinate_expansion K c hc p v
  conv_lhs => rw [he]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  change _ = _ * pairing p.val (coordinateTopForm K c hc p) v
  conv_rhs => rw [he]
  simp only [pairing, map_smul, smul_eq_mul]
  rw [show (exteriorPower.pairingDual ℝ (TangentSpace S p.val) n)
      (coordinateTopForm K c hc p) (OrientationData.coordinateVector K c hc p) = 1 from
        coordinateTopForm_pairing K c hc p]
  ring


theorem coordinateTopForm_transition (K : FiberCoordinates S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) :
    coordinateTopForm K c hc ⟨p.val, p.property.1⟩ =
      transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩ •
        coordinateTopForm K d hd ⟨p.val, p.property.2⟩ := by
  have he := topForm_expansion K d hd ⟨p.val, p.property.2⟩
    (coordinateTopForm K c hc ⟨p.val, p.property.1⟩)
  have hp : pairing p.val (coordinateTopForm K c hc ⟨p.val, p.property.1⟩)
      (OrientationData.coordinateVector K d hd ⟨p.val, p.property.2⟩) =
      transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩ := by
    rw [coordinateVector_transition K c d hc hd p]
    simp only [pairing, map_smul, smul_eq_mul]
    rw [show (exteriorPower.pairingDual ℝ (TangentSpace S p.val) n)
      (coordinateTopForm K c hc ⟨p.val, p.property.1⟩)
      (OrientationData.coordinateVector K c hc ⟨p.val, p.property.1⟩) = 1 from
        coordinateTopForm_pairing K c hc ⟨p.val, p.property.1⟩, mul_one]
  rwa [hp] at he


private theorem density_line_core :
    Specs.SmoothManifolds.Orientations.MetricVolume.density_lineType.{u} := by
  intro n a M _ S K
  exact ⟨density_finrank K, densityCoefficient_bijective K, density_transition K⟩

end Coordinates

section Smoothness
open Filter
open scoped Topology
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem smoothOnBase_restrict {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Set M) (hU : IsOpen U) (f : M → V) (hf : SmoothOnBase S f U) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU) (fun p : U => f p.val) := by
  intro p
  refine ⟨(hf p.val p.property).1.comp continuousAt_subtype_val, ?_⟩
  rintro _ ⟨hne, c, hc, rfl⟩ hp
  obtain ⟨W, hW, hpW, F, hF, he⟩ := (hf p.val p.property).2 c hc
    (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hp)
  exact ⟨W, hW, hpW, F, hF, he.comp_tendsto continuousAt_subtype_val⟩

theorem metricMatrix_smooth {C : CotangentBundle S} (g : Metric C)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (i j : Fin n) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => metricMatrix g K c hc p i j) := by
  letI := C.realization.space.topology
  let k : TangentIndex S := ⟨c, hc⟩
  let B := C.realization.space.bundle
  have hb (p : c.source) : p.val ∈ B.baseSet k := by
    rw [C.realization.baseSet k]
    exact p.property
  have hcoord (p : c.source) : B.fiberCoordinates k p.val (hb p) =
      K.equiv c hc p.val p.property := by
    apply LinearEquiv.ext
    intro v
    rw [BundleData.SmoothVectorBundle.fiberCoordinates_apply, C.realization.coordinates]
    exact LinearEquiv.congr_fun
      (TangentBundle.chartCoordinates_unique (C.tangent.fiberCoordinates.isCoordinates c hc p.val p.property)
        (K.isCoordinates c hc p.val p.property)) v
  have heq (p : c.source) (i : Fin n) :
      (B.trivialization k).symm p.val (Pi.single i 1) =
        (K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) i) := by
    rw [← BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply B k p.val (hb p), hcoord p]
    simp
  have hs : SmoothOnBase S
      (fun p => g.form p ((B.trivialization k).symm p (Pi.single i 1))
        ((B.trivialization k).symm p (Pi.single j 1))) c.source := by
    simpa only [C.realization.baseSet k] using g.smooth k i j
  have he : (fun p : c.source => metricMatrix g K c hc p i j) =
      (fun p : c.source => g.form p.val ((B.trivialization k).symm p.val (Pi.single i 1))
        ((B.trivialization k).symm p.val (Pi.single j 1))) := by
    funext p
    rw [heq, heq]
    rfl
  rw [he]
  exact smoothOnBase_restrict c.source c.open_source _ hs

theorem matrix_det_smooth (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ => (Matrix.of A).det) := by
  classical
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

end Smoothness

section Metric
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S}

/-- Homogeneity of the induced norm holds directly for the bilinear exterior
metric; no positive frame or volume form is assumed. -/
theorem determinantNorm_smul (g : Metric C) (p : M) (t : ℝ)
    (v : DeterminantLine S p) :
    determinantNorm g p (t • v) = |t| * determinantNorm g p v := by
  unfold determinantNorm
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Real.sqrt_mul (mul_self_nonneg t), Real.sqrt_mul_self_eq_abs]

/-- Canonical metric density as an element of the absolute dual at each point. -/
def metricDensity (g : Metric C) : DensityField S :=
  fun p => ⟨determinantNorm g p, fun t v => determinantNorm_smul g p t v⟩

@[simp] theorem metricDensity_apply (g : Metric C) (p : M) (v : DeterminantLine S p) :
    (metricDensity g p).val v = determinantNorm g p v := rfl

theorem metricDensity_unique (g : Metric C) (ρ : DensityField S)
    (h : IsMetricDensity g ρ) : ρ = metricDensity g := by
  funext p
  apply Subtype.ext
  funext v
  exact h p v

theorem gram_formula (g : Metric C) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    determinantNorm g p.val (OrientationData.coordinateVector K c hc p) =
      Real.sqrt (metricMatrix g K c hc p).det := by
  unfold determinantNorm determinantMetric coordinateVector
  simp only [LinearMap.BilinForm.exteriorPower, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  congr 1
  exact Matrix.det_transpose _

@[simp] theorem metricDensity_coefficient (g : Metric C) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    densityCoefficient K c hc p (metricDensity g p.val) =
      Real.sqrt (metricMatrix g K c hc p).det := gram_formula g K c hc p

theorem metricMatrix_det_pos (g : Metric C) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    0 < (metricMatrix g K c hc p).det := by
  letI := C.realization.space.topology
  exact (bilinear_gram_posDef (g.form p.val) (g.symmetric p.val)
    (g.positive p.val) (coordinateBasis K c hc p)).det_pos

theorem metric_coefficient_smooth (g : Metric C) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => Real.sqrt (metricMatrix g K c hc p).det) := by
  intro p
  have hm := FrameData.VectorSmoothAt.pi (fun i : Fin n =>
    FrameData.VectorSmoothAt.pi (fun j : Fin n => metricMatrix_smooth g K c hc i j p))
  have hd := hm.postcomp (matrix_det_smooth n)
  apply hd.postcompOn isOpen_Ioi (metricMatrix_det_pos g K c hc p)
  intro x hx
  exact (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt

private theorem gram_core : Specs.SmoothManifolds.Orientations.MetricVolume.gramType.{u} := by
  intro n a M _ S C g K c hc
  exact ⟨fun p => ⟨gram_formula g K c hc p, metricMatrix_det_pos g K c hc p⟩,
    metric_coefficient_smooth g K c hc⟩

theorem metricDensity_smooth (g : Metric C) : IsSmoothDensity (metricDensity g) := by
  intro K c hc
  simpa only [metricDensity_coefficient] using metric_coefficient_smooth g K c hc


theorem determinantNorm_pos (g : Metric C) (p : M) (v : DeterminantLine S p)
    (hv : v ≠ 0) : 0 < determinantNorm g p v := by
  let K := C.tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  have ht : determinantCoefficient K c hc ⟨p, hp⟩ v ≠ 0 := by
    intro hz
    apply hv
    simpa [hz] using coordinate_expansion K c hc ⟨p, hp⟩ v
  rw [coordinate_expansion K c hc ⟨p, hp⟩ v, determinantNorm_smul, gram_formula g K c hc ⟨p, hp⟩]
  exact mul_pos (abs_pos.mpr ht) (Real.sqrt_pos.mpr (metricMatrix_det_pos g K c hc ⟨p, hp⟩))

theorem metricDensity_positive (g : Metric C) : IsPositiveDensity (metricDensity g) :=
  determinantNorm_pos g

theorem metricDensity_nonzero (g : Metric C) (p : M) : metricDensity g p ≠ 0 := by
  let K := C.tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  intro hz
  have h := metricDensity_positive g p (OrientationData.coordinateVector K c hc ⟨p, hp⟩)
    (coordinateVector_ne_zero K c hc ⟨p, hp⟩)
  rw [hz] at h
  exact lt_irrefl 0 h

private theorem density_exists_unique_core :
    Specs.SmoothManifolds.Orientations.MetricVolume.density_exists_uniqueType.{u} := by
  intro n a M _ S C g
  refine ⟨metricDensity g, ⟨(fun _ _ => rfl), metricDensity_smooth g,
    metricDensity_positive g, metricDensity_nonzero g, metricDensity_coefficient g⟩, ?_⟩
  intro ρ hρ
  exact metricDensity_unique g ρ hρ.1


theorem metric_coefficient_transition (g : Metric C) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)) :
    Real.sqrt (metricMatrix g K d hd ⟨p.val, p.property.2⟩).det =
      |transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩| *
        Real.sqrt (metricMatrix g K c hc ⟨p.val, p.property.1⟩).det := by
  rw [← gram_formula g K d hd, coordinateVector_transition K c d hc hd p,
    determinantNorm_smul, gram_formula g K c hc ⟨p.val, p.property.1⟩]


theorem signed_overlap_scalar (a b t r : ℝ) (hs : a = b * (SignType.sign t : ℝ)) :
    (a * r) * t = b * (|t| * r) := by
  rw [hs]
  calc
    _ = b * ((SignType.sign t : ℝ) * t) * r := by ring
    _ = _ := by rw [sign_mul_self]; ring

private theorem overlap_core : Specs.SmoothManifolds.Orientations.MetricVolume.overlapType.{u} := by
  intro n a M _ S C g K s c d hc hd p
  dsimp only
  let pc : c.source := ⟨p.val, p.property.1⟩
  let pd : d.source := ⟨p.val, p.property.2⟩
  let T := transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩
  let f := coordinateTopForm K d hd pd
  let x := Real.sqrt (metricMatrix g K c hc pc).det
  let e := signValue (s.sign c hc pc)
  let e' := signValue (s.sign d hd pd)
  have ht : coordinateTopForm K c hc pc = T • f := coordinateTopForm_transition K c d hc hd p
  have hg := metric_coefficient_transition g K c d hc hd p
  have hs : (e*x)*T = e'*(|T| * x) := signed_overlap_scalar _ _ _ _
    (s.compatible K d c hd hc ⟨p.val, p.property.2, p.property.1⟩)
  refine ⟨hg, ?_⟩
  calc
    _ = (e*x) • (T • f) := congrArg (fun w : Fiber (TangentSpace S p.val) n => (e*x) • w) ht
    _ = ((e*x)*T) • f := smul_smul _ _ _
    _ = (e'*(|T| * x)) • f := congrArg (fun t : ℝ => t • f) hs
    _ = _ := congrArg (fun t : ℝ => (e'*t) • f) hg.symm


theorem positive_smul {p : M} {r : DeterminantRay S p} {v : DeterminantLine S p}
    (h : IsPositive r v) {t : ℝ} (ht : 0 < t) : IsPositive r (t • v) := by
  obtain ⟨hv, hr⟩ := h
  refine ⟨smul_ne_zero ht.ne' hv, ?_⟩
  rw [ray_pos_smul hv ht, hr]

theorem metricVolume_evaluate_positive {D : FormBundle C n}
    (g : Metric C) (o : Orientation S) (ω : Form D) (hω : IsMetricVolume g o ω)
    (p : M) (v : DeterminantLine S p) (hv : IsPositive (o.val p) v) :
    pairing p (ω.field p) v = determinantNorm g p v := by
  have hn : 0 < determinantNorm g p v := determinantNorm_pos g p v hv.choose
  have hunit : determinantNorm g p ((determinantNorm g p v)⁻¹ • v) = 1 := by
    rw [determinantNorm_smul, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have he := hω p _ (positive_smul hv (inv_pos.mpr hn)) hunit
  have he' : (determinantNorm g p v)⁻¹ * pairing p (ω.field p) v = 1 := by
    simpa only [pairing, map_smul, smul_eq_mul] using he
  have he'' := congrArg (fun z : ℝ => determinantNorm g p v * z) he'
  simpa only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_one] using he''

private theorem volume_coordinates_core :
    Specs.SmoothManifolds.Orientations.MetricVolume.volume_coordinatesType.{u} := by
  intro n a M _ S C D g o ω hω s hs K c hc p
  have hv := metricVolume_evaluate_positive g o ω hω p.val _ (hs K c hc p)
  rw [determinantNorm_smul, gram_formula g K c hc p] at hv
  have he : pairing p.val (ω.field p.val) (OrientationData.coordinateVector K c hc p) =
      signValue (s.sign c hc p) * Real.sqrt (metricMatrix g K c hc p).det := by
    cases h : s.sign c hc p
    · have hneg : -pairing p.val (ω.field p.val) (OrientationData.coordinateVector K c hc p) =
          Real.sqrt (metricMatrix g K c hc p).det := by
        simpa [pairing, signValue, h] using hv
      simp only [signValue, Bool.false_eq_true, ite_false, neg_one_mul]
      exact neg_eq_iff_eq_neg.mp hneg
    · simpa [pairing, signValue, h] using hv
  rw [topForm_expansion K c hc p (ω.field p.val), he]


def oppositeOrientation (o : Orientation S) : Orientation S :=
  ⟨fun p => -o.val p, by
    intro K c hc
    simpa only [Function.comp_def, Module.Ray.map_neg] using
      (o.property K c hc).comp (fun r => -r)⟩

theorem positive_neg {p : M} {r : DeterminantRay S p} {v : DeterminantLine S p}
    (h : IsPositive r v) : IsPositive (-r) (-v) := by
  obtain ⟨hv, hr⟩ := h
  refine ⟨neg_ne_zero.mpr hv, ?_⟩
  exact (neg_rayOfNeZero ℝ v hv).symm.trans (congrArg Neg.neg hr)

theorem metricVolume_abs_pairing {D : FormBundle C n} (g : Metric C) (o : Orientation S)
    (ω : Form D) (hω : IsMetricVolume g o ω) (s : SignedCharts S)
    (hs : RepresentsSignedCharts o.val s) (p : M) (v : DeterminantLine S p) :
    |pairing p (ω.field p) v| = determinantNorm g p v := by
  let K := C.tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  have hw := volume_coordinates_core S C D g o ω hω s hs K c hc ⟨p, hp⟩
  rw [coordinate_expansion K c hc ⟨p, hp⟩ v, determinantNorm_smul,
    gram_formula g K c hc ⟨p, hp⟩]
  simp only [pairing, map_smul, smul_eq_mul, abs_mul]
  rw [hw]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul]
  rw [show (exteriorPower.pairingDual ℝ (TangentSpace S p) n)
    (coordinateTopForm K c hc ⟨p, hp⟩) (OrientationData.coordinateVector K c hc ⟨p, hp⟩) = 1 from
      coordinateTopForm_pairing K c hc ⟨p, hp⟩]
  have hsign : |signValue (s.sign c hc ⟨p, hp⟩)| = 1 := by
    cases h : s.sign c hc ⟨p, hp⟩ <;> simp [signValue, h]
  rw [hsign, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp

private theorem orientation_reversal_core
    (hcharts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u}) :
    Specs.SmoothManifolds.Orientations.MetricVolume.orientation_reversalType.{u} := by
  intro n a M _ S C D g o
  refine ⟨oppositeOrientation o, (fun _ => rfl), ?_⟩
  intro α β hα hβ
  obtain ⟨s, hs, _⟩ := (hcharts S o.val).mp o.property
  have hneg : ∀ p, β.field p = -α.field p := by
    intro p
    let K := C.tangent.fiberCoordinates
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    let w := signValue (s.sign c hc ⟨p, hp⟩) • OrientationData.coordinateVector K c hc ⟨p, hp⟩
    have hpos : IsPositive (o.val p) w := hs K c hc ⟨p, hp⟩
    have ha := metricVolume_evaluate_positive g o α hα p w hpos
    have hb := metricVolume_evaluate_positive g (oppositeOrientation o) β hβ p (-w) (positive_neg hpos)
    have hn : determinantNorm g p (-w) = determinantNorm g p w := by
      simp only [determinantNorm, map_neg, LinearMap.neg_apply, neg_neg]
    rw [hn] at hb
    have he : pairing p (β.field p) (OrientationData.coordinateVector K c hc ⟨p, hp⟩) =
        -pairing p (α.field p) (OrientationData.coordinateVector K c hc ⟨p, hp⟩) := by
      have hsum : pairing p (β.field p) (-w) = pairing p (α.field p) w := hb.trans ha.symm
      cases h : s.sign c hc ⟨p, hp⟩ <;>
        simp only [w, signValue, h, Bool.false_eq_true, ite_false, ite_true,
          one_smul, pairing, map_neg, map_smul, smul_eq_mul, neg_one_mul, neg_neg] at hsum ⊢
      · exact hsum
      · exact neg_eq_iff_eq_neg.mp hsum
    rw [topForm_expansion K c hc ⟨p, hp⟩ (β.field p),
      topForm_expansion K c hc ⟨p, hp⟩ (α.field p), he]
    exact neg_smul (pairing p (α.field p) (OrientationData.coordinateVector K c hc ⟨p, hp⟩))
      (coordinateTopForm K c hc ⟨p, hp⟩)
  refine ⟨hneg, ?_⟩
  intro ρ hρ p v
  have habs := metricVolume_abs_pairing g o α hα s hs p v
  refine ⟨habs.trans (hρ p v).symm, ?_⟩
  rw [hneg]
  simpa only [pairing, map_neg, LinearMap.neg_apply, abs_neg] using habs.trans (hρ p v).symm


/-- The empty wedge is the canonical scalar one, independently of the metric. -/
theorem zero_norm {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} {C : CotangentBundle S} (g : Metric C) (p : M) :
    determinantNorm g p ((exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1) = 1 := by
  have he : (exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1 =
      exteriorPower.ιMulti ℝ 0 (fun i => Fin.elim0 i) := by
    apply (exteriorPower.zeroEquiv ℝ (TangentSpace S p)).injective
    simp
  rw [he]
  simp [determinantNorm, determinantMetric]

private theorem zero_dimension_core :
    Specs.SmoothManifolds.Orientations.MetricVolume.zero_dimensionType.{u} := by
  intro a M _ S C D g o ω ρ hω hρ s hs K c hc p
  let one : DeterminantLine S p.val :=
    (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1
  have he : OrientationData.coordinateVector K c hc p = one := by
    apply (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).injective
    simp [OrientationData.coordinateVector, one]
  have hn : determinantNorm g p.val one = 1 := zero_norm g p.val
  have hp := hs K c hc p
  rw [he] at hp
  have hunit : determinantNorm g p.val (signValue (s.sign c hc p) • one) = 1 := by
    rw [determinantNorm_smul, hn]
    cases h : s.sign c hc p <;> simp [signValue, h]
  have hvalue := hω p.val _ hp hunit
  have hpair : pairing p.val (ω.field p.val) one = signValue (s.sign c hc p) := by
    cases h : s.sign c hc p
    · have hneg : -pairing p.val (ω.field p.val) one = 1 := by
        simpa [pairing, signValue, h] using hvalue
      simpa only [neg_eq_iff_eq_neg, signValue, Bool.false_eq_true, ite_false] using hneg
    · simpa [pairing, signValue, h] using hvalue
  exact ⟨Matrix.det_isEmpty, hn, hpair, (hρ p.val one).trans hn⟩


end Metric
section Normalization
open Filter
open scoped Topology
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {D : FormBundle C n}

theorem pairing_coordinate_ne_zero (α : NonvanishingTopForm D) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    pairing p.val (α.val.field p.val) (OrientationData.coordinateVector K c hc p) ≠ 0 := by
  intro hz
  have he := topForm_expansion K c hc p (α.val.field p.val)
  exact α.property p.val (by simpa only [hz, zero_smul] using he)

theorem exists_unit_pairing (α : NonvanishingTopForm D) (p : M) :
    ∃ v : DeterminantLine S p, pairing p (α.val.field p) v = 1 := by
  let K := C.tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  have h := pairing_coordinate_ne_zero α K c hc ⟨p, hp⟩
  refine ⟨(pairing p (α.val.field p) (OrientationData.coordinateVector K c hc ⟨p, hp⟩))⁻¹ •
    OrientationData.coordinateVector K c hc ⟨p, hp⟩, ?_⟩
  simpa only [pairing, map_smul, smul_eq_mul] using inv_mul_cancel₀ h

/-- A unit for an already nonvanishing form, used only to define its intrinsic
metric normalization. Its choices cancel in every coordinate expression. -/
def unitPairingVector (α : NonvanishingTopForm D) (p : M) : DeterminantLine S p :=
  Classical.choose (exists_unit_pairing α p)

theorem unitPairingVector_pairing (α : NonvanishingTopForm D) (p : M) :
    pairing p (α.val.field p) (unitPairingVector α p) = 1 :=
  Classical.choose_spec (exists_unit_pairing α p)

def normalizationFactor (g : Metric C) (α : NonvanishingTopForm D) (p : M) : ℝ :=
  determinantNorm g p (unitPairingVector α p)

theorem normalizationFactor_coordinates (g : Metric C) (α : NonvanishingTopForm D)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) :
    normalizationFactor g α p.val = Real.sqrt (metricMatrix g K c hc p).det /
      |pairing p.val (α.val.field p.val) (OrientationData.coordinateVector K c hc p)| := by
  have hb := pairing_coordinate_ne_zero α K c hc p
  have hu := unitPairingVector_pairing α p.val
  rw [coordinate_expansion K c hc p (unitPairingVector α p.val)] at hu
  have hu' : determinantCoefficient K c hc p (unitPairingVector α p.val) *
      pairing p.val (α.val.field p.val) (OrientationData.coordinateVector K c hc p) = 1 := by
    simpa only [pairing, map_smul, smul_eq_mul] using hu
  have habs := congrArg abs hu'
  simp only [abs_mul, abs_one] at habs
  have hcoef : |determinantCoefficient K c hc p (unitPairingVector α p.val)| =
      1 / |pairing p.val (α.val.field p.val) (OrientationData.coordinateVector K c hc p)| :=
    (eq_div_iff (abs_ne_zero.mpr hb)).mpr habs
  unfold normalizationFactor
  rw [coordinate_expansion K c hc p (unitPairingVector α p.val), determinantNorm_smul,
    gram_formula g K c hc p, hcoef]
  ring

theorem normalizationFactor_pairing (g : Metric C) (α : NonvanishingTopForm D)
    (p : M) (v : DeterminantLine S p) :
    normalizationFactor g α p * |pairing p (α.val.field p) v| = determinantNorm g p v := by
  let K := C.tangent.fiberCoordinates
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  have hb := pairing_coordinate_ne_zero α K c hc ⟨p, hp⟩
  rw [normalizationFactor_coordinates g α K c hc ⟨p, hp⟩,
    coordinate_expansion K c hc ⟨p, hp⟩ v, determinantNorm_smul, gram_formula g K c hc ⟨p, hp⟩]
  simp only [pairing, map_smul, smul_eq_mul, abs_mul]
  unfold pairing at hb
  field_simp [abs_ne_zero.mpr hb]

/-- Constants recording evaluation of each increasing coordinate wedge. This
avoids making any arbitrary ordering choice in the top-degree index set. -/
def wedgeWeight (n : ℕ) (I : Index n n) : ℝ :=
  (Matrix.of (fun i j => (Pi.basisFun ℝ (Fin n))
    (Set.powersetCard.ofFinEmbEquiv.symm I j) i)).det

theorem coordinate_wedge_pairing (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n n) :
    pairing p.val (exteriorPower.ιMulti ℝ n (fun j => CovectorData.coordinateCovector
      C.tangent.fiberCoordinates c hc p.val p.property (Set.powersetCard.ofFinEmbEquiv.symm I j)))
      (OrientationData.coordinateVector C.tangent.fiberCoordinates c hc p) = wedgeWeight n I := by
  unfold pairing OrientationData.coordinateVector wedgeWeight
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  congr 1
  ext i j
  simp [CovectorData.coordinateCovector, Pi.single_apply, eq_comm]

theorem coordinate_pairing_expansion
    (hexp : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u})
    (α : Form D) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    pairing p.val (α.field p.val) (OrientationData.coordinateVector C.tangent.fiberCoordinates c hc p) =
      ∑ I : Index n n, coefficients C n c hc α.field p I * wedgeWeight n I := by
  have he := congrArg (fun β : Fiber (TangentSpace S p.val) n =>
    pairing p.val β (OrientationData.coordinateVector C.tangent.fiberCoordinates c hc p))
      (hexp C n c hc α.field p)
  simp only [pairing, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at he
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro I _
  exact congrArg (coefficients C n c hc α.field p I * ·) (coordinate_wedge_pairing c hc p I)

theorem coordinate_pairing_smooth
    (hexp : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u})
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    (α : Form D) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => pairing p.val (α.field p.val)
        (OrientationData.coordinateVector C.tangent.fiberCoordinates c hc p)) := by
  intro p
  have hs : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun q => ∑ I : Index n n, coefficients C n c hc α.field q I * wedgeWeight n I) p := by
    apply FrameData.VectorSmoothAt.sum
    intro I
    exact ((hcoeff C n D α.field).mp α.smooth c hc I p).postcomp
      (contDiff_id.mul contDiff_const)
  exact hs.congr (Filter.Eventually.of_forall fun q => (coordinate_pairing_expansion hexp α c hc q).symm)

theorem normalizationFactor_smooth
    (hexp : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u})
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    (g : Metric C) (α : NonvanishingTopForm D)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => normalizationFactor g α p.val) := by
  intro p
  have hs := (metric_coefficient_smooth g C.tangent.fiberCoordinates c hc p).prod
    (coordinate_pairing_smooth hexp hcoeff α.val c hc p)
  have hratio : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun q => Real.sqrt (metricMatrix g C.tangent.fiberCoordinates c hc q).det /
        |pairing q.val (α.val.field q.val)
          (OrientationData.coordinateVector C.tangent.fiberCoordinates c hc q)|) p := by
    apply hs.postcompOn (h := fun z : ℝ × ℝ => z.1 / |z.2|)
      (s := {z : ℝ × ℝ | z.2 ≠ 0})
      (isOpen_ne.preimage continuous_snd) (pairing_coordinate_ne_zero α _ c hc p)
    intro z hz
    exact contDiffWithinAt_fst.div (contDiffWithinAt_snd.abs hz) (abs_ne_zero.mpr hz)
  exact hratio.congr (Filter.Eventually.of_forall fun q =>
    (normalizationFactor_coordinates g α C.tangent.fiberCoordinates c hc q).symm)

theorem form_smul_smooth
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    (α : Form D) (f : M → ℝ)
    (hf : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
      VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
        (fun p => f p.val)) : IsForm D (fun p => f p • α.field p) := by
  apply (hcoeff C n D _).mpr
  intro c hc I p
  have hs := ((hf c hc p).prod ((hcoeff C n D α.field).mp α.smooth c hc I p)).postcomp
    (contDiff_fst.mul contDiff_snd)
  apply hs.congr
  filter_upwards [] with q
  simp [ExteriorData.coefficients, map_smul]

def normalizedForm
    (hexp : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u})
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    (g : Metric C) (α : NonvanishingTopForm D) : Form D :=
  ⟨fun p => normalizationFactor g α p • α.val.field p,
    form_smul_smooth hcoeff α.val _ (normalizationFactor_smooth hexp hcoeff g α)⟩

theorem normalizedForm_normalization
    (hexp : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u})
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    (g : Metric C) (o : Orientation S) (α : NonvanishingTopForm D)
    (hα : IsPositiveTopForm o.val α.val.field) :
    IsMetricVolume g o (normalizedForm hexp hcoeff g α) := by
  intro p v hv hn
  have h := normalizationFactor_pairing g α p v
  rw [abs_of_pos (hα p v hv), hn] at h
  simpa only [normalizedForm, pairing, map_smul, LinearMap.smul_apply, smul_eq_mul] using h

private theorem volume_exists_unique_core
    (hpositive : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (hcharts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (hexp : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.coefficient_expansionType.{u})
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u}) :
    Specs.SmoothManifolds.Orientations.MetricVolume.volume_exists_uniqueType.{u} := by
  intro n a M _ S C D g o
  obtain ⟨α, hα⟩ := (hpositive S C D o.val).mp o.property
  refine ⟨normalizedForm hexp hcoeff g α, normalizedForm_normalization hexp hcoeff g o α hα, ?_⟩
  intro β hβ
  obtain ⟨s, hs, _⟩ := (hcharts S o.val).mp o.property
  have he : β.field = (normalizedForm hexp hcoeff g α).field := by
    funext p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    exact (volume_coordinates_core S C D g o β hβ s hs C.tangent.fiberCoordinates c hc ⟨p, hp⟩).trans
      (volume_coordinates_core S C D g o (normalizedForm hexp hcoeff g α)
        (normalizedForm_normalization hexp hcoeff g o α hα) s hs C.tangent.fiberCoordinates c hc ⟨p, hp⟩).symm
  have form_ext : ∀ (β γ : Form D), β.field = γ.field → β = γ := by
    rintro ⟨f, hf⟩ ⟨j, hj⟩ h
    cases h
    rfl
  exact form_ext _ _ he

end Normalization

/-! Each public helper below has all upstream conditional premises in the
contract order. The original result names are reserved for dependency closure. -/
section Conditional
set_option linter.unusedVariables false

theorem density_line_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.density_lineType.{u} :=
  density_line_core

theorem gram_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.gramType.{u} :=
  gram_core

theorem volume_exists_unique_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.volume_exists_uniqueType.{u} :=
  volume_exists_unique_core h06 h07
    ExteriorAlgebraResults.coefficient_expansion ExteriorAlgebraResults.smooth_iff_coefficients

theorem volume_coordinates_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.volume_coordinatesType.{u} :=
  volume_coordinates_core

theorem overlap_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.overlapType.{u} :=
  overlap_core

theorem density_exists_unique_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.density_exists_uniqueType.{u} :=
  density_exists_unique_core

theorem orientation_reversal_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.orientation_reversalType.{u} :=
  orientation_reversal_core h07

theorem zero_dimension_conditional
    (h01 : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h02 : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h03 : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h04 : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h05 : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h06 : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h07 : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h08 : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h09 : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h10 : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h11 : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h12 : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.MetricVolume.zero_dimensionType.{u} :=
  zero_dimension_core

end Conditional

end SmoothManifolds.MetricVolumeResults

universe v8_closure_e700dc6324c6bdf0_u0
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«density_exists_unique» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«density_exists_uniqueType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«density_exists_unique_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«density_line» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«density_lineType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«density_line_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«gram» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«gramType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«gram_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«orientation_reversal» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«orientation_reversalType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«orientation_reversal_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«overlap» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«overlapType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«overlap_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«volume_coordinates» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«volume_coordinatesType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«volume_coordinates_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«volume_exists_unique» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«volume_exists_uniqueType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«volume_exists_unique_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
theorem _root_.«SmoothManifolds».«MetricVolumeResults».«zero_dimension» : _root_.«Specs».«SmoothManifolds».«Orientations».«MetricVolume».«zero_dimensionType».{v8_closure_e700dc6324c6bdf0_u0} :=
  @_root_.«SmoothManifolds».«MetricVolumeResults».«zero_dimension_conditional».{v8_closure_e700dc6324c6bdf0_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_e700dc6324c6bdf0_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_e700dc6324c6bdf0_u0})
