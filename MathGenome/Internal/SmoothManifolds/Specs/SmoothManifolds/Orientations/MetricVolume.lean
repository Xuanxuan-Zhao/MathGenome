import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Equivalences
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.BundleMetrics
import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent formulation of paper.tex, M09.04 (1764--1786).
The determinant metric is the exterior power of the given bilinear form.
Densities are absolute-homogeneous functions on the actual determinant line;
this is the absolute dual line, with no orientation chosen. Smoothness is
scalar smoothness in its canonical coordinate trivializations. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SmoothManifolds.MetricVolumeData
open ModelData AtlasData MapData TangentData TangentBundleData BundleOperationsData
  BundleMetricData OrientationData ExteriorData FrameData CovectorData PartitionData Module Set
universe u

abbrev Metric {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) :=
  letI := C.realization.space.topology
  SmoothFiberMetric C.realization.space.bundle

/-- Underlying bilinear form with the specified realization topology explicit. -/
def metricForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} (g : Metric C) (p : M) :
    LinearMap.BilinForm ℝ (TangentSpace S p) :=
  letI := C.realization.space.topology
  g.form p

/-- The induced determinant metric, rather than a supplied volume certificate. -/
def determinantMetric {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} (g : Metric C) (p : M) :
    LinearMap.BilinForm ℝ (DeterminantLine S p) := (metricForm g p).exteriorPower n

def determinantNorm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} (g : Metric C) (p : M)
    (v : DeterminantLine S p) : ℝ := Real.sqrt (determinantMetric g p v v)

/-- Absolute dual, as a real vector subspace of functions on the determinant line.
The defining condition includes zero scalars, so every density vanishes at zero. -/
def densitySubmodule (L : Type u) [AddCommGroup L] [Module ℝ L] :
    Submodule ℝ (L → ℝ) where
  carrier := {f | ∀ (t : ℝ) (v : L), f (t • v) = |t| * f v}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh t v
    change f (t • v) + h (t • v) = |t| * (f v + h v)
    rw [hf, hh, mul_add]
  smul_mem' := by
    intro t f hf s v
    change t * f (s • v) = |s| * (t * f v)
    rw [hf]
    ring

abbrev DensityLine {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) := densitySubmodule (DeterminantLine S p)

abbrev DensityField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) := (p : M) → DensityLine S p

def densityCoefficient {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    DensityLine S p.val →ₗ[ℝ] ℝ where
  toFun ρ := ρ.val (coordinateVector K c hc p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical density atlas: coefficients on ordered coordinate determinants. -/
def IsSmoothDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ρ : DensityField S) : Prop :=
  ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => densityCoefficient K c hc p (ρ p.val))

def IsPositiveDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ρ : DensityField S) : Prop :=
  ∀ p v, v ≠ 0 → 0 < (ρ p).val v

def IsMetricDensity {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} (g : Metric C)
    (ρ : DensityField S) : Prop :=
  ∀ p v, (ρ p).val v = determinantNorm g p v

/-- Normalization on *all* positive unit determinant vectors. -/
def IsMetricVolume {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {D : FormBundle C n}
    (g : Metric C) (o : Orientation S) (ω : Form D) : Prop :=
  ∀ p v, IsPositive (o.val p) v → determinantNorm g p v = 1 →
    pairing p (ω.field p) v = 1

/-- The actual coordinate Gram matrix. -/
def metricMatrix {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} (g : Metric C)
    (K : FiberCoordinates S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : c.source) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => metricForm g p.val
    ((K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) i))
    ((K.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) j)))

def coordinateTopForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    Fiber (TangentSpace S p.val) n :=
  exteriorPower.ιMulti ℝ n (fun j => coordinateCovector K c hc p.val p.property j)

def Opposite {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (o q : Orientation S) : Prop :=
  ∀ p, q.val p = -o.val p

end SmoothManifolds.MetricVolumeData

namespace Specs.SmoothManifolds.Orientations.MetricVolume
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.MetricVolumeData _root_.SmoothManifolds.PartitionData Set Module
universe u

/-- The absolute dual really is a line; its canonical coordinate maps use the
absolute determinant transition law. No metric or orientation is needed. -/
def density_lineType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (K : FiberCoordinates S),
    (∀ p, Module.finrank ℝ (DensityLine S p) = 1) ∧
    (∀ c hc (p : c.source), Function.Bijective (densityCoefficient K c hc p)) ∧
    ∀ (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source))
      (ρ : DensityLine S p.val),
      densityCoefficient K d hd ⟨p.val, p.property.2⟩ ρ =
        |transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩| *
          densityCoefficient K c hc ⟨p.val, p.property.1⟩ ρ

/-- Gram determinant formula, positivity, and smooth square root. -/
def gramType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (g : Metric C)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val),
    (∀ p : c.source,
      determinantNorm g p.val (coordinateVector K c hc p) =
        Real.sqrt (metricMatrix g K c hc p).det ∧ 0 < (metricMatrix g K c hc p).det) ∧
    FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source)
      (fun p => Real.sqrt (metricMatrix g K c hc p).det)

def volume_exists_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S), ∃! ω : Form D, IsMetricVolume g o ω

/-- Intrinsic normalization yields precisely the signed coordinate expression. -/
def volume_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S) (ω : Form D), IsMetricVolume g o ω →
    ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
    ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source), ω.field p.val =
      (signValue (s.sign c hc p) * Real.sqrt (metricMatrix g K c hc p).det) •
        coordinateTopForm K c hc p

/-- Both unsigned coefficients and signed forms agree on overlaps, with the
same direction x=x(y) as in the manuscript. -/
def overlapType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (g : Metric C)
    (K : FiberCoordinates S) (s : SignedCharts S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)),
    let pc : c.source := ⟨p.val, p.property.1⟩
    let pd : d.source := ⟨p.val, p.property.2⟩
    Real.sqrt (metricMatrix g K d hd pd).det =
      |transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩| *
        Real.sqrt (metricMatrix g K c hc pc).det ∧
    (signValue (s.sign c hc pc) * Real.sqrt (metricMatrix g K c hc pc).det) •
        coordinateTopForm K c hc pc =
      (signValue (s.sign d hd pd) * Real.sqrt (metricMatrix g K d hd pd).det) •
        coordinateTopForm K d hd pd

/-- Intrinsic metric density, including positivity, smoothness, nonvanishing and
its unsigned coordinate formula, on arbitrary (possibly nonorientable) M. -/
def density_exists_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (g : Metric C),
    ∃! ρ : DensityField S, IsMetricDensity g ρ ∧ IsSmoothDensity ρ ∧
      IsPositiveDensity ρ ∧ (∀ p, ρ p ≠ 0) ∧
      ∀ (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
        (p : c.source), densityCoefficient K c hc p (ρ p.val) =
          Real.sqrt (metricMatrix g K c hc p).det

/-- Reversal negates the normalized form; its absolute pairing is the same
metric density for either orientation. Existence of the opposite is included. -/
def orientation_reversalType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (g : Metric C) (o : Orientation S),
    ∃ q : Orientation S, Opposite o q ∧
      ∀ (α β : Form D), IsMetricVolume g o α → IsMetricVolume g q β →
        (∀ p, β.field p = -α.field p) ∧
        ∀ (ρ : DensityField S), IsMetricDensity g ρ → ∀ p v,
          |pairing p (α.field p) v| = (ρ p).val v ∧
          |pairing p (β.field p) v| = (ρ p).val v

/-- Empty determinants are one; the form retains the independently assigned
point sign, whereas the density takes value one on the canonical 1. -/
def zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (C : CotangentBundle S) (D : FormBundle C 0)
    (g : Metric C) (o : Orientation S) (ω : Form D) (ρ : DensityField S),
    IsMetricVolume g o ω → IsMetricDensity g ρ →
    ∀ (s : SignedCharts S), RepresentsSignedCharts o.val s →
    ∀ (K : FiberCoordinates S) (c : ModelChart 0 a M) (hc : c ∈ S.smoothStructure.val)
      (p : c.source),
      let one := (exteriorPower.zeroEquiv ℝ (TangentSpace S p.val)).symm 1
      (metricMatrix g K c hc p).det = 1 ∧ determinantNorm g p.val one = 1 ∧
        pairing p.val (ω.field p.val) one = signValue (s.sign c hc p) ∧
        (ρ p.val).val one = 1

end Specs.SmoothManifolds.Orientations.MetricVolume
