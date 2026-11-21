import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussCodazziRicci
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Corollary 7.6, paper.tex 3808–3828. All vectors below belong to the
intrinsic tangent fibers and to the actual orthogonal normal subspaces.
No global normal, orientation, embedding, or orthonormal parametrization is
part of these definitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.EgregiumData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GaussWeingartenData
  P202.CurvatureData P202.CurvatureEquationsData
universe u

noncomputable def firstFormMatrix {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (g : RiemannianMetric S) (p : M) (e : Module.Basis (Fin 2) ℝ (TangentSpace S p)) :
    Matrix (Fin 2) (Fin 2) ℝ := fun j k => pairing g p (e j) (e k)

/-- The standard Euclidean metric, described in an actual global identity
chart on Euclidean space. This is a metric-coefficient condition, not a
curvature or connection certificate. -/
def StandardEuclideanMetric {n : ℕ}
    (T : SmoothManifold n .euclidean (SmoothManifolds.ModelData.Euclidean n))
    (h : RiemannianMetric T) : Prop :=
  ∃ c : SmoothManifolds.BundleOperationsData.TangentIndex T,
    c.val.source = Set.univ ∧
    (∀ x, (c.val x).val = x) ∧
    ∀ p, metricMatrix h c p = 1

section Surface
variable {a b : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold 2 a M} {T : SmoothManifold 3 b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)
  {g : RiemannianMetric S} {C : Connection (tangentBundle S)}
  {D : letI := P.space.topology; Connection P.space.bundle}

/-- The ambient bilinear form, with the prescribed pullback topology explicit. -/
abbrev ambientForm (p : M) : LinearMap.BilinForm ℝ (TangentSpace T (F p)) := by
  letI := P.space.topology
  exact hP.form p

abbrev NormalFiber (p : M) : Submodule ℝ (TangentSpace T (F p)) := by
  letI := P.space.topology
  exact SmoothManifolds.MetricSplittingData.orthogonal P.space.bundle hP (tangentImage i) p

noncomputable abbrev secondTensor (G : Geometry i P hP W g C D) (p : M) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  exact G.B p

noncomputable abbrev shapeOperator (G : Geometry i P hP W g C D) (p : M) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  exact G.A p

noncomputable def scalarSecondForm (G : Geometry i P hP W g C D)
    (p : M) (ν : NormalFiber i P hP p) (v w : TangentSpace S p) : ℝ :=
  ambientForm P hP p (secondTensor i P hP W G p v w).val ν.val

noncomputable def secondFormMatrix (G : Geometry i P hP W g C D)
    (p : M) (ν : NormalFiber i P hP p)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace S p)) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun j k => scalarSecondForm i P hP W G p ν (e j) (e k)

/-- The full fiberwise conclusion. Because it holds for every unit normal at
every point it applies to each chosen smooth normal on each open patch,
without imposing existence of a global normal. A basis includes the derivative
basis of every regular parametrization. -/
def SurfaceFormula (G : Geometry i P hP W g C D) (R : CurvatureTensor S) : Prop :=
  ∀ (p : M) (ν : NormalFiber i P hP p), ambientForm P hP p ν.val ν.val = 1 →
  ∀ e : Module.Basis (Fin 2) ℝ (TangentSpace S p),
    ∀ he : LinearIndependent ℝ ![e 0, e 1],
    0 < (firstFormMatrix g p e).det ∧
    sectionalCurvature g R p (e 0) (e 1) he = LinearMap.det (A := ℝ) (M := TangentSpace S p) (shapeOperator i P hP W G p ν) ∧
    sectionalCurvature g R p (e 0) (e 1) he =
      (secondFormMatrix i P hP W G p ν e).det / (firstFormMatrix g p e).det ∧
    LinearMap.det (A := ℝ) (M := TangentSpace S p) (shapeOperator i P hP W G p ((-1 : ℝ) • ν)) = LinearMap.det (A := ℝ) (M := TangentSpace S p) (shapeOperator i P hP W G p ν) ∧
    (secondFormMatrix i P hP W G p ((-1 : ℝ) • ν) e).det =
      (secondFormMatrix i P hP W G p ν e).det

end Surface
end P202.EgregiumData

namespace P202Specs.Geometry.TheoremaEgregium
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GaussWeingartenData
  P202.CurvatureData P202.CurvatureEquationsData P202.EgregiumData
universe u

/-- Positive denominator in every regular tangent basis. -/
def firstForm_det_posType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M)
    (e : Module.Basis (Fin 2) ℝ (TangentSpace S p)), 0 < (firstFormMatrix g p e).det

/-- Pointwise version for a flat ambient three-manifold. The ambient flatness
hypothesis is an intermediate generalization; Euclidean specialization still
requires establishing it for the standard Euclidean metric. -/
def flat_surface_formulaType : Prop :=
  ∀ {a b : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 2 a M} {T : SmoothManifold 3 b N}
    {F : M → N} (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F),
    letI := P.space.topology
    ∀ (hP : SmoothFiberMetric P.space.bundle) (W : AdaptedSplitting i P hP)
      (g : RiemannianMetric S) (C : Connection (tangentBundle S))
      (K : Connection (tangentBundle T)) (D : Connection P.space.bundle),
    IsLeviCivita g C → IsTorsionFree K →
    (∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w) →
    P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D →
    ∀ (R₀ : CurvatureTensor S) (R : CurvatureTensor T),
    RepresentsCurvature C R₀ → RepresentsCurvature K R →
    (∀ p v w z, R.val (F p) v w z = 0) →
    ∀ G : Geometry i P hP W g C D, SurfaceFormula i P hP W G R₀

/-- The original Euclidean surface statement, including existence of the
actual normal geometry. All local normals and all regular bases are quantified
by SurfaceFormula; no global normal or injectivity of F is assumed. -/
def euclidean_surface_formulaType : Prop :=
  ∀ {a : ModelKind} {M : Type} [TopologicalSpace M]
    {S : SmoothManifold 2 a M}
    {T : SmoothManifold 3 .euclidean (SmoothManifolds.ModelData.Euclidean 3)}
    (g : RiemannianMetric S) (h : RiemannianMetric T),
    StandardEuclideanMetric T h →
    ∀ (F : M → SmoothManifolds.ModelData.Euclidean 3) (i : SmoothImmersion S T F),
    IsMetricPreserving g h F i.differential →
    ∀ (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
    IsLeviCivita g C → IsLeviCivita h K →
    ∀ (R₀ : CurvatureTensor S) (R : CurvatureTensor T),
    RepresentsCurvature C R₀ → RepresentsCurvature K R →
    ∀ P : PullbackBundle (tangentBundle T) S F,
    letI := P.space.topology
    ∃ (hP : SmoothFiberMetric P.space.bundle) (D : Connection P.space.bundle)
      (W : AdaptedSplitting i P hP) (G : Geometry i P hP W g C D),
      (∀ p, hP.form p = h.form (F p)) ∧
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D ∧
      SurfaceFormula i P hP W G R₀

/-- Intrinsic curvature is preserved by every local isometry. The independent
pairs and their images specify the same sectional plane under the actual
differential. This applies in particular to induced surface metrics. -/
def localIsometry_curvatureType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
    IsLeviCivita g C → IsLeviCivita h K →
    ∀ (R₀ : CurvatureTensor S) (R : CurvatureTensor T),
    RepresentsCurvature C R₀ → RepresentsCurvature K R →
    ∀ (f : M → N), IsLocalIsometry g h f →
    ∀ (hf : SmoothManifolds.MapData.IsSmoothMap S T f)
      (p : M) (v w : TangentSpace S p) (hv : LinearIndependent ℝ ![v, w])
      , ∃ hw : LinearIndependent ℝ ![SmoothManifolds.differential S T f hf p v,
        SmoothManifolds.differential S T f hf p w],
      sectionalCurvature g R₀ p v w hv = sectionalCurvature h R (f p)
        (SmoothManifolds.differential S T f hf p v)
        (SmoothManifolds.differential S T f hf p w) hw

end P202Specs.Geometry.TheoremaEgregium
