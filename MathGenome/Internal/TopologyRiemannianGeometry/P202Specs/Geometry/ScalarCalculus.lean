import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RiemannianVolume
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.MetricSplittings
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Covectors
import Mathlib.LinearAlgebra.Trace

/-! Independent scalar differential calculus statements for paper.tex 3246–3257,
3272–3281, with the sign convention on lines 95–96. All tangent and cotangent
fibers are the fixed upstream fibers. The metric musical isomorphism and the
smooth differential used in the gradient are proved library constructions.
Connections are explicit arguments; independence of the Levi–Civita choice is
an obligation below. No orientation, compactness or positive dimension is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
noncomputable section

namespace P202.ScalarData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- The metric identification of the tangent fiber with its actual linear dual. -/
def musical (g : RiemannianMetric S) (p : M) :
    TangentSpace S p ≃ₗ[ℝ] Module.Dual ℝ (TangentSpace S p) :=
  SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p

/-- Gradient as a smooth field, obtained by applying the smooth inverse metric
map to the genuine differential of the given smooth function. -/
def gradient (g : RiemannianMetric S) (u : GlobalSmooth S) : Field S := by
  let D := P202.VolumeData.cotangentBundle S
  let hu := (SmoothManifolds.mem_globalSmoothAlgebra_iff S u.val).mp u.property
  let du := SmoothManifolds.CovectorData.dFunction S u.val hu
  let e := SmoothManifolds.MetricSplittings.metricIso (tangentBundle S) g D.dual
  refine ⟨fun p => (musical g p).symm (du p), ?_⟩
  intro p
  exact SmoothManifolds.manifoldContDiffAt_comp
    D.dual.space.bundle.totalManifold.smoothStructure.property.1.1
    (SmoothManifolds.Covectors.differential_smooth S D u.val hu p)
    (e.inverse_smooth ⟨p, du p⟩)

/-- Hessian as a bilinear form on full intrinsic tangent fibers. -/
def hessian (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (u : GlobalSmooth S) (p : M) : LinearMap.BilinForm ℝ (TangentSpace S p) :=
  (pairing g p).compl₁₂ (pointDerivative C (gradient g u).val p) LinearMap.id

/-- Divergence is the algebraic trace of the tangent-linear covariant derivative. -/
def divergence (C : Connection (tangentBundle S)) (X : Field S) (p : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace S p) (pointDerivative C X.val p)

/-- Positive divergence-of-gradient convention of the source. -/
def laplacian (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (u : GlobalSmooth S) (p : M) : ℝ := divergence C (gradient g u) p

/-- Metric trace contracts a bilinear form with the inverse metric. -/
def metricTrace (g : RiemannianMetric S) (p : M)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p)) : ℝ :=
  LinearMap.trace ℝ (TangentSpace S p) ((musical g p).symm.toLinearMap.comp B)

/-- Total chart coefficient; assertions below are only on the open chart source. -/
def component (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (X : Field S) (i : Fin n) (p : M) : ℝ :=
  (((tangentBundle S).trivialization c) ⟨p, X.val p⟩).2 i

/-- Intrinsic coordinate directional derivative, including at genuine boundary points. -/
def coordinateDerivative (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (i : Fin n) (f : M → ℝ) (p : M) : ℝ :=
  scalarDerivative S f p (coordinateVector c i p)

def rho (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (p : M) : ℝ :=
  Real.sqrt (metricMatrix g c p).det

end P202.ScalarData

namespace P202Specs.Geometry.ScalarCalculus
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
universe u

def gradient_characterizationType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (u : GlobalSmooth S)
    (p : M) (v : TangentSpace S p),
    pairing g p ((gradient g u).val p) v = scalarDerivative S u.val p v

def hessian_covariantType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (u : GlobalSmooth S)
    (X Y : Field S) (p : M),
    hessian g C u p (X.val p) (Y.val p) =
      pairing g p ((C.cov X (gradient g u)).val p) (Y.val p)

def hessian_formulaType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (u : GlobalSmooth S) (X Y : Field S) (p : M),
    hessian g C u p (X.val p) (Y.val p) =
      (act S X (act S Y u)).val p - (act S (C.cov X Y) u).val p

def hessian_symmetryType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (u : GlobalSmooth S) (p : M) (v w : TangentSpace S p),
    hessian g C u p v w = hessian g C u p w v

/-- The defining trace identity is valid for every smooth connection. -/
def laplacian_traceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (u : GlobalSmooth S) (p : M),
    laplacian g C u p = metricTrace g p (hessian g C u p)

def gradient_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (u : GlobalSmooth S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (i : Fin n),
    component c (gradient g u) i p.val = ∑ j : Fin n,
      (metricMatrix g c p.val)⁻¹ i j * coordinateDerivative c j u.val p.val

def divergence_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (X : Field S) (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c),
    divergence C X p.val = (rho g c p.val)⁻¹ * ∑ i : Fin n,
      coordinateDerivative c i (fun q => rho g c q * component c X i q) p.val

def laplacian_coordinatesType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (u : GlobalSmooth S) (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c),
    laplacian g C u p.val = (rho g c p.val)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
      coordinateDerivative c i (fun q => rho g c q * (metricMatrix g c q)⁻¹ i j *
        coordinateDerivative c j u.val q) p.val

/-- The g-dependent objects do not depend on which Levi–Civita connection
realizes them; together with existence this makes their definitions intrinsic. -/
def connection_independenceType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    (∃ C : Connection (tangentBundle S), IsLeviCivita g C) ∧
    ∀ C D : Connection (tangentBundle S), IsLeviCivita g C → IsLeviCivita g D →
      (∀ (u : GlobalSmooth S) (p : M), hessian g C u p = hessian g D u p) ∧
      (∀ (X : Field S) (p : M), divergence C X p = divergence D X p) ∧
      (∀ (u : GlobalSmooth S) (p : M), laplacian g C u p = laplacian g D u p)

end P202Specs.Geometry.ScalarCalculus
