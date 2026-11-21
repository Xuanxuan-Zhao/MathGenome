import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TorsionAndMetric
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionCalculus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Independent statements of Theorem 6.3 (paper.tex 3086–3132).
All fibers, smooth sections, connections, metrics and differentials are the
canonical upstream objects. A connection takes smooth fields to smooth fields;
thus existence here includes smoothness, rather than only pointwise existence.
The model kind and dimension, including dimension zero, are unrestricted. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.LeviCivitaData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.TorsionMetricData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

def IsTorsionFree (C : Connection (tangentBundle S)) : Prop :=
  ∀ X Y : Field S, torsion C X Y = 0

def IsMetricCompatible (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) : Prop :=
  ∀ (X Y Z : Field S) (p : M),
    scalarDerivative S (fun q => pairing g q (Y.val q) (Z.val q)) p (X.val p) =
      pairing g p ((C.cov X Y).val p) (Z.val p) +
        pairing g p (Y.val p) ((C.cov X Z).val p)

def IsLeviCivita (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) : Prop :=
  IsTorsionFree C ∧ IsMetricCompatible g C

noncomputable def koszulRHS (g : RiemannianMetric S) (X Y Z : Field S) (p : M) : ℝ :=
  scalarDerivative S (fun q => pairing g q (Y.val q) (Z.val q)) p (X.val p) +
  scalarDerivative S (fun q => pairing g q (Z.val q) (X.val q)) p (Y.val p) -
  scalarDerivative S (fun q => pairing g q (X.val q) (Y.val q)) p (Z.val p) -
  pairing g p (X.val p) ((bracket Y Z).val p) +
  pairing g p (Y.val p) ((bracket Z X).val p) +
  pairing g p (Z.val p) ((bracket X Y).val p)

noncomputable def coordinateVector
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (j : Fin n) (p : M) : TangentSpace S p :=
  ((tangentBundle S).trivialization c).symm p (Pi.single j 1)

noncomputable def metricMatrix (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (p : M) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => pairing g p (coordinateVector c i p) (coordinateVector c j p)

noncomputable def christoffel (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (k i j : Fin n) : ℝ :=
  connectionForm C (SmoothManifolds.ConstantRankBundles.trivializationFrame
    (tangentBundle S) c) p k j (coordinateVector c i p.val)

end P202.LeviCivitaData

namespace P202Specs.Geometry.LeviCivita
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
universe u

def exists_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    ∃! C : Connection (tangentBundle S), IsLeviCivita g C

def uniquenessType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C D : Connection (tangentBundle S)),
    IsLeviCivita g C → IsLeviCivita g D → C = D

def koszul_formulaType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (X Y Z : Field S) (p : M),
      2 * pairing g p ((C.cov X Y).val p) (Z.val p) = koszulRHS g X Y Z p

def christoffel_formulaType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
      (p : (tangentBundle S).baseSet c) (k i j : Fin n),
    christoffel C c p k i j = (1 / 2 : ℝ) * ∑ l : Fin n,
      (metricMatrix g c p.val)⁻¹ k l *
        (scalarDerivative S (fun q => metricMatrix g c q j l) p.val
            (coordinateVector c i p.val) +
         scalarDerivative S (fun q => metricMatrix g c q i l) p.val
            (coordinateVector c j p.val) -
         scalarDerivative S (fun q => metricMatrix g c q i j) p.val
            (coordinateVector c l p.val))

/-- The differential of a local isometry is parallel as a map into the
pullback tangent bundle. Existence of the pushed smooth section is included;
the connection D is any actual pullback connection, not extra geometric data.
This formulation applies without global injectivity or surjectivity of f. -/
def localIsometry_intertwinesType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
    IsLeviCivita g C → IsLeviCivita h K →
    ∀ (f : M → N), IsLocalIsometry g h f →
    ∀ (hf : IsSmoothMap S T f)
      (P : SmoothManifolds.BundleOperationsData.PullbackBundle (tangentBundle T) S f),
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle),
      P202.PullbackData.IsPullback (tangentBundle T) K f hf P D →
    ∀ Y : Field S, ∃ t : Section P.space.bundle,
      (∀ q, t.val q = SmoothManifolds.differential S T f hf q (Y.val q)) ∧
      ∀ (X : Field S) (p : M),
        (D.cov X t).val p =
          SmoothManifolds.differential S T f hf p ((C.cov X Y).val p)

end P202Specs.Geometry.LeviCivita
