import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussWeingarten
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra

/-! Theorem 7.5 (paper.tex 3758–3806). The normal connection and all lifted
vectors live over the source of the immersion, with no global injectivity or
codimension restriction. Curvature is the commutator of actual connections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.CurvatureEquationsData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GaussWeingartenData
universe u v w

/-- Actual curvature of an arbitrary vector-bundle connection. -/
noncomputable def bundleCurvature
    {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (D : Connection B)
    (X Y : Field S) (s : Section B) : Section B :=
  D.cov X (D.cov Y s) - D.cov Y (D.cov X s) -
    D.cov (P202.TorsionMetricData.bracket X Y) s

/-- First-order Gauss–Weingarten data on two actual smooth bundles.
Curvature equations are not fields of this structure. -/
structure GeometryData
    {n r k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {κ : Type v}
    {E : M → Type w} {H : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [∀ p, AddCommGroup (H p)] [∀ p, Module ℝ (H p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean k) H)]
    (PB : SmoothVectorBundle S r ι E) (NB : SmoothVectorBundle S k κ H)
    (d : (p : M) → TangentSpace S p →ₗ[ℝ] E p)
    (j : (p : M) → H p →ₗ[ℝ] E p)
    (g : RiemannianMetric S) (h : SmoothFiberMetric PB)
    (C : Connection (tangentBundle S)) (D : Connection PB) where
  CN : Connection NB
  second : Field S →ₗ[ℝ] Field S →ₗ[ℝ] Section NB
  shape : Section NB →ₗ[ℝ] Field S →ₗ[ℝ] Field S
  tangentLift : Field S →ₗ[ℝ] Section PB
  normalLift : Section NB →ₗ[ℝ] Section PB
  tangentLift_val : ∀ X p, (tangentLift X).val p = d p (X.val p)
  normalLift_val : ∀ s p, (normalLift s).val p = j p (s.val p)
  B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] H p
  A : (p : M) → H p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace S p
  second_val : ∀ X Y p, (second X Y).val p = B p (X.val p) (Y.val p)
  shape_val : ∀ s X p, (shape s X).val p = A p (s.val p) (X.val p)
  gauss : ∀ X Y, D.cov X (tangentLift Y) = tangentLift (C.cov X Y) + normalLift (second X Y)
  weingarten : ∀ X s, D.cov X (normalLift s) =
    (-1 : ℝ) • tangentLift (shape s X) + normalLift (CN.cov X s)
  symmetric : ∀ p v w, B p v w = B p w v
  adjoint : ∀ p xi v w, pairing g p (A p xi v) w = h.form p (j p (B p v w)) (j p xi)
  selfAdjoint : ∀ p xi v w, pairing g p (A p xi v) w = pairing g p v (A p xi w)

section Immersion
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)
/-- The first-order geometry on the prescribed actual bundles. -/
abbrev Geometry (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (D : letI := P.space.topology; Connection P.space.bundle) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  exact GeometryData P.space.bundle W.orthogonal.right.bundle
    i.differential (fun p => (SmoothManifolds.MetricSplittingData.orthogonal
      P.space.bundle hP (tangentImage i) p).subtype) g hP C D

variable {i P hP W}
/-- Normal curvature is the actual curvature of the normal connection. -/
noncomputable def normalCurvature {g : RiemannianMetric S}
    {C : Connection (tangentBundle S)} {D : letI := P.space.topology; Connection P.space.bundle}
    (G : Geometry i P hP W g C D) (X Y : Field S)
    (xi : letI := P.space.topology; letI := W.orthogonal.right.topology;
      Section W.orthogonal.right.bundle) :
    letI := P.space.topology; letI := W.orthogonal.right.topology;
      Section W.orthogonal.right.bundle := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  exact bundleCurvature G.CN X Y xi

/-- Covariant derivative of B, using CN on its value and C on both inputs. -/
noncomputable def covariantB {g : RiemannianMetric S}
    {C : Connection (tangentBundle S)} {D : letI := P.space.topology; Connection P.space.bundle}
    (G : Geometry i P hP W g C D) (X Y Z : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology;
      Section W.orthogonal.right.bundle := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  exact G.CN.cov X (G.second Y Z) - G.second (C.cov X Y) Z - G.second Y (C.cov X Z)

/-- All three equations in actual pullback fibers. The separate naturality
statement below identifies this ambient pullback curvature with Rbar(dF X,dF Y).
The field formulation quantifies over every smooth field; arbitrary fiber
values admit smooth extensions by the accepted section extension theorem. -/
def Equations {g : RiemannianMetric S} {C : Connection (tangentBundle S)}
    {D : letI := P.space.topology; Connection P.space.bundle} (G : Geometry i P hP W g C D) : Prop := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  exact (∀ (X Y Z V : Field S) (p : M),
    pairing g p ((bundleCurvature C X Y Z).val p) (V.val p) =
      hP.form p ((bundleCurvature D X Y (G.tangentLift Z)).val p)
        (i.differential p (V.val p)) +
      hP.form p (G.B p (X.val p) (V.val p)).val (G.B p (Y.val p) (Z.val p)).val -
      hP.form p (G.B p (Y.val p) (V.val p)).val (G.B p (X.val p) (Z.val p)).val) ∧
  (∀ (X Y Z : Field S) (p : M),
    ((W.iso.equiv p).symm ((bundleCurvature D X Y (G.tangentLift Z)).val p)).2 =
      (covariantB G X Y Z - covariantB G Y X Z).val p) ∧
  (∀ (X Y : Field S) (xi eta : Section W.orthogonal.right.bundle) (p : M),
    hP.form p ((normalCurvature G X Y xi).val p).val (eta.val p).val =
      hP.form p ((bundleCurvature D X Y (G.normalLift xi)).val p) (eta.val p).val +
      pairing g p
        (G.A p (xi.val p) (G.A p (eta.val p) (X.val p)) -
         G.A p (eta.val p) (G.A p (xi.val p) (X.val p))) (Y.val p))
/-- The source equations with ambient curvature explicitly evaluated on dF.
Both curvature tensors are arbitrary representatives of their connections. -/
def AmbientEquations {g : RiemannianMetric S} {C : Connection (tangentBundle S)}
    {D : letI := P.space.topology; Connection P.space.bundle}
    (G : Geometry i P hP W g C D)
    (R₀ : P202.CurvatureData.CurvatureTensor S)
    (R : P202.CurvatureData.CurvatureTensor T) : Prop := by
  letI := P.space.topology; letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  exact (∀ (X Y Z V : Field S) (p : M),
    P202.CurvatureData.curvatureForm g R₀ p (X.val p) (Y.val p) (Z.val p) (V.val p) =
      hP.form p (R.val (F p) (i.differential p (X.val p))
        (i.differential p (Y.val p)) (i.differential p (Z.val p)))
        (i.differential p (V.val p)) +
      hP.form p (G.B p (X.val p) (V.val p)).val (G.B p (Y.val p) (Z.val p)).val -
      hP.form p (G.B p (Y.val p) (V.val p)).val (G.B p (X.val p) (Z.val p)).val) ∧
  (∀ (X Y Z : Field S) (p : M),
    ((W.iso.equiv p).symm (R.val (F p) (i.differential p (X.val p))
      (i.differential p (Y.val p)) (i.differential p (Z.val p)))).2 =
      (covariantB G X Y Z - covariantB G Y X Z).val p) ∧
  (∀ (X Y : Field S) (xi eta : Section W.orthogonal.right.bundle) (p : M),
    hP.form p ((normalCurvature G X Y xi).val p).val (eta.val p).val =
      hP.form p (R.val (F p) (i.differential p (X.val p))
        (i.differential p (Y.val p)) (xi.val p).val) (eta.val p).val +
      pairing g p
        (G.A p (xi.val p) (G.A p (eta.val p) (X.val p)) -
         G.A p (eta.val p) (G.A p (xi.val p) (X.val p))) (Y.val p))

end Immersion
end P202.CurvatureEquationsData

namespace P202Specs.Geometry.GaussCodazziRicci
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleMetricData P202.ConnectionData P202.MetricData
  P202.LeviCivitaData P202.GaussWeingartenData P202.CurvatureData
  P202.CurvatureEquationsData
universe u

/-- Curvature naturality for every immersion, with arbitrary smooth sections
of its ambient pullback bundle (in particular tangent and normal sections). -/
def pullback_curvatureType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M → N} (i : SmoothImmersion S T F)
    (K : Connection (tangentBundle T)) (R : CurvatureTensor T),
    IsTorsionFree K → RepresentsCurvature K R →
    ∀ P : PullbackBundle (tangentBundle T) S F,
    letI := P.space.topology
    ∀ D : Connection P.space.bundle,
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D →
    ∀ (X Y : Field S) (s : Section P.space.bundle) (p : M),
      (bundleCurvature D X Y s).val p =
        R.val (F p) (i.differential p (X.val p)) (i.differential p (Y.val p)) (s.val p)

/-- The equations for every representative of the first-order data established
by Gauss–Weingarten. No curvature formula is a hypothesis. -/
def equationsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M → N} (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F),
    letI := P.space.topology
    ∀ (hP : SmoothFiberMetric P.space.bundle) (W : AdaptedSplitting i P hP)
      (g : RiemannianMetric S) (C : Connection (tangentBundle S))
      (D : Connection P.space.bundle),
    IsLeviCivita g C →
    (∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w) →
    ∀ G : Geometry i P hP W g C D, Equations G

/-- Existence of the first-order data used in equationsType, for each isometric
immersion and arbitrary intrinsic/ambient Levi–Civita representatives. -/
def geometry_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (F : M → N) (i : SmoothImmersion S T F)
    (hi : IsMetricPreserving g h F i.differential)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
    IsLeviCivita g C → IsLeviCivita h K →
    ∀ P : PullbackBundle (tangentBundle T) S F,
    letI := P.space.topology
    ∃ (hP : SmoothFiberMetric P.space.bundle)
      (D : Connection P.space.bundle) (W : AdaptedSplitting i P hP),
      (∀ p, hP.form p = h.form (F p)) ∧
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D ∧
      Nonempty (Geometry i P hP W g C D)

/-- Full Theorem 7.5: existence of the geometry and all three ambient equations
for every isometric immersion, in every codimension. No normal frame, ambient
flatness or embedding is assumed. -/
def curvature_equationsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (F : M → N) (i : SmoothImmersion S T F)
    (hi : IsMetricPreserving g h F i.differential)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T)),
    IsLeviCivita g C → IsLeviCivita h K →
    ∀ (R₀ : CurvatureTensor S) (R : CurvatureTensor T),
    RepresentsCurvature C R₀ → RepresentsCurvature K R →
    ∀ P : PullbackBundle (tangentBundle T) S F,
    letI := P.space.topology
    ∃ (hP : SmoothFiberMetric P.space.bundle)
      (D : Connection P.space.bundle) (W : AdaptedSplitting i P hP)
      (G : Geometry i P hP W g C D),
      (∀ p, hP.form p = h.form (F p)) ∧
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D ∧
      AmbientEquations G R₀ R

end P202Specs.Geometry.GaussCodazziRicci
