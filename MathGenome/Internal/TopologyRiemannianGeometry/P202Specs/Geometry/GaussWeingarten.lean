import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LeviCivita
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.MetricSplittings

/-! Proposition 7.4, paper.tex 3717–3756.
The bundles are over the source of the immersion; global injectivity is absent.
The normal fibers below are actual orthogonal subspaces in the pullback tangent
fibers. Connections and smoothness use the shared P104 realization throughout.
The existence statement includes the geometric constructions, not certificates
supplied as additional hypotheses. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.GaussWeingartenData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  SmoothManifolds.MetricSplittingData SmoothManifolds.ConstantRankData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N}

def tangentImage (i : SmoothImmersion S T F) (p : M) :
    Submodule ℝ (TangentSpace T (F p)) := LinearMap.range (i.differential p)

/-- Smooth orthogonal splitting with the left factor identified with the
original source tangent bundle by dF. Its inverse gives both projections. -/
structure AdaptedSplitting (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F)
    (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle) where
  orthogonal : letI := P.space.topology
    OrthogonalSplitting P.space.bundle hP (tangentImage i) n
  sum : letI := P.space.topology; letI := orthogonal.right.topology
    DirectSumBundle (tangentBundle S) orthogonal.right.bundle
  iso : letI := P.space.topology; letI := orthogonal.right.topology
    letI := sum.space.topology
    SmoothBundleIso sum.space.bundle P.space.bundle
  canonical : letI := P.space.topology; letI := orthogonal.right.topology
    letI := sum.space.topology
    ∀ p v, iso.equiv p v = i.differential p v.1 + v.2.val

section Constructions
variable (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)

/-- Type of the entire conclusion. The projection definitions refer to the
inverse of the actual smooth canonical sum isomorphism. -/
def GaussWeingartenConclusion (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (D : letI := P.space.topology; Connection P.space.bundle)
    (W : AdaptedSplitting i P hP) : Prop := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  let NB := W.orthogonal.right.bundle
  let normal := fun p => SmoothManifolds.MetricSplittingData.orthogonal
    P.space.bundle hP (tangentImage i) p
  let tanProj := fun p => (LinearMap.fst ℝ (TangentSpace S p) (normal p)).comp
    (W.iso.equiv p).symm.toLinearMap
  let norProj := fun p => (LinearMap.snd ℝ (TangentSpace S p) (normal p)).comp
    (W.iso.equiv p).symm.toLinearMap
  exact ∃ (CT : Connection (tangentBundle S)) (CN : Connection NB)
      (hN : SmoothFiberMetric NB)
      (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] normal p)
      (A : (p : M) → normal p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace S p),
    CT = C ∧
    (∀ p v w, hN.form p v w = hP.form p v.val w.val) ∧
    P202.TorsionMetricData.MetricCompatible NB CN hN ∧
    (∀ X Y : Field S, ∃ V : Section P.space.bundle,
      (∀ p, V.val p = i.differential p (Y.val p)) ∧
      (∀ p, (CT.cov X Y).val p = tanProj p ((D.cov X V).val p)) ∧
      (∀ p, B p (X.val p) (Y.val p) = norProj p ((D.cov X V).val p)) ∧
      (∀ p, (D.cov X V).val p =
        i.differential p ((C.cov X Y).val p) + (B p (X.val p) (Y.val p)).val)) ∧
    (∀ X : Field S, ∀ xi : Section NB, ∃ U : Section P.space.bundle,
      (∀ p, U.val p = (xi.val p).val) ∧
      (∀ p, (CN.cov X xi).val p = norProj p ((D.cov X U).val p)) ∧
      (∀ p, A p (xi.val p) (X.val p) = -tanProj p ((D.cov X U).val p)) ∧
      (∀ p, (D.cov X U).val p =
        -i.differential p (A p (xi.val p) (X.val p)) + ((CN.cov X xi).val p).val)) ∧
    (∀ X Y : Field S, SmoothManifolds.SectionExtensionData.SmoothSection NB
      (fun p => B p (X.val p) (Y.val p))) ∧
    (∀ (xi : Section NB) (X : Field S),
      SmoothManifolds.SectionExtensionData.SmoothSection (tangentBundle S)
        (fun p => A p (xi.val p) (X.val p))) ∧
    (∀ p v w, B p v w = B p w v) ∧
    (∀ p xi v w, pairing g p (A p xi v) w = hP.form p (B p v w).val xi.val) ∧
    (∀ p xi v w, pairing g p (A p xi v) w = pairing g p v (A p xi w))


/-- The bundle/connection part of Proposition 7.4, before descending the
second fundamental operation to a tensor on individual fibers. -/
def ProjectedConnectionsConclusion
    (C : Connection (tangentBundle S))
    (D : letI := P.space.topology; Connection P.space.bundle)
    (W : AdaptedSplitting i P hP) : Prop := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  let NB := W.orthogonal.right.bundle
  let normal := fun p => SmoothManifolds.MetricSplittingData.orthogonal
    P.space.bundle hP (tangentImage i) p
  let tanProj := fun p => (LinearMap.fst ℝ (TangentSpace S p) (normal p)).comp
    (W.iso.equiv p).symm.toLinearMap
  let norProj := fun p => (LinearMap.snd ℝ (TangentSpace S p) (normal p)).comp
    (W.iso.equiv p).symm.toLinearMap
  exact ∃ (CN : Connection NB) (hN : SmoothFiberMetric NB),
    (∀ p v w, hN.form p v w = hP.form p v.val w.val) ∧
    P202.TorsionMetricData.MetricCompatible NB CN hN ∧
    (∀ X Y : Field S, ∃ V : Section P.space.bundle,
      (∀ p, V.val p = i.differential p (Y.val p)) ∧
      (∀ p, (C.cov X Y).val p = tanProj p ((D.cov X V).val p))) ∧
    (∀ X : Field S, ∀ xi : Section NB, ∃ U : Section P.space.bundle,
      (∀ p, U.val p = (xi.val p).val) ∧
      (∀ p, (CN.cov X xi).val p = norProj p ((D.cov X U).val p)))

end Constructions
end P202.GaussWeingartenData

namespace P202Specs.Geometry.GaussWeingarten
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleMetricData SmoothManifolds.MetricSplittingData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GaussWeingartenData
universe u

/-- The metric on the actual pullback fibers, with exactly the ambient form. -/
def pullback_metric_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    (h : RiemannianMetric T) (F : M → N)
    (hf : SmoothManifolds.MapData.IsSmoothMap S T F)
    (P : PullbackBundle (tangentBundle T) S F),
    letI := P.space.topology
    ∃ hP : SmoothFiberMetric P.space.bundle, ∀ p, hP.form p = h.form (F p)

/-- Constant rank and the orthogonal splitting, including the actual dF
identification of the left factor. Neither an embedding nor a normal frame is
part of the hypotheses. -/
def adapted_splitting_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {F : M → N} (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F),
    letI := P.space.topology
    ∀ hP : SmoothFiberMetric P.space.bundle, Nonempty (AdaptedSplitting i P hP)

/-- Complete Proposition 7.4. C and K are arbitrary representatives of the
unique intrinsic and ambient Levi–Civita connections. P is any actual pullback
realization. Existence of the ambient pullback connection and of every
projected geometric object is included in the conclusion. -/
def exists_geometryType : Prop :=
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
      GaussWeingartenConclusion i P hP g C D W


/-- Construction of the orthogonal normal bundle, the projected normal metric
connection, and identification of the tangent projection with intrinsic LC. -/
def projected_connections_existsType : Prop :=
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
      ProjectedConnectionsConclusion i P hP C D W

/-- The tangent subbundle has the actual image fibers of the injective
intrinsic differential. This is the primary geometric definition. -/
def tangentImageType := {n m : ℕ} → {a b : ModelKind} → {M N : Type u} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  {S : SmoothManifold n a M} → {T : SmoothManifold m b N} →
  {F : M → N} → (i : SmoothImmersion S T F) → (p : M) →
  Submodule ℝ (SmoothManifolds.TangentData.TangentSpace T (F p))

def tangentImageValue : tangentImageType := @P202.GaussWeingartenData.tangentImage

end P202Specs.Geometry.GaussWeingarten
