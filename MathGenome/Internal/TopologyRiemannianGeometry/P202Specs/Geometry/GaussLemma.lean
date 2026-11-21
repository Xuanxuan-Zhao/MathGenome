import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialNormalCoordinates

/-! Gauss lemma, paper.tex:3362–3371 and 3381–3394.
The fiber differential is the Fréchet derivative of the already defined
exponential, transported through the intrinsic tangent coordinates. Source
fiber coordinates are linear, so this uses T_v(T_p M) = T_p M. All charts
are quantified; no injectivity or nonsingularity hypothesis is imposed.
The theorem concerns every point of the actual open time-one domain. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.GaussData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.GeodesicData P202.ExponentialData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Coordinate representation of the actual fiber differential. Under the
maximal-family and domain hypotheses its defining coordinate function is
smooth; outside that domain no derivative assertion is made. -/
noncomputable def fiberDifferential (F : CurveFamily (Phase S))
    (p : M) (v : TangentSpace S p)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source)
    (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
    (hq : fiberExponential F p v ∈ d.source) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S (fiberExponential F p v) :=
  let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let D := (tangentStructure S).fiberCoordinates.equiv d hd (fiberExponential F p v) hq
  D.symm.toLinearMap.comp
    ((fderiv ℝ (fun x : Euclidean n =>
      (d (fiberExponential F p (E.symm x))).val) (E v)).toLinearMap.comp E.toLinearMap)

end P202.GaussData

namespace P202Specs.Geometry.GaussLemma
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.GeodesicData P202.LeviCivitaData
  P202.ExponentialData P202.GaussData
universe u

def gauss_lemmaType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p),
      (⟨p, v⟩ : Phase S) ∈ exponentialDomain F →
    ∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (hp : p ∈ e.source)
      (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
      (hq : fiberExponential F p v ∈ d.source) (w : TangentSpace S p),
      let L := fiberDifferential F p v e he hp d hd hq
      pairing g (fiberExponential F p v) (L v) (L w) = pairing g p v w

def radial_lengthType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p),
      (⟨p, v⟩ : Phase S) ∈ exponentialDomain F →
    ∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (hp : p ∈ e.source)
      (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
      (hq : fiberExponential F p v ∈ d.source),
      tangentNorm g (fiberExponential F p v)
        (fiberDifferential F p v e he hp d hd hq v) = tangentNorm g p v

def angular_orthogonalityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p),
      (⟨p, v⟩ : Phase S) ∈ exponentialDomain F →
    ∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (hp : p ∈ e.source)
      (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
      (hq : fiberExponential F p v ∈ d.source) (w : TangentSpace S p),
      pairing g p v w = 0 →
      let L := fiberDifferential F p v e he hp d hd hq
      pairing g (fiberExponential F p v) (L v) (L w) = 0

end P202Specs.Geometry.GaussLemma
