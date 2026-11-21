import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.IndexLemma

/-! Independent specification of `thm:p202-rauch`, paper.tex 4317–4373.
The two curves are restrictions of affine geodesics on their actual open time
domains. Both use the shared intrinsic tangent fibers, metrics, and curvature
sign convention. The radial bound quantifies over every pair of unit normals;
there is no chosen identification of the two tangent spaces. -/
set_option autoImplicit false

namespace P202.RauchComparisonData
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.GeodesicData P202.CurvatureData
open Set
universe u

def UnitSpeedOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (q : ℝ → Phase S) (K : Set ℝ) : Prop :=
  ∀ t ∈ K, pairing g (q t).1 (q t).2 (q t).2 = 1

def NormalFieldOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (q : ℝ → Phase S) (J : (t : ℝ) → TangentSpace S (q t).1)
    (K : Set ℝ) : Prop :=
  ∀ t ∈ K, pairing g (q t).1 (J t) (q t).2 = 0

/-- For an orthonormal pair the Gram denominator of sectional curvature is
one. Thus the displayed curvature form is precisely K(T,u). Quantifying over
all u and ū separately is essential; no matched-vector condition is used. -/
def RadialSectionalBound {n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n .euclidean M} {Sbar : SmoothManifold n .euclidean N}
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar) (K : Set ℝ) : Prop :=
  ∀ t ∈ K, ∀ (u : TangentSpace S (q t).1) (ū : TangentSpace Sbar (qbar t).1),
    pairing g (q t).1 u (q t).2 = 0 → pairing g (q t).1 u u = 1 →
    pairing gbar (qbar t).1 ū (qbar t).2 = 0 → pairing gbar (qbar t).1 ū ū = 1 →
    curvatureForm g R (q t).1 (q t).2 u u (q t).2 ≤
      curvatureForm gbar Rbar (qbar t).1 (qbar t).2 ū ū (qbar t).2

end P202.RauchComparisonData

namespace P202Specs.Geometry.RauchComparison
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.ExponentialJacobiData P202.RauchComparisonData
open Set
universe u

/-- Full Rauch comparison, including nonconjugacy at b, the value at t=0,
and the zero-initial-derivative case. There is no nonconjugacy assumption on
the lower-curvature curve. No nonzero condition on either field is imposed. -/
def rauchType : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n .euclidean M) (Sbar : SmoothManifold n .euclidean N)
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar)),
    IsLeviCivita g C → IsLeviCivita gbar Cbar →
    ∀ (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar),
      RepresentsCurvature C R → RepresentsCurvature Cbar Rbar →
    ∀ (I Ibar : D13Unified.OpenTimeInterval)
      (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar),
      IsGeodesicOn S C I.carrier q → IsGeodesicOn Sbar Cbar Ibar.carrier qbar →
    ∀ (h0 : 0 ∈ I.carrier) (hbar0 : 0 ∈ Ibar.carrier) (b : ℝ), 0 < b →
      Icc 0 b ⊆ I.carrier → Icc 0 b ⊆ Ibar.carrier →
      UnitSpeedOn g q (Icc 0 b) → UnitSpeedOn gbar qbar (Icc 0 b) →
      RadialSectionalBound g gbar R Rbar q qbar (Icc 0 b) →
      (∀ t ∈ Ioc 0 b, ∀ ht : t ∈ Ibar.carrier,
        ¬ ConjugateAlong Sbar Cbar Rbar Ibar qbar ⟨0,hbar0⟩ ⟨t,ht⟩) →
      (∀ t ∈ Ioc 0 b, ∀ ht : t ∈ I.carrier,
        ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩) ∧
      ∀ (J : (t : ℝ) → TangentSpace S (q t).1)
        (Jbar : (t : ℝ) → TangentSpace Sbar (qbar t).1),
        IsJacobiField C R I.carrier q J → IsJacobiField Cbar Rbar Ibar.carrier qbar Jbar →
        J 0 = 0 → Jbar 0 = 0 →
        NormalFieldOn g q J (Icc 0 b) → NormalFieldOn gbar qbar Jbar (Icc 0 b) →
      ∀ (w : TangentSpace S (q 0).1) (wbar : TangentSpace Sbar (qbar 0).1),
        HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w →
        HasCovariantDerivativeAt Cbar (fun s => (qbar s).1) Jbar 0 wbar →
        tangentNorm g (q 0).1 w = tangentNorm gbar (qbar 0).1 wbar →
        ∀ t ∈ Icc 0 b,
          tangentNorm gbar (qbar t).1 (Jbar t) ≤ tangentNorm g (q t).1 (J t)

end P202Specs.Geometry.RauchComparison
