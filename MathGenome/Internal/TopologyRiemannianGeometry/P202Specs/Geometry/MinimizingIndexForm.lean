import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SecondVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LengthDistance

/-! The energy-minimality and index-nonnegativity steps in
`cor:p202-no-interior-conjugate` (paper.tex 4153–4162), also used in
`thm:p202-bonnet-myers` (4710–4726). No conjugacy hypothesis is imposed.
All fields take values in the original intrinsic tangent fibers. -/
set_option autoImplicit false
namespace P202.MinimizingIndexData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData P202.GeodesicData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Absolute length minimality among the compact-interval competitors in the
source definition of length distance. Competitor intervals can differ. -/
def IsLengthMinimizing (g : RiemannianMetric S) {a b : ℝ}
    (γ : PiecewiseC1Curve S a b) : Prop :=
  ∀ {l r : ℝ} (σ : PiecewiseC1Curve S l r),
    σ l = γ a → σ r = γ b → length g γ ≤ length g σ

/-- Smoothness of the actual tangent lift in the canonical tangent charts.
The coordinates have ambient smooth extensions at ends of closed pieces.
Together with continuity of the lift this is the usual smooth field along a
smooth curve, expressed in the same tangent atlas as the exponential map. -/
def SmoothFieldOn (γ : ℝ → M) (V : (t : ℝ) → TangentSpace S (γ t))
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ e, ∃ he : e ∈ S.smoothStructure.val, γ t ∈ e.source ∧
    ∃ x : ℝ → Euclidean (n+n), ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      (((tangentStructure S).chart e he) (⟨γ t, V t⟩ : Phase S)).val = x t ∧
      (fun r => (((tangentStructure S).chart e he) (⟨γ r, V r⟩ : Phase S)).val)
        =ᶠ[𝓝[J] t] x

/-- A continuous piecewise smooth field on a fixed finite partition. The
continuity assertion uses the topology of the canonical tangent bundle. -/
def PiecewiseSmoothFieldOn (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace S (γ t))
    {k : ℕ} (node : Fin (k+2) → ℝ) : Prop :=
  ContinuousOn (fun t => (⟨γ t, V t⟩ : Phase S))
    (Icc (node 0) (node (Fin.last (k+1)))) ∧
  ∀ i : Fin (k+1), SmoothFieldOn γ V (Icc (node i.castSucc) (node i.succ))

end P202.MinimizingIndexData

namespace P202Specs.Geometry.MinimizingIndexForm
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData P202.MetricData P202.CurveData
  P202.ConnectionData P202.LeviCivitaData P202.FirstVariationData
  P202.SecondVariationData P202.CurvatureData P202.MinimizingIndexData
open Set
universe u

/-- The original quantitative length-energy inequality is retained. -/
def length_sq_le_energyType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    {a b : ℝ} (σ : PiecewiseC1Curve S a b),
    length g σ ^ 2 ≤ 2 * (b - a) * energy g σ

/-- Constant affine speed gives equality for the minimizing segment. -/
def geodesic_energy_equalityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ {a b : ℝ} (γ : PiecewiseC1Curve S a b), a < b →
      IsAffineGeodesicSegment C γ a b →
      length g γ ^ 2 = 2 * (b - a) * energy g γ

def minimizes_energyType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ {a b : ℝ} (γ : PiecewiseC1Curve S a b), a < b →
      IsAffineGeodesicSegment C γ a b → IsLengthMinimizing g γ →
      ∀ σ : PiecewiseC1Curve S a b,
        σ a = γ a → σ b = γ b → energy g γ ≤ energy g σ

/-- Existence of a variation is a conclusion, including a common positive
s-interval, the central curve, fixed endpoints and its prescribed field.
The equality of central curves transports V between identical tangent fibers.
Total representatives outside the segment can be made to agree as well. -/
def realizes_fieldType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (γ : ℝ → M) {a b : ℝ}, a < b →
    IsAffineGeodesicSegment C γ a b →
    ∀ {k : ℕ} (node : Fin (k+2) → ℝ), StrictMono node →
    node 0 = a → node (Fin.last (k+1)) = b →
    ∀ V : (t : ℝ) → TangentSpace S (γ t),
      PiecewiseSmoothFieldOn γ V node → V a = 0 → V b = 0 →
      ∃ (ε : ℝ) (F : ℝ × ℝ → M) (hγ : (fun t => F (0,t)) = γ),
        0 < ε ∧ PiecewiseSmoothVariationOn S F ε node ∧ FixedEndpoints F ε a b ∧
        ∀ t ∈ Icc a b, variationField S F t = (hγ.symm ▸ V) t

/-- Every continuous piecewise smooth field vanishing at the two ends,
including fields with finitely many breaks, has nonnegative index. -/
def indexForm_nonnegType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ {a b : ℝ} (γ : PiecewiseC1Curve S a b), a < b →
      IsAffineGeodesicSegment C γ a b → IsLengthMinimizing g γ →
    ∀ {k : ℕ} (node : Fin (k+2) → ℝ), StrictMono node →
      node 0 = a → node (Fin.last (k+1)) = b →
    ∀ V : (t : ℝ) → TangentSpace S (γ t),
      PiecewiseSmoothFieldOn γ V node → V a = 0 → V b = 0 →
      0 ≤ indexForm g C R γ a b V V

end P202Specs.Geometry.MinimizingIndexForm
