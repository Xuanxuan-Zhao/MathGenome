import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MyersDiameterCompact
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CoveringMetricCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SubgroupCoverConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Monodromy

/-! Independent complete statements of paper.tex:4703–4742. The universal
cover is the accepted path-class construction, with its original topology.
All distances, tensors, differentials and tangent fibers are the upstream ones.
No compactness or finiteness certificate is part of the hypotheses. -/
set_option autoImplicit false
namespace P202Specs.Geometry.BonnetMyers
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MapData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
  P202.CurvatureData P202.RicciData P202.MyersData
  P202.CompletenessData P202.CoveringMetricData P202.CompleteExponentialData
  P202Specs.Topology
open Set
universe u

/-- Naturality is with the actual differential, for arbitrary local isometries.
In particular there is no global injectivity, compactness or completeness premise. -/
def localIsometry_ricciType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    {T : SmoothManifold n .euclidean E} {S : SmoothManifold n .euclidean B}
    (h : RiemannianMetric T) (g : RiemannianMetric S)
    (D : Connection (tangentBundle T)) (C : Connection (tangentBundle S)),
    IsLeviCivita h D → IsLeviCivita g C →
    ∀ (Q : CurvatureTensor T) (R : CurvatureTensor S),
    RepresentsCurvature D Q → RepresentsCurvature C R →
    ∀ (p : E → B) (hi : IsLocalIsometry h g p) (x : E)
      (v w : TangentSpace T x),
      ricci Q x v w = ricci R (p x)
        (SmoothManifolds.differential T S p hi.1.1 x v)
        (SmoothManifolds.differential T S p hi.1.1 x w)

/-- Complete geometric and topological data used in the source proof. The
metric formula rules out replacing the pullback by an unrelated metric. -/
def universal_coverType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R → 2 ≤ n →
    ∀ k : ℝ, 0 < k → RicciLowerBound g R k → LengthMetricComplete g →
    ∀ b : M,
    let E := SubgroupCover b (⊥ : Subgroup (Pi1 M b))
    let p : E → M := SubgroupCover.endpoint ⊥
    ∃ (T : SmoothManifold n .euclidean E) (hp : SmoothCovering T S p)
      (h : RiemannianMetric T) (D : Connection (tangentBundle T))
      (Q : CurvatureTensor T),
      IsLocalIsometry h g p ∧
      (∀ x v w, pairing h x v w = pairing g (p x)
        (SmoothManifolds.differential T S p hp.2.1 x v)
        (SmoothManifolds.differential T S p hp.2.1 x w)) ∧
      IsLeviCivita h D ∧ RepresentsCurvature D Q ∧ RicciLowerBound h Q k ∧
      LengthMetricComplete h ∧ IsCompact (univ : Set E) ∧
      Nonempty (Pi1 M b ≃ Fiber p b) ∧ Finite (Fiber p b)

/-- The complete theorem, for every based fundamental group with the original
first-path-first convention. Levi-Civita and curvature representatives exist
upstream for every metric, so these quantifiers do not restrict applicability. -/
def bonnet_myersType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R → 2 ≤ n →
    ∀ k : ℝ, 0 < k → RicciLowerBound g R k → LengthMetricComplete g →
      (∀ p q : M, lengthDistance g p q ≤ Real.pi / Real.sqrt k) ∧
      lengthDiameter g ≤ Real.pi / Real.sqrt k ∧ IsCompact (univ : Set M) ∧
      ∀ b : M, Finite (Pi1 M b)

/-- A global identity-coordinate chart fixes the standard smooth structure on
ℝ; the metric formula is exactly dx² on the intrinsic derivation tangents.
The distance is the existing integral-length distance, not a replacement. -/
def euclidean_lineType : Prop :=
  ∃ (S : SmoothManifold 1 .euclidean ℝ) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S),
    (∃ c ∈ S.smoothStructure.val,
      c.source = univ ∧ c.target = univ ∧ ∀ x : ℝ, (c x).val 0 = x) ∧
    (∀ (x : ℝ) (v w : TangentSpace S x), pairing g x v w =
      P202.ConnectionData.scalarDerivative S (fun y : ℝ => y) x v *
      P202.ConnectionData.scalarDerivative S (fun y : ℝ => y) x w) ∧
    ConnectedSpace ℝ ∧ LengthMetricComplete g ∧ IsLeviCivita g C ∧
    RepresentsCurvature C R ∧ (∀ x : ℝ, ricci R x = 0) ∧
    (∀ k : ℝ, 0 < k → RicciLowerBound g R k) ∧
    (∀ x y : ℝ, lengthDistance g x y = |x - y|) ∧
    ∀ A : ℝ, 0 < A → ∃ x y : ℝ, A < lengthDistance g x y

end P202Specs.Geometry.BonnetMyers
