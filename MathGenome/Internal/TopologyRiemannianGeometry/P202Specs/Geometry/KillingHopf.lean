import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GlobalSpaceFormDevelopment
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ModelPolarDomains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CompleteLocalIsometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.DeckGroup
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Independent statement of the complete Killing–Hopf theorem,
`paper.tex`, Theorem `thm:p202-killing-hopf`, lines 4544–4635.

All distances are the infima of the original piecewise-C¹ lengths. The
universal cover retains its given topology, the maximal lifted atlas, and the
pullback metric. The quotient is the orbit space of the actual deck group,
with its quotient topology and a smooth Riemannian structure for which the
quotient projection is a local isometry. The identification with M is a
Riemannian isometry, not just a homeomorphism.

`CrossIsometry` only extends the usual intrinsic differential definition to
two possibly different universes; its action on every smooth germ is stated
explicitly. This lets the literal standard models live in Type while the
manifold being classified has arbitrary universe.
-/
set_option autoImplicit false
noncomputable section
namespace P202.KillingHopfData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.CoveringData
  P202.MetricData P202.SpaceFormData P202.ModelPolarData P202.CompletenessData
  P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.ConstantCurvaturePolarData P202Specs.Topology
open Set Filter
open scoped _root_.Topology
universe u v

/-- Smooth Riemannian isometry, including the intrinsic length distance. -/
def IsRiemannianIsometry {n : ℕ} {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean Y}
    (g : RiemannianMetric S) (h : RiemannianMetric T) (e : X ≃ₜ Y) : Prop :=
  IsLocalIsometry g h e ∧ IsSmoothMap T S e.symm ∧
    ∀ x y, P202.CompleteExponentialData.lengthDistance h (e x) (e y) =
      P202.CompleteExponentialData.lengthDistance g x y

/-- The same geometric meaning without imposing equality of universes. -/
structure CrossIsometry {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean Y)
    (g : RiemannianMetric S) (h : RiemannianMetric T) where
  homeomorph : X ≃ₜ Y
  smooth : IsSmoothMap S T homeomorph
  smooth_inverse : IsSmoothMap T S homeomorph.symm
  linear : (x : X) → TangentSpace S x →ₗ[ℝ] TangentSpace T (homeomorph x)
  differential : ∀ (x : X) (v : TangentSpace S x)
    (a : SmoothGerm T (homeomorph x)) (b : SmoothGerm S x) (r : Y → ℝ),
    Germ.ofFun r = a.val → Germ.ofFun (r ∘ homeomorph) = b.val →
      (linear x v).val a = v.val b
  preserves : ∀ x v w,
    pairing h (homeomorph x) (linear x v) (linear x w) = pairing g x v w
  distance : ∀ x y,
    P202.CompleteExponentialData.lengthDistance h (homeomorph x) (homeomorph y) =
      P202.CompleteExponentialData.lengthDistance g x y

/-- Identification with the literal Euclidean, round spherical, or induced
hyperboloid model, with exactly the radius prescribed in the source. -/
def IsStandardModel {n : ℕ} {X : Type u} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X) (g : RiemannianMetric S) (k : ℝ) : Prop :=
  (k = 0 ∧ ∃ G : EuclideanModel n, Nonempty (CrossIsometry S G.manifold g G.metric)) ∨
  (0 < k ∧ ∃ (A : EuclideanModel (n + 1))
    (B : SphericalModel n (1 / Real.sqrt k) A),
      Nonempty (CrossIsometry S B.manifold g B.metric)) ∨
  (k < 0 ∧ ∃ T : SmoothManifold n .euclidean
      (P202.HyperboloidData.Hyperboloid n (1 / Real.sqrt (-k))),
    ∃ h : RiemannianMetric T,
      HasProjectionChart T ∧ P202.HyperboloidData.IsInduced h ∧
        Nonempty (CrossIsometry S T g h))

abbrev DeckQuotient {X M : Type u} [TopologicalSpace X] (f : X → M) :=
  Quotient (MulAction.orbitRel (DeckGroup f) X)

/-- All global, universal-cover and quotient conclusions. In particular no
completeness, curvature, regularity or single-valuedness conclusion is assumed
in this predicate's definition. -/
structure Classification {n : ℕ} {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : X → M) : Prop where
  localIsometry : IsLocalIsometry g h f
  covering : Covering f
  canonicalAtlas : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    (liftedAtlas T.smoothStructure.val f)
  deckIsometries : ∀ F : DeckGroup f, IsRiemannianIsometry g g F.val
  free : ∀ (F : DeckGroup f) (x : X), F.val x = x → F = 1
  properlyDiscontinuous : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ F : DeckGroup f, F ≠ 1 → Disjoint U (F.val '' U)
  fibers : ∀ x y : X, f x = f y ↔ ∃ F : DeckGroup f, F.val x = y
  quotient : ∃ e : DeckQuotient f ≃ₜ M,
    (∀ x : X, e (Quotient.mk _ x) = f x) ∧
    ∃ Q : SmoothManifold n .euclidean (DeckQuotient f),
    ∃ j : RiemannianMetric Q,
      IsRiemannianIsometry j h e ∧
      IsLocalIsometry g j (Quotient.mk (MulAction.orbitRel (DeckGroup f) X))
  universal : ∀ (U : Type u) [TopologicalSpace U] [SimplyConnectedSpace U]
    (p : U → M), Covering p →
    ∃ Q : SmoothManifold n .euclidean U,
      Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (liftedAtlas T.smoothStructure.val p) ∧
    ∃ j : RiemannianMetric Q, IsLocalIsometry j h p ∧ LengthMetricComplete j ∧
      ∃ e : X ≃ₜ U, (∀ x, p (e x) = f x) ∧ IsRiemannianIsometry g j e
  simplyConnected : SimplyConnectedSpace M →
    ∃ e : X ≃ₜ M, (∀ x, e x = f x) ∧ IsRiemannianIsometry g h e

end P202.KillingHopfData

namespace P202Specs.Geometry.KillingHopf
open SmoothManifolds.AtlasData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.CurvatureData P202.ConstantCurvaturePolarData
  P202.CompletenessData P202.KillingHopfData
universe u

/-- Full original conclusion, with no chosen model, covering, or global
local isometry as an additional hypothesis. -/
def killingHopfType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (M : Type u) [TopologicalSpace M] [ConnectedSpace M]
    (T : SmoothManifold n .euclidean M) (h : RiemannianMetric T)
    (D : Connection (tangentBundle T)), IsLeviCivita h D →
    ∀ R : CurvatureTensor T, RepresentsCurvature D R →
    ∀ k : ℝ, ConstantSectional h R k → LengthMetricComplete h →
    ∃ (X : Type u) (t : TopologicalSpace X),
    ∃ S : SmoothManifold n .euclidean X, ∃ g : RiemannianMetric S,
      SimplyConnectedSpace X ∧ IsStandardModel S g k ∧
      ∃ f : X → M, Classification S T g h f

end P202Specs.Geometry.KillingHopf
