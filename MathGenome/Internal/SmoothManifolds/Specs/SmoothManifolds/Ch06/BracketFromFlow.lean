import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.LieBracket
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.BoundaryTangentFlow

/-! The derivative clauses of M06.07 (paper.tex:1424--1433).

The time maps below are total representatives. All assertions about their
pullbacks are restricted to the recorded flow domain. A tangent vector is a
germ derivation, so its time derivative is tested in each linear coordinate
identification of the fixed fiber at p. Boundary regularity means local smooth
ambient extension, as elsewhere in the project. No tangency is imposed on Y.
-/
namespace SmoothManifolds.BracketFlowData
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  VectorFieldData LieBracketData MaximalFlowData Set Filter
open scoped Topology
universe u

/-- The intrinsic differential of the inverse time map at `F.curve p t`, with
its target fiber rebased to p. At admissible times the flow law proves that
`F.curve (F.curve p t) (-t) = p`. This predicate is exactly `IsDifferential`
after that equality, and tests every representative of every smooth germ. -/
def IsInverseTimeDifferential {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (t : ℝ) (p : M)
    (L : TangentSpace S (F.curve p t) →ₗ[ℝ] TangentSpace S p) : Prop :=
  ∀ (v : TangentSpace S (F.curve p t)) (h : SmoothGerm S p)
    (k : SmoothGerm S (F.curve p t)) (r : M → ℝ),
    Germ.ofFun r = h.val →
    Germ.ofFun (r ∘ fun q => F.curve q (-t)) = k.val →
      (L v).val h = v.val k

/-- An ordinary choice of a differential, with a zero default where it does
not exist. Existence and uniqueness on the actual flow domain are obligations
below, rather than assumed certificates in the data. -/
noncomputable def inverseTimeDifferential {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M)
    (t : ℝ) (p : M) :
    TangentSpace S (F.curve p t) →ₗ[ℝ] TangentSpace S p := by
  classical
  exact if h : ∃ L, IsInverseTimeDifferential S F t p L then Classical.choose h else 0

/-- `(φ_t^*Y)(p) = d(φ_{-t})_{φ_t(p)} Y(φ_t(p))`. The point at which the
inverse differential is evaluated is part of its dependent source type. -/
noncomputable def pullback {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (F : CurveFamily M)
    (Y : Section S) (t : ℝ) : Section S :=
  fun p => inverseTimeDifferential S F t p (Y (F.curve p t))

/-- Coordinates in the fiber over the initial point, not the moving point.
The zero convention outside a chart is the shared `coefficients` convention. -/
noncomputable def pullbackCoefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : CurveFamily M) (Y : Section S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (z : ℝ × M) : Euclidean n :=
  coefficients B (pullback F Y z.1) e he z.2

/-- Joint smoothness in time and the initial state, with a smooth ambient
extension even at a boundary state. The chart e is any chart through p. -/
def PullbackSmoothAt {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : CurveFamily M) (Y : Section S) (z : ℝ × M) : Prop :=
  ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val), z.2 ∈ e.source →
    ∃ U : Set (ℝ × Euclidean n), IsOpen U ∧ (z.1, (e z.2).val) ∈ U ∧
      ∃ G : ℝ × Euclidean n → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 z]
          pullbackCoefficients B F Y e he

/-- Proper inverse domain, actual inverse differential, and uniqueness of that
differential at every allowed time; no statement is made off the domain. -/
def PullbackCorrect {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (F : CurveFamily M) : Prop :=
  ∀ (p : M) (t : ℝ), t ∈ (F.interval p).carrier →
    -t ∈ (F.interval (F.curve p t)).carrier ∧
    F.curve (F.curve p t) (-t) = p ∧
    IsInverseTimeDifferential S F t p (inverseTimeDifferential S F t p) ∧
    ∀ L, IsInverseTimeDifferential S F t p L → L = inverseTimeDifferential S F t p

/-- The derivative in the fixed fiber at every point, expressed in every
chart. This is a two-sided `HasDerivAt`, including at boundary states. -/
def HasPullbackTimeDerivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (B : TangentBundleStructure S)
    (F : CurveFamily M) (Y Z : Section S) (p : M) (t : ℝ) : Prop :=
  ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val), p ∈ e.source →
    HasDerivAt (fun s => pullbackCoefficients B F Y e he (s, p))
      (coefficients B Z e he p) t

end SmoothManifolds.BracketFlowData

namespace Specs.SmoothManifolds.Ch06.BracketFromFlow
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.VectorFieldData _root_.SmoothManifolds.LieBracketData
  _root_.SmoothManifolds.MaximalFlowData _root_.SmoothManifolds.BracketFlowData
  _root_.SmoothManifolds.BoundaryFlowData Set
universe u

/-- The construction on an arbitrary boundaryless manifold, with no tangency
premise, including empty and zero-dimensional manifolds. -/
def pullback_boundarylessType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M),
    MaximalFlowData.IsMaximalFamily X F →
      PullbackCorrect S F ∧
      ∀ (Y : SmoothField B) (p : M), pullback F Y.val 0 p = Y.val p

/-- The same construction on either ordinary model, with precisely tangency
of X to the boundary. Y is arbitrary, including its normal component. -/
def pullback_boundaryType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, BoundaryFlowData.IsMaximalFamily X F →
      PullbackCorrect S F ∧
      ∀ (Y : SmoothField B) (p : M), pullback F Y.val 0 p = Y.val p

def pullback_smoothType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M),
    MaximalFlowData.IsMaximalFamily X F →
    ∀ (Y : SmoothField B) (z : ℝ × M), z ∈ flowDomain F →
      PullbackSmoothAt B F Y.val z

def boundary_pullback_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, BoundaryFlowData.IsMaximalFamily X F →
    ∀ (Y : SmoothField B) (z : ℝ × M), z ∈ flowDomain F →
      PullbackSmoothAt B F Y.val z

def derivative_zeroType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B) (F : CurveFamily M),
      MaximalFlowData.IsMaximalFamily X F → ∀ p : M,
        HasPullbackTimeDerivative B F Y.val (b X Y).val p 0

def derivative_at_timeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B) (F : CurveFamily M),
      MaximalFlowData.IsMaximalFamily X F →
      ∀ (p : M) (t : ℝ), t ∈ (F.interval p).carrier →
        HasPullbackTimeDerivative B F Y.val (pullback F (b X Y).val t) p t

def boundary_derivative_zeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, BoundaryFlowData.IsMaximalFamily X F → ∀ p : M,
      HasPullbackTimeDerivative B F Y.val (b X Y).val p 0

def boundary_derivative_at_timeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (b : SmoothField B → SmoothField B → SmoothField B), BracketOperation b →
    ∀ (X Y : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, BoundaryFlowData.IsMaximalFamily X F →
      ∀ (p : M) (t : ℝ), t ∈ (F.interval p).carrier →
        HasPullbackTimeDerivative B F Y.val (pullback F (b X Y).val t) p t

end Specs.SmoothManifolds.Ch06.BracketFromFlow
