import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalFlow
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.BoundaryCones

/-! M06.06, boundary-flow clause, together with the flow laws of M06.03.
The two uniform ordinary models are allowed, including dimension zero and empty
boundary. Integral curves have open, two-sided time intervals. Smoothness at a
boundary point means an actual smooth local ambient extension in coordinates.
The raw family is the same `CurveFamily` as in the boundaryless interface.
-/
namespace SmoothManifolds.BoundaryFlowData
open ModelData AtlasData MapData TangentBundleData VectorFieldData BoundaryData
  MaximalFlowData Set Filter
open scoped Topology
universe u

/-- The tangent hyperplane in the ordinary model. In dimension zero there is no
normal coordinate; for a Euclidean model the boundary condition is vacuous. -/
def FaceTangent : (n : ℕ) → ModelKind → Euclidean n → Prop
  | 0, _, _ => True
  | n + 1, .halfSpace, v => v (Fin.last n) = 0
  | _ + 1, .euclidean, _ => True

/-- Intrinsic tangency, tested in every boundary chart. The boundary tangent
identification upstream identifies this kernel with the inclusion differential's
image, so this is exactly membership in `T_p ∂M`, not an inward inequality. -/
def IsTangentToBoundary {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (X : SmoothField B) : Prop :=
  ∀ p ∈ intrinsicBoundary S, ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val),
    ∀ hp : p ∈ e.source, FaceTangent n a (B.fiberCoordinates.equiv e he p hp (X.val p))

/-- The same intrinsic ODE as in the boundaryless interface, now on either
ordinary model. Derivatives are two-sided derivatives in the time variable. -/
def IsIntegralCurveOn {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (X : SmoothField B) (I : Set ℝ) (γ : ℝ → M) : Prop :=
  ContinuousOn γ I ∧ ∀ t ∈ I,
    ∀ (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
      (ht : γ t ∈ e.source),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (γ s)).val) t ∧
      HasDerivAt (fun s => (e (γ s)).val)
        (B.fiberCoordinates.equiv e he (γ t) ht (X.val (γ t))) t

/-- Universal extension among all integral curves through the initial point;
comparison curves are not assumed to satisfy a separate preservation property. -/
def IsMaximalThrough {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (X : SmoothField B) (p : M) (I : D13Unified.OpenTimeInterval)
    (γ : ℝ → M) : Prop :=
  0 ∈ I.carrier ∧ γ 0 = p ∧ IsIntegralCurveOn X I.carrier γ ∧
    ∀ (J : D13Unified.OpenTimeInterval) (η : ℝ → M),
      0 ∈ J.carrier → η 0 = p → IsIntegralCurveOn X J.carrier η →
        J.carrier ⊆ I.carrier ∧ EqOn γ η J.carrier

def IsMaximalFamily {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {B : TangentBundleStructure S}
    (X : SmoothField B) (F : CurveFamily M) : Prop :=
  ∀ p, IsMaximalThrough X p (F.interval p) (F.curve p)

/-- Joint smoothness relative to `ℝ × M`, in product coordinates, with an
ambient extension on an open subset of `ℝ × ℝⁿ` even at boundary states. -/
def FlowSmoothAt {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (F : CurveFamily M) (z : ℝ × M) : Prop :=
  ContinuousAt (flow F) z ∧
  ∀ e ∈ S.smoothStructure.val, ∀ d ∈ S.smoothStructure.val,
    z.2 ∈ e.source → flow F z ∈ d.source →
    ∃ U : Set (ℝ × Euclidean n), IsOpen U ∧ (z.1, (e z.2).val) ∈ U ∧
      ∃ G : ℝ × Euclidean n → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 z]
          (fun w => (d (flow F w)).val)

end SmoothManifolds.BoundaryFlowData

namespace Specs.SmoothManifolds.Ch06.BoundaryTangentFlow
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.BoundaryData
open _root_.SmoothManifolds.MaximalFlowData (CurveFamily flowDomain flow timeDomain)
open _root_.SmoothManifolds.BoundaryFlowData Set
universe u

def maximal_family_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
      ∃ F : CurveFamily M, IsMaximalFamily X F

/-- Only recorded domains and on-domain values are unique. -/
def maximal_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
    ∀ (F G : CurveFamily M), IsMaximalFamily X F → IsMaximalFamily X G →
    ∀ p, (F.interval p).carrier = (G.interval p).carrier ∧
      EqOn (F.curve p) (G.curve p) (F.interval p).carrier

def domain_open_smoothType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, IsMaximalFamily X F →
      IsOpen (flowDomain F) ∧ ∀ z ∈ flowDomain F, FlowSmoothAt S F z

def lifespan_flow_lawType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, IsMaximalFamily X F →
    ∀ (p : M) (s : ℝ), s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t : ℝ, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t)

/-- Both forward and reverse preservation are asserted at every admissible
time. Thus neither an interior point nor a boundary point can change stratum. -/
def preserves_boundary_interiorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, IsMaximalFamily X F →
    ∀ (p : M) (t : ℝ), t ∈ (F.interval p).carrier →
      (F.curve p t ∈ intrinsicBoundary S ↔ p ∈ intrinsicBoundary S) ∧
      (F.curve p t ∈ manifoldInterior S ↔ p ∈ manifoldInterior S)

def time_diffeomorphType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (B : TangentBundleStructure S)
    (X : SmoothField B), IsTangentToBoundary X →
    ∀ F : CurveFamily M, IsMaximalFamily X F →
    ∀ s : ℝ, ∃ (hs : IsOpen (timeDomain F s)) (hneg : IsOpen (timeDomain F (-s))),
      ∃ h : Diffeomorph
        (openSubsetAtlas S.smoothStructure.val (timeDomain F s) hs)
        (openSubsetAtlas S.smoothStructure.val (timeDomain F (-s)) hneg),
        (∀ p : timeDomain F s, (h.toEquiv p).val = F.curve p.val s) ∧
        (∀ q : timeDomain F (-s), (h.toEquiv.symm q).val = F.curve q.val (-s))

end Specs.SmoothManifolds.Ch06.BoundaryTangentFlow
