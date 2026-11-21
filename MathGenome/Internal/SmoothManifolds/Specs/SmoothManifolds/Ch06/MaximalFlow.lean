import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalIntegralCurves

/-! The flow clauses of M06.03 (paper.tex:1372–1385).
The interval and curve family below contains only raw data. Correctness is the
full universal maximality property in the frozen integral-curve interface.
All conclusions apply to every such family and therefore to any canonical choice.
Smoothness is tested in product coordinates `(time, state coordinates)`.
This uses the same local ambient-extension convention as `MapData`, without
choosing a linear identification of `ℝ × Euclidean n` with `Euclidean (1+n)`.
-/
namespace SmoothManifolds.MaximalFlowData
open ModelData AtlasData MapData TangentBundleData VectorFieldData IntegralCurveData Set Filter
open scoped Topology
universe u

structure CurveFamily (M : Type u) where
  interval : M → D13Unified.OpenTimeInterval
  curve : M → ℝ → M

def IsMaximalFamily {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    (X : SmoothField B) (F : CurveFamily M) : Prop :=
  ∀ p, IsMaximalThrough X p (F.interval p) (F.curve p)

def flowDomain {M : Type u} (F : CurveFamily M) : Set (ℝ × M) :=
  {z | z.1 ∈ (F.interval z.2).carrier}

def flow {M : Type u} (F : CurveFamily M) (z : ℝ × M) : M := F.curve z.2 z.1

def timeDomain {M : Type u} (F : CurveFamily M) (s : ℝ) : Set M :=
  {p | s ∈ (F.interval p).carrier}

/-- Joint smoothness in all product charts, including continuity. The functions
are total representatives; this predicate is only asserted at interior domain points. -/
def FlowSmoothAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (F : CurveFamily M) (z : ℝ × M) : Prop :=
  ContinuousAt (flow F) z ∧
  ∀ e ∈ S.smoothStructure.val, ∀ d ∈ S.smoothStructure.val,
    z.2 ∈ e.source → flow F z ∈ d.source →
    ∃ U : Set (ℝ × Euclidean n), IsOpen U ∧ (z.1, (e z.2).val) ∈ U ∧
      ∃ G : ℝ × Euclidean n → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun w : ℝ × M => G (w.1, (e w.2).val)) =ᶠ[𝓝 z]
          (fun w => (d (flow F w)).val)

end SmoothManifolds.MaximalFlowData

namespace Specs.SmoothManifolds.Ch06.MaximalFlow
open _root_.SmoothManifolds _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.VectorFieldData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.MaximalFlowData Set
universe u

/-- Simultaneous choice of the prerequisite's maximal curves, without any
nonemptiness or dimension restriction on the base manifold. -/
def maximal_family_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B), ∃ F : CurveFamily M, IsMaximalFamily X F

/-- Openness of the actual joint domain and joint C-infinity regularity there. -/
def domain_open_smoothType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M), IsMaximalFamily X F →
      IsOpen (flowDomain F) ∧ ∀ z ∈ flowDomain F, FlowSmoothAt S F z

/-- Exact lifespan identity and the domain-restricted flow law. A translated
interval is represented as the preimage by `t ↦ s+t`, hence exactly `I_p-s`. -/
def lifespan_flow_lawType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M), IsMaximalFamily X F →
    ∀ (p : M) (s : ℝ), s ∈ (F.interval p).carrier →
      (F.interval (F.curve p s)).carrier = {t | s + t ∈ (F.interval p).carrier} ∧
      ∀ t : ℝ, s + t ∈ (F.interval p).carrier →
        F.curve (F.curve p s) t = F.curve p (s + t)

/-- Each time map is a diffeomorphism between the two actual open domains.
Both directions are specified, including the inverse time map's base point. -/
def time_diffeomorphType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (X : SmoothField B) (F : CurveFamily M), IsMaximalFamily X F →
    ∀ s : ℝ, ∃ (hs : IsOpen (timeDomain F s)) (hneg : IsOpen (timeDomain F (-s))),
      ∃ h : Diffeomorph
        (openSubsetAtlas S.smoothStructure.val (timeDomain F s) hs)
        (openSubsetAtlas S.smoothStructure.val (timeDomain F (-s)) hneg),
        (∀ p : timeDomain F s, (h.toEquiv p).val = F.curve p.val s) ∧
        (∀ q : timeDomain F (-s), (h.toEquiv.symm q).val = F.curve q.val (-s))

end Specs.SmoothManifolds.Ch06.MaximalFlow
