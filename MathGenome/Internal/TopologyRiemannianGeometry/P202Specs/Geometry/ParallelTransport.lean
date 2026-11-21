import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionCalculus
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TorsionAndMetric

/-! Independent statements for paper.tex, Theorem 6.4 (3134–3170).

Fields are ambient representatives, compared only on the actual compact
interval. At a corner the two closed-piece derivatives are separate relations.
Repeated partition nodes impose no derivative condition. Neither positive rank
nor a nondegenerate parameter interval is assumed. -/
set_option autoImplicit false

namespace P202.ParallelData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.CurveData P202.CurveConnectionData
open Set Filter
open scoped Topology
universe u v w
variable {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  {B : SmoothVectorBundle S r ι E}

/-- A continuous field, C¹ on each given closed piece, with zero actual
covariant derivative on each positive-length piece, including its endpoints.
There is no equality condition between derivatives belonging to distinct pieces. -/
def ParallelField (C : Connection B) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) (f : (t : ℝ) → E (c t)) : Prop :=
  ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace (Euclidean r) E)) (Icc a b) ∧
  (∀ i : Fin c.pieces,
    C1FieldOn (B := B) c f (Icc (c.node i.castSucc) (c.node i.succ))) ∧
  ∀ i : Fin c.pieces, c.node i.castSucc < c.node i.succ →
    ∀ t ∈ Icc (c.node i.castSucc) (c.node i.succ),
      HasCovariantDerivativeWithinAt C c f
        (Icc (c.node i.castSucc) (c.node i.succ)) t 0

/-- The ordinary metric-compatibility identity on arbitrary smooth sections.
The scalar derivative is the canonical intrinsic germ differential. -/
abbrev IsMetricConnection (C : Connection B) (h : SmoothFiberMetric B) : Prop :=
  P202.TorsionMetricData.MetricCompatible B C h

/-- A harmless ambient field with the prescribed value. This is used only to
make the choice below total before existence of parallel fields is proved. -/
noncomputable def seedField {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (s : Icc a b) (ξ : E (c s)) (t : ℝ) : E (c t) := by
  classical
  exact if ht : t = s.val then ht.symm ▸ ξ else 0

/-- Selection of a parallel field when one exists. The fallback is not asserted
to be parallel. Existence and uniqueness below are independent obligations. -/
noncomputable def selectedField (C : Connection B) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) (s : Icc a b) (ξ : E (c s)) :
    (t : ℝ) → E (c t) := by
  classical
  exact if h : ∃ f : (t : ℝ) → E (c t), ParallelField C c f ∧ f s = ξ then
    Classical.choose h else seedField c s ξ

/-- Evaluation of the selected solution in the original destination fiber.
It is defined without assuming an existence or linearity certificate. -/
noncomputable def transport (C : Connection B) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) (s t : Icc a b) : E (c s) → E (c t) :=
  fun ξ => selectedField C c s ξ t

end P202.ParallelData

namespace P202Specs.Geometry.ParallelTransport
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.BundleMetricData
  P202.ConnectionData P202.CurveData P202.CurveConnectionData P202.ParallelData
open Set
universe u v w

/-- Existence and uniqueness at every initial time, with comparison only on
[a,b]. This includes constant curves, a=b, and zero-dimensional fibers. -/
def parallel_exists_uniqueType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s : Icc a b) (ξ : E (c s)),
    ∃ f : (t : ℝ) → E (c t), ParallelField C c f ∧ f s = ξ ∧
      ∀ g : (t : ℝ) → E (c t), ParallelField C c g → g s = ξ →
        ∀ t ∈ Icc a b, g t = f t

/-- The selected field actually realizes transport and is parallel. -/
def selectedField_parallelType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s : Icc a b) (ξ : E (c s)),
    ParallelField C c (selectedField C c s ξ) ∧ selectedField C c s ξ s = ξ

def transport_linearType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t : Icc a b),
    (∀ ξ η, transport C c s t (ξ + η) = transport C c s t ξ + transport C c s t η) ∧
    (∀ (k : ℝ) ξ, transport C c s t (k • ξ) = k • transport C c s t ξ)

def transport_reflType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s : Icc a b) (ξ : E (c s)),
    transport C c s s ξ = ξ

def transport_compType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t q : Icc a b) (ξ : E (c s)),
    transport C c t q (transport C c s t ξ) = transport C c s q ξ

def transport_inverseType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t : Icc a b),
    Function.LeftInverse (transport C c t s) (transport C c s t) ∧
    Function.RightInverse (transport C c t s) (transport C c s t)

/-- The actual fiber maps form linear isomorphisms, with the reverse transport
as inverse. No order restriction on s,t is imposed. -/
def transport_equivType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t : Icc a b),
    ∃ L : E (c s) ≃ₗ[ℝ] E (c t),
      (∀ ξ, L ξ = transport C c s t ξ) ∧
      (∀ η, L.symm η = transport C c t s η)

def transport_isometryType : Prop :=
  ∀ {n r : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E} (C : Connection B)
    (h : SmoothFiberMetric B), IsMetricConnection C h →
    ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b) (s t : Icc a b) (ξ η : E (c s)),
      h.form (c t) (transport C c s t ξ) (transport C c s t η) = h.form (c s) ξ η

end P202Specs.Geometry.ParallelTransport
