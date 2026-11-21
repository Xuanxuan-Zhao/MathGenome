import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SmoothMetrics
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.ProjIcc

/-! Compact interval curves use ambient C¹ coordinate extensions on each closed
piece. No extension with values in the manifold is required. The total function
representation is constrained only on the stated compact interval. -/
set_option autoImplicit false

namespace P202.CurveData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData P202.MetricData
open Set Filter
open scoped Topology
universe u

variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]

/-- Local C¹ regularity up to the endpoints of a closed piece. The extension
is Euclidean-valued, including when the target has boundary. -/
def CoordinateC1On (S : SmoothManifold n kind M) (c : ℝ → M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ e ∈ S.smoothStructure.val, c t ∈ e.source ∧
    ∃ x : ℝ → Euclidean n, ContDiffAt ℝ 1 x t ∧
      x t = (e (c t)).val ∧
      (fun s => (e (c s)).val) =ᶠ[𝓝[J] t] x

/-- Repeated nodes are allowed: they represent harmless empty pieces, and allow
degenerate intervals without a separate curve type. No derivative, velocity,
chain rule, or integrability certificate is part of this structure. -/
structure PiecewiseC1Curve (S : SmoothManifold n kind M) (a b : ℝ) where
  ordered : a ≤ b
  toFun : ℝ → M
  continuousOn : ContinuousOn toFun (Icc a b)
  pieces : ℕ
  node : Fin (pieces + 1) → ℝ
  monotone_node : Monotone node
  first_node : node 0 = a
  last_node : node (Fin.last pieces) = b
  regular : ∀ i : Fin pieces,
    CoordinateC1On S toFun (Icc (node i.castSucc) (node i.succ))

instance {S : SmoothManifold n kind M} {a b : ℝ} :
    CoeFun (PiecewiseC1Curve S a b) (fun _ => ℝ → M) := ⟨fun c => c.toFun⟩

/-- Includes all possible corners and both endpoints, even for a degenerate
interval. These are a finite set, rather than differentiability assumptions. -/
noncomputable def breakpoints {S : SmoothManifold n kind M} {a b : ℝ}
    (c : PiecewiseC1Curve S a b) : Finset ℝ :=
  Finset.univ.image c.node

/-- The original compact-interval map represented by the total function. -/
def compactCurve {S : SmoothManifold n kind M} {a b : ℝ}
    (c : PiecewiseC1Curve S a b) : Icc a b → M := fun t => c t.val

/-- The same definition for curves whose domain is literally the compact
interval. Clamping supplies a total representative only for the coordinate
regularity test; agreement is still required solely within each closed piece. -/
structure CompactPiecewiseC1Curve (S : SmoothManifold n kind M) (a b : ℝ) where
  ordered : a ≤ b
  toFun : Icc a b → M
  continuous : Continuous toFun
  pieces : ℕ
  node : Fin (pieces + 1) → ℝ
  monotone_node : Monotone node
  first_node : node 0 = a
  last_node : node (Fin.last pieces) = b
  regular : ∀ i : Fin pieces,
    CoordinateC1On S (IccExtend ordered toFun) (Icc (node i.castSucc) (node i.succ))

/-- An intrinsic velocity is represented by the coordinate derivative in one
actual atlas chart. The implementation proves that every chart then gives the
same intrinsic tangent vector. Continuity prevents using a chart outside its
domain near the parameter in this definition. -/
def HasVelocityAt (S : SmoothManifold n kind M) (c : ℝ → M) (t : ℝ)
    (v : TangentSpace S (c t)) : Prop :=
  ContinuousAt c t ∧ ∃ e, ∃ he : e ∈ S.smoothStructure.val, ∃ hp : c t ∈ e.source,
    HasDerivAt (fun s => (e (c s)).val)
      ((tangentStructure S).fiberCoordinates.equiv e he
        (c t) hp v) t

/-- The unique intrinsic velocity at differentiable parameters, and zero at
parameters where no velocity exists. It depends on neither a partition nor
selected coordinate extensions. -/
noncomputable def velocity (S : SmoothManifold n kind M) (c : ℝ → M) (t : ℝ) :
    TangentSpace S (c t) := by
  classical
  exact if h : ∃ v, HasVelocityAt S c t v then Classical.choose h else 0

noncomputable def speed {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (c : ℝ → M) (t : ℝ) : ℝ := tangentNorm g (c t) (velocity S c t)

noncomputable def length {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) : ℝ := ∫ t in a..b, speed g c t

noncomputable def energy {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in a..b, (speed g c t) ^ 2

/-- A local ambient scalar C1 extension with positive derivative, including
one-sided endpoint germs on a closed subinterval. -/
def RegularRealC1On (φ : ℝ → ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 1 ψ t ∧ φ t = ψ t ∧
    φ =ᶠ[𝓝[J] t] ψ ∧ 0 < deriv ψ t

/-- A finite piecewise regular increasing change of compact parameter.
The compact order isomorphism records increasingness and surjectivity. -/
structure PiecewiseRegularIncreasing (a b l r : ℝ) where
  source_ordered : l ≤ r
  target_ordered : a ≤ b
  map : Icc l r ≃o Icc a b
  pieces : ℕ
  node : Fin (pieces + 1) → ℝ
  monotone_node : Monotone node
  first_node : node 0 = l
  last_node : node (Fin.last pieces) = r
  regular : ∀ i : Fin pieces,
    RegularRealC1On (IccExtend source_ordered (fun t => (map t).val))
      (Icc (node i.castSucc) (node i.succ))

noncomputable def PiecewiseRegularIncreasing.toFun {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : ℝ → ℝ :=
  IccExtend φ.source_ordered (fun t => (φ.map t).val)

noncomputable instance {a b l r : ℝ} :
    CoeFun (PiecewiseRegularIncreasing a b l r) (fun _ => ℝ → ℝ) :=
  ⟨PiecewiseRegularIncreasing.toFun⟩

noncomputable def parameterBreakpoints {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : Finset ℝ :=
  Finset.univ.image φ.node

end P202.CurveData


set_option linter.unusedVariables false

namespace P202Specs.Geometry.PiecewiseCurves
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData P202.MetricData P202.CurveData
open Set Filter
open scoped Topology
universe u

def coordinateC1OnType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n kind M → (ℝ → M) → Set ℝ → Prop

def piecewiseC1CurveType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n kind M → ℝ → ℝ → Type u

def compactPiecewiseC1CurveType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n kind M → ℝ → ℝ → Type u

def breakpointsType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n kind M} → {a b : ℝ} → PiecewiseC1Curve S a b → Finset ℝ

def compactCurveType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n kind M} → {a b : ℝ} → PiecewiseC1Curve S a b → (Icc a b → M)

def hasVelocityAtType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n kind M) → (c : ℝ → M) →
  (t : ℝ) → TangentSpace S (c t) → Prop

def velocityType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → (S : SmoothManifold n kind M) → (c : ℝ → M) →
  (t : ℝ) → TangentSpace S (c t)

def speedType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n kind M} → RiemannianMetric S → (ℝ → M) → ℝ → ℝ

def lengthType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n kind M} → RiemannianMetric S → {a b : ℝ} → PiecewiseC1Curve S a b → ℝ

def energyType :=
  {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n kind M} → RiemannianMetric S → {a b : ℝ} → PiecewiseC1Curve S a b → ℝ

def hasVelocityAt_coordinatesType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {t : ℝ}
    {v : TangentSpace S (c t)} (hv : HasVelocityAt S c t v)
    (d : ModelChart n kind M) (hd : d ∈ S.smoothStructure.val)
    (hpd : c t ∈ d.source),
    HasDerivAt (fun s => (d (c s)).val)
      ((tangentStructure S).fiberCoordinates.equiv d hd (c t) hpd v) t

def hasVelocityAt_uniqueType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {t : ℝ}
    {v w : TangentSpace S (c t)} (hv : HasVelocityAt S c t v)
    (hw : HasVelocityAt S c t w),
    v = w

def velocity_eqType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {t : ℝ} {v : TangentSpace S (c t)}
    (hv : HasVelocityAt S c t v),
    velocity S c t = v

def velocity_congrType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c d : ℝ → M} {t : ℝ}
    (hc : HasVelocityAt S c t (velocity S c t)) (heq : c =ᶠ[𝓝 t] d),
    HEq (velocity S c t) (velocity S d t)

def speed_congr_of_eventuallyEqType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {c d : ℝ → M} {t : ℝ}
    (hc : HasVelocityAt S c t (velocity S c t)) (heq : c =ᶠ[𝓝 t] d),
    speed g c t = speed g d t

def hasVelocityAt_constType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (p : M) (t : ℝ),
    HasVelocityAt S (fun _ => p) t 0

def velocity_constType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (p : M) (t : ℝ),
    velocity S (fun _ => p) t = 0

def coordinateC1On_constType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (p : M) (J : Set ℝ),
    CoordinateC1On S (fun _ => p) J

def CoordinateC1On_exists_velocityType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) {t : ℝ} (hJ : J ∈ 𝓝 t)
    (hc : ContinuousAt c t),
    ∃ v, HasVelocityAt S c t v

def exists_velocity_on_pieceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (i : Fin c.pieces) {t : ℝ}
    (ht : t ∈ Ioo (c.node i.castSucc) (c.node i.succ)),
    ∃ v, HasVelocityAt S c t v

def velocity_on_pieceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (i : Fin c.pieces) {t : ℝ}
    (ht : t ∈ Ioo (c.node i.castSucc) (c.node i.succ)),
    HasVelocityAt S c t (velocity S c t)

def hasVelocityAt_off_breakpointsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {t : ℝ} (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c),
    HasVelocityAt S c t (velocity S c t)

def speed_integrableType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b),
    IntervalIntegrable (speed g c) MeasureTheory.volume a b

def squared_speed_integrableType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b),
    IntervalIntegrable (fun t => speed g c t ^ 2) MeasureTheory.volume a b

def speed_eq_of_eqOnType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) {d : ℝ → M} (heq : EqOn c d (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c),
    speed g c t = speed g d t

def length_eq_of_eqOnType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ}
    (c d : PiecewiseC1Curve S a b) (heq : EqOn c d (Icc a b)),
    length g c = length g d

def energy_eq_of_eqOnType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ}
    (c d : PiecewiseC1Curve S a b) (heq : EqOn c d (Icc a b)),
    energy g c = energy g d

def compactCurve_continuousType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b),
    Continuous (compactCurve c)

def integral_eq_of_eq_off_finiteType : Prop :=
  ∀ {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∉ K → f t = h t),
    (∫ t in a..b, f t) = ∫ t in a..b, h t

def intervalIntegrable_iff_of_eq_off_finiteType : Prop :=
  ∀ {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∉ K → f t = h t),
    IntervalIntegrable f MeasureTheory.volume a b ↔
      IntervalIntegrable h MeasureTheory.volume a b

def integral_norm_eq_of_velocity_eq_off_finiteType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∉ K → v t = w t),
    (∫ t in a..b, tangentNorm g (c t) (v t)) =
      ∫ t in a..b, tangentNorm g (c t) (w t)

def integral_sq_norm_eq_of_velocity_eq_off_finiteType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∉ K → v t = w t),
    (∫ t in a..b, tangentNorm g (c t) (v t) ^ 2) =
      ∫ t in a..b, tangentNorm g (c t) (w t) ^ 2

def HasVelocityAt_postcompType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N} {f : M → N}
    (hf : IsSmoothMap S T f) {c : ℝ → M} {t : ℝ}
    {v : TangentSpace S (c t)} (hv : HasVelocityAt S c t v)
    (L : TangentSpace S (c t) →ₗ[ℝ] TangentSpace T (f (c t)))
    (hL : SmoothManifolds.DifferentialData.IsDifferential S T f (c t) L),
    HasVelocityAt T (f ∘ c) t (L v)

def HasVelocityAt_reparamType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {t r : ℝ} {φ : ℝ → ℝ}
    {v : TangentSpace S (c (φ t))} (hv : HasVelocityAt S c (φ t) v)
    (hφ : HasDerivAt φ r t),
    HasVelocityAt S (c ∘ φ) t (r • v)

def CoordinateC1On_postcompType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N} {f : M → N}
    (hf : IsSmoothMap S T f) {c : ℝ → M} {J : Set ℝ}
    (hc : ContinuousOn c J) (h : CoordinateC1On S c J),
    CoordinateC1On T (f ∘ c) J

def CoordinateC1On_reparamType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {J K : Set ℝ} {φ : ℝ → ℝ}
    (h : CoordinateC1On S c J) (hφ : ∀ t ∈ K, ContDiffAt ℝ 1 φ t)
    (hmaps : MapsTo φ K J),
    CoordinateC1On S (c ∘ φ) K

def coordinateC1On_singletonType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (c : ℝ → M) (t : ℝ),
    CoordinateC1On S c {t}

def length_degenerateType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) (a : ℝ)
    (c : PiecewiseC1Curve S a a),
    length g c = 0

def energy_degenerateType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) (a : ℝ)
    (c : PiecewiseC1Curve S a a),
    energy g c = 0

def finiteConcatenation_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {k : ℕ} (node : Fin (k + 1) → ℝ)
    (p : Fin (k + 1) → M)
    (curves : (i : Fin k) → PiecewiseC1Curve S (node i.castSucc) (node i.succ))
    (hstart : ∀ i, curves i (node i.castSucc) = p i.castSucc)
    (hend : ∀ i, curves i (node i.succ) = p i.succ),
    ∃ c : PiecewiseC1Curve S (node 0) (node (Fin.last k)),
      c (node 0) = p 0 ∧ c (node (Fin.last k)) = p (Fin.last k) ∧
      ∀ (i : Fin k) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) → c t = curves i t

def velocity_eq_of_eqOnType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {d : ℝ → M} (heq : EqOn c d (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c),
    HEq (velocity S c t) (velocity S d t)

def finiteConcatenation_velocityType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {k : ℕ} (node : Fin (k + 1) → ℝ)
    (p : Fin (k + 1) → M)
    (curves : (i : Fin k) → PiecewiseC1Curve S (node i.castSucc) (node i.succ))
    (hstart : ∀ i, curves i (node i.castSucc) = p i.castSucc)
    (hend : ∀ i, curves i (node i.succ) = p i.succ),
    ∃ c : PiecewiseC1Curve S (node 0) (node (Fin.last k)),
      c (node 0) = p 0 ∧ c (node (Fin.last k)) = p (Fin.last k) ∧
      (∀ (i : Fin k) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) → c t = curves i t) ∧
      ∀ (i : Fin k) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
        t ∉ breakpoints (curves i) → HEq (velocity S c t) (velocity S (curves i) t)


/-- Restriction retains the total map and hence its intrinsic velocities. -/
def restriction_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (l r : ℝ) (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b),
    ∃ d : PiecewiseC1Curve S l r, (∀ t, d t = c t) ∧
      ∀ t, HEq (velocity S d t) (velocity S c t)

/-- Reversal retains regularity and reverses each original interior velocity. -/
def reversal_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {a b : ℝ} (c : PiecewiseC1Curve S a b),
    ∃ d : PiecewiseC1Curve S a b, (∀ t, d t = c (a + b - t)) ∧
      ∀ (t : ℝ), a + b - t ∈ Icc a b → a + b - t ∉ breakpoints c →
        HEq (velocity S d t) (-velocity S c (a + b - t))

/-- Smooth postcomposition constructs a curve and satisfies the intrinsic
chain rule for its actual differential. -/
def postcomposition_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M}
    {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N} (f : M → N) (hf : IsSmoothMap S T f)
    {a b : ℝ} (c : PiecewiseC1Curve S a b),
    ∃ d : PiecewiseC1Curve T a b, (∀ t, d t = f (c t)) ∧
      ∀ (t : ℝ), t ∈ Icc a b → t ∉ breakpoints c →
        ∀ (L : TangentSpace S (c t) →ₗ[ℝ] TangentSpace T (f (c t))),
          SmoothManifolds.DifferentialData.IsDifferential S T f (c t) L →
          HEq (velocity T d t) (L (velocity S c t))

/-- Curves on consecutive intervals with matching values concatenate without
altering either map or its interior intrinsic velocities. -/
def concatenation_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (hmatch : c b = d b),
    ∃ e : PiecewiseC1Curve S a z,
      EqOn e c (Icc a b) ∧ EqOn e d (Icc b z) ∧
      (∀ (t : ℝ), t ∈ Icc a b → t < b → t ∉ breakpoints c →
        HEq (velocity S e t) (velocity S c t)) ∧
      (∀ (t : ℝ), t ∈ Icc b z → b < t → t ∉ breakpoints d →
        HEq (velocity S e t) (velocity S d t))

/-- Stationary curves exist on all ordered intervals, including a singleton,
and have zero length and energy for every smooth Riemannian metric. -/
def stationary_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (a b : ℝ) (hab : a ≤ b) (p : M),
    ∃ c : PiecewiseC1Curve S a b, (∀ t, c t = p) ∧
      ∀ g : RiemannianMetric S, length g c = 0 ∧ energy g c = 0

/-- Both representations cover exactly the same compact-domain curves.
Only values on the compact interval are identified. -/
def compact_representationType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} {a b : ℝ},
    (∀ c : PiecewiseC1Curve S a b,
      ∃ d : CompactPiecewiseC1Curve S a b, d.toFun = compactCurve c) ∧
    (∀ d : CompactPiecewiseC1Curve S a b,
      ∃ c : PiecewiseC1Curve S a b, compactCurve c = d.toFun)


/-- Scalar regularity uses local ambient C¹ extensions, including at ends. -/
def regularRealC1OnType := (ℝ → ℝ) → Set ℝ → Prop

def piecewiseRegularIncreasingType := ℝ → ℝ → ℝ → ℝ → Type

def parameterToFunType := {a b l r : ℝ} →
  PiecewiseRegularIncreasing a b l r → ℝ → ℝ

def parameterBreakpointsType := {a b l r : ℝ} →
  PiecewiseRegularIncreasing a b l r → Finset ℝ

def velocity_eq_coordinateExtensionType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hc : ContinuousAt c t) (hJ : J ∈ 𝓝 t)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hp : c t ∈ e.source) {x : ℝ → Euclidean n}
    (hx : ContDiffAt ℝ 1 x t)
    (heq : (fun s => (e (c s)).val) =ᶠ[𝓝[J] t] x),
    velocity S c t = ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp).symm
      (deriv x t)

def coordinateExtension_independentType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {c : ℝ → M} {J K : Set ℝ} {t : ℝ}
    (hc : ContinuousAt c t) (hJ : J ∈ 𝓝 t) (hK : K ∈ 𝓝 t)
    (e d : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (hp : c t ∈ e.source) (hq : c t ∈ d.source)
    {x y : ℝ → Euclidean n} (hx : ContDiffAt ℝ 1 x t) (hy : ContDiffAt ℝ 1 y t)
    (hxeq : (fun s => (e (c s)).val) =ᶠ[𝓝[J] t] x)
    (hyeq : (fun s => (d (c s)).val) =ᶠ[𝓝[K] t] y),
    ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp).symm (deriv x t) =
      ((tangentStructure S).fiberCoordinates.equiv d hd (c t) hq).symm (deriv y t)


/-- Shared structures as values for faithful implementation aliases. -/
def piecewiseC1CurveValue : piecewiseC1CurveType := @P202.CurveData.PiecewiseC1Curve

def compactPiecewiseC1CurveValue : compactPiecewiseC1CurveType :=
  @P202.CurveData.CompactPiecewiseC1Curve

def piecewiseRegularIncreasingValue : piecewiseRegularIncreasingType :=
  P202.CurveData.PiecewiseRegularIncreasing

def parameter_representationType : Prop :=
  ∀ {a b l r : ℝ} (hab : a ≤ b) (hlr : l ≤ r)
    (f : ℝ → ℝ) (hmaps : MapsTo f (Icc l r) (Icc a b))
    (hincr : StrictMonoOn f (Icc l r)) (honto : SurjOn f (Icc l r) (Icc a b))
    (k : ℕ) (node : Fin (k + 1) → ℝ) (hnode : Monotone node)
    (hfirst : node 0 = l) (hlast : node (Fin.last k) = r)
    (hregular : ∀ i : Fin k, RegularRealC1On f (Icc (node i.castSucc) (node i.succ))),
    ∃ φ : PiecewiseRegularIncreasing a b l r, EqOn φ f (Icc l r)

def reparametrization_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r),
    ∃ q : PiecewiseC1Curve S l r, (∀ t, q t = c (φ t)) ∧
      ∃ K : Finset ℝ, ∀ t ∈ Icc l r, t ∉ K →
        ContDiffAt ℝ 1 φ t ∧ 0 < deriv φ t ∧
          HEq (velocity S q t) (deriv φ t • velocity S c (φ t))

def reparametrization_exists_off_breakpointsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r),
    ∃ q : PiecewiseC1Curve S l r, (∀ t, q t = c (φ t)) ∧
      ∀ t ∈ Icc l r, t ∉ parameterBreakpoints φ → φ t ∉ breakpoints c →
        HEq (velocity S q t) (deriv φ t • velocity S c (φ t))

def reparametrization_velocity_finite_exceptionsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r),
    ∃ K : Finset ℝ, ∀ t ∈ Icc l r, t ∉ K →
      ContDiffAt ℝ 1 φ t ∧ 0 < deriv φ t ∧
        velocity S (c ∘ φ) t = deriv φ t • velocity S c (φ t)

def parameter_contDiffAt_pos_derivType : Prop :=
  ∀ {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) {t : ℝ}
    (ht : t ∈ Icc l r) (hcorner : t ∉ parameterBreakpoints φ),
    ContDiffAt ℝ 1 φ t ∧ 0 < deriv φ t

def parameter_continuousType : Prop :=
  ∀ {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r),
    Continuous φ

def parameter_mapsToType : Prop :=
  ∀ {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r),
    MapsTo φ (Icc l r) (Icc a b)

def parameter_strictMonoOnType : Prop :=
  ∀ {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r),
    StrictMonoOn φ (Icc l r)

def parameter_surjOnType : Prop :=
  ∀ {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r),
    SurjOn φ (Icc l r) (Icc a b)

def parameter_firstType : Prop :=
  ∀ {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r),
    φ l = a

def parameter_lastType : Prop :=
  ∀ {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r),
    φ r = b

def integral_eq_of_eqOn_off_finiteType : Prop :=
  ∀ {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∈ uIoc a b → t ∉ K → f t = h t),
    (∫ t in a..b, f t) = ∫ t in a..b, h t

def intervalIntegrable_iff_of_eqOn_off_finiteType : Prop :=
  ∀ {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∈ uIoc a b → t ∉ K → f t = h t),
    IntervalIntegrable f MeasureTheory.volume a b ↔
      IntervalIntegrable h MeasureTheory.volume a b

def integral_norm_eq_of_velocity_eqOn_off_finiteType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∈ uIoc a b → t ∉ K → v t = w t),
    (∫ t in a..b, tangentNorm g (c t) (v t)) =
      ∫ t in a..b, tangentNorm g (c t) (w t)

def integral_sq_norm_eq_of_velocity_eqOn_off_finiteType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∈ uIoc a b → t ∉ K → v t = w t),
    (∫ t in a..b, tangentNorm g (c t) (v t) ^ 2) =
      ∫ t in a..b, tangentNorm g (c t) (w t) ^ 2

end P202Specs.Geometry.PiecewiseCurves
