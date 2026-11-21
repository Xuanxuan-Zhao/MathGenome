import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PiecewiseCurves

/-! Length laws for the canonical intrinsic metric and compact piecewise C¹
curves. Only libraries and independent upstream Specs are imported here.
All model kinds and dimensions, stationary pieces, and singleton intervals
are included. No velocity, speed formula, or length equality is assumed. -/
set_option autoImplicit false
namespace P202Specs.Geometry.LengthLaws
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.CurveData
open Set
universe u

def isometricImmersion_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N}
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : M → N),
  IsIsometricImmersion g h f →
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b) (d : PiecewiseC1Curve T a b),
    EqOn d (f ∘ c) (Icc a b) → length h d = length g c

def localIsometry_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N}
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : M → N),
  IsLocalIsometry g h f →
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b) (d : PiecewiseC1Curve T a b),
    EqOn d (f ∘ c) (Icc a b) → length h d = length g c

def localIsometry_length_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N}
    (g : RiemannianMetric S) (h : RiemannianMetric T) (f : M → N),
  IsLocalIsometry g h f →
  ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b),
    ∃ d : PiecewiseC1Curve T a b,
      (∀ t, d t = f (c t)) ∧ length h d = length g c

def subdivision_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {k : ℕ} (node : Fin (k + 1) → ℝ) (hnode : Monotone node)
    (hfirst : node 0 = a) (hlast : node (Fin.last k) = b),
  ∀ (pieces : (i : Fin k) → PiecewiseC1Curve S (node i.castSucc) (node i.succ)),
    (∀ i : Fin k, EqOn (pieces i) c (Icc (node i.castSucc) (node i.succ))) →
    length g c = ∑ i : Fin k, length g (pieces i)

def subdivision_length_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {k : ℕ} (node : Fin (k + 1) → ℝ) (hnode : Monotone node)
    (hfirst : node 0 = a) (hlast : node (Fin.last k) = b),
  ∃ pieces : (i : Fin k) → PiecewiseC1Curve S (node i.castSucc) (node i.succ),
    (∀ i : Fin k, ∀ t, pieces i t = c t) ∧
      length g c = ∑ i : Fin k, length g (pieces i)

def finiteConcatenation_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {k : ℕ} (node : Fin (k + 1) → ℝ)
    (p : Fin (k + 1) → M)
    (curves : (i : Fin k) → PiecewiseC1Curve S (node i.castSucc) (node i.succ))
    (hstart : ∀ i, curves i (node i.castSucc) = p i.castSucc)
    (hend : ∀ i, curves i (node i.succ) = p i.succ),
    ∃ c : PiecewiseC1Curve S (node 0) (node (Fin.last k)),
      c (node 0) = p 0 ∧ c (node (Fin.last k)) = p (Fin.last k) ∧
      (∀ i : Fin k, EqOn c (curves i) (Icc (node i.castSucc) (node i.succ))) ∧
      length g c = ∑ i : Fin k, length g (curves i)

def concatenation_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b z : ℝ}
    (c : PiecewiseC1Curve S a b) (d : PiecewiseC1Curve S b z),
    c b = d b → ∃ e : PiecewiseC1Curve S a z,
      EqOn e c (Icc a b) ∧ EqOn e d (Icc b z) ∧
      length g e = length g c + length g d

def reversal_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ} (c : PiecewiseC1Curve S a b),
  ∀ d : PiecewiseC1Curve S a b,
    EqOn d (fun t => c (a + b - t)) (Icc a b) → length g d = length g c

def reversal_length_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b : ℝ} (c : PiecewiseC1Curve S a b),
  ∃ d : PiecewiseC1Curve S a b,
    (∀ t, d t = c (a + b - t)) ∧ length g d = length g c

def reparametrization_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r),
  ∀ q : PiecewiseC1Curve S l r,
    EqOn q (c ∘ φ) (Icc l r) → length g q = length g c

def reparametrization_length_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r),
  ∃ q : PiecewiseC1Curve S l r,
    (∀ t, q t = c (φ t)) ∧ length g q = length g c

end P202Specs.Geometry.LengthLaws
