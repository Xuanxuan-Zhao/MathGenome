import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularCornerRounding
import Mathlib.Order.Fin.Basic

/-! Independent statements for the angular part of literal circular surgery.
The main statement takes only the original geometry and the supplied arrays.
All subdivisions, labels, scalar changes and estimates are conclusions. -/
noncomputable section
open Set Metric
open scoped Topology ContDiff NNReal

namespace D12Complex.CircularAngularCuts
open CircularExhaustion CircularCornerRounding

/-- The hypotheses on the supplied arrays, including their actual set side. -/
def BoundaryHypotheses (U : Set ℂ) (n : ℕ) (center : Fin n → ℂ)
    (radius start stop sign : Fin n → ℝ) : Prop :=
  (∀ i, 0 < radius i ∧ start i < stop i ∧ stop i - start i ≤ 2 * Real.pi) ∧
  (∀ i, sign i = 1 ∨ sign i = -1) ∧
  frontier U = ⋃ i, arcParam (center i) (radius i) '' Icc (start i) (stop i) ∧
  (∀ i j, i ≠ j → Disjoint
    (arcParam (center i) (radius i) '' Ioo (start i) (stop i))
    (arcParam (center j) (radius j) '' Ioo (start j) (stop j))) ∧
  (∀ i, InjOn (arcParam (center i) (radius i)) (Ioo (start i) (stop i))) ∧
  ∀ i, ∀ t ∈ Ioo (start i) (stop i), ∃ W : Set ℂ,
    IsOpen W ∧ arcParam (center i) (radius i) t ∈ W ∧
    ∀ z ∈ W, z ∈ U ↔ sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0

/-- Actual disjoint normalized charts with a common radius and inverse bound. -/
structure UniformCharts (U : Set ℂ) (J : Finset ℂ) where
  angle : ℂ → ℝ
  chart : ℂ → OpenPartialHomeomorph ℂ ℂ
  R : ℝ
  L : ℝ≥0
  radius_pos : 0 < R
  lipschitz_pos : 0 < L
  angle_bounds : ∀ p ∈ J, 0 < angle p ∧ angle p < 2 * Real.pi
  side : ∀ p ∈ J, (chart p).IsImage U (sector (angle p))
  smooth : ∀ p ∈ J, ContDiffOn ℝ 1 (chart p) (chart p).source ∧
    ContDiffOn ℝ 1 (chart p).symm (chart p).target
  normalized : ∀ p ∈ J, p ∈ (chart p).source ∧ chart p p = 0
  disjoint : ∀ p ∈ J, ∀ q ∈ J, p ≠ q →
    Disjoint (chart p).source (chart q).source
  target_bound : ∀ p ∈ J, closedBall (0 : ℂ) R ⊆ (chart p).target ∧
    LipschitzOnWith L (chart p).symm (closedBall (0 : ℂ) R)

/-- The literal domain, using the canonical model tips. -/
def surgeryDomain {U : Set ℂ} {J : Finset ℂ} (c : UniformCharts U J) (ε : ℝ) : Set ℂ :=
  U \ ⋃ p ∈ J, (c.chart p).symm '' sectorTip ε (c.angle p)

structure Subdivision (a b : ℝ) where
  k : ℕ
  node : Fin (k + 1) → ℝ
  strict : StrictMono node
  first : node 0 = a
  last : node (Fin.last k) = b
  retained : Fin k → Bool

def rayDirection (θ : ℝ) (upper : Bool) : ℂ :=
  if upper then Complex.exp ((θ : ℂ) * Complex.I) else 1

/-- A genuine regular change of the original angular parameter. -/
structure RayChange {U : Set ℂ} {J : Finset ℂ} (c : UniformCharts U J)
    (ε : ℝ) (center : ℂ) (radius a b : ℝ) where
  corner : ℂ
  corner_mem : corner ∈ J
  upper : Bool
  lo : ℝ
  hi : ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  hi_le_one : hi ≤ 1
  scalar : ℝ → ℝ
  neighborhood : Set ℝ
  open_neighborhood : IsOpen neighborhood
  contains_interval : Icc a b ⊆ neighborhood
  smooth : ContDiffOn ℝ 1 scalar neighborhood
  regular : ∀ t ∈ neighborhood, deriv scalar t ≠ 0
  monotonicity :
    (StrictMonoOn scalar (Icc a b) ∧ scalar a = lo ∧ scalar b = hi) ∨
    (StrictAntiOn scalar (Icc a b) ∧ scalar a = hi ∧ scalar b = lo)
  image_interval : scalar '' Icc a b = Icc lo hi
  curve_eq : ∀ t ∈ Icc a b, arcParam center radius t =
    (c.chart corner).symm ((ε * scalar t) • rayDirection (c.angle corner) upper)

/-- Full cut data at one scale; each deleted piece has exactly one ray change. -/
structure CutsAt {U : Set ℂ} {J : Finset ℂ} (c : UniformCharts U J)
    (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ)
    (ε Cdel : ℝ) where
  cuts : ∀ i, Subdivision (start i) (stop i)
  retained_closed : ∀ i (j : Fin (cuts i).k), (cuts i).retained j = true →
    arcParam (center i) (radius i) ''
      Icc ((cuts i).node j.castSucc) ((cuts i).node j.succ) ⊆ frontier (surgeryDomain c ε)
  retained_cover : ∀ z : ℂ, z ∈ frontier U ∩ frontier (surgeryDomain c ε) ↔
    ∃ (i : Fin n) (j : Fin (cuts i).k), (cuts i).retained j = true ∧
      z ∈ arcParam (center i) (radius i) ''
        Icc ((cuts i).node j.castSucc) ((cuts i).node j.succ)
  open_classification : ∀ i (j : Fin (cuts i).k),
    ∀ t ∈ Ioo ((cuts i).node j.castSucc) ((cuts i).node j.succ),
      arcParam (center i) (radius i) t ∈ frontier (surgeryDomain c ε) ↔
        (cuts i).retained j = true
  retained_side : ∀ i (j : Fin (cuts i).k), (cuts i).retained j = true →
    ∀ t ∈ Ioo ((cuts i).node j.castSucc) ((cuts i).node j.succ), ∃ W : Set ℂ,
      IsOpen W ∧ arcParam (center i) (radius i) t ∈ W ∧
      U ∩ W = surgeryDomain c ε ∩ W ∧
      ∀ z ∈ W, z ∈ surgeryDomain c ε ↔
        sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0
  deleted : ∀ i (j : Fin (cuts i).k), (cuts i).retained j = false →
    RayChange c ε (center i) (radius i) ((cuts i).node j.castSucc) ((cuts i).node j.succ)
  radial_cover : ∀ p ∈ J, ∀ upper : Bool, ∀ s ∈ Icc (0 : ℝ) 1,
    ∃ (i : Fin n) (j : Fin (cuts i).k) (h : (cuts i).retained j = false),
      (deleted i j h).corner = p ∧ (deleted i j h).upper = upper ∧
      s ∈ Icc (deleted i j h).lo (deleted i j h).hi
  radial_disjoint : ∀ i (j : Fin (cuts i).k) (h : (cuts i).retained j = false),
    ∀ i' (j' : Fin (cuts i').k) (h' : (cuts i').retained j' = false),
      (i, j.val) ≠ (i', j'.val) →
      (deleted i j h).corner = (deleted i' j' h').corner →
      (deleted i j h).upper = (deleted i' j' h').upper →
      Disjoint (Ioo (deleted i j h).lo (deleted i j h).hi)
        (Ioo (deleted i' j' h').lo (deleted i' j' h').hi)
  corner_cuts : ∀ i, ∀ t ∈ Icc (start i) (stop i),
    arcParam (center i) (radius i) t ∈ J → t ∈ Set.range (cuts i).node
  deleted_length :
    (∑ i, ∑ j : Fin (cuts i).k, if (cuts i).retained j then 0 else
      radius i * ((cuts i).node j.succ - (cuts i).node j.castSucc)) ≤ Cdel * ε

end D12Complex.CircularAngularCuts

namespace Specs.D12Complex.Ch14.CircularAngularCuts
open _root_.D12Complex.CircularAngularCuts
open _root_.D12Complex.CircularCornerRounding

/-- The unchanged complete obligation. Empty sets and empty index types are allowed. -/
def circular_angular_cuts_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
  ∀ (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ),
    BoundaryHypotheses U n center radius start stop sign →
    ∃ (c : UniformCharts U J) (ε₀ Cdel : ℝ),
      0 < ε₀ ∧ ε₀ ≤ c.R ∧ 0 < Cdel ∧
      (∀ p ∈ J, ∀ i, ∀ q ∈ ({_root_.D12Complex.CircularExhaustion.arcParam (center i) (radius i) (start i),
          _root_.D12Complex.CircularExhaustion.arcParam (center i) (radius i) (stop i)} : Set ℂ),
        q ≠ p → q ∉ (c.chart p).source) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → Nonempty (CutsAt c n center radius start stop sign ε Cdel)

def exists_uniform_charts_avoiding_type : Prop :=
  ∀ (U : Set ℂ) (J K : Finset ℂ), RoundingGeometry U J →
    ∃ c : UniformCharts U J, ∀ p ∈ J, ∀ q ∈ K,
      q ≠ p → q ∉ (c.chart p).source

def literal_surgery_regular_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
  ∀ (c : UniformCharts U J) (ε : ℝ), 0 < ε → ε < c.R →
    IsOpen (surgeryDomain c ε) ∧ HasC1DefiningFunctions (surgeryDomain c ε) ∧
      Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain
        (realPlane '' surgeryDomain c ε) ∧
      HasRegularBoundaryParametrizations (surgeryDomain c ε)

end Specs.D12Complex.Ch14.CircularAngularCuts
