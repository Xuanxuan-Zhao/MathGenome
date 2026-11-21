import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularCornerRounding
import Mathlib.Topology.Maps.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Raw finite parametrizations for the literal corner surgery of
paper.tex:2669–2678. The inputs below are circle, chart, and finite-cut geometry.
In particular they contain no local extension or boundary display certificate. -/
noncomputable section
open Set Metric
open scoped Topology ContDiff NNReal

namespace D12Complex.CircularRetainedDisplay
open CircularExhaustion CircularCornerRounding

/-- The supplied signed circular arrays, including their actual local side. -/
structure CircleData (U : Set ℂ) where
  n : ℕ
  center : Fin n → ℂ
  radius : Fin n → ℝ
  start : Fin n → ℝ
  stop : Fin n → ℝ
  sign : Fin n → ℝ
  bounds : ∀ i, 0 < radius i ∧ start i < stop i ∧ stop i - start i ≤ 2 * Real.pi
  signs : ∀ i, sign i = 1 ∨ sign i = -1
  cover : frontier U = ⋃ i, arcParam (center i) (radius i) '' Icc (start i) (stop i)
  injective : ∀ i, InjOn (arcParam (center i) (radius i)) (Ioo (start i) (stop i))
  disjoint : ∀ i j, i ≠ j → Disjoint
    (arcParam (center i) (radius i) '' Ioo (start i) (stop i))
    (arcParam (center j) (radius j) '' Ioo (start j) (stop j))
  side : ∀ i t, t ∈ Ioo (start i) (stop i) → ∃ W : Set ℂ,
    IsOpen W ∧ arcParam (center i) (radius i) t ∈ W ∧
    ∀ z ∈ W, z ∈ U ↔ sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0

/-- Ordinary C1 sector charts, with the common radius and inverse bound. -/
structure Charts (U : Set ℂ) (J : Finset ℂ) where
  e : ℂ → OpenPartialHomeomorph ℂ ℂ
  angle : ℂ → ℝ
  radius : ℝ
  lip : ℝ≥0
  radius_pos : 0 < radius
  lip_pos : 0 < lip
  angles : ∀ p ∈ J, 0 < angle p ∧ angle p < 2 * Real.pi
  side : ∀ p ∈ J, (e p).IsImage U (sector (angle p))
  smooth : ∀ p ∈ J, ContDiffOn ℝ 1 (e p) (e p).source ∧
    ContDiffOn ℝ 1 (e p).symm (e p).target
  normalized : ∀ p ∈ J, p ∈ (e p).source ∧ e p p = 0
  disjoint : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source
  target_ball : ∀ p ∈ J, closedBall (0 : ℂ) radius ⊆ (e p).target
  inverse_bound : ∀ p ∈ J, LipschitzOnWith lip (e p).symm (closedBall (0 : ℂ) radius)

/-- The domain is the literal finite removal, not an existential rounding. -/
def surgeryDomain {U : Set ℂ} {J : Finset ℂ} (H : Charts U J) (ε : ℝ) : Set ℂ :=
  U \ ⋃ p ∈ J, (H.e p).symm '' sectorTip ε (H.angle p)

def insertedCurve {U : Set ℂ} {J : Finset ℂ} (H : Charts U J) (ε : ℝ) (p : ℂ)
    (t : ℝ) : ℂ := (H.e p).symm (roundingArc ε (H.angle p) t)

/-- Only finite node geometry is assumed; there is no parametrized regular
extension among these inputs. -/
structure CutData {U : Set ℂ} (C : CircleData U) (V : Set ℂ) where
  count : Fin C.n → ℕ
  node : (i : Fin C.n) → Fin (count i + 1) → ℝ
  strict : ∀ i, StrictMono (node i)
  first : ∀ i, node i 0 = C.start i
  last : ∀ i, node i (Fin.last (count i)) = C.stop i
  retained : (i : Fin C.n) → Fin (count i) → Bool
  retained_frontier : ∀ i j, retained i j = true →
    arcParam (C.center i) (C.radius i) '' Icc (node i j.castSucc) (node i j.succ) ⊆ frontier V
  retained_cover : frontier U ∩ frontier V =
    ⋃ (i : Fin C.n) (j : Fin (count i)) (_h : retained i j = true),
      arcParam (C.center i) (C.radius i) '' Icc (node i j.castSucc) (node i j.succ)
  classification : ∀ i j t, t ∈ Ioo (node i j.castSucc) (node i j.succ) →
    (arcParam (C.center i) (C.radius i) t ∈ frontier V ↔ retained i j = true)
  unchanged_side : ∀ i j, retained i j = true → ∀ t,
    t ∈ Ioo (node i j.castSucc) (node i j.succ) → ∃ W : Set ℂ,
      IsOpen W ∧ arcParam (C.center i) (C.radius i) t ∈ W ∧ U ∩ W = V ∩ W ∧
      ∀ z ∈ W, z ∈ U ↔ C.sign i * (‖z - C.center i‖ ^ 2 - C.radius i ^ 2) < 0

def RetainedIndex {U V : Set ℂ} {C : CircleData U} (P : CutData C V) :=
  {q : (i : Fin C.n) × Fin (P.count i) // P.retained q.1 q.2 = true}

/-- Endpoint agreement is one-sided when necessary; the total literal circle
is deliberately not required to remain on the frontier past an endpoint. -/
def HasLocalRegularExtensions (V : Set ℂ) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∃ (δ : ℝ) (W : Set ℂ) (η : ℝ → ℂ),
    0 < δ ∧ IsOpen W ∧ γ t ∈ W ∧
    ContDiffOn ℝ 1 η (Ioo (t - δ) (t + δ)) ∧
    (∀ s ∈ Ioo (t - δ) (t + δ), deriv η s ≠ 0) ∧
    EqOn η γ (Ioo (t - δ) (t + δ) ∩ Icc a b) ∧
    Topology.IsEmbedding (fun s : Ioo (t - δ) (t + δ) => η s) ∧
    η '' Ioo (t - δ) (t + δ) = frontier V ∩ W

/-- A finite set containing every possible nontrivial overlap. -/
def endpointSet {m : ℕ} (γ : Fin m → ℝ → ℂ) (a b : Fin m → ℝ) : Set ℂ :=
  Set.range (fun i => γ i (a i)) ∪ Set.range (fun i => γ i (b i))

/-- Exact finite enumeration and literal interval data, with the full closed
endpoint extension requirement for every displayed piece. -/
structure RawDisplay {U : Set ℂ} {J : Finset ℂ} (C : CircleData U) (H : Charts U J)
    (ε : ℝ) (P : CutData C (surgeryDomain H ε)) where
  count : ℕ
  curve : Fin count → ℝ → ℂ
  left : Fin count → ℝ
  right : Fin count → ℝ
  index : Fin count ≃ (RetainedIndex P ⊕ {p : ℂ // p ∈ J})
  literal : ∀ i, curve i = match index i with
    | .inl q => arcParam (C.center q.val.1) (C.radius q.val.1)
    | .inr p => insertedCurve H ε p
  left_eq : ∀ i, left i = match index i with
    | .inl q => P.node q.val.1 q.val.2.castSucc
    | .inr _ => 0
  right_eq : ∀ i, right i = match index i with
    | .inl q => P.node q.val.1 q.val.2.succ
    | .inr _ => 1
  start_point : ∀ i, curve i (left i) = match index i with
    | .inl q => arcParam (C.center q.val.1) (C.radius q.val.1) (P.node q.val.1 q.val.2.castSucc)
    | .inr p => (H.e p).symm (ε : ℂ)
  stop_point : ∀ i, curve i (right i) = match index i with
    | .inl q => arcParam (C.center q.val.1) (C.radius q.val.1) (P.node q.val.1 q.val.2.succ)
    | .inr p => (H.e p).symm ((ε : ℂ) * Complex.exp ((H.angle p : ℂ) * Complex.I))
  positive : ∀ i, left i < right i
  regular : ∀ i, ∃ T : Set ℝ, IsOpen T ∧ Icc (left i) (right i) ⊆ T ∧
    ContDiffOn ℝ 1 (curve i) T ∧ ∀ t ∈ Icc (left i) (right i), deriv (curve i) t ≠ 0
  cover : frontier (surgeryDomain H ε) = ⋃ i, curve i '' Icc (left i) (right i)
  injective : ∀ i, InjOn (curve i) (Ioo (left i) (right i))
  disjoint : ∀ i j, i ≠ j → Disjoint
    (curve i '' Ioo (left i) (right i)) (curve j '' Ioo (left j) (right j))
  finite_endpoints : (endpointSet curve left right).Finite
  overlaps : ∀ i j s t, s ∈ Icc (left i) (right i) → t ∈ Icc (left j) (right j) →
    curve i s = curve j t → (i ≠ j ∨ s ≠ t) → curve i s ∈ endpointSet curve left right
  extensions : ∀ i, HasLocalRegularExtensions (surgeryDomain H ε) (curve i) (left i) (right i)

end D12Complex.CircularRetainedDisplay

namespace Specs.D12Complex.Ch14.CircularRetainedDisplay
open _root_.D12Complex.CircularRetainedDisplay
open _root_.D12Complex.CircularCornerRounding

/-- The unchanged complete child obligation, at every allowed scale and for
all supplied raw arrays and cut data. -/
def circular_retained_display_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
    ∀ (C : CircleData U) (H : Charts U J) (ε : ℝ), 0 < ε → ε < H.radius →
      ∀ P : CutData C (surgeryDomain H ε), Nonempty (RawDisplay C H ε P)

/-- Generic endpoint extension, a proper reusable component of the main goal. -/
def regular_extension_type : Prop :=
  ∀ (V : Set ℂ), HasC1DefiningFunctions V → ∀ (γ : ℝ → ℂ) (a b : ℝ), a < b →
    (∃ T : Set ℝ, IsOpen T ∧ Icc a b ⊆ T ∧ ContDiffOn ℝ 1 γ T) →
    (∀ t ∈ Icc a b, deriv γ t ≠ 0) → γ '' Icc a b ⊆ frontier V →
    HasLocalRegularExtensions V γ a b

end Specs.D12Complex.Ch14.CircularRetainedDisplay
