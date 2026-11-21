import MathGenome.Internal.FourierSobolev.Specs.P102.U4.GraphArea
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Geometry of paper.tex:1714–1732, and the finite localization used at
1756–1761 and 2617–2669. `Ambient m` is Euclidean (m+1)-space, with
its L² norm, including m=0. There are no Sobolev/trace certificates in
any of the geometric definitions. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal ContDiff

namespace P102.Sobolev.Geometry
open P102.U4 P102.U4.GraphPieces

def shear {m : ℕ} (γ : Space m → ℝ) (z : Ambient m) : Ambient m :=
  WithLp.toLp 2 (z.ofLp.1, γ z.ofLp.1 + z.ofLp.2)

def unshear {m : ℕ} (γ : Space m → ℝ) (z : Ambient m) : Ambient m :=
  WithLp.toLp 2 (z.ofLp.1, z.ofLp.2 - γ z.ofLp.1)

def strip {m : ℕ} (B : Set (Space m)) : Set (Ambient m) :=
  {z | z.ofLp.1 ∈ B}

def cylinder {m : ℕ} (c : Space m) (r a : ℝ) : Set (Ambient m) :=
  {z | z.ofLp.1 ∈ ball c r ∧ z.ofLp.2 ∈ Ioo (-a) a}

def upperCylinder {m : ℕ} (c : Space m) (r a : ℝ) : Set (Ambient m) :=
  {z | z.ofLp.1 ∈ ball c r ∧ z.ofLp.2 ∈ Ioo 0 a}

def chartImage {m : ℕ} (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m)
    (γ : Space m → ℝ) (c : Space m) (r a : ℝ) : Set (Ambient m) :=
  e '' (shear γ '' cylinder c r a)

/-- Only the local graph and one-sided set conditions are hypotheses. In
particular Lipschitzness and measure preservation of the flattening are not fields. -/
structure BoundaryChart {m : ℕ} (Ω : Set (Ambient m)) where
  frame : Ambient m ≃ᵃⁱ[ℝ] Ambient m
  center : Space m
  radius : ℝ
  height : ℝ
  radius_pos : 0 < radius
  height_pos : 0 < height
  graphFunction : Space m → ℝ
  constant : ℝ≥0
  graph_lipschitz : LipschitzOnWith constant graphFunction (ball center radius)
  side : Ω ∩ chartImage frame graphFunction center radius height =
    frame '' (shear graphFunction '' upperCylinder center radius height)
  boundary : frontier Ω ∩ chartImage frame graphFunction center radius height =
    frame '' (graph graphFunction '' ball center radius)

def IsLipschitzOpen {m : ℕ} (Ω : Set (Ambient m)) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧
    ∀ p ∈ frontier Ω, ∃ C : BoundaryChart Ω,
      C.frame (graph C.graphFunction C.center) = p

def IsLipschitzDomain {m : ℕ} (Ω : Set (Ambient m)) : Prop :=
  IsLipschitzOpen Ω ∧ IsConnected Ω

/-- A convenient finite constant; optimal Lipschitz constants are not asserted. -/
def shearConstant (L : ℝ≥0) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal * max 1 (L + 1)

def graphConstant (L : ℝ≥0) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal * max 1 L

namespace Expected

def lipschitzOpenType := {m : ℕ} → Set (Ambient m) → Prop

def lipschitzOpenValue : lipschitzOpenType := fun Ω =>
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧
    ∀ p ∈ frontier Ω, ∃ C : BoundaryChart Ω,
      C.frame (graph C.graphFunction C.center) = p

def lipschitzDomainType := {m : ℕ} → Set (Ambient m) → Prop

def lipschitzDomainValue : lipschitzDomainType := fun Ω =>
  lipschitzOpenValue Ω ∧ IsConnected Ω

def ShearInverse : Prop :=
  ∀ (m : ℕ) (γ : Space m → ℝ),
    Function.LeftInverse (unshear γ) (shear γ) ∧
      Function.RightInverse (unshear γ) (shear γ)

def ShearLipschitz : Prop :=
  ∀ (m : ℕ) (B : Set (Space m)) (γ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L γ B →
      LipschitzOnWith (shearConstant L) (shear γ) (strip B) ∧
      LipschitzOnWith (shearConstant L) (unshear γ) (strip B)

/-- All subsets, without a measurability restriction, use Lebesgue outer measure. -/
def ShearVolume : Prop :=
  ∀ (m : ℕ) (B : Set (Space m)) (γ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L γ B → ∀ S : Set (Ambient m), S ⊆ strip B →
      volume (shear γ '' S) = volume S ∧ volume (unshear γ '' S) = volume S

def GraphGeometry : Prop :=
  ∀ (m : ℕ) (B : Set (Space m)) (γ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L γ B →
      LipschitzOnWith (graphConstant L) (graph γ) B ∧
      (∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist (graph γ x) (graph γ y)) ∧
      ∀ S : Set (Space m), S ⊆ B →
        volume S ≤ (μHE[m] : Measure (Ambient m)) (graph γ '' S) ∧
        (μHE[m] : Measure (Ambient m)) (graph γ '' S) ≤
          (graphConstant L : ℝ≥0∞) ^ m * volume S

/-- The same surface comparison in any rigid coordinate frame. -/
def GraphGeometryInFrame : Prop :=
  ∀ (m : ℕ) (B : Set (Space m)) (γ : Space m → ℝ) (L : ℝ≥0),
    LipschitzOnWith L γ B → ∀ e : Ambient m ≃ᵃⁱ[ℝ] Ambient m,
      LipschitzOnWith (graphConstant L) (e ∘ graph γ) B ∧
      (∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist (e (graph γ x)) (e (graph γ y))) ∧
      ∀ S : Set (Space m), S ⊆ B →
        volume S ≤ (μHE[m] : Measure (Ambient m)) ((e ∘ graph γ) '' S) ∧
        (μHE[m] : Measure (Ambient m)) ((e ∘ graph γ) '' S) ≤
          (graphConstant L : ℝ≥0∞) ^ m * volume S

/-- Finite symmetric subcylinders relatively compact in the original cylinders,
and a fixed ambient smooth partition on an open neighborhood of closure Ω.
Index 0 is the interior piece; boundary pieces use indices i.succ. -/
def FiniteLocalization : Prop :=
  ∀ (m : ℕ) (Ω : Set (Ambient m)), IsLipschitzOpen Ω →
    ∃ (n : ℕ) (C : Fin n → BoundaryChart Ω) (r a : Fin n → ℝ),
      (∀ i, 0 < r i ∧ r i < (C i).radius ∧ 0 < a i ∧ a i < (C i).height) ∧
      frontier Ω ⊆ ⋃ i, chartImage (C i).frame (C i).graphFunction (C i).center (r i) (a i) ∧
      ∃ (V : Set (Ambient m)) (χ : Fin (n + 1) → Ambient m → ℝ),
        IsOpen V ∧ closure Ω ⊆ V ∧
        (∀ i, ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧ ∀ x, 0 ≤ χ i x) ∧
        (∀ x ∈ V, ∑ i, χ i x = 1) ∧
        tsupport (χ 0) ⊆ Ω ∧
        (∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ tsupport (χ 0), ∀ y ∈ frontier Ω, ε ≤ dist x y) ∧
        ∀ i : Fin n, tsupport (χ i.succ) ⊆
          chartImage (C i).frame (C i).graphFunction (C i).center (r i) (a i)

/-- Strictly smaller symmetric cylinders are relatively compact in the full
physical chart; this is also used to keep reflected supports inside the chart. -/
def SmallerChartCompact : Prop :=
  ∀ (m : ℕ) (Ω : Set (Ambient m)) (C : BoundaryChart Ω) (r a : ℝ),
    0 < r → r < C.radius → 0 < a → a < C.height →
      IsCompact (closure (chartImage C.frame C.graphFunction C.center r a)) ∧
      closure (chartImage C.frame C.graphFunction C.center r a) ⊆
        chartImage C.frame C.graphFunction C.center C.radius C.height

/-- The full local condition in dimension one, including disconnected and empty
sets, is equivalent to a finite disjoint interval decomposition. Endpoints
are pairwise distinct, including endpoints from different components. -/
def OneDimension : Prop :=
  ∀ Ω : Set (Ambient 0), IsLipschitzOpen Ω ↔
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧
      Function.Injective (Sum.elim a b) ∧
      Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) ∧
      Ω = ⋃ i, {z | z.ofLp.2 ∈ Ioo (a i) (b i)} ∧
      frontier Ω = ⋃ i, {WithLp.toLp 2 (0, a i), WithLp.toLp 2 (0, b i)}

def CountingBoundary : Prop :=
  (μHE[0] : Measure (Ambient 0)) = Measure.count

def EmptyOpen : Prop := ∀ m : ℕ, IsLipschitzOpen (∅ : Set (Ambient m))

end Expected
end P102.Sobolev.Geometry
