import Mathlib.Topology.MetricSpace.Defs

/-! Independent statement types for paper.tex, W70 and the approximate-evaluation
paragraph of W71. The domain need not be closed or complete; a fixed point is given.
The point used to approximate `T x` need not belong to the contraction domain. -/
namespace Specs.NumAnalysis206.Iterations.ResidualCertificate

universe u

def ResidualBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q < 1) (_hinv : Set.MapsTo T D D)
    (_hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (_hp : p ∈ D) (_hfixed : T p = p) (x : X) (_hx : x ∈ D),
    dist x p ≤ dist x (T x) / (1 - q)

def ResidualUpperBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q < 1) (_hinv : Set.MapsTo T D D)
    (_hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (_hp : p ∈ D) (_hfixed : T p = p) (x : X) (_hx : x ∈ D)
    (R : ℝ) (_hR : dist x (T x) ≤ R),
    dist x p ≤ R / (1 - q)

def ResidualStopping : Prop :=
  ∀ {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q < 1) (_hinv : Set.MapsTo T D D)
    (_hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (_hp : p ∈ D) (_hfixed : T p = p) (x : X) (_hx : x ∈ D)
    (ε R : ℝ) (_hε : 0 < ε) (_hR : dist x (T x) ≤ R)
    (_hstop : R ≤ (1 - q) * ε),
    dist x p ≤ ε

def ApproximateResidualBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (T : X → X) (x y : X)
    (δ : ℝ) (_herror : dist y (T x) ≤ δ),
    dist x (T x) ≤ dist x y + δ

def ApproximateDistanceBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q < 1) (_hinv : Set.MapsTo T D D)
    (_hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (_hp : p ∈ D) (_hfixed : T p = p) (x : X) (_hx : x ∈ D)
    (y : X) (δ R : ℝ) (_herror : dist y (T x) ≤ δ) (_hR : dist x y ≤ R),
    dist x p ≤ (R + δ) / (1 - q)

def ApproximateResidualStopping : Prop :=
  ∀ {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q < 1) (_hinv : Set.MapsTo T D D)
    (_hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (_hp : p ∈ D) (_hfixed : T p = p) (x : X) (_hx : x ∈ D)
    (y : X) (δ ε R : ℝ) (_hε : 0 < ε)
    (_herror : dist y (T x) ≤ δ) (_hR : dist x y ≤ R)
    (_hstop : R + δ ≤ (1 - q) * ε),
    dist x p ≤ ε

end Specs.NumAnalysis206.Iterations.ResidualCertificate
