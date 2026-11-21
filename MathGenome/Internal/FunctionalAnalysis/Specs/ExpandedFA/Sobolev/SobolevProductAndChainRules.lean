import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! Weak calculus on arbitrary open Euclidean domains, including dimension zero
and p = infinity. HasWeakCoordinateDerivatives is the coordinate formulation of
the canonical distribution derivative graph, not an additional regularity assumption. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Sobolev.Lines
open _root_.ExpandedFA.Distributions

/-- Bounded means essentially bounded; the result is an Lp class with the stated
Lp weak derivatives. The accepted first-order graph characterization identifies
these data with W^{1,p}. -/
def ProductRule : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u v : DomainLp 𝕜 Ω p) (g h : Fin d → DomainLp 𝕜 Ω p),
  HasWeakCoordinateDerivatives u g → HasWeakCoordinateDerivatives v h →
  MemLp u ∞ (volume.restrict (Ω : Set (Domain d))) →
  MemLp v ∞ (volume.restrict (Ω : Set (Domain d))) →
  ∃ (w : DomainLp 𝕜 Ω p) (k : Fin d → DomainLp 𝕜 Ω p),
    HasWeakCoordinateDerivatives w k ∧
    w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => u x * v x) ∧
    ∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => g i x * v x + u x * h i x)

def ChainRule : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p)
    (g : Fin d → DomainLp ℝ Ω p) (F : ℝ → ℝ),
  HasWeakCoordinateDerivatives u g → ContDiff ℝ 1 F →
  (∃ C : ℝ≥0, ∀ t, ‖deriv F t‖ ≤ C) →
  MemLp (fun x => F (u x)) p (volume.restrict (Ω : Set (Domain d))) →
  ∃ (w : DomainLp ℝ Ω p) (k : Fin d → DomainLp ℝ Ω p),
    HasWeakCoordinateDerivatives w k ∧
    w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => F (u x)) ∧
    ∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => deriv F (u x) * g i x)

def ChainZeroCondition : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p) (F : ℝ → ℝ),
  ContDiff ℝ 1 F → (∃ C : ℝ≥0, ∀ t, ‖deriv F t‖ ≤ C) → F 0 = 0 →
  MemLp (fun x => F (u x)) p (volume.restrict (Ω : Set (Domain d)))

/-- Each level has zero gradient almost everywhere; the exceptional null set
may depend on the level. -/
def LevelSetRule : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p)
    (g : Fin d → DomainLp ℝ Ω p), HasWeakCoordinateDerivatives u g →
  ∀ (c : ℝ) (i : Fin d), ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)),
    u x = c → g i x = 0

def AbsoluteValueRule : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p)
    (g : Fin d → DomainLp ℝ Ω p), HasWeakCoordinateDerivatives u g →
  ∃ (w : DomainLp ℝ Ω p) (k : Fin d → DomainLp ℝ Ω p),
    HasWeakCoordinateDerivatives w k ∧
    w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => |u x|) ∧
    ∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => if 0 < u x then g i x else if u x < 0 then -g i x else 0)

def PositivePartRule : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p)
    (g : Fin d → DomainLp ℝ Ω p), HasWeakCoordinateDerivatives u g →
  ∃ (w : DomainLp ℝ Ω p) (k : Fin d → DomainLp ℝ Ω p),
    HasWeakCoordinateDerivatives w k ∧
    w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => max 0 (u x)) ∧
    ∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => if 0 < u x then g i x else 0)

/-- Clipping to any interval for which the clipped function is in Lp; this
includes the usual symmetric truncations and has zero derivative at BOTH levels. -/
def TruncationRule : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p)
    (g : Fin d → DomainLp ℝ Ω p) (a b : ℝ), a ≤ b →
  HasWeakCoordinateDerivatives u g →
  MemLp (fun x => max a (min b (u x))) p (volume.restrict (Ω : Set (Domain d))) →
  ∃ (w : DomainLp ℝ Ω p) (k : Fin d → DomainLp ℝ Ω p),
    HasWeakCoordinateDerivatives w k ∧
    w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => max a (min b (u x))) ∧
    ∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => if a < u x ∧ u x < b then g i x else 0)

def TruncationZeroCondition : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p) (a b : ℝ),
  a ≤ 0 → 0 ≤ b →
  MemLp (fun x => max a (min b (u x))) p (volume.restrict (Ω : Set (Domain d)))
/-- An explicit bridge to the canonical W^{1,p} graph, valid also for d=0. -/
def FirstOrderGraphBridge : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p),
  (∃ v : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p,
      v.val (zeroIndex d 1) = u) ↔
    ∃ g : Fin d → DomainLp 𝕜 Ω p, HasWeakCoordinateDerivatives u g

def NegativePartRule : Prop := ∀ (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp ℝ Ω p)
    (g : Fin d → DomainLp ℝ Ω p), HasWeakCoordinateDerivatives u g →
  ∃ (w : DomainLp ℝ Ω p) (k : Fin d → DomainLp ℝ Ω p),
    HasWeakCoordinateDerivatives w k ∧
    w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => max 0 (-u x)) ∧
    ∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => if u x < 0 then -g i x else 0)
end Specs.ExpandedFA.Sobolev.SobolevProductAndChainRules
