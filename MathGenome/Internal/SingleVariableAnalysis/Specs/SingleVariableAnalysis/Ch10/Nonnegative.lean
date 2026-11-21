import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint

/-! Independent statements of K03.10.nonnegative, paper.tex:2958–2972.
The right endpoint is a finite real or +∞. All partial values are the proper
Darboux truncations of the shared one-endpoint interface. Nonnegativity is
required on [a,b), including the regular endpoint a. Boundedness concerns the
entire range of partial values, and convergence means a finite real limit.
-/
namespace Specs.SingleVariableAnalysis.Ch10.Nonnegative
open OneEndpoint

def rightNonnegativeMonotone : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
    (h : rightRegularValue .real f a b),
    (∀ x : ℝ, a ≤ x → (x : WithTop ℝ) < b → 0 ≤ f x) →
    ∀ u v : rightIndexValue a b, u.val ≤ v.val →
      (show ℝ from rightTruncationValue .real f a b h u) ≤
        (show ℝ from rightTruncationValue .real f a b h v)

def rightNonnegativeConvergesIffBounded : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
    (h : rightRegularValue .real f a b),
    (∀ x : ℝ, a ≤ x → (x : WithTop ℝ) < b → 0 ≤ f x) →
    (rightConvergesValue .real f a b ↔
      BddAbove (Set.range (fun t => (show ℝ from rightTruncationValue .real f a b h t))))

def rightNonnegativeHasIntegralSupremum : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
    (h : rightRegularValue .real f a b),
    (∀ x : ℝ, a ≤ x → (x : WithTop ℝ) < b → 0 ≤ f x) →
    BddAbove (Set.range (fun t => (show ℝ from rightTruncationValue .real f a b h t))) →
    rightHasIntegralValue .real f a b
      (sSup (α := ℝ) (Set.range (fun t => (show ℝ from rightTruncationValue .real f a b h t))))

def rightNonnegativeDivergesOfUnbounded : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
    (h : rightRegularValue .real f a b),
    (∀ x : ℝ, a ≤ x → (x : WithTop ℝ) < b → 0 ≤ f x) →
    ¬ BddAbove (Set.range (fun t => (show ℝ from rightTruncationValue .real f a b h t))) →
    rightDivergesPosValue f a b

def rightNonnegativeDivergesOfNotConverges : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
    (h : rightRegularValue .real f a b),
    (∀ x : ℝ, a ≤ x → (x : WithTop ℝ) < b → 0 ≤ f x) →
    ¬ rightConvergesValue .real f a b → rightDivergesPosValue f a b

end Specs.SingleVariableAnalysis.Ch10.Nonnegative
