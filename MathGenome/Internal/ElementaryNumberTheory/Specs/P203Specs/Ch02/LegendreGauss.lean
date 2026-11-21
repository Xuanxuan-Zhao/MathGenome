import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! Source: paper.tex, conventions at 58–65 and 80–86; definition and Theorem 2.7
at 634–672. Numerators are arbitrary integers; denominators are odd natural primes.
These definitions and proposition types are independent of the implementation. -/
namespace P203Specs.Ch02

/-- The source's numerator-first symbol, using integer square congruences. -/
noncomputable def legendreSymbol (a : ℤ) (p : ℕ) : ℤ := by
  classical
  exact if (p : ℤ) ∣ a then 0 else
    if ∃ x : ℤ, x ^ 2 ≡ a [ZMOD (p : ℤ)] then 1 else -1

/-- The representative in `1,…,p`: the zero residue is represented by `p`. -/
def leastPositiveResidue (p : ℕ) (a : ℤ) : ℕ :=
  if (a : ZMod p).val = 0 then p else (a : ZMod p).val

/-- `2*r > p` is the exact integral version of `r > p/2` in the source. -/
def gaussCount (p : ℕ) (a : ℤ) : ℕ :=
  ((Finset.Icc 1 ((p - 1) / 2)).filter
    (fun i : ℕ => p < 2 * leastPositiveResidue p ((i : ℤ) * a))).card

def LegendreSymbolType : Type := ℤ → ℕ → ℤ
def LeastPositiveResidueType : Type := ℕ → ℤ → ℕ
def GaussCountType : Type := ℕ → ℤ → ℕ

def SymbolBridge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a : ℤ), legendreSymbol a p = legendreSym p a

def ResidueSpecification : Prop :=
  ∀ (p : ℕ), 0 < p → ∀ (a : ℤ),
    1 ≤ leastPositiveResidue p a ∧ leastPositiveResidue p a ≤ p ∧
      (leastPositiveResidue p a : ℤ) ≡ a [ZMOD (p : ℤ)]

def EulerCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (a : ℤ),
    a ^ ((p - 1) / 2) ≡ legendreSymbol a p [ZMOD (p : ℤ)]

def Multiplicativity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (a b : ℤ),
    legendreSymbol (a * b) p = legendreSymbol a p * legendreSymbol b p

/-- Explicit bridge to the finite residue count used by Mathlib's Gauss lemma. -/
def CountBridge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (a : ℤ), ¬(p : ℤ) ∣ a →
    gaussCount p a =
      ((Finset.Ico 1 (p / 2).succ).filter
        (fun i : ℕ => p / 2 < ((a : ZMod p) * (i : ZMod p)).val)).card

def GaussLemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (a : ℤ), ¬(p : ℤ) ∣ a →
    legendreSymbol a p = (-1 : ℤ) ^ gaussCount p a

end P203Specs.Ch02
