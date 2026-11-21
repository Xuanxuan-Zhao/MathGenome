import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.TwoSquaresCriterion
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic

/-! The two-square recognition step of the proof of Theorem 4.10 (`nt:D06`),
`paper.tex`, lines 1969–1994. All square witnesses and lattice coordinates are
integers. The positive squarefree integer and rational primes are represented
by naturals. Nonzero square residue means a nonzero square in the residue field.
No assumptions from the auxiliary-prime construction or lattice existence are
added to the recognition data. -/
namespace P203Specs.Ch04

def ThreeSquaresRecognition : Prop :=
  ∀ (n ℓ q : ℕ), 1 < n → Squarefree n → (ℓ = 0 ∨ ℓ = 1) →
    q.Prime → Odd q → n < q →
    let b₀ := 2 ^ ℓ * q
    Nat.Coprime b₀ n →
    (∀ p : ℕ, p.Prime → Odd p → p ∣ n →
      IsSquare (-(b₀ : ℤ) : ZMod p) ∧ (-(b₀ : ℤ) : ZMod p) ≠ 0) →
    ∀ X W s S : ℤ, 0 ≤ S → S ≤ (n : ℤ) →
      X ^ 2 + S = (n : ℤ) →
      (b₀ : ℤ) * S = W ^ 2 + (n : ℤ) * s ^ 2 →
      ∃ a b : ℤ, S = a ^ 2 + b ^ 2

end P203Specs.Ch04
