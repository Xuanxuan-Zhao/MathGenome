import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.TotientClassicalCongruences

/-! Independent statements for the two-power decomposition in paper.tex:550–580.
Natural exponents with `k ≥ 3` represent precisely the source's integer exponents.
The finite types impose the source's bounds on both parameters. -/
namespace P203Specs.Ch02

/-- The source's expression, in the ordinary residue ring. -/
def twoPowerExpression (k a b : ℕ) : ZMod (2 ^ k) := (-1) ^ a * 5 ^ b

/-- The order of five, including modulus eight. -/
def TwoPowerFiveOrder : Prop :=
  ∀ k : ℕ, 3 ≤ k → orderOf (5 : ZMod (2 ^ k)) = 2 ^ (k - 2)

/-- Every residue unit has exactly one pair of bounded exponents. -/
def TwoPowerUniqueRepresentation : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ u : ResidueUnits (2 ^ k),
    ∃! p : Fin 2 × Fin (2 ^ (k - 2)),
      twoPowerExpression k p.1.val p.2.val = (u : ZMod (2 ^ k))

/-- The powers of five exhaust exactly the residue classes that are one
modulo four. Under `k ≥ 3`, `ZMod.cast` here is ordinary reduction modulo four. -/
def TwoPowerFiveExhaustion : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ x : ZMod (2 ^ k),
    (ZMod.cast x : ZMod 4) = 1 ↔
      ∃ b : Fin (2 ^ (k - 2)), x = 5 ^ b.val

end P203Specs.Ch02
