import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.TotientClassicalCongruences
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-! The primitive-root assertion of Theorem 2.4 (`nt:B03`), paper.tex:511–549.
The source's positive prime integer is represented by a natural prime and its
integer cast. A primitive root is an integer representative of a generator
of the actual residue unit group. The same integer is used at every level.
-/
namespace P203Specs.Ch02

/-- One integer simultaneously generates the units modulo every positive
power of the given odd prime. The unit witness identifies its underlying
residue with that integer, making invertibility at each level explicit. -/
def UniformPrimitiveRoot : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → ∃ g : ℤ, ∀ k : ℕ, 1 ≤ k →
    ∃ u : ResidueUnits (p ^ k),
      (u : ZMod (p ^ k)) = (g : ZMod (p ^ k)) ∧ Subgroup.zpowers u = ⊤

end P203Specs.Ch02
