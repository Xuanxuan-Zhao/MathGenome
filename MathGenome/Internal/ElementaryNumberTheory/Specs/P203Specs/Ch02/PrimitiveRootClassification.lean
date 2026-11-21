import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.MultiplicativeCyclicity

/-! Independent statements for the classification and count in Theorem 2.5,
paper.tex:550–601. The unique decomposition at powers of two is allocated to
the separate TwoPowerUnits goal. Moduli here are positive, and primitive-root
classes are residue classes that underlie generating units, also at modulus one.
-/

namespace P203Specs.Ch02

/-- A primitive-root class is the underlying residue class of a generating unit. -/
def IsPrimitiveRootClass (m : ℕ) (x : ZMod m) : Prop :=
  ∃ g : ResidueUnits m, (g : ZMod m) = x ∧ Subgroup.zpowers g = ⊤

/-- An integer is a primitive root when its residue class is a generator. -/
def IsPrimitiveRootMod (m : ℕ) (a : ℤ) : Prop :=
  IsPrimitiveRootClass m (a : ZMod m)

def PrimitiveRootClassification : Prop :=
  ∀ m : ℕ, 0 < m →
    (IsCyclic (ResidueUnits m) ↔ m = 1 ∨ m = 2 ∨ m = 4 ∨
      ∃ p k : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ k ∧ (m = p ^ k ∨ m = 2 * p ^ k))

/-- The count is of classes, rather than of their infinitely many integer representatives. -/
def PrimitiveRootCount : Prop :=
  ∀ m : ℕ, 0 < m → IsCyclic (ResidueUnits m) →
    Nat.card {x : ZMod m // IsPrimitiveRootClass m x} = totient (totient m)

/-- Every residue class has an integer representative, with the same
primitive-root predicate. This includes the sole class at modulus one. -/
def PrimitiveRootRepresentatives : Prop :=
  ∀ m : ℕ, 0 < m → ∀ x : ZMod m,
    ∃ a : ℤ, (a : ZMod m) = x ∧
      (IsPrimitiveRootMod m a ↔ IsPrimitiveRootClass m x)

end P203Specs.Ch02
