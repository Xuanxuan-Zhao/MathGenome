import MathGenome.Internal.Specs.D07.Ch13.PrimitivePolynomials
import MathGenome.Internal.Specs.D07.Ch13.MultiplicativeCyclic
import MathGenome.Internal.Specs.D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible
import Mathlib.Data.Rat.Defs

/-! Independent statements for K07.20.primitive_count, paper.tex:6102–6122.
The extension L has the specified embedding of K and exactly q^n elements.
The predicate is the shared multiplicative one, including monicity, degree,
irreducibility, and a root generating Lˣ. Counts are actual finite cardinalities.
The rational quotient and its integer product identity express exact division.
-/
universe u v
namespace Specs.D07.Ch20.PrimitiveCount
open Polynomial
open Specs.D07.Ch13.PrimitivePolynomials

def PrimitivePolynomialsFinite : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [Finite L] (n : ℕ), 0 < n → Nat.card L = Nat.card K ^ n →
    Finite {f : K[X] // primitivePredicateValue K L n f}

def PrimitiveCountProduct : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [Finite L] (n : ℕ), 0 < n → Nat.card L = Nat.card K ^ n →
    n * Nat.card {f : K[X] // primitivePredicateValue K L n f} =
      Nat.totient (Nat.card K ^ n - 1)

def PrimitiveCount : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [Finite L] (n : ℕ), 0 < n → Nat.card L = Nat.card K ^ n →
    (Nat.card {f : K[X] // primitivePredicateValue K L n f} : ℚ) =
      (Nat.totient (Nat.card K ^ n - 1) : ℚ) / (n : ℚ)

def OrderCriterion : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [Finite L] (n : ℕ) (f : K[X]),
    0 < n → Nat.card L = Nat.card K ^ n → f.Monic → f.natDegree = n →
    f.eval 0 ≠ 0 →
    (primitivePredicateValue K L n f ↔
      Specs.D07.Ch20.PolynomialOrder.orderValue K f = Nat.card K ^ n - 1)

def MaximalOrderForcesIrreducible : Prop :=
  Specs.D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible.MaximalOrderForcesIrreducible.{u,v}

end Specs.D07.Ch20.PrimitiveCount
