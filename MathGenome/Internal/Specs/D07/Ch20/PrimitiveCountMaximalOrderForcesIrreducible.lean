import MathGenome.Internal.Specs.D07.Ch20.PolynomialOrder

/-! The converse order test in K07.20.primitive_count, paper.tex:6102–6122.
The order is the canonical quotient order already specified upstream.
Every root is quantified in every compatible q^n-element extension field. -/
universe u v
namespace Specs.D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible
open Polynomial

def MaximalOrderForcesIrreducible : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (n : ℕ) (f : F[X]),
    0 < n → f.Monic → f.natDegree = n → f.eval 0 ≠ 0 →
    Specs.D07.Ch20.PolynomialOrder.orderValue F f = Nat.card F ^ n - 1 →
    Irreducible f ∧
      ∀ (L : Type v) [Field L] [Algebra F L] [Finite L],
        Nat.card L = Nat.card F ^ n →
        ∀ a : L, aeval a f = 0 →
          ∃ z : Lˣ, (z : L) = a ∧ Subgroup.zpowers z = ⊤

end Specs.D07.Ch20.PrimitiveCountMaximalOrderForcesIrreducible
