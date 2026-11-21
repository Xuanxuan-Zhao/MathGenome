import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.GCDMonoid.Finset

/-! Independent specification for the repeated-factor assertion of
K07.20.polynomial_order, paper.tex:6084–6105.  The residue of X in the
canonical quotient is used to express polynomial order.  The implementation
also proves that this is the least positive divisibility exponent. -/

universe u v
namespace Specs.D07.Ch20.PolynomialOrderRepeatedFactorOrder
open Polynomial

/-- Frobenius preserves the full multiplicity p^u, not just the root set. -/
def FrobeniusMultiplicity : Prop :=
  ∀ (F : Type u) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (u v : ℕ),
    (X ^ (p ^ u * v) - 1 : F[X]) = (X ^ v - 1) ^ (p ^ u)

/-- A chosen root in any extension has the same order as the canonical root. -/
def RootOrder : Prop :=
  ∀ (F : Type u) [Field F] (g : F[X]), Irreducible g →
    ∀ (L : Type v) [Field L] [Algebra F L] (a : L), aeval a g = 0 →
      orderOf a = orderOf (AdjoinRoot.root g)

/-- The distinct irreducibles are indexed by an arbitrary finite nonempty
set. The bound on all b_j is equivalent to the bound on their maximum;
t is explicitly the least exponent with that bound. Scalar c is retained. -/
def RepeatedFactorOrder : Prop :=
  ∀ (F : Type u) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (ι : Type v) [Fintype ι] [Nonempty ι]
    (g : ι → F[X]) (b : ι → ℕ) (c : F) (f : F[X]),
    (∀ i, (g i).Monic) → (∀ i, Irreducible (g i)) → Function.Injective g →
    (∀ i, 0 < b i) → c ≠ 0 → 0 < f.natDegree → f.eval 0 ≠ 0 →
    f = C c * ∏ i, (g i) ^ b i →
    (∀ i, Nat.Coprime (orderOf (AdjoinRoot.root (g i))) p) ∧
    (∃ t : ℕ, IsLeast {u : ℕ | ∀ i, b i ≤ p ^ u} t) ∧
    ∀ t : ℕ, (∀ i, b i ≤ p ^ t) →
      (∀ u : ℕ, (∀ i, b i ≤ p ^ u) → t ≤ u) →
      let e := Finset.univ.lcm (fun i => orderOf (AdjoinRoot.root (g i)))
      orderOf (AdjoinRoot.root f) = e * p ^ t ∧
      IsLeast {h : ℕ | 0 < h ∧ f ∣ X ^ h - 1} (e * p ^ t)

/-- Exact multiplicity criterion for a positive exponent written p^u v,
with v prime to p. This includes both absence and repeated-factor bounds. -/
def DivisibilityMultiplicity : Prop :=
  ∀ (F : Type u) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (ι : Type v) [Fintype ι]
    (g : ι → F[X]) (b : ι → ℕ) (c : F),
    (∀ i, (g i).Monic) → (∀ i, Irreducible (g i)) → Function.Injective g →
    (∀ i, 0 < b i) → c ≠ 0 →
    ∀ (u v : ℕ) (_hv : ¬p ∣ v),
      (C c * ∏ i, (g i) ^ b i ∣ (X ^ (p ^ u * v) - 1 : F[X])) ↔
      ∀ i, orderOf (AdjoinRoot.root (g i)) ∣ v ∧ b i ≤ p ^ u

end Specs.D07.Ch20.PolynomialOrderRepeatedFactorOrder
