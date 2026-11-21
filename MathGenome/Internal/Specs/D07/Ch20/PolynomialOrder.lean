import MathGenome.Internal.Specs.D07.Ch20.PolynomialOrderRepeatedFactorOrder
import Mathlib.Algebra.Field.ZMod

/-! Independent specification of K07.20.polynomial_order (paper.tex:6084–6107).
`orderOf` of the canonical residue is polynomial order; the assertions below
prove its positivity and least-exponent characterization on the stated domain. -/
universe u v
namespace Specs.D07.Ch20.PolynomialOrder
open Polynomial

abbrev OrderFunctionType := (F : Type u) → [Field F] → F[X] → ℕ

noncomputable def orderValue : OrderFunctionType.{u} :=
  fun _F _ f => orderOf (AdjoinRoot.root f)

/-- This numerical order is the order in the unit group of the finite quotient. -/
def QuotientUnitOrder : Prop :=
  ∀ (F : Type u) [Field F] (f : F[X]), f.eval 0 ≠ 0 →
    ∃ a : (AdjoinRoot f)ˣ,
      (a : AdjoinRoot f) = AdjoinRoot.root f ∧ orderValue F f = orderOf a

def OrderExists : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (f : F[X]),
    0 < f.natDegree → f.eval 0 ≠ 0 →
    IsLeast {h : ℕ | 0 < h ∧ f ∣ X ^ h - 1} (orderValue F f)

def OrderDivisibility : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (f : F[X]),
    0 < f.natDegree → f.eval 0 ≠ 0 →
    ∀ h : ℕ, f ∣ X ^ h - 1 ↔ orderValue F f ∣ h

def RootOrder : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (g : F[X]),
    Irreducible g → 0 < g.natDegree → g.eval 0 ≠ 0 →
    ∀ (L : Type v) [Field L] [Algebra F L] (a : L),
      aeval a g = 0 → orderValue F g = orderOf a

/-- The q^degree - 1 divisibility asserted in the proof for irreducibles. -/
def IrreducibleOrderBound : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (g : F[X]),
    Irreducible g → g.eval 0 ≠ 0 →
    orderValue F g ∣ Nat.card F ^ g.natDegree - 1

/-- All factorization hypotheses, including the nonzero scalar, are retained.
The least bound on all multiplicities is the bound on their maximum. -/
def RepeatedFactorOrder : Prop :=
  ∀ (F : Type u) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (ι : Type v) [Fintype ι] [Nonempty ι]
    (g : ι → F[X]) (b : ι → ℕ) (c : F) (f : F[X]),
    (∀ i, (g i).Monic) → (∀ i, Irreducible (g i)) → Function.Injective g →
    (∀ i, 0 < b i) → c ≠ 0 → 0 < f.natDegree → f.eval 0 ≠ 0 →
    f = C c * ∏ i, g i ^ b i →
    (∀ i, Nat.Coprime (orderValue F (g i)) p) ∧
    (∃ t : ℕ, IsLeast {u : ℕ | ∀ i, b i ≤ p ^ u} t) ∧
    ∀ t : ℕ, (∀ i, b i ≤ p ^ t) →
      (∀ u : ℕ, (∀ i, b i ≤ p ^ u) → t ≤ u) →
      let e := Finset.univ.lcm (fun i => orderValue F (g i))
      orderValue F f = e * p ^ t ∧
      IsLeast {h : ℕ | 0 < h ∧ f ∣ X ^ h - 1} (e * p ^ t)

/-- The example rules out extending the irreducible order bound to all f. -/
def BinaryExample : Prop :=
  let g : (ZMod 2)[X] := X ^ 2 + X + 1
  orderValue (ZMod 2) g = 3 ∧
  orderValue (ZMod 2) (g ^ 3) = 12 ∧
  (g ^ 3).natDegree = 6 ∧
  (g ^ 3).eval 0 ≠ 0 ∧
  ¬orderValue (ZMod 2) (g ^ 3) ∣ 2 ^ (g ^ 3).natDegree - 1 ∧
  IsLeast {u : ℕ | 3 ≤ 2 ^ u} 2
end Specs.D07.Ch20.PolynomialOrder
