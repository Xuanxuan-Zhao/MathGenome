import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.ZMod.Basic

/-! Independent specification of paper.tex:6061–6080.
The polynomial is the coefficient image of the integer cyclotomic polynomial.
`orderOf (q : ZMod m)` denotes modular multiplicative order; the separate
least-positive-exponent assertion makes this interpretation explicit.
A finite set of factors records distinctness, with an exact product equality.
The splitting field is a concrete intermediate field in the specified closure;
its finiteness, degree and cardinality identify F_(q^d) over the chosen base.
-/

universe u v
namespace Specs.D07.Ch20.CyclotomicFiniteFactors
open Polynomial

/-- The notation ord_m(q) has its usual least-positive-exponent meaning. -/
def ModularOrder : Prop :=
  ∀ (q m : ℕ), 1 < m → q.Coprime m →
    let d := orderOf (q : ZMod m)
    0 < d ∧ (q : ZMod m) ^ d = 1 ∧
      ∀ j : ℕ, 0 < j → (q : ZMod m) ^ j = 1 → d ≤ j

/-- All irreducible factors, with no repetitions or scalar unit omitted. -/
def Factorization : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (m : ℕ),
    1 < m → (Nat.card K).Coprime m →
    let d := orderOf (Nat.card K : ZMod m)
    (cyclotomic m ℤ).map (Int.castRingHom K) = cyclotomic m K ∧
    (cyclotomic m K).Separable ∧
    ∃ s : Finset (Polynomial K),
      s.card = m.totient / d ∧
      cyclotomic m K = ∏ P ∈ s, P ∧
      ∀ P ∈ s, P.Monic ∧ Irreducible P ∧ P.natDegree = d

/-- No coprimality or nonzero-characteristic assumption is added to the
source's element statement: coprimality is itself a conclusion. -/
def ElementDegree : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L] (a : Lˣ),
    1 < orderOf a →
    (Nat.card K).Coprime (orderOf a) ∧
    (minpoly K (a : L)).natDegree = orderOf (Nat.card K : ZMod (orderOf a)) ∧
    Module.finrank K (IntermediateField.adjoin K {(a : L)}) =
      orderOf (Nat.card K : ZMod (orderOf a))

/-- This identifies the actual splitting field inside the common closure,
including uniqueness among finite embedded fields of that cardinality. -/
def SplittingField : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [IsAlgClosed Ω] (m : ℕ),
    1 < m → (Nat.card K).Coprime m →
    let d := orderOf (Nat.card K : ZMod m)
    let E := IntermediateField.adjoin K ((cyclotomic m K).rootSet Ω)
    Finite E ∧ IsSplittingField K E (cyclotomic m K) ∧
    Module.finrank K E = d ∧ Nat.card E = Nat.card K ^ d ∧
    (∀ S : IntermediateField K Ω, Finite S → Nat.card S = Nat.card K ^ d → S = E)

def OrderOne : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (a : Lˣ),
    orderOf a = 1 → a = 1 ∧ minpoly K (a : L) = X - 1 ∧
      (minpoly K (a : L)).natDegree = 1 ∧
      Module.finrank K (IntermediateField.adjoin K {(a : L)}) = 1

def FirstCyclotomic : Prop :=
  ∀ (R : Type u) [CommRing R], cyclotomic 1 R = X - 1

def FifthCyclotomic : Prop :=
  ∀ (R : Type u) [CommRing R], cyclotomic 5 R = X ^ 4 + X ^ 3 + X ^ 2 + X + 1

def ModTwoExample : Prop :=
  orderOf (2 : ZMod 5) = 4 ∧ Irreducible (cyclotomic 5 (ZMod 2))

def ModFourExample : Prop :=
  orderOf (4 : ZMod 5) = 2 ∧
  ∀ (K : Type u) [Field K] [Finite K], Nat.card K = 4 →
    ∃ s : Finset (Polynomial K), s.card = 2 ∧
      cyclotomic 5 K = ∏ P ∈ s, P ∧
      ∀ P ∈ s, P.Monic ∧ Irreducible P ∧ P.natDegree = 2

def CharacteristicMultiplicity : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ),
    (X ^ (p * m) - 1 : Polynomial K) = (X ^ m - 1) ^ p

end Specs.D07.Ch20.CyclotomicFiniteFactors
