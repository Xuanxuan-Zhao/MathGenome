import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
Independent specification of K07.07.torsion_count_invariants
(paper.tex:3430–3441). A list, including the empty list, indexes the full
finite Cartesian product. Scalar multiplication is natural repeated addition.
The positivity hypotheses exclude invisible trivial cyclic factors from recovery.
-/
namespace Specs.D07.Ch07.TorsionCountInvariants

/-- The source's product of cyclic groups of orders `p ^ eᵢ`. -/
abbrev PrimePowerProduct (p : ℕ) (e : List ℕ) :=
  (i : Fin e.length) → ZMod (p ^ e.get i)

/-- The subgroup `A[p^k]`, with its actual annihilation condition. -/
def torsionSubgroup (A : Type*) [AddCommGroup A] (p k : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (p ^ k) : A →+ A).ker

/-- The integer exponent `s_k` in the cardinality formula. -/
def torsionExponent (e : List ℕ) (k : ℕ) : ℕ :=
  (e.map fun n => min k n).sum

def TorsionCardinality : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (e : List ℕ), (∀ n ∈ e, 0 < n) → ∀ k : ℕ,
    Nat.card (torsionSubgroup (PrimePowerProduct p e) p k) =
      p ^ torsionExponent e k

def SuccessiveDifference : Prop :=
  ∀ (e : List ℕ), (∀ n ∈ e, 0 < n) → ∀ k : ℕ, 1 ≤ k →
    torsionExponent e k - torsionExponent e (k - 1) =
      (e.filter fun n => k ≤ n).length

/-- Differences of consecutive tail counts give each positive multiplicity. -/
def ExponentMultiplicity : Prop :=
  ∀ (e : List ℕ), (∀ n ∈ e, 0 < n) → ∀ k : ℕ, 1 ≤ k →
    e.count k = (torsionExponent e k - torsionExponent e (k - 1)) -
      (torsionExponent e (k + 1) - torsionExponent e k)

/-- Equality of all the intrinsic counts determines the exponent multiset.
`List.Perm` is equality of multisets, allowing different list lengths. -/
def CountsRecoverExponents : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (e f : List ℕ),
    (∀ n ∈ e, 0 < n) → (∀ n ∈ f, 0 < n) →
    (∀ k : ℕ,
      Nat.card (torsionSubgroup (PrimePowerProduct p e) p k) =
      Nat.card (torsionSubgroup (PrimePowerProduct p f) p k)) →
    e.Perm f

def BoundaryCounts : Prop :=
  ∀ (p : ℕ), p.Prime →
    (∀ (e : List ℕ), (∀ n ∈ e, 0 < n) →
      Nat.card (torsionSubgroup (PrimePowerProduct p e) p 0) = 1) ∧
    (∀ k : ℕ, Nat.card (torsionSubgroup (PrimePowerProduct p []) p k) = 1)

end Specs.D07.Ch07.TorsionCountInvariants
