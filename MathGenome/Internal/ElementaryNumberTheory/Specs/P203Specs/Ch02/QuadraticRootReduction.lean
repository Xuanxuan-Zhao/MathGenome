import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.FactorizationValuations
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic

/-!
Singular and valuation branches of Theorem `nt:B09`, paper.tex:794–838.
`Fin m` is the usual complete system of representatives `0 ≤ x < m` for
integer residue classes. Congruence is integer divisibility, also for negative
`a`. All valuations reuse the extended valuation from Chapter 1.
-/
namespace P203Specs.Ch02
open P203Specs.Ch01

/-- Roots represented once each in the standard interval of residues. -/
def QuadraticRoots (m : ℕ) (a : ℤ) :=
  {x : Fin m // (m : ℤ) ∣ (x.val : ℤ) ^ 2 - a}

noncomputable def quadraticRootCount (m : ℕ) (a : ℤ) : ℕ :=
  Nat.card (QuadraticRoots m a)

/-- Identifies the bounded representative model with the ordinary residue ring,
including its count. -/
def QuadraticRootsResidueBridge : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (a : ℤ),
    (∃ e : QuadraticRoots m a ≃ {x : ZMod m // x^2 = (a : ZMod m)},
      ∀ x, (e x).val = (x.val.val : ZMod m)) ∧
    quadraticRootCount m a = Nat.card {x : ZMod m // x^2 = (a : ZMod m)}

/-- Includes the zero integer representative. `(k+1)/2` is `ceil(k/2)`. -/
def ZeroResidueRoots : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (k : ℕ), 1 ≤ k → ∀ (a : ℤ), (p : ℤ)^k ∣ a →
    (∀ x : ℤ, (p : ℤ)^k ∣ x^2 - a ↔ (p : ℤ)^((k+1)/2) ∣ x) ∧
    quadraticRootCount (p^k) a = p^(k/2)

/-- The finite valuation is below the modulus exponent and independent of
any integer representative of the same nonzero residue class. -/
def NonzeroResidueValuation : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (k : ℕ), 1 ≤ k → ∀ (a : ℤ), ¬(p : ℤ)^k ∣ a →
    a ≠ 0 ∧ ∃ s : ℕ, primeValuation p a = (s : ℕ∞) ∧ s < k ∧
      ∀ b : ℤ, (p : ℤ)^k ∣ b-a → primeValuation p b = (s : ℕ∞)

def OddValuationNoRoots : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (k s : ℕ) (a : ℤ),
    primeValuation p a = (s : ℕ∞) → s < k → Odd s →
    (∀ x : ℤ, ¬(p : ℤ)^k ∣ x^2-a) ∧ quadraticRootCount (p^k) a = 0

/-- The explicit equivalence records both division of the congruence and
exactly `p^t` distinct lifts of every reduced root. Its first coordinate is
`y mod p^j`, its second coordinate selects the lift modulo `p^(k-t)`.
No sign condition on `a` is imposed, and `t=0` is included. -/
def EvenValuationReduction : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (k t : ℕ) (a : ℤ),
    primeValuation p a = ((2*t : ℕ) : ℕ∞) → 2*t < k →
    let j := k-2*t
    let a' := a / (p : ℤ)^(2*t)
    1 ≤ j ∧ a = (p : ℤ)^(2*t)*a' ∧ ¬(p : ℤ) ∣ a' ∧
    (∀ x : ℤ, (p : ℤ)^k ∣ x^2-a ↔
      ∃ y : ℤ, x = (p : ℤ)^t*y ∧ (p : ℤ)^j ∣ y^2-a') ∧
    (∃ e : (QuadraticRoots (p^j) a' × Fin (p^t)) ≃ QuadraticRoots (p^k) a,
      ∀ z, ((e z).val.val : ℕ) = p^t * (z.1.val.val + p^j*z.2.val)) ∧
    quadraticRootCount (p^k) a = p^t * quadraticRootCount (p^j) a'

end P203Specs.Ch02
