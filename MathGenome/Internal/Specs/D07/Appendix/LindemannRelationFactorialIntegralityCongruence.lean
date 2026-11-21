import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Prime.Defs

/-! Arithmetic part of `lem:lindemann-special-relation`, paper.tex:7700–7736.
The finite family includes repetitions and may be empty. All derivatives are
formal polynomial derivatives. No exponential relation is assumed here. -/

noncomputable section
namespace Specs.D07.Appendix.LindemannRelationFactorialIntegralityCongruence
open Polynomial

/-- The integer auxiliary polynomial before substitution and normalization. -/
def H (Q : ℤ[X]) (p : ℕ) : ℤ[X] := X ^ (p - 1) * Q ^ p

/-- The exact upper derivative index used in the paper. -/
def N (m p : ℕ) : ℕ := (m + 1) * p - 1

/-- Normalized polynomial after the positive integer change of variable. -/
def f (a : ℤ) (Q : ℤ[X]) (p : ℕ) : ℂ[X] :=
  C ((Nat.factorial (p - 1) : ℂ)⁻¹) *
    ((H Q p).map (Int.castRingHom ℂ)).comp (C (a : ℂ) * X)

/-- Finite sum of all the derivatives up to the degree. -/
def F (a : ℤ) (Q : ℤ[X]) (m p : ℕ) : ℂ[X] :=
  ∑ r ∈ Finset.range (N m p + 1), derivative^[r] (f a Q p)

/-- The integer whose size is compared with the later analytic estimate. -/
def J {m : ℕ} (β : Fin m → ℂ) (k a : ℤ) (Q : ℤ[X]) (p : ℕ) : ℂ :=
  (k : ℂ) * (F a Q m p).eval 0 + ∑ j, (F a Q m p).eval (β j)

/-- Every derivative of an integer polynomial is factorial times a single
integer polynomial, and r!/(p-1)! is divisible by p at r ≥ p. -/
def FactorialDerivatives : Prop :=
  (∀ (P : ℤ[X]) (r : ℕ),
    derivative^[r] P = C (Nat.factorial r : ℤ) * hasseDeriv r P) ∧
  (∀ p r : ℕ, 0 < p → p ≤ r →
    ∃ t : ℕ, Nat.factorial r = p * Nat.factorial (p - 1) * t)

/-- The repeated chain rule, including the factorial normalization. -/
def DerivativeSubstitution : Prop :=
  ∀ (a : ℤ) (Q : ℤ[X]) (p r : ℕ) (z : ℂ),
    (derivative^[r] (f a Q p)).eval z =
      (a : ℂ) ^ r / (Nat.factorial (p - 1) : ℂ) *
        (derivative^[r] (H Q p)).eval₂ (Int.castRingHom ℂ) ((a : ℂ) * z)

/-- Multiplicities, low-order vanishing, the first nonzero derivative at zero,
and the same integer polynomial witness for every root (indeed every z). -/
def DerivativeArithmetic : Prop :=
  ∀ (m : ℕ) (β : Fin m → ℂ) (a : ℤ) (Q : ℤ[X]) (p : ℕ),
    0 < a → Q.Monic → Q.coeff 0 ≠ 0 → Nat.Prime p →
    Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j)) →
    (H Q p).natDegree = N m p ∧
    (∀ j, (X - C ((a : ℂ) * β j)) ^ p ∣ (H Q p).map (Int.castRingHom ℂ)) ∧
    (∀ j, p ≤ ((H Q p).map (Int.castRingHom ℂ)).rootMultiplicity ((a : ℂ) * β j)) ∧
    (∀ r, r < p - 1 → (derivative^[r] (f a Q p)).eval 0 = 0) ∧
    (derivative^[p - 1] (f a Q p)).eval 0 =
      ((a ^ (p - 1) * Q.coeff 0 ^ p : ℤ) : ℂ) ∧
    (∀ j r, r < p → (derivative^[r] (f a Q p)).eval (β j) = 0) ∧
    (∀ r, p ≤ r → ∃ A : ℤ[X], ∀ z : ℂ,
      (derivative^[r] (f a Q p)).eval z =
        (p : ℂ) * A.eval₂ (Int.castRingHom ℂ) ((a : ℂ) * z))

/-- Both congruences retain their integer witnesses. The final witness is
nonzero modulo p, nonzero as an integer, and has complex norm at least one. -/
def IntegralityCongruences : Prop :=
  ∀ (m : ℕ) (β : Fin m → ℂ) (k a : ℤ) (Q : ℤ[X]) (p : ℕ),
    0 < k → 0 < a → Q.Monic → Q.coeff 0 ≠ 0 → Nat.Prime p →
    ¬ (p : ℤ) ∣ k * a * Q.coeff 0 →
    Q.map (Int.castRingHom ℂ) = ∏ j, (X - C ((a : ℂ) * β j)) →
    (∃ u : ℤ, (F a Q m p).eval 0 = (u : ℂ) ∧
      (p : ℤ) ∣ u - a ^ (p - 1) * Q.coeff 0 ^ p) ∧
    (∃ v : ℤ, ∑ j, (F a Q m p).eval (β j) = ((p : ℤ) * v : ℤ)) ∧
    (∃ w : ℤ, J β k a Q p = (w : ℂ) ∧
      (p : ℤ) ∣ w - k * a ^ (p - 1) * Q.coeff 0 ^ p ∧
      ¬ (p : ℤ) ∣ w ∧ w ≠ 0 ∧ 1 ≤ ‖J β k a Q p‖)

end Specs.D07.Appendix.LindemannRelationFactorialIntegralityCongruence
