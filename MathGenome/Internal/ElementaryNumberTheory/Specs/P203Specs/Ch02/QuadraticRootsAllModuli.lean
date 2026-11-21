import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.QuadraticRootReduction
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.QuadraticUnitRoots

/-! The complete count and CRT conclusion of Theorem nt:B09,
paper.tex:792–857. The prime index is exactly the finite set of primes
dividing the positive modulus; exponents are its ordinary factorization.
The root and valuation models are the canonical upstream definitions. -/
namespace P203Specs.Ch02
open P203Specs.Ch01
open scoped BigOperators

/-- The unit contribution at positive exponent `j`. The three powers-of-two
ranges are separate, and the odd-prime branch uses the Legendre symbol. -/
noncomputable def unitRootFactor (p j : ℕ) (b : ℤ) : ℕ :=
  if p = 2 then
    if j = 1 then 1
    else if j = 2 then (if b ≡ 1 [ZMOD 4] then 2 else 0)
    else (if b ≡ 1 [ZMOD 8] then 4 else 0)
  else if legendreSymbol b p = 1 then 2 else 0

/-- The explicit local factor, including singular and zero residues.
The valuation is inspected only after excluding the zero residue, so it
is finite even when the integer parameter is zero in other branches.
In the even branch `s=2t`, `s/2=t` and `k-s=k-2t`. -/
noncomputable def primePowerRootFactor (p k : ℕ) (a : ℤ) : ℕ :=
  if (p : ℤ)^k ∣ a then p^(k/2)
  else
    let s := (primeValuation p a).toNat
    if Odd s then 0
    else p^(s/2) * unitRootFactor p (k-s) (a / (p : ℤ)^s)

/-- The CRT bijection is the natural reduction in every coordinate.
No coprimality condition is imposed on `a` and `m`. -/
def QuadraticRootsCRT : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (a : ℤ),
    ∃ e : UnitQuadratic.QuadraticRoots m a ≃
        ((p : m.primeFactors) →
          UnitQuadratic.QuadraticRoots ((p : ℕ)^m.factorization p) a),
      ∀ x p, (e x p).val =
        ZMod.castHom (Nat.ordProj_dvd m p) (ZMod ((p : ℕ)^m.factorization p)) x.val

/-- The bounded-representative root count is the product of all local counts. -/
def QuadraticRootCountProduct : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (a : ℤ),
    quadraticRootCount m a =
      ∏ p : m.primeFactors, quadraticRootCount ((p : ℕ)^m.factorization p) a

def PrimePowerRootCountExplicit : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (k : ℕ), 1 ≤ k → ∀ (a : ℤ),
    quadraticRootCount (p^k) a = primePowerRootFactor p k a

/-- The full formula for every integer and every positive modulus. -/
def QuadraticRootCountExplicit : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (a : ℤ),
    quadraticRootCount m a =
      ∏ p : m.primeFactors, primePowerRootFactor p (m.factorization p) a

/-- The unique class modulo one is a root for every right hand side,
and the corresponding prime-factor product is empty. -/
def QuadraticRootsModulusOne : Prop :=
  ∀ a : ℤ, quadraticRootCount 1 a = 1 ∧
    (∃! x : ZMod 1, x^2 = (a : ZMod 1)) ∧
    (∏ p : Nat.primeFactors 1, primePowerRootFactor p (Nat.factorization 1 p) a) = 1

end P203Specs.Ch02
