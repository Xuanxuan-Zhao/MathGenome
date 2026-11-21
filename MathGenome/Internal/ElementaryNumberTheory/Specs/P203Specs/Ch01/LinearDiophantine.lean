import Mathlib.Data.Int.GCD
import Mathlib.Data.Fin.Basic

/-!
Theorem 1.4 (`nt:A03`), paper.tex:197–229. Integers, nonnegative gcds,
and congruences `m ∣ a*x-b` use the conventions of paper.tex:77–85.
The last specification expresses an exact class count by an enumeration:
there are gcd(a,m) representatives, pairwise incongruent, covering every root.
-/
namespace P203Specs.Ch01

def LinearSolvability : Prop :=
  ∀ a b c : ℤ, (∃ x y : ℤ, a*x+b*y=c) ↔ (Int.gcd a b : ℤ) ∣ c

def LinearSolutions : Prop :=
  ∀ a b c x₀ y₀ : ℤ, 0 < (Int.gcd a b : ℤ) → a*x₀+b*y₀=c →
    ∀ x y : ℤ, a*x+b*y=c ↔
      ∃ t : ℤ, x=x₀+(b/(Int.gcd a b : ℤ))*t ∧
        y=y₀-(a/(Int.gcd a b : ℤ))*t

def ZeroLinearEquation : Prop :=
  ∀ a b : ℤ, Int.gcd a b = 0 →
    a=0 ∧ b=0 ∧ ∀ c x y : ℤ, (a*x+b*y=c ↔ c=0)

def CongruenceSolvability : Prop :=
  ∀ a b m : ℤ, 0 < m →
    ((∃ x : ℤ, m ∣ a*x-b) ↔ (Int.gcd a m : ℤ) ∣ b)

def CongruenceSolutions : Prop :=
  ∀ a b m x₀ : ℤ, 0 < m → m ∣ a*x₀-b →
    ∀ x : ℤ, (m ∣ a*x-b) ↔
      ∃ t : ℤ, x=x₀+(m/(Int.gcd a m : ℤ))*t

/-- An exact enumeration of the solution classes modulo the positive integer m.
The second clause is pairwise distinctness modulo m; the third is exhaustion.
This also applies to m=1 and a=0. -/
def CongruenceClassCount : Prop :=
  ∀ a b m : ℤ, 0 < m → (∃ x : ℤ, m ∣ a*x-b) →
    ∃ reps : Fin (Int.gcd a m) → ℤ,
      (∀ i, m ∣ a*reps i-b) ∧
      (∀ i j, (m ∣ reps i-reps j) ↔ i=j) ∧
      (∀ x : ℤ, m ∣ a*x-b → ∃ i, m ∣ x-reps i)

end P203Specs.Ch01
