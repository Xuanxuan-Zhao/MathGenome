import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD

/-!
The general (possibly non-coprime) part of Theorem 1.6, `paper.tex:268–307`.
An arbitrary finite indexed family is represented by a finset of indices;
indices need not have distinct moduli or residues. Congruence means divisibility
of the difference, with the integer conventions of `paper.tex:77–85`.
-/
namespace P203Specs.Ch01

universe u

/-- The simultaneous congruences on a finite set of indices. -/
def CRTSolution {ι : Type u} (s : Finset ι) (m a : ι → ℤ) (x : ℤ) : Prop :=
  ∀ i ∈ s, m i ∣ x - a i

/-- Mathlib's normalized integer lcm: nonnegative, with empty lcm one. -/
def finiteCRTLcm {ι : Type u} (s : Finset ι) (m : ι → ℤ) : ℤ := s.lcm m

/-- Existence is equivalent to pairwise compatibility, with arbitrary positive
moduli, including modulus one, repeated moduli, singleton and empty families. -/
def CompatibleCRTExistence : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (m a : ι → ℤ), (∀ i ∈ s, 0 < m i) →
    ((∃ x : ℤ, CRTSolution s m a x) ↔
      ∀ i ∈ s, ∀ j ∈ s, (Int.gcd (m i) (m j) : ℤ) ∣ a i - a j)

/-- The full solution set is the coset of the lcm multiples through any solution. -/
def CompatibleCRTSolutions : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (m a : ι → ℤ), (∀ i ∈ s, 0 < m i) →
    ∀ x₀ : ℤ, CRTSolution s m a x₀ → ∀ x : ℤ,
      CRTSolution s m a x ↔ ∃ t : ℤ, x = x₀ + finiteCRTLcm s m * t

/-- The chosen lcm has exactly the common-multiple universal property and
is positive for positive moduli. The empty convention is explicit. -/
def CompatibleCRTLcm : Prop :=
  (∀ {ι : Type u} (s : Finset ι) (m : ι → ℤ), (∀ i ∈ s, 0 < m i) →
    0 < finiteCRTLcm s m ∧
      ∀ z : ℤ, finiteCRTLcm s m ∣ z ↔ ∀ i ∈ s, m i ∣ z) ∧
  (∀ {ι : Type u} (m : ι → ℤ), finiteCRTLcm ∅ m = 1)

end P203Specs.Ch01
