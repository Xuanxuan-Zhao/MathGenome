import MathGenome.Internal.Specs.D05.Foundations.IdealsGcd

/-! Independent statements for the factorization part of paper.tex:370–382.
The factors are formal polynomials over an arbitrary field. Multisets retain
every occurrence of a factor, while forgetting precisely their order. Units
are actual polynomial units; the final statements identify them with nonzero
constants and explicitly treat the empty product. -/

namespace D05.Specs.Factorization

/-- The Bézout identity used to prove that an irreducible is prime. -/
def irreducibleBezout : Prop :=
  ∀ (K : Type*) [Field K] (p a : Polynomial K),
    Irreducible p → ¬ p ∣ a →
    ∃ u v : Polynomial K, u * p + v * a = 1

/-- Irreducibles are prime, including the nonzero and nonunit conditions. -/
def irreduciblesPrime : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K), Irreducible p → Prime p

/-- Factorization of every nonzero polynomial, with no positive-degree
assumption. A multiset can be empty and can contain repeated factors. -/
def factorization : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K), p ≠ 0 →
    ∃ (u : (Polynomial K)ˣ) (s : Multiset (Polynomial K)),
      (∀ q ∈ s, q.Monic ∧ Irreducible q) ∧ p = (u : Polynomial K) * s.prod

/-- Any two such factorizations agree in their unit and in their factors,
including all multiplicities. Equality of multisets is uniqueness up to order. -/
def factorizationUnique : Prop :=
  ∀ (K : Type*) [Field K] (u v : (Polynomial K)ˣ)
    (s t : Multiset (Polynomial K)),
    (∀ q ∈ s, q.Monic ∧ Irreducible q) →
    (∀ q ∈ t, q.Monic ∧ Irreducible q) →
    (u : Polynomial K) * s.prod = (v : Polynomial K) * t.prod →
    u = v ∧ s = t

/-- Polynomial units over a field are exactly the nonzero constants. -/
def unitsAreConstants : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K),
    IsUnit p ↔ ∃ c : K, c ≠ 0 ∧ p = Polynomial.C c

/-- In any factorization, there are no irreducible factors precisely when
the polynomial is a unit. This includes all nonzero constant polynomials. -/
def emptyFactors : Prop :=
  ∀ (K : Type*) [Field K] (p : Polynomial K)
    (u : (Polynomial K)ˣ) (s : Multiset (Polynomial K)),
    (∀ q ∈ s, q.Monic ∧ Irreducible q) →
    p = (u : Polynomial K) * s.prod → (s = 0 ↔ IsUnit p)

/-- A nonzero constant has an explicit factorization with the empty product. -/
def constantFactorization : Prop :=
  ∀ (K : Type*) [Field K] (c : K), c ≠ 0 →
    ∃ u : (Polynomial K)ˣ,
      (u : Polynomial K) = Polynomial.C c ∧
      Polynomial.C c = (u : Polynomial K) * (0 : Multiset (Polynomial K)).prod

end D05.Specs.Factorization
