import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
The definitions and maximal-annihilator observation in paper.tex:961.
Rings are commutative and unital; zero rings and arbitrary (possibly zero,
not necessarily finite) modules are allowed. In particular, the definition
of associated primes uses exact annihilators, with no radical and no
Noetherian hypothesis. The localization in support is the same fraction
module used in Chapter 4.
-/
namespace P103.Specs.Ch05.AssociatedPrimesInterface

universe u v

def ElementAnnihilatorType :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    M → Ideal R

def elementAnnihilatorValue : ElementAnnihilatorType.{u,v} :=
  fun R _ M _ _ x => (⊥ : Submodule R M).colon {x}

def AssociatedPrimesType :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Set (Ideal R)

def associatedPrimesValue : AssociatedPrimesType.{u,v} :=
  fun R _ M _ _ => {p | p.IsPrime ∧ ∃ x : M, p = elementAnnihilatorValue R M x}

def SupportType :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    Set (PrimeSpectrum R)

def supportValue : SupportType.{u,v} :=
  fun _ _ M _ _ => {p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M)}

def mem_elementAnnihilatorType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : M) (r : R), r ∈ elementAnnihilatorValue R M x ↔ r • x = 0

def mem_associatedPrimesType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (p : Ideal R),
    p ∈ associatedPrimesValue R M ↔ p.IsPrime ∧ ∃ x : M, p = elementAnnihilatorValue R M x

def mem_supportType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R),
    p ∈ supportValue R M ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M)

def annihilator_witness_ne_zeroType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (p : Ideal R) (x : M), p.IsPrime → p = elementAnnihilatorValue R M x → x ≠ 0

/-- The equivalence holds over every commutative ring, without finiteness. -/
def mem_associatedPrimes_iff_embeddingType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (p : Ideal R),
    p ∈ associatedPrimesValue R M ↔
      p.IsPrime ∧ ∃ f : R ⧸ p →ₗ[R] M, Function.Injective f

/-- Maximality is among the annihilators of all nonzero elements of M. -/
def exists_maximal_annihilatorType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Nontrivial M],
    ∃ x : M, x ≠ 0 ∧ ∀ y : M, y ≠ 0 →
      elementAnnihilatorValue R M x ≤ elementAnnihilatorValue R M y →
        elementAnnihilatorValue R M x = elementAnnihilatorValue R M y

/-- Once such an annihilator is maximal, primality needs no ring finiteness. -/
def maximal_annihilator_isPrimeType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : M), x ≠ 0 →
    (∀ y : M, y ≠ 0 →
      elementAnnihilatorValue R M x ≤ elementAnnihilatorValue R M y →
        elementAnnihilatorValue R M x = elementAnnihilatorValue R M y) →
    (elementAnnihilatorValue R M x).IsPrime

def associatedPrimes_nonemptyType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Nontrivial M],
    (associatedPrimesValue R M).Nonempty

def associatedPrimes_eq_emptyType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M], associatedPrimesValue R M = ∅

def support_eq_emptyType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M], supportValue R M = ∅

end P103.Specs.Ch05.AssociatedPrimesInterface
