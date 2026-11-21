import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Polynomial.Basis

/-!
Independent statements for K07.22.hilbert_basis, paper.tex:6995–7045.
Rings and algebras are commutative and unital. The Hilbert basis and
finite-type conclusions allow zero divisors and the zero ring, and the
number of variables may be zero. `Algebra.FiniteType` means a finite set
of algebra generators, rather than generators as a module.

The last two facets retain the source's field examples: the countable
variable ring has a strictly increasing sequence of ideals, whereas k[X]
is generated as an algebra by X but its powers are linearly independent
and it is not a finite k-module. Natural index i denotes source X_{i+1}.
-/

universe u v

namespace Specs.D07.Ch22.HilbertBasis

def OneVariableNoetherian : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    IsNoetherianRing (Polynomial R)

def FiniteVariablesNoetherian : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ),
    IsNoetherianRing (MvPolynomial (Fin n) R)

/-- A finite algebra generating list gives exactly a surjection from a
polynomial ring on a finite list of formal variables. -/
def FiniteTypePresentation : Prop :=
  ∀ (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A],
    Algebra.FiniteType R A ↔
      ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective f

def FiniteTypeNoetherian : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A],
    IsNoetherianRing A

/-- The ideal (X₁,...,Xₙ); for n=0 this is the zero ideal. -/
noncomputable def initialVariableIdeal (k : Type u) [CommRing k] (n : ℕ) :
    Ideal (MvPolynomial ℕ k) :=
  Ideal.span (MvPolynomial.X '' {i : ℕ | i < n})

def InfiniteVariableChain : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    initialVariableIdeal k n < initialVariableIdeal k (n + 1) ∧
    MvPolynomial.X n ∉ initialVariableIdeal k n ∧
    MvPolynomial.X n ∈ initialVariableIdeal k (n + 1)

def InfiniteVariablesNotNoetherian : Prop :=
  ∀ (k : Type u) [Field k], ¬ IsNoetherianRing (MvPolynomial ℕ k)

def AlgebraFiniteNotModuleFinite : Prop :=
  ∀ (k : Type u) [Field k],
    Algebra.adjoin k ({Polynomial.X} : Set (Polynomial k)) = ⊤ ∧
    Algebra.FiniteType k (Polynomial k) ∧
    LinearIndependent k (fun n : ℕ => (Polynomial.X : Polynomial k) ^ n) ∧
    ¬ Module.Finite k (Polynomial k)

end Specs.D07.Ch22.HilbertBasis
