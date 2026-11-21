import Mathlib.RingTheory.FiniteType
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.ChainConditions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FinitePresentation

/-!
The opening Noetherian conventions and Theorem 5.1 of paper.tex (937–947).
Chapters 4–7 use commutative unital rings, including the zero ring.
`Module.Finite` means finitely generated as a module; `Algebra.FiniteType`
means finitely generated as an algebra. They are deliberately distinct here.
`Module.FinitePresentation` has the finite-free-presentation interpretation
proved in Chapter 2. No freeness hypothesis is imposed on M or its submodules.
-/

universe u v w

namespace P103.Specs.Ch05.NoetherianFiniteness

/-- The source's ACC convention for rings agrees with the library predicate
and with finite generation of every ideal. -/
def ring_characterizationsType : Prop :=
  ∀ (R : Type u) [CommRing R],
    (IsNoetherianRing R ↔
      ∀ c : ℕ → Ideal R, Monotone c → ∃ n, ∀ m, n ≤ m → c n = c m) ∧
    (IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG)

/-- The same conventions for arbitrary modules, using the Chapter 2 interface. -/
def module_characterizationsType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    (IsNoetherian R M ↔
      ∀ c : ℕ → Submodule R M, Monotone c → ∃ n, ∀ m, n ≤ m → c n = c m) ∧
    (IsNoetherian R M ↔ ∀ N : Submodule R M, N.FG)

/-- Hilbert's basis theorem in one variable. -/
def polynomial_noetherianType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    IsNoetherianRing (Polynomial R)

/-- Any finite set of variables is allowed, including the empty set. -/
def mvPolynomial_noetherianType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (ι : Type v) [Finite ι], IsNoetherianRing (MvPolynomial ι R)

/-- Finite type is an algebra condition; no module-finiteness is assumed. -/
def finiteType_noetherianType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.FiniteType R A],
    IsNoetherianRing A

/-- A finite module is Noetherian and finitely presented, even when nonfree. -/
def finite_moduleType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    IsNoetherian R M ∧ Module.FinitePresentation R M

/-- Every submodule of a finite module is finite, Noetherian and finitely
presented as a module over the original ring. -/
def submodule_finitenessType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M),
    N.FG ∧ IsNoetherian R N ∧ Module.FinitePresentation R N

end P103.Specs.Ch05.NoetherianFiniteness
