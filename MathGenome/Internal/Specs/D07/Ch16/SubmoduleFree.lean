import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Independent statements for K07.16.submodule_free, paper.tex:3018–3086.
The supplied ambient basis expresses finite freeness of rank n. The conclusion
uses the first s vectors of a newly chosen ambient basis, with nonzero diagonal
coefficients in divisibility order. No finite-generation assumption is placed
on N, and rank zero and the zero submodule are included. -/

universe u v

namespace Specs.D07.Ch16.SubmoduleFree

open Module

/-- The full diagonal-basis theorem over an arbitrary nontrivial PID. -/
def DiagonalBasis : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type v) [AddCommGroup M] [Module R M]
    (_b : Basis (Fin n) R M) (N : Submodule R M),
    ∃ (s : ℕ) (hs : s ≤ n) (e : Basis (Fin n) R M)
      (a : Fin s → R) (f : Basis (Fin s) R N),
      (∀ i, a i ≠ 0) ∧
      (∀ i j, i ≤ j → a i ∣ a j) ∧
      (∀ i, (f i : M) = a i • e (Fin.castLE hs i))

/-- In particular, every submodule of a finite free module is finite free. -/
def FiniteFree : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type v) [AddCommGroup M] [Module R M]
    (_b : Basis (Fin n) R M) (N : Submodule R M),
    Module.Free R N ∧ Module.Finite R N

end Specs.D07.Ch16.SubmoduleFree
