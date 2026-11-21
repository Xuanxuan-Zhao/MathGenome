import MathGenome.Internal.Specs.D07.Ch22.NoetherianEquivalences
import Mathlib.Algebra.Module.FinitePresentation

/-!
Independent statements for K07.22.noetherian_finite_modules,
paper.tex:6969–6995. Scalars are commutative unital rings, including
the zero ring; modules are unital and may be zero. No domain, PID,
freeness, or finite generation of a general Noetherian module is assumed.

`IsNoetherian` is linked to the source's ascending-chain condition in
`NoetherianEquivalences.NoetherianCharacterization`. `Module.Finite`
means finite generation, not finiteness of the underlying set.
`Module.FinitePresentation` records finitely many relations as well as
generators. The last statement also spells out a finite free presentation.
-/

universe u v w z

namespace Specs.D07.Ch22.NoetherianFiniteModules

def SubmoduleNoetherian : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian R M] (N : Submodule R M), IsNoetherian R N

def QuotientNoetherian : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [IsNoetherian R M] (N : Submodule R M), IsNoetherian R (M ⧸ N)

/-- Injectivity, exactness at M, and surjectivity express the displayed
short exact sequence, with no splitting assumption. -/
def ExactSequenceNoetherian : Prop :=
  ∀ (R : Type u) [CommRing R]
    (U : Type v) [AddCommGroup U] [Module R U]
    (M : Type w) [AddCommGroup M] [Module R M]
    (V : Type z) [AddCommGroup V] [Module R V]
    (f : U →ₗ[R] M) (g : M →ₗ[R] V),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsNoetherian R U → IsNoetherian R V → IsNoetherian R M

def FiniteModuleNoetherian : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    IsNoetherian R M

def FiniteModuleFinitelyPresented : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    Module.FinitePresentation R M

/-- A concrete presentation Rˢ → Rⁿ → M → 0, including finite generation
of the relation submodule; no freeness of that kernel is claimed. -/
def FiniteFreePresentation : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ (n s : ℕ) (π : (Fin n → R) →ₗ[R] M)
      (A : (Fin s → R) →ₗ[R] (Fin n → R)),
      Function.Surjective π ∧ Function.Exact A π ∧ (LinearMap.ker π).FG

end Specs.D07.Ch22.NoetherianFiniteModules
