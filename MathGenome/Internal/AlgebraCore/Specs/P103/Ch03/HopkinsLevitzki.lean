import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.ArtinianRadical
import Mathlib.RingTheory.FiniteLength

/-!
Independent statements for the finite-length conclusions of paper.tex,
Theorem 3.3, lines 652–689, and the semisimplicity facts stated in its proof.
Rings are associative and unital; neither commutativity nor nontriviality
is assumed. Modules are unital left modules, in an arbitrary universe.

`radical R` is the intersection of maximal left ideals, already identified
with `Ring.jacobson R` in the upstream interface. Its two-sidedness gives
its powers and quotient ring. The semisimplicity hypothesis on that quotient
uses its own regular action, not the action of R on an unrelated module.
`IsFiniteLength` means a finite sequence of extensions by simple modules;
it is equivalent to existence of a composition series from bottom to top.

Right regular modules are represented by the left regular module of Rᵐᵒᵖ,
as in the global convention at paper.tex line 47. This has exactly the
right-ideal lattice of R under the bijection `op`.
The finite decomposition permits n = 0, so the zero module and zero ring
are included. The commutative local-product conclusion and the radical
conclusions of the same source theorem belong to separate goals.
-/

universe u v

namespace P103.Specs.Ch03.HopkinsLevitzki

open P103.Specs.Ch03.JacobsonRadical (radical)

/-- Every module over a ring whose left regular module is semisimple is semisimple. -/
def all_modules_semisimpleType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R R], IsSemisimpleModule R M

/-- Either chain condition makes a semisimple decomposition finite. -/
def semisimple_finite_decompositionType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M],
    (IsArtinian R M ∨ IsNoetherian R M) →
      ∃ (n : ℕ) (S : Fin n → Submodule R M)
        (_ : M ≃ₗ[R] Π₀ i : Fin n, S i), ∀ i, IsSimpleModule R (S i)

def left_regular_finite_lengthType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing R], IsFiniteLength R R

def left_noetherianType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing R], IsNoetherianRing R

def right_regular_finite_lengthType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing Rᵐᵒᵖ],
    IsFiniteLength Rᵐᵒᵖ Rᵐᵒᵖ

def right_noetherianType : Prop :=
  ∀ (R : Type u) [Ring R] [IsArtinianRing Rᵐᵒᵖ],
    IsNoetherianRing Rᵐᵒᵖ

/-- The two ring hypotheses are explicit; R need not itself be Artinian. -/
def noetherian_finite_lengthType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    IsNilpotent (radical R) →
    IsSemisimpleModule (R ⧸ radical R) (R ⧸ radical R) →
    IsNoetherian R M → IsFiniteLength R M

end P103.Specs.Ch03.HopkinsLevitzki
