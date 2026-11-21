import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Exact.Basic

/-! Chain conditions for modules, paper.tex 509–534.

`R` is an arbitrary associative unital ring. No commutativity or nontriviality
is assumed. The results apply to right S-modules by taking `R := Sᵐᵒᵖ`.
Chains are indexed by ℕ; stabilization means equality at every later stage.
A maximal/minimal member need not be a greatest/least member. `U.FG` means
that a finite set of elements of U spans U. The zero results cover every
subsingleton module, and all results allow the zero ring.
-/

namespace P103.Specs.Ch02.ChainConditions

def noetherian_iff_ascendingType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M],
    IsNoetherian R M ↔
    ∀ c : ℕ → Submodule R M, Monotone c →
      ∃ n, ∀ m, n ≤ m → c n = c m

def noetherian_iff_maximalType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M],
    IsNoetherian R M ↔
    ∀ S : Set (Submodule R M), S.Nonempty →
      ∃ U ∈ S, ∀ V ∈ S, ¬ U < V

def noetherian_iff_fgType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M],
    IsNoetherian R M ↔ ∀ U : Submodule R M, U.FG

def artinian_iff_descendingType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M],
    IsArtinian R M ↔
    ∀ c : ℕ → Submodule R M, Antitone c →
      ∃ n, ∀ m, n ≤ m → c n = c m

def artinian_iff_minimalType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M],
    IsArtinian R M ↔
    ∀ S : Set (Submodule R M), S.Nonempty →
      ∃ U ∈ S, ∀ V ∈ S, ¬ V < U

def noetherian_submoduleType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M),
    IsNoetherian R M → IsNoetherian R U

def noetherian_quotientType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M),
    IsNoetherian R M → IsNoetherian R (M ⧸ U)

def noetherian_extensionType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C),
    Function.Exact u v → IsNoetherian R A → IsNoetherian R C → IsNoetherian R B

def noetherian_short_exact_iffType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C)
    (_hu : Function.Injective u) (_he : Function.Exact u v) (_hv : Function.Surjective v),
    IsNoetherian R B ↔ IsNoetherian R A ∧ IsNoetherian R C

def noetherian_submodule_quotient_iffType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M),
    IsNoetherian R M ↔ IsNoetherian R U ∧ IsNoetherian R (M ⧸ U)

def noetherian_zeroType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M],
    IsNoetherian R M

def artinian_submoduleType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M),
    IsArtinian R M → IsArtinian R U

def artinian_quotientType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M),
    IsArtinian R M → IsArtinian R (M ⧸ U)

def artinian_extensionType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C),
    Function.Exact u v → IsArtinian R A → IsArtinian R C → IsArtinian R B

def artinian_short_exact_iffType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C)
    (_hu : Function.Injective u) (_he : Function.Exact u v) (_hv : Function.Surjective v),
    IsArtinian R B ↔ IsArtinian R A ∧ IsArtinian R C

def artinian_submodule_quotient_iffType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M),
    IsArtinian R M ↔ IsArtinian R U ∧ IsArtinian R (M ⧸ U)

def artinian_zeroType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M],
    IsArtinian R M

end P103.Specs.Ch02.ChainConditions
