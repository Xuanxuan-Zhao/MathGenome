import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.ChainConditions
import MathGenome.Internal.AlgebraCore.P103.Ch01.ModuleExactness

/-! Chain conditions for modules, paper.tex 509–534.

`R` is an arbitrary associative unital ring. No commutativity or nontriviality
is assumed. The results apply to right S-modules by taking `R := Sᵐᵒᵖ`.
Chains are indexed by ℕ; stabilization means equality at every later stage.
A maximal/minimal member need not be a greatest/least member. `U.FG` means
that a finite set of elements of U spans U. The zero results cover every
subsingleton module, and all results allow the zero ring.
-/

namespace P103.Ch02.ChainConditions

theorem noetherian_iff_ascending (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    IsNoetherian R M ↔
    ∀ c : ℕ → Submodule R M, Monotone c →
      ∃ n, ∀ m, n ≤ m → c n = c m := by
  constructor
  · intro h c hc
    exact monotone_stabilizes_iff_noetherian.mpr h ⟨c, hc⟩
  · intro h
    apply monotone_stabilizes_iff_noetherian.mp
    intro c
    exact h c c.monotone

theorem noetherian_iff_maximal (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    IsNoetherian R M ↔
    ∀ S : Set (Submodule R M), S.Nonempty →
      ∃ U ∈ S, ∀ V ∈ S, ¬ U < V := by
  exact set_has_maximal_iff_noetherian.symm

theorem noetherian_iff_fg (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    IsNoetherian R M ↔ ∀ U : Submodule R M, U.FG := by
  exact isNoetherian_def

theorem artinian_iff_descending (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔
    ∀ c : ℕ → Submodule R M, Antitone c →
      ∃ n, ∀ m, n ≤ m → c n = c m := by
  constructor
  · intro h c hc
    exact monotone_stabilizes_iff_artinian.mpr h ⟨c, hc⟩
  · intro h
    apply monotone_stabilizes_iff_artinian.mp
    intro c
    exact h c c.monotone

theorem artinian_iff_minimal (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔
    ∀ S : Set (Submodule R M), S.Nonempty →
      ∃ U ∈ S, ∀ V ∈ S, ¬ V < U := by
  exact set_has_minimal_iff_artinian.symm

theorem noetherian_submodule (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) :
    IsNoetherian R M → IsNoetherian R U := by
  intro h
  have := h
  infer_instance

theorem noetherian_quotient (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) :
    IsNoetherian R M → IsNoetherian R (M ⧸ U) := by
  intro h
  have := h
  infer_instance

theorem noetherian_extension (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C) :
    Function.Exact u v → IsNoetherian R A → IsNoetherian R C → IsNoetherian R B := by
  intro he hA hC
  have := hA
  have := hC
  exact isNoetherian_of_range_eq_ker u v
    ((P103.Ch01.ModuleExactness.exact_iff R A B C u v).mp he)

theorem noetherian_short_exact_iff (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C)
    (hu : Function.Injective u) (he : Function.Exact u v) (hv : Function.Surjective v) :
    IsNoetherian R B ↔ IsNoetherian R A ∧ IsNoetherian R C := by
  constructor
  · intro hB
    have := hB
    exact ⟨isNoetherian_of_injective u hu,
      isNoetherian_of_surjective v (LinearMap.range_eq_top.mpr hv)⟩
  · rintro ⟨hA, hC⟩
    exact noetherian_extension R A B C u v he hA hC

theorem noetherian_submodule_quotient_iff (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) :
    IsNoetherian R M ↔ IsNoetherian R U ∧ IsNoetherian R (M ⧸ U) := by
  exact isNoetherian_iff_submodule_quotient U

theorem noetherian_zero (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    IsNoetherian R M := by
  infer_instance

theorem artinian_submodule (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) :
    IsArtinian R M → IsArtinian R U := by
  intro h
  have := h
  infer_instance

theorem artinian_quotient (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) :
    IsArtinian R M → IsArtinian R (M ⧸ U) := by
  intro h
  have := h
  infer_instance

theorem artinian_extension (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C) :
    Function.Exact u v → IsArtinian R A → IsArtinian R C → IsArtinian R B := by
  intro he hA hC
  have := hA
  have := hC
  exact isArtinian_of_range_eq_ker u v
    ((P103.Ch01.ModuleExactness.exact_iff R A B C u v).mp he)

theorem artinian_short_exact_iff (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] (u : A →ₗ[R] B) (v : B →ₗ[R] C)
    (hu : Function.Injective u) (he : Function.Exact u v) (hv : Function.Surjective v) :
    IsArtinian R B ↔ IsArtinian R A ∧ IsArtinian R C := by
  constructor
  · intro hB
    have := hB
    exact ⟨isArtinian_of_injective u hu, isArtinian_of_surjective B v hv⟩
  · rintro ⟨hA, hC⟩
    exact artinian_extension R A B C u v he hA hC

theorem artinian_submodule_quotient_iff (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) :
    IsArtinian R M ↔ IsArtinian R U ∧ IsArtinian R (M ⧸ U) := by
  exact isArtinian_iff_submodule_quotient U

theorem artinian_zero (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    IsArtinian R M := by
  exact isArtinian_of_finite

end P103.Ch02.ChainConditions
