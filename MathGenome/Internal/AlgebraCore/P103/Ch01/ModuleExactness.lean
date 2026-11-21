import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.ModuleExactness

/-! Submodules and exactness, paper.tex 75–94.
All scalar rings are arbitrary unital, possibly noncommutative rings. There is
no nontriviality assumption on a ring or module. In particular every statement
can be instantiated with `R := Sᵐᵒᵖ` for right S-modules, using the paper's
convention that a right module is a left module over the opposite ring.
-/

namespace P103.Ch01.ModuleExactness

noncomputable def firstIsomorphism (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  f.quotKerEquivRange

theorem firstIsomorphism_apply (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (m : M) :
    (firstIsomorphism R M N f ((LinearMap.ker f).mkQ m) : N) = f m := by
  exact LinearMap.quotKerEquivRange_apply_mk f m

noncomputable def surjectiveIsomorphism (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] N :=
  f.quotKerEquivOfSurjective hf

theorem surjectiveIsomorphism_apply (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) (m : M) :
    surjectiveIsomorphism R M N f hf ((LinearMap.ker f).mkQ m) = f m := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk f hf m

theorem quotient_smul (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) (r : R) (m : M) :
    U.mkQ (r • m) = r • U.mkQ m := by
  exact U.mkQ.map_smul r m

theorem quotient_universal (R M P : Type*) [Ring R] [AddCommGroup M] [AddCommGroup P] [Module R M] [Module R P] (U : Submodule R M) (g : M →ₗ[R] P) :
    (∃! h : (M ⧸ U) →ₗ[R] P, h.comp U.mkQ = g) ↔ U ≤ LinearMap.ker g := by
  constructor
  · rintro ⟨h, hh, _⟩
    intro m hm
    change g m = 0
    rw [← hh]
    change h (U.mkQ m) = 0
    have hz : U.mkQ m = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hm
    rw [hz, map_zero]
  · intro hg
    refine ⟨U.liftQ g hg, U.liftQ_mkQ g hg, ?_⟩
    intro h hh
    apply U.quot_hom_ext
    intro m
    change h (U.mkQ m) = _
    simpa using DFunLike.congr_fun hh m

theorem kernel_annihilates (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    f.comp (LinearMap.ker f).subtype = 0 := by
  ext m
  exact m.property

theorem kernel_universal (R M N P : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : P →ₗ[R] M) :
    (∃! k : P →ₗ[R] LinearMap.ker f, (LinearMap.ker f).subtype.comp k = g) ↔ f.comp g = 0 := by
  constructor
  · rintro ⟨k, hk, _⟩
    rw [← hk, ← LinearMap.comp_assoc, kernel_annihilates R M N f]
    simp
  · intro hfg
    have hg : ∀ p, g p ∈ LinearMap.ker f := by
      intro p
      exact DFunLike.congr_fun hfg p
    refine ⟨g.codRestrict (LinearMap.ker f) hg, ?_, ?_⟩
    · ext p
      rfl
    · intro k hk
      ext p
      exact DFunLike.congr_fun hk p

theorem cokernel_annihilates (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    (LinearMap.range f).mkQ.comp f = 0 := by
  apply LinearMap.range_le_ker_iff.mp
  rw [Submodule.ker_mkQ]

theorem cokernel_universal (R M N P : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (∃! k : (N ⧸ LinearMap.range f) →ₗ[R] P, k.comp (LinearMap.range f).mkQ = g) ↔ g.comp f = 0 := by
  exact (quotient_universal R N P (LinearMap.range f) g).trans LinearMap.range_le_ker_iff

theorem exact_iff (R L M N : Type*) [Ring R] [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [Module R L] [Module R M] [Module R N] (u : L →ₗ[R] M) (v : M →ₗ[R] N) :
    Function.Exact u v ↔ LinearMap.range u = LinearMap.ker v := by
  exact LinearMap.exact_iff.trans eq_comm

theorem kernel_exact (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    Function.Exact (LinearMap.ker f).subtype f := by
  exact LinearMap.exact_subtype_ker_map f

theorem cokernel_exact (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    Function.Exact f (LinearMap.range f).mkQ := by
  exact LinearMap.exact_map_mkQ_range f

theorem zero_left_iff_injective (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] (f : M →ₗ[R] N) :
    Function.Exact (0 : Z →ₗ[R] M) f ↔ Function.Injective f := by
  exact LinearMap.exact_zero_iff_injective Z f

theorem zero_right_iff_surjective (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] (f : M →ₗ[R] N) :
    Function.Exact f (0 : N →ₗ[R] Z) ↔ Function.Surjective f := by
  exact LinearMap.exact_zero_iff_surjective Z f

theorem zero_module_left_iff_injective (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] [Subsingleton Z] (a : Z →ₗ[R] M) (f : M →ₗ[R] N) :
    Function.Exact a f ↔ Function.Injective f := by
  have ha : a = 0 := by
    ext z
    have hz : z = 0 := Subsingleton.elim _ _
    simp [hz]
  rw [ha]
  exact zero_left_iff_injective R M N Z f

theorem zero_module_right_iff_surjective (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] [Subsingleton Z] (f : M →ₗ[R] N) (b : N →ₗ[R] Z) :
    Function.Exact f b ↔ Function.Surjective f := by
  have hb : b = 0 := Subsingleton.elim _ _
  rw [hb]
  exact zero_right_iff_surjective R M N Z f

end P103.Ch01.ModuleExactness
