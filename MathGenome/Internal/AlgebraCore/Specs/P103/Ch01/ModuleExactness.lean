import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact.Basic

/-! Submodules and exactness, paper.tex 75–94.
All scalar rings are arbitrary unital, possibly noncommutative rings. There is
no nontriviality assumption on a ring or module. In particular every statement
can be instantiated with `R := Sᵐᵒᵖ` for right S-modules, using the paper's
convention that a right module is a left module over the opposite ring.
-/

namespace P103.Specs.Ch01.ModuleExactness

def firstIsomorphismType := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N), (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f

noncomputable def firstIsomorphismValue (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  f.quotKerEquivRange

def firstIsomorphism_applyType : Prop := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (m : M),
  (firstIsomorphismValue R M N f ((LinearMap.ker f).mkQ m) : N) = f m

def surjectiveIsomorphismType := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f), (M ⧸ LinearMap.ker f) ≃ₗ[R] N

noncomputable def surjectiveIsomorphismValue (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] N :=
  f.quotKerEquivOfSurjective hf

def surjectiveIsomorphism_applyType : Prop := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) (m : M),
  surjectiveIsomorphismValue R M N f hf ((LinearMap.ker f).mkQ m) = f m

def quotient_smulType : Prop := ∀ (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] (U : Submodule R M) (r : R) (m : M),
  U.mkQ (r • m) = r • U.mkQ m

def quotient_universalType : Prop := ∀ (R M P : Type*) [Ring R] [AddCommGroup M] [AddCommGroup P] [Module R M] [Module R P] (U : Submodule R M) (g : M →ₗ[R] P),
  (∃! h : (M ⧸ U) →ₗ[R] P, h.comp U.mkQ = g) ↔ U ≤ LinearMap.ker g

def kernel_annihilatesType : Prop := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N),
  f.comp (LinearMap.ker f).subtype = 0

def kernel_universalType : Prop := ∀ (R M N P : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : P →ₗ[R] M),
  (∃! k : P →ₗ[R] LinearMap.ker f, (LinearMap.ker f).subtype.comp k = g) ↔ f.comp g = 0

def cokernel_annihilatesType : Prop := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N),
  (LinearMap.range f).mkQ.comp f = 0

def cokernel_universalType : Prop := ∀ (R M N P : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P),
  (∃! k : (N ⧸ LinearMap.range f) →ₗ[R] P, k.comp (LinearMap.range f).mkQ = g) ↔ g.comp f = 0

def exact_iffType : Prop := ∀ (R L M N : Type*) [Ring R] [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [Module R L] [Module R M] [Module R N] (u : L →ₗ[R] M) (v : M →ₗ[R] N),
  Function.Exact u v ↔ LinearMap.range u = LinearMap.ker v

def kernel_exactType : Prop := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N),
  Function.Exact (LinearMap.ker f).subtype f

def cokernel_exactType : Prop := ∀ (R M N : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N),
  Function.Exact f (LinearMap.range f).mkQ

def zero_left_iff_injectiveType : Prop := ∀ (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] (f : M →ₗ[R] N),
  Function.Exact (0 : Z →ₗ[R] M) f ↔ Function.Injective f

def zero_right_iff_surjectiveType : Prop := ∀ (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] (f : M →ₗ[R] N),
  Function.Exact f (0 : N →ₗ[R] Z) ↔ Function.Surjective f

def zero_module_left_iff_injectiveType : Prop := ∀ (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] [Subsingleton Z] (a : Z →ₗ[R] M) (f : M →ₗ[R] N),
  Function.Exact a f ↔ Function.Injective f

def zero_module_right_iff_surjectiveType : Prop := ∀ (R M N Z : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup Z] [Module R M] [Module R N] [Module R Z] [Subsingleton Z] (f : M →ₗ[R] N) (b : N →ₗ[R] Z),
  Function.Exact f b ↔ Function.Surjective f

end P103.Specs.Ch01.ModuleExactness
