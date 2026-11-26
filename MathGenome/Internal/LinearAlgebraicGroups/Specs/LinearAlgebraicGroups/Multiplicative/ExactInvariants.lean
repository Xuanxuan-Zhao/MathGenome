import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.Algebra.Exact.Basic

open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.RationalRepresentations

variable {k V W : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {A : HopfAlgebraCategory k}
  {ρ : RightComodule k A V} {σ : RightComodule k A W}

theorem mem_invariants {v : V} :
    v ∈ invariants A ρ ↔ ρ.coaction v = v ⊗ₜ[k] (1 : A) := by
  change ρ.coaction v - v ⊗ₜ[k] (1 : A) = 0 ↔ _
  exact sub_eq_zero

/-- An equivariant linear map restricted to the invariant subspaces. -/
def invariantsMap (f : V →ₗ[k] W)
    (hf : (f.rTensor A).comp ρ.coaction = σ.coaction.comp f) :
    invariants A ρ →ₗ[k] invariants A σ :=
  f.restrict fun v hv ↦ mem_invariants.mpr (by
    have h := DFunLike.congr_fun hf v
    change (f.rTensor A) (ρ.coaction v) = σ.coaction (f v) at h
    rw [mem_invariants.mp hv, LinearMap.rTensor_tmul] at h
    exact h.symm)

@[simp]
theorem coe_invariantsMap (f : V →ₗ[k] W)
    (hf : (f.rTensor A).comp ρ.coaction = σ.coaction.comp f) (v : invariants A ρ) :
    (invariantsMap f hf v : W) = f (v : V) :=
  rfl

end LinearAlgebraicGroups.RationalRepresentations

namespace LinearAlgebraicGroups.Specs.ExactInvariants

open LinearAlgebraicGroups.RationalRepresentations

/-- Invariants of finite-dimensional rational modules over a group of multiplicative
type take short exact sequences to short exact sequences. The modules and maps
are presented as right comodules and comodule maps over its coordinate Hopf algebra. -/
def ExactInvariants : Prop :=
  ∀ {k U V W : Type u} [Field k]
    [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (A : HopfAlgebraCategory k), CharacterDescent.IsMultiplicativeType A →
    ∀ (ρ : RightComodule k A U) (σ : RightComodule k A V) (τ : RightComodule k A W)
      (f : U →ₗ[k] V) (g : V →ₗ[k] W)
      (hf : (f.rTensor A).comp ρ.coaction = σ.coaction.comp f)
      (hg : (g.rTensor A).comp σ.coaction = τ.coaction.comp g),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
        Function.Injective (invariantsMap f hf) ∧
          Function.Exact (invariantsMap f hf) (invariantsMap g hg) ∧
          Function.Surjective (invariantsMap g hg)

end LinearAlgebraicGroups.Specs.ExactInvariants
