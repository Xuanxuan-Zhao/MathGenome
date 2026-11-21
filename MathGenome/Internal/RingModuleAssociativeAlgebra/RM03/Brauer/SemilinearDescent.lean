import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.SemilinearDescent
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.GaloisDescent

open scoped TensorProduct
open Module

universe u v w w'

namespace RM03.Brauer.SemilinearDescent

open LieAlgebrasAndRepresentations.GaloisDescent (SemilinearAction)

section VectorSpace

/-- Fixed vectors span over the extension field. -/
theorem fixed_span {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V] [FiniteDimensional K V]
    (ρ : SemilinearAction k K V) :
    Submodule.span K (ρ.fixed : Set V) = ⊤ :=
  ρ.invariant_span

/-- The same vectors of an invariant basis are a basis of the fixed space. -/
theorem fixed_basis {k : Type u} {K : Type v} {V : Type w} {ι : Type w'} [Field k] [Field K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V] [FiniteDimensional K V]
    (ρ : SemilinearAction k K V) (b : Basis ι K V) (hb : ∀ i, b i ∈ ρ.fixed) :
    ∃ c : Basis ι k ρ.fixed, ∀ i, (c i : V) = b i :=
  ⟨ρ.basisFixed b hb, ρ.basisFixed_apply b hb⟩

/-- Canonical linear descent along a finite Galois extension. -/
theorem linear_descent {k : Type u} {K : Type v} {V : Type w} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [AddCommGroup V] [Module K V]
    [Module k V] [IsScalarTower k K V] [FiniteDimensional K V]
    (ρ : SemilinearAction k K V) :
    ∃ e : (K ⊗[k] ρ.fixed) ≃ₗ[K] V, ∀ (a : K) (x : ρ.fixed),
      e (a ⊗ₜ[k] x) = a • (x : V) :=
  ⟨LinearEquiv.ofBijective ρ.descentMap ρ.fixed_point_descent, fun _ _ => rfl⟩

end VectorSpace

namespace AlgebraAction

variable {k : Type u} {K : Type v} {A : Type w} [Field k] [Field K] [Algebra k K]
variable [Ring A] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
variable (ρ : AlgebraAction k K A)

/-- The algebra map agrees with the vector-space descent map on the same
fixed vectors. -/
theorem descentMap_toLinearMap :
    ρ.descentMap.toLinearMap = ρ.toSemilinearAction.descentMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  exact ρ.descentMap_tmul a x

variable [FiniteDimensional k K] [IsGalois k K]

/-- The canonical algebra equivalence extending the fixed-point inclusion. -/
noncomputable def descentEquiv : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K] A :=
  AlgEquiv.ofBijective ρ.descentMap <| by
    change Function.Bijective ρ.descentMap.toLinearMap
    rw [ρ.descentMap_toLinearMap]
    exact ρ.toSemilinearAction.fixed_point_descent

@[simp]
theorem descentEquiv_tmul (a : K) (x : ρ.fixedSubalgebra) :
    ρ.descentEquiv (a ⊗ₜ[k] x) = a • (x : A) :=
  ρ.descentMap_tmul a x

end AlgebraAction

section Algebra

/-- Canonical algebra descent along a finite Galois extension. -/
theorem algebra_descent {k : Type u} {K : Type v} {A : Type w} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] [Ring A] [Algebra K A]
    [Algebra k A] [IsScalarTower k K A] [FiniteDimensional K A]
    (ρ : AlgebraAction k K A) :
    ∃ e : (K ⊗[k] ρ.fixedSubalgebra) ≃ₐ[K] A, ∀ (a : K) (x : ρ.fixedSubalgebra),
      e (a ⊗ₜ[k] x) = a • (x : A) :=
  ⟨ρ.descentEquiv, ρ.descentEquiv_tmul⟩

/-- Extending a restriction to fixed subalgebras recovers the original
equivariant map via the two canonical descent maps. -/
theorem equivariant_restriction {k : Type u} {K : Type v} {A : Type w} {B : Type w'}
    [Field k] [Field K] [Algebra k K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Algebra k A] [IsScalarTower k K A] [Algebra k B] [IsScalarTower k K B]
    (ρ : AlgebraAction k K A) (τ : AlgebraAction k K B)
    (f : A →ₐ[K] B) (hf : ρ.Equivariant τ f) :
    (∀ x : ρ.fixedSubalgebra, (ρ.restrictHom τ f hf x : B) = f (x : A)) ∧
    τ.descentMap.comp (Algebra.TensorProduct.map (AlgHom.id K K) (ρ.restrictHom τ f hf)) =
      f.comp ρ.descentMap := by
  have h (x : ρ.fixedSubalgebra) : (ρ.restrictHom τ f hf x : B) = f (x : A) := rfl
  refine ⟨h, Algebra.TensorProduct.ext' ?_⟩
  intro a x
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgebraAction.descentMap_tmul, h, map_smul]

end Algebra

end RM03.Brauer.SemilinearDescent
