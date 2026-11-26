import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.TensorAndDual

open scoped TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.RationalRepresentations

variable {k K V W : Type u} [Field k] [Field K] [Algebra k K]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (A : HopfAlgebraCategory k)

/-- The scalar-extended coaction is the extension of the original coaction
under the canonical identification of the tensor products. -/
def IsScalarExtension (ρ : RightComodule k A V)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V)) : Prop :=
  ρK.coaction =
    (TensorProduct.AlgebraTensorModule.distribBaseChange k K V A).toLinearMap.comp
      (ρ.coaction.baseChange K)

/-- The linear obstruction to equivariance. -/
def equivarianceDifference (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    (V →ₗ[k] W) →ₗ[k] (V →ₗ[k] W ⊗[k] A) :=
  LinearMap.compRight k σ.coaction -
    ((LinearMap.llcomp k V (V ⊗[k] A) (W ⊗[k] A)).flip ρ.coaction).comp
      (LinearMap.rTensorHom A)

/-- Equivariant maps, as a subspace of the space of linear maps. -/
def equivariantHom (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    Submodule k (V →ₗ[k] W) :=
  LinearMap.ker (equivarianceDifference A ρ σ)

/-- Semisimplicity in the splitting formulation: every subcomodule
inclusion has an equivariant retraction. The coaction on the subspace
is characterized by equivariance of the inclusion. -/
def IsSemisimple (ρ : RightComodule k A V) : Prop :=
  ∀ (U : Submodule k V) (τ : RightComodule k A U), IsEquivariant A τ ρ U.subtype →
    ∃ r : V →ₗ[k] U, IsEquivariant A ρ τ r ∧ r.comp U.subtype = LinearMap.id

end LinearAlgebraicGroups.RationalRepresentations

namespace LinearAlgebraicGroups.Specs.RationalBaseChange

open LinearAlgebraicGroups.RationalRepresentations

/-- Scalar extension of a finite dimensional representation over the
scalar-extended coordinate Hopf algebra. -/
def ScalarExtension : Prop :=
  ∀ {k K V : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V),
    ∃ ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V),
      IsScalarExtension A ρ ρK

/-- The canonical comparison on invariant subspaces. Its value on pure
tensors specifies the natural map. -/
def InvariantBaseChange : Prop :=
  ∀ {k K V : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V)),
    IsScalarExtension A ρ ρK →
    ∃ e : K ⊗[k] (invariants A ρ) ≃ₗ[K] invariants (scalarExtension A K) ρK,
      ∀ (a : K) (v : invariants A ρ),
        (e (a ⊗ₜ[k] v) : K ⊗[k] V) = a ⊗ₜ[k] (v : V)

/-- The comparison on equivariant Hom is the scalar extension of the maps,
with scalar multiplication on the extended target. -/
def EquivariantHomBaseChange : Prop :=
  ∀ {k K V W : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (σK : RightComodule K (scalarExtension A K) (K ⊗[k] W)),
    IsScalarExtension A ρ ρK → IsScalarExtension A σ σK →
    ∃ e : K ⊗[k] (equivariantHom A ρ σ) ≃ₗ[K] equivariantHom (scalarExtension A K) ρK σK,
      ∀ (a : K) (f : equivariantHom A ρ σ),
        (e (a ⊗ₜ[k] f) : (K ⊗[k] V) →ₗ[K] (K ⊗[k] W)) =
          a • (f : V →ₗ[k] W).baseChange K

/-- An equivariant retraction of an extended subcomodule inclusion
implies an equivariant retraction over the original field. -/
def RetractionDescent : Prop :=
  ∀ {k K V : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (U : Submodule k V) (τ : RightComodule k A U)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (τK : RightComodule K (scalarExtension A K) (K ⊗[k] U)),
    IsEquivariant A τ ρ U.subtype →
    IsScalarExtension A ρ ρK → IsScalarExtension A τ τK →
    (∃ rK : (K ⊗[k] V) →ₗ[K] (K ⊗[k] U), IsEquivariant (scalarExtension A K) ρK τK rK ∧
      rK.comp (U.subtype.baseChange K) = LinearMap.id) →
    ∃ r : V →ₗ[k] U, IsEquivariant A ρ τ r ∧ r.comp U.subtype = LinearMap.id

/-- Semisimplicity descends along arbitrary field extensions. -/
def SemisimplicityDescent : Prop :=
  ∀ {k K V : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V)),
    IsScalarExtension A ρ ρK → IsSemisimple (scalarExtension A K) ρK → IsSemisimple A ρ


/-- The invariant comparison commutes with every equivariant linear map. -/
def InvariantNaturality : Prop :=
  ∀ {k K V W : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (σK : RightComodule K (scalarExtension A K) (K ⊗[k] W))
    (_ : IsScalarExtension A ρ ρK) (_ : IsScalarExtension A σ σK)
    (f : V →ₗ[k] W) (_ : IsEquivariant A ρ σ f),
    ∃ (m : invariants A ρ →ₗ[k] invariants A σ)
      (mK : invariants (scalarExtension A K) ρK →ₗ[K] invariants (scalarExtension A K) σK),
      (∀ v, (m v : W) = f v) ∧ (∀ v, (mK v : K ⊗[k] W) = f.baseChange K v) ∧
      ∀ (e : K ⊗[k] (invariants A ρ) ≃ₗ[K] invariants (scalarExtension A K) ρK)
        (e' : K ⊗[k] (invariants A σ) ≃ₗ[K] invariants (scalarExtension A K) σK),
        (∀ a v, (e (a ⊗ₜ[k] v) : K ⊗[k] V) = a ⊗ₜ[k] (v : V)) →
        (∀ a w, (e' (a ⊗ₜ[k] w) : K ⊗[k] W) = a ⊗ₜ[k] (w : W)) →
        mK.comp e.toLinearMap = e'.toLinearMap.comp (m.baseChange K)

/-- The equivariant Hom comparison commutes with precomposition in the source
and postcomposition in the target. -/
def EquivariantHomNaturality : Prop :=
  ∀ {k K V W V' W' : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρ' : RightComodule k A V') (σ' : RightComodule k A W')
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (σK : RightComodule K (scalarExtension A K) (K ⊗[k] W))
    (ρK' : RightComodule K (scalarExtension A K) (K ⊗[k] V'))
    (σK' : RightComodule K (scalarExtension A K) (K ⊗[k] W'))
    (_ : IsScalarExtension A ρ ρK) (_ : IsScalarExtension A σ σK)
    (_ : IsScalarExtension A ρ' ρK') (_ : IsScalarExtension A σ' σK')
    (i : V' →ₗ[k] V) (j : W →ₗ[k] W')
    (_ : IsEquivariant A ρ' ρ i) (_ : IsEquivariant A σ σ' j),
    ∃ (m : equivariantHom A ρ σ →ₗ[k] equivariantHom A ρ' σ')
      (mK : equivariantHom (scalarExtension A K) ρK σK →ₗ[K]
        equivariantHom (scalarExtension A K) ρK' σK'),
      (∀ f, (m f : V' →ₗ[k] W') = j.comp ((f : V →ₗ[k] W).comp i)) ∧
      (∀ f, (mK f : (K ⊗[k] V') →ₗ[K] (K ⊗[k] W')) =
        (j.baseChange K).comp ((f : (K ⊗[k] V) →ₗ[K] (K ⊗[k] W)).comp (i.baseChange K))) ∧
      ∀ (e : K ⊗[k] (equivariantHom A ρ σ) ≃ₗ[K] equivariantHom (scalarExtension A K) ρK σK)
        (e' : K ⊗[k] (equivariantHom A ρ' σ') ≃ₗ[K] equivariantHom (scalarExtension A K) ρK' σK'),
        (∀ a f, (e (a ⊗ₜ[k] f) : (K ⊗[k] V) →ₗ[K] (K ⊗[k] W)) =
          a • (f : V →ₗ[k] W).baseChange K) →
        (∀ a f, (e' (a ⊗ₜ[k] f) : (K ⊗[k] V') →ₗ[K] (K ⊗[k] W')) =
          a • (f : V' →ₗ[k] W').baseChange K) →
        mK.comp e.toLinearMap = e'.toLinearMap.comp (m.baseChange K)

end LinearAlgebraicGroups.Specs.RationalBaseChange
