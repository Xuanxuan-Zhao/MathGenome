import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels

/-! Frobenius reciprocity for the shared left balanced tensor.  All vector spaces,
groups and subgroup indices are arbitrary.  The universal-arrow formulation at
the end is the induction-left-adjoint-to-restriction assertion. -/
noncomputable section
universe u v w x y
namespace P103.Ch09
open scoped MonoidAlgebra
variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type x} [AddCommGroup W] [Module k W]

/-- The linear Hom isomorphism, including the formulas in both directions.
`D` carries the scalar and group actions on the shared tensor object. -/
structure FrobeniusData (ρ : Representation k H V) (σ : Representation k G W)
    (D : InductionData H ρ) where
  equivalence : letI := D.module
    D.representation.IntertwiningMap σ ≃ₗ[k] ρ.IntertwiningMap (restrict H σ)
  forward_one : letI := D.module
    ∀ (F : D.representation.IntertwiningMap σ) (z : V),
      equivalence F z = F (tensor H ρ 1 z)
  inverse_tensor : letI := D.module
    ∀ (f : ρ.IntertwiningMap (restrict H σ)) (g : G) (z : V),
      equivalence.symm f (tensor H ρ (MonoidAlgebra.single g 1) z) = σ g (f z)

namespace FrobeniusSpecs

def reciprocityType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (σ : Representation k G W) (D : InductionData H ρ),
    Nonempty (FrobeniusData H ρ σ D)

/-- Contravariant naturality in the inducing representation.  `J` is any
induced intertwiner with the prescribed tensor formula. -/
def naturalityPreType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    {U : Type y} [AddCommGroup U] [Module k U]
    (ρ : Representation k H V) (σ : Representation k G W)
    (τ : Representation k H U) (D : InductionData H ρ) (D' : InductionData H τ)
    (E : FrobeniusData H ρ σ D) (E' : FrobeniusData H τ σ D'),
    letI := D.module
    letI := D'.module
    ∀ (f : τ.IntertwiningMap ρ) (J : D'.representation.IntertwiningMap D.representation),
      (∀ (a : k[G]) (z : U), J (tensor H τ a z) = tensor H ρ a (f z)) →
      ∀ (F : D.representation.IntertwiningMap σ) (z : U),
        E'.equivalence (F.comp J) z = E.equivalence F (f z)

/-- Covariant naturality in the target representation. -/
def naturalityPostType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    {U : Type y} [AddCommGroup U] [Module k U]
    (ρ : Representation k H V) (σ : Representation k G W)
    (τ : Representation k G U) (D : InductionData H ρ)
    (E : FrobeniusData H ρ σ D) (E' : FrobeniusData H ρ τ D),
    letI := D.module
    ∀ (f : σ.IntertwiningMap τ) (F : D.representation.IntertwiningMap σ) (z : V),
      E'.equivalence (f.comp F) z = f (E.equivalence F z)

/-- The universal arrow `z ↦ 1 ⊗ z`: every H-map to a restriction extends
uniquely to a G-map from induction. Together with the natural linear Hom
isomorphisms above, this is the adjunction Ind ⊣ Res. -/
def leftAdjointType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (σ : Representation k G W) (D : InductionData H ρ),
    letI := D.module
    ∀ f : ρ.IntertwiningMap (restrict H σ),
      ∃! F : D.representation.IntertwiningMap σ,
        ∀ z : V, F (tensor H ρ 1 z) = f z

end FrobeniusSpecs
end P103.Ch09
