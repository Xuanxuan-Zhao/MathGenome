import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InductionModels

/-! The projection formula in the shared left balanced-tensor convention.
All tensor products over the field carry the diagonal group action. -/
noncomputable section
universe u v w x y z
namespace P103.Ch09.Projection
open scoped MonoidAlgebra TensorProduct

variable {k : Type u} {G : Type v} [Field k] [Group G]
variable (H : Subgroup G)
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {W : Type x} [AddCommGroup W] [Module k W]

/-- The representation being induced on the left of the projection formula. -/
abbrev diagonal (ρ : Representation k H V) (σ : Representation k G W) :=
  ρ.tprod (restrict H σ)

namespace Specs

/-- Existence of the equivariant isomorphism, with both specified generator
formulas. The induction data specify the actions on the shared tensor objects. -/
def projectionFormulaType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (σ : Representation k G W),
    ∃ (D : InductionData H ρ) (DP : InductionData H (diagonal H ρ σ)),
      letI := D.module
      letI := DP.module
      ∃ e : DP.representation.Equiv (D.representation.tprod σ),
        (∀ (g : G) (v : V) (w : W),
          e (tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] w)) =
            (tensor H ρ (MonoidAlgebra.single g 1) v) ⊗ₜ[k] (σ g w)) ∧
        (∀ (g : G) (v : V) (w : W),
          e.toLinearEquiv.symm ((tensor H ρ (MonoidAlgebra.single g 1) v) ⊗ₜ[k] w) =
            tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] (σ g⁻¹ w)))

/-- Naturality for arbitrary intertwiners in both variables. The maps `F` and
`FP` are the induction maps, characterized by their elementary-tensor formulas;
the upstream functoriality theorem supplies them for all induction data. -/
def naturalityOfFormulasType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    {V' : Type y} [AddCommGroup V'] [Module k V']
    {W' : Type z} [AddCommGroup W'] [Module k W']
    (ρ : Representation k H V) (σ : Representation k G W)
    (ρ' : Representation k H V') (σ' : Representation k G W')
    (D : InductionData H ρ) (DP : InductionData H (diagonal H ρ σ))
    (D' : InductionData H ρ') (DP' : InductionData H (diagonal H ρ' σ')),
    letI := D.module
    letI := DP.module
    letI := D'.module
    letI := DP'.module
    ∀ (e : Induced H (diagonal H ρ σ) ≃ₗ[k] (Induced H ρ ⊗[k] W))
      (e' : Induced H (diagonal H ρ' σ') ≃ₗ[k] (Induced H ρ' ⊗[k] W')),
      (∀ g v w, e (tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] w)) =
        (tensor H ρ (MonoidAlgebra.single g 1) v) ⊗ₜ[k] (σ g w)) →
      (∀ g v w, e' (tensor H (diagonal H ρ' σ') (MonoidAlgebra.single g 1) (v ⊗ₜ[k] w)) =
        (tensor H ρ' (MonoidAlgebra.single g 1) v) ⊗ₜ[k] (σ' g w)) →
      ∀ (f : ρ.IntertwiningMap ρ') (j : σ.IntertwiningMap σ')
        (F : Induced H ρ →ₗ[k] Induced H ρ')
        (FP : Induced H (diagonal H ρ σ) →ₗ[k] Induced H (diagonal H ρ' σ')),
        (∀ a v, F (tensor H ρ a v) = tensor H ρ' a (f v)) →
        (∀ a q, FP (tensor H (diagonal H ρ σ) a q) =
          tensor H (diagonal H ρ' σ') a (TensorProduct.map f.toLinearMap j.toLinearMap q)) →
        ∀ q, e' (FP q) = TensorProduct.map F j.toLinearMap (e q)

/-- The naturality square exists for every pair of intertwiners, using genuine
induced intertwiners with their full elementary-tensor formulas. -/
def projectionNaturalityType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module k V]
    {W : Type x} [AddCommGroup W] [Module k W]
    {V' : Type y} [AddCommGroup V'] [Module k V']
    {W' : Type z} [AddCommGroup W'] [Module k W']
    (ρ : Representation k H V) (σ : Representation k G W)
    (ρ' : Representation k H V') (σ' : Representation k G W')
    (D : InductionData H ρ) (DP : InductionData H (diagonal H ρ σ))
    (D' : InductionData H ρ') (DP' : InductionData H (diagonal H ρ' σ')),
    letI := D.module
    letI := DP.module
    letI := D'.module
    letI := DP'.module
    ∀ (e : Induced H (diagonal H ρ σ) ≃ₗ[k] (Induced H ρ ⊗[k] W))
      (e' : Induced H (diagonal H ρ' σ') ≃ₗ[k] (Induced H ρ' ⊗[k] W')),
      (∀ g v w, e (tensor H (diagonal H ρ σ) (MonoidAlgebra.single g 1) (v ⊗ₜ[k] w)) =
        (tensor H ρ (MonoidAlgebra.single g 1) v) ⊗ₜ[k] (σ g w)) →
      (∀ g v w, e' (tensor H (diagonal H ρ' σ') (MonoidAlgebra.single g 1) (v ⊗ₜ[k] w)) =
        (tensor H ρ' (MonoidAlgebra.single g 1) v) ⊗ₜ[k] (σ' g w)) →
      ∀ (f : ρ.IntertwiningMap ρ') (j : σ.IntertwiningMap σ'),
        ∃ (F : D.representation.IntertwiningMap D'.representation)
          (FP : DP.representation.IntertwiningMap DP'.representation),
          (∀ a v, F (tensor H ρ a v) = tensor H ρ' a (f v)) ∧
          (∀ a q, FP (tensor H (diagonal H ρ σ) a q) =
            tensor H (diagonal H ρ' σ') a (TensorProduct.map f.toLinearMap j.toLinearMap q)) ∧
          (∀ q, e' (FP q) = TensorProduct.map F.toLinearMap j.toLinearMap (e q))

end Specs
end P103.Ch09.Projection
