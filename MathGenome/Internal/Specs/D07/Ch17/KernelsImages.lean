import MathGenome.Internal.Specs.D07.Ch17.IntertwinersEquivalence
import MathGenome.Internal.Specs.D07.Ch17.SubrepresentationsQuotients
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Independent specification of K07.17.kernels_images (paper.tex:4687–4706).
The field, group and vector spaces are arbitrary; zero spaces and zero maps
are included. The isomorphism is the canonical linear first isomorphism,
with the quotient and restriction actions from the upstream specification.
-/
namespace Specs.D07.Ch17.KernelsImages

universe u v w x

/-- The kernel is invariant under the source representation. -/
def KernelInvariant : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W),
    ρ.IsIntertwiningMap σ T →
      SubrepresentationsQuotients.invariantValue K G V ρ (LinearMap.ker T)

/-- The image is invariant under the target representation. -/
def ImageInvariant : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W),
    ρ.IsIntertwiningMap σ T →
      SubrepresentationsQuotients.invariantValue K G W σ (LinearMap.range T)

/-- The invariance witnesses are conclusions, and the resulting representation
equivalence has precisely the canonical first-isomorphism linear map. The final
formula explicitly identifies its value on every coset representative. -/
def FirstIsomorphismEquivariant : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W),
    ρ.IsIntertwiningMap σ T →
      ∃ (hker : SubrepresentationsQuotients.invariantValue K G V ρ (LinearMap.ker T))
        (himage : SubrepresentationsQuotients.invariantValue K G W σ (LinearMap.range T)),
        ∃ e : (SubrepresentationsQuotients.quotientValue K G V ρ (LinearMap.ker T) hker).Equiv
          (SubrepresentationsQuotients.restrictionValue K G W σ (LinearMap.range T) himage),
          e.toLinearEquiv = T.quotKerEquivRange ∧
            ∀ v, (e ((LinearMap.ker T).mkQ v) : W) = T v

end Specs.D07.Ch17.KernelsImages
