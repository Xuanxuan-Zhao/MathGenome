import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism

/-! The central-character assertions of LA-H08. -/

noncomputable section

universe u v

namespace Specs.LieAlgebrasAndRepresentations.CentralCharacters

open VermaModules SolvableRadical HarishChandraIsomorphism FiniteModuleWeights

/-- Central characters of Verma modules and their nonzero highest-weight
quotients, with classification by shifted Weyl orbits. -/
def central_characters_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∃ (habel : ∀ a b : H, ⁅a, b⁆ = 0)
      (ht : Function.Bijective (triangular_value H φ))
      (γ : Subalgebra.center ℂ (U L) ≃ₐ[ℂ] weylInvariants H)
      (χ : Module.Dual ℂ H → (Subalgebra.center ℂ (U L) →ₐ[ℂ] ℂ)),
      (∀ z, (γ z).val = shiftedProjection H φ habel ht z.val) ∧
      (∀ lam z, χ lam z = evaluation H (lam + rhoValue H φ) (γ z).val) ∧
      (∀ lam : Module.Dual ℂ H, ∃! ξ, IsWeightCharacter H φ lam ξ) ∧
      (∀ (lam : Module.Dual ℂ H) (ξ : U (borel_value H φ) →ₐ[ℂ] ℂ),
        IsWeightCharacter H φ lam ξ →
        ∀ z, (∀ v : induced_value H φ ξ, z.val • v = χ lam z • v) ∧
          ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] [Module (U L) V]
            [IsScalarTower ℂ (U L) V] [Nontrivial V]
            (q : induced_value H φ ξ →ₗ[U L] V), Function.Surjective q →
            ∀ v : V, z.val • v = χ lam z • v) ∧
      (∀ lam mu, χ lam = χ mu ↔
        ∃ w : weightWeylGroup H, mu + rhoValue H φ = w.val (lam + rhoValue H φ)) ∧
      Function.Surjective χ

end Specs.LieAlgebrasAndRepresentations.CentralCharacters
