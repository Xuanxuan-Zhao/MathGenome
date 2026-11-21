import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient

/-! LA-G05, Chapter 7, Theorem 7.7. The two modules are the quotients of the
same induced Verma module. The action on weights is ordinary Weyl conjugacy
on the Killing-induced real Cartan dual, carried into the complex dual by
the natural extension. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence

open VermaModules HighestWeightData SerreRelations IntegrableHighestWeightQuotient
open SimpleHighestWeightQuotient RealRootSpace
open SolvableRadical (IsSemisimple_value)

universe u

def finite_highest_weight_existence_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∀ (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ), IsWeightCharacter H φ lam χ →
    ∀ (hd : IsDominant H φ lam) (e f : simple H φ → L), Normalized H φ e f →
    letI := VermaWeightsUniversal.inducedLieRingModule H φ χ
    letI := VermaWeightsUniversal.inducedLieModule H φ χ
    let Q := quotient_value H φ χ hd f
    let W := weightSpace_value Q H
    FiniteDimensional ℂ Q ∧
    (∀ μ, W μ ≠ ⊥ → μ ∈ integralWeights_value (coroots H φ)) ∧
    (∀ d : Realization H,
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      ∀ (w : _root_.LieAlgebrasAndRepresentations.rootWeylGroup (realRoots H)) (x : E H),
        Module.finrank ℂ (W (d.j (w.val x))) = Module.finrank ℂ (W (d.j x))) ∧
    FiniteDimensional ℂ (simpleQuotient_value H φ χ)

end Specs.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
