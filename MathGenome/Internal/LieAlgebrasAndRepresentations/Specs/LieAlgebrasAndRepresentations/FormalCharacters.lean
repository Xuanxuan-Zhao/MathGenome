import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacterDefinitions
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightClassification
import Mathlib.Algebra.Lie.TensorProduct

/-! Character identities for LA-H01 in the integral group ring and
the completion of the full complex Cartan dual. -/

noncomputable section

namespace Specs.LieAlgebrasAndRepresentations.FormalCharacters

open Module SerreRelations VermaModules HighestWeightData RootForm FiniteModuleWeights
open scoped BigOperators Classical Pointwise TensorProduct

universe u v w z

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

attribute [local instance 100] LieRing.ofAssociativeRing
open SolvableRadical (IsSemisimple_value)
open SimpleHighestWeightQuotient VermaWeightsUniversal
open IntegrableHighestWeightQuotient (IsDominant)

def bounded_coefficients_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
      (φ : Direction H) (f : Module.Dual ℂ H → ℤ),
    (∃ x : Completion H φ, ∀ a, coeff H φ x a = f a) ↔
      Bounded H φ (fun a => f ((exponent H φ).symm a))

def convolution_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Direction H) (f g : Completion H φ) (η : Module.Dual ℂ H),
    ∃ s : Finset (Module.Dual ℂ H × Module.Dual ℂ H),
      (∀ p, p ∈ s ↔ coeff H φ f p.1 ≠ 0 ∧ coeff H φ g p.2 ≠ 0 ∧ p.1 + p.2 = η) ∧
      coeff H φ (f * g) η = ∑ p ∈ s, coeff H φ f p.1 * coeff H φ g p.2

def finiteCharacter_integral_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] (μ : Module.Dual ℂ H),
      (finiteCharacter H V).coeff μ ≠ 0 → μ ∈ integralWeights H φ

def additivity_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    [FiniteDimensional ℂ W]
    {X : Type z} [AddCommGroup X] [Module ℂ X] [LieRingModule L X] [LieModule ℂ L X]
    [FiniteDimensional ℂ X]
    (f : V →ₗ⁅ℂ,L⁆ W) (g : W →ₗ⁅ℂ,L⁆ X),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      character H φ W = character H φ V + character H φ X

def multiplicativity_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V]
    (W : Type w) [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    [FiniteDimensional ℂ W],
      character H φ (V ⊗[ℂ] W) = character H φ V * character H φ W

def weyl_invariance_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] (w : weightWeylGroup H) (μ : Module.Dual ℂ H),
      (finiteCharacter H V).coeff (w.val μ) = (finiteCharacter H V).coeff μ

/-- Linear independence of the canonical family indexed by the dominant integral weights. -/
def SimpleCharactersIndependent [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
    (χ : {a : Module.Dual ℂ H // IsDominant H φ a} → (U (borel_value H φ) →ₐ[ℂ] ℂ)) :
    Prop :=
  ∃ finite : ∀ a, FiniteDimensional ℂ (simpleQuotient_value H φ (χ a)),
    LinearIndependent ℤ (fun a =>
      letI := inducedLieRingModule H φ (χ a)
      letI := inducedLieModule H φ (χ a)
      letI := finite a
      character H φ (simpleQuotient_value H φ (χ a)))

def independence_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
      (φ : Direction H), Regular H φ →
    ∀ χ : {a : Module.Dual ℂ H // IsDominant H φ a} → (U (borel_value H φ) →ₐ[ℂ] ℂ),
      (∀ a, IsWeightCharacter H φ a.val (χ a)) → SimpleCharactersIndependent H φ χ

def simple_character_family_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
      (φ : Direction H), Regular H φ →
    ∃ χ : {a : Module.Dual ℂ H // IsDominant H φ a} → (U (borel_value H φ) →ₐ[ℂ] ℂ),
      (∀ a, IsWeightCharacter H φ a.val (χ a)) ∧ SimpleCharactersIndependent H φ χ

/-- The actual weight multiplicities of the Verma module are the coefficients of the
product of the inverse denominator factors, shifted by the highest weight. -/
def VermaCharacterFormula (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) : Prop :=
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  ∃ pos : Finset (positive H φ), (∀ a, a ∈ pos) ∧
  ∃ d : positive H φ → (Completion H φ)ˣ,
    (∀ a, (d a).val = 1 - monomial H φ (-a.val)) ∧
    ∀ μ : Module.Dual ℂ H,
      coeff H φ (monomial H φ lam * ∏ a ∈ pos, ((d a)⁻¹).val) μ =
        multiplicity H (induced_value H φ χ) μ

def verma_character_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∀ (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ), IsWeightCharacter H φ lam χ →
      VermaCharacterFormula H φ lam χ

def every_verma_character_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ → ∀ lam : Module.Dual ℂ H,
      ∃! χ : U (borel_value H φ) →ₐ[ℂ] ℂ,
        IsWeightCharacter H φ lam χ ∧ VermaCharacterFormula H φ lam χ

def completion_ext_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H)
    {f g : Completion H φ}, (∀ a, coeff H φ f a = coeff H φ g a) → f = g

def monomial_laws_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H),
    monomial H φ 0 = 1 ∧ ∀ a b, monomial H φ a * monomial H φ b = monomial H φ (a + b)

end Specs.LieAlgebrasAndRepresentations.FormalCharacters
