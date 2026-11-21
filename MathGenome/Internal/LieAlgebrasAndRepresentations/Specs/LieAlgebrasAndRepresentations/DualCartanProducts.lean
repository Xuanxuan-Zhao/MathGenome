import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestWeightClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Module.ULift

/-! LA-G08, source lines 3413–3443, with the Chapter 7 conventions.
The Weyl action is the ordinary action on the complex Cartan dual. The
modules and their top vectors are the canonical simple Verma quotients. -/

noncomputable section
open scoped TensorProduct

namespace Specs.LieAlgebrasAndRepresentations.DualCartanProducts

open VermaModules VermaWeightsUniversal SimpleHighestWeightQuotient
open FiniteModuleWeights HighestWeightData IntegrableHighestWeightQuotient
open Module
open SolvableRadical (IsSemisimple_value)
open SerreRelations (simple)

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

local instance {H : LieSubalgebra ℂ L} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {H : LieSubalgebra ℂ L} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

variable [FiniteDimensional ℂ L]

def IsLongest (H : LieSubalgebra ℂ L) (φ : Direction H) (w : weightWeylGroup H) : Prop :=
  w.val '' SerreRelations.positive H φ = Neg.neg '' SerreRelations.positive H φ

/-- The dual is the canonical simple module of weight `-w₀ λ`.
The Weyl element reversing the positive system exists for the chosen Cartan
and direction. The isomorphism assertion applies to any such element. -/
def dual_highest_weight_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    (∃ w : weightWeylGroup H, IsLongest H φ w) ∧
    ∀ (w : weightWeylGroup H), IsLongest H φ w →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
      IsWeightCharacter H φ lam χ → IsDominant H φ lam →
      IsDominant H φ (-w.val lam) ∧
      ∃ ψ : U (borel_value H φ) →ₐ[ℂ] ℂ, IsWeightCharacter H φ (-w.val lam) ψ ∧
        Nonempty (Module.Dual ℂ (simpleQuotient_value H φ χ) ≃ₗ⁅ℂ,L⁆
          simpleQuotient_value H φ ψ)

/-- The tensor of the chosen generators spans the full top weight space,
and its Lie span is the unique submodule isomorphic to `L(λ+μ)`. -/
def cartan_product_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam mu : Module.Dual ℂ H) (χ ψ : U (borel_value H φ) →ₐ[ℂ] ℂ),
      IsWeightCharacter H φ lam χ → IsWeightCharacter H φ mu ψ →
      IsDominant H φ lam → IsDominant H φ mu →
    ∃ ξ : U (borel_value H φ) →ₐ[ℂ] ℂ, IsWeightCharacter H φ (lam + mu) ξ ∧
      let V := simpleQuotient_value H φ χ ⊗[ℂ] simpleQuotient_value H φ ψ
      let x : V := quotientHighestVector H φ χ ⊗ₜ[ℂ] quotientHighestVector H φ ψ
      let K := LieSubmodule.lieSpan ℂ L ({x} : Set V)
      x ≠ 0 ∧ weightSpace_value V H (lam + mu) = ℂ ∙ x ∧
      (∃ i : simpleQuotient_value H φ ξ ≃ₗ⁅ℂ,L⁆ K,
        (i (quotientHighestVector H φ ξ) : V) = x) ∧
      ∀ J : LieSubmodule ℂ L V,
        Nonempty (simpleQuotient_value H φ ξ ≃ₗ⁅ℂ,L⁆ J) ↔ J = K

/-- A Lie module with a specified vector, used for iterated tensor products. -/
structure ModuleWithVector (L : Type u) [LieRing L] [LieAlgebra ℂ L] where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  [lieRingModule : LieRingModule L carrier]
  [lieModule : LieModule ℂ L carrier]
  vector : carrier

attribute [instance] ModuleWithVector.addCommGroup ModuleWithVector.module
  ModuleWithVector.lieRingModule ModuleWithVector.lieModule

namespace ModuleWithVector

/-- The trivial scalar module, lifted to the universe of the factors. -/
def unit (L : Type u) [LieRing L] [LieAlgebra ℂ L] : ModuleWithVector L where
  carrier := TrivialLieModule ℂ L (ULift.{u} ℂ)
  vector := ⟨1⟩

def tensor (A B : ModuleWithVector L) : ModuleWithVector L where
  carrier := A.carrier ⊗[ℂ] B.carrier
  vector := A.vector ⊗ₜ[ℂ] B.vector

def tensorList {ι : Type v} (A : ι → ModuleWithVector L) : List ι → ModuleWithVector L
  | [] => unit L
  | i :: is => tensor (A i) (tensorList A is)

end ModuleWithVector

/-- The empty tensor product is the trivial complex representation,
with the empty pure tensor corresponding to the scalar `1`. -/
def empty_product_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] {ι : Type v} (A : ι → ModuleWithVector L),
    let T := ModuleWithVector.tensorList A []
    ∃ e : T.carrier ≃ₗ⁅ℂ,L⁆ TrivialLieModule ℂ L ℂ,
      (TrivialLieModule.equiv ℂ L ℂ) (e T.vector) = 1

def simpleFactor (H : LieSubalgebra ℂ L) (φ : Direction H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) : ModuleWithVector L where
  carrier := simpleQuotient_value H φ χ
  vector := quotientHighestVector H φ χ

/-- A tensor word has exactly `λ(hᵢ)` occurrences of the fundamental factor
of weight `ωᵢ`, defined using the simple-coroot basis. Its pure tensor of
top vectors generates the asserted simple module. -/
def fundamental_products_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
      IsWeightCharacter H φ lam χ → IsDominant H φ lam →
    ∃ (c : Basis (simple H φ) ℂ H) (ψ : simple H φ → U (borel_value H φ) →ₐ[ℂ] ℂ)
      (word : List (simple H φ)),
      (∀ i, c i = coroots H φ i) ∧
      (∀ i, IsWeightCharacter H φ (c.coord i) (ψ i)) ∧
      (∀ i, lam (coroots H φ i) = (@List.count _ (@instBEqOfDecidableEq _ (Classical.decEq _)) i word : ℂ)) ∧
      (lam = 0 → word = []) ∧
      let T := ModuleWithVector.tensorList (fun i => simpleFactor H φ (ψ i)) word
      let K := LieSubmodule.lieSpan ℂ L ({T.vector} : Set T.carrier)
      T.vector ≠ 0 ∧ weightSpace_value T.carrier H lam = ℂ ∙ T.vector ∧
      ∃ e : simpleQuotient_value H φ χ ≃ₗ⁅ℂ,L⁆ K,
        (e (quotientHighestVector H φ χ) : T.carrier) = T.vector

end Specs.LieAlgebrasAndRepresentations.DualCartanProducts
