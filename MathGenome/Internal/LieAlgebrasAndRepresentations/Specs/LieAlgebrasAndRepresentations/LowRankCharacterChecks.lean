import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels

noncomputable section

open scoped TensorProduct DirectSum

namespace Specs.LieAlgebrasAndRepresentations.LowRankCharacterChecks

open ClassicalRootsA TypeAHighestWeightModels VermaModules VermaWeightsUniversal
  SimpleHighestWeightQuotient SerreRelations
open RootForm (coroot_value)
open RootDecomposition (rootSet_value)
open IntegrableHighestWeightQuotient (IsDominant)
open SolvableRadical (IsSemisimple_value)

universe u

section RankTwo

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} {φ : Direction H}

/-- The positive roots and simple coroot coordinates of type A₂. -/
structure RankTwoData where
  α₁ : Module.Dual ℂ H
  α₂ : Module.Dual ℂ H
  ω₁ : Module.Dual ℂ H
  ω₂ : Module.Dual ℂ H
  positiveOrder : Fin 3 ≃ positive H φ
  firstRoot : (positiveOrder 0).val = α₁
  secondRoot : (positiveOrder 1).val = α₂
  highestRoot : (positiveOrder 2).val = α₁ + α₂
  simpleRoots : simple H φ = {α₁, α₂}
  highestCoroot : coroot_value H (α₁ + α₂) = coroot_value H α₁ + coroot_value H α₂
  highestWeight : α₁ + α₂ = ω₁ + ω₂
  firstFirst : ω₁ (coroot_value H α₁) = 1
  firstSecond : ω₁ (coroot_value H α₂) = 0
  secondFirst : ω₂ (coroot_value H α₁) = 0
  secondSecond : ω₂ (coroot_value H α₂) = 1

/-- For the chosen Cartan and positive system, a two-vertex type A₂ Cartan
matrix gives the positive-root enumeration and the fundamental weights in
the prescribed order. The two simple coroots determine each weight. -/
def rankTwoDataForPositiveSystemType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (b : Fin 2 ≃ simple H φ),
      (b 1).val (coroot_value H (b 0).val) = -1 →
      (b 0).val (coroot_value H (b 1).val) = -1 →
    ∃ A : RankTwoData (H := H) (φ := φ),
      A.α₁ = (b 0).val ∧ A.α₂ = (b 1).val ∧
      Function.Injective (fun x : Module.Dual ℂ H =>
        (x (coroot_value H A.α₁), x (coroot_value H A.α₂)))

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

/-- The Weyl dimension specialization in A₂ coroot coordinates. -/
def rankTwoDimensionType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (A : RankTwoData (H := H) (φ := φ)) (a b : ℕ),
    let lam := (a : ℂ) • A.ω₁ + (b : ℂ) • A.ω₂
    (∃ χ, IsWeightCharacter H φ lam χ) ∧
    ∀ χ, IsWeightCharacter H φ lam χ →
      FiniteDimensional ℂ (simpleQuotient_value H φ χ) ∧
      (Module.finrank ℂ (simpleQuotient_value H φ χ) : ℂ) =
        ((a : ℂ) + 1) * ((b : ℂ) + 1) * ((a : ℂ) + (b : ℂ) + 2) / 2

/-- Kostant's partition count for a chosen positive system of type A₂. -/
def rankTwoPartitionForPositiveSystemType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H),
    ∀ (A : RankTwoData (H := H) (φ := φ)) (s t : ℕ),
      KostantMultiplicity.partition H φ (s • A.α₁ + t • A.α₂) = min s t + 1

/-- At the highest root of A₂ the simple module is the adjoint, with its
zero-weight space corresponding to the Cartan subalgebra. -/
def rankTwoAdjointForPositiveSystemType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (A : RankTwoData (H := H) (φ := φ)),
    let lam := A.α₁ + A.α₂
    (∃ χ, IsWeightCharacter H φ lam χ) ∧
    ∀ χ, IsWeightCharacter H φ lam χ →
      (∃ e : L ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ χ,
        H.toSubmodule.map e.toLinearEquiv.toLinearMap =
          HighestWeightData.weightSpace_value (simpleQuotient_value H φ χ) H 0) ∧
      FormalCharacters.multiplicity H (simpleQuotient_value H φ χ) 0 = 2 ∧
      Module.finrank ℂ (simpleQuotient_value H φ χ) = 8

end RankTwo

local instance {χ : U (borel_value (cartan 2) (direction 2)) →ₐ[ℂ] ℂ} :
    LieRingModule (sl 2) (induced_value (cartan 2) (direction 2) χ) :=
  inducedLieRingModule (cartan 2) (direction 2) χ

local instance {χ : U (borel_value (cartan 2) (direction 2)) →ₐ[ℂ] ℂ} :
    LieModule ℂ (sl 2) (induced_value (cartan 2) (direction 2) χ) :=
  inducedLieModule (cartan 2) (direction 2) χ

section RankOne

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} {φ : Direction H}

/-- The roots and the simple coroot coordinate of A₁. -/
structure RankOneData where
  ω : Module.Dual ℂ H
  h : H
  positives : positive H φ = {2 • ω}
  roots : rootSet_value H = {2 • ω, -(2 • ω)}
  positiveCoroot : coroot_value H (2 • ω) = h
  negativeCoroot : coroot_value H (-(2 • ω)) = -h
  omegaValue : ω h = 1
  separates : Function.Injective (fun x : Module.Dual ℂ H => x h)

/-- For the chosen Cartan and positive system of type A₁, recover the root
enumeration and the fundamental weight of its unique simple root. -/
def rankOneDataForPositiveSystemType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (b : Fin 1 ≃ simple H φ),
    ∃ A : RankOneData (H := H) (φ := φ), 2 • A.ω = (b 0).val

/-- The double sum in type A₁, where each weight is labelled by its simple coroot coordinate. -/
def rankOneSignedSumType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (φ : Direction H) (A : RankOneData (H := H) (φ := φ))
    (hS : (positive H φ).Finite) (a b c : ℕ),
    SteinbergTensorMultiplicity.signedPartitionSum H φ hS
      ((a : ℂ) • A.ω) ((b : ℂ) • A.ω) ((c : ℂ) • A.ω) =
      if ∃ j : Fin (min a b + 1), c = a + b - 2 * j.val then 1 else 0

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

/-- The Clebsch–Gordan decomposition for the canonical simple quotients of type A₁. -/
def rankOneTensorType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H), Regular H φ →
    ∀ (A : RankOneData (H := H) (φ := φ)) (a b : ℕ),
    ∃ χ : ℕ → U (borel_value H φ) →ₐ[ℂ] ℂ,
      (∀ c : ℕ, IsWeightCharacter H φ ((c : ℂ) • A.ω) (χ c)) ∧
      ∀ ψ ξ, IsWeightCharacter H φ ((a : ℂ) • A.ω) ψ →
        IsWeightCharacter H φ ((b : ℂ) • A.ω) ξ →
        Nonempty ((simpleQuotient_value H φ ψ ⊗[ℂ] simpleQuotient_value H φ ξ) ≃ₗ⁅ℂ,L⁆
          (⨁ j : Fin (min a b + 1), simpleQuotient_value H φ (χ (a + b - 2 * j.val))))

end RankOne

/-- The concrete rank-one decomposition in the symmetric-power realizations. -/
def rankOneMatrixTensorType : Prop :=
  ∀ a b : ℕ, Nonempty ((symmetricPower 1 a ⊗[ℂ] symmetricPower 1 b) ≃ₗ⁅ℂ,sl 1⁆
    (⨁ j : Fin (min a b + 1), symmetricPower 1 (a + b - 2 * j.val)))

def alpha₁ : Module.Dual ℂ (cartan 2) := root 2 0 1
def alpha₂ : Module.Dual ℂ (cartan 2) := root 2 1 2

/-- The A₂ dimension formula, for every realization of the Borel character. -/
def rankTwoMatrixDimensionType : Prop :=
  ∀ a b : ℕ,
    let lam := (a : ℂ) • omega 2 1 + (b : ℂ) • omega 2 2
    (∃ χ, IsWeightCharacter (cartan 2) (direction 2) lam χ) ∧
    ∀ χ, IsWeightCharacter (cartan 2) (direction 2) lam χ →
      FiniteDimensional ℂ (simpleQuotient_value (cartan 2) (direction 2) χ) ∧
      (Module.finrank ℂ (simpleQuotient_value (cartan 2) (direction 2) χ) : ℂ) =
        ((a : ℂ) + 1) * ((b : ℂ) + 1) * ((a : ℂ) + (b : ℂ) + 2) / 2

/-- Kostant's partition function for the chosen A₂ positive system. -/
def rankTwoPartitionType : Prop :=
  ∀ s t : ℕ, KostantMultiplicity.partition (cartan 2) (direction 2)
    (s • alpha₁ + t • alpha₂) = min s t + 1

/-- The zero-weight multiplicity and total dimension at the adjoint highest weight. -/
def rankTwoAdjointType : Prop :=
  (∃ χ, IsWeightCharacter (cartan 2) (direction 2) (alpha₁ + alpha₂) χ) ∧
  ∀ χ, IsWeightCharacter (cartan 2) (direction 2) (alpha₁ + alpha₂) χ →
    FormalCharacters.multiplicity (cartan 2)
      (simpleQuotient_value (cartan 2) (direction 2) χ) 0 = 2 ∧
    Module.finrank ℂ (simpleQuotient_value (cartan 2) (direction 2) χ) = 8

end Specs.LieAlgebrasAndRepresentations.LowRankCharacterChecks
