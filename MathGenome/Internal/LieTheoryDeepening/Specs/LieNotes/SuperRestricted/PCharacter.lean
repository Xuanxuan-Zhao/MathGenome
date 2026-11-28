import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.ReducedEnveloping
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.SimpleModule.Basic

/-! The p-character of a finite-dimensional simple ordinary Lie module (SR09). -/

namespace Specs.LieNotes.SuperRestricted.PCharacter

open _root_.Shared.Lie (U inclusion)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping
  (quotientMapValue reducedEnvelopingValue)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

/-- The ordinary enveloping action on a finite-dimensional simple Lie module factors through
exactly one reduced enveloping algebra. -/
def existsUnique_pCharacterType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] [Module.Finite k G]
    (power : restrictedPowerValue k p G)
    {M : Type w} [AddCommGroup M] [Module k M] [LieRingModule G M] [LieModule k G M]
    [Module.Finite k M] [IsSimpleOrder (LieSubmodule k G M)],
    ∃! χ : G →ₗ[k] k,
      ∃ F : reducedEnvelopingValue power χ →ₐ[k] Module.End k M,
        F.comp (quotientMapValue power χ) =
          UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k G M)

/-- A simple module over the reduced enveloping algebra restricts to a finite-dimensional
simple Lie module whose ordinary enveloping action factors exactly at the given character. -/
def simple_restrict_pCharacterType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] [Module.Finite k G]
    (power : restrictedPowerValue k p G) (χ : G →ₗ[k] k),
    let Q := reducedEnvelopingValue power χ
    ∀ {M : Type w} [AddCommGroup M] [Module Q M] [IsSimpleModule Q M],
    letI : Module k M := Module.restrictScalars k Q M
    letI : IsScalarTower k Q M := IsScalarTower.restrictScalars k Q M
    let A : Q →ₐ[k] Module.End k M := Algebra.lsmul k k M
    let ρ : U k G →ₐ[k] Module.End k M := A.comp (quotientMapValue power χ)
    let f : G →ₗ⁅k⁆ Module.End k M := ρ.toLieHom.comp (inclusion k G)
    letI := LieRingModule.compLieHom M f
    letI := LieModule.compLieHom M f
    Module.Finite k M ∧ IsSimpleOrder (LieSubmodule k G M) ∧
      ∀ ψ : G →ₗ[k] k,
        (∃ F : reducedEnvelopingValue power ψ →ₐ[k] Module.End k M,
          F.comp (quotientMapValue power ψ) =
            UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k G M)) ↔ ψ = χ

end Specs.LieNotes.SuperRestricted.PCharacter
