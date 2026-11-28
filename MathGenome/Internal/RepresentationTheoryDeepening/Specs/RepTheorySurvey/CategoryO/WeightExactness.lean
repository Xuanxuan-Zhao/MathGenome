import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Lie.DirectSum
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Basic.Complex.Basic

/-! Ordinary weight spaces for the Cartan action used in the finite and affine chapters. -/

open scoped DirectSum

namespace RepTheorySurvey.CategoryO.WeightExactness

variable {H : Type*} [LieRing H] [LieAlgebra ℂ H]
variable (X : Type*) [AddCommGroup X] [Module ℂ X] [LieRingModule H X] [LieModule ℂ H X]

/-- The simultaneous eigenspace for a linear functional on the acting Lie algebra.
For a Lie subalgebra of an ambient algebra, use the restricted Lie action. -/
abbrev weightSpace (μ : Module.Dual ℂ H) : Submodule ℂ X :=
  (LieModule.weightSpace X (μ : H → ℂ)).toSubmodule

/-- The canonical sum of ordinary weight spaces is an algebraic internal direct sum. -/
def IsWeightModule : Prop := by
  classical
  exact DirectSum.IsInternal (weightSpace X (H := H))

variable {X} {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [LieRingModule H Y] [LieModule ℂ H Y]

/-- The map induced on an ordinary weight space by an intertwining map. -/
def weightMap (f : X →ₗ⁅ℂ,H⁆ Y) (μ : Module.Dual ℂ H) :
    weightSpace X μ →ₗ[ℂ] weightSpace Y μ :=
  ((f : X →ₗ[ℂ] Y).comp (weightSpace X μ).subtype).codRestrict (weightSpace Y μ)
    (fun x => by
      change f x ∈ LieModule.weightSpace Y (μ : H → ℂ)
      rw [LieModule.mem_weightSpace]
      intro h
      have hx := (LieModule.mem_weightSpace (μ : H → ℂ) (x : X)).mp x.property h
      rw [← f.map_lie, hx, map_smul])

namespace Spec

def stableSubspace : Prop :=
  ∀ {H : Type*} [LieRing H] [LieAlgebra ℂ H]
    {X : Type*} [AddCommGroup X] [Module ℂ X] [LieRingModule H X] [LieModule ℂ H X]
    (S : LieSubmodule ℂ H X), IsWeightModule (H := H) X →
    IsWeightModule (H := H) S ∧
    (∀ μ : Module.Dual ℂ H,
      (weightSpace S μ).map S.toSubmodule.subtype = S.toSubmodule ⊓ weightSpace X μ) ∧
    (⨆ μ : Module.Dual ℂ H, S.toSubmodule ⊓ weightSpace X μ) = S.toSubmodule

def quotient : Prop :=
  ∀ {H : Type*} [LieRing H] [LieAlgebra ℂ H]
    {X : Type*} [AddCommGroup X] [Module ℂ X] [LieRingModule H X] [LieModule ℂ H X]
    (S : LieSubmodule ℂ H X), IsWeightModule (H := H) X →
    IsWeightModule (H := H) (X ⧸ S) ∧
    ∀ μ : Module.Dual ℂ H,
      ∃ e : (weightSpace X μ ⧸ S.toSubmodule.comap (weightSpace X μ).subtype) ≃ₗ[ℂ]
            weightSpace (X ⧸ S) μ,
        ∀ x : weightSpace X μ,
          (e (Submodule.Quotient.mk x) : X ⧸ S) = LieSubmodule.Quotient.mk' S (x : X)

def shortExact : Prop :=
  ∀ {H : Type*} [LieRing H] [LieAlgebra ℂ H]
    {X : Type*} [AddCommGroup X] [Module ℂ X] [LieRingModule H X] [LieModule ℂ H X]
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [LieRingModule H Y] [LieModule ℂ H Y]
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [LieRingModule H Z] [LieModule ℂ H Z]
    (f : X →ₗ⁅ℂ,H⁆ Y) (g : Y →ₗ⁅ℂ,H⁆ Z),
    IsWeightModule (H := H) Y →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    ∀ μ : Module.Dual ℂ H,
      Function.Injective (weightMap f μ) ∧
      Function.Exact (weightMap f μ) (weightMap g μ) ∧
      Function.Surjective (weightMap g μ)

def directSum : Prop :=
  ∀ {H : Type*} [LieRing H] [LieAlgebra ℂ H]
    {ι : Type*} (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, LieRingModule H (V i)] [∀ i, LieModule ℂ H (V i)],
    (∀ i, IsWeightModule (H := H) (V i)) →
    IsWeightModule (H := H) (⨁ i, V i)

/-- The joint weight condition for a left enveloping module under restriction
first along the canonical Lie map and then to a Lie subalgebra. -/
def envelopingWeightSpace : Prop :=
  ∀ {L V : Type*} [LieRing L] [LieAlgebra ℂ L] [AddCommGroup V]
    [Module ℂ V] [Module (UniversalEnvelopingAlgebra ℂ L) V]
    [IsScalarTower ℂ (UniversalEnvelopingAlgebra ℂ L) V]
    (h : LieSubalgebra ℂ L) (μ : Module.Dual ℂ h) (v : V),
    letI : LieRing (UniversalEnvelopingAlgebra ℂ L) := LieRing.ofAssociativeRing
    letI : LieRingModule (UniversalEnvelopingAlgebra ℂ L) V := LieRingModule.ofAssociativeModule
    letI : LieModule ℂ (UniversalEnvelopingAlgebra ℂ L) V := LieModule.ofAssociativeModule
    letI : LieRingModule L V := LieRingModule.compLieHom V (UniversalEnvelopingAlgebra.ι ℂ)
    letI : LieModule ℂ L V := LieModule.compLieHom V (UniversalEnvelopingAlgebra.ι ℂ)
    v ∈ weightSpace V μ ↔
      ∀ a : h, (UniversalEnvelopingAlgebra.ι ℂ (a : L)) • v = μ a • v

end Spec
end RepTheorySurvey.CategoryO.WeightExactness
