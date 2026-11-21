import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-! The Harish–Chandra map for the negative–Cartan–positive triangular
ordering, in the conventions of LA-H08 (lines 3891–3967). -/

noncomputable section

open scoped TensorProduct

namespace Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism

open VermaModules RootDecomposition SolvableRadical FiniteModuleWeights
open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

/-- The half-sum of the positive roots, as a complex linear form on the Cartan. -/
def rhoValue : Module.Dual ℂ H :=
  (1 / 2 : ℂ) • ∑ᶠ a : {a : rootSet_value H // 0 < φ a.val}, a.val.val

/-- The canonical generator-preserving map `U(H) → S(H)`.
For a Cartan of a complex semisimple Lie algebra this is the usual identification. -/
def cartanToSymmetric (habel : ∀ a b : H, ⁅a, b⁆ = 0) : U H →ₐ[ℂ] SymmetricAlgebra ℂ H :=
  lift ℂ
    { toLinearMap := SymmetricAlgebra.ι ℂ H
      map_lie' := fun {a b} => by
        change _ = SymmetricAlgebra.ι ℂ H a * SymmetricAlgebra.ι ℂ H b -
          SymmetricAlgebra.ι ℂ H b * SymmetricAlgebra.ι ℂ H a
        rw [mul_comm, sub_self]
        rw [habel]
        exact map_zero (SymmetricAlgebra.ι ℂ H) }

/-- Projection in triangular coordinates by augmentation on the two outer
factors. A monomial survives only when all its factors lie in the Cartan. -/
def tensorProjection (habel : ∀ a b : H, ⁅a, b⁆ = 0) :
    U (negative_value H φ) ⊗[ℂ] (U H ⊗[ℂ] U (positive_value H φ)) →ₗ[ℂ]
      SymmetricAlgebra ℂ H :=
  (TensorProduct.lid ℂ (SymmetricAlgebra ℂ H)).toLinearMap.comp
    (TensorProduct.map (Shared.Lie.augmentation ℂ (negative_value H φ)).toLinearMap
      ((TensorProduct.rid ℂ (SymmetricAlgebra ℂ H)).toLinearMap.comp
        (TensorProduct.map (cartanToSymmetric H habel).toLinearMap
          (Shared.Lie.augmentation ℂ (positive_value H φ)).toLinearMap)))

/-- The PBW projection (p) after (U(H)=S(H)). -/
def projectionValue (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ)) :
    U L →ₗ[ℂ] SymmetricAlgebra ℂ H :=
  (tensorProjection H φ habel).comp
    (LinearEquiv.ofBijective (triangular_value H φ) ht).symm.toLinearMap

/-- Evaluate (S(H)) as polynomials on the space of weights (H^*). -/
def evaluation (η : Module.Dual ℂ H) : SymmetricAlgebra ℂ H →ₐ[ℂ] ℂ :=
  SymmetricAlgebra.lift η

/-- Pullback by the translation sending a weight η to η - δ. -/
def translation (δ : Module.Dual ℂ H) :
    SymmetricAlgebra ℂ H →ₐ[ℂ] SymmetricAlgebra ℂ H :=
  SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ H - (Algebra.linearMap ℂ (SymmetricAlgebra ℂ H)).comp δ)

def shiftedProjection (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ)) :
    U L →ₗ[ℂ] SymmetricAlgebra ℂ H :=
  (translation H (rhoValue H φ)).toLinearMap.comp (projectionValue H φ habel ht)

variable [FiniteDimensional ℂ L]

/-- The ordinary Weyl invariants in the symmetric algebra of the Cartan.
The Weyl group acts on weights by its complex coroot reflections. -/
def weylInvariants : Subalgebra ℂ (SymmetricAlgebra ℂ H) where
  carrier := {p | ∀ w ∈ weightWeylGroup H, ∀ η,
    evaluation H (w η) p = evaluation H η p}
  zero_mem' := by intro w hw η; simp
  one_mem' := by intro w hw η; simp
  add_mem' := by intro p q hp hq w hw η; simp [hp w hw η, hq w hw η]
  mul_mem' := by intro p q hp hq w hw η; simp [hp w hw η, hq w hw η]
  algebraMap_mem' := by intro c w hw η; simp

/-- Type of the half-sum of the positive roots of the chosen system. -/
def rho_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L),
    Direction H → Module.Dual ℂ H

/-- Type of the projection along the negative–Cartan–positive PBW decomposition. -/
def projection_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H),
    (∀ a b : H, ⁅a, b⁆ = 0) → Function.Bijective (triangular_value H φ) →
    U L →ₗ[ℂ] SymmetricAlgebra ℂ H

/-- For an abelian Cartan, the generator-preserving map realizes the
canonical identification used in the PBW projection. -/
def cartan_identification_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] (H : LieSubalgebra ℂ L)
    (habel : ∀ a b : H, ⁅a, b⁆ = 0),
    ∃ e : U H ≃ₐ[ℂ] SymmetricAlgebra ℂ H, e.toAlgHom = cartanToSymmetric H habel

def highest_vector_scalar_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (habel : ∀ a b : H, ⁅a, b⁆ = 0)
      (ht : Function.Bijective (triangular_value H φ))
      (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ∀ z : Subalgebra.center ℂ (U L), ∀ v : induced_value H φ χ,
      z.val • v = evaluation H lam (projectionValue H φ habel ht z.val) • v

/-- Each simple-root hyperplane supports the indicated nonzero singular
vector in the actual Verma module, with its reflected (dot action) weight. -/
def singular_vector_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∀ (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ),
    IsWeightCharacter H φ lam χ →
    ∀ (e f : SerreRelations.simple H φ → L),
    IntegrableHighestWeightQuotient.Normalized H φ e f →
    ∀ (i : SerreRelations.simple H φ) (m : ℕ),
    lam (RootForm.coroot_value H i.val) = (m : ℂ) →
    letI := VermaWeightsUniversal.inducedLieRingModule H φ χ
    let v := (ι ℂ (f i)) ^ (m + 1) • highestVector_value H φ χ
    v ≠ 0 ∧ (∀ j, ⁅e j, v⁆ = 0) ∧
      ∀ h : H, ⁅(h : L), v⁆ = (lam - (m + 1) • i.val) h • v

/-- The isomorphism has its specified shifted PBW value on every central element.
The existence of the triangular inverse and the abelianness of the Cartan are
included so that they need not be supplied as assumptions. -/
def harish_chandra_isomorphism_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    IsSemisimple_value ℂ L → ∀ (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H), Regular H φ →
    ∃ (habel : ∀ a b : H, ⁅a, b⁆ = 0)
      (ht : Function.Bijective (triangular_value H φ))
      (γ : Subalgebra.center ℂ (U L) ≃ₐ[ℂ] weylInvariants H),
      ∀ z, (γ z).val = shiftedProjection H φ habel ht z.val

end Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism
