import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.LoopAlgebra
import Mathlib.Algebra.Lie.OfAssociative

/-! The evaluation maps and the finite-dimensional level and extension statements of LO13. -/

noncomputable section

open scoped TensorProduct LaurentPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

namespace Specs.RepTheorySurvey.Affine.EvaluationAndLevel

open _root_.RepTheorySurvey.Affine
open Specs.RepTheorySurvey.Affine.LoopAlgebra

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

/-- Substitution at a nonzero complex number on the Laurent coefficient algebra. -/
def laurentEvaluation (a : ℂˣ) : ℂ[T;T⁻¹] →ₐ[ℂ] ℂ where
  __ := LaurentPolynomial.eval₂ (RingHom.id ℂ) a
  commutes' r := by
    change LaurentPolynomial.eval₂ (RingHom.id ℂ) a (algebraMap ℂ ℂ[T;T⁻¹] r) = r
    rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C]
    rfl

/-- The scalar action identifies extension of scalars from ℂ to itself with the original algebra. -/
def scalarTensorToLie : ℂ ⊗[ℂ] G →ₗ⁅ℂ⁆ G where
  __ := (TensorProduct.lid ℂ G).toLinearMap
  map_lie' {x y} := by
    let f := (TensorProduct.lid ℂ G).toLinearMap
    change f ⁅x, y⁆ = ⁅f x, f y⁆
    induction x using TensorProduct.inductionOn with
    | tmul c x =>
        induction y using TensorProduct.inductionOn with
        | tmul e y =>
            simp only [LieAlgebra.ExtendScalars.bracket_tmul, f, LinearEquiv.coe_coe,
              TensorProduct.lid_tmul, smul_lie, lie_smul, smul_smul, mul_comm]
        | add y z hy hz =>
            rw [lie_add (c ⊗ₜ[ℂ] x) y z]
            simp only [map_add, hy, hz, lie_add]
    | add x z hx hz => simp only [add_lie, map_add, hx, hz]

/-- Evaluate the loop component and kill the central line. -/
def evaluation_value (B : InvariantForm G) (a : ℂˣ) : LoopCentral B →ₗ⁅ℂ⁆ G :=
  scalarTensorToLie.comp <|
    (LieAlgebra.ExtendScalars.map (laurentEvaluation a) LieHom.id).comp <|
      (LieAlgebra.loopAlgebraEquivLaurent ℂ G).toLieHom.comp (centralExtension_value B).proj

def evaluation_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G),
    ℂˣ → LoopCentral B →ₗ⁅ℂ⁆ G

def evaluation_homogeneous_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (a : ℂˣ) (m : ℤ) (x : G),
    evaluation_value B a (centralLoopIncl_value B (loopVector_value m x)) = (a : ℂ) ^ m • x

def evaluation_central_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] (B : InvariantForm G)
    (a : ℂˣ) (k : ℂ), evaluation_value B a (centralLineIncl_value B k) = 0

variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The action of the loop-central algebra obtained by pulling back a representation of G. -/
def evaluationRepresentation_value (B : InvariantForm G) (a : ℂˣ)
    (ρ : G →ₗ⁅ℂ⁆ Module.End ℂ M) : LoopCentral B →ₗ⁅ℂ⁆ Module.End ℂ M :=
  ρ.comp (evaluation_value B a)

set_option linter.checkUnivs false in
def evaluationRepresentation_type :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {M : Type v} [AddCommGroup M] [Module ℂ M]
    (B : InvariantForm G), ℂˣ →
    (G →ₗ⁅ℂ⁆ Module.End ℂ M) → (LoopCentral B →ₗ⁅ℂ⁆ Module.End ℂ M)

/-- Representations of the affine bracket in the fixed direct-sum coordinates. -/
def PreservesAffineBracket (B : InvariantForm G) (ρ : AffineAlgebra B →ₗ[ℂ] Module.End ℂ M) :
    Prop :=
  ∀ x y, ρ (affineBracket_value B x y) = ⁅ρ x, ρ y⁆

def loopCentralLevelZero_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
    (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra] (B : InvariantForm G), B.IsNormalized H →
    ∀ {M : Type v} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
      (ρ : LoopCentral B →ₗ⁅ℂ⁆ Module.End ℂ M) (ℓ : ℂ),
      ρ (centralLineIncl_value B 1) = ℓ • 1 → ℓ = 0

def affineLevelZero_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
    (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra] (B : InvariantForm G), B.IsNormalized H →
    ∀ {M : Type v} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
      (ρ : AffineAlgebra B →ₗ[ℂ] Module.End ℂ M),
      PreservesAffineBracket B ρ → ∀ ℓ : ℂ, ρ (K_value B) = ℓ • 1 → ℓ = 0

def evaluationNoDegreeOperator_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {M : Type v} [AddCommGroup M] [Module ℂ M]
    (B : InvariantForm G) (a : ℂˣ) (ρ : G →ₗ⁅ℂ⁆ Module.End ℂ M), ρ ≠ 0 →
    ¬ ∃ D : Module.End ℂ M, ∀ (m : ℤ) (x : G),
      let X := evaluationRepresentation_value B a ρ (centralLoopIncl_value B (loopVector_value m x))
      ⁅D, X⁆ = (m : ℂ) • X

def evaluationDoesNotExtend_type : Prop :=
  ∀ {G : Type u} [LieRing G] [LieAlgebra ℂ G] {M : Type v} [AddCommGroup M] [Module ℂ M]
    (B : InvariantForm G) (a : ℂˣ) (ρ : G →ₗ⁅ℂ⁆ Module.End ℂ M), ρ ≠ 0 →
    ¬ ∃ σ : AffineAlgebra B →ₗ[ℂ] Module.End ℂ M, PreservesAffineBracket B σ ∧
      ∀ z : LoopCentral B, σ (centralInclLinear_value B z) = evaluationRepresentation_value B a ρ z

end Specs.RepTheorySurvey.Affine.EvaluationAndLevel
