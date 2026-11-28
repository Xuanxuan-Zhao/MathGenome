import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.EvaluationAndLevel
import Mathlib.LinearAlgebra.Trace

/-! Nonzero finite-dimensional affine modules have scalar level zero, and
evaluation modules with nontrivial action do not extend across the degree line. -/

noncomputable section

open scoped LaurentPolynomial
open LieAlgebra LieModule
open Specs.RepTheorySurvey.Affine.EvaluationAndLevel

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

namespace RepTheorySurvey.Affine

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The Lie evaluation map on the loop-central extension. -/
def evaluation (B : InvariantForm G) (a : ℂˣ) : LoopCentral B →ₗ⁅ℂ⁆ G :=
  evaluation_value B a

@[simp] theorem evaluation_homogeneous (B : InvariantForm G) (a : ℂˣ) (m : ℤ) (x : G) :
    evaluation B a (centralLoopIncl B (loopVector m x)) = (a : ℂ) ^ m • x := by
  change laurentEvaluation a (LaurentPolynomial.T m) • x = _
  rw [show laurentEvaluation a (LaurentPolynomial.T m) =
    LaurentPolynomial.eval₂ (RingHom.id ℂ) a (LaurentPolynomial.T m) from rfl,
    LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val]

@[simp] theorem evaluation_central (B : InvariantForm G) (a : ℂˣ) (k : ℂ) :
    evaluation B a (centralLineIncl B k) = 0 := by
  have hp : (centralExtension B).proj (centralLineIncl B k) = 0 := rfl
  change scalarTensorToLie
    (ExtendScalars.map (laurentEvaluation a) LieHom.id
      (loopAlgebraEquivLaurent ℂ G ((centralExtension B).proj (centralLineIncl B k)))) = 0
  rw [hp, map_zero, map_zero, map_zero]

/-- Pull back the given action along evaluation. -/
def evaluationRepresentation (B : InvariantForm G) (a : ℂˣ)
    (ρ : G →ₗ⁅ℂ⁆ Module.End ℂ M) : LoopCentral B →ₗ⁅ℂ⁆ Module.End ℂ M :=
  ρ.comp (evaluation B a)

section ScalarLevel

variable [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]

/-- The loop-central algebra already forces scalar level zero in finite dimension. -/
theorem loopCentralLevelZero (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (B : InvariantForm G) (hB : B.IsNormalized H)
    {M : Type v} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
    (ρ : LoopCentral B →ₗ⁅ℂ⁆ Module.End ℂ M) (ℓ : ℂ)
    (hℓ : ρ (centralLineIncl B 1) = ℓ • 1) : ℓ = 0 := by
  have : Nontrivial H := cartanNontrivial H
  have : IsLieAbelian H := cartanAbelian H
  obtain ⟨h, hh⟩ := exists_ne (0 : H)
  obtain ⟨h', hp⟩ : ∃ h' : H, B.form (h : G) (h' : G) ≠ 0 := by
    by_contra! hz
    exact hh ((cartanNondegenerate H B hB.1).1 h hz)
  have hcomm : ⁅(h : G), (h' : G)⁆ = 0 :=
    congrArg Subtype.val (trivial_lie_zero H H h h')
  let x := centralLoopIncl B (loopVector 1 (h : G))
  let y := centralLoopIncl B (loopVector (-1) (h' : G))
  have hbr : ⁅x, y⁆ = B.form (h : G) (h' : G) • centralLineIncl B 1 := by
    change ⁅centralLoopIncl B (loopVector 1 (h : G)),
      centralLoopIncl B (loopVector (-1) (h' : G))⁆ = _
    rw [centralBracket, hcomm]
    simp
  have ht : LinearMap.trace ℂ M (ρ (B.form (h : G) (h' : G) • centralLineIncl B 1)) = 0 := by
    rw [← hbr, LieHom.map_lie, LinearMap.trace_lie]
  simp only [map_smul, hℓ, LinearMap.trace_one, smul_eq_mul] at ht
  have hdim : (Module.finrank ℂ M : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos : 0 < Module.finrank ℂ M).ne'
  exact (mul_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left hp)).resolve_right hdim

/-- The same trace obstruction for the full affine algebra, by restriction. -/
theorem affineLevelZero (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]
    (B : InvariantForm G) (hB : B.IsNormalized H)
    {M : Type v} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
    (ρ : AffineAlgebra B →ₗ[ℂ] Module.End ℂ M) (hρ : PreservesAffineBracket B ρ)
    (ℓ : ℂ) (hℓ : ρ (K B) = ℓ • 1) : ℓ = 0 := by
  let σ : AffineAlgebra B →ₗ⁅ℂ⁆ Module.End ℂ M :=
    { ρ with map_lie' := fun {x y} ↦ hρ x y }
  exact loopCentralLevelZero H B hB (σ.comp (centralIncl B)) ℓ hℓ

end ScalarLevel

/-- The degree commutators for homogeneous loops cannot hold on a nontrivial
evaluation representation, even in infinite dimension. -/
theorem evaluationNoDegreeOperator (B : InvariantForm G) (a : ℂˣ)
    (ρ : G →ₗ⁅ℂ⁆ Module.End ℂ M) (hρ : ρ ≠ 0) :
    ¬ ∃ D : Module.End ℂ M, ∀ (m : ℤ) (x : G),
      let X := evaluationRepresentation B a ρ (centralLoopIncl B (loopVector m x))
      ⁅D, X⁆ = (m : ℂ) • X := by
  rintro ⟨D, hD⟩
  have hact (m : ℤ) (x : G) :
      evaluationRepresentation B a ρ (centralLoopIncl B (loopVector m x)) =
        (a : ℂ) ^ m • ρ x := by
    change ρ (evaluation B a (centralLoopIncl B (loopVector m x))) = _
    rw [evaluation_homogeneous, map_smul]
  apply hρ
  apply LieHom.ext
  intro x
  have hzero : ⁅D, ρ x⁆ = 0 := by
    simpa only [hact, zpow_zero, one_smul, Int.cast_zero, zero_smul] using hD 0 x
  have hone : ⁅D, (a : ℂ) • ρ x⁆ = (a : ℂ) • ρ x := by
    simpa only [hact, zpow_one, Int.cast_one, one_smul] using hD 1 x
  rw [lie_smul, hzero, smul_zero] at hone
  exact (smul_eq_zero.mp hone.symm).resolve_left a.ne_zero

/-- A nontrivial evaluation representation has no extension to the full affine algebra. -/
theorem evaluationDoesNotExtend (B : InvariantForm G) (a : ℂˣ)
    (ρ : G →ₗ⁅ℂ⁆ Module.End ℂ M) (hρ : ρ ≠ 0) :
    ¬ ∃ σ : AffineAlgebra B →ₗ[ℂ] Module.End ℂ M, PreservesAffineBracket B σ ∧
      ∀ z : LoopCentral B, σ (centralIncl B z) = evaluationRepresentation B a ρ z := by
  rintro ⟨σ, hσ, hrestrict⟩
  apply evaluationNoDegreeOperator B a ρ hρ
  refine ⟨σ (d B), fun m x ↦ ?_⟩
  have h := hσ (d B) (homogeneous B m x)
  rw [← affineBracket_eq, degreeBracket, map_smul] at h
  have hx := hrestrict (centralLoopIncl B (loopVector m x))
  change σ (homogeneous B m x) = _ at hx
  rw [hx] at h
  exact h.symm

end RepTheorySurvey.Affine
