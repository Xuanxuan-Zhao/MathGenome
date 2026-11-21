import MathGenome.Internal.Specs.D07.Ch21.CharacterCompletenessCenterClassSumBasis
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.LinearAlgebra.StdBasis

namespace D07.Ch21.CharacterCompletenessCenterClassSumBasis

universe u
noncomputable section
open Specs.D07.Ch21.CharacterCompletenessCenterClassSumBasis

/-- Commuting with every group basis vector is equivalent to being central. -/
theorem central_iff_basis_commutes (G : Type u) [Group G] [Fintype G]
    (a : MonoidAlgebra ℂ G) :
    a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) ↔
      ∀ h : G, MonoidAlgebra.single h 1 * a = a * MonoidAlgebra.single h 1 := by
  classical
  rw [Subalgebra.mem_center_iff]
  constructor
  · exact fun h g => h _
  · intro h b
    have hb := (MonoidAlgebra.basis G ℂ).sum_repr b
    rw [← hb, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    simpa only [MonoidAlgebra.basis_apply, smul_mul_assoc, mul_smul_comm] using
      congrArg (fun x => ((MonoidAlgebra.basis G ℂ).repr b) g • x) (h g)

theorem central_iff_class_constant : CentralIffClassConstant.{u} := by
  intro G _ _ a
  rw [central_iff_basis_commutes]
  constructor
  · intro h x y hxy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    have hc := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff (g * x)) (h g)
    simpa [mul_assoc] using hc
  · intro h g
    ext x
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
      one_mul, mul_one]
    apply h
    apply isConj_iff.mpr
    exact ⟨g, by simp⟩

theorem central_iff_conjugation_fixed : CentralIffConjugationFixed.{u} := by
  intro G _ _ a
  rw [central_iff_basis_commutes]
  constructor
  · intro h g
    rw [h g, mul_assoc, MonoidAlgebra.single_mul_single]
    simp [← MonoidAlgebra.one_def]
  · intro h g
    have hc := congrArg (fun z => z * MonoidAlgebra.single g (1 : ℂ)) (h g)
    simpa [mul_assoc, MonoidAlgebra.single_mul_single, ← MonoidAlgebra.one_def] using hc

theorem class_sum_coefficients : ClassSumCoefficients.{u} := by
  classical
  intro G _ _ c g
  simp only [classSumValue, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single g]
  · split_ifs <;> simp_all
  · intro b _ hbg
    split_ifs <;> simp [MonoidAlgebra.coeff_single, hbg]
  · simp

/-- Assign to a list of class coefficients the corresponding group-algebra element. -/
def classFunctionToAlgebra (G : Type u) [Group G] [Fintype G] :
    (ConjClasses G → ℂ) →ₗ[ℂ] MonoidAlgebra ℂ G where
  toFun f := MonoidAlgebra.ofCoeff
    ((Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm (fun g => f (ConjClasses.mk g)))
  map_add' f k := by ext g; rfl
  map_smul' z f := by ext g; rfl

@[simp] theorem classFunctionToAlgebra_coeff (G : Type u) [Group G] [Fintype G]
    (f : ConjClasses G → ℂ) (g : G) :
    (classFunctionToAlgebra G f).coeff g = f (ConjClasses.mk g) := rfl

/-- Class coefficients always produce central elements. -/
def classFunctionToCenter (G : Type u) [Group G] [Fintype G] :
    (ConjClasses G → ℂ) →ₗ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ G) where
  toFun f := ⟨classFunctionToAlgebra G f,
    (central_iff_class_constant G _).mpr (by
      intro x y hxy
      simp only [classFunctionToAlgebra_coeff,
        ConjClasses.mk_eq_mk_iff_isConj.mpr hxy])⟩
  map_add' f k := Subtype.ext (map_add (classFunctionToAlgebra G) f k)
  map_smul' z f := Subtype.ext (map_smul (classFunctionToAlgebra G) z f)

theorem classFunctionToCenter_bijective (G : Type u) [Group G] [Fintype G] :
    Function.Bijective (classFunctionToCenter G) := by
  constructor
  · intro f k h
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    exact congrArg (fun z : Subalgebra.center ℂ (MonoidAlgebra ℂ G) => z.val.coeff g) h
  · intro z
    let f : ConjClasses G → ℂ := Quotient.lift (fun g => z.val.coeff g)
      (fun x y hxy => (central_iff_class_constant G z.val).mp z.property x y hxy)
    refine ⟨f, ?_⟩
    apply Subtype.ext
    ext g
    rfl

/-- The center is linearly equivalent to arbitrary complex coefficient lists on classes. -/
def classCoefficientsEquiv (G : Type u) [Group G] [Fintype G] :
    (ConjClasses G → ℂ) ≃ₗ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  LinearEquiv.ofBijective (classFunctionToCenter G) (classFunctionToCenter_bijective G)

theorem class_sum_basis : ClassSumBasis.{u} := by
  classical
  intro G _ _
  let b := (Pi.basisFun ℂ (ConjClasses G)).map (classCoefficientsEquiv G)
  refine ⟨b, ?_⟩
  intro c
  ext g
  change (Pi.basisFun ℂ (ConjClasses G) c) (ConjClasses.mk g) = _
  rw [class_sum_coefficients]
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

theorem center_dimension : CenterDimension.{u} := by
  classical
  intro G _ _
  obtain ⟨b, _⟩ := class_sum_basis G
  exact ⟨Module.Finite.of_basis b,
    (Module.finrank_eq_card_basis b).trans (Nat.card_eq_fintype_card.symm)⟩

end
end D07.Ch21.CharacterCompletenessCenterClassSumBasis
