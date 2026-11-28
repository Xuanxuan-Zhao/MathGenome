import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SimpleReflections
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import Mathlib.Tactic.Ring

/-! Invariance of the Tits form under simple vertex reflections. -/

open scoped BigOperators Matrix

namespace RepTheorySurvey.Quiver.SimpleReflections

open Forms

universe u v r

noncomputable abbrev vertexUnit := @SimpleReflectionsSpec.vertexUnit
noncomputable abbrev simpleReflection := @SimpleReflectionsSpec.simpleReflection

private theorem vertexUnit_dotProduct {Q : Type u} [Fintype Q] {R : Type r} [CommRing R]
    (i : Q) (x : Q → R) :
    vertexUnit R i ⬝ᵥ x = x i := by
  classical
  exact single_one_dotProduct i x

theorem vertexUnit_int : SimpleReflectionsSpec.IntegralVertexUnit.{u} := by
  classical
  intro Q i
  funext j
  simp [SimpleReflectionsSpec.vertexUnit, FormsSpec.unitVector, Pi.single_apply]

section Matrix

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] {R : Type r} [CommRing R]

theorem vertexUnit_squareLength (R : Type r) [CommRing R] (i : Q) :
    vertexUnit R i ⬝ᵥ (polarizationMatrix R *ᵥ vertexUnit R i) = 2 := by
  classical
  rw [vertexUnit_dotProduct]
  change (polarizationMatrix R *ᵥ Pi.single i 1) i = 2
  rw [Matrix.mulVec_single_one]
  exact polarizationMatrix_apply_self R i

theorem simpleReflection_apply (i : Q) (x : Q → R) :
    simpleReflection R i x = x - (vertexUnit R i ⬝ᵥ (polarizationMatrix R *ᵥ x)) • vertexUnit R i := by
  rw [vertexUnit_dotProduct]
  exact Module.reflection_apply x _

theorem simpleReflection_involutive (R : Type r) [CommRing R] (i : Q) :
    Function.Involutive (simpleReflection R i) :=
  Module.involutive_reflection _

theorem simpleReflection_apply_ne {i j : Q} (h : j ≠ i) (x : Q → R) :
    simpleReflection R i x j = x j := by
  classical
  rw [simpleReflection_apply]
  simp [vertexUnit, SimpleReflectionsSpec.vertexUnit, h]

theorem simpleReflection_apply_self (h : ¬ RM03.HasOrientedCycle Q) (i : Q) (x : Q → R) :
    simpleReflection R i x i = -x i + ∑ j, (edgeMultiplicity i j : R) * x j := by
  classical
  have hrow (j : Q) :
      polarizationMatrix R i j * x j =
        (if j = i then 2 * x i else 0) - (edgeMultiplicity i j : R) * x j := by
    by_cases hj : j = i
    · subst j
      simp [edgeMultiplicity_self h]
    · rw [polarizationMatrix_apply_of_ne (Ne.symm hj)]
      simp [hj]
  rw [simpleReflection_apply, vertexUnit_dotProduct]
  simp only [Pi.sub_apply, Pi.smul_apply, vertexUnit, SimpleReflectionsSpec.vertexUnit,
    Pi.single_eq_same, smul_eq_mul, mul_one, Matrix.mulVec, dotProduct, hrow,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private theorem pairing_comm (x y : Q → R) :
    x ⬝ᵥ (polarizationMatrix R *ᵥ y) = y ⬝ᵥ (polarizationMatrix R *ᵥ x) := by
  simpa only [polarizationMatrix, polarizationMatrix_transpose] using
    Matrix.dotProduct_transpose_mulVec (polarizationMatrix R) x y

theorem simpleReflection_preservesPolarization (i : Q) (x y : Q → R) :
    simpleReflection R i x ⬝ᵥ (polarizationMatrix R *ᵥ simpleReflection R i y) =
      x ⬝ᵥ (polarizationMatrix R *ᵥ y) := by
  simp only [simpleReflection_apply, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, vertexUnit_squareLength]
  rw [pairing_comm x (vertexUnit R i)]
  ring

theorem simpleReflection_intCast (i : Q) (x : DimensionVector Q) :
    simpleReflection ℝ i (fun j => (x j : ℝ)) = fun j => (simpleReflection ℤ i x j : ℝ) := by
  classical
  have hmatrix (j : Q) :
      (polarizationMatrix ℤ i j : ℝ) = polarizationMatrix ℝ i j := by
    by_cases hj : i = j
    · subst j
      simp
    · rw [polarizationMatrix_apply_of_ne hj, polarizationMatrix_apply_of_ne hj]
      simp
  have hrow :
      ((polarizationMatrix ℤ *ᵥ x) i : ℝ) =
        (polarizationMatrix ℝ *ᵥ (fun j => (x j : ℝ))) i := by
    simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hmatrix]
  funext j
  by_cases hj : j = i
  · subst j
    simp [simpleReflection_apply, vertexUnit, SimpleReflectionsSpec.vertexUnit, hrow]
  · simp [simpleReflection_apply_ne hj]

end Matrix

section TitsForm

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)]
variable {R : Type r} [CommRing R]

private theorem titsForm_smul_vertexUnit (h : ¬ RM03.HasOrientedCycle Q) (i : Q) (c : R) :
    titsForm (c • vertexUnit R i) = c ^ 2 := by
  classical
  change (∑ j : Q, (c • vertexUnit R i) j * (c • vertexUnit R i) j) -
    (∑ a : RM03.Arrow Q, (c • vertexUnit R i) a.1 * (c • vertexUnit R i) a.2.1) = c ^ 2
  have ha (a : RM03.Arrow Q) : (c • vertexUnit R i) a.1 * (c • vertexUnit R i) a.2.1 = 0 := by
    obtain ⟨j, l, a⟩ := a
    by_cases hj : j = i
    · subst j
      have hl : l ≠ i := fun hl => by
        subst l
        exact (noLoop h i).false a
      simp [Pi.smul_apply, vertexUnit, SimpleReflectionsSpec.vertexUnit, hl]
    · simp [Pi.smul_apply, vertexUnit, SimpleReflectionsSpec.vertexUnit, Pi.single_apply, hj]
  simp only [ha, Finset.sum_const_zero, sub_zero]
  rw [Finset.sum_eq_single i]
  · simp [vertexUnit, SimpleReflectionsSpec.vertexUnit, pow_two]
  · intro j _ hj
    simp [vertexUnit, SimpleReflectionsSpec.vertexUnit, hj]
  · simp

theorem simpleReflection_preservesTitsForm (h : ¬ RM03.HasOrientedCycle Q) (i : Q) (x : Q → R) :
    titsForm (simpleReflection R i x) = titsForm x := by
  set b := vertexUnit R i ⬝ᵥ (polarizationMatrix R *ᵥ x) with hb
  have hp := titsForm_polarization h x ((-b) • vertexUnit R i)
  rw [titsForm_smul_vertexUnit h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    pairing_comm x (vertexUnit R i), ← hb] at hp
  rw [simpleReflection_apply, ← hb, sub_eq_add_neg, ← neg_smul]
  have hcancel : (-b) * b + (-b) ^ 2 = 0 := by ring
  have hdifference := sub_eq_iff_eq_add.mp hp
  rwa [hcancel, sub_eq_zero] at hdifference

end TitsForm

end RepTheorySurvey.Quiver.SimpleReflections
