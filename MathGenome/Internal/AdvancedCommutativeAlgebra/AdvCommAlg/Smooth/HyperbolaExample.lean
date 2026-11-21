import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.StandardPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.LocalJacobianCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.HyperbolaExample
import Mathlib.RingTheory.Ideal.Basis

namespace AdvCommAlg.Smooth.HyperbolaExample
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial TensorProduct
open Specs.AdvCommAlg.Smooth.HyperbolaExample
open Specs.AdvCommAlg.Smooth.LocalJacobianCriterion

variable {A : Type u} [CommRing A]

lemma quotient_aeval (b : A) :
    aeval (coordinate b) = Ideal.Quotient.mkₐ A (Ideal.span {equation b}) := by
  ext i
  simp [coordinate]

/-- The specified global two-variable, one-equation presentation. -/
def presentation (b : A) : Algebra.Presentation A (Hyperbola A b) (Fin 2) (Fin 1) where
  val := coordinate b
  σ' := Function.surjInv Ideal.Quotient.mk_surjective
  aeval_val_σ' x := by
    rw [quotient_aeval]
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective x
  algebra := inferInstance
  algebraMap_eq := by rw [quotient_aeval]; rfl
  relation := fun _ => equation b
  span_range_relation_eq_ker := by
    change Ideal.span (Set.range (fun _ : Fin 1 => equation b)) =
      RingHom.ker (Ideal.Quotient.mk (Ideal.span {equation b}))
    rw [Ideal.mk_ker, Set.range_const]

lemma partial_zero (b : A) : pderiv 0 (equation b) = X 1 := by
  simp [equation]

lemma partial_one (b : A) : pderiv 1 (equation b) = X 0 := by
  simp [equation]

/-- Select the Y derivative when inverting X, or the X derivative when inverting Y. -/
def prePresentation (b : A) (i : Fin 2) :
    Algebra.PreSubmersivePresentation A (Hyperbola A b) (Fin 2) (Fin 1) where
  toPresentation := presentation b
  map := fun _ => if i = 0 then 1 else 0
  map_inj := fun _ _ _ => Subsingleton.elim _ _

lemma pre_jacobian (b : A) (i : Fin 2) :
    (prePresentation b i).jacobian = coordinate b i := by
  rw [selected_minor_jacobian]
  rw [Matrix.det_unique]
  fin_cases i <;>
    simp [Specs.AdvCommAlg.Smooth.selectedMinor,
      Specs.AdvCommAlg.Differentials.presentationJacobian,
      prePresentation, presentation, coordinate, equation]

lemma chart_standard (b : A) (i : Fin 2) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 A
      (Localization.Away (coordinate b i)) := by
  let C := Localization.Away (coordinate b i)
  let Q := (Algebra.PreSubmersivePresentation.localizationAway C (coordinate b i)).comp
    (prePresentation b i)
  have hu : IsUnit (algebraMap (Hyperbola A b) C (coordinate b i)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hj : IsUnit Q.jacobian := by
    dsimp only [Q]
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      pre_jacobian, Algebra.PreSubmersivePresentation.localizationAway_jacobian,
      Algebra.smul_def]
    exact hu.mul hu
  let T : Algebra.SubmersivePresentation A C (Unit ⊕ Fin 2) (Unit ⊕ Fin 1) :=
    { Q with jacobian_isUnit := hj }
  exact T.isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

theorem hyperbola_charts : charts.{u} := by
  intro A _ b
  exact ⟨chart_standard b 0, chart_standard b 1⟩

lemma subtract_constant_mem (p : MvPolynomial (Fin 2) A) :
    p - C (constantCoeff p) ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) A)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    convert Ideal.add_mem _ hp hq using 1
    simp only [map_add]
    ring
  | mul_X p i hp =>
    simpa using Ideal.mul_mem_left (Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) A))) p
      (Ideal.subset_span ⟨i, rfl⟩)

theorem origin_ideal : originIdeal.{u} := by
  intro k _
  apply le_antisymm
  · intro z hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    change aeval (fun _ : Fin 2 => (0 : k)) p = 0 at hz
    have hc : constantCoeff p = 0 := by simpa [aeval_zero'] using hz
    have hp := subtract_constant_mem p
    simp only [hc, map_zero, sub_zero] at hp
    have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {equation (0 : k)})) hp
    rw [Ideal.map_span, ← Set.range_comp] at hm
    exact hm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change originEvaluation k (Ideal.Quotient.mk _ (X i)) = 0
    simp [originEvaluation]

section Origin
variable (k : Type u) [Field k]
local notation "P" => MvPolynomial (Fin 2) k
local notation "B" => Hyperbola k 0

lemma equation_ne_zero : equation (0 : k) ≠ 0 := by
  simp [equation]

/-- The nonzero principal ideal (XY) is free on the displayed equation. -/
def kernelBasis : Module.Basis (Fin 1) P
    (RingHom.ker (algebraMap P B)) :=
  (Ideal.basisSpanSingleton (Module.Basis.singleton (Fin 1) P) (equation_ne_zero k)).map
    (LinearEquiv.ofEq _ _ Ideal.mk_ker.symm)

lemma kernelBasis_apply (j : Fin 1) : kernelBasis k j = relationFamily (0 : k) j := by
  apply Subtype.ext
  simp [kernelBasis, relationFamily]

/-- Localization carries this basis to a basis of I_Q itself. Consequently
its single generator is indispensable even after localization. -/
lemma origin_minimal_relation_at :
    IsMinimalLocalGeneratingFamily
      (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap P B))
      (origin k) (relationFamily (0 : k)) := by
  let h : Function.Surjective (algebraMap P B) := Ideal.Quotient.mk_surjective
  let E := Specs.AdvCommAlg.Differentials.conormalExtension k P B h
  let L := localizedPolynomialExtension h (origin k)
  let e := (localPresentation_kernel_isBaseChange E (origin k)).equiv
  let b := ((kernelBasis k).baseChange L.Ring).map e
  have hb (j : Fin 1) : b j = localizedRelation h (origin k) (relationFamily (0 : k) j) := by
    dsimp only [b]
    erw [Module.Basis.map_apply, Module.Basis.baseChange_apply, kernelBasis_apply]
    exact (IsBaseChange.equiv_tmul _ _ _).trans (one_smul _ _)
  change Submodule.span L.Ring (Set.range
    (fun j => localizedRelation h (origin k) (relationFamily (0 : k) j))) = ⊤ ∧ _
  constructor
  · simpa only [← hb] using b.span_eq
  · intro j
    have he : (Set.univ \ {j} : Set (Fin 1)) = ∅ := by
      ext i
      simp [Subsingleton.elim i j]
    rw [he, Set.image_empty, Submodule.span_empty]
    simpa only [Submodule.mem_bot, ← hb] using b.ne_zero j

lemma residue_coordinate_zero (i : Fin 2) :
    algebraMap P (origin k).asIdeal.ResidueField (X i) = 0 := by
  rw [IsScalarTower.algebraMap_apply P B (origin k).asIdeal.ResidueField]
  apply Ideal.algebraMap_residueField_eq_zero.mpr
  change originEvaluation k (Ideal.Quotient.mk _ (X i)) = 0
  simp [originEvaluation]

lemma origin_jacobian_zero : residueJacobian (origin k) (relationFamily (0 : k)) = 0 := by
  ext i j
  change algebraMap P (origin k).asIdeal.ResidueField
    (pderiv i (equation (0 : k))) = 0
  fin_cases i
  · simpa [equation] using residue_coordinate_zero k 1
  · simpa [equation] using residue_coordinate_zero k 0

lemma origin_not_smooth_at : ¬ Specs.AdvCommAlg.Smooth.isSmoothAtValue k B (origin k) := by
  have : Algebra.FinitePresentation k B := (presentation (0 : k)).finitePresentation_of_isFinite
  have hc := minimal_local_jacobian_criterion k B 2
    (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap P B))
    (origin k) 1 (relationFamily (0 : k)) (origin_minimal_relation_at k)
  intro hs
  have hr := hc.mp hs
  rw [origin_jacobian_zero, Matrix.rank_zero] at hr
  exact Nat.zero_ne_one hr

end Origin

theorem origin_minimal_relation : originMinimalRelation.{u} := by
  intro k _
  exact origin_minimal_relation_at k

theorem origin_not_smooth : originNotSmooth.{u} := by
  intro k _
  exact origin_not_smooth_at k

end
end AdvCommAlg.Smooth.HyperbolaExample
