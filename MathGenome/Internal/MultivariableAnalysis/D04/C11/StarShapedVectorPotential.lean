import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.StarShapedVectorPotential
import MathGenome.Internal.MultivariableAnalysis.D04.C13.EuclideanPoincareLemma
import MathGenome.Internal.MultivariableAnalysis.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.D04.C11.VectorDifferentialIdentities
import MathGenome.Internal.MultivariableAnalysis.D04.C15.RadialFluxObstruction

noncomputable section
open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.VectorPotential
open D04.Homotopy D04.Dictionary
open Specs.D04.C13.ClosedAndExactForms.Model

abbrev radialVectorPotential :=
  Specs.D04.C11.StarShapedVectorPotential.Model.radialVectorPotential

/-- Inserting x-a first fixes the cross-product order in the primitive. -/
lemma beta_radial_integrand (a x : E 3) (F : E 3 → E 3) (i : Fin 3) :
    homotopyIntegrand a (beta F) x (fun _ => standardBasis 3 i) =
      fun t => t * (euclideanCross (F (a + t • (x-a))) (x-a)) i := by
  funext t
  change t ^ 1 * beta F (a + t • (x-a))
    (Fin.cons (x-a) (fun _ : Fin 1 => standardBasis 3 i)) = _
  have hv : (Fin.cons (x-a) (fun _ : Fin 1 => standardBasis 3 i)) =
      (![x-a, standardBasis 3 i] : Fin 2 → E 3) := by
    funext j
    fin_cases j <;> rfl
  rw [hv, beta_cross, pow_one, inner_coordinates]
  congr 1
  fin_cases i <;>
    simp [euclideanCross,
      Specs.D04.C13.OrientedEuclideanDictionary.Model.euclideanCross,
      cross_apply, standardBasis_apply, Fin.sum_univ_three] <;> ring

lemma homotopy_beta_coefficient (a : E 3) (F : E 3 → E 3) (x : E 3) (i : Fin 3) :
    coefficient (standardBasis 3) (homotopyOperator a (beta F) x)
      (Set.powersetCard.ofSingleton i) = radialVectorPotential a F x i := by
  rw [homotopy_coefficient]
  simp only [indexTuple_singleton]
  rw [beta_radial_integrand]
  rfl

theorem alpha_radialVectorPotential :
    Specs.D04.C11.StarShapedVectorPotential.alpha_radialVectorPotentialType := by
  intro a F
  funext x
  apply (covectorBasis (standardBasis 3) 1).repr.injective
  ext I
  obtain ⟨i, rfl⟩ := (Set.powersetCard.ofSingleton (α := Fin 3)).surjective I
  rw [← coefficient_eq_repr, ← coefficient_eq_repr]
  rw [alpha_coefficient_singleton, homotopy_beta_coefficient]

lemma radialVectorPotential_isCr (U : Set (E 3)) (a : E 3) (F : E 3 → E 3)
    (hU : IsOpen U) (hH : IsCrForm (some 1) U (homotopyOperator a (beta F))) :
    CrOn 1 U (radialVectorPotential a F) := by
  apply (crOn_iff_contDiffOn 1 U _ hU).mpr
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hi := hH.2 (Set.powersetCard.ofSingleton i)
  change CrOn 1 U (fun x => coefficient (standardBasis 3)
    (homotopyOperator a (beta F) x) (Set.powersetCard.ofSingleton i)) at hi
  simp_rw [homotopy_beta_coefficient] at hi
  exact (crOn_iff_contDiffOn 1 U _ hU).mp hi

theorem starShaped_vector_potential :
    Specs.D04.C11.StarShapedVectorPotential.starShaped_vector_potentialType := by
  intro U a F hU ha hstar hF hdiv
  have hβ := beta_isCr 1 U F hU hF
  have hclosed : IsClosedForm U (beta F) := by
    refine ⟨hβ, ?_⟩
    intro x hx
    change exteriorDerivative (beta F) x = 0
    rw [exterior_beta_divergence U F hU hF x hx,
      show divergence F x = 0 from hdiv x hx, zero_smul]
  obtain ⟨hH, hdH, _⟩ := Poincare.poincare_primitive (beta F) hU ha hstar hclosed
  have hA := radialVectorPotential_isCr U a F hU hH
  refine ⟨?_, hA, ?_⟩
  · intro x hx i
    have hi := homotopy_integrable (beta F) hU ha hstar
      (fun I => ((crOn_iff_contDiffOn 1 U _ hU).mp (hβ.2 I)).continuousOn) x hx
      (fun _ => standardBasis 3 i)
    change ScalarIntegrable (homotopyIntegrand a (beta F) x
      (fun _ => standardBasis 3 i)) at hi
    rw [beta_radial_integrand] at hi
    exact hi
  · intro x hx
    apply Eq.symm
    apply curl_identification_unique U (radialVectorPotential a F) hU hA x hx (F x)
    intro v w
    have he : alpha (radialVectorPotential a F) = homotopyOperator a (beta F) :=
      alpha_radialVectorPotential a F
    change EqOn (exteriorDerivative (homotopyOperator a (beta F))) (beta F) U at hdH
    rw [he, hdH hx, beta_cross]

theorem divergence_curl_C2 :
    Specs.D04.C11.StarShapedVectorPotential.divergence_curl_C2Type := by
  intro U A hU hA x hx
  exact D04.divergence_curl U A x hU hA hx

theorem radial_obstruction :
    Specs.D04.C11.StarShapedVectorPotential.radial_obstructionType := by
  refine ⟨RadialFluxObstruction.puncturedSpace_open,
    RadialFluxObstruction.radialField_smooth 1,
    RadialFluxObstruction.divergence_zero,
    RadialFluxObstruction.no_vector_potential, ?_⟩
  rintro ⟨A, hA, hc⟩
  apply RadialFluxObstruction.no_vector_potential
  refine ⟨A, ?_, hc⟩
  apply (crOn_iff_contDiffOn 1 _ _ RadialFluxObstruction.puncturedSpace_open).mpr
  exact ((crOn_iff_contDiffOn 2 _ _ RadialFluxObstruction.puncturedSpace_open).mp hA).of_le
    (by norm_num)

theorem global_vector_potential_may_fail :
    Specs.D04.C11.StarShapedVectorPotential.global_vector_potential_may_failType :=
  ⟨RadialFluxObstruction.puncturedSpace, RadialFluxObstruction.radialField, radial_obstruction⟩

end D04.VectorPotential
