import MathGenome.Internal.Specs.D07.Ch19.ResultantProductDiscriminant
import MathGenome.Internal.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Field.ZMod

/-! Assembly of K07.19.resultant_product_discriminant. The two prerequisite
modules prove the determinant/root and universal coefficient bridges. Here those
results are exposed together with the derivative-degree correction and its
boundary cases. All resultants keep the descending-row convention of the notes. -/
universe u v
noncomputable section
namespace D07.Ch19.ResultantProductDiscriminant
open Polynomial
open Specs.D07.Ch19.ResultantDefinition
open Specs.D07.Ch19.ResultantProductDiscriminant
open Specs.D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant

theorem padded_root_product : Specs.D07.Ch19.ResultantProductDiscriminant.PaddedRootProduct.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.paddedRootProduct

theorem root_multiplicity_count : Specs.D07.Ch19.ResultantProductDiscriminant.RootMultiplicityCount.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.rootMultiplicityCount

theorem indexed_root_product : Specs.D07.Ch19.ResultantProductDiscriminant.IndexedRootProduct.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.indexedRootProduct

theorem monic_root_product : Specs.D07.Ch19.ResultantProductDiscriminant.MonicRootProduct.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.monicRootProduct

theorem fixed_resultant_scaling : Specs.D07.Ch19.ResultantProductDiscriminant.FixedResultantScaling.{u} :=
  D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.fixedResultantScaling

theorem monic_normalization : Specs.D07.Ch19.ResultantProductDiscriminant.MonicNormalization.{u} :=
  D07.Ch19.ResultantProductDiscriminantPaddedRootProduct.monicNormalization

theorem root_product_equals_discriminant : Specs.D07.Ch19.ResultantProductDiscriminant.RootProductEqualsDiscriminant.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.rootProductEqualsDiscriminant

theorem permutation_invariance : Specs.D07.Ch19.ResultantProductDiscriminant.PermutationInvariance.{u} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.permutationInvariance

theorem numbering_independence : Specs.D07.Ch19.ResultantProductDiscriminant.NumberingIndependence.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.numberingIndependence

theorem vanishing_iff_repeated_entries : Specs.D07.Ch19.ResultantProductDiscriminant.VanishingIffRepeatedEntries.{u} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.vanishingIffRepeatedEntries

theorem vanishing_iff_repeated_root : Specs.D07.Ch19.ResultantProductDiscriminant.VanishingIffRepeatedRoot.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.vanishingIffRepeatedRoot

theorem discriminant_resultant_identity : Specs.D07.Ch19.ResultantProductDiscriminant.DiscriminantResultantIdentity.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.discriminantResultantIdentity

theorem universal_specialization : Specs.D07.Ch19.ResultantProductDiscriminant.UniversalSpecialization.{u} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.universalSpecialization

theorem universal_root_specialization : Specs.D07.Ch19.ResultantProductDiscriminant.UniversalRootSpecialization.{u,v} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.universalRootSpecialization

theorem universal_resultant_division : Specs.D07.Ch19.ResultantProductDiscriminant.UniversalResultantDivision :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.universalResultantDivision

theorem degree_one : Specs.D07.Ch19.ResultantProductDiscriminant.DegreeOne.{u} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.degreeOne

theorem zero_derivative : Specs.D07.Ch19.ResultantProductDiscriminant.ZeroDerivative.{u} :=
  D07.Ch19.ResultantProductDiscriminantUniversalDiscriminant.zeroDerivative

theorem derivative_at_root : DerivativeAtRoot.{u} := by
  intro L _ f n α hs hα i
  exact ResultantProductDiscriminantUniversalDiscriminant.evalDerivativeAtIndex f α hs hα i

theorem derivative_product : DerivativeProduct.{u} := by
  intro L _ f n α hs hα
  exact ResultantProductDiscriminantUniversalDiscriminant.derivativeProduct f α hs hα

theorem coefficient_resultant_identity : CoefficientResultantIdentity.{u} := by
  intro R _ f n hn hp
  exact ResultantProductDiscriminantUniversalDiscriminant.resultantDiscriminant f n hn hp

theorem derivative_padding_adjustment : DerivativePaddingAdjustment.{u} := by
  intro F _ f n hf hn hp
  have hd : f.derivative.natDegree ≤ n-1 := by
    simpa [hn] using Polynomial.natDegree_derivative_le f
  rw [ResultantDefinition.resultantBridge F f f.derivative n (n-1) hn.le hd,
    ordinaryResultant,
    ResultantDefinition.resultantBridge F f f.derivative _ _ le_rfl le_rfl, hn]
  conv_lhs => rw [← Nat.add_sub_of_le hd]
  rw [Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, ← hn]
  rfl

theorem monic_derivative_padding : MonicDerivativePadding.{u} := by
  intro F _ f n hf hn hp
  simpa [hf.leadingCoeff] using derivative_padding_adjustment F f n hf.ne_zero hn hp

theorem monic_coefficient_polynomial : MonicCoefficientPolynomial.{u} := by
  classical
  intro n hp
  let q : Fin (n+1) → MvPolynomial (Fin n) ℤ :=
    fun i => if h : i.val < n then MvPolynomial.X ⟨i.val, h⟩ else 1
  refine ⟨MvPolynomial.bind₁ q (universalDiscriminant n), ?_⟩
  intro R _ f hf hn
  rw [MvPolynomial.eval₂Hom_bind₁]
  have hq : (fun i => MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun j : Fin n => f.coeff j) (q i)) =
      (fun i : Fin (n+1) => f.coeff i) := by
    funext i
    dsimp only [q]
    split_ifs with hi
    · simp
    · have hieq : i.val = n := by omega
      simp only [map_one]
      rw [hieq, ← hn]
      exact hf.leadingCoeff.symm
  rw [hq]
  exact ResultantProductDiscriminantUniversalDiscriminant.universalSpecialization R f n hn

theorem universal_divisibility : UniversalDivisibility := by
  intro n hp
  rw [ResultantProductDiscriminantUniversalDiscriminant.universalResultantDivision n hp]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

theorem universal_leading_zero : UniversalLeadingZero.{u} := by
  intro n hp R _ c hc
  rw [ResultantProductDiscriminantUniversalDiscriminant.universalResultantDivision n hp,
    map_mul, map_mul, MvPolynomial.eval₂Hom_X', hc, mul_zero, zero_mul]

theorem degree_drop_counterexample : DegreeDropCounterexample := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let f : (ZMod 3)[X] := C 2 * X^3 + X^2 + 1
  change f.natDegree = 3 ∧ _
  have hn : f.natDegree = 3 := by
    dsimp [f]
    compute_degree!
  have hf : f ≠ 0 := by
    intro hz
    simp [hz] at hn
  have hd : f.derivative = C 2 * X := by
    simp only [f, derivative_add, derivative_C_mul_X_pow, derivative_X_pow, derivative_one]
    norm_num
    ring_nf
    decide
  have hdn : f.derivative.natDegree = 1 := by
    rw [hd, natDegree_C_mul (by decide : (2 : ZMod 3) ≠ 0), natDegree_X]
  have hl : f.leadingCoeff = 2 := by
    rw [Polynomial.leadingCoeff, hn]
    simp [f, Polynomial.coeff_one]
  have ho : ordinaryResultant f f.derivative = 1 := by
    rw [ordinaryResultant, ResultantDefinition.resultantBridge _ _ _ _ _ le_rfl le_rfl,
      hn, hdn, hd, Polynomial.resultant_C_mul_right]
    have hr := Polynomial.resultant_X_sub_C_right f 3 0 hn.le
    rw [C_0, sub_zero] at hr
    rw [hr]
    norm_num [f]
    decide
  have hp : fixedResultant f f.derivative 3 2 = 2 := by
    rw [derivative_padding_adjustment (ZMod 3) f 3 hf hn (by decide), hdn, ho, hl]
    decide
  have hdisc : f.discr = 2 := by
    have h := coefficient_resultant_identity (ZMod 3) f 3 hn (by decide)
    rw [hp, hl] at h
    norm_num at h
    rw [← neg_mul, show (-2 : ZMod 3) = 1 by decide, one_mul] at h
    exact h.symm
  refine ⟨hn, hdn, hp, ho, ?_⟩
  rw [hdisc, hl, ho]
  have hi : (2 : ZMod 3)⁻¹ = 2 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  rw [hi]
  decide

end D07.Ch19.ResultantProductDiscriminant
