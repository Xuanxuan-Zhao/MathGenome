import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurWeylCharacter
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SchurAlternant
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.WeylDimension
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
open scoped BigOperators
universe u
namespace AdvancedFiniteGroupRepresentations

abbrev weylDimensionProduct := @Specs.AdvancedFiniteGroupRepresentations.weylDimensionProduct

/-- A polynomial divided difference valid without ordering the exponents. -/
def powerDifferenceQuotient (a b : ℕ) : Polynomial ℂ :=
  (∑ k ∈ Finset.range a, Polynomial.X ^ k) -
    (∑ k ∈ Finset.range b, Polynomial.X ^ k)

theorem powerDifferenceQuotient_mul (a b : ℕ) :
    (Polynomial.X - 1) * powerDifferenceQuotient a b =
      (Polynomial.X : Polynomial ℂ) ^ a - Polynomial.X ^ b := by
  unfold powerDifferenceQuotient
  rw [mul_sub, mul_geom_sum, mul_geom_sum]
  ring

@[simp] theorem powerDifferenceQuotient_eval_one (a b : ℕ) :
    Polynomial.eval 1 (powerDifferenceQuotient a b) = (a : ℂ) - (b : ℂ) := by
  simp [powerDifferenceQuotient]

/-- Principal specialization transposes the determinant into an ordinary
Vandermonde matrix. No nonvanishing of its values is assumed. -/
theorem principal_alternant {d : ℕ} (b : Fin d → ℕ) :
    MvPolynomial.eval₂Hom Polynomial.C
      (fun i : Fin d => (Polynomial.X : Polynomial ℂ) ^ staircase d i)
      (alternant b) =
    ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
      ((Polynomial.X : Polynomial ℂ) ^ b i - Polynomial.X ^ b j) := by
  rw [alternant, Specs.AdvancedFiniteGroupRepresentations.alternant, RingHom.map_det]
  have hm :
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i : Fin d => (Polynomial.X : Polynomial ℂ) ^ staircase d i)).mapMatrix
        (Matrix.of fun i j : Fin d => (MvPolynomial.X i : Alphabet d) ^ b j) =
      (Matrix.of fun i j : Fin d =>
        ((Polynomial.X : Polynomial ℂ) ^ b i) ^ staircase d j).transpose := by
    apply Matrix.ext
    intro i j
    change (MvPolynomial.eval₂Hom Polynomial.C
      (fun i : Fin d => (Polynomial.X : Polynomial ℂ) ^ staircase d i))
      ((MvPolynomial.X i : Alphabet d) ^ b j) =
        ((Polynomial.X : Polynomial ℂ) ^ b j) ^ staircase d i
    rw [map_pow, MvPolynomial.eval₂Hom_X', ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hm, Matrix.det_transpose]
  exact det_staircase_product Polynomial.C _

/-- Cancelling the common vanishing polynomial before evaluating at one
is the algebraic form of the limit in the source proof. -/
theorem schur_at_one_times_staircase {n : ℕ} (p : Partition n) (d : ℕ)
    (hp : length p ≤ d) :
    (∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
      ((staircase d i : ℂ) - (staircase d j : ℂ))) *
      MvPolynomial.eval (fun _ : Fin d => (1 : ℂ)) (schurPolynomial p d) =
    ∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
      ((shiftedPartition d p i : ℂ) - (shiftedPartition d p j : ℂ)) := by
  classical
  let F := MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin d => (Polynomial.X : Polynomial ℂ) ^ staircase d i)
  let C : Polynomial ℂ := ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (Polynomial.X - 1)
  let Q (b : Fin d → ℕ) : Polynomial ℂ :=
    ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, powerDifferenceQuotient (b i) (b j)
  have hf (b : Fin d → ℕ) :
      (∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
        ((Polynomial.X : Polynomial ℂ) ^ b i - Polynomial.X ^ b j)) = C * Q b := by
    simp_rw [← powerDifferenceQuotient_mul]
    simp only [Finset.prod_mul_distrib, C, Q]
  have hC : C ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    simpa using Polynomial.X_sub_C_ne_zero (1 : ℂ)
  have h := congrArg F (schurPolynomial_characterization p d hp)
  rw [map_mul] at h
  change F (alternant (staircase d)) * F (schurPolynomial p d) =
    F (alternant (shiftedPartition d p)) at h
  simp only [F, principal_alternant] at h
  rw [hf, hf, mul_assoc] at h
  have hc := mul_left_cancel₀ hC h
  have he := congrArg (Polynomial.evalRingHom (1 : ℂ)) hc
  have hF : Polynomial.eval 1 (F (schurPolynomial p d)) =
      MvPolynomial.eval (fun _ : Fin d => (1 : ℂ)) (schurPolynomial p d) := by
    change Polynomial.eval 1 (MvPolynomial.eval₂ Polynomial.C _ _) = _
    rw [MvPolynomial.polynomial_eval_eval₂]
    have hh : (Polynomial.evalRingHom (1 : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
      ext c
      simp
    simp only [hh, Polynomial.eval_pow, Polynomial.eval_X, one_pow, MvPolynomial.eval₂_id]
  simp only [map_mul] at he
  change Polynomial.eval 1 (Q (staircase d)) *
    Polynomial.eval 1 (F (schurPolynomial p d)) =
      Polynomial.eval 1 (Q (shiftedPartition d p)) at he
  rw [hF] at he
  simpa only [Q, Polynomial.eval_prod, powerDifferenceQuotient_eval_one] using he

theorem staircase_cast {d : ℕ} (i : Fin d) :
    (staircase d i : ℂ) = (d : ℂ) - 1 - (i.val : ℂ) := by
  have h : staircase d i + 1 + i.val = d := by
    change d - 1 - i.val + 1 + i.val = d
    omega
  have hc := congrArg (fun k : ℕ => (k : ℂ)) h
  simp only [Nat.cast_add, Nat.cast_one] at hc
  linear_combination hc

theorem schur_at_one_weyl_product :
    Specs.AdvancedFiniteGroupRepresentations.schur_at_one_weyl_productType := by
  intro n p d hp
  classical
  have h := schur_at_one_times_staircase p d hp
  have ha (i j : Fin d) :
      ((staircase d i : ℂ) - (staircase d j : ℂ)) =
        (j.val : ℂ) - (i.val : ℂ) := by
    rw [staircase_cast, staircase_cast]
    ring
  have hb (i j : Fin d) :
      ((shiftedPartition d p i : ℂ) - (shiftedPartition d p j : ℂ)) =
        (rowLength p i.val : ℂ) - (rowLength p j.val : ℂ) +
          (j.val : ℂ) - (i.val : ℂ) := by
    change ((rowLength p i.val + staircase d i : ℕ) : ℂ) -
      ((rowLength p j.val + staircase d j : ℕ) : ℂ) = _
    simp only [Nat.cast_add, staircase_cast]
    ring
  simp_rw [ha, hb] at h
  have hn : (∏ i : Fin d, ∏ j ∈ Finset.Ioi i,
      ((j.val : ℂ) - (i.val : ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hijv : i.val < j.val := hij
    exact_mod_cast (ne_of_gt hijv)
  change _ = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, _ / _
  simp only [Finset.prod_div_distrib]
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using h

/-- At the identity the diagonal character is the dimension of the original
Hom-defined multiplicity space. -/
theorem tensorMultiplicity_finrank_eq_schur {V : Type u} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {n : ℕ} (p : Partition n) :
    (Module.finrank ℂ (TensorMultiplicity V p) : ℂ) =
      MvPolynomial.eval (fun _ : Fin (Module.finrank ℂ V) => (1 : ℂ))
        (schurPolynomial p (Module.finrank ℂ V)) := by
  have h := schurWeyl_diagonal_character V p (Module.finBasis ℂ V)
    (fun _ => (1 : ℂ)) (fun _ => one_ne_zero) 1 (by intro i; simp)
  simpa only [tensorMultiplicityOperator_one, LinearMap.trace_one] using h

theorem schurWeyl_dimension_product :
    Specs.AdvancedFiniteGroupRepresentations.schurWeyl_dimension_productType.{u} := by
  intro V _ _ _ n p hp
  rw [tensorMultiplicity_finrank_eq_schur p]
  exact schur_at_one_weyl_product p _ hp

theorem schurWeyl_dimension_length_cutoff :
    Specs.AdvancedFiniteGroupRepresentations.schurWeyl_dimension_length_cutoffType.{u} := by
  intro V _ _ _ n p hp
  have hn : ¬ Nontrivial (TensorMultiplicity V p) := by
    rw [tensorMultiplicity_nonzero_iff V p]
    exact Nat.not_le_of_gt hp
  let : Subsingleton (TensorMultiplicity V p) := not_nontrivial_iff_subsingleton.mp hn
  exact Module.finrank_zero_of_subsingleton

theorem weyl_diagonal_character :
    Specs.AdvancedFiniteGroupRepresentations.weyl_diagonal_characterType.{u} :=
  schurWeyl_diagonal_character

theorem schurWeyl_empty_dimension :
    Specs.AdvancedFiniteGroupRepresentations.schurWeyl_empty_dimensionType.{u} := by
  intro V _ _ _
  obtain ⟨e, _⟩ := tensorMultiplicity_empty_line V
  simpa using e.finrank_eq

theorem weylDimensionProduct_empty :
    Specs.AdvancedFiniteGroupRepresentations.weylDimensionProduct_emptyType := by
  intro d
  change weylDimensionProduct emptyPartition d = 1
  have hp : length emptyPartition ≤ d := by rw [empty_length]; omega
  have h := schur_at_one_weyl_product emptyPartition d hp
  have hs : MvPolynomial.eval (fun _ : Fin d => (1 : ℂ))
      (schurPolynomial emptyPartition d) = 1 := by
    rw [empty_schurPolynomial, map_one]
  exact h.symm.trans hs

theorem weylDimensionProduct_small :
    Specs.AdvancedFiniteGroupRepresentations.weylDimensionProduct_smallType := by
  intro n p d hd
  classical
  change (∏ i : Fin d, ∏ j ∈ Finset.Ioi i, _) = 1
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j hj
  have hij := Finset.mem_Ioi.mp hj
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val < j.val := hij
  omega

end AdvancedFiniteGroupRepresentations
