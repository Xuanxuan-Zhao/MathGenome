import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LaurentLatticeReduction
import Mathlib.Order.Int.LeastGreatest
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped LaurentSeries PowerSeries Polynomial RatFunc
open WithZero HahnSeries Matrix
open scoped BigOperators

set_option maxHeartbeats 600000
open Matrix.GeneralLinearGroup (det_ne_zero)

namespace LinearAlgebraicGroups.Arithmetic.LaurentLattice

noncomputable section

variable {F : Type*} [Field F] {d : ℕ}

@[simp] theorem polePower_zero : polePower F 0 = 1 := by simp [polePower]

@[simp] theorem polePower_mul (n m : ℤ) :
    polePower F n * polePower F m = polePower F (n + m) := by
  simp [polePower, add_comm]

@[simp] theorem valuation_polePower (n : ℤ) :
    baseValuation F (polePower F n) = exp n := by
  simp [polePower, LaurentSeries.valuation_single_zpow]

theorem polePower_ne_zero (n : ℤ) : polePower F n ≠ 0 := by simp [polePower]

@[simp] theorem polynomialEmbedding_C (a : F) :
    polynomialEmbedding F (Polynomial.C a) = HahnSeries.C a := by
  simp [polynomialEmbedding]

@[simp] theorem polynomialEmbedding_X :
    polynomialEmbedding F Polynomial.X = polePower F 1 := by simp [polynomialEmbedding]

private theorem polynomialEmbedding_monomial (n : ℕ) (a : F) :
    polynomialEmbedding F (Polynomial.monomial n a) = HahnSeries.single (-(n : ℤ)) a := by
  simp [polynomialEmbedding, Polynomial.eval₂_monomial, polePower,
    HahnSeries.C_apply]

private theorem coeff_polynomialEmbedding (p : F[X]) (n : ℤ) :
    (polynomialEmbedding F p).coeff n = if n ≤ 0 then p.coeff (-n).toNat else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, HahnSeries.coeff_add', Polynomial.coeff_add]
    split <;> simp_all
  | monomial m a =>
    rw [polynomialEmbedding_monomial, HahnSeries.coeff_single]
    by_cases h : n = -(m : ℤ)
    · subst n
      simp
    · rw [ite_eq_right h]
      by_cases hn : n ≤ 0
      · rw [ite_eq_left hn, Polynomial.coeff_monomial, ite_eq_right]
        omega
      · simp [hn]

theorem polynomialEmbedding_injective : Function.Injective (polynomialEmbedding F) := by
  intro a b h
  ext n
  have hn := congrArg (fun x : F⸨X⸩ => x.coeff (-(n : ℤ))) h
  simpa [coeff_polynomialEmbedding] using hn

theorem polynomial_valuation (p : F[X]) (hp : p ≠ 0) :
    baseValuation F (polynomialEmbedding F p) = exp (p.natDegree : ℤ) := by
  apply le_antisymm
  · rw [← neg_neg (p.natDegree : ℤ), LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
    intro n hn
    simp only [coeff_polynomialEmbedding, ite_eq_left (show n ≤ 0 by omega)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · by_contra! h
    have h' : baseValuation F (polynomialEmbedding F p) ≤ exp ((p.natDegree : ℤ) - 1) := by
      have hv : baseValuation F (polynomialEmbedding F p) ≠ 0 :=
        (map_ne_zero (baseValuation F)).mpr (fun h => hp (polynomialEmbedding_injective (h.trans (map_zero _).symm)))
      rw [← exp_log hv] at h ⊢
      simp only [exp_lt_exp, exp_le_exp] at *
      omega
    have hz := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := F)
      (D := 1 - (p.natDegree : ℤ))).mp (by convert h' using 2; omega)
        (-(p.natDegree : ℤ)) (by omega)
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp) (by simpa [coeff_polynomialEmbedding] using hz)

private theorem polynomial_unit (u : F[X]ˣ) :
    ∃ a : Fˣ, (u : F[X]) = Polynomial.C (a : F) := by
  obtain ⟨a, ha, he⟩ := Polynomial.isUnit_iff.mp u.isUnit
  exact ⟨ha.unit, by simpa using he.symm⟩

private theorem valuation_polynomial_unit (u : F[X]ˣ) :
    baseValuation F (polynomialEmbedding F u) = 1 := by
  obtain ⟨a, ha⟩ := polynomial_unit u
  rw [ha, polynomial_valuation _ (by simp), Polynomial.natDegree_C, Nat.cast_zero, exp_zero]

private theorem det_map_explicit {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Matrix (Fin d) (Fin d) R) : (M.map f).det = f M.det :=
  (f.map_det M).symm

private theorem valuation_integral (p : F⟦X⟧) :
    baseValuation F (HahnSeries.ofPowerSeries ℤ F p) ≤ 1 :=
  (LaurentSeries.val_le_one_iff_eq_coe F _).2 ⟨p, rfl⟩

private theorem valuation_integral_unit (u : F⟦X⟧ˣ) :
    baseValuation F (HahnSeries.ofPowerSeries ℤ F u) = 1 := by
  apply le_antisymm (valuation_integral _)
  have h := valuation_integral (F := F) ((u⁻¹ : F⟦X⟧ˣ) : F⟦X⟧)
  have hm := map_mul (baseValuation F) (HahnSeries.ofPowerSeries ℤ F u)
    (HahnSeries.ofPowerSeries ℤ F (↑(u⁻¹)))
  rw [← map_mul (HahnSeries.ofPowerSeries ℤ F), Units.mul_inv, map_one, map_one] at hm
  calc
    1 = _ := hm
    _ ≤ _ := mul_le_mul_of_nonneg_left h (zero_le)
    _ = _ := mul_one _

private theorem det_basis_valuation (g : SquareGL d F⸨X⸩) (b : SquareGL d F[X]) :
    baseValuation F (basisMatrix g b).val.det = baseValuation F g.val.det := by
  change baseValuation F (g.val * b.val.map (polynomialEmbedding F)).det = _
  rw [Matrix.det_mul, det_map_explicit, map_mul]
  have hb := valuation_polynomial_unit (Matrix.GeneralLinearGroup.det b)
  change baseValuation F (polynomialEmbedding F b.val.det) = 1 at hb
  rw [hb, mul_one]

private theorem valuation_le_column_bound {A : Matrix (Fin d) (Fin d) F⸨X⸩} {n : Fin d → ℤ}
    (h : ∀ i j, baseValuation F (A i j) ≤ exp (n j)) :
    ∃ B : Matrix (Fin d) (Fin d) F⟦X⟧,
      A = B.map (HahnSeries.ofPowerSeries ℤ F) * diagonal (polePower F ∘ n) := by
  have hex (i j : Fin d) : ∃ p : F⟦X⟧,
      HahnSeries.ofPowerSeries ℤ F p = A i j * polePower F (-n j) := by
    apply (LaurentSeries.val_le_one_iff_eq_coe F _).mp
    rw [map_mul, valuation_polePower]
    calc
      _ ≤ exp (n j) * exp (-n j) := mul_le_mul_of_nonneg_right (h i j) (zero_le)
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  choose B hB using hex
  refine ⟨B, ?_⟩
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal]
  change A i j = HahnSeries.ofPowerSeries ℤ F (B i j) * polePower F (n j)
  rw [hB, mul_assoc, polePower_mul, neg_add_cancel, polePower_zero, mul_one]

private theorem det_pole_diagonal (n : Fin d → ℤ) :
    (diagonal (polePower F ∘ n)).det = polePower F (∑ j, n j) := by
  rw [det_diagonal]
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]; simp

private theorem det_diagonal_pole (n : Fin d → ℤ) :
    baseValuation F (diagonal (polePower F ∘ n)).det = exp (∑ j, n j) := by
  rw [det_pole_diagonal, valuation_polePower]

theorem sum_ordered_exponents : exponentSum := by
  intro F _ d g b k n h
  rw [← det_basis_valuation g b, h.2, det_mul, det_map_explicit, map_mul, det_diagonal_pole]
  have hk := valuation_integral_unit (Matrix.GeneralLinearGroup.det k)
  change baseValuation F (HahnSeries.ofPowerSeries ℤ F k.val.det) = 1 at hk
  rw [hk, one_mul]

private theorem valuation_integral_small (p : F⟦X⟧) (h : PowerSeries.constantCoeff p = 0) :
    baseValuation F (HahnSeries.ofPowerSeries ℤ F p) ≤ exp (-1) := by
  apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero F (D := 1)).mpr
  intro n hn
  by_cases h0 : n = 0
  · subst n
    change (HahnSeries.ofPowerSeries ℤ F p).coeff ((0 : ℕ) : ℤ) = 0
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  · exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero F (D := 0)).mp
      (by simpa using valuation_integral p) n (by omega)

private theorem updateUnitColumn {R : Type*} [CommRing R] (j : Fin d) (a : Fin d → R)
    (h : a j = 1) :
    ∃ c : SquareGL d R, c.val = (1 : Matrix (Fin d) (Fin d) R).updateCol j a := by
  have h₁ : (fun k => ∑ i, (a i) • (1 : Matrix (Fin d) (Fin d) R) k i) = a := by
    funext k
    simp [Matrix.one_apply, smul_eq_mul, mul_ite]
  have hd : ((1 : Matrix (Fin d) (Fin d) R).updateCol j a).det = 1 := by
    rw [← h₁, det_updateCol_sum, h, det_one, smul_eq_mul, mul_one]
  exact ⟨((Matrix.isUnit_iff_isUnit_det _).mpr (hd ▸ isUnit_one)).unit, rfl⟩

private theorem lowerColumnDegree (g : SquareGL d F⸨X⸩) (b : SquareGL d F[X])
    (n : Fin d → ℤ) (B : Matrix (Fin d) (Fin d) F⟦X⟧)
    (hB : (basisMatrix g b).val =
      B.map (HahnSeries.ofPowerSeries ℤ F) * diagonal (polePower F ∘ n))
    (hbad : (B.map PowerSeries.constantCoeff).det = 0) :
    ∃ (b' : SquareGL d F[X]) (j : Fin d),
      ∀ i l, baseValuation F ((basisMatrix g b').val i l) ≤
        exp (Function.update n j (n j - 1) l) := by
  classical
  let A := (basisMatrix g b).val
  let M := B.map (PowerSeries.constantCoeff (R := F))
  have hninj : ¬Function.Injective M.mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, show M.det = 0 from hbad]
    simp
  obtain ⟨x, y, hxy, hnxy⟩ := Function.not_injective_iff.mp hninj
  let c := x - y
  have hc : c ≠ 0 := sub_ne_zero.mpr hnxy
  have hMc : M.mulVec c = 0 := by
    rw [show c = x - y from rfl, Matrix.mulVec_sub, hxy, sub_self]
  let s := Finset.univ.filter fun i => c i ≠ 0
  have hs : s.Nonempty := by
    by_contra! h
    apply hc
    funext i
    by_contra hi
    have hm : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simp [h] at hm
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image s n hs
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  let r : Fin d → F := fun l => c l / c j
  let a : Fin d → F[X] := fun l =>
    Polynomial.monomial (n j - n l).toNat (r l)
  have haj : a j = 1 := by simp [a, r, hcj]
  have ha (l : Fin d) : polePower F (n l) * polynomialEmbedding F (a l) =
      HahnSeries.C (r l) * polePower F (n j) := by
    by_cases hl : c l = 0
    · simp [a, r, hl]
    · have hle := hmax l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
      rw [show a l = Polynomial.monomial (n j - n l).toNat (r l) from rfl,
        polynomialEmbedding_monomial]
      simp only [polePower, HahnSeries.C_apply, HahnSeries.single_mul_single, one_mul, mul_one]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
      rw [show -n l + -(n j - n l) = -n j by omega, zero_add]
  obtain ⟨U, hU⟩ := updateUnitColumn j a haj
  let p : Fin d → F⟦X⟧ := B.mulVec (PowerSeries.C ∘ r)
  have hp (i : Fin d) : PowerSeries.constantCoeff (p i) = 0 := by
    rw [show p i = B.mulVec (PowerSeries.C ∘ r) i from rfl, RingHom.map_mulVec]
    change M.mulVec (fun l => PowerSeries.constantCoeff (PowerSeries.C (r l))) i = 0
    simp only [PowerSeries.constantCoeff_C]
    have hr : r = (c j)⁻¹ • c := by
      funext l
      simp [r, div_eq_mul_inv, mul_comm]
    rw [hr, Matrix.mulVec_smul, hMc, smul_zero]
    rfl
  have hrow (i l : Fin d) : A i l =
      HahnSeries.ofPowerSeries ℤ F (B i l) * polePower F (n l) := by
    change (basisMatrix g b).val i l = _
    rw [hB, Matrix.mul_diagonal]
    rfl
  have hval (i : Fin d) : A.mulVec (polynomialEmbedding F ∘ a) i =
      HahnSeries.ofPowerSeries ℤ F (p i) * polePower F (n j) := by
    simp only [Matrix.mulVec, dotProduct, Function.comp_apply, hrow, mul_assoc, ha]
    simp [p, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc, HahnSeries.ofPowerSeries_C]
  refine ⟨b * U, j, ?_⟩
  intro i l
  have heq : (basisMatrix g (b * U)).val =
      A.updateCol j (A.mulVec (polynomialEmbedding F ∘ a)) := by
    have hmap : U.val.map (polynomialEmbedding F) =
        (1 : Matrix (Fin d) (Fin d) F⸨X⸩).updateCol j (polynomialEmbedding F ∘ a) := by
      rw [hU]
      apply Matrix.ext
      intro i l
      by_cases h : l = j <;> simp [Matrix.one_apply, h]
    change g.val * (b.val * U.val).map (polynomialEmbedding F) = _
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← mul_assoc, hmap, Matrix.mul_updateCol, Matrix.mul_one]
    rfl
  rw [heq]
  by_cases hl : l = j
  · subst l
    rw [Function.update_self, Matrix.updateCol_self, hval, map_mul, valuation_polePower]
    calc
      _ ≤ exp (-1) * exp (n j) :=
        mul_le_mul_of_nonneg_right (valuation_integral_small (p i) (hp i)) (zero_le)
      _ = exp (n j - 1) := by rw [← exp_add]; congr 1; omega
  · rw [Function.update_of_ne hl, Matrix.updateCol_ne hl, hrow, map_mul, valuation_polePower]
    exact mul_le_of_le_one_left (zero_le) (valuation_integral _)

private theorem unorderedReduction (g : SquareGL d F⸨X⸩) :
    ∃ (b : SquareGL d F[X]) (k : SquareGL d F⟦X⟧) (n : Fin d → ℤ),
      (basisMatrix g b).val =
        k.val.map (HahnSeries.ofPowerSeries ℤ F) * diagonal (polePower F ∘ n) := by
  classical
  let admissible : ℤ → Prop := fun t => ∃ (b : SquareGL d F[X]) (n : Fin d → ℤ),
    t = ∑ j, n j ∧ ∀ i j, baseValuation F ((basisMatrix g b).val i j) ≤ exp (n j)
  have hlower : ∀ t, admissible t → log (baseValuation F g.val.det) ≤ t := by
    rintro t ⟨b, n, rfl, h⟩
    obtain ⟨B, hB⟩ := valuation_le_column_bound h
    have hd : baseValuation F g.val.det ≠ 0 := (map_ne_zero (baseValuation F)).mpr (det_ne_zero g)
    apply (log_le_iff_le_exp hd).mpr
    rw [← det_basis_valuation g b, hB, det_mul, det_map_explicit, map_mul, det_diagonal_pole]
    exact mul_le_of_le_one_left (zero_le) (valuation_integral _)
  have hcovered (j : Fin d) : ∃ n : ℤ,
      ∀ i, baseValuation F ((basisMatrix g 1).val i j) ≤ exp n := by
    let degree := fun i : Fin d => log (baseValuation F ((basisMatrix g 1).val i j))
    obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d)) degree
      ⟨j, Finset.mem_univ j⟩
    refine ⟨degree i, fun l => ?_⟩
    by_cases h : baseValuation F ((basisMatrix g 1).val l j) = 0
    · rw [h]
      exact zero_le
    · exact (log_le_iff_le_exp h).mp (hmax l (Finset.mem_univ l))
  choose n hn using hcovered
  obtain ⟨t, ⟨b, m, rfl, hm⟩, hmin⟩ := Int.exists_least_of_bdd
    ⟨_, hlower⟩ ⟨∑ j, n j, 1, n, rfl, fun i j => hn j i⟩
  obtain ⟨B, hB⟩ := valuation_le_column_bound hm
  have hunit : IsUnit B.det := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [← det_map_explicit]
    apply isUnit_iff_ne_zero.mpr
    intro hbad
    obtain ⟨b', j, h'⟩ := lowerColumnDegree g b m B hB hbad
    have hle := hmin _ ⟨b', _, rfl, h'⟩
    rw [Finset.sum_update_of_mem (Finset.mem_univ j)] at hle
    simp only [Finset.sdiff_singleton_eq_erase] at hle
    have hj := Finset.add_sum_erase (Finset.univ : Finset (Fin d)) m (Finset.mem_univ j)
    omega
  exact ⟨b, ((Matrix.isUnit_iff_isUnit_det _).mpr hunit).unit, m, hB⟩

private def columnPermutation (R : Type*) [CommRing R] (σ : Equiv.Perm (Fin d)) :
    SquareGL d R where
  val := (σ⁻¹).permMatrix R
  inv := σ.permMatrix R
  val_inv := by rw [← Matrix.permMatrix_mul]; simp
  inv_val := by rw [← Matrix.permMatrix_mul]; simp

private theorem mul_columnPermutation {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin d) (Fin d) S) (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    (A * (columnPermutation R σ).val.map f) i j = A i (σ j) := by
  have hm : (columnPermutation R σ).val.map f = (σ⁻¹).permMatrix S := by
    apply Matrix.ext
    intro i j
    change f (((σ⁻¹).permMatrix R) i j) = _
    simp [PEquiv.toMatrix_apply]
  rw [hm]
  exact congrFun (Matrix.vecMul_permMatrix (σ⁻¹) (v := A i)) j

theorem ordered_basis : orderedReduction := by
  intro F _ d g
  obtain ⟨b, k, n, h⟩ := unorderedReduction g
  let σ := Tuple.sort n
  refine ⟨b * columnPermutation F[X] σ, k * columnPermutation F⟦X⟧ σ,
    n ∘ σ, Tuple.monotone_sort n, ?_⟩
  apply Matrix.ext
  intro i j
  have he : basisMatrix g (b * columnPermutation F[X] σ) =
      basisMatrix g b * Matrix.GeneralLinearGroup.map (polynomialEmbedding F)
        (columnPermutation F[X] σ) := by
    simp only [basisMatrix, map_mul, mul_assoc]
  rw [he, Matrix.mul_diagonal]
  change ((basisMatrix g b).val * (columnPermutation F[X] σ).val.map (polynomialEmbedding F))
    i j = _ * polePower F (n (σ j))
  rw [mul_columnPermutation, h, Matrix.mul_diagonal]
  congr 1
  change HahnSeries.ofPowerSeries ℤ F (k.val i (σ j)) =
    HahnSeries.ofPowerSeries ℤ F ((k.val * (columnPermutation F⟦X⟧ σ).val) i j)
  exact congrArg (HahnSeries.ofPowerSeries ℤ F) <| by
    simpa using (mul_columnPermutation (RingHom.id F⟦X⟧) k.val σ i j).symm

private def diagonalUnits {R : Type*} [CommRing R] (u : Fin d → Rˣ) : SquareGL d R where
  val := Matrix.diagonal fun i => (u i : R)
  inv := Matrix.diagonal fun i => ((u i)⁻¹ : Rˣ).val
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

private def poleUnit (F : Type*) [Field F] (n : ℤ) : F⸨X⸩ˣ where
  val := polePower F n
  inv := polePower F (-n)
  val_inv := by simp
  inv_val := by simp

private theorem inverse_reduced {g : SquareGL d F⸨X⸩} {b : SquareGL d F[X]}
    {k : SquareGL d F⟦X⟧} {n : Fin d → ℤ} (h : Reduced g b k n) :
    ((basisMatrix g b)⁻¹).val =
      diagonal (fun i => polePower F (-n i)) * (k⁻¹).val.map (HahnSeries.ofPowerSeries ℤ F) := by
  let δ := diagonalUnits (fun i => poleUnit F (n i))
  let K := Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F) k
  have h' : basisMatrix g b = K * δ := Units.ext h.2
  rw [h', _root_.mul_inv_rev]
  rfl

private theorem residue_card_gt_one (F : Type*) [Field F] [Finite F] :
    1 < (Nat.card F : ℝ) := by
  exact_mod_cast (Finite.one_lt_card (α := F))

private theorem absoluteValue_of_valuation {F : Type*} [Field F] [Finite F]
    {x : F⸨X⸩} {n : ℤ} (h : baseValuation F x = exp n) :
    absoluteValue F x = (Nat.card F : ℝ) ^ n := by
  simp [absoluteValue, h]

private theorem absoluteValue_le_of_valuation {F : Type*} [Field F] [Finite F]
    {x : F⸨X⸩} {n : ℤ} (h : baseValuation F x ≤ exp n) :
    absoluteValue F x ≤ (Nat.card F : ℝ) ^ n := by
  by_cases hz : baseValuation F x = 0
  · rw [absoluteValue, ite_eq_left hz]
    positivity
  · rw [absoluteValue, ite_eq_right hz]
    exact zpow_le_zpow_right₀ (residue_card_gt_one F).le ((log_le_iff_le_exp hz).mpr h)

theorem sum_zero_iff_determinant_norm_one : exponentSumZero := by
  intro F _ _ d g b k n h
  rw [absoluteValue_of_valuation (sum_ordered_exponents h), ← zpow_zero (Nat.card F : ℝ)]
  exact (zpow_right_strictMono₀ (residue_card_gt_one F)).injective.eq_iff

theorem bounded_ordered_basis : boundedReduction := by
  intro F _ _ d ε hε
  classical
  let q : ℝ := Nat.card F
  have hq : 1 < q := residue_card_gt_one F
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  have hM' : q ^ (-(M : ℤ)) < ε := by simpa [zpow_neg, inv_pow] using hM
  let N := d * M
  refine ⟨N, fun g hg hshort => ?_⟩
  obtain ⟨b, k, n, h⟩ := ordered_basis g
  have hsum := (sum_zero_iff_determinant_norm_one h).1 hg
  have hcolumn (i j : Fin d) :
      baseValuation F ((basisMatrix g b).val i j) ≤ exp (n j) := by
    rw [h.2, Matrix.mul_diagonal]
    change baseValuation F (HahnSeries.ofPowerSeries ℤ F (k.val i j) * polePower F (n j)) ≤ _
    rw [map_mul, valuation_polePower]
    exact mul_le_of_le_one_left zero_le (valuation_integral _)
  have hcoe (j : Fin d) :
      g.val.mulVec (polynomialEmbedding F ∘ (fun i => b.val i j)) =
        fun i => (basisMatrix g b).val i j := by
    funext i
    rfl
  have hb (j : Fin d) : (fun i => b.val i j) ≠ 0 := by
    intro hz
    exact det_ne_zero b (Matrix.det_eq_zero_of_column_eq_zero j (fun i => congrFun hz i))
  have hlower (j : Fin d) : -(M : ℤ) ≤ n j := by
    have hlen : length F (fun i => (basisMatrix g b).val i j) ≤ q ^ (n j) := by
      apply Finset.sup'_le
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · positivity
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
        exact absoluteValue_le_of_valuation (hcolumn i j)
    have hs := hshort _ (hb j)
    rw [hcoe] at hs
    exact (zpow_right_strictMono₀ hq).le_iff_le.mp (hM'.le.trans (hs.trans hlen))
  have hupper (j : Fin d) : n j ≤ (N : ℤ) := by
    have hs : ∑ i ∈ (Finset.univ : Finset (Fin d)).erase j, -(M : ℤ) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin d)).erase j, n i :=
      Finset.sum_le_sum (fun i _ => hlower i)
    have herase := Finset.add_sum_erase (Finset.univ : Finset (Fin d)) n (Finset.mem_univ j)
    rw [hsum] at herase
    rw [Finset.sum_const, nsmul_eq_mul] at hs
    have hcard : ((Finset.univ : Finset (Fin d)).erase j).card ≤ d := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin d)))
    have hmul := Nat.mul_le_mul_right M hcard
    have hmul' : (((Finset.univ : Finset (Fin d)).erase j).card : ℤ) * (M : ℤ) ≤ (N : ℤ) := by
      exact_mod_cast hmul
    linarith
  have habs (j : Fin d) : |n j| ≤ (N : ℤ) := by
    have hd : 1 ≤ d := Nat.succ_le_of_lt (Nat.zero_lt_of_lt j.isLt)
    have hm : M ≤ N := by simpa using Nat.mul_le_mul_right M hd
    have hm' : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hm
    exact abs_le.mpr ⟨by linarith [hlower j], hupper j⟩
  refine ⟨b, k, n, h, hsum, habs, fun i j => ⟨?_, ?_⟩⟩
  · rw [← zpow_natCast]
    exact absoluteValue_le_of_valuation ((hcolumn i j).trans (exp_le_exp.mpr (hupper j)))
  · rw [inverse_reduced h, Matrix.diagonal_mul, ← zpow_natCast]
    apply absoluteValue_le_of_valuation
    change baseValuation F (polePower F (-n i) * HahnSeries.ofPowerSeries ℤ F ((k⁻¹).val i j)) ≤ _
    rw [map_mul, valuation_polePower]
    exact (mul_le_of_le_one_right zero_le (valuation_integral _)).trans
      (exp_le_exp.mpr (by have hi := (abs_le.mp (habs i)).1; omega))

theorem correct_determinant : determinantCorrection := by
  intro F _ d g b k n h u hu
  classical
  by_cases hd : d = 0
  · subst d
    exact ⟨1, k, by simpa using h, Matrix.det_isEmpty, Matrix.det_isEmpty⟩
  have hpos : 0 < d := Nat.pos_of_ne_zero hd
  let j : Fin d := ⟨0, hpos⟩
  obtain ⟨v, hv⟩ := polynomial_unit (Matrix.GeneralLinearGroup.det b)
  change b.val.det = Polynomial.C (v : F) at hv
  let c₀ := (u * v)⁻¹
  let a : Fin d → Fˣ := fun i => if i = j then c₀ else 1
  let c := diagonalUnits a
  let c' := diagonalUnits (fun i => Units.map PowerSeries.C.toMonoidHom (a i))
  have ha : (∏ i, (a i : F)) = (c₀ : F) := by
    rw [Finset.prod_eq_single_of_mem j (Finset.mem_univ j)]
    · simp [a]
    · intro i _ hi
      simp [a, hi]
  have hPoly : (Matrix.GeneralLinearGroup.map Polynomial.C c).val.map (polynomialEmbedding F) =
      diagonal (fun i => HahnSeries.C (a i : F)) := by
    apply Matrix.ext
    intro i l
    change polynomialEmbedding F (Polynomial.C (diagonal (fun k => (a k : F)) i l)) = _
    by_cases hil : i = l <;> simp [hil]
  have hSeries : c'.val.map (HahnSeries.ofPowerSeries ℤ F) =
      diagonal (fun i => HahnSeries.C (a i : F)) := by
    apply Matrix.ext
    intro i l
    change HahnSeries.ofPowerSeries ℤ F (diagonal (fun k => PowerSeries.C (a k : F)) i l) = _
    by_cases hil : i = l <;> simp [hil, HahnSeries.ofPowerSeries_C]
  let b' := b * Matrix.GeneralLinearGroup.map Polynomial.C c
  have hmul : (basisMatrix g b').val =
      (basisMatrix g b).val * diagonal (fun i => HahnSeries.C (a i : F)) := by
    unfold b' basisMatrix
    rw [map_mul, ← mul_assoc]
    exact congrArg (fun B => (basisMatrix g b).val * B) hPoly
  have hr : Reduced g b' (k * c') n := by
    refine ⟨h.1, ?_⟩
    rw [hmul, h.2]
    have hMap : (k * c').val.map (HahnSeries.ofPowerSeries ℤ F) =
        k.val.map (HahnSeries.ofPowerSeries ℤ F) *
          c'.val.map (HahnSeries.ofPowerSeries ℤ F) :=
      map_mul (RingHom.mapMatrix (HahnSeries.ofPowerSeries ℤ F)) k.val c'.val
    rw [hMap, hSeries]
    apply Matrix.ext
    intro i l
    simp only [Matrix.mul_diagonal, Function.comp_apply]
    ac_rfl
  have hd' : (basisMatrix g b').val.det = 1 := by
    have hb : (basisMatrix g b).val.det = HahnSeries.C ((u * v : Fˣ) : F) := by
      change (g.val * b.val.map (polynomialEmbedding F)).det = _
      rw [det_mul, det_map_explicit, hv, polynomialEmbedding_C, hu, ← map_mul]
      rfl
    rw [hmul, det_mul, hb, det_diagonal, ← map_prod, ha, ← map_mul]
    change HahnSeries.C (((u * v : Fˣ) : F) * (↑((u * v : Fˣ)⁻¹) : F)) = 1
    rw [Units.mul_inv, map_one]
  have hsum : (∑ i, n i) = 0 := by
    have he := sum_ordered_exponents hr
    rw [← det_basis_valuation g b', hd', map_one] at he
    exact (exp_le_exp.mp he.ge).antisymm (exp_le_exp.mp he.le)
  refine ⟨c, k * c', hr, hd', ?_⟩
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := F))
  have he := congrArg Matrix.det hr.2
  rw [hd', det_mul, det_map_explicit, det_pole_diagonal, hsum, polePower_zero, mul_one] at he
  rw [map_one]
  exact he.symm


theorem integral_ring : integralIdentification := by
  intro F _ x
  exact LaurentSeries.val_le_one_iff_eq_coe F x

def rationalEmbedding (F : Type*) [Field F] : F⟮X⟯ →+* F⸨X⸩ :=
  RatFunc.liftRingHom (polynomialEmbedding F)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ polynomialEmbedding_injective)

@[simp] theorem rationalEmbedding_polynomial (p : F[X]) :
    rationalEmbedding F (algebraMap F[X] F⟮X⟯ p) = polynomialEmbedding F p := by
  apply RatFunc.liftRingHom_algebraMap

@[simp] theorem rationalEmbedding_X : rationalEmbedding F RatFunc.X = polePower F 1 := by
  rw [← RatFunc.algebraMap_X, rationalEmbedding_polynomial, polynomialEmbedding_X]

open Classical in
private theorem valuation_rationalEmbedding (x : F⟮X⟯) :
    baseValuation F (rationalEmbedding F x) = RatFunc.inftyValuation F x := by
  have hp (p : F[X]) : baseValuation F (polynomialEmbedding F p) =
      RatFunc.inftyValuation F (algebraMap F[X] F⟮X⟯ p) := by
    by_cases hp : p = 0
    · simp [hp]
    · exact (polynomial_valuation p hp).trans (RatFunc.inftyValuation.polynomial F hp).symm
  calc
    _ = baseValuation F (rationalEmbedding F
        (algebraMap F[X] F⟮X⟯ x.num / algebraMap F[X] F⟮X⟯ x.denom)) :=
      congrArg (fun y => baseValuation F (rationalEmbedding F y)) (RatFunc.num_div_denom x).symm
    _ = RatFunc.inftyValuation F
        (algebraMap F[X] F⟮X⟯ x.num / algebraMap F[X] F⟮X⟯ x.denom) := by
      simp only [map_div₀, rationalEmbedding_polynomial, hp]
    _ = _ := congrArg _ (RatFunc.num_div_denom x)

private theorem rationalEmbedding_dense (F : Type*) [Field F] :
    DenseRange (rationalEmbedding F) := by
  refine (LaurentSeries.coe_range_dense (K := F)).mono ?_
  have hX : (HahnSeries.single (1 : ℤ) 1 : F⸨X⸩) ∈ (rationalEmbedding F).range := by
    refine ⟨(RatFunc.X : F⟮X⟯)⁻¹, ?_⟩
    rw [map_inv₀, rationalEmbedding_X, polePower, HahnSeries.inv_single]
    simp
  have hp (p : F[X]) :
      algebraMap F[X] F⸨X⸩ p ∈ (rationalEmbedding F).range := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using (rationalEmbedding F).range.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply (rationalEmbedding F).range.mul_mem
      · refine ⟨algebraMap F[X] F⟮X⟯ (Polynomial.C a), ?_⟩
        rw [rationalEmbedding_polynomial, polynomialEmbedding_C]
        simp
      · apply (rationalEmbedding F).range.pow_mem _ n
        simpa using hX
  rintro _ ⟨x, rfl⟩
  change algebraMap F⟮X⟯ F⸨X⸩ x ∈ (rationalEmbedding F).range
  obtain ⟨a, ha⟩ := hp x.num
  obtain ⟨b, hb⟩ := hp x.denom
  refine ⟨a / b, ?_⟩
  rw [map_div₀, ha, hb]
  rw [IsScalarTower.algebraMap_apply F[X] F⟮X⟯ F⸨X⸩,
    IsScalarTower.algebraMap_apply F[X] F⟮X⟯ F⸨X⸩, ← map_div₀, RatFunc.num_div_denom]

open Filter Uniformity Topology in
private theorem valuation_uniformity {K : Type*} [Field K] [vK : Valued K ℤᵐ⁰]
    (hs : Function.Surjective vK.v) :
    (𝓤 K).HasBasis (fun r : ℤᵐ⁰ => r ≠ 0)
      (fun r => {p : K × K | vK.v (p.2 - p.1) < r}) := by
  apply (Valued.hasBasis_uniformity K ℤᵐ⁰).to_hasBasis
  · intro u _
    let g := MonoidWithZeroHom.ValueGroup₀.embedding (f := (vK.v : K →*₀ ℤᵐ⁰))
    refine ⟨g (u : vK.v.ValueGroup₀), ?_, ?_⟩
    · exact (map_ne_zero g).mpr u.ne_zero
    · intro p hp
      exact (Valuation.restrict_lt_iff_lt_embedding _).2 hp
  · intro r hr
    obtain ⟨x, hx⟩ := hs r
    have hx' : x ≠ 0 := (map_ne_zero vK.v).mp (hx ▸ hr)
    let u := Units.mk0 (vK.v.restrict x) ((map_ne_zero vK.v.restrict).mpr hx')
    refine ⟨u, trivial, ?_⟩
    intro p hp
    have h := (Valuation.restrict_lt_iff_lt_embedding _).mp hp
    simpa [u, Valuation.restrict_def, hx] using h

open Classical in
private theorem infinity_valuation_surjective (F : Type*) [Field F] :
    Function.Surjective (RatFunc.inftyValuation F) := by
  intro a
  by_cases h : a = 0
  · exact ⟨0, by simp [h]⟩
  · exact ⟨RatFunc.X ^ log a, by rw [RatFunc.inftyValuation.X_zpow, exp_log h]⟩

open Classical in
open scoped WithZeroTopology in
set_option maxHeartbeats 1000000 in
theorem completion_at_infinity : completionIdentification := by
  intro F _
  let : Valued F⟮X⟯ ℤᵐ⁰ := RatFunc.inftyValued F
  let f := rationalEmbedding F
  have hval (x : F⟮X⟯) : baseValuation F (f x) = Valued.v x := valuation_rationalEmbedding x
  have hf : IsUniformInducing f := by
    rw [(valuation_uniformity (infinity_valuation_surjective F)).isUniformInducing_iff
      (valuation_uniformity (LaurentSeries.valuation_surjective F))]
    constructor <;> intro i hi <;> refine ⟨i, hi, fun x y h => ?_⟩ <;>
      simpa only [Set.mem_ofPred_eq, ← map_sub f, hval] using h
  let E := UniformSpace.Completion.extensionHom f hf.uniformContinuous.continuous
  have hE : IsUniformInducing E := UniformSpace.Completion.isUniformInducing_extension hf
  have hcoe (x : F⟮X⟯) : E (x : UniformSpace.Completion F⟮X⟯) = f x :=
    UniformSpace.Completion.extensionHom_coe _ _ _
  have hclosed := hE.isComplete_range.isClosed
  have hdense : DenseRange E := (rationalEmbedding_dense F).mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hcoe x⟩)
  have hsurj : Function.Surjective E :=
    Set.range_eq_univ.mp (hclosed.closure_eq ▸ hdense.closure_eq)
  let e := RingEquiv.ofBijective E ⟨hE.injective, hsurj⟩
  refine ⟨e, e.toEquiv.toHomeomorphOfIsInducing hE.isInducing, rfl, ?_, ?_⟩
  · intro p
    change E ((algebraMap F[X] F⟮X⟯ p : F⟮X⟯) : UniformSpace.Completion F⟮X⟯) = _
    rw [hcoe, rationalEmbedding_polynomial]
  · intro x
    change baseValuation F (E x) = (RatFunc.inftyValued F).extensionValuation x
    have hsurj' : Function.Surjective (Valued.v (R := UniformSpace.Completion F⟮X⟯)
        (Γ₀ := ℤᵐ⁰)) := by
      intro a
      obtain ⟨y, hy⟩ := infinity_valuation_surjective F a
      refine ⟨(y : UniformSpace.Completion F⟮X⟯), ?_⟩
      change (RatFunc.inftyValued F).extensionValuation (y : UniformSpace.Completion F⟮X⟯) = a
      rw [Valued.extensionValuation_apply_coe]
      exact hy
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_eq
        ((Valued.continuous_valuation_of_surjective (LaurentSeries.valuation_surjective F)).comp
          hE.uniformContinuous.continuous)
        (Valued.continuous_valuation_of_surjective hsurj')
    · intro y
      rw [hcoe, hval, Valued.extensionValuation_apply_coe]

private theorem valuation_lt_one_iff (x : F⸨X⸩) :
    baseValuation F x < 1 ↔ ∀ n : ℤ, n ≤ 0 → x.coeff n = 0 := by
  have h : baseValuation F x < 1 ↔ baseValuation F x ≤ exp (-1) := by
    by_cases hz : baseValuation F x = 0
    · simp [hz]
    · rw [← exp_log hz, ← exp_zero, exp_lt_exp, exp_le_exp]
      omega
  rw [h, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero F (D := 1)]
  exact forall_congr' fun n => by rw [show n < 1 ↔ n ≤ 0 by omega]

private theorem exists_polynomial_part (x : F⸨X⸩) :
    ∃ p : F[X], x - polynomialEmbedding F p ∈ positivePart F := by
  classical
  let N := (-x.order).toNat + 1
  let p : F[X] := ∑ k ∈ Finset.range N, Polynomial.monomial k (x.coeff (-(k : ℤ)))
  refine ⟨p, (valuation_lt_one_iff _).2 ?_⟩
  intro m hm
  rw [HahnSeries.coeff_sub, coeff_polynomialEmbedding, ite_eq_left hm]
  let j := (-m).toNat
  have hj : -(j : ℤ) = m := by dsimp [j]; omega
  change x.coeff m - p.coeff j = 0
  have hc : p.coeff j = if j < N then x.coeff (-(j : ℤ)) else 0 := by
    simp [p, Polynomial.coeff_monomial, Finset.sum_ite_eq']
  rw [hc, hj]
  by_cases h : j < N
  · simp [h]
  · rw [ite_eq_right h, sub_zero]
    apply HahnSeries.coeff_eq_zero_of_lt_order
    dsimp [j, N] at h
    omega

theorem polynomial_part : polynomialPartDecomposition := by
  intro F _ d x
  choose a ha using fun i => exists_polynomial_part (x i)
  refine ⟨a, ha, ?_⟩
  intro b hb
  funext i
  by_contra hne
  have ha' : baseValuation F (x i - polynomialEmbedding F (a i)) < 1 := ha i
  have hb' : baseValuation F (x i - polynomialEmbedding F (b i)) < 1 := hb i
  have h : baseValuation F (polynomialEmbedding F (b i - a i)) < 1 := by
    rw [map_sub, show polynomialEmbedding F (b i) - polynomialEmbedding F (a i) =
      (x i - polynomialEmbedding F (a i)) - (x i - polynomialEmbedding F (b i)) by abel]
    exact ((baseValuation F).map_sub _ _).trans_lt (max_lt ha' hb')
  rw [polynomial_valuation _ (sub_ne_zero.mpr hne), ← exp_zero, exp_lt_exp] at h
  omega

private def valuationBall (F : Type*) [Field F] (m : ℤ) : Set F⸨X⸩ :=
  {x | baseValuation F x < exp m}

private theorem valuationBall_coeff (m : ℤ) (x : F⸨X⸩) :
    x ∈ valuationBall F m ↔ ∀ j : ℤ, j ≤ -m → x.coeff j = 0 := by
  change baseValuation F x < exp m ↔ _
  have h : baseValuation F x < exp m ↔ baseValuation F x ≤ exp (m - 1) := by
    by_cases hz : baseValuation F x = 0
    · simp [hz]
    · rw [← exp_log hz, exp_lt_exp, exp_le_exp]
      omega
  rw [h, show m - 1 = -(1 - m) by omega, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero F]
  exact forall_congr' fun j => by rw [show j < 1 - m ↔ j ≤ -m by omega]

private theorem valuationBall_open (m : ℤ) : IsOpen (valuationBall F m) := by
  obtain ⟨x, hx⟩ := LaurentSeries.valuation_surjective F (exp m)
  rw [show valuationBall F m = {y : F⸨X⸩ | (baseValuation F).restrict y <
        (baseValuation F).restrict x} by
    ext y
    change baseValuation F y < exp m ↔
      (baseValuation F).restrict y < (baseValuation F).restrict x
    rw [Valuation.restrict_lt_iff, hx]]
  exact Valued.isOpen_ball _ _

private theorem valuationBall_image (m : ℤ) :
    valuationBall F m = (fun x => polePower F m * x) '' positivePart F := by
  ext x
  constructor
  · intro hx
    refine ⟨polePower F (-m) * x, ?_, ?_⟩
    · change baseValuation F (polePower F (-m) * x) < 1
      rw [map_mul, valuation_polePower]
      calc
        _ < exp (-m) * exp m := mul_lt_mul_of_pos_left hx exp_pos
        _ = _ := by rw [← exp_add, neg_add_cancel, exp_zero]
    · change polePower F m * (polePower F (-m) * x) = x
      rw [← mul_assoc, polePower_mul, add_neg_cancel, polePower_zero, one_mul]
  · rintro ⟨y, hy, rfl⟩
    change baseValuation F (polePower F m * y) < exp m
    rw [map_mul, valuation_polePower]
    calc
      _ < exp m * 1 := mul_lt_mul_of_pos_left hy exp_pos
      _ = _ := mul_one _

open scoped Valued in
private def powerSeriesIntegerEquiv (F : Type*) [Field F] :
    F⟦X⟧ ≃+* 𝒪[F⸨X⸩] := by
  let f : F⟦X⟧ →+* 𝒪[F⸨X⸩] :=
    (HahnSeries.ofPowerSeries ℤ F).codRestrict _ valuation_integral
  exact RingEquiv.ofBijective f ⟨fun _ _ h => HahnSeries.ofPowerSeries_injective
    (congrArg Subtype.val h), fun x => by
      obtain ⟨p, hp⟩ := (integral_ring F (x : F⸨X⸩)).mp x.property
      exact ⟨p, Subtype.ext hp⟩⟩

open scoped Valued in
private theorem compact_integers (F : Type*) [Field F] [Finite F] :
    IsCompact (𝒪[F⸨X⸩] : Set F⸨X⸩) := by
  let e := powerSeriesIntegerEquiv F
  let : IsDiscreteValuationRing 𝒪[F⸨X⸩] := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  let : Finite 𝓀[F⸨X⸩] := Finite.of_equiv F
    (PowerSeries.residueFieldOfPowerSeries.symm.trans (IsLocalRing.ResidueField.mapEquiv e)).toEquiv
  let : (baseValuation F).IsNontrivial := ⟨⟨polePower F 1, by simp⟩⟩
  have h_arch : MulArchimedean (baseValuation F).ValueGroup₀ :=
    MulArchimedean.comap MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  let : (baseValuation F).RankOne :=
    ((Valuation.nonempty_rankOne_iff_mulArchimedean (v := baseValuation F)).mpr h_arch).some
  have hball : (𝒪[F⸨X⸩] : Set F⸨X⸩) = valuationBall F 1 := by
    ext x
    change baseValuation F x ≤ 1 ↔ baseValuation F x < exp 1
    by_cases hx : baseValuation F x = 0
    · simp [hx]
    · rw [← exp_log hx, ← exp_zero, exp_le_exp, exp_lt_exp]
      omega
  let : CompleteSpace 𝒪[F⸨X⸩] := by
    apply IsComplete.completeSpace_coe
    apply IsClosed.isComplete
    rw [hball]
    exact AddSubgroup.isClosed_of_isOpen
      ((baseValuation F).ltAddSubgroup (Units.mk0 (exp 1) (by simp))) (valuationBall_open 1)
  let : CompactSpace 𝒪[F⸨X⸩] :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact isCompact_iff_compactSpace.mpr inferInstance

private theorem positivePart_compact (F : Type*) [Field F] [Finite F] :
    IsCompact (positivePart F) := by
  have hi : (Valued.integer F⸨X⸩ : Set F⸨X⸩) = valuationBall F 1 := by
    ext x
    change baseValuation F x ≤ 1 ↔ baseValuation F x < exp 1
    by_cases hx : baseValuation F x = 0
    · simp [hx]
    · rw [← exp_log hx, ← exp_zero, exp_le_exp, exp_lt_exp]
      omega
  have h := (compact_integers F).image
    (show Continuous (fun x => polePower F (-1) * x) from continuous_const.mul continuous_id)
  rw [hi, valuationBall_image, Set.image_image] at h
  convert h using 1
  simp [← mul_assoc]

theorem compact_absoluteValue_ball : compactEntryBounds := by
  intro F _ _ N
  have h : {x : F⸨X⸩ | absoluteValue F x ≤ (Nat.card F : ℝ) ^ N} =
      valuationBall F (N + 1) := by
    ext x
    change absoluteValue F x ≤ (Nat.card F : ℝ) ^ N ↔
      baseValuation F x < exp ((N : ℤ) + 1)
    rw [← zpow_natCast]
    by_cases hz : baseValuation F x = 0
    · simp [absoluteValue, hz]
    · rw [absoluteValue, ite_eq_right hz, ← exp_log hz, exp_lt_exp,
        (zpow_right_strictMono₀ (residue_card_gt_one F)).le_iff_le, log_exp]
      omega
  rw [h, valuationBall_image]
  exact (positivePart_compact F).image (continuous_const.mul continuous_id)

private theorem positivePart_open (F : Type*) [Field F] : IsOpen (positivePart F) :=
  valuationBall_open 0

private theorem laurent_locallyCompact (F : Type*) [Field F] [Finite F] :
    LocallyCompactSpace F⸨X⸩ :=
  (positivePart_compact F).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((positivePart_open F).mem_nhds (show (0 : F⸨X⸩) ∈ positivePart F by simp [positivePart]))

private instance polynomialCountable (F : Type*) [Field F] [Finite F] : Countable F[X] :=
  (show Function.Injective (fun p : F[X] => p.toFinsupp.coeff) from fun _ _ h => by
    exact Polynomial.ext (fun n => congrArg (fun a : ℕ →₀ F => a n) h)).countable

open Classical TopologicalSpace in
private theorem laurent_secondCountable (F : Type*) [Field F] [Finite F] :
    SecondCountableTopology F⸨X⸩ := by
  let : Countable F⟮X⟯ :=
    (show Function.Injective (fun x : F⟮X⟯ => (x.num, x.denom)) from fun x y h => by
      have hn : x.num = y.num := congrArg Prod.fst h
      have hd : x.denom = y.denom := congrArg Prod.snd h
      rw [← x.num_div_denom, ← y.num_div_denom, hn, hd]).countable
  let : SeparableSpace F⸨X⸩ :=
    ⟨⟨Set.range (rationalEmbedding F), Set.countable_range _, rationalEmbedding_dense F⟩⟩
  let : Countable ℤᵐ⁰ := by
    change Countable (Option (Multiplicative ℤ))
    infer_instance
  let : (_root_.uniformity F⸨X⸩).IsCountablyGenerated :=
    (valuation_uniformity (LaurentSeries.valuation_surjective F)).isCountablyGenerated
  exact UniformSpace.secondCountable_of_separable _

open MeasureTheory Set TopologicalSpace in
private def positivePartCompact (F : Type*) [Field F] [Finite F] : PositiveCompacts F⸨X⸩ :=
  ⟨⟨positivePart F, positivePart_compact F⟩,
    (positivePart_open F).interior_eq.symm ▸ ⟨0, by simp [positivePart]⟩⟩

open scoped Pointwise ENNReal NNReal
open MeasureTheory Set TopologicalSpace

private theorem valuationBall_succ_volume [Finite F] [MeasurableSpace F⸨X⸩] [BorelSpace F⸨X⸩]
    (μ : Measure F⸨X⸩) [μ.IsAddHaarMeasure] (m : ℤ) :
    μ (valuationBall F (m + 1)) = (Nat.card F : ℝ≥0∞) * μ (valuationBall F m) := by
  classical
  let := Fintype.ofFinite F
  let W : F → Set F⸨X⸩ := fun a => HahnSeries.single (-m) a +ᵥ valuationBall F m
  have hW (a : F) (x : F⸨X⸩) : x ∈ W a ↔ x - HahnSeries.single (-m) a ∈ valuationBall F m := by
    change (∃ y ∈ valuationBall F m, HahnSeries.single (-m) a + y = x) ↔ _
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [add_comm] using hy
    · intro h
      exact ⟨_, h, by abel⟩
  have hcover : valuationBall F (m + 1) = ⋃ a, W a := by
    ext x
    rw [Set.mem_iUnion, valuationBall_coeff]
    simp only [hW, valuationBall_coeff, HahnSeries.coeff_sub, HahnSeries.coeff_single]
    constructor
    · intro h
      refine ⟨x.coeff (-m), fun j hj => ?_⟩
      by_cases h' : j = -m
      · subst j
        simp
      · simp [h', h j (by omega)]
    · rintro ⟨a, ha⟩ j hj
      simpa [show j ≠ -m by omega] using ha j (by omega)
  have hdisj : Pairwise (fun a b => Disjoint (W a) (W b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro x ha hb
    have ha' := (valuationBall_coeff m _).mp ((hW a x).mp ha) (-m) le_rfl
    have hb' := (valuationBall_coeff m _).mp ((hW b x).mp hb) (-m) le_rfl
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_single, ite_true, sub_eq_zero] at ha' hb'
    exact hab (ha'.symm.trans hb')
  rw [hcover, measure_iUnion hdisj]
  · simp [W, measure_vadd, tsum_fintype, Nat.card_eq_fintype_card, nsmul_eq_mul]
  · intro a
    have hopen := (valuationBall_open (F := F) m).preimage
      (continuous_id.sub (continuous_const (y := (HahnSeries.single (-m) a : F⸨X⸩))))
    exact (show IsOpen (W a) from by convert hopen using 1; ext x; exact hW a x).measurableSet

private theorem valuationBall_volume [Finite F] [MeasurableSpace F⸨X⸩] [BorelSpace F⸨X⸩]
    (μ : Measure F⸨X⸩) [μ.IsAddHaarMeasure] (hμ : μ (positivePart F) = 1) (m : ℤ) :
    μ (valuationBall F m) = (((Nat.card F : ℝ≥0) ^ m : ℝ≥0) : ℝ≥0∞) := by
  let q : ℝ≥0 := Nat.card F
  have hq : q ≠ 0 := by
    have : 0 < Nat.card F := Nat.card_pos
    change (Nat.card F : ℝ≥0) ≠ 0
    exact_mod_cast this.ne'
  have hmul (r : ℤ) : ((q ^ (r + 1) : ℝ≥0) : ℝ≥0∞) =
      (q : ℝ≥0∞) * ((q ^ r : ℝ≥0) : ℝ≥0∞) := by
    rw [zpow_add₀ hq, zpow_one, ENNReal.coe_mul, mul_comm]
  induction m using Int.induction_on with
  | zero => simpa [valuationBall, positivePart] using hμ
  | succ m ih =>
    rw [valuationBall_succ_volume, ih, hmul]
    simp [q]
  | pred m ih =>
    have heq := valuationBall_succ_volume μ (-(m : ℤ) - 1)
    rw [sub_add_cancel, ih] at heq
    have h := hmul (-(m : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [h] at heq
    have hcoe : (q : ℝ≥0∞) = (Nat.card F : ℝ≥0∞) := by simp [q]
    rw [← hcoe, ENNReal.mul_right_inj (by simpa) ENNReal.coe_ne_top] at heq
    exact heq.symm

private theorem continuous_mulVec (A : Matrix (Fin d) (Fin d) F⸨X⸩) :
    Continuous A.mulVec := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Fin d → F⸨X⸩ => ∑ j, A i j * x j)
  fun_prop

private def ambientEquiv (g : SquareGL d F⸨X⸩) :
    (Fin d → F⸨X⸩) ≃ₜ+ (Fin d → F⸨X⸩) where
  toAddEquiv := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toAddEquiv
  continuous_toFun := continuous_mulVec g.val
  continuous_invFun := continuous_mulVec (g⁻¹).val

private theorem lattice_change_basis (g : SquareGL d F⸨X⸩) (b : SquareGL d F[X]) :
    (latticeVector (basisMatrix g b)).range = (latticeVector g).range := by
  have h (a : Fin d → F[X]) : latticeVector (basisMatrix g b) a =
      latticeVector g (b.val.mulVec a) := by
    change (g.val * b.val.map (polynomialEmbedding F)) *ᵥ (polynomialEmbedding F ∘ a) =
      g.val *ᵥ (polynomialEmbedding F ∘ b.val.mulVec a)
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact ((polynomialEmbedding F).map_mulVec b.val a i).symm
  apply AddSubgroup.ext
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (h a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(b⁻¹).val.mulVec a, ?_⟩
    rw [h, Matrix.mulVec_mulVec, show b.val * (b⁻¹).val = 1 from b.val_inv, Matrix.one_mulVec]

private theorem standardDomain_pi (F : Type*) [Field F] (d : ℕ) :
    standardDomain F d = Set.univ.pi (fun _ => positivePart F) := by
  ext x
  simp [standardDomain]

private theorem standardDomain_open (F : Type*) [Field F] (d : ℕ) :
    IsOpen (standardDomain F d) := by
  rw [standardDomain_pi]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => positivePart_open F)

private theorem standardDomain_compact (F : Type*) [Field F] [Finite F] (d : ℕ) :
    IsCompact (standardDomain F d) := by
  rw [standardDomain_pi]
  exact isCompact_univ_pi (fun _ => positivePart_compact F)

theorem polynomial_lattice_discrete : discreteLattice := by
  intro F _ d g
  let e := ambientEquiv g
  let S := e '' standardDomain F d
  rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
  refine ⟨S, e.toHomeomorph.isOpenMap _ (standardDomain_open F d), ?_⟩
  ext x
  obtain ⟨a, ha⟩ := x.property
  change (x : Fin d → F⸨X⸩) ∈ S ↔ x ∈ ({0} : Set (latticeVector g).range)
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := hx
    change e (polynomialEmbedding F ∘ a) = (x : Fin d → F⸨X⸩) at ha
    have hy' : polynomialEmbedding F ∘ a ∈ standardDomain F d :=
      e.injective (he.trans ha.symm) ▸ hy
    have ha₀ : a = 0 := by
      funext i
      by_contra hne
      have h := hy' i
      change baseValuation F (polynomialEmbedding F (a i)) < 1 at h
      rw [polynomial_valuation _ hne, ← exp_zero, exp_lt_exp] at h
      omega
    exact Set.mem_singleton_iff.mpr (Subtype.ext (by simpa [ha₀] using ha.symm))
  · rintro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨0, ?_, e.map_zero⟩
    intro i
    simp [positivePart]

private theorem lattice_domain {F : Type*} [Field F] {d : ℕ}
    [MeasurableSpace F⸨X⸩] [BorelSpace F⸨X⸩] [SecondCountableTopology F⸨X⸩]
    (μ : Measure (Fin d → F⸨X⸩)) (g : SquareGL d F⸨X⸩) :
    IsAddFundamentalDomain (latticeVector g).range
      (ambientEquiv g '' standardDomain F d) μ := by
  let e := ambientEquiv g
  let S := e '' standardDomain F d
  have hopen : IsOpen S := e.toHomeomorph.isOpenMap _ (standardDomain_open F d)
  have hpol (a : Fin d → F[X]) :
      latticeVector g a = e (polynomialEmbedding F ∘ a) := rfl
  have htranslate (x : Fin d → F⸨X⸩) (a : Fin d → F[X]) :
      x - latticeVector g a ∈ S ↔ e.symm x - (polynomialEmbedding F ∘ a) ∈ standardDomain F d := by
    change _ ∈ e.toEquiv '' standardDomain F d ↔ _
    rw [e.toEquiv.image_eq_preimage_symm]
    change e.symm (x - latticeVector g a) ∈ standardDomain F d ↔ _
    rw [map_sub, hpol, e.symm_apply_apply]
  refine ⟨hopen.measurableSet.nullMeasurableSet, Filter.Eventually.of_forall (fun x => ?_), ?_⟩
  · obtain ⟨a, ha, _⟩ := polynomial_part F d (e.symm x)
    refine ⟨-⟨latticeVector g a, ⟨a, rfl⟩⟩, ?_⟩
    change -(latticeVector g a) + x ∈ S
    rw [add_comm, ← sub_eq_add_neg]
    exact (htranslate x a).2 ha
  · intro a b hab
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro x hax hbx
    obtain ⟨p, hp⟩ := a.property
    obtain ⟨q, hq⟩ := b.property
    change (∃ y ∈ S, (a : Fin d → F⸨X⸩) + y = x) at hax
    change (∃ y ∈ S, (b : Fin d → F⸨X⸩) + y = x) at hbx
    obtain ⟨y, hy, rfl⟩ := hax
    obtain ⟨z, hz, he⟩ := hbx
    let x := (a : Fin d → F⸨X⸩) + y
    have hpy : x - latticeVector g p ∈ S := by simpa [x, hp, add_comm] using hy
    have hqz : x - latticeVector g q ∈ S := by simpa [x, hq, ← he, add_comm] using hz
    have hpq := (polynomial_part F d (e.symm x)).unique
      ((htranslate x p).1 hpy) ((htranslate x q).1 hqz)
    exact hab (Subtype.ext (hp.symm.trans (hpq ▸ hq)))

private theorem integral_preserves_domain (k : SquareGL d F⟦X⟧) :
    ambientEquiv (Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F) k) ''
      standardDomain F d = standardDomain F d := by
  let K := Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F) k
  have h (K₀ : SquareGL d F⟦X⟧) (x : Fin d → F⸨X⸩) (hx : x ∈ standardDomain F d) :
      ambientEquiv (Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F) K₀) x ∈
        standardDomain F d := by
    intro i
    let U := (baseValuation F).ltAddSubgroup (1 : (ℤᵐ⁰)ˣ)
    change (∑ j, HahnSeries.ofPowerSeries ℤ F (K₀.val i j) * x j) ∈ U
    apply U.sum_mem
    intro j _
    change baseValuation F (HahnSeries.ofPowerSeries ℤ F (K₀.val i j) * x j) < 1
    rw [map_mul]
    exact (mul_le_of_le_one_left zero_le (valuation_integral _)).trans_lt (hx j)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h k y hy
  · intro hx
    refine ⟨(ambientEquiv K).symm x, ?_, (ambientEquiv K).apply_symm_apply x⟩
    change ambientEquiv K⁻¹ x ∈ standardDomain F d
    rw [← map_inv]
    exact h k⁻¹ x hx

private theorem diagonal_domain (n : Fin d → ℤ) :
    ambientEquiv (diagonalUnits (fun i => poleUnit F (n i))) '' standardDomain F d =
      Set.univ.pi (fun i => valuationBall F (n i)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ i _
    change _ ∈ valuationBall F (n i)
    rw [valuationBall_image]
    refine ⟨y i, hy i, ?_⟩
    change _ = (Matrix.diagonal (polePower F ∘ n) *ᵥ y) i
    rw [Matrix.mulVec_diagonal]
    rfl
  · intro hx
    have h (i : Fin d) := hx i (Set.mem_univ i)
    simp only [valuationBall_image, Set.mem_image] at h
    choose y hy he using h
    refine ⟨y, hy, funext fun i => ?_⟩
    change (Matrix.diagonal (polePower F ∘ n) *ᵥ y) i = _
    rw [Matrix.mulVec_diagonal]
    exact he i

private def standardDomainCompact (F : Type*) [Field F] [Finite F] (d : ℕ) :
    PositiveCompacts (Fin d → F⸨X⸩) :=
  ⟨⟨standardDomain F d, standardDomain_compact F d⟩,
    (standardDomain_open F d).interior_eq.symm ▸ ⟨0, by simp [standardDomain, positivePart]⟩⟩

private theorem integral_preserves_measure [Finite F] [MeasurableSpace F⸨X⸩] [BorelSpace F⸨X⸩]
    [SecondCountableTopology F⸨X⸩] [LocallyCompactSpace F⸨X⸩]
    (μ : Measure (Fin d → F⸨X⸩)) [μ.IsAddHaarMeasure] (hμ : μ (standardDomain F d) = 1)
    (k : SquareGL d F⟦X⟧) :
    let K := ambientEquiv (Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F) k)
    Measure.map K μ = μ := by
  let K := ambientEquiv (Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F) k)
  let C := standardDomainCompact F d
  have hmap : (Measure.map K μ) (standardDomain F d) = 1 := by
    have hm : Measurable (⇑K : (Fin d → F⸨X⸩) → _) := K.continuous.measurable
    rw [Measure.map_apply hm (standardDomain_open F d).measurableSet]
    have h := integral_preserves_domain k
    change K.toEquiv '' standardDomain F d = _ at h
    rw [← h, show (⇑K : (Fin d → F⸨X⸩) → _) ⁻¹' (K.toEquiv '' standardDomain F d) =
      standardDomain F d from Set.preimage_image_eq _ K.injective]
    exact hμ
  have he₁ : Measure.addHaarMeasure C = μ :=
    (Measure.addHaarMeasure_eq_iff C μ).mpr hμ
  have he₂ : Measure.addHaarMeasure C = Measure.map K μ :=
    (Measure.addHaarMeasure_eq_iff C (Measure.map K μ)).mpr hmap
  exact he₂.symm.trans he₁

theorem normalized_haar_covolume : haarCovolume := by
  intro F _ _ d
  let : MeasurableSpace F⸨X⸩ := borel _
  let : BorelSpace F⸨X⸩ := ⟨rfl⟩
  let : LocallyCompactSpace F⸨X⸩ := laurent_locallyCompact F
  let : SecondCountableTopology F⸨X⸩ := laurent_secondCountable F
  let ν := Measure.addHaarMeasure (positivePartCompact F)
  let μ := Measure.pi (fun _ : Fin d => ν)
  have hν : ν (positivePart F) = 1 := Measure.addHaarMeasure_self
  have hμ : μ (standardDomain F d) = 1 := by
    rw [standardDomain_pi]
    change Measure.pi (fun _ : Fin d => ν) (Set.univ.pi (fun _ => positivePart F)) = 1
    rw [Measure.pi_pi]
    simp [hν]
  refine ⟨μ, inferInstance, hμ, fun g => ?_⟩
  obtain ⟨b, k, n, hb⟩ := ordered_basis g
  let A := basisMatrix g b
  let K := Matrix.GeneralLinearGroup.map (HahnSeries.ofPowerSeries ℤ F) k
  let D := diagonalUnits (fun i => poleUnit F (n i))
  have hA : A = K * D := Units.ext hb.2
  let S := ambientEquiv A '' standardDomain F d
  have hcomp : IsCompact S := (standardDomain_compact F d).image (ambientEquiv A).continuous
  have hopen : IsOpen S := (ambientEquiv A).toHomeomorph.isOpenMap _ (standardDomain_open F d)
  have hFD : IsAddFundamentalDomain (latticeVector g).range S μ := by
    rw [← lattice_change_basis g b]
    exact lattice_domain μ A
  refine ⟨⟨S, hcomp, hopen, hFD⟩, ?_⟩
  let : Countable (latticeVector g).range := (Set.countable_range (latticeVector g)).to_subtype
  rw [hFD.covolume_eq_volume μ]
  have hS : S = ambientEquiv K '' (ambientEquiv D '' standardDomain F d) := by
    dsimp [S]
    rw [hA, Set.image_image]
    congr 1
    funext x
    change (K.val * D.val) *ᵥ x = K.val *ᵥ (D.val *ᵥ x)
    exact (Matrix.mulVec_mulVec x K.val D.val).symm
  rw [hS]
  have hmeas : MeasurableSet (ambientEquiv K '' (ambientEquiv D '' standardDomain F d)) :=
    (hS ▸ hopen).measurableSet
  have hmap := integral_preserves_measure μ hμ k
  change Measure.map (ambientEquiv K) μ = μ at hmap
  rw [← hmap]
  have hm : Measurable (⇑(ambientEquiv K) : (Fin d → F⸨X⸩) → _) :=
    (ambientEquiv K).continuous.measurable
  rw [Measure.map_apply hm hmeas,
    Set.preimage_image_eq _ (ambientEquiv K).injective, diagonal_domain]
  change Measure.pi (fun _ : Fin d => ν) (Set.univ.pi (fun i => valuationBall F (n i))) = _
  rw [Measure.pi_pi]
  simp_rw [valuationBall_volume ν hν]
  let q : ℝ≥0 := Nat.card F
  change (∏ i, ENNReal.ofNNRealHom (q ^ n i)) = _
  rw [← map_prod]
  have hq : q ≠ 0 := by
    change (Nat.card F : ℝ≥0) ≠ 0
    exact_mod_cast (Nat.card_pos (α := F)).ne'
  have hprod (s : Finset (Fin d)) : (∏ i ∈ s, q ^ n i) = q ^ (∑ i ∈ s, n i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]
  rw [hprod, absoluteValue_of_valuation (sum_ordered_exponents hb)]
  change (↑(q ^ (∑ i, n i)) : ℝ≥0∞) = ENNReal.ofReal (↑(q ^ (∑ i, n i)) : ℝ)
  exact ENNReal.ofReal_coe_nnreal.symm

end

end LinearAlgebraicGroups.Arithmetic.LaurentLattice
