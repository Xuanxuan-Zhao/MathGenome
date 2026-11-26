import LinearAlgebraicGroups.Relative.ParabolicIntersection
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import LinearAlgebraicGroups.Relative.RelativeChambers
import LinearAlgebraicGroups.Relative.RelativeBruhat
import LinearAlgebraicGroups.Classification.RationalRealization
import Mathlib.Analysis.Complex.Polynomial.Basic
import Specs.LinearAlgebraicGroups.Relative.RealUnitaryCells
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import LinearAlgebraicGroups.Unipotent.CentralSeries
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.Finite.Perm
import Mathlib.LinearAlgebra.Matrix.Permutation

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Matrix TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Relative.RealUnitaryCells

open Specs.RealUnitaryCells
open Specs (ClosedSubgroup)

set_option maxHeartbeats 1200000
set_option Elab.async false

noncomputable section

private def complexCoordinates : QuadraticAlgebra ℝ (-1) 0 ≃ₐ[ℝ] ℂ where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv := by rintro ⟨r, i⟩; rfl
  right_inv := by rintro ⟨r, i⟩; rfl
  map_mul' z w := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, sub_eq_add_neg]
  map_add' z w := rfl
  commutes' r := rfl

theorem complexTensorModel : ComplexTensorModel := by
  intro R _ _
  let c := complexCoordinates.symm
  let e := Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[ℝ] R) c
  let b := QuadraticAlgebra.baseChangeEquiv R (-1 : ℝ) (0 : ℝ)
  let a : QuadraticAlgebra R (algebraMap ℝ R (-1)) (algebraMap ℝ R 0) ≃ₐ[R]
      Complexification R :=
    { toFun := fun x => ⟨x.re, x.im⟩
      invFun := fun x => ⟨x.re, x.im⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun x y => by
        apply QuadraticAlgebra.ext <;>
          simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let eR : R ⊗[ℝ] ℂ ≃ₐ[R] R ⊗[ℝ] QuadraticAlgebra ℝ (-1) 0 :=
    { toRingEquiv := e.toRingEquiv
      commutes' := fun r => by
        change e (r ⊗ₜ (1 : ℂ)) = r ⊗ₜ (1 : QuadraticAlgebra ℝ (-1) 0)
        simp [e] }
  refine ⟨eR.trans (b.trans a), ?_⟩
  intro r z
  change a (b (e (r ⊗ₜ z))) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    QuadraticAlgebra.baseChangeEquiv_tmul]
  rfl

private def splitCoordinates (R : Type) [CommRing R] [Algebra ℂ R] :
    Complexification R ≃ₐ[R] R × R := by
  let i := algebraMap ℂ R Complex.I
  let half := algebraMap ℂ R (1 / 2)
  let invI := algebraMap ℂ R (-Complex.I)
  have hi : i * i = -1 := by
    simp [i, ← map_mul, Complex.I_mul_I]
  have hh : half + half = 1 := by
    simp only [half, ← map_add, ← map_one (algebraMap ℂ R)]
    norm_num
  have hinv : invI * i = 1 := by
    simp [invI, i, ← map_mul, Complex.I_mul_I]
  refine
    { toFun := fun z => (z.re + z.im * i, z.re - z.im * i)
      invFun := fun xy => ⟨(xy.1 + xy.2) * half, (xy.1 - xy.2) * invI * half⟩
      left_inv := ?_, right_inv := ?_, map_mul' := ?_, map_add' := ?_, commutes' := ?_ }
  · intro z
    apply QuadraticAlgebra.ext
    · dsimp
      linear_combination z.re * hh
    · dsimp
      calc
        (z.re + z.im * i - (z.re - z.im * i)) * invI * half =
            z.im * (invI * i) * (half + half) := by ring
        _ = z.im := by rw [hinv, hh]; ring
  · rintro ⟨p, q⟩
    apply Prod.ext
    · dsimp
      rw [show (p - q) * invI * half * i = (p - q) * (invI * i) * half by ring, hinv]
      linear_combination p * hh
    · dsimp
      rw [show (p - q) * invI * half * i = (p - q) * (invI * i) * half by ring, hinv]
      linear_combination q * hh
  · intro z w
    apply Prod.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
      linear_combination -z.im * w.im * hi
  · intro z w
    apply Prod.ext <;> simp <;> ring
  · intro r
    apply Prod.ext <;> simp

theorem complexSplitting : ComplexSplitting := by
  intro R _ _
  refine ⟨splitCoordinates R, fun _ => rfl, ?_⟩
  intro z
  apply Prod.ext <;>
    simp [splitCoordinates, sub_eq_add_neg]

private def rev : Fin 3 ≃ Fin 3 := Equiv.swap 0 2

@[simp] private theorem rev_zero : rev 0 = 2 := by decide
@[simp] private theorem rev_one : rev 1 = 1 := by decide
@[simp] private theorem rev_two : rev 2 = 0 := by decide

private theorem J_mul {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R)
    (i j : Fin 3) : (J R * M) i j = M (rev i) j := by
  fin_cases i <;> simp [J, Matrix.mul_apply, Fin.sum_univ_three]

private theorem mul_J {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R)
    (i j : Fin 3) : (M * J R) i j = M i (rev j) := by
  fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_three]

private theorem J_sq (R : Type*) [CommRing R] : J R * J R = 1 := by
  ext i j
  rw [J_mul]
  fin_cases i <;> fin_cases j <;> simp [J]

private theorem map_J {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    f.mapMatrix (J R) = J S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, RingHom.mapMatrix_apply]

private def partner {R : Type*} [CommRing R] (x : SL R) : SL R :=
  ⟨(x⁻¹).val.transpose.submatrix rev rev, by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact (x⁻¹).property⟩

private theorem partner_matrix {R : Type*} [CommRing R] (x : SL R) :
    (partner x).val = J R * (x⁻¹).val.transpose * J R := by
  ext i j
  rw [mul_J, J_mul]
  rfl

private theorem partner_form {R : Type*} [CommRing R] (x : SL R) :
    (partner x).val.transpose * J R * x.val = J R := by
  have ht : (J R).transpose = J R := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.transpose_apply]
  have h : (x⁻¹).val * x.val = 1 := congrArg Subtype.val (inv_mul_cancel x)
  rw [partner_matrix, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, ht]
  simp only [mul_assoc]
  rw [← mul_assoc (J R) (J R) x.val, J_sq, one_mul, h, mul_one]

private theorem partner_unique {R : Type*} [CommRing R] (x y : SL R)
    (h : y.val.transpose * J R * x.val = J R) : y = partner x := by
  have hinv : x.val * (x⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel x)
  have ht : y.val.transpose = (partner x).val.transpose := by
    have cancel (M : Matrix (Fin 3) (Fin 3) R) :
        (M * J R * x.val) * (x⁻¹).val * J R = M := by
      simp only [mul_assoc]
      rw [← mul_assoc x.val (x⁻¹).val (J R), hinv, one_mul, J_sq, mul_one]
    rw [← cancel y.val.transpose, h, ← cancel (partner x).val.transpose, partner_form]
  apply Subtype.ext
  simpa using congrArg Matrix.transpose ht

private theorem other_partner_form {R : Type*} [CommRing R] (x : SL R) :
    x.val.transpose * J R * (partner x).val = J R := by
  have ht : (J R).transpose = J R := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.transpose_apply]
  have h := congrArg Matrix.transpose (partner_form x)
  simpa [Matrix.transpose_mul, ht, mul_assoc] using h

private theorem upper_iff {R : Type*} [CommRing R] (x : SL R) :
    x.val.IsUpperTriangular ↔ x.val 1 0 = 0 ∧ x.val 2 0 = 0 ∧ x.val 2 1 = 0 := by
  refine ⟨fun h => ⟨h (by decide), h (by decide), h (by decide)⟩, ?_⟩
  rintro ⟨h10, h20, h21⟩ i j hij
  fin_cases i <;> fin_cases j <;> first | exact h10 | exact h20 | exact h21 | contradiction

private theorem line_partner_iff {R : Type*} [CommRing R] (x : SL R) :
    PreservesLine x ∧ PreservesLine (partner x) ↔ x.val.IsUpperTriangular := by
  have p10 : (partner x).val 1 0 =
      -(x.val 0 0 * x.val 2 1) + x.val 0 1 * x.val 2 0 := by
    change (x⁻¹).val 2 1 = _
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    rfl
  have p20 : (partner x).val 2 0 = x.val 1 0 * x.val 2 1 - x.val 1 1 * x.val 2 0 := by
    change (x⁻¹).val 2 0 = _
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    rfl
  rw [upper_iff]
  constructor
  · rintro ⟨⟨h10, h20⟩, h⟩
    have hdet := x.property
    rw [Matrix.det_fin_three, h10, h20] at hdet
    have hprod : x.val 0 0 * (x.val 1 1 * x.val 2 2 - x.val 1 2 * x.val 2 1) = 1 := by
      linear_combination hdet
    have hmul : x.val 0 0 * x.val 2 1 = 0 := by
      have h' := h.1
      rw [p10, h20, mul_zero, add_zero, neg_eq_zero] at h'
      exact h'
    refine ⟨h10, h20, ?_⟩
    have hu : IsUnit (x.val 0 0) := isUnit_iff_exists_inv.mpr ⟨_, hprod⟩
    exact hu.mul_left_cancel (hmul.trans (mul_zero _).symm)
  · rintro ⟨h10, h20, h21⟩
    exact ⟨⟨h10, h20⟩, by simp [PreservesLine, p10, p20, h20, h21]⟩

private def firstCoordinate (R : Type) [CommRing R] [Algebra ℂ R] :
    Complexification R →+* R :=
  (RingHom.fst R R).comp (splitCoordinates R).toRingHom

private def secondCoordinate (R : Type) [CommRing R] [Algebra ℂ R] :
    Complexification R →+* R :=
  (RingHom.snd R R).comp (splitCoordinates R).toRingHom

private theorem first_star (R : Type) [CommRing R] [Algebra ℂ R] (z : Complexification R) :
    firstCoordinate R (star z) = secondCoordinate R z := by
  change (star z).re + (star z).im * _ = z.re - z.im * _
  simp [sub_eq_add_neg]

private theorem second_star (R : Type) [CommRing R] [Algebra ℂ R] (z : Complexification R) :
    secondCoordinate R (star z) = firstCoordinate R z := by
  rw [← first_star, star_star]

private theorem pair_injective (R : Type) [CommRing R] [Algebra ℂ R]
    {a b : Complexification R} (h₁ : firstCoordinate R a = firstCoordinate R b)
    (h₂ : secondCoordinate R a = secondCoordinate R b) : a = b :=
  (splitCoordinates R).injective (Prod.ext h₁ h₂)

private theorem first_form {R : Type} [CommRing R] [Algebra ℂ R]
    (g : SL (Complexification R)) :
    (firstCoordinate R).mapMatrix (g.valᴴ * J _ * g.val) =
      (Matrix.SpecialLinearGroup.map (secondCoordinate R) g).val.transpose * J R *
        (Matrix.SpecialLinearGroup.map (firstCoordinate R) g).val := by
  simp only [map_mul, map_J]
  congr 2
  ext i j
  exact first_star R _

private theorem second_form {R : Type} [CommRing R] [Algebra ℂ R]
    (g : SL (Complexification R)) :
    (secondCoordinate R).mapMatrix (g.valᴴ * J _ * g.val) =
      (Matrix.SpecialLinearGroup.map (firstCoordinate R) g).val.transpose * J R *
        (Matrix.SpecialLinearGroup.map (secondCoordinate R) g).val := by
  simp only [map_mul, map_J]
  congr 2
  ext i j
  exact second_star R _

private def pairedMatrix {R : Type} [CommRing R] [Algebra ℂ R] (x y : SL R) :
    SL (Complexification R) :=
  Matrix.SpecialLinearGroup.map (splitCoordinates R).symm.toRingHom
    ⟨fun i j => (x.val i j, y.val i j), by
      apply Prod.ext
      · exact ((RingHom.map_det (RingHom.fst R R)
          (fun i j : Fin 3 => (x.val i j, y.val i j))).trans x.property)
      · exact ((RingHom.map_det (RingHom.snd R R)
          (fun i j : Fin 3 => (x.val i j, y.val i j))).trans y.property)⟩


private theorem first_pair {R : Type} [CommRing R] [Algebra ℂ R] (x y : SL R) :
    Matrix.SpecialLinearGroup.map (firstCoordinate R) (pairedMatrix x y) = x := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((splitCoordinates R) ((splitCoordinates R).symm (x.val i j, y.val i j))).1 = _
  rw [AlgEquiv.apply_symm_apply]

private theorem second_pair {R : Type} [CommRing R] [Algebra ℂ R] (x y : SL R) :
    Matrix.SpecialLinearGroup.map (secondCoordinate R) (pairedMatrix x y) = y := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((splitCoordinates R) ((splitCoordinates R).symm (x.val i j, y.val i j))).2 = _
  rw [AlgEquiv.apply_symm_apply]

private def complexGroupEquiv (R : Type) [CommRing R] [Algebra ℂ R] :
    {g : SL (Complexification R) // IsUnitary g} ≃ SL R := by
  let f := Matrix.SpecialLinearGroup.map (n := Fin 3) (firstCoordinate R)
  let s := Matrix.SpecialLinearGroup.map (n := Fin 3) (secondCoordinate R)
  have hs (g : SL (Complexification R)) (hg : IsUnitary g) : s g = partner (f g) := by
    apply partner_unique
    exact (first_form g).symm.trans (by rw [show g.valᴴ * J _ * g.val = J _ from hg, map_J])
  refine
    { toFun := fun g => f g.val
      invFun := fun x => ⟨pairedMatrix x (partner x), ?_⟩
      left_inv := ?_, right_inv := fun x => first_pair x (partner x) }
  · let g := pairedMatrix x (partner x)
    have h₁ := (first_form g).trans (by rw [first_pair, second_pair, partner_form])
    have h₂ := (second_form g).trans (by rw [first_pair, second_pair, other_partner_form])
    change g.valᴴ * J _ * g.val = J _
    apply Matrix.ext
    intro i j
    apply pair_injective R
    · simpa only [← map_J (firstCoordinate R), RingHom.mapMatrix_apply, Matrix.map_apply] using
        congrFun (congrFun h₁ i) j
    · simpa only [← map_J (secondCoordinate R), RingHom.mapMatrix_apply, Matrix.map_apply] using
        congrFun (congrFun h₂ i) j
  · intro g
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    apply pair_injective R
    · exact congrArg (fun x : SL R => x.val i j) (first_pair (f g.val) (partner (f g.val)))
    · exact congrArg (fun x : SL R => x.val i j)
        ((second_pair (f g.val) (partner (f g.val))).trans (hs g.val g.property).symm)

theorem complexGroupComparison : ComplexGroupComparison := by
  intro R _ _
  refine ⟨complexGroupEquiv R, fun _ _ _ => rfl, ?_, ?_⟩
  · intro g h m hm
    change Matrix.SpecialLinearGroup.map (firstCoordinate R) m.val = _
    rw [hm, map_mul]
    rfl
  · intro g
    let x := Matrix.SpecialLinearGroup.map (firstCoordinate R) g.val
    let y := Matrix.SpecialLinearGroup.map (secondCoordinate R) g.val
    have hy : y = partner x := by
      apply partner_unique
      exact (first_form g.val).symm.trans (by rw [show g.val.valᴴ * J _ * g.val.val = J _ from g.property, map_J])
    have hline : PreservesLine g.val ↔ PreservesLine x ∧ PreservesLine y := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact ⟨⟨by change firstCoordinate R (g.val.val 1 0) = _; rw [h.1, map_zero],
                by change firstCoordinate R (g.val.val 2 0) = _; rw [h.2, map_zero]⟩,
               ⟨by change secondCoordinate R (g.val.val 1 0) = _; rw [h.1, map_zero],
                by change secondCoordinate R (g.val.val 2 0) = _; rw [h.2, map_zero]⟩⟩
      · exact ⟨pair_injective R (h.1.1.trans (map_zero _).symm) (h.2.1.trans (map_zero _).symm),
               pair_injective R (h.1.2.trans (map_zero _).symm) (h.2.2.trans (map_zero _).symm)⟩
    change PreservesLine g.val ↔ x.val.IsUpperTriangular
    rw [hline, hy, line_partner_iff]


private theorem isUnitary_one (R : Type*) [CommRing R] [StarRing R] :
    IsUnitary (1 : SL R) := by
  simp [IsUnitary, Matrix.SpecialLinearGroup.coe_one]

private theorem isUnitary_mul {R : Type*} [CommRing R] [StarRing R] {g h : SL R}
    (hg : IsUnitary g) (hh : IsUnitary h) : IsUnitary (g * h) := by
  change g.valᴴ * J _ * g.val = J _ at hg
  change h.valᴴ * J _ * h.val = J _ at hh
  change (g.val * h.val)ᴴ * J R * (g.val * h.val) = J R
  rw [Matrix.conjTranspose_mul]
  calc
    h.valᴴ * g.valᴴ * J R * (g.val * h.val) =
        h.valᴴ * (g.valᴴ * J R * g.val) * h.val := by simp only [mul_assoc]
    _ = J R := by rw [hg, hh]

private theorem isUnitary_inv {R : Type*} [CommRing R] [StarRing R] {g : SL R}
    (hg : IsUnitary g) : IsUnitary g⁻¹ := by
  have h : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  have ht : (g⁻¹).valᴴ * g.valᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose h
  calc
    (g⁻¹).valᴴ * J R * (g⁻¹).val =
        (g⁻¹).valᴴ * (g.valᴴ * J R * g.val) * (g⁻¹).val := by
          rw [show g.valᴴ * J R * g.val = J R from hg]
    _ = ((g⁻¹).valᴴ * g.valᴴ) * J R * (g.val * (g⁻¹).val) := by simp only [mul_assoc]
    _ = J R := by rw [h, ht, one_mul, mul_one]

private def longest (R : Type*) [CommRing R] : SL R :=
  ⟨longestMatrix R, by simp [longestMatrix, Matrix.det_fin_three]⟩

private def adjacent (R : Type*) [CommRing R] : SL R :=
  ⟨adjacentMatrix R, by simp [adjacentMatrix, Matrix.det_fin_three]⟩

private theorem longest_unitary (R : Type*) [CommRing R] [StarRing R] :
    IsUnitary (longest R) := by
  change (longestMatrix R)ᴴ * J R * longestMatrix R = J R
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, J, longestMatrix]

private theorem multiply_line_entry {R : Type*} [CommRing R] {g p : SL R}
    (hp : PreservesLine p) (i : Fin 3) :
    (g * p).val i 0 = g.val i 0 * p.val 0 0 := by
  simp [show (g * p).val = g.val * p.val from rfl, Matrix.mul_apply, Fin.sum_univ_three, hp.1, hp.2]

private theorem upper_diag20_det {R : Type*} [CommRing R] (p : SL R)
    (hp : p.val.IsUpperTriangular) :
    p.val 0 0 * (p.val 1 1 * p.val 2 2) = 1 := by
  rcases (upper_iff p).mp hp with ⟨h10, h20, h21⟩
  have hdet := p.property
  rw [Matrix.det_fin_three] at hdet
  simpa only [h10, h20, h21, mul_zero, zero_mul, sub_zero, add_zero, mul_assoc] using hdet

private theorem longest_pivot {R : Type*} [Field R] {p q : SL R}
    (hp : p.val.IsUpperTriangular) (hq : q.val.IsUpperTriangular) :
    (p * longest R * q).val 2 0 ≠ 0 := by
  have hp' := upper_diag20_det p hp
  have hq' := upper_diag20_det q hq
  rw [multiply_line_entry ⟨(upper_iff q).mp hq |>.1, (upper_iff q).mp hq |>.2.1⟩]
  have h : (p * longest R).val 2 0 = p.val 2 2 := by
    change (p.val * longestMatrix R) 2 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_three, longestMatrix]
  rw [h]
  refine mul_ne_zero (fun hn => ?_) (fun hn => ?_)
  · simp [hn] at hp'
  · simp [hn] at hq'

private theorem unitary_upper_iff {R : Type*} [CommRing R] [StarRing R] {g : SL R}
    (hg : IsUnitary g) : PreservesLine g ↔ g.val.IsUpperTriangular := by
  let y := Matrix.SpecialLinearGroup.map (starRingEnd R) g
  have hy : y = partner g := by
    apply partner_unique
    exact hg
  have hline : PreservesLine g → PreservesLine y := fun h => by
    exact ⟨(congrArg (starRingEnd R) h.1).trans (map_zero _),
      (congrArg (starRingEnd R) h.2).trans (map_zero _)⟩
  refine ⟨fun h => (line_partner_iff g).mp ⟨h, hy ▸ hline h⟩, fun h => ?_⟩
  exact ⟨h (by decide), h (by decide)⟩

private theorem column_norm {R : Type*} [CommRing R] [StarRing R] {g : SL R}
    (hg : IsUnitary g) :
    star (g.val 0 0) * g.val 2 0 + star (g.val 1 0) * g.val 1 0 +
      star (g.val 2 0) * g.val 0 0 = 0 := by
  change g.valᴴ * J R * g.val = J R at hg
  have h := congrFun (congrFun hg 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, J] at h
  linear_combination h

private theorem unitary_line_iff_pivot_zero {g : SL ℂ} (hg : IsUnitary g) :
    PreservesLine g ↔ g.val 2 0 = 0 := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  have he : star (g.val 1 0) * g.val 1 0 = 0 := by
    simpa [h] using column_norm hg
  exact (mul_eq_zero.mp he).elim
    (fun hn => star_injective (hn.trans (star_zero ℂ).symm)) id

private def upperUnipotent {R : Type*} [CommRing R] [StarRing R] (x y : R) : SL R :=
  ⟨!![1, -star y, x; 0, 1, y; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

private theorem upperUnipotent_unitary {R : Type*} [CommRing R] [StarRing R] {x y : R}
    (h : star x + x + star y * y = 0) : IsUnitary (upperUnipotent x y) := by
  unfold IsUnitary
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, J]
  linear_combination h

private theorem upperUnipotent_line {R : Type*} [CommRing R] [StarRing R] (x y : R) :
    PreservesLine (upperUnipotent x y) := ⟨rfl, rfl⟩

private theorem line_of_equal_column {R : Type*} [CommRing R] (u g : SL R) (c : R)
    (h : ∀ i, g.val i 0 = u.val i 0 * c) : PreservesLine (u⁻¹ * g) := by
  have hp : (u⁻¹).val * u.val = 1 := congrArg Subtype.val (inv_mul_cancel u)
  have he (i : Fin 3) : (u⁻¹ * g).val i 0 = (1 : Matrix (Fin 3) (Fin 3) R) i 0 * c := by
    change ((u⁻¹).val * g.val) i 0 = _
    rw [← hp]
    simp only [Matrix.mul_apply, h, Finset.sum_mul, mul_assoc]
  exact ⟨by simpa using he 1, by simpa using he 2⟩

private theorem real_longest_factor {g : SL ℂ} (hg : IsUnitary g) (hc : g.val 2 0 ≠ 0) :
    InDoubleCoset (fun x : SL ℂ => IsUnitary x ∧ PreservesLine x) (longest ℂ) g := by
  let c := g.val 2 0
  let x := g.val 0 0 / c
  let y := g.val 1 0 / c
  have hx : x * c = g.val 0 0 := div_mul_cancel₀ _ hc
  have hy : y * c = g.val 1 0 := div_mul_cancel₀ _ hc
  have hc' : star c * c ≠ 0 :=
    mul_ne_zero (fun h => hc (star_injective (h.trans (star_zero ℂ).symm))) hc
  have hxy : star x + x + star y * y = 0 := by
    suffices he : (star x + x + star y * y) * (star c * c) = 0 from
      (mul_eq_zero.mp he).resolve_right hc'
    calc
      (star x + x + star y * y) * (star c * c) =
        star (x * c) * c + star (y * c) * (y * c) + star c * (x * c) := by
          simp only [star_mul]
          ring
      _ = 0 := by rw [hx, hy]; exact column_norm hg
  let p := upperUnipotent x y
  let u := p * longest ℂ
  let q := u⁻¹ * g
  have hp : IsUnitary p := upperUnipotent_unitary hxy
  have hu : IsUnitary u := isUnitary_mul hp (longest_unitary ℂ)
  have hcol (i : Fin 3) : g.val i 0 = u.val i 0 * c := by
    change g.val i 0 = (p.val * longestMatrix ℂ) i 0 * c
    fin_cases i <;>
      simp [p, Matrix.mul_apply, Fin.sum_univ_three, longestMatrix, upperUnipotent, hx, hy, c]
  exact ⟨p, q, ⟨hp, upperUnipotent_line x y⟩,
    ⟨isUnitary_mul (isUnitary_inv hu) hg, line_of_equal_column u g c hcol⟩,
    (mul_inv_cancel_left u g).symm⟩

theorem realDoubleCosets : RealDoubleCosets := by
  refine ⟨longest ℂ, rfl, longest_unitary ℂ, fun g hg => ⟨?_, ?_⟩⟩
  · refine ⟨?_, fun hg0 => ⟨g, 1, ⟨hg, (unitary_line_iff_pivot_zero hg).mpr hg0⟩,
        ⟨isUnitary_one ℂ, by simp [PreservesLine, Matrix.SpecialLinearGroup.coe_one]⟩,
        by simp⟩⟩
    rintro ⟨p, q, hp, hq, rfl⟩
    rw [mul_one, multiply_line_entry hq.2 2, hp.2.2, zero_mul]
  · refine ⟨?_, real_longest_factor hg⟩
    rintro ⟨p, q, hp, hq, rfl⟩
    exact longest_pivot ((unitary_upper_iff hp.1).mp hp.2)
      ((unitary_upper_iff hq.1).mp hq.2)

theorem missingComplexCell : MissingComplexCell := by
  refine ⟨longest ℂ, adjacent ℂ, rfl, rfl, ?_, ?_⟩
  · rintro ⟨p, q, hp, hq, he⟩
    have hpq : (p.val * q.val).IsUpperTriangular := Matrix.BlockTriangular.mul hp hq
    have h := hpq (i := 1) (j := 0) (by decide)
    rw [← show (p * q).val = p.val * q.val from rfl, ← one_mul q, ← mul_assoc, ← he] at h
    change (-1 : ℂ) = 0 at h
    norm_num at h
  · rintro ⟨p, q, hp, hq, he⟩
    have h := longest_pivot hp hq
    rw [← he] at h
    exact h rfl

theorem signature : Signature := by
  let B : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 1; 0, 1, 0; 1 / 2, 0, -(1 / 2)]
  refine ⟨B, ?_, ?_⟩
  · apply isUnit_iff_ne_zero.mpr
    norm_num [B, Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        Fin.sum_univ_three, J, map_div₀, map_ofNat]


private theorem preservesLine_one (R : Type*) [CommRing R] :
    PreservesLine (1 : SL R) := by simp [PreservesLine, Matrix.SpecialLinearGroup.coe_one]

private theorem preservesLine_inv {R : Type*} [CommRing R] {g : SL R}
    (h : PreservesLine g) : PreservesLine g⁻¹ := by
  unfold PreservesLine
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
  simp [h.1, h.2]

private def realMatrixSubgroup (line : Bool) (R : Type) [CommRing R] :
    Subgroup (SL (Complexification R)) where
  carrier := {g | MatrixCondition line g}
  one_mem' := ⟨isUnitary_one _, fun _ => preservesLine_one _⟩
  mul_mem' {g h} hg hh := ⟨isUnitary_mul hg.1 hh.1, fun hl =>
    ⟨by rw [multiply_line_entry (hh.2 hl), (hg.2 hl).1, zero_mul],
      by rw [multiply_line_entry (hh.2 hl), (hg.2 hl).2, zero_mul]⟩⟩
  inv_mem' hg := ⟨isUnitary_inv hg.1, fun hl => preservesLine_inv (hg.2 hl)⟩

private theorem complexMap_star {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (x : Complexification R) : complexMap f (star x) = star (complexMap f x) := by
  apply QuadraticAlgebra.ext
  · change f (x.re + 0 * x.im) = f x.re + 0 * f x.im
    simp
  · exact map_neg f x.im

private theorem map_conjTranspose {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (M : Matrix (Fin 3) (Fin 3) (Complexification R)) :
    (complexMap f).mapMatrix Mᴴ = ((complexMap f).mapMatrix M)ᴴ := by
  apply Matrix.ext
  intro i j
  exact complexMap_star f _

private def realMatrixMap (line : Bool) {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) :
    realMatrixSubgroup line R →* realMatrixSubgroup line A :=
  ((Matrix.SpecialLinearGroup.map (complexMap f)).comp (realMatrixSubgroup line R).subtype).codRestrict
    (realMatrixSubgroup line A) (fun g => by
      change IsUnitary (Matrix.SpecialLinearGroup.map (complexMap f) g.val) ∧ _
      refine ⟨?_, fun hl => ?_⟩
      · have hg : g.val.valᴴ * J _ * g.val.val = J _ := g.property.1
        have h := congrArg (complexMap f).mapMatrix hg
        simpa only [IsUnitary, Matrix.SpecialLinearGroup.map_apply_coe, map_mul, map_J,
          map_conjTranspose] using h
      · have h : PreservesLine g.val := g.property.2 hl
        exact ⟨(congrArg (complexMap f) h.1).trans (map_zero _),
          (congrArg (complexMap f) h.2).trans (map_zero _)⟩)

private def realMatrixFunctor (line : Bool) : TestAlgebra ℝ ⥤ GrpCat where
  obj R := GrpCat.of (realMatrixSubgroup line R)
  map f := GrpCat.ofHom (realMatrixMap line f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro g; apply Subtype.ext; apply Matrix.SpecialLinearGroup.ext; intros; rfl
  map_comp _ _ := by apply GrpCat.ext; intro g; apply Subtype.ext; apply Matrix.SpecialLinearGroup.ext; intros; rfl

private abbrev definingIdeal (line : Bool) : Ideal MatrixPolynomial :=
  unitaryIdeal ⊔ if line then lineIdeal else ⊥

private def evaluatedMatrix {R : Type} [CommRing R] [Algebra ℝ R]
    (f : MatrixPolynomial →ₐ[ℝ] R) : Matrix (Fin 3) (Fin 3) (Complexification R) :=
  (complexMap f.toRingHom).mapMatrix genericUnitaryMatrix

private theorem vanishes_coefficients {R : Type} [CommRing R] [Algebra ℝ R]
    (f : MatrixPolynomial →ₐ[ℝ] R) (s : Set (Complexification MatrixPolynomial)) :
    (∀ a ∈ Ideal.span (coefficientSet s), f a = 0) ↔
      ∀ x ∈ s, complexMap f.toRingHom x = 0 := by
  constructor
  · intro h x hx
    apply QuadraticAlgebra.ext
    · exact h _ (Ideal.subset_span (Or.inl ⟨x, hx, rfl⟩))
    · exact h _ (Ideal.subset_span (Or.inr ⟨x, hx, rfl⟩))
  · intro h a ha
    have hle : Ideal.span (coefficientSet s) ≤ RingHom.ker f.toRingHom := Ideal.span_le.mpr (by
      rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact congrArg QuadraticAlgebra.re (h x hx)
      · exact congrArg QuadraticAlgebra.im (h x hx))
    exact hle ha

private theorem vanishes_unitary {R : Type} [CommRing R] [Algebra ℝ R]
    (f : MatrixPolynomial →ₐ[ℝ] R) :
    (∀ a ∈ unitaryIdeal, f a = 0) ↔
      (evaluatedMatrix f).det = 1 ∧
      (evaluatedMatrix f)ᴴ * J _ * evaluatedMatrix f = J _ := by
  rw [unitaryIdeal, vanishes_coefficients]
  let a := complexMap f.toRingHom
  let N := genericUnitaryMatrixᴴ * J (Complexification MatrixPolynomial) *
    genericUnitaryMatrix - J (Complexification MatrixPolynomial)
  have hdet : a (genericUnitaryMatrix.det - 1) = (evaluatedMatrix f).det - 1 := by
    rw [map_sub, map_one, RingHom.map_det]
    rfl
  have hN (i j : Fin 3) : a (N i j) =
      ((evaluatedMatrix f)ᴴ * J (Complexification R) * evaluatedMatrix f - J (Complexification R)) i j := by
    change a.mapMatrix N i j = _
    simp only [N, evaluatedMatrix, a, map_sub, map_mul, map_J, map_conjTranspose, Matrix.sub_apply]
  constructor
  · intro h
    refine ⟨sub_eq_zero.mp (hdet.symm.trans (h _ (Or.inl rfl))), sub_eq_zero.mp ?_⟩
    apply Matrix.ext
    intro i j
    rw [← hN]
    exact h _ (Or.inr ⟨(i, j), rfl⟩)
  · rintro ⟨hd, h⟩ _ (rfl | ⟨⟨i, j⟩, rfl⟩)
    · rw [hdet, hd, sub_self]
    · change a (N i j) = _
      rw [hN, h, sub_self]
      rfl

private theorem vanishes_line {R : Type} [CommRing R] [Algebra ℝ R]
    (f : MatrixPolynomial →ₐ[ℝ] R) :
    (∀ a ∈ lineIdeal, f a = 0) ↔
      evaluatedMatrix f 1 0 = 0 ∧ evaluatedMatrix f 2 0 = 0 := by
  rw [lineIdeal, vanishes_coefficients]
  exact ⟨fun h => ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩, by
    rintro ⟨h₁, h₂⟩ _ (rfl | rfl)
    · exact h₁
    · exact h₂⟩

private theorem vanishes_defining {R : Type} [CommRing R] [Algebra ℝ R]
    (line : Bool) (f : MatrixPolynomial →ₐ[ℝ] R) :
    (∀ a ∈ definingIdeal line, f a = 0) ↔
      (evaluatedMatrix f).det = 1 ∧
      (evaluatedMatrix f)ᴴ * J _ * evaluatedMatrix f = J _ ∧
      (line = true → evaluatedMatrix f 1 0 = 0 ∧ evaluatedMatrix f 2 0 = 0) := by
  change (definingIdeal line ≤ RingHom.ker f.toRingHom) ↔ _
  have h₁ := vanishes_unitary f
  have h₂ := vanishes_line f
  cases line
  · have hzero : definingIdeal false = unitaryIdeal := by simp [definingIdeal]
    rw [hzero]
    change (∀ a ∈ unitaryIdeal, f a = 0) ↔ _
    simpa only [Bool.false_eq_true, false_implies, and_true] using h₁
  · change (unitaryIdeal ⊔ lineIdeal ≤ RingHom.ker f.toRingHom) ↔ _
    rw [sup_le_iff]
    change ((∀ a ∈ unitaryIdeal, f a = 0) ∧ (∀ a ∈ lineIdeal, f a = 0)) ↔ _
    simp only [h₁, h₂, and_assoc, forall_const]

private abbrev coordinateQuotient (line : Bool) : MatrixPolynomial →ₐ[ℝ] Coordinates line :=
  Ideal.Quotient.mkₐ ℝ (definingIdeal line)

private def matrixEvaluation {R : Type} [CommRing R] [Algebra ℝ R]
    (g : Matrix (Fin 3) (Fin 3) (Complexification R)) : MatrixPolynomial →ₐ[ℝ] R :=
  MvPolynomial.aeval fun x : CoordinateIndex =>
    if x.1 then (g x.2.1 x.2.2).im else (g x.2.1 x.2.2).re

private theorem evaluatedMatrix_matrixEvaluation {R : Type} [CommRing R] [Algebra ℝ R]
    (g : Matrix (Fin 3) (Fin 3) (Complexification R)) :
    evaluatedMatrix (matrixEvaluation g) = g := by
  apply Matrix.ext
  intro i j
  apply QuadraticAlgebra.ext <;>
    simp [evaluatedMatrix, matrixEvaluation, RingHom.mapMatrix_apply, complexMap, genericUnitaryMatrix]

private theorem matrixEvaluation_evaluatedMatrix {R : Type} [CommRing R] [Algebra ℝ R]
    (f : MatrixPolynomial →ₐ[ℝ] R) : matrixEvaluation (evaluatedMatrix f) = f := by
  apply MvPolynomial.algHom_ext
  rintro ⟨b, i, j⟩
  cases b <;>
    simp [evaluatedMatrix, matrixEvaluation, RingHom.mapMatrix_apply, complexMap, genericUnitaryMatrix]

private def coordinateEquiv (line : Bool) (R : TestAlgebra ℝ) :
    (Coordinates line →ₐ[ℝ] R) ≃ realMatrixSubgroup line R where
  toFun f := by
    let a := f.comp (coordinateQuotient line)
    have ha := (vanishes_defining line a).mp (fun z hz => by
      change f (Ideal.Quotient.mk (definingIdeal line) z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero])
    exact ⟨⟨evaluatedMatrix a, ha.1⟩, ha.2⟩
  invFun g := Ideal.Quotient.liftₐ (definingIdeal line) (matrixEvaluation g.val.val) (by
    apply (vanishes_defining line _).mpr
    rw [evaluatedMatrix_matrixEvaluation]
    exact ⟨g.val.property, g.property.1, g.property.2⟩)
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    rw [Ideal.Quotient.liftₐ_comp]
    exact matrixEvaluation_evaluatedMatrix _
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change evaluatedMatrix ((Ideal.Quotient.liftₐ _ _ _).comp (coordinateQuotient line)) = g.val.val
    rw [Ideal.Quotient.liftₐ_comp, evaluatedMatrix_matrixEvaluation]

private theorem coordinateEquiv_naturality (line : Bool)
    {R A : TestAlgebra ℝ} (f : R ⟶ A) (g : Coordinates line →ₐ[ℝ] R) :
    coordinateEquiv line A (f.hom.comp g) =
      (realMatrixFunctor line).map f (coordinateEquiv line R g) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

open private Representation spectrumPointsIso from LinearAlgebraicGroups.Affine.StandardGroups
open private Representation.mk Representation.operations Representation.convolutionIso from LinearAlgebraicGroups.Affine.StandardGroups

private def realGroupRepresentation (line : Bool) :
    Representation (Coordinates line) (realMatrixFunctor line) :=
  Representation.mk (coordinateEquiv line) (coordinateEquiv_naturality line)

private def unitaryOperations (line : Bool) :
    Specs.StandardGroups.HopfOperations ℝ (Coordinates line) :=
  Representation.operations (realGroupRepresentation line)

private def representedGroup (line : Bool) : AffineAlgebraicGroup ℝ :=
  letI := (unitaryOperations line).hopf
  Specs.StandardGroups.spectrum ℝ (Coordinates line)

private def representedGroupPointIso (line : Bool) :
    (groupPointsFunctor ℝ).obj (representedGroup line).val ≅ realMatrixFunctor line :=
  letI := (unitaryOperations line).hopf
  spectrumPointsIso (Representation.convolutionIso (realGroupRepresentation line))

theorem realGroupModels : RealGroupModels := by
  intro line
  refine ⟨unitaryOperations line, fun R => ((representedGroupPointIso line).app R).groupIsoToMulEquiv.toEquiv,
    ?_, ?_⟩
  · intro R A f g
    exact congrArg Subtype.val (GrpCat.ext_iff.mp
      ((representedGroupPointIso line).hom.naturality f) g)
  · intro R g h
    exact congrArg Subtype.val (map_mul ((representedGroupPointIso line).app R).groupIsoToMulEquiv g h)


private theorem lineIdeal_le : definingIdeal false ≤ definingIdeal true := by
  simp [definingIdeal]

private def lineQuotient : Coordinates false →ₐ[ℝ] Coordinates true :=
  Ideal.Quotient.factorₐ ℝ lineIdeal_le

private def includeLinePoint (R : TestAlgebra ℝ) :
    realMatrixSubgroup true R →* realMatrixSubgroup false R :=
  Subgroup.inclusion (fun _ h => ⟨h.1, fun hf => by cases hf⟩)

private theorem coordinateEquiv_lineQuotient (R : TestAlgebra ℝ) (f : Coordinates true →ₐ[ℝ] R) :
    coordinateEquiv false R (f.comp lineQuotient) = includeLinePoint R (coordinateEquiv true R f) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intros
  rfl

open private Representation.compatible from LinearAlgebraicGroups.Affine.StandardGroups

private def lineQuotientHopf :
    letI := (unitaryOperations false).hopf
    letI := (unitaryOperations true).hopf
    CommHopfAlgCat.of ℝ (Coordinates false) ⟶ CommHopfAlgCat.of ℝ (Coordinates true) := by
  letI := (unitaryOperations false).hopf
  letI := (unitaryOperations true).hopf
  obtain ⟨hΔ, hε, _⟩ :=
    Representation.compatible (realGroupRepresentation false) (realGroupRepresentation true)
      lineQuotient includeLinePoint coordinateEquiv_lineQuotient
  exact CommHopfAlgCat.ofHom (BialgHom.ofAlgHom lineQuotient hε.symm hΔ)

private def lineSubgroup : ClosedSubgroup (representedGroup false).val :=
  { group := (representedGroup true).val
    inclusion := specGroupMap lineQuotientHopf
    isClosedImmersion := IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.factor_surjective lineIdeal_le) }

private theorem inclusion_evaluation (line : Bool) (R : TestAlgebra ℝ)
    (f : Coordinates line →ₐ[ℝ] R) :
    letI := (unitaryOperations line).hopf
    let A := CommHopfAlgCat.of ℝ (Coordinates line)
    (representedGroupPointIso line).hom.app R
      ((hopfSpecPointIso A).hom.app R (WithConv.toConv f)) =
    coordinateEquiv line R f := by
  letI := (unitaryOperations line).hopf
  let A := CommHopfAlgCat.of ℝ (Coordinates line)
  have he := ((hopfSpecPointIso A).app R).groupIsoToMulEquiv.symm_apply_apply (WithConv.toConv f)
  change (hopfSpecPointIso A).inv.app R
    ((hopfSpecPointIso A).hom.app R (WithConv.toConv f)) = WithConv.toConv f at he
  exact congrArg (fun p : WithConv (Coordinates line →ₐ[ℝ] R) => coordinateEquiv line R p.ofConv) he

private theorem inclusion_line_point (R : TestAlgebra ℝ) (p : Points lineSubgroup.group.X R) :
    (representedGroupPointIso false).hom.app R (p ≫ lineSubgroup.inclusion.hom.hom) =
      includeLinePoint R ((representedGroupPointIso true).hom.app R p) := by
  letI := (unitaryOperations false).hopf
  letI := (unitaryOperations true).hopf
  let A := CommHopfAlgCat.of ℝ (Coordinates false)
  let B := CommHopfAlgCat.of ℝ (Coordinates true)
  let e := hopfSpecPointIso B
  obtain ⟨f, hp⟩ := ((e.app R).groupIsoToMulEquiv.surjective) p
  change (e.hom.app R) f = p at hp
  have hmap :
      (e.hom.app R) f ≫ lineSubgroup.inclusion.hom.hom =
        (hopfSpecPointIso A).hom.app R (WithConv.toConv (f.ofConv.comp lineQuotient)) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom lineQuotient.toRingHom) =
      Spec.map (CommRingCat.ofHom ((f.ofConv.comp lineQuotient).toRingHom))
    exact (Spec.map_comp _ _).symm
  let E₀ := (representedGroupPointIso false).hom.app R
  let E₁ := (representedGroupPointIso true).hom.app R
  have h₀ : E₀ ((hopfSpecPointIso A).hom.app R (WithConv.toConv (f.ofConv.comp lineQuotient))) =
      coordinateEquiv false R (f.ofConv.comp lineQuotient) :=
    inclusion_evaluation false R (f.ofConv.comp lineQuotient)
  have h₁ : E₁ (e.hom.app R f) = coordinateEquiv true R f.ofConv :=
    inclusion_evaluation true R f.ofConv
  have hh := congrArg (fun p : Points lineSubgroup.group.X R => E₀
    (p ≫ lineSubgroup.inclusion.hom.hom)) hp.symm
  have he := congrArg (fun p : Points (representedGroup false).val.X R => E₀ p) hmap
  have ht := h₁.symm.trans (congrArg (fun p : Points lineSubgroup.group.X R => E₁ p) hp)
  exact hh.trans (he.trans (h₀.trans ((coordinateEquiv_lineQuotient R _).trans
    (congrArg (includeLinePoint R) ht))))

private theorem lineSubgroup_range (R : TestAlgebra ℝ)
    (g : Points (representedGroup false).val.X R) :
    (∃ p : Points lineSubgroup.group.X R, p ≫ lineSubgroup.inclusion.hom.hom = g) ↔
      PreservesLine ((representedGroupPointIso false).hom.app R g).val := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [inclusion_line_point]
    exact ((representedGroupPointIso true).hom.app R p).property.2 rfl
  · intro h
    let x := (representedGroupPointIso false).hom.app R g
    let y : realMatrixSubgroup true R := ⟨x.val, x.property.1, fun _ => h⟩
    let p := (representedGroupPointIso true).inv.app R y
    have hp : (representedGroupPointIso true).hom.app R p = y :=
      ((representedGroupPointIso true).app R).groupIsoToMulEquiv.apply_symm_apply y
    refine ⟨p, ((representedGroupPointIso false).app R).groupIsoToMulEquiv.injective ?_⟩
    change (representedGroupPointIso false).hom.app R (p ≫ _) = x
    exact (inclusion_line_point R p).trans (congrArg (includeLinePoint R) hp)

private theorem firstCoordinate_natural {R A : TestAlgebra ℂ} (f : R ⟶ A)
    (x : Complexification R) :
    firstCoordinate A (complexMap f.hom.toRingHom x) = f.hom (firstCoordinate R x) := by
  change f.hom x.re + f.hom x.im * algebraMap ℂ A Complex.I =
    f.hom (x.re + x.im * algebraMap ℂ R Complex.I)
  rw [map_add, map_mul, AlgHom.commutes]

private def complexGroupMulEquiv (R : TestAlgebra ℂ) :
    realMatrixSubgroup false R ≃* SL R where
  toEquiv := (Equiv.subtypeEquivRight (fun _ => ⟨And.left, fun h => ⟨h, fun hfalse => by cases hfalse⟩⟩)).trans
    (complexGroupEquiv R)
  map_mul' := fun x y => (Matrix.SpecialLinearGroup.map (firstCoordinate R)).map_mul x.val y.val

private def complexGroupPointIso :
    restrictTestAlgebra ℝ ℂ ⋙ realMatrixFunctor false ≅ Specs.StandardGroups.specialLinearPoints ℂ (Fin 3) :=
  NatIso.ofComponents (fun R => (complexGroupMulEquiv R).toGrpIso) (by
    intro R A f
    apply GrpCat.ext
    intro x
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact firstCoordinate_natural f (x.val.val i j))

private def liftIndex (R : Type) [CommRing R] :
    SL R ≃* Matrix.SpecialLinearGroup (Specs.Unipotent.Index.{0} 3) R where
  toFun g := ⟨g.val.submatrix ULift.down ULift.down,
    (Matrix.det_submatrix_equiv_self Equiv.ulift g.val).trans g.property⟩
  invFun g := ⟨g.val.submatrix ULift.up ULift.up,
    (Matrix.det_submatrix_equiv_self Equiv.ulift.symm g.val).trans g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrFun (congrFun ((Matrix.reindexRingEquiv R (Equiv.ulift.symm : Fin 3 ≃ Specs.Unipotent.Index.{0} 3)).map_mul g.val h.val) i) j

private def liftIndicesIso :
    Specs.StandardGroups.specialLinearPoints ℂ (Fin 3) ≅
      Specs.StandardGroups.specialLinearPoints ℂ (Specs.Unipotent.Index.{0} 3) :=
  NatIso.ofComponents (fun R => (liftIndex R).toGrpIso) (by
    intros
    apply GrpCat.ext
    intro x
    apply Matrix.SpecialLinearGroup.ext
    intros
    rfl)

private abbrev complexSL : AffineAlgebraicGroup ℂ :=
  StandardGroups.specialLinearGroup ℂ (Specs.Unipotent.Index.{0} 3)

private def complexSLPoints : Specs.GeneralLinearStructure.SpecialMatrixPoints complexSL 3 :=
  StandardGroups.specialLinearGroupPointsIso ℂ (Specs.Unipotent.Index.{0} 3)

private def realPointsAtComplexIso (G : GroupScheme ℝ) :
    (groupPointsFunctor ℂ).obj ((groupBaseChange ℝ ℂ).obj G) ≅
      restrictTestAlgebra ℝ ℂ ⋙ (groupPointsFunctor ℝ).obj G :=
  NatIso.ofComponents (fun R => (baseChangePointGroupEquiv ℂ G R).toGrpIso) (by
    intro R A f
    apply GrpCat.ext
    exact baseChangePointsNaturality ℝ ℂ G.X f)

private def comparisonPoints :
    (groupPointsFunctor ℂ).obj ((groupBaseChange ℝ ℂ).obj (representedGroup false).val) ≅
      (groupPointsFunctor ℂ).obj complexSL.val :=
  realPointsAtComplexIso _ ≪≫ Functor.isoWhiskerLeft _ (representedGroupPointIso false) ≪≫
    complexGroupPointIso ≪≫ liftIndicesIso ≪≫ complexSLPoints.symm

private abbrev complexUnitary : AffineAlgebraicGroup ℂ :=
  Specs.Unipotent.baseChangedAlgebraicGroup ℂ (representedGroup false)

private theorem iso_of_group_points {k : Type} [Field k] {G H : AffineAlgebraicGroup k}
    (p : (groupPointsFunctor k).obj G.val ≅ (groupPointsFunctor k).obj H.val) :
    ∃ e : G.val ≅ H.val, (groupPointsFunctor k).map e.hom = p.hom := by
  let f := (AffineAlgebraicGroup.groupHomEquiv G H).symm p.hom
  let g := (AffineAlgebraicGroup.groupHomEquiv H G).symm p.inv
  have hf : (groupPointsFunctor k).map f = p.hom :=
    (AffineAlgebraicGroup.groupHomEquiv G H).apply_symm_apply _
  have hg : (groupPointsFunctor k).map g = p.inv :=
    (AffineAlgebraicGroup.groupHomEquiv H G).apply_symm_apply _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (groupHomComparison k _ _ G.property.1).injective
    change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map (𝟙 G.val)
    rw [Functor.map_comp, hf, hg]
    exact p.hom_inv_id.trans ((groupPointsFunctor k).map_id _).symm
  · apply (groupHomComparison k _ _ H.property.1).injective
    change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map (𝟙 H.val)
    rw [Functor.map_comp, hg, hf]
    exact p.inv_hom_id.trans ((groupPointsFunctor k).map_id _).symm

private def complexSchemeIso : complexUnitary.val ≅ complexSL.val :=
  (iso_of_group_points (G := complexUnitary) (H := complexSL) comparisonPoints).choose

set_option maxHeartbeats 3000000 in
private theorem complexSchemeIso_eval (R : TestAlgebra ℂ) (g : Points complexUnitary.val.X R)
    (i j : Fin 3) :
    (complexSLPoints.hom.app R (g ≫ complexSchemeIso.hom.hom.hom)).val ⟨i⟩ ⟨j⟩ =
      firstCoordinate R (((representedGroupPointIso false).hom.app _
        (baseChangePoint ℝ ℂ _ R g)).val.val i j) := by
  have h : (groupPointsFunctor ℂ).map complexSchemeIso.hom = comparisonPoints.hom :=
    (iso_of_group_points (G := complexUnitary) (H := complexSL) comparisonPoints).choose_spec
  let x : Matrix.SpecialLinearGroup (Specs.Unipotent.Index.{0} 3) R :=
    liftIndex R (complexGroupMulEquiv R ((representedGroupPointIso false).hom.app _
      (baseChangePoint ℝ ℂ _ R g)))
  have he : g ≫ complexSchemeIso.hom.hom.hom = comparisonPoints.hom.app R g :=
    congrArg (fun a => a.app R g) h
  have hx : comparisonPoints.hom.app R g = complexSLPoints.inv.app R x := rfl
  have hSL : complexSLPoints.hom.app R (complexSLPoints.inv.app R x) = x :=
    ((complexSLPoints.app R).groupIsoToMulEquiv).apply_symm_apply x
  exact congrArg (fun y : Matrix.SpecialLinearGroup (Specs.Unipotent.Index.{0} 3) R => y.val ⟨i⟩ ⟨j⟩)
    ((congrArg (fun y : Points complexSL.val.X R => complexSLPoints.hom.app R y)
      (he.trans hx)).trans hSL)

private theorem complex_upper_iff (R : TestAlgebra ℂ) (g : Points complexUnitary.val.X R) :
    PreservesLine ((representedGroupPointIso false).hom.app _
      (baseChangePoint ℝ ℂ _ R g)).val ↔
      (complexSLPoints.hom.app R (g ≫ complexSchemeIso.hom.hom.hom)).val.IsUpperTriangular := by
  let z := (representedGroupPointIso false).hom.app _ (baseChangePoint ℝ ℂ _ R g)
  let x := (complexGroupEquiv R) ⟨z.val, z.property.1⟩
  have h (i j : Fin 3) :
      (complexSLPoints.hom.app R (g ≫ complexSchemeIso.hom.hom.hom)).val ⟨i⟩ ⟨j⟩ = x.val i j :=
    complexSchemeIso_eval R g i j
  have hupper : x.val.IsUpperTriangular ↔
      (complexSLPoints.hom.app R (g ≫ complexSchemeIso.hom.hom.hom)).val.IsUpperTriangular := by
    constructor
    · intro hu i j hij
      cases i with | up i =>
        cases j with | up j =>
          rw [h]
          exact hu hij
    · intro hu i j hij
      rw [← h]
      exact hu (show (⟨j⟩ : Specs.Unipotent.Index.{0} 3) < ⟨i⟩ from hij)
  have hc := complexGroupComparison
  obtain ⟨e, he, _, hp⟩ := hc R
  have heq : e ⟨z.val, z.property.1⟩ = x := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact he _ i j
  rw [← hupper, ← heq]
  exact hp ⟨z.val, z.property.1⟩

private abbrev complexParabolic : AffineAlgebraicGroup ℂ :=
  Specs.Unipotent.baseChangedAlgebraicGroup ℂ (representedGroup true)

private def complexLineInclusion : complexParabolic.val ⟶ complexSL.val :=
  (groupBaseChange ℝ ℂ).map lineSubgroup.inclusion ≫ complexSchemeIso.hom

private theorem complexLineClosed : IsClosedImmersion complexLineInclusion.hom.hom.left := by
  let a := ((groupBaseChange ℝ ℂ).map lineSubgroup.inclusion).hom.hom.left
  let b := complexSchemeIso.hom.hom.hom.left
  have ha : IsClosedImmersion a :=
    baseChangeClosedSubgroup ℝ ℂ lineSubgroup.inclusion lineSubgroup.isClosedImmersion
  have hb : IsIso b :=
    (Grp.forget (SchemeOver ℂ) ⋙ Over.forget _).map_isIso complexSchemeIso.hom
  letI : IsIso b := hb
  letI : IsClosedImmersion b := inferInstance
  exact @IsClosedImmersion.comp _ _ _ a b ha ‹IsClosedImmersion b›

private theorem baseChange_point_range {k K : Type} [Field k] [Field K] [Algebra k K]
    {A G : Specs.GroupScheme k} (i : A ⟶ G) (R : TestAlgebra K)
    (g : Points ((groupBaseChange k K).obj G).X R) :
    (∃ p : Points ((groupBaseChange k K).obj A).X R,
        p ≫ ((groupBaseChange k K).map i).hom.hom = g) ↔
      ∃ p : Points A.X ((restrictTestAlgebra k K).obj R),
        p ≫ i.hom.hom = baseChangePoint k K G.X R g := by
  let e := baseChangePointsEquiv K A.X R
  let f := baseChangePointsEquiv K G.X R
  have he (p : Points ((groupBaseChange k K).obj A).X R) :
      f (p ≫ ((groupBaseChange k K).map i).hom.hom) = e p ≫ i.hom.hom :=
    baseChangePointsSchemeNaturality k K i.hom.hom R p
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨e p, (he p).symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨q, rfl⟩ := e.surjective p
    exact ⟨q, f.injective ((he q).trans hp)⟩

private theorem image_comp_iso {k : Type} [Field k] {Y X Z W : SchemeOver k}
    (i : X ⟶ Y) (e : Y ≅ Z) (p : W ⟶ Z) :
    (∃ q : W ⟶ X, q ≫ (i ≫ e.hom) = p) ↔
      ∃ q : W ⟶ X, q ≫ i = p ≫ e.inv := by
  have hp : (p ≫ e.inv) ≫ e.hom = p := by simp
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, (cancel_mono e.hom).mp ((Category.assoc q i e.hom).trans (hq.trans hp.symm))⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, (Category.assoc q i e.hom).symm.trans ((congrArg (· ≫ e.hom) hq).trans hp)⟩

private theorem complexLine_range (R : TestAlgebra ℂ) (h : Points complexSL.val.X R) :
    (∃ p : Points complexParabolic.val.X R, p ≫ complexLineInclusion.hom.hom = h) ↔
      (complexSLPoints.hom.app R h).val.IsUpperTriangular := by
  let e : complexUnitary.val.X ≅ complexSL.val.X := (Grp.forget (SchemeOver ℂ)).mapIso complexSchemeIso
  let g : Points complexUnitary.val.X R := h ≫ e.inv
  have hg : g ≫ e.hom = h := by
    change (h ≫ e.inv) ≫ e.hom = h
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  exact (image_comp_iso ((groupBaseChange ℝ ℂ).map lineSubgroup.inclusion).hom.hom e h).trans
    ((baseChange_point_range lineSubgroup.inclusion R g).trans
      ((lineSubgroup_range ((restrictTestAlgebra ℝ ℂ).obj R) _).trans
        ((complex_upper_iff R g).trans (Iff.of_eq
          (congrArg (fun p : Points complexSL.val.X R =>
            (complexSLPoints.hom.app R p).val.IsUpperTriangular) hg)))))

open private Unipotent.factor_through_closed
  from LinearAlgebraicGroups.Unipotent.CentralSeries
open private subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag

private theorem complexLine_borel
    {T : Specs.SpecialLinearDatum.DiagonalTorus complexSLPoints}
    {L : Specs.SpecialLinearDatum.LatticeIdentification T}
    {M : Specs.SpecialLinearDatum.RootIdentification T L}
    (B : Specs.SpecialLinearDatum.UpperTriangularBorel T L M) :
    ∃ p : complexParabolic.val ≅ B.limits.parabolic.group,
      p.hom ≫ B.limits.parabolic.inclusion = complexLineInclusion := by
  let H := Specs.Unipotent.closedSubgroupAlgebraicGroup B.limits.parabolic
  obtain ⟨f, hf⟩ := Unipotent.factor_through_closed (A := complexParabolic) (B := H)
      (C := complexSL) complexLineInclusion B.limits.parabolic.inclusion
      B.limits.parabolic.isClosedImmersion (fun R x =>
        (B.matrix R _).mpr ((complexLine_range R _).mp ⟨x, rfl⟩))
  obtain ⟨g, hg⟩ := Unipotent.factor_through_closed (A := H) (B := complexParabolic)
      (C := complexSL) B.limits.parabolic.inclusion complexLineInclusion
      complexLineClosed (fun R x => (complexLine_range R _).mpr ((B.matrix R _).mp ⟨x, rfl⟩))
  let P : ClosedSubgroup complexSL.val :=
    ⟨complexParabolic.val, complexLineInclusion, complexLineClosed⟩
  exact subgroupIso_of_same (A := P) (B := B.limits.parabolic) ⟨⟨f, hf⟩, ⟨g, hg⟩⟩

open private specialLinearRepresentation from LinearAlgebraicGroups.Affine.StandardGroups

open Specs.SpecialLinearDatum

private theorem root_dot (i j : Fin 3) (y : CocharacterLattice 3) :
    dotPairing 3 (root 3 i j) y = y.val i - y.val j := by
  change (∑ l : Fin 3, (coordinate 3 i - coordinate 3 j) l * y.val l) = _
  simp [coordinate, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
    Pi.single_apply, ite_mul, Finset.sum_ite_eq']

private theorem exponents_eq (i : Fin 3) : (coroot 3 0 2).val i = (![1, 0, -1] : Fin 3 → ℤ) i := by
  fin_cases i <;> decide

private theorem root_add :
    root 3 0 1 + root 3 1 2 = root 3 0 2 := by
  unfold root
  rw [← map_add]
  congr 1
  abel

private theorem root_range :
    Set.range (fun p : RootIndices 3 => dotPairing 3 (root 3 p.val.1 p.val.2) (coroot 3 0 2)) =
      ({1, -1, 2, -2} : Set ℤ) := by
  ext n
  constructor
  · rintro ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
    dsimp only at hij ⊢
    rw [root_dot, exponents_eq, exponents_eq]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases i <;> fin_cases j <;> (first | contradiction | decide)
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨⟨(0, 1), by decide⟩, by dsimp only; rw [root_dot, exponents_eq, exponents_eq]; decide⟩
    · exact ⟨⟨(1, 0), by decide⟩, by dsimp only; rw [root_dot, exponents_eq, exponents_eq]; decide⟩
    · exact ⟨⟨(0, 2), by decide⟩, by dsimp only; rw [root_dot, exponents_eq, exponents_eq]; decide⟩
    · exact ⟨⟨(2, 0), by decide⟩, by dsimp only; rw [root_dot, exponents_eq, exponents_eq]; decide⟩


private def diagonalUnits {R : Type*} [CommRing R] (t : Rˣ) : Fin 3 → R :=
  ![(t : R), 1, (↑t⁻¹ : R)]

private def splitMatrix {R : Type*} [CommRing R] (t : Rˣ) : SL (Complexification R) :=
  ⟨Matrix.diagonal (fun i => algebraMap R (Complexification R) (diagonalUnits t i)), by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp [diagonalUnits, ← map_mul]⟩

private theorem splitMatrix_unitary {R : Type*} [CommRing R] (t : Rˣ) :
    IsUnitary (splitMatrix t) := by
  let d := fun i : Fin 3 => algebraMap R (Complexification R) (diagonalUnits t i)
  have hs (a : R) : star (algebraMap R (Complexification R) a) = algebraMap R _ a := by
    apply QuadraticAlgebra.ext <;> simp
  change (Matrix.diagonal d)ᴴ * J _ * Matrix.diagonal d = J _
  rw [Matrix.diagonal_conjTranspose]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply, d, hs]
  fin_cases i <;> fin_cases j <;> simp [J, diagonalUnits, ← map_mul]

private def splitPoints (R : TestAlgebra ℝ) : Rˣ →* realMatrixSubgroup false R where
  toFun t := ⟨splitMatrix t, splitMatrix_unitary t, fun h => by cases h⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Matrix.diagonal (fun i => algebraMap R (Complexification R) (diagonalUnits 1 i)) i j =
      (1 : Matrix (Fin 3) (Fin 3) (Complexification R)) i j
    have h (k : Fin 3) : diagonalUnits (1 : Rˣ) k = 1 := by fin_cases k <;> rfl
    simp [h, Matrix.diagonal_one]
  map_mul' t u := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Matrix.diagonal (fun i => algebraMap R (Complexification R) (diagonalUnits (t * u) i)) i j =
      (Matrix.diagonal (fun i => algebraMap R (Complexification R) (diagonalUnits t i)) *
        Matrix.diagonal (fun i => algebraMap R (Complexification R) (diagonalUnits u i))) i j
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    rw [← map_mul]
    congr 1
    fin_cases k <;> simp [diagonalUnits, mul_inv_rev, mul_comm]

private theorem splitPoints_natural {R A : TestAlgebra ℝ} (f : R ⟶ A) (t : Rˣ) :
    (realMatrixFunctor false).map f (splitPoints R t) =
      splitPoints A (Units.map f.hom.toMonoidHom t) := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst j
    change (complexMap f.hom.toRingHom)
      (Matrix.diagonal (fun i => algebraMap R (Complexification R) (diagonalUnits t i)) i i) =
      Matrix.diagonal
        (fun i => algebraMap A (Complexification A) (diagonalUnits (Units.map f.hom.toMonoidHom t) i)) i i
    simp only [Matrix.diagonal_apply_eq]
    apply QuadraticAlgebra.ext <;> fin_cases i <;> simp [diagonalUnits, complexMap]
    · exact map_one f.hom
    · exact map_zero f.hom
  · change (complexMap f.hom.toRingHom)
      (Matrix.diagonal (fun i => algebraMap R (Complexification R) (diagonalUnits t i)) i j) =
      Matrix.diagonal
        (fun i => algebraMap A (Complexification A) (diagonalUnits (Units.map f.hom.toMonoidHom t) i)) i j
    simp [Matrix.diagonal_apply_ne _ hij]

open LaurentPolynomial (T C)
open private multiplicativeRepresentation Representation.equiv from LinearAlgebraicGroups.Affine.StandardGroups

private abbrev LaurentTest := CommAlgCat.of ℝ (LaurentPolynomial ℝ)

private def laurentGenerator : (LaurentPolynomial ℝ)ˣ :=
  (LaurentPolynomial.isUnit_T 1).unit

private theorem laurentGenerator_val : (laurentGenerator : LaurentPolynomial ℝ) = T 1 :=
  (LaurentPolynomial.isUnit_T 1).unit_spec

private theorem laurentGenerator_inv : (↑laurentGenerator⁻¹ : LaurentPolynomial ℝ) = T (-1) := by
  apply laurentGenerator.isUnit.mul_left_cancel
  rw [Units.mul_inv, laurentGenerator_val, ← LaurentPolynomial.T_add]
  simp [LaurentPolynomial.T_zero]

private def splitRestriction : Coordinates false →ₐ[ℝ] LaurentPolynomial ℝ :=
  (coordinateEquiv false LaurentTest).symm (splitPoints LaurentTest laurentGenerator)

private theorem splitRestriction_natural (R : TestAlgebra ℝ) (f : LaurentPolynomial ℝ →ₐ[ℝ] R) :
    coordinateEquiv false R (f.comp splitRestriction) =
      splitPoints R (Representation.equiv (multiplicativeRepresentation ℝ) R f) := by
  let a : LaurentTest ⟶ R := CommAlgCat.ofHom f
  exact (coordinateEquiv_naturality false a splitRestriction).trans <|
    (congrArg ((realMatrixFunctor false).map a)
      ((coordinateEquiv false LaurentTest).apply_symm_apply _)).trans <|
    splitPoints_natural a laurentGenerator

private theorem splitRestriction_surjective : Function.Surjective splitRestriction := by
  let F := splitRestriction.range
  have hM : evaluatedMatrix (splitRestriction.comp (coordinateQuotient false)) =
      (splitMatrix laurentGenerator).val := by
    exact congrArg (fun x : realMatrixSubgroup false (LaurentPolynomial ℝ) => x.val.val)
      ((coordinateEquiv false LaurentTest).apply_symm_apply _)
  have h1 : (T 1 : LaurentPolynomial ℝ) ∈ F := by
    refine ⟨coordinateQuotient false (MvPolynomial.X (false, 0, 0)), ?_⟩
    have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) (Complexification (LaurentPolynomial ℝ)) =>
      (m 0 0).re) hM
    exact h.trans laurentGenerator_val
  have hm1 : (T (-1) : LaurentPolynomial ℝ) ∈ F := by
    refine ⟨coordinateQuotient false (MvPolynomial.X (false, 2, 2)), ?_⟩
    have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) (Complexification (LaurentPolynomial ℝ)) =>
      (m 2 2).re) hM
    exact h.trans laurentGenerator_inv
  intro p
  suffices p ∈ F from this
  refine p.induction_on (fun a => F.algebraMap_mem a) (fun hp hq => F.add_mem hp hq) ?_ ?_
  · intro n a h
    rw [LaurentPolynomial.T_add, ← mul_assoc]
    exact F.mul_mem h h1
  · intro n a h
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc]
    exact F.mul_mem h hm1

private def splitHopfMap :
    letI := (unitaryOperations false).hopf
    letI := StandardGroups.multiplicativeHopf ℝ
    CommHopfAlgCat.of ℝ (Coordinates false) ⟶ CommHopfAlgCat.of ℝ (LaurentPolynomial ℝ) := by
  letI := (unitaryOperations false).hopf
  letI := StandardGroups.multiplicativeHopf ℝ
  obtain ⟨hΔ, hε, _⟩ :=
    Representation.compatible (realGroupRepresentation false) (multiplicativeRepresentation ℝ)
      splitRestriction splitPoints splitRestriction_natural
  exact @CommHopfAlgCat.ofHom ℝ _ (Coordinates false) (LaurentPolynomial ℝ) _ _
    (unitaryOperations false).hopf (StandardGroups.multiplicativeHopf ℝ)
    (@BialgHom.ofAlgHom ℝ (Coordinates false) (LaurentPolynomial ℝ) _ _ _
      (unitaryOperations false).hopf.toBialgebra (StandardGroups.multiplicativeHopf ℝ).toBialgebra
      splitRestriction hε.symm hΔ)

private def splitSubgroup : ClosedSubgroup (representedGroup false).val where
  group := (StandardGroups.multiplicativeGroup ℝ).val
  inclusion := specGroupMap splitHopfMap
  isClosedImmersion := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom splitRestriction.toRingHom))
    exact IsClosedImmersion.spec_of_surjective _ splitRestriction_surjective

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)
open private unitEquiv unitEquiv_unitPoint subgroupInclusionFactors
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private toMultiplicativeGroup_points
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private abbrev multLine (k : Type) [Field k] := specGroup (groupAlgebra k IntegerCharacters)

private def splitIso : multLine ℝ ≅ splitSubgroup.group :=
  DiagonalizableGroups.multiplicativeGroupIso ℝ

private theorem hopfPoint_map {k : Type} [Field k] {A B : HopfAlgebraCategory k}
    (f : A ⟶ B) (R : TestAlgebra k) (x : B →ₐ[k] R) :
    (hopfSpecPointIso B).hom.app R (WithConv.toConv x) ≫ (specGroupMap f).hom.hom =
      (hopfSpecPointIso A).hom.app R (WithConv.toConv (x.comp f.hom.toAlgHom)) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom x.toRingHom)).symm

private abbrev splitUnits :=
  StandardGroups.multiplicativeGroupPointsIso ℝ

private theorem splitUnits_hopfPoint (R : TestAlgebra ℝ) (f : LaurentPolynomial ℝ →ₐ[ℝ] R) :
    letI := StandardGroups.multiplicativeHopf ℝ
    splitUnits.hom.app R ((hopfSpecPointIso (CommHopfAlgCat.of ℝ (LaurentPolynomial ℝ))).hom.app R
      (WithConv.toConv f)) = Representation.equiv (multiplicativeRepresentation ℝ) R f := by
  letI := StandardGroups.multiplicativeHopf ℝ
  let A := CommHopfAlgCat.of ℝ (LaurentPolynomial ℝ)
  exact congrArg
    (fun p : WithConv (LaurentPolynomial ℝ →ₐ[ℝ] R) ↦
      Representation.equiv (multiplicativeRepresentation ℝ) R p.ofConv)
    (((hopfSpecPointIso A).app R).groupIsoToMulEquiv.symm_apply_apply (WithConv.toConv f))

private theorem splitSubgroup_point (R : TestAlgebra ℝ) (p : Points splitSubgroup.group.X R) :
    (representedGroupPointIso false).hom.app R (p ≫ splitSubgroup.inclusion.hom.hom) =
      splitPoints R (splitUnits.hom.app R p) := by
  letI := StandardGroups.multiplicativeHopf ℝ
  let A := CommHopfAlgCat.of ℝ (LaurentPolynomial ℝ)
  obtain ⟨f, rfl⟩ := ((hopfSpecPointIso A).app R).groupIsoToMulEquiv.surjective p
  have hp := hopfPoint_map splitHopfMap R f.ofConv
  change (hopfSpecPointIso A).hom.app R f ≫ splitSubgroup.inclusion.hom.hom =
    (hopfSpecPointIso _).hom.app R (WithConv.toConv (f.ofConv.comp splitRestriction)) at hp
  exact (congrArg (fun p : Points (representedGroup false).val.X R =>
    (representedGroupPointIso false).hom.app R p) hp).trans
      ((inclusion_evaluation false R _).trans ((splitRestriction_natural R f.ofConv).trans
        (congrArg (splitPoints R) (splitUnits_hopfPoint R f.ofConv).symm)))

private theorem splitIso_unit (R : TestAlgebra ℝ) (t : Rˣ) :
    splitUnits.hom.app R (unitPoint R t ≫ splitIso.hom.hom.hom) = t := by
  have h := toMultiplicativeGroup_points (StandardGroups.multiplicativeGroup ℝ) splitUnits
  have he := congrArg (fun q => q.app R (unitPoint R t)) h
  exact he.trans (unitEquiv_unitPoint R t)

private theorem splitPoint_formula (R : TestAlgebra ℝ) (t : Rˣ) :
    (representedGroupPointIso false).hom.app R
      ((unitPoint R t ≫ splitIso.hom.hom.hom) ≫ splitSubgroup.inclusion.hom.hom) =
      splitPoints R t := by
  exact (splitSubgroup_point R _).trans (congrArg (splitPoints R) (splitIso_unit R t))

private theorem splitSubgroup_isSplit : IsSplitTorus splitSubgroup.group := by
  let k := ℝ
  let I := ULift.{0} (Fin 1)
  let A := StandardGroups.multiplicativeGroup k
  let B := StandardGroups.multiplicativePowerGroup k I
  letI : Unique I := inferInstanceAs (Unique (ULift.{0} (Fin 1)))
  let p : Specs.StandardGroups.multiplicativePoints k ≅ Specs.StandardGroups.multiplicativePowerPoints k I :=
    NatIso.ofComponents (fun (R : TestAlgebra k) => (MulEquiv.funUnique (α := I) (M := Rˣ)).symm.toGrpIso) (by
      intro R T f
      apply GrpCat.ext
      intro x
      rfl)
  let e := splitUnits ≪≫ p ≪≫ (StandardGroups.multiplicativePowerGroupPointsIso k I).symm
  obtain ⟨h, _⟩ := iso_of_group_points (G := A) (H := B) e
  exact ⟨1, ⟨h⟩⟩

private theorem splitSubgroup_in_line : IsSubgroupOf splitSubgroup lineSubgroup := by
  apply subgroupInclusionFactors (StandardGroups.multiplicativeGroup ℝ).property.1
    lineSubgroup splitSubgroup.inclusion
  intro R p
  apply (lineSubgroup_range R _).mpr
  exact (congrArg (fun x : realMatrixSubgroup false R => PreservesLine x.val)
    (splitSubgroup_point R p)).symm ▸
      ⟨Matrix.diagonal_apply_ne _ (by decide), Matrix.diagonal_apply_ne _ (by decide)⟩



section Minimal

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open Specs.GeometricRadicals (IsReductive)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel IsSmoothConnectedSolvable)
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.RankOneFlag (SameSubgroup)
open private reductive_of_groupIso extendSubgroup extend_subgroupOf subgroupOf_of_extend
  borel_of_same from LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private fieldSpecMap_surjective from LinearAlgebraicGroups.Affine.Stabilizers
open private geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private smooth_baseChange_iff from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private isKBorel_iff_of_isAlgClosed groupObjectsFunctor_isEquivalence
  schemeBaseChange_isEquivalence extendRationalEquiv connected_extend_iso_iff
  smoothConnectedSolvable_of_iso closedImmersion_of_extend_iso
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private solvable_iff_sections from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private groupBaseChangeTowerIso from LinearAlgebraicGroups.Relative.RationalCocharacter
open private borelUnderIso from LinearAlgebraicGroups.Relative.ParabolicIntersection
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem unitary_reductive (h : IsReductive complexSL) :
    IsReductive (representedGroup false) := by
  let G := representedGroup false
  have hC : IsReductive (baseChangedAlgebraicGroup ℂ G) :=
    reductive_of_groupIso complexSchemeIso.symm h
  have hs : Smooth G.val.X.hom := (smooth_baseChange_iff (K := ℂ) G.val.X).mp hC.1
  letI : Surjective (fieldSpecMap ℝ ℂ) := fieldSpecMap_surjective ℂ
  letI : GeometricallyConnected (baseChangedAlgebraicGroup ℂ G).val.X.hom := hC.2.1
  letI : ConnectedSpace ((baseChange ℝ ℂ).obj G.val.X).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (baseChangedAlgebraicGroup ℂ G).val.X.hom
  letI : ConnectedSpace ↥(pullback G.val.X.hom (fieldSpecMap ℝ ℂ)) :=
    inferInstanceAs (ConnectedSpace ((baseChange ℝ ℂ).obj G.val.X).left)
  have hc : ConnectedSpace G.val.X.left :=
    (pullback.fst G.val.X.hom (fieldSpecMap ℝ ℂ)).surjective.connectedSpace
      (pullback.fst G.val.X.hom (fieldSpecMap ℝ ℂ)).continuous
  letI : ConnectedSpace G.val.X.left := hc
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := ℂ) G hs
    (geometricallyConnected_of_connected G)).mp hC

section IsomorphicFields

variable {k K : Type} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    [IsIso (fieldSpecMap k K)]

private theorem solvableSubgroup_extend_iff {A : AffineAlgebraicGroup k}
    (B : ClosedSubgroup A.val) :
    IsSmoothConnectedSolvable (extendSubgroup K B) ↔ IsSmoothConnectedSolvable B := by
  let D := closedSubgroupAlgebraicGroup B
  let E := closedSubgroupAlgebraicGroup
    (G := baseChangedAlgebraicGroup K A) (extendSubgroup K B)
  let q := extendRationalEquiv K D.val
  let hs := smooth_baseChange_iff (K := K) D.val.X
  let hc := connected_extend_iso_iff K D.val.X
  constructor
  · rintro ⟨hs', hc', hb⟩
    letI : Group.IsSolvable (𝟙_ (SchemeOver K) ⟶ ((groupBaseChange k K).obj D.val).X) :=
      (solvable_iff_sections E hs' hc').mp hb
    exact ⟨hs.mp hs', hc.mp hc', (solvable_iff_sections D (hs.mp hs') (hc.mp hc')).mpr
      (Group.isSolvable_of_surjective (f := q.symm.toMonoidHom) q.symm.surjective)⟩
  · rintro ⟨hs', hc', hb⟩
    haveI := (solvable_iff_sections D hs' hc').mp hb
    exact ⟨hs.mpr hs', hc.mpr hc', (solvable_iff_sections E (hs.mpr hs') (hc.mpr hc')).mpr
      (Group.isSolvable_of_surjective (f := q.toMonoidHom) q.surjective)⟩

private theorem borel_extend_of_fieldIso (A : AffineAlgebraicGroup k)
    (B : ClosedSubgroup A.val) (hB : IsBorel B) :
    IsBorel (extendSubgroup K B) := by
  let F := groupBaseChange k K
  letI : (baseChange k K).IsEquivalence := schemeBaseChange_isEquivalence K
  letI : F.IsEquivalence := groupObjectsFunctor_isEquivalence (baseChange k K)
  refine ⟨(solvableSubgroup_extend_iff B).mpr hB.1, ?_⟩
  intro C hC hBC
  let J := F.asEquivalence.inverse.obj C.group
  let e : F.obj J ≅ C.group := F.asEquivalence.counitIso.app C.group
  let i : J ⟶ A.val := F.preimage (e.hom ≫ C.inclusion)
  have hi : F.map i = e.hom ≫ C.inclusion := F.map_preimage (e.hom ≫ C.inclusion)
  have hc : IsClosedImmersion i.hom.hom.left := by
    apply closedImmersion_of_extend_iso K
    change IsClosedImmersion (F.map i).hom.hom.left
    rw [hi]
    letI : IsIso e.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
    exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance C.isClosedImmersion
  let D : ClosedSubgroup A.val := ⟨J, i, hc⟩
  have he : e.hom ≫ C.inclusion = (extendSubgroup K D).inclusion := hi.symm
  have hCD : IsSubgroupOf C (extendSubgroup K D) := ⟨e.inv, by rw [← he, e.inv_hom_id_assoc]⟩
  have hD : IsSmoothConnectedSolvable D := (solvableSubgroup_extend_iff D).mp <|
    smoothConnectedSolvable_of_iso
      (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K A) C)
      (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K A) (extendSubgroup K D))
      e.symm hC
  have hBD : IsSubgroupOf B D := subgroupOf_of_extend (subgroupOf_trans hBC hCD)
  exact subgroupOf_trans hCD (extend_subgroupOf (hB.2 D hD hBD))

end IsomorphicFields

private theorem minimal_of_kBorel {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    (hG : IsReductive G) (P : ClosedSubgroup G.val) (hP : IsKBorel P) :
    IsMinimalParabolic G P := by
  let K := AlgebraicClosure k
  let P' := extendSubgroup K P
  obtain ⟨_, hB : IsBorel P'⟩ := hP
  have hs := (smooth_baseChange_iff (K := K) P.group.X).mp hB.1.1
  refine ⟨⟨hG, hs, P'.isClosedImmersion, P', hB, 𝟙 _, Category.id_comp _⟩, ?_⟩
  intro Q hQ hQP
  let Q' := extendSubgroup K Q
  obtain ⟨_, B, hB', hBQ : IsSubgroupOf B Q'⟩ := hQ.2.2
  have hBP : IsSubgroupOf B P' := subgroupOf_trans hBQ (extend_subgroupOf hQP)
  exact subgroupOf_of_extend (subgroupOf_trans (hB'.2 P' hB.1 hBP) hBQ)

private theorem line_isKBorel {T : DiagonalTorus complexSLPoints}
    {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) :
    IsKBorel lineSubgroup := by
  let K := AlgebraicClosure ℝ
  let f : ℂ →ₐ[ℝ] K := IsAlgClosed.lift
  letI : Algebra ℂ K := f.toRingHom.toAlgebra
  letI : IsScalarTower ℝ ℂ K := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : Algebra.IsIntegral ℂ K := Algebra.IsIntegral.tower_top ℝ
  let a := CommRingCat.ofHom (algebraMap ℂ K)
  letI : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  letI : IsIso (fieldSpecMap ℂ K) := inferInstanceAs (IsIso (Spec.map a))
  let F := groupBaseChange ℂ K
  let E := groupBaseChangeTowerIso (k := ℝ) (K := ℂ) (L := K)
  let C := extendSubgroup K B.limits.parabolic
  let G := representedGroup false
  let H := baseChangedAlgebraicGroup K G
  have hB : IsBorel B.limits.parabolic := (isKBorel_iff_of_isAlgClosed complexSL _).mp B.isBorel
  have hC : IsBorel C := borel_extend_of_fieldIso complexSL B.limits.parabolic hB
  obtain ⟨p, hp⟩ := complexLine_borel B
  let e : H.val ≅ (baseChangedAlgebraicGroup K complexSL).val :=
    (E.app G.val).symm ≪≫ F.mapIso complexSchemeIso
  let D := transportSubgroup e.symm C
  have hD : IsBorel D := borelUnderIso e.symm hC
  let P' := extendSubgroup K lineSubgroup
  let b : P'.group ≅ D.group := (E.app lineSubgroup.group).symm ≪≫ F.mapIso p
  have hn : P'.inclusion ≫ (E.app G.val).inv =
      (E.app lineSubgroup.group).inv ≫ F.map ((groupBaseChange ℝ ℂ).map lineSubgroup.inclusion) :=
    E.inv.naturality lineSubgroup.inclusion
  have hb₁ : b.hom ≫ C.inclusion = P'.inclusion ≫ e.hom := by
    change ((E.app lineSubgroup.group).inv ≫ F.map p.hom) ≫ F.map B.limits.parabolic.inclusion =
      P'.inclusion ≫ (E.app G.val).inv ≫ F.map complexSchemeIso.hom
    rw [Category.assoc, ← F.map_comp, hp, complexLineInclusion, F.map_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ F.map complexSchemeIso.hom) hn.symm).trans (Category.assoc _ _ _))
  have hb : b.hom ≫ D.inclusion = P'.inclusion := by
    change b.hom ≫ C.inclusion ≫ e.inv = P'.inclusion
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ e.inv) hb₁).trans ((Category.assoc _ _ _).trans
        ((congrArg (P'.inclusion ≫ ·) e.hom_inv_id).trans (Category.comp_id _))))
  have hDP : SameSubgroup D P' := ⟨⟨b.inv, by rw [← hb, b.inv_hom_id_assoc]⟩, ⟨b.hom, hb⟩⟩
  exact ⟨P'.isClosedImmersion, borel_of_same (H := H) hD hDP⟩



end Minimal

section Centralizer

set_option backward.isDefEq.respectTransparency false

open Specs (SubgroupSections)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private isAffine_product_left from LinearAlgebraicGroups.Affine.FixedPointSchemes
open private splitTorus_sectionsCommute from LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

private theorem centralizes_affine_iff {k : Type} [Field k] {A G : Specs.GroupScheme k}
    (j : A ⟶ G) (ha : IsAffine A.X.left) (R : TestAlgebra k) (x : Points G.X R) :
    Centralizes j x ↔ ∀ (T : TestAlgebra k)
      (p : Points ((testSpec k).obj (Opposite.op R)) T) (a : Points A.X T),
      Commute (p ≫ x) (a ≫ j.hom.hom) := by
  refine ⟨fun h T => (centralizes_iff j x).mp h ((testSpec k).obj (Opposite.op T)), ?_⟩
  intro h
  let Y := (testSpec k).obj (Opposite.op R)
  change (snd A.X Y ≫ x) * (fst A.X Y ≫ j.hom.hom) * (snd A.X Y ≫ x)⁻¹ =
    fst A.X Y ≫ j.hom.hom
  apply mul_inv_eq_iff_eq_mul.mpr
  have hY : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  letI : IsAffine A.X.left := ha
  letI : IsAffine Y.left := hY
  apply hom_ext_of_points (X := A.X ⊗ Y) isAffine_product_left
  intro T p
  simpa only [MonObj.comp_mul, Category.assoc] using (h T (p ≫ snd _ _) (p ≫ fst _ _)).eq

private theorem centralizes_of_split_factor {k : Type} [Field k] {G A B : Specs.GroupScheme k}
    (i : A ⟶ G) (j : B ⟶ G) (b : A ⟶ B) (hb : b ≫ j = i) (hB : IsSplitTorus B)
    (Y : SchemeOver k) (p : Y ⟶ B.X) : Centralizes i (p ≫ j.hom.hom) := by
  have h := (Grp.forget (SchemeOver k)).congr_map hb
  change b.hom.hom ≫ j.hom.hom = i.hom.hom at h
  apply (centralizes_iff _ _).mpr
  intro W q a
  letI := splitTorus_sectionsCommute hB W
  have hcomm : Commute (q ≫ p) (a ≫ b.hom.hom) := mul_comm' _ _
  change (q ≫ p ≫ j.hom.hom) * (a ≫ i.hom.hom) =
    (a ≫ i.hom.hom) * (q ≫ p ≫ j.hom.hom)
  simpa only [MonObj.mul_comp, Category.assoc, h] using
    congrArg (fun z : W ⟶ B.X => z ≫ j.hom.hom) hcomm.eq

private def twice : ℝˣ := Units.mk0 2 (by norm_num)

private theorem diagonal_twice_injective : Function.Injective (diagonalUnits twice) := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | norm_num [diagonalUnits, twice] at h

private theorem offDiagonal_of_commutes {I F R : Type*} [Fintype I] [DecidableEq I]
    [Field F] [CommRing R] (f : F →+* R) (d : I → F) (hd : Function.Injective d)
    (M : Matrix I I R) (h : Commute (Matrix.diagonal (fun i => f (d i))) M)
    (i j : I) (hij : i ≠ j) : M i j = 0 := by
  have hc := congrArg (fun A : Matrix I I R => A i j) h.eq
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hc
  have hu : IsUnit (f (d i - d j)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun he => hij (hd he)))).map f
  apply hu.mul_left_cancel
  rw [map_sub, sub_mul, hc, mul_comm (M i j), sub_self, mul_zero]

private abbrev SLpoints (R : TestAlgebra ℂ) :=
  Matrix.SpecialLinearGroup (Specs.Unipotent.Index.{0} 3) R

private def complexMatrixPoint (R : TestAlgebra ℂ) :
    Points complexUnitary.val.X R →* SLpoints R :=
  (complexSLPoints.app R).groupIsoToMulEquiv.toMonoidHom.comp
    (((groupPointsFunctor ℂ).map complexSchemeIso.hom).app R).hom

private theorem complexMatrixPoint_injective (R : TestAlgebra ℂ) :
    Function.Injective (complexMatrixPoint R) :=
  (complexSLPoints.app R).groupIsoToMulEquiv.injective.comp
    (fun _ _ h => (cancel_mono ((Grp.forget (SchemeOver ℂ)).map complexSchemeIso.hom)).mp h)

private abbrev splitComplex := extendSubgroup ℂ splitSubgroup

private def splitComplexPoint (R : TestAlgebra ℂ) (t : Rˣ) :
    Points splitComplex.group.X R :=
  (baseChangePointsEquiv ℂ splitSubgroup.group.X R).symm
    (unitPoint ((restrictTestAlgebra ℝ ℂ).obj R) t ≫ splitIso.hom.hom.hom)

private theorem splitComplex_eval (R : TestAlgebra ℂ) (p : Points splitComplex.group.X R) :
    (complexMatrixPoint R (p ≫ splitComplex.inclusion.hom.hom)).val =
      Matrix.diagonal (fun i : Specs.Unipotent.Index.{0} 3 =>
        diagonalUnits (splitUnits.hom.app ((restrictTestAlgebra ℝ ℂ).obj R)
          (baseChangePoint ℝ ℂ splitSubgroup.group.X R p)) i.down) := by
  let E := (restrictTestAlgebra ℝ ℂ).obj R
  let q : Points splitSubgroup.group.X E := baseChangePoint ℝ ℂ splitSubgroup.group.X R p
  let t : Rˣ := splitUnits.hom.app E q
  have hq : baseChangePoint ℝ ℂ (representedGroup false).val.X R
      (p ≫ splitComplex.inclusion.hom.hom) = q ≫ splitSubgroup.inclusion.hom.hom :=
    baseChangePointsSchemeNaturality ℝ ℂ splitSubgroup.inclusion.hom.hom R p
  have he := congrArg (fun x : Points (representedGroup false).val.X E =>
    (representedGroupPointIso false).hom.app E x) hq
  have hf := he.trans (splitSubgroup_point E q)
  apply Matrix.ext
  intro i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  have hw := complexSchemeIso_eval R (p ≫ splitComplex.inclusion.hom.hom) i j
  have hm := congrArg (fun x : realMatrixSubgroup false E => firstCoordinate R (x.val.val i j)) hf
  refine hw.trans (hm.trans ?_)
  change firstCoordinate R
      (Matrix.diagonal (fun k => algebraMap R (Complexification R) (diagonalUnits t k)) i j) =
    Matrix.diagonal (fun k : Specs.Unipotent.Index.{0} 3 => diagonalUnits t k.down) ⟨i⟩ ⟨j⟩
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    change (diagonalUnits t i) + 0 * algebraMap ℂ R Complex.I = _
    rw [zero_mul, add_zero]
  · rw [Matrix.diagonal_apply_ne _ hij, map_zero,
      Matrix.diagonal_apply_ne _ (fun h => hij (congrArg ULift.down h))]

private theorem splitComplexPoint_eval (R : TestAlgebra ℂ) (t : Rˣ) :
    (complexMatrixPoint R ((splitComplexPoint R t) ≫ splitComplex.inclusion.hom.hom)).val =
      Matrix.diagonal (fun i : Specs.Unipotent.Index.{0} 3 => diagonalUnits t i.down) := by
  let E := (restrictTestAlgebra ℝ ℂ).obj R
  let p := splitComplexPoint R t
  have hq : baseChangePoint ℝ ℂ splitSubgroup.group.X R p =
      unitPoint E t ≫ splitIso.hom.hom.hom :=
    (baseChangePointsEquiv ℂ splitSubgroup.group.X R).apply_symm_apply _
  exact (splitComplex_eval R p).trans <| congrArg
    (fun r : Rˣ => Matrix.diagonal (fun i : Specs.Unipotent.Index.{0} 3 => diagonalUnits r i.down))
    ((congrArg (fun r : Points splitSubgroup.group.X E => splitUnits.hom.app E r) hq).trans
      (splitIso_unit E t))

private theorem centralizes_splitComplex_iff (R : TestAlgebra ℂ) (x : Points complexUnitary.val.X R) :
    Centralizes splitComplex.inclusion x ↔
      ∀ i j, i ≠ j → (complexMatrixPoint R x).val i j = 0 := by
  have ha := (closedSubgroupAlgebraicGroup (G := complexUnitary) splitComplex).property.1
  refine (centralizes_affine_iff (G := complexUnitary.val) splitComplex.inclusion ha R x).trans ?_
  constructor
  · intro h i j hij
    let t := Units.map (algebraMap ℝ R).toMonoidHom twice
    let p := splitComplexPoint R t
    have hc := h R (𝟙 _) p
    have hc' : Commute (complexMatrixPoint R (p ≫ splitComplex.inclusion.hom.hom))
        (complexMatrixPoint R x) := by
      have hx : Commute x (p ≫ splitComplex.inclusion.hom.hom) := by
        simpa only [Category.id_comp] using hc
      exact hx.symm.map (complexMatrixPoint R)
    have hmatrix : Commute (complexMatrixPoint R (p ≫ splitComplex.inclusion.hom.hom)).val
        (complexMatrixPoint R x).val := congrArg Subtype.val hc'.eq
    have hd : (fun i : Specs.Unipotent.Index.{0} 3 => diagonalUnits t i.down) =
        fun i => algebraMap ℝ R (diagonalUnits twice i.down) := by
      funext i
      rcases i with ⟨i⟩
      fin_cases i <;> simp [t, diagonalUnits]
    rw [show (complexMatrixPoint R (p ≫ splitComplex.inclusion.hom.hom)).val =
        Matrix.diagonal (fun i : Specs.Unipotent.Index.{0} 3 => diagonalUnits t i.down) from
      splitComplexPoint_eval R t, hd] at hmatrix
    exact offDiagonal_of_commutes (algebraMap ℝ R)
      (fun i : Specs.Unipotent.Index.{0} 3 => diagonalUnits twice i.down)
      (diagonal_twice_injective.comp ULift.down_injective) _ hmatrix i j hij
  · intro hd T a p
    have hd' : (complexMatrixPoint T (a ≫ x)).val =
        Matrix.diagonal (fun i => (complexMatrixPoint T (a ≫ x)).val i i) := by
      -- Affine precomposition corresponds to coefficient change under the matrix functor.
      let f := ((algSpec.fullyFaithful (R := CommRingCat.of ℂ)).preimage a).unop
      have hf : (testSpec ℂ).map f.op = a :=
        (algSpec.fullyFaithful (R := CommRingCat.of ℂ)).map_preimage a
      have hn := complexSLPoints.hom.naturality f
      have hmap : complexMatrixPoint T (a ≫ x) =
          Matrix.SpecialLinearGroup.map f.hom.toRingHom (complexMatrixPoint R x) := by
        have h := congrArg (fun m => m (x ≫ complexSchemeIso.hom.hom.hom)) hn
        change complexSLPoints.hom.app T (mapPoints f (x ≫ complexSchemeIso.hom.hom.hom)) = _ at h
        exact (congrArg (fun g : Points complexSL.val.X T => complexSLPoints.hom.app T g)
          ((Category.assoc _ _ _).trans
            (congrArg (fun b => b ≫ x ≫ complexSchemeIso.hom.hom.hom) hf.symm))).trans h
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ hij, hmap]
        exact (congrArg f.hom (hd i j hij)).trans (map_zero f.hom)
    have ht := splitComplex_eval T p
    apply (complexMatrixPoint_injective T)
    rw [map_mul, map_mul]
    apply Subtype.ext
    change (complexMatrixPoint T _).val * (complexMatrixPoint T _).val =
      (complexMatrixPoint T _).val * (complexMatrixPoint T _).val
    rw [ht, hd', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _

private theorem centralizerComplex_diagonal
    {H : ClosedSubgroup (representedGroup false).val}
    (hH : RepresentsSubgroup H (fun _ g => Centralizes splitSubgroup.inclusion g))
    (T : DiagonalTorus complexSLPoints) :
    ∃ e : (extendSubgroup ℂ H).group ≅ T.subgroup.group,
      e.hom ≫ T.subgroup.inclusion = (extendSubgroup ℂ H).inclusion ≫ complexSchemeIso.hom := by
  obtain ⟨_, hC⟩ := centralizerSchemeBaseChange ℝ ℂ splitSubgroup.inclusion H hH
  let C := extendSubgroup ℂ H
  let C' := transportSubgroup complexSchemeIso C
  have hC' (R : TestAlgebra ℂ) (x : Points complexSL.val.X R) :
      x ∈ SubgroupSections C' ((testSpec ℂ).obj (Opposite.op R)) ↔
        x ∈ SubgroupSections T.subgroup ((testSpec ℂ).obj (Opposite.op R)) := by
    let g : Points complexUnitary.val.X R := x ≫ complexSchemeIso.inv.hom.hom
    have hi := image_comp_iso C.inclusion.hom.hom
      ((Grp.forget (SchemeOver ℂ)).mapIso complexSchemeIso) x
    have hg : g ≫ complexSchemeIso.hom.hom.hom = x := by
      have e := ((Grp.forget (SchemeOver ℂ)).mapIso complexSchemeIso).inv_hom_id
      exact (Category.assoc _ _ _).trans
        ((congrArg (x ≫ ·) e).trans (Category.comp_id _))
    exact hi.trans (((hC _ g).symm.trans (centralizes_splitComplex_iff R g)).trans
      ((show (∀ i j, i ≠ j → (complexMatrixPoint R g).val i j = 0) ↔
          ∀ i j, i ≠ j → (complexSLPoints.hom.app R x).val i j = 0 from
        Iff.of_eq (congrArg (fun q : Points complexSL.val.X R =>
          ∀ i j, i ≠ j → (complexSLPoints.hom.app R q).val i j = 0) hg)).trans (T.range R x).symm))
  have ha (S : ClosedSubgroup complexSL.val) : IsAffine S.group.X.left :=
    (closedSubgroupAlgebraicGroup S).property.1
  have hf : IsSubgroupOf C' T.subgroup :=
    subgroupInclusionFactors (ha C') T.subgroup C'.inclusion (fun R p => (hC' R _).mp ⟨p, rfl⟩)
  have hg : IsSubgroupOf T.subgroup C' :=
    subgroupInclusionFactors (ha T.subgroup) C' T.subgroup.inclusion (fun R p => (hC' R _).mpr ⟨p, rfl⟩)
  exact subgroupIso_of_same ⟨hf, hg⟩



end Centralizer

section Roots

set_option backward.isDefEq.respectTransparency false

open Specs.CharacterDescent (Character Cocharacter StandardLattice compositionPairing)
open Specs.CharacterPairing (absoluteRoots pairing powerMorphism characterValue)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra groupAlgebraMap integerGenerator)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)
open private diagonalBaseChange diagonalBaseChange_natural limitMultiplicativeExtension_eq
  from LinearAlgebraicGroups.Classification.RationalRealization
open private extendSubgroup cocharacter_ext_units from LinearAlgebraicGroups.RootData.RankOneFlag
open private splitPresentation powerEquiv powerEquiv_apply pairing_eq_iff
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private gm_baseChange subgroupInclusionFactors
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private characterValue_extend from LinearAlgebraicGroups.Relative.RelativeChambers
open private rootsOfIso from LinearAlgebraicGroups.RootData.BorelsAndChambers

private abbrev scalarExtension := groupBaseChange ℝ ℂ

private def gmComplexIso : multLine ℂ ≅ scalarExtension.obj (multLine ℝ) :=
  (diagonalBaseChange ℝ ℂ IntegerCharacters).symm

private theorem gmComplexIso_unit (R : TestAlgebra ℂ) (t : Rˣ) :
    baseChangePoint ℝ ℂ (multLine ℝ).X R (unitPoint R t ≫ gmComplexIso.hom.hom.hom) =
      unitPoint ((restrictTestAlgebra ℝ ℂ).obj R) t := by
  obtain ⟨e, he⟩ := gm_baseChange ℝ ℂ
  have h : e.hom = gmComplexIso.hom := limitMultiplicativeExtension_eq e he
  exact (congrArg (fun f : multLine ℂ ⟶ scalarExtension.obj (multLine ℝ) =>
    baseChangePoint ℝ ℂ (multLine ℝ).X R (unitPoint R t ≫ f.hom.hom)) h).symm.trans (he R t)

private theorem character_descends_of_split {S : GroupScheme ℝ} (hS : IsSplitTorus S)
    (a : Character (scalarExtension.obj S)) :
    ∃ b : Character S, scalarExtension.map b ≫ gmComplexIso.inv = a := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hS
  obtain ⟨p, _, hp, _, _⟩ := CharacterDescent.splitCompositionPairing (k := ℝ) r
  obtain ⟨q, _, hq, _, _⟩ := CharacterDescent.splitCompositionPairing (k := ℂ) r
  let d := diagonalBaseChange ℝ ℂ (StandardLattice.{0} r)
  let e := (scalarExtension.mapIso i).symm ≪≫ d
  obtain ⟨m, hm⟩ := q.surjective (e.inv ≫ a)
  refine ⟨i.inv ≫ p m, ?_⟩
  have hn : scalarExtension.map (p m) ≫ gmComplexIso.inv = d.hom ≫ q m := by
    rw [hp, hq]
    exact diagonalBaseChange_natural ℝ ℂ _
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, show
    scalarExtension.map i.inv ≫ d.hom = e.hom from rfl, hm, e.hom_inv_id_assoc]

private theorem powerMorphism_extend (n : ℤ) :
    gmComplexIso.hom ≫ scalarExtension.map (powerMorphism (k := ℝ) n) ≫ gmComplexIso.inv =
      powerMorphism (k := ℂ) n := by
  have h := diagonalBaseChange_natural ℝ ℂ
    ((zpowersHom IntegerCharacters (integerGenerator ^ n)).comp MulEquiv.ulift.toMonoidHom)
  change scalarExtension.map (powerMorphism (k := ℝ) n) ≫ gmComplexIso.inv =
    gmComplexIso.inv ≫ powerMorphism (k := ℂ) n at h
  rw [h, gmComplexIso.hom_inv_id_assoc]

private theorem rootsExtensionExponent {S : GroupScheme ℝ} (f : multLine ℝ ≅ S)
    (a : Character S) :
    let c := gmComplexIso.hom ≫ scalarExtension.map f.hom
    c ≫ scalarExtension.map a ≫ gmComplexIso.inv = powerMorphism (pairing S a f.hom) := by
  intro c
  have ha : f.hom ≫ a = powerMorphism (pairing S a f.hom) :=
    (pairing_eq_iff a f.hom _).mpr rfl
  change (gmComplexIso.hom ≫ scalarExtension.map f.hom) ≫
      scalarExtension.map a ≫ gmComplexIso.inv = _
  rw [Category.assoc, ← Functor.map_comp_assoc, ha, powerMorphism_extend]

private theorem character_exponent_bijective {k : Type} [Field k] {S : GroupScheme k}
    (f : multLine k ≅ S) : Function.Bijective fun a : Character S => pairing S a f.hom := by
  have h (a : Character S) : f.hom ≫ a = (powerEquiv (k := k)) (pairing S a f.hom) :=
    ((pairing_eq_iff a f.hom _).mpr rfl).trans (powerEquiv_apply _).symm
  constructor
  · intro a b hab
    apply (cancel_epi f.hom).mp
    exact (h a).trans ((congrArg (powerEquiv (k := k)) hab).trans (h b).symm)
  · intro n
    refine ⟨f.inv ≫ powerMorphism n, (pairing_eq_iff _ f.hom _).mp ?_⟩
    exact f.hom_inv_id_assoc _

private theorem cocharacterComplex_matrix
    {H : ClosedSubgroup (representedGroup false).val}
    (i : splitSubgroup.group ⟶ H.group) (hi : i ≫ H.inclusion = splitSubgroup.inclusion)
    (T : DiagonalTorus complexSLPoints) (L : LatticeIdentification T)
    (d : (extendSubgroup ℂ H).group ≅ T.subgroup.group)
    (hd : d.hom ≫ T.subgroup.inclusion =
      (extendSubgroup ℂ H).inclusion ≫ complexSchemeIso.hom) :
    letI := L.comm
    let c := (gmComplexIso.hom ≫ scalarExtension.map splitIso.hom) ≫
      scalarExtension.map i ≫ d.hom
    L.cocharacters (Additive.ofMul c) = coroot 3 0 2 := by
  letI := L.comm
  intro c
  let s := gmComplexIso.hom ≫ scalarExtension.map splitIso.hom
  have hc : c ≫ T.subgroup.inclusion =
      s ≫ scalarExtension.map splitSubgroup.inclusion ≫ complexSchemeIso.hom := by
    change (s ≫ scalarExtension.map i ≫ d.hom) ≫ T.subgroup.inclusion = _
    simp only [Category.assoc, hd]
    rw [show (extendSubgroup ℂ H).inclusion = scalarExtension.map H.inclusion from rfl,
      ← Functor.map_comp_assoc, hi]
  have hct : c = Additive.toMul (L.cocharacters.symm (coroot 3 0 2)) := by
    apply cocharacter_ext_units
    intro R t
    let a := T.subgroup.inclusion.hom.hom
    let z := splitComplexPoint R t
    have hs : unitPoint R t ≫ s.hom.hom = z := by
      apply (baseChangePointsEquiv ℂ splitSubgroup.group.X R).injective
      change baseChangePoint ℝ ℂ splitSubgroup.group.X R
        ((unitPoint R t ≫ gmComplexIso.hom.hom.hom) ≫
          (scalarExtension.map splitIso.hom).hom.hom) =
        (baseChangePointsEquiv ℂ splitSubgroup.group.X R)
          ((baseChangePointsEquiv ℂ splitSubgroup.group.X R).symm _)
      rw [Equiv.apply_symm_apply]
      exact (baseChangePointsSchemeNaturality ℝ ℂ splitIso.hom.hom.hom R _).trans
        (congrArg (· ≫ splitIso.hom.hom.hom) (gmComplexIso_unit R t))
    letI : IsClosedImmersion a.left := T.subgroup.isClosedImmersion
    letI : Mono a := Over.mono_of_mono_left _
    apply (cancel_mono a).mp
    apply (complexSLPoints.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    have hm : (cocharacterPoint c R t) ≫ a =
        (z ≫ (extendSubgroup ℂ splitSubgroup).inclusion.hom.hom) ≫ complexSchemeIso.hom.hom.hom := by
      have h := congrArg (fun f : multLine ℂ ⟶ complexSL.val =>
        unitPoint R t ≫ f.hom.hom) hc
      change (unitPoint R t ≫ c.hom.hom) ≫ a = _
      simp only [Functor.map_comp, Category.assoc] at h ⊢
      exact h.trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) hs).trans (Category.assoc _ _ _).symm
    change (complexSLPoints.hom.app R (cocharacterPoint c R t ≫ a)).val =
      (complexSLPoints.hom.app R _).val
    rw [hm, L.cocharacterPoint_eq]
    refine (splitComplexPoint_eval R t).trans ?_
    congr 1
    funext x
    rw [exponents_eq]
    rcases x with ⟨x⟩
    fin_cases x <;> simp [diagonalUnits]
  change L.cocharacters (Additive.ofMul c) = _
  rw [hct]
  exact L.cocharacters.apply_symm_apply _

private theorem complexRoots_restrict {T : DiagonalTorus complexSLPoints}
    (L : LatticeIdentification T) (M : RootIdentification T L)
    (c : Cocharacter T.subgroup.group)
    (hc : letI := L.comm; L.cocharacters (Additive.ofMul c) = coroot 3 0 2) :
    (∀ p : RootIndices 3, pairing T.subgroup.group (M.indices p).val c =
      (![1, 0, -1] : Fin 3 → ℤ) p.val.1 - (![1, 0, -1] : Fin 3 → ℤ) p.val.2) ∧
    Set.range (fun p : RootIndices 3 => pairing T.subgroup.group (M.indices p).val c) =
      ({1, -1, 2, -2} : Set ℤ) := by
  letI := L.comm
  have h (p : RootIndices 3) : pairing T.subgroup.group (M.indices p).val c =
      dotPairing 3 (root 3 p.val.1 p.val.2) (coroot 3 0 2) := by
    rw [L.pairing_eq, M.character_eq, hc]
  exact ⟨fun p => (h p).trans (by rw [root_dot, exponents_eq, exponents_eq]), by
    simp only [h, root_range]⟩

open private powerMorphism_zero from LinearAlgebraicGroups.Flag.StandardParabolicLevi

private theorem splitContainedInCentralizer
    {H : ClosedSubgroup (representedGroup false).val}
    (hH : RepresentsSubgroup H (fun _ g => Centralizes splitSubgroup.inclusion g)) :
    IsSubgroupOf splitSubgroup H := by
  apply subgroupInclusionFactors (StandardGroups.multiplicativeGroup ℝ).property.1
    H splitSubgroup.inclusion
  intro R p
  exact (hH _ _).mp <| centralizes_of_split_factor splitSubgroup.inclusion splitSubgroup.inclusion
    (𝟙 _) (Category.id_comp _) splitSubgroup_isSplit _ p

private theorem unitary_real_roots
    (T : DiagonalTorus complexSLPoints) (L : LatticeIdentification T)
    (M : RootIdentification T L) :
    Set.range (fun a : relativeRoots splitSubgroup => pairing splitSubgroup.group a.val splitIso.hom) =
      ({1, -1, 2, -2} : Set ℤ) := by
  let G := representedGroup false
  obtain ⟨H, hH⟩ := centralizerScheme ℝ G splitSubgroup
  obtain ⟨i, hi⟩ := splitContainedInCentralizer hH
  obtain ⟨d, hd⟩ := centralizerComplex_diagonal hH T
  let H' := extendSubgroup ℂ H
  have hsplit : IsSplitTorus H'.group := by
    obtain ⟨r, ⟨f⟩⟩ := T.split
    exact ⟨r, ⟨d ≪≫ f⟩⟩
  obtain ⟨e, he, _, hroots⟩ := RelativeChambers.relativeRootsByRestriction G splitSubgroup H
    i hi splitSubgroup_isSplit H'.isClosedImmersion hsplit
  have h : e = gmComplexIso := Iso.ext (limitMultiplicativeExtension_eq e he)
  subst e
  have hrootEq :
      (fun x : Character splitSubgroup.group => scalarExtension.map x ≫ gmComplexIso.inv) ''
        relativeRoots splitSubgroup =
      ((fun x : Character H'.group => scalarExtension.map i ≫ x) '' absoluteRoots H') \
        ({1} : Set (Character (scalarExtension.obj splitSubgroup.group))) := hroots
  let a := gmComplexIso.hom ≫ scalarExtension.map splitIso.hom
  let c : Cocharacter T.subgroup.group := a ≫ scalarExtension.map i ≫ d.hom
  let roots := fun p : RootIndices 3 => pairing T.subgroup.group (M.indices p).val c
  have hr : Set.range roots = ({1, -1, 2, -2} : Set ℤ) :=
    (complexRoots_restrict L M c (cocharacterComplex_matrix i hi T L d hd)).2
  have hrestrict (p : RootIndices 3) :
      a ≫ (scalarExtension.map i ≫ (d.hom ≫ (M.indices p).val)) =
        powerMorphism (roots p) := by
    have h := (pairing_eq_iff (M.indices p).val c (roots p)).mpr rfl
    simpa only [compositionPairing, c, Category.assoc] using h
  rw [← hr]
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    have hx : scalarExtension.map x.val ≫ gmComplexIso.inv ∈
        ((fun b : Character H'.group => scalarExtension.map i ≫ b) '' absoluteRoots H') \
          ({1} : Set (Character (scalarExtension.obj splitSubgroup.group))) := by
      rw [← hrootEq]
      exact ⟨x.val, x.property, rfl⟩
    obtain ⟨⟨b, hb, hb'⟩, _⟩ := hx
    let y : Character T.subgroup.group := d.inv ≫ b
    have hy : d.hom ≫ y = b := d.hom_inv_id_assoc _
    have hyt : y ∈ absoluteRoots T.subgroup :=
      (rootsOfIso complexSchemeIso d hd.symm y).mp (hy ▸ hb)
    obtain ⟨p, hp⟩ := M.indices.surjective ⟨y, hyt⟩
    refine ⟨p, ?_⟩
    have hp' : (M.indices p).val = y := congrArg Subtype.val hp
    have hh := hrestrict p
    change scalarExtension.map i ≫ b = scalarExtension.map x.val ≫ gmComplexIso.inv at hb'
    rw [hp', hy, hb'] at hh
    have hz := rootsExtensionExponent splitIso x.val
    change roots p = pairing splitSubgroup.group x.val splitIso.hom
    apply (powerEquiv (k := ℂ)).injective
    rw [powerEquiv_apply, powerEquiv_apply]
    exact hh.symm.trans (by simpa only [a, Category.assoc] using hz)
  · rintro ⟨p, rfl⟩
    let y := (M.indices p).val
    let b : Character H'.group := d.hom ≫ y
    have hb : b ∈ absoluteRoots H' :=
      (rootsOfIso complexSchemeIso d hd.symm y).mpr (M.indices p).property
    have hz := hrestrict p
    have hp0 : roots p ≠ 0 := by
      have hh : roots p ∈ ({1, -1, 2, -2} : Set ℤ) := hr ▸ ⟨p, rfl⟩
      intro he
      rw [he] at hh
      norm_num at hh
    have hn : scalarExtension.map i ≫ b ≠ 1 := by
      intro hh
      change a ≫ (scalarExtension.map i ≫ b) = powerMorphism (roots p) at hz
      rw [hh] at hz
      have ha : a ≫ (1 : Character (extendSubgroup ℂ splitSubgroup).group) = 1 := by
        apply Grp.hom_ext
        exact MonObj.comp_one _
      have he : powerMorphism (k := ℂ) (roots p) = powerMorphism 0 :=
        hz.symm.trans (ha.trans powerMorphism_zero.symm)
      exact hp0 ((powerEquiv (k := ℂ)).injective (by simpa only [powerEquiv_apply] using he))
    have hx : scalarExtension.map i ≫ b ∈
        (fun x : Character splitSubgroup.group => scalarExtension.map x ≫ gmComplexIso.inv) ''
          relativeRoots splitSubgroup := by
      rw [hrootEq]
      exact ⟨⟨b, hb, rfl⟩, fun h => hn (Set.mem_singleton_iff.mp h)⟩
    obtain ⟨x, hx, hh⟩ := hx
    refine ⟨⟨x, hx⟩, ?_⟩
    have he := rootsExtensionExponent splitIso x
    change pairing splitSubgroup.group x splitIso.hom = roots p
    apply (powerEquiv (k := ℂ)).injective
    rw [powerEquiv_apply, powerEquiv_apply]
    have ht : a ≫ (scalarExtension.map x ≫ gmComplexIso.inv) = powerMorphism (roots p) := by
      exact (congrArg (a ≫ ·) hh).trans hz
    exact he.symm.trans ht



end Roots

section OrbitGeometry

set_option backward.isDefEq.respectTransparency false

open Specs.Relative.RelativeBruhat (DoubleOrbit doubleOrbitMap)
open private comp_doubleOrbitMap from LinearAlgebraicGroups.Relative.RelativeBruhat
open private prodComparison_inv_fst prodComparison_inv_snd
  from LinearAlgebraicGroups.Affine.Stabilizers
open private baseChangeMapIsPullback from LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private descends from LinearAlgebraicGroups.Reductive.BorelProper

private theorem sameOrbit_of_common_projection {k : Type} [Field k] {X Y A B : SchemeOver k}
    {a : A ⟶ Y} {b : B ⟶ Y}
    (ha : IsImmersion a.left) (hb : IsImmersion b.left)
    (p : X ⟶ A) (q : X ⟶ B) (h : p ≫ a = q ≫ b)
    (hp : Flat p.left ∧ Surjective p.left ∧ LocallyOfFinitePresentation p.left)
    (hq : Flat q.left ∧ Surjective q.left ∧ LocallyOfFinitePresentation q.left) :
    ∃ e : A ≅ B, e.hom ≫ b = a := by
  letI := ha
  letI := hb
  letI : Mono a := Over.mono_of_mono_left _
  letI : Mono b := Over.mono_of_mono_left _
  letI : Flat p.left := hp.1
  letI : Surjective p.left := hp.2.1
  letI : LocallyOfFinitePresentation p.left := hp.2.2
  letI : Flat q.left := hq.1
  letI : Surjective q.left := hq.2.1
  letI : LocallyOfFinitePresentation q.left := hq.2.2
  have hd {A B : SchemeOver k} {a : A ⟶ Y} {b : B ⟶ Y} [Mono b]
      (p : X ⟶ A) (q : X ⟶ B) [Flat p.left] [Surjective p.left]
      [LocallyOfFinitePresentation p.left] (h : p ≫ a = q ≫ b) :
      ∃ f : A ⟶ B, f ≫ b = a := by
    obtain ⟨f, hf⟩ := descends p q (fun T x z hx => (cancel_mono b).mp (by
      simpa only [Category.assoc, ← h] using congrArg (· ≫ a) hx))
    letI : Epi p := Over.epi_of_epi_left _
    refine ⟨f, (cancel_epi p).mp ?_⟩
    rw [← Category.assoc, hf, h]
  obtain ⟨f, hf⟩ := hd p q h
  obtain ⟨g, hg⟩ := hd q p h.symm
  exact ⟨⟨f, g, (cancel_mono a).mp (by simp only [Category.assoc, hg, hf, Category.id_comp]),
    (cancel_mono b).mp (by simp only [Category.assoc, hf, hg, Category.id_comp])⟩, hf⟩

open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag

private theorem baseChange_doubleOrbitMap {k K : Type} [Field k] [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} (P : ClosedSubgroup G.val) (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    (prodComparisonIso (baseChange k K) P.group.X P.group.X).inv ≫
      (baseChange k K).map (doubleOrbitMap P n) =
    doubleOrbitMap (G := Specs.Unipotent.baseChangedAlgebraicGroup K G) (extendSubgroup K P)
      (scalarExtendedRationalPoint K n) := by
  let F := baseChange k K
  let : GrpObj (F.obj G.val.X) := ((groupBaseChange k K).obj G.val).grp
  have hconst (V : SchemeOver k) :
      F.map (toUnit V ≫ n) = toUnit (F.obj V) ≫ scalarExtendedRationalPoint K n := by
    rw [Functor.map_comp, scalarExtendedRationalPoint, ← Category.assoc,
      Functor.Monoidal.toUnit_ε]
  let a := (prodComparisonIso F P.group.X P.group.X).inv
  change a ≫ F.map ((fst _ _ ≫ P.inclusion.hom.hom) * _ * (snd _ _ ≫ P.inclusion.hom.hom)) = _
  rw [Functor.map_mul, Functor.map_mul, hconst, Functor.map_comp, Functor.map_comp]
  simp only [MonObj.comp_mul, ← Category.assoc]
  rw [show a ≫ F.map (fst P.group.X P.group.X) = fst _ _ from prodComparison_inv_fst K _ _,
    show a ≫ F.map (snd P.group.X P.group.X) = snd _ _ from prodComparison_inv_snd K _ _,
    comp_toUnit]
  rfl

private def baseChange_doubleOrbit {k K : Type} [Field k] [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} {P : ClosedSubgroup G.val} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (O : DoubleOrbit P n) :
    DoubleOrbit (G := Specs.Unipotent.baseChangedAlgebraicGroup K G) (extendSubgroup K P)
      (scalarExtendedRationalPoint K n) := by
  let F := baseChange k K
  let s := (prodComparisonIso F P.group.X P.group.X).inv
  letI : IsIso s.left := (Over.forget _).map_isIso s
  have hi := MorphismProperty.of_isPullback (P := @IsImmersion)
    (baseChangeMapIsPullback K O.inclusion).flip O.immersion
  letI hp₁ := MorphismProperty.of_isPullback (P := @Flat)
    (baseChangeMapIsPullback K O.projection).flip O.flat
  letI hp₂ := MorphismProperty.of_isPullback (P := @Surjective)
    (baseChangeMapIsPullback K O.projection).flip O.surjective
  letI hp₃ := MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (baseChangeMapIsPullback K O.projection).flip O.finitePresentation
  refine ⟨F.obj O.scheme, F.map O.inclusion, hi, s ≫ F.map O.projection, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← Functor.map_comp, O.factors]
    exact baseChange_doubleOrbitMap P n
  · change Flat (s.left ≫ (F.map O.projection).left)
    infer_instance
  · change Surjective (s.left ≫ (F.map O.projection).left)
    infer_instance
  · change LocallyOfFinitePresentation (s.left ≫ (F.map O.projection).left)
    infer_instance

private def transport_doubleOrbit {k : Type} [Field k] {G H : AffineAlgebraicGroup k}
    {P : ClosedSubgroup G.val} {Q : ClosedSubgroup H.val} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (O : DoubleOrbit P n) (e : G.val ≅ H.val) (p : P.group ≅ Q.group)
    (hp : p.hom ≫ Q.inclusion = P.inclusion ≫ e.hom) :
    DoubleOrbit Q (n ≫ e.hom.hom.hom) := by
  let E : G.val.X ≅ H.val.X := (Grp.forget (SchemeOver k)).mapIso e
  let F : P.group.X ≅ Q.group.X := (Grp.forget (SchemeOver k)).mapIso p
  let s := F.inv ⊗ₘ F.inv
  letI : IsIso s := inferInstanceAs (IsIso ((F.symm ⊗ᵢ F.symm).hom))
  letI : IsMonHom E.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  let i := O.inclusion ≫ E.hom
  let q := s ≫ O.projection
  letI : IsIso E.hom.left := (Over.forget _).map_isIso E.hom
  letI : IsIso s.left := (Over.forget _).map_isIso s
  letI := O.immersion
  letI := O.flat
  letI := O.surjective
  letI := O.finitePresentation
  refine ⟨O.scheme, i, ?_, q, ?_, ?_, ?_, ?_⟩
  · change IsImmersion (O.inclusion.left ≫ E.hom.left)
    infer_instance
  · have h : p.inv ≫ P.inclusion ≫ e.hom = Q.inclusion := by rw [← hp, p.inv_hom_id_assoc]
    have h' := (Grp.forget (SchemeOver k)).congr_map h
    change F.inv ≫ P.inclusion.hom.hom ≫ E.hom = Q.inclusion.hom.hom at h'
    change (s ≫ O.projection) ≫ O.inclusion ≫ E.hom = _
    rw [Category.assoc, ← Category.assoc O.projection, O.factors, ← Category.assoc s,
      comp_doubleOrbitMap]
    unfold doubleOrbitMap
    simp only [s, MonObj.mul_comp, Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc, h']
    rfl
  · change Flat (s.left ≫ O.projection.left)
    infer_instance
  · change Surjective (s.left ≫ O.projection.left)
    infer_instance
  · change LocallyOfFinitePresentation (s.left ≫ O.projection.left)
    infer_instance

private theorem doubleOrbit_iso {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    {P : ClosedSubgroup G.val} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (A B : DoubleOrbit P n) :
    ∃ e : A.scheme ≅ B.scheme, e.hom ≫ B.inclusion = A.inclusion :=
  sameOrbit_of_common_projection A.immersion B.immersion A.projection B.projection
    (A.factors.trans B.factors.symm) ⟨A.flat, A.surjective, A.finitePresentation⟩
    ⟨B.flat, B.surjective, B.finitePresentation⟩


end OrbitGeometry


open Specs.GeometricRadicals (IsReductive)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
set_option backward.isDefEq.respectTransparency false in
private def markedComparison
    (T : DiagonalTorus complexSLPoints) (L : LatticeIdentification T)
    (M : RootIdentification T L) (B : UpperTriangularBorel T L M)
    (D : Specs.Pinning.AttachedDatum B.pair) (hD : IsMatrixBasedDatum B D)
    (hpin : HasTransvectionPinning B)
    (p : complexParabolic.val ≅ B.limits.parabolic.group)
    (hp : p.hom ≫ B.limits.parabolic.inclusion = complexLineInclusion) :
    UnitaryComparison where
  realGroup := representedGroup false
  line := lineSubgroup
  points R := ((representedGroupPointIso false).app R).groupIsoToMulEquiv.toEquiv
  pointsNatural R A f g := congrArg Subtype.val (GrpCat.ext_iff.mp
    ((representedGroupPointIso false).hom.naturality f) g)
  pointsMul R g h := congrArg Subtype.val (map_mul
    ((representedGroupPointIso false).app R).groupIsoToMulEquiv g h)
  complexGroup := complexSL
  matrixPoints := complexSLPoints
  complexIso := complexSchemeIso
  complexCoordinateModel := ⟨Representation.operations specialLinearRepresentation, ⟨Iso.refl _⟩⟩
  linePoints := lineSubgroup_range
  complexPoints := complexSchemeIso_eval
  diagonal := T
  lattice := L
  roots := M
  borel := B
  datum := D
  basedDatum := hD
  pinning := hpin
  borelIso := p
  borelInclusion := hp

theorem unitarySchemeComparison : UnitarySchemeComparison := by
  obtain ⟨T, L, M, B, D, hD, hpin, _⟩ :=
    LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixPinnedDatum ℂ 2 complexSL complexSLPoints
  obtain ⟨p, hp⟩ := complexLine_borel B
  exact ⟨markedComparison T L M B D hD hpin p hp⟩

private def splitParameterComplex :
    multLine ℂ ≅ scalarExtension.obj splitSubgroup.group :=
  gmComplexIso ≪≫ scalarExtension.mapIso splitIso

private theorem splitParameterComplex_value (R : TestAlgebra ℂ) (t : Rˣ) :
    baseChangePoint ℝ ℂ splitSubgroup.group.X R (unitPoint R t ≫ splitParameterComplex.hom.hom.hom) =
      unitPoint ((restrictTestAlgebra ℝ ℂ).obj R) t ≫ splitIso.hom.hom.hom := by
  have h : unitPoint R t ≫ splitParameterComplex.hom.hom.hom =
      (unitPoint R t ≫ gmComplexIso.hom.hom.hom) ≫ (scalarExtension.map splitIso.hom).hom.hom :=
    (Category.assoc _ _ _).symm
  exact (congrArg (baseChangePoint ℝ ℂ splitSubgroup.group.X R) h).trans
    ((baseChangePointsSchemeNaturality ℝ ℂ splitIso.hom.hom.hom R _).trans
      (congrArg (· ≫ splitIso.hom.hom.hom) (gmComplexIso_unit R t)))

set_option backward.isDefEq.respectTransparency false in
private theorem markedSplitTorus
    (T : DiagonalTorus complexSLPoints) (L : LatticeIdentification T)
    (M : RootIdentification T L) (B : UpperTriangularBorel T L M)
    (D : Specs.Pinning.AttachedDatum B.pair) (hD : IsMatrixBasedDatum B D)
    (hpin : HasTransvectionPinning B)
    (p : complexParabolic.val ≅ B.limits.parabolic.group)
    (hp : p.hom ≫ B.limits.parabolic.inclusion = complexLineInclusion) :
    ∃ S : SplitTorusComparison (markedComparison T L M B D hD hpin p hp),
      S.torus = splitSubgroup := by
  obtain ⟨H, hH⟩ := centralizerScheme ℝ (representedGroup false) splitSubgroup
  obtain ⟨i, hi⟩ := splitContainedInCentralizer hH
  obtain ⟨d, hd⟩ := centralizerComplex_diagonal hH T
  let j := scalarExtension.map i ≫ d.hom
  have hj : j ≫ T.subgroup.inclusion = scalarExtension.map splitSubgroup.inclusion ≫ complexSchemeIso.hom := by
    change (scalarExtension.map i ≫ d.hom) ≫ T.subgroup.inclusion = _
    simp only [Category.assoc, hd]
    rw [show (extendSubgroup ℂ H).inclusion = scalarExtension.map H.inclusion from rfl,
      ← Functor.map_comp_assoc, hi]
  have hG := unitary_reductive B.reductive
  let S : SplitTorusComparison (markedComparison T L M B D hD hpin p hp) :=
    { torus := splitSubgroup
      parameter := splitIso
      matrix R t := congrArg (fun x : realMatrixSubgroup false R => x.val.val)
        (splitPoint_formula R t)
      isSplit := splitSubgroup_isSplit
      contained := splitSubgroup_in_line
      reductive := hG
      minimal := minimal_of_kBorel hG lineSubgroup (line_isKBorel B)
      complexParameter := splitParameterComplex
      complexParameterValue := splitParameterComplex_value
      complexInclusion := j
      complexFactor := hj
      absoluteRestriction :=
        (complexRoots_restrict L M _ (cocharacterComplex_matrix i hi T L d hd)).1
      characterExponents := character_exponent_bijective splitIso
      relativeRootExponents := unitary_real_roots T L M }
  exact ⟨S, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem simpleRootRestrictions {C : UnitaryComparison} (S : SplitTorusComparison C) :
    SimpleRootRestrictions S := by
  letI := C.datum.comm
  dsimp only [SimpleRootRestrictions]
  refine ⟨?_, ?_, S.absoluteRestriction _, S.absoluteRestriction _, S.absoluteRestriction _⟩
  · intro r
    obtain ⟨p, rfl⟩ := C.roots.indices.surjective r
    constructor
    · intro hr
      obtain ⟨i, hi, hj⟩ := (C.basedDatum.2 p).mp hr
      fin_cases i
      · exact Or.inl (congrArg C.roots.indices (Subtype.ext (Prod.ext hi hj)))
      · exact Or.inr (congrArg C.roots.indices (Subtype.ext (Prod.ext hi hj)))
    · rintro (h | h)
      · rw [h]
        exact (C.basedDatum.2 ⟨(0, 1), by decide⟩).mpr ⟨0, rfl, rfl⟩
      · rw [h]
        exact (C.basedDatum.2 ⟨(1, 2), by decide⟩).mpr ⟨1, rfl, rfl⟩
  · apply Additive.ofMul.injective
    apply C.lattice.characters.injective
    rw [ofMul_mul, map_add, C.roots.character_eq, C.roots.character_eq, C.roots.character_eq]
    exact root_add

theorem unitaryRootSystem : UnitaryRootSystem := by
  obtain ⟨T, L, M, B, D, hD, hpin, _⟩ :=
    LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixPinnedDatum ℂ 2 complexSL complexSLPoints
  obtain ⟨p, hp⟩ := complexLine_borel B
  obtain ⟨S, _⟩ := markedSplitTorus T L M B D hD hpin p hp
  exact ⟨markedComparison T L M B D hD hpin p hp, S, simpleRootRestrictions S⟩

section Maximality

set_option backward.isDefEq.respectTransparency false

open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Algebra.TensorProduct (includeRight)
open Specs.CharacterPairing (characterValue)
open Specs.CharacterDescent (Character)
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private subgroupInclusionFactors from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
open private characterValue_extend from LinearAlgebraicGroups.Relative.RelativeChambers

private theorem diagonalCharacter_eval (T : DiagonalTorus complexSLPoints)
    (L : LatticeIdentification T) (i : Fin 3) (R : TestAlgebra ℂ)
    (p : Points T.subgroup.group.X R) :
    characterValue (Additive.toMul (L.characters.symm
        ((Submodule.span ℤ ({(1 : Fin 3 → ℤ)} : Set (Fin 3 → ℤ))).mkQ (coordinate 3 i)))) R p =
      (complexSLPoints.hom.app R (p ≫ T.subgroup.inclusion.hom.hom)).val ⟨i⟩ ⟨i⟩ := by
  rw [L.characterValue_eq, T.matrix, Matrix.diagonal_apply_eq]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp [coordinate]
  · intro j _ hj
    simp [coordinate, Pi.single_eq_of_ne hj]
  · simp

private theorem realDiagonal_of_centralizes (R : TestAlgebra ℝ)
    (g : Points (representedGroup false).val.X R)
    (hg : Centralizes splitSubgroup.inclusion g) :
    ∀ i j : Fin 3, i ≠ j → ((representedGroupPointIso false).hom.app R g).val.val i j = 0 := by
  let e := ((representedGroupPointIso false).app R).groupIsoToMulEquiv
  let t := Units.map (algebraMap ℝ R).toMonoidHom twice
  let p := unitPoint R t ≫ splitIso.hom.hom.hom
  have h := (centralizes_iff splitSubgroup.inclusion g).mp hg
    ((testSpec ℝ).obj (.op R)) (𝟙 _) p
  rw [Category.id_comp] at h
  have he := congrArg (fun x : realMatrixSubgroup false R => x.val.val) (h.symm.map e.toMonoidHom).eq
  change Commute (e (p ≫ splitSubgroup.inclusion.hom.hom)).val.val (e g).val.val at he
  rw [show e (p ≫ splitSubgroup.inclusion.hom.hom) = splitPoints R t from splitPoint_formula R t] at he
  have hd : (fun i : Fin 3 => algebraMap R (Complexification R) (diagonalUnits t i)) =
      fun i => (algebraMap R (Complexification R)).comp (algebraMap ℝ R) (diagonalUnits twice i) := by
    funext i
    fin_cases i <;> simp [t, diagonalUnits]
  change Commute (Matrix.diagonal _) (e g).val.val at he
  rw [hd] at he
  exact offDiagonal_of_commutes _ _ diagonal_twice_injective _ he

private theorem unitary_diagonal_with_real_first {R : Type} [CommRing R]
    (g : SL (Complexification R)) (h : IsUnitary g)
    (hd : ∀ i j, i ≠ j → g.val i j = 0) (hi : (g.val 0 0).im = 0) :
    ∃ t : Rˣ, g = splitMatrix t := by
  let z (i : Fin 3) := g.val i i
  have hg : g.val = Matrix.diagonal z := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hd i j hij]
  have hz : z 0 = algebraMap R (Complexification R) (z 0).re := by
    apply QuadraticAlgebra.ext
    · rfl
    · exact hi
  have hs : star (z 0) = z 0 := by
    apply QuadraticAlgebra.ext
    · rw [QuadraticAlgebra.re_star, zero_mul, add_zero]
    · change -(z 0).im = (z 0).im
      rw [show (z 0).im = 0 from hi, neg_zero]
  change g.valᴴ * J _ * g.val = J _ at h
  rw [hg, Matrix.diagonal_conjTranspose] at h
  have hh := congrArg (fun m : Matrix (Fin 3) (Fin 3) (Complexification R) => m 0 2) h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply, hs] at hh
  have hz02 : z 0 * z 2 = 1 := by simpa [J] using hh
  have hr := congrArg QuadraticAlgebra.re hz02
  rw [QuadraticAlgebra.re_mul, show (z 0).im = 0 from hi] at hr
  have hre : (z 0).re * (z 2).re = 1 := by
    change _ = (1 : R) at hr
    simpa using hr
  let t : Rˣ := ⟨(z 0).re, (z 2).re, hre, (mul_comm _ _).trans hre⟩
  have h02 : z 2 = algebraMap R (Complexification R) (↑t⁻¹ : R) := by
    have hu : IsUnit (z 0) := ⟨⟨z 0, z 2, hz02, (mul_comm _ _).trans hz02⟩, rfl⟩
    apply hu.mul_left_cancel
    rw [hz02, hz, ← map_mul, show (z 0).re * (↑t⁻¹ : R) = 1 from hre, map_one]
  have hz1 : z 1 = 1 := by
    have hdet := g.property
    rw [hg, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
    calc
      z 1 = (z 0 * z 2) * z 1 := by rw [hz02, one_mul]
      _ = 1 := (by ac_rfl : (z 0 * z 2) * z 1 = z 0 * z 1 * z 2).trans hdet
  refine ⟨t, Subtype.ext (hg.trans ?_)⟩
  change Matrix.diagonal z = Matrix.diagonal (fun i => algebraMap R _ (diagonalUnits t i))
  congr 1
  funext i
  fin_cases i
  · exact hz
  · simpa [diagonalUnits] using hz1
  · exact h02

private theorem firstEntry_real_of_split
    {A H : ClosedSubgroup (representedGroup false).val}
    (hA : IsSplitTorus A.group)
    (a : A.group ⟶ H.group) (ha : a ≫ H.inclusion = A.inclusion)
    (T : DiagonalTorus complexSLPoints) (L : LatticeIdentification T)
    (d : (extendSubgroup ℂ H).group ≅ T.subgroup.group)
    (hd : d.hom ≫ T.subgroup.inclusion =
      (extendSubgroup ℂ H).inclusion ≫ complexSchemeIso.hom)
    (R : TestAlgebra ℝ) (x : Points A.group.X R) :
    (((representedGroupPointIso false).hom.app R (x ≫ A.inclusion.hom.hom)).val.val 0 0).im = 0 := by
  let j := scalarExtension.map a ≫ d.hom
  have hj : j ≫ T.subgroup.inclusion = scalarExtension.map A.inclusion ≫ complexSchemeIso.hom := by
    change (scalarExtension.map a ≫ d.hom) ≫ T.subgroup.inclusion = _
    simp only [Category.assoc, hd]
    rw [show (extendSubgroup ℂ H).inclusion = scalarExtension.map H.inclusion from rfl,
      ← Functor.map_comp_assoc, ha]
  let χ : Character T.subgroup.group := Additive.toMul (L.characters.symm
    ((Submodule.span ℤ ({(1 : Fin 3 → ℤ)} : Set (Fin 3 → ℤ))).mkQ (coordinate 3 0)))
  obtain ⟨b, hb⟩ := character_descends_of_split hA (j ≫ χ)
  let E := CommAlgCat.of ℂ (ℂ ⊗[ℝ] R)
  let V := (restrictTestAlgebra ℝ ℂ).obj E
  let aR : R →ₐ[ℝ] ℂ ⊗[ℝ] R := includeRight
  let f : R ⟶ V := ConcreteCategory.ofHom
    (@AlgHom.mk ℝ R V _ _ _ R.algebra V.algebra aR.toRingHom (fun r => by
      change aR (algebraMap ℝ R r) = algebraMap ℂ (ℂ ⊗[ℝ] R) (algebraMap ℝ ℂ r)
      rw [aR.commutes, ← IsScalarTower.algebraMap_apply]))
  let x' : Points (scalarExtension.obj A.group).X E :=
    (baseChangePointsEquiv ℂ A.group.X E).symm (mapPoints f x)
  have hx : baseChangePoint ℝ ℂ A.group.X E x' = mapPoints f x :=
    (baseChangePointsEquiv ℂ A.group.X E).apply_symm_apply _
  have hb' := characterValue_extend b gmComplexIso gmComplexIso_unit E x'
  rw [hb, hx] at hb'
  have hv : characterValue b V (mapPoints f x) = f.hom (characterValue b R x) := by
    let p : Points (multLine ℝ).X R := x ≫ b.hom.hom
    let c := ((algSpec.fullyFaithful (R := CommRingCat.of ℝ)).preimage p).unop
    have hc : (testSpec ℝ).map c.op = p :=
      (algSpec.fullyFaithful (R := CommRingCat.of ℝ)).map_preimage p
    have hf : mapPoints f x ≫ b.hom.hom = (testSpec ℝ).map (c ≫ f).op := by
      change ((testSpec ℝ).map f.op ≫ x) ≫ b.hom.hom = _
      rw [Category.assoc]
      change (testSpec ℝ).map f.op ≫ p = _
      rw [← hc, ← Functor.map_comp]
      rfl
    unfold characterValue
    change ((algSpec.fullyFaithful (R := CommRingCat.of ℝ)).preimage
      (mapPoints f x ≫ b.hom.hom)).unop.hom _ = f.hom (c.hom _)
    rw [hf, (algSpec.fullyFaithful (R := CommRingCat.of ℝ)).preimage_map]
    rfl
  rw [hv] at hb'
  have hc : characterValue (j ≫ χ) E x' = characterValue χ E (x' ≫ j.hom.hom) := by
    unfold characterValue
    simp only [Functor.map_comp, Category.assoc]
    rfl
  rw [hc, diagonalCharacter_eval T L] at hb'
  have hm : (x' ≫ j.hom.hom) ≫ T.subgroup.inclusion.hom.hom =
      (x' ≫ (scalarExtension.map A.inclusion).hom.hom) ≫ complexSchemeIso.hom.hom.hom := by
    have hh := (Grp.forget (SchemeOver ℂ)).congr_map hj
    change j.hom.hom ≫ T.subgroup.inclusion.hom.hom =
      (scalarExtension.map A.inclusion).hom.hom ≫ complexSchemeIso.hom.hom.hom at hh
    simpa only [Category.assoc] using congrArg (x' ≫ ·) hh
  rw [hm, complexSchemeIso_eval] at hb'
  have ht := baseChangePointsSchemeNaturality ℝ ℂ A.inclusion.hom.hom E x'
  change baseChangePoint ℝ ℂ (representedGroup false).val.X E
    (x' ≫ (scalarExtension.map A.inclusion).hom.hom) =
    baseChangePoint ℝ ℂ A.group.X E x' ≫ A.inclusion.hom.hom at ht
  have hcomp : mapPoints f x ≫ A.inclusion.hom.hom =
      mapPoints f (x ≫ A.inclusion.hom.hom) := Category.assoc _ _ _
  rw [ht, hx, hcomp] at hb'
  change firstCoordinate E
      (((representedGroupPointIso false).hom.app V
        (mapPoints f (x ≫ A.inclusion.hom.hom))).val.val 0 0) = _ at hb'
  have hn := GrpCat.ext_iff.mp ((representedGroupPointIso false).hom.naturality f)
    (x ≫ A.inclusion.hom.hom)
  change (representedGroupPointIso false).hom.app V
      (mapPoints f (x ≫ A.inclusion.hom.hom)) =
    (realMatrixFunctor false).map f ((representedGroupPointIso false).hom.app R
      (x ≫ A.inclusion.hom.hom)) at hn
  rw [hn] at hb'
  let z := ((representedGroupPointIso false).hom.app R (x ≫ A.inclusion.hom.hom)).val.val 0 0
  change f.hom z.re + f.hom z.im * algebraMap ℂ E Complex.I =
    f.hom (characterValue b R x) at hb'
  have hf (r : R) : f.hom r = (1 : ℂ) ⊗ₜ[ℝ] r := rfl
  have hI : algebraMap ℂ E Complex.I = Complex.I ⊗ₜ[ℝ] (1 : R) := rfl
  rw [hf, hf, hf, hI] at hb'
  obtain ⟨e, he⟩ := complexTensorModel R
  let s : ℂ ⊗[ℝ] R ≃+* Complexification R :=
    (Algebra.TensorProduct.comm ℝ ℂ R).toRingEquiv.trans e.toRingEquiv
  have hs (c : ℂ) (r : R) :
      s (c ⊗ₜ[ℝ] r) = ⟨r * algebraMap ℝ R c.re, r * algebraMap ℝ R c.im⟩ := he r c
  have him := congrArg s hb'
  rw [map_add, map_mul, hs, hs, hs, hs] at him
  have hi := congrArg (fun z : Complexification R => z.im) him
  simpa [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul] using hi

private theorem splitSubgroup_maximal (T : DiagonalTorus complexSLPoints)
    (L : LatticeIdentification T) : IsMaximalSplitTorus splitSubgroup := by
  refine ⟨splitSubgroup_isSplit, ?_⟩
  intro A hA hSA
  obtain ⟨i, hi⟩ := hSA
  obtain ⟨H, hH⟩ := centralizerScheme ℝ (representedGroup false) splitSubgroup
  have hcent (R : TestAlgebra ℝ) (x : Points A.group.X R) :
      Centralizes splitSubgroup.inclusion (x ≫ A.inclusion.hom.hom) :=
    centralizes_of_split_factor splitSubgroup.inclusion A.inclusion i hi hA _ x
  have hAff := (closedSubgroupAlgebraicGroup A).property.1
  obtain ⟨a, ha⟩ := subgroupInclusionFactors hAff H A.inclusion
    (fun R x => (hH _ _).mp (hcent R x))
  obtain ⟨d, hd⟩ := centralizerComplex_diagonal hH T
  apply subgroupInclusionFactors hAff splitSubgroup A.inclusion
  intro R x
  let g := x ≫ A.inclusion.hom.hom
  let E := ((representedGroupPointIso false).app R).groupIsoToMulEquiv
  obtain ⟨t, ht⟩ := unitary_diagonal_with_real_first (E g).val (E g).property.1
    (realDiagonal_of_centralizes R g (hcent R x))
    (firstEntry_real_of_split hA a ha T L d hd R x)
  refine ⟨unitPoint R t ≫ splitIso.hom.hom.hom, E.injective ?_⟩
  apply Subtype.ext
  exact (congrArg Subtype.val (splitPoint_formula R t)).trans ht.symm

end Maximality

section PermutationMatrices

private def signedPermutation (R : Type*) [CommRing R] (s : Equiv.Perm (Fin 3)) : SL R :=
  ⟨Matrix.diagonal (fun i => if i = (1 : Fin 3) then (↑(Equiv.Perm.sign s) : R) else 1) *
      (s⁻¹).permMatrix R, by
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]
    rw [Fin.prod_univ_three]
    simp only [show (0 : Fin 3) ≠ 1 by decide, show (2 : Fin 3) ≠ 1 by decide, ite_false,
      one_mul, mul_one, map_inv]
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp [h]⟩

private theorem signedPermutation_entry (R : Type*) [CommRing R] (s : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (signedPermutation R s).val i j =
      if i = s j then (if i = 1 then (↑(Equiv.Perm.sign s) : R) else 1) else 0 := by
  simp [signedPermutation, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_eq]

private theorem signedPermutation_support (R : Type*) [CommRing R] [Nontrivial R]
    (s : Equiv.Perm (Fin 3)) : HasPermutationSupport s (signedPermutation R s).val := by
  intro i j
  rw [signedPermutation_entry]
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> by_cases hi : i = 1 <;> simp [h, hi]

private theorem signedPermutation_one (R : Type*) [CommRing R] :
    signedPermutation R 1 = 1 := by
  apply Subtype.ext
  simp [signedPermutation]

private theorem signedPermutation_longest (R : Type*) [CommRing R] :
    (signedPermutation R (Equiv.swap 0 2)).val =
      !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  apply Matrix.ext
  intro i j
  rw [signedPermutation_entry, Equiv.Perm.sign_swap (by decide)]
  fin_cases i <;> fin_cases j <;> first | rfl | change ((-1 : ℤ) : R) = -1; simp

private theorem signedPermutation_adjacent (R : Type*) [CommRing R] :
    (signedPermutation R (Equiv.swap 0 1)).val =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  apply Matrix.ext
  intro i j
  rw [signedPermutation_entry, Equiv.Perm.sign_swap (by decide)]
  fin_cases i <;> fin_cases j <;> first | rfl | change ((-1 : ℤ) : R) = -1; simp

private theorem conjugateDiagonal {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (s : Equiv.Perm I) (g : Matrix.SpecialLinearGroup I R)
    (hg : ∀ i j, i ≠ s j → g.val i j = 0) (d : I → R) :
    g.val * Matrix.diagonal d * g⁻¹.val = Matrix.diagonal (fun i => d (s.symm i)) ∧
    g⁻¹.val * Matrix.diagonal d * g.val = Matrix.diagonal (fun i => d (s i)) := by
  have h (d : I → R) :
      g.val * Matrix.diagonal d = Matrix.diagonal (fun i => d (s.symm i)) * g.val := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = s j
    · subst i
      rw [s.symm_apply_apply, mul_comm]
    · simp [hg i j hij]
  constructor
  · rw [h, Matrix.mul_assoc,
      show g.val * g⁻¹.val = (1 : Matrix I I R) from congrArg Subtype.val (mul_inv_cancel g),
      Matrix.mul_one]
  · have hm := h (fun i => d (s i))
    simp only [Equiv.apply_symm_apply] at hm
    rw [Matrix.mul_assoc, ← hm, ← Matrix.mul_assoc,
      show g⁻¹.val * g.val = (1 : Matrix I I R) from congrArg Subtype.val (inv_mul_cancel g),
      Matrix.one_mul]

private theorem monomial_of_conjugates_diagonal {I F : Type*} [Fintype I] [DecidableEq I] [Field F]
    (g : Matrix.SpecialLinearGroup I F) (d e : I → F) (hd : Function.Injective d)
    (h : g.val * Matrix.diagonal d = Matrix.diagonal e * g.val) :
    ∃ s : Equiv.Perm I, ∀ i j, g.val i j ≠ 0 ↔ i = s j := by
  classical
  have he (i j) (hij : g.val i j ≠ 0) : d j = e i := by
    have hh := congrArg (fun m : Matrix I I F => m i j) h
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    rw [mul_comm (e i)] at hh
    exact mul_left_cancel₀ hij hh
  have hcol (j : I) : ∃ i, g.val i j ≠ 0 := by
    by_contra! ha
    have hzero : g.val.det = 0 := Matrix.det_eq_zero_of_column_eq_zero j ha
    rw [g.property] at hzero
    exact one_ne_zero hzero
  choose p hp using hcol
  have hpinj : Function.Injective p := by
    intro j k hjk
    apply hd
    rw [he (p j) j (hp j), he (p k) k (hp k), hjk]
  let s := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hpinj)
  refine ⟨s, ?_⟩
  intro i j
  obtain ⟨k, rfl⟩ := s.surjective i
  change g.val (p k) j ≠ 0 ↔ p k = p j
  refine ⟨fun hj => congrArg p (hd ((he (p k) k (hp k)).trans (he (p k) j hj).symm)), ?_⟩
  rintro hkj
  rw [hkj]
  exact hp j

private theorem differingByDiagonal_of_sameSupport {I F : Type*} [Fintype I] [DecidableEq I]
    [Field F] (s : Equiv.Perm I) (p q : Matrix.SpecialLinearGroup I F)
    (hp : ∀ i j, i ≠ s j → p.val i j = 0)
    (hq : ∀ i j, i ≠ s j → q.val i j = 0) (d : I → F) (hd : Function.Injective d) :
    ∀ i j, i ≠ j → (p⁻¹ * q).val i j = 0 := by
  let c := p⁻¹ * q
  have he : c.val * Matrix.diagonal d = Matrix.diagonal d * c.val := by
    change (p⁻¹.val * q.val) * Matrix.diagonal d = Matrix.diagonal d * (p⁻¹.val * q.val)
    have h₁ := (conjugateDiagonal s q hq d).1
    have h₂ := (conjugateDiagonal s p hp (fun i => d (s.symm i))).2
    simp only [Equiv.symm_apply_apply] at h₂
    have hq' := congrArg (· * q.val) h₁
    rw [Matrix.mul_assoc (q.val * Matrix.diagonal d),
      show q⁻¹.val * q.val = (1 : Matrix I I F) from congrArg Subtype.val (inv_mul_cancel q),
      Matrix.mul_one] at hq'
    have hp' := congrArg (· * p⁻¹.val) h₂
    rw [Matrix.mul_assoc (p⁻¹.val * Matrix.diagonal (fun i => d (s.symm i))),
      show p.val * p⁻¹.val = (1 : Matrix I I F) from congrArg Subtype.val (mul_inv_cancel p),
      Matrix.mul_one] at hp'
    rw [Matrix.mul_assoc, hq', ← Matrix.mul_assoc, hp', Matrix.mul_assoc]
  intro i j hij
  have hc := congrArg (fun m : Matrix I I F => m i j) he
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  by_contra hne
  rw [mul_comm (d i)] at hc
  exact hij (hd (mul_left_cancel₀ hne hc)).symm

end PermutationMatrices

section MatrixRepresentatives

set_option backward.isDefEq.respectTransparency false

open scoped Pointwise
open Specs (SubgroupSections)
open Specs.AbstractPairing (Datum)
open Specs.DatumAndWeyl (Identification)
open Specs.BruhatOrbitParametrization (Cell IsRepresentative)
open Specs.Relative.RelativeBruhat (DoubleOrbit doubleOrbitMap)
open private conjugatesInto_of_affine_points from LinearAlgebraicGroups.RootData.SpecialLinearDatum
open private normalizes_iff_sections from LinearAlgebraicGroups.RootData.BorelNormalizer
open private normalizerLabel normalizer_isRepresentative normalizerLabel_eq
  from LinearAlgebraicGroups.Flag.BruhatCells
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private exists_doubleOrbit range_doubleOrbit from LinearAlgebraicGroups.Relative.RelativeBruhat

private def rationalEvaluation {k : Type} [Field k] (G : GroupScheme k) :
    (𝟙_ (SchemeOver k) ⟶ G.X) ≃* Points G.X (CommAlgCat.of k k) where
  toFun n := (rationalTestIso k).inv ≫ n
  invFun p := (rationalTestIso k).hom ≫ p
  left_inv _ := Iso.hom_inv_id_assoc _ _
  right_inv _ := Iso.inv_hom_id_assoc _ _
  map_mul' := MonObj.comp_mul (rationalTestIso k).inv

private theorem test_of_rational {k : Type} [Field k] {X : SchemeOver k}
    (n : 𝟙_ (SchemeOver k) ⟶ X) (R : TestAlgebra k) :
    toUnit ((testSpec k).obj (.op R)) ≫ n =
      mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) ((rationalTestIso k).inv ≫ n) := by
  change toUnit ((testSpec k).obj (.op R)) ≫ n =
    (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k R)).op ≫ (rationalTestIso k).inv ≫ n
  rw [← Category.assoc]
  exact congrArg (· ≫ n) (Subsingleton.elim _ _)

private theorem normalizes_from_test {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    (A : ClosedSubgroup G.val) (g : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (h : ∀ (R : TestAlgebra k) (x : Points A.group.X R),
      let a := x ≫ A.inclusion.hom.hom
      let p := toUnit ((testSpec k).obj (.op R)) ≫ g
      p * a * p⁻¹ ∈ SubgroupSections A ((testSpec k).obj (.op R)) ∧
      p⁻¹ * a * p ∈ SubgroupSections A ((testSpec k).obj (.op R))) :
    Normalizes A.inclusion g := by
  letI : IsAffine A.group.X.left := (closedSubgroupAlgebraicGroup A).property.1
  letI : IsAffine (𝟙_ (SchemeOver k)).left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of k)))
  apply (normalizesIff k A.inclusion A.isClosedImmersion _ _).mpr
  constructor
  · apply conjugatesInto_of_affine_points A.inclusion g
    intro R t x
    change ∃ y : Points A.group.X R, y ≫ A.inclusion.hom.hom = _
    rw [show t = toUnit _ from Subsingleton.elim _ _]
    exact (h R x).1
  · apply conjugatesInto_of_affine_points A.inclusion g⁻¹
    intro R t x
    let z : Points G.val.X R := t ≫ g⁻¹
    let a : Points G.val.X R := x ≫ A.inclusion.hom.hom
    change ∃ y : Points A.group.X R, y ≫ A.inclusion.hom.hom =
      z * a * z⁻¹
    have hz : z = ((toUnit ((testSpec k).obj (.op R)) ≫ g) : Points G.val.X R)⁻¹ := by
      dsimp only [z]
      rw [show t = toUnit _ from Subsingleton.elim _ _, GrpObj.comp_inv]
    rw [hz, inv_inv]
    exact (h R x).2

private theorem diagonal_of_offDiagonal_zero {I R : Type*} [DecidableEq I] [Zero R]
    (m : Matrix I I R) (h : ∀ i j, i ≠ j → m i j = 0) :
    m = Matrix.diagonal (fun i => m i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij, h i j hij]

private def complexSLMatrices :=
  complexSLPoints ≪≫ liftIndicesIso.symm

private def complexAt (R : TestAlgebra ℂ) : Points complexSL.val.X R ≃* SL R :=
  (complexSLMatrices.app R).groupIsoToMulEquiv

private def complexGround :=
  (rationalEvaluation complexSL.val).trans (complexAt (CommAlgCat.of ℂ ℂ))

private theorem complexAt_mapPoints (R A : TestAlgebra ℂ) (f : R ⟶ A)
    (g : Points complexSL.val.X R) :
    complexAt A (mapPoints f g) = Matrix.SpecialLinearGroup.map f.hom.toRingHom (complexAt R g) :=
  GrpCat.ext_iff.mp (complexSLMatrices.hom.naturality f) g

private theorem complexAt_const (R : TestAlgebra ℂ) (g : 𝟙_ (SchemeOver ℂ) ⟶ complexSL.val.X) :
    complexAt R (toUnit ((testSpec ℂ).obj (.op R)) ≫ g) =
      Matrix.SpecialLinearGroup.map (algebraMap ℂ R) (complexGround g) := by
  rw [test_of_rational, complexAt_mapPoints]
  rfl

private theorem complexDiag_iff (T : DiagonalTorus complexSLPoints)
    (R : TestAlgebra ℂ) (g : Points complexSL.val.X R) :
    g ∈ SubgroupSections T.subgroup ((testSpec ℂ).obj (.op R)) ↔
      ∀ i j : Fin 3, i ≠ j → (complexAt R g).val i j = 0 := by
  rw [T.range]
  constructor
  · intro h i j hij
    change (complexSLPoints.hom.app R g).val ⟨i⟩ ⟨j⟩ = 0
    exact h ⟨i⟩ ⟨j⟩ (fun e => hij (congrArg ULift.down e))
  · intro h i j hij
    have hne : i.down ≠ j.down := fun he => hij (ULift.down_injective he)
    exact h i.down j.down hne

private def complexRepresentative (σ : Equiv.Perm (Fin 3)) :
    𝟙_ (SchemeOver ℂ) ⟶ complexSL.val.X :=
  complexGround.symm (signedPermutation ℂ σ)

private theorem complexRep_matrix (σ : Equiv.Perm (Fin 3)) :
    complexGround (complexRepresentative σ) = signedPermutation ℂ σ :=
  complexGround.apply_symm_apply _

private theorem complexRep_normalizes (T : DiagonalTorus complexSLPoints)
    (σ : Equiv.Perm (Fin 3)) : Normalizes T.subgroup.inclusion (complexRepresentative σ) := by
  apply normalizes_from_test
  intro R x
  let a := x ≫ T.subgroup.inclusion.hom.hom
  let p := toUnit ((testSpec ℂ).obj (.op R)) ≫ complexRepresentative σ
  have ha := (complexDiag_iff T R a).mp ⟨x, rfl⟩
  have hd := diagonal_of_offDiagonal_zero (complexAt R a).val ha
  have hp : ∀ i j, i ≠ σ j → (complexAt R p).val i j = 0 := by
    intro i j hij
    change (complexAt R (toUnit _ ≫ complexRepresentative σ)).val i j = 0
    rw [complexAt_const, complexRep_matrix]
    change (algebraMap ℂ R) ((signedPermutation ℂ σ).val i j) = 0
    rw [signedPermutation_entry, if_neg hij, map_zero]
  have hm := conjugateDiagonal σ (complexAt R p) hp (fun i => (complexAt R a).val i i)
  change (p * a * p⁻¹ ∈ SubgroupSections T.subgroup _) ∧ (p⁻¹ * a * p ∈ SubgroupSections T.subgroup _)
  constructor
  · apply (complexDiag_iff T R _).mpr
    intro i j hij
    simp only [map_mul, map_inv]
    change ((complexAt R p).val * (complexAt R a).val * (complexAt R p)⁻¹.val) i j = 0
    rw [hd, hm.1]
    exact Matrix.diagonal_apply_ne _ hij
  · apply (complexDiag_iff T R _).mpr
    intro i j hij
    simp only [map_mul, map_inv]
    change ((complexAt R p)⁻¹.val * (complexAt R a).val * (complexAt R p).val) i j = 0
    rw [hd, hm.2]
    exact Matrix.diagonal_apply_ne _ hij

private def regularDiagonal : Fin 3 → ℂ := fun i => algebraMap ℝ ℂ (diagonalUnits twice i)

private theorem regularDiagonal_injective : Function.Injective regularDiagonal :=
  (algebraMap ℝ ℂ).injective.comp diagonal_twice_injective

private theorem det_regularDiagonal : (Matrix.diagonal regularDiagonal).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp [regularDiagonal, diagonalUnits, ← map_mul]

private theorem normalizer_hasPermutation (T : DiagonalTorus complexSLPoints)
    (g : 𝟙_ (SchemeOver ℂ) ⟶ complexSL.val.X) (hg : Normalizes T.subgroup.inclusion g) :
    ∃ σ : Equiv.Perm (Fin 3), HasPermutationSupport σ (complexGround g).val := by
  let R := CommAlgCat.of ℂ ℂ
  let X := (testSpec ℂ).obj (.op R)
  let d : SL ℂ := ⟨Matrix.diagonal regularDiagonal, det_regularDiagonal⟩
  let a := (complexAt R).symm d
  have ha : complexAt R a = d := (complexAt R).apply_symm_apply _
  obtain ⟨x, hx⟩ := (complexDiag_iff T R a).mpr (fun i j hij => by
    rw [ha]; exact Matrix.diagonal_apply_ne _ hij)
  have h := ((normalizes_iff_sections T.subgroup g).mp hg X (rationalTestIso ℂ).inv x).1
  let b := (rationalTestIso ℂ).inv ≫ g
  change x ≫ T.subgroup.inclusion.hom.hom = a at hx
  change b * (x ≫ T.subgroup.inclusion.hom.hom) * b⁻¹ ∈ SubgroupSections T.subgroup X at h
  rw [hx] at h
  have hh := (complexDiag_iff T R (b * a * b⁻¹)).mp h
  let y := complexAt R (b * a * b⁻¹)
  have hy := diagonal_of_offDiagonal_zero y.val hh
  have he : complexAt R b = complexGround g := rfl
  have hba : y = complexGround g * d * (complexGround g)⁻¹ := by
    simp only [y, map_mul, map_inv, he, ha]
  let m := complexGround g
  have hc : (m * d * m⁻¹).val = Matrix.diagonal (fun i => y.val i i) :=
    (congrArg Subtype.val hba.symm).trans hy
  have hn := congrArg (· * m.val) hc
  change ((m.val * Matrix.diagonal regularDiagonal) * m⁻¹.val) * m.val =
    Matrix.diagonal (fun i => y.val i i) * m.val at hn
  rw [Matrix.mul_assoc (m.val * Matrix.diagonal regularDiagonal),
    show m⁻¹.val * m.val = (1 : Matrix (Fin 3) (Fin 3) ℂ) from congrArg Subtype.val (inv_mul_cancel m),
    Matrix.mul_one] at hn
  exact monomial_of_conjugates_diagonal m _ _ regularDiagonal_injective hn

/-- On rational points of the normalizer, the kernel of the Weyl label
is precisely the diagonal subgroup. -/
private theorem complex_normalizerLabel_ker (T : DiagonalTorus complexSLPoints)
    [IsCommMonObj T.subgroup.group.X] {D : Datum T.subgroup} (I : Identification D)
    (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X) :
    normalizerLabel I n = 1 ↔
      ∀ i j, i ≠ j → (complexGround (n ≫ I.normalizer.inclusion.hom.hom)).val i j = 0 := by
  let R := CommAlgCat.of ℂ ℂ
  let r := (rationalTestIso ℂ).inv
  let t := n ≫ I.normalizer.inclusion.hom.hom
  have hpt : (complexGround t) = complexAt R (r ≫ t) := rfl
  rw [hpt, ← complexDiag_iff T R (r ≫ t)]
  have hf : (n ≫ I.quotient.hom.hom = 1) ↔ normalizerLabel I n = 1 := by
    refine ⟨fun h => normalizerLabel_eq I (?_ : IsRepresentative I 1 n), fun h => ?_⟩
    · simpa [IsRepresentative, map_one] using h
    · have hp := normalizer_isRepresentative I n
      rw [h] at hp
      simpa [IsRepresentative, map_one] using hp
  rw [← hf, ← schemeKernel_sections I.isQuotient.1]
  have hi := (Grp.forget (SchemeOver ℂ)).congr_map I.inclusion_eq
  change I.torusInclusion.hom.hom ≫ I.normalizer.inclusion.hom.hom = T.subgroup.inclusion.hom.hom at hi
  constructor
  · rintro ⟨x, hx⟩
    change x ≫ I.torusInclusion.hom.hom = n at hx
    refine ⟨r ≫ x, ?_⟩
    change (r ≫ x) ≫ T.subgroup.inclusion.hom.hom = r ≫ t
    rw [Category.assoc, ← hi, ← Category.assoc x, hx]
  · rintro ⟨x, hx⟩
    change x ≫ T.subgroup.inclusion.hom.hom = r ≫ t at hx
    let a := (rationalTestIso ℂ).hom ≫ x
    letI : IsClosedImmersion I.normalizer.inclusion.hom.hom.left := I.normalizer.isClosedImmersion
    letI : Mono I.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
    refine ⟨a, ?_⟩
    change a ≫ I.torusInclusion.hom.hom = n
    apply (cancel_mono I.normalizer.inclusion.hom.hom).mp
    change (((rationalTestIso ℂ).hom ≫ x) ≫ I.torusInclusion.hom.hom) ≫
      I.normalizer.inclusion.hom.hom = t
    rw [Category.assoc, Category.assoc, hi, hx, ← Category.assoc,
      show (rationalTestIso ℂ).hom ≫ r = 𝟙 _ from (rationalTestIso ℂ).hom_inv_id,
      Category.id_comp]

private theorem absolute_labels (T : DiagonalTorus complexSLPoints)
    [IsCommMonObj T.subgroup.group.X] {D : Datum T.subgroup} (I : Identification D)
    (hrep : ∀ w, ∃ n, IsRepresentative I w n) :
    ∃ (n : Equiv.Perm (Fin 3) → (𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X))
      (e : Equiv.Perm (Fin 3) ≃ D.rootDatum.weylGroup),
      (∀ σ, n σ ≫ I.normalizer.inclusion.hom.hom = complexRepresentative σ) ∧
      ∀ σ, IsRepresentative I (e σ) (n σ) := by
  classical
  have h (σ : Equiv.Perm (Fin 3)) :
      ∃ n, n ≫ I.normalizer.inclusion.hom.hom = complexRepresentative σ :=
    (I.representsNormalizer _ _).mp (complexRep_normalizes T σ)
  choose n hn using h
  let f := fun σ => normalizerLabel I (n σ)
  let F := complexGround.toMonoidHom.comp (IsMonHom.monoidHom I.normalizer.inclusion.hom.hom _)
  have hF (σ : Equiv.Perm (Fin 3)) : F (n σ) = signedPermutation ℂ σ :=
    (congrArg complexGround (hn σ)).trans (complexRep_matrix σ)
  have hdiff (a b : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X) :
      normalizerLabel I a = normalizerLabel I b ↔
      ∀ i j, i ≠ j → ((F a)⁻¹ * F b).val i j = 0 := by
    have h := complex_normalizerLabel_ker T I (a⁻¹ * b)
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    change (_ ↔ (∀ i j, i ≠ j → (F (a⁻¹ * b)).val i j = 0)) at h
    simpa only [map_mul, map_inv] using h
  have hf : Function.Bijective f := by
    constructor
    · intro σ τ he
      have hd := (hdiff (n σ) (n τ)).mp he
      rw [hF, hF] at hd
      let a := signedPermutation ℂ σ
      let b := signedPermutation ℂ τ
      let z := a⁻¹ * b
      have hz : z.val = Matrix.diagonal (fun i => z.val i i) :=
        diagonal_of_offDiagonal_zero z.val hd
      have hprod : b.val = a.val * z.val :=
        (congrArg Subtype.val (mul_inv_cancel_left a b)).symm
      rw [hz] at hprod
      apply Equiv.ext
      intro j
      by_contra hij
      have h0 : a.val (τ j) j = 0 :=
        not_ne_iff.mp (fun hh => hij ((signedPermutation_support ℂ σ _ _).mp hh).symm)
      have h1 : b.val (τ j) j ≠ 0 := (signedPermutation_support ℂ τ _ _).mpr rfl
      apply h1
      rw [hprod, Matrix.mul_diagonal, h0, zero_mul]
    · intro w
      obtain ⟨b, hb⟩ := hrep w
      have hg := (I.representsNormalizer _ _).mpr ⟨b, rfl⟩
      obtain ⟨σ, hσ⟩ := normalizer_hasPermutation T _ hg
      refine ⟨σ, ?_⟩
      change normalizerLabel I (n σ) = w
      rw [← normalizerLabel_eq I hb]
      apply (hdiff (n σ) b).mpr
      rw [hF]
      apply differingByDiagonal_of_sameSupport σ _ _ (fun i j hij => ?_)
        (fun i j hij => ?_) regularDiagonal regularDiagonal_injective
      · rw [signedPermutation_entry, if_neg hij]
      · exact not_ne_iff.mp (fun h => hij ((hσ i j).mp h))
  exact ⟨n, Equiv.ofBijective f hf, hn, fun σ => normalizer_isRepresentative I (n σ)⟩

private theorem range_cell_doubleOrbit {T B : ClosedSubgroup complexSL.val}
    {Q : Specs.QuotientEmbedding.Presentation B}
    {a : ModObj complexSL.val.X Q.scheme}
    {n : 𝟙_ (SchemeOver ℂ) ⟶ complexSL.val.X} {U : ClosedSubgroup complexSL.val}
    (C : Cell (T := T) Q a n U) (O : DoubleOrbit B n) :
    Set.range O.inclusion.left = Set.range C.doubleOrbitInclusion.left := by
  rw [range_doubleOrbit]
  obtain ⟨s, hs⟩ := (C.doubleOrbitSections _ (doubleOrbitMap B n)).mpr ⟨fst _ _, snd _ _, rfl⟩
  obtain ⟨p, q, hpq⟩ := (C.doubleOrbitSections _ C.doubleOrbitInclusion).mp ⟨𝟙 _, Category.id_comp _⟩
  have hcomp : lift p q ≫ doubleOrbitMap B n = C.doubleOrbitInclusion := by
    simpa only [doubleOrbitMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, comp_toUnit_assoc]
      using hpq
  apply Set.Subset.antisymm
  · rw [← hs]
    change Set.range (C.doubleOrbitInclusion.left ∘ s.left) ⊆ _
    exact Set.range_comp_subset_range _ _
  · rw [← hcomp]
    change Set.range ((doubleOrbitMap B n).left ∘ (lift p q).left) ⊆ _
    exact Set.range_comp_subset_range _ _

private theorem range_cell_sameDoubleOrbit {T B : ClosedSubgroup complexSL.val}
    {Q : Specs.QuotientEmbedding.Presentation B}
    {a : ModObj complexSL.val.X Q.scheme}
    {n m : 𝟙_ (SchemeOver ℂ) ⟶ complexSL.val.X} {U : ClosedSubgroup complexSL.val}
    (h : n = m) (C : Cell (T := T) Q a n U) (O : DoubleOrbit B m) :
    Set.range O.inclusion.left = Set.range C.doubleOrbitInclusion.left := by
  subst m
  exact range_cell_doubleOrbit C O

private theorem complex_absolute_orbits
    (T : DiagonalTorus complexSLPoints) (L : LatticeIdentification T)
    (M : RootIdentification T L) (B : UpperTriangularBorel T L M)
    (D : Specs.Pinning.AttachedDatum B.pair) (hD : IsMatrixBasedDatum B D)
    (hpin : HasTransvectionPinning B)
    (p : complexParabolic.val ≅ B.limits.parabolic.group)
    (hp : p.hom ≫ B.limits.parabolic.inclusion = complexLineInclusion) :
    Nonempty (UnitaryAbsoluteOrbits (markedComparison T L M B D hD hpin p hp)) := by
  classical
  let P := B.limits.parabolic
  have hP := minimal_of_kBorel B.reductive P B.isBorel
  obtain ⟨comm, E, I, U, Bneg, Rpos, Rneg, c, b, _, _, _, _, _, _, _, _, hrep, _, hcells⟩ :=
    LinearAlgebraicGroups.Flag.BruhatCells.bruhatCells complexSL B.reductive
      T.subgroup P T.split B.maximal B.isBorel B.containsTorus
  letI := comm
  obtain ⟨n, e, hn, hne⟩ := absolute_labels T I hrep
  obtain ⟨⟨Q⟩, hQ⟩ := LinearAlgebraicGroups.ProjectiveFlags.smoothProjectiveQuotient
    ℂ complexSL P hP.1
  obtain ⟨a, _, hcell⟩ := hcells Q
  let r := fun w => n (e.symm w)
  have hr (w : E.rootDatum.weylGroup) : IsRepresentative I w (r w) := by
    simpa only [r, e.apply_symm_apply] using hne (e.symm w)
  obtain ⟨A, Cell, _, hdisj, hcover, _⟩ := hcell r hr
  let O := fun σ => Classical.choice (exists_doubleOrbit hP Q (hQ Q).2.1
    (n σ ≫ I.normalizer.inclusion.hom.hom))
  have hR (σ : Equiv.Perm (Fin 3)) : Set.range (O σ).inclusion.left =
      Set.range (Cell (e σ)).doubleOrbitInclusion.left := by
    apply range_cell_sameDoubleOrbit _ (Cell (e σ)) (O σ)
    simp only [r, e.symm_apply_apply]
  refine ⟨{
    comm := comm
    datum := E
    normalizer := I
    index := e
    cardinality := ?_
    longestReversesOrder := ?_
    lift := n
    representative := hne
    support := ?_
    identity_eq := ?_
    longestMatrix_eq := ?_
    adjacentMatrix_eq := ?_
    orbits := O
    partition := ?_
    disjoint := ?_ }⟩
  · rw [Nat.card_congr e.symm, Nat.card_perm, Nat.card_fin]
    decide
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · intro σ
    change HasPermutationSupport σ (complexGround (n σ ≫ I.normalizer.inclusion.hom.hom)).val
    rw [hn, complexRep_matrix]
    exact signedPermutation_support ℂ σ
  · rw [hn]
    apply complexGround.injective
    rw [complexRep_matrix, signedPermutation_one, map_one]
  · intro i j
    change (complexGround (n longestPermutation ≫ I.normalizer.inclusion.hom.hom)).val i j = _
    rw [hn, complexRep_matrix, signedPermutation_longest]
    rfl
  · intro i j
    change (complexGround (n adjacentPermutation ≫ I.normalizer.inclusion.hom.hom)).val i j = _
    rw [hn, complexRep_matrix, signedPermutation_adjacent]
    rfl
  · calc
      _ = ⋃ σ, Set.range (Cell (e σ)).doubleOrbitInclusion.left := Set.iUnion_congr hR
      _ = ⋃ w, Set.range (Cell w).doubleOrbitInclusion.left :=
        e.surjective.iUnion_comp (fun w => Set.range (Cell w).doubleOrbitInclusion.left)
      _ = _ := hcover
  · intro σ τ hστ
    refine Set.disjoint_left.mpr (fun x hx hy => ?_)
    have hh := (hdisj (e σ) (e τ) (fun h => hστ (e.injective h))).2
    exact Set.disjoint_left.mp hh (hR σ ▸ hx) (hR τ ▸ hy)

end MatrixRepresentatives

section RelativeOrbits

set_option backward.isDefEq.respectTransparency false

open scoped Pointwise
open Specs (SubgroupSections)
open Specs.Relative.RelativeBruhat (DoubleOrbit)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.SimpleParabolicProduct (doubleCoset)
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private isAffine_product_left from LinearAlgebraicGroups.Affine.FixedPointSchemes
open private comp_conjugateFamily centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private representative_mem_doubleCoset from LinearAlgebraicGroups.Flag.BruhatCells

private def realAt (R : TestAlgebra ℝ) :
    Points (representedGroup false).val.X R ≃* realMatrixSubgroup false R :=
  ((representedGroupPointIso false).app R).groupIsoToMulEquiv

private abbrev realGround :=
  (rationalEvaluation (representedGroup false).val).trans (realAt (CommAlgCat.of ℝ ℝ))

private def realRepresentative : 𝟙_ (SchemeOver ℝ) ⟶ (representedGroup false).val.X :=
  realGround.symm ⟨longest (Complexification ℝ), longest_unitary _, fun h => by cases h⟩

private theorem realRepresentative_matrix :
    (realGround realRepresentative).val = longest (Complexification ℝ) :=
  congrArg Subtype.val (realGround.apply_symm_apply _)

private theorem constantRealRepresentative (R : TestAlgebra ℝ) :
    (realAt R (toUnit ((testSpec ℝ).obj (.op R)) ≫ realRepresentative)).val =
      longest (Complexification R) := by
  rw [test_of_rational]
  let f : CommAlgCat.of ℝ ℝ ⟶ R := CommAlgCat.ofHom (Algebra.ofId ℝ R)
  have h := GrpCat.ext_iff.mp ((representedGroupPointIso false).hom.naturality f)
    ((rationalTestIso ℝ).inv ≫ realRepresentative)
  change realAt R (mapPoints f ((rationalTestIso ℝ).inv ≫ realRepresentative)) =
    (realMatrixFunctor false).map f (realGround realRepresentative) at h
  rw [h]
  change Matrix.SpecialLinearGroup.map (complexMap f.hom.toRingHom)
    (realGround realRepresentative).val = _
  rw [realRepresentative_matrix]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change complexMap f.hom.toRingHom (longestMatrix (Complexification ℝ) i j) =
    longestMatrix (Complexification R) i j
  fin_cases i <;> fin_cases j <;>
    first | exact map_zero _ | exact map_one _ | change complexMap f.hom.toRingHom (-1) = -1; simp only [map_neg, map_one]

private theorem realRepresentative_conjugation (R : TestAlgebra ℝ)
    (x : Points splitSubgroup.group.X R) :
    let p := toUnit ((testSpec ℝ).obj (.op R)) ≫ realRepresentative
    let a := x ≫ splitSubgroup.inclusion.hom.hom
    p * a * p⁻¹ = a⁻¹ ∧ p⁻¹ * a * p = a⁻¹ := by
  intro p a
  let E := realAt R
  let t := splitUnits.hom.app R x
  have ha : (E a).val = splitMatrix t := congrArg Subtype.val (splitSubgroup_point R x)
  have hap : (E a).val⁻¹ = splitMatrix t⁻¹ := by
    rw [ha]
    exact (congrArg Subtype.val ((splitPoints R).map_inv t)).symm
  have hp : (E p).val = longest (Complexification R) := constantRealRepresentative R
  let d := fun i => algebraMap R (Complexification R) (diagonalUnits t i)
  let w := longest (Complexification R)
  have hw : ∀ i j : Fin 3, i ≠ longestPermutation j → w.val i j = 0 := by
    intro i j hij
    have hEq : w.val = (signedPermutation (Complexification R) longestPermutation).val :=
      (signedPermutation_longest (Complexification R)).symm
    rw [hEq, signedPermutation_entry, if_neg hij]
  have hrev : (fun i => d (longestPermutation i)) =
      fun i => algebraMap R (Complexification R) (diagonalUnits t⁻¹ i) := by
    funext i
    fin_cases i <;> rfl
  have hh := conjugateDiagonal longestPermutation w hw d
  have hh' : (fun i => d (longestPermutation.symm i)) = fun i => d (longestPermutation i) := rfl
  rw [hh', hrev] at hh
  constructor
  · apply E.injective
    apply Subtype.ext
    apply Subtype.ext
    simp only [map_mul, map_inv]
    change (E p).val.val * (E a).val.val * (E p).val⁻¹.val = (E a).val⁻¹.val
    rw [hap, hp, ha]
    exact hh.1
  · apply E.injective
    apply Subtype.ext
    apply Subtype.ext
    simp only [map_mul, map_inv]
    change (E p).val⁻¹.val * (E a).val.val * (E p).val.val = (E a).val⁻¹.val
    rw [hap, hp, ha]
    exact hh.2

private theorem realRepresentative_normalizes : Normalizes splitSubgroup.inclusion realRepresentative := by
  apply normalizes_from_test
  intro R x
  change _ ∈ SubgroupSections splitSubgroup _ ∧ _ ∈ SubgroupSections splitSubgroup _
  rw [(realRepresentative_conjugation R x).1, (realRepresentative_conjugation R x).2]
  have h : (x ≫ splitSubgroup.inclusion.hom.hom)⁻¹ ∈
      SubgroupSections splitSubgroup ((testSpec ℝ).obj (.op R)) := by
    refine ⟨x⁻¹, ?_⟩
    change x⁻¹ ≫ splitSubgroup.inclusion.hom.hom = _
    exact GrpObj.inv_comp _ _
  exact ⟨h, h⟩

private theorem realRepresentative_inversion :
    conjugateFamily splitSubgroup.inclusion realRepresentative =
      (fst splitSubgroup.group.X (𝟙_ (SchemeOver ℝ)) ≫ splitSubgroup.inclusion.hom.hom)⁻¹ := by
  letI : IsAffine splitSubgroup.group.X.left := (StandardGroups.multiplicativeGroup ℝ).property.1
  letI : IsAffine (𝟙_ (SchemeOver ℝ)).left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of ℝ)))
  apply hom_ext_of_points isAffine_product_left
  intro R y
  rw [comp_conjugateFamily, GrpObj.comp_inv]
  have hy : y ≫ snd splitSubgroup.group.X (𝟙_ (SchemeOver ℝ)) = toUnit _ :=
    Subsingleton.elim _ _
  have hp : y ≫ snd splitSubgroup.group.X (𝟙_ (SchemeOver ℝ)) ≫ realRepresentative =
      toUnit _ ≫ realRepresentative :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ realRepresentative) hy)
  rw [hp]
  exact (realRepresentative_conjugation R (y ≫ fst _ _)).1

private theorem realRepresentative_not_central :
    ¬ Centralizes splitSubgroup.inclusion realRepresentative := by
  intro h
  let R := CommAlgCat.of ℝ ℝ
  let s := unitPoint R twice ≫ splitIso.hom.hom.hom
  let p := s ≫ splitSubgroup.inclusion.hom.hom
  have h' := congrArg (fun f => lift s (toUnit ((testSpec ℝ).obj (.op R))) ≫ f) h
  simp only [comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc] at h'
  have hi := (realRepresentative_conjugation R s).1
  rw [hi] at h'
  have hmat := congrArg (fun q : Points (representedGroup false).val.X R =>
    ((realAt R q).val.val 0 0).re) h'
  have he := splitPoint_formula R twice
  change realAt R p = splitPoints R twice at he
  rw [map_inv, he, ← map_inv (splitPoints R)] at hmat
  norm_num [splitPoints, splitMatrix, diagonalUnits, twice, Matrix.diagonal_apply_eq] at hmat

private def unitaryComplexSubgroup : Subgroup (SL ℂ) where
  carrier := {g | IsUnitary g}
  one_mem' := isUnitary_one _
  mul_mem' := isUnitary_mul
  inv_mem' := isUnitary_inv

private theorem complexCoordinates_star (z : Complexification ℝ) :
    complexCoordinates (star z) = star (complexCoordinates z) := by
  apply Complex.ext
  · change (star z).re = z.re
    simp [QuadraticAlgebra.re_star]
  · rfl

private def realToComplexMatrix : SL (Complexification ℝ) ≃* SL ℂ where
  toFun := Matrix.SpecialLinearGroup.map complexCoordinates.toRingHom
  invFun := Matrix.SpecialLinearGroup.map complexCoordinates.symm.toRingHom
  left_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact complexCoordinates.symm_apply_apply (g.val i j)
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact complexCoordinates.apply_symm_apply (g.val i j)
  map_mul' := map_mul (Matrix.SpecialLinearGroup.map complexCoordinates.toRingHom)

private theorem realToComplex_unitary (g : SL (Complexification ℝ)) :
    IsUnitary (realToComplexMatrix g) ↔ IsUnitary g := by
  let f := complexCoordinates.toRingHom
  have hstar : g.valᴴ.map f = (g.val.map f)ᴴ := by
    ext i j
    exact complexCoordinates_star _
  change (g.val.map f)ᴴ * J ℂ * g.val.map f = J ℂ ↔ g.valᴴ * J _ * g.val = J _
  have hj : (J (Complexification ℝ)).map f = J ℂ := map_J f
  rw [← hj, ← hstar, ← Matrix.map_mul, ← Matrix.map_mul]
  have hf : Function.Injective f := complexCoordinates.injective
  exact ⟨fun h => Matrix.map_injective hf h,
    congrArg (fun m : Matrix (Fin 3) (Fin 3) (Complexification ℝ) => m.map f)⟩

private theorem realToComplex_line (g : SL (Complexification ℝ)) :
    PreservesLine (realToComplexMatrix g) ↔ PreservesLine g := by
  let f := complexCoordinates.toRingHom
  change f (g.val 1 0) = 0 ∧ f (g.val 2 0) = 0 ↔ _
  exact and_congr (map_eq_zero_iff _ complexCoordinates.injective)
    (map_eq_zero_iff _ complexCoordinates.injective)

private def realGroundComplex :
    (𝟙_ (SchemeOver ℝ) ⟶ (representedGroup false).val.X) ≃* unitaryComplexSubgroup :=
  realGround.trans {
    toFun := fun g => ⟨realToComplexMatrix g.val, (realToComplex_unitary g.val).mpr g.property.1⟩
    invFun := fun g => ⟨realToComplexMatrix.symm g.val,
      (realToComplex_unitary _).mp (realToComplexMatrix.apply_symm_apply g.val ▸ g.property),
      fun h => by cases h⟩
    left_inv := fun g => Subtype.ext (realToComplexMatrix.symm_apply_apply g.val)
    right_inv := fun g => Subtype.ext (realToComplexMatrix.apply_symm_apply g.val)
    map_mul' := fun g h => Subtype.ext (map_mul realToComplexMatrix g.val h.val) }

private theorem realRepresentative_overComplex :
    (realGroundComplex realRepresentative).val = longest ℂ := by
  change realToComplexMatrix (realGround realRepresentative).val = _
  rw [realRepresentative_matrix]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change complexCoordinates (longestMatrix (Complexification ℝ) i j) = longestMatrix ℂ i j
  fin_cases i <;> fin_cases j <;>
    first | exact map_zero _ | exact map_one _ | change complexCoordinates (-1) = -1; simp only [map_neg, map_one]

private theorem realGroundComplex_line (g : 𝟙_ (SchemeOver ℝ) ⟶ (representedGroup false).val.X) :
    g ∈ SubgroupSections lineSubgroup (𝟙_ (SchemeOver ℝ)) ↔ PreservesLine (realGroundComplex g).val := by
  let R := CommAlgCat.of ℝ ℝ
  let r := rationalTestIso ℝ
  have h := lineSubgroup_range R (r.inv ≫ g)
  change _ ↔ PreservesLine (realToComplexMatrix (realGround g).val)
  rw [realToComplex_line]
  refine (Iff.trans ?_ h)
  change (∃ p : 𝟙_ (SchemeOver ℝ) ⟶ lineSubgroup.group.X, p ≫ lineSubgroup.inclusion.hom.hom = g) ↔
    ∃ p : Points lineSubgroup.group.X R, p ≫ lineSubgroup.inclusion.hom.hom = r.inv ≫ g
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨r.inv ≫ p, Category.assoc _ _ _⟩
  · rintro ⟨p, hp⟩
    exact ⟨r.hom ≫ p, (Category.assoc _ _ _).trans (hp ▸ r.hom_inv_id_assoc _)⟩

private theorem realCoset_matrix (n g : 𝟙_ (SchemeOver ℝ) ⟶ (representedGroup false).val.X) :
    g ∈ doubleCoset lineSubgroup (𝟙_ (SchemeOver ℝ)) n ↔
      InDoubleCoset (fun a => IsUnitary a ∧ PreservesLine a) (realGroundComplex n).val
        (realGroundComplex g).val := by
  unfold doubleCoset
  have hu : toUnit (𝟙_ (SchemeOver ℝ)) = 𝟙 _ := Subsingleton.elim _ _
  rw [hu, Category.id_comp]
  constructor
  · intro h
    obtain ⟨_, hq', q, hq, rfl⟩ := Set.mem_mul.mp h
    obtain ⟨p, hp, m, hm, rfl⟩ := Set.mem_mul.mp hq'
    rw [Set.mem_singleton_iff] at hm
    subst m
    have he : realGroundComplex (p * n * q) =
        realGroundComplex p * realGroundComplex n * realGroundComplex q := by
      rw [map_mul, map_mul]
    exact ⟨(realGroundComplex p).val, (realGroundComplex q).val,
      ⟨(realGroundComplex p).property, (realGroundComplex_line _).mp hp⟩,
      ⟨(realGroundComplex q).property, (realGroundComplex_line _).mp hq⟩,
      congrArg (fun a : unitaryComplexSubgroup => a.val) he⟩
  · rintro ⟨p, q, hp, hq, h⟩
    let a := realGroundComplex.symm ⟨p, hp.1⟩
    let b := realGroundComplex.symm ⟨q, hq.1⟩
    have ha : (realGroundComplex a).val = p :=
      congrArg Subtype.val (realGroundComplex.apply_symm_apply _)
    have hb : (realGroundComplex b).val = q :=
      congrArg Subtype.val (realGroundComplex.apply_symm_apply _)
    have he : g = a * n * b := by
      apply realGroundComplex.injective
      apply Subtype.ext
      rw [map_mul, map_mul]
      change (realGroundComplex g).val = (realGroundComplex a).val * (realGroundComplex n).val *
        (realGroundComplex b).val
      rwa [ha, hb]
    have ha' : a ∈ SubgroupSections lineSubgroup (𝟙_ (SchemeOver ℝ)) :=
      (realGroundComplex_line a).mpr (ha.symm ▸ hp.2)
    have hb' : b ∈ SubgroupSections lineSubgroup (𝟙_ (SchemeOver ℝ)) :=
      (realGroundComplex_line b).mpr (hb.symm ▸ hq.2)
    exact Set.mem_mul.mpr
      ⟨a * n, Set.mem_mul.mpr ⟨a, ha', n, Set.mem_singleton _, rfl⟩, b, hb', he.symm⟩

private theorem two_real_cosets :
    doubleCoset lineSubgroup (𝟙_ (SchemeOver ℝ)) 1 ∪
      doubleCoset lineSubgroup (𝟙_ (SchemeOver ℝ)) realRepresentative = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨w, hw, _, calcCosets⟩ := realDoubleCosets
  have eq : w = (realGroundComplex realRepresentative).val := Subtype.ext
    (hw.trans (congrArg Subtype.val realRepresentative_overComplex).symm)
  have h := calcCosets (realGroundComplex g).val (realGroundComplex g).property
  rw [eq] at h
  rcases eq_or_ne ((realGroundComplex g).val.val 2 0) 0 with h0 | h0
  · have hm : (realGroundComplex 1).val = 1 :=
      congrArg (fun a : unitaryComplexSubgroup => a.val) realGroundComplex.map_one
    apply Or.inl
    apply (realCoset_matrix 1 g).mpr
    rw [hm]
    exact h.1.mpr h0
  · exact Or.inr ((realCoset_matrix realRepresentative g).mpr (h.2.mpr h0))

private theorem real_relative_orbits
    (T : DiagonalTorus complexSLPoints) (L : LatticeIdentification T)
    (M : RootIdentification T L) (B : UpperTriangularBorel T L M)
    (D : Specs.Pinning.AttachedDatum B.pair) (hD : IsMatrixBasedDatum B D)
    (hpin : HasTransvectionPinning B)
    (p : complexParabolic.val ≅ B.limits.parabolic.group)
    (hp : p.hom ≫ B.limits.parabolic.inclusion = complexLineInclusion)
    (S : SplitTorusComparison (markedComparison T L M B D hD hpin p hp))
    (hS : S.torus = splitSubgroup) : Nonempty (UnitaryRelativeOrbits S) := by
  classical
  let G := representedGroup false
  let C := markedComparison T L M B D hD hpin p hp
  have hm : IsMaximalSplitTorus S.torus := hS.symm ▸ splitSubgroup_maximal T L
  obtain ⟨Q, hZ, e, he, hrep, horbits⟩ := RelativeBruhat.relativeBruhat G S.reductive
    S.torus lineSubgroup hm S.minimal S.contained
  letI := hZ
  have hn : Normalizes S.torus.inclusion realRepresentative := hS.symm ▸ realRepresentative_normalizes
  obtain ⟨z, hz⟩ := (Q.normalizerProperty _ _).mp hn
  let v := e (QuotientGroup.mk z)
  have hv := he z
  change rationalProjection Q z = Q.splitImage.constantGroup.sectionPoint v at hv
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, map_one] at hv
    obtain ⟨a, ha⟩ := (schemeKernel_sections Q.quotientProperty.1 z).mpr hv
    have hj := (Grp.forget (SchemeOver ℝ)).congr_map Q.inclusionProperty
    change Q.inclusion.hom.hom ≫ Q.normalizer.inclusion.hom.hom = Q.centralizer.inclusion.hom.hom at hj
    change a ≫ Q.inclusion.hom.hom = z at ha
    have hc : realRepresentative ∈ SubgroupSections Q.centralizer (𝟙_ (SchemeOver ℝ)) := by
      refine ⟨a, ?_⟩
      change a ≫ Q.centralizer.inclusion.hom.hom = realRepresentative
      rw [← hj, ← Category.assoc, ha, hz]
    exact realRepresentative_not_central (hS ▸ (Q.centralizerProperty _ _).mpr hc)
  let n w := if w = 1 then 1 else if w = v then z else Classical.choose (hrep w)
  have h1 : n 1 = 1 := by simp [n]
  have hnv : n v = z := by simp [n, hv1]
  have nproj (w : Q.splitImage.labels) :
      rationalProjection Q (n w) = Q.splitImage.constantGroup.sectionPoint w := by
    by_cases w1 : w = 1
    · rw [w1, h1, map_one, map_one]
    · by_cases wv : w = v
      · rwa [wv, hnv]
      · simpa only [n, if_neg w1, if_neg wv] using Classical.choose_spec (hrep w)
  let g w := n w ≫ Q.normalizer.inclusion.hom.hom
  have g1 : g 1 = 1 := by
    change n 1 ≫ _ = _
    rw [h1]
    exact (IsMonHom.monoidHom Q.normalizer.inclusion.hom.hom _).map_one
  have gv : g v = realRepresentative := by
    change n v ≫ _ = _
    rwa [hnv]
  obtain ⟨_, hdisj, O, _⟩ := horbits n nproj
  have htwo (w : Q.splitImage.labels) : w = 1 ∨ w = v := by
    by_contra h
    push Not at h
    have hex : g w ∈ doubleCoset lineSubgroup (𝟙_ (SchemeOver ℝ)) (g w) := by
      simpa only [show toUnit (𝟙_ (SchemeOver ℝ)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
        using representative_mem_doubleCoset lineSubgroup (𝟙_ (SchemeOver ℝ)) (g w)
    have hh : g w ∈ doubleCoset lineSubgroup (𝟙_ (SchemeOver ℝ)) 1 ∪
        doubleCoset lineSubgroup (𝟙_ (SchemeOver ℝ)) realRepresentative :=
      two_real_cosets ▸ Set.mem_univ _
    rw [← g1, ← gv] at hh
    exact hh.elim (fun hw => Set.disjoint_left.mp (hdisj h.1) hex hw)
      (fun hw => Set.disjoint_left.mp (hdisj h.2) hex hw)
  refine ⟨{
    quotient := Q
    longestLift := z
    longestLabel := v
    longestProjects := hv
    longestLabel_ne_one := hv1
    twoLabels := htwo
    longestMatrix_eq := ?_
    inversion := ?_
    identityOrbit := ?_
    longestOrbit := ?_
    rationalCover := ?_
    rationalDisjoint := ?_ }⟩
  · change (realGround (z ≫ Q.normalizer.inclusion.hom.hom)).val.val = _
    rw [hz, realRepresentative_matrix]
    rfl
  · rw [hz]
    exact hS.symm ▸ realRepresentative_inversion
  · exact g1 ▸ O 1
  · exact (gv.trans hz.symm) ▸ O v
  · rw [hz]
    exact two_real_cosets
  · rw [hz, ← g1, ← gv]
    exact hdisj (Ne.symm hv1)

end RelativeOrbits

section ComplexifiedOrbits

set_option backward.isDefEq.respectTransparency false

open Specs.Relative.RelativeBruhat (DoubleOrbit doubleOrbitMap)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open private range_doubleOrbit comp_doubleOrbitMap from LinearAlgebraicGroups.Relative.RelativeBruhat

private theorem scalarExtendedPoint_eval {k K : Type} [Field k] [Field K] [Algebra k K]
    (X : SchemeOver k) (n : 𝟙_ (SchemeOver k) ⟶ X) :
    baseChangePoint k K X (CommAlgCat.of K K)
      ((rationalTestIso K).inv ≫ scalarExtendedRationalPoint K n) =
    mapPoints
      (CommAlgCat.ofHom (Algebra.ofId k ((restrictTestAlgebra k K).obj (CommAlgCat.of K K))))
      ((rationalTestIso k).inv ≫ n) := by
  apply Over.OverMorphism.ext
  let f := fieldSpecMap k K
  let F := baseChange k K
  let ε : 𝟙_ (SchemeOver K) ⟶ F.obj (𝟙_ (SchemeOver k)) := Functor.LaxMonoidal.ε F
  have hε : ε.left ≫ pullback.snd (𝟙 (Spec (CommRingCat.of k))) f =
      𝟙 (Spec (CommRingCat.of K)) := Over.w ε
  change ((𝟙 _) ≫ (ε.left ≫ (F.map n).left)) ≫ pullback.fst X.hom f =
    f ≫ (𝟙 _) ≫ n.left
  have hF : (F.map n).left ≫ pullback.fst X.hom f =
      pullback.fst (𝟙 (Spec (CommRingCat.of k))) f ≫ n.left := by
    change ((Over.pullback f).map n).left ≫ pullback.fst X.hom f = _
    exact pullback.lift_fst _ _ _
  rw [Category.id_comp, Category.id_comp, Category.assoc, hF,
    ← Category.assoc ε.left, show pullback.fst (𝟙 (Spec (CommRingCat.of k))) f =
      pullback.snd (𝟙 (Spec (CommRingCat.of k))) f ≫ f from
      (Category.comp_id _).symm.trans pullback.condition, ← Category.assoc, hε]
  exact congrArg (· ≫ n.left) (Category.id_comp f)

private theorem realRepresentative_complexMatrix :
    complexGround (scalarExtendedRationalPoint ℂ realRepresentative ≫ complexSchemeIso.hom.hom.hom) =
      longest ℂ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (complexSLPoints.hom.app (CommAlgCat.of ℂ ℂ)
    (((rationalTestIso ℂ).inv ≫ scalarExtendedRationalPoint ℂ realRepresentative) ≫
      complexSchemeIso.hom.hom.hom)).val ⟨i⟩ ⟨j⟩ = _
  rw [complexSchemeIso_eval, scalarExtendedPoint_eval]
  let R := (restrictTestAlgebra ℝ ℂ).obj (CommAlgCat.of ℂ ℂ)
  let f : CommAlgCat.of ℝ ℝ ⟶ R := CommAlgCat.ofHom (Algebra.ofId ℝ R)
  have h := GrpCat.ext_iff.mp ((representedGroupPointIso false).hom.naturality f)
    ((rationalTestIso ℝ).inv ≫ realRepresentative)
  change (representedGroupPointIso false).hom.app R
      (mapPoints f ((rationalTestIso ℝ).inv ≫ realRepresentative)) =
    (realMatrixFunctor false).map f (realGround realRepresentative) at h
  rw [h]
  change firstCoordinate (CommAlgCat.of ℂ ℂ)
    (complexMap f.hom.toRingHom ((realGround realRepresentative).val.val i j)) =
    longestMatrix ℂ i j
  rw [realRepresentative_matrix]
  let φ := (firstCoordinate (CommAlgCat.of ℂ ℂ)).comp (complexMap f.hom.toRingHom)
  change φ (longestMatrix (Complexification ℝ) i j) = longestMatrix ℂ i j
  fin_cases i <;> fin_cases j <;>
    first | exact map_zero φ | exact map_one φ | change φ (-1) = -1; simp only [map_neg, map_one]

private theorem compare_orbits {C : UnitaryComparison}
    {n : 𝟙_ (SchemeOver ℝ) ⟶ C.realGroup.val.X} {m : 𝟙_ (SchemeOver ℂ) ⟶ C.complexGroup.val.X}
    (O : DoubleOrbit C.line n) (A : DoubleOrbit C.borel.limits.parabolic m)
    (h : m = scalarExtendedRationalPoint ℂ n ≫ C.complexIso.hom.hom.hom) :
    OrbitBaseChangeComparison O A := by
  subst m
  let P := baseChange_doubleOrbit (K := ℂ) O
  let Q := transport_doubleOrbit P C.complexIso C.borelIso C.borelInclusion
  exact doubleOrbit_iso Q A

private theorem orbit_contains_representative {k : Type} [Field k] {G : AffineAlgebraicGroup k}
    {P : ClosedSubgroup G.val} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (O : DoubleOrbit P n) :
    n.left (IsLocalRing.closedPoint k) ∈ Set.range O.inclusion.left := by
  rw [range_doubleOrbit]
  let u : 𝟙_ (SchemeOver k) ⟶ P.group.X := 1
  let p := lift u u
  have h : p ≫ doubleOrbitMap P n = n := by
    rw [comp_doubleOrbitMap]
    simp only [p, lift_fst_assoc, lift_snd_assoc, u, MonObj.one_comp, one_mul, mul_one]
    rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
  exact ⟨p.left (IsLocalRing.closedPoint k),
    congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ G.val.X => f.left (IsLocalRing.closedPoint k)) h⟩

private theorem range_of_orbitComparison {C : UnitaryComparison}
    {n : 𝟙_ (SchemeOver ℝ) ⟶ C.realGroup.val.X} {m : 𝟙_ (SchemeOver ℂ) ⟶ C.complexGroup.val.X}
    (O : DoubleOrbit C.line n) (A : DoubleOrbit C.borel.limits.parabolic m)
    (h : OrbitBaseChangeComparison O A) :
    Set.range ((baseChange ℝ ℂ).map O.inclusion ≫ C.complexIso.hom.hom.hom).left =
      Set.range A.inclusion.left := by
  obtain ⟨e, he⟩ := h
  rw [← he]
  change Set.range (A.inclusion.left ∘ e.hom.left) = _
  have hs : Function.Surjective e.hom.left := e.hom.left.homeomorph.surjective
  rw [Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ]

theorem maximalUnitarySplitTorus : MaximalUnitarySplitTorus := by
  obtain ⟨T, L, M, B, D, hD, hpin, _⟩ :=
    LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixPinnedDatum ℂ 2 complexSL complexSLPoints
  obtain ⟨p, hp⟩ := complexLine_borel B
  obtain ⟨S, hS⟩ := markedSplitTorus T L M B D hD hpin p hp
  exact ⟨markedComparison T L M B D hD hpin p hp, S, hS.symm ▸ splitSubgroup_maximal T L⟩

theorem unitaryCells : UnitaryCells := by
  obtain ⟨T, L, M, B, D, hD, hpin, _⟩ :=
    LinearAlgebraicGroups.RootData.SpecialLinearDatum.matrixPinnedDatum ℂ 2 complexSL complexSLPoints
  obtain ⟨p, hp⟩ := complexLine_borel B
  let C := markedComparison T L M B D hD hpin p hp
  obtain ⟨S, hS⟩ := markedSplitTorus T L M B D hD hpin p hp
  obtain ⟨R⟩ := real_relative_orbits T L M B D hD hpin p hp S hS
  obtain ⟨A⟩ := complex_absolute_orbits T L M B D hD hpin p hp
  have h1 : A.point 1 = scalarExtendedRationalPoint ℂ (1 : 𝟙_ (SchemeOver ℝ) ⟶ C.realGroup.val.X) ≫
      C.complexIso.hom.hom.hom := by
    calc
      A.point 1 = 1 := A.identity_eq
      _ = _ := by
        symm
        letI : GrpObj ((baseChange ℝ ℂ).obj C.realGroup.val.X) :=
          ((groupBaseChange ℝ ℂ).obj C.realGroup.val).grp
        rw [scalarExtendedRationalPoint, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  have hR : R.longestPoint = realRepresentative := by
    apply realGround.injective
    apply Subtype.ext
    apply Subtype.ext
    exact R.longestMatrix_eq.trans (congrArg Subtype.val realRepresentative_matrix).symm
  have hw : A.point longestPermutation =
      scalarExtendedRationalPoint ℂ R.longestPoint ≫ C.complexIso.hom.hom.hom := by
    rw [hR]
    apply complexGround.injective
    change complexGround (A.point longestPermutation) =
      complexGround (scalarExtendedRationalPoint ℂ realRepresentative ≫ complexSchemeIso.hom.hom.hom)
    rw [realRepresentative_complexMatrix]
    apply Matrix.SpecialLinearGroup.ext
    exact A.longestMatrix_eq
  have e1 := compare_orbits R.identityOrbit (A.orbits 1) h1
  have ew := compare_orbits R.longestOrbit (A.orbits longestPermutation) hw
  refine ⟨C, S, hS.symm ▸ splitSubgroup_maximal T L, R, A, e1, ew,
    orbit_contains_representative (A.orbits adjacentPermutation), ?_⟩
  rw [range_of_orbitComparison _ _ e1, range_of_orbitComparison _ _ ew]
  have hAdj := orbit_contains_representative (A.orbits adjacentPermutation)
  have h₁ : adjacentPermutation ≠ 1 := by
    intro h
    have h0 := Equiv.Perm.congr_fun h 0
    exact (by decide : adjacentPermutation 0 ≠ (1 : Equiv.Perm (Fin 3)) 0) h0
  have h₂ : adjacentPermutation ≠ longestPermutation := by
    intro h
    have h0 := Equiv.Perm.congr_fun h 0
    exact (by decide : adjacentPermutation 0 ≠ longestPermutation 0) h0
  rintro (h | h)
  · exact Set.disjoint_left.mp (A.disjoint h₁) hAdj h
  · exact Set.disjoint_left.mp (A.disjoint h₂) hAdj h

end ComplexifiedOrbits

end

end LinearAlgebraicGroups.Relative.RealUnitaryCells
