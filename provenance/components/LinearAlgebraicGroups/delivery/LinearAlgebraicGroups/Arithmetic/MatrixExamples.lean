import Specs.LinearAlgebraicGroups.Arithmetic.MatrixExamples
import LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.Tactic.Ring

noncomputable section

open AlgebraicGeometry CategoryTheory
open Matrix (SpecialLinearGroup single)
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)

namespace LinearAlgebraicGroups.Arithmetic.MatrixExamples

open AdelicGroups ApproximationOfLocalWords
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.IntegralModels (MatrixRealization)
open Specs.MatrixExamples
open Specs.Unipotent (Index)
open Matrix.SpecialLinearGroup

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The rank-one diagonal word on coordinates `i` and `j`. -/
private theorem diag2n_eq_transvections {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {i j : ι} (hij : i ≠ j) (t : F) (ht : t ≠ 0) :
    diag2n hij t ht =
      (transvection hij t * transvection hij.symm (-t⁻¹) * transvection hij t) *
      (transvection hij (-1) * transvection hij.symm 1 * transvection hij (-1)) := by
  have single_mul_of_ne {l m : ι} (hlm : l ≠ m) (r s : ι) (a b : F) :
      single r l a * single m s b = 0 :=
    Matrix.single_mul_single_of_ne a r l m hlm b
  have hw (a : F) (ha : a ≠ 0) :
      (transvection hij a * transvection hij.symm (-a⁻¹) * transvection hij a).val =
        (1 - single i i 1 - single j j 1) + single i j a + single j i (-a⁻¹) := by
    simp only [coe_mul, transvection_coe, Matrix.add_mul, Matrix.mul_add, one_mul, mul_one,
      Matrix.single_mul_single_same, single_mul_of_ne hij.symm, add_zero,
      mul_neg, neg_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
    split_ifs <;> ring
  have hm : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hwm := hw (-1) hm
  simp only [inv_neg, inv_one, neg_neg] at hwm
  apply Subtype.ext
  rw [coe_mul, hw t ht, hwm]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, one_mul, mul_one,
    Matrix.single_mul_single_same, single_mul_of_ne hij, single_mul_of_ne hij.symm,
    add_zero, mul_neg, neg_neg, diag2n_coe]
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hxi : x = i
    · subst x
      simp [hij.symm]
    · by_cases hxj : x = j
      · subst x
        simp [hij.symm, hij]
      · simp [hxi, Ne.symm hxi, hxj, Ne.symm hxj]
  · have hi : ¬(i = x ∧ i = y) := fun h => hxy (h.1.symm.trans h.2)
    have hj : ¬(j = x ∧ j = y) := fun h => hxy (h.1.symm.trans h.2)
    simp [hxy, hi, hj]

private theorem mem_of_transvections {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [Field F] (H : Subgroup (SpecialLinearGroup ι F))
    (h : ∀ i j (hij : i ≠ j) (a : F), transvection hij a ∈ H) (g : SpecialLinearGroup ι F) :
    g ∈ H := by
  apply diagonal_transvection_induction' (fun g => g ∈ H) g _ h
    (fun _ _ => H.mul_mem)
  intro i j hij t ht
  rw [diag2n_eq_transvections hij t ht]
  exact H.mul_mem (H.mul_mem (H.mul_mem (h _ _ _ _) (h _ _ _ _)) (h _ _ _ _))
    (H.mul_mem (H.mul_mem (h _ _ _ _) (h _ _ _ _)) (h _ _ _ _))

private abbrev OffDiagonal (n : ℕ) := {ij : Index.{0} n × Index.{0} n // ij.1 ≠ ij.2}

/-- The elementary matrix with the universal affine-line coordinate as its entry. -/
private def transvectionParameter {n : ℕ} {G : AffineAlgebraicGroup ℚ}
    (s : SpecialMatrixPoints G n) (ij : OffDiagonal n) :
    ParameterSpace ℚ 1 ⟶ G.val.X :=
  (s.inv.app (CommAlgCat.of ℚ (MvPolynomial (Fin 1) ℚ)))
    (transvection ij.2 (MvPolynomial.X 0))

private theorem map_transvection {ι R T : Type} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing T] {i j : ι} (hij : i ≠ j) (φ : R →+* T) (a : R) :
    SpecialLinearGroup.map φ (transvection hij a) = transvection hij (φ a) := by
  apply Subtype.ext
  change φ.mapMatrix (1 + single i j a) = 1 + single i j (φ a)
  rw [map_add, map_one]
  exact congrArg (1 + ·) (Matrix.map_single i j a φ)

set_option maxHeartbeats 2000000 in
private theorem evaluate_transvectionParameter {n : ℕ} {G : AffineAlgebraicGroup ℚ}
    (s : SpecialMatrixPoints G n) (ij : OffDiagonal n)
    {R : Type} [CommRing R] [Algebra ℚ R] (a : Fin 1 → R) :
    (s.hom.app (CommAlgCat.of ℚ R)) (evaluate (transvectionParameter s ij) a) =
      transvection ij.2 (a 0) := by
  let b := CommAlgCat.ofHom (MvPolynomial.aeval (R := ℚ) a)
  have h := congrArg
    (fun f => f (transvectionParameter s ij)) (s.hom.naturality b)
  change s.hom.app (CommAlgCat.of ℚ R) (evaluate (transvectionParameter s ij) a) =
    SpecialLinearGroup.map (MvPolynomial.aeval a).toRingHom
      (s.hom.app (CommAlgCat.of ℚ (MvPolynomial (Fin 1) ℚ)) (transvectionParameter s ij)) at h
  refine h.trans ((congrArg (SpecialLinearGroup.map (MvPolynomial.aeval a).toRingHom)
    (GrpCat.hom_inv_apply (s.app (CommAlgCat.of ℚ (MvPolynomial (Fin 1) ℚ))) _)).trans ?_)
  rw [map_transvection]
  exact congrArg (transvection ij.2) (MvPolynomial.aeval_X a 0)

private theorem strongApproximationOfSpecialMatrixPoints {n : ℕ} (hn : 2 ≤ n)
    {G : AffineAlgebraicGroup ℚ} (s : SpecialMatrixPoints G n) (i : MatrixRealization G)
    (D : GlobalFieldData.{0, 0} ℚ) (S : Finset D.Place) (hS : S.Nonempty) :
    StrongApproximation D i S := by
  classical
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let f := transvectionParameter s
  apply localDenseGeneration D i S hS (n := fun _ : OffDiagonal n => 1) f
  · intro ij
    let e := s.app (CommAlgCat.of ℚ ℚ)
    apply (Function.LeftInverse.injective (GrpCat.inv_hom_apply e))
    change s.hom.app (CommAlgCat.of ℚ ℚ)
      (evaluate (transvectionParameter s ij) (0 : Fin 1 → ℚ)) = e.hom 1
    rw [evaluate_transvectionParameter, Pi.zero_apply, transvection_coeff_zero, map_one]
  · intro w
    have hevery (g : LocalPoints D i w.1) :
        g ∈ generatedAt f D i w.1 := by
      let e := s.app (CommAlgCat.of ℚ (D.Completion w.1))
      let H := (generatedAt f D i w.1).comap e.inv.hom
      have htrans (l m : Index.{0} n) (hlm : l ≠ m) (a : D.Completion w.1) :
          transvection hlm a ∈ H := by
        let ij : OffDiagonal n := ⟨(l, m), hlm⟩
        apply Subgroup.subset_closure
        refine ⟨ij, fun _ => a, ?_⟩
        apply (Function.LeftInverse.injective (GrpCat.inv_hom_apply e))
        rw [GrpCat.hom_inv_apply e]
        exact evaluate_transvectionParameter s ij (fun _ => a)
      have hg := mem_of_transvections H htrans (e.hom g)
      change e.inv (e.hom g) ∈ generatedAt f D i w.1 at hg
      simpa only [GrpCat.inv_hom_apply e] using hg
    intro g
    exact subset_closure (s := (generatedAt f D i w.1 :
      Set (LocalPoints D i w.1))) (hevery g)

theorem rationalStrongApproximation : RationalStrongApproximation := by
  intro n hn
  let G := StandardGroups.specialLinearGroup ℚ (Index.{0} n)
  let s : SpecialMatrixPoints G n := StandardGroups.specialLinearGroupPointsIso ℚ (Index.{0} n)
  obtain ⟨m, L, ⟨e⟩, f, hf⟩ := LinearAlgebraicGroups.faithfulLinearization ℚ G
  exact ⟨G, ⟨s⟩, ⟨⟨m, L, e, f, hf⟩⟩, fun i =>
    strongApproximationOfSpecialMatrixPoints hn s i rationalPlaces archimedeanPlaces
      (Finset.singleton_nonempty _)⟩

theorem realNoncompact : RealNoncompact := by
  intro n hn hc
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  let entry (g : SpecialLinearGroup (Fin n) ℝ) : ℝ := g.val i j
  have hentry : Continuous entry :=
    continuous_subtype_val.matrix_elem i j
  have hsurj : Function.Surjective entry := by
    intro a
    exact ⟨transvection hij a, by simp [entry, transvection_coe, hij]⟩
  apply not_bddAbove_univ (α := ℝ)
  rw [← Set.range_eq_univ.mpr hsurj, ← Set.image_univ]
  exact (hc.image hentry).bddAbove

end LinearAlgebraicGroups.Arithmetic.MatrixExamples
