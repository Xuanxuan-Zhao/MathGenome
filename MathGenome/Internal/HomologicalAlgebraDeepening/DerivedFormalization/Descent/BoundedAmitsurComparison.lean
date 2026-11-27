import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurExactness
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurTotalComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.BoundedAmitsurComparison
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! Exact rows and a lower bound on the internal degree imply that the
augmented Amitsur product totalization is acyclic. -/

open CategoryTheory Limits

namespace DerivedFormalization.Descent.BoundedAmitsurComparison

open AmitsurTotalComplexSpec

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B] (X : Complex.{u, v, w} A)

open private AmitsurExactness.exactAt_iff_function_exact
  AmitsurExactness.augmentation_injective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurExactness

private theorem horizontal_exact (p : ℕ) (q : ℤ) :
    Function.Exact (horizontal A B X p q) (horizontal A B X (p + 1) q) := by
  have h := (AmitsurExactness.exactAt_iff_function_exact A _ ((p : ℤ) + 1)).mp
    (AmitsurExactness.exactAt A B (X.X q) ((p : ℤ) + 1))
  rw [show (p : ℤ) + 1 - 1 = p by omega] at h
  let K := AmitsurComplex.complex A B (X.X q)
  change Function.Exact (K.d (p : ℤ) ((p : ℤ) + 1))
    (K.d (↑(p + 1 : ℕ)) (↑(p + 1 : ℕ) + 1)) at h
  rw [AmitsurComplex.complex_d_ofNat, AmitsurComplex.complex_d_ofNat] at h
  exact h

private theorem diagonalHorizontal_exact (n : ℤ) (p : ℕ) :
    Function.Exact (diagonalHorizontal A B X n p)
      (diagonalHorizontal A B X (n + 1) (p + 1)) := by
  have reindex {q r s : ℤ} (h : q = r) (h' : r = s) :
      Function.Exact (horizontalTo A B X p h) (horizontalTo A B X (p + 1) h') := by
    subst r s
    simpa [horizontalTo] using horizontal_exact A B X p q
  exact reindex _ _

private theorem augmentation_exact (n : ℤ) :
    Function.Exact (AmitsurComplexSpec.augmentation A B (X.X n))
      (diagonalHorizontal A B X n 0) := by
  have h := (AmitsurExactness.exactAt_iff_function_exact A _ 0).mp
    (AmitsurExactness.exactAt A B (X.X n) 0)
  change Function.Exact ((AmitsurComplex.complex A B (X.X n)).d (-1) 0)
    ((AmitsurComplex.complex A B (X.X n)).d (↑(0 : ℕ)) (↑(0 : ℕ) + 1)) at h
  rw [AmitsurComplex.complex_d_neg_one, AmitsurComplex.complex_d_ofNat] at h
  change Function.Exact (AmitsurComplexSpec.augmentation A B (X.X n))
    (horizontal A B X 0 n) at h
  have reindex {r : ℤ} (e : n = r) :
      Function.Exact (AmitsurComplexSpec.augmentation A B (X.X n))
        (horizontalTo A B X 0 e) := by
    subst r
    simpa [horizontalTo] using h
  exact reindex _

omit [Module.FaithfullyFlat A B] in
private theorem step_step (n : ℤ) (y : augmentedTerm A B X n) :
    augmentedStep A B X (n + 1) (augmentedStep A B X n y) = 0 := by
  have h := (augmentedTotal A B X).d_comp_d n (n + 1) (n + 1 + 1)
  rw [augmentedTotal_d_succ, augmentedTotal_d_succ] at h
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) y

omit [Module.FaithfullyFlat A B] in
private theorem cycle_sub_boundary (n : ℤ) (x : augmentedTerm A B X (n + 1))
    (hx : augmentedStep A B X (n + 1) x = 0) (y : augmentedTerm A B X n) :
    augmentedStep A B X (n + 1) (x - augmentedStep A B X n y) = 0 := by
  rw [map_sub, hx, step_step, sub_zero]

omit [Module.FaithfullyFlat A B] in
private theorem augmentedStep_zero (n : ℤ) (x : augmentedTerm A B X n) :
    (augmentedStep A B X n x).1 0 =
      diagonalVertical A B X n 0 (x.1 0) +
        AmitsurComplexSpec.augmentation A B (X.X (n + 1)) x.2 := by
  rw [augmentedStep_apply]
  change step A B X n x.1 0 + (augmentation A B X).f (n + 1) x.2 0 = _
  rw [step_zero]
  rfl

private theorem cycle_augmented_eq_zero (n : ℤ) (x : augmentedTerm A B X (n + 1))
    (hx : augmentedStep A B X (n + 1) x = 0) (h : ∀ p, x.1 p = 0) :
    x = 0 := by
  have h₀ := congrArg (fun z : augmentedTerm A B X (n + 1 + 1) => z.1 0) hx
  change (augmentedStep A B X (n + 1) x).1 0 = 0 at h₀
  rw [augmentedStep_zero, h 0, map_zero, zero_add] at h₀
  have hinj := AmitsurExactness.augmentation_injective A B (X.X (n + 1 + 1))
  have hx₂ : x.2 = 0 := hinj (h₀.trans (map_zero _).symm)
  exact Prod.ext (funext h) hx₂

-- A primitive in column k has a boundary supported in columns k and k+1.
-- The base of the induction uses a primitive in the augmented column.
set_option maxHeartbeats 600000 in
private theorem finite_cycle_is_boundary (n : ℤ) (k : ℕ)
    (x : augmentedTerm A B X (n + 1)) (hx : augmentedStep A B X (n + 1) x = 0)
    (h : ∀ p, k < p → x.1 p = 0) :
    ∃ y : augmentedTerm A B X n, augmentedStep A B X n y = x := by
  induction k generalizing x with
  | zero =>
    have h₁ := congrArg (fun z : augmentedTerm A B X (n + 1 + 1) => z.1 1) hx
    change (augmentedStep A B X (n + 1) x).1 (0 + 1) = 0 at h₁
    rw [AmitsurTotalComplex.augmentedStep_succ, step_succ, h 1 (by omega),
      map_zero, zsmul_zero, add_zero] at h₁
    obtain ⟨a, ha⟩ := (augmentation_exact A B X (n + 1) (x.1 0)).mp h₁
    let y : augmentedTerm A B X n := (0, a)
    have hres : x - augmentedStep A B X n y = 0 := by
      apply cycle_augmented_eq_zero A B X n _ (cycle_sub_boundary A B X n x hx y)
      intro p
      cases p with
      | zero =>
        change x.1 0 - (augmentedStep A B X n y).1 0 = 0
        rw [augmentedStep_zero]
        change x.1 0 - (diagonalVertical A B X n 0 0 +
          AmitsurComplexSpec.augmentation A B (X.X (n + 1)) a) = 0
        rw [map_zero]
        exact sub_eq_zero.mpr (ha.symm.trans (zero_add _).symm)
      | succ p =>
        change x.1 (p + 1) - (augmentedStep A B X n y).1 (p + 1) = 0
        rw [h (p + 1) (by omega), AmitsurTotalComplex.augmentedStep_succ]
        change 0 - step A B X n 0 (p + 1) = 0
        rw [map_zero]
        exact sub_self _
    exact ⟨y, (sub_eq_zero.mp hres).symm⟩
  | succ k ih =>
    have hnext :=
      congrArg (fun z : augmentedTerm A B X (n + 1 + 1) => z.1 (k + 1 + 1)) hx
    change (augmentedStep A B X (n + 1) x).1 (k + 1 + 1) = 0 at hnext
    rw [AmitsurTotalComplex.augmentedStep_succ, step_succ, h (k + 1 + 1) (by omega),
      map_zero, zsmul_zero, add_zero] at hnext
    obtain ⟨a, ha⟩ := (diagonalHorizontal_exact A B X n k (x.1 (k + 1))).mp hnext
    let y : augmentedTerm A B X n :=
      (Pi.single (M := fun p => cell A B X p (rowIndex n p)) k a, 0)
    have hy_ne (j : ℕ) (hj : j ≠ k) : y.1 j = 0 := by
      change Pi.single (M := fun p => cell A B X p (rowIndex n p)) k a j = 0
      rw [Pi.single_eq_of_ne hj]
    have hres : ∀ p, k < p → (x - augmentedStep A B X n y).1 p = 0 := by
      intro p hp
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, p = j + 1 := ⟨p - 1, by omega⟩
      change x.1 (j + 1) - (augmentedStep A B X n y).1 (j + 1) = 0
      have hv := hy_ne (j + 1) (by omega)
      rw [AmitsurTotalComplex.augmentedStep_succ, step_succ, hv, map_zero, zsmul_zero, add_zero]
      by_cases hj : j = k
      · subst j
        have hy : y.1 k = a := Pi.single_eq_same _ _
        rw [hy, ha, sub_self]
      · rw [hy_ne j hj, map_zero, sub_zero, h (j + 1) (by omega)]
    obtain ⟨z, hz⟩ := ih _ (cycle_sub_boundary A B X n x hx y) hres
    exact ⟨z + y, by rw [map_add, hz, sub_add_cancel]⟩

private theorem augmentedTotal_acyclic (lower : ℤ) (hlower : X.IsStrictlyGE lower) :
    (augmentedTotal A B X).Acyclic := by
  intro q
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = q := ⟨q - 1, by omega⟩
  apply (AmitsurExactness.exactAt_iff_function_exact A _ (n + 1)).mpr
  rw [add_sub_cancel_right, augmentedTotal_d_succ, augmentedTotal_d_succ]
  intro x
  constructor
  · intro hx
    refine finite_cycle_is_boundary A B X n (Int.toNat (n + 1 - lower)) x hx ?_
    intro p hp
    have hrow : rowIndex (n + 1) p < lower := by
      rw [rowIndex_eq]
      omega
    have : Subsingleton (X.X (rowIndex (n + 1) p)) :=
      ModuleCat.isZero_iff_subsingleton.mp (X.isZero_of_isStrictlyGE lower _ hrow)
    exact Subsingleton.elim _ _
  · rintro ⟨y, rfl⟩
    exact step_step A B X n y

private theorem common_augmentation_quasiIso (lower : ℤ) (hlower : X.IsStrictlyGE lower) :
    QuasiIso (augmentation A B X) := by
  let f := augmentation A B X
  have hcone : (CochainComplex.mappingCone f).Acyclic :=
    fun n => (augmentedTotal_acyclic A B X lower hlower n).of_iso (coneIso A B X).symm
  apply (HomologicalComplex.mem_quasiIso_iff f).mp
  rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic _).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).mpr
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mpr hcone)

/-- For faithfully flat base change, the canonical augmentation into the
Amitsur product totalization is a quasi-isomorphism on bounded-below complexes. -/
theorem augmentation_quasiIso (Y : AmitsurTotalComplex.Independent.Input.{u, w} A)
    (lower : ℤ) (hlower : Y.IsStrictlyGE lower) :
    QuasiIso (AmitsurTotalComplex.Independent.augmentation.{u, v, w} A B Y) := by
  let L := (AmitsurTotalComplex.Independent.lift.{u, v, w} A).obj Y
  have hL : L.IsStrictlyGE lower :=
    (Y.isStrictlyGE_mapHomologicalComplex_obj_iff (ModuleCat.uliftFunctor.{max u v, w} A)
      lower).mpr hlower
  let e := AmitsurTotalComplex.Independent.totalIso.{u, v, w} A B Y
  have hIso : QuasiIso e.hom := by
    have : IsIso e.hom := e.isIso_hom
    exact quasiIso_of_isIso e.hom
  have hAug := common_augmentation_quasiIso A B L lower hL
  rw [AmitsurTotalComplex.Independent.augmentation_comparison A B Y]
  exact quasiIso_comp (augmentation A B L) e.hom (hφ := hAug) (hφ' := hIso)

end DerivedFormalization.Descent.BoundedAmitsurComparison
