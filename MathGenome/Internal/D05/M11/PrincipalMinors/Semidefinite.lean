import MathGenome.Internal.Specs.D05.M11.PrincipalMinors.Semidefinite
import MathGenome.Internal.D05.M11.PrincipalMinors.Leading
import MathGenome.Internal.D05.M11.Inertia
import MathGenome.Internal.D05.M11.HermitianInertia
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.IntervalCases

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace D05.M11.PrincipalMinors.Semidefinite
open Specs.D05.M11.PrincipalMinors.Semidefinite

/-- Expand by selecting rows of A or rows of tI. The complementary identity
rows leave the principal determinant, with no cofactor sign. -/
theorem determinant_expansion : Specs.D05.M11.PrincipalMinors.Semidefinite.determinant_expansion := by
  intro R n _ _ _ A t
  classical
  let D := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
  change D ((fun i => A i) + (fun i => (t • (1 : Matrix n n R)) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hr : s.piecewise (fun i => A i) (fun i => (t • (1 : Matrix n n R)) i) =
      fun i => (if i ∈ s then 1 else t) • s.piecewise A (1 : Matrix n n R) i := by
    funext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hr, D.map_smul_univ]
  change (∏ i, if i ∈ s then 1 else t) *
    (Matrix.of (s.piecewise A.row (1 : Matrix n n R).row)).det = _
  rw [det_piecewise_one_eq_submatrix_det]
  congr 1
  simp [Finset.prod_ite, ← Finset.sdiff_eq_filter, Finset.card_sdiff]


variable {K n m : Type*} [RCLike K] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

theorem allPrincipal_submatrix {A : Matrix n n K} (hA : AllPrincipalNonnegative A)
    (f : m → n) (hf : Function.Injective f) : AllPrincipalNonnegative (A.submatrix f f) := by
  classical
  intro s
  let emb : m ↪ n := ⟨f, hf⟩
  let e : s ≃ s.map emb := Finset.equivMap emb s
  have h := hA (s.map emb)
  rw [← det_submatrix_equiv_self e] at h
  convert h using 1
  congr 1

theorem shifted_determinant_positive :
    Specs.D05.M11.PrincipalMinors.Semidefinite.shifted_determinant_positive := by
  intro K n _ _ _ A hA ε hε
  classical
  rw [shift, determinant_expansion, map_sum]
  have hterm (s : Finset n) :
      RCLike.re ((ε : K) ^ (Fintype.card n - s.card) *
        (A.submatrix (Subtype.val : s → n) Subtype.val).det) =
      ε ^ (Fintype.card n - s.card) *
        RCLike.re (A.submatrix (Subtype.val : s → n) Subtype.val).det := by
    rw [← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
  simp_rw [hterm]
  apply Finset.sum_pos' (fun s _ => mul_nonneg (pow_nonneg hε.le _) (hA s))
  refine ⟨∅, Finset.mem_univ _, ?_⟩
  simpa using pow_pos hε (Fintype.card n)

theorem shift_submatrix (A : Matrix n n K) (ε : ℝ) (f : m → n)
    (hf : Function.Injective f) :
    (shift A ε).submatrix f f = shift (A.submatrix f f) ε := by
  simp [shift, submatrix_add, submatrix_smul, submatrix_one _ hf]

theorem shifted_positive_definite :
    Specs.D05.M11.PrincipalMinors.Semidefinite.shifted_positive_definite := by
  intro K _ n A hA hp ε hε
  have hshift : (shift A ε).IsHermitian := by
    exact hA.add (Matrix.isHermitian_one.smul (RCLike.conj_ofReal ε))
  apply (D05.M11.PrincipalMinors.Leading.strict_criterion (shift A ε) hshift).mpr
  intro k hk _
  rw [Specs.D05.M11.PrincipalMinors.Leading.leadingBlock, shift_submatrix]
  exact shifted_determinant_positive _
    (allPrincipal_submatrix hp _ (Fin.castLE_injective hk)) ε hε
  exact Fin.castLE_injective hk

theorem limit_nonnegative : Specs.D05.M11.PrincipalMinors.Semidefinite.limit_nonnegative := by
  intro K _ n A hp x
  by_cases hx : x = 0
  · simp [hx]
  have hε (ε : ℝ) (hε : 0 < ε) :
      0 ≤ RCLike.re (star x ⬝ᵥ shift A ε *ᵥ x) := (hp ε hε x hx).le
  have hc : Continuous (fun ε : ℝ => RCLike.re (star x ⬝ᵥ shift A ε *ᵥ x)) := by
    unfold shift
    fun_prop
  have hh := ge_of_tendsto (hc.continuousWithinAt.tendsto :
    Filter.Tendsto (fun ε : ℝ => RCLike.re (star x ⬝ᵥ shift A ε *ᵥ x))
      (nhdsWithin 0 (Set.Ioi 0)) _) (Filter.eventually_of_mem self_mem_nhdsWithin hε)
  simpa [shift] using hh


/-- Congruence scales determinants by a squared absolute value. -/
theorem congruence_determinant (H P : Matrix n n K) :
    RCLike.re (Pᵀ * H * P.map star).det = ‖P.det‖ ^ 2 * RCLike.re H.det := by
  have heq : (Pᵀ * H * P.map star).det = (‖P.det‖ ^ 2 : ℝ) * H.det := by
    rw [det_mul, det_mul, det_transpose]
    have hm : (P.map star).det = star P.det := (RingHom.map_det (starRingEnd K) P).symm
    rw [hm]
    calc P.det * H.det * star P.det = (P.det * star P.det) * H.det := by ring
         _ = _ := by rw [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow]
  rw [heq, RCLike.re_ofReal_mul]

theorem congruence_determinant_scaling :
    Specs.D05.M11.PrincipalMinors.Semidefinite.congruence_determinant_scaling := by
  intro K n _ _ _ H P
  refine ⟨congruence_determinant H P, ?_⟩
  intro hP
  have hd : P.det ≠ 0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det P).mp hP)
  exact sq_pos_of_pos (norm_pos_iff.mpr hd)

theorem principal_determinants_real :
    Specs.D05.M11.PrincipalMinors.Semidefinite.principal_determinants_real := by
  intro K n _ _ _ A hA s
  apply RCLike.conj_eq_iff_im.mp
  change star (A.submatrix (Subtype.val : s → n) Subtype.val).det = _
  rw [← det_conjTranspose, (hA.submatrix _).eq]

open Specs.D05.M11.Inertia.MaximalPositive

/-- In an inertia basis every diagonal value is nonnegative. Transporting back
multiplies its determinant by a squared absolute value. -/
theorem normal_form_det_nonnegative {k p q r : ℕ}
    (B : Form K (Fin k → K)) (e : (Fin k → K) ≃ₗ[K] Coordinates K p q r)
    (he : IsNormalForm B e) (hB : Specs.D05.M11.Hermitian.isHermitian_value B)
    (hp : ∀ x, 0 ≤ RCLike.re (B x x)) :
    0 ≤ RCLike.re (Specs.D05.M11.Hermitian.formMatrix_value (Pi.basisFun K (Fin k)) B).det := by
  classical
  let b := normalBasis e
  let a := b.indexEquiv (Pi.basisFun K (Fin k))
  let c := b.reindex a
  let H := Specs.D05.M11.Hermitian.formMatrix_value c B
  have hnormal := (D05.M11.Inertia.MaximalPositive.normal_form_matrix B e).mp he
  have hdiag : H = diagonal (fun i => B (c i) (c i)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [H, Specs.D05.M11.Hermitian.formMatrix_value]
    · rw [diagonal_apply_ne _ hij]
      have hab : a.symm i ≠ a.symm j := a.symm.injective.ne hij
      have h := congrArg (fun M => M (a.symm i) (a.symm j)) hnormal
      simpa [H, Specs.D05.M11.Hermitian.formMatrix_value, c, b,
        normalMatrix, diagonal_apply_ne _ hab] using h
  have hd : 0 ≤ H.det := by
    rw [hdiag, det_diagonal]
    apply Finset.prod_nonneg
    intro i _
    apply RCLike.nonneg_iff.mpr
    exact ⟨hp (c i), RCLike.conj_eq_iff_im.mp (hB (c i) (c i)).symm⟩
  have hc := D05.M11.Hermitian.change_basis c (Pi.basisFun K (Fin k)) B
  rw [hc, congruence_determinant]
  exact mul_nonneg (sq_nonneg _) (RCLike.nonneg_iff.mp hd).1

private def matrixForm {k : ℕ} (A : Matrix (Fin k) (Fin k) K) : Form K (Fin k → K) :=
  Matrix.toLinearMapₛₗ₂' K (RingHom.id K) (starRingEnd K) Aᵀ

private theorem matrixForm_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) K)
    (x y : Fin k → K) : matrixForm A x y = star y ⬝ᵥ A *ᵥ x := by
  simp only [matrixForm, Matrix.toLinearMapₛₗ₂'_apply, RingHom.id_apply,
    starRingEnd_apply, smul_eq_mul, transpose_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change x j * (star (y i) * A i j) = star (y i) * (A i j * x j)
  ring

private theorem matrixForm_hermitian {k : ℕ} (A : Matrix (Fin k) (Fin k) K)
    (hA : A.IsHermitian) : Specs.D05.M11.Hermitian.isHermitian_value (matrixForm A) := by
  intro x y
  simp only [matrixForm_apply]
  exact (hA.star_dotProduct_mulVec_comm y x).symm

private theorem matrixForm_matrix {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    Specs.D05.M11.Hermitian.formMatrix_value (Pi.basisFun K (Fin k)) (matrixForm A) = Aᵀ := by
  ext i j
  simp [Specs.D05.M11.Hermitian.formMatrix_value, matrixForm, Pi.basisFun_apply]

/-- Necessity from complex Hermitian inertia, with no positivity certificate
assumed and with the zero-dimensional case retained. -/
theorem complex_determinant_nonnegative {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (hp : ∀ x, 0 ≤ RCLike.re (star x ⬝ᵥ A *ᵥ x)) :
    0 ≤ RCLike.re A.det := by
  let B := matrixForm A
  have hB := matrixForm_hermitian A hA
  obtain ⟨p, q, r, e, he⟩ := D05.M11.HermitianInertia.normal_form_exists B hB
  have hd := normal_form_det_nonnegative B e he hB (by simpa [B, matrixForm_apply] using hp)
  simpa [B, matrixForm_matrix, det_transpose] using hd


/-- The real symmetric necessity uses the real inertia theorem and the same
congruence computation as in the complex case. -/
theorem real_determinant_nonnegative {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsSymm) (hp : ∀ x, 0 ≤ x ⬝ᵥ A *ᵥ x) : 0 ≤ A.det := by
  let B := A.toBilin'
  have hB : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hA
  obtain ⟨p, q, r, e, he⟩ := D05.M11.Inertia.normal_form_exists B hB
  obtain ⟨S, hS, hHS, _⟩ := D05.M11.Inertia.MaximalPositive.real_bilinear_bridge B
  have heS : IsNormalForm S e := by
    simpa only [IsNormalForm, Specs.D05.M11.Inertia.IsNormalForm, hS, star_trivial] using he
  have hd := normal_form_det_nonnegative S e heS (hHS.mpr hB) (by
    intro x
    simpa only [hS, B, Matrix.toBilin'_apply', RCLike.re_to_real] using hp x)
  have hm : Specs.D05.M11.Hermitian.formMatrix_value (Pi.basisFun ℝ (Fin k)) S = A := by
    ext i j
    simp [Specs.D05.M11.Hermitian.formMatrix_value, hS, B, Pi.basisFun_apply]
  simpa only [hm, RCLike.re_to_real] using hd


/-- Bridge the real-part convention to Mathlib's star order. -/
theorem positiveSemidefinite_iff_posSemidef (A : Matrix n n K) (hA : A.IsHermitian) :
    Specs.D05.M11.Definiteness.positiveSemidefinite_value
      (fun x y => star y ⬝ᵥ A *ᵥ x) ↔ A.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hp
    refine ⟨hA, fun x => RCLike.nonneg_iff.mpr ⟨hp x, ?_⟩⟩
    exact RCLike.conj_eq_iff_im.mp (hA.star_dotProduct_mulVec_comm x x)
  · rintro ⟨_, hp⟩ x
    exact (RCLike.nonneg_iff.mp (hp x)).1

theorem principal_restrictions_nonnegative :
    Specs.D05.M11.PrincipalMinors.Semidefinite.principal_restrictions_nonnegative := by
  intro n A hA hp s
  let e := (Fintype.equivFin s).symm
  let C := (A.submatrix (Subtype.val : s → Fin n) Subtype.val).submatrix e e
  have hps := (positiveSemidefinite_iff_posSemidef A hA).mp hp
  have hC : C.PosSemidef := (hps.submatrix Subtype.val).submatrix e
  have hd := complex_determinant_nonnegative C hC.isHermitian (fun x =>
    (RCLike.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg x)).1)
  simpa only [C, det_submatrix_equiv_self] using hd

theorem real_principal_restrictions_nonnegative {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hp : ∀ x, 0 ≤ x ⬝ᵥ A *ᵥ x) : AllPrincipalNonnegative A := by
  intro s
  let e := (Fintype.equivFin s).symm
  let C := (A.submatrix (Subtype.val : s → Fin k) Subtype.val).submatrix e e
  have hH : A.IsHermitian := by simpa using hA
  have hp' : Specs.D05.M11.Definiteness.positiveSemidefinite_value
      (fun x y => star y ⬝ᵥ A *ᵥ x) := by simpa [Specs.D05.M11.Definiteness.positiveSemidefinite_value] using hp
  have hps := (positiveSemidefinite_iff_posSemidef A hH).mp hp'
  have hC : C.PosSemidef := (hps.submatrix Subtype.val).submatrix e
  have hd := real_determinant_nonnegative C hC.isHermitian.isSymm (fun x => by
    simpa using hC.dotProduct_mulVec_nonneg x)
  simpa only [C, det_submatrix_equiv_self, RCLike.re_to_real] using hd

theorem criterion : Specs.D05.M11.PrincipalMinors.Semidefinite.criterion := by
  intro n A hA
  exact ⟨principal_restrictions_nonnegative A hA, fun h =>
    limit_nonnegative A (shifted_positive_definite A hA h)⟩

theorem real_criterion : Specs.D05.M11.PrincipalMinors.Semidefinite.real_criterion := by
  intro n A hA
  constructor
  · exact real_principal_restrictions_nonnegative A hA
  · intro hp
    have hH : A.IsHermitian := by simpa using hA
    have h := limit_nonnegative A (shifted_positive_definite A hH hp)
    simpa [Specs.D05.M11.Definiteness.positiveSemidefinite_value] using h

theorem empty_minor : Specs.D05.M11.PrincipalMinors.Semidefinite.empty_minor := by
  intro R n _ A
  exact det_isEmpty

theorem leading_minors_insufficient :
    Specs.D05.M11.PrincipalMinors.Semidefinite.leading_minors_insufficient := by
  dsimp only [Specs.D05.M11.PrincipalMinors.Semidefinite.leading_minors_insufficient]
  have hval : (![0, 1] : Fin 2 → ℝ) ⬝ᵥ (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)
      *ᵥ ![0, 1] = -1 := by norm_num [dotProduct, mulVec, Fin.sum_univ_two]
  refine ⟨?_, hval, ?_⟩
  · intro k hk
    interval_cases k <;>
      norm_num [Specs.D05.M11.PrincipalMinors.Leading.leadingBlock,
        det_fin_one, det_fin_two]
  · intro hp
    have h := hp ![0, 1]
    change 0 ≤ (![0, 1] : Fin 2 → ℝ) ⬝ᵥ (!![0, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)
      *ᵥ ![0, 1] at h
    rw [hval] at h
    norm_num at h

theorem transpose_criterion : Specs.D05.M11.PrincipalMinors.Semidefinite.transpose_criterion := by
  intro K _ n H
  unfold AllPrincipalNonnegative
  simp only [← transpose_submatrix, det_transpose]

theorem form_criterion : Specs.D05.M11.PrincipalMinors.Semidefinite.form_criterion := by
  intro V _ _ n e B hB
  let H := Specs.D05.M11.Hermitian.formMatrix_value e B
  have hH : H.IsHermitian := (D05.M11.Hermitian.hermitian_iff_matrix e B).mp hB
  have hq (v : V) : B v v = star (e.equivFun v) ⬝ᵥ Hᵀ *ᵥ e.equivFun v :=
    D05.M11.Hermitian.quadratic_matrix_expression e B v
  have hb : Specs.D05.M11.Definiteness.positiveSemidefinite_value (fun x y => B x y) ↔
      Specs.D05.M11.Definiteness.positiveSemidefinite_value (fun x y => star y ⬝ᵥ Hᵀ *ᵥ x) := by
    constructor
    · intro h x
      have hh := h (e.equivFun.symm x)
      change 0 ≤ RCLike.re (B _ _) at hh
      rw [hq] at hh
      simpa only [LinearEquiv.apply_symm_apply] using hh
    · intro h v
      change 0 ≤ RCLike.re (B v v)
      rw [hq]
      exact h _
  exact hb.trans ((criterion Hᵀ hH.transpose).trans (transpose_criterion H))

end D05.M11.PrincipalMinors.Semidefinite
