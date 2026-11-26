import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.HermitianRadicalComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Flat.Basic

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.Arithmetic.HermitianRadicalComparison

open LinearAlgebraicGroups.Specs
open Specs.Arithmetic.HermitianRadicalComparison
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics
open private unitEquiv unitEquiv_unitPoint unitPoint_inv opposite_point
  centralizes_onAlgebras centralizes_hasLimit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private cocharacter_parabolic contracting_le_unipotentGenerated
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {F E ι : Type u} [Field F] [Field E] [Algebra F E] [Fintype ι] [DecidableEq ι]
  {G : AffineAlgebraicGroup F} {σ : E ≃ₐ[F] E} {H : Matrix ι ι E}
  {R S : TestAlgebra F} {e f : ι}

private def matrixHom (M : Model G σ H) (R : TestAlgebra F) :
    GroupPoints G.val R →* Matrix.SpecialLinearGroup ι (Coeff E R) :=
  MonoidHom.mk' (fun x => (M.point R x).val) (M.mul R)

private theorem matrix_injective (M : Model G σ H) :
    Function.Injective (M.matrix (R := R)) := by
  intro x y h
  exact (M.point R).injective (Subtype.ext (Subtype.ext h))

private theorem matrix_one (M : Model G σ H) :
    M.matrix (1 : GroupPoints G.val R) = 1 :=
  congrArg Subtype.val ((matrixHom M R).map_one)

private theorem matrix_mul (M : Model G σ H) (x y : GroupPoints G.val R) :
    M.matrix (x * y) = M.matrix x * M.matrix y :=
  congrArg Subtype.val (M.mul R x y)

private theorem matrix_preimage (M : Model G σ H) (x : Matrix ι ι (Coeff E R))
    (hd : x.det = 1) (hp : Preserves σ H x) :
    ∃ g : GroupPoints G.val R, M.matrix g = x := by
  let y : {x : Matrix.SpecialLinearGroup ι (Coeff E R) // Preserves σ H x.val} :=
    ⟨⟨x, hd⟩, hp⟩
  exact ⟨(M.point R).symm y, congrArg (fun v => v.val.val) ((M.point R).apply_symm_apply y)⟩

private theorem matrix_det (M : Model G σ H) (x : GroupPoints G.val R) :
    (M.matrix x).det = 1 := (M.point R x).val.property

private theorem matrix_preserves (M : Model G σ H) (x : GroupPoints G.val R) :
    Preserves σ H (M.matrix x) := (M.point R x).property

private theorem conjugation_algebraMap (r : R) :
    conjugation σ R (algebraMap R (Coeff E R) r) = algebraMap R (Coeff E R) r := by
  change conjugation σ R (r ⊗ₜ (1 : E)) = r ⊗ₜ (1 : E)
  simp [conjugation]

omit [Fintype ι] in
private theorem weight_swap (h : e ≠ f) (i : ι) :
    weight f e i = -weight e f i := by
  by_cases he : i = e
  · subst i
    simp [weight, h]
  · by_cases hf : i = f
    · subst i
      simp [weight, h.symm]
    · simp [weight, he, hf]

omit [Fintype ι] in
private theorem weight_negative_iff (h : e ≠ f) (i j : ι) :
    weight e f i < weight e f j ↔ (j = e ∧ i ≠ e) ∨ (i = f ∧ j ≠ f) := by
  by_cases hi : i = e <;> by_cases hi' : i = f <;>
    by_cases hj : j = e <;> by_cases hj' : j = f <;>
    simp_all [weight]

omit [Fintype ι] in
private theorem gram_row_e (h : HyperbolicPair H e f) (j : ι) :
    gram H R e j = if j = f then 1 else 0 := by
  change (Algebra.TensorProduct.includeRight (R := F) (A := R)) (H e j) = _
  rw [h.row_e]
  split <;> simp [Algebra.TensorProduct.one_def]

omit [Fintype ι] in
private theorem gram_col_e (h : HyperbolicPair H e f) (i : ι) :
    gram H R i e = if i = f then 1 else 0 := by
  change (Algebra.TensorProduct.includeRight (R := F) (A := R)) (H i e) = _
  rw [h.col_e]
  split <;> simp [Algebra.TensorProduct.one_def]

omit [Fintype ι] in
private theorem swap_pair (h : HyperbolicPair H e f) : HyperbolicPair H f e :=
  ⟨h.distinct.symm, h.row_f, h.row_e, h.col_f, h.col_e⟩

private theorem diagonal_det (h : e ≠ f) (t : Rˣ) :
    (diagonal (E := E) e f t).det = 1 := by
  rw [diagonal, Matrix.det_diagonal]
  simp only [← map_prod]
  change (algebraMap R (Coeff E R)) (∏ i : ι, Units.coeHom R (t ^ weight e f i)) = 1
  rw [← map_prod]
  have hp : (∏ i : ι, t ^ weight e f i) = 1 := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
    have he : weight e f e = 1 := by simp [weight]
    rw [he, zpow_one]
    have hp' : (∏ i ∈ (Finset.univ : Finset ι).erase e, t ^ weight e f i) = t⁻¹ := by
      calc
        _ = t ^ weight e f f := Finset.prod_eq_single_of_mem f (by simp [h.symm])
          (fun i hi hif => by simp [weight, (Finset.mem_erase.mp hi).1, hif])
        _ = _ := by simp [weight, h.symm]
    rw [hp']
    exact mul_inv_cancel _
  rw [hp]
  change (algebraMap R (Coeff E R)) 1 = 1
  exact map_one (algebraMap R (Coeff E R))

private theorem diagonal_preserves (h : HyperbolicPair H e f) (t : Rˣ) :
    Preserves σ H (diagonal e f t) := by
  unfold Preserves diagonal
  rw [Matrix.diagonal_map (map_zero (conjugation σ R)), Matrix.diagonal_transpose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, conjugation_algebraMap]
  by_cases hi : i = e
  · subst i
    rw [gram_row_e h]
    by_cases hj : j = f
    · subst j
      simp [weight, h.distinct.symm, Algebra.TensorProduct.one_def]
    · simp [hj]
  · by_cases hi' : i = f
    · subst i
      rw [gram_row_e (swap_pair h)]
      by_cases hj : j = e
      · subst j
        simp [weight, h.distinct.symm, Algebra.TensorProduct.one_def]
      · simp [hj]
    · by_cases hj : j = e
      · subst j
        rw [gram_col_e h]
        simp [hi']
      · by_cases hj' : j = f
        · subst j
          rw [gram_col_e (swap_pair h)]
          simp [hi]
        · simp [weight, hi, hi', hj, hj']
          rw [← Algebra.TensorProduct.one_def, one_mul, mul_one]

private theorem diagonal_mul (t s : Rˣ) :
    diagonal (E := E) e f (t * s) = diagonal e f t * diagonal e f s := by
  simp [diagonal, Matrix.diagonal_mul_diagonal, mul_zpow]

omit [Fintype ι] in
private theorem diagonal_map (a : R ⟶ S) (t : Rˣ) :
    (diagonal (E := E) e f t).map (changeCoefficients a) =
      diagonal e f (Units.map a.hom.toMonoidHom t) := by
  rw [diagonal, Matrix.diagonal_map (map_zero (changeCoefficients (E := E) a)), diagonal]
  congr 1
  funext i
  rw [← map_zpow]
  change changeCoefficients a (((t ^ weight e f i).val) ⊗ₜ (1 : E)) =
    (a.hom (t ^ weight e f i).val) ⊗ₜ (1 : E)
  simp [changeCoefficients]

private def unitLift (M : Model G σ H) (h : HyperbolicPair H e f) (R : TestAlgebra F) :
    Rˣ →* GroupPoints G.val R :=
  MonoidHom.mk' (fun t => (M.point R).symm
    ⟨⟨diagonal e f t, diagonal_det h.distinct t⟩, diagonal_preserves h t⟩) (by
      intro t s
      apply matrix_injective M
      rw [matrix_mul]
      simp only [Model.matrix, Equiv.apply_symm_apply]
      exact diagonal_mul t s)

private theorem unitLift_matrix (M : Model G σ H) (h : HyperbolicPair H e f) (t : Rˣ) :
    M.matrix (unitLift M h R t) = diagonal e f t := by
  change ((M.point R) ((M.point R).symm _)).val.val = _
  rw [Equiv.apply_symm_apply]

private theorem unitLift_natural (M : Model G σ H) (h : HyperbolicPair H e f)
    (a : R ⟶ S) (t : Rˣ) :
    (mapPoints a (unitLift M h R t) : GroupPoints G.val S) =
       unitLift M h S (Units.map a.hom.toMonoidHom t) := by
  apply matrix_injective M
  rw [show M.matrix (mapPoints a (unitLift M h R t)) =
    (M.matrix (unitLift M h R t)).map (changeCoefficients a) from M.natural a _,
    unitLift_matrix, unitLift_matrix, diagonal_map]

private theorem exists_cocharacter (M : Model G σ H) (h : HyperbolicPair H e f) :
    ∃ c : Cocharacter G.val, ∀ (R : TestAlgebra F) (t : Rˣ),
      M.matrix (cocharacterPoint c R t) = diagonal e f t := by
  let T := specGroup (DiagonalizableGroups.groupAlgebra F DiagonalizableGroups.IntegerCharacters)
  let n : (groupPointsFunctor F).obj T ⟶ (groupPointsFunctor F).obj G.val :=
    { app := fun R => show GrpCat.of (GroupPoints T R) ⟶ GrpCat.of (GroupPoints G.val R) from
        GrpCat.ofHom ((unitLift M h R).comp (unitEquiv R).toMonoidHom)
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        obtain ⟨t, rfl⟩ : ∃ t : Rˣ, unitPoint R t = x :=
          ⟨unitEquiv R x, (unitEquiv R).injective (unitEquiv_unitPoint R _)⟩
        change unitLift M h S (unitEquiv S (mapPoints a (unitPoint R t))) =
          mapPoints a (unitLift M h R (unitEquiv R (unitPoint R t)))
        rw [mapPoints_unitPoint, unitEquiv_unitPoint, unitEquiv_unitPoint, unitLift_natural] }
  let eqv := LinearAlgebraicGroups.groupHomEquiv T G.val (by
    change IsAffine (Spec _)
    infer_instance)
  refine ⟨eqv.symm n, fun R t => ?_⟩
  have hn : ((groupPointsFunctor F).map (eqv.symm n)).app R = n.app R :=
    CategoryTheory.congr_app (eqv.apply_symm_apply n) R
  change M.matrix ((((groupPointsFunctor F).map (eqv.symm n)).app R) (unitPoint R t)) = _
  rw [hn]
  change M.matrix (unitLift M h R (unitEquiv R (unitPoint R t))) = _
  rw [unitEquiv_unitPoint, unitLift_matrix]

private theorem regular_iff_stabilizes (h : HyperbolicPair H e f)
    (M : Model G σ H) (g : GroupPoints G.val R) :
    Regular e f (M.matrix g) ↔ StabilizesLine e (M.matrix g) := by
  let x := M.matrix g
  constructor
  · intro hr i hi
    exact hr i e ((weight_negative_iff h.distinct i e).2 (Or.inl ⟨rfl, hi⟩))
  · intro hl
    have ha (j : ι) : ((x.map (conjugation σ R)).transpose * gram H R) e j =
        conjugation σ R (x e e) * gram H R e j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single e]
      · rfl
      · intro b _ hb
        change conjugation σ R (x b e) * gram H R b j = 0
        have hz : x b e = 0 := hl b hb
        rw [hz, map_zero, zero_mul]
      · simp
    have hb (j : ι) : conjugation σ R (x e e) * x f j = if j = f then 1 else 0 := by
      have hp := congrFun (congrFun (matrix_preserves M g) e) j
      change (((x.map (conjugation σ R)).transpose * gram H R) * x) e j = gram H R e j at hp
      rw [Matrix.mul_apply, Finset.sum_eq_single f, ha, gram_row_e h, ite_eq_left rfl, mul_one,
        gram_row_e h] at hp
      · exact hp
      · intro b _ hb
        rw [ha, gram_row_e h, ite_eq_right hb, mul_zero, zero_mul]
      · simp
    intro i j hij
    rcases (weight_negative_iff h.distinct i j).1 hij with ⟨hj, hi⟩ | ⟨hi, hj⟩
    · subst j
      exact hl i hi
    · subst i
      calc
        x f j = (conjugation σ R (x e e) * x f f) * x f j := by simp [hb]
        _ = x f f * (conjugation σ R (x e e) * x f j) := by ring
        _ = 0 := by simp [hb, hj]

private theorem change_tmul (a : R ⟶ S) (r : R) (z : E) :
    changeCoefficients a (r ⊗ₜ z) = a.hom r ⊗ₜ z := by simp [changeCoefficients]

private theorem change_conjugation (a : R ⟶ S) (x : Coeff E R) :
    changeCoefficients a (conjugation σ R x) =
      conjugation σ S (changeCoefficients a x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r z => simp [changeCoefficients, conjugation]
  | add x y hx hy => simp [hx, hy]

omit [Fintype ι] [DecidableEq ι] in
private theorem change_gram (a : R ⟶ S) : (gram H R).map (changeCoefficients a) = gram H S := by
  ext i j
  change changeCoefficients a ((1 : R) ⊗ₜ H i j) = (1 : S) ⊗ₜ H i j
  simp [change_tmul]

omit [DecidableEq ι] in
private theorem changePreserves_iff (a : R ⟶ S)
    (ha : Function.Injective (changeCoefficients (E := E) a))
    (x : Matrix ι ι (Coeff E R)) :
    Preserves σ H (x.map (changeCoefficients a)) ↔ Preserves σ H x := by
  have hm : (x.map (conjugation σ R)).map (changeCoefficients a) =
      (x.map (changeCoefficients a)).map (conjugation σ S) := by
    ext i j
    exact change_conjugation a (x i j)
  unfold Preserves
  rw [← hm, ← change_gram (H := H) a]
  change ((x.map (conjugation σ R)).transpose.map (changeCoefficients a)) *
    (gram H R).map (changeCoefficients a) * x.map (changeCoefficients a) = _ ↔ _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  constructor
  · intro h
    ext i j
    exact ha (congrFun (congrFun h i) j)
  · intro h
    rw [h]

private def laurentCoeffLinear (R : TestAlgebra F) (n : ℤ) : LaurentPolynomial R →ₗ[F] R :=
  ((Finsupp.lapply n : (ℤ →₀ R) →ₗ[R] R).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap).restrictScalars F

private def laurentCoeff (R : TestAlgebra F) (n : ℤ) :
    Coeff E (laurentAlgebra R) →ₗ[F] Coeff E R :=
  TensorProduct.map (laurentCoeffLinear R n) (LinearMap.id : E →ₗ[F] E)

private theorem laurentCoeff_tmul (n : ℤ) (p : LaurentPolynomial R) (a : E) :
    laurentCoeff (E := E) R n (p ⊗ₜ a) = (p.coeff n) ⊗ₜ a := rfl

private theorem change_polyToLaurent_injective :
    Function.Injective (changeCoefficients (E := E) (polynomialToLaurent R)) := by
  change Function.Injective (TensorProduct.map
    (polynomialToLaurent R).hom.toLinearMap (LinearMap.id : E →ₗ[F] E))
  exact TensorProduct.map_injective_of_flat_flat _ _ Polynomial.toLaurent_injective (fun _ _ h => h)

private theorem coeff_polynomial_negative (n : ℤ) (hn : n < 0)
    (p : Coeff E (polynomialAlgebra R)) :
    laurentCoeff R n (changeCoefficients (polynomialToLaurent R) p) = 0 := by
  induction p using TensorProduct.inductionOn with
  | tmul q a =>
    rw [change_tmul, laurentCoeff_tmul]
    change q.toLaurent.coeff n ⊗ₜ a = 0
    rw [coeff_toLaurent_neg q hn, TensorProduct.zero_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem coeff_polynomial_zero (p : Coeff E (polynomialAlgebra R)) :
    laurentCoeff R 0 (changeCoefficients (polynomialToLaurent R) p) =
      changeCoefficients (polynomialEvaluate R 0) p := by
  induction p using TensorProduct.inductionOn with
  | tmul q a =>
    rw [change_tmul, change_tmul, laurentCoeff_tmul]
    change q.toLaurent.coeff (0 : ℤ) ⊗ₜ a = q.eval 0 ⊗ₜ a
    rw [show (0 : ℤ) = (↑(0 : ℕ) : ℤ) by rfl, coeff_toLaurent_nat, Polynomial.coeff_zero_eq_eval_zero]
  | add x y hx hy => simp [hx, hy]

private def polynomialConstants (R : TestAlgebra F) : R ⟶ polynomialAlgebra R :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom F R (Polynomial R))

private def polynomialMonomial (n : ℕ) (x : Coeff E R) : Coeff E (polynomialAlgebra R) :=
  (algebraMap (Polynomial R) (Coeff E (polynomialAlgebra R))) (Polynomial.X ^ n) *
    changeCoefficients (polynomialConstants R) x

private def laurentMonomial (n : ℤ) (x : Coeff E R) : Coeff E (laurentAlgebra R) :=
  (algebraMap (LaurentPolynomial R) (Coeff E (laurentAlgebra R))) (LaurentPolynomial.T n) *
    changeCoefficients (laurentConstants R) x

private theorem coeff_laurentMonomial (n m : ℤ) (x : Coeff E R) :
    laurentCoeff R m (laurentMonomial n x) = if n = m then x else 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    unfold laurentMonomial
    rw [change_tmul]
    change laurentCoeff R m ((LaurentPolynomial.T n ⊗ₜ (1 : E)) *
      (LaurentPolynomial.C r ⊗ₜ a)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, laurentCoeff_tmul,
      mul_comm (LaurentPolynomial.T n) (LaurentPolynomial.C r),
      ← LaurentPolynomial.single_eq_C_mul_T]
    change (AddMonoidAlgebra.single n r).coeff m ⊗ₜ a = _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split <;> simp
  | add x y hx hy =>
    simp only [laurentMonomial, map_add, mul_add] at hx hy ⊢
    rw [hx, hy]
    split <;> simp_all

private theorem polynomialMonomial_map (n : ℕ) (x : Coeff E R) :
    changeCoefficients (polynomialToLaurent R) (polynomialMonomial n x) =
      laurentMonomial (n : ℤ) x := by
  unfold polynomialMonomial laurentMonomial
  rw [map_mul]
  congr 1
  · change changeCoefficients (polynomialToLaurent R) ((Polynomial.X ^ n : Polynomial R) ⊗ₜ (1 : E)) =
      LaurentPolynomial.T (n : ℤ) ⊗ₜ (1 : E)
    rw [change_tmul]
    change (Polynomial.toLaurent (Polynomial.X ^ n : Polynomial R)) ⊗ₜ (1 : E) = _
    rw [Polynomial.toLaurent_X_pow]
  · induction x using TensorProduct.inductionOn with
    | tmul r a =>
      rw [change_tmul, change_tmul, change_tmul]
      change (Polynomial.C r).toLaurent ⊗ₜ a = LaurentPolynomial.C r ⊗ₜ a
      rw [Polynomial.toLaurent_C]
    | add x y hx hy => simp [hx, hy]

private theorem parameter_zpow (R : TestAlgebra F) (n : ℤ) :
    ((laurentParameter R) ^ n).val = LaurentPolynomial.T n := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    change LaurentPolynomial.T 1 ^ n = _
    rw [LaurentPolynomial.T_pow, mul_one]
  | negSucc n =>
    rw [show Int.negSucc n = -(↑(n + 1) : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow,
      Units.val_pow_eq_pow_val]
    change LaurentPolynomial.T (-1) ^ (n + 1) = _
    rw [LaurentPolynomial.T_pow]
    norm_num

private theorem orbit_matrix (M : Model G σ H) (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t)
    (g : GroupPoints G.val R) (i j : ι) :
    M.matrix (orbit c g) i j =
      laurentMonomial (weight e f i - weight e f j) (M.matrix g i j) := by
  let t := laurentParameter R
  have hInv : (cocharacterPoint c (laurentAlgebra R) t)⁻¹ =
      cocharacterPoint c (laurentAlgebra R) t⁻¹ := by
    let a : GroupPoints _ (laurentAlgebra R) →* GroupPoints G.val (laurentAlgebra R) :=
      (((groupPointsFunctor F).map c).app (laurentAlgebra R)).hom
    change (a (unitPoint _ t))⁻¹ = a (unitPoint _ t⁻¹)
    rw [unitPoint_inv, map_inv]
  unfold orbit
  rw [matrix_mul, matrix_mul, hInv, hc, hc]
  unfold diagonal laurentMonomial
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change _ * (M.matrix ((mapPoints (laurentConstants R) g : GroupPoints G.val _)) i j) * _ = _
  rw [show M.matrix (mapPoints (laurentConstants R) g) =
    (M.matrix g).map (changeCoefficients (laurentConstants R)) from M.natural _ _]
  dsimp only [Matrix.map_apply, t]
  rw [inv_zpow, ← zpow_neg, parameter_zpow, parameter_zpow,
    mul_right_comm, ← map_mul, ← LaurentPolynomial.T_add, sub_eq_add_neg]

private theorem polynomial_extension (M : Model G σ H) (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t)
    (g : GroupPoints G.val R) (hr : Regular e f (M.matrix g)) :
    ∃ p : GroupPoints G.val (polynomialAlgebra R),
      mapPoints (polynomialToLaurent R) p = orbit c g ∧
        M.matrix (mapPoints (polynomialEvaluate R 0) p) = zeroWeight e f (M.matrix g) := by
  let q : Matrix ι ι (Coeff E (polynomialAlgebra R)) := fun i j =>
    if weight e f i < weight e f j then 0
    else polynomialMonomial (weight e f i - weight e f j).toNat (M.matrix g i j)
  have hq : q.map (changeCoefficients (polynomialToLaurent R)) = M.matrix (orbit c g) := by
    ext i j
    rw [orbit_matrix M c hc g i j]
    change changeCoefficients (polynomialToLaurent R) (q i j) = _
    by_cases hlt : weight e f i < weight e f j
    · simp [q, hlt, hr i j hlt, laurentMonomial]
    · rw [show q i j = polynomialMonomial (weight e f i - weight e f j).toNat
        (M.matrix g i j) by simp [q, hlt], polynomialMonomial_map, Int.toNat_of_nonneg]
      exact sub_nonneg.mpr (le_of_not_gt hlt)
  have hj := change_polyToLaurent_injective (E := E) (R := R)
  have hdet : q.det = 1 := by
    apply hj
    let j := changeCoefficients (E := E) (polynomialToLaurent R)
    change j.toRingHom q.det = j 1
    rw [RingHom.map_det]
    change (q.map j).det = j 1
    rw [hq, matrix_det, map_one]
  have hform : Preserves σ H q := by
    apply (changePreserves_iff (polynomialToLaurent R) hj q).1
    rw [hq]
    exact matrix_preserves M _
  obtain ⟨p, hp⟩ := matrix_preimage M q hdet hform
  refine ⟨p, matrix_injective M ?_, ?_⟩
  · rw [show M.matrix (mapPoints (polynomialToLaurent R) p) =
      (M.matrix p).map (changeCoefficients (polynomialToLaurent R)) from M.natural _ _, hp, hq]
  · rw [show M.matrix (mapPoints (polynomialEvaluate R 0) p) =
      (M.matrix p).map (changeCoefficients (polynomialEvaluate R 0)) from M.natural _ _, hp]
    ext i j
    change changeCoefficients (polynomialEvaluate R 0) (q i j) = _
    rw [← coeff_polynomial_zero]
    have h := congrFun (congrFun hq i) j
    change changeCoefficients (polynomialToLaurent R) (q i j) = _ at h
    rw [h, orbit_matrix M c hc g i j, coeff_laurentMonomial]
    simp [zeroWeight, sub_eq_zero]

private theorem matrix_limits (M : Model G σ H) (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t) :
    DescribesLimits M c e f := by
  intro R g z
  constructor
  · rintro ⟨p, hp, hz⟩
    have h (i j : ι) : changeCoefficients (polynomialToLaurent R) (M.matrix p i j) =
        laurentMonomial (weight e f i - weight e f j) (M.matrix g i j) := by
      rw [← orbit_matrix M c hc g i j, ← hp]
      exact (congrFun (congrFun (M.natural (polynomialToLaurent R) p) i) j).symm
    refine ⟨fun i j hij => ?_, ?_⟩
    · have hh := congrArg (laurentCoeff (E := E) R (weight e f i - weight e f j)) (h i j)
      rwa [coeff_polynomial_negative _ (sub_neg.mpr hij), coeff_laurentMonomial,
        ite_eq_left rfl, eq_comm] at hh
    · ext i j
      rw [← hz]
      rw [show M.matrix (mapPoints (polynomialEvaluate R 0) p) =
        (M.matrix p).map (changeCoefficients (polynomialEvaluate R 0)) from M.natural _ _]
      change changeCoefficients (polynomialEvaluate R 0) (M.matrix p i j) = _
      rw [← coeff_polynomial_zero, h, coeff_laurentMonomial]
      simp [zeroWeight, sub_eq_zero]
  · rintro ⟨hr, hz⟩
    obtain ⟨p, hp, hzero⟩ := polynomial_extension M c hc g hr
    exact ⟨p, hp, matrix_injective M (hzero.trans hz.symm)⟩

private theorem opposite_matrix (M : Model G σ H) (c : Cocharacter G.val) (hne : e ≠ f)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t)
    (R : TestAlgebra F) (t : Rˣ) :
    M.matrix (cocharacterPoint (oppositeCocharacter c) R t) = diagonal f e t := by
  rw [opposite_point, hc]
  unfold diagonal
  congr 1
  funext i
  rw [weight_swap hne, zpow_neg, inv_zpow]

private theorem transvection_preserves (h : HyperbolicPair H e f) (b : Coeff E R)
    (hb : conjugation σ R b + b = 0) :
    Preserves σ H (Matrix.transvection e f b) := by
  have hmap : ((Matrix.transvection e f b).map (conjugation σ R)).transpose =
      Matrix.transvection f e (conjugation σ R b) := by
    unfold Matrix.transvection
    rw [show (1 + Matrix.single e f b).map (conjugation σ R) =
        (1 : Matrix ι ι (Coeff E R)).map (conjugation σ R) +
          (Matrix.single e f b).map (conjugation σ R) by
      ext i j
      exact map_add (conjugation σ R) _ _]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single e f b (conjugation σ R),
      Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  unfold Preserves
  rw [hmap]
  let a := Matrix.transvection f e (conjugation σ R b) * gram H R
  change a * Matrix.transvection e f b = _
  have ha (i j : ι) : a i j =
      gram H R i j + (if i = f ∧ j = f then conjugation σ R b else 0) := by
    by_cases hi : i = f
    · subst i
      rw [show a f j = _ from Matrix.transvection_mul_apply_same f e j _ _,
        gram_row_e h]
      by_cases hj : j = f <;> simp [hj]
    · rw [show a i j = _ from Matrix.transvection_mul_apply_of_ne f e i j hi _ _]
      simp [hi]
  ext i j
  by_cases hj : j = f
  · subst j
    rw [Matrix.mul_transvection_apply_same, ha, ha, gram_col_e h]
    by_cases hi : i = f
    · simp [hi, h.distinct, add_assoc, hb]
    · simp [hi]
  · rw [Matrix.mul_transvection_apply_of_ne e f i j hj, ha]
    simp [hj]

private theorem cocharacter_noncentral (M : Model G σ H) (h : HyperbolicPair H e f)
    (hne : σ ≠ 1) (hsq : ∀ a, σ (σ a) = a)
    (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t) :
    ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes c g := by
  let R := CommAlgCat.of F F
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra! hh
    exact hne (AlgEquiv.ext hh)
  let b : Coeff E R := (1 : F) ⊗ₜ (a - σ a)
  have hb : b ≠ 0 := by
    let j : E →ₐ[F] Coeff E R := Algebra.TensorProduct.includeRight
    have hj : Function.Injective j :=
      Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
    exact fun he => sub_ne_zero.mpr ha.symm (hj (he.trans (map_zero j).symm))
  have hb' : conjugation σ R b + b = 0 := by
    change (conjugation σ R) ((1 : F) ⊗ₜ (a - σ a)) + (1 : F) ⊗ₜ (a - σ a) = 0
    simp [conjugation, map_sub, hsq, ← TensorProduct.tmul_add]
  obtain ⟨g, hg⟩ := matrix_preimage M (Matrix.transvection e f b)
    (Matrix.det_transvection_of_ne e f h.distinct b) (transvection_preserves h b hb')
  refine ⟨(testSpec F).obj (op R), g, fun hcentral => hb ?_⟩
  have hcomm := (centralizes_iff c g).1 hcentral
      ((testSpec F).obj (op (laurentAlgebra R))) ((testSpec F).map (laurentConstants R).op)
      (unitPoint (laurentAlgebra R) (laurentParameter R))
  have horbit : orbit c g = mapPoints (laurentConstants R) g := by
    unfold orbit
    let x : GroupPoints G.val (laurentAlgebra R) := mapPoints (laurentConstants R) g
    let t := cocharacterPoint c (laurentAlgebra R) (laurentParameter R)
    have hh : Commute x t := hcomm
    change t * x * t⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr hh.eq.symm
  have he : M.matrix g e f = b := by
    rw [hg, Matrix.transvection, Matrix.add_apply, Matrix.single_apply_same,
      Matrix.one_apply_ne h.distinct, zero_add]
  have hm : M.matrix (orbit c g) e f = laurentMonomial 2 b := by
    rw [orbit_matrix M c hc g e f, he]
    have hv : weight e f e - weight e f f = 2 := by simp [weight, h.distinct.symm]
    rw [hv]
  have hconst : M.matrix (orbit c g) e f = laurentMonomial 0 b := by
    rw [horbit]
    have hv := congrFun (congrFun (M.natural (laurentConstants R) g) e) f
    change M.matrix (mapPoints (laurentConstants R) g) e f =
      changeCoefficients (laurentConstants R) (M.matrix g e f) at hv
    rw [hv, he]
    simp [laurentMonomial, ← Algebra.TensorProduct.one_def]
  have hh := congrArg (laurentCoeff (E := E) R 2) (hm.symm.trans hconst)
  simpa [coeff_laurentMonomial] using hh

theorem matrixComparison : MatrixComparison.{u} := by
  intro F E ι _ _ _ _ _ _ _ σ hne hsq H hHerm e f h G M
  obtain ⟨c, hc⟩ := exists_cocharacter M h
  refine ⟨c, hc, cocharacter_noncentral M h hne hsq c hc, matrix_limits M c hc,
    matrix_limits M _ (opposite_matrix M c h.distinct hc), fun R g => ?_⟩
  exact ⟨regular_iff_stabilizes h M g, regular_iff_stabilizes (swap_pair h) M g⟩

private def testUnitIso (F : Type u) [Field F] :
    (testSpec F).obj (op (CommAlgCat.of F F)) ≅ 𝟙_ (SchemeOver F) := by
  refine Over.isoMk (Iso.refl (Spec (CommRingCat.of F))) ?_
  change 𝟙 _ ≫ 𝟙 _ = _
  rw [Category.id_comp]
  exact (Spec.map_id (CommRingCat.of F)).symm

private theorem rational_mem_of_limit {c : Cocharacter G.val} (D : LimitDecomposition c)
    (hG : GeometricRadicals.IsReductive G)
    (x : GroupPoints G.val (CommAlgCat.of F F)) (hx : HasLimit c x 1) :
    RationalMember G x := by
  obtain ⟨p, hp⟩ := (D.contracting_points _ x).1 hx
  let i := testUnitIso F
  have hi : i.hom = toUnit _ := toUnit_unique _ _
  let s : (𝟙_ (SchemeOver F)) ⟶ G.val.X := i.inv ≫ x
  refine ⟨s, contracting_le_unipotentGenerated hG D ?_, ?_⟩
  · refine ⟨i.inv ≫ p, ?_⟩
    change (i.inv ≫ p) ≫ D.contracting.inclusion.hom.hom = i.inv ≫ x
    rw [Category.assoc]
    exact congrArg (i.inv ≫ ·) hp
  · rw [← hi]
    exact i.hom_inv_id_assoc x

private theorem parabolic_points_of_matrix (M : Model G σ H) {c : Cocharacter G.val}
    (D : LimitDecomposition c)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t)
    (hs : ∀ (R : TestAlgebra F) (g : GroupPoints G.val R),
      Regular e f (M.matrix g) ↔ StabilizesLine e (M.matrix g)) :
    RepresentsOnAlgebras D.parabolic (fun _ g => StabilizesLine e (M.matrix g)) := by
  intro R g
  rw [← D.parabolic_points]
  change StabilizesLine e (M.matrix g) ↔ HasExtension c g
  rw [← hs]
  constructor
  · intro hg
    obtain ⟨p, hp, _⟩ := polynomial_extension M c hc g hg
    exact ⟨mapPoints (polynomialEvaluate R 0) p, p, hp, rfl⟩
  · rintro ⟨z, hz⟩
    exact ((matrix_limits M c hc R g z).1 hz).1

private theorem contracting_points_of_matrix (M : Model G σ H) {c : Cocharacter G.val}
    (D : LimitDecomposition c) (hd : DescribesLimits M c e f) :
    RepresentsOnAlgebras D.contracting (fun _ g => Unitriangular e f (M.matrix g)) := by
  intro R g
  rw [← D.contracting_points]
  change Unitriangular e f (M.matrix g) ↔ HasLimit c g 1
  rw [hd, matrix_one]
  exact and_congr_right (fun _ => eq_comm)

private theorem stabilizes_both_iff_block_diagonal
    (M : Model G σ H) (h : HyperbolicPair H e f) (g : GroupPoints G.val R) :
    StabilizesLine e (M.matrix g) ∧ StabilizesLine f (M.matrix g) ↔
      ∀ i j, weight e f i ≠ weight e f j → M.matrix g i j = 0 := by
  rw [← regular_iff_stabilizes h M g, ← regular_iff_stabilizes (swap_pair h) M g]
  constructor
  · rintro ⟨hp, hn⟩ i j hij
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact hp i j hh
    · apply hn i j
      simpa only [weight_swap h.distinct, neg_lt_neg_iff] using hh
  · intro hall
    refine ⟨fun i j hij => hall i j hij.ne, fun i j hij => hall i j ?_⟩
    rw [weight_swap h.distinct, weight_swap h.distinct, neg_lt_neg_iff] at hij
    exact hij.ne.symm

private theorem centralizer_points_of_matrix (M : Model G σ H) (h : HyperbolicPair H e f)
    {c : Cocharacter G.val} (D : LimitDecomposition c)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t) :
    RepresentsOnAlgebras D.centralizer
      (fun _ g => StabilizesLine e (M.matrix g) ∧ StabilizesLine f (M.matrix g)) := by
  intro R g
  refine ((stabilizes_both_iff_block_diagonal M h g).trans ?_).trans
    (D.centralizer_points _ g)
  constructor
  · intro hblock
    apply (centralizes_onAlgebras c g).2
    intro S a t
    let x : GroupPoints G.val S := mapPoints a g
    change Commute x (cocharacterPoint c S t)
    show x * cocharacterPoint c S t = cocharacterPoint c S t * x
    apply matrix_injective M
    rw [matrix_mul, matrix_mul, hc]
    ext i j
    unfold diagonal
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : weight e f i = weight e f j
    · rw [hij, mul_comm]
    · have hz : M.matrix x i j = 0 := by
        change M.matrix (mapPoints a g) i j = 0
        have hp := congrFun (congrFun (M.natural a g) i) j
        change M.matrix (mapPoints a g) i j = changeCoefficients a (M.matrix g i j) at hp
        rw [hp, hblock i j hij, map_zero]
      rw [hz, zero_mul, mul_zero]
  · intro hz i j hij
    have he := ((matrix_limits M c hc) R g g).1 (centralizes_hasLimit c hz)
    have hm := congrFun (congrFun he.2 i) j
    simpa [zeroWeight, hij] using hm

theorem radicalComparison : RadicalComparison.{u} := by
  intro F E ι _ _ _ _ _ _ _ σ hne hsq H hHerm e f h G hG M
  obtain ⟨c, hc, hn, hd, hd', hs⟩ := matrixComparison σ hne hsq H hHerm e f h G M
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition G c
  obtain ⟨D'⟩ := CocharacterDynamics.existsLimitDecomposition G (oppositeCocharacter c)
  let := hG.1
  have hc' := opposite_matrix M c h.distinct hc
  have hZ' := centralizer_points_of_matrix M (swap_pair h) D' hc'
  refine ⟨c, D, D', hc, hn, cocharacter_parabolic hG c D, cocharacter_parabolic hG _ D',
    CocharacterDynamics.bigCell G c D D',
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG c D,
    Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG _ D',
    parabolic_points_of_matrix M D hc (fun R g => (hs R g).1),
    parabolic_points_of_matrix M D' hc' (fun R g => (hs R g).2),
    centralizer_points_of_matrix M h D hc, fun R g => (and_comm.trans (hZ' R g)),
    contracting_points_of_matrix M D hd, contracting_points_of_matrix M D' hd', ?_⟩
  intro g hg
  rcases hg with hg | hg
  · exact rational_mem_of_limit D hG g ((hd _ g 1).2 ⟨hg.1, (matrix_one M).trans hg.2.symm⟩)
  · exact rational_mem_of_limit D' hG g ((hd' _ g 1).2 ⟨hg.1, (matrix_one M).trans hg.2.symm⟩)

end
end LinearAlgebraicGroups.Arithmetic.HermitianRadicalComparison
