import Specs.LinearAlgebraicGroups.Representation.NonsplitSymmetricPower
import LinearAlgebraicGroups.Affine.RelativeFrobenius
import LinearAlgebraicGroups.Representation.WeylDimension
import LinearAlgebraicGroups.Representation.SimpleClassification
import LinearAlgebraicGroups.Representation.IntegralFlagGeometry
import LinearAlgebraicGroups.Representation.PositiveKempfVanishing
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section

namespace LinearAlgebraicGroups.Representation.NonsplitSymmetricPower

open LinearAlgebraicGroups.Specs.NonsplitSymmetricPower
open MvPolynomial
open scoped BigOperators Matrix

universe u

variable {k R : Type u} [Field k] [CommRing R]

private theorem exponents_zero (n : ℕ) (i : Fin (n + 1)) :
    exponents n i 0 = n - (i : ℕ) := by simp [exponents]

private theorem exponents_one (n : ℕ) (i : Fin (n + 1)) :
    exponents n i 1 = (i : ℕ) := by simp [exponents]

private theorem exponents_injective (n : ℕ) : Function.Injective (exponents n) := by
  intro i j h
  apply Fin.ext
  simpa only [exponents_one] using congrArg (fun a : Fin 2 →₀ ℕ ↦ a 1) h

private theorem exponents_surjective {n : ℕ} {d : Fin 2 →₀ ℕ} (h : d.degree = n) :
    ∃ i, exponents n i = d := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
  let i : Fin (n + 1) := ⟨d 1, by omega⟩
  refine ⟨i, Finsupp.ext fun j ↦ ?_⟩
  fin_cases j
  · have hi : exponents n i 0 = n - d 1 := exponents_zero n i
    change exponents n i 0 = d 0
    omega
  · exact exponents_one n i

private theorem term_val {n : ℕ} (i : Fin (n + 1)) :
    (term R n i).val = X 0 ^ (n - (i : ℕ)) * X 1 ^ (i : ℕ) := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  change monomial (exponents n i) (1 : R) = _
  apply congrArg (fun d ↦ monomial d (1 : R))
  apply Finsupp.ext
  intro j
  fin_cases j
  · change exponents n i 0 = _
    simp [exponents_zero]
  · change exponents n i 1 = _
    simp [exponents_one]

private theorem coeff_term {n : ℕ} (i j : Fin (n + 1)) :
    (term R n i).val.coeff (exponents n j) = if i = j then 1 else 0 := by
  simp [term, coeff_monomial, (exponents_injective n).eq_iff]

private def coefficients (R : Type u) [CommRing R] (n : ℕ) :
    Forms R n →ₗ[R] (Fin (n + 1) → R) where
  toFun f i := f.val.coeff (exponents n i)
  map_add' f g := by ext i; simp
  map_smul' r f := by ext i; exact coeff_smul _ _ _

private theorem coefficients_injective (n : ℕ) :
    Function.Injective (coefficients R n) := by
  intro f g h
  apply Subtype.ext
  apply MvPolynomial.ext
  intro d
  by_cases hd : d.degree = n
  · obtain ⟨i, rfl⟩ := exponents_surjective hd
    exact congrFun h i
  · rw [f.property.coeff_eq_zero hd, g.property.coeff_eq_zero hd]

private theorem coefficients_sum {n : ℕ} (a : Fin (n + 1) → R) :
    coefficients R n (∑ i, a i • term R n i) = a := by
  ext j
  simp [coefficients, coeff_term, smul_eq_mul, mul_ite]

private def coefficientEquiv (R : Type u) [CommRing R] (n : ℕ) :
    Forms R n ≃ₗ[R] (Fin (n + 1) → R) :=
  LinearEquiv.ofBijective (coefficients R n)
    ⟨coefficients_injective n, fun a ↦ ⟨_, coefficients_sum a⟩⟩

private theorem sum_terms {n : ℕ} (f : Forms R n) :
    ∑ i : Fin (n + 1), f.val.coeff (exponents n i) • term R n i = f := by
  apply coefficients_injective n
  exact coefficients_sum (coefficients R n f)

private theorem pure_zero {n : ℕ} : (term R n 0).val = X 0 ^ n := by
  simpa only [Fin.val_zero, Nat.sub_zero, pow_zero, mul_one] using (term_val (R := R) (0 : Fin (n + 1)))

private theorem pure_last {n : ℕ} : (term R n (Fin.last n)).val = X 1 ^ n := by
  simpa only [Fin.val_last, Nat.sub_self, pow_zero, one_mul] using
    (term_val (R := R) (Fin.last n))

private theorem substitution_X (g : Matrix (Fin 2) (Fin 2) R) (j : Fin 2) :
    substitution g (X j) = C (g 0 j) * X 0 + C (g 1 j) * X 1 := by
  rw [substitution, aeval_X, Fin.sum_univ_two]

/-- The polynomial substitution is the map of the symmetric algebra induced by the
natural linear action on the two generators. -/
theorem substitution_symmetricAlgebra {R : Type u} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) :
    let b := Pi.basisFun R (Fin 2)
    let e := SymmetricAlgebra.equivMvPolynomial b
    (substitution g).comp e.toAlgHom =
      e.toAlgHom.comp (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R (Fin 2 → R)).comp g.mulVecLin)) := by
  intro b e
  apply SymmetricAlgebra.algHom_ext
  apply b.ext
  intro j
  change substitution g (e (SymmetricAlgebra.ι R (Fin 2 → R) (b j))) =
    e ((SymmetricAlgebra.lift ((SymmetricAlgebra.ι R (Fin 2 → R)).comp g.mulVecLin))
      (SymmetricAlgebra.ι R (Fin 2 → R) (b j)))
  rw [show e (SymmetricAlgebra.ι R (Fin 2 → R) (b j)) = X j from
    SymmetricAlgebra.equivMvPolynomial_ι_apply b j,
    substitution_X, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
  have h : g.mulVecLin (b j) = ∑ i, g i j • b i := by
    change g.mulVec ((Pi.basisFun R (Fin 2)) j) = _
    rw [Pi.basisFun_apply, Matrix.mulVec_single_one]
    simpa only [b, Pi.basisFun_repr, Matrix.col_apply] using (b.sum_repr (g.col j)).symm
  have hterm (i : Fin 2) :
      e (SymmetricAlgebra.ι R (Fin 2 → R) (g i j • b i)) = C (g i j) * X i := by
    rw [map_smul, map_smul]
    rw [show e (SymmetricAlgebra.ι R (Fin 2 → R) (b i)) = X i from
      SymmetricAlgebra.equivMvPolynomial_ι_apply b i, MvPolynomial.smul_eq_C_mul]
  rw [h, map_sum, map_sum]
  simp only [hterm, Fin.sum_univ_two]


private theorem substitution_one :
    substitution (1 : Matrix (Fin 2) (Fin 2) R) = AlgHom.id R _ := by
  ext j
  fin_cases j <;> simp [substitution_X]

private theorem substitution_mul (g h : Matrix (Fin 2) (Fin 2) R) :
    substitution (g * h) = (substitution g).comp (substitution h) := by
  have hC (r : R) : substitution g (C r) = C r := aeval_C _ r
  ext j
  simp only [AlgHom.comp_apply, substitution_X, map_add, map_mul, hC,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem substitution_map {S : Type u} [CommRing S] (f : R →+* S)
    (g : Matrix (Fin 2) (Fin 2) R) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (substitution g P) =
      substitution (g.map f) (MvPolynomial.map f P) := by
  have h : (MvPolynomial.map f).comp (substitution g).toRingHom =
      (substitution (g.map f)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [substitution]
    · intro j
      simp [substitution_X]
  exact DFunLike.congr_fun h P

private def generic (k : Type u) [Field k] : Matrix (Fin 2) (Fin 2)
    (MvPolynomial (Fin 2 × Fin 2) k) :=
  fun i j ↦ X (i, j)

private def entries (k : Type u) [Field k] (n : ℕ) (i j : Fin (n + 1)) :
    MvPolynomial (Fin 2 × Fin 2) k :=
  (act (generic k) (term _ n j)).val.coeff (exponents n i)

private theorem coeff_homogeneous_of_C_mul_X_pow {d : ℕ} {F : MvPolynomial (Fin 2 × Fin 2) k}
    (hF : F.IsHomogeneous d) (i : Fin 2) (s : Fin 2 →₀ ℕ) (a : ℕ) :
    ((C F * (X i) ^ a : MvPolynomial (Fin 2) _).coeff s).IsHomogeneous d := by
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  split
  · exact hF
  · exact isHomogeneous_zero _ _ _

private theorem entries_homogeneous (n : ℕ) (i j : Fin (n + 1)) :
    (entries k n i j).IsHomogeneous n := by
  let P := MvPolynomial (Fin 2) (MvPolynomial (Fin 2 × Fin 2) k)
  have hadd {m : ℕ} {a b : P}
      (ha : ∀ d, (a.coeff d).IsHomogeneous m) (hb : ∀ d, (b.coeff d).IsHomogeneous m) :
      ∀ d, ((a + b).coeff d).IsHomogeneous m := by
    intro d
    change (a.coeff d + b.coeff d).IsHomogeneous m
    exact (ha d).add (hb d)
  have hmul {m q : ℕ} {a b : P}
      (ha : ∀ d, (a.coeff d).IsHomogeneous m) (hb : ∀ d, (b.coeff d).IsHomogeneous q) :
      ∀ d, ((a * b).coeff d).IsHomogeneous (m + q) := by
    intro d
    classical
    rw [MvPolynomial.coeff_mul]
    apply IsHomogeneous.sum
    intro e _
    exact (ha e.1).mul (hb e.2)
  have hpow {m : ℕ} {a : P} (ha : ∀ d, (a.coeff d).IsHomogeneous m) (r : ℕ) :
      ∀ d, ((a ^ r).coeff d).IsHomogeneous (r * m) := by
    induction r with
    | zero =>
      intro d
      rw [pow_zero, zero_mul, coeff_one]
      split
      · exact isHomogeneous_one _ _
      · exact isHomogeneous_zero _ _ _
    | succ r ih =>
      simpa only [pow_succ, Nat.succ_mul] using hmul ih ha
  have hgen (j : Fin 2) :
      ∀ d, ((substitution (generic k) (X j)).coeff d).IsHomogeneous 1 := by
    rw [substitution_X]
    exact hadd
      (fun d ↦ by simpa only [pow_one, generic] using
        coeff_homogeneous_of_C_mul_X_pow (isHomogeneous_X _ (0, j)) 0 d 1)
      (fun d ↦ by simpa only [pow_one, generic] using
        coeff_homogeneous_of_C_mul_X_pow (isHomogeneous_X _ (1, j)) 1 d 1)
  change ((substitution (generic k) (term _ n j).val).coeff (exponents n i)).IsHomogeneous n
  rw [term_val, map_mul, map_pow, map_pow]
  simpa only [mul_one, Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)] using
    hmul (hpow (hgen 0) (n - (j : ℕ))) (hpow (hgen 1) (j : ℕ)) (exponents n i)

theorem polynomialAction : PolynomialAction.{u} := by
  intro k _ n
  refine ⟨?_, entries k n, entries_homogeneous n, ?_⟩
  · intro R _
    constructor
    · ext f : 1
      apply Subtype.ext
      exact DFunLike.congr_fun (substitution_one (R := R)) f.val
    · intro g h
      ext f : 1
      apply Subtype.ext
      exact DFunLike.congr_fun (substitution_mul g h) f.val
  · intro R _ _ g i j
    let f : MvPolynomial (Fin 2 × Fin 2) k →ₐ[k] R := aeval (fun a ↦ g a.1 a.2)
    have hg : (generic k).map f.toRingHom = g := by ext a b; exact aeval_X _ _
    have ht : MvPolynomial.map f.toRingHom (term _ n j).val = (term R n j).val := by
      simp [term, map_monomial]
    have h := substitution_map f.toRingHom (generic k) (term _ n j).val
    rw [hg, ht] at h
    exact (congrArg (fun P : MvPolynomial (Fin 2) R ↦ P.coeff (exponents n i)) h).symm.trans
      (coeff_map _ _ _)

private theorem act_pure (p : ℕ) [Fact p.Prime] [CharP R p]
    (g : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) :
    act g (purePowerMap R p v) = purePowerMap R p ((frobeniusMatrix p g).mulVec v) := by
  apply Subtype.ext
  change substitution g (v 0 • (term R p 0).val + v 1 • (term R p (Fin.last p)).val) =
    ((frobeniusMatrix p g).mulVec v) 0 • (term R p 0).val +
    ((frobeniusMatrix p g).mulVec v) 1 • (term R p (Fin.last p)).val
  simp only [pure_zero, pure_last, Algebra.smul_def, map_add, map_mul, map_pow,
    MvPolynomial.algebraMap_eq, substitution_X, add_pow_char, mul_pow,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, frobeniusMatrix]
  simp only [substitution, aeval_C, MvPolynomial.algebraMap_eq, ← map_pow]
  ring

private theorem end_indices_ne {p : ℕ} (hp : 0 < p) : (0 : Fin (p + 1)) ≠ Fin.last p := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

private theorem pure_coeff (p : ℕ) (v : Fin 2 → R) (i : Fin (p + 1)) :
    (purePowerMap R p v).val.coeff (exponents p i) =
      (if 0 = i then v 0 else 0) + (if Fin.last p = i then v 1 else 0) := by
  change (v 0 • (term R p 0).val + v 1 • (term R p (Fin.last p)).val).coeff _ = _
  simp [coeff_term, smul_eq_mul, mul_ite]

private theorem purePower_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (purePowerMap R p) := by
  intro v w h
  ext i
  fin_cases i
  · simpa [pure_coeff, (end_indices_ne hp).symm] using
      congrArg (fun f : Forms R p ↦ f.val.coeff (exponents p 0)) h
  · simpa [pure_coeff, end_indices_ne hp] using
      congrArg (fun f : Forms R p ↦ f.val.coeff (exponents p (Fin.last p))) h

private theorem purePower_range (p : ℕ) : (purePowerMap k p).range = purePowers k p := by
  apply le_antisymm
  · rintro f ⟨v, rfl⟩
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    rintro f (rfl | rfl)
    · exact ⟨![1, 0], by simp [purePowerMap]⟩
    · exact ⟨![0, 1], by simp [purePowerMap]⟩

theorem frobeniusSubmodule : FrobeniusSubmodule.{u} := by
  intro k _ p hp _
  refine ⟨purePower_injective hp.out.pos, purePower_range _, ?_⟩
  intro R _ _ g v
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subtype.ext (Subsingleton.elim _ _)
  · let _ : CharP R p := charP_of_injective_algebraMap (algebraMap k R).injective p
    exact act_pure p g v

private theorem coeff_contract [Algebra k R] {n : ℕ} (ℓ : R →ₗ[k] k)
    (f : Forms R n) (i : Fin (n + 1)) :
    (contract ℓ f).val.coeff (exponents n i) = ℓ (f.val.coeff (exponents n i)) :=
  congrFun (coefficients_sum (fun j ↦ ℓ (f.val.coeff (exponents n j)))) i

private theorem extend_pure [Algebra k R] (p : ℕ) (v : Fin 2 → k) :
    extend (purePowerMap k p v) = purePowerMap R p (algebraMap k R ∘ v) := by
  apply coefficients_injective p
  ext i
  change (MvPolynomial.map (algebraMap k R) (purePowerMap k p v).val).coeff _ =
     (purePowerMap R p (algebraMap k R ∘ v)).val.coeff _
  rw [coeff_map, pure_coeff, pure_coeff]
  split <;> split <;> simp_all

private theorem contract_pure [Algebra k R] (p : ℕ) (ℓ : R →ₗ[k] k) (v : Fin 2 → R) :
    contract ℓ (purePowerMap R p v) = purePowerMap k p (ℓ ∘ v) := by
  apply coefficients_injective p
  ext i
  change (contract ℓ _).val.coeff (exponents p i) = (purePowerMap k p _).val.coeff _
  rw [coeff_contract, pure_coeff, pure_coeff]
  split <;> split <;> simp_all

private theorem pure_stable {p : ℕ} [Fact p.Prime] [CharP k p] (special : Bool) :
    Stable (purePowers k p) special := by
  intro R _ _ g _ ℓ f hf
  rw [← purePower_range] at hf ⊢
  obtain ⟨v, rfl⟩ := hf
  have he := (frobeniusSubmodule k p).2.2 R g (algebraMap k R ∘ v)
  rw [extend_pure, he, contract_pure]
  exact ⟨_, rfl⟩

private def laurentCoeff (k : Type u) [Field k] (s : ℤ) : LaurentPolynomial k →ₗ[k] k :=
  (Finsupp.lapply s).comp (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

private def weight {n : ℕ} (i : Fin (n + 1)) : ℤ := (n : ℤ) - 2 * (i : ℤ)

private theorem weight_injective (n : ℕ) : Function.Injective (weight (n := n)) := by
  intro i j h
  apply Fin.ext
  dsimp [weight] at h
  omega

private def torus (k : Type u) [Field k] : Matrix (Fin 2) (Fin 2) (LaurentPolynomial k) :=
  !![LaurentPolynomial.T 1, 0; 0, LaurentPolynomial.T (-1)]

private theorem torus_det : (torus k).det = 1 := by
  rw [Matrix.det_fin_two]
  change (LaurentPolynomial.T 1 : LaurentPolynomial k) * LaurentPolynomial.T (-1) -
    0 * 0 = 1
  rw [mul_zero, sub_zero, ← LaurentPolynomial.T_add]
  exact LaurentPolynomial.T_zero (R := k)

private theorem torus_term {n : ℕ} (i : Fin (n + 1)) :
    act (torus k) (term (LaurentPolynomial k) n i) =
      LaurentPolynomial.T (R := k) (weight i) • term (LaurentPolynomial k) n i := by
  apply Subtype.ext
  change substitution (torus k) (term (LaurentPolynomial k) n i).val =
    LaurentPolynomial.T (R := k) (weight i) • (term (LaurentPolynomial k) n i).val
  rw [term_val, map_mul, map_pow, map_pow, substitution_X, substitution_X]
  change ((C (LaurentPolynomial.T 1 : LaurentPolynomial k) * X 0 + C 0 * X 1) ^
    (n - (i : ℕ))) * ((C 0 * X 0 + C (LaurentPolynomial.T (-1)) * X 1) ^ (i : ℕ)) =
    LaurentPolynomial.T (R := k) (weight i) • (X 0 ^ (n - (i : ℕ)) * X 1 ^ (i : ℕ))
  simp only [map_zero, zero_mul, zero_add, add_zero, mul_pow, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, ← map_pow, LaurentPolynomial.T_pow]
  have hw : ((n - (i : ℕ) : ℕ) : ℤ) * 1 + (i : ℤ) * (-1) = weight i := by
    have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
    rw [Nat.cast_sub hi]
    dsimp [weight]
    ring
  rw [← hw, LaurentPolynomial.T_add, map_mul]
  ring

private theorem coeff_extend [Algebra k R] {n : ℕ} (f : Forms k n) (i : Fin (n + 1)) :
    (extend (R := R) f).val.coeff (exponents n i) =
      algebraMap k R (f.val.coeff (exponents n i)) :=
  coeff_map _ _ _

private theorem torus_projection {n : ℕ} (f : Forms k n) (i : Fin (n + 1)) :
    contract (laurentCoeff k (weight i)) (act (torus k) (extend f)) =
      f.val.coeff (exponents n i) • term k n i := by
  have h (j : Fin (n + 1)) :
      (act (torus k) (extend f)).val.coeff (exponents n j) =
        algebraMap k (LaurentPolynomial k) (f.val.coeff (exponents n j)) *
          LaurentPolynomial.T (weight j) := by
    conv_lhs => rw [← sum_terms (extend (R := LaurentPolynomial k) f)]
    change coefficients _ n (act _ _) j = _
    rw [map_sum, map_sum, Finset.sum_apply]
    simp [map_smul, torus_term, coefficients, coeff_term, coeff_extend, mul_ite]
  apply coefficients_injective n
  ext j
  change (contract _ _).val.coeff (exponents n j) = _
  rw [coeff_contract, h]
  change _ = (f.val.coeff (exponents n i) • (term k n i).val).coeff (exponents n j)
  rw [coeff_smul, coeff_term]
  change (LaurentPolynomial.C _ * LaurentPolynomial.T (weight j)).coeff (weight i) = _
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rw [AddMonoidAlgebra.coeff_single]
  by_cases hij : i = j
  · subst j
    simp
  · have hw : weight j ≠ weight i := fun h ↦ hij ((weight_injective n h).symm)
    simp [hij, Ne.symm hw]

private theorem contains_term {n : ℕ} {M : Submodule k (Forms k n)}
    (hM : Stable M true) {f : Forms k n} (hf : f ∈ M)
    (i : Fin (n + 1)) (hi : f.val.coeff (exponents n i) ≠ 0) : term k n i ∈ M := by
  have hh := hM (LaurentPolynomial k) (torus k) torus_det (laurentCoeff k (weight i)) f hf
  rw [torus_projection] at hh
  simpa [smul_smul, hi] using M.smul_mem (f.val.coeff (exponents n i))⁻¹ hh

private theorem extend_self {n : ℕ} (f : Forms k n) : extend (R := k) f = f := by
  apply coefficients_injective n
  ext i
  exact coeff_extend f i

private theorem contract_self {n : ℕ} (f : Forms k n) :
    contract (LinearMap.id : k →ₗ[k] k) f = f := sum_terms f

private theorem stable_at_k {n : ℕ} {M : Submodule k (Forms k n)}
    (hM : Stable M true) (g : Matrix (Fin 2) (Fin 2) k) (hg : g.det = 1)
    (f : Forms k n) (hf : f ∈ M) : act g f ∈ M := by
  simpa only [extend_self, contract_self] using hM k g hg LinearMap.id f hf

private def upper (k : Type u) [Field k] : Matrix (Fin 2) (Fin 2) k :=
  !![1, 1; 0, 1]

private def swap (k : Type u) [Field k] : Matrix (Fin 2) (Fin 2) k :=
  !![0, -1; 1, 0]

private theorem eval_term {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial.eval (![1, 0] : Fin 2 → k) (term k n i).val = if i = 0 then 1 else 0 := by
  by_cases h : i = 0
  · subst i
    simp [pure_zero]
  · have hi : (i : ℕ) ≠ 0 := fun h' ↦ h (Fin.ext h')
    simp [term_val, h, zero_pow hi]

private theorem eval_coeff_zero {n : ℕ} (f : Forms k n) :
    MvPolynomial.eval (![1, 0] : Fin 2 → k) f.val = f.val.coeff (exponents n 0) := by
  conv_lhs => rw [← sum_terms f]
  change ((MvPolynomial.eval (![1, 0] : Fin 2 → k)).toAddMonoidHom
    ((homogeneousSubmodule _ k n).subtype (∑ i, f.val.coeff (exponents n i) • term k n i))) = _
  simp [eval_term, map_smul, Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_ite]

private theorem upper_coeff_zero {n : ℕ} (i : Fin (n + 1)) :
    (act (upper k) (term k n i)).val.coeff (exponents n 0) = 1 := by
  rw [← eval_coeff_zero]
  change MvPolynomial.eval (![1, 0] : Fin 2 → k)
    (substitution (upper k) (term k n i).val) = 1
  simp [term_val, substitution_X, upper]

private theorem swap_pure {n : ℕ} :
    act (swap k) (term k n 0) = term k n (Fin.last n) := by
  apply Subtype.ext
  change substitution (swap k) (term k n 0).val = (term k n (Fin.last n)).val
  simp [pure_zero, pure_last, substitution_X, swap]

private theorem pure_le_of_stable {n : ℕ} {M : Submodule k (Forms k n)}
    (hM : Stable M true) (h : M ≠ ⊥) : purePowers k n ≤ M := by
  obtain ⟨f, hf, hfn⟩ := (Submodule.ne_bot_iff M).mp h
  have ⟨i, hi⟩ : ∃ i, f.val.coeff (exponents n i) ≠ 0 := by
    by_contra! he
    apply hfn
    apply coefficients_injective n
    ext i
    exact he i
  have hi' := contains_term hM hf i hi
  have hh := stable_at_k hM (upper k) (by simp [upper, Matrix.det_fin_two]) _ hi'
  have hx := contains_term hM hh 0 (by rw [upper_coeff_zero]; exact one_ne_zero)
  have hy := stable_at_k hM (swap k) (by simp [swap, Matrix.det_fin_two]) _ hx
  rw [swap_pure] at hy
  apply Submodule.span_le.mpr
  rintro f (rfl | rfl)
  · exact hx
  · exact hy

theorem nonsplit : Nonsplit.{u} := by
  intro k _ p hp _
  dsimp only
  let e : (Fin 2 → k) ≃ₗ[k] purePowers k p :=
    (LinearEquiv.ofInjective _ (purePower_injective hp.out.pos)).trans
      (LinearEquiv.ofEq _ _ (purePower_range p))
  have hs : Module.finrank k (purePowers k p) = 2 := by
    rw [← e.finrank_eq]
    simp
  have hf : Module.finrank k (Forms k p) = p + 1 := by
    rw [(coefficientEquiv k p).finrank_eq]
    simp
  have hn : purePowers k p ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hs
    contradiction
  have hproper : purePowers k p ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hf] at hs
    have := hp.out.two_le
    omega
  refine ⟨pure_stable true, pure_stable false, hn, hs, hf, fun M ↦ pure_le_of_stable, ?_⟩
  intro special h
  obtain ⟨M, hM, hc⟩ := h
  have hM' : Stable M true := by
    intro R _ _ g hg ℓ v hv
    apply hM R g _ ℓ v hv
    cases special <;> simp_all
  have hMn : M ≠ ⊥ := by
    rintro rfl
    exact hproper (by simpa using hc.sup_eq_top)
  have he := pure_le_of_stable hM' hMn
  exact hn (le_antisymm (le_trans (le_inf le_rfl he) hc.disjoint.le_bot) bot_le)

section Induction

open CategoryTheory
open scoped MatrixGroups

private theorem secondColumn_surj : Function.Surjective (secondColumn (R := R)) := by
  intro v
  obtain ⟨g, h0, h1⟩ := v.property.exists_SL2_col 1
  exact ⟨g, Subtype.ext (by funext i; fin_cases i <;> assumption)⟩

private theorem secondColumn_map {S : Type u} [CommRing S] (a : R →+* S) (g : SL(2, R)) :
    secondColumn (Matrix.SpecialLinearGroup.map a g) = (secondColumn g).map a := rfl

private theorem secondColumn_mul (g h : SL(2, R)) :
    (secondColumn (g * h)).val = g.val.mulVec (secondColumn h).val := rfl

private theorem diagonalUnit (b : SL(2, R)) (hb : b 0 1 = 0) : IsUnit (b 1 1) := by
  have h := b.det_coe
  rw [Matrix.det_fin_two] at h
  change b 0 0 * b 1 1 - b 0 1 * b 1 0 = 1 at h
  rw [hb, zero_mul, sub_zero] at h
  exact ⟨⟨b 1 1, b 0 0, by rw [mul_comm, h], h⟩, rfl⟩

private theorem secondColumn_lower (g b : SL(2, R)) (hb : b 0 1 = 0) :
    secondColumn (g * b) = (secondColumn g).scale (diagonalUnit b hb).unit := by
  apply Subtype.ext
  rw [secondColumn_mul]
  funext i
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change g i 0 * b 0 1 + g i 1 * b 1 1 = ↑(diagonalUnit b hb).unit * g i 1
  rw [hb, mul_zero, zero_add, IsUnit.unit_spec, mul_comm]

private theorem lower_of_scale (g h : SL(2, R)) (u : Rˣ)
    (H : secondColumn h = (secondColumn g).scale u) :
    (g⁻¹ * h) 0 1 = 0 ∧ (g⁻¹ * h) 1 1 = ↑u := by
  have hCol := congrArg Subtype.val H
  change (secondColumn h).val = (u : R) • (secondColumn g).val at hCol
  have he : (secondColumn (g⁻¹ * h)).val = (u : R) • (secondColumn (1 : SL(2, R))).val := by
    rw [secondColumn_mul, hCol, Matrix.mulVec_smul, ← secondColumn_mul, inv_mul_cancel]
  exact ⟨by simpa [secondColumn] using congrFun he 0,
    by simpa [secondColumn] using congrFun he 1⟩

private def pullbackSections (k : Type u) [Field k] (n : ℕ) :
    projectiveSections k n →ₗ[k] matrixInduction k n where
  toFun f := ⟨fun R g ↦ f.val R (secondColumn g), by
    refine ⟨fun a g ↦ ?_, fun R g b hb ↦ ?_⟩
    · change _ = f.val _ (secondColumn _)
      rw [f.property.1, secondColumn_map]
    · change f.val R (secondColumn (g * b)) = b 1 1 ^ n * f.val R (secondColumn g)
      rw [secondColumn_lower g b hb, f.property.2, IsUnit.unit_spec]⟩
  map_add' f g := rfl
  map_smul' c f := rfl

private theorem pullback_bijective (n : ℕ) : Function.Bijective (pullbackSections k n) := by
  constructor
  · intro f h e
    apply Subtype.ext
    funext R v
    obtain ⟨g, rfl⟩ := secondColumn_surj v
    exact congrFun (congrFun (congrArg Subtype.val e) R) g
  · intro f
    classical
    let lift (R : TestAlgebra k) (v : Column R) := (secondColumn_surj v).choose
    have hlift (R : TestAlgebra k) (v : Column R) : secondColumn (lift R v) = v :=
      (secondColumn_surj v).choose_spec
    have hscale (R : TestAlgebra k) (g h : SL(2, R)) (u : Rˣ)
        (H : secondColumn h = (secondColumn g).scale u) :
        f.val R h = (u : R)^n * f.val R g := by
      obtain ⟨h0, h1⟩ := lower_of_scale g h u H
      simpa only [mul_inv_cancel_left, h1] using f.property.2 R g (g⁻¹ * h) h0
    have hsame (R : TestAlgebra k) (g h : SL(2, R))
        (H : secondColumn h = secondColumn g) : f.val R h = f.val R g := by
      have hs : (secondColumn g).scale (1 : Rˣ) = secondColumn g := by
        apply Subtype.ext
        funext i
        exact one_mul _
      simpa using hscale R g h 1 (H.trans hs.symm)
    refine ⟨⟨fun R v ↦ f.val R (lift R v), ?_⟩, ?_⟩
    · constructor
      · intro R S a v
        rw [f.property.1]
        apply hsame
        rw [hlift, secondColumn_map, hlift]
      · intro R u v
        apply hscale
        rw [hlift, hlift]
    · apply Subtype.ext
      funext R g
      change f.val R (lift R (secondColumn g)) = f.val R g
      exact hsame R g _ (hlift _ _)

private def xChart (t : R) : Column R :=
  ⟨![1, t], ⟨1, 0, by simp⟩⟩

private def yChart (t : R) : Column R :=
  ⟨![t, 1], ⟨0, 1, by simp⟩⟩

private theorem xChart_map {S : Type u} [CommRing S] (a : R →+* S) (t : R) :
    (xChart t).map a = xChart (a t) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [Column.map, xChart]

private theorem yChart_map {S : Type u} [CommRing S] (a : R →+* S) (t : R) :
    (yChart t).map a = yChart (a t) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [Column.map, yChart]

private theorem eval_homogeneous {n : ℕ} [Algebra k R] (f : Forms k n)
    (a : R) (v : Fin 2 → R) :
    aeval (a • v) f.val = a ^ n * aeval v f.val := by
  have hmono (i : Fin (n + 1)) :
      aeval (a • v) (term k n i).val = a ^ n * aeval v (term k n i).val := by
    rw [term_val]
    simp only [map_mul, map_pow, aeval_X, Pi.smul_apply, smul_eq_mul, mul_pow]
    have hsum : n - (i : ℕ) + (i : ℕ) = n := Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)
    calc
      _ = (a ^ (n - (i : ℕ)) * a ^ (i : ℕ)) *
          (v 0 ^ (n - (i : ℕ)) * v 1 ^ (i : ℕ)) := by ring
      _ = _ := by rw [← pow_add, hsum]
  rw [← sum_terms f]
  simp only [Submodule.coe_sum, map_sum, SetLike.val_smul, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, map_mul, aeval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ * aeval (a • v) (term k n i).val = _
  rw [hmono]
  ring

private def evalSections (k : Type u) [Field k] (n : ℕ) :
    Forms k n →ₗ[k] projectiveSections k n where
  toFun f := ⟨fun R v ↦ aeval v.val f.val, by
    constructor
    · intro R S a v
      exact comp_aeval_apply v.val a.hom f.val
    · intro R u v
      exact eval_homogeneous f (u : R) v.val⟩
  map_add' f g := by
    apply Subtype.ext
    funext R v
    exact map_add (aeval v.val) f.val g.val
  map_smul' a f := by
    apply Subtype.ext
    funext R v
    change (aeval (R := k) v.val).toLinearMap (a • f.val) = a • _
    exact map_smul (aeval v.val).toLinearMap a f.val

private def polynomialTest (k : Type u) [Field k] : TestAlgebra k :=
  CommAlgCat.of k (Polynomial k)

private def laurentTest (k : Type u) [Field k] : TestAlgebra k :=
  CommAlgCat.of k (LaurentPolynomial k)

private def xPolynomial {n : ℕ} (s : projectiveSections k n) : Polynomial k :=
  s.val (polynomialTest k) (xChart Polynomial.X)

private def yPolynomial {n : ℕ} (s : projectiveSections k n) : Polynomial k :=
  s.val (polynomialTest k) (yChart Polynomial.X)

private theorem section_xChart {n : ℕ} (s : projectiveSections k n) {R : TestAlgebra k} (t : R) :
    s.val R (xChart t) = Polynomial.aeval t (xPolynomial s) := by
  have h := s.property.1 (CommAlgCat.ofHom (Polynomial.aeval t)) (xChart Polynomial.X)
  change Polynomial.aeval t (xPolynomial s) = s.val R ((xChart _).map _) at h
  rw [xChart_map] at h
  change _ = s.val R (xChart (Polynomial.aeval t Polynomial.X)) at h
  rwa [Polynomial.aeval_X, eq_comm] at h

private theorem section_yChart {n : ℕ} (s : projectiveSections k n) {R : TestAlgebra k} (t : R) :
    s.val R (yChart t) = Polynomial.aeval t (yPolynomial s) := by
  have h := s.property.1 (CommAlgCat.ofHom (Polynomial.aeval t)) (yChart Polynomial.X)
  change Polynomial.aeval t (yPolynomial s) = s.val R ((yChart _).map _) at h
  rw [yChart_map] at h
  change _ = s.val R (yChart (Polynomial.aeval t Polynomial.X)) at h
  rwa [Polynomial.aeval_X, eq_comm] at h

private def laurentUnit (k : Type u) [Field k] : (LaurentPolynomial k)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; exact LaurentPolynomial.T_zero
  inv_val := by rw [← LaurentPolynomial.T_add]; exact LaurentPolynomial.T_zero

private theorem section_overlap {n : ℕ} (s : projectiveSections k n) :
    (yPolynomial s).toLaurent =
      LaurentPolynomial.T (n : ℤ) * LaurentPolynomial.invert ((xPolynomial s).toLaurent) := by
  let T := laurentTest k
  let u : Tˣ := laurentUnit k
  have hu : (xChart (↑u⁻¹ : T)).scale u = yChart (u : T) := by
    apply Subtype.ext
    funext i
    change (u : T) * _ = _
    fin_cases i
    · exact mul_one _
    · exact Units.mul_inv u
  have h := s.property.2 T u (xChart (↑u⁻¹ : T))
  rw [hu, section_yChart, section_xChart] at h
  have hpos : Polynomial.aeval (LaurentPolynomial.T (R := k) 1) = Polynomial.toLaurentAlg := by
    ext
    rw [Polynomial.aeval_X, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X]
  have hneg : Polynomial.aeval (LaurentPolynomial.T (R := k) (-1)) =
      LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg := by
    ext
    rw [Polynomial.aeval_X, AlgHom.comp_apply, Polynomial.toLaurentAlg_apply,
      Polynomial.toLaurent_X, AlgEquiv.toAlgHom_apply, LaurentPolynomial.invert_T]
  change (Polynomial.aeval (LaurentPolynomial.T (R := k) 1)) (yPolynomial s) =
    LaurentPolynomial.T (R := k) 1 ^ n *
      (Polynomial.aeval (LaurentPolynomial.T (R := k) (-1))) (xPolynomial s) at h
  rw [hpos, hneg] at h
  change _ = (LaurentPolynomial.T 1 : LaurentPolynomial k) ^ n * _ at h
  simpa only [Polynomial.toLaurentAlg_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    LaurentPolynomial.T_pow, mul_one] using h

private theorem coeff_T_mul (f : LaurentPolynomial k) (a b : ℤ) :
    (LaurentPolynomial.T a * f).coeff b = f.coeff (b - a) := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    rw [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg]
    rfl
  | C_mul_T d c =>
    rw [mul_comm (LaurentPolynomial.T a), LaurentPolynomial.mul_T_assoc,
      ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single]
    have h : b = d + a ↔ b - a = d := by omega
    simp only [Finsupp.single_apply, eq_comm (a := d + a), eq_comm (a := d), h]

private theorem toLaurent_coeff_nat (f : Polynomial k) (i : ℕ) :
    f.toLaurent.coeff (i : ℤ) = f.coeff i := by
  rw [LaurentPolynomial.coeff_toLaurent]
  change (Finsupp.mapDomain (Nat.castEmbedding : ℕ ↪ ℤ) f.toFinsupp.coeff)
    ((Nat.castEmbedding : ℕ ↪ ℤ) i) = f.coeff i
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ i

private theorem toLaurent_coeff_neg (f : Polynomial k) (i : ℤ) (hi : i < 0) :
    f.toLaurent.coeff i = 0 := by
  by_contra h
  have hm : i ∈ f.toLaurent.coeff.support := Finsupp.mem_support_iff.mpr h
  rw [LaurentPolynomial.support_coeff_toLaurent] at hm
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
  change (j : ℤ) = i at hj
  omega

private theorem xPolynomial_degree {n : ℕ} (s : projectiveSections k n) :
    (xPolynomial s).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  let d : ℤ := (n : ℤ) - (i : ℤ)
  have h := toLaurent_coeff_neg (yPolynomial s) d (by dsimp [d]; omega)
  rw [section_overlap, coeff_T_mul, LaurentPolynomial.invert_apply] at h
  have hd : -(d - n) = (i : ℤ) := by dsimp [d]; omega
  rwa [hd, toLaurent_coeff_nat] at h

private theorem localization_equal {a b x y : R} (h : IsCoprime a b)
    (ha : algebraMap R (Localization.Away a) x = algebraMap R (Localization.Away a) y)
    (hb : algebraMap R (Localization.Away b) x = algebraMap R (Localization.Away b) y) :
    x = y := by
  have hx (c : R) (hc : algebraMap R (Localization.Away c) x =
      algebraMap R (Localization.Away c) y) : ∃ r : ℕ, c ^ r * (x - y) = 0 := by
    have hz : algebraMap R (Localization.Away c) (x - y) = 0 := by rw [map_sub, hc, sub_self]
    obtain ⟨⟨z, hz⟩, h⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers c)
      (Localization.Away c) _).mp hz
    obtain ⟨r, rfl⟩ := hz
    exact ⟨r, h⟩
  obtain ⟨r, hr⟩ := hx a ha
  obtain ⟨s, hs⟩ := hx b hb
  obtain ⟨u, v, huv⟩ := h.pow (m := r) (n := s)
  have he := congrArg (· * (x - y)) huv
  rw [add_mul, mul_assoc, mul_assoc, hr, hs, mul_zero, mul_zero, zero_add, one_mul] at he
  exact sub_eq_zero.mp he.symm

private theorem section_ext {n : ℕ} {s t : projectiveSections k n}
    (hx : xPolynomial s = xPolynomial t) : s = t := by
  have hy : yPolynomial s = yPolynomial t := by
    apply Polynomial.toLaurent_injective
    rw [section_overlap, section_overlap, hx]
  have compare_x (R : TestAlgebra k) (c : Column R) (hc : IsUnit (c.val 0)) :
      s.val R c = t.val R c := by
    let u := hc.unit
    have he : (xChart ((↑u⁻¹ : R) * c.val 1)).scale u = c := by
      apply Subtype.ext
      funext i
      fin_cases i
      · change (u : R) * 1 = c.val 0
        rw [mul_one, IsUnit.unit_spec]
      · change (u : R) * (↑u⁻¹ * c.val 1) = c.val 1
        rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [← he, s.property.2, t.property.2, section_xChart, section_xChart, hx]
  have compare_y (R : TestAlgebra k) (c : Column R) (hc : IsUnit (c.val 1)) :
      s.val R c = t.val R c := by
    let u := hc.unit
    have he : (yChart ((↑u⁻¹ : R) * c.val 0)).scale u = c := by
      apply Subtype.ext
      funext i
      fin_cases i
      · change (u : R) * (↑u⁻¹ * c.val 0) = c.val 0
        rw [← mul_assoc, Units.mul_inv, one_mul]
      · change (u : R) * 1 = c.val 1
        rw [mul_one, IsUnit.unit_spec]
    rw [← he, s.property.2, t.property.2, section_yChart, section_yChart, hy]
  apply Subtype.ext
  funext R v
  apply localization_equal v.property
  · let S : TestAlgebra k := CommAlgCat.of k (Localization.Away (v.val 0))
    let a : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away (v.val 0)))
    change a.hom (s.val R v) = a.hom (t.val R v)
    rw [s.property.1, t.property.1]
    apply compare_x
    exact IsLocalization.Away.algebraMap_isUnit (v.val 0)
  · let S : TestAlgebra k := CommAlgCat.of k (Localization.Away (v.val 1))
    let a : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away (v.val 1)))
    change a.hom (s.val R v) = a.hom (t.val R v)
    rw [s.property.1, t.property.1]
    apply compare_y
    exact IsLocalization.Away.algebraMap_isUnit (v.val 1)

private theorem xPolynomial_eval {n : ℕ} (f : Forms k n) :
    xPolynomial (evalSections k n f) =
      ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (f.val.coeff (exponents n i)) := by
  change aeval (![1, Polynomial.X] : Fin 2 → Polynomial k) f.val = _
  conv_lhs => rw [← sum_terms f]
  simp only [Submodule.coe_sum, map_sum, SetLike.val_smul, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, map_mul, aeval_C, term_val, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul, map_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact Polynomial.C_mul_X_pow_eq_monomial

private theorem xPolynomial_eval_coeff {n : ℕ} (f : Forms k n) (i : Fin (n + 1)) :
    (xPolynomial (evalSections k n f)).coeff (i : ℕ) = f.val.coeff (exponents n i) := by
  rw [xPolynomial_eval, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Fin.val_inj]
  simp

private theorem evalSections_bijective (n : ℕ) : Function.Bijective (evalSections k n) := by
  constructor
  · intro f g h
    apply coefficients_injective n
    ext i
    change f.val.coeff (exponents n i) = g.val.coeff (exponents n i)
    rw [← xPolynomial_eval_coeff, ← xPolynomial_eval_coeff, h]
  · intro s
    let a := xPolynomial s
    let f : Forms k n := ∑ i : Fin (n + 1), a.coeff (i : ℕ) • term k n i
    refine ⟨f, section_ext ?_⟩
    have ha : ∀ i : Fin (n + 1), f.val.coeff (exponents n i) = a.coeff (i : ℕ) :=
      fun i ↦ congrFun (coefficients_sum _) i
    rw [xPolynomial_eval]
    simp only [ha]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ Polynomial.monomial i (a.coeff i))]
    exact (Polynomial.as_sum_range' a (n + 1) (Nat.lt_succ_of_le (xPolynomial_degree s))).symm

private theorem eval_substitution [Algebra k R] (g : Matrix (Fin 2) (Fin 2) R)
    (v : Fin 2 → R) (f : MvPolynomial (Fin 2) k) :
    aeval v (substitution g (MvPolynomial.map (algebraMap k R) f)) =
      aeval (fun j ↦ g 0 j * v 0 + g 1 j * v 1) f := by
  have h : (aeval v).toRingHom.comp ((substitution g).toRingHom.comp (MvPolynomial.map (algebraMap k R))) =
      (aeval (R := k) (fun j ↦ g 0 j * v 0 + g 1 j * v 1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [substitution]
    · intro j
      simp [substitution_X]
  exact DFunLike.congr_fun h f

private theorem determinantCoordinates_action (g : SL(2, R)) (v : Fin 2 → R) :
    (fun j ↦ g 0 j * determinantCoordinates v 0 + g 1 j * determinantCoordinates v 1) =
      determinantCoordinates ((g⁻¹ : SL(2, R)).val.mulVec v) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  funext j
  fin_cases j <;> simp [determinantCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]

private def determinantChange (k : Type u) [Field k] (n : ℕ) : Forms k n ≃ₗ[k] Forms k n :=
  let g : SL(2, k) := ⟨swap k, by simp [swap, Matrix.det_fin_two]⟩
  let h := (polynomialAction k n).1 k
  LinearEquiv.ofLinearMap (act g.val) (act (g⁻¹ : SL(2, k)).val)
    (by rw [← h.2, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, h.1])
    (by rw [← h.2, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, h.1])

private theorem eval_determinantChange {n : ℕ} {R : TestAlgebra k} (v : Column R) (f : Forms k n) :
    aeval v.val (determinantChange k n f).val = aeval (determinantCoordinates v.val) f.val := by
  change aeval v.val (substitution (swap k) f.val) = _
  rw [substitution, comp_aeval_apply]
  have he : (fun j ↦ aeval v.val (∑ i, C (swap k i j) * X i)) =
      determinantCoordinates v.val := by
    funext j
    fin_cases j <;> simp [swap, Fin.sum_univ_two, determinantCoordinates]
  rw [he]

theorem inductionIdentification : InductionIdentification.{u} := by
  intro k _ n
  let E := (determinantChange k n).trans (LinearEquiv.ofBijective _ (evalSections_bijective n))
  let F := LinearEquiv.ofBijective _ (pullback_bijective (k := k) n)
  refine ⟨E, F, fun f R v ↦ eval_determinantChange v f, fun f R g ↦ rfl, ?_⟩
  intro R g h f
  change aeval (determinantCoordinates (secondColumn h).val)
    (substitution g.val (MvPolynomial.map (algebraMap k R) f.val)) =
    aeval (secondColumn (g⁻¹ * h)).val (determinantChange k n f).val
  rw [eval_substitution, determinantCoordinates_action, ← secondColumn_mul, eval_determinantChange]

end Induction


section RelativeFrobenius

open AlgebraicGeometry CategoryTheory Opposite Coalgebra WithConv
open Algebra.TensorProduct
open scoped TensorProduct
open Specs.StandardGroups (SLCoordinates GLCoordinates determinantOneIdeal)
open Specs.RelativeFrobenius (extendAlong scalarTensor)
open private slEvaluation slEvaluation_entry quotient_det glCoordinates_ext from
  LinearAlgebraicGroups.Affine.StandardGroups
open private liftSemilinear liftSemilinear_apply extAlong counit_tmul comul_tmul
  comulTensorMap comulTensorMap_tmul extensionInclusion
  from LinearAlgebraicGroups.Affine.RelativeFrobenius

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private def entry (k : Type u) [Field k] (i j : ι) : SLCoordinates k ι :=
  Ideal.Quotient.mkₐ k (determinantOneIdeal k ι) (StandardGroups.universalMatrix k ι i j)

private def universalSL (k : Type u) [Field k] : Matrix.SpecialLinearGroup ι (SLCoordinates k ι) :=
  ⟨entry k, by
    change ((Ideal.Quotient.mkₐ k (determinantOneIdeal k ι)).mapMatrix
      (StandardGroups.universalMatrix k ι)).det = 1
    rw [← AlgHom.map_det, quotient_det]⟩

private theorem slAlgHom_ext [Algebra k R] {f g : SLCoordinates k ι →ₐ[k] R}
    (h : ∀ i j, f (entry k i j) = g (entry k i j)) : f = g := by
  apply Ideal.Quotient.algHom_ext k
  exact glCoordinates_ext h

private theorem slRingHom_ext {f g : SLCoordinates k ι →+* R}
    (hc : ∀ c : k, f (algebraMap k (SLCoordinates k ι) c) =
      g (algebraMap k (SLCoordinates k ι) c))
    (he : ∀ i j, f (entry k i j) = g (entry k i j)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (Specs.StandardGroups.genericDeterminant k ι))
  apply MvPolynomial.ringHom_ext
  · exact hc
  · rintro ⟨i, j⟩
    exact he i j

private abbrev slHopf (h : Specs.StandardGroups.HopfOperations k (SLCoordinates k ι)) :=
  letI := h.hopf
  CommHopfAlgCat.of k (SLCoordinates k ι)

variable (h : Specs.StandardGroups.HopfOperations k (SLCoordinates k ι))

private abbrev slTwist (σ : k →+* k) := extendAlong σ (slHopf h)

private def toTwist (σ : k →+* k) : slHopf h →ₐ[k] slTwist h σ :=
  slEvaluation (Matrix.SpecialLinearGroup.map (extensionInclusion σ (slHopf h)) (universalSL k))

private theorem toTwist_entry (σ : k →+* k) (i j : ι) :
    toTwist h σ (entry k i j) = scalarTensor σ (slHopf h) 1 (entry k i j) :=
  slEvaluation_entry (Matrix.SpecialLinearGroup.map (extensionInclusion σ (slHopf h)) (universalSL k)) i j

private def evaluateOver (φ : k →+* R) (g : Matrix.SpecialLinearGroup ι R) :
    SLCoordinates k ι →+* R :=
  letI := φ.toAlgebra
  (slEvaluation g).toRingHom

private theorem evaluateOver_entry (φ : k →+* R) (g : Matrix.SpecialLinearGroup ι R) (i j : ι) :
    evaluateOver φ g (entry k i j) = g i j :=
  letI := φ.toAlgebra
  slEvaluation_entry g i j

private theorem evaluateOver_coeff (φ : k →+* R) (g : Matrix.SpecialLinearGroup ι R) (c : k) :
    evaluateOver φ g (algebraMap k (SLCoordinates k ι) c) = φ c :=
  letI := φ.toAlgebra
  (slEvaluation g).commutes c

private def fromTwist (σ : k →+* k) : slTwist h σ →ₐ[k] slHopf h :=
  let φ := (algebraMap k (SLCoordinates k ι)).comp σ
  liftSemilinear σ _ _ (evaluateOver φ (universalSL k)) (evaluateOver_coeff φ (universalSL k))

private theorem fromTwist_entry (σ : k →+* k) (i j : ι) :
    fromTwist h σ (scalarTensor σ (slHopf h) 1 (entry k i j)) = entry k i j := by
  rw [fromTwist, liftSemilinear_apply, one_smul, evaluateOver_entry]
  rfl

private theorem extensionInclusion_coeff {K : Type u} [Field K]
    (σ : k →+* K) (A : HopfAlgebraCategory k) (c : k) :
    extensionInclusion σ A (algebraMap k A c) = algebraMap K (extendAlong σ A) (σ c) := by
  let := σ.toAlgebra
  change (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) (algebraMap k A c) =
    (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[k] A) (σ c)
  exact Algebra.TensorProduct.includeRight.commutes c

private theorem slTwist_ext (σ : k →+* k) {R : Type u} [CommRing R] [Algebra k R]
    {f g : slTwist h σ →ₐ[k] R}
    (he : ∀ i j, f (scalarTensor σ (slHopf h) 1 (entry k i j)) =
      g (scalarTensor σ (slHopf h) 1 (entry k i j))) : f = g := by
  apply extAlong σ (slHopf h)
  have e : f.toRingHom.comp (extensionInclusion σ (slHopf h)) =
      g.toRingHom.comp (extensionInclusion σ (slHopf h)) := by
    apply slRingHom_ext
    · intro c
      change f (extensionInclusion σ (slHopf h) (algebraMap k (slHopf h) c)) =
        g (extensionInclusion σ (slHopf h) (algebraMap k (slHopf h) c))
      rw [extensionInclusion_coeff σ (slHopf h) c, f.commutes, g.commutes]
    · exact he
  exact RingHom.congr_fun e

private def twistAlgEquiv (σ : k →+* k) : slHopf h ≃ₐ[k] slTwist h σ :=
  AlgEquiv.ofAlgHom (toTwist h σ) (fromTwist h σ)
    (slTwist_ext h σ (fun i j ↦ by
      rw [AlgHom.comp_apply, fromTwist_entry, toTwist_entry, AlgHom.id_apply]))
    (slAlgHom_ext (fun i j ↦ by
      rw [AlgHom.comp_apply, toTwist_entry, fromTwist_entry, AlgHom.id_apply]))

private theorem twistIso_of_generators (A : HopfAlgebraCategory k) (σ : k →+* k)
    (x : ι → ι → A) (E : A ≃ₐ[k] extendAlong σ A)
    (hE : ∀ i j, E (x i j) = scalarTensor σ A 1 (x i j))
    (hε : ∀ i j, Bialgebra.counitAlgHom k A (x i j) = if i = j then 1 else 0)
    (hΔ : ∀ i j, Bialgebra.comulAlgHom k A (x i j) = ∑ l, x i l ⊗ₜ[k] x l j)
    (hext : ∀ {R : Type u} [CommRing R] [Algebra k R] {f g : A →ₐ[k] R},
      (∀ i j, f (x i j) = g (x i j)) → f = g) :
    ∃ e : A ≅ extendAlong σ A, ∀ i j, e.hom.hom (x i j) = scalarTensor σ A 1 (x i j) := by
  have ec : (Bialgebra.counitAlgHom k (extendAlong σ A)).comp E.toAlgHom =
      Bialgebra.counitAlgHom k A := by
    apply hext
    intro i j
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hE, counit_tmul, hε]
    split_ifs <;> simp
  have ed : (Algebra.TensorProduct.map E.toAlgHom E.toAlgHom).comp (Bialgebra.comulAlgHom k A) =
      (Bialgebra.comulAlgHom k (extendAlong σ A)).comp E.toAlgHom := by
    apply hext
    intro i j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hE, comul_tmul, hΔ]
    simp only [map_sum, Algebra.TensorProduct.map_tmul, comulTensorMap_tmul, AlgEquiv.coe_toAlgHom, hE]
  let b := BialgEquiv.ofAlgEquiv E ec ed
  let m : A ⟶ extendAlong σ A := ⟨b⟩
  let n : extendAlong σ A ⟶ A := ⟨b.symm⟩
  refine ⟨⟨m, n, ?_, ?_⟩, hE⟩
  · apply CommHopfAlgCat.hom_ext
    exact BialgHom.ext (fun a ↦ b.symm_apply_apply a)
  · apply CommHopfAlgCat.hom_ext
    exact BialgHom.ext (fun a ↦ b.apply_symm_apply a)

private theorem hopf_entries_of_matrixPoints (A : HopfAlgebraCategory k) (x : ι → ι → A)
    (s : (groupPointsFunctor k).obj (specGroup A) ≅
      Specs.StandardGroups.specialLinearPoints k ι)
    (hs : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (i j : ι),
      (s.hom.app R ((testSpec k).map (CommAlgCat.ofHom a).op)).val i j = a (x i j)) :
    (∀ i j : ι, Bialgebra.counitAlgHom k A (x i j) = if i = j then 1 else 0) ∧
    (∀ i j : ι, Bialgebra.comulAlgHom k A (x i j) = ∑ l, x i l ⊗ₜ[k] x l j) := by
  obtain ⟨e, he, _⟩ := hopfSpecPoints k
  let m (R : TestAlgebra k) := (e A ≪≫ s).hom.app R
  have hm (R : TestAlgebra k) (a : A →ₐ[k] R) (i j : ι) :
      (m R (toConv a)).val i j = a (x i j) := by
    have hh : (e A).hom.app R (toConv a) = (testSpec k).map (CommAlgCat.ofHom a).op :=
      Over.OverMorphism.ext (he A R (toConv a))
    change (s.hom.app R ((e A).hom.app R (toConv a))).val i j = _
    exact (congrArg (fun g ↦ (s.hom.app R g).val i j) hh).trans (hs R a i j)
  constructor
  · intro i j
    let K := CommAlgCat.of k k
    have h := hm K (Bialgebra.counitAlgHom k A) i j
    change (m K 1).val i j = Bialgebra.counitAlgHom k A (x i j) at h
    rw [map_one] at h
    exact h.symm.trans Matrix.one_apply
  · intro i j
    let T := CommAlgCat.of k (A ⊗[k] A)
    let a : A →ₐ[k] T := Algebra.TensorProduct.includeLeft
    let b : A →ₐ[k] T := Algebra.TensorProduct.includeRight
    let := convolutionGroup A T
    have h := hm T (toConv a * toConv b).ofConv i j
    change (m T (toConv a * toConv b)).val i j = _ at h
    rw [map_mul] at h
    change (∑ l, (m T (toConv a)).val i l * (m T (toConv b)).val l j) = _ at h
    simp only [hm] at h
    have hl : Algebra.TensorProduct.lift a b (fun x y ↦ Commute.all (a x) (b y)) = AlgHom.id k T := by
      apply Algebra.TensorProduct.ext'
      intro x y
      rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
      change (x ⊗ₜ[k] (1 : A)) * ((1 : A) ⊗ₜ[k] y) = x ⊗ₜ[k] y
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hprod : (toConv a * toConv b : WithConv (A →ₐ[k] T)) (x i j) =
        Bialgebra.comulAlgHom k A (x i j) := by
      rw [AlgHom.convMul_apply, hl, AlgHom.id_apply]
      rfl
    rw [← hprod, ← h]
    apply Finset.sum_congr rfl
    intro l _
    change (x i l ⊗ₜ[k] (1 : A)) * ((1 : A) ⊗ₜ[k] x l j) = x i l ⊗ₜ[k] x l j
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem relativeFrobenius_entries (A : HopfAlgebraCategory k) (p : ℕ)
    [Fact p.Prime] [CharP k p] (x : ι → ι → A)
    (s : (groupPointsFunctor k).obj (specGroup A) ≅
      Specs.StandardGroups.specialLinearPoints k ι)
    (hs : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (i j : ι),
      (s.hom.app R ((testSpec k).map (CommAlgCat.ofHom a).op)).val i j = a (x i j))
    (E : A ≅ Specs.RelativeFrobenius.twistCoordinates k p A)
    (hE : ∀ i j, E.hom.hom (x i j) = scalarTensor (frobenius k p) A 1 (x i j)) :
    ∃ (e : Specs.RelativeFrobenius.twist k p A ≅ specGroup A)
      (f : Specs.RelativeFrobenius.twistCoordinates k p A ⟶ A),
      Specs.RelativeFrobenius.PullbackFormula k p A f ∧
      ∀ (R : TestAlgebra k) (g : Points (specGroup A).X R) (i j : ι),
        (s.hom.app R (g ≫ (specGroupMap f ≫ e.hom).hom.hom)).val i j =
          ((s.hom.app R g).val i j) ^ p := by
  let e : Specs.RelativeFrobenius.twist k p A ≅ specGroup A :=
    (hopfSpec (CommRingCat.of k)).mapIso E.op
  let f := LinearAlgebraicGroups.RelativeFrobenius.pullback p A
  have hf := LinearAlgebraicGroups.RelativeFrobenius.pullback_formula p A
  refine ⟨e, f, hf, ?_⟩
  intro R g i j
  obtain ⟨b, hb, hn⟩ := hopfSpecPoints k
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso ((b A).hom.app R)).surjective g
  have hb' (c : WithConv (A →ₐ[k] R)) :
      (b A).hom.app R c = (testSpec k).map (CommAlgCat.ofHom c.ofConv).op :=
    Over.OverMorphism.ext (hb A R c)
  let d := E.hom ≫ f
  have hd : specGroupMap d = specGroupMap f ≫ e.hom :=
    (hopfSpec (CommRingCat.of k)).map_comp f.op E.hom.op
  have hn' := hn d R a
  change (b A).hom.app R (toConv (a.ofConv.comp d.hom.toAlgHom)) =
    (b A).hom.app R a ≫ (specGroupMap d).hom.hom at hn'
  have hpre : (s.hom.app R g).val i j = a.ofConv (x i j) := by
    exact (congrArg (fun t ↦ (s.hom.app R t).val i j) (ha.symm.trans (hb' a))).trans
      (hs R a.ofConv i j)
  have hpost : g ≫ (specGroupMap f ≫ e.hom).hom.hom =
      (testSpec k).map (CommAlgCat.ofHom (a.ofConv.comp d.hom.toAlgHom)).op := by
    rw [← hd, ← ha, ← hn']
    exact hb' _
  rw [hpost, hpre]
  refine (hs R _ _ _).trans ?_
  change a.ofConv (f.hom (E.hom.hom (x i j))) = a.ofConv (x i j) ^ p
  rw [hE, hf 1, one_smul, map_pow]

theorem relativeFrobeniusComparison : RelativeFrobeniusComparison.{u} := by
  intro k _ p _ _ h A X q s hs
  let σ := frobenius k p
  obtain ⟨hε, hΔ⟩ := hopf_entries_of_matrixPoints A (entry k) s hs
  obtain ⟨E, hE⟩ := twistIso_of_generators A σ (entry k) (twistAlgEquiv h σ)
    (toTwist_entry h σ) hε hΔ (fun he ↦ slAlgHom_ext he)
  obtain ⟨e, f, hf, he⟩ := relativeFrobenius_entries A p (entry k) s hs E hE
  exact ⟨e, f, hf, fun R g ↦ Matrix.ext fun i j ↦ he R g (ULift.up i) (ULift.up j)⟩

end RelativeFrobenius

section MarkedBorel

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.RankOneFlag (Index)
open Specs.SpecialLinearDatum
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue pairing)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.WeylDimension (MatrixOpposite firstDiagonalCharacter)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots contractingSubgroup)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics
open private matrixOrbit_entry matrixCocharacter_pairing matrixCocharacter matrixPoints_map
  from LinearAlgebraicGroups.RootData.SpecialLinearDatum
open private iso_of_sameSubgroup from LinearAlgebraicGroups.Representation.IntegralMarkedOppositeBorel
open private borelProjection_eq from LinearAlgebraicGroups.Representation.PositiveKempfVanishing
open private matrix_dominant exists_matrix_opposite from LinearAlgebraicGroups.Representation.WeylDimension

private theorem two_index (i : Index.{u}) : i = ⟨0⟩ ∨ i = ⟨1⟩ := by
  rcases i with ⟨i⟩
  fin_cases i <;> simp

variable {G : AffineAlgebraicGroup k} {s : SpecialMatrixPoints G 2}
variable {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
variable (B : UpperTriangularBorel T L M)

private abbrev negativeCocharacter : Cocharacter T.subgroup.group :=
  matrixCocharacter L (-B.exponents)

private abbrev negativeDirection : Cocharacter G.val :=
  negativeCocharacter B ≫ T.subgroup.inclusion

private def negativeExponent (i j : Index.{u}) : ℤ :=
  2 * ((i.down.val : ℤ) - j.down.val)

private theorem negativeOrbit_entry (R : TestAlgebra k) (g : Points G.val.X R) (i j : Index.{u}) :
    (s.hom.app (laurentAlgebra R) (orbit (negativeDirection B) g)).val i j =
      LaurentPolynomial.C ((s.hom.app R g).val i j) * LaurentPolynomial.T (negativeExponent i j) := by
  rw [matrixOrbit_entry (s := s) L (-B.exponents) R g i j]
  congr 2
  change -B.exponents.val i.down - -B.exponents.val j.down = _
  rw [B.exponent_eq]
  change -(1 - 2 * (i.down.val : ℤ)) - -(1 - 2 * (j.down.val : ℤ)) = _
  simp only [negativeExponent]
  ring

private theorem lower_of_limit (R : TestAlgebra k) {g z : Points G.val.X R}
    (h : HasLimit (negativeDirection B) g z) : (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0 := by
  obtain ⟨f, hf, _⟩ := h
  let i : Index.{u} := ⟨0⟩
  let j : Index.{u} := ⟨1⟩
  have e := congrArg (fun x : Points G.val.X (laurentAlgebra R) ↦
    (s.hom.app (laurentAlgebra R) x).val i j) hf
  rw [matrixPoints_map, negativeOrbit_entry B] at e
  change ((s.hom.app (polynomialAlgebra R) f).val i j).toLaurent =
    LaurentPolynomial.C ((s.hom.app R g).val i j) * LaurentPolynomial.T (-2) at e
  have hc := congrArg (fun a : LaurentPolynomial R ↦ a.coeff (-2)) e
  rw [CocharacterDynamics.coeff_toLaurent_neg _ (by decide),
    ← LaurentPolynomial.single_eq_C_mul_T] at hc
  simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, i, j] using hc.symm

private def lowerOrbitPolynomial (R : TestAlgebra k) (g : Points G.val.X R) :
    Matrix Index.{u} Index.{u} (Polynomial R) :=
  fun i j ↦ if 0 ≤ negativeExponent i j then
    Polynomial.C ((s.hom.app R g).val i j) * Polynomial.X ^ (negativeExponent i j).toNat else 0

private theorem lowerOrbitPolynomial_map (R : TestAlgebra k) (g : Points G.val.X R)
    (hg : (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0) :
    (lowerOrbitPolynomial (s := s) R g).map Polynomial.toLaurent =
      (s.hom.app (laurentAlgebra R) (orbit (negativeDirection B) g)).val := by
  ext i j
  rw [Matrix.map_apply, negativeOrbit_entry B]
  dsimp only [lowerOrbitPolynomial]
  split_ifs with h
  · rw [Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg h]
  · rcases two_index i with rfl | rfl <;> rcases two_index j with rfl | rfl <;>
      first | exact (h (by decide)).elim | simp [hg]

private theorem lower_hasExtension (R : TestAlgebra k) (g : Points G.val.X R)
    (hg : (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0) :
    HasExtension (negativeDirection B) g := by
  let a := lowerOrbitPolynomial (s := s) R g
  have he := lowerOrbitPolynomial_map B R g hg
  have hd : a.det = 1 := by
    apply Polynomial.toLaurent_injective
    rw [(Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R).map_det a]
    change (a.map Polynomial.toLaurent).det = Polynomial.toLaurent 1
    rw [he, map_one]
    exact (s.hom.app (laurentAlgebra R) (orbit (negativeDirection B) g)).property
  let f := (s.app (polynomialAlgebra R)).groupIsoToMulEquiv.symm ⟨a, hd⟩
  refine ⟨mapPoints (polynomialEvaluate R 0) f, f, ?_, rfl⟩
  apply (s.app (laurentAlgebra R)).groupIsoToMulEquiv.injective
  change s.hom.app (laurentAlgebra R) (mapPoints (polynomialToLaurent R) f) = _
  rw [matrixPoints_map, show s.hom.app (polynomialAlgebra R) f = ⟨a, hd⟩ from
    (s.app (polynomialAlgebra R)).groupIsoToMulEquiv.apply_symm_apply _]
  exact Subtype.ext he

private theorem limit_diagonal_entry (R : TestAlgebra k) {g z : Points G.val.X R}
    (h : HasLimit (negativeDirection B) g z) (i : Index.{u}) :
    (s.hom.app R z).val i i = (s.hom.app R g).val i i := by
  obtain ⟨f, hf, rfl⟩ := h
  have e := congrArg (fun x : Points G.val.X (laurentAlgebra R) ↦
    (s.hom.app (laurentAlgebra R) x).val i i) hf
  rw [matrixPoints_map, negativeOrbit_entry B] at e
  change ((s.hom.app (polynomialAlgebra R) f).val i i).toLaurent =
    LaurentPolynomial.C ((s.hom.app R g).val i i) * LaurentPolynomial.T (negativeExponent i i) at e
  have hC : ((s.hom.app (polynomialAlgebra R) f).val i i).toLaurent =
      (Polynomial.C ((s.hom.app R g).val i i)).toLaurent := by
    simpa [negativeExponent] using e
  have hPoly := Polynomial.toLaurent_injective hC
  rw [matrixPoints_map]
  change Polynomial.eval 0 ((s.hom.app (polynomialAlgebra R) f).val i i) = _
  rw [hPoly, Polynomial.eval_C]

private theorem negative_chamber :
    IsRegular T.subgroup (negativeCocharacter B) ∧
      positiveRoots T.subgroup (negativeCocharacter B) = (subgroupRoots T.subgroup B.limits.parabolic)ᶜ := by
  have he (r : RootIndices 2) :
      pairing T.subgroup.group (M.indices r).val (negativeCocharacter B) =
        2 * ((r.val.1.val : ℤ) - r.val.2.val) := by
    rw [matrixCocharacter_pairing]
    change -B.exponents.val r.val.1 - -B.exponents.val r.val.2 = _
    rw [B.exponent_eq]
    change -(1 - 2 * (r.val.1.val : ℤ)) - -(1 - 2 * (r.val.2.val : ℤ)) = _
    ring
  have hne (r : RootIndices 2) : r.val.1.val ≠ r.val.2.val := fun h ↦ r.property (Fin.ext h)
  refine ⟨?_, ?_⟩
  · intro α
    obtain ⟨r, rfl⟩ := M.indices.surjective α
    rw [he]
    have := hne r
    omega
  · ext α
    obtain ⟨r, rfl⟩ := M.indices.surjective α
    change 0 < pairing T.subgroup.group (M.indices r).val (negativeCocharacter B) ↔
      ¬ M.indices r ∈ subgroupRoots T.subgroup B.limits.parabolic
    rw [he, B.positive_iff]
    have := hne r
    change 0 < 2 * ((r.val.1.val : ℤ) - r.val.2.val) ↔ ¬ r.val.1.val < r.val.2.val
    omega

private theorem firstDiagonal_value (R : TestAlgebra k) (t : Points T.subgroup.group.X R) :
    characterValue (firstDiagonalCharacter L) R t =
      (s.hom.app R (t ≫ T.subgroup.inclusion.hom.hom)).val ⟨0⟩ ⟨0⟩ := by
  rw [firstDiagonalCharacter, L.characterValue_eq, T.matrix]
  simp [Specs.SpecialLinearDatum.coordinate, Pi.single_apply]

private theorem markedBorels (D : LimitDecomposition (negativeDirection B)) :
    ∃ (Q : MatrixOpposite B) (U : ClosedSubgroup Q.pair.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup Q.pair.positive) U ∧
      (∀ (R : TestAlgebra k) (g : Points G.val.X R),
        g ∈ SubgroupSections Q.pair.negative ((testSpec k).obj (op R)) ↔
          (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0) ∧
      ∀ (b : BorelProjection Q.pair) (R : TestAlgebra k) (g : Points Q.pair.negative.group.X R),
        characterValue (b.projection ≫ firstDiagonalCharacter L) R (g⁻¹) =
          (s.hom.app R (g ≫ Q.pair.negative.inclusion.hom.hom)).val ⟨1⟩ ⟨1⟩ := by
  obtain ⟨hreg, hop⟩ := negative_chamber B
  obtain ⟨hc, hB, hT, hroots, hU, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel G B.reductive T.subgroup T.split B.maximal
      (negativeCocharacter B) hreg D
  obtain ⟨_, U, hUpos⟩ := exists_matrix_opposite B
  let Q : MatrixOpposite B := ⟨D.parabolic, hB, hT, hroots.trans hop⟩
  refine ⟨Q, U, hUpos, ?_, ?_⟩
  · intro R g
    exact (D.parabolic_points R g).symm.trans
      ⟨fun ⟨_, hz⟩ ↦ lower_of_limit B R hz, lower_hasExtension B R g⟩
  · obtain ⟨e, he, hei⟩ := iso_of_sameSubgroup hc
    let b₀ : BorelProjection Q.pair := {
      inclusion := e.inv ≫ D.sectionMap
      inclusion_comp := by rw [Category.assoc, D.section_in_G, hei]
      projection := D.limit ≫ e.hom
      section_projection := by simp only [← Category.assoc, Category.assoc e.inv D.sectionMap D.limit,
        D.section_limit, Category.comp_id, Iso.inv_hom_id]
      radical := contractingSubgroup D
      isRadical := hU
      isKernel := by
        let e' : D.centralizer.group.X ≅ T.subgroup.group.X := (Grp.forget _).mapIso e
        change IsPullback D.contractingToParabolic.hom.hom (toUnit D.contracting.group.X)
          (D.limit.hom.hom ≫ e'.hom) η[T.subgroup.group.X]
        exact D.isKernel.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) e'.symm
          (by simp) (by simp)
          (by
            change 𝟙 _ ≫ D.limit.hom.hom = (D.limit.hom.hom ≫ e'.hom) ≫ e'.inv
            rw [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id])
          (by
            change 𝟙 _ ≫ η[D.centralizer.group.X] = η[T.subgroup.group.X] ≫ e.inv.hom.hom
            rw [Category.id_comp, IsMonHom.one_hom]) }
    intro b R g
    rw [borelProjection_eq b b₀]
    change characterValue (firstDiagonalCharacter L) R
      (g⁻¹ ≫ (D.limit ≫ e.hom).hom.hom) = _
    rw [firstDiagonal_value, Category.assoc, ← Grp.comp_hom_hom, Category.assoc, he]
    have h := limit_diagonal_entry B R (D.limit_points R g⁻¹) ⟨0⟩
    change (s.hom.app R (g⁻¹ ≫ (D.limit ≫ D.centralizer.inclusion).hom.hom)).val ⟨0⟩ ⟨0⟩ =
      (s.hom.app R (g⁻¹ ≫ D.parabolic.inclusion.hom.hom)).val ⟨0⟩ ⟨0⟩ at h
    rw [h]
    have hh : (s.hom.app R (g⁻¹ ≫ D.parabolic.inclusion.hom.hom)) =
        (s.hom.app R (g ≫ D.parabolic.inclusion.hom.hom))⁻¹ := by
      rw [GrpObj.inv_comp, map_inv]
    rw [hh]
    let a := s.hom.app R (g ≫ D.parabolic.inclusion.hom.hom)
    let b : Matrix.SpecialLinearGroup (Fin 2) R :=
      ⟨a.val.submatrix ULift.up ULift.up,
        (Matrix.det_submatrix_equiv_self Equiv.ulift.symm a.val).trans a.property⟩
    have h (x y : Fin 2) : (b⁻¹ : Matrix.SpecialLinearGroup (Fin 2) R).val x y =
        (a⁻¹ : Matrix.SpecialLinearGroup Index.{u} R).val ⟨x⟩ ⟨y⟩ := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv]
      exact congrFun (congrFun (Matrix.adjugate_submatrix_equiv_self Equiv.ulift.symm a.val) x) y
    change (a⁻¹ : Matrix.SpecialLinearGroup Index.{u} R).val ⟨0⟩ ⟨0⟩ = _
    rw [← h 0 0, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl

end MarkedBorel

section MarkedGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj MatrixGroups TensorProduct
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.RankOneFlag (Index plane planeBasis projectiveLine HasCoordinates)
open Specs.ProjectiveSpaces (LineRepresentation)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.QuotientEmbedding (Presentation)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open private matrixPoints_map from LinearAlgebraicGroups.RootData.SpecialLinearDatum
open private planeRepresentation vectorOfCoordinates coordinatesLine coordinatesLine_submodule
  planeLine planeLine_ext pointOfPlaneLine planeLine_pointOfPlaneLine hasCoordinates_change
  projectiveLineChart projectiveLineCharts_cover affinePoint_coordinates affineCoordinates
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private overHom overAlong glueOver glueOver_fac overHom_ext_affine exists_of_affineTests
  extendVector from LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private vectorOfCoordinates_change from LinearAlgebraicGroups.RootData.RankOneFlag
open private projection_eq_iff from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private descendAlongEffectiveEpi from LinearAlgebraicGroups.Representation.IntegralFlagGeometry

variable {G : AffineAlgebraicGroup k} (s : SpecialMatrixPoints G 2)

private def downMatrix (g : Matrix.SpecialLinearGroup Index.{u} R) : SL(2, R) :=
  ⟨g.val.submatrix ULift.up ULift.up, (Matrix.det_submatrix_equiv_self Equiv.ulift.symm g.val).trans g.property⟩

private def upMatrix (g : SL(2, R)) : Matrix.SpecialLinearGroup Index.{u} R :=
  ⟨g.val.submatrix ULift.down ULift.down, (Matrix.det_submatrix_equiv_self Equiv.ulift g.val).trans g.property⟩

private def reindexSL (R : Type u) [CommRing R] : Matrix.SpecialLinearGroup Index.{u} R ≃* SL(2, R) where
  toFun := downMatrix
  invFun := upMatrix
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' g h := Subtype.ext (Matrix.submatrix_mul_equiv g.val h.val ULift.up Equiv.ulift.symm ULift.up).symm

private def matrixPoint (R : TestAlgebra k) : Points G.val.X R ≃* SL(2, R) :=
  (s.app R).groupIsoToMulEquiv.trans (reindexSL R)

private theorem matrixPoint_entry (R : TestAlgebra k) (g : Points G.val.X R) (i j : Fin 2) :
    (matrixPoint s R g).val i j = (s.hom.app R g).val ⟨i⟩ ⟨j⟩ := rfl

private theorem matrixPoint_map {R S : TestAlgebra k} (a : R ⟶ S) (g : Points G.val.X R) :
    matrixPoint s S (mapPoints a g) = Matrix.SpecialLinearGroup.map a.hom.toRingHom (matrixPoint s R g) := by
  apply Subtype.ext
  ext i j
  rw [matrixPoint_entry]
  erw [matrixPoints_map (s := s) a g]
  rfl

private def secondFrame (R : TestAlgebra k) (g : Points G.val.X R) : R ⊗[k] plane k :=
  vectorOfCoordinates R (fun i ↦ (s.hom.app R g).val i ⟨1⟩)

private theorem column_unimodular (R : TestAlgebra k)
    (g : Matrix.SpecialLinearGroup Index.{u} R) :
    ∑ i : Index.{u}, (g⁻¹ : Matrix.SpecialLinearGroup Index.{u} R).val ⟨1⟩ i * g.val i ⟨1⟩ = 1 := by
  change (g⁻¹ * g : Matrix.SpecialLinearGroup Index.{u} R).val ⟨1⟩ ⟨1⟩ = 1
  rw [inv_mul_cancel]
  exact Matrix.one_apply_eq _

private def secondColumnPoint (R : TestAlgebra k) (g : Points G.val.X R) : Points (projectiveLine k) R :=
  let m : Matrix.SpecialLinearGroup Index.{u} R := s.hom.app R g
  pointOfPlaneLine (coordinatesLine R (fun i ↦ m.val i ⟨1⟩)
    (fun i ↦ (m⁻¹ : Matrix.SpecialLinearGroup Index.{u} R).val ⟨1⟩ i) (column_unimodular R m))

private theorem secondColumnPoint_coordinates (R : TestAlgebra k) (g : Points G.val.X R) :
    HasCoordinates (planeRepresentation k) R (secondColumnPoint s R g)
      (fun i ↦ (s.hom.app R g).val i ⟨1⟩) :=
  (congrArg Specs.ProjectiveSpaces.AffineLine.submodule (planeLine_pointOfPlaneLine _)).trans
    (coordinatesLine_submodule _ _ _ _)

private theorem secondColumnPoint_map {R S : TestAlgebra k} (a : R ⟶ S) (g : Points G.val.X R) :
    secondColumnPoint s S (mapPoints a g) = mapPoints a (secondColumnPoint s R g) := by
  apply planeLine_ext
  have h := secondColumnPoint_coordinates s S (mapPoints a g)
  erw [matrixPoints_map (s := s) a g] at h
  exact h.trans (hasCoordinates_change a (secondColumnPoint_coordinates s R g)).symm

private theorem secondFrame_injective (R : TestAlgebra k) (g : Points G.val.X R) :
    Function.Injective (fun r : R ↦ r • secondFrame s R g) := by
  let B := (planeBasis k).baseChange R
  let m : Matrix.SpecialLinearGroup Index.{u} R := s.hom.app R g
  intro a b hab
  have h (i : Index.{u}) : a * m.val i ⟨1⟩ = b * m.val i ⟨1⟩ := by
    have hi := congrArg (fun z ↦ B.equivFun z i) hab
    change B.equivFun (a • B.equivFun.symm (fun j ↦ m.val j ⟨1⟩)) i =
      B.equivFun (b • B.equivFun.symm (fun j ↦ m.val j ⟨1⟩)) i at hi
    simpa only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] using hi
  have e := column_unimodular R m
  have he (c : R) : ∑ i : Index.{u}, (m⁻¹ : Matrix.SpecialLinearGroup Index.{u} R).val ⟨1⟩ i *
      (c * m.val i ⟨1⟩) = c := by
    conv_lhs =>
      arg 2
      intro i
      rw [mul_left_comm]
    rw [← Finset.mul_sum, e, mul_one]
  rw [← he a, ← he b]
  exact Finset.sum_congr rfl (fun i _ ↦ congrArg (_ * ·) (h i))

private theorem secondColumnPoint_eq (R : TestAlgebra k) (g h : Points G.val.X R) :
    secondColumnPoint s R g = secondColumnPoint s R h ↔
      (matrixPoint s R (g⁻¹ * h)).val 0 1 = 0 := by
  let a := matrixPoint s R g
  let b := matrixPoint s R h
  let v (m : SL(2, R)) := fun i : Index.{u} ↦ m.val i.down 1
  let f (m : SL(2, R)) := vectorOfCoordinates (k := k) R (v m)
  have hg : (planeLine (secondColumnPoint s R g)).submodule = Submodule.span R {f a} :=
    secondColumnPoint_coordinates s R g
  have hh : (planeLine (secondColumnPoint s R h)).submodule = Submodule.span R {f b} :=
    secondColumnPoint_coordinates s R h
  rw [map_mul, map_inv]
  constructor
  · intro e
    have he : Submodule.span R {f a} = Submodule.span R {f b} := hg.symm.trans (e ▸ hh)
    have hb : f b ∈ Submodule.span R {f a} := he.symm ▸ Submodule.subset_span (Set.mem_singleton _)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    have hcol : (secondColumn b).val = fun i ↦ c * (secondColumn a).val i := by
      funext i
      have hi := congrArg (fun z ↦ ((planeBasis k).baseChange R).equivFun z (ULift.up i)) hc
      change ((planeBasis k).baseChange R).equivFun (c • ((planeBasis k).baseChange R).equivFun.symm (v a)) ⟨i⟩ =
        ((planeBasis k).baseChange R).equivFun (((planeBasis k).baseChange R).equivFun.symm (v b)) ⟨i⟩ at hi
      change b i 1 = c * a i 1
      simpa only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, v] using hi.symm
    have hu : IsUnit c := by
      obtain ⟨x, y, he⟩ := (secondColumn b).property
      change x * b 0 1 + y * b 1 1 = 1 at he
      rw [show b 0 1 = c * a 0 1 from congrFun hcol 0,
        show b 1 1 = c * a 1 1 from congrFun hcol 1] at he
      exact IsUnit.of_mul_eq_one (x * a 0 1 + y * a 1 1) (by linear_combination he)
    obtain ⟨u, rfl⟩ := hu
    exact (lower_of_scale a b u (Subtype.ext hcol)).1
  · intro e
    apply planeLine_ext
    rw [hg, hh]
    let d := a⁻¹ * b
    have hd : a * d = b := by simp [d]
    have h0 : d 0 1 = 0 := e
    obtain ⟨u, hu⟩ := diagonalUnit d h0
    have hu' : (u : R) • f a = f b := by
      apply ((planeBasis k).baseChange R).equivFun.injective
      have hcol := (secondColumn_lower a d h0)
      rw [hd] at hcol
      ext i
      change ((planeBasis k).baseChange R).equivFun ((u : R) •
        ((planeBasis k).baseChange R).equivFun.symm (v a)) i =
          ((planeBasis k).baseChange R).equivFun (((planeBasis k).baseChange R).equivFun.symm (v b)) i
      simp only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, v]
      have e := (congrFun (congrArg Subtype.val hcol) i.down).symm
      change (d 1 1) * a i.down 1 = b i.down 1 at e
      exact hu.symm ▸ e
    rw [← hu']
    exact (Submodule.span_singleton_smul_eq (Units.isUnit u) (f a)).symm

private theorem markedQuotient {H : ClosedSubgroup G.val} (Q : Presentation H)
    (hH : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections H ((testSpec k).obj (op R)) ↔
        (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0) :
    ∃ c : Q.scheme ≅ projectiveLine k,
      ∀ (R : TestAlgebra k) (g : Points G.val.X R),
        g ≫ Q.projection ≫ c.hom = secondColumnPoint s R g := by
  obtain ⟨q, hq⟩ := exists_of_affineTests (secondColumnPoint s) (secondColumnPoint_map s)
  have sameFibre {T : SchemeOver k} (g h : T ⟶ G.val.X) :
      g ≫ Q.projection = h ≫ Q.projection ↔ g ≫ q = h ≫ q := by
    have he (R : TestAlgebra k) (a : Points T R) :
        (a ≫ g) ≫ Q.projection = (a ≫ h) ≫ Q.projection ↔
          (a ≫ g) ≫ q = (a ≫ h) ≫ q := by
      rw [projection_eq_iff Q, hH, hq, hq, secondColumnPoint_eq s]
      rfl
    constructor <;> intro h'
    · apply overHom_ext_affine
      intro R a
      simpa only [Category.assoc] using (he R a).1 (by simpa only [Category.assoc] using congrArg (a ≫ ·) h')
    · apply overHom_ext_affine
      intro R a
      simpa only [Category.assoc] using (he R a).2 (by simpa only [Category.assoc] using congrArg (a ≫ ·) h')
  let := Q.flat
  let := Q.surjective
  let := Q.finitePresentation
  obtain ⟨c, hc⟩ := descendAlongEffectiveEpi Q.projection q
    (fun _ _ _ h ↦ (sameFibre _ _).mp h)
  let i₀ : Index.{u} := ⟨0⟩
  let i₁ : Index.{u} := ⟨1⟩
  obtain ⟨hopen, hcover, _⟩ := projectiveLineCharts_cover (k := k) i₀
  let 𝒰 : (projectiveLine k).left.OpenCover := {
    I₀ := Index.{u}
    X := fun _ ↦ (Specs.FlagLineBundle.affineLine k).left
    f := fun i ↦ (projectiveLineChart k i).left
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ (hcover x).elim (fun h ↦ ⟨i₀,h⟩) (fun h ↦ ⟨i₁,h⟩), hopen⟩ }
  let K := CommAlgCat.of k (Polynomial k)
  have hlift (i : Index.{u}) :
      ∃ g : Points G.val.X K, g ≫ q = projectiveLineChart k i := by
    let v := affineCoordinates i (R := K) Polynomial.X
    have hv : IsCoprime (v ⟨0⟩) (v ⟨1⟩) := by
      rcases two_index i with rfl | rfl
      · exact ⟨1, 0, by simp [v, affineCoordinates]⟩
      · exact ⟨0, 1, by simp [v, affineCoordinates]⟩
    obtain ⟨m, hm₀, hm₁⟩ := hv.exists_SL2_col 1
    let g := (matrixPoint s K).symm m
    refine ⟨g, ?_⟩
    rw [hq]
    apply planeLine_ext
    change _ = (planeLine (projectiveLineChart k i)).submodule
    rw [secondColumnPoint_coordinates s K g, projectiveLineChart, affinePoint_coordinates]
    have hv' : (fun j : Index.{u} ↦ (s.hom.app K g).val j ⟨1⟩) = v := by
      funext j
      change (s.hom.app K g).val ⟨j.down⟩ ⟨1⟩ = _
      rw [← matrixPoint_entry s K g j.down 1, MulEquiv.apply_symm_apply]
      rcases two_index j with rfl | rfl
      · exact hm₀
      · exact hm₁
    rw [hv']
    rfl
  choose g hg using hlift
  let chart (i : 𝒰.I₀) : Specs.FlagLineBundle.affineLine k ⟶ projectiveLine k :=
    projectiveLineChart k i
  let d (i : 𝒰.I₀) : overAlong (𝒰.f i) ⟶ Specs.FlagLineBundle.affineLine k :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ (Specs.FlagLineBundle.affineLine k).hom =
        (chart i).left ≫ (projectiveLine k).hom
      rw [Category.id_comp]
      exact (Over.w (chart i)).symm)
  let m (i : 𝒰.I₀) : overAlong (𝒰.f i) ⟶ Q.scheme := d i ≫ g i ≫ Q.projection
  have hm (i j : 𝒰.I₀) : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (m i).left =
      pullback.snd _ _ ≫ (m j).left := by
    let W : SchemeOver k := Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ (chart i).left ≫ (projectiveLine k).hom)
    let a : W ⟶ Specs.FlagLineBundle.affineLine k := Over.homMk (pullback.fst _ _)
      (congrArg (pullback.fst (𝒰.f i) (𝒰.f j) ≫ ·) (Over.w (chart i)).symm)
    let b : W ⟶ Specs.FlagLineBundle.affineLine k := Over.homMk (pullback.snd _ _) (by
      change _ ≫ _ = pullback.fst _ _ ≫ (chart i).left ≫ _
      rw [← Category.assoc, pullback.condition, Category.assoc]
      exact congrArg (pullback.snd (𝒰.f i) (𝒰.f j) ≫ ·) (Over.w (chart j)).symm)
    have hh : a ≫ g i ≫ q = b ≫ g j ≫ q := by
      rw [hg, hg]
      exact Over.OverMorphism.ext pullback.condition
    exact congrArg Over.Hom.left ((sameFibre (a ≫ g i) (b ≫ g j)).2 (by simpa [Category.assoc] using hh))
  let t := glueOver 𝒰 m hm
  have ht (i : 𝒰.I₀) : chart i ≫ t = g i ≫ Q.projection := by
    apply Over.OverMorphism.ext
    have hf := congrArg Over.Hom.left (glueOver_fac 𝒰 m hm i)
    change (chart i).left ≫ t.left = (d i).left ≫ (g i).left ≫ Q.projection.left at hf
    change (chart i).left ≫ t.left = (g i).left ≫ Q.projection.left
    simpa only [d, Over.homMk_left, Category.id_comp] using hf
  have htc : t ≫ c = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply 𝒰.hom_ext
    intro i
    have h : chart i ≫ t ≫ c = chart i ≫ 𝟙 _ := by
      rw [← Category.assoc, ht, Category.assoc, hc, hg, Category.comp_id]
    exact congrArg Over.Hom.left h
  have hct : c ≫ t = 𝟙 _ := by
    let := Over.epi_of_epi_left Q.projection
    apply (cancel_epi Q.projection).mp
    rw [← Category.assoc, hc, Category.comp_id]
    apply Over.OverMorphism.ext
    let 𝒱 : G.val.X.left.OpenCover := 𝒰.pullback₁ q.left
    apply 𝒱.hom_ext
    intro i
    change Index.{u} at i
    let W : SchemeOver k := Over.mk (pullback.snd q.left (𝒰.f i) ≫ (Specs.FlagLineBundle.affineLine k).hom)
    let a : W ⟶ G.val.X := Over.homMk (pullback.fst _ _) (by
      change pullback.fst q.left (𝒰.f i) ≫ G.val.X.hom =
        pullback.snd q.left (𝒰.f i) ≫ (Specs.FlagLineBundle.affineLine k).hom
      rw [← Over.w q, ← Category.assoc, pullback.condition, Category.assoc, Over.w (chart i)])
    let b : W ⟶ Specs.FlagLineBundle.affineLine k := Over.homMk (pullback.snd _ _) rfl
    have hab : a ≫ q = b ≫ chart i := Over.OverMorphism.ext pullback.condition
    have h := (sameFibre a (b ≫ g i)).2 (by rw [Category.assoc, hg, hab])
    have hh : a ≫ q ≫ t = a ≫ Q.projection := by
      rw [← Category.assoc, hab, Category.assoc, ht, h, Category.assoc]
    exact congrArg Over.Hom.left hh
  exact ⟨⟨c, t, hct, htc⟩, fun R g ↦ by rw [hc, hq]⟩

end MarkedGeometry

section MarkedInduction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra WithConv
open Algebra.TensorProduct
open scoped CategoryTheory.MonObj MatrixGroups TensorProduct
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection covariantFunctions SchemeCovariant leftRegularCoaction)
open Specs.SimpleClassification (SocleModel)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.PrimitiveLine (orbitCoefficient)
open _root_.LinearAlgebraicGroups.RationalRepresentations (evaluate tensorCoordinate)
open private transport_point_surjective affinePoint affinePointEquiv affinePoint_mul affinePoint_inv
  linePoint_comp linePointEquiv schemeCovariant_iff eval_coordinateFunction
  leftCoactionHom leftCoactionHom_linear leftEval tensorPoint tensorPoint_map
  tensorPoint_inclusions includeLeft_mul_includeRight from
  LinearAlgebraicGroups.Representation.FlagLineBundle
open private characterValue_pow from LinearAlgebraicGroups.Representation.RootWeightAction
open private tensor_eq_sum_basis from LinearAlgebraicGroups.Affine.RationalRepresentations

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {U : ClosedSubgroup P.positive.group}
variable (s : SpecialMatrixPoints G 2) {χ : Character P.torus.group} {n : ℕ}
variable (V : SocleModel P U (χ ^ n))

private def atPoint {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (R : TestAlgebra k) (g : Points G.val.X R) : A →ₐ[k] R :=
  (affinePointEquiv A R).symm (g ≫ e.inv.hom.hom)

private theorem atPoint_apply {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (R : TestAlgebra k) (a : A →ₐ[k] R) :
    atPoint e R (affinePoint R a ≫ e.hom.hom.hom) = a := by
  change (affinePointEquiv A R).symm ((affinePoint R a ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) = a
  rw [Category.assoc, show e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ from
    ((Grp.forget (SchemeOver k)).mapIso e).hom_inv_id, Category.comp_id]
  exact (affinePointEquiv A R).symm_apply_apply a

private theorem atPoint_injective {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (R : TestAlgebra k) : Function.Injective (atPoint e R) := by
  intro g h he
  let i := (Grp.forget (SchemeOver k)).mapIso e
  have : IsIso e.inv.hom.hom := i.isIso_inv
  exact (cancel_mono e.inv.hom.hom).mp ((affinePointEquiv A R).symm.injective he)

private theorem atPoint_natural {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    {R S : TestAlgebra k} (a : R ⟶ S) (g : Points G.val.X R) :
    atPoint e S (mapPoints a g) = a.hom.comp (atPoint e R g) := by
  obtain ⟨f, rfl⟩ := transport_point_surjective e R g
  have h : mapPoints a (affinePoint R f ≫ e.hom.hom.hom) =
      affinePoint S (a.hom.comp f) ≫ e.hom.hom.hom := by
    rw [mapPoints, ← Category.assoc]
    unfold affinePoint
    rw [← Functor.map_comp]
    rfl
  rw [h, atPoint_apply, atPoint_apply]

private theorem inverse_character_pow
    (hχ : ∀ (R : TestAlgebra k) (b : Points P.negative.group.X R),
      characterValue (V.projection.projection ≫ χ) R b⁻¹ =
        (matrixPoint s R (b ≫ P.negative.inclusion.hom.hom)).val 1 1)
    (R : TestAlgebra k) (b : Points P.negative.group.X R) :
    characterValue (V.projection.projection ≫ χ ^ n) R b⁻¹ =
      (matrixPoint s R (b ≫ P.negative.inclusion.hom.hom)).val 1 1 ^ n := by
  rw [← hχ]
  change characterValue (χ ^ n) R (b⁻¹ ≫ V.projection.projection.hom.hom) =
    characterValue χ R (b⁻¹ ≫ V.projection.projection.hom.hom) ^ n
  exact characterValue_pow χ R _ n

private theorem covariantMatrixComparison
    (hB : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections P.negative ((testSpec k).obj (op R)) ↔
        (matrixPoint s R g).val 0 1 = 0)
    (hχ : ∀ (R : TestAlgebra k) (b : Points P.negative.group.X R),
      characterValue (V.projection.projection ≫ χ) R b⁻¹ =
        (matrixPoint s R (b ≫ P.negative.inclusion.hom.hom)).val 1 1) :
    ∃ E : covariantFunctions V.restriction V.coordinate ≃ₗ[k] matrixInduction k n,
      ∀ f (R : TestAlgebra k) (g : Points G.val.X R),
        (E f).val R (matrixPoint s R g) = atPoint V.groupIso R g f.val := by
  let C := covariantFunctions V.restriction V.coordinate
  let K := CommAlgCat.of k V.A
  let uv := affinePoint K (AlgHom.id k V.A) ≫ V.groupIso.hom.hom.hom
  let L : V.A →ₗ[k] GroupFunctions k :=
    LinearMap.pi fun R ↦ LinearMap.pi fun m ↦
      (atPoint V.groupIso R ((matrixPoint s R).symm m)).toLinearMap
  have hL (f : V.A) (R : TestAlgebra k) (g : Points G.val.X R) :
      L f R (matrixPoint s R g) = atPoint V.groupIso R g f := by
    change atPoint V.groupIso R ((matrixPoint s R).symm (matrixPoint s R g)) f = _
    rw [MulEquiv.symm_apply_apply]
  have hn {R S : TestAlgebra k} (a : R ⟶ S) (m : SL(2, R)) (f : V.A) :
      a.hom (L f R m) = L f S (Matrix.SpecialLinearGroup.map a.hom.toRingHom m) := by
    obtain ⟨g, rfl⟩ := (matrixPoint s R).surjective m
    rw [← matrixPoint_map s a g, hL, hL, atPoint_natural]
    rfl
  have hcov (f : V.A) : f ∈ C ↔ L f ∈ matrixInduction k n := by
    rw [← schemeCovariant_iff V.groupIso V.borelIso V.restriction V.character
      V.restriction_spec V.character_spec V.coordinate V.coordinate_spec]
    constructor
    · intro hf
      refine ⟨fun a m ↦ hn a m f, ?_⟩
      intro R g b hb
      obtain ⟨x, rfl⟩ := (matrixPoint s R).surjective g
      obtain ⟨y, rfl⟩ := (matrixPoint s R).surjective b
      obtain ⟨b, rfl⟩ := (hB R y).2 hb
      let y := b ≫ P.negative.inclusion.hom.hom
      change L f R (matrixPoint s R x * matrixPoint s R y) = _ 
      rw [← map_mul, hL, hL]
      obtain ⟨g, rfl⟩ := transport_point_surjective V.groupIso R x
      have h := hf R (affinePoint R g ≫ V.groupIso.hom.hom.hom) b (g f)
        (eval_coordinateFunction V.groupIso R g f)
      change _ = Specs.FlagLineBundle.linePoint R
        (characterValue (V.projection.projection ≫ χ ^ n) R b⁻¹ * g f) at h
      rw [inverse_character_pow s V hχ] at h
      obtain ⟨m, hm⟩ := transport_point_surjective V.groupIso R
        ((affinePoint R g ≫ V.groupIso.hom.hom.hom) * y)
      rw [← hm, eval_coordinateFunction] at h
      rw [← hm, atPoint_apply, atPoint_apply]
      exact (linePointEquiv R).injective h
    · intro hf R x b z hz
      let y := b ≫ P.negative.inclusion.hom.hom
      have hb : (matrixPoint s R y).val 0 1 = 0 := (hB R y).mp ⟨b, rfl⟩
      have hc := hf.2 R (matrixPoint s R x) (matrixPoint s R y) hb
      rw [← map_mul, hL, hL] at hc
      obtain ⟨g, rfl⟩ := transport_point_surjective V.groupIso R x
      obtain ⟨m, hm⟩ := transport_point_surjective V.groupIso R
        ((affinePoint R g ≫ V.groupIso.hom.hom.hom) * y)
      rw [eval_coordinateFunction] at hz
      have h := (linePointEquiv R).injective hz
      rw [← hm, atPoint_apply, atPoint_apply, h] at hc
      change ((affinePoint R g ≫ V.groupIso.hom.hom.hom) * y) ≫ _ = _
      rw [← hm, eval_coordinateFunction, hc, inverse_character_pow s V hχ]
  let E := (L.comp C.subtype).codRestrict _ (fun f ↦ (hcov f.val).1 f.property)
  have hE : Function.Bijective E := by
    constructor
    · intro f g h
      apply Subtype.ext
      have l := congrArg (fun x : matrixInduction k n ↦ x.val K (matrixPoint s K uv)) h
      change L f.val K (matrixPoint s K uv) = L g.val K (matrixPoint s K uv) at l
      rw [hL, hL, atPoint_apply] at l
      exact l
    · intro f
      let x := f.val K (matrixPoint s K uv)
      have hx : L x = f.val := by
        funext R m
        obtain ⟨g, rfl⟩ := (matrixPoint s R).surjective m
        obtain ⟨a, rfl⟩ := transport_point_surjective V.groupIso R g
        have hm : mapPoints (CommAlgCat.ofHom a) uv = affinePoint R a ≫ V.groupIso.hom.hom.hom := by
          apply atPoint_injective V.groupIso R
          rw [atPoint_natural, atPoint_apply, atPoint_apply]
          exact AlgHom.comp_id a
        have h := f.property.1 (CommAlgCat.ofHom a) (matrixPoint s K uv)
        rw [← matrixPoint_map s (CommAlgCat.ofHom a) uv, hm] at h
        rw [hL, atPoint_apply]
        exact h
      refine ⟨⟨x, (hcov x).2 (hx.symm ▸ f.property)⟩, Subtype.ext hx⟩
  exact ⟨LinearEquiv.ofBijective E hE, fun f R g ↦ hL f.val R g⟩


private def contractTensor {A R : Type u} [AddCommGroup A] [Module k A]
    [CommRing R] [Algebra k R] (ℓ : R →ₗ[k] k) : A ⊗[k] R →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp (ℓ.lTensor A)

private theorem contractTensor_tmul {A R : Type u} [AddCommGroup A] [Module k A]
    [CommRing R] [Algebra k R] (ℓ : R →ₗ[k] k) (a : A) (z : R) :
    contractTensor ℓ (a ⊗ₜ[k] z) = ℓ z • a := by simp [contractTensor]

private theorem tensorProject_evaluate {V A : Type u} [AddCommGroup V] [Module k V]
    [CommRing A] [Algebra k A] [Algebra k R]
    (j : V →ₗ[k] A) (a : A →ₐ[k] R) (z : V ⊗[k] A) :
    (Algebra.TensorProduct.map (AlgHom.id k A) a) (j.rTensor A z) =
      j.rTensor R (a.toLinearMap.lTensor V z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem form_contraction_eq {V A I : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup A] [Module k A] [Fintype I] [DecidableEq I] [Algebra k R]
    (b : Module.Basis I k V) (F : Forms k n →ₗ[k] V) (j : V →ₗ[k] A)
    (hj : Function.Injective j) (w : Forms R n) (z : V ⊗[k] R)
    (hte : (∑ i : Fin (n + 1), j (F (term k n i)) ⊗ₜ[k] w.val.coeff (exponents n i)) =
      j.rTensor R z) (ℓ : R →ₗ[k] k) :
    F (contract ℓ w) = ∑ i, ℓ (tensorCoordinate b i z) • b i := by
  have ht := congrArg (contractTensor ℓ : A ⊗[k] R →ₗ[k] A) hte
  have hz : contractTensor ℓ (j.rTensor R z) = ∑ i, ℓ (tensorCoordinate b i z) • j (b i) := by
    conv_lhs => rw [← tensor_eq_sum_basis b z]
    simp only [map_sum, LinearMap.rTensor_tmul, contractTensor_tmul]
  apply hj
  simp only [map_sum, map_smul, contract, hz, contractTensor_tmul] at ht ⊢
  exact ht


private theorem extend_orbit {R S : TestAlgebra k}
    (a : R ⟶ S) (g : SL(2, R)) (v : Forms k n) :
    MvPolynomial.map a.hom.toRingHom (act g.val (extend v)).val =
      (act (Matrix.SpecialLinearGroup.map a.hom.toRingHom g).val (extend v)).val := by
  change MvPolynomial.map a.hom.toRingHom (substitution g.val (MvPolynomial.map (algebraMap k R) v.val)) =
    substitution (g.val.map a.hom.toRingHom) (MvPolynomial.map (algebraMap k S) v.val)
  rw [substitution_map, MvPolynomial.map_map]
  exact congrArg (fun h : k →+* S ↦ substitution (g.val.map a.hom.toRingHom) (MvPolynomial.map h v.val))
    a.hom.comp_algebraMap

private theorem eval_mapped_form {S : Type u} [CommRing S] [Algebra k R] [Algebra k S]
    (a : R →ₐ[k] S) {m : ℕ} (w : Forms R m) (d : Fin 2 → S) :
    aeval d (MvPolynomial.map a.toRingHom w.val) =
      ∑ i : Fin (m + 1), a (w.val.coeff (exponents m i)) * aeval d (term k m i).val := by
  let := a.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  have hterm (i : Fin (m + 1)) :
      aeval (R := R) d (term R m i).val = aeval (R := k) d (term k m i).val := by
    simp [term, aeval_monomial]
  change aeval (R := S) d (MvPolynomial.map (algebraMap R S) w.val) = _
  rw [aeval_map_algebraMap]
  have h := congrArg (fun f : Forms R m ↦ aeval (R := R) d f.val) (sum_terms w)
  refine h.symm.trans ?_
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum, map_smul, hterm]
  rfl

private theorem covariant_orbit_tensors (F : Forms k n ≃ₗ[k] covariantFunctions V.restriction V.coordinate)
    (hF : ∀ (f : Forms k n) (R : TestAlgebra k) (g : Points G.val.X R),
      atPoint V.groupIso R g (F f).val =
        aeval (determinantCoordinates (secondColumn (matrixPoint s R g)).val) f.val)
    (R : TestAlgebra k) (a : V.A →ₐ[k] R) (f : Forms k n) :
    let g : Points G.val.X R := affinePoint R a ≫ V.groupIso.hom.hom.hom
    let w := act (matrixPoint s R g).val (extend f)
    (∑ i : Fin (n + 1), (F (term k n i)).val ⊗ₜ[k] coefficients R n w i) =
      (covariantFunctions V.restriction V.coordinate).subtype.rTensor R
        (evaluate V.A V.inducedCoaction a (F f)) := by
  intro g w
  let A := V.A
  let T := CommAlgCat.of k (A ⊗[k] R)
  let l : A →ₐ[k] T := includeLeft
  let r : R →ₐ[k] T := includeRight
  let q : R ⟶ T := CommAlgCat.ofHom r
  let h : Points G.val.X T := affinePoint T l ≫ V.groupIso.hom.hom.hom
  have hmap : mapPoints q g = affinePoint T (r.comp a) ≫ V.groupIso.hom.hom.hom := by
    apply atPoint_injective V.groupIso T
    have hg : atPoint V.groupIso R g = a := atPoint_apply V.groupIso R a
    rw [atPoint_natural, hg, atPoint_apply]
    rfl
  have he (u : Forms k n) : l (F u).val =
      aeval (determinantCoordinates (secondColumn (matrixPoint s T h)).val) u.val := by
    rw [← hF u T h]
    exact congrArg (fun j : A →ₐ[k] T ↦ j (F u).val) (atPoint_apply V.groupIso T l).symm
  have ht :
      (∑ i : Fin (n + 1), (F (term k n i)).val ⊗ₜ[k] coefficients R n w i) =
        aeval (determinantCoordinates (secondColumn (matrixPoint s T h)).val)
          (MvPolynomial.map r.toRingHom w.val) := by
    change _ = aeval (determinantCoordinates (secondColumn (matrixPoint s T h)).val)
      (MvPolynomial.map r.toRingHom w.val)
    rw [eval_mapped_form r]
    apply Finset.sum_congr rfl
    intro i _
    rw [← he, mul_comm]
    exact (includeLeft_mul_includeRight ((F (term k n i)).val)
      (w.val.coeff (exponents n i))).symm
  rw [ht]
  have hw := extend_orbit q (matrixPoint s R g) f
  change MvPolynomial.map r.toRingHom w.val =
    (act (Matrix.SpecialLinearGroup.map q.hom.toRingHom (matrixPoint s R g)).val (extend f)).val at hw
  rw [hw, ← matrixPoint_map s q g]
  have hag : aeval (determinantCoordinates (secondColumn (matrixPoint s T h)).val)
        (act (matrixPoint s T (mapPoints q g)).val (extend f)).val =
      atPoint V.groupIso T ((mapPoints q g)⁻¹ * h) (F f).val := by
    rw [hF]
    change aeval (determinantCoordinates (secondColumn (matrixPoint s T h)).val)
        (substitution (matrixPoint s T (mapPoints q g)).val (MvPolynomial.map (algebraMap k T) f.val)) = _
    rw [eval_substitution, determinantCoordinates_action, ← secondColumn_mul, map_mul, map_inv]
  rw [hag, hmap]
  let := convolutionGroup A T
  let b : WithConv (A →ₐ[k] T) := toConv (r.comp a)
  let d : WithConv (A →ₐ[k] T) := toConv l
  have hp : (affinePoint T (b⁻¹ * d).ofConv ≫ V.groupIso.hom.hom.hom) =
      (affinePoint T (r.comp a) ≫ V.groupIso.hom.hom.hom)⁻¹ * h := by
    rw [affinePoint_mul, affinePoint_inv, MonObj.mul_comp, GrpObj.inv_comp]
  rw [← hp, atPoint_apply]
  have hδ := LinearMap.congr_fun V.leftTranslation (F f)
  change (covariantFunctions V.restriction V.coordinate).subtype.rTensor A
    (V.inducedCoaction.coaction (F f)) = leftRegularCoaction A (F f).val at hδ
  have hm : Algebra.TensorProduct.map (AlgHom.id k A) a = tensorPoint l (r.comp a) := by
    have h' := tensorPoint_map (AlgHom.id k A) a l r
    rw [tensorPoint_inclusions, AlgHom.id_comp, AlgHom.comp_id] at h'
    exact h'
  have hh := tensorProject_evaluate (covariantFunctions V.restriction V.coordinate).subtype a
    (V.inducedCoaction.coaction (F f))
  change _ = (covariantFunctions V.restriction V.coordinate).subtype.rTensor R
    (evaluate V.A V.inducedCoaction a (F f)) at hh
  rw [← hh, hδ, hm, ← leftCoactionHom_linear]
  exact (leftEval l (r.comp a) (F f).val).symm

private theorem intertwines_induction (F : Forms k n ≃ₗ[k] covariantFunctions V.restriction V.coordinate)
    (hF : ∀ (f : Forms k n) (R : TestAlgebra k) (g : Points G.val.X R),
      atPoint V.groupIso R g (F f).val =
        aeval (determinantCoordinates (secondColumn (matrixPoint s R g)).val) f.val)
    (R : TestAlgebra k) (g : Points G.val.X R) (ℓ : R →ₗ[k] k) (f : Forms k n) :
    let E := F.trans V.inducedBasis.equivFun
    E (contract ℓ (act (matrixPoint s R g).val (extend f))) =
      orbitCoefficient V.inducedAction R g ℓ (E f) := by
  intro E
  obtain ⟨a, rfl⟩ := transport_point_surjective V.groupIso R g
  let g : Points G.val.X R := affinePoint R a ≫ V.groupIso.hom.hom.hom
  let w := act (matrixPoint s R g).val (extend f)
  let z := evaluate V.A V.inducedCoaction a (F f)
  let b := V.inducedBasis
  let C := covariantFunctions V.restriction V.coordinate
  have hx := covariant_orbit_tensors s V F hF R a f
  have h : F (contract ℓ w) = ∑ i, ℓ (tensorCoordinate b i z) • b i :=
    form_contraction_eq b F.toLinearMap C.subtype Subtype.val_injective w z hx ℓ
  change b.equivFun (F (contract ℓ w)) = orbitCoefficient V.inducedAction R g ℓ (E f)
  rw [h, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  funext i
  have he := V.inducedAction_spec R a (E f) i
  have hf : b.equivFun.symm (E f) = F f := LinearEquiv.symm_apply_apply b.equivFun (F f)
  rw [hf] at he
  exact congrArg ℓ he.symm

private theorem stability_iff {I : Type u} [Fintype I] [DecidableEq I]
    (ρ : Specs.RootWeightAction.Representation G.val I) (N : Submodule k (I → k)) :
    Specs.PrimitiveLine.IsStable ρ N ↔
      ∀ (R : TestAlgebra k) (g : Points G.val.X R) (ℓ : R →ₗ[k] k) (v : I → k), v ∈ N →
        orbitCoefficient ρ R g ℓ v ∈ N := by
  unfold Specs.PrimitiveLine.IsStable Specs.CyclicHighestWeight.orbitSpan
  simp only [Category.comp_id, iSup_le_iff, Submodule.span_le, Set.range_subset_iff]
  exact ⟨fun h R g ℓ v hv ↦ h v hv R g ℓ, fun h v hv R g ℓ ↦ h R g ℓ v hv⟩

private theorem induction_socle {p : ℕ} [Fact p.Prime] [CharP k p] {χ : Character P.torus.group}
    (V : SocleModel P U (χ ^ p)) (E : Forms k p ≃ₗ[k] (V.I → k))
    (hE : ∀ (R : TestAlgebra k) (g : Points G.val.X R) (ℓ : R →ₗ[k] k) (v : Forms k p),
      E (contract ℓ (act (matrixPoint s R g).val (extend v))) = orbitCoefficient V.inducedAction R g ℓ (E v)) :
    (purePowers k p).map E.toLinearMap = V.socle ∧
    Module.finrank k V.socle = 2 ∧ Module.finrank k (V.I → k) = p + 1 := by
  obtain ⟨hs, _, hn, hr, hd, hmin, _⟩ := nonsplit k p
  let W := purePowers k p
  have hs' : Specs.PrimitiveLine.IsStable V.inducedAction (W.map E.toLinearMap) := by
    apply (stability_iff _ _).2
    intro R g ℓ v hv
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hv
    change orbitCoefficient V.inducedAction R g ℓ (E f) ∈ W.map E.toLinearMap
    rw [← hE R g ℓ f]
    exact Submodule.mem_map.mpr ⟨_, hs R _ (matrixPoint s R g).property ℓ f hf, rfl⟩
  have hn' : W.map E.toLinearMap ≠ ⊥ := by
    intro h
    exact hn (Submodule.map_injective_of_injective E.injective (h.trans (Submodule.map_bot _).symm))
  have hsimple : Specs.InducedSocle.IsSimpleSubmodule V.inducedAction (W.map E.toLinearMap) := by
    refine ⟨hs', hn', ?_⟩
    intro N hN hNW
    by_cases h0 : N = ⊥
    · exact Or.inl h0
    · right
      apply le_antisymm hNW
      have hstable : Stable (N.comap E.toLinearMap) true := by
        intro R _ _ m hm ℓ f hf
        let g := (matrixPoint s (CommAlgCat.of k R)).symm ⟨m, hm⟩
        change E (contract ℓ (act m (extend f))) ∈ N
        have hm' : (matrixPoint s (CommAlgCat.of k R) g).val = m :=
          congrArg Subtype.val ((matrixPoint s (CommAlgCat.of k R)).apply_symm_apply ⟨m, hm⟩)
        rw [← hm']
        have hs := (stability_iff _ _).1 hN (CommAlgCat.of k R) g ℓ (E f) hf
        exact (hE (CommAlgCat.of k R) g ℓ f).symm ▸ hs
      have hne : N.comap E.toLinearMap ≠ ⊥ := by
        intro h
        apply h0
        rw [← Submodule.map_comap_eq_of_surjective E.surjective N, h, Submodule.map_bot]
      exact (Submodule.map_le_iff_le_comap).2 (hmin _ hstable hne)
  have heq := V.socle_unique _ hsimple
  refine ⟨heq, ?_, E.finrank_eq.symm.trans hd⟩
  rw [← heq]
  exact ((Submodule.equivMapOfInjective E.toLinearMap E.injective W).finrank_eq).symm.trans hr

end MarkedInduction

section MarkedFlag

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj MatrixGroups TensorProduct
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections)
open Specs.RankOneFlag (Index plane planeBasis projectiveLine HasCoordinates)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.QuotientEmbedding (Presentation)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.WeylDimension (firstDiagonalCharacter)
open Specs.AmpleFlagWeights (IsHyperplanePullback)
open Specs.ProjectiveSpaces (LineFamily.pullback)
open private planeRepresentation planeLine vectorOfCoordinates vectorOfCoordinates_change from
  LinearAlgebraicGroups.RootData.RankOneFlag
open private matrixPoints_map from LinearAlgebraicGroups.RootData.SpecialLinearDatum
open private matrix_dominant from LinearAlgebraicGroups.Representation.WeylDimension

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {G : AffineAlgebraicGroup k} (s : SpecialMatrixPoints G 2) {P : OppositeBorelPair G}

private theorem secondFrame_hyperplane (Q : Presentation P.negative) (b : BorelProjection P)
    (χ : Character P.torus.group) (c : Q.scheme ≅ projectiveLine k)
    (hc : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ≫ Q.projection ≫ c.hom = secondColumnPoint s R g)
    (hB : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections P.negative ((testSpec k).obj (op R)) ↔
        (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0)
    (hχ : ∀ (R : TestAlgebra k) (g : Points P.negative.group.X R),
      characterValue (b.projection ≫ χ) R g⁻¹ =
        (s.hom.app R (g ≫ P.negative.inclusion.hom.hom)).val ⟨1⟩ ⟨1⟩) :
    IsHyperplanePullback Q b χ c.hom (planeRepresentation k) := by
  refine ⟨secondFrame s, ?_, ?_, ?_⟩
  · intro R g
    refine ⟨?_, secondFrame_injective s R g⟩
    have h := congrArg
      (fun L : Specs.ProjectiveSpaces.LineFamily k (plane k) ((testSpec k).obj (op R)) ↦
        (L.line R (𝟙 _)).submodule)
      ((planeRepresentation k).naturality (g ≫ Q.projection) c.hom)
    simp only [Specs.ProjectiveSpaces.LineFamily.pullback, Category.id_comp] at h
    rw [← h, Category.assoc, hc]
    exact secondColumnPoint_coordinates s R g
  · intro R S a g
    change vectorOfCoordinates S (fun i ↦ (s.hom.app S (mapPoints a g)).val i ⟨1⟩) = _
    rw [matrixPoints_map]
    exact (vectorOfCoordinates_change a _).symm
  · intro R g z
    rw [hχ]
    let y := z ≫ P.negative.inclusion.hom.hom
    have hlow : (matrixPoint s R y) 0 1 = 0 := (hB R y).1 ⟨z, rfl⟩
    have h := secondColumn_lower (matrixPoint s R g) (matrixPoint s R y) hlow
    apply ((planeBasis k).baseChange R).equivFun.injective
    change ((planeBasis k).baseChange R).equivFun
      (((planeBasis k).baseChange R).equivFun.symm (fun i ↦ (s.hom.app R (g * y)).val i ⟨1⟩)) =
      ((planeBasis k).baseChange R).equivFun
        ((s.hom.app R y).val ⟨1⟩ ⟨1⟩ •
          ((planeBasis k).baseChange R).equivFun.symm (fun i ↦ (s.hom.app R g).val i ⟨1⟩))
    rw [map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    funext i
    change (matrixPoint s R (g * y)).val i.down 1 =
      (matrixPoint s R y).val 1 1 * (matrixPoint s R g).val i.down 1
    rw [map_mul]
    exact congrFun (congrArg Subtype.val h) i.down


theorem markedFlagAndSocle : MarkedFlagAndSocle.{u} := by
  intro k _ p _ _ G s
  obtain ⟨T, L, M, B, D, hD, _, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k 1 G s
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition G (negativeDirection B)
  obtain ⟨Bminus, U, hU, hBminus, hχ⟩ := markedBorels B E
  let P := Bminus.pair
  let χ := firstDiagonalCharacter L
  obtain ⟨l, y, hl, hy, _, hpair⟩ := RootData.SpecialLinearDatum.sizeTwoLattices
  have hDom := matrix_dominant B Bminus D hD l y hl hy hpair p
  obtain ⟨V, _⟩ := (SimpleClassification.classification G P U hU).2.2 (χ ^ p) hDom
  obtain ⟨Q⟩ := QuotientEmbedding.quotientEmbedding k G P.negative
  obtain ⟨c, hc⟩ := markedQuotient s Q hBminus
  have hFrame := secondFrame_hyperplane s Q V.projection χ c hc hBminus (hχ V.projection)
  refine ⟨P, χ, U, Q, planeRepresentation k, c, V, hU, ?_, ?_, ?_, hBminus, hFrame, ?_, ?_⟩
  · intro R g
    rw [T.range]
    refine ⟨fun h ↦ ⟨h ⟨0⟩ ⟨1⟩ (by decide), h ⟨1⟩ ⟨0⟩ (by decide)⟩, ?_⟩
    rintro ⟨h₀, h₁⟩ i j hij
    rcases two_index i with rfl | rfl <;> rcases two_index j with rfl | rfl <;> first | contradiction | assumption
  · exact firstDiagonal_value
  · intro R g
    rw [B.matrix]
    constructor
    · intro h
      exact h (by decide : (⟨0⟩ : Index.{u}) < ⟨1⟩)
    · intro h i j hij
      rcases two_index i with rfl | rfl <;> rcases two_index j with rfl | rfl <;>
        first | exact h | simp at hij
  · intro R g
    rw [hc]
    exact secondColumnPoint_coordinates s R g
  · obtain ⟨I, J, hI, hJ, _⟩ := inductionIdentification k p
    obtain ⟨C, hC⟩ := covariantMatrixComparison s V hBminus (hχ V.projection)
    let F := (I.trans J).trans C.symm
    have hF (f : Forms k p) (R : TestAlgebra k) (g : Points G.val.X R) :
        atPoint V.groupIso R g (F f).val =
          aeval (determinantCoordinates (secondColumn (matrixPoint s R g)).val) f.val := by
      rw [← hC]
      change (C (C.symm (J (I f)))).val R (matrixPoint s R g) = _
      rw [LinearEquiv.apply_symm_apply, hJ, hI]
    let E := F.trans V.inducedBasis.equivFun
    have hE (R : TestAlgebra k) (g : Points G.val.X R) (ℓ : R →ₗ[k] k) (v : Forms k p) :
        E (contract ℓ (act (matrixPoint s R g).val (extend v))) =
          Specs.PrimitiveLine.orbitCoefficient V.inducedAction R g ℓ (E v) :=
      intertwines_induction s V F hF R g ℓ v
    obtain ⟨hS, h2, hp⟩ := induction_socle s V E hE
    exact ⟨E, hS, h2, hp, hE⟩

end MarkedFlag


end LinearAlgebraicGroups.Representation.NonsplitSymmetricPower
