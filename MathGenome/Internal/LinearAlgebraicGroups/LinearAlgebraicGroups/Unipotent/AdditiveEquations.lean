import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.AdditiveEquations
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section

open CategoryTheory Coalgebra MvPolynomial TensorProduct
open scoped BigOperators MonomialOrder

namespace LinearAlgebraicGroups.AdditiveEquations

open Specs.AdditiveEquations
open Specs.StandardGroups (HopfOperations)

universe u

variable {k ι : Type u} [Field k]

local notation "A" => MvPolynomial ι k
local notation "E" => ι →₀ ℕ

private def tensorBasis : Module.Basis (E × E) k (A ⊗[k] A) :=
  (basisMonomials ι k).tensorProduct (basisMonomials ι k)

private def tensorCoeff (s t : E) : A ⊗[k] A →ₗ[k] k :=
  (Finsupp.lapply (s, t)).comp (tensorBasis (k := k) (ι := ι)).repr.toLinearMap

@[simp] private theorem tensorCoeff_tmul (s t : E) (f g : A) :
    tensorCoeff s t (f ⊗ₜ[k] g) = f.coeff s * g.coeff t := by
  change (tensorBasis (k := k) (ι := ι)).repr (f ⊗ₜ[k] g) (s, t) = _
  rw [tensorBasis, Module.Basis.tensorProduct_repr_tmul_apply]
  change g.coeff t * f.coeff s = _
  exact mul_comm _ _

private theorem prod_tmul (s : Finset ι) (f g : ι → A) :
    (∏ i ∈ s, f i ⊗ₜ[k] g i) = (∏ i ∈ s, f i) ⊗ₜ[k] (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.TensorProduct.one_def]
  | insert i s hi ih => simp [Finset.prod_insert hi, ih]


private theorem primitive_iff (h : HopfOperations k A) (f : A) :
    IsPrimitivePolynomial h f ↔ h.delta f = (1 : A) ⊗ₜ[k] f + f ⊗ₜ[k] (1 : A) :=
  @Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul k A _ _
    h.hopf.toHopfAlgebraStruct.toBialgebra f _

section Finite

variable [Fintype ι] {h : HopfOperations k (MvPolynomial ι k)}

section Coefficients

variable [DecidableEq ι]

omit [DecidableEq ι] in
private theorem prod_X_pow_univ (v : E) :
    (∏ i, (X i : A) ^ v i) = monomial v 1 := by
  rw [← prod_X_pow_eq_monomial]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp [Finsupp.notMem_support_iff.mp hi]

omit [Fintype ι] [DecidableEq ι] in
private theorem comul_X_pow (hX : HasPrimitiveCoordinates h) (i : ι) (n : ℕ) :
    h.delta ((X i : A) ^ n) =
      ∑ j : Fin (n + 1), (n.choose j : k) • (((X i : A) ^ (j : ℕ)) ⊗ₜ[k] ((X i : A) ^ (n - j))) := by
  rw [map_pow]
  rw [((primitive_iff h _).mp (hX i)), add_comm, add_pow,
    Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (n.choose j : k) • (((X i : A) ^ j) ⊗ₜ[k] ((X i : A) ^ (n - j))))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
    one_pow, mul_one, one_mul]
  rw [Nat.cast_smul_eq_nsmul k, nsmul_eq_mul, mul_comm]

private theorem comul_monomial (hX : HasPrimitiveCoordinates h) (v : E) (a : k) :
    h.delta (monomial v a : A) =
      ∑ j : (i : ι) → Fin (v i + 1),
        (a * ∏ i, ((v i).choose (j i) : k)) •
          ((monomial (Finsupp.equivFunOnFinite.symm fun i => (j i : ℕ)) 1 : A) ⊗ₜ[k]
            monomial (Finsupp.equivFunOnFinite.symm fun i => v i - (j i : ℕ)) 1) := by
  classical
  calc
    _ = a • h.delta (monomial v 1 : A) := by
      rw [← map_smul, ← (monomial v).map_smul, smul_eq_mul, mul_one]
    _ = a • ∏ i, h.delta ((X i : A) ^ v i) := by
      rw [← prod_X_pow_univ]
      exact congrArg (a • ·) (map_prod h.delta _ _)
    _ = _ := by
      simp_rw [comul_X_pow hX, Fintype.prod_sum, Finset.prod_smul, prod_tmul, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro j _
      have left := prod_X_pow_univ (k := k) (Finsupp.equivFunOnFinite.symm fun i => (j i : ℕ))
      have right := prod_X_pow_univ (k := k)
        (Finsupp.equivFunOnFinite.symm fun i => v i - (j i : ℕ))
      simpa only [Finsupp.equivFunOnFinite_symm_apply_apply] using
        congrArg₂ (fun x y : A => (a * ∏ i, ((v i).choose (j i) : k)) • (x ⊗ₜ[k] y)) left right

private theorem tensorCoeff_comul_monomial (hX : HasPrimitiveCoordinates h) (v s t : E) (a : k) :
    tensorCoeff s t (h.delta (monomial v a : A)) =
      if s + t = v then a * ∏ i, ((v i).choose (s i) : k) else 0 := by
  classical
  rw [comul_monomial hX, map_sum]
  simp only [map_smul, tensorCoeff_tmul, coeff_monomial, smul_eq_mul]
  have indices (j : (i : ι) → Fin (v i + 1))
      (hs : Finsupp.equivFunOnFinite.symm (fun i => (j i : ℕ)) = s)
      (ht : Finsupp.equivFunOnFinite.symm (fun i => v i - (j i : ℕ)) = t) : s + t = v := by
    ext i
    have hs' := congrArg (fun x : E => x i) hs
    have ht' := congrArg (fun x : E => x i) ht
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply] at hs' ht'
    simpa only [Finsupp.add_apply, ← hs', ← ht'] using Nat.add_sub_of_le (Nat.le_of_lt_succ (j i).isLt)
  split_ifs with h
  · let j : (i : ι) → Fin (v i + 1) := fun i =>
      ⟨s i, by have h' := congrArg (fun x : E => x i) h; simp only [Finsupp.add_apply] at h'; omega⟩
    have hj : Finsupp.equivFunOnFinite.symm (fun i => (j i : ℕ)) = s := by ext i; simp [j]
    have hj' : Finsupp.equivFunOnFinite.symm (fun i => v i - (j i : ℕ)) = t := by
      ext i
      have h' := congrArg (fun x : E => x i) h
      simp only [Finsupp.add_apply] at h'
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply, j]
      omega
    rw [Finset.sum_eq_single j]
    · simp [hj, hj', j]
    · intro l _ hl
      have hl' : Finsupp.equivFunOnFinite.symm (fun i => (l i : ℕ)) ≠ s := by
        intro he
        apply hl
        funext i
        apply Fin.ext
        simpa only [Finsupp.equivFunOnFinite_symm_apply_apply] using congrArg (fun x : E => x i) he
      simp [hl']
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    split_ifs with hs ht
    · exact (h (indices j hs ht)).elim
    all_goals simp

private theorem tensorCoeff_comul (hX : HasPrimitiveCoordinates h) (f : A) (s t : E) :
    tensorCoeff s t (h.delta f) =
      f.coeff (s + t) * ∏ i, (((s + t) i).choose (s i) : k) := by
  classical
  conv_lhs => rw [f.as_sum]
  simp only [map_sum, tensorCoeff_comul_monomial hX]
  rw [Finset.sum_eq_single (s + t)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    simp [notMem_support_iff.mp h]


end Coefficients

private theorem primitiveSupport (hX : HasPrimitiveCoordinates h) (p : ℕ)
    [CharP k p] [Fact p.Prime] {f : A} (hf : IsPrimitivePolynomial h f)
    (v : E) (hv : v ∈ f.support) :
    ∃ ij : ι × ℕ, v = Finsupp.single ij.1 (p ^ ij.2) := by
  classical
  have mixed (s t : E) (hs : s ≠ 0) (ht : t ≠ 0) :
      f.coeff (s + t) * (∏ i, (((s + t) i).choose (s i) : k)) = 0 := by
    rw [← tensorCoeff_comul hX, ((primitive_iff h f).mp hf)]
    simp [coeff_one, Ne.symm hs, Ne.symm ht]
  have hv' : f.coeff v ≠ 0 := mem_support_iff.mp hv
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    have h0 := congrArg (tensorCoeff (k := k) (ι := ι) 0 0) ((primitive_iff h f).mp hf)
    simp only [tensorCoeff_comul hX, map_add, tensorCoeff_tmul, zero_add,
      Finsupp.zero_apply, Nat.choose_self, Nat.cast_one, Finset.prod_const_one,
      mul_one, coeff_one, ite_true, one_mul] at h0
    exact hv' (by
      apply add_right_cancel (b := f.coeff 0)
      simpa only [zero_add] using h0.symm)
  have hcoord : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv0 (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hcoord
  have split {s t : E} (hst : s + t = v) (hs : s ≠ 0) (ht : t ≠ 0) :
      (∏ j, ((v j).choose (s j) : k)) = 0 := by
    have hz := mixed s t hs ht
    rw [hst] at hz
    exact (mul_eq_zero.mp hz).resolve_left hv'
  have pure : v = Finsupp.single i (v i) := by
    by_contra h
    let s : E := Finsupp.single i (v i)
    have hsv : s ≤ v := Finsupp.single_le_iff.mpr le_rfl
    have hst : s + (v - s) = v := add_tsub_cancel_of_le hsv
    have hs : s ≠ 0 := by simpa [s] using hi
    have ht : v - s ≠ 0 := by
      intro he
      apply h
      simpa only [he, add_zero] using hst.symm
    have hz := split hst hs ht
    have hone (j : ι) : ((v j).choose (s j) : k) = 1 := by
      by_cases hj : j = i
      · subst j; simp [s]
      · simp [s, Finsupp.single_eq_of_ne hj]
    simp only [hone, Finset.prod_const_one, one_ne_zero] at hz
  have hpowers (n : ℕ) (hn : n ∈ Finset.Icc 1 (v i - 1)) :
      (v i).choose n ≡ 0 [MOD p] := by
    have hn0 : n ≠ 0 := by have := Finset.mem_Icc.mp hn; omega
    have hnv : n < v i := by have := Finset.mem_Icc.mp hn; omega
    let s : E := Finsupp.single i n
    let t : E := Finsupp.single i (v i - n)
    have hst : s + t = v := by
      dsimp [s, t]
      rw [← Finsupp.single_add, Nat.add_sub_of_le hnv.le, ← pure]
    have hz := split hst (by simpa [s] using hn0)
      (by
        intro ht
        exact Nat.sub_ne_zero_of_lt hnv (by simpa only [t, Finsupp.single_eq_same,
          Finsupp.zero_apply] using congrArg (fun x : E => x i) ht))
    rw [Finset.prod_eq_single i] at hz
    · rw [show s i = n by simp [s]] at hz
      exact Nat.modEq_zero_iff_dvd.mpr ((CharP.cast_eq_zero_iff k p _).mp hz)
    · intro j _ hj
      simp [s, Finsupp.single_eq_of_ne hj]
    · simp
  refine ⟨(i, multiplicity p (v i)), ?_⟩
  calc
    v = Finsupp.single i (v i) := pure
    _ = _ := congrArg (Finsupp.single i)
      (Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat (Nat.pos_of_ne_zero hi) hpowers)

omit [Fintype ι] in
private theorem primitiveXPow (hX : HasPrimitiveCoordinates h) (p : ℕ)
    [CharP k p] [Fact p.Prime] (i : ι) (j : ℕ) :
    IsPrimitivePolynomial h ((X i : A) ^ (p ^ j)) := by
  rw [primitive_iff]
  let : CharP (A ⊗[k] A) p :=
    charP_of_injective_algebraMap (algebraMap k (A ⊗[k] A)).injective p
  rw [map_pow]
  rw [((primitive_iff h _).mp (hX i)), add_pow_char_pow _ _ p,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow]

/-- The primitive elements of an additive polynomial Hopf algebra in characteristic `p`. -/
theorem primitivePolynomials : PrimitivePolynomials.{u} := by
  intro k ι _ _ p _ _ h hX f
  classical
  constructor
  · intro hf
    let exponent (v : f.support) : ι × ℕ := (primitiveSupport hX p hf v v.prop).choose
    have hexp (v : f.support) : v.val =
        Finsupp.single (exponent v).1 (p ^ (exponent v).2) :=
      (primitiveSupport hX p hf v v.prop).choose_spec
    let powers : (ι × ℕ) → MvPolynomial ι k := fun ij => X ij.1 ^ (p ^ ij.2)
    let c : (ι × ℕ) →₀ k :=
      ∑ v ∈ f.support.attach, Finsupp.single (exponent v) (f.coeff v)
    refine ⟨c, ?_⟩
    change f = Finsupp.linearCombination k powers c
    rw [show c = _ from rfl, map_sum]
    simp only [Finsupp.linearCombination_single, powers, X_pow_eq_monomial, ← hexp,
      ← map_smul, smul_eq_mul, mul_one]
    rw [Finset.sum_attach f.support (fun v => monomial v (f.coeff v))]
    exact f.as_sum
  · rintro ⟨c, rfl⟩
    let : Coalgebra k (MvPolynomial ι k) := h.hopf.toHopfAlgebraStruct.toBialgebra.toCoalgebra
    let P := Coalgebra.skewPrimitive k (1 : MvPolynomial ι k) 1
    change c.sum _ ∈ P
    exact Submodule.sum_mem P fun ij _ =>
      Submodule.smul_mem P _ (primitiveXPow hX p ij.1 ij.2)


omit [Fintype ι] in
private theorem coeff_zero_of_mem_hopfIdeal (hX : HasPrimitiveCoordinates h)
    (I : Ideal A) [hI : letI := h.hopf; I.IsHopfIdeal k] {f : A} (hf : f ∈ I) : f.coeff 0 = 0 := by
  have hε : h.epsilon = aeval (fun _ : ι => (0 : k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [aeval_X]
    exact @Bialgebra.counit_eq_zero_of_comul_eq_tmul_add_tmul k A _ _
      h.hopf.toHopfAlgebraStruct.toBialgebra _ _ ((primitive_iff h _).mp (hX i))
  calc
    f.coeff 0 = aeval (fun _ : ι => (0 : k)) f := by
      rw [aeval_zero', Algebra.algebraMap_self_apply]
      rfl
    _ = h.epsilon f := by rw [← hε]
    _ = 0 := hI.counit_eq_zero hf

/-- An exponent is standard for an ideal if it is absent from its leading monomials. -/
private def IsStandard (m : MonomialOrder ι) (I : Ideal A) (s : E) : Prop :=
  ∀ g ∈ I, g ≠ 0 → m.degree g ≠ s

private def standardSubspace (m : MonomialOrder ι) (I : Ideal A) : Submodule k A where
  carrier := {f | ∀ s ∈ f.support, IsStandard m I s}
  zero_mem' := by simp
  add_mem' := by
    classical
    intro f g hf hg s hs
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hf s hs
    · exact hg s hs
  smul_mem' := by
    intro a f hf s hs
    apply hf s
    contrapose! hs
    rw [notMem_support_iff] at hs ⊢
    simp [hs]

omit [Fintype ι] in
private theorem monomial_mem_standardSubspace (m : MonomialOrder ι) (I : Ideal A) {s : E}
    (hs : IsStandard m I s) : monomial s (1 : k) ∈ standardSubspace m I := by
  classical
  change ∀ t ∈ (monomial s (1 : k)).support, IsStandard m I t
  intro t ht
  have he : t = s := by simpa [support_monomial, one_ne_zero] using ht
  exact he ▸ hs

omit [Fintype ι] in
/-- The quotient map admits a linear left inverse on standard monomials. -/
private theorem standardMonomialSection (m : MonomialOrder ι) (I : Ideal A) :
    ∃ L : (A ⧸ I) →ₗ[k] A, ∀ s, IsStandard m I s →
      L (Ideal.Quotient.mk I (monomial s 1)) = monomial s 1 := by
  let V := standardSubspace m I
  let q := (Ideal.Quotient.mkₐ k I).toLinearMap
  let qV := q.comp V.subtype
  have hker : LinearMap.ker qV = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    by_contra h
    have hmem : (f : A) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hf
    have hstd : ∀ s ∈ f.val.support, IsStandard m I s := f.prop
    exact hstd (m.degree f.val) (m.degree_mem_support h) f.val hmem h rfl
  obtain ⟨L, hL⟩ := qV.exists_leftInverse_of_injective hker
  refine ⟨V.subtype.comp L, fun s hs => ?_⟩
  let a : V := ⟨monomial s 1, monomial_mem_standardSubspace m I hs⟩
  exact congrArg Subtype.val (LinearMap.congr_fun hL a)

omit [Fintype ι] in
private theorem tensor_eq_zero_of_standard (m : MonomialOrder ι) (I : Ideal A)
    (z : A ⊗[k] A)
    (hz : ∀ s t, tensorCoeff s t z ≠ 0 → IsStandard m I s ∧ IsStandard m I t)
    (hqz : let q := (Ideal.Quotient.mkₐ k I).toLinearMap; TensorProduct.map q q z = 0) :
    z = 0 := by
  classical
  let q := (Ideal.Quotient.mkₐ k I).toLinearMap
  obtain ⟨L, hL⟩ := standardMonomialSection m I
  let T := TensorProduct.map (L.comp q) (L.comp q)
  have hTz : T z = 0 := by
    change (TensorProduct.map (L.comp q) (L.comp q)) z = 0
    rw [TensorProduct.map_comp, LinearMap.comp_apply, hqz, map_zero]
  suffices T z = z by rw [← this, hTz]
  let B := tensorBasis (k := k) (ι := ι)
  have hexpand : (∑ x ∈ (B.repr z).support, B.repr z x • B x) = z := by
    exact B.linearCombination_repr z
  calc
    T z = T (∑ x ∈ (B.repr z).support, B.repr z x • B x) := congrArg T hexpand.symm
    _ = ∑ x ∈ (B.repr z).support, B.repr z x • B x := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      rintro ⟨s, t⟩ hst
      have hC : tensorCoeff s t z ≠ 0 := Finsupp.mem_support_iff.mp hst
      obtain ⟨hs, ht⟩ := hz s t hC
      rw [map_smul]
      congr 1
      simp only [B, tensorBasis, Module.Basis.tensorProduct_apply, coe_basisMonomials]
      change TensorProduct.map (L.comp q) (L.comp q) _ = _
      rw [TensorProduct.map_tmul]
      exact congrArg₂ (fun a b : A => a ⊗ₜ[k] b) (hL s hs) (hL t ht)
    _ = z := hexpand

private theorem primitiveOfStandardDivisors (hX : HasPrimitiveCoordinates h)
    (m : MonomialOrder ι) (I : Ideal A) [hI : letI := h.hopf; I.IsHopfIdeal k] {f : A} (hf : f ∈ I)
    (hstd : ∀ v ∈ f.support, ∀ s t : E, s + t = v → s ≠ 0 → t ≠ 0 →
      IsStandard m I s ∧ IsStandard m I t) : IsPrimitivePolynomial h f := by
  classical
  rw [primitive_iff, ← sub_eq_zero]
  apply tensor_eq_zero_of_standard m I
  · intro s t hst
    simp only [map_sub, map_add, tensorCoeff_tmul, tensorCoeff_comul hX, coeff_one] at hst
    have hc := coeff_zero_of_mem_hopfIdeal hX I hf
    have hs : s ≠ 0 := by
      rintro rfl
      simp [hc] at hst
    have ht : t ≠ 0 := by
      rintro rfl
      simp [hc, eq_comm] at hst
    apply hstd (s + t) _ s t rfl hs ht
    apply mem_support_iff.mpr
    contrapose! hst
    simp [hst, Ne.symm hs, Ne.symm ht]
  · let q := (Ideal.Quotient.mkₐ k I).toLinearMap
    have hq : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
    have hc : TensorProduct.map q q (h.delta f) = 0 :=
      hI.map_mkQ_comul_eq_zero hf
    change TensorProduct.map q q _ = 0
    simp [hc, hq, TensorProduct.map_tmul]

private theorem spanPrimitive (hX : HasPrimitiveCoordinates h)
    (m : MonomialOrder ι) (I : Ideal A) [hI : letI := h.hopf; I.IsHopfIdeal k] :
    I = Ideal.span {f | f ∈ I ∧ IsPrimitivePolynomial h f} := by
  classical
  let J : Ideal A := Ideal.span {f | f ∈ I ∧ IsPrimitivePolynomial h f}
  have hJI : J ≤ I := Ideal.span_le.mpr fun _ h => h.1
  apply le_antisymm _ hJI
  intro f hf
  have wf : WellFounded (fun a b : A => m.degree a ≺[m] m.degree b) :=
    (wellFounded_lt (α := m.syn)).onFun
  revert hf
  induction f using wf.induction with
  | h f ih =>
    intro hf
    by_contra hfJ
    let B : Set A := {b | b ∈ I ∧ b ≠ 0 ∧ m.degree b ≺[m] m.degree f}
    obtain ⟨g, r, hfr, hg, hr⟩ := m.div_set (B := B)
      (fun b hb => isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hb.2.1)) f
    let q := Finsupp.linearCombination A (fun b : B => (b : A)) g
    have hqJ : q ∈ J := by
      dsimp [q]
      rw [Finsupp.linearCombination_apply]
      exact Submodule.sum_mem J fun b _ => J.smul_mem _ (ih b b.prop.2.2 b.prop.1)
    have hrs : r ∈ I := by
      rw [show r = f - q by rw [hfr]; exact (add_sub_cancel_left q r).symm]
      exact I.sub_mem hf (hJI hqJ)
    have hqdeg : m.degree q ≼[m] m.degree f := by
      dsimp [q]
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      exact m.degree_sum_le.trans (Finset.sup_le fun b _ => by
        simpa [smul_eq_mul, mul_comm] using hg b)
    have hrdeg : m.degree r ≼[m] m.degree f := by
      have heq : r = f - q := by
        rw [hfr]
        exact (add_sub_cancel_left q r).symm
      rw [heq, sub_eq_add_neg]
      refine m.degree_add_le.trans (sup_le le_rfl ?_)
      simpa using hqdeg
    have pr : IsPrimitivePolynomial h r := by
      refine primitiveOfStandardDivisors hX m I hrs ?_
      intro v hv s t hst hs ht
      have hvs : v ≼[m] m.degree f := by
        exact (m.le_degree hv).trans hrdeg
      have hsv : s < v := by rw [← hst]; exact lt_add_of_pos_right _ (bot_lt_iff_ne_bot.mpr ht)
      have htv : t < v := by rw [← hst]; exact lt_add_of_pos_left _ (bot_lt_iff_ne_bot.mpr hs)
      have standard (a : E) (ha : a < v) : IsStandard m I a := by
        intro b hb hb0 hba
        apply hr v hv b
        · exact ⟨hb, hb0, hba ▸ (m.toSyn_strictMono ha).trans_le hvs⟩
        · exact hba.symm ▸ ha.le
      exact ⟨standard s hsv, standard t htv⟩
    have hrJ : r ∈ J := Ideal.subset_span (show r ∈ {f | f ∈ I ∧ IsPrimitivePolynomial h f} from ⟨hrs, pr⟩)
    exact hfJ (hfr ▸ J.add_mem hqJ hrJ)

/-- Every Hopf ideal has a finite set of primitive additive generators. -/
theorem hopfIdealAdditiveGenerators : HopfIdealAdditiveGenerators.{u} := by
  intro k ι _ _ p _ _ h
  let := h.hopf
  intro hX I _
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let : WellFoundedGT ι := Finite.wellFounded_of_trans_of_irrefl (· > ·)
  have hspan := spanPrimitive hX (MonomialOrder.degLex (σ := ι)) I
  obtain ⟨T, hT⟩ := (isNoetherianRing_iff_ideal_fg _).mp
    (inferInstance : IsNoetherianRing (MvPolynomial ι k)) I
  let P := {f | f ∈ I ∧ IsPrimitivePolynomial h f}
  have hT' : (T : Set (MvPolynomial ι k)) ⊆ Ideal.span P := by
    rw [← hspan, ← hT]
    exact Ideal.subset_span
  obtain ⟨S, hS, hTS⟩ := Submodule.subset_span_finite_of_subset_span
    (R := MvPolynomial ι k) hT'
  refine ⟨S, le_antisymm ?_ (Ideal.span_le.mpr fun f hf => (hS hf).1), ?_⟩
  · rw [← hT]
    exact Ideal.span_le.mpr hTS
  · intro f hf
    have hp := (hS hf).2
    exact ⟨hp, (primitivePolynomials k ι p h hX f).mp hp⟩


/-- The defining equations of a closed subgroup in the additive vector group. -/
theorem closedVectorSubgroupEquations : ClosedVectorSubgroupEquations.{u} := by
  intro k ι _ _ p _ _ h
  let := h.hopf
  intro hX H i hi
  let B := CommHopfAlgCat.of k (MvPolynomial ι k)
  obtain ⟨I, ⟨hI, e, he⟩, _⟩ := (closedSubgroupClassification k B H i).mp hi
  let := hI
  obtain ⟨S, hS, hprim⟩ := hopfIdealAdditiveGenerators k ι p h hX I
  subst I
  exact ⟨S, fun f hf => (hprim f hf).2, hI, e, he⟩

end Finite

/-- A finite subgroup of the additive line has a single monic nonzero additive equation. -/
theorem finiteAdditiveSubgroupEquation : FiniteAdditiveSubgroupEquation.{u} := by
  intro k _ p _ _ h
  let := h.hopf
  intro hX I _ _
  classical
  let R := MvPolynomial PUnit.{u + 1} k
  let e := MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}
  have hI : ∃ f : R, f ∈ I ∧ f ≠ 0 := by
    by_contra! h0
    have hbot : I = ⊥ := le_antisymm (fun f hf => h0 f hf) bot_le
    subst I
    exact Polynomial.not_finite
      (Module.Finite.equiv ((AlgEquiv.quotientBot k R).trans e).toLinearEquiv)
  let m := MonomialOrder.lex (σ := PUnit.{u + 1})
  have wf : WellFounded (fun a b : R => m.degree a ≺[m] m.degree b) :=
    (wellFounded_lt (α := m.syn)).onFun
  obtain ⟨f, hf, hmin⟩ := wf.has_min {f : R | f ∈ I ∧ f ≠ 0} hI
  have hfI : f ∈ I := hf.1
  have hf0 : f ≠ 0 := hf.2
  have hprim : IsPrimitivePolynomial h f := by
    refine primitiveOfStandardDivisors hX m I hfI ?_
    intro v hv s t hst hs ht
    have hvdeg := m.le_degree hv
    have hsv : s < v := by rw [← hst]; exact lt_add_of_pos_right _ (bot_lt_iff_ne_bot.mpr ht)
    have htv : t < v := by rw [← hst]; exact lt_add_of_pos_left _ (bot_lt_iff_ne_bot.mpr hs)
    have std (a : PUnit.{u + 1} →₀ ℕ) (ha : a < v) : IsStandard m I a := by
      intro b hb hb0 hba
      apply hmin b ⟨hb, hb0⟩
      rw [hba]
      exact (m.toSyn_strictMono ha).trans_le hvdeg
    exact ⟨std s hsv, std t htv⟩
  have hspan : I = Ideal.span {f} := by
    apply le_antisymm _ ((Ideal.span_singleton_le_iff_mem I).mpr hfI)
    intro g hg
    obtain ⟨q, r, hgr, _, hr⟩ :=
      m.div_single (isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr hf0)) g
    have hr0 : r = 0 := by
      by_contra hr0
      have hre : r = g - q * f := by rw [hgr]; exact (add_sub_cancel_left _ _).symm
      have hrI : r ∈ I := by rw [hre]; exact I.sub_mem hg (I.mul_mem_left q hfI)
      have hle : m.degree f ≼[m] m.degree r := le_of_not_gt (hmin r ⟨hrI, hr0⟩)
      apply hr _ (m.degree_mem_support hr0)
      have hnat := MonomialOrder.lex_le_iff_of_unique.mp hle
      intro i
      simpa only [Unique.eq_default i] using hnat
    exact Ideal.mem_span_singleton.mpr ⟨q, by simpa [hr0, mul_comm] using hgr⟩
  let c : k := (e f).leadingCoeff⁻¹
  have he0 : e f ≠ 0 := fun hzero => hf0 (e.injective (by simpa using hzero))
  have hc : c ≠ 0 := inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr he0)
  let g : R := c • f
  have hmonic : (e g).Monic := by
    change (e (c • f)).Monic
    rw [map_smul, Algebra.smul_def, Polynomial.algebraMap_apply, mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv he0
  have hspan' : I = Ideal.span {g} := by
    have hg : g = f * C c := by
      change c • f = _
      rw [smul_eq_C_mul, mul_comm]
    rw [hspan, hg, Ideal.span_singleton_mul_right_unit
      (IsUnit.map C (isUnit_iff_ne_zero.mpr hc))]
  refine ⟨g, hspan', ?_, fun hg => hmonic.ne_zero (by rw [hg, map_zero]), hmonic⟩
  apply (primitivePolynomials k PUnit.{u + 1} p h hX g).mp
  rw [primitive_iff]
  change h.delta (c • f) = _
  rw [map_smul, (primitive_iff h f).mp hprim, smul_add, tmul_smul, smul_tmul']
  rfl


/-- The finite closed subgroup and the equation define the same subgroup scheme. -/
theorem finiteAdditiveLineSubgroupEquation : FiniteAdditiveLineSubgroupEquation.{u} := by
  intro k _ p _ _ h
  let := h.hopf
  intro B Hprim H i hi hfin
  let R := MvPolynomial PUnit.{u + 1} k
  obtain ⟨I, ⟨hI, e, he⟩, _⟩ := (closedSubgroupClassification k B H i).mp hi
  let := hI
  let S := specGroup (hopfQuotient B I)
  have hcomp : e.inv.hom.hom.left ≫ H.X.hom = S.X.hom :=
    Over.w e.inv.hom.hom
  let : IsIso e.inv.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.inv)
    infer_instance
  have hfin' : AlgebraicGeometry.IsFinite S.X.hom := by
    rw [← hcomp]
    infer_instance
  let : Module.Finite k (R ⧸ I) := by
    change AlgebraicGeometry.IsFinite
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ I)))) at hfin'
    exact RingHom.finite_algebraMap.mp (AlgebraicGeometry.IsFinite.SpecMap_iff _ |>.mp hfin')
  obtain ⟨f, hspan, hf, hf0, hmonic⟩ := finiteAdditiveSubgroupEquation k p h Hprim I
  subst I
  exact ⟨f, hf, hf0, hmonic, hI, e, he⟩

end LinearAlgebraicGroups.AdditiveEquations
