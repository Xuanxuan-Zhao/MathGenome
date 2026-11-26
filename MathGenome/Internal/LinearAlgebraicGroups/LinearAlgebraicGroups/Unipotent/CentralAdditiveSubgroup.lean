import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralAdditiveSubgroup
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.KilledByPVectorEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.AdditiveEquations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Trace.Basic

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralKilledByPCurves
open AlgebraicGeometry CategoryTheory Opposite Polynomial
open scoped CategoryTheory.MonObj Classical TensorProduct

universe u

namespace LinearAlgebraicGroups.Unipotent

noncomputable section

open Specs (AffineAlgebraicGroup GroupScheme)
open Specs.Unipotent
open Specs.AdditiveEquations

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

private def SupportedOnPowers (p : ℕ) (f : Polynomial k) : Prop :=
  ∀ n, (¬ ∃ j, n = p ^ j) → f.coeff n = 0

private theorem coeff_pow_char {R : Type u} [CommRing R] [ExpChar R p]
    (f : Polynomial R) (m n : ℕ) :
    (f ^ (p ^ m)).coeff n =
      if p ^ m ∣ n then f.coeff (n / p ^ m) ^ (p ^ m) else 0 := by
  rw [← map_iterateFrobenius_expand p, coeff_map, coeff_expand (pow_pos (Fact.out : p.Prime).pos _)]
  split_ifs <;> simp [iterateFrobenius_def, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

/-- Keep the coefficients with degree `e * p^j` and reindex them by `p^j`. -/
private def selectPowers (p e : ℕ) (f : Polynomial k) : Polynomial k :=
  Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff ((Polynomial.contract e f).toFinsupp.coeff.filter
      (fun n ↦ ∃ j, n = p ^ j)))

omit [Fact p.Prime] [CharP k p] in
private theorem coeff_selectPowers {e : ℕ} (he : e ≠ 0) (f : Polynomial k) (n : ℕ) :
    (selectPowers p e f).coeff n = if ∃ j, n = p ^ j then f.coeff (n * e) else 0 := by
  classical
  rw [show (selectPowers p e f).coeff n =
      if ∃ j, n = p ^ j then (Polynomial.contract e f).coeff n else 0 by
    simp only [selectPowers, Finsupp.filter_apply, coeff_ofFinsupp]
    rfl]
  rw [Polynomial.coeff_contract he]

private def selectPowersLinear (p : ℕ) {e : ℕ} (he : e ≠ 0) :
    Polynomial k →ₗ[k] Polynomial k where
  toFun := selectPowers p e
  map_add' f g := by
    ext n
    simp only [coeff_selectPowers (p := p) he, coeff_add]
    split_ifs <;> simp
  map_smul' c f := by
    ext n
    simp only [coeff_selectPowers (p := p) he, coeff_smul, RingHom.id_apply]
    split_ifs <;> simp

private theorem selectPowers_pow {e : ℕ} (he : e ≠ 0) (hp : ¬ p ∣ e)
    (f : Polynomial k) (m : ℕ) :
    selectPowers p e (f ^ (p ^ m)) = selectPowers p e f ^ (p ^ m) := by
  classical
  let : ExpChar k p := ExpChar.prime Fact.out
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp
  ext n
  rw [coeff_selectPowers he, coeff_pow_char, coeff_pow_char]
  have hd : p ^ m ∣ n * e ↔ p ^ m ∣ n := (hcop.pow_left m).dvd_mul_right
  by_cases hn : ∃ j, n = p ^ j
  · rw [ite_eq_left hn]
    by_cases hdiv : p ^ m ∣ n
    · rw [ite_eq_left (hd.mpr hdiv), ite_eq_left hdiv, coeff_selectPowers he]
      obtain ⟨j, rfl⟩ := hn
      obtain ⟨r, hr, hquot⟩ := (Nat.dvd_prime_pow Fact.out).mp
        (show p ^ j / p ^ m ∣ p ^ j from ⟨p ^ m, Nat.div_mul_cancel hdiv |>.symm⟩)
      rw [ite_eq_left ⟨r, hquot⟩]
      congr 2
      obtain ⟨d, h⟩ := hdiv
      rw [h, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos (Fact.out : p.Prime).pos _),
        Nat.mul_div_cancel_left _ (pow_pos (Fact.out : p.Prime).pos _)]
    · rw [ite_eq_right (mt hd.mp hdiv), ite_eq_right hdiv]
  · rw [ite_eq_right hn]
    by_cases hdiv : p ^ m ∣ n
    · rw [ite_eq_left hdiv, coeff_selectPowers he, ite_eq_right, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
      rintro ⟨j, hj⟩
      apply hn
      exact ⟨j + m, by rw [pow_add, ← hj, Nat.div_mul_cancel hdiv]⟩
    · rw [ite_eq_right hdiv]

section Trace

variable {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

private theorem trace_pow (x : K) (m : ℕ) :
    Algebra.trace k K (x ^ (p ^ m)) = (Algebra.trace k K x) ^ (p ^ m) := by
  let : ExpChar k p := ExpChar.prime Fact.out
  let : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  apply (algebraMap k K).injective
  rw [map_pow (algebraMap k K), trace_eq_sum_automorphisms, trace_eq_sum_automorphisms]
  classical
  simpa only [iterateFrobenius_def, map_pow] using
    (_root_.map_sum (iterateFrobenius K p m) (fun σ : Gal(K/k) ↦ σ x) Finset.univ).symm

private theorem exists_trace_mul_pow_ne_zero {c : K} (hc : c ≠ 0) (m : ℕ) :
    ∃ a : K, Algebra.trace k K (c * a ^ (p ^ m)) ≠ 0 := by
  let : ExpChar k p := ExpChar.prime Fact.out
  by_contra! h
  have hspan := Field.span_map_pow_expChar_pow_eq_top_of_isSeparable
    (F := k) (E := K) (v := id) p m (by simp)
  apply hc
  apply (traceForm_nondegenerate k K).1 c
  intro b
  have hker : Submodule.span k (Set.range (fun a : K ↦ a ^ (p ^ m))) ≤
      LinearMap.ker (Algebra.traceForm k K c) :=
    Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact h a)
  exact hker (hspan.symm ▸ Submodule.mem_top)

private def tracePolynomial : Polynomial K →ₗ[k] Polynomial k where
  toFun f := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (f.toFinsupp.coeff.mapRange (Algebra.trace k K) (map_zero _)))
  map_add' f g := by ext n; simp [Polynomial.coeff_ofFinsupp, coeff_add]
  map_smul' c f := by ext n; simp [Polynomial.coeff_ofFinsupp, coeff_smul]

omit [FiniteDimensional k K] [IsGalois k K] in
@[simp] private theorem coeff_tracePolynomial (f : Polynomial K) (n : ℕ) :
    (tracePolynomial (k := k) f).coeff n = Algebra.trace k K (f.coeff n) := rfl

private theorem tracePolynomial_pow (f : Polynomial K) (m : ℕ) :
    tracePolynomial (k := k) (f ^ (p ^ m)) = tracePolynomial f ^ (p ^ m) := by
  let : ExpChar k p := ExpChar.prime Fact.out
  let : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  ext n
  rw [coeff_tracePolynomial, coeff_pow_char, coeff_pow_char]
  split_ifs <;> simp [trace_pow]

private theorem coeff_aeval_scale (a : K) (f : Polynomial K) (n : ℕ) :
    (aeval (R := K) (C a * X) f).coeff n = f.coeff n * a ^ n := by
  classical
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [coeff_add, hf, hg, add_mul]
  | monomial m c =>
    rw [aeval_monomial, mul_pow, ← C.map_pow, Polynomial.algebraMap_eq,
      ← mul_assoc, ← C.map_mul, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp

/-- Project to one class of exponents, scale the parameter, and take coefficientwise trace. -/
private theorem traceExtract {ix : Type u} (v : ix → Polynomial K)
    (h : ∃ i n, n ≠ 0 ∧ (v i).coeff n ≠ 0) :
    ∃ T : Polynomial K →ₗ[k] Polynomial k,
      (∀ f m, T (f ^ (p ^ m)) = T f ^ (p ^ m)) ∧
      (∀ f, SupportedOnPowers p (T f)) ∧ ∃ i, T (v i) ≠ 0 := by
  classical
  obtain ⟨i, n, hn, hc⟩ := h
  obtain ⟨m, e, he, hne⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
  have he0 : e ≠ 0 := fun he0 ↦ he (he0 ▸ dvd_zero _)
  obtain ⟨a, ha⟩ := exists_trace_mul_pow_ne_zero (k := k) (p := p) hc m
  let S := (aeval (R := K) (C a * X)).toLinearMap.restrictScalars k
  let T := (tracePolynomial (k := k)).comp (S.comp ((selectPowersLinear (k := K) p he0).restrictScalars k))
  have hcoeff (f : Polynomial K) (n : ℕ) :
      (T f).coeff n =
        Algebra.trace k K ((selectPowers p e f).coeff n * a ^ n) := by
    change (tracePolynomial (k := k) (aeval (R := K) (C a * X) (selectPowers p e f))).coeff n = _
    rw [coeff_tracePolynomial, coeff_aeval_scale]
  refine ⟨T, ?_, ?_, i, ?_⟩
  · intro f j
    let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    change tracePolynomial (k := k) (aeval (R := K) (C a * X) (selectPowers p e (f ^ (p ^ j)))) = _
    rw [selectPowers_pow he0 he, map_pow, tracePolynomial_pow]
    rfl
  · intro f n hn
    simp [hcoeff, coeff_selectPowers he0, hn]
  · intro hzero
    have hz := congrArg (fun f : Polynomial k ↦ f.coeff (p ^ m)) hzero
    rw [hcoeff, coeff_selectPowers he0, ite_eq_left ⟨m, rfl⟩, ← hne, coeff_zero] at hz
    exact ha hz

end Trace

omit [Fact p.Prime] [CharP k p] in
private theorem map_additive_equation {ix R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (T : R →ₗ[k] S)
    (hT : ∀ (f : R) (m : ℕ), T (f ^ (p ^ m)) = T f ^ (p ^ m))
    (v : ix → R) {f : MvPolynomial ix k} (hf : IsAdditivePolynomial p f) :
    T (MvPolynomial.aeval (R := k) v f) = MvPolynomial.aeval (T ∘ v) f := by
  obtain ⟨c, rfl⟩ := hf
  simp only [Finsupp.sum, map_sum, map_smul, map_pow, MvPolynomial.aeval_X, hT, Function.comp_apply]

omit [Fact p.Prime] [CharP k p] in
private theorem SupportedOnPowers.degree_eq {f : Polynomial k}
    (hf : SupportedOnPowers p f) (h : f ≠ 0) :
    ∃ j, f.natDegree = p ^ j := by
  by_contra! hn
  exact (leadingCoeff_ne_zero.mpr h) (hf _ (by simpa using hn))

omit [Fact p.Prime] [CharP k p] in
private theorem SupportedOnPowers.monomial (j : ℕ) (a : k) :
    SupportedOnPowers p (C a * X ^ (p ^ j)) := by
  intro n hn
  rw [coeff_C_mul_X_pow, ite_eq_right (fun e ↦ hn ⟨j, e⟩)]

omit [Fact p.Prime] [CharP k p] in
private theorem SupportedOnPowers.add {f g : Polynomial k}
    (hf : SupportedOnPowers p f) (hg : SupportedOnPowers p g) :
    SupportedOnPowers p (f + g) := by
  intro n hn
  rw [coeff_add, hf n hn, hg n hn, add_zero]

omit [Fact p.Prime] [CharP k p] in
private theorem SupportedOnPowers.sub {f g : Polynomial k}
    (hf : SupportedOnPowers p f) (hg : SupportedOnPowers p g) :
    SupportedOnPowers p (f - g) := by
  intro n hn
  rw [coeff_sub, hf n hn, hg n hn, sub_self]

private theorem SupportedOnPowers.coeff_C_mul_pow {f : Polynomial k}
    (hf : SupportedOnPowers p f) (a : k) (m : ℕ) :
    SupportedOnPowers p (C a * f ^ (p ^ m)) := by
  let : ExpChar k p := ExpChar.prime Fact.out
  intro n hn
  rw [coeff_C_mul, coeff_pow_char]
  split_ifs with hd
  · rw [hf _ (fun ⟨j, hj⟩ ↦ hn ⟨j + m, by rw [pow_add, ← hj, Nat.div_mul_cancel hd]⟩),
      zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), mul_zero]
  · rw [mul_zero]

private theorem aeval_injective_of_natDegree_ne_zero {g : Polynomial k} (hg : g.natDegree ≠ 0) :
    Function.Injective (aeval (R := k) g) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have hdeg := congrArg natDegree hf
  rw [← comp_eq_aeval, natDegree_comp, natDegree_zero, mul_eq_zero] at hdeg
  rw [eq_C_of_natDegree_eq_zero (hdeg.resolve_right hg)] at hf ⊢
  simpa using hf

/-- Divide additive polynomials by one of least degree in the coordinate image. -/
private theorem reparametrize {ix : Type u} (v : ix → Polynomial k)
    (hv : ∀ i, SupportedOnPowers p (v i)) (hnonzero : ∃ i, v i ≠ 0) :
    ∃ q : ix → Polynomial k, (∀ i, SupportedOnPowers p (q i)) ∧
      Function.Surjective (MvPolynomial.aeval (R := k) q) ∧
      ∃ g : Polynomial k, Function.Injective (aeval (R := k) g) ∧ ∀ i, aeval (R := k) g (q i) = v i := by
  classical
  let B := (MvPolynomial.aeval (R := k) v).range
  let P (n : ℕ) := ∃ g : Polynomial k,
    g ∈ B ∧ SupportedOnPowers p g ∧ g ≠ 0 ∧ g.natDegree = n
  have hvB (i : ix) : v i ∈ B := ⟨MvPolynomial.X i, MvPolynomial.aeval_X v i⟩
  have hex : ∃ n, P n := by
    obtain ⟨i, hi⟩ := hnonzero
    exact ⟨_, v i, hvB i, hv i, hi, rfl⟩
  obtain ⟨g, hgB, hg, hg0, hmin⟩ := Nat.find_spec hex
  obtain ⟨l, hl⟩ := hg.degree_eq hg0
  have hgpos : g.natDegree ≠ 0 := by rw [hl]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hdiv : ∀ x : Polynomial k, x ∈ B → SupportedOnPowers p x →
      ∃ q : Polynomial k, SupportedOnPowers p q ∧ aeval (R := k) g q = x := by
    intro x
    induction x using (measure (natDegree : Polynomial k → ℕ)).wf.induction with
    | h x ih =>
      intro hxB hx
      by_cases hx0 : x = 0
      · exact ⟨0, fun n _ ↦ coeff_zero n, by simp [hx0]⟩
      obtain ⟨m, hm⟩ := hx.degree_eq hx0
      have hle : l ≤ m := by
        apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
        rw [← hl, ← hm, hmin]
        exact Nat.find_min' hex ⟨x, hxB, hx, hx0, rfl⟩
      let j := m - l
      let a := x.leadingCoeff / g.leadingCoeff ^ (p ^ j)
      have hden : g.leadingCoeff ^ (p ^ j) ≠ 0 := pow_ne_zero _ (leadingCoeff_ne_zero.mpr hg0)
      have ha : a ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hx0) hden
      let y := C a * g ^ (p ^ j)
      have hyB : y ∈ B := B.mul_mem (B.algebraMap_mem a) (B.pow_mem hgB _)
      have hyd : y.natDegree = x.natDegree := by
        dsimp [y]
        rw [natDegree_C_mul ha, natDegree_pow, hl, hm, ← pow_add]
        congr 1
        exact Nat.sub_add_cancel hle
      have hyl : y.leadingCoeff = x.leadingCoeff := by
        rw [show y = C a * g ^ (p ^ j) from rfl,
          leadingCoeff_C_mul_of_isUnit ha.isUnit, leadingCoeff_pow, div_mul_cancel₀ _ hden]
      let r := x - y
      have hr : SupportedOnPowers p r := hx.sub (hg.coeff_C_mul_pow a j)
      have hrB : r ∈ B := B.sub_mem hxB hyB
      have hrd : r.natDegree < x.natDegree := by
        by_cases hr0 : r = 0
        · rw [hr0, natDegree_zero, hm]; exact pow_pos (Fact.out : p.Prime).pos _
        apply (natDegree_lt_iff_degree_lt hr0).mpr
        rw [← degree_eq_natDegree hx0]
        apply degree_sub_lt_left _ hx0 hyl.symm
        have hy0 : y ≠ 0 := leadingCoeff_ne_zero.mp (hyl ▸ leadingCoeff_ne_zero.mpr hx0)
        rw [degree_eq_natDegree hx0, degree_eq_natDegree hy0, hyd]
      obtain ⟨q, hq, hqr⟩ := ih r hrd hrB hr
      refine ⟨q + C a * X ^ (p ^ j), hq.add (.monomial j a), ?_⟩
      simp only [map_add, map_mul, aeval_C, map_pow, aeval_X, hqr]
      change x - y + y = x
      exact sub_add_cancel _ _
  choose q hq heq using fun i ↦ hdiv (v i) (hvB i) (hv i)
  have hinj := aeval_injective_of_natDegree_ne_zero hgpos
  refine ⟨q, hq, ?_, g, hinj, heq⟩
  obtain ⟨f, hf⟩ := hgB
  have hcomp : (aeval (R := k) g).comp (MvPolynomial.aeval (R := k) q) = MvPolynomial.aeval (R := k) v :=
    MvPolynomial.algHom_ext (by simp [heq])
  have hx : X ∈ (MvPolynomial.aeval (R := k) q).range := by
    refine ⟨f, hinj ?_⟩
    change (aeval (R := k) g) ((MvPolynomial.aeval (R := k) q) f) = _
    change (MvPolynomial.aeval (R := k) v) f = g at hf
    rw [← AlgHom.comp_apply, hcomp, hf, aeval_X]
  intro w
  obtain ⟨f, hf⟩ := hx
  change (MvPolynomial.aeval (R := k) q) f = X at hf
  refine ⟨aeval f w, ?_⟩
  rw [← AlgHom.comp_apply, ← aeval_algHom, hf, aeval_X_left_apply]


section Scheme

variable {ix : Type u}

private def testAlgebraRingMap {R S : TestAlgebra k} (f : R ⟶ S) : R →+* S :=
  f.hom.toRingHom

private theorem testAlgebraRingMap_commutes {R S : TestAlgebra k} (f : R ⟶ S) (x : k) :
    testAlgebraRingMap f (algebraMap k R x) = algebraMap k S x := f.hom.commutes x

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate polynomials of a nonconstant curve in a closed vector subgroup
have a nonzero coefficient in positive degree. -/
private theorem curve_coordinates {K : Type u} [Field K] [Algebra k K]
    {G : GroupScheme k} {Q : HopfAlgebraCategory k}
    (e : G ≅ specGroup Q) (j : MvPolynomial ix k →ₐ[k] Q) (hj : Function.Surjective j)
    (y : AffineLineCurve ((groupBaseChange k K).obj G)) (hy : IsNonconstantCurve y) :
    ∃ f : Q →ₐ[k] Polynomial K, ∃ i n, n ≠ 0 ∧ (f (j (MvPolynomial.X i))).coeff n ≠ 0 := by
  let res := restrictTestAlgebra k K
  let ff : (testSpec k).FullyFaithful := algSpec.fullyFaithful (R := CommRingCat.of k)
  let A := CommAlgCat.of k Q
  let eO : G.X ⟶ (testSpec k).obj (op A) := e.hom.hom.hom
  let coords (R : TestAlgebra K) (z : Points ((baseChange k K).obj G.X) R) :
      (op (res.obj R)) ⟶ op A :=
    ff.preimage (baseChangePoint k K G.X R z ≫ eO)
  have hnat {R S : TestAlgebra K} (a : R ⟶ S) (z : Points ((baseChange k K).obj G.X) R) :
      coords S (mapPoints a z) = (res.map a).op ≫ coords R z := by
    apply ff.map_injective
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage, coords]
    rw [baseChangePointsNaturality k K G.X a z]
    exact Category.assoc _ _ _
  let R := CommAlgCat.of K (Polynomial K)
  let Z := CommAlgCat.of K K
  let a : R ⟶ Z := CommAlgCat.ofHom (aeval (0 : K))
  let c : Z ⟶ R := CommAlgCat.ofHom (Algebra.ofId K (Polynomial K))
  let fC : A ⟶ res.obj R := (coords R y).unop
  let f : Q →ₐ[k] Polynomial K :=
    { toRingHom := testAlgebraRingMap fC
      commutes' := fun x ↦ testAlgebraRingMap_commutes fC x }
  refine ⟨f, ?_⟩
  by_contra! h
  have hf (i : ix) : (f (j (MvPolynomial.X i))).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact natDegree_le_iff_coeff_eq_zero.mpr (fun n hn ↦ h i n (Nat.ne_of_gt hn))
  suffices eq : coords R y = coords R (mapPoints c (mapPoints a y)) by
    apply hy
    apply (baseChangePoints k K G.X R).1
    let : IsIso eO := inferInstanceAs (IsIso ((Grp.forget (SchemeOver k)).map e.hom))
    apply (cancel_mono eO).mp
    change baseChangePoint k K G.X R y ≫ eO =
      baseChangePoint k K G.X R (mapPoints c (mapPoints a y)) ≫ eO
    simpa only [coords, Functor.FullyFaithful.map_preimage] using congrArg ((testSpec k).map) eq
  rw [hnat c, hnat a]
  apply Quiver.Hom.unop_inj
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  obtain ⟨w, rfl⟩ := hj x
  let evalZero : Polynomial K →ₐ[K] Polynomial K :=
    (Algebra.ofId K (Polynomial K)).comp (aeval (0 : K))
  let evalZeroK := evalZero.restrictScalars k
  have hcomp : f.comp j = (evalZeroK.comp f).comp j := by
    apply MvPolynomial.algHom_ext
    intro i
    change f (j (MvPolynomial.X i)) = C (aeval (0 : K) (f (j (MvPolynomial.X i))))
    rw [← coeff_zero_eq_aeval_zero]
    exact eq_C_of_natDegree_eq_zero (hf i)
  exact DFunLike.congr_fun hcomp w

private theorem delta_of_supported
    (h : Specs.StandardGroups.HopfOperations k (Polynomial k))
    (hX : h.delta (X : Polynomial k) = X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] X)
    (f : Polynomial k) (hf : SupportedOnPowers p f) :
    h.delta f = f ⊗ₜ[k] 1 + 1 ⊗ₜ[k] f := by
  classical
  let : ExpChar (Polynomial k ⊗[k] Polynomial k) p :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective k (Polynomial k ⊗[k] Polynomial k)) p
  let L : Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k :=
    Algebra.TensorProduct.includeLeft
  let R : Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k :=
    Algebra.TensorProduct.includeRight
  let D := L.toLinearMap + R.toLinearMap
  change h.delta f = D f
  conv_lhs => rw [← sum_monomial_eq f, Polynomial.sum, map_sum]
  conv_rhs => rw [← sum_monomial_eq f, Polynomial.sum, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = p ^ m := by
    by_contra! h
    exact (Polynomial.mem_support_iff.mp hn) (hf n (by simpa using h))
  change h.delta (monomial (p ^ m) (f.coeff (p ^ m))) =
    L (monomial (p ^ m) (f.coeff (p ^ m))) + R (monomial (p ^ m) (f.coeff (p ^ m)))
  simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, hX, add_pow_expChar_pow]
  simp only [← Polynomial.algebraMap_eq, AlgHom.commutes]
  exact mul_add ..

private def additiveCoordinateMap
    (h : Specs.StandardGroups.HopfOperations k (MvPolynomial ix k))
    (hX : ∀ i, h.delta (MvPolynomial.X i) = MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i)
    (he : ∀ i, h.epsilon (MvPolynomial.X i) = 0)
    (h₀ : Specs.StandardGroups.HopfOperations k (Polynomial k))
    (h₀X : h₀.delta (X : Polynomial k) = X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] X)
    (h₀e : h₀.epsilon (X : Polynomial k) = 0)
    (q : ix → Polynomial k) (hq : ∀ i, SupportedOnPowers p (q i)) :
    letI := h.hopf
    letI := h₀.hopf
    CommHopfAlgCat.of k (MvPolynomial ix k) ⟶ CommHopfAlgCat.of k (Polynomial k) := by
  letI := h.hopf
  letI := h₀.hopf
  letI : Bialgebra k (MvPolynomial ix k) := h.hopf.toBialgebra
  letI : Bialgebra k (Polynomial k) := h₀.hopf.toBialgebra
  let ev := MvPolynomial.aeval (R := k) q
  refine CommHopfAlgCat.ofHom (BialgHom.ofAlgHom ev ?_ ?_)
  · apply MvPolynomial.algHom_ext
    intro i
    change h₀.epsilon (ev (MvPolynomial.X i)) = h.epsilon (MvPolynomial.X i)
    change h₀.epsilon (MvPolynomial.aeval q (MvPolynomial.X i)) = _
    have hε : h₀.epsilon = aeval (0 : k) := by
      ext
      simpa using h₀e
    rw [MvPolynomial.aeval_X, he, hε, ← coeff_zero_eq_aeval_zero]
    exact hq i 0 (by rintro ⟨m, hm⟩; exact (pow_ne_zero m (Fact.out : p.Prime).ne_zero) hm.symm)
  · apply MvPolynomial.algHom_ext
    intro i
    change Algebra.TensorProduct.map ev ev (h.delta (MvPolynomial.X i)) =
      h₀.delta (ev (MvPolynomial.X i))
    rw [hX, map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one]
    change MvPolynomial.aeval q (MvPolynomial.X i) ⊗ₜ[k] 1 +
      1 ⊗ₜ[k] MvPolynomial.aeval q (MvPolynomial.X i) =
      h₀.delta (MvPolynomial.aeval q (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X, delta_of_supported h₀ h₀X _ (hq i)]

end Scheme

open private groupIsoOfPoints from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private liftHopfQuotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private primitive_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.AdditiveEquations

set_option maxHeartbeats 600000 in
private theorem vectorSubgroupContainsAdditive {p : ℕ} [Fact p.Prime] [CharP k p]
    {ix K : Type u} [Fintype ix]
    [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (h : Specs.StandardGroups.HopfOperations k (MvPolynomial ix k))
    (hδ : ∀ i, h.delta (MvPolynomial.X i) = MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i)
    (hε : ∀ i, h.epsilon (MvPolynomial.X i) = 0)
    {F : GroupScheme k}
    (j : letI := h.hopf; F ⟶ specGroup (CommHopfAlgCat.of k (MvPolynomial ix k)))
    (hj : IsClosedImmersion j.hom.hom.left)
    (y : AffineLineCurve ((groupBaseChange k K).obj F)) (hy : IsNonconstantCurve y) :
    ∃ (J : GroupScheme k) (i : J ⟶ F), IsClosedImmersion i.hom.hom.left ∧
      Nonempty ((groupPointsFunctor k).obj J ≅ Specs.StandardGroups.additivePoints k) := by
  classical
  let := h.hopf
  let A := CommHopfAlgCat.of k (MvPolynomial ix k)
  have hX : HasPrimitiveCoordinates h := by
    intro i
    exact (primitive_iff h _).mpr ((hδ i).trans (add_comm _ _))
  obtain ⟨S, hS, hI, e, _⟩ :=
    AdditiveEquations.closedVectorSubgroupEquations k ix p h hX F j hj
  let I : Ideal A := Ideal.span (S : Set (MvPolynomial ix k))
  let : I.IsHopfIdeal k := hI
  let Q := hopfQuotient A I
  let π : A →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  obtain ⟨f, hf⟩ := curve_coordinates (Q := Q) e π hπ y hy
  let v (i : ix) := f (π (MvPolynomial.X i))
  have hvan (s : MvPolynomial ix k) (hs : s ∈ S) : MvPolynomial.aeval (R := k) v s = 0 := by
    have hev : MvPolynomial.aeval (R := k) v = f.comp π :=
      MvPolynomial.algHom_ext (fun i ↦ MvPolynomial.aeval_X v i)
    rw [hev, AlgHom.comp_apply, show π s = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hs), map_zero]
  obtain ⟨T, hTpow, hTsupp, hi⟩ := traceExtract (k := k) (p := p) v hf
  obtain ⟨q, hq, hsurj, g, hg, heq⟩ :=
    reparametrize (p := p) (T ∘ v) (fun i ↦ hTsupp (v i)) hi
  have hvanq (s : MvPolynomial ix k) (hs : s ∈ S) : MvPolynomial.aeval (R := k) q s = 0 := by
    apply hg
    have hm : (aeval (R := k) g).comp (MvPolynomial.aeval (R := k) q) =
        MvPolynomial.aeval (R := k) (T ∘ v) :=
      MvPolynomial.algHom_ext (by simp [heq])
    rw [← AlgHom.comp_apply, hm, ← map_additive_equation T hTpow v (hS s hs),
      hvan s hs, map_zero, map_zero]
  obtain ⟨h₀, h₀X, h₀e, _, _, _, gaIso, _⟩ := StandardGroups.additiveGroupSpecification k
  let := h₀.hopf
  let B := CommHopfAlgCat.of k (Polynomial k)
  let a : A ⟶ B := additiveCoordinateMap (p := p) h hδ hε h₀ h₀X h₀e q hq
  have ha : ∀ z ∈ I, a.hom z = 0 := by
    intro z hz
    exact show z ∈ RingHom.ker (MvPolynomial.aeval (R := k) q) from
      (Ideal.span_le.mpr fun s hs ↦ hvanq s hs) hz
  let b : Q ⟶ B := liftHopfQuotient I a ha
  have hb : Function.Surjective b.hom := by
    intro w
    obtain ⟨z, hz⟩ := hsurj w
    exact ⟨π z, hz⟩
  let : IsClosedImmersion (specGroupMap b).hom.hom.left := (hopfMapClosedImmersion k b).mpr hb
  let : IsClosedImmersion e.inv.hom.hom.left := by
    change IsClosedImmersion (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.inv)
    infer_instance
  refine ⟨specGroup B, specGroupMap b ≫ e.inv, ?_, ⟨gaIso⟩⟩
  change IsClosedImmersion ((specGroupMap b).hom.hom.left ≫ e.inv.hom.hom.left)
  infer_instance

set_option maxHeartbeats 600000 in
private theorem vectorEmbeddingContainsAdditive {p : ℕ} [Fact p.Prime] [CharP k p]
    {K : Type u}
    [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {F : GroupScheme k} (d : ℕ) (V : AffineAlgebraicGroup k)
    (vIso : (groupPointsFunctor k).obj V.val ≅ Specs.StandardGroups.additivePowerPoints k (Index.{u} d))
    (j : F ⟶ V.val) (hj : IsClosedImmersion j.hom.hom.left)
    (y : AffineLineCurve ((groupBaseChange k K).obj F)) (hy : IsNonconstantCurve y) :
    ∃ (J : GroupScheme k) (i : J ⟶ F), IsClosedImmersion i.hom.hom.left ∧
      Nonempty ((groupPointsFunctor k).obj J ≅ Specs.StandardGroups.additivePoints k) := by
  let ix := Index.{u} d
  obtain ⟨h, hδ, hε, _, _, _, sIso, _⟩ := StandardGroups.additivePowerSpecification k ix
  let := h.hopf
  let W := Specs.StandardGroups.spectrum k (MvPolynomial ix k)
  let eV : V.val ≅ W.val := groupIsoOfPoints (vIso ≪≫ sIso.symm)
  let : IsClosedImmersion eV.hom.hom.hom.left := by
    change IsClosedImmersion (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map eV.hom)
    infer_instance
  let : IsClosedImmersion j.hom.hom.left := hj
  have hj' : IsClosedImmersion (j ≫ eV.hom).hom.hom.left := by
    change IsClosedImmersion (j.hom.hom.left ≫ eV.hom.hom.hom.left)
    infer_instance
  exact vectorSubgroupContainsAdditive (p := p) h hδ hε (j ≫ eV.hom) hj' y hy

set_option maxHeartbeats 700000 in
/-- A normalized central curve in a subgroup killed by the characteristic yields
a central additive subgroup over the original field. -/
theorem centralAdditiveSubgroup_conditional :
    CentralKilledByPCurves.{u} → CentralAdditiveSubgroup.{u} := by
  intro hcentralize k _ p _ _ U hs hc hu L _ _ _ x hx
  obtain ⟨F, hFs, hFc, hFcentral, hFp, K, _, _, _, _, y, _, hy⟩ :=
    hcentralize p U hs hc hu L x hx
  let G := closedSubgroupAlgebraicGroup F
  have : Smooth G.val.X.hom := hFs
  have : ConnectedSpace G.val.X.left := hFc
  have huG : IsUnipotent G := closedSubgroupsUnipotent U F hu
  let : IsClosedImmersion F.inclusion.hom.hom.left := F.isClosedImmersion
  let : Mono F.inclusion.hom.hom := (Over.forget _).mono_of_mono_map
    (inferInstanceAs (Mono F.inclusion.hom.hom.left))
  have hcomm (R : TestAlgebra k) (a b : Points F.group.X R) : Commute a b := by
    change a * b = b * a
    apply (cancel_mono F.inclusion.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    simpa using ((centralizes_iff (𝟙 U.val) _).mp hFcentral
      ((testSpec k).obj (op R)) a (b ≫ F.inclusion.hom.hom)).eq
  obtain ⟨d, V, ⟨vIso⟩, j, hj⟩ := killedByPVectorEmbedding p G huG hcomm hFp
  obtain ⟨J, i, hi, hiso⟩ := vectorEmbeddingContainsAdditive (p := p) d V vIso j hj y hy
  change J ⟶ F.group at i
  have hi' : IsClosedImmersion (i ≫ F.inclusion).hom.hom.left := by
    change IsClosedImmersion (i.hom.hom.left ≫ F.inclusion.hom.hom.left)
    exact @IsClosedImmersion.comp _ _ _ _ _ hi F.isClosedImmersion
  refine ⟨⟨J, i ≫ F.inclusion, hi'⟩, ?_, hiso⟩
  apply (centralizes_iff (𝟙 U.val) _).mpr
  intro S t hS
  change S ⟶ J.X at t
  change Commute (t ≫ i.hom.hom ≫ F.inclusion.hom.hom) _
  rw [← Category.assoc t i.hom.hom F.inclusion.hom.hom]
  exact (centralizes_iff (𝟙 U.val) _).mp hFcentral S (t ≫ i.hom.hom) hS

end

end LinearAlgebraicGroups.Unipotent

universe v8_closure_55f43d613c742f0c_u0
theorem _root_.«LinearAlgebraicGroups».«Unipotent».«centralAdditiveSubgroup» : _root_.«LinearAlgebraicGroups».«Specs».«Unipotent».«CentralAdditiveSubgroup».{v8_closure_55f43d613c742f0c_u0} :=
  @_root_.«LinearAlgebraicGroups».«Unipotent».«centralAdditiveSubgroup_conditional».{v8_closure_55f43d613c742f0c_u0} (@_root_.«LinearAlgebraicGroups».«Unipotent».«centralKilledByPCurves».{v8_closure_55f43d613c742f0c_u0})
