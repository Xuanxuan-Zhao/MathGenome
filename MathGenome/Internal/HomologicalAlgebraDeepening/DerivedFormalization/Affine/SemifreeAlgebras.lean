import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeAlgebras
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.DirectSum.Ring

open CategoryTheory

universe u v

namespace DerivedFormalization.Affine.Semifree

noncomputable section

variable {k : Type u} [Field k] [CharZero k]

namespace Variables

variable (V : Variables.{v})

theorem weight_nonpositive (m : V.Exponent) : V.weight m ≤ 0 := by
  rw [weight, Finsupp.weight_apply]
  exact Finsupp.sum_nonpos fun x _ => nsmul_nonpos (V.nonpositive x) _

@[simp] theorem weight_constant : V.weight V.constant.val = 0 :=
  V.weight.map_zero

@[simp] theorem weight_singleton (x : V.Index) : V.weight (V.singleton x).val = V.degree x := by
  simp [weight, singleton, Finsupp.weight_single]

@[simp] theorem inversions_zero_left (p : V.Exponent) : V.inversions 0 p = 0 := by
  simp [inversions]

@[simp] theorem inversions_zero_right (m : V.Exponent) : V.inversions m 0 = 0 := by
  simp [inversions]

theorem inversions_add_left (m n p : V.Exponent) :
    V.inversions (m + n) p = V.inversions m p + V.inversions n p := by
  classical
  unfold inversions
  apply Finsupp.sum_add_index'
  · intro x
    exact Finset.sum_eq_zero fun y _ => by dsimp; split <;> simp
  · intro x a b
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    split <;> simp [add_mul]

theorem inversions_add_right (m n p : V.Exponent) :
    V.inversions m (n + p) = V.inversions m n + V.inversions m p := by
  classical
  let := V.normalOrder
  unfold inversions
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finsupp.sum_add_index'
  · intro y
    split <;> simp
  · intro y a b
    split <;> simp [add_mul, mul_add]

theorem admissible_mono {m n : V.Exponent} (h : ∀ x, m x ≤ n x)
    (hn : V.Admissible n) : V.Admissible m :=
  fun x hx => (h x).trans (hn x hx)

theorem admissible_left {m n : V.Exponent} (h : V.Admissible (m + n)) : V.Admissible m :=
  V.admissible_mono (fun x => by simp) h

theorem admissible_right {m n : V.Exponent} (h : V.Admissible (m + n)) : V.Admissible n :=
  V.admissible_mono (fun x => by simp) h

end Variables

variable (A : NonpositiveCDGA.{u,v} k) (V : Variables.{v})

theorem polynomial_nonpositive (i : ℤ) (hi : 0 < i) : Subsingleton (Polynomial A V i) := by
  refine ⟨fun a b => DFinsupp.ext fun m => ?_⟩
  exact (A.nonpositive _ (by linarith [V.weight_nonpositive m.val])).elim _ _

/-- The coefficient embeddings are injective. -/
theorem term_injective (i : ℤ) (m : V.Monomial) :
    Function.Injective (term A V i m) := by
  classical
  intro a b h
  have hh := congrArg (fun p : Polynomial A V i => p m) h
  simpa only [term, DirectSum.lof_apply] using hh

/-- The support of each homogeneous polynomial is finite. -/
theorem polynomial_finite_support (i : ℤ) (p : Polynomial A V i) :
    {m | p m ≠ 0}.Finite := by
  classical
  exact p.support.finite_toSet.subset fun m hm => DFinsupp.mem_support_iff.mpr hm

/-- A term written using the coefficient's degree as a separate index. -/
def homogeneousTerm (i : ℤ) (m : V.Monomial) {r : ℤ} (h : r + V.weight m.val = i) :
    A.complex.X r →ₗ[k] Polynomial A V i :=
  (term A V i m).comp (castDegree A.complex.X (by omega))

@[simp] theorem homogeneousTerm_self (i : ℤ) (m : V.Monomial) :
    homogeneousTerm A V i m (r := i - V.weight m.val) (by omega) = term A V i m := by
  simp [homogeneousTerm]

private theorem mul_cast {r s n : ℤ} (h : r + s = n)
    (a : A.complex.X r) (b : A.complex.X s) :
    A.mul r s n h a b = castDegree A.complex.X h (A.mul r s (r+s) rfl a b) := by
  subst n
  rfl

open Classical in
theorem polynomialMul_homogeneousTerm {i j n : ℤ} (h : i + j = n)
    (m p : V.Monomial) {r s : ℤ} (hr : r + V.weight m.val = i) (hs : s + V.weight p.val = j)
    (a : A.complex.X r) (b : A.complex.X s) :
    polynomialMul A V i j n h (homogeneousTerm A V i m hr a) (homogeneousTerm A V j p hs b) =
      if hp : V.Admissible (m.val + p.val) then
        (V.weight m.val * s + V.inversions m.val p.val).negOnePow •
          homogeneousTerm A V n ⟨m.val + p.val, hp⟩
            (by change r + s + V.weight (m.val + p.val) = n; rw [map_add]; omega)
            (A.mul r s (r + s) rfl a b)
      else 0 := by
  classical
  obtain rfl : r = i - V.weight m.val := by omega
  obtain rfl : s = j - V.weight p.val := by omega
  rw [homogeneousTerm_self, homogeneousTerm_self, polynomialMul_term]
  unfold termProduct
  split
  · simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, homogeneousTerm, LinearMap.comp_apply]
    congr 2
    apply mul_cast
  · rfl


private theorem polynomial_induction {i : ℤ} (P : Polynomial A V i → Prop)
    (zero : P 0) (single : ∀ m a, P (term A V i m a))
    (add : ∀ a b, P a → P b → P (a + b)) (a : Polynomial A V i) : P a := by
  classical
  exact DirectSum.induction_on a zero single add

private theorem polynomialMul_sign_left {i j n : ℤ} (h : i + j = n)
    (s : ℤˣ) (x : Polynomial A V i) (y : Polynomial A V j) :
    polynomialMul A V i j n h (s • x) y = s • polynomialMul A V i j n h x y :=
  ((polynomialMul A V i j n h).flip y).map_smul_of_tower s x

private theorem polynomialMul_sign_right {i j n : ℤ} (h : i + j = n)
    (s : ℤˣ) (x : Polynomial A V i) (y : Polynomial A V j) :
    polynomialMul A V i j n h x (s • y) = s • polynomialMul A V i j n h x y :=
  (polynomialMul A V i j n h x).map_smul_of_tower s y

private theorem homogeneousTerm_congr {n r : ℤ} {m p : V.Monomial}
    (h : m = p) (hm : r + V.weight m.val = n) (hp : r + V.weight p.val = n)
    (a : A.complex.X r) :
    homogeneousTerm A V n m hm a = homogeneousTerm A V n p hp a := by
  subst p
  rfl

private theorem homogeneousTerm_cast {n r s : ℤ} (m : V.Monomial)
    (h : r = s) (hr : r + V.weight m.val = n) (hs : s + V.weight m.val = n)
    (a : A.complex.X r) :
    homogeneousTerm A V n m hs (castDegree A.complex.X h a) =
      homogeneousTerm A V n m hr a := by
  subst s
  rfl

private theorem polynomialMul_assoc_terms {i j l : ℤ} (m p q : V.Monomial)
    {r s t : ℤ} (hr : r + V.weight m.val = i) (hs : s + V.weight p.val = j)
    (ht : t + V.weight q.val = l) (a : A.complex.X r) (b : A.complex.X s) (c : A.complex.X t) :
    polynomialMul A V (i+j) l (i+j+l) rfl
        (polynomialMul A V i j (i+j) rfl
          (homogeneousTerm A V i m hr a) (homogeneousTerm A V j p hs b))
        (homogeneousTerm A V l q ht c) =
      polynomialMul A V i (j+l) (i+j+l) (add_assoc i j l).symm
        (homogeneousTerm A V i m hr a)
        (polynomialMul A V j l (j+l) rfl
          (homogeneousTerm A V j p hs b) (homogeneousTerm A V l q ht c)) := by
  classical
  rw [polynomialMul_homogeneousTerm, polynomialMul_homogeneousTerm A V (i := j)]
  by_cases hmp : V.Admissible (m.val + p.val)
  · rw [dite_eq_left hmp, polynomialMul_sign_left, polynomialMul_homogeneousTerm]
    by_cases hpq : V.Admissible (p.val + q.val)
    · rw [dite_eq_left hpq, polynomialMul_sign_right, polynomialMul_homogeneousTerm]
      by_cases hmpq : V.Admissible (m.val + p.val + q.val)
      · have hmpq' : V.Admissible (m.val + (p.val + q.val)) := by
          simpa only [add_assoc] using hmpq
        rw [dite_eq_left hmpq, dite_eq_left hmpq']
        simp only [smul_smul, ← Int.negOnePow_add]
        have hsign :
            V.weight m.val * s + V.inversions m.val p.val +
                (V.weight (m.val + p.val) * t + V.inversions (m.val + p.val) q.val) =
              V.weight p.val * t + V.inversions p.val q.val +
                (V.weight m.val * (s+t) + V.inversions m.val (p.val + q.val)) := by
          rw [map_add, V.inversions_add_left, V.inversions_add_right]
          ring
        rw [hsign]
        congr 1
        rw [A.toDGAlgebra.assoc r s t a b c, mul_cast]
        rw [homogeneousTerm_cast (hr := by
          change r + (s+t) + V.weight (m.val+p.val+q.val) = i+j+l
          simp only [map_add]
          omega)]
        apply homogeneousTerm_congr A V
        exact Subtype.ext (add_assoc _ _ _)
      · have hmpq' : ¬ V.Admissible (m.val + (p.val + q.val)) := by
          simpa only [add_assoc] using hmpq
        rw [dite_eq_right hmpq, dite_eq_right hmpq', smul_zero, smul_zero]
    · have hmpq : ¬ V.Admissible (m.val + p.val + q.val) := fun h =>
        hpq (V.admissible_right (by simpa only [← add_assoc] using h))
      rw [dite_eq_right hpq, map_zero, dite_eq_right hmpq, smul_zero]
  · rw [dite_eq_right hmp, map_zero, LinearMap.zero_apply]
    by_cases hpq : V.Admissible (p.val + q.val)
    · have hmpq : ¬ V.Admissible (m.val + (p.val + q.val)) := fun h =>
        hmp (V.admissible_left (by simpa only [add_assoc] using h))
      rw [dite_eq_left hpq, polynomialMul_sign_right, polynomialMul_homogeneousTerm,
        dite_eq_right hmpq, smul_zero]
    · rw [dite_eq_right hpq, map_zero]

theorem polynomialMul_assoc (i j l : ℤ)
    (x : Polynomial A V i) (y : Polynomial A V j) (z : Polynomial A V l) :
    polynomialMul A V (i+j) l (i+j+l) rfl (polynomialMul A V i j (i+j) rfl x y) z =
      polynomialMul A V i (j+l) (i+j+l) (add_assoc i j l).symm x
        (polynomialMul A V j l (j+l) rfl y z) := by
  induction x using polynomial_induction A V with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | single m a =>
    induction y using polynomial_induction A V with
    | zero => simp
    | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | single p b =>
      induction z using polynomial_induction A V with
      | zero => simp
      | add z z' h h' => simp only [map_add, h, h']
      | single q c =>
        rw [← homogeneousTerm_self A V i m, ← homogeneousTerm_self A V j p,
          ← homogeneousTerm_self A V l q]
        exact polynomialMul_assoc_terms A V m p q _ _ _ a b c


omit [CharZero k] in
private theorem castDegree_cancel (X : ℤ → ModuleCat.{v} k) {i j : ℤ}
    (h : i = j) (a : X i) :
    castDegree X h.symm (castDegree X h a) = a := by
  subst j
  rfl

private theorem mul_one_left_cast (r : ℤ) (a : A.complex.X r) :
    A.mul 0 r (0+r) rfl A.one a = castDegree A.complex.X (zero_add r).symm a := by
  have h := mul_cast A (zero_add r) A.one a
  have hu := A.toDGAlgebra.id_comp r a
  change A.mul 0 r r (zero_add r) A.one a = a at hu
  rw [hu] at h
  have ht := congrArg (castDegree A.complex.X (zero_add r).symm) h
  rwa [castDegree_cancel, eq_comm] at ht

private theorem mul_one_right_cast (r : ℤ) (a : A.complex.X r) :
    A.mul r 0 (r+0) rfl a A.one = castDegree A.complex.X (add_zero r).symm a := by
  have h := mul_cast A (add_zero r) a A.one
  have hu := A.toDGAlgebra.comp_id r a
  change A.mul r 0 r (add_zero r) a A.one = a at hu
  rw [hu] at h
  have ht := congrArg (castDegree A.complex.X (add_zero r).symm) h
  rwa [castDegree_cancel, eq_comm] at ht

theorem polynomialMul_one_left (i : ℤ) (x : Polynomial A V i) :
    polynomialMul A V 0 i i (zero_add i) (coefficient A V 0 A.one) x = x := by
  classical
  induction x using polynomial_induction A V with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | single m a =>
    change polynomialMul A V 0 i i (zero_add i)
      (homogeneousTerm A V 0 V.constant (r := 0) (by simp) A.one) (term A V i m a) = _
    nth_rw 1 [← homogeneousTerm_self A V i m]
    rw [polynomialMul_homogeneousTerm]
    have hm : V.Admissible (V.constant.val + m.val) := by simpa [Variables.constant] using m.prop
    rw [dite_eq_left hm]
    rw [show (V.weight V.constant.val * (i - V.weight m.val) +
      V.inversions V.constant.val m.val).negOnePow = 1 by
        change (V.weight 0 * (i - V.weight m.val) + V.inversions 0 m.val).negOnePow = 1
        simp, one_smul]
    rw [mul_one_left_cast, homogeneousTerm_cast (hr := by
      change i - V.weight m.val + V.weight (0+m.val) = i
      simp)]
    rw [← homogeneousTerm_self A V i m]
    apply homogeneousTerm_congr A V
    exact Subtype.ext (zero_add _)

theorem polynomialMul_one_right (i : ℤ) (x : Polynomial A V i) :
    polynomialMul A V i 0 i (add_zero i) x (coefficient A V 0 A.one) = x := by
  classical
  induction x using polynomial_induction A V with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy]
  | single m a =>
    change polynomialMul A V i 0 i (add_zero i) (term A V i m a)
      (homogeneousTerm A V 0 V.constant (r := 0) (by simp) A.one) = _
    nth_rw 1 [← homogeneousTerm_self A V i m]
    rw [polynomialMul_homogeneousTerm]
    have hm : V.Admissible (m.val + V.constant.val) := by simpa [Variables.constant] using m.prop
    rw [dite_eq_left hm]
    rw [show (V.weight m.val * 0 + V.inversions m.val V.constant.val).negOnePow = 1 by
      change (V.weight m.val * 0 + V.inversions m.val 0).negOnePow = 1
      simp, one_smul]
    rw [mul_one_right_cast, homogeneousTerm_cast (hr := by
      change i - V.weight m.val + V.weight (m.val+0) = i
      simp)]
    rw [← homogeneousTerm_self A V i m]
    apply homogeneousTerm_congr A V
    exact Subtype.ext (add_zero _)


private theorem sum_even {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (h : ∀ x ∈ s, Even (f x)) : Even (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).add
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

private theorem inversions_parity (m p : V.Exponent) (h : V.Admissible (m+p)) :
    Even (V.weight m * V.weight p - (V.inversions m p + V.inversions p m)) := by
  classical
  let := V.normalOrder
  let a : V.Index → ℤ := fun x => (m x : ℤ) * V.degree x
  let b : V.Index → ℤ := fun y => (p y : ℤ) * V.degree y
  have hw : V.weight m * V.weight p = ∑ x ∈ m.support, ∑ y ∈ p.support, a x * b y := by
    simp only [Variables.weight, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, a, b]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hmp : V.inversions m p =
      ∑ x ∈ m.support, ∑ y ∈ p.support, if y < x then a x * b y else 0 := rfl
  have hpm : V.inversions p m =
      ∑ x ∈ m.support, ∑ y ∈ p.support, if x < y then a x * b y else 0 := by
    rw [Finset.sum_comm]
    change (∑ y ∈ p.support, ∑ x ∈ m.support, if x < y then b y * a x else 0) = _
    simp only [mul_comm (b _) (a _)]
  rw [hw, hmp, hpm, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply sum_even
  intro x hx
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply sum_even
  intro y hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · simp [hxy, not_lt_of_gt hxy]
  · simp only [lt_irrefl, ite_false, add_zero, sub_zero]
    rcases Int.even_or_odd (V.degree x) with he | ho
    · exact (he.mul_left (m x : ℤ)).mul_right (b x)
    · have hab := h x ho
      have hm := Finsupp.mem_support_iff.mp hx
      have hp := Finsupp.mem_support_iff.mp hy
      rw [Finsupp.add_apply] at hab
      omega
  · simp [hyx, not_lt_of_gt hyx]

private theorem polynomialMul_comm_terms {i j n : ℤ} (h : i + j = n) (m p : V.Monomial)
    {r s : ℤ} (hr : r + V.weight m.val = i) (hs : s + V.weight p.val = j)
    (a : A.complex.X r) (b : A.complex.X s) :
    polynomialMul A V i j n h (homogeneousTerm A V i m hr a) (homogeneousTerm A V j p hs b) =
      (i*j).negOnePow • polynomialMul A V j i n ((add_comm j i).trans h)
        (homogeneousTerm A V j p hs b) (homogeneousTerm A V i m hr a) := by
  classical
  rw [polynomialMul_homogeneousTerm, polynomialMul_homogeneousTerm A V (i := j)]
  by_cases hmp : V.Admissible (m.val + p.val)
  · have hpm : V.Admissible (p.val + m.val) := by rwa [add_comm]
    rw [dite_eq_left hmp, dite_eq_left hpm]
    have hcomm := A.toCommDGAlgebra.graded_comm r s (r+s) rfl a b
    rw [hcomm, mul_cast A ((add_comm s r).trans (rfl : r+s = r+s))]
    rw [LinearMap.map_smul_of_tower, homogeneousTerm_cast (hr := by
      change s+r+V.weight (m.val+p.val) = n
      rw [map_add]
      omega)]
    simp only [smul_smul, ← Int.negOnePow_add]
    have he := inversions_parity V m.val p.val hmp
    have hsign :
        (V.weight m.val * s + V.inversions m.val p.val + r*s).negOnePow =
          (i*j + (V.weight p.val * r + V.inversions p.val m.val)).negOnePow := by
      rw [Int.negOnePow_eq_iff, ← hr, ← hs]
      convert ((he.neg).sub (even_two_mul (r * V.weight p.val +
        V.inversions p.val m.val))) using 1; ring
    rw [hsign]
    congr 1
    apply homogeneousTerm_congr A V
    exact Subtype.ext (add_comm _ _)
  · have hpm : ¬ V.Admissible (p.val + m.val) := by rwa [add_comm]
    rw [dite_eq_right hmp, dite_eq_right hpm, smul_zero]

theorem polynomialMul_comm (i j n : ℤ) (h : i + j = n)
    (x : Polynomial A V i) (y : Polynomial A V j) :
    polynomialMul A V i j n h x y =
      (i*j).negOnePow • polynomialMul A V j i n ((add_comm j i).trans h) y x := by
  induction x using polynomial_induction A V with
  | zero => simp
  | add x x' h h' => simp only [map_add, LinearMap.add_apply, smul_add, h, h']
  | single m a =>
    induction y using polynomial_induction A V with
    | zero => simp
    | add y y' h h' => simp only [map_add, LinearMap.add_apply, smul_add, h, h']
    | single p b =>
      rw [← homogeneousTerm_self A V i m, ← homogeneousTerm_self A V j p]
      exact polynomialMul_comm_terms A V h m p _ _ a b


open Specs.DerivedFormalization.Affine.SemifreeAlgebras

theorem degreeZeroVariable : DegreeZeroVariable.{u,v} := by
  intro k _ _ A V x hx p
  exact (polynomial_nonpositive A V _ (by omega)).elim p 0

theorem continuousStages : ContinuousStages.{u,v} := by
  classical
  intro k _ _ A V S a hb hlimit i p
  constructor
  · intro h
    let allVars : Finset V.Index := p.support.biUnion fun m => m.val.support
    have hall : ∀ x ∈ allVars, S.stage x < a := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp hx
      exact h m (DFinsupp.mem_support_iff.mp hm) x hxm
    have bounded : ∀ t : Finset V.Index, (∀ x ∈ t, S.stage x < a) →
        ∃ b : S.Stage, b < a ∧ ∀ x ∈ t, S.stage x < b := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using hb
      | insert x t hxt ih =>
        intro ht
        obtain ⟨b, hba, hbt⟩ := ih (fun y hy => ht y (Finset.mem_insert_of_mem hy))
        obtain ⟨c, hxc, hca⟩ := hlimit x (ht x (Finset.mem_insert_self _ _))
        refine ⟨max b c, max_lt hba hca, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxc.trans_le (le_max_right _ _)
        · exact (hbt y hy).trans_le (le_max_left _ _)
    obtain ⟨b, hba, hb⟩ := bounded allVars hall
    refine ⟨b, hba, fun m hm x hx => hb x ?_⟩
    exact Finset.mem_biUnion.mpr ⟨m, DFinsupp.mem_support_iff.mpr hm, hx⟩
  · rintro ⟨b, hba, hb⟩ m hm x hx
    exact (hb m hm x hx).trans hba

private theorem polynomial_induction_on_support (S : Set V.Index) {i : ℤ}
    (P : Polynomial A V i → Prop) (zero : P 0)
    (single : ∀ m a, (∀ x ∈ m.val.support, x ∈ S) → P (term A V i m a))
    (add : ∀ a b, P a → P b → P (a+b))
    (a : Polynomial A V i) (ha : UsesOnly A V S a) : P a := by
  classical
  have he : (∑ m ∈ a.support, term A V i m (a m)) = a := DirectSum.sum_support_of a
  rw [← he]
  exact Finset.sum_induction _ P add zero fun m hm => single m (a m)
    (ha m (DFinsupp.mem_support_iff.mp hm))

/-- The polynomials using only a set of variables are generated by that set and the base. -/
theorem polynomial_generated_on (S : Set V.Index) (P : ∀ i, Polynomial A V i → Prop)
    (zero : ∀ i, P i 0)
    (add : ∀ i (a b : Polynomial A V i), P i a → P i b → P i (a+b))
    (sign : ∀ i (s : ℤˣ) (a : Polynomial A V i), P i a → P i (s • a))
    (base : ∀ i a, P i (coefficient A V i a))
    (var : ∀ x ∈ S, P (V.degree x) (variableTerm A V x))
    (mul : ∀ i j n (h : i+j = n) a b, P i a → P j b → P n (polynomialMul A V i j n h a b))
    (i : ℤ) (a : Polynomial A V i) (ha : UsesOnly A V S a) : P i a := by
  classical
  have monomials : ∀ m : V.Monomial, (∀ x ∈ m.val.support, x ∈ S) → ∀ i a, P i (term A V i m a) := by
    intro m
    induction m using (measure fun m : V.Monomial => m.val.degree).wf.induction with
    | h m ih =>
      intro hmS i a
      by_cases hm : m.val = 0
      · have he : m = V.constant := Subtype.ext hm
        subst m
        have hm' : i = i - V.weight V.constant.val := by rw [V.weight_constant, sub_zero]
        have hb := base i (castDegree A.complex.X hm'.symm a)
        rwa [coefficient, LinearMap.comp_apply, castDegree_cancel] at hb
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr ((Finsupp.support_nonempty_iff).mpr hm).ne_empty
        have hx' : m.val x ≠ 0 := Finsupp.mem_support_iff.mp hx
        let r := m.val - Finsupp.single x 1
        have hr : r + Finsupp.single x 1 = m.val :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hx'))
        have hr' : V.Admissible r := V.admissible_mono (fun y => by
          change (m.val - _ : V.Exponent) y ≤ m.val y
          rw [Finsupp.tsub_apply]
          exact Nat.sub_le _ _) m.prop
        let p : V.Monomial := ⟨r, hr'⟩
        have hp : p.val + (V.singleton x).val = m.val := hr
        have hlt : p.val.degree < m.val.degree := by
          have hd := congrArg Finsupp.degree hp
          rw [map_add, show (V.singleton x).val.degree = 1 by
            change (Finsupp.single x (1 : ℕ)).degree = 1
            rw [Finsupp.degree_single]] at hd
          omega
        have hw : V.weight p.val + V.degree x = V.weight m.val := by
          rw [← V.weight_singleton x, ← map_add, hp]
        let j := i - V.degree x
        have hj : j + V.degree x = i := by dsimp [j]; omega
        let s := i - V.weight m.val
        have hs : s + V.weight p.val = j := by dsimp [s,j]; omega
        have hv : 0 + V.weight (V.singleton x).val = V.degree x := by simp
        have hpp : P j (homogeneousTerm A V j p hs a) := by
          apply ih p hlt (fun y hy => hmS y ?_) j _
          apply Finsupp.mem_support_iff.mpr
          have hn := Finsupp.mem_support_iff.mp hy
          change (m.val - _ : V.Exponent) y ≠ 0 at hn
          rw [Finsupp.tsub_apply] at hn
          omega
        have hh := mul j (V.degree x) i hj _ _ hpp (var x (hmS x hx))
        change P i (polynomialMul A V j (V.degree x) i hj
          (homogeneousTerm A V j p hs a) (homogeneousTerm A V _ (V.singleton x) hv A.one)) at hh
        rw [polynomialMul_homogeneousTerm,
          dite_eq_left (show V.Admissible (p.val + (V.singleton x).val) by rw [hp]; exact m.prop)] at hh
        rw [mul_one_right_cast, homogeneousTerm_cast (hr := by
          change s + V.weight (p.val + (V.singleton x).val) = i
          rw [hp]
          dsimp [s]
          omega)] at hh
        have ht : (⟨p.val + (V.singleton x).val, by rw [hp]; exact m.prop⟩ : V.Monomial) = m :=
          Subtype.ext hp
        rw [homogeneousTerm_congr A V ht _ (by dsimp [s]; omega), homogeneousTerm_self] at hh
        have hu := sign i (V.weight p.val * 0 + V.inversions p.val (V.singleton x).val).negOnePow⁻¹ _ hh
        simpa only [smul_smul, inv_mul_cancel, one_smul] using hu
  exact polynomial_induction_on_support A V S (P i) (zero i)
    (fun m a hm => monomials m hm i a) (add i) a ha

/-- Finite polynomials are generated by the base and the individual variables. -/
theorem polynomial_generated (P : ∀ i, Polynomial A V i → Prop)
    (zero : ∀ i, P i 0)
    (add : ∀ i (a b : Polynomial A V i), P i a → P i b → P i (a+b))
    (sign : ∀ i (s : ℤˣ) (a : Polynomial A V i), P i a → P i (s • a))
    (base : ∀ i a, P i (coefficient A V i a))
    (var : ∀ x, P (V.degree x) (variableTerm A V x))
    (mul : ∀ i j n (h : i+j = n) a b, P i a → P j b → P n (polynomialMul A V i j n h a b))
    (i : ℤ) (a : Polynomial A V i) : P i a :=
  polynomial_generated_on A V Set.univ P zero add sign base (fun x _ => var x)
    mul i a (fun _ _ _ _ => Set.mem_univ _)



theorem gradedLift_unique (B : CommDGAlgebra.{u,v} k)
    (f : ∀ i, A.complex.X i →ₗ[k] B.complex.X i)
    (x : ∀ a, B.complex.X (V.degree a)) :
    Subsingleton (GradedLift A V B f x) := by
  constructor
  intro F G
  have he : F.component = G.component := by
    funext i
    apply LinearMap.ext
    apply polynomial_generated A V (fun i p => F.component i p = G.component i p)
    · intro i
      simp
    · intro i a b ha hb
      simp only [map_add, ha, hb]
    · intro i s a ha
      simp only [LinearMap.map_smul_of_tower, ha]
    · intro i a
      rw [F.map_base, G.map_base]
    · intro a
      rw [F.map_var, G.map_var]
    · intro i j n h a b ha hb
      rw [F.map_mul, G.map_mul, ha, hb]
  cases F
  cases G
  cases he
  rfl

theorem derivation_unique (dx : ∀ x, Polynomial A V (V.degree x + 1)) :
    Subsingleton (Derivation A V dx) := by
  constructor
  intro D E
  have he : D.d = E.d := by
    funext i
    apply LinearMap.ext
    apply polynomial_generated A V (fun i p => D.d i p = E.d i p)
    · intro i
      simp
    · intro i a b ha hb
      simp only [map_add, ha, hb]
    · intro i s a ha
      simp only [LinearMap.map_smul_of_tower, ha]
    · intro i a
      rw [D.on_base, E.on_base]
    · intro a
      rw [D.on_var, E.on_var]
    · intro i j n h a b ha hb
      rw [D.leibniz, E.leibniz, ha, hb]
  cases D
  cases E
  cases he
  rfl

private theorem derivative_sq_on_product {dx : ∀ x, Polynomial A V (V.degree x+1)}
    (D : Derivation A V dx) (i j n : ℤ) (h : i+j = n)
    (a : Polynomial A V i) (b : Polynomial A V j)
    (ha : D.d (i+1) (D.d i a) = 0) (hb : D.d (j+1) (D.d j b) = 0) :
    D.d (n+1) (D.d n (polynomialMul A V i j n h a b)) = 0 := by
  rw [D.leibniz, map_add, LinearMap.map_smul_of_tower, D.leibniz, D.leibniz, ha, hb]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add, add_zero]
  rw [Int.negOnePow_succ, Units.neg_smul, neg_add_cancel]

theorem differentialSquaresToZero : DifferentialSquaresToZero.{u,v} := by
  intro k _ _ A V dx D h
  apply polynomial_generated A V (fun i p => D.d (i+1) (D.d i p) = 0)
  · intro i
    simp
  · intro i a b ha hb
    simp only [map_add, ha, hb, add_zero]
  · intro i s a ha
    simp only [LinearMap.map_smul_of_tower, ha, smul_zero]
  · intro i a
    rw [D.on_base, D.on_base]
    have hd := DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom (A.complex.d_comp_d i (i+1) (i+1+1))) a
    change A.complex.d (i+1) (i+1+1) (A.complex.d i (i+1) a) = 0 at hd
    rw [hd, map_zero]
  · intro x
    rw [D.on_var, h]
  · exact derivative_sq_on_product A V D


theorem polynomialMul_coefficient (i j n : ℤ) (h : i+j=n)
    (a : A.complex.X i) (b : A.complex.X j) :
    polynomialMul A V i j n h (coefficient A V i a) (coefficient A V j b) =
      coefficient A V n (A.mul i j n h a b) := by
  classical
  change polynomialMul A V i j n h
    (homogeneousTerm A V i V.constant (r := i) (by simp) a)
    (homogeneousTerm A V j V.constant (r := j) (by simp) b) =
    homogeneousTerm A V n V.constant (r := n) (by simp) (A.mul i j n h a b)
  rw [polynomialMul_homogeneousTerm]
  have hp : V.Admissible (V.constant.val + V.constant.val) := by
    change V.Admissible (0 + 0)
    rw [add_zero]
    exact V.constant.prop
  rw [dite_eq_left hp, show (V.weight V.constant.val * j +
    V.inversions V.constant.val V.constant.val).negOnePow = 1 by
      change (V.weight 0 * j + V.inversions 0 0).negOnePow = 1
      simp, one_smul, mul_cast A h, homogeneousTerm_cast (hr := by simp [h])]
  apply homogeneousTerm_congr A V
  exact Subtype.ext (zero_add _)

section Model

variable {A V}
variable {dx : ∀ x, Polynomial A V (V.degree x + 1)} (D : Derivation A V dx)
variable (cycles : ∀ x, D.d (V.degree x+1) (dx x) = 0)

include cycles in
private theorem square_zero_morphism (i : ℤ) :
    ModuleCat.ofHom (D.d i) ≫ ModuleCat.ofHom (D.d (i+1)) = 0 := by
  apply ModuleCat.hom_ext
  exact LinearMap.ext (differentialSquaresToZero A V dx D cycles i)

def polynomialComplex : ModuleCochain.{u,v} k :=
  CochainComplex.of (fun i => ModuleCat.of k (Polynomial A V i))
    (fun i => ModuleCat.ofHom (D.d i)) (square_zero_morphism D cycles)

@[simp] theorem polynomialComplex_d (i : ℤ) :
    (polynomialComplex D cycles).d i (i+1) = ModuleCat.ofHom (D.d i) :=
  CochainComplex.of_d (X := fun i => ModuleCat.of k (Polynomial A V i)) (fun i => ModuleCat.ofHom (D.d i)) i

/-- The canonical nonpositive CDGA carried by the monomials and a
derivation whose prescribed values are cycles. -/
def polynomialCDGA : NonpositiveCDGA.{u,v} k where
  toCommDGAlgebra :=
    { toDGAlgebra :=
        { hom := fun _ _ => polynomialComplex D cycles
          comp := fun i j n h => polynomialMul A V i j n h
          id := fun _ => coefficient A V 0 A.one
          d_id := by
            intro _
            have he := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
              (polynomialComplex_d D cycles 0)) (coefficient A V 0 A.one)
            refine he.trans ?_
            change D.d 0 (coefficient A V 0 A.one) = 0
            rw [D.on_base]
            have hd : A.complex.d 0 (0+1) A.one = 0 := A.d_zero_apply A.one
            rw [hd, map_zero]
          id_comp := by intros; apply polynomialMul_one_left
          comp_id := by intros; apply polynomialMul_one_right
          assoc := by intros; apply polynomialMul_assoc
          leibniz := by
            intro _ _ _ i j n h a b
            rw [polynomialComplex_d, polynomialComplex_d, polynomialComplex_d]
            exact D.leibniz i j n h a b }
      graded_comm := polynomialMul_comm A V }
  nonpositive := polynomial_nonpositive A V

/-- The coefficient inclusion is a map of CDGAs. -/
def polynomialBase : A ⟶ polynomialCDGA D cycles where
  chainMap :=
    { f := fun i => ModuleCat.ofHom (coefficient A V i)
      comm' := by
        intro i j hij
        have hh : i+1 = j := hij
        subst j
        change ModuleCat.ofHom (coefficient A V i) ≫ (polynomialComplex D cycles).d i (i+1) =
          A.complex.d i (i+1) ≫ ModuleCat.ofHom (coefficient A V (i+1))
        rw [polynomialComplex_d]
        apply ModuleCat.hom_ext
        exact LinearMap.ext (D.on_base i) }
  map_one := rfl
  map_mul := by
    intro i j n h a b
    exact (polynomialMul_coefficient A V i j n h a b).symm

def polynomialPresentation : Presentation A V (polynomialBase D cycles) where
  component := fun _ => LinearEquiv.refl _ _
  map_one := rfl
  map_mul := fun _ _ _ _ _ _ => rfl
  map_base := fun _ _ => rfl

def polynomialStagedPresentation (S : Stages V)
    (earlier : ∀ x, UsesOnly A V (S.before (S.stage x)) (dx x)) :
    StagedPresentation A V (polynomialBase D cycles) where
  toPresentation := polynomialPresentation D cycles
  stages := S
  earlier := by
    intro x
    change UsesOnly A V (S.before (S.stage x))
      ((polynomialComplex D cycles).d (V.degree x) (V.degree x + 1) (variableTerm A V x))
    rw [polynomialComplex_d]
    change UsesOnly A V _ (D.d _ (variableTerm A V x))
    rw [D.on_var]
    exact earlier x

end Model


/-- With no generators, the constant coefficient contains the entire polynomial. -/
theorem coefficient_bijective_of_isEmpty [IsEmpty V.Index] (i : ℤ) :
    Function.Bijective (coefficient A V i) := by
  classical
  have he (m : V.Monomial) : m = V.constant := by
    apply Subtype.ext
    ext x
    exact isEmptyElim x
  have hdeg : i = i - V.weight V.constant.val := by rw [V.weight_constant, sub_zero]
  refine ⟨?_, ?_⟩
  · intro a b hab
    change term A V i V.constant (castDegree A.complex.X hdeg a) =
      term A V i V.constant (castDegree A.complex.X hdeg b) at hab
    have hh := term_injective A V i V.constant hab
    have := congrArg (castDegree A.complex.X hdeg.symm) hh
    simpa only [castDegree_cancel] using this
  · intro p
    refine ⟨castDegree A.complex.X hdeg.symm (p V.constant), DFinsupp.ext fun m => ?_⟩
    rw [he m]
    change (term A V i V.constant (castDegree A.complex.X hdeg
      (castDegree A.complex.X hdeg.symm (p V.constant)))) V.constant = _
    rw [castDegree_cancel]
    exact DirectSum.lof_apply k V.constant (p V.constant)

theorem emptyVariables : EmptyVariables.{u,v} := by
  intro k _ _ A P f V _ E
  have hc (i : ℤ) : Function.Bijective (f.chainMap.f i) := by
    have hfun : (f.chainMap.f i : A.complex.X i → P.complex.X i) =
        fun x => E.component i (coefficient A V i x) :=
      funext fun a => (E.map_base i a).symm
    rw [hfun]
    exact (E.component i).bijective.comp (coefficient_bijective_of_isEmpty A V i)
  have hloc (i : ℤ) : IsIso (f.chainMap.f i) :=
    (LinearEquiv.ofBijective (f.chainMap.f i).hom (hc i)).toModuleIso.isIso_hom
  have : IsIso f.chainMap := HomologicalComplex.Hom.isIso_of_components _
  let g : P.complex ⟶ A.complex := inv f.chainMap
  have hgf (i : ℤ) (x : P.complex.X i) : f.chainMap.f i (g.f i x) = x := by
    have h := congrArg (fun m : P.complex ⟶ P.complex => m.f i) (IsIso.inv_hom_id f.chainMap)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) x
  let F : P ⟶ A :=
    { chainMap := g
      map_one := (hc 0).1 (by rw [hgf, f.map_one])
      map_mul := fun i j n h x y => (hc n).1 (by
        rw [hgf, f.map_mul, hgf, hgf]) }
  refine ⟨⟨F, ?_, ?_⟩⟩
  · apply CommDGAlgebra.Hom.ext_chainMap
    exact IsIso.hom_inv_id f.chainMap
  · apply CommDGAlgebra.Hom.ext_chainMap
    exact IsIso.inv_hom_id f.chainMap

section Total

variable (B : CommDGAlgebra.{u,v} k)

private abbrev Part (i : ℤ) : Type v := B.complex.X i
private abbrev Total := DirectSum ℤ (Part B)

omit [CharZero k] in
private theorem castDegree_heq (X : ℤ → ModuleCat.{v} k) {i j : ℤ} (h : i = j) (a : X i) :
    HEq a (castDegree X h a) := by
  subst j
  rfl

private theorem mul_degree_cast {r s n : ℤ} (h : r+s=n)
    (a : Part B r) (b : Part B s) :
    B.mul r s n h a b = castDegree B.complex.X h (B.mul r s (r+s) rfl a b) := by
  subst n
  rfl

local instance totalOne : GradedMonoid.GOne (Part B) := ⟨B.one⟩
local instance totalMul : GradedMonoid.GMul (Part B) := ⟨fun {i j} a b => B.mul i j (i+j) rfl a b⟩

local instance totalMonoid : GradedMonoid.GMonoid (Part B) where
  toGOne := totalOne B
  toGMul := totalMul B
  one_mul := by
    rintro ⟨i, a⟩
    apply Sigma.ext (zero_add i)
    have hh := B.toDGAlgebra.id_comp i a
    change B.mul 0 i i (zero_add i) B.one a = a at hh
    rw [mul_degree_cast] at hh
    exact (castDegree_heq _ _ _).trans (heq_of_eq hh)
  mul_one := by
    rintro ⟨i, a⟩
    apply Sigma.ext (add_zero i)
    have hh := B.toDGAlgebra.comp_id i a
    change B.mul i 0 i (add_zero i) a B.one = a at hh
    rw [mul_degree_cast] at hh
    exact (castDegree_heq _ _ _).trans (heq_of_eq hh)
  mul_assoc := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨l, c⟩
    apply Sigma.ext (add_assoc i j l)
    have hh := B.toDGAlgebra.assoc i j l a b c
    change B.mul (i+j) l (i+j+l) rfl (B.mul i j (i+j) rfl a b) c =
      B.mul i (j+l) (i+j+l) (add_assoc i j l).symm a (B.mul j l (j+l) rfl b c) at hh
    rw [mul_degree_cast B (add_assoc i j l).symm] at hh
    exact (heq_of_eq hh).trans (castDegree_heq _ _ _).symm
local instance totalGradedRing : DirectSum.GRing (Part B) where
  toGMonoid := totalMonoid B
  mul_zero a := map_zero _
  zero_mul := by
    intro i j b
    change B.mul i j (i+j) rfl 0 b = 0
    simp only [map_zero, LinearMap.zero_apply]
  mul_add a b c := map_add _ _ _
  add_mul := by
    intro i j a b c
    change B.mul i j (i+j) rfl (a+b) c = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  natCast n := (n : B.DegreeZero)
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ
  intCast n := (n : B.DegreeZero)
  intCast_ofNat := Int.cast_natCast
  intCast_negSucc_ofNat := Int.cast_negSucc

private abbrev includePart (i : ℤ) : Part B i →ₗ[k] Total B := DirectSum.lof k ℤ _ i

private theorem includePart_cast {i j : ℤ} (h : i = j) (a : Part B i) :
    includePart B j (castDegree B.complex.X h a) = includePart B i a := by
  subst j
  rfl

private theorem includePart_mul {i j n : ℤ} (h : i+j=n) (a : Part B i) (b : Part B j) :
    includePart B n (B.mul i j n h a b) = includePart B i a * includePart B j b := by
  subst n
  exact (DirectSum.of_mul_of a b).symm

private theorem includePart_one : includePart B 0 B.one = 1 := rfl

private theorem includePart_comm {i j : ℤ} (a : Part B i) (b : Part B j) :
    includePart B i a * includePart B j b =
      (i*j).negOnePow • (includePart B j b * includePart B i a) := by
  rw [← includePart_mul B rfl, B.graded_comm, LinearMap.map_smul_of_tower, includePart_mul]

private theorem includePart_injective (i : ℤ) : Function.Injective (includePart B i) := by
  intro a b h
  have he := congrArg (fun z : Total B => z i) h
  simpa only [includePart, DirectSum.lof_apply] using he

private theorem includePart_odd_square {i : ℤ} (hi : Odd i) (a : Part B i) :
    includePart B i a * includePart B i a = 0 := by
  let z := includePart B i a * includePart B i a
  have hz : z = (-1 : ℤˣ) • z := by
    have hh := includePart_comm B a a
    rwa [Int.negOnePow_mul_self, Int.negOnePow_odd _ hi] at hh
  rw [Units.neg_smul, one_smul] at hz
  have ht : (2 : k) • z = 0 := by
    rw [two_smul, ← eq_neg_iff_add_eq_zero]
    exact hz
  exact (smul_eq_zero.mp ht).resolve_left (by exact two_ne_zero)



section Words

open Classical in
private def wordExponent (w : List V.Index) : V.Exponent := (w : Multiset V.Index).toFinsupp

private theorem wordExponent_nil : wordExponent V [] = 0 := map_zero _

private theorem wordExponent_cons (x : V.Index) (w : List V.Index) :
    wordExponent V (x :: w) = Finsupp.single x 1 + wordExponent V w := by
  classical
  ext y
  by_cases h : x = y
  · subst y; simp [wordExponent, Finsupp.add_apply, add_comm]
  · simp [wordExponent, Finsupp.add_apply, h]

private theorem wordExponent_append (x y : List V.Index) :
    wordExponent V (x ++ y) = wordExponent V x + wordExponent V y := by
  classical
  change Multiset.toFinsupp ((x : Multiset V.Index) + (y : Multiset V.Index)) = _
  exact map_add (Multiset.toFinsupp : Multiset V.Index ≃+ V.Exponent) _ _

private theorem wordExponent_perm {x y : List V.Index} (h : wordExponent V x = wordExponent V y) :
    x.Perm y := by
  classical
  exact Multiset.coe_eq_coe.mp (Multiset.toFinsupp.injective h)

private noncomputable def exponentWord (m : V.Exponent) : List V.Index :=
  m.toMultiset.toList

private theorem wordExponent_exponentWord (m : V.Exponent) :
    wordExponent V (exponentWord V m) = m := by
  classical
  simp [wordExponent, exponentWord]

private def wordInversions : List V.Index → ℤ
  | [] => 0
  | x :: w => V.inversions (Finsupp.single x 1) (wordExponent V w) + wordInversions w

private theorem wordInversions_append (x y : List V.Index) :
    wordInversions V (x ++ y) =
      wordInversions V x + wordInversions V y +
        V.inversions (wordExponent V x) (wordExponent V y) := by
  induction x with
  | nil => simp [wordInversions, wordExponent_nil]
  | cons x xs ih =>
    simp only [List.cons_append, wordInversions, wordExponent_cons, wordExponent_append,
      V.inversions_add_left, V.inversions_add_right, ih]
    ring

private theorem single_inversions (x y : V.Index) :
    V.inversions (Finsupp.single x 1) (Finsupp.single y 1) =
      if (V.normalOrder.toLT.lt y x) then V.degree x * V.degree y else 0 := by
  classical
  unfold Variables.inversions
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  · simp
  · split <;> simp
  · exact Finset.sum_eq_zero fun z _ => by dsimp; split <;> simp

private theorem swapped_words_sign (x y : V.Index) (w : List V.Index) (h : x ≠ y) :
    (wordInversions V (y :: x :: w)).negOnePow =
      (V.degree x * V.degree y).negOnePow * (wordInversions V (x :: y :: w)).negOnePow := by
  classical
  let := V.normalOrder
  simp only [← Int.negOnePow_add, Int.negOnePow_eq_iff, wordInversions, wordExponent_cons,
    V.inversions_add_right, single_inversions]
  rcases lt_or_gt_of_ne h with hxy | hyx
  · rw [ite_eq_left hxy, ite_eq_right (not_lt_of_gt hxy)]
    convert (Even.zero : Even (0 : ℤ)) using 1
    ring
  · rw [ite_eq_left hyx, ite_eq_right (not_lt_of_gt hyx)]
    convert (even_two_mul (-(V.degree x * V.degree y))) using 1
    ring

private def totalWord (x : ∀ a, Part B (V.degree a)) (w : List V.Index) : Total B :=
  (w.map fun a => includePart B _ (x a)).prod

private theorem totalWord_cons (x : ∀ a, Part B (V.degree a)) (a : V.Index) (w : List V.Index) :
    totalWord V B x (a :: w) = includePart B _ (x a) * totalWord V B x w := rfl

private theorem totalWord_append (x : ∀ a, Part B (V.degree a)) (w z : List V.Index) :
    totalWord V B x (w ++ z) = totalWord V B x w * totalWord V B x z := by
  simp [totalWord]

private def normalWord (x : ∀ a, Part B (V.degree a)) (w : List V.Index) : Total B :=
  (wordInversions V w).negOnePow • totalWord V B x w

private theorem wordExponent_eq_of_perm {s t : List V.Index} (h : s.Perm t) :
    wordExponent V s = wordExponent V t := by
  classical
  exact congrArg Multiset.toFinsupp (Multiset.coe_eq_coe.mpr h)

private theorem normalWord_eq_of_perm (x : ∀ a, Part B (V.degree a))
    {s t : List V.Index} (h : s.Perm t) :
    normalWord V B x s = normalWord V B x t := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    simp only [normalWord, wordInversions, Int.negOnePow_add, totalWord_cons] at ih ⊢
    simp only [wordExponent_eq_of_perm V h, ← smul_smul, ← mul_smul_comm, ih]
  | swap a b w =>
    by_cases hab : a = b
    · subst b
      rfl
    rw [normalWord, normalWord, swapped_words_sign V a b w hab]
    simp only [totalWord_cons]
    rw [← mul_assoc, includePart_comm B (x b) (x a), smul_mul_assoc, smul_smul]
    rw [mul_comm (V.degree b) (V.degree a), mul_assoc,
      mul_comm (wordInversions V (a :: b :: w)).negOnePow, ← mul_assoc,
      Int.units_mul_self, one_mul, mul_assoc]
  | trans _ _ ih ih' => exact ih.trans ih'

private theorem normalWord_append (x : ∀ a, Part B (V.degree a)) (s t : List V.Index) :
    normalWord V B x s * normalWord V B x t =
      (V.inversions (wordExponent V s) (wordExponent V t)).negOnePow • normalWord V B x (s++t) := by
  simp only [normalWord, wordInversions_append, Int.negOnePow_add, totalWord_append, smul_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hsign : (wordInversions V s).negOnePow * (wordInversions V t).negOnePow =
      (V.inversions (wordExponent V s) (wordExponent V t)).negOnePow *
        ((wordInversions V s).negOnePow * (wordInversions V t).negOnePow *
          (V.inversions (wordExponent V s) (wordExponent V t)).negOnePow) := by
    rw [mul_comm _ (_ * _ * _), mul_assoc, Int.units_mul_self, mul_one]
  exact congrArg (fun u : ℤˣ => u • (totalWord V B x s * totalWord V B x t)) hsign

private theorem normalWord_zero (x : ∀ a, Part B (V.degree a)) (s : List V.Index)
    (h : ¬ V.Admissible (wordExponent V s)) : normalWord V B x s = 0 := by
  classical
  rw [Variables.Admissible] at h
  push Not at h
  obtain ⟨a, ha, hn⟩ := h
  simp only [wordExponent, Multiset.toFinsupp_apply, Multiset.coe_count] at hn
  have hmem : a ∈ s := List.count_pos_iff.mp (by omega)
  have hmem' : a ∈ s.erase a := List.count_pos_iff.mp (by rw [List.count_erase_self]; omega)
  have hp := (List.perm_cons_erase hmem).trans ((List.perm_cons_erase hmem').cons a)
  rw [normalWord_eq_of_perm V B x hp, normalWord, totalWord_cons, totalWord_cons,
    ← mul_assoc, includePart_odd_square B ha, zero_mul, smul_zero]

private def wordDegree : List V.Index → ℤ
  | [] => 0
  | a :: w => V.degree a + wordDegree w

private theorem wordDegree_eq_weight (w : List V.Index) :
    wordDegree V w = V.weight (wordExponent V w) := by
  induction w with
  | nil => simp [wordDegree, wordExponent_nil]
  | cons a w ih =>
    simp only [wordDegree, ih, wordExponent_cons, map_add, Variables.weight,
      Finsupp.weight_single, one_smul]

private def wordHomogeneous (x : ∀ a, Part B (V.degree a)) :
    (w : List V.Index) → Part B (wordDegree V w)
  | [] => B.one
  | a :: w => B.mul (V.degree a) (wordDegree V w) _ rfl (x a) (wordHomogeneous x w)

private theorem includePart_wordHomogeneous (x : ∀ a, Part B (V.degree a))
    (w : List V.Index) :
    includePart B (wordDegree V w) (wordHomogeneous V B x w) = totalWord V B x w := by
  induction w with
  | nil => exact includePart_one B
  | cons a w ih =>
    change includePart B (V.degree a + wordDegree V w)
        (B.mul (V.degree a) (wordDegree V w) _ rfl (x a) (wordHomogeneous V B x w)) = _
    rw [includePart_mul, ih, totalWord_cons]

private def monomialValue (x : ∀ a, Part B (V.degree a)) (m : V.Exponent) :
    Part B (V.weight m) :=
  let w := exponentWord V m
  (wordInversions V w).negOnePow • castDegree B.complex.X
    ((wordDegree_eq_weight V w).trans (congrArg V.weight (wordExponent_exponentWord V m)))
    (wordHomogeneous V B x w)

private theorem includePart_monomialValue (x : ∀ a, Part B (V.degree a))
    (m : V.Exponent) (w : List V.Index) (hw : wordExponent V w = m) :
    includePart B (V.weight m) (monomialValue V B x m) = normalWord V B x w := by
  unfold monomialValue
  dsimp only
  rw [LinearMap.map_smul_of_tower, includePart_cast, includePart_wordHomogeneous]
  apply normalWord_eq_of_perm V B x
  exact wordExponent_perm V ((wordExponent_exponentWord V m).trans hw.symm)

private theorem monomialValue_zeroExponent (x : ∀ a, Part B (V.degree a)) :
    includePart B (V.weight 0) (monomialValue V B x 0) = 1 := by
  rw [includePart_monomialValue V B x 0 [] (wordExponent_nil V)]
  exact one_smul _ _

private theorem monomialValue_singleExponent (x : ∀ a, Part B (V.degree a)) (a : V.Index) :
    includePart B (V.weight (V.singleton a).val) (monomialValue V B x (V.singleton a).val) =
      includePart B (V.degree a) (x a) := by
  have hw : wordExponent V [a] = (V.singleton a).val := by
    rw [wordExponent_cons, wordExponent_nil, add_zero]
    rfl
  rw [includePart_monomialValue V B x _ [a] hw]
  simp [normalWord, wordInversions, wordExponent_nil, totalWord]

private theorem monomialValue_mul (x : ∀ a, Part B (V.degree a)) (m p : V.Exponent) :
    includePart B (V.weight m) (monomialValue V B x m) *
        includePart B (V.weight p) (monomialValue V B x p) =
      (V.inversions m p).negOnePow • includePart B (V.weight (m+p)) (monomialValue V B x (m+p)) := by
  let w := exponentWord V m
  let z := exponentWord V p
  have hw := wordExponent_exponentWord V m
  have hz := wordExponent_exponentWord V p
  have hwz : wordExponent V (w++z) = m+p := by
    rw [wordExponent_append, hw, hz]
  rw [includePart_monomialValue V B x m w hw, includePart_monomialValue V B x p z hz,
    includePart_monomialValue V B x (m+p) (w++z) hwz, normalWord_append, hw, hz]

private theorem monomialValue_invalid (x : ∀ a, Part B (V.degree a)) (m : V.Exponent)
    (hm : ¬ V.Admissible m) :
    includePart B (V.weight m) (monomialValue V B x m) = 0 := by
  rw [includePart_monomialValue V B x m (exponentWord V m) (wordExponent_exponentWord V m)]
  apply normalWord_zero
  rwa [wordExponent_exponentWord]

private def evalPolynomial (f : ∀ i, A.complex.X i →ₗ[k] Part B i)
    (x : ∀ a, Part B (V.degree a)) (n : ℤ) : Polynomial A V n →ₗ[k] Part B n := by
  classical
  exact DirectSum.toModule k _ _ fun m =>
    ((B.mul (n - V.weight m.val) (V.weight m.val) n (by omega)).flip
      (monomialValue V B x m.val)).comp (f _)

private theorem evalPolynomial_homogeneousTerm
    (f : ∀ i, A.complex.X i →ₗ[k] Part B i) (x : ∀ a, Part B (V.degree a))
    (n : ℤ) (m : V.Monomial) {r : ℤ} (hr : r + V.weight m.val = n) (a : A.complex.X r) :
    includePart B n (evalPolynomial A V B f x n (homogeneousTerm A V n m hr a)) =
      includePart B r (f r a) * includePart B (V.weight m.val) (monomialValue V B x m.val) := by
  classical
  obtain rfl : r = n - V.weight m.val := by omega
  rw [homogeneousTerm_self]
  simp only [evalPolynomial, term, DirectSum.toModule_lof, LinearMap.comp_apply,
    LinearMap.flip_apply, includePart_mul]

private theorem evalPolynomial_multiplicative_terms
    (f : ∀ i, A.complex.X i →ₗ[k] Part B i) (x : ∀ a, Part B (V.degree a))
    (hf : ∀ (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (b : A.complex.X j),
      f n (A.mul i j n h a b) = B.mul i j n h (f i a) (f j b))
    (i j n : ℤ) (h : i+j=n) (m p : V.Monomial) {r s : ℤ}
    (hr : r + V.weight m.val = i) (hs : s + V.weight p.val = j)
    (a : A.complex.X r) (b : A.complex.X s) :
    evalPolynomial A V B f x n (polynomialMul A V i j n h
      (homogeneousTerm A V i m hr a) (homogeneousTerm A V j p hs b)) =
    B.mul i j n h (evalPolynomial A V B f x i (homogeneousTerm A V i m hr a))
      (evalPolynomial A V B f x j (homogeneousTerm A V j p hs b)) := by
  classical
  apply includePart_injective B n
  rw [includePart_mul, evalPolynomial_homogeneousTerm, evalPolynomial_homogeneousTerm,
    polynomialMul_homogeneousTerm]
  rw [mul_assoc, ← mul_assoc (includePart B (V.weight m.val) (monomialValue V B x m.val)),
    includePart_comm B (monomialValue V B x m.val) (f s b),
    smul_mul_assoc, mul_smul_comm, mul_assoc (includePart B s (f s b)), ← mul_assoc,
    monomialValue_mul]
  by_cases hp : V.Admissible (m.val + p.val)
  · rw [dite_eq_left hp, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      evalPolynomial_homogeneousTerm, hf, includePart_mul, mul_smul_comm,
      smul_smul, ← Int.negOnePow_add]
  · rw [dite_eq_right hp, map_zero, map_zero, monomialValue_invalid V B x _ hp,
      smul_zero, mul_zero, smul_zero]

theorem gradedUniversalProperty : GradedUniversalProperty.{u,v} := by
  intro k _ _ A V B f hone hmul x
  let F := evalPolynomial A V B f x
  have hb (i : ℤ) (a : A.complex.X i) : F i (coefficient A V i a) = f i a := by
    apply includePart_injective B i
    change includePart B i (F i (homogeneousTerm A V i V.constant (r := i) (by simp) a)) = _
    change includePart B i (evalPolynomial A V B f x i _) = _
    rw [evalPolynomial_homogeneousTerm, monomialValue_zeroExponent, mul_one]
  have hx (a : V.Index) : F (V.degree a) (variableTerm A V a) = x a := by
    apply includePart_injective B (V.degree a)
    change includePart B _ (F _ (homogeneousTerm A V _ (V.singleton a) (r := 0) (by simp) A.one)) = _
    change includePart B _ (evalPolynomial A V B f x _ _) = _
    rw [evalPolynomial_homogeneousTerm, monomialValue_singleExponent, hone, includePart_one, one_mul]
  have hm (i j n : ℤ) (h : i+j=n) (a : Polynomial A V i) (b : Polynomial A V j) :
      F n (polynomialMul A V i j n h a b) = B.mul i j n h (F i a) (F j b) := by
    induction a using polynomial_induction A V with
    | zero => simp
    | add a a' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | single m a =>
      induction b using polynomial_induction A V with
      | zero => simp
      | add b b' h h' => simp only [map_add, h, h']
      | single p b =>
        rw [← homogeneousTerm_self A V i m, ← homogeneousTerm_self A V j p]
        exact evalPolynomial_multiplicative_terms A V B f x hmul i j n h m p _ _ a b
  exact ⟨{ default := ⟨F, hm, hb, hx⟩
           uniq := fun _ => (gradedLift_unique A V B f x).elim _ _ }⟩

end Words

end Total

/-- The monomial algebra equipped with zero differential, for use in the
graded universal property. -/
def polynomialGradedAlgebra : NonpositiveCDGA.{u,v} k where
  toCommDGAlgebra :=
    { toDGAlgebra :=
        { hom := fun _ _ => { X := fun i => ModuleCat.of k (Polynomial A V i), d := fun _ _ => 0 }
          comp := fun i j n h => polynomialMul A V i j n h
          id := fun _ => coefficient A V 0 A.one
          d_id := by intros; rfl
          id_comp := by intros; apply polynomialMul_one_left
          comp_id := by intros; apply polynomialMul_one_right
          assoc := by intros; apply polynomialMul_assoc
          leibniz := by
            intros
            simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero] }
      graded_comm := polynomialMul_comm A V }
  nonpositive := polynomial_nonpositive A V

section SquareZero

variable (B : CommDGAlgebra.{u,v} k)

private abbrev DualPart (i : ℤ) : Type v := B.complex.X i × B.complex.X (i+1)

private def dualMul (i j n : ℤ) (h : i+j=n) :
    DualPart B i →ₗ[k] DualPart B j →ₗ[k] DualPart B n :=
  let fst (r : ℤ) := LinearMap.fst k (B.complex.X r) (B.complex.X (r+1))
  let snd (r : ℤ) := LinearMap.snd k (B.complex.X r) (B.complex.X (r+1))
  let first := ((B.mul i j n h).compl₂ (fst j)).comp (fst i)
  let second := ((B.mul (i+1) j (n+1) (by omega)).compl₂ (fst j)).comp (snd i) +
    i.negOnePow • (((B.mul i (j+1) (n+1) (by omega)).compl₂ (snd j)).comp (fst i))
  { toFun := fun a => (first a).prod (second a)
    map_add' := fun a b => LinearMap.ext fun c => by
      simp only [LinearMap.prod_apply, Function.prod_apply, map_add, LinearMap.add_apply, Prod.mk_add_mk]
    map_smul' := fun r a => LinearMap.ext fun b => by
      simp only [LinearMap.prod_apply, Function.prod_apply, map_smul, LinearMap.smul_apply, Prod.smul_mk, RingHom.id_apply] }

private theorem mul_assoc_at {i j l p q n : ℤ}
    (hp : i+j=p) (hq : j+l=q) (hn : p+l=n)
    (a : B.complex.X i) (b : B.complex.X j) (c : B.complex.X l) :
    B.mul p l n hn (B.mul i j p hp a b) c =
      B.mul i q n (by omega) a (B.mul j l q hq b c) := by
  subst p; subst q; subst n
  exact B.toDGAlgebra.assoc i j l a b c

private theorem dualMul_assoc (i j l : ℤ) (a : DualPart B i) (b : DualPart B j) (c : DualPart B l) :
    dualMul B (i+j) l (i+j+l) rfl (dualMul B i j (i+j) rfl a b) c =
      dualMul B i (j+l) (i+j+l) (add_assoc i j l).symm a (dualMul B j l (j+l) rfl b c) := by
  apply Prod.ext
  · exact B.toDGAlgebra.assoc i j l a.1 b.1 c.1
  · change
      B.mul (i+j+1) l (i+j+l+1) _
        (B.mul (i+1) j (i+j+1) _ a.2 b.1 + i.negOnePow • B.mul i (j+1) (i+j+1) _ a.1 b.2) c.1 +
        (i+j).negOnePow • B.mul (i+j) (l+1) (i+j+l+1) _ (B.mul i j (i+j) rfl a.1 b.1) c.2 =
      B.mul (i+1) (j+l) (i+j+l+1) _ a.2 (B.mul j l (j+l) rfl b.1 c.1) +
        i.negOnePow • B.mul i (j+l+1) (i+j+l+1) _ a.1
          (B.mul (j+1) l (j+l+1) _ b.2 c.1 + j.negOnePow • B.mul j (l+1) (j+l+1) _ b.1 c.2)
    simp only [map_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
      smul_add, smul_smul, ← Int.negOnePow_add]
    rw [mul_assoc_at B (i := i+1) (j := j) (l := l) (q := j+l) (hq := rfl),
      mul_assoc_at B (i := i) (j := j+1) (l := l) (q := j+l+1) (hq := by omega),
      mul_assoc_at B (i := i) (j := j) (l := l+1) (q := j+l+1) (hq := by omega)]
    exact add_assoc _ _ _

private theorem dualMul_comm (i j n : ℤ) (h : i+j=n) (a : DualPart B i) (b : DualPart B j) :
    dualMul B i j n h a b = (i*j).negOnePow • dualMul B j i n ((add_comm j i).trans h) b a := by
  apply Prod.ext
  · exact B.graded_comm i j n h a.1 b.1
  · change
      B.mul (i+1) j (n+1) _ a.2 b.1 + i.negOnePow • B.mul i (j+1) (n+1) _ a.1 b.2 =
        (i*j).negOnePow • (B.mul (j+1) i (n+1) _ b.2 a.1 +
          j.negOnePow • B.mul j (i+1) (n+1) _ b.1 a.2)
    rw [B.graded_comm (j+1) i _ _ b.2 a.1, B.graded_comm j (i+1) _ _ b.1 a.2]
    simp only [smul_add, smul_smul, ← Int.negOnePow_add]
    have hi : (i*j + (j+1)*i).negOnePow = i.negOnePow := by
      rw [show i*j + (j+1)*i = 2*(i*j)+i by ring, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]
    have hj : (i*j + (j + j*(i+1))).negOnePow = 1 := by
      rw [show i*j + (j + j*(i+1)) = 2*(i*j+j) by ring, Int.negOnePow_two_mul]
    rw [hi, hj, one_smul]
    exact add_comm _ _

/-- The graded square-zero algebra with an odd parameter of degree -1.
In the pair (a,b), the parameter is written on the left of b. -/
private def dualAlgebra : CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => { X := fun i => ModuleCat.of k (DualPart B i), d := fun _ _ => 0 }
      comp := fun i j n h => dualMul B i j n h
      id := fun _ => (B.one, 0)
      d_id := by intros; rfl
      id_comp := by
        intro _ _ i a
        apply Prod.ext
        · exact B.toDGAlgebra.id_comp i a.1
        · change B.mul (0+1) i (i+1) _ 0 a.1 + (0 : ℤ).negOnePow •
            B.mul 0 (i+1) (i+1) _ B.one a.2 = a.2
          simpa only [map_zero, LinearMap.zero_apply, zero_add, Int.negOnePow_zero, one_smul]
            using B.toDGAlgebra.id_comp (i+1) a.2
      comp_id := by
        intro _ _ i a
        apply Prod.ext
        · exact B.toDGAlgebra.comp_id i a.1
        · change B.mul (i+1) 0 (i+1) _ a.2 B.one + i.negOnePow •
            B.mul i (0+1) (i+1) _ a.1 0 = a.2
          simpa only [map_zero, smul_zero, add_zero] using B.toDGAlgebra.comp_id (i+1) a.2
      assoc := by intros; apply dualMul_assoc
      leibniz := by
        intros
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero] }
  graded_comm := dualMul_comm B

theorem derivationExtension : DerivationExtension.{u,v} := by
  intro k _ _ A V dx
  let B := (polynomialGradedAlgebra A V).toCommDGAlgebra
  let f (i : ℤ) : A.complex.X i →ₗ[k] (dualAlgebra B).complex.X i :=
    (coefficient A V i).prod ((coefficient A V (i+1)).comp (A.complex.d i (i+1)).hom)
  have hone : f 0 A.one = (dualAlgebra B).one := by
    apply Prod.ext
    · rfl
    · change coefficient A V (0+1) (A.complex.d 0 (0+1) A.one) = 0
      have hd : A.complex.d 0 (0+1) A.one = 0 := A.d_zero_apply A.one
      rw [hd, map_zero]
  have hmul (i j n : ℤ) (h : i+j=n) (a : A.complex.X i) (b : A.complex.X j) :
      f n (A.mul i j n h a b) = (dualAlgebra B).mul i j n h (f i a) (f j b) := by
    apply Prod.ext
    · exact (polynomialMul_coefficient A V i j n h a b).symm
    · change coefficient A V (n+1) (A.complex.d n (n+1) (A.mul i j n h a b)) =
        polynomialMul A V (i+1) j (n+1) _ (coefficient A V (i+1) (A.complex.d i (i+1) a))
          (coefficient A V j b) +
        i.negOnePow • polynomialMul A V i (j+1) (n+1) _ (coefficient A V i a)
          (coefficient A V (j+1) (A.complex.d j (j+1) b))
      simp only [polynomialMul_coefficient]
      rw [A.toDGAlgebra.leibniz, map_add, LinearMap.map_smul_of_tower]
  obtain ⟨F⟩ := gradedUniversalProperty A V (dualAlgebra B) f hone hmul
    (fun x => (variableTerm A V x, dx x))
  let L := F.default
  let first (i : ℤ) : Polynomial A V i →ₗ[k] Polynomial A V i :=
    (LinearMap.fst k (Polynomial A V i) (Polynomial A V (i+1))).comp (L.component i)
  have hfirst (i : ℤ) (a : Polynomial A V i) : first i a = a := by
    apply polynomial_generated A V (fun i p => first i p = p)
    · intro i
      exact map_zero _
    · intro i x y hx hy
      rw [map_add, hx, hy]
    · intro i s x hx
      rw [LinearMap.map_smul_of_tower, hx]
    · intro i a
      change (L.component i (coefficient A V i a)).1 = _
      rw [L.map_base]
      rfl
    · intro x
      change (L.component (V.degree x) (variableTerm A V x)).1 = _
      rw [L.map_var]
    · intro i j n h a b ha hb
      change (L.component n (polynomialMul A V i j n h a b)).1 = _
      rw [L.map_mul]
      change polynomialMul A V i j n h (first i a) (first j b) = _
      rw [ha, hb]
  let D : Derivation A V dx :=
    { d := fun i =>
        (LinearMap.snd k (Polynomial A V i) (Polynomial A V (i+1))).comp (L.component i)
      leibniz := by
        intro i j n h a b
        change (L.component n (polynomialMul A V i j n h a b)).2 = _
        rw [L.map_mul]
        change polynomialMul A V (i+1) j (n+1) _ (L.component i a).2 (first j b) +
          i.negOnePow • polynomialMul A V i (j+1) (n+1) _ (first i a) (L.component j b).2 = _
        rw [hfirst, hfirst]
        rfl
      on_base := by
        intro i a
        change (L.component i (coefficient A V i a)).2 = _
        rw [L.map_base]
        rfl
      on_var := by
        intro x
        change (L.component (V.degree x) (variableTerm A V x)).2 = _
        rw [L.map_var] }
  exact ⟨{ default := D, uniq := fun _ => (derivation_unique A V dx).elim _ _ }⟩

end SquareZero

section Stages

variable {A V}
variable {T : Set V.Index}

theorem UsesOnly.zero (i : ℤ) : UsesOnly A V T (0 : Polynomial A V i) := by
  intro m hm
  exact (hm (DFinsupp.zero_apply m)).elim

theorem UsesOnly.add {i : ℤ} {a b : Polynomial A V i}
    (ha : UsesOnly A V T a) (hb : UsesOnly A V T b) : UsesOnly A V T (a+b) := by
  classical
  intro m hm
  by_cases h : a m = 0
  · apply hb m
    simpa only [DirectSum.add_apply, h, zero_add] using hm
  · exact ha m h

theorem UsesOnly.smul {i : ℤ} (r : k) {a : Polynomial A V i}
    (ha : UsesOnly A V T a) : UsesOnly A V T (r • a) := by
  intro m hm
  apply ha m
  intro h
  exact hm (by rw [DirectSum.smul_apply, h, smul_zero])

theorem UsesOnly.sign {i : ℤ} (r : ℤˣ) {a : Polynomial A V i}
    (ha : UsesOnly A V T a) : UsesOnly A V T (r • a) := by
  intro m hm
  apply ha m
  intro h
  exact hm (by
    change ((r : ℤ) • a) m = 0
    change (r : ℤ) • a m = 0
    rw [h, smul_zero])

theorem UsesOnly.mono {U : Set V.Index} (h : T ⊆ U)
    {i : ℤ} {p : Polynomial A V i} (hp : UsesOnly A V T p) : UsesOnly A V U p :=
  fun m hm x hx => h (hp m hm x hx)

theorem term_usesOnly {i : ℤ} (m : V.Monomial) (a : Coefficient A V i m)
    (h : ∀ x ∈ m.val.support, x ∈ T) : UsesOnly A V T (term A V i m a) := by
  classical
  intro p hp
  have hp' : p = m := by
    by_contra hne
    exact hp (DFinsupp.single_eq_of_ne hne)
  simpa only [hp'] using h

theorem coefficient_usesOnly (i : ℤ) (a : A.complex.X i) :
    UsesOnly A V T (coefficient A V i a) := by
  apply term_usesOnly
  simp

theorem variable_usesOnly (x : V.Index) (hx : x ∈ T) :
    UsesOnly A V T (variableTerm A V x) := by
  apply term_usesOnly
  classical
  simpa [Variables.singleton] using hx

theorem UsesOnly.mul {i j n : ℤ} (h : i+j=n)
    {a : Polynomial A V i} {b : Polynomial A V j}
    (ha : UsesOnly A V T a) (hb : UsesOnly A V T b) :
    UsesOnly A V T (polynomialMul A V i j n h a b) := by
  classical
  apply polynomial_induction_on_support A V T _ _ _ _ a ha
  · simp only [map_zero, LinearMap.zero_apply]
    exact UsesOnly.zero n
  · intro m a hm
    apply polynomial_induction_on_support A V T _ _ _ _ b hb
    · rw [map_zero]
      exact UsesOnly.zero n
    · intro p b hp
      rw [polynomialMul_term]
      unfold termProduct
      split
      · apply UsesOnly.sign
        apply term_usesOnly
        intro x hx
        rcases Finset.mem_union.mp (Finsupp.support_add hx) with hxm | hxp
        · exact hm x hxm
        · exact hp x hxp
      · exact UsesOnly.zero n
    · intro x y hx hy
      rw [map_add]
      exact hx.add hy
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply]
    exact hx.add hy

/-- The graded pieces of the subalgebra of earlier variables. -/
def stagePart (S : Stages V) (a : S.Stage) (i : ℤ) : Submodule k (Polynomial A V i) where
  carrier := {p | UsesOnly A V (S.before a) p}
  zero_mem' := UsesOnly.zero i
  add_mem' := fun hx hy => UsesOnly.add hx hy
  smul_mem' := UsesOnly.smul

theorem derivationLocality : DerivationLocality.{u,v} := by
  intro k _ _ A V T dx dy D E h
  apply polynomial_generated_on A V T (fun i p => D.d i p = E.d i p)
  · intro i
    simp
  · intro i a b ha hb
    simp only [map_add, ha, hb]
  · intro i s a ha
    simp only [LinearMap.map_smul_of_tower, ha]
  · intro i a
    rw [D.on_base, E.on_base]
  · intro x hx
    rw [D.on_var, E.on_var, h x hx]
  · intro i j n h a b ha hb
    rw [D.leibniz, E.leibniz, ha, hb]

theorem stageDifferential : StageDifferential.{u,v} := by
  intro k _ _ A V S dx D hd a i p hp
  refine (polynomial_generated_on A V (S.before a)
    (fun j q => UsesOnly A V (S.before a) q ∧ UsesOnly A V (S.before a) (D.d j q))
    ?_ ?_ ?_ ?_ ?_ ?_ i p hp).2
  · intro i
    exact ⟨UsesOnly.zero i, by rw [map_zero]; exact UsesOnly.zero (i+1)⟩
  · intro i p q hp hq
    exact ⟨hp.1.add hq.1, by rw [map_add]; exact hp.2.add hq.2⟩
  · intro i s p hp
    exact ⟨hp.1.sign s, by rw [LinearMap.map_smul_of_tower]; exact hp.2.sign s⟩
  · intro i v
    exact ⟨coefficient_usesOnly i v, by rw [D.on_base]; exact coefficient_usesOnly _ _⟩
  · intro x hx
    refine ⟨variable_usesOnly x hx, ?_⟩
    rw [D.on_var]
    exact (hd x).mono fun _ hy => lt_trans hy hx
  · intro i j n h p q hp hq
    refine ⟨hp.1.mul h hq.1, ?_⟩
    rw [D.leibniz]
    exact (hp.2.mul _ hq.1).add ((hp.1.mul _ hq.2).sign _)

/-- Extend assigned homogeneous values to a derivation on the monomial algebra. -/
def extendDerivation (dx : ∀ x, Polynomial A V (V.degree x+1)) : Derivation A V dx :=
  (Classical.choice (derivationExtension A V dx)).default

theorem earlierCycles_iff (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x+1))
    (earlier : ∀ x, UsesOnly A V (S.before (S.stage x)) (dx x)) :
    EarlierCycles A V S dx ↔ ∀ x, (extendDerivation dx).d (V.degree x+1) (dx x) = 0 := by
  constructor
  · intro h x
    exact h x dx (extendDerivation dx) fun _ _ => rfl
  · intro h x dy D hdy
    rw [derivationLocality A V (S.before (S.stage x)) dy dx D (extendDerivation dx) hdy _ _
      (earlier x)]
    exact h x

theorem stagedDifferentialExtension : StagedDifferentialExtension.{u,v} := by
  intro k _ _ A V S dx earlier cycles
  let D := extendDerivation dx
  have hc : ∀ x, D.d (V.degree x+1) (dx x) = 0 := fun x =>
    cycles x dx D (fun _ _ => rfl)
  refine ⟨D, ⟨differentialSquaresToZero A V dx D hc, polynomialCDGA D hc,
    polynomialBase D hc, polynomialStagedPresentation D hc S earlier, rfl, ?_⟩, ?_⟩
  · intro i p
    change D.d i p = (polynomialComplex D hc).d i (i+1) p
    rw [polynomialComplex_d]
    rfl
  · intro E _
    exact (derivation_unique A V dx).elim _ _

/-- The staged extension with its prescribed differential. -/
def stagedAlgebra (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x+1))
    (cycles : EarlierCycles A V S dx) : NonpositiveCDGA.{u,v} k :=
  polynomialCDGA (extendDerivation dx) (fun x => cycles x dx _ fun _ _ => rfl)

def stagedBase (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x+1))
    (cycles : EarlierCycles A V S dx) : A ⟶ stagedAlgebra S dx cycles :=
  polynomialBase (extendDerivation dx) (fun x => cycles x dx _ fun _ _ => rfl)

def stagedPresentation (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x+1))
    (earlier : ∀ x, UsesOnly A V (S.before (S.stage x)) (dx x)) (cycles : EarlierCycles A V S dx) :
    StagedPresentation A V (stagedBase S dx cycles) :=
  polynomialStagedPresentation (extendDerivation dx) (fun x => cycles x dx _ fun _ _ => rfl)
    S earlier

theorem staged_isSemifree (S : Stages V) (dx : ∀ x, Polynomial A V (V.degree x+1))
    (earlier : ∀ x, UsesOnly A V (S.before (S.stage x)) (dx x)) (cycles : EarlierCycles A V S dx) :
    IsSemifree A (stagedBase S dx cycles) :=
  ⟨V, ⟨stagedPresentation S dx earlier cycles⟩⟩

theorem empty_staged_base_isIso [IsEmpty V.Index] (S : Stages V)
    (dx : ∀ x, Polynomial A V (V.degree x+1)) (cycles : EarlierCycles A V S dx) :
    IsIso (stagedBase S dx cycles) :=
  emptyVariables _ V (polynomialPresentation _ _)

end Stages

theorem monomialExpansion : MonomialExpansion.{u,v} := by
  classical
  intro k _ _ A V i p
  exact DirectSum.sum_support_of p

theorem powersOfAVariable : PowersOfAVariable.{v} := by
  classical
  intro V x r
  change (∀ y, Odd (V.degree y) → Finsupp.single x r y ≤ 1) ↔ _
  constructor
  · intro h hx
    simpa only [Finsupp.single_eq_same] using h x hx
  · intro h y hy
    by_cases hxy : x = y
    · subst y
      simpa only [Finsupp.single_eq_same] using h hy
    · simp [Finsupp.single_eq_of_ne (Ne.symm hxy)]

theorem oddVariableSquare : OddVariableSquare.{u,v} := by
  classical
  intro k _ _ A V x hx
  rw [variableTerm, polynomialMul_term]
  unfold termProduct
  have hn : ¬ V.Admissible ((V.singleton x).val + (V.singleton x).val) := by
    intro h
    have hs := h x hx
    change (Finsupp.single x (1 : ℕ) + Finsupp.single x (1 : ℕ)) x ≤ 1 at hs
    simp at hs
  rw [dite_eq_right hn]
  rfl

theorem continuousLimitStages : ContinuousLimitStages.{u,v} := by
  intro k _ _ A V S a ha
  apply continuousStages A V S a
  · exact ha.nonempty_Iio
  · intro x hx
    exact (ha.lt_iff_nonempty_Ioo.mp hx)

end
end DerivedFormalization.Affine.Semifree

namespace DerivedFormalization

abbrev SemifreeVariables := Affine.Semifree.Variables

abbrev SemifreeMonomial (V : SemifreeVariables.{v}) := V.Monomial

abbrev SemifreePolynomial {k : Type u} [Field k] [CharZero k]
    (A : Affine.NonpositiveCDGA.{u,v} k) (V : SemifreeVariables.{v}) (i : ℤ) :=
  Affine.Semifree.Polynomial A V i

abbrev SemifreeStages (V : SemifreeVariables.{v}) := Affine.Semifree.Stages V

abbrev SemifreePresentation {k : Type u} [Field k] [CharZero k]
    {A P : Affine.NonpositiveCDGA.{u,v} k} (V : SemifreeVariables.{v}) (f : A ⟶ P) :=
  Affine.Semifree.StagedPresentation A V f

abbrev IsSemifreeExtension {k : Type u} [Field k] [CharZero k]
    {A P : Affine.NonpositiveCDGA.{u,v} k} (f : A ⟶ P) : Prop :=
  Affine.Semifree.IsSemifree A f

end DerivedFormalization
