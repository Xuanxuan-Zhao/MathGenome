import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.AssociatedGraded
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.GradedComparison

namespace AdvCommAlg.RegularSequence.AssociatedGraded
noncomputable section
open scoped TensorProduct
open P103.Rees GradedComparison GradedComparison.Core Core
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (x : List R)

/-- The algebraic coefficient criterion implies vanishing of every homogeneous
kernel element of the exact canonical comparison. -/
lemma homogeneous_kernel_eq_zero (hc : HomogeneousCoefficients M x)
    (n : ℕ) (p : GradedComparison.Core.PolynomialModule M x)
    (hp : PolynomialHomogeneous M x n p)
    (hzero : GradedComparison.comparison M x p = 0) : p = 0 := by
  classical
  let c := polynomialCoefficients M x p
  let s := c.support
  choose m hm using fun d =>
    (sequenceIdeal x • (⊤ : Submodule R M)).mkQ_surjective (c d)
  have hd : ∀ d ∈ s, d.degree = n := fun d hd => hp d (Finsupp.mem_support_iff.mp hd)
  have hexp : p = ∑ d ∈ s, MvPolynomial.monomial d 1 ⊗ₜ Submodule.Quotient.mk (m d) := by
    rw [polynomial_expansion M x p]
    change (∑ d ∈ s, MvPolynomial.monomial d 1 ⊗ₜ c d) = _
    apply Finset.sum_congr rfl
    intro d _
    rw [← hm d]
    rfl
  have heval : (∑ d ∈ s, monomialValue x d • m d) ∈
      (sequenceIdeal x ^ (n + 1) • (⊤ : Submodule R M)) := by
    apply (moduleClass_eq_zero_iff (sequenceIdeal x) M n
      (homogeneousEvaluation M x n s hd m)).mp
    rw [← comparison_homogeneous_sum M x n s hd m, ← hexp]
    exact hzero
  have hcoeff := hc n s hd m heval
  rw [hexp]
  apply Finset.sum_eq_zero
  intro d hd'
  rw [(Submodule.Quotient.mk_eq_zero _).mpr (hcoeff d hd'), TensorProduct.tmul_zero]

/-- Homogeneous projections detect the entire kernel, so no separation of M
or its filtration is needed. -/
lemma comparison_injective_of_coefficients (hc : HomogeneousCoefficients M x) :
    Function.Injective (GradedComparison.comparison M x) := by
  suffices hker : ∀ p, GradedComparison.comparison M x p = 0 → p = 0 by
    intro p q hpq
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hpq, sub_self]
  intro p hp
  apply (polynomialCoefficients M x).injective
  ext d
  have hz : homogeneousPart M x d.degree p = 0 :=
    homogeneous_kernel_eq_zero M x hc d.degree _
      (homogeneousPart_homogeneous M x d.degree p) (by
        rw [comparison_homogeneousPart, hp, map_zero])
  have h := congrArg (fun q => polynomialCoefficients M x q d) hz
  simpa [homogeneousPart] using h

/-- A bijective canonical comparison has a graded inverse even when the
coefficient module is zero (proper quasi-regularity is unnecessary). -/
lemma homogeneous_iff_of_injective
    (hinj : Function.Injective (GradedComparison.comparison M x))
    (n : ℕ) (p : GradedComparison.Core.PolynomialModule M x) :
    PolynomialHomogeneous M x n p ↔
      GradedComparison.comparison M x p ∈ modulePiece (sequenceIdeal x) M n := by
  constructor
  · exact comparison_homogeneous M x n p
  · intro hp
    obtain ⟨q, hq, he⟩ := comparison_degreewise_surjective M x n
      (GradedComparison.comparison M x p) hp
    exact hinj he ▸ hq

/-- Conversely, injectivity detects every coefficient of a lifted homogeneous
relation. This also supplies the empty-list case without a properness assumption. -/
lemma coefficients_of_comparison_injective
    (hi : Function.Injective (GradedComparison.Core.comparison M x)) :
    HomogeneousCoefficients M x := by
  classical
  intro n s hd m hm d hd'
  let p : GradedComparison.Core.PolynomialModule M x :=
    ∑ e ∈ s, MvPolynomial.monomial e 1 ⊗ₜ Submodule.Quotient.mk (m e)
  have hp : GradedComparison.comparison M x p = 0 := by
    rw [show p = _ from rfl, comparison_homogeneous_sum M x n s hd m]
    exact (moduleClass_eq_zero_iff (sequenceIdeal x) M n _).mpr hm
  have hp0 : p = 0 := hi (hp.trans (map_zero _).symm)
  have hcoeff := congrArg (fun q => polynomialCoefficients M x q d) hp0
  apply (Submodule.Quotient.mk_eq_zero _).mp
  simpa [p, polynomialCoefficients, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
    MvPolynomial.basisMonomials, MvPolynomial.coeff_monomial, hd'] using hcoeff

/-- Finite module-valued polynomials whose coefficients belong to `N` and
whose monomials have degree `n`. -/
def homogeneousRelations (N : Submodule R M) (n : ℕ) :
    Submodule R ((Fin x.length →₀ ℕ) →₀ M) where
  carrier := {p | (∀ d, p d ∈ N) ∧ (∀ d, p d ≠ 0 → d.degree = n)}
  zero_mem' := by simp
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    refine ⟨fun d => N.add_mem (hp d) (hq d), ?_⟩
    intro d hd
    by_cases h : p d = 0
    · exact hq' d (by simpa [h] using hd)
    · exact hp' d h
  smul_mem' := by
    rintro r p ⟨hp, hp'⟩
    refine ⟨fun d => N.smul_mem r (hp d), ?_⟩
    intro d hd
    exact hp' d (fun h => hd (by simp [h]))

/-- Evaluation before quotienting, for finite module-valued polynomials. -/
def relationEvaluation : ((Fin x.length →₀ ℕ) →₀ M) →ₗ[R] M :=
  Finsupp.lsum R (fun d => monomialValue x d • (LinearMap.id : M →ₗ[R] M))

lemma relationEvaluation_apply (p : (Fin x.length →₀ ℕ) →₀ M) :
    relationEvaluation M x p = ∑ d ∈ p.support, monomialValue x d • p d := rfl

/-- Every element of `J^n N` has a homogeneous polynomial representation,
with all coefficients in `N`. -/
lemma homogeneous_generation (N : Submodule R M) (n : ℕ) {m : M}
    (hm : m ∈ sequenceIdeal x ^ n • N) :
    ∃ p ∈ homogeneousRelations M x N n, relationEvaluation M x p = m := by
  classical
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr m hm
    rw [← generators_span x] at hr
    obtain ⟨q, hq, hqr⟩ :=
      (Ideal.mem_span_pow_iff_exists_isHomogeneous (fun i : Fin x.length => x[i]) r).mp hr
    let p : (Fin x.length →₀ ℕ) →₀ M := q.coeff.mapRange (fun a => a • m) (zero_smul R m)
    refine ⟨p, ⟨?_, ?_⟩, ?_⟩
    · intro d
      exact N.smul_mem _ hm
    · intro d hd
      have hc : q.coeff d ≠ 0 := fun h => hd (by simp [p, h])
      simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using hq hc
    · rw [← hqr, MvPolynomial.eval_eq, Finset.sum_smul]
      change (∑ d ∈ p.support, monomialValue x d • p d) = _
      have hsub : p.support ⊆ q.support := Finsupp.support_mapRange
      rw [Finset.sum_subset hsub ?_]
      · apply Finset.sum_congr rfl
        intro d hd
        simp only [p, Finsupp.mapRange_apply, monomialValue, smul_smul, Finsupp.prod]
        rw [mul_comm]
      · intro d hd hdp
        simp only [Finsupp.notMem_support_iff.mp hdp, smul_zero]
  · intro m m' hp hp'
    obtain ⟨p, hp, rfl⟩ := hp
    obtain ⟨p', hp', rfl⟩ := hp'
    exact ⟨p + p', (homogeneousRelations M x N n).add_mem hp hp', map_add _ _ _⟩

/-- Evaluation preserves membership in the appropriate power times the
coefficient submodule. -/
lemma relationEvaluation_mem (N : Submodule R M) (n : ℕ)
    {p : (Fin x.length →₀ ℕ) →₀ M} (hp : p ∈ homogeneousRelations M x N n) :
    relationEvaluation M x p ∈ sequenceIdeal x ^ n • N := by
  classical
  apply Submodule.sum_mem
  intro d hd
  have he := hp.2 d (Finsupp.mem_support_iff.mp hd)
  exact Submodule.smul_mem_smul (he ▸ monomial_mem x d) (hp.1 d)

/-- The prefix comparison detects coefficients in the finite polynomial model. -/
lemma relation_coefficients (hc : HomogeneousCoefficients M x) (n : ℕ)
    {p : (Fin x.length →₀ ℕ) →₀ M}
    (hp : p ∈ homogeneousRelations M x ⊤ n)
    (he : relationEvaluation M x p ∈ sequenceIdeal x ^ (n + 1) • (⊤ : Submodule R M)) :
    ∀ d, p d ∈ (sequenceIdeal x • (⊤ : Submodule R M)) := by
  classical
  intro d
  by_cases hd : d ∈ p.support
  · exact hc n p.support (fun e he => hp.2 e (Finsupp.mem_support_iff.mp he)) p he d hd
  · simp [Finsupp.notMem_support_iff.mp hd]

/-- Finite-filtration cancellation: regularity modulo `JM` and the prefix
comparison imply regularity modulo every `J^n M`. -/
lemma prefix_power_cancellation
    (hi : Function.Injective (GradedComparison.Core.comparison M x))
    (a : R) (ha : IsSMulRegular (Coefficients (sequenceIdeal x) M) a)
    (n : ℕ) {m : M}
    (hm : a • m ∈ sequenceIdeal x ^ n • (⊤ : Submodule R M)) :
    m ∈ sequenceIdeal x ^ n • (⊤ : Submodule R M) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      have hle : sequenceIdeal x ^ (n + 1) ≤ sequenceIdeal x ^ n := Ideal.pow_le_pow_right (by omega)
      have hmn := ih (Submodule.smul_mono_left hle hm)
      obtain ⟨p, hp, he⟩ := homogeneous_generation M x ⊤ n hmn
      have hap : a • p ∈ homogeneousRelations M x ⊤ n :=
        (homogeneousRelations M x ⊤ n).smul_mem a hp
      have hcoeff := relation_coefficients M x (coefficients_of_comparison_injective M x hi)
        n hap (by simpa only [map_smul, he] using hm)
      have hp' : p ∈ homogeneousRelations M x (sequenceIdeal x • ⊤) n := by
        refine ⟨?_, hp.2⟩
        intro d
        exact mem_of_isSMulRegular_quotient_of_smul_mem ha (hcoeff d)
      rw [← he]
      have hg := relationEvaluation_mem M x (sequenceIdeal x • ⊤) n hp'
      simpa only [pow_succ, mul_smul] using hg

/-- Inclusion of the prefix positions into an appended list. -/
def prefixIndex (a : R) : Fin x.length ↪ Fin (x ++ [a]).length where
  toFun i := ⟨i.val, by simpa using Nat.lt_succ_of_lt i.isLt⟩
  inj' i j h := Fin.ext (congrArg (fun k : Fin (x ++ [a]).length => k.val) h)

def lastIndex (a : R) : Fin (x ++ [a]).length := ⟨x.length, by simp⟩

lemma index_cases (a : R) (i : Fin (x ++ [a]).length) :
    (∃ j, prefixIndex x a j = i) ∨ i = lastIndex x a := by
  by_cases h : i.val < x.length
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · right
    apply Fin.ext
    have := i.isLt
    simp only [List.length_append, List.length_singleton] at this
    dsimp [lastIndex]
    omega

def prefixExponent (a : R) (d : Fin x.length →₀ ℕ) : Fin (x ++ [a]).length →₀ ℕ :=
  d.embDomain (prefixIndex x a)

lemma prefixExponent_injective (a : R) : Function.Injective (prefixExponent x a) :=
  Finsupp.embDomain_injective _

@[simp] lemma prefixExponent_degree (a : R) (d : Fin x.length →₀ ℕ) :
    (prefixExponent x a d).degree = d.degree := by
  rw [prefixExponent, Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]

@[simp] lemma prefixExponent_last (a : R) (d : Fin x.length →₀ ℕ) :
    prefixExponent x a d (lastIndex x a) = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  exact (Nat.ne_of_lt i.isLt) he

@[simp] lemma prefixExponent_value (a : R) (d : Fin x.length →₀ ℕ) :
    monomialValue (x ++ [a]) (prefixExponent x a d) = monomialValue x d := by
  classical
  simp only [monomialValue, prefixExponent, Finsupp.prod_embDomain]
  apply Finsupp.prod_congr
  intro i hi
  simp [prefixIndex, List.getElem_append_left]

lemma exponent_of_last_zero (a : R) (d : Fin (x ++ [a]).length →₀ ℕ)
    (hd : d (lastIndex x a) = 0) : ∃ e, prefixExponent x a e = d := by
  let e := d.comapDomain (prefixIndex x a) (prefixIndex x a).injective.injOn
  refine ⟨e, ?_⟩
  ext i
  rcases index_cases x a i with ⟨j, rfl⟩ | rfl
  · simp [prefixExponent, e]
  · simpa using hd.symm

lemma exponent_of_last_pos (a : R) (d : Fin (x ++ [a]).length →₀ ℕ)
    (hd : d (lastIndex x a) ≠ 0) :
    ∃ e, e + Finsupp.single (lastIndex x a) 1 = d := by
  refine ⟨d - Finsupp.single (lastIndex x a) 1, ?_⟩
  apply tsub_add_cancel_of_le
  rw [Finsupp.le_def]
  intro i
  by_cases h : lastIndex x a = i
  · subst i; simpa using Nat.one_le_iff_ne_zero.mpr hd
  · simp [Finsupp.single_apply, h]

lemma monomialValue_add (y : List R) (d e : Fin y.length →₀ ℕ) :
    monomialValue y (d + e) = monomialValue y d * monomialValue y e :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

@[simp] lemma monomialValue_last (a : R) :
    monomialValue (x ++ [a]) (Finsupp.single (lastIndex x a) 1) = a := by
  simp [monomialValue, lastIndex]

/-- The part independent of the final variable. -/
def relationPrefix (a : R) :
    ((Fin (x ++ [a]).length →₀ ℕ) →₀ M) →ₗ[R] ((Fin x.length →₀ ℕ) →₀ M) :=
  Finsupp.lcomapDomain (prefixExponent x a) (prefixExponent_injective x a)

/-- Division of all terms containing the final variable by that variable. -/
def relationTail (a : R) :
    ((Fin (x ++ [a]).length →₀ ℕ) →₀ M) →ₗ[R]
      ((Fin (x ++ [a]).length →₀ ℕ) →₀ M) :=
  Finsupp.lcomapDomain (fun d => d + Finsupp.single (lastIndex x a) 1)
    (fun _ _ h => add_right_cancel h)

lemma relation_evaluation_split (a : R) (p : (Fin (x ++ [a]).length →₀ ℕ) →₀ M) :
    relationEvaluation M (x ++ [a]) p =
      relationEvaluation M x (relationPrefix M x a p) +
      a • relationEvaluation M (x ++ [a]) (relationTail M x a p) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, smul_add, hp, hq]; abel
  | single d m =>
      by_cases hd : d (lastIndex x a) = 0
      · obtain ⟨e, rfl⟩ := exponent_of_last_zero x a d hd
        have hn : prefixExponent x a e ∉
            Set.range (fun d => d + Finsupp.single (lastIndex x a) 1) := by
          rintro ⟨f, hf⟩
          have h := congrArg (fun t => t (lastIndex x a)) hf
          simp at h
        simp [relationPrefix, relationTail, Finsupp.lcomapDomain,
          Finsupp.comapDomain_single, Finsupp.comapDomain_single_of_notMem_range hn,
          relationEvaluation, Finsupp.lsum_single]
      · obtain ⟨e, rfl⟩ := exponent_of_last_pos x a d hd
        have hn : e + Finsupp.single (lastIndex x a) 1 ∉ Set.range (prefixExponent x a) := by
          rintro ⟨f, hf⟩
          have h := congrArg (fun t => t (lastIndex x a)) hf
          simp at h
        simp [relationPrefix, relationTail, Finsupp.lcomapDomain,
          Finsupp.comapDomain_single, Finsupp.comapDomain_single_of_notMem_range hn,
          relationEvaluation, Finsupp.lsum_single, monomialValue_add, smul_smul,
          mul_comm]

lemma relationPrefix_homogeneous (a : R) (n : ℕ)
    {p : (Fin (x ++ [a]).length →₀ ℕ) →₀ M}
    (hp : p ∈ homogeneousRelations M (x ++ [a]) ⊤ n) :
    relationPrefix M x a p ∈ homogeneousRelations M x ⊤ n := by
  refine ⟨fun _ => trivial, ?_⟩
  intro d hd
  have h := hp.2 (prefixExponent x a d) hd
  simpa using h

lemma relationTail_homogeneous (a : R) (n : ℕ)
    {p : (Fin (x ++ [a]).length →₀ ℕ) →₀ M}
    (hp : p ∈ homogeneousRelations M (x ++ [a]) ⊤ (n + 1)) :
    relationTail M x a p ∈ homogeneousRelations M (x ++ [a]) ⊤ n := by
  refine ⟨fun _ => trivial, ?_⟩
  intro d hd
  have h := hp.2 (d + Finsupp.single (lastIndex x a) 1) hd
  simpa only [map_add, Finsupp.degree_single, Nat.add_right_cancel_iff] using h

lemma prefixIdeal_le_append (a : R) : sequenceIdeal x ≤ sequenceIdeal (x ++ [a]) := by
  apply Ideal.span_mono
  intro r hr
  exact List.mem_append_left _ hr

lemma last_mem_append (a : R) : a ∈ sequenceIdeal (x ++ [a]) :=
  Ideal.subset_span (by simp)

/-- Subtract a homogeneous representation with coefficients in `IM` to
reduce a relation modulo `I^(n+1) M` to an exact relation. -/
lemma relation_coefficients_of_exact (n : ℕ)
    (hexact : ∀ p ∈ homogeneousRelations M x ⊤ n,
      relationEvaluation M x p = 0 →
      ∀ d, p d ∈ sequenceIdeal x • (⊤ : Submodule R M))
    {p : (Fin x.length →₀ ℕ) →₀ M}
    (hp : p ∈ homogeneousRelations M x ⊤ n)
    (he : relationEvaluation M x p ∈ sequenceIdeal x ^ (n + 1) • (⊤ : Submodule R M)) :
    ∀ d, p d ∈ sequenceIdeal x • (⊤ : Submodule R M) := by
  have he' : relationEvaluation M x p ∈
      sequenceIdeal x ^ n • (sequenceIdeal x • (⊤ : Submodule R M)) := by
    simpa only [pow_succ, mul_smul] using he
  obtain ⟨q, hq, heq⟩ := homogeneous_generation M x (sequenceIdeal x • ⊤) n he'
  have hqt : q ∈ homogeneousRelations M x ⊤ n := ⟨fun _ => trivial, hq.2⟩
  have h := hexact (p - q) ((homogeneousRelations M x ⊤ n).sub_mem hp hqt)
    (by rw [map_sub, heq, sub_self])
  intro d
  exact (Submodule.sub_mem_iff_left _ (hq.1 d)).mp (h d)

/-- The degree induction in the append argument, in finite coefficient form. -/
lemma relation_append_coefficients (a : R)
    (hi : Function.Injective (GradedComparison.Core.comparison M x))
    (ha : IsSMulRegular (Coefficients (sequenceIdeal x) M) a) (n : ℕ)
    {p : (Fin (x ++ [a]).length →₀ ℕ) →₀ M}
    (hp : p ∈ homogeneousRelations M (x ++ [a]) ⊤ n)
    (he : relationEvaluation M (x ++ [a]) p ∈
      sequenceIdeal (x ++ [a]) ^ (n + 1) • (⊤ : Submodule R M)) :
    ∀ d, p d ∈ sequenceIdeal (x ++ [a]) • (⊤ : Submodule R M) := by
  classical
  induction n generalizing p with
  | zero =>
      have hp0 : p = Finsupp.single 0 (p 0) := by
        ext d
        by_cases hd : d = 0
        · subst d; simp
        · have hz : p d = 0 := by
            by_contra h
            exact hd ((Finsupp.degree_eq_zero_iff d).mp (hp.2 d h))
          simp [Finsupp.single_apply, hd, hz, Ne.symm hd]
      rw [hp0] at he ⊢
      have hm : p 0 ∈ sequenceIdeal (x ++ [a]) • (⊤ : Submodule R M) := by
        simpa [relationEvaluation, monomialValue] using he
      intro d
      by_cases hd : d = 0
      · subst d; simpa using hm
      · simp [Finsupp.single_apply, hd, Ne.symm hd]
  | succ n ih =>
      apply relation_coefficients_of_exact M (x ++ [a]) (n + 1) ?_ hp he
      intro f hf hfe
      let g := relationPrefix M x a f
      let h := relationTail M x a f
      have hg : g ∈ homogeneousRelations M x ⊤ (n + 1) :=
        relationPrefix_homogeneous M x a (n + 1) hf
      have hh : h ∈ homogeneousRelations M (x ++ [a]) ⊤ n :=
        relationTail_homogeneous M x a n hf
      have hsplit : relationEvaluation M x g +
          a • relationEvaluation M (x ++ [a]) h = 0 := by
        rw [← relation_evaluation_split M x a f]
        exact hfe
      have ham : a • relationEvaluation M (x ++ [a]) h ∈
          sequenceIdeal x ^ (n + 1) • (⊤ : Submodule R M) := by
        rw [eq_neg_of_add_eq_zero_right hsplit]
        exact Submodule.neg_mem _ (relationEvaluation_mem M x ⊤ (n + 1) hg)
      have hm := prefix_power_cancellation M x hi a ha (n + 1) ham
      have hmh : relationEvaluation M (x ++ [a]) h ∈
          sequenceIdeal (x ++ [a]) ^ (n + 1) • (⊤ : Submodule R M) :=
        Submodule.smul_mono_left (Ideal.pow_right_mono (prefixIdeal_le_append x a) (n + 1)) hm
      have hhc : ∀ d, h d ∈ sequenceIdeal (x ++ [a]) • (⊤ : Submodule R M) := ih hh hmh
      obtain ⟨h', hh', heh'⟩ := homogeneous_generation M x ⊤ (n + 1) hm
      have hnew : g + a • h' ∈ homogeneousRelations M x ⊤ (n + 1) :=
        (homogeneousRelations M x ⊤ (n + 1)).add_mem hg
          ((homogeneousRelations M x ⊤ (n + 1)).smul_mem a hh')
      have henew : relationEvaluation M x (g + a • h') = 0 := by
        rw [map_add, map_smul, heh']
        exact hsplit
      have hgc : ∀ d, g d ∈ sequenceIdeal (x ++ [a]) • (⊤ : Submodule R M) := by
        intro d
        have hc := relation_coefficients M x (coefficients_of_comparison_injective M x hi)
          (n + 1) hnew (henew ▸ (Submodule.zero_mem _)) d
        have hsub : (g + a • h') d ∈ sequenceIdeal (x ++ [a]) • (⊤ : Submodule R M) :=
          Submodule.smul_mono_left (prefixIdeal_le_append x a) hc
        have hsmul : a • h' d ∈ sequenceIdeal (x ++ [a]) • (⊤ : Submodule R M) :=
          Submodule.smul_mem_smul (last_mem_append x a) (Submodule.mem_top)
        exact (Submodule.add_mem_iff_left _ hsmul).mp hsub
      intro d
      by_cases hd : d (lastIndex x a) = 0
      · obtain ⟨e, rfl⟩ := exponent_of_last_zero x a d hd
        exact hgc e
      · obtain ⟨e, rfl⟩ := exponent_of_last_pos x a d hd
        exact hhc e

/-- Remaining inductive step. Its hypotheses are the already established
comparison for the prefix and injectivity of the appended scalar on M/JM. -/
lemma coefficients_append (a : R)
    (hi : Function.Injective (GradedComparison.Core.comparison M x))
    (ha : IsSMulRegular (Coefficients (sequenceIdeal x) M) a) :
    HomogeneousCoefficients M (x ++ [a]) := by
  classical
  intro n s hd m he d hd'
  let p : (Fin (x ++ [a]).length →₀ ℕ) →₀ M := ∑ e ∈ s, Finsupp.single e (m e)
  have hp : p ∈ homogeneousRelations M (x ++ [a]) ⊤ n := by
    apply (homogeneousRelations M (x ++ [a]) ⊤ n).sum_mem
    intro e he
    refine ⟨fun _ => trivial, ?_⟩
    intro f hf
    by_cases h : e = f
    · subst f; exact hd e he
    · exact False.elim (hf (by simp [Finsupp.single_apply, h]))
  have hep : relationEvaluation M (x ++ [a]) p =
      ∑ e ∈ s, monomialValue (x ++ [a]) e • m e := by
    simp [p, relationEvaluation, Finsupp.lsum_single]
  have hc := relation_append_coefficients M x a hi ha n hp (hep ▸ he) d
  simpa [p, Finsupp.finsetSum_apply, Finsupp.single_apply, hd'] using hc

/-- The length induction reduces RK-11 to the precise append step above. -/
theorem coefficients_of_weaklyRegular (hx : WeaklyRegular M x) :
    HomogeneousCoefficients M x := by
  induction x using List.reverseRecOn with
  | nil =>
      exact coefficients_of_comparison_injective M [] (comparison_nil_bijective M).1
  | append_singleton x a ih =>
      have h := (RingTheory.Sequence.isWeaklyRegular_append_iff M x [a]).mp hx
      have ha := (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ a).mp h.2
      exact coefficients_append M x a (comparison_injective_of_coefficients M x (ih h.1)) ha

theorem comparison_bijective (hx : WeaklyRegular M x) :
    Function.Bijective (GradedComparison.Core.comparison M x) :=
  ⟨comparison_injective_of_coefficients M x (coefficients_of_weaklyRegular M x hx),
    comparison_surjective M x⟩

/-- RK-11 as an isomorphism with the given polynomial action and grading. -/
theorem gradedModuleEquiv (hx : WeaklyRegular M x) :
    ∃ e : GradedComparison.Core.PolynomialModule M x ≃ₗ[PolynomialRing x]
        AssociatedModule (sequenceIdeal x) M,
      (∀ p, e p = GradedComparison.Core.comparison M x p) ∧
      (∀ n p, PolynomialHomogeneous M x n p ↔ e p ∈ modulePiece (sequenceIdeal x) M n) := by
  refine ⟨LinearEquiv.ofBijective (GradedComparison.Core.comparison M x)
    (comparison_bijective M x hx), fun _ => rfl, ?_⟩
  exact homogeneous_iff_of_injective M x (comparison_bijective M x hx).1

end
end AdvCommAlg.RegularSequence.AssociatedGraded

namespace AdvCommAlg.RegularSequence.AssociatedGraded
noncomputable section
open P103.Rees GradedComparison GradedComparison.Core Core
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (x : List R)

/-- The module specialization and the algebra evaluation are the same map
under the already established source and target identifications. -/
lemma ringComparison_injective_of_module
    (hi : Function.Injective (GradedComparison.Core.comparison R x)) :
    Function.Injective (GradedComparison.Core.ringComparison x) := by
  intro p q hpq
  apply (ringSourceEquiv x).symm.injective
  apply hi
  apply (associatedRingEquiv (sequenceIdeal x)).injective
  simpa only [comparison_ring_bridge, LinearEquiv.apply_symm_apply] using hpq

theorem ringComparison_bijective (hx : WeaklyRegular R x) :
    Function.Bijective (GradedComparison.Core.ringComparison x) :=
  ⟨ringComparison_injective_of_module x (comparison_bijective R x hx).1,
    ringComparison_surjective x⟩

lemma ringComparison_monomial_projection (n : ℕ) (d : Fin x.length →₀ ℕ)
    (c : R ⧸ sequenceIdeal x) :
    ringProjection (sequenceIdeal x) n
      (GradedComparison.ringComparison x (MvPolynomial.monomial d c)) =
      if d.degree = n then GradedComparison.ringComparison x (MvPolynomial.monomial d c) else 0 := by
  classical
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [GradedComparison.ringComparison_monomial, ringProjection_class]
  simp only [eq_comm]

lemma ringComparison_homogeneousComponent (n : ℕ) (p : PolynomialRing x) :
    GradedComparison.ringComparison x (MvPolynomial.homogeneousComponent n p) =
      ringProjection (sequenceIdeal x) n (GradedComparison.ringComparison x p) := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply, map_sum]
  conv_rhs => rw [p.as_sum, map_sum, map_sum]
  simp only [ringComparison_monomial_projection]
  rw [Finset.sum_filter]

lemma ring_homogeneous_iff_of_injective
    (hi : Function.Injective (GradedComparison.Core.ringComparison x))
    (n : ℕ) (p : PolynomialRing x) :
    p.IsHomogeneous n ↔ GradedComparison.Core.ringComparison x p ∈ ringPiece (sequenceIdeal x) n := by
  constructor
  · exact ringComparison_homogeneous x n p
  · intro hp
    have he : GradedComparison.ringComparison x (MvPolynomial.homogeneousComponent n p) =
        GradedComparison.ringComparison x p := by
      rw [ringComparison_homogeneousComponent]
      obtain ⟨a, ha⟩ := hp
      change ringProjection (sequenceIdeal x) n (GradedComparison.Core.ringComparison x p) = _
      rw [← ha, ringProjection_class]
      simp only [ite_true]
      exact ha
    have heq := hi he
    rw [← heq]
    exact MvPolynomial.homogeneousComponent_isHomogeneous n p

/-- The ring specialization is an algebra isomorphism with graded inverse. -/
theorem gradedAlgebraEquiv (hx : WeaklyRegular R x) :
    ∃ e : PolynomialRing x ≃ₐ[R ⧸ sequenceIdeal x] AssociatedRing (sequenceIdeal x),
      (∀ p, e p = GradedComparison.Core.ringComparison x p) ∧
      (∀ n p, p.IsHomogeneous n ↔ e p ∈ ringPiece (sequenceIdeal x) n) := by
  refine ⟨AlgEquiv.ofBijective (GradedComparison.Core.ringComparison x)
    (ringComparison_bijective x hx), fun _ => rfl, ?_⟩
  exact ring_homogeneous_iff_of_injective x (ringComparison_bijective x hx).1

/-- The named generator classes span the actual conormal module, without
regularity or any finiteness assumptions on the ambient ring. -/
lemma conormal_span :
    Submodule.span (R ⧸ sequenceIdeal x) (Set.range (conormalClass x)) = ⊤ := by
  let I := sequenceIdeal x
  let v : Fin x.length → I := fun i =>
    ⟨x[i], Ideal.subset_span (List.getElem_mem i.isLt)⟩
  have hv : Submodule.span R (Set.range v) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I
      (fun i => Ideal.subset_span (List.getElem_mem i.isLt))).mpr (generators_span x)
  apply (Submodule.restrictScalars_injective R (R ⧸ I) I.Cotangent)
  rw [Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective,
    Submodule.restrictScalars_top]
  calc
    Submodule.span R (Set.range (conormalClass x)) =
        (Submodule.span R (Set.range v)).map I.toCotangent := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = ⊤ := by rw [hv, Submodule.map_top, Ideal.toCotangent_range]

end
end AdvCommAlg.RegularSequence.AssociatedGraded

namespace AdvCommAlg.RegularSequence.AssociatedGraded
noncomputable section
open P103.Rees GradedComparison GradedComparison.Core Core
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (x : List R)

lemma ringComparison_C_mul_X (i : Fin x.length) (r : R) :
    GradedComparison.Core.ringComparison x
      (MvPolynomial.C (Ideal.Quotient.mk (sequenceIdeal x) r) * MvPolynomial.X i) =
    ringClass (sequenceIdeal x) 1
      ⟨r * x[i], by
        rw [pow_one]
        exact (sequenceIdeal x).mul_mem_left r (Ideal.subset_span (List.getElem_mem i.isLt))⟩ := by
  change (MvPolynomial.aeval (initialForm x)) _ = _
  rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, baseClass, initialForm, ringClass_mul]
  rfl

/-- Only injectivity of the canonical ring comparison is needed for
independence of the specified conormal classes. -/
lemma conormal_linearIndependent_of_injective
    (hi : Function.Injective (GradedComparison.Core.ringComparison x)) :
    LinearIndependent (R ⧸ sequenceIdeal x) (conormalClass x) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i his
  choose r hr using fun j => (Ideal.Quotient.mk_surjective (I := sequenceIdeal x) (g j))
  let I := sequenceIdeal x
  let v : Fin x.length → I := fun j =>
    ⟨x[j], Ideal.subset_span (List.getElem_mem j.isLt)⟩
  let a : I := ∑ j ∈ s, r j • v j
  have ha : I.toCotangent a = 0 := by
    change I.toCotangent (∑ j ∈ s, r j • v j) = 0
    rw [map_sum]
    simp only [map_smul]
    simp only [← hr, ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul] at hg
    exact hg
  have ha2 : (a : R) ∈ I ^ 2 := (I.toCotangent_eq_zero a).mp ha
  let p : PolynomialRing x := ∑ j ∈ s, MvPolynomial.C (g j) * MvPolynomial.X j
  have hp : GradedComparison.Core.ringComparison x p = 0 := by
    have he : GradedComparison.Core.ringComparison x p =
        ringClass I 1 ⟨a.1, by simpa using a.2⟩ := by
      change GradedComparison.Core.ringComparison x (∑ j ∈ s,
        MvPolynomial.C (g j) * MvPolynomial.X j) = _
      rw [map_sum]
      have hab : (⟨a.1, by simpa using a.2⟩ : (I ^ 1 : Ideal R)) =
          ∑ j ∈ s, (⟨r j * x[j], by
            simpa only [pow_one, v] using I.mul_mem_left (r j) (v j).2⟩ : (I ^ 1 : Ideal R)) := by
        apply Subtype.ext
        simp only [a, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul, v]
      rw [hab, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hr j]
      exact ringComparison_C_mul_X x j (r j)
    rw [he]
    exact (ringClass_eq_zero_iff I 1 _).mpr ha2
  have hp0 : p = 0 := hi (hp.trans (map_zero _).symm)
  have hc := congrArg (fun q : PolynomialRing x => q.coeff (Finsupp.single i 1)) hp0
  have hsingle : ∀ j : Fin x.length, Finsupp.single i 1 = Finsupp.single j 1 ↔ i = j := by
    intro j
    exact ⟨fun h => Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) h,
      fun h => h ▸ rfl⟩
  simpa [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X, eq_comm, hsingle, his] using hc

lemma conormalBasis_of_injective
    (hi : Function.Injective (GradedComparison.Core.ringComparison x)) :
    ∃ b : Module.Basis (Fin x.length) (R ⧸ sequenceIdeal x) (sequenceIdeal x).Cotangent,
      ∀ i, b i = conormalClass x i := by
  exact ⟨Module.Basis.mk (conormal_linearIndependent_of_injective x hi)
    (conormal_span x).ge, fun i => Module.Basis.mk_apply _ _ i⟩

/-- The degree-one corollary of RK-11, in Mathlib's actual I/I² module. -/
theorem conormalBasis (hx : RingRegular x) :
    ∃ b : Module.Basis (Fin x.length) (R ⧸ sequenceIdeal x) (sequenceIdeal x).Cotangent,
      ∀ i, b i = conormalClass x i :=
  conormalBasis_of_injective x (ringComparison_bijective x hx.toIsWeaklyRegular).1

end
end AdvCommAlg.RegularSequence.AssociatedGraded
