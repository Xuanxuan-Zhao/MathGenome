import MathGenome.Internal.MultivariableAnalysis.D04.C03.Symmetry
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.FactorialBridge
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin

noncomputable section
open scoped BigOperators
namespace D04
abbrev multiIndices := Specs.D04.C03.FactorialBridge.Model.multiIndices
abbrev tensorMultiIndex := @Specs.D04.C03.FactorialBridge.Model.tensorMultiIndex
abbrev multiIndexTaylorPolynomial := @Specs.D04.C03.FactorialBridge.Model.multiIndexTaylorPolynomial

/-- The finite summation range contains exactly the degree-j multi-indices. -/
theorem mem_multiIndices_iff {n j : ℕ} (α : DerivativeMultiIndex n) :
    α ∈ multiIndices n j ↔ multiIndexDegree α = j := by
  simp [multiIndices, Specs.D04.C03.FactorialBridge.Model.multiIndices,
    multiIndexDegree, Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree]

namespace FactorialBridge
variable {n j : ℕ}
/-- Multiplicities of an ordered coordinate tuple. -/
def tupleCounts (w : Fin j → Fin n) : Fin n → ℕ :=
  fun i => (Finset.univ.filter (fun r => w r = i)).card

lemma counts_finsupp (w : Fin j → Fin n) :
    (∑ r, Finsupp.single (w r) 1 : Fin n →₀ ℕ) = Finsupp.equivFunOnFinite.symm (tupleCounts w) := by
  ext i
  change (∑ r, Finsupp.single (w r) 1 : Fin n →₀ ℕ) i = tupleCounts w i
  simp [tupleCounts, Finsupp.single_apply, eq_comm]

lemma tupleCounts_degree (w : Fin j → Fin n) : multiIndexDegree (tupleCounts w) = j := by
  classical
  unfold multiIndexDegree Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree tupleCounts
  simpa using (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := w) (fun _ _ => Finset.mem_univ _)).symm

lemma tupleCounts_list (w : Fin j → Fin n) (i : Fin n) :
    tupleCounts w i = (List.ofFn w).count i := by
  classical
  simpa [tupleCounts] using
    (Fin.card_filter_univ_eq_vector_get_eq_count i (List.Vector.ofFn w))

lemma tuple_product (w : Fin j → Fin n) (h : E n) :
    (∏ r, h (w r)) = multiIndexMonomial (tupleCounts w) h := by
  classical
  symm
  unfold multiIndexMonomial Specs.D04.C03.HigherInterfaces.Model.multiIndexMonomial tupleCounts
  simpa using (Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.univ)
    (g := w) (fun _ _ => Finset.mem_univ _) (fun i => h i))

lemma tuple_monomial (w : Fin j → Fin n) :
    (∏ r, MvPolynomial.X (w r) : MvPolynomial (Fin n) ℕ) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (tupleCounts w)) 1 := by
  rw [← counts_finsupp, MvPolynomial.monomial_sum_one]
  rfl

/-- Coefficient extraction counts words with exactly the prescribed multiplicities. -/
lemma tuple_fiber_card (α : DerivativeMultiIndex n) (hα : multiIndexDegree α = j) :
    (Finset.univ.filter (fun w : Fin j → Fin n => tupleCounts w = α)).card =
      Nat.multinomial Finset.univ α := by
  classical
  let d : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm α
  have hd : d.sum (fun _ m => m) = j := by
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
    exact hα
  have hc := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℕ) d j
  rw [ite_eq_left hd, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at hc
  rw [Fintype.sum_pow, MvPolynomial.coeff_sum] at hc
  simp_rw [tuple_monomial, MvPolynomial.coeff_monomial] at hc
  simpa [d, Equiv.apply_eq_iff_eq, eq_comm] using hc

/-- Equal multiplicities give an actual permutation of the argument positions. -/
lemma tupleCounts_equiv (u v : Fin j → Fin n) (hc : tupleCounts u = tupleCounts v) :
    ∃ σ : Equiv.Perm (Fin j), v ∘ σ = u := by
  classical
  have he (i : Fin n) : Fintype.card {r // u r = i} = Fintype.card {r // v r = i} := by
    simpa [Fintype.card_subtype, tupleCounts] using congrFun hc i
  let e (i : Fin n) : {r // u r = i} ≃ {r // v r = i} := Fintype.equivOfCardEq (he i)
  exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩

lemma tensor_coefficient {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : Differential (E n) Y j)
    (hs : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → E n), T (v ∘ σ) = T v)
    (w : Fin j → Fin n) :
    differentialCoefficients j T w = tensorMultiIndex T (tupleCounts w) := by
  classical
  have hlen : (multiIndexWord (tupleCounts w)).length = j :=
    (multiIndexWord_length _).trans (tupleCounts_degree w)
  let v : Fin j → Fin n := fun r => (multiIndexWord (tupleCounts w)).get (Fin.cast hlen.symm r)
  have hv : List.ofFn v = multiIndexWord (tupleCounts w) := by
    exact (List.ofFn_congr hlen (multiIndexWord (tupleCounts w)).get).symm.trans
      (List.ofFn_get _)
  have hc : tupleCounts v = tupleCounts w := by
    funext i
    rw [tupleCounts_list, hv, multiIndexWord_count]
  obtain ⟨σ, hσ⟩ := tupleCounts_equiv w v hc.symm
  have ht := hs σ (fun r => standardBasis n (v r))
  have ht' : T (fun r => standardBasis n (w r)) = T (fun r => standardBasis n (v r)) := by
    convert ht using 1
    exact congrArg T (congrArg (fun z : Fin j → Fin n => fun r => standardBasis n (z r)) hσ.symm)
  simpa [differentialCoefficients_apply, tensorMultiIndex,
    Specs.D04.C03.FactorialBridge.Model.tensorMultiIndex, hlen, v,
    standardBasis, Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
    multiIndexWord] using ht'

lemma multinomial_factorial (α : DerivativeMultiIndex n) (hα : multiIndexDegree α = j) :
    (multiIndexFactorial α) * Nat.multinomial Finset.univ α = j.factorial := by
  simpa only [multiIndexFactorial, Specs.D04.C03.HigherInterfaces.Model.multiIndexFactorial,
    ← hα, multiIndexDegree, Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree] using Nat.multinomial_spec Finset.univ α

end FactorialBridge

/-- The number of ordered j-tuples with multiplicity α is j!/α!,
including the empty tuple and the empty coordinate set. -/
theorem coordinate_tuple_multiplicity {n j : ℕ} (α : DerivativeMultiIndex n)
    (hα : multiIndexDegree α = j) :
    (Finset.univ.filter (fun w : Fin j → Fin n =>
      ∀ i, (List.ofFn w).count i = α i)).card = j.factorial / multiIndexFactorial α := by
  classical
  have hc : (Finset.univ.filter (fun w : Fin j → Fin n =>
      ∀ i, (List.ofFn w).count i = α i)) =
      Finset.univ.filter (fun w => FactorialBridge.tupleCounts w = α) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff,
      FactorialBridge.tupleCounts_list]
  rw [hc, FactorialBridge.tuple_fiber_card α hα]
  simp only [Nat.multinomial, ← hα, multiIndexDegree, multiIndexFactorial,
    Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree,
    Specs.D04.C03.HigherInterfaces.Model.multiIndexFactorial]

/-- The factorial bridge for an arbitrary symmetric tensor. No regularity or
positive-dimension assumption is needed for this algebraic assertion. -/
theorem symmetric_factorial_bridge {n j : ℕ} {Y : Type} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (T : Differential (E n) Y j)
    (hs : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → E n), T (v ∘ σ) = T v)
    (h : E n) :
    ((j.factorial : ℝ)⁻¹) • differentialDiagonal T h =
      ∑ α ∈ multiIndices n j,
        (multiIndexMonomial α h / (multiIndexFactorial α : ℝ)) • tensorMultiIndex T α := by
  classical
  let term (w : Fin j → Fin n) : Y := (∏ r, h (w r)) • differentialCoefficients j T w
  have hg : (∑ α ∈ multiIndices n j,
      ∑ w ∈ Finset.univ.filter (fun w => FactorialBridge.tupleCounts w = α), term w) =
      ∑ w, term w := by
    apply Finset.sum_fiberwise_of_maps_to
    intro w _
    simp only [multiIndices, Specs.D04.C03.FactorialBridge.Model.multiIndices,
      Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true]
    exact FactorialBridge.tupleCounts_degree w
  have he : differentialDiagonal T h = ∑ w, term w := differential_expansion T (fun _ => h)
  rw [he, ← hg, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hd : multiIndexDegree α = j := by
    simpa [multiIndices, Specs.D04.C03.FactorialBridge.Model.multiIndices,
      multiIndexDegree, Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree] using hα
  have ht : (∑ w ∈ Finset.univ.filter (fun w => FactorialBridge.tupleCounts w = α), term w) =
      ((Nat.multinomial Finset.univ α : ℝ) * multiIndexMonomial α h) • tensorMultiIndex T α := by
    calc
      _ = ∑ _w ∈ Finset.univ.filter (fun w : Fin j → Fin n => FactorialBridge.tupleCounts w = α),
          (multiIndexMonomial α h) • tensorMultiIndex T α := by
        apply Finset.sum_congr rfl
        intro w hw
        have hw' := (Finset.mem_filter.mp hw).2
        simp only [term, FactorialBridge.tuple_product,
          FactorialBridge.tensor_coefficient T hs, hw']
      _ = _ := by
        rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          FactorialBridge.tuple_fiber_card α hd]
  rw [ht, smul_smul]
  congr 1
  have hfac : (multiIndexFactorial α : ℝ) * (Nat.multinomial Finset.univ α : ℝ) =
      (j.factorial : ℝ) := by exact_mod_cast FactorialBridge.multinomial_factorial α hd
  have ha : (multiIndexFactorial α : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (α i))
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  apply (mul_left_cancel₀ hj)
  rw [← mul_assoc, mul_inv_cancel₀ hj, one_mul]
  rw [← hfac]
  field_simp

/-- The canonical tensor coefficient is the shared multi-index partial, under
pointwise differentiability of the stated order. -/
theorem tensorMultiIndex_higherDifferential {n j : ℕ} {Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set (E n)) (f : E n → Y)
    (a : E n) (hf : TimesDifferentiableAt j U f a) (α : DerivativeMultiIndex n)
    (hα : multiIndexDegree α = j) :
    tensorMultiIndex (higherDifferential j f a) α = multiIndexPartial α f a := by
  classical
  have hlen : (multiIndexWord α).length = j := (multiIndexWord_length α).trans hα
  let w : Fin j → Fin n := fun r => (multiIndexWord α).get (Fin.cast hlen.symm r)
  have hw : List.ofFn w = multiIndexWord α :=
    (List.ofFn_congr hlen (multiIndexWord α).get).symm.trans (List.ofFn_get _)
  change (if h : (multiIndexWord α).length = j then
    higherDifferential j f a (fun r => standardBasis n ((multiIndexWord α).get (Fin.cast h.symm r)))
    else 0) = multiIndexPartial α f a
  rw [dite_eq_left hlen]
  change higherDifferential j f a (fun r => standardBasis n (w r)) = _
  rw [higherDifferential_basis j U f a hf, hw]
  rfl

/-- Vector-valued version of the source formula; ℝ-valued maps are included. -/
theorem factorial_bridge {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (j : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n)
    (hf : TimesDifferentiableAt j U f a) (h : E n) :
    ((j.factorial : ℝ)⁻¹) • differentialDiagonal (higherDifferential j f a) h =
      ∑ α ∈ multiIndices n j,
        (multiIndexMonomial α h / (multiIndexFactorial α : ℝ)) • multiIndexPartial α f a := by
  rw [symmetric_factorial_bridge _ (higherDifferential_symmetric j U f a hf)]
  apply Finset.sum_congr rfl
  intro α hα
  rw [tensorMultiIndex_higherDifferential U f a hf α]
  simpa [multiIndices, Specs.D04.C03.FactorialBridge.Model.multiIndices,
    multiIndexDegree, Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree] using hα

namespace FactorialBridge

lemma timesDifferentiableAt_of_le {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k j : ℕ} (U : Set X) (f : X → Y)
    (a : X) (hf : TimesDifferentiableAt k U f a) (hjk : j ≤ k) :
    TimesDifferentiableAt j U f a := by
  induction k generalizing j with
  | zero => have hj : j = 0 := Nat.eq_zero_of_le_zero hjk; subst j; exact hf
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with he | he
    · simpa only [he] using hf
    · exact ih (timesDifferentiableAt_lower k U f a hf) (Nat.le_of_lt_succ he)

end FactorialBridge

/-- Equality of the polynomial functions, at every finite order, with precisely
the original factorial conventions. -/
theorem taylorPolynomial_eq_multiIndex {n : ℕ} {Y : Type} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (k : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n)
    (hf : TimesDifferentiableAt k U f a) :
    taylorPolynomial k f a = multiIndexTaylorPolynomial k f a := by
  funext h
  change (∑ j ∈ Finset.range (k+1), ((j.factorial : ℝ)⁻¹) •
    differentialDiagonal (higherDifferential j f a) h) = _
  apply Finset.sum_congr rfl
  intro j hj
  exact factorial_bridge j U f a
    (FactorialBridge.timesDifferentiableAt_of_le U f a hf
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) h

/-- Ordinary division and multiplication give the scalar presentation printed
in the source. -/
theorem factorial_bridge_scalar {n : ℕ} (j : ℕ) (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (hf : TimesDifferentiableAt j U f a) (h : E n) :
    differentialDiagonal (higherDifferential j f a) h / (j.factorial : ℝ) =
      ∑ α ∈ multiIndices n j,
        (multiIndexPartial α f a / (multiIndexFactorial α : ℝ)) * multiIndexMonomial α h := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using factorial_bridge j U f a hf h

/-- There is one empty tuple at order zero. -/
theorem multiIndices_zero (n : ℕ) : multiIndices n 0 = {0} :=
  Finset.piAntidiag_zero _

/-- In dimension zero there are no positive-degree multi-indices. -/
theorem multiIndices_dimension_zero_succ (j : ℕ) : multiIndices 0 (j+1) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro α hα
  have hd := (mem_multiIndices_iff α).mp hα
  rw [multiIndexDegree_dimension_zero] at hd
  omega

end D04
