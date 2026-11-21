import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Recurrence.ExponentialPolynomial
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Recurrence.RepeatedRoots
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
open Polynomial
universe u
namespace FiniteCombinatorics.Recurrence
variable {K : Type u} [Field K] [hchar : CharZero K]

/-- Evaluation on the natural numbers followed by multiplication by λⁿ. -/
def exponentialEvaluation (lam : K) : K[X] →ₗ[K] (ℕ → K) where
  toFun P n := P.eval (n : K) * lam ^ n
  map_add' P Q := by ext n; simp [add_mul]
  map_smul' k P := by ext n; simp [mul_assoc]

/-- The polynomial whose exponential sequence is the j-th root sequence. -/
def rootPolynomial (lam : K) (j : ℕ) : K[X] :=
  ((lam ^ j)⁻¹ / (j.factorial : K)) • descPochhammer K j

theorem rootPolynomial_degree (lam : K) (hlam : lam ≠ 0) (j : ℕ) :
    (rootPolynomial lam j).degree = j := by
  rw [rootPolynomial, degree_smul_of_isRightRegular_leadingCoeff]
  · exact (degree_eq_natDegree (monic_descPochhammer K j).ne_zero).trans
      (congrArg Nat.cast (descPochhammer_natDegree K j))
  · exact div_ne_zero (inv_ne_zero (pow_ne_zero _ hlam))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
  · rw [(monic_descPochhammer K j).leadingCoeff]
    exact isRegular_one.right

theorem exponentialEvaluation_rootPolynomial (lam : K) (hlam : lam ≠ 0) (j : ℕ) :
    exponentialEvaluation lam (rootPolynomial lam j) = rootSequence lam j := by
  ext n
  change (((lam ^ j)⁻¹ / (j.factorial : K)) • descPochhammer K j).eval (n : K) *
    lam ^ n = rootSequence lam j n
  rw [eval_smul, smul_eq_mul, rootSequence_coeff]
  have hc := Nat.cast_choose_eq_descPochhammer_div (K := K) n j
  by_cases h : j ≤ n
  · rw [ite_eq_left h, pow_sub₀ lam hlam h, hc]
    simp only [div_eq_mul_inv]
    ring
  · rw [ite_eq_right h, descPochhammer_eval_coe_nat_of_lt (R := K) (Nat.lt_of_not_ge h)]
    simp

/-- The normalized falling-factorial polynomials span exactly the bounded-degree
polynomials; evaluation transports this to the accepted root-sequence family. -/
theorem map_degreeLT_exponentialEvaluation (lam : K) (hlam : lam ≠ 0) (m : ℕ) :
    (degreeLT K m).map (exponentialEvaluation lam) =
      Specs.FiniteCombinatorics.Recurrence.rootSpan lam m := by
  classical
  let Q : Polynomial.Sequence K := ⟨rootPolynomial lam, rootPolynomial_degree lam hlam⟩
  have hs : Submodule.span K (rootPolynomial lam '' Set.Iio m) = degreeLT K m :=
    Q.span_degreeLT (fun j _ => isUnit_iff_ne_zero.mpr
      (leadingCoeff_ne_zero.mpr (Q.ne_zero j)))
  rw [← hs, Submodule.map_span]
  change Submodule.span K ((exponentialEvaluation lam) ''
    (rootPolynomial lam '' Set.Iio m)) =
    Submodule.span K (Set.range (fun j : Fin m => rootSequence lam j.val))
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨⟨j, hj⟩, (exponentialEvaluation_rootPolynomial lam hlam j).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨rootPolynomial lam j, ⟨j, j.isLt, rfl⟩,
      exponentialEvaluation_rootPolynomial lam hlam j⟩

/-- The span consists exactly of the exponential polynomial sequences. -/
theorem exponential_polynomial_span (lam : K) (hlam : lam ≠ 0)
    (m : ℕ) (a : ℕ → K) :
    a ∈ Specs.FiniteCombinatorics.Recurrence.rootSpan lam m ↔
      ∃ P : K[X], P.degree < m ∧ ∀ n : ℕ, a n = P.eval (n : K) * lam ^ n := by
  rw [← map_degreeLT_exponentialEvaluation lam hlam m, Submodule.mem_map]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, mem_degreeLT.mp hP, fun _ => rfl⟩
  · rintro ⟨P, hP, h⟩
    exact ⟨P, mem_degreeLT.mpr hP, (funext h).symm⟩

/-- In characteristic zero, values at natural numbers determine a polynomial.
The nonzero exponential factor can be cancelled at every index. -/
theorem exponentialEvaluation_injective (lam : K) (hlam : lam ≠ 0) :
    Function.Injective (exponentialEvaluation lam) := by
  intro P Q h
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
  rintro _ ⟨n, rfl⟩
  exact mul_right_cancel₀ (pow_ne_zero n hlam) (congrFun h n)

/-- The polynomial representing an element of the root span is unique. -/
theorem exponential_polynomial_unique (lam : K) (hlam : lam ≠ 0)
    (m : ℕ) (a : ℕ → K)
    (ha : a ∈ Specs.FiniteCombinatorics.Recurrence.rootSpan lam m) :
    ∃! P : K[X], P.degree < m ∧ ∀ n : ℕ, a n = P.eval (n : K) * lam ^ n := by
  obtain ⟨P, hP, heq⟩ := (exponential_polynomial_span lam hlam m a).mp ha
  refine ⟨P, ⟨hP, heq⟩, ?_⟩
  intro Q hQ
  apply exponentialEvaluation_injective lam hlam
  exact (funext hQ.2).symm.trans (funext heq)

section
omit hchar

/-- Each finite root chain lies in its generalized eigenspace. -/
theorem rootSpan_le_genEigenspace (lam : K) (m : ℕ) :
    Specs.FiniteCombinatorics.Recurrence.rootSpan lam m ≤
      (leftShift (K := K)).genEigenspace lam ⊤ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Module.End.mem_genEigenspace_top.mpr
    ⟨j.val + 1, rootSequence_annihilation lam j.val⟩

/-- The chain for a root of the split characteristic polynomial consists of solutions. -/
theorem rootSpan_le_solutionSpace {r : ℕ} (c : Fin r → K)
    (s : Finset K) (m : K → ℕ)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam)
    (lam : K) (hlam : lam ∈ s) :
    Specs.FiniteCombinatorics.Recurrence.rootSpan lam (m lam) ≤ solutionSpace c := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact rootSequence_mem_solutionSpace c s m hp ⟨⟨lam, hlam⟩, j⟩

/-- Rewriting the accepted repeated-root basis as a sum of its root spans. -/
theorem solutionSpace_eq_iSup_rootSpan {r : ℕ} (c : Fin r → K)
    (s : Finset K) (m : K → ℕ)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam) :
    solutionSpace c = ⨆ lam ∈ s, Specs.FiniteCombinatorics.Recurrence.rootSpan lam (m lam) := by
  classical
  apply le_antisymm
  · intro a ha
    let B := repeatedRootBasis c s m hp
    have heq : a = ∑ i, B.repr ⟨a, ha⟩ i • rootSequence i.1.val i.2.val := by
      have h := congrArg (fun w : solutionSpace c => (w : ℕ → K)) (B.sum_repr ⟨a, ha⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, B, repeatedRootBasis_apply] using h.symm
    rw [heq]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.mem_iSup_of_mem i.1.val
      (Submodule.mem_iSup_of_mem i.1.property (Submodule.subset_span ⟨i.2, rfl⟩))
  · exact iSup_le fun lam => iSup_le fun h => rootSpan_le_solutionSpace c s m hp lam h

end

include hchar

/-- In the recurrence solution module, the generalized eigenspace for a root
is precisely the span of that root's chain. Together with the span and uniqueness
results above, this identifies it with the stated exponential polynomials. -/
theorem exponential_polynomial_root_space {r : ℕ} (c : Fin r → K) (_hr : 1 ≤ r)
    (s : Finset K) (m : K → ℕ) (_hm : ∀ lam ∈ s, 0 < m lam)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam)
    (lam : K) (hlam : lam ∈ s) (_hzero : lam ≠ 0) :
    Specs.FiniteCombinatorics.Recurrence.rootSpan lam (m lam) =
      solutionSpace c ⊓ (leftShift (K := K)).genEigenspace lam ⊤ := by
  classical
  let F : K → Submodule K (ℕ → K) :=
    fun mu => Specs.FiniteCombinatorics.Recurrence.rootSpan mu (m mu)
  have hsplit : solutionSpace c = F lam ⊔ ⨆ mu ∈ s.erase lam, F mu := by
    rw [solutionSpace_eq_iSup_rootSpan c s m hp]
    change (⨆ mu ∈ s, F mu) = _
    have h := congrArg (fun t : Finset K => t.sup F) (Finset.insert_erase hlam)
    rw [Finset.sup_insert] at h
    simpa only [Finset.sup_eq_iSup] using h.symm
  have hd : Disjoint ((leftShift (K := K)).genEigenspace lam ⊤)
      (⨆ mu ∈ s.erase lam, F mu) := by
    have hi := ((leftShift (K := K)).independent_genEigenspace ⊤).disjoint_biSup
      (y := (↑(s.erase lam) : Set K)) (x := lam) (by simp)
    exact hi.mono_right (iSup₂_mono fun mu _ => rootSpan_le_genEigenspace mu (m mu))
  rw [hsplit, sup_inf_assoc_of_le _ (rootSpan_le_genEigenspace lam (m lam)),
    hd.symm.eq_bot, sup_bot_eq]

/-- The full characteristic-zero description, with uniqueness, stated directly
for the corresponding root space of the split recurrence. -/
theorem exponential_polynomial_root_space_iff {r : ℕ} (c : Fin r → K) (hr : 1 ≤ r)
    (s : Finset K) (m : K → ℕ) (hm : ∀ lam ∈ s, 0 < m lam)
    (hp : characteristicPolynomial c = ∏ lam ∈ s, (X - C lam) ^ m lam)
    (lam : K) (hlam : lam ∈ s) (hzero : lam ≠ 0) (a : ℕ → K) :
    (a ∈ solutionSpace c ∧ a ∈ (leftShift (K := K)).genEigenspace lam ⊤) ↔
      ∃! P : K[X], P.degree < m lam ∧ ∀ n : ℕ, a n = P.eval (n : K) * lam ^ n := by
  have hspace := exponential_polynomial_root_space c hr s m hm hp lam hlam hzero
  constructor
  · intro ha
    apply exponential_polynomial_unique lam hzero (m lam) a
    rw [hspace]
    exact ha
  · rintro ⟨P, hP, _⟩
    have ha := (exponential_polynomial_span lam hzero (m lam) a).mpr ⟨P, hP⟩
    rw [hspace] at ha
    exact ha

end FiniteCombinatorics.Recurrence
