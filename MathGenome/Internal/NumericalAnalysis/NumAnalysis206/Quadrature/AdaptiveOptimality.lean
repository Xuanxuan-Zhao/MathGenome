import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.AdaptiveOptimality
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.GramSupport

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

namespace NumAnalysis206.Quadrature

/-- Induction on the answers shows that a function vanishing at the zero-path
queries has the all-zero transcript. -/
lemma pointTranscript_eq_zero_of_vanishes (q : AdaptiveQueries) (f : ℝ → ℝ)
    (n : ℕ) (hf : ∀ k < n, f (q k 0) = 0) :
    pointTranscript q f n = 0 := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hprev : pointTranscript q f n = 0 := ih (fun k hk => hf k (by omega))
    simp only [pointTranscript, hprev, hf n (by omega)]
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

lemma pointTranscript_zero (q : AdaptiveQueries) (n : ℕ) :
    pointTranscript q (fun _ => 0) n = 0 :=
  pointTranscript_eq_zero_of_vanishes q _ n (by simp)

/-- The nodal product permits repeated query locations: it remains monic of
exactly the query-budget degree. -/
def zeroPathProduct (q : AdaptiveQueries) (n : ℕ) : ℝ[X] :=
  ∏ i : Fin n, (X - C (q i.val 0))

lemma zeroPathProduct_monic (q : AdaptiveQueries) (n : ℕ) :
    (zeroPathProduct q n).Monic :=
  monic_prod_X_sub_C (fun i : Fin n => q i.val 0) Finset.univ

lemma zeroPathProduct_natDegree (q : AdaptiveQueries) (n : ℕ) :
    (zeroPathProduct q n).natDegree = n := by
  simp [zeroPathProduct]

lemma zeroPathProduct_eval (q : AdaptiveQueries) (n : ℕ) (k : ℕ) (hk : k < n) :
    (zeroPathProduct q n).eval (q k 0) = 0 := by
  classical
  simp only [zeroPathProduct, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨k, hk⟩ : Fin n)) (sub_self _)

theorem adaptive_fooling_polynomial : Specs.adaptiveFoolingPolynomial := by
  intro μ _ n hm hG q
  let r := zeroPathProduct q n
  have hr0 : r ≠ 0 := (zeroPathProduct_monic q n).ne_zero
  have hdeg : r.natDegree ≤ n := (zeroPathProduct_natDegree q n).le
  have hpos := polynomial_square_positive μ n hm hG r hr0 hdeg
  refine ⟨r ^ 2, ?_, ?_, ?_⟩
  · calc
      (r ^ 2).natDegree ≤ 2 * r.natDegree := natDegree_pow_le
      _ ≤ 2 * n := by omega
  · rw [pointTranscript_zero]
    apply pointTranscript_eq_zero_of_vanishes
    intro k hk
    simp only [eval_pow]
    change ((zeroPathProduct q n).eval (q k 0)) ^ 2 = 0
    rw [zeroPathProduct_eval q n k hk]
    norm_num
  · simpa only [eval_pow] using hpos

theorem adaptive_optimality : Specs.adaptiveOptimality := by
  intro μ _ n _hn hm hG q output hexact
  obtain ⟨p, hp, htranscript, hpos⟩ := adaptive_fooling_polynomial μ n hm hG q
  have hz := hexact 0 (by simp)
  have hpExact := hexact p hp
  have hsame : pointRule n q output (fun x => p.eval x) =
      pointRule n q output (fun _ => 0) := congrArg output htranscript
  have hout : pointRule n q output (fun _ => 0) = 0 := by
    simpa only [eval_zero, integral_zero] using hz
  rw [hsame, hout] at hpExact
  exact (ne_of_gt hpos) hpExact.symm

end NumAnalysis206.Quadrature
