import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.Operations
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.GammaProducts
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.Rounding

def dotTrace : DotSpecs.TraceType := DotSpecs.trace
def dotSafe : DotSpecs.SafeType := DotSpecs.safe

theorem dot_boundary_cases : DotSpecs.boundaryCases := by
  intro fused round x y
  exact ⟨rfl, rfl⟩

theorem dot_fused_recurrence : DotSpecs.fusedRecurrence := by
  intro round x y n
  cases n with
  | zero => simp [DotSpecs.trace]
  | succ n => simp [DotSpecs.trace, add_comm]

theorem dot_separate_recurrence : DotSpecs.separateRecurrence := by
  intro round x y n
  rfl

/-- Expand each term along the additions it actually traverses. -/
private theorem trace_chains (fused : Bool) (round : ℝ → ℝ) (x y : ℕ → ℝ)
    (u : ℝ) (D : Set ℝ) (hm : RelativeModel round u D) :
    ∀ n, dotSafe fused round D x y n →
    ∃ ds : ℕ → List ℝ,
      dotTrace fused round x y n =
        ∑ i ∈ Finset.range n, x i * y i * ((ds i).map (1 + ·)).prod ∧
      ∀ i < n, (ds i).length ≤ n ∧ ∀ d ∈ ds i, |d| ≤ u := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro _
      refine ⟨fun _ => [], ?_, ?_⟩
      · simp [dotTrace, DotSpecs.trace]
      · intro i hi; omega
  | one =>
      intro hs
      obtain ⟨a, ha, hau⟩ := relativeModel_error round u D hm (x 0 * y 0) hs
      refine ⟨fun _ => [a], ?_, ?_⟩
      · simpa [dotTrace, DotSpecs.trace] using ha
      · intro i hi
        simp only [List.length_singleton, le_refl, List.mem_singleton, true_and]
        intro d hd; simpa [hd] using hau
  | more n _ ih =>
      intro hs
      change DotSpecs.safe fused round D x y (n + 1) ∧ _ at hs
      obtain ⟨ds, heq, hds⟩ := ih hs.1
      change DotSpecs.trace fused round x y (n + 1) = _ at heq
      obtain ⟨d, hd, hdu⟩ := relativeModel_error round u D hm _ hs.2.2
      have extend (a : ℝ) (ha : |a| ≤ u)
          (hnew : (if fused then x (n + 1) * y (n + 1) else round (x (n + 1) * y (n + 1))) =
            x (n + 1) * y (n + 1) * (1 + a)) :
          ∃ es : ℕ → List ℝ,
            dotTrace fused round x y (n + 2) =
              ∑ i ∈ Finset.range (n + 2), x i * y i * ((es i).map (1 + ·)).prod ∧
            ∀ i < n + 2, (es i).length ≤ n + 2 ∧ ∀ e ∈ es i, |e| ≤ u := by
        let es : ℕ → List ℝ := fun i => if i = n + 1 then [a, d] else d :: ds i
        refine ⟨es, ?_, ?_⟩
        · change round _ = _
          rw [hd, hnew, heq, Finset.sum_range_succ (n := n + 1), add_mul, Finset.sum_mul]
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            have hne : i ≠ n + 1 := by have := Finset.mem_range.mp hi; omega
            simp [es, hne]
            ring
          · simp [es]
            ring
        · intro i hi
          by_cases he : i = n + 1
          · subst i
            simp only [es, ite_eq_left rfl, List.length_cons, List.length_nil, List.mem_cons,
              List.not_mem_nil, or_false]
            refine ⟨by omega, ?_⟩
            intro e he
            rcases he with rfl | rfl <;> assumption
          · have hip : i < n + 1 := by omega
            obtain ⟨hl, hb⟩ := hds i hip
            simp only [es, ite_eq_right he, List.length_cons, List.mem_cons]
            refine ⟨by omega, ?_⟩
            intro e he
            rcases he with rfl | he
            · exact hdu
            · exact hb e he
      by_cases hf : fused = true
      · exact extend 0 (by simpa using hm.1) (by simp [hf])
      · obtain ⟨a, ha, hau⟩ := relativeModel_error round u D hm _ (by simpa [hf] using hs.2.1)
        exact extend a hau (by simpa [hf] using ha)

/-- Apply W06 to a chain of length at most the stated budget. -/
private theorem chain_budget (ds : List ℝ) {n : ℕ} {u : ℝ}
    (hu : BudgetDomain n u) (hl : ds.length ≤ n) (hb : ∀ d ∈ ds, |d| ≤ u) :
    ∃ θ : ℝ, (ds.map (1 + ·)).prod = 1 + θ ∧ |θ| ≤ gamma n u := by
  let δ : ℕ → ℝ := fun k => if h : k < ds.length then ds[k] else 0
  have hd : ∀ k < ds.length, |δ k| ≤ u := by
    intro k hk
    simpa [δ, hk] using hb ds[k] (List.getElem_mem hk)
  obtain ⟨θ, he, ht, _⟩ := signed_products δ (fun _ => 1)
    (budgetDomain_mono hl hu) hd (fun _ _ => Or.inr rfl)
  have hp : (∏ k ∈ Finset.range ds.length, (1 + δ k) ^ (1 : ℤ)) =
      (ds.map (1 + ·)).prod := by
    simp only [zpow_one]
    rw [Finset.prod_range]
    simp [δ]
  exact ⟨θ, hp.symm.trans he, ht.trans (gamma_mono hl hu)⟩

/-- Both evaluation traces have the componentwise representation and forward
absolute bound with the per-term budget n, including n=0. -/
theorem sequential_dot_product : DotSpecs.sequentialDotProduct := by
  intro fused round x y n u D hm hnu hs
  have hmodel : RelativeModel round u D := hm
  have hu : BudgetDomain n u := ⟨hm.1, hm.2.1, hnu⟩
  obtain ⟨ds, heq, hds⟩ := trace_chains fused round x y u D hmodel n hs
  let θ : ℕ → ℝ := fun i => ((ds i).map (1 + ·)).prod - 1
  have hcoef (i : ℕ) : 1 + θ i = ((ds i).map (1 + ·)).prod := by dsimp [θ]; ring
  have hb : ∀ i < n, |θ i| ≤ gamma n u := by
    intro i hi
    obtain ⟨t, ht, htu⟩ := chain_budget (ds i) hu (hds i hi).1 (hds i hi).2
    have he : θ i = t := by dsimp [θ]; linarith
    simpa [he] using htu
  have hexp : DotSpecs.trace fused round x y n =
      ∑ i ∈ Finset.range n, x i * y i * (1 + θ i) := by
    simp_rw [hcoef]
    exact heq
  refine ⟨⟨θ, hexp, hb⟩, ?_⟩
  have herr : DotSpecs.trace fused round x y n - ∑ i ∈ Finset.range n, x i * y i =
      ∑ i ∈ Finset.range n, x i * y i * θ i := by
    rw [hexp, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr]
  calc
    |∑ i ∈ Finset.range n, x i * y i * θ i| ≤
        ∑ i ∈ Finset.range n, |x i * y i * θ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, |x i * y i| * gamma n u := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb i (Finset.mem_range.mp hi)) (abs_nonneg _)
    _ = gamma n u * ∑ i ∈ Finset.range n, |x i * y i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _

/-- Conservative budgets require N u < 1, even when the sharp budget needs only n u < 1. -/
theorem dot_coarse_estimate : DotSpecs.coarseEstimate := by
  intro fused round x y n N u D hm hn hu hs
  have hN : BudgetDomain N u := hu
  have hnu := budgetDomain_mono hn hN
  have he := (sequential_dot_product fused round x y n u D hm hnu.2.2 hs).2
  exact he.trans (mul_le_mul_of_nonneg_right (gamma_mono hn hN)
    (Finset.sum_nonneg (fun i _ => abs_nonneg (x i * y i))))

def finiteDotTrace : DotSpecs.FiniteTraceType := DotSpecs.finiteTrace
def finiteDotSafe : DotSpecs.FiniteSafeType := DotSpecs.finiteSafe

/-- The prefix theorem applied to actual finite vectors, with no hypotheses on
unused coordinates. This also supplies the finite-vector interface downstream. -/
theorem finite_sequential_dot_product : DotSpecs.finiteSequentialDotProduct := by
  intro fused round n x y u D hm hnu hs
  obtain ⟨⟨θ, he, hb⟩, ha⟩ := sequential_dot_product fused round
    (DotSpecs.extendVector x) (DotSpecs.extendVector y) n u D hm hnu hs
  refine ⟨⟨fun i => θ i.val, ?_, ?_⟩, ?_⟩
  · simpa [DotSpecs.finiteTrace, Finset.sum_range, DotSpecs.extendVector] using he
  · intro i
    exact hb i.val i.isLt
  · simpa [DotSpecs.finiteTrace, Finset.sum_range, DotSpecs.extendVector] using ha

/-- Specialization to the finite radix model's stored input values. -/
theorem stored_dot_product : DotSpecs.storedDotProduct := by
  intro P fused n x y u D hm hnu hs
  exact finite_sequential_dot_product fused (Specs.flValue P) n
    (fun i => (x i).val) (fun i => (y i).val) u D hm hnu hs

end NumAnalysis206.Rounding
