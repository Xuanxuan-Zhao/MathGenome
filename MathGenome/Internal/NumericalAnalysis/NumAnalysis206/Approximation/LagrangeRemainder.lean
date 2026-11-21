import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.LagrangeRemainder
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalCalculus
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.Lagrange
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.RepeatedRolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace NumAnalysis206.Approximation
open Set Polynomial

/-- The finite-set version of repeated Rolle, with simple zeros. -/
theorem exists_jet_zero_finset {a b : ℝ} {r : ℕ} {g : ℝ → ℝ}
    {E : ℕ → ℝ → ℝ} (S : Finset ℝ) (hab : a ≤ b)
    (hcard : S.card = r + 1) (hE : IntervalJet a b r g E)
    (hmem : ∀ t ∈ S, t ∈ Icc a b) (hz : ∀ t ∈ S, E 0 t = 0) :
    ∃ ξ ∈ convexHull ℝ (S : Set ℝ), E r ξ = 0 := by
  let l := (S.sort (· ≤ ·)).map (fun t => (t, (1 : ℕ)))
  have hne : l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [l, hcard] at this
  have hpoint : ∀ p ∈ l, p.1 ∈ S := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    simpa using ht
  obtain ⟨ξ, hξ, hzero⟩ := repeated_rolle (N := r + 1) l hne hab (by omega)
    (by simpa using hE) (by
      exact List.pairwise_map.mpr S.sortedLT_sort.pairwise) (by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      exact Nat.zero_lt_one) (fun p hp => hmem p.1 (hpoint p hp)) (by
      simp [l, List.map_map, Function.comp_def, hcard]) (by
      intro p hp j hj
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      have : j = 0 := by simpa using hj
      subst j
      exact hz t (by simpa using ht))
  refine ⟨ξ, ?_, by simpa using hzero⟩
  exact (convex_convexHull ℝ (S : Set ℝ)).ordConnected.out
    (subset_convexHull ℝ _ (hpoint _ (List.head_mem hne)))
    (subset_convexHull ℝ _ (hpoint _ (List.getLast_mem hne))) hξ

/-- Subtract a polynomial from an interval jet using its algebraic derivatives. -/
theorem jet_sub_polynomial {a b : ℝ} {r : ℕ} {f : ℝ → ℝ}
    {D : ℕ → ℝ → ℝ} (hD : IntervalJet a b r f D) (q : ℝ[X]) :
    IntervalJet a b r (fun t => f t - q.eval t)
      (fun j t => D j t - (derivative^[j] q).eval t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp [hD.1 ht]
  · intro j hj
    exact (hD.2.1 j hj).sub (derivative^[j] q).continuous.continuousOn
  · intro j hj t ht
    simpa only [Function.iterate_succ_apply'] using!
      (hD.2.2 j hj t ht).sub ((derivative^[j] q).hasDerivWithinAt t (Icc a b))

/-- Lagrange interpolation remainder, including evaluation at a node. -/
theorem lagrange_remainder : LagrangeRemainderSpec.lagrange_remainder_type := by
  intro ι _ s nodes n a b f D x hab hcard hinj hnodes hx hD
  classical
  let p := interpolant s nodes (f ∘ nodes)
  let S := s.image nodes
  let ω : ℝ[X] := ∏ t ∈ S, (X - C t)
  have hScard : S.card = n + 1 := (Finset.card_image_iff.mpr hinj).trans hcard
  have hωeval (t : ℝ) : ω.eval t = ∏ i ∈ s, (t - nodes i) := by
    simp only [ω, S, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_image hinj
  have hpeval (i : ι) (hi : i ∈ s) : p.eval (nodes i) = f (nodes i) :=
    interpolant_eval s nodes (f ∘ nodes) hinj i hi
  change ∃ ξ ∈ convexHull ℝ (insert x (nodes '' (s : Set ι))),
    f x - p.eval x = D (n + 1) ξ / (n + 1).factorial * ∏ i ∈ s, (x - nodes i)
  by_cases hnode : x ∈ S
  · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hnode
    refine ⟨x, subset_convexHull ℝ _ (mem_insert x _), ?_⟩
    rw [← hix, hpeval i hi, sub_self]
    rw [Finset.prod_eq_zero hi (sub_self (nodes i)), mul_zero]
  · have hωne : ω.eval x ≠ 0 := by
      rw [hωeval]
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact sub_ne_zero.mpr (fun heq => hnode (Finset.mem_image.mpr ⟨i, hi, heq.symm⟩))
    let c := (f x - p.eval x) / ω.eval x
    let q := p - C (-c) * ω
    let E := fun j t => D j t - (derivative^[j] q).eval t
    have hE : IntervalJet a b (n + 1) (fun t => f t - q.eval t) E :=
      jet_sub_polynomial hD q
    have hqeval (t : ℝ) : q.eval t = p.eval t + c * ω.eval t := by
      simp [q]
    have hzero : ∀ t ∈ insert x S, E 0 t = 0 := by
      intro t ht
      change D 0 t - q.eval t = 0
      rcases Finset.mem_insert.mp ht with rfl | ht
      · rw [hD.1 hx, hqeval]
        dsimp [c]
        rw [div_mul_cancel₀ _ hωne]
        ring
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
        have hωzero : ω.eval (nodes i) = 0 := by
          rw [hωeval]
          exact Finset.prod_eq_zero hi (sub_self _)
        rw [hD.1 (hnodes i hi), hqeval, hpeval i hi, hωzero]
        ring
    have hTmem : ∀ t ∈ insert x S, t ∈ Icc a b := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hx
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
        exact hnodes i hi
    obtain ⟨ξ, hξ, hξzero⟩ := exists_jet_zero_finset (insert x S) hab
      (by rw [Finset.card_insert_of_notMem hnode, hScard]) hE hTmem hzero
    have hhull : (↑(insert x S) : Set ℝ) = insert x (nodes '' (s : Set ι)) := by
      simp [S]
    refine ⟨ξ, by simpa only [hhull] using hξ, ?_⟩
    have hpder : derivative^[n + 1] p = 0 :=
      iterate_derivative_eq_zero_of_degree_lt (by
        simpa only [hcard] using interpolant_degree_lt s nodes (f ∘ nodes) hinj)
    have hωder : derivative^[n + 1] ω = ((n + 1).factorial : ℝ[X]) := by
      have h := iterate_derivative_prod_X_sub_C (R := ℝ) (S := S) (k := n + 1)
        (by omega)
      simpa [ω, hScard] using h
    have hqder : derivative^[n + 1] q = C (c * (n + 1).factorial) := by
      simp [q, hpder, hωder, C_mul]
    have hDξ : D (n + 1) ξ = c * (n + 1).factorial := by
      change D (n + 1) ξ - (derivative^[n + 1] q).eval ξ = 0 at hξzero
      rw [hqder, eval_C] at hξzero
      exact sub_eq_zero.mp hξzero
    have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [hDξ, mul_div_cancel_right₀ _ hfac, ← hωeval]
    exact (div_mul_cancel₀ _ hωne).symm

end NumAnalysis206.Approximation
