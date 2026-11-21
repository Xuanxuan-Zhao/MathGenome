import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.IncidenceTU
import MathGenome.Internal.ExtremalOptimization.P205.Polyhedra.TotalUnimodularity
import MathGenome.Internal.ExtremalOptimization.P205.Matching.Models
import Lean.Elab.Tactic.Omega

/-! The two incidence-matrix assertions of paper.tex W35. -/

universe u v
noncomputable section
open scoped BigOperators
namespace P205.Networks

abbrev directedIncidence : Specs.P205.Networks.directedIncidenceType.{u, v} :=
  @Specs.P205.Networks.directedIncidence.{u, v}

/-- The determinant induction for columns having at most one +1 and at most
one -1. The pairwise condition expresses that any two nonzero entries in a
column have opposite signs. It is preserved on deleting rows and columns. -/
lemma det_mem_signs_of_column_condition (k : ℕ) (A : Matrix (Fin k) (Fin k) ℤ)
    (hentry : ∀ i j, A i j ∈ Set.range (SignType.cast : SignType → ℤ))
    (hpair : ∀ i i' j, i ≠ i' → A i j ≠ 0 → A i' j ≠ 0 → A i j = - A i' j) :
    A.det ∈ Set.range (SignType.cast : SignType → ℤ) := by
  classical
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    by_cases hsparse : ∃ j i, ∀ r, r ≠ i → A r j = 0
    · obtain ⟨j, i, hi⟩ := hsparse
      rw [Matrix.det_succ_column A j, Fintype.sum_eq_single i]
      · change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
        apply mul_mem
        · apply mul_mem
          · apply pow_mem
            exact ⟨-1, by simp⟩
          · exact hentry i j
        · apply ih
          · intro r c
            exact hentry _ _
          · intro r s c hrs hr hs
            exact hpair _ _ _ (Fin.succAbove_right_injective.ne hrs) hr hs
      · intro r hri
        simp [hi r hri]
    · have hsum : ∀ j, ∑ i, A i j = 0 := by
        intro j
        have hn : ∀ i, ∃ r, r ≠ i ∧ A r j ≠ 0 := by
          intro i
          by_contra hn
          apply hsparse
          refine ⟨j, i, ?_⟩
          intro r hri
          by_contra hr
          exact hn ⟨r, hri, hr⟩
        obtain ⟨p, _, hp⟩ := hn 0
        obtain ⟨q, hqp, hq⟩ := hn p
        have hpq := hpair p q j hqp.symm hp hq
        have hz : ∀ r, r ≠ p → r ≠ q → A r j = 0 := by
          intro r hrp hrq
          by_contra hr
          have hrp' := hpair r p j hrp hr hp
          have hrq' := hpair r q j hrq hr hq
          omega
        calc
          ∑ r, A r j = ∑ r, ((if r = p then A p j else 0) +
              (if r = q then A q j else 0)) := by
            apply Finset.sum_congr rfl
            intro r _
            by_cases hrp : r = p
            · subst r; simp [hqp.symm]
            · by_cases hrq : r = q
              · subst r; simp [hqp]
              · simp [hrp, hrq, hz r hrp hrq]
          _ = A p j + A q j := by simp [Finset.sum_add_distrib]
          _ = 0 := by omega
      have hrows : (∑ i, (1 : ℤ) • A i) = 0 := by
        ext j
        simpa only [one_smul, Pi.zero_apply] using
          (Finset.sum_apply j Finset.univ (fun i => A i)).trans (hsum j)
      have hd := Matrix.det_updateRow_sum A 0 (fun _ => (1 : ℤ))
      rw [hrows] at hd
      have hzero : (A.updateRow 0 0).det = 0 :=
        Matrix.det_eq_zero_of_row_eq_zero 0 (by intro j; simp)
      refine ⟨0, ?_⟩
      simpa [hzero] using hd

/-- Net-outflow node--arc incidence is TU, including loops and parallel labels. -/
theorem directed_incidence_tu : Specs.P205.Networks.directed_incidence_tu.{u, v} := by
  intro V E tail head k f g hf _
  apply det_mem_signs_of_column_condition
  · intro i j
    simp only [Matrix.submatrix_apply, Specs.P205.Networks.directedIncidence]
    split_ifs <;> simp [SignType.range_eq, SignType.cast]
  · intro i i' j hii' hi hi'
    have hfi : f i ≠ f i' := hf.ne hii'
    simp only [Matrix.submatrix_apply, Specs.P205.Networks.directedIncidence] at hi hi' ⊢
    split_ifs at * <;> simp_all

/-- Exact orientation and row-sign bridge for the existing allowed-edge matrix. -/
theorem bipartite_orientation : Specs.P205.Networks.bipartite_orientation.{u, v} := by
  intro L R G
  classical
  ext (i | j) e <;>
    simp [Specs.P205.Networks.directedIncidence, Specs.P205.Matching.incidence,
      Specs.P205.Matching.incident] <;> rfl

/-- Unsigned vertex--edge incidence of every bipartite graph is TU. -/
theorem bipartite_incidence_tu : Specs.P205.Networks.bipartite_incidence_tu.{u, v} := by
  intro L R G
  let s : L ⊕ R → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)
  have hs : ∀ i, s i = 1 ∨ s i = -1 := by rintro (i | j) <;> simp [s]
  have hdir := directed_incidence_tu
    (fun e : Specs.P205.Matching.Edge G => Sum.inl e.val.1)
    (fun e => Sum.inr e.val.2)
  have h := P205.Polyhedra.TotalUnimodularity.row_signs hdir s hs
  rw [bipartite_orientation G] at h
  have heq : Matrix.of (fun i e => s i *
      Matrix.of (fun i e => s i * Specs.P205.Matching.incidence G i e) i e) =
      Specs.P205.Matching.incidence G := by
    ext (i | j) e <;> simp [s]
  exact heq ▸ h

end P205.Networks
