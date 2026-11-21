import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.CellLengthSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.LocalizedComparison
import Mathlib.Tactic.Ring

noncomputable section
namespace D03Insertion

theorem localized_tagged_sum_comparison :
    Specification.localized_tagged_sum_comparisonType := by
  classical
  intro K _ _ a b hab s n t p q r hp hq hr hu f M hM hf ξ hξ
  obtain ⟨c, hc, hc_unique, hunchanged, hsingle⟩ :=
    refined_cell_geometry hab hp hq hr hu
  have hends : ∀ j, c j ∉ marked p q →
      left r j = left q (c j) ∧ right r j = right q (c j) := by
    intro j hj
    obtain ⟨k, hk, _⟩ := hunchanged (c j) hj
    have hfiber := (hsingle (c j) k).mpr ⟨hk, hj⟩
    have hjk : j = k := (hfiber j).mp rfl
    exact hjk ▸ hk
  let endpoint : Fin t → Set.Icc a b := fun j =>
    ⟨left r j, (cell_endpoint_bounds hr j).1,
      (sub_pos.mp (width_pos hr j)).le.trans (cell_endpoint_bounds hr j).2⟩
  let ζ : Fin t → Set.Icc a b := fun j =>
    if c j ∉ marked p q then ξ (c j) else endpoint j
  have hζ : Legal r ζ := by
    intro j
    by_cases hj : c j ∉ marked p q
    · have he := hends j hj
      simpa only [ζ, ite_eq_left hj, he.1, he.2] using hξ (c j)
    · simp only [ζ, ite_eq_right hj, endpoint]
      exact ⟨le_rfl, (sub_pos.mp (width_pos hr j)).le⟩
  have hpreserve : ∀ i, i ∉ marked p q → ∀ j,
      left r j = left q i → right r j = right q i → ζ j = ξ i := by
    intro i hi j hL hR
    have hci : c j = i := hc_unique j i ⟨hL.ge, hR.le⟩
    simp only [ζ, hci, ite_eq_left hi]
  let fiber : Fin n → Finset (Fin t) := fun i =>
    Finset.univ.filter (fun j => c j = i)
  have hlength : ∀ i, ∑ j ∈ fiber i, width r j = width q i :=
    refined_cell_length_sum hab hp hq hr hu c hc
  let E : Fin n → K := fun i => width q i • f (ξ i) -
    ∑ j ∈ fiber i, width r j • f (ζ j)
  have hzero : ∀ i, i ∉ marked p q → E i = 0 := by
    intro i hi
    have htags : ∀ j ∈ fiber i, ζ j = ξ i := by
      intro j hj
      have hci : c j = i := (Finset.mem_filter.mp hj).2
      simp only [ζ, hci, ite_eq_left hi]
    have heq : (∑ j ∈ fiber i, width r j • f (ζ j)) =
        width q i • f (ξ i) := by
      calc
        _ = ∑ j ∈ fiber i, width r j • f (ξ i) :=
          Finset.sum_congr rfl (fun j hj => by rw [htags j hj])
        _ = (∑ j ∈ fiber i, width r j) • f (ξ i) :=
          Finset.sum_smul.symm
        _ = _ := by rw [hlength i]
    exact sub_eq_zero.mpr heq.symm
  have hterm : ∀ {k : ℕ} (u : Fin (k + 1) → ℝ),
      ValidPartition a b u → ∀ (i : Fin k) (x : Set.Icc a b),
      ‖width u i • f x‖ ≤ width u i * M := by
    intro k u hu i x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (width_pos hu i)]
    exact mul_le_mul_of_nonneg_left (hf x) (width_pos hu i).le
  have hlocal : ∀ i, ‖E i‖ ≤ 2 * M * width q i := by
    intro i
    have hrefined : ‖∑ j ∈ fiber i, width r j • f (ζ j)‖ ≤ width q i * M := by
      calc
        _ ≤ ∑ j ∈ fiber i, ‖width r j • f (ζ j)‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ fiber i, width r j * M :=
          Finset.sum_le_sum (fun j _ => hterm r hr j (ζ j))
        _ = width q i * M := by rw [← Finset.sum_mul, hlength i]
    calc
      ‖E i‖ ≤ ‖width q i • f (ξ i)‖ +
          ‖∑ j ∈ fiber i, width r j • f (ζ j)‖ := norm_sub_le _ _
      _ ≤ width q i * M + width q i * M :=
        add_le_add (hterm q hq i (ξ i)) hrefined
      _ = 2 * M * width q i := by ring
  have hsum : taggedSum f q ξ - taggedSum f r ζ = ∑ i : Fin n, E i := by
    unfold taggedSum
    rw [parent_fiber_sum c (fun j => width r j • f (ζ j))]
    exact (Finset.sum_sub_distrib _ _).symm
  refine ⟨ζ, hζ, hpreserve, ?_⟩
  calc
    ‖taggedSum f q ξ - taggedSum f r ζ‖ = ‖∑ i : Fin n, E i‖ := by rw [hsum]
    _ = ‖∑ i ∈ marked p q, E i‖ := by
      congr 1
      exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)).symm
    _ ≤ ∑ i ∈ marked p q, ‖E i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ marked p q, 2 * M * width q i :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = 2 * M * (∑ i ∈ marked p q, width q i) := by rw [Finset.mul_sum]

end D03Insertion
