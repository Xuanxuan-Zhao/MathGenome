import MathGenome.Internal.Specs.D05.M05.Alternating
import MathGenome.Internal.D05.Foundations.PermutationSign

/-! K05.05.alternating: alternation, signs, and the characteristic-two boundary. -/

namespace D05.M05.Alternating

open D05.Specs.Alternating

/-- Bundle the paper's vanishing condition without adding any hypotheses. -/
theorem alternating_iff_bundled : D05.Specs.Alternating.alternating_iff_bundled := by
  intro R M _ _ _ n f
  constructor
  · intro h
    exact ⟨⟨f, h⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact fun v i j heq hij => a.map_eq_zero_of_eq v heq hij

theorem cross_terms : D05.Specs.Alternating.cross_terms := by
  intro R M _ _ _ n f hf v i j hij u w
  let a : AlternatingMap R M R (Fin n) := ⟨f, hf⟩
  have h := a.map_update_update v hij (u + w)
  simp only [a.map_update_add] at h
  rw [Function.update_comm hij (u + w) u v,
    Function.update_comm hij (u + w) w v] at h
  simp only [a.map_update_add] at h
  have hu' := a.map_update_update v hij.symm u
  have hw' := a.map_update_update v hij.symm w
  rw [hu', hw', zero_add, add_zero] at h
  rw [Function.update_comm hij.symm u w v,
    Function.update_comm hij.symm w u v, add_comm] at h
  exact h.symm

theorem swap_neg : D05.Specs.Alternating.swap_neg := by
  intro R M _ _ _ n f hf v i j hij
  exact (show AlternatingMap R M R (Fin n) from ⟨f, hf⟩).map_swap v hij

theorem permutation_rule : D05.Specs.Alternating.permutation_rule := by
  intro R M _ _ _ n f hf σ v
  let a : AlternatingMap R M R (Fin n) := ⟨f, hf⟩
  have h := a.map_perm v σ
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_eq_mul] at h
  rw [D05.Foundations.PermutationSign.signIdentification n σ]
  exact h

theorem converse_char_ne_two : D05.Specs.Alternating.converse_char_ne_two := by
  intro K M _ _ _ n f h2 hf v i j heq hij
  have hsame : v ∘ Equiv.swap i j = v := by
    funext k
    exact Equiv.apply_swap_eq_self heq k
  have h := hf (Equiv.swap i j) v
  rw [hsame, D05.Foundations.PermutationSign.signTransposition n i j hij] at h
  have hsum : f v + f v = 0 := by
    simpa using (eq_neg_iff_add_eq_zero.mp (by simpa using h))
  exact (mul_eq_zero.mp (by simpa only [two_mul] using hsum)).resolve_left h2

/-- The bilinear multiplication form on a scalar ring. -/
def multiplication_form : D05.Specs.Alternating.multiplication_form_type :=
  D05.Specs.Alternating.multiplication_form_value

theorem multiplication_formula : D05.Specs.Alternating.multiplication_formula := by
  intro R _ v
  simp [multiplicationForm, Fin.prod_univ_two]

theorem characteristic_two_counterexample :
    D05.Specs.Alternating.characteristic_two_counterexample := by
  intro K _ _
  have hsign (σ : Equiv.Perm (Fin 2)) :
      (D05.Foundations.permutationSign σ : K) = 1 := by
    simp [D05.Foundations.permutationSign, Int.cast_pow, CharTwo.neg_one_eq_one]
  have hinv (σ : Equiv.Perm (Fin 2)) (v : Fin 2 → K) :
      multiplicationForm K (v ∘ σ) = multiplicationForm K v := by
    simpa only [multiplicationForm, MultilinearMap.mkPiAlgebra_apply, Function.comp_apply]
      using Equiv.prod_comp σ v
  refine ⟨?_, fun v => hinv (Equiv.swap 0 1) v, ?_, ?_⟩
  · intro σ v
    rw [hsign, one_mul]
    exact hinv σ v
  · simp [multiplicationForm]
  · intro h
    have hz := h (fun _ => 1) 0 1 rfl (by decide)
    simp [multiplicationForm] at hz

end D05.M05.Alternating
