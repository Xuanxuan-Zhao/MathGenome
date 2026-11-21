import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreierCyclicDegreePConverse
import MathGenome.Internal.D07.Ch20.Hilbert90Additive
import Mathlib.Algebra.CharP.Algebra

/-! Artin–Schreier generators of cyclic extensions of degree p in characteristic p.
The trace-zero argument never divides by the degree. -/

universe u v
namespace D07.Ch20.ArtinSchreierCyclicDegreePConverse

noncomputable section

open IntermediateField

/-- The required generator, for any chosen generator of the cyclic Galois group. -/
theorem cyclic_degree_p_converse :
    Specs.D07.Ch20.ArtinSchreierCyclicDegreePConverse.CyclicDegreePConverse.{u,v} := by
  intro K L _ _ _ p _ _ _ _ hdeg σ hσ
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have htrace : Algebra.trace K L (-1) = 0 := by
    have h1 : Algebra.trace K L 1 = (p : K) := by
      simpa [hdeg] using (Algebra.trace_algebraMap (R := K) (S := L) (1 : K))
    rw [map_neg, h1, CharP.cast_eq_zero, neg_zero]
  obtain ⟨θ, hθ⟩ := (Hilbert90Additive.additive_hilbert90 K L σ hσ (-1)).mp htrace
  have htrans : σ θ = θ + 1 := by linear_combination hθ
  have hnotbase : θ ∉ (⊥ : IntermediateField K L) := by
    intro h
    obtain ⟨c, hc⟩ := (IntermediateField.mem_bot).mp h
    have hfix : σ θ = θ := by rw [← hc]; exact σ.commutes c
    have : (1 : L) = 0 := by linear_combination hfix - htrans
    exact one_ne_zero this
  have hprim : adjoin K ({θ} : Set L) = ⊤ := by
    have : IsSimpleOrder (IntermediateField K L) :=
      IntermediateField.isSimpleOrder_of_finrank_prime K L (hdeg.symm ▸ Fact.out)
    rcases eq_bot_or_eq_top (adjoin K ({θ} : Set L)) with h | h
    · exact False.elim (hnotbase (h ▸ mem_adjoin_simple_self K θ))
    · exact h
  have hfixed : σ (θ ^ p - θ) = θ ^ p - θ := by
    rw [map_sub, map_pow, htrans, add_pow_char, one_pow]
    ring
  obtain ⟨a, ha⟩ := (Hilbert90Additive.fixed_generator_iff K L σ hσ _).mp hfixed
  refine ⟨θ, a, htrans, ha.symm, ?_, hprim⟩
  rintro ⟨c, hc⟩
  have hpow : (θ - algebraMap K L c) ^ p = θ - algebraMap K L c := by
    rw [sub_pow_char]
    have hrel : θ ^ p - θ = (algebraMap K L c) ^ p - algebraMap K L c := by
      rw [← ha, hc, map_sub, map_pow]
    linear_combination hrel
  have hbot := (Subfield.mem_bot_iff_pow_eq_self L p).mpr hpow
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p L).mp hbot
  have hfix : σ (θ - algebraMap K L c) = θ - algebraMap K L c := by
    rw [← hn, map_intCast]
  rw [map_sub, σ.commutes, htrans] at hfix
  have : (1 : L) = 0 := by linear_combination hfix
  exact one_ne_zero this

end
end D07.Ch20.ArtinSchreierCyclicDegreePConverse
