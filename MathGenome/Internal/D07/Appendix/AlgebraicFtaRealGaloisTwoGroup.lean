import MathGenome.Internal.Specs.D07.Appendix.AlgebraicFtaRealGaloisTwoGroup
import MathGenome.Internal.D07.Appendix.RealOddExtensions
import MathGenome.Internal.D07.Ch06.SylowExistence
import MathGenome.Internal.D07.Ch14.DegreeIndex
import MathGenome.Internal.D07.Ch14.FundamentalCorrespondence

/-!
The Sylow-2 argument in the algebraic FTA appendix. Write the positive
Galois group order as 2^a m with m odd. Sylow existence supplies a subgroup
of order 2^a and hence index m. Its fixed field has odd real degree, so
all its elements are real scalars. The Galois correspondence makes the
subgroup the full group. This uses neither the complex FTA nor any
transcendence result.
-/

universe u

namespace D07.Appendix.AlgebraicFtaRealGaloisTwoGroup

open Specs.D07.Appendix.AlgebraicFtaRealGaloisTwoGroup

theorem odd_index_fixed_field : OddIndexFixedField.{u} := by
  intro L _ _ _ _ H hodd
  let E := IntermediateField.fixedField H
  have hdegree : Module.finrank ℝ E = H.index :=
    (Ch14.DegreeIndex.degree_index ℝ L H).2.1
  have hsurj := RealOddExtensions.odd_extension_surjective E (hdegree.symm ▸ hodd)
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, hr⟩ := hsurj ⟨x, hx⟩
  exact IntermediateField.mem_bot.mpr ⟨r, congrArg Subtype.val hr⟩

theorem odd_index_subgroup : OddIndexSubgroup.{u} := by
  intro L _ _ _ _ H hodd
  have hfixed := odd_index_fixed_field L H hodd
  have hinverse := Ch14.FundamentalCorrespondence.fixing_subgroup_fixed_field ℝ L H
  change (IntermediateField.fixedField H).fixingSubgroup = H at hinverse
  rw [hfixed, IntermediateField.fixingSubgroup_bot] at hinverse
  exact hinverse.symm

theorem finite_galois_two_group : FiniteGaloisTwoGroup.{u} := by
  intro L _ _ _ _
  let G := L ≃ₐ[ℝ] L
  obtain ⟨a, m, hm, hcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := G)).ne' 2 (by decide)
  obtain ⟨H, hH⟩ :=
    Ch06.SylowExistence.largest_prime_power_existence G 2 a m (by decide) hcard hm
  have hindex : H.index = m := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) a)
    calc
      2 ^ a * H.index = Nat.card H * H.index := by rw [hH]
      _ = Nat.card G := H.card_mul_index
      _ = 2 ^ a * m := hcard
  have hodd : Odd H.index := by
    rw [hindex]
    exact Nat.not_even_iff_odd.mp (fun he => hm he.two_dvd)
  have htop : H = ⊤ := odd_index_subgroup L H hodd
  refine ⟨inferInstance, a, ?_⟩
  simpa [htop] using hH

end D07.Appendix.AlgebraicFtaRealGaloisTwoGroup
