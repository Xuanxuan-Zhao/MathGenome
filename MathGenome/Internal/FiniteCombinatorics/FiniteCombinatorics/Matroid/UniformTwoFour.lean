import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.RankTwoBound
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.UniformTwoFour
import Mathlib.Tactic.FinCases

namespace FiniteCombinatorics.Matroid
open Set
universe v w

def uniformTwoFour : _root_.Matroid (Fin 4) := Expected.uniformTwoFour
instance : uniformTwoFour.Finite := inferInstanceAs Expected.uniformTwoFour.Finite

def uniformTwoFourColumns (K : Type v) [Field K] (t : K) : Fin 4 → K × K :=
  Expected.uniformTwoFourColumns K t

theorem uniformTwoFourGround : Expected.uniformTwoFourGround := rfl

theorem uniformTwoFourIndep : Expected.uniformTwoFourIndep := by intro I; rfl

private theorem columns_ne_zero (K : Type v) [Field K] (t : K) (i : Fin 4) :
    uniformTwoFourColumns K t i ≠ 0 := by
  fin_cases i <;> simp [uniformTwoFourColumns, Expected.uniformTwoFourColumns]

private theorem columns_pair (K : Type v) [Field K] (t : K) (ht : t ≠ 0) (ht1 : t ≠ 1)
    (i j : Fin 4) (hij : i ≠ j) :
    LinearIndepOn K (uniformTwoFourColumns K t) {i,j} := by
  rw [linearIndepOn_pair_iff _ hij (columns_ne_zero K t i)]
  intro c hc
  have hfst := congrArg Prod.fst hc
  have hsnd := congrArg Prod.snd hc
  fin_cases i <;> fin_cases j <;>
    simp_all [uniformTwoFourColumns, Expected.uniformTwoFourColumns, Prod.smul_mk, smul_eq_mul]

theorem uniformTwoFourColumnsIndep : Expected.uniformTwoFourColumnsIndep := by
  intro K _ t ht ht1 I
  change LinearIndepOn K (uniformTwoFourColumns K t) I ↔ I.ncard ≤ 2
  constructor
  · intro h
    let := (toFinite I).fintype
    have hc := h.fintype_card_le_finrank
    simpa [Module.finrank_prod, Module.finrank_self, fintypeCard_eq_ncard] using hc
  · intro hc
    by_cases hsmall : I.ncard ≤ 1
    · rcases (ncard_le_one_iff_eq (toFinite I)).mp hsmall with rfl | ⟨i, rfl⟩
      · exact linearIndepOn_empty _ _
      · exact (linearIndepOn_singleton_iff K).mpr (columns_ne_zero K t i)
    · have heq : I.ncard = 2 := by omega
      obtain ⟨i,j,hij,rfl⟩ := ncard_eq_two.mp heq
      exact columns_pair K t ht ht1 i j hij

theorem uniformTwoFourRepresents : Expected.uniformTwoFourRepresents := by
  intro K _ t ht ht1 I
  rw [uniformTwoFourIndep I, uniformTwoFourGround]
  simp only [subset_univ, true_and]
  exact (uniformTwoFourColumnsIndep K t ht ht1 I).symm

private theorem uniformTwoFour_nonloop (e : Fin 4) : uniformTwoFour.IsNonloop e := by
  apply _root_.Matroid.Indep.isNonloop
  exact (uniformTwoFourIndep {e}).mpr (by simp)

private theorem uniformTwoFour_simple (e f : Fin 4)
    (h : ParallelRelated uniformTwoFour e f) : e = f := by
  rcases h with h | ⟨hne, hr⟩
  · exact h
  have hi : uniformTwoFour.Indep {e,f} :=
    (uniformTwoFourIndep {e,f}).mpr (by simp [ncard_pair hne])
  have hcard := ((rankRecovery uniformTwoFour {e,f}).mpr hi).2
  rw [ncard_pair hne] at hcard
  change rank uniformTwoFour {e,f} = 1 at hr
  omega

private theorem uniformTwoFour_rank : rank uniformTwoFour uniformTwoFour.E = 2 := by
  have heq : uniformTwoFour.eRk uniformTwoFour.E = 2 := by
    apply le_antisymm
    · apply _root_.Matroid.eRk_le_iff.mpr
      intro I hI hi
      have hc := (uniformTwoFourIndep I).mp hi
      have hfin : I.Finite := finite_univ.subset (subset_univ I)
      rw [← hfin.cast_ncard_eq]
      exact_mod_cast hc
    · apply _root_.Matroid.le_eRk_iff.mpr
      refine ⟨{0,1}, subset_univ _, (uniformTwoFourIndep _).mpr ?_, ?_⟩
      · norm_num
      · exact encard_pair (by decide : (0 : Fin 4) ≠ 1)
  change ((uniformTwoFour.eRk uniformTwoFour.E).toNat : ℤ) = 2
  rw [heq]
  rfl

theorem uniformTwoFourNecessary : Expected.uniformTwoFourNecessary.{v,w} := by
  intro K _ hrep
  classical
  by_contra! hn
  let f : Bool → K := fun b => if b then 1 else 0
  have hf : Function.Surjective f := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simpa [f] using hx.symm⟩
    · exact ⟨true, by simpa [f] using (hn x hx).symm⟩
  let := Finite.of_surjective f hf
  have hk : Nat.card K ≤ 2 := by simpa using Nat.card_le_card_of_surjective f hf
  have hb := rankTwoBound.{0,v,w} K uniformTwoFour hrep
    (fun e _ => uniformTwoFour_nonloop e)
    (fun e _ f _ h => uniformTwoFour_simple e f h) uniformTwoFour_rank
  change (univ : Set (Fin 4)).ncard ≤ _ at hb
  norm_num at hb
  omega

theorem uniformTwoFourRepresentable : Expected.uniformTwoFourRepresentable := by
  intro K _
  constructor
  · exact uniformTwoFourNecessary K
  · rintro ⟨t, ht, ht1⟩
    exact ⟨K × K, inferInstance, inferInstance, uniformTwoFourColumns K t,
      uniformTwoFourRepresents K t ht ht1⟩

theorem fieldThreeElements : Expected.fieldThreeElements := by
  intro K _
  constructor
  · rintro ⟨t, ht, ht1⟩
    exact ⟨0,1,t,zero_ne_one,ht.symm,ht1.symm⟩
  · rintro ⟨a,b,c,hab,hac,hbc⟩
    by_contra! h
    have hcases : ∀ x : K, x = 0 ∨ x = 1 := by
      intro x
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    rcases hcases a with ha | ha <;> rcases hcases b with hb | hb <;>
      rcases hcases c with hc | hc <;> simp_all

theorem uniformTwoFourRepresentableIffThree : Expected.uniformTwoFourRepresentableIffThree := by
  intro K _
  exact (uniformTwoFourRepresentable K).trans (fieldThreeElements K)

theorem uniformTwoFourNotBinary : Expected.uniformTwoFourNotBinary.{v,w} := by
  intro K _ _ hcard hrep
  obtain ⟨t,ht,ht1⟩ := uniformTwoFourNecessary K hrep
  have hinj : Function.Injective (fun i : Fin 3 => (![0,1,t] : Fin 3 → K) i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hc := Nat.card_le_card_of_injective _ hinj
  rw [hcard] at hc
  norm_num at hc

theorem uniformTwoFourNotRepresentableF2 : Expected.uniformTwoFourNotRepresentableF2.{w} := by
  exact uniformTwoFourNotBinary (ZMod 2) (by simp)

end FiniteCombinatorics.Matroid
