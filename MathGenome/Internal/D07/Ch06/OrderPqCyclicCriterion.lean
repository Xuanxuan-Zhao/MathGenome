import MathGenome.Internal.Specs.D07.Ch06.OrderPqCyclicCriterion
import MathGenome.Internal.D07.Ch02.CyclicAutomorphisms
import MathGenome.Internal.D07.Ch04.InternalDirectProduct
import MathGenome.Internal.D07.Ch04.OrderProductElement
import MathGenome.Internal.D07.Ch04.SemidirectProduct
import MathGenome.Internal.D07.Ch06.Cauchy
import MathGenome.Internal.D07.Ch06.SylowCounting
import MathGenome.Internal.D07.Ch06.SylowNormalIffUnique

namespace D07.Ch06.OrderPqCyclicCriterion

universe u
open scoped Pointwise

/-- Sylow arithmetic: if r does not divide s-1, there is only one Sylow r-subgroup
in a group of order r*s, for distinct primes r and s. -/
theorem sylow_count_eq_one (G : Type u) [Group G] [Finite G]
    (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hne : r ≠ s)
    (hcard : Nat.card G = r * s) (hnd : ¬ r ∣ s - 1) :
    Nat.card (Sylow r G) = 1 := by
  have hnot : ¬ r ∣ s := fun h => hne ((Nat.prime_dvd_prime_iff_eq hr hs).mp h)
  have hcard' : Nat.card G = r ^ 1 * s := by simpa using hcard
  have hcount := SylowCounting.card_subgroups_eq_card_sylow G r 1 s hr hcard' hnot
  have hdiv := SylowCounting.count_dvd_cofactor G r 1 s hr hcard' hnot
  have hmod := SylowCounting.count_modEq_one G r 1 s hr hcard' hnot
  rw [hcount] at hdiv hmod
  rcases (Nat.dvd_prime hs).mp hdiv with h | h
  · exact h
  · exact False.elim (hnd (by simpa only [h] using hmod.symm.dvd'))

theorem large_prime_sylow_normal :
    Specs.D07.Ch06.OrderPqCyclicCriterion.LargePrimeSylowNormal.{u} := by
  intro G _ _ p q hp hq hpq hcard Q
  apply (SylowNormalIffUnique.normal_iff_count_one G q hq Q).mpr
  apply sylow_count_eq_one G q p hq hp (Ne.symm hpq.ne)
    (by simpa only [Nat.mul_comm] using hcard)
  exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt)
    ((Nat.sub_le p 1).trans_lt hpq)

/-- In the nondivisibility case the two prime-order factors are both normal. -/
theorem cyclic_of_not_dvd :
    Specs.D07.Ch06.OrderPqCyclicCriterion.CyclicOfNotDvd.{u} := by
  intro G _ _ p q hp hq hpq hcard hnd
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hP⟩ := Cauchy.exists_subgroup_card_eq G p hp (hcard ▸ dvd_mul_right p q)
  obtain ⟨Q, hQ⟩ := Cauchy.exists_subgroup_card_eq G q hq (hcard ▸ dvd_mul_left q p)
  have hnp : ¬ p ∣ q := fun h => hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hnq : ¬ q ∣ p := fun h => hpq.ne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  obtain ⟨SP, hSP⟩ := (SylowDefinition.sylow_iff_card G p 1 q hp
    (by simpa using hcard) hnp P).mpr (by simpa using hP)
  obtain ⟨SQ, hSQ⟩ := (SylowDefinition.sylow_iff_card G q 1 p hq
    (by simpa [Nat.mul_comm] using hcard) hnq Q).mpr (by simpa using hQ)
  have hPN : P.Normal := hSP ▸
    (SylowNormalIffUnique.normal_iff_count_one G p hp SP).mpr
      (sylow_count_eq_one G p q hp hq hpq.ne hcard hnd)
  have hQN : Q.Normal := hSQ ▸ large_prime_sylow_normal G p q hp hq hpq hcard SQ
  let := hPN
  let := hQN
  have hcop : (Nat.card P).Coprime (Nat.card Q) := by
    rw [hP, hQ]
    exact hp.coprime_iff_not_dvd.mpr hnp
  have hcomp := Subgroup.isComplement'_of_coprime
    (H := P) (K := Q) (by rw [hP, hQ, hcard]) hcop
  obtain ⟨e, _he⟩ := D07.Ch04.InternalDirectProduct.internal_direct_product G P Q
    hcomp.disjoint.eq_bot hcomp.mul_eq
  let : IsCyclic P := isCyclic_of_prime_card hP
  let : IsCyclic Q := isCyclic_of_prime_card hQ
  let : IsCyclic (P × Q) :=
    (D07.Ch04.OrderProductElement.finite_cyclic_product_iff P Q).mpr hcop
  let : IsCyclic G := isCyclic_of_surjective e.toMonoidHom e.surjective
  have ecyc := (zmodCyclicMulEquiv (G := G) inferInstance).symm
  rw [hcard] at ecyc
  exact ⟨ecyc⟩

theorem nonabelian_semidirect_exists :
    Specs.D07.Ch06.OrderPqCyclicCriterion.NonabelianSemidirectExists := by
  intro p q hp hq _hpq hdiv
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let N := Multiplicative (ZMod q)
  let H := Multiplicative (ZMod p)
  have hN : Nat.card N = q := by simp [N]
  have hH : Nat.card H = p := by simp [H]
  have haut : Nat.card (MulAut N) = q - 1 := by
    rw [IsCyclic.card_mulAut, hN, Nat.totient_prime hq]
  obtain ⟨a, ha⟩ := Cauchy.exists_element_order_eq (MulAut N) p hp (haut ▸ hdiv)
  let A := Subgroup.zpowers a
  have hA : Nat.card A = p := (Nat.card_zpowers a).trans ha
  let e : H ≃* A := mulEquivOfCyclicCardEq (hH.trans hA.symm)
  let φ : H →* MulAut N := A.subtype.comp e.toMonoidHom
  have ha1 : a ≠ 1 := by
    intro h
    simp only [h, orderOf_one] at ha
    exact hp.ne_one ha.symm
  obtain ⟨h, hh⟩ := e.surjective (⟨a, Subgroup.mem_zpowers a⟩ : A)
  have hφ : φ h = a := congrArg Subtype.val hh
  have hmove : ∃ n : N, a n ≠ n := by
    by_contra! h
    apply ha1
    ext n
    exact h n
  obtain ⟨n, hn⟩ := hmove
  refine ⟨φ, ?_, SemidirectProduct.inr h, SemidirectProduct.inl n, ?_⟩
  · rw [SemidirectProduct.card, hN, hH, Nat.mul_comm]
  · intro hcomm
    have heq := congrArg SemidirectProduct.left hcomm
    have : a n = n := by simpa [SemidirectProduct.mul_left, hφ] using heq
    exact hn this

theorem cyclic_model_exists :
    Specs.D07.Ch06.OrderPqCyclicCriterion.CyclicModelExists := by
  intro p q hp hq _
  let : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  refine ⟨inferInstance, ?_, inferInstance⟩
  simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

end D07.Ch06.OrderPqCyclicCriterion
