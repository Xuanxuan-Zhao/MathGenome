import MathGenome.Internal.Specs.D07.Ch19.SturmChain
import MathGenome.Internal.D07.Ch19.SturmChainSquarefreeReduction
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

noncomputable section

namespace D07.Ch19.SturmChain

open Polynomial
open Specs.D07.Ch19.SturmChain
open scoped Classical

variable {K : Type*} [Field K]

/-- The normalized monic gcd is invariant under the signed remainder step. -/
theorem gcd_signed_remainder (p q : Polynomial K) :
    gcd q (-(p % q)) = gcd p q := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
  · apply dvd_gcd
    · exact (EuclideanDomain.dvd_mod_iff (gcd_dvd_left q (-(p % q)))).mp
        (dvd_neg.mp (gcd_dvd_right q (-(p % q))))
    · exact gcd_dvd_left _ _
  · exact dvd_gcd (gcd_dvd_right _ _)
      (dvd_neg.mpr ((EuclideanDomain.dvd_mod_iff (gcd_dvd_right p q)).mpr
        (gcd_dvd_left p q)))

/-- Coprimality propagates without any assumption about the remainder being nonzero. -/
theorem coprime_signed_remainder {p q : Polynomial K} (h : IsCoprime p q) :
    IsCoprime q (-(p % q)) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a * (p / q) + b, -a, ?_⟩
  rw [EuclideanDomain.mod_eq_sub_mul_div]
  calc
    (a * (p / q) + b) * q + -a * -(p - q * (p / q)) = a * p + b * q := by ring
    _ = 1 := hab

/-- Every list produced by the library sequence obeys the source's signed
remainder identities, including its stopping rule. -/
theorem division_laws (p q : Polynomial K) : DivisionLaws (sturmSeq p q) := by
  induction p, q using sturmSeq.induct
  next q => simp [DivisionLaws]
  next p q hp ih =>
    rw [sturmSeq_cons hp]
    by_cases hq : q = 0
    · subst q
      simp [DivisionLaws]
    · rw [sturmSeq_cons hq] at ih ⊢
      by_cases hr : -p % q = 0
      · rw [hr, sturmSeq_zero_left]
        simp only [DivisionLaws]
        simpa only [neg_mod, neg_eq_zero] using hr
      · rw [sturmSeq_cons hr]
        refine ⟨by rw [neg_mod], ?_, ?_⟩
        · rw [neg_mod, sub_neg_eq_add, mul_comm (p / q), EuclideanDomain.div_add_mod]
        · rwa [sturmSeq_cons hr] at ih

/-- Strict decrease of adjacent degrees, once the first pair decreases. -/
theorem decreasing_degrees (p q : Polynomial K)
    (hdeg : q ≠ 0 → q.degree < p.degree) :
    (sturmSeq p q).IsChain (fun a b => b.degree < a.degree) := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    rw [sturmSeq_cons hp]
    by_cases hq : q = 0
    · subst q
      simp
    · have htail := ih (fun _ => degree_mod_lt (-p) hq)
      rw [sturmSeq_cons hq, List.isChain_cons_cons]
      exact ⟨hdeg hq, by rwa [← sturmSeq_cons hq]⟩

/-- Each adjacent pair remains coprime. -/
theorem coprime_neighbors (p q : Polynomial K) (h : IsCoprime p q) :
    (sturmSeq p q).IsChain IsCoprime := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    rw [sturmSeq_cons hp]
    by_cases hq : q = 0
    · subst q
      simp
    · rw [sturmSeq_cons hq, List.isChain_cons_cons]
      refine ⟨h, ?_⟩
      have htail := ih (by simpa only [neg_mod] using coprime_signed_remainder h)
      rwa [← sturmSeq_cons hq]

/-- The final nonzero member is a unit, hence a nonzero constant. -/
theorem last_constant (p q : Polynomial K) (hp : p ≠ 0) (h : IsCoprime p q) :
    ∃ c : K, c ≠ 0 ∧ (sturmSeq p q).getLast? = some (C c) := by
  induction p, q using sturmSeq.induct
  next q => exact (hp rfl).elim
  next p q hp0 ih =>
    rw [sturmSeq_cons hp0]
    by_cases hq : q = 0
    · subst q
      have hu : IsUnit p := h.isUnit_of_dvd (dvd_zero p)
      have hc : p = C (p.coeff 0) :=
        eq_C_of_degree_le_zero (degree_eq_zero_of_isUnit hu).le
      refine ⟨p.coeff 0, ?_, ?_⟩
      · intro hz
        apply hp0
        rw [hc, hz, map_zero]
      · simpa only [sturmSeq_zero_left, List.getLast?_singleton] using congrArg some hc
    · obtain ⟨c, hc, hlast⟩ := ih hq
        (by simpa only [neg_mod] using coprime_signed_remainder h)
      refine ⟨c, hc, ?_⟩
      rw [sturmSeq_cons hq, List.getLast?_cons_cons]
      rwa [← sturmSeq_cons hq]

/-- A Bézout identity rules out a common root over the coefficient field. -/
theorem no_common_root_of_coprime {p q : Polynomial K} (h : IsCoprime p q)
    (a : K) : ¬ (p.eval a = 0 ∧ q.eval a = 0) := by
  rintro ⟨hp, hq⟩
  obtain ⟨u, v, huv⟩ := h
  have heval := congrArg (fun r : Polynomial K => r.eval a) huv
  simp only [eval_add, eval_mul, hp, hq, mul_zero, add_zero, eval_one] at heval
  exact zero_ne_one heval

theorem signed_division_identities : SignedDivisionIdentities := by
  intro p q
  exact division_laws p q

theorem gcd_invariant : GcdInvariant := by
  intro p q
  exact gcd_signed_remainder p q

theorem chain_of_coprime_derivative : ChainOfCoprimeDerivative := by
  intro s hs hgcd
  have hs0 : s ≠ 0 := ne_zero_of_natDegree_gt hs
  have hds : s.derivative ≠ 0 := derivative_ne_zero.mpr hs.ne'
  have hcop : IsCoprime s s.derivative :=
    (gcd_isUnit_iff _ _).mp (hgcd.symm ▸ isUnit_one)
  refine ⟨?_, fun p hp => ne_zero_of_mem_sturmSeq hp,
    division_laws s s.derivative,
    decreasing_degrees s s.derivative (fun _ => degree_derivative_lt hs0),
    coprime_neighbors s s.derivative hcop, last_constant s s.derivative hs0 hcop, ?_⟩
  · exact ⟨sturmSeq (-s % s.derivative) (-s.derivative % (-s % s.derivative)), by
      rw [sturmSeq_cons hs0, sturmSeq_cons hds]⟩
  · exact (coprime_neighbors s s.derivative hcop).imp
      (fun _ _ h a => no_common_root_of_coprime h a)

/-- Full source conclusion, retaining the arbitrary chosen monic gcd. -/
theorem sturm_chain_for_monic_gcd : SturmChainForMonicGcd := by
  intro f hf d hd hdf hdf' hgreatest
  obtain ⟨hmul, hpos, hroots, hsq, _, hgcd, hmult⟩ :=
    SturmChainSquarefreeReduction.reduction_for_monic_gcd f hf d hd hdf hdf' hgreatest
  exact ⟨hmul, hpos, hroots, hsq, hgcd, hmult,
    chain_of_coprime_derivative (f / d) hpos hgcd⟩

end D07.Ch19.SturmChain
