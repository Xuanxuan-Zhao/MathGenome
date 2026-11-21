import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch01.CoprimeCRT
import MathGenome.Internal.D07.Ch09.CrtFiniteInteger
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.CompatibleCRT

namespace P203.Ch01
open P203Specs.Ch01
open scoped BigOperators
universe u

/-- Completing the coefficient family at modulus one by zero allows use of
the full finite integer CRT formula. -/
theorem coprimeCRTSum_solution {ι : Type u} [Fintype ι]
    (m : ι → ℤ) (hm : ∀ i, 0 < m i)
    (hc : ∀ i j, i ≠ j → Int.gcd (m i) (m j) = 1)
    (u : ι → ℤ)
    (hu : ∀ i, 1 < m i → m i ∣ ((∏ j, m j) / m i) * u i - 1)
    (a : ι → ℤ) : ∀ i, m i ∣ coprimeCRTSum m a u - a i := by
  classical
  let t : ι → ℤ := fun i => if 1 < m i then u i else 0
  have ht : ∀ i, m i ∣ t i * ((∏ j, m j) / m i) - 1 := by
    intro i
    by_cases hi : 1 < m i
    · simpa [t, hi, mul_comm] using hu i hi
    · have hmi : m i = 1 := by
        have := hm i
        omega
      simp [hmi]
  have heq : coprimeCRTSum m a u =
      ∑ j, a j * t j * ((∏ k, m k) / m j) := by
    unfold coprimeCRTSum
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 1 < m i <;> simp [t, hi, mul_comm, mul_left_comm]
  rw [heq]
  exact D07.Ch09.CrtFiniteInteger.explicitSolution ι m hm hc t ht a

theorem coprimeCRTCofactors : CoprimeCRTCofactors.{u} := by
  intro ι _ m hm hc
  classical
  choose u hu using fun i => (D07.Ch09.CrtFiniteInteger.cofactorData ι m hm hc i).2.2
  exact ⟨u, fun i _ => by simpa [mul_comm] using hu i⟩

theorem coprimeCRTRing : CoprimeCRTRing.{u} := by
  intro ι _ m hm hc
  obtain ⟨e, he⟩ := D07.Ch09.CrtFiniteInteger.integerRingCRT ι m hm hc
  refine ⟨e, he, ?_⟩
  intro u hu a
  apply e.injective
  rw [e.apply_symm_apply]
  funext i
  rw [he]
  symm
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  exact Ideal.mem_span_singleton.mpr (coprimeCRTSum_solution m hm hc u hu a i)

theorem coprimeCRTChoiceIndependent : CoprimeCRTChoiceIndependent.{u} := by
  intro ι _ m hm hc u v a b hu hv hab
  apply (D07.Ch09.CrtFiniteInteger.integerUniqueness ι m hm hc _ _).mp
  intro i
  have h₁ := coprimeCRTSum_solution m hm hc u hu a i
  have h₂ := coprimeCRTSum_solution m hm hc v hv b i
  convert dvd_sub (dvd_add h₁ (hab i)) h₂ using 1
  ring

theorem coprimeCRTLcm : CoprimeCRTLcm.{u} := by
  intro ι _ m hm hc
  have hl := (compatibleCRTLcm.1 Finset.univ m (fun i _ => hm i)).1
  have hp : 0 < ∏ i, m i := Finset.prod_pos (fun i _ => hm i)
  apply Int.dvd_antisymm (le_of_lt hl) (le_of_lt hp)
  · exact Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem m hi)
  · have hd : (∏ i, m i) ∣ finiteCRTLcm Finset.univ m - 0 :=
      (D07.Ch09.CrtFiniteInteger.integerUniqueness ι m hm hc _ 0).mp (fun i => by
        simpa only [sub_zero, finiteCRTLcm] using (Finset.dvd_lcm (f := m) (Finset.mem_univ i)))
    simpa only [sub_zero] using hd

theorem coprimeCRTBoundary : CoprimeCRTBoundary.{u} := by
  have h : Subsingleton (CRTResidue 1) := by
    apply Ideal.Quotient.subsingleton_iff.mpr
    simp
  refine ⟨h, ?_⟩
  intro ι _ _ m a u
  have hp : (∏ i, m i) = 1 := by simp
  refine ⟨hp, ?_, ?_, ?_, inferInstance⟩
  · simp [finiteCRTLcm]
  · simp [coprimeCRTSum]
  · rw [hp]
    exact h

end P203.Ch01
