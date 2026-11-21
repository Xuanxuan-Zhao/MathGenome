import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.FiniteOrderOmittedValue
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.HadamardFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.ElementaryOrderOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.AlgebraicClosure
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential

/-! Finite-order omitted values, paper.tex:3092–3106. We apply Hadamard to
f-a; its intrinsic divisor is empty and its center multiplicity is zero.
The remaining polynomial cannot be constant. Root existence for Q-C(log(b-a))
then excludes any second omitted value, without a Picard theorem. -/
noncomputable section
open Set Polynomial

namespace D12Complex.FiniteOrderOmittedValue
open OrderDivisorDefinitions CanonicalLowerCircles

/-- Hadamard specializes to a polynomial exponential for a zero-free function. -/
lemma zero_free_polynomial_exp (g : NonzeroEntireFunction)
    (hfin : order g ≠ ⊤) (hne : ∀ z, g.toFun z ≠ 0) :
    ∃ Q : Polynomial ℂ, ∀ z, g.toFun z = Complex.exp (Q.eval z) := by
  haveI : IsEmpty (RepeatedZero g) := ⟨fun i => hne i.1.val i.1.property.2⟩
  have hm : analyticOrderAt g.toFun 0 = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (hne 0))
  obtain ⟨Q, _, _, _, _, he⟩ := HadamardFactorization.hadamard_factorization.1 g hfin
  refine ⟨Q, fun z => ?_⟩
  simpa [hm, canonicalProduct] using he z

/-- The algebraic root theorem makes a nonconstant complex polynomial onto. -/
lemma polynomial_surjective (Q : Polynomial ℂ) (hQ : 0 < Q.natDegree) :
    Function.Surjective Q.eval := by
  intro w
  have hnc : ¬ ∃ c : ℂ, Q - C w = C c := by
    rintro ⟨c, hc⟩
    have he : Q = C (c + w) := by
      rw [map_add]
      exact sub_eq_iff_eq_add.mp hc
    have hd := congrArg Polynomial.natDegree he
    simp only [natDegree_C] at hd
    omega
  obtain ⟨z, hz⟩ := AlgebraicClosure.polynomial_exists_root (Q - C w) hnc
  exact ⟨z, sub_eq_zero.mp (by simpa using hz)⟩

theorem finite_order_omitted_value :
    Specs.D12Complex.Ch17.FiniteOrderOmittedValue.finite_order_omitted_value_type := by
  intro f hnc hfin a ha
  obtain ⟨g, hg, horder⟩ := ElementaryOrderOperations.translated_order f a hnc
  have hgne : ∀ z, g.toFun z ≠ 0 := by
    intro z
    simpa [hg, sub_ne_zero] using ha z
  obtain ⟨Q, hQ⟩ := zero_free_polynomial_exp g (by
    change Specs.D12Complex.Ch17.OrderDivisorDefinitions.order_value g ≠ ⊤
    rw [horder]
    exact hfin) hgne
  have he (z : ℂ) : f.toFun z = a + Complex.exp (Q.eval z) := by
    have h := hQ z
    rw [hg] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hpos : 0 < Q.natDegree := by
    by_contra h
    have hc : Q = C (Q.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h)
    apply hnc
    refine ⟨a + Complex.exp (Q.coeff 0), fun z => ?_⟩
    have hz := he z
    rw [hc, eval_C] at hz
    exact hz
  refine ⟨Q, hpos, he, fun b hb => ?_⟩
  obtain ⟨z, hz⟩ := polynomial_surjective Q hpos (Complex.log (b - a))
  change Q.eval z = Complex.log (b - a) at hz
  refine ⟨z, ?_⟩
  rw [he, hz, Complex.exp_log (sub_ne_zero.mpr hb)]
  ring

end D12Complex.FiniteOrderOmittedValue
