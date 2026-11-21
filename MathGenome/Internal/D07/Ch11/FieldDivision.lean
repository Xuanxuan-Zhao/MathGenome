import MathGenome.Internal.Specs.D07.Ch11.FieldDivision
import MathGenome.Internal.D07.Ch11.MonicDivision

/-!
Division over a field, K07.11.field_division.

A nonzero divisor has unit leading coefficient, so the upstream unit-leading-
coefficient theorem gives existence and uniqueness. The explicit cancellation
step is monic cancellation after normalizing the divisor by its leading
coefficient. Well-founded induction on degree then supplies a finite long-
division run, with reconstruction proved at every step. No result here applies
to division by the zero polynomial.
-/

universe u

namespace D07.Ch11.FieldDivision

open Polynomial
open Specs.D07.Ch11.FieldDivision

theorem uniqueFieldDivision : UniqueFieldDivision.{u} := by
  intro F _ f g hg
  have hlc : IsUnit g.leadingCoeff :=
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg)
  obtain ⟨qr, ⟨heq, hdeg⟩, huniq⟩ :=
    MonicDivision.unitLeadingCoefficientDivision F f g hlc
  have bound : ∀ r : Polynomial F,
      (r = 0 ∨ r.degree < g.degree) → r.degree < g.degree := by
    intro r hr
    rcases hr with rfl | hr
    · simpa only [Polynomial.degree_zero] using
        (bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr hg))
    · exact hr
  exact ⟨qr, ⟨heq, Or.inr hdeg⟩,
    fun qr' h => huniq qr' ⟨h.1, bound qr'.2 h.2⟩⟩

theorem leadingTermCancellation : LeadingTermCancellation.{u} := by
  intro F _ p g hg hp hdeg
  let h : Polynomial F := C g.leadingCoeff⁻¹ * g
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
  have hh : h.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    (inv_mul_cancel₀ hlc)
  have hd : h.degree = g.degree :=
    Polynomial.degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc)) g
  have hn : h.natDegree = g.natDegree := by
    unfold Polynomial.natDegree
    rw [hd]
  have hdrop := Polynomial.div_wf_lemma (q := h) ⟨by rwa [hd], hp⟩ hh
  have hterm :
      h * (C p.leadingCoeff * X ^ (p.natDegree - h.natDegree)) =
        cancellationTerm p g * g := by
    simp only [h, hn, cancellationTerm, div_eq_mul_inv, map_mul]
    ac_rfl
  rwa [hterm] at hdrop

theorem terminatingDivisionAlgorithm : TerminatingDivisionAlgorithm.{u} := by
  intro F _ f g hg
  induction f using Polynomial.degree_lt_wf.induction with
  | h p ih =>
    by_cases hstop : p = 0 ∨ p.degree < g.degree
    · exact ⟨0, 0, p, DivisionSteps.stop hstop, by simp, hstop⟩
    · have hp : p ≠ 0 := fun hz => hstop (Or.inl hz)
      have hdeg : g.degree ≤ p.degree := le_of_not_gt (fun h => hstop (Or.inr h))
      have hdrop := leadingTermCancellation F p g hg hp hdeg
      obtain ⟨n, q, r, hrun, heq, hr⟩ := ih (p - cancellationTerm p g * g) hdrop
      refine ⟨n + 1, cancellationTerm p g + q, r,
        DivisionSteps.cancel hp hdeg hrun, ?_, hr⟩
      calc
        p = (p - cancellationTerm p g * g) + cancellationTerm p g * g :=
          (sub_add_cancel _ _).symm
        _ = (q * g + r) + cancellationTerm p g * g := by rw [heq]
        _ = (cancellationTerm p g + q) * g + r := by
          rw [add_mul]
          ac_rfl

theorem nonzeroConstantDivision : NonzeroConstantDivision.{u} := by
  intro F _ f a ha q r heq hr
  have hr0 : r = 0 := by
    rcases hr with hr | hr
    · exact hr
    · rw [Polynomial.degree_C ha] at hr
      exact Polynomial.degree_eq_bot.mp ((WithBot.lt_zero_iff_eq_bot r.degree).mp hr)
  refine ⟨hr0, ?_⟩
  have hf : f = q * C a := by simpa only [hr0, add_zero] using heq
  rw [hf, mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, mul_one]

end D07.Ch11.FieldDivision
