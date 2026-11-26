import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.CompleteLocalCoefficientRings
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CoefficientField
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingExistence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingMap

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing

/-- Coefficient rings of complete Noetherian local rings. -/
theorem completeLocalCoefficientRings :
    _root_.Specs.CommutativeAlgebraNotes.CoefficientRings.completeLocalCoefficientRings := by
  intro R _ _ _ _
  refine ⟨exists_coefficientField R, ?_⟩
  intro p hp _
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Λ, hΛ, hdomain, hdvr, hchar, hcomplete, hgen, ⟨e⟩⟩ :=
    cohenRingExistence p hp (ResidueField R)
  let e' := (Ideal.quotEquivOfEq hgen.symm).trans e
  obtain ⟨φ, hlocal, hcontinuous, hresidue, hker, hkerPow⟩ :=
    cohenRingMap R Λ p hgen.symm e'
  refine ⟨Λ, hΛ, hdomain, hdvr, hchar, hcomplete, hgen,
    e, φ, hlocal, hcontinuous, ?_, hker, hkerPow⟩
  apply RingHom.ext
  intro x
  change residue R (φ x) = e (Ideal.Quotient.mk (maximalIdeal Λ) x)
  calc
    residue R (φ x) = e' (Ideal.Quotient.mk (Ideal.span {(p : Λ)}) x) :=
      RingHom.congr_fun hresidue x
    _ = e (Ideal.quotEquivOfEq hgen.symm (Ideal.Quotient.mk (Ideal.span {(p : Λ)}) x)) :=
      rfl
    _ = e (Ideal.Quotient.mk (maximalIdeal Λ) x) :=
      congrArg e (Ideal.quotEquivOfEq_mk hgen.symm x)

end CommutativeAlgebraNotes.CoefficientRings
