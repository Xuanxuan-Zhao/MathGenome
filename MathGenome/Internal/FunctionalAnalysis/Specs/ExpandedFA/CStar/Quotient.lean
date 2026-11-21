import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.IdealApproximateIdentities

/-! The quotient stage of `fa2:p2:cstar-quotient`. The algebra is possibly
nonunital and the ideal may be the whole algebra. Every structure below is
on the original submodule quotient, with its distance norm and metric. -/
noncomputable section
namespace ExpandedFA.CStar.Quotient.Spec
universe u

abbrev ClosedTwoSidedIdeal := IdealApproximateIdentities.Spec.ClosedTwoSidedIdeal

/-- A C*-structure with precisely the existing quotient vector space, norm,
metric and induced multiplication and involution. -/
def QuotientCStar : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
    (I : ClosedTwoSidedIdeal A),
    letI := P1.C02QuotientNorm.Spec.quotientNormedGroupValue ℂ A I.toSubmodule I.isClosed
    (∀ a : A, ‖I.toSubmodule.mkQ a‖ =
      sInf ((fun i : A => ‖a - i‖) '' (I : Set A))) ∧
    ∃ C : NonUnitalCStarAlgebra (A ⧸ I.toSubmodule),
      C.toNorm = (inferInstance : Norm (A ⧸ I.toSubmodule)) ∧
      C.toMetricSpace = (inferInstance : MetricSpace (A ⧸ I.toSubmodule)) ∧
      C.toAddCommGroup = (inferInstance : AddCommGroup (A ⧸ I.toSubmodule)) ∧
      C.toSMul = (inferInstance : SMul ℂ (A ⧸ I.toSubmodule)) ∧
      (letI := C
       (∀ a b : A, I.toSubmodule.mkQ (a * b) = I.toSubmodule.mkQ a * I.toSubmodule.mkQ b) ∧
       (∀ a : A, I.toSubmodule.mkQ (star a) = star (I.toSubmodule.mkQ a)) ∧
       (∀ x : A ⧸ I.toSubmodule, ‖star x * x‖ = ‖x‖ ^ 2))

end ExpandedFA.CStar.Quotient.Spec
