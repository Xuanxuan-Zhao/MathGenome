import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Norm

/-!
The distance seminorm and canonical projection of Definition
`fa2:p1:c02:quotient-norm`. These constructions use `E ⧸ M`, the algebraic
quotient by `M` itself; neither closedness nor completeness is assumed until
the genuine quotient norm is selected.
-/

noncomputable section

namespace ExpandedFA.P1.C02QuotientNorm

/-- The canonical linear surjection `x ↦ x + M`. -/
def quotientMap : Spec.quotientMapType := fun _ _ _ _ _ M => M.mkQ

/-- The distance seminorm on the original algebraic quotient. -/
def distanceSeminorm : Spec.distanceSeminormType :=
  fun 𝕜 E _ _ _ M => normSeminorm 𝕜 (E ⧸ M)

/-- For closed `M`, the genuine quotient norm has the same norm function. -/
def quotientNormedGroup : Spec.quotientNormedGroupType :=
  fun _ E _ _ _ M hM => by
    letI : IsClosed (M : Set E) := hM
    exact Submodule.Quotient.normedAddCommGroup M

theorem quotientMap_apply : Spec.ProjectionFormula := by
  intro 𝕜 E _ _ _ M x
  rfl

theorem quotientMap_surjective : Spec.ProjectionSurjective := by
  intro 𝕜 E _ _ _ M
  exact M.mkQ_surjective

theorem distanceCandidates_nonempty_bddBelow : Spec.DistanceCandidates := by
  intro 𝕜 E _ _ _ M x
  refine ⟨⟨‖x - 0‖, 0, M.zero_mem, rfl⟩, ⟨0, ?_⟩⟩
  rintro _ ⟨m, _, rfl⟩
  exact norm_nonneg _

theorem distanceSeminorm_mk : Spec.DistanceFormula := by
  intro 𝕜 E _ _ _ M x
  have hd : ‖M.mkQ x‖ = Metric.infDist x (M : Set E) :=
    QuotientAddGroup.norm_mk x
  refine ⟨?_, hd, fun _ => rfl⟩
  change ‖M.mkQ x‖ = _
  rw [hd, Metric.infDist_eq_iInf, sInf_image']
  simp only [dist_eq_norm]

theorem closed_quotient_norm : Spec.ClosedQuotientNorm := by
  intro 𝕜 E _ _ _ M hM
  letI : IsClosed (M : Set E) := hM
  change C01Norm.NormAxioms 𝕜 (norm : E ⧸ M → ℝ) ∧ _
  exact ⟨C01Norm.canonical_norm_axioms 𝕜 (E ⧸ M), fun _ => rfl⟩

end ExpandedFA.P1.C02QuotientNorm
