import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm

/-! Norm/seminorm and metric-topology bridges for Definition `fa2:p1:c01:norm`. -/

namespace ExpandedFA.P1.C01Norm

/-- Package a function satisfying precisely the manuscript axioms as Mathlib's
standard bundled seminorm. This preserves the function and the given module. -/
def seminormOfAxioms : Spec.seminormOfAxiomsType :=
  fun _ _ _ _ _ p h => Seminorm.of p h.2.2 h.2.1

theorem seminorm_identification : Spec.SeminormIdentification := by
  intro 𝕜 E _ _ _ p
  constructor
  · intro h
    exact ⟨seminormOfAxioms 𝕜 E p h, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨fun x => apply_nonneg q x, map_smul_eq_mul q, map_add_le_add q⟩

theorem norm_identification : Spec.NormIdentification := by
  intro 𝕜 E _ _ _ p
  constructor
  · rintro ⟨hs, hd⟩
    exact ⟨seminormOfAxioms 𝕜 E p hs, rfl, fun x hx => (hd x).mp hx⟩
  · rintro ⟨q, rfl, hd⟩
    refine ⟨(seminorm_identification 𝕜 E q).mpr ⟨q, rfl⟩, ?_⟩
    intro x
    exact ⟨hd x, fun hx => hx ▸ map_zero q⟩

theorem canonical_seminorm_axioms : Spec.CanonicalSeminormAxioms := by
  intro 𝕜 E _ _ _
  exact ⟨norm_nonneg, norm_smul, norm_add_le⟩

theorem canonical_norm_axioms : Spec.CanonicalNormAxioms := by
  intro 𝕜 E _ _ _
  exact ⟨canonical_seminorm_axioms 𝕜 E, fun _ => norm_eq_zero⟩

theorem canonical_geometry : Spec.CanonicalGeometry := by
  intro E _
  refine ⟨fun _ => rfl, dist_eq_norm, ?_, ?_, ?_⟩
  · intro x r
    ext y
    exact mem_ball_iff_norm
  · intro x r
    ext y
    exact mem_closedBall_iff_norm
  · intro s
    simpa only [Metric.ball, dist_eq_norm, Set.subset_def, Set.mem_ofPred_eq]
      using (Metric.isOpen_iff (s := s))

theorem seminorm_realization : Spec.SeminormRealization := by
  intro 𝕜 E _ _ m p
  let := seminormedGroup p
  refine ⟨?_, canonical_geometry E⟩
  exact ⟨{ m with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }, rfl⟩

theorem norm_realization : Spec.NormRealization := by
  intro 𝕜 E _ _ m p h
  let := normedGroup p h
  refine ⟨?_, canonical_geometry E, fun _ _ => dist_eq_zero⟩
  exact ⟨{ m with norm_smul_le := fun a x => (map_smul_eq_mul p a x).le }, rfl⟩

end ExpandedFA.P1.C01Norm
