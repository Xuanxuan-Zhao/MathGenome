import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.SemidefiniteNonattainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.NonclosedPSDImage
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.RelativeInteriorSegments

noncomputable section
namespace VariationalNotes.Ch05.SemidefiniteNonattainment
open Specs
open VariationalNotes.ConvexGeometry.Specs.PSDImage (symmetricMatrix psdCone quadraticForm)
open VariationalNotes.ConvexGeometry.PSDImage (symmetricMatrix_representation
  symmetricMatrix_isSymm psd_first_entry_nonneg psd_zero_first_entry positive_psd_lift)

theorem feasible_iff : Specs.feasible_iff := by
  intro M
  constructor
  · intro h
    refine ⟨M 0 0, M 1 1, ?_, ?_⟩
    · have heq : M = symmetricMatrix (M 0 0) (M 0 1) (M 1 1) :=
        symmetricMatrix_representation M h.1.1
      simpa only [h.2] using heq
    · have heq := symmetricMatrix_representation M h.1.1
      rw [h.2] at heq
      exact heq ▸ h.1
  · rintro ⟨a, c, rfl, h⟩
    exact ⟨h, rfl⟩

theorem strict_feasibility : Specs.strict_feasibility := by
  have hq (u v : ℝ) :
      ConvexGeometry.Specs.PSDImage.quadraticForm (symmetricMatrix 2 1 2) u v =
        u ^ 2 + v ^ 2 + (u + v) ^ 2 := by
    change 2 * u ^ 2 + (1 + 1) * u * v + 2 * v ^ 2 = _
    ring
  constructor
  · exact ⟨⟨symmetricMatrix_isSymm _ _ _, fun u v => by rw [hq]; positivity⟩, rfl⟩
  · intro u v huv
    rw [hq]
    have h : 0 < u ^ 2 + v ^ 2 := by
      by_contra hn
      have hu : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
      have hv : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
      exact huv (by simp [hu, hv])
    nlinarith [sq_nonneg (u + v)]

/-- A direct relative-interior certificate in the full PSD cone, whose ambient
matrix space also contains nonsymmetric matrices. -/
theorem relative_strict_feasibility : Specs.relative_strict_feasibility := by
  refine ⟨?_, rfl⟩
  apply (ConvexGeometry.mem_relativeInterior_iff_extendible psdCone
    ConvexGeometry.PSDImage.psdCone_convex (symmetricMatrix 2 1 2)
    strict_feasibility.1.1).mpr
  intro M hM
  have hdiag : 0 ≤ M 1 1 := by
    simpa [ConvexGeometry.Specs.PSDImage.quadraticForm] using hM.2 0 1
  have ht : 0 < M 0 0 + M 1 1 + 1 := by
    linarith [psd_first_entry_nonneg M hM]
  let s : ℝ := 1 / (M 0 0 + M 1 1 + 1)
  have hs : 0 < s := one_div_pos.mpr ht
  have heq : s * (M 0 0 + M 1 1 + 1) = 1 :=
    one_div_mul_cancel (ne_of_gt ht)
  refine ⟨s, hs, ?_, ?_⟩
  · exact (symmetricMatrix_isSymm 2 1 2).add
      (((symmetricMatrix_isSymm 2 1 2).sub hM.1).smul s)
  · intro u v
    have hq := hM.2 (-v) u
    have hidentity :
        quadraticForm (symmetricMatrix 2 1 2 + s • (symmetricMatrix 2 1 2 - M)) u v =
        2 * s * (u ^ 2 + v ^ 2) + (1 + s) * (u + v) ^ 2 +
          s * quadraticForm M (-v) u := by
      dsimp [quadraticForm, ConvexGeometry.Specs.PSDImage.quadraticForm,
        symmetricMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
      change (2 + s * (2 - M 0 0)) * u ^ 2 +
        ((1 + s * (1 - M 0 1)) + (1 + s * (1 - M 1 0))) * u * v +
        (2 + s * (2 - M 1 1)) * v ^ 2 = _
      nlinarith [sq_nonneg u, sq_nonneg v]
    change 0 ≤ quadraticForm _ u v
    rw [hidentity]
    positivity

theorem feasible_first_pos : Specs.feasible_first_pos := by
  intro M h
  have hn := psd_first_entry_nonneg M h.1
  have hne : M 0 0 ≠ 0 := by
    intro heq
    have hz := psd_zero_first_entry M h.1 heq
    linarith [h.2]
  exact lt_of_le_of_ne hn (Ne.symm hne)

theorem feasible_lifts : Specs.feasible_lifts := by
  intro a ha
  refine ⟨?_, rfl⟩
  have h : symmetricMatrix a 1 (1 ^ 2 / a) ∈ psdCone := positive_psd_lift a 1 ha
  simpa only [one_pow] using h

theorem primal_value_zero : Specs.primal_value_zero := by
  apply le_antisymm
  · apply (EReal.le_of_forall_lt_iff_le).mp
    intro a ha
    have ha' : 0 < a := by exact_mod_cast ha
    exact iInf_le_of_le (symmetricMatrix a 1 (1 / a))
      (iInf_le_of_le (feasible_lifts a ha') le_rfl)
  · apply le_iInf
    intro M
    apply le_iInf
    intro hM
    exact_mod_cast (feasible_first_pos M hM).le

theorem primal_unattained : Specs.primal_unattained := by
  rintro ⟨M, hM, heq⟩
  rw [primal_value_zero] at heq
  have hz : M 0 0 = 0 := by exact_mod_cast heq
  linarith [feasible_first_pos M hM]

private theorem trace_formula (S M : Matrix2) :
    tracePair S M = S 0 0 * M 0 0 + S 0 1 * M 1 0 +
      (S 1 0 * M 0 1 + S 1 1 * M 1 1) := by
  simp [tracePair, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

theorem trace_adjoint_identity : Specs.trace_adjoint_identity := by
  intro y M hM
  rw [trace_formula]
  have hsym := hM.apply 0 1
  change 0 * M 0 0 + (y / 2) * M 1 0 + ((y / 2) * M 0 1 + 0 * M 1 1) = _
  change M 1 0 = M 0 1 at hsym
  change _ = y * M 0 1
  rw [hsym]
  ring

theorem cost_identity : Specs.cost_identity := by
  intro M
  rw [trace_formula]
  change 1 * M 0 0 + 0 * M 1 0 + (0 * M 0 1 + 0 * M 1 1) = _
  ring

private theorem slack_formula (y : ℝ) : slack y = symmetricMatrix 1 (-y / 2) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slack, cost, traceAdjoint, symmetricMatrix, ConvexGeometry.Specs.PSDImage.symmetricMatrix] <;> ring

private theorem slack_pair (y : ℝ) (M : Matrix2) (hM : M.IsSymm) :
    tracePair (slack y) M = M 0 0 - y * M 0 1 := by
  rw [slack_formula, trace_formula]
  have hsym : M 1 0 = M 0 1 := hM.apply 0 1
  change 1 * M 0 0 + (-y / 2) * M 1 0 + ((-y / 2) * M 0 1 + 0 * M 1 1) = _
  rw [hsym]
  ring

theorem lagrangian_identity : Specs.lagrangian_identity := by
  intro y M hM
  rw [slack_pair y M hM]
  change M 0 0 + y * (1 - M 0 1) = _
  ring

private theorem slack_psd_iff (y : ℝ) :
    symmetricMatrix 1 (-y / 2) 0 ∈ psdCone ↔ y = 0 := by
  constructor
  · intro h
    have hq := h.2 y 2
    change 0 ≤ 1 * y ^ 2 + (-y / 2 + -y / 2) * y * 2 + 0 * 2 ^ 2 at hq
    nlinarith [sq_nonneg y]
  · rintro rfl
    refine ⟨symmetricMatrix_isSymm _ _ _, ?_⟩
    intro u v
    change 0 ≤ 1 * u ^ 2 + (-0 / 2 + -0 / 2) * u * v + 0 * v ^ 2
    nlinarith [sq_nonneg u]

theorem dual_feasible_iff : Specs.dual_feasible_iff := by
  intro y
  constructor
  · intro hy
    let M := symmetricMatrix (y ^ 2) (2 * y) 4
    have hM : M ∈ psdCone := by
      refine ⟨symmetricMatrix_isSymm _ _ _, ?_⟩
      intro u v
      change 0 ≤ y ^ 2 * u ^ 2 + (2 * y + 2 * y) * u * v + 4 * v ^ 2
      nlinarith [sq_nonneg (y * u + 2 * v)]
    have ht := hy.2 M hM
    rw [slack_pair y M hM.1] at ht
    change 0 ≤ y ^ 2 - y * (2 * y) at ht
    nlinarith [sq_nonneg y]
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [slack_formula]
      exact symmetricMatrix_isSymm _ _ _
    · intro M hM
      rw [slack_pair 0 M hM.1]
      simpa using psd_first_entry_nonneg M hM

theorem dual_derivation : Specs.dual_derivation := by
  intro y
  exact ⟨slack_formula y, (dual_feasible_iff y).trans (slack_psd_iff y).symm⟩

theorem dual_zero_feasible : Specs.dual_zero_feasible := (dual_feasible_iff 0).mpr rfl

theorem dual_value_zero : Specs.dual_value_zero := by
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    rw [(dual_feasible_iff y).mp hy]
    rfl
  · exact le_iSup_of_le 0 (le_iSup_of_le dual_zero_feasible le_rfl)

theorem dual_attained : Specs.dual_attained := by
  refine ⟨dual_zero_feasible, ?_, ?_⟩
  · intro y hy
    rw [(dual_feasible_iff y).mp hy]
  · exact dual_value_zero.symm

theorem values_equal : Specs.values_equal := primal_value_zero.trans dual_value_zero.symm

end VariationalNotes.Ch05.SemidefiniteNonattainment
