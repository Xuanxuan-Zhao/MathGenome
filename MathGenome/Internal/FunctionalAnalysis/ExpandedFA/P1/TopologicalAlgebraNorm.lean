import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TopologicalAlgebraNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SeparateBilinear
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.IdentityOperatorNorm
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Ring

open Filter

namespace ExpandedFA.P1.TopologicalAlgebraNorm

variable {𝕜 E : Type*} [RCLike 𝕜] [old : NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A Banach space is an F-space for its given topology. -/
lemma banach_fspace : FSpace 𝕜 E := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  unfold TranslationComplete
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- Separate continuity produces a bounded curried multiplication. -/
lemma exists_continuous_multiplication (B : E →ₗ[𝕜] E →ₗ[𝕜] E)
    (hl : ∀ y, Continuous (fun x => B x y)) (hr : ∀ x, Continuous (B x)) :
    ∃ L : E →L[𝕜] E →L[𝕜] E, ∀ x y, L x y = B x y := by
  let A : E →ₗ[𝕜] E →L[𝕜] E :=
    { toFun := fun x => ⟨B x, hr x⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hc : Continuous (fun p : E × E => A p.1 p.2) :=
    separately_continuous_bilinear_continuous (banach_fspace (𝕜 := 𝕜)) B hl hr
  exact ⟨⟨A, ContinuousLinearMap.continuous_of_continuous_uncurry A hc⟩,
    fun _ _ => rfl⟩

/-- Equivalent norm bounds give equality of the induced translation
uniformities and therefore transfer completeness to the new norm. -/
lemma equivalentCompleteNorm_of_bounds (p : Seminorm 𝕜 E)
    (hp : ∀ x, p x = 0 → x = 0)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ x, c * ‖x‖ ≤ p x) (hhi : ∀ x, p x ≤ C * ‖x‖) :
    EquivalentCompleteNorm p := by
  have hball : p.closedBall 0 C ∈ nhds (0 : E) := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) zero_lt_one)
    intro x hx
    rw [Seminorm.mem_closedBall_zero]
    have hx' : ‖x‖ < 1 := by simpa using hx
    exact (hhi x).trans ((mul_le_mul_of_nonneg_left hx'.le hC.le).trans_eq (mul_one C))
  have hu : old.toUniformSpace = (C01Norm.normedGroup p hp).toUniformSpace := by
    apply p.uniformSpace_eq_of_hasBasis NormedAddGroup.nhds_zero_basis_norm_lt ⟨C, hball⟩
    intro r hr
    refine ⟨c * r, mul_pos hc hr, ?_⟩
    intro x hx
    have hx' : p x < c * r := by simpa only [Seminorm.mem_ball_zero] using hx
    exact (mul_lt_mul_iff_right₀ hc).mp ((hlo x).trans_lt hx')
  refine ⟨hp, ⟨c, hc, C, hC, fun x => ⟨hlo x, hhi x⟩⟩, ?_⟩
  rw [← hu]
  infer_instance

/-- Scaling a uniform bilinear bound gives a submultiplicative norm,
including when the underlying space is zero. -/
theorem submultiplicative_renorming : Spec.SubmultiplicativeRenorming := by
  intro 𝕜 E _ _ _ _ B _hassoc hl hr
  obtain ⟨L, hL⟩ := exists_continuous_multiplication B hl hr
  let C : ℝ := max ‖L‖ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let p : Seminorm 𝕜 E := Seminorm.of (fun x => C * ‖x‖)
    (fun x y => by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (norm_add_le x y) hC.le)
    (fun a x => by rw [norm_smul]; ring)
  have hp (x : E) : p x = C * ‖x‖ := rfl
  have hd (x : E) (hx : p x = 0) : x = 0 := by
    rw [hp, mul_eq_zero] at hx
    exact norm_eq_zero.mp (hx.resolve_left (ne_of_gt hC))
  refine ⟨p, equivalentCompleteNorm_of_bounds p hd hC hC
    (fun x => (hp x).ge) (fun x => (hp x).le), ?_⟩
  intro x y
  simp only [hp]
  calc
    C * ‖B x y‖ ≤ C * (C * ‖x‖ * ‖y‖) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [← hL x y]
      exact L.le_of_opNorm₂_le_of_le (le_max_left _ _) le_rfl le_rfl
    _ = C * ‖x‖ * (C * ‖y‖) := by ring

/-- In a nonzero unital algebra, the faithful left regular representation
supplies a complete equivalent norm whose value at the identity is one. -/
theorem normalized_unital_renorming : Spec.NormalizedUnitalRenorming := by
  intro 𝕜 E _ _ _ _ _ B hassoc hl hr e heL heR
  obtain ⟨L, hL⟩ := exists_continuous_multiplication B hl hr
  let p : Seminorm 𝕜 E := (normSeminorm 𝕜 (E →L[𝕜] E)).comp L.toLinearMap
  have hp (x : E) : p x = ‖L x‖ := rfl
  have he : e ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    apply hx
    simpa [he] using (heR x).symm
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hd (x : E) (hx : p x = 0) : x = 0 := by
    have hz : L x = 0 := norm_eq_zero.mp hx
    calc
      x = B x e := (heR x).symm
      _ = L x e := (hL x e).symm
      _ = 0 := by rw [hz]; rfl
  have hlo (x : E) : ‖e‖⁻¹ * ‖x‖ ≤ p x := by
    apply (inv_mul_le_iff₀ hepos).mpr
    rw [hp, mul_comm ‖e‖]
    calc
      ‖x‖ = ‖L x e‖ := by rw [hL, heR]
      _ ≤ ‖L x‖ * ‖e‖ := (L x).le_opNorm e
  have hhi (x : E) : p x ≤ max ‖L‖ 1 * ‖x‖ :=
    (L.le_opNorm x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  refine ⟨p, ⟨equivalentCompleteNorm_of_bounds p hd (inv_pos.mpr hepos)
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hlo hhi, ?_⟩, ?_⟩
  · intro x y
    have hm : L (B x y) = (L x).comp (L y) := by
      ext z
      simp only [ContinuousLinearMap.comp_apply, hL, hassoc]
    simp only [hp, hm]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  · have hid : L e = ContinuousLinearMap.id 𝕜 E := by
      ext x
      simp only [hL, heL, ContinuousLinearMap.id_apply]
    rw [hp, hid]
    exact IdentityOperatorNorm.operator_identity_norm_nontrivial 𝕜 E

/-- The zero-algebra conclusion uses the original norm and does not impose
unit normalization. -/
theorem zero_algebra_renorming : Spec.ZeroAlgebraRenorming := by
  intro 𝕜 E _ _ _ _ _ B e _ _
  have he : e = 0 := Subsingleton.elim _ _
  let p : Seminorm 𝕜 E := normSeminorm 𝕜 E
  have hd (x : E) (hx : p x = 0) : x = 0 := norm_eq_zero.mp hx
  refine ⟨he, p, ⟨equivalentCompleteNorm_of_bounds p hd zero_lt_one zero_lt_one
    (fun x => by simp [p]) (fun x => by simp [p]), ?_⟩, ?_⟩
  · intro x y
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · simp [he]

end ExpandedFA.P1.TopologicalAlgebraNorm
