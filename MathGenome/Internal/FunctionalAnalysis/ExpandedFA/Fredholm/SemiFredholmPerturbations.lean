import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.SemiFredholmPerturbations
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.ReducedMinimumModulus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.HilbertSemiFredholmIndex

noncomputable section
open scoped ENNReal NNReal
universe u v w
namespace ExpandedFA.Fredholm.SemiFredholmPerturbations
open Hilbert.ReducedMinimumModulus

section Helpers
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]

/-- A finite lower bound strictly larger than the perturbation norm exists
also when the reduced minimum modulus is infinite. -/
theorem exists_lower_bound (A B : H →L[𝕜] K)
    (h : (‖B‖₊ : ℝ≥0∞) < reducedMinimumModulus 𝕜 H K A) :
    ∃ c : ℝ, ‖B‖ < c ∧ ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖ := by
  obtain ⟨c, hcB, hcA⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  exact ⟨c, by exact_mod_cast hcB, (le_modulus_iff A c).mp hcA.le⟩

/-- The perturbed operator remains bounded below on the old kernel complement. -/
theorem lower_bound_add (A B : H →L[𝕜] K) {c : ℝ}
    (hb : ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖)
    (x : H) (hx : x ∈ A.ker.orthogonal) :
    (c - ‖B‖) * ‖x‖ ≤ ‖(A + B) x‖ := by
  have h₁ := hb x hx
  have h₂ := B.le_opNorm x
  have h₃ : ‖A x‖ ≤ ‖(A + B) x‖ + ‖B x‖ := by
    simpa only [add_apply, add_sub_cancel_right] using
      norm_sub_le ((A + B) x) (B x)
  nlinarith

variable [CompleteSpace H]

/-- Projection into the old kernel is injective on the new kernel. -/
theorem exists_kernel_embedding (A B : H →L[𝕜] K) {c : ℝ}
    (hc : ‖B‖ < c)
    (hb : ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖) :
    ∃ f : (A + B).ker →ₗ[𝕜] A.ker, Function.Injective f := by
  let : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
  let f := (A.ker.orthogonalProjectionOnto.domRestrict (A + B).ker).toLinearMap
  refine ⟨f, LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_)⟩
  intro x hx
  have hxo : (x : H) ∈ A.ker.orthogonal :=
    (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hx
  have hh := lower_bound_add A B hb x hxo
  have hz : (A + B) (x : H) = 0 := x.property
  rw [hz, norm_zero] at hh
  have hn : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
  exact Subtype.ext (norm_eq_zero.mp hn)

/-- A closed infinite block plus the image of the finite old kernel gives
closedness of the entire perturbed range. -/
theorem isClosed_range_add_of_finite_kernel (A B : H →L[𝕜] K)
    [FiniteDimensional 𝕜 A.ker] {c : ℝ} (hc : ‖B‖ < c)
    (hb : ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖) :
    IsClosed ((A + B).range : Set K) := by
  let : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
  let : CompleteSpace A.ker.orthogonal := A.ker.isClosed_orthogonal.completeSpace_coe
  let f := (A + B).domRestrict A.ker.orthogonal
  have hp : 0 < c - ‖B‖ := sub_pos.mpr hc
  have ha : AntilipschitzWith (⟨(c - ‖B‖)⁻¹, inv_nonneg.mpr hp.le⟩ : ℝ≥0) f := by
    apply f.antilipschitz_of_bound
    intro x
    change ‖(x : H)‖ ≤ (c - ‖B‖)⁻¹ * ‖(A + B) x‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hp).mpr (by
      simpa only [mul_comm] using lower_bound_add A B hb x x.property)
  have hclosed : IsClosed (f.range : Set K) := by
    exact ha.isClosed_range f.uniformContinuous
  have hr : (A + B).range = f.range ⊔ A.ker.map (A + B).toLinearMap := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      obtain ⟨m, hm, n, hn, hmn⟩ := A.ker.exists_add_mem_mem_orthogonal x
      rw [hmn, map_add]
      refine Submodule.mem_sup.mpr ⟨(A + B) n, ?_, (A + B) m, ?_, add_comm _ _⟩
      · exact ⟨⟨n, hn⟩, rfl⟩
      · exact Submodule.mem_map.mpr ⟨m, hm, rfl⟩
    · exact sup_le (by rintro y ⟨x, rfl⟩; exact (A + B).mem_range_self x)
        (LinearMap.map_le_range)
  rw [hr]
  exact Submodule.isClosed_sup_finiteDimensional _ _ hclosed

/-- Quantitative left semi-Fredholm stability. -/
theorem left_add_of_lower_bound (A B : H →L[𝕜] K)
    [FiniteDimensional 𝕜 A.ker] {c : ℝ} (hc : ‖B‖ < c)
    (hb : ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖) :
    IsLeftSemiFredholm (A + B) := by
  obtain ⟨f, hf⟩ := exists_kernel_embedding A B hc hb
  exact ⟨isClosed_range_add_of_finite_kernel A B hc hb,
    FiniteDimensional.of_injective f hf⟩

/-- Algebraic cardinal nullity cannot increase, even for infinite kernels. -/
theorem kernel_rank_le (A B : H →L[𝕜] K) {c : ℝ} (hc : ‖B‖ < c)
    (hb : ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖) :
    Module.rank 𝕜 (A + B).ker ≤ Module.rank 𝕜 A.ker := by
  obtain ⟨f, hf⟩ := exists_kernel_embedding A B hc hb
  exact f.rank_le_of_injective hf

variable [CompleteSpace K]

/-- Semi-Fredholmness supplies the finite block on at least one side. -/
theorem semiFredholm_add_of_lower_bound (A B : H →L[𝕜] K)
    (hA : IsSemiFredholm A) {c : ℝ} (hc : ‖B‖ < c)
    (hb : ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖) :
    IsSemiFredholm (A + B) := by
  rcases hA with hl | hr
  · let := hl.2
    exact Or.inl (left_add_of_lower_bound A B hc hb)
  · have hstar := (hilbert_right_iff_left_adjoint A).mp hr
    let := hstar.2
    have hcstar : ‖B.adjoint‖ < c := by simpa only [LinearIsometryEquiv.norm_map] using hc
    have hcpos : 0 < c := lt_of_le_of_lt (norm_nonneg B) hc
    have h := left_add_of_lower_bound A.adjoint B.adjoint hcstar
      (adjoint_lower_bound A hcpos hb)
    apply Or.inr
    apply (hilbert_right_iff_left_adjoint (A + B)).mpr
    change IsLeftSemiFredholm ((A + B).adjoint)
    rw [show (A + B).adjoint = A.adjoint + B.adjoint from
      ContinuousLinearMap.adjoint.map_add A B]
    exact h

/-- Closed actual cokernels are adjoint kernels, so the same argument gives
cardinal deficiency control. -/
theorem cokernel_rank_le (A B : H →L[𝕜] K)
    (hA : IsClosed (A.range : Set K))
    (hAB : IsClosed ((A + B).range : Set K))
    {c : ℝ} (hc : ‖B‖ < c)
    (hb : ∀ x : H, x ∈ A.ker.orthogonal → c * ‖x‖ ≤ ‖A x‖) :
    Module.rank 𝕜 (K ⧸ (A + B).range) ≤ Module.rank 𝕜 (K ⧸ A.range) := by
  rw [(cokernelEquivAdjointKer (A + B) hAB).rank_eq,
    (cokernelEquivAdjointKer A hA).rank_eq]
  have hcstar : ‖B.adjoint‖ < c := by simpa only [LinearIsometryEquiv.norm_map] using hc
  have hcpos : 0 < c := lt_of_le_of_lt (norm_nonneg B) hc
  rw [show (A + B).adjoint = A.adjoint + B.adjoint from
    ContinuousLinearMap.adjoint.map_add A B]
  exact kernel_rank_le A.adjoint B.adjoint hcstar (adjoint_lower_bound A hcpos hb)

end Helpers
/-- The full quantitative assertion, including both infinite-defect cases. -/
theorem perturbation : Spec.Perturbation.{u,v,w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ A B hA hB
  change IsSemiFredholm A at hA
  change (‖B‖₊ : ℝ≥0∞) < reducedMinimumModulus 𝕜 H K A at hB
  obtain ⟨c, hc, hb⟩ := exists_lower_bound A B hB
  have hAB := semiFredholm_add_of_lower_bound A B hA hc hb
  have hAc : IsClosed (A.range : Set K) := hA.elim And.left And.left
  have hABc : IsClosed ((A + B).range : Set K) := hAB.elim And.left And.left
  refine ⟨hAB, ?_, ?_⟩
  · exact OrderHom.mono (β := ℕ∞) Cardinal.toENat (kernel_rank_le A B hc hb)
  · exact OrderHom.mono (β := ℕ∞) Cardinal.toENat (cokernel_rank_le A B hAc hABc hc hb)

end ExpandedFA.Fredholm.SemiFredholmPerturbations
