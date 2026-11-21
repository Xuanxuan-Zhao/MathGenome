import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.OrthogonalProjection

/-!
Projection onto a closed Hilbert subspace (paper.tex:5679–5691).

We use Mathlib's projection construction, whose minimizer existence proof is
the Cauchy-sequence/parallelogram argument in `Projection.Minimal`. Closedness
in the complete ambient space supplies completeness of the subspace. The
first-slot convention is obtained by reversing Mathlib's inner arguments;
its orthogonal complement is therefore exactly the paper's complement.
-/

namespace D11.Ch20.OrthogonalProjection

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Reversing the arguments gives the paper's first-slot linearity. -/
theorem innerFirst_add_smul (a : 𝕜) (x y z : H) :
    innerFirst (𝕜 := 𝕜) (x + a • y) z =
      innerFirst (𝕜 := 𝕜) x z + a * innerFirst (𝕜 := 𝕜) y z := by
  simp only [innerFirst, inner_add_right, inner_smul_right]

/-- The full orthogonal projection theorem, including uniqueness of the
minimizer and of the orthogonal decomposition and all degenerate cases. -/
theorem orthogonal_projection : statement.{u, v} := by
  intro 𝕜 _ H _ _ _ V hV
  let : CompleteSpace V := hV.completeSpace_coe
  refine ⟨V.starProjection, ?_⟩
  have hmem (x : H) : V.starProjection x ∈ V := V.starProjection_apply_mem x
  have hfix (x : H) (hx : x ∈ V) : V.starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have horth (x : H) : x - V.starProjection x ∈ Vᗮ :=
    V.sub_starProjection_mem_orthogonal x
  refine {
    mem := hmem
    minimizing := ?_
    unique_minimizer := ?_
    orthogonal_iff := ?_
    residual := horth
    additive := V.starProjection.map_add
    scalar_linear := V.starProjection.map_smul
    fixes_subspace := hfix
    idempotent := fun x => hfix _ (hmem x)
    contractive := V.norm_starProjection_apply_le
    decomposition := ?_
    canonical_decomposition := fun x => (add_sub_cancel _ _).symm
    zero := V.starProjection.map_zero
    bot := ?_
    top := ?_
  }
  · intro x w hw
    rw [Submodule.starProjection_minimal]
    exact ciInf_le (f := fun v : V => ‖x - (v : H)‖)
      ⟨0, by rintro r ⟨v, rfl⟩; exact norm_nonneg _⟩ ⟨w, hw⟩
  · intro x w hw hmin
    have heq : ‖x - w‖ = ⨅ v : V, ‖x - v‖ := by
      apply le_antisymm
      · exact le_ciInf fun v => hmin v v.property
      · exact ciInf_le (f := fun v : V => ‖x - (v : H)‖)
          ⟨0, by rintro r ⟨v, rfl⟩; exact norm_nonneg _⟩ ⟨w, hw⟩
    exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hw
      ((V.norm_eq_iInf_iff_inner_eq_zero hw).mp heq)).symm
  · intro z
    exact V.mem_orthogonal z
  · intro x
    refine ⟨(⟨V.starProjection x, hmem x⟩, ⟨x - V.starProjection x, horth x⟩),
      (add_sub_cancel _ _).symm, ?_⟩
    intro yz hyz
    have hp : V.starProjection x = (yz.1 : H) :=
      Submodule.eq_starProjection_of_mem_orthogonal' yz.1.property yz.2.property hyz
    apply Prod.ext
    · exact Subtype.ext hp.symm
    · apply Subtype.ext
      change (yz.2 : H) = x - V.starProjection x
      rw [hp, hyz]
      exact (add_sub_cancel_left _ _).symm
  · intro hbot x
    have := hmem x
    simpa only [hbot, Submodule.mem_bot] using this
  · intro htop x
    exact hfix x (htop.symm ▸ Submodule.mem_top)

end D11.Ch20.OrthogonalProjection
