import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FiniteKernel

/-! Exact reduction of a finite-rank equation, without independence assumptions. -/

namespace ExpandedFA.PartV.FiniteKernel

open scoped BigOperators

universe u v

variable {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] {m : ℕ}

theorem finiteRankOperator_apply (a : Fin m → X)
    (ℓ : Fin m → X →L[𝕜] 𝕜) (u : X) :
    finiteRankOperator a ℓ u = ∑ j, ℓ j u • a j := by
  simp [finiteRankOperator]

theorem functional_synthesis (a : Fin m → X)
    (ℓ : X →L[𝕜] 𝕜) (c : Fin m → 𝕜) :
    ℓ (∑ j, c j • a j) = ∑ j, ℓ (a j) * c j := by
  simp [map_sum, mul_comm]

theorem coordinates_reconstruct (a : Fin m → X)
    (ℓ : Fin m → X →L[𝕜] 𝕜) (z : 𝕜) (f : X) (c : Fin m → 𝕜)
    (hc : c ∈ matrixSolutions a ℓ z f) :
    coordinates ℓ (reconstruct a z f c) = c := by
  funext i
  change ℓ i (f + z • ∑ j, c j • a j) = c i
  rw [map_add, map_smul, functional_synthesis]
  exact (eq_add_of_sub_eq (hc i)).symm

theorem exact_reduction : Spec.ExactReduction.{u, v} := by
  intro 𝕜 X _ _ _ _ m a ℓ z f u
  constructor
  · intro hu
    change u - z • finiteRankOperator a ℓ u = f at hu
    constructor
    · intro i
      have hi := congrArg (ℓ i) hu
      simpa only [coordinates, map_sub, map_smul, finiteRankOperator_apply,
        functional_synthesis, smul_eq_mul] using hi
    · change u = f + z • ∑ j, ℓ j u • a j
      rw [← finiteRankOperator_apply]
      exact sub_eq_iff_eq_add.mp hu
  · rintro ⟨_, hu⟩
    change u - z • finiteRankOperator a ℓ u = f
    rw [sub_eq_iff_eq_add, finiteRankOperator_apply]
    exact hu

theorem unique_reconstruction : Spec.UniqueReconstruction.{u, v} := by
  intro 𝕜 X _ _ _ _ m a ℓ z f c hc
  have hcoords := coordinates_reconstruct a ℓ z f c hc
  have hsol : reconstruct a z f c ∈ operatorSolutions a ℓ z f := by
    apply (exact_reduction 𝕜 X m a ℓ z f (reconstruct a z f c)).mpr
    rw [hcoords]
    exact ⟨hc, rfl⟩
  refine ⟨⟨hsol, hcoords⟩, reconstruct a z f c, ⟨hsol, hcoords⟩, ?_⟩
  intro u hu
  have h := ((exact_reduction 𝕜 X m a ℓ z f u).mp hu.1).2
  rwa [hu.2] at h

theorem solution_set_equivalence : Spec.SolutionSetEquivalence.{u, v} := by
  intro 𝕜 X _ _ _ _ m a ℓ z f
  let e : {u // u ∈ operatorSolutions a ℓ z f} ≃
      {c // c ∈ matrixSolutions a ℓ z f} :=
    { toFun := fun u =>
        ⟨coordinates ℓ u.val, ((exact_reduction 𝕜 X m a ℓ z f u.val).mp u.property).1⟩
      invFun := fun c =>
        ⟨reconstruct a z f c.val,
          ((unique_reconstruction 𝕜 X m a ℓ z f c.val c.property).1).1⟩
      left_inv := by
        intro u
        apply Subtype.ext
        exact (((exact_reduction 𝕜 X m a ℓ z f u.val).mp u.property).2).symm
      right_inv := by
        intro c
        apply Subtype.ext
        exact coordinates_reconstruct a ℓ z f c.val c.property }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end ExpandedFA.PartV.FiniteKernel
