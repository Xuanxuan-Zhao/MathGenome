import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.LocallyConvex.WeakDual

/-! The initial weak topology of a bilinear pairing, its finite-test
neighborhoods, and compatibility with the existing canonical weak topology.
All results hold without imposing any norm or completeness on the paired spaces.
-/

namespace ExpandedFA.P1

universe u v w
open scoped Topology
noncomputable section

/-- The identity equivalence into the native weak space for `B y x`. -/
def dualPairEquiv : C12DualPairSpec.DualPairEquivType :=
  fun 𝕜 X _ _ _ _ _ _ _ => LinearEquiv.refl 𝕜 X

/-- Transport the native `WeakBilin B.flip` topology to X. -/
def dualPairTopology : C12DualPairSpec.DualPairTopologyType :=
  fun 𝕜 X Y _ _ _ _ _ B => TopologicalSpace.induced
    (dualPairEquiv 𝕜 X Y B) (WeakBilin.instTopologicalSpace B.flip)

/-- A common positive radius and finitely many scalar tests at a center. -/
def pairNeighborhood : C12DualPairSpec.PairNeighborhoodType :=
  fun _ X _ _ _ _ _ _ B x₀ s ε => {x : X | ∀ y ∈ s, ‖B y (x - x₀)‖ < ε}

theorem dualPairEquiv_apply : C12DualPairSpec.EquivIdentity := by
  intro 𝕜 X Y _ _ _ _ _ B x
  rfl

theorem dualPairTopology_initial : C12DualPairSpec.Initial := by
  intro 𝕜 X Y _ _ _ _ _ B
  change TopologicalSpace.induced id
    (TopologicalSpace.induced (fun (x : X) (y : Y) => B y x) Pi.topologicalSpace) = _
  exact (@induced_id X (TopologicalSpace.induced
    (fun (x : X) (y : Y) => B y x) Pi.topologicalSpace)).trans (induced_to_pi _)

theorem dualPairTopology_coarsest : C12DualPairSpec.Coarsest := by
  intro 𝕜 X Y _ _ _ _ _ B t
  rw [dualPairTopology_initial 𝕜 X Y B, le_iInf_iff]
  simp only [continuous_iff_le_induced]

/-- Translate a finite supremum seminorm ball into the manuscript's tests.
Positivity handles the empty supremum, which is the zero seminorm. -/
private theorem seminorm_ball_eq_tests {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (x₀ : X) (s : Finset Y) {ε : ℝ} (hε : 0 < ε) :
    (s.sup (B.flip.toSeminormFamily : Y → Seminorm 𝕜 (WeakBilin B.flip))).ball x₀ ε =
      pairNeighborhood 𝕜 X Y B x₀ s ε := by
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hε]
  ext x
  simp only [Set.mem_iInter, Seminorm.mem_ball, LinearMap.toSeminormFamily_apply,
    LinearMap.flip_apply, pairNeighborhood, Set.mem_ofPred_eq]

theorem dualPairTopology_nhds_basis : C12DualPairSpec.NeighborhoodBasis := by
  intro 𝕜 X Y _ _ _ _ _ B x₀
  have h := (LinearMap.weakBilin_withSeminorms B.flip).hasBasis_ball (x := x₀)
  change (@nhds (WeakBilin B.flip) (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip)) x₀).HasBasis _ _
  rw [induced_id]
  refine h.congr (fun _ => Iff.rfl) ?_
  intro p hp
  exact seminorm_ball_eq_tests B x₀ p.1 hp

theorem dualPairTopology_isOpen_iff : C12DualPairSpec.OpenCharacterization := by
  intro 𝕜 X Y _ _ _ _ _ B U
  let : TopologicalSpace X := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
  change IsOpen U ↔ _
  rw [isOpen_iff_mem_nhds]
  simp only [(dualPairTopology_nhds_basis 𝕜 X Y B _).mem_iff, Prod.exists]

theorem pairNeighborhood_empty : C12DualPairSpec.EmptyNeighborhood := by
  intro 𝕜 X Y _ _ _ _ _ B x₀ ε
  ext x
  simp [C12DualPairSpec.PairNeighborhoodValue]

/-- Finite-test neighborhoods are open in the initial topology. -/
private theorem pairNeighborhood_open {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
    (B : Y →ₗ[𝕜] X →ₗ[𝕜] 𝕜) (x₀ : X) (s : Finset Y) (ε : ℝ) :
    @IsOpen X (C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B)
      (pairNeighborhood 𝕜 X Y B x₀ s ε) := by
  change @IsOpen (WeakBilin B.flip) (TopologicalSpace.induced id
    (WeakBilin.instTopologicalSpace B.flip)) _
  rw [induced_id]
  have heq : pairNeighborhood 𝕜 X Y B x₀ s ε =
      ⋂ y ∈ s, {x : X | ‖B y x - B y x₀‖ < ε} := by
    ext x
    simp only [pairNeighborhood, Set.mem_ofPred_eq, Set.mem_iInter, map_sub]
  rw [heq]
  change IsOpen (⋂ y ∈ s, {x : WeakBilin B.flip | ‖B.flip x y - B.flip x₀ y‖ < ε})
  exact isOpen_biInter_finset fun y _ =>
    isOpen_lt (((WeakBilin.eval_continuous B.flip y).sub continuous_const).norm)
      continuous_const

theorem dualPairTopology_open_basis : C12DualPairSpec.OpenBasis := by
  intro 𝕜 X Y _ _ _ _ _ B
  let : TopologicalSpace X := C12DualPairSpec.DualPairTopologyValue 𝕜 X Y B
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨x₀, s, ε, _, rfl⟩
    exact pairNeighborhood_open B x₀ s ε
  · intro x U hx hU
    obtain ⟨s, ε, hε, hsub⟩ :=
      (dualPairTopology_isOpen_iff 𝕜 X Y B U).mp hU x hx
    refine ⟨pairNeighborhood 𝕜 X Y B x s ε, ⟨x, s, ε, hε, rfl⟩, ?_, hsub⟩
    simp [pairNeighborhood, hε]

theorem dualPairTopology_evaluation : C12DualPairSpec.EvaluationCompatibility := by
  intro 𝕜 E _ _ _
  exact dualPairTopology_initial 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)

theorem dualPairTopology_weakSpace : C12DualPairSpec.WeakSpaceCompatibility := by
  intro 𝕜 E _ _ _
  rfl

end
end ExpandedFA.P1
