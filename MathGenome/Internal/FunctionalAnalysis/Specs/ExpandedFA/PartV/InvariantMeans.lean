import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! Independent statements for paper.tex 23247–23280. The group is discrete,
so bounded continuous functions here are exactly all bounded scalar functions.
Positivity in the complex case means preservation of real nonnegative functions.
The set probabilities are finitely additive; no σ-additivity is required. -/
namespace ExpandedFA.PartV.InvariantMeans

universe u v

abbrev BoundedFunction (G : Type u) (𝕜 : Type v) [PseudoMetricSpace 𝕜] :=
  @BoundedContinuousFunction G 𝕜 ⊥ _

noncomputable def constant (G : Type u) {𝕜 : Type v} [PseudoMetricSpace 𝕜]
    (c : 𝕜) : BoundedFunction G 𝕜 :=
  @BoundedContinuousFunction.const G 𝕜 ⊥ _ c

noncomputable def translate {G : Type u} [Group G] {𝕜 : Type v} [RCLike 𝕜]
    (g : G) (f : BoundedFunction G 𝕜) : BoundedFunction G 𝕜 := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  exact f.compContinuous ⟨fun x => g * x, continuous_of_discreteTopology⟩

def NonnegScalar {𝕜 : Type v} [RCLike 𝕜] (z : 𝕜) : Prop :=
  0 ≤ RCLike.re z ∧ RCLike.im z = 0

def IsInvariantMean {G : Type u} [Group G] {𝕜 : Type v} [RCLike 𝕜]
    (L : BoundedFunction G 𝕜 →L[𝕜] 𝕜) : Prop :=
  (∀ f, (∀ x, NonnegScalar (f x)) → NonnegScalar (L f)) ∧
  L (constant G (1 : 𝕜)) = 1 ∧
  (∀ g f, L (translate g f) = L f) ∧ ‖L‖ = 1

/-- A left-invariant finitely additive probability on *all* subsets. -/
def IsInvariantProbability {G : Type u} [Group G] (m : Set G → ℝ) : Prop :=
  (∀ A, 0 ≤ m A) ∧ m ∅ = 0 ∧ m Set.univ = 1 ∧
  (∀ A B, Disjoint A B → m (A ∪ B) = m A + m B) ∧
  (∀ g A, m ((fun x => g * x) '' A) = m A)

noncomputable def indicator (G : Type u) (𝕜 : Type v) [RCLike 𝕜]
    (A : Set G) : BoundedFunction G 𝕜 := by
  classical
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  exact BoundedContinuousFunction.mkOfDiscrete (fun x => if x ∈ A then 1 else 0) 2
    (fun x y => by split_ifs <;> simp)

namespace Spec

def AbelianMean : Prop :=
  ∀ (G : Type u) [CommGroup G] (𝕜 : Type v) [RCLike 𝕜],
    ∃ L : BoundedFunction G 𝕜 →L[𝕜] 𝕜, IsInvariantMean L

def ProbabilityFromMean : Prop :=
  ∀ (G : Type u) [Group G] (𝕜 : Type v) [RCLike 𝕜]
    (L : BoundedFunction G 𝕜 →L[𝕜] 𝕜), IsInvariantMean L →
    ∃ m : Set G → ℝ, IsInvariantProbability m ∧
      ∀ A, L (indicator G 𝕜 A) = RCLike.ofReal (m A)

def AbelianProbability : Prop :=
  ∀ (G : Type u) [CommGroup G], ∃ m : Set G → ℝ, IsInvariantProbability m

def FreeGroupNoProbability : Prop :=
  ¬ ∃ m : Set (FreeGroup Bool) → ℝ, IsInvariantProbability m

def FreeGroupNoMean : Prop :=
  ∀ (𝕜 : Type v) [RCLike 𝕜],
    ¬ ∃ L : BoundedFunction (FreeGroup Bool) 𝕜 →L[𝕜] 𝕜, IsInvariantMean L

end Spec
end ExpandedFA.PartV.InvariantMeans
