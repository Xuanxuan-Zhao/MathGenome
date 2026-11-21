import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.CoordinateDependency
import MathGenome.Internal.ExtremalOptimization.P205.Probability.FiniteModels
import MathGenome.Internal.ExtremalOptimization.P205.Probability.DependencyGraph

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace P205.Probability.CoordinateDependency

variable {K I : Type*} {X : K → Type*}

/-- Enlarging a determining block preserves determination. -/
theorem DependsOn.mono {S T : Set K} {A : Set (∀ k, X k)}
    (hA : DependsOn S A) (hST : S ⊆ T) : DependsOn T A := by
  intro x y hxy
  exact hA x y (fun k hk => hxy k (hST hk))

section Measurability
variable [Fintype K] [∀ k, Fintype (X k)]
  [∀ k, MeasurableSpace (X k)] [∀ k, MeasurableSingletonClass (X k)]

/-- A determined event is a measurable preimage under restriction to its block. -/
theorem cylinder_measurable (S : Set K) (A : Set (∀ k, X k))
    (hA : DependsOn S A) :
    MeasurableSet[blockSpace (X := X) S] A ∧ MeasurableSet A := by
  classical
  refine ⟨?_, A.toFinite.measurableSet⟩
  let r : (∀ k, X k) → (∀ k : S, X k) := fun x k => x k
  refine ⟨r '' A, (r '' A).toFinite.measurableSet, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact (hA y x (fun k hk => congrFun heq ⟨k, hk⟩)).mp hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem nonneighbor_sigma_le [Finite I] (S : I → Set K)
    (A : I → Set (∀ k, X k)) (hA : ∀ i, DependsOn (S i) (A i)) (i : I) :
    MeasurableSpace.generateFrom
      (A '' {j | j ≠ i ∧ ¬ (overlapGraph S).Adj i j}) ≤
      blockSpace (X := X) (nonneighborBlock S i) := by
  apply MeasurableSpace.generateFrom_le
  rintro B ⟨j, hj, rfl⟩
  apply (cylinder_measurable _ _ ((hA j).mono ?_)).1
  intro k hk
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hk⟩⟩

end Measurability

theorem blocks_disjoint (S : I → Set K) (i : I) :
    Disjoint (S i) (nonneighborBlock S i) := by
  apply Set.disjoint_left.mpr
  intro k hki hkt
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hkt
  obtain ⟨hj, hkj⟩ := Set.mem_iUnion.mp hj
  exact hj.2 ⟨Ne.symm hj.1, k, hki, hkj⟩

section Probability
variable [Fintype K] [∀ k, Fintype (X k)]
  [∀ k, MeasurableSpace (X k)] [∀ k, MeasurableSingletonClass (X k)]

theorem independent_blocks (M : ∀ k, FiniteModel (X k)) (S T : Set K)
    (hST : Disjoint S T) :
    Indep (blockSpace (X := X) S) (blockSpace (X := X) T) (FiniteModel.pi M).measure := by
  exact (FiniteModel.independent_coordinates M).indepFun_set S T hST
    (fun k => measurable_pi_apply k)

theorem isDependencyGraph [Finite I] (M : ∀ k, FiniteModel (X k))
    (S : I → Set K) (A : I → Set (∀ k, X k))
    (hA : ∀ i, DependsOn (S i) (A i)) :
    IsDependencyGraph (FiniteModel.pi M).measure A (overlapGraph S) := by
  refine ⟨fun i => (cylinder_measurable _ _ (hA i)).2, ?_⟩
  intro i B hB
  have hAi := (cylinder_measurable _ _ (hA i)).1
  have hBT : MeasurableSet[blockSpace (X := X) (nonneighborBlock S i)] B :=
    nonneighbor_sigma_le S A hA i B hB
  exact ((independent_blocks M _ _ (blocks_disjoint S i)).indepSet_of_measurableSet
    hAi hBT).measure_inter_eq_mul

end Probability
end P205.Probability.CoordinateDependency
