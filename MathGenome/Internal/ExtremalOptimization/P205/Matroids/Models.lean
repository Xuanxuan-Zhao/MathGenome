import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Finite matroid rank and coordinate interfaces, with no union-matroid assumption. -/
namespace P205.Matroids
open scoped BigOperators
noncomputable section
universe u

/-- Natural rank, identified below with the maximum independent subset size. -/
def rank : Specs.P205.Matroids.rankType.{u} :=
  @Specs.P205.Matroids.rankValue.{u}

/-- The sum of the coordinates whose ground elements belong to a set. -/
def subsetSum : Specs.P205.Matroids.subsetSumType.{u} :=
  @Specs.P205.Matroids.subsetSumValue.{u}

/-- The real indicator on the actual ground set. -/
def indicator : Specs.P205.Matroids.indicatorType.{u} :=
  @Specs.P205.Matroids.indicatorValue.{u}

/-- The real dot product on the actual ground set. -/
def dot : Specs.P205.Matroids.dotType.{u} :=
  @Specs.P205.Matroids.dotValue.{u}

/-- Nonnegative vectors satisfying every ground-subset rank inequality. -/
def rankInequalities : Specs.P205.Matroids.rankInequalitiesType.{u} :=
  @Specs.P205.Matroids.rankInequalitiesValue.{u}

/-- The rank inequalities together with equality on the whole ground. -/
def baseInequalities : Specs.P205.Matroids.baseInequalitiesType.{u} :=
  @Specs.P205.Matroids.baseInequalitiesValue.{u}

/-- The family of indicators of the canonical independent sets. -/
def independentIndicators : Specs.P205.Matroids.independentIndicatorsType.{u} :=
  @Specs.P205.Matroids.independentIndicatorsValue.{u}

/-- The family of indicators of the canonical matroid bases. -/
def basisIndicators : Specs.P205.Matroids.basisIndicatorsType.{u} :=
  @Specs.P205.Matroids.basisIndicatorsValue.{u}

/-- Sets expressible as a union of one independent set from each family member. -/
def Assignable : Specs.P205.Matroids.AssignableType.{u} :=
  @Specs.P205.Matroids.AssignableValue.{u}

/-- All assignable subsets of a set, enumerated in the finite common ground. -/
def assignableSubsets : Specs.P205.Matroids.assignableSubsetsType.{u} :=
  @Specs.P205.Matroids.assignableSubsetsValue.{u}

/-- The finite maximum assignable subset size, independent of any union matroid. -/
def q : Specs.P205.Matroids.qType.{u} :=
  @Specs.P205.Matroids.qValue.{u}

/-- Finite rank has no infinite-rank junk value. -/
theorem rank_natCast {α : Type u} (M : Matroid α) [M.Finite] (S : Set α) :
    (rank M S : ℕ∞) = M.eRk S :=
  ENat.natCast_toNat ((Matroid.eRk_ne_top_iff).2 (Matroid.isRkFinite_set M S))

theorem rank_canonical : Specs.P205.Matroids.RankCanonical := by
  intro α M S
  rfl

theorem basis_rank : Specs.P205.Matroids.BasisRank := by
  intro α M _ I S hS
  constructor
  · intro h
    exact ⟨h.subset, h.indep, congrArg ENat.toNat h.encard_eq_eRk⟩
  · rintro ⟨hIS, hI, hcard⟩
    apply (Matroid.isBasis_iff_indep_encard_eq_of_finite hI.finite hS).2
    refine ⟨hIS, hI, ?_⟩
    exact hI.finite.cast_ncard_eq.symm.trans
      ((congrArg (fun n : ℕ => (n : ℕ∞)) hcard).trans (rank_natCast M S))

theorem base_rank : Specs.P205.Matroids.BaseRank := by
  intro α M _ B
  rw [← Matroid.isBasis_ground_iff, basis_rank M B M.E Set.Subset.rfl]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨h.1.subset_ground, h⟩⟩

theorem independent_rank : Specs.P205.Matroids.IndependentRank := by
  intro α M _ I hI
  constructor
  · intro h
    exact congrArg ENat.toNat h.eRk_eq_encard
  · intro h
    apply Matroid.indep_iff_eRk_eq_encard.mpr
    exact (rank_natCast M I).symm.trans
      ((congrArg (fun n : ℕ => (n : ℕ∞)) h).trans (M.set_finite I hI).cast_ncard_eq)

theorem basis_exists : Specs.P205.Matroids.BasisExists := by
  intro α M _ S hS
  obtain ⟨I, hI⟩ := M.exists_isBasis S hS
  exact ⟨I, hI, hI.indep.finite, (basis_rank M I S hS).1 hI |>.2.2⟩

theorem base_exists : Specs.P205.Matroids.BaseExists := by
  intro α M _
  obtain ⟨B, hB⟩ := M.exists_isBase
  exact ⟨B, hB, hB.finite, (base_rank M B).1 hB |>.2⟩

theorem rank_maximum : Specs.P205.Matroids.RankMaximum := by
  intro α M _ S hS
  obtain ⟨I, hI, _, hcard⟩ := basis_exists M S hS
  refine ⟨⟨I, hI.subset, hI.indep, hcard⟩, ?_⟩
  intro J hJS hJ
  exact ENat.toNat_le_toNat (hJ.encard_le_eRk_of_subset hJS)
    ((Matroid.eRk_ne_top_iff).2 (Matroid.isRkFinite_set M S))

theorem rank_empty : Specs.P205.Matroids.RankEmpty := by
  intro α M
  simp [Specs.P205.Matroids.rankValue]

theorem empty_ground_base : Specs.P205.Matroids.EmptyGroundBase := by
  intro α M hE B
  have hempty : ∀ {B : Set α}, M.IsBase B → B = ∅ := by
    intro B hB
    exact Set.subset_empty_iff.mp (hE ▸ hB.subset_ground)
  constructor
  · exact hempty
  · intro hB
    obtain ⟨D, hD⟩ := M.exists_isBase
    simpa [hempty hD, hB] using hD

theorem indicator_dot : Specs.P205.Matroids.IndicatorDot := by
  intro α M _ w I
  classical
  simp [Specs.P205.Matroids.dotValue, Specs.P205.Matroids.subsetSumValue,
    Specs.P205.Matroids.indicatorValue, mul_ite]

theorem indicator_sum : Specs.P205.Matroids.IndicatorSum := by
  intro α M _ I S
  classical
  let := M.ground_finite.fintype
  change (∑ e : M.E, if (e : α) ∈ S then
    (if (e : α) ∈ I then (1 : ℝ) else 0) else 0) = _
  calc
    _ = ∑ e : M.E, if (e : α) ∈ I ∩ S then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hi : (e : α) ∈ I <;> by_cases hs : (e : α) ∈ S <;> simp [hi, hs]
    _ = (({e : M.E | (e : α) ∈ I ∩ S}).ncard : ℝ) := by
      rw [Finset.sum_boole]
      congr 1
      rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
      congr 1
      ext e
      simp
    _ = ((I ∩ S ∩ M.E).ncard : ℝ) := by rw [Set.ncard_subtype]; rfl

theorem empty_coordinates : Specs.P205.Matroids.EmptyCoordinates := by
  intro α M hE x y
  funext e
  exact False.elim (by simpa [hE] using e.property)

theorem assignable_ground : Specs.P205.Matroids.AssignableGround := by
  intro α k F I
  rintro ⟨parts, hparts, rfl⟩
  exact Set.iUnion_subset fun i => (hparts i).subset_ground.trans (F.ground_eq i).subset

theorem assignable_empty : Specs.P205.Matroids.AssignableEmpty := by
  intro α k F
  refine ⟨fun _ => ∅, fun i => (F.matroid i).empty_indep, ?_⟩
  simp

theorem assignable_zero : Specs.P205.Matroids.AssignableZero := by
  intro α F I
  constructor
  · rintro ⟨parts, _, h⟩
    simpa using h
  · rintro rfl
    exact assignable_empty F

/-- Exact membership criterion for the finite family used to compute `q`. -/
theorem mem_assignableSubsets {α : Type u} {k : ℕ} (F : Family α k)
    (S : Set α) (I : Finset α) :
    I ∈ assignableSubsets F S ↔ (↑I : Set α) ⊆ S ∧ Assignable F (↑I : Set α) := by
  classical
  simp only [assignableSubsets, Specs.P205.Matroids.assignableSubsetsValue,
    Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    intro e he
    exact F.ground_finite.mem_toFinset.mpr (assignable_ground F _ h.2 he)

theorem q_maximum : Specs.P205.Matroids.QMaximum := by
  intro α k F S
  classical
  have hne : (assignableSubsets F S).Nonempty := by
    refine ⟨∅, (mem_assignableSubsets F S ∅).2 ?_⟩
    simpa [Assignable] using And.intro (Set.empty_subset S) (assignable_empty F)
  obtain ⟨I, hI, hmax⟩ := Finset.exists_mem_eq_sup (assignableSubsets F S) hne Finset.card
  obtain ⟨hIS, hIa⟩ := (mem_assignableSubsets F S I).1 hI
  refine ⟨⟨↑I, hIS, hIa, ?_⟩, ?_⟩
  · simpa [q, Specs.P205.Matroids.qValue, assignableSubsets] using hmax.symm
  · intro J hJS hJa
    have hJf := F.ground_finite.subset (assignable_ground F J hJa)
    have hm : hJf.toFinset ∈ assignableSubsets F S := by
      apply (mem_assignableSubsets F S _).2
      simpa [Assignable] using And.intro hJS hJa
    have hle := Finset.le_sup (f := Finset.card) hm
    simpa [q, Specs.P205.Matroids.qValue, assignableSubsets, ← Set.ncard_eq_toFinset_card J hJf] using hle

theorem q_empty : Specs.P205.Matroids.QEmpty := by
  intro α k F
  obtain ⟨⟨I, hI, _, hcard⟩, _⟩ := q_maximum F ∅
  have hi : I = ∅ := Set.subset_empty_iff.mp hI
  simpa [hi] using hcard.symm

theorem q_zero : Specs.P205.Matroids.QZero := by
  intro α F S
  obtain ⟨⟨I, _, hI, hcard⟩, _⟩ := q_maximum F S
  have hi : I = ∅ := (assignable_zero F I).1 hI
  simpa [hi] using hcard.symm

end
end P205.Matroids
