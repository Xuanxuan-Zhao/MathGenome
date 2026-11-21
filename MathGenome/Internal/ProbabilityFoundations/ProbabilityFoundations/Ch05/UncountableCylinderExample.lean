import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.CylinderFramework

namespace ProbabilityFoundations.Ch05.UncountableCylinderExample

open CylinderFramework
universe u v

/-- Finite cylinders depend on their finite support; complements preserve the
support, and a countable union uses the union of the countable supports. -/
theorem countableDependence :
    Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample.CountableDependence.{u,v} := by
  intro I S inst A hA
  refine MeasurableSpace.generateFrom_induction (finiteCylinders S)
    (fun A _ => ∃ J : Set I, J.Countable ∧ Determines J A) ?_ ?_ ?_ ?_ A hA
  · intro A hA _
    rcases hA with ⟨F, B, _, rfl⟩
    refine ⟨(F : Set I), F.countable_toSet, ?_⟩
    intro x y hxy
    have hproj : finiteProjection S F x = finiteProjection S F y := by
      funext i
      exact hxy i i.property
    exact show finiteProjection S F x ∈ B ↔ finiteProjection S F y ∈ B from
      hproj ▸ Iff.rfl
  ·
    exact ⟨∅, Set.countable_empty, fun _ _ _ => Iff.rfl⟩
  · intro A _ hA
    rcases hA with ⟨J, hJ, hdet⟩
    exact ⟨J, hJ, fun x y hxy => not_congr (hdet x y hxy)⟩
  · intro A _ hA
    choose J hJ hdet using hA
    refine ⟨⋃ n, J n, Set.countable_iUnion hJ, ?_⟩
    intro x y hxy
    simp only [Set.mem_iUnion]
    apply exists_congr
    intro n
    exact hdet n x y (fun i hi => hxy i (Set.mem_iUnion.mpr ⟨n, hi⟩))

/-- Changing a coordinate outside `J` from zero to one preserves the coordinates
in `J`, but takes the point out of the zero singleton. -/
theorem zeroSingletonNotDetermined :
    Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample.ZeroSingletonNotDetermined.{u} := by
  intro I inst J hJ hdet
  classical
  have hex : ∃ i : I, i ∉ J := by
    by_contra h
    have hJuniv : J = Set.univ := Set.eq_univ_of_forall (by simpa using h)
    exact Set.not_countable_univ (hJuniv ▸ hJ)
  obtain ⟨i, hi⟩ := hex
  let y : ProductSpace (fun _ : I => Bool) := Function.update (zeroPoint I) i true
  have hagree : ∀ j ∈ J, zeroPoint I j = y j := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hi hj
    simp [y, Function.update_of_ne hji]
  have hy : y ∈ ({zeroPoint I} : Set (ProductSpace (fun _ : I => Bool))) :=
    (hdet (zeroPoint I) y hagree).mp (Set.mem_singleton _)
  have heq : y = zeroPoint I := Set.mem_singleton_iff.mp hy
  have hval := congrFun heq i
  simp [y, zeroPoint] at hval

theorem zeroSingletonClosed :
    Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample.ZeroSingletonClosed.{u} := by
  intro I
  exact isClosed_singleton

theorem zeroSingletonNotMeasurable :
    Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample.ZeroSingletonNotMeasurable.{u} := by
  intro I inst h
  obtain ⟨J, hJ, hdet⟩ := countableDependence (fun _ : I => Bool) {zeroPoint I} h
  exact zeroSingletonNotDetermined I J hJ hdet

theorem cylinderLtBorel :
    Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample.CylinderLtBorel.{u} := by
  intro I inst
  apply lt_of_le_of_ne
  · rw [cylinderSigma_eq_pi]
    exact pi_le_borel_pi
  · intro heq
    apply zeroSingletonNotMeasurable I
    rw [heq]
    have h := @MeasurableSpace.measurableSet_generateFrom
      (ProductSpace (fun _ : I => Bool)) {U | IsOpen U} ({zeroPoint I}ᶜ)
      (zeroSingletonClosed I).isOpen_compl
    exact h.of_compl

end ProbabilityFoundations.Ch05.UncountableCylinderExample
