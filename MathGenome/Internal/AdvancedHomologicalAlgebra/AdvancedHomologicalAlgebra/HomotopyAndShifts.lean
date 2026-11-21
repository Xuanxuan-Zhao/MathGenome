import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts

/-! HA-K01: cochain homotopy category, signed shifts, and cohomology.
The reused Mathlib shifts have X^n = X^(n+m), differential (-1)^m d,
and homotopies (-1)^m h. The quotient is by existence of cochain homotopy,
not by quasi-isomorphism. All isomorphisms below are natural isomorphisms.
-/

open CategoryTheory
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts

namespace AdvancedHomologicalAlgebra.HomotopyAndShifts

/-- The cochain homotopy category: the categorical quotient by existence of a cochain homotopy. -/
noncomputable abbrev homotopyCategory : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.homotopyCategoryType :=
  fun A _ _ => HomotopyCategory A (ComplexShape.up ℤ)

/-- The quotient functor sends a cochain map to its homotopy class. -/
noncomputable abbrev quotient : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.quotientType :=
  fun A _ _ => HomotopyCategory.quotient A (ComplexShape.up ℤ)

/-- Two cochain maps have the same quotient class exactly when they are cochain homotopic. -/
theorem quotient_eq_iff : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.quotient_eq_iffType :=
  by
  intro A _ _ X Y f g
  exact CategoryTheory.Quotient.functor_map_eq_iff (homotopic A (ComplexShape.up ℤ)) f g

/-- Addition descends to homotopy classes. -/
theorem quotient_add : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.quotient_addType :=
  by
  intro A _ _ X Y f g
  exact (Q A).map_add

/-- The signed cochain shift functor, including its action on cochain maps. -/
noncomputable abbrev complexShift : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.complexShiftType :=
  fun A _ _ m => CategoryTheory.shiftFunctor (CochainComplex A ℤ) m

/-- The shifted object in degree n is the original object in degree n + m. -/
theorem shift_object : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.shift_objectType :=
  by intro A _ _ X m n; rfl

/-- The shifted differential is multiplied by (-1)^m. Int.negOnePow is (-1 : ℤˣ)^m, acting on each Hom group. -/
theorem shift_differential : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.shift_differentialType :=
  by intro A _ _ X m i j; rfl

/-- Shifting cochain maps reindexes their components without a sign. -/
theorem shift_map : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.shift_mapType :=
  by intro A _ _ X Y f m n; rfl

/-- A homotopy shifts with the same (-1)^m sign as the differentials. -/
noncomputable def shiftHomotopy : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.shiftHomotopyType :=
  fun _A _ _ _X _Y _f _g h m => h.shift m

/-- In particular the degree -1 homotopy component is (-1)^m times the original reindexed component. -/
theorem shift_homotopy_component : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.shift_homotopy_componentType :=
  by intro A _ _ X Y f g h m i j; rfl

/-- The shift functor on the homotopy category. -/
noncomputable abbrev homotopyShift : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.homotopyShiftType :=
  fun A _ _ m => CategoryTheory.shiftFunctor (K A) m

/-- The quotient functor commutes naturally with shifts; hence the signed shifts descend. -/
noncomputable def shiftDescends : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.shiftDescendsType :=
  fun A _ _ m => (Q A).commShiftIso m

/-- The zero shift on cochain complexes is naturally the identity. -/
noncomputable def complexShiftZero : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.complexShiftZeroType :=
  fun A _ _ => CategoryTheory.shiftFunctorZero (CochainComplex A ℤ) ℤ

/-- Shifts of cochain complexes compose by addition, naturally in the complex. -/
noncomputable def complexShiftAdd : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.complexShiftAddType :=
  fun A _ _ m l => CategoryTheory.shiftFunctorAdd (CochainComplex A ℤ) m l

/-- The zero shift on the homotopy category is naturally the identity. -/
noncomputable def homotopyShiftZero : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.homotopyShiftZeroType :=
  fun A _ _ => CategoryTheory.shiftFunctorZero (K A) ℤ

/-- Shifts on the homotopy category compose by addition. -/
noncomputable def homotopyShiftAdd : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.homotopyShiftAddType :=
  fun A _ _ m l => CategoryTheory.shiftFunctorAdd (K A) m l

/-- Cohomology in cochain degree n, as a functor on the homotopy category. -/
noncomputable def cohomology : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.cohomologyType :=
  fun A _ _ n => HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n

/-- The ordinary cohomology functor factors naturally through the homotopy quotient. -/
noncomputable def cohomologyFactors : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.cohomologyFactorsType :=
  fun A _ _ n => HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) n

/-- Homotopic maps induce equal cohomology maps in every degree. -/
theorem homotopic_cohomology_map : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.homotopic_cohomology_mapType :=
  by
  intro A _ _ X Y f g h n
  exact h.homologyMap_eq n

/-- The natural cohomology identification H^n(X[m]) ≅ H^(n+m)(X). -/
noncomputable def cohomologyShiftComplex : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.cohomologyShiftComplexType :=
  fun A _ _ m n => CochainComplex.ShiftSequence.shiftIso A m n (n + m) (add_comm m n)

/-- The same cohomology identification is natural on the homotopy category. -/
noncomputable def cohomologyShiftHomotopy : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.cohomologyShiftHomotopyType :=
  fun A _ _ m n =>
  (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0).shiftIso
    m n (n + m) (add_comm m n)

/-- The cohomology shift comparison commutes with every cochain map. -/
theorem cohomology_shift_naturality : Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts.cohomology_shift_naturalityType :=
  by
  intro A _ _ X Y f m n
  exact (CochainComplex.ShiftSequence.shiftIso A m n (n + m) (add_comm m n)).hom.naturality f

end AdvancedHomologicalAlgebra.HomotopyAndShifts
