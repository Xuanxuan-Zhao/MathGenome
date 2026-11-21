import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing

/-! LA-C04, source lines 1323–1359. The section assumes an arbitrary
characteristic-zero field, a finite-dimensional semisimple Lie algebra, and
finite-dimensional left modules. Cohomology is the canonical exterior CE
complex, with the enveloping action extending the given Lie action. -/

noncomputable section
open AdvancedHomologicalAlgebra.CE
open LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
open P103.Specs.Ch10.Complexes
universe u v w

namespace Specs.LieAlgebrasAndRepresentations.FirstWhitehead

def cohomology_vanishes_type : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M],
    SolvableRadical.IsSemisimple_value k g →
      Subsingleton (Homology (ceCochain k g M) 1)

def cocycle_inner_type : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M],
    SolvableRadical.IsSemisimple_value k g →
    ∀ a : g →ₗ[k] M,
      (∀ x y, a ⁅x,y⁆ = ⁅x, a y⁆ - ⁅y, a x⁆) →
      ∃ m : M, ∀ x, a x = ⁅x,m⁆

end Specs.LieAlgebrasAndRepresentations.FirstWhitehead
