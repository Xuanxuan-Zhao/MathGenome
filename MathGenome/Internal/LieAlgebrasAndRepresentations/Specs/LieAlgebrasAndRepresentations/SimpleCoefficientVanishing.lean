import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CentralActionHomotopy

/-! LA-C03, source lines 1259–1321. The field is arbitrary of characteristic
zero. Cohomology uses the exterior CE complex with its constructed boundary,
and Ext uses an arbitrary projective resolution of the augmentation module.
The coefficient action is the extension of the original Lie representation. -/

noncomputable section
open CategoryTheory
open AdvancedHomologicalAlgebra.CE AdvancedHomologicalAlgebra.CE.Ext
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open LieAlgebrasAndRepresentations.CentralActionHomotopy
universe u v w

namespace LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
variable (k : Type u) (g : Type v) (M : Type w)
  [Field k] [LieRing g] [LieAlgebra k g]
  [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]

attribute [local instance] LieAlgebrasAndRepresentations.CentralActionHomotopy.coefficientModule

/-- The extended action restricts to the given scalar action. -/
instance coefficientScalarTower : IsScalarTower k (U k g) M := by
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change ModuleCasimir.action k g M (algebraMap k (U k g) r) m = r • m
  rw [AlgHom.commutes]
  rfl

/-- The canonical exterior CE complex, including its degree-zero term. -/
abbrev ceCochain [FiniteDimensional k g] :=
  let C := cochainData k g M (boundaryData k g)
  cochain k g M C.differential C.squared

end LieAlgebrasAndRepresentations.SimpleCoefficientVanishing

namespace Specs.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
open _root_.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing

/-- All natural degrees are included; no algebraic closure hypothesis occurs. -/
def cohomology_vanishes_type : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M] [LieModule.IsIrreducible k g M],
    SolvableRadical.IsSemisimple_value k g → ¬ LieModule.IsTrivial g M →
    ∀ q : ℕ, Subsingleton (Homology (ceCochain k g M) q)

/-- The same vanishing in the resolution-independent Ext model. -/
def ext_vanishes_type : Prop :=
  ∀ (k : Type u) (g : Type v) (M : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule g M] [LieModule k g M] [LieModule.IsIrreducible k g M],
    SolvableRadical.IsSemisimple_value k g → ¬ LieModule.IsTrivial g M →
    letI := LieAlgebrasAndRepresentations.CentralActionHomotopy.coefficientModule k g M
    letI := trivialModule k g
    ∀ (Q : LeftResolution (U k g) k), Q.IsProjective →
      ∀ q : ℕ, Subsingleton (ExtWith Q M q)

end Specs.LieAlgebrasAndRepresentations.SimpleCoefficientVanishing
