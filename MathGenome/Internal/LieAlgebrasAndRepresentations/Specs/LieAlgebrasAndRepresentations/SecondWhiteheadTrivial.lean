import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical

/-! LA-I04, source lines 4188–4208, with the chapter's left-module convention
(lines 4048–4058). The coefficients carry the trivial enveloping-algebra action
via its augmentation. The complex below is the canonical exterior CE complex,
with the actual boundary constructed in HA-A06; in particular dℓ(x,y)=-ℓ([x,y]).
Semisimplicity means vanishing solvable radical. No algebraic closure or
nonzero-algebra assumption is made. -/
noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.SecondWhiteheadTrivial
open AdvancedHomologicalAlgebra.CE

variable (k : Type u) (g : Type v) [Field k] [LieRing g] [LieAlgebra k g]

local instance : Module (U k g) k := Ext.trivialModule k g
local instance : IsScalarTower k (U k g) k :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change Shared.Lie.augmentation k g (algebraMap k (U k g) r) * x = r • x
    simp

abbrev cochains [Module.Free k g] := cochainData k g k (boundaryData k g)

abbrev differential [Module.Free k g] := (cochains k g).differential

abbrev complex [Module.Free k g] :=
  Ext.cochain k g k (differential k g) (cochains k g).squared

abbrev H2 [Module.Free k g] :=
  P103.Specs.Ch10.Complexes.Homology (complex k g) 2

end LieAlgebrasAndRepresentations.SecondWhiteheadTrivial

namespace Specs.LieAlgebrasAndRepresentations.SecondWhiteheadTrivial
open _root_.AdvancedHomologicalAlgebra.CE
open _root_.LieAlgebrasAndRepresentations.SecondWhiteheadTrivial

/-- Every actual degree-two CE cocycle has a degree-one primitive. -/
def cocycleExactType : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g]
    [LieAlgebra k g] [FiniteDimensional k g],
    SolvableRadical.IsSemisimple_value k g →
    ∀ ω : W k g 2 →ₗ[k] k, differential k g 2 ω = 0 →
      ∃ ℓ : W k g 1 →ₗ[k] k, differential k g 1 ℓ = ω

/-- Vanishing of the quotient cohomology of the same canonical complex. -/
def secondWhiteheadType : Prop :=
  ∀ (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g]
    [LieAlgebra k g] [FiniteDimensional k g],
    SolvableRadical.IsSemisimple_value k g → Subsingleton (H2 k g)

end Specs.LieAlgebrasAndRepresentations.SecondWhiteheadTrivial
