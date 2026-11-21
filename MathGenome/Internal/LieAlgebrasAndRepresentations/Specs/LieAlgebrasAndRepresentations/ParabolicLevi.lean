import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.StandardParabolics
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Nilradical
import Mathlib.Algebra.Lie.Semisimple.Defs

/-! The Levi and nilradical assertions of LA-F07, source lines 3032–3055 and
3077–3093. All root spaces belong to the original complex Lie algebra. -/

noncomputable section

universe u

namespace Specs.LieAlgebrasAndRepresentations.ParabolicLevi

open _root_.LieAlgebrasAndRepresentations (RootRegular)
open StandardParabolics RealRootSpace RootDecomposition RootForm
open CompactConjugation (PositiveRoot)
open CompactFlagOrbit (borel)
open BorelSubalgebras (IsBorel)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L}

/-- The complex roots in the real span of the selected simple roots. -/
abbrev SubsystemRoot (d : Realization H) (v : E H) (S : Set (Simple d v)) :=
  {a : rootSet_value H // rootRestriction H a.val ∈ subsystemSpan d v S}

/-- The original Cartan plus all the subsystem root spaces. -/
def leviSpace (d : Realization H) (v : E H) (S : Set (Simple d v)) : Submodule ℂ L :=
  H.toSubmodule ⊔ ⨆ a : SubsystemRoot d v S, rootSpace_value H a.val.val

/-- The roots on one side of the subsystem. Use the negative functional for
the opposite side. -/
def nilSpace (d : Realization H) (v : E H) (S : Set (Simple d v))
    (f : Module.Dual ℂ H →ₗ[ℝ] ℝ) : Submodule ℂ L :=
  ⨆ a : {a : PositiveRoot H f // rootRestriction H a.val ∉ subsystemSpan d v S},
    rootSpace_value H a.val.val

/-- The opposite standard parabolic uses the negative Borel and the positive
root spaces of the subsystem. -/
def oppositeSpace (d : Realization H) (v : E H) (S : Set (Simple d v)) : Submodule ℂ L :=
  borel H (-positiveFunctional d v) ⊔
    ⨆ a : SubsystemPositiveRoot d v S, rootSpace_value H a.val.val

/-- The Cartan span of the normalized subsystem coroots. -/
def subsystemCartan (d : Realization H) (v : E H) (S : Set (Simple d v)) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun a : SubsystemRoot d v S => coroot_value H a.val.val)

/-- The Cartan complement annihilated by the selected simple roots. -/
def centralCartan (d : Realization H) (v : E H) (S : Set (Simple d v)) : Submodule ℂ H :=
  ⨅ i : S, LinearMap.ker (d.j (i.val : E H))

def decompositionType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (d : Realization H) (v : E H),
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      RootRegular (realRoots H) v →
      ∀ (S : Set (Simple d v)) (P : LieSubalgebra ℂ L),
        P.toSubmodule = parabolicSpace d v S →
        ∃ (M Q : LieSubalgebra ℂ L) (U : LieIdeal ℂ P) (V : LieIdeal ℂ Q),
          M.toSubmodule = leviSpace d v S ∧ Q.toSubmodule = oppositeSpace d v S ∧
          U.toSubmodule.map P.incl.toLinearMap = nilSpace d v S (positiveFunctional d v) ∧
          V.toSubmodule.map Q.incl.toLinearMap = nilSpace d v S (-positiveFunctional d v) ∧
          Disjoint M.toSubmodule (U.toSubmodule.map P.incl.toLinearMap) ∧
          P.toSubmodule = M.toSubmodule ⊔ U.toSubmodule.map P.incl.toLinearMap ∧
          Disjoint M.toSubmodule (V.toSubmodule.map Q.incl.toLinearMap) ∧
          Q.toSubmodule = M.toSubmodule ⊔ V.toSubmodule.map Q.incl.toLinearMap ∧
          (∃ B : LieSubalgebra ℂ L,
            B.toSubmodule = borel H (-positiveFunctional d v) ∧ IsBorel B ∧ B ≤ Q) ∧
          P ⊓ Q = M ∧
          U = Nilradical.nilradical_value ℂ P ∧
          V = Nilradical.nilradical_value ℂ Q ∧
          LieRing.IsNilpotent U ∧ LieRing.IsNilpotent V ∧
          (S = Set.univ → M = ⊤ ∧ U = ⊥ ∧ V = ⊥) ∧
          (S = ∅ → M = H ∧ P.toSubmodule = borel H (positiveFunctional d v) ∧
            Q.toSubmodule = borel H (-positiveFunctional d v))

def structureType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ (d : Realization H) (v : E H),
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      RootRegular (realRoots H) v →
      ∀ (S : Set (Simple d v)) (M : LieSubalgebra ℂ L),
        M.toSubmodule = leviSpace d v S →
        LieAlgebra.HasCentralRadical ℂ M ∧
        (LieAlgebra.center ℂ M).toSubmodule.map M.incl.toLinearMap =
          (centralCartan d v S).map H.incl.toLinearMap ∧
        ∃ K : LieIdeal ℂ M,
          LieAlgebra.IsSemisimple ℂ K ∧
          K.toSubmodule.map M.incl.toLinearMap =
            (subsystemCartan d v S).map H.incl.toLinearMap ⊔
              ⨆ a : SubsystemRoot d v S, rootSpace_value H a.val.val ∧
          IsCompl K (LieAlgebra.center ℂ M)

end Specs.LieAlgebrasAndRepresentations.ParabolicLevi
