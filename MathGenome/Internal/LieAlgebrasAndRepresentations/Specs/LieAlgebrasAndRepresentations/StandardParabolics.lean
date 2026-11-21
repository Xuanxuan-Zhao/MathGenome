import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.BorelSubalgebras
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleRoots

/-! The classification part of LA-F07, source lines 3020–3032 and 3057–3075.
The real span is taken in the Killing-induced real root space of the given
Cartan. The root spaces in the formula are the original complex root spaces. -/

noncomputable section

universe u

namespace Specs.LieAlgebrasAndRepresentations.StandardParabolics

open _root_.LieAlgebrasAndRepresentations (RootRegular simpleRoots)
open BorelSubalgebras CompactFlagOrbit RealRootSpace RootDecomposition
open CompactConjugation (PositiveRoot)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L}

/-- Restriction of the complex Cartan dual to the real Cartan, followed
by taking real parts. -/
def restrictRoot (H : LieSubalgebra ℂ L) : Module.Dual ℂ H →ₗ[ℝ] E H where
  toFun := rootRestriction H
  map_add' a b := by
    ext x
    exact Complex.add_re (a x) (b x)
  map_smul' r a := by
    ext x
    change ((r : ℂ) * a x).re = r * (a x).re
    simp [Complex.mul_re]

/-- The regular vector specifies the same positive roots as this functional
on the complex Cartan dual. -/
def positiveFunctional (d : Realization H) (v : E H) : Module.Dual ℂ H →ₗ[ℝ] ℝ :=
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  (innerₗ (E H) v).comp (restrictRoot H)

/-- The simple roots of the chosen positive system, as an indexing type. -/
abbrev Simple (d : Realization H) (v : E H) : Type u :=
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  simpleRoots (realRoots H) v

/-- The real span of the selected simple roots. -/
def subsystemSpan (d : Realization H) (v : E H) (S : Set (Simple d v)) :
    Submodule ℝ (E H) :=
  Submodule.span ℝ (Subtype.val '' S)

/-- Positive roots in the real span of the selected simple roots. -/
abbrev SubsystemPositiveRoot (d : Realization H) (v : E H) (S : Set (Simple d v)) :=
  {a : PositiveRoot H (positiveFunctional d v) //
    restrictRoot H a.val ∈ subsystemSpan d v S}

/-- The negative summands belonging to the chosen subsystem. -/
def negativeSpace (d : Realization H) (v : E H) (S : Set (Simple d v)) : Submodule ℂ L :=
  ⨆ a : SubsystemPositiveRoot d v S, rootSpace_value H (-a.val.val)

/-- The Cartan and positive root spaces, together with the negative spaces
whose opposite roots lie in the indicated subsystem. -/
def parabolicSpace (d : Realization H) (v : E H) (S : Set (Simple d v)) :
    Submodule ℂ L :=
  borel H (positiveFunctional d v) ⊔ negativeSpace d v S

def classificationType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∃ d : Realization H,
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      ∀ (v : E H), RootRegular (realRoots H) v →
        ∃ B : LieSubalgebra ℂ L,
          B.toSubmodule = borel H (positiveFunctional d v) ∧ IsBorel B ∧
          ∃ e : Set (Simple d v) ≃ {P : LieSubalgebra ℂ L // B ≤ P},
            (∀ S, (e S).val.toSubmodule = parabolicSpace d v S) ∧
            (∀ S, Disjoint B.toSubmodule (negativeSpace d v S) ∧
              iSupIndep (fun a : SubsystemPositiveRoot d v S => rootSpace_value H (-a.val.val))) ∧
            (e ∅).val = B ∧ (e Set.univ).val = ⊤ ∧
            ∃ (τ : CompactConjugation.ConjugateMap L)
                (hs : HermitianSymmetric τ) (hp : HermitianPositive τ),
              letI c := hermitianCore τ hs hp
              letI := c.toNormedAddCommGroup
              letI := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := L)
              letI : NormedAlgebra ℝ (End L) := NormedAlgebra.restrictScalars ℝ ℂ _
              ∀ P : LieSubalgebra ℂ L, (∃ A : LieSubalgebra ℂ L, IsBorel A ∧ A ≤ P) →
                ∃ (S : Set (Simple d v)) (g : (End L)ˣ), g ∈ innerGroup ∧
                  P.toSubmodule = ((e S).val.toSubmodule).map g.val.toLinearMap

end Specs.LieAlgebrasAndRepresentations.StandardParabolics
