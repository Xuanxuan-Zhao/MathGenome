import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CentralIsogenies
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.PathConnected

noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open LinearAlgebraicGroups.Arithmetic.AdelicGroups

namespace LinearAlgebraicGroups.Specs.ExceptionalComplexPointGeometry

open IntegralModels (MatrixRealization)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsSplitAdditive)
open Unipotent (baseChangedAlgebraicGroup)

variable {k : Type} [Field k] {G H : AffineAlgebraicGroup k}

/-- The actual map on complex points induced by a morphism over the ground field. -/
abbrev pointMap [Algebra k ℂ] (i : MatrixRealization G) (j : MatrixRealization H)
    (f : G.val ⟶ H.val) : PointsIn i ℂ →* PointsIn j ℂ :=
  (((groupPointsFunctor k).map f).app (CommAlgCat.of k ℂ)).hom

/-- Polynomial coordinate maps are continuous in the given closed matrix realizations. -/
def ContinuousPointMap : Prop :=
  ∀ {k : Type} [Field k] [Algebra k ℂ] {G H : AffineAlgebraicGroup k}
    (i : MatrixRealization G) (j : MatrixRealization H) (f : G.val ⟶ H.val),
    Continuous (pointMap i j f)

/-- The scalar-extension point comparison in the original real realizations. -/
def ContinuousComplexifiedPointMap : Prop :=
  ∀ {G H : AffineAlgebraicGroup ℝ} (i : MatrixRealization G) (j : MatrixRealization H)
    (f : (groupBaseChange ℝ ℂ).obj G.val ⟶ (groupBaseChange ℝ ℂ).obj H.val),
    ∃ p : PointsIn i ℂ →* PointsIn j ℂ, Continuous p ∧
      ∀ z : Points ((groupBaseChange ℝ ℂ).obj G.val).X (CommAlgCat.of ℂ ℂ),
        (show Points H.val.X (CommAlgCat.of ℝ ℂ) from
          p (baseChangePoint ℝ ℂ G.val.X (CommAlgCat.of ℂ ℂ) z)).left =
        (baseChangePoint ℝ ℂ H.val.X (CommAlgCat.of ℂ ℂ) (z ≫ f.hom.hom)).left

/-- In the original realizations a finite surjective real group morphism induces
a surjective covering of complex point groups with finite kernel. -/
def FiniteSurjectiveCovering : Prop :=
  ∀ {G H : AffineAlgebraicGroup ℝ} (i : MatrixRealization G) (j : MatrixRealization H)
    (f : G.val ⟶ H.val), IsFinite f.hom.hom.left → AlgebraicGeometry.Surjective f.hom.hom.left →
    let p := pointMap i j f
    Continuous p ∧ Function.Surjective p ∧ Finite p.ker ∧ IsCoveringMap p

/-- The finite covering conclusion for the central isogeny to an adjoint quotient. -/
def CentralIsogenyCovering : Prop :=
  ∀ {G H : AffineAlgebraicGroup ℝ} (i : MatrixRealization G) (j : MatrixRealization H)
    (f : G.val ⟶ H.val), CentralIsogenies.IsCentralIsogeny f →
    let p := pointMap i j f
    Continuous p ∧ Function.Surjective p ∧ Finite p.ker ∧ IsCoveringMap p

/-- Images of complex split tori and additive lines are path connected in the
target's matrix realization. -/
def PathConnectedLineImages : Prop :=
  ∀ {H : AffineAlgebraicGroup ℂ} (j : MatrixRealization H) {S : GroupScheme ℂ}
    (f : S ⟶ H.val), IsSplitTorus S ∨ IsSplitAdditive S →
    IsPathConnected (Set.range (fun z : Points S.X (CommAlgCat.of ℂ ℂ) =>
      (show PointsIn j ℂ from z ≫ f.hom.hom)))

/-- The same image statements for maps into a complexification, using the
canonical comparison to the original real group's complex points. -/
def PathConnectedComplexifiedLineImages : Prop :=
  ∀ {H : AffineAlgebraicGroup ℝ} (j : MatrixRealization H) {S : GroupScheme ℂ}
    (f : S ⟶ (groupBaseChange ℝ ℂ).obj H.val), IsSplitTorus S ∨ IsSplitAdditive S →
    IsPathConnected (Set.range (fun z : Points S.X (CommAlgCat.of ℂ ℂ) =>
      (show PointsIn j ℂ from baseChangePoint ℝ ℂ H.val.X (CommAlgCat.of ℂ ℂ) (z ≫ f.hom.hom))))

/-- A reductive group over ℂ has a path connected complex point group. -/
def ComplexPointsPathConnected : Prop :=
  ∀ (G : AffineAlgebraicGroup ℂ) (i : MatrixRealization G), IsReductive G →
    PathConnectedSpace (PointsIn i ℂ)

/-- The same conclusion in the original matrix realization of a real group
whose complexification is reductive. -/
def RealGroupComplexPointsPathConnected : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsReductive (baseChangedAlgebraicGroup ℂ G) → PathConnectedSpace (PointsIn i ℂ)

/-- For a reductive real group the complex point group in its given matrix
realization is path connected. -/
def ReductiveRealGroupComplexPointsPathConnected : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsReductive G → PathConnectedSpace (PointsIn i ℂ)

end LinearAlgebraicGroups.Specs.ExceptionalComplexPointGeometry
