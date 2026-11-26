import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner
import Mathlib.Analysis.Complex.Circle

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Topology

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterAlgebraicBorelPair

open Arithmetic.AdelicGroups (PointsIn)
open AdjointRepresentation (GroupPoints)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open CharacterDescent (Cocharacter)
open CharacterPairing (absoluteRoots characterValue)
open ExceptionalCompactInner (ActsOnComplexPoints HasCompactDifferential HasExceptionalType
  fixedSubgroup realConjugation)
open IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open Pinning (SplitBorelPair)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)

/-- The connected component containing the identity, viewed in the ambient group. -/
def identityComponent {X : Type*} [Group X] [TopologicalSpace X] (J : Subgroup X) : Set X :=
  Subtype.val '' connectedComponent (1 : J)

/-- A compact torus with the topology inherited from the ambient group. -/
def IsCompactTorus {X : Type*} [Group X] [TopologicalSpace X] (S : Subgroup X) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → Circle) ≃* S), Continuous e ∧ Continuous e.symm

/-- Maximality among the compact tori in the indicated subgroup or component. -/
def IsMaximalCompactTorus {X : Type*} [Group X] [TopologicalSpace X]
    (J : Set X) (S : Subgroup X) : Prop :=
  IsCompactTorus S ∧ (S : Set X) ⊆ J ∧
    ∀ U : Subgroup X, IsCompactTorus U → (U : Set X) ⊆ J → S ≤ U → U = S

variable {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}

abbrev complexGroup (G : AffineAlgebraicGroup ℝ) := (groupBaseChange ℝ ℂ).obj G.val
abbrev complexTest := CommAlgCat.of ℂ ℂ

/-- Evaluation through the actual inclusion into the complexification, followed
by the canonical comparison with complex-valued points of the real group. -/
def onPoints {P : SplitBorelPair ℂ} (hP : P.G = baseChangedAlgebraicGroup ℂ G)
    {Q : GroupScheme ℂ} (f : Q ⟶ P.G.val) (x : GroupPoints Q complexTest) : PointsIn i ℂ :=
  baseChangePoint ℝ ℂ G.val.X complexTest
    (((groupPointsFunctor ℂ).map (f ≫ eqToHom (congrArg Subtype.val hP))).app complexTest x)

/-- Conjugate inversion on complex units. -/
def conjugateInverse (z : ℂˣ) : ℂˣ :=
  Units.map Complex.conjAe.toRingHom.toMonoidHom z⁻¹

/-- A stable Borel pair on the actual complexification, with its restriction
automorphisms and a fixed regular integral cocharacter in the chosen chamber. -/
def StableChamber {P : SplitBorelPair ℂ}
    (hP : P.G = baseChangedAlgebraicGroup ℂ G) (θ : MulAut (PointsIn i ℂ)) : Prop :=
  let f : P.G.val ⟶ complexGroup G := eqToHom (congrArg Subtype.val hP)
  ∃ (a : Aut (complexGroup G)) (aT : Aut P.T.group) (aB : Aut P.B.group)
    (c : Cocharacter P.T.group),
    ActsOnComplexPoints (i := i) a θ ∧
    P.T.inclusion ≫ f ≫ a.asIso.hom = aT.asIso.hom ≫ P.T.inclusion ≫ f ∧
    P.B.inclusion ≫ f ≫ a.asIso.hom = aB.asIso.hom ≫ P.B.inclusion ≫ f ∧
    c ≫ aT.asIso.hom = c ∧ IsRegular P.T c ∧
    subgroupRoots P.T P.B = positiveRoots P.T c

def Statement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)),
      Continuous ω → Continuous θ →
      (∃ a, ActsOnComplexPoints (i := i) a
        (fun x => ω (realConjugation G i x)) ∧ HasCompactDifferential a) →
      (∃ a, ActsOnComplexPoints (i := i) a θ) →
      Function.Involutive ω → Function.Involutive θ → Function.Commute θ ω →
      CompactSpace (fixedSubgroup ω) → ConnectedSpace (fixedSubgroup ω) →
      ∀ (S T : Subgroup (PointsIn i ℂ)),
        IsMaximalCompactTorus (identityComponent (fixedSubgroup ω ⊓ fixedSubgroup θ)) S →
        (T : Set (PointsIn i ℂ)) =
          identityComponent (fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _)) →
        S ≤ T → IsMaximalCompactTorus (fixedSubgroup ω : Set _) T →
        ∃ (P : SplitBorelPair ℂ) (hP : P.G = baseChangedAlgebraicGroup ℂ G),
          T = fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _) ∧
          (T : Set (PointsIn i ℂ)) = (fixedSubgroup ω : Set _) ∩
            Set.range (onPoints (i := i) hP P.T.inclusion) ∧
          (∀ α : ↥(absoluteRoots P.T), ∃ t : GroupPoints P.T.group complexTest,
            onPoints (i := i) hP P.T.inclusion t ∈ S ∧
            characterValue α.val complexTest t ≠ 1) ∧
          (∀ (c : Cocharacter P.T.group) (z : ℂˣ),
            ω (onPoints (i := i) hP P.T.inclusion (cocharacterPoint c complexTest z)) =
              onPoints (i := i) hP P.T.inclusion
                (cocharacterPoint c complexTest (conjugateInverse z))) ∧
          StableChamber (i := i) hP θ

end LinearAlgebraicGroups.Specs.ExceptionalOuterAlgebraicBorelPair
