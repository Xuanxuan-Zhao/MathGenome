import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalCompactInner

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.ExceptionalOuterCompactPinning

open AbsoluteDynkinTypes (E6Reflection IsAbsolutelyAlmostSimple PreservesCartan)
open AdjointRepresentation (GroupPoints)
open Arithmetic.AdelicGroups (PointsIn)
open CharacterDescent (Cocharacter)
open ExceptionalCompactInner (ActsOnComplexPoints HasCompactDifferential HasExceptionalType
  fixedSubgroup realConjugation)
open IntegralModels (MatrixRealization)
open Pinning (AttachedDatum PinnedGroup PinnedIso SplitBorelPair)
open RootGroups (AdditiveLine CorootReflection rootPoint)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)

abbrev complexTest := CommAlgCat.of ℂ ℂ
abbrev complexGroup (G : AffineAlgebraicGroup ℝ) := (groupBaseChange ℝ ℂ).obj G.val

/-- The restrictions of an algebraic automorphism to the same Borel and torus. -/
structure PairAction (P : SplitBorelPair ℂ) where
  group : Aut P.G.val
  torus : Aut P.T.group
  borel : Aut P.B.group
  torus_comm : P.T.inclusion ≫ group.asIso.hom = torus.asIso.hom ≫ P.T.inclusion
  borel_comm : P.B.inclusion ≫ group.asIso.hom = borel.asIso.hom ≫ P.B.inclusion

def comparison {G : AffineAlgebraicGroup ℝ} {P : SplitBorelPair ℂ}
    (h : P.G = Unipotent.baseChangedAlgebraicGroup ℂ G) : P.G.val ≅ complexGroup G :=
  eqToIso (congrArg (fun H : AffineAlgebraicGroup ℂ => H.val) h)

def onPoints {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G} {P : SplitBorelPair ℂ}
    (e : P.G.val ≅ complexGroup G) {Q : GroupScheme ℂ} (f : Q ⟶ P.G.val)
    (x : GroupPoints Q complexTest) : PointsIn i ℂ :=
  baseChangePoint ℝ ℂ G.val.X complexTest
    (((groupPointsFunctor ℂ).map (f ≫ e.hom)).app complexTest x)

def conjugateInverseUnit (u : ℂˣ) : ℂˣ :=
  (Units.map Complex.conjAe.toMonoidHom u)⁻¹

/-- Conjugate inversion on the cocharacters of the actual torus. -/
def ConjugateInversion {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {P : SplitBorelPair ℂ} (e : P.G.val ≅ complexGroup G) (ω : MulAut (PointsIn i ℂ)) : Prop :=
  ∀ (c : Cocharacter P.T.group) (u : ℂˣ),
    ω (onPoints e P.T.inclusion (LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint c complexTest u)) =
      onPoints e P.T.inclusion
        (LinearAlgebraicGroups.CocharacterDynamics.cocharacterPoint c complexTest (conjugateInverseUnit u))

structure OuterInvolutions {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    (ω θ : MulAut (PointsIn i ℂ)) : Prop where
  continuous_compact : Continuous ω
  continuous_outer : Continuous θ
  compact_differential :
    ∃ a, ActsOnComplexPoints (i := i) a (fun x => ω (realConjugation G i x)) ∧
      HasCompactDifferential a
  algebraic_outer : ∃ a, ActsOnComplexPoints (i := i) a θ
  compact_involutive : Function.Involutive ω
  outer_involutive : Function.Involutive θ
  commute : Function.Commute θ ω
  compact_fixed : CompactSpace (fixedSubgroup ω)
  connected_fixed : ConnectedSpace (fixedSubgroup ω)
  outer : ¬ ∃ t : PointsIn i ℂ, θ = MulAut.conj t

abbrev simple {P : SplitBorelPair ℂ} (D : AttachedDatum P)
    (numbering : letI := D.comm; D.base.support ≃ Fin 6) (j : Fin 6) : Pinning.SimpleRoot P :=
  letI := D.comm
  ⟨(numbering.symm j).val, (D.simple_iff _).mp (numbering.symm j).property⟩

def simpleCoordinate {A : AdditiveLine ℂ} (P : PinnedGroup A) (α : Pinning.SimpleRoot P.pair) :
    A.group ⟶ P.pair.G.val :=
  (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion

def simpleCoroot {P : SplitBorelPair ℂ} (D : AttachedDatum P) (α : Pinning.SimpleRoot P) :
    Cocharacter P.T.group :=
  letI := D.comm
  Additive.toMul (D.datum.rootDatum.coroot α.val)

def CompactCompatible {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A} (e : P.pair.G.val ≅ complexGroup G)
    (D : AttachedDatum P.pair) (ω : MulAut (PointsIn i ℂ)) : Prop :=
  ∀ α : Pinning.SimpleRoot P.pair,
    ∃ (β : AbstractPairing.Root P.pair.T) (x : Pinning.RootCoordinate A P.pair.T
        (P.roots β).val α.val.val⁻¹),
      β.val = α.val.val⁻¹ ∧
      let xneg := x.val.hom ≫ (P.roots β).val.inclusion
      ∃ r : CorootReflection P.pair.T α.val.val (simpleCoordinate P α) xneg,
        r.coroot = simpleCoroot D α ∧
        ∀ z : ℂ,
          ω (onPoints e (𝟙 _) (rootPoint (simpleCoordinate P α) complexTest z)) =
            onPoints e (𝟙 _) (rootPoint xneg complexTest (-Complex.conjAe z))

/-- The algebraic diagram factor, together with its realization on the original points. -/
structure DiagramDecomposition {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {A : AdditiveLine ℂ} {P : PinnedGroup A} (e : P.pair.G.val ≅ complexGroup G)
    (a : PairAction P.pair) (θ : MulAut (PointsIn i ℂ)) where
  datum : AttachedDatum P.pair
  full_coroot_lattice : corootLattice datum = ⊤
  numbering : letI := datum.comm; datum.base.support ≃ Fin 6
  cartan : letI := datum.comm
    PreservesCartan (RootData.integralCartan datum.datum.rootDatum datum.base)
      (CartanMatrix.E 6) numbering
  diagram : PinnedIso P P
  pointDiagram : MulAut (PointsIn i ℂ)
  permutes_coordinates : ∀ j, simpleCoordinate P (simple datum numbering j) ≫ diagram.group.hom =
    simpleCoordinate P (simple datum numbering (E6Reflection j))
  permutes_coroots : ∀ j, simpleCoroot datum (simple datum numbering j) ≫ diagram.torus.hom =
    simpleCoroot datum (simple datum numbering (E6Reflection j))
  torus_eq : a.torus.asIso.hom = diagram.torus.hom
  acts : ActsOnComplexPoints (i := i) (Aut.of (e.symm ≪≫ diagram.group ≪≫ e)) pointDiagram
  involutive : Function.Involutive pointDiagram
  continuous : Continuous pointDiagram
  implements : ∃ t : GroupPoints P.pair.T.group complexTest,
    θ = MulAut.conj (onPoints e P.pair.T.inclusion t) * pointDiagram

/-- The diagram factor exists for any pinning of the preserved pair. -/
def DiagramDecompositionStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (A : AdditiveLine ℂ) (P : PinnedGroup A)
      (h : P.pair.G = Unipotent.baseChangedAlgebraicGroup ℂ G)
      (a : PairAction P.pair) (θ : MulAut (PointsIn i ℂ)),
      ActsOnComplexPoints (i := i) (Aut.of ((comparison h).symm ≪≫ a.group.asIso ≪≫ comparison h)) θ →
      Function.Involutive θ →
      (¬ ∃ t : PointsIn i ℂ, θ = MulAut.conj t) →
      Nonempty (DiagramDecomposition (i := i) (comparison h) a θ)

/-- Compact pinning and diagram decomposition of the specified actual Borel pair. -/
def CompactPinningStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∀ (ω θ : MulAut (PointsIn i ℂ)), OuterInvolutions (i := i) ω θ →
    ∀ (P : SplitBorelPair ℂ) (h : P.G = Unipotent.baseChangedAlgebraicGroup ℂ G)
      (a : PairAction P),
      ActsOnComplexPoints (i := i) (Aut.of ((comparison h).symm ≪≫ a.group.asIso ≪≫ comparison h)) θ →
      ConjugateInversion (i := i) (comparison h) ω →
      ∃ (A : AdditiveLine ℂ) (U : OrderedRootProducts.RootSubgroupFamily P.T)
        (p : Pinning.Pinning A P U),
        let pin : PinnedGroup A := ⟨P, U, p⟩
        ∃ d : DiagramDecomposition (P := pin) (i := i) (comparison h) a θ,
          CompactCompatible (P := pin) (comparison h) d.datum ω ∧
          Function.Commute d.pointDiagram ω ∧
          ∃ t : GroupPoints P.T.group complexTest,
            ω (onPoints (comparison h) P.T.inclusion t) = onPoints (comparison h) P.T.inclusion t ∧
            θ = MulAut.conj (onPoints (i := i) (comparison h) P.T.inclusion t) * d.pointDiagram

end LinearAlgebraicGroups.Specs.ExceptionalOuterCompactPinning
