import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.CharacterRing
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalJordanFactors
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.LinearAlgebra.Trace

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Classical TensorProduct

universe u v w

namespace LinearAlgebraicGroups.Specs.SteinbergGeometricFibres

open CharacterDescent (Character)
open CharacterPairing (characterValue)
open FlagLineBundle (OppositeBorelPair)
open RootWeightAction (Representation)
open FormalCharacters (formalCharacter)
open _root_.LinearAlgebraicGroups.Affine (RationalPoints IsRationalJordanDecomposition)

noncomputable section

/-- Evaluate a Laurent polynomial using the given values of its characters. -/
def integralEvaluation {k X : Type*} [Field k] [CommGroup X] (t : X →* kˣ) :
    MonoidAlgebra ℤ X →+* k :=
  MonoidAlgebra.liftNCRingHom (Int.castRingHom k) ((Units.coeHom k).comp t)
    (fun _ _ => Commute.all _ _)

/-- The trace of the matrix of a rational point in the given representation. -/
def pointTrace {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    {G : GroupScheme k} (ρ : Representation G I) (g : RationalPoints G) : k :=
  Matrix.trace (ρ.app (CommAlgCat.of k k) g).val

/-- On the torus the integral formal character evaluates to the matrix trace. -/
def TorusTrace : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (_hs : GeometricRadicals.IsSplitTorus T.group) [IsCommMonObj T.group.X]
    (ρ : Representation G.val I) (t : RationalPoints T.group)
    (z : Character T.group →* kˣ),
    (∀ χ, (z χ : k) = characterValue χ (CommAlgCat.of k k) t) →
    pointTrace ρ (t ≫ T.inclusion.hom.hom) =
      integralEvaluation z (formalCharacter T ρ)

/-- Trace is insensitive to the unipotent multiplicative Jordan factor. -/
def JordanTrace : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
    (G : AffineAlgebraicGroup k) (ρ : Representation G.val I)
    {g s v : RationalPoints G.val},
    IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ g s v →
    pointTrace ρ g = pointTrace ρ s

/-- A monic highest monomial for an integral grading of the weight lattice. -/
def HasHighestTerm {X : Type*} [CommGroup X] (degree : X →* Multiplicative ℤ)
    (p : MonoidAlgebra ℤ X) (x : X) : Prop :=
  p.coeff x = 1 ∧
    ∀ y, y ≠ x → p.coeff y ≠ 0 → (degree y).toAdd < (degree x).toAdd

/-- Simply connected weight coordinates and the orbit representatives imply
generation by any Weyl-invariant monic fundamental characters. -/
def IntegralGeneration : Prop :=
  ∀ {X W A J : Type*} [CommGroup X] [Group W] [Finite W] [Fintype J]
    (a : W →* MulAut X) (i : A ↪ X) (degree : X →* Multiplicative ℤ)
    (weight : J → X) (character : J → MonoidAlgebra ℤ X),
    (∀ x, ∃ j w, a w x = i j) →
    (∀ j l : A, (∃ w, a w (i j) = i l) ↔ j = l) →
    (∀ j, 0 ≤ (degree (i j)).toAdd) →
    (∀ j, ∃ m : J → ℕ, i j = ∏ r, weight r ^ m r) →
    (∀ j, character j ∈ CharacterRing.invariantRing a) →
    (∀ j, HasHighestTerm degree (character j) (weight j)) →
    Subring.closure (Set.range character) = CharacterRing.invariantRing a

/-- Agreement on the generators propagates to the whole integral invariant
ring, regardless of the characteristic of the coefficient field. -/
def IntegralEvaluationAgreement : Prop :=
  ∀ {k X W J : Type*} [Field k] [CommGroup X] [Group W]
    (a : W →* MulAut X) (character : J → MonoidAlgebra ℤ X)
    (z z' : X →* kˣ),
    Subring.closure (Set.range character) = CharacterRing.invariantRing a →
    (∀ j, integralEvaluation z (character j) = integralEvaluation z' (character j)) →
    ∀ f ∈ CharacterRing.invariantRing a, integralEvaluation z f = integralEvaluation z' f

/-- For a split semisimple group with full simply connected cocharacter
lattice, take the fundamental characters of its marked positive Borel.
The modules realizing them are the rational simple socles from E06. -/
def FundamentalGeneration : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G),
    GeometricRadicals.IsSemisimple G → SimplyConnectedLattice.GeometricallySimplyConnected G →
    ∃ (comm : IsCommMonObj P.torus.group.X), letI := comm
    ∃ (D : AbstractPairing.Datum P.torus) (e : DatumAndWeyl.Identification D)
      (b : D.rootDatum.Base) (U : ClosedSubgroup P.positive.group),
      DominantOrder.IsBaseFor D.rootDatum (BorelsAndChambers.subgroupRoots P.torus P.positive) b ∧
      GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U ∧
      ∃ (ω : b.support → Character P.torus.group)
        (S : ∀ j, SimpleClassification.SocleModel P U (ω j)),
        (∀ i j, D.rootDatum.toLinearMap (Additive.ofMul (ω i)) (D.rootDatum.coroot j.val) =
          if i = j then 1 else 0) ∧
        (∀ x, ∃ (l : CharacterRing.dominantWeights P) (w : D.rootDatum.weylGroup),
          CharacterRing.weylAction e w x = l.val) ∧
        (∀ j l : CharacterRing.dominantWeights P,
          (∃ w, CharacterRing.weylAction e w j.val = l.val) ↔ j = l) ∧
        Subring.closure (Set.range fun j => formalCharacter P.torus (S j).socleAction) =
          CharacterRing.invariantRing (CharacterRing.weylAction e)

/-- Matrix traces are class functions on the rational point group. -/
def TraceConjugation : Prop :=
  ∀ {k I : Type u} [Field k] [Fintype I] [DecidableEq I] {G : GroupScheme k}
    (ρ : Representation G I) (h g : RationalPoints G),
    pointTrace ρ (h * g * h⁻¹) = pointTrace ρ g

/-- Evaluation with coefficients already in the field. -/
def fieldEvaluation {k X : Type*} [Field k] [CommGroup X] (t : X →* kˣ) :
    MonoidAlgebra k X →+* k :=
  MonoidAlgebra.liftNCRingHom (RingHom.id k) ((Units.coeHom k).comp t)
    (fun _ _ => Commute.all _ _)

/-- The orbit separation result proved separately in the Steinberg section. -/
def InvariantLaurentSeparation : Prop :=
  ∀ {k X W : Type*} [Field k] [CommGroup X] [Group W] [Fintype W],
  ∀ (a : W →* MulAut X) (z z' : X →* kˣ),
    (∀ w, z.comp (a w).toMonoidHom ≠ z') →
    ∃ f : MonoidAlgebra k X,
      (∀ w, MonoidAlgebra.mapDomainRingEquiv k (a w) f = f) ∧
      fieldEvaluation z f = 0 ∧ fieldEvaluation z' f = 1

/-- Integral orbit sums suffice to test the same orbit-separation relation
as the invariant polynomials with field coefficients. -/
def IntegralOrbitSeparation : Prop :=
  InvariantLaurentSeparation.{u,v,w} →
  ∀ {k : Type u} {X : Type v} {W : Type w} {A : Type*} [Field k] [CommGroup X] [Group W] [Finite W]
    (a : W →* MulAut X) (i : A ↪ X) (z z' : X →* kˣ),
    (∀ x, ∃ j w, a w x = i j) →
    (∀ j l : A, (∃ w, a w (i j) = i l) ↔ j = l) →
    (∀ f ∈ CharacterRing.invariantRing a, integralEvaluation z f = integralEvaluation z' f) →
    ∃ w, z.comp (a w).toMonoidHom = z'

/-- Evaluation in the actual character lattice distinguishes points of the
split torus and yields their unit-valued coordinates. -/
def TorusPointCoordinates : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, GeometricRadicals.IsSplitTorus T →
    ∃ z : RationalPoints T → (Character T →* kˣ), Function.Injective z ∧
      ∀ t χ, (z t χ : k) = characterValue χ (CommAlgCat.of k k) t

/-- A group scheme morphism evaluated on points over the ground field. -/
def pointHom {k : Type u} [Field k] {G H : GroupScheme k} (f : G ⟶ H) :
    RationalPoints G →* RationalPoints H :=
  (((groupPointsFunctor k).map f).app (CommAlgCat.of k k)).hom

/-- Equality under the lattice Weyl action yields conjugacy of torus points
by a rational representative in the actual scheme normalizer. -/
def TorusWeylConjugation : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val},
    GeometricRadicals.IsSplitTorus T.group → ∀ [IsCommMonObj T.group.X]
    {D : AbstractPairing.Datum T} (e : DatumAndWeyl.Identification D)
    (w : D.rootDatum.weylGroup) (t t' : RationalPoints T.group),
    (∀ χ, characterValue χ (CommAlgCat.of k k) t' =
      characterValue (CharacterRing.weylAction e w χ) (CommAlgCat.of k k) t) →
    ∃ g : RationalPoints G.val,
      g * pointHom T.inclusion t * g⁻¹ = pointHom T.inclusion t'

/-- Every point of a split torus is its own semisimple part. -/
def SplitTorusJordan : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (T : AffineAlgebraicGroup k),
    GeometricRadicals.IsSplitTorus T.val → ∀ t : RationalPoints T.val,
      IsRationalJordanDecomposition ⟨T.val, T.property.1⟩ t t 1

/-- The fibre calculation once the two semisimple factors are represented
in the marked torus. The two original points need not lie in the torus. -/
def TorusRepresentativeFibres : Prop :=
  InvariantLaurentSeparation.{u,u,u} →
  ∀ {k J A : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val), GeometricRadicals.IsSplitTorus T.group →
    ∀ [IsCommMonObj T.group.X] {D : AbstractPairing.Datum T}
      (e : DatumAndWeyl.Identification D) (i : A ↪ Character T.group),
      (∀ x, ∃ a w, CharacterRing.weylAction e w x = i a) →
      (∀ a b, (∃ w, CharacterRing.weylAction e w (i a) = i b) ↔ a = b) →
      ∀ (V : J → CharacterRing.Rep G),
        Subring.closure (Set.range fun j => formalCharacter T (V j).action) =
          CharacterRing.invariantRing (CharacterRing.weylAction e) →
        ∀ {x y s r v u' : RationalPoints G.val},
          IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ x s v →
          IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ y r u' →
          ∀ (t t' : RationalPoints T.group) (h h' : RationalPoints G.val),
            h * s * h⁻¹ = pointHom T.inclusion t →
            h' * r * h'⁻¹ = pointHom T.inclusion t' →
            (∀ j, pointTrace (V j).action x = pointTrace (V j).action y) →
            ∃ g : RationalPoints G.val, g * s * g⁻¹ = r

/-- Scheme centralizers are tested on all families over the field. -/
def IsPointCentralizer {k : Type u} [Field k] {G : GroupScheme k}
    (C : ClosedSubgroup G) (y : 𝟙_ (SchemeOver k) ⟶ G.X) : Prop :=
  RepresentsSubgroup C (fun Y g => Commute g (toUnit Y ≫ y))

/-- A point whose semisimple factor is conjugate to an element with torus
scheme centralizer already lies in that conjugacy class. -/
def TorusCentralizerCollapse : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (C : ClosedSubgroup G.val) (y : 𝟙_ (SchemeOver k) ⟶ G.val.X),
    GeometricRadicals.IsTorus C.group → IsPointCentralizer C y →
    ∀ {x s v : RationalPoints G.val},
      IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ x s v →
      ∀ h : RationalPoints G.val,
        h * s * h⁻¹ = (toUnit ((testSpec k).obj (Opposite.op (CommAlgCat.of k k))) ≫ y :
          RationalPoints G.val) →
        h * x * h⁻¹ = (toUnit ((testSpec k).obj (Opposite.op (CommAlgCat.of k k))) ≫ y :
          RationalPoints G.val)

/-- The split-field rational module defines the same matrices on the
algebraically extended group via the base change of its point functor. -/
def RepresentationExtension : Prop :=
  ∀ {k K I : Type u} [Field k] [Field K] [Algebra k K] [Fintype I] [DecidableEq I]
    {G : GroupScheme k} (ρ : Representation G I),
    ∃ σ : Representation ((groupBaseChange k K).obj G) I,
      ∀ (R : TestAlgebra K) (g : AdjointRepresentation.GroupPoints
        ((groupBaseChange k K).obj G) R),
        (σ.app R g).val =
          (ρ.app ((restrictTestAlgebra k K).obj R) (baseChangePoint k K G.X R g)).val

open _root_.LinearAlgebraicGroups.RationalRepresentations
  (scalarExtension IsScalarExtension coefficients)
open SimpleClassification (SocleModel)
open Unipotent (closedSubgroupAlgebraicGroup)
open GeometricRadicals (IsUnipotentRadical)
open WithConv

/-- Scalar-extending a simple socle keeps its simplicity and highest line,
and its extended coefficient matrices give the split-field trace representation
on the actual extended scheme. -/
def SocleRepresentationExtension : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U →
    ∀ (χ : Character P.torus.group) (S : SocleModel P U χ),
    ∃ (σ : Representation ((groupBaseChange k K).obj G.val) S.J)
      (δ : RightComodule K (scalarExtension S.A K) (K ⊗[k] S.socle))
      (e : convolutionPoints (scalarExtension S.A K) ≅
        (groupPointsFunctor K).obj ((groupBaseChange k K).obj G.val)),
      IsScalarExtension S.A S.socleCoaction δ ∧
      (⊤ : Submodule K (K ⊗[k] S.socle)) ≠ ⊥ ∧
      (∀ M : Submodule K (K ⊗[k] S.socle), δ.IsSubcomodule M → M = ⊥ ∨ M = ⊤) ∧
      (∀ (R : TestAlgebra K) (g : AdjointRepresentation.GroupPoints
        ((groupBaseChange k K).obj G.val) R), (σ.app R g).val =
          (S.socleAction.app ((restrictTestAlgebra k K).obj R)
            (baseChangePoint k K G.val.X R g)).val) ∧
      (∀ (R : TestAlgebra K) (g : scalarExtension S.A K →ₐ[K] R),
        (σ.app R (e.hom.app R (toConv g))).val =
          g.mapMatrix (coefficients (scalarExtension S.A K) (S.socleBasis.baseChange K) δ)) ∧
      ∃ (C E : HopfAlgebraCategory k) (eU : specGroup C ≅ U.group)
        (eT : specGroup E ≅ P.torus.group) (qU : S.A ⟶ C) (qT : S.A ⟶ E)
        (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ E),
        specGroupMap qU ≫ S.groupIso.hom = eU.hom ≫ U.inclusion ≫ P.positive.inclusion ∧
        specGroupMap qT ≫ S.groupIso.hom = eT.hom ≫ P.torus.inclusion ∧
        specGroupMap φ = eT.hom ≫ χ ∧
        let v := (1 : K) ⊗ₜ[k] S.highestVector
        v ≠ 0 ∧
        let restr := fun {B : HopfAlgebraCategory k} (q : S.A ⟶ B) =>
          ((extendedHopfMap K q).hom.toAlgHom.toLinearMap.lTensor (K ⊗[k] S.socle)).comp
            δ.coaction
        {x | restr qU x = x ⊗ₜ[K] (1 : scalarExtension C K)} = (Submodule.span K {v} : Set _) ∧
        {x | restr qT x = x ⊗ₜ[K] ((1 : K) ⊗ₜ[k] FlagLineBundle.characterCoordinate φ)} =
          (Submodule.span K {v} : Set _)

/-- For an action on a proper scheme over an algebraically closed field, a
dense set of points admitting fixed flags forces every point to fix a flag. -/
def ProperFixedIncidence : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X), IsProper X.hom →
    Dense {z : G.X.left | ∃ (g : 𝟙_ (SchemeOver k) ⟶ G.X) (x : 𝟙_ (SchemeOver k) ⟶ X),
      g.left (IsLocalRing.closedPoint k) = z ∧ lift g x ≫ a.smul = x} →
    ∀ g : 𝟙_ (SchemeOver k) ⟶ G.X,
      ∃ x : 𝟙_ (SchemeOver k) ⟶ X, lift g x ≫ a.smul = x

/-- The geometric torality input required for arbitrary Jordan factors. -/
def SemisimpleTorusRepresentatives : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (P : OppositeBorelPair G) {x s v : RationalPoints G.val},
    IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ x s v →
    ∃ (h : RationalPoints G.val) (t : RationalPoints P.torus.group),
      h * s * h⁻¹ = pointHom P.torus.inclusion t

/-- The geometric fibre assertion on the actual fundamental simple modules.
The finite Weyl-orbit separation theorem is supplied independently. -/
def GeometricFibres : Prop :=
  InvariantLaurentSeparation.{u,u,u} →
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k) (P : OppositeBorelPair G),
    GeometricRadicals.IsSemisimple G → SimplyConnectedLattice.GeometricallySimplyConnected G →
    ∃ (comm : IsCommMonObj P.torus.group.X), letI := comm
    ∃ (D : AbstractPairing.Datum P.torus) (e : DatumAndWeyl.Identification D)
      (b : D.rootDatum.Base) (U : ClosedSubgroup P.positive.group),
      DominantOrder.IsBaseFor D.rootDatum (BorelsAndChambers.subgroupRoots P.torus P.positive) b ∧
      IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U ∧
      ∃ (ω : b.support → Character P.torus.group) (S : ∀ j, SocleModel P U (ω j)),
        (∀ i j, D.rootDatum.toLinearMap (Additive.ofMul (ω i)) (D.rootDatum.coroot j.val) =
          if i = j then 1 else 0) ∧
        Subring.closure (Set.range fun j => formalCharacter P.torus (S j).socleAction) =
          CharacterRing.invariantRing (CharacterRing.weylAction e) ∧
        ∀ {x y s r v u' : RationalPoints G.val},
          IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ x s v →
          IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ y r u' →
          (∀ i, pointTrace (S i).socleAction x = pointTrace (S i).socleAction y) →
          ∃ h : RationalPoints G.val, h * s * h⁻¹ = r ∧
            ∀ (C : ClosedSubgroup G.val) (y₀ : 𝟙_ (SchemeOver k) ⟶ G.val.X),
              GeometricRadicals.IsTorus C.group → IsPointCentralizer C y₀ →
              y = (toUnit ((testSpec k).obj (Opposite.op (CommAlgCat.of k k))) ≫ y₀ :
                RationalPoints G.val) →
              r = y → h * x * h⁻¹ = y

/-- The assembly identifies precisely the remaining geometric torality input. -/
def GeometricFibresFromTorusRepresentatives : Prop :=
  SemisimpleTorusRepresentatives.{u} → GeometricFibres.{u}

end
end LinearAlgebraicGroups.Specs.SteinbergGeometricFibres
