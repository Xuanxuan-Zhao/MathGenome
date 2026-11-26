import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatumTorusAndBorel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatumRankOneAndPinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralDerived

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Specs.SymplecticDatum

open SymplecticMatrixStructure (Indices PointGroup symplecticPoints mapSymplecticPoint)
open SymplecticDatumRankOneAndPinning (RootIndex determinantOnePoints upper lower diagonal)

noncomputable section

export SymplecticDatumAdjointDescent (MatrixAlgebra adjoint IsScalarMuTwo conjugateMatrix)

abbrev AdjointIdentities := SymplecticDatumAdjointDescent.AdjointIdentities.{u}

/-- The symplectic points identify naturally with the units satisfying the
adjoint isometry equation. -/
def IsometryGroupPoints : Prop :=
  ∀ (I : Type u) [Fintype I] [DecidableEq I],
    ∃ e : ∀ (R : Type u) [CommRing R], PointGroup I R →* (MatrixAlgebra I R)ˣ,
      (∀ (R : Type u) [CommRing R] (g : PointGroup I R), (e R g).val = g.val) ∧
      (∀ (R : Type u) [CommRing R], Function.Injective (e R)) ∧
      (∀ (R : Type u) [CommRing R] (g : (MatrixAlgebra I R)ˣ),
        adjoint g.val * g.val = 1 ↔ ∃ h, e R h = g) ∧
      ∀ (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) (g : PointGroup I R),
        Units.map f.mapMatrix.toMonoidHom (e R g) = e S (mapSymplecticPoint f g)

def ConjugationAction : Prop :=
  ∀ (I R : Type u) [Fintype I] [DecidableEq I] [CommRing R],
    ∃ c : PointGroup I R →* (MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R),
      (∀ g X, c g X = conjugateMatrix g X) ∧
      (∀ g X, c g (adjoint X) = adjoint (c g X)) ∧
      (∀ (S : Type u) [CommRing S] (f : R →+* S)
        (g : PointGroup I R) (X : MatrixAlgebra I R),
        (c g X).map f = conjugateMatrix (mapSymplecticPoint f g) (X.map f)) ∧
      (∀ (g h : PointGroup I R), c g h.val = (g * h * g⁻¹).val) ∧
      ∀ g, c g = 1 ↔ IsScalarMuTwo g.val

/-- Centrality after all changes of test ring computes the scheme centre,
including the points over rings with nilpotents. -/
def ScalarCentreOnPoints : Prop :=
  ∀ (I R : Type u) [Fintype I] [DecidableEq I] [Nonempty I] [CommRing R]
    (g : PointGroup I R),
    (∀ (S : Type u) [CommRing S] (f : R →+* S) (h : PointGroup I S),
      Commute (mapSymplecticPoint f g) h) ↔ IsScalarMuTwo g.val

/-- The scalar centre of the represented group, with its original inclusion. -/
def ScalarSchemeCentre : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I),
    ∃ Z : ClosedSubgroup G.val, CentralTorus.IsSchemeCentre Z ∧
      ∀ (R : TestAlgebra k) (g : (groupPointsFunctor k).obj G.val |>.obj R),
        (∃ z : (groupPointsFunctor k).obj Z.group |>.obj R,
          ((groupPointsFunctor k).map Z.inclusion).app R z = g) ↔
        IsScalarMuTwo (show PointGroup I R from c.hom.app R g).val

/-- On the hyperbolic plane the defining equation is the determinant equation
over every commutative ring, using the ordered hyperbolic basis. -/
def RankOneIdentification : Prop :=
  ∃ e : Indices (ULift.{u} Unit) ≃ Fin 2,
    e (Sum.inl ⟨()⟩) = 0 ∧ e (Sum.inr ⟨()⟩) = 1 ∧
    (∀ (R : Type u) [CommRing R] (g : MatrixAlgebra (ULift.{u} Unit) R),
      g ∈ Matrix.symplecticGroup (ULift.{u} Unit) R ↔ (Matrix.reindex e e g).det = 1) ∧
    ∀ (k : Type u) [Field k],
      ∃ t : symplecticPoints k (ULift.{u} Unit) ≅ determinantOnePoints k,
        (∀ (R : TestAlgebra k) (g : PointGroup (ULift.{u} Unit) R),
          (show Matrix.SpecialLinearGroup (Fin 2) R from t.hom.app R g).val =
            Matrix.reindex e e g.val) ∧
        ∀ (G S : AffineAlgebraicGroup k)
          (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k (ULift.{u} Unit))
          (s : (groupPointsFunctor k).obj S.val ≅ determinantOnePoints k),
          ∃ f : G.val ≅ S.val, (groupPointsFunctor k).map f.hom ≫ s.hom = c.hom ≫ t.hom

open SymplecticDatumTorusAndBorel
  (RootLabel coordinate sign rootVector simpleLabel HyperbolicIndex signedIndex
    elementaryDirection MatrixHasWeight)

def simpleCoroot {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) → ℤ :=
  coordinate i - if h : i.val < n then coordinate ⟨i.val + 1, by omega⟩ else 0

def SimpleCorootBasis : Prop :=
  ∀ n : ℕ, ∃ b : Module.Basis (Fin (n + 1)) ℤ (Fin (n + 1) → ℤ),
    ∀ i, b i = simpleCoroot i

def corootVector {n : ℕ} : RootLabel n → (Fin n → ℤ)
  | .long i s => sign s • coordinate i
  | .short i j _ s t => sign s • coordinate i + sign t • coordinate j

/-- The plane for a long root, or the ordered pair and its paired dual for a short root. -/
def rankOneIndex {n : ℕ} : RootLabel n → RootIndex (HyperbolicIndex.{u} n)
  | .long i s => .long (signedIndex i s)
  | .short i j h s t => .short (signedIndex i s) (signedIndex j (!t)) (by
      intro he
      apply h.ne
      have hi := congrArg ULift.down he
      cases s <;> cases t <;>
        exact hi)

/-- The lower transvection uses the reverse matrix unit. For short roots,
the companion entry is forced by preservation of the alternating pairing. -/
def oppositeDirection {n : ℕ} (R : Type u) [CommRing R] :
    RootLabel n → MatrixAlgebra (HyperbolicIndex.{u} n) R
  | .long i s => Matrix.single (signedIndex i (!s)) (signedIndex i s) 1
  | .short i j _ s t =>
    Matrix.single (signedIndex j (!t)) (signedIndex i s) 1 +
    Matrix.single (signedIndex i (!s)) (signedIndex j t) ((sign s * sign t : ℤ) : R)

open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue pairing adjointWeightVectors)
open StandardGroups (multiplicativePowerPoints)
open AbstractPairing (Root)
open Pinning (AttachedDatum Pinning SplitBorelPair)
open RootGroups (AdditiveLine rootPoint)
open OrderedRootProducts (RootSubgroupFamily)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition cocharacterPoint)
open scoped BigOperators

/-- The coordinates, based datum, and pinning with their explicit values on
the actual represented symplectic group. Rank one is the case `n = 0`. -/
def BasedComputation : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k (HyperbolicIndex.{u} (n + 1))),
    ∃ (P : SplitBorelPair k) (eG : P.G = G),
      let cP : (groupPointsFunctor k).obj P.G.val ≅
          symplecticPoints k (HyperbolicIndex.{u} (n + 1)) := eG.symm ▸ c
      ∃ (d : (groupPointsFunctor k).obj P.T.group ≅
          multiplicativePowerPoints k (HyperbolicIndex.{u} (n + 1)))
        (D : AttachedDatum P),
        letI := D.comm
        ∃ (X : Additive (Character P.T.group) ≃ₗ[ℤ] (Fin (n + 1) → ℤ))
          (Y : Additive (Cocharacter P.T.group) ≃ₗ[ℤ] (Fin (n + 1) → ℤ))
          (label : RootLabel (n + 1) ≃ Root P.T)
          (cochar : Cocharacter P.T.group) (dyn : LimitDecomposition (cochar ≫ P.T.inclusion))
          (A : AdditiveLine k) (U : RootSubgroupFamily P.T) (pin : Pinning A P U)
          (S : AffineAlgebraicGroup k)
          (s : (groupPointsFunctor k).obj S.val ≅ determinantOnePoints k)
          (rankOne : RootLabel (n + 1) → (S.val ⟶ P.G.val))
          (e : Lie k P.G.val ≃+ SymplecticMatrixStructure.symplecticLieSubspace k
            (HyperbolicIndex.{u} (n + 1)))
          (b : Module.Basis (Fin (n + 1)) ℤ (Additive (Cocharacter P.T.group))),
          let eval (a : RootLabel (n + 1)) (R : TestAlgebra k)
              (m : Matrix.SpecialLinearGroup (Fin 2) R) :=
            ((groupPointsFunctor k).map (rankOne a)).app R (s.inv.app R m)
          (∀ (R : TestAlgebra k) (t : HyperbolicIndex.{u} (n + 1) → Rˣ),
            (show PointGroup _ R from cP.hom.app R
              (((groupPointsFunctor k).map P.T.inclusion).app R (d.inv.app R t))).val =
                SymplecticMatrixStructure.hyperbolicDiagonal t) ∧
          (∀ (R : TestAlgebra k) (t : HyperbolicIndex.{u} (n + 1) → Rˣ)
            (χ : Character P.T.group),
            characterValue χ R (d.inv.app R t) =
              (↑(∏ i : Fin (n + 1), t ⟨i⟩ ^ X (Additive.ofMul χ) i) : R)) ∧
          (∀ (R : TestAlgebra k) (r : Rˣ) (y : Cocharacter P.T.group)
            (i : Fin (n + 1)), (d.hom.app R (cocharacterPoint y R r) :
              HyperbolicIndex.{u} (n + 1) → Rˣ) ⟨i⟩ = r ^ Y (Additive.ofMul y) i) ∧
          (∀ x y, pairing P.T.group x y =
            ∑ i : Fin (n + 1), X (Additive.ofMul x) i * Y (Additive.ofMul y) i) ∧
          (∀ p i j, (e p).val i j =
            ((show PointGroup _ (DualNumber k) from
              cP.hom.app (CommAlgCat.of k (DualNumber k)) p.toMul.val).val i j).snd) ∧
          (∀ χ v, v ∈ adjointWeightVectors P.T χ ↔
            MatrixHasWeight (X (Additive.ofMul χ)) (e v).val) ∧
          (∀ a, ∃ v ∈ adjointWeightVectors P.T (label a).val,
            v ≠ 0 ∧ (e v).val = elementaryDirection k a) ∧
          (∀ a, X (D.datum.rootDatum.root (label a)) = rootVector a ∧
            Y (D.datum.rootDatum.coroot (label a)) = corootVector a) ∧
          (∀ i, Y (Additive.ofMul cochar) i = (n + 1 : ℤ) - i.val) ∧
          IsRegular P.T cochar ∧ RankOneFlag.SameSubgroup P.B dyn.parabolic ∧
          subgroupRoots P.T P.B = positiveRoots P.T cochar ∧
          (∀ a, label a ∈ D.base.support ↔ ∃ i, a = simpleLabel i) ∧
          (∀ i, b i = D.datum.rootDatum.coroot (label (simpleLabel i)) ∧
            Y (b i) = simpleCoroot i) ∧
          (∀ i : Pinning.SimpleRoot P, ∀ (R : TestAlgebra k) (r : R),
            rootPoint ((pin i).val.hom ≫ (U i.val).val.inclusion) R r =
              eval (label.symm i.val) R (upper r)) ∧
          (∀ a (R : TestAlgebra k) (g : Matrix.SpecialLinearGroup (Fin 2) R),
            (show PointGroup _ R from cP.hom.app R (eval a R g)).val = (rankOneIndex a).matrix g) ∧
          (∀ a (R : TestAlgebra k) (r : R),
            (show PointGroup _ R from cP.hom.app R (eval a R (upper r))).val =
              1 + r • elementaryDirection R a ∧
            (show PointGroup _ R from cP.hom.app R (eval a R (lower r))).val =
              1 + r • oppositeDirection R a) ∧
          (∀ a (R : TestAlgebra k) (z : Rˣ),
            eval a R (diagonal z) =
              cocharacterPoint (Additive.toMul (D.datum.rootDatum.coroot (label a))) R z ≫
                P.T.inclusion.hom.hom) ∧
          GeometricRadicals.IsSemisimple G ∧ SimplyConnectedLattice.GeometricallySimplyConnected G

open SchemeDerivedGroup (RepresentsQuotient)

/-- The fppf quotient by the scalar scheme centre acts on the split algebra
with involution and on the represented isometry group. -/
def AdjointQuotientAction : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I),
    ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      CentralTorus.IsSchemeCentre Z ∧ SymplecticDatumAdjointDescent.ScalarCentre c Z ∧
      IsSchemeKernel q Z ∧ RepresentsQuotient Z q ∧
      (∀ (R : TestAlgebra k) (a : ((groupPointsFunctor k).obj Q.val).obj R),
        ∃ (S : TestAlgebra k) (f : R ⟶ S) (g : ((groupPointsFunctor k).obj G.val).obj S),
          f.hom.toRingHom.FaithfullyFlat ∧ f.hom.toRingHom.FinitePresentation ∧
          ((groupPointsFunctor k).map q).app S g =
            ((groupPointsFunctor k).obj Q.val).map f a) ∧
      ∃ (action : ∀ R : TestAlgebra k, ((groupPointsFunctor k).obj Q.val).obj R →*
          (MatrixAlgebra I R ≃ₐ[R] MatrixAlgebra I R))
        (isometryAction : ∀ R : TestAlgebra k, ((groupPointsFunctor k).obj Q.val).obj R →*
          MulAut (PointGroup I R)),
        (∀ R, Function.Injective (action R)) ∧
        (∀ (R : TestAlgebra k) (a : ((groupPointsFunctor k).obj Q.val).obj R) X,
          action R a (adjoint X) = adjoint (action R a X)) ∧
        (∀ (R S : TestAlgebra k) (f : R ⟶ S)
          (a : ((groupPointsFunctor k).obj Q.val).obj R) X,
          (action R a X).map f.hom = action S
            (((groupPointsFunctor k).obj Q.val).map f a) (X.map f.hom)) ∧
        (∀ (R : TestAlgebra k) (g : ((groupPointsFunctor k).obj G.val).obj R) X,
          action R (((groupPointsFunctor k).map q).app R g) X =
            conjugateMatrix (c.hom.app R g) X) ∧
        (∀ (R : TestAlgebra k) (a : ((groupPointsFunctor k).obj Q.val).obj R)
          (h : PointGroup I R), (isometryAction R a h).val = action R a h.val) ∧
        (∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : ((groupPointsFunctor k).obj Q.val).obj R)
          (h : PointGroup I R),
          mapSymplecticPoint f.hom.toRingHom (isometryAction R a h) =
            isometryAction S (((groupPointsFunctor k).obj Q.val).map f a)
              (mapSymplecticPoint f.hom.toRingHom h)) ∧
        ∀ (R S : TestAlgebra k) (f : R ⟶ S) (a : ((groupPointsFunctor k).obj Q.val).obj R)
          (g : ((groupPointsFunctor k).obj G.val).obj S) (h : PointGroup I R),
          ((groupPointsFunctor k).map q).app S g =
            ((groupPointsFunctor k).obj Q.val).map f a →
          mapSymplecticPoint f.hom.toRingHom (isometryAction R a h) =
            (show PointGroup I S from c.hom.app S g) * mapSymplecticPoint f.hom.toRingHom h *
              (show PointGroup I S from c.hom.app S g)⁻¹

abbrev MatrixWeightEntries := SymplecticDatumTorusAndBorel.MatrixWeightEntries.{u}
abbrev MatrixLieWeights := SymplecticDatumTorusAndBorel.MatrixLieWeights.{u}
abbrev MatrixScalarExtension := SymplecticDatumAdjointDescent.MatrixScalarExtension.{u}

/-- The coordinate Hopf algebra is the group algebra of the cyclic group
of order two, with no restriction on the characteristic of the field. -/
abbrev muTwo (k : Type u) [Field k] : AffineAlgebraicGroup k :=
  DiagonalizableGroups.diagonalGroup k (ULift.{u} (Multiplicative (ZMod 2)))

def CentreIsMuTwo : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] [Nonempty I]
    (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅ symplecticPoints k I),
    ∃ (Z : ClosedSubgroup G.val) (e : (muTwo k).val ≅ Z.group)
      (d : (groupPointsFunctor k).obj (muTwo k).val ≅ DiagonalizableGroups.rootsOfUnityPoints k 2),
      CentralTorus.IsSchemeCentre Z ∧ IsFinite Z.group.X.hom ∧
      ∀ (R : TestAlgebra k) (a : rootsOfUnity 2 R),
        (show PointGroup I R from c.hom.app R
          (((groupPointsFunctor k).map (e.hom ≫ Z.inclusion)).app R (d.inv.app R a))).val =
            Matrix.scalar (Indices I) (a.val : R)

end

end LinearAlgebraicGroups.Specs.SymplecticDatum
