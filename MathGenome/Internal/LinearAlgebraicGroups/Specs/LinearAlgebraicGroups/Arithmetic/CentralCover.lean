import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CentralCoverDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Specs.CentralCover

open CentralIsogenies (IsCentralIsogeny IsTorusRestriction characterPullback)
open CharacterDescent (Character)
open DiagonalizableGroups (groupAlgebra splitProductPoints)
open GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsTrivialSubgroup)
open RankOneFlag (IsGeometricallyMaximal)

noncomputable section

/-- A homomorphism from a reduced connected group to a finite group
scheme is trivial. The target need not be reduced. -/
def FiniteTargetRigidity : Prop :=
  ∀ {k : Type u} [Field k] (G H : GroupScheme k),
    IsReduced G.X.left → ConnectedSpace G.X.left → IsFinite H.X.hom →
    ∀ (f : G.X ⟶ H.X), η[G.X] ≫ f = η[H.X] → f = 1

/-- There is at most one lift through an isogeny of a morphism from a
reduced connected group. -/
def UniqueLift : Prop :=
  ∀ {k : Type u} [Field k] (G H J : GroupScheme k),
    IsReduced G.X.left → ConnectedSpace G.X.left →
    ∀ (q : H ⟶ J), IsCentralIsogeny q →
    ∀ (a b : G ⟶ H), a ≫ q = b ≫ q → a = b

/-- For a central isogeny restricting to an isogeny between split maximal
tori, the full scheme kernel is diagonalizable with the indicated
cokernel of the actual character map. -/
def SplitKernelCharacters : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k),
    IsReductive G → IsReductive H →
    ∀ (T : ClosedSubgroup G.val) (S : ClosedSubgroup H.val),
      IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∀ (q : G.val ⟶ H.val) (qT : T.group ⟶ S.group),
        IsCentralIsogeny q → IsTorusRestriction q qT →
        ∀ (N : ClosedSubgroup G.val), IsSchemeKernel q N →
          let l := characterPullback qT
          let M := Character T.group ⧸ l.range
          Function.Injective l ∧ Finite M ∧
            Nonempty (N.group ≅ specGroup (groupAlgebra k M))

/-- For the kernel of a group map over a field, the standard right-translation
map realizes the relation of lying over the same point of the target. -/
def KernelTorsorSquare : Prop :=
  ∀ {k : Type u} [Field k] {G H : GroupScheme k}
    (q : G ⟶ H) (N : ClosedSubgroup G),
    IsSchemeKernel q N →
    IsPullback (fst G.X N.group.X)
      (fst G.X N.group.X * (snd G.X N.group.X ≫ N.inclusion.hom.hom))
      q.hom.hom q.hom.hom

open SimplyConnectedLattice (GeometricallySimplyConnected)
open Unipotent (baseChangedAlgebraicGroup)
open SchemeDerivedGroup (RepresentsQuotient)
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open IntegralCentralQuotient (OverBase fibreGroup HopfSpectrum spectrumOfHopfHom)

variable {k : Type u} [Field k]

/-- The cover and its target have a common quotient by their full scheme centres. -/
def SameAdjointQuotient {G H : AffineAlgebraicGroup k} (q : H.val ⟶ G.val) : Prop :=
  ∃ (Z : ClosedSubgroup H.val) (W : ClosedSubgroup G.val)
      (Q : AffineAlgebraicGroup k) (p : G.val ⟶ Q.val),
    RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 H.val) z) ∧
    RepresentsSubgroup W (fun _ w => Centralizes (𝟙 G.val) w) ∧
    RepresentsQuotient Z (q ≫ p) ∧ RepresentsQuotient W p

/-- A central isogeny between split semisimple groups induces a common
quotient by the respective full scheme centres. -/
def SplitSameAdjointQuotient : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k),
    IsSemisimple G → IsSemisimple H →
    ∀ (T : ClosedSubgroup H.val) (S : ClosedSubgroup G.val),
      IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∀ (q : H.val ⟶ G.val) (qT : T.group ⟶ S.group),
        IsCentralIsogeny q → IsTorusRestriction q qT → SameAdjointQuotient q

/-- A central isogeny from a geometrically simply connected semisimple
group has trivial scheme kernel precisely when its target is
geometrically simply connected. -/
def TrivialKernelIffSimplyConnected : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k),
    IsSemisimple H → GeometricallySimplyConnected H →
    ∀ (q : H.val ⟶ G.val) (N : ClosedSubgroup H.val),
      IsCentralIsogeny q → IsSchemeKernel q N →
      (IsTrivialSubgroup N ↔ GeometricallySimplyConnected G)

/-- The common adjoint quotient descends when the isogeny admits a split
maximal torus restriction after scalar extension. -/
def SameAdjointQuotientAfterSplitting : Prop :=
  ∀ {k E : Type u} [Field k] [Field E] [Algebra k E]
    (G H : AffineAlgebraicGroup k) (q : H.val ⟶ G.val),
    IsCentralIsogeny q →
    let G' := baseChangedAlgebraicGroup E G
    let H' := baseChangedAlgebraicGroup E H
    IsSemisimple G' → IsSemisimple H' →
    ∀ (T : ClosedSubgroup H'.val) (S : ClosedSubgroup G'.val),
      IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∀ qT : T.group ⟶ S.group,
        IsTorusRestriction ((groupBaseChange k E).map q) qT → SameAdjointQuotient q

/-- The kernel is finite and becomes a finite diagonalizable group over a
finite Galois extension. -/
def IsFiniteMultiplicativeType (N : GroupScheme k) : Prop :=
  IsFinite N.X.hom ∧
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E)
      (_ : IsGalois k E) (M : Type u) (_ : CommGroup M) (_ : Finite M),
      Nonempty ((groupBaseChange k E).obj N ≅ specGroup (groupAlgebra E M))

/-- Point-functor coordinates of a split torus in an integral basis of
its characters. -/
def torusCoordinates (I : Type) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (I → Rˣ)
  map a := GrpCat.ofHom (MonoidHom.pi fun i =>
    (Units.map a.hom.toMonoidHom).comp (Pi.evalMonoidHom _ i))
  map_id _ := by apply GrpCat.ext; intro x; ext; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext; rfl

/-- The diagonal map on the two split tori has the same positive
integers as the roots-of-unity factors in its full scheme kernel. -/
def HasPowerCoordinates {T S : GroupScheme k} (q : T ⟶ S)
    {I : Type} (n : I → ℕ) : Prop :=
  ∃ (eT : (groupPointsFunctor k).obj T ≅ torusCoordinates (k := k) I)
    (eS : (groupPointsFunctor k).obj S ≅ torusCoordinates (k := k) I),
    ∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj T).obj R) (i : I),
      (show I → Rˣ from eS.hom.app R (((groupPointsFunctor k).map q).app R x)) i =
        (show I → Rˣ from eT.hom.app R x) i ^ n i

/-- A cover together with its split torus isogeny and the finite central
kernel in the coordinates of that isogeny. -/
structure SplitCoverData (G H : AffineAlgebraicGroup k) (q : H.val ⟶ G.val)
    (N : ClosedSubgroup H.val) where
  sourceTorus : ClosedSubgroup H.val
  targetTorus : ClosedSubgroup G.val
  sourceSplit : IsSplitTorus sourceTorus.group
  targetSplit : IsSplitTorus targetTorus.group
  sourceMaximal : IsGeometricallyMaximal sourceTorus
  targetMaximal : IsGeometricallyMaximal targetTorus
  restriction : sourceTorus.group ⟶ targetTorus.group
  restricts : IsTorusRestriction q restriction
  kernelTorusInclusion : N.group ⟶ sourceTorus.group
  kernelInTorus : kernelTorusInclusion ≫ sourceTorus.inclusion = N.inclusion
  torusKernel : IsPullback kernelTorusInclusion.hom.hom (toUnit N.group.X)
    restriction.hom.hom η[targetTorus.group.X]
  indices : Type
  finiteIndices : Fintype indices
  exponents : indices → ℕ
  positiveExponents : ∀ i, 0 < exponents i
  powerCoordinates : HasPowerCoordinates restriction exponents
  kernelFactors : Nonempty ((groupPointsFunctor k).obj N.group ≅
    splitProductPoints k PEmpty indices exponents)
  nontrivialFactors : (¬ IsTrivialSubgroup N) ↔ ∃ i, 1 < exponents i

/-- Smith coordinates and the roots-of-unity kernel for a given split
central isogeny carrying a maximal torus onto a maximal torus. -/
def SplitCoverDataExists : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k),
    IsReductive G → IsReductive H →
    ∀ (T : ClosedSubgroup H.val) (S : ClosedSubgroup G.val),
      IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∀ (q : H.val ⟶ G.val) (qT : T.group ⟶ S.group),
        IsCentralIsogeny q → IsTorusRestriction q qT →
        ∀ (N : ClosedSubgroup H.val), IsSchemeKernel q N →
          Nonempty (SplitCoverData G H q N)

/-- The original semisimple group has a split simply connected cover after
a finite Galois scalar extension. -/
def SplitCoverAfterFiniteGaloisExtension : Prop :=
  ∀ {K : Type u} [Field K] (G : AffineAlgebraicGroup K), IsSemisimple G →
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E)
      (_ : IsGalois K E),
      let G' := baseChangedAlgebraicGroup E G
      ∃ (H : AffineAlgebraicGroup E) (q : H.val ⟶ G'.val) (N : ClosedSubgroup H.val),
        IsSemisimple G' ∧ IsSemisimple H ∧ GeometricallySimplyConnected H ∧
          IsCentralIsogeny q ∧ IsSchemeKernel q N ∧ Nonempty (SplitCoverData G' H q N)

/-- The descent step for a prescribed finite Galois field that splits a
maximal torus of the target. -/
abbrev CoverDescent : Prop := CentralCoverDescent.CoverDescent.{u}

/-- The arithmetic cover statement holds for all connected semisimple groups,
so in particular for connected absolutely almost simple groups. -/
def CoverExists : Prop :=
  ∀ {K : Type u} [Field K] (G : AffineAlgebraicGroup K), IsSemisimple G →
    ∃ (H : AffineAlgebraicGroup K) (q : H.val ⟶ G.val) (N : ClosedSubgroup H.val),
      IsSemisimple H ∧ GeometricallySimplyConnected H ∧ IsCentralIsogeny q ∧
      IsSchemeKernel q N ∧ IsFiniteMultiplicativeType N.group ∧
      SameAdjointQuotient q ∧ (IsTrivialSubgroup N ↔ GeometricallySimplyConnected G) ∧
      ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E)
        (_ : IsGalois K E),
        let G' := baseChangedAlgebraicGroup E G
        let H' := baseChangedAlgebraicGroup E H
        let q' := (groupBaseChange K E).map q
        ∃ hc : IsClosedImmersion ((groupBaseChange K E).map N.inclusion).hom.hom.left,
          let N' : ClosedSubgroup H'.val := ⟨_, (groupBaseChange K E).map N.inclusion, hc⟩
          IsSemisimple G' ∧ IsSemisimple H' ∧ IsCentralIsogeny q' ∧
            IsSchemeKernel q' N' ∧ Nonempty (SplitCoverData G' H' q' N')

/-- A finite separable extension of a global field is again a global field. -/
def GlobalFieldExtension : Prop :=
  ∀ {K E : Type u} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E], GlobalFieldData.{u, v} K → Nonempty (GlobalFieldData.{u, v} E)

/-- Elements integral at every finite place of the global field outside the
specified exceptional set. -/
def integersOutside {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E)
    (S : Set D.FinitePlace) : Subring E :=
  ⨅ w : {w : D.FinitePlace // w ∉ S},
    (D.integers w).toSubring.comap (D.embedding (.inl w.val))

/-- The ring of integers of the number field, or the normalization for the
separating parameter, is contained in the integers outside a finite set. -/
def DedekindIntegralBase : Prop :=
  ∀ {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E) (B : Set D.FinitePlace),
    B.Finite →
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDedekindDomain A)
      (_ : Algebra A E) (_ : IsFractionRing A E) (S : Set D.FinitePlace),
        S.Finite ∧ B ⊆ S ∧ ∀ a : A, algebraMap A E a ∈ integersOutside D S

/-- After removing the poles of the separating parameter when necessary,
each ring of integers outside the exceptional set has the original fraction field. -/
def IntegersOutsideFractionRing : Prop :=
  ∀ {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E) (B : Set D.FinitePlace),
    B.Finite →
    ∃ S : Set D.FinitePlace, S.Finite ∧ B ⊆ S ∧
      ∀ T : Set D.FinitePlace, S ⊆ T → IsFractionRing (integersOutside D T) E

/-- A finite list of field coefficients can be made integral simultaneously,
including inverses of nonzero coefficients when needed. -/
def FiniteCoefficientsIntegral : Prop :=
  ∀ {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E)
      (B : Set D.FinitePlace) (C : Set E),
    B.Finite → C.Finite →
    ∃ S : Set D.FinitePlace, S.Finite ∧ B ⊆ S ∧
      C ⊆ (integersOutside D S : Set E)

/-- A principal localization of the given ring of integers maps into
the integers outside a finite enlargement, compatibly with its fraction field. -/
def IntegralLocalization : Prop :=
  ∀ {A E : Type u} [CommRing A] [Field E] [Algebra A E] [IsFractionRing A E]
    (D : GlobalFieldData.{u, v} E) (B : Set D.FinitePlace),
    B.Finite → (∀ a : A, algebraMap A E a ∈ integersOutside D B) →
    ∀ (d : A) [Algebra (Localization.Away d) E] [IsScalarTower A (Localization.Away d) E],
      d ≠ 0 →
      ∃ S : Set D.FinitePlace, S.Finite ∧ B ⊆ S ∧
        ∃ f : Localization.Away d →+* integersOutside D S,
          (integersOutside D S).subtype.comp f = algebraMap (Localization.Away d) E

/-- The character map is a diagonal positive integral matrix in split
character bases. Factor orders equal the diagonal coefficients. -/
def CharacterSmithBases : Prop :=
  ∀ {k : Type u} [Field k] {T S : GroupScheme k} (q : T ⟶ S),
    IsSplitTorus T → Function.Injective (characterPullback q) →
    Finite (Character T ⧸ (characterPullback q).range) →
    ∃ (r : ℕ) (bT : Module.Basis (Fin r) ℤ (Additive (Character T)))
      (bS : Module.Basis (Fin r) ℤ (Additive (Character S))) (n : Fin r → ℕ),
      (∀ i, 0 < n i) ∧
      ∀ i, Additive.ofMul (characterPullback q (bS i).toMul) = (n i : ℤ) • bT i

/-- A finite-index isogeny of split tori acts by coordinatewise positive
powers after changing the two integral bases. -/
def SplitTorusPowerCoordinates : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k),
    IsReductive G → IsReductive H →
    ∀ (T : ClosedSubgroup G.val) (S : ClosedSubgroup H.val),
      IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsSplitTorus S.group → IsGeometricallyMaximal S →
      ∀ (q : G.val ⟶ H.val) (qT : T.group ⟶ S.group),
        IsCentralIsogeny q → IsTorusRestriction q qT →
        ∃ (r : ℕ) (n : Fin r → ℕ), (∀ i, 0 < n i) ∧ HasPowerCoordinates qT n

/-- The matrix coordinate ring with the determinant inverted over an arbitrary
commutative base. -/
def matrixDeterminant (R : Type u) [CommRing R] (m : ℕ) :
    MvPolynomial (ULift.{u} (Fin m) × ULift.{u} (Fin m)) R :=
  Matrix.det (Matrix.of fun i j => MvPolynomial.X (i, j))

abbrev matrixCoordinates (R : Type u) [CommRing R] (m : ℕ) :=
  Localization.Away (matrixDeterminant R m)

/-- The usual extension of scalars on the matrix entries and inverse determinant. -/
def matrixCoordinateMap (R E : Type u) [CommRing R] [CommRing E] [Algebra R E] (m : ℕ) :
    matrixCoordinates R m →+* matrixCoordinates E m := by
  let f := MvPolynomial.map (algebraMap R E)
      (σ := ULift.{u} (Fin m) × ULift.{u} (Fin m))
  have h : f (matrixDeterminant R m) = matrixDeterminant E m := by
    unfold matrixDeterminant
    refine (f.map_det _).trans (congrArg Matrix.det ?_)
    exact Matrix.ext (fun i j => MvPolynomial.map_X (algebraMap R E) (i, j))
  letI : IsLocalization.Away (f (matrixDeterminant R m)) (matrixCoordinates E m) :=
    h.symm ▸ inferInstanceAs (IsLocalization.Away (matrixDeterminant E m) _)
  exact IsLocalization.Away.map _ _ f (matrixDeterminant R m)

/-- The chosen faithful matrix realization, with the usual evaluation on
each test algebra. -/
structure MatrixRealization (G : AffineAlgebraicGroup k) where
  size : ℕ
  operations : StandardGroups.HopfOperations k
    (StandardGroups.GLCoordinates k (ULift.{u} (Fin size)))
  represents :
    letI := operations.hopf
    StandardGroups.Represents _ (StandardGroups.generalLinearPoints k (ULift.{u} (Fin size)))
      (fun _ f M => M.val = f.mapMatrix (StandardGroups.universalMatrix k _))
  inclusion :
    letI := operations.hopf
    G.val ⟶ HopfSpectrum k (StandardGroups.GLCoordinates k (ULift.{u} (Fin size)))
  closed : IsClosedImmersion inclusion.hom.hom.left

/-- The determinant-localized matrix scheme, over its coefficient ring. -/
abbrev matrixScheme (R : Type u) [CommRing R] (m : ℕ) : OverBase R :=
  (algSpec (CommRingCat.of R)).obj (Opposite.op (CommAlgCat.of R (matrixCoordinates R m)))

/-- The underlying closed immersion of a chosen matrix realization. -/
structure MatrixEmbedding (G : AffineAlgebraicGroup k) (m : ℕ) where
  inclusion : G.val.X ⟶ matrixScheme k m
  closed : IsClosedImmersion inclusion.left

def MatrixRealization.toEmbedding {G : AffineAlgebraicGroup k} (i : MatrixRealization G) :
    MatrixEmbedding G i.size :=
  ⟨i.inclusion.hom.hom, i.closed⟩

/-- Scalar extension of the chosen closed matrix embedding preserves its entries,
including the inverse determinant. -/
def MatrixEmbeddingScalarExtension : Prop :=
  ∀ {k E : Type u} [Field k] [Field E] [Algebra k E] {G : AffineAlgebraicGroup k}
    {m : ℕ} (i : MatrixEmbedding G m),
    ∃ j : MatrixEmbedding (baseChangedAlgebraicGroup E G) m,
      j.inclusion.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap k E m)) =
        pullback.fst G.val.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))) ≫ i.inclusion.left

abbrev AffineModel (R : Type u) [CommRing R] :=
  {G : Grp (OverBase R) // IsAffine G.X.left ∧ LocallyOfFinitePresentation G.X.hom}

variable {R : Type u} [CommRing R]

/-- A group whose projection is a finite faithfully flat torsor under the
specified closed kernel, with the action given by right multiplication. -/
structure FiniteKernelTorsor {G H : Grp (OverBase R)} (q : H ⟶ G)
    {Z : Grp (OverBase R)} (j : Z ⟶ H) : Prop where
  finite : IsFinite q.hom.hom.left
  flat : Flat q.hom.hom.left
  surjective : Surjective q.hom.hom.left
  finitePresentation : LocallyOfFinitePresentation q.hom.hom.left
  closed : IsClosedImmersion j.hom.hom.left
  kernel : IsPullback j.hom.hom (toUnit Z.X) q.hom.hom η[G.X]
  torsor : IsPullback (fst H.X Z.X)
    (fst H.X Z.X * (snd H.X Z.X ≫ j.hom.hom)) q.hom.hom q.hom.hom

/-- The full scheme kernel gives the finite flat torsor for a finite
faithfully flat homomorphism of finite presentation over a ring. -/
def FiniteKernelTorsorOfKernel : Prop :=
  ∀ {R : Type u} [CommRing R] {G H Z : Grp (OverBase R)}
    (q : H ⟶ G) (j : Z ⟶ H),
    IsFinite q.hom.hom.left → Flat q.hom.hom.left → Surjective q.hom.hom.left →
    LocallyOfFinitePresentation q.hom.hom.left → IsClosedImmersion j.hom.hom.left →
    IsPullback j.hom.hom (toUnit Z.X) q.hom.hom η[G.X] → FiniteKernelTorsor q j

/-- The generic fibre of a flat model over a domain is schematically dense in the
model in the sense that every map out of the model has the same image ideal
after restriction to its generic fibre. -/
def GenericFibreImage : Prop :=
  ∀ {R E : Type u} [CommRing R] [IsDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)), Flat f → ∀ j : X ⟶ Y,
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R E))) ≫ j).ker = j.ker

/-- The character pullback for a product of positive power maps. -/
def powerOnCharacters {I : Type} (n : I → ℕ) :
    Multiplicative (I → ℤ) →* Multiplicative (I → ℤ) where
  toFun c := Multiplicative.ofAdd fun i => (n i : ℤ) * c.toAdd i
  map_one' := congrArg Multiplicative.ofAdd (funext fun i => mul_zero (n i : ℤ))
  map_mul' c d := congrArg Multiplicative.ofAdd (funext fun i => mul_add (n i : ℤ) (c.toAdd i) (d.toAdd i))

abbrev integralSplitTorus (R : Type u) [CommRing R] (I : Type) :=
  HopfSpectrum R (MonoidAlgebra R (ULift.{u} (Multiplicative (I → ℤ))))

abbrev powerOnLiftedCharacters {I : Type} (n : I → ℕ) :
    ULift.{u} (Multiplicative (I → ℤ)) →* ULift.{u} (Multiplicative (I → ℤ)) :=
  MulEquiv.ulift.symm.toMonoidHom.comp ((powerOnCharacters n).comp MulEquiv.ulift.toMonoidHom)

abbrev integralPowerMap (R : Type u) [CommRing R] {I : Type} (n : I → ℕ) :
    integralSplitTorus R I ⟶ integralSplitTorus R I :=
  spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom R (powerOnLiftedCharacters n))

abbrev integralRootsOfUnityProduct (R : Type u) [CommRing R] {I : Type} (n : I → ℕ) :=
  HopfSpectrum R (MonoidAlgebra R (ULift.{u} (∀ i, Multiplicative (ZMod (n i)))))

/-- The power coordinates and the product of roots of unity, as
isomorphisms of group schemes over the splitting field. -/
def SplitCoverSchemeCoordinates : Prop :=
  ∀ {k : Type u} [Field k] {G H : AffineAlgebraicGroup k} {q : H.val ⟶ G.val}
    {N : ClosedSubgroup H.val} (T : SplitCoverData G H q N),
    ∃ (eT : T.sourceTorus.group ≅ integralSplitTorus k T.indices)
      (eS : T.targetTorus.group ≅ integralSplitTorus k T.indices),
      T.restriction ≫ eS.hom = eT.hom ≫ integralPowerMap k T.exponents ∧
        Nonempty (N.group ≅ integralRootsOfUnityProduct k T.exponents)

/-- Integral models with the original isogeny, closed torus embeddings and
kernel as their generic fibres. The target is the closure in the chosen
matrix realization. -/
structure IntegralModel {E : Type u} [Field E] [Algebra R E]
    {G H : AffineAlgebraicGroup E} {q : H.val ⟶ G.val} {N : ClosedSubgroup H.val}
    (T : SplitCoverData G H q N) {m : ℕ} (i : MatrixEmbedding G m) where
  target : AffineModel R
  targetFlat : Flat target.val.X.hom
  source : AffineModel R
  kernel : AffineModel R
  kernelFinite : IsFinite kernel.val.X.hom
  kernelFlat : Flat kernel.val.X.hom
  sourceTorus : AffineModel R
  targetTorus : AffineModel R
  map : source.val ⟶ target.val
  kernelInclusion : kernel.val ⟶ source.val
  sourceTorusInclusion : sourceTorus.val ⟶ source.val
  targetTorusInclusion : targetTorus.val ⟶ target.val
  torusMap : sourceTorus.val ⟶ targetTorus.val
  torsor : FiniteKernelTorsor map kernelInclusion
  kernelCentral : Commute (fst source.val.X kernel.val.X)
    (snd source.val.X kernel.val.X ≫ kernelInclusion.hom.hom)
  sourceTorusClosed : IsClosedImmersion sourceTorusInclusion.hom.hom.left
  targetTorusClosed : IsClosedImmersion targetTorusInclusion.hom.hom.left
  torusCompatibility : sourceTorusInclusion ≫ map = torusMap ≫ targetTorusInclusion
  splitSourceTorus : sourceTorus.val ≅ integralSplitTorus R T.indices
  splitTargetTorus : targetTorus.val ≅ integralSplitTorus R T.indices
  splitTorusMap : torusMap ≫ splitTargetTorus.hom =
    splitSourceTorus.hom ≫ integralPowerMap R T.exponents
  splitKernel : kernel.val ≅ integralRootsOfUnityProduct R T.exponents
  genericTarget : (fibreGroup E).obj target.val ≅ G.val
  genericSource : (fibreGroup E).obj source.val ≅ H.val
  genericKernel : (fibreGroup E).obj kernel.val ≅ N.group
  genericSourceTorus : (fibreGroup E).obj sourceTorus.val ≅ T.sourceTorus.group
  genericTargetTorus : (fibreGroup E).obj targetTorus.val ≅ T.targetTorus.group
  genericMap : (fibreGroup E).map map ≫ genericTarget.hom = genericSource.hom ≫ q
  genericKernelInclusion : (fibreGroup E).map kernelInclusion ≫ genericSource.hom =
    genericKernel.hom ≫ N.inclusion
  genericSourceTorusInclusion : (fibreGroup E).map sourceTorusInclusion ≫ genericSource.hom =
    genericSourceTorus.hom ≫ T.sourceTorus.inclusion
  genericTargetTorusInclusion : (fibreGroup E).map targetTorusInclusion ≫ genericTarget.hom =
    genericTargetTorus.hom ≫ T.targetTorus.inclusion
  genericTorusMap : (fibreGroup E).map torusMap ≫ genericTargetTorus.hom =
    genericSourceTorus.hom ≫ T.restriction
  matrixInclusion : target.val.X ⟶ matrixScheme R m
  matrixClosed : IsClosedImmersion matrixInclusion.left
  genericMatrix : genericTarget.hom.hom.hom.left ≫ i.inclusion.left ≫
    Spec.map (CommRingCat.ofHom (matrixCoordinateMap R E m)) =
      pullback.fst target.val.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R E))) ≫ matrixInclusion.left
  matrixClosure :
    (pullback.fst target.val.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R E))) ≫
      matrixInclusion.left).ker = matrixInclusion.left.ker

/-- The finitely presented isogeny with its torus data and finite kernel
torsor extends over the integers away from finitely many places. -/
def IntegralModels : Prop :=
  ∀ {E : Type u} [Field E] (D : GlobalFieldData.{u, v} E) (B : Set D.FinitePlace),
    B.Finite →
    ∀ (G H : AffineAlgebraicGroup E) (q : H.val ⟶ G.val) (N : ClosedSubgroup H.val),
      IsCentralIsogeny q → IsSchemeKernel q N →
      ∀ (T : SplitCoverData G H q N) {m : ℕ} (i : MatrixEmbedding G m),
        ∃ S : Set D.FinitePlace, S.Finite ∧ B ⊆ S ∧
          Nonempty (IntegralModel (R := integersOutside D S) T i)

/-- The cover, its split coordinates, and integral models of that same diagram
for any chosen matrix embedding over the original global field. -/
def GlobalCoverWithModels : Prop :=
  ∀ {K : Type u} [Field K] (_D : GlobalFieldData.{u, v} K) (G : AffineAlgebraicGroup K),
    IsSemisimple G → ∀ {m : ℕ} (i : MatrixEmbedding G m),
    ∃ (H : AffineAlgebraicGroup K) (q : H.val ⟶ G.val) (N : ClosedSubgroup H.val),
      IsSemisimple H ∧ GeometricallySimplyConnected H ∧ IsCentralIsogeny q ∧ IsSchemeKernel q N ∧
      IsFiniteMultiplicativeType N.group ∧ SameAdjointQuotient q ∧
      (IsTrivialSubgroup N ↔ GeometricallySimplyConnected G) ∧
      ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E) (_ : IsGalois K E),
        let G' := baseChangedAlgebraicGroup E G
        let H' := baseChangedAlgebraicGroup E H
        let q' := (groupBaseChange K E).map q
        ∃ hc : IsClosedImmersion ((groupBaseChange K E).map N.inclusion).hom.hom.left,
          let N' : ClosedSubgroup H'.val := ⟨_, (groupBaseChange K E).map N.inclusion, hc⟩
          ∃ (T : SplitCoverData G' H' q' N') (D' : GlobalFieldData.{u, v} E)
            (j : MatrixEmbedding G' m),
            IsSemisimple G' ∧ IsSemisimple H' ∧ IsCentralIsogeny q' ∧ IsSchemeKernel q' N' ∧
            ((∃ a, 1 < T.exponents a) ↔ ¬ GeometricallySimplyConnected G) ∧
            (j.inclusion.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap K E m)) =
              pullback.fst G.val.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K E))) ≫ i.inclusion.left) ∧
            ∀ (B : Set D'.FinitePlace), B.Finite →
              ∃ S : Set D'.FinitePlace, S.Finite ∧ B ⊆ S ∧
                Nonempty (IntegralModel (R := integersOutside D' S) T j)

end

end LinearAlgebraicGroups.Specs.CentralCover
