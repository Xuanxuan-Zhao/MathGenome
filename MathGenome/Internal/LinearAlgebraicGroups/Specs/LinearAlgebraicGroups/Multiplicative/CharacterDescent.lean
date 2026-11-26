import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineGroups
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology

open CategoryTheory Opposite Coalgebra
open scoped TensorProduct MonoidAlgebra

namespace LinearAlgebraicGroups.Specs.CharacterDescent

open DiagonalizableGroups LinearAlgebraicGroups.Descent

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The split coordinate algebra represents a diagonalizable group. -/
def IsDiagonalizable (A : HopfAlgebraCategory k) : Prop :=
  ∃ M : FGAbelianGroup.{u}, Nonempty (groupAlgebra k M.obj ≅ A)

/-- Splitting is allowed over any separable algebraic extension. -/
def IsMultiplicativeType (A : HopfAlgebraCategory k) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E),
    IsDiagonalizable (extendedHopf E A)

/-- The character lattice of the split torus of rank `r`, in multiplicative notation. -/
abbrev StandardLattice (r : ℕ) := Fin r → IntegerCharacters.{u}

/-- A torus is a separable form of a split torus. -/
def IsTorus (A : HopfAlgebraCategory k) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E) (r : ℕ),
    Nonempty (groupAlgebra E (StandardLattice.{u} r) ≅ extendedHopf E A)

/-- Characters and cocharacters are group-scheme morphisms to and from the multiplicative group. -/
abbrev Character (G : GroupScheme k) :=
  G ⟶ (specGroup (groupAlgebra k IntegerCharacters))

abbrev Cocharacter (G : GroupScheme k) :=
  (specGroup (groupAlgebra k IntegerCharacters)) ⟶ G

instance groupAlgebraSpectrumIsCommMonObj {M : Type u} [CommGroup M] :
    IsCommMonObj (specGroup (groupAlgebra k M)).X :=
  AlgebraicGeometry.isCommMonObj_spec_asOver_spec
    (R := CommRingCat.of k) (A := CommRingCat.of (MonoidAlgebra k M))

/-- Characters multiply as morphisms into the commutative group `Gm`. -/
instance characterCommGroup (G : GroupScheme k) : CommGroup (Character G) :=
  CategoryTheory.Hom.commGroup

/-- For a commutative group scheme the cocharacters have the pointwise group law. -/
instance cocharacterCommGroup (G : GroupScheme k) [IsCommMonObj G.X] :
    CommGroup (Cocharacter G) :=
  CategoryTheory.Hom.commGroup

/-- Evaluation of a character on a cocharacter is composition as an endomorphism of Gm. -/
def compositionPairing (G : GroupScheme k) (χ : Character G) (cochar : Cocharacter G) :
    Character (specGroup (groupAlgebra k IntegerCharacters)) :=
  cochar ≫ χ

/-- Coordinate Hopf algebras of groups of multiplicative type. -/
abbrev MultiplicativeTypeHopf (k : Type u) [Field k] :=
  (show ObjectProperty (FiniteTypeHopfAlgebraCategory k) from
    fun A => IsMultiplicativeType A.val).FullSubcategory

/-- Continuity for a discrete target is expressed by openness of the stabilizers. -/
def HasContinuousAction {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (M : Action CommGrpCat.{u} Γ) : Prop :=
  ∀ m : M.V, IsOpen {g : Γ | (M.ρ g).asHom m = m}

/-- Finitely generated abelian groups with a continuous discrete Galois action. -/
abbrev CharacterModule (k K : Type u) [Field k] [Field K] [Algebra k K] :=
  (show ObjectProperty (Action CommGrpCat.{u} Gal(K/k)) from
    fun M => Group.FG M.V ∧ HasContinuousAction M).FullSubcategory

/-- The action on the group algebra changes both the coefficients and their indices. -/
def groupAlgebraOperator {M : Type u} [CommGroup M] (σ : Gal(K/k)) (e : M ≃* M) :
    MonoidAlgebra K M ≃+* MonoidAlgebra K M :=
  (MonoidAlgebra.mapRingEquiv M σ.toRingEquiv).trans (MonoidAlgebra.domCongr K K e).toRingEquiv

abbrev IsDiagonalizableType := ∀ {k : Type u} [Field k], HopfAlgebraCategory k → Prop
abbrev IsMultiplicativeTypeType := IsDiagonalizableType.{u}
abbrev IsTorusType := IsDiagonalizableType.{u}
abbrev CharacterType := ∀ {k : Type u} [Field k], GroupScheme k → Type u
abbrev CocharacterType := CharacterType.{u}
abbrev CompositionPairingType := ∀ {k : Type u} [Field k] (G : GroupScheme k),
  Character G → Cocharacter G → Character (specGroup (groupAlgebra k IntegerCharacters))
abbrev GroupAlgebraOperatorType := ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
  {M : Type u} [CommGroup M], Gal(K/k) → (M ≃* M) → (MonoidAlgebra K M ≃+* MonoidAlgebra K M)

/-- The underlying geometric characters, represented as group-like elements of the base change. -/
abbrev GeometricCharacters (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k) :=
  GroupLike K (extendedHopf K A)

/-- Explicit finite-level descent and the normalization of its comparison on the basis. -/
def FiniteGroupAlgebraDescent : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Type u} [CommGroup M] [Group.FG M] (ρ : Gal(K/k) →* MulAut M),
    ∃ (D : HopfDescentDatum k (groupAlgebra K M)) (H : HopfDescent D),
      (∀ g, D.action.act g = (groupAlgebraOperator g (ρ g)).toAddEquiv) ∧
      Algebra.FiniteType k H.algebra ∧
      (SemilinearAction.scalarExtension (K := K) H.algebra).Equivariant D.action
        H.iso.hom.hom.toLinearMap ∧
      IsMultiplicativeType H.algebra ∧
      Nonempty ((groupBaseChange k K).obj (specGroup H.algebra) ≅ specGroup (groupAlgebra K M))

/-- Every continuous action on a finitely generated discrete group descends to a finite
Galois subextension of the separable closure. -/
def FactorsThroughFiniteGalois : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (M : CharacterModule k K),
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (hN : Normal k E)
      (ρ : Gal(E/k) →* MulAut M.obj.V),
      letI := hN
      ∀ σ m, (M.obj.ρ σ).asHom m = ρ (AlgEquiv.restrictNormalHom E σ) m


/-- Group-like elements are the characters of the represented group scheme. -/
def CharacterInterpretation : Prop :=
  ∀ {k : Type u} [Field k],
    ∃ e : ∀ A : HopfAlgebraCategory k, GroupLike k A ≃* Character (specGroup A),
      (∀ (A B : HopfAlgebraCategory k) (f : A ⟶ B) (x : GroupLike k A),
        e B ⟨f.hom x.val, x.2.map f.hom⟩ = specGroupMap f ≫ e A x) ∧
      (∀ (A : HopfAlgebraCategory k) (x : GroupLike k A),
        ∃ f : groupAlgebra k IntegerCharacters ⟶ A,
          f.hom (MonoidAlgebra.of k _ integerGenerator) = x.val ∧ e A x = specGroupMap f)

/-- Every affine group of multiplicative type splits over the separable closure,
and the converse uses separability of the closure. -/
def SplitsOverSeparableClosure : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (A : HopfAlgebraCategory k),
    IsMultiplicativeType A ↔ IsDiagonalizable (extendedHopf K A)

/-- A separably diagonalizable affine group is of finite type and commutative. -/
def MultiplicativeTypeProperties : Prop :=
  ∀ {k : Type u} [Field k] (A : HopfAlgebraCategory k), IsMultiplicativeType A →
    Algebra.FiniteType k A ∧ IsCommMonObj (specGroup A).X

/-- The torus definition is a special case of multiplicative type. -/
def TorusIsMultiplicativeType : Prop :=
  ∀ {k : Type u} [Field k] (A : HopfAlgebraCategory k), IsTorus A → IsMultiplicativeType A

/-- The geometric character functor is an equivalence on coordinate algebras.
Taking spectra reverses its direction on the group schemes. -/
def GeometricCharacterAntiequivalence : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K],
    ∃ F : MultiplicativeTypeHopf k ⥤ CharacterModule k K,
      F.IsEquivalence ∧
      ∃ e : ∀ A : MultiplicativeTypeHopf k, (F.obj A).obj.V ≃* GeometricCharacters K A.obj.val,
        (∀ (A : MultiplicativeTypeHopf k) (σ : Gal(K/k)) (m : (F.obj A).obj.V),
          (e A ((F.obj A).obj.ρ σ |>.asHom m)).val =
            (SemilinearAction.scalarExtension (K := K) A.obj.val).act σ (e A m).val) ∧
        (∀ (A B : MultiplicativeTypeHopf k) (f : A ⟶ B) (m : (F.obj A).obj.V),
          (e B ((F.map f).hom.hom m)).val =
            (extendedHopfMap K f.hom.hom).hom (e A m).val)

/-- Splitness and the distinction between all multiplicative-type groups and tori. -/
def TorusAndSplitCriteria : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (A : HopfAlgebraCategory k), IsMultiplicativeType A →
    (IsTorus A ↔ ∃ r : ℕ, Nonempty (GeometricCharacters K A ≃* StandardLattice.{u} r)) ∧
    (IsDiagonalizable A ↔
      ∀ (σ : Gal(K/k)) (m : GeometricCharacters K A),
        (SemilinearAction.scalarExtension (K := K) A).act σ m.val = m.val)

/-- Enlarging the finite Galois field does not change the descended algebra.
The isomorphism is normalized by the canonical maps on the group algebras. -/
def DescentIndependentOfField : Prop :=
  ∀ {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [FiniteDimensional k L]
    [IsGalois k K] [IsGalois k L] {M : Type u} [CommGroup M] [Group.FG M]
    (ρ : Gal(K/k) →* MulAut M)
    (D : HopfDescentDatum k (groupAlgebra K M)) (D' : HopfDescentDatum k (groupAlgebra L M))
    (H : HopfDescent D) (H' : HopfDescent D'),
    (∀ g, D.action.act g = (groupAlgebraOperator g (ρ g)).toAddEquiv) →
    (∀ g, D'.action.act g =
      (groupAlgebraOperator g (ρ (AlgEquiv.restrictNormalHom K g))).toAddEquiv) →
    ∃! e : H.algebra ≅ H'.algebra, ∀ x : D.fixed,
      (e.hom.hom x).val = MonoidAlgebra.mapAlgHom M (Algebra.ofId K L) x.val

/-- After any field extension, the group of geometric characters is unchanged
and the action is restricted using the compatible separable closures. -/
def BaseChangeRestrictsAction : Prop :=
  ∀ {k K L S : Type u} [Field k] [Field K] [Field L] [Field S]
    [Algebra k K] [Algebra k L] [Algebra k S] [Algebra K S] [Algebra L S]
    [IsScalarTower k K S] [IsScalarTower k L S] [IsSepClosure k K] [IsSepClosure L S]
    (A : HopfAlgebraCategory k), IsMultiplicativeType A →
    IsMultiplicativeType (extendedHopf L A) ∧
    ∃ e : GeometricCharacters K A ≃* GeometricCharacters S (extendedHopf L A),
      (∀ (x : GeometricCharacters K A),
        (Algebra.TensorProduct.cancelBaseChange k L S S A) (e x).val =
          (Algebra.TensorProduct.map (Algebra.ofId K S |>.restrictScalars k)
            (AlgHom.id k A)) x.val) ∧
      ∀ (σ : Gal(S/L)) (x y : GeometricCharacters K A),
        (SemilinearAction.scalarExtension (K := K) A).act
            ((σ.restrictScalars k).restrictNormal K) x.val = y.val →
        (SemilinearAction.scalarExtension (K := S) (extendedHopf L A)).act σ (e x).val =
          (e y).val


/-- The usual split torus is the spectrum of the group algebra of its lattice. -/
def StandardSplitTorus : Prop :=
  ∀ {k : Type u} [Field k] (r : ℕ),
    Nonempty (specGroup (groupAlgebra k (StandardLattice.{u} r)) ≅
      (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val)

/-- For a split torus, composition agrees with evaluation of the cocharacter
on the character lattice, with the resulting endomorphism of the multiplicative
group given by its exponent. -/
def SplitCompositionPairing : Prop :=
  ∀ {k : Type u} [Field k] (r : ℕ),
    let M := StandardLattice.{u} r
    let T := specGroup (groupAlgebra k M)
    ∃ (χ : M ≃* Character T) (cochar : (M →* IntegerCharacters.{u}) ≃* Cocharacter T),
      (∀ m, χ m = specGroupMap (groupAlgebraMap k
        ((zpowersHom M m).comp (MulEquiv.ulift.toMonoidHom)))) ∧
      (∀ f, cochar f = specGroupMap (groupAlgebraMap k f)) ∧
      (∀ m f, compositionPairing T (χ m) (cochar f) =
        specGroupMap (groupAlgebraMap k
          ((zpowersHom IntegerCharacters (f m)).comp MulEquiv.ulift.toMonoidHom)))

/-- The coordinate-algebra presentation agrees with diagonalizability after
a separable extension of the group scheme itself. -/
def MultiplicativeTypeOnSchemes : Prop :=
  ∀ {k : Type u} [Field k] (A : HopfAlgebraCategory k),
    IsMultiplicativeType A ↔
      ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E)
        (M : FGAbelianGroup.{u}),
        Nonempty ((groupBaseChange k E).obj (specGroup A) ≅ specGroup (groupAlgebra E M.obj))

/-- The corresponding comparison for a torus, using powers of the multiplicative group. -/
def TorusOnSchemes : Prop :=
  ∀ {k : Type u} [Field k] (A : HopfAlgebraCategory k),
    IsTorus A ↔
      ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E) (r : ℕ),
        Nonempty ((groupBaseChange k E).obj (specGroup A) ≅
          (StandardGroups.multiplicativePowerGroup E (ULift.{u} (Fin r))).val)

def multiplicativeTypeSpecFunctor (k : Type u) [Field k] :
    (MultiplicativeTypeHopf k)ᵒᵖ ⥤ AffineAlgebraicGroupCategory k :=
  (ObjectProperty.ι (fun A : FiniteTypeHopfAlgebraCategory k => IsMultiplicativeType A.val)).op ⋙
    finiteTypeHopfSpec k

abbrev MultiplicativeTypeGroup (k : Type u) [Field k] :=
  (multiplicativeTypeSpecFunctor k).EssImageSubcategory

/-- The domain of the scheme antiequivalence consists of the groups that become
diagonalizable after a separable field extension. -/
def MultiplicativeTypeGroupCriterion : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroupCategory k),
    (multiplicativeTypeSpecFunctor k).essImage G ↔
      ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E)
        (M : FGAbelianGroup.{u}),
        Nonempty ((groupBaseChange k E).obj G.val ≅ specGroup (groupAlgebra E M.obj))

/-- The scheme antiequivalence, compared on group-algebra spectra with the geometric
character module of the coordinate algebra. -/
def GeometricCharacterSchemeAntiequivalence : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K],
    ∃ E : (MultiplicativeTypeGroup k)ᵒᵖ ≌ CharacterModule k K,
      ∃ F : MultiplicativeTypeHopf k ⥤ CharacterModule k K,
        F.IsEquivalence ∧
        Nonempty ((multiplicativeTypeSpecFunctor k).toEssImage.rightOp ⋙ E.functor ≅ F) ∧
      ∃ e : ∀ A : MultiplicativeTypeHopf k, (F.obj A).obj.V ≃* GeometricCharacters K A.obj.val,
        (∀ (A : MultiplicativeTypeHopf k) (σ : Gal(K/k)) (m : (F.obj A).obj.V),
          (e A ((F.obj A).obj.ρ σ |>.asHom m)).val =
            (SemilinearAction.scalarExtension (K := K) A.obj.val).act σ (e A m).val) ∧
        (∀ (A B : MultiplicativeTypeHopf k) (f : A ⟶ B) (m : (F.obj A).obj.V),
          (e B ((F.map f).hom.hom m)).val =
            (extendedHopfMap K f.hom.hom).hom (e A m).val)

/-- Both closures can be taken inside the same algebraic closure of the extension field. -/
def CompatibleSeparableClosures : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L],
    let K := separableClosure k (AlgebraicClosure L)
    let S := SeparableClosure L
    ∃ (a : Algebra K S), letI := a; IsScalarTower k K S

/-- Two finite splitting fields inside a common Galois extension give the same
descent, canonically inside the group algebra over the common field. -/
def DescentIndependentOfTwoFields : Prop :=
  ∀ {k K L S : Type u} [Field k] [Field K] [Field L] [Field S]
    [Algebra k K] [Algebra k L] [Algebra k S] [Algebra K S] [Algebra L S]
    [IsScalarTower k K S] [IsScalarTower k L S] [IsGalois k S]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    {M : Type u} [CommGroup M] [Group.FG M]
    (ρ : Gal(K/k) →* MulAut M) (τ : Gal(L/k) →* MulAut M)
    (D : HopfDescentDatum k (groupAlgebra K M)) (D' : HopfDescentDatum k (groupAlgebra L M))
    (H : HopfDescent D) (H' : HopfDescent D'),
    (∀ σ : Gal(S/k), ρ (σ.restrictNormal K) = τ (σ.restrictNormal L)) →
    (∀ g, D.action.act g = (groupAlgebraOperator g (ρ g)).toAddEquiv) →
    (∀ g, D'.action.act g = (groupAlgebraOperator g (τ g)).toAddEquiv) →
    ∃! e : H.algebra ≅ H'.algebra, ∀ x : D.fixed,
      MonoidAlgebra.mapAlgHom M (Algebra.ofId L S) (e.hom.hom x).val =
        MonoidAlgebra.mapAlgHom M (Algebra.ofId K S) x.val

/-- Finite descent recovers the prescribed characters and the induced action on them.
The Hopf comparison sends a fixed element to its image under extension of coefficients. -/
def FiniteDescentCharacters : Prop :=
  ∀ {k K S : Type u} [Field k] [Field K] [Field S]
    [Algebra k K] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    [FiniteDimensional k K] [IsGalois k K] [IsSepClosure k S]
    {M : Type u} [CommGroup M] (ρ : Gal(K/k) →* MulAut M)
    (D : HopfDescentDatum k (groupAlgebra K M)) (H : HopfDescent D),
    (∀ g, D.action.act g = (groupAlgebraOperator g (ρ g)).toAddEquiv) →
    ∃ (e : M ≃* GeometricCharacters S H.algebra)
      (j : extendedHopf S H.algebra ≅ groupAlgebra S M),
      (∀ (a : S) (x : D.fixed), j.hom.hom (a ⊗ₜ[k] x) =
        a • MonoidAlgebra.mapAlgHom M (Algebra.ofId K S) x.val) ∧
      (∀ m, j.hom.hom (e m).val = MonoidAlgebra.single m 1) ∧
      ∀ (σ : Gal(S/k)) m, (SemilinearAction.scalarExtension (K := S) H.algebra).act σ
        (e m).val = (e (ρ (σ.restrictNormal K) m)).val

/-- A multiplicative-type group has a finite Galois splitting subfield of the separable closure. -/
def FiniteGaloisSplitting : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    (A : HopfAlgebraCategory k), IsMultiplicativeType A →
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (_ : IsGalois k E),
      IsDiagonalizable (extendedHopf E A)

end

end LinearAlgebraicGroups.Specs.CharacterDescent
