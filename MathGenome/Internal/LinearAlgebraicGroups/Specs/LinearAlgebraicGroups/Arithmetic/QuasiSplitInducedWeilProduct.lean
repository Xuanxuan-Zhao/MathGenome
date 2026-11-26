import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.FieldTheory.Galois.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Coalgebra HopfAlgebra
open scoped TensorProduct

namespace LinearAlgebraicGroups.Specs.QuasiSplitInducedWeilProduct

universe u

open _root_.LinearAlgebraicGroups.Descent
open _root_.LinearAlgebraicGroups.WeilRestriction (extendScalars)

noncomputable section

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- The inclusion of a subgroup of the finite Galois group from the Galois
group over its fixed field. -/
abbrev restrictToFixedFieldSubgroup [FiniteDimensional F K] (J : Subgroup Gal(K/F)) :
    Gal(K/IntermediateField.fixedField J) ≃* J :=
  (IntermediateField.subgroupEquivAlgEquiv J).symm

/-- Scalar extension of a test algebra from the ground field, evaluated
at a particular embedding of the intermediate field. -/
def orbitTestAlgebra (L : IntermediateField F K) (a : L →ₐ[F] K) (R : TestAlgebra K) :
    TestAlgebra L :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  (restrictTestAlgebra L K).obj R

/-- Evaluation sends `r ⊗ l` to `r * a(l)`. -/
def orbitTestProjection (L : IntermediateField F K) (a : L →ₐ[F] K) (R : TestAlgebra K) :
    (extendScalars F L).obj ((restrictTestAlgebra F K).obj R) ⟶ orbitTestAlgebra L a R := by
  let S := (restrictTestAlgebra F K).obj R
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  let g : L →ₐ[F] S := (IsScalarTower.toAlgHom F K S).comp a
  let e := Algebra.TensorProduct.lift (AlgHom.id S S) g (fun _ _ => Commute.all _ _)
  let T := (extendScalars F L).obj S
  let V := orbitTestAlgebra L a R
  letI : Algebra L T := T.algebra
  letI : Algebra L V := V.algebra
  refine ConcreteCategory.ofHom (C := CommAlgCat L)
    ({ e.toRingHom with commutes' := fun x => ?_ } : T →ₐ[L] V)
  change (1 : S) * algebraMap K R (a x) = algebraMap K R (a x)
  exact one_mul _

/-- Base change through the indicated embedding, including when the same
underlying field carries several distinct scalar structures. -/
def orbitBaseChangedGroup (L : IntermediateField F K) (a : L →ₐ[F] K)
    (H : GroupScheme L) : GroupScheme K :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  (groupBaseChange L K).obj H

def orbitBaseChangePoint (L : IntermediateField F K) (a : L →ₐ[F] K)
    (H : GroupScheme L) (R : TestAlgebra K)
    (x : Points (orbitBaseChangedGroup L a H).X R) : Points H.X (orbitTestAlgebra L a R) :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  baseChangePoint L K H.X R x

/-- The split Weil projection is evaluation at the given embedding on
every test algebra. -/
def IsWeilProjection (L : IntermediateField F K) (a : L →ₐ[F] K) {W : GroupScheme F}
    {H : GroupScheme L}
    (e : (groupPointsFunctor F).obj W ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj H)
    (p : (groupBaseChange F K).obj W ⟶ orbitBaseChangedGroup L a H) : Prop :=
  ∀ (R : TestAlgebra K) (x : Points ((groupBaseChange F K).obj W).X R),
    orbitBaseChangePoint L a H R (x ≫ p.hom.hom) =
      ((groupPointsFunctor L).obj H).map (orbitTestProjection L a R)
        (e.hom.app ((restrictTestAlgebra F K).obj R) (baseChangePoint F K W.X R x))

def OrbitFieldEmbeddings : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I] (i : I),
    (∀ j : I, ∃ σ : Gal(K/F), σ • i = j) →
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∃ e : I ≃ (L →ₐ[F] K), e i = L.val ∧
      ∀ σ : Gal(K/F), ∀ j, e (σ • j) = σ.toAlgHom.comp (e j)

def OrbitFieldTensorSplitting : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (L : IntermediateField F K),
    ∃ e : K ⊗[F] L ≃ₐ[K] ((L →ₐ[F] K) → K),
      ∀ r l a, e (r ⊗ₜ[F] l) a = r * a l

def OrbitTensorSplittingOnTestAlgebras : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (L : IntermediateField F K),
    let U := restrictTestAlgebra F K
    ∃ e : ∀ R : TestAlgebra K, (U.obj R) ⊗[F] L ≃ₐ[R] ((L →ₐ[F] K) → R),
      (∀ (R : TestAlgebra K) (r : R) (l : L) (a : L →ₐ[F] K),
        e R (r ⊗ₜ[F] l) a = r * algebraMap K R (a l)) ∧
      ∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : (U.obj R) ⊗[F] L) (a : L →ₐ[F] K),
        e S (Algebra.TensorProduct.map (U.map f).hom (AlgHom.id F L) x) a =
          f.hom (e R x a)

def OrbitTestAlgebraProduct : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (L : IntermediateField F K) (R : TestAlgebra K),
    Nonempty (IsLimit (Fan.mk ((extendScalars F L).obj ((restrictTestAlgebra F K).obj R))
      (fun a => orbitTestProjection L a R)))

def WeilRestrictionBaseChangeProduct : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (L : IntermediateField F K)
    (W : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup L)
    (e : (groupPointsFunctor F).obj W.val ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj H.val),
    ∃ p : ∀ a : L →ₐ[F] K,
        (groupBaseChange F K).obj W.val ⟶ orbitBaseChangedGroup L a H.val,
      Nonempty (IsLimit (Fan.mk _ p)) ∧
      ∀ a, IsWeilProjection L a e (p a)

def WeilRestrictionProjectionNaturality : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (a : L →ₐ[F] K)
    {V W : AffineAlgebraicGroup F} {S H : AffineAlgebraicGroup L}
    (f : V.val ⟶ W.val) (g : S.val ⟶ H.val)
    (e : (groupPointsFunctor F).obj W.val ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj H.val)
    (d : (groupPointsFunctor F).obj V.val ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj S.val)
    {p : (groupBaseChange F K).obj W.val ⟶ orbitBaseChangedGroup L a H.val}
    {q : (groupBaseChange F K).obj V.val ⟶ orbitBaseChangedGroup L a S.val},
    IsWeilProjection L a e p → IsWeilProjection L a d q →
    (groupPointsFunctor F).map f ≫ e.hom =
      d.hom ≫ Functor.whiskerLeft (extendScalars F L) ((groupPointsFunctor L).map g) →
    letI : Algebra L K := a.toRingHom.toAlgebra
    (groupBaseChange F K).map f ≫ p = q ≫ (groupBaseChange L K).map g

/-- The universal property of the actual projections of a product of affine
groups, written on their coordinate algebras. -/
def IsCoordinateProduct {k I : Type u} [Field k]
    {P : HopfAlgebraCategory k} {Q : I → HopfAlgebraCategory k} (p : ∀ i, Q i ⟶ P) : Prop :=
  ∀ R : TestAlgebra k, Function.Bijective
    (fun (x : P →ₐ[k] R) i => x.comp (p i).hom.toAlgHom)

/-- A known descent is specified with an equivariant scalar extension
comparison. The coordinate isomorphism is oriented against the group map. -/
structure KnownDescent {A : HopfAlgebraCategory K} (D : HopfDescentDatum F A) where
  coordinate : HopfAlgebraCategory F
  comparison : extendedHopf K coordinate ≅ A
  equivariant : ∀ σ x, comparison.hom.hom
    ((SemilinearAction.scalarExtension coordinate).act σ x) =
      D.action.act σ (comparison.hom.hom x)

variable {I : Type u} [MulAction Gal(K/F) I]

/-- The semilinear action permutes the actual projections of a finite
product. The inverse pullback convention is used on coordinates. -/
structure SplitProduct where
  total : HopfAlgebraCategory K
  factor : I → HopfAlgebraCategory K
  finiteType : ∀ i, Algebra.FiniteType K (factor i)
  projection : ∀ i, factor i ⟶ total
  product : IsCoordinateProduct projection
  datum : HopfDescentDatum F total
  transport : ∀ (σ : Gal(K/F)) (i j : I), σ • i = j → factor i ≃+* factor j
  transportScalar : ∀ σ i j h r, transport σ i j h (algebraMap K (factor i) r) =
    algebraMap K (factor j) (σ r)
  transportProjection : ∀ σ i j h x, (projection j).hom (transport σ i j h x) =
    datum.action.act σ ((projection i).hom x)

/-- The split product together with its given form over the ground field. -/
structure ProductDescent extends SplitProduct (F := F) (K := K) (I := I) where
  descent : KnownDescent datum

/-- A finite product of affine algebraic groups and its descended form are
both of finite type. -/
def ProductDescentFiniteType : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [Finite I] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)),
    Algebra.FiniteType K A.total ∧ Algebra.FiniteType F A.descent.coordinate

/-- A compatible family of closed subgroup inclusions into the same
ambient product and its given descent. -/
structure ProductInclusion (A S : ProductDescent (F := F) (K := K) (I := I)) where
  extended : A.total ⟶ S.total
  ground : A.descent.coordinate ⟶ S.descent.coordinate
  factor : ∀ i, A.factor i ⟶ S.factor i
  closed : ∀ i, Function.Surjective (factor i).hom
  projected : ∀ i, A.projection i ≫ extended = factor i ≫ S.projection i
  compared : A.descent.comparison.hom ≫ extended =
    extendedHopfMap K ground ≫ S.descent.comparison.hom

/-- Stability data for a product of closed subgroup schemes before its
ground-field form has been constructed. -/
structure StableProductInclusion (A : ProductDescent (F := F) (K := K) (I := I))
    (S : SplitProduct (F := F) (K := K) (I := I)) where
  extended : A.total ⟶ S.total
  factor : ∀ i, A.factor i ⟶ S.factor i
  closed : ∀ i, Function.Surjective (factor i).hom
  projected : ∀ i, A.projection i ≫ extended = factor i ≫ S.projection i
  equivariant : A.datum.Equivariant S.datum extended

def StableProductDescent : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I))
    (S : SplitProduct (F := F) (K := K) (I := I)) (j : StableProductInclusion A S),
    ∃ (d : KnownDescent S.datum) (g : A.descent.coordinate ⟶ d.coordinate),
      A.descent.comparison.hom ≫ j.extended = extendedHopfMap K g ≫ d.comparison.hom ∧
      Function.Surjective g.hom ∧ IsClosedImmersion (specGroupMap g).hom.hom.left

/-- The representative comparison intertwines the induced stabilizer action
and the standard action on extension of scalars from the orbit field. -/
def IsRepresentativeDescent [FiniteDimensional F K]
    (A : ProductDescent (F := F) (K := K) (I := I)) (i : I)
    {H : HopfAlgebraCategory (IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i))}
    (e : extendedHopf K H ≅ A.factor i) : Prop :=
  let J := MulAction.stabilizer Gal(K/F) i
  ∀ σ : Gal(K/IntermediateField.fixedField J), ∀ x : extendedHopf K H,
    let s := restrictToFixedFieldSubgroup J σ
    e.hom.hom ((SemilinearAction.scalarExtension H).act σ x) =
      A.transport s.val i i (MulAction.mem_stabilizer_iff.mp s.property) (e.hom.hom x)

def RepresentativeDescent : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)) (i : I),
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∃ (H : HopfAlgebraCategory L) (e : extendedHopf K H ≅ A.factor i),
      Algebra.FiniteType L H ∧ IsRepresentativeDescent A i e

def RepresentativeInclusionDescent : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    {A S : ProductDescent (F := F) (K := K) (I := I)} (j : ProductInclusion A S) (i : I),
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∀ {H D : HopfAlgebraCategory L}
      {e : extendedHopf K H ≅ A.factor i} {d : extendedHopf K D ≅ S.factor i},
      IsRepresentativeDescent A i e → IsRepresentativeDescent S i d →
      ∃ f : H ⟶ D, Function.Surjective f.hom ∧
        e.hom ≫ j.factor i = extendedHopfMap K f ≫ d.hom


/-- The actual projection at a representative descends to a morphism from
the given ground-field form extended to the orbit field. -/
def RepresentativeProjectionDescent : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)) (i : I),
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∀ {H : HopfAlgebraCategory L} {e : extendedHopf K H ≅ A.factor i},
      IsRepresentativeDescent A i e →
      ∃ g : H ⟶ extendedHopf L A.descent.coordinate,
        e.hom ≫ A.projection i = extendedHopfMap K g ≫
          (_root_.LinearAlgebraicGroups.Descent.Forms.scalarTowerIso A.descent.coordinate).hom ≫
          A.descent.comparison.hom


section CoordinateProjections

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open _root_.LinearAlgebraicGroups.Descent.Forms (scalarTowerIso)

variable (L : IntermediateField F K)

def representativeEvaluation {R : TestAlgebra F} {B : HopfAlgebraCategory F}
    {H : HopfAlgebraCategory L} (g : H ⟶ extendedHopf L B) (x : B →ₐ[F] R) :
    H →ₐ[L] (extendScalars F L).obj R :=
  ((Algebra.TensorProduct.commRight F L R).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id L L) x)).comp g.hom.toAlgHom

def groundCoordinatePoint
    (A : ProductDescent (F := F) (K := K) (I := I)) {R : TestAlgebra K}
    (x : A.total →ₐ[K] R) :
    let S := (restrictTestAlgebra F K).obj R
    letI : Algebra F S := S.algebra
    A.descent.coordinate →ₐ[F] S := by
  let S := (restrictTestAlgebra F K).obj R
  letI : Algebra F S := S.algebra
  letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' rfl
  exact ((x.comp A.descent.comparison.hom.hom.toAlgHom).restrictScalars F).comp
    Algebra.TensorProduct.includeRight

def componentAtEmbedding [FiniteDimensional F K]
    (A : ProductDescent (F := F) (K := K) (I := I)) {i : I}
    {H : HopfAlgebraCategory (IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i))}
    (e : extendedHopf K H ≅ A.factor i) (σ : Gal(K/F)) {j : I} (h : σ • i = j)
    {R : TestAlgebra K} (x : A.factor j →ₐ[K] R) :
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    let V := orbitTestAlgebra L (σ.toAlgHom.comp L.val) R
    letI : Algebra L V := V.algebra
    H →ₐ[L] V := by
  let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
  let V := orbitTestAlgebra L (σ.toAlgHom.comp L.val) R
  letI : Algebra L V := V.algebra
  let t := A.transport σ i j h
  refine { x.toRingHom.comp (t.toRingHom.comp
    (e.hom.hom.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight : H →ₐ[L] K ⊗[L] H).toRingHom)) with
    commutes' := fun l => ?_ }
  change x (t (e.hom.hom (1 ⊗ₜ[L] algebraMap L H l))) = algebraMap K R (σ (l : K))
  have he : e.hom.hom (1 ⊗ₜ[L] algebraMap L H l) = algebraMap K (A.factor i) (l : K) := by
    rw [show (1 ⊗ₜ[L] algebraMap L H l : K ⊗[L] H) = algebraMap K (K ⊗[L] H) (l : K) by
      rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rfl,
      show e.hom.hom (algebraMap K (K ⊗[L] H) (l : K)) = _ from e.hom.hom.toAlgHom.commutes _]
  rw [he, A.transportScalar, x.commutes]

/-- In split coordinates the actual projection at any embedding is obtained
by applying the embedding to the orbit-field tensor factor. -/
def SplitRepresentativeProjectionFormula : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)) (i : I),
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∀ {H : HopfAlgebraCategory L} {e : extendedHopf K H ≅ A.factor i}
      (g : H ⟶ extendedHopf L A.descent.coordinate),
      e.hom ≫ A.projection i = extendedHopfMap K g ≫
        (scalarTowerIso A.descent.coordinate).hom ≫ A.descent.comparison.hom →
      ∀ (σ : Gal(K/F)) (j : I) (h : σ • i = j) (R : TestAlgebra K)
        (x : A.total →ₐ[K] R),
      let T := (extendScalars F L).obj ((restrictTestAlgebra F K).obj R)
      let V := orbitTestAlgebra L (σ.toAlgHom.comp L.val) R
      letI : Algebra L T := T.algebra
      letI : Algebra L V := V.algebra
      (orbitTestProjection L (σ.toAlgHom.comp L.val) R).hom.comp
        (representativeEvaluation L g (groundCoordinatePoint A x)) =
      componentAtEmbedding A e σ h (x.comp (A.projection j).hom.toAlgHom)

def ComponentAtEmbeddingBijective : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)) (i : I),
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∀ {H : HopfAlgebraCategory L} (e : extendedHopf K H ≅ A.factor i)
      (σ : Gal(K/F)) (j : I) (h : σ • i = j) (R : TestAlgebra K),
      Function.Bijective (componentAtEmbedding A e σ h (R := R))

end CoordinateProjections

section OrbitAssembly

open _root_.LinearAlgebraicGroups.WeilRestriction (Representation)
open _root_.LinearAlgebraicGroups.Descent.Forms (scalarTowerIso)

variable [FiniteDimensional F K]

abbrev Orbits := MulAction.orbitRel.Quotient Gal(K/F) I

abbrev orbitField (i : I) : IntermediateField F K :=
  IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)

/-- The data for one orbit of factors, with the given representative, its
stabilizer comparison and the descended actual representative projection. -/
structure OrbitCoordinates (A : ProductDescent (F := F) (K := K) (I := I)) (i : I) where
  coordinate : HopfAlgebraCategory (orbitField (F := F) (K := K) i)
  finiteType : Algebra.FiniteType (orbitField (F := F) (K := K) i) coordinate
  comparison : extendedHopf K coordinate ≅ A.factor i
  equivariant : IsRepresentativeDescent A i comparison
  projection : coordinate ⟶ extendedHopf (orbitField (F := F) (K := K) i) A.descent.coordinate
  projected : comparison.hom ≫ A.projection i = extendedHopfMap K projection ≫
    (scalarTowerIso A.descent.coordinate).hom ≫ A.descent.comparison.hom

/-- A comparison of a product of group schemes with a product of Weil
representations, expressed on the underlying affine coordinate algebras. -/
def IsWeilCoordinateProjection (A : ProductDescent (F := F) (K := K) (I := I)) {i : I}
    (D : OrbitCoordinates A i)
    (W : Representation F (orbitField (F := F) (K := K) i)
      (CommAlgCat.of _ D.coordinate)) (p : W.coordinate ⟶ CommAlgCat.of F A.descent.coordinate) :
    Prop :=
  ∀ (R : TestAlgebra F) (x : CommAlgCat.of F A.descent.coordinate ⟶ R),
    (show CommAlgCat.of _ D.coordinate ⟶ _ from W.points.hom.app R (p ≫ x)).hom =
      representativeEvaluation (orbitField (F := F) (K := K) i) D.projection x.hom

/-- The known ground-field form of the product has the coproduct coordinate
algebra of the Weil restrictions. The empty family gives the initial
coordinate algebra of the trivial group. -/
def InducedCoordinateProduct : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [Finite I] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)),
    let O := Orbits (F := F) (K := K) (I := I)
    ∀ (D : ∀ o : O, OrbitCoordinates A o.out)
      (W : ∀ o : O, Representation F (orbitField (F := F) (K := K) o.out)
        (CommAlgCat.of _ (D o).coordinate)),
    ∃ p : ∀ o : O, (W o).coordinate ⟶ CommAlgCat.of F A.descent.coordinate,
      (∀ o, IsWeilCoordinateProjection A (D o) (W o) (p o)) ∧
      Nonempty (IsColimit (Cofan.mk (CommAlgCat.of F A.descent.coordinate) p))

end OrbitAssembly

section SchemeProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open _root_.LinearAlgebraicGroups.WeilRestriction (Representation)

variable [FiniteDimensional F K]

/-- Extension of the ground-field test algebra identifies it with the orbit
field, with its given scalar structure. -/
def scalarExtensionOfGroundField (E : Type u) [Field E] [Algebra F E] :
    (extendScalars F E).obj (CommAlgCat.of F F) ≅ CommAlgCat.of E E :=
  CommAlgCat.isoMk
    { (Algebra.TensorProduct.lid F E).toRingEquiv with
      commutes' := fun a => by
        change Algebra.TensorProduct.lid F E (1 ⊗ₜ[F] a) = a
        simp }

def weilFieldPointIso {E : Type u} [Field E] [Algebra F E]
    {G : GroupScheme E} {W : GroupScheme F}
    (e : (groupPointsFunctor F).obj W ≅ extendScalars F E ⋙ (groupPointsFunctor E).obj G) :
    ((groupPointsFunctor F).obj W).obj (CommAlgCat.of F F) ≅
      ((groupPointsFunctor E).obj G).obj (CommAlgCat.of E E) :=
  e.app _ ≪≫ ((groupPointsFunctor E).obj G).mapIso (scalarExtensionOfGroundField E)

/-- Each restriction is tied to its affine coordinates, its representing
group functor, and the actual projection of the ground-field form. -/
structure OrbitWeilRestriction (A : ProductDescent (F := F) (K := K) (I := I)) (i : I) where
  descended : OrbitCoordinates A i
  representation : Representation F (orbitField (F := F) (K := K) i)
    (CommAlgCat.of _ descended.coordinate)
  restriction : AffineAlgebraicGroup F
  coordinateIso : (testSpec F).obj (Opposite.op representation.coordinate) ≅ restriction.val.X
  weil : (groupPointsFunctor F).obj restriction.val ≅
    extendScalars F (orbitField (F := F) (K := K) i) ⋙
      (groupPointsFunctor _).obj (specGroup descended.coordinate)
  represents : ∀ (R : TestAlgebra F) (x : representation.coordinate ⟶ R),
    ((weil.hom.app R) ((testSpec F).map x.op ≫ coordinateIso.hom)).left =
      Spec.map (CommRingCat.ofHom
        (show CommAlgCat.of _ descended.coordinate ⟶ _ from
          representation.points.hom.app R x).hom.toRingHom)
  coordinateProjection : representation.coordinate ⟶ CommAlgCat.of F A.descent.coordinate
  projects : IsWeilCoordinateProjection A descended representation coordinateProjection
  projection : specGroup A.descent.coordinate ⟶ restriction.val
  compares : projection.hom.hom = (testSpec F).map coordinateProjection.op ≫ coordinateIso.hom

/-- On the coordinates of the actual restriction, evaluation at
`σ|L` recovers the original projection at the factor `σ • i`. -/
def InducedWeilSplitProjectionFormula : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)) (i : I)
    (W : OrbitWeilRestriction A i) (σ : Gal(K/F)) (j : I) (h : σ • i = j)
    (R : TestAlgebra K) (x : A.total →ₐ[K] R),
    let L := orbitField (F := F) (K := K) i
    let a := σ.toAlgHom.comp L.val
    let U := (restrictTestAlgebra F K).obj R
    let T := (extendScalars F L).obj U
    let V := orbitTestAlgebra L a R
    letI : Algebra L T := T.algebra
    letI : Algebra L V := V.algebra
    let y : CommAlgCat.of F A.descent.coordinate ⟶ U :=
      ConcreteCategory.ofHom (C := CommAlgCat F) (groundCoordinatePoint A (R := R) x)
    (orbitTestProjection L a R).hom.comp
      (show CommAlgCat.of L W.descended.coordinate ⟶ T from
        W.representation.points.hom.app U (W.coordinateProjection ≫ y)).hom =
      componentAtEmbedding A W.descended.comparison σ h (x.comp (A.projection j).hom.toAlgHom)

/-- The group homomorphism on ground-field points obtained by projecting to
one orbit and evaluating the Weil restriction on the ground field. -/
def orbitFieldProjection {A : ProductDescent (F := F) (K := K) (I := I)} {i : I}
    (W : OrbitWeilRestriction A i) :
    let L := orbitField (F := F) (K := K) i
    ((groupPointsFunctor F).obj (specGroup A.descent.coordinate)).obj (CommAlgCat.of F F) ⟶
    ((groupPointsFunctor L).obj (specGroup W.descended.coordinate)).obj (CommAlgCat.of L L) :=
  ((groupPointsFunctor F).map W.projection).app (CommAlgCat.of F F) ≫
    (weilFieldPointIso W.weil).hom

def InducedWeilProduct : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [Finite I] [MulAction Gal(K/F) I]
    (A : ProductDescent (F := F) (K := K) (I := I)),
    let O := Orbits (F := F) (K := K) (I := I)
    ∃ pieces : ∀ o : O, OrbitWeilRestriction A o.out,
      Nonempty (IsLimit (Fan.mk (specGroup A.descent.coordinate)
        (fun o => (pieces o).projection))) ∧
      ∃ points : ((groupPointsFunctor F).obj (specGroup A.descent.coordinate)).obj
          (CommAlgCat.of F F) ≃*
          (∀ o : O, ((groupPointsFunctor _).obj (specGroup (pieces o).descended.coordinate)).obj
            (CommAlgCat.of _ _)),
        ∀ x o, points x o = orbitFieldProjection (pieces o) x

end SchemeProduct

section MarkedInclusions

open _root_.LinearAlgebraicGroups.WeilRestriction (Representation)

variable [FiniteDimensional F K]

/-- The restrictions of matched closed subgroups of the representatives
are closed subgroups of the same ambient restrictions. -/
def InducedWeilProductInclusions : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [Finite I] [MulAction Gal(K/F) I]
    {A S : ProductDescent (F := F) (K := K) (I := I)} (j : ProductInclusion A S),
    let O := Orbits (F := F) (K := K) (I := I)
    ∀ (W : ∀ o : O, OrbitWeilRestriction A o.out)
      (V : ∀ o : O, OrbitWeilRestriction S o.out),
    ∃ (g : ∀ o : O, (W o).descended.coordinate ⟶ (V o).descended.coordinate)
      (f : ∀ o : O, (V o).restriction.val ⟶ (W o).restriction.val),
      (∀ o, Function.Surjective (g o).hom ∧ IsClosedImmersion (f o).hom.hom.left ∧
        (W o).descended.comparison.hom ≫ j.factor o.out =
          extendedHopfMap K (g o) ≫ (V o).descended.comparison.hom ∧
        specGroupMap j.ground ≫ (W o).projection = (V o).projection ≫ f o ∧
        (groupPointsFunctor F).map (f o) ≫ (W o).weil.hom =
          (V o).weil.hom ≫ Functor.whiskerLeft (extendScalars F (orbitField (F := F) (K := K) o.out))
            ((groupPointsFunctor _).map (specGroupMap (g o)))) ∧
      (∀ o, ((groupPointsFunctor F).map (specGroupMap j.ground)).app (CommAlgCat.of F F) ≫
          orbitFieldProjection (W o) =
        orbitFieldProjection (V o) ≫
          ((groupPointsFunctor _).map (specGroupMap (g o))).app (CommAlgCat.of _ _)) ∧
      ∀ (_hW : IsLimit (Fan.mk (specGroup A.descent.coordinate) (fun o => (W o).projection)))
        (_hV : IsLimit (Fan.mk (specGroup S.descent.coordinate) (fun o => (V o).projection))),
        ∀ x, x ∈ (((groupPointsFunctor F).map (specGroupMap j.ground)).app
          (CommAlgCat.of F F)).hom.range ↔
          ∀ o : O, orbitFieldProjection (W o) x ∈ (((groupPointsFunctor _).map (specGroupMap (g o))).app
            (CommAlgCat.of _ _)).hom.range

end MarkedInclusions

end
end LinearAlgebraicGroups.Specs.QuasiSplitInducedWeilProduct
