import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Specs.QuasiSplitComponentDescent

open AbsoluteDynkinTypes (SupportedOn IsAbsolutelyAlmostSimple)
open Pinning (AttachedDatum BasedRootDatum BasedIso PinnedGroup)
open GeometricRadicals (IsSemisimple IsTorus IsUnipotentRadical)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open UnipotentRadicalIntersection (IsSchemeIntersection)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open RankOneFlag (IsGeometricallyMaximal)
open Unipotent (closedSubgroupAlgebraicGroup)
open RootGroups (AdditiveLine)
open LinearAlgebraicGroups.WeilRestriction (extendScalars)

noncomputable section

abbrev Adjacent := @QuasiSplitPinnedProduct.Adjacent
abbrev componentSetoid := @QuasiSplitPinnedProduct.componentSetoid
abbrev Components := @QuasiSplitPinnedProduct.Components
abbrev component := @QuasiSplitPinnedProduct.component

/-- Vertex permutations preserving the Cartan matrix act on its connected components. -/
def ComponentAction : Prop :=
  ∀ {Γ : Type u} {I : Type v} [Group Γ] [MulAction Γ I] (A : Matrix I I ℤ),
    (∀ σ : Γ, ∀ i j, A (σ • i) (σ • j) = A i j) →
    ∃ ρ : MulAction Γ (Components A),
      letI := ρ
      (∀ σ : Γ, ∀ i : I, σ • component (A := A) i = component (σ • i)) ∧
      (∀ i j : I, component (A := A) i ≠ component j → A i j = 0 ∧ A j i = 0)

abbrev ComponentDatum := @QuasiSplitPinnedProduct.ComponentDatum

/-- Coordinates of the full simply connected datum, with each actual matched
root and coroot pair on a unique connected block. -/
def RootComponentCoordinates : Prop :=
  ∀ {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) [P.IsReduced] (B : P.Base),
    Submodule.span ℤ (Set.range P.coroot) = ⊤ →
    ∃ (x : X ≃ₗ[ℤ] (B.support → ℤ)) (y : Y ≃ₗ[ℤ] (B.support → ℤ)),
      (∀ i j : B.support, x (P.root i.val) j = RootData.integralCartan P B j i) ∧
      (∀ i : B.support, y (P.coroot i.val) = (by classical exact Pi.single i 1)) ∧
      (∀ a b, P.toLinearMap a b = ∑ j, y b j * x a j) ∧
      ∀ i : I, ∃! c : Components (RootData.integralCartan P B),
        SupportedOn {j | component j = c} (x (P.root i), y (P.coroot i))

/-- The connected blocks of a simply connected based datum, with all roots,
coroots and base vertices matched to the corresponding original ones. -/
def RootComponentData : Prop :=
  ∀ {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) [P.IsReduced] (B : P.Base),
    Submodule.span ℤ (Set.range P.coroot) = ⊤ →
    ∃ (x : X ≃ₗ[ℤ] (B.support → ℤ)) (y : Y ≃ₗ[ℤ] (B.support → ℤ)),
      (∀ a b, P.toLinearMap a b = ∑ j, y b j * x a j) ∧
      (∀ i : B.support, y (P.coroot i.val) = (by classical exact Pi.single i 1)) ∧
      ∀ c : Components (RootData.integralCartan P B),
        let S := {j : B.support | component (A := RootData.integralCartan P B) j = c}
        letI : DecidablePred (· ∈ S) := Classical.decPred _
        ∃ (D : ComponentDatum P B c)
          (a : D.datum.I ≃ {i : I // SupportedOn S (x (P.root i), y (P.coroot i))})
          (v : D.datum.X ≃ₗ[ℤ] (S → ℤ)) (w : D.datum.Y ≃ₗ[ℤ] (S → ℤ)),
          (∀ h k, D.datum.datum.toLinearMap h k = ∑ j, w k j * v h j) ∧
          (∀ i, v (D.datum.datum.root i) = fun j => x (P.root (a i).val) j.val) ∧
          (∀ i, w (D.datum.datum.coroot i) = fun j => y (P.coroot (a i).val) j.val) ∧
          ∀ i : D.datum.base.support, (a i.val).val = (D.vertices i).val.val


section Points

variable {Γ I : Type u} {A : Type v} [Group Γ] [MulAction Γ I] [Group A]

/-- A section fixed by transport around its orbit of factors. -/
def equivariantFamilies (transport : Γ → I → MulAut A) : Subgroup (I → A) where
  carrier := {x | ∀ g i, transport g i (x i) = x (g • i)}
  one_mem' g i := map_one (transport g i)
  mul_mem' hx hy g i := (map_mul (transport g i) _ _).trans
    (congrArg₂ (· * ·) (hx g i) (hy g i))
  inv_mem' hx g i := (map_inv (transport g i) _).trans (congrArg Inv.inv (hx g i))

/-- The points of one component fixed by its stabilizer. -/
def componentFixedPoints (transport : Γ → I → MulAut A) (i : I) : Subgroup A where
  carrier := {a | ∀ g : Γ, g • i = i → transport g i a = a}
  one_mem' g _ := map_one (transport g i)
  mul_mem' hx hy g hg := (map_mul (transport g i) _ _).trans
    (congrArg₂ (· * ·) (hx g hg) (hy g hg))
  inv_mem' hx g hg := (map_inv (transport g i) _).trans (congrArg Inv.inv (hx g hg))

/-- Evaluation on an orbit representative identifies invariant sections and
stabilizer-fixed points and preserves every transported subgroup family. -/
def TransitiveComponentPoints : Prop :=
  ∀ {Γ I : Type u} {A : Type v} [Group Γ] [MulAction Γ I] [Group A]
    (transport : Γ → I → MulAut A)
    (i : I), (∀ j : I, ∃ g : Γ, g • i = j) →
    (∀ g h j, transport (g * h) j = transport g (h • j) * transport h j) →
    ∃ e : equivariantFamilies transport ≃* componentFixedPoints transport i,
      (∀ x, (e x).val = x.val i) ∧
      ∀ U : I → Subgroup A,
        (∀ g j, Subgroup.map (transport g j).toMonoidHom (U j) ≤ U (g • j)) →
        ∀ x, (∀ j, x.val j ∈ U j) ↔ (e x).val ∈ U i

end Points

section WeilRestriction

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (F E : Type u) [Field F] [Field E] [Algebra F E]

/-- The ground field extended as a test algebra for restriction of scalars. -/
def scalarExtensionOfGroundField :
    (extendScalars F E).obj (CommAlgCat.of F F) ≅ CommAlgCat.of E E :=
  CommAlgCat.isoMk
    { (Algebra.TensorProduct.lid F E).toRingEquiv with
      commutes' := fun a => by
        change Algebra.TensorProduct.lid F E (1 ⊗ₜ[F] a) = a
        simp }

/-- The field-point isomorphism from the representing isomorphism. -/
def weilFieldPointIso {G : GroupScheme E} {H : GroupScheme F}
    (e : (groupPointsFunctor F).obj H ≅ extendScalars F E ⋙ (groupPointsFunctor E).obj G) :
    ((groupPointsFunctor F).obj H).obj (CommAlgCat.of F F) ≅
      ((groupPointsFunctor E).obj G).obj (CommAlgCat.of E E) :=
  e.app _ ≪≫ ((groupPointsFunctor E).obj G).mapIso (scalarExtensionOfGroundField F E)

/-- The field-point isomorphism is compatible with the actual subgroup inclusions. -/
def WeilFieldPointsRespectInclusions : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    {V H : GroupScheme F} {U G : GroupScheme E} (i : V ⟶ H) (j : U ⟶ G)
    (a : (groupPointsFunctor F).obj V ≅ extendScalars F E ⋙ (groupPointsFunctor E).obj U)
    (b : (groupPointsFunctor F).obj H ≅ extendScalars F E ⋙ (groupPointsFunctor E).obj G),
    (groupPointsFunctor F).map i ≫ b.hom =
      a.hom ≫ Functor.whiskerLeft (extendScalars F E) ((groupPointsFunctor E).map j) →
    ((groupPointsFunctor F).map i).app (CommAlgCat.of F F) ≫ (weilFieldPointIso F E b).hom =
      (weilFieldPointIso F E a).hom ≫ ((groupPointsFunctor E).map j).app (CommAlgCat.of E E)

end WeilRestriction

abbrev BorelPair := @QuasiSplitPinnedPairModel.BorelPair
abbrev Marking := QuasiSplitPinnedPairModel.Marking

variable {F : Type u} [Field F]

/-- A comparison identifies the actual ambient group and the five marked
inclusions. The two groups can originally have different ground fields. -/
structure MarkedComparison {E K : Type u} [Field E] [Field K] [Algebra F K] [Algebra E K]
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup E}
    (M : BorelPair G) (N : BorelPair H) where
  groupIso : (groupBaseChange F K).obj G.val ≅ (groupBaseChange E K).obj H.val
  subgroupIso : ∀ m, (groupBaseChange F K).obj (M.subgroup m).group ≅
    (groupBaseChange E K).obj (N.subgroup m).group
  commutes : ∀ m, (groupBaseChange F K).map (M.subgroup m).inclusion ≫ groupIso.hom =
    (subgroupIso m).hom ≫ (groupBaseChange E K).map (N.subgroup m).inclusion

/-- Scheme products are specified by their projections, with the universal
property also checked on each of the five subgroup schemes. -/
structure MarkedProduct {I : Type u}
    {G : AffineAlgebraicGroup F} {H : I → AffineAlgebraicGroup F}
    (M : BorelPair G) (N : ∀ i, BorelPair (H i)) where
  projection : ∀ i, G.val ⟶ (H i).val
  subgroupProjection : ∀ m i, (M.subgroup m).group ⟶ ((N i).subgroup m).group
  commutes : ∀ m i, (M.subgroup m).inclusion ≫ projection i =
    subgroupProjection m i ≫ ((N i).subgroup m).inclusion
  product : IsLimit (Fan.mk G.val projection)
  subgroupProduct : ∀ m, IsLimit (Fan.mk (M.subgroup m).group (subgroupProjection m))

/-- After scalar extension, an orbit product has projections to the
specified members of the split component family. -/
structure ScalarExtendedMarkedProduct {K I : Type u} [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {H : I → AffineAlgebraicGroup F}
    (M : BorelPair G) (N : ∀ i, BorelPair (H i)) where
  projection : ∀ i, (groupBaseChange F K).obj G.val ⟶
    (groupBaseChange F K).obj (H i).val
  subgroupProjection : ∀ m i, (groupBaseChange F K).obj (M.subgroup m).group ⟶
    (groupBaseChange F K).obj ((N i).subgroup m).group
  commutes : ∀ m i, (groupBaseChange F K).map (M.subgroup m).inclusion ≫ projection i =
    subgroupProjection m i ≫ (groupBaseChange F K).map ((N i).subgroup m).inclusion
  product : IsLimit (Fan.mk _ projection)
  subgroupProduct : ∀ m, IsLimit (Fan.mk _ (subgroupProjection m))

/-- The restriction representing isomorphisms commute with the specified
inclusions for the positive and negative sides and the common torus. -/
structure MarkedWeilRestriction {E : Type u} [Field E] [Algebra F E]
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup E}
    (M : BorelPair G) (N : BorelPair H) where
  groupIso : (groupPointsFunctor F).obj G.val ≅
    extendScalars F E ⋙ (groupPointsFunctor E).obj H.val
  subgroupIso : ∀ m, (groupPointsFunctor F).obj (M.subgroup m).group ≅
    extendScalars F E ⋙ (groupPointsFunctor E).obj (N.subgroup m).group
  commutes : ∀ m, (groupPointsFunctor F).map (M.subgroup m).inclusion ≫ groupIso.hom =
    (subgroupIso m).hom ≫ Functor.whiskerLeft (extendScalars F E)
      ((groupPointsFunctor E).map (N.subgroup m).inclusion)

/-- Products of marked restrictions induce the actual field-point isomorphism,
compatible with all of the signed radical inclusions. -/
def MarkedProductFieldPoints : Prop :=
  ∀ {F I : Type u} [Field F] [Finite I] (E : I → Type u) [∀ i, Field (E i)] [∀ i, Algebra F (E i)]
    {G : AffineAlgebraicGroup F} {H : I → AffineAlgebraicGroup F}
    (M : BorelPair G) (N : ∀ i, BorelPair (H i))
    {J : ∀ i, AffineAlgebraicGroup (E i)} (W : ∀ i, BorelPair (J i))
    (prod : MarkedProduct M N) (weil : ∀ i, MarkedWeilRestriction (N i) (W i)),
    ∃ e : ((groupPointsFunctor F).obj G.val).obj (CommAlgCat.of F F) ≃*
        (∀ i, ((groupPointsFunctor (E i)).obj (J i).val).obj (CommAlgCat.of _ _)),
      (∀ x i, e x i = (weilFieldPointIso F (E i) (weil i).groupIso).hom
        (((groupPointsFunctor F).map (prod.projection i)).app _ x)) ∧
      ∀ m x,
        x ∈ (((groupPointsFunctor F).map (M.subgroup m).inclusion).app (CommAlgCat.of F F)).hom.range ↔
        ∀ i, e x i ∈ (((groupPointsFunctor (E i)).map ((W i).subgroup m).inclusion).app
          (CommAlgCat.of _ _)).hom.range


abbrev simplePermutation := QuasiSplitPinnedProduct.simplePermutation

open AdjointBorelCohomology (PinnedTwist)

/-- The connected-component relation agrees with the relation defined by
the edge multiplicities of the actual integral Dynkin diagram. -/
def DiagramAdjacency : Prop :=
  ∀ {I X Y : Type u} [Finite I] [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (B : P.Base) (i j : B.support),
    Adjacent (RootData.integralCartan P B) i j ↔
      (AbsoluteDynkinTypes.integralDiagram (RootData.integralCartan P B)).edges i j ≠ 0

/-- Any based action induces the actual action on connected components. -/
def BasedComponentAction : Prop :=
  ∀ {Γ : Type u} [Group Γ] (D : BasedRootDatum.{u}) (ω : Γ →* Aut D),
    let A := RootData.integralCartan D.datum D.base
    ∃ ρ : MulAction Γ (Components A), letI := ρ
    ∀ σ : Γ, ∀ i : D.base.support,
      σ • component (A := A) i = component (A := A) (simplePermutation D (ω σ) i)

/-- A block indexed by a connected component has a nonempty connected
diagram, with the edges prescribed by the original Cartan pairing. -/
def ComponentDiagramConnected : Prop :=
  ∀ (D : BasedRootDatum.{u}) {c : Components (RootData.integralCartan D.datum D.base)}
    (B : ComponentDatum D.datum D.base c),
    (AbsoluteDynkinTypes.integralDiagram
      (RootData.integralCartan B.datum.datum B.datum.base)).IsConnected

/-- Each based automorphism identifies the full root datum of a block with
that of the permuted block. On a fixed block the lifts form an action of
its stabilizer and agree with the transports. -/
def BasedComponentTransport : Prop :=
  ∀ {Γ : Type u} [Group Γ] (D : BasedRootDatum.{u}) (ω : Γ →* Aut D),
    let A := RootData.integralCartan D.datum D.base
    ∀ [MulAction Γ (Components A)],
    (∀ σ : Γ, ∀ i : D.base.support,
      σ • component (A := A) i = component (A := A) (simplePermutation D (ω σ) i)) →
    ∀ B : ∀ c : Components A, ComponentDatum D.datum D.base c,
    ∃ e : ∀ (σ : Γ) c, BasedIso (B c).datum (B (σ • c)).datum,
      (∀ (σ : Γ) c (i : (B c).datum.base.support) (j : (B (σ • c)).datum.base.support),
        (e σ c).val.indexEquiv i.val = j.val ↔
          simplePermutation D (ω σ) ((B c).vertices i).val = ((B (σ • c)).vertices j).val) ∧
      ∀ c, ∃ s : MulAction.stabilizer Γ c →* Aut (B c).datum,
        ∀ (σ : MulAction.stabilizer Γ c),
          (s σ).asIso.hom = e σ.val c ≫
            eqToHom (congrArg (fun d => (B d).datum) (MulAction.mem_stabilizer_iff.mp σ.property))

/-- Realizations of the blocks transport as pinned groups, including a
genuine pinned automorphism action of each component stabilizer. -/
def PinnedComponentTransport : Prop :=
  ∀ {F Γ : Type u} [Field F] [Group Γ] (A : AdditiveLine F)
    (D : BasedRootDatum.{u}) (ω : Γ →* Aut D),
    let C := Components (RootData.integralCartan D.datum D.base)
    ∀ [MulAction Γ C],
    (∀ σ : Γ, ∀ i : D.base.support,
      σ • component (A := RootData.integralCartan D.datum D.base) i =
        component (A := RootData.integralCartan D.datum D.base) (simplePermutation D (ω σ) i)) →
    ∀ B : ∀ c : C, ComponentDatum D.datum D.base c,
    ∃ (Q : C → PinnedGroup A) (T : ∀ c, AttachedDatum (Q c).pair)
      (a : ∀ c, BasedIso (B c).datum (T c).toBased)
      (transport : ∀ (σ : Γ) c, Pinning.PinnedIso (Q c) (Q (σ • c))),
      (∀ c, IsSemisimple (Q c).pair.G ∧ GeometricallySimplyConnected (Q c).pair.G) ∧
      (∀ (σ : Γ) c (i : (B c).datum.base.support) (j : (B (σ • c)).datum.base.support),
        simplePermutation D (ω σ) ((B c).vertices i).val = ((B (σ • c)).vertices j).val →
        (transport σ c).torus.inv ≫ ((a c).val.indexEquiv i.val).val =
          ((a (σ • c)).val.indexEquiv j.val).val) ∧
      ∀ c, ∃ s : MulAction.stabilizer Γ c →* Aut (Q c),
        ∀ (σ : MulAction.stabilizer Γ c),
          (s σ).asIso.hom = transport σ.val c ≫ eqToHom
            (congrArg Q (MulAction.mem_stabilizer_iff.mp σ.property))


/-- Embeddings of the stabilizer's fixed field are exactly the components
in the orbit, with the natural Galois permutation action. -/
def OrbitFieldEmbeddings : Prop :=
  ∀ {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] [MulAction Gal(K/F) I] (i : I),
    (∀ j : I, ∃ σ : Gal(K/F), σ • i = j) →
    let L := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
    ∃ e : I ≃ (L →ₐ[F] K), e i = L.val ∧
      ∀ σ : Gal(K/F), ∀ j, e (σ • j) = σ.toAlgHom.comp (e j)

/-- Over a finite Galois splitting field the tensor algebra of an
intermediate field is the product indexed by its embeddings. -/
def OrbitFieldTensorSplitting : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (L : IntermediateField F K),
    ∃ e : K ⊗[F] L ≃ₐ[K] ((L →ₐ[F] K) → K),
      ∀ r l a, e (r ⊗ₜ[F] l) a = r * a l

/-- The tensor algebra in the Weil restriction splits over every test
algebra over the Galois field, naturally and with the stated embeddings. -/
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

section OrbitTestAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {K : Type u} [Field K] [Algebra F K] (L : IntermediateField F K)

/-- Regard a test algebra as an algebra over the orbit field through a
specified embedding of that field into the Galois field. -/
def orbitTestAlgebra (a : L →ₐ[F] K) (R : TestAlgebra K) : TestAlgebra L :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  (restrictTestAlgebra L K).obj R

/-- Evaluate the scalar tensor algebra at an embedding of the orbit field. -/
def orbitTestProjection (a : L →ₐ[F] K) (R : TestAlgebra K) :
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

/-- The actual evaluation morphisms display the extended test algebra as
the categorical product of the algebras with the corresponding scalar structures. -/
def OrbitTestAlgebraProduct : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (L : IntermediateField F K) (R : TestAlgebra K),
    Nonempty (IsLimit (Fan.mk ((extendScalars F L).obj ((restrictTestAlgebra F K).obj R))
      (fun a => orbitTestProjection L a R)))

/-- The base change of a group through one embedding of the orbit field. -/
def orbitBaseChangedGroup (a : L →ₐ[F] K) (H : GroupScheme L) : GroupScheme K :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  (groupBaseChange L K).obj H

/-- The usual base-change point comparison with the scalar structure
chosen by the indicated embedding. -/
def orbitBaseChangePoint (a : L →ₐ[F] K) (H : GroupScheme L) (R : TestAlgebra K)
    (p : Points (orbitBaseChangedGroup L a H).X R) : Points H.X (orbitTestAlgebra L a R) :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  baseChangePoint L K H.X R p

/-- The projection characterizing one factor of the split Weil restriction. -/
def IsWeilProjection (a : L →ₐ[F] K) {W : GroupScheme F} {H : GroupScheme L}
    (e : (groupPointsFunctor F).obj W ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj H)
    (p : (groupBaseChange F K).obj W ⟶ orbitBaseChangedGroup L a H) : Prop :=
  ∀ (R : TestAlgebra K) (x : Points ((groupBaseChange F K).obj W).X R),
    orbitBaseChangePoint L a H R (x ≫ p.hom.hom) =
      ((groupPointsFunctor L).obj H).map (orbitTestProjection L a R)
        (e.hom.app ((restrictTestAlgebra F K).obj R) (baseChangePoint F K W.X R x))

/-- The split base change of a representing Weil restriction is the product
over the embeddings of the orbit field, with its canonical projections. -/
def WeilRestrictionBaseChangeProduct : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (L : IntermediateField F K)
    (W : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup L)
    (e : (groupPointsFunctor F).obj W.val ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj H.val),
    ∃ p : ∀ a : L →ₐ[F] K,
        (groupBaseChange F K).obj W.val ⟶ orbitBaseChangedGroup L a H.val,
      Nonempty (IsLimit (Fan.mk _ p)) ∧
      ∀ a, IsWeilProjection L a e (p a)

/-- The actual projections from a split Weil restriction preserve the
commuting squares for morphisms and closed inclusions. -/
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

end OrbitTestAlgebra

/-- Each actual connected block admits a split pinned simply connected
semisimple realization, with its full based datum identified. -/
def PinnedComponentModels : Prop :=
  ∀ {F : Type u} [Field F] {A : AdditiveLine F} (P : PinnedGroup A)
    (D : AttachedDatum P.pair),
    corootLattice D = ⊤ →
    let B := D.toBased
    ∃ (block : ∀ c, ComponentDatum B.datum B.base c)
      (Q : Components (RootData.integralCartan B.datum B.base) → PinnedGroup A)
      (T : ∀ c, AttachedDatum (Q c).pair),
      ∀ c, IsSemisimple (Q c).pair.G ∧ GeometricallySimplyConnected (Q c).pair.G ∧
        Nonempty (BasedIso (block c).datum (T c).toBased)

/-- With a full coroot lattice, an empty diagram gives the empty marked
product, including the trivial radicals and torus. -/
def EmptyMarkedSplitProduct : Prop :=
  ∀ {F : Type u} [Field F] (P : Pinning.SplitBorelPair F) (D : AttachedDatum P)
    (M : BorelPair P.G),
    corootLattice D = ⊤ → IsEmpty D.toBased.base.support →
    ∀ {I : Type u} [IsEmpty I] {H : I → AffineAlgebraicGroup F}
      (N : ∀ i, BorelPair (H i)), Nonempty (MarkedProduct M N)


section CoordinateDescent

open _root_.LinearAlgebraicGroups.Descent (HopfDescentDatum HopfDescent SemilinearAction)

/-- Rational points of an effective descent over every test algebra. The
extension of a coordinate point is equivariant and preserves convolution. -/
def DescendedCoordinatePoints : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [IsGalois F K]
    {A : HopfAlgebraCategory K} (D : HopfDescentDatum F A) (H : HopfDescent D)
    (_he : (SemilinearAction.scalarExtension (K := K) D.fixed).Equivariant
      D.action H.iso.hom.hom.toLinearMap) (R : TestAlgebra F),
    letI := H.operations.toHopfAlgebra
    ∃ e : (H.algebra →ₐ[F] R) ≃
      {f : A →ₐ[K] K ⊗[F] R //
        ∀ (σ : Gal(K/F)) x, f (D.action.act σ x) =
          (SemilinearAction.scalarExtension (K := K) R).act σ (f x)},
      (∀ f x, (e f).val (H.iso.hom.hom (1 ⊗ₜ[F] x)) = 1 ⊗ₜ[F] (f x)) ∧
      ∀ f g : WithConv (H.algebra →ₐ[F] R),
        WithConv.toConv (e (f * g).ofConv).val =
          WithConv.toConv (e f.ofConv).val * WithConv.toConv (e g.ofConv).val

end CoordinateDescent



open AdjointCocharacters (coordinateHopf coordinateHopfIso coordinateHopfMap)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open _root_.LinearAlgebraicGroups.Descent.Forms (spectrumIso IsScalarExtensionComparison)

/-- The comparison with the form over a fixed field intertwines its scalar
action with the one twisted by the specified stabilizer automorphisms. -/
def IsStabilizerCoordinateComparison {K : Type u} [Field K] [Algebra F K]
    [FiniteDimensional F K] (J : Subgroup Gal(K/F)) {P : AffineAlgebraicGroup F}
    (a : J →* Aut P.val) {H : AffineAlgebraicGroup (IntermediateField.fixedField J)}
    (i : extendedHopf K (coordinateHopf P) ≅ extendedHopf K (coordinateHopf H)) : Prop :=
  let L := IntermediateField.fixedField J
  ∀ (σ : Gal(K/L)) (x : extendedHopf K (coordinateHopf P)),
    let s : J := ⟨σ.restrictScalars F, by
      rw [← IntermediateField.fixingSubgroup_fixedField J]
      exact (L.fixingSubgroupEquiv.symm σ).property⟩
    (SemilinearAction.scalarExtension (K := K) (coordinateHopf H)).act σ (i.hom.hom x) =
      i.hom.hom ((extendedHopfMap K
        (coordinateHopfMap (G := P) (H := P) (a s).asIso.inv)).hom
        ((SemilinearAction.scalarExtension (K := K) (coordinateHopf P)).act s.val x))

/-- Finite Galois descent over the fixed field of a subgroup, using the
given ground-field automorphisms as coefficients of the semilinear action. -/
def StabilizerGroupDescent : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (J : Subgroup Gal(K/F)) (P : AffineAlgebraicGroup F)
    (a : J →* Aut P.val),
    ∃ (H : AffineAlgebraicGroup (IntermediateField.fixedField J))
      (i : extendedHopf K (coordinateHopf P) ≅ extendedHopf K (coordinateHopf H)),
      IsStabilizerCoordinateComparison J a i

/-- All closed subgroup schemes equipped with the induced stabilizer action
descend inside the same descended ambient group. Their actual inclusion maps
are identified by the two Hopf comparisons. -/
def StabilizerSubgroupsDescent : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsGalois F K] (J : Subgroup Gal(K/F)) (P : AffineAlgebraicGroup F)
    (a : J →* Aut P.val),
    ∃ (H : AffineAlgebraicGroup (IntermediateField.fixedField J))
      (i : extendedHopf K (coordinateHopf P) ≅ extendedHopf K (coordinateHopf H)),
      IsStabilizerCoordinateComparison J a i ∧
      ∀ (S : ClosedSubgroup P.val) (b : J →* Aut S.group),
        (∀ σ : J, S.inclusion ≫ (a σ).asIso.inv = (b σ).asIso.inv ≫ S.inclusion) →
        ∃ (V : ClosedSubgroup H.val)
          (j : extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup S)) ≅
            extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup V))),
          IsStabilizerCoordinateComparison J b j ∧
          i.hom ≫ extendedHopfMap K (coordinateHopfMap
              (G := closedSubgroupAlgebraicGroup V) (H := H) V.inclusion) =
            extendedHopfMap K (coordinateHopfMap
              (G := closedSubgroupAlgebraicGroup S) (H := P) S.inclusion) ≫ j.hom

/-- The comparison on schemes is the one obtained from the inverse
pullback of the indicated Hopf algebra isomorphism. -/
def MatchesCoordinateComparison {E K : Type u} [Field E] [Field K] [Algebra F K] [Algebra E K]
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup E}
    {M : BorelPair G} {N : BorelPair H} (j : MarkedComparison (K := K) M N)
    (i : extendedHopf K (coordinateHopf G) ≅ extendedHopf K (coordinateHopf H)) : Prop :=
  ∃ (tF : ∀ A : HopfAlgebraCategory F,
        specGroup (extendedHopf K A) ≅ (groupBaseChange F K).obj (specGroup A))
      (tE : ∀ A : HopfAlgebraCategory E,
        specGroup (extendedHopf K A) ≅ (groupBaseChange E K).obj (specGroup A)),
    IsScalarExtensionComparison tF ∧ IsScalarExtensionComparison tE ∧
    j.groupIso =
      ((groupBaseChange F K).mapIso (coordinateHopfIso G)).symm ≪≫
        (tF (coordinateHopf G)).symm ≪≫ spectrumIso i ≪≫ tE (coordinateHopf H) ≪≫
        (groupBaseChange E K).mapIso (coordinateHopfIso H)

/-- A simultaneous coordinate comparison of a pair and its marked inclusions
induces the corresponding comparison of all the subgroup schemes. -/
def MarkedComparisonOfHopf : Prop :=
  ∀ {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F K] [Algebra E K]
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup E}
    (M : BorelPair G) (N : BorelPair H)
    (i : extendedHopf K (coordinateHopf G) ≅ extendedHopf K (coordinateHopf H))
    (d : ∀ m, extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup (M.subgroup m))) ≅
      extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup (N.subgroup m)))),
    (∀ m, i.hom ≫ extendedHopfMap K (coordinateHopfMap
        (G := closedSubgroupAlgebraicGroup (N.subgroup m)) (H := H) (N.subgroup m).inclusion) =
      extendedHopfMap K (coordinateHopfMap
        (G := closedSubgroupAlgebraicGroup (M.subgroup m)) (H := G) (M.subgroup m).inclusion) ≫
        (d m).hom) →
    ∃ j : MarkedComparison (K := K) M N, MatchesCoordinateComparison j i

/-- The marked split product has the actual paired lattices of the individual
blocks and the projections on the torus and root coordinates. -/
structure SplitComponents {A : AdditiveLine F} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) (S : BorelPair P.pair.G) where
  factors : QuasiSplitPinnedProduct.PinnedFactors D
  pairs : ∀ c, BorelPair (factors.factor c).pair.G
  positive_eq : ∀ c, (pairs c).positive = (factors.factor c).pair.B
  torus_eq : ∀ c, (pairs c).torus = (factors.factor c).pair.T
  absolutelyAlmostSimple : ∀ c, IsAbsolutelyAlmostSimple (factors.factor c).pair.G
  product : MarkedProduct S pairs
  torusProjection : ∀ c, P.pair.T.group ⟶ (factors.factor c).pair.T.group
  torusSquare : ∀ c, P.pair.T.inclusion ≫ product.projection c =
    torusProjection c ≫ (factors.factor c).pair.T.inclusion
  torusBlock : ∀ c, QuasiSplitPinnedProduct.IsBlockTorusProjection factors c (torusProjection c)
  pinProjection : ∀ (i : D.toBased.base.support) c (h : component i = c),
    QuasiSplitPinnedProduct.pinnedCoordinate P (QuasiSplitPinnedProduct.labeledSimpleRoot D i) ≫
      product.projection c = QuasiSplitPinnedProduct.pinnedCoordinate (factors.factor c)
        (QuasiSplitPinnedProduct.factorSimpleRoot factors c ⟨i, h⟩)
  pinProjectionOutside : ∀ (i : D.toBased.base.support) c, component i ≠ c →
    QuasiSplitPinnedProduct.pinnedCoordinate P (QuasiSplitPinnedProduct.labeledSimpleRoot D i) ≫
      product.projection c = 0
  equivariance : ∀ (a : Aut D.toBased) (f : Pinning.PinnedIso P P),
    QuasiSplitPinnedProduct.LiftsBasedAutomorphism D a f →
    ∃ (g : Equiv.Perm (QuasiSplitPinnedProduct.DatumComponents D.toBased))
      (e : ∀ c, Pinning.PinnedIso (factors.factor c) (factors.factor (g c))),
      (∀ i : D.toBased.base.support,
        g (component i) = component (simplePermutation D.toBased a i)) ∧
      ∀ c, f.group.hom ≫ product.projection (g c) = product.projection c ≫ (e c).group.hom

section OrbitFactors

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

open QuasiSplitInducedWeilProduct (IsCoordinateProduct ProductDescent OrbitWeilRestriction)
open QuasiSplitPinnedPairModel (IsBasedLift IsTransportedBasedAction)
open LinearAlgebraicGroups.Descent (HopfDescentDatum)

variable {K I : Type u} [Field K] [Algebra F K] [MulAction Gal(K/F) I]

abbrev extensionCoordinates (P : AffineAlgebraicGroup F) :=
  extendedHopf K (coordinateHopf P)

abbrev projectionCoordinates {P Q : AffineAlgebraicGroup F} (f : P.val ⟶ Q.val) :
    extensionCoordinates (K := K) Q ⟶ extensionCoordinates (K := K) P :=
  extendedHopfMap K (coordinateHopfMap f)

/-- The coordinate descent uses the specified split product projections
and comparison with the specified ground-field form. -/
structure ProjectedDescent {P G : AffineAlgebraicGroup F} {Q : I → AffineAlgebraicGroup F}
    (p : ∀ c, P.val ⟶ (Q c).val)
    (e : extensionCoordinates (K := K) P ≅ extensionCoordinates (K := K) G) where
  finiteType : ∀ c, Algebra.FiniteType K (extensionCoordinates (K := K) (Q c))
  product : IsCoordinateProduct (fun c => projectionCoordinates (P := P) (K := K) (Q := Q c) (p c))
  datum : HopfDescentDatum F (extensionCoordinates (K := K) P)
  equivariant : ∀ σ x, e.inv.hom ((SemilinearAction.scalarExtension (coordinateHopf G)).act σ x) =
    datum.action.act σ (e.inv.hom x)
  transport : ∀ (σ : Gal(K/F)) (c j : I), σ • c = j →
    extensionCoordinates (K := K) (Q c) ≃+* extensionCoordinates (K := K) (Q j)
  transportScalar : ∀ σ c j h r, transport σ c j h (algebraMap K _ r) = algebraMap K _ (σ r)
  transportProjection : ∀ σ c j h x,
    (projectionCoordinates (P := P) (Q := Q j) (p j)).hom (transport σ c j h x) =
      datum.action.act σ ((projectionCoordinates (P := P) (Q := Q c) (p c)).hom x)

/-- The same coordinate diagram in the general finite-product descent interface. -/
def ProjectedDescent.productDescent {P G : AffineAlgebraicGroup F} {Q : I → AffineAlgebraicGroup F}
    {p : ∀ c, P.val ⟶ (Q c).val}
    {e : extensionCoordinates (K := K) P ≅ extensionCoordinates (K := K) G}
    (d : ProjectedDescent p e) : ProductDescent (F := F) (K := K) (I := I) where
  total := extensionCoordinates P
  factor c := extensionCoordinates (Q c)
  finiteType := d.finiteType
  projection c := projectionCoordinates (p c)
  product := d.product
  datum := d.datum
  transport := d.transport
  transportScalar := d.transportScalar
  transportProjection := d.transportProjection
  descent := ⟨coordinateHopf G, e.symm, d.equivariant⟩

variable [FiniteDimensional F K]

abbrev orbitField (c : I) := QuasiSplitInducedWeilProduct.orbitField (F := F) (K := K) c

/-- The affine group over the stabilizer field supplied by the orbit
descent. -/
abbrev descendedGroup {A : ProductDescent (F := F) (K := K) (I := I)} {c : I}
    (W : OrbitWeilRestriction A c) : AffineAlgebraicGroup (orbitField (F := F) (K := K) c) :=
  LinearAlgebraicGroups.Descent.Forms.schemeModel W.descended.coordinate W.descended.finiteType

/-- The subgroup inclusions of one descended factor and of its Weil
restriction, with the same representing isomorphism on the ambient group. -/
structure OrbitFactor (A : ProductDescent (F := F) (K := K) (I := I)) (c : I)
    {P : AffineAlgebraicGroup F} (S : BorelPair P) where
  orbit : OrbitWeilRestriction A c
  pair : BorelPair (descendedGroup orbit)
  quasiSplit : GeometricBorelConjugacy.IsQuasiSplit (descendedGroup orbit)
  absolutelyAlmostSimple : IsAbsolutelyAlmostSimple (descendedGroup orbit)
  simplyConnected : GeometricallySimplyConnected (descendedGroup orbit)
  comparison : MarkedComparison (K := K) S pair
  comparisonCoordinate : extendedHopf K (coordinateHopf P) ≅
    extendedHopf K (coordinateHopf (descendedGroup orbit))
  comparisonMatches : MatchesCoordinateComparison comparison comparisonCoordinate
  factorPresentation : extensionCoordinates (K := K) P = A.factor c
  comparisonPresents :
    ∃ e : coordinateHopf (descendedGroup orbit) ≅ orbit.descended.coordinate,
      specGroupMap e.hom = (coordinateHopfIso (descendedGroup orbit)).inv ∧
      comparisonCoordinate.hom ≫ extendedHopfMap K e.hom =
        eqToHom factorPresentation ≫ orbit.descended.comparison.inv
  restrictedSubgroup : Marking → ClosedSubgroup orbit.restriction.val
  weilSubgroup : ∀ m, (groupPointsFunctor F).obj (restrictedSubgroup m).group ≅
    extendScalars F (orbitField (F := F) (K := K) c) ⋙ (groupPointsFunctor _).obj (pair.subgroup m).group
  weilCommutes : ∀ m, (groupPointsFunctor F).map (restrictedSubgroup m).inclusion ≫ orbit.weil.hom =
    (weilSubgroup m).hom ≫ Functor.whiskerLeft (extendScalars F (orbitField (F := F) (K := K) c))
      ((groupPointsFunctor _).map (pair.subgroup m).inclusion)

/-- The actual product of the orbit restrictions, with the corresponding
product of each marked subgroup scheme. -/
structure OrbitProduct {G : AffineAlgebraicGroup F}
    (M : BorelPair G) {Q : I → AffineAlgebraicGroup F} {S : ∀ c, BorelPair (Q c)}
    {A : ProductDescent (F := F) (K := K) (I := I)}
    (W : ∀ o : MulAction.orbitRel.Quotient Gal(K/F) I, OrbitFactor A o.out (S o.out)) where
  project : ∀ o, G.val ⟶ (W o).orbit.restriction.val
  markedProject : ∀ m o, (M.subgroup m).group ⟶ ((W o).restrictedSubgroup m).group
  projectCommutes : ∀ m o, (M.subgroup m).inclusion ≫ project o =
    markedProject m o ≫ ((W o).restrictedSubgroup m).inclusion
  product : IsLimit (Fan.mk G.val project)
  markedProduct : ∀ m, IsLimit (Fan.mk (M.subgroup m).group (markedProject m))

/-- The statement at a finite pinned splitting layer. The orbit field is
the fixed field of the stabilizer of the chosen diagram component. -/
def DescentOfSplitComponents {G : AffineAlgebraicGroup F}
    {M : BorelPair G} {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {S : BorelPair P.pair.G}
    (w : PinnedTwist K D l M.positive M.torus) (W : SplitComponents D S)
    [MulAction Gal(K/F) (QuasiSplitPinnedProduct.DatumComponents D.toBased)] : Prop :=
  let C := QuasiSplitPinnedProduct.DatumComponents D.toBased
  let O := MulAction.orbitRel.Quotient Gal(K/F) C
  ∃ (t : ∀ (σ : Gal(K/F)) c, Pinning.PinnedIso (W.factors.factor c) (W.factors.factor (σ • c)))
    (d : ProjectedDescent W.product.projection w.groupIso)
    (pieces : ∀ o : O, OrbitFactor d.productDescent o.out (W.pairs o.out))
    (p : OrbitProduct M pieces),
    (∀ σ c, (l (w.outer σ)).asIso.hom.group.hom ≫ W.product.projection (σ • c) =
      W.product.projection c ≫ (t σ c).group.hom) ∧
    (∀ σ c j (h : σ • c = j) x,
      let e : (W.factors.factor c).pair.G.val ≅ (W.factors.factor j).pair.G.val :=
        h ▸ (t σ c).group
      d.transport σ c j h x = (projectionCoordinates (K := K)
        (P := (W.factors.factor j).pair.G) (Q := (W.factors.factor c).pair.G) e.inv).hom
          ((SemilinearAction.scalarExtension (coordinateHopf (W.factors.factor c).pair.G)).act σ x)) ∧
    (∀ o, p.project o = (coordinateHopfIso G).inv ≫ (pieces o).orbit.projection) ∧
    ∃ (points : ((groupPointsFunctor F).obj G.val).obj (CommAlgCat.of F F) ≃*
        (∀ o : O, ((groupPointsFunctor _).obj (descendedGroup (pieces o).orbit).val).obj
          (CommAlgCat.of _ _))),
      (∀ x o, points x o =
        (weilFieldPointIso F _ (pieces o).orbit.weil).hom
          (((groupPointsFunctor F).map (p.project o)).app _ x)) ∧
      ∀ m x,
        x ∈ (((groupPointsFunctor F).map (M.subgroup m).inclusion).app
          (CommAlgCat.of F F)).hom.range ↔
        ∀ o : O, points x o ∈
          (((groupPointsFunctor _).map ((pieces o).pair.subgroup m).inclusion).app
            (CommAlgCat.of _ _)).hom.range

end OrbitFactors

/-- Component decomposition for a geometrically simply connected
semisimple group with its specified opposite rational Borel pair. -/
def Statement : Prop :=
  ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F),
    IsSemisimple G → GeometricallySimplyConnected G → ∀ M : BorelPair G,
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (_ : IsGalois F K) (A : AdditiveLine F) (P : PinnedGroup A)
      (D : AttachedDatum P.pair) (lift : Aut D.toBased ≃* Aut P)
      (twist : PinnedTwist K D lift M.positive M.torus) (S : BorelPair P.pair.G),
      S.positive = P.pair.B ∧ S.torus = P.pair.T ∧ corootLattice D = ⊤ ∧
      QuasiSplitPinnedPairModel.IsBasedLift D lift ∧
      QuasiSplitPinnedPairModel.IsTransportedBasedAction twist ∧
      (∃ cmp : QuasiSplitPinnedPairModel.MarkedComparison (K := K) S M,
        QuasiSplitPinnedPairModel.MatchesCoordinateComparison cmp twist.groupIso) ∧
      ∃ (W : SplitComponents D S) (ρ : MulAction Gal(K/F)
          (QuasiSplitPinnedProduct.DatumComponents D.toBased)),
        letI := ρ
        (∀ σ : Gal(K/F), ∀ a : D.toBased.base.support,
          σ • component (A := RootData.integralCartan D.toBased.datum D.toBased.base) a =
            component (A := RootData.integralCartan D.toBased.datum D.toBased.base)
              (simplePermutation D.toBased (twist.outer σ) a)) ∧
        DescentOfSplitComponents twist W


end

end LinearAlgebraicGroups.Specs.QuasiSplitComponentDescent
