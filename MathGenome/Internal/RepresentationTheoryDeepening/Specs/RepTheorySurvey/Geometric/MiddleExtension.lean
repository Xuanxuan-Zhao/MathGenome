import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedLocalSheaves
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.IntersectionComplexes

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace RepTheorySurvey.Geometric.Analytic.IntersectionComplex

/-- The closed complement of the image of the open inclusion. -/
def boundary {U X : TopCat.{u}} (j : U ⟶ X) : Set X :=
  (Set.range j)ᶜ

theorem boundary_isClosed {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j) :
    IsClosed (boundary j) :=
  hj.isOpen_range.isClosed_compl

/-- The strata of an attachment consist of the previous strata and the new closed
stratum of smaller complex dimension. The ranges specify the actual subspaces
regardless of the open neighborhoods used to exhibit local closedness. -/
structure AttachmentStratification {U X : TopCat.{u}} (j : U ⟶ X) (s : ℕ)
    (P : Stratification U) (Q : Stratification X) where
  closedIndex : Q.Index
  previousIndex : P.Index ≃ {q : Q.Index // q ≠ closedIndex}
  closedRange : Set.range (Q.stratum closedIndex).inclusion = boundary j
  closedDimension : (Q.stratum closedIndex).complexDimension = s
  previousRange (p : P.Index) :
    Set.range (Q.stratum (previousIndex p).val).inclusion =
      j '' Set.range (P.stratum p).inclusion
  previousDimension (p : P.Index) :
    (Q.stratum (previousIndex p).val).complexDimension = (P.stratum p).complexDimension
  dimension_lt (p : P.Index) : s < (P.stratum p).complexDimension

/-- Bounded, locally constant finite-rank cohomology on the new stratum. -/
def IsConstructibleOnBoundary {U X : TopCat.{u}} (j : U ⟶ X) (F : BoundedBelow X) : Prop :=
  let i := closedInclusion (boundary j)
  let G := (derivedInverseImage i).obj F.obj
  (Set.Finite {n : ℤ | ¬ IsZero ((cohomology _ n).obj G)}) ∧
    ∀ n : ℤ, LocallyConstantFiniteRank ((cohomology _ n).obj G)

/-- The two strict conditions on the new stratum of complex dimension `s`. -/
def IsStrictExtension {U X : TopCat.{u}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) (s : ℕ) (F : BoundedBelow X) : Prop :=
  let i := closedInclusion (boundary j)
  ((boundedBelowInverseImage i).obj F).IsLE (-(s : ℤ) - 1) ∧
    ((derivedExtraordinaryInverseImage (boundary_isClosed hj)).obj F).IsGE (-(s : ℤ) + 1)

/-- The open restriction on the full subcategory of objects satisfying the strict bounds. -/
def strictRestriction {U X : TopCat.{u}} {j : U ⟶ X} (hj : IsOpenEmbedding j) (s : ℕ) :
    (show ObjectProperty (BoundedBelow X) from IsStrictExtension hj s).FullSubcategory ⥤
      BoundedBelow U :=
  ObjectProperty.ι _ ⋙ boundedBelowInverseImage j

/-- The canonical inclusion of the ordinary upper truncation into the derived direct image. -/
def attachmentInclusion {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j) (s : ℕ) :
    attachment j hj s ⟶ derivedDirectImage j where
  app F := ObjectProperty.homMk (attachmentι j hj s F)
  naturality F G f := by
    apply ObjectProperty.hom_ext
    exact ((DerivedCategory.TStructure.t (C := Sheaves X)).truncLEι (-(s : ℤ) - 1)).naturality
      ((derivedDirectImage j).map f).hom

/-- The ordinary derived pullback composition comparison on bounded-below objects. -/
def boundedBelowPullbackComposition {V U X : TopCat.{u}} (k : V ⟶ U) (j : U ⟶ X) :
    boundedBelowInverseImage (k ≫ j) ≅
      boundedBelowInverseImage j ⋙ boundedBelowInverseImage k :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ ((derivedInverseImageComposition k j).app F.obj))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (derivedInverseImageComposition k j).hom.naturality f.hom)

/-- The pullback comparison for a commutative square with vertical maps `e` and `v`. -/
def pullbackSquare {U X V Y : TopCat.{u}} {j : U ⟶ X} {k : V ⟶ Y}
    {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k) :
    boundedBelowInverseImage e ⋙ boundedBelowInverseImage j ≅
      boundedBelowInverseImage k ⋙ boundedBelowInverseImage v :=
  (boundedBelowPullbackComposition j e).symm ≪≫
    eqToIso (congrArg (fun f => boundedBelowInverseImage f) h) ≪≫
    boundedBelowPullbackComposition v k

/-- The map of direct images obtained by transposing a pullback square through
the two adjunctions. -/
def adjointSquareMap {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R) (F : D) :
    E.obj (R.obj F) ⟶ S.obj (V.obj F) :=
  a.homEquiv (E.obj (R.obj F)) (V.obj F)
    (α.hom.app (R.obj F) ≫ V.map (b.counit.app F))

/-- The direct image comparison is adjoint to the pullback comparison followed by
the counit over the second open inclusion. -/
def directImageComparison {U X V Y : TopCat.{u}} {j : U ⟶ X} {k : V ⟶ Y}
    {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage k ⊣ derivedDirectImage k) (F : BoundedBelow V) :
    (boundedBelowInverseImage e).obj ((derivedDirectImage k).obj F) ⟶
      (derivedDirectImage j).obj ((boundedBelowInverseImage v).obj F) :=
  adjointSquareMap (pullbackSquare h) a b F

/-- A homeomorphism of dimension filtrations preserves the top dimension, the cutoff
at each attachment and the open inclusions between stages. -/
inductive FiltrationIso : {X Y : TopCat.{u}} → {s : ℕ} → (X ≅ Y) →
    DimensionFiltration X s → DimensionFiltration Y s → Prop
  | top {X Y : TopCat.{u}} (e : X ≅ Y) (d : ℕ) :
      FiltrationIso e (.top X d) (.top Y d)
  | attach {U X V Y : TopCat.{u}} {d s : ℕ} {P : DimensionFiltration U d}
      {Q : DimensionFiltration V d} {e : X ≅ Y} {v : U ≅ V} {j : U ⟶ X} {k : V ⟶ Y}
      {hj : IsOpenEmbedding j} {hk : IsOpenEmbedding k} {hs : s < d}
      (hprev : FiltrationIso v P Q) (h : j ≫ e.hom = v.hom ≫ k) :
      FiltrationIso e (.attach P j hj hs) (.attach Q k hk hs)

namespace Expected

/-- The attachment is perverse and strict on the boundary. Its identification on
the open part is the restriction of the truncation inclusion followed by the
derived adjunction counit. -/
def AttachmentIsMiddleExtension : Prop :=
  ∀ {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j) (s : ℕ)
    (P : Stratification U) (Q : Stratification X) (_ : AttachmentStratification j s P Q)
    (F : BoundedBelow U), IsMiddlePerverse P F.obj →
    IsConstructibleOnBoundary j ((derivedDirectImage j).obj F) →
    let E := (attachment j hj s).obj F
    IsMiddlePerverse Q E.obj ∧ IsStrictExtension hj s E ∧
      ∀ a : boundedBelowInverseImage j ⊣ derivedDirectImage j,
        IsIso ((boundedBelowInverseImage j).map ((attachmentInclusion j hj s).app F) ≫
          a.counit.app F)

/-- Every map of open restrictions lifts uniquely to a map of strict extensions.
In particular, a specified identification on the open part lifts to a unique
isomorphism, and the lifts preserve identity and composition. -/
def StrictRestrictionFullyFaithful : Prop :=
  ∀ {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j) (s : ℕ),
    Nonempty (strictRestriction hj s).FullyFaithful

/-- The degree-zero Hom vanishings against objects supported on the new perverse stratum. -/
def StrictExtensionNoSupportedMorphisms : Prop :=
  ∀ {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j) (s : ℕ)
    (F : BoundedBelow X) (G : BoundedBelow (TopCat.of (boundary j))),
    IsStrictExtension hj s F → G.IsGE (-(s : ℤ)) → G.IsLE (-(s : ℤ)) →
    (∀ f : (LocalSheaf.closedExtensionPlus (boundary_isClosed hj)).obj G ⟶ F, f = 0) ∧
      (∀ g : F ⟶ (LocalSheaf.closedExtensionPlus (boundary_isClosed hj)).obj G, g = 0)

/-- Transport in a square of open inclusions and homeomorphisms commutes with the
attachment functors and their canonical maps into the derived direct images. -/
def AttachmentTransport : Prop :=
  ∀ {U X V Y : TopCat.{u}} (j : U ⟶ X) (k : V ⟶ Y)
    (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k)
    (e : X ≅ Y) (v : U ≅ V) (h : j ≫ e.hom = v.hom ≫ k) (s : ℕ)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage k ⊣ derivedDirectImage k),
    ∃ τ : attachment k hk s ⋙ boundedBelowInverseImage e.hom ≅
        boundedBelowInverseImage v.hom ⋙ attachment j hj s,
      ∀ F : BoundedBelow V,
        τ.hom.app F ≫ (attachmentInclusion j hj s).app ((boundedBelowInverseImage v.hom).obj F) =
          (boundedBelowInverseImage e.hom).map ((attachmentInclusion k hk s).app F) ≫
            directImageComparison h a b F

/-- Transport of the whole intersection complex retains the shifted constant
normalization at the top stage and the ordinary truncation at each later stage. -/
def ComplexTransport : Prop :=
  ∀ {X Y : TopCat.{u}} {s : ℕ} (e : X ≅ Y) (P : DimensionFiltration X s)
    (Q : DimensionFiltration Y s), FiltrationIso e P Q →
    Nonempty ((boundedBelowInverseImage e.hom).obj (complex Q) ≅ complex P)

end Expected
end RepTheorySurvey.Geometric.Analytic.IntersectionComplex
