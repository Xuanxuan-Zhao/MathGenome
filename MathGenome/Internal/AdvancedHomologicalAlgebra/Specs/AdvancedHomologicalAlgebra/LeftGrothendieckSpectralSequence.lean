import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckEdges
import Mathlib.Algebra.Homology.CochainComplexOpposite

/-! HA-G06, source lines 2782–2863. A homological diagram is encoded by a
cohomological diagram in the opposite of the target category. Page 0 is E²,
and the integer coordinates are filtration degree and total degree. -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

namespace AdvancedHomologicalAlgebra.LeftGrothendieckSpectralSequence

open HypercohomologyDerivedNaturality GrothendieckSpectralSequence

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]

/-- An encoded sequence has actual homological page objects and arrows in C. -/
abbrev HomologicalDiagram (C : Type u₃) [Category.{v₃} C] [Abelian C] :=
  (RowDiagram Cᵒᵖ)ᵒᵖ

abbrev homologicalPage (r : ℕ) (p n : ℤ) : HomologicalDiagram C ⥤ C :=
  (pageEval (C := Cᵒᵖ) r p n).leftOp

abbrev homologicalTarget (n : ℤ) : HomologicalDiagram C ⥤ C :=
  (targetEval (C := Cᵒᵖ) n).leftOp

/-- The same differential indexed by its destination. -/
abbrev incoming (D : HomologicalDiagram C) (r : ℕ) (p n : ℤ) :
    (homologicalPage r (p + ((r : ℤ) + 2)) (n + 1)).obj D ⟶
      (homologicalPage r p n).obj D :=
  (D.unop.differential r p n).unop

/-- On page r+2 the displayed arrow lowers total degree by one and lowers
filtration degree by r+2. -/
def differential (D : HomologicalDiagram C) (r : ℕ) (p n : ℤ) :
    (homologicalPage r p n).obj D ⟶ (homologicalPage r (p - ((r : ℤ) + 2)) (n - 1)).obj D :=
  eqToHom (congrArg₂ (fun a b => (D.unop.page r a b).unop)
    (show p = p - ((r : ℤ) + 2) + ((r : ℤ) + 2) by omega)
    (show n = n - 1 + 1 by omega)) ≫
    incoming D r (p - ((r : ℤ) + 2)) (n - 1)

/-- The incoming arrow, middle page object and outgoing arrow, in that order. -/
abbrev pageComplex (D : HomologicalDiagram C) (r : ℕ) (p n : ℤ) : ShortComplex C :=
  (D.unop.pageComplex r p n).unop

/-- In the original category the decreasing inclusion becomes a quotient.
The kernel of the quotient at p+1 is the increasing step at p. -/
def filtration (D : HomologicalDiagram C) (p n : ℤ) :
    Subobject ((homologicalTarget n).obj D) :=
  kernelSubobject (D.unop.inclusion (p + 1) n).unop

/-- A quotient in an increasing filtration. -/
abbrev graded {X : C} (S T : Subobject X) (h : S ≤ T) :=
  cokernel (Subobject.ofLE S T h)

/-- Full convergence on the original target in C. -/
structure FiniteConvergence (D : HomologicalDiagram C) : Prop where
  increasing : ∀ p n : ℤ, filtration D (p - 1) n ≤ filtration D p n
  natural_filtration : ∀ (D' : HomologicalDiagram C) (f : D ⟶ D') (p n : ℤ),
    (filtration D' p n).Factors
      ((filtration D p n).arrow ≫ (homologicalTarget n).map f)
  finite : ∀ n : ℤ, ∃ a b : ℤ,
    (∀ p, p ≤ a → filtration D p n = ⊥) ∧
    (∀ p, b ≤ p → filtration D p n = ⊤)
  stable : ∀ n : ℤ, ∃ N : ℕ, ∀ r : ℕ, N ≤ r → ∀ p : ℤ,
    differential D r p n = 0 ∧
      Nonempty ((homologicalPage r p n).obj D ≅
        graded _ _ (increasing p n))

/-- The reversed edges arise from the canonical whole-diagram model of a
localized row sequence for the opposite functor. -/
def FilteredEdgeFormulas (G : B ⥤ C) [G.Additive] (D : HomologicalDiagram C)
    (E : G05FilteredEdges.EdgeData D.unop) : Prop :=
  ∃ (hB : HasDerivedCategory.{max u₂ v₂} Bᵒᵖ)
    (hC : HasDerivedCategory.{max u₃ v₃} Cᵒᵖ)
    (hI : EnoughInjectives Bᵒᵖ),
    letI := hB
    letI := hC
    letI := hI
    ∃ (R : DerivedRow G.op) (Y : DerivedCategory.Plus Bᵒᵖ)
      (hD : D.unop = R.derived.obj Y),
      GrothendieckEdges.FilteredEdgesOn G.op R Y (hD ▸ E)

/-- Exactness of the four maps in the source, including the terminal zero. -/
structure FiveTerms {W V X Y Z : C}
    (f : W ⟶ V) (d : V ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : Prop where
  epi : Epi h
  fd : f ≫ d = 0
  dg : d ≫ g = 0
  gh : g ≫ h = 0
  exact_f_d : (ShortComplex.mk f d fd).Exact
  exact_d_g : (ShortComplex.mk d g dg).Exact
  exact_g_h : (ShortComplex.mk g h gh).Exact

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{w₃} C]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated] [(minus C).IsTriangulated]

/-- Homological homology on D⁻, with the source's convention H_j = H^(-j). -/
abbrev homologicalHomology (n : ℤ) : DerivedCategory.Minus C ⥤ C :=
  DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor C (-n)

variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  (LF : ExactLeftData F) (LG : ExactLeftData G) (LFG : ExactLeftData (F ⋙ G))

def termwiseComposition :
    termwiseMinusValue F ⋙ termwiseMinusValue G ≅ termwiseMinusValue (F ⋙ G) :=
  ((FullyFaithful.ofFullyFaithful (minusInclusion C)).whiskeringRight _).preimageIso
    (isoWhiskerLeft (minusInclusion A)
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)))

/-- The composite counit that defines the canonical comparison by HA-R05.
Termwise composition is identified before derivation. -/
def composedCounit : QMinus A ⋙ (LF.functor ⋙ LG.functor) ⟶ minusUValue (F ⋙ G) :=
  (associator _ _ _).inv ≫ whiskerRight LF.counit LG.functor ≫
    (associator _ _ _).hom ≫ whiskerLeft (termwiseMinusValue F) LG.counit ≫
    (associator _ _ _).inv ≫ (isoWhiskerRight (termwiseComposition F G) (QMinus C)).hom

section StalkComparisons

/-- A single object placed in cochain degree k in the bounded-above category. -/
def minusPoint (B : Type u₂) [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (k : ℤ) : B ⥤ DerivedCategory.Minus B :=
  DerivedCategory.TStructure.t.minus.lift (DerivedCategory.singleFunctor B k)
    (fun _ => ⟨k, inferInstance⟩)

def minusPointModel (A : Type u₁) [Category.{v₁} A] [Abelian A] (k : ℤ) (X : A) :
    KMinus A :=
  ⟨(HomotopyCategory.singleFunctor A k).obj X, k, by
    change ((CochainComplex.singleFunctor A k).obj X).IsStrictlyLE k
    infer_instance⟩

/-- The actual derived counit on a shifted stalk, using the standard
comparison of termwise application of F to a single complex. -/
def stalkCounit (k : ℤ) (X : A) :
    LF.functor.obj ((minusPoint A k).obj X) ⟶ (minusPoint B k).obj (F.obj X) := by
  let K := (CochainComplex.singleFunctor A k).obj X
  let M := minusPointModel A k X
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
  let Q := HomotopyCategory.quotient B (.up ℤ)
  let e₁ : (minusPoint A k).obj X ≅ (QMinus A).obj M :=
    DerivedCategory.Minus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQh A k).app X)
  let e₂ :
      ((minusUValue F).obj M).obj ≅ (DerivedCategory.Qh (C := B)).obj (Q.obj FK) :=
    DerivedCategory.Qh.mapIso
      ((F.mapHomotopyCategory (.up ℤ)).mapIso
        ((HomotopyCategory.singleFunctorPostcompQuotientIso A k).app X) ≪≫
        (F.mapHomotopyCategoryFactors (.up ℤ)).app K)
  let e₃ : (minusUValue F).obj M ≅ (minusPoint B k).obj (F.obj X) :=
    DerivedCategory.Minus.ι.preimageIso (e₂ ≪≫
      (DerivedCategory.quotientCompQhIso B).symm.app FK ≪≫
      DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) k).app X))
  exact LF.functor.map e₁.hom ≫ LF.counit.app M ≫ e₃.hom

def pointComparison (k : ℤ) (X : A) :
    (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor B k).obj
      (LF.functor.obj ((minusPoint A k).obj X)) ⟶ F.obj X :=
  (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor B k).map
    (stalkCounit F LF k X) ≫
  (DerivedCategory.singleFunctorCompHomologyFunctorIso B k).hom.app (F.obj X)

/-- For k = 0 this is the actual degree-zero derived counit. -/
abbrev degreeZeroComparison (X : A) : (leftValue F LF 0).obj X ⟶ F.obj X :=
  pointComparison F LF 0 X

end StalkComparisons

section OppositeModels

variable (A)

/-- Cochain degree j after reversal is degree -j with arrows reversed. -/
abbrev reversedComplex (K : CochainComplex A ℤ) : CochainComplex Aᵒᵖ ℤ :=
  (CochainComplex.opEquivalence A).functor.obj (Opposite.op K)

def reversedBounded (K : KMinus A) : CochainComplex.Plus Aᵒᵖ :=
  ⟨reversedComplex A K.obj.as, by
    obtain ⟨b, hb⟩ := K.property
    refine ⟨-b, (CochainComplex.isStrictlyGE_iff _ _).2 ?_⟩
    intro j hj
    have h := (CochainComplex.isStrictlyLE_iff _ _).1 hb (-j) (by omega)
    exact h.op⟩

/-- The canonical kernel/cokernel duality in this degree, including the
actual integer reindexing of the adjacent differentials. -/
def reversedHomology (K : CochainComplex A ℤ) (n : ℤ) :
    (reversedComplex A K).homology n ≅ Opposite.op (K.homology (-n)) := by
  let S := K.sc' (-(n+1)) (-n) (-(n-1))
  let T := (reversedComplex A K).sc' (n-1) n (n+1)
  let e : T ≅ S.op := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 (Opposite.op (K.X (-(n-1)))) ≫ (K.d (-n) (-(n-1))).op =
      (K.d (-n) (-(n-1))).op ≫ 𝟙 (Opposite.op (K.X (-n)))
    simp) (by
    change 𝟙 (Opposite.op (K.X (-n))) ≫ (K.d (-(n+1)) (-n)).op =
      (K.d (-(n+1)) (-n)).op ≫ 𝟙 (Opposite.op (K.X (-(n+1))))
    simp)
  exact (reversedComplex A K).homologyIsoSc' _ _ _ (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso e ≪≫ S.homologyOpIso ≪≫
      (K.homologyIsoSc' _ _ _ (by simp; omega) (by simp; omega)).op

/-- The opposite of a degree-zero stalk, with the identity at its
nonzero term in the standard stalk coordinates. -/
def reversedStalk (X : A) :
    reversedComplex A ((CochainComplex.singleFunctor A 0).obj X) ≅
      (CochainComplex.singleFunctor Aᵒᵖ 0).obj (Opposite.op X) := by
  let e : ∀ j : ℤ, (reversedComplex A ((CochainComplex.singleFunctor A 0).obj X)).X j ≅
      ((CochainComplex.singleFunctor Aᵒᵖ 0).obj (Opposite.op X)).X j := fun j => by
    by_cases h : j = 0
    · subst j
      exact (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).symm.op ≪≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (Opposite.op X)).symm
    · have h' : -j ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X (-j) h').op.iso
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (Opposite.op X) j h)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j _
  rw [HomologicalComplex.single_obj_d, comp_zero]
  change 0 = (((CochainComplex.singleFunctor A 0).obj X).d (-j) (-i)).op ≫ _
  simp
end OppositeModels
section DerivedOpposite

variable (A) [HasDerivedCategory.{max u₁ v₁} Aᵒᵖ]

def derivedHomologyOnModel (K : KMinus A) (n : ℤ) :
    (homologicalHomology (C := A) n).obj ((QMinus A).obj K) ≅ K.obj.as.homology (-n) :=
  (DerivedCategory.homologyFunctor A (-n)).mapIso
      ((DerivedCategory.quotientCompQhIso A).symm.app K.obj.as) ≪≫
    (DerivedCategory.homologyFunctorFactors A (-n)).app K.obj.as

def minusStalkModelIso (X : A) :
    (minusSingle A).obj X ≅ (QMinus A).obj (minusPointModel A 0 X) :=
  DerivedCategory.Minus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQh A 0).app X)

def reversedStalkToPlus (X : A) :
    DerivedCategory.Plus.Q.obj (reversedBounded A (minusPointModel A 0 X)) ⟶
      (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (Opposite.op X) := by
  let K : CochainComplex.Plus Aᵒᵖ :=
    ⟨(CochainComplex.singleFunctor Aᵒᵖ 0).obj (Opposite.op X), ⟨0, inferInstance⟩⟩
  change _ ⟶ DerivedCategory.Plus.Q.obj K
  exact DerivedCategory.Plus.Q.map (ObjectProperty.homMk (reversedStalk A X).hom)

/-- Bounded derived reversal, specified on the actual complex and on its
canonical homology and stalk comparisons. -/
structure DerivedReversal where
  functor : (DerivedCategory.Minus A)ᵒᵖ ⥤ DerivedCategory.Plus Aᵒᵖ
  localized : ∀ K : KMinus A, functor.obj (Opposite.op ((QMinus A).obj K)) ≅
    DerivedCategory.Plus.Q.obj (reversedBounded A K)
  localized_naturality : ∀ (K L : KMinus A) (f : K.obj.as ⟶ L.obj.as),
    let m : K ⟶ L := ObjectProperty.homMk ((HomotopyCategory.quotient A (.up ℤ)).map f)
    let fm : reversedBounded A L ⟶ reversedBounded A K :=
      ObjectProperty.homMk ((CochainComplex.opEquivalence A).functor.map f.op)
    functor.map ((QMinus A).map m).op ≫ (localized K).hom =
      (localized L).hom ≫ DerivedCategory.Plus.Q.map fm
  homology : ∀ n : ℤ, functor ⋙ DerivedCategory.Plus.homologyFunctor Aᵒᵖ n ≅
    (homologicalHomology (C := A) n).op
  homology_eq : ∀ K : KMinus A, ∀ n : ℤ,
    (homology n).hom.app (Opposite.op ((QMinus A).obj K)) =
      (DerivedCategory.Plus.homologyFunctor Aᵒᵖ n).map (localized K).hom ≫
      (DerivedCategory.homologyFunctorFactors Aᵒᵖ n).hom.app (reversedBounded A K).obj ≫
      (reversedHomology A K.obj.as n).hom ≫
      (derivedHomologyOnModel A K n).hom.op
  stalk : ∀ X : A, functor.obj (Opposite.op ((minusSingle A).obj X)) ≅
    (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (Opposite.op X)
  stalk_eq : ∀ X : A,
    let M := minusPointModel A 0 X
    (stalk X).hom = functor.map (minusStalkModelIso A X).inv.op ≫ (localized M).hom ≫
      reversedStalkToPlus A X

end DerivedOpposite

section DerivedReversalComparison

variable [HasDerivedCategory.{max u₁ v₁} Aᵒᵖ] [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ]
  [EnoughInjectives Aᵒᵖ]
  (OA : DerivedReversal A) (OB : DerivedReversal B)

/-- Termwise application of the opposite functor commutes with reversal. -/
def reversedTermwise (K : KMinus A) :
    reversedBounded B ((termwiseMinusValue F).obj K) ≅
      F.op.mapCochainComplexPlus.obj (reversedBounded A K) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- The comparison of the actual left and right derived functors is fixed
by the reversed counit and the right-derived unit on bounded models. -/
structure ReversedDerivedFunctor where
  iso : LF.functor.op ⋙ OB.functor ≅ OA.functor ⋙ F.op.rightDerivedFunctorPlus
  unit_counit : ∀ K : KMinus A,
    OB.functor.map (LF.counit.app K).op ≫
        iso.hom.app (Opposite.op ((QMinus A).obj K)) ≫
        F.op.rightDerivedFunctorPlus.map (OA.localized K).hom =
      (OB.localized ((termwiseMinusValue F).obj K)).hom ≫
        DerivedCategory.Plus.Q.map (reversedTermwise F K).hom ≫
        F.op.rightDerivedFunctorPlusUnit.app (reversedBounded A K)

def ReversedDerivedFunctor.classical (R : ReversedDerivedFunctor F LF OA OB)
    (p : ℕ) (X : A) :
    (rightValue F.op p).obj (Opposite.op X) ≅ Opposite.op ((leftValue F LF p).obj X) :=
  (DerivedCategory.Plus.homologyFunctor Bᵒᵖ (p : ℤ)).mapIso
    ((F.op.rightDerivedFunctorPlus.mapIso (OA.stalk X).symm) ≪≫
      (R.iso.app (Opposite.op ((minusSingle A).obj X))).symm) ≪≫
    (OB.homology (p : ℤ)).app (Opposite.op (LF.functor.obj ((minusSingle A).obj X)))

end DerivedReversalComparison
abbrev objectSecond (p q : ℕ) : A ⥤ C := leftValue F LF q ⋙ leftValue G LG p

abbrev abutment (n : ℤ) : DerivedCategory.Minus A ⥤ C :=
  LFG.functor ⋙ homologicalHomology n

/-- The full derived sequence, natural identifications, and canonical
composition comparison. The target isomorphism uses that same comparison. -/
structure Package where
  sequence : DerivedCategory.Minus A ⥤ HomologicalDiagram C
  secondIso : ∀ (p : ℕ) (q : ℤ),
    sequence ⋙ homologicalPage 0 p ((p : ℤ) + q) ≅
      LF.functor ⋙ homologicalHomology q ⋙ leftValue G LG p
  negative : ∀ (X : DerivedCategory.Minus A) (p n : ℤ), p < 0 →
    IsZero ((homologicalPage 0 p n).obj (sequence.obj X))
  comparison : LF.functor ⋙ LG.functor ≅ LFG.functor
  comparison_counit : whiskerLeft (QMinus A) comparison.hom ≫ LFG.counit =
    composedCounit F G LF LG
  iteratedIso : ∀ n : ℤ, sequence ⋙ homologicalTarget n ≅
    (LF.functor ⋙ LG.functor) ⋙ homologicalHomology n
  convergence : ∀ X : DerivedCategory.Minus A, FiniteConvergence (sequence.obj X)
  /-- The page and target coordinates are the coordinate maps of this same
  reversed row diagram. This also fixes signs when both edges vanish. -/
  rowPresentation :
    ∃ (hB : HasDerivedCategory.{max u₂ v₂} Bᵒᵖ)
      (hC : HasDerivedCategory.{max u₃ v₃} Cᵒᵖ)
      (hI : EnoughInjectives Bᵒᵖ),
      letI := hB
      letI := hC
      letI := hI
      ∃ (OB : DerivedReversal B) (OC : DerivedReversal C)
        (OG : ReversedDerivedFunctor G LG OB OC)
        (R : DerivedRow G.op) (U : RowCoordinates G.op R)
        (e : sequence.leftOp ≅ LF.functor.op ⋙ OB.functor ⋙ R.derived),
        (∀ (X : DerivedCategory.Minus A) (p : ℕ) (q : ℤ),
          let Y := Opposite.op (LF.functor.obj X)
          let H := (homologicalHomology (C := B) q).obj (LF.functor.obj X)
          ((secondIso p q).inv.app X).op =
            (e.hom.app (Opposite.op X)).page 0 p ((p : ℤ) + q) ≫
            (U.second p q).hom.app (OB.functor.obj Y) ≫
            (rightValue G.op p).map ((OB.homology q).hom.app Y) ≫
            (ReversedDerivedFunctor.classical G LG OB OC OG p H).hom) ∧
        (∀ (X : DerivedCategory.Minus A) (n : ℤ),
          let Y := Opposite.op (LF.functor.obj X)
          ((iteratedIso n).inv.app X).op =
            (e.hom.app (Opposite.op X)).target n ≫
            (U.target n).hom.app (OB.functor.obj Y) ≫
            (DerivedCategory.Plus.homologyFunctor Cᵒᵖ n).map (OG.iso.inv.app Y) ≫
            (OC.homology n).hom.app (Opposite.op (LG.functor.obj (LF.functor.obj X))))

abbrev targetIso (P : Package F G LF LG LFG) (n : ℤ) :
    P.sequence ⋙ homologicalTarget n ≅ abutment F G LFG n :=
  P.iteratedIso n ≪≫ isoWhiskerRight P.comparison (homologicalHomology n)

/-- The induced increasing filtration on the stated homology of L(GF). -/
def abutmentFiltration (P : Package F G LF LG LFG) (X : DerivedCategory.Minus A) (p n : ℤ) :
    Subobject ((abutment F G LFG n).obj X) :=
  (Subobject.map ((targetIso F G LF LG LFG P n).hom.app X)).obj
    (filtration (P.sequence.obj X) p n)

/-- Convergence on the homology of the composite derived functor itself. -/
structure AbutmentConvergence (P : Package F G LF LG LFG) : Prop where
  monotone : ∀ (X : DerivedCategory.Minus A) (n : ℤ),
    Monotone (fun p => abutmentFiltration F G LF LG LFG P X p n)
  natural_filtration : ∀ {X Y : DerivedCategory.Minus A} (f : X ⟶ Y) (p n : ℤ),
    (abutmentFiltration F G LF LG LFG P Y p n).Factors
      ((abutmentFiltration F G LF LG LFG P X p n).arrow ≫ (abutment F G LFG n).map f)
  finite : ∀ (X : DerivedCategory.Minus A) (n : ℤ), ∃ a b : ℤ,
    (∀ p, p ≤ a → abutmentFiltration F G LF LG LFG P X p n = ⊥) ∧
    (∀ p, b ≤ p → abutmentFiltration F G LF LG LFG P X p n = ⊤)
  stable : ∀ (X : DerivedCategory.Minus A) (n : ℤ), ∃ N : ℕ,
    ∀ r : ℕ, N ≤ r → ∀ p : ℤ,
      differential (P.sequence.obj X) r p n = 0 ∧
      Nonempty ((homologicalPage r p n).obj (P.sequence.obj X) ≅
        graded _ _ (monotone X n (show p - 1 ≤ p by omega)))

abbrev objectSequence (P : Package F G LF LG LFG) :=
  minusSingle A ⋙ P.sequence

/-- Object values and edge maps on the restriction of the derived sequence
to the actual stalks. The differential in the five terms is the page
differential transported through the two axis identifications. -/
structure ObjectCase (P : Package F G LF LG LFG) where
  secondIso : ∀ p q : ℕ, objectSequence F G LF LG LFG P ⋙
    homologicalPage 0 p ((p : ℤ) + q) ≅ objectSecond F G LF LG p q
  secondIso_eq : ∀ p q : ℕ, secondIso p q =
    associator _ _ _ ≪≫
      isoWhiskerLeft (minusSingle A) (P.secondIso p (q : ℤ)) ≪≫
      (associator (minusSingle A) (LF.functor ⋙ homologicalHomology (q : ℤ))
        (leftValue G LG p)).symm
  quadrant : ∀ (X : A) (r : ℕ) (p n : ℤ), p < 0 ∨ n < p →
    IsZero ((homologicalPage r p n).obj ((objectSequence F G LF LG LFG P).obj X))
  degreeZeroF : leftValue F LF 0 ≅ F
  degreeZeroG : leftValue G LG 0 ≅ G
  degreeZeroF_hom : ∀ X, degreeZeroF.hom.app X = degreeZeroComparison F LF X
  degreeZeroG_hom : ∀ X, degreeZeroG.hom.app X = degreeZeroComparison G LG X
  column : ∀ n : ℕ, objectSequence F G LF LG LFG P ⋙ homologicalPage 0 0 n ⟶
    objectSequence F G LF LG LFG P ⋙ homologicalTarget n
  row : ∀ n : ℕ, objectSequence F G LF LG LFG P ⋙ homologicalTarget n ⟶
    objectSequence F G LF LG LFG P ⋙ homologicalPage 0 n n
  filtered : ∀ X : A, let D := (objectSequence F G LF LG LFG P).obj X
    FilteredEdgeFormulas G D {
      row := fun n => ((row n).app X).op
      column := fun n => ((column n).app X).op }
  fiveTerms : ∀ X : A, let D := (objectSequence F G LF LG LFG P).obj X
    FiveTerms ((row 2).app X) (differential D 0 2 2) ((column 1).app X) ((row 1).app X)

section ClassicalEdges

variable {F G LF LG LFG} {P : Package F G LF LG LFG}
  (O : ObjectCase F G LF LG LFG P)

/-- The axis at (n,0), identified with LₙG(F(-)). -/
def rowValueIso (n : ℕ) :
    objectSequence F G LF LG LFG P ⋙ homologicalPage 0 n n ≅ F ⋙ leftValue G LG n :=
  eqToIso (by simp only [Int.natCast_zero, add_zero]) ≪≫ O.secondIso n 0 ≪≫
    isoWhiskerRight O.degreeZeroF (leftValue G LG n)

/-- The axis at (0,n), identified with G(LₙF(-)). -/
def columnValueIso (n : ℕ) :
    objectSequence F G LF LG LFG P ⋙ homologicalPage 0 0 n ≅ leftValue F LF n ⋙ G :=
  eqToIso (by simp only [Int.natCast_zero, zero_add]) ≪≫ O.secondIso 0 n ≪≫
    isoWhiskerLeft (leftValue F LF n) O.degreeZeroG

/-- The object case abuts to the classical left derived value. -/
def objectTargetIso (n : ℕ) :
    objectSequence F G LF LG LFG P ⋙ homologicalTarget n ≅ leftValue (F ⋙ G) LFG n :=
  associator _ _ _ ≪≫ isoWhiskerLeft (minusSingle A) (targetIso F G LF LG LFG P n)

/-- The edge G(LₙF(-)) → Lₙ(GF)(-). -/
def firstEdge (n : ℕ) : leftValue F LF n ⋙ G ⟶ leftValue (F ⋙ G) LFG n :=
  (columnValueIso O n).inv ≫ O.column n ≫ (objectTargetIso (P := P) n).hom

/-- The edge Lₙ(GF)(-) → LₙG(F(-)). -/
def secondEdge (n : ℕ) : leftValue (F ⋙ G) LFG n ⟶ F ⋙ leftValue G LG n :=
  (objectTargetIso (P := P) n).inv ≫ O.row n ≫ (rowValueIso O n).hom

/-- The page-two differential from (2,0) to (0,1) in classical values. -/
def objectTransgression (X : A) :
    (F ⋙ leftValue G LG 2).obj X ⟶ (leftValue F LF 1 ⋙ G).obj X :=
  (rowValueIso O 2).inv.app X ≫
    differential ((objectSequence F G LF LG LFG P).obj X) 0 2 2 ≫
    (columnValueIso O 1).hom.app X

/-- In degree k, the homological truncation span uses the actual
cochain truncation in degrees ≥ k and then its term supported in degree k. -/
structure DualTruncation (k : ℤ) where
  upper : LG.functor ⋙ DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor C k ≅
    DerivedCategory.TStructure.t.onMinus.truncGE k ⋙ LG.functor ⋙
      DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor C k
  upper_hom : upper.hom =
    whiskerRight (DerivedCategory.TStructure.t.onMinus.truncGEπ k)
      (LG.functor ⋙ DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor C k)
  point : DerivedCategory.TStructure.t.onMinus.truncGE k ⋙
      DerivedCategory.TStructure.t.onMinus.truncLE k ≅
    (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor B k) ⋙ minusPoint B k
  point_normalization : ∀ Y : DerivedCategory.Minus B,
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B k).inv.app
      ((DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor B k).obj Y) ≫
    (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor B k).map
      (point.inv.app Y ≫ (DerivedCategory.TStructure.t.onMinus.truncLEι k).app
        ((DerivedCategory.TStructure.t.onMinus.truncGE k).obj Y)) =
    (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor B k).map
      ((DerivedCategory.TStructure.t.onMinus.truncGEπ k).app Y)
  stalk : ∀ Z : B, (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor C k).obj
    (LG.functor.obj ((minusPoint B k).obj Z)) ≅ G.obj Z
  stalk_hom : ∀ Z, (stalk Z).hom = pointComparison G LG k Z

/-- The two classical edges are given by the reversed truncation formulas
of HA-G05 under the same canonical composition comparison. -/
def CanonicalEdges : Prop :=
  ∃ T : ∀ n : ℕ, DualTruncation (G := G) (LG := LG) (-(n : ℤ)),
    ∀ (n : ℕ) (X : A),
      let Y := LF.functor.obj ((minusSingle A).obj X)
      let H := homologicalHomology (C := C) (n : ℤ)
      (firstEdge O n).app X =
        ((T n).stalk ((homologicalHomology (C := B) (n : ℤ)).obj Y)).inv ≫
          H.map (LG.functor.map
            ((T n).point.inv.app Y ≫
              (DerivedCategory.TStructure.t.onMinus.truncLEι (-(n : ℤ))).app
                ((DerivedCategory.TStructure.t.onMinus.truncGE (-(n : ℤ))).obj Y))) ≫
          (T n).upper.inv.app Y ≫ H.map (P.comparison.hom.app ((minusSingle A).obj X)) ∧
      (secondEdge O n).app X =
        H.map (P.comparison.inv.app ((minusSingle A).obj X)) ≫
          H.map (LG.functor.map (stalkCounit F LF 0 X))

end ClassicalEdges

namespace Specs

/-- Derived and stalk cases under the same projective acyclicity condition,
for arbitrary exact left derived data of the three functors. -/
def FullStatement : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [EnoughProjectives A] [EnoughProjectives B],
    ∃ (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated)
      (hC : (minus C).IsTriangulated),
      letI := hA
      letI := hB
      letI := hC
      ∀ (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
        [PreservesFiniteColimits F] [PreservesFiniteColimits G]
        (LF : ExactLeftData F) (LG : ExactLeftData G) (LFG : ExactLeftData (F ⋙ G)),
        (∀ (P : A), Projective P → ∀ i : ℕ, 0 < i →
          IsZero ((leftValue G LG i).obj (F.obj P))) →
        ∃ P : Package F G LF LG LFG,
          AbutmentConvergence F G LF LG LFG P ∧
            ∃ O : ObjectCase F G LF LG LFG P, CanonicalEdges O

/-- Existence of the total derived models under the stated categorical hypotheses,
with the sequence for every choice of those models satisfying the vanishing condition. -/
def ExistsApplicable : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [EnoughProjectives A] [EnoughProjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G],
    ∃ (hA : (minus A).IsTriangulated) (hB : (minus B).IsTriangulated)
      (hC : (minus C).IsTriangulated),
      letI := hA
      letI := hB
      letI := hC
      Nonempty (ExactLeftData F) ∧ Nonempty (ExactLeftData G) ∧
        Nonempty (ExactLeftData (F ⋙ G)) ∧
        ∀ (LF : ExactLeftData F) (LG : ExactLeftData G) (LFG : ExactLeftData (F ⋙ G)),
          (∀ (P : A), Projective P → ∀ i : ℕ, 0 < i →
            IsZero ((leftValue G LG i).obj (F.obj P))) →
          ∃ P : Package F G LF LG LFG,
            AbutmentConvergence F G LF LG LFG P ∧
            ∃ O : ObjectCase F G LF LG LFG P, CanonicalEdges O

/-- The five terms on the stated derived values, with the actual spectral
sequence transgression and the two natural edge maps. -/
def ClassicalExactness : Prop :=
  ∀ (A : Type u₁) (B : Type u₂) (C : Type u₃)
    [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
    [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
    [(minus A).IsTriangulated] [(minus B).IsTriangulated] [(minus C).IsTriangulated]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (LF : ExactLeftData F) (LG : ExactLeftData G) (LFG : ExactLeftData (F ⋙ G))
    (P : Package F G LF LG LFG) (O : ObjectCase F G LF LG LFG P) (X : A),
    FiveTerms ((secondEdge O 2).app X) (objectTransgression O X)
      ((firstEdge O 1).app X) ((secondEdge O 1).app X)

end Specs
end AdvancedHomologicalAlgebra.LeftGrothendieckSpectralSequence
