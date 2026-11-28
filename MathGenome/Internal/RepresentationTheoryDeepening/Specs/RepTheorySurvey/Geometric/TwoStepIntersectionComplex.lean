import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionSurface
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MiddleExtension

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace Topology
open LinearAlgebraicGroups (Points)

namespace RepTheorySurvey.Geometric.TwoStepIntersectionComplexSpecs

open LatticeModelSpecs MinusculeAndTwoStepSpecs
open Analytic Analytic.IntersectionComplex

/-- The colength-two stage of the actual lattice Grassmannian, with its analytic topology. -/
abbrev X : TopCat := TopCat.of (Colength 2)

abbrev vertex (h : scalarPoint ∈ colength 2) : X := ⟨scalarPoint, h⟩

abbrev U (x : X) (hx : IsClosed ({x} : Set X)) : Opens X :=
  complementOpen {x} hx

abbrev inclusion (x : X) (hx : IsClosed ({x} : Set X)) : TopCat.of (U x hx) ⟶ X :=
  openInclusion (U x hx)

/-- The open and closed inclusions, with their respective complex dimensions. -/
def openStratum (x : X) (hx : IsClosed ({x} : Set X)) : Stratum X where
  ambientOpen := U x hx
  subset := Set.univ
  closed := isClosed_univ
  complexDimension := 2

def closedStratum (x : X) (hx : IsClosed ({x} : Set X)) : Stratum X where
  ambientOpen := ⊤
  subset := Subtype.val ⁻¹' {x}
  closed := hx.preimage continuous_subtype_val
  complexDimension := 0

theorem openStratum_range (x : X) (hx : IsClosed ({x} : Set X)) :
    Set.range (openStratum x hx).inclusion = ({x} : Set X)ᶜ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.val.property
  · intro hy
    exact ⟨⟨⟨y, hy⟩, Set.mem_univ _⟩, rfl⟩

theorem closedStratum_range (x : X) (hx : IsClosed ({x} : Set X)) :
    Set.range (closedStratum x hx).inclusion = {x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.property
  · intro hy
    exact ⟨⟨⟨y, Set.mem_univ _⟩, hy⟩, rfl⟩

def stratification (x : X) (hx : IsClosed ({x} : Set X)) : Stratification X where
  Index := Bool
  stratum b := if b then openStratum x hx else closedStratum x hx
  partition y := by
    by_cases hy : y ∈ ({x} : Set X)
    · refine ⟨false, ?_, ?_⟩
      · change y ∈ Set.range (closedStratum x hx).inclusion
        rwa [closedStratum_range]
      · intro b hb
        cases b
        · rfl
        · change y ∈ Set.range (openStratum x hx).inclusion at hb
          rw [openStratum_range] at hb
          exact False.elim (hb hy)
    · refine ⟨true, ?_, ?_⟩
      · change y ∈ Set.range (openStratum x hx).inclusion
        rwa [openStratum_range]
      · intro b hb
        cases b
        · change y ∈ Set.range (closedStratum x hx).inclusion at hb
          rw [closedStratum_range] at hb
          exact False.elim (hy hb)
        · rfl

abbrev shifted (x : X) (hx : IsClosed ({x} : Set X)) : BoundedBelow (TopCat.of (U x hx)) :=
  shiftedConstant (TopCat.of (U x hx)) 2

/-- The identification of constant coefficients under pullback, induced by
the global-sections adjunctions and the inverse/direct image adjunction. -/
def rationalPullback {A B : TopCat} (f : A ⟶ B) :
    (inverseImage f).obj (rational B) ≅ rational A :=
  let a := constantSheafAdj (Opens.grothendieckTopology B) Coeff.{0}
    (isTerminalTop (α := Opens B))
  let b := constantSheafAdj (Opens.grothendieckTopology A) Coeff.{0}
    (isTerminalTop (α := Opens A))
  let e : directImage f ⋙ LocalSheaf.globalSections B ≅ LocalSheaf.globalSections A :=
    NatIso.ofComponents
      (fun F ↦ F.obj.mapIso (eqToIso (congrArg Opposite.op (Opens.map_top f))))
      (fun g ↦ (g.hom.naturality _).symm)
  ((a.comp (inverseDirectAdjunction f)).leftAdjointUniq (b.ofNatIsoRight e.symm)).app _

/-- The same identification on coefficient complexes in perverse normalization. -/
def shiftedRestriction (x : X) (hx : IsClosed ({x} : Set X)) :
    (boundedBelowInverseImage (inclusion x hx)).obj (shiftedConstant X 2) ≅ shifted x hx := by
  let f := inclusion x hx
  let A := TopCat.of (U x hx)
  let K := (DerivedCategory.singleFunctor (Sheaves X) 0).obj (rational X)
  apply ObjectProperty.isoMk _
  exact ((inverseImage f).mapDerivedCategory.commShiftIso (2 : ℤ)).app K ≪≫
    (shiftFunctor (Derived A) (2 : ℤ)).mapIso
      (((inverseImage f).mapDerivedCategorySingleFunctor 0).app (rational X) ≪≫
        (DerivedCategory.singleFunctor (Sheaves A) 0).mapIso (rationalPullback f))

/-- Derived stalk cohomology at the closed orbit. -/
abbrev vertexStalk (x : X) (F : BoundedBelow X) (n : ℤ) : Coeff.{0} :=
  (cohomology X n ⋙ stalk x).obj F.obj

/-- Derived costalk cohomology at the closed orbit. -/
abbrev vertexCostalk (x : X) (hx : IsClosed ({x} : Set X)) (F : BoundedBelow X)
    (n : ℤ) : Coeff.{0} :=
  (DerivedCategory.Plus.homologyFunctor _ n ⋙ stalk (⟨x, rfl⟩ : ({x} : Set X))).obj
    ((derivedExtraordinaryInverseImage hx).obj F)

/-- Exactly one rational cohomology degree; all other degrees vanish. -/
def HasSingleDegree (H : ℤ → Coeff.{0}) (d : ℤ) : Prop :=
  Nonempty (H d ≅ ModuleCat.of ℚ ℚ) ∧ ∀ n : ℤ, n ≠ d → IsZero (H n)

namespace Expected

/-- The closed stratum is the scalar lattice. The open stratum is the analytic
space of complex points of the smooth surface obtained by removing that point. -/
def SmoothOpenOrbit : Prop :=
  ∃ (h : scalarPoint ∈ colength 2) (hx : IsClosed ({vertex h} : Set X))
    (e : Colength 2 ≃ₜ TwoStepPoints)
    (points : Points twoStepScheme complexAlgebra ≃ TwoStepPoints)
    (p : Points twoStepScheme complexAlgebra) (W : twoStepScheme.left.Opens),
    ConvolutionSurfaceSpecs.ScalarTerminalPoint p ∧
    (W : Set twoStepScheme.left) = {pointLocation p}ᶜ ∧
    SmoothOfRelativeDimension 2 (ConvolutionSurfaceSpecs.openOver W).hom ∧
    (∀ q, (points q).val = q ≫ twoStepSchemeInGrassmannian) ∧
    points p = e (vertex h) ∧
    ∀ L : Colength 2,
      grassmannianSubspace twoStepBasis twoStepRank (e L).val =
        (latticeSubspace 0 2 L.val).map twoStepCoordinates.toLinearMap ∧
      (pointLocation (points.symm (e L)) ∈ W ↔ L ∈ U (vertex h) hx) ∧
      (L ∈ U (vertex h) hx ↔ L.val ∈ gl2Orbit twoStepPair)

/-- The ordinary perverse bounds on both strata and the strict bounds at the vertex. -/
def Perverse : Prop :=
  ∀ (h : scalarPoint ∈ colength 2) (hx : IsClosed ({vertex h} : Set X)),
    let x := vertex h
    let j := inclusion x hx
    let hj : IsOpenEmbedding j := (U x hx).isOpenEmbedding
    IsMiddlePerverse (stratification x hx) (shiftedConstant X 2).obj ∧
    IsMiddlePerverse (stratification x hx) (surface x hx).obj ∧
    IsStrictExtension hj 0 (shiftedConstant X 2) ∧
    IsStrictExtension hj 0 (surface x hx)

/-- The stalk and costalk of both descriptions of the normalized complex. -/
def VertexCohomology : Prop :=
  ∀ (h : scalarPoint ∈ colength 2) (hx : IsClosed ({vertex h} : Set X)),
    let x := vertex h
    HasSingleDegree (vertexStalk x (surface x hx)) (-2) ∧
    HasSingleDegree (vertexCostalk x hx (surface x hx)) 2 ∧
    HasSingleDegree (vertexStalk x (shiftedConstant X 2)) (-2) ∧
    HasSingleDegree (vertexCostalk x hx (shiftedConstant X 2)) 2

/-- The isomorphism factors the adjunction map to the actual derived open
direct image and restricts to the constant coefficient identification. -/
def ConstantIdentification : Prop :=
  ∀ (h : scalarPoint ∈ colength 2) (hx : IsClosed ({vertex h} : Set X)),
    let x := vertex h
    let j := inclusion x hx
    let hj : IsOpenEmbedding j := (U x hx).isOpenEmbedding
    let F := shifted x hx
    let K := shiftedConstant X 2
    ∀ a : boundedBelowInverseImage j ⊣ derivedDirectImage j,
    ∃ e : K ≅ surface x hx,
      e.hom ≫ (attachmentInclusion j hj 0).app F =
        a.homEquiv K F (shiftedRestriction x hx).hom ∧
      (boundedBelowInverseImage j).map e.hom ≫
        (boundedBelowInverseImage j).map ((attachmentInclusion j hj 0).app F) ≫
        a.counit.app F = (shiftedRestriction x hx).hom

end Expected
end RepTheorySurvey.Geometric.TwoStepIntersectionComplexSpecs
