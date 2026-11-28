import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.CentralFrameDescentSpecs

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open ConvolutionConstantDescentSpec (shiftedConstantPullback)
open Analytic.DerivedPullbackPasting.Expected (squareValue)

abbrev centralPair (a : ℤ) : DominantPair := ⟨(a, a), le_rfl⟩

/-- The coefficient comparison for a parameter map to the central point. -/
def centralPointUnitMap {R C : TopCat.{0}} (z : R ⟶ C) {P : Derived C}
    (c : P ≅ (shiftedConstant C 0).obj) :
    (derivedInverseImage z).obj P ⟶ (shiftedConstant R 0).obj :=
  ((derivedInverseImage z).mapIso c ≪≫ shiftedConstantPullback z 0).hom

/-- The point and its normalized coefficient system are fixed at every jet level. -/
def CentralPointCoefficients {J : GL2JetParameters} {a : ℤ} {N : ℕ}
    {hN : OrbitBound (centralPair a) N} (B : SchubertJetAction J (centralPair a) N hN)
    {P : Derived (SchubertSpace (centralPair a) N hN)} (η : B.action.Equivariance P)
    (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) N hN) 0).obj) : Prop :=
  let C := SchubertSpace (centralPair a) N hN
  ∀ (k : ℕ) (hk : B.action.cutoff ≤ k),
    let π := AnalyticAction.projection (J.toJetSystem.group k) C
    let act := (B.action.action k hk).act
    (∀ (g : PositiveJet k) (x : C), act (g, x) = x) ∧
      (η.datum k hk).iso.hom ≫ centralPointUnitMap π c = centralPointUnitMap act c

namespace Expected

/-- The normalized IC on the actual equal-pair Schubert space identifies with
the degree-zero rational tensor unit, compatibly with equivariance and pullback. -/
def CentralPointNormalization : Prop :=
  ∀ (J : GL2JetParameters) (a : ℤ) (N : ℕ) (hN : OrbitBound (centralPair a) N)
    (B : SchubertJetAction J (centralPair a) N hN) (adj : DerivedAdjunctions.{0}),
    let C := SchubertSpace (centralPair a) N hN
    ∀ (P : Stratification C)
      (D : DimensionFiltration C (orbitDimension (centralPair a) (difference (centralPair a) / 2)))
      (_ : IsNormalizedOrbitIC (centralPair a) N hN (𝟙 C) (difference (centralPair a) / 2) P D)
      (η : B.action.Equivariance (complex D).obj)
      (_ : NormalizedICDatum (@adj) B.action D η),
      ∃ c : (complex D).obj ≅ (shiftedConstant C 0).obj,
        CentralPointCoefficients B η c ∧
          ∀ {R : TopCat.{0}} (z : R ⟶ C), IsIso (centralPointUnitMap z c)

/-- After identifying the first factor with the tensor unit, the left frame change
`(gh,L) ∼ (g,hL)` uses the multiplication equation of the second factor. -/
def LeftFrameComparison : Prop :=
  ∀ {J : JetSystem.{0}} {X : TopCat.{0}} (A : JetAction J X)
    (F G : A.Object) (i : G ≅ F) (k : ℕ) (hk : A.cutoff ≤ k),
    let H := J.group k
    let Aₖ := A.action k hk
    let p := AnalyticAction.projection H X
    let q := Aₖ.act
    ∃ d : (derivedInverseImage q).obj G.obj ≅ (derivedInverseImage p).obj F.obj,
      d.hom = (derivedInverseImage q).map i.hom.hom ≫ (F.equivariance.datum k hk).iso.hom ∧
      let s := AnalyticAction.firstAfterSecond Aₖ
      let t := AnalyticAction.multiplyParameters H X
      let u := AnalyticAction.secondParameter H X
      let b := (derivedInverseImage q).map i.inv.hom ≫ d.hom
      pullbackMorphism t rfl rfl b =
        pullbackMorphism s (AnalyticAction.multiply_act Aₖ) (AnalyticAction.first_projection Aₖ) b ≫
        pullbackMorphism u rfl AnalyticAction.multiply_projection (F.equivariance.datum k hk).iso.hom

/-- In the right chart the quotient reads the first lattice. The comparison
commutes with inverse image along every overlap of frame representatives. -/
def RightFrameComparison : Prop :=
  ∀ {J : JetSystem.{0}} {R X : TopCat.{0}} (A : JetAction J X)
    (F G : A.Object) (i : G ≅ F) (p q : R ⟶ X) (hqp : q = p),
    ∃ d : (derivedInverseImage q).obj G.obj ≅ (derivedInverseImage p).obj F.obj,
      d.hom = (derivedInverseImage q).map i.hom.hom ≫
        (eqToIso (congrArg (fun f : R ⟶ X ↦ (derivedInverseImage f).obj F.obj) hqp)).hom ∧
      ∀ {V : TopCat.{0}} (s t : V ⟶ R) (hp : s ≫ p = t ≫ p) (hq : s ≫ q = t ≫ q),
        (squareValue hq).hom.app G.obj ≫ (derivedInverseImage t).map d.hom =
          (derivedInverseImage s).map d.hom ≫ (squareValue hp).hom.app F.obj

/-- Pull back the normalized point coefficient equation by the jet of the
right frame change, whose point coordinate is the constant second lattice. -/
def RightPointComparison : Prop :=
  ∀ {J : GL2JetParameters} {a : ℤ} {N : ℕ} {hN : OrbitBound (centralPair a) N}
    (B : SchubertJetAction J (centralPair a) N hN),
    let C := SchubertSpace (centralPair a) N hN
    ∀ {P : Derived C} (η : B.action.Equivariance P) (c : P ≅ (shiftedConstant C 0).obj),
      CentralPointCoefficients B η c →
      ∀ (k : ℕ) (hk : B.action.cutoff ≤ k) {R V : TopCat.{0}} (x : C) (s t : V ⟶ R)
        (u : V ⟶ AnalyticAction.Parameters (J.toJetSystem.group k) C),
        (∀ v : V, (u v).2 = x) →
        let z : R ⟶ C := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
        let π := AnalyticAction.projection (J.toJetSystem.group k) C
        let act := (B.action.action k hk).act
        u ≫ act = s ≫ z ∧ u ≫ π = t ≫ z ∧
          (derivedInverseImage u).map ((η.datum k hk).iso.hom ≫ centralPointUnitMap π c) =
            (derivedInverseImage u).map (centralPointUnitMap act c)

end Expected
end RepTheorySurvey.Geometric.CentralFrameDescentSpecs
