import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralFrameDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.CentralFrameDescent

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open CentralFrameDescentSpecs CentralFrameDescentSpecs.Expected
open ConvolutionConstantDescentSpec (shiftedConstantPullback)
open Analytic.DerivedPullbackPasting.Expected (squareValue)

private theorem centralPair_difference (a : ℤ) : difference (centralPair a) = 0 := by
  change (a - a).toNat = 0
  simp

private theorem centralSpace_subsingleton (a : ℤ) (N : ℕ)
    (hN : OrbitBound (centralPair a) N) : Subsingleton (SchubertSpace (centralPair a) N hN) := by
  obtain ⟨e, _, _⟩ := RankTwoSchubertStrata.schubertStratification (centralPair a) N hN
  have he (p : SchubertSpace (centralPair a) N hN) : (e p).val.val = scalarLattice 2 a := by
    have hp := (e p).property
    change (e p).val.val ∈ closureLattices (centralPair a) at hp
    rw [(RankTwoSchubertStrata.equalPairOrbit (centralPair a) N hN rfl).1] at hp
    exact hp
  exact ⟨fun p q ↦ e.injective (Subtype.ext (Subtype.ext ((he p).trans (he q).symm)))⟩

private theorem normalizedTopUnit {J : JetSystem.{0}} {X : TopCat.{0}} {d : ℕ}
    (hd : d = 0) {A : JetAction J X} (adj : DerivedAdjunctions.{0})
    (η : A.Equivariance (shiftedConstant X d).obj)
    (hη : NormalizedICDatum (@adj) A (.top X d) η) :
    ∃ c : (shiftedConstant X d).obj ≅ (shiftedConstant X 0).obj,
      ∀ (k : ℕ) (hk : A.cutoff ≤ k),
        (η.datum k hk).iso.hom ≫ centralPointUnitMap (AnalyticAction.projection (J.group k) X) c =
          centralPointUnitMap (A.action k hk).act c := by
  subst d
  cases hη with
  | top e coefficients =>
    refine ⟨Iso.refl _, fun k hk ↦ ?_⟩
    rw [coefficients k hk]
    simp [centralPointUnitMap]

private theorem pointNormalization {J : GL2JetParameters} {a : ℤ} {N : ℕ}
    {hN : OrbitBound (centralPair a) N} (B : SchubertJetAction J (centralPair a) N hN)
    (adj : DerivedAdjunctions.{0}) {d k : ℕ}
    {P : Stratification (SchubertSpace (centralPair a) N hN)}
    {D : DimensionFiltration (SchubertSpace (centralPair a) N hN) d}
    (hD : IsNormalizedOrbitIC (centralPair a) N hN (𝟙 _) k P D) (hk : k = 0)
    (η : B.action.Equivariance (complex D).obj)
    (hη : NormalizedICDatum (@adj) B.action D η) :
    ∃ c : (complex D).obj ≅ (shiftedConstant (SchubertSpace (centralPair a) N hN) 0).obj,
      CentralPointCoefficients B η c := by
  subst k
  cases hD with
  | top stage perverse =>
    obtain ⟨c, hc⟩ := normalizedTopUnit (centralPair_difference a) (@adj) η hη
    have := centralSpace_subsingleton a N hN
    exact ⟨c, fun k hk ↦ ⟨fun _ _ ↦ Subsingleton.elim _ _, hc k hk⟩⟩

theorem centralPointNormalization : CentralPointNormalization := by
  intro J a N hN B adj C P D hD η hη
  obtain ⟨c, hc⟩ := pointNormalization B (@adj) hD (by rw [centralPair_difference]) η hη
  refine ⟨c, hc, fun z ↦ ?_⟩
  unfold centralPointUnitMap
  infer_instance

theorem leftFrameComparison : LeftFrameComparison := by
  intro J X A F G i k hk
  let q := (A.action k hk).act
  let v : (derivedInverseImage q).obj G.obj ≅ (derivedInverseImage q).obj F.obj :=
    (derivedInverseImage q).mapIso (A.forget.mapIso i)
  let e := F.equivariance.datum k hk
  refine ⟨v ≪≫ e.iso, rfl, ?_⟩
  have hb : (derivedInverseImage (A.action k hk).act).map i.inv.hom ≫ (v ≪≫ e.iso).hom =
      e.iso.hom := by
    change v.inv ≫ v.hom ≫ e.iso.hom = e.iso.hom
    exact v.inv_hom_id_assoc _
  dsimp only
  rw [hb]
  exact e.multiplication

private theorem comparisonNaturality {ι C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    (P : ι → C ⥤ D) (S T : D ⥤ E) {H : ι → Prop}
    (square : ∀ j, H j → ((P j ⋙ S) ≅ (P j ⋙ T)))
    (p q : ι) (hqp : q = p) {G F : C} (i : G ≅ F) (hp : H p) (hq : H q) :
    let d := (P q).mapIso i ≪≫ eqToIso (congrArg (fun j ↦ (P j).obj F) hqp)
    (square q hq).hom.app G ≫ T.map d.hom = S.map d.hom ≫ (square p hp).hom.app F := by
  cases hqp
  simpa only [eqToIso_refl, Iso.trans_refl, Functor.mapIso_hom, Functor.comp_map] using
    ((square p hp).hom.naturality i.hom).symm

theorem rightFrameComparison : RightFrameComparison := by
  intro J R X A F G i p q hqp
  let v : G.obj ≅ F.obj := A.forget.mapIso i
  refine ⟨(derivedInverseImage q).mapIso v ≪≫
    eqToIso (congrArg (fun f : R ⟶ X ↦ (derivedInverseImage f).obj F.obj) hqp), rfl, ?_⟩
  intro V s t hp hq
  exact comparisonNaturality (fun j : R ⟶ X ↦ derivedInverseImage j)
    (derivedInverseImage s) (derivedInverseImage t)
    (H := fun j ↦ s ≫ j = t ≫ j) (fun _ h ↦ squareValue h) p q hqp v hp hq

theorem rightPointComparison : RightPointComparison := by
  intro J a N hN B C P η c hc k hk R V x s t u hu
  obtain ⟨hfixed, hcoeff⟩ := hc k hk
  refine ⟨TopCat.ext (fun v ↦ ?_), TopCat.ext (fun v ↦ hu v), ?_⟩
  · change (B.action.action k hk).act (u v) = x
    exact (hfixed (u v).1 (u v).2).trans (hu v)
  · exact congrArg (fun f ↦ (derivedInverseImage u).map f) hcoeff

end RepTheorySurvey.Geometric.CentralFrameDescent
