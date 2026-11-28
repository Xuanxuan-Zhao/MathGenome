import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionActionComparisons
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepLocalCohomology
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralMinusculeRule
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeConvolutionSquare
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralLatticeTranslation
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.JetEquivariantRestriction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionBundle
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.IntervalProjectionPullback
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.PositiveJetTruncationPullback
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SupportIntersectionJetDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertSupportStages
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open LinearAlgebraicGroups (Points testSpec)
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.CentralMinusculeRule

open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs MinusculeAndTwoStepSpecs
open CentralLatticeTranslationSpecs CentralMinusculeRuleSpecs
open MinusculeConvolutionSquareSpecs
open ConvolutionUnitConeSpecs
open ConvolutionBundleSpecs (firstStage OrderedProduct firstPlane secondPlane)
open ConvolutionFrameQuotientSpecs (FrameRepresentative)
open ConvolutionFrameOverlapSpecs (ActualDescent)
open Analytic
open Analytic.IntersectionComplex (DimensionFiltration complex boundedBelowPullbackComposition)
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open EquivariantHomeomorphismDirectImageSpecs (EquivariantDirectImageComparison)

open private translate_eq_smul inversePullbackComparison from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralLatticeTranslation
open private colength_bound from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
open private pullbackEquivalence from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem translate_commutes (hs : ScalarTranslation) (a : ℤ) (g : Loop)
    (L : GL2Lattice) : translate a (g • L) = g • translate a L := by
  simp only [translate_eq_smul, ← mul_smul, hs.2.2.2.1 a g]

private def translationChart (hs : ScalarTranslation) (s : ℤ) : Gr ≃ₜ Gr where
  toFun := translate s
  invFun := translate (-s)
  left_inv L := by rw [hs.2.1, neg_add_cancel, hs.2.2.1]
  right_inv L := by rw [hs.2.1, add_neg_cancel, hs.2.2.1]
  continuous_toFun := (hs.2.2.2.2.2.2 s).1
  continuous_invFun := (hs.2.2.2.2.2.2 s).2

private theorem translate_scalar (hs : ScalarTranslation) (s n : ℤ) :
    translate s (scalarLattice 2 n) = scalarLattice 2 (s + n) := by
  rw [← hs.1 n, hs.2.1, hs.1]

private theorem translate_mono (s : ℤ) {L M : GL2Lattice} (h : L.val ≤ M.val) :
    (translate s L).val ≤ (translate s M).val :=
  Submodule.map_mono h

private theorem scalar_mono {a b : ℤ} (h : b ≤ a) :
    (scalarLattice 2 a).val ≤ (scalarLattice 2 b).val := by
  have hm : scalarLattice 2 a ∈ gl2Orbit (centralPair a) := by
    refine ⟨1, ?_⟩
    change (1 : PositiveGL 2) • _ = _
    rw [one_smul]
    congr 1
    funext i
    simp [pairCoweight]
  exact ((RankTwoSchubertStrata.smithClassification.2 _ _ hm).2.1 b).mpr h

private theorem lower_natAbs (z : ℤ) : -(z.natAbs : ℤ) ≤ z := by
  have h := Int.le_natAbs (a := -z)
  rw [Int.natAbs_neg] at h
  omega

private theorem translate_bound (hs : ScalarTranslation) (s : ℤ) (N : ℕ) {L : Gr}
    (hL : L ∈ boundedSet N) : translate s L ∈ boundedSet (N + s.natAbs) := by
  have hlo := translate_mono s hL.1
  have hhi := translate_mono s hL.2
  rw [translate_scalar hs] at hlo hhi
  exact ⟨(scalar_mono (by have := Int.le_natAbs (a := s); omega)).trans hlo,
    hhi.trans (scalar_mono (by have := lower_natAbs s; omega))⟩

private def translatedStages (hs : ScalarTranslation) {c : ContinuousJets}
    (D : GrassmannianStages c) (s : ℤ) : TranslatedStages D s where
  chart := TopCat.isoOfHomeo (translationChart hs s)
  onLattices _ := rfl
  onInverse _ := rfl
  commutes g L := translate_commutes hs s (positiveGLMap 2 g) L
  intoSymmetric N := by
    refine ⟨N + s.natAbs, ?_⟩
    rintro _ ⟨p, rfl⟩
    apply translate_bound hs
    exact D.isBoundedSet N ▸ p.property
  fromSymmetric N := by
    refine ⟨N + (-s).natAbs, ?_⟩
    intro L hL
    refine ⟨⟨translate (-s) L, (D.isBoundedSet _).symm ▸ translate_bound hs (-s) N hL⟩, ?_⟩
    change translate s (translate (-s) L) = L
    rw [hs.2.1, add_neg_cancel, hs.2.2.1]

private theorem colength_one_closure : colength 1 = closureLattices minusculePair := by
  rw [MinusculeAndTwoStep.minusculeOrbit.1]
  ext L
  constructor
  · intro h
    exact ⟨minusculePair, ⟨0, by decide, by simp, by simp⟩, h⟩
  · rintro ⟨ab, ⟨j, hj, h₁, h₂⟩, hL⟩
    have h0 : j = 0 := by
      change 2 * (j : ℤ) ≤ 1 at hj
      omega
    have he : ab = minusculePair := Subtype.ext (Prod.ext
      (by simpa [h0] using h₁) (by simpa [h0] using h₂))
    exact he ▸ hL

private theorem firstStage_iff (g : Loop) :
    coset (PositiveGL 2) g ∈ firstStage ↔ g • standardLattice 2 ∈ colength 1 := by
  obtain ⟨e, he⟩ := BoundedLattices.glCosets 2
  constructor
  · rintro ⟨f, hf, hL⟩
    rwa [← he f, hf, he g] at hL
  · exact fun hL ↦ ⟨g, rfl, hL⟩

private theorem schubertFirst_iff (ab : DominantPair) (g : Loop) :
    coset (PositiveGL 2) g ∈ schubertFirst ab ↔
      g • standardLattice 2 ∈ closureLattices ab := by
  obtain ⟨e, he⟩ := BoundedLattices.glCosets 2
  constructor
  · rintro ⟨f, hf, hfg⟩
    change f • standardLattice 2 ∈ closureLattices ab at hf
    rwa [← he f, hfg, he g] at hf
  · exact fun hL ↦ ⟨g, hL, rfl⟩

private theorem translate_mem_closure (hs : ScalarTranslation) (s : ℤ) (ab : DominantPair)
    (L : GL2Lattice) :
    translate s L ∈ closureLattices (shiftPair s ab) ↔ L ∈ closureLattices ab := by
  rw [← (hs.2.2.2.2.2.1 s ab).2]
  exact ⟨fun ⟨x, hx, he⟩ ↦ (translationChart hs s).injective he ▸ hx,
    fun h ↦ ⟨L, h, rfl⟩⟩

private def translateFrames (hs : ScalarTranslation) (a b : ℤ) :
    FrameRepresentative ≃ ShiftedRepresentative a b :=
  let e : Loop × GL2Lattice ≃ Loop × GL2Lattice :=
    (Equiv.mulLeft (scalarLoop a)).prodCongr (translationChart hs b).toEquiv
  e.subtypeEquiv (by
    intro p
    change (coset (PositiveGL 2) p.1 ∈ firstStage ∧ p.2 ∈ colength 1) ↔
      (coset (PositiveGL 2) (scalarLoop a * p.1) ∈ schubertFirst (shiftPair a minusculePair) ∧
        translate b p.2 ∈ closureLattices (shiftPair b minusculePair))
    rw [firstStage_iff, schubertFirst_iff, mul_smul, ← translate_eq_smul,
      translate_mem_closure hs, translate_mem_closure hs, colength_one_closure])

private def translateOrdered (hs : ScalarTranslation) (a b : ℤ)
    (h : StableStage (PositiveGL 2) (colength 1)) :
    OrderedProduct h ≃ ShiftedOrdered a b :=
  Quotient.congr (translateFrames hs a b) (by
    intro p q
    change (∃ i : PositiveGL 2, q.val.1 = p.val.1 * (i : Loop) ∧
        q.val.2 = ((i⁻¹ : PositiveGL 2) : Loop) • p.val.2) ↔
      (∃ i : PositiveGL 2, scalarLoop a * q.val.1 =
          (scalarLoop a * p.val.1) * (i : Loop) ∧
        translate b q.val.2 = ((i⁻¹ : PositiveGL 2) : Loop) • translate b p.val.2)
    simp only [mul_assoc, mul_left_cancel_iff, ← translate_commutes hs b]
    constructor <;> rintro ⟨i, h₁, h₂⟩
    · exact ⟨i, h₁, congrArg (translate b) h₂⟩
    · exact ⟨i, h₁, (translationChart hs b).injective h₂⟩)

private theorem translated_terminal (hs : ScalarTranslation) (a b : ℤ)
    (h : StableStage (PositiveGL 2) (colength 1)) (p : FrameRepresentative) :
    shiftedTerminal a b (translateOrdered hs a b h (Quotient.mk _ p)) =
      translate (a + b) (p.val.1 • p.val.2) := by
  change (scalarLoop a * p.val.1) • translate b p.val.2 = _
  rw [mul_smul, ← translate_commutes hs b, ← translate_eq_smul]
  exact hs.2.1 a b (p.val.1 • p.val.2)

private theorem translation_bound_exists (a : ℤ) (ab : DominantPair) :
    ∃ N : ℕ, OrbitBound (shiftPair a ab) N := by
  refine ⟨(ab.val.1 + a).natAbs + (ab.val.2 + a).natAbs, ?_⟩
  intro i
  have h₁ := Int.le_natAbs (a := ab.val.1 + a)
  have h₂ := lower_natAbs (ab.val.1 + a)
  have h₃ := Int.le_natAbs (a := ab.val.2 + a)
  have h₄ := lower_natAbs (ab.val.2 + a)
  have ha : ((ab.val.1 + a).natAbs : ℤ) ≤
      (((ab.val.1 + a).natAbs + (ab.val.2 + a).natAbs : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (Nat.le_add_right _ _)
  have hb : ((ab.val.2 + a).natAbs : ℤ) ≤
      (((ab.val.1 + a).natAbs + (ab.val.2 + a).natAbs : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (Nat.le_add_left _ _)
  fin_cases i
  · change _ ≤ ab.val.1 + a ∧ ab.val.1 + a ≤ _
    exact ⟨(neg_le_neg ha).trans h₂, h₁.trans ha⟩
  · change _ ≤ ab.val.2 + a ∧ ab.val.2 + a ≤ _
    exact ⟨(neg_le_neg hb).trans h₄, h₃.trans hb⟩

private theorem directImageComposition (adj : DerivedAdjunctions.{0}) {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Nonempty (derivedDirectImage (f ≫ g) ≅ derivedDirectImage f ⋙ derivedDirectImage g) :=
  ⟨(adj (f ≫ g)).rightAdjointUniq
    (((adj g).comp (adj f)).ofNatIsoLeft (boundedBelowPullbackComposition f g).symm)⟩

private theorem eq_of_shortCoordinates {m : ℕ} {L M : GL2Lattice}
    (hL : L ∈ colength m) (hM : M ∈ colength m)
    (h : latticeSubspace 0 m L = latticeSubspace 0 m M) : L = M := by
  let x : WindowLattice 2 0 m := ⟨L, by simpa using colength_bound hL, hL.1⟩
  let y : WindowLattice 2 0 m := ⟨M, by simpa using colength_bound hM, hM.1⟩
  obtain ⟨e, he, _⟩ := BoundedLattices.windowLatticeComparison 2 0 m
  have hxy : e x = e y := Subtype.ext ((he x).trans (h.trans (he y).symm))
  exact congrArg Subtype.val (e.injective hxy)

private theorem eq_of_mappedSubspace {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) {P Q : Submodule ℂ V}
    (h : P.map e.toLinearMap = Q.map e.toLinearMap) : P = Q := by
  exact Submodule.map_injective_of_injective e.injective h

private theorem frame_terminal_colength (p : FrameRepresentative) :
    p.val.1 • p.val.2 ∈ colength 2 := by
  obtain ⟨h, e, he, hF⟩ := ConvolutionBundle.twistedFlags
  have hr := (hF (e (Quotient.mk _ p))).1
  rw [he] at hr
  exact hr

private theorem translatedFlags_exists (hs : ScalarTranslation) {c : ContinuousJets}
    (S : LocalSquare c) (a b : ℤ)
    (hd : ActualDescent S.splitting.firstEq S.splitting.orderedEq) :
    Nonempty (TranslatedFlags S a b) := by
  obtain ⟨h, e, r, q, hq, hcoords, hcoeff⟩ := hd
  let E := translateOrdered hs a b h
  refine ⟨{
    frames := translateFrames hs a b
    onFrames := fun _ ↦ rfl
    quotient := E.symm.trans e
    relative := r
    projection := q
    quotientTopology := hq
    onQuotient := ?_
    coefficients := hcoeff
    firstLattice := ?_
    relativeLattice := ?_
    terminalLattice := ?_ }⟩
  · intro p
    change q p = e (E.symm (E (Quotient.mk _ p)))
    rw [Equiv.symm_apply_apply, (hcoords p).1]
  · intro p
    have hcoord := (S.minusculeCoordinates (firstStageMap (q p))).2.symm.trans
      (hcoords p).2.1
    exact eq_of_shortCoordinates (S.minusculeCoordinates _).1
      ((firstStage_iff p.val.1).mp p.property.1) (eq_of_mappedSubspace _ hcoord)
  · intro p
    have hcoord := (S.minusculeCoordinates (r p)).2.symm.trans (hcoords p).2.2.1
    exact eq_of_shortCoordinates (S.minusculeCoordinates _).1 p.property.2
      (eq_of_mappedSubspace _ hcoord)
  · intro y
    obtain ⟨p, hp⟩ := Quotient.exists_rep (E.symm y)
    have hy : E (Quotient.mk _ p) = y := by rw [hp, Equiv.apply_symm_apply]
    rw [← hy]
    change shiftedTerminal a b (E (Quotient.mk _ p)) =
      translate (a + b) (S.twoStepIC.lattice (convolutionMap (e (E.symm (E
        (Quotient.mk _ p)))))).val
    rw [Equiv.symm_apply_apply, ← (hcoords p).1, translated_terminal hs]
    congr 1
    have hcoord := (hcoords p).2.2.2.symm.trans
      (S.terminalCoordinates (convolutionMap (q p))).2
    exact eq_of_shortCoordinates (frame_terminal_colength p) (S.terminalCoordinates _).1
      (eq_of_mappedSubspace _ hcoord)

private theorem translatedIC_exists (ht : SchubertTranslation)
    (hc : CentralConvolution) {c : ContinuousJets} {ab : DominantPair} {Y : TopCat.{0}}
    {A : JetAction (jetSystem c) Y} {F : BoundedBelow Y} {α : A.Equivariance F.obj}
    (C : ICComparison ab A F α) (s : ℤ) : Nonempty (TranslatedIC C s) := by
  obtain ⟨M, hM⟩ := translation_bound_exists s ab
  obtain ⟨T⟩ := ht s ab 2 M C.bound hM
  obtain ⟨B⟩ := EquivariantIntersectionComplexes.schubertJetActionExists c _ M hM
  obtain ⟨_, _, _, _, _, exIC, _⟩ := hc.1
  obtain ⟨P, Q, hQ⟩ := exIC (shiftPair s ab) M hM
  have h := T.intertwines c ⟨C.action, C.actionActual⟩ B
  have hstrata : EquivariantIntersectionComplexes.PreservesOrbitStrata T.analyticIso := by
    obtain ⟨ι, hι⟩ := T.preservesStrata
    exact ⟨ι, fun j ↦ (hι j).2⟩
  obtain ⟨β, e, hβ, he⟩ :=
    EquivariantIntersectionComplexes.normalizedEquivarianceTransportOnOrbits
      C.adjunctions C.actionActual B.actual T.analyticIso hstrata h C.isIC hQ C.normalized
  have hcut : C.action.cutoff = B.action.cutoff := by
    rw [C.actionActual.1, B.actual.1]
    have he : ab.val.1 - ab.val.2 = (ab.val.1 + s) - (ab.val.2 + s) := by omega
    exact congrArg (fun z : ℤ ↦ z.toNat - 1) he
  have hcomp : JetMapsCommute A B.action (C.model.hom ≫ T.analyticIso.hom) := by
    intro k hk hl
    have hm : C.action.cutoff ≤ k := hcut.symm ▸ hl
    apply TopCat.ext
    rintro ⟨g, y⟩
    change (B.action.action k hl).act (g, T.analyticIso.hom (C.model.hom y)) =
      T.analyticIso.hom (C.model.hom ((A.action k hk).act (g, y)))
    rw [EquivariantIntersectionComplexes.intertwines_apply h k hm hl,
      EquivariantIntersectionComplexes.intertwines_apply C.action_commutes k hk hm]
  let v := C.model ≪≫ T.analyticIso
  let u : F.obj ≅ (derivedInverseImage v.hom).obj (complex Q).obj :=
    C.comparison ≪≫ (derivedInverseImage C.model.hom).mapIso e ≪≫
      ((derivedInverseImageComposition C.model.hom T.analyticIso.hom).app (complex Q).obj).symm
  have hu : IntertwinesPullback hcomp α β u.hom := by
    intro k hk hl
    have hm : C.action.cutoff ≤ k := hcut.symm ▸ hl
    have h₁ := (EquivariantIntersectionComplexes.commutes_iff C.action_commutes α C.datum
      C.comparison.hom k hk hm).mpr (C.equivariant k hk hm)
    have h₂ := (EquivariantIntersectionComplexes.commutes_iff h C.datum β
      e.hom k hm hl).mpr (he k hm hl)
    apply (EquivariantIntersectionComplexes.commutes_iff hcomp α β _ k hk hl).mp
    exact (JetEquivariantRestriction.equivariancePasting
      (C.action_commutes k hk hm) (h k hm hl) (hcomp k hk hl) _ _ _ _ _ h₁).1 h₂
  obtain ⟨w, hw⟩ := inversePullbackComparison hcomp α β u hu
  obtain ⟨i, _, hi⟩ :=
    (EquivariantHomeomorphismDirectImage.equivariantHomeomorphismDirectImage
      v C.adjunctions A B.action hcomp).1 F (complex Q) α β w hw
  exact ⟨⟨M, hM, T, B, h, P, Q, hQ, β, hβ, e, he, hcomp, hu, ⟨i, hi⟩,
    fun y ↦ T.onLattices (C.model.hom y) (C.lattice y) (C.coordinates y)⟩⟩

private theorem translatedFactorMaps {c : ContinuousJets} (S : LocalSquare c) {a b : ℤ}
    (A : TranslatedIC S.minusculeIC a) (B : TranslatedIC S.minusculeIC b)
    (F : TranslatedFlags S a b) : TranslatedFactorMaps S A B F := by
  refine ⟨⟨translatedFactorIso A (F.projection ≫ firstStageMap) ≪≫
      eqToIso (congrArg (fun f ↦ (derivedInverseImage f).obj (complex A.filtration).obj)
        (Category.assoc _ _ _))⟩, ⟨translatedFactorIso B F.relative⟩, ?_⟩
  intro p
  constructor
  · change schubertPointSubspace
      (A.translation.analyticIso.hom (S.minusculeIC.model.hom (firstStageMap (F.projection p)))) = _
    rw [A.onCoordinates, F.firstLattice, F.onFrames, mul_smul, translate_eq_smul]
  · change schubertPointSubspace
      (B.translation.analyticIso.hom (S.minusculeIC.model.hom (F.relative p))) = _
    rw [B.onCoordinates, F.relativeLattice, F.onFrames]

section FrameCoefficients

open AnalyticAction (Parameters)
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)
open ConvolutionFrameOverlapSpecs
  (pullbackFactorIso shiftedSingleMap commonImage FrameOverlapIdentification FrameActionIdentification)
open private postcompHom postcompHom_pullback
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage

/-- Pull an intertwining equation back along the map carrying a frame
change, with the comparison written on the composite lattice maps. -/
private theorem pullbackIntertwiningOnParameters {J : JetSystem.{0}} {W X Y : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {i : X ⟶ Y}
    (h : JetMapsCommute A B i) {F : Derived X} {G : Derived Y}
    (α : A.Equivariance F) (β : B.Equivariance G)
    (u : F ≅ (derivedInverseImage i).obj G) (hu : IntertwinesPullback h α β u.hom)
    (k : ℕ) (ha : A.cutoff ≤ k) (hb : B.cutoff ≤ k)
    (γ : W ⟶ Parameters (J.group k) X) {f₁ f₀ : W ⟶ X}
    (h₁ : γ ≫ (A.action k ha).act = f₁)
    (h₀ : γ ≫ AnalyticAction.projection (J.group k) X = f₀)
    (h₁' : (γ ≫ parameterInclusion (J.group k) i) ≫ (B.action k hb).act = f₁ ≫ i)
    (h₀' : (γ ≫ parameterInclusion (J.group k) i) ≫ AnalyticAction.projection (J.group k) Y =
      f₀ ≫ i) :
    (pullbackAlong u f₁).hom ≫
        pullbackMorphism _ h₁' h₀' (β.datum k hb).iso.hom =
      pullbackMorphism γ h₁ h₀ (α.datum k ha).iso.hom ≫ (pullbackAlong u f₀).hom := by
  let r := restrictedArrow h β k ha hb
  have hpost : postcompHom i (A.action k ha).act
      (AnalyticAction.projection (J.group k) X) G r =
      pullbackMorphism (parameterInclusion (J.group k) i) (h k ha hb)
        (projectionSquare _ i) (β.datum k hb).iso.hom := by
    simp [r, postcompHom, restrictedArrow]
  have hs : postcompHom i f₁ f₀ G (pullbackMorphism γ h₁ h₀ r) =
      pullbackMorphism _ h₁' h₀' (β.datum k hb).iso.hom := by
    rw [postcompHom_pullback, hpost, DerivedPullbackPasting.pullbackSuccessive]
  have hn := DerivedPullbackPasting.pullbackNaturality γ h₁ h₀ u.hom
    (α.datum k ha).iso.hom r (hu k ha hb)
  rw [← hs]
  simp only [pullbackAlong, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    postcompHom, Equiv.coe_fn_mk, Category.assoc, Iso.app_inv, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hn]

private theorem pullbackMorphism_changeSource {W X Y : TopCat.{0}}
    (γ : W ⟶ X) {a a' p : X ⟶ Y} {f₁ f₀ : W ⟶ Y}
    (h : a = a') (ha : γ ≫ a' = f₁) (hp : γ ≫ p = f₀)
    {F : Derived Y} (u : (derivedInverseImage a').obj F ⟶ (derivedInverseImage p).obj F) :
    pullbackMorphism γ ((congrArg (γ ≫ ·) h).trans ha) hp
      (eqToHom (congrArg (fun f ↦ (derivedInverseImage f).obj F) h) ≫ u) =
        pullbackMorphism γ ha hp u := by
  subst a'
  simp

private theorem translatedActionTransition {c : ContinuousJets} {S : LocalSquare c} {s : ℤ}
    (K : TranslatedIC S.minusculeIC s) {W : TopCat.{0}} {f₁ f₀ : W ⟶ minuscule}
    (γ : W ⟶ Parameters ((jetSystem c).group 1) minuscule)
    (h₁ : γ ≫ S.splitting.firstAction.act = f₁)
    (h₀ : γ ≫ AnalyticAction.projection ((jetSystem c).group 1) minuscule = f₀)
    (e : (inverseImage f₁).obj (rational minuscule) ⟶
      (inverseImage f₀).obj (rational minuscule))
    (he : (pullbackFactorIso f₁ 1).hom ≫ shiftedSingleMap 1 e ≫
          (pullbackFactorIso f₀ 1).inv =
        pullbackMorphism γ h₁ h₀ S.splitting.firstEq.iso.hom) :
    TranslatedActionTransition K γ h₁ h₀ e := by
  let v := S.minusculeIC.model.hom ≫ K.translation.analyticIso.hom
  have hk : K.targetAction.action.cutoff ≤ 1 := by
    rw [K.targetAction.actual.1]
    change ((1 + s - (0 + s) : ℤ).toNat - 1) ≤ 1
    omega
  have h₁ₘ : γ ≫ (S.minAction.action 1 S.minCutoff).act = f₁ :=
    (congrArg (γ ≫ ·) S.minActs).trans h₁
  have ht : (γ ≫ parameterInclusion ((jetSystem c).group 1) v) ≫
      (K.targetAction.action.action 1 hk).act = f₁ ≫ v := by
    rw [Category.assoc, K.composedCommutes 1 S.minCutoff hk, ← Category.assoc, h₁ₘ]
  have hp : (γ ≫ parameterInclusion ((jetSystem c).group 1) v) ≫
      AnalyticAction.projection ((jetSystem c).group 1) _ = f₀ ≫ v := by
    rw [Category.assoc, projectionSquare, ← Category.assoc, h₀]
  have heq := pullbackIntertwiningOnParameters K.composedCommutes S.minDatum K.datum K.localIso
    K.composedIntertwines 1 S.minCutoff hk γ h₁ₘ h₀ ht hp
  have hOld : pullbackMorphism γ h₁ₘ h₀ (S.minDatum.datum 1 S.minCutoff).iso.hom =
      pullbackMorphism γ h₁ h₀ S.splitting.firstEq.iso.hom := by
    rw [S.minDatumAtTwo]
    exact pullbackMorphism_changeSource γ S.minActs h₁ h₀ _
  rw [hOld, ← he] at heq
  refine ⟨hk, ht, hp, ?_⟩
  simp only [TranslatedFactorTransition, translatedFactorIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [heq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem translatedUnchangedFactor {c : ContinuousJets} {S : LocalSquare c} {s : ℤ}
    (K : TranslatedIC S.minusculeIC s) {W : TopCat.{0}} {f₁ f₀ : W ⟶ minuscule}
    (h : f₁ = f₀) : TranslatedUnchangedFactor K h := by
  subst f₀
  simp [TranslatedUnchangedFactor, TranslatedFactorTransition, shiftedSingleMap]

set_option maxHeartbeats 500000 in
private theorem translatedTensorDescent (hs : ScalarTranslation) {c : ContinuousJets}
    (S : LocalSquare c) {a b : ℤ}
    (A : TranslatedIC S.minusculeIC a) (B : TranslatedIC S.minusculeIC b)
    (F : TranslatedFlags S a b) : TranslatedTensorDescent S A B F := by
  obtain ⟨μ, d, hμ, hd, hOverlap, hAction⟩ := F.coefficients
  refine ⟨d, ?_, ?_⟩
  · obtain ⟨γ, h₁, h₀, hgeom, hi₁, hi₀, e₂, he₂, ht⟩ := hOverlap
    refine ⟨γ, h₁, h₀, ?_, hi₁, hi₀, e₂, translatedUnchangedFactor A (by
      simp only [← Category.assoc, commonImage]), translatedActionTransition B γ h₁ h₀ e₂ he₂, ht⟩
    intro w
    obtain ⟨g, hf, hr, hγ⟩ := hgeom w
    refine ⟨g, ?_, ?_, hγ⟩
    · simp only [F.onFrames, hf, mul_assoc]
    · rw [F.onFrames, F.onFrames]
      change translate b _ = _
      rw [hr, translate_commutes hs]
  · obtain ⟨r₁, hq₁, h₁, hy, hgeom, hi₁, hi₀, e₁, he₁, ht⟩ := hAction
    refine ⟨r₁, hq₁, h₁, hy, ?_, hi₁, hi₀, e₁, ?_, translatedUnchangedFactor B hy, ht⟩
    · intro w
      obtain ⟨g, hg, hf, hr⟩ := hgeom w
      refine ⟨g, hg, ?_, ?_⟩
      · rw [F.onFrames, F.onFrames]
        change scalarLoop a * (r₁ w).val.1 = positiveGLMap 2 g * (scalarLoop a * w.2.val.1)
        change (r₁ w).val.1 = positiveGLMap 2 g * w.2.val.1 at hf
        rw [hf, ← mul_assoc, hs.2.2.2.1 a (positiveGLMap 2 g), mul_assoc]
      · rw [F.onFrames, F.onFrames]
        exact congrArg (translate b) hr
    · exact translatedActionTransition A _ h₁ (TopCat.ext (fun _ ↦ rfl)) e₁ he₁

end FrameCoefficients

set_option maxHeartbeats 600000 in
private theorem translatedTerminalScheme (hw : WindowTranslation)
    {c : ContinuousJets} (S : LocalSquare c)
    {a b : ℤ} (K : TranslatedIC S.twoStepIC (a + b)) (F : TranslatedFlags S a b) :
    TranslatedTerminalScheme S K F := by
  let t := a + b
  obtain ⟨d, hd, e, he, _⟩ := (hw t 0 2).2.2 (shortDimension 2)
  obtain ⟨z, hz⟩ := MinusculeAndTwoStep.twoStepStableModel.2.2.2.2
  let v := z.symm ≪≫ e
  refine ⟨d, ConvolutionBundleSpecs.terminalProjection ≫ v.hom, hd, ?_, ?_⟩
  · let : IsProper ConvolutionBundleSpecs.terminalProjection.left :=
      ConvolutionBundle.surfaceGeometry.2.2
    let : IsIso (v.hom.left) := inferInstanceAs (IsIso ((Over.forget _).map v.hom))
    exact inferInstanceAs
      (IsProper (ConvolutionBundleSpecs.terminalProjection.left ≫ v.hom.left))
  intro p
  let y := convolutionMap (F.quotient p)
  let L := S.twoStepIC.lattice y
  let u : WindowLattice 2 0 2 :=
    ⟨L.val, by simpa using colength_bound (S.terminalCoordinates y).1,
      (S.terminalCoordinates y).1.1⟩
  let q : Points (windowStableScheme 2 0 2 (shortDimension 2)) complexAlgebra := y ≫ z.inv
  have hq : q ≫ z.hom = y := by simp [q]
  have hcoord := hz q
  change secondPlane (q ≫ z.hom) =
    (windowSchemeSubspace q).map twoStepCoordinates.toLinearMap at hcoord
  rw [hq] at hcoord
  have hP : windowSchemeSubspace q = latticeSubspace 0 2 L.val :=
    eq_of_mappedSubspace _ (hcoord.symm.trans (S.terminalCoordinates y).2)
  constructor
  · have hm : F.quotient p ≫ (ConvolutionBundleSpecs.terminalProjection ≫ v.hom) =
        q ≫ e.hom := by
      have hy : y = F.quotient p ≫ ConvolutionBundleSpecs.terminalProjection := rfl
      simp only [v, q, hy, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    calc
      _ = windowSchemeSubspace (q ≫ e.hom) :=
        congrArg (fun w : Points (windowStableScheme 2 (0 + t) 2 d) complexAlgebra ↦
          windowSchemeSubspace w) hm
      _ = (windowSchemeSubspace q).map (shiftWindow t 0 2).toLinearMap := he q
      _ = (latticeSubspace 0 2 L.val).map (shiftWindow t 0 2).toLinearMap :=
        congrArg (Submodule.map (shiftWindow t 0 2).toLinearMap) hP
      _ = latticeSubspace (0 + t) 2 (translate t L.val) := ((hw t 0 2).1 u).2.symm
      _ = _ := congrArg (latticeSubspace (0 + t) 2) (F.terminalLattice p).symm
  · exact (K.onCoordinates y).trans
      (congrArg (latticeSubspace (-(K.bound : ℤ)) (2 * K.bound)) (F.terminalLattice p).symm)

section ShiftedStages

open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)
open Analytic.IntersectionComplex (directImageComparison)
open AnalyticAction (Parameters)
open private pushComposition paste_comm EquivariantClosedDirectImageComposition.compare
  compare_paste DirectImageComparisonAt
  from_intertwining to_intertwining
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantClosedDirectImageComposition
open private derivedPullbackEquivalence from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage

local notation "R" => derivedDirectImage
local notation "L" => boundedBelowInverseImage
private abbrev stageMate := @EquivariantClosedDirectImageComposition.compare

private theorem translatedStageGeometry (hs : ScalarTranslation) {c : ContinuousJets}
    {D : GrassmannianStages c} {s : ℤ} (T : TranslatedStages D s) :
    TranslatedStageGeometry T := by
  refine ⟨fun n ↦ (TopCat.homeoOfIso T.chart).isClosedEmbedding.comp
    (D.stages.closed n).isClosedEmbedding_subtypeVal, ?_, ?_, ?_⟩
  · intro n m h
    rw [← Category.assoc, D.stages.transition_inclusion h]
  · intro n k hk g p
    change T.chart.hom (((D.actions.stageAction n).action k hk).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)).val = positiveGLMap 2 g • T.chart.hom p.val
    rw [D.actionOnLattices n k hk g p, T.commutes]
  · intro n i
    obtain ⟨ab, hRange, hDim⟩ := D.orbitStrata n i
    refine ⟨ab, ?_, ?_⟩
    · rw [← (hs.2.2.2.2.2.1 s ab).1]
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        let x := ((D.stratification n).stratum i).inclusion p
        have hp : x ∈ {x : D.stages.space n | x.val ∈ gl2Orbit ab} :=
          hRange ▸ Set.mem_range_self p
        exact ⟨⟨x.val, hp, (T.onLattices _).symm⟩, ⟨x, rfl⟩⟩
      · rintro ⟨⟨p, hp, hpeq⟩, ⟨x, hxeq⟩⟩
        have hx : p = x.val := (TopCat.homeoOfIso T.chart).injective
          ((T.onLattices p).trans (hpeq.trans hxeq.symm))
        have hxm : x ∈ {x : D.stages.space n | x.val ∈ gl2Orbit ab} := by
          change x.val ∈ gl2Orbit ab
          rwa [← hx]
        obtain ⟨r, hr⟩ := hRange.symm ▸ hxm
        exact ⟨r, (congrArg (fun y ↦ T.inclusion n y) hr).trans hxeq⟩
    · rw [hDim]
      change ((ab.val.1 - ab.val.2).toNat) = ((ab.val.1 + s - (ab.val.2 + s)).toNat)
      congr 1
      omega

private theorem transportedStageMorphism {c : ContinuousJets} {D : GrassmannianStages c}
    {s : ℤ} (T : TranslatedStages D s) {P Q : D.actions.Object} (u : P ⟶ Q)
    {F G : Derived Gr} (i : F ≅ T.realize.obj P.obj) (j : G ≅ T.realize.obj Q.obj) :
    T.Intertwines P Q i j (i.hom ≫ T.realize.map u.hom ≫ j.inv) := by
  intro n k hk
  let U := derivedInverseImage (T.inclusion n)
  let V := derivedInverseImage (D.stages.inclusion n)
  let s' := T.coefficientIso P i n
  let t' := T.coefficientIso Q j n
  let a := derivedInverseImage ((D.actions.stageAction n).action k hk).act
  let p := derivedInverseImage (AnalyticAction.projection ((jetSystem c).group k) (D.stages.space n))
  let f := i.hom ≫ T.realize.map u.hom ≫ j.inv
  have he : U.map f ≫ t'.hom = s'.hom ≫ V.map u.hom := by
    have hn := (T.restrictionIso n).hom.naturality u.hom
    change U.map (T.realize.map u.hom) ≫ (T.restrictionIso n).hom.app Q.obj =
      (T.restrictionIso n).hom.app P.obj ≫ V.map u.hom at hn
    change U.map f ≫ (U.map j.hom ≫ (T.restrictionIso n).hom.app Q.obj) =
      (U.map i.hom ≫ (T.restrictionIso n).hom.app P.obj) ≫ V.map u.hom
    rw [Category.assoc (U.map i.hom)]
    have hfj : f ≫ j.hom = i.hom ≫ T.realize.map u.hom := by simp [f]
    rw [← U.map_comp_assoc, hfj, U.map_comp, Category.assoc, hn]
  have hf := t'.eq_comp_inv.mpr he
  change a.map (U.map f) ≫ a.map t'.hom ≫ (Q.equivariance.datum n |>.datum k hk).iso.hom ≫ p.map t'.inv =
    (a.map s'.hom ≫ (P.equivariance.datum n |>.datum k hk).iso.hom ≫ p.map s'.inv) ≫ p.map (U.map f)
  rw [← a.map_comp_assoc, he, a.map_comp, Category.assoc, reassoc_of% (u.comm n k hk)]
  have hpull : p.map s'.inv ≫ p.map (U.map f) = p.map (V.map u.hom) ≫ p.map t'.inv := by
    rw [← p.map_comp, hf, Category.assoc, Iso.inv_hom_id_assoc, p.map_comp]
  simp only [Category.assoc, hpull]
  rfl

private def homeomorphismDirectImageIso (a : DerivedAdjunctions.{0})
    {X Y : TopCat.{0}} (v : X ≅ Y) :
    R v.hom ≅ L v.inv :=
  (a v.hom).rightAdjointUniq
    (pullbackEquivalence v).toAdjunction

private theorem occupiesTranslatedStage (a : DerivedAdjunctions.{0}) {c : ContinuousJets}
    {D : GrassmannianStages c} {s : ℤ} (T : TranslatedStages D s) {F : Derived Gr}
    (h : IsFiniteStagePerverse D.stages D.stratification F) :
    ∃ (n : ℕ) (P : MiddlePerverse (D.stratification n))
      (hp : DerivedCategory.TStructure.t.plus P.obj),
      Nonempty (((R (T.inclusion n)).obj ⟨P.obj, hp⟩).obj ≅ T.realize.obj F) := by
  obtain ⟨n, P, ⟨e⟩⟩ := h
  obtain ⟨hp, _⟩ := P.property.2
  obtain ⟨b⟩ := EquivariantIntersectionComplexes.closedAdjunctionExists (D.stages.closed n)
  let I := DerivedCategory.Plus.ι (C := Sheaves Gr)
  let Q : BoundedBelow (D.stages.space n) := ⟨P.obj, hp⟩
  let e₁ := ((a (D.stages.inclusion n)).rightAdjointUniq b).app Q
  let e₂ := (pushComposition a (D.stages.inclusion n) T.chart.hom).app Q
  let e₃ := (homeomorphismDirectImageIso a T.chart).app ((R (D.stages.inclusion n)).obj Q)
  exact ⟨n, P, hp, ⟨I.mapIso (e₂ ≪≫ e₃) ≪≫ T.realize.mapIso (I.mapIso e₁ ≪≫ e)⟩⟩

set_option maxHeartbeats 650000 in
/-- Cancel the direct-image comparison of the first map in a pair of
composable equivariant squares. This uses the pasted canonical mates, so
the remaining equation is the one for direct image by the second map. -/
private theorem directImageComparisonAt_cancel {U V W X Y Z : TopCat.{0}}
    (a : DerivedAdjunctions.{0}) {t₁ : U ⟶ V} {t₂ : V ⟶ W} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x₁ p₁ : U ⟶ X} {x₂ p₂ : V ⟶ Y} {x₃ p₃ : W ⟶ Z}
    (a₁ : t₁ ≫ x₂ = x₁ ≫ f) (a₂ : t₂ ≫ x₃ = x₂ ≫ g)
    (b₁ : t₁ ≫ p₂ = p₁ ≫ f) (b₂ : t₂ ≫ p₃ = p₂ ≫ g)
    {F : BoundedBelow X} {G : BoundedBelow Y} {K : BoundedBelow Z}
    (c₁ : (R f).obj F ≅ G) (c₂ : (R g).obj G ≅ K)
    {γ₁ : (L x₁).obj F ⟶ (L p₁).obj F} {γ₂ : (L x₂).obj G ⟶ (L p₂).obj G}
    {γ₃ : (L x₃).obj K ⟶ (L p₃).obj K}
    (h₁ : DirectImageComparisonAt a a₁ b₁ c₁ γ₁ γ₂)
    (h₃ : DirectImageComparisonAt a (paste_comm a₁ a₂) (paste_comm b₁ b₂)
      ((pushComposition a f g).app F ≪≫ (R g).mapIso c₁ ≪≫ c₂) γ₁ γ₃) :
    DirectImageComparisonAt a a₂ b₂ c₂ γ₂ γ₃ := by
  let c := (pushComposition a f g).app F ≪≫ (R g).mapIso c₁ ≪≫ c₂
  let act := paste_comm a₁ a₂
  let proj := paste_comm b₁ b₂
  let q := pushComposition a t₁ t₂
  obtain ⟨ha₁, hb₁, ht₁⟩ := h₁
  obtain ⟨ha₃, hb₃, ht₃⟩ := h₃
  have hleft : γ₂ ≫ stageMate a b₁ c₁ = stageMate a a₁ c₁ ≫ (R t₁).map γ₁ :=
    from_intertwining c₁ γ₂ _ _ _ ht₁
  have hpaste : γ₃ ≫ stageMate a proj c = stageMate a act c ≫ (R (t₁ ≫ t₂)).map γ₁ :=
    from_intertwining c γ₃ _ _ _ ht₃
  have iso₂ {y₁ : U ⟶ X} {y₂ : V ⟶ Y} {y₃ : W ⟶ Z}
      (s₁ : t₁ ≫ y₂ = y₁ ≫ f) (s₂ : t₂ ≫ y₃ = y₂ ≫ g)
      (h1 : IsIso (directImageComparison s₁ (a t₁) (a f) F))
      (h3 : IsIso (directImageComparison (paste_comm s₁ s₂) (a (t₁ ≫ t₂)) (a (f ≫ g)) F)) :
      IsIso (directImageComparison s₂ (a t₂) (a g) G) := by
    have he := compare_paste a s₁ s₂ c₁ c₂
    have : IsIso (stageMate a s₁ c₁) := by dsimp only [stageMate, EquivariantClosedDirectImageComposition.compare]; infer_instance
    have : IsIso (stageMate a (paste_comm s₁ s₂) c) := by dsimp only [stageMate, EquivariantClosedDirectImageComposition.compare]; infer_instance
    have h : IsIso (stageMate a s₂ c₂ ≫ (R t₂).map (stageMate a s₁ c₁)) := he ▸ inferInstance
    have h' := (isIso_comp_right_iff _ _).mp h
    exact (isIso_comp_left_iff _ _).mp h'
  refine ⟨iso₂ a₁ a₂ ha₁ ha₃, iso₂ b₁ b₂ hb₁ hb₃, ?_⟩
  apply to_intertwining c₂ γ₃ _ _ _
  have : IsIso (stageMate a b₁ c₁) := by dsimp only [stageMate, EquivariantClosedDirectImageComposition.compare]; infer_instance
  apply (cancel_mono ((R t₂).map (stageMate a b₁ c₁))).mp
  have ha := compare_paste a a₁ a₂ c₁ c₂
  have hb := compare_paste a b₁ b₂ c₁ c₂
  calc
    (γ₃ ≫ stageMate a b₂ c₂) ≫ (R t₂).map (stageMate a b₁ c₁) =
        (γ₃ ≫ stageMate a proj c) ≫ q.hom.app _ := by
          simp only [Category.assoc, ← hb]
          rfl
    _ = (stageMate a act c ≫ (R (t₁ ≫ t₂)).map γ₁) ≫ q.hom.app _ := by rw [hpaste]
    _ = (stageMate a a₂ c₂ ≫ (R t₂).map γ₂) ≫ (R t₂).map (stageMate a b₁ c₁) := by
      rw [Category.assoc, q.hom.naturality, ← Category.assoc, ha]
      change (_ ≫ (R t₂).map (stageMate a a₁ c₁)) ≫ (R t₂).map ((R t₁).map γ₁) = _
      rw [Category.assoc, ← Functor.map_comp, ← hleft, Functor.map_comp]
      simp only [stageMate, Category.assoc]

private theorem actionSquareAfterIso {H : AnalyticGroup.{0}} {X Y Z : TopCat.{0}}
    {A : AnalyticAction H X} {B : AnalyticAction H Y} {C : AnalyticAction H Z}
    (v : X ≅ Y) (j : Y ⟶ Z)
    (h₁ : parameterInclusion H v.hom ≫ B.act = A.act ≫ v.hom)
    (h₂ : parameterInclusion H (v.hom ≫ j) ≫ C.act = A.act ≫ (v.hom ≫ j)) :
    parameterInclusion H j ≫ C.act = B.act ≫ j := by
  apply TopCat.ext
  rintro ⟨g, y⟩
  obtain ⟨x, rfl⟩ := (TopCat.homeoOfIso v).surjective y
  change C.act (g, j (v.hom x)) = j (B.act (g, v.hom x))
  have e₁ : B.act (g, v.hom x) = v.hom (A.act (g, x)) :=
    congrArg (fun f ↦ f (g, x)) h₁
  have e₂ : C.act (g, j (v.hom x)) = j (v.hom (A.act (g, x))) :=
    congrArg (fun f ↦ f (g, x)) h₂
  exact e₂.trans (congrArg (fun z ↦ j z) e₁).symm

set_option maxHeartbeats 700000 in
private theorem closedStageAfterTranslation {J : JetSystem.{0}} {X Y Z : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {C : JetAction J Z}
    {F : BoundedBelow X} {G : BoundedBelow Y} {K : BoundedBelow Z}
    {α : A.Equivariance F.obj} {β : B.Equivariance G.obj} {δ : C.Equivariance K.obj}
    (a : DerivedAdjunctions.{0}) (v : X ≅ Y) (h : JetMapsCommute A B v.hom)
    (hcut : A.cutoff ≤ C.cutoff) (j : Y ⟶ Z)
    (e : ((R (v.hom ≫ j)).obj F).obj ≅ K.obj)
    (he : ExtendsAtStage (v.hom ≫ j) a α δ e)
    (hlocal : EquivariantDirectImageComparison a A B v.hom h F α G β) :
    ∃ d : ((R j).obj G).obj ≅ K.obj, ExtendsAtStage j a β δ d := by
  obtain ⟨c₁, hc₁⟩ := hlocal
  let I := DerivedCategory.Plus.ι (C := Sheaves Z)
  let d := ((R j).mapIso c₁).symm ≪≫ ((pushComposition a v.hom j).app F).symm ≪≫ ObjectProperty.isoMk _ e
  have ec : (pushComposition a v.hom j).app F ≪≫ (R j).mapIso c₁ ≪≫ d = ObjectProperty.isoMk _ e := by
    apply Iso.ext
    simp [d]
  refine ⟨I.mapIso d, ?_⟩
  intro k hy hz
  let hx := hcut.trans hz
  let H := J.group k
  let t₁ := parameterInclusion H v.hom
  let t₂ := parameterInclusion H j
  let s₁ := h k hx hy
  let p₁ := projectionSquare H v.hom
  let p₂ := projectionSquare H j
  obtain ⟨sg, ha₃, hb₃, ht₃⟩ := he k hx hz
  let s₂ := actionSquareAfterIso v j s₁ sg
  obtain ⟨ha₁, hb₁, ht₁⟩ := hc₁ k hx hy
  let γ₁ : (L (A.action k hx).act).obj F ⟶ (L (AnalyticAction.projection H X)).obj F :=
    ObjectProperty.homMk (α.datum k hx).iso.hom
  let γ₂ : (L (B.action k hy).act).obj G ⟶ (L (AnalyticAction.projection H Y)).obj G :=
    ObjectProperty.homMk (β.datum k hy).iso.hom
  let γ₃ : (L (C.action k hz).act).obj K ⟶ (L (AnalyticAction.projection H Z)).obj K :=
    ObjectProperty.homMk (δ.datum k hz).iso.hom
  have h₁ : DirectImageComparisonAt a s₁ p₁ c₁ γ₁ γ₂ :=
    ⟨ha₁, hb₁, ObjectProperty.hom_ext _ ht₁⟩
  have h₃ : DirectImageComparisonAt a (paste_comm s₁ s₂) (paste_comm p₁ p₂)
      ((pushComposition a v.hom j).app F ≪≫ (R j).mapIso c₁ ≪≫ d) γ₁ γ₃ := by
    rw [ec]
    refine ⟨ha₃, hb₃, ObjectProperty.hom_ext _ ?_⟩
    exact ht₃
  obtain ⟨hai, hpi, hcomm⟩ := directImageComparisonAt_cancel a s₁ s₂ p₁ p₂ c₁ d h₁ h₃
  exact ⟨s₂, hai, hpi, congrArg (fun u ↦ u.hom) hcomm⟩

open private changeCoefficients from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage

/-- The stage mates are invariant under changing the target to an
isomorphic realization with the conjugated equivariance. -/
private theorem extensionOnRealizedStage {J : JetSystem.{0}} {X Y : TopCat.{0}}
    {A : JetAction J Y} {B : JetAction J X} {F : BoundedBelow Y} {G G' : Derived X}
    (j : Y ⟶ X) (a : DerivedAdjunctions.{0}) {α : A.Equivariance F.obj}
    {β : B.Equivariance G} {e : ((R j).obj F).obj ≅ G}
    (he : ExtendsAtStage j a α β e) (u : G' ≅ G) :
    ExtendsAtStage j a α (changeCoefficients u β) (e ≪≫ u.symm) := by
  intro k hy hx
  obtain ⟨h, ha, hp, hm⟩ := he k hy hx
  refine ⟨h, ha, hp, ?_⟩
  let U := derivedInverseImage (B.action k hx).act
  let V := derivedInverseImage (AnalyticAction.projection (J.group k) X)
  change U.map (e.hom ≫ u.inv) ≫
      (U.map u.hom ≫ (β.datum k hx).iso.hom ≫ V.map u.inv) ≫
      V.map (u.hom ≫ e.inv) ≫ _ = _
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc _ u.inv u.hom,
    Iso.inv_hom_id]
  rw [U.map_id, V.map_id, Category.id_comp, Category.id_comp]
  exact hm

private theorem shiftedClosedExtension {c : ContinuousJets} {D : GrassmannianStages c}
    {s : ℤ} (T : TranslatedStages D s) {ab : DominantPair} {Y : TopCat.{0}}
    {A : JetAction (jetSystem c) Y} {F : BoundedBelow Y} {α : A.Equivariance F.obj}
    {C : ICComparison ab A F α} (K : TranslatedIC C s)
    (j : Y ⟶ Gr) (E : GrassmannianExtension D A F α j)
    (hcut : A.cutoff ≤ 1) :
    let v := C.model ≪≫ K.translation.analyticIso
    let k := v.inv ≫ j ≫ T.chart.hom
    IsClosedEmbedding k ∧
      Nonempty (TranslatedStageExtension T K.targetAction.action (complex K.filtration) K.datum k
        ⟨E.sheaf, E.perverse⟩) := by
  intro v k
  let a : DerivedAdjunctions.{0} := @C.adjunctions
  let I := DerivedCategory.Plus.ι (C := Sheaves Gr)
  let G := complex K.filtration
  have hv : IsClosedEmbedding v.inv := (TopCat.homeoOfIso v.symm).isClosedEmbedding
  have hj : IsClosedEmbedding (j ≫ T.chart.hom) :=
    (TopCat.homeoOfIso T.chart).isClosedEmbedding.comp E.closed
  have h : v.hom ≫ k = j ≫ T.chart.hom := by simp [k]
  obtain ⟨u, hu⟩ := inversePullbackComparison K.composedCommutes α K.datum K.localIso K.composedIntertwines
  obtain ⟨eK, heK⟩ := K.directImage
  let et := (pushComposition a j T.chart.hom).app F ≪≫
    (homeomorphismDirectImageIso a T.chart).app ((R j).obj F)
  let ek := ((R k).mapIso eK).symm ≪≫ ((pushComposition a v.hom k).app F).symm ≪≫
    eqToIso (congrArg (fun f ↦ (R f).obj F) h) ≪≫ et
  let ord := I.mapIso ek ≪≫ T.realize.mapIso E.ordinary
  refine ⟨hj.comp hv, ⟨⟨ord,
    occupiesTranslatedStage a T E.perverse, ?_⟩⟩⟩
  intro n hn
  obtain ⟨m, a', e, hm, hClosed, he⟩ := E.stagewise n hn
  let m' := v.inv ≫ m
  have hcomp : v.hom ≫ m' = m := by simp [m']
  have hf : m' ≫ T.inclusion n = k := by simp [m', k, ← hm, Category.assoc]
  let P : ObjectProperty (Derived Gr) := DerivedCategory.TStructure.t.plus
  let Q : BoundedBelow Gr := ⟨E.sheaf.obj, P.prop_of_iso E.ordinary ((R j).obj F).property⟩
  let Q' := (L (D.stages.inclusion n)).obj Q
  have hl : A.cutoff ≤ (D.actions.stageAction n).cutoff := by
    rw [D.actionCutoff]
    omega
  have hLocal : EquivariantDirectImageComparison a' A K.targetAction.action v.hom
      K.composedCommutes F α G K.datum := by
    obtain ⟨p, _, hp⟩ := (EquivariantHomeomorphismDirectImage.equivariantHomeomorphismDirectImage
      v a' A K.targetAction.action K.composedCommutes).1 F G α K.datum u hu
    exact ⟨p, hp⟩
  let e' : ((R (v.hom ≫ m')).obj F).obj ≅ Q'.obj :=
    eqToIso (congrArg (fun f ↦ ((R f).obj F).obj) hcomp) ≪≫ e
  have he' : ExtendsAtStage (v.hom ≫ m') a' α (E.sheaf.equivariance.datum n) e' := by
    generalize v.hom ≫ m' = m'' at hcomp ⊢
    subst m''
    simpa [e'] using he
  obtain ⟨d, hd⟩ := closedStageAfterTranslation (K := Q') a' v K.composedCommutes hl m' e' he' hLocal
  let w := T.coefficientIso E.sheaf ord n
  exact ⟨m', a', d ≪≫ w.symm, changeCoefficients w (E.sheaf.equivariance.datum n), hf,
    fun _ _ ↦ rfl, extensionOnRealizedStage m' a' hd w⟩

private theorem shiftedConvolutionExtension {c : ContinuousJets} {D : GrassmannianStages c}
    {s : ℤ} (T : TranslatedStages D s) (a : DerivedAdjunctions.{0}) (S : LocalSquare c)
    (j : surface ⟶ Gr)
    (E : GrassmannianExtension D S.terminalAction convolution S.convolutionDatum j) :
    Nonempty (TranslatedStageExtension T S.terminalAction convolution S.convolutionDatum
      (j ≫ T.chart.hom) ⟨E.sheaf, E.perverse⟩) := by
  let e := (pushComposition a j T.chart.hom).app convolution ≪≫
    (homeomorphismDirectImageIso a T.chart).app ((R j).obj convolution)
  let ord := DerivedCategory.Plus.ι.mapIso e ≪≫ T.realize.mapIso E.ordinary
  refine ⟨⟨ord, occupiesTranslatedStage a T E.perverse, ?_⟩⟩
  intro n hn
  obtain ⟨m, a', i, hm, _, hi⟩ := E.stagewise n hn
  let w := T.coefficientIso E.sheaf ord n
  exact ⟨m, a', i ≪≫ w.symm, changeCoefficients w (E.sheaf.equivariance.datum n),
    by rw [← Category.assoc, hm], fun _ _ ↦ rfl, extensionOnRealizedStage m a' hi w⟩

end ShiftedStages


section OrderedDirectImage

open ConvolutionActionComparisonsSpecs
open ConvolutionEquivariantSplittingSpecs (UsesConvolutionMates)
open TwoStepLocalCohomologySpecs (ComparisonTopology)
open AnalyticAction (Parameters)
open private comparisonTopology_of_openEmbedding normedOpenBasis
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepLocalCohomology
open private projectionMate_isIso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting

private theorem finiteJetComparisonTopology (c : ContinuousJets) (k : ℕ) :
    ComparisonTopology ((jetSystem c).group k).space := by
  let E := Fin 2 → Fin 2 → Fin (k + 1) → ℂ
  exact comparisonTopology_of_openEmbedding (c.coefficientOpen k)
    (show ComparisonTopology (TopCat.of E) from
      ⟨inferInstance, inferInstance, inferInstance, normedOpenBasis E⟩)

private theorem restrictConvolutionMates {H K : AnalyticGroup.{0}}
    {A : AnalyticAction H surface} {B : AnalyticAction H ordered}
    (h : Commutes A B) (φ : K.space →* H.space) (hφ : Continuous φ)
    (htop : ComparisonTopology K.space) (α : A.Equivariance convolution.obj)
    (hα : UsesConvolutionMates h α) :
    TruncatedConvolutionMates h φ hφ α := by
  obtain ⟨a, b, ha, hb, hp, hm, hα⟩ := hα
  let a' := DerivedLocalSheaves.derivedInverseDirectAdjunctionData (productMap K.space)
  have hp' : IsIso (projectionMate K.space a' b) := projectionMate_isIso htop a' b
  have hn := ConvolutionActionComparisons.derivedAdjunction_normalized (productMap K.space)
  obtain ⟨α', hα', hφ'⟩ := ConvolutionActionComparisons.parameterTransport h φ hφ a a' b
    α ha hn hb hp hp' hα
  have hm' := ConvolutionActionComparisons.actionMate_isIso (restrict_commutes h φ hφ) a' b
  exact ⟨α', ⟨a', b, hn, hb, hp', hm', hα'⟩, hφ'⟩

private theorem orderedConvolutionMates {c : ContinuousJets} (S : LocalSquare c) :
    TranslatedConvolutionMates S := by
  refine ⟨S.splitting.convolution_normalized, S.convolutionDatumAtTwo, ?_⟩
  intro k hk
  exact restrictConvolutionMates S.splitting.commutes (jetTruncation hk) (c.truncation hk)
    (finiteJetComparisonTopology c k) S.splitting.convolutionEq S.splitting.convolution_normalized

end OrderedDirectImage

section Assembly

open private pushComposition from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantClosedDirectImageComposition
open private jetActionAbove jetActionAbove_at constantJetEquivariance mapBiprodDescIsIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeConvolutionSquare

private def perverseCofanIsColimit {C : Type*} [Category C] {Q : ObjectProperty C}
    {X Y Z : Q.FullSubcategory} (u : X ⟶ Z) (v : Y ⟶ Z)
    (h : IsColimit (BinaryCofan.mk u.hom v.hom)) : IsColimit (BinaryCofan.mk u v) := by
  refine BinaryCofan.IsColimit.mk _ (fun {W} f g ↦ ObjectProperty.homMk
      (h.desc (BinaryCofan.mk f.hom g.hom))) ?_ ?_ ?_
  · intro W f g
    exact ObjectProperty.hom_ext _ (h.fac (BinaryCofan.mk f.hom g.hom) ⟨WalkingPair.left⟩)
  · intro W f g
    exact ObjectProperty.hom_ext _ (h.fac (BinaryCofan.mk f.hom g.hom) ⟨WalkingPair.right⟩)
  · intro W f g m hm hn
    apply ObjectProperty.hom_ext
    apply BinaryCofan.IsColimit.hom_ext h
    · exact (congrArg (fun q ↦ q.hom) hm).trans
        (h.fac (BinaryCofan.mk f.hom g.hom) ⟨WalkingPair.left⟩).symm
    · exact (congrArg (fun q ↦ q.hom) hn).trans
        (h.fac (BinaryCofan.mk f.hom g.hom) ⟨WalkingPair.right⟩).symm

private theorem translatedConvolutionDatum {c : ContinuousJets} (S : LocalSquare c) :
    Nonempty (TranslatedConvolutionDatum S) := by
  let B : JetAction (jetSystem c) ordered := jetActionAbove S.splitting.orderedAction
  have hB : B.cutoff = 1 := rfl
  have h₁ : (B.action 1 hB.le).act = S.splitting.orderedAction.act := jetActionAbove_at _
  obtain ⟨β, hβ⟩ := constantJetEquivariance B 2
  refine ⟨⟨B, β, hB, h₁, ?_, hβ, orderedConvolutionMates S⟩⟩
  rw [hβ, S.splitting.ordered_normalized]
  simp only [Iso.trans_hom, Iso.symm_hom]
  have reindex {X Y : TopCat.{0}} {p q : X ⟶ Y} (h : p = q) :
      (shiftedConstantPullback p 2).hom =
        eqToHom (congrArg (fun u ↦ (derivedInverseImage u).obj
          (Analytic.IntersectionComplex.shiftedConstant Y 2).obj) h) ≫
          (shiftedConstantPullback q 2).hom := by
    subst q
    simp
  rw [reindex h₁, Category.assoc]
  rfl

set_option maxHeartbeats 650000 in
private theorem translatedExtension (hs : ScalarTranslation) (a : DerivedAdjunctions.{0})
    {c : ContinuousJets} (D : GrassmannianStages c) (S : LocalSquare c) {s : ℤ}
    (T : TranslatedStages D s) (K' : TranslatedIC S.twoStepIC s)
    (P' : TranslatedIC S.scalarIC s) (h : ExtendsSquare D S) :
    TranslatedExtension D S T K' P' := by
  obtain ⟨j₁, j₂, h₁, h₂, _, K, P, L, u, v, _, _, _, _, huv, ⟨hcolim⟩⟩ := h
  let i := closedInclusion ({S.splitting.point} : Set surface)
  obtain ⟨hk, ⟨eK⟩⟩ := shiftedClosedExtension T K' j₂ K S.terminalCutoff
  obtain ⟨hp, ⟨eP⟩⟩ := shiftedClosedExtension T P' (i ≫ j₂) P S.pointCutoff
  obtain ⟨eL⟩ := shiftedConvolutionExtension T a S j₂ L
  let l := j₂ ≫ T.chart.hom
  have hl : IsClosedEmbedding l := (TopCat.homeoOfIso T.chart).isClosedEmbedding.comp L.closed
  let e := DerivedCategory.Plus.ι.mapIso ((pushComposition a convolutionMap l).app orderedFactor)
  let F : D.actions.FiniteSupportPerverse D.stratification := ⟨K.sheaf, K.perverse⟩
  let G : D.actions.FiniteSupportPerverse D.stratification := ⟨P.sheaf, P.perverse⟩
  let M : D.actions.FiniteSupportPerverse D.stratification := ⟨L.sheaf, L.perverse⟩
  let f : F ⟶ M := ObjectProperty.homMk u
  let g : G ⟶ M := ObjectProperty.homMk v
  let r := e ≪≫ eL.ordinary
  refine ⟨translatedStageGeometry hs T, translatedConvolutionDatum S,
    j₂, h₂, hk, hp, hl, F, G, M, eK, eP, eL, e, f, g,
    ⟨perverseCofanIsColimit f g hcolim⟩,
    transportedStageMorphism T u eK.ordinary r,
    transportedStageMorphism T v eP.ordinary r, ?_⟩
  have : T.realize.Additive := by
    change ((inverseImage T.chart.inv).mapDerivedCategory).Additive
    infer_instance
  exact mapBiprodDescIsIso T.realize u.hom v.hom eK.ordinary.symm eP.ordinary.symm r.symm

end Assembly

section CentralPoint

open EquivariantHomeomorphismDirectImageSpecs (DirectImageIntertwines)
open AnalyticAction (projection)

local notation "P" => derivedInverseImage

private def stageRestrictionIso {X : TopCat.{0}} (T : ClosedStages X) {n m : ℕ} (h : n ≤ m) :
    P (T.inclusion n) ≅ P (T.inclusion m) ⋙ P (T.transition h) :=
  eqToIso (congrArg (fun f => P f) (T.transition_inclusion h).symm) ≪≫
    derivedInverseImageComposition (T.transition h) (T.inclusion m)

private theorem stageRestrictionIso_app {X : TopCat.{0}} (T : ClosedStages X)
    {n m : ℕ} (h : n ≤ m) (K : Derived X) :
    (stageRestrictionIso T h).app K = StageJetActions.restrictionComparison K h := by
  apply Iso.ext
  simp only [stageRestrictionIso, StageJetActions.restrictionComparison, NatIso.trans_app,
    Iso.trans_hom, Iso.app_hom, eqToIso.hom, eqToHom_app]

private def stageParameterIso {V X : TopCat.{0}} (T : ClosedStages X)
    {n m : ℕ} (h : n ≤ m) (q : V ⟶ T.space n) :
    P (T.inclusion n) ⋙ P q ≅ P (T.inclusion m) ⋙ P (q ≫ T.transition h) :=
  Functor.isoWhiskerRight (stageRestrictionIso T h) (P q) ≪≫
    Functor.associator (P (T.inclusion m)) (P (T.transition h)) (P q) ≪≫
    Functor.isoWhiskerLeft (P (T.inclusion m)) (derivedInverseImageComposition q (T.transition h)).symm

private theorem stageParameterIso_hom {V X : TopCat.{0}} (T : ClosedStages X)
    {n m : ℕ} (h : n ≤ m) (q : V ⟶ T.space n) (K : Derived X) :
    (stageParameterIso T h q).hom.app K =
      (P q).map (StageJetActions.restrictionComparison K h).hom ≫
        (derivedInverseImageComposition q (T.transition h)).inv.app ((P (T.inclusion m)).obj K) := by
  simp [stageParameterIso, ← stageRestrictionIso_app T h K]

private theorem stageParameterIso_inv {V X : TopCat.{0}} (T : ClosedStages X)
    {n m : ℕ} (h : n ≤ m) (q : V ⟶ T.space n) (K : Derived X) :
    (stageParameterIso T h q).inv.app K =
      (derivedInverseImageComposition q (T.transition h)).hom.app ((P (T.inclusion m)).obj K) ≫
        (P q).map (StageJetActions.restrictionComparison K h).inv := by
  simp [stageParameterIso, ← stageRestrictionIso_app T h K]

private theorem restrictDatum_naturality {X : TopCat.{0}} {J : JetSystem.{0}} {T : ClosedStages X}
    (D : StageJetActions J T) {F G : Derived X} (f : F ⟶ G) {n m k : ℕ} (h : n ≤ m)
    (hn : (D.stageAction n).cutoff ≤ k) (hm : (D.stageAction m).cutoff ≤ k)
    (α : ((D.stageAction m).action k hm).Equivariance ((P (T.inclusion m)).obj F))
    (β : ((D.stageAction m).action k hm).Equivariance ((P (T.inclusion m)).obj G))
    (hf : (P ((D.stageAction m).action k hm).act).map ((P (T.inclusion m)).map f) ≫ β.iso.hom =
      α.iso.hom ≫ (P (projection (J.group k) (T.space m))).map ((P (T.inclusion m)).map f)) :
    (P ((D.stageAction n).action k hn).act).map ((P (T.inclusion n)).map f) ≫
        D.restrictDatum h hn hm β =
      D.restrictDatum h hn hm α ≫
        (P (projection (J.group k) (T.space n))).map ((P (T.inclusion n)).map f) := by
  let a := ((D.stageAction n).action k hn).act
  let p := projection (J.group k) (T.space n)
  let t := T.transition h
  let v := J.parameterMap (le_refl k) t
  have ha := D.compatible h hn hm
  have hp : v ≫ projection (J.group k) (T.space m) = p ≫ t := TopCat.ext (fun _ => rfl)
  have hl := (stageParameterIso T h a).hom.naturality f
  have hr := (stageParameterIso T h p).inv.naturality f
  simp only [Functor.comp_map] at hl hr
  have hc := DerivedPullbackPasting.pullbackNaturality v ha hp ((P (T.inclusion m)).map f)
    α.iso.hom β.iso.hom hf
  have hFormula {K : Derived X}
      (η : ((D.stageAction m).action k hm).Equivariance ((P (T.inclusion m)).obj K)) :
      D.restrictDatum h hn hm η =
        (stageParameterIso T h a).hom.app K ≫ pullbackMorphism v ha hp η.iso.hom ≫
          (stageParameterIso T h p).inv.app K := by
    simp only [StageJetActions.restrictDatum, stageParameterIso_hom, stageParameterIso_inv,
      Category.assoc]
    rfl
  rw [hFormula, hFormula, Category.assoc, reassoc_of% hl, reassoc_of% hc, Category.assoc, hr]


open private changeCoefficients changeDatumCoefficients
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage

/-- Transport an isomorphism of coefficient complexes through the compatible
action data and their canonical restriction comparisons. -/
private theorem stageIsoOfIso {X : TopCat.{0}} {J : JetSystem.{0}} {T : ClosedStages X}
    (D : StageJetActions J T) {F G : Derived X} (e : F ≅ G) (β : D.Equivariance G) :
    ∃ (α : D.Equivariance F) (u : (⟨F, α⟩ : D.Object) ≅ ⟨G, β⟩),
      u.hom.hom = e.hom := by
  let γ (n : ℕ) := changeCoefficients ((P (T.inclusion n)).mapIso e) (β.datum n)
  have hf (n k : ℕ) (hk : (D.stageAction n).cutoff ≤ k) :
      (P ((D.stageAction n).action k hk).act).map ((P (T.inclusion n)).map e.hom) ≫
          ((β.datum n).datum k hk).iso.hom =
        ((γ n).datum k hk).iso.hom ≫
          (P (projection (J.group k) (T.space n))).map ((P (T.inclusion n)).map e.hom) := by
    simp only [γ, changeCoefficients, changeDatumCoefficients, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.mapIso_inv, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  let α : D.Equivariance F :=
    { datum := γ
      compatibility := by
        intro n m k h hn hm
        have hComm := restrictDatum_naturality D e.hom h hn hm
          ((γ m).datum k hm) ((β.datum m).datum k hm) (hf m k hm)
        rw [β.compatibility h hn hm] at hComm
        let p := P (projection (J.group k) (T.space n))
        exact (cancel_mono (p.map ((P (T.inclusion n)).map e.hom))).mp
          (hComm.symm.trans (hf n k hn)) }
  let u : (⟨F, α⟩ : D.Object) ≅ ⟨G, β⟩ :=
    { hom := ⟨e.hom, hf⟩
      inv := ⟨e.inv, by
        intro n k hk
        let v := (P (T.inclusion n)).mapIso e
        let a := P ((D.stageAction n).action k hk).act
        let p := P (projection (J.group k) (T.space n))
        let b := ((β.datum n).datum k hk).iso.hom
        change a.map v.inv ≫ (changeDatumCoefficients v ((β.datum n).datum k hk)).iso.hom =
          b ≫ p.map v.inv
        simp only [changeDatumCoefficients, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
        change a.map v.inv ≫ a.map v.hom ≫ b ≫ p.map v.inv = b ≫ p.map v.inv
        rw [← a.map_comp_assoc, Iso.inv_hom_id, a.map_id, Category.id_comp]⟩
      hom_inv_id := StageJetActions.Hom.ext e.hom_inv_id
      inv_hom_id := StageJetActions.Hom.ext e.inv_hom_id }
  exact ⟨α, u, rfl⟩

open FiniteStageClosedExtensionSpecs (SupportIntersections)
open SchubertSupportStagesSpecs (SchubertStageSupport StageOrbitLabels NormalizedClosedImage)
open private boundedSubspace_injective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

local notation "R" => derivedDirectImage

private theorem positiveJetParameterPullback (c : ContinuousJets) {k l : ℕ} (h : k ≤ l)
    (U : TopCat.{0}) :
    Nonempty ((boundedBelowInverseImage ((jetSystem c).parameterMap h (𝟙 U))).FullyFaithful) :=
  (PositiveJetTruncationPullback.truncationPullback
    IntervalProjectionPullback.intervalProjectionFullyFaithful c k l h U).1

private theorem positiveJetDoubleParameterPullback (c : ContinuousJets) {k l : ℕ} (h : k ≤ l)
    (U : TopCat.{0}) :
    let J := jetSystem c
    Nonempty ((boundedBelowInverseImage (J.parameterMap h (J.parameterMap h (𝟙 U)))).FullyFaithful) :=
  (PositiveJetTruncationPullback.truncationPullback
    IntervalProjectionPullback.intervalProjectionFullyFaithful c k l h U).2

open private localEquivariance from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SupportIntersectionJetDescent

/-- The restricted support datum descends to each of the stage's allowed jets. -/
private def supportLocalEquivariance {c : ContinuousJets} {X Y : TopCat.{0}}
    {T : ClosedStages X} {D : StageJetActions (jetSystem c) T}
    {i : Y ⟶ X} {B : JetAction (jetSystem c) Y}
    (I : SupportIntersections D i B) (G : BoundedBelow Y) (β : B.Equivariance G.obj) :
    I.LocalEquivariance G β :=
  @localEquivariance X Y (jetSystem c) T D i B I
    (@positiveJetParameterPullback c) (@positiveJetDoubleParameterPullback c) G β

private def stageEquivariantIso {J : JetSystem.{0}} {Z : TopCat.{0}} {T : ClosedStages Z}
    {D : StageJetActions J T} {C K : D.Object} (u : C.obj ≅ K.obj)
    (h : ∀ n k (hk : (D.stageAction n).cutoff ≤ k),
      (P ((D.stageAction n).action k hk).act).map ((P (T.inclusion n)).map u.inv) ≫
          ((C.equivariance.datum n).datum k hk).iso.hom =
        ((K.equivariance.datum n).datum k hk).iso.hom ≫ (P (projection (J.group k) (T.space n))).map
          ((P (T.inclusion n)).map u.inv)) : C ≅ K where
  hom := ⟨u.hom, by
    intro n k hk
    let v := (P (T.inclusion n)).mapIso u
    let a := (P ((D.stageAction n).action k hk).act).mapIso v
    let p := (P (projection (J.group k) (T.space n))).mapIso v
    let g := ((C.equivariance.datum n).datum k hk).iso.hom
    let d := ((K.equivariance.datum n).datum k hk).iso.hom
    have hc : a.inv ≫ g = d ≫ p.inv := h n k hk
    change a.hom ≫ d = g ≫ p.hom
    rw [← cancel_mono p.inv, Category.assoc, ← hc, Iso.hom_inv_id_assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]⟩
  inv := ⟨u.inv, h⟩
  hom_inv_id := StageJetActions.Hom.ext u.hom_inv_id
  inv_hom_id := StageJetActions.Hom.ext u.inv_hom_id

open private local_naturality from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SupportIntersectionJetDescent

/-- Equip the direct image on the Schubert support with the normalized datum
computed by the action and projection mates of the ordered map. -/
private theorem terminalDirectImageDatum {J : JetSystem.{0}} {X Y : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {f : X ⟶ Y} (h : JetMapsCommute A B f)
    (adj : DerivedAdjunctions) {F : BoundedBelow X} {G : BoundedBelow Y}
    (α : A.Equivariance F.obj) (β : B.Equivariance G.obj) (e : (R f).obj F ≅ G)
    (he : DirectImageIntertwines adj A B h F α G β e) :
    let H := (R f).obj F
    ∃ θ : B.Equivariance H.obj,
      DirectImageIntertwines adj A B h F α H θ (Iso.refl H) ∧
      ∀ k (hk : B.cutoff ≤ k),
        (P (B.action k hk).act).map e.hom.hom ≫ (β.datum k hk).iso.hom =
          (θ.datum k hk).iso.hom ≫ (P (projection (J.group k) Y)).map e.hom.hom := by
  intro H
  let i := (DerivedCategory.Plus.ι (C := Sheaves Y)).mapIso e
  let θ := changeCoefficients i β
  refine ⟨θ, ?_, ?_⟩
  · intro k hx hy
    obtain ⟨ha, hp, hEq⟩ := he k hx hy
    refine ⟨ha, hp, ?_⟩
    let a := P (B.action k hy).act
    let p := P (projection (J.group k) Y)
    change a.map (𝟙 H.obj) ≫ (θ.datum k hy).iso.hom ≫ p.map (𝟙 H.obj) ≫ _ = _
    erw [a.map_id H.obj, p.map_id H.obj, Category.id_comp, Category.id_comp]
    simpa only [θ, changeCoefficients, changeDatumCoefficients, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.mapIso_inv, Category.assoc] using! hEq
  · intro k hk
    change (P (B.action k hk).act).map i.hom ≫ (β.datum k hk).iso.hom =
      (θ.datum k hk).iso.hom ≫ (P (projection (J.group k) Y)).map i.hom
    simp only [θ, changeCoefficients, changeDatumCoefficients, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

set_option maxHeartbeats 650000 in
private theorem centralStageTransportOfLocal {c : ContinuousJets} (D : GrassmannianStages c)
    {X Y : TopCat.{0}} {A : JetAction (jetSystem c) X} {B : JetAction (jetSystem c) Y}
    (adj : DerivedAdjunctions) {f : X ⟶ Y} (h : JetMapsCommute A B f)
    (hCut : A.cutoff ≤ B.cutoff) {i : Y ⟶ Gr} (hi : IsClosedEmbedding i)
    {F : BoundedBelow X} {G : BoundedBelow Y} (α : A.Equivariance F.obj) (β : B.Equivariance G.obj)
    (e : (R f).obj F ≅ G) (he : DirectImageIntertwines adj A B h F α G β e)
    (I : SupportIntersections D.actions i B)
    (hK : IsFiniteStagePerverse D.stages D.stratification ((R i).obj G).obj) :
    CentralStageTransport D A B adj i h α β e := by
  obtain ⟨θ, hθ, hLocal⟩ := terminalDirectImageDatum h adj α β e he
  let H := (R f).obj F
  let L' := supportLocalEquivariance I H θ
  let M := supportLocalEquivariance I G β
  obtain ⟨γ', hγ', _⟩ := FiniteStageClosedExtensions.closedExtensionAtStages hi I adj H θ L'
  obtain ⟨δ, hδ, _⟩ := FiniteStageClosedExtensions.closedExtensionAtStages hi I adj G β M
  have hLoc : ∀ n k (hk : (I.action n).cutoff ≤ k),
      let q := ((boundedBelowInverseImage (I.intoSupport n)).map e.hom).hom
      (P ((I.action n).action k hk).act).map q ≫ ((M.datum n).datum k hk).iso.hom =
        ((L'.datum n).datum k hk).iso.hom ≫
          (P (projection ((jetSystem c).group k) (I.space n))).map q := by
    intro n k hk
    exact local_naturality I (@positiveJetParameterPullback c) e.hom hLocal n k hk
  obtain ⟨g, hg⟩ := (FiniteStageClosedExtensions.closedExtensionNaturality I adj e.hom).2
    L' M hγ' hδ hLoc
  let ι := DerivedCategory.Plus.ι (C := Sheaves Gr)
  let p := ι.mapIso ((centralDirectImageComposition adj f i).app F)
  let d := ι.mapIso ((R i).mapIso e)
  obtain ⟨γ, v, hv⟩ := stageIsoOfIso D.actions p γ'
  let w : (⟨((R i).obj G).obj, δ⟩ : D.actions.Object) ≅ ⟨((R i).obj H).obj, γ'⟩ :=
    stageEquivariantIso d.symm (by
      intro n k hk
      have hc := g.comm n k hk
      rw [hg] at hc
      exact hc)
  let u := v ≪≫ w.symm
  have hC : IsFiniteStagePerverse D.stages D.stratification ((R (f ≫ i)).obj F).obj := by
    obtain ⟨n, Q, ⟨q⟩⟩ := hK
    exact ⟨n, Q, ⟨q ≪≫ (p ≪≫ d).symm⟩⟩
  refine ⟨hCut, θ, I, L', M, γ', γ, δ, hC, hK, hθ, hγ', hδ, ⟨v, hv⟩, ⟨w.symm, rfl⟩,
    ObjectProperty.isoMk _ u, ?_⟩
  change v.hom.hom ≫ d.hom = _
  rw [hv]
  exact (ι.map_comp _ _).symm

private theorem centralTerminalLattices {c : ContinuousJets} {a : ℤ} {ab : DominantPair}
    {N M C : ℕ} {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    {hC : OrbitBound (centralPair a) C}
    {A : SchubertJetAction c ab N hN} {B : SchubertJetAction c (shiftPair a ab) M hM}
    {T : SchubertTranslationData a ab N M hN hM} {W : OrderedCharts a ab}
    {point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)}
    (S : RealizesOrderedSchemes A T W point) {D : GrassmannianStages c}
    (H : SchubertStageSupport D B) (p : SchubertSpace ab N hN) :
    H.inclusion (T.analyticIso.hom p) = leftTerminal a ab (S.left p) ∧
      H.inclusion (T.analyticIso.hom p) = rightTerminal a ab (S.right p) := by
  let q := T.analyticIso.hom p
  let L := (S.E p).val.val
  have hq : H.inclusion q ∈ closureLattices (shiftPair a ab) :=
    H.range_eq ▸ Set.mem_range_self q
  have hτ : translate a L ∈ closureLattices (shiftPair a ab) :=
    (translate_mem_closure CentralLatticeTranslation.scalarTranslation a ab L).mpr (S.E p).property
  obtain ⟨U, hU⟩ := RankTwoSchubertStrata.closureLattices_bounded hM hq
  obtain ⟨V, hV⟩ := RankTwoSchubertStrata.closureLattices_bounded hM hτ
  have hSub : boundedSubspace U = boundedSubspace V := by
    change latticeSubspace (-(M : ℤ)) (2 * M) U.val = latticeSubspace (-(M : ℤ)) (2 * M) V.val
    rw [hU, hV]
    exact (H.coordinates q).symm.trans (T.onLattices p (S.E p).val (S.onSubspaces p))
  have hUV := boundedSubspace_injective M hSub
  have hTranslate : H.inclusion q = translate a L :=
    hU.symm.trans ((congrArg Subtype.val hUV).trans hV)
  constructor
  · rw [W.leftMap, (S.onRepresentatives p).1]
    exact hTranslate
  · rw [W.rightMap, (S.onRepresentatives p).2.1]
    exact hTranslate

private theorem schubertStageTransport {c : ContinuousJets} {D : GrassmannianStages c}
    {labels : StageOrbitLabels D}
    {ab : DominantPair} {M : ℕ} {hM : OrbitBound ab M} {B : SchubertJetAction c ab M hM}
    (H : SchubertStageSupport D B) (hH : NormalizedClosedImage labels H)
    {Q : Stratification (SchubertSpace ab M hM)}
    {G : DimensionFiltration (SchubertSpace ab M hM) (orbitDimension ab (difference ab / 2))}
    (hG : IsNormalizedOrbitIC ab M hM (𝟙 _) (difference ab / 2) Q G)
    (β : B.action.Equivariance (complex G).obj) (adj : DerivedAdjunctions.{0})
    {X : TopCat.{0}} {f : X ⟶ SchubertSpace ab M hM} {A : JetAction (jetSystem c) X}
    (h : JetMapsCommute A B.action f) (hCut : A.cutoff ≤ B.action.cutoff)
    {F : BoundedBelow X} (α : A.Equivariance F.obj) (e : (R f).obj F ≅ complex G)
    (he : DirectImageIntertwines adj A B.action h F α (complex G) β e) :
    CentralStageTransport D A B.action adj H.inclusion h α β e := by
  have hK : IsFiniteStagePerverse D.stages D.stratification
      ((derivedDirectImage H.inclusion).obj (complex G)).obj := by
    obtain ⟨_, _, _, _, hK⟩ := hH.2 Q G hG
    exact hK
  exact centralStageTransportOfLocal D adj h hCut H.closed α β e he H.intersections hK

private theorem centralPointAllStages : CentralPointAllStages := by
  intro c
  obtain ⟨D, _, stageSupport⟩ := SchubertSupportStages.schubertSupportStages c
  refine ⟨D, ?_⟩
  intro a ab N M C hN hM hC A B T W point S adj P' Q F G _ hG α β _ _ h e he
  obtain ⟨H, hH⟩ := stageSupport (shiftPair a ab) M hM B
  have hCut : A.action.cutoff = B.action.cutoff := by
    rw [A.actual.1, B.actual.1]
    have hd : ab.val.1 - ab.val.2 = (ab.val.1 + a) - (ab.val.2 + a) := by omega
    exact congrArg (fun z : ℤ ↦ z.toNat - 1) hd
  exact ⟨H.inclusion, H.closed, H.range_eq, H.coordinates, centralTerminalLattices S H,
    schubertStageTransport H hH hG β adj h hCut.le α e he⟩

end CentralPoint

/-- Convolution with the scalar point is the translated IC in either order. -/
theorem centralPointRule : CentralMinusculeRuleSpecs.Expected.CentralPointRule :=
  ⟨CentralLatticeTranslation.centralConvolution, centralPointAllStages⟩

/-- Transport the ordered minuscule square along the two independent scalar shifts. -/
theorem translatedMinusculeRule_conditional
    (square : MinusculeConvolutionSquareSpecs.Expected.MinusculeConvolutionSquare) :
    CentralMinusculeRuleSpecs.Expected.TranslatedMinusculeRule := by
  let central := CentralLatticeTranslation.centralConvolution
  let scalar := CentralLatticeTranslation.scalarTranslation
  let schubert := CentralLatticeTranslation.schubertTranslation
  let windows := CentralLatticeTranslation.windowTranslation
  intro a b
  obtain ⟨c, D, S, descent, extension⟩ := square
  obtain ⟨A⟩ := translatedIC_exists schubert central S.minusculeIC a
  obtain ⟨B⟩ := translatedIC_exists schubert central S.minusculeIC b
  obtain ⟨K⟩ := translatedIC_exists schubert central S.twoStepIC (a + b)
  obtain ⟨P⟩ := translatedIC_exists schubert central S.scalarIC (a + b)
  obtain ⟨F⟩ := translatedFlags_exists scalar S a b descent
  let T := translatedStages scalar D (a + b)
  exact ⟨c, D, S, A, B, K, P, F, T, translatedFactorMaps S A B F, translatedTensorDescent scalar S A B F,
    translatedTerminalScheme windows S K F,
    translatedExtension scalar S.twoStepIC.adjunctions D S T K P extension⟩

end RepTheorySurvey.Geometric.CentralMinusculeRule

theorem _root_.«RepTheorySurvey».«Geometric».«CentralMinusculeRule».«translatedMinusculeRule» : _root_.«RepTheorySurvey».«Geometric».«CentralMinusculeRuleSpecs».«Expected».«TranslatedMinusculeRule» :=
  @_root_.«RepTheorySurvey».«Geometric».«CentralMinusculeRule».«translatedMinusculeRule_conditional» (@_root_.«RepTheorySurvey».«Geometric».«MinusculeConvolutionSquare».«minusculeConvolutionSquare»)
