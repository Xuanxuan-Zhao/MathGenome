import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeConvolutionSquare
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeFrameDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepICNormalization
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeLocalSquare
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeSupportIntersections
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SupportIntersectionEquivariance
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.PointMatesOnSupportIntersections
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.FiniteStageClosedExtensions
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option maxHeartbeats 1500000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.MinusculeConvolutionSquare

open Analytic
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs
open ConvolutionUnitConeSpecs MinusculeConvolutionSquareSpecs
open ConvolutionBundleSpecs (firstPlane secondPlane)
open ConvolutionEquivariantSplittingSpecs (SplittingData)

open private colength_inclusion_closed
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem minusculeLatticeModel :
    ∃ j : minuscule ⟶ Gr,
      IsClosedEmbedding j ∧ Set.range j = colength 1 ∧
        ∀ p, firstPlane p = (latticeSubspace 0 1 (j p)).map constantCoordinates.toLinearMap := by
  obtain ⟨e, he, _⟩ := MinusculeAndTwoStep.minusculeProjective.1
  let j : minuscule ⟶ Gr :=
    TopCat.ofHom ⟨fun p ↦ (e.symm p).val, continuous_subtype_val.comp e.symm.continuous⟩
  refine ⟨j, (colength_inclusion_closed (m := 1) (Or.inl rfl)).comp
    e.symm.isClosedEmbedding, ?_, ?_⟩
  · ext L
    constructor
    · rintro ⟨p, rfl⟩
      exact (e.symm p).property
    · intro hL
      exact ⟨e ⟨L, hL⟩, congrArg Subtype.val (e.symm_apply_apply ⟨L, hL⟩)⟩
  · intro p
    exact (congrArg (grassmannianSubspace projectiveBasis projectiveRank)
      (e.apply_symm_apply p)).symm.trans (he (e.symm p))

section Coproduct

open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions)

private def underlyingCofanIsColimit {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z : C} [HasBinaryBiproduct X Y] (u : X ⟶ Z) (v : Y ⟶ Z)
    [h : IsIso (biprod.desc u v)] : IsColimit (BinaryCofan.mk u v) := by
  let e : (X ⊞ Y) ≅ Z := @asIso _ _ _ _ _ h
  exact (BinaryBiproduct.isColimit X Y).ofIsoColimit
    (Cocone.ext e (by rintro ⟨i⟩; cases i <;> simp [e]))

/-- A coproduct of equivariant maps is detected on the ordinary derived
objects. The universal map commutes with equivariance because the inverse
images preserve the ordinary coproduct. -/
private theorem equivariantCofanIsColimit
    {X : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {K P L : B.Object} (u : K ⟶ L) (v : P ⟶ L)
    [IsIso (biprod.desc u.hom v.hom)] : Nonempty (IsColimit (BinaryCofan.mk u v)) := by
  let c := underlyingCofanIsColimit u.hom v.hom
  have left (T : B.Object) (f : K ⟶ T) (g : P ⟶ T) :
      u.hom ≫ c.desc (BinaryCofan.mk f.hom g.hom) = f.hom :=
    c.fac _ ⟨WalkingPair.left⟩
  have right (T : B.Object) (f : K ⟶ T) (g : P ⟶ T) :
      v.hom ≫ c.desc (BinaryCofan.mk f.hom g.hom) = g.hom :=
    c.fac _ ⟨WalkingPair.right⟩
  refine ⟨BinaryCofan.IsColimit.mk _ (fun {T} f g ↦ ⟨c.desc (BinaryCofan.mk f.hom g.hom), ?_⟩)
    (fun f g ↦ StageJetActions.Hom.ext (left _ f g))
    (fun f g ↦ StageJetActions.Hom.ext (right _ f g)) ?_⟩
  · intro n k hk
    let r := derivedInverseImage (A.inclusion n)
    let p := derivedInverseImage (AnalyticAction.projection (J.group k) (A.space n))
    let a := derivedInverseImage ((B.stageAction n).action k hk).act
    let w := c.desc (BinaryCofan.mk f.hom g.hom)
    change a.map (r.map w) ≫ ((T.equivariance.datum n).datum k hk).iso.hom =
      ((L.equivariance.datum n).datum k hk).iso.hom ≫ p.map (r.map w)
    let : PreservesFiniteCoproducts r := by dsimp [r, derivedInverseImage]; infer_instance
    let : PreservesFiniteCoproducts a := by dsimp [a, derivedInverseImage]; infer_instance
    let c' := mapIsColimitOfPreservesOfIsColimit (r ⋙ a) _ _ c
    apply BinaryCofan.IsColimit.hom_ext c'
    · change a.map (r.map u.hom) ≫ a.map (r.map w) ≫ _ =
          a.map (r.map u.hom) ≫ _ ≫ p.map (r.map w)
      rw [← Category.assoc, ← a.map_comp, ← r.map_comp, left _ f g,
        f.comm n k hk, ← Category.assoc, u.comm n k hk, Category.assoc,
        ← p.map_comp, ← r.map_comp, left _ f g]
    · change a.map (r.map v.hom) ≫ a.map (r.map w) ≫ _ =
          a.map (r.map v.hom) ≫ _ ≫ p.map (r.map w)
      rw [← Category.assoc, ← a.map_comp, ← r.map_comp, right _ f g,
        g.comm n k hk, ← Category.assoc, v.comm n k hk, Category.assoc,
        ← p.map_comp, ← r.map_comp, right _ f g]
  · intro T f g m hf hg
    apply StageJetActions.Hom.ext
    apply BinaryCofan.IsColimit.hom_ext c
    · exact (congrArg StageJetActions.Hom.hom hf).trans (left _ f g).symm
    · exact (congrArg StageJetActions.Hom.hom hg).trans (right _ f g).symm

private theorem additivePreservesBinaryBiproduct {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] (X Y : C) :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb := ⟨isBinaryBilimitOfTotal _ (by
    simp only [Functor.mapBinaryBicone_fst, Functor.mapBinaryBicone_inl,
      Functor.mapBinaryBicone_snd, Functor.mapBinaryBicone_inr,
      ← F.map_comp, ← F.map_add, IsBilimit.binary_total hb, F.map_id]
    rfl)⟩

private theorem mapBiprodDescIsIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [h : IsIso (biprod.desc f g)] {X' Y' Z' : D}
    (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') (e₃ : F.obj Z ≅ Z') :
    IsIso (biprod.desc (e₁.inv ≫ F.map f ≫ e₃.hom) (e₂.inv ≫ F.map g ≫ e₃.hom)) := by
  let : PreservesBinaryBiproduct X Y F := additivePreservesBinaryBiproduct F X Y
  let e := biprod.mapIso e₁.symm e₂.symm ≪≫ (F.mapBiprod X Y).symm ≪≫
    F.mapIso (@asIso _ _ _ _ _ h) ≪≫ e₃
  suffices biprod.desc (e₁.inv ≫ F.map f ≫ e₃.hom) (e₂.inv ≫ F.map g ≫ e₃.hom) = e.hom by
    rw [this]
    infer_instance
  rw [show e.hom = (biprod.mapIso e₁.symm e₂.symm).hom ≫
      (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) ≫ e₃.hom by simp [e]]
  rw [← Category.assoc (F.mapBiprod X Y).inv, biprod.mapBiprod_inv_map_desc]
  apply biprod.hom_ext' <;> simp

private theorem isIsoLocalSummandMaps {c : EquivariantIntersectionComplexesSpecs.ContinuousJets}
    (S : LocalSquare c) :
    IsIso (biprod.desc (S.constantIdentification.inv ≫ unit) S.splitting.sectionMap) := by
  let e := biprod.mapIso S.constantIdentification.symm
    (Iso.refl (pointSkyscraper S.splitting.point S.splitting.closed)) ≪≫ S.splitting.splitIso
  suffices biprod.desc (S.constantIdentification.inv ≫ unit) S.splitting.sectionMap = e.hom by
    rw [this]
    infer_instance
  apply biprod.hom_ext'
  · simp [e, S.splitting.split_constant]
  · simp [e, S.splitting.split_point]

/-- Direct image carries the two local summand maps to a biproduct whenever
the extensions realize the specified ordinary direct images. -/
private theorem ordinaryImageSplit {c : EquivariantIntersectionComplexesSpecs.ContinuousJets}
    (D : GrassmannianStages c) (S : LocalSquare c)
    (j₂ : surface ⟶ Gr)
    (K : GrassmannianExtension D S.terminalAction (IntersectionComplex.surface S.splitting.point S.splitting.closed)
      S.intersectionDatum j₂)
    (P : GrassmannianExtension D S.pointAction (IntersectionComplex.point S.splitting.point) S.pointDatum
      (closedInclusion {S.splitting.point} ≫ j₂))
    (L : GrassmannianExtension D S.terminalAction convolution S.convolutionDatum j₂)
    (u : K.sheaf ⟶ L.sheaf) (v : P.sheaf ⟶ L.sheaf)
    (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion {S.splitting.point}) ⊣
      LocalSheaf.closedExtensionPlus S.splitting.closed)
    (hu : u.hom = K.ordinary.inv ≫
      ((derivedDirectImage j₂).map (ObjectProperty.homMk (S.constantIdentification.inv ≫ unit))).hom ≫
      L.ordinary.hom)
    (hv : v.hom = P.ordinary.inv ≫ ((closedPointComposition S.splitting j₂ a b).hom.app
      (IntersectionComplex.point S.splitting.point)).hom ≫
      ((derivedDirectImage j₂).map (ObjectProperty.homMk S.splitting.sectionMap)).hom ≫
      L.ordinary.hom) :
    IsIso (biprod.desc u.hom v.hom) := by
  let F := IntersectionComplex.surface S.splitting.point S.splitting.closed
  let Q := (LocalSheaf.closedExtensionPlus S.splitting.closed).obj
    (IntersectionComplex.point S.splitting.point)
  let f : F ⟶ convolution := ObjectProperty.homMk (S.constantIdentification.inv ≫ unit)
  let g : Q ⟶ convolution := ObjectProperty.homMk S.splitting.sectionMap
  let i : BoundedBelow surface ⥤ Derived surface := DerivedCategory.Plus.ι
  have hs : IsIso (biprod.desc (i.map f) (i.map g)) := isIsoLocalSummandMaps S
  let : PreservesBinaryBiproduct F Q i := additivePreservesBinaryBiproduct i F Q
  have : IsIso (i.map (biprod.desc f g)) := by
    rw [← biprod.mapBiprod_hom_desc i]
    infer_instance
  have : IsIso (biprod.desc f g) := isIso_of_reflects_iso _ i
  let G := derivedDirectImage j₂
  let : G.Additive := by dsimp [G, derivedDirectImage]; infer_instance
  let H : BoundedBelow surface ⥤ Derived Gr := G ⋙ DerivedCategory.Plus.ι
  let p : H.obj Q ≅ P.sheaf.obj :=
    DerivedCategory.Plus.ι.mapIso ((closedPointComposition S.splitting j₂ a b).app _).symm ≪≫
      P.ordinary
  have hi := mapBiprodDescIsIso H f g K.ordinary p L.ordinary
  rw [hu, hv]
  simp only [p, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Category.assoc,
    H, Functor.comp_map] at hi
  exact hi

end Coproduct

section Stages

open TopologicalSpace
open RankTwoSchubertStrataSpecs EquivariantIntersectionComplexesSpecs

open private boundedVal_closedEmbedding from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShortWindowTopology
open private orbit_iff_not_inner orbit_mem_of_small from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

private def latticeStages : ClosedStages Gr where
  stage := boundedSet
  closed N := by
    convert (boundedVal_closedEmbedding N).isClosed_range using 1
    ext L
    exact ⟨fun h ↦ ⟨⟨L, h⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.property⟩
  monotone _ _ h _ hL := (boundedInclusion h ⟨_, hL⟩).property
  exhaustive L := by
    obtain ⟨N, B, rfl⟩ := BoundedLattices.latticeExhaustion.1 2 L
    exact ⟨N, B.property⟩

private def boundedHomeomorph (N : ℕ) : BoundedLattice 2 N ≃ₜ latticeStages.space N :=
  ((boundedVal_closedEmbedding N).isEmbedding.codRestrict (s := boundedSet N)
    (fun x ↦ x.property)).toHomeomorphOfSurjective (fun x ↦ ⟨⟨x.val, x.property⟩, rfl⟩)

private theorem boundedHomeomorph_symm_val (N : ℕ) (x : latticeStages.space N) :
    ((boundedHomeomorph N).symm x).val = x.val :=
  congrArg Subtype.val ((boundedHomeomorph N).apply_symm_apply x)

private theorem truncate_reduce {k l : ℕ} (h : k ≤ l) (g : GL (Fin 2) O) :
    jetTruncation h (reduceGL 2 (l + 1) (Nat.succ_pos l) g) =
      reduceGL 2 (k + 1) (Nat.succ_pos k) g := by
  apply Units.ext
  ext i j
  rfl

private theorem boundedActionExists (c : ContinuousJets) (N k : ℕ) (hk : 2 * N - 1 ≤ k) :
    ∃ A : AnalyticAction ((jetSystem c).group k) (TopCat.of (BoundedLattice 2 N)),
      ∀ (g : GL (Fin 2) O) (L : BoundedLattice 2 N),
        (A.act (reduceGL 2 (k+1) (Nat.succ_pos k) g, L)).val = positiveGLMap 2 g • L.val := by
  let hModel := (BoundedLattices.boundedStageComparison 2 N).1
  let e : BoundedLattice 2 N ≃ₜ BoundedStage 2 N :=
    (show IsEmbedding (boundedPoint (r := 2) (N := N)) from
      ⟨⟨rfl⟩, hModel.injective⟩).toHomeomorphOfSurjective hModel.surjective
  have hn : 2 * N ≤ k + 1 := by omega
  obtain ⟨ρ, _, hρ, hc⟩ :=
    BoundedLattices.glJetAction 2 (-(N : ℤ)) (2 * N) (k + 1) (Nat.succ_pos k) hn
  refine ⟨{ act := TopCat.ofHom ⟨fun p ↦ e.symm (ρ.smul p.1 (e p.2)),
              e.symm.continuous.comp (hc.comp
                (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩
            one_act := fun x ↦
              (congrArg e.symm (ρ.one_smul (e x))).trans (e.symm_apply_apply x)
            mul_act := fun g h x ↦
              (congrArg e.symm (ρ.mul_smul g h (e x))).trans
                (congrArg (fun y ↦ e.symm (ρ.smul g y))
                  (e.apply_symm_apply (ρ.smul h (e x))).symm) }, ?_⟩
  intro g L
  have hL : (positiveGLMap 2 g • L.val) ∈ boundedSet N := by
    have eq : -(N : ℤ) + ((2 * N : ℕ) : ℤ) = N := by omega
    have hh := BoundedLattices.windowPositiveStable 2 (-(N : ℤ)) (2 * N) g
      ⟨L.val, by rw [eq]; exact L.property⟩
    change (scalarLattice 2 (-(N : ℤ) + ((2 * N : ℕ) : ℤ))).val ≤
      (positiveGLMap 2 g • L.val).val ∧
      (positiveGLMap 2 g • L.val).val ≤ (scalarLattice 2 (-(N : ℤ))).val at hh
    rw [eq] at hh
    exact hh
  let M : BoundedLattice 2 N := ⟨_, hL⟩
  change (e.symm (ρ.smul (reduceGL 2 (k+1) (Nat.succ_pos k) g) (e L))).val = M.val
  have h : ρ.smul (reduceGL 2 (k+1) (Nat.succ_pos k) g) (e L) = e M := hρ g L.val
  rw [h, e.symm_apply_apply]

private theorem stageActionExists (c : ContinuousJets) (N k : ℕ) (hk : 2 * N - 1 ≤ k) :
    ∃ A : AnalyticAction ((jetSystem c).group k) (latticeStages.space N),
      ∀ (g : GL (Fin 2) O) (L : latticeStages.space N),
        (A.act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, L)).val = positiveGLMap 2 g • L.val := by
  obtain ⟨B, hB⟩ := boundedActionExists c N k hk
  let e := boundedHomeomorph N
  let A : AnalyticAction ((jetSystem c).group k) (latticeStages.space N) :=
    { act := TopCat.ofHom ⟨fun p ↦ e (B.act (p.1, e.symm p.2)),
        e.continuous.comp (B.act.hom.continuous.comp
          (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))⟩
      one_act := fun x ↦ by
        change e (B.act (1, e.symm x)) = x
        rw [B.one_act, e.apply_symm_apply]
      mul_act := fun g h x ↦ by
        change e (B.act (g * h, e.symm x)) =
          e (B.act (g, e.symm (e (B.act (h, e.symm x)))))
        rw [B.mul_act, e.symm_apply_apply] }
  refine ⟨A, fun g L ↦ ?_⟩
  change (B.act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, e.symm L)).val = _
  rw [hB, boundedHomeomorph_symm_val]

private def latticeJetAction {c : ContinuousJets} (N : ℕ)
    (ρ : ∀ k, 2 * N - 1 ≤ k → AnalyticAction ((jetSystem c).group k) (latticeStages.space N))
    (hρ : ∀ k (hk : 2 * N - 1 ≤ k) (g : GL (Fin 2) O) (x : latticeStages.space N),
      ((ρ k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, x)).val = positiveGLMap 2 g • x.val) :
    JetAction (jetSystem c) (latticeStages.space N) where
  cutoff := 2 * N - 1
  action := ρ
  factors := by
    intro k l hk hkl
    apply TopCat.ext
    rintro ⟨p, x⟩
    obtain ⟨g, rfl⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 _ (Nat.succ_pos l) p
    apply Subtype.ext
    change ((ρ k hk).act (jetTruncation hkl (reduceGL 2 (l + 1) (Nat.succ_pos l) g), x)).val =
      ((ρ l (hk.trans hkl)).act (reduceGL 2 (l + 1) (Nat.succ_pos l) g, x)).val
    exact (congrArg (fun q => ((ρ k hk).act (q, x)).val) (truncate_reduce hkl g)).trans
      ((hρ k hk g x).trans (hρ l (hk.trans hkl) g x).symm)

private theorem stageActionTransition {X : TopCat.{0}} {J : JetSystem.{0}}
    {D : ClosedStages X} {n m k : ℕ} (h : n ≤ m)
    (B : AnalyticAction (J.group k) (D.space n)) (C : AnalyticAction (J.group k) (D.space m))
    (commutes : ∀ (g : (J.group k).space) (x : D.space n),
      (C.act (g, D.transition h x)).val = (B.act (g, x)).val) :
    J.parameterMap (le_refl k) (D.transition h) ≫ C.act = B.act ≫ D.transition h := by
  apply TopCat.ext
  rintro ⟨g, x⟩
  apply Subtype.ext
  change (C.act (J.truncate k k (le_refl k) g, D.transition h x)).val = (B.act (g, x)).val
  have ht : J.truncate k k (le_refl k) g = g :=
    congrArg (fun f : (J.group k).space ⟶ (J.group k).space => f g) (J.truncate_id k)
  rw [ht]
  exact commutes g x

private theorem stageActionTransitionOfLifts {X : TopCat.{0}} {J : JetSystem.{0}}
    {D : ClosedStages X} {n m k : ℕ} (h : n ≤ m)
    (B : AnalyticAction (J.group k) (D.space n)) (C : AnalyticAction (J.group k) (D.space m))
    {G : Type} (lift : G → (J.group k).space) (hlift : Function.Surjective lift)
    (act : G → X → X)
    (hB : ∀ g (x : D.space n), (B.act (lift g, x)).val = act g x.val)
    (hC : ∀ g (x : D.space m), (C.act (lift g, x)).val = act g x.val) :
    J.parameterMap (le_refl k) (D.transition h) ≫ C.act = B.act ≫ D.transition h := by
  apply stageActionTransition h
  intro q x
  obtain ⟨g, rfl⟩ := hlift q
  exact (hC g (D.transition h x)).trans (hB g x).symm

private theorem latticeStageActions (c : ContinuousJets) :
    ∃ (B : StageJetActions (jetSystem c) latticeStages),
      (∀ N, (B.stageAction N).cutoff = 2 * N - 1) ∧
      ∀ N k (hk : (B.stageAction N).cutoff ≤ k) (g : GL (Fin 2) O)
        (L : latticeStages.space N),
        (((B.stageAction N).action k hk).act
          (reduceGL 2 (k + 1) (Nat.succ_pos k) g, L)).val = positiveGLMap 2 g • L.val := by
  classical
  choose ρ hρ using stageActionExists c
  let A := fun n => latticeJetAction n (ρ n) (hρ n)
  refine ⟨⟨A, ?_⟩, fun _ => rfl, hρ⟩
  intro n m k h hn hm
  exact stageActionTransitionOfLifts h ((A n).action k hn) ((A m).action k hm)
    (reduceGL 2 (k + 1) (Nat.succ_pos k))
    (RankTwoSchubertStrata.reduceGL_surjective 2 (k + 1) (Nat.succ_pos k))
    (fun g (L : Gr) => positiveGLMap 2 g • L) (hρ n k hn) (hρ m k hm)

private theorem boundedOrbitLocallyClosed (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    IsLocallyClosed (boundedOrbit ab N) := by
  have hc : IsClosed (schubertLatticeSet ab N) := by
    rw [← (RankTwoSchubertStrata.boundedSchubertComparison ab N hN).2.2.2.2.2.1]
    exact isClosed_closure
  have subset : boundedOrbit ab N ⊆ schubertLatticeSet ab N := by
    rw [← (RankTwoSchubertStrata.boundedSchubertComparison ab N hN).2.2.2.2.2.1]
    exact subset_closure
  by_cases h : 2 ≤ difference ab
  · let cd := adjacentPair ab h
    have hcd : Below cd ab := by
      apply (RankTwoSchubertStrata.below_iff _ _).mpr
      change (ab.val.1 - 1) + (ab.val.2 + 1) = ab.val.1 + ab.val.2 ∧
        ab.val.1 - 1 ≤ ab.val.1 ∧ ab.val.2 ≤ ab.val.2 + 1
      omega
    have hN' := RankTwoSchubertStrata.orbitBound_of_below hcd hN
    have hclosed : IsClosed (schubertLatticeSet cd N) := by
      rw [← (RankTwoSchubertStrata.boundedSchubertComparison cd N hN').2.2.2.2.2.1]
      exact isClosed_closure
    refine ⟨(schubertLatticeSet cd N)ᶜ, schubertLatticeSet ab N, hclosed.isOpen_compl, hc, ?_⟩
    ext L
    exact ⟨fun hL ↦ ⟨(orbit_iff_not_inner h (subset hL)).mp hL, subset hL⟩,
      fun ⟨hi, hL⟩ ↦ (orbit_iff_not_inner h hL).mpr hi⟩
  · have he : boundedOrbit ab N = schubertLatticeSet ab N :=
      Set.Subset.antisymm subset fun _ hL ↦ orbit_mem_of_small h hL
    exact ⟨Set.univ, _, isOpen_univ, hc, by rw [he, Set.univ_inter]⟩

private theorem orbitInclusionRange {X : TopCat.{0}} (U : Opens X) (Z : Set X)
    (hZ : IsClosed Z) (d : ℕ) :
    let S : Stratum X := ⟨U, Subtype.val ⁻¹' Z, hZ.preimage continuous_subtype_val, d⟩
    Set.range S.inclusion = (U : Set X) ∩ Z := by
  ext x
  constructor
  · rintro ⟨⟨⟨x, hx⟩, hz⟩, rfl⟩
    exact ⟨hx, hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨⟨⟨x, hx⟩, hz⟩, rfl⟩

private theorem latticeStageStratification (N : ℕ) :
    ∃ (P : Stratification (latticeStages.space N)) (label : P.Index → DominantPair),
      (∀ s, OrbitBound (label s) N) ∧
      (∀ s, Set.range (P.stratum s).inclusion = {L | L.val ∈ gl2Orbit (label s)}) ∧
      (∀ s, (P.stratum s).complexDimension = difference (label s)) := by
  classical
  let e := boundedHomeomorph N
  let I := {ab : DominantPair // OrbitBound ab N}
  choose U Z hU hZ hUZ using fun (s : I) ↦ boundedOrbitLocallyClosed s.val N s.property
  let S (s : I) : Stratum (latticeStages.space N) :=
    ⟨⟨e.symm ⁻¹' U s, (hU s).preimage e.symm.continuous⟩,
      Subtype.val ⁻¹' (e.symm ⁻¹' Z s),
      (hZ s).preimage (e.symm.continuous.comp continuous_subtype_val), difference s.val⟩
  have hS (s : I) : Set.range (S s).inclusion = {L | L.val ∈ gl2Orbit s.val} := by
    rw [show Set.range (S s).inclusion = e.symm ⁻¹' U s ∩ e.symm ⁻¹' Z s from
      orbitInclusionRange ⟨_, (hU s).preimage e.symm.continuous⟩ _
        ((hZ s).preimage e.symm.continuous) _,
      ← Set.preimage_inter, ← hUZ]
    ext L
    change ((e.symm L).val ∈ gl2Orbit s.val) ↔ L.val ∈ gl2Orbit s.val
    rw [boundedHomeomorph_symm_val]
  refine ⟨⟨I, S, ?_⟩, Subtype.val, Subtype.property, hS, fun _ ↦ rfl⟩
  intro L
  obtain ⟨ab, hL, hu⟩ := RankTwoSchubertStrata.smithClassification.1 L.val
  have hl := ((RankTwoSchubertStrata.orbit_endpoints hL).1 N).mp L.property.1
  have hr := ((RankTwoSchubertStrata.orbit_endpoints hL).2 (-(N : ℤ))).mp L.property.2
  have hab : ab.val.2 ≤ ab.val.1 := ab.property
  have hN : OrbitBound ab N := by
    intro i
    fin_cases i <;> simp only [pairCoweight] <;> omega
  refine ⟨⟨ab, hN⟩, ?_, ?_⟩
  · change L ∈ Set.range (S ⟨ab, hN⟩).inclusion
    rw [hS]
    exact hL
  · intro s hs
    change L ∈ Set.range (S s).inclusion at hs
    rw [hS] at hs
    exact Subtype.ext (hu s.val hs)

/-- The symmetric bounds give the common finite-stage action and orbit stratification. -/
private theorem grassmannianStages (c : ContinuousJets) :
    ∃ (D : GrassmannianStages c) (label : (D.stratification 2).Index → DominantPair),
      (∀ s, OrbitBound (label s) 2) ∧
      (∀ s, Set.range ((D.stratification 2).stratum s).inclusion = {L | L.val ∈ gl2Orbit (label s)}) ∧
      (∀ s, ((D.stratification 2).stratum s).complexDimension = difference (label s)) := by
  classical
  obtain ⟨B, hcutoff, hact⟩ := latticeStageActions c
  choose P label hBound hRange hDim using latticeStageStratification
  let G : GrassmannianStages c := ⟨latticeStages, fun _ ↦ rfl, B, hcutoff, hact, P,
    fun n s ↦ ⟨label n s, hRange n s, hDim n s⟩⟩
  exact ⟨G, label 2, hBound 2, hRange 2, hDim 2⟩

end Stages
section CoefficientEquivariance

open AnalyticAction
open Analytic.IntersectionComplex (shiftedConstant)
open EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)

open private pullback_constantTransition
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent

private def jetActionAbove {J : JetSystem.{0}} {X : TopCat.{0}} {n : ℕ}
    (A : AnalyticAction (J.group n) X) : JetAction J X where
  cutoff := n
  action k hk :=
    { act := J.parameterMap hk (𝟙 X) ≫ A.act
      one_act x := by
        change A.act (J.truncate n k hk 1, x) = x
        rw [J.truncate_one, A.one_act]
      mul_act g h x := by
        change A.act (J.truncate n k hk (g * h), x) =
          A.act (J.truncate n k hk g, A.act (J.truncate n k hk h, x))
        rw [J.truncate_mul, A.mul_act] }
  factors := by
    intro k l hk hkl
    apply TopCat.ext
    rintro ⟨g, x⟩
    change A.act (J.truncate n k hk (J.truncate k l hkl g), x) =
      A.act (J.truncate n l (hk.trans hkl) g, x)
    exact congrArg (fun p ↦ A.act (p, x))
      (congrArg (fun f : (J.group l).space ⟶ (J.group n).space ↦ f g) (J.truncate_comp hk hkl))

private theorem jetActionAbove_at {J : JetSystem.{0}} {X : TopCat.{0}} {n : ℕ}
    (A : AnalyticAction (J.group n) X) : ((jetActionAbove A).action n (le_refl n)).act = A.act := by
  apply TopCat.ext
  rintro ⟨g, x⟩
  change A.act (J.truncate n n (le_refl n) g, x) = A.act (g, x)
  rw [J.truncate_id]
  rfl

/-- The normalized coefficient data at different jet levels use the same constant
pullback comparisons. -/
private theorem constantJetEquivariance {J : JetSystem.{0}} {X : TopCat.{0}}
    (A : JetAction J X) (d : ℕ) :
    ∃ e : A.Equivariance (shiftedConstant X d).obj,
      ∀ k hk, (e.datum k hk).iso =
        shiftedConstantPullback (A.action k hk).act d ≪≫
          (shiftedConstantPullback (projection _ X) d).symm := by
  classical
  choose e he using fun k (hk : A.cutoff ≤ k) ↦
    ConvolutionConstantDescent.normalizedEquivariance (A.action k hk) d
  refine ⟨⟨e, ?_⟩, he⟩
  intro k l hk h
  change pullbackMorphism (J.parameterMap h (𝟙 X)) (A.factors hk h)
    (TopCat.ext (fun _ ↦ rfl)) (e k hk).iso.hom = (e l (hk.trans h)).iso.hom
  rw [he, he, pullback_constantTransition]
  rfl

private theorem constantComparisonIntertwines {J : JetSystem.{0}}
    {Y Z : TopCat.{0}} {A : JetAction J Y} {B : JetAction J Z} {f : Y ⟶ Z}
    (h : EquivariantIntersectionComplexesSpecs.Intertwines A B f) (d : ℕ)
    (α : A.Equivariance (shiftedConstant Y d).obj)
    (β : B.Equivariance (shiftedConstant Z d).obj)
    (hα : ∀ k hk, (α.datum k hk).iso =
      shiftedConstantPullback (A.action k hk).act d ≪≫ (shiftedConstantPullback (projection _ Y) d).symm)
    (hβ : ∀ k hk, (β.datum k hk).iso =
      shiftedConstantPullback (B.action k hk).act d ≪≫ (shiftedConstantPullback (projection _ Z) d).symm) :
    IntertwinesPullback h α β (shiftedConstantPullback f d).inv := by
  intro k hA hB
  let a := (A.action k hA).act
  let p := projection (J.group k) Y
  let F := (shiftedConstant Z d).obj
  let ψ := shiftedConstantPullback f d
  have compare (t : Parameters (J.group k) Y ⟶ Y) :
      (derivedInverseImageComposition t f).app F ≪≫ (derivedInverseImage t).mapIso ψ ≪≫
        shiftedConstantPullback t d = shiftedConstantPullback (t ≫ f) d := by
    apply Iso.ext
    exact ConvolutionConstantDescent.shiftedPullbackComposition t f d
  have restricted :
      restrictedArrow h β k hA hB =
        ((derivedInverseImage a).mapIso ψ ≪≫ shiftedConstantPullback a d ≪≫
          (shiftedConstantPullback p d).symm ≪≫ ((derivedInverseImage p).mapIso ψ).symm).hom := by
    dsimp only [restrictedArrow]
    rw [hβ]
    rw [pullback_constantTransition (parameterInclusion (J.group k) f)
      (h k hA hB) (projectionSquare (J.group k) f) d]
    change (derivedInverseImageComposition a f).inv.app F ≫
      (shiftedConstantPullback (a ≫ f) d ≪≫ (shiftedConstantPullback (p ≫ f) d).symm).hom ≫
        (derivedInverseImageComposition p f).hom.app F = _
    rw [← compare a, ← compare p]
    simp
  rw [restricted, hα]
  simp [a, p, ψ]

end CoefficientEquivariance
section SmallSchubertModels

open RankTwoSchubertStrataSpecs SchubertIntersectionConstructibilitySpecs
open EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion)

open private schubert_point_homeomorph orbit_mem_of_small boundedSubspace_injective
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
open private boundedVal_closedEmbedding from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShortWindowTopology

private theorem closureLattices_small {ab : DominantPair} (h : ¬2 ≤ difference ab) :
    closureLattices ab = gl2Orbit ab := by
  ext L
  constructor
  · exact orbit_mem_of_small h
  · intro hL
    exact ⟨ab, (RankTwoSchubertStrata.below_iff ab ab).mpr ⟨rfl, le_rfl, le_rfl⟩, hL⟩

private theorem minusculeClosure : closureLattices minusculePair = colength 1 :=
  (closureLattices_small (by decide)).trans MinusculeAndTwoStep.minusculeOrbit.1.symm

/-- Identify a closed analytic chart with the occupied Schubert scheme
of the same lattices in any admissible symmetric window. -/
private theorem schubertModelOfChart {Y : TopCat.{0}} (j : Y ⟶ Gr)
    (hj : IsClosedEmbedding j)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (hRange : Set.range j = closureLattices ab) :
    ∃ (e : Y ≅ SchubertSpace ab N hN) (L : Y → BoundedLattice 2 N),
      ∀ y, (L y).val = j y ∧ schubertPointSubspace (e.hom y) = boundedSubspace (L y) := by
  obtain ⟨E, hE⟩ := schubert_point_homeomorph ab N hN
  let k : schubertLatticeSet ab N → Gr := fun b ↦ b.val.val
  have hk : IsEmbedding k := (boundedVal_closedEmbedding N).isEmbedding.comp IsEmbedding.subtypeVal
  have hr : Set.range k = closureLattices ab := by
    ext L
    constructor
    · rintro ⟨b, rfl⟩
      exact b.property
    · intro hL
      obtain ⟨b, hb⟩ := RankTwoSchubertStrata.closureLattices_bounded hN hL
      refine ⟨⟨b, ?_⟩, hb⟩
      change b.val ∈ closureLattices ab
      rwa [hb]
  let t := hj.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr (hRange.trans hr.symm)).trans hk.toHomeomorph.symm)
  let e : Y ≃ₜ SchubertSpace ab N hN := t.trans E.symm
  refine ⟨TopCat.isoOfHomeo e, fun y ↦ (t y).val, fun y ↦ ⟨?_, ?_⟩⟩
  · have ht := congrArg Subtype.val (hk.toHomeomorph.apply_symm_apply
      (Homeomorph.setCongr (hRange.trans hr.symm) (hj.isEmbedding.toHomeomorph y)))
    exact ht
  · change schubertPointSubspace (E.symm (t y)) = _
    rw [hE, E.apply_symm_apply]

private theorem actionCommutesWithSchubertModel
    {c : ContinuousJets} {Y : TopCat.{0}} {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    (A : JetAction (jetSystem c) Y) (B : JetAction (jetSystem c) (SchubertSpace ab N hN))
    (hB : ActualSchubertAction ab N hN B) (f : Y ⟶ SchubertSpace ab N hN)
    (L : Y → BoundedLattice 2 N)
    (hf : ∀ y, schubertPointSubspace (f y) = boundedSubspace (L y))
    (actual : ∀ k (hk : A.cutoff ≤ k) (g : GL (Fin 2) O) (y : Y),
      (L ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y))).val =
        positiveGLMap 2 g • (L y).val) :
    EquivariantIntersectionComplexesSpecs.Intertwines A B f := by
  intro k hx hy
  apply TopCat.ext
  rintro ⟨q, y⟩
  obtain ⟨g, rfl⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 _ (Nat.succ_pos k) q
  apply (show Function.Injective (schubertPointSubspace (ab := ab) (N := N) (hN := hN)) from by
    obtain ⟨E, hE⟩ := schubert_point_homeomorph ab N hN
    intro p r hr
    apply E.injective
    apply Subtype.ext
    apply boundedSubspace_injective N
    simpa only [hE] using hr)
  change schubertPointSubspace ((B.action k hy).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, f y)) =
    schubertPointSubspace (f ((A.action k hx).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y)))
  rw [hB.2.1 k hy g (f y) (L y) (hf y), hf]
  change _ = latticeSubspace (-(N : ℤ)) (2 * N) _
  rw [actual]

open AnalyticAction
open Analytic.IntersectionComplex (DimensionFiltration complex shiftedConstant)

private theorem filtrationAtDepthZero {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {Y : TopCat.{0}} {f : Y ⟶ SchubertSpace ab N hN} {P : Stratification Y}
    {s k : ℕ} {D : DimensionFiltration Y s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) (hk : k = 0) :
    HEq D (DimensionFiltration.top Y (difference ab)) := by
  cases h with
  | top => rfl
  | attach => omega

private theorem normalizedTopCoefficients {J : JetSystem.{0}} {Y : TopCat.{0}}
    (a : DerivedAdjunctions.{0}) (A : JetAction J Y) (d : ℕ)
    (e : A.Equivariance (shiftedConstant Y d).obj)
    (h : NormalizedICDatum a A (.top Y d) e) :
    ∀ k hk, (e.datum k hk).iso = shiftedConstantPullback (A.action k hk).act d ≪≫
      (shiftedConstantPullback (projection _ Y) d).symm := by
  cases h with
  | top _ coefficients => exact coefficients

private theorem topICComparison
    {c : ContinuousJets} {ab : DominantPair} {Y : TopCat.{0}}
    (a : DerivedAdjunctions.{0}) (A : JetAction (jetSystem c) Y)
    (α : A.Equivariance (shiftedConstant Y (difference ab)).obj)
    (hα : ∀ k hk, (α.datum k hk).iso =
      shiftedConstantPullback (A.action k hk).act (difference ab) ≪≫
        (shiftedConstantPullback (projection _ Y) (difference ab)).symm)
    (h : difference ab / 2 = 0) (hN : OrbitBound ab 2)
    (e : Y ≅ SchubertSpace ab 2 hN)
    (L : Y → BoundedLattice 2 2)
    (hL : ∀ y, schubertPointSubspace (e.hom y) = boundedSubspace (L y))
    (B : SchubertJetAction c ab 2 hN)
    (hc : EquivariantIntersectionComplexesSpecs.Intertwines A B.action e.hom)
    (P : Stratification (SchubertSpace ab 2 hN))
    (D : DimensionFiltration (SchubertSpace ab 2 hN) (orbitDimension ab (difference ab / 2)))
    (hIC : IsNormalizedOrbitIC ab 2 hN (𝟙 _) (difference ab / 2) P D)
    (β : B.action.Equivariance (complex D).obj)
    (hβ : NormalizedICDatum a B.action D β) :
    ∃ C : ICComparison ab A (shiftedConstant Y (difference ab)) α, C.lattice = L := by
  let T := SchubertSpace ab 2 hN
  have build (D₀ : DimensionFiltration T (difference ab))
      (h₀ : IsNormalizedOrbitIC ab 2 hN (𝟙 _) 0 P D₀)
      (β₀ : B.action.Equivariance (complex D₀).obj)
      (n₀ : NormalizedICDatum a B.action D₀ β₀) :
      ∃ C : ICComparison ab A (shiftedConstant Y (difference ab)) α, C.lattice = L := by
    have ht := eq_of_heq (filtrationAtDepthZero h₀ rfl)
    subst D₀
    let v := (shiftedConstantPullback e.hom (difference ab)).symm
    have hv := constantComparisonIntertwines hc (difference ab) α β₀ hα
      (normalizedTopCoefficients a B.action (difference ab) β₀ n₀)
    let D' : DimensionFiltration T (orbitDimension ab (difference ab / 2)) :=
      h.symm ▸ (.top T (difference ab) : DimensionFiltration T (orbitDimension ab 0))
    have result :
        ∃ (β' : B.action.Equivariance (complex D').obj)
          (v' : (shiftedConstant Y (difference ab)).obj ≅ (derivedInverseImage e.hom).obj (complex D').obj),
          IsNormalizedOrbitIC ab 2 hN (𝟙 _) (difference ab / 2) P D' ∧
          NormalizedICDatum a B.action D' β' ∧ IntertwinesPullback hc α β' v'.hom := by
      generalize (difference ab / 2) = n at h D' ⊢
      subst n
      exact ⟨β₀, v, h₀, n₀, hv⟩
    obtain ⟨β', v', h', hn, hv'⟩ := result
    exact ⟨⟨hN, e, L, hL, P, D', h', B.action, B.actual, hc, β', a, hn, v', hv'⟩, rfl⟩
  generalize difference ab / 2 = n at h D hIC β hβ
  subst n
  exact build D hIC β hβ

end SmallSchubertModels

section MinusculeCoordinates

open private firstLine_jet from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
open private latticeSubspace_positive from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices

private theorem firstPlane_positive (g : GL (Fin 2) O) (L : GL2Lattice) :
    ((latticeSubspace 0 1 L).map constantCoordinates.toLinearMap).map
        (constantJetLinear (reduceGL 2 2 (by decide) g)) =
      (latticeSubspace 0 1 (positiveGLMap 2 g • L)).map constantCoordinates.toLinearMap :=
  (firstLine_jet _ _ _ (latticeSubspace_positive 0 (m := 2) (by decide : 1 ≤ 2) (le_refl 2) g L).symm).symm

end MinusculeCoordinates


section MinusculeComparison

open AnalyticAction
open Analytic.IntersectionComplex (shiftedConstant DimensionFiltration complex)
open EquivariantIntersectionComplexesSpecs
open RankTwoSchubertStrataSpecs SchubertIntersectionConstructibilitySpecs

open private colength_positive from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem minusculeLatticeCoordinatesInjective :
    Function.Injective (fun L : Colength 1 ↦
      (latticeSubspace 0 1 L.val).map constantCoordinates.toLinearMap) := by
  intro L M h
  obtain ⟨e, he, _⟩ := BoundedLattices.windowLatticeComparison 2 0 1
  let l : WindowLattice 2 0 1 := ⟨L.val, MinusculeAndTwoStep.minusculeOrbit.2 L, L.property.1⟩
  let m : WindowLattice 2 0 1 := ⟨M.val, MinusculeAndTwoStep.minusculeOrbit.2 M, M.property.1⟩
  have h' := (Submodule.map_injective_of_injective constantCoordinates.injective) h
  have he' : (e l).val = (e m).val :=
    (he l).trans (h'.trans (he m).symm)
  exact Subtype.ext (congrArg (fun q : WindowLattice 2 0 1 ↦ q.val) (e.injective (Subtype.ext he')))

private theorem constantArrowChange {W Z : TopCat.{0}} {a b : W ⟶ Z}
    (p : W ⟶ Z) (d : ℕ) (h : a = b) :
    (shiftedConstantPullback a d ≪≫ (shiftedConstantPullback p d).symm).hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj (shiftedConstant Z d).obj) h) ≫
        (shiftedConstantPullback b d ≪≫ (shiftedConstantPullback p d).symm).hom := by
  subst b
  simp

private theorem minusculeActionOnLattices (c : ContinuousJets) (d : SplittingData)
    (j : minuscule ⟶ Gr) (hr : Set.range j = colength 1)
    (hp : ∀ p, firstPlane p = (latticeSubspace 0 1 (j p)).map constantCoordinates.toLinearMap) :
    let A := jetActionAbove (J := jetSystem c) (n := 1) d.firstAction
    ∀ k (hk : A.cutoff ≤ k) (g : GL (Fin 2) O) (p : minuscule),
      j ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
        positiveGLMap 2 g • j p := by
  intro A k hk g p
  let z := d.firstAction.act (reduceGL 2 2 (by decide) g, p)
  have hact : (A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p) = z := by
    change d.firstAction.act (jetTruncation (show 1 ≤ k from hk)
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g), p) = z
    rw [truncate_reduce]
  rw [hact]
  have colengthAt (w : minuscule) : j w ∈ colength 1 :=
    hr ▸ Set.mem_range_self w
  have hpos : positiveGLMap 2 g • j p ∈ colength 1 :=
    (colength_positive g (colengthAt p).1).mpr (colengthAt p)
  apply congrArg Subtype.val (minusculeLatticeCoordinatesInjective
    (a₁ := ⟨j z, colengthAt z⟩) (a₂ := ⟨_, hpos⟩) ?_)
  change (latticeSubspace 0 1 (j z)).map constantCoordinates.toLinearMap = _
  rw [← hp, d.first_action, hp, firstPlane_positive]

private theorem minusculeICComparison (c : ContinuousJets) (d : SplittingData)
    (j : minuscule ⟶ Gr) (hj : IsClosedEmbedding j) (hr : Set.range j = colength 1)
    (hp : ∀ p, firstPlane p = (latticeSubspace 0 1 (j p)).map constantCoordinates.toLinearMap)
    (a : DerivedAdjunctions.{0})
    (hIC : ∀ hN : OrbitBound minusculePair 2,
      ∃ (B : SchubertJetAction c minusculePair 2 hN)
        (P : Stratification (SchubertSpace minusculePair 2 hN))
        (D : DimensionFiltration (SchubertSpace minusculePair 2 hN) 1),
        IsNormalizedOrbitIC minusculePair 2 hN (𝟙 _) 0 P D ∧
          ∃ β : B.action.Equivariance (complex D).obj, NormalizedICDatum a B.action D β) :
    ∃ (A : JetAction (jetSystem c) minuscule) (h₁ : A.cutoff ≤ 1)
      (ha : (A.action 1 h₁).act = d.firstAction.act)
      (α : A.Equivariance minusculeFactor.obj)
      (C : ICComparison minusculePair A minusculeFactor α),
      (∀ p, (C.lattice p).val = j p) ∧
        (∀ k (hk : A.cutoff ≤ k) (g : GL (Fin 2) O) (p : minuscule),
          j ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
            positiveGLMap 2 g • j p) ∧
        (α.datum 1 h₁).iso.hom =
          eqToHom (congrArg (fun f => (derivedInverseImage f).obj minusculeFactor.obj) ha) ≫
            d.firstEq.iso.hom := by
  let A : JetAction (jetSystem c) minuscule := jetActionAbove (J := jetSystem c) (n := 1) d.firstAction
  have ha := jetActionAbove_at (J := jetSystem c) (n := 1) d.firstAction
  obtain ⟨α, hα⟩ := constantJetEquivariance A 1
  have hN : OrbitBound minusculePair 2 := by
    intro i
    fin_cases i <;> decide
  obtain ⟨e, L, hL⟩ := schubertModelOfChart j hj minusculePair 2 hN (hr.trans minusculeClosure.symm)
  obtain ⟨B, P, D, hP, β, hβ⟩ := hIC hN
  have hc : EquivariantIntersectionComplexesSpecs.Intertwines A B.action e.hom := by
    apply actionCommutesWithSchubertModel A B.action B.actual e.hom L (fun p ↦ (hL p).2)
    intro k hk g p
    rw [(hL _).1, (hL _).1]
    exact minusculeActionOnLattices c d j hr hp k hk g p
  obtain ⟨C, hC⟩ := topICComparison (ab := minusculePair) a A α hα (by decide) hN e L (fun p ↦ (hL p).2) B hc P D hP β hβ
  refine ⟨A, le_rfl, ha, α, C, fun p ↦ ?_, minusculeActionOnLattices c d j hr hp, ?_⟩
  · rw [hC]
    exact (hL p).1
  · rw [hα, d.first_normalized]
    exact constantArrowChange _ _ ha

end MinusculeComparison

section LocalAssembly

open AnalyticAction
open EquivariantIntersectionComplexesSpecs

private theorem reduceAction {c : ContinuousJets} {Y : TopCat.{0}}
    (A : JetAction (jetSystem c) Y) (h : A.cutoff = 1)
    {B : AnalyticAction ((jetSystem c).group 1) Y} (hB : (A.action 1 h.le).act = B.act)
    (k : ℕ) (hk : A.cutoff ≤ k) (g : PositiveJet k) (y : Y) :
    (A.action k hk).act (g, y) = B.act (jetTruncation (h ▸ hk) g, y) := by
  have h1 : 1 ≤ k := h ▸ hk
  have he := (A.factors h.le h1).symm.trans
    (congrArg (fun f => (jetSystem c).parameterMap h1 (𝟙 Y) ≫ f) hB)
  exact congrArg (fun f : Parameters ((jetSystem c).group k) Y ⟶ Y => f (g, y)) he

open private twoStepCoordinates_injective terminalPlane_positive
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepICNormalization
open private colength_positive from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem terminalLatticeAction (c : ContinuousJets) (d : SplittingData)
    (A : JetAction (jetSystem c) surface) (hA : A.cutoff = 1)
    (hact : (A.action 1 hA.le).act = d.terminalAction.act) (e : surface ⟶ TwoStepIntersectionComplexSpecs.X)
    (he : ∀ p, secondPlane p =
      (latticeSubspace 0 2 (e p).val).map twoStepCoordinates.toLinearMap) :
    ∀ k (hk : A.cutoff ≤ k) (g : GL (Fin 2) O) (p : surface),
      (e ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p))).val =
        positiveGLMap 2 g • (e p).val := by
  intro k hk g p
  rw [reduceAction A hA hact, truncate_reduce]
  let z := d.terminalAction.act (reduceGL 2 2 (by decide) g, p)
  have hpos : positiveGLMap 2 g • (e p).val ∈ colength 2 :=
    (colength_positive g (e p).property.1).mpr (e p).property
  apply congrArg Subtype.val (twoStepCoordinates_injective (a₁ := e z) (a₂ := ⟨_, hpos⟩) ?_)
  change (latticeSubspace 0 2 (e z).val).map twoStepCoordinates.toLinearMap = _
  rw [← he, d.terminal_action, he, terminalPlane_positive]

private def ActsOnLattices {c : ContinuousJets} {Y : TopCat.{0}}
    (A : JetAction (jetSystem c) Y) (i : Y ⟶ Gr) : Prop :=
  ∀ k (hk : A.cutoff ≤ k) (g : GL (Fin 2) O) (y : Y),
    i ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y)) = positiveGLMap 2 g • i y

private structure SquareSupports {c : ContinuousJets} (S : LocalSquare c) where
  first : minuscule ⟶ Gr
  terminal : surface ⟶ Gr
  firstClosed : IsClosedEmbedding first
  terminalClosed : IsClosedEmbedding terminal
  firstCoordinates : ∀ p, first p = (S.minusculeIC.lattice p).val
  terminalCoordinates : ∀ p, terminal p = (S.twoStepIC.lattice p).val
  firstRange : Set.range first = colength 1
  terminalRange : Set.range terminal = colength 2
  firstActs : ActsOnLattices S.minAction first
  terminalActs : ActsOnLattices S.terminalAction terminal

end LocalAssembly

section FrameDescent

open Analytic AnalyticAction ConvolutionUnitConeSpecs MinusculeFrameDescentSpecs
open ConvolutionConstantDescentSpec (coefficientTensor)
open ConvolutionEquivariantSplittingSpecs (SplittingData)

private theorem frameTensorMap {Z : TopCat.{0}} {F F' G G' : Sheaves Z}
    (u : F ⟶ F') (v : G ⟶ G') :
    ConvolutionFrameOverlapSpecs.tensorMap u v = tensorMap u v := by
  unfold ConvolutionFrameOverlapSpecs.tensorMap tensorMap
  rfl

private theorem frameInverseTensorMap {W Z : TopCat.{0}} (r : W ⟶ Z)
    (F G : Sheaves Z) : ConvolutionFrameOverlapSpecs.inverseTensorMap r F G =
      inverseTensorMap r F G := by
  unfold ConvolutionFrameOverlapSpecs.inverseTensorMap inverseTensorMap
  rfl

private theorem framePullbackTensorMap {W Z X Y : TopCat.{0}} (r : W ⟶ Z)
    (a : Z ⟶ X) (b : Z ⟶ Y) :
    ConvolutionFrameOverlapSpecs.pullbackTensorMap r a b = MinusculeFrameDescentSpecs.pullbackTensorMap r a b := by
  simp only [ConvolutionFrameOverlapSpecs.pullbackTensorMap, MinusculeFrameDescentSpecs.pullbackTensorMap,
    frameInverseTensorMap, frameTensorMap]

private theorem frameOverlap {hH : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup hH) minuscule} (α : A.Equivariance minusculeFactor.obj)
    (q : representativeSpace ⟶ ordered) (b : representativeSpace ⟶ minuscule)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b) :
    ConvolutionFrameOverlapSpecs.FrameOverlapIdentification α q b d =
      FrameOverlapIdentification α q b d := by
  simp only [ConvolutionFrameOverlapSpecs.FrameOverlapIdentification, FrameOverlapIdentification,
    framePullbackTensorMap, frameTensorMap, ConvolutionFrameOverlapSpecs.leftLeg,
    ConvolutionFrameOverlapSpecs.rightLeg, leftLeg, rightLeg,
    ConvolutionFrameOverlapSpecs.pullbackFactorIso, pullbackFactorIso,
    ConvolutionFrameOverlapSpecs.quotientTransition, quotientTransition,
    ConvolutionFrameOverlapSpecs.overlap, overlap,
    ConvolutionFrameOverlapSpecs.shiftedSingleMap, shiftedSingleMap]

private theorem frameAction {hH : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup hH) minuscule} {B : AnalyticAction (jetGroup hH) ordered}
    (α : A.Equivariance minusculeFactor.obj) (β : B.Equivariance orderedFactor.obj)
    (q : representativeSpace ⟶ ordered) (b : representativeSpace ⟶ minuscule)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b) :
    ConvolutionFrameOverlapSpecs.FrameActionIdentification α β q b d =
      FrameActionIdentification α β q b d := by
  simp only [ConvolutionFrameOverlapSpecs.FrameActionIdentification, FrameActionIdentification,
    framePullbackTensorMap, frameTensorMap, ConvolutionFrameOverlapSpecs.pullbackFactorIso,
    pullbackFactorIso, ConvolutionFrameOverlapSpecs.orderedTransition, orderedTransition]

private theorem frameDescentCondition (d : SplittingData) :
    ConvolutionFrameOverlapSpecs.ActualDescent d.firstEq d.orderedEq =
      ActualDescent d.firstEq d.orderedEq := by
  simp only [ConvolutionFrameOverlapSpecs.ActualDescent, ActualDescent, frameOverlap, frameAction]

end FrameDescent

section StageAssembly

open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open EquivariantIntersectionComplexesSpecs (ContinuousJets jetSystem Intertwines)
open FiniteStageClosedExtensionSpecs (AgreesWithMates MatesAreIso fullSupportComparison)
open MinusculeSupportIntersectionsSpecs (SupportInStage pointEmbedding)
open ClosedSupportBaseChangeSpecs (MateCommutes)

private theorem extendsAtStageFromMates {J : JetSystem.{0}} {X Y : TopCat.{0}}
    {A : JetAction J Y} {B : JetAction J X} {F : BoundedBelow Y} {G : Derived X}
    {i : Y ⟶ X} (h : Intertwines A B i) (a : DerivedAdjunctions.{0})
    {α : A.Equivariance F.obj} {β : B.Equivariance G}
    (e : ((derivedDirectImage i).obj F).obj ≅ G)
    (hIso : MatesAreIso h (@a) F) (hEq : AgreesWithMates h (@a) α β e.inv) :
    ExtendsAtStage i (@a) α β e := by
  intro k hy hx
  refine ⟨h k hy hx, (hIso k hy hx).1, (hIso k hy hx).2, ?_⟩
  let pull := derivedInverseImage (B.action k hx).act
  have hCancel : pull.map e.hom ≫ pull.map e.inv = 𝟙 _ := by
    rw [← pull.map_comp, Iso.hom_inv_id, pull.map_id]
  have hEq' := congrArg (fun m => pull.map e.hom ≫ m) (hEq k hy hx)
  dsimp only [pull] at hCancel hEq'
  simpa only [Category.assoc, reassoc_of% hCancel, Category.id_comp] using hEq'

private def extendFromStages {c : ContinuousJets} (D : GrassmannianStages c)
    {Y : TopCat.{0}} {i : Y ⟶ Gr} {A : JetAction (jetSystem c) Y}
    {F : BoundedBelow Y} {α : A.Equivariance F.obj}
    (a : DerivedAdjunctions.{0}) (hi : IsClosedEmbedding i)
    (β : D.actions.Equivariance ((derivedDirectImage i).obj F).obj)
    (hp : IsFiniteStagePerverse D.stages D.stratification ((derivedDirectImage i).obj F).obj)
    (hfull : ∀ (n : ℕ) (j : Y ⟶ D.stages.space n) (h : j ≫ D.stages.inclusion n = i)
      (commutes : Intertwines A (D.actions.stageAction n) j),
        IsIso (fullSupportComparison h (@a) F) ∧ MatesAreIso commutes (@a) F ∧
          AgreesWithMates commutes (@a) α (β.datum n) (fullSupportComparison h (@a) F))
    (hStage : ∀ n, 2 ≤ n → SupportInStage D.actions i A n) :
    GrassmannianExtension D A F α i := by
  refine ⟨⟨_, β⟩, hi, Iso.refl _, hp, ?_⟩
  intro n hn
  let r := hStage n hn
  obtain ⟨hiso, hmates, hcompare⟩ := hfull n r.inclusion r.factors r.actionSquare
  let e := (@asIso _ _ _ _ (fullSupportComparison r.factors (@a) F) hiso).symm
  exact ⟨r.inclusion, @a, e, r.factors, r.closed,
    extendsAtStageFromMates r.actionSquare (@a) e hmates hcompare⟩

open RankTwoSchubertStrataSpecs (difference)

private theorem extendLocalSquare {c : ContinuousJets} (D : GrassmannianStages c)
    (label : (D.stratification 2).Index → DominantPair)
    (hBound : ∀ s, OrbitBound (label s) 2)
    (hRange : ∀ s, Set.range ((D.stratification 2).stratum s).inclusion =
      {L | L.val ∈ gl2Orbit (label s)})
    (hDimension : ∀ s, ((D.stratification 2).stratum s).complexDimension = difference (label s))
    (S : LocalSquare c) (H : SquareSupports S) (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({S.splitting.point} : Set surface)) ⊣
      LocalSheaf.closedExtensionPlus S.splitting.closed)
    (hPoint : Intertwines S.pointAction S.terminalAction (closedInclusion ({S.splitting.point} : Set surface)))
    (hMates : ∀ (k : ℕ) (hₚ : S.pointAction.cutoff ≤ k) (hₛ : S.terminalAction.cutoff ≤ k),
      let J := (jetSystem c).group k
      let i := closedInclusion ({S.splitting.point} : Set surface)
      let F := IntersectionComplex.point S.splitting.point
      MateCommutes (hPoint k hₚ hₛ) (projectionSquare J i) (a (parameterInclusion J i)) b
        (𝟙 ((LocalSheaf.closedExtensionPlus S.splitting.closed).obj F))
        (S.pointAsSkyscraper.datum k hₛ).iso.hom (S.pointDatum.datum k hₚ).iso.hom)
    (hUnit : ∀ (k : ℕ) (hk : S.terminalAction.cutoff ≤ k),
      ConvolutionEquivariantSplittingSpecs.Intertwines (S.intersectionDatum.datum k hk)
        (S.convolutionDatum.datum k hk) (S.constantIdentification.inv ≫ unit))
    (hSection : ∀ (k : ℕ) (hk : S.terminalAction.cutoff ≤ k),
      ConvolutionEquivariantSplittingSpecs.Intertwines (S.pointAsSkyscraper.datum k hk)
        (S.convolutionDatum.datum k hk) S.splitting.sectionMap) : ExtendsSquare D S := by
  let d := S.splitting
  let j := H.terminal
  let p := pointEmbedding d j
  let F := IntersectionComplex.surface d.point d.closed
  let P := IntersectionComplex.point d.point
  let Q := (LocalSheaf.closedExtensionPlus d.closed).obj P
  let f : F ⟶ convolution := ObjectProperty.homMk (S.constantIdentification.inv ≫ unit)
  let g : Q ⟶ convolution := ObjectProperty.homMk d.sectionMap
  have hScalar : j d.point = scalarPoint :=
    (H.terminalCoordinates d.point).trans (S.scalarCoordinates ⟨d.point, rfl⟩).2
  have hp : IsClosedEmbedding p := H.terminalClosed.comp d.closed.isClosedEmbedding_subtypeVal
  obtain ⟨G, _, hPerversity⟩ := MinusculeSupportIntersections.minusculeSupportIntersections c D.stages
    D.actions D.isBoundedSet D.actionCutoff D.actionOnLattices D.stratification label hBound hRange
    hDimension d H.first j H.firstClosed H.terminalClosed H.firstRange H.terminalRange hScalar
    S.minAction S.terminalAction S.pointAction S.minCutoff S.terminalCutoff S.pointCutoff
    H.firstActs H.terminalActs S.pointActs
  obtain ⟨hp₁, hp₂, hpₚ, hpL⟩ := hPerversity S.constantIdentification
  obtain ⟨r₁, _, _, _⟩ := SupportIntersectionEquivariance.supportIntersectionEquivariance G.first G.firstLevels
  obtain ⟨r₂, _, _, hn₂⟩ := SupportIntersectionEquivariance.supportIntersectionEquivariance G.terminal G.terminalLevels
  obtain ⟨rₚ, _, _, _⟩ := SupportIntersectionEquivariance.supportIntersectionEquivariance G.scalar G.scalarLevels
  obtain ⟨α₁, _, h₁⟩ := FiniteStageClosedExtensions.closedExtensionAtStages H.firstClosed G.first
    (@a) minusculeFactor S.minDatum (r₁ minusculeFactor S.minDatum)
  obtain ⟨α₂, hc₂, h₂⟩ := FiniteStageClosedExtensions.closedExtensionAtStages H.terminalClosed G.terminal
    (@a) F S.intersectionDatum (r₂ F S.intersectionDatum)
  obtain ⟨αₚ, hcₚ, hₚ⟩ := FiniteStageClosedExtensions.closedExtensionAtStages hp G.scalar
    (@a) P S.pointDatum (rₚ P S.pointDatum)
  obtain ⟨αL, hcL, hL⟩ := FiniteStageClosedExtensions.closedExtensionAtStages H.terminalClosed G.terminal
    (@a) convolution S.convolutionDatum (r₂ convolution S.convolutionDatum)
  obtain ⟨αQ, hcQ, _⟩ := FiniteStageClosedExtensions.closedExtensionAtStages H.terminalClosed G.terminal
    (@a) Q S.pointAsSkyscraper (r₂ Q S.pointAsSkyscraper)
  let E := extendFromStages D (@a) H.firstClosed α₁ hp₁.2 h₁ G.firstInStage
  let K := extendFromStages D (@a) H.terminalClosed α₂ hp₂.2 h₂ G.terminalInStage
  let M := extendFromStages D (@a) hp αₚ hpₚ.2 hₚ G.scalarInStage
  let L := extendFromStages D (@a) H.terminalClosed αL hpL.2 hL G.terminalInStage
  obtain ⟨u₀, hu⟩ := (FiniteStageClosedExtensions.closedExtensionNaturality G.terminal (@a) f).2
    (r₂ F S.intersectionDatum) (r₂ convolution S.convolutionDatum) hc₂ hcL (hn₂ f hUnit)
  obtain ⟨s, hs⟩ := (FiniteStageClosedExtensions.closedExtensionNaturality G.terminal (@a) g).2
    (r₂ Q S.pointAsSkyscraper) (r₂ convolution S.convolutionDatum) hcQ hcL (hn₂ g hSection)
  have hCompat := PointMatesOnSupportIntersections.pointMatesOnIntersections d.closed G.terminal
    G.scalar G.pointMaps hPoint (@a) b (rₚ P S.pointDatum) (r₂ Q S.pointAsSkyscraper)
    hMates G.pointTerminalLevels
  obtain ⟨r, hr⟩ := FiniteStageClosedExtensions.closedPointCompositionEquivariant H.terminalClosed
    d.closed G.terminal G.scalar G.pointMaps (@a) b (rₚ P S.pointDatum) (r₂ Q S.pointAsSkyscraper)
    αₚ αQ hcₚ hcQ hCompat
  let u : K.sheaf ⟶ L.sheaf := u₀
  let v : M.sheaf ⟶ L.sheaf := r ≫ s
  have huv : u.hom = K.ordinary.inv ≫ ((derivedDirectImage j).map f).hom ≫ L.ordinary.hom := by
    change u.hom = 𝟙 _ ≫ _ ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using hu
  have hv : v.hom = M.ordinary.inv ≫ ((closedPointComposition d j (@a) b).hom.app P).hom ≫
      ((derivedDirectImage j).map g).hom ≫ L.ordinary.hom := by
    change r.hom ≫ s.hom = 𝟙 _ ≫ _ ≫ _ ≫ 𝟙 _
    simp only [hr, hs, j, Category.id_comp, Category.comp_id,
      FiniteStageClosedExtensionSpecs.closedPointComposition,
      MinusculeConvolutionSquareSpecs.closedPointComposition]
  have hIso := ordinaryImageSplit D S j K M L u v (@a) b huv hv
  have hCoproduct := @equivariantCofanIsColimit _ _ _ _ K.sheaf M.sheaf L.sheaf u v hIso
  exact ⟨H.first, j, H.firstCoordinates, H.terminalCoordinates, E, K, M, L,
    u, v, @a, b, huv, hv, hIso, hCoproduct⟩

end StageAssembly

section Assembly

open Analytic.IntersectionComplex (complex adjointSquareMap pullbackSquare)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions)
open ClosedSupportBaseChangeSpecs (MateCommutes)
open EquivariantIntersectionComplexesSpecs
open SchubertIntersectionConstructibilitySpecs

private theorem terminalEmbedding (e : surface ≅ TwoStepIntersectionComplexSpecs.X) :
    ∃ j : surface ⟶ Gr, IsClosedEmbedding j ∧ Set.range j = colength 2 ∧
      ∀ p, j p = (e.hom p).val := by
  let j : surface ⟶ Gr :=
    TopCat.ofHom ⟨fun p ↦ (e.hom p).val, continuous_subtype_val.comp e.hom.hom.continuous⟩
  refine ⟨j, (colength_inclusion_closed (m := 2) (Or.inr rfl)).comp
    (TopCat.homeoOfIso e).isClosedEmbedding, ?_, fun _ ↦ rfl⟩
  ext L
  constructor
  · rintro ⟨p, rfl⟩
    exact (e.hom p).property
  · intro hL
    refine ⟨(TopCat.homeoOfIso e).symm ⟨L, hL⟩, ?_⟩
    exact congrArg Subtype.val ((TopCat.homeoOfIso e).apply_symm_apply ⟨L, hL⟩)

private theorem mateCommutesForIdentity {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    {R : BoundedBelow U ⥤ BoundedBelow X} (b : boundedBelowInverseImage i ⊣ R)
    (F : BoundedBelow U)
    (α : (derivedInverseImage e).obj (R.obj F).obj ⟶ (derivedInverseImage p).obj (R.obj F).obj)
    (β : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj)
    (h : α ≫ (adjointSquareMap (pullbackSquare hp) a b F).hom =
      (adjointSquareMap (pullbackSquare he) a b F).hom ≫
        ((derivedDirectImage j).map (ObjectProperty.homMk β)).hom) :
    MateCommutes he hp a b (𝟙 (R.obj F)) α β := by
  let mP := adjointSquareMap (pullbackSquare hp) a b F
  let mA := adjointSquareMap (pullbackSquare he) a b F
  let vβ : (boundedBelowInverseImage v).obj F ⟶ (boundedBelowInverseImage q).obj F :=
    ObjectProperty.homMk β
  let mC := ((derivedDirectImage j).map vβ).hom
  have compare (f : W ⟶ X) {K : BoundedBelow W}
      (m : (boundedBelowInverseImage f).obj (R.obj F) ⟶ K) :
      ((boundedBelowInverseImage f).map (𝟙 (R.obj F)) ≫ m).hom = m.hom := by
    have hm := (boundedBelowInverseImage f).map_id (R.obj F)
    exact congrArg (fun r => r.hom)
      ((congrArg (fun r => r ≫ m) hm).trans (Category.id_comp m))
  exact (congrArg (fun r => α ≫ r) (compare p mP)).trans
    (h.trans (congrArg (fun r => r ≫ mC) (compare e mA)).symm)

/-- The minuscule convolution square with the normalized rational intersection complexes. -/
theorem minusculeConvolutionSquare : MinusculeConvolutionSquareSpecs.Expected.MinusculeConvolutionSquare := by
  obtain ⟨d⟩ := ConvolutionEquivariantSplitting.convolutionEquivariantSplitting
  obtain ⟨⟨a⟩, hAdj, _, c, hIC, _, _⟩ := EquivariantIntersectionComplexes.equivariantIntersectionComplexes
  obtain ⟨b⟩ := hAdj d.closed
  obtain ⟨D, label, hBound, hRange, hDimension⟩ := grassmannianStages c
  obtain ⟨j₁, hClosed₁, hRange₁, hPlane₁⟩ := minusculeLatticeModel
  obtain ⟨A₁, hCutoff₁, hAction₁, α₁, M, hCoordinates₁, hActs₁, hDatum₁⟩ :=
    minusculeICComparison c d j₁ hClosed₁ hRange₁ hPlane₁ (@a) (hIC (@a) minusculePair 2)
  have hBound₂ : OrbitBound twoStepPair 2 := by
    intro i
    fin_cases i <;> decide
  obtain ⟨B, P₂, D₂, hIC₂, β, hβ⟩ := hIC (@a) twoStepPair 2 hBound₂
  obtain ⟨T⟩ := TwoStepICNormalization.terminalICNormalization c (@a) d hBound₂ B P₂ D₂ hIC₂ β hβ
  have hBoundₚ : OrbitBound scalarPair 2 := by
    intro i
    fin_cases i <;> decide
  obtain ⟨C, Pₚ, Dₚ, hICₚ, γ, hγ⟩ := hIC (@a) scalarPair 2 hBoundₚ
  obtain ⟨R⟩ := MinusculeLocalSquare.minusculeLocalSquare c (@a) d hBound₂ B D₂ β T b
    hBoundₚ C Pₚ Dₚ hICₚ γ hγ
  obtain ⟨j₂, hClosed₂, hRange₂, hChart⟩ := terminalEmbedding T.latticeChart
  let M₂ : ICComparison twoStepPair T.action (IntersectionComplex.surface d.point d.closed)
      T.intersectionDatum := {
    bound := hBound₂
    model := T.model
    lattice := T.lattice
    coordinates := T.modelCoordinates
    stratification := P₂
    filtration := D₂
    isIC := hIC₂
    action := B.action
    actionActual := B.actual
    action_commutes := T.modelAction
    datum := β
    adjunctions := @a
    normalized := hβ
    comparison := T.modelIdentification
    equivariant := T.modelIntertwines }
  let Mₚ : ICComparison scalarPair R.pointAction (IntersectionComplex.point d.point) R.pointDatum := {
    bound := hBoundₚ
    model := R.model
    lattice := R.lattice
    coordinates := R.modelCoordinates
    stratification := Pₚ
    filtration := Dₚ
    isIC := hICₚ
    action := C.action
    actionActual := C.actual
    action_commutes := R.modelAction
    datum := γ
    adjunctions := @a
    normalized := hγ
    comparison := R.modelIdentification
    equivariant := R.modelIntertwines }
  let S : LocalSquare c := {
    splitting := d
    minAction := A₁
    terminalAction := T.action
    pointAction := R.pointAction
    minCutoff := hCutoff₁
    terminalCutoff := T.cutoff.le
    pointCutoff := R.pointCutoff.le
    minActs := hAction₁
    terminalActs := T.actsAtTwo
    pointActs := R.pointActs
    minDatum := α₁
    convolutionDatum := R.convolutionDatum
    constantDatum := T.constantDatum
    intersectionDatum := T.intersectionDatum
    pointDatum := R.pointDatum
    minDatumAtTwo := hDatum₁
    convolutionDatumAtTwo := R.convolutionAtTwo
    constantDatumAtTwo := T.constantAtTwo
    minusculeIC := M
    twoStepIC := M₂
    scalarIC := Mₚ
    minusculeCoordinates := fun p ↦ by
      rw [hCoordinates₁ p]
      exact ⟨hRange₁ ▸ Set.mem_range_self p, hPlane₁ p⟩
    terminalCoordinates := fun p ↦ ⟨T.chartCoordinates p ▸ (T.latticeChart.hom p).property,
      T.terminalCoordinates p⟩
    scalarCoordinates := fun p ↦ ⟨R.latticeScalar p, by
      change (T.lattice p.val).val = scalarPoint
      rw [← T.chartCoordinates, show p.val = d.point from p.property]
      exact T.chartScalar⟩
    latticeChart := T.latticeChart
    latticeChartCoordinates := T.chartCoordinates
    constantIdentification := T.constantIdentification
    isGS10Identification := ⟨a (openInclusion (complementOpen {d.point} d.closed)), T.isGS10Identification⟩
    constantIdentificationEquivariant := T.constantIntertwines
    pointAsSkyscraper := R.skyscraperDatum
    pointAsSkyscraperAtTwo := R.skyscraperAtTwo
    pointExtension := ⟨@a, b, extendsAtStageFromMates R.pointInclusionAction (@a)
      (DerivedCategory.Plus.ι.mapIso (((a (closedInclusion {d.point})).rightAdjointUniq b).app _))
      R.directImageMatesAreIso R.directImageMates⟩ }
  have hPlanes₂ (p : surface) : secondPlane p =
      (latticeSubspace 0 2 (T.latticeChart.hom p).val).map twoStepCoordinates.toLinearMap := by
    rw [T.chartCoordinates p]
    exact T.terminalCoordinates p
  let H : SquareSupports S := {
    first := j₁
    terminal := j₂
    firstClosed := hClosed₁
    terminalClosed := hClosed₂
    firstCoordinates := fun p ↦ (hCoordinates₁ p).symm
    terminalCoordinates := fun p ↦ (hChart p).trans (T.chartCoordinates p)
    firstRange := hRange₁
    terminalRange := hRange₂
    firstActs := hActs₁
    terminalActs := by
      intro k hk g p
      change j₂ ((T.action.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
        positiveGLMap 2 g • j₂ p
      rw [hChart, hChart]
      exact terminalLatticeAction c d T.action T.cutoff T.actsAtTwo T.latticeChart.hom hPlanes₂ k hk g p }
  refine ⟨c, D, S, ?_, ?_⟩
  · exact (frameDescentCondition d).mpr (MinusculeFrameDescent.minusculeFrameDescent d)
  · refine extendLocalSquare D label hBound hRange hDimension S H (@a) b R.pointInclusionAction ?_
      R.unitIntertwines R.sectionIntertwines
    intro k hp ht
    exact mateCommutesForIdentity _ _ _ b _ _ _ (R.exactExtensionMates k hp ht)

end Assembly

end RepTheorySurvey.Geometric.MinusculeConvolutionSquare
