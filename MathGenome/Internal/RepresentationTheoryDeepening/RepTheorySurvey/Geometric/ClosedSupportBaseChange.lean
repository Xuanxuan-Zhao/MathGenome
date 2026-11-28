import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.JetEquivariantRestriction
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.ClosedSupportBaseChange

open Analytic Analytic.IntersectionComplex LocalSheaf
open ClosedSupportBaseChangeSpecs
open Analytic.DerivedPullbackPasting.Expected (squareValue)
set_option allowUnsafeReducibility true in
attribute [local reducible] Analytic.DerivedPullbackPasting.Expected.SquareType

open AnalyticAction (projection)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open EquivariantIntersectionComplexesSpecs (Intertwines)

open private derivedClosedImage_supported derivedClosedImageCounit_isIso
  closedEmbedding_reflectsIso squareMap_counit_isIso pullback_supported
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
open private parameterInclusion_closed
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
theorem closedBaseChange : Expected.ClosedBaseChange := by
  intro U X V Y j i e v hi hj h hC a F
  refine closedEmbedding_reflectsIso hj _ ?_ (derivedClosedImage_supported hj _) ?_
  · rw [hC]
    exact pullback_supported e _ _ (derivedClosedImage_supported hi F)
  · exact squareMap_counit_isIso (pullbackSquare h) (a j) (a i) F
      (derivedClosedImageCounit_isIso hj (a j) _) (derivedClosedImageCounit_isIso hi (a i) _)

private theorem parameter_range {U V : TopCat.{0}} (H : AnalyticGroup.{0}) (j : U ⟶ V) :
    Set.range (parameterInclusion H j) =
      (AnalyticAction.projection H V) ⁻¹' Set.range j := by
  ext ⟨g, x⟩
  change (∃ p : H.space × U, (p.1, j p.2) = (g, x)) ↔ ∃ u : U, j u = x
  constructor
  · rintro ⟨⟨_, u⟩, h⟩
    exact ⟨u, congrArg Prod.snd h⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(g, u), rfl⟩

private theorem action_range {U V : TopCat.{0}} {H : AnalyticGroup.{0}} {j : U ⟶ V}
    {C : AnalyticAction H U} {E : AnalyticAction H V}
    (h : parameterInclusion H j ≫ E.act = C.act ≫ j) :
    E.act ⁻¹' Set.range j = (AnalyticAction.projection H V) ⁻¹' Set.range j := by
  have he (g : H.space) (u : U) : E.act (g, j u) = j (C.act (g, u)) :=
    congrArg (fun f : TopCat.of (H.space × U) ⟶ V => f (g, u)) h
  ext ⟨g, x⟩
  change (∃ u, j u = E.act (g, x)) ↔ ∃ u, j u = x
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨C.act (g⁻¹, u), ?_⟩
    rw [← he, hu, ← E.mul_act, inv_mul_cancel, E.one_act]
  · rintro ⟨u, rfl⟩
    exact ⟨C.act (g, u), (he g u).symm⟩

theorem actionProjectionMatesAreIso : Expected.ActionProjectionMatesAreIso := by
  intro U V J j C E hj h a F k hu hv
  let H := J.group k
  let hh := h k hu hv
  have hi := parameterInclusion_closed H hj
  exact ⟨closedBaseChange hj hi hh ((parameter_range H j).trans (action_range hh).symm) a F,
    closedBaseChange hj hi (projectionSquare H j) (parameter_range H j) a F⟩

section SupportedRestriction

open JetEquivariantRestrictionSpecs (ActionSquare Commutes)
open AnalyticAction (multiplyParameters)

private theorem supportedUnit_isIso {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) (a : DerivedAdjunctions.{0}) (F : BoundedBelow X)
    (hF : DerivedSupportedOn (Set.range j) F) : IsIso ((a j).unit.app F) := by
  apply closedEmbedding_reflectsIso hj _ hF (derivedClosedImage_supported hj _)
  haveI := derivedClosedImageCounit_isIso hj (a j) ((boundedBelowInverseImage j).obj F)
  haveI : IsIso ((boundedBelowInverseImage j).map ((a j).unit.app F) ≫
      (a j).counit.app ((boundedBelowInverseImage j).obj F)) := by
    exact (a j).left_triangle_components F ▸ inferInstanceAs (IsIso (𝟙 _))
  exact IsIso.of_isIso_comp_right _ ((a j).counit.app _)

private theorem adjoint_map_bijective {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (S T : C) [IsIso (a.unit.app T)] :
    Function.Bijective (L.map : (S ⟶ T) → (L.obj S ⟶ L.obj T)) := by
  have h (f : S ⟶ T) : a.homEquiv S (L.obj T) (L.map f) = f ≫ a.unit.app T := by
    rw [a.homEquiv_unit]
    exact (a.unit.naturality f).symm
  constructor
  · intro f g e
    apply (cancel_mono (a.unit.app T)).mp
    rw [← h, ← h, e]
  · intro m
    refine ⟨a.homEquiv S (L.obj T) m ≫ inv (a.unit.app T), ?_⟩
    apply (a.homEquiv S (L.obj T)).injective
    rw [h]
    simp

theorem supportedRestrictionBijective : Expected.SupportedRestrictionBijective := by
  intro U X j hj a F G hG
  haveI := supportedUnit_isIso hj a G hG
  have h := adjoint_map_bijective (a j) F G
  constructor
  · intro f g hfg
    have he := h.1 (ObjectProperty.hom_ext _ hfg :
      (boundedBelowInverseImage j).map (ObjectProperty.homMk f : F ⟶ G) =
      (boundedBelowInverseImage j).map (ObjectProperty.homMk g : F ⟶ G))
    exact congrArg (fun f => f.hom) he
  · intro f
    obtain ⟨g, hg⟩ := h.2 (ObjectProperty.homMk f)
    exact ⟨g.hom, congrArg (fun f => f.hom) hg⟩

private theorem restrictedIso_datum {U X : TopCat.{0}} {J : JetSystem.{0}} {j : U ⟶ X}
    {C : JetAction J U} {E : JetAction J X} (hj : IsClosedEmbedding j)
    (h : Intertwines C E j) (hle : C.cutoff ≤ E.cutoff)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow U) (G : BoundedBelow X)
    (hG : DerivedSupportedOn (Set.range j) G)
    (c : F ≅ (boundedBelowInverseImage j).obj G) (α : C.Equivariance F.obj) :
    ∃ β : E.Equivariance G.obj, ∀ k (hk : E.cutoff ≤ k),
      Commutes (h k (hle.trans hk) hk) (α.datum k (hle.trans hk)) (β.datum k hk) c.hom.hom := by
  have hbij {W : TopCat.{0}} (f : W ⟶ X) {V : TopCat.{0}} (g : V ⟶ W)
      (hg : IsClosedEmbedding g) (hg' : Set.range g = f ⁻¹' Set.range j)
      (A' : BoundedBelow W) :
      Function.Bijective ((derivedInverseImage g).map :
        (A'.obj ⟶ ((boundedBelowInverseImage f).obj G).obj) → _) :=
    supportedRestrictionBijective hg a A' _ (hg' ▸ pullback_supported f _ G hG)
  have hid := hbij (𝟙 X) j hj (Set.preimage_id.symm) ((boundedBelowInverseImage (𝟙 X)).obj G)
  have hpar (k : ℕ) (hk : E.cutoff ≤ k) :
      ∀ (S T : Derived (AnalyticAction.Parameters (J.group k) X)),
        (S = (derivedInverseImage (E.action k hk).act).obj G.obj ∨
          S = (derivedInverseImage (projection (J.group k) X)).obj G.obj) →
        (T = (derivedInverseImage (E.action k hk).act).obj G.obj ∨
          T = (derivedInverseImage (projection (J.group k) X)).obj G.obj) →
        Function.Bijective ((derivedInverseImage (parameterInclusion (J.group k) j)).map :
          (S ⟶ T) → _) := by
    let H := J.group k
    let p := projection H X
    let e := (E.action k hk).act
    let i := parameterInclusion H j
    have hi : IsClosedEmbedding i := parameterInclusion_closed H hj
    have hp := parameter_range H j
    have he := hp.trans (action_range (h k (hle.trans hk) hk)).symm
    intro S T hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · exact hbij e i hi he ((boundedBelowInverseImage e).obj G)
    · exact hbij p i hi hp ((boundedBelowInverseImage e).obj G)
    · exact hbij e i hi he ((boundedBelowInverseImage p).obj G)
    · exact hbij p i hi hp ((boundedBelowInverseImage p).obj G)
  have hmul (k : ℕ) (hk : E.cutoff ≤ k) :
      Function.Injective ((derivedInverseImage
        (parameterInclusion (J.group k) (parameterInclusion (J.group k) j))).map :
        ((derivedInverseImage (multiplyParameters (J.group k) X ≫ (E.action k hk).act)).obj G.obj ⟶
          (derivedInverseImage (multiplyParameters (J.group k) X ≫ projection (J.group k) X)).obj G.obj)
        → _) := by
    let H := J.group k
    let p := projection H X
    let i := parameterInclusion H j
    let i₂ := parameterInclusion H i
    have hh : Set.range i₂ = (multiplyParameters H X ≫ p) ⁻¹' Set.range j := by
      rw [parameter_range H i, parameter_range H j]
      rfl
    exact (hbij (multiplyParameters H X ≫ p) i₂
      (parameterInclusion_closed H (parameterInclusion_closed H hj)) hh
      ((boundedBelowInverseImage (multiplyParameters H X ≫ (E.action k hk).act)).obj G)).1
  obtain ⟨β, hb, _⟩ := JetEquivariantRestriction.equivarianceLifting j hle
    (fun k hk => h k (hle.trans hk) hk) (DerivedCategory.Plus.ι.mapIso c) α hid.1 hpar hmul
  exact ⟨β, hb⟩

private theorem transposeMate {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (σ : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R)
    {F : D} {G : B} (c : G ⟶ R.obj F) :
    (a.homEquiv (E.obj G) (V.obj F)).symm (E.map c ≫ adjointSquareMap σ a b F) =
      σ.hom.app G ≫ V.map (K.map c ≫ b.counit.app F) := by
  rw [a.homEquiv_naturality_left_symm, adjointSquareMap, Equiv.symm_apply_apply,
    ← Category.assoc]
  change ((E ⋙ J).map c ≫ σ.hom.app (R.obj F)) ≫ _ = _
  rw [σ.hom.naturality c, Functor.map_comp, Category.assoc]
  rfl

set_option maxHeartbeats 600000 in
theorem mateEquationIff : Expected.MateEquationIff := by
  intro U X V W i j e p v q he hp a R b F G c α β
  unfold MateCommutes
  let L := boundedBelowInverseImage j
  let z : (boundedBelowInverseImage e).obj G ⟶ (boundedBelowInverseImage p).obj G :=
    ObjectProperty.homMk α
  let w : (boundedBelowInverseImage v).obj F ⟶ (boundedBelowInverseImage q).obj F :=
    ObjectProperty.homMk β
  let cp := (boundedBelowInverseImage p).map c ≫ adjointSquareMap (pullbackSquare hp) a b F
  let ce := (boundedBelowInverseImage e).map c ≫ adjointSquareMap (pullbackSquare he) a b F
  let τ := (boundedBelowInverseImage i).map c ≫ b.counit.app F
  let cP := (pullbackSquare hp).hom.app G ≫ (boundedBelowInverseImage q).map τ
  let cA := (pullbackSquare he).hom.app G ≫ (boundedBelowInverseImage v).map τ
  have hcp : (a.homEquiv _ _).symm cp = cP := transposeMate (pullbackSquare hp) a b c
  have hce : (a.homEquiv _ _).symm ce = cA := transposeMate (pullbackSquare he) a b c
  calc
    _ ↔ z ≫ cp = ce ≫ (derivedDirectImage j).map w :=
      ⟨ObjectProperty.hom_ext _, congrArg (DerivedCategory.Plus.ι (C := Sheaves W)).map⟩
    _ ↔ L.map z ≫ cP = cA ≫ w := by
      rw [← hcp, ← hce]
      exact (a.homEquiv_naturality_right_square_iff z cp ce w).symm
    _ ↔ _ := by
      have hhe := DerivedPullbackPasting.squareBoundedBelowCompatibility he G
      have hhp := DerivedPullbackPasting.squareBoundedBelowCompatibility hp G
      constructor
      · intro h
        have hh := congrArg (fun f : (L.obj ((boundedBelowInverseImage e).obj G) ⟶
            (boundedBelowInverseImage q).obj F) => f.hom) h
        simpa only [cP, cA, ObjectProperty.FullSubcategory.comp_hom, hhe, hhp,
          Category.assoc] using! hh
      · intro h
        apply ObjectProperty.hom_ext
        simp only [cP, cA, ObjectProperty.FullSubcategory.comp_hom, hhe, hhp, Category.assoc]
        exact h

theorem derivedDirectImageMateEquationIff : Expected.DerivedDirectImageMateEquationIff := by
  intro U X V W i j e p v q he hp a F G c α β
  exact mateEquationIff he hp (a j) (a i) c α β

open private coefficientIso restrictsTo_iff commutes_iff_restrictsTo
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.JetEquivariantRestriction

private theorem squareRestrictionOfCommutes {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    {C : AnalyticAction H U} {E : AnalyticAction H X} {j : U ⟶ X}
    (he : ActionSquare C E j) {K : Derived U} {G : Derived X}
    (α : C.Equivariance K) (β : E.Equivariance G)
    (d : K ≅ (derivedInverseImage j).obj G)
    (hc : Commutes he α β d.hom) :
    SquareRestriction he (projectionSquare H j) d.inv β.iso.hom α.iso.hom := by
  have hh := (commutes_iff_restrictsTo he α β d).mp hc
  have hh' := (restrictsTo_iff he (projectionSquare H j) d β.iso.hom α.iso.hom).mp hh
  simpa only [SquareRestriction, coefficientIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, Category.assoc] using! hh'

private theorem mateCommutesAtJet {U X : TopCat.{0}} {j : U ⟶ X} {J : JetSystem.{0}}
    {C : JetAction J U} {E : JetAction J X} (h : Intertwines C E j) (a : DerivedAdjunctions.{0})
    {K : BoundedBelow U} {G : BoundedBelow X} (c : G ⟶ (derivedDirectImage j).obj K)
    (α : C.Equivariance K.obj) (β : E.Equivariance G.obj)
    (m : ∀ k hu hv, MateCommutes (h k hu hv) (projectionSquare (J.group k) j)
      (a (parameterInclusion (J.group k) j)) (a j) c
      (β.datum k hv).iso.hom (α.datum k hu).iso.hom) :
    AgreesWithMates h a α β c.hom := by
  intro k hu hv
  have hm := m k hu hv
  simp only [MateCommutes, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc] at hm
  exact hm

theorem stageDatum : Expected.StageDatum := by
  intro U X V Y i j e v J C E hi hj hs hr h hle a F α
  dsimp only
  let G := (boundedBelowInverseImage e).obj ((derivedDirectImage i).obj F)
  let K := (boundedBelowInverseImage v).obj F
  let c := directImageComparison hs (a j) (a i) F
  let ε := (boundedBelowInverseImage j).map c ≫ (a j).counit.app K
  haveI : IsIso c := closedBaseChange hi hj hs hr a F
  haveI : IsIso ((a j).counit.app K) := derivedClosedImageCounit_isIso hj (a j) K
  haveI : IsIso ε := by dsimp only [ε]; infer_instance
  have hG : DerivedSupportedOn (Set.range j) G :=
    hr ▸ pullback_supported e _ _ (derivedClosedImage_supported hi F)
  let d := (asIso ε).symm
  obtain ⟨β, hb⟩ := restrictedIso_datum hj h hle a K G hG d α
  refine ⟨β, inferInstance, actionProjectionMatesAreIso hj h a K, ?_⟩
  apply mateCommutesAtJet h a c α β
  intro k hu hv
  let H := J.group k
  let he := h k hu hv
  let hp := projectionSquare H j
  have hh : SquareRestriction he hp ε.hom (β.datum k hv).iso.hom (α.datum k hu).iso.hom :=
    squareRestrictionOfCommutes he (α.datum k hu) (β.datum k hv)
      ((DerivedCategory.Plus.ι (C := Sheaves U)).mapIso d) (hb k hv)
  exact (derivedDirectImageMateEquationIff he hp a c _ _).mpr hh

end SupportedRestriction

end RepTheorySurvey.Geometric.ClosedSupportBaseChange
