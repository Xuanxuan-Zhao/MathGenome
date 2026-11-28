import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SupportIntersectionJetDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SupportIntersectionEquivariance
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace RepTheorySurvey.Geometric.SupportIntersectionJetDescent

open Analytic Analytic.AnalyticAction
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)
open EquivariantIntersectionComplexesSpecs (Intertwines IntertwinesPullback restrictedArrow)
open FiniteStageClosedExtensionSpecs (SupportIntersections)

open private compositionAt pullbackMorphism_eq pullbackMorphism_paste pullbackMorphism_congr
  pullbackMorphism_comp RestrictsTo RestrictsTo.pullback restrictionComparison
  restrictionComparison_paste restrictionComparison_paste_assoc
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private restrictDatum squareIso_hom squareIso_restrictsTo restriction_unique
  squareIso_naturality squareIso_transition intersectionComparison_underlying
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SupportIntersectionEquivariance

private theorem inverseImage_map_injective {W V : TopCat.{0}} {q : W ⟶ V}
    (hq : (boundedBelowInverseImage q).FullyFaithful)
    {F G : BoundedBelow V} {f g : F.obj ⟶ G.obj}
    (h : (derivedInverseImage q).map f = (derivedInverseImage q).map g) : f = g := by
  have hh : (boundedBelowInverseImage q).map (ObjectProperty.homMk f : F ⟶ G) =
      (boundedBelowInverseImage q).map (ObjectProperty.homMk g : F ⟶ G) :=
    ObjectProperty.hom_ext _ h
  exact congrArg (fun v : F ⟶ G => v.hom) (hq.map_injective hh)

private theorem pullback_injective {W V U : TopCat.{0}} {q : W ⟶ V}
    (hq : (boundedBelowInverseImage q).FullyFaithful)
    {a p : V ⟶ U} {a' p' : W ⟶ U} (ha : q ≫ a = a') (hp : q ≫ p = p')
    (F : BoundedBelow U)
    {f g : (derivedInverseImage a).obj F.obj ⟶ (derivedInverseImage p).obj F.obj}
    (h : pullbackMorphism q ha hp f = pullbackMorphism q ha hp g) : f = g := by
  simp only [pullbackMorphism_eq] at h
  exact inverseImage_map_injective hq (F := (boundedBelowInverseImage a).obj F)
    (G := (boundedBelowInverseImage p).obj F)
    ((cancel_mono _).mp ((cancel_epi _).mp h))

/-- Descend an isomorphism between the inverse images along the two factored maps. -/
private def descendIso {W V U : TopCat.{0}} {q : W ⟶ V}
    (hq : (boundedBelowInverseImage q).FullyFaithful)
    {a p : V ⟶ U} {a' p' : W ⟶ U} (ha : q ≫ a = a') (hp : q ≫ p = p')
    (F : BoundedBelow U) (e : (derivedInverseImage a').obj F.obj ≅
      (derivedInverseImage p').obj F.obj) :
    (derivedInverseImage a).obj F.obj ≅ (derivedInverseImage p).obj F.obj :=
  let C := ClosedSupportPullbackPasting.pullbackComparisonAt q a ha F
  let D := ClosedSupportPullbackPasting.pullbackComparisonAt q p hp F
  let E : (boundedBelowInverseImage a').obj F ≅ (boundedBelowInverseImage p').obj F :=
    ObjectProperty.isoMk _ (X := (boundedBelowInverseImage a').obj F)
      (Y := (boundedBelowInverseImage p').obj F) e
  (DerivedCategory.Plus.ι (C := Sheaves V)).mapIso
    (hq.preimageIso (C.symm ≪≫ E ≪≫ D))

private theorem pullback_descendIso {W V U : TopCat.{0}} {q : W ⟶ V}
    (hq : (boundedBelowInverseImage q).FullyFaithful)
    {a p : V ⟶ U} {a' p' : W ⟶ U} (ha : q ≫ a = a') (hp : q ≫ p = p')
    (F : BoundedBelow U) (e : (derivedInverseImage a').obj F.obj ≅
      (derivedInverseImage p').obj F.obj) :
    pullbackMorphism q ha hp (descendIso hq ha hp F e).hom = e.hom := by
  let C := ClosedSupportPullbackPasting.pullbackComparisonAt q a ha F
  let D := ClosedSupportPullbackPasting.pullbackComparisonAt q p hp F
  let eBelow : (boundedBelowInverseImage a').obj F ≅ (boundedBelowInverseImage p').obj F :=
    ObjectProperty.isoMk _ (X := (boundedBelowInverseImage a').obj F)
      (Y := (boundedBelowInverseImage p').obj F) e
  let E := C.symm ≪≫ eBelow ≪≫ D
  have h := (DerivedCategory.Plus.ι (C := Sheaves W)).congr_map (hq.map_preimage E.hom)
  change (derivedInverseImage q).map (descendIso hq ha hp F e).hom =
    C.inv.hom ≫ e.hom ≫ D.hom.hom at h
  have hC := ClosedSupportPullbackPasting.pullbackComparisonAtUnderlying q a ha F
  have hD := ClosedSupportPullbackPasting.pullbackComparisonAtUnderlying q p hp F
  change (DerivedCategory.Plus.ι (C := Sheaves W)).mapIso C = compositionAt q a ha F.obj at hC
  change (DerivedCategory.Plus.ι (C := Sheaves W)).mapIso D = compositionAt q p hp F.obj at hD
  rw [pullbackMorphism_eq, h, ← hC, ← hD]
  change C.hom.hom ≫ (C.inv.hom ≫ e.hom ≫ D.hom.hom) ≫ D.inv.hom = e.hom
  have hc : C.hom.hom ≫ C.inv.hom = 𝟙 _ :=
    (DerivedCategory.Plus.ι (C := Sheaves W)).congr_map C.hom_inv_id
  have hd : D.hom.hom ≫ D.inv.hom = 𝟙 _ :=
    (DerivedCategory.Plus.ι (C := Sheaves W)).congr_map D.hom_inv_id
  simp only [Category.assoc]
  rw [reassoc_of% hc, hd]
  exact Category.comp_id e.hom

private theorem pullback_commutes {W V W' V' U : TopCat.{0}}
    {q : W ⟶ V} {q' : W' ⟶ V'} {s : V' ⟶ V} {t : W' ⟶ W}
    (h : t ≫ q = q' ≫ s)
    {a p : V ⟶ U} {a₁ p₁ : W ⟶ U} {a₂ p₂ : V' ⟶ U} {a₃ p₃ : W' ⟶ U}
    (ha : q ≫ a = a₁) (hp : q ≫ p = p₁)
    (hb : s ≫ a = a₂) (hr : s ≫ p = p₂)
    (hc : t ≫ a₁ = a₃) (hu : t ≫ p₁ = p₃)
    (hd : q' ≫ a₂ = a₃) (hv : q' ≫ p₂ = p₃)
    {F : Derived U} (f : (derivedInverseImage a).obj F ⟶ (derivedInverseImage p).obj F) :
    pullbackMorphism t hc hu (pullbackMorphism q ha hp f) =
      pullbackMorphism q' hd hv (pullbackMorphism s hb hr f) := by
  rw [DerivedPullbackPasting.pullbackSuccessive, DerivedPullbackPasting.pullbackSuccessive]
  exact pullbackMorphism_congr h _ _ _ _ f

section Jets

variable {J : JetSystem.{0}} {U Y : TopCat.{0}} {i : U ⟶ Y}
variable {C : JetAction J U} {S : JetAction J Y}

private abbrev single {k l : ℕ} (h : k ≤ l) (X : TopCat.{0}) :=
  J.parameterMap h (𝟙 X)

private abbrev double {k l : ℕ} (h : k ≤ l) (X : TopCat.{0}) :=
  J.parameterMap h (J.parameterMap h (𝟙 X))

private theorem single_comp {k l m : ℕ} (h : k ≤ l) (j : l ≤ m) (X : TopCat.{0}) :
    single (J := J) j X ≫ single (J := J) h X = single (J := J) (h.trans j) X :=
  TopCat.ext fun p => Prod.ext
    (congrArg (fun f : (J.group m).space ⟶ (J.group k).space => f p.1)
      (J.truncate_comp h j)) rfl

private theorem single_projection {k l : ℕ} (h : k ≤ l) (X : TopCat.{0}) :
    single (J := J) h X ≫ projection (J.group k) X = projection (J.group l) X :=
  TopCat.ext (fun _ => rfl)

private theorem single_inclusion {k l : ℕ} (h : k ≤ l) (f : U ⟶ Y) :
    parameterInclusion (J.group l) f ≫ single (J := J) h Y =
      single (J := J) h U ≫ parameterInclusion (J.group k) f :=
  TopCat.ext (fun _ => rfl)

variable (w : Intertwines C S i) {F : BoundedBelow Y} (α : S.Equivariance F.obj)

private abbrev highDatum (k : ℕ) (hk : C.cutoff ≤ k) (hs : S.cutoff ≤ k) :=
  restrictDatum (S.action k hs) (C.action k hk) (w k hk hs) (α.datum k hs)

private theorem highDatum_hom (k : ℕ) (hk : C.cutoff ≤ k) (hs : S.cutoff ≤ k) :
    (highDatum w α k hk hs).iso.hom = restrictedArrow w α k hk hs :=
  squareIso_hom (w k hk hs) (projectionSquare (J.group k) i) (α.datum k hs).iso

private theorem highDatum_compat {k l : ℕ} (hk : C.cutoff ≤ k) (hs : S.cutoff ≤ k)
    (h : k ≤ l) :
    pullbackMorphism (single (J := J) h U) (C.factors hk h) (single_projection h U)
      (highDatum w α k hk hs).iso.hom = (highDatum w α l (hk.trans h) (hs.trans h)).iso.hom := by
  have hr := RestrictsTo.pullback (single (J := J) h Y) (single (J := J) h U)
    (single_inclusion h i) (S.factors hs h) (single_projection h Y) (C.factors hk h)
    (single_projection h U) (w l (hk.trans h) (hs.trans h))
    (projectionSquare (J.group l) i)
    (squareIso_restrictsTo (w k hk hs) (projectionSquare (J.group k) i) (α.datum k hs).iso)
  rw [α.compatibility hs h] at hr
  exact restriction_unique hr
    (squareIso_restrictsTo (w l (hk.trans h) (hs.trans h))
      (projectionSquare (J.group l) i) (α.datum l (hs.trans h)).iso)

variable
  (oneFF : ∀ {k l : ℕ} (h : k ≤ l) (X : TopCat.{0}),
    Nonempty ((boundedBelowInverseImage (single (J := J) h X)).FullyFaithful))

private def levelIso (k : ℕ) (hk : C.cutoff ≤ k) :
    (derivedInverseImage (C.action k hk).act).obj ((derivedInverseImage i).obj F.obj) ≅
      (derivedInverseImage (projection (J.group k) U)).obj
        ((derivedInverseImage i).obj F.obj) :=
  let h := Nat.le_max_left k S.cutoff
  descendIso (Classical.choice (oneFF h U)) (C.factors hk h) (single_projection h U)
    ((boundedBelowInverseImage i).obj F)
    (highDatum w α (max k S.cutoff) (hk.trans h) (Nat.le_max_right k S.cutoff)).iso

private theorem levelIso_agrees {k l : ℕ} (hk : C.cutoff ≤ k) (h : k ≤ l) (hs : S.cutoff ≤ l) :
    pullbackMorphism (single (J := J) h U) (C.factors hk h) (single_projection h U)
      (levelIso w α oneFF k hk).hom = (highDatum w α l (hk.trans h) hs).iso.hom := by
  let h₀ := Nat.le_max_left k S.cutoff
  let h₁ : max k S.cutoff ≤ l := max_le h hs
  have hm := pullback_descendIso (Classical.choice (oneFF h₀ U)) (C.factors hk h₀)
    (single_projection h₀ U) ((boundedBelowInverseImage i).obj F)
    (highDatum w α (max k S.cutoff) (hk.trans h₀) (Nat.le_max_right k S.cutoff)).iso
  change pullbackMorphism (single (J := J) h₀ U) (C.factors hk h₀) (single_projection h₀ U)
    (levelIso w α oneFF k hk).hom = _ at hm
  have hp := pullbackMorphism_paste
    (single (J := J) h₁ U) (single (J := J) h₀ U)
    (C.factors hk h₀) (single_projection h₀ U) (C.factors (hk.trans h₀) h₁)
    (single_projection h₁ U)
    ((congrArg (· ≫ (C.action k hk).act) (single_comp h₀ h₁ U)).trans (C.factors hk h))
    ((congrArg (· ≫ projection (J.group k) U) (single_comp h₀ h₁ U)).trans
      (single_projection h U)) (levelIso w α oneFF k hk).hom
  rw [hm] at hp
  exact (pullbackMorphism_congr (single_comp h₀ h₁ U).symm _ _ _ _ _).trans
    (hp.symm.trans (highDatum_compat w α (hk.trans h₀) (Nat.le_max_right k S.cutoff) h₁))

private theorem levelIso_at_common (k : ℕ) (hk : C.cutoff ≤ k) (hs : S.cutoff ≤ k) :
    (levelIso w α oneFF k hk).hom = (highDatum w α k hk hs).iso.hom := by
  have h := Nat.le_max_left k S.cutoff
  apply pullback_injective (Classical.choice (oneFF h U))
    (C.factors hk h) (single_projection h U) ((boundedBelowInverseImage i).obj F)
  rw [levelIso_agrees w α oneFF hk h (Nat.le_max_right k S.cutoff),
    highDatum_compat w α hk hs h]

private theorem levelIso_identity (k : ℕ) (hk : C.cutoff ≤ k) :
    pullbackMorphism (identitySection (J.group k) U) (identity_act (C.action k hk))
      identity_projection (levelIso w α oneFF k hk).hom = 𝟙 _ := by
  let l := max k S.cutoff
  let h : k ≤ l := Nat.le_max_left k S.cutoff
  let hs : S.cutoff ≤ l := Nat.le_max_right k S.cutoff
  have hSection : identitySection (J.group l) U ≫ single (J := J) h U =
      𝟙 U ≫ identitySection (J.group k) U :=
    TopCat.ext fun _ => Prod.ext (J.truncate_one h) rfl
  have hh := pullback_commutes hSection (C.factors hk h) (single_projection h U)
    (identity_act (C.action k hk)) identity_projection (identity_act (C.action l (hk.trans h)))
    identity_projection (Category.id_comp (𝟙 U)) (Category.id_comp (𝟙 U))
    (levelIso w α oneFF k hk).hom
  rw [levelIso_agrees w α oneFF hk h hs, (highDatum w α l (hk.trans h) hs).identity,
    DerivedPullbackPasting.pullbackIdentityMap] at hh
  exact hh.symm

variable
  (twoFF : ∀ {k l : ℕ} (h : k ≤ l) (X : TopCat.{0}),
    Nonempty ((boundedBelowInverseImage (double (J := J) h X)).FullyFaithful))

include twoFF in
private theorem levelIso_multiplication (k : ℕ) (hk : C.cutoff ≤ k) :
    let c := C.action k hk
    let r := (levelIso w α oneFF k hk).hom
    pullbackMorphism (multiplyParameters (J.group k) U) rfl rfl r =
      pullbackMorphism (firstAfterSecond c) (multiply_act c) (first_projection c) r ≫
      pullbackMorphism (secondParameter (J.group k) U) rfl multiply_projection r := by
  dsimp only
  let l := max k S.cutoff
  let h : k ≤ l := Nat.le_max_left k S.cutoff
  let hs : S.cutoff ≤ l := Nat.le_max_right k S.cutoff
  let ak := (C.action k hk).act
  let al := (C.action l (hk.trans h)).act
  let pk := projection (J.group k) U
  let pl := projection (J.group l) U
  let mk := multiplyParameters (J.group k) U
  let ml := multiplyParameters (J.group l) U
  let fk := firstAfterSecond (C.action k hk)
  let fl := firstAfterSecond (C.action l (hk.trans h))
  let sk := secondParameter (J.group k) U
  let sl := secondParameter (J.group l) U
  let q := single (J := J) h U
  let q₂ := double (J := J) h U
  have hm : ml ≫ q = q₂ ≫ mk :=
    TopCat.ext fun z => Prod.ext (J.truncate_mul h z.1 z.2.1) rfl
  have hf : fl ≫ q = q₂ ≫ fk :=
    TopCat.ext fun z => Prod.ext rfl
      (congrArg (fun f : Parameters (J.group l) U ⟶ U => f z.2) (C.factors hk h)).symm
  have ht : sl ≫ q = q₂ ≫ sk := TopCat.ext fun _ => rfl
  have ha : q₂ ≫ (mk ≫ ak) = ml ≫ al := by
    rw [← Category.assoc, ← hm, Category.assoc]
    exact congrArg (ml ≫ ·) (C.factors hk h)
  have hp : q₂ ≫ (mk ≫ pk) = ml ≫ pl := by
    rw [← Category.assoc, ← hm, Category.assoc]
    exact congrArg (ml ≫ ·) (single_projection h U)
  have hb : q₂ ≫ (sk ≫ ak) = sl ≫ al := by
    rw [← Category.assoc, ← ht, Category.assoc]
    exact congrArg (sl ≫ ·) (C.factors hk h)
  let r := (levelIso w α oneFF k hk).hom
  let rl := highDatum w α l (hk.trans h) hs
  have hr := levelIso_agrees w α oneFF hk h hs
  have hm' := pullback_commutes hm (C.factors hk h) (single_projection h U)
    rfl rfl rfl rfl ha hp r
  have hf' := pullback_commutes hf (C.factors hk h) (single_projection h U)
    (multiply_act (C.action k hk)) (first_projection (C.action k hk))
    (multiply_act (C.action l (hk.trans h))) (first_projection (C.action l (hk.trans h))) ha hb r
  have ht' := pullback_commutes ht (C.factors hk h) (single_projection h U)
    rfl (multiply_projection (H := J.group k) (X := U))
    rfl (multiply_projection (H := J.group l) (X := U)) hb hp r
  rw [hr] at hm' hf' ht'
  apply pullback_injective (Classical.choice (twoFF h U)) ha hp ((boundedBelowInverseImage i).obj F)
  rw [pullbackMorphism_comp q₂ ha hb hp, ← hm', ← hf', ← ht']
  exact rl.multiplication

private theorem levelIso_compat {k l : ℕ} (hk : C.cutoff ≤ k) (h : k ≤ l) :
    pullbackMorphism (single (J := J) h U) (C.factors hk h) (single_projection h U)
      (levelIso w α oneFF k hk).hom = (levelIso w α oneFF l (hk.trans h)).hom := by
  let m := max l S.cutoff
  let j : l ≤ m := Nat.le_max_left l S.cutoff
  let hs : S.cutoff ≤ m := Nat.le_max_right l S.cutoff
  apply pullback_injective (Classical.choice (oneFF j U))
    (C.factors (hk.trans h) j) (single_projection j U) ((boundedBelowInverseImage i).obj F)
  rw [levelIso_agrees w α oneFF (hk.trans h) j hs, DerivedPullbackPasting.pullbackSuccessive]
  exact (pullbackMorphism_congr (single_comp h j U) _ _ _ _ _).trans
    (levelIso_agrees w α oneFF hk (h.trans j) hs)

private def descendEquivariance : C.Equivariance ((derivedInverseImage i).obj F.obj) where
  datum k hk :=
    ⟨levelIso w α oneFF k hk, levelIso_identity w α oneFF k hk,
      levelIso_multiplication w α oneFF twoFF k hk⟩
  compatibility := levelIso_compat w α oneFF

end Jets

/-- A compatible parameter change reflects the restriction equation when its
inverse image on the small parameter space is faithful. -/
private theorem restrictsTo_of_pullback {U X V W V' W' : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {j' : V' ⟶ W'} {k : W' ⟶ W} {l : V' ⟶ V}
    (hFF : (boundedBelowInverseImage l).FullyFaithful) (hl : j' ≫ k = l ≫ j)
    {e p : W ⟶ X} {v q : V ⟶ U} {e' p' : W' ⟶ X} {v' q' : V' ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (hke : k ≫ e = e') (hkp : k ≫ p = p') (hlv : l ≫ v = v') (hlq : l ≫ q = q')
    (he' : j' ≫ e' = v' ≫ i) (hp' : j' ≫ p' = q' ≫ i)
    {G : BoundedBelow X} {F : BoundedBelow U} {ε : (derivedInverseImage i).obj G.obj ⟶ F.obj}
    {a : (derivedInverseImage e).obj G.obj ⟶ (derivedInverseImage p).obj G.obj}
    {b : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj}
    (h : RestrictsTo i j' he' hp' ε (pullbackMorphism k hke hkp a)
      (pullbackMorphism l hlv hlq b)) :
    RestrictsTo i j he hp ε a b := by
  have hv : l ≫ (v ≫ i) = v' ≫ i := congrArg (· ≫ i) hlv
  have hq : l ≫ (q ≫ i) = q' ≫ i := congrArg (· ≫ i) hlq
  have hc := pullback_commutes hl.symm he hp hke hkp hv hq he' hp' a
  unfold RestrictsTo at h ⊢
  rw [← hc] at h
  have hh := congrArg (· ≫ (compositionAt l q hlq F.obj).hom) h
  simp only [pullbackMorphism_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [← restrictionComparison_paste i q l hlq hq ε, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, ← restrictionComparison_paste_assoc i v l hlv hv ε,
    ← Functor.map_comp] at hh
  rw [pullbackMorphism_eq]
  exact inverseImage_map_injective hFF (F := (boundedBelowInverseImage (v ≫ i)).obj G)
    (G := (boundedBelowInverseImage q).obj F) ((cancel_epi _).mp hh)

private theorem restriction_comparison_iff {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G : Derived X} {F : Derived U} (c : F ≅ (derivedInverseImage i).obj G)
    (a : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (b : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F) :
    (derivedInverseImage v).map c.hom ≫
        ((derivedInverseImageComposition v i).inv.app G ≫ pullbackMorphism j he hp a ≫
          (derivedInverseImageComposition q i).hom.app G) =
      b ≫ (derivedInverseImage q).map c.hom ↔
      RestrictsTo i j he hp c.inv a b := by
  let A := (derivedInverseImageComposition v i).app G
  let P := (derivedInverseImageComposition q i).app G
  let V := (derivedInverseImage v).mapIso c
  let Q := (derivedInverseImage q).mapIso c
  let d := pullbackMorphism j he hp a
  change V.hom ≫ (A.inv ≫ d ≫ P.hom) = b ≫ Q.hom ↔
    d ≫ (P.hom ≫ Q.inv) = (A.hom ≫ V.inv) ≫ b
  constructor
  · intro h
    calc
      _ = A.hom ≫ V.inv ≫ (V.hom ≫ (A.inv ≫ d ≫ P.hom)) ≫ Q.inv := by simp
      _ = _ := by rw [h]; simp
  · intro h
    calc
      _ = V.hom ≫ A.inv ≫ (d ≫ (P.hom ≫ Q.inv)) ≫ Q.hom := by simp
      _ = _ := by rw [h]; simp

private theorem compositionAt_naturality {W V U : TopCat.{0}} {q : W ⟶ V}
    {a : V ⟶ U} {a' : W ⟶ U} (ha : q ≫ a = a') {F G : Derived U} (f : F ⟶ G) :
    (derivedInverseImage a').map f ≫ (compositionAt q a ha G).hom =
      (compositionAt q a ha F).hom ≫ (derivedInverseImage q).map ((derivedInverseImage a).map f) := by
  subst a'
  simpa only [compositionAt, eqToIso_refl, Iso.refl_trans, Iso.app_hom, Functor.comp_map] using
    (derivedInverseImageComposition q a).hom.naturality f

private theorem naturality_of_pullback {W V U : TopCat.{0}} {t : W ⟶ V}
    (hFF : (boundedBelowInverseImage t).FullyFaithful)
    {a p : V ⟶ U} {a' p' : W ⟶ U} (ha : t ≫ a = a') (hp : t ≫ p = p')
    {F G : BoundedBelow U} (f : F.obj ⟶ G.obj)
    (r : (derivedInverseImage a).obj F.obj ⟶ (derivedInverseImage p).obj F.obj)
    (s : (derivedInverseImage a).obj G.obj ⟶ (derivedInverseImage p).obj G.obj)
    (h : (derivedInverseImage a').map f ≫ pullbackMorphism t ha hp s =
      pullbackMorphism t ha hp r ≫ (derivedInverseImage p').map f) :
    (derivedInverseImage a).map f ≫ s = r ≫ (derivedInverseImage p).map f := by
  have hh := congrArg (· ≫ (compositionAt t p hp G.obj).hom) h
  simp only [pullbackMorphism_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [reassoc_of% (compositionAt_naturality ha f), ← Functor.map_comp,
    compositionAt_naturality hp f, Iso.inv_hom_id_assoc, ← Functor.map_comp] at hh
  exact inverseImage_map_injective hFF (F := (boundedBelowInverseImage a).obj F)
    (G := (boundedBelowInverseImage p).obj G) ((cancel_epi _).mp hh)

section Intersections

variable {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
variable {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
variable (I : SupportIntersections B i S)
variable
  (oneFF : ∀ {k l : ℕ} (h : k ≤ l) (U : TopCat.{0}),
    Nonempty ((boundedBelowInverseImage (single (J := J) h U)).FullyFaithful))
  (twoFF : ∀ {k l : ℕ} (h : k ≤ l) (U : TopCat.{0}),
    Nonempty ((boundedBelowInverseImage (double (J := J) h U)).FullyFaithful))
variable (F : BoundedBelow Y) (α : S.Equivariance F.obj)

private theorem levelIso_transition {n m : ℕ} (t : n ≤ m) (k : ℕ)
    (hn : (I.action n).cutoff ≤ k) (hm : (I.action m).cutoff ≤ k) :
    let c := compositionAt (I.transition t) (I.intoSupport m) (I.transition_support t) F.obj
    let v := ((I.action n).action k hn).act
    let q := projection (J.group k) (I.space n)
    let j := parameterInclusion (J.group k) (I.transition t)
    let he := I.transitionActionSquare t k hn hm
    let hp := projectionSquare (J.group k) (I.transition t)
    let a := (levelIso (I.supportActionSquare m) α oneFF k hm).hom
    let b := (levelIso (I.supportActionSquare n) α oneFF k hn).hom
    (derivedInverseImage v).map c.hom ≫
        ((derivedInverseImageComposition v (I.transition t)).inv.app
          (I.intersectionRestriction F m).obj ≫ pullbackMorphism j he hp a ≫
          (derivedInverseImageComposition q (I.transition t)).hom.app
            (I.intersectionRestriction F m).obj) =
      b ≫ (derivedInverseImage q).map c.hom := by
  dsimp only
  apply (restriction_comparison_iff _ _ _ _ _).mpr
  let l := max k S.cutoff
  let h : k ≤ l := Nat.le_max_left k S.cutoff
  let hs : S.cutoff ≤ l := Nat.le_max_right k S.cutoff
  let hn' := hn.trans h
  let hm' := hm.trans h
  let he := I.transitionActionSquare t k hn hm
  let hp := projectionSquare (J.group k) (I.transition t)
  let he' := I.transitionActionSquare t l hn' hm'
  let hp' := projectionSquare (J.group l) (I.transition t)
  apply restrictsTo_of_pullback (Classical.choice (oneFF h (I.space n)))
    (single_inclusion h (I.transition t)) he hp
    ((I.action m).factors hm h) (single_projection h (I.space m))
    ((I.action n).factors hn h) (single_projection h (I.space n)) he' hp'
    (G := I.intersectionRestriction F m) (F := I.intersectionRestriction F n)
  rw [levelIso_agrees (I.supportActionSquare m) α oneFF hm h hs,
    levelIso_agrees (I.supportActionSquare n) α oneFF hn h hs]
  apply (restriction_comparison_iff he' hp' _ _ _).mp
  have hh := squareIso_transition (I.transition_support t) he'
    (I.supportActionSquare m l hm' hs) (I.supportActionSquare n l hn' hs) (α.datum l hs)
  dsimp only at hh
  rw [squareIso_hom he' hp'] at hh
  exact hh

private def localEquivariance : I.LocalEquivariance F α where
  datum n := descendEquivariance (I.supportActionSquare n) α oneFF twoFF
  onSupport := by
    intro n k hn hs
    have h := (levelIso_at_common (I.supportActionSquare n) α oneFF k hn hs).trans
      (highDatum_hom (I.supportActionSquare n) α k hn hs)
    change (derivedInverseImage ((I.action n).action k hn).act).map (𝟙 _) ≫
        restrictedArrow (I.supportActionSquare n) α k hn hs =
      (levelIso (I.supportActionSquare n) α oneFF k hn).hom ≫
        (derivedInverseImage (projection (J.group k) (I.space n))).map (𝟙 _)
    rw [(derivedInverseImage ((I.action n).action k hn).act).map_id,
      (derivedInverseImage (projection (J.group k) (I.space n))).map_id,
      Category.id_comp, Category.comp_id]
    exact h.symm
  onTransitions := by
    intro n m t k hn hm
    have hc := congrArg Iso.hom (intersectionComparison_underlying I F t)
    change (I.intersectionRestrictionComparison F t).hom.hom =
      (compositionAt (I.transition t) (I.intoSupport m) (I.transition_support t) F.obj).hom at hc
    unfold restrictedArrow
    rw [hc]
    exact levelIso_transition I oneFF F α t k hn hm

omit α in
private theorem local_naturality {F G : BoundedBelow Y}
    {α : S.Equivariance F.obj} {γ : S.Equivariance G.obj}
    (f : F ⟶ G)
    (hf : ∀ (k : ℕ) (hk : S.cutoff ≤ k),
      (derivedInverseImage (S.action k hk).act).map f.hom ≫ (γ.datum k hk).iso.hom =
        (α.datum k hk).iso.hom ≫ (derivedInverseImage (projection (J.group k) Y)).map f.hom)
    (n k : ℕ) (hk : (I.action n).cutoff ≤ k) :
    let qf := ((boundedBelowInverseImage (I.intoSupport n)).map f).hom
    (derivedInverseImage ((I.action n).action k hk).act).map qf ≫
        (levelIso (I.supportActionSquare n) γ oneFF k hk).hom =
      (levelIso (I.supportActionSquare n) α oneFF k hk).hom ≫
        (derivedInverseImage (projection (J.group k) (I.space n))).map qf := by
  dsimp only
  let l := max k S.cutoff
  let h : k ≤ l := Nat.le_max_left k S.cutoff
  let hs : S.cutoff ≤ l := Nat.le_max_right k S.cutoff
  apply naturality_of_pullback (Classical.choice (oneFF h (I.space n)))
    ((I.action n).factors hk h) (single_projection h (I.space n))
    (F := I.intersectionRestriction F n) (G := I.intersectionRestriction G n)
  rw [levelIso_agrees (I.supportActionSquare n) α oneFF hk h hs,
    levelIso_agrees (I.supportActionSquare n) γ oneFF hk h hs]
  exact squareIso_naturality (I.supportActionSquare n l (hk.trans h) hs)
    (projectionSquare (J.group l) (I.intoSupport n)) f.hom
    (α.datum l hs).iso (γ.datum l hs).iso (hf l hs)

end Intersections

theorem supportIntersectionJetDescent :
    SupportIntersectionJetDescentSpecs.Expected.SupportIntersectionJetDescent := by
  intro X Y J A B i S I oneFF twoFF
  refine ⟨localEquivariance I oneFF twoFF, ?_, ?_, ?_⟩
  · intro F α n k hk hs
    exact (levelIso_at_common (I.supportActionSquare n) α oneFF k hk hs).trans
      (highDatum_hom (I.supportActionSquare n) α k hk hs)
  · intro F α n k l hk h hs
    exact (levelIso_agrees (I.supportActionSquare n) α oneFF hk h hs).trans
      (highDatum_hom (I.supportActionSquare n) α l (hk.trans h) hs)
  · intro F G α γ f hf n k hk
    exact local_naturality I oneFF f hf n k hk

end RepTheorySurvey.Geometric.SupportIntersectionJetDescent
