import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.FlagCovarianceLinearization

open _root_.LinearAlgebraicGroups.Specs
open Specs.FlagCohomology Specs.EquivariantAffineModules Specs.FlagCovarianceLinearization
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.QuotientEmbedding (Presentation)
open Specs.CharacterDescent (Character)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Representation.FlagCohomology
open Scheme.Modules

noncomputable section

set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section AdjointComposition

variable {X Y Z : Scheme.{u}}

private abbrev adj (f : X ⟶ Y) := pullbackPushforwardAdjunction f

private theorem transpose_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : X.Modules} {H : Y.Modules} {K : Z.Modules}
    (a : F ⟶ (pushforward f).obj H) (b : H ⟶ (pushforward g).obj K) :
    ((adj (g ≫ f)).homEquiv F K).symm
      (a ≫ (pushforward f).map b ≫ (pushforwardComp g f).hom.app K) =
    (pullbackComp g f).inv.app F ≫
      (Scheme.Modules.pullback g).map (((adj f).homEquiv F H).symm a) ≫
      ((adj g).homEquiv H K).symm b := by
  let A := (adj f).comp (adj g)
  let B := adj (g ≫ f)
  let e := (pullbackComp g f).inv
  have h := conjugateEquiv_counit A B e K
  rw [conjugateEquiv_pullbackComp_inv] at h
  simp only [Category.assoc, Adjunction.homEquiv_counit, Functor.map_comp]
  change (Scheme.Modules.pullback (g ≫ f)).map a ≫
      (Scheme.Modules.pullback (g ≫ f)).map ((pushforward f).map b) ≫
      (Scheme.Modules.pullback (g ≫ f)).map ((pushforwardComp g f).hom.app K) ≫ B.counit.app K =
    e.app F ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map a) ≫
      (Scheme.Modules.pullback g).map ((adj f).counit.app H) ≫
      (Scheme.Modules.pullback g).map b ≫ (adj g).counit.app K
  rw [h]
  change _ ≫ _ ≫ e.app _ ≫
      (Scheme.Modules.pullback g).map ((adj f).counit.app ((pushforward g).obj K)) ≫
      (adj g).counit.app K = _
  rw [e.naturality_assoc, e.naturality_assoc]
  change _ ≫ _ ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map ((pushforward f).map b)) ≫
      (Scheme.Modules.pullback g).map ((adj f).counit.app ((pushforward g).obj K)) ≫ _ = _
  have hn := (adj f).counit.naturality b
  change (Scheme.Modules.pullback f).map ((pushforward f).map b) ≫
    (adj f).counit.app ((pushforward g).obj K) = (adj f).counit.app H ≫ b at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  rfl

end AdjointComposition

section CovarianceArrows

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable {X : SchemeOverRing A} {Y : SchemeOverRing B} {Z : SchemeOverRing C}

private structure CovarianceArrow (D : CovarianceData X) (E : CovarianceData Y) where
  base : X.left ⟶ Y.left
  torsor : D.torsor.left ⟶ E.torsor.left
  overlap : D.overlap.left ⟶ E.overlap.left
  projection : torsor ≫ E.projection.left = D.projection.left ≫ base
  first : overlap ≫ E.first.left = D.first.left ≫ torsor
  second : overlap ≫ E.second.left = D.second.left ≫ torsor
  multiplier : overlap.appTop E.multiplier = D.multiplier

variable {D : CovarianceData X} {E : CovarianceData Y} {F : CovarianceData Z}

private def CovarianceArrow.comp (a : CovarianceArrow D E) (b : CovarianceArrow E F) :
    CovarianceArrow D F where
  base := a.base ≫ b.base
  torsor := a.torsor ≫ b.torsor
  overlap := a.overlap ≫ b.overlap
  projection := by simp only [Category.assoc, b.projection, reassoc_of% a.projection]
  first := by simp only [Category.assoc, b.first, reassoc_of% a.first]
  second := by simp only [Category.assoc, b.second, reassoc_of% a.second]
  multiplier := by rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, b.multiplier, a.multiplier]

private def CovarianceArrow.coeff (a : CovarianceArrow D E) :
    E.sheaf ⟶ (pushforward a.base).obj D.sheaf :=
  (covariancePullback_exists E D a.base a.torsor a.projection
    a.overlap a.first a.second a.multiplier).choose

private theorem CovarianceArrow.coeff_spec (a : CovarianceArrow D E) :
    E.IsPullbackMap D a.base a.torsor a.projection a.coeff :=
  (covariancePullback_exists E D a.base a.torsor a.projection
    a.overlap a.first a.second a.multiplier).choose_spec

private def CovarianceArrow.pull (a : CovarianceArrow D E) :
    (Scheme.Modules.pullback a.base).obj E.sheaf ⟶ D.sheaf :=
  ((adj a.base).homEquiv _ _).symm a.coeff

private theorem CovarianceArrow.coeff_comp (a : CovarianceArrow D E) (b : CovarianceArrow E F) :
    (a.comp b).coeff =
      b.coeff ≫ (pushforward b.base).map a.coeff ≫ (pushforwardComp a.base b.base).hom.app _ :=
  covariancePullback_unique F D _ _ _ (a.comp b).coeff_spec
    (covariancePullback_comp b.coeff_spec a.coeff_spec)

private theorem CovarianceArrow.pull_comp (a : CovarianceArrow D E) (b : CovarianceArrow E F) :
    (a.comp b).pull =
      (pullbackComp a.base b.base).inv.app _ ≫ (Scheme.Modules.pullback a.base).map b.pull ≫ a.pull := by
  unfold CovarianceArrow.pull
  rw [CovarianceArrow.coeff_comp]
  exact transpose_comp _ _ _ _

private theorem CovarianceArrow.comp_pull_isIso (a : CovarianceArrow D E) (b : CovarianceArrow E F)
    [IsIso a.pull] [IsIso b.pull] : IsIso (a.comp b).pull := by
  rw [CovarianceArrow.pull_comp]
  infer_instance

private theorem CovarianceArrow.pull_congr (a b : CovarianceArrow D E)
    (h : a.base = b.base) (ht : a.torsor = b.torsor) :
    (pullbackCongr h).hom.app _ ≫ b.pull = a.pull := by
  cases a
  cases b
  dsimp at h ht
  subst_vars
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  apply congrArg (((adj _).homEquiv _ _).symm)
  exact covariancePullback_unique _ _ _ _ _ (CovarianceArrow.coeff_spec _)
    (CovarianceArrow.coeff_spec _)

private def CovarianceArrow.extension {k : Type u} [Field k] {X : SchemeOver k}
    (D : CovarianceData X) (R : TestAlgebra k) : CovarianceArrow (D.extend R) D where
  base := extensionProjection R X
  torsor := extensionProjection R D.torsor
  overlap := extensionProjection R D.overlap
  projection := (extensionProjection_natural R D.projection).symm
  first := (extensionProjection_natural R D.first).symm
  second := (extensionProjection_natural R D.second).symm
  multiplier := rfl

private theorem CovarianceArrow.extension_pull {k : Type u} [Field k] {X : SchemeOver k}
    {D : CovarianceData X} {R : TestAlgebra k} (e : D.ScalarExtension R) :
    (CovarianceArrow.extension D R).pull =
      ((adj (extensionProjection R X)).homEquiv _ _).symm e.coefficientMap := by
  apply congrArg (((adj (extensionProjection R X)).homEquiv _ _).symm)
  exact covariancePullback_unique D (D.extend R) _ _ _
    (CovarianceArrow.extension D R).coeff_spec e.pullsBack

private theorem CovarianceArrow.extension_pull_isIso {k : Type u} [Field k] {X : SchemeOver k}
    {D : CovarianceData X} {R : TestAlgebra k} (e : D.ScalarExtension R) :
    IsIso (CovarianceArrow.extension D R).pull :=
  (CovarianceArrow.extension_pull e).symm ▸ e.sheafIso

end CovarianceArrows

section InvertibleArrows

variable {A B : Type u} [CommRing A] [CommRing B]
variable {X : SchemeOverRing A} {Y : SchemeOverRing B}
variable {D : CovarianceData X} {E : CovarianceData Y}

open private pullFunctions_app
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

private def CovarianceArrow.id (D : CovarianceData X) : CovarianceArrow D D where
  base := 𝟙 _
  torsor := 𝟙 _
  overlap := 𝟙 _
  projection := by simp
  first := by simp
  second := by simp
  multiplier := by simp

private theorem identity_isPullbackMap (D : CovarianceData X)
    (w : 𝟙 D.torsor.left ≫ D.projection.left = D.projection.left ≫ 𝟙 X.left) :
    D.IsPullbackMap D (𝟙 X.left) (𝟙 D.torsor.left) w ((pushforwardId X.left).inv.app D.sheaf) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  let q := D.projection.left
  let z : Γ(D.torsor.left, q ⁻¹ᵁ U) := D.inclusion.app U x
  change z = (D.pullFunctions D (𝟙 X.left) (𝟙 D.torsor.left) w).app U z
  rw [pullFunctions_app]
  change z = (𝟙 D.torsor.left : D.torsor.left ⟶ D.torsor.left).appLE
    (q ⁻¹ᵁ U) ((q ≫ 𝟙 X.left) ⁻¹ᵁ U) _ z
  erw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
  rfl

private theorem CovarianceArrow.coeff_id (D : CovarianceData X) :
    (CovarianceArrow.id D).coeff = (pushforwardId X.left).inv.app D.sheaf :=
  covariancePullback_unique D D (𝟙 X.left) (𝟙 D.torsor.left) (CovarianceArrow.id D).projection
    (CovarianceArrow.id D).coeff_spec (identity_isPullbackMap D _)

private theorem CovarianceArrow.pull_id (D : CovarianceData X) :
    (CovarianceArrow.id D).pull = (pullbackId X.left).hom.app D.sheaf := by
  unfold CovarianceArrow.pull
  rw [CovarianceArrow.coeff_id, Adjunction.homEquiv_counit]
  have h := conjugateEquiv_counit
    (Adjunction.id (C := X.left.Modules)) (adj (𝟙 X.left)) (pullbackId X.left).hom D.sheaf
  rw [conjugateEquiv_pullbackId_hom] at h
  exact h.trans (Category.comp_id _)

private theorem CovarianceArrow.pull_isIso_of_inverse
    (a : CovarianceArrow D E) (b : CovarianceArrow E D)
    (hab : a.base ≫ b.base = 𝟙 _) (hba : b.base ≫ a.base = 𝟙 _)
    (ht₁ : a.torsor ≫ b.torsor = 𝟙 _) (ht₂ : b.torsor ≫ a.torsor = 𝟙 _) :
    IsIso a.pull := by
  have h := (a.comp b).pull_congr (CovarianceArrow.id D) hab ht₁
  have h' := (b.comp a).pull_congr (CovarianceArrow.id E) hba ht₂
  rw [CovarianceArrow.pull_comp, CovarianceArrow.pull_id] at h h'
  have h₁ : IsIso ((Scheme.Modules.pullback a.base).map b.pull ≫ a.pull) := by
    rw [← isIso_comp_left_iff ((pullbackComp a.base b.base).inv.app _), ← h]
    infer_instance
  have h₂ : IsIso ((Scheme.Modules.pullback b.base).map a.pull ≫ b.pull) := by
    rw [← isIso_comp_left_iff ((pullbackComp b.base a.base).inv.app _), ← h']
    infer_instance
  have : IsIso b.base := ⟨⟨a.base, hba, hab⟩⟩
  let : (Scheme.Modules.pullback b.base).IsEquivalence := by
    let e : X.left.Modules ≌ Y.left.Modules :=
      CategoryTheory.Equivalence.mk (Scheme.Modules.pullback b.base) (Scheme.Modules.pullback a.base)
        ((pullbackId X.left).symm ≪≫ (pullbackCongr hab).symm ≪≫
          (pullbackComp a.base b.base).symm)
        (pullbackComp b.base a.base ≪≫ pullbackCongr hba ≪≫ pullbackId Y.left)
    exact e.isEquivalence_functor
  let : Mono ((Scheme.Modules.pullback b.base).map a.pull) := mono_of_mono_fac (rfl :
    (Scheme.Modules.pullback b.base).map a.pull ≫ b.pull = _)
  let : Mono a.pull := Functor.mono_of_mono_map (Scheme.Modules.pullback b.base) (f := a.pull) inferInstance
  let c := (Scheme.Modules.pullback a.base).map b.pull
  let d := inv (c ≫ a.pull) ≫ c
  have hd : d ≫ a.pull = 𝟙 _ := by simp [d, Category.assoc]
  exact ⟨⟨d, (cancel_mono a.pull).mp (by rw [Category.assoc, hd, Category.comp_id, Category.id_comp]),
    hd⟩⟩

end InvertibleArrows

section Translations

open private overlapTranslation overlapTranslation_first overlapTranslation_second
  overlapTranslation_multiplier pointTranslation_natural pointTranslation_comp
  pointTranslation_one pointTranslation_fst pointTranslation_structure
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}

private abbrev FlagActionCompatible (a : ModObj G.val.X Q.scheme) :=
  μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul

private def includeTorusPoint (P : OppositeBorelPair G) (S : TestAlgebra k)
    (t : GroupPoints P.torus.group S) : GroupPoints G.val S :=
  t ≫ P.torus.inclusion.hom.hom

private def translation (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    CovarianceArrow ((flagLineData Q p χ h).extend R) ((flagLineData Q p χ h).extend R) where
  base := pointTranslation a.smul R g
  torsor := pointTranslation μ[G.val.X] R g
  overlap := overlapTranslation (P := P) R g
  projection := by
    have hn := pointTranslation_natural R (𝟙 G.val.X) Q.projection _ _ ha g
    rwa [Category.comp_id] at hn
  first := overlapTranslation_first R g
  second := overlapTranslation_second R g
  multiplier := overlapTranslation_multiplier R p χ g

private abbrev translatedPull (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :=
  ((translation (p := p) (χ := χ) (h := h) ha R g).comp
    (CovarianceArrow.extension (flagLineData Q p χ h) R)).pull

private theorem translation_pull_isIso (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    IsIso (translation (p := p) (χ := χ) (h := h) ha R g).pull := by
  let := a
  let : ModObj G.val.X G.val.X := ModObj.regular G.val.X
  apply CovarianceArrow.pull_isIso_of_inverse _ (translation ha R g⁻¹)
  · change pointTranslation γ[G.val.X, Q.scheme] R g ≫
      pointTranslation γ[G.val.X, Q.scheme] R g⁻¹ = 𝟙 _
    exact (pointTranslation_comp R g g⁻¹).trans (by rw [inv_mul_cancel, pointTranslation_one])
  · change pointTranslation γ[G.val.X, Q.scheme] R g⁻¹ ≫
      pointTranslation γ[G.val.X, Q.scheme] R g = 𝟙 _
    exact (pointTranslation_comp R g⁻¹ g).trans (by rw [mul_inv_cancel, pointTranslation_one])
  · change pointTranslation γ[G.val.X, G.val.X] R g ≫
      pointTranslation γ[G.val.X, G.val.X] R g⁻¹ = 𝟙 _
    exact (pointTranslation_comp R g g⁻¹).trans (by rw [inv_mul_cancel, pointTranslation_one])
  · change pointTranslation γ[G.val.X, G.val.X] R g⁻¹ ≫
      pointTranslation γ[G.val.X, G.val.X] R g = 𝟙 _
    exact (pointTranslation_comp R g⁻¹ g).trans (by rw [mul_inv_cancel, pointTranslation_one])

/-- The pullback of covariant functions along inverse translation induces
the previously constructed action in every degree over every test algebra. -/
private theorem translation_cohomology (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (g : GroupPoints G.val R)
    (E : (flagLineData Q p χ h).ScalarExtension R) (n : ℕ) :
    let D := (flagLineData Q p χ h).extend R
    let Y := (extendScheme R).obj Q.scheme
    let t := translation (p := p) (χ := χ) (h := h) ha R g⁻¹
    ∃ m : (cohomology Y n).obj D.sheaf ⟶ (cohomology Y n).obj D.sheaf,
      IsCohomologyMap (RingHom.id R) t.base (pointTranslation_over a.smul R g⁻¹) t.coeff n
        (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv) ∧
      ∀ (b : CohomologyBasis (p := p) (χ := χ) h n)
        (ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n)),
        IsFlagCohomologyAction h a n b ρ →
          ∀ v, extendedCoordinates R b ((E.iso n).inv (m v)) =
            RootWeightAction.act ρ R g (extendedCoordinates R b ((E.iso n).inv v)) := by
  dsimp only
  obtain ⟨w, β, hβ, hm⟩ := flagCohomologyTranslate_induced Q p χ h a ha R n g
  let t := translation (p := p) (χ := χ) (h := h) ha R g⁻¹
  have heq : β = t.coeff := covariancePullback_unique _ _ _ _ w hβ t.coeff_spec
  subst β
  refine ⟨flagCohomologyTranslate Q p χ h a ha R n g, hm, ?_⟩
  intro b ρ hρ v
  obtain ⟨_, α, m, hα, hm', hc⟩ := hρ R g E
  have heq' : α = t.coeff := covariancePullback_unique _ _ _ _ w hα t.coeff_spec
  subst α
  have eq := inducedCohomologyMap_unique _ _ _ _ n hm' hm
  have em := (cancel_mono (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv).mp eq
  rw [← em]
  exact hc v

end Translations

section Products

variable {k : Type u} [Field k] {X V W : SchemeOver k}

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private extension_hom_ext extensionArrow extensionArrow_original extensionArrow_testScheme
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {R : TestAlgebra k}

private def extensionProductIso (j : (testSpec k).obj (op R) ≅ W) (X : SchemeOver k) :
    extensionAsSchemeOverField R X ≅ W ⊗ X := by
  let f := lift (projectionToTestScheme R X ≫ j.hom) (projectionToOriginal R X)
  let p := snd W X
  let q := fst W X ≫ j.inv
  let w : p.left ≫ X.hom = q.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) :=
    (Over.w p).trans (Over.w q).symm
  let g₀ : (W ⊗ X).left ⟶ ((extendScheme R).obj X).left :=
    Limits.pullback.lift p.left q.left w
  have hq : g₀ ≫ ((extendScheme R).obj X).hom = q.left :=
    Limits.pullback.lift_snd p.left q.left w
  let g : W ⊗ X ⟶ extensionAsSchemeOverField R X :=
    Over.homMk g₀ (by
      change g₀ ≫ ((extendScheme R).obj X).hom ≫ Spec.map
        (CommRingCat.ofHom (algebraMap k R)) = _
      rw [← Category.assoc, hq]
      exact Over.w q)
  have gp : g ≫ projectionToOriginal R X = p :=
    Over.OverMorphism.ext (Limits.pullback.lift_fst p.left q.left w)
  have gq : g ≫ projectionToTestScheme R X = q :=
    Over.OverMorphism.ext hq
  refine ⟨f, g, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    apply extension_hom_ext R
    · change ((f ≫ g) ≫ projectionToOriginal R X).left = _
      rw [Category.assoc, gp, lift_snd]
      rfl
    · change ((f ≫ g) ≫ projectionToTestScheme R X).left = _
      rw [Category.assoc, gq]
      simp [f, q]
      rfl
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, show f ≫ fst W X = projectionToTestScheme R X ≫ j.hom
        from lift_fst _ _, ← Category.assoc, gq]
      simp [q]
    · rw [Category.assoc, show f ≫ snd W X = projectionToOriginal R X from lift_snd _ _, gp]
      simp [p]

@[reassoc]
private theorem extensionProductIso_snd (j : (testSpec k).obj (op R) ≅ W) (X : SchemeOver k) :
    (extensionProductIso j X).hom ≫ snd W X = projectionToOriginal R X :=
  lift_snd _ _

@[reassoc]
private theorem extensionProductIso_fst (j : (testSpec k).obj (op R) ≅ W) (X : SchemeOver k) :
    (extensionProductIso j X).hom ≫ fst W X = projectionToTestScheme R X ≫ j.hom :=
  lift_fst _ _

end Products

/-- Evaluating the transport and then taking the translated coordinate gives
the original coordinate. -/
private def TransportMatches {k : Type u} [Field k] {T : GroupScheme k}
    {X Z : SchemeOver k} (a : ModObj T.X X) {F : X.left.Modules} {M : Z.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) {x y : Z ⟶ X}
    (u : Pull x F ⟶ M) (v : Pull y F ⟶ M) : Prop :=
  ∃ w : actOn a t x = y, (transport a θ t x).hom ≫ (pullCongr F w).hom ≫ v = u

section UniversalPoint

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private translationArrow pointTranslation_fst pointTranslation_structure
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private comparePull evalPullIso pullback_map_evalPullIso_to transport_eq_evalPullIso
  pullCongr_refl evalPullIso_comp_congr
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}

private theorem torus_actOn {Z : SchemeOver k} (t : Z ⟶ P.torus.group.X) (x : Z ⟶ Q.scheme) :
    actOn (torusAction (P := P) a) t x =
      lift (t ≫ P.torus.inclusion.hom.hom) x ≫ a.smul := by
  change lift t x ≫ (P.torus.inclusion.hom.hom ⊗ₘ 𝟙 _) ≫ a.smul = _
  rw [← Category.assoc, lift_map, Category.comp_id]

private theorem translation_base_original (R : TestAlgebra k) (t : GroupPoints G.val R) :
    translationArrow R a.smul t ≫ projectionToOriginal R Q.scheme =
      lift (projectionToTestScheme R Q.scheme ≫ t) (projectionToOriginal R Q.scheme) ≫ a.smul :=
  Over.OverMorphism.ext (pointTranslation_fst R a.smul t)

private theorem universal_smul (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X) :
    (extensionProductIso j Q.scheme).hom ≫ (torusAction (P := P) a).smul =
      translationArrow R a.smul (j.hom ≫ P.torus.inclusion.hom.hom) ≫
        projectionToOriginal R Q.scheme := by
  rw [translation_base_original]
  change lift (projectionToTestScheme R Q.scheme ≫ j.hom) (projectionToOriginal R Q.scheme) ≫
      (torusAction (P := P) a).smul = _
  exact (torus_actOn (a := a) _ _).trans (by rw [Category.assoc])

private theorem evaluatedIso {X W B Z : SchemeOver k} {F : X.left.Modules}
    {g₁ g₂ : W ⟶ X} {l : B ⟶ W} {f : Z ⟶ B}
    {x y : B ⟶ X} {x' y' : Z ⟶ X}
    (θ : Pull g₁ F ≅ Pull g₂ F) (hx : l ≫ g₁ = x) (hy : l ≫ g₂ = y)
    (hx' : f ≫ x = x') (hy' : f ≫ y = y') :
    evalPullIso (evalPullIso θ l hx hy) f hx' hy' =
      evalPullIso θ (f ≫ l) (by rw [Category.assoc, hx, hx'])
        (by rw [Category.assoc, hy, hy']) := by
  apply Iso.ext
  change (comparePull F f x hx').inv ≫
      (Scheme.Modules.pullback f.left).map (evalPullIso θ l hx hy).hom ≫
      (comparePull F f y hy').hom = _
  have h := pullback_map_evalPullIso_to θ l hx hy f rfl hx' hy'
    ((Category.assoc f l g₁).trans ((congrArg (f ≫ ·) hx).trans hx'))
    ((Category.assoc f l g₂).trans ((congrArg (f ≫ ·) hy).trans hy'))
  exact (congrArg ((comparePull F f x hx').inv ≫ ·) h).trans
    ((comparePull F f x hx').inv_hom_id_assoc _)

private def universalPointIso (ha : FlagActionCompatible a) (R : TestAlgebra k)
    (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R) :
    Pull (snd P.torus.group.X Q.scheme) (flagLineSheaf Q p χ h) ≅
      Pull (torusAction (P := P) a).smul (flagLineSheaf Q p χ h) := by
  let D := flagLineData Q p χ h
  let π := CovarianceArrow.extension D R
  let δ := translation (p := p) (χ := χ) (h := h) ha R (j.hom ≫ P.torus.inclusion.hom.hom)
  let τ := δ.comp π
  haveI : IsIso π.pull := CovarianceArrow.extension_pull_isIso E
  haveI : IsIso δ.pull := translation_pull_isIso ha R _
  haveI : IsIso τ.pull := CovarianceArrow.comp_pull_isIso δ π
  let e := extensionProductIso j Q.scheme
  let x := projectionToOriginal R Q.scheme
  let x' := translationArrow R a.smul (j.hom ≫ P.torus.inclusion.hom.hom) ≫ x
  let φ : Pull x D.sheaf ≅ Pull x' D.sheaf :=
    (show Pull x D.sheaf ≅ (D.extend R).sheaf from asIso π.pull) ≪≫
      (show Pull x' D.sheaf ≅ (D.extend R).sheaf from asIso τ.pull).symm
  let hx : e.inv ≫ x = snd P.torus.group.X Q.scheme := by
    exact (congrArg (e.inv ≫ ·) (extensionProductIso_snd j Q.scheme).symm).trans
      (e.inv_hom_id_assoc _)
  let hx' : e.inv ≫ x' = (torusAction (P := P) a).smul := by
    exact (congrArg (e.inv ≫ ·) (universal_smul (a := a) R j).symm).trans
      (e.inv_hom_id_assoc _)
  exact evalPullIso φ e.inv hx hx'

set_option maxHeartbeats 700000 in
private theorem eval_comp_pull {A B : Type u} [CommRing A] [CommRing B]
    {Y : SchemeOverRing A} {W : SchemeOverRing B} {D : CovarianceData Q.scheme}
    {J : CovarianceData W} (C : CovarianceData Y)
    (d : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k))
    (v₁ v₂ : CovarianceArrow J D)
    (w₁ : v₁.base ≫ Q.scheme.hom = W.hom ≫ d)
    (w₂ : v₂.base ≫ Q.scheme.hom = W.hom ≫ d)
    (e₁ : (Scheme.Modules.pullback v₁.base).obj D.sheaf ≅ J.sheaf)
    (e₂ : (Scheme.Modules.pullback v₂.base).obj D.sheaf ≅ J.sheaf)
    (he₁ : e₁.hom = v₁.pull) (he₂ : e₂.hom = v₂.pull)
    (v : CovarianceArrow C J)
    (b : Y.left ⟶ Spec (CommRingCat.of k))
    (hb : v.base ≫ W.hom ≫ d = b) :
    let Wk : SchemeOver k := Over.mk (W.hom ≫ d)
    let Z : SchemeOver k := Over.mk b
    let r : Z ⟶ Wk := Over.homMk v.base hb
    let x₁ : Wk ⟶ Q.scheme := Over.homMk v₁.base w₁
    let x₂ : Wk ⟶ Q.scheme := Over.homMk v₂.base w₂
    (evalPullIso (F := D.sheaf) (g₁ := x₁) (g₂ := x₂) (e₁ ≪≫ e₂.symm) r rfl rfl).hom ≫
      (v.comp v₂).pull = (v.comp v₁).pull := by
  dsimp only
  rw [CovarianceArrow.pull_comp, CovarianceArrow.pull_comp, ← he₁, ← he₂]
  let L := Scheme.Modules.pullback v.base
  let c₁ := (pullbackComp v.base v₁.base).app D.sheaf
  let c₂ := (pullbackComp v.base v₂.base).app D.sheaf
  have hf : L.map (e₁.hom ≫ e₂.inv) ≫ L.map e₂.hom = L.map e₁.hom := by
    rw [← Functor.map_comp, Category.assoc, e₂.inv_hom_id, Category.comp_id]
  simp only [evalPullIso, comparePull, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, pullCongr_refl, Category.comp_id, Category.assoc,
    Functor.mapIso_hom]
  change c₁.inv ≫ L.map (e₁.hom ≫ e₂.inv) ≫ c₂.hom ≫ c₂.inv ≫ L.map e₂.hom ≫ v.pull = _
  rw [c₂.hom_inv_id_assoc, reassoc_of% hf]
  rfl

private theorem evalPullIso_eq_of_map_eq {X W Z : SchemeOver k} {F : X.left.Modules}
    {p q : W ⟶ X} (φ : Pull p F ≅ Pull q F)
    {r r' : Z ⟶ W} (hh : r = r') {x y : Z ⟶ X}
    (hp : r ≫ p = x) (hq : r ≫ q = y) (hp' : r' ≫ p = x) (hq' : r' ≫ q = y) :
    evalPullIso φ r hp hq = evalPullIso φ r' hp' hq' := by
  subst r'
  rfl

private abbrev translatedProjection (a : ModObj G.val.X Q.scheme) (R : TestAlgebra k)
    (g : GroupPoints G.val R) :=
  translationArrow R a.smul g ≫ projectionToOriginal R Q.scheme

set_option maxHeartbeats 2500000 in
private theorem universalTransport (ha : FlagActionCompatible a) {A : Type u} [CommRing A]
    {Y : SchemeOverRing A} (C : CovarianceData Y)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (v : CovarianceArrow C ((flagLineData Q p χ h).extend R))
    (b : Y.left ⟶ Spec (CommRingCat.of k))
    (hb : v.base ≫ (extensionAsSchemeOverField R Q.scheme).hom = b) :
    let Z : SchemeOver k := Over.mk b
    let r : Z ⟶ extensionAsSchemeOverField R Q.scheme := Over.homMk v.base hb
    let x := r ≫ projectionToOriginal R Q.scheme
    let t := r ≫ projectionToTestScheme R Q.scheme ≫ j.hom
    let x' := r ≫ translatedProjection a R (j.hom ≫ P.torus.inclusion.hom.hom)
    let π := CovarianceArrow.extension (flagLineData Q p χ h) R
    let τ := (translation (p := p) (χ := χ) (h := h) ha R
      (j.hom ≫ P.torus.inclusion.hom.hom)).comp π
    TransportMatches (torusAction (P := P) a) (universalPointIso ha R j E) t
      (x := x) (y := x') (v.comp π).pull (v.comp τ).pull := by
  intro Z r x t x' π τ
  unfold TransportMatches
  let D := flagLineData Q p χ h
  let aT := torusAction (P := P) a
  let x₀ := projectionToOriginal R Q.scheme
  let x₁ := translatedProjection a R (j.hom ≫ P.torus.inclusion.hom.hom)
  let e := extensionProductIso j Q.scheme
  let δ := translation (p := p) (χ := χ) (h := h) ha R (j.hom ≫ P.torus.inclusion.hom.hom)
  have : IsIso π.pull := CovarianceArrow.extension_pull_isIso E
  have : IsIso δ.pull := translation_pull_isIso ha R _
  have : IsIso τ.pull := CovarianceArrow.comp_pull_isIso δ π
  let e₀ : Pull x₀ D.sheaf ≅ (D.extend R).sheaf := asIso π.pull
  let e₁ : Pull x₁ D.sheaf ≅ (D.extend R).sheaf := asIso τ.pull
  let φ := e₀ ≪≫ e₁.symm
  have hL : lift t x = r ≫ e.hom := by
    change lift t x = r ≫ lift (projectionToTestScheme R Q.scheme ≫ j.hom) x₀
    rw [comp_lift]
  have hw : actOn aT t x = r ≫ x₁ := by
    change lift t x ≫ aT.smul = _
    rw [hL, Category.assoc]
    congr 1
    exact universal_smul R j
  refine ⟨hw, ?_⟩
  have hxe : e.inv ≫ x₀ = snd P.torus.group.X Q.scheme := by
    exact (congrArg (e.inv ≫ ·) (extensionProductIso_snd j Q.scheme).symm).trans
      (e.inv_hom_id_assoc _)
  have hye : e.inv ≫ x₁ = aT.smul := by
    exact (congrArg (e.inv ≫ ·) (universal_smul (a := a) R j).symm).trans
      (e.inv_hom_id_assoc _)
  have hr : lift t x ≫ e.inv = r := by
    rw [hL, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (transport aT (evalPullIso φ e.inv hxe hye) t x).hom ≫
      (pullCongr D.sheaf hw).hom ≫ (v.comp τ).pull = _
  let θ := evalPullIso φ e.inv hxe hye
  have hθ : (transport aT θ t x).hom ≫ (pullCongr D.sheaf hw).hom =
      (evalPullIso θ (lift t x) (lift_snd t x) hw).hom := by
    rw [transport_eq_evalPullIso]
    exact evalPullIso_comp_congr θ (lift t x) (lift_snd t x) rfl hw
  have eq : evalPullIso θ (lift t x) (lift_snd t x) hw = evalPullIso φ r rfl rfl := by
    exact (evaluatedIso φ hxe hye (lift_snd t x) hw).trans
      (evalPullIso_eq_of_map_eq φ hr _ _ rfl rfl)
  have hc := eval_comp_pull C (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    π τ (Over.w x₀) (Over.w x₁) e₀ e₁ rfl rfl v b hb
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (v.comp τ).pull) (hθ.trans (congrArg Iso.hom eq)))).trans hc

end UniversalPoint

section ScalarTower

open private scalarTowerMap scalarTowerMap_original scalarTowerMap_naturality
  scalarTowerArrow scalarTowerArrow_original scalarTowerArrow_test
  pointTranslation_scalarTowerMap translationArrow translationArrow_testScheme
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] {X : SchemeOver k} {R S : TestAlgebra k}

private def covarianceTower (D : CovarianceData X) (j : R ⟶ S) :
    CovarianceArrow (D.extend S) (D.extend R) where
  base := scalarTowerMap j X
  torsor := scalarTowerMap j D.torsor
  overlap := scalarTowerMap j D.overlap
  projection := scalarTowerMap_naturality j D.projection
  first := scalarTowerMap_naturality j D.first
  second := scalarTowerMap_naturality j D.second
  multiplier := by
    change (scalarTowerMap j D.overlap).appTop
      ((extensionProjection R D.overlap).appTop D.multiplier) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, scalarTowerMap_original]
    rfl

private theorem covarianceTower_original (D : CovarianceData X) (j : R ⟶ S) :
    ((covarianceTower D j).comp (CovarianceArrow.extension D R)).base =
      (CovarianceArrow.extension D S).base :=
  scalarTowerMap_original j X

private theorem covarianceTower_original_torsor (D : CovarianceData X) (j : R ⟶ S) :
    ((covarianceTower D j).comp (CovarianceArrow.extension D R)).torsor =
      (CovarianceArrow.extension D S).torsor :=
  scalarTowerMap_original j D.torsor

private def pointParameter {W : SchemeOver k} (e : (testSpec k).obj (op R) ≅ W)
    (t : Points W S) : R ⟶ S :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (t ≫ e.inv)).unop

private theorem pointParameter_point {W : SchemeOver k} (e : (testSpec k).obj (op R) ≅ W)
    (t : Points W S) : (testSpec k).map (pointParameter e t).op ≫ e.hom = t := by
  have w : (testSpec k).map (pointParameter e t).op = t ≫ e.inv :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  rw [w, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ScalarTower

section SpecializedTransport

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private scalarTowerArrow scalarTowerArrow_original scalarTowerArrow_test
  scalarTowerMap scalarTowerMap_original pointTranslation_scalarTowerMap pointTranslation_comp
  translationArrow translationArrow_testScheme
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private pullCongr_refl pullCongr_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}

private theorem compareTransport {T : GroupScheme k} {X Z : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules} {H : Z.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    {t t' : Z ⟶ T.X} {x x' y y' : Z ⟶ X}
    (ht : t = t') (hx : x = x') (hy : y = y')
    {u : Pull x F ⟶ H} {v : Pull y F ⟶ H}
    {u' : Pull x' F ⟶ H} {v' : Pull y' F ⟶ H}
    (hu : (pullCongr F hx).hom ≫ u' = u) (hv : (pullCongr F hy).hom ≫ v' = v)
    (hh : TransportMatches a θ t (x := x) (y := y) u v) :
    TransportMatches a θ t' (x := x') (y := y') u' v' := by
  subst t' x' y'
  simp only [pullCongr_refl, Category.id_comp] at hu hv
  rw [hu, hv]
  exact hh

private theorem compareTransport_source {T : GroupScheme k} {X Z : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules} {M : Z.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    (t : Z ⟶ T.X) {x x' y : Z ⟶ X}
    (u : Pull x F ⟶ M) (u' : Pull x' F ⟶ M) (v : Pull y F ⟶ M)
    (hx : x = x') (hu : (pullCongr F hx).hom ≫ u' = u)
    (h : TransportMatches a θ t (x := x) (y := y) u v) :
    TransportMatches a θ t (x := x') (y := y) u' v := by
  subst x'
  rw [pullCongr_refl, Category.id_comp] at hu
  rw [hu]
  exact h

set_option maxHeartbeats 1000000 in
private theorem compareArrowTransport {T : GroupScheme k} {X : SchemeOver k}
    {A : Type u} [CommRing A] {Y : SchemeOverRing A} {D : CovarianceData X}
    {C : CovarianceData Y} (b : Y.left ⟶ Spec (CommRingCat.of k))
    (a : ModObj T.X X) (θ : Pull (snd T.X X) D.sheaf ≅ Pull a.smul D.sheaf)
    {t t' : (Over.mk b : SchemeOver k) ⟶ T.X} (ht : t = t')
    (u v u' v' : CovarianceArrow C D)
    (hu : u.base ≫ X.hom = b) (hv : v.base ≫ X.hom = b)
    (hu' : u'.base ≫ X.hom = b) (hv' : v'.base ≫ X.hom = b)
    (hbase : u.base = u'.base) (htorsor : u.torsor = u'.torsor)
    (hbase' : v.base = v'.base) (htorsor' : v.torsor = v'.torsor)
    (h : TransportMatches a θ t (x := Over.homMk u.base hu)
      (y := Over.homMk v.base hv) u.pull v.pull) :
    TransportMatches a θ t' (x := Over.homMk u'.base hu')
      (y := Over.homMk v'.base hv') u'.pull v'.pull := by
  let Z : SchemeOver k := Over.mk b
  let x : Z ⟶ X := Over.homMk u.base hu
  let x' : Z ⟶ X := Over.homMk u'.base hu'
  let y : Z ⟶ X := Over.homMk v.base hv
  let y' : Z ⟶ X := Over.homMk v'.base hv'
  have eqx : x = x' := Over.OverMorphism.ext hbase
  have eqy : y = y' := Over.OverMorphism.ext hbase'
  exact compareTransport (T := T) (X := X) (Z := Z) (F := D.sheaf) (H := C.sheaf) a θ
    (x := x) (x' := x') (y := y) (y' := y')
    (u := u.pull) (u' := u'.pull) (v := v.pull) (v' := v'.pull)
    ht eqx eqy (u.pull_congr u' hbase htorsor) (v.pull_congr v' hbase' htorsor') h

private theorem translatedScalarTower_projection {H X : SchemeOver k} [MonObj H] [ModObj H X]
    {R S : TestAlgebra k} (j : R ⟶ S) (g : Points H S) (t : Points H R) :
    (pointTranslation γ[H, X] S g ≫ scalarTowerMap j X) ≫
        pointTranslation γ[H, X] R t ≫ extensionProjection R X =
      pointTranslation γ[H, X] S (mapPoints j t * g) ≫ extensionProjection S X := by
  simp only [Category.assoc]
  rw [← Category.assoc _ (pointTranslation γ[H, X] R t),
    pointTranslation_scalarTowerMap, Category.assoc, scalarTowerMap_original,
    ← Category.assoc, pointTranslation_comp]

set_option maxHeartbeats 1500000 in
private theorem specializedTransport (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (S : TestAlgebra k) (t : GroupPoints P.torus.group S) (g : GroupPoints G.val S) :
    let D := flagLineData Q p χ h
    let x := translatedProjection a S g
    let s := projectionToTestScheme S Q.scheme ≫ t
    let tG : GroupPoints G.val S := t ≫ P.torus.inclusion.hom.hom
    let z := tG * g
    let v := translation (h := h) (p := p) (χ := χ) ha S g
    let w := translation (h := h) (p := p) (χ := χ) ha S z
    let π := CovarianceArrow.extension D S
    TransportMatches (torusAction (P := P) a) (universalPointIso ha R j E) s
      (x := x) (y := translatedProjection a S z) (v.comp π).pull (w.comp π).pull := by
  intro D x s tG z v w π
  let f := translationArrow S a.smul g
  let aT := torusAction (P := P) a
  let j₀ := pointParameter j t
  let πR := CovarianceArrow.extension D R
  let gR : GroupPoints G.val R := j.hom ≫ P.torus.inclusion.hom.hom
  let δ := translation (h := h) (p := p) (χ := χ) ha R gR
  let baseChange := covarianceTower D j₀
  let r₀ := f ≫ scalarTowerArrow j₀ Q.scheme
  have hgR : mapPoints j₀ gR = tG := by
    change ((testSpec k).map j₀.op) ≫ j.hom ≫ P.torus.inclusion.hom.hom = _
    rw [← Category.assoc, pointParameter_point j t]
  have hb : (v.comp baseChange).base ≫ (extensionAsSchemeOverField R Q.scheme).hom =
      ((extendScheme S).obj Q.scheme).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)) := Over.w r₀
  let r : extensionAsSchemeOverField S Q.scheme ⟶ extensionAsSchemeOverField R Q.scheme :=
    Over.homMk (v.comp baseChange).base hb
  have hr : r = r₀ := Over.OverMorphism.ext rfl
  have he := universalTransport ha (D.extend S) R j E (v.comp baseChange) _ hb
  have hs : r ≫ projectionToTestScheme R Q.scheme ≫ j.hom = projectionToTestScheme S Q.scheme ≫ t := by
    rw [hr]
    change (f ≫ scalarTowerArrow j₀ Q.scheme) ≫ projectionToTestScheme R Q.scheme ≫ j.hom = _
    rw [Category.assoc, ← Category.assoc (scalarTowerArrow j₀ Q.scheme), scalarTowerArrow_test,
      Category.assoc, pointParameter_point j t, ← Category.assoc, translationArrow_testScheme]
  have hbase : ((v.comp baseChange).comp (δ.comp πR)).base = (w.comp π).base := by
    let := a
    change (pointTranslation a.smul S g ≫ scalarTowerMap j₀ Q.scheme) ≫
      pointTranslation a.smul R gR ≫ extensionProjection R Q.scheme =
      pointTranslation a.smul S z ≫ extensionProjection S Q.scheme
    exact (translatedScalarTower_projection (H := G.val.X) (X := Q.scheme) j₀ g gR).trans
      (congrArg (fun t' : GroupPoints G.val S =>
        pointTranslation a.smul S (t' * g) ≫ extensionProjection S Q.scheme) hgR)
  have htorsor : ((v.comp baseChange).comp (δ.comp πR)).torsor = (w.comp π).torsor := by
    let : ModObj G.val.X G.val.X := ModObj.regular G.val.X
    change (pointTranslation μ[G.val.X] S g ≫ scalarTowerMap j₀ G.val.X) ≫
      pointTranslation μ[G.val.X] R gR ≫ extensionProjection R G.val.X =
      pointTranslation μ[G.val.X] S z ≫ extensionProjection S G.val.X
    exact (translatedScalarTower_projection (H := G.val.X) (X := G.val.X) j₀ g gR).trans
      (congrArg (fun t' : GroupPoints G.val S =>
        pointTranslation μ[G.val.X] S (t' * g) ≫ extensionProjection S G.val.X) hgR)
  have hbase' : ((v.comp baseChange).comp πR).base = (v.comp π).base := by
    exact (Category.assoc _ _ _).trans
      (congrArg (v.base ≫ ·) (covarianceTower_original D j₀))
  have htor' : ((v.comp baseChange).comp πR).torsor = (v.comp π).torsor := by
    exact (Category.assoc _ _ _).trans
      (congrArg (v.torsor ≫ ·) (covarianceTower_original_torsor D j₀))
  let y := r ≫ translatedProjection a R gR
  exact compareArrowTransport (T := P.torus.group) (X := Q.scheme)
    (Y := (extendScheme S).obj Q.scheme) (D := D) (C := D.extend S)
    (extensionAsSchemeOverField S Q.scheme).hom aT (universalPointIso ha R j E)
    hs ((v.comp baseChange).comp πR) ((v.comp baseChange).comp (δ.comp πR))
    (v.comp π) (w.comp π)
    (Over.w (r ≫ projectionToOriginal R Q.scheme)) (Over.w y)
    (Over.w x) (Over.w (translatedProjection a S z))
    hbase' htor' hbase htorsor he

set_option maxHeartbeats 700000 in
private theorem specializedTransport_at (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (S : TestAlgebra k) (t : GroupPoints P.torus.group S) (g g' : GroupPoints G.val S)
    (r : extensionAsSchemeOverField S Q.scheme ⟶ P.torus.group.X)
    (hr : projectionToTestScheme S Q.scheme ≫ t = r)
    (hg : includeTorusPoint P S t * g = g') :
    let b := torusAction (P := P) a
    let C := translatedPull (p := p) (χ := χ) (h := h) ha S
    let x := translatedProjection a S g
    TransportMatches b (universalPointIso ha R j E) r
      (x := x) (y := translatedProjection a S g') (C g) (C g') := by
  intro b C x
  let θ := universalPointIso ha R j E
  let law (u : extensionAsSchemeOverField S Q.scheme ⟶ P.torus.group.X)
      (v : GroupPoints G.val S) :=
    TransportMatches b θ u (x := x) (y := translatedProjection a S v) (C g) (C v)
  have h₀ : law (projectionToTestScheme S Q.scheme ≫ t) (includeTorusPoint P S t * g) :=
    specializedTransport ha R j E S t g
  exact Eq.mp (congrArg₂ law hr hg) h₀

end SpecializedTransport

section TorsorCoordinates

open private pullFunctions_app pullbackRegular_app pointTranslation_fst overlapTranslation_original
  flagMultiplierAt flagMultiplierAt_testPoint topRegular_ext
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q}

private def trivialCovariance (Z : SchemeOver k) : CovarianceData Z where
  torsor := Z
  overlap := Z
  projection := 𝟙 _
  overlapProjection := 𝟙 _
  first := 𝟙 _
  second := 𝟙 _
  fst_w := rfl
  snd_w := rfl
  multiplier := 1

private def trivialCovarianceCoordinate (Z : SchemeOver k) :
    (trivialCovariance Z).sheaf ⟶ structureModule Z.left :=
  (trivialCovariance Z).inclusion ≫ (pushforwardId Z.left).hom.app _

private theorem flagTransition_at_unit {Z : SchemeOver k} (g : Z ⟶ G.val.X) :
    (prod.lift g (1 : Z ⟶ P.negative.group.X)).left.appTop (flagTransition p χ) = 1 := by
  apply topRegular_ext
  intro R z
  apply (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (flagMultiplierAt (p := p) (χ := χ) (z ≫ prod.lift g 1)) = _
  rw [flagMultiplierAt_testPoint, Category.assoc, prod.lift_snd, MonObj.comp_one,
    inv_one, map_one, map_one]
  let e : GroupPoints P.negative.group R := 1
  let χ₀ : Character P.negative.group := 1
  have he : e ≫ (p.projection ≫ χ).hom.hom = e ≫ χ₀.hom.hom :=
    (MonObj.one_comp _).trans (MonObj.one_comp _).symm
  have hv : CharacterPairing.characterValue (p.projection ≫ χ) R e =
      CharacterPairing.characterValue χ₀ R e := by
    unfold CharacterPairing.characterValue
    dsimp only
    rw [he]
  exact hv.trans (characterValue_one R e)

private theorem rightMultiplication_at_unit {Z : SchemeOver k} (g : Z ⟶ G.val.X) :
    prod.lift g (1 : Z ⟶ P.negative.group.X) ≫
      HomogeneousQuotient.rightMultiplication P.negative = g := by
  rw [HomogeneousQuotient.rightMultiplication, MonObj.comp_mul, prod.lift_fst,
    ← Category.assoc, prod.lift_snd, MonObj.one_comp, mul_one]

private def torsorLiftArrow {Z : SchemeOver k} (g : Z ⟶ G.val.X) :
    CovarianceArrow (trivialCovariance Z) (flagLineData Q p χ h) where
  base := (g ≫ Q.projection).left
  torsor := g.left
  overlap := (prod.lift g (1 : Z ⟶ P.negative.group.X)).left
  projection := by rw [Over.comp_left]; simp [trivialCovariance, flagLineData]
  first := by
    change (prod.lift g (1 : Z ⟶ P.negative.group.X)).left ≫ (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X).left = 𝟙 _ ≫ g.left
    rw [← Over.comp_left, prod.lift_fst, Category.id_comp]
  second := by
    change (prod.lift g (1 : Z ⟶ P.negative.group.X)).left ≫
      (HomogeneousQuotient.rightMultiplication P.negative).left = 𝟙 _ ≫ g.left
    rw [← Over.comp_left, Category.id_comp]
    exact congrArg Over.Hom.left (rightMultiplication_at_unit (P := P) g)
  multiplier := flagTransition_at_unit g

set_option maxHeartbeats 700000 in
private theorem torsorLiftArrow_coordinate {Z : SchemeOver k} (g : Z ⟶ G.val.X) :
    (torsorLiftArrow (Q := Q) (p := p) (χ := χ) (h := h) g).pull ≫
      trivialCovarianceCoordinate Z =
    flagLineCoordinate Q p χ h g := by
  let D := flagLineData Q p χ h
  let C := trivialCovariance Z
  let a := torsorLiftArrow (Q := Q) (p := p) (χ := χ) (h := h) g
  let β := D.inclusion ≫ (pushforward Q.projection.left).map (pullbackRegular g.left) ≫
    (pushforwardComp g.left Q.projection.left).hom.app (structureModule Z.left)
  have hb : a.coeff ≫ (pushforward a.base).map (trivialCovarianceCoordinate Z) = β := by
    change a.coeff ≫ (pushforward a.base).map
      (C.inclusion ≫ (pushforwardId Z.left).hom.app (structureModule Z.left)) = _
    rw [Functor.map_comp, ← Category.assoc, a.coeff_spec]
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardId_hom_app_app]
    change (D.pullFunctions C a.base a.torsor a.projection).app U (D.inclusion.app U x) =
      (pullbackRegular g.left).app (Q.projection.left ⁻¹ᵁ U) (D.inclusion.app U x)
    rw [pullFunctions_app, pullbackRegular_app]
    let V := Q.projection.left ⁻¹ᵁ U
    exact congrArg (fun f : Γ(G.val.X.left, V) ⟶ Γ(Z.left, g.left ⁻¹ᵁ V) =>
      f (D.inclusion.app U x)) (g.left.appLE_eq_app (U := V))
  unfold flagLineCoordinate
  change (((adj a.base).homEquiv D.sheaf C.sheaf).symm a.coeff) ≫
    trivialCovarianceCoordinate Z = _
  rw [← Adjunction.homEquiv_naturality_right_symm, hb]
  exact transpose_comp Q.projection.left g.left D.inclusion (pullbackRegular g.left)

end TorsorCoordinates

section LiftToExtension

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private extension_hom_ext extensionArrow extensionArrow_original extensionArrow_testScheme
  translationArrow pointTranslation_fst overlapTranslation_original
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private pullCongr_refl pullCongr_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}

private def liftToExtension {Z X : SchemeOver k} {R : TestAlgebra k}
    (r : Z ⟶ (testSpec k).obj (op R)) (x : Z ⟶ X) : Z ⟶ extensionAsSchemeOverField R X :=
  lift r x ≫ (extensionProductIso (Iso.refl _) X).inv

@[reassoc]
private theorem liftToExtension_original {Z X : SchemeOver k} {R : TestAlgebra k}
    (r : Z ⟶ (testSpec k).obj (op R)) (x : Z ⟶ X) :
    liftToExtension r x ≫ projectionToOriginal R X = x := by
  unfold liftToExtension
  rw [← extensionProductIso_snd (Iso.refl _) X, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]

@[reassoc]
private theorem liftToExtension_parameter {Z X : SchemeOver k} {R : TestAlgebra k}
    (r : Z ⟶ (testSpec k).obj (op R)) (x : Z ⟶ X) :
    liftToExtension r x ≫ projectionToTestScheme R X = r := by
  have hw : (extensionProductIso (Iso.refl _) X).hom ≫
      fst ((testSpec k).obj (op R)) X = projectionToTestScheme R X := by
    simpa only [Iso.refl_hom, Category.comp_id] using extensionProductIso_fst (Iso.refl _) X
  unfold liftToExtension
  rw [← hw, Category.assoc, Iso.inv_hom_id_assoc, lift_fst]

private theorem liftToExtension_naturality {Z X Y : SchemeOver k} {R : TestAlgebra k}
    (r : Z ⟶ (testSpec k).obj (op R)) (x : Z ⟶ X) (f : X ⟶ Y) :
    liftToExtension r x ≫ extensionArrow R f = liftToExtension r (x ≫ f) := by
  apply Over.OverMorphism.ext
  apply extension_hom_ext R
  · change ((liftToExtension r x ≫ extensionArrow R f) ≫ projectionToOriginal R Y).left =
      (liftToExtension r (x ≫ f) ≫ projectionToOriginal R Y).left
    rw [Category.assoc, extensionArrow_original, liftToExtension_original_assoc,
      liftToExtension_original]
  · change ((liftToExtension r x ≫ extensionArrow R f) ≫ projectionToTestScheme R Y).left =
      (liftToExtension r (x ≫ f) ≫ projectionToTestScheme R Y).left
    rw [Category.assoc, extensionArrow_testScheme, liftToExtension_parameter,
      liftToExtension_parameter]

private def liftTorsorToExtension {Z : SchemeOver k} {R : TestAlgebra k}
    (r : Z ⟶ (testSpec k).obj (op R)) (g : Z ⟶ G.val.X) :
    CovarianceArrow (trivialCovariance Z) ((flagLineData Q p χ h).extend R) where
  base := (liftToExtension r (g ≫ Q.projection)).left
  torsor := (liftToExtension r g).left
  overlap := (liftToExtension r (prod.lift g (1 : Z ⟶ P.negative.group.X))).left
  projection := by
    change (liftToExtension r g).left ≫ (extensionArrow R Q.projection).left =
      𝟙 _ ≫ (liftToExtension r (g ≫ Q.projection)).left
    rw [Category.id_comp]
    exact congrArg Over.Hom.left (liftToExtension_naturality r g Q.projection)
  first := by
    change (liftToExtension r (prod.lift g (1 : Z ⟶ P.negative.group.X))).left ≫
      (extensionArrow R prod.fst).left = 𝟙 _ ≫ (liftToExtension r g).left
    rw [Category.id_comp, ← Over.comp_left, liftToExtension_naturality, prod.lift_fst]
  second := by
    change (liftToExtension r (prod.lift g (1 : Z ⟶ P.negative.group.X))).left ≫
      (extensionArrow R (HomogeneousQuotient.rightMultiplication P.negative)).left =
      𝟙 _ ≫ (liftToExtension r g).left
    rw [Category.id_comp, ← Over.comp_left, liftToExtension_naturality, rightMultiplication_at_unit]
  multiplier := by
    change (liftToExtension r (prod.lift g (1 : Z ⟶ P.negative.group.X))).left.appTop
      ((projectionToOriginal R _).left.appTop (flagTransition p χ)) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left,
      liftToExtension_original]
    exact flagTransition_at_unit g

private theorem flagProjection_transport (ha : FlagActionCompatible a)
    {Z : SchemeOver k} (t : Z ⟶ P.torus.group.X) (g : Z ⟶ G.val.X) :
    actOn (torusAction (P := P) a) t (g ≫ Q.projection) =
      (lift (t ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X]) ≫ Q.projection := by
  rw [torus_actOn, Category.assoc, ha, ← Category.assoc, lift_map, Category.comp_id]

private theorem TransportMatches.postcomp {T : GroupScheme k} {X Z : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules} {M N : Z.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) {x y : Z ⟶ X}
    {u : Pull x F ⟶ M} {v : Pull y F ⟶ M}
    {u' : Pull x F ⟶ N} {v' : Pull y F ⟶ N} (c : M ⟶ N)
    (hu : u ≫ c = u') (hv : v ≫ c = v')
    (h : TransportMatches a θ t (x := x) (y := y) u v) :
    TransportMatches a θ t (x := x) (y := y) u' v' := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  rw [← hv, reassoc_of% hw, hu]

set_option maxHeartbeats 1400000 in
private theorem universalPointIso_coordinate (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (Z : SchemeOver k) (t : Z ⟶ P.torus.group.X) (g : Z ⟶ G.val.X) :
    let aT := torusAction (P := P) a
    let D := flagLineData Q p χ h
    let g' := lift (t ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X]
    ∃ w : actOn aT t (g ≫ Q.projection) = g' ≫ Q.projection,
      (transport aT (universalPointIso ha R j E) t (g ≫ Q.projection)).hom ≫
        (pullCongr D.sheaf w).hom ≫ flagLineCoordinate Q p χ h g' =
        flagLineCoordinate Q p χ h g := by
  intro aT D g'
  let C := trivialCovariance Z
  let s := t ≫ j.inv
  let v := liftTorsorToExtension (p := p) (χ := χ) (h := h) s g
  let r := liftToExtension s (g ≫ Q.projection)
  let u : GroupPoints G.val R := j.hom ≫ P.torus.inclusion.hom.hom
  let π := CovarianceArrow.extension D R
  let τ := (translation (p := p) (χ := χ) (h := h) ha R u).comp π
  have hr : v.base ≫ (extensionAsSchemeOverField R Q.scheme).hom = Z.hom := Over.w r
  have hw := universalTransport ha C R j E v Z.hom hr
  have ht : r ≫ projectionToTestScheme R Q.scheme ≫ j.hom = t := by
    rw [liftToExtension_parameter_assoc]
    simp [s]
  have hg : r ≫ projectionToOriginal R Q.scheme = g ≫ Q.projection :=
    liftToExtension_original _ _
  have hy : r ≫ translatedProjection a R u = g' ≫ Q.projection := by
    have ht' : r ≫ (projectionToTestScheme R Q.scheme ≫ u) = t ≫ P.torus.inclusion.hom.hom := by
      simpa only [u, Category.assoc] using
        congrArg (· ≫ P.torus.inclusion.hom.hom) ht
    change r ≫ (translationArrow R a.smul u ≫ projectionToOriginal R Q.scheme) = _
    rw [translation_base_original, ← Category.assoc, comp_lift, ht', hg]
    exact (torus_actOn (a := a) t (g ≫ Q.projection)).symm.trans (flagProjection_transport ha t g)
  have htor : (v.comp τ).torsor = (torsorLiftArrow (p := p) (χ := χ) (h := h) g').torsor := by
    change (liftToExtension s g).left ≫ pointTranslation μ[G.val.X] R u ≫
      extensionProjection R G.val.X = g'.left
    have hh := pointTranslation_fst R μ[G.val.X] u
    have ht' : liftToExtension s g ≫ (projectionToTestScheme R G.val.X ≫ u) =
        t ≫ P.torus.inclusion.hom.hom := by
      rw [← Category.assoc, liftToExtension_parameter]
      change (t ≫ j.inv) ≫ j.hom ≫ P.torus.inclusion.hom.hom = _
      rw [Category.assoc, Iso.inv_hom_id_assoc]
    have he : liftToExtension s g ≫
        lift (projectionToTestScheme R G.val.X ≫ u) (projectionToOriginal R G.val.X) ≫
          μ[G.val.X] = g' := by
      rw [← Category.assoc, comp_lift, ht', liftToExtension_original]
    exact (congrArg ((liftToExtension s g).left ≫ ·) hh).trans (congrArg Over.Hom.left he)
  have w₀ := (v.comp π).pull_congr (torsorLiftArrow (p := p) (χ := χ) (h := h) g)
    (congrArg Over.Hom.left hg) (congrArg Over.Hom.left (liftToExtension_original s g))
  have w₁ := (v.comp τ).pull_congr (torsorLiftArrow (p := p) (χ := χ) (h := h) g')
    (congrArg Over.Hom.left hy) htor
  have he := compareTransport (T := P.torus.group) (X := Q.scheme) (Z := Z)
    (F := D.sheaf) (H := C.sheaf) aT (universalPointIso ha R j E)
    (u := (v.comp π).pull) (v := (v.comp τ).pull)
    (u' := (torsorLiftArrow (p := p) (χ := χ) (h := h) g).pull)
    (v' := (torsorLiftArrow (p := p) (χ := χ) (h := h) g').pull) ht hg hy w₀ w₁ hw
  exact TransportMatches.postcomp (T := P.torus.group) (X := Q.scheme) (Z := Z)
    (F := D.sheaf) (M := C.sheaf) (N := structureModule Z.left)
    aT (universalPointIso ha R j E) t
    (x := g ≫ Q.projection) (y := g' ≫ Q.projection)
    (trivialCovarianceCoordinate Z)
    (torsorLiftArrow_coordinate (p := p) (χ := χ) (h := h) g)
    (torsorLiftArrow_coordinate (p := p) (χ := χ) (h := h) g') he

end LiftToExtension

section TransportLaws

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private pointTranslation_one translationArrow
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private comparePull pullCongr_refl pullCongr_trans transport_congr_point
  evalPullIso transport_eq_evalPullIso pullback_map_evalPullIso_to
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k]

private theorem actOn_comp {T : GroupScheme k} {X Z W : SchemeOver k} (a : ModObj T.X X)
    (f : Z ⟶ W) (t : W ⟶ T.X) (x : W ⟶ X) :
    f ≫ actOn a t x = actOn a (f ≫ t) (f ≫ x) := by
  simp only [actOn, ← Category.assoc, comp_lift]

private theorem transport_pullback {T : GroupScheme k} {X Z W : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (f : Z ⟶ W)
    (t : W ⟶ T.X) (x : W ⟶ X) :
    (Scheme.Modules.pullback f.left).map (transport a θ t x).hom ≫
      (comparePull F f (actOn a t x) (actOn_comp a f t x)).hom =
    (pullComp F f x).hom ≫ (transport a θ (f ≫ t) (f ≫ x)).hom := by
  rw [transport_eq_evalPullIso, transport_eq_evalPullIso]
  exact pullback_map_evalPullIso_to θ (lift t x) (lift_snd t x) rfl f
    (comp_lift f t x) rfl (actOn_comp a f t x) (lift_snd _ _) rfl

private theorem transport_pullback_to {T : GroupScheme k} {X Z W : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (f : Z ⟶ W)
    (t : W ⟶ T.X) (x : W ⟶ X) {t' : Z ⟶ T.X} {x' : Z ⟶ X}
    (ht : f ≫ t = t') (hx : f ≫ x = x') (hy : f ≫ actOn a t x = actOn a t' x') :
    (Scheme.Modules.pullback f.left).map (transport a θ t x).hom ≫
      (comparePull F f (actOn a t x) hy).hom =
    (comparePull F f x hx).hom ≫ (transport a θ t' x').hom := by
  subst t' x'
  have hc : (comparePull F f x (rfl : f ≫ x = f ≫ x)).hom = (pullComp F f x).hom := by
    simp only [comparePull, Iso.trans_hom, pullCongr_refl, Category.comp_id]
  rw [hc]
  exact transport_pullback a θ f t x

private theorem evalPullIso_trans {X Z W : SchemeOver k} {F : X.left.Modules}
    (f : Z ⟶ W) {x₀ x₁ x₂ : W ⟶ X} {y₀ y₁ y₂ : Z ⟶ X}
    (h₀ : f ≫ x₀ = y₀) (h₁ : f ≫ x₁ = y₁) (h₂ : f ≫ x₂ = y₂)
    (e₁ : Pull x₀ F ≅ Pull x₁ F) (e₂ : Pull x₁ F ≅ Pull x₂ F) :
    evalPullIso (e₁ ≪≫ e₂) f h₀ h₂ =
      evalPullIso e₁ f h₀ h₁ ≪≫ evalPullIso e₂ f h₁ h₂ := by
  apply Iso.ext
  simp only [evalPullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

private theorem evalPullIso_pullCongr {X Z W : SchemeOver k} {F : X.left.Modules}
    (f : Z ⟶ W) {x₁ x₂ : W ⟶ X} {y₁ y₂ : Z ⟶ X}
    (h₁ : f ≫ x₁ = y₁) (h₂ : f ≫ x₂ = y₂) (e : x₁ = x₂) (h : y₁ = y₂) :
    evalPullIso (pullCongr F e) f h₁ h₂ = pullCongr F h := by
  subst x₂ y₁ y₂
  apply Iso.ext
  let L := Scheme.Modules.pullback f.left
  let e := comparePull F f x₁ (rfl : f ≫ x₁ = f ≫ x₁)
  change e.inv ≫ L.map (𝟙 (Pull x₁ F)) ≫ e.hom = 𝟙 _
  rw [L.map_id, Category.id_comp, e.inv_hom_id]

private theorem evalPullIso_transport {T : GroupScheme k} {X Z W : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (f : Z ⟶ W)
    (t : W ⟶ T.X) (x : W ⟶ X) {t' : Z ⟶ T.X} {x' : Z ⟶ X}
    (ht : f ≫ t = t') (hx : f ≫ x = x') (hy : f ≫ actOn a t x = actOn a t' x') :
    evalPullIso (transport a θ t x) f hx hy = transport a θ t' x' := by
  apply Iso.ext
  change (comparePull F f x hx).inv ≫
    (Scheme.Modules.pullback f.left).map (transport a θ t x).hom ≫
    (comparePull F f (actOn a t x) hy).hom = _
  rw [transport_pullback_to a θ f t x ht hx hy, Iso.inv_hom_id_assoc]

private theorem evaluateComposition {X Z W : SchemeOver k} {F : X.left.Modules}
    (f : Z ⟶ W) {x₀ x₁ x₂ x₃ : W ⟶ X} {y₀ y₁ y₂ y₃ : Z ⟶ X}
    (h₀ : f ≫ x₀ = y₀) (h₁ : f ≫ x₁ = y₁) (h₂ : f ≫ x₂ = y₂) (h₃ : f ≫ x₃ = y₃)
    (a : Pull x₀ F ≅ Pull x₁ F) (b : Pull x₁ F ≅ Pull x₂ F)
    (c : Pull x₂ F ≅ Pull x₃ F) (d : Pull x₀ F ≅ Pull x₃ F)
    (w : ComposesTo a.hom b.hom c.hom d.hom) :
    ComposesTo (evalPullIso a f h₀ h₁).hom (evalPullIso b f h₁ h₂).hom
      (evalPullIso c f h₂ h₃).hom (evalPullIso d f h₀ h₃).hom := by
  have e : a ≪≫ b ≪≫ c = d := Iso.ext w
  have h := congrArg (fun i : Pull x₀ F ≅ Pull x₃ F => evalPullIso i f h₀ h₃) e
  rw [evalPullIso_trans f h₀ h₁ h₃, evalPullIso_trans f h₁ h₂ h₃] at h
  exact congrArg Iso.hom h

set_option maxHeartbeats 1600000 in
private theorem transport_composition_pullback {T : GroupScheme k} {X Z W : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (f : Z ⟶ W)
    (s t r : W ⟶ T.X) (x : W ⟶ X)
    (w : actOn a s (actOn a t x) = actOn a r x)
    (hw : ComposesTo (transport a θ t x).hom (transport a θ s (actOn a t x)).hom
      (pullCongr F w).hom (transport a θ r x).hom) :
    ∃ w' : actOn a (f ≫ s) (actOn a (f ≫ t) (f ≫ x)) =
        actOn a (f ≫ r) (f ≫ x),
      ComposesTo (transport a θ (f ≫ t) (f ≫ x)).hom
        (transport a θ (f ≫ s) (actOn a (f ≫ t) (f ≫ x))).hom
        (pullCongr F w').hom (transport a θ (f ≫ r) (f ≫ x)).hom := by
  let x₁ := actOn a t x
  let x₂ := actOn a s x₁
  let x₃ := actOn a r x
  let y := f ≫ x
  let y₁ := actOn a (f ≫ t) y
  let y₂ := actOn a (f ≫ s) y₁
  let y₃ := actOn a (f ≫ r) y
  let h₁ : f ≫ x₁ = y₁ := actOn_comp a f t x
  let h₂ : f ≫ x₂ = y₂ := (actOn_comp a f s x₁).trans (congrArg (actOn a (f ≫ s)) h₁)
  let h₃ : f ≫ x₃ = y₃ := actOn_comp a f r x
  let w' := h₂.symm.trans ((congrArg (f ≫ ·) w).trans h₃)
  refine ⟨w', ?_⟩
  have H := evaluateComposition f rfl h₁ h₂ h₃
    (transport a θ t x) (transport a θ s x₁) (pullCongr F w) (transport a θ r x) hw
  rw [evalPullIso_transport a θ f t x rfl rfl h₁,
    evalPullIso_transport a θ f s x₁ rfl h₁ h₂,
    evalPullIso_pullCongr f h₂ h₃ w w',
    evalPullIso_transport a θ f r x rfl rfl h₃] at H
  exact H

private theorem transport_multiplication_pullback {T : GroupScheme k} {X Z W : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (f : Z ⟶ W)
    (s t : W ⟶ T.X) (x : W ⟶ X)
    (w : actOn a s (actOn a t x) = actOn a (s * t) x)
    (hw : TransportComposition θ s t x w) :
    ∃ w' : actOn a (f ≫ s) (actOn a (f ≫ t) (f ≫ x)) =
        actOn a ((f ≫ s) * (f ≫ t)) (f ≫ x),
      TransportComposition θ (f ≫ s) (f ≫ t) (f ≫ x) w' := by
  let law (r : Z ⟶ T.X) := ∃ w' : actOn a (f ≫ s) (actOn a (f ≫ t) (f ≫ x)) =
      actOn a r (f ≫ x),
    ComposesTo (transport a θ (f ≫ t) (f ≫ x)).hom
      (transport a θ (f ≫ s) (actOn a (f ≫ t) (f ≫ x))).hom
      (pullCongr F w').hom (transport a θ r (f ≫ x)).hom
  have h : law (f ≫ (s * t)) := transport_composition_pullback a θ f s t (s * t) x w hw
  exact Eq.mp (congrArg law (MonObj.comp_mul f s t)) h

private theorem transportComposition_of_compatible_coordinates {T : GroupScheme k}
    {X Z : SchemeOver k} (a : ModObj T.X X) {F : X.left.Modules} {M : Z.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (s t : Z ⟶ T.X) (x : Z ⟶ X)
    {y z : Z ⟶ X} (u : Pull x F ⟶ M) (v : Pull y F ⟶ M) (c : Pull z F ⟶ M) (hc : Mono c)
    (H₁ : TransportMatches a θ t (x := x) (y := y) u v)
    (H₂ : TransportMatches a θ s (x := y) (y := z) v c)
    (H₃ : TransportMatches a θ (s * t) (x := x) (y := z) u c) :
    ∃ w : actOn a s (actOn a t x) = actOn a (s * t) x, TransportComposition θ s t x w := by
  obtain ⟨ht, ht'⟩ := H₁
  obtain ⟨hs, hs'⟩ := H₂
  obtain ⟨hm, hm'⟩ := H₃
  subst ht hs
  rw [pullCongr_refl, Category.id_comp] at ht' hs'
  refine ⟨hm.symm, ?_⟩
  unfold TransportComposition ComposesTo
  have hcancel : (pullCongr F hm.symm).hom ≫ (pullCongr F hm).hom ≫ c = c := by
    rw [reassoc_of% (pullCongr_trans F hm.symm hm)]
    change 𝟙 _ ≫ c = c
    exact Category.id_comp c
  apply (cancel_mono ((pullCongr F hm).hom ≫ c)).mp
  simp only [Category.assoc, hcancel, hs', ht', hm']

section Flag

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}

private theorem translatedProjection_one (S : TestAlgebra k) :
    translatedProjection a S (1 : GroupPoints G.val S) = projectionToOriginal S Q.scheme := by
  let := a
  have hf : translationArrow S a.smul (1 : GroupPoints G.val S) = 𝟙 _ :=
    Over.OverMorphism.ext (pointTranslation_one (H := G.val.X) (X := Q.scheme) S)
  unfold translatedProjection
  rw [hf, Category.id_comp]

set_option maxHeartbeats 1800000 in
private theorem universalPointIso_mul_over (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (S : TestAlgebra k) (s₀ t₀ : GroupPoints P.torus.group S) :
    let b := torusAction (P := P) a
    let q := projectionToTestScheme S Q.scheme
    let x := translatedProjection a S (1 : GroupPoints G.val S)
    let s := q ≫ s₀
    let t := q ≫ t₀
    ∃ w : actOn b s (actOn b t x) = actOn b (s * t) x,
      TransportComposition (universalPointIso ha R j E) s t x w := by
  intro b q x s t
  let D := flagLineData Q p χ h
  let F := D.sheaf
  let z : GroupPoints G.val S := 1
  let θ := universalPointIso ha R j E
  let i := includeTorusPoint P S
  let C := translatedPull (p := p) (χ := χ) (h := h) ha S
  have h₀ : i t₀ * z = i t₀ := mul_one _
  have h₁ : i (s₀ * t₀) * z = i s₀ * i t₀ := by
    rw [mul_one]
    exact MonObj.mul_comp s₀ t₀ _
  have idcomp : q ≫ (s₀ * t₀) = s * t := MonObj.comp_mul _ _ _
  have hT₀ := specializedTransport_at ha R j E S t₀ z (i t₀) t rfl h₀
  have hT₁ := specializedTransport_at ha R j E S s₀ (i t₀) (i s₀ * i t₀) s rfl rfl
  have hT₂ := specializedTransport_at ha R j E S (s₀ * t₀) z
    (i s₀ * i t₀) (s * t) idcomp h₁
  obtain ⟨eS⟩ := flagCohomologyBaseChange Q p χ h S
  let δ := translation (p := p) (χ := χ) (h := h) ha S (i s₀ * i t₀)
  let π := CovarianceArrow.extension D S
  have : IsIso δ.pull := translation_pull_isIso ha S _
  have : IsIso π.pull := CovarianceArrow.extension_pull_isIso eS
  have : IsIso (C (i s₀ * i t₀)) := CovarianceArrow.comp_pull_isIso δ π
  have hmono : Mono (C (i s₀ * i t₀)) := inferInstance
  exact transportComposition_of_compatible_coordinates (T := P.torus.group) (X := Q.scheme)
    (Z := extensionAsSchemeOverField S Q.scheme) (F := F) (M := (D.extend S).sheaf)
    b θ s t x (y := translatedProjection a S (i t₀))
    (z := translatedProjection a S (i s₀ * i t₀))
    (C z) (C (i t₀)) (C (i s₀ * i t₀)) hmono hT₀ hT₁ hT₂

end Flag

end TransportLaws

section Linearization

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private translationArrow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private evalPullIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.EquivariantAffineModules

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}

private theorem torus_affine : IsAffine P.torus.group.X.left := by
  let := G.property.1
  let := P.torus.isClosedImmersion
  exact isAffine_of_isAffineHom P.torus.inclusion.hom.hom.left

set_option maxHeartbeats 1000000 in
private theorem universalPointIso_mul (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (Z : SchemeOver k) (s t : Z ⟶ P.torus.group.X) (x : Z ⟶ Q.scheme) :
    let b := torusAction (P := P) a
    ∃ w : actOn b s (actOn b t x) = actOn b (s * t) x,
      TransportComposition (universalPointIso ha R j E) s t x w := by
  let T := P.torus.group.X
  let : IsAffine T.left := torus_affine (P := P)
  have hh := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst T T) (snd T T)) (CartesianMonoidalCategory.tensorProductIsBinaryProduct T T)
  have hT : IsAffine (T ⊗ T).left := IsAffine.of_isPullback hh
  obtain ⟨S₀, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hT
  let S : TestAlgebra k := S₀.unop
  let b := torusAction (P := P) a
  let s₀ : GroupPoints P.torus.group S := e.hom ≫ fst T T
  let t₀ : GroupPoints P.torus.group S := e.hom ≫ snd T T
  let f := liftToExtension (lift s t ≫ e.inv) x
  let q := projectionToTestScheme S Q.scheme
  let x₀ := translatedProjection a S (1 : GroupPoints G.val S)
  let θ := universalPointIso ha R j E
  have hs : f ≫ (q ≫ s₀) = s := by
    change f ≫ q ≫ e.hom ≫ fst T T = s
    rw [liftToExtension_parameter_assoc, Category.assoc, Iso.inv_hom_id_assoc, lift_fst]
  have ht : f ≫ (q ≫ t₀) = t := by
    change f ≫ q ≫ e.hom ≫ snd T T = t
    rw [liftToExtension_parameter_assoc, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]
  have hx : f ≫ x₀ = x := by
    exact (congrArg (f ≫ ·) (translatedProjection_one (a := a) S)).trans
      (liftToExtension_original _ _)
  have H := universalPointIso_mul_over ha R j E S s₀ t₀
  obtain ⟨w, hw⟩ := H
  have H' := transport_multiplication_pullback b θ f (q ≫ s₀) (q ≫ t₀) x₀ w hw
  -- The property depends only on the three pulled-back maps.
  let predicate (s t : Z ⟶ T) (x : Z ⟶ Q.scheme) :=
    ∃ w : actOn b s (actOn b t x) = actOn b (s * t) x,
      TransportComposition θ s t x w
  change predicate (f ≫ (q ≫ s₀)) (f ≫ (q ≫ t₀)) (f ≫ x₀) at H'
  rw [hs, ht, hx] at H'
  exact H'

private def IsIdentityTransport {T : GroupScheme k} {X Z : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) (x : Z ⟶ X) : Prop :=
  ∃ w : actOn a t x = x, (transport a θ t x).hom ≫ (pullCongr F w).hom = 𝟙 _

private theorem transport_unit_pullback {T : GroupScheme k} {X Z W : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (f : Z ⟶ W)
    (t : W ⟶ T.X) (x : W ⟶ X) {t' : Z ⟶ T.X} {x' : Z ⟶ X}
    (ht : f ≫ t = t') (hx : f ≫ x = x')
    (u : IsIdentityTransport a θ t x) :
    IsIdentityTransport a θ t' x' := by
  obtain ⟨w, hw⟩ := u
  let hy : f ≫ actOn a t x = actOn a t' x' :=
    (actOn_comp a f t x).trans (congrArg₂ (actOn a) ht hx)
  let w' : actOn a t' x' = x' := hy.symm.trans ((congrArg (f ≫ ·) w).trans hx)
  have e : transport a θ t x ≪≫ pullCongr F w = pullCongr F (rfl : x = x) := Iso.ext hw
  have he := congrArg (fun e : Pull x F ≅ Pull x F ↦ evalPullIso e f hx hx) e
  rw [evalPullIso_trans f hx hy hx, evalPullIso_transport a θ f t x ht hx hy,
    evalPullIso_pullCongr f hy hx w w', evalPullIso_pullCongr f hx hx rfl rfl] at he
  exact ⟨w', congrArg Iso.hom he⟩

private theorem transport_unit_of_coordinates {T : GroupScheme k} {X Z : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules} {M : Z.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Z ⟶ T.X) (x : Z ⟶ X)
    (c : Pull x F ⟶ M) [Mono c] (h : TransportMatches a θ t (x := x) (y := x) c c) :
    IsIdentityTransport a θ t x := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, (cancel_mono c).mp ?_⟩
  simpa only [Category.assoc, Category.id_comp] using hw

set_option maxHeartbeats 650000 in
private theorem universalPointIso_unit_over (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R) :
    let W := extensionAsSchemeOverField R Q.scheme
    let b := torusAction (P := P) a
    let z : GroupPoints G.val R := 1
    let x := translatedProjection a R z
    IsIdentityTransport b (universalPointIso ha R j E) (1 : W ⟶ P.torus.group.X) x := by
  intro W b z x
  let F := flagLineSheaf Q p χ h
  let T := P.torus.group
  let t : GroupPoints T R := 1
  let θ := universalPointIso ha R j E
  let C := translatedPull (p := p) (χ := χ) (h := h) ha R z
  let q := projectionToTestScheme R Q.scheme
  have ht : q ≫ t = (1 : W ⟶ T.X) := MonObj.comp_one q
  have hg : includeTorusPoint P R t * z = z := by
    exact (mul_one (includeTorusPoint P R t)).trans (MonObj.one_comp P.torus.inclusion.hom.hom)
  have hC := specializedTransport_at ha R j E R t z z 1 ht hg
  have : IsIso (translation (p := p) (χ := χ) (h := h) ha R z).pull :=
    translation_pull_isIso ha R z
  have : IsIso (CovarianceArrow.extension (flagLineData Q p χ h) R).pull :=
    CovarianceArrow.extension_pull_isIso E
  have : IsIso C := CovarianceArrow.comp_pull_isIso _ _
  exact transport_unit_of_coordinates (T := T) (X := Q.scheme) (Z := W)
    (F := F) b θ 1 x C hC

set_option maxHeartbeats 650000 in
private theorem universalPointIso_unit (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (Z : SchemeOver k) (x : Z ⟶ Q.scheme) :
    let b := torusAction (P := P) a
    IsIdentityTransport b (universalPointIso ha R j E) 1 x := by
  intro b
  let T := P.torus.group
  let W := extensionAsSchemeOverField R Q.scheme
  let F := flagLineSheaf Q p χ h
  let t : W ⟶ T.X := 1
  let t' : Z ⟶ T.X := 1
  let θ := universalPointIso ha R j E
  let f := liftToExtension (t' ≫ j.inv) x
  let x₀ := translatedProjection a R (1 : GroupPoints G.val R)
  have hx : f ≫ x₀ = x :=
    (congrArg (f ≫ ·) (translatedProjection_one (a := a) R)).trans
      (liftToExtension_original _ _)
  have ht : f ≫ t = t' := MonObj.comp_one f
  have hunit : IsIdentityTransport b θ t x₀ := universalPointIso_unit_over ha R j E
  exact transport_unit_pullback (T := T) (X := Q.scheme) (Z := Z) (W := W) (F := F)
    b θ f t x₀ (t' := t') (x' := x) ht hx hunit

private def constructedLinearization (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R) :
    Linearization (torusAction (P := P) a) (flagLineSheaf Q p χ h) where
  iso := universalPointIso ha R j E
  unit Z x := universalPointIso_unit ha R j E Z x
  mul Z s t x := universalPointIso_mul ha R j E Z s t x

end Linearization

section CohomologyComparison

open private extensionAsSchemeOverField projectionToOriginal projectionToTestScheme
  from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private translationArrow pointTranslation_one
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {p : BorelProjection P} {χ : Character P.torus.group}
variable {h : FlagKernelPair Q} {a : ModObj G.val.X Q.scheme}

private theorem reverse_transport {C : Type*} [Category* C] {A B D U V H : C}
    (t : A ≅ B) (w : U ≅ B) (c : V ≅ U) (i : V ≅ D) (e : A ≅ H)
    (δ : D ⟶ H)
    (he : t.hom ≫ w.inv ≫ c.inv ≫ i.hom ≫ δ = e.hom) :
    i.inv ≫ c.hom ≫ w.hom ≫ t.inv ≫ e.hom = δ := by
  rw [← he]
  simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

private theorem translatedExtension_one (ha : FlagActionCompatible a) (S : TestAlgebra k) :
    let D := flagLineData Q p χ h
    let π := CovarianceArrow.extension D S
    let t := translation (p := p) (χ := χ) (h := h) ha S (1 : GroupPoints G.val S)
    let w := translatedProjection_one (a := a) S
    (pullCongr D.sheaf w).hom ≫ π.pull = (t.comp π).pull := by
  let := a
  let : ModObj G.val.X G.val.X := ModObj.regular G.val.X
  dsimp only
  let D := flagLineData Q p χ h
  let π := CovarianceArrow.extension D S
  let t := translation (p := p) (χ := χ) (h := h) ha S (1 : GroupPoints G.val S)
  have hb : (t.comp π).base = π.base :=
    congrArg Over.Hom.left (translatedProjection_one (a := a) S)
  have ht : (t.comp π).torsor = π.torsor := by
    change pointTranslation μ[G.val.X] S (1 : GroupPoints G.val S) ≫
      extensionProjection S G.val.X = extensionProjection S G.val.X
    exact (congrArg (· ≫ extensionProjection S G.val.X)
      (pointTranslation_one (H := G.val.X) (X := G.val.X) S)).trans (Category.id_comp _)
  exact (t.comp π).pull_congr π hb ht

private def inverseTransportCoefficient {X Y : SchemeOver k} (F : X.left.Modules)
    (f : Y ⟶ Y) (x : Y ⟶ X) {M : Y.left.Modules} (e : Pull x F ≅ M) {y : Y ⟶ X}
    (t : Pull x F ≅ Pull y F) (w : f ≫ x = y) : M ⟶ (pushforward f.left).obj M :=
  ((adj f.left).homEquiv M M) ((Scheme.Modules.pullback f.left).map e.inv ≫
    (pullComp F f x).hom ≫ (pullCongr F w).hom ≫ t.inv ≫ e.hom)

private theorem inverseTransportCoefficient_eq {X Y : SchemeOver k} (F : X.left.Modules)
    (f : Y ⟶ Y) (x : Y ⟶ X) {M : Y.left.Modules} (e : Pull x F ≅ M) {y : Y ⟶ X}
    (t : Pull x F ≅ Pull y F) (w : f ≫ x = y) (δ : Pull f M ⟶ M)
    (h : t.hom ≫ (pullCongr F w).inv ≫ (pullComp F f x).inv ≫
      (Scheme.Modules.pullback f.left).map e.hom ≫ δ = e.hom) :
    inverseTransportCoefficient F f x e t w = ((adj f.left).homEquiv M M) δ := by
  exact congrArg ((adj f.left).homEquiv M M)
    (reverse_transport t (pullCongr F w) (pullComp F f x)
      ((Scheme.Modules.pullback f.left).mapIso e) e δ h)

private theorem pullCongr_symm_inv {X Y : SchemeOver k} (F : X.left.Modules)
    {x y : Y ⟶ X} (w : x = y) : (pullCongr F w.symm).inv = (pullCongr F w).hom := by
  cases w
  rfl

private theorem inverseTransportCoefficient_of_match {T : GroupScheme k} {X Y : SchemeOver k}
    (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F) (t : Y ⟶ T.X)
    (f : Y ⟶ Y) (x : Y ⟶ X) {M : Y.left.Modules} (e : Pull x F ≅ M)
    (α : M ⟶ (pushforward f.left).obj M) (u : Pull x F ⟶ M) (v : Pull (f ≫ x) F ⟶ M)
    (hu : e.hom = u)
    (hv : v = (pullComp F f x).inv ≫ (Scheme.Modules.pullback f.left).map e.hom ≫
      ((adj f.left).homEquiv M M).symm α)
    (h : TransportMatches a θ t (x := x) (y := f ≫ x) u v) :
    ∃ w : f ≫ x = actOn a t x, inverseTransportCoefficient F f x e (transport a θ t x) w = α := by
  rw [← hu, hv] at h
  obtain ⟨w, hw⟩ := h
  let equiv := (adj f.left).homEquiv M M
  refine ⟨w.symm, (inverseTransportCoefficient_eq F f x e (transport a θ t x) w.symm
    (equiv.symm α) ?_).trans (equiv.apply_symm_apply α)⟩
  rw [pullCongr_symm_inv F w]
  exact hw

set_option maxHeartbeats 1900000 in
private theorem universalPointIso_coefficient (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R)
    (S : TestAlgebra k) (t : GroupPoints P.torus.group S)
    (ES : (flagLineData Q p χ h).ScalarExtension S) :
    let D := flagLineData Q p χ h
    let g : GroupPoints G.val S := t ≫ P.torus.inclusion.hom.hom
    let x := projectionToOriginal S Q.scheme
    let y := projectionToTestScheme S Q.scheme
    let f := translationArrow S a.smul g⁻¹
    let b := torusAction (P := P) a
    let e : Pull x D.sheaf ≅ (D.extend S).sheaf := @asIso _ _ _ _ _ ES.sheafIso
    ∃ w : f ≫ x = actOn b (y ≫ t⁻¹) x,
      inverseTransportCoefficient D.sheaf f x e (transport b (universalPointIso ha R j E) (y ≫ t⁻¹) x) w =
        (translation (p := p) (χ := χ) (h := h) ha S g⁻¹).coeff := by
  intro D g x y f aT e
  let θ := universalPointIso ha R j E
  let π := CovarianceArrow.extension D S
  let v := translation (p := p) (χ := χ) (h := h) ha S g⁻¹
  let z : GroupPoints G.val S := 1
  have hz : includeTorusPoint P S t⁻¹ * z = g⁻¹ :=
    (mul_one _).trans (GrpObj.inv_comp t _)
  have atOne := specializedTransport_at ha R j E S t⁻¹ z g⁻¹ (y ≫ t⁻¹) rfl hz
  have cmp : TransportMatches aT θ (y ≫ t⁻¹) (x := x) (y := f ≫ x)
      π.pull (v.comp π).pull :=
    compareTransport_source (T := P.torus.group) (X := Q.scheme)
      (Z := extensionAsSchemeOverField S Q.scheme) (F := D.sheaf) (M := (D.extend S).sheaf)
      aT θ (y ≫ t⁻¹) (x := translatedProjection a S z) (x' := x) (y := f ≫ x)
      (translatedPull (p := p) (χ := χ) (h := h) ha S z) π.pull (v.comp π).pull
      (translatedProjection_one (a := a) S)
      (translatedExtension_one (p := p) (χ := χ) (h := h) ha S) atOne
  let c := pullComp D.sheaf f x
  let iIso := (Scheme.Modules.pullback f.left).mapIso e
  have he : e.hom = π.pull := (CovarianceArrow.extension_pull ES).symm
  have hcomp : (v.comp π).pull = c.inv ≫ iIso.hom ≫ v.pull := by
    let L := Scheme.Modules.pullback f.left
    calc
      (v.comp π).pull = c.inv ≫ L.map π.pull ≫ v.pull := CovarianceArrow.pull_comp v π
      _ = c.inv ≫ iIso.hom ≫ v.pull :=
        congrArg (fun j => c.inv ≫ L.map j ≫ v.pull) he.symm
  exact inverseTransportCoefficient_of_match (T := P.torus.group) (X := Q.scheme)
    (Y := extensionAsSchemeOverField S Q.scheme) (F := D.sheaf) (M := (D.extend S).sheaf)
    aT θ (y ≫ t⁻¹) f x e v.coeff π.pull (v.comp π).pull he hcomp cmp

set_option maxHeartbeats 1200000 in
private theorem constructedLinearization_cohomology (ha : FlagActionCompatible a)
    (R : TestAlgebra k) (j : (testSpec k).obj (op R) ≅ P.torus.group.X)
    (E : (flagLineData Q p χ h).ScalarExtension R) :
    AgreesWithFlagCohomologyAction Q a p χ h (constructedLinearization ha R j E) := by
  intro S t ES
  let D := flagLineData Q p χ h
  let g : GroupPoints G.val S := t ≫ P.torus.inclusion.hom.hom
  let f := translationArrow S a.smul g⁻¹
  obtain ⟨w, hα⟩ := universalPointIso_coefficient ha R j E S t ES
  refine ⟨w, fun n => ?_⟩
  obtain ⟨m, hm, hcoord⟩ := translation_cohomology ha S g ES n
  refine ⟨m, ?_, hcoord⟩
  let m' := m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id S) rfl _).inv
  let induced (β : (D.extend S).sheaf ⟶ (pushforward f.left).obj (D.extend S).sheaf) :=
    IsCohomologyMap (RingHom.id S) f.left (pointTranslation_over a.smul S g⁻¹) β n m'
  exact Eq.mpr (congrArg induced hα) hm

/-- Left translation gives a torus linearization of the covariance sheaf.
It preserves the associated-line coordinate and induces the same derived
action as inverse point translation over every test algebra. -/
theorem flagCovarianceLinearization : FlagCovarianceLinearizationStatement.{u} := by
  intro k _ G P Q a p χ h ha
  obtain ⟨R₀, ⟨j⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr (torus_affine (P := P))
  let R : TestAlgebra k := R₀.unop
  obtain ⟨E⟩ := flagCohomologyBaseChange Q p χ h R
  exact ⟨constructedLinearization ha R j E, universalPointIso_coordinate ha R j E,
    constructedLinearization_cohomology ha R j E⟩

end CohomologyComparison

end

end LinearAlgebraicGroups.Representation.FlagCovarianceLinearization
