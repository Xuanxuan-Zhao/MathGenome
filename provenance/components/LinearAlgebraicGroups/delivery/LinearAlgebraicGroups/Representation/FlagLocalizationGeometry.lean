import Specs.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry
import LinearAlgebraicGroups.Flag.BruhatCells
import LinearAlgebraicGroups.Flag.SchubertClosures
import LinearAlgebraicGroups.Representation.FlagLineBundle
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.AlgebraicClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.FlagLocalizationGeometry

open _root_.LinearAlgebraicGroups.Specs
  (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.FlagLocalizationGeometry
open Specs.AbstractPairing (Datum Root)
open Specs.BruhatOrbitParametrization (Cell IsRepresentative FixedOver)
open Specs.CharacterDescent (Character)
open Specs.DatumAndWeyl (Identification)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.QuotientEmbedding (Presentation)

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open private vanishingSubschemeReduced from LinearAlgebraicGroups.Flag.SchubertClosures
open private splitTorusSmooth from LinearAlgebraicGroups.Reductive.WeylScheme
open private geometricallyReduced_of_smooth isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private abbrev openScheme (X : SchemeOver k) (V : X.left.Opens) : SchemeOver k :=
  Over.mk (V.ι ≫ X.hom)

private def openInclusion (X : SchemeOver k) (V : X.left.Opens) : openScheme X V ⟶ X :=
  Over.homMk V.ι

section Cotangent

private theorem ker_evalZero_eq_span_X {k I : Type*} [CommRing k] :
    RingHom.ker (MvPolynomial.aeval (R := k) (0 : I → k)).toRingHom =
      Ideal.span (Set.range (MvPolynomial.X : I → MvPolynomial I k)) := by
  let J := Ideal.span (Set.range (MvPolynomial.X : I → MvPolynomial I k))
  let ε := MvPolynomial.aeval (R := k) (0 : I → k)
  have hh : Ideal.Quotient.mkₐ k J = (Algebra.ofId k (MvPolynomial I k ⧸ J)).comp ε := by
    ext i
    show Ideal.Quotient.mk J (MvPolynomial.X i) = _
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))]
    simp [ε]
  apply le_antisymm
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ k J a = 0
    change ε a = 0 at ha
    rw [hh, AlgHom.comp_apply, ha, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ε (MvPolynomial.X i) = 0
    simp [ε]

/-- The variable classes form a ground-field basis of the cotangent space
at the origin of affine space. -/
theorem polynomialCotangentBasis {k I : Type*} [Field k] [Fintype I] :
    let ε := MvPolynomial.aeval (R := k) (0 : I → k)
    let m := RingHom.ker ε.toRingHom
    ∃ b : Module.Basis I k m.Cotangent,
      ∀ i, b i = m.toCotangent ⟨MvPolynomial.X i, by change MvPolynomial.aeval (R := k) (0 : I → k) (MvPolynomial.X i) = 0; simp⟩ := by
  classical
  let ε := MvPolynomial.aeval (R := k) (0 : I → k)
  let m := RingHom.ker ε.toRingHom
  let x (i : I) : m := ⟨MvPolynomial.X i, by simp [m, ε]⟩
  let v (i : I) := m.toCotangent (x i)
  let l (i : I) : m →ₗ[k] k :=
    ε.toLinearMap.comp <| (MvPolynomial.pderiv i).toLinearMap.comp (m.subtype.restrictScalars k)
  have hl (i : I) (a b : m) : l i (a * b) = 0 := by
    change ε (MvPolynomial.pderiv i (a.val * b.val)) = 0
    have ha : ε a.val = 0 := a.property
    have hb : ε b.val = 0 := b.property
    rw [MvPolynomial.pderiv_mul]
    simp only [map_add, map_mul, ha, hb, zero_mul, mul_zero, zero_add]
  let d (i : I) : m.Cotangent →ₗ[k] k := Ideal.Cotangent.lift (l i) (hl i)
  have hd (i j : I) : d i (v j) = if i = j then 1 else 0 := by
    change ε (MvPolynomial.pderiv i (MvPolynomial.X j)) = _
    rw [MvPolynomial.pderiv_X]
    simp [Pi.single_apply, eq_comm]
  have hi : LinearIndependent k v := by
    rw [Fintype.linearIndependent_iff]
    intro w hw i
    have he := congrArg (d i) hw
    simpa [map_sum, hd, smul_eq_mul] using he
  let V := Submodule.span k (Set.range v)
  have hscalar (a : MvPolynomial I k) (z : m.Cotangent) : a • z = ε a • z := by
    have ha : a - algebraMap k (MvPolynomial I k) (ε a) ∈ m := by
      change ε (_ - _) = 0
      simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    have hz := Ideal.Cotangent.smul_eq_zero_of_mem ha z
    rw [sub_smul, sub_eq_zero, algebraMap_smul] at hz
    exact hz
  let W : Submodule (MvPolynomial I k) m.Cotangent :=
    { V.toAddSubmonoid with
      smul_mem' := fun a z hz => show a • z ∈ V by
        rw [hscalar]
        exact V.smul_mem _ hz }
  let N := (W.comap m.toCotangent).map m.subtype
  have hN : (m : Submodule (MvPolynomial I k) (MvPolynomial I k)) ≤ N := by
    have hgen : m = Ideal.span (Set.range (MvPolynomial.X : I → MvPolynomial I k)) :=
      ker_evalZero_eq_span_X
    rw [hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, Submodule.subset_span (Set.mem_range_self i), rfl⟩
  have hs : ⊤ ≤ V := by
    intro y _
    obtain ⟨a, rfl⟩ := m.toCotangent_surjective y
    obtain ⟨b, hb, he⟩ := hN a.property
    have e : b = a := Subtype.ext he
    subst b
    exact hb
  exact ⟨Module.Basis.mk hi hs, Module.Basis.mk_apply hi hs⟩

private def cotangentEquivOfAlgEquiv {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (m : Ideal A) (n : Ideal B) (e : A ≃ₐ[k] B)
    (h : ∀ r, e r ∈ n ↔ r ∈ m) : m.Cotangent ≃ₗ[k] n.Cotangent := by
  let f : m.Cotangent →ₗ[k] n.Cotangent :=
    m.mapCotangent n e.toAlgHom (fun x hx => (h x).2 hx)
  let g : n.Cotangent →ₗ[k] m.Cotangent :=
    n.mapCotangent m e.symm.toAlgHom (fun x hx => (h (e.symm x)).1 (by rw [e.apply_symm_apply]; exact hx))
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · ext z
    obtain ⟨r, rfl⟩ := n.toCotangent_surjective z
    apply congrArg n.toCotangent
    exact Subtype.ext (e.apply_symm_apply (r : B))
  · ext z
    obtain ⟨r, rfl⟩ := m.toCotangent_surjective z
    apply congrArg m.toCotangent
    exact Subtype.ext (e.symm_apply_apply (r : A))

variable {T : GroupScheme k} {X : SchemeOver k}

private def pointEvaluation (y : 𝟙_ (SchemeOver k) ⟶ X) :
    let A := Γ(X.left, ⊤)
    letI : Algebra k A := (groundRingHom X).toAlgebra
    A →ₐ[k] k := by
  letI : Algebra k Γ(X.left, ⊤) := (groundRingHom X).toAlgebra
  dsimp only
  let p : Γ((𝟙_ (SchemeOver k) : SchemeOver k).left, ⊤) ⟶ CommRingCat.of k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom
  refine ⟨(y.left.appTop ≫ p).hom, ?_⟩
  intro r
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop ≫
    y.left.appTop ≫ p) r = r
  have h : y.left ≫ X.hom = 𝟙 _ := Over.w y
  rw [← Scheme.Hom.comp_appTop_assoc, h, Scheme.Hom.id_appTop]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    𝟙 Γ(Spec (.of k), ⊤) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) r = r
  rw [Category.id_comp, Iso.inv_hom_id]
  rfl


/-- The variable classes give a cotangent basis on every chart with the
specified polynomial coordinates and origin. -/
theorem cotangentBasisOfCoordinates {a : ModObj T.X X}
    {I : Type u} [Fintype I] {o : 𝟙_ (SchemeOver k) ⟶ X}
    {ν : I → Character T} (p : PolynomialCoordinates a o ν) :
    letI : Algebra k Γ(X.left, ⊤) := (groundRingHom X).toAlgebra
    ∃ b : Module.Basis I k (RingHom.ker o.left.appTop.hom).Cotangent,
      ∀ i, (RingHom.ker o.left.appTop.hom).toCotangent
        ⟨p.coordinates (MvPolynomial.X i), p.vanishes i⟩ = b i := by
  letI : Algebra k Γ(X.left, ⊤) := (groundRingHom X).toAlgebra
  let e := p.coordinates
  let ε := MvPolynomial.aeval (R := k) (0 : I → k)
  let m := RingHom.ker ε.toRingHom
  let n := RingHom.ker o.left.appTop.hom
  have hε : (pointEvaluation o).comp e.toAlgHom = ε := by
    ext i
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (o.left.appTop (e (MvPolynomial.X i))) = _
    rw [show o.left.appTop (e (MvPolynomial.X i)) = 0 from p.vanishes i, map_zero]
    simp [ε]
  have hk (r : MvPolynomial I k) : e r ∈ n ↔ r ∈ m := by
    change o.left.appTop (e r) = 0 ↔ ε r = 0
    rw [← hε]
    change _ ↔ (Scheme.ΓSpecIso (CommRingCat.of k)).hom (o.left.appTop (e r)) = 0
    constructor
    · exact fun h => h ▸ map_zero _
    · intro h
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
      simpa only [map_zero] using h
  let e' := cotangentEquivOfAlgEquiv m n e hk
  obtain ⟨b, hb⟩ := polynomialCotangentBasis (k := k) (I := I)
  refine ⟨b.map e', fun i ↦ ?_⟩
  rw [Module.Basis.map_apply, hb]
  rfl

end Cotangent
section Geometry

variable {G : AffineAlgebraicGroup k} {X : SchemeOver k}

/-- A point over a field factors through any immersed subscheme whose
underlying image contains the point. -/
private theorem fieldPoint_lift {K : Type u} [Field K] [Algebra k K] {V X : SchemeOver k}
    (i : V ⟶ X) [IsImmersion i.left] (y : Over.mk (fieldSpecMap k K) ⟶ X)
    (hy : y.left (IsLocalRing.closedPoint K) ∈ Set.range i.left) :
    ∃ q : Over.mk (fieldSpecMap k K) ⟶ V, q ≫ i = y := by
  let p := pullback.fst i.left y.left
  let q := pullback.snd i.left y.left
  have hpb := IsPullback.of_hasPullback i.left y.left
  obtain ⟨v, hv⟩ := hy
  obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback hpb v
    (IsLocalRing.closedPoint K) hv
  let : Subsingleton (Over.mk (fieldSpecMap k K)).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  let : IsReduced (Over.mk (fieldSpecMap k K)).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  have hsurj : Function.Surjective q := by
    intro x
    exact ⟨z, hz.trans (Subsingleton.elim _ _)⟩
  let : Surjective q := ⟨hsurj⟩
  let : IsImmersion q := inferInstanceAs (IsImmersion (pullback.snd i.left y.left))
  let : IsClosedImmersion q :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hsurj.range_eq]; exact isClosed_univ)
  let : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  have he : (inv q ≫ p) ≫ i.left = y.left := by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  exact ⟨Over.homMk (inv q ≫ p)
    (by rw [← Over.w i, ← Category.assoc, he, Over.w y]), Over.OverMorphism.ext he⟩

private theorem productProjection_pullback (W : SchemeOver k) {X Y : SchemeOver k}
    (f : Y ⟶ X) :
    IsPullback (snd W Y) (W ◁ f) f (snd W X) := by
  have hw : snd W Y ≫ f = (W ◁ f) ≫ snd W X := by simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun c => lift (c.snd ≫ fst W X) c.fst) (fun _ => lift_snd _ _) (fun c => ?_)
    (fun c m hm hn => ?_))
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using c.condition
  · apply CartesianMonoidalCategory.hom_ext
    · have he := congrArg (· ≫ fst W X) hn
      simpa using he
    · simpa using hm

/-- The underlying range of an equivariant morphism is invariant under
the scheme action. This applies to cell immersions and fixed-point sections. -/
theorem action_preimage_range_of_equivariant {T : GroupScheme k} {X Y : SchemeOver k}
    {a : ModObj T.X X} {b : ModObj T.X Y}
    (f : Y ⟶ X) (hf : IsEquivariantMap a b f) :
    a.smul.left ⁻¹' Set.range f.left = (snd T.X X).left ⁻¹' Set.range f.left := by
  let p := snd T.X X
  let q := T.X ◁ f
  let h := (productProjection_pullback T.X f).flip.map (Over.forget (Spec (CommRingCat.of k)))
  have hq : Set.range q.left = p.left ⁻¹' Set.range f.left := by
    change Set.range ((Over.forget _).map q) = _
    rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ]
    exact Scheme.Pullback.range_fst _ _
  have hforward (z : (T.X ⊗ X).left) (hz : p.left z ∈ Set.range f.left) :
      a.smul.left z ∈ Set.range f.left := by
    obtain ⟨y, rfl⟩ : z ∈ Set.range q.left := hq.symm ▸ hz
    refine ⟨b.smul.left y, ?_⟩
    have hcomp : b.smul ≫ f = q ≫ a.smul := by simpa [IsEquivariantMap, q] using hf
    exact congrArg (fun m : T.X ⊗ Y ⟶ X => m.left y) hcomp
  let := a
  let r := lift (fst T.X X)⁻¹ a.smul
  have hs : r ≫ p = a.smul := lift_snd _ _
  have ha : r ≫ a.smul = p := by
    change (fst T.X X)⁻¹ • a.smul = p
    have e : a.smul = fst T.X X • p := by rw [Hom.smul_def, lift_fst_snd, Category.id_comp]
    rw [e, inv_smul_smul]
  ext z
  change a.smul.left z ∈ Set.range f.left ↔ p.left z ∈ Set.range f.left
  refine ⟨fun hz => ?_, hforward z⟩
  have hz' : p.left (r.left z) ∈ Set.range f.left :=
    ((congrArg (fun m : T.X ⊗ X ⟶ X => m.left z) hs).symm ▸ hz)
  exact (congrArg (fun m : T.X ⊗ X ⟶ X => m.left z) ha) ▸ hforward _ hz'


/-- A scheme-theoretically fixed rational point is an equivariant section
from the point with the trivial action. -/
theorem fixedOver_iff_equivariant_section {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (a : ModObj G.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    Specs.BruhatOrbitParametrization.FixedOver (T := T) a x ↔
      IsEquivariantMap (torusAction T a) (pointAction T.group) x := by
  let S := T.group.X
  let W := (𝟙_ (SchemeOver k))
  let i := T.inclusion.hom.hom
  have h : (𝟙 S ⊗ₘ x) ≫ (i ▷ X) = lift (fst S W ≫ i) (snd S W ≫ x) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [S, W, i]
  change lift (fst S W ≫ i) (snd S W ≫ x) ≫ a.smul = snd S W ≫ x ↔
    snd S W ≫ x = (𝟙 S ⊗ₘ x) ≫ (i ▷ X) ≫ a.smul
  rw [← Category.assoc, h, eq_comm]

/-- The complement of finitely many equivariant rational sections is an
invariant open. -/
theorem invariant_open_complement_of_fixed_sections {T : GroupScheme k} {I : Type u} [Finite I]
    (a : ModObj T.X X) (x : I → (𝟙_ (SchemeOver k) ⟶ X))
    (hx : ∀ j, IsEquivariantMap a (pointAction T) (x j)) :
    ∃ U : X.left.Opens, (U : Set X.left) = (⋃ j, Set.range (x j).left)ᶜ ∧
      a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U := by
  let S : Set X.left := ⋃ j, Set.range (x j).left
  have hS : IsClosed S := by
    apply isClosed_iUnion_of_finite
    intro j
    let : Subsingleton (𝟙_ (SchemeOver k) : SchemeOver k).left :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
    let : IsClosedImmersion (x j).left :=
      isClosedImmersion_of_comp_eq_id X.hom (x j).left (Over.w (x j))
    exact (x j).left.isClosedEmbedding.isClosed_range
  refine ⟨⟨Sᶜ, hS.isOpen_compl⟩, rfl, ?_⟩
  apply TopologicalSpace.Opens.ext
  change a.smul.left ⁻¹' Sᶜ = (snd T.X X).left ⁻¹' Sᶜ
  simp only [S, Set.preimage_compl, Set.preimage_iUnion]
  exact congrArg Set.compl (Set.iUnion_congr fun j => action_preimage_range_of_equivariant (x j) (hx j))


private theorem whiskerLeft_epi (W : SchemeOver k) {X Y : SchemeOver k} (f : X ⟶ Y)
    [Flat f.left] [Surjective f.left] : Epi (W ◁ f) := by
  have H' := (productProjection_pullback W f).map (Over.forget (Spec (CommRingCat.of k)))
  let : Flat (W ◁ f).left := MorphismProperty.of_isPullback H' (‹Flat f.left›)
  let : Surjective (W ◁ f).left := MorphismProperty.of_isPullback H' (‹Surjective f.left›)
  let : Epi (W ◁ f).left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

private theorem fixedOver_whiskerLeft {T : ClosedSubgroup G.val} {X Y Z : SchemeOver k}
    (a : ModObj G.val.X X) (y : Y ⟶ X) (f : Z ⟶ Y) [Epi (T.group.X ◁ f)] :
    FixedOver (T := T) a (f ≫ y) ↔ FixedOver (T := T) a y := by
  have hl : (T.group.X ◁ f) ≫
      lift (fst T.group.X Y ≫ T.inclusion.hom.hom) (snd T.group.X Y ≫ y) =
      lift (fst T.group.X Z ≫ T.inclusion.hom.hom) (snd T.group.X Z ≫ f ≫ y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change
    lift (fst T.group.X Z ≫ T.inclusion.hom.hom) (snd T.group.X Z ≫ f ≫ y) ≫ a.smul =
      snd T.group.X Z ≫ f ≫ y ↔ _
  rw [FixedOver, ← cancel_epi (T.group.X ◁ f), reassoc_of% hl, whiskerLeft_snd_assoc]

private theorem fixedOver_section_of_fields {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val) {X : SchemeOver k}
    (a : ModObj G.val.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (h : FixedOver (T := T) a (toUnit (Over.mk (fieldSpecMap k k)) ≫ x)) :
    FixedOver (T := T) a x := by
  let Y := Over.mk (fieldSpecMap k k)
  let f : Y ⟶ 𝟙_ (SchemeOver k) := toUnit Y
  let : Subsingleton ((𝟙_ (SchemeOver k) : SchemeOver k).left) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  let : Flat f.left := inferInstanceAs (Flat (fieldSpecMap k k))
  let : Surjective f.left := ⟨fun _ => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  let : Epi (T.group.X ◁ f) := whiskerLeft_epi T.group.X f
  exact (fixedOver_whiskerLeft a x f).mp h

private def cellOrigin {G : AffineAlgebraicGroup k} {T B U : ClosedSubgroup G.val}
    {Q : Presentation B} {a : ModObj G.val.X Q.scheme}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (C : Cell (T := T) Q a n U) :
    𝟙_ (SchemeOver k) ⟶ C.orbit :=
  η[U.group.X] ≫ C.orbitIso.hom

private theorem cellOrigin_comp {G : AffineAlgebraicGroup k} {T B U : ClosedSubgroup G.val}
    {Q : Presentation B} {a : ModObj G.val.X Q.scheme}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (C : Cell (T := T) Q a n U) :
    cellOrigin C ≫ C.orbitInclusion = n ≫ Q.projection := by
  change η[U.group.X] ≫ C.orbitIso.hom ≫ C.orbitInclusion = _
  rw [C.orbitIso_eq, ← Category.assoc, MonObj.comp_mul]
  have he : η[U.group.X] ≫ U.inclusion.hom.hom = 1 :=
    IsMonHom.one_hom U.inclusion.hom.hom
  rw [← Category.assoc, he, one_mul]
  have h : η[U.group.X] ≫ toUnit U.group.X = 𝟙 _ := Subsingleton.elim _ _
  rw [h, Category.id_comp]

/-- The fixed points in the split cells descend from an algebraic closure to
the named rational points over every extension field. -/
private theorem fixedOver_iff_of_cells {T B : ClosedSubgroup G.val}
    {Q : Presentation B} {a : ModObj G.val.X Q.scheme} {W : Type u}
    (n : W → (𝟙_ (SchemeOver k) ⟶ G.val.X)) (A : W → ClosedSubgroup G.val)
    (C : ∀ w, Cell (T := T) Q a (n w) (A w))
    (hdisj : ∀ w v, w ≠ v →
      Disjoint (Set.range (C w).orbitInclusion.left) (Set.range (C v).orbitInclusion.left))
    (hcover : (⋃ w, Set.range (C w).orbitInclusion.left) = Set.univ)
    (K : Type u) [Field K] [Algebra k K] (y : Over.mk (fieldSpecMap k K) ⟶ Q.scheme) :
    FixedOver (T := T) a y ↔ ∃! w, y = toUnit _ ≫ n w ≫ Q.projection := by
  let L := AlgebraicClosure K
  let φ := (algebraMap K L).comp (algebraMap k K)
  let : Algebra k L := φ.toAlgebra
  let e : Over.mk (fieldSpecMap k L) ⟶ Over.mk (fieldSpecMap k K) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K L))) (by
      exact (Spec.map_comp (CommRingCat.ofHom (algebraMap k K))
        (CommRingCat.ofHom (algebraMap K L))).symm)
  let : Flat e.left :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_free : Module.Flat K L))
  let : Subsingleton (Over.mk (fieldSpecMap k K)).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  let : Surjective e.left := ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  let : Epi e.left := Flat.epi_of_flat_of_surjective _
  let : Epi e := Over.epi_of_epi_left _
  let : Epi (T.group.X ◁ e) := whiskerLeft_epi _ _
  have ht : e ≫ toUnit (Over.mk (fieldSpecMap k K)) = toUnit (Over.mk (fieldSpecMap k L)) :=
    Subsingleton.elim _ _
  have ho (w : W) : cellOrigin (C w) ≫ (C w).orbitInclusion = n w ≫ Q.projection :=
    cellOrigin_comp (C w)
  have hrange {S : SchemeOver k} (w : W) (s : S.left) :
      (toUnit S ≫ n w ≫ Q.projection).left s ∈ Set.range (C w).orbitInclusion.left := by
    rw [← ho w, ← Category.assoc]
    exact ⟨(toUnit S ≫ cellOrigin (C w)).left s, rfl⟩
  constructor
  · intro hy
    have hp : y.left (IsLocalRing.closedPoint K) ∈ ⋃ w, Set.range (C w).orbitInclusion.left := by
      rw [hcover]
      exact Set.mem_univ _
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hp
    have hwp : (e ≫ y).left (IsLocalRing.closedPoint L) ∈ Set.range (C w).orbitInclusion.left := by
      have he : e.left (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint K :=
        Subsingleton.elim _ _
      change y.left (e.left (IsLocalRing.closedPoint L)) ∈ _
      rwa [he]
    let : IsImmersion (C w).orbitInclusion.left := (C w).orbitImmersion
    obtain ⟨q, hq⟩ := fieldPoint_lift (C w).orbitInclusion (e ≫ y) hwp
    have hyL := (fixedOver_whiskerLeft a y e).mpr hy
    have hyL' := ((C w).uniqueGeometricFixedPoint L q).mp (hq.symm ▸ hyL)
    have heq : y = toUnit _ ≫ n w ≫ Q.projection := by
      apply (cancel_epi e).mp
      rw [← Category.assoc, ht, ← hq]
      exact hyL'
    refine ⟨w, heq, fun w' hw' => ?_⟩
    by_contra hne
    exact Set.disjoint_left.mp (hdisj w' w hne)
      (hw' ▸ hrange (S := Over.mk (fieldSpecMap k K)) w' (IsLocalRing.closedPoint K)) hw
  · rintro ⟨w, rfl, -⟩
    apply (fixedOver_whiskerLeft a _ e).mp
    rw [← Category.assoc, ht, ← ho w, ← Category.assoc]
    apply ((C w).uniqueGeometricFixedPoint L _).2
    rw [Category.assoc, ho]

/-- The two actions compatible with the quotient projection agree by
faithfully flat descent. -/
private theorem flagAction_unique {B : ClosedSubgroup G.val} (Q : Presentation B)
    (a a' : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (ha' : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a'.smul =
      μ[G.val.X] ≫ Q.projection) :
    a = a' := by
  let : Flat Q.projection.left := Q.flat
  let : Surjective Q.projection.left := Q.surjective
  let : Epi (G.val.X ◁ Q.projection) := whiskerLeft_epi _ _
  apply ModObj.ext
  apply (cancel_epi (G.val.X ◁ Q.projection)).mp
  have hp : G.val.X ◁ Q.projection =
      lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hleft : 𝟙 G.val.X ⊗ₘ Q.projection = G.val.X ◁ Q.projection := by simp
  rw [hleft] at ha
  rw [← ha, hp, ha']

end Geometry
section InvariantOpen
@[instance_reducible]
private def actionOfMono {C : Type*} [Category C] [MonoidalCategory C]
    {M X Y : C} [MonObj M] (a : ModObj M X) (i : Y ⟶ X) [Mono i]
    (r : M ⊗ Y ⟶ Y) (hr : r ≫ i = M ◁ i ≫ a.smul) : ModObj M Y where
  smul := r
  one_smul := by
    change (η[M] ▷ Y) ≫ r = (λ_ Y).hom
    apply (cancel_mono i).mp
    rw [Category.assoc, hr, ← whisker_exchange_assoc,
      ModObj.one_smul_self, leftUnitor_naturality]
  mul_smul := by
    change (μ[M] ▷ Y) ≫ r = (α_ M M Y).hom ≫ M ◁ r ≫ r
    apply (cancel_mono i).mp
    simp only [Category.assoc, hr]
    have H := congrArg (M ◁ ·) hr
    simp only [whiskerLeft_comp] at H
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self,
      associator_naturality_right_assoc, reassoc_of% H]

variable {T : GroupScheme k} {X : SchemeOver k}
  (a : ModObj T.X X) (U : X.left.Opens)
  (hU : a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U)

private instance openInclusion_isOpenImmersion (V : X.left.Opens) :
    IsOpenImmersion (openInclusion X V).left :=
  inferInstanceAs (IsOpenImmersion V.ι)

include hU in
private theorem invariantOpen_range :
    Set.range ((T.X ◁ openInclusion X U) ≫ a.smul).left ⊆
      Set.range (openInclusion X U).left := by
  let j := openInclusion X U
  rw [show Set.range j.left = (U : Set X.left) from Scheme.Opens.range_ι U]
  rintro _ ⟨z, rfl⟩
  have hz : a.smul.left ((T.X ◁ j).left z) ∈ U := by
    change (T.X ◁ j).left z ∈ a.smul.left ⁻¹ᵁ U
    rw [hU]
    change (snd T.X X).left ((T.X ◁ j).left z) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
    have h : (T.X ◁ j) ≫ snd T.X X = snd T.X _ ≫ j := by simp
    rw [h, Over.comp_left, Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι U).le ⟨(snd T.X _).left z, rfl⟩
  exact hz

private def invariantOpen_smul :
    T.X ⊗ openScheme X U ⟶ openScheme X U :=
  let j := openInclusion X U
  let g := (T.X ◁ j) ≫ a.smul
  Over.homMk (IsOpenImmersion.lift j.left g.left (invariantOpen_range a U hU))
    (by
      change (IsOpenImmersion.lift j.left g.left _ ≫ j.left) ≫ X.hom = _
      rw [IsOpenImmersion.lift_fac]
      exact Over.w g)

@[reassoc]
private theorem invariantOpen_smul_comp :
    invariantOpen_smul a U hU ≫ openInclusion X U =
      (T.X ◁ openInclusion X U) ≫ a.smul :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

/-- An invariant open subscheme inherits the action of the ambient scheme. -/
@[instance_reducible]
def invariantOpenAction : ModObj T.X (openScheme X U) :=
  letI : Mono (openInclusion X U) := Over.mono_of_mono_left _
  actionOfMono a (openInclusion X U) (invariantOpen_smul a U hU)
    (invariantOpen_smul_comp a U hU)

theorem invariantOpenInclusion_equivariant :
    IsEquivariantMap a (invariantOpenAction a U hU) (openInclusion X U) := by
  exact (invariantOpen_smul_comp a U hU).trans (by rw [id_tensorHom])

end InvariantOpen

section InvariantClosed

open Scheme.IdealSheafData

variable {T : GroupScheme k} {X : SchemeOver k}

private abbrev closedScheme (X : SchemeOver k) (Z : TopologicalSpace.Closeds X.left) :
    SchemeOver k := Over.mk ((vanishingIdeal Z).subschemeι ≫ X.hom)

private def closedInclusion (X : SchemeOver k) (Z : TopologicalSpace.Closeds X.left) :
    closedScheme X Z ⟶ X := Over.homMk (vanishingIdeal Z).subschemeι

/-- The kernel of a morphism from a reduced scheme is the ideal of the closed
support of its image. -/
theorem ker_eq_vanishingIdeal_of_isReduced {V W : Scheme.{u}} [IsReduced V] (g : V ⟶ W) :
    g.ker = vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range g)) := by
  rw [← map_bot, ← Scheme.nilradical_eq_bot, ← vanishingIdeal_top, map_vanishingIdeal]
  congr 1
  rw [TopologicalSpace.Closeds.coe_top, Set.image_univ]

/-- A closed invariant set has an equivariant inclusion with the reduced
induced structure if its product with the acting group is reduced. -/
theorem exists_invariantClosedSubscheme
    (a : ModObj T.X X) (Z : TopologicalSpace.Closeds X.left)
    (hZ : a.smul.left ⁻¹' (Z : Set X.left) = (snd T.X X).left ⁻¹' (Z : Set X.left))
    (hr : IsReduced (T.X ⊗ closedScheme X Z).left) :
    ∃ (S : SchemeOver k) (b : ModObj T.X S) (i : S ⟶ X),
      i.left.ker = vanishingIdeal Z ∧ IsClosedImmersion i.left ∧
      IsEquivariantMap a b i ∧ Set.range i.left = (Z : Set X.left) := by
  let S := closedScheme X Z
  let i := closedInclusion X Z
  let : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (vanishingIdeal Z).subschemeι)
  let : Mono i := Over.mono_of_mono_left i
  let g : T.X ⊗ S ⟶ X := (T.X ◁ i) ≫ a.smul
  have hi : Set.range i.left = (Z : Set X.left) := by
    change Set.range (vanishingIdeal Z).subschemeι = _
    rw [range_subschemeι, coe_support_vanishingIdeal]
  have hg : Set.range g.left ⊆ (Z : Set X.left) := by
    rintro _ ⟨z, rfl⟩
    change (T.X ◁ i).left z ∈ a.smul.left ⁻¹' (Z : Set X.left)
    rw [hZ]
    change (snd T.X X).left ((T.X ◁ i).left z) ∈ (Z : Set X.left)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
    have h : (T.X ◁ i) ≫ snd T.X X = snd T.X S ≫ i := by simp [S]
    rw [h, Over.comp_left, Scheme.Hom.comp_apply, ← hi]
    exact Set.mem_range_self _
  let : IsReduced (T.X ⊗ S).left := hr
  have hk : i.left.ker ≤ g.left.ker := by
    change (vanishingIdeal Z).subschemeι.ker ≤ g.left.ker
    rw [ker_subschemeι, ker_eq_vanishingIdeal_of_isReduced]
    apply vanishingIdeal_antimono
    exact closure_minimal hg Z.isClosed
  let r : T.X ⊗ S ⟶ S := Over.homMk (IsClosedImmersion.lift i.left g.left hk)
    (by
      change (IsClosedImmersion.lift i.left g.left hk ≫ i.left) ≫ X.hom = _
      rw [IsClosedImmersion.lift_fac]
      exact Over.w g)
  have he : r ≫ i = (T.X ◁ i) ≫ a.smul :=
    Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ hk)
  refine ⟨S, actionOfMono a i r he, i, ker_subschemeι _, inferInstance, ?_, hi⟩
  exact he.trans (by rw [id_tensorHom])

end InvariantClosed


section ClosedLocus

open Scheme.IdealSheafData

private theorem reduced_closedScheme_product {T : GroupScheme k} {X : SchemeOver k}
    [GeometricallyReduced T.X.hom] [LocallyOfFiniteType X.hom] (Z : Closeds X.left) :
    IsReduced (T.X ⊗ closedScheme X Z).left := by
  let Y := closedScheme X Z
  let : IsReduced Y.left := vanishingSubschemeReduced Z
  let : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType ((vanishingIdeal Z).subschemeι ≫ X.hom)
    infer_instance
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let p := snd T.X Y
  have h := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (fst T.X Y) p) (tensorProductIsBinaryProduct T.X Y)
  let : GeometricallyReduced p.left :=
    MorphismProperty.of_isPullback h (show GeometricallyReduced T.X.hom from inferInstance)
  let : Flat p.left := MorphismProperty.of_isPullback h (show Flat T.X.hom from inferInstance)
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian p.left

/-- Containment of the images gives the factorization through a reduced closed
subscheme when the source is reduced. -/
private def liftReducedClosed {X Y Z : SchemeOver k} (i : Z ⟶ X) (f : Y ⟶ X)
    [IsClosedImmersion i.left] [IsReduced Z.left] [IsReduced Y.left]
    (h : Set.range f.left ⊆ Set.range i.left) : Y ⟶ Z :=
  let hf : i.left.ker ≤ f.left.ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced, ker_eq_vanishingIdeal_of_isReduced]
    exact vanishingIdeal_antimono (closure_mono h)
  Over.homMk (IsClosedImmersion.lift i.left f.left hf) (by
    rw [← Over.w i, ← Category.assoc, IsClosedImmersion.lift_fac, Over.w f])

@[reassoc (attr := simp)]
private theorem liftReducedClosed_fac {X Y Z : SchemeOver k} (i : Z ⟶ X) (f : Y ⟶ X)
    [IsClosedImmersion i.left] [IsReduced Z.left] [IsReduced Y.left]
    (h : Set.range f.left ⊆ Set.range i.left) :
    liftReducedClosed i f h ≫ i = f :=
  Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)

private theorem openImmersion_of_closedImmersion_of_open_range {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] [IsReduced Y] (h : IsOpen (Set.range f)) :
    IsOpenImmersion f := by
  let V : Y.Opens := ⟨Set.range f, h⟩
  have hr : Set.range V.ι = Set.range f := Scheme.Opens.range_ι V
  let g := IsOpenImmersion.lift V.ι f hr.ge
  have hg : g ≫ V.ι = f := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion g := by
    letI : IsClosedImmersion (g ≫ V.ι) := hg.symm ▸ (inferInstance : IsClosedImmersion f)
    exact IsClosedImmersion.of_comp g V.ι
  letI : Surjective g := ⟨by
    intro z
    obtain ⟨x, hx⟩ := hr ▸ Set.mem_range_self (f := V.ι) z
    refine ⟨x, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg, hx]⟩
  letI : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  letI : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  rw [← hg]
  infer_instance

/-- The reduced union of finitely many distinct rational sections is their
coproduct over the ground field. -/
private theorem reducedClosed_isCoproduct {X Z : SchemeOver k}
    (i : Z ⟶ X) [IsReduced Z.left] [IsClosedImmersion i.left]
    {I : Type u} [Finite I] (x : I → (𝟙_ (SchemeOver k) ⟶ X))
    (hdisj : ∀ v w, v ≠ w → Disjoint (Set.range (x v).left) (Set.range (x w).left))
    (hrange : Set.range i.left = ⋃ w, Set.range (x w).left) :
    ∃ e : (∐ fun _ : I ↦ 𝟙_ (SchemeOver k)) ≅ Z,
      ∀ w, Sigma.ι _ w ≫ e.hom ≫ i = x w := by
  classical
  let pt := 𝟙_ (SchemeOver k)
  letI : IsReduced pt.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  letI : Subsingleton pt.left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  let c (w : I) : pt ⟶ Z := liftReducedClosed i (x w) (by
    rw [hrange]
    exact Set.subset_iUnion (fun v : I ↦ Set.range (x v).left) w)
  have hc (w : I) : c w ≫ i = x w := liftReducedClosed_fac _ _ _
  have hc_range (w : I) : Set.range (c w).left = i.left ⁻¹' Set.range (x w).left := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, congrArg (fun g : pt ⟶ X ↦ g.left s) (hc w).symm⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, i.left.isClosedEmbedding.injective ?_⟩
      exact (congrArg (fun g : pt ⟶ X ↦ g.left s) (hc w)).trans hs
  have hd : Pairwise (fun v w ↦ Disjoint (Set.range (c v).left) (Set.range (c w).left)) := by
    intro v w hvw
    rw [hc_range, hc_range]
    exact (hdisj v w hvw).preimage _
  have hcov : (⋃ w, Set.range (c w).left) = Set.univ := by
    simp only [hc_range, ← Set.preimage_iUnion, ← hrange, Set.preimage_range]
  haveI hclosed (w : I) : IsClosedImmersion (c w).left := by
    haveI : IsClosedImmersion (x w).left :=
      isClosedImmersion_of_comp_eq_id X.hom (x w).left (Over.w (x w))
    haveI : IsClosedImmersion ((c w).left ≫ i.left) := by
      rw [← Over.comp_left, hc]
      infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion _ i.left
  haveI hopen (w : I) : IsOpenImmersion (c w).left := by
    apply openImmersion_of_closedImmersion_of_open_range
    have he : (Set.range (c w).left)ᶜ =
        ⋃ v : {v : I // v ≠ w}, Set.range (c v.val).left := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Subtype.exists]
      constructor
      · intro hz
        have hz' : z ∈ ⋃ v, Set.range (c v).left := hcov ▸ Set.mem_univ _
        obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz'
        exact ⟨v, fun e ↦ hz (e ▸ hv), hv⟩
      · rintro ⟨v, hv, hz⟩ hw
        exact Set.disjoint_left.mp (hd hv) hz hw
    apply isClosed_compl_iff.mp
    rw [he]
    exact isClosed_iUnion_of_finite fun v ↦ (c v.val).left.isClosedEmbedding.isClosed_range
  haveI : IsOpenImmersion (Sigma.desc (fun w ↦ (c w).left)) :=
    isOpenImmersion_sigmaDesc _ _ hd
  have htop : (Sigma.desc (fun w ↦ (c w).left)).opensRange = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, s, rfl⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ z)
    exact ⟨Sigma.ι (fun _ : I ↦ pt.left) w s, by
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
  letI : IsIso (Sigma.desc (fun w ↦ (c w).left)) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ htop
  let L := Over.forget (Spec (CommRingCat.of k))
  let e₀ : (∐ fun _ : I ↦ pt.left) ≅ L.obj (∐ fun _ : I ↦ pt) :=
    (PreservesCoproduct.iso L (fun _ : I ↦ pt)).symm
  let e := Sigma.desc c
  have he : e₀.hom ≫ L.map e = Sigma.desc (fun w ↦ (c w).left) := by
    apply Sigma.hom_ext
    intro w
    change _ ≫ sigmaComparison L (fun _ : I ↦ pt) ≫ L.map e = _
    have hi : Sigma.ι (fun _ : I ↦ pt.left) w ≫ sigmaComparison L (fun _ : I ↦ pt) =
        L.map (Sigma.ι (fun _ : I ↦ pt) w) :=
      ι_comp_sigmaComparison L (fun _ : I ↦ pt) w
    rw [← Category.assoc, hi, ← L.map_comp, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    rfl
  haveI : IsIso (L.map e) :=
    have h : L.map e = e₀.inv ≫ Sigma.desc (fun w ↦ (c w).left) := by
      rw [← he, Iso.inv_hom_id_assoc]
    h.symm ▸ inferInstance
  haveI : IsIso e := isIso_of_reflects_iso e L
  exact ⟨asIso e, fun w ↦ (Sigma.ι_comp_desc_assoc c w i).trans (hc w)⟩

private theorem exists_fixedUnion {T : GroupScheme k} {X : SchemeOver k}
    (a : ModObj T.X X) [LocallyOfFiniteType X.hom] [GeometricallyReduced T.X.hom]
    {W : Type u} [Finite W] (x : W → (𝟙_ (SchemeOver k) ⟶ X))
    (hx : ∀ w, IsEquivariantMap a (pointAction T) (x w))
    (hd : ∀ v w, v ≠ w → Disjoint (Set.range (x v).left) (Set.range (x w).left)) :
    ∃ (Z : InvariantClosed a) (_ : InvariantComplement a Z),
      Set.range Z.inclusion.left = (⋃ w, Set.range (x w).left) ∧
      ∃ e : (∐ fun _ : W ↦ 𝟙_ (SchemeOver k)) ≅ Z.scheme,
        ∀ w, Sigma.ι _ w ≫ e.hom ≫ Z.inclusion = x w := by
  obtain ⟨U, hU, hInv⟩ := invariant_open_complement_of_fixed_sections a x hx
  let F : Closeds X.left := ⟨(U : Set X.left)ᶜ, U.isOpen.isClosed_compl⟩
  have hF : (F : Set X.left) = ⋃ w, Set.range (x w).left := by simp [F, hU]
  have hFinv : a.smul.left ⁻¹' (F : Set X.left) =
      (snd T.X X).left ⁻¹' (F : Set X.left) := by
    rw [hF, Set.preimage_iUnion, Set.preimage_iUnion]
    exact Set.iUnion_congr fun w ↦ action_preimage_range_of_equivariant (x w) (hx w)
  obtain ⟨S, b, i, hi, hclosed, hb, hr⟩ :=
    exists_invariantClosedSubscheme a F hFinv (reduced_closedScheme_product F)
  haveI : IsClosedImmersion i.left := hclosed
  haveI : IsReduced S.left := by
    have hk : IsReduced i.left.image := by
      change IsReduced i.left.ker.subscheme
      rw [hi]
      exact vanishingSubschemeReduced F
    exact isReduced_of_isOpenImmersion i.left.toImage
  let Z : InvariantClosed a := ⟨S, b, i, inferInstance, hclosed, hb⟩
  let V : InvariantComplement a Z :=
    ⟨_, invariantOpenAction a U hInv, openInclusion X U, inferInstance,
      invariantOpenInclusion_equivariant a U hInv,
      (Scheme.Opens.range_ι U).trans (by simp [Z, hr, F])⟩
  exact ⟨Z, V, hr.trans hF, reducedClosed_isCoproduct i x hd (hr.trans hF)⟩

end ClosedLocus

section ClosedPrefixes

open Specs.SimpleRoots (wordLength wordProduct)
open Specs.GallerySubwords (IsReduced)
open Specs.SchubertClosures (subwordProducts SubwordLE closureIdeal)
open Specs.BorelsAndChambers (subgroupRoots)
open private align_representatives range_closureIdeal
  from LinearAlgebraicGroups.Flag.SchubertClosures
open private exists_shortest_word from LinearAlgebraicGroups.RootData.SimpleRoots

private theorem finiteOrderByRank {W : Type u} [Fintype W] (r : W → ℕ) :
    ∃ e : Fin (Fintype.card W) ≃ W, Monotone (r ∘ e) := by
  classical
  let f := Fintype.equivFin W
  let L (w : W) : ℕ ×ₗ Fin (Fintype.card W) := toLex (r w, f w)
  letI : LinearOrder W := LinearOrder.lift' L (fun v w h ↦
    f.injective (congrArg (fun z ↦ (ofLex z).2) h))
  let o := (Finset.univ : Finset W).orderIsoOfFin rfl
  let e : Fin (Fintype.card W) ≃ W := o.toEquiv.trans
    ⟨Subtype.val, fun w ↦ ⟨w, Finset.mem_univ w⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  refine ⟨e, fun i j hij ↦ ?_⟩
  have hl : L (e i) ≤ L (e j) := o.monotone hij
  exact (Prod.Lex.le_iff.mp hl).elim Nat.le_of_lt (fun h ↦ h.1.le)

/-- When the closures are unions of cells with strictly smaller ranks,
ordering by rank makes every prefix closed. -/
private theorem closedPrefixes_of_rank {X : SchemeOver k} {W : Type u} [Fintype W]
    (F : W → Set X.left) (r : W → ℕ)
    (h : ∀ w, closure (F w) ⊆ F w ∪ ⋃ v : {v // r v < r w}, F v.val) :
    ∃ e : Fin (Fintype.card W) ≃ W, ClosedPrefixes F e := by
  classical
  obtain ⟨e, he⟩ := finiteOrderByRank r
  refine ⟨e, fun j ↦ ?_⟩
  have hc : (⋃ i : Fin (Fintype.card W), ⋃ (_ : i.val < j), closure (F (e i))) =
      ⋃ i : Fin (Fintype.card W), ⋃ (_ : i.val < j), F (e i) := by
    refine Set.Subset.antisymm ?_ (Set.iUnion_mono fun i ↦ Set.iUnion_mono fun _ ↦ subset_closure)
    intro z hz
    simp only [Set.mem_iUnion, exists_prop] at hz ⊢
    obtain ⟨i, hi, hz⟩ := hz
    rcases h (e i) hz with hz | hz
    · exact ⟨i, hi, hz⟩
    · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
      let j' := e.symm v.val
      have hvj : e j' = v.val := e.apply_symm_apply _
      have hj'i : j' < i := by
        apply lt_of_not_ge
        intro hij'
        exact (not_lt_of_ge (show r (e i) ≤ r (e j') from he hij'))
          (hvj.symm ▸ v.property)
      exact ⟨j', Nat.lt_trans hj'i hi, hvj.symm ▸ hv⟩
  rw [← hc]
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_iUnion_of_finite fun _ ↦ isClosed_closure

private theorem cell_range_eq_orbit {G : AffineAlgebraicGroup k} {T B A : ClosedSubgroup G.val}
    {Q : Presentation B} {a : ModObj G.val.X Q.scheme} {g : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a g A) :
    Set.range C.orbitInclusion.left =
      Set.range (lift B.inclusion.hom.hom (toUnit B.group.X ≫ g ≫ Q.projection) ≫ a.smul).left := by
  rw [← C.projection_eq, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, C.orbitSurjective.1.range_eq, Set.image_univ]

/-- The cells for the chosen family of rational representatives admit a
closed-prefix enumeration on the actual quotient. -/
theorem bruhatClosedPrefixes {G : AffineAlgebraicGroup k}
    {T B : ClosedSubgroup G.val} (hG : Specs.GeometricRadicals.IsReductive G)
    (hT : Specs.GeometricRadicals.IsSplitTorus T.group)
    (hmax : Specs.RankOneFlag.IsGeometricallyMaximal T)
    (hB : Specs.GeometricBorelConjugacy.IsKBorel B)
    (hTB : Specs.SchemeDerivedGroup.IsSubgroupOf T B)
    (Q : Presentation B) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    [IsCommMonObj T.group.X] {D : Datum T} (J : Identification D)
    [Fintype D.rootDatum.weylGroup]
    (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X))
    (hn : ∀ w, IsRepresentative J w (n w))
    (A : D.rootDatum.weylGroup → ClosedSubgroup G.val)
    (C : ∀ w, Cell (T := T) Q a (n w ≫ J.normalizer.inclusion.hom.hom) (A w)) :
    ∃ e : Fin (Fintype.card D.rootDatum.weylGroup) ≃ D.rootDatum.weylGroup,
      ClosedPrefixes (fun w ↦ Set.range (C w).orbitInclusion.left) e := by
  classical
  obtain ⟨_, D', J', _, b, _, _, hb, hr, _, hQ⟩ :=
    LinearAlgebraicGroups.Flag.SchubertClosures.schubertClosures G hG T B hT hmax hB hTB
  obtain ⟨a', ha', hC⟩ := hQ Q
  have haeq := flagAction_unique Q a a' ha ha'
  subst a'
  obtain ⟨label, m, hm, hlabel⟩ := align_representatives J J' n hn hr
  obtain ⟨A', C', _, _, hclos⟩ := hC m hm
  let F := fun w ↦ Set.range (C w).orbitInclusion.left
  let F' := fun w ↦ Set.range (C' w).orbitInclusion.left
  have hF (w : D.rootDatum.weylGroup) : F w = F' (label w) := by
    change Set.range (C w).orbitInclusion.left = Set.range (C' (label w)).orbitInclusion.left
    rw [cell_range_eq_orbit, cell_range_eq_orbit]
    simp only [hlabel]
  let len := wordLength D'.rootDatum b
  apply closedPrefixes_of_rank F (len ∘ label)
  intro w z hz
  obtain ⟨l, hl, hlen, _⟩ := exists_shortest_word D'.rootDatum b hb.generates (label w)
  have hred : IsReduced D'.rootDatum b l := by
    change len (wordProduct D'.rootDatum b l) = l.length
    rw [hl, hlen]
  have hcl : closure (F w) = ⋃ v ∈ subwordProducts D'.rootDatum b l, F' v := by
    rw [hF, ← hl, ← range_closureIdeal]
    exact (hclos l hred).2.1
  rw [hcl] at hz
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
  obtain ⟨⟨s, hs, hsv⟩, hz⟩ := Set.mem_iUnion.mp hv
  by_cases heq : v = label w
  · left
    rwa [hF, ← heq]
  · right
    have hslt : s.length < l.length := by
      refine lt_of_le_of_ne hs.length_le fun he ↦ heq ?_
      rw [← hsv, hs.eq_of_length he, hl]
    have hvs : len v ≤ s.length := by
      exact csInf_le' ⟨s, rfl, hsv⟩
    have hlt : len v < len (label w) := (lt_of_le_of_lt hvs hslt).trans_le hlen.le
    refine Set.mem_iUnion.mpr ⟨⟨label.symm v, ?_⟩, ?_⟩
    · change len (label (label.symm v)) < _
      rwa [label.apply_symm_apply]
    · simp only [hF, label.apply_symm_apply]
      exact hz

end ClosedPrefixes

section Coordinates

open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily product)
open Specs.CharacterPairing (characterValue)
open LinearAlgebraicGroups.GrassmannianCharts (hom_ext_on_affines affineProbesEquiv)

private abbrev polynomialScheme (k : Type u) [Field k] (I : Type u) : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k (MvPolynomial I k)))

private def polynomialPoint {I : Type u} (R : TestAlgebra k) (v : I → R) :
    Points (polynomialScheme k I) R :=
  (testSpec k).map (CommAlgCat.ofHom (MvPolynomial.aeval v)).op

private theorem polynomialPoint_map {I : Type u} {R S : TestAlgebra k} (f : R ⟶ S)
    (v : I → R) :
    mapPoints f (polynomialPoint R v) = polynomialPoint S (fun i ↦ f.hom (v i)) := by
  change (testSpec k).map f.op ≫ (testSpec k).map _ =
    (testSpec k).map (CommAlgCat.ofHom (MvPolynomial.aeval _)).op
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  ext i
  simp

private theorem polynomialPoint_bijective {I : Type u} (R : TestAlgebra k) :
    Function.Bijective (polynomialPoint (I := I) R) := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  constructor
  · intro v w hvw
    have h := ff.map_injective hvw
    funext i
    exact (MvPolynomial.aeval_X _ _).symm.trans
      ((congrArg (fun f ↦ f.unop.hom (MvPolynomial.X i)) h).trans (MvPolynomial.aeval_X _ _))
  · intro p
    let f := ff.preimage p
    refine ⟨fun i ↦ f.unop.hom (MvPolynomial.X i), ?_⟩
    have h : CommAlgCat.ofHom
        (MvPolynomial.aeval (fun i ↦ f.unop.hom (MvPolynomial.X i))) = f.unop := by
      apply CommAlgCat.hom_ext
      ext i
      simp
    rw [polynomialPoint, h]
    exact ff.map_preimage p

private theorem polynomialPoint_universal {I : Type u} (R : TestAlgebra k) (v : I → R) :
    mapPoints (CommAlgCat.ofHom (MvPolynomial.aeval v))
      (polynomialPoint (CommAlgCat.of k (MvPolynomial I k)) MvPolynomial.X) =
      polynomialPoint R v := by
  rw [polynomialPoint_map]
  congr 1
  funext i
  exact MvPolynomial.aeval_X _ _

/-- Evaluation at an affine test point, using the actual pullback of functions. -/
private def evaluateFunction {X : SchemeOver k} (R : TestAlgebra k) (q : Points X R) :
    Γ(X.left, ⊤) →+* R :=
  (q.left.appTop ≫ (Scheme.ΓSpecIso _).hom).hom

private theorem evaluateFunction_comp {X Y : SchemeOver k} (R : TestAlgebra k)
    (q : Points X R) (f : X ⟶ Y) (c : Γ(Y.left, ⊤)) :
    evaluateFunction R (q ≫ f) c = evaluateFunction R q (f.left.appTop c) := by
  unfold evaluateFunction
  rw [Over.comp_left, Scheme.Hom.comp_appTop, Category.assoc]
  rfl

private theorem evaluateFunction_character {T : GroupScheme k} (χ : Character T)
    (R : TestAlgebra k) (t : Points T.X R) :
    evaluateFunction R t (characterFunction χ) = characterValue χ R t := by
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let m := ff.preimage (t ≫ χ.hom.hom)
  have hm : (testSpec k).map m = t ≫ χ.hom.hom := ff.map_preimage _
  have hm' : Spec.map (CommRingCat.ofHom m.unop.hom.toRingHom) =
      (t ≫ χ.hom.hom).left := congrArg Over.Hom.left hm
  let B := Specs.DiagonalizableGroups.groupAlgebra k Specs.DiagonalizableGroups.IntegerCharacters
  let φ : CommRingCat.of B ⟶ CommRingCat.of R := CommRingCat.ofHom m.unop.hom.toRingHom
  have h : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (t ≫ χ.hom.hom).left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom = φ := by
    change _ ≫ (t ≫ χ.hom.hom).left.appTop ≫ _ = _
    rw [← hm', ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
    χ.hom.hom.left.appTop ≫ t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom)
      (MonoidAlgebra.of k _ Specs.DiagonalizableGroups.integerGenerator) = _
  rw [← Scheme.Hom.comp_appTop_assoc, ← Over.comp_left, h]
  rfl

private theorem functionWeight_of_points {T : GroupScheme k} {X : SchemeOver k}
    [IsAffine T.X.left] [IsAffine X.left]
    (a : ModObj T.X X) (f : Γ(X.left, ⊤)) (χ : Character T)
    (h : ∀ (R : TestAlgebra k) (t : Points T.X R) (p : Points X R),
      evaluateFunction R (lift t p ≫ a.smul) f =
        characterValue χ⁻¹ R t * evaluateFunction R p f) :
    HasFunctionWeight a f χ := by
  letI : IsAffine (T.X ⊗ X).left := by rw [Over.tensorObj_left]; infer_instance
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (G := T.X ⊗ X)).mpr inferInstance
  let z : Points (T.X ⊗ X) R.unop := e.hom
  letI : IsIso z.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  letI : IsIso z.left.appTop := inferInstanceAs (IsIso (Scheme.Γ.map z.left.op))
  have hz : Function.Injective (evaluateFunction R.unop z) :=
    (ConcreteCategory.bijective_of_isIso (z.left.appTop ≫ (Scheme.ΓSpecIso _).hom)).1
  change a.smul.left.appTop f =
    (fst T.X X).left.appTop (characterFunction χ⁻¹) * (snd T.X X).left.appTop f
  apply hz
  have he : lift (z ≫ fst T.X X) (z ≫ snd T.X X) = z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  calc
    evaluateFunction R.unop z (a.smul.left.appTop f) =
        evaluateFunction R.unop (z ≫ a.smul) f :=
      (evaluateFunction_comp R.unop z a.smul f).symm
    _ = characterValue χ⁻¹ R.unop (z ≫ fst T.X X) *
        evaluateFunction R.unop (z ≫ snd T.X X) f := by
      simpa only [he] using h R.unop (z ≫ fst T.X X) (z ≫ snd T.X X)
    _ = evaluateFunction R.unop z
        ((fst T.X X).left.appTop (characterFunction χ⁻¹) * (snd T.X X).left.appTop f) := by
      rw [← evaluateFunction_character, evaluateFunction_comp, evaluateFunction_comp, map_mul]

private def coordinatesFromIso {X : SchemeOver k} {I : Type u}
    (e : polynomialScheme k I ≅ X) :
    letI : Algebra k Γ(X.left, ⊤) := (groundRingHom X).toAlgebra
    MvPolynomial I k ≃ₐ[k] Γ(X.left, ⊤) := by
  letI : Algebra k Γ(X.left, ⊤) := (groundRingHom X).toAlgebra
  let j := (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv ≫ e.inv.left.appTop
  letI : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  letI : IsIso e.inv.left.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.inv.left.op))
  letI : IsIso j := inferInstanceAs (IsIso (_ ≫ e.inv.left.appTop))
  refine AlgEquiv.ofBijective ⟨j.hom, fun x ↦ ?_⟩
    (ConcreteCategory.bijective_of_isIso j)
  let φ := CommRingCat.ofHom (algebraMap k (MvPolynomial I k))
  have ho : e.inv.left ≫ Spec.map φ = X.hom := Over.w e.inv
  have hj : φ ≫ j = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop := by
    change φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv ≫
      e.inv.left.appTop = _
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop, ho]
  exact congrArg (fun f : CommRingCat.of k ⟶ Γ(X.left, ⊤) ↦ f x) hj

private theorem coordinatesFromIso_apply {X : SchemeOver k} {I : Type u}
    (e : polynomialScheme k I ≅ X) (r : MvPolynomial I k) :
    coordinatesFromIso e r =
      e.inv.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv r) := by
  rfl

private theorem evaluate_coordinatesFromIso {X : SchemeOver k} {I : Type u}
    (e : polynomialScheme k I ≅ X) (R : TestAlgebra k) (v : I → R) (i : I) :
    evaluateFunction R (polynomialPoint R v ≫ e.hom)
      (coordinatesFromIso e (MvPolynomial.X i)) = v i := by
  rw [coordinatesFromIso_apply, ← evaluateFunction_comp, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  let φ : CommRingCat.of (MvPolynomial I k) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom
  have h : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv ≫
      (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom = φ := by
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := congrArg (fun f : CommRingCat.of (MvPolynomial I k) ⟶ CommRingCat.of R ↦
    f (MvPolynomial.X i)) h
  exact hv.trans (MvPolynomial.aeval_X _ _)

end Coordinates

section RootCoordinates

open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily product rootProduct)
open Specs.CharacterPairing (characterValue)
open LinearAlgebraicGroups.GrassmannianCharts (hom_ext_on_affines)
open private RootCoordinate RootCoordinate.line RootCoordinate.iso RootCoordinate.scalar
  rootCoordinate_exists ProductScheme productPoint productPoint_map
  productPoint_surjective productPoint_eq_iff productPoint_mul rootPoint_zero
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private affine_subgroup from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
  {U : RootSubgroupFamily T} {S : Set (Root T)}

private def extendRootTuple (R : Type u) [Zero R] (v : S → R) : Root T → R := by
  classical
  exact fun a ↦ if ha : a ∈ S then v ⟨a, ha⟩ else 0

private theorem extendRootTuple_of_mem {R : Type u} [Zero R] (v : S → R)
    {a : Root T} (h : a ∈ S) : extendRootTuple R v a = v ⟨a, h⟩ := by simp [extendRootTuple, h]

private theorem orderedPoint_eq_productPoint (x : ∀ α, RootCoordinate U α)
    (R : TestAlgebra k) (v : S → R) (l : List (Root T)) (h : ∀ α ∈ l, α ∈ S) :
    orderedPoint (fun α : S ↦ ⟨RootCoordinate.line (x α.val), RootCoordinate.iso (x α.val)⟩) R v l h =
      productPoint x R (extendRootTuple R v) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change lift (rootPoint (RootCoordinate.iso (x a)).hom R (v ⟨a, h a List.mem_cons_self⟩))
      (orderedPoint (fun α : S ↦ ⟨RootCoordinate.line (x α.val), RootCoordinate.iso (x α.val)⟩)
        R v l (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))) =
        lift (rootPoint (RootCoordinate.iso (x a)).hom R (extendRootTuple R v a))
          (productPoint x R (extendRootTuple R v) l)
    rw [ih, extendRootTuple_of_mem _ (h a List.mem_cons_self)]

private theorem orderedRootPoint_bijective (x : ∀ α, RootCoordinate U α)
    (R : TestAlgebra k) (l : List (Root T)) (hl : Enumerates l S) :
    Function.Bijective fun v : S → R ↦ productPoint x R (extendRootTuple R v) l := by
  constructor
  · intro v w he
    have hv := (productPoint_eq_iff x R _ _ l).mp he
    funext a
    have h := hv a.val ((hl.2 _).mpr a.property)
    simpa only [extendRootTuple_of_mem _ a.property] using h
  · intro p
    obtain ⟨v, rfl⟩ := productPoint_surjective x R l hl.1 p
    refine ⟨fun a ↦ v a.val, (productPoint_eq_iff x R _ _ l).mpr fun a ha ↦ ?_⟩
    exact extendRootTuple_of_mem _ ((hl.2 _).mp ha)

private theorem rootPolynomialIso (x : ∀ α, RootCoordinate U α)
    (l : List (Root T)) (hl : Enumerates l S) :
    ∃ e : polynomialScheme k S ≅ ProductScheme U l,
      ∀ (R : TestAlgebra k) (v : S → R),
        polynomialPoint R v ≫ e.hom = productPoint x R (extendRootTuple R v) l := by
  let A := CommAlgCat.of k (MvPolynomial S k)
  let f := productPoint x A (extendRootTuple A MvPolynomial.X) l
  have hf (R : TestAlgebra k) (v : S → R) :
      polynomialPoint R v ≫ f = productPoint x R (extendRootTuple R v) l := by
    change mapPoints (CommAlgCat.ofHom (MvPolynomial.aeval v)) f = _
    unfold f
    rw [productPoint_map]
    apply (productPoint_eq_iff x R _ _ l).mpr
    intro a ha
    have hs := (hl.2 _).mp ha
    simp only [extendRootTuple_of_mem _ hs]
    exact MvPolynomial.aeval_X _ _
  have hbij (R : TestAlgebra k) : Function.Bijective
      (fun p : Points (polynomialScheme k S) R ↦ p ≫ f) := by
    have h₁ := orderedRootPoint_bijective x R l hl
    have h₂ := polynomialPoint_bijective (I := S) R
    constructor
    · intro p q hpq
      obtain ⟨v, rfl⟩ := h₂.2 p
      obtain ⟨w, rfl⟩ := h₂.2 q
      exact congrArg (polynomialPoint R) (h₁.1 ((hf R v).symm.trans
        (hpq.trans (hf R w))))
    · intro y
      obtain ⟨v, hv⟩ := h₁.2 y
      exact ⟨polynomialPoint R v, (hf R v).trans hv⟩
  have hAff (l : List (Root T)) : IsAffine (ProductScheme U l).left := by
    induction l with
    | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
    | cons a l ih =>
      letI : IsAffine (ProductScheme U l).left := ih
      letI : IsAffine (U a).val.group.X.left := affine_subgroup G.property.1 (U a).val
      change IsAffine ((U a).val.group.X ⊗ ProductScheme U l).left
      rw [Over.tensorObj_left]
      infer_instance
  obtain ⟨R, ⟨d⟩⟩ := (essImage_algSpec (G := ProductScheme U l)).mpr (hAff l)
  obtain ⟨j, hj⟩ := (hbij R.unop).2 d.hom
  change j ≫ f = d.hom at hj
  let g := d.inv ≫ j
  have hg : g ≫ f = 𝟙 _ := by rw [Category.assoc, hj, Iso.inv_hom_id]
  have hfg : f ≫ g = 𝟙 _ := by
    apply hom_ext_on_affines
    intro A₁ p
    apply (hbij A₁).1
    change (p ≫ f ≫ g) ≫ f = (p ≫ 𝟙 _) ≫ f
    rw [Category.assoc p, Category.assoc f, hg, Category.comp_id, Category.comp_id]
  exact ⟨⟨f, g, hfg, hg⟩, hf⟩

private theorem conjugate_orderedRootProduct (x : ∀ α, RootCoordinate U α)
    (R : TestAlgebra k) (t : Points T.group.X R) (v : Root T → R) (l : List (Root T)) :
    let g := t ≫ T.inclusion.hom.hom
    let f := productPoint x R v l ≫ rootProduct U l
    g * f * g⁻¹ =
      productPoint x R (fun α ↦ characterValue α.val R t * v α) l ≫ rootProduct U l := by
  dsimp only
  rw [productPoint_mul, productPoint_mul]
  let g := t ≫ T.inclusion.hom.hom
  let c := (MulAut.conj g).toMonoidHom
  change c (List.map _ l).prod = _
  rw [MonoidHom.map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact RootCoordinate.scalar (x a) R t (v a)

end RootCoordinates

section Scaling

open Specs.CharacterPairing (characterValue)
open LinearAlgebraicGroups.GrassmannianCharts
  (hom_ext_on_affines affineProbesEquiv affineProbesEquiv_apply)
open private characterValue_natural from LinearAlgebraicGroups.RootData.RootGroups
open private groundPointIso from LinearAlgebraicGroups.Flag.BruhatCells

variable {T : GroupScheme k} {I : Type u}

private def polynomialTuple (R : TestAlgebra k) (p : Points (polynomialScheme k I) R) :
    I → R :=
  (Equiv.ofBijective _ (polynomialPoint_bijective (I := I) R)).symm p

private theorem polynomialTuple_point (R : TestAlgebra k) (v : I → R) :
    polynomialTuple R (polynomialPoint R v) = v :=
  (Equiv.ofBijective _ (polynomialPoint_bijective (I := I) R)).symm_apply_apply v

private theorem polynomialPoint_tuple (R : TestAlgebra k) (p : Points (polynomialScheme k I) R) :
    polynomialPoint R (polynomialTuple R p) = p :=
  (Equiv.ofBijective _ (polynomialPoint_bijective (I := I) R)).apply_symm_apply p

private theorem polynomialTuple_map {R S : TestAlgebra k} (f : R ⟶ S)
    (p : Points (polynomialScheme k I) R) :
    polynomialTuple S (mapPoints f p) = fun i ↦ f.hom (polynomialTuple R p i) := by
  conv_lhs => rw [← polynomialPoint_tuple R p, polynomialPoint_map, polynomialTuple_point]

private def scalingNat (χ : I → Character T) :
    pointsFunctor (T.X ⊗ polynomialScheme k I) ⟶ pointsFunctor (polynomialScheme k I) where
  app R := ↾ fun p ↦ polynomialPoint R (fun i ↦
    characterValue (χ i) R (p ≫ fst _ _) * polynomialTuple R (p ≫ snd _ _) i)
  naturality R S f := by
    apply ConcreteCategory.hom_ext
    intro p
    change polynomialPoint S (fun i ↦ characterValue (χ i) S
      (mapPoints f p ≫ fst _ _) * polynomialTuple S (mapPoints f p ≫ snd _ _) i) =
        mapPoints f (polynomialPoint R _)
    rw [polynomialPoint_map]
    congr 1
    funext i
    change characterValue (χ i) S (mapPoints f (p ≫ fst _ _)) *
      polynomialTuple S (mapPoints f (p ≫ snd _ _)) i = _
    rw [characterValue_natural, polynomialTuple_map, map_mul]

private def scalingMorphism (χ : I → Character T) :
    T.X ⊗ polynomialScheme k I ⟶ polynomialScheme k I :=
  (affineProbesEquiv _ _).symm (scalingNat χ)

private theorem scalingMorphism_point (χ : I → Character T) (R : TestAlgebra k)
    (t : Points T.X R) (v : I → R) :
    lift t (polynomialPoint R v) ≫ scalingMorphism χ =
      polynomialPoint R (fun i ↦ characterValue (χ i) R t * v i) := by
  rw [← affineProbesEquiv_apply]
  have he : affineProbesEquiv _ _ (scalingMorphism χ) = scalingNat χ :=
    (affineProbesEquiv _ _).apply_symm_apply _
  rw [he]
  change polynomialPoint R (fun i ↦ characterValue (χ i) R (lift t (polynomialPoint R v) ≫ fst _ _) *
    polynomialTuple R (lift t (polynomialPoint R v) ≫ snd _ _) i) = _
  rw [lift_fst, lift_snd, polynomialTuple_point]

private def polynomialOrigin (k : Type u) [Field k] (I : Type u) :
    𝟙_ (SchemeOver k) ⟶ polynomialScheme k I :=
  (groundPointIso k).hom ≫ polynomialPoint (CommAlgCat.of k k) 0

private theorem polynomialOrigin_point (R : TestAlgebra k) :
    toUnit ((testSpec k).obj (op R)) ≫ polynomialOrigin k I =
      polynomialPoint R 0 := by
  let f : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have hf : toUnit ((testSpec k).obj (op R)) ≫ (groundPointIso k).hom =
      (testSpec k).map f.op := by
    apply (cancel_mono (groundPointIso k).inv).mp
    exact Subsingleton.elim _ _
  rw [polynomialOrigin, ← Category.assoc, hf]
  change mapPoints f (polynomialPoint _ 0) = _
  rw [polynomialPoint_map]
  congr 1
  ext i
  simp

private theorem polynomialScaling_of_mono {X Y : SchemeOver k}
    (a : ModObj T.X X) [IsAffine T.X.left] (e : polynomialScheme k I ≅ Y)
    (f : Y ⟶ X) [Mono f] (χ : I → Character T)
    (h : ∀ (R : TestAlgebra k) (t : Points T.X R) (v : I → R),
      lift t ((polynomialPoint R v ≫ e.hom) ≫ f) ≫ a.smul =
        (polynomialPoint R (fun i ↦ characterValue (χ i) R t * v i) ≫ e.hom) ≫ f) :
    ∃ (b : ModObj T.X Y)
      (c : PolynomialCoordinates b (polynomialOrigin k I ≫ e.hom) (fun i ↦ (χ i)⁻¹)),
      IsEquivariantMap a b f ∧
      c.coordinates = coordinatesFromIso e ∧
      ∀ (R : TestAlgebra k) (v : I → R) i, evaluateFunction R (polynomialPoint R v ≫ e.hom)
        (c.coordinates (MvPolynomial.X i)) = v i := by
  let r := (T.X ◁ e.inv) ≫ scalingMorphism χ ≫ e.hom
  have hr (R : TestAlgebra k) (t : Points T.X R) (v : I → R) :
      lift t (polynomialPoint R v ≫ e.hom) ≫ r =
        polynomialPoint R (fun i ↦ characterValue (χ i) R t * v i) ≫ e.hom := by
    rw [show r = _ from rfl, ← Category.assoc, ← Category.assoc,
      ← id_tensorHom, lift_map, Category.comp_id, Category.assoc (polynomialPoint R v),
      Iso.hom_inv_id, Category.comp_id, scalingMorphism_point]
  have hf : r ≫ f = (T.X ◁ f) ≫ a.smul := by
    apply hom_ext_on_affines
    intro R p
    let t := p ≫ fst T.X Y
    obtain ⟨v, hv⟩ := (polynomialPoint_bijective (I := I) R).2 (p ≫ snd T.X Y ≫ e.inv)
    have hv' : polynomialPoint R v ≫ e.hom = p ≫ snd T.X Y := by
      simp [hv, Category.assoc]
    have hp : p = lift t (polynomialPoint R v ≫ e.hom) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [t, hv']
    rw [hp, ← Category.assoc, hr, Category.assoc, ← Category.assoc _ (T.X ◁ f),
      ← id_tensorHom, lift_map, Category.comp_id]
    exact (h R t v).symm
  let b := actionOfMono a f r hf
  have hb : IsEquivariantMap a b f := hf.trans (by rw [id_tensorHom])
  haveI : IsAffine (polynomialScheme k I).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial I k))))
  haveI : IsAffine Y.left := IsAffine.of_isIso (Y := (polynomialScheme k I).left) e.inv.left
  let c := coordinatesFromIso e
  refine ⟨b, ⟨inferInstance, c, ?_, ?_⟩, hb, rfl, ?_⟩
  · intro i
    let R := CommAlgCat.of k k
    have hz := evaluate_coordinatesFromIso e R 0 i
    have hpoint : polynomialPoint R (0 : I → R) ≫ e.hom =
        (groundPointIso k).inv ≫ (polynomialOrigin k I ≫ e.hom) := by
      rw [← Category.assoc, show (groundPointIso k).inv ≫ polynomialOrigin k I =
          polynomialPoint R (0 : I → R) by
            simp [polynomialOrigin]
            rfl]
    rw [hpoint] at hz
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      ((polynomialOrigin k I ≫ e.hom).left.appTop (c (MvPolynomial.X i))) = _
    have ht : (groundPointIso k).inv.left = 𝟙 (Spec (CommRingCat.of k)) := rfl
    rw [evaluateFunction_comp] at hz
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      ((groundPointIso k).inv.left.appTop
        ((polynomialOrigin k I ≫ e.hom).left.appTop (c (MvPolynomial.X i)))) = 0 at hz
    rw [ht, Scheme.Hom.id_appTop] at hz
    exact hz.trans (map_zero _).symm
  · intro i
    apply functionWeight_of_points b
    intro R t p
    obtain ⟨v, hv⟩ := (polynomialPoint_bijective (I := I) R).2 (p ≫ e.inv)
    have hp : p = polynomialPoint R v ≫ e.hom := by simp [hv, Category.assoc]
    rw [hp]
    change evaluateFunction R (lift t (polynomialPoint R v ≫ e.hom) ≫ r)
      (c (MvPolynomial.X i)) = _
    rw [hr, evaluate_coordinatesFromIso, evaluate_coordinatesFromIso, inv_inv]
  · exact evaluate_coordinatesFromIso e

end Scaling

section Puncture

open Specs.CharacterPairing (characterValue)

private theorem polynomialOrigin_range {I : Type u} :
    Set.range (polynomialOrigin k I).left =
      ⋂ i : I, (↑(PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial I k)) :
        Set (PrimeSpectrum (MvPolynomial I k)))ᶜ := by
  let ε := MvPolynomial.aeval (R := k) (0 : I → k)
  have hsurj : Function.Surjective ε.toRingHom := by
    intro a
    exact ⟨MvPolynomial.C a, MvPolynomial.aeval_C _ _⟩
  change Set.range (PrimeSpectrum.comap ε.toRingHom) = _
  rw [range_comap_of_surjective _ _ hsurj, ker_evalZero_eq_span_X]
  ext p
  simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_iInter, Set.mem_compl_iff]
  change Ideal.span (Set.range (MvPolynomial.X : I → MvPolynomial I k)) ≤ p.asIdeal ↔ _
  rw [Ideal.span_le, Set.range_subset_iff]
  simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, not_not]

private theorem polynomialIso_puncture {Y : SchemeOver k} {I : Type u}
    (e : polynomialScheme k I ≅ Y) :
    (⋃ i : I, (Y.left.basicOpen (coordinatesFromIso e (MvPolynomial.X i)) : Set Y.left)) =
      (Set.range (polynomialOrigin k I ≫ e.hom).left)ᶜ := by
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  apply (Set.preimage_injective.mpr e.hom.left.surjective)
  simp only [Set.preimage_iUnion, Set.preimage_compl]
  have hcoord (i : I) :
      e.hom.left ⁻¹' (Y.left.basicOpen (coordinatesFromIso e (MvPolynomial.X i)) :
        Set Y.left) =
        (↑(PrimeSpectrum.basicOpen (MvPolynomial.X i : MvPolynomial I k)) :
          Set (PrimeSpectrum (MvPolynomial I k))) := by
    change (e.hom.left ⁻¹ᵁ Y.left.basicOpen (coordinatesFromIso e (MvPolynomial.X i)) :
      Set (polynomialScheme k I).left) = _
    rw [Scheme.preimage_basicOpen_top, coordinatesFromIso_apply, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, ← Over.comp_left, Iso.hom_inv_id, Over.id_left,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
    exact congrArg (fun U : (Spec (CommRingCat.of (MvPolynomial I k))).Opens ↦
      (U : Set (Spec (CommRingCat.of (MvPolynomial I k)))))
      (basicOpen_eq_of_affine (R := CommRingCat.of (MvPolynomial I k)) (MvPolynomial.X i))
  rw [show e.hom.left ⁻¹' Set.range (polynomialOrigin k I ≫ e.hom).left =
      Set.range (polynomialOrigin k I).left from ?_]
  · simp only [hcoord, polynomialOrigin_range, Set.compl_iInter, compl_compl]
  · rw [Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact e.hom.left.isOpenEmbedding.injective.preimage_image _

end Puncture

section BruhatCoordinates

open Specs.BruhatOrbitParametrization (conjugatePoint OrderedParametrization)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily rootProduct)
open Specs.CharacterPairing (characterValue)
open Specs.RootGroups (AdditiveLine rootPoint)
open private RootCoordinate RootCoordinate.line RootCoordinate.iso RootCoordinate.scalar
  rootCoordinate_exists productPoint productPoint_eq_iff productPoint_mul rootPoint_zero
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private existsEnumeration representativeConjugation conjugateInverse_mem_torus
  section_mem_of_le actionOnQuotient torus_translate_coset
  from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private groundPointIso from LinearAlgebraicGroups.Flag.BruhatCells
open private affine_subgroup from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem torusAction_quotient {G : AffineAlgebraicGroup k} {T B : ClosedSubgroup G.val}
    (Q : Presentation B) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    {Y : SchemeOver k} (t : Y ⟶ T.group.X) (z : Y ⟶ G.val.X) :
    lift t (z ≫ Q.projection) ≫ (torusAction T a).smul =
      ((t ≫ T.inclusion.hom.hom) * z) ≫ Q.projection := by
  change lift t (z ≫ Q.projection) ≫ (T.inclusion.hom.hom ▷ Q.scheme) ≫ a.smul = _
  rw [← tensorHom_id, lift_map_assoc, Category.comp_id]
  apply actionOnQuotient Q a _ _ _
  rw [ha]
  congr 1

private theorem productScaling {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {S : Set (Root T)}
    (x : ∀ α, RootCoordinate U α) {l : List (Root T)} (hl : Enumerates l S)
    (R : TestAlgebra k) (t : Points T.group.X R) (v : S → R) :
    let g := t ≫ T.inclusion.hom.hom
    let f := productPoint x R (extendRootTuple R v) l ≫ rootProduct U l
    g * f * g⁻¹ = productPoint x R
      (extendRootTuple R (fun α : S ↦ characterValue α.val.val R t * v α)) l ≫ rootProduct U l := by
  dsimp only
  rw [conjugate_orderedRootProduct]
  congr 1
  apply (productPoint_eq_iff x R _ _ l).mpr
  intro α hα
  have ha := (hl.2 α).mp hα
  simp only [extendRootTuple_of_mem _ ha]

private theorem productAtOrigin {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {S : Set (Root T)}
    (x : ∀ α, RootCoordinate U α) (l : List (Root T)) (R : TestAlgebra k) :
    productPoint x R (extendRootTuple R (0 : S → R)) l ≫ rootProduct U l = 1 := by
  rw [productPoint_mul]
  have h (a : Root T) :
      rootPoint ((RootCoordinate.iso (x a)).hom ≫ (U a).val.inclusion) R
        (extendRootTuple R (0 : S → R) a) = 1 := by
    have he : extendRootTuple R (0 : S → R) a = 0 := by
      classical
      by_cases ha : a ∈ S <;> simp [extendRootTuple, ha]
    rw [he, rootPoint_zero]
  simp only [h, List.map_const', List.prod_replicate, one_pow]

private theorem orderedCellCoordinates {G : AffineAlgebraicGroup k}
    {T B H : ClosedSubgroup G.val} (hG : Specs.GeometricRadicals.IsReductive G)
    (hT : Specs.GeometricRadicals.IsSplitTorus T.group)
    (hmax : Specs.RankOneFlag.IsGeometricallyMaximal T) [Finite (Root T)]
    (Q : Presentation B) (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    [IsCommMonObj T.group.X] {D : Datum T} (J : Identification D)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X}
    (hn : IsRepresentative J w n) (hTB : Specs.SchemeDerivedGroup.IsSubgroupOf T B)
    (C : Cell (T := T) Q a (n ≫ J.normalizer.inclusion.hom.hom) H)
    (U : RootSubgroupFamily T) (S : Set (Root T)) (hS : OrderedParametrization U S H) :
    Nonempty (OrderedCellCoordinates C U S) := by
  let g := n ≫ J.normalizer.inclusion.hom.hom
  let x : ∀ α, RootCoordinate U α := fun α ↦ Classical.choice
    (rootCoordinate_exists RootData.RootGroups.rootSubgroups G hG T hT hmax U α)
  obtain ⟨l, hl⟩ := existsEnumeration S
  obtain ⟨e, he⟩ := hS l hl
  obtain ⟨p, hp⟩ := rootPolynomialIso x l hl
  let q := p ≪≫ e ≪≫ C.orbitIso
  let f := C.orbitInclusion
  haveI : IsImmersion f.left := C.orbitImmersion
  haveI : Mono f := Over.mono_of_mono_left f
  haveI : IsAffine T.group.X.left := affine_subgroup G.property.1 T
  have hformula (R : TestAlgebra k) (v : S → R) :
      (polynomialPoint R v ≫ q.hom) ≫ f =
        ((productPoint x R (extendRootTuple R v) l ≫ rootProduct U l) *
          (toUnit ((testSpec k).obj (op R)) ≫ g)) ≫ Q.projection := by
    calc
      _ = ((polynomialPoint R v ≫ p.hom) ≫ e.hom) ≫
          C.orbitIso.hom ≫ C.orbitInclusion := by simp [q, f, Category.assoc]
      _ = _ := by
        rw [hp, C.orbitIso_eq, ← Category.assoc, MonObj.comp_mul]
        simp only [Category.assoc, he, comp_toUnit_assoc, g]
  have hnT (Y : SchemeOver k) (t : Y ⟶ T.group.X) :
      conjugatePoint g⁻¹ (t ≫ T.inclusion.hom.hom) ∈ Specs.SubgroupSections B Y :=
    section_mem_of_le hTB (conjugateInverse_mem_torus g _
      (representativeConjugation J hn) ⟨t, rfl⟩)
  let χ : S → Character T.group := fun α ↦ α.val.val
  have hscale (R : TestAlgebra k) (t : Points T.group.X R) (v : S → R) :
      lift t ((polynomialPoint R v ≫ q.hom) ≫ f) ≫ (torusAction T a).smul =
        (polynomialPoint R (fun i ↦ characterValue (χ i) R t * v i) ≫ q.hom) ≫ f := by
    rw [hformula, hformula, torusAction_quotient Q a ha, ← mul_assoc,
      torus_translate_coset Q g hnT, productScaling x hl R t v]
  obtain ⟨b, c, hb, hc, hev⟩ := polynomialScaling_of_mono (torusAction T a) q f χ hscale
  have ho : polynomialOrigin k S ≫ q.hom = η[H.group.X] ≫ C.orbitIso.hom := by
    apply (cancel_mono f).mp
    change (polynomialOrigin k S ≫ q.hom) ≫ f = cellOrigin C ≫ C.orbitInclusion
    rw [cellOrigin_comp]
    apply (cancel_epi (groundPointIso k).inv).mp
    let R := CommAlgCat.of k k
    have h0 : (groundPointIso k).inv ≫ polynomialOrigin k S = polynomialPoint R 0 := by
      rw [← polynomialOrigin_point (I := S) R]
      congr 1
      exact Subsingleton.elim _ _
    rw [← Category.assoc, ← Category.assoc, h0, hformula, productAtOrigin, one_mul]
    have hunit : toUnit ((testSpec k).obj (op R)) = (groundPointIso k).inv :=
      Subsingleton.elim _ _
    rw [hunit, Category.assoc]
  have transportCoordinates {o o' : 𝟙_ (SchemeOver k) ⟶ C.orbit} (h : o = o')
      (c₀ : PolynomialCoordinates b o (fun i : S ↦ i.val.val⁻¹)) :
      (cast (congrArg (fun p ↦ PolynomialCoordinates b p (fun i : S ↦ i.val.val⁻¹)) h) c₀).coordinates =
        c₀.coordinates := by subst o'; rfl
  let c' : PolynomialCoordinates b (η[H.group.X] ≫ C.orbitIso.hom)
      (fun i : S ↦ i.val.val⁻¹) :=
    cast (congrArg (fun p ↦ PolynomialCoordinates b p (fun i : S ↦ i.val.val⁻¹)) ho) c
  have hc' : c'.coordinates = coordinatesFromIso q := by
    exact (transportCoordinates ho c).trans hc
  refine ⟨⟨l, hl, e, he,
    fun α ↦ ⟨RootCoordinate.line (x α.val), RootCoordinate.iso (x α.val)⟩,
    fun α ↦ RootCoordinate.scalar (x α.val), b, hb, c', ?_, ?_⟩⟩
  · intro R v i
    change evaluateFunction R (_ ≫ e.hom ≫ C.orbitIso.hom)
      (c'.coordinates (MvPolynomial.X i)) = v i
    rw [orderedPoint_eq_productPoint, ← hp, hc']
    simpa only [q, Iso.trans_hom, Category.assoc] using evaluate_coordinatesFromIso q R v i
  · rw [hc', ← ho]
    exact polynomialIso_puncture q

end BruhatCoordinates

section WeylCharts

open Specs.BruhatOrbitParametrization (conjugatePoint IsConjugateIntersection)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.OrderedRootProducts (RootSubgroupFamily rootProduct)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CharacterPairing (characterValue)
open private sectionProduct_radical_open sectionProduct_open sectionProduct_translate_open
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open private radicalProductFor from LinearAlgebraicGroups.Flag.OpenCell
open private RootCoordinate rootCoordinate_exists productPoint
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private existsEnumeration representativeConjugation quotient_rightMul
  from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private groundPointIso from LinearAlgebraicGroups.Flag.BruhatCells
open private affine_subgroup from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem weylChart
    {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G) (Q : Presentation P.negative)
    (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    [IsCommMonObj P.torus.group.X] [Finite (Root P.torus)] [Fintype (PositiveRoot P)]
    {D : Datum P.torus} (J : Identification D)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X}
    (hn : IsRepresentative J w n) (U : RootSubgroupFamily P.torus)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf P.torus B)
    (hOpp : Specs.OpenCell.AreOpposite P.torus P.negative B)
    (R : ClosedSubgroup B.group) (hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R) :
    ∃ C : FixedPointChart (torusAction P.torus a)
        (n ≫ J.normalizer.inclusion.hom.hom ≫ Q.projection) (cotangentWeight J w),
      Set.range C.inclusion.left =
        Set.range (((toUnit R.group.X ≫ n ≫ J.normalizer.inclusion.hom.hom) *
          (R.inclusion ≫ B.inclusion).hom.hom) ≫ Q.projection).left ∧
      (⋃ i : PositiveRoot P, (C.scheme.left.basicOpen
        (C.polynomial.coordinates (MvPolynomial.X i)) : Set C.scheme.left)) =
          (Set.range C.point.left)ᶜ := by
  let g := n ≫ J.normalizer.inclusion.hom.hom
  let s := (R.inclusion ≫ B.inclusion).hom.hom
  let f := ((toUnit R.group.X ≫ g) * s) ≫ Q.projection
  obtain ⟨_, _, _, _, _, _, decompose⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  obtain ⟨R₀, i, _, hR₀, _, hi, _, _, hfactor, _⟩ :=
    decompose P.negative P.negativeBorel P.inNegative
  obtain ⟨hOpen, _, _⟩ := Flag.OpenCell.openCell G P.reductive P.torus P.split P.maximal
    P.negative B P.negativeBorel hB P.inNegative hTB hOpp R R₀ hR hR₀
  have hOpenF : IsOpenImmersion f.left :=
    sectionProduct_open Q _ (sectionProduct_translate_open s g
      (sectionProduct_radical_open hi hfactor hOpen))
  letI : IsOpenImmersion f.left := hOpenF
  letI : Mono f := Over.mono_of_mono_left f
  letI : IsAffine P.torus.group.X.left := affine_subgroup G.property.1 P.torus
  obtain ⟨R', hR', hprod⟩ := RootData.OrderedRootProducts.borelRadicalProduct
    G P.reductive P.torus P.split P.maximal B hB hTB
  have hRoots : subgroupRoots P.torus B = subgroupRoots P.torus P.positive := by
    rw [hOpp, P.opposite, compl_compl]
  obtain ⟨l, hl⟩ := existsEnumeration (subgroupRoots P.torus P.positive)
  obtain ⟨r, hr⟩ := radicalProductFor U l hR hR' (hprod U l (by rw [hRoots]; exact hl))
  let roots : ∀ α, RootCoordinate U α := fun α ↦ Classical.choice
    (rootCoordinate_exists RootData.RootGroups.rootSubgroups G P.reductive
      P.torus P.split P.maximal U α)
  obtain ⟨p, hp⟩ := rootPolynomialIso roots l hl
  let q := p ≪≫ r
  have hcoord (A : TestAlgebra k) (v : PositiveRoot P → A) :
      polynomialPoint A v ≫ q.hom ≫ s =
        productPoint roots A (extendRootTuple A v) l ≫ rootProduct U l := by
    change polynomialPoint A v ≫ (p.hom ≫ r.hom) ≫ s = _
    have h' : r.hom ≫ s = rootProduct U l := hr
    simp only [Category.assoc]
    rw [h', ← Category.assoc, hp]
  have hformula (A : TestAlgebra k) (v : PositiveRoot P → A) :
      (polynomialPoint A v ≫ q.hom) ≫ f =
        ((toUnit ((testSpec k).obj (op A)) ≫ g) *
          (productPoint roots A (extendRootTuple A v) l ≫ rootProduct U l)) ≫ Q.projection := by
    let z := polynomialPoint A v ≫ q.hom
    change z ≫ (((toUnit R.group.X ≫ g) * s) ≫ Q.projection) = _
    rw [← Category.assoc, MonObj.comp_mul, comp_toUnit_assoc]
    have hz : z ≫ s = productPoint roots A (extendRootTuple A v) l ≫ rootProduct U l :=
      (Category.assoc _ _ _).trans (hcoord A v)
    rw [hz]
  let χ (i : PositiveRoot P) := (J.labelEquiv w).val i.val.val
  have heq : (fun i : PositiveRoot P ↦ (χ i)⁻¹) = cotangentWeight J w := by
    funext i
    exact (map_inv (J.labelEquiv w).val _).symm
  have hscale (A : TestAlgebra k) (t : Points P.torus.group.X A) (v : PositiveRoot P → A) :
      lift t ((polynomialPoint A v ≫ q.hom) ≫ f) ≫ (torusAction P.torus a).smul =
        (polynomialPoint A (fun i ↦ characterValue (χ i) A t * v i) ≫ q.hom) ≫ f := by
    let e := J.image.conjugation (J.labelEquiv w)
    let t' := t ≫ e.inv.hom.hom
    let b := t' ≫ i.hom.hom
    let tG := t ≫ P.torus.inclusion.hom.hom
    let tG' := t' ≫ P.torus.inclusion.hom.hom
    let gA := toUnit ((testSpec k).obj (op A)) ≫ g
    have hc := congrArg (fun u ↦ t' ≫ u) (representativeConjugation J hn)
    have htinv : t' ≫ (e.hom ≫ P.torus.inclusion).hom.hom = tG := by
      change (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom ≫ P.torus.inclusion.hom.hom = _
      have h := congrArg (fun h : P.torus.group ⟶ P.torus.group ↦ h.hom.hom) e.inv_hom_id
      change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ at h
      simp only [Category.assoc, reassoc_of% h, tG]
    simp only [conjugatePoint, MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc] at hc
    change t' ≫ (e.hom ≫ P.torus.inclusion).hom.hom = gA * tG' * gA⁻¹ at hc
    have ht : tG * gA = gA * tG' := by
      rw [← htinv, hc, inv_mul_cancel_right]
    have hb : b ≫ P.negative.inclusion.hom.hom = tG' :=
      congrArg (fun u : P.torus.group ⟶ G.val ↦ t' ≫ u.hom.hom) hi
    have hχ (j : PositiveRoot P) : characterValue (χ j) A t =
        characterValue j.val.val A t' := by
      unfold χ
      rw [J.image.characterAction]
      rfl
    rw [hformula, hformula, torusAction_quotient Q a ha]
    simp only [hχ]
    let z := productPoint roots A (extendRootTuple A v) l ≫ rootProduct U l
    rw [← productScaling roots hl A t' v]
    change (tG * (gA * z)) ≫ Q.projection = (gA * (tG' * z * tG'⁻¹)) ≫ Q.projection
    rw [← mul_assoc, ht]
    have he : (gA * (tG' * z * tG'⁻¹)) * (b ≫ P.negative.inclusion.hom.hom) =
        (gA * tG') * z := by rw [hb]; group
    rw [← he, quotient_rightMul]
  obtain ⟨act, coords, he, hcoords, _⟩ :=
    polynomialScaling_of_mono (torusAction P.torus a) q f χ hscale
  have hOrigin : (polynomialOrigin k (PositiveRoot P) ≫ q.hom) ≫ f =
      n ≫ J.normalizer.inclusion.hom.hom ≫ Q.projection := by
    apply (cancel_epi (groundPointIso k).inv).mp
    let A := CommAlgCat.of k k
    have hzero : (groundPointIso k).inv ≫ polynomialOrigin k (PositiveRoot P) =
        polynomialPoint A 0 := by
      rw [← polynomialOrigin_point (I := PositiveRoot P) A]
      congr 1
      exact Subsingleton.elim _ _
    have hleft : (groundPointIso k).inv ≫
        ((polynomialOrigin k (PositiveRoot P) ≫ q.hom) ≫ f) =
          (polynomialPoint A 0 ≫ q.hom) ≫ f := by
      simpa only [Category.assoc] using congrArg (fun p ↦ p ≫ q.hom ≫ f) hzero
    rw [hleft, hformula, productAtOrigin, mul_one]
    have hunit : toUnit ((testSpec k).obj (op A)) = (groundPointIso k).inv :=
      Subsingleton.elim _ _
    simp only [hunit, g, Category.assoc]
  let coords' : PolynomialCoordinates act (polynomialOrigin k (PositiveRoot P) ≫ q.hom)
      (cotangentWeight J w) :=
    ⟨coords.affine, coords.coordinates, coords.vanishes, fun i ↦ by
      rw [← heq]
      exact coords.weight i⟩
  refine ⟨⟨_, act, f, _, hOpenF, he, hOrigin, coords', cotangentBasisOfCoordinates coords'⟩,
    rfl, ?_⟩
  change (⋃ i : PositiveRoot P,
    (R.group.X.left.basicOpen (coords.coordinates (MvPolynomial.X i)) : Set R.group.X.left)) =
      (Set.range (polynomialOrigin k (PositiveRoot P) ≫ q.hom).left)ᶜ
  rw [hcoords]
  exact polynomialIso_puncture q

private theorem cell_range_subset_translate
    {G : AffineAlgebraicGroup k} {T B B' A H : ClosedSubgroup G.val}
    {Q : Presentation B} {a : ModObj G.val.X Q.scheme}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} {R : ClosedSubgroup B'.group}
    (C : Cell (T := T) Q a n H)
    (h : IsConjugateIntersection A (subgroupOfSubgroup B' R) H n) :
    Set.range C.orbitInclusion.left ⊆
      Set.range (((toUnit R.group.X ≫ n) * (R.inclusion ≫ B'.inclusion).hom.hom) ≫
        Q.projection).left := by
  let g := H.inclusion.hom.hom
  have hg : g ∈ Specs.SubgroupSections H H.group.X := by
    change ∃ b : H.group.X ⟶ H.group.X, b ≫ g = g
    exact ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨m₀, hm⟩ := ((h _ g).mp hg).2
  let m : H.group.X ⟶ R.group.X := m₀
  let f := ((toUnit R.group.X ≫ n) * (R.inclusion ≫ B'.inclusion).hom.hom) ≫ Q.projection
  have hm' : m ≫ (R.inclusion ≫ B'.inclusion).hom.hom = conjugatePoint n⁻¹ g := hm
  have he : m ≫ f = C.orbitIso.hom ≫ C.orbitInclusion := by
    rw [C.orbitIso_eq]
    change m ≫ (((toUnit R.group.X ≫ n) * (R.inclusion ≫ B'.inclusion).hom.hom) ≫
      Q.projection) = (g * (toUnit H.group.X ≫ n)) ≫ Q.projection
    rw [← Category.assoc, MonObj.comp_mul, comp_toUnit_assoc, hm']
    congr 1
    rw [conjugatePoint, GrpObj.comp_inv]
    group
  have hr : Set.range C.orbitInclusion.left =
      Set.range (C.orbitIso.hom ≫ C.orbitInclusion).left := by
    haveI : IsIso C.orbitIso.hom.left :=
      inferInstanceAs (IsIso ((Over.forget (Spec (CommRingCat.of k))).map C.orbitIso.hom))
    rw [Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      C.orbitIso.hom.left.surjective.range_eq, Set.image_univ]
  rw [hr, ← he, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

end WeylCharts

section SchemeSupports

open Scheme.IdealSheafData

variable {T : GroupScheme k} {X Y Z : SchemeOver k}

private theorem equivariant_of_comp_mono {a : ModObj T.X X} {b : ModObj T.X Y}
    {c : ModObj T.X Z} {f : Y ⟶ X} {g : Z ⟶ Y} [Mono f]
    (hf : IsEquivariantMap a b f) (hg : IsEquivariantMap a c (g ≫ f)) :
    IsEquivariantMap b c g := by
  apply (cancel_mono f).mp
  change (c.smul ≫ g) ≫ f = ((𝟙 T.X ⊗ₘ g) ≫ b.smul) ≫ f
  rw [Category.assoc, Category.assoc, hf, hg]
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]

private theorem equivariant_comp {a : ModObj T.X X} {b : ModObj T.X Y}
    {c : ModObj T.X Z} {f : Y ⟶ X} {g : Z ⟶ Y}
    (hf : IsEquivariantMap a b f) (hg : IsEquivariantMap b c g) :
    IsEquivariantMap a c (g ≫ f) := by
  change c.smul ≫ g ≫ f = _
  rw [← Category.assoc, hg, Category.assoc, hf]
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc]

private theorem preimage_invariantOpen {a : ModObj T.X X} {b : ModObj T.X Y}
    (f : Y ⟶ X) (hf : IsEquivariantMap a b f) (U : X.left.Opens)
    (hU : IsInvariantOpen a U) : IsInvariantOpen b (f.left ⁻¹ᵁ U) := by
  let q := 𝟙 T.X ⊗ₘ f
  have hcomp : q ≫ snd T.X X = snd T.X Y ≫ f := by simp [q]
  calc
    b.smul.left ⁻¹ᵁ (f.left ⁻¹ᵁ U) = (b.smul ≫ f).left ⁻¹ᵁ U := rfl
    _ = q.left ⁻¹ᵁ (a.smul.left ⁻¹ᵁ U) := by rw [hf]; rfl
    _ = q.left ⁻¹ᵁ ((snd T.X X).left ⁻¹ᵁ U) := by rw [hU]
    _ = (snd T.X Y).left ⁻¹ᵁ (f.left ⁻¹ᵁ U) := by
      change (q ≫ snd T.X X).left ⁻¹ᵁ U = (snd T.X Y ≫ f).left ⁻¹ᵁ U
      rw [hcomp]

private theorem invariantOpen_of_range {a : ModObj T.X X} {b : ModObj T.X Y}
    (j : Y ⟶ X) [IsOpenImmersion j.left] (h : IsEquivariantMap a b j) :
    IsInvariantOpen a j.left.opensRange := by
  apply TopologicalSpace.Opens.ext
  exact action_preimage_range_of_equivariant j h

private theorem restrictionGeometry_of_closed {a : ModObj T.X X} {b : ModObj T.X Y}
    (i : Y ⟶ X) [IsClosedImmersion i.left] (hi : IsEquivariantMap a b i)
    (h : RestrictionGeometry a) : RestrictionGeometry b := by
  haveI : LocallyOfFiniteType X.hom := h.1
  haveI : CompactSpace X.left := h.2.1
  haveI : IsSeparated X.hom := h.2.2.1
  have hft : LocallyOfFiniteType Y.hom := Over.w i ▸
    (inferInstance : LocallyOfFiniteType (i.left ≫ X.hom))
  have hsep : IsSeparated Y.hom :=
    Over.w i ▸ (inferInstance : IsSeparated (i.left ≫ X.hom))
  refine ⟨hft, QuasiCompact.compactSpace_of_compactSpace i.left, hsep, fun y ↦ ?_⟩
  obtain ⟨U, hU, hAff, hInv⟩ := h.2.2.2 (i.left y)
  exact ⟨i.left ⁻¹ᵁ U, hU, hAff.preimage i.left, preimage_invariantOpen i hi U hInv⟩

private theorem restrictionGeometry_of_open {a : ModObj T.X X} {b : ModObj T.X Y}
    (i : Y ⟶ X) [IsOpenImmersion i.left]
    (h : RestrictionGeometry a) (hcover : HasInvariantAffineCover b) : RestrictionGeometry b := by
  haveI : LocallyOfFiniteType X.hom := h.1
  haveI : CompactSpace X.left := h.2.1
  haveI : IsSeparated X.hom := h.2.2.1
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hft : LocallyOfFiniteType Y.hom :=
    Over.w i ▸ (inferInstance : LocallyOfFiniteType (i.left ≫ X.hom))
  have hsep : IsSeparated Y.hom :=
    Over.w i ▸ (inferInstance : IsSeparated (i.left ≫ X.hom))
  exact ⟨hft, QuasiCompact.compactSpace_of_compactSpace i.left, hsep, hcover⟩

private def closedOfSupport (a : ModObj T.X X) [LocallyOfFiniteType X.hom]
    [GeometricallyReduced T.X.hom] (K : Closeds X.left)
    (h : a.smul.left ⁻¹' (K : Set X.left) = (snd T.X X).left ⁻¹' (K : Set X.left)) :
    {V : InvariantClosed a // Set.range V.inclusion.left = (K : Set X.left)} :=
  Classical.choice (by
    obtain ⟨S, b, i, hi, hclosed, hb, hr⟩ :=
      exists_invariantClosedSubscheme a K h (reduced_closedScheme_product K)
    letI : IsClosedImmersion i.left := hclosed
    haveI : IsReduced i.left.image := by
      change IsReduced i.left.ker.subscheme
      rw [hi]
      exact vanishingSubschemeReduced K
    exact ⟨⟨⟨S, b, i, isReduced_of_isOpenImmersion i.left.toImage, hclosed, hb⟩, hr⟩⟩)

private def complementOfClosed (a : ModObj T.X X) (Z : InvariantClosed a) :
    InvariantComplement a Z := by
  haveI : IsClosedImmersion Z.inclusion.left := Z.closedImmersion
  let U : X.left.Opens :=
    ⟨_, Z.inclusion.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : IsInvariantOpen a U := by
    apply Opens.ext
    change a.smul.left ⁻¹' (Set.range Z.inclusion.left)ᶜ =
      (snd T.X X).left ⁻¹' (Set.range Z.inclusion.left)ᶜ
    rw [Set.preimage_compl, Set.preimage_compl,
      action_preimage_range_of_equivariant Z.inclusion Z.equivariant]
  exact ⟨openScheme X U, invariantOpenAction a U hU, openInclusion X U,
    inferInstance, invariantOpenInclusion_equivariant a U hU, Scheme.Opens.range_ι U⟩

private theorem reducedLiftThroughImmersion (g : Z ⟶ X) (f : Y ⟶ X)
    [IsImmersion g.left] [IsReduced Z.left] [IsReduced Y.left]
    (h : Set.range f.left ⊆ Set.range g.left) :
    ∃ e : Y ⟶ Z, e ≫ g = f := by
  let U := g.left.coborderRange
  let j := openInclusion X U
  let g₀ : Z ⟶ openScheme X U := Over.homMk g.left.liftCoborder (by
    change _ ≫ U.ι ≫ X.hom = _
    rw [Scheme.Hom.liftCoborder_ι_assoc, Over.w])
  have hg : g₀ ≫ j = g := Over.OverMorphism.ext (Scheme.Hom.liftCoborder_ι g.left)
  letI : IsClosedImmersion g₀.left := inferInstanceAs (IsClosedImmersion g.left.liftCoborder)
  let hF : Set.range f.left ⊆ Set.range j.left := by
    rw [← hg, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at h
    exact h.trans (Set.image_subset_range _ _)
  let f₀ : Y ⟶ openScheme X U := Over.homMk
    (IsOpenImmersion.lift j.left f.left hF) (by
      change IsOpenImmersion.lift j.left f.left hF ≫ j.left ≫ X.hom = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w])
  have hf : f₀ ≫ j = f := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have h₀ : Set.range f₀.left ⊆ Set.range g₀.left := by
    have h' := h
    rw [← hg, ← hf, Over.comp_left, Over.comp_left, Scheme.Hom.comp_base,
      Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp,
      Set.range_comp, Set.range_comp] at h'
    exact Set.image_subset_image_iff j.left.isOpenEmbedding.injective |>.mp h'
  exact ⟨liftReducedClosed g₀ f₀ h₀, by rw [← hg, liftReducedClosed_fac_assoc, hf]⟩

/-- Two reduced locally closed subschemes with the same image identify
canonically over their ambient scheme. -/
private theorem reducedImmersionsIso (f : Y ⟶ X) (g : Z ⟶ X)
    [IsImmersion f.left] [IsImmersion g.left] [IsReduced Y.left] [IsReduced Z.left]
    (h : Set.range f.left = Set.range g.left) :
    ∃ e : Y ≅ Z, e.hom ≫ g = f := by
  obtain ⟨m, hm⟩ := reducedLiftThroughImmersion g f h.le
  obtain ⟨n, hn⟩ := reducedLiftThroughImmersion f g h.ge
  haveI : Mono f := Over.mono_of_mono_left f
  haveI : Mono g := Over.mono_of_mono_left g
  exact ⟨⟨m, n, (cancel_mono f).mp (by simp [Category.assoc, hm, hn]),
    (cancel_mono g).mp (by simp [Category.assoc, hm, hn])⟩, hm⟩

end SchemeSupports

section AffineCovers

open Specs.CharacterPairing (characterValue)
open private characterValue_one from LinearAlgebraicGroups.RootData.CharacterPairing

variable {T : GroupScheme k} {X Y Z : SchemeOver k}

private theorem characterFunction_isUnit (χ : Character T) :
    IsUnit (characterFunction χ) := by
  unfold characterFunction
  apply IsUnit.map χ.hom.hom.left.appTop.hom
  apply IsUnit.map (Scheme.ΓSpecIso _).inv.hom
  exact (Group.isUnit _).map (MonoidAlgebra.of k _)

private theorem basicOpen_invariant {a : ModObj T.X X} {f : Γ(X.left, ⊤)}
    {χ : Character T} (h : HasFunctionWeight a f χ) :
    IsInvariantOpen a (X.left.basicOpen f) := by
  unfold IsInvariantOpen
  rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top, h, Scheme.basicOpen_mul]
  let A := (T.X ⊗ X).left
  let u : Γ(A, ⊤) := (fst T.X X).left.appTop (characterFunction χ⁻¹)
  let r : Γ(A, ⊤) := (snd T.X X).left.appTop f
  have hu : IsUnit u := (characterFunction_isUnit χ⁻¹).map (fst T.X X).left.appTop.hom
  change A.basicOpen u ⊓ A.basicOpen r = A.basicOpen r
  rw [A.basicOpen_of_isUnit hu, top_inf_eq]

private theorem evaluateFunction_section (R : TestAlgebra k) (y : 𝟙_ (SchemeOver k) ⟶ X)
    (f : Γ(X.left, ⊤)) :
    evaluateFunction R (toUnit ((testSpec k).obj (op R)) ≫ y) f =
      algebraMap k R (pointEvaluation y f) := by
  let φ := CommRingCat.ofHom (algebraMap k R)
  have hγ : (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ φ := by
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).inv).mp
    rw [← Category.assoc _ (Scheme.ΓSpecIso (CommRingCat.of k)).hom, Iso.inv_hom_id,
      Category.id_comp, ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [evaluateFunction_comp]
  change ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) (y.left.appTop f) = _
  rw [hγ]
  rfl

private theorem vanishes_on_fixedSection {a : ModObj T.X X}
    (hT : Specs.GeometricRadicals.IsSplitTorus T) (y : 𝟙_ (SchemeOver k) ⟶ X)
    (hy : IsEquivariantMap a (pointAction T) y) {f : Γ(X.left, ⊤)}
    {χ : Character T} (hχ : χ ≠ 1) (hf : HasFunctionWeight a f χ) :
    y.left.appTop f = 0 := by
  let d := pointEvaluation y f
  have hd : d = 0 := by
    by_contra hn
    have hchar : χ⁻¹ = (1 : Character T) := by
      apply LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters hT
      intro R t₀
      let t : Points T.X R := t₀
      let o := toUnit ((testSpec k).obj (op R))
      have he : lift t (o ≫ y) ≫ a.smul = o ≫ y := by
        have hl : lift t o ≫ (𝟙 T.X ⊗ₘ y) = lift t (o ≫ y) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [← hl, Category.assoc, ← hy]
        exact lift_snd_assoc _ _ _
      let p : Points (T.X ⊗ X) R := lift t (o ≫ y)
      have hv : evaluateFunction R (p ≫ a.smul) f =
          characterValue χ⁻¹ R t₀ * evaluateFunction R (o ≫ y) f := by
        let c : Γ((T.X ⊗ X).left, ⊤) := (fst T.X X).left.appTop (characterFunction χ⁻¹)
        let r : Γ((T.X ⊗ X).left, ⊤) := (snd T.X X).left.appTop f
        calc
          _ = evaluateFunction R p (a.smul.left.appTop f) := evaluateFunction_comp R p a.smul f
          _ = evaluateFunction R p (c * r) := congrArg (evaluateFunction R p) hf
          _ = _ := by
            rw [map_mul]
            have hc := (evaluateFunction_comp R p (fst T.X X) (characterFunction χ⁻¹)).symm
            have hr := (evaluateFunction_comp R p (snd T.X X) f).symm
            rw [show evaluateFunction R p c = _ from hc, show evaluateFunction R p r = _ from hr]
            simp only [p, lift_fst, lift_snd, evaluateFunction_character]
            rfl
      change evaluateFunction R (lift t (o ≫ y) ≫ a.smul) f = _ at hv
      rw [he, evaluateFunction_section] at hv
      have hu : IsUnit (algebraMap k R d) := (isUnit_iff_ne_zero.mpr hn).map (algebraMap k R)
      have hc : (1 : R) = characterValue χ⁻¹ R t₀ :=
        hu.mul_right_cancel ((one_mul _).trans hv)
      exact hc.symm.trans (characterValue_one R t).symm
    exact hχ (inv_eq_one.mp hchar)
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
  exact hd.trans (map_zero _).symm

private theorem invariantAffineOpen_of_range_subset
    {a : ModObj T.X X} {b : ModObj T.X Y} {c : ModObj T.X Z}
    (i : Z ⟶ X) (j : Y ⟶ X) [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    [IsAffine Z.left] (hi : IsEquivariantMap a c i) (hj : IsEquivariantMap a b j)
    (h : Set.range i.left ⊆ Set.range j.left) {y : Y.left} (hy : j.left y ∈ Set.range i.left) :
    ∃ U : Y.left.Opens, y ∈ U ∧ IsAffineOpen U ∧ IsInvariantOpen b U := by
  let l : Z ⟶ Y := Over.homMk (IsOpenImmersion.lift j.left i.left h)
    (by
      rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w i])
  have hl : l ≫ j = i := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ h)
  haveI : IsOpenImmersion (l.left ≫ j.left) := by rwa [← Over.comp_left, hl]
  haveI : IsOpenImmersion l.left := IsOpenImmersion.of_comp l.left j.left
  haveI : Mono j := Over.mono_of_mono_left j
  refine ⟨l.left.opensRange, ?_, isAffineOpen_opensRange l.left,
    invariantOpen_of_range l (equivariant_of_comp_mono hj (hl.symm ▸ hi))⟩
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, j.left.isOpenEmbedding.injective ?_⟩
  exact (congrArg (fun f : Z ⟶ X ↦ f.left z) hl).trans hz

private theorem hasInvariantAffineCover_of_puncture
    {a : ModObj T.X X} {b : ModObj T.X Y} {I : Type u} {o : 𝟙_ (SchemeOver k) ⟶ X}
    {ν : I → Character T} (p : PolynomialCoordinates a o ν)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (hj : IsEquivariantMap a b j)
    (hr : Set.range j.left =
      ⋃ i : I, (X.left.basicOpen (p.coordinates (MvPolynomial.X i)) : Set X.left)) :
    HasInvariantAffineCover b := by
  intro y
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hr ▸ Set.mem_range_self y)
  let U := X.left.basicOpen (p.coordinates (MvPolynomial.X i))
  haveI : IsAffine X.left := p.affine
  haveI : IsAffine (openScheme X U).left :=
    (isAffineOpen_top X.left).basicOpen (p.coordinates (MvPolynomial.X i))
  let hU : IsInvariantOpen a U := basicOpen_invariant (p.weight i)
  have hUr : Set.range (openInclusion X U).left = (U : Set X.left) := Scheme.Opens.range_ι U
  apply invariantAffineOpen_of_range_subset (openInclusion X U) j
    (invariantOpenInclusion_equivariant a U hU) hj
  · rw [hUr, hr]
    exact Set.subset_iUnion
      (fun j : I ↦ (X.left.basicOpen (p.coordinates (MvPolynomial.X j)) : Set X.left)) i
  · rw [hUr]
    exact hi

private theorem polynomialCoordinates_isReduced
    {a : ModObj T.X X} {I : Type u} {o : 𝟙_ (SchemeOver k) ⟶ X}
    {ν : I → Character T} (p : PolynomialCoordinates a o ν) : IsReduced X.left := by
  letI : IsAffine X.left := p.affine
  letI : Algebra k Γ(X.left, ⊤) := (groundRingHom X).toAlgebra
  letI : _root_.IsReduced Γ(X.left, ⊤) :=
    isReduced_of_injective p.coordinates.symm.toRingEquiv.toRingHom p.coordinates.symm.injective
  exact isReduced_of_isAffine_isReduced X.left

end AffineCovers

section Filtration

variable {T : GroupScheme k} {X Y Z : SchemeOver k}

private theorem range_over_comp (f : Z ⟶ Y) (g : Y ⟶ X) :
    Set.range (f ≫ g).left = g.left '' Set.range f.left := by
  rw [Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

private def prefixSupport {W S : Type u} {m : ℕ} (F : W → Set S)
    (e : Fin m ≃ W) (j : ℕ) : Set S :=
  ⋃ i : Fin m, ⋃ (_ : i.val < j), F (e i)

private theorem prefixSupport_mono {W S : Type u} {m : ℕ} (F : W → Set S) (e : Fin m ≃ W) :
    Monotone (prefixSupport F e) := by
  intro i j hij z hz
  simp only [prefixSupport, Set.mem_iUnion, exists_prop] at hz ⊢
  obtain ⟨r, hr, hz⟩ := hz
  exact ⟨r, hr.trans_le hij, hz⟩

private theorem prefixSupport_sdiff {W S : Type u} {m : ℕ} (F : W → Set S) (e : Fin m ≃ W)
    (hd : Pairwise (fun v w ↦ Disjoint (F v) (F w))) (i : Fin m) :
    prefixSupport F e (i.val + 1) \ prefixSupport F e i.val = F (e i) := by
  ext z
  simp only [Set.mem_sdiff, prefixSupport, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨j, hj, hz⟩, hn⟩
    have he : j = i := Fin.ext (by
      by_contra hne
      exact hn ⟨j, by omega, hz⟩)
    simpa only [he] using hz
  · refine fun hz ↦ ⟨⟨i, Nat.lt_succ_self _, hz⟩, ?_⟩
    rintro ⟨j, hj, hz'⟩
    have hne : e j ≠ e i := fun h ↦ (Nat.ne_of_lt hj) (congrArg Fin.val (e.injective h))
    exact Set.disjoint_left.mp (hd hne) hz' hz

private theorem preimage_fixedUnion {W : Type u} {cells : W → SchemeOver k}
    (inc : ∀ w, cells w ⟶ X) (o : ∀ w, 𝟙_ (SchemeOver k) ⟶ cells w)
    (hinj : ∀ w, Function.Injective (inc w).left)
    (hd : Pairwise (fun v w ↦ Disjoint (Set.range (inc v).left) (Set.range (inc w).left))) (w : W) :
    (inc w).left ⁻¹' (⋃ v, Set.range (o v ≫ inc v).left) = Set.range (o w).left := by
  ext z
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
    have he : v = w := by
      by_contra hne
      have hl : (inc w).left z ∈ Set.range (inc v).left := by
        rw [range_over_comp] at hv
        exact Set.image_subset_range _ _ hv
      exact Set.disjoint_left.mp (hd hne) hl (Set.mem_range_self z)
    subst v
    rw [range_over_comp] at hv
    obtain ⟨y, hy, h⟩ := hv
    exact hinj w h ▸ hy
  · rintro ⟨z, rfl⟩
    exact Set.mem_iUnion.mpr ⟨w, ⟨z, rfl⟩⟩

/-- Closed prefixes restrict to the complement. The difference of successive
prefixes is the punctured cell with its reduced induced scheme structure. -/
private theorem complementFiltration
    {a : ModObj T.X X} (Z : InvariantClosed a) (V : InvariantComplement a Z)
    [GeometricallyReduced T.X.hom] [IsReduced V.scheme.left] (hV : RestrictionGeometry V.action)
    {W : Type u} {m : ℕ} (e : Fin m ≃ W)
    (cells : W → SchemeOver k) (act : ∀ w, ModObj T.X (cells w))
    (inc : ∀ w, cells w ⟶ X) (o : ∀ w, 𝟙_ (SchemeOver k) ⟶ cells w)
    (hi : ∀ w, IsImmersion (inc w).left)
    (he : ∀ w, IsEquivariantMap a (act w) (inc w))
    (hd : Pairwise (fun v w ↦ Disjoint (Set.range (inc v).left) (Set.range (inc w).left)))
    (hc : (⋃ w, Set.range (inc w).left) = Set.univ)
    (hp : ClosedPrefixes (fun w ↦ Set.range (inc w).left) e)
    (hz : Set.range Z.inclusion.left = ⋃ w, Set.range (o w ≫ inc w).left)
    {I : W → Type u} {ν : ∀ w, I w → Character T}
    (coordinates : ∀ w, PolynomialCoordinates (act w) (o w) (ν w))
    (hpuncture : ∀ w, (⋃ i : I w, ((cells w).left.basicOpen
      ((coordinates w).coordinates (MvPolynomial.X i)) : Set (cells w).left)) =
        (Set.range (o w).left)ᶜ) :
    Nonempty (ComplementFiltration a Z V cells act inc o) := by
  let F w := Set.range (inc w).left
  let q := V.inclusion
  let K (j : ℕ) := q.left ⁻¹' prefixSupport F e j
  letI : LocallyOfFiniteType V.scheme.hom := hV.1
  haveI : IsOpenImmersion q.left := V.openImmersion
  haveI (w : W) : IsImmersion (inc w).left := hi w
  haveI (w : W) : IsReduced (cells w).left := polynomialCoordinates_isReduced (coordinates w)
  have hK (j : ℕ) : IsClosed (K j) := (hp j).preimage q.left.continuous
  have hInv (j : ℕ) : V.action.smul.left ⁻¹' K j = (snd T.X V.scheme).left ⁻¹' K j := by
    have H : a.smul.left ⁻¹' prefixSupport F e j =
        (snd T.X X).left ⁻¹' prefixSupport F e j := by
      simp only [prefixSupport, Set.preimage_iUnion]
      exact Set.iUnion_congr fun i ↦ Set.iUnion_congr fun _ ↦
        action_preimage_range_of_equivariant (inc (e i)) (he (e i))
    have h : (𝟙 T.X ⊗ₘ q) ≫ snd T.X X = snd T.X V.scheme ≫ q := by simp
    calc
      _ = (V.action.smul ≫ V.inclusion).left ⁻¹' prefixSupport F e j := rfl
      _ = (𝟙 T.X ⊗ₘ q).left ⁻¹' (a.smul.left ⁻¹' prefixSupport F e j) := by
        rw [V.equivariant]
        rfl
      _ = (𝟙 T.X ⊗ₘ q).left ⁻¹' ((snd T.X X).left ⁻¹' prefixSupport F e j) := by rw [H]
      _ = _ := by
        change ((𝟙 T.X ⊗ₘ q) ≫ snd T.X X).left ⁻¹' prefixSupport F e j =
          (snd T.X V.scheme ≫ q).left ⁻¹' prefixSupport F e j
        rw [h]
  let stage (j : Fin (m + 1)) := closedOfSupport V.action ⟨K j.val, hK j.val⟩ (hInv j.val)
  have hstage (j : Fin (m + 1)) : Set.range (stage j).1.inclusion.left = K j.val :=
    (stage j).2
  haveI (j : Fin (m + 1)) : IsClosedImmersion (stage j).1.inclusion.left := (stage j).1.closedImmersion
  haveI (j : Fin (m + 1)) : IsReduced (stage j).1.scheme.left := (stage j).1.reduced
  have hgeom (j : Fin (m + 1)) : RestrictionGeometry (stage j).1.action :=
    restrictionGeometry_of_closed (stage j).1.inclusion (stage j).1.equivariant hV
  refine ⟨⟨m, e, fun j ↦ (stage j).1, hgeom, ?_, ?_, ?_⟩⟩
  · apply (Set.range_eq_empty_iff (f := (stage 0).1.inclusion.left)).mp
    rw [hstage]
    simp [K, prefixSupport]
  · have hr : K m = Set.univ := by
      have heq : prefixSupport F e m = ⋃ w, F w := by
        simp only [prefixSupport, Fin.is_lt, Set.iUnion_true]
        exact e.surjective.iUnion_comp F
      rw [show K m = q.left ⁻¹' prefixSupport F e m from rfl, heq, hc, Set.preimage_univ]
    haveI : Surjective (stage (Fin.last m)).1.inclusion.left :=
      ⟨Set.range_eq_univ.mp ((hstage _).trans hr)⟩
    haveI : IsIso (stage (Fin.last m)).1.inclusion.left :=
      isIso_of_isClosedImmersion_of_surjective _
    haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map
        (stage (Fin.last m)).1.inclusion) := ‹_›
    exact isIso_of_reflects_iso _ (Over.forget _)
  · intro i
    let A := (stage i.castSucc).1
    let B := (stage i.succ).1
    let prev := A.inclusion
    let next := B.inclusion
    have hs : Set.range prev.left ⊆ Set.range next.left := by
      change Set.range (stage i.castSucc).1.inclusion.left ⊆
        Set.range (stage i.succ).1.inclusion.left
      rw [hstage, hstage]
      exact Set.preimage_mono (prefixSupport_mono F e (Nat.le_succ i.val))
    let j := liftReducedClosed next prev hs
    have hj : j ≫ next = prev := liftReducedClosed_fac next prev hs
    haveI : IsClosedImmersion (j.left ≫ next.left) := by
      rw [← Over.comp_left, hj]
      exact A.closedImmersion
    haveI : IsClosedImmersion j.left := IsClosedImmersion.of_comp_isClosedImmersion j.left next.left
    haveI : Mono next := Over.mono_of_mono_left next
    have hje : IsEquivariantMap B.action A.action j :=
      equivariant_of_comp_mono B.equivariant (hj.symm ▸ A.equivariant)
    let S : InvariantClosed B.action := ⟨A.scheme, A.action, j, A.reduced, inferInstance, hje⟩
    let O := complementOfClosed B.action S
    let p : O.scheme ⟶ X := (O.inclusion ≫ next) ≫ q
    letI : IsOpenImmersion O.inclusion.left := O.openImmersion
    letI : IsReduced O.scheme.left := isReduced_of_isOpenImmersion O.inclusion.left
    haveI : IsImmersion p.left := by dsimp [p]; infer_instance
    have hO : Set.range (O.inclusion ≫ next).left = K (i.val + 1) \ K i.val := by
      rw [range_over_comp, O.range_eq]
      change next.left '' (Set.range j.left)ᶜ = _
      rw [Set.image_compl_eq_range_sdiff_image next.left.isClosedEmbedding.injective,
        ← range_over_comp, hj]
      exact congrArg₂ SDiff.sdiff (hstage i.succ) (hstage i.castSucc)
    have hp' : Set.range p.left = F (e i) \ Set.range Z.inclusion.left := by
      rw [range_over_comp, hO]
      change q.left '' ((q.left ⁻¹' prefixSupport F e (i.val + 1)) \
        (q.left ⁻¹' prefixSupport F e i.val)) = _
      rw [← Set.preimage_sdiff, prefixSupport_sdiff F e hd, Set.image_preimage_eq_range_inter,
        V.range_eq, Set.sdiff_eq, Set.inter_comm]
    let U : (cells (e i)).left.Opens :=
      ⟨(Set.range (o (e i)).left)ᶜ, by
        rw [← hpuncture]
        exact isOpen_iUnion fun i' ↦ ((cells (e i)).left.basicOpen _).isOpen⟩
    let d := openInclusion (cells (e i)) U
    have hU : Set.range d.left = (Set.range (o (e i)).left)ᶜ := Scheme.Opens.range_ι U
    have hd' : Set.range (d ≫ inc (e i)).left = Set.range p.left := by
      have hpre : (inc (e i)).left ⁻¹' Set.range Z.inclusion.left =
          Set.range (o (e i)).left := by
        rw [hz]
        exact preimage_fixedUnion inc o (fun w ↦ (inc w).left.isEmbedding.injective) hd (e i)
      rw [range_over_comp, hU, ← hpre, Set.image_compl_preimage, hp']
    haveI : IsImmersion (d ≫ inc (e i)).left := by rw [Over.comp_left]; infer_instance
    haveI : IsReduced (openScheme (cells (e i)) U).left := isReduced_of_isOpenImmersion d.left
    obtain ⟨E, hE⟩ := reducedImmersionsIso p (d ≫ inc (e i)) hd'.symm
    let l := E.hom ≫ d
    have hl : l ≫ inc (e i) = O.inclusion ≫ next ≫ q := by
      simpa only [l, p, Category.assoc] using hE
    haveI : IsOpenImmersion l.left := by dsimp [l]; infer_instance
    haveI : Mono (inc (e i)) := Over.mono_of_mono_left _
    have hle : IsEquivariantMap (act (e i)) O.action l :=
      equivariant_of_comp_mono (he (e i)) (hl.symm ▸
        equivariant_comp (equivariant_comp V.equivariant B.equivariant) O.equivariant)
    have hlrange : Set.range l.left = (Set.range (o (e i)).left)ᶜ := by
      rw [range_over_comp, E.hom.left.surjective.range_eq, Set.image_univ, hU]
    have hcover : HasInvariantAffineCover O.action :=
      hasInvariantAffineCover_of_puncture (coordinates (e i)) l hle
        (hlrange.trans (hpuncture (e i)).symm)
    refine ⟨S, Iso.refl _, ?_, ?_, O, l, inferInstance, hle, hlrange, hl, ?_⟩
    · simpa only [Iso.refl_hom, Category.id_comp] using hj.symm
    · simp [IsEquivariantMap]
    · exact restrictionGeometry_of_open O.inclusion (hgeom i.succ) hcover

end Filtration

section ChartCovers

variable {T : GroupScheme k} {X Y : SchemeOver k}

private theorem chartBasicOpen_disjoint_fixedSection
    {a : ModObj T.X X} {b : ModObj T.X Y} (hT : Specs.GeometricRadicals.IsSplitTorus T)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (hj : IsEquivariantMap a b j)
    (x : 𝟙_ (SchemeOver k) ⟶ X) (hx : IsEquivariantMap a (pointAction T) x)
    {f : Γ(Y.left, ⊤)} {χ : Character T} (hχ : χ ≠ 1) (hf : HasFunctionWeight b f χ) :
    Disjoint (Set.range (openInclusion Y (Y.left.basicOpen f) ≫ j).left) (Set.range x.left) := by
  let U := Y.left.basicOpen f
  let i := openInclusion Y U
  apply Set.disjoint_left.mpr
  rintro _ ⟨v, rfl⟩ ⟨z, hz⟩
  have hr : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨z', rfl⟩
    haveI : Subsingleton ((𝟙_ (SchemeOver k) : SchemeOver k).left) :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
    rw [Subsingleton.elim z' z, hz]
    exact ⟨i.left v, rfl⟩
  let y : 𝟙_ (SchemeOver k) ⟶ Y := Over.homMk (IsOpenImmersion.lift j.left x.left hr)
    (by rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w x])
  have hy : y ≫ j = x := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ hr)
  haveI : Mono j := Over.mono_of_mono_left j
  have hye : IsEquivariantMap b (pointAction T) y := equivariant_of_comp_mono hj (hy.symm ▸ hx)
  have hzero := vanishes_on_fixedSection hT y hye hχ hf
  have hp : y.left z = i.left v := j.left.isOpenEmbedding.injective
    ((congrArg (fun g : 𝟙_ (SchemeOver k) ⟶ X ↦ g.left z) hy).trans hz)
  have hmem : y.left z ∈ U := hp.symm ▸ v.property
  have hpre : y.left ⁻¹ᵁ U = ⊥ := by
    change y.left ⁻¹ᵁ Y.left.basicOpen f = ⊥
    rw [Scheme.preimage_basicOpen_top]
    exact (congrArg (fun r : Γ((𝟙_ (SchemeOver k) : SchemeOver k).left, ⊤) ↦
      (𝟙_ (SchemeOver k) : SchemeOver k).left.basicOpen r) hzero).trans
        (Scheme.basicOpen_zero _ _)
  have hmem' : z ∈ y.left ⁻¹ᵁ U := hmem
  rw [hpre] at hmem'
  exact hmem'

private theorem invariantAffineCover_of_charts
    {a : ModObj T.X X} {W I : Type u} {x : W → (𝟙_ (SchemeOver k) ⟶ X)}
    {ν : W → I → Character T} (C : ∀ w, FixedPointChart a (x w) (ν w))
    (hcover : ∀ y : X.left, ∃ w, y ∈ Set.range (C w).inclusion.left) :
    HasInvariantAffineCover a := by
  intro y
  obtain ⟨w, hw⟩ := hcover y
  haveI : IsOpenImmersion (C w).inclusion.left := (C w).openImmersion
  haveI : IsAffine (C w).scheme.left := (C w).polynomial.affine
  exact ⟨(C w).inclusion.left.opensRange, hw, isAffineOpen_opensRange _,
    invariantOpen_of_range (C w).inclusion (C w).equivariant⟩

private theorem complementAffineCover_of_charts
    {a : ModObj T.X X} (S : InvariantClosed a) (V : InvariantComplement a S)
    (hT : Specs.GeometricRadicals.IsSplitTorus T)
    {W I : Type u} {x : W → (𝟙_ (SchemeOver k) ⟶ X)} {ν : W → I → Character T}
    (C : ∀ w, FixedPointChart a (x w) (ν w))
    (hν : ∀ w i, ν w i ≠ 1)
    (hx : ∀ w, IsEquivariantMap a (pointAction T) (x w))
    (hS : Set.range S.inclusion.left = ⋃ w, Set.range (x w).left)
    (hcover : ∀ y : X.left, ∃ w, y ∈ Set.range (C w).inclusion.left)
    (hpuncture : ∀ w, (⋃ i : I, ((C w).scheme.left.basicOpen
      ((C w).polynomial.coordinates (MvPolynomial.X i)) : Set (C w).scheme.left)) =
        (Set.range (C w).point.left)ᶜ) :
    HasInvariantAffineCover V.action := by
  intro y
  obtain ⟨w, z, hz⟩ := hcover (V.inclusion.left y)
  have hz' : z ∈ (Set.range (C w).point.left)ᶜ := by
    rintro ⟨v, rfl⟩
    have h : V.inclusion.left y ∈ Set.range S.inclusion.left := by
      rw [hS]
      exact Set.mem_iUnion.mpr ⟨w, v,
        (congrArg (fun p : 𝟙_ (SchemeOver k) ⟶ X ↦ p.left v) (C w).over).symm.trans hz⟩
    exact (V.range_eq ▸ Set.mem_range_self y) h
  rw [← hpuncture] at hz'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz'
  let U := (C w).scheme.left.basicOpen ((C w).polynomial.coordinates (MvPolynomial.X i))
  let j := openInclusion (C w).scheme U
  let f := j ≫ (C w).inclusion
  haveI : IsOpenImmersion (C w).inclusion.left := (C w).openImmersion
  haveI : IsOpenImmersion V.inclusion.left := V.openImmersion
  haveI : IsOpenImmersion f.left := by dsimp [f]; infer_instance
  haveI : IsAffine (C w).scheme.left := (C w).polynomial.affine
  haveI : IsAffine (openScheme (C w).scheme U).left :=
    (isAffineOpen_top _).basicOpen ((C w).polynomial.coordinates (MvPolynomial.X i))
  have hU : IsInvariantOpen (C w).action U := basicOpen_invariant ((C w).polynomial.weight i)
  have hf := equivariant_comp (C w).equivariant
    (invariantOpenInclusion_equivariant (C w).action U hU)
  apply invariantAffineOpen_of_range_subset f V.inclusion hf V.equivariant
  · rw [V.range_eq, hS]
    intro p hp hp'
    obtain ⟨w', hw'⟩ := Set.mem_iUnion.mp hp'
    exact Set.disjoint_left.mp (chartBasicOpen_disjoint_fixedSection hT
      (C w).inclusion (C w).equivariant (x w') (hx w') (hν w i) ((C w).polynomial.weight i))
      hp hw'
  · exact ⟨⟨z, hi⟩, hz⟩

end ChartCovers

/-- The split opposite-Borel flag has the fixed-point charts and the
invariant Bruhat filtration used in equivariant localization. -/
theorem flagLocalizationGeometry : Statement.{u} := by
  classical
  intro k _ G P Q a ha
  obtain ⟨hT, D, J, U, B', Rneg, Rpos, _, _, hB', hTB', hOpp, _, hRpos,
    _, _, _, hrep, _, hQ⟩ :=
    LinearAlgebraicGroups.Flag.BruhatCells.bruhatCells G P.reductive P.torus P.negative
      P.split P.maximal P.negativeBorel P.inNegative
  letI := hT
  obtain ⟨a', ha', hcells⟩ := hQ Q
  have he := flagAction_unique Q a a' ha ha'
  subst a'
  letI : Finite (Root P.torus) := D.finiteRoots
  letI : Finite J.image.labels := J.image.finite
  letI : Finite D.rootDatum.weylGroup := Finite.of_injective J.labelEquiv J.labelEquiv.injective
  letI : Fintype D.rootDatum.weylGroup := Fintype.ofFinite _
  letI : Fintype (PositiveRoot P) := Fintype.ofFinite _
  refine ⟨hT, D, J, inferInstance, inferInstance, hrep, ?_⟩
  intro n hn g x t
  let W := D.rootDatum.weylGroup
  obtain ⟨A, C, hC, hd, _, hc⟩ := hcells n hn
  have hdisj : Pairwise (fun (v w : W) ↦
      Disjoint (Set.range (C v).orbitInclusion.left) (Set.range (C w).orbitInclusion.left)) :=
    fun _ _ h ↦ (hd _ _ h).1
  have hfix (K : Type u) [Field K] [Algebra k K]
      (y : Over.mk (fieldSpecMap k K) ⟶ Q.scheme) :
      FixedOver (T := P.torus) a y ↔ ∃! w, y = toUnit _ ≫ x w := by
    simpa only [x, g, Category.assoc] using fixedOver_iff_of_cells g A C hdisj hc K y
  have hcoset (w : W) : cellOrigin (C w) ≫ (C w).orbitInclusion = x w := cellOrigin_comp (C w)
  have hsub (w : W) : Set.range (x w).left ⊆ Set.range (C w).orbitInclusion.left := by
    rw [← hcoset, range_over_comp]
    exact Set.image_subset_range _ _
  have hx (w : W) : IsEquivariantMap t (pointAction P.torus.group) (x w) := by
    apply (fixedOver_iff_equivariant_section P.torus a (x w)).mp
    apply fixedOver_section_of_fields
    let S := Over.mk (fieldSpecMap k k)
    let r : S.left := IsLocalRing.closedPoint k
    have hm (v : W) : (toUnit S ≫ x v).left r ∈ Set.range (C v).orbitInclusion.left :=
      hsub v ⟨(toUnit S).left r, rfl⟩
    apply (hfix k (toUnit S ≫ x w)).mpr
    refine ⟨w, rfl, fun v hv ↦ ?_⟩
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hv ▸ hm v) (hm w)
  have hcharts (w : W) := weylChart P Q a ha J (hn w) U B' hB' hTB' hOpp Rpos hRpos
  choose charts htranslate hpuncture using hcharts
  have hcover (y : Q.scheme.left) : ∃ w : W, y ∈ Set.range (charts w).inclusion.left := by
    have hy : y ∈ ⋃ w : W, Set.range (C w).orbitInclusion.left := hc.symm ▸ Set.mem_univ y
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hy
    refine ⟨w, ?_⟩
    rw [htranslate]
    exact cell_range_subset_translate (C w) (hC w).1 hw
  have hν (w : W) (i : PositiveRoot P) : cotangentWeight J w i ≠ 1 := by
    intro h
    have he' : i.val.val⁻¹ = 1 := (J.labelEquiv w).val.injective
      (h.trans (map_one (J.labelEquiv w).val).symm)
    exact i.val.property.1 (inv_eq_one.mp he')
  obtain ⟨_, _, hgeometry⟩ :=
    LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P
  obtain ⟨hSmooth, hProper, _⟩ := hgeometry Q
  letI : Smooth Q.scheme.hom := hSmooth
  letI : IsProper Q.scheme.hom := hProper
  letI : Smooth P.torus.group.X.hom := splitTorusSmooth P.split
  letI : GeometricallyReduced P.torus.group.X.hom := geometricallyReduced_of_smooth _
  letI : IsReduced Q.scheme.left := isReduced_of_smooth_over_field Q.scheme.hom
  have hgeom : RestrictionGeometry t :=
    ⟨inferInstance, QuasiCompact.compactSpace_of_compactSpace Q.scheme.hom, inferInstance,
      invariantAffineCover_of_charts charts hcover⟩
  refine ⟨hfix, fun w ↦ ⟨charts w⟩, hgeom, ?_⟩
  obtain ⟨Z, V, hZ, hZiso⟩ := exists_fixedUnion t x hx fun v w hvw ↦
    Disjoint.mono (hsub v) (hsub w) (hdisj hvw)
  haveI : IsClosedImmersion Z.inclusion.left := Z.closedImmersion
  haveI : IsOpenImmersion V.inclusion.left := V.openImmersion
  haveI : IsReduced V.scheme.left := isReduced_of_isOpenImmersion V.inclusion.left
  have hV : RestrictionGeometry V.action :=
    restrictionGeometry_of_open V.inclusion hgeom
      (complementAffineCover_of_charts Z V P.split charts hν hx hZ hcover hpuncture)
  refine ⟨Z, V, hZiso, restrictionGeometry_of_closed Z.inclusion Z.equivariant hgeom, hV, ?_⟩
  have hRoots : Specs.BorelsAndChambers.subgroupRoots P.torus B' =
      Specs.BorelsAndChambers.subgroupRoots P.torus P.positive := by
    rw [hOpp, P.opposite, compl_compl]
  let S (w : W) := Specs.BorelsAndChambers.subgroupRoots P.torus P.negative ∩
    D.rootDatum.weylGroupToPerm w '' Specs.BorelsAndChambers.subgroupRoots P.torus P.positive
  have hparam (w : W) : Specs.BruhatOrbitParametrization.OrderedParametrization U (S w) (A w) := by
    simpa only [S, hRoots] using (hC w).2.1
  let coords (w : W) : OrderedCellCoordinates (C w) U (S w) :=
    Classical.choice (orderedCellCoordinates P.reductive P.split P.maximal Q a ha J (hn w)
      P.inNegative (C w) U (S w) (hparam w))
  refine ⟨U, A, C, coords, ?_⟩
  obtain ⟨e, hp⟩ := bruhatClosedPrefixes P.reductive P.split P.maximal P.negativeBorel
    P.inNegative Q a ha J n hn A C
  exact complementFiltration Z V hV e (fun w ↦ (C w).orbit) (fun w ↦ (coords w).action)
    (fun w ↦ (C w).orbitInclusion) (fun w ↦ cellOrigin (C w))
    (fun w ↦ (C w).orbitImmersion) (fun w ↦ (coords w).equivariant) hdisj hc hp
    (by simpa only [hcoset] using hZ) (fun w ↦ (coords w).polynomial) (fun w ↦ (coords w).puncture)

/-- The rational Weyl sections identify the fixed points on every
extension field and give their equivariant closed union. -/
theorem fixedPointLocus : FixedPointLocus.{u} := by
  intro k _ G P Q a ha
  obtain ⟨hT, D, J, hW, hRoots, hrep, hgeometry⟩ := flagLocalizationGeometry P Q a ha
  letI := hT
  refine ⟨hT, D, J, hW, hRoots, hrep, ?_⟩
  intro n hn x t
  obtain ⟨hfix, _, _, Z, V, hZ, _, _, _⟩ := hgeometry n hn
  exact ⟨hfix, Z, V, hZ⟩

end

end LinearAlgebraicGroups.Representation.FlagLocalizationGeometry
