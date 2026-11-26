import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.FixedPointSchemes
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.LinearAlgebra.TensorProduct.Basis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem isFixedBy_comp {H X T U : SchemeOver k}
    {a : H ⊗ X ⟶ X} {x : T ⟶ X} (hx : IsFixedBy a x) (f : U ⟶ T) :
    IsFixedBy a (f ≫ x) := by
  unfold IsFixedBy at hx ⊢
  rw [whiskerLeft_comp, Category.assoc, hx]
  simp

private theorem isAffine_product_left {H T : SchemeOver k}
    [IsAffine H.left] [IsAffine T.left] : IsAffine (H ⊗ T).left := by
  exact IsAffine.of_isPullback <|
    Over.isPullback_of_binaryFan_isLimit _
      (tensorProductIsBinaryProduct H T)

/-- The universal test algebra for a family is the coordinate algebra of the product
of the acting group and the affine test scheme. -/
theorem isFixedBy_iff_forall_points : Specs.IsFixedByIffForallPoints.{u} := by
  intro k _ H X hH a R x
  constructor
  · intro hx S f h
    dsimp [IsFixedBy] at hx
    have e := congrArg (fun z ↦ lift h ((testSpec k).map f.op) ≫ z) hx
    simpa [Category.assoc, ← comp_lift, lift_whiskerLeft] using e
  · intro hx
    have : IsAffine H.left := hH
    have : IsAffine ((testSpec k).obj (op R)).left := inferInstanceAs (IsAffine (Spec (.of R)))
    obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
      (isAffine_product_left (H := H) (T := (testSpec k).obj (op R)))
    let F := algSpec.fullyFaithful (R := CommRingCat.of k)
    let f := (F.preimage (e.hom ≫ snd H ((testSpec k).obj (op R)))).unop
    have hf : (testSpec k).map f.op = e.hom ≫ snd H ((testSpec k).obj (op R)) := F.map_preimage _
    have he := hx A.unop f (e.hom ≫ fst H ((testSpec k).obj (op R)))
    unfold IsFixedBy
    rw [← cancel_epi e.hom]
    have hl : lift (e.hom ≫ fst H ((testSpec k).obj (op R)))
        (mapPoints f x) = e.hom ≫ (H ◁ x) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [mapPoints, hf, Category.assoc]
    rw [hl] at he
    simpa only [mapPoints, hf, Category.assoc] using he

private abbrev affineSpec (A : TestAlgebra k) : SchemeOver k := (testSpec k).obj (op A)

private def quotientProjection {A : TestAlgebra k} (I : Ideal A) :
    A ⟶ CommAlgCat.of k (A ⧸ I) :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)

private theorem factorsThrough_affineQuotient {A B : TestAlgebra k}
    (I : Ideal A) (g : affineSpec B ⟶ affineSpec A) :
    (∃ z, z ≫ (testSpec k).map (quotientProjection I).op = g) ↔
      I ≤ RingHom.ker ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage g).unop.hom := by
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := (F.preimage g).unop
  have hg : (testSpec k).map f.op = g := F.map_preimage _
  change _ ↔ I ≤ RingHom.ker f.hom
  constructor
  · rintro ⟨z, hz⟩
    let h := (F.preimage z).unop
    have hh : (testSpec k).map h.op = z := F.map_preimage _
    have e : quotientProjection I ≫ h = f := by
      apply Quiver.Hom.op_inj
      apply F.map_injective
      simpa [hg, hh] using hz
    intro x hx
    rw [← e]
    change h.hom (Ideal.Quotient.mk I x) = 0
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  · intro h
    let z : CommAlgCat.of k (A ⧸ I) ⟶ B :=
      CommAlgCat.ofHom (Ideal.Quotient.liftₐ I f.hom fun x hx ↦ h hx)
    have e : quotientProjection I ≫ z = f := by
      ext x
      rfl
    refine ⟨(testSpec k).map z.op, ?_⟩
    rw [← Functor.map_comp, ← op_comp, e, hg]

private theorem closedImmersion_over_affineSpec {A : TestAlgebra k}
    {D : SchemeOver k} (j : D ⟶ affineSpec A) (hj : IsClosedImmersion j.left) :
    ∃ (I : Ideal A) (e : D ≅ affineSpec (CommAlgCat.of k (A ⧸ I))),
      j = e.hom ≫ (testSpec k).map (quotientProjection I).op := by
  change IsClosedImmersion (Y := Spec (.of A)) j.left at hj
  obtain ⟨(I : Ideal A), e, he⟩ := IsClosedImmersion.Spec_iff.mp hj
  let q := (testSpec k).map (quotientProjection I).op
  have hq : q.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := rfl
  change D.left ≅ Spec (.of (A ⧸ I)) at e
  change j.left = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) at he
  have he' : e.hom ≫ (affineSpec (CommAlgCat.of k (A ⧸ I))).hom = D.hom := by
    calc
      _ = (e.hom ≫ q.left) ≫ (affineSpec A).hom := by
        exact ((Category.assoc _ _ _).trans (congrArg (e.hom ≫ ·) (Over.w q))).symm
      _ = j.left ≫ (affineSpec A).hom :=
        congrArg (fun m ↦ m ≫ (affineSpec A).hom) ((congrArg (e.hom ≫ ·) hq).trans he.symm)
      _ = _ := Over.w j
  refine ⟨I, Over.isoMk e he', ?_⟩
  exact Over.OverMorphism.ext he

open Algebra.TensorProduct in
private theorem coefficient_naturality {A B C : TestAlgebra k} {ι : Type*} [DecidableEq ι]
    (basis : Module.Basis ι k A) (f : B →ₐ[k] C) (x : A ⊗[k] B) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft basis (map (AlgHom.id k A) f x) i =
      f (TensorProduct.equivFinsuppOfBasisLeft basis x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

private def coefficientIdeal {A B : TestAlgebra k} {ι : Type*} [DecidableEq ι]
    (basis : Module.Basis ι k A) (I : Ideal (A ⊗[k] B)) : Ideal B :=
  Ideal.span { b | ∃ x ∈ I, ∃ i, TensorProduct.equivFinsuppOfBasisLeft basis x i = b }

private theorem coefficientIdeal_le_ker {A B C : TestAlgebra k} {ι : Type*} [DecidableEq ι]
    (basis : Module.Basis ι k A) (I : Ideal (A ⊗[k] B)) (f : B →ₐ[k] C) :
    coefficientIdeal basis I ≤ RingHom.ker f ↔
      I ≤ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k A) f) := by
  rw [coefficientIdeal, Ideal.span_le]
  constructor
  · intro H x hx
    apply RingHom.mem_ker.mpr
    apply (TensorProduct.equivFinsuppOfBasisLeft basis).injective
    ext i
    rw [coefficient_naturality]
    simpa using RingHom.mem_ker.mp (H ⟨x, hx, i, rfl⟩)
  · rintro H b ⟨x, hx, i, rfl⟩
    apply RingHom.mem_ker.mpr
    rw [← coefficient_naturality, RingHom.mem_ker.mp (H hx)]
    simp


private theorem whiskerLeft_pullback {H T U : SchemeOver k} (f : U ⟶ T) :
    IsPullback (H ◁ f) (snd H U) (snd H T) f := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift (c.fst ≫ fst H T) c.snd) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using c.condition.symm
  · intro c
    simp
  · intro c g h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using congrArg (fun t ↦ t ≫ fst H T) h₁
    · simpa using h₂

private abbrev overCoverObj {T : SchemeOver k} (cover : T.left.OpenCover) (j : cover.I₀) :
    SchemeOver k :=
  Over.mk (cover.f j ≫ T.hom)

private abbrev overCoverMap {T : SchemeOver k} (cover : T.left.OpenCover) (j : cover.I₀) :
    overCoverObj cover j ⟶ T :=
  Over.homMk (cover.f j)

private theorem isFixedBy_iff_cover {H X T : SchemeOver k} (cover : T.left.OpenCover)
    (a : H ⊗ X ⟶ X) (x : T ⟶ X) :
    IsFixedBy a x ↔ ∀ j, IsFixedBy a (overCoverMap cover j ≫ x) := by
  refine ⟨fun hx j ↦ isFixedBy_comp hx (overCoverMap cover j), fun h ↦ ?_⟩
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (cover.pullback₁ (snd H T).left)
  intro j
  change cover.I₀ at j
  let pb : IsPullback (H ◁ overCoverMap cover j).left (snd H (overCoverObj cover j)).left
      (snd H T).left (cover.f j) := (whiskerLeft_pullback (H := H) (overCoverMap cover j)).map (Over.forget _)
  apply (cancel_epi pb.isoPullback.hom).mp
  change pb.isoPullback.hom ≫ pullback.fst (snd H T).left (cover.f j) ≫ _ =
    pb.isoPullback.hom ≫ pullback.fst (snd H T).left (cover.f j) ≫ _
  simp only [pb.isoPullback_hom_fst_assoc]
  have h' := h j
  unfold IsFixedBy at h'
  rw [whiskerLeft_comp, Category.assoc, ← whiskerLeft_snd_assoc] at h'
  exact congrArg (fun m ↦ m.left) h'

private theorem factorsThrough_iff_cover {X Z T : SchemeOver k} (cover : T.left.OpenCover)
    (i : Z ⟶ X) [Mono i.left] (x : T ⟶ X) :
    (∃ y, y ≫ i = x) ↔ ∀ j, ∃ y, y ≫ i = overCoverMap cover j ≫ x := by
  constructor
  · rintro ⟨y, rfl⟩ j
    exact ⟨overCoverMap cover j ≫ y, Category.assoc ..⟩
  · intro h
    choose y hy using h
    have hy' (j : cover.I₀) : (y j).left ≫ i.left = cover.f j ≫ x.left :=
      congrArg (fun m ↦ m.left) (hy j)
    let z : T.left ⟶ Z.left := cover.glueMorphisms (fun j ↦ (y j).left) (fun j l ↦ by
      rw [← cancel_mono i.left, Category.assoc, Category.assoc, hy', hy', pullback.condition_assoc])
    have hz : z ≫ i.left = x.left := by
      apply cover.hom_ext
      intro j
      rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hy']
    refine ⟨Over.homMk z ?_, Over.OverMorphism.ext hz⟩
    rw [← Over.w i, ← Category.assoc, hz, Over.w x]

private theorem affine_fixed_locus_of_affineSpec {A B : TestAlgebra k} {X : SchemeOver k}
    [IsSeparated X.hom] (a : affineSpec A ⊗ X ⟶ X) (j : affineSpec B ⟶ X) :
    ∃ (Z : SchemeOver k) (i : Z ⟶ affineSpec B), IsClosedImmersion i.left ∧
      ∀ (C : TestAlgebra k) (x : affineSpec C ⟶ affineSpec B),
        IsFixedBy a (x ≫ j) ↔ ∃ y : affineSpec C ⟶ Z, y ≫ i = x := by
  classical
  let F := testSpec k
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of k)
  let bc := asIso (Functor.OplaxMonoidal.δ F (op A) (op B))
  let f := (affineSpec A ◁ j) ≫ a
  let g := snd (affineSpec A) (affineSpec B) ≫ j
  let d := equalizer.ι f g
  have hd : IsClosedImmersion (d ≫ bc.inv).left :=
    IsClosedImmersion.comp d.left bc.inv.left
  obtain ⟨I, e, he⟩ := closedImmersion_over_affineSpec (d ≫ bc.inv) hd
  let basis := Module.Free.chooseBasis k A
  let J := coefficientIdeal basis I
  let q := F.map (quotientProjection J).op
  refine ⟨_, q, ?_, ?_⟩
  · change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  · intro C x
    let rc := asIso (Functor.OplaxMonoidal.δ F (op A) (op C))
    let h := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x
    have hh : F.map h = x := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
    have hc : rc.hom ≫ (affineSpec A ◁ x) = F.map (op A ◁ h) ≫ bc.hom := by
      change Functor.OplaxMonoidal.δ F (op A) (op C) ≫ _ = _ ≫
        Functor.OplaxMonoidal.δ F (op A) (op B)
      rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
        Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, ← hh]
      exact (prodComparison_natural_whiskerLeft F (A := op A) h).symm
    have he' : d = e.hom ≫ F.map (quotientProjection I).op ≫ bc.hom := by
      have eq := congrArg (fun m ↦ m ≫ bc.hom) he
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using eq
    have e₁ : IsFixedBy a (x ≫ j) ↔
        ∃ t : (affineSpec A ⊗ affineSpec C) ⟶ equalizer f g, t ≫ d = affineSpec A ◁ x := by
      have eq : IsFixedBy a (x ≫ j) ↔ (affineSpec A ◁ x) ≫ f = (affineSpec A ◁ x) ≫ g := by
        simp [IsFixedBy, f, g, whiskerLeft_comp, Category.assoc]
      rw [eq]
      exact ⟨fun H ↦ ⟨equalizer.lift _ H, equalizer.lift_ι _ _⟩, fun ⟨t, ht⟩ ↦ by
        rw [← ht, Category.assoc, Category.assoc, equalizer.condition]⟩
    rw [e₁, factorsThrough_affineQuotient]
    refine (Iff.trans ?_ (coefficientIdeal_le_ker basis I h.unop.hom).symm)
    have quotientCriterion := factorsThrough_affineQuotient I
      ((testSpec k).map (op A ◁ h))
    rw [Functor.FullyFaithful.preimage_map] at quotientCriterion
    refine Iff.trans ?_ quotientCriterion
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨rc.hom ≫ z ≫ e.hom, (cancel_mono bc.hom).mp ?_⟩
      calc
        _ = rc.hom ≫ z ≫ d := by simp only [Category.assoc, he', F]
        _ = _ := by rw [hz, hc]
    · rintro ⟨z, hz⟩
      refine ⟨rc.inv ≫ z ≫ e.inv, ?_⟩
      rw [he']
      calc
        _ = rc.inv ≫ (z ≫ (testSpec k).map (quotientProjection I).op) ≫ bc.hom := by simp [F]
        _ = _ := by rw [hz, ← hc, Iso.inv_hom_id_assoc]


private theorem isFixedBy_groupIso {H H' X T : SchemeOver k} (e : H' ≅ H)
    (a : H ⊗ X ⟶ X) (x : T ⟶ X) :
    IsFixedBy ((e.hom ▷ X) ≫ a) x ↔ IsFixedBy a x := by
  unfold IsFixedBy
  rw [whisker_exchange_assoc]
  change (whiskerRightIso e T).hom ≫ ((H ◁ x) ≫ a) = snd H' T ≫ x ↔ _
  rw [← (cancel_epi (whiskerRightIso e T).hom)]
  simp

private theorem isFixedBy_comp_iso {H X T U : SchemeOver k}
    (a : H ⊗ X ⟶ X) (e : U ≅ T) (x : T ⟶ X) :
    IsFixedBy a (e.hom ≫ x) ↔ IsFixedBy a x :=
  ⟨fun h ↦ by simpa using isFixedBy_comp h e.inv, fun h ↦ isFixedBy_comp h e.hom⟩

private theorem affine_fixed_locus {H X U : SchemeOver k} [IsAffine H.left] [IsAffine U.left]
    [IsSeparated X.hom] (a : H ⊗ X ⟶ X) (j : U ⟶ X) :
    ∃ (Z : SchemeOver k) (i : Z ⟶ U), IsClosedImmersion i.left ∧
      ∀ (T : SchemeOver k) (x : T ⟶ U),
        IsFixedBy a (x ≫ j) ↔ ∃ y : T ⟶ Z, y ≫ i = x := by
  obtain ⟨A, ⟨eH⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine H.left)
  obtain ⟨B, ⟨eU⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine U.left)
  obtain ⟨Z, i, hi, H₀⟩ :=
    affine_fixed_locus_of_affineSpec (A := A.unop) (B := B.unop)
      ((eH.hom ▷ X) ≫ a) (eU.hom ≫ j)
  let i' := i ≫ eU.hom
  have hi' : IsClosedImmersion i'.left := IsClosedImmersion.comp i.left eU.hom.left
  refine ⟨Z, i', hi', fun T x ↦ ?_⟩
  have : Mono i'.left := inferInstance
  let cover := T.left.affineOpenCover
  rw [isFixedBy_iff_cover cover.openCover, factorsThrough_iff_cover cover.openCover]
  apply forall_congr'
  intro l
  let V := overCoverObj cover.openCover l
  let u := overCoverMap cover.openCover l ≫ x
  have hV : IsAffine V.left := inferInstanceAs (IsAffine (Spec (cover.X l)))
  obtain ⟨C, ⟨eV⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hV
  have eq := H₀ C.unop (eV.hom ≫ u ≫ eU.inv)
  rw [isFixedBy_groupIso] at eq
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at eq

  change IsFixedBy a (u ≫ j) ↔ ∃ y, y ≫ i' = u
  rw [← isFixedBy_comp_iso a eV (u ≫ j), eq]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨eV.inv ≫ v, ?_⟩
    change (eV.inv ≫ v) ≫ (i ≫ eU.hom) = u
    rw [Category.assoc, ← Category.assoc v, hv]
    simp
  · rintro ⟨v, hv⟩
    refine ⟨eV.hom ≫ v, ?_⟩
    have hv' : v ≫ i = u ≫ eU.inv := by
      simpa [i', Category.assoc] using congrArg (fun m ↦ m ≫ eU.inv) hv
    simp [hv']


private structure LocalFixedLocus {H X U : SchemeOver k} (a : H ⊗ X ⟶ X) (j : U ⟶ X) where
  source : SchemeOver k
  ι : source ⟶ U
  closed : IsClosedImmersion ι.left
  represents : ∀ (T : SchemeOver k) (x : T ⟶ U),
    IsFixedBy a (x ≫ j) ↔ ∃ y : T ⟶ source, y ≫ ι = x

namespace LocalFixedLocus

variable {H X U V : SchemeOver k} {a : H ⊗ X ⟶ X} {j : U ⟶ X} {l : V ⟶ X}
    (D : LocalFixedLocus a j) (E : LocalFixedLocus a l)

private instance : Mono D.ι.left := by
  have := D.closed
  infer_instance

private instance : Mono D.ι := Over.mono_of_mono_left _

private theorem fixed : IsFixedBy a (D.ι ≫ j) :=
  (D.represents _ _).mpr ⟨𝟙 _, Category.id_comp _⟩

private def lift {T : SchemeOver k} {x : T ⟶ U} (hx : IsFixedBy a (x ≫ j)) : T ⟶ D.source :=
  ((D.represents T x).mp hx).choose

@[reassoc (attr := simp)]
private theorem lift_ι {T : SchemeOver k} {x : T ⟶ U} (hx : IsFixedBy a (x ≫ j)) :
    D.lift hx ≫ D.ι = x := ((D.represents T x).mp hx).choose_spec

private def transition (w : U ⟶ V) (hw : w ≫ l = j) : D.source ⟶ E.source :=
  E.lift (by simpa only [Category.assoc, hw] using D.fixed :
    IsFixedBy a ((D.ι ≫ w) ≫ l))

@[reassoc (attr := simp)]
private theorem transition_ι (w : U ⟶ V) (hw : w ≫ l = j) :
    D.transition E w hw ≫ E.ι = D.ι ≫ w := E.lift_ι _

private theorem transition_isPullback (w : U ⟶ V) (hw : w ≫ l = j) :
    IsPullback D.ι (D.transition E w hw) w E.ι := by
  let factor (c : PullbackCone w E.ι) : c.pt ⟶ D.source :=
    D.lift (x := c.fst) (by
      rw [← hw, ← Category.assoc, c.condition, Category.assoc]
      exact isFixedBy_comp E.fixed c.snd)
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ factor ?_ ?_ ?_⟩⟩
  · intro c
    exact D.lift_ι _
  · intro c
    apply (cancel_mono E.ι).mp
    rw [Category.assoc, transition_ι]
    exact (D.lift_ι_assoc _ _).trans c.condition
  · intro c m hm _
    exact (cancel_mono D.ι).mp (hm.trans (D.lift_ι _).symm)

end LocalFixedLocus

private theorem fixed_locus {H X : SchemeOver k} [IsAffine H.left] [IsSeparated X.hom]
    (a : H ⊗ X ⟶ X) :
    ∃ (Z : SchemeOver k) (i : Z ⟶ X), IsClosedImmersion i.left ∧ RepresentsFixedPoints a i := by
  classical
  let 𝒰 := X.left.directedAffineCover
  let D (j : 𝒰.I₀) : LocalFixedLocus a (overCoverMap 𝒰 j) := by
    have : IsAffine (overCoverObj 𝒰 j).left := j.2
    exact Classical.choice (show Nonempty (LocalFixedLocus a (overCoverMap 𝒰 j)) from by
      obtain ⟨Z, i, hi, h⟩ := affine_fixed_locus a (overCoverMap 𝒰 j)
      exact ⟨⟨Z, i, hi, h⟩⟩)
  let w {j l : 𝒰.I₀} (g : j ⟶ l) : overCoverObj 𝒰 j ⟶ overCoverObj 𝒰 l :=
    Over.homMk (𝒰.trans g) ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ X.hom) (𝒰.trans_map g)))
  have hw {j l : 𝒰.I₀} (g : j ⟶ l) : w g ≫ overCoverMap 𝒰 l = overCoverMap 𝒰 j :=
    Over.OverMorphism.ext (𝒰.trans_map g)
  let t {j l : 𝒰.I₀} (g : j ⟶ l) := (D j).transition (D l) (w g) (hw g)
  have ht {j l : 𝒰.I₀} (g : j ⟶ l) : (t g).left ≫ (D l).ι.left =
      (D j).ι.left ≫ 𝒰.trans g :=
    congrArg (fun m ↦ m.left) ((D j).transition_ι (D l) (w g) (hw g))
  let d : Scheme.Cover.RelativeGluingData 𝒰 :=
    { functor :=
        { obj j := (D j).source.left
          map g := (t g).left
          map_id j := by
            apply (cancel_mono (D j).ι.left).mp
            rw [ht, 𝒰.trans_id]
            simp
          map_comp g g' := by
            apply (cancel_mono (D _).ι.left).mp
            rw [ht, Category.assoc, ht, ← Category.assoc, ht, 𝒰.trans_comp, Category.assoc] }
      natTrans :=
        { app j := (D j).ι.left
          naturality _ _ g := ht g }
      equifibered _ _ g :=
        ((D _).transition_isPullback (D _) (w g) (hw g) |>.map (Over.forget _)).flip }
  let : ∀ {j l : 𝒰.I₀} (g : j ⟶ l), IsOpenImmersion (d.functor.map g) :=
    fun g ↦ MorphismProperty.of_isPullback (d.equifibered g).flip
      (show IsOpenImmersion (𝒰.trans g) from inferInstance)
  let : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.isLocallyDirected_of_equifibered_of_injective d.natTrans d.equifibered
      (fun g ↦ (d.functor.map g).injective)
  let Z := Over.mk (d.toBase ≫ X.hom)
  let i : Z ⟶ X := Over.homMk d.toBase
  have hclosed : IsClosedImmersion i.left := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒰
    intro j
    have closed := (D j).closed
    let pb := d.isPullback_natTrans_ι_toBase j
    change IsClosedImmersion (pullback.snd d.toBase (𝒰.f j))
    rw [← pb.flip.isoPullback_inv_snd]
    exact IsClosedImmersion.comp pb.flip.isoPullback.inv ((D j).ι.left)
  let localMap (j : 𝒰.I₀) : (D j).source ⟶ Z :=
    Over.homMk (colimit.ι d.functor j) (by
      change colimit.ι d.functor j ≫ (d.toBase ≫ X.hom) = (D j).source.hom
      rw [← Category.assoc, d.ι_toBase]
      change ((D j).ι.left ≫ 𝒰.f j) ≫ X.hom = (D j).source.hom
      rw [Category.assoc]
      exact Over.w (D j).ι)
  have localMap_ι (j : 𝒰.I₀) : localMap j ≫ i = (D j).ι ≫ overCoverMap 𝒰 j :=
    Over.OverMorphism.ext (d.ι_toBase j)
  refine ⟨Z, i, hclosed, fun T x ↦ ?_⟩
  constructor
  · intro h
    have : Mono i.left := inferInstance
    let cover : T.left.OpenCover := 𝒰.pullback₁ x.left
    apply (factorsThrough_iff_cover cover i x).mpr
    intro j
    change 𝒰.I₀ at j
    let xj : overCoverObj cover j ⟶ overCoverObj 𝒰 j :=
      Over.homMk (𝒰.pullbackHom x.left j) (by
        change 𝒰.pullbackHom x.left j ≫ (𝒰.f j ≫ X.hom) = cover.f j ≫ T.hom
        exact (Scheme.Cover.pullbackHom_map_assoc 𝒰 x.left j X.hom).trans
          (congrArg (cover.f j ≫ ·) (Over.w x)))
    have hxj : xj ≫ overCoverMap 𝒰 j = overCoverMap cover j ≫ x :=
      Over.OverMorphism.ext (Scheme.Cover.pullbackHom_map 𝒰 x.left j)
    have fj : IsFixedBy a (xj ≫ overCoverMap 𝒰 j) := by
      rw [hxj]
      exact isFixedBy_comp h (overCoverMap cover j)
    exact ⟨(D j).lift fj ≫ localMap j, by
      rw [Category.assoc, localMap_ι, LocalFixedLocus.lift_ι_assoc, hxj]⟩
  · rintro ⟨y, rfl⟩
    apply isFixedBy_comp (x := i) ?_ y
    apply (isFixedBy_iff_cover d.cover a i).mpr
    intro j
    change 𝒰.I₀ at j
    have he : (colimit.ι d.functor j) ≫ Z.hom = (D j).source.hom :=
      Over.w (localMap j)
    let v : overCoverObj (T := Z) d.cover j ⟶ (D j).source :=
      Over.homMk (𝟙 ((D j).source.left)) (by
        change 𝟙 _ ≫ (D j).source.hom = colimit.ι d.functor j ≫ Z.hom
        rw [Category.id_comp, he])
    have e : overCoverMap (T := Z) d.cover j ≫ i =
        v ≫ (D j).ι ≫ overCoverMap 𝒰 j := by
      apply Over.OverMorphism.ext
      change colimit.ι d.functor j ≫ d.toBase = 𝟙 _ ≫ (D j).ι.left ≫ 𝒰.f j
      simpa only [Category.id_comp] using d.ι_toBase j
    rw [e]
    exact isFixedBy_comp (D j).fixed v

/-- The fixed-point functor of an affine algebraic group is a closed subscheme. -/
theorem fixedPointScheme : Specs.FixedPointScheme.{u} := by
  intro k _ H X act hX _ _
  have : IsAffine H.1.X.left := H.2.1
  have : IsSeparated X.hom := hX
  exact fixed_locus act.smul


private theorem over_product_isPullback {S : Scheme.{u}} (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
  Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct X Y)

private theorem over_pullback_counit {S S' : Scheme.{u}} (f : S' ⟶ S) (H : Over S) :
    IsPullback ((Over.mapPullbackAdj f).counit.app H).left
      ((Over.pullback f).obj H).hom H.hom f :=
  IsPullback.of_hasPullback H.hom f

/-- Pulling the first factor to the new base and then forming the product there gives
the same scheme as forming the product over the original base. -/
private theorem isIso_over_product_map {S S' : Scheme.{u}} (f : S' ⟶ S)
    (H : Over S) (T : Over S') :
    IsIso (lift
      ((Over.map f).map (fst ((Over.pullback f).obj H) T) ≫
        (Over.mapPullbackAdj f).counit.app H)
      ((Over.map f).map (snd ((Over.pullback f).obj H) T))) := by
  let L := Over.map f
  let F := Over.pullback f
  let e := (Over.mapPullbackAdj f).counit.app H
  let p := (over_product_isPullback (F.obj H) T).paste_horiz (over_pullback_counit f H)
  let q := over_product_isPullback H (L.obj T)
  let b := p.isoPullback ≪≫ q.isoPullback.symm
  have hfst : b.hom ≫ (fst H (L.obj T)).left = (fst (F.obj H) T).left ≫ e.left := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc, q.isoPullback_inv_fst]
    exact p.isoPullback_hom_fst
  have hsnd : b.hom ≫ (snd H (L.obj T)).left = (snd (F.obj H) T).left := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc, q.isoPullback_inv_snd]
    exact p.isoPullback_hom_snd
  let e' : L.obj (F.obj H ⊗ T) ≅ H ⊗ L.obj T := Over.isoMk b (by
    rw [← Over.w (snd H (L.obj T)), ← Category.assoc, hsnd]
    exact Over.w (L.map (snd (F.obj H) T)))
  have h : e'.hom = lift (L.map (fst (F.obj H) T) ≫ e) (L.map (snd (F.obj H) T)) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact Over.OverMorphism.ext hfst
    · exact (Over.OverMorphism.ext hsnd).trans (lift_snd _ _).symm
  change IsIso (lift (L.map (fst (F.obj H) T) ≫ e) (L.map (snd (F.obj H) T)))
  rw [← h]
  infer_instance

private theorem isFixedBy_baseChange_iff {H X : SchemeOver k}
    (K : Type u) [Field K] [Algebra k K] (a : H ⊗ X ⟶ X)
    (T : SchemeOver K) (x : T ⟶ (baseChange k K).obj X) :
    IsFixedBy (baseChangeAction K a) x ↔
      IsFixedBy a ((Over.mapPullbackAdj (fieldSpecMap k K)).homEquiv T X |>.symm x) := by
  let f := fieldSpecMap k K
  let L := Over.map f
  let F := baseChange k K
  let adj := Over.mapPullbackAdj f
  let H' := F.obj H
  let P := H' ⊗ T
  let c := prodComparisonIso (baseChange k K) H X
  let e : L.obj P ⟶ H ⊗ L.obj T :=
    lift (L.map (fst H' T) ≫ adj.counit.app H) (L.map (snd H' T))
  have : IsIso e := isIso_over_product_map f H T
  let y := (adj.homEquiv T X).symm x
  let w : P ⟶ F.obj (H ⊗ X) := (H' ◁ x) ≫ c.inv
  have hfst : w ≫ F.map (fst H X) = fst H' T := by
    have eq : c.inv ≫ F.map (fst H X) = fst H' (F.obj X) := by
      apply (cancel_epi c.hom).mp
      rw [Iso.hom_inv_id_assoc]
      exact (CartesianMonoidalCategory.prodComparison_fst (baseChange k K) H X).symm
    rw [Category.assoc, eq, whiskerLeft_fst]
  have hsnd : w ≫ F.map (snd H X) = snd H' T ≫ x := by
    have eq : c.inv ≫ F.map (snd H X) = snd H' (F.obj X) := by
      apply (cancel_epi c.hom).mp
      rw [Iso.hom_inv_id_assoc]
      exact (CartesianMonoidalCategory.prodComparison_snd (baseChange k K) H X).symm
    rw [Category.assoc, eq, whiskerLeft_snd]
  have hy : (adj.homEquiv P X).symm (snd H' T ≫ x) = L.map (snd H' T) ≫ y :=
    adj.homEquiv_naturality_left_symm _ _
  have hw : (adj.homEquiv P (H ⊗ X)).symm w = e ≫ (H ◁ y) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, ← adj.homEquiv_naturality_right_symm, hfst,
        adj.homEquiv_counit]
      exact (lift_fst _ _).symm
    · rw [Category.assoc, whiskerLeft_snd, ← adj.homEquiv_naturality_right_symm, hsnd, hy]
      exact (lift_snd_assoc _ _ _).symm
  change w ≫ F.map a = snd H' T ≫ x ↔ ((H ◁ y) ≫ a = snd H (L.obj T) ≫ y)
  rw [← (adj.homEquiv P X).symm.injective.eq_iff, adj.homEquiv_naturality_right_symm, hw, hy,
    Category.assoc]
  have he : e ≫ snd H (L.obj T) = L.map (snd H' T) := lift_snd _ _
  rw [← he, Category.assoc, cancel_epi]

/-- The scalar extension of a closed fixed-point subscheme represents the
fixed-point functor for the scalar-extended action. -/
theorem fixedPointSchemeBaseChange : Specs.FixedPointSchemeBaseChange.{u} := by
  intro k K _ _ _ H X Z a i hclosed hi
  let f := fieldSpecMap k K
  let F := baseChange k K
  let adj := Over.mapPullbackAdj f
  have pb : IsPullback (F.map i).left (pullback.fst Z.hom f) (pullback.fst X.hom f) i.left := by
    have he : (F.map i).left ≫ pullback.fst X.hom f = pullback.fst Z.hom f ≫ i.left :=
      pullback.lift_fst _ _ _
    have he' : (F.map i).left ≫ pullback.snd X.hom f = pullback.snd Z.hom f :=
      pullback.lift_snd _ _ _
    have outer : IsPullback ((F.map i).left ≫ pullback.snd X.hom f)
        (pullback.fst Z.hom f) f (i.left ≫ X.hom) := by
      rw [he', Over.w i]
      exact (IsPullback.of_hasPullback Z.hom f).flip
    exact outer.of_right he (IsPullback.of_hasPullback X.hom f).flip
  refine ⟨MorphismProperty.of_isPullback pb.flip hclosed, fun T x ↦ ?_⟩
  rw [isFixedBy_baseChange_iff K a T x, hi]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨adj.homEquiv T Z y, (adj.homEquiv T X).symm.injective ?_⟩
    rw [adj.homEquiv_naturality_right_symm, Equiv.symm_apply_apply, hy]
  · rintro ⟨y, hy⟩
    exact ⟨(adj.homEquiv T Z).symm y,
      (adj.homEquiv_naturality_right_symm y i).symm.trans
        (congrArg (adj.homEquiv T X).symm hy)⟩

end
end LinearAlgebraicGroups
