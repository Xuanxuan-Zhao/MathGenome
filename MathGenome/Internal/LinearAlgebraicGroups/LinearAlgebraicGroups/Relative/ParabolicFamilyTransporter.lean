import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

open LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup AffineAlgebraicGroup SubgroupSections)
open Specs.ParabolicFamilyTransporter

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] {G : GroupScheme k} {T U : SchemeOver k}

open private familyFactorizationLocus
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

@[reassoc (attr := simp)]
theorem Family.ambient_snd (Q : Family G T) :
    Q.ambient ≫ snd _ _ = Q.base := by
  simp [Specs.ParabolicFamilyTransporter.Family.ambient]

private theorem familyAmbient_left (Q : Family G T) :
    Q.ambient.left = Q.inclusion.hom.hom.left := by
  apply pullback.hom_ext
  · exact congrArg (fun f : Q.overField ⟶ G.X ↦ f.left)
      (lift_fst (f := Over.homMk _ _) (g := Q.base))
  · exact (congrArg (fun f : Q.overField ⟶ T ↦ f.left)
      (lift_snd (f := Over.homMk _ _) (g := Q.base))).trans (Over.w Q.inclusion.hom.hom).symm

theorem familyAmbient_closed (Q : Family G T) : IsClosedImmersion Q.ambient.left := by
  rw [familyAmbient_left]
  exact Q.closed

private def universalConjugate (P : ClosedSubgroup G) (T : SchemeOver k) :
    P.group.X ⊗ (G.X ⊗ T) ⟶ G.X ⊗ T :=
  lift (conjugateFamily P.inclusion (fst G.X T)) (snd _ _ ≫ snd _ _)

private theorem universalConjugate_comp (P : ClosedSubgroup G) (a : U ⟶ T) (g : U ⟶ G.X) :
    (P.group.X ◁ lift g a) ≫ universalConjugate P T =
      conjugateInclusion P g ≫ (G.X ◁ a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [universalConjugate, conjugateInclusion, conjugateFamily, MonObj.comp_mul,
      GrpObj.comp_inv]
  · simp [universalConjugate, conjugateInclusion]

theorem conjugateContained_of_conjugates {P : ClosedSubgroup G} {Q : Family G T}
    {a : U ⟶ T} {g : U ⟶ G.X} (h : Conjugates P Q a g) :
    ConjugateContained P Q a g := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.hom ≫ pullback.fst _ _, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, he]

open private coefficientIdeal coefficientIdeal_le_ker coefficient_naturality
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes

private theorem coefficientIdeal_fg {A B : TestAlgebra k} {I : Ideal (A ⊗[k] B)}
    {Iota : Type u} [DecidableEq Iota] (basis : Module.Basis Iota k A) (hI : I.FG) :
    (coefficientIdeal basis I).FG := by
  classical
  obtain ⟨s, hs⟩ := hI
  let coeff (x : A ⊗[k] B) := TensorProduct.equivFinsuppOfBasisLeft basis x
  let c := s.biUnion fun x ↦ (coeff x).support.image (coeff x)
  refine ⟨c, le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    intro b hb
    obtain ⟨x, hx, i, _, rfl⟩ : ∃ x ∈ s, ∃ i ∈ (coeff x).support, coeff x i = b := by
      obtain ⟨x, hx, hb⟩ := Finset.mem_biUnion.mp hb
      obtain ⟨i, hi, hbi⟩ := Finset.mem_image.mp hb
      exact ⟨x, hx, i, hi, hbi⟩
    exact Ideal.subset_span ⟨x, hs ▸ Ideal.subset_span hx, i, rfl⟩
  · let J : Ideal B := Ideal.span (c : Set B)
    let q : B →ₐ[k] CommAlgCat.of k (B ⧸ J) := Ideal.Quotient.mkₐ k J
    have heq : RingHom.ker q = J := Ideal.mk_ker
    change coefficientIdeal basis I ≤ J
    rw [← heq, coefficientIdeal_le_ker basis I q, ← hs, Ideal.span_le]
    intro x hx
    apply RingHom.mem_ker.mpr
    apply (TensorProduct.equivFinsuppOfBasisLeft basis).injective
    ext i
    rw [coefficient_naturality]
    by_cases hi : i ∈ (coeff x).support
    · have hm : coeff x i ∈ J :=
        Ideal.subset_span (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
      exact (show q (coeff x i) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hm).trans (by simp)
    · have hzero : coeff x i = 0 := Finsupp.notMem_support_iff.mp hi
      simp [coeff] at hzero
      simp [hzero]

private theorem finitePresentation_of_closed_over {X Y S : Scheme.{u}}
    [IsAffine Y] [IsAffine S] (f : X ⟶ Y) (g : Y ⟶ S)
    [IsClosedImmersion f] [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFinitePresentation g] : LocallyOfFinitePresentation f := by
  have hX := (IsClosedImmersion.isAffine_surjective_of_isAffine f).1
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  have h₁ := g.finitePresentation_appTop
  have h₂ := (f ≫ g).finitePresentation_appTop
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h₂
  apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation) (f := f)).mpr
  apply RingHom.FinitePresentation.of_surjective _ hsurj
  algebraize [g.appTop.hom, f.appTop.hom.comp g.appTop.hom]
  exact Algebra.FinitePresentation.ker_fG_of_surjective
    ({ f.appTop.hom with commutes' := fun _ ↦ rfl } : _ →ₐ[↑(S.presheaf.obj (op ⊤))] _) hsurj


open private affineSpec quotientProjection factorsThrough_affineQuotient
  closedImmersion_over_affineSpec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes

private theorem affineLocus_finite {A B : TestAlgebra k} {D Z : SchemeOver k}
    (d : D ⟶ affineSpec A ⊗ affineSpec B) (hd : IsClosedImmersion d.left)
    (hdf : LocallyOfFinitePresentation d.left)
    (j : Z ⟶ affineSpec B) (hj : IsClosedImmersion j.left)
    (h : ∀ (T : SchemeOver k) (x : T ⟶ affineSpec B),
      (∃ t : affineSpec A ⊗ T ⟶ D, t ≫ d = affineSpec A ◁ x) ↔ ∃ y : T ⟶ Z, y ≫ j = x) :
    LocallyOfFinitePresentation j.left := by
  classical
  let F := testSpec k
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of k)
  let b := asIso (Functor.OplaxMonoidal.δ F (op A) (op B))
  have hb : IsClosedImmersion (d ≫ b.inv).left := IsClosedImmersion.comp d.left b.inv.left
  obtain ⟨I, e, he⟩ := closedImmersion_over_affineSpec (d ≫ b.inv) hb
  let qI := F.map (quotientProjection I).op
  have qI_fp : LocallyOfFinitePresentation qI.left := by
    have hd' : LocallyOfFinitePresentation (d ≫ b.inv).left :=
      inferInstanceAs (LocallyOfFinitePresentation (d.left ≫ b.inv.left))
    have he' : (d ≫ b.inv).left = e.hom.left ≫ qI.left := congrArg (·.left) he
    rw [he', MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)] at hd'
    exact hd'
  have hI : I.FG := by
    have qI_fp' : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      qI_fp
    have hfp := (LocallyOfFinitePresentation.SpecMap_iff _).mp qI_fp'
    change (Ideal.Quotient.mk I).FinitePresentation at hfp
    let C := A ⊗[k] B
    let : Algebra.FinitePresentation C (C ⧸ I) :=
      RingHom.finitePresentation_algebraMap.mp hfp
    have H := Algebra.FinitePresentation.ker_fG_of_surjective
      (Ideal.Quotient.mkₐ C I) Ideal.Quotient.mk_surjective
    simpa only [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using H
  let basis := Module.Free.chooseBasis k A
  let J := coefficientIdeal basis I
  let q := F.map (quotientProjection J).op
  have hqf : LocallyOfFinitePresentation q.left := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    exact RingHom.FinitePresentation.of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact coefficientIdeal_fg basis hI)
  have hc (C : TestAlgebra k) (x : affineSpec C ⟶ affineSpec B) :
      (∃ t : affineSpec A ⊗ affineSpec C ⟶ D, t ≫ d = affineSpec A ◁ x) ↔
        ∃ y, y ≫ q = x := by
    let c := asIso (Functor.OplaxMonoidal.δ F (op A) (op C))
    let f := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x
    have hf : F.map f = x := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
    have en : c.hom ≫ (affineSpec A ◁ x) ≫ b.inv = F.map (op A ◁ f) := by
      apply (cancel_mono b.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change Functor.OplaxMonoidal.δ F (op A) (op C) ≫ _ =
        _ ≫ Functor.OplaxMonoidal.δ F (op A) (op B)
      rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
        Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, ← hf]
      exact (prodComparison_natural_whiskerLeft F (A := op A) f).symm
    have hh : (∃ t : affineSpec A ⊗ affineSpec C ⟶ D, t ≫ d = affineSpec A ◁ x) ↔
        ∃ z, z ≫ qI = F.map (op A ◁ f) := by
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨c.hom ≫ t ≫ e.hom, ?_⟩
        have he' : e.hom ≫ qI = d ≫ b.inv := he.symm
        simp only [Category.assoc, he', reassoc_of% ht, en]
      · rintro ⟨z, hz⟩
        refine ⟨c.inv ≫ z ≫ e.inv, (cancel_mono b.inv).mp ?_⟩
        have he' : d ≫ b.inv = e.hom ≫ qI := he
        simp only [Category.assoc, he', e.inv_hom_id_assoc, hz, ← en,
          c.inv_hom_id_assoc]
    rw [hh, factorsThrough_affineQuotient, factorsThrough_affineQuotient,
      Functor.FullyFaithful.preimage_map]
    exact (coefficientIdeal_le_ker basis I f.unop.hom).symm
  have : IsAffine (affineSpec B).left := inferInstanceAs (IsAffine (Spec (.of B)))
  have hZa : IsAffine Z.left := isAffine_of_isAffineHom j.left
  obtain ⟨C, ⟨eZ⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hZa
  obtain ⟨i, hi⟩ := (hc C.unop (eZ.hom ≫ j)).mp
    ((h (affineSpec C.unop) (eZ.hom ≫ j)).mpr ⟨eZ.hom, rfl⟩)
  obtain ⟨r, hr⟩ := (h _ q).mp ((hc _ q).mpr ⟨𝟙 _, Category.id_comp q⟩)
  have h₁ : eZ.inv ≫ i ≫ q = j := by rw [hi, eZ.inv_hom_id_assoc]
  have mj : Mono j := (Over.forget _).mono_of_mono_map (f := j)
    (inferInstanceAs (Mono j.left))
  have mq : Mono q := by
    have : IsClosedImmersion q.left := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact (Over.forget _).mono_of_mono_map (f := q) (inferInstanceAs (Mono q.left))
  let e' : Z ≅ _ := ⟨eZ.inv ≫ i, r,
    (cancel_mono j).mp (by rw [Category.assoc, hr, Category.assoc, h₁, Category.id_comp]),
    (cancel_mono q).mp (by rw [Category.assoc, Category.assoc eZ.inv i q, h₁, hr, Category.id_comp])⟩
  have eq : j.left = e'.hom.left ≫ q.left := congrArg (·.left) h₁.symm
  have : IsIso e'.hom.left := ((Over.forget _).mapIso e').isIso_hom
  rw [eq]
  infer_instance


private theorem familyLocus_finite {A B D Z : SchemeOver k} [IsAffine A.left] [IsAffine B.left]
    (d : D ⟶ A ⊗ B) (hd : IsClosedImmersion d.left) (hdf : LocallyOfFinitePresentation d.left)
    (j : Z ⟶ B) (hj : IsClosedImmersion j.left)
    (h : ∀ (T : SchemeOver k) (x : T ⟶ B),
      (∃ t : A ⊗ T ⟶ D, t ≫ d = A ◁ x) ↔ ∃ y : T ⟶ Z, y ≫ j = x) :
    LocallyOfFinitePresentation j.left := by
  obtain ⟨X, ⟨eA⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine A.left)
  obtain ⟨Y, ⟨eB⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (inferInstance : IsAffine B.left)
  let s := eA ⊗ᵢ eB
  have hsi : IsIso s.inv.left := inferInstanceAs (IsIso ((Over.forget _).map s.inv))
  have hbi : IsIso eB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map eB.inv))
  have hjf : LocallyOfFinitePresentation (j ≫ eB.inv).left :=
    affineLocus_finite (A := X.unop) (B := Y.unop) (d ≫ s.inv)
      (IsClosedImmersion.comp d.left s.inv.left)
      (inferInstanceAs (LocallyOfFinitePresentation (d.left ≫ s.inv.left)))
      (j ≫ eB.inv) (IsClosedImmersion.comp j.left eB.inv.left) (fun T x ↦ by
        let a := eA ⊗ᵢ Iso.refl T
        have eq : a.hom ≫ (A ◁ (x ≫ eB.hom)) ≫ s.inv = affineSpec X.unop ◁ x := by
          apply CartesianMonoidalCategory.hom_ext <;> simp [a, s, tensorIso]
        have h₁ : (∃ t : affineSpec X.unop ⊗ T ⟶ D,
            t ≫ (d ≫ s.inv) = affineSpec X.unop ◁ x) ↔
            ∃ t : A ⊗ T ⟶ D, t ≫ d = A ◁ (x ≫ eB.hom) := by
          constructor
          · rintro ⟨t, ht⟩
            refine ⟨a.inv ≫ t, (cancel_mono s.inv).mp ?_⟩
            simp only [Category.assoc, ht, ← eq, Iso.inv_hom_id_assoc]
          · rintro ⟨t, ht⟩
            exact ⟨a.hom ≫ t, by simp only [Category.assoc, reassoc_of% ht, eq]⟩
        rw [h₁, h]
        constructor
        · rintro ⟨z, hz⟩
          refine ⟨z, ?_⟩
          rw [← Category.assoc, hz, Category.assoc, eB.hom_inv_id, Category.comp_id]
        · rintro ⟨z, hz⟩
          refine ⟨z, (cancel_mono eB.inv).mp ?_⟩
          simpa [Category.assoc] using hz)
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @LocallyOfFinitePresentation)
    j.left eB.inv.left).mp hjf

/-- Coefficient equations for containment in a smooth closed subgroup family. -/
theorem containmentLocus (A : AffineAlgebraicGroup k) (P : ClosedSubgroup A.val)
    (R : TestAlgebra k) (Q : Family A.val ((testSpec k).obj (op R))) :
    ∃ (Z : SchemeOver k) (j : Z ⟶ A.val.X ⊗ (testSpec k).obj (op R)),
      IsClosedImmersion j.left ∧ LocallyOfFinitePresentation (j ≫ snd _ _).left ∧
        QuasiCompact (j ≫ snd _ _).left ∧ QuasiSeparated (j ≫ snd _ _).left ∧
        ∀ (U : SchemeOver k) (a : U ⟶ (testSpec k).obj (op R)) (g : U ⟶ A.val.X),
          ConjugateContained P Q a g ↔ ∃ y : U ⟶ Z, y ≫ j = lift g a := by
  let T := (testSpec k).obj (op R)
  let F := universalConjugate P T
  let d := pullback.fst F Q.ambient
  have hG : IsAffine A.val.X.left := A.property.1
  have hP : IsAffine P.group.X.left := by
    have := P.isClosedImmersion
    exact isAffine_of_isAffineHom P.inclusion.hom.hom.left
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec (.of R)))
  have hB : IsAffine (A.val.X ⊗ T).left := by
    rw [Over.tensorObj_left]
    infer_instance
  have hd : IsClosedImmersion d.left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback F Q.ambient).map (Over.forget _)).flip)
      (familyAmbient_closed Q)
  have hp : LocallyOfFinitePresentation (snd A.val.X T).left := by
    have : LocallyOfFiniteType A.val.X.hom := A.property.2.1
    have : LocallyOfFinitePresentation A.val.X.hom := inferInstance
    exact inferInstanceAs (LocallyOfFinitePresentation (pullback.snd A.val.X.hom T.hom))
  have hQclosed := familyAmbient_closed Q
  have hQsmooth : Smooth (Q.ambient ≫ snd A.val.X T).left := by
    rw [Family.ambient_snd]
    exact Q.smooth
  have hQf : LocallyOfFinitePresentation Q.ambient.left := by
    apply finitePresentation_of_closed_over Q.ambient.left (snd A.val.X T).left
  have hdf : LocallyOfFinitePresentation d.left :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_hasPullback F Q.ambient).map (Over.forget _)).flip) hQf
  obtain ⟨Z, j, hj, h⟩ := familyFactorizationLocus d hd
  have hjf : LocallyOfFinitePresentation j.left := familyLocus_finite d hd hdf j hj h
  have hZa : IsAffine Z.left := isAffine_of_isAffineHom j.left
  refine ⟨Z, j, hj, inferInstanceAs (LocallyOfFinitePresentation (j.left ≫ (snd A.val.X T).left)),
    inferInstanceAs (QuasiCompact (j.left ≫ (snd A.val.X T).left)),
    inferInstanceAs (QuasiSeparated (j.left ≫ (snd A.val.X T).left)), fun U a g ↦ ?_⟩
  rw [← h]
  constructor
  · rintro ⟨f, hf⟩
    have eq : (P.group.X ◁ lift g a) ≫ F = f ≫ Q.ambient :=
      (universalConjugate_comp P a g).trans hf.symm
    exact ⟨pullback.lift _ _ eq, pullback.lift_fst _ _ _⟩
  · rintro ⟨f, hf⟩
    refine ⟨f ≫ pullback.snd _ _, ?_⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hf]
    exact universalConjugate_comp P a g


private theorem comp_conjugateInclusion (P : ClosedSubgroup G) (g : U ⟶ G.X)
    {V : SchemeOver k} (p : V ⟶ P.group.X) (v : V ⟶ U) :
    lift p v ≫ conjugateInclusion P g =
      lift ((v ≫ g) * (p ≫ P.inclusion.hom.hom) * (v ≫ g)⁻¹) v := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [conjugateInclusion, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv]
  · simp [conjugateInclusion]

/-- Scheme equality can be tested by comparing all factorizations of points
over the test scheme, including on nonreduced schemes. -/
theorem conjugates_iff_factorizations {P : ClosedSubgroup G} {Q : Family G T}
    {a : U ⟶ T} {g : U ⟶ G.X} :
    Conjugates P Q a g ↔
      ∀ (V : SchemeOver k) (v : V ⟶ U) (z : V ⟶ G.X),
        (∃ y : V ⟶ Q.overField, y ≫ Q.ambient = lift z (v ≫ a)) ↔
          ∃ p : V ⟶ P.group.X,
            (v ≫ g) * (p ≫ P.inclusion.hom.hom) * (v ≫ g)⁻¹ = z := by
  let f := Q.ambient
  let b := G.X ◁ a
  let c := conjugateInclusion P g
  have hc : Mono c := by
    have hi : IsClosedImmersion P.inclusion.hom.hom.left := P.isClosedImmersion
    have hmono : Mono P.inclusion.hom.hom :=
      (Over.forget _).mono_of_mono_map (f := P.inclusion.hom.hom)
        (inferInstanceAs (Mono P.inclusion.hom.hom.left))
    constructor
    intro V x y h
    have hs : x ≫ snd P.group.X U = y ≫ snd P.group.X U := by
      simpa [c, conjugateInclusion] using congrArg (· ≫ snd G.X U) h
    have ht : (x ≫ snd P.group.X U ≫ g) * (x ≫ fst P.group.X U ≫ P.inclusion.hom.hom) *
        (x ≫ snd P.group.X U ≫ g)⁻¹ =
        (y ≫ snd P.group.X U ≫ g) * (y ≫ fst P.group.X U ≫ P.inclusion.hom.hom) *
        (y ≫ snd P.group.X U ≫ g)⁻¹ := by
      simpa [c, conjugateInclusion, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv] using
        congrArg (· ≫ fst G.X U) h
    have hs' := congrArg (· ≫ g) hs
    simp only [Category.assoc] at hs'
    rw [hs'] at ht
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono P.inclusion.hom.hom).mp
      simpa [Category.assoc] using ht
    · exact hs
  have : Mono f := by
    have : IsClosedImmersion f.left := familyAmbient_closed Q
    exact (Over.forget _).mono_of_mono_map (f := f) (inferInstanceAs (Mono f.left))
  constructor
  · rintro ⟨e, he⟩ V v z
    constructor
    · rintro ⟨y, hy⟩
      have hcomm : y ≫ f = lift z v ≫ b := by
        rw [hy]
        apply CartesianMonoidalCategory.hom_ext <;> simp [b]
      let s := pullback.lift y (lift z v) hcomm ≫ e.inv
      have hs : s ≫ c = lift z v := by
        change s ≫ conjugateInclusion P g = _
        rw [← he]
        simpa only [s, Category.assoc, Iso.inv_hom_id_assoc] using
          (pullback.lift_snd y (lift z v) hcomm)
      have hsv : s ≫ snd P.group.X U = v := by
        simpa [c, conjugateInclusion] using congrArg (· ≫ snd G.X U) hs
      refine ⟨s ≫ fst P.group.X U, ?_⟩
      have hx : lift (s ≫ fst P.group.X U) v = s := by
        apply CartesianMonoidalCategory.hom_ext
        · simp
        · simpa using hsv.symm
      have h' : lift (s ≫ fst P.group.X U) v ≫ conjugateInclusion P g = lift z v := by
        rw [hx]
        exact hs
      rw [comp_conjugateInclusion] at h'
      simpa only [lift_fst] using congrArg (· ≫ fst G.X U) h'
    · rintro ⟨p, hp⟩
      refine ⟨lift p v ≫ e.hom ≫ pullback.fst _ _, ?_⟩
      rw [Category.assoc, Category.assoc e.hom, pullback.condition, ← Category.assoc e.hom, he,
        ← Category.assoc, comp_conjugateInclusion, hp]
      apply CartesianMonoidalCategory.hom_ext <;> simp
  · intro h
    let A := P.group.X ⊗ U
    let B := pullback f b
    let v : A ⟶ U := snd _ _
    let z : A ⟶ G.X := conjugateFamily P.inclusion g
    have hz : (v ≫ g) * (fst P.group.X U ≫ P.inclusion.hom.hom) * (v ≫ g)⁻¹ = z := rfl
    obtain ⟨y, hy⟩ := (h A v z).mpr ⟨fst _ _, hz⟩
    have hy' : y ≫ f = c ≫ b := by
      rw [hy]
      apply CartesianMonoidalCategory.hom_ext <;> simp [c, v, z, b, conjugateInclusion]
    let l : A ⟶ B := pullback.lift y c hy'
    have hl : l ≫ pullback.snd f b = c := pullback.lift_snd _ _ _
    let v' : B ⟶ U := pullback.snd f b ≫ snd _ _
    let z' : B ⟶ G.X := pullback.snd f b ≫ fst _ _
    have hz' : pullback.fst f b ≫ f = lift z' (v' ≫ a) := by
      rw [pullback.condition]
      apply CartesianMonoidalCategory.hom_ext <;> simp [z', v', b]
    obtain ⟨p, hp⟩ := (h B v' z').mp ⟨pullback.fst _ _, hz'⟩
    let r : B ⟶ A := lift p v'
    have hr : r ≫ c = pullback.snd f b := by
      change lift p v' ≫ conjugateInclusion P g = _
      rw [comp_conjugateInclusion, hp]
      apply CartesianMonoidalCategory.hom_ext <;> simp [z', v']
    refine ⟨⟨l, r, (cancel_mono c).mp ?_, (cancel_mono (pullback.snd f b)).mp ?_⟩, hl⟩
    · rw [Category.assoc, hr, hl, Category.id_comp]
    · rw [Category.assoc, hl, hr, Category.id_comp]

theorem conjugates_pullback {P : ClosedSubgroup G} {Q : Family G T}
    {a : U ⟶ T} {g : U ⟶ G.X} (h : Conjugates P Q a g)
    {V : SchemeOver k} (v : V ⟶ U) :
    Conjugates P Q (v ≫ a) (v ≫ g) := by
  rw [conjugates_iff_factorizations] at h ⊢
  intro W w z
  simpa only [Category.assoc] using h W (w ≫ v) z

open private conjugateLe_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

/-- Two simultaneous conjugacies differ by an element of the scheme normalizer. -/
theorem normalizes_of_conjugates {P : ClosedSubgroup G} {Q : Family G T}
    {a : U ⟶ T} {g h : U ⟶ G.X} (hg : Conjugates P Q a g) (hh : Conjugates P Q a h) :
    Normalizes P.inclusion (g⁻¹ * h) := by
  have aux {g h : U ⟶ G.X} (hg : Conjugates P Q a g) (hh : Conjugates P Q a h) :
      ConjugateLe P.inclusion (g⁻¹ * h) := by
    apply (conjugateLe_iff _ _).mpr
    intro V v p
    let z := (v ≫ h) * (p ≫ P.inclusion.hom.hom) * (v ≫ h)⁻¹
    obtain ⟨q, hq⟩ := ((conjugates_iff_factorizations.mp hg) V v z).mp
      (((conjugates_iff_factorizations.mp hh) V v z).mpr ⟨p, rfl⟩)
    refine ⟨q, ?_⟩
    calc
      _ = (v ≫ g)⁻¹ * z * (v ≫ g) := by rw [← hq]; group
      _ = _ := by simp only [z, MonObj.comp_mul, GrpObj.comp_inv]; group
  apply (LinearAlgebraicGroups.normalizesIff k P.inclusion
    P.isClosedImmersion U _).mpr
  exact ⟨aux hg hh, by simpa using aux hh hg⟩

private theorem conjugates_mul_subgroup {P : ClosedSubgroup G} {Q : Family G T}
    {a : U ⟶ T} {g : U ⟶ G.X} (hg : Conjugates P Q a g) (p : U ⟶ P.group.X) :
    Conjugates P Q a (g * (p ≫ P.inclusion.hom.hom)) := by
  rw [conjugates_iff_factorizations] at hg ⊢
  intro V v z
  rw [hg V v z]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(v ≫ p)⁻¹ * x * (v ≫ p), ?_⟩
    simp only [MonObj.comp_mul, Category.assoc, MonObj.mul_comp,
      GrpObj.inv_comp] at *
    rw [← hx]
    group
  · rintro ⟨x, hx⟩
    refine ⟨(v ≫ p) * x * (v ≫ p)⁻¹, ?_⟩
    simp only [MonObj.comp_mul, Category.assoc, MonObj.mul_comp,
      GrpObj.inv_comp] at *
    rw [← hx]
    group

private theorem quotient_eq_iff {P : ClosedSubgroup G} (D : Specs.QuotientEmbedding.Presentation P)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection)
    (g h : U ⟶ G.X) :
      g ≫ D.projection = h ≫ D.projection ↔
        ∃ p : U ⟶ P.group.X, p ≫ P.inclusion.hom.hom = g⁻¹ * h := by
  constructor
  · intro he
    let w := hD.lift g h he
    have hg : w ≫ prod.fst = g := hD.lift_fst g h he
    have hh : w ≫ Specs.HomogeneousQuotient.rightMultiplication P = h := hD.lift_snd g h he
    have eq : g * (w ≫ prod.snd ≫ P.inclusion.hom.hom) = h := by
      simpa only [Specs.HomogeneousQuotient.rightMultiplication, MonObj.comp_mul,
        Category.assoc, hg] using hh
    exact ⟨w ≫ prod.snd, by
      rw [Category.assoc, ← eq, inv_mul_cancel_left]⟩
  · rintro ⟨p, hp⟩
    have eq : (prod.lift g p) ≫ Specs.HomogeneousQuotient.rightMultiplication P = h := by
      simp [Specs.HomogeneousQuotient.rightMultiplication, MonObj.comp_mul, hp]
    calc
      _ = (prod.lift g p) ≫ prod.fst ≫ D.projection := by simp
      _ = (prod.lift g p) ≫ Specs.HomogeneousQuotient.rightMultiplication P ≫ D.projection :=
        congrArg ((prod.lift g p) ≫ ·) hD.w
      _ = _ := by rw [← Category.assoc, eq]

private theorem exists_over_desc {W X Y : SchemeOver k}
    (f : W ⟶ X) [EffectiveEpi f.left] (q : W ⟶ Y)
    (hq : ∀ (V : SchemeOver k) (a b : V ⟶ W), a ≫ f = b ≫ f → a ≫ q = b ≫ q) :
    ∃ x : X ⟶ Y, f ≫ x = q := by
  have heq {V : Scheme} (a b : V ⟶ W.left) (he : a ≫ f.left = b ≫ f.left) :
      a ≫ q.left = b ≫ q.left := by
    let V' : SchemeOver k := Over.mk (a ≫ W.hom)
    let a' : V' ⟶ W := Over.homMk a
    let b' : V' ⟶ W := Over.homMk b (by
      rw [← Over.w f, ← Category.assoc, ← he, Category.assoc, Over.w f]; rfl)
    exact congrArg (·.left) (hq V' a' b' (Over.OverMorphism.ext he))
  let x := EffectiveEpi.desc f.left q.left heq
  have hx : f.left ≫ x = q.left := EffectiveEpi.fac f.left q.left heq
  let x' : X ⟶ Y := Over.homMk x ((cancel_epi f.left).mp (by
    rw [← Category.assoc, hx, Over.w q, Over.w f]))
  exact ⟨x', Over.OverMorphism.ext hx⟩

/-- A simultaneous conjugacy after a faithfully flat finitely presented cover
gives a unique flag parameter when its transporter is represented. -/
theorem uniqueFlagParameter (P : ClosedSubgroup G) (Q : Family G T)
    (D : Specs.QuotientEmbedding.Presentation P)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection)
    (hN : RepresentsSubgroup P (fun _ g ↦ Normalizes P.inclusion g))
    {Z : SchemeOver k} (j : Z ⟶ G.X ⊗ T) (hj : IsClosedImmersion j.left)
    (hZ : RepresentsTransporter P Q j)
    [Flat (j ≫ snd G.X T).left] [Surjective (j ≫ snd G.X T).left]
    [LocallyOfFinitePresentation (j ≫ snd G.X T).left] :
    ∃! x : T ⟶ D.scheme, Classifies D Q x := by
  let f := j ≫ snd G.X T
  let g := j ≫ fst G.X T
  have hg : Conjugates P Q f g :=
    (hZ Z f g).mpr ⟨𝟙 _, by simp [f, g]⟩
  have cmp {V : SchemeOver k} {a : V ⟶ T} {b c : V ⟶ G.X}
      (hb : Conjugates P Q a b) :
      c ≫ D.projection = b ≫ D.projection ↔ Conjugates P Q a c := by
    constructor
    · intro eq
      obtain ⟨p, hp⟩ := (quotient_eq_iff D hD b c).mp eq.symm
      have hcp : b * (p ≫ P.inclusion.hom.hom) = c := by rw [hp, mul_inv_cancel_left]
      exact hcp ▸ conjugates_mul_subgroup hb p
    · intro hc
      exact ((quotient_eq_iff D hD b c).mpr
        ((hN V (b⁻¹ * c)).mp (normalizes_of_conjugates hb hc))).symm
  have hc : ∀ (V : SchemeOver k) (a b : V ⟶ Z),
      a ≫ f = b ≫ f → a ≫ (g ≫ D.projection) = b ≫ (g ≫ D.projection) := by
    intro V a b he
    have ha := conjugates_pullback hg a
    have hb := conjugates_pullback hg b
    rw [he] at ha
    exact (by simpa only [Category.assoc] using (cmp hb).mpr ha)
  have : EffectiveEpi f.left := inferInstanceAs (EffectiveEpi (j ≫ snd G.X T).left)
  obtain ⟨x, hx⟩ := exists_over_desc f (g ≫ D.projection) hc
  refine ⟨x, ?_, ?_⟩
  · intro V a b
    constructor
    · intro hb
      let p := pullback.fst a f
      let r := pullback.snd a f
      have hp : p ≫ a = r ≫ f := pullback.condition
      have hr : Conjugates P Q (p ≫ a) (r ≫ g) := hp ▸ conjugates_pullback hg r
      have hpb : (p ≫ b) ≫ D.projection = (r ≫ g) ≫ D.projection := by
        calc
          _ = p ≫ a ≫ x := by rw [Category.assoc, hb]
          _ = _ := by rw [← Category.assoc, hp, Category.assoc, hx]; exact (Category.assoc ..).symm
      obtain ⟨y, hy⟩ := (hZ _ (p ≫ a) (p ≫ b)).mp ((cmp hr).mp hpb)
      have hyl : y ≫ j = p ≫ lift b a := by
        rw [hy]
        apply CartesianMonoidalCategory.hom_ext <;> simp
      have pull := (IsPullback.of_hasPullback a f).map (Over.forget _)
      have : Flat p.left := MorphismProperty.of_isPullback pull.flip ‹Flat f.left›
      have : Surjective p.left := MorphismProperty.of_isPullback pull.flip ‹Surjective f.left›
      have : LocallyOfFinitePresentation p.left :=
        MorphismProperty.of_isPullback pull.flip ‹LocallyOfFinitePresentation f.left›
      have : Mono j := (Over.forget _).mono_of_mono_map (f := j)
        (by let := hj; exact inferInstanceAs (Mono j.left))
      obtain ⟨w, hw⟩ := exists_over_desc p y
        (fun W c d heq ↦ (cancel_mono j).mp (by
          simp only [Category.assoc, hyl, reassoc_of% heq]))
      apply (hZ _ a b).mpr
      have : Epi p := (Over.forget _).epi_of_epi_map (f := p)
        (inferInstanceAs (Epi p.left))
      exact ⟨w, (cancel_epi p).mp (by rw [← Category.assoc, hw, hyl])⟩
    · intro hb
      obtain ⟨y, hy⟩ := (hZ V a b).mp hb
      have eq₁ : y ≫ g = b := by simp [g, ← Category.assoc, hy]
      have eq₂ : y ≫ f = a := by simp [f, ← Category.assoc, hy]
      calc
        _ = y ≫ (g ≫ D.projection) := by rw [← Category.assoc, eq₁]
        _ = _ := by rw [← hx, ← Category.assoc, eq₂]
  · intro x' hx'
    have hf : g ≫ D.projection = f ≫ x' := (hx' Z f g).mpr hg
    have : Epi f := (Over.forget _).epi_of_epi_map (f := f) (inferInstanceAs (Epi f.left))
    exact (cancel_epi f).mp (hf.symm.trans hx.symm)


private theorem exists_geometric_point_over (T : SchemeOver k) (x : T.left) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K)
      (a : (testSpec k).obj (op (CommAlgCat.of k K)) ⟶ T),
        a.left (IsLocalRing.closedPoint K) = x := by
  let K := AlgebraicClosure (T.left.residueField x)
  let i : Spec (CommRingCat.of K) ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K)) ≫
      T.left.fromSpecResidueField x
  obtain ⟨f, hf⟩ := Spec.map_surjective (i ≫ T.hom)
  let : Algebra k K := f.hom.toAlgebra
  let a : (testSpec k).obj (op (CommAlgCat.of k K)) ⟶ T := Over.homMk i hf.symm
  refine ⟨K, inferInstance, inferInstance, inferInstance, a, ?_⟩
  have h : (Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K)))
      (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint (T.left.residueField x) :=
    Subsingleton.elim _ _
  change i (IsLocalRing.closedPoint K) = x
  calc
    _ = T.left.fromSpecResidueField x
        ((Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField x) K)))
          (IsLocalRing.closedPoint K)) := Scheme.Hom.comp_apply ..
    _ = _ := congrArg (T.left.fromSpecResidueField x) h
    _ = _ := Scheme.fromSpecResidueField_apply _ _

/-- The coefficient locus hits every base point when the two subgroups have
geometrically conjugate fibres. -/
theorem containmentLocus_surjective (P : ClosedSubgroup G) (Q : Family G T)
    (hQ : SameGeometricType P Q) {Z : SchemeOver k} (j : Z ⟶ G.X ⊗ T)
    (hj : ∀ (U : SchemeOver k) (a : U ⟶ T) (g : U ⟶ G.X),
      ConjugateContained P Q a g ↔ ∃ y : U ⟶ Z, y ≫ j = lift g a) :
    Surjective (j ≫ snd G.X T).left := by
  constructor
  intro x
  obtain ⟨K, hK, hcl, hAlg, a, ha⟩ := exists_geometric_point_over T x
  let : Field K := hK
  let : IsAlgClosed K := hcl
  let : Algebra k K := hAlg
  obtain ⟨g, hg⟩ := hQ K a
  obtain ⟨y, hy⟩ := (hj _ a g).mp (conjugateContained_of_conjugates hg)
  have hya : y ≫ (j ≫ snd G.X T) = a := by rw [← Category.assoc, hy, lift_snd]
  exact ⟨y.left (IsLocalRing.closedPoint K), by
    simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
      (congrArg (fun f ↦ f.left (IsLocalRing.closedPoint K)) hya).trans ha⟩


/-- A surjection with finitely generated kernel and projective target over the
base is an isomorphism if it is injective on base change to every field. -/
theorem injective_of_injective_field_baseChange
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Module.Projective R A]
    (f : B →ₐ[R] A) (hf : Function.Surjective f) (hfin : (RingHom.ker f.toRingHom).FG)
    (hfield : ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id R K) f)) :
    Function.Injective f := by
  let I := RingHom.ker f.toRingHom
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top_of_surjective _ hf)
  have hs' (x : A) : f (s x) = x := LinearMap.congr_fun hs x
  let r : B →ₗ[R] I := (LinearMap.id - s.comp f.toLinearMap).codRestrict
    (I.restrictScalars R) (fun x ↦ by
      change f (x - s (f x)) = 0
      rw [map_sub, hs', sub_self])
  have hr (x : I) : r x = x := by
    have hx : f x = 0 := x.property
    apply Subtype.ext
    change (x : B) - s (f x) = x
    rw [hx, map_zero, sub_zero]
  have hI : (I : Submodule B B) = ⊥ := by
    rw [← Submodule.annihilator_eq_top_iff]
    by_contra h
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (I : Submodule B B).annihilator h
    let K := B ⧸ q
    let : Field K := Ideal.Quotient.field q
    let : Algebra R K := inferInstanceAs (Algebra R (B ⧸ q))
    let : IsScalarTower R B K := inferInstanceAs (IsScalarTower R B (B ⧸ q))
    have hqI : (I : Submodule B B) ≤ q • (I : Submodule B B) := by
      intro x hx
      let y : I := ⟨x, hx⟩
      have ht : (1 : K) ⊗ₜ[R] x = 0 := by
        apply hfield K
        have hfx : f x = 0 := hx
        simp [hfx]
      have ht' : (1 : K) ⊗ₜ[R] y = 0 := by
        have h' := congrArg (r.lTensor K) ht
        change (1 : K) ⊗ₜ[R] r x = (r.lTensor K) 0 at h'
        simpa only [show r x = y from hr y, map_zero] using h'
      let t : K ⊗[R] I →ₗ[R] K ⊗[B] I := TensorProduct.lift
        { toFun := fun a ↦ ((TensorProduct.mk B K I) a).restrictScalars R
          map_add' := by intros; ext; simp
          map_smul' := by
            intro a b
            ext c
            change (a • b) ⊗ₜ[B] c = a • (b ⊗ₜ[B] c)
            rw [← IsScalarTower.algebraMap_smul B a b, TensorProduct.smul_tmul',
              IsScalarTower.algebraMap_smul] }
      have e : (1 : K) ⊗ₜ[B] y = 0 := by
        have ht'' := congrArg t ht'
        rw [map_zero] at ht''
        exact ht''
      have ey : y ∈ q • (⊤ : Submodule B I) := by
        have eq := congrArg (TensorProduct.quotTensorEquivQuotSMul I q) e
        rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
          Submodule.Quotient.mk_eq_zero] at eq
        exact eq
      have em : x ∈ (q • (⊤ : Submodule B I)).map I.subtype := ⟨y, ey, rfl⟩
      simpa only [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] using em
    obtain ⟨a, ha, hann⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      q (I : Submodule B B) hfin hqI
    have haq : a ∈ q := hle (Submodule.mem_annihilator.mpr hann)
    exact hq.ne_top ((Ideal.eq_top_iff_one q).mpr (by simpa using q.sub_mem haq ha))
  exact (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr hI



private theorem injective_of_surjective_ringEnd {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A →+* A) (hf : Function.Surjective f) : Function.Injective f := by
  let F : ℕ →o Submodule A A :=
    ⟨fun n ↦ RingHom.ker (f ^ n), fun n m hnm x hx ↦ by
      change (f ^ n) x = 0 at hx
      change (f ^ m) x = 0
      rw [show m = (m - n) + n by omega, pow_add, RingHom.coe_mul, Function.comp_apply,
        hx, map_zero]⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian A A)) F
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, hy⟩ := hf.iterate n x
  have hy' : y ∈ F (n + 1) := by
    change (f ^ (n + 1)) y = 0
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, RingHom.coe_pow, hy]
    exact hx
  have hny : (f^[n]) y = 0 := by
    rwa [← hn (n + 1) (Nat.le_succ n)] at hy'
  exact (Submodule.mem_bot A).mpr (hy.symm.trans hny)

private theorem isIso_closedEnd_of_noetherian_affine {X : Scheme.{u}} [IsAffine X]
    [IsNoetherianRing (X.presheaf.obj (op ⊤))] (f : X ⟶ X) [IsClosedImmersion f] : IsIso f := by
  have hf := (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  exact IsClosedImmersion.isIso_of_injective_of_isAffine (f := f)
    (injective_of_surjective_ringEnd f.appTop.hom hf)

private def conjugationOver (g : U ⟶ G.X) : G.X ⊗ U ⟶ G.X ⊗ U :=
  lift (conjugateFamily (𝟙 G) g) (snd _ _)

private theorem comp_conjugationOver (g : U ⟶ G.X) {V : SchemeOver k}
    (v : V ⟶ G.X ⊗ U) :
    v ≫ conjugationOver g =
      lift ((v ≫ snd _ _ ≫ g) * (v ≫ fst _ _) * (v ≫ snd _ _ ≫ g)⁻¹) (v ≫ snd _ _) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [conjugationOver, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv]
  · simp [conjugationOver]

private theorem conjugationOver_mul_inv (g : U ⟶ G.X) :
    conjugationOver g ≫ conjugationOver g⁻¹ = 𝟙 _ := by
  rw [comp_conjugationOver]
  apply CartesianMonoidalCategory.hom_ext
  · simp [conjugationOver, conjugateFamily, GrpObj.comp_inv, mul_assoc]
  · simp [conjugationOver]

private def conjugationOverIso (g : U ⟶ G.X) : G.X ⊗ U ≅ G.X ⊗ U :=
  ⟨conjugationOver g, conjugationOver g⁻¹, conjugationOver_mul_inv g,
    by simpa only [inv_inv] using conjugationOver_mul_inv g⁻¹⟩

theorem conjugateInclusion_closed (P : ClosedSubgroup G) (g : U ⟶ G.X) :
    IsClosedImmersion (conjugateInclusion P g).left := by
  let i := P.inclusion.hom.hom
  have hpb : IsPullback (i ▷ U) (fst P.group.X U) (fst G.X U) i := by
    refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _
      (fun c ↦ lift c.snd (c.fst ≫ snd G.X U)) ?_ ?_ ?_⟩⟩
    · intro c
      apply CartesianMonoidalCategory.hom_ext
      · simpa using c.condition.symm
      · simp
    · simp
    · intro c m hm hm'
      apply CartesianMonoidalCategory.hom_ext
      · simpa using hm'
      · simpa using congrArg (· ≫ snd G.X U) hm
  have hi : IsClosedImmersion (i ▷ U).left := MorphismProperty.of_isPullback
    ((hpb.map (Over.forget _)).flip) P.isClosedImmersion
  have eq : conjugateInclusion P g = (i ▷ U) ≫ (conjugationOverIso g).hom := by
    change _ = (i ▷ U) ≫ conjugationOver g
    rw [comp_conjugationOver]
    apply CartesianMonoidalCategory.hom_ext <;> simp [conjugateInclusion, conjugateFamily, i]
  have hIso : IsIso (conjugationOverIso g).hom.left :=
    ((Over.forget _).mapIso (conjugationOverIso g)).isIso_hom
  rw [eq]
  exact IsClosedImmersion.comp (i ▷ U).left (conjugationOverIso g).hom.left

/-- A containment is equality whenever the two subgroups are already known to
be conjugate and the constant subgroup on the test scheme is Noetherian affine. -/
theorem conjugates_of_containment_of_noetherian
    {P : ClosedSubgroup G} {Q : Family G T} {a : U ⟶ T} {g h : U ⟶ G.X}
    [IsAffine (P.group.X ⊗ U).left]
    [IsNoetherianRing ((P.group.X ⊗ U).left.presheaf.obj (op ⊤))]
    (hg : ConjugateContained P Q a g) (hh : Conjugates P Q a h) :
    Conjugates P Q a g := by
  obtain ⟨p, hp⟩ := hg
  obtain ⟨e, he⟩ := hh
  let f := pullback.lift p (conjugateInclusion P g) hp
  have hf : f ≫ pullback.snd _ _ = conjugateInclusion P g := pullback.lift_snd _ _ _
  let F := f ≫ e.inv
  have he' : F ≫ conjugateInclusion P h = conjugateInclusion P g := by
    rw [← he]
    simp only [F, Category.assoc, Iso.inv_hom_id_assoc, hf]
  have hfc : IsClosedImmersion F.left := by
    have hclosed := conjugateInclusion_closed P g
    have hclosed' := conjugateInclusion_closed P h
    have hleft : F.left ≫ (conjugateInclusion P h).left =
        (conjugateInclusion P g).left := congrArg (·.left) he'
    have hcomp : IsClosedImmersion (F.left ≫ (conjugateInclusion P h).left) := by
      rw [hleft]
      exact hclosed
    exact IsClosedImmersion.of_comp_isClosedImmersion F.left (conjugateInclusion P h).left
  have hi : IsIso F.left := isIso_closedEnd_of_noetherian_affine _
  have hF : IsIso F := by
    have : IsIso ((Over.forget _).map F) := hi
    exact isIso_of_reflects_iso F (Over.forget _)
  have hf' : f = F ≫ e.hom := by simp [F]
  have hi' : IsIso f := hf'.symm ▸ inferInstanceAs (IsIso (F ≫ e.hom))
  exact ⟨asIso f, hf⟩


/-- A strictly negative Laurent weight in a polynomial orbit must have zero
coefficient. This holds over any commutative test ring. -/
theorem negativeWeightCoefficient_eq_zero {R : Type u} [CommRing R]
    {n : ℤ} (hn : n < 0) {a : R} (p : Polynomial R)
    (he : Polynomial.toLaurent p = LaurentPolynomial.C a * LaurentPolynomial.T n) :
    a = 0 := by
  by_contra h
  have hmem : n ∈ (Polynomial.toLaurent p).coeff.support := by
    rw [he, LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero h n]
    simp
  rw [LaurentPolynomial.support_coeff_toLaurent] at hmem
  obtain ⟨m, _, hm⟩ := Finset.mem_map.mp hmem
  change (m : ℤ) = n at hm
  omega


/-- For an affine finitely presented morphism, lifting points across every
square-zero quotient is sufficient to prove smoothness. -/
theorem smooth_of_squareZeroLifting {R : CommRingCat.{u}} {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec R) [LocallyOfFinitePresentation f]
    (hl : ∀ (B : CommRingCat.{u}) (I : Ideal B), I ^ 2 = ⊥ →
      ∀ (b : Spec B ⟶ Spec R) (x : Spec (CommRingCat.of (B ⧸ I)) ⟶ X),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b = x ≫ f →
        ∃ y : Spec B ⟶ X, y ≫ f = b ∧
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y = x) :
    Smooth f := by
  let e := X.isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ f)
  let C := X.presheaf.obj (op ⊤)
  let : Algebra R C := φ.hom.toAlgebra
  have hφₐ : CommRingCat.ofHom (algebraMap R C) = φ := rfl
  have hfp : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have hfpₐ : Algebra.FinitePresentation R C := (LocallyOfFinitePresentation.SpecMap_iff φ).mp hfp
  have hformal : Algebra.FormallySmooth R C := by
    apply Algebra.FormallySmooth.iff_comp_surjective.mpr
    intro B _ _ I hI v
    let r := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let v' := Spec.map (CommRingCat.ofHom v.toRingHom)
    let x := v' ≫ e.inv
    have hbx : r ≫ b = x ≫ f := by
      change r ≫ b = (v' ≫ e.inv) ≫ f
      rw [Category.assoc, ← hφ, ← hφₐ]
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom v.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R C))
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      exact (v.commutes a).symm
    obtain ⟨y, hy, hy'⟩ := hl (.of B) I hI b x hbx
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ e.hom)
    have hψφ : Spec.map ψ ≫ Spec.map φ = b := by
      rw [hψ, hφ, Category.assoc, e.hom_inv_id_assoc]
      exact hy
    have hψR : φ ≫ ψ = CommRingCat.ofHom (algebraMap R B) :=
      Spec.map_injective (by simpa only [Spec.map_comp] using hψφ)
    let w : C →ₐ[R] B :=
      { toRingHom := ψ.hom
        commutes' := by
          intro a
          exact congrArg (fun m : R ⟶ CommRingCat.of B ↦ m a) hψR }
    refine ⟨w, ?_⟩
    have hψv : r ≫ Spec.map ψ = v' := by
      rw [hψ, ← Category.assoc]
      change r ≫ y = x at hy'
      rw [hy']
      change (v' ≫ e.inv) ≫ e.hom = _
      simp
    have hψI : ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) =
        CommRingCat.ofHom v.toRingHom :=
      Spec.map_injective (by simpa only [Spec.map_comp] using hψv)
    exact AlgHom.ext fun a ↦ congrArg (fun m : C ⟶ CommRingCat.of (B ⧸ I) ↦ m a) hψI
  have hs : Smooth (Spec.map φ) := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (show Algebra.Smooth R C from ⟨hformal, hfpₐ⟩)
  rw [hφ, MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)] at hs
  exact hs


/-- Geometric fibres suffice in the projective-target form of the fibral
isomorphism criterion for a closed immersion. -/
theorem injective_of_injective_geometric_baseChange
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Module.Projective R A]
    (f : B →ₐ[R] A) (hf : Function.Surjective f) (hfin : (RingHom.ker f.toRingHom).FG)
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id R K) f)) :
    Function.Injective f := by
  apply injective_of_injective_field_baseChange f hf hfin
  intro K _ _
  let L := AlgebraicClosure K
  let : Algebra R L := inferInstanceAs (Algebra R (AlgebraicClosure K))
  let : IsScalarTower R K L := inferInstanceAs (IsScalarTower R K (AlgebraicClosure K))
  let t : K →ₐ[R] L := IsScalarTower.toAlgHom R K L
  have hlin : Function.Injective (Algebra.linearMap K L) := (algebraMap K L).injective
  obtain ⟨s, hs⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hlin)
  have htensor : Function.Injective (Algebra.TensorProduct.map t (AlgHom.id R B)) := by
    have hl : (TensorProduct.map (s.restrictScalars R) (LinearMap.id : B →ₗ[R] B)).comp
        (Algebra.TensorProduct.map t (AlgHom.id R B)).toLinearMap = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      have hst : s (t x) = x := LinearMap.congr_fun hs x
      simp [hst]
    have leftInv : Function.LeftInverse
        (TensorProduct.map (s.restrictScalars R) (LinearMap.id : B →ₗ[R] B))
        (Algebra.TensorProduct.map t (AlgHom.id R B)) :=
      fun x ↦ LinearMap.congr_fun hl x
    exact leftInv.injective
  intro x y hxy
  apply htensor
  apply hgeom L
  have hc : (Algebra.TensorProduct.map (AlgHom.id R L) f).comp
      (Algebra.TensorProduct.map t (AlgHom.id R B)) =
      (Algebra.TensorProduct.map t (AlgHom.id R A)).comp
        (Algebra.TensorProduct.map (AlgHom.id R K) f) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro a b
    simp
  exact (DFunLike.congr_fun hc x).trans
    ((congrArg (Algebra.TensorProduct.map t (AlgHom.id R A)) hxy).trans
      (DFunLike.congr_fun hc y).symm)

private abbrev algebraSpecMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

private theorem tensorSpecPullback (R S A : Type u) [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] :
    IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom))
      (algebraSpecMap S (S ⊗[R] A)) (algebraSpecMap R A) (algebraSpecMap R S) := by
  refine (IsPullback.of_hasPullback (algebraSpecMap R S) (algebraSpecMap R A)).flip.of_iso
    (pullbackSpecIso R S A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [pullbackSpecIso_hom_fst']
  · simp
  · simp

private theorem tensorSpecMapPullback (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {B A : Type u} [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
    (f : B →ₐ[R] A) :
    IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom)) := by
  have h₁ : Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom) ≫ algebraSpecMap S (S ⊗[R] B) =
      algebraSpecMap S (S ⊗[R] A) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h₂ : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ algebraSpecMap R B =
      algebraSpecMap R A := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact f.commutes x
  apply IsPullback.of_bot (v₂₁ := algebraSpecMap S (S ⊗[R] B))
    (v₂₂ := algebraSpecMap R B) (h₃₁ := algebraSpecMap R S)
  · rw [h₁, h₂]
    exact tensorSpecPullback R S A
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · exact tensorSpecPullback R S B

private theorem surjective_of_closedSpecMap {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsClosedImmersion (Spec.map f)] : Function.Surjective f.hom := by
  have hf := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map f)).2
  have h := (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.surjective.comp hf
  have he : (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom = (Scheme.ΓSpecIso R).hom ≫ f := by
    exact Scheme.ΓSpecIso_naturality f
  exact fun a ↦ by
    obtain ⟨b, hb⟩ := h a
    refine ⟨(Scheme.ΓSpecIso R).hom b, ?_⟩
    exact (congrArg (fun g : _ ⟶ S ↦ g b) he).symm.trans hb

private theorem isIso_of_geometricFibres {R : CommRingCat.{u}} {A : CommAlgCat R}
    [Module.Projective R A] [Algebra.FinitePresentation R A]
    {Y : Over (Spec R)} [IsAffine Y.left] [LocallyOfFinitePresentation Y.hom]
    (f : (algSpec R).obj (op A) ⟶ Y) [IsClosedImmersion f.left]
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
      {V W : Scheme.{u}} (v : W ⟶ Y.left) (w : W ⟶ Spec (.of K))
      (p : V ⟶ Spec (.of A)) (q : V ⟶ W),
      IsPullback v w Y.hom (algebraSpecMap R K) → IsPullback p q f.left v → IsIso q) :
    IsIso f.left := by
  let FF := algSpec.fullyFaithful (R := R)
  obtain ⟨B, ⟨e⟩⟩ := (essImage_algSpec (R := R)).mpr (inferInstance : IsAffine Y.left)
  let φ : B.unop →ₐ[R] A := (FF.preimage (f ≫ e.inv)).unop.hom
  let d := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hd : d = f.left ≫ e.inv.left :=
    congrArg (·.left) (FF.map_preimage (f ≫ e.inv))
  have he : d ≫ e.hom.left = f.left := by
    rw [hd, Category.assoc]
    change ((Over.forget _).map f) ≫ ((Over.forget _).mapIso e).inv ≫
      ((Over.forget _).mapIso e).hom = _
    simp
  have heb : e.hom.left ≫ Y.hom = algebraSpecMap R B.unop := Over.w e.hom
  have hei : IsIso e.inv.left := ((Over.forget _).mapIso e).isIso_inv
  have heh : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have hc : IsClosedImmersion d := by rw [hd]; infer_instance
  have hsurj : Function.Surjective φ := surjective_of_closedSpecMap (CommRingCat.ofHom φ.toRingHom)
  have hfp : LocallyOfFinitePresentation (algebraSpecMap R B.unop) := by
    rw [← heb]
    infer_instance
  have : Algebra.FinitePresentation R B.unop :=
    RingHom.finitePresentation_algebraMap.mp ((LocallyOfFinitePresentation.SpecMap_iff _).mp hfp)
  have hker := Algebra.FinitePresentation.ker_fG_of_surjective φ hsurj
  have hfi : Function.Injective φ := by
    apply injective_of_injective_geometric_baseChange φ hsurj hker
    intro K _ _ _
    let iA := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom)
    let iB := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B.unop →ₐ[R] K ⊗[R] B.unop).toRingHom)
    let q := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R K) φ).toRingHom)
    let w := algebraSpecMap K (K ⊗[R] B.unop)
    have hb : IsPullback (iB ≫ e.hom.left) w Y.hom (algebraSpecMap R K) := by
      exact (tensorSpecPullback R K B.unop).of_iso (Iso.refl _)
        ((Over.forget _).mapIso e) (Iso.refl _) (Iso.refl _) (by simp [iB]) (by simp [w])
        (by change algebraSpecMap R B.unop = e.hom.left ≫ Y.hom; exact heb.symm) (by simp)
    have hq : IsPullback iA q f.left (iB ≫ e.hom.left) :=
      (tensorSpecMapPullback R K φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Over.forget _).mapIso e) (by simp [iA]) (by simp [q])
        (by change d ≫ e.hom.left = f.left; exact he) (by simp [iB])
    have hi : IsIso q := hgeom K _ _ _ _ hb hq
    let m := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R K) φ).toRingHom
    have : IsIso (Scheme.Spec.map m.op) := hi
    have : IsIso m.op := isIso_of_reflects_iso m.op Scheme.Spec
    have : IsIso m := isIso_of_op m
    exact (ConcreteCategory.bijective_of_isIso m).injective
  let E := RingEquiv.ofBijective φ.toRingHom ⟨hfi, hsurj⟩
  let r := CommRingCat.ofHom φ.toRingHom
  have : IsIso r := E.toCommRingCatIso.isIso_hom
  have : IsIso r.op := isIso_op r
  have hdIso : IsIso d := Scheme.Spec.map_isIso r.op
  rw [← he]
  exact IsIso.comp_isIso' hdIso heh


private theorem tensorPullback {S : Type u} [Field S] (X : SchemeOver S) {A B : SchemeOver S}
    (v : A ⟶ B) : IsPullback (X ◁ v) (snd X A) (snd X B) v := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro W m n h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using congrArg (· ≫ fst X B) h₁
    · exact h₂
  · intro W a b h
    refine ⟨lift (a ≫ fst X B) b, ?_, by simp⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using h.symm

private abbrev familyPullback (Q : Family G T) (a : U ⟶ T) :=
  pullback Q.ambient (G.X ◁ a)

private abbrev familyPullbackBase (Q : Family G T) (a : U ⟶ T) :
    familyPullback Q a ⟶ U :=
  pullback.snd Q.ambient (G.X ◁ a) ≫ snd G.X U

private theorem familyPullbackSquare (Q : Family G T) (a : U ⟶ T) :
    IsPullback (pullback.fst Q.ambient (G.X ◁ a)) (familyPullbackBase Q a) Q.base a := by
  simpa only [Family.ambient_snd] using
    (IsPullback.of_hasPullback Q.ambient (G.X ◁ a)).paste_vert (tensorPullback G.X a)

private def familyPullbackMap (Q : Family G T) (a : U ⟶ T) {V : SchemeOver k} (v : V ⟶ U) :
    familyPullback Q (v ≫ a) ⟶ familyPullback Q a :=
  pullback.map _ _ _ _ (𝟙 _) (G.X ◁ v) (𝟙 _) (by simp) (by simp)

private theorem familyBaseChange (Q : Family G T) (a : U ⟶ T) {V : SchemeOver k} (v : V ⟶ U) :
    IsPullback (familyPullbackMap Q a v) (familyPullbackBase Q (v ≫ a))
      (familyPullbackBase Q a) v := by
  apply IsPullback.of_right (h₁₂ := pullback.fst Q.ambient (G.X ◁ a))
    (h₂₂ := a) (v₁₃ := Q.base)
  · simpa [familyPullbackMap] using familyPullbackSquare Q (v ≫ a)
  · simp [familyPullbackMap]
  · exact familyPullbackSquare Q a

private theorem conjugateInclusion_baseChange (P : ClosedSubgroup G) (g : U ⟶ G.X)
    {V : SchemeOver k} (v : V ⟶ U) :
    (P.group.X ◁ v) ≫ conjugateInclusion P g =
      conjugateInclusion P (v ≫ g) ≫ (G.X ◁ v) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [conjugateInclusion, conjugateFamily,
    MonObj.comp_mul, GrpObj.comp_inv]

private theorem containment_pullback {P : ClosedSubgroup G} {Q : Family G T}
    {a : U ⟶ T} {g : U ⟶ G.X} (h : ConjugateContained P Q a g) {V : SchemeOver k}
    (v : V ⟶ U) : ConjugateContained P Q (v ≫ a) (v ≫ g) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(P.group.X ◁ v) ≫ f, ?_⟩
  rw [Category.assoc, hf, ← Category.assoc, conjugateInclusion_baseChange, Category.assoc]
  simp

private theorem factorBaseChange {P : ClosedSubgroup G} {Q : Family G T}
    {a : U ⟶ T} {g : U ⟶ G.X} (f : P.group.X ⊗ U ⟶ familyPullback Q a)
    (hf : f ≫ pullback.snd _ _ = conjugateInclusion P g)
    {V : SchemeOver k} (v : V ⟶ U)
    (d : P.group.X ⊗ V ⟶ familyPullback Q (v ≫ a))
    (hd : d ≫ pullback.snd _ _ = conjugateInclusion P (v ≫ g)) :
    IsPullback (P.group.X ◁ v) d f (familyPullbackMap Q a v) := by
  have hp : Mono (pullback.snd Q.ambient (G.X ◁ a)) := by
    have hc := familyAmbient_closed Q
    have : Mono Q.ambient := (Over.forget _).mono_of_mono_map (f := Q.ambient)
      (inferInstanceAs (Mono Q.ambient.left))
    infer_instance
  have hcomm : (P.group.X ◁ v) ≫ f = d ≫ familyPullbackMap Q a v := by
    apply (cancel_mono (pullback.snd Q.ambient (G.X ◁ a))).mp
    have hm : familyPullbackMap Q a v ≫ pullback.snd Q.ambient (G.X ◁ a) =
        pullback.snd Q.ambient (G.X ◁ (v ≫ a)) ≫ (G.X ◁ v) := by
      simp [familyPullbackMap]
    rw [Category.assoc, hf, Category.assoc, hm, ← Category.assoc d, hd]
    exact conjugateInclusion_baseChange P g v
  apply IsPullback.of_bot (t := familyBaseChange Q a v) (p := hcomm)
  have hbase : f ≫ familyPullbackBase Q a = snd P.group.X U := by
    rw [← Category.assoc, hf]
    simp [conjugateInclusion]
  have hbase' : d ≫ familyPullbackBase Q (v ≫ a) = snd P.group.X V := by
    rw [← Category.assoc, hd]
    simp [conjugateInclusion]
  rw [hbase, hbase']
  exact tensorPullback P.group.X v

private def constantAffineIso {X : SchemeOver k} {A : TestAlgebra k}
    (e : (testSpec k).obj (op A) ≅ X) (R : TestAlgebra k) :
    (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (R ⊗[k] A))) ≅
      Over.mk (snd X ((testSpec k).obj (op R))).left := by
  let i := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A).toRingHom)
  let F := Over.forget (Spec (CommRingCat.of k))
  have hp : IsPullback (i ≫ e.hom.left) (algebraSpecMap R (R ⊗[k] A))
      X.hom ((testSpec k).obj (op R)).hom :=
    (tensorSpecPullback k R A).of_iso (Iso.refl _) (F.mapIso e) (Iso.refl _) (Iso.refl _)
      (by simp [i, F]) (by simp) (by exact (Over.w e.hom).symm) (by simp)
  exact Over.isoMk hp.isoPullback hp.isoPullback_hom_snd

private theorem coordinate_finiteType {X : SchemeOver k} {A : TestAlgebra k}
    (e : (testSpec k).obj (op A) ≅ X) [LocallyOfFiniteType X.hom] :
    Algebra.FiniteType k A := by
  have hi : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have ht : LocallyOfFiniteType (algebraSpecMap k A) := by
    rw [show algebraSpecMap k A = e.hom.left ≫ X.hom from (Over.w e.hom).symm]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  exact RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp ht)

private theorem isIso_pullback_snd_of_isIso {A B X Y : Scheme.{u}} {f : X ⟶ Y} {v : B ⟶ Y}
    {p : A ⟶ X} {q : A ⟶ B} (h : IsPullback p q f v) [IsIso q] :
    IsIso (pullback.snd f v) :=
  IsIso.of_isIso_fac_left h.isoPullback_hom_snd

private theorem isIso_snd_of_isIso_pullback {A B X Y : Scheme.{u}} {f : X ⟶ Y} {v : B ⟶ Y}
    {p : A ⟶ X} {q : A ⟶ B} (h : IsPullback p q f v) [IsIso (pullback.snd f v)] :
    IsIso q := h.isoPullback_hom_snd ▸ inferInstanceAs
      (IsIso (h.isoPullback.hom ≫ pullback.snd f v))


private theorem isIso_of_pullback_base {X Y S D W W' V V' : Scheme.{u}} {f : X ⟶ Y}
    {b : Y ⟶ S} {a : D ⟶ S} {j : W ⟶ Y} {t : W ⟶ D} {p : V ⟶ X} {q : V ⟶ W}
    {j' : W' ⟶ Y} {t' : W' ⟶ D} {p' : V' ⟶ X} {q' : V' ⟶ W'}
    (h₁ : IsPullback j t b a) (h₂ : IsPullback j' t' b a)
    (hq : IsPullback p q f j) (hq' : IsPullback p' q' f j') [IsIso q] : IsIso q' := by
  let e := h₁.isoPullback ≪≫ h₂.isoPullback.symm
  have he : j = e.hom ≫ j' := by
    calc
      j = h₁.isoPullback.hom ≫ pullback.fst b a := h₁.isoPullback_hom_fst.symm
      _ = _ := by rw [← h₂.isoPullback_hom_fst]; simp [e]
  have hi : IsPullback p (q ≫ e.hom) f j' :=
    hq.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp)
      (by simp) (by simpa using he)
  have : IsIso (q ≫ e.hom) := IsIso.comp_isIso' ‹IsIso q› e.isIso_hom
  have : IsIso (pullback.snd f j') := isIso_pullback_snd_of_isIso hi
  exact isIso_snd_of_isIso_pullback hq'

private theorem isIso_factor_over_affine (H : AffineAlgebraicGroup k)
    {P : ClosedSubgroup H.val} {Q : Family H.val T} (hQ : SameGeometricType P Q)
    {R : TestAlgebra k} {a : (testSpec k).obj (op R) ⟶ T}
    {g : (testSpec k).obj (op R) ⟶ H.val.X}
    (f : P.group.X ⊗ (testSpec k).obj (op R) ⟶ familyPullback Q a)
    (hf : f ≫ pullback.snd _ _ = conjugateInclusion P g) :
    IsIso f.left := by
  let U := (testSpec k).obj (op R)
  let F := Over.forget (Spec (CommRingCat.of k))
  have hA := H.property.1
  have hGt := H.property.2.1
  have hPc := P.isClosedImmersion
  have hP : IsAffine P.group.X.left := isAffine_of_isAffineHom P.inclusion.hom.hom.left
  have hPft : LocallyOfFiniteType P.group.X.hom := by
    rw [← Over.w P.inclusion.hom.hom]
    infer_instance
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hP
  let : Algebra.FiniteType k A.unop := coordinate_finiteType e
  let : Algebra.FinitePresentation k A.unop := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let E := constantAffineIso e R
  have hE : IsIso E.hom.left := ((Over.forget U.left).mapIso E).isIso_hom
  let b := familyPullbackBase Q a
  have hb : Smooth b.left :=
    MorphismProperty.of_isPullback ((familyPullbackSquare Q a).map F) Q.smooth
  have hbf : LocallyOfFinitePresentation b.left := inferInstance
  have hc : IsClosedImmersion (pullback.snd Q.ambient (H.val.X ◁ a)).left :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback _ _).map F)
      (familyAmbient_closed Q)
  have hU : IsAffine U.left := inferInstanceAs (IsAffine (Spec (.of R)))
  have hY : IsAffine (familyPullback Q a).left := by
    have : IsAffine (H.val.X ⊗ U).left := by
      rw [Over.tensorObj_left]
      infer_instance
    exact isAffine_of_isAffineHom (pullback.snd Q.ambient (H.val.X ◁ a)).left
  have hfc : IsClosedImmersion f.left := by
    have hcomp : IsClosedImmersion (f.left ≫ (pullback.snd Q.ambient (H.val.X ◁ a)).left) := by
      change IsClosedImmersion (f ≫ pullback.snd Q.ambient (H.val.X ◁ a)).left
      rw [hf]
      exact conjugateInclusion_closed P g
    exact IsClosedImmersion.of_comp_isClosedImmersion f.left (pullback.snd Q.ambient (H.val.X ◁ a)).left
  have hfb : f.left ≫ b.left = (snd P.group.X U).left := by
    have hfb' : f ≫ b = snd P.group.X U := by
      change f ≫ (pullback.snd Q.ambient (H.val.X ◁ a) ≫ snd H.val.X U) = _
      rw [← Category.assoc, hf]
      simp [conjugateInclusion, U]
    exact congrArg (·.left) hfb'
  let f' : (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (R ⊗[k] A.unop))) ⟶
      Over.mk b.left :=
    E.hom ≫ Over.homMk f.left hfb
  have hc' : IsClosedImmersion f'.left := IsClosedImmersion.comp E.hom.left f.left
  have hi : IsIso f'.left := by
    have : IsAffine (Over.mk b.left).left := hY
    have : LocallyOfFinitePresentation (Over.mk b.left).hom := hbf
    apply isIso_of_geometricFibres f'
    intro K _ _ _ V W j t p q hW hq
    let : Algebra k K := ((algebraMap R K).comp (algebraMap k R)).toAlgebra
    let : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq' rfl
    let L : TestAlgebra k := CommAlgCat.of k K
    let S := (testSpec k).obj (op L)
    let v : S ⟶ U := Over.homMk (algebraSpecMap R K) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      rfl)
    obtain ⟨g', hg'⟩ := hQ K (v ≫ a)
    have : IsAffine S.left := inferInstanceAs (IsAffine (Spec (.of K)))
    have hK : IsAffine (P.group.X ⊗ S).left := by
      rw [Over.tensorObj_left]
      infer_instance
    have : IsNoetherianRing ((P.group.X ⊗ S).left.presheaf.obj (op ⊤)) := by
      let E' := constantAffineIso e L
      let e' : Spec (CommRingCat.of (K ⊗[k] A.unop)) ≅ (P.group.X ⊗ S).left :=
        (Over.forget S.left).mapIso E'
      let eΓ := Scheme.ΓSpecIso (CommRingCat.of (K ⊗[k] A.unop))
      have : Algebra.FiniteType K (K ⊗[k] A.unop) := inferInstance
      let : IsNoetherianRing (K ⊗[k] A.unop) := Algebra.FiniteType.isNoetherianRing K _
      let iso := Scheme.Γ.mapIso e'.op ≪≫ eΓ
      exact isNoetherianRing_of_ringEquiv _ iso.commRingCatIsoToRingEquiv.symm
    have hg : ConjugateContained P Q a g := by
      refine ⟨f ≫ pullback.fst _ _, ?_⟩
      rw [Category.assoc, pullback.condition, ← Category.assoc, hf]
    obtain ⟨d, hd⟩ := conjugates_of_containment_of_noetherian (containment_pullback hg v) hg'
    let l := familyPullbackMap Q a v
    have hW' := (familyBaseChange Q a v).map F
    have hq' : IsPullback (P.group.X ◁ v).left d.hom.left f.left l.left :=
      (factorBaseChange f hf v d.hom hd).map F
    have hq'' : IsPullback ((P.group.X ◁ v).left ≫ E.inv.left) d.hom.left f'.left l.left := by
      have ew : E.inv.left ≫ f'.left = f.left := by
        change ((Over.forget U.left).mapIso E).inv ≫
          (((Over.forget U.left).mapIso E).hom ≫ f.left) = _
        simp
      exact hq'.of_iso (Iso.refl _) ((Over.forget U.left).mapIso E).symm
        (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simpa using ew.symm) (by simp)
    have : IsIso d.hom.left := (F.mapIso d).isIso_hom
    exact isIso_of_pullback_base hW' hW hq'' hq
  have : IsIso (E.hom.left ≫ f.left) := hi
  exact IsIso.of_isIso_comp_left E.hom.left f.left

/-- Scheme-theoretic containment in a family of the same geometric type forces equality. -/
theorem conjugates_of_containment (H : AffineAlgebraicGroup k)
    {P : ClosedSubgroup H.val} {Q : Family H.val T} (hQ : SameGeometricType P Q)
    {a : U ⟶ T} {g : U ⟶ H.val.X} (h : ConjugateContained P Q a g) :
    Conjugates P Q a g := by
  let F := Over.forget (Spec (CommRingCat.of k))
  obtain ⟨p, hp⟩ := h
  let f := pullback.lift p (conjugateInclusion P g) hp
  have hf : f ≫ pullback.snd _ _ = conjugateInclusion P g := pullback.lift_snd _ _ _
  let b := familyPullbackBase Q a
  let 𝒰 := U.left.affineCover
  have hIso : IsIso f.left := by
    apply (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme)
      (f := f.left) (𝒰.pullback₁ b.left)).mpr
    intro i
    let V : SchemeOver k := Over.mk (𝒰.f i ≫ U.hom)
    let v₀ : V ⟶ U := Over.homMk (𝒰.f i)
    have hV : IsAffine V.left := inferInstanceAs (IsAffine (𝒰.X i))
    obtain ⟨R, ⟨E⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hV
    let v := E.hom ≫ v₀
    obtain ⟨r, hr⟩ := containment_pullback (g := g) ⟨p, hp⟩ v
    let d := pullback.lift r (conjugateInclusion P (v ≫ g)) hr
    have hd : d ≫ pullback.snd _ _ = conjugateInclusion P (v ≫ g) :=
      pullback.lift_snd _ _ _
    have hdIso : IsIso d.left := isIso_factor_over_affine H hQ d hd
    have hq := (factorBaseChange f hf v d hd).map F
    have hv : IsPullback (familyPullbackMap Q a v).left
        (familyPullbackBase Q (v ≫ a)).left b.left v.left :=
      (familyBaseChange Q a v).map F
    let E' := F.mapIso E
    have hv' : IsPullback (familyPullbackMap Q a v).left
        ((familyPullbackBase Q (v ≫ a)).left ≫ E'.hom) b.left (𝒰.f i) :=
      hv.of_iso (Iso.refl _) (Iso.refl _) E' (Iso.refl _) (by simp) (by simp)
        (by simp) (by change (E.hom.left ≫ 𝒰.f i) ≫ 𝟙 _ = E.hom.left ≫ 𝒰.f i; simp)
    change IsIso (pullback.snd f.left (pullback.fst b.left (𝒰.f i)))
    have : IsIso (F.map d) := hdIso
    exact isIso_of_pullback_base hv' (IsPullback.of_hasPullback _ _) hq
      (IsPullback.of_hasPullback _ _)
  have : IsIso (F.map f) := hIso
  have : IsIso f := isIso_of_reflects_iso f F
  exact ⟨asIso f, hf⟩


private theorem overEpi_of_flat_surjective {Y X : SchemeOver k} (p : Y ⟶ X)
    [Flat p.left] [Surjective p.left] : Epi p :=
  (Over.forget _).epi_of_epi_map (f := p) (Flat.epi_of_flat_of_surjective p.left)

private theorem quotientAction_exists {P : ClosedSubgroup G}
    (D : Specs.QuotientEmbedding.Presentation P)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection) :
    ∃ a : G.X ⊗ D.scheme ⟶ D.scheme,
      ∀ (U : SchemeOver k) (g h : U ⟶ G.X), lift g (h ≫ D.projection) ≫ a =
        (g * h) ≫ D.projection := by
  let q := D.projection
  let p := G.X ◁ q
  let m := μ[G.X] ≫ q
  have sq := (tensorPullback G.X q).map (Over.forget (Spec (CommRingCat.of k)))
  have : Flat p.left := MorphismProperty.of_isPullback sq.flip D.flat
  have : Surjective p.left := MorphismProperty.of_isPullback sq.flip D.surjective
  have : LocallyOfFinitePresentation p.left :=
    MorphismProperty.of_isPullback sq.flip D.finitePresentation
  have : EffectiveEpi p.left := inferInstance
  obtain ⟨a, ha⟩ := exists_over_desc p m (fun V b c eq ↦ by
    have h₁ : b ≫ fst G.X G.X = c ≫ fst G.X G.X := by
      simpa [p] using congrArg (· ≫ fst G.X D.scheme) eq
    have h₂ : (b ≫ snd G.X G.X) ≫ q = (c ≫ snd G.X G.X) ≫ q := by
      simpa [p] using congrArg (· ≫ snd G.X D.scheme) eq
    have hp := (quotient_eq_iff D hD _ _).mp h₂
    change b ≫ μ[G.X] ≫ q = c ≫ μ[G.X] ≫ q
    have mul_proj (e : V ⟶ G.X ⊗ G.X) :
        e ≫ μ[G.X] = (e ≫ fst G.X G.X) * (e ≫ snd G.X G.X) := by
      rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
    rw [← Category.assoc, ← Category.assoc c, mul_proj, mul_proj, h₁, quotient_eq_iff D hD]
    obtain ⟨w, hw⟩ := hp
    refine ⟨w, hw.trans ?_⟩
    group)
  refine ⟨a, fun V g h ↦ ?_⟩
  have eq : lift g (h ≫ q) = lift g h ≫ p := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [p]
  rw [eq, Category.assoc, ha]
  rfl

private theorem quotientSeparated {P : ClosedSubgroup G}
    (D : Specs.QuotientEmbedding.Presentation P) : IsSeparated D.scheme.hom := by
  obtain ⟨V, _, _, _, j, hj⟩ := D.quasiProjective
  let X := Specs.ProjectiveSpaces.projectiveSpace k V
  have hX : IsSeparated X.hom := by
    let idx := ULift.{u} (Fin (Module.finrank k V))
    change IsSeparated (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule idx k) ≫
      Spec.map (CommRingCat.ofHom (Specs.ProjectiveSpaces.constants k idx)))
    infer_instance
  have hj' : IsSeparated j.left := inferInstance
  rw [← Over.w j]
  exact MorphismProperty.comp_mem _ _ _ hj' hX

private theorem quotientQuasiCompact (H : AffineAlgebraicGroup k) {P : ClosedSubgroup H.val}
    (D : Specs.QuotientEmbedding.Presentation P) : QuasiCompact D.projection.left := by
  have : IsSeparated D.scheme.hom := quotientSeparated D
  have : QuasiCompact (D.projection.left ≫ D.scheme.hom) := Over.w D.projection ▸ H.property.2.2
  exact QuasiCompact.of_comp D.projection.left D.scheme.hom

private theorem fixes_iff_conjugate {P : ClosedSubgroup G}
    (D : Specs.QuotientEmbedding.Presentation P)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection)
    {s : G.X ⊗ D.scheme ⟶ D.scheme}
    (hs : ∀ (U : SchemeOver k) (g h : U ⟶ G.X),
      lift g (h ≫ D.projection) ≫ s = (g * h) ≫ D.projection)
    {w : U ⟶ D.scheme} {g : U ⟶ G.X} (hg : g ≫ D.projection = w)
    (z : U ⟶ G.X) :
    lift z w ≫ s = w ↔ ∃ p : U ⟶ P.group.X,
        g * (p ≫ P.inclusion.hom.hom) * g⁻¹ = z := by
  rw [← hg, hs, eq_comm, quotient_eq_iff D hD]
  apply exists_congr
  intro p
  constructor
  · intro h
    rw [h]
    group
  · intro h
    rw [← h]
    group

private abbrev overBase (T : SchemeOver k) (A : Over T.left) : (Over.map T.hom).obj A ⟶ T :=
  Over.homMk A.hom

private def relativePoint {A : Over T.left} {X : SchemeOver k}
    (p : A ⟶ (Over.pullback T.hom).obj X) : (Over.map T.hom).obj A ⟶ X :=
  ((Over.mapPullbackAdj T.hom).homEquiv A X).symm p

private theorem relativePoint_left {A : Over T.left} {X : SchemeOver k}
    (p : A ⟶ (Over.pullback T.hom).obj X) :
    (relativePoint p).left = p.left ≫ pullback.fst X.hom T.hom := rfl

private theorem relativePoint_natural {A : Over T.left} {X Y : SchemeOver k}
    (p : A ⟶ (Over.pullback T.hom).obj X) (f : X ⟶ Y) :
    relativePoint (p ≫ (Over.pullback T.hom).map f) = relativePoint p ≫ f := by
  apply Over.OverMorphism.ext
  simp only [relativePoint_left, Over.comp_left, Category.assoc, Over.pullback_map_left,
    pullback.lift_fst]

private theorem relativePoint_comp {A B : Over T.left} {X : SchemeOver k}
    (p : A ⟶ B) (z : B ⟶ (Over.pullback T.hom).obj X) :
    relativePoint (p ≫ z) = (Over.map T.hom).map p ≫ relativePoint z := by
  apply Over.OverMorphism.ext
  simp [relativePoint_left, Category.assoc]

private theorem relativePoint_mul {A : Over T.left}
    (p q : A ⟶ (relativeGroup G T).X) :
    relativePoint (p * q) = relativePoint p * relativePoint q := by
  let F := Over.pullback T.hom
  let t : A ⟶ F.obj (G.X ⊗ G.X) := lift p q ≫ Functor.LaxMonoidal.μ F G.X G.X
  have ht : relativePoint t = lift (relativePoint p) (relativePoint q) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← relativePoint_natural t (fst G.X G.X), lift_fst]
      change relativePoint ((lift p q ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map _) = _
      rw [Category.assoc, Functor.Monoidal.μ_fst]
      exact congrArg relativePoint (lift_fst (f := p) (g := q))
    · rw [← relativePoint_natural t (snd G.X G.X), lift_snd]
      change relativePoint ((lift p q ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map _) = _
      rw [Category.assoc, Functor.Monoidal.μ_snd]
      exact congrArg relativePoint (lift_snd (f := p) (g := q))
  change relativePoint (lift p q ≫
    (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X])) =
      lift (relativePoint p) (relativePoint q) ≫ μ[G.X]
  rw [← Category.assoc]
  change relativePoint (t ≫ (Over.pullback T.hom).map μ[G.X]) = _
  rw [relativePoint_natural, ht]

private def relativePointHom (A : Over T.left) :
    (A ⟶ (relativeGroup G T).X) →* ((Over.map T.hom).obj A ⟶ G.X) :=
  { toFun := relativePoint
    map_one' := by
      have h := (relativePoint_mul (1 : A ⟶ (relativeGroup G T).X) 1).symm
      rw [one_mul] at h
      exact (mul_eq_right.mp h)
    map_mul' := relativePoint_mul }

private theorem groupOnLocus {C : Type (u + 1)} [Category.{u} C]
    [CartesianMonoidalCategory C] {Z H : C} [GrpObj H] (j : Z ⟶ H) [Mono j]
    (S : ∀ V : C, Subgroup (V ⟶ H))
    (hS : ∀ (V : C) (z : V ⟶ H), (∃ a : V ⟶ Z, a ≫ j = z) ↔ z ∈ S V) :
    ∃ grp : GrpObj Z, letI := grp; IsMonHom j := by
  obtain ⟨e, he⟩ := (hS _ _).mpr ((S (𝟙_ C)).one_mem)
  have hm₁ : fst Z Z ≫ j ∈ S (Z ⊗ Z) := (hS _ _).mp ⟨fst Z Z, rfl⟩
  have hm₂ : snd Z Z ≫ j ∈ S (Z ⊗ Z) := (hS _ _).mp ⟨snd Z Z, rfl⟩
  obtain ⟨m, hm⟩ := (hS _ _).mpr ((S _).mul_mem hm₁ hm₂)
  obtain ⟨i, hi⟩ := (hS _ _).mpr ((S _).inv_mem ((hS _ _).mp ⟨𝟙 Z, Category.id_comp _⟩))
  have unit : e ≫ j = η[H] := by rw [he, MonObj.one_eq_one]
  have mul (V : C) (a b : V ⟶ Z) : lift a b ≫ m ≫ j = (a ≫ j) * (b ≫ j) := by
    rw [hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have left_one : e ▷ Z ≫ m = (λ_ Z).hom := by
    apply (cancel_mono j).mp
    rw [Category.assoc]
    have eq : e ▷ Z = lift (toUnit _ ≫ e) (λ_ Z).hom := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [toUnit_unique (fst (𝟙_ C) Z) (toUnit (𝟙_ C ⊗ Z))]
      · simp [leftUnitor_hom]
    rw [eq, mul]
    simp [unit, Hom.one_def]
  have right_one : Z ◁ e ≫ m = (ρ_ Z).hom := by
    apply (cancel_mono j).mp
    rw [Category.assoc]
    have eq : Z ◁ e = lift (ρ_ Z).hom (toUnit _ ≫ e) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [rightUnitor_hom]
      · simp [toUnit_unique (snd Z (𝟙_ C)) (toUnit (Z ⊗ 𝟙_ C))]
    rw [eq, mul]
    simp [unit, Hom.one_def]
  have assoc : (m ▷ Z) ≫ m = (α_ Z Z Z).hom ≫ (Z ◁ m) ≫ m := by
    apply (cancel_mono j).mp
    let a := fst (Z ⊗ Z) Z ≫ fst Z Z
    let b := fst (Z ⊗ Z) Z ≫ snd Z Z
    let c := snd (Z ⊗ Z) Z
    have hl : m ▷ Z = lift (lift a b ≫ m) c := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [a, b, c, ← comp_lift]
    have hr : (α_ Z Z Z).hom ≫ (Z ◁ m) = lift a (lift b c ≫ m) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [a]
      · have hs : (α_ Z Z Z).hom ≫ snd Z (Z ⊗ Z) = lift b c := by
          apply CartesianMonoidalCategory.hom_ext <;> simp [b, c]
        simp only [Category.assoc, whiskerLeft_snd, lift_snd, ← Category.assoc _ _ m, hs]
    simp only [Category.assoc]
    rw [← Category.assoc (α_ Z Z Z).hom (Z ◁ m), hl, hr, mul, mul]
    simp only [Category.assoc, mul, mul_assoc]
  have inv_left : lift i (𝟙 Z) ≫ m = toUnit Z ≫ e := by
    apply (cancel_mono j).mp
    simp [mul, hi, he, MonObj.comp_one]
  have inv_right : lift (𝟙 Z) i ≫ m = toUnit Z ≫ e := by
    apply (cancel_mono j).mp
    simp [mul, hi, he, MonObj.comp_one]
  let grp : GrpObj Z :=
    { one := e
      mul := m
      one_mul := left_one
      mul_one := right_one
      mul_assoc := assoc
      inv := i
      left_inv := inv_left
      right_inv := inv_right }
  refine ⟨grp, ?_⟩
  let := grp
  exact ⟨unit, by
    change m ≫ j = _
    rw [hm, Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]⟩

private theorem relativeFamilyAmbient {Z : Over T.left}
    (j : Z ⟶ (relativeGroup G T).X) :
    ∃ q : (Over.map T.hom).obj Z ⟶ G.X ⊗ T, q.left = j.left ∧
      ∀ (A : Over T.left) (m : A ⟶ Z),
        (Over.map T.hom).map m ≫ q =
          lift (relativePoint (m ≫ j)) (overBase T A) := by
  let q : (Over.map T.hom).obj Z ⟶ G.X ⊗ T := lift (relativePoint j) (overBase T Z)
  have hq : q.left = j.left := by
    apply pullback.hom_ext
    · exact congrArg (fun f : (Over.map T.hom).obj Z ⟶ G.X ↦ f.left)
        (lift_fst (f := relativePoint j) (g := overBase T Z))
    · exact (congrArg (fun f : (Over.map T.hom).obj Z ⟶ T ↦ f.left)
          (lift_snd (f := relativePoint j) (g := overBase T Z))).trans (Over.w j).symm
  refine ⟨q, hq, fun A m ↦ ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · simp [q, relativePoint_comp]
  · have hb : (Over.map T.hom).map m ≫ overBase T Z = overBase T A :=
      Over.OverMorphism.ext (Over.w m)
    simp [q, hb]

private theorem factors_relative_iff {Z : Over T.left} (j : Z ⟶ (relativeGroup G T).X)
    {q : (Over.map T.hom).obj Z ⟶ G.X ⊗ T} (hq : q.left = j.left)
    {A : Over T.left} (p : A ⟶ (relativeGroup G T).X) :
    (∃ f : A ⟶ Z, f ≫ j = p) ↔
      ∃ f : (Over.map T.hom).obj A ⟶ (Over.map T.hom).obj Z,
        f ≫ q = lift (relativePoint p) (overBase T A) := by
  have hp : (lift (relativePoint p) (overBase T A)).left = p.left := by
    obtain ⟨w, hw, h⟩ := relativeFamilyAmbient p
    simpa [hw] using congrArg (·.left) (h A (𝟙 _)).symm
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(Over.map T.hom).map f, Over.OverMorphism.ext ?_⟩
    change f.left ≫ q.left = _
    rw [hp, hq]
    exact congrArg (·.left) hf
  · rintro ⟨f, hf⟩
    have hf' : f.left ≫ j.left = p.left := by
      have eq := congrArg (·.left) hf
      simpa only [Over.comp_left, hp, hq] using eq
    let f' : A ⟶ Z := Over.homMk f.left (by
      rw [← Over.w j, ← Category.assoc, hf', Over.w p])
    exact ⟨f', Over.OverMorphism.ext hf'⟩

private theorem fixesSubgroup {P : ClosedSubgroup G}
    (D : Specs.QuotientEmbedding.Presentation P)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection)
    {s : G.X ⊗ D.scheme ⟶ D.scheme}
    (hs : ∀ (U : SchemeOver k) (g h : U ⟶ G.X),
      lift g (h ≫ D.projection) ≫ s = (g * h) ≫ D.projection)
    (w : U ⟶ D.scheme) :
    ∃ S : Subgroup (U ⟶ G.X), ∀ z, z ∈ S ↔ lift z w ≫ s = w := by
  let V := pullback w D.projection
  let p : V ⟶ U := pullback.fst w D.projection
  let g : V ⟶ G.X := pullback.snd w D.projection
  have hpg : g ≫ D.projection = p ≫ w := pullback.condition.symm
  have sq := (IsPullback.of_hasPullback w D.projection).map (Over.forget (Spec (CommRingCat.of k)))
  have : Flat p.left := MorphismProperty.of_isPullback sq.flip D.flat
  have : Surjective p.left := MorphismProperty.of_isPullback sq.flip D.surjective
  have : Epi p := overEpi_of_flat_surjective p
  let comp : (U ⟶ G.X) →* (V ⟶ G.X) :=
    { toFun := fun z ↦ p ≫ z
      map_one' := MonObj.comp_one p
      map_mul' := MonObj.comp_mul p }
  let C : Subgroup (V ⟶ G.X) :=
    (SubgroupSections P V).map (MulAut.conj g).toMonoidHom
  refine ⟨C.comap comp, fun z ↦ ?_⟩
  have he : ((p ≫ z) ∈ C) ↔ lift (p ≫ z) (p ≫ w) ≫ s = p ≫ w := by
    rw [fixes_iff_conjugate D hD hs hpg]
    change (∃ q ∈ SubgroupSections P V, (MulAut.conj g) q = p ≫ z) ↔ _
    constructor
    · rintro ⟨q, ⟨x, rfl⟩, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x ≫ P.inclusion.hom.hom, ⟨x, rfl⟩, hx⟩
  change (p ≫ z) ∈ C ↔ _
  rw [he, ← comp_lift, Category.assoc]
  exact cancel_epi p

private theorem relativeClosedLocus (Z : SchemeOver k) (j : Z ⟶ G.X ⊗ T)
    (hj : IsClosedImmersion j.left)
    (hsub : ∀ (U : SchemeOver k) (a : U ⟶ T),
      ∃ S : Subgroup (U ⟶ G.X), ∀ z, z ∈ S ↔
        ∃ y : U ⟶ Z, y ≫ j = lift z a) :
    ∃ (H : Grp (Over T.left)) (i : H ⟶ relativeGroup G T)
      (e : (Over.map T.hom).obj H.X ≅ Z),
      i.hom.hom.left = e.hom.left ≫ j.left ∧
        H.X.hom = e.hom.left ≫ (j ≫ snd _ _).left := by
  classical
  let W : Over T.left := Over.mk ((j ≫ snd G.X T).left)
  let i : W ⟶ (relativeGroup G T).X := Over.homMk j.left
  have : Mono i := Over.mono_of_mono_left i
  let e : (Over.map T.hom).obj W ≅ Z := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Z.hom = (j ≫ snd G.X T).left ≫ T.hom
    rw [Category.id_comp, Over.w])
  have ei : i.left = e.hom.left ≫ j.left := (Category.id_comp _).symm
  have ew : W.hom = e.hom.left ≫ (j ≫ snd _ _).left := (Category.id_comp _).symm
  let M := Over.map T.hom
  let S (A : Over T.left) := (hsub (M.obj A) (overBase T A)).choose.comap
    (relativePointHom (G := G) A)
  have hmem (A : Over T.left) (z : A ⟶ (relativeGroup G T).X) : z ∈ S A ↔
      ∃ f : M.obj A ⟶ Z, f ≫ j = lift (relativePoint z) (overBase T A) :=
    (hsub (M.obj A) (overBase T A)).choose_spec _
  have hS (A : Over T.left) (z : A ⟶ (relativeGroup G T).X) :
      (∃ y : A ⟶ W, y ≫ i = z) ↔ z ∈ S A := by
    rw [hmem]
    have eq := factors_relative_iff i (q := e.hom ≫ j) ei.symm z
    constructor
    · intro he
      obtain ⟨f, hf⟩ := eq.mp he
      exact ⟨f ≫ e.hom, by simpa only [Category.assoc] using hf⟩
    · rintro ⟨f, hf⟩
      exact eq.mpr ⟨f ≫ e.inv, by simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hf⟩
  obtain ⟨grp, hgrp⟩ := groupOnLocus i S hS
  let := grp
  let J := Grp.mk W
  let inc : J ⟶ relativeGroup G T := Grp.homMk'' i hgrp.one_hom hgrp.mul_hom
  exact ⟨J, inc, e, ei, ew⟩

private theorem isoOfSubschemeFactorizations {A B X : SchemeOver k}
    (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g]
    (hg : ∃ a : A ⟶ B, a ≫ g = f) (hf : ∃ b : B ⟶ A, b ≫ f = g) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb⟩ := hf
  refine ⟨⟨a, b, (cancel_mono f).mp ?_, (cancel_mono g).mp ?_⟩, ha⟩
  · rw [Category.assoc, hb, ha, Category.id_comp]
  · rw [Category.assoc, ha, hb, Category.id_comp]

private theorem stabilizer_locus_on_lift {P : ClosedSubgroup G}
    (D : Specs.QuotientEmbedding.Presentation P)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection)
    {s : G.X ⊗ D.scheme ⟶ D.scheme}
    (hs : ∀ (U : SchemeOver k) (g h : U ⟶ G.X),
      lift g (h ≫ D.projection) ≫ s = (g * h) ≫ D.projection)
    (x : T ⟶ D.scheme) {Z : SchemeOver k} (j : Z ⟶ G.X ⊗ T) [Mono j]
    (h : ∀ (V : SchemeOver k) (a : V ⟶ T) (z : V ⟶ G.X),
      (∃ y : V ⟶ Z, y ≫ j = lift z a) ↔ lift z (a ≫ x) ≫ s = a ≫ x)
    {a : U ⟶ T} {g : U ⟶ G.X} (hg : g ≫ D.projection = a ≫ x) :
    ∃ e : P.group.X ⊗ U ≅ pullback j (G.X ◁ a),
      e.hom ≫ pullback.snd _ _ = conjugateInclusion P g := by
  let f := conjugateInclusion P g
  let b := G.X ◁ a
  let c := pullback.snd j b
  have hf : IsClosedImmersion f.left := conjugateInclusion_closed P g
  have : Mono f := Over.mono_of_mono_left f
  have aux (V : SchemeOver k) (v : V ⟶ G.X ⊗ U) :
      (∃ y, y ≫ c = v) ↔ ∃ y, y ≫ f = v := by
    have comp_eq : v ≫ b = lift (v ≫ fst G.X U) (v ≫ snd G.X U ≫ a) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [b]
    have hpb : (∃ y, y ≫ c = v) ↔ ∃ y, y ≫ j = v ≫ b := by
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y ≫ pullback.fst j b, by rw [Category.assoc, pullback.condition, ← Category.assoc, ← hy]⟩
      · rintro ⟨y, hy⟩
        exact ⟨pullback.lift y v hy, pullback.lift_snd _ _ _⟩
    rw [hpb, comp_eq, h]
    have hgv : (v ≫ snd G.X U ≫ g) ≫ D.projection = (v ≫ snd G.X U ≫ a) ≫ x := by
      simp only [Category.assoc, hg]
    rw [fixes_iff_conjugate D hD hs hgv]
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨lift p (v ≫ snd _ _), ?_⟩
      change lift p (v ≫ snd _ _) ≫ conjugateInclusion P g = v
      rw [comp_conjugateInclusion]
      simp only [Category.assoc] at hp ⊢
      rw [hp, lift_comp_fst_snd]
    · rintro ⟨y, hy⟩
      have eq : y ≫ snd P.group.X U = v ≫ snd G.X U := by
        simpa [f, conjugateInclusion] using congrArg (· ≫ snd G.X U) hy
      refine ⟨y ≫ fst _ _, ?_⟩
      have he : y ≫ f = lift (y ≫ fst _ _) (y ≫ snd _ _) ≫ conjugateInclusion P g := by
        rw [lift_comp_fst_snd]
      rw [he, comp_conjugateInclusion, eq] at hy
      simpa only [Category.assoc, lift_fst] using congrArg (· ≫ fst G.X U) hy
  exact isoOfSubschemeFactorizations f c
    ((aux _ f).mpr ⟨𝟙 _, Category.id_comp _⟩) ((aux _ c).mp ⟨𝟙 _, Category.id_comp _⟩)

private theorem stabilizer_locus_smooth (H : AffineAlgebraicGroup k) {P : ClosedSubgroup H.val}
    (D : Specs.QuotientEmbedding.Presentation P) (hP : Smooth P.group.X.hom)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection)
    {s : H.val.X ⊗ D.scheme ⟶ D.scheme}
    (hs : ∀ (U : SchemeOver k) (g h : U ⟶ H.val.X),
      lift g (h ≫ D.projection) ≫ s = (g * h) ≫ D.projection)
    (x : T ⟶ D.scheme) {Z : SchemeOver k} (j : Z ⟶ H.val.X ⊗ T) [Mono j]
    (h : ∀ (V : SchemeOver k) (a : V ⟶ T) (z : V ⟶ H.val.X),
      (∃ y : V ⟶ Z, y ≫ j = lift z a) ↔ lift z (a ≫ x) ≫ s = a ≫ x) :
    Smooth (j ≫ snd _ _).left := by
  let W := pullback x D.projection
  let p : W ⟶ T := pullback.fst x D.projection
  let g : W ⟶ H.val.X := pullback.snd x D.projection
  let F := Over.forget (Spec (CommRingCat.of k))
  have hg : g ≫ D.projection = p ≫ x := pullback.condition.symm
  obtain ⟨e, he⟩ := stabilizer_locus_on_lift D hD hs x j h hg
  let b := H.val.X ◁ p
  let f := pullback.snd j b ≫ snd H.val.X W
  have hsq : IsPullback (pullback.fst j b).left f.left (j ≫ snd _ _).left p.left :=
    ((IsPullback.of_hasPullback j b).paste_vert (tensorPullback H.val.X p)).map F
  have hf : Smooth f.left := by
    have eq : e.hom ≫ f = snd P.group.X W := by
      change e.hom ≫ pullback.snd j b ≫ snd _ _ = _
      rw [← Category.assoc, he]
      simp [conjugateInclusion]
    have hi : IsIso e.hom.left := (F.mapIso e).isIso_hom
    have hp : Smooth (snd P.group.X W).left :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback P.group.X.hom W.hom) hP
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) ..).mp
      (show Smooth (e.hom ≫ f).left from (congrArg (·.left) eq).symm ▸ hp)
  have sq := (IsPullback.of_hasPullback x D.projection).map F
  have hcover : (Surjective p.left ∧ Flat p.left) ∧ QuasiCompact p.left :=
    ⟨⟨MorphismProperty.of_isPullback sq.flip D.surjective,
      MorphismProperty.of_isPullback sq.flip D.flat⟩,
      MorphismProperty.of_isPullback sq.flip (quotientQuasiCompact H D)⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq.flip hcover hf

private theorem factors_locally {V W Z X : SchemeOver k} (p : W ⟶ V)
    [EffectiveEpi p.left] (j : Z ⟶ X) [Mono j] {x : V ⟶ X} :
    (∃ y : W ⟶ Z, y ≫ j = p ≫ x) ↔ ∃ z : V ⟶ Z, z ≫ j = x := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := exists_over_desc p y (fun A a b eq ↦ (cancel_mono j).mp (by
      simp only [Category.assoc, hy, reassoc_of% eq]))
    have : Epi p := (Over.forget _).epi_of_epi_map (f := p) (inferInstanceAs (Epi p.left))
    exact ⟨z, (cancel_epi p).mp (by rw [← Category.assoc, hz, hy])⟩
  · rintro ⟨z, hz⟩
    exact ⟨p ≫ z, by rw [Category.assoc, hz]⟩

private theorem existsFamily_of_parameter (H : AffineAlgebraicGroup k) {P : ClosedSubgroup H.val}
    (D : Specs.QuotientEmbedding.Presentation P) (hP : Smooth P.group.X.hom)
    (hD : IsPullback prod.fst (Specs.HomogeneousQuotient.rightMultiplication P)
      D.projection D.projection)
    (hN : RepresentsSubgroup P (fun _ g ↦ Normalizes P.inclusion g))
    (x : T ⟶ D.scheme) :
    ∃ Q : Family H.val T, SameGeometricType P Q ∧ Classifies D Q x := by
  obtain ⟨s, hs⟩ := quotientAction_exists D hD
  let f := lift (fst H.val.X T) (snd H.val.X T ≫ x) ≫ s
  let b := snd H.val.X T ≫ x
  let Z := equalizer f b
  let j : Z ⟶ H.val.X ⊗ T := equalizer.ι f b
  have : IsSeparated D.scheme.hom := quotientSeparated D
  have hclosed : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (equalizer.ι f b).left)
  have : Mono j := Over.mono_of_mono_left j
  have hf (V : SchemeOver k) (a : V ⟶ T) (z : V ⟶ H.val.X) :
      (∃ y : V ⟶ Z, y ≫ j = lift z a) ↔ lift z (a ≫ x) ≫ s = a ≫ x := by
    have eq : lift z a ≫ f = lift z (a ≫ x) ≫ s := by simp [f, comp_lift_assoc]
    have eb : lift z a ≫ b = a ≫ x := by simp [b]
    rw [← eq, ← eb]
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy, Category.assoc, Category.assoc, equalizer.condition]
    · intro h
      exact ⟨equalizer.lift _ h, equalizer.lift_ι _ _⟩
  have hsub (V : SchemeOver k) (a : V ⟶ T) : ∃ S : Subgroup (V ⟶ H.val.X), ∀ z,
      z ∈ S ↔ ∃ y : V ⟶ Z, y ≫ j = lift z a := by
    obtain ⟨S, hS⟩ := fixesSubgroup D hD hs (a ≫ x)
    exact ⟨S, fun z ↦ (hS z).trans (hf V a z).symm⟩
  obtain ⟨J, i, e, hi, hb⟩ := relativeClosedLocus Z j hclosed hsub
  have hE : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have hic : IsClosedImmersion i.hom.hom.left := hi.symm ▸ IsClosedImmersion.comp _ j.left
  have hz := stabilizer_locus_smooth H D hP hD hs x j hf
  have hJ : Smooth J.X.hom := hb.symm ▸ MorphismProperty.comp_mem _ _ _ inferInstance hz
  let Q : Family H.val T := ⟨J, i, hic, hJ⟩
  have eamb : Q.ambient = e.hom ≫ j := by
    exact Over.OverMorphism.ext ((familyAmbient_left Q).trans hi)
  have hQ (V : SchemeOver k) (a : V ⟶ T) (z : V ⟶ H.val.X) :
      (∃ y : V ⟶ Q.overField, y ≫ Q.ambient = lift z a) ↔ lift z (a ≫ x) ≫ s = a ≫ x := by
    rw [← hf, eamb]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y ≫ e.hom, by simpa only [Category.assoc] using hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y ≫ e.inv, by simp only [Category.assoc, Iso.inv_hom_id_assoc, hy]⟩
  have conj_of_lift {V : SchemeOver k} {a : V ⟶ T} {g : V ⟶ H.val.X}
      (h : g ≫ D.projection = a ≫ x) : Conjugates P Q a g := by
    rw [conjugates_iff_factorizations]
    intro W w z
    rw [hQ]
    apply fixes_iff_conjugate D hD hs
    simp [Category.assoc, h]
  have hx : Classifies D Q x := by
    intro V a g
    refine ⟨conj_of_lift, fun h ↦ ?_⟩
    let W := pullback (a ≫ x) D.projection
    let p : W ⟶ V := pullback.fst (a ≫ x) D.projection
    let g' : W ⟶ H.val.X := pullback.snd (a ≫ x) D.projection
    have hg' : g' ≫ D.projection = (p ≫ a) ≫ x := by
      rw [Category.assoc]
      exact pullback.condition.symm
    have nh := normalizes_of_conjugates (conj_of_lift hg') (conjugates_pullback h p)
    have eq := (quotient_eq_iff D hD g' (p ≫ g)).mpr ((hN _ _).mp nh)
    have sq := (IsPullback.of_hasPullback (a ≫ x) D.projection).map (Over.forget _)
    have : Flat p.left := MorphismProperty.of_isPullback sq.flip D.flat
    have : Surjective p.left := MorphismProperty.of_isPullback sq.flip D.surjective
    have : Epi p := overEpi_of_flat_surjective p
    exact (cancel_epi p).mp (by simpa only [hg', Category.assoc] using eq.symm)
  refine ⟨Q, ?_, hx⟩
  intro K _ _ _ a
  let V := (testSpec k).obj (op (CommAlgCat.of k K))
  let W := pullback (a ≫ x) D.projection
  let p : W ⟶ V := pullback.fst (a ≫ x) D.projection
  let g : W ⟶ H.val.X := pullback.snd (a ≫ x) D.projection
  have sq := (IsPullback.of_hasPullback (a ≫ x) D.projection).map (Over.forget _)
  have : Surjective p.left := MorphismProperty.of_isPullback sq.flip D.surjective
  have : LocallyOfFiniteType p.left := by
    let : LocallyOfFinitePresentation p.left := MorphismProperty.of_isPullback sq.flip D.finitePresentation
    infer_instance
  -- A nonempty finite-type scheme over an algebraically closed field has a rational point.
  let W' : SchemeOver K := Over.mk p.left
  have hw' : Nonempty W'.left := ⟨(Surjective.surj (f := p.left) (IsLocalRing.closedPoint K)).choose⟩
  have hft : LocallyOfFiniteType W'.hom := inferInstanceAs (LocallyOfFiniteType p.left)
  have : JacobsonSpace W'.left := LocallyOfFiniteType.jacobsonSpace W'.hom
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set W'.left)) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let w : (𝟙_ (SchemeOver K)) ⟶ W' :=
    Over.homMk (pointOfClosedPoint W'.hom y hy) (pointOfClosedPoint_comp W'.hom y hy)
  let r : V ⟶ W := Over.homMk w.left (by
    change w.left ≫ W.hom = V.hom
    rw [← Over.w p, ← Category.assoc]
    change (w.left ≫ W'.hom) ≫ V.hom = _
    rw [Over.w w]
    simp)
  have hr : r ≫ p = 𝟙 V := Over.OverMorphism.ext (Over.w w)
  refine ⟨r ≫ g, conj_of_lift ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hr, Category.id_comp]

private theorem sameFamily_of_classifies {P : ClosedSubgroup G}
    (D : Specs.QuotientEmbedding.Presentation P) {Q Q' : Family G T} {x : T ⟶ D.scheme}
    (hQ : Classifies D Q x) (hQ' : Classifies D Q' x) :
    SameFamily Q Q' := by
  let j := Q.ambient
  let j' := Q'.ambient
  have hc := familyAmbient_closed Q
  have hc' := familyAmbient_closed Q'
  have : Mono j := Over.mono_of_mono_left j
  have : Mono j' := Over.mono_of_mono_left j'
  have aux (V : SchemeOver k) (a : V ⟶ T) (z : V ⟶ G.X) :
      (∃ y : V ⟶ Q.overField, y ≫ j = lift z a) ↔
        ∃ y : V ⟶ Q'.overField, y ≫ j' = lift z a := by
    let W := pullback (a ≫ x) D.projection
    let p : W ⟶ V := pullback.fst (a ≫ x) D.projection
    let g : W ⟶ G.X := pullback.snd (a ≫ x) D.projection
    have hp : g ≫ D.projection = (p ≫ a) ≫ x := by rw [Category.assoc]; exact pullback.condition.symm
    have sq := (IsPullback.of_hasPullback (a ≫ x) D.projection).map (Over.forget _)
    have : Flat p.left := MorphismProperty.of_isPullback sq.flip D.flat
    have : Surjective p.left := MorphismProperty.of_isPullback sq.flip D.surjective
    have : LocallyOfFinitePresentation p.left := MorphismProperty.of_isPullback sq.flip D.finitePresentation
    have : EffectiveEpi p.left := inferInstance
    rw [← factors_locally p j, ← factors_locally p j', comp_lift]
    have hW := ((conjugates_iff_factorizations.mp ((hQ _ _ _).mp hp)) W (𝟙 _) (p ≫ z)).trans
      (((conjugates_iff_factorizations.mp ((hQ' _ _ _).mp hp)) W (𝟙 _) (p ≫ z)).symm)
    simpa only [Category.id_comp] using hW
  apply isoOfSubschemeFactorizations j j'
  · simpa using (aux Q.overField (j ≫ snd _ _) (j ≫ fst _ _)).mp ⟨𝟙 _, by simp⟩
  · simpa using (aux Q'.overField (j' ≫ snd _ _) (j' ≫ fst _ _)).mpr ⟨𝟙 _, by simp⟩

/-- The transporter is a surjective, finitely presented closed subscheme of the constant group. -/
theorem closedTransporter (H : AffineAlgebraicGroup k) (P : ClosedSubgroup H.val)
    (R : TestAlgebra k) (Q : Family H.val ((testSpec k).obj (op R))) (hQ : SameGeometricType P Q) :
    ∃ (Z : SchemeOver k) (j : Z ⟶ H.val.X ⊗ (testSpec k).obj (op R)),
      IsClosedImmersion j.left ∧ RepresentsTransporter P Q j ∧
        Surjective (j ≫ snd _ _).left ∧ LocallyOfFinitePresentation (j ≫ snd _ _).left ∧
        QuasiCompact (j ≫ snd _ _).left ∧ QuasiSeparated (j ≫ snd _ _).left := by
  obtain ⟨Z, j, hc, hf, hqc, hqs, hj⟩ := containmentLocus H P R Q
  refine ⟨Z, j, hc, ?_, containmentLocus_surjective P Q hQ j hj, hf, hqc, hqs⟩
  intro U a g
  exact (Iff.intro conjugateContained_of_conjugates (conjugates_of_containment H hQ)).trans
    (hj U a g)

/-- Local conjugacy via a smooth transporter, together with the parabolic
normalizer identity, identifies the quotient with families of parabolics. -/
theorem representability_of_transporter (transport : ParabolicTransporter.{u})
    (normalizer : ∀ {k : Type u} [Field k] (H : AffineAlgebraicGroup k) (P : ClosedSubgroup H.val),
      Specs.BorelProper.IsParabolic H P →
        RepresentsSubgroup P (fun _ g ↦ Normalizes P.inclusion g)) :
    ParabolicFamilyRepresentability.{u} := by
  intro k _ G P hP
  refine ⟨(HomogeneousQuotient.homogeneousQuotient k G P).1, fun D R ↦ ⟨?_, ?_⟩⟩
  · intro Q hQ
    obtain ⟨Z, j, hc, hj, _, _, _, _, _, _⟩ := transport G P hP R Q hQ
    exact uniqueFlagParameter P Q D (HomogeneousQuotient.quotientPullback D)
      (normalizer G P hP) j hc hj
  · intro x
    obtain ⟨Q, hQ, hx⟩ := existsFamily_of_parameter G D hP.2.1
      (HomogeneousQuotient.quotientPullback D) (normalizer G P hP) x
    exact ⟨Q, hQ, hx, fun Q' _ hx' ↦ sameFamily_of_classifies D hx hx'⟩

private abbrev reductionMap (B : TestAlgebra k) (I : Ideal B) :
    (testSpec k).obj (op (CommAlgCat.of k (B ⧸ I))) ⟶ (testSpec k).obj (op B) :=
  (testSpec k).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)).op

/-- The infinitesimal lifting property for conjugacies of a constant parabolic. -/
def ConjugacyLiftsAcrossSquareZero : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    Specs.BorelProper.IsParabolic G P →
    ∀ (R : TestAlgebra k) (Q : Family G.val ((testSpec k).obj (op R))),
      SameGeometricType P Q →
    ∀ (B : TestAlgebra k) (I : Ideal B), I ^ 2 = ⊥ →
      ∀ (a : (testSpec k).obj (op B) ⟶ (testSpec k).obj (op R))
        (g₀ : (testSpec k).obj (op (CommAlgCat.of k (B ⧸ I))) ⟶ G.val.X),
        Conjugates P Q (reductionMap B I ≫ a) g₀ →
        ∃ g : (testSpec k).obj (op B) ⟶ G.val.X, Conjugates P Q a g ∧
          reductionMap B I ≫ g = g₀

/-- The infinitesimal lifting property makes the closed transporter smooth. -/
theorem parabolicTransporter_of_conjugacy_lifting
    (hl : ConjugacyLiftsAcrossSquareZero.{u}) : ParabolicTransporter.{u} := by
  intro k _ G P hP R Q hQ
  obtain ⟨Z, j, hj, hrep, hsurj, hfp, hqc, hqs⟩ := closedTransporter G P R Q hQ
  let T := (testSpec k).obj (op R)
  let f := j ≫ snd G.val.X T
  have hGa : IsAffine G.val.X.left := G.property.1
  have hTa : IsAffine T.left := inferInstanceAs (IsAffine (Spec (.of R)))
  have hAa : IsAffine (G.val.X ⊗ T).left := by
    rw [Over.tensorObj_left]
    infer_instance
  have hZa : IsAffine Z.left := isAffine_of_isAffineHom j.left
  have hSm : Smooth f.left := by
    apply smooth_of_squareZeroLifting f.left
    intro B I hI b x hx
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (b ≫ T.hom)
    let : Algebra k B := φ.hom.toAlgebra
    let C : TestAlgebra k := CommAlgCat.of k B
    let V := (testSpec k).obj (op C)
    let V₀ := (testSpec k).obj (op (CommAlgCat.of k (B ⧸ I)))
    let r := reductionMap C I
    let a : V ⟶ T := Over.homMk b hφ.symm
    let x' : V₀ ⟶ Z := Over.homMk x (by
      change x ≫ Z.hom = V₀.hom
      rw [← Over.w f, ← Category.assoc, ← hx, Category.assoc, ← hφ]
      exact (Spec.map_comp φ (CommRingCat.ofHom (Ideal.Quotient.mk I))).symm)
    have hfx : x' ≫ f = r ≫ a := Over.OverMorphism.ext hx.symm
    let g₀ := x' ≫ j ≫ fst G.val.X T
    have hg₀ : Conjugates P Q (r ≫ a) g₀ := (hrep _ _ _).mpr ⟨x', by
      apply CartesianMonoidalCategory.hom_ext
      · simp [g₀, T]
      · simpa only [lift_snd, Category.assoc] using hfx⟩
    obtain ⟨g, hg, hrg⟩ := hl G P hP R Q hQ C I hI a g₀ hg₀
    obtain ⟨y, hy⟩ := (hrep _ _ _).mp hg
    have hyf : y ≫ f = a := by
      rw [← Category.assoc, hy, lift_snd]
    have hm : Mono j := Over.mono_of_mono_left j
    have hred : r ≫ y = x' := (cancel_mono j).mp (by
      rw [Category.assoc, hy, comp_lift, hrg]
      apply CartesianMonoidalCategory.hom_ext
      · simp [g₀, T]
      · simpa only [lift_snd, Category.assoc] using hfx.symm)
    exact ⟨y.left, congrArg (·.left) hyf, congrArg (·.left) hred⟩
  exact ⟨Z, j, hj, hrep, hSm, inferInstance, hsurj, hfp, hqc, hqs⟩

section SquareZero

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

private theorem extendedIdeal_squareZero (I : Ideal R) (hI : I ^ 2 = ⊥) (A : Type u)
    [CommRing A] [Algebra R A] : (I.map (algebraMap R A)) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hI, Ideal.map_bot]

private theorem bijective_of_endomorphism_eq_id_mod (I : Ideal R)
    (hI : I ^ 2 = ⊥) (f : A →ₐ[R] A)
    (h : (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))).comp f =
      Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) : Function.Bijective f := by
  let J := I.map (algebraMap R A)
  have hsq : J ^ 2 = ⊥ := extendedIdeal_squareZero I hI A
  have hf (x : A) : f x - x ∈ J := Ideal.Quotient.eq.mp (DFunLike.congr_fun h x)
  have hmul {x y : A} (hx : x ∈ J) (hy : y ∈ J) : x * y = 0 := by
    simpa [pow_two] using (hsq ▸ (show x * y ∈ J ^ 2 from
      (pow_two J).symm ▸ Ideal.mul_mem_mul hx hy) : x * y ∈ (⊥ : Ideal A))
  have hfJ (x : A) (hx : x ∈ J) : f x = x := by
    unfold J at hx
    change x ∈ Ideal.span ((algebraMap R A) '' (I : Set R)) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, _, rfl⟩ := hx
      exact f.commutes r
    | zero => exact map_zero f
    | add x y hx hy ex ey => rw [map_add, ex, ey]
    | smul a x hx ex =>
      change f (a * x) = a * x
      rw [map_mul, ex]
      apply sub_eq_zero.mp
      rw [← sub_mul]
      exact hmul (hf a) hx
  have h_inv (x : A) : f (x - (f x - x)) = x := by
    rw [map_sub, hfJ _ (hf x)]
    abel
  refine ⟨?_, fun x ↦ ⟨_, h_inv x⟩⟩
  intro x y hxy
  have hdiff : f x - x = f y - y := by
    calc
      _ = f (f x - x) := (hfJ _ (hf x)).symm
      _ = f (f y - y) := by simp only [map_sub, hxy]
      _ = _ := hfJ _ (hf y)
  exact neg_injective (by simpa only [hxy, sub_eq_add_neg, add_left_cancel_iff] using hdiff)

private theorem bijective_of_iso_mod_squareZero (I : Ideal R) (hI : I ^ 2 = ⊥)
    [Algebra.FormallySmooth R B]
    (f : A →ₐ[R] B)
    (e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[R] (B ⧸ I.map (algebraMap R B)))
    (he : (Ideal.Quotient.mkₐ R _).comp f = e.toAlgHom.comp (Ideal.Quotient.mkₐ R _)) :
    Function.Bijective f := by
  let qA := Ideal.Quotient.mkₐ R (I.map (algebraMap R A))
  let qB := Ideal.Quotient.mkₐ R (I.map (algebraMap R B))
  have hK : IsNilpotent (RingHom.ker qA.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker]
    exact extendedIdeal_squareZero I hI A
  let g := Algebra.FormallySmooth.liftOfSurjective (e.symm.toAlgHom.comp qB) qA
    Ideal.Quotient.mk_surjective hK
  have hg : qA.comp g = e.symm.toAlgHom.comp qB :=
    Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hfd : Function.Bijective (g.comp f) := by
    apply bijective_of_endomorphism_eq_id_mod I hI
    ext x
    change qA (g (f x)) = qA x
    rw [show qA (g (f x)) = e.symm (qB (f x)) from DFunLike.congr_fun hg (f x)]
    rw [show qB (f x) = e (qA x) from DFunLike.congr_fun he x]
    exact e.symm_apply_apply _
  have hgd : Function.Bijective (f.comp g) := by
    apply bijective_of_endomorphism_eq_id_mod I hI
    ext x
    change qB (f (g x)) = qB x
    rw [show qB (f (g x)) = e (qA (g x)) from DFunLike.congr_fun he (g x)]
    rw [show qA (g x) = e.symm (qB x) from DFunLike.congr_fun hg x]
    exact e.apply_symm_apply _
  exact ⟨fun a b eq ↦ hfd.injective (congrArg g eq),
    fun b ↦ let ⟨a, ha⟩ := hgd.surjective b; ⟨g a, ha⟩⟩

private abbrev quotientSpec {S : Type u} [CommRing S] (I : Ideal S) :
    Spec (CommRingCat.of (S ⧸ I)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

private def quotientScalar (I : Ideal R) (A : Type u) [CommRing A] [Algebra R A] :
    R ⧸ I →+* A ⧸ I.map (algebraMap R A) :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp (algebraMap R A)) (fun _ hr ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr))

private theorem quotientSpecPullback (I : Ideal R) (A : Type u) [CommRing A] [Algebra R A] :
    IsPullback (quotientSpec (I.map (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (quotientScalar I A))) (algebraSpecMap R A) (quotientSpec I) := by
  let a := CommRingCat.ofHom (algebraMap R A)
  let q := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let p := CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R A)))
  let b := CommRingCat.ofHom (quotientScalar I A)
  apply isPullback_SpecMap_of_isPushout a q p b
  apply IsPushout.mk'
  · ext r
    rfl
  · intro X m n h _
    ext x
    exact congrArg (fun g : CommRingCat.of A ⟶ X ↦ g x) h
  · intro X m n h
    have hz : I ≤ (RingHom.ker m.hom).comap (algebraMap R A) := by
      intro r hr
      change m (algebraMap R A r) = 0
      have e := congrArg (fun g : CommRingCat.of R ⟶ X ↦ g r) h
      change m (algebraMap R A r) = n (Ideal.Quotient.mk I r) at e
      rw [e, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
    let l := CommRingCat.ofHom (Ideal.Quotient.lift _ m.hom
      (Ideal.map_le_iff_le_comap.mpr hz))
    refine ⟨l, ?_, ?_⟩
    · ext x
      rfl
    · ext x
      exact congrArg (fun g : CommRingCat.of R ⟶ X ↦ g x) h

private def quotientAlgHom (I : Ideal R) (f : A →ₐ[R] B) :
    (A ⧸ I.map (algebraMap R A)) →ₐ[R] (B ⧸ I.map (algebraMap R B)) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp f) (by
    have hz : I ≤ (RingHom.ker ((Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp f).toRingHom).comap
        (algebraMap R A) := by
      intro x hx
      change Ideal.Quotient.mk _ (f (algebraMap R A x)) = 0
      rw [f.commutes, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hx
    exact Ideal.map_le_iff_le_comap.mpr hz)

private theorem quotientSpecMapPullback (I : Ideal R) (f : A →ₐ[R] B) :
    IsPullback (quotientSpec (I.map (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (quotientAlgHom I f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (quotientSpec (I.map (algebraMap R A))) := by
  have h₁ : Spec.map (CommRingCat.ofHom (quotientAlgHom I f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (quotientScalar I A)) =
        Spec.map (CommRingCat.ofHom (quotientScalar I B)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    change Ideal.Quotient.mk _ (f (algebraMap R A x)) = Ideal.Quotient.mk _ (algebraMap R B x)
    rw [f.commutes]
  have h₂ : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ algebraSpecMap R A =
      algebraSpecMap R B := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact f.commutes x
  apply IsPullback.of_bot (v₂₁ := Spec.map (CommRingCat.ofHom (quotientScalar I A)))
    (v₂₂ := algebraSpecMap R A) (h₃₁ := quotientSpec I)
  · rw [h₁, h₂]
    exact quotientSpecPullback I B
  · rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  · exact quotientSpecPullback I A

private def laurentConstantModIdeal (I : Ideal R) : Subalgebra R (LaurentPolynomial R) where
  carrier := {p | ∀ n : ℤ, n ≠ 0 → p.coeff n ∈ I}
  add_mem' hf hg n hn := I.add_mem (hf n hn) (hg n hn)
  mul_mem' {p q} hp hq n hn := by
    rw [AddMonoidAlgebra.coeff_mul]
    apply Ideal.sum_mem
    intro i _
    apply Ideal.sum_mem
    intro j _
    change (if i + j = n then p.coeff i * q.coeff j else 0) ∈ I
    split
    next eq =>
      by_cases hi : i = 0
      · subst i
        refine I.mul_mem_left _ (hq _ ?_)
        omega
      · exact I.mul_mem_right _ (hp _ hi)
    next => exact I.zero_mem
  algebraMap_mem' r n hn := by
    change (LaurentPolynomial.C r).coeff n ∈ I
    rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne hn]
    exact I.zero_mem

private theorem mul_coeff_zero_of_squareZero (I : Ideal R) (hI : I ^ 2 = ⊥)
    {p q : LaurentPolynomial R}
    (hp : p ∈ laurentConstantModIdeal I) (hq : q ∈ laurentConstantModIdeal I) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  classical
  have hprod {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 :=
    (Submodule.mem_bot R).mp (hI ▸ (pow_two I).symm ▸ Ideal.mul_mem_mul ha hb)
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum]
  rw [Finset.sum_eq_single (0 : ℤ)]
  · rw [Finset.sum_eq_single (0 : ℤ)]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hj
      simp [Finsupp.notMem_support_iff.mp hj]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    split
    · rename_i e
      exact hprod (hp _ hi) (hq _ (by omega))
    · rfl
  · intro hi
    simp [Finsupp.notMem_support_iff.mp hi]

/-- On Laurent polynomials constant modulo a square-zero ideal, taking the
constant coefficient is an algebra homomorphism. -/
def laurentAverage (I : Ideal R) (hI : I ^ 2 = ⊥) :
    laurentConstantModIdeal I →ₐ[R] R where
  toFun p := p.val.coeff 0
  map_one' := by
    change (1 : LaurentPolynomial R).coeff 0 = 1
    change (AddMonoidAlgebra.single 0 1 : LaurentPolynomial R).coeff 0 = 1
    simp
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' p q := mul_coeff_zero_of_squareZero I hI p.property q.property
  commutes' r := by
    change (LaurentPolynomial.C r).coeff 0 = r
    rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

private theorem smoothAffineCoordinates {S : CommRingCat.{u}} {X : Over (Spec S)}
    {A : CommAlgCat S} (e : (algSpec S).obj (op A) ≅ X) (hX : Smooth X.hom) :
    Algebra.Smooth S A := by
  have he : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have hf : Smooth (algebraSpecMap S A) := by
    rw [show algebraSpecMap S A = e.hom.left ≫ X.hom from (Over.w e.hom).symm]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hX
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hf)

private theorem smoothAffine_lift {S : CommRingCat.{u}} {X : Over (Spec S)}
    [IsAffine X.left] (hX : Smooth X.hom)
    (B : CommAlgCat S) (I : Ideal B) (hI : I ^ 2 = ⊥)
    (x : (algSpec S).obj (op (CommAlgCat.of S (B ⧸ I))) ⟶ X) :
    ∃ y : (algSpec S).obj (op B) ⟶ X,
      (algSpec S).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ S I)).op ≫ y = x := by
  let F := algSpec S
  let FF := algSpec.fullyFaithful (R := S)
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := S)).mpr (inferInstance : IsAffine X.left)
  have hs : Algebra.Smooth S A.unop := smoothAffineCoordinates e hX
  let f : A.unop →ₐ[S] (B ⧸ I) := (FF.preimage (x ≫ e.inv)).unop.hom
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.iff_comp_surjective.mp
    (inferInstance : Algebra.FormallySmooth S A.unop) I hI f
  refine ⟨F.map (CommAlgCat.ofHom g).op ≫ e.hom, ?_⟩
  have eq : (CommAlgCat.ofHom g) ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ S I) =
      (FF.preimage (x ≫ e.inv)).unop := CommAlgCat.hom_ext hg
  have eq' : (CommAlgCat.ofHom (Ideal.Quotient.mkₐ S I)).op ≫ (CommAlgCat.ofHom g).op =
      FF.preimage (x ≫ e.inv) := Quiver.Hom.unop_inj eq
  rw [← Category.assoc, ← F.map_comp, eq', FF.map_preimage, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem quotientSpec_surjective_of_squareZero {S : Type u} [CommRing S]
    (I : Ideal S) (hI : I ^ 2 = ⊥) : Surjective (quotientSpec I) := by
  have hnil : I ≤ nilradical S := by
    intro x hx
    refine ⟨2, ?_⟩
    have hmem : x ^ 2 ∈ I ^ 2 := (pow_two I).symm ▸ (pow_two x).symm ▸ Ideal.mul_mem_mul hx hx
    rw [hI] at hmem
    exact (Submodule.mem_bot S).mp hmem
  exact ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hnil).surjective⟩

/-- A morphism between affine schemes over an affine base is invertible when
its source is smooth and its restriction to a square-zero quotient is invertible. -/
private theorem isIso_of_squareZero_pullback {S : CommRingCat.{u}} {X Y : Over (Spec S)}
    [IsAffine X.left] [IsAffine Y.left] (hX : Smooth X.hom) (f : X ⟶ Y)
    (I : Ideal S) (hI : I ^ 2 = ⊥)
    (hmod : ∀ {V W : Scheme.{u}} (v : W ⟶ Y.left) (w : W ⟶ Spec (.of (S ⧸ I)))
      (p : V ⟶ X.left) (q : V ⟶ W),
      IsPullback v w Y.hom (quotientSpec I) → IsPullback p q f.left v → IsIso q) :
    IsIso f.left := by
  let FF := algSpec.fullyFaithful (R := S)
  obtain ⟨B, ⟨eX⟩⟩ := (essImage_algSpec (R := S)).mpr (inferInstance : IsAffine X.left)
  obtain ⟨A, ⟨eY⟩⟩ := (essImage_algSpec (R := S)).mpr (inferInstance : IsAffine Y.left)
  have heX : IsIso eX.hom.left := ((Over.forget _).mapIso eX).isIso_hom
  have heY : IsIso eY.hom.left := ((Over.forget _).mapIso eY).isIso_hom
  have hs : Algebra.Smooth S B.unop := smoothAffineCoordinates eX hX
  let φ : A.unop →ₐ[S] B.unop := (FF.preimage (eX.hom ≫ f ≫ eY.inv)).unop.hom
  let d := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hd : d = (eX.hom ≫ f ≫ eY.inv).left :=
    congrArg (·.left) (FF.map_preimage (eX.hom ≫ f ≫ eY.inv))
  have he : d ≫ eY.hom.left = eX.hom.left ≫ f.left := by
    rw [hd, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    change eX.hom.left ≫ f.left ≫ ((Over.forget _).mapIso eY).inv ≫
      ((Over.forget _).mapIso eY).hom = _
    simp
  let p := quotientSpec (I.map (algebraMap S B.unop))
  let v := quotientSpec (I.map (algebraMap S A.unop))
  let w := Spec.map (CommRingCat.ofHom (quotientScalar I A.unop))
  let q := Spec.map (CommRingCat.ofHom (quotientAlgHom I φ).toRingHom)
  have hYsq : IsPullback (v ≫ eY.hom.left) w Y.hom (quotientSpec I) :=
    (quotientSpecPullback I A.unop).of_iso (Iso.refl _) ((Over.forget _).mapIso eY)
      (Iso.refl _) (Iso.refl _) (by simp [v]) (by simp [w])
      (by exact (Over.w eY.hom).symm) (by simp)
  have hq : IsPullback (p ≫ eX.hom.left) q f.left (v ≫ eY.hom.left) :=
    (quotientSpecMapPullback I φ).of_iso (Iso.refl _) ((Over.forget _).mapIso eX)
      (Iso.refl _) ((Over.forget _).mapIso eY) (by simp [p]) (by simp [q]) (by exact he) (by simp [v])
  have hi := hmod _ _ _ _ hYsq hq
  let r0 := CommRingCat.ofHom (quotientAlgHom I φ).toRingHom
  have : IsIso (Scheme.Spec.map r0.op) := hi
  have : IsIso r0.op := isIso_of_reflects_iso r0.op Scheme.Spec
  have : IsIso r0 := isIso_of_op r0
  let e := AlgEquiv.ofBijective (quotientAlgHom I φ) (ConcreteCategory.bijective_of_isIso r0)
  have hφ := bijective_of_iso_mod_squareZero I hI φ e (by ext x; rfl)
  let r := CommRingCat.ofHom φ.toRingHom
  have : IsIso r := (RingEquiv.ofBijective φ.toRingHom hφ).toCommRingCatIso.isIso_hom
  have : IsIso r.op := isIso_op r
  have hdIso : IsIso d := Scheme.Spec.map_isIso r.op
  have : IsIso (eX.hom.left ≫ f.left) := he ▸ IsIso.comp_isIso' hdIso heY
  exact IsIso.of_isIso_comp_left eX.hom.left f.left

end SquareZero


section OpenProduct

variable {P N : ClosedSubgroup G} {B : TestAlgebra k}

private abbrev cellMultiplication (N P : ClosedSubgroup G) :
    N.group.X ⊗ P.group.X ⟶ G.X :=
  (fst _ _ ≫ N.inclusion.hom.hom) * (snd _ _ ≫ P.inclusion.hom.hom)

/-- In an open product of an opposite subgroup and a constant subgroup, a smooth
deformation with constant square-zero reduction is a graph over the constant factor. -/
private theorem deformation_is_graph
    (hG : IsAffine G.X.left) (hm : IsOpenImmersion (cellMultiplication N P).left)
    (I : Ideal B) (hI : I ^ 2 = ⊥)
    {X : SchemeOver k} (j : X ⟶ G.X ⊗ (testSpec k).obj (op B))
    (hclosed : IsClosedImmersion j.left) (hSmooth : Smooth (j ≫ snd _ _).left)
    (e₀ : P.group.X ⊗ (testSpec k).obj (op (CommAlgCat.of k (B ⧸ I))) ≅
      pullback j (G.X ◁ reductionMap B I))
    (he₀ : e₀.hom ≫ pullback.snd _ _ = P.inclusion.hom.hom ▷ _) :
    let U := (testSpec k).obj (op B)
    ∃ (e : X ≅ P.group.X ⊗ U) (c : P.group.X ⊗ U ⟶ N.group.X),
      e.inv ≫ j = lift ((c ≫ N.inclusion.hom.hom) *
        (fst P.group.X U ≫ P.inclusion.hom.hom)) (snd P.group.X U) ∧
        (P.group.X ◁ reductionMap B I) ≫ c = 1 := by
  let U := (testSpec k).obj (op B)
  let U₀ := (testSpec k).obj (op (CommAlgCat.of k (B ⧸ I)))
  let r := reductionMap B I
  let C := N.group.X ⊗ P.group.X
  let m := cellMultiplication N P
  let mU := m ▷ U
  let j₀ := pullback.snd j (G.X ◁ r)
  let p := pullback.fst j (G.X ◁ r)
  let F := Over.forget (Spec (CommRingCat.of k))
  have hmo : IsOpenImmersion mU.left := by
    have hs : IsPullback (m ▷ U) (fst C U) (fst G.X U) m := by
      apply IsPullback.mk'
      · simp [C]
      · intro W f g h₁ h₂
        apply CartesianMonoidalCategory.hom_ext
        · exact h₂
        · simpa using congrArg (· ≫ snd G.X U) h₁
      · intro W f g h
        refine ⟨lift g (f ≫ snd G.X U), ?_, by simp⟩
        apply CartesianMonoidalCategory.hom_ext
        · simpa using h.symm
        · simp
    exact MorphismProperty.of_isPullback (hs.map F).flip hm
  have hr : Surjective r.left := quotientSpec_surjective_of_squareZero I hI
  have hgr : Surjective (G.X ◁ r).left :=
    MorphismProperty.of_isPullback ((tensorPullback G.X r).map F).flip hr
  have hp : Surjective p.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback j (G.X ◁ r)).map F).flip hgr
  let l₀ : P.group.X ⊗ U₀ ⟶ C ⊗ U :=
    lift (lift (1 : P.group.X ⊗ U₀ ⟶ N.group.X) (fst P.group.X U₀)) (snd _ _ ≫ r)
  have heJ : (e₀.hom ≫ p) ≫ j = l₀ ≫ mU := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he₀]
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [l₀, mU, m, cellMultiplication, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, U₀, U]
  have hrange : Set.range j.left ⊆ Set.range mU.left := by
    rintro _ ⟨x, rfl⟩
    have heP : Surjective ((e₀.hom ≫ p).left) :=
      have : IsIso e₀.hom.left := (F.mapIso e₀).isIso_hom
      MorphismProperty.comp_mem _ _ _ inferInstance hp
    obtain ⟨y, hy⟩ := heP.surj x
    refine ⟨l₀.left y, ?_⟩
    have he := congrArg (fun f : P.group.X ⊗ U₀ ⟶ G.X ⊗ U ↦ f.left y) heJ
    have hy' : p.left (e₀.hom.left y) = x := by
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using hy
    calc
      mU.left (l₀.left y) = j.left (p.left (e₀.hom.left y)) := by
        simpa only [Over.comp_left, Scheme.Hom.comp_apply] using he.symm
      _ = j.left x := congrArg j.left hy'
  let liftJ : X ⟶ C ⊗ U := Over.homMk (IsOpenImmersion.lift mU.left j.left hrange) (by
    rw [← Over.w mU, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  have hlift : liftJ ≫ mU = j :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac mU.left j.left hrange)
  have hmU : Mono mU := Over.mono_of_mono_left mU
  have heLift : (e₀.hom ≫ p) ≫ liftJ = l₀ := (cancel_mono mU).mp (by
    rw [Category.assoc, hlift, heJ])
  let qX := liftJ ≫ fst C U
  let tX := liftJ ≫ snd C U
  let π := lift (qX ≫ snd N.group.X P.group.X) tX
  have ht : tX = j ≫ snd G.X U := by
    rw [← hlift, Category.assoc]
    simp [tX, mU, C]
  have hπ : π ≫ snd P.group.X U = j ≫ snd G.X U := by simp [π, ht]
  have hπ₀ : (e₀.hom ≫ p) ≫ π = P.group.X ◁ r := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, π, lift_fst]
      simpa [qX, l₀, C, U₀, U] using
        congrArg (· ≫ fst C U ≫ snd N.group.X P.group.X) heLift
    · simp only [Category.assoc, π, lift_snd, whiskerLeft_snd]
      simpa [tX, l₀, C, U₀, U] using congrArg (· ≫ snd C U) heLift
  have hOuter : IsPullback (e₀.hom ≫ p) (snd P.group.X U₀)
      (j ≫ snd G.X U) r := by
    have hs := (IsPullback.of_hasPullback j (G.X ◁ r)).paste_vert (tensorPullback G.X r)
    exact hs.of_iso e₀.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [p])
      (by
        apply (cancel_epi e₀.hom).mp
        simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, e₀.hom_inv_id_assoc]
        rw [← Category.assoc, he₀]
        simp [U₀])
      (by simp [U]) (by simp)
  have hTopsq : IsPullback (e₀.hom ≫ p) (𝟙 (P.group.X ⊗ U₀)) π (P.group.X ◁ r) := by
    apply IsPullback.of_bot (t := tensorPullback P.group.X r)
    · change IsPullback _ (_ ≫ snd P.group.X U₀) (π ≫ snd P.group.X U) r
      rw [Category.id_comp, hπ]
      exact hOuter
    · change _ = (𝟙 (P.group.X ⊗ U₀)) ≫ (P.group.X ◁ r)
      rw [Category.id_comp]
      exact hπ₀
  have hU : IsAffine U.left := inferInstanceAs (IsAffine (Spec (.of B)))
  have hGU : IsAffine (G.X ⊗ U).left := by rw [Over.tensorObj_left]; infer_instance
  have hX : IsAffine X.left := isAffine_of_isAffineHom j.left
  have hPc := P.isClosedImmersion
  have hPa : IsAffine P.group.X.left := isAffine_of_isAffineHom P.inclusion.hom.hom.left
  have hPU : IsAffine (P.group.X ⊗ U).left := by rw [Over.tensorObj_left]; infer_instance
  let VX : Over U.left := Over.mk (j ≫ snd G.X U).left
  let VY : Over U.left := Over.mk (snd P.group.X U).left
  have hVX : IsAffine VX.left := hX
  have hVY : IsAffine VY.left := hPU
  let f : VX ⟶ VY := Over.homMk π.left (congrArg (·.left) hπ)
  have hIso : IsIso π.left := by
    change IsIso f.left
    apply isIso_of_squareZero_pullback hSmooth f I hI
    intro V W v w a b hv hb
    have hs₁ : IsPullback (P.group.X ◁ r).left (snd P.group.X U₀).left
        (snd P.group.X U).left r.left := (tensorPullback P.group.X r).map F
    have hs₂ : IsPullback (e₀.hom ≫ p).left (𝟙 (P.group.X ⊗ U₀).left)
        π.left (P.group.X ◁ r).left := hTopsq.map F
    exact isIso_of_pullback_base hs₁ hv hs₂ hb
  have : IsIso (F.map π) := hIso
  have : IsIso π := isIso_of_reflects_iso π F
  let e := asIso π
  let c := e.inv ≫ qX ≫ fst N.group.X P.group.X
  have hqP : qX ≫ snd N.group.X P.group.X = π ≫ fst P.group.X U := (lift_fst ..).symm
  have hqT : tX = π ≫ snd P.group.X U := (lift_snd ..).symm
  have ec : e.inv ≫ liftJ = lift (lift c (fst P.group.X U)) (snd P.group.X U) := by
    apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simp [c, qX, Category.assoc]
      · have eq : lift (lift c (fst P.group.X U)) (snd P.group.X U) ≫ fst C U =
            lift c (fst P.group.X U) := lift_fst _ _
        rw [eq, lift_snd]
        simp only [Category.assoc]
        change e.inv ≫ (qX ≫ snd N.group.X P.group.X) = _
        rw [hqP]
        exact e.inv_hom_id_assoc _
    · rw [lift_snd]
      change e.inv ≫ tX = _
      rw [hqT]
      exact e.inv_hom_id_assoc _
  refine ⟨e, c, ?_, ?_⟩
  · rw [← hlift, ← Category.assoc, ec]
    apply CartesianMonoidalCategory.hom_ext <;> simp [mU, m, cellMultiplication, MonObj.comp_mul, U]
  · have eq : (P.group.X ◁ r) ≫ e.inv = e₀.hom ≫ p := by
      rw [← hπ₀]
      change ((e₀.hom ≫ p) ≫ e.hom) ≫ e.inv = _
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    change (P.group.X ◁ r) ≫ e.inv ≫ liftJ ≫ fst C U ≫ fst N.group.X P.group.X = _
    rw [← Category.assoc, eq, ← Category.assoc, heLift]
    simp [l₀]

variable {U X : SchemeOver k} {j : X ⟶ G.X ⊗ U}
  {c : P.group.X ⊗ U ⟶ N.group.X} {e : X ≅ P.group.X ⊗ U}

private theorem graph_factors_iff
    (he : e.inv ≫ j = lift ((c ≫ N.inclusion.hom.hom) *
      (fst P.group.X U ≫ P.inclusion.hom.hom)) (snd P.group.X U))
    {V : SchemeOver k} (a : V ⟶ U) (g : V ⟶ G.X) :
    (∃ y : V ⟶ X, y ≫ j = lift g a) ↔
      ∃ p : V ⟶ P.group.X, (lift p a ≫ c ≫ N.inclusion.hom.hom) *
        (p ≫ P.inclusion.hom.hom) = g := by
  have hcomp (p : V ⟶ P.group.X) (v : V ⟶ U) :
      lift p v ≫ e.inv ≫ j = lift ((lift p v ≫ c ≫ N.inclusion.hom.hom) *
        (p ≫ P.inclusion.hom.hom)) v := by
    rw [he, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  constructor
  · rintro ⟨y, hy⟩
    have h : y ≫ e.hom ≫ snd _ _ = a := by
      have he' := congrArg (· ≫ snd G.X U) he
      simp only [Category.assoc, lift_snd] at he'
      have hy' := congrArg (· ≫ snd G.X U) hy
      rw [← he', Iso.hom_inv_id_assoc]
      simpa only [Category.assoc, lift_snd] using hy'
    let p := y ≫ e.hom ≫ fst P.group.X U
    have el : lift p a = y ≫ e.hom := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [p]
      · simpa using h.symm
    have eq := hcomp p a
    rw [el, Category.assoc, Iso.hom_inv_id_assoc, hy] at eq
    exact ⟨p, by simpa only [lift_fst, ← el] using congrArg (· ≫ fst G.X U) eq.symm⟩
  · rintro ⟨p, hp⟩
    exact ⟨lift p a ≫ e.inv, by rw [Category.assoc, hcomp, hp]⟩

private theorem cell_factors_unique
    (hm : IsOpenImmersion (cellMultiplication N P).left)
    {V : SchemeOver k} {n n' : V ⟶ N.group.X} {p p' : V ⟶ P.group.X}
    (h : (n ≫ N.inclusion.hom.hom) * (p ≫ P.inclusion.hom.hom) =
      (n' ≫ N.inclusion.hom.hom) * (p' ≫ P.inclusion.hom.hom)) :
    n = n' ∧ p = p' := by
  have : Mono (cellMultiplication N P) := Over.mono_of_mono_left _
  have l : lift n p = lift n' p' := (cancel_mono (cellMultiplication N P)).mp (by
    simpa only [cellMultiplication, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc] using h)
  exact ⟨by simpa using congrArg (· ≫ fst _ _) l, by simpa using congrArg (· ≫ snd _ _) l⟩

end OpenProduct

section LaurentCoordinates

private def laurentPower (R : Type u) [CommRing R] :
    Multiplicative ℤ →* (LaurentPolynomial R)ˣ where
  toFun n :=
    ⟨LaurentPolynomial.T n.toAdd, LaurentPolynomial.T (-n.toAdd),
      by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
      by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩
  map_one' := Units.ext LaurentPolynomial.T_zero
  map_mul' m n := Units.ext (LaurentPolynomial.T_add m.toAdd n.toAdd)

private theorem pow_laurentVariable (R : Type u) [CommRing R] (n : ℤ) :
    ((laurentPower R (Multiplicative.ofAdd 1)) ^ n).val = LaurentPolynomial.T n := by
  rw [← map_zpow]
  have e : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    change Multiplicative.ofAdd (n • (1 : ℤ)) = _
    simp
  rw [e]
  rfl

private def laurentScale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (v : Sˣ) :
    LaurentPolynomial R →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp f)
    ((Units.map LaurentPolynomial.C.toMonoidHom v) * laurentPower S (Multiplicative.ofAdd 1))

private theorem coeff_laurentScale {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Sˣ) (p : LaurentPolynomial R) (n : ℤ) :
    (laurentScale f v p).coeff n = f (p.coeff n) * (v ^ n).val := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_mul]
  | C_mul_T d r =>
    unfold laurentScale
    rw [LaurentPolynomial.eval₂_C_mul_T, Commute.mul_zpow (Commute.all _ _), Units.val_mul,
      ← map_zpow, pow_laurentVariable]
    change (LaurentPolynomial.C (f r) * (LaurentPolynomial.C ((v ^ d).val) *
      LaurentPolynomial.T d)).coeff n = _
    rw [← mul_assoc, ← map_mul, ← LaurentPolynomial.single_eq_C_mul_T,
      ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : d = n
    · subst d
      simp
    · simp [h]

private theorem laurentScale_mem {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (v : Sˣ) (I : Ideal R) (J : Ideal S)
    (h : I ≤ J.comap f) {p : LaurentPolynomial R}
    (hp : p ∈ laurentConstantModIdeal I) : laurentScale f v p ∈ laurentConstantModIdeal J := by
  intro n hn
  rw [coeff_laurentScale]
  exact J.mul_mem_right _ (h (hp n hn))

variable {k : Type u} [Field k]

private def affinePointCoordinates {X : SchemeOver k} {A : TestAlgebra k}
    (e : (testSpec k).obj (op A) ≅ X) (R : TestAlgebra k) :
    Points X R ≃ (A →ₐ[k] R) where
  toFun x := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (x ≫ e.inv)).unop.hom
  invFun x := (testSpec k).map (CommAlgCat.ofHom x).op ≫ e.hom
  left_inv x := by
    change _ ≫ e.hom = x
    rw [show (testSpec k).map
          (CommAlgCat.ofHom
            ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (x ≫ e.inv)).unop.hom).op =
        x ≫ e.inv from (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _]
    simp
  right_inv x := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Functor.FullyFaithful.preimage_map]
    rfl

private theorem affinePointCoordinates_map {X : SchemeOver k} {A R S : TestAlgebra k}
    (e : (testSpec k).obj (op A) ≅ X) (a : R ⟶ S) (x : Points X R) :
    affinePointCoordinates e S (mapPoints a x) = a.hom.comp (affinePointCoordinates e R x) := by
  apply (affinePointCoordinates e S).symm.injective
  simp only [Equiv.symm_apply_apply]
  have h := (affinePointCoordinates e R).symm_apply_apply x
  change (testSpec k).map a.op ≫ x = _
  conv_lhs => rw [← h]
  change (testSpec k).map a.op ≫ ((testSpec k).map
    (CommAlgCat.ofHom (affinePointCoordinates e R x)).op ≫ e.hom) =
      (testSpec k).map (CommAlgCat.ofHom
        (a.hom.comp (affinePointCoordinates e R x))).op ≫ e.hom
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  rfl

private theorem affine_mapPoints_injective {X : SchemeOver k} {R S : TestAlgebra k}
    (ha : IsAffine X.left) (a : R ⟶ S) (h : Function.Injective a.hom) :
    Function.Injective (mapPoints (X := X) a) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  intro x y eq
  apply (affinePointCoordinates e R).injective
  have he := congrArg (affinePointCoordinates e S) eq
  rw [affinePointCoordinates_map, affinePointCoordinates_map] at he
  exact AlgHom.ext (fun t ↦ h (DFunLike.congr_fun he t))

end LaurentCoordinates

open CocharacterDynamics
open Specs.CharacterDescent (Cocharacter)
open Specs.AdjointRepresentation (GroupPoints)

open private cocharacterPoint_mul centralizes_onAlgebras centralizes_hasLimit opposite_point
  pointHom pointHom_injective affine_subgroup polynomialConstants polynomialConstants_laurent
  unitPointHom unitPointHom_apply evalLaurent evalLaurent_constants evalLaurent_parameter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

section ContractingGraph

variable {B : TestAlgebra k}

private theorem cocharacterPoint_centralizes (c : Cocharacter G) (R : TestAlgebra k) (s : Rˣ) :
    Centralizes c (cocharacterPoint c R s) := by
  apply (centralizes_onAlgebras c _).mpr
  intro S a t
  rw [mapPoints_cocharacterPoint]
  change cocharacterPoint c S _ * cocharacterPoint c S t =
    cocharacterPoint c S t * cocharacterPoint c S _
  rw [← cocharacterPoint_mul, ← cocharacterPoint_mul, mul_comm]

private theorem polynomial_factors_of_laurent_factors
    {H : ClosedSubgroup G} (hG : IsAffine G.X.left) {R : TestAlgebra k}
    (g : GroupPoints G (polynomialAlgebra R))
    (hg : ∃ p : GroupPoints H.group (laurentAlgebra R),
      p ≫ H.inclusion.hom.hom = mapPoints (polynomialToLaurent R) g) :
    ∃ p : GroupPoints H.group (polynomialAlgebra R), p ≫ H.inclusion.hom.hom = g := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hG
  let i := H.inclusion.hom.hom ≫ e.inv
  have hci := H.isClosedImmersion
  have he : IsIso e.inv.left := ((Over.forget _).mapIso e).isIso_inv
  have hi : IsClosedImmersion i.left := IsClosedImmersion.comp _ _
  obtain ⟨J, eJ, hJ⟩ := closedImmersion_over_affineSpec i hi
  let q := (testSpec k).map (quotientProjection J).op
  have base {S : TestAlgebra k} (f : GroupPoints G S) :
      (∃ p : GroupPoints H.group S, p ≫ H.inclusion.hom.hom = f) ↔ ∃ y, y ≫ q = f ≫ e.inv := by
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p ≫ eJ.hom, ?_⟩
      rw [Category.assoc, ← hJ, ← Category.assoc, hp]
    · rintro ⟨p, hp⟩
      refine ⟨p ≫ eJ.inv, (cancel_mono e.inv).mp ?_⟩
      change p ≫ eJ.inv ≫ i = f ≫ e.inv
      rw [hJ, Iso.inv_hom_id_assoc]
      exact hp
  rw [base] at hg ⊢
  dsimp only [q] at hg ⊢
  have hk := (factorsThrough_affineQuotient (B := laurentAlgebra R) J
    (mapPoints (polynomialToLaurent R) g ≫ e.inv)).mp hg
  apply (factorsThrough_affineQuotient (B := polynomialAlgebra R) J (g ≫ e.inv)).mpr
  let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
  have eg : mapPoints (polynomialToLaurent R) g ≫ e.inv =
      (testSpec k).map ((polynomialToLaurent R).op ≫ FF.preimage (g ≫ e.inv)) := by
    simp [mapPoints, FF]
  rw [eg, Functor.FullyFaithful.preimage_map] at hk
  intro x hx
  apply RingHom.mem_ker.mpr
  apply Polynomial.toLaurent_injective
  exact RingHom.mem_ker.mp (hk hx)

private theorem limit_parabolic_cell_open {c : Cocharacter G}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hcell : IsOpenImmersion (bigCellMap D E).left) :
    IsOpenImmersion (cellMultiplication E.contracting D.parabolic).left := by
  let θ := multiplyFactors D.sectionMap D.contractingToParabolic
  have ht : IsIso θ := D.product_iso
  let h := E.contracting.group.X ◁ θ
  have hIso : IsIso h := inferInstanceAs (IsIso (E.contracting.group.X ◁ θ))
  have hi : IsIso h.left := (Over.forget _).map_isIso h
  have hcomp : h ≫ cellMultiplication E.contracting D.parabolic = bigCellMap D E := by
    have eq : θ ≫ D.parabolic.inclusion.hom.hom =
        multiplyFactors D.centralizer.inclusion D.contracting.inclusion := by
      simp only [θ, multiplyFactors, MonObj.mul_comp, Category.assoc,
        ← Grp.comp_hom_hom, D.section_in_G, D.contracting_in_G]
    simp [h, cellMultiplication, bigCellMap, MonObj.comp_mul, eq]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion)
    h.left (cellMultiplication E.contracting D.parabolic).left).mp
    (show IsOpenImmersion (h ≫ cellMultiplication E.contracting D.parabolic).left from
      (congrArg (·.left) hcomp).symm ▸ hcell)

private def HasSubgroupPoints {U X : SchemeOver k} (j : X ⟶ G.X ⊗ U) : Prop :=
  ∀ (V : SchemeOver k) (a : V ⟶ U),
    ∃ S : Subgroup (V ⟶ G.X), ∀ z, z ∈ S ↔ ∃ y : V ⟶ X, y ≫ j = lift z a

set_option maxHeartbeats 800000 in
/-- A subgroup graph containing the cocharacter has trivial opposite contracting component. -/
private theorem graph_eq_one_of_contains_cocharacter
    (hG : IsAffine G.X.left) {c : Cocharacter G}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hm : IsOpenImmersion (cellMultiplication E.contracting D.parabolic).left)
    {X : SchemeOver k} {j : X ⟶ G.X ⊗ (testSpec k).obj (op B)}
    (hsub : HasSubgroupPoints j)
    {e : X ≅ D.parabolic.group.X ⊗ (testSpec k).obj (op B)}
    {d : D.parabolic.group.X ⊗ (testSpec k).obj (op B) ⟶ E.contracting.group.X}
    (he : e.inv ≫ j = lift ((d ≫ E.contracting.inclusion.hom.hom) *
      (fst _ _ ≫ D.parabolic.inclusion.hom.hom)) (snd _ _))
    (hCochar : ∀ (R : TestAlgebra k) (b : B ⟶ R) (t : Rˣ), ∃ y : (testSpec k).obj (op R) ⟶ X,
      y ≫ j = lift (cocharacterPoint c R t) ((testSpec k).map b.op)) : d = 1 := by
  let U := (testSpec k).obj (op B)
  let P := D.parabolic
  let N := E.contracting
  let ip := P.inclusion.hom.hom
  let ineg := N.inclusion.hom.hom
  have hpA := affine_subgroup hG P
  have hUA : IsAffine U.left := inferInstanceAs (IsAffine (Spec (.of B)))
  have hA : IsAffine (P.group.X ⊗ U).left := by rw [Over.tensorObj_left]; infer_instance
  have h (R : TestAlgebra k) (b : B ⟶ R) (p : GroupPoints P.group R) :
      lift p ((testSpec k).map b.op) ≫ d = 1 := by
    let L := laurentAlgebra R
    let r := laurentConstants R
    let t := laurentParameter R
    let a : (testSpec k).obj (op R) ⟶ U := (testSpec k).map b.op
    let aL : (testSpec k).obj (op L) ⟶ U := (testSpec k).map (b ≫ r).op
    let n : GroupPoints N.group R := lift p a ≫ d
    let nL : GroupPoints N.group L := mapPoints r n
    let q : GroupPoints P.group L := mapPoints r p
    let l : GroupPoints G L := cocharacterPoint c L t
    have heq : lift q aL ≫ d = nL := by
      change lift (mapPoints r p) ((testSpec k).map (b ≫ r).op) ≫ d = mapPoints r (lift p a ≫ d)
      simp [mapPoints, a, Functor.map_comp, comp_lift_assoc]
    have lP := (D.parabolic_points L l).mp
      ⟨_, centralizes_hasLimit c (cocharacterPoint_centralizes c L t)⟩
    obtain ⟨lp, hlp⟩ := lP
    change lp ≫ ip = l at hlp
    let pL : GroupPoints P.group L := lp * q * lp⁻¹
    let xP : GroupPoints G L := q ≫ ip
    let xN : GroupPoints G L := nL ≫ ineg
    have hpL : pL ≫ ip = l * xP * l⁻¹ := by
      change pointHom P.inclusion L pL = _
      simp only [pL, map_mul, map_inv, show pointHom P.inclusion L lp = l from hlp]
      rfl
    have hlN : Centralizes (oppositeCocharacter c) l := by
      apply (centralizes_onAlgebras _ _).mpr
      intro S f s
      rw [opposite_point, show cocharacterPoint c S s⁻¹ = (cocharacterPoint c S s)⁻¹ by
        simp only [cocharacterPoint, ← unitPointHom_apply, map_inv]]
      exact ((centralizes_onAlgebras c l).mp (cocharacterPoint_centralizes c L t) S f s).inv_right
    have hnLimit := (E.contracting_points L (nL ≫ ineg)).mpr ⟨nL, rfl⟩
    have hlLimit := centralizes_hasLimit _ hlN
    have hhN : CocharacterDynamics.HasLimit (oppositeCocharacter c) (l * xN * l⁻¹) 1 := by
      simpa using (hlLimit.mul hnLimit).mul hlLimit.inv
    obtain ⟨n', hn'⟩ := (E.contracting_points L _).mp hhN
    change n' ≫ ineg = l * xN * l⁻¹ at hn'
    obtain ⟨S, hS⟩ := hsub ((testSpec k).obj (op L)) aL
    have hSl : l ∈ S := (hS l).mpr (hCochar L (b ≫ r) t)
    have hSg : xN * xP ∈ S := by
      apply (hS _).mpr
      exact (graph_factors_iff he aL _).mpr ⟨q, by rw [reassoc_of% heq]⟩
    have hprod := (hS _).mp (S.mul_mem (S.mul_mem hSl hSg) (S.inv_mem hSl))
    obtain ⟨p', hp'⟩ := (graph_factors_iff he aL _).mp hprod
    have hfg : (n' ≫ ineg) * (pL ≫ ip) =
        (l * (xN * xP) * l⁻¹ : GroupPoints G L) := by
      have hl : (n' ≫ ineg : GroupPoints G L) = l * xN * l⁻¹ := hn'
      have hr : (pL ≫ ip : GroupPoints G L) = l * xP * l⁻¹ := hpL
      change (n' ≫ ineg : GroupPoints G L) * (pL ≫ ip : GroupPoints G L) = _
      rw [hl, hr]
      group
    have hEq : ((lift p' aL ≫ d) ≫ ineg) * (p' ≫ ip) = (n' ≫ ineg) * (pL ≫ ip) :=
      hp'.trans hfg.symm
    obtain ⟨hnc, hp'c⟩ := cell_factors_unique (N := N) (P := P) hm
      (V := (testSpec k).obj (op L)) (n := lift p' aL ≫ d) (n' := n') (p := p') (p' := pL) hEq
    have hdn' : (lift pL aL ≫ d) ≫ ineg = l * xN * l⁻¹ := by
      rw [← hp'c, hnc]
      exact hn'
    have hOrbit : pL ≫ ip = orbit c (p ≫ ip) := by
      rw [hpL]
      rfl
    obtain ⟨z, pPoly, hpPoly, _⟩ := (D.parabolic_points R (p ≫ ip)).mpr ⟨p, rfl⟩
    obtain ⟨w, hw⟩ := polynomial_factors_of_laurent_factors hG pPoly ⟨pL, hOrbit.trans hpPoly.symm⟩
    have hwL : mapPoints (polynomialToLaurent R) w = pL := by
      have hi : IsClosedImmersion ip.left := P.isClosedImmersion
      have : Mono ip := Over.mono_of_mono_left ip
      apply (cancel_mono ip).mp
      rw [show mapPoints (polynomialToLaurent R) w ≫ ip = mapPoints (polynomialToLaurent R) (w ≫ ip)
        from Category.assoc .., hw, hpPoly, hOrbit]
    let bP := b ≫ polynomialConstants R
    let aP := (testSpec k).map bP.op
    have haP : (testSpec k).map (polynomialToLaurent R).op ≫ aP = aL := by
      simp only [aP, aL, bP, r, ← Functor.map_comp, ← op_comp, Category.assoc,
        polynomialConstants_laurent]
    have hNeg : HasExtension c (n ≫ ineg) := by
      refine ⟨_, lift w aP ≫ d ≫ ineg, ?_, rfl⟩
      change _ ≫ lift w aP ≫ d ≫ ineg = _
      rw [comp_lift_assoc, show (testSpec k).map (polynomialToLaurent R).op ≫ w =
        mapPoints (polynomialToLaurent R) w from rfl, hwL, haP]
      rw [← Category.assoc _ d, hdn']
      rfl
    have hunit : n ≫ ineg = (1 : GroupPoints G R) :=
      oppositeLimit_intersection_onPoints hG c _ hNeg
        ((E.contracting_points R (n ≫ ineg)).mpr ⟨n, rfl⟩)
    exact pointHom_injective N R (hunit.trans ((pointHom N.inclusion R).map_one).symm)
  obtain ⟨A, ⟨i⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hA
  let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
  let b := (FF.preimage (i.hom ≫ snd P.group.X U)).unop
  have hb : (testSpec k).map b.op = i.hom ≫ snd P.group.X U := FF.map_preimage _
  have h' := h A.unop b (i.hom ≫ fst P.group.X U)
  rw [hb, lift_comp_fst_snd] at h'
  exact (cancel_epi i.hom).mp (h'.trans (MonObj.comp_one i.hom).symm)

end ContractingGraph

section LaurentCocycle

variable {B : TestAlgebra k}

private def laurentScaleMap {R S : TestAlgebra k} (a : R ⟶ S) (t : Sˣ) :
    laurentAlgebra R ⟶ laurentAlgebra S :=
  CommAlgCat.ofHom
    { laurentScale a.hom.toRingHom t with
      commutes' := fun v ↦ by
        change LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp a.hom.toRingHom) _
          (LaurentPolynomial.C (algebraMap k R v)) = LaurentPolynomial.C (algebraMap k S v)
        rw [LaurentPolynomial.eval₂_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          a.hom.commutes] }

/-- Averaging the second Laurent variable gives an infinitesimal conjugator for the cocycle. -/
private theorem laurent_cocycle_coboundary
    (hG : IsAffine G.X.left) (N : ClosedSubgroup G)
    (I : Ideal B) (hI : I ^ 2 = ⊥)
    (n : GroupPoints N.group (laurentAlgebra B)) (g : GroupPoints G (laurentAlgebra B))
    (hn : mapPoints (laurentScaleMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)) 1) n = 1)
    (h : let r := laurentConstants B
      let j := laurentConstants (laurentAlgebra B)
      let t := laurentParameter B
      let z := n ≫ N.inclusion.hom.hom
      (mapPoints (laurentScaleMap r t) z : GroupPoints G (laurentAlgebra (laurentAlgebra B))) =
        (mapPoints j z : GroupPoints G _) * mapPoints j g *
          mapPoints (laurentScaleMap r 1) z * (mapPoints j g : GroupPoints G _)⁻¹) :
    ∃ v : GroupPoints N.group B,
      mapPoints (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)) v = 1 ∧
        let vG : GroupPoints G (laurentAlgebra B) :=
          mapPoints (laurentConstants B) (pointHom N.inclusion B v)
        pointHom N.inclusion (laurentAlgebra B) n * g = vG * g * vG⁻¹ := by
  let L := laurentAlgebra B
  let R₀ : TestAlgebra k := CommAlgCat.of k (B ⧸ I)
  let q : B ⟶ R₀ := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  let r := laurentConstants B
  let j := laurentConstants L
  let t := laurentParameter B
  let J := I.map (algebraMap B L)
  let C := (laurentConstantModIdeal I).restrictScalars k
  let E := (laurentConstantModIdeal J).restrictScalars k
  let U : TestAlgebra k := CommAlgCat.of k C
  let W : TestAlgebra k := CommAlgCat.of k E
  let i : U ⟶ L := CommAlgCat.ofHom C.val
  let f : W ⟶ laurentAlgebra L := CommAlgCat.ofHom E.val
  let avg : U ⟶ B := CommAlgCat.ofHom ((laurentAverage I hI).restrictScalars k)
  let avg' : W ⟶ L := CommAlgCat.ofHom
    ((laurentAverage J (extendedIdeal_squareZero I hI L)).restrictScalars k)
  have hN := affine_subgroup hG N
  obtain ⟨A, ⟨en⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hN
  let coords := affinePointCoordinates en L n
  have red_coords (a : A.unop) (m : ℤ) :
      q.hom ((coords a).coeff m) =
        (LaurentPolynomial.C (affinePointCoordinates en R₀ (1 : GroupPoints N.group R₀) a)).coeff m := by
    have eq₁ := DFunLike.congr_fun (affinePointCoordinates_map en (laurentScaleMap q 1) n) a
    have eq₂ := DFunLike.congr_fun
      (affinePointCoordinates_map en (laurentConstants R₀) (1 : GroupPoints N.group R₀)) a
    have h₁ : mapPoints (laurentScaleMap q 1) n = 1 := hn
    have h₂ : mapPoints (laurentConstants R₀) (1 : GroupPoints N.group R₀) = 1 :=
      (groupPointsFunctor k).obj N.group |>.map (laurentConstants R₀) |>.hom.map_one
    rw [h₁] at eq₁
    rw [h₂] at eq₂
    have eq := congrArg (fun s : LaurentPolynomial R₀ ↦ s.coeff m) (eq₁.symm.trans eq₂)
    change (laurentScale q.hom.toRingHom 1 (coords a)).coeff m =
      (LaurentPolynomial.C (affinePointCoordinates en R₀ (1 : GroupPoints N.group R₀) a)).coeff m at eq
    rw [coeff_laurentScale, one_zpow, Units.val_one, mul_one] at eq
    exact eq
  let ap : A.unop →ₐ[k] U := coords.codRestrict C (fun a m hm ↦ by
    have hEq := red_coords a m
    rw [LaurentPolynomial.C_apply, ite_eq_right hm] at hEq
    exact Ideal.Quotient.eq_zero_iff_mem.mp hEq)
  let p : GroupPoints N.group U := (affinePointCoordinates en U).symm ap
  have hp : mapPoints i p = n := by
    apply (affinePointCoordinates en L).injective
    rw [affinePointCoordinates_map, Equiv.apply_symm_apply]
    rfl
  let v : GroupPoints N.group B := mapPoints avg p
  have hv : mapPoints q v = 1 := by
    apply (affinePointCoordinates en R₀).injective
    rw [affinePointCoordinates_map, show v = mapPoints avg p from rfl, affinePointCoordinates_map,
      Equiv.apply_symm_apply]
    apply AlgHom.ext
    intro a
    change q.hom ((coords a).coeff 0) = _
    simpa using red_coords a 0
  let constMap : L ⟶ W := CommAlgCat.ofHom (j.hom.codRestrict E (by
    intro x m hm
    change (LaurentPolynomial.C x).coeff m ∈ J
    rw [LaurentPolynomial.C_apply, ite_eq_right hm]
    exact J.zero_mem))
  let scaled (s : Lˣ) : U ⟶ W := CommAlgCat.ofHom
    (((laurentScaleMap r s).hom.comp i.hom).codRestrict E (fun x ↦
      laurentScale_mem r.hom.toRingHom s I J (fun _ hx ↦ Ideal.mem_map_of_mem _ hx) x.property))
  have fConst : constMap ≫ f = j := rfl
  have fScale (s : Lˣ) : scaled s ≫ f = i ≫ laurentScaleMap r s := rfl
  have avgConst : constMap ≫ avg' = 𝟙 L := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change (LaurentPolynomial.C x).coeff 0 = x
    simp
  have avgScale (s : Lˣ) : scaled s ≫ avg' = avg ≫ r := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change (laurentScale r.hom.toRingHom s x.val).coeff 0 = r.hom (x.val.coeff 0)
    simp [coeff_laurentScale]
  let pG : GroupPoints G U := p ≫ N.inclusion.hom.hom
  let z : GroupPoints G L := n ≫ N.inclusion.hom.hom
  have zi : mapPoints i pG = z := by
    simpa only [mapPoints, Category.assoc] using congrArg (· ≫ N.inclusion.hom.hom) hp
  have dep : (mapPoints (scaled t) pG : GroupPoints G W) =
      (mapPoints constMap z : GroupPoints G W) * mapPoints constMap g *
        mapPoints (scaled 1) pG * (mapPoints constMap g : GroupPoints G W)⁻¹ := by
    apply affine_mapPoints_injective hG f Subtype.val_injective
    change _ = ((groupPointsFunctor k).obj G |>.map f |>.hom) (_ * _ * _ * _⁻¹)
    rw [map_mul, map_mul, map_mul, map_inv]
    change mapPoints f (mapPoints (scaled t) pG) =
      (mapPoints f (mapPoints constMap z) : GroupPoints G _) * mapPoints f (mapPoints constMap g) *
        mapPoints f (mapPoints (scaled 1) pG) * (mapPoints f (mapPoints constMap g) : GroupPoints G _)⁻¹
    simp only [← mapPoints_comp, fConst, fScale]
    simp only [mapPoints_comp i, zi]
    exact h
  have ev := congrArg ((groupPointsFunctor k).obj G |>.map avg' |>.hom) dep
  rw [map_mul, map_mul, map_mul, map_inv] at ev
  change mapPoints avg' (mapPoints (scaled t) pG) =
    (mapPoints avg' (mapPoints constMap z) : GroupPoints G _) * mapPoints avg' (mapPoints constMap g) *
      mapPoints avg' (mapPoints (scaled 1) pG) *
        (mapPoints avg' (mapPoints constMap g) : GroupPoints G _)⁻¹ at ev
  simp only [← mapPoints_comp, avgConst, avgScale] at ev
  have hEval : mapPoints (avg ≫ r) pG = mapPoints r (v ≫ N.inclusion.hom.hom) := by
    rw [mapPoints_comp]
    rfl
  have idPt (x : GroupPoints G L) : mapPoints (𝟙 L) x = x := by simp [mapPoints]
  rw [hEval, idPt z, idPt g] at ev
  let a : GroupPoints G L := mapPoints r (v ≫ N.inclusion.hom.hom)
  refine ⟨v, hv, ?_⟩
  change z * g = a * g * a⁻¹
  change a = z * g * a * g⁻¹ at ev
  calc
    z * g = (z * g * a * g⁻¹) * g * a⁻¹ := by group
    _ = _ := by rw [← ev]

end LaurentCocycle

@[reassoc (attr := simp)]
private theorem conjugationOver_snd (g : U ⟶ G.X) :
    conjugationOver g ≫ snd G.X U = snd G.X U := lift_snd _ _

private theorem conjugationOver_comp (g h : U ⟶ G.X) :
    conjugationOver g ≫ conjugationOver h = conjugationOver (h * g) := by
  rw [comp_conjugationOver]
  apply CartesianMonoidalCategory.hom_ext
  · simp [conjugationOver, conjugateFamily, MonObj.comp_mul]
    group
  · simp

private theorem conjugationOver_lift {V : SchemeOver k} (g : U ⟶ G.X)
    (z : V ⟶ G.X) (v : V ⟶ U) :
    lift z v ≫ conjugationOver g = lift ((v ≫ g) * z * (v ≫ g)⁻¹) v := by
  simp [comp_conjugationOver]

private theorem conjugationOver_natural (g : U ⟶ G.X) {V : SchemeOver k} (v : V ⟶ U) :
    conjugationOver (v ≫ g) ≫ (G.X ◁ v) = (G.X ◁ v) ≫ conjugationOver g := by
  rw [comp_conjugationOver g]
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [conjugationOver, conjugateFamily]

private theorem conjugationOver_one : conjugationOver (1 : U ⟶ G.X) = 𝟙 _ := by
  simp [conjugationOver, conjugateFamily]

private theorem conjugateInclusion_eq (P : ClosedSubgroup G) (g : U ⟶ G.X) :
    conjugateInclusion P g = (P.inclusion.hom.hom ▷ U) ≫ conjugationOver g := by
  rw [comp_conjugationOver]
  apply CartesianMonoidalCategory.hom_ext <;> simp [conjugateInclusion, conjugateFamily]

private theorem factors_conjugation_iff {X V : SchemeOver k} (j : X ⟶ G.X ⊗ U)
    (v : V ⟶ U) (g : U ⟶ G.X) (z : V ⟶ G.X) :
    (∃ y : V ⟶ X, y ≫ (j ≫ conjugationOver g) = lift z v) ↔
      ∃ y : V ⟶ X, y ≫ j = lift ((v ≫ g)⁻¹ * z * (v ≫ g)) v := by
  have h : lift z v ≫ conjugationOver g⁻¹ = lift ((v ≫ g)⁻¹ * z * (v ≫ g)) v := by
    simp [conjugationOver_lift, GrpObj.comp_inv]
  rw [← h]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← hy, Category.assoc, Category.assoc, conjugationOver_mul_inv, Category.comp_id]
  · rintro ⟨y, hy⟩
    have hm : Mono (conjugationOver g⁻¹) := by
      have : IsIso (conjugationOver g⁻¹) := (conjugationOverIso g⁻¹).isIso_hom
      infer_instance
    refine ⟨y, (cancel_mono (conjugationOver g⁻¹)).mp ?_⟩
    rw [Category.assoc, Category.assoc, conjugationOver_mul_inv, Category.comp_id, hy]

private theorem family_base_change_over_ambient (Q : Family G T) (a : U ⟶ T)
    {V : SchemeOver k} (v : V ⟶ U) :
    IsPullback (familyPullbackMap Q a v) (pullback.snd Q.ambient (G.X ◁ (v ≫ a)))
      (pullback.snd Q.ambient (G.X ◁ a)) (G.X ◁ v) := by
  apply IsPullback.of_right (h₁₂ := pullback.fst Q.ambient (G.X ◁ a))
    (h₂₂ := G.X ◁ a) (v₁₃ := Q.ambient)
  · simpa [familyPullbackMap] using IsPullback.of_hasPullback Q.ambient (G.X ◁ (v ≫ a))
  · simp [familyPullbackMap]
  · exact IsPullback.of_hasPullback Q.ambient (G.X ◁ a)

private theorem family_factors_subgroup (Q : Family G T) (a : U ⟶ T) :
    ∃ S : Subgroup (U ⟶ G.X), ∀ z, z ∈ S ↔
      ∃ y : U ⟶ Q.overField, y ≫ Q.ambient = lift z a := by
  let A : Over T.left := Over.mk a.left
  let E : (Over.map T.hom).obj A ≅ U := Over.isoMk (Iso.refl _) (by
    simp [A])
  let M := relativePointHom (G := G) A
  let mapInc : (A ⟶ Q.group.X) →* (A ⟶ (relativeGroup G T).X) :=
    { toFun := fun z ↦ z ≫ Q.inclusion.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun _ _ ↦ MonObj.mul_comp .. }
  let mapE : ((Over.map T.hom).obj A ⟶ G.X) →* (U ⟶ G.X) :=
    { toFun := fun z ↦ E.inv ≫ z
      map_one' := MonObj.comp_one _
      map_mul' := fun _ _ ↦ MonObj.comp_mul .. }
  refine ⟨(mapE.comp (M.comp mapInc)).range, fun z ↦ ?_⟩
  let p := ((Over.mapPullbackAdj T.hom).homEquiv A G.X) (E.hom ≫ z)
  have hp : M p = E.hom ≫ z :=
    ((Over.mapPullbackAdj T.hom).homEquiv A G.X).symm_apply_apply _
  have ea : overBase T A = E.hom ≫ a := by
    apply Over.OverMorphism.ext
    change a.left = 𝟙 _ ≫ a.left
    simp
  have hq := factors_relative_iff Q.inclusion.hom.hom (q := Q.ambient) (familyAmbient_left Q) p
  constructor
  · rintro ⟨v, hv⟩
    have hcase : M (v ≫ Q.inclusion.hom.hom) = E.hom ≫ z := by
      change E.inv ≫ M (v ≫ Q.inclusion.hom.hom) = z at hv
      rw [← hv, E.hom_inv_id_assoc]
    have hpre : v ≫ Q.inclusion.hom.hom = p := by
      apply ((Over.mapPullbackAdj T.hom).homEquiv A G.X).symm.injective
      exact hcase.trans hp.symm
    obtain ⟨y, hy⟩ := hq.mp ⟨v, hpre⟩
    refine ⟨E.inv ≫ y, ?_⟩
    rw [Category.assoc, hy, ea, show relativePoint p = E.hom ≫ z from hp, comp_lift]
    simp
  · rintro ⟨y, hy⟩
    have he : (E.hom ≫ y) ≫ Q.ambient = lift (relativePoint p) (overBase T A) := by
      rw [Category.assoc, hy, ea, show relativePoint p = E.hom ≫ z from hp, comp_lift]
    obtain ⟨v, hv⟩ := hq.mpr ⟨E.hom ≫ y, he⟩
    refine ⟨v, ?_⟩
    change E.inv ≫ M (v ≫ Q.inclusion.hom.hom) = z
    rw [hv, hp, E.inv_hom_id_assoc]

section CocharacterLift

variable {B : TestAlgebra k}

private theorem laurentScaleMap_constants {R S : TestAlgebra k} (a : R ⟶ S) (s : Sˣ) :
    laurentConstants R ≫ laurentScaleMap a s = a ≫ laurentConstants S := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp a.hom.toRingHom) _
    (LaurentPolynomial.C x) = LaurentPolynomial.C (a.hom x)
  rw [LaurentPolynomial.eval₂_C]
  rfl

private theorem laurentScaleMap_parameter {R S : TestAlgebra k} (a : R ⟶ S) (s : Sˣ) :
    Units.map (laurentScaleMap a s).hom.toMonoidHom (laurentParameter R) =
      Units.map (laurentConstants S).hom.toMonoidHom s * laurentParameter S := by
  apply Units.ext
  change LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp a.hom.toRingHom) _
      (LaurentPolynomial.T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

private theorem torus_conjugates_contracting
    {c : Cocharacter G} (E : LimitDecomposition (oppositeCocharacter c))
    {R : TestAlgebra k} (s : Rˣ) (u : GroupPoints E.contracting.group R) :
    ∃ u' : GroupPoints E.contracting.group R,
      pointHom E.contracting.inclusion R u' =
        cocharacterPoint c R s * pointHom E.contracting.inclusion R u * (cocharacterPoint c R s)⁻¹ := by
  let l := cocharacterPoint c R s
  have hl : Centralizes (oppositeCocharacter c) l := by
    apply (centralizes_onAlgebras _ _).mpr
    intro S f t
    rw [opposite_point, show cocharacterPoint c S t⁻¹ = (cocharacterPoint c S t)⁻¹ by
      simp only [cocharacterPoint, ← unitPointHom_apply, map_inv]]
    exact ((centralizes_onAlgebras c l).mp (cocharacterPoint_centralizes c R s) S f t).inv_right
  have hlLim := centralizes_hasLimit _ hl
  have hlim := (E.contracting_points R _).mpr ⟨u, rfl⟩
  exact (E.contracting_points R _).mp (by simpa using (hlLim.mul hlim).mul hlLim.inv)

set_option maxHeartbeats 1500000 in
private theorem graph_contains_conjugate_cocharacter
    (hG : IsAffine G.X.left) {c : Cocharacter G}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hm : IsOpenImmersion (cellMultiplication E.contracting D.parabolic).left)
    (I : Ideal B) (hI : I ^ 2 = ⊥)
    {X : SchemeOver k} {j : X ⟶ G.X ⊗ (testSpec k).obj (op B)}
    (hsub : HasSubgroupPoints j)
    {e : X ≅ D.parabolic.group.X ⊗ (testSpec k).obj (op B)}
    {d : D.parabolic.group.X ⊗ (testSpec k).obj (op B) ⟶ E.contracting.group.X}
    (he : e.inv ≫ j = lift ((d ≫ E.contracting.inclusion.hom.hom) *
      (fst _ _ ≫ D.parabolic.inclusion.hom.hom)) (snd _ _))
    (hd : (D.parabolic.group.X ◁ reductionMap B I) ≫ d = 1) :
    ∃ v : GroupPoints G B,
      reductionMap B I ≫ v = 1 ∧
      ∀ (R : TestAlgebra k) (a : B ⟶ R) (s : Rˣ),
        let va : GroupPoints G R := mapPoints a v
        ∃ y : (testSpec k).obj (op R) ⟶ X,
          y ≫ j = lift (va * cocharacterPoint c R s * va⁻¹) ((testSpec k).map a.op) := by
  let P := D.parabolic
  let N := E.contracting
  let L := laurentAlgebra B
  let F := testSpec k
  let r := laurentConstants B
  let t := laurentParameter B
  let vL : (F.obj (op L)) ⟶ F.obj (op B) := F.map r.op
  let l : GroupPoints G L := cocharacterPoint c L t
  obtain ⟨p, hp⟩ := (D.parabolic_points L l).mp
    ⟨_, centralizes_hasLimit c (cocharacterPoint_centralizes c L t)⟩
  let n : GroupPoints N.group L := lift p vL ≫ d
  let j₁ := laurentConstants L
  let j₂ := laurentScaleMap r 1
  let j₁₂ := laurentScaleMap r t
  let W := laurentAlgebra L
  let vW : (F.obj (op W)) ⟶ F.obj (op B) := F.map (r ≫ j₁).op
  have hvW (s : Lˣ) : r ≫ laurentScaleMap r s = r ≫ j₁ := laurentScaleMap_constants r s
  have hpt (a : L ⟶ W) (ha : r ≫ a = r ≫ j₁) :
      lift (mapPoints a p) vW ≫ d = mapPoints a n := by
    change lift (mapPoints a p) (F.map (r ≫ j₁).op) ≫ d = _
    rw [← ha]
    simp [mapPoints, n, vL, F, Functor.map_comp, comp_lift_assoc]
  let p₁ : GroupPoints P.group W := mapPoints j₁ p
  let p₂ : GroupPoints P.group W := mapPoints j₂ p
  let p₁₂ : GroupPoints P.group W := mapPoints j₁₂ p
  let n₁ : GroupPoints N.group W := mapPoints j₁ n
  let n₂ : GroupPoints N.group W := mapPoints j₂ n
  let n₁₂ : GroupPoints N.group W := mapPoints j₁₂ n
  let l₁ : GroupPoints G W := mapPoints j₁ l
  let l₂ : GroupPoints G W := mapPoints j₂ l
  let l₁₂ : GroupPoints G W := mapPoints j₁₂ l
  have hl₁ : pointHom P.inclusion W p₁ = l₁ := by
    change mapPoints j₁ p ≫ P.inclusion.hom.hom = mapPoints j₁ l
    rw [show mapPoints j₁ p ≫ P.inclusion.hom.hom = mapPoints j₁ (pointHom P.inclusion L p)
      from Category.assoc .., hp]
  have hl₂ : pointHom P.inclusion W p₂ = l₂ := by
    change mapPoints j₂ p ≫ P.inclusion.hom.hom = mapPoints j₂ l
    rw [show mapPoints j₂ p ≫ P.inclusion.hom.hom = mapPoints j₂ (pointHom P.inclusion L p)
      from Category.assoc .., hp]
  have hl₁₂ : pointHom P.inclusion W p₁₂ = l₁₂ := by
    change mapPoints j₁₂ p ≫ P.inclusion.hom.hom = mapPoints j₁₂ l
    rw [show mapPoints j₁₂ p ≫ P.inclusion.hom.hom = mapPoints j₁₂ (pointHom P.inclusion L p)
      from Category.assoc .., hp]
  have hmul : l₁₂ = l₁ * l₂ := by
    have ht₁₂ : Units.map j₁₂.hom.toMonoidHom t =
        Units.map j₁.hom.toMonoidHom t * laurentParameter L := laurentScaleMap_parameter r t
    have ht₂ : Units.map j₂.hom.toMonoidHom t = laurentParameter L := by
      have hh := laurentScaleMap_parameter r (1 : Lˣ)
      simpa only [map_one, one_mul] using hh
    change mapPoints j₁₂ (cocharacterPoint c L t) =
      (mapPoints j₁ (cocharacterPoint c L t) : GroupPoints G W) * mapPoints j₂ (cocharacterPoint c L t)
    rw [mapPoints_cocharacterPoint, mapPoints_cocharacterPoint, mapPoints_cocharacterPoint,
      ht₁₂, ht₂, cocharacterPoint_mul]
  obtain ⟨n', hn'⟩ := torus_conjugates_contracting (c := c) E
    (Units.map j₁.hom.toMonoidHom t) n₂
  have hn' : pointHom N.inclusion W n' = l₁ * pointHom N.inclusion W n₂ * l₁⁻¹ := by
    simpa only [l₁, l, mapPoints_cocharacterPoint] using hn'
  obtain ⟨S, hS⟩ := hsub (F.obj (op W)) vW
  have h₁ : pointHom N.inclusion W n₁ * l₁ ∈ S := by
    apply (hS _).mpr
    exact (graph_factors_iff he vW _).mpr ⟨p₁, by
      rw [reassoc_of% (hpt j₁ rfl)]
      exact congrArg ((pointHom N.inclusion W n₁) * ·) hl₁⟩
  have h₂ : pointHom N.inclusion W n₂ * l₂ ∈ S := by
    apply (hS _).mpr
    exact (graph_factors_iff he vW _).mpr ⟨p₂, by
      rw [reassoc_of% (hpt j₂ (hvW _))]
      exact congrArg ((pointHom N.inclusion W n₂) * ·) hl₂⟩
  obtain ⟨p', hp'⟩ := (graph_factors_iff he vW _).mp ((hS _).mp (S.mul_mem h₁ h₂))
  have hcalc : pointHom N.inclusion W (n₁ * n') * pointHom P.inclusion W p₁₂ =
      (pointHom N.inclusion W n₁ * l₁) * (pointHom N.inclusion W n₂ * l₂) := by
    rw [map_mul, hn', hl₁₂, hmul]
    group
  have hEq : ((lift p' vW ≫ d) ≫ N.inclusion.hom.hom) * (p' ≫ P.inclusion.hom.hom) =
      ((n₁ * n') ≫ N.inclusion.hom.hom) * (p₁₂ ≫ P.inclusion.hom.hom) := hp'.trans hcalc.symm
  obtain ⟨heq, hpEq⟩ := cell_factors_unique (N := N) (P := P) hm
    (V := F.obj (op W)) (n := lift p' vW ≫ d) (n' := n₁ * n') (p := p') (p' := p₁₂) hEq
  have heq' : n₁₂ = n₁ * n' := by
    change mapPoints j₁₂ n = _
    rw [← hpt j₁₂ (hvW t)]
    change lift p₁₂ vW ≫ d = _
    rw [← hpEq]
    exact heq
  have hcoc : (mapPoints j₁₂ (pointHom N.inclusion L n) : GroupPoints G W) =
        (mapPoints j₁ (pointHom N.inclusion L n) : GroupPoints G W) * mapPoints j₁ l *
          mapPoints j₂ (pointHom N.inclusion L n) * (mapPoints j₁ l : GroupPoints G W)⁻¹ := by
    change pointHom N.inclusion W n₁₂ = (pointHom N.inclusion W n₁) * l₁ *
      (pointHom N.inclusion W n₂) * l₁⁻¹
    rw [heq', map_mul, hn']
    group
  let B₀ : TestAlgebra k := CommAlgCat.of k (B ⧸ I)
  let q : B ⟶ B₀ := CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  let m := laurentScaleMap q 1
  have hred : mapPoints m n = 1 := by
    have hb : r ≫ m = q ≫ laurentConstants B₀ := laurentScaleMap_constants q 1
    change F.map m.op ≫ lift p vL ≫ d = _
    rw [comp_lift_assoc]
    have eq : F.map m.op ≫ vL = F.map (laurentConstants B₀).op ≫ reductionMap B I := by
      rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hb]
    rw [eq]
    have ee : lift (F.map m.op ≫ p) (F.map (laurentConstants B₀).op ≫ reductionMap B I) =
        lift (F.map m.op ≫ p) (F.map (laurentConstants B₀).op) ≫ (P.group.X ◁ reductionMap B I) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [P]
    rw [ee, Category.assoc, hd, MonObj.comp_one]
  obtain ⟨u, hu, hul⟩ := laurent_cocycle_coboundary hG N I hI n l hred hcoc
  let v : GroupPoints G B := pointHom N.inclusion B u
  refine ⟨v, ?_, fun R a s ↦ ?_⟩
  · change F.map q.op ≫ u ≫ N.inclusion.hom.hom = _
    rw [← Category.assoc, show F.map q.op ≫ u = 1 from hu, MonObj.one_comp]
  · let ηR := evalLaurent a s
    have hbase : r ≫ ηR = a := evalLaurent_constants a s
    have hlη : mapPoints ηR l = cocharacterPoint c R s := by
      rw [show l = cocharacterPoint c L t from rfl, mapPoints_cocharacterPoint]
      rw [evalLaurent_parameter]
    have hvη : (mapPoints ηR (mapPoints r v) : GroupPoints G R) = mapPoints a v := by
      rw [← mapPoints_comp, hbase]
    have hgrp := congrArg (((groupPointsFunctor k).obj G).map ηR).hom hul
    rw [map_mul, map_mul, map_mul, map_inv] at hgrp
    change (mapPoints ηR (pointHom N.inclusion L n) : GroupPoints G R) * mapPoints ηR l =
      (mapPoints ηR (mapPoints r v) : GroupPoints G R) * mapPoints ηR l *
        (mapPoints ηR (mapPoints r v) : GroupPoints G R)⁻¹ at hgrp
    rw [hlη, hvη] at hgrp
    apply (graph_factors_iff he (F.map a.op) _).mpr
    refine ⟨mapPoints ηR p, ?_⟩
    have hnη : lift (mapPoints ηR p) (F.map a.op) ≫ d = mapPoints ηR n := by
      rw [← hbase]
      simp [mapPoints, n, vL, F, Functor.map_comp, comp_lift_assoc]
    rw [reassoc_of% hnη]
    change (mapPoints ηR (pointHom N.inclusion L n) : GroupPoints G R) *
      (mapPoints ηR (pointHom P.inclusion L p) : GroupPoints G R) = _
    rwa [hp, hlη]

end CocharacterLift

open Specs.RankOneFlag (SameSubgroup)

private theorem conjugates_of_sameSubgroup {P P' : ClosedSubgroup G} (h : SameSubgroup P P')
    {Q : Family G T} {a : U ⟶ T} {g : U ⟶ G.X} (hg : Conjugates P Q a g) : Conjugates P' Q a g := by
  obtain ⟨f, hf⟩ := h.1
  obtain ⟨f', hf'⟩ := h.2
  have hf₁ : f.hom.hom ≫ P'.inclusion.hom.hom = P.inclusion.hom.hom := congrArg (·.hom.hom) hf
  have hf₂ : f'.hom.hom ≫ P.inclusion.hom.hom = P'.inclusion.hom.hom := congrArg (·.hom.hom) hf'
  rw [conjugates_iff_factorizations] at hg ⊢
  intro V v z
  rw [hg]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p ≫ f.hom.hom, by simpa [Category.assoc, hf₁] using hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p ≫ f'.hom.hom, by simpa [Category.assoc, hf₂] using hp⟩

private theorem pullback_factors_iff {V X Y S : SchemeOver k}
    (i : X ⟶ S) (b : Y ⟶ S) (p : V ⟶ Y) :
    (∃ h : V ⟶ pullback i b, h ≫ pullback.snd i b = p) ↔
      ∃ h : V ⟶ X, h ≫ i = p ≫ b := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h ≫ pullback.fst i b, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hh]
  · rintro ⟨h, hh⟩
    exact ⟨pullback.lift h p hh, pullback.lift_snd _ _ _⟩

private theorem subgroup_points_pullback (Q : Family G T) (a : U ⟶ T) :
    HasSubgroupPoints (pullback.snd Q.ambient (G.X ◁ a)) := by
  intro V v
  obtain ⟨S, hS⟩ := family_factors_subgroup Q (v ≫ a)
  refine ⟨S, fun z ↦ ?_⟩
  rw [hS z, pullback_factors_iff]
  have he : lift z v ≫ (G.X ◁ a) = lift z (v ≫ a) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [he]

/-- The classifying parameter of a pulled-back family is the pulled-back parameter. -/
theorem classifies_baseChange : ClassifiesBaseChange.{u} := by
  intro k _ G T U P D Q hQ a x hx
  let F := Over.forget (Spec (CommRingCat.of k))
  let j := pullback.snd Q.ambient (G.X ◁ a)
  have hc : IsClosedImmersion j.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback Q.ambient (G.X ◁ a)).map F) (familyAmbient_closed Q)
  have hs : Smooth (j ≫ snd G.X U).left :=
    MorphismProperty.of_isPullback ((familyPullbackSquare Q a).map F) Q.smooth
  obtain ⟨J, i, e, hi, hb⟩ := relativeClosedLocus _ j hc (subgroup_points_pullback Q a)
  have he : IsIso e.hom.left := (F.mapIso e).isIso_hom
  have hclosed : IsClosedImmersion i.hom.hom.left := hi.symm ▸ IsClosedImmersion.comp _ j.left
  have hJ : Smooth J.X.hom := hb.symm ▸ MorphismProperty.comp_mem _ _ _ inferInstance hs
  let Q' : Family G U := ⟨J, i, hclosed, hJ⟩
  have heq : Q'.ambient = e.hom ≫ j :=
    Over.OverMorphism.ext ((familyAmbient_left Q').trans hi)
  have hfactor {V : SchemeOver k} (b : V ⟶ U) (z : V ⟶ G.X) :
      (∃ y : V ⟶ Q'.overField, y ≫ Q'.ambient = lift z b) ↔
        ∃ y : V ⟶ Q.overField, y ≫ Q.ambient = lift z (b ≫ a) := by
    rw [heq]
    have hlift : lift z b ≫ (G.X ◁ a) = lift z (b ≫ a) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [← hlift, ← pullback_factors_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y ≫ e.hom, by simpa only [Category.assoc] using hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨y ≫ e.inv, ?_⟩
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hy
  have hconj {V : SchemeOver k} (b : V ⟶ U) (g : V ⟶ G.X) :
      Conjugates P Q' b g ↔ Conjugates P Q (b ≫ a) g := by
    simp only [conjugates_iff_factorizations, hfactor, Category.assoc]
  refine ⟨Q', e, heq.symm, ?_, ?_⟩
  · intro K _ _ _ b
    obtain ⟨g, hg⟩ := hQ K (b ≫ a)
    exact ⟨g, (hconj b g).mpr hg⟩
  · intro V b g
    rw [hconj, ← Category.assoc]
    exact hx _ _ _

private theorem subgroup_points_conjugation {X : SchemeOver k} {j : X ⟶ G.X ⊗ U}
    (h : HasSubgroupPoints j) (g : U ⟶ G.X) :
    HasSubgroupPoints (j ≫ conjugationOver g) := by
  intro V a
  obtain ⟨S, hS⟩ := h V a
  refine ⟨S.comap (MulAut.conj (a ≫ g)⁻¹).toMonoidHom, fun z ↦ ?_⟩
  rw [factors_conjugation_iff, ← hS]
  change ((a ≫ g)⁻¹ * z * ((a ≫ g)⁻¹)⁻¹ ∈ S) ↔ _
  rw [inv_inv]

private theorem twist_square {V X Y : SchemeOver k} {i : X ⟶ G.X ⊗ U} {v : V ⟶ U}
    {a : Y ⟶ X} {b : Y ⟶ G.X ⊗ V} (h : IsPullback a b i (G.X ◁ v))
    (g : U ⟶ G.X) :
    IsPullback a (b ≫ conjugationOver (v ≫ g)) (i ≫ conjugationOver g) (G.X ◁ v) :=
  h.of_iso (Iso.refl _) (Iso.refl _) (conjugationOverIso (v ≫ g)) (conjugationOverIso g)
    (by simp) (by simp [conjugationOverIso]) (by simp [conjugationOverIso])
    ((conjugationOver_natural g v).symm)

set_option maxHeartbeats 1500000 in
/-- Lift the conjugating point, then correct it using the graph over the limit parabolic. -/
private theorem conjugacy_lifts_for_limit_parabolic {B : TestAlgebra k}
    (H : AffineAlgebraicGroup k) (hSm : Smooth H.val.X.hom)
    (c : Cocharacter H.val) (D : LimitDecomposition c)
    (Q : Family H.val T) (a : (testSpec k).obj (op B) ⟶ T) (I : Ideal B) (hI : I ^ 2 = ⊥)
    (g₀ : (testSpec k).obj (op (CommAlgCat.of k (B ⧸ I))) ⟶ H.val.X)
    (hg₀ : Conjugates D.parabolic Q (reductionMap B I ≫ a) g₀) :
    ∃ g : (testSpec k).obj (op B) ⟶ H.val.X,
      Conjugates D.parabolic Q a g ∧ reductionMap B I ≫ g = g₀ := by
  let P := D.parabolic
  let U := (testSpec k).obj (op B)
  let U₀ := (testSpec k).obj (op (CommAlgCat.of k (B ⧸ I)))
  let r := reductionMap B I
  let F := Over.forget (Spec (CommRingCat.of k))
  let X := pullback Q.ambient (H.val.X ◁ a)
  let j := pullback.snd Q.ambient (H.val.X ◁ a)
  let b₀ := pullback.snd Q.ambient (H.val.X ◁ (r ≫ a))
  have ha := H.property.1
  have hj : IsClosedImmersion j.left := MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback Q.ambient (H.val.X ◁ a)).map F) (familyAmbient_closed Q)
  have hSj : Smooth (j ≫ snd H.val.X U).left :=
    MorphismProperty.of_isPullback ((familyPullbackSquare Q a).map F) Q.smooth
  obtain ⟨E⟩ := existsLimitDecomposition H (oppositeCocharacter c)
  have hm := limit_parabolic_cell_open D E (bigCell H c D E)
  obtain ⟨g, hg⟩ := smoothAffine_lift (S := CommRingCat.of k) hSm B I hI g₀
  change r ≫ g = g₀ at hg
  obtain ⟨e₀, he₀⟩ := hg₀
  let j₁ := j ≫ conjugationOver g⁻¹
  let b₁ := b₀ ≫ conjugationOver (r ≫ g⁻¹)
  have hs₁ := twist_square (family_base_change_over_ambient Q a r) g⁻¹
  have h₁ : e₀.hom ≫ b₁ = P.inclusion.hom.hom ▷ U₀ := by
    change e₀.hom ≫ b₀ ≫ conjugationOver (r ≫ g⁻¹) = _
    rw [← Category.assoc, he₀, conjugateInclusion_eq, Category.assoc, GrpObj.comp_inv, hg,
      conjugationOver_mul_inv, Category.comp_id]
  let e₁ := e₀ ≪≫ hs₁.isoPullback
  have he₁ : e₁.hom ≫ pullback.snd j₁ (H.val.X ◁ r) = P.inclusion.hom.hom ▷ U₀ := by
    rw [show e₁.hom = e₀.hom ≫ hs₁.isoPullback.hom from rfl, Category.assoc]
    change e₀.hom ≫ hs₁.isoPullback.hom ≫ pullback.snd (j ≫ conjugationOver g⁻¹) (H.val.X ◁ r) = _
    rw [hs₁.isoPullback_hom_snd]
    exact h₁
  have hc₁ : IsClosedImmersion j₁.left :=
    have : IsIso (conjugationOver g⁻¹).left := (F.mapIso (conjugationOverIso g⁻¹)).isIso_hom
    IsClosedImmersion.comp j.left (conjugationOver g⁻¹).left
  have hS₁ : Smooth (j₁ ≫ snd H.val.X U).left := by
    simpa [j₁, Category.assoc] using hSj
  obtain ⟨e, d, he, hd⟩ := deformation_is_graph ha hm I hI j₁ hc₁ hS₁ e₁ he₁
  have hgps : HasSubgroupPoints j₁ := subgroup_points_conjugation (subgroup_points_pullback Q a) _
  obtain ⟨v, hv, hcv⟩ := graph_contains_conjugate_cocharacter ha D E hm I hI hgps he hd
  change r ≫ v = 1 at hv
  let j₂ := j₁ ≫ conjugationOver v⁻¹
  let b₂ := b₁ ≫ conjugationOver (r ≫ v⁻¹)
  have hs₂ := twist_square hs₁ v⁻¹
  have h₂ : e₀.hom ≫ b₂ = P.inclusion.hom.hom ▷ U₀ := by
    change e₀.hom ≫ b₁ ≫ conjugationOver (r ≫ v⁻¹) = _
    rw [← Category.assoc, h₁, GrpObj.comp_inv, hv, inv_one, conjugationOver_one, Category.comp_id]
  let e₂ := e₀ ≪≫ hs₂.isoPullback
  have he₂ : e₂.hom ≫ pullback.snd j₂ (H.val.X ◁ r) = P.inclusion.hom.hom ▷ U₀ := by
    rw [show e₂.hom = e₀.hom ≫ hs₂.isoPullback.hom from rfl, Category.assoc]
    change e₀.hom ≫ hs₂.isoPullback.hom ≫ pullback.snd (j₁ ≫ conjugationOver v⁻¹) (H.val.X ◁ r) = _
    rw [hs₂.isoPullback_hom_snd]
    exact h₂
  have hc₂ : IsClosedImmersion j₂.left :=
    have : IsIso (conjugationOver v⁻¹).left := (F.mapIso (conjugationOverIso v⁻¹)).isIso_hom
    IsClosedImmersion.comp j₁.left (conjugationOver v⁻¹).left
  have hS₂ : Smooth (j₂ ≫ snd H.val.X U).left := by
    simpa [j₂, Category.assoc] using hS₁
  obtain ⟨e', d', he', _⟩ := deformation_is_graph ha hm I hI j₂ hc₂ hS₂ e₂ he₂
  have ho : d' = 1 := by
    apply graph_eq_one_of_contains_cocharacter ha D E hm
      (subgroup_points_conjugation hgps v⁻¹) he'
    intro R f t
    rw [factors_conjugation_iff]
    simpa only [GrpObj.comp_inv, inv_inv] using hcv R f t
  have hf : e'.inv ≫ j₂ = P.inclusion.hom.hom ▷ U := by
    rw [he', ho, MonObj.one_comp, one_mul]
    apply CartesianMonoidalCategory.hom_ext <;> simp [P, U]
  let g' : U ⟶ H.val.X := g * (show U ⟶ H.val.X from v)
  have hj₂ : j₂ = j ≫ conjugationOver g'⁻¹ := by
    simp only [j₂, j₁, g', Category.assoc, conjugationOver_comp, mul_inv_rev]
  refine ⟨g', ⟨e'.symm, ?_⟩, ?_⟩
  · change e'.inv ≫ j = _
    rw [conjugateInclusion_eq, ← hf, hj₂, Category.assoc, Category.assoc]
    have hi := conjugationOver_mul_inv g'⁻¹
    rw [inv_inv] at hi
    rw [hi, Category.comp_id]
  · change r ≫ (g * (show U ⟶ H.val.X from v)) = g₀
    rw [MonObj.comp_mul, hg, hv, mul_one]

private theorem conjugacy_lifts : ConjugacyLiftsAcrossSquareZero.{u} := by
  intro k _ G P hP R Q _ B I hI a g₀ hg₀
  obtain ⟨c, D, hD, -, -⟩ :=
    LinearAlgebraicGroups.Relative.RationalCocharacter.rationalParabolic G P hP
  obtain ⟨g, hg, hr⟩ := conjugacy_lifts_for_limit_parabolic G hP.1.1 c D Q a I hI g₀
    (conjugates_of_sameSubgroup hD hg₀)
  exact ⟨g, conjugates_of_sameSubgroup ⟨hD.2, hD.1⟩ hg, hr⟩

/-- The scheme of conjugacies of a parabolic with a family of its geometric type. -/
theorem parabolicTransporter : ParabolicTransporter.{u} :=
  parabolicTransporter_of_conjugacy_lifting conjugacy_lifts

/-- The right homogeneous quotient represents parabolic families of the given type. -/
theorem parabolicFamilyRepresentability : ParabolicFamilyRepresentability.{u} :=
  representability_of_transporter parabolicTransporter
    LinearAlgebraicGroups.Flag.StandardParabolics.groundFieldParabolicNormalizer

end

end LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
