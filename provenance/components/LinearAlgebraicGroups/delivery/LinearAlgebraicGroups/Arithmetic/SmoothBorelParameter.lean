import Specs.LinearAlgebraicGroups.Arithmetic.SmoothBorelParameter
import LinearAlgebraicGroups.Classification.IntegralRealization
import LinearAlgebraicGroups.Flag.BruhatCells
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.TotallySplit
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Spectrum.Prime.RingHom

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct LaurentPolynomial

universe u v

namespace LinearAlgebraicGroups.Arithmetic.SmoothBorelParameter

open Specs.SmoothBorelParameter
open Specs.GeometricBorelConjugacy (IsBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

/-- The algebraic-closure fibre of a Borel family over a field gives its rational Borel. -/
theorem fieldBorel : FieldBorel.{u} := by
  intro S G k _ a B hB
  exact hB (AlgebraicClosure k) (fieldSpecMap k (AlgebraicClosure k))

/-- The smoothness of a geometric Borel descends through the field extension. -/
theorem fieldBorelSmooth : FieldBorelSmooth.{u} := by
  intro k _ G B hB
  obtain ⟨_, h⟩ := hB
  apply MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := fieldSpecMap k (AlgebraicClosure k))
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact h.1.1

/-- Field points of a presentation identify the Borel subgroups in the original
fibre up to group isomorphism commuting with their inclusions. -/
theorem fieldComparison : FieldComparison.{u} := by
  intro S G P k _ a
  refine ⟨fun x ↦ fieldBorel _ (P.pullbackBorel _ x), ?_⟩
  intro B hB
  obtain ⟨x, e, he⟩ := P.fieldClassifies k a B hB
  refine ⟨x, ⟨e, he⟩, ?_⟩
  rintro y ⟨d, hd⟩
  let BX := P.universal.pullback x
  have h := P.represents (Over.mk a) BX (P.pullbackBorel _ x)
  have hxx : SameFamily (P.universal.pullback x) BX := ⟨Iso.refl _, Category.id_comp _⟩
  have hyx : SameFamily (P.universal.pullback y) BX := by
    refine ⟨d ≪≫ e.symm, ?_⟩
    change (d.hom ≫ e.inv) ≫ BX.inclusion = (P.universal.pullback y).inclusion
    dsimp only [BX]
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, hd]
  exact h.unique hyx hxx


open MorphismProperty

/-- The finite étale splitting algebra gives an étale faithfully flat
quasi-compact cover on schemes. -/
theorem splittingCover (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] [Algebra.Etale R A] :
    Surjective (algebraSpecMap R A) ∧ Flat (algebraSpecMap R A) ∧
    QuasiCompact (algebraSpecMap R A) ∧ Etale (algebraSpecMap R A) := by
  have hflat : Flat (algebraSpecMap R A) ∧ Surjective (algebraSpecMap R A) :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R A))).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have het : Etale (algebraSpecMap R A) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.mpr inferInstance)
  exact ⟨hflat.2, hflat.1, inferInstance, het⟩

/-- A finite faithfully flat splitting algebra over a discrete valuation ring
is free as a module. -/
theorem splittingAlgebraFree (R A : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.FaithfullyFlat R A] : Module.Free R A :=
  inferInstance

section SchemeDescent

variable {S T : Scheme.{u}} {X Y Z : Over S}

private theorem isIsoOfIsIsoPullback (a : T ⟶ S) [Surjective a] [Flat a] [QuasiCompact a]
    (q : X ⟶ Y) [IsIso ((Over.pullback a).map q)] : IsIso q := by
  have h : IsIso q.left := of_isPullback_of_descendsAlong (P := isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (pullbackMapSquare a q)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    (by change IsIso ((Over.pullback a).map q).left; infer_instance)
  have : IsIso ((Over.forget S).map q) := h
  exact isIso_of_reflects_iso q (Over.forget S)

set_option backward.isDefEq.respectTransparency false in
private theorem factorsOfFactorsPullback (a : T ⟶ S) [Surjective a] [Flat a] [QuasiCompact a]
    (i : Z ⟶ Y) [Mono i] (f : X ⟶ Y)
    (h : ∃ g : (Over.pullback a).obj X ⟶ (Over.pullback a).obj Z,
      g ≫ (Over.pullback a).map i = (Over.pullback a).map f) :
    ∃ g : X ⟶ Z, g ≫ i = f := by
  let F := Over.pullback a
  obtain ⟨g, hg⟩ := h
  let p := pullback.fst f i
  let q := pullback.snd f i
  have hp := (IsPullback.of_hasPullback f i).map F
  change IsPullback (F.map p) (F.map q) (F.map f) (F.map i) at hp
  have hmono : Mono (F.map p) := hp.mono_fst_of_mono
  let s := hp.lift (𝟙 (F.obj X)) g (by simpa using hg.symm)
  have hsec : IsSplitEpi (F.map p) := IsSplitEpi.mk' ⟨s, hp.lift_fst _ _ _⟩
  have hiso : IsIso (F.map p) := isIso_of_mono_of_isSplitEpi _
  have hpi : IsIso p := isIsoOfIsIsoPullback a p
  exact ⟨inv p ≫ q, by rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- Smoothness descends once the underlying scheme has been descended. -/
theorem smoothOfSmoothPullback (a : T ⟶ S) [Surjective a] [Flat a] [QuasiCompact a]
    (X : Over S) (h : Smooth ((Over.pullback a).obj X).hom) : Smooth X.hom :=
  of_pullback_snd_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h


section Monomorphism

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {V W : C} [GrpObj W]

@[instance_reducible]
private def groupObjectOfOperations (i : V ⟶ W) [Mono i]
    (e : 𝟙_ C ⟶ V) (m : V ⊗ V ⟶ V) (v : V ⟶ V)
    (he : e ≫ i = η[W]) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[W]) (hv : v ≫ i = i ≫ ι[W]) :
    GrpObj V where
  one := e
  mul := m
  inv := v
  one_mul := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hm, ← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
      he, Category.id_comp]
    rw [tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
  mul_one := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hm, ← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
      he, Category.id_comp]
    rw [tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
  mul_assoc := by
    apply (cancel_mono i).mp
    have hL : (m ▷ V) ≫ (i ⊗ₘ i) = ((i ⊗ₘ i) ⊗ₘ i) ≫ (μ[W] ▷ W) := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hm]
    have hR : (V ◁ m) ≫ (i ⊗ₘ i) = (i ⊗ₘ (i ⊗ₘ i)) ≫ (W ◁ μ[W]) := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hm]
    simp only [Category.assoc, hm, reassoc_of% hL, reassoc_of% hR]
    rw [← associator_naturality_assoc, MonObj.mul_assoc]
  left_inv := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, he, hm, lift_map_assoc, hv, Category.id_comp]
    have hi : lift (i ≫ ι[W]) i = i ≫ lift ι[W] (𝟙 W) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hi, Category.assoc, GrpObj.left_inv, ← Category.assoc, toUnit_unique (i ≫ toUnit W)]
  right_inv := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, he, hm, lift_map_assoc, hv, Category.id_comp]
    have hi : lift i (i ≫ ι[W]) = i ≫ lift (𝟙 W) ι[W] := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hi, Category.assoc, GrpObj.right_inv, ← Category.assoc, toUnit_unique (i ≫ toUnit W)]

/-- An isomorphism of the underlying objects over a common group object
preserves the subgroup operations. -/
private def subgroupIso {G H H' : Grp C} (i : H ⟶ G) (j : H' ⟶ G) [Mono j.hom.hom]
    (w : H.X ≅ H'.X) (hw : w.hom ≫ j.hom.hom = i.hom.hom) : H ≅ H' :=
  Grp.mkIso w
    (by
      apply (cancel_mono j.hom.hom).mp
      simp only [Category.assoc, hw, IsMonHom.one_hom])
    (by
      apply (cancel_mono j.hom.hom).mp
      simp only [Category.assoc, hw, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc])


end Monomorphism

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- A monomorphism into a group scheme carries the subgroup operations when
its pullback along a faithfully flat quasi-compact cover carries them. -/
theorem groupOfBaseChangedSubgroup {G : Grp (Over S)} (a : T ⟶ S)
    [Surjective a] [Flat a] [QuasiCompact a]
    {Z : Over S} (i : Z ⟶ G.X) [Mono i]
    [GrpObj ((Over.pullback a).obj Z)] [IsMonHom ((Over.pullback a).map i)] :
    ∃ (Q : Grp (Over S)) (j : Q ⟶ G) (e : Q.X ≅ Z), j.hom.hom = e.hom ≫ i := by
  let F := Over.pullback a
  have he' : ∃ e' : F.obj (𝟙_ (Over S)) ⟶ F.obj Z, e' ≫ F.map i = F.map η[G.X] := by
    refine ⟨(Functor.Monoidal.εIso F).inv ≫ η[F.obj Z], ?_⟩
    rw [Category.assoc, IsMonHom.one_hom]
    change (Functor.Monoidal.εIso F).inv ≫ (Functor.Monoidal.εIso F).hom ≫ F.map η[G.X] = _
    exact Iso.inv_hom_id_assoc _ _
  have hm' : ∃ m' : F.obj (Z ⊗ Z) ⟶ F.obj Z,
      m' ≫ F.map i = F.map ((i ⊗ₘ i) ≫ μ[G.X]) := by
    refine ⟨(Functor.Monoidal.μIso F Z Z).inv ≫ μ[F.obj Z], ?_⟩
    rw [Category.assoc, IsMonHom.mul_hom]
    change (Functor.Monoidal.μIso F Z Z).inv ≫
      (F.map i ⊗ₘ F.map i) ≫ Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X] = _
    rw [← Category.assoc (F.map i ⊗ₘ F.map i), Functor.LaxMonoidal.μ_natural]
    rw [Category.assoc, Functor.map_comp]
    change (Functor.Monoidal.μIso F Z Z).inv ≫
      (Functor.Monoidal.μIso F Z Z).hom ≫ (F.map (i ⊗ₘ i) ≫ F.map μ[G.X]) = _
    exact Iso.inv_hom_id_assoc _ _
  have hv' : ∃ v' : F.obj Z ⟶ F.obj Z, v' ≫ F.map i = F.map (i ≫ ι[G.X]) := by
    refine ⟨ι[F.obj Z], ?_⟩
    rw [GrpObj.inv_hom, F.map_comp]
    rfl
  obtain ⟨e, he⟩ := factorsOfFactorsPullback a i η[G.X] he'
  obtain ⟨m, hm⟩ := factorsOfFactorsPullback a i ((i ⊗ₘ i) ≫ μ[G.X]) hm'
  obtain ⟨v, hv⟩ := factorsOfFactorsPullback a i (i ≫ ι[G.X]) hv'
  let : GrpObj Z := groupObjectOfOperations i e m v he hm hv
  exact ⟨Grp.mk Z, Grp.homMk'' i he hm, Iso.refl _, (Category.id_comp i).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- Once a closed subscheme of the ambient group is descended, its subgroup
structure and smoothness descend with the original subgroup inclusion. -/
theorem smoothClosedSubgroupOfBaseChange {S T : Scheme.{u}} (a : T ⟶ S)
    [Surjective a] [Flat a] [QuasiCompact a] {G : Grp (Over S)} {Z : Over S}
    (i : Z ⟶ G.X) [IsClosedImmersion i.left]
    [GrpObj ((Over.pullback a).obj Z)] [IsMonHom ((Over.pullback a).map i)]
    (hs : Smooth ((Over.pullback a).obj Z).hom) :
    ∃ (Q : Grp (Over S)) (q : Q ⟶ G) (e : Q.X ≅ Z),
      q.hom.hom = e.hom ≫ i ∧ Smooth Q.X.hom ∧ IsClosedImmersion q.hom.hom.left ∧
        ∃ d : (changeBase a).obj Q ≅ Grp.mk ((Over.pullback a).obj Z),
          d.hom ≫ Grp.ofHom ((Over.pullback a).map i) = (changeBase a).map q := by
  have : Mono i := Over.mono_of_mono_left i
  obtain ⟨Q, q, e, hq⟩ := groupOfBaseChangedSubgroup a i
  have hsZ : Smooth Z.hom := smoothOfSmoothPullback a Z hs
  have hsQ : Smooth Q.X.hom := by
    rw [← Over.w e.hom]
    have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    infer_instance
  refine ⟨Q, q, e, hq, hsQ, ?_, ?_⟩
  · rw [hq]
    change IsClosedImmersion (e.hom.left ≫ i.left)
    have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    infer_instance
  · let F := Over.pullback a
    let j : Grp.mk (F.obj Z) ⟶ (changeBase a).obj G := Grp.ofHom (F.map i)
    have hj : Mono j.hom.hom := by change Mono (F.map i); infer_instance
    let w := F.mapIso e
    have hw : w.hom ≫ j.hom.hom = ((changeBase a).map q).hom.hom := by
      change F.map e.hom ≫ F.map i = F.map q.hom.hom
      rw [hq, Functor.map_comp]
    let d := subgroupIso ((changeBase a).map q) j w hw
    refine ⟨d, ?_⟩
    apply Grp.hom_ext
    exact hw


end SchemeDescent

section IdealDescent

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private def coefficientOnFirstFactor (l : A →ₗ[R] R) : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap.comp (TensorProduct.map l (LinearMap.id : A →ₗ[R] A))

private theorem coefficientOnFirstFactor_tmul (l : A →ₗ[R] R) (a b : A) :
    coefficientOnFirstFactor l (a ⊗ₜ[R] b) = l a • b := by
  simp [coefficientOnFirstFactor]

private theorem coefficientOnFirstFactor_mul_includeRight (l : A →ₗ[R] R)
    (x : A ⊗[R] A) (a : A) :
    coefficientOnFirstFactor l (x * Algebra.TensorProduct.includeRight (R := R) a) =
      coefficientOnFirstFactor l x * a := by
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, coefficientOnFirstFactor_tmul, coefficientOnFirstFactor_tmul, smul_mul_assoc]
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]

private theorem coefficientOnFirstFactor_mem (I : Ideal A) (l : A →ₗ[R] R)
    {x : A ⊗[R] A} (hx : x ∈ I.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) :
    coefficientOnFirstFactor l x ∈ I := by
  suffices ∀ c : A ⊗[R] A, coefficientOnFirstFactor l (c * x) ∈ I by
    simpa using this 1
  change x ∈ Submodule.span (A ⊗[R] A) ((Algebra.TensorProduct.includeRight (R := R) (A := A)) '' (I : Set A)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      rw [coefficientOnFirstFactor_mul_includeRight]
      exact I.mul_mem_left _ ha
  | zero => simp
  | add x y _ _ hx hy =>
      intro c
      rw [mul_add, map_add]
      exact I.add_mem (hx c) (hy c)
  | smul a y _ hy =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (c * a)

/-- A closed subscheme over a finite free cover descends when its two
base-changed ideals agree. The descended ideal is its contraction. -/
theorem ideal_eq_map_comap_of_descent [Module.Free R A] [Module.Finite R A]
    (I : Ideal A)
    (h : I.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := A)) =
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) :
    (I.comap (algebraMap R A)).map (algebraMap R A) = I := by
  classical
  apply le_antisymm Ideal.map_comap_le
  intro a ha
  let b := Module.Free.chooseBasis R A
  have hc : ∀ i, algebraMap R A (b.repr a i) ∈ I := by
    intro i
    have hin : Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := A) a ∈
        I.map (Algebra.TensorProduct.includeRight (R := R) (A := A)) :=
      h ▸ Ideal.mem_map_of_mem (Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := A)) ha
    have hcoeff := coefficientOnFirstFactor_mem I (b.coord i) hin
    simpa [Algebra.TensorProduct.includeLeft_apply, coefficientOnFirstFactor_tmul,
      Algebra.smul_def, Module.Basis.coord_apply] using hcoeff
  rw [← b.sum_repr a]
  apply Submodule.sum_mem
  intro i _
  rw [Algebra.smul_def, mul_comm]
  apply Ideal.mul_mem_left
  exact Ideal.mem_map_of_mem (algebraMap R A) (hc i)

end IdealDescent

section ClosedSubschemeDescent

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private abbrev quotientSpecMap {R : Type u} [CommRing R] (I : Ideal R) :
    ringSpec (R ⧸ I) ⟶ ringSpec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

set_option backward.isDefEq.respectTransparency false in
private theorem closedSubschemePullback (J : Ideal R) :
    ∃ q : ringSpec (A ⧸ J.map (algebraMap R A)) ⟶ ringSpec (R ⧸ J),
      IsPullback (quotientSpecMap (J.map (algebraMap R A))) q
        (algebraSpecMap R A) (quotientSpecMap J) := by
  let I := J.map (algebraMap R A)
  let E := Algebra.TensorProduct.quotIdealMapEquivTensorQuot A J
  let e := (Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (pullbackSpecIso R A (R ⧸ J)).symm
  have h : e.hom ≫ pullback.fst (algebraSpecMap R A) (quotientSpecMap J) = quotientSpecMap I := by
    change (Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫
      (pullbackSpecIso R A (R ⧸ J)).inv) ≫ pullback.fst _ _ = _
    rw [Category.assoc, pullbackSpecIso_inv_fst R A (R ⧸ J), ← Spec.map_comp]
    congr 1
    ext a
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A J).symm
      (a ⊗ₜ[R] Ideal.Quotient.mk J 1) = Ideal.Quotient.mk I a
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, one_smul]
    rfl
  let q := e.hom ≫ pullback.snd (algebraSpecMap R A) (quotientSpecMap J)
  refine ⟨q, IsPullback.of_iso_pullback ⟨?_⟩ e h ?_⟩
  · dsimp only [q]
    rw [← h, Category.assoc, Category.assoc, pullback.condition]
  · rfl

/-- A closed subscheme of an affine finite free cover with matching overlap
ideals is the pullback of the closed subscheme defined by its contracted ideal. -/
theorem affineClosedSubschemeDescent [Module.Free R A] [Module.Finite R A]
    (I : Ideal A)
    (h : I.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := A)) =
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := A))) :
    ∃ q : ringSpec (A ⧸ I) ⟶ ringSpec (R ⧸ I.comap (algebraMap R A)),
      IsPullback (quotientSpecMap I) q
        (algebraSpecMap R A) (quotientSpecMap (I.comap (algebraMap R A))) := by
  let J := I.comap (algebraMap R A)
  have hI : J.map (algebraMap R A) = I := ideal_eq_map_comap_of_descent I h
  have hbase (I' : Ideal A) (e : J.map (algebraMap R A) = I') :
      ∃ q : ringSpec (A ⧸ I') ⟶ ringSpec (R ⧸ J),
        IsPullback (quotientSpecMap I') q (algebraSpecMap R A) (quotientSpecMap J) := by
    subst I'
    exact closedSubschemePullback J
  exact hbase I hI

end ClosedSubschemeDescent

section AffineDescent

open Algebra.TensorProduct

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

private def tensorMultiplication : A ⊗[R] B →ₐ[A] B :=
  lift (Algebra.ofId A B) (AlgHom.id R B) fun _ _ ↦ Commute.all _ _

/-- An affine algebra descent datum expressed on the two tensor extensions.
The counit is the restriction to the diagonal and the cocycle is on three factors. -/
structure AffineDescentData (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] where
  coaction : B →ₐ[A] A ⊗[R] B
  counit : ∀ b, tensorMultiplication (coaction b) = b
  cocycle : ∀ b,
    map (AlgHom.id A A) (coaction.restrictScalars R) (coaction b) =
      map (AlgHom.id A A) (includeRight (A := A)) (coaction b)

/-- The algebra of coordinates fixed by the affine descent datum. -/
def AffineDescentData.fixedAlgebra (d : AffineDescentData R A B) : Subalgebra R B :=
  AlgHom.equalizer (d.coaction.restrictScalars R) (includeRight (A := A))

private theorem tensorMultiplication_map_coaction (d : AffineDescentData R A B)
    (x : A ⊗[R] B) :
    tensorMultiplication (map (AlgHom.id A A) (d.coaction.restrictScalars R) x) =
      d.coaction (tensorMultiplication x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply, tensorMultiplication,
        lift_tmul, Algebra.ofId_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Algebra A B] [IsScalarTower R A B] in
private theorem tensorMultiplication_map_includeRight (x : A ⊗[R] B) :
    tensorMultiplication (map (AlgHom.id A A) (includeRight (A := A)) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      rw [map_tmul, AlgHom.id_apply, includeRight_apply, tensorMultiplication, lift_tmul,
        AlgHom.id_apply, Algebra.ofId_apply]
      change (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) = _
      rw [tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

private def AffineDescentData.coactionEquiv (d : AffineDescentData R A B) :
    B ≃ₐ[A] AlgHom.equalizer
      (map (AlgHom.id A A) (d.coaction.restrictScalars R))
      (map (AlgHom.id A A) (includeRight (A := A))) := by
  let fixed := AlgHom.equalizer
    (map (AlgHom.id A A) (d.coaction.restrictScalars R))
    (map (AlgHom.id A A) (includeRight (A := A)))
  let f := d.coaction.codRestrict fixed fun b ↦ (AlgHom.mem_equalizer _ _ _).mpr (d.cocycle b)
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y h
    exact (d.counit x).symm.trans
      ((congrArg (tensorMultiplication (R := R) (A := A) (B := B))
        (congrArg Subtype.val h)).trans (d.counit y))
  · intro x
    refine ⟨tensorMultiplication x.val, Subtype.ext ?_⟩
    have hx := congrArg (tensorMultiplication (R := R) (A := A) (B := A ⊗[R] B)) x.property
    change d.coaction (tensorMultiplication x.val) = x.val
    rwa [tensorMultiplication_map_coaction d, tensorMultiplication_map_includeRight] at hx

/-- The fixed algebra descends the original affine algebra along a flat cover. -/
def AffineDescentData.baseChangeIso (d : AffineDescentData R A B) [Module.Flat R A] :
    A ⊗[R] d.fixedAlgebra ≃ₐ[A] B :=
  (AlgHom.tensorEqualizerEquiv A A
    (d.coaction.restrictScalars R) (includeRight (A := A))).trans d.coactionEquiv.symm

end AffineDescent

section GradedQuotient

variable {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

/-- The Laurent coefficients of an action of the multiplicative group.
Each coefficient is homogeneous of its indicated degree, and their sum
recovers the original coordinate. -/
structure LaurentGrading (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] where
  coaction : A →ₐ[R] LaurentPolynomial A
  homogeneous : ∀ x n, coaction ((coaction x).coeff n) =
    AddMonoidAlgebra.single n ((coaction x).coeff n)
  sum_coefficients : ∀ x, (coaction x).coeff.sum (fun _ a ↦ a) = x

/-- The defining ideal of the locus where the Laurent orbit extends over zero. -/
def LaurentGrading.negativeIdeal (d : LaurentGrading R A) : Ideal A :=
  Ideal.span {a | ∃ x n, n < 0 ∧ a = (d.coaction x).coeff n}

private theorem LaurentGrading.induction (d : LaurentGrading R A) {P : A → Prop}
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hdegree : ∀ x n, d.coaction x = AddMonoidAlgebra.single n x → P x) (x : A) :
    P x := by
  rw [← d.sum_coefficients x]
  change P (∑ n ∈ (d.coaction x).coeff.support, (d.coaction x).coeff n)
  exact Finset.sum_induction _ _ hadd hzero fun n _ ↦ hdegree _ n (d.homogeneous x n)

private theorem LaurentGrading.factors_iff (d : LaurentGrading R A) (f : A →ₐ[R] B) :
    d.negativeIdeal ≤ RingHom.ker f ↔
      ∀ x n, n < 0 → ((AddMonoidAlgebra.mapAlgHom ℤ f) (d.coaction x)).coeff n = 0 := by
  simp only [AddMonoidAlgebra.coeff_mapAlgHom]
  rw [LaurentGrading.negativeIdeal, Ideal.span_le]
  constructor
  · intro h x n hn
    exact h ⟨x, n, hn, rfl⟩
  · rintro h a ⟨x, n, hn, rfl⟩
    exact h x n hn

private abbrev toLaurentOver : Polynomial B →ₐ[R] LaurentPolynomial B :=
  Polynomial.toLaurentAlg.restrictScalars R

private theorem polynomialLift_iff (f : A →ₐ[R] LaurentPolynomial B) :
    (∃ p : A →ₐ[R] Polynomial B, toLaurentOver.comp p = f) ↔
      ∀ x n, n < 0 → (f x).coeff n = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩ x n hn
    exact CocharacterDynamics.coeff_toLaurent_neg (p x) hn
  · intro h
    let j : Polynomial B →ₐ[R] LaurentPolynomial B := toLaurentOver
    let e := AlgEquiv.ofInjective j Polynomial.toLaurent_injective
    let g := f.codRestrict j.range fun x ↦
      (AlgHom.mem_range j).mpr (CocharacterDynamics.exists_toLaurent_eq_iff.mpr (h x))
    refine ⟨e.symm.toAlgHom.comp g, AlgHom.ext fun x ↦ ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply (g x))

private theorem lift_of_surjective [Algebra.FormallySmooth R A]
    {C : Type u} [CommRing C] [Algebra R C] (q : B →ₐ[R] C)
    (hs : Function.Surjective q) (hker : RingHom.ker q ^ 2 = ⊥)
    (f : A →ₐ[R] C) : ∃ g : A →ₐ[R] B, q.comp g = f := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hs
  obtain ⟨g, hg⟩ := (Algebra.FormallySmooth.iff_comp_surjective.mp
    (inferInstance : Algebra.FormallySmooth R A)) (RingHom.ker q) hker
    (e.symm.toAlgHom.comp f)
  refine ⟨g, AlgHom.ext fun x ↦ ?_⟩
  exact (congrArg e (DFunLike.congr_fun hg x)).trans (e.apply_symm_apply (f x))

private theorem polynomial_ker_square_zero (I : Ideal B) (hI : I ^ 2 = ⊥) :
    RingHom.ker (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R I)) ^ 2 = ⊥ := by
  rw [pow_two, ← le_bot_iff, Ideal.mul_le]
  intro p hp q hq
  have coeff_mem (f : Polynomial B)
      (hf : f ∈ RingHom.ker (Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R I))) (n : ℕ) :
      f.coeff n ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← Ideal.Quotient.mkₐ_eq_mk R I, ← Polynomial.coeff_mapAlgHom_apply,
      RingHom.mem_ker.mp hf, Polynomial.coeff_zero]
  change p * q = 0
  ext n
  rw [Polynomial.coeff_mul, Polynomial.coeff_zero]
  apply Finset.sum_eq_zero
  intro j _
  have hm := Ideal.mul_mem_mul (coeff_mem p hp j.1) (coeff_mem q hq j.2)
  simpa only [← pow_two, hI, Submodule.mem_bot] using hm

private theorem toLaurent_map (q : B →ₐ[R] B ⧸ (I : Ideal B)) (p : Polynomial B) :
    (AddMonoidAlgebra.mapAlgHom ℤ q) p.toLaurent = (Polynomial.mapAlgHom q p).toLaurent := by
  ext n : 1
  rw [AddMonoidAlgebra.coeff_mapAlgHom]
  by_cases hn : n < 0
  · simp only [CocharacterDynamics.coeff_toLaurent_neg _ hn, map_zero]
  · lift n to ℕ using le_of_not_gt hn
    simp only [CocharacterDynamics.coeff_toLaurent_nat, Polynomial.coeff_mapAlgHom_apply]

private theorem coeff_product_of_homogeneous_mod (I : Ideal B) (hI : I ^ 2 = ⊥)
    (p q : LaurentPolynomial B) (i j : ℤ)
    (hp : ∀ n, n ≠ i → p.coeff n ∈ I) (hq : ∀ n, n ≠ j → q.coeff n ∈ I) :
    (p * q).coeff (i + j) = p.coeff i * q.coeff j := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_eq_single i]
  · simp
  · intro n _ hn
    have hh : -n + (i + j) ≠ j := by omega
    have hm := Ideal.mul_mem_mul (hp n hn) (hq _ hh)
    simpa only [← pow_two, hI, Submodule.mem_bot] using hm
  · simp

/-- For a smooth algebra, imposing that the Laurent orbit extend over zero
is formally smooth. This works over the coefficient ring itself. -/
theorem LaurentGrading.formallySmooth_quotient (d : LaurentGrading R A)
    [Algebra.FormallySmooth R A] : Algebra.FormallySmooth R (A ⧸ d.negativeIdeal) := by
  rw [Algebra.FormallySmooth.iff_comp_surjective]
  intro B _ _ I hI f
  let q := Ideal.Quotient.mkₐ R I
  let q₀ := Ideal.Quotient.mkₐ R d.negativeIdeal
  let ψ := f.comp q₀
  have hψ : d.negativeIdeal ≤ RingHom.ker ψ := by
    intro x hx
    rw [RingHom.mem_ker]
    change f (Ideal.Quotient.mk d.negativeIdeal x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  let o := (AddMonoidAlgebra.mapAlgHom ℤ ψ).comp d.coaction
  obtain ⟨p, hp⟩ := (polynomialLift_iff o).mpr ((d.factors_iff ψ).mp hψ)
  let Q := Polynomial.mapAlgHom q
  obtain ⟨g, hg⟩ := lift_of_surjective Q
    (Polynomial.map_surjective q.toRingHom (Ideal.Quotient.mkₐ_surjective R I))
    (polynomial_ker_square_zero I hI) p
  let gL : A →ₐ[R] LaurentPolynomial B := toLaurentOver.comp g
  have hchange (x : A) : (AddMonoidAlgebra.mapAlgHom ℤ q) (gL x) = o x := by
    change (AddMonoidAlgebra.mapAlgHom ℤ q) (g x).toLaurent = o x
    rw [toLaurent_map]
    exact (congrArg Polynomial.toLaurent (DFunLike.congr_fun hg x)).trans
      (DFunLike.congr_fun hp x)
  let L (x : A) := (d.coaction x).coeff.sum fun n a ↦ (gL a).coeff n
  have hdeg (x : A) (n : ℤ) (hx : d.coaction x = AddMonoidAlgebra.single n x) :
      L x = (gL x).coeff n := by
    simp only [L, hx, AddMonoidAlgebra.coeff_single]
    exact Finsupp.sum_single_index (by simp)
  have hcoeff (x : A) (i : ℤ) (hx : d.coaction x = AddMonoidAlgebra.single i x) (n : ℤ) :
      q ((gL x).coeff n) = (Finsupp.single i (ψ x)) n := by
    have he := congrArg (fun y : LaurentPolynomial (B ⧸ I) ↦ y.coeff n) (hchange x)
    simpa only [o, AlgHom.comp_apply, hx, AddMonoidAlgebra.coeff_mapAlgHom,
      AddMonoidAlgebra.mapAlgHom_single, AddMonoidAlgebra.coeff_single] using he
  have hoff (x : A) (i : ℤ) (hx : d.coaction x = AddMonoidAlgebra.single i x)
      (n : ℤ) (hn : n ≠ i) : (gL x).coeff n ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((gL x).coeff n) = 0
    rw [hcoeff x i hx n, Finsupp.single_eq_of_ne hn]
  have hzero : L 0 = 0 := by simp [L]
  have hadd (x y : A) : L (x + y) = L x + L y := by
    simp only [L, map_add, AddMonoidAlgebra.coeff_add]
    apply Finsupp.sum_add_index
    · intro n _
      simp
    · intro n _ x y
      simp
  have hmul (x y : A) : L (x * y) = L x * L y := by
    revert y
    induction x using d.induction with
    | hzero => simp [hzero]
    | hadd x y hx hy =>
        intro z
        rw [add_mul, hadd, hx, hy, hadd, add_mul]
    | hdegree x i hx =>
        intro y
        induction y using d.induction with
        | hzero => simp [hzero]
        | hadd a b ha hb => rw [mul_add, hadd, ha, hb, hadd, mul_add]
        | hdegree y j hy =>
            have hxy : d.coaction (x * y) = AddMonoidAlgebra.single (i + j) (x * y) := by
              rw [map_mul, hx, hy, AddMonoidAlgebra.single_mul_single]
            rw [hdeg _ _ hxy, hdeg _ _ hx, hdeg _ _ hy, map_mul]
            exact coeff_product_of_homogeneous_mod I hI _ _ i j (hoff x i hx) (hoff y j hy)
  have hscalar (r : R) : L (algebraMap R A r) = algebraMap R B r := by
    rw [hdeg _ 0 (by rw [AlgHom.commutes, LaurentPolynomial.algebraMap_apply]; rfl),
      AlgHom.commutes, LaurentPolynomial.algebraMap_apply]
    simp
  let ℓ : A →ₐ[R] B :=
    { toFun := L
      map_zero' := hzero
      map_add' := hadd
      map_mul' := hmul
      map_one' := by simpa using hscalar 1
      commutes' := hscalar }
  have hneg : d.negativeIdeal ≤ RingHom.ker ℓ := by
    rw [LaurentGrading.negativeIdeal, Ideal.span_le]
    rintro _ ⟨x, n, hn, rfl⟩
    change L ((d.coaction x).coeff n) = 0
    rw [hdeg _ _ (d.homogeneous x n)]
    exact CocharacterDynamics.coeff_toLaurent_neg _ hn
  have heq (x : A) : q (L x) = ψ x := by
    induction x using d.induction with
    | hzero => simp [hzero]
    | hadd x y hx hy => rw [hadd, map_add, map_add, hx, hy]
    | hdegree x i hx => rw [hdeg _ _ hx, hcoeff x i hx, Finsupp.single_eq_same]
  refine ⟨Ideal.Quotient.liftₐ d.negativeIdeal ℓ (fun x hx ↦ hneg hx), ?_⟩
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R d.negativeIdeal x
  exact heq y

/-- Over a noetherian base the affine attracting locus of a smooth algebra
is smooth. Finite presentation follows from finite type over the base. -/
theorem LaurentGrading.smooth_quotient (d : LaurentGrading R A)
    [IsNoetherianRing R] [Algebra.Smooth R A] : Algebra.Smooth R (A ⧸ d.negativeIdeal) := by
  let : Algebra.FormallySmooth R (A ⧸ d.negativeIdeal) := d.formallySmooth_quotient
  let : Algebra.FiniteType R (A ⧸ d.negativeIdeal) := Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ R d.negativeIdeal) (Ideal.Quotient.mkₐ_surjective R d.negativeIdeal)
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- If all negative weight components of a Laurent grading reduce to zero
modulo a square-zero ideal of the base, those components vanish. -/
theorem LaurentGrading.negativeIdeal_eq_bot_of_squareZero
    (d : LaurentGrading R B) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h : d.negativeIdeal ≤ I.map (algebraMap R B)) : d.negativeIdeal = ⊥ := by
  let J := I.map (algebraMap R B)
  have hJ : J.restrictScalars R = I • (⊤ : Submodule R B) := (Ideal.smul_top_eq_map I).symm
  refine le_antisymm ?_ bot_le
  rw [LaurentGrading.negativeIdeal, Ideal.span_le]
  rintro _ ⟨x, n, hn, rfl⟩
  let p : B →ₗ[R] B :=
    { toFun := fun x ↦ (d.coaction x).coeff n
      map_add' := by intro a b; simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      map_smul' := by
        intro r a
        change (d.coaction (r • a)).coeff n = r • (d.coaction a).coeff n
        rw [map_smul]
        rfl }
  have hp (b : B) : p b ∈ I • (⊤ : Submodule R B) := by
    rw [← hJ]
    apply h
    exact Ideal.subset_span ⟨b, n, hn, rfl⟩
  have hr : LinearMap.range p ≤ I • (⊤ : Submodule R B) := by
    rintro _ ⟨b, rfl⟩
    exact hp b
  have hm : Submodule.map p (I • (⊤ : Submodule R B)) ≤ ⊥ := by
    rw [Submodule.map_smul'', Submodule.map_top]
    calc
      _ ≤ I • (I • (⊤ : Submodule R B)) := Submodule.smul_mono le_rfl hr
      _ = ⊥ := by rw [smul_smul, ← pow_two, hI, Submodule.bot_smul]
  have hh : p (p x) = p x := by
    change (d.coaction ((d.coaction x).coeff n)).coeff n = (d.coaction x).coeff n
    rw [d.homogeneous x n, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  change p x ∈ (⊥ : Submodule R B)
  rw [← hh]
  exact hm ⟨p x, hp x, rfl⟩

/-- A surjective map respecting the Laurent gradings kills all negative
weights if the induced map does so modulo a square-zero ideal of scalars. -/
theorem LaurentGrading.negativeIdeal_le_ker_of_squareZero
    (d : LaurentGrading R A) (e : LaurentGrading R B) (f : A →ₐ[R] B)
    (hf : Function.Surjective f)
    (hgrad : e.coaction.comp f = (AddMonoidAlgebra.mapAlgHom ℤ f).comp d.coaction)
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h : d.negativeIdeal ≤ (I.map (algebraMap R B)).comap f.toRingHom) :
    d.negativeIdeal ≤ RingHom.ker f := by
  have hcoeff (a : A) (n : ℤ) : (e.coaction (f a)).coeff n = f ((d.coaction a).coeff n) := by
    have hh := congrArg (fun p : LaurentPolynomial B ↦ p.coeff n) (DFunLike.congr_fun hgrad a)
    simpa only [AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom] using hh
  have he : e.negativeIdeal ≤ I.map (algebraMap R B) := by
    rw [LaurentGrading.negativeIdeal, Ideal.span_le]
    rintro _ ⟨b, n, hn, rfl⟩
    obtain ⟨a, rfl⟩ := hf b
    rw [hcoeff]
    exact h (Ideal.subset_span ⟨a, n, hn, rfl⟩)
  have hz := e.negativeIdeal_eq_bot_of_squareZero I hI he
  rw [LaurentGrading.negativeIdeal, Ideal.span_le]
  rintro _ ⟨a, n, hn, rfl⟩
  change f ((d.coaction a).coeff n) = 0
  rw [← hcoeff]
  have hh : (e.coaction (f a)).coeff n ∈ e.negativeIdeal := Ideal.subset_span ⟨f a, n, hn, rfl⟩
  exact Ideal.mem_bot.mp (hz ▸ hh)

end GradedQuotient

section LaurentAction

variable {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

private def laurentEval (f : A →ₐ[R] B) (t : Bˣ) : LaurentPolynomial A →ₐ[R] B where
  toRingHom := LaurentPolynomial.eval₂ f.toRingHom t
  commutes' r := by
    show LaurentPolynomial.eval₂ f.toRingHom t (LaurentPolynomial.C (algebraMap R A r)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact f.commutes r

private def laurentVariable (A : Type u) [CommRing A] (n : ℤ) : (LaurentPolynomial A)ˣ where
  val := LaurentPolynomial.T n
  inv := LaurentPolynomial.T (-n)
  val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

private theorem laurentVariable_pow (A : Type u) [CommRing A] (n : ℤ) :
    laurentVariable A 1 ^ n = laurentVariable A n := by
  let f : Multiplicative ℤ →* (LaurentPolynomial A)ˣ :=
    { toFun := fun n ↦ laurentVariable A n.toAdd
      map_one' := Units.ext LaurentPolynomial.T_zero
      map_mul' := fun m n ↦ Units.ext (LaurentPolynomial.T_add m.toAdd n.toAdd) }
  have he : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    change Multiplicative.ofAdd (n • (1 : ℤ)) = Multiplicative.ofAdd n
    simp
  have h := (map_zpow f (Multiplicative.ofAdd (1 : ℤ)) n).symm
  rw [he] at h
  exact h

private theorem laurentEval_single (f : A →ₐ[R] B) (t : Bˣ) (n : ℤ) (a : A) :
    laurentEval f t (AddMonoidAlgebra.single n a) = f a * ↑(t ^ n) := by
  rw [LaurentPolynomial.single_eq_C_mul_T]
  exact LaurentPolynomial.eval₂_C_mul_T f.toRingHom t a n

private abbrev laurentConstants (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    A →ₐ[R] LaurentPolynomial A :=
  IsScalarTower.toAlgHom R A (LaurentPolynomial A)

private theorem laurentEval_constants (f : A →ₐ[R] B) (t : Bˣ) :
    (laurentEval f t).comp (laurentConstants R A) = f := by
  ext a : 1
  exact LaurentPolynomial.eval₂_C f.toRingHom t a

private theorem laurentEval_variable (f : A →ₐ[R] B) (t : Bˣ) :
    Units.map (laurentEval f t).toMonoidHom (laurentVariable A 1) = t := by
  apply Units.ext
  change LaurentPolynomial.eval₂ f.toRingHom t (LaurentPolynomial.T 1) = ↑t
  rw [LaurentPolynomial.eval₂_T, zpow_one]

private theorem coeff_laurentEval_mul_variable (p : LaurentPolynomial A) (n : ℤ) :
    (laurentEval (laurentConstants R (LaurentPolynomial A) |>.comp (laurentConstants R A))
      (Units.map (laurentConstants R (LaurentPolynomial A)).toMonoidHom (laurentVariable A 1) *
        laurentVariable (LaurentPolynomial A) 1) p).coeff n =
      AddMonoidAlgebra.single n (p.coeff n) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      rw [hp, hq, AddMonoidAlgebra.single_add]
  | C_mul_T m a =>
      rw [← LaurentPolynomial.single_eq_C_mul_T, laurentEval_single, mul_zpow,
        ← map_zpow, laurentVariable_pow, laurentVariable_pow]
      change (LaurentPolynomial.C (LaurentPolynomial.C a) *
        (LaurentPolynomial.C (LaurentPolynomial.T m) *
          LaurentPolynomial.T m)).coeff n = _
      rw [← mul_assoc, ← map_mul, ← LaurentPolynomial.single_eq_C_mul_T]
      by_cases h : m = n
      · subst m
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
          AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
          LaurentPolynomial.single_eq_C_mul_T]
      · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne (Ne.symm h),
          AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne (Ne.symm h),
          AddMonoidAlgebra.single_zero]

private theorem laurentEval_one (p : LaurentPolynomial A) :
    laurentEval (AlgHom.id R A) 1 p = p.coeff.sum (fun _ a ↦ a) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add]
      exact (Finsupp.sum_add_index (by simp) (by simp)).symm
  | C_mul_T n a =>
      rw [← LaurentPolynomial.single_eq_C_mul_T, laurentEval_single,
        one_zpow, Units.val_one, mul_one, AddMonoidAlgebra.coeff_single]
      exact (Finsupp.sum_single_index (h := fun (_ : ℤ) (a : A) ↦ a) rfl).symm

/-- The two Laurent variables in the action law force the weight decomposition. -/
private def LaurentGrading.ofCoaction (α : A →ₐ[R] LaurentPolynomial A)
    (one : (laurentEval (AlgHom.id R A) 1).comp α = AlgHom.id R A)
    (mul : (AddMonoidAlgebra.mapAlgHom ℤ α).comp α =
      (laurentEval (laurentConstants R (LaurentPolynomial A) |>.comp (laurentConstants R A))
        (Units.map (laurentConstants R (LaurentPolynomial A)).toMonoidHom (laurentVariable A 1) *
          laurentVariable (LaurentPolynomial A) 1)).comp α) :
    LaurentGrading R A where
  coaction := α
  homogeneous x n := by
    have h := congrArg (fun g : A →ₐ[R] LaurentPolynomial (LaurentPolynomial A) ↦ (g x).coeff n) mul
    simpa only [AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom,
      coeff_laurentEval_mul_variable] using h
  sum_coefficients x := (laurentEval_one (R := R) (α x)).symm.trans (DFunLike.congr_fun one x)

end LaurentAction

section AffineCocharacter

variable {R : Type u} [CommRing R]

private abbrev ringAlgebraSpec (R : Type u) [CommRing R] :=
  algSpec (CommRingCat.of R)

private abbrev coordSpec (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :=
  (ringAlgebraSpec R).obj (op (CommAlgCat.of R A))

private abbrev coordSpecMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) : coordSpec R B ⟶ coordSpec R A :=
  (ringAlgebraSpec R).map (CommAlgCat.ofHom f).op

private theorem coordSpecMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    coordSpecMap (g.comp f) = coordSpecMap g ≫ coordSpecMap f :=
  Functor.map_comp (ringAlgebraSpec R) (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op

private abbrev affinePoints (G : Grp (Over (ringSpec R))) (B : CommAlgCat.{u} R) :=
  (ringAlgebraSpec R).obj (op B) ⟶ G.X

private def mapAffinePoints (G : Grp (Over (ringSpec R))) {B C : CommAlgCat.{u} R}
    (f : B ⟶ C) : affinePoints G B →* affinePoints G C :=
  (((ringAlgebraSpec R).rightOp ⋙ yonedaGrp.obj G).map f).hom

private theorem mapAffinePoints_apply (G : Grp (Over (ringSpec R))) {B C : CommAlgCat.{u} R}
    (f : B ⟶ C) (g : affinePoints G B) :
    mapAffinePoints G f g = (ringAlgebraSpec R).map f.op ≫ g := rfl

/-- A cocharacter on affine test algebras, with naturality on every algebra. -/
structure UnitCocharacter (G : Grp (Over (ringSpec R))) where
  point : (B : CommAlgCat.{u} R) → Bˣ →* affinePoints G B
  natural : ∀ {B C : CommAlgCat.{u} R} (f : B ⟶ C) (t : Bˣ),
    mapAffinePoints G f (point B t) = point C (Units.map f.hom.toMonoidHom t)

variable {G : Grp (Over (ringSpec R))} {A B C : Type u}
  [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

private def pointCoordinates (e : coordSpec R A ≅ G.X) :
    (coordSpec R B ⟶ G.X) ≃ (A →ₐ[R] B) where
  toFun g := ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage (g ≫ e.inv)).unop.hom
  invFun f := coordSpecMap f ≫ e.hom
  left_inv g := by
    change (ringAlgebraSpec R).map
      ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage (g ≫ e.inv)) ≫ e.hom = g
    rw [(algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  right_inv f := by
    change ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
      ((coordSpecMap f ≫ e.hom) ≫ e.inv)).unop.hom = f
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact congrArg (fun g : op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R A) ↦ g.unop.hom)
      ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage_map (CommAlgCat.ofHom f).op)

private theorem pointCoordinates_natural (e : coordSpec R A ≅ G.X)
    (f : B →ₐ[R] C) (g : coordSpec R B ⟶ G.X) :
    pointCoordinates e (coordSpecMap f ≫ g) = f.comp (pointCoordinates e g) := by
  apply (pointCoordinates e).symm.injective
  rw [Equiv.symm_apply_apply]
  change coordSpecMap f ≫ g = coordSpecMap (f.comp (pointCoordinates e g)) ≫ e.hom
  rw [coordSpecMap_comp, Category.assoc]
  exact congrArg (coordSpecMap f ≫ ·) ((pointCoordinates e).symm_apply_apply g).symm

private def conjugatePoint (c : UnitCocharacter G) (B : CommAlgCat.{u} R) (t : Bˣ) :
    affinePoints G B ≃* affinePoints G B :=
  MulAut.conj (c.point B t)

private theorem conjugatePoint_mul (c : UnitCocharacter G) (B : CommAlgCat.{u} R)
    (s t : Bˣ) (g : affinePoints G B) :
    conjugatePoint c B (s * t) g = conjugatePoint c B s (conjugatePoint c B t g) := by
  change c.point B (s * t) * g * (c.point B (s * t))⁻¹ =
    c.point B s * (c.point B t * g * (c.point B t)⁻¹) * (c.point B s)⁻¹
  simp only [map_mul, mul_inv_rev, mul_assoc]

private theorem conjugatePoint_natural (c : UnitCocharacter G)
    (f : B →ₐ[R] C) (t : Bˣ) (g : coordSpec R B ⟶ G.X) :
    coordSpecMap f ≫ conjugatePoint c (CommAlgCat.of R B) t g =
      conjugatePoint c (CommAlgCat.of R C) (Units.map f.toMonoidHom t) (coordSpecMap f ≫ g) := by
  change mapAffinePoints G (CommAlgCat.ofHom f)
    (c.point (CommAlgCat.of R B) t * g * (c.point (CommAlgCat.of R B) t)⁻¹) = _
  rw [map_mul, map_mul, map_inv, c.natural, mapAffinePoints_apply]
  rfl

private def coactionOfCocharacter (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G) :
    A →ₐ[R] LaurentPolynomial A :=
  pointCoordinates e
    (conjugatePoint c (CommAlgCat.of R (LaurentPolynomial A)) (laurentVariable A 1)
      (coordSpecMap (laurentConstants R A) ≫ e.hom))

private theorem coactionOfCocharacter_eval (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G)
    (f : A →ₐ[R] B) (t : Bˣ) :
    (laurentEval f t).comp (coactionOfCocharacter e c) =
      pointCoordinates e (conjugatePoint c (CommAlgCat.of R B) t (coordSpecMap f ≫ e.hom)) := by
  rw [coactionOfCocharacter, ← pointCoordinates_natural, conjugatePoint_natural,
    laurentEval_variable, ← Category.assoc, ← coordSpecMap_comp, laurentEval_constants]

private theorem laurentEval_variable_eq_map (f : A →ₐ[R] B) :
    laurentEval ((laurentConstants R B).comp f) (laurentVariable B 1) =
      AddMonoidAlgebra.mapAlgHom ℤ f := by
  apply AlgHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a =>
      rw [← LaurentPolynomial.single_eq_C_mul_T, laurentEval_single,
        laurentVariable_pow, AddMonoidAlgebra.mapAlgHom_single, LaurentPolynomial.single_eq_C_mul_T]
      rfl

private theorem coactionOfCocharacter_one (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G) :
    (laurentEval (AlgHom.id R A) 1).comp (coactionOfCocharacter e c) = AlgHom.id R A := by
  rw [coactionOfCocharacter_eval]
  have h : conjugatePoint c (CommAlgCat.of R A) 1 (coordSpecMap (AlgHom.id R A) ≫ e.hom) =
      coordSpecMap (AlgHom.id R A) ≫ e.hom := by
    change c.point _ 1 * _ * (c.point _ 1)⁻¹ = _
    rw [map_one, one_mul, inv_one, mul_one]
  rw [h]
  exact (pointCoordinates e).apply_symm_apply (AlgHom.id R A)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem coactionOfCocharacter_mul (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G) :
    (AddMonoidAlgebra.mapAlgHom ℤ (coactionOfCocharacter e c)).comp (coactionOfCocharacter e c) =
      (laurentEval (laurentConstants R (LaurentPolynomial A) |>.comp (laurentConstants R A))
        (Units.map (laurentConstants R (LaurentPolynomial A)).toMonoidHom (laurentVariable A 1) *
          laurentVariable (LaurentPolynomial A) 1)).comp (coactionOfCocharacter e c) := by
  let s := Units.map (laurentConstants R (LaurentPolynomial A)).toMonoidHom (laurentVariable A 1)
  let t := laurentVariable (LaurentPolynomial A) 1
  rw [← laurentEval_variable_eq_map, coactionOfCocharacter_eval, coactionOfCocharacter_eval]
  apply congrArg (pointCoordinates e (B := LaurentPolynomial (LaurentPolynomial A)))
  change conjugatePoint c _ t
    (coordSpecMap ((laurentConstants R (LaurentPolynomial A)).comp (coactionOfCocharacter e c)) ≫ e.hom) =
    conjugatePoint c _ (s * t)
      (coordSpecMap ((laurentConstants R (LaurentPolynomial A)).comp (laurentConstants R A)) ≫ e.hom)
  rw [coordSpecMap_comp, Category.assoc]
  have h : coordSpecMap (coactionOfCocharacter e c) ≫ e.hom =
      conjugatePoint c (CommAlgCat.of R (LaurentPolynomial A)) (laurentVariable A 1)
        (coordSpecMap (laurentConstants R A) ≫ e.hom) :=
    (pointCoordinates e (B := LaurentPolynomial A)).symm_apply_apply
      (conjugatePoint c (CommAlgCat.of R (LaurentPolynomial A)) (laurentVariable A 1)
        (coordSpecMap (laurentConstants R A) ≫ e.hom))
  rw [h, conjugatePoint_natural, coordSpecMap_comp, Category.assoc, mul_comm s t]
  let g : coordSpec R (LaurentPolynomial (LaurentPolynomial A)) ⟶ G.X :=
    coordSpecMap (laurentConstants R (LaurentPolynomial A)) ≫
      (coordSpecMap (laurentConstants R A) ≫ e.hom)
  exact (conjugatePoint_mul c (CommAlgCat.of R (LaurentPolynomial (LaurentPolynomial A)))
    t s g).symm

/-- Conjugation by the cocharacter gives a grading of the coordinate algebra. -/
private def LaurentGrading.ofCocharacter (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G) :
    LaurentGrading R A :=
  .ofCoaction (coactionOfCocharacter e c) (coactionOfCocharacter_one e c)
    (coactionOfCocharacter_mul e c)

end AffineCocharacter

section AttractingSubgroup

variable {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}

private def orbitPoint (c : UnitCocharacter G) (B : Type u) [CommRing B] [Algebra R B] :
    (coordSpec R B ⟶ G.X) →* (coordSpec R (LaurentPolynomial B) ⟶ G.X) :=
  (conjugatePoint c (CommAlgCat.of R (LaurentPolynomial B)) (laurentVariable B 1)).toMonoidHom.comp
    (mapAffinePoints G (CommAlgCat.ofHom (laurentConstants R B)))

/-- The orbit for conjugation extends from the punctured line to the affine line. -/
def HasPolynomialOrbit (c : UnitCocharacter G) {B : Type u} [CommRing B] [Algebra R B]
    (g : coordSpec R B ⟶ G.X) : Prop :=
  ∃ h : coordSpec R (Polynomial B) ⟶ G.X,
    coordSpecMap (toLaurentOver (R := R) (B := B)) ≫ h = orbitPoint c B g

private theorem HasPolynomialOrbit.one (c : UnitCocharacter G) (B : Type u)
    [CommRing B] [Algebra R B] : HasPolynomialOrbit c (1 : coordSpec R B ⟶ G.X) := by
  exact ⟨1, (MonObj.comp_one _).trans (map_one (orbitPoint c B)).symm⟩

private theorem HasPolynomialOrbit.mul (c : UnitCocharacter G) {B : Type u}
    [CommRing B] [Algebra R B] {g h : coordSpec R B ⟶ G.X}
    (hg : HasPolynomialOrbit c g) (hh : HasPolynomialOrbit c h) : HasPolynomialOrbit c (g * h) := by
  obtain ⟨p, hp⟩ := hg
  obtain ⟨q, hq⟩ := hh
  exact ⟨p * q, by rw [MonObj.comp_mul, hp, hq, map_mul]⟩

private theorem HasPolynomialOrbit.inv (c : UnitCocharacter G) {B : Type u}
    [CommRing B] [Algebra R B] {g : coordSpec R B ⟶ G.X} (hg : HasPolynomialOrbit c g) :
    HasPolynomialOrbit c g⁻¹ := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p⁻¹, by rw [GrpObj.comp_inv, hp, map_inv]⟩

variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

private theorem pointCoordinates_orbit (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G)
    (g : coordSpec R B ⟶ G.X) :
    pointCoordinates e (orbitPoint c B g) =
      (AddMonoidAlgebra.mapAlgHom ℤ (pointCoordinates e g)).comp (coactionOfCocharacter e c) := by
  rw [← laurentEval_variable_eq_map, coactionOfCocharacter_eval, coordSpecMap_comp, Category.assoc]
  have hg : coordSpecMap (pointCoordinates e g) ≫ e.hom = g :=
    (pointCoordinates e).symm_apply_apply g
  rw [hg]
  rfl

private theorem hasPolynomialOrbit_iff (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G)
    (g : coordSpec R B ⟶ G.X) :
    HasPolynomialOrbit c g ↔
      (LaurentGrading.ofCocharacter e c).negativeIdeal ≤ RingHom.ker (pointCoordinates e g) := by
  rw [LaurentGrading.factors_iff (LaurentGrading.ofCocharacter e c)]
  change HasPolynomialOrbit c g ↔ ∀ x n, n < 0 →
    (((AddMonoidAlgebra.mapAlgHom ℤ (pointCoordinates e g)).comp
      (coactionOfCocharacter e c)) x).coeff n = 0
  rw [← pointCoordinates_orbit, ← polynomialLift_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨pointCoordinates e p, ?_⟩
    rw [← pointCoordinates_natural (f := toLaurentOver (R := R) (B := B)), hp]
  · rintro ⟨p, hp⟩
    refine ⟨(pointCoordinates e).symm p, (pointCoordinates e).injective ?_⟩
    rwa [pointCoordinates_natural, Equiv.apply_symm_apply]

private theorem factorsThroughQuotient (e : coordSpec R A ≅ G.X) (I : Ideal A)
    (g : coordSpec R B ⟶ G.X) :
    (∃ p : coordSpec R B ⟶ coordSpec R (A ⧸ I),
      p ≫ coordSpecMap (Ideal.Quotient.mkₐ R I) ≫ e.hom = g) ↔
    I ≤ RingHom.ker (pointCoordinates e g) := by
  constructor
  · rintro ⟨p, hp⟩
    let a := ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage p).unop.hom
    have ha : coordSpecMap a = p :=
      (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage p
    have hg : pointCoordinates e g = a.comp (Ideal.Quotient.mkₐ R I) := by
      apply (pointCoordinates e).symm.injective
      rw [Equiv.symm_apply_apply]
      change g = coordSpecMap (a.comp (Ideal.Quotient.mkₐ R I)) ≫ e.hom
      rw [coordSpecMap_comp, Category.assoc, ha, hp]
    intro x hx
    rw [RingHom.mem_ker, hg, AlgHom.comp_apply]
    change a (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    let a := Ideal.Quotient.liftₐ I (pointCoordinates e g) fun _ hx ↦ h hx
    refine ⟨coordSpecMap a, ?_⟩
    rw [← Category.assoc, ← coordSpecMap_comp]
    exact (pointCoordinates e).symm_apply_apply g

set_option backward.isDefEq.respectTransparency false in
/-- Over a noetherian ring the cocharacter's attracting subgroup is smooth if the
ambient affine group is smooth. Membership over each algebra is extension of its
conjugation orbit over zero. -/
theorem existsAttractingSubgroup [IsNoetherianRing R]
    (ha : IsAffine G.X.left) (hs : Smooth G.X.hom) (c : UnitCocharacter G) :
    ∃ (H : Grp (Over (ringSpec R))) (j : H ⟶ G),
      IsClosedImmersion j.hom.hom.left ∧ Smooth H.X.hom ∧
        ∀ (B : Type u) [CommRing B] [Algebra R B] (g : coordSpec R B ⟶ G.X),
          HasPolynomialOrbit c g ↔ ∃ p : coordSpec R B ⟶ H.X, p ≫ j.hom.hom = g := by
  obtain ⟨Aop, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr ha
  let A := Aop.unop
  let e : coordSpec R A ≅ G.X := e₀
  let d := LaurentGrading.ofCocharacter e c
  let I := d.negativeIdeal
  let Z := coordSpec R (A ⧸ I)
  let q : Z ⟶ G.X := coordSpecMap (Ideal.Quotient.mkₐ R I) ≫ e.hom
  have hclosed : IsClosedImmersion q.left := by
    have hq : IsClosedImmersion (coordSpecMap (Ideal.Quotient.mkₐ R I)).left :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have he : IsIso e.hom.left := (CategoryTheory.Over.forget (ringSpec R)).map_isIso e.hom
    exact IsClosedImmersion.comp _ _
  have hmono : Mono q := Over.mono_of_mono_left q
  have hpoint (B : Type u) [CommRing B] [Algebra R B] (g : coordSpec R B ⟶ G.X) :
      HasPolynomialOrbit c g ↔ ∃ p : coordSpec R B ⟶ Z, p ≫ q = g :=
    (hasPolynomialOrbit_iff e c g).trans (factorsThroughQuotient e I g).symm
  have hZ : IsAffine Z.left := inferInstanceAs (IsAffine (ringSpec (A ⧸ I)))
  have hZprod : IsAffine (Z ⊗ Z).left := by
    rw [Over.tensorObj_left]
    infer_instance
  have hunit : IsAffine (𝟙_ (Over (ringSpec R))).left := by
    change IsAffine (ringSpec R)
    infer_instance
  have productFactors {T : Over (ringSpec R)} (hT : IsAffine T.left) (f g : T ⟶ Z) :
      ∃ h : T ⟶ Z, h ≫ q = (f ≫ q) * (g ≫ q) := by
    obtain ⟨Bop, ⟨b₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr hT
    let B := Bop.unop
    let b : coordSpec R B ≅ T := b₀
    have hf := (hpoint B ((b.hom ≫ f) ≫ q)).mpr ⟨b.hom ≫ f, rfl⟩
    have hg := (hpoint B ((b.hom ≫ g) ≫ q)).mpr ⟨b.hom ≫ g, rfl⟩
    obtain ⟨a, ha⟩ := (hpoint B _).mp (hf.mul c hg)
    refine ⟨b.inv ≫ a, ?_⟩
    simpa only [Category.assoc, ← MonObj.comp_mul, Iso.inv_hom_id_assoc] using
      congrArg (b.inv ≫ ·) ha
  obtain ⟨m, hm⟩ := productFactors hZprod (fst Z Z) (snd Z Z)
  obtain ⟨Bop, ⟨b₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr hunit
  let B := Bop.unop
  let b : coordSpec R B ≅ 𝟙_ (Over (ringSpec R)) := b₀
  obtain ⟨ηZ, hηZ⟩ := (hpoint B 1).mp (HasPolynomialOrbit.one c B)
  let w := b.inv ≫ ηZ
  have hw : w ≫ q = η[G.X] := by
    rw [Category.assoc, hηZ, MonObj.comp_one]
    exact MonObj.one_eq_one (M := G.X)
  obtain ⟨v, hv⟩ := (hpoint (A ⧸ I) q⁻¹).mp
    (((hpoint (A ⧸ I) q).mpr ⟨𝟙 Z, Category.id_comp _⟩).inv c)
  have hmul : m ≫ q = (q ⊗ₘ q) ≫ μ[G.X] := by
    rw [hm, Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
  let : GrpObj Z := groupObjectOfOperations q w m v hw hmul hv
  let H : Grp (Over (ringSpec R)) := Grp.mk Z
  let j : H ⟶ G := Grp.homMk'' q hw hmul
  have hA : Algebra.Smooth R A := by
    apply RingHom.smooth_algebraMap.mp
    refine (HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap R A))).mp ?_
    change Smooth (coordSpec R A).hom
    rw [← Over.w e.hom]
    have : IsIso e.hom.left := (CategoryTheory.Over.forget (ringSpec R)).map_isIso e.hom
    infer_instance
  have hquotient : Algebra.Smooth R (A ⧸ I) := d.smooth_quotient
  have hZsmooth : Smooth Z.hom :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap R (A ⧸ I)))).mpr (RingHom.smooth_algebraMap.mpr hquotient)
  exact ⟨H, j, hclosed, hZsmooth, hpoint⟩

end AttractingSubgroup

section IntegralCocharacter

open WithConv
open Specs.IntegralSemisimpleModel (Integers Base Model IntegralAlgebra integralSpec
  IntegralPoints TorusValues splitTorus torusPoint cocharacter)
open Specs.Pinning (BasedRootDatum)

variable {D : BasedRootDatum.{u}}

private abbrev torusCoordinates (D : BasedRootDatum.{u}) (B : IntegralAlgebra.{u})
    (v : TorusValues D B) : MonoidAlgebra Integers.{u} (Multiplicative D.X) →ₐ[Integers.{u}] B :=
  MonoidAlgebra.lift Integers.{u} B (Multiplicative D.X) ((Units.coeHom B).comp v)

private theorem torusPoint_mul (B : IntegralAlgebra.{u}) (v w : TorusValues D B) :
    torusPoint D B (v * w) = torusPoint D B v * torusPoint D B w := by
  let e := Spec.mapMulEquiv (R := Integers.{u})
    (S := MonoidAlgebra Integers.{u} (Multiplicative D.X)) (T := B)
  change e (toConv (torusCoordinates D B (v * w))) =
    e (toConv (torusCoordinates D B v)) * e (toConv (torusCoordinates D B w))
  rw [← map_mul]
  apply congrArg e
  apply WithConv.ofConv_injective
  apply MonoidAlgebra.algHom_ext
  · intro m
    change torusCoordinates D B (v * w) (MonoidAlgebra.single m 1) =
      (toConv (torusCoordinates D B v) * toConv (torusCoordinates D B w))
        (MonoidAlgebra.single m 1)
    rw [AlgHom.convMul_apply, (MonoidAlgebra.isGroupLikeElem_single_one m).comul_eq_tmul_self]
    simp [Algebra.TensorProduct.lift_tmul, MonoidAlgebra.lift_single, MonoidHom.mul_apply, Algebra.smul_def]
  · exact Subsingleton.elim _ _

private theorem torusPoint_natural {B C : IntegralAlgebra.{u}} (f : B ⟶ C)
    (v : TorusValues D B) :
    integralSpec.map f.op ≫ torusPoint D B v =
      torusPoint D C ((Units.map f.hom.toMonoidHom).comp v) := by
  change coordSpecMap f.hom ≫ coordSpecMap (torusCoordinates D B v) =
    coordSpecMap (torusCoordinates D C ((Units.map f.hom.toMonoidHom).comp v))
  rw [← coordSpecMap_comp]
  congr 1
  apply MonoidAlgebra.algHom_ext
  · intro m
    rw [AlgHom.comp_apply, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single]
    simp only [Algebra.smul_def, map_one, one_mul]
    rfl
  · exact Subsingleton.elim _ _

/-- The cocharacter of the marked integral torus, included in the actual model. -/
def integralUnitCocharacter (M : Model D) (y : D.Y) : UnitCocharacter M.group where
  point B := MonoidHom.mk'
    (fun s ↦ torusPoint D B (cocharacter D y B s) ≫ M.torus.hom.hom) (by
      intro s t
      have h : cocharacter D y B (s * t) = cocharacter D y B s * cocharacter D y B t := by
        apply MonoidHom.ext
        intro m
        exact mul_zpow s t (D.datum.toLinearMap m.toAdd y)
      rw [h, torusPoint_mul, MonObj.mul_comp])
  natural {B C} f t := by
    change integralSpec.map f.op ≫
      (torusPoint D B (cocharacter D y B t) ≫ M.torus.hom.hom) =
      torusPoint D C (cocharacter D y C (Units.map f.hom.toMonoidHom t)) ≫ M.torus.hom.hom
    rw [← Category.assoc, torusPoint_natural]
    apply congrArg (fun v : TorusValues D C ↦ torusPoint D C v ≫ M.torus.hom.hom)
    apply MonoidHom.ext
    intro m
    exact map_zpow (Units.map f.hom.toMonoidHom) t (D.datum.toLinearMap m.toAdd y)

/-- The cocharacter orbit condition is represented over the integers themselves. -/
theorem integralAttractingSubgroup (M : Model D) (y : D.Y) :
    ∃ (H : Grp (Over Base.{u})) (j : H ⟶ M.group),
      IsClosedImmersion j.hom.hom.left ∧ Smooth H.X.hom ∧
        ∀ (B : IntegralAlgebra.{u}) (g : IntegralPoints M.group B),
          HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
            ∃ p : IntegralPoints H B, p ≫ j.hom.hom = g := by
  have : IsNoetherianRing Integers.{u} := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  obtain ⟨H, j, hclosed, hsmooth, hpoint⟩ :=
    existsAttractingSubgroup M.affine M.smooth (integralUnitCocharacter M y)
  exact ⟨H, j, hclosed, hsmooth, fun B g ↦ hpoint B g⟩

end IntegralCocharacter

section BaseChangePoints

variable {S U : Scheme.{u}}

private abbrev pullbackPoint (a : U ⟶ S) (T : Over U) (X : Over S) :
    (T ⟶ (Over.pullback a).obj X) ≃ ((Over.map a).obj T ⟶ X) :=
  ((Over.mapPullbackAdj a).homEquiv T X).symm

set_option backward.isDefEq.respectTransparency false in
private theorem adjunctionPoint_mul {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    {L : D ⥤ C} {F : C ⥤ D} [F.Monoidal] (adj : L ⊣ F) (T : D) (G : Grp C)
    (p q : T ⟶ (F.mapGrp.obj G).X) :
    (adj.homEquiv T G.X).symm (p * q) =
      (adj.homEquiv T G.X).symm p * (adj.homEquiv T G.X).symm q := by
  let p' : T ⟶ F.obj G.X := p
  let q' : T ⟶ F.obj G.X := q
  let x := (adj.homEquiv T G.X).symm p'
  let y := (adj.homEquiv T G.X).symm q'
  let t : T ⟶ F.obj (G.X ⊗ G.X) := lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X
  have hfst : t ≫ F.map (fst G.X G.X) = p' := by
    simp only [t, Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hsnd : t ≫ F.map (snd G.X G.X) = q' := by
    simp only [t, Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
  have hpair : (adj.homEquiv T (G.X ⊗ G.X)).symm t = lift x y := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← adj.homEquiv_naturality_right_symm, hfst]
    · rw [lift_snd, ← adj.homEquiv_naturality_right_symm, hsnd]
  rw [Hom.mul_def, Hom.mul_def]
  change (adj.homEquiv T G.X).symm
    (lift p' q' ≫ (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X])) = lift x y ≫ μ[G.X]
  rw [← Category.assoc]
  change (adj.homEquiv T G.X).symm (t ≫ F.map μ[G.X]) = _
  rw [adj.homEquiv_naturality_right_symm, hpair]

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private abbrev restrictAlgebra (R : Type u) [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A] (B : CommAlgCat.{u} A) : CommAlgCat.{u} R :=
  letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  CommAlgCat.of R B

private def restrictAlgebraHom {B C : CommAlgCat.{u} A} (f : B ⟶ C) :
    restrictAlgebra R B ⟶ restrictAlgebra R C :=
  ConcreteCategory.ofHom (C := CommAlgCat R)
    ({ toRingHom := f.hom.toRingHom
       commutes' := fun r ↦ f.hom.commutes (algebraMap R A r) } :
      restrictAlgebra R B →ₐ[R] restrictAlgebra R C)

private def restrictSpecIso (B : CommAlgCat.{u} A) :
    (ringAlgebraSpec R).obj (op (restrictAlgebra R B)) ≅
      (Over.map (algebraSpecMap R A)).obj ((ringAlgebraSpec A).obj (op B)) :=
  Over.isoMk (Iso.refl (ringSpec B)) (by
    change 𝟙 (ringSpec B) ≫
      (algebraSpecMap A B ≫ algebraSpecMap R A) =
      Spec.map (CommRingCat.ofHom ((algebraMap A B).comp (algebraMap R A)))
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap A B))).symm)

private def scalarExtensionPointEquiv (X : Over (ringSpec R)) (B : CommAlgCat.{u} A) :
    (((ringAlgebraSpec A).obj (op B)) ⟶ (Over.pullback (algebraSpecMap R A)).obj X) ≃
      (((ringAlgebraSpec R).obj (op (restrictAlgebra R B))) ⟶ X) :=
  (pullbackPoint (algebraSpecMap R A) _ X).trans
    (Iso.homCongr (restrictSpecIso B).symm (Iso.refl X))

private theorem scalarExtensionPointEquiv_natural (X : Over (ringSpec R)) {B C : CommAlgCat.{u} A}
    (f : B ⟶ C) (p : (ringAlgebraSpec A).obj (op B) ⟶
      (Over.pullback (algebraSpecMap R A)).obj X) :
    scalarExtensionPointEquiv X C ((ringAlgebraSpec A).map f.op ≫ p) =
      (ringAlgebraSpec R).map (restrictAlgebraHom f).op ≫ scalarExtensionPointEquiv X B p := by
  let a := algebraSpecMap R A
  let T := (ringAlgebraSpec A).obj (op B)
  let U := (ringAlgebraSpec A).obj (op C)
  let g := (ringAlgebraSpec A).map f.op
  change (restrictSpecIso C).hom ≫ pullbackPoint a U X (g ≫ p) ≫ 𝟙 X =
    (ringAlgebraSpec R).map (restrictAlgebraHom f).op ≫
      (restrictSpecIso B).hom ≫ pullbackPoint a T X p ≫ 𝟙 X
  rw [(Over.mapPullbackAdj a).homEquiv_naturality_left_symm]
  have h : (restrictSpecIso C).hom ≫ (Over.map a).map g =
      (ringAlgebraSpec R).map (restrictAlgebraHom f).op ≫ (restrictSpecIso B).hom := by
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom f.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ 𝟙 _
    simp
  simp only [Category.assoc, reassoc_of% h]
  rfl

private theorem scalarExtensionPointEquiv_map {X Y : Over (ringSpec R)} (f : X ⟶ Y)
    (B : CommAlgCat.{u} A) (p : (ringAlgebraSpec A).obj (op B) ⟶
      (Over.pullback (algebraSpecMap R A)).obj X) :
    scalarExtensionPointEquiv Y B (p ≫ (Over.pullback (algebraSpecMap R A)).map f) =
      scalarExtensionPointEquiv X B p ≫ f := by
  let a := algebraSpecMap R A
  let T := (ringAlgebraSpec A).obj (op B)
  change (restrictSpecIso B).hom ≫ pullbackPoint a T Y (p ≫ (Over.pullback a).map f) ≫ 𝟙 Y =
    ((restrictSpecIso B).hom ≫ pullbackPoint a T X p ≫ 𝟙 X) ≫ f
  rw [(Over.mapPullbackAdj a).homEquiv_naturality_right_symm]
  simp

private def scalarExtensionGroupEquiv (G : Grp (Over (ringSpec R))) (B : CommAlgCat.{u} A) :
    affinePoints ((changeBase (algebraSpecMap R A)).obj G) B ≃*
      affinePoints G (restrictAlgebra R B) where
  toEquiv := scalarExtensionPointEquiv G.X B
  map_mul' p q := by
    let T := (ringAlgebraSpec A).obj (op B)
    let a := algebraSpecMap R A
    change (restrictSpecIso B).hom ≫ pullbackPoint a T G.X (p * q) ≫ 𝟙 G.X =
      ((restrictSpecIso B).hom ≫ pullbackPoint a T G.X p ≫ 𝟙 G.X) *
        ((restrictSpecIso B).hom ≫ pullbackPoint a T G.X q ≫ 𝟙 G.X)
    have hm := adjunctionPoint_mul (Over.mapPullbackAdj a) T G p q
    change pullbackPoint a T G.X (p * q) = _ at hm
    rw [hm]
    simp only [Category.comp_id, MonObj.comp_mul]

/-- Extend a cocharacter by using the same unit on each algebra over the new base. -/
def UnitCocharacter.changeScalars {G : Grp (Over (ringSpec R))} (c : UnitCocharacter G) :
    UnitCocharacter ((changeBase (algebraSpecMap R A)).obj G) where
  point B := (scalarExtensionGroupEquiv G B).symm.toMonoidHom.comp (c.point (restrictAlgebra R B))
  natural {B C} f t := by
    let p : (ringAlgebraSpec A).obj (op B) ⟶ (Over.pullback (algebraSpecMap R A)).obj G.X :=
      (scalarExtensionGroupEquiv G B).symm (c.point (restrictAlgebra R B) t)
    have hp : scalarExtensionPointEquiv G.X B p = c.point (restrictAlgebra R B) t :=
      (scalarExtensionGroupEquiv G B).apply_symm_apply _
    apply (scalarExtensionGroupEquiv G C).injective
    change scalarExtensionPointEquiv G.X C ((ringAlgebraSpec A).map f.op ≫ p) =
      (scalarExtensionGroupEquiv G C)
        ((scalarExtensionGroupEquiv G C).symm
          (c.point (restrictAlgebra R C) (Units.map f.hom.toMonoidHom t)))
    rw [scalarExtensionPointEquiv_natural, hp, MulEquiv.apply_symm_apply,
      ← mapAffinePoints_apply, c.natural]
    rfl

end BaseChangePoints

section AttractingSubgroupBaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {G : Grp (Over (ringSpec R))}

private abbrev polynomialTest (B : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (Polynomial B)

private abbrev laurentTest (B : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (LaurentPolynomial B)

private def coefficientAlgebraIso (B C : CommAlgCat.{u} R) (f : B ≃+* C)
    (h : ∀ r, f (algebraMap R B r) = algebraMap R C r) : B ≅ C :=
  let e : B ≃ₐ[R] C := AlgEquiv.ofRingEquiv h
  CommAlgCat.isoMk e

private def polynomialRestriction (B : CommAlgCat.{u} A) :
    restrictAlgebra R (polynomialTest B) ≅ polynomialTest (restrictAlgebra R B) :=
  coefficientAlgebraIso _ _ (RingEquiv.refl (Polynomial B)) fun _ ↦ rfl

private def laurentRestriction (B : CommAlgCat.{u} A) :
    restrictAlgebra R (laurentTest B) ≅ laurentTest (restrictAlgebra R B) :=
  coefficientAlgebraIso _ _ (RingEquiv.refl (LaurentPolynomial B)) fun _ ↦ rfl

private theorem mapAffinePoints_comp (H : Grp (Over (ringSpec R))) {B C D : CommAlgCat.{u} R}
    (f : B ⟶ C) (g : C ⟶ D) (x : affinePoints H B) :
    mapAffinePoints H (f ≫ g) x = mapAffinePoints H g (mapAffinePoints H f x) := by
  simp only [mapAffinePoints_apply, op_comp, CategoryTheory.Functor.map_comp, Category.assoc]

private abbrev changedGroup (G : Grp (Over (ringSpec R))) :=
  (changeBase (algebraSpecMap R A)).obj G

private def polynomialPointEquiv (G : Grp (Over (ringSpec R))) (B : CommAlgCat.{u} A) :
    affinePoints (changedGroup (A := A) G) (polynomialTest B) ≃*
      affinePoints G (polynomialTest (restrictAlgebra R B)) :=
  (scalarExtensionGroupEquiv G (polynomialTest B)).trans
    ((((ringAlgebraSpec R).rightOp ⋙ yonedaGrp.obj G).mapIso (polynomialRestriction B)).groupIsoToMulEquiv)

private def laurentPointEquiv (G : Grp (Over (ringSpec R))) (B : CommAlgCat.{u} A) :
    affinePoints (changedGroup (A := A) G) (laurentTest B) ≃*
      affinePoints G (laurentTest (restrictAlgebra R B)) :=
  (scalarExtensionGroupEquiv G (laurentTest B)).trans
    ((((ringAlgebraSpec R).rightOp ⋙ yonedaGrp.obj G).mapIso (laurentRestriction B)).groupIsoToMulEquiv)

private def polynomialInclusion (B : CommAlgCat.{u} R) : polynomialTest B ⟶ laurentTest B :=
  CommAlgCat.ofHom (toLaurentOver (R := R) (B := B))

private def laurentConstantInclusion (B : CommAlgCat.{u} R) : B ⟶ laurentTest B :=
  CommAlgCat.ofHom (laurentConstants R B)

private theorem polynomialPointEquiv_inclusion (B : CommAlgCat.{u} A)
    (p : affinePoints (changedGroup (A := A) G) (polynomialTest B)) :
    laurentPointEquiv G B (mapAffinePoints _ (polynomialInclusion B) p) =
      mapAffinePoints G (polynomialInclusion (restrictAlgebra R B)) (polynomialPointEquiv G B p) := by
  have h : restrictAlgebraHom (R := R) (polynomialInclusion B) ≫ (laurentRestriction B).hom =
      (polynomialRestriction B).hom ≫ polynomialInclusion (restrictAlgebra R B) := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun _ ↦ rfl
  let p' : (ringAlgebraSpec A).obj (op (polynomialTest B)) ⟶
      (Over.pullback (algebraSpecMap R A)).obj G.X := p
  change mapAffinePoints G (laurentRestriction B).hom (scalarExtensionPointEquiv G.X _
    ((ringAlgebraSpec A).map (polynomialInclusion B).op ≫ p')) = _
  rw [scalarExtensionPointEquiv_natural, ← mapAffinePoints_apply, ← mapAffinePoints_comp, h,
    mapAffinePoints_comp]
  rfl

private theorem laurentPointEquiv_constants (B : CommAlgCat.{u} A)
    (p : affinePoints (changedGroup (A := A) G) B) :
    laurentPointEquiv G B (mapAffinePoints _ (laurentConstantInclusion B) p) =
      mapAffinePoints G (laurentConstantInclusion (restrictAlgebra R B)) (scalarExtensionGroupEquiv G B p) := by
  have h : restrictAlgebraHom (R := R) (laurentConstantInclusion B) ≫ (laurentRestriction B).hom =
      laurentConstantInclusion (restrictAlgebra R B) := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun _ ↦ rfl
  let p' : (ringAlgebraSpec A).obj (op B) ⟶
      (Over.pullback (algebraSpecMap R A)).obj G.X := p
  change mapAffinePoints G (laurentRestriction B).hom (scalarExtensionPointEquiv G.X _
    ((ringAlgebraSpec A).map (laurentConstantInclusion B).op ≫ p')) = _
  rw [scalarExtensionPointEquiv_natural, ← mapAffinePoints_apply, ← mapAffinePoints_comp, h]
  rfl

private theorem laurentPointEquiv_cocharacter (c : UnitCocharacter G)
    (B : CommAlgCat.{u} A) :
    laurentPointEquiv G B ((c.changeScalars (A := A)).point (laurentTest B) (laurentVariable B 1)) =
      c.point (laurentTest (restrictAlgebra R B)) (laurentVariable (restrictAlgebra R B) 1) := by
  change mapAffinePoints G (laurentRestriction B).hom (scalarExtensionGroupEquiv G (laurentTest B)
    ((scalarExtensionGroupEquiv G (laurentTest B)).symm
      (c.point (restrictAlgebra R (laurentTest B)) (laurentVariable B 1)))) = _
  rw [MulEquiv.apply_symm_apply, c.natural]
  congr 1

private theorem laurentPointEquiv_orbit (c : UnitCocharacter G)
    (B : CommAlgCat.{u} A) (p : affinePoints (changedGroup (A := A) G) B) :
    laurentPointEquiv G B (orbitPoint (c.changeScalars (A := A)) B p) =
      orbitPoint c (restrictAlgebra R B) (scalarExtensionGroupEquiv G B p) := by
  let C := c.changeScalars (A := A)
  let t := C.point (laurentTest B) (laurentVariable B 1)
  let g := mapAffinePoints (changedGroup (A := A) G) (laurentConstantInclusion B) p
  change laurentPointEquiv G B (t * g * t⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  have ht := laurentPointEquiv_cocharacter c B
  have hg := laurentPointEquiv_constants B p
  change laurentPointEquiv G B t = _ at ht
  change laurentPointEquiv G B g = _ at hg
  rw [ht, hg]
  rfl

private theorem hasPolynomialOrbit_changeScalars (c : UnitCocharacter G)
    (B : CommAlgCat.{u} A) (p : affinePoints (changedGroup (A := A) G) B) :
    HasPolynomialOrbit (c.changeScalars (A := A)) p ↔
      HasPolynomialOrbit c (B := restrictAlgebra R B) (scalarExtensionGroupEquiv G B p) := by
  constructor
  · rintro ⟨q, hq⟩
    change mapAffinePoints _ (polynomialInclusion B) q =
      orbitPoint (c.changeScalars (A := A)) B p at hq
    refine ⟨polynomialPointEquiv G B q, ?_⟩
    change mapAffinePoints _ (polynomialInclusion (restrictAlgebra R B)) (polynomialPointEquiv G B q) = _
    rw [← polynomialPointEquiv_inclusion, hq, laurentPointEquiv_orbit]
  · rintro ⟨q, hq⟩
    refine ⟨(polynomialPointEquiv G B).symm q, ?_⟩
    change mapAffinePoints _ (polynomialInclusion B) ((polynomialPointEquiv G B).symm q) =
      orbitPoint (c.changeScalars (A := A)) B p
    apply (laurentPointEquiv G B).injective
    rw [polynomialPointEquiv_inclusion, MulEquiv.apply_symm_apply, laurentPointEquiv_orbit]
    exact hq

/-- The same closed subgroup represents the cocharacter orbit condition after
extension of scalars. -/
theorem attractingSubgroup_changeScalars (c : UnitCocharacter G) {H : Grp (Over (ringSpec R))}
    (j : H ⟶ G)
    (hj : ∀ (B : Type u) [CommRing B] [Algebra R B] (p : coordSpec R B ⟶ G.X),
      HasPolynomialOrbit c p ↔ ∃ q : coordSpec R B ⟶ H.X, q ≫ j.hom.hom = p)
    (B : CommAlgCat.{u} A) (p : affinePoints (changedGroup (A := A) G) B) :
    HasPolynomialOrbit (c.changeScalars (A := A)) p ↔
      ∃ q : affinePoints (changedGroup (A := A) H) B,
        q ≫ ((changeBase (algebraSpecMap R A)).map j).hom.hom = p := by
  rw [hasPolynomialOrbit_changeScalars, hj (restrictAlgebra R B)]
  let a := algebraSpecMap R A
  let F := Over.pullback a
  let X := (ringAlgebraSpec A).obj (op B)
  let Gpoints := scalarExtensionPointEquiv (A := A) G.X B
  let Hpoints := scalarExtensionPointEquiv (A := A) H.X B
  let j' := F.map j.hom.hom
  let p' : X ⟶ F.obj G.X := p
  change (∃ q, q ≫ j.hom.hom = Gpoints p') ↔
    (∃ q : X ⟶ F.obj H.X, q ≫ j' = p')
  have hmap (q : X ⟶ F.obj H.X) : Gpoints (q ≫ j') = Hpoints q ≫ j.hom.hom :=
    scalarExtensionPointEquiv_map j.hom.hom B q
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨Hpoints.symm q, Gpoints.injective ?_⟩
    rw [hmap, Equiv.apply_symm_apply, hq]
  · rintro ⟨q, hq⟩
    refine ⟨Hpoints q, ?_⟩
    rw [← hmap, hq]

end AttractingSubgroupBaseChange

section CompareSubgroups

variable {R : Type u} [CommRing R] {G H J : Grp (Over (ringSpec R))}

/-- Closed subgroups of an affine group with the same points on all algebras
are isomorphic over the ambient group. -/
theorem subgroupIsoOfAlgebraPoints (ha : IsAffine G.X.left) (i : H ⟶ G) (j : J ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) (hj : IsClosedImmersion j.hom.hom.left)
    (hpoints : ∀ (B : Type u) [CommRing B] [Algebra R B] (x : coordSpec R B ⟶ G.X),
      (∃ y : coordSpec R B ⟶ H.X, y ≫ i.hom.hom = x) ↔
        (∃ z : coordSpec R B ⟶ J.X, z ≫ j.hom.hom = x)) :
    ∃ e : H ≅ J, e.hom ≫ j = i := by
  have hH : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have hJ : IsAffine J.X.left := isAffine_of_isAffineHom j.hom.hom.left
  obtain ⟨B, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr hH
  obtain ⟨C, ⟨d₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr hJ
  let e : coordSpec R B.unop ≅ H.X := e₀
  let d : coordSpec R C.unop ≅ J.X := d₀
  obtain ⟨f, hf⟩ := (hpoints B.unop (e.hom ≫ i.hom.hom)).mp ⟨e.hom, rfl⟩
  obtain ⟨g, hg⟩ := (hpoints C.unop (d.hom ≫ j.hom.hom)).mpr ⟨d.hom, rfl⟩
  let f' := e.inv ≫ f
  let g' := d.inv ≫ g
  have hf' : f' ≫ j.hom.hom = i.hom.hom := by simp [f', hf]
  have hg' : g' ≫ i.hom.hom = j.hom.hom := by simp [g', hg]
  have hmonoI : Mono i.hom.hom := Over.mono_of_mono_left _
  have hmonoJ : Mono j.hom.hom := Over.mono_of_mono_left _
  let k : H.X ≅ J.X :=
    ⟨f', g', (cancel_mono i.hom.hom).mp (by simp [hg', hf']),
      (cancel_mono j.hom.hom).mp (by simp [hf', hg'])⟩
  refine ⟨subgroupIso i j k hf', ?_⟩
  apply Grp.hom_ext
  exact hf'

end CompareSubgroups

section AmbientIsomorphism

variable {k : Type u} [Field k] {G H : Specs.GroupScheme k}

/-- Transport a closed subgroup by a group scheme isomorphism. -/
private def transportClosedSubgroup (e : G ≅ H) (B : ClosedSubgroup G) : ClosedSubgroup H := by
  have hB := B.isClosedImmersion
  have he : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ CategoryTheory.Over.forget _).map_isIso e.hom
  exact ⟨B.group, B.inclusion ≫ e.hom, IsClosedImmersion.comp _ _⟩

private theorem transportClosedSubgroup_subgroupOf (e : G ≅ H) {B C : ClosedSubgroup G} :
    IsSubgroupOf (transportClosedSubgroup e B) (transportClosedSubgroup e C) ↔ IsSubgroupOf B C := by
  constructor
  · rintro ⟨f, hf⟩
    change B.group ⟶ C.group at f
    change f ≫ C.inclusion ≫ e.hom = B.inclusion ≫ e.hom at hf
    exact ⟨f, (cancel_mono e.hom).mp ((Category.assoc _ _ _).trans hf)⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    change f ≫ C.inclusion ≫ e.hom = B.inclusion ≫ e.hom
    rw [← Category.assoc, hf]

private theorem transportClosedSubgroup_inverse (e : G ≅ H) (B : ClosedSubgroup G) :
    transportClosedSubgroup e.symm (transportClosedSubgroup e B) = B := by
  cases B
  simp [transportClosedSubgroup, Category.assoc]

private theorem isBorel_transport_iff (e : G ≅ H) (B : ClosedSubgroup G) :
    IsBorel (transportClosedSubgroup e B) ↔ IsBorel B := by
  have descends (e' : G ≅ H) (B' : ClosedSubgroup G) (hB : IsBorel (transportClosedSubgroup e' B')) :
      IsBorel B' := by
    refine ⟨hB.1, fun C hC hle ↦ (transportClosedSubgroup_subgroupOf e').mp
      (hB.2 _ hC ((transportClosedSubgroup_subgroupOf e').mpr hle))⟩
  refine ⟨descends e B, ?_⟩
  intro hB
  refine ⟨hB.1, ?_⟩
  intro C hC hle
  have hle' := (transportClosedSubgroup_subgroupOf e.symm).mpr hle
  rw [transportClosedSubgroup_inverse] at hle'
  apply (transportClosedSubgroup_subgroupOf e.symm).mp
  rw [transportClosedSubgroup_inverse]
  exact hB.2 _ hC hle'

end AmbientIsomorphism

section SplitModel

open Specs.IntegralSemisimpleModel (Integers Base IntegralGroup IntegralAlgebra integralSpec
  IntegralPoints Model TorusValues splitTorus torusPoint cocharacter forgetFibrePoint fibre integerAlgebra)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (Realization)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (characterValue pairing)
open Specs.BorelsAndChambers (IsRegular)
open Specs.RankOneFlag (SameSubgroup)
open CocharacterDynamics (cocharacterPoint HasExtension)

open private torusPoint_surjective
  from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private centralizer_of_regular regular_isBorel
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private borel_of_same from LinearAlgebraicGroups.RootData.RankOneFlag

section IntegralFibres

variable {k : Type u} [Field k]

attribute [local instance] integerAlgebra

private def integerRestrictionIso (B : TestAlgebra k) :
    restrictAlgebra Integers.{u} B ≅ (CommAlgCat.of Integers.{u} B : IntegralAlgebra.{u}) :=
  coefficientAlgebraIso _ _ (RingEquiv.refl B) fun r ↦ by
    change algebraMap k B ((r.down : ℤ) : k) = ((r.down : ℤ) : B)
    exact map_intCast (algebraMap k B) r.down

private theorem scalarExtensionPointEquiv_left {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (X : Over (ringSpec R)) (B : CommAlgCat.{u} A)
    (p : (ringAlgebraSpec A).obj (op B) ⟶ (Over.pullback (algebraSpecMap R A)).obj X) :
    (scalarExtensionPointEquiv X B p).left =
      p.left ≫ pullback.fst X.hom (algebraSpecMap R A) := by
  change 𝟙 (ringSpec B) ≫ (p.left ≫ pullback.fst X.hom (algebraSpecMap R A)) ≫ 𝟙 X.left = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem map_scalarExtensionGroupEquiv_integral (G : IntegralGroup.{u}) (B : TestAlgebra k)
    (p : GroupPoints ((fibre k).obj G) B) :
    mapAffinePoints G (integerRestrictionIso B).hom (scalarExtensionGroupEquiv G B p) =
      forgetFibrePoint G B p := by
  apply Over.OverMorphism.ext
  let q : (ringAlgebraSpec k).obj (op B) ⟶
      (Over.pullback (algebraSpecMap Integers.{u} k)).obj G.X := p
  change ((integralSpec.map (integerRestrictionIso B).hom.op) ≫
    scalarExtensionPointEquiv G.X B q).left = p.left ≫ _
  change (integralSpec.map (integerRestrictionIso B).hom.op).left ≫
    (scalarExtensionPointEquiv G.X B q).left = p.left ≫ _
  have hid : (integralSpec.map (integerRestrictionIso B).hom.op).left = 𝟙 (ringSpec B) := by
    change Spec.map (𝟙 (CommRingCat.of B)) = _
    exact Scheme.Spec.map_id _
  rw [hid]
  let x : ringSpec B ⟶ G.X.left := (scalarExtensionPointEquiv G.X B q).left
  change 𝟙 (ringSpec B) ≫ x = p.left ≫ pullback.fst G.X.hom (algebraSpecMap Integers.{u} k)
  rw [Category.id_comp]
  exact scalarExtensionPointEquiv_left G.X B q

set_option backward.isDefEq.respectTransparency false in
private theorem forgetFibrePoint_map {G H : IntegralGroup.{u}} (j : G ⟶ H) (B : TestAlgebra k)
    (p : GroupPoints ((fibre k).obj G) B) :
    forgetFibrePoint H B (p ≫ ((fibre k).map j).hom.hom) =
      forgetFibrePoint G B p ≫ j.hom.hom := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((Over.pullback (algebraSpecMap Integers.{u} k)).map j.hom.hom).left) ≫
      pullback.fst H.X.hom (algebraSpecMap Integers.{u} k) =
    (p.left ≫ pullback.fst G.X.hom (algebraSpecMap Integers.{u} k)) ≫ j.hom.hom.left
  let a := algebraSpecMap Integers.{u} k
  have h := (pullbackMapSquare a j.hom.hom).w
  change ((Over.pullback a).map j.hom.hom).left ≫ pullback.fst H.X.hom a =
    pullback.fst G.X.hom a ≫ j.hom.hom.left at h
  simpa only [Category.assoc] using congrArg (p.left ≫ ·) h

private theorem torusPoint_after_integerRestriction {D : Specs.Pinning.BasedRootDatum.{u}} (y : D.Y)
    (B : TestAlgebra k) (s : Bˣ) :
    integralSpec.map (integerRestrictionIso B).hom.op ≫
        torusPoint D (restrictAlgebra Integers.{u} B) (cocharacter D y (restrictAlgebra Integers.{u} B) s) =
      torusPoint D (CommAlgCat.of Integers.{u} B) (cocharacter D y (CommAlgCat.of Integers.{u} B) s) := by
  rw [torusPoint_natural]
  apply congrArg (torusPoint D _)
  apply MonoidHom.ext
  intro m
  apply Units.ext
  rfl

end IntegralFibres

section FieldCocharacter

variable {k : Type u} [Field k]
variable {D : BasedRootDatum.{u}} {L : Specs.RootGroups.AdditiveLine k}

attribute [local instance] integerAlgebra

private abbrev markedCocharacter (F : Realization D L) (y : D.Y) :
    Cocharacter F.pinned.pair.T.group :=
  Additive.toMul (F.datumIso.val.coweightEquiv.symm y)

private theorem markedPairing (F : Realization D L) (x : D.X) (y : D.Y) :
    pairing F.pinned.pair.T.group (Additive.toMul (F.datumIso.val.weightEquiv x))
      (markedCocharacter F y) = D.datum.toLinearMap x y := by
  let := F.attached.comm
  rw [← F.attached.datum.pairing_eq]
  change F.attached.toBased.datum.toLinearMap (F.datumIso.val.weightEquiv x)
    (F.datumIso.val.coweightEquiv.symm y) = _
  rw [F.datumIso.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem markedCocharacter_regular (F : Realization D L) (y : D.Y)
    (hy : ∀ i : D.I, D.datum.toLinearMap (D.datum.root i) y ≠ 0) :
    IsRegular F.pinned.pair.T (markedCocharacter F y) := by
  intro α
  obtain ⟨i, rfl⟩ := F.datumIso.val.indexEquiv.surjective α
  let := F.attached.comm
  rw [← F.attached.datum.pairing_eq, ← F.attached.datum.root_eq]
  change F.attached.toBased.datum.root' (F.datumIso.val.indexEquiv i)
    (F.datumIso.val.coweightEquiv.symm y) ≠ 0
  rw [F.datumIso.val.root'_coweightEquiv]
  exact hy i

set_option backward.isDefEq.respectTransparency false in
private theorem fieldCocharacter_of_marking (M : Model D) (y : D.Y)
    {L : Specs.RootGroups.AdditiveLine k} (F : Realization D L)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (ht : (fibre k).map M.torus ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion)
    (hval : ∀ (B : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) B)
      (v : TorusValues D (CommAlgCat.of Integers.{u} B)),
      forgetFibrePoint (splitTorus D) B s = torusPoint D (CommAlgCat.of Integers.{u} B) v →
      ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) B
        (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : B)) :
    ∀ (B : TestAlgebra k) (s : Bˣ),
      ((integralUnitCocharacter M y).changeScalars (A := k)).point B s ≫ e.hom.hom.hom =
        cocharacterPoint (markedCocharacter F y ≫ F.pinned.pair.T.inclusion) B s := by
  intro B s
  let q : (testSpec k).obj (op B) ⟶ F.pinned.pair.T.group.X :=
    cocharacterPoint (markedCocharacter F y) B s
  let p : (testSpec k).obj (op B) ⟶ ((fibre k).obj (splitTorus D)).X :=
    q ≫ t.inv.hom.hom
  obtain ⟨v, hv₀⟩ := torusPoint_surjective D (CommAlgCat.of Integers.{u} B)
    (forgetFibrePoint (splitTorus D) B p)
  have hpq : p ≫ t.hom.hom.hom = q := by
    change (q ≫ t.inv.hom.hom) ≫ t.hom.hom.hom = q
    have hi : t.inv.hom.hom ≫ t.hom.hom.hom = 𝟙 _ :=
      congrArg (fun f : F.pinned.pair.T.group ⟶ F.pinned.pair.T.group ↦ f.hom.hom) t.inv_hom_id
    rw [Category.assoc, hi, Category.comp_id]
  have hv : v = cocharacter D y (CommAlgCat.of Integers.{u} B) s := by
    apply MonoidHom.ext
    intro m
    apply Units.ext
    have h := hval B p v hv₀.symm m.toAdd
    rw [hpq] at h
    let χ : Specs.CharacterDescent.Character F.pinned.pair.T.group :=
      Additive.toMul (F.datumIso.val.weightEquiv m.toAdd)
    have hpair := (RootData.CharacterPairing.characterPairingComposition F.pinned.pair.T.group
      χ (markedCocharacter F y)).2 B s
    have hdegree : pairing F.pinned.pair.T.group χ (markedCocharacter F y) =
        D.datum.toLinearMap m.toAdd y := markedPairing F m.toAdd y
    exact h.symm.trans (hpair.trans (congrArg (fun n : ℤ ↦ (↑(s ^ n) : B)) hdegree))
  let j := (fibre k).map M.torus
  let C := (integralUnitCocharacter M y).changeScalars (A := k)
  have hc : C.point B s = p ≫ j.hom.hom := by
    let ff := mapAffinePoints M.group (integerRestrictionIso B).hom
    have hff : Function.Injective ff := by
      let functor := (ringAlgebraSpec Integers.{u}).rightOp ⋙ yonedaGrp.obj M.group
      exact (functor.mapIso (integerRestrictionIso B)).groupIsoToMulEquiv.injective
    apply (scalarExtensionGroupEquiv M.group B).injective
    apply hff
    change mapAffinePoints M.group (integerRestrictionIso B).hom
      (scalarExtensionGroupEquiv M.group B (C.point B s)) =
      mapAffinePoints M.group (integerRestrictionIso B).hom
        (scalarExtensionGroupEquiv M.group B (p ≫ j.hom.hom))
    rw [map_scalarExtensionGroupEquiv_integral M.group B (p ≫ j.hom.hom),
      forgetFibrePoint_map M.torus B p, ← hv₀, hv]
    have hC : scalarExtensionGroupEquiv M.group B (C.point B s) =
        (integralUnitCocharacter M y).point (restrictAlgebra Integers.{u} B) s :=
      (scalarExtensionGroupEquiv M.group B).apply_symm_apply _
    rw [hC, mapAffinePoints_apply]
    change integralSpec.map (integerRestrictionIso B).hom.op ≫
      (torusPoint D _ (cocharacter D y _ s) ≫ M.torus.hom.hom) = _
    rw [← Category.assoc, torusPoint_after_integerRestriction]
  rw [hc, Category.assoc]
  have hj := congrArg (fun j : (fibre k).obj (splitTorus D) ⟶ F.pinned.pair.G.val ↦ j.hom.hom) ht
  change j.hom.hom ≫ e.hom.hom.hom = t.hom.hom.hom ≫ F.pinned.pair.T.inclusion.hom.hom at hj
  rw [hj, ← Category.assoc, hpq]
  rfl

private theorem fieldCocharacter_comparison (M : Model D) (y : D.Y) :
    ∃ (L : Specs.RootGroups.AdditiveLine k) (F : Realization D L)
      (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val),
      ∀ (B : TestAlgebra k) (s : Bˣ),
        ((integralUnitCocharacter M y).changeScalars (A := k)).point B s ≫ e.hom.hom.hom =
          cocharacterPoint (markedCocharacter F y ≫ F.pinned.pair.T.inclusion) B s := by
  obtain ⟨L, F, e, t, _, ht, _, hval, _⟩ := M.fieldFibre k
  exact ⟨L, F, e, fieldCocharacter_of_marking M y F e t ht hval⟩

end FieldCocharacter

section FieldOrbit

open CocharacterDynamics (orbit laurentParameter laurentAlgebra polynomialAlgebra polynomialEvaluate)

variable {k : Type u} [Field k]
variable {G H : Specs.GroupScheme k}

set_option backward.isDefEq.respectTransparency false in
private theorem orbitPoint_comp_iso (c : UnitCocharacter G) (d : Cocharacter H) (e : G ≅ H)
    (he : ∀ (B : TestAlgebra k) (s : Bˣ), c.point B s ≫ e.hom.hom.hom = cocharacterPoint d B s)
    (B : TestAlgebra k) (p : GroupPoints G B) :
    orbitPoint c B p ≫ e.hom.hom.hom = orbit d (p ≫ e.hom.hom.hom) := by
  let : IsMonHom e.hom.hom.hom := e.hom.hom.isMonHom_hom
  let g : (testSpec k).obj (op (laurentAlgebra B)) ⟶ G.X :=
    c.point (laurentAlgebra B) (laurentVariable B 1)
  let z : (testSpec k).obj (op (laurentAlgebra B)) ⟶ H.X :=
    cocharacterPoint d (laurentAlgebra B) (laurentParameter B)
  let u := (ringAlgebraSpec k).map (CommAlgCat.ofHom (laurentConstants k B)).op
  have hg : g ≫ e.hom.hom.hom = z := by
    have hz : laurentVariable B 1 = laurentParameter B := Units.ext rfl
    simpa only [g, z, hz] using he (laurentAlgebra B) (laurentVariable B 1)
  change (g * (u ≫ p) * g⁻¹) ≫ e.hom.hom.hom =
    z * (u ≫ p ≫ e.hom.hom.hom) * z⁻¹
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hg, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem hasPolynomialOrbit_iff_field (c : UnitCocharacter G) (d : Cocharacter H)
    (e : G ≅ H)
    (he : ∀ (B : TestAlgebra k) (s : Bˣ), c.point B s ≫ e.hom.hom.hom = cocharacterPoint d B s)
    (B : TestAlgebra k) (p : GroupPoints G B) :
    HasPolynomialOrbit c p ↔ HasExtension d (p ≫ e.hom.hom.hom) := by
  let i := (testSpec k).map (CocharacterDynamics.polynomialToLaurent B).op
  constructor
  · rintro ⟨q, hq⟩
    let q' : GroupPoints H (polynomialAlgebra B) := q ≫ e.hom.hom.hom
    refine ⟨mapPoints (polynomialEvaluate B 0) q', q', ?_, rfl⟩
    change i ≫ q ≫ e.hom.hom.hom = _
    rw [← Category.assoc, show i ≫ q = orbitPoint c B p from hq,
      orbitPoint_comp_iso c d e he B p]
  · rintro ⟨_, q, hq, _⟩
    let q' : GroupPoints G (polynomialAlgebra B) := q ≫ e.inv.hom.hom
    refine ⟨q', ?_⟩
    have heIso : IsIso e.hom.hom.hom := (Grp.forget (SchemeOver k)).map_isIso e.hom
    apply (cancel_mono e.hom.hom.hom).mp
    let q₀ : (testSpec k).obj (op (polynomialAlgebra B)) ⟶ H.X := q
    change (i ≫ (q₀ ≫ e.inv.hom.hom)) ≫ e.hom.hom.hom = _
    have heId : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
      congrArg (fun f : H ⟶ H ↦ f.hom.hom) e.inv_hom_id
    rw [Category.assoc, Category.assoc, heId, Category.comp_id,
      orbitPoint_comp_iso c d e he B p]
    exact hq

end FieldOrbit

section IntegralBorel

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 550000 in
/-- The integral attracting subgroup specializes to the actual field limit
parabolic, with the comparison commuting with the inclusion into the group. -/
theorem attractingSubgroupFibreIso {k : Type u} [Field k] {L : Specs.RootGroups.AdditiveLine k}
    (M : Model D) (y : D.Y)
    {H : IntegralGroup.{u}} (j : H ⟶ M.group)
    (hj : IsClosedImmersion j.hom.hom.left)
    (hpoints : ∀ (R : IntegralAlgebra.{u}) (g : IntegralPoints M.group R),
      HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
        ∃ p : IntegralPoints H R, p ≫ j.hom.hom = g)
    (F : Realization D L) (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (he : letI := integerAlgebra k; ∀ (B : TestAlgebra k) (s : Bˣ),
      ((integralUnitCocharacter M y).changeScalars (A := k)).point B s ≫ e.hom.hom.hom =
        cocharacterPoint (markedCocharacter F y ≫ F.pinned.pair.T.inclusion) B s)
    (E : CocharacterDynamics.LimitDecomposition (markedCocharacter F y ≫ F.pinned.pair.T.inclusion)) :
    ∃ u : (fibre k).obj H ≅ E.parabolic.group,
      u.hom ≫ E.parabolic.inclusion = (fibre k).map j ≫ e.hom := by
  let := integerAlgebra k
  let a := algebraSpecMap Integers.{u} k
  let P := F.pinned.pair
  let d := markedCocharacter F y ≫ P.T.inclusion
  have hj' : IsClosedImmersion ((changeBase a).map j).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare a j.hom.hom).flip hj
  let B : ClosedSubgroup ((changeBase a).obj M.group) :=
    ⟨(changeBase a).obj H, (changeBase a).map j, hj'⟩
  let J := transportClosedSubgroup e B
  have hp (C : Type u) [CommRing C] [Algebra k C] (g : coordSpec k C ⟶ P.G.val.X) :
      (∃ p : coordSpec k C ⟶ J.group.X, p ≫ J.inclusion.hom.hom = g) ↔
        ∃ p : coordSpec k C ⟶ E.parabolic.group.X, p ≫ E.parabolic.inclusion.hom.hom = g := by
    let T := CommAlgCat.of k C
    let x : GroupPoints ((changeBase a).obj M.group) T := g ≫ e.inv.hom.hom
    have hx : x ≫ e.hom.hom.hom = g := by
      change (g ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = g
      have hh : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
        congrArg (fun f : P.G.val ⟶ P.G.val ↦ f.hom.hom) e.inv_hom_id
      rw [Category.assoc, hh, Category.comp_id]
    have hl := attractingSubgroup_changeScalars (A := k) (integralUnitCocharacter M y) j
      (fun C _ _ z ↦ hpoints (CommAlgCat.of Integers.{u} C) z) T x
    have hr := hasPolynomialOrbit_iff_field ((integralUnitCocharacter M y).changeScalars (A := k))
      d e he T x
    rw [hx] at hr
    have h := E.parabolic_points T g
    change HasExtension d g ↔
      ∃ p : coordSpec k C ⟶ E.parabolic.group.X, p ≫ E.parabolic.inclusion.hom.hom = g at h
    refine Iff.trans ?_ (hl.symm.trans (hr.trans h))
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p, (cancel_mono e.hom.hom.hom).mp ?_⟩
      rw [hx, Category.assoc]
      exact hp
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      change p ≫ B.inclusion.hom.hom ≫ e.hom.hom.hom = g
      rw [← Category.assoc, hp, hx]
  exact subgroupIsoOfAlgebraPoints P.G.property.1 J.inclusion E.parabolic.inclusion
    J.isClosedImmersion E.parabolic.isClosedImmersion hp


variable {D : BasedRootDatum.{u}}

private theorem integralBaseMap_eq {k : Type u} [Field k] (a : ringSpec k ⟶ Base.{u}) :
    a = integralSpecMap k := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective a
  congr 1
  ext x
  exact map_intCast (f.hom.comp (ULift.ringEquiv : Integers.{u} ≃+* ℤ).symm.toRingHom) x.down

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
/-- A regular cocharacter of the marked torus defines a smooth closed subgroup
with Borel geometric fibres. -/
theorem integralBorelOfRegularCocharacter (M : Model D) (y : D.Y)
    (hy : ∀ i : D.I, D.datum.toLinearMap (D.datum.root i) y ≠ 0) :
    ∃ (H : IntegralGroup.{u}) (j : H ⟶ M.group),
      IsClosedImmersion j.hom.hom.left ∧ Smooth H.X.hom ∧
      (∀ (B : IntegralAlgebra.{u}) (g : IntegralPoints M.group B),
        HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
          ∃ p : IntegralPoints H B, p ≫ j.hom.hom = g) ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ Base.{u}),
        ∃ hc : IsClosedImmersion ((changeBase a).map j).hom.hom.left,
          IsBorel (G := (changeBase a).obj M.group) ⟨(changeBase a).obj H, (changeBase a).map j, hc⟩ := by
  obtain ⟨H, j, hj, hs, hpoints⟩ := integralAttractingSubgroup M y
  refine ⟨H, j, hj, hs, hpoints, ?_⟩
  intro k _ _ a
  have ha := integralBaseMap_eq a
  subst a
  let := integerAlgebra k
  let a := algebraSpecMap Integers.{u} k
  have hj' : IsClosedImmersion ((changeBase a).map j).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare a j.hom.hom).flip hj
  let B : ClosedSubgroup ((changeBase a).obj M.group) :=
    ⟨(changeBase a).obj H, (changeBase a).map j, hj'⟩
  refine ⟨hj', ?_⟩
  obtain ⟨L, F, e, he⟩ := fieldCocharacter_comparison (k := k) M y
  let P := F.pinned.pair
  let c := markedCocharacter F y
  let d := c ≫ P.T.inclusion
  have hc : IsRegular P.T c := markedCocharacter_regular F y hy
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition P.G d
  have hE : IsBorel E.parabolic := regular_isBorel P.G P.reductive P.T P.split P.maximal c hc E
    (centralizer_of_regular P.G P.reductive P.T P.split P.maximal c hc E)
  let J := transportClosedSubgroup e B
  obtain ⟨u, hu⟩ := attractingSubgroupFibreIso M y j hj hpoints F e he E
  have hsame : SameSubgroup E.parabolic J := by
    refine ⟨⟨u.inv, ?_⟩, ⟨u.hom, hu⟩⟩
    change u.inv ≫ ((fibre k).map j ≫ e.hom) = E.parabolic.inclusion
    rw [← hu, Iso.inv_hom_id_assoc]
  exact (isBorel_transport_iff e B).mp (borel_of_same (H := P.G) hE hsame)

/-- A split integral model has a smooth closed subgroup which is Borel on every
geometric fibre. The inclusions are the scalar extensions of one integral map. -/
theorem integralBorel (M : Model D) :
    ∃ (H : IntegralGroup.{u}) (j : H ⟶ M.group),
      IsClosedImmersion j.hom.hom.left ∧ Smooth H.X.hom ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ Base.{u}),
        ∃ hc : IsClosedImmersion ((changeBase a).map j).hom.hom.left,
          IsBorel (G := (changeBase a).obj M.group) ⟨(changeBase a).obj H, (changeBase a).map j, hc⟩ := by
  obtain ⟨height, n, hn, hheight⟩ := Classification.IntegralLattices.exists_integralHeight D
  let y := D.datum.toLinearMap.flip.toPerfPair.symm height
  have hy (i : D.I) : D.datum.toLinearMap (D.datum.root i) y ≠ 0 := by
    change D.datum.toLinearMap.flip y (D.datum.root i) ≠ 0
    change (D.datum.toLinearMap.flip.toPerfPair y) (D.datum.root i) ≠ 0
    rw [LinearEquiv.apply_symm_apply, hheight]
    exact mul_ne_zero (ne_of_gt hn) (D.base.height_ne_zero i)
  obtain ⟨H, j, hclosed, hsmooth, _, hB⟩ := integralBorelOfRegularCocharacter M y hy
  exact ⟨H, j, hclosed, hsmooth, hB⟩

end IntegralBorel

section PositiveRoots

open Specs.IntegralSemisimpleModel (AdditiveLine additivePoint product rootProduct)

private theorem additivePoint_natural {B C : IntegralAlgebra.{u}} (f : B ⟶ C) (z : B) :
    integralSpec.map f.op ≫ additivePoint B z = additivePoint C (f.hom z) := by
  change coordSpecMap f.hom ≫ coordSpecMap (Polynomial.aeval z : Polynomial Integers.{u} →ₐ[_] B) =
    coordSpecMap (Polynomial.aeval (f.hom z) : Polynomial Integers.{u} →ₐ[_] C)
  rw [← coordSpecMap_comp]
  congr 1
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply, Polynomial.aeval_X]

private theorem linePoint_natural (L : AdditiveLine.{u}) {B C : IntegralAlgebra.{u}}
    (f : B ⟶ C) (z : B) :
    integralSpec.map f.op ≫ L.point B z = L.point C (f.hom z) :=
  additivePoint_natural f z

set_option backward.isDefEq.respectTransparency false in
/-- A marked root with nonnegative weight lies in the integral attracting locus. -/
theorem integralRoot_hasPolynomialOrbit {D : BasedRootDatum.{u}} (M : Model D)
    (y : D.Y) (i : D.I) (hi : 0 ≤ D.datum.toLinearMap (D.datum.root i) y)
    (B : IntegralAlgebra.{u}) (z : B) :
    HasPolynomialOrbit (integralUnitCocharacter M y)
      (M.line.point B z ≫ (M.root i).hom.hom) := by
  let P := CommAlgCat.of Integers.{u} (Polynomial B)
  let L := CommAlgCat.of Integers.{u} (LaurentPolynomial B)
  let t := laurentVariable B 1
  let v := cocharacter D y L t
  let n := (D.datum.toLinearMap (D.datum.root i) y).toNat
  let f : B ⟶ L := CommAlgCat.ofHom (laurentConstants Integers.{u} B)
  let j : P ⟶ L := CommAlgCat.ofHom (toLaurentOver (R := Integers.{u}) (B := B))
  let s := torusPoint D L v ≫ M.torus.hom.hom
  refine ⟨M.line.point P (Polynomial.C z * Polynomial.X ^ n) ≫ (M.root i).hom.hom, ?_⟩
  change integralSpec.map j.op ≫
      (M.line.point P (Polynomial.C z * Polynomial.X ^ n) ≫ (M.root i).hom.hom) =
    s * (integralSpec.map f.op ≫ (M.line.point B z ≫ (M.root i).hom.hom)) * s⁻¹
  rw [← Category.assoc (integralSpec.map j.op), linePoint_natural,
    ← Category.assoc (integralSpec.map f.op), linePoint_natural, M.conjugation]
  congr 1
  congr 1
  change (Polynomial.C z * Polynomial.X ^ n).toLaurent =
    (↑(t ^ D.datum.toLinearMap (D.datum.root i) y) : LaurentPolynomial B) * LaurentPolynomial.C z
  rw [laurentVariable_pow, Polynomial.toLaurent_C_mul_X_pow, mul_comm]
  have hn : (n : ℤ) = D.datum.toLinearMap (D.datum.root i) y := Int.toNat_of_nonneg hi
  rw [hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The marked torus is fixed by conjugation by the cocharacter. -/
theorem integralTorus_hasPolynomialOrbit {D : BasedRootDatum.{u}} (M : Model D)
    (y : D.Y) (B : IntegralAlgebra.{u}) (v : TorusValues D B) :
    HasPolynomialOrbit (integralUnitCocharacter M y)
      (torusPoint D B v ≫ M.torus.hom.hom) := by
  let P := CommAlgCat.of Integers.{u} (Polynomial B)
  let L := CommAlgCat.of Integers.{u} (LaurentPolynomial B)
  let p : B ⟶ P := CommAlgCat.ofHom (IsScalarTower.toAlgHom Integers.{u} B (Polynomial B))
  let j : P ⟶ L := CommAlgCat.ofHom (toLaurentOver (R := Integers.{u}) (B := B))
  let f : B ⟶ L := CommAlgCat.ofHom (laurentConstants Integers.{u} B)
  let g := torusPoint D B v ≫ M.torus.hom.hom
  let w := cocharacter D y L (laurentVariable B 1)
  let t := torusPoint D L w ≫ M.torus.hom.hom
  have hcomp : p ≫ j = f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    exact Polynomial.toLaurent_C b
  have hconj : t * (integralSpec.map f.op ≫ g) = (integralSpec.map f.op ≫ g) * t := by
    change (torusPoint D L w ≫ M.torus.hom.hom) *
        (integralSpec.map f.op ≫ (torusPoint D B v ≫ M.torus.hom.hom)) =
      (integralSpec.map f.op ≫ (torusPoint D B v ≫ M.torus.hom.hom)) *
        (torusPoint D L w ≫ M.torus.hom.hom)
    rw [← Category.assoc (integralSpec.map f.op), torusPoint_natural,
      ← MonObj.mul_comp, ← MonObj.mul_comp, ← torusPoint_mul, ← torusPoint_mul]
    apply congrArg (fun u : TorusValues D L ↦ torusPoint D L u ≫ M.torus.hom.hom)
    apply MonoidHom.ext
    intro m
    exact mul_comm (w m) (Units.map f.hom.toMonoidHom (v m))
  refine ⟨integralSpec.map p.op ≫ g, ?_⟩
  change integralSpec.map j.op ≫ integralSpec.map p.op ≫ g =
    t * (integralSpec.map f.op ≫ g) * t⁻¹
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp, hcomp, hconj,
    mul_assoc, mul_inv_cancel, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The torus and each marked root of nonnegative weight factor through the
integral attracting subgroup. -/
theorem markedSubgroupsFactor {D : BasedRootDatum.{u}} (M : Model D) (y : D.Y)
    {H : IntegralGroup.{u}} (j : H ⟶ M.group)
    (hj : ∀ (B : IntegralAlgebra.{u}) (g : IntegralPoints M.group B),
      HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
        ∃ p : IntegralPoints H B, p ≫ j.hom.hom = g) :
    (∃ t : (splitTorus D).X ⟶ H.X, t ≫ j.hom.hom = M.torus.hom.hom) ∧
      ∀ i : D.I, 0 ≤ D.datum.toLinearMap (D.datum.root i) y →
        ∃ x : M.line.group.X ⟶ H.X, x ≫ j.hom.hom = (M.root i).hom.hom := by
  constructor
  · let B := CommAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative D.X))
    have hb : (integralSpec.obj (op B)) = (splitTorus D).X := rfl
    obtain ⟨v, hv⟩ := torusPoint_surjective D B (eqToHom hb)
    obtain ⟨t, ht⟩ := (hj B _).mp (integralTorus_hasPolynomialOrbit M y B v)
    refine ⟨eqToHom hb.symm ≫ t, ?_⟩
    rw [Category.assoc, ht, hv, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · intro i hi
    let B := CommAlgCat.of Integers.{u} (Polynomial Integers.{u})
    let x := (Polynomial.X : B)
    have hx : M.line.point B x = 𝟙 M.line.group.X := by
      change integralSpec.map (CommAlgCat.ofHom (Polynomial.aeval (Polynomial.X :
        Polynomial Integers.{u}))).op = _
      rw [Polynomial.aeval_X_left]
      exact CategoryTheory.Functor.map_id _ _
    obtain ⟨p, hp⟩ := (hj B _).mp (integralRoot_hasPolynomialOrbit M y i hi B x)
    let p' : M.line.group.X ⟶ H.X := p
    refine ⟨p', hp.trans ?_⟩
    exact (congrArg (· ≫ (M.root i).hom.hom) hx).trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- The ordered product of the torus and the marked nonnegative root factors
maps into the attracting subgroup. -/
theorem markedPositiveProductFactors {D : BasedRootDatum.{u}} (M : Model D) (y : D.Y)
    {H : IntegralGroup.{u}} (j : H ⟶ M.group)
    (hj : ∀ (B : IntegralAlgebra.{u}) (g : IntegralPoints M.group B),
      HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
        ∃ p : IntegralPoints H B, p ≫ j.hom.hom = g)
    (l : List D.I) (hl : ∀ i ∈ l, 0 ≤ D.datum.toLinearMap (D.datum.root i) y) :
    ∃ f : (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) l ⟶ H.X,
      f ≫ j.hom.hom =
        (fst _ _ ≫ M.torus.hom.hom) * (snd _ _ ≫ rootProduct M.line M.root l) := by
  obtain ⟨⟨t, ht⟩, hroot⟩ := markedSubgroupsFactor M y j hj
  have hlist (p : List D.I) (hp : ∀ i ∈ p, 0 ≤ D.datum.toLinearMap (D.datum.root i) y) :
      ∃ f : product (fun _ : D.I ↦ M.line.group.X) p ⟶ H.X,
        f ≫ j.hom.hom = rootProduct M.line M.root p := by
    induction p with
    | nil => exact ⟨1, MonObj.one_comp _⟩
    | cons a p ih =>
        obtain ⟨u, hu⟩ := hroot a (hp a (List.mem_cons.mpr (Or.inl rfl)))
        obtain ⟨w, hw⟩ := ih fun b hb ↦ hp b (List.mem_cons.mpr (Or.inr hb))
        refine ⟨(fst _ _ ≫ u) * (snd _ _ ≫ w), ?_⟩
        rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, hw]
        rfl
  obtain ⟨n, hn⟩ := hlist l hl
  exact ⟨(fst _ _ ≫ t) * (snd _ _ ≫ n),
    by rw [MonObj.mul_comp, Category.assoc, Category.assoc, ht, hn]⟩

end PositiveRoots

section IntegralCell

open Specs.IntegralSemisimpleModel (cellMap product rootProduct)
open Specs.Pinning (RootCoordinate)
open Specs.OrderedRootProducts (Enumerates)
open Specs.BorelsAndChambers (positiveRoots)
open CocharacterDynamics (LimitDecomposition)

open private forgetFibrePoint_surjective lineProduct_affine lineProductIso
  from LinearAlgebraicGroups.Classification.IntegralRealization
open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private rootPoint_eq from LinearAlgebraicGroups.RootData.RootGroups

section FieldFactors

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}}

attribute [local instance] integerAlgebra

private theorem forgetFibrePoint_one (G : IntegralGroup.{u}) (B : TestAlgebra k) :
    forgetFibrePoint G B 1 = 1 := by
  rw [← map_scalarExtensionGroupEquiv_integral]
  exact ((mapAffinePoints G (integerRestrictionIso B).hom).comp
    (scalarExtensionGroupEquiv G B).toMonoidHom).map_one

private theorem forgetFibrePoint_mul (G : IntegralGroup.{u}) (B : TestAlgebra k)
    (p q : GroupPoints ((fibre k).obj G) B) :
    forgetFibrePoint G B (p * q) = forgetFibrePoint G B p * forgetFibrePoint G B q := by
  simp only [← map_scalarExtensionGroupEquiv_integral]
  exact ((mapAffinePoints G (integerRestrictionIso B).hom).comp
    (scalarExtensionGroupEquiv G B).toMonoidHom).map_mul p q

set_option backward.isDefEq.respectTransparency false in
private theorem markedRootWeight {L : Specs.RootGroups.AdditiveLine k} (F : Realization D L)
    (y : D.Y) (i : D.I) :
    pairing F.pinned.pair.T.group (F.datumIso.val.indexEquiv i).val (markedCocharacter F y) =
      D.datum.toLinearMap (D.datum.root i) y := by
  let := F.attached.comm
  rw [← F.attached.datum.pairing_eq, ← F.attached.datum.root_eq]
  change F.attached.toBased.datum.root' (F.datumIso.val.indexEquiv i)
    (F.datumIso.val.coweightEquiv.symm y) = _
  exact F.datumIso.val.root'_coweightEquiv i y

set_option backward.isDefEq.respectTransparency false in
private theorem integralRootProductPoint (M : Model D)
    {L : Specs.RootGroups.AdditiveLine k} (F : Realization D L)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (z : ∀ i : D.I, RootCoordinate L F.pinned.pair.T
      (F.pinned.roots (F.datumIso.val.indexEquiv i)).val (F.datumIso.val.indexEquiv i).val)
    (hz : ∀ (i : D.I) (B : TestAlgebra k) (r : B),
      forgetFibrePoint M.group B
          (Specs.RootGroups.rootPoint ((z i).val.hom ≫
            (F.pinned.roots (F.datumIso.val.indexEquiv i)).val.inclusion ≫ e.inv) B r) =
        M.line.point (CommAlgCat.of Integers.{u} B) r ≫ (M.root i).hom.hom)
    (B : TestAlgebra k) (l : List D.I) (p : (testSpec k).obj (op B) ⟶
      Specs.OrderedRootProducts.product (fun α ↦ (F.pinned.roots α).val.group.X)
        (l.map F.datumIso.val.indexEquiv)) :
    ∃ q : integralSpec.obj (op (CommAlgCat.of Integers.{u} B)) ⟶
        product (fun _ : D.I ↦ M.line.group.X) l,
      q ≫ rootProduct M.line M.root l =
        forgetFibrePoint M.group B
          (p ≫ Specs.OrderedRootProducts.rootProduct F.pinned.roots
             (l.map F.datumIso.val.indexEquiv) ≫ e.inv.hom.hom) := by
  let S := CommAlgCat.of Integers.{u} B
  induction l with
  | nil =>
    refine ⟨toUnit _, ?_⟩
    change (toUnit _ ≫ (1 : 𝟙_ (Over Base.{u}) ⟶ M.group.X)) =
      forgetFibrePoint M.group B (p ≫ (1 : 𝟙_ (SchemeOver k) ⟶ F.pinned.pair.G.val.X) ≫ e.inv.hom.hom)
    let : IsMonHom e.inv.hom.hom := e.inv.hom.isMonHom_hom
    rw [MonObj.comp_one, MonObj.one_comp, MonObj.comp_one, forgetFibrePoint_one]
  | cons i l ih =>
    let α := F.datumIso.val.indexEquiv i
    let U := (F.pinned.roots α).val
    let u : GroupPoints U.group B := p ≫ fst _ _
    let w := (z i).val
    obtain ⟨r, hr⟩ := (LinearAlgebraicGroups.RootData.RootGroups.additivePoints L B).surjective (u ≫ w.inv.hom.hom)
    let q₁ := M.line.point S r
    let p₂ := p ≫ snd _ _
    obtain ⟨q₂, hq₂⟩ := ih p₂
    refine ⟨lift q₁ q₂, ?_⟩
    have hw : Specs.RootGroups.rootPoint (w.hom ≫ U.inclusion ≫ e.inv) B r =
        u ≫ U.inclusion.hom.hom ≫ e.inv.hom.hom := by
      rw [rootPoint_eq, hr]
      change (u ≫ w.inv.hom.hom) ≫
        w.hom.hom.hom ≫ U.inclusion.hom.hom ≫ e.inv.hom.hom = _
      have h := (Grp.forget (SchemeOver k)).congr_map w.inv_hom_id
      change w.inv.hom.hom ≫ w.hom.hom.hom = 𝟙 _ at h
      rw [Category.assoc, ← Category.assoc w.inv.hom.hom, h, Category.id_comp]
    have hq₁ := (hz i B r).symm
    change q₁ ≫ (M.root i).hom.hom =
      forgetFibrePoint M.group B (Specs.RootGroups.rootPoint (w.hom ≫ U.inclusion ≫ e.inv) B r) at hq₁
    rw [hw] at hq₁
    let : IsMonHom e.inv.hom.hom := e.inv.hom.isMonHom_hom
    change lift q₁ q₂ ≫
      ((fst _ _ ≫ (M.root i).hom.hom) * (snd _ _ ≫ rootProduct M.line M.root l)) =
      forgetFibrePoint M.group B (p ≫
        ((fst _ _ ≫ U.inclusion.hom.hom) *
          (snd _ _ ≫ Specs.OrderedRootProducts.rootProduct F.pinned.roots
            (l.map F.datumIso.val.indexEquiv))) ≫ e.inv.hom.hom)
    simp only [MonObj.comp_mul, MonObj.mul_comp, ← Category.assoc, lift_fst, lift_snd]
    rw [hq₁, hq₂, ← forgetFibrePoint_mul]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem integralPositiveFactors_onField (M : Model D) (y : D.Y)
    (hy : ∀ i, D.datum.toLinearMap (D.datum.root i) y ≠ 0)
    (l : List D.I) (hl : Enumerates l {i | 0 < D.datum.toLinearMap (D.datum.root i) y})
    (B : TestAlgebra k) (p : GroupPoints ((fibre k).obj M.group) B)
    (hp : HasPolynomialOrbit ((integralUnitCocharacter M y).changeScalars (A := k)) p) :
    ∃ q : integralSpec.obj (op (CommAlgCat.of Integers.{u} B)) ⟶
        (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) l,
      q ≫ ((fst _ _ ≫ M.torus.hom.hom) * (snd _ _ ≫ rootProduct M.line M.root l)) =
        forgetFibrePoint M.group B p := by
  obtain ⟨L, F, e, t, z, ht, _, hval, hz⟩ := M.fieldFibre k
  let P := F.pinned.pair
  let c := markedCocharacter F y
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition P.G (c ≫ P.T.inclusion)
  have hreg := markedCocharacter_regular F y hy
  obtain ⟨j, hj⟩ := (centralizer_of_regular P.G P.reductive P.T P.split P.maximal c hreg E).1
  let φ := F.datumIso.val.indexEquiv
  have hl' : Enumerates (l.map φ) (positiveRoots P.T c) := by
    refine ⟨hl.1.map φ.injective, ?_⟩
    intro α
    obtain ⟨i, rfl⟩ := φ.surjective α
    rw [List.mem_map]
    change (∃ i' ∈ l, φ i' = φ i) ↔
      0 < pairing F.pinned.pair.T.group (F.datumIso.val.indexEquiv i).val (markedCocharacter F y)
    rw [markedRootWeight]
    exact ⟨fun ⟨i', hi', h⟩ ↦ (hl.2 i).mp (φ.injective h ▸ hi'),
      fun hi ↦ ⟨i, (hl.2 i).mpr hi, rfl⟩⟩
  obtain ⟨q, hq⟩ := ((RootData.OrderedRootProducts.contractingProduct
    P.G P.reductive P.T P.split P.maximal).2.2 c).2 E F.pinned.roots (l.map φ) hl'
  let X := (testSpec k).obj (op B)
  let g : X ⟶ P.G.val.X := p ≫ e.hom.hom.hom
  have hExt : HasExtension (c ≫ P.T.inclusion) g :=
    (hasPolynomialOrbit_iff_field _ _ e (fieldCocharacter_of_marking M y F e t ht hval) B p).mp hp
  obtain ⟨a, ha⟩ := (E.parabolic_points B g).mp hExt
  let a' : (testSpec k).obj (op B) ⟶ E.parabolic.group.X := a
  have ha' : a' ≫ E.parabolic.inclusion.hom.hom = g := ha
  let mul := CocharacterDynamics.multiplyFactors E.sectionMap E.contractingToParabolic
  have : IsIso mul := E.product_iso
  let m := a' ≫ inv mul
  let v : X ⟶ P.T.group.X := m ≫ fst _ _ ≫ j.hom.hom
  let w : X ⟶ _ := m ≫ snd _ _ ≫ q.inv
  let r : X ⟶ ((fibre k).obj (splitTorus D)).X := v ≫ t.inv.hom.hom
  let v₀ : X ⟶ P.G.val.X := v ≫ P.T.inclusion.hom.hom
  let v₁ : X ⟶ P.G.val.X := w ≫ Specs.OrderedRootProducts.rootProduct F.pinned.roots (l.map φ)
  obtain ⟨s, hs⟩ := integralRootProductPoint M F e z hz B l w
  refine ⟨lift (forgetFibrePoint (splitTorus D) B r) s, ?_⟩
  have hm : v ≫ P.T.inclusion.hom.hom =
      m ≫ fst _ _ ≫ E.centralizer.inclusion.hom.hom := by
    have h := (Grp.forget (SchemeOver k)).congr_map hj
    change j.hom.hom ≫ P.T.inclusion.hom.hom = E.centralizer.inclusion.hom.hom at h
    simp only [v, Category.assoc, h]
  have hsub : v₀ * v₁ = g := by
    have h₁ : v₁ = m ≫ snd _ _ ≫ E.contracting.inclusion.hom.hom := by
      simp only [v₁, w, ← hq, Category.assoc, Iso.inv_hom_id_assoc]
    rw [show v₀ = _ from hm, h₁]
    calc
      _ = (m ≫ mul) ≫ E.parabolic.inclusion.hom.hom := by
        let : IsMonHom E.parabolic.inclusion.hom.hom := E.parabolic.inclusion.hom.isMonHom_hom
        have hel := congrArg (fun f : E.centralizer.group ⟶ P.G.val ↦ f.hom.hom) E.section_in_G
        have her := congrArg (fun f : E.contracting.group ⟶ P.G.val ↦ f.hom.hom) E.contracting_in_G
        change E.sectionMap.hom.hom ≫ E.parabolic.inclusion.hom.hom = _ at hel
        change E.contractingToParabolic.hom.hom ≫ E.parabolic.inclusion.hom.hom = _ at her
        simp only [mul, CocharacterDynamics.multiplyFactors, MonObj.comp_mul, MonObj.mul_comp,
          Category.assoc, hel, her]
      _ = g := by
        simpa only [m, Category.assoc, IsIso.inv_hom_id, Category.comp_id] using ha'
  have ht' : r ≫ ((fibre k).map M.torus).hom.hom =
      v ≫ P.T.inclusion.hom.hom ≫ e.inv.hom.hom := by
    have h := (Grp.forget (SchemeOver k)).congr_map ht
    change ((fibre k).map M.torus).hom.hom ≫ e.hom.hom.hom =
      t.hom.hom.hom ≫ P.T.inclusion.hom.hom at h
    have hte := (Grp.forget (SchemeOver k)).congr_map t.inv_hom_id
    have he := (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
    change t.inv.hom.hom ≫ t.hom.hom.hom = 𝟙 _ at hte
    change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ at he
    have : Mono e.hom.hom.hom := (Grp.forget (SchemeOver k)).map_mono e.hom
    apply (cancel_mono e.hom.hom.hom).mp
    calc
      _ = v ≫ P.T.inclusion.hom.hom := by
        simp only [r, Category.assoc, h, reassoc_of% hte]
      _ = _ := by
        simp only [Category.assoc, he]
        exact (Category.comp_id _).symm
  simp only [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, hs]
  rw [← forgetFibrePoint_map, ht', ← forgetFibrePoint_mul]
  congr 1
  let : IsMonHom e.inv.hom.hom := e.inv.hom.isMonHom_hom
  have hi := (Grp.forget (SchemeOver k)).congr_map e.hom_inv_id
  change e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ at hi
  change (v₀ ≫ e.inv.hom.hom) * (v₁ ≫ e.inv.hom.hom) = p
  rw [← MonObj.mul_comp, hsub]
  change (p ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = p
  simp only [Category.assoc, hi, Category.comp_id]

end FieldFactors

variable {D : BasedRootDatum.{u}}

set_option backward.isDefEq.respectTransparency false in
private theorem markedPositiveProduct_surjective (M : Model D) (y : D.Y)
    (hy : ∀ i, D.datum.toLinearMap (D.datum.root i) y ≠ 0)
    {H : IntegralGroup.{u}} (j : H ⟶ M.group) (hclosed : IsClosedImmersion j.hom.hom.left)
    (hj : ∀ (B : IntegralAlgebra.{u}) (g : IntegralPoints M.group B),
      HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
        ∃ p : IntegralPoints H B, p ≫ j.hom.hom = g)
    (positive : List D.I) (hpositive : Enumerates positive
      {i | 0 < D.datum.toLinearMap (D.datum.root i) y})
    (f : (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) positive ⟶ H.X)
    (hf : f ≫ j.hom.hom =
      (fst _ _ ≫ M.torus.hom.hom) * (snd _ _ ≫ rootProduct M.line M.root positive)) :
    Surjective f.left := by
  refine ⟨fun x ↦ ?_⟩
  let K := H.X.left.residueField x
  let B : TestAlgebra K := CommAlgCat.of K K
  let := integerAlgebra K
  let S : IntegralAlgebra.{u} := CommAlgCat.of Integers.{u} K
  let p : IntegralPoints H S := Over.homMk (H.X.left.fromSpecResidueField x)
    (integralBaseMap_eq _)
  obtain ⟨q, hq⟩ := forgetFibrePoint_surjective H B p
  let g : GroupPoints ((fibre K).obj M.group) B := q ≫ ((fibre K).map j).hom.hom
  have hg : HasPolynomialOrbit ((integralUnitCocharacter M y).changeScalars (A := K)) g :=
    (attractingSubgroup_changeScalars (A := K) (integralUnitCocharacter M y) j
      (fun C _ _ z ↦ hj (CommAlgCat.of Integers.{u} C) z) B g).mpr ⟨q, rfl⟩
  obtain ⟨w, hw⟩ := integralPositiveFactors_onField M y hy positive hpositive B g hg
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hwp : w ≫ f = p := by
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, hf, hw, show g = q ≫ ((fibre K).map j).hom.hom from rfl,
      forgetFibrePoint_map, hq]
  refine ⟨w.left (IsLocalRing.closedPoint K), ?_⟩
  have he := congrArg (fun a : integralSpec.obj (op S) ⟶ H.X ↦
    a.left (IsLocalRing.closedPoint K)) hwp
  exact he.trans (Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint K))

private def rootProductIdentity (M : Model D) :
    (l : List D.I) → 𝟙_ (Over Base.{u}) ⟶ product (fun _ : D.I ↦ M.line.group.X) l
  | [] => 𝟙 _
  | _ :: l =>
      letI : GrpObj M.line.group.X := M.line.group.grp
      lift η[M.line.group.X] (rootProductIdentity M l)

private theorem rootProductIdentity_comp (M : Model D) (l : List D.I) :
    rootProductIdentity M l ≫ rootProduct M.line M.root l = 1 := by
  induction l with
  | nil => exact Category.id_comp _
  | cons i l ih =>
      let : GrpObj M.line.group.X := M.line.group.grp
      change lift η[M.line.group.X] (rootProductIdentity M l) ≫
        ((fst _ _ ≫ (M.root i).hom.hom) * (snd _ _ ≫ rootProduct M.line M.root l)) = 1
      let : IsMonHom (M.root i).hom.hom := (M.root i).hom.isMonHom_hom
      simp only [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, ih, mul_one]
      exact IsMonHom.one_hom _

private theorem reduced_of_smooth_over_reduced {X S : Scheme.{u}} (a : X ⟶ S)
    [Smooth a] [IsReduced S] [IsLocallyNoetherian S] : IsReduced X := by
  have : GeometricallyReduced a := by
    rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
    intro K _ b
    have : Smooth (pullback.snd a b) := inferInstance
    exact isReduced_of_smooth_over_field (pullback.snd a b)
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian a

set_option backward.isDefEq.respectTransparency false in
private theorem markedPositiveProduct_isIso (M : Model D) (y : D.Y)
    (hy : ∀ i, D.datum.toLinearMap (D.datum.root i) y ≠ 0)
    {H : IntegralGroup.{u}} (j : H ⟶ M.group) (hclosed : IsClosedImmersion j.hom.hom.left)
    (hsmooth : Smooth H.X.hom)
    (hj : ∀ (B : IntegralAlgebra.{u}) (g : IntegralPoints M.group B),
      HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
        ∃ p : IntegralPoints H B, p ≫ j.hom.hom = g)
    (negative positive : List D.I) (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i})
    (hpos : ∀ i, D.base.IsPos i ↔ 0 < D.datum.toLinearMap (D.datum.root i) y)
    (f : (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) positive ⟶ H.X)
    (hf : f ≫ j.hom.hom =
      (fst _ _ ≫ M.torus.hom.hom) * (snd _ _ ≫ rootProduct M.line M.root positive)) :
    IsIso f := by
  let N := product (fun _ : D.I ↦ M.line.group.X) negative
  let P := (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) positive
  let a : P ⟶ N ⊗ P := lift (toUnit P ≫ rootProductIdentity M negative) (𝟙 P)
  let b := cellMap M.line M.torus M.root negative positive
  have hnegative : IsAffine N.left := by
    let e := (Over.forget Base.{u}).mapIso (lineProductIso M.line negative)
    exact @IsAffine.of_isIso _ _ e.inv (by infer_instance) (lineProduct_affine negative)
  have hsnd : IsSeparated (snd N P).left := by
    change IsSeparated (pullback.snd N.hom P.hom)
    infer_instance
  have hcomp : IsClosedImmersion (a.left ≫ (snd N P).left) := by
    change IsClosedImmersion ((a ≫ snd N P).left)
    rw [show a ≫ snd N P = 𝟙 P from lift_snd _ _]
    infer_instance
  have : IsClosedImmersion a.left := IsClosedImmersion.of_comp a.left (snd N P).left
  have : IsOpenImmersion b.left := M.openCell negative positive hn hp
  have hab : a ≫ b = f ≫ j.hom.hom := by
    rw [hf]
    change a ≫ ((fst N P ≫ rootProduct M.line M.root negative) *
      (snd N P ≫ ((fst _ _ ≫ M.torus.hom.hom) *
        (snd _ _ ≫ rootProduct M.line M.root positive)))) = _
    have ha : a ≫ fst N P = toUnit P ≫ rootProductIdentity M negative := lift_fst _ _
    have hb : a ≫ snd N P = 𝟙 P := lift_snd _ _
    rw [MonObj.comp_mul, reassoc_of% ha, reassoc_of% hb,
      rootProductIdentity_comp, MonObj.comp_one, one_mul]
  have : IsImmersion (f.left ≫ j.hom.hom.left) := by
    change IsImmersion (f ≫ j.hom.hom).left
    rw [← hab]
    change IsImmersion (a.left ≫ b.left)
    infer_instance
  have : IsImmersion f.left := IsImmersion.of_comp f.left j.hom.hom.left
  have : Surjective f.left :=
    markedPositiveProduct_surjective M y hy j hclosed hj positive
      ⟨hp.1, fun i ↦ (hp.2 i).trans (hpos i)⟩ f hf
  have : IsClosedImmersion f.left := IsClosedImmersion.of_isPreimmersion f.left
    (by rw [Set.range_eq_univ.mpr f.left.surjective]; exact isClosed_univ)
  have : IsDomain Integers.{u} :=
    ULift.ringEquiv.injective.isDomain (ULift.ringEquiv : Integers.{u} ≃+* ℤ)
  have : IsNoetherianRing Integers.{u} := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsReduced H.X.left := reduced_of_smooth_over_reduced H.X.hom
  have : IsIso ((Over.forget Base.{u}).map f) :=
    isIso_of_isClosedImmersion_of_surjective f.left
  exact isIso_of_reflects_iso f (Over.forget Base.{u})

set_option backward.isDefEq.respectTransparency false in
private theorem existsRegularPositiveCocharacter (D : BasedRootDatum.{u}) :
    ∃ y : D.Y, (∀ i, D.datum.toLinearMap (D.datum.root i) y ≠ 0) ∧
      ∀ i, D.base.IsPos i ↔ 0 < D.datum.toLinearMap (D.datum.root i) y := by
  obtain ⟨height, n, hn, hheight⟩ := Classification.IntegralLattices.exists_integralHeight D
  let y := D.datum.toLinearMap.flip.toPerfPair.symm height
  have hw (i : D.I) : D.datum.toLinearMap (D.datum.root i) y = n * D.base.height i := by
    change (D.datum.toLinearMap.flip.toPerfPair y) (D.datum.root i) = _
    rw [LinearEquiv.apply_symm_apply, hheight]
  have hy (i : D.I) : D.datum.toLinearMap (D.datum.root i) y ≠ 0 := by
    rw [hw]
    exact mul_ne_zero (ne_of_gt hn) (D.base.height_ne_zero i)
  have hpos (i : D.I) : D.base.IsPos i ↔ 0 < D.datum.toLinearMap (D.datum.root i) y := by
    rw [hw, D.base.isPos_iff, mul_pos_iff_of_pos_left hn]
  exact ⟨y, hy, hpos⟩

set_option backward.isDefEq.respectTransparency false in
private theorem integralBorelBigCellOfCocharacter (M : Model D) (y : D.Y)
    (hy : ∀ i, D.datum.toLinearMap (D.datum.root i) y ≠ 0)
    (hpos : ∀ i, D.base.IsPos i ↔ 0 < D.datum.toLinearMap (D.datum.root i) y) :
    ∃ (H : IntegralGroup.{u}) (j : H ⟶ M.group),
      IsClosedImmersion j.hom.hom.left ∧ Smooth H.X.hom ∧
      (∀ (R : IntegralAlgebra.{u}) (g : IntegralPoints M.group R),
        HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
          ∃ p : IntegralPoints H R, p ≫ j.hom.hom = g) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ Base.{u}),
        ∃ hc : IsClosedImmersion ((changeBase a).map j).hom.hom.left,
          Specs.GeometricBorelConjugacy.IsBorel (G := (changeBase a).obj M.group)
            ⟨(changeBase a).obj H, (changeBase a).map j, hc⟩) ∧
      ∀ (negative positive : List D.I), Enumerates negative {i | ¬ D.base.IsPos i} →
        Enumerates positive {i | D.base.IsPos i} →
        ∃ e : (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) positive ≅ H.X,
          e.hom ≫ j.hom.hom =
            (fst _ _ ≫ M.torus.hom.hom) * (snd _ _ ≫ rootProduct M.line M.root positive) ∧
          IsOpenImmersion (((fst _ _ ≫ rootProduct M.line M.root negative) *
            (snd _ _ ≫ j.hom.hom)) :
              product (fun _ : D.I ↦ M.line.group.X) negative ⊗ H.X ⟶ M.group.X).left := by
  obtain ⟨H, j, hclosed, hsmooth, hj, hB⟩ := integralBorelOfRegularCocharacter M y hy
  refine ⟨H, j, hclosed, hsmooth, hj, hB, ?_⟩
  intro negative positive hnegative hpositive
  obtain ⟨f, hf⟩ := markedPositiveProductFactors M y j hj positive
    (fun i hi ↦ le_of_lt ((hpos i).mp ((hpositive.2 i).mp hi)))
  have : IsIso f := markedPositiveProduct_isIso M y hy j hclosed hsmooth hj negative positive
    hnegative hpositive hpos f hf
  let N := product (fun _ : D.I ↦ M.line.group.X) negative
  let m : N ⊗ H.X ⟶ M.group.X :=
    (fst _ _ ≫ rootProduct M.line M.root negative) * (snd _ _ ≫ j.hom.hom)
  let P := (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) positive
  let t := tensorIso (Iso.refl N) (asIso f)
  have he : t.hom ≫ m = cellMap M.line M.torus M.root negative positive := by
    change (𝟙 N ⊗ₘ f) ≫ ((fst N H.X ≫ rootProduct M.line M.root negative) *
      (snd N H.X ≫ j.hom.hom)) =
      (fst N P ≫ rootProduct M.line M.root negative) *
        (snd N P ≫ ((fst _ _ ≫ M.torus.hom.hom) *
          (snd _ _ ≫ rootProduct M.line M.root positive)))
    have ha : (𝟙 N ⊗ₘ f) ≫ fst N H.X = fst N P :=
      (tensorHom_fst (𝟙 N) f).trans (Category.comp_id _)
    have hb : (𝟙 N ⊗ₘ f) ≫ snd N H.X = snd N P ≫ f := tensorHom_snd _ _
    rw [MonObj.comp_mul, reassoc_of% ha, reassoc_of% hb, hf]
  refine ⟨asIso f, hf, ?_⟩
  have ht : IsOpenImmersion (t.hom.left ≫ m.left) := by
    change IsOpenImmersion (t.hom ≫ m).left
    rw [he]
    exact M.openCell negative positive hnegative hpositive
  have : IsIso t.hom.left := (Over.forget Base.{u}).map_isIso t.hom
  exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion t.hom.left m.left).mp ht

set_option backward.isDefEq.respectTransparency false in
/-- The integral big cell is the product of the ordered negative root chart and
the smooth integral Borel. The Borel factor uses the actual subgroup inclusion. -/
theorem integralBorelBigCell (M : Model D) :
    ∃ (H : IntegralGroup.{u}) (j : H ⟶ M.group),
      IsClosedImmersion j.hom.hom.left ∧ Smooth H.X.hom ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ Base.{u}),
        ∃ hc : IsClosedImmersion ((changeBase a).map j).hom.hom.left,
          Specs.GeometricBorelConjugacy.IsBorel (G := (changeBase a).obj M.group)
            ⟨(changeBase a).obj H, (changeBase a).map j, hc⟩) ∧
      ∀ (negative positive : List D.I), Enumerates negative {i | ¬ D.base.IsPos i} →
        Enumerates positive {i | D.base.IsPos i} →
        ∃ e : (splitTorus D).X ⊗ product (fun _ : D.I ↦ M.line.group.X) positive ≅ H.X,
          e.hom ≫ j.hom.hom =
            (fst _ _ ≫ M.torus.hom.hom) * (snd _ _ ≫ rootProduct M.line M.root positive) ∧
          IsOpenImmersion (((fst _ _ ≫ rootProduct M.line M.root negative) *
            (snd _ _ ≫ j.hom.hom)) :
              product (fun _ : D.I ↦ M.line.group.X) negative ⊗ H.X ⟶ M.group.X).left := by
  obtain ⟨y, hy, hpos⟩ := existsRegularPositiveCocharacter D
  obtain ⟨H, j, hj, hs, _, hB, hcell⟩ := integralBorelBigCellOfCocharacter M y hy hpos
  exact ⟨H, j, hj, hs, hB, hcell⟩

end IntegralCell

section IntegralWeyl

open Specs.IntegralRootRelations (upper lower diagonal)
open private elementaryWord rankOneWord_reflection
  from LinearAlgebraicGroups.Classification.IntegralRealization

variable {D : BasedRootDatum.{u}}

/-- The point given by the marked rank-one Weyl word. -/
def integralWeylPoint (M : Model D) (a : D.I) (C : IntegralAlgebra.{u}) :
    IntegralPoints M.group C :=
  (M.rankOne a).app C (elementaryWord (1 : Cˣ))

/-- The reflection acts on the same character lattice as the marked torus. -/
def reflectionOnCharacters (D : BasedRootDatum.{u}) (a : D.I) :
    Multiplicative D.X →* Multiplicative D.X where
  toFun m := Multiplicative.ofAdd (D.datum.reflection a m.toAdd)
  map_one' := by change Multiplicative.ofAdd (D.datum.reflection a 0) = _; rw [map_zero]; rfl
  map_mul' m n := by
    change Multiplicative.ofAdd (D.datum.reflection a (m.toAdd + n.toAdd)) = _
    rw [map_add]
    rfl

set_option maxHeartbeats 450000 in
private theorem torusPoint_inv (C : IntegralAlgebra.{u}) (v : TorusValues D C) :
    torusPoint D C v⁻¹ = (torusPoint D C v)⁻¹ := by
  let f : TorusValues D C →* IntegralPoints (splitTorus D) C :=
    MonoidHom.mk' (torusPoint D C) (torusPoint_mul C)
  exact f.map_inv v

set_option backward.isDefEq.respectTransparency false in
/-- The marked rank-one word normalizes the ordered torus coordinates and
acts on them by the root reflection over every integral test algebra. -/
theorem integralWeylPoint_reflectsTorus (M : Model D) (a : D.I)
    (C : IntegralAlgebra.{u}) (t : TorusValues D C) :
    integralWeylPoint M a C * (torusPoint D C t ≫ M.torus.hom.hom) *
      (integralWeylPoint M a C)⁻¹ =
      torusPoint D C (t.comp (reflectionOnCharacters D a)) ≫ M.torus.hom.hom := by
  let r : Matrix.SpecialLinearGroup (Fin 2) C →* IntegralPoints M.group C :=
    ((M.rankOne a).app C).hom
  let v := torusPoint D C t ≫ M.torus.hom.hom
  let b := t (Multiplicative.ofAdd (D.datum.root a))
  let d := cocharacter D (D.datum.coroot a) C b
  have hUpper (z : C) : v * r (upper z) * v⁻¹ = r (upper ((b : C) * z)) := by
    have hu (w : C) : r (upper w) = M.line.point C w ≫ (M.root a).hom.hom :=
      M.rankOneUpper a C w
    rw [hu, hu]
    exact M.conjugation C t a z
  have hLower (z : C) : v * r (lower z) * v⁻¹ = r (lower ((↑b⁻¹ : C) * z)) := by
    have hl (w : C) : r (lower w) =
        M.line.point C w ≫ (M.root (D.datum.reflectionPerm a a)).hom.hom :=
      M.rankOneLower a C w
    rw [hl, hl]
    have hn : D.datum.root (D.datum.reflectionPerm a a) = -D.datum.root a :=
      (D.datum.root_reflectionPerm a a).trans (D.datum.reflection_apply_self a)
    have hb : t (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm a a))) = b⁻¹ := by
      rw [hn]
      exact t.map_inv _
    simpa only [hb] using M.conjugation C t (D.datum.reflectionPerm a a) z
  have hd : r (diagonal b) = torusPoint D C d ≫ M.torus.hom.hom := M.rankOneDiagonal a C b
  have hComm : Commute v (r (diagonal b)) := by
    rw [hd]
    change (torusPoint D C t ≫ M.torus.hom.hom) * (torusPoint D C d ≫ M.torus.hom.hom) =
      (torusPoint D C d ≫ M.torus.hom.hom) * (torusPoint D C t ≫ M.torus.hom.hom)
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, ← torusPoint_mul, ← torusPoint_mul, mul_comm t d]
  have hvalue : t.comp (reflectionOnCharacters D a) = t * d⁻¹ := by
    apply MonoidHom.ext
    intro m
    change t (Multiplicative.ofAdd (D.datum.reflection a m.toAdd)) =
      t m * (b ^ D.datum.coroot' a m.toAdd)⁻¹
    rw [D.datum.reflection_apply]
    change t (m / (Multiplicative.ofAdd (D.datum.root a)) ^ D.datum.coroot' a m.toAdd) = _
    rw [map_div, map_zpow, div_eq_mul_inv]
  change r (elementaryWord (1 : Cˣ)) * v * (r (elementaryWord (1 : Cˣ)))⁻¹ = _
  rw [rankOneWord_reflection r v b hUpper hLower hComm, hd]
  change (torusPoint D C t ≫ M.torus.hom.hom) *
    (torusPoint D C d ≫ M.torus.hom.hom)⁻¹ = _
  rw [← GrpObj.inv_comp, ← MonObj.mul_comp, ← torusPoint_inv, ← torusPoint_mul, ← hvalue]

/-- Restriction of the marked rank-one word uses the same section. -/
theorem integralWeylPoint_natural (M : Model D) (a : D.I)
    {C E : IntegralAlgebra.{u}} (f : C ⟶ E) :
    integralSpec.map f.op ≫ integralWeylPoint M a C = integralWeylPoint M a E := by
  have h := ConcreteCategory.congr_hom (NatTrans.naturality (M.rankOne a) f) (elementaryWord (1 : Cˣ))
  change (M.rankOne a).app E (Matrix.SpecialLinearGroup.map f.hom.toRingHom
      (elementaryWord (1 : Cˣ))) =
    integralSpec.map f.op ≫ integralWeylPoint M a C at h
  have he : Matrix.SpecialLinearGroup.map f.hom.toRingHom (elementaryWord (1 : Cˣ)) =
      elementaryWord (1 : Eˣ) := by
    have hu : Matrix.SpecialLinearGroup.map f.hom.toRingHom (upper (1 : C)) = upper (1 : E) := by
      apply Subtype.ext
      ext i l
      change f.hom ((upper (1 : C) : Matrix (Fin 2) (Fin 2) C) i l) =
        (upper (1 : E) : Matrix (Fin 2) (Fin 2) E) i l
      fin_cases i <;> fin_cases l <;> simp [upper]
    have hl : Matrix.SpecialLinearGroup.map f.hom.toRingHom (lower (-1 : C)) = lower (-1 : E) := by
      apply Subtype.ext
      ext i l
      change f.hom ((lower (-1 : C) : Matrix (Fin 2) (Fin 2) C) i l) =
        (lower (-1 : E) : Matrix (Fin 2) (Fin 2) E) i l
      fin_cases i <;> fin_cases l <;> simp [lower]
    simp only [elementaryWord, inv_one, Units.val_one, map_mul, hu, hl]
  rw [he] at h
  exact h.symm


end IntegralWeyl

end SplitModel

section GeometricFibres

open private borel_of_same from LinearAlgebraicGroups.RootData.RankOneFlag

variable {S T : Scheme.{u}} {G H : Grp (Over S)}

/-- Each algebraically closed field fibre of the given inclusion is Borel. -/
def HasBorelFibres (i : H ⟶ G) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ S),
    ∃ hc : IsClosedImmersion ((changeBase a).map i).hom.hom.left,
      IsBorel (G := (changeBase a).obj G) ⟨(changeBase a).obj H, (changeBase a).map i, hc⟩

private theorem isBorel_of_isos {k : Type u} [Field k] [IsAlgClosed k] {G : Specs.GroupScheme k}
    {G' : AffineAlgebraicGroup k} {B : ClosedSubgroup G} {C : ClosedSubgroup G'.val}
    (e : G ≅ G'.val) (d : B.group ≅ C.group)
    (h : B.inclusion ≫ e.hom = d.hom ≫ C.inclusion) (hB : IsBorel B) : IsBorel C := by
  apply borel_of_same (H := G') ((isBorel_transport_iff e B).mpr hB)
  refine ⟨⟨d.hom, h.symm⟩, ⟨d.inv, ?_⟩⟩
  change d.inv ≫ B.inclusion ≫ e.hom = C.inclusion
  rw [h, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem hasBorelFibres_changeBase [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] {i : H ⟶ G} (hi : IsClosedImmersion i.hom.hom.left)
    (h : HasBorelFibres i) (a : T ⟶ S) :
    HasBorelFibres ((changeBase a).map i) := by
  intro k _ _ b
  let F := changeBase a
  let J := changeBase b
  have hf : IsClosedImmersion (F.map i).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare a i.hom.hom).flip hi
  have hg : IsClosedImmersion (J.map (F.map i)).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare b (F.map i).hom.hom).flip hf
  obtain ⟨hc, hB⟩ := h k (b ≫ a)
  have : IsAffineHom (F.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom a ‹IsAffineHom G.X.hom›
  have : LocallyOfFinitePresentation (F.obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom a))
  have : QuasiCompact (F.obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom a))
  let A := affineFibre (G := F.obj G) b
  let B : ClosedSubgroup ((changeBase (b ≫ a)).obj G) :=
    ⟨(changeBase (b ≫ a)).obj H, (changeBase (b ≫ a)).map i, hc⟩
  let C : ClosedSubgroup A.val := ⟨J.obj (F.obj H), J.map (F.map i), hg⟩
  let e := changeBaseComp b a
  refine ⟨hg, isBorel_of_isos (B := B) (C := C) (e.app G) (e.app H) ?_ hB⟩
  exact e.hom.naturality i

set_option backward.isDefEq.respectTransparency false in
private theorem hasBorelFibres_comp_iso {G' : Grp (Over S)} (e : G ≅ G')
    {i : H ⟶ G} (h : HasBorelFibres i) : HasBorelFibres (i ≫ e.hom) := by
  intro k _ _ a
  let F := changeBase a
  obtain ⟨hc, hB⟩ := h k a
  let B : ClosedSubgroup (F.obj G) := ⟨F.obj H, F.map i, hc⟩
  let C := transportClosedSubgroup (F.mapIso e) B
  have he : F.map (i ≫ e.hom) = C.inclusion := F.map_comp i e.hom
  have hclosed : IsClosedImmersion (F.map (i ≫ e.hom)).hom.hom.left := by
    rw [he]
    exact C.isClosedImmersion
  refine ⟨hclosed, ?_⟩
  have hC := (isBorel_transport_iff (F.mapIso e) B).mpr hB
  have transport (q : F.obj H ⟶ F.obj G') (hq : q = C.inclusion)
      (hqClosed : IsClosedImmersion q.hom.hom.left) :
      IsBorel (G := F.obj G') ⟨F.obj H, q, hqClosed⟩ := by
    subst q
    exact hC
  exact transport _ he hclosed

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of a Borel family preserves the Borel condition on the actual
geometric fibres of the ambient group. -/
theorem isBorelFamily_pullback [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] {X Y : Over S} (B : Family G X) (h : IsBorelFamily B) (a : Y ⟶ X) :
    IsBorelFamily (B.pullback a) := by
  let F := changeBase X.hom
  have : IsAffineHom (F.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom X.hom ‹IsAffineHom G.X.hom›
  have : LocallyOfFinitePresentation (F.obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom X.hom))
  have : QuasiCompact (F.obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom X.hom))
  have h₀ : HasBorelFibres B.inclusion := h
  have h₁ := hasBorelFibres_changeBase B.closed h₀ a.left
  have h₂ := hasBorelFibres_comp_iso ((changeBaseComp a.left X.hom).symm.app G) h₁
  have h₃ := hasBorelFibres_comp_iso (changeBaseCongr (Over.w a) G) h₂
  change HasBorelFibres (((changeBase a.left).map B.inclusion ≫
    (changeBaseComp a.left X.hom).inv.app G) ≫ (changeBaseCongr (Over.w a) G).hom) at h₃
  change HasBorelFibres ((changeBase a.left).map B.inclusion ≫
    (changeBaseComp a.left X.hom).inv.app G ≫ (changeBaseCongr (Over.w a) G).hom)
  simpa only [Category.assoc] using h₃

end GeometricFibres

section SplittingCoverBorel

open Specs.IntegralSemisimpleModel (Model)

/-- The splitting cover of the given group carries an actual smooth closed
Borel subgroup of the pulled-back group. -/
theorem borelOnSplittingCover {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}
    (hG : HasSplitModel G) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (_ : Module.Finite R A) (_ : Module.FaithfullyFlat R A) (_ : Algebra.Etale R A)
      (H : Grp (Over (ringSpec A))) (i : H ⟶ (changeBase (algebraSpecMap R A)).obj G),
      IsClosedImmersion i.hom.hom.left ∧ Smooth H.X.hom ∧ HasBorelFibres i := by
  obtain ⟨A, _, _, hfinite, hflat, het, D, _, M, ⟨e⟩⟩ := hG
  obtain ⟨B, j, hclosed, hsmooth, hB⟩ := integralBorel M
  let a := integralSpecMap A
  let F := changeBase a
  have : IsAffine M.group.X.left := M.affine
  have : IsAffineHom M.group.X.hom := inferInstance
  have : LocallyOfFinitePresentation M.group.X.hom := M.locallyOfFinitePresentation
  have : QuasiCompact M.group.X.hom := M.quasiCompact
  have hj : IsClosedImmersion (F.map j).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare a j.hom.hom).flip hclosed
  have hsm : Smooth (F.obj B).X.hom := by
    change Smooth (pullback.snd B.X.hom a)
    infer_instance
  let i := F.map j ≫ e.inv
  have he : IsIso e.inv.hom.hom.left :=
    (Grp.forget (Over (ringSpec A)) ⋙ CategoryTheory.Over.forget _).map_isIso e.inv
  refine ⟨A, _, _, hfinite, hflat, het, F.obj B, i, IsClosedImmersion.comp _ _, hsm, ?_⟩
  exact hasBorelFibres_comp_iso e.symm (hasBorelFibres_changeBase hclosed hB a)

end SplittingCoverBorel

section RationalBorelFamilies

open Specs.GeometricBorelConjugacy (IsKBorel ConjugatesSubgroups)
open Specs.GeometricRadicals (baseChangedSubgroup)

open private conjugate conjugate_inclusion conjugation conjugation_apply borel_conjugate
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private conjugates_baseChange from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag

set_option backward.isDefEq.respectTransparency false in
private theorem borel_of_conjugates {k : Type u} [Field k] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} {A B : ClosedSubgroup G.val}
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X) (h : ConjugatesSubgroups g A B)
    (hA : IsBorel A) : IsBorel B := by
  obtain ⟨e, he⟩ := h
  apply isBorel_of_isos (B := conjugate g A) (G' := G) (Iso.refl _) e ?_ (borel_conjugate g hA)
  rw [Iso.refl_hom, Category.comp_id]
  apply Grp.hom_ext
  rw [conjugate_inclusion]
  change A.inclusion.hom.hom ≫ (conjugation g).hom.hom =
    (e.hom ≫ B.inclusion).hom.hom
  rw [conjugation_apply]
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 750000 in
/-- A geometric Borel on the algebraic-closure fibre is Borel after all
algebraically closed scalar extensions if the fibre admits a reference
subgroup whose geometric fibres are Borels. -/
theorem rationalBorelHasBorelFibres {k : Type u} [Field k] {G : Specs.GroupScheme k}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    (A : ClosedSubgroup ((groupBaseChange k (AlgebraicClosure k)).obj G))
    (hA : HasBorelFibres A.inclusion)
    (B : ClosedSubgroup G) (hB : IsKBorel B) :
    HasBorelFibres B.inclusion := by
  let L := AlgebraicClosure k
  let b := fieldSpecMap k L
  let G₁ := affineFibre (G := G) b
  have hA' : IsBorel A := by
    obtain ⟨hc, hb⟩ := hA L (𝟙 (ringSpec L))
    exact isBorel_of_isos (G' := G₁) ((changeBaseId _).app G₁.val)
      ((changeBaseId _).app A.group) ((changeBaseId _).hom.naturality A.inclusion) hb
  obtain ⟨hcB, hB'⟩ := hB
  let B₁ := baseChangedSubgroup L B hcB
  have hsmooth : Smooth G₁.val.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have hconnected : ConnectedSpace G₁.val.X.left := by
    have : GeometricallyConnected G₁.val.X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom b))
    exact GeometricallyConnected.connectedSpace_of_subsingleton G₁.val.X.hom
  obtain ⟨g, hg⟩ := GeometricBorelConjugacy.borelsConjugate G₁ hsmooth hconnected A B₁ hA' hB'
  intro K _ _ a
  obtain ⟨φ, rfl⟩ := Spec.map_surjective a
  let := φ.hom.toAlgebra
  let fieldEmbedding : L →ₐ[k] K := IsAlgClosed.lift
  let := fieldEmbedding.toRingHom.toAlgebra
  let c := fieldSpecMap L K
  have heq : c ≫ b = Spec.map φ := by
    change Spec.map (CommRingCat.ofHom fieldEmbedding.toRingHom) ≫ Spec.map
      (CommRingCat.ofHom (algebraMap k L)) = _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact fieldEmbedding.commutes x
  rw [← heq]
  let G₂ := affineFibre (G := G) (c ≫ b)
  let j := changeBaseComp c b
  have hclosed : IsClosedImmersion ((changeBase (c ≫ b)).map B.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare (c ≫ b) B.inclusion.hom.hom).flip
      B.isClosedImmersion
  have h₂ : IsBorel (extendSubgroup K B₁) := by
    have : IsAffine G₁.val.X.left := G₁.property.1
    have : IsAffineHom G₁.val.X.hom := inferInstance
    have : LocallyOfFinitePresentation G₁.val.X.hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom b))
    have : QuasiCompact G₁.val.X.hom := G₁.property.2.2
    obtain ⟨d, hd⟩ := hA K c
    exact borel_of_conjugates (G := affineFibre (G := G₁.val) c) _
      (conjugates_baseChange K hg) hd
  refine ⟨hclosed, ?_⟩
  exact isBorel_of_isos (G' := G₂) (j.symm.app G) (j.symm.app B.group)
    (j.inv.naturality B.inclusion) h₂

set_option backward.isDefEq.respectTransparency false in
/-- Algebraically closed field-valued points lift through a finite surjective morphism. -/
theorem liftAlgebraicallyClosedPoint {S T : Scheme.{u}} (f : T ⟶ S) [IsFinite f] [Surjective f]
    (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ S) :
    ∃ b : ringSpec k ⟶ T, b ≫ f = a := by
  let X := pullback f a
  let p : X ⟶ ringSpec k := pullback.snd f a
  have : IsFinite p := inferInstanceAs (IsFinite (pullback.snd f a))
  have : Surjective p := inferInstanceAs (Surjective (pullback.snd f a))
  have : IsAffine X := isAffine_of_isAffineHom p
  let e := X.isoSpec
  let A := Γ(X, ⊤)
  let φ : CommRingCat.of k ⟶ A := Spec.preimage (e.inv ≫ p)
  have hφ : Spec.map φ = e.inv ≫ p := Spec.map_preimage _
  have hfinite : φ.hom.Finite := by
    apply (IsFinite.SpecMap_iff φ).mp
    rw [hφ]
    infer_instance
  obtain ⟨x, _⟩ := p.surjective (IsLocalRing.closedPoint k)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨e.hom x⟩
  let := φ.hom.toAlgebra
  have : Module.Finite k A := hfinite
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (α := A)
  let := Ideal.Quotient.field I
  let q := Ideal.Quotient.mkₐ k I
  have : Module.Finite k (A ⧸ I) :=
    Module.Finite.of_surjective q.toLinearMap Ideal.Quotient.mk_surjective
  let h : A ⧸ I →ₐ[k] k := IsAlgClosed.lift
  let g := Spec.map (CommRingCat.ofHom (h.comp q).toRingHom)
  have hgp : g ≫ Spec.map φ = 𝟙 (ringSpec k) := by
    have he : φ ≫ CommRingCat.ofHom (h.comp q).toRingHom = 𝟙 (CommRingCat.of k) := by
      ext r
      exact (h.comp q).commutes r
    change Spec.map (CommRingCat.ofHom (h.comp q).toRingHom) ≫ Spec.map φ = _
    rw [← Spec.map_comp, he]
    exact Scheme.Spec.map_id _
  let b := g ≫ e.inv ≫ pullback.fst f a
  refine ⟨b, ?_⟩
  calc
    b ≫ f = (g ≫ e.inv ≫ p) ≫ a := by
      simp only [b, p, Category.assoc, pullback.condition]
    _ = a := by rw [← hφ, hgp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyConnectedOfFiniteBaseChange {S T : Scheme.{u}}
    (a : T ⟶ S) [IsFinite a] [Surjective a] (X : Over S)
    (h : GeometricallyConnected ((Over.pullback a).obj X).hom) :
    GeometricallyConnected X.hom := by
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro k _ b
  let L := AlgebraicClosure k
  let c := fieldSpecMap k L
  obtain ⟨d, hd⟩ := liftAlgebraicallyClosedPoint a L (c ≫ b)
  let X' := (Over.pullback a).obj X
  let Y := (Over.pullback d).obj X'
  let Z := (Over.pullback c).obj ((Over.pullback b).obj X)
  have : GeometricallyConnected Y.hom := inferInstanceAs (GeometricallyConnected (pullback.snd X'.hom d))
  have hY : ConnectedSpace Y.left := GeometricallyConnected.connectedSpace_of_subsingleton Y.hom
  let e : Y ≅ Z := (Over.pullbackComp d a).symm.app X ≪≫
    eqToIso (congrArg (fun f ↦ (Over.pullback f).obj X) hd) ≪≫
      (Over.pullbackComp c b).app X
  let e' := (Over.forget (ringSpec L)).mapIso e
  have : ConnectedSpace Z.left := e'.hom.homeomorph.connectedSpace_iff.mp hY
  let p : Z.left ⟶ pullback X.hom b := pullback.fst (pullback.snd X.hom b) c
  have : Surjective p := inferInstanceAs (Surjective (pullback.fst (pullback.snd X.hom b) c))
  exact p.surjective.connectedSpace p.continuous

set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyConnectedOfOverIso {S : Scheme.{u}} {X Y : Over S}
    (e : X ≅ Y) (h : GeometricallyConnected Y.hom) : GeometricallyConnected X.hom := by
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro k _ b
  let e' := (Over.pullback b ⋙ Over.forget (ringSpec k)).mapIso e
  have : GeometricallyConnected (pullback.snd Y.hom b) := inferInstance
  exact e'.hom.homeomorph.connectedSpace_iff.mpr
    (GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd Y.hom b))

set_option backward.isDefEq.respectTransparency false in
/-- Connected smoothness of the split integral model descends to the actual group. -/
theorem splitModelGeometry {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}
    (hG : HasSplitModel G) : Smooth G.X.hom ∧ GeometricallyConnected G.X.hom := by
  obtain ⟨A, _, _, hfinite, hflat, het, D, _, M, ⟨e⟩⟩ := hG
  let f := algebraSpecMap R A
  let z := integralSpecMap A
  let v := (changeBase z).obj M.group
  obtain ⟨hf₀, hf₁, hf₂, _⟩ := splittingCover R A
  have : IsFinite f := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R A))).mpr
    (RingHom.finite_algebraMap.mpr hfinite)
  have hs := M.smooth
  have hc := M.connected
  let e₀ : ((changeBase f).obj G).X ≅ v.X := (Grp.forget (Over (ringSpec A))).mapIso e
  have hv : Smooth v.X.hom := inferInstanceAs (Smooth (pullback.snd M.group.X.hom z))
  have hV : GeometricallyConnected v.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd M.group.X.hom z))
  refine ⟨smoothOfSmoothPullback f G.X ?_, geometricallyConnectedOfFiniteBaseChange f G.X
    (geometricallyConnectedOfOverIso e₀ hV)⟩
  change Smooth ((changeBase f).obj G).X.hom
  rw [← Over.w e₀.hom]
  have : IsIso e₀.hom.left := (Over.forget (ringSpec A)).map_isIso e₀.hom
  infer_instance


set_option backward.isDefEq.respectTransparency false in
/-- The specified finite splitting cover provides a reference Borel on every
algebraically closed field fibre, compatible with further scalar extension. -/
theorem borelReferenceOnFibre {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSplitModel G)
    (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ ringSpec R) :
    ∃ B : ClosedSubgroup ((changeBase a).obj G), HasBorelFibres B.inclusion := by
  obtain ⟨A, _, _, hfinite, hflat, het, H, i, hi, _, hB⟩ := borelOnSplittingCover hG
  let f := algebraSpecMap R A
  have : IsFinite f := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R A))).mpr
    (RingHom.finite_algebraMap.mpr hfinite)
  have : Surjective f := (splittingCover R A).1
  obtain ⟨b, hb⟩ := liftAlgebraicallyClosedPoint f k a
  let F := changeBase f
  have : IsAffineHom (F.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom f inferInstance
  have : LocallyOfFinitePresentation (F.obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom f))
  have : QuasiCompact (F.obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom f))
  let e := (changeBaseComp b f).symm.app G ≪≫ changeBaseCongr hb G
  let j := (changeBase b).map i
  have hj : IsClosedImmersion j.hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare b i.hom.hom).flip hi
  let B : ClosedSubgroup ((changeBase b).obj (F.obj G)) := ⟨(changeBase b).obj H, j, hj⟩
  exact ⟨transportClosedSubgroup e B,
    hasBorelFibres_comp_iso e (hasBorelFibres_changeBase hi hB b)⟩

set_option backward.isDefEq.respectTransparency false in
/-- On a field fibre of the model, a rational Borel is a smooth Borel family
over the field, with its original inclusion. -/
theorem fieldBorelFamily {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSplitModel G)
    {k : Type u} [Field k] (a : ringSpec k ⟶ ringSpec R)
    (B : ClosedSubgroup ((changeBase a).obj G)) (hB : IsKBorel B) :
      ∃ C : Family G (Over.mk a), IsBorelFamily C ∧
        ∃ e : C.group ≅ B.group, e.hom ≫ B.inclusion = C.inclusion := by
  let L := AlgebraicClosure k
  let b := fieldSpecMap k L
  let F := changeBase a
  obtain ⟨D, hD⟩ := borelReferenceOnFibre hG L (b ≫ a)
  let e := (changeBaseComp b a).app G
  let A := transportClosedSubgroup e D
  have hA : HasBorelFibres A.inclusion := hasBorelFibres_comp_iso e hD
  have : IsAffineHom (F.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom a inferInstance
  have : LocallyOfFinitePresentation (F.obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom a))
  have : QuasiCompact (F.obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom a))
  obtain ⟨hs, hc⟩ := splitModelGeometry hG
  have : Smooth (F.obj G).X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom a))
  have : GeometricallyConnected (F.obj G).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom a))
  let C : Family G (Over.mk a) :=
    ⟨B.group, B.inclusion, B.isClosedImmersion, fieldBorelSmooth B hB⟩
  exact ⟨C, rationalBorelHasBorelFibres A hA B hB, Iso.refl _, Category.id_comp _⟩

/-- Representability of Borel families supplies the rational field comparison
for a group with the given split model. -/
theorem fieldClassifiesOfRepresents {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSplitModel G) {P : Over (ringSpec R)} (B₀ : Family G P)
    (represents : ∀ (T : Over (ringSpec R)) (C : Family G T), IsBorelFamily C →
      ∃! x : T ⟶ P, SameFamily (B₀.pullback x) C)
    (k : Type u) [Field k] (a : ringSpec k ⟶ ringSpec R)
    (B : ClosedSubgroup ((changeBase a).obj G)) (hB : IsKBorel B) :
    ∃ x : Over.mk a ⟶ P,
      ∃ e : (B₀.pullback x).group ≅ B.group,
        e.hom ≫ B.inclusion = (B₀.pullback x).inclusion := by
  obtain ⟨C, hC, e, he⟩ := fieldBorelFamily hG a B hB
  obtain ⟨x, ⟨f, hf⟩, _⟩ := represents _ C hC
  exact ⟨x, f ≪≫ e, by rw [Iso.trans_hom, Category.assoc, he, hf]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The geometric Borel condition can be checked after a base change that
lifts every algebraically closed field point of the base. -/
theorem hasBorelFibres_of_pointLifts {S T : Scheme.{u}} {G B : Grp (Over S)}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (a : T ⟶ S)
    (hlift : ∀ (k : Type u) [Field k] [IsAlgClosed k] (b : ringSpec k ⟶ S),
      ∃ c : ringSpec k ⟶ T, c ≫ a = b)
    {i : B ⟶ G} (hi : IsClosedImmersion i.hom.hom.left)
    (h : HasBorelFibres ((changeBase a).map i)) : HasBorelFibres i := by
  intro k _ _ b
  obtain ⟨c, rfl⟩ := hlift k b
  obtain ⟨hc, hb⟩ := h k c
  have hclosed : IsClosedImmersion ((changeBase (c ≫ a)).map i).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare (c ≫ a) i.hom.hom).flip hi
  let F := changeBase a
  let J := changeBase c
  let A : ClosedSubgroup (J.obj (F.obj G)) := ⟨J.obj (F.obj B), J.map (F.map i), hc⟩
  let G' := affineFibre (G := G) (c ≫ a)
  let B' : ClosedSubgroup G'.val :=
    ⟨(changeBase (c ≫ a)).obj B, (changeBase (c ≫ a)).map i, hclosed⟩
  let e := (changeBaseComp c a).symm
  exact ⟨hclosed, isBorel_of_isos (B := A) (C := B') (e.app G) (e.app B)
    (e.hom.naturality i) hb⟩

/-- On the given inclusion, the geometric Borel condition can be checked after
a finite surjective base change. -/
theorem hasBorelFibres_of_finiteBaseChange {S T : Scheme.{u}} {G H : Grp (Over S)}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (a : T ⟶ S) [IsFinite a] [Surjective a] {i : H ⟶ G}
    (hi : IsClosedImmersion i.hom.hom.left)
    (h : HasBorelFibres ((changeBase a).map i)) : HasBorelFibres i :=
  hasBorelFibres_of_pointLifts a (fun k _ _ b ↦ liftAlgebraicallyClosedPoint a k b) hi h


end RationalBorelFamilies

section QuotientCharts

variable {S : Scheme.{u}} {G B : Grp (Over S)} (j : B ⟶ G)
variable {I : Type u} {X : I → Over S} (s : ∀ i, X i ⟶ G.X)

/-- A right-product chart multiplies the section by the subgroup on the right. -/
def rightProductChart {Y : Over S} (a : Y ⟶ G.X) : Y ⊗ B.X ⟶ G.X :=
  (fst _ _ ≫ a) * (snd _ _ ≫ j.hom.hom)

private theorem lift_comp_rightProductChart {Y T : Over S} (a : Y ⟶ G.X)
    (x : T ⟶ Y) (b : T ⟶ B.X) :
    lift x b ≫ rightProductChart j a = (x ≫ a) * (b ≫ j.hom.hom) := by
  simp only [rightProductChart, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd]

private abbrev chartOverlap (i l : I) := pullback (s i) (rightProductChart j (s l))

private abbrev overlapLeft (i l : I) : chartOverlap j s i l ⟶ X i :=
  pullback.fst (s i) (rightProductChart j (s l))

private abbrev overlapRight (i l : I) : chartOverlap j s i l ⟶ X l :=
  pullback.snd (s i) (rightProductChart j (s l)) ≫ fst _ _

private abbrev overlapSubgroup (i l : I) : chartOverlap j s i l ⟶ B.X :=
  pullback.snd (s i) (rightProductChart j (s l)) ≫ snd _ _

private theorem overlapRelation (i l : I) :
    overlapLeft j s i l ≫ s i =
      (overlapRight j s i l ≫ s l) * (overlapSubgroup j s i l ≫ j.hom.hom) := by
  rw [show overlapLeft j s i l ≫ s i =
      pullback.snd (s i) (rightProductChart j (s l)) ≫ rightProductChart j (s l)
    from pullback.condition]
  simp only [rightProductChart, MonObj.comp_mul, Category.assoc]
  rfl

private def overlapLift {T : Over S} {i l : I}
    (a : T ⟶ X i) (b : T ⟶ X l) (h : T ⟶ B.X)
    (e : a ≫ s i = (b ≫ s l) * (h ≫ j.hom.hom)) : T ⟶ chartOverlap j s i l :=
  pullback.lift a (lift b h) (e.trans (lift_comp_rightProductChart j (s l) b h).symm)

@[simp, reassoc]
private theorem overlapLift_left {T : Over S} {i l : I}
    (a : T ⟶ X i) (b : T ⟶ X l) (h : T ⟶ B.X)
    (e : a ≫ s i = (b ≫ s l) * (h ≫ j.hom.hom)) :
    overlapLift j s a b h e ≫ overlapLeft j s i l = a :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
private theorem overlapLift_right {T : Over S} {i l : I}
    (a : T ⟶ X i) (b : T ⟶ X l) (h : T ⟶ B.X)
    (e : a ≫ s i = (b ≫ s l) * (h ≫ j.hom.hom)) :
    overlapLift j s a b h e ≫ overlapRight j s i l = b := by
  simp only [overlapLift, ← Category.assoc, pullback.lift_snd, lift_fst]

private theorem overlapFactor {T : Over S} {i l : I}
    (a : T ⟶ chartOverlap j s i l) :
    (a ≫ overlapLeft j s i l) ≫ s i =
      ((a ≫ overlapRight j s i l) ≫ s l) *
        ((a ≫ overlapSubgroup j s i l) ≫ j.hom.hom) := by
  simp only [Category.assoc, overlapRelation j s i l, MonObj.comp_mul]

private def overlapSwitch (i l : I) : chartOverlap j s i l ⟶ chartOverlap j s l i :=
  overlapLift j s (overlapRight j s i l) (overlapLeft j s i l) (overlapSubgroup j s i l)⁻¹
    (by
      let : IsMonHom j.hom.hom := j.hom.isMonHom_hom
      rw [overlapRelation j s i l, GrpObj.inv_comp, mul_inv_cancel_right])

@[simp, reassoc]
private theorem overlapSwitch_left (i l : I) :
    overlapSwitch j s i l ≫ overlapLeft j s l i = overlapRight j s i l :=
  overlapLift_left _ _ _ _ _ _

@[simp, reassoc]
private theorem overlapSwitch_right (i l : I) :
    overlapSwitch j s i l ≫ overlapRight j s l i = overlapLeft j s i l :=
  overlapLift_right _ _ _ _ _ _

private abbrev chartTriple (i l m : I) :=
  pullback (overlapLeft j s i l) (overlapLeft j s i m)

private abbrev tripleLeft (i l m : I) : chartTriple j s i l m ⟶ X i :=
  pullback.fst (overlapLeft j s i l) (overlapLeft j s i m) ≫ overlapLeft j s i l

private abbrev tripleMiddle (i l m : I) : chartTriple j s i l m ⟶ X l :=
  pullback.fst (overlapLeft j s i l) (overlapLeft j s i m) ≫ overlapRight j s i l

private abbrev tripleRight (i l m : I) : chartTriple j s i l m ⟶ X m :=
  pullback.snd (overlapLeft j s i l) (overlapLeft j s i m) ≫ overlapRight j s i m

private def tripleOverlap (i l m : I) : chartTriple j s i l m ⟶ chartOverlap j s l m := by
  let a := pullback.fst (overlapLeft j s i l) (overlapLeft j s i m)
  let b := pullback.snd (overlapLeft j s i l) (overlapLeft j s i m)
  let h := a ≫ overlapSubgroup j s i l
  let k := b ≫ overlapSubgroup j s i m
  refine overlapLift j s (tripleMiddle j s i l m) (tripleRight j s i l m) (k * h⁻¹) ?_
  have e₁ := overlapFactor j s a
  have e₂ := overlapFactor j s b
  have e : (a ≫ overlapLeft j s i l) = b ≫ overlapLeft j s i m := pullback.condition
  rw [e, e₂] at e₁
  let : IsMonHom j.hom.hom := j.hom.isMonHom_hom
  rw [MonObj.mul_comp, GrpObj.inv_comp, ← mul_assoc]
  exact (eq_mul_inv_iff_mul_eq.mpr e₁.symm)

@[simp, reassoc]
private theorem tripleOverlap_left (i l m : I) :
    tripleOverlap j s i l m ≫ overlapLeft j s l m = tripleMiddle j s i l m := by
  simp only [tripleOverlap, overlapLift_left]

@[simp, reassoc]
private theorem tripleOverlap_right (i l m : I) :
    tripleOverlap j s i l m ≫ overlapRight j s l m = tripleRight j s i l m := by
  simp only [tripleOverlap, overlapLift_right]

private def tripleRotate (i l m : I) : chartTriple j s i l m ⟶ chartTriple j s l m i :=
  pullback.lift (tripleOverlap j s i l m) (pullback.fst _ _ ≫ overlapSwitch j s i l)
    (by simp only [tripleOverlap_left, Category.assoc, overlapSwitch_left])

@[simp, reassoc]
private theorem tripleRotate_fst (i l m : I) :
    tripleRotate j s i l m ≫ pullback.fst _ _ = tripleOverlap j s i l m :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
private theorem tripleRotate_snd (i l m : I) :
    tripleRotate j s i l m ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ overlapSwitch j s i l :=
  pullback.lift_snd _ _ _

private theorem tripleRotate_cycle (i l m : I)
    [Mono (overlapLeft j s i l)] [Mono (overlapLeft j s i m)] :
    tripleRotate j s i l m ≫ tripleRotate j s l m i ≫ tripleRotate j s m i l =
      𝟙 (chartTriple j s i l m) := by
  apply (cancel_mono (tripleLeft j s i l m)).mp
  simp only [Category.assoc, tripleRotate_fst_assoc, tripleOverlap_left,
    tripleOverlap_right, tripleRotate_snd_assoc, overlapSwitch_right, Category.id_comp]

variable [∀ i, IsOpenImmersion (rightProductChart j (s i)).left]

private instance overlapLeft_open (i l : I) : IsOpenImmersion (overlapLeft j s i l).left :=
  MorphismProperty.of_isPullback
    (((IsPullback.of_hasPullback (s i) (rightProductChart j (s l))).map (Over.forget S)).flip)
    (inferInstance : IsOpenImmersion (rightProductChart j (s l)).left)

private instance overlapLeft_mono (i l : I) : Mono (overlapLeft j s i l) :=
  Over.mono_of_mono_left _

private def rightProductGlueDataOver : CategoryTheory.GlueData (Over S) where
  J := I
  U := X
  V p := chartOverlap j s p.1 p.2
  f := overlapLeft j s
  f_id i := by
    let a := overlapLeft j s i i
    let b := overlapLift j s (i := i) (l := i) (𝟙 (X i)) (𝟙 (X i)) 1
      (by simp only [Category.id_comp, MonObj.one_comp, mul_one])
    have h : b ≫ a = 𝟙 (X i) := overlapLift_left _ _ _ _ _ _
    refine ⟨⟨b, (cancel_mono a).mp ?_, h⟩⟩
    simp only [Category.assoc, h, Category.comp_id, Category.id_comp]
    rfl
  t := overlapSwitch j s
  t_id i := by
    apply (cancel_mono (overlapLeft j s i i)).mp
    rw [overlapSwitch_left, Category.id_comp]
    let b := overlapLift j s (i := i) (l := i) (𝟙 (X i)) (𝟙 (X i)) 1
      (by simp only [Category.id_comp, MonObj.one_comp, mul_one])
    have e : overlapLeft j s i i ≫ b = 𝟙 _ := by
      apply (cancel_mono (overlapLeft j s i i)).mp
      simp only [b, Category.assoc, overlapLift_left, Category.comp_id, Category.id_comp]
    rw [← Category.id_comp (overlapRight j s i i), ← e, Category.assoc]
    have h : b ≫ overlapRight j s i i = 𝟙 (X i) := overlapLift_right _ _ _ _ _ _
    rw [h, Category.comp_id]
  t' := tripleRotate j s
  t_fac := tripleRotate_snd j s
  cocycle i l m := tripleRotate_cycle j s i l m

private def rightProductGlueData : Scheme.GlueData.{u} where
  toGlueData := (rightProductGlueDataOver j s).mapGlueData (Over.forget S)
  f_open i l := overlapLeft_open j s i l

private def rightProductGluedBase : (rightProductGlueData j s).glued ⟶ S := by
  fapply Multicoequalizer.desc
  · exact fun i ↦ (X i).hom
  · rintro ⟨i, l⟩
    change (overlapLeft j s i l).left ≫ (X i).hom =
      (overlapSwitch j s i l ≫ overlapLeft j s l i).left ≫ (X l).hom
    rw [Over.w (overlapLeft j s i l), Over.w (overlapSwitch j s i l ≫ overlapLeft j s l i)]

private abbrev rightProductGlued : Over S :=
  Over.mk (rightProductGluedBase j s)

private def rightProductGluedChart (i : I) : X i ⟶ rightProductGlued j s :=
  Over.homMk ((rightProductGlueData j s).ι i) (Multicoequalizer.π_desc _ _ _ _ _)

private theorem overlap_gluedChart (i l : I) :
    overlapLeft j s i l ≫ rightProductGluedChart j s i =
      overlapRight j s i l ≫ rightProductGluedChart j s l := by
  apply Over.OverMorphism.ext
  have e := (rightProductGlueData j s).glue_condition i l
  change (overlapSwitch j s i l).left ≫ (overlapLeft j s l i).left ≫
      (rightProductGluedChart j s l).left = _ at e
  rw [← Category.assoc, ← Over.comp_left, overlapSwitch_left] at e
  exact e.symm

private theorem productGluedCharts_agree {T : Over S} {i l : I}
    (a : T ⟶ X i ⊗ B.X) (b : T ⟶ X l ⊗ B.X)
    (e : a ≫ rightProductChart j (s i) = b ≫ rightProductChart j (s l)) :
    a ≫ fst _ _ ≫ rightProductGluedChart j s i =
      b ≫ fst _ _ ≫ rightProductGluedChart j s l := by
  let x := a ≫ fst (X i) B.X
  let y := b ≫ fst (X l) B.X
  let c := a ≫ snd (X i) B.X
  let d := b ≫ snd (X l) B.X
  have eu : (x ≫ s i) * (c ≫ j.hom.hom) = (y ≫ s l) * (d ≫ j.hom.hom) := by
    calc
      _ = lift x c ≫ rightProductChart j (s i) := (lift_comp_rightProductChart ..).symm
      _ = lift y d ≫ rightProductChart j (s l) := by
        rw [show lift x c = a from lift_comp_fst_snd _, show lift y d = b from lift_comp_fst_snd _, e]
      _ = _ := lift_comp_rightProductChart ..
  have ex : x ≫ s i = (y ≫ s l) * ((d * c⁻¹) ≫ j.hom.hom) := by
    let : IsMonHom j.hom.hom := j.hom.isMonHom_hom
    rw [MonObj.mul_comp, GrpObj.inv_comp, ← mul_assoc]
    exact eq_mul_inv_iff_mul_eq.mpr eu
  let t := overlapLift j s x y (d * c⁻¹) ex
  have h := congrArg (t ≫ ·) (overlap_gluedChart j s i l)
  simpa only [Category.assoc, overlapLift_left_assoc, overlapLift_right_assoc, t, x, y] using h

variable (hcover : ∀ x : G.X.left, ∃ (i : I) (y : (X i ⊗ B.X).left),
    (rightProductChart j (s i)).left y = x)

private def rightProductOpenCover : G.X.left.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) I (fun i ↦ (X i ⊗ B.X).left)
    (fun i ↦ (rightProductChart j (s i)).left) hcover

set_option backward.isDefEq.respectTransparency false in
private theorem rightProductProjection_agree (i l : I) :
    pullback.fst ((rightProductOpenCover j s hcover).f i) ((rightProductOpenCover j s hcover).f l) ≫
        (fst (X i) B.X ≫ rightProductGluedChart j s i).left =
      pullback.snd ((rightProductOpenCover j s hcover).f i) ((rightProductOpenCover j s hcover).f l) ≫
        (fst (X l) B.X ≫ rightProductGluedChart j s l).left := by
  let p := (rightProductChart j (s i)).left
  let q := (rightProductChart j (s l)).left
  let a := pullback.fst p q
  let b := pullback.snd p q
  let T : Over S := Over.mk (a ≫ (X i ⊗ B.X).hom)
  let a' : T ⟶ X i ⊗ B.X := Over.homMk a
  have hb : b ≫ (X l ⊗ B.X).hom = T.hom := by
    change b ≫ (X l ⊗ B.X).hom = a ≫ (X i ⊗ B.X).hom
    rw [← Over.w (rightProductChart j (s i)), ← Over.w (rightProductChart j (s l))]
    exact (pullback.condition_assoc (f := p) (g := q) G.X.hom).symm
  let b' : T ⟶ X l ⊗ B.X := Over.homMk b hb
  have h : a' ≫ rightProductChart j (s i) = b' ≫ rightProductChart j (s l) := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  exact congrArg (fun f : T ⟶ rightProductGlued j s ↦ f.left)
    (productGluedCharts_agree j s a' b' h)

private def rightProductProjectionLeft : G.X.left ⟶ (rightProductGlued j s).left :=
  (rightProductOpenCover j s hcover).glueMorphisms
    (fun i ↦ (fst (X i) B.X ≫ rightProductGluedChart j s i).left)
    (rightProductProjection_agree j s hcover)

private theorem rightProductProjectionLeft_chart (i : I) :
    (rightProductChart j (s i)).left ≫ rightProductProjectionLeft j s hcover =
      (fst (X i) B.X ≫ rightProductGluedChart j s i).left :=
  (rightProductOpenCover j s hcover).ι_glueMorphisms _ _ i

set_option backward.isDefEq.respectTransparency false in
private def rightProductProjection : G.X ⟶ rightProductGlued j s := by
  refine Over.homMk (rightProductProjectionLeft j s hcover) ?_
  apply (rightProductOpenCover j s hcover).hom_ext _ _
  intro i
  let k : I := i
  change (rightProductChart j (s k)).left ≫ rightProductProjectionLeft j s hcover ≫
    (rightProductGlued j s).hom = (rightProductChart j (s k)).left ≫ G.X.hom
  rw [← Category.assoc, rightProductProjectionLeft_chart j s hcover k,
    Over.w (fst (X k) B.X ≫ rightProductGluedChart j s k), Over.w (rightProductChart j (s k))]

private theorem rightProductProjection_chart (i : I) :
    rightProductChart j (s i) ≫ rightProductProjection j s hcover =
      fst _ _ ≫ rightProductGluedChart j s i :=
  Over.OverMorphism.ext (rightProductProjectionLeft_chart j s hcover i)

set_option backward.isDefEq.respectTransparency false in
private theorem overlap_of_glued_eq {T : Over S} {i l : I}
    (a : T ⟶ X i) (b : T ⟶ X l)
    (he : a ≫ rightProductGluedChart j s i = b ≫ rightProductGluedChart j s l) :
    ∃ t : T ⟶ chartOverlap j s i l,
      t ≫ overlapLeft j s i l = a ∧ t ≫ overlapRight j s i l = b := by
  let D := rightProductGlueData j s
  have ha : a.left ≫ D.ι i = b.left ≫ D.ι l :=
    congrArg (fun f : T ⟶ rightProductGlued j s ↦ f.left) he
  let w := PullbackCone.IsLimit.lift (D.vPullbackConeIsLimit i l) a.left b.left ha
  have h₁ : w ≫ (overlapLeft j s i l).left = a.left :=
    PullbackCone.IsLimit.lift_fst _ _ _ _
  have h₂ : w ≫ (overlapRight j s i l).left = b.left := by
    have h := PullbackCone.IsLimit.lift_snd (D.vPullbackConeIsLimit i l) a.left b.left ha
    change w ≫ ((overlapSwitch j s i l).left ≫ (overlapLeft j s l i).left) = b.left at h
    rw [← Over.comp_left, overlapSwitch_left] at h
    exact h
  let t : T ⟶ chartOverlap j s i l := Over.homMk w (by
    rw [← Over.w (overlapLeft j s i l), ← Category.assoc, h₁, Over.w a])
  exact ⟨t, Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩

private theorem factors_rightProductChart_of_glued_eq {T : Over S} {i l : I}
    (a : T ⟶ X i ⊗ B.X) (b : T ⟶ X l)
    (e : (a ≫ fst (X i) B.X) ≫ rightProductGluedChart j s i =
      b ≫ rightProductGluedChart j s l) :
    ∃ d : T ⟶ X l ⊗ B.X, d ≫ rightProductChart j (s l) = a ≫ rightProductChart j (s i) := by
  let x := a ≫ fst (X i) B.X
  let c := a ≫ snd (X i) B.X
  obtain ⟨t, h₁, h₂⟩ := overlap_of_glued_eq j s x b e
  let v := t ≫ overlapSubgroup j s i l
  have he := overlapFactor j s t
  rw [h₁, h₂] at he
  let : IsMonHom j.hom.hom := j.hom.isMonHom_hom
  refine ⟨lift b (v * c), ?_⟩
  rw [lift_comp_rightProductChart, MonObj.mul_comp, ← mul_assoc, ← he,
    ← lift_comp_rightProductChart j (s i) x c, show lift x c = a from lift_comp_fst_snd _]

set_option backward.isDefEq.respectTransparency false in
private theorem rightProductProjection_pullback (i : I) :
    IsPullback (rightProductChart j (s i)).left (fst (X i) B.X).left
      (rightProductProjection j s hcover).left (rightProductGluedChart j s i).left := by
  let m := rightProductChart j (s i)
  let p := rightProductProjection j s hcover
  let c := rightProductGluedChart j s i
  let Z := pullback p.left c.left
  let r : Z ⟶ G.X.left := pullback.fst p.left c.left
  let v : Z ⟶ (X i).left := pullback.snd p.left c.left
  have hp : m.left ≫ p.left = (fst (X i) B.X).left ≫ c.left :=
    congrArg (fun f : X i ⊗ B.X ⟶ rightProductGlued j s ↦ f.left)
      (rightProductProjection_chart j s hcover i)
  have : IsOpenImmersion c.left := (rightProductGlueData j s).ι_isOpenImmersion i
  have : IsOpenImmersion r := inferInstanceAs (IsOpenImmersion (pullback.fst p.left c.left))
  have hr : Set.range m.left = Set.range r := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      let f := pullback.lift m.left (fst (X i) B.X).left hp
      exact ⟨f x, congrArg (fun g : (X i ⊗ B.X).left ⟶ G.X.left ↦ g x)
        (pullback.lift_fst m.left (fst (X i) B.X).left hp)⟩
    · rintro _ ⟨z, rfl⟩
      let t := Z.fromSpecResidueField z
      let T : Over S := Over.mk ((t ≫ r) ≫ G.X.hom)
      let g : T ⟶ G.X := Over.homMk (t ≫ r)
      have hv : (t ≫ v) ≫ (X i).hom = T.hom := by
        change (t ≫ v) ≫ (X i).hom = (t ≫ r) ≫ G.X.hom
        rw [← Over.w c, ← Over.w p]
        simp only [Category.assoc, r, v, pullback.condition_assoc]
      let b : T ⟶ X i := Over.homMk (t ≫ v) hv
      obtain ⟨l, y, hy⟩ := hcover (r z)
      let n := rightProductChart j (s l)
      have ht : Set.range g.left ⊆ Set.range n.left := by
        rintro _ ⟨x, rfl⟩
        refine ⟨y, ?_⟩
        change n.left y = (t ≫ r) x
        rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
        exact hy
      let a₀ := IsOpenImmersion.lift n.left g.left ht
      have ha₀ : a₀ ≫ n.left = g.left := IsOpenImmersion.lift_fac _ _ _
      let a : T ⟶ X l ⊗ B.X := Over.homMk a₀ (by rw [← Over.w n, ← Category.assoc, ha₀, Over.w g])
      have ha : a ≫ n = g := Over.OverMorphism.ext ha₀
      have e : (a ≫ fst (X l) B.X) ≫ rightProductGluedChart j s l = b ≫ c := by
        rw [Category.assoc, ← rightProductProjection_chart j s hcover l, ← Category.assoc, ha]
        apply Over.OverMorphism.ext
        change (t ≫ r) ≫ p.left = (t ≫ v) ≫ c.left
        simp only [r, v, Category.assoc, pullback.condition]
      obtain ⟨d, hd⟩ := factors_rightProductChart_of_glued_eq j s a b e
      have hd' : d ≫ m = g := hd.trans ha
      let x := IsLocalRing.closedPoint (Z.residueField z)
      refine ⟨d.left x, ?_⟩
      have h := congrArg (fun f : T ⟶ G.X ↦ f.left x) hd'
      change m.left (d.left x) = (t ≫ r) x at h
      exact h.trans (by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply])
  let d := IsOpenImmersion.isoOfRangeEq m.left r hr
  have hd : d.hom ≫ r = m.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he : d.hom ≫ v = (fst (X i) B.X).left := by
    apply (cancel_mono c.left).mp
    rw [Category.assoc, ← pullback.condition (f := p.left) (g := c.left),
      ← Category.assoc, hd, hp]
  exact IsPullback.of_iso_pullback ⟨hp⟩ d hd he

include hcover in
set_option backward.isDefEq.respectTransparency false in
/-- A covering by open right-product charts gives a smooth parameter scheme
and the projection which is the first factor in every chart. -/
theorem glueRightProductCharts (hB : Smooth B.X.hom) (hX : ∀ i, Smooth (X i).hom) :
    ∃ (P : Over S) (p : G.X ⟶ P) (c : ∀ i, X i ⟶ P),
      Smooth P.hom ∧ Smooth p.left ∧ Surjective p.left ∧
      (∀ i, IsOpenImmersion (c i).left) ∧
      (∀ x : P.left, ∃ i y, (c i).left y = x) ∧
      (∀ i, rightProductChart j (s i) ≫ p = fst _ _ ≫ c i) ∧
      ∀ i, IsPullback (rightProductChart j (s i)).left (fst (X i) B.X).left p.left (c i).left := by
  let D := rightProductGlueData j s
  let P := rightProductGlued j s
  let c := rightProductGluedChart j s
  let p := rightProductProjection j s hcover
  refine ⟨P, p, c, ?_, ?_, ?_, fun i ↦ ?_, ?_, rightProductProjection_chart j s hcover,
    rightProductProjection_pullback j s hcover⟩
  · exact (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) D.openCover).mpr
      (fun i ↦ (Over.w (c i)).symm ▸ hX i)
  · refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth)
      (rightProductOpenCover j s hcover)).mpr fun i ↦ ?_
    change Smooth ((rightProductChart j (s i)).left ≫ p.left)
    rw [← Over.comp_left, rightProductProjection_chart]
    have : Smooth (fst (X i) B.X).left := by
      change Smooth (pullback.fst (X i).hom B.X.hom)
      infer_instance
    have : IsOpenImmersion (c i).left := D.ι_isOpenImmersion i
    change Smooth ((fst (X i) B.X).left ≫ (c i).left)
    infer_instance
  · refine ⟨fun x ↦ ?_⟩
    obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
    let e := lift (𝟙 (X i)) (1 : X i ⟶ B.X)
    refine ⟨(e ≫ rightProductChart j (s i)).left y, ?_⟩
    have he : (e ≫ rightProductChart j (s i)) ≫ p = c i := by
      rw [Category.assoc, rightProductProjection_chart, ← Category.assoc, lift_fst, Category.id_comp]
    exact (congrArg (fun f : X i ⟶ P ↦ f.left y) he).trans hy
  · exact D.ι_isOpenImmersion i
  · exact D.ι_jointly_surjective

end QuotientCharts

section Conjugation

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

private def innerConjugationHom (G : Grp C) (g : 𝟙_ C ⟶ G.X) : G ⟶ G := by
  let a : G.X ⟶ G.X := toUnit _ ≫ g
  refine Grp.homMk'' (a * 𝟙 _ * a⁻¹) ?_ ?_
  · simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, MonObj.one_eq_one]
    simp
  · have step (Z : C) (f : Z ⟶ G.X) : f ≫ a = toUnit Z ≫ g := by
      simp [a]
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id]
    conv_rhs => rw [MonObj.mul_eq_mul]
    simp only [MonObj.comp_mul, tensorHom_fst, tensorHom_snd, GrpObj.comp_inv, Category.comp_id, step]
    rw [MonObj.mul_eq_mul]
    group

private theorem comp_innerConjugation (G : Grp C) (g : 𝟙_ C ⟶ G.X)
    {Z : C} (x : Z ⟶ G.X) :
    x ≫ (innerConjugationHom G g).hom.hom = (toUnit Z ≫ g) * x * (toUnit Z ≫ g)⁻¹ := by
  change x ≫ ((toUnit G.X ≫ g) * 𝟙 G.X * (toUnit G.X ≫ g)⁻¹) = _
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc, Category.comp_id]

private def innerConjugation (G : Grp C) (g : 𝟙_ C ⟶ G.X) : G ≅ G where
  hom := innerConjugationHom G g
  inv := innerConjugationHom G g⁻¹
  hom_inv_id := by
    apply Grp.hom_ext
    change (innerConjugationHom G g).hom.hom ≫ (innerConjugationHom G g⁻¹).hom.hom = 𝟙 _
    rw [comp_innerConjugation, ← Category.id_comp (innerConjugationHom G g).hom.hom,
      comp_innerConjugation, GrpObj.comp_inv]
    group
  inv_hom_id := by
    apply Grp.hom_ext
    change (innerConjugationHom G g⁻¹).hom.hom ≫ (innerConjugationHom G g).hom.hom = 𝟙 _
    rw [comp_innerConjugation, ← Category.id_comp (innerConjugationHom G g⁻¹).hom.hom,
      comp_innerConjugation, GrpObj.comp_inv]
    group

set_option backward.isDefEq.respectTransparency false in
private theorem mapInnerConjugation {D : Type*} [Category* D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (G : Grp C) (g : 𝟙_ C ⟶ G.X) :
    F.mapGrp.map (innerConjugationHom G g) =
      innerConjugationHom (F.mapGrp.obj G) (Functor.LaxMonoidal.ε F ≫ F.map g) := by
  apply Grp.hom_ext
  have lhs := comp_innerConjugation G g (𝟙 G.X)
  rw [Category.id_comp] at lhs
  have rhs := comp_innerConjugation (F.mapGrp.obj G)
    (Functor.LaxMonoidal.ε F ≫ F.map g) (𝟙 (F.mapGrp.obj G).X)
  rw [Category.id_comp] at rhs
  change F.map (innerConjugationHom G g).hom.hom =
    (innerConjugationHom (F.mapGrp.obj G) (Functor.LaxMonoidal.ε F ≫ F.map g)).hom.hom
  rw [lhs, rhs]
  simp only [Functor.map_mul, Functor.map_inv', ← Category.assoc, Functor.map_comp]
  change (F.map (toUnit G.X) ≫ F.map g) * F.map (𝟙 G.X) *
      (F.map (toUnit G.X) ≫ F.map g)⁻¹ =
    ((toUnit (F.obj G.X) ≫ Functor.LaxMonoidal.ε F) ≫ F.map g) * 𝟙 (F.obj G.X) *
      ((toUnit (F.obj G.X) ≫ Functor.LaxMonoidal.ε F) ≫ F.map g)⁻¹
  rw [Functor.Monoidal.toUnit_ε, F.map_id G.X]

end Conjugation

section ConjugateFamily

variable {S : Scheme.{u}} {G B : Grp (Over S)} {T : Over S}

/-- The section of the pulled-back group corresponding to a test point of the
original group. -/
private def sectionOfPoint (g : T ⟶ G.X) : 𝟙_ (Over T.left) ⟶ ((changeBase T.hom).obj G).X :=
  CategoryTheory.Over.homMk (pullback.lift g.left (𝟙 T.left) (by
    change g.left ≫ G.X.hom = (𝟙 T.left) ≫ T.hom
    rw [Category.id_comp, CategoryTheory.Over.w g])) (by
    change pullback.lift _ _ _ ≫ pullback.snd G.X.hom T.hom = 𝟙 _
    simp)

private theorem sectionOfPoint_fst (g : T ⟶ G.X) :
    (sectionOfPoint g).left ≫ pullback.fst G.X.hom T.hom = g.left :=
  pullback.lift_fst _ _ _

/-- The conjugate of a smooth closed subgroup by a point over a test scheme. -/
def conjugateSubgroupFamily (i : B ⟶ G) (hi : IsClosedImmersion i.hom.hom.left)
    (hs : Smooth B.X.hom) (g : T ⟶ G.X) : Family G T where
  group := (changeBase T.hom).obj B
  inclusion := (changeBase T.hom).map i ≫
    (innerConjugation _ (sectionOfPoint g)).hom
  closed := by
    have : IsClosedImmersion (((changeBase T.hom).map i).hom.hom.left) :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (pullbackMapSquare T.hom i.hom.hom).flip hi
    let g' := innerConjugation ((changeBase T.hom).obj G) (sectionOfPoint g)
    have : IsIso g'.hom.hom.hom.left :=
      (Grp.forget (Over T.left) ⋙ CategoryTheory.Over.forget T.left).map_isIso g'.hom
    exact inferInstanceAs (IsClosedImmersion
      (((changeBase T.hom).map i).hom.hom.left ≫ g'.hom.hom.hom.left))
  smooth := by
    change Smooth (pullback.snd B.X.hom T.hom)
    infer_instance

/-- The pullback adjunction on points with their group law. -/
private def unbasePoint {U : Scheme.{u}} (a : U ⟶ S) (V : Over U) (H : Grp (Over S)) :
    (V ⟶ ((changeBase a).obj H).X) ≃* ((CategoryTheory.Over.map a).obj V ⟶ H.X) where
  toEquiv := ((CategoryTheory.Over.mapPullbackAdj a).homEquiv V H.X).symm
  map_mul' := adjunctionPoint_mul (CategoryTheory.Over.mapPullbackAdj a) V H

private theorem unbasePoint_left {U : Scheme.{u}} (a : U ⟶ S) {V : Over U}
    {H : Grp (Over S)} (g : V ⟶ ((changeBase a).obj H).X) :
    (unbasePoint a V H g).left = g.left ≫ pullback.fst H.X.hom a := rfl

private theorem unbasePoint_map {U : Scheme.{u}} (a : U ⟶ S) {V : Over U}
    {H J : Grp (Over S)} (i : H ⟶ J) (g : V ⟶ ((changeBase a).obj H).X) :
    unbasePoint a V J (g ≫ ((changeBase a).map i).hom.hom) =
      unbasePoint a V H g ≫ i.hom.hom :=
  (CategoryTheory.Over.mapPullbackAdj a).homEquiv_naturality_right_symm g i.hom.hom

private theorem unbasePoint_section (g : T ⟶ G.X) (V : Over T.left) :
    unbasePoint T.hom V G (toUnit V ≫ sectionOfPoint g) =
      CategoryTheory.Over.homMk V.hom ≫ g := by
  apply CategoryTheory.Over.OverMorphism.ext
  change ((toUnit V).left ≫ (sectionOfPoint g).left) ≫ pullback.fst G.X.hom T.hom =
    V.hom ≫ g.left
  calc
    _ = (toUnit V).left ≫ ((sectionOfPoint g).left ≫ pullback.fst G.X.hom T.hom) :=
      Category.assoc _ _ _
    _ = (toUnit V).left ≫ g.left := congrArg ((toUnit V).left ≫ ·) (sectionOfPoint_fst g)
    _ = _ := rfl

/-- Conjugation in the ambient product, with the test scheme as the second
factor of the product. -/
private def conjugateOver (i : B ⟶ G) (g : T ⟶ G.X) : B.X ⊗ T ⟶ G.X ⊗ T :=
  lift ((snd _ _ ≫ g) * (fst _ _ ≫ i.hom.hom) * (snd _ _ ≫ g)⁻¹) (snd _ _)

private theorem lift_comp_conjugateOver (i : B ⟶ G) (g : T ⟶ G.X)
    {V : Over S} (b : V ⟶ B.X) (v : V ⟶ T) :
    lift b v ≫ conjugateOver i g =
      lift ((v ≫ g) * (b ≫ i.hom.hom) * (v ≫ g)⁻¹) v := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [conjugateOver, Category.assoc, lift_fst, MonObj.comp_mul,
      GrpObj.comp_inv, lift_snd_assoc, lift_fst_assoc]
  · simp only [conjugateOver, Category.assoc, lift_snd]

set_option backward.isDefEq.respectTransparency false in
private theorem conjugateSubgroupFamily_left (i : B ⟶ G) (hi : IsClosedImmersion i.hom.hom.left)
    (hs : Smooth B.X.hom) (g : T ⟶ G.X) :
    (conjugateSubgroupFamily i hi hs g).inclusion.hom.hom.left =
      (conjugateOver i g).left := by
  let a := T.hom
  let V := ((changeBase a).obj B).X
  let j := ((changeBase a).map i).hom.hom
  let d := (innerConjugation ((changeBase a).obj G) (sectionOfPoint g)).hom.hom.hom
  let f := unbasePoint a V B (𝟙 V)
  let v : (CategoryTheory.Over.map a).obj V ⟶ T := CategoryTheory.Over.homMk V.hom
  let l := lift f v
  have hl : l.left = 𝟙 (B.X ⊗ T).left := by
    apply pullback.hom_ext
    · exact (congrArg CategoryTheory.Over.Hom.left (lift_fst f v)).trans (by
        change (𝟙 (B.X ⊗ T).left ≫ (fst B.X T).left) = _
        rfl)
    · exact (congrArg CategoryTheory.Over.Hom.left (lift_snd f v)).trans (by
        change (𝟙 (B.X ⊗ T).left ≫ (snd B.X T).left) = _
        exact (Category.id_comp _).symm)
  have hj : unbasePoint a V G j = f ≫ i.hom.hom := by
    rw [← unbasePoint_map a i (𝟙 V), Category.id_comp]
  change (j ≫ d).left = (conjugateOver i g).left
  apply pullback.hom_ext
  · change (unbasePoint a V G (j ≫ d)).left =
      (conjugateOver i g).left ≫ (fst G.X T).left
    rw [show j ≫ d = (toUnit V ≫ sectionOfPoint g) * j *
        (toUnit V ≫ sectionOfPoint g)⁻¹ from comp_innerConjugation _ _ j,
      map_mul, map_mul, map_inv, unbasePoint_section, hj]
    change (((v ≫ g) * (f ≫ i.hom.hom) * (v ≫ g)⁻¹)).left =
      (conjugateOver i g).left ≫ (fst G.X T).left
    have hh := congrArg (fun p : (CategoryTheory.Over.map a).obj V ⟶ G.X ⊗ T ↦
      (p ≫ fst G.X T).left) (lift_comp_conjugateOver i g f v)
    simp only [Category.assoc, lift_fst, CategoryTheory.Over.comp_left] at hh
    change l.left ≫ ((conjugateOver i g).left ≫ (fst G.X T).left) = _ at hh
    rw [hl] at hh
    exact hh.symm.trans (Category.id_comp _)
  · change (j ≫ d).left ≫ ((changeBase a).obj G).X.hom =
      (conjugateOver i g).left ≫ (snd G.X T).left
    rw [CategoryTheory.Over.w (j ≫ d), ← CategoryTheory.Over.comp_left, conjugateOver, lift_snd]
    rfl

end ConjugateFamily

section QuotientRelation

variable {S : Scheme.{u}} {G B : Grp (Over S)} (j : B ⟶ G)
variable {I : Type u} {X : I → Over S} (s : ∀ i, X i ⟶ G.X)
variable {P : Over S} (p : G.X ⟶ P) (c : ∀ i, X i ⟶ P)

variable (hcp : ∀ i, IsPullback (rightProductChart j (s i)).left (fst (X i) B.X).left
  p.left (c i).left)

include hcp in
private theorem factorsInRightChart {T : Over S} {i : I}
    (g : T ⟶ G.X) (x : T ⟶ X i) (h : g ≫ p = x ≫ c i) :
    ∃ b : T ⟶ B.X, g = (x ≫ s i) * (b ≫ j.hom.hom) := by
  let a := rightProductChart j (s i)
  have h₀ : g.left ≫ p.left = x.left ≫ (c i).left := congrArg CategoryTheory.Over.Hom.left h
  let d := (hcp i).lift g.left x.left h₀
  have hd : d ≫ a.left = g.left := (hcp i).lift_fst _ _ _
  let d' : T ⟶ X i ⊗ B.X := CategoryTheory.Over.homMk d (by
    rw [← CategoryTheory.Over.w a, ← Category.assoc, hd, CategoryTheory.Over.w g])
  have hfst : d' ≫ fst (X i) B.X = x :=
    CategoryTheory.Over.OverMorphism.ext ((hcp i).lift_snd _ _ _)
  have ha : d' ≫ a = g := CategoryTheory.Over.OverMorphism.ext hd
  refine ⟨d' ≫ snd _ _, ?_⟩
  calc
    g = d' ≫ a := ha.symm
    _ = lift x (d' ≫ snd _ _) ≫ a :=
      congrArg (· ≫ a) (show d' = lift x (d' ≫ snd _ _) from by rw [← hfst, lift_comp_fst_snd])
    _ = _ := lift_comp_rightProductChart _ _ _ _

variable (hopen : ∀ i, IsOpenImmersion (c i).left)
variable (hcover : ∀ x : P.left, ∃ i y, (c i).left y = x)

private def chartsCover : P.left.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) I (fun i ↦ (X i).left)
    (fun i ↦ (c i).left) hcover hopen

include hcp hopen hcover in
set_option backward.isDefEq.respectTransparency false in
/-- Two points of the group have the same quotient point exactly when their
relative right multiplier factors through the subgroup. -/
theorem rightProductQuotient_eq_iff {T : Over S} (g h : T ⟶ G.X)
    (hj : IsClosedImmersion j.hom.hom.left) :
    g ≫ p = h ≫ p ↔ ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h := by
  let U := chartsCover c hopen hcover
  let V : T.left.OpenCover := U.pullback₁ (g ≫ p).left
  let W (i : V.I₀) : Over S := CategoryTheory.Over.mk (V.f i ≫ T.hom)
  let f (i : V.I₀) : W i ⟶ T := CategoryTheory.Over.homMk (V.f i)
  let x (i : V.I₀) : W i ⟶ X i := CategoryTheory.Over.homMk (U.pullbackHom (g ≫ p).left i) (by
    have he := U.pullbackHom_map (g ≫ p).left i
    change U.pullbackHom (g ≫ p).left i ≫ (c i).left = V.f i ≫ (g ≫ p).left at he
    rw [← CategoryTheory.Over.w (c i), ← Category.assoc, he, Category.assoc, CategoryTheory.Over.w (g ≫ p)]
    rfl)
  have hx (i : V.I₀) : (f i ≫ g) ≫ p = x i ≫ c i :=
    CategoryTheory.Over.OverMorphism.ext (U.pullbackHom_map (g ≫ p).left i).symm
  have hfactors (i : V.I₀) : ∃ b : W i ⟶ B.X,
      f i ≫ g = (x i ≫ s i) * (b ≫ j.hom.hom) :=
    factorsInRightChart j s p c hcp (f i ≫ g) (x i) (hx i)
  have hgm (f₀ : T ⟶ G.X) (b : T ⟶ B.X) (he : g * (b ≫ j.hom.hom) = f₀) :
      g ≫ p = f₀ ≫ p := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply V.hom_ext
    intro i
    obtain ⟨b₀, hb₀⟩ := hfactors i
    let b₁ := b₀ * (f i ≫ b)
    have hh : f i ≫ f₀ = (x i ≫ s i) * (b₁ ≫ j.hom.hom) := by
      rw [← he, MonObj.comp_mul, hb₀]
      let : IsMonHom j.hom.hom := j.hom.isMonHom_hom
      rw [← Category.assoc, mul_assoc, ← MonObj.mul_comp]
    have hc : rightProductChart j (s i) ≫ p = fst (X i) B.X ≫ c i :=
      CategoryTheory.Over.OverMorphism.ext (hcp i).w
    have heq : (f i ≫ f₀) ≫ p = x i ≫ c i := by
      rw [hh, ← lift_comp_rightProductChart, Category.assoc, hc, lift_fst_assoc]
    exact congrArg CategoryTheory.Over.Hom.left ((hx i).trans heq.symm)
  constructor
  · intro he
    have hhfactors (i : V.I₀) : ∃ b : W i ⟶ B.X,
        f i ≫ h = (x i ≫ s i) * (b ≫ j.hom.hom) := by
      apply factorsInRightChart j s p c hcp (f i ≫ h) (x i)
      rw [Category.assoc, ← he, ← Category.assoc, hx i]
    choose b₀ hb₀ using hfactors
    choose b₁ hb₁ using hhfactors
    let bLocal (i : V.I₀) : W i ⟶ B.X := (b₀ i)⁻¹ * b₁ i
    let d := g⁻¹ * h
    have hbLocal (i : V.I₀) : bLocal i ≫ j.hom.hom = f i ≫ d := by
      let : IsMonHom j.hom.hom := j.hom.isMonHom_hom
      dsimp only [bLocal, d]
      rw [MonObj.mul_comp, GrpObj.inv_comp, MonObj.comp_mul, GrpObj.comp_inv, hb₀ i, hb₁ i]
      group
    let bLeft := V.glueMorphisms (fun i ↦ (bLocal i).left) (fun i l ↦ by
      have : Mono j.hom.hom.left := inferInstance
      apply (cancel_mono j.hom.hom.left).mp
      have e (a : V.I₀) : (bLocal a).left ≫ j.hom.hom.left = V.f a ≫ d.left :=
        congrArg CategoryTheory.Over.Hom.left (hbLocal a)
      rw [Category.assoc, Category.assoc, e, e, ← Category.assoc, ← Category.assoc,
        pullback.condition])
    have hbLeft : bLeft ≫ j.hom.hom.left = d.left := by
      apply V.hom_ext
      intro i
      rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
      exact congrArg CategoryTheory.Over.Hom.left (hbLocal i)
    let b : T ⟶ B.X := CategoryTheory.Over.homMk bLeft (by
      rw [← CategoryTheory.Over.w j.hom.hom, ← Category.assoc, hbLeft, CategoryTheory.Over.w d])
    have hb : b ≫ j.hom.hom = d := CategoryTheory.Over.OverMorphism.ext hbLeft
    refine ⟨b, ?_⟩
    rw [hb, show d = g⁻¹ * h from rfl, mul_inv_cancel_left]
  · rintro ⟨b, hb⟩
    exact hgm h b hb

end QuotientRelation

section SchemeImage

variable {W X Y : Scheme.{u}}

private theorem idealComapMapOfClosedImmersion (i : Y ⟶ X) [IsClosedImmersion i]
    (J : Y.IdealSheafData) : (J.map i).comap i = J := by
  let f := J.subschemeι ≫ i
  have hfi : IsClosedImmersion f := IsClosedImmersion.comp _ _
  have hf : IsIso f.toImage := inferInstance
  have pb : IsPullback J.subschemeι f.toImage i f.imageι :=
    IsPullback.of_vert_isIso_mono ⟨f.toImage_imageι.symm⟩
  have he := pb.isoPullback_hom_fst
  change (pullback.fst i f.imageι).ker = J
  rw [← Scheme.Hom.ker_comp_of_isIso pb.isoPullback.hom, he,
    Scheme.IdealSheafData.ker_subschemeι]

private theorem toImage_schematicallyDominant (f : X ⟶ Y) :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  have hk : f.toImage.ker.map f.imageι = f.ker := by
    rw [Scheme.IdealSheafData.map_ker, Scheme.Hom.toImage_imageι]
  have h := congrArg (fun J ↦ J.comap f.imageι) hk
  rw [idealComapMapOfClosedImmersion] at h
  exact h.trans (by
    rw [show f.ker = f.imageι.ker from (Scheme.IdealSheafData.ker_subschemeι _).symm,
      ← Scheme.IdealSheafData.map_bot, idealComapMapOfClosedImmersion])

/-- The kernel ideal sheaf of a quasi-compact morphism pulls back along a
flat map to the kernel of its scalar extension. -/
theorem kernelOfFlatPullback (f : X ⟶ Y) [QuasiCompact f] (g : W ⟶ Y) [Flat g] :
    (pullback.snd f g).ker = f.ker.comap g := by
  let Z := pullback g f.imageι
  let d : pullback f g ⟶ Z :=
    pullback.lift (pullback.snd f g) (pullback.fst f g ≫ f.toImage) (by
      rw [Category.assoc, Scheme.Hom.toImage_imageι, pullback.condition])
  have hd : IsPullback (pullback.fst f g) d f.toImage (pullback.snd g f.imageι) := by
    have outer : IsPullback (pullback.fst f g) (d ≫ pullback.fst g f.imageι)
        (f.toImage ≫ f.imageι) g := by
      simpa only [Scheme.Hom.toImage_imageι, d, pullback.lift_fst] using
        IsPullback.of_hasPullback f g
    exact outer.of_bot (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback g f.imageι).flip
  have hg' : Flat (pullback.snd g f.imageι) := inferInstance
  have hf : IsSchemeTheoreticallyDominant f.toImage := toImage_schematicallyDominant f
  have hdDom : IsSchemeTheoreticallyDominant d := IsSchemeTheoreticallyDominant.of_isPullback hd
  have hcomp : d ≫ pullback.fst g f.imageι = pullback.snd f g := pullback.lift_fst _ _ _
  rw [← hcomp, Scheme.Hom.ker_comp, hdDom.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  rfl

end SchemeImage

private theorem productPullback {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    (X : C) {A B : C} (v : A ⟶ B) :
    IsPullback (X ◁ v) (snd X A) (snd X B) v := by
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

section ConjugateImage

variable {S : Scheme.{u}} {G B : Grp (Over S)} (j : B ⟶ G)
variable {P : Over S} (p : G.X ⟶ P)

/-- The map taking a group point and a subgroup point to the conjugated
point over the corresponding right coset. -/
private def conjugationAlongQuotient : B.X ⊗ G.X ⟶ G.X ⊗ P :=
  conjugateOver j (𝟙 G.X) ≫ (G.X ◁ p)

private theorem conjugationAlongQuotient_fst :
    conjugationAlongQuotient j p ≫ fst G.X P =
      (snd B.X G.X) * (fst B.X G.X ≫ j.hom.hom) * (snd B.X G.X)⁻¹ := by
  simp [conjugationAlongQuotient, conjugateOver]

private theorem conjugationAlongQuotient_snd :
    conjugationAlongQuotient j p ≫ snd G.X P = snd B.X G.X ≫ p := by
  simp [conjugationAlongQuotient, conjugateOver]

variable (hcosets : ∀ {T : Over S} (g h : T ⟶ G.X), g ≫ p = h ≫ p →
  ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h)

include hcosets in
set_option backward.isDefEq.respectTransparency false in
private theorem conjugateImagePullbackFactors :
    ∃ d : pullback (conjugationAlongQuotient j p) (G.X ◁ p) ⟶ B.X ⊗ G.X,
      d ≫ conjugateOver j (𝟙 G.X) = pullback.snd _ _ := by
  let q := conjugationAlongQuotient j p
  let a := G.X ◁ p
  let L := pullback q a
  let l : L ⟶ B.X ⊗ G.X := pullback.fst _ _
  let r : L ⟶ G.X ⊗ G.X := pullback.snd _ _
  let u := l ≫ snd B.X G.X
  let v := r ≫ snd G.X G.X
  have hlr : l ≫ q = r ≫ a := pullback.condition
  have hbase : v ≫ p = u ≫ p := by
    have h := congrArg (· ≫ snd G.X P) hlr
    simpa only [a, Category.assoc, conjugationAlongQuotient_snd, whiskerLeft_snd, u, v, q]
      using h.symm
  obtain ⟨b, hb⟩ := hcosets v u hbase
  let b₀ := l ≫ fst B.X G.X
  let b' := b * b₀ * b⁻¹
  refine ⟨lift b' v, ?_⟩
  have hfst := congrArg (· ≫ fst G.X P) hlr
  have hfst' : u * (b₀ ≫ j.hom.hom) * u⁻¹ = r ≫ fst G.X G.X := by
    simpa only [a, Category.assoc, conjugationAlongQuotient_fst, whiskerLeft_fst,
      MonObj.comp_mul, GrpObj.comp_inv, u, b₀, q] using hfst
  rw [lift_comp_conjugateOver]
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.comp_id]
    change v * (b' ≫ j.hom.hom) * v⁻¹ = r ≫ fst G.X G.X
    rw [← hfst', ← hb]
    let : IsMonHom j.hom.hom := j.hom.isMonHom_hom
    simp only [b', MonObj.mul_comp, GrpObj.inv_comp, mul_inv_rev]
    group
  · exact lift_snd _ _

include hcosets in
set_option backward.isDefEq.respectTransparency false in
private theorem conjugationImage_kernel [Flat p.left] [QuasiCompact p.left]
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) :
    (conjugationAlongQuotient j p).left.ker.comap (G.X ◁ p).left =
      (conjugateOver j (𝟙 G.X)).left.ker := by
  let f := conjugateOver j (𝟙 G.X)
  let a := G.X ◁ p
  let q := conjugationAlongQuotient j p
  let r := pullback.snd q a
  have ha := (productPullback G.X p).map (CategoryTheory.Over.forget S)
  have haFlat : Flat a.left :=
    MorphismProperty.of_isPullback (P := @Flat) ha.flip (inferInstance : Flat p.left)
  have haQC : QuasiCompact a.left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) ha.flip (inferInstance : QuasiCompact p.left)
  have hf : IsClosedImmersion f.left := by
    rw [← conjugateSubgroupFamily_left j hj hs (𝟙 G.X)]
    exact (conjugateSubgroupFamily j hj hs (𝟙 G.X)).closed
  have hq : QuasiCompact q.left := by
    change QuasiCompact (f.left ≫ a.left)
    infer_instance
  have hr := (IsPullback.of_hasPullback q a).map (CategoryTheory.Over.forget S)
  change IsPullback (pullback.fst q a).left r.left q.left a.left at hr
  have he : r.left.ker = q.left.ker.comap a.left := by
    rw [← hr.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]
    exact kernelOfFlatPullback q.left a.left
  rw [← he]
  have hfq : f ≫ a = q := rfl
  let k := pullback.lift (𝟙 (B.X ⊗ G.X)) f (by rw [Category.id_comp, hfq])
  have hk : k ≫ r = f := pullback.lift_snd _ _ _
  obtain ⟨d, hd⟩ := conjugateImagePullbackFactors j p hcosets
  change d ≫ f = r at hd
  apply le_antisymm
  · have h := Scheme.Hom.le_ker_comp k.left r.left
    rwa [← CategoryTheory.Over.comp_left, hk] at h
  · have h := Scheme.Hom.le_ker_comp d.left f.left
    rwa [← CategoryTheory.Over.comp_left, hd] at h

include hcosets in
set_option backward.isDefEq.respectTransparency false in
/-- The universal conjugate on the group descends as a closed subscheme of the
ambient group over the right quotient. Its pullback along the projection is
the original conjugate subgroup, scheme-theoretically. -/
theorem conjugationImage_pullback [Flat p.left] [QuasiCompact p.left]
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) :
    let q := conjugationAlongQuotient j p
    IsPullback (conjugateOver j (𝟙 G.X)).left q.left.toImage (G.X ◁ p).left q.left.imageι := by
  dsimp only
  have hf : IsClosedImmersion (conjugateOver j (𝟙 G.X)).left := by
    rw [← conjugateSubgroupFamily_left j hj hs (𝟙 G.X)]
    exact (conjugateSubgroupFamily j hj hs (𝟙 G.X)).closed
  apply isPullback_of_isClosedImmersion
  · exact ((conjugationAlongQuotient j p).left.toImage_imageι).symm
  · rw [Scheme.IdealSheafData.ker_subschemeι]
    exact conjugationImage_kernel j p hcosets hj hs

end ConjugateImage

section Descent

variable {S T : Scheme.{u}}

/-- A descended closed subscheme whose pullback is a smooth subgroup carries
the unique group structure compatible with its inclusion. -/
private theorem descendSubgroupFromIso (a : T ⟶ S)
    [Surjective a] [Flat a] [QuasiCompact a]
    {G : Grp (Over S)} {Z : Over S} (i : Z ⟶ G.X) [IsClosedImmersion i.left]
    {H : Grp (Over T)} (j : H ⟶ (changeBase a).obj G) (hs : Smooth H.X.hom)
    (e : H.X ≅ (CategoryTheory.Over.pullback a).obj Z)
    (he : e.hom ≫ (CategoryTheory.Over.pullback a).map i = j.hom.hom) :
    ∃ (Q : Grp (Over S)) (q : Q ⟶ G) (e₀ : Q.X ≅ Z),
      q.hom.hom = e₀.hom ≫ i ∧ Smooth Q.X.hom ∧ IsClosedImmersion q.hom.hom.left ∧
        ∃ d : (changeBase a).obj Q ≅ H, d.hom ≫ j = (changeBase a).map q := by
  let F := CategoryTheory.Over.pullback a
  let : GrpObj (F.obj Z) := GrpObj.ofIso e
  have hhom : IsMonHom e.hom := isMonHom_ofIso e
  let u : H ≅ Grp.mk (F.obj Z) :=
    Grp.mkIso e (IsMonHom.one_hom e.hom) (IsMonHom.mul_hom e.hom)
  have hi : F.map i = e.inv ≫ j.hom.hom := by
    have he' : e.hom ≫ F.map i = j.hom.hom := he
    exact (e.inv_hom_id_assoc (F.map i)).symm.trans (congrArg (e.inv ≫ ·) he')
  have : IsMonHom (F.map i) := by
    rw [hi]
    exact inferInstanceAs (IsMonHom (u.inv.hom.hom ≫ j.hom.hom))
  have hsm : Smooth (F.obj Z).hom := by
    have : IsIso e.inv.left := (CategoryTheory.Over.forget _).map_isIso e.inv
    rw [← CategoryTheory.Over.w e.inv]
    exact inferInstanceAs (Smooth (e.inv.left ≫ H.X.hom))
  obtain ⟨Q, q, e₀, hq, hqs, hqc, w, hw⟩ := smoothClosedSubgroupOfBaseChange a i hsm
  refine ⟨Q, q, e₀, hq, hqs, hqc, w ≪≫ u.symm, ?_⟩
  apply Grp.hom_ext
  rw [show ((w ≪≫ u.symm).hom ≫ j).hom.hom =
    w.hom.hom.hom ≫ e.inv ≫ j.hom.hom from Category.assoc _ _ _, ← hi]
  exact congrArg (fun f ↦ f.hom.hom) hw

end Descent

section CompareAmbient

variable {S T U : Scheme.{u}}

/-- The first projection of the comparison between iterated and direct
pullbacks is the original first projection after composition. -/
private theorem pullbackComp_first (a : U ⟶ T) (b : T ⟶ S) (X : Over S) :
    ((CategoryTheory.Over.pullbackComp a b).hom.app X).left ≫ pullback.fst ((CategoryTheory.Over.pullback b).obj X).hom a ≫
      pullback.fst X.hom b = pullback.fst X.hom (a ≫ b) := by
  let A := CategoryTheory.Over.mapPullbackAdj a
  let B := CategoryTheory.Over.mapPullbackAdj b
  let C := CategoryTheory.Over.mapPullbackAdj (a ≫ b)
  let α := (CategoryTheory.Over.mapComp a b).inv
  have h := conjugateEquiv_counit C (A.comp B) α X
  exact congrArg CategoryTheory.Over.Hom.left h |>.trans (Category.id_comp _)

variable {P Y : Over S} (p : Y ⟶ P) (G : Grp (Over S))

private def compareAmbient :
    (changeBase Y.hom).obj G ≅ (changeBase p.left).obj ((changeBase P.hom).obj G) :=
  (changeBaseCongr (CategoryTheory.Over.w p) G).symm ≪≫ (changeBaseComp p.left P.hom).app G

set_option backward.isDefEq.respectTransparency false in
private theorem compareAmbient_first :
    (compareAmbient p G).hom.hom.hom.left ≫
      pullback.fst ((changeBase P.hom).obj G).X.hom p.left = (G.X ◁ p).left := by
  have helper (a : Y.left ⟶ P.left) (c : Y.left ⟶ S) (h : a ≫ P.hom = c) :
      (changeBaseCongr h G).inv.hom.hom.left ≫ pullback.fst G.X.hom (a ≫ P.hom) =
        pullback.fst G.X.hom c := by
    cases h
    exact Category.id_comp _
  let A := (changeBase Y.hom).obj G
  let A' := (changeBase P.hom).obj G
  let a := p.left
  let e := compareAmbient p G
  have hcomp : e.hom.hom.hom =
      (changeBaseCongr (CategoryTheory.Over.w p) G).inv.hom.hom ≫
        (CategoryTheory.Over.pullbackComp p.left P.hom).hom.app G.X ≫ 𝟙 _ := rfl
  apply pullback.hom_ext
  · change (e.hom.hom.hom.left ≫ pullback.fst A'.X.hom a) ≫ (fst G.X P).left =
      (G.X ◁ p).left ≫ (fst G.X P).left
    rw [Category.assoc, hcomp, Category.comp_id, CategoryTheory.Over.comp_left, Category.assoc]
    have hc : ((CategoryTheory.Over.pullbackComp a P.hom).hom.app G.X).left ≫
        pullback.fst A'.X.hom a ≫ (fst G.X P).left = pullback.fst G.X.hom (a ≫ P.hom) :=
      pullbackComp_first a P.hom G.X
    refine (congrArg ((changeBaseCongr (CategoryTheory.Over.w p) G).inv.hom.hom.left ≫ ·) hc).trans ?_
    rw [helper p.left Y.hom (CategoryTheory.Over.w p), ← CategoryTheory.Over.comp_left, whiskerLeft_fst]
    rfl
  · change (e.hom.hom.hom.left ≫ pullback.fst A'.X.hom a) ≫ A'.X.hom =
      (G.X ◁ p).left ≫ (snd G.X P).left
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← CategoryTheory.Over.comp_left, whiskerLeft_snd]
    have h := CategoryTheory.Over.w e.hom.hom.hom
    change e.hom.hom.hom.left ≫ pullback.snd A'.X.hom a = (snd G.X Y).left at h
    rw [h]
    rfl

end CompareAmbient

section UniversalFamily

variable {S : Scheme.{u}} {G B : Grp (Over S)} (j : B ⟶ G)
variable {P : Over S} (p : G.X ⟶ P)
variable (hcosets : ∀ {T : Over S} (g h : T ⟶ G.X), g ≫ p = h ≫ p →
  ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h)

include hcosets in
set_option backward.isDefEq.respectTransparency false in
/-- The conjugate of the subgroup by the tautological point on the group
descends to a smooth closed subgroup over the right quotient. -/
theorem universalFamilyOfRightQuotient [Surjective p.left] [Flat p.left] [QuasiCompact p.left]
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) :
    ∃ U : Family G P,
      SameFamily (U.pullback p) (conjugateSubgroupFamily j hj hs (𝟙 G.X)) := by
  let q := conjugationAlongQuotient j p
  let i := q.left.imageι
  let A := (changeBase P.hom).obj G
  let Z := CategoryTheory.Over.mk (i ≫ (snd G.X P).left)
  let l : Z ⟶ A.X := CategoryTheory.Over.homMk i
  have hl : IsClosedImmersion l.left := inferInstanceAs (IsClosedImmersion i)
  let U := conjugateSubgroupFamily j hj hs (𝟙 G.X)
  have hU : U.inclusion.hom.hom.left = (conjugateOver j (𝟙 G.X)).left :=
    conjugateSubgroupFamily_left j hj hs _
  have hp := conjugationImage_pullback j p hcosets hj hs
  change IsPullback _ q.left.toImage (G.X ◁ p).left i at hp
  rw [← hU] at hp
  have pb := hp.flip.paste_vert ((productPullback G.X p).map (CategoryTheory.Over.forget S))
  have hS : IsPullback q.left.toImage U.group.X.hom Z.hom p.left := by
    change IsPullback q.left.toImage (U.inclusion.hom.hom.left ≫ (snd G.X G.X).left)
      Z.hom p.left at pb
    have hu : U.inclusion.hom.hom.left ≫ (snd G.X G.X).left = U.group.X.hom :=
      CategoryTheory.Over.w U.inclusion.hom.hom
    exact hu ▸ pb
  let e : U.group.X ≅ (CategoryTheory.Over.pullback p.left).obj Z :=
    CategoryTheory.Over.isoMk hS.isoPullback hS.isoPullback_hom_snd
  let d := compareAmbient p G
  let m := U.inclusion ≫ d.hom
  have he : e.hom ≫ (CategoryTheory.Over.pullback p.left).map l = m.hom.hom := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (e.hom.left ≫ ((CategoryTheory.Over.pullback p.left).map l).left) ≫ pullback.fst A.X.hom p.left =
        (U.inclusion.hom.hom.left ≫ d.hom.hom.hom.left) ≫ pullback.fst A.X.hom p.left
      rw [Category.assoc, Category.assoc, compareAmbient_first, (pullbackMapSquare p.left l).w,
        ← Category.assoc, show e.hom.left ≫ pullback.fst Z.hom p.left = q.left.toImage
          from hS.isoPullback_hom_fst]
      exact hp.w.symm
    · exact (CategoryTheory.Over.w (e.hom ≫ (CategoryTheory.Over.pullback p.left).map l)).trans
        (CategoryTheory.Over.w m.hom.hom).symm
  obtain ⟨H, k, _, _, hks, hkc, v, hv⟩ :=
    descendSubgroupFromIso p.left l m U.smooth e he
  let Q : Family G P := ⟨H, k, hkc, hks⟩
  refine ⟨Q, v, ?_⟩
  change v.hom ≫ U.inclusion = (changeBase p.left).map k ≫
    (changeBaseComp p.left P.hom).inv.app G ≫ (changeBaseCongr (CategoryTheory.Over.w p) G).hom
  rw [← hv]
  change _ = (v.hom ≫ U.inclusion ≫ d.hom) ≫ d.inv
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end UniversalFamily

section IntegralWeylSections

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open private torusPoint_surjective
  from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

private abbrev integersAlgebra : IntegralAlgebra.{u} :=
  CommAlgCat.of Integers.{u} Integers.{u}

private def integralSpecUnit : 𝟙_ (Over Base.{u}) ≅ integralSpec.obj (op integersAlgebra) :=
  CategoryTheory.Over.isoMk (Iso.refl _) (by
    change (𝟙 Base.{u}) ≫ Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} Integers.{u})) =
      𝟙 Base.{u}
    rw [Category.id_comp]
    exact Scheme.Spec.map_id _)

/-- The rank-one word evaluated as a section over the integers. -/
def integralWeylSection {D : BasedRootDatum.{u}} (M : Model D) (i : D.I) :
    𝟙_ (Over Base.{u}) ⟶ M.group.X :=
  integralSpecUnit.hom ≫ integralWeylPoint M i integersAlgebra

private theorem integralWeylSection_eval {D : BasedRootDatum.{u}} (M : Model D) (i : D.I)
    (C : IntegralAlgebra.{u}) :
    toUnit (integralSpec.obj (op C)) ≫ integralWeylSection M i = integralWeylPoint M i C := by
  let f : integersAlgebra ⟶ C := CommAlgCat.ofHom (Algebra.ofId Integers.{u} C)
  have he : toUnit (integralSpec.obj (op C)) ≫ integralSpecUnit.hom = integralSpec.map f.op := by
    apply (cancel_mono integralSpecUnit.inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact Subsingleton.elim _ _
  rw [integralWeylSection, ← Category.assoc, he, integralWeylPoint_natural]

private def torusReflection (D : BasedRootDatum.{u}) (i : D.I) : splitTorus D ⟶ splitTorus D :=
  (hopfSpec (CommRingCat.of Integers.{u})).map
    (CommHopfAlgCat.ofHom
      (MonoidAlgebra.mapDomainBialgHom Integers.{u} (reflectionOnCharacters D i))).op

private theorem reflectionOnCharacters_comp (D : BasedRootDatum.{u}) (i : D.I) :
    (reflectionOnCharacters D i).comp (reflectionOnCharacters D i) =
      MonoidHom.id (Multiplicative D.X) := by
  apply MonoidHom.ext
  intro x
  change Multiplicative.ofAdd (D.datum.reflection i (D.datum.reflection i x.toAdd)) = x
  rw [D.datum.reflection_same i]
  rfl

private theorem torusReflection_comp (D : BasedRootDatum.{u}) (i : D.I) :
    torusReflection D i ≫ torusReflection D i = 𝟙 _ := by
  let P := CommHopfAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative D.X))
  let f : P ⟶ P := CommHopfAlgCat.ofHom
    (MonoidAlgebra.mapDomainBialgHom Integers.{u} (reflectionOnCharacters D i))
  have h : f.op ≫ f.op = 𝟙 (op P) := by
    apply Quiver.Hom.unop_inj
    apply CommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom Integers.{u} (reflectionOnCharacters D i)).comp
      (MonoidAlgebra.mapDomainBialgHom Integers.{u} (reflectionOnCharacters D i)) = _
    rw [← MonoidAlgebra.mapDomainBialgHom_comp, reflectionOnCharacters_comp,
      MonoidAlgebra.mapDomainBialgHom_id]
    rfl
  let F := hopfSpec (CommRingCat.of Integers.{u})
  change F.map f.op ≫ F.map f.op = 𝟙 (F.obj (op P))
  rw [← Functor.map_comp, h, F.map_id]

private def torusReflectionIso (D : BasedRootDatum.{u}) (i : D.I) : splitTorus D ≅ splitTorus D :=
  ⟨torusReflection D i, torusReflection D i, torusReflection_comp D i, torusReflection_comp D i⟩

set_option backward.isDefEq.respectTransparency false in
private theorem torusPoint_reflection (D : BasedRootDatum.{u}) (i : D.I)
    (C : IntegralAlgebra.{u}) (v : TorusValues D C) :
    torusPoint D C v ≫ (torusReflection D i).hom.hom =
      torusPoint D C (v.comp (reflectionOnCharacters D i)) := by
  let M := Multiplicative D.X
  let a := reflectionOnCharacters D i
  let q :
      MonoidAlgebra Integers.{u} M →ₐ[Integers.{u}] MonoidAlgebra Integers.{u} M :=
    (MonoidAlgebra.mapDomainBialgHom Integers.{u} a).toAlgHom
  let e (w : TorusValues D C) := MonoidAlgebra.lift Integers.{u} C M
    ((Units.coeHom C).comp w)
  change integralSpec.map (CommAlgCat.ofHom (e v)).op ≫
      integralSpec.map (CommAlgCat.ofHom q).op =
    integralSpec.map (CommAlgCat.ofHom (e (v.comp a))).op
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  change (e v).comp q = e (v.comp a)
  apply MonoidAlgebra.algHom_ext
  · intro x
    change e v (MonoidAlgebra.mapDomain a (MonoidAlgebra.single x 1)) =
      e (v.comp a) (MonoidAlgebra.single x 1)
    rw [MonoidAlgebra.mapDomain_single]
    simp [e]
    rfl
  · apply AlgHom.ext
    intro r
    exact (((e v).comp q).commutes r).trans ((e (v.comp a)).commutes r).symm

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by the integral rank-one section restricts to the reflection
automorphism of the marked split torus. -/
theorem integralWeylSection_conjugates {D : BasedRootDatum.{u}} (M : Model D) (i : D.I) :
    (torusReflectionIso D i).hom ≫ M.torus =
      M.torus ≫ innerConjugationHom _ (integralWeylSection M i) := by
  apply Grp.hom_ext
  let C := CommAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative D.X))
  obtain ⟨v, hv⟩ := torusPoint_surjective D C (𝟙 (splitTorus D).X)
  have h := integralWeylPoint_reflectsTorus M i C v
  rw [← integralWeylSection_eval M i C, ← torusPoint_reflection, hv] at h
  change ((toUnit (splitTorus D).X ≫ integralWeylSection M i) *
    ((𝟙 (splitTorus D).X) ≫ M.torus.hom.hom) *
    ((toUnit (splitTorus D).X ≫ integralWeylSection M i)⁻¹)) =
      (𝟙 (splitTorus D).X ≫ (torusReflection D i).hom.hom) ≫ M.torus.hom.hom at h
  simp only [Category.id_comp] at h
  change (torusReflection D i).hom.hom ≫ M.torus.hom.hom =
    M.torus.hom.hom ≫ (innerConjugationHom _ (integralWeylSection M i)).hom.hom
  rw [comp_innerConjugation]
  simpa only [comp_toUnit_assoc] using h.symm


end IntegralWeylSections
section CompareBorelFibres

variable {S T : Scheme.{u}} {G B J : Grp (Over S)}
variable [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]

private theorem hasBorelFibres_of_sourceIso {i : B ⟶ G} {j : J ⟶ G}
    (hj : IsClosedImmersion j.hom.hom.left) (e : B ≅ J) (he : e.hom ≫ j = i)
    (hi : HasBorelFibres i) : HasBorelFibres j := by
  intro k _ _ a
  let F := changeBase a
  obtain ⟨hc, hB⟩ := hi k a
  have hclosed : IsClosedImmersion (F.map j).hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare a j.hom.hom).flip hj
  let A : ClosedSubgroup (F.obj G) := ⟨F.obj B, F.map i, hc⟩
  let V : ClosedSubgroup (F.obj G) := ⟨F.obj J, F.map j, hclosed⟩
  refine ⟨hclosed, isBorel_of_isos (G' := affineFibre (G := G) a) (B := A) (C := V)
    (Iso.refl _) (F.mapIso e) ?_ hB⟩
  change F.map i ≫ 𝟙 _ = F.map e.hom ≫ F.map j
  rw [Category.comp_id, ← F.map_comp, he]

/-- Conjugating a family preserves its Borel condition in every geometric
fibre, including for nonreduced test schemes. -/
theorem conjugateSubgroupFamily_isBorel {U : Over S} (i : B ⟶ G)
    (hiclosed : IsClosedImmersion i.hom.hom.left) (hs : Smooth B.X.hom)
    (hi : HasBorelFibres i) (g : U ⟶ G.X) :
    IsBorelFamily (conjugateSubgroupFamily i hiclosed hs g) :=
  hasBorelFibres_comp_iso (innerConjugation _ (sectionOfPoint g))
    (hasBorelFibres_changeBase hiclosed hi U.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem isBorelFamily_of_pullback_pointLifts {P Q : Over S} (p : Q ⟶ P)
    (hlift : ∀ (k : Type u) [Field k] [IsAlgClosed k] (b : ringSpec k ⟶ P.left),
      ∃ c : ringSpec k ⟶ Q.left, c ≫ p.left = b)
    (U : Family G P) (V : Family G Q) (e : SameFamily (U.pullback p) V)
    (hV : IsBorelFamily V) : IsBorelFamily U := by
  let A := (changeBase P.hom).obj G
  have : IsAffineHom A.X.hom :=
    MorphismProperty.pullback_snd G.X.hom P.hom (inferInstance : IsAffineHom G.X.hom)
  have : LocallyOfFinitePresentation A.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom P.hom))
  have : QuasiCompact A.X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom P.hom))
  let D := (changeBase Q.hom).obj G
  have : IsAffineHom D.X.hom :=
    MorphismProperty.pullback_snd G.X.hom Q.hom (inferInstance : IsAffineHom G.X.hom)
  have : LocallyOfFinitePresentation D.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom Q.hom))
  have : QuasiCompact D.X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom Q.hom))
  obtain ⟨d, hd⟩ := e
  have hd' : d.inv ≫ (U.pullback p).inclusion = V.inclusion := by
    rw [← hd, Iso.inv_hom_id_assoc]
  have hv : HasBorelFibres (U.pullback p).inclusion :=
    hasBorelFibres_of_sourceIso (G := D) (U.pullback p).closed d.symm hd' hV
  let w := compareAmbient p G
  have h := hasBorelFibres_comp_iso w hv
  have hw : (U.pullback p).inclusion ≫ w.hom = (changeBase p.left).map U.inclusion := by
    change ((changeBase p.left).map U.inclusion ≫ w.inv) ≫ w.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hw] at h
  exact hasBorelFibres_of_pointLifts p.left hlift U.closed h

end CompareBorelFibres

section ChartParametrization

variable {S : Scheme.{u}} {G B : Grp (Over S)} (j : B ⟶ G)
variable [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
variable {I : Type u} {X : I → Over S} (s : ∀ i, X i ⟶ G.X)

set_option backward.isDefEq.respectTransparency false in
/-- A cover by smooth right-product charts yields the relative right quotient
and its smooth closed Borel family. The construction uses actual subgroup
conjugation after pullback to the group. -/
theorem borelFamilyOfRightProductCharts
    (hj : IsClosedImmersion j.hom.hom.left) (hB : Smooth B.X.hom)
    (hgeom : HasBorelFibres j) (hX : ∀ i, Smooth (X i).hom)
    (hopen : ∀ i, IsOpenImmersion (rightProductChart j (s i)).left)
    (hcover : ∀ x : G.X.left, ∃ (i : I) (y : (X i ⊗ B.X).left),
      (rightProductChart j (s i)).left y = x) :
    ∃ (P : Over S) (p : G.X ⟶ P) (U : Family G P), Smooth P.hom ∧
      Smooth p.left ∧ Surjective p.left ∧ QuasiCompact p.left ∧ IsBorelFamily U ∧
      SameFamily (U.pullback p) (conjugateSubgroupFamily j hj hB (𝟙 G.X)) ∧
      ∀ (T : Over S) (g h : T ⟶ G.X),
        g ≫ p = h ≫ p ↔ ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h := by
  have : ∀ i, IsOpenImmersion (rightProductChart j (s i)).left := hopen
  obtain ⟨P, p, c, hP, hp, hsp, hc, hcov, _, hcp⟩ :=
    glueRightProductCharts j s hcover hB hX
  let C := chartsCover c hc hcov
  have hbqc : QuasiCompact B.X.hom := by
    rw [← CategoryTheory.Over.w j.hom.hom]
    infer_instance
  have hpqc : QuasiCompact p.left := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @QuasiCompact) C).mpr fun i ↦ ?_
    let h := hcp i
    have hsub : QuasiCompact (fst (X i) B.X).left :=
      inferInstanceAs (QuasiCompact (pullback.fst (X i).hom B.X.hom))
    exact (MorphismProperty.cancel_left_of_respectsIso @QuasiCompact h.isoPullback.hom
      (pullback.snd p.left (c i).left)).mp (h.isoPullback_hom_snd.symm ▸ hsub)
  have hcosets {T : Over S} (g h : T ⟶ G.X) (hgh : g ≫ p = h ≫ p) :
      ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h :=
    (rightProductQuotient_eq_iff j s p c hcp hc hcov g h hj).mp hgh
  obtain ⟨U, hU⟩ := universalFamilyOfRightQuotient j p hcosets hj hB
  have hlift (k : Type u) [Field k] [IsAlgClosed k] (b : ringSpec k ⟶ P.left) :
      ∃ d : ringSpec k ⟶ G.X.left, d ≫ p.left = b := by
    obtain ⟨i, y, hy⟩ := hcov (b (IsLocalRing.closedPoint k))
    have hr : Set.range b ⊆ Set.range (c i).left := by
      rintro _ ⟨t, rfl⟩
      have ht : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      exact ⟨y, hy.trans (congrArg b ht.symm)⟩
    have : IsOpenImmersion (c i).left := hc i
    let v := IsOpenImmersion.lift (c i).left b hr
    let e := lift (𝟙 (X i)) (1 : X i ⟶ B.X)
    refine ⟨v ≫ (e ≫ rightProductChart j (s i)).left, ?_⟩
    have he : (e ≫ rightProductChart j (s i)).left ≫ p.left = (c i).left := by
      have h : rightProductChart j (s i) ≫ p = fst (X i) B.X ≫ c i :=
        CategoryTheory.Over.OverMorphism.ext (hcp i).w
      have eh : (e ≫ rightProductChart j (s i)) ≫ p = c i := by
        rw [Category.assoc, h, ← Category.assoc, lift_fst, Category.id_comp]
      exact congrArg CategoryTheory.Over.Hom.left eh
    rw [Category.assoc, he]
    exact IsOpenImmersion.lift_fac _ _ _
  exact ⟨P, p, U, hP, hp, hsp, hpqc, isBorelFamily_of_pullback_pointLifts p hlift U
    (conjugateSubgroupFamily j hj hB (𝟙 G.X)) hU
    (conjugateSubgroupFamily_isBorel j hj hB hgeom (𝟙 G.X)), hU,
    fun _ g h ↦ rightProductQuotient_eq_iff j s p c hcp hc hcov g h hj⟩

end ChartParametrization

/-- Tensoring a system of equations with a fixed free algebra turns its
vanishing into the vanishing of coefficients in the variable algebra.
The resulting ideal is finitely generated when the original ideal is. -/
theorem existsCoefficientIdeal {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Free R A]
    (I : Ideal (A ⊗[R] B)) (hI : I.FG) :
    ∃ J : Ideal B, J.FG ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C] (f : B →ₐ[R] C),
        J ≤ RingHom.ker f ↔ I ≤ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) f) := by
  classical
  obtain ⟨s, hs⟩ := hI
  let basis := Module.Free.chooseBasis R A
  let coord := TensorProduct.equivFinsuppOfBasisLeft (N := B) basis
  let t := s.biUnion (fun x ↦ (coord x).support.image (coord x))
  refine ⟨Ideal.span (t : Set B), ⟨t, rfl⟩, ?_⟩
  intro C _ _ f
  let coord' := TensorProduct.equivFinsuppOfBasisLeft (N := C) basis
  let map := Algebra.TensorProduct.map (AlgHom.id R A) f
  have hcoord (x : A ⊗[R] B) (i) : coord' (map x) i = f (coord x i) := by
    refine TensorProduct.inductionOn (motive := fun z ↦ coord' (map z) i = f (coord z i)) x ?_ ?_
    · intro a b
      simp [coord', map, coord]
    · intro y z hy hz
      simp only [map_add, Finsupp.add_apply, hy, hz]
  have vanish (x : A ⊗[R] B) : map x = 0 ↔
      ∀ i ∈ (coord x).support, f (coord x i) = 0 := by
    refine ⟨fun h i _ ↦ (hcoord x i).symm.trans (by simp [h]), fun h ↦ ?_⟩
    apply coord'.injective
    ext i
    rw [hcoord, map_zero, Finsupp.zero_apply]
    by_cases hi : i ∈ (coord x).support
    · exact h i hi
    · rw [Finsupp.notMem_support_iff.mp hi, map_zero]
  rw [← hs, Ideal.span_le, Ideal.span_le]
  constructor
  · intro h x hx
    apply (vanish x).mpr
    intro i hi
    exact h (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩)
  · intro h b hb
    obtain ⟨x, hx, hbx⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hbx
    exact (vanish x).mp (h hx) i hi

open TensorProduct in
/-- A finitely generated ideal cutting out a base-flat algebra vanishes if
it vanishes on every field fibre of the base. -/
theorem ideal_eq_bot_of_flat_quotient_fieldFibres
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I.FG) [Module.Flat R (A ⧸ I)]
    (hf : ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id R K) (Ideal.Quotient.mkₐ R I))) :
    I = ⊥ := by
  let q := (Ideal.Quotient.mkₐ R I).toLinearMap
  let i := I.subtype.restrictScalars R
  have ex : Function.Exact i q := by
    intro a
    change Ideal.Quotient.mk I a = 0 ↔ a ∈ Set.range i
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨fun ha ↦ ⟨⟨a, ha⟩, rfl⟩, by rintro ⟨⟨b, hb⟩, rfl⟩; exact hb⟩
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hi : Function.Injective i := I.injective_subtype
  have hfin : Module.Finite A I := Module.Finite.of_fg hI
  have hsupport : Module.support A I = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    let K := p.asIdeal.ResidueField
    let : Algebra R K := inferInstanceAs (Algebra R p.asIdeal.ResidueField)
    let : IsScalarTower R A K := inferInstanceAs (IsScalarTower R A p.asIdeal.ResidueField)
    have htr : Function.Injective (i.lTensor K) :=
      LinearMap.lTensor_injective_of_exact_of_flat q hq i hi ex K
    let e := ((LinearMap.id : I →ₗ[A] I).restrictScalars R).liftBaseChange A
    let ρ : K ⊗[R] I →ₗ[K] K ⊗[A] I :=
      (AlgebraTensorModule.lTensor K K e) ∘ₗ
        (AlgebraTensorModule.cancelBaseChange R A K K I).symm.toLinearMap
    have hzero (a : K) (x : I) : a ⊗ₜ[A] x = 0 := by
      have h : a ⊗ₜ[R] x = 0 := by
        apply htr
        rw [LinearMap.lTensor_tmul, map_zero]
        apply hf K
        have hx : (Ideal.Quotient.mk I) (i x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr x.property
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
          hx, tmul_zero, map_zero]
      have hρ := congrArg ρ h
      simpa [ρ, e, LinearMap.liftBaseChange_tmul] using hρ
    have hs : Subsingleton (K ⊗[A] I) := by
      apply subsingleton_of_forall_eq 0
      intro t
      refine TensorProduct.inductionOn (motive := fun t ↦ t = 0) t hzero ?_
      intro x y hx hy
      rw [hx, hy, add_zero]
    exact not_nontrivial_iff_subsingleton.mpr hs
      ((Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hp)
  have hs : Subsingleton I := (Module.support_eq_empty_iff (R := A)).mp hsupport
  exact Submodule.subsingleton_iff_eq_bot.mp hs

section AffineFactorization

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

private theorem coordinateQuotient_factors (I : Ideal A) (f : A →ₐ[R] C) :
    (∃ g : coordSpec R C ⟶ coordSpec R (A ⧸ I),
      g ≫ coordSpecMap (Ideal.Quotient.mkₐ R I) = coordSpecMap f) ↔ I ≤ RingHom.ker f := by
  let F := algSpec (CommRingCat.of R)
  let FF := algSpec.fullyFaithful (R := CommRingCat.of R)
  constructor
  · rintro ⟨g, hg⟩
    let l := FF.preimage g
    have eq : l ≫ (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op = (CommAlgCat.ofHom f).op := by
      apply FF.map_injective
      rw [Functor.map_comp, FF.map_preimage]
      exact hg
    have hf : l.unop.hom.comp (Ideal.Quotient.mkₐ R I) = f :=
      congrArg (fun v ↦ v.unop.hom) eq
    intro a ha
    change f a = 0
    rw [← hf, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      map_zero]
  · intro hf
    let l := Ideal.Quotient.liftₐ I f (fun a ha ↦ hf ha)
    refine ⟨coordSpecMap l, ?_⟩
    rw [← coordSpecMap_comp]
    exact congrArg coordSpecMap (show l.comp (Ideal.Quotient.mkₐ R I) = f from by ext; rfl)

private def coordinateProductIso (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : coordSpec R (A ⊗[R] B) ≅ coordSpec R A ⊗ coordSpec R B :=
  let F := algSpec (CommRingCat.of R)
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of R)
  asIso (Functor.OplaxMonoidal.δ F (op (CommAlgCat.of R A)) (op (CommAlgCat.of R B)))

private theorem coordinateProductIso_natural (f : B →ₐ[R] C) :
    (coordinateProductIso R A C).hom ≫ (coordSpec R A ◁ coordSpecMap f) =
      coordSpecMap (Algebra.TensorProduct.map (AlgHom.id R A) f) ≫
        (coordinateProductIso R A B).hom := by
  let F := algSpec (CommRingCat.of R)
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of R)
  exact Functor.OplaxMonoidal.δ_natural_right F (op (CommAlgCat.of R A)) (CommAlgCat.ofHom f).op

set_option backward.isDefEq.respectTransparency false in
/-- A closed condition on the product with a scheme with free affine
coordinates gives a finitely presented closed condition on the affine test factor. -/
theorem existsAffineFactorizationLocus [Module.Free R A]
    {D : CategoryTheory.Over (Spec (CommRingCat.of R))}
    (d : D ⟶ coordSpec R A ⊗ coordSpec R B) (hd : IsClosedImmersion d.left)
    (hdf : LocallyOfFinitePresentation d.left) :
    ∃ J : Ideal B, J.FG ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C] (f : B →ₐ[R] C),
        (∃ g : coordSpec R A ⊗ coordSpec R C ⟶ D, g ≫ d = coordSpec R A ◁ coordSpecMap f) ↔
        ∃ v : coordSpec R C ⟶ coordSpec R (B ⧸ J),
          v ≫ coordSpecMap (Ideal.Quotient.mkₐ R J) = coordSpecMap f := by
  let b := coordinateProductIso R A B
  let i := d ≫ b.inv
  have hi : IsClosedImmersion i.left := by
    have : IsIso b.inv.left := ((CategoryTheory.Over.forget _).mapIso b).isIso_inv
    exact IsClosedImmersion.comp d.left b.inv.left
  change IsClosedImmersion (Y := Spec (CommRingCat.of (A ⊗[R] B))) i.left at hi
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (R := CommRingCat.of (A ⊗[R] B))
    (f := i.left)).mp hi
  change D.left ≅ (coordSpec R ((A ⊗[R] B) ⧸ I)).left at e
  let qI := coordSpecMap (Ideal.Quotient.mkₐ R I)
  have hei : i.left = e.hom ≫ qI.left := he
  have hw : e.hom ≫ (coordSpec R ((A ⊗[R] B) ⧸ I)).hom = D.hom := by
    rw [← CategoryTheory.Over.w qI, ← Category.assoc, ← hei, CategoryTheory.Over.w i]
  let ei : D ≅ coordSpec R ((A ⊗[R] B) ⧸ I) := CategoryTheory.Over.isoMk e hw
  have heq : i = ei.hom ≫ qI := CategoryTheory.Over.OverMorphism.ext hei
  have qfp : LocallyOfFinitePresentation qI.left := by
    have hif : LocallyOfFinitePresentation i.left := by
      have : IsIso b.inv.left := ((CategoryTheory.Over.forget _).mapIso b).isIso_inv
      exact MorphismProperty.comp_mem _ _ _ hdf inferInstance
    rw [show qI.left = e.inv ≫ i.left from by rw [hei, Iso.inv_hom_id_assoc]]
    exact MorphismProperty.comp_mem _ _ _ inferInstance hif
  have hI : I.FG := by
    have hfp := (LocallyOfFinitePresentation.SpecMap_iff _).mp qfp
    let : Algebra.FinitePresentation (A ⊗[R] B) ((A ⊗[R] B) ⧸ I) :=
      RingHom.finitePresentation_algebraMap.mp hfp
    simpa only [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using
      Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ (A ⊗[R] B) I)
        Ideal.Quotient.mk_surjective
  obtain ⟨J, hJ, hcoeff⟩ := existsCoefficientIdeal I hI
  refine ⟨J, hJ, ?_⟩
  intro C _ _ f
  let c := coordinateProductIso R A C
  let m := Algebra.TensorProduct.map (AlgHom.id R A) f
  have ec : c.hom ≫ (coordSpec R A ◁ coordSpecMap f) = coordSpecMap m ≫ b.hom :=
    coordinateProductIso_natural f
  have hm : (∃ g : coordSpec R A ⊗ coordSpec R C ⟶ D,
      g ≫ d = coordSpec R A ◁ coordSpecMap f) ↔
      ∃ v : coordSpec R (A ⊗[R] C) ⟶ coordSpec R ((A ⊗[R] B) ⧸ I),
        v ≫ qI = coordSpecMap m := by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨c.hom ≫ g ≫ ei.hom, ?_⟩
      simp only [Category.assoc, ← heq, i, reassoc_of% hg, reassoc_of% ec,
        Iso.hom_inv_id, Category.comp_id]
    · rintro ⟨v, hv⟩
      refine ⟨c.inv ≫ v ≫ ei.inv, (cancel_mono b.inv).mp ?_⟩
      simp only [Category.assoc, show d ≫ b.inv = i from rfl, heq, Iso.inv_hom_id_assoc, hv]
      rw [← Iso.inv_hom_id_assoc c (coordSpec R A ◁ coordSpecMap f), ec, Category.assoc,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact hm.trans ((coordinateQuotient_factors I m).trans
    ((hcoeff C f).symm.trans (coordinateQuotient_factors J f).symm))

set_option backward.isDefEq.respectTransparency false in
/-- The same closed factorization locus tests containment on arbitrary base
schemes, by gluing the unique lifts on affine open charts. -/
theorem existsClosedFactorizationLocus [Module.Free R A]
    {D : CategoryTheory.Over (Spec (CommRingCat.of R))}
    (d : D ⟶ coordSpec R A ⊗ coordSpec R B) (hd : IsClosedImmersion d.left)
    (hdf : LocallyOfFinitePresentation d.left) :
    ∃ (Z : CategoryTheory.Over (Spec (CommRingCat.of R))) (j : Z ⟶ coordSpec R B),
      IsClosedImmersion j.left ∧ LocallyOfFinitePresentation j.left ∧
      ∀ (T : CategoryTheory.Over (Spec (CommRingCat.of R))) (x : T ⟶ coordSpec R B),
        (∃ g : coordSpec R A ⊗ T ⟶ D, g ≫ d = coordSpec R A ◁ x) ↔
        ∃ v : T ⟶ Z, v ≫ j = x := by
  obtain ⟨J, hJ, htest⟩ := existsAffineFactorizationLocus d hd hdf
  let Z := coordSpec R (B ⧸ J)
  let j := coordSpecMap (Ideal.Quotient.mkₐ R J)
  have hj : IsClosedImmersion j.left :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hfp : LocallyOfFinitePresentation j.left := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    change (Ideal.Quotient.mk J).FinitePresentation
    exact RingHom.FinitePresentation.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  have hAffine (C : Type u) [CommRing C] [Algebra R C] (x : coordSpec R C ⟶ coordSpec R B) :
      (∃ g : coordSpec R A ⊗ coordSpec R C ⟶ D, g ≫ d = coordSpec R A ◁ x) ↔
        ∃ v : coordSpec R C ⟶ Z, v ≫ j = x := by
    let FF := algSpec.fullyFaithful (R := CommRingCat.of R)
    let f : B →ₐ[R] C := (FF.preimage x).unop.hom
    have hf : coordSpecMap f = x := FF.map_preimage x
    simpa only [hf] using htest C f
  refine ⟨Z, j, hj, hfp, ?_⟩
  intro T x
  constructor
  · rintro ⟨g, hg⟩
    let V := T.left.affineCover
    let X (i : V.I₀) := CategoryTheory.Over.mk (V.f i ≫ T.hom)
    let a (i : V.I₀) : X i ⟶ T := CategoryTheory.Over.homMk (V.f i) rfl
    have hlift (i : V.I₀) : ∃ v : X i ⟶ Z, v ≫ j = a i ≫ x := by
      have hX : IsAffine (X i).left := Scheme.isAffine_affineCover T.left i
      obtain ⟨C, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr hX
      let c := e.hom ≫ a i
      have he : ((coordSpec R A ◁ c) ≫ g) ≫ d = coordSpec R A ◁ (c ≫ x) := by
        rw [Category.assoc, hg, ← MonoidalCategory.whiskerLeft_comp]
      obtain ⟨v, hv⟩ := (hAffine C.unop (c ≫ x)).mp ⟨_, he⟩
      exact ⟨e.inv ≫ v, by simp only [Category.assoc, hv, c, Iso.inv_hom_id_assoc]⟩
    choose v hv using hlift
    have hvLeft (i : V.I₀) : (v i).left ≫ j.left = V.f i ≫ x.left :=
      congrArg CategoryTheory.Over.Hom.left (hv i)
    have : Mono j.left := inferInstance
    let vLeft := V.glueMorphisms (fun i ↦ (v i).left) (fun i l ↦ by
      apply (cancel_mono j.left).mp
      rw [Category.assoc, Category.assoc, hvLeft, hvLeft, ← Category.assoc, ← Category.assoc,
        pullback.condition])
    have hLeft : vLeft ≫ j.left = x.left := by
      apply V.hom_ext
      intro i
      rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hvLeft]
    let w : T ⟶ Z := CategoryTheory.Over.homMk vLeft (by
      rw [← CategoryTheory.Over.w j, ← Category.assoc, hLeft, CategoryTheory.Over.w x])
    exact ⟨w, CategoryTheory.Over.OverMorphism.ext hLeft⟩
  · rintro ⟨v, hv⟩
    obtain ⟨g, hg⟩ := (hAffine (B ⧸ J) j).mpr ⟨𝟙 Z, Category.id_comp _⟩
    refine ⟨(coordSpec R A ◁ v) ≫ g, ?_⟩
    rw [Category.assoc, hg, ← MonoidalCategory.whiskerLeft_comp, hv]

set_option backward.isDefEq.respectTransparency false in
/-- The factorization locus is intrinsic to the given closed immersion.
Affine coordinates on its fixed factor are only used to obtain equations. -/
theorem existsClosedFactorizationLocus_of_affine [Module.Free R A]
    {X Y D : CategoryTheory.Over (Spec (CommRingCat.of R))} [IsAffine Y.left]
    (eX : X ≅ coordSpec R A) (d : D ⟶ X ⊗ Y) (hd : IsClosedImmersion d.left)
    (hdf : LocallyOfFinitePresentation d.left) :
    ∃ (Z : CategoryTheory.Over (Spec (CommRingCat.of R))) (j : Z ⟶ Y),
      IsClosedImmersion j.left ∧ LocallyOfFinitePresentation j.left ∧
      ∀ (T : CategoryTheory.Over (Spec (CommRingCat.of R))) (x : T ⟶ Y),
        (∃ g : X ⊗ T ⟶ D, g ≫ d = X ◁ x) ↔ ∃ v : T ⟶ Z, v ≫ j = x := by
  obtain ⟨B, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr
    (inferInstance : IsAffine Y.left)
  let eY := e.symm
  let b := tensorIso eX eY
  let d' := d ≫ b.hom
  have : IsIso b.hom.left := ((CategoryTheory.Over.forget _).mapIso b).isIso_hom
  have hd' : IsClosedImmersion d'.left := IsClosedImmersion.comp d.left b.hom.left
  have hdf' : LocallyOfFinitePresentation d'.left :=
    MorphismProperty.comp_mem _ _ _ hdf inferInstance
  obtain ⟨Z, j, hj, hfp, h⟩ := existsClosedFactorizationLocus (B := B.unop) d' hd' hdf'
  have : IsIso eY.inv.left := ((CategoryTheory.Over.forget _).mapIso eY).isIso_inv
  refine ⟨Z, j ≫ eY.inv, IsClosedImmersion.comp j.left eY.inv.left,
    MorphismProperty.comp_mem _ _ _ hfp inferInstance, ?_⟩
  intro T x
  let a := tensorIso eX (Iso.refl T)
  let x' := x ≫ eY.hom
  have hc : a.hom ≫ (coordSpec R A ◁ x') = (X ◁ x) ≫ b.hom := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [a, b]
    · simp [a, b, x']
  have hv : (∃ v : T ⟶ Z, v ≫ j = x') ↔ ∃ v : T ⟶ Z, v ≫ (j ≫ eY.inv) = x := by
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v, (Category.assoc _ _ _).symm.trans ?_⟩
      rw [hv, show x' = x ≫ eY.hom from rfl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rintro ⟨v, hv⟩
      refine ⟨v, (cancel_mono eY.inv).mp ?_⟩
      simpa only [Category.assoc, x', Iso.hom_inv_id, Category.comp_id] using hv
  rw [← hv, ← h T x']
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨a.inv ≫ g, ?_⟩
    simp only [d', Category.assoc, reassoc_of% hg, ← hc, Iso.inv_hom_id_assoc]
  · rintro ⟨g, hg⟩
    refine ⟨a.hom ≫ g, (cancel_mono b.hom).mp ?_⟩
    rw [Category.assoc, Category.assoc, show d ≫ b.hom = d' from rfl, hg, hc]

end AffineFactorization

section BorelContainment

open private finitePresentation_of_closed_over from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

variable {S : Scheme.{u}} {G B : Grp (CategoryTheory.Over S)}
variable {T U : CategoryTheory.Over S}

private abbrev familyOverBase (Q : Family G T) : CategoryTheory.Over S :=
  (CategoryTheory.Over.map T.hom).obj Q.group.X

/-- The family inclusion as a closed subscheme of the ambient product. -/
def familyProductInclusion (Q : Family G T) : familyOverBase Q ⟶ G.X ⊗ T :=
  lift (unbasePoint T.hom Q.group.X G Q.inclusion.hom.hom)
    (CategoryTheory.Over.homMk Q.group.X.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem familyProductInclusion_left (Q : Family G T) :
    (familyProductInclusion Q).left = Q.inclusion.hom.hom.left := by
  apply pullback.hom_ext
  · exact congrArg CategoryTheory.Over.Hom.left (lift_fst _ _)
  · change (familyProductInclusion Q ≫ snd G.X T).left =
      Q.inclusion.hom.hom.left ≫ ((changeBase T.hom).obj G).X.hom
    rw [familyProductInclusion, lift_snd, CategoryTheory.Over.w Q.inclusion.hom.hom]
    rfl

/-- Containment of the conjugate of a fixed subgroup in a given closed family
on a test scheme. The morphism respects the actual inclusions in the group. -/
def ConjugateContained (j : B ⟶ G) (Q : Family G T) (a : U ⟶ T) (g : U ⟶ G.X) : Prop :=
  ∃ b : B.X ⊗ U ⟶ familyOverBase Q,
    b ≫ familyProductInclusion Q = conjugateOver j g ≫ (G.X ◁ a)

set_option backward.isDefEq.respectTransparency false in
/-- A fixed subgroup with free affine coordinates has a finitely presented
closed conjugacy-containment locus against a smooth closed family over an
underlying affine test scheme. -/
theorem existsConjugateContainmentLocus {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Free R A]
    {G B : Grp (CategoryTheory.Over (ringSpec R))} {T : CategoryTheory.Over (ringSpec R)}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [IsAffine T.left]
    (j : B ⟶ G) (hB : B.X ≅ coordSpec R A) (Q : Family G T) :
    ∃ (Z : CategoryTheory.Over (ringSpec R)) (l : Z ⟶ G.X ⊗ T),
      IsClosedImmersion l.left ∧ LocallyOfFinitePresentation l.left ∧
        ∀ (U : CategoryTheory.Over (ringSpec R)) (a : U ⟶ T) (g : U ⟶ G.X),
          ConjugateContained j Q a g ↔ ∃ b : U ⟶ Z, b ≫ l = lift g a := by
  let Y := G.X ⊗ T
  let i := familyProductInclusion Q
  let c := conjugateOver j (fst G.X T) ≫ (G.X ◁ snd G.X T)
  let D := pullback i c
  let d : D ⟶ B.X ⊗ Y := pullback.snd i c
  have hi : IsClosedImmersion i.left := (familyProductInclusion_left Q).symm ▸ Q.closed
  have hY : IsAffine Y.left := inferInstanceAs (IsAffine (pullback G.X.hom T.hom))
  have hp : LocallyOfFinitePresentation (snd G.X T).left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom T.hom))
  have hcomp : LocallyOfFinitePresentation (i.left ≫ (snd G.X T).left) := by
    have h : i.left ≫ (snd G.X T).left = Q.group.X.hom :=
      congrArg CategoryTheory.Over.Hom.left (lift_snd _ _)
    rw [h]
    have : Smooth Q.group.X.hom := Q.smooth
    infer_instance
  have hif : LocallyOfFinitePresentation i.left := finitePresentation_of_closed_over i.left (snd G.X T).left
  have hd := (IsPullback.of_hasPullback i c).map (CategoryTheory.Over.forget (ringSpec R))
  have hc : IsClosedImmersion d.left := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hd hi
  have hdf : LocallyOfFinitePresentation d.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hd hif
  obtain ⟨Z, l, hl, hlf, h⟩ := existsClosedFactorizationLocus_of_affine hB d hc hdf
  refine ⟨Z, l, hl, hlf, ?_⟩
  intro U a g
  have hcg : (B.X ◁ lift g a) ≫ c = conjugateOver j g ≫ (G.X ◁ a) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [c, conjugateOver, MonObj.comp_mul, GrpObj.comp_inv]
    · simp [c, conjugateOver]
  rw [← h U (lift g a), ConjugateContained, ← hcg]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨pullback.lift z (B.X ◁ lift g a) hz, pullback.lift_snd _ _ _⟩
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ pullback.fst i c, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, show z ≫ pullback.snd i c = _ from hz]

end BorelContainment


private theorem innerConjugationComp {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {B G : Grp C} (j : B ⟶ G) (g : 𝟙_ C ⟶ B.X) :
    innerConjugationHom B g ≫ j = j ≫ innerConjugationHom G (g ≫ j.hom.hom) := by
  apply Grp.hom_ext
  have hj : IsMonHom j.hom.hom := j.hom.isMonHom_hom
  change (innerConjugationHom B g).hom.hom ≫ j.hom.hom =
    j.hom.hom ≫ (innerConjugationHom G (g ≫ j.hom.hom)).hom.hom
  have h := comp_innerConjugation B g (𝟙 B.X)
  simp only [Category.id_comp] at h
  rw [h, comp_innerConjugation, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
    Category.assoc, Category.id_comp]

section WeylFibre

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.RationalRealization (Realization)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.BorelNormalizer (InducesTorusConjugation)
open private torusPoint_surjective
  from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

variable {D : BasedRootDatum.{u}} {k : Type u} [Field k]
variable {L : Specs.RootGroups.AdditiveLine k}
attribute [local instance] integerAlgebra

private def integralWeylSectionFibre (M : Model D) (a : D.I) :
    𝟙_ (SchemeOver k) ⟶ ((fibre k).obj M.group).X :=
  Functor.LaxMonoidal.ε (CategoryTheory.Over.pullback (integralSpecMap k)) ≫
    (CategoryTheory.Over.pullback (integralSpecMap k)).map (integralWeylSection M a)

private def markedReflection (F : Realization D L)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group) (a : D.I) :
    F.pinned.pair.T.group ≅ F.pinned.pair.T.group :=
  t.symm ≪≫ (fibre k).mapIso (torusReflectionIso D a) ≪≫ t

private theorem markedReflection_inv (F : Realization D L)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group) (a : D.I) :
    (markedReflection F t a).inv = (markedReflection F t a).hom := by
  change t.inv ≫ (fibre k).map (torusReflection D a) ≫ t.hom =
    (t.inv ≫ (fibre k).map (torusReflection D a)) ≫ t.hom
  exact (Category.assoc ..).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 350000 in
/-- In any marked field fibre, the reduction of the rank-one section
normalizes the specified maximal torus and induces its marked reflection. -/
theorem integralWeylSection_induces_on_fibre (M : Model D) (a : D.I) (F : Realization D L)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (ht : (fibre k).map M.torus ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion) :
    InducesTorusConjugation F.pinned.pair.T
      (integralWeylSectionFibre M a ≫ e.hom.hom.hom) (markedReflection F t a) := by
  let T := F.pinned.pair.T
  let F₀ := fibre k
  let i := F₀.map M.torus
  let w := integralWeylSectionFibre (k := k) M a
  let g := w ≫ e.hom.hom.hom
  have h := F₀.congr_map (integralWeylSection_conjugates M a)
  simp only [Functor.map_comp] at h
  have hm : F₀.map (innerConjugationHom M.group (integralWeylSection M a)) =
      innerConjugationHom (F₀.obj M.group) w :=
    mapInnerConjugation (CategoryTheory.Over.pullback (integralSpecMap k)) M.group (integralWeylSection M a)
  rw [hm] at h
  have ht₀ : i ≫ e.hom = t.hom ≫ T.inclusion := ht
  have ht' : T.inclusion = t.inv ≫ i ≫ e.hom := by
    rw [ht₀, Iso.inv_hom_id_assoc]
  suffices heq : (markedReflection F t a).hom ≫ T.inclusion =
       T.inclusion ≫ innerConjugationHom F.pinned.pair.G.val g by
    unfold InducesTorusConjugation
    rw [heq]
    exact comp_innerConjugation _ _ T.inclusion.hom.hom
  calc
    _ = t.inv ≫ F₀.map (torusReflectionIso D a).hom ≫ i ≫ e.hom := by
      change (t.inv ≫ F₀.map (torusReflectionIso D a).hom ≫ t.hom) ≫ T.inclusion = _
      simp only [Category.assoc, ← ht₀]
    _ = (t.inv ≫ i) ≫ innerConjugationHom (F₀.obj M.group) w ≫ e.hom := by
      have hv := congrArg
        (fun f : F₀.obj (splitTorus D) ⟶ F₀.obj M.group ↦ t.inv ≫ f ≫ e.hom) h
      change t.inv ≫ (F₀.map (torusReflectionIso D a).hom ≫ i) ≫ e.hom =
        t.inv ≫ (i ≫ innerConjugationHom (F₀.obj M.group) w) ≫ e.hom at hv
      simpa only [Category.assoc] using hv
    _ = t.inv ≫ i ≫ e.hom ≫ innerConjugationHom F.pinned.pair.G.val g := by
      have hconj := innerConjugationComp e.hom w
      change innerConjugationHom (F₀.obj M.group) w ≫ e.hom =
        e.hom ≫ innerConjugationHom F.pinned.pair.G.val g at hconj
      simpa only [Category.assoc] using congrArg (fun a ↦ t.inv ≫ i ≫ a) hconj
    _ = _ := by simp only [ht', Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The induced automorphism acts on the characters in the integral marking
by the same lattice reflection as the rank-one word. -/
theorem markedReflection_character (a : D.I) (F : Realization D L)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (hval : ∀ (R : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) R)
      (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
      ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
        (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    (x : D.X) :
    (markedReflection F t a).inv ≫ Additive.toMul (F.datumIso.val.weightEquiv x) =
      Additive.toMul (F.datumIso.val.weightEquiv (D.datum.reflection a x)) := by
  apply RootData.CharacterPairing.characterValuesDetectCharacters F.pinned.pair.split
  intro R z
  let C := CommAlgCat.of Integers.{u} R
  let s : GroupPoints ((fibre k).obj (splitTorus D)) R := z ≫ t.inv.hom.hom
  let b := (torusReflection D a)
  let sb : GroupPoints ((fibre k).obj (splitTorus D)) R := s ≫ ((fibre k).map b).hom.hom
  obtain ⟨v, hv⟩ := torusPoint_surjective D C (forgetFibrePoint (splitTorus D) R s)
  have hvb : forgetFibrePoint (splitTorus D) R sb =
      torusPoint D C (v.comp (reflectionOnCharacters D a)) := by
    rw [forgetFibrePoint_map b R s, ← hv, torusPoint_reflection]
  have hz : s ≫ t.hom.hom.hom = z := by
    have he := congrArg (fun p ↦ p.hom.hom) t.inv_hom_id
    change t.inv.hom.hom ≫ t.hom.hom.hom = 𝟙 _ at he
    change (z ≫ t.inv.hom.hom) ≫ t.hom.hom.hom = z
    simpa only [Category.assoc, Category.comp_id] using congrArg (z ≫ ·) he
  have hzb : sb ≫ t.hom.hom.hom = z ≫ (markedReflection F t a).inv.hom.hom := by
    rw [markedReflection_inv]
    change ((z ≫ t.inv.hom.hom) ≫ ((fibre k).map b).hom.hom) ≫ t.hom.hom.hom =
      z ≫ t.inv.hom.hom ≫ ((fibre k).map b).hom.hom ≫ t.hom.hom.hom
    simp only [Category.assoc]
  have hx := hval R s v hv.symm (D.datum.reflection a x)
  have hb := hval R sb _ hvb x
  rw [hz] at hx
  rw [hzb] at hb
  exact hb.trans hx.symm

open Specs.AbstractPairing (Datum)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)

open private normalizes_of_conjugates_self from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private labelConjugation inducedConjugation_unique automorphism_eq_of_weight
  from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private normalizerLabel normalizer_isRepresentative
  from LinearAlgebraicGroups.Flag.BruhatCells
open private coroot_functional_of_reflection from LinearAlgebraicGroups.Classification.Pinning

set_option backward.isDefEq.respectTransparency false in
private theorem integralWeylSection_label (M : Model D) (a : D.I) (F : Realization D L)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (ht : (fibre k).map M.torus ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion)
    (hval : ∀ (R : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) R)
      (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
      ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
        (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    [IsCommMonObj F.pinned.pair.T.group.X] {E : Datum F.pinned.pair.T} (I : Identification E) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X,
      n ≫ I.normalizer.inclusion.hom.hom =
        integralWeylSectionFibre M a ≫ e.hom.hom.hom ∧
      normalizerLabel I n = RootPairing.weylGroup.ofIdx E.rootDatum (F.datumIso.val.indexEquiv a) := by
  let T := F.pinned.pair.T
  let g : 𝟙_ (SchemeOver k) ⟶ F.pinned.pair.G.val.X :=
    integralWeylSectionFibre M a ≫ e.hom.hom.hom
  let r := markedReflection F t a
  have hr : InducesTorusConjugation T g r := integralWeylSection_induces_on_fibre M a F e t ht
  have hn : Normalizes T.inclusion g :=
    normalizes_of_conjugates_self T (show ConjugatesSubgroups g T T from ⟨r, hr⟩)
  obtain ⟨n, he⟩ := (I.representsNormalizer _ g).mp hn
  let w := normalizerLabel I n
  have hc := labelConjugation I.image (I.labelEquiv w) n (normalizer_isRepresentative I n)
  rw [he] at hc
  have hh : I.image.conjugation (I.labelEquiv w) = r := inducedConjugation_unique hc hr
  let f := F.datumIso.val.weightEquiv
  let b := F.datumIso.val.indexEquiv a
  let p := (D.datum.coroot' a).comp f.symm.toLinearMap
  have hb : f (D.datum.root a) = E.rootDatum.root b := by
    let := F.attached.comm
    have hroot := F.datumIso.val.toHom.root_weightMap_apply D.datum F.attached.toBased.datum a
    change f (D.datum.root a) = F.attached.datum.rootDatum.root b at hroot
    rw [hroot, F.attached.datum.root_eq, E.root_eq]
  have hp : p (E.rootDatum.root b) = 2 := by
    rw [← hb]
    change D.datum.coroot' a (f.symm (f (D.datum.root a))) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact D.datum.pairing_same a
  have hact (y : Additive (Character T.group)) :
      w.val.weightEquiv y = y - p y • E.rootDatum.root b := by
    obtain ⟨x, rfl⟩ := f.surjective y
    let χ := Additive.toMul (f x)
    change w.val.weightEquiv (Additive.ofMul χ) = _
    rw [I.characterAction, I.image.characterAction, hh]
    have hrχ := markedReflection_character a F t hval x
    change Additive.ofMul ((markedReflection F t a).inv ≫
      Additive.toMul (F.datumIso.val.weightEquiv x)) = _
    rw [hrχ]
    change f (D.datum.reflection a x) = f x - D.datum.coroot' a (f.symm (f x)) • _
    rw [LinearEquiv.symm_apply_apply, D.datum.reflection_apply, map_sub, map_smul, hb]
  have hcoroot := coroot_functional_of_reflection E.rootDatum b w.val p hp hact
  refine ⟨n, he, Subtype.ext (automorphism_eq_of_weight (D := E) fun χ ↦ ?_)⟩
  change w.val.weightEquiv (Additive.ofMul χ) =
    (RootPairing.Equiv.reflection E.rootDatum b).weightEquiv (Additive.ofMul χ)
  rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply, hact]
  change _ = _ - (E.rootDatum.toLinearMap.flip (E.rootDatum.coroot b)) (Additive.ofMul χ) • _
  rw [hcoroot]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension of integral points followed by the marked field comparison. -/
private def integralSectionsToFibre (M : Model D) (F : Realization D L)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val) :
    (𝟙_ (Over Base.{u}) ⟶ M.group.X) →* (𝟙_ (SchemeOver k) ⟶ F.pinned.pair.G.val.X) := by
  let A := CategoryTheory.Over.pullback (integralSpecMap k)
  let f (g : 𝟙_ (Over Base.{u}) ⟶ M.group.X) :
      𝟙_ (SchemeOver k) ⟶ F.pinned.pair.G.val.X :=
    (Functor.LaxMonoidal.ε A ≫ A.map g) ≫ e.hom.hom.hom
  refine MonoidHom.mk' f fun g h ↦ ?_
  have : IsMonHom e.hom.hom.hom := e.hom.hom.isMonHom_hom
  change (Functor.LaxMonoidal.ε A ≫ A.map (g * h)) ≫ e.hom.hom.hom = f g * f h
  let G' := A.mapGrp.obj M.group
  let x : A.obj (𝟙_ (Over Base.{u})) ⟶ G'.X := A.map g
  let y : A.obj (𝟙_ (Over Base.{u})) ⟶ G'.X := A.map h
  have hmap : A.map (g * h) = x * y := Functor.map_mul A g h
  have hr := congrArg (fun v : A.obj (𝟙_ (Over Base.{u})) ⟶ G'.X ↦
    (Functor.LaxMonoidal.ε A ≫ v) ≫ e.hom.hom.hom) hmap
  rw [MonObj.comp_mul, MonObj.mul_comp] at hr
  exact hr

set_option backward.isDefEq.respectTransparency false in
/-- Every Weyl element of a marked field fibre can be represented by a normalizer
point whose image in the group is the specialization of an integral section. -/
theorem integralSectionsRepresentWeyl (M : Model D) (F : Realization D L)
    (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
    (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
    (ht : (fibre k).map M.torus ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion)
    (hval : ∀ (R : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) R)
      (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
      forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
      ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
        (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R))
    [IsCommMonObj F.pinned.pair.T.group.X] {E : Datum F.pinned.pair.T} (I : Identification E)
    (w : E.rootDatum.weylGroup) :
    ∃ (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) (g : 𝟙_ (Over Base.{u}) ⟶ M.group.X),
      n ≫ I.quotient.hom.hom = I.image.constantGroup.sectionPoint (I.labelEquiv w) ∧
      n ≫ I.normalizer.inclusion.hom.hom = integralSectionsToFibre M F e g := by
  let j := ((yonedaGrp.map I.normalizer.inclusion).app (op (𝟙_ (SchemeOver k)))).hom
  let lift := integralSectionsToFibre M F e
  let N := lift.range.comap j
  let W := N.map (normalizerLabel I)
  have hgen (b : Specs.AbstractPairing.Root F.pinned.pair.T) :
      RootPairing.weylGroup.ofIdx E.rootDatum b ∈ W := by
    obtain ⟨a, rfl⟩ := F.datumIso.val.indexEquiv.surjective b
    obtain ⟨n, hn, hnw⟩ := integralWeylSection_label M a F e t ht hval I
    refine ⟨n, ⟨integralWeylSection M a, ?_⟩, hnw⟩
    change integralWeylSectionFibre M a ≫ e.hom.hom.hom =
      n ≫ I.normalizer.inclusion.hom.hom
    exact hn.symm
  have hw : w ∈ W :=
    RootPairing.weylGroup.induction E.rootDatum
      (pred := fun x hx ↦ (⟨x, hx⟩ : E.rootDatum.weylGroup) ∈ W)
      hgen (W.one_mem) (fun _ _ _ _ hx hy ↦ W.mul_mem hx hy) w.property
  obtain ⟨n, ⟨g, hg⟩, hlabel⟩ := hw
  have hrep := normalizer_isRepresentative I n
  rw [hlabel] at hrep
  refine ⟨n, g, hrep, ?_⟩
  change j n = lift g
  exact hg.symm

end WeylFibre

section IntegralProductCharts

open Specs.IntegralSemisimpleModel (AdditiveLine IntegralScheme product Integers)

private def leftTranslationIso {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    (G : Grp C) (g : 𝟙_ C ⟶ G.X) : G.X ≅ G.X where
  hom := (toUnit G.X ≫ g) * 𝟙 _
  inv := (toUnit G.X ≫ g⁻¹) * 𝟙 _
  hom_inv_id := by
    simp only [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, GrpObj.comp_inv]
    group
  inv_hom_id := by
    simp only [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, GrpObj.comp_inv]
    group

section TranslatedCharts

variable {S : Scheme.{u}} {G B : Grp (Over S)} {X : Over S}

/-- Every left translate of an open right-product chart is an open chart
with the same right subgroup factor. -/
theorem rightProductChart_leftTranslation_open (j : B ⟶ G) (s : X ⟶ G.X)
    (hs : IsOpenImmersion (rightProductChart j s).left)
    (g : 𝟙_ (Over S) ⟶ G.X) :
    IsOpenImmersion (rightProductChart j ((toUnit X ≫ g) * s)).left := by
  have h : rightProductChart j ((toUnit X ≫ g) * s) =
      rightProductChart j s ≫ (leftTranslationIso G g).hom := by
    simp only [rightProductChart, leftTranslationIso, MonObj.comp_mul, Category.comp_id,
      comp_toUnit_assoc, mul_assoc]
  rw [h]
  have : IsIso (leftTranslationIso G g).hom.left := (CategoryTheory.Over.forget S).map_isIso (leftTranslationIso G g).hom
  exact inferInstanceAs
    (IsOpenImmersion ((rightProductChart j s).left ≫ (leftTranslationIso G g).hom.left))

/-- A factorization on algebraically closed field points suffices for the
joint covering condition on the translated charts. -/
theorem rightProductCharts_cover_of_geometricFactors (j : B ⟶ G)
    {I : Type u} {X : I → Over S} (s : ∀ i, X i ⟶ G.X)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : ringSpec K ⟶ S)
      (g : CategoryTheory.Over.mk a ⟶ G.X),
      ∃ (i : I) (p : CategoryTheory.Over.mk a ⟶ X i ⊗ B.X), p ≫ rightProductChart j (s i) = g) :
    ∀ x : G.X.left, ∃ (i : I) (y : (X i ⊗ B.X).left), (rightProductChart j (s i)).left y = x := by
  intro x
  let k := G.X.left.residueField x
  let K := AlgebraicClosure k
  let a := fieldSpecMap k K ≫ G.X.left.fromSpecResidueField x
  let T := CategoryTheory.Over.mk (a ≫ G.X.hom)
  let g : T ⟶ G.X := CategoryTheory.Over.homMk a
  obtain ⟨i, p, hp⟩ := h K T.hom g
  let z : ringSpec K := IsLocalRing.closedPoint K
  have ha : a z = x := by
    change (fieldSpecMap k K ≫ G.X.left.fromSpecResidueField x) z = x
    rw [Scheme.Hom.comp_apply]
    have hpoint : fieldSpecMap k K z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hpoint]
    exact Scheme.fromSpecResidueField_apply (X := G.X.left) x _
  exact ⟨i, p.left z, (congrArg (fun f : T ⟶ G.X ↦ f.left z) hp).trans ha⟩

end TranslatedCharts

/-- An ordered product of integral additive root coordinates is smooth over
the integers. -/
theorem smoothIntegralLineProduct {I : Type u} (L : AdditiveLine.{u}) (l : List I) :
    Smooth (product (fun _ : I ↦ L.group.X) l).hom := by
  have hL : Smooth L.group.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (Polynomial Integers.{u}))))
    have h : Algebra.Smooth Integers.{u} (Polynomial Integers.{u}) := ⟨inferInstance, inferInstance⟩
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr h)
  induction l with
  | nil =>
    exact inferInstanceAs (Smooth (𝟙 _))
  | cons i l hl =>
    let Y := product (fun _ : I ↦ L.group.X) l
    change Smooth ((L.group.X ⊗ Y).hom)
    rw [CategoryTheory.Over.tensorObj_hom]
    have : Smooth (pullback.fst L.group.X.hom Y.hom) := inferInstance
    exact inferInstanceAs (Smooth (pullback.fst L.group.X.hom Y.hom ≫ L.group.X.hom))

end IntegralProductCharts

section BruhatFactors

open Specs.AbstractPairing (Datum Root)
open Specs.DatumAndWeyl (Identification)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily)
open Specs.BruhatOrbitParametrization (IsRepresentative)

open private lift_of_range from LinearAlgebraicGroups.Flag.BruhatCells

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
/-- The split Bruhat cells put each algebraically closed field point in a
left translate of the negative-root right-product chart. The normalizer
representatives can be chosen with any specified lifting property. -/
theorem bruhatRightChartFactors {k : Type u} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) {T B : ClosedSubgroup G.val}
    (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T) (hB : IsKBorel B)
    (hTB : IsSubgroupOf T B) (U : RootSubgroupFamily T)
    (l : List (Root T)) (hl : Enumerates l (subgroupRoots T B)ᶜ)
    (P : (𝟙_ (SchemeOver k) ⟶ G.val.X) → Prop)
    (hrep : ∀ [_c : IsCommMonObj T.group.X] (D : Datum T) (I : Identification D)
      (w : D.rootDatum.weylGroup), ∃ n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X,
        IsRepresentative I w n ∧ P (n ≫ I.normalizer.inclusion.hom.hom))
    (g : CategoryTheory.Over.mk (fieldSpecMap k k) ⟶ G.val.X) :
    let Y := CategoryTheory.Over.mk (fieldSpecMap k k)
    ∃ (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
      (z : Y ⟶ Specs.OrderedRootProducts.product (fun a ↦ (U a).val.group.X) l)
      (b : Y ⟶ B.group.X), P n ∧
        (toUnit Y ≫ n) * (z ≫ Specs.OrderedRootProducts.rootProduct U l) *
          (b ≫ B.inclusion.hom.hom) = g := by
  let Y := CategoryTheory.Over.mk (fieldSpecMap k k)
  obtain ⟨hc, D, I, _, Bneg, _, Rneg, _, _, hBn, hTBn, hroot, _, hRneg, _, _, _, _, ⟨Q⟩, hQ⟩ :=
    LinearAlgebraicGroups.Flag.BruhatCells.bruhatCells G hG T B hT hmax hB hTB
  let := hc
  choose n hn hPn using hrep D I
  obtain ⟨act, _, hc⟩ := hQ Q
  obtain ⟨A, C, hC, _, hcover, _⟩ := hc n hn
  have hx : g.left (IsLocalRing.closedPoint k) ∈
      ⋃ w, Set.range (C w).doubleOrbitInclusion.left := hcover ▸ Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
  let q := C w
  let nw := n w ≫ I.normalizer.inclusion.hom.hom
  have hqi : IsImmersion q.doubleOrbitInclusion.left := q.doubleOrbitImmersion
  obtain ⟨a, ha⟩ := lift_of_range (K := k) q.doubleOrbitInclusion g hw
  let v := a ≫ q.doubleOrbitIso.inv
  let d := v ≫ fst (A w).group.X B.group.X
  let b := v ≫ snd (A w).group.X B.group.X
  let dG := d ≫ (A w).inclusion.hom.hom
  let nY := toUnit Y ≫ nw
  have hfac : dG * nY * (b ≫ B.inclusion.hom.hom) = g := by
    calc
      _ = v ≫ (q.doubleOrbitIso.hom ≫ q.doubleOrbitInclusion) := by
        rw [q.doubleOrbitIso_eq]
        simp only [MonObj.comp_mul, comp_toUnit_assoc, Category.assoc, dG, nY, d, b]
        rfl
      _ = g := by
        rw [show v = a ≫ q.doubleOrbitIso.inv from rfl,
          Category.assoc, Iso.inv_hom_id_assoc, ha]
  obtain ⟨r, hr⟩ := (((hC w).1 Y dG).mp ⟨d, rfl⟩).2
  obtain ⟨R, hR, hprod⟩ := RootData.OrderedRootProducts.borelRadicalProduct G hG T hT hmax Bneg hBn hTBn
  obtain ⟨i, hi⟩ := hR.2.2 Rneg hRneg.1 hRneg.2.1
  obtain ⟨e, he⟩ := hprod U l (hroot.symm ▸ hl)
  let z := r ≫ i.hom.hom ≫ e.inv
  have hpath : z ≫ Specs.OrderedRootProducts.rootProduct U l =
      Specs.BruhatOrbitParametrization.conjugatePoint nw⁻¹ dG := by
    have h₁ := congrArg (fun f : Rneg.group ⟶ Bneg.group ↦ f.hom.hom) hi
    change i.hom.hom ≫ R.inclusion.hom.hom = Rneg.inclusion.hom.hom at h₁
    have h₂ : r ≫ Rneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom = Specs.BruhatOrbitParametrization.conjugatePoint nw⁻¹ dG :=
      hr
    rw [← he, show z = r ≫ i.hom.hom ≫ e.inv from rfl, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc, ← Category.assoc i.hom.hom, h₁]
    exact h₂
  refine ⟨nw, z, b, hPn w, ?_⟩
  rw [hpath, ← hfac]
  change nY * ((toUnit Y ≫ nw⁻¹) * dG * (toUnit Y ≫ nw⁻¹)⁻¹) *
    (b ≫ B.inclusion.hom.hom) = _
  rw [GrpObj.comp_inv, inv_inv]
  change nY * (nY⁻¹ * dG * nY) * (b ≫ B.inclusion.hom.hom) = _
  group

end BruhatFactors

section SplitCover

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.AdjointRepresentation (GroupPoints)
open Specs.OrderedRootProducts (Enumerates)
open Specs.BorelsAndChambers (positiveRoots)
open private forgetFibrePoint_surjective from LinearAlgebraicGroups.Classification.IntegralRealization

section RationalSections

variable {k : Type u} [Field k]
attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem forgetScalarExtendedSection (G : IntegralGroup.{u})
    (w : 𝟙_ (Over Base.{u}) ⟶ G.X) :
    let R := CommAlgCat.of k k
    let Y := (testSpec k).obj (op R)
    let F := CategoryTheory.Over.pullback (integralSpecMap k)
    let r : Y ⟶ ((fibre k).obj G).X := toUnit Y ≫ Functor.LaxMonoidal.ε F ≫ F.map w
    forgetFibrePoint G R r = toUnit (integralSpec.obj (op (CommAlgCat.of Integers.{u} R))) ≫ w := by
  dsimp only
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (op R)
  let β := integralSpecMap k
  let F := CategoryTheory.Over.pullback β
  let ε := Functor.LaxMonoidal.ε F
  have hε : ε.left ≫ pullback.fst (𝟙_ (Over Base.{u})).hom β = β := by
    have h := pullback.condition (f := (𝟙_ (Over Base.{u})).hom) (g := β)
    change pullback.fst (𝟙 Base.{u}) β ≫ 𝟙 _ = pullback.snd (𝟙 Base.{u}) β ≫ β at h
    rw [Category.comp_id] at h
    have he := CategoryTheory.Over.w ε
    change ε.left ≫ pullback.snd (𝟙 Base.{u}) β = 𝟙 _ at he
    change ε.left ≫ pullback.fst (𝟙 Base.{u}) β = β
    rw [h, ← Category.assoc, he, Category.id_comp]
  have hY : (toUnit Y).left = 𝟙 (ringSpec k) := by
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    exact Scheme.Spec.map_id _
  apply CategoryTheory.Over.OverMorphism.ext
  change ((toUnit Y).left ≫ ε.left ≫ (F.map w).left) ≫ pullback.fst G.X.hom β =
    (toUnit (integralSpec.obj (op (CommAlgCat.of Integers.{u} R)))).left ≫ w.left
  have hw := (pullbackMapSquare β w).w
  change (F.map w).left ≫ pullback.fst G.X.hom β =
    pullback.fst (𝟙_ (Over Base.{u})).hom β ≫ w.left at hw
  rw [Category.assoc, Category.assoc, hw, ← Category.assoc ε.left, hε, hY]
  change 𝟙 (ringSpec k) ≫ β ≫ w.left = β ≫ w.left
  exact Category.id_comp _

end RationalSections

section IntegralRightCharts

variable {D : BasedRootDatum.{u}} (M : Model D)

private def integralTranslatedRootChart (negative : List D.I)
    (w : 𝟙_ (Over Base.{u}) ⟶ M.group.X) :
    product (fun _ : D.I ↦ M.line.group.X) negative ⟶ M.group.X :=
  (toUnit _ ≫ w) * rootProduct M.line M.root negative

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 950000 in
/-- The field Bruhat factorization with integral Weyl representatives covers
the split integral group by translates of the negative-root chart. -/
theorem integralRightProductCharts_cover (y : D.Y)
    (hy : ∀ i, D.datum.toLinearMap (D.datum.root i) y ≠ 0)
    (hpos : ∀ i, D.base.IsPos i ↔ 0 < D.datum.toLinearMap (D.datum.root i) y)
    {H : IntegralGroup.{u}} (j : H ⟶ M.group)
    (hj : IsClosedImmersion j.hom.hom.left)
    (hpoints : ∀ (R : IntegralAlgebra.{u}) (g : IntegralPoints M.group R),
      HasPolynomialOrbit (integralUnitCocharacter M y) g ↔
        ∃ p : IntegralPoints H R, p ≫ j.hom.hom = g)
    (negative : List D.I) (hneg : Enumerates negative {i | ¬ D.base.IsPos i}) :
    let X := product (fun _ : D.I ↦ M.line.group.X) negative
    ∀ x : M.group.X.left, ∃ (w : 𝟙_ (Over Base.{u}) ⟶ M.group.X) (z : (X ⊗ H.X).left),
      (rightProductChart j (integralTranslatedRootChart M negative w)).left z = x := by
  apply rightProductCharts_cover_of_geometricFactors
  intro k _ _ a g
  have ha := integralBaseMap_eq a
  subst a
  let := integerAlgebra k
  let R := CommAlgCat.of k k
  let A := CommAlgCat.of Integers.{u} R
  let Y := (testSpec k).obj (op R)
  let X₀ := integralSpec.obj (op A)
  let g₀ : IntegralPoints M.group A := g
  obtain ⟨gF, hg⟩ := forgetFibrePoint_surjective M.group R g₀
  obtain ⟨L, F, e, t, z, ht, _, hval, hz⟩ := M.fieldFibre k
  let P := F.pinned.pair
  let c := markedCocharacter F y
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition P.G (c ≫ P.T.inclusion)
  obtain ⟨_, hB, hTB, hRoots, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel P.G P.reductive P.T P.split P.maximal c
      (markedCocharacter_regular F y hy) E
  obtain ⟨u, hu⟩ := attractingSubgroupFibreIso M y j hj hpoints F e
    (fieldCocharacter_of_marking M y F e t ht hval) E
  let φ := F.datumIso.val.indexEquiv
  have hl : Enumerates (negative.map φ) (Specs.BorelsAndChambers.subgroupRoots P.T E.parabolic)ᶜ := by
    refine ⟨hneg.1.map φ.injective, ?_⟩
    intro α
    obtain ⟨i, rfl⟩ := φ.surjective α
    rw [List.mem_map, hRoots]
    change (∃ i' ∈ negative, φ i' = φ i) ↔ ¬ 0 <
      Specs.CharacterPairing.pairing P.T.group (φ i).val c
    rw [markedRootWeight, ← hpos]
    exact ⟨fun ⟨i', hi', h⟩ ↦ (hneg.2 i).mp (φ.injective h ▸ hi'),
      fun hi ↦ ⟨i, (hneg.2 i).mpr hi, rfl⟩⟩
  obtain ⟨n, p, b, ⟨w, hw⟩, h⟩ := bruhatRightChartFactors P.G P.reductive P.split
    P.maximal hB hTB F.pinned.roots (negative.map φ) hl (Set.range (integralSectionsToFibre M F e))
    (fun D I w ↦ by
      obtain ⟨n, g, hn, hg'⟩ := integralSectionsRepresentWeyl M F e t ht hval I w
      exact ⟨n, hn, g, hg'.symm⟩) (gF ≫ e.hom.hom.hom)
  obtain ⟨r, hr⟩ := integralRootProductPoint M F e z hz R negative p
  let bF : GroupPoints ((fibre k).obj H) R := b ≫ u.inv.hom.hom
  let b₀ := forgetFibrePoint H R bF
  have heb : u.inv ≫ (fibre k).map j = E.parabolic.inclusion ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, ← hu, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hb : b₀ ≫ j.hom.hom = forgetFibrePoint M.group R
      ((b ≫ E.parabolic.inclusion.hom.hom) ≫ e.inv.hom.hom) := by
    rw [← forgetFibrePoint_map]
    apply congrArg (forgetFibrePoint M.group R)
    have hh := congrArg
      (fun f : E.parabolic.group ⟶ (fibre k).obj M.group ↦ f.hom.hom) heb
    change u.inv.hom.hom ≫ ((fibre k).map j).hom.hom =
      E.parabolic.inclusion.hom.hom ≫ e.inv.hom.hom at hh
    simpa only [bF, Category.assoc] using congrArg (b ≫ ·) hh
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ :=
    congrArg (fun f : (fibre k).obj M.group ⟶ (fibre k).obj M.group ↦ f.hom.hom) e.hom_inv_id
  let ret : GroupPoints ((fibre k).obj M.group) R :=
    toUnit Y ≫ Functor.LaxMonoidal.ε (CategoryTheory.Over.pullback (integralSpecMap k)) ≫
      (CategoryTheory.Over.pullback (integralSpecMap k)).map w
  have hret : (ret ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = ret := by
    rw [Category.assoc, he, Category.comp_id]
  have hn : (toUnit X₀ ≫ w) =
      forgetFibrePoint M.group R ((toUnit Y ≫ n) ≫ e.inv.hom.hom) := by
    rw [← hw]
    have hew : (toUnit Y ≫ (integralSectionsToFibre M F e) w) ≫ e.inv.hom.hom =
        (ret ≫ e.hom.hom.hom) ≫ e.inv.hom.hom := by
      change (toUnit Y ≫ (_ ≫ e.hom.hom.hom)) ≫ _ = (ret ≫ e.hom.hom.hom) ≫ _
      rw [← Category.assoc (toUnit Y)]
    rw [hew, hret]
    exact (forgetScalarExtendedSection M.group w).symm
  let nF : GroupPoints P.G.val R := toUnit Y ≫ n
  let pF : GroupPoints P.G.val R := p ≫ Specs.OrderedRootProducts.rootProduct F.pinned.roots
    (negative.map φ)
  let bG : GroupPoints P.G.val R := b ≫ E.parabolic.inclusion.hom.hom
  have h' : nF * pF * bG = gF ≫ e.hom.hom.hom := h
  have hv := congrArg (fun v : GroupPoints P.G.val R ↦
    forgetFibrePoint M.group R (v ≫ e.inv.hom.hom)) h'
  have : IsMonHom e.inv.hom.hom := e.inv.hom.isMonHom_hom
  have hg' : (gF ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = gF := by
    rw [Category.assoc, he, Category.comp_id]
  rw [MonObj.mul_comp, MonObj.mul_comp, forgetFibrePoint_mul, forgetFibrePoint_mul, hg', hg] at hv
  change forgetFibrePoint M.group R ((toUnit Y ≫ n) ≫ e.inv.hom.hom) *
      forgetFibrePoint M.group R (pF ≫ e.inv.hom.hom) *
      forgetFibrePoint M.group R ((b ≫ E.parabolic.inclusion.hom.hom) ≫ e.inv.hom.hom) = g₀ at hv
  rw [← hn, ← hb] at hv
  have hr' : r ≫ rootProduct M.line M.root negative =
      forgetFibrePoint M.group R (pF ≫ e.inv.hom.hom) := hr
  rw [← hr'] at hv
  refine ⟨w, lift r b₀, ?_⟩
  rw [lift_comp_rightProductChart, integralTranslatedRootChart, MonObj.comp_mul, comp_toUnit_assoc]
  exact hv

end IntegralRightCharts

end SplitCover

section IntegralBorelCoordinates

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel

attribute [-instance] ULift.module

private theorem productHasFreeIntegralCoordinates {X Y : IntegralScheme.{u}}
    (hX : ∃ C : IntegralAlgebra.{u}, Module.Free Integers.{u} C ∧
      Nonempty (X ≅ integralSpec.obj (op C)))
    (hY : ∃ C : IntegralAlgebra.{u}, Module.Free Integers.{u} C ∧
      Nonempty (Y ≅ integralSpec.obj (op C))) :
    ∃ C : IntegralAlgebra.{u}, Module.Free Integers.{u} C ∧
      Nonempty (X ⊗ Y ≅ integralSpec.obj (op C)) := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hX
  obtain ⟨B, hB, ⟨eB⟩⟩ := hY
  let C := CommAlgCat.of Integers.{u} (A ⊗[Integers.{u}] B)
  have h : ∀ {R : Type u} [CommRing R] (A B : CommAlgCat.{u} R)
      [Module.Free R A] [Module.Free R B], Module.Free R (A ⊗[R] B) := by
    intro R _ A B _ _
    exact Module.Free.tensor (R := R) (S := R)
  refine ⟨C, h A B, ⟨?_⟩⟩
  let F := integralSpec.{u}
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of Integers.{u})
  exact (tensorIso eA eB) ≪≫ (asIso (Functor.OplaxMonoidal.δ F (op A) (op B))).symm

private theorem lineProductHasFreeIntegralCoordinates {I : Type u} (L : AdditiveLine.{u})
    (l : List I) :
    ∃ C : IntegralAlgebra.{u}, Module.Free Integers.{u} C ∧
      Nonempty (product (fun _ : I ↦ L.group.X) l ≅ integralSpec.obj (op C)) := by
  induction l with
  | nil =>
    exact ⟨CommAlgCat.of Integers.{u} Integers.{u}, inferInstance, ⟨integralSpecUnit⟩⟩
  | cons i l ih =>
    change ∃ C : IntegralAlgebra.{u}, Module.Free Integers.{u} C ∧
      Nonempty (L.group.X ⊗ product (fun _ : I ↦ L.group.X) l ≅ integralSpec.obj (op C))
    apply productHasFreeIntegralCoordinates _ ih
    exact ⟨CommAlgCat.of Integers.{u} (Polynomial Integers.{u}),
      inferInstanceAs (Module.Free Integers.{u} (Polynomial Integers.{u})), ⟨Iso.refl _⟩⟩

/-- The integral Borel in its ordered torus and positive-root coordinates
has an affine coordinate algebra free over the integers. -/
theorem integralBorelHasFreeCoordinates {D : BasedRootDatum.{u}} (L : AdditiveLine.{u})
    (positive : List D.I) {B : IntegralGroup.{u}}
    (e : (splitTorus D).X ⊗ product (fun _ : D.I ↦ L.group.X) positive ≅ B.X) :
    ∃ C : IntegralAlgebra.{u}, Module.Free Integers.{u} C ∧
      Nonempty (B.X ≅ integralSpec.obj (op C)) := by
  let A := MonoidAlgebra Integers.{u} (Multiplicative D.X)
  have hT : ∃ C : IntegralAlgebra.{u}, Module.Free Integers.{u} C ∧
      Nonempty ((splitTorus D).X ≅ integralSpec.obj (op C)) := by
    refine ⟨CommAlgCat.of Integers.{u} A, ?_, ⟨Iso.refl _⟩⟩
    exact Module.Free.of_basis (MonoidAlgebra.basis (Multiplicative D.X) Integers.{u})
  obtain ⟨C, hC, ⟨f⟩⟩ := productHasFreeIntegralCoordinates hT
    (lineProductHasFreeIntegralCoordinates L positive)
  exact ⟨C, hC, ⟨e.symm ≪≫ f⟩⟩

end IntegralBorelCoordinates

section IntegralFlag

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.OrderedRootProducts (Enumerates)
open private rootOrderings_exist from LinearAlgebraicGroups.Classification.IntegralRealization

attribute [-instance] ULift.module

set_option backward.isDefEq.respectTransparency false in
/-- The integral right quotient with the polynomial-orbit description of its standard Borel. -/
private theorem integralBorelQuotientWithCocharacter {D : BasedRootDatum.{u}} (M : Model D) :
    ∃ (B : IntegralGroup.{u}) (j : B ⟶ M.group)
      (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
      (P : IntegralScheme.{u}) (p : M.group.X ⟶ P) (U : Family M.group P),
      HasBorelFibres j ∧ Smooth P.hom ∧ Smooth p.left ∧ Surjective p.left ∧ QuasiCompact p.left ∧
      (∃ A : IntegralAlgebra.{u}, Module.Free Integers.{u} A ∧
        Nonempty (B.X ≅ integralSpec.obj (op A))) ∧ IsBorelFamily U ∧
      SameFamily (U.pullback p) (conjugateSubgroupFamily j hj hs (𝟙 M.group.X)) ∧
      (∀ (T : IntegralScheme.{u}) (g h : T ⟶ M.group.X),
        g ≫ p = h ≫ p ↔ ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h) ∧
      ∃ c : UnitCocharacter M.group,
        ∀ (E : Type u) [CommRing E] [Algebra Integers.{u} E]
          (x : coordSpec Integers.{u} E ⟶ M.group.X),
          HasPolynomialOrbit c x ↔ ∃ b : coordSpec Integers.{u} E ⟶ B.X, b ≫ j.hom.hom = x := by
  obtain ⟨y, hy, hpos⟩ := existsRegularPositiveCocharacter D
  obtain ⟨B, j, hj, hs, hpoints, hB, hcell⟩ := integralBorelBigCellOfCocharacter M y hy hpos
  obtain ⟨negative, positive, hnegative, hpositive⟩ := rootOrderings_exist D
  let X := product (fun _ : D.I ↦ M.line.group.X) negative
  let s : (𝟙_ (Over Base.{u}) ⟶ M.group.X) → (X ⟶ M.group.X) :=
    integralTranslatedRootChart M negative
  have hX : Smooth X.hom := smoothIntegralLineProduct M.line negative
  obtain ⟨e, _, hopen⟩ := hcell negative positive hnegative hpositive
  have hFree := integralBorelHasFreeCoordinates M.line positive e
  have htranslated (w : 𝟙_ (Over Base.{u}) ⟶ M.group.X) :
      IsOpenImmersion (rightProductChart j (s w)).left :=
    rightProductChart_leftTranslation_open j (rootProduct M.line M.root negative) hopen w
  have hcover := integralRightProductCharts_cover M y hy hpos j hj hpoints negative hnegative
  have : IsAffine M.group.X.left := M.affine
  have : IsAffineHom M.group.X.hom := inferInstance
  have : LocallyOfFinitePresentation M.group.X.hom := M.locallyOfFinitePresentation
  have : QuasiCompact M.group.X.hom := M.quasiCompact
  obtain ⟨P, p, U, hP, hp, hpSurj, hpQC, hU, hd, hq⟩ :=
    borelFamilyOfRightProductCharts j s hj hs hB (fun _ ↦ hX) htranslated hcover
  exact ⟨B, j, hj, hs, P, p, U, hB, hP, hp, hpSurj, hpQC, hFree, hU, hd, hq, integralUnitCocharacter M y, fun E _ _ x ↦
    hpoints (CommAlgCat.of Integers.{u} E) x⟩

set_option backward.isDefEq.respectTransparency false in
/-- The split integral model has a smooth right quotient by its standard
Borel, carrying a smooth closed family of geometric Borels. -/
theorem integralBorelQuotient {D : BasedRootDatum.{u}} (M : Model D) :
    ∃ (B : IntegralGroup.{u}) (j : B ⟶ M.group)
      (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
      (P : IntegralScheme.{u}) (p : M.group.X ⟶ P) (U : Family M.group P),
      HasBorelFibres j ∧ Smooth P.hom ∧ Smooth p.left ∧ Surjective p.left ∧ QuasiCompact p.left ∧
      (∃ A : IntegralAlgebra.{u}, Module.Free Integers.{u} A ∧
        Nonempty (B.X ≅ integralSpec.obj (op A))) ∧ IsBorelFamily U ∧
      SameFamily (U.pullback p) (conjugateSubgroupFamily j hj hs (𝟙 M.group.X)) ∧
      ∀ (T : IntegralScheme.{u}) (g h : T ⟶ M.group.X),
        g ≫ p = h ≫ p ↔ ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h := by
  obtain ⟨B, j, hj, hs, P, p, U, hB, hP, hp, hsurj, hqc, hfree, hU, hUp, hq, _⟩ :=
    integralBorelQuotientWithCocharacter M
  exact ⟨B, j, hj, hs, P, p, U, hB, hP, hp, hsurj, hqc, hfree, hU, hUp, hq⟩

end IntegralFlag

section SplittingCoverParameter

variable {S S' : Scheme.{u}} {G : Grp (Over S)} {G' : Grp (Over S')}

/-- Pull a Borel family to a changed base and identify its ambient group via
the given isomorphism. -/
def scalarExtendedFamily (a : S' ⟶ S) (e : G' ≅ (changeBase a).obj G)
    {P : Over S} (U : Family G P) : Family G' ((Over.pullback a).obj P) := by
  let Q := (Over.pullback a).obj P
  let v := (Over.mapPullbackAdj a).counit.app P
  let U' := U.pullback v
  let e' := (changeBase Q.hom).mapIso e ≪≫ (changeBaseComp Q.hom a).symm.app G
  have he : IsIso e'.inv.hom.hom.left :=
    (Grp.forget (Over Q.left) ⋙ Over.forget _).map_isIso e'.inv
  have hU' : IsClosedImmersion U'.inclusion.hom.hom.left := U'.closed
  exact ⟨U'.group, U'.inclusion ≫ e'.inv, IsClosedImmersion.comp _ _, U'.smooth⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
/-- Scalar extension preserves the geometric Borel property of the actual
closed subgroup family. -/
theorem scalarExtendedFamily_isBorel [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] (a : S' ⟶ S) (e : G' ≅ (changeBase a).obj G)
    {P : Over S} (U : Family G P) (hU : IsBorelFamily U) :
    IsBorelFamily (scalarExtendedFamily a e U) := by
  let Q := (Over.pullback a).obj P
  let v := (Over.mapPullbackAdj a).counit.app P
  let e' := (changeBase Q.hom).mapIso e ≪≫ (changeBaseComp Q.hom a).symm.app G
  have hU' : HasBorelFibres (U.pullback v).inclusion := isBorelFamily_pullback U hU v
  exact hasBorelFibres_comp_iso e'.symm hU'

/-- The split chart construction gives a smooth scheme with a Borel family
of the actual model on its specified finite étale splitting cover. -/
theorem borelParameterOnSplittingCover {R : Type u} [CommRing R]
    {G : Grp (Over (ringSpec R))} (hG : HasSplitModel G) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (_ : Module.Finite R A) (_ : Module.FaithfullyFlat R A) (_ : Algebra.Etale R A)
      (P : Over (ringSpec A)) (U : Family ((changeBase (algebraSpecMap R A)).obj G) P),
      Smooth P.hom ∧ IsBorelFamily U := by
  obtain ⟨A, _, _, hf, hff, het, D, _, M, ⟨e⟩⟩ := hG
  obtain ⟨B, j, hj, hs, P, p, U, hB, hP, hp, hsurj, hqc, hfree, hU, hUn, hq⟩ :=
    integralBorelQuotient M
  let a := integralSpecMap A
  have : IsAffine M.group.X.left := M.affine
  have : IsAffineHom M.group.X.hom := inferInstance
  have : LocallyOfFinitePresentation M.group.X.hom := M.locallyOfFinitePresentation
  have : QuasiCompact M.group.X.hom := M.quasiCompact
  have hP' : Smooth ((Over.pullback a).obj P).hom :=
    inferInstanceAs (Smooth (pullback.snd P.hom a))
  exact ⟨A, _, _, hf, hff, het, (Over.pullback a).obj P, scalarExtendedFamily a e U,
    hP', scalarExtendedFamily_isBorel a e U hU⟩

end SplittingCoverParameter

open private laurentConstantModIdeal laurentScale coeff_laurentScale laurentScale_mem from
  LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

open LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter (laurentAverage)

section LaurentAverage

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

private abbrev constantReductionAlgebra (R : Type u) [CommRing R] [Algebra R B] (I : Ideal B) :=
  (laurentConstantModIdeal I).restrictScalars R

set_option backward.isDefEq.respectTransparency false in
/-- The Laurent family of points with constant square-zero reduction can be
averaged by taking the constant coefficient of its affine coordinates. The
averaged point has the prescribed reduction. -/
theorem liftPointToConstantReduction {G : Grp (CategoryTheory.Over (ringSpec R))}
    (e : coordSpec R A ≅ G.X) (I : Ideal B) (hI : I ^ 2 = ⊥)
    (g : coordSpec R (LaurentPolynomial B) ⟶ G.X) (g₀ : coordSpec R (B ⧸ I) ⟶ G.X)
    (hg : coordSpecMap (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I)) ≫ g =
      coordSpecMap (laurentConstants R (B ⧸ I)) ≫ g₀) :
    ∃ p : coordSpec R (constantReductionAlgebra R I) ⟶ G.X,
      coordSpecMap (constantReductionAlgebra R I).val ≫ p = g ∧
      coordSpecMap (Ideal.Quotient.mkₐ R I) ≫
        coordSpecMap ((laurentAverage I hI).restrictScalars R) ≫ p = g₀ := by
  let q := Ideal.Quotient.mkₐ R I
  let W := constantReductionAlgebra R I
  let f := pointCoordinates e g
  let f₀ := pointCoordinates e g₀
  have he : (AddMonoidAlgebra.mapAlgHom ℤ q).comp f = (laurentConstants R (B ⧸ I)).comp f₀ := by
    rw [← pointCoordinates_natural, ← pointCoordinates_natural, hg]
  have hc (a : A) (n : ℤ) : q ((f a).coeff n) = (LaurentPolynomial.C (f₀ a)).coeff n := by
    have ht := congrArg (fun s : LaurentPolynomial (B ⧸ I) ↦ s.coeff n) (DFunLike.congr_fun he a)
    simp only [AlgHom.comp_apply, AddMonoidAlgebra.coeff_mapAlgHom] at ht
    change q ((f a).coeff n) = (LaurentPolynomial.C (f₀ a)).coeff n at ht
    exact ht
  let F : A →ₐ[R] W := f.codRestrict W (fun a n hn ↦ by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((f a).coeff n) = 0
    rw [hc, LaurentPolynomial.C_apply, ite_eq_right hn])
  let p := (pointCoordinates e).symm F
  let avg : W →ₐ[R] B := (laurentAverage I hI).restrictScalars R
  refine ⟨p, ?_, ?_⟩
  · apply (pointCoordinates e).injective
    rw [pointCoordinates_natural, Equiv.apply_symm_apply]
    exact rfl
  · apply (pointCoordinates e).injective
    change (pointCoordinates e) (coordSpecMap q ≫ coordSpecMap avg ≫ p) = f₀
    rw [pointCoordinates_natural e q, pointCoordinates_natural e avg]
    have hF : pointCoordinates e p = F := (pointCoordinates e).apply_symm_apply F
    rw [hF]
    apply AlgHom.ext
    intro a
    change q ((f a).coeff 0) = f₀ a
    simpa only [LaurentPolynomial.C_apply, ite_true] using hc a 0

private def scaleLaurent (f : B →ₐ[R] C) (t : Cˣ) : LaurentPolynomial B →ₐ[R] LaurentPolynomial C where
  toRingHom := laurentScale f.toRingHom t
  commutes' r := by
    change laurentScale f.toRingHom t (LaurentPolynomial.C (algebraMap R B r)) =
      LaurentPolynomial.C (algebraMap R C r)
    rw [laurentScale, LaurentPolynomial.eval₂_C, RingHom.comp_apply]
    exact congrArg LaurentPolynomial.C (f.commutes r)

/-- Scaling the Laurent variable by a unit preserves the constant
coefficient after any change of scalars carrying one ideal into the other. -/
def scaleConstantReduction (I : Ideal B) (J : Ideal C) (f : B →ₐ[R] C)
    (hf : I ≤ J.comap f.toRingHom) (t : Cˣ) :
    constantReductionAlgebra R I →ₐ[R] constantReductionAlgebra R J := by
  exact ((scaleLaurent f t).comp (constantReductionAlgebra R I).val).codRestrict
    (constantReductionAlgebra R J)
    (fun x ↦ laurentScale_mem f.toRingHom t I J hf x.property)

/-- The constant coefficient on the subalgebra commutes with the chosen
change of scalars and with Laurent-variable scaling. -/
theorem laurentAverage_comp_scaleConstantReduction (I : Ideal B) (J : Ideal C)
    (hI : I ^ 2 = ⊥) (hJ : J ^ 2 = ⊥) (f : B →ₐ[R] C) (hf : I ≤ J.comap f.toRingHom) (t : Cˣ) :
    ((laurentAverage J hJ).restrictScalars R).comp (scaleConstantReduction I J f hf t) =
      f.comp ((laurentAverage I hI).restrictScalars R) := by
  apply AlgHom.ext
  intro p
  change (laurentScale f.toRingHom t p.val).coeff 0 = f (p.val.coeff 0)
  rw [coeff_laurentScale, zpow_zero, Units.val_one, mul_one]
  rfl

section AverageGroupPoints

variable {G : Grp (CategoryTheory.Over (ringSpec R))}

private theorem mapAffinePoints_injective (e : coordSpec R A ≅ G.X) (f : B →ₐ[R] C)
    (hf : Function.Injective f) :
    Function.Injective (mapAffinePoints G (CommAlgCat.ofHom f)) := by
  intro g h hgh
  apply (pointCoordinates e).injective
  have he := congrArg (pointCoordinates e) hgh
  change pointCoordinates e (coordSpecMap f ≫ g) = pointCoordinates e (coordSpecMap f ≫ h) at he
  rw [pointCoordinates_natural, pointCoordinates_natural] at he
  exact AlgHom.ext fun a ↦ hf (DFunLike.congr_fun he a)

private abbrev inclusionOfConstantReduction (I : Ideal B) := (constantReductionAlgebra R I).val

private def constantPointMap (I : Ideal B) : B →ₐ[R] constantReductionAlgebra R I :=
  (laurentConstants R B).codRestrict (constantReductionAlgebra R I) (fun b n hn ↦ by
    change (LaurentPolynomial.C b).coeff n ∈ I
    rw [LaurentPolynomial.C_apply, ite_eq_right hn]
    exact I.zero_mem)

private lemma constantPointMap_val (I : Ideal B) :
    (inclusionOfConstantReduction (R := R) I).comp (constantPointMap (R := R) I) =
      laurentConstants R B := rfl

private lemma laurentAverage_comp_constantPointMap (I : Ideal B) (hI : I ^ 2 = ⊥) :
    ((laurentAverage I hI).restrictScalars R).comp (constantPointMap (R := R) I) = AlgHom.id R B := by
  ext b
  change (LaurentPolynomial.C b).coeff 0 = b
  simp [LaurentPolynomial.C_apply]

/-- The average on points with coordinates in the constant-reduction algebra
is a group homomorphism. -/
def averageLaurentPoints (G : Grp (CategoryTheory.Over (ringSpec R)))
    (I : Ideal B) (hI : I ^ 2 = ⊥) :
    affinePoints G (CommAlgCat.of R (constantReductionAlgebra R I)) →*
      affinePoints G (CommAlgCat.of R B) :=
  mapAffinePoints G (CommAlgCat.ofHom ((laurentAverage I hI).restrictScalars R))

set_option backward.isDefEq.respectTransparency false in
/-- Averaging a constant point recovers the original point. -/
theorem averageLaurentPoints_const (I : Ideal B) (hI : I ^ 2 = ⊥)
    (g : affinePoints G (CommAlgCat.of R B)) :
    averageLaurentPoints G I hI (mapAffinePoints G (CommAlgCat.ofHom (constantPointMap (R := R) I)) g) = g := by
  change coordSpecMap ((laurentAverage I hI).restrictScalars R) ≫
    coordSpecMap (constantPointMap (R := R) I) ≫ g = g
  rw [← Category.assoc, ← coordSpecMap_comp, laurentAverage_comp_constantPointMap]
  have hid : coordSpecMap (AlgHom.id R B) = 𝟙 _ :=
    CategoryTheory.Functor.map_id (algSpec (CommRingCat.of R)) _
  rw [hid, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Point averaging is compatible with scaling the variable and changing the
base algebra. -/
theorem averageLaurentPoints_scale (I : Ideal B) (J : Ideal C) (hI : I ^ 2 = ⊥)
    (hJ : J ^ 2 = ⊥) (f : B →ₐ[R] C) (hf : I ≤ J.comap f.toRingHom) (t : Cˣ)
    (g : affinePoints G (CommAlgCat.of R (constantReductionAlgebra R I))) :
    averageLaurentPoints G J hJ
      (mapAffinePoints G (CommAlgCat.ofHom (scaleConstantReduction I J f hf t)) g) =
      mapAffinePoints G (CommAlgCat.ofHom f) (averageLaurentPoints G I hI g) := by
  change coordSpecMap ((laurentAverage J hJ).restrictScalars R) ≫
    coordSpecMap (scaleConstantReduction I J f hf t) ≫ g =
      coordSpecMap f ≫ coordSpecMap ((laurentAverage I hI).restrictScalars R) ≫ g
  rw [← Category.assoc, ← Category.assoc, ← coordSpecMap_comp, ← coordSpecMap_comp,
    laurentAverage_comp_scaleConstantReduction]

end AverageGroupPoints

section CocharacterDefect

variable {G : Grp (CategoryTheory.Over (ringSpec R))}

/-- A natural family of points on the punctured line, before imposing the
multiplication law. -/
structure UnitPointMap (G : Grp (CategoryTheory.Over (ringSpec R))) where
  point : (B : CommAlgCat.{u} R) → Bˣ → affinePoints G B
  natural : ∀ {B C : CommAlgCat.{u} R} (f : B ⟶ C) (t : Bˣ),
    mapAffinePoints G f (point B t) = point C (Units.map f.hom.toMonoidHom t)

private def UnitPointMap.defect (l : UnitPointMap G) (B : CommAlgCat.{u} R) (s t : Bˣ) :
    affinePoints G B := l.point B s * l.point B t * (l.point B (s * t))⁻¹

private theorem UnitPointMap.defect_natural (l : UnitPointMap G)
    {B C : CommAlgCat.{u} R} (f : B ⟶ C) (s t : Bˣ) :
    mapAffinePoints G f (l.defect B s t) =
      l.defect C (Units.map f.hom.toMonoidHom s) (Units.map f.hom.toMonoidHom t) := by
  simp only [UnitPointMap.defect, map_mul, map_inv, l.natural]

private theorem UnitPointMap.defect_cocycle (l : UnitPointMap G)
    (B : CommAlgCat.{u} R) (s t u : Bˣ) :
    l.defect B s t * l.defect B (s * t) u =
      l.point B s * l.defect B t u * (l.point B s)⁻¹ * l.defect B s (t * u) := by
  simp only [UnitPointMap.defect, mul_assoc s t u]
  group

private abbrev mapAffinePointAlong (G : Grp (CategoryTheory.Over (ringSpec R)))
    (f : B →ₐ[R] C) : affinePoints G (CommAlgCat.of R B) →* affinePoints G (CommAlgCat.of R C) :=
  mapAffinePoints G (CommAlgCat.ofHom f)

private theorem mapAffinePointAlong_comp {D : Type u} [CommRing D] [Algebra R D]
    (f : B →ₐ[R] C) (g : C →ₐ[R] D) (x : affinePoints G (CommAlgCat.of R B)) :
    mapAffinePointAlong G (g.comp f) x = mapAffinePointAlong G g (mapAffinePointAlong G f x) := by
  change coordSpecMap (g.comp f) ≫ x = coordSpecMap g ≫ coordSpecMap f ≫ x
  rw [coordSpecMap_comp, Category.assoc]

private theorem scaleLaurent_constants (f : B →ₐ[R] C) (t : Cˣ) :
    (scaleLaurent f t).comp (laurentConstants R B) = (laurentConstants R C).comp f := by
  ext b : 1
  change laurentScale f.toRingHom t (LaurentPolynomial.C b) = LaurentPolynomial.C (f b)
  rw [laurentScale, LaurentPolynomial.eval₂_C]
  rfl

private theorem scaleLaurent_var (f : B →ₐ[R] C) (t : Cˣ) :
    Units.map (scaleLaurent f t).toMonoidHom (laurentVariable B 1) =
      Units.map (laurentConstants R C).toMonoidHom t * laurentVariable C 1 := by
  apply Units.ext
  change laurentScale f.toRingHom t (LaurentPolynomial.T 1) = _
  rw [laurentScale, LaurentPolynomial.eval₂_T, zpow_one]
  rfl

private theorem scaleReduction_val (I : Ideal B) (J : Ideal C)
    (f : B →ₐ[R] C) (hf : I ≤ J.comap f.toRingHom) (t : Cˣ) :
    (inclusionOfConstantReduction (R := R) J).comp (scaleConstantReduction I J f hf t) =
      (scaleLaurent f t).comp (inclusionOfConstantReduction (R := R) I) := rfl

variable (l : UnitPointMap G) (I : Ideal R)

private abbrev scalarIdeal (B : Type u) [CommRing B] [Algebra R B] := I.map (algebraMap R B)

private theorem scalarIdeal_squareZero (hI : I ^ 2 = ⊥) : scalarIdeal I B ^ 2 = ⊥ := by
  rw [scalarIdeal, ← Ideal.map_pow, hI, Ideal.map_bot]

private theorem scalarIdeal_map_le (f : B →ₐ[R] C) : scalarIdeal I B ≤
    (scalarIdeal I C).comap f.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change f (algebraMap R B r) ∈ scalarIdeal I C
  rw [f.commutes]
  exact Ideal.mem_map_of_mem _ hr

private abbrev parameterPoint (l : UnitPointMap G) (s : Bˣ) :=
  l.defect (CommAlgCat.of R (LaurentPolynomial B))
    (Units.map (laurentConstants R B).toMonoidHom s) (laurentVariable B 1)

set_option backward.isDefEq.respectTransparency false in
private theorem parameterPoint_scale (l : UnitPointMap G) (f : B →ₐ[R] C) (s : Bˣ) (t : Cˣ) :
    mapAffinePointAlong G (scaleLaurent f t) (parameterPoint l s) =
      l.defect (CommAlgCat.of R (LaurentPolynomial C))
        (Units.map (laurentConstants R C).toMonoidHom (Units.map f.toMonoidHom s))
        (Units.map (laurentConstants R C).toMonoidHom t * laurentVariable C 1) := by
  let a := Units.map (laurentConstants R B).toMonoidHom s
  have hs : Units.map (scaleLaurent f t).toMonoidHom a =
      Units.map (laurentConstants R C).toMonoidHom (Units.map f.toMonoidHom s) := by
    apply Units.ext
    exact DFunLike.congr_fun (scaleLaurent_constants f t) s.val
  exact (l.defect_natural (CommAlgCat.ofHom (scaleLaurent f t)) a
    (laurentVariable B 1)).trans
      (congrArg₂ (l.defect (CommAlgCat.of R (LaurentPolynomial C))) hs (scaleLaurent_var f t))

/-- Multiplicativity on all test algebras on which the base ideal vanishes. -/
def UnitPointMap.IsMultiplicativeModulo (l : UnitPointMap G) (I : Ideal R) : Prop :=
  ∀ (B : CommAlgCat.{u} R), I ≤ RingHom.ker (algebraMap R B) → ∀ s t : Bˣ,
    l.point B (s * t) = l.point B s * l.point B t

variable (e : coordSpec R A ≅ G.X) (hI : I ^ 2 = ⊥) (hl : l.IsMultiplicativeModulo I)

private abbrev scalarReduction : B →ₐ[R] (B ⧸ scalarIdeal I B) := Ideal.Quotient.mkₐ R _

include hl in
set_option backward.isDefEq.respectTransparency false in
private theorem parameterPoint_reduces (s : Bˣ) :
    mapAffinePointAlong G (AddMonoidAlgebra.mapAlgHom ℤ (scalarReduction I (B := B)))
      (parameterPoint l s) = 1 := by
  let C := LaurentPolynomial (B ⧸ scalarIdeal I B)
  have h : I ≤ RingHom.ker (algebraMap R C) := by
    intro r hr
    change algebraMap R C r = 0
    rw [IsScalarTower.algebraMap_apply R (B ⧸ scalarIdeal I B)]
    change LaurentPolynomial.C (Ideal.Quotient.mk (scalarIdeal I B) (algebraMap R B r)) = 0
    have hr' := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (algebraMap R B) hr)
    rw [hr', map_zero]
  have he := l.defect_natural
    (CommAlgCat.ofHom (AddMonoidAlgebra.mapAlgHom ℤ (scalarReduction I (B := B))))
    (Units.map (laurentConstants R B).toMonoidHom s) (laurentVariable B 1)
  exact he.trans (by rw [UnitPointMap.defect, hl (CommAlgCat.of R C) h, mul_inv_cancel])

include e hl in
private theorem existsParameterPointLift (s : Bˣ) :
    ∃ v : affinePoints G (CommAlgCat.of R (constantReductionAlgebra R (scalarIdeal I B))),
      mapAffinePointAlong G (inclusionOfConstantReduction (R := R) (scalarIdeal I B)) v =
        parameterPoint l s ∧
      mapAffinePointAlong G (scalarReduction I (B := B))
        (averageLaurentPoints G (scalarIdeal I B) (scalarIdeal_squareZero I hI) v) = 1 := by
  have h := parameterPoint_reduces l I hl s
  change coordSpecMap (AddMonoidAlgebra.mapAlgHom ℤ (scalarReduction I (B := B))) ≫
    parameterPoint l s = 1 at h
  exact liftPointToConstantReduction e _ (scalarIdeal_squareZero I hI) (parameterPoint l s) 1
    (h.trans (MonObj.comp_one _).symm)

private def parameterPointLift (s : Bˣ) :
    affinePoints G (CommAlgCat.of R (constantReductionAlgebra R (scalarIdeal I B))) :=
  (existsParameterPointLift l I e hI hl s).choose

private theorem parameterPointLift_val (s : Bˣ) :
    mapAffinePointAlong G (inclusionOfConstantReduction (R := R) (scalarIdeal I B))
      (parameterPointLift l I e hI hl s) = parameterPoint l s :=
  (existsParameterPointLift l I e hI hl s).choose_spec.1

private abbrev avgDefect (s : Bˣ) : affinePoints G (CommAlgCat.of R B) :=
  averageLaurentPoints G (scalarIdeal I B) (scalarIdeal_squareZero I hI)
    (parameterPointLift l I e hI hl s)

private theorem avgDefect_reduces (s : Bˣ) :
    mapAffinePointAlong G (scalarReduction I (B := B)) (avgDefect l I e hI hl s) = 1 :=
  (existsParameterPointLift l I e hI hl s).choose_spec.2

set_option backward.isDefEq.respectTransparency false in
private theorem parameterPointLift_natural (f : B →ₐ[R] C) (s : Bˣ) :
    mapAffinePointAlong G
      (scaleConstantReduction (scalarIdeal I B) (scalarIdeal I C) f (scalarIdeal_map_le I f) 1)
      (parameterPointLift l I e hI hl s) =
      parameterPointLift l I e hI hl (Units.map f.toMonoidHom s) := by
  apply mapAffinePoints_injective e (inclusionOfConstantReduction (R := R) (scalarIdeal I C))
    Subtype.val_injective
  rw [← mapAffinePointAlong_comp, scaleReduction_val, mapAffinePointAlong_comp,
    parameterPointLift_val, parameterPointLift_val, parameterPoint_scale]
  rw [map_one, one_mul]

private theorem avgDefect_natural (f : B →ₐ[R] C) (s : Bˣ) :
    mapAffinePointAlong G f (avgDefect l I e hI hl s) =
      avgDefect l I e hI hl (Units.map f.toMonoidHom s) := by
  change mapAffinePointAlong G f (averageLaurentPoints G (scalarIdeal I B) (scalarIdeal_squareZero I hI)
    (parameterPointLift l I e hI hl s)) = _
  rw [← averageLaurentPoints_scale (scalarIdeal I B) (scalarIdeal I C) _ (scalarIdeal_squareZero I hI)
    f (scalarIdeal_map_le I f) 1, parameterPointLift_natural]

private theorem mapAffinePointAlong_id (x : affinePoints G (CommAlgCat.of R B)) :
    mapAffinePointAlong G (AlgHom.id R B) x = x := by
  change coordSpecMap (AlgHom.id R B) ≫ x = x
  have h : coordSpecMap (AlgHom.id R B) = 𝟙 _ :=
    CategoryTheory.Functor.map_id (algSpec (CommRingCat.of R)) _
  rw [h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem avgDefect_cocycle (s t : Bˣ) :
    l.defect (CommAlgCat.of R B) s t * avgDefect l I e hI hl (s * t) =
      l.point (CommAlgCat.of R B) s * avgDefect l I e hI hl t *
        (l.point (CommAlgCat.of R B) s)⁻¹ * avgDefect l I e hI hl s := by
  let J := scalarIdeal I B
  let hJ := scalarIdeal_squareZero (B := B) I hI
  let p (v : Bˣ) := parameterPointLift l I e hI hl v
  let a := CommAlgCat.of R B
  let L := CommAlgCat.of R (LaurentPolynomial B)
  let u := Units.map (laurentConstants R B).toMonoidHom
  let c := mapAffinePointAlong G (constantPointMap (R := R) J)
  let j := mapAffinePointAlong G (inclusionOfConstantReduction (R := R) J)
  let f : B →ₐ[R] B := AlgHom.id R B
  let σ := mapAffinePointAlong G (scaleConstantReduction J J f (scalarIdeal_map_le I f) t)
  let avg := averageLaurentPoints G J hJ
  have hconst (x : affinePoints G a) : j (c x) = mapAffinePointAlong G (laurentConstants R B) x := by
    change mapAffinePointAlong G (inclusionOfConstantReduction (R := R) J)
      (mapAffinePointAlong G (constantPointMap (R := R) J) x) = _
    rw [← mapAffinePointAlong_comp, constantPointMap_val]
  have hcd : j (c (l.defect a s t)) = l.defect L (u s) (u t) := by
    rw [hconst]
    exact l.defect_natural (CommAlgCat.ofHom (laurentConstants R B)) s t
  have hcp : j (c (l.point a s)) = l.point L (u s) := by
    rw [hconst]
    exact l.natural (CommAlgCat.ofHom (laurentConstants R B)) s
  have hpar (v : Bˣ) : j (p v) = l.defect L (u v) (laurentVariable B 1) :=
    parameterPointLift_val l I e hI hl v
  have hscale : j (σ (p s)) = l.defect L (u s) (u t * laurentVariable B 1) := by
    change mapAffinePointAlong G (inclusionOfConstantReduction (R := R) J)
      (mapAffinePointAlong G (scaleConstantReduction J J f (scalarIdeal_map_le I f) t) (p s)) = _
    rw [← mapAffinePointAlong_comp, scaleReduction_val, mapAffinePointAlong_comp, hpar]
    exact parameterPoint_scale l f s t
  have h : c (l.defect a s t) * p (s * t) =
      c (l.point a s) * p t * (c (l.point a s))⁻¹ * σ (p s) := by
    apply mapAffinePoints_injective e (inclusionOfConstantReduction (R := R) J) Subtype.val_injective
    change j (_ * _) = j (_ * _ * _ * _)
    simpa only [map_mul, map_inv, hcd, hpar, hcp, hscale] using
      l.defect_cocycle L (u s) (u t) (laurentVariable B 1)
  have hav (x : affinePoints G a) : avg (c x) = x := averageLaurentPoints_const J hJ x
  have has : avg (σ (p s)) = avg (p s) := by
    change averageLaurentPoints G J hJ
      (mapAffinePointAlong G (scaleConstantReduction J J f (scalarIdeal_map_le I f) t) (p s)) = _
    rw [averageLaurentPoints_scale, mapAffinePointAlong_id]
  simpa only [map_mul, map_inv, hav, has] using congrArg avg h

private def correctedUnitPoint (s : Bˣ) : affinePoints G (CommAlgCat.of R B) :=
  (avgDefect l I e hI hl s)⁻¹ * l.point (CommAlgCat.of R B) s

private theorem correctedUnitPoint_mul (s t : Bˣ) :
    correctedUnitPoint l I e hI hl (s * t) =
      correctedUnitPoint l I e hI hl s * correctedUnitPoint l I e hI hl t := by
  let b (v : Bˣ) := avgDefect l I e hI hl v
  let a (v : Bˣ) := l.point (CommAlgCat.of R B) v
  let d := l.defect (CommAlgCat.of R B) s t
  have h : d * b (s * t) = a s * b t * (a s)⁻¹ * b s := avgDefect_cocycle l I e hI hl s t
  have hd : d = a s * b t * (a s)⁻¹ * b s * (b (s * t))⁻¹ :=
    (mul_inv_cancel_right d (b (s * t))).symm.trans (congrArg (· * (b (s * t))⁻¹) h)
  have hmul : a s * a t = (a s * b t * (a s)⁻¹ * b s * (b (s * t))⁻¹) * a (s * t) := by
    rw [← hd]
    change a s * a t = (a s * a t * (a (s * t))⁻¹) * a (s * t)
    group
  change (b (s * t))⁻¹ * a (s * t) = (b s)⁻¹ * a s * ((b t)⁻¹ * a t)
  symm
  calc
    _ = (b s)⁻¹ * a s * (b t)⁻¹ * (a s)⁻¹ * (a s * a t) := by group
    _ = _ := by rw [hmul]; group

include e hI hl in
set_option backward.isDefEq.respectTransparency false in
/-- Correct a map of the punctured line into an affine group to a
cocharacter when its reduction modulo a square-zero scalar ideal is a
cocharacter. The correction reduces to the identity. -/
theorem UnitPointMap.existsCocharacter :
    ∃ c : UnitCocharacter G,
      ∀ (B : CommAlgCat.{u} R) (t : Bˣ),
        mapAffinePointAlong G (scalarReduction I (B := B)) (c.point B t) =
          mapAffinePointAlong G (scalarReduction I (B := B)) (l.point B t) := by
  let c (B : CommAlgCat.{u} R) : Bˣ →* affinePoints G B :=
    { toFun := correctedUnitPoint l I e hI hl
      map_mul' := correctedUnitPoint_mul l I e hI hl
      map_one' := by
        let z := correctedUnitPoint l I e hI hl (B := B) (1 : Bˣ)
        have hm : z = z * z := by
          simpa only [one_mul] using correctedUnitPoint_mul l I e hI hl (1 : Bˣ) 1
        exact mul_left_cancel (hm.symm.trans (mul_one z).symm) }
  let cochar : UnitCocharacter G :=
    { point := c
      natural := by
        intro B C f t
        change mapAffinePointAlong G f.hom (correctedUnitPoint l I e hI hl t) =
          correctedUnitPoint l I e hI hl (Units.map f.hom.toMonoidHom t)
        rw [correctedUnitPoint, map_mul, map_inv, avgDefect_natural]
        have hn : mapAffinePointAlong G f.hom (l.point (CommAlgCat.of R B) t) =
            l.point (CommAlgCat.of R C) (Units.map f.hom.toMonoidHom t) := l.natural f t
        exact congrArg (fun z ↦
          (avgDefect l I e hI hl (Units.map f.hom.toMonoidHom t))⁻¹ * z) hn }
  refine ⟨cochar, ?_⟩
  intro B t
  change mapAffinePointAlong G (scalarReduction I (B := B)) (correctedUnitPoint l I e hI hl t) = _
  rw [correctedUnitPoint, map_mul, map_inv, avgDefect_reduces, inv_one, one_mul]
  rfl

end CocharacterDefect

end LaurentAverage

section FlatFibreCriterion

open Algebra.TensorProduct in
private theorem tensorMap_injective_of_geometric
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (h : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id R L) f))
    (K : Type u) [Field K] [Algebra R K] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id R K) f) := by
  let L := AlgebraicClosure K
  let : Algebra R L := inferInstanceAs (Algebra R (AlgebraicClosure K))
  let : IsScalarTower R K L := inferInstanceAs (IsScalarTower R K (AlgebraicClosure K))
  let t : K →ₐ[R] L := IsScalarTower.toAlgHom R K L
  obtain ⟨s, hs⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  let m := Algebra.TensorProduct.map t (AlgHom.id R A)
  have hm : Function.Injective m := by
    apply Function.LeftInverse.injective (g := TensorProduct.map (s.restrictScalars R)
      (LinearMap.id : A →ₗ[R] A))
    have hlin : (TensorProduct.map (s.restrictScalars R) (LinearMap.id : A →ₗ[R] A)).comp
        m.toLinearMap = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      have hx : s (t x) = x := LinearMap.congr_fun hs x
      simp [m, hx]
    exact LinearMap.congr_fun hlin
  intro x y hxy
  apply hm
  apply h L
  have hc : (Algebra.TensorProduct.map (AlgHom.id R L) f).comp m =
      (Algebra.TensorProduct.map t (AlgHom.id R B)).comp
        (Algebra.TensorProduct.map (AlgHom.id R K) f) := by
    dsimp only [m]
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    simp
  exact (DFunLike.congr_fun hc x).trans
    ((congrArg (Algebra.TensorProduct.map t (AlgHom.id R B)) hxy).trans
      (DFunLike.congr_fun hc y).symm)

/-- A surjective homomorphism to a base-flat algebra is injective if
its finitely generated kernel vanishes on all geometric base fibres. -/
theorem injective_of_flat_of_geometricFibres
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) (hfg : (RingHom.ker f).FG)
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id R K) f)) :
    Function.Injective f := by
  let I := RingHom.ker f
  let e : (A ⧸ I) ≃ₐ[R] B := Ideal.quotientKerAlgEquivOfSurjective hf
  have : Module.Flat R (A ⧸ I) := Module.Flat.of_linearEquiv e.toLinearEquiv
  have h : I = ⊥ := by
    apply ideal_eq_bot_of_flat_quotient_fieldFibres (R := R) I hfg
    intro K _ _
    have he : f = e.toAlgHom.comp (Ideal.Quotient.mkₐ R I) := by ext a; rfl
    have hw := tensorMap_injective_of_geometric f hgeom K
    rw [he, Algebra.TensorProduct.map_id_comp] at hw
    intro x y hxy
    exact hw (congrArg (Algebra.TensorProduct.map (AlgHom.id R K) e.toAlgHom) hxy)
  exact (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr h

open private tensorSpecPullback tensorSpecMapPullback surjective_of_closedSpecMap
  isIso_of_pullback_base finitePresentation_of_closed_over from
  LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

set_option backward.isDefEq.respectTransparency false in
private theorem affineClosedImmersion_isIso_of_geometricFibres {R : Type u} [CommRing R]
    {X Y : Over (ringSpec R)} (f : X ⟶ Y) [IsAffine X.left] [IsAffine Y.left]
    [IsClosedImmersion f.left] [LocallyOfFinitePresentation f.left] [Flat X.hom]
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      IsIso (((CategoryTheory.Over.pullback (algebraSpecMap R K)).map f).left)) :
    IsIso f.left := by
  let F := CategoryTheory.Over.forget (ringSpec R)
  obtain ⟨A, ⟨eX⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr
    (inferInstance : IsAffine X.left)
  obtain ⟨B, ⟨eY⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr
    (inferInstance : IsAffine Y.left)
  let θ := ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
    (eX.hom ≫ f ≫ eY.inv)).unop.hom
  let d := (coordSpecMap θ).left
  have hθ : coordSpecMap θ ≫ eY.hom = eX.hom ≫ f := by
    change (algSpec (CommRingCat.of R)).map
        ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage (eX.hom ≫ f ≫ eY.inv)) ≫
      eY.hom = _
    simp
  have hd : d ≫ eY.hom.left = eX.hom.left ≫ f.left := congrArg CategoryTheory.Over.Hom.left hθ
  have hd' : d = eX.hom.left ≫ f.left ≫ eY.inv.left := by
    apply (cancel_mono (F.mapIso eY).hom).mp
    change d ≫ eY.hom.left = (eX.hom.left ≫ f.left ≫ (F.mapIso eY).inv) ≫ (F.mapIso eY).hom
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hd
  have : IsIso eX.hom.left := (F.mapIso eX).isIso_hom
  have : IsIso eY.hom.left := (F.mapIso eY).isIso_hom
  have : IsIso eY.inv.left := (F.mapIso eY).isIso_inv
  have hc : IsClosedImmersion d := by rw [hd']; infer_instance
  have hfp : LocallyOfFinitePresentation d := by rw [hd']; infer_instance
  have hfR : Flat (algebraSpecMap R A.unop) := by
    change Flat ((algSpec (CommRingCat.of R)).obj A).hom
    rw [← CategoryTheory.Over.w eX.hom]
    infer_instance
  let : Module.Flat R A.unop := RingHom.flat_algebraMap_iff.mp
    ((HasRingHomProperty.Spec_iff (P := @Flat)).mp hfR)
  have hsurj : Function.Surjective θ := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom)) := hc
    exact surjective_of_closedSpecMap (CommRingCat.ofHom θ.toRingHom)
  have hfg : (RingHom.ker θ).FG := by
    let : Algebra B.unop A.unop := θ.toRingHom.toAlgebra
    have : Algebra.FinitePresentation B.unop A.unop :=
      (LocallyOfFinitePresentation.SpecMap_iff (CommRingCat.ofHom θ.toRingHom)).mp hfp
    exact Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom B.unop B.unop A.unop)
      hsurj
  have hi : Function.Injective θ := by
    apply injective_of_flat_of_geometricFibres θ hsurj hfg
    intro K _ _ _
    let a := algebraSpecMap R K
    let iA := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A.unop →ₐ[R] K ⊗[R] A.unop).toRingHom)
    let iB := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B.unop →ₐ[R] K ⊗[R] B.unop).toRingHom)
    let q := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R K) θ).toRingHom)
    let w := algebraSpecMap K (K ⊗[R] B.unop)
    have hb : IsPullback (iB ≫ eY.hom.left) w Y.hom a :=
      (tensorSpecPullback R K B.unop).of_iso (Iso.refl _) (F.mapIso eY) (Iso.refl _) (Iso.refl _)
        (by simp [iB]; rfl) (by simp [w]) (CategoryTheory.Over.w eY.hom).symm (by simp [a])
    have hq : IsPullback (iA ≫ eX.hom.left) q f.left (iB ≫ eY.hom.left) :=
      (tensorSpecMapPullback R K θ).of_iso (Iso.refl _) (F.mapIso eX) (Iso.refl _) (F.mapIso eY)
        (by simp [iA]; rfl) (by simp [q]) hd (by simp [iB]; rfl)
    have hp : IsPullback (pullback.fst Y.hom a) (pullback.snd Y.hom a) Y.hom a :=
      IsPullback.of_hasPullback _ _
    have : IsIso (((CategoryTheory.Over.pullback a).map f).left) := hgeom K
    have : IsIso q := isIso_of_pullback_base hp hb (pullbackMapSquare a f).flip hq
    let m := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R K) θ).toRingHom
    have : IsIso (Scheme.Spec.map m.op) := ‹IsIso q›
    have : IsIso m.op := isIso_of_reflects_iso m.op Scheme.Spec
    have : IsIso m := isIso_of_op m
    exact (ConcreteCategory.bijective_of_isIso m).injective
  let E := RingEquiv.ofBijective θ.toRingHom ⟨hi, hsurj⟩
  let r := CommRingCat.ofHom θ.toRingHom
  have : IsIso r := E.toCommRingCatIso.isIso_hom
  have : IsIso r.op := isIso_op r
  have : IsIso d := Scheme.Spec.map_isIso r.op
  have : IsIso (eX.hom.left ≫ f.left) := hd ▸ inferInstanceAs (IsIso (d ≫ eY.hom.left))
  exact IsIso.of_isIso_comp_left eX.hom.left f.left

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackComp_map_isIso {S T U : Scheme.{u}} {X Y : Over S}
    (a : U ⟶ T) (b : T ⟶ S) (f : X ⟶ Y)
    [IsIso ((CategoryTheory.Over.pullback (a ≫ b)).map f)] :
    IsIso ((CategoryTheory.Over.pullback a).map ((CategoryTheory.Over.pullback b).map f)) := by
  let e := CategoryTheory.Over.pullbackComp a b
  have h : e.hom.app X ≫ (CategoryTheory.Over.pullback a).map ((CategoryTheory.Over.pullback b).map f) =
      (CategoryTheory.Over.pullback (a ≫ b)).map f ≫ e.hom.app Y := (e.hom.naturality f).symm
  exact IsIso.of_isIso_fac_left h

set_option backward.isDefEq.respectTransparency false in
/-- A finitely presented closed immersion from a base-flat scheme into an
affine scheme over the same base is an isomorphism when its geometric
base fibres are isomorphisms. -/
theorem closedImmersion_isIso_of_geometricFibres {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [IsAffineHom Y.hom] [Flat X.hom] [IsClosedImmersion f.left]
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : ringSpec K ⟶ S),
      IsIso ((CategoryTheory.Over.pullback a).map f)) :
    IsIso f := by
  let c := S.affineCover
  have hf : IsIso f.left := by
    apply (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme)
      (f := f.left) (c.pullback₁ Y.hom)).mpr
    intro i
    let e := (c.X i).isoSpec
    let R := (c.X i).presheaf.obj (op ⊤)
    let b : ringSpec R ⟶ S := e.inv ≫ c.f i
    let F := CategoryTheory.Over.pullback b
    have hq := pullbackMapSquare b f
    have : IsAffine (F.obj Y).left := by
      change IsAffine (pullback Y.hom b)
      infer_instance
    have : IsClosedImmersion (F.map f).left :=
      MorphismProperty.of_isPullback hq.flip (inferInstance : IsClosedImmersion f.left)
    have : IsAffine (F.obj X).left := isAffine_of_isAffineHom (F.map f).left
    have : LocallyOfFinitePresentation (F.obj Y).hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Y.hom b))
    have : LocallyOfFinitePresentation (F.obj X).hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd X.hom b))
    have : LocallyOfFinitePresentation ((F.map f).left ≫ (F.obj Y).hom) := by
      rw [CategoryTheory.Over.w (F.map f)]
      exact ‹LocallyOfFinitePresentation (F.obj X).hom›
    have : LocallyOfFinitePresentation (F.map f).left :=
      finitePresentation_of_closed_over (F.map f).left (F.obj Y).hom
    have : Flat (F.obj X).hom :=
      inferInstanceAs (Flat (pullback.snd X.hom b))
    have hi : IsIso (F.map f).left := by
      apply affineClosedImmersion_isIso_of_geometricFibres
      intro K _ _ _
      let a := algebraSpecMap R K
      have := hgeom K (a ≫ b)
      have h := pullbackComp_map_isIso a b f
      exact (CategoryTheory.Over.forget (ringSpec K)).map_isIso ((CategoryTheory.Over.pullback a).map (F.map f))
    have hY : IsPullback (pullback.fst Y.hom b) (pullback.snd Y.hom b ≫ e.inv) Y.hom (c.f i) :=
      (IsPullback.of_hasPullback Y.hom b).of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp [b])
    exact isIso_of_pullback_base hY (IsPullback.of_hasPullback Y.hom (c.f i))
      hq.flip (IsPullback.of_hasPullback f.left (pullback.fst Y.hom (c.f i)))
  have : IsIso ((CategoryTheory.Over.forget S).map f) := hf
  exact isIso_of_reflects_iso f (CategoryTheory.Over.forget S)

private def groupHomOfFactor {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G H J : Grp C} (i : H ⟶ G) (j : J ⟶ G) [Mono j.hom.hom]
    (f : H.X ⟶ J.X) (h : f ≫ j.hom.hom = i.hom.hom) : H ⟶ J :=
  Grp.homMk'' f
    (by
      apply (cancel_mono j.hom.hom).mp
      simp only [Category.assoc, h, IsMonHom.one_hom])
    (by
      apply (cancel_mono j.hom.hom).mp
      simp only [Category.assoc, h, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc])

private theorem groupHomOfFactor_comp {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {G H J : Grp C} (i : H ⟶ G) (j : J ⟶ G) [Mono j.hom.hom]
    (f : H.X ⟶ J.X) (h : f ≫ j.hom.hom = i.hom.hom) :
    groupHomOfFactor i j f h ≫ j = i := Grp.hom_ext _ _ h

set_option backward.isDefEq.respectTransparency false in
private theorem groupHom_iso_of_borel {K : Type u} [Field K]
    {G : Specs.GroupScheme K} (H J : ClosedSubgroup G)
    (hH : IsBorel H) (hJ : IsBorel J)
    (f : H.group ⟶ J.group) (hf : f ≫ J.inclusion = H.inclusion) :
    IsIso f := by
  obtain ⟨g, hg⟩ := hH.2 J hJ.1 ⟨f, hf⟩
  have hcH := H.isClosedImmersion
  have hcJ := J.isClosedImmersion
  have hmH : Mono H.inclusion.hom.hom := CategoryTheory.Over.mono_of_mono_left _
  have hmJ : Mono J.inclusion.hom.hom := CategoryTheory.Over.mono_of_mono_left _
  have he (U V : Grp (Over (ringSpec K))) (i : V ⟶ G) [Mono i.hom.hom]
      (a b : U ⟶ V) (h : a ≫ i = b ≫ i) : a = b :=
    Grp.hom_ext _ _ ((cancel_mono i.hom.hom).mp (congrArg (fun q ↦ q.hom.hom) h))
  refine ⟨g, ?_, ?_⟩
  · apply he _ _ H.inclusion
    rw [Category.assoc, hg, hf, Category.id_comp]
  · apply he _ _ J.inclusion
    rw [Category.assoc, hf, hg, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Containment between two smooth closed subgroups with Borel fibres
gives an isomorphism over the ambient group. -/
theorem subgroupIsoOfBorelInclusion {S : Scheme.{u}} {G B C : Grp (Over S)}
    [IsAffineHom G.X.hom] (i : B ⟶ G) (j : C ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) (hj : IsClosedImmersion j.hom.hom.left)
    (hBs : Smooth B.X.hom) (hCs : Smooth C.X.hom)
    (hB : HasBorelFibres i) (hC : HasBorelFibres j)
    (f : B.X ⟶ C.X) (hf : f ≫ j.hom.hom = i.hom.hom) :
    ∃ e : B ≅ C, e.hom ≫ j = i := by
  have hmono : Mono j.hom.hom := CategoryTheory.Over.mono_of_mono_left _
  let g := groupHomOfFactor i j f hf
  have hg : g ≫ j = i := groupHomOfFactor_comp _ _ _ _
  have hfcl : IsClosedImmersion f.left := by
    have : IsClosedImmersion (f.left ≫ j.hom.hom.left) := by
      change IsClosedImmersion (f ≫ j.hom.hom).left
      rw [hf]
      exact hi
    exact IsClosedImmersion.of_comp_isClosedImmersion f.left j.hom.hom.left
  have hCaff : IsAffineHom C.X.hom := by
    rw [← CategoryTheory.Over.w j.hom.hom]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have hIso : IsIso f := by
    apply closedImmersion_isIso_of_geometricFibres
    intro k _ _ a
    let F := changeBase a
    obtain ⟨hbc, hb⟩ := hB k a
    obtain ⟨hcc, hc⟩ := hC k a
    let D : ClosedSubgroup (F.obj G) :=
      ⟨F.obj B, F.map i, hbc⟩
    let E : ClosedSubgroup (F.obj G) :=
      ⟨F.obj C, F.map j, hcc⟩
    have hv : F.map g ≫ E.inclusion = D.inclusion := (F.map_comp _ _).symm.trans (congrArg F.map hg)
    have : IsIso (F.map g) := groupHom_iso_of_borel D E hb hc _ hv
    exact (Grp.forget (Over (ringSpec k))).map_isIso (F.map g)
  let e := subgroupIso i j (asIso f) hf
  exact ⟨e, Grp.hom_ext _ _ hf⟩

set_option backward.isDefEq.respectTransparency false in
/-- Containment of Borel families is equality as subgroup schemes. -/
theorem sameFamily_of_inclusion {S : Scheme.{u}} {G : Grp (Over S)} {T : Over S}
    [IsAffineHom G.X.hom] {B C : Family G T}
    (hB : IsBorelFamily B) (hC : IsBorelFamily C)
    (f : B.group.X ⟶ C.group.X) (hf : f ≫ C.inclusion.hom.hom = B.inclusion.hom.hom) :
    SameFamily B C := by
  have : IsAffineHom ((changeBase T.hom).obj G).X.hom :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.X.hom T.hom)
      ‹IsAffineHom G.X.hom›
  exact subgroupIsoOfBorelInclusion B.inclusion C.inclusion B.closed C.closed B.smooth C.smooth
    hB hC f hf

end FlatFibreCriterion

section LaurentPointLift

open private smoothAffineCoordinates from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

private theorem laurentMap_ker_squareZero (I : Ideal R) (hI : I ^ 2 = ⊥) :
    RingHom.ker (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I)) ^ 2 = ⊥ := by
  rw [pow_two, ← le_bot_iff, Ideal.mul_le]
  intro p hp q hq
  have hmem (v : LaurentPolynomial R)
      (hv : v ∈ RingHom.ker (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I))) (n : ℤ) :
      v.coeff n ∈ I := by
    have h := congrArg (fun p : LaurentPolynomial (R ⧸ I) ↦ p.coeff n) (RingHom.mem_ker.mp hv)
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  change p * q = 0
  ext n : 1
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  have h := Ideal.mul_mem_mul (hmem p hp j) (hmem q hq (-j + n))
  simpa only [← pow_two, hI, Submodule.mem_bot] using h

/-- Smoothness lifts the generic Laurent point across a square-zero
base extension before imposing the cocharacter law. -/
theorem existsLaurentPointLift {G : Grp (Over (ringSpec R))} (e : coordSpec R A ≅ G.X)
    (hs : Smooth G.X.hom) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (x : coordSpec R (LaurentPolynomial (R ⧸ I)) ⟶ G.X) :
    ∃ y : coordSpec R (LaurentPolynomial R) ⟶ G.X,
      coordSpecMap (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I)) ≫ y = x := by
  let q := Ideal.Quotient.mkₐ R I
  let f := AddMonoidAlgebra.mapAlgHom ℤ q
  have hf : Function.Surjective f :=
    AddMonoidAlgebra.map_surjective q.toRingHom.toAddMonoidHom Ideal.Quotient.mk_surjective
  have : Algebra.Smooth R A := smoothAffineCoordinates (S := CommRingCat.of R) e hs
  obtain ⟨z, hz⟩ := lift_of_surjective f hf (laurentMap_ker_squareZero I hI) (pointCoordinates e x)
  refine ⟨(pointCoordinates e).symm z, (pointCoordinates e).injective ?_⟩
  rw [pointCoordinates_natural, Equiv.apply_symm_apply]
  exact hz

private theorem map_laurentEval {D E F : Type u} [CommRing D] [CommRing E] [CommRing F]
    [Algebra R D] [Algebra R E] [Algebra R F] (f : D →ₐ[R] E) (g : E →ₐ[R] F) (t : Eˣ) :
    g.comp (laurentEval f t) = laurentEval (g.comp f) (Units.map g.toMonoidHom t) := by
  apply AlgHom.ext
  intro p
  refine p.induction_on' (fun s t hs ht ↦ by simp only [map_add, hs, ht]) (fun n a ↦ ?_)
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp only [AlgHom.comp_apply, laurentEval_single, map_mul]
  have h := congrArg Units.val (map_zpow (Units.map g.toMonoidHom) t n)
  exact congrArg (g (f a) * ·) h

/-- The natural map parametrized by one affine Laurent point. -/
def UnitPointMap.ofLaurentPoint {G : Grp (Over (ringSpec R))}
    (x : coordSpec R (LaurentPolynomial R) ⟶ G.X) : UnitPointMap G where
  point B t := coordSpecMap (laurentEval (Algebra.ofId R B) t) ≫ x
  natural {B C} f t := by
    have h : f.hom.comp (Algebra.ofId R B) = Algebra.ofId R C :=
      Subsingleton.elim _ _
    change coordSpecMap f.hom ≫ coordSpecMap (laurentEval (Algebra.ofId R B) t) ≫ x =
      coordSpecMap (laurentEval (Algebra.ofId R C) (Units.map f.hom.toMonoidHom t)) ≫ x
    rw [← Category.assoc, ← coordSpecMap_comp, map_laurentEval, h]

/-- If the scalar ideal vanishes, evaluating a Laurent point can be
performed after reducing it modulo that ideal. -/
theorem UnitPointMap.ofLaurentPoint_reduces {G : Grp (Over (ringSpec R))}
    {I : Ideal R} (x : coordSpec R (LaurentPolynomial R) ⟶ G.X)
    (B : CommAlgCat R) (hB : I ≤ RingHom.ker (algebraMap R B)) (t : Bˣ) :
    let f : R ⧸ I →ₐ[R] B := Ideal.Quotient.liftₐ I (Algebra.ofId R B) hB
    (UnitPointMap.ofLaurentPoint x).point B t =
      coordSpecMap (laurentEval f t) ≫
        coordSpecMap (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I)) ≫ x := by
  let f := Ideal.Quotient.liftₐ I (Algebra.ofId R B) hB
  change coordSpecMap (laurentEval (Algebra.ofId R B) t) ≫ x =
    coordSpecMap (laurentEval f t) ≫
      coordSpecMap (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I)) ≫ x
  suffices he : (laurentEval f t).comp (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I)) =
      laurentEval (Algebra.ofId R B) t by
    rw [← Category.assoc, ← coordSpecMap_comp, he]
  apply AlgHom.ext
  intro p
  refine LaurentPolynomial.induction_on' p (fun p q hp hq ↦ by simp only [map_add, hp, hq]) (fun n a ↦ ?_)
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp only [AlgHom.comp_apply, AddMonoidAlgebra.mapAlgHom_single, laurentEval_single]
  rfl

end LaurentPointLift

section CocharacterConjugation

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {G : Grp (Over (ringSpec R))}

/-- Two cocharacters agree modulo an ideal if they agree on all algebras
over the quotient, viewed as algebras over the original base. -/
def UnitCocharacter.AgreeModulo (c d : UnitCocharacter G) (I : Ideal R) : Prop :=
  ∀ (B : CommAlgCat.{u} R), I ≤ RingHom.ker (algebraMap R B) → ∀ t : Bˣ,
    c.point B t = d.point B t

private def cocharacterDifference (c d : UnitCocharacter G) (B : CommAlgCat.{u} R) (t : Bˣ) :
    affinePoints G B :=
  d.point B t * (c.point B t)⁻¹

private theorem cocharacterDifference_natural (c d : UnitCocharacter G)
    {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : B →ₐ[R] C) (t : Bˣ) :
    mapAffinePointAlong G f (cocharacterDifference c d (CommAlgCat.of R B) t) =
      cocharacterDifference c d (CommAlgCat.of R C) (Units.map f.toMonoidHom t) := by
  simp only [cocharacterDifference, map_mul, map_inv]
  exact congrArg₂ (fun x y ↦ x * y⁻¹) (d.natural (CommAlgCat.ofHom f) t)
    (c.natural (CommAlgCat.ofHom f) t)

private theorem cocharacterDifference_mul (c d : UnitCocharacter G)
    (B : CommAlgCat.{u} R) (s t : Bˣ) :
    cocharacterDifference c d B (s * t) =
      cocharacterDifference c d B s * c.point B s *
        cocharacterDifference c d B t * (c.point B s)⁻¹ := by
  simp only [cocharacterDifference, map_mul]
  group

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- A square-zero change in a cocharacter is conjugation by a point
which reduces to the identity. -/
theorem UnitCocharacter.existsConjugationOfAgreeModulo (e : coordSpec R A ≅ G.X)
    {c d : UnitCocharacter G} (I : Ideal R) (hI : I ^ 2 = ⊥) (hcd : c.AgreeModulo d I) :
    ∃ v : affinePoints G (CommAlgCat.of R R),
      mapAffinePointAlong G (Ideal.Quotient.mkₐ R I) v = 1 ∧
      ∀ (B : CommAlgCat.{u} R) (t : Bˣ),
        let vB := mapAffinePointAlong G (Algebra.ofId R B) v
        vB * c.point B t * vB⁻¹ = d.point B t := by
  let L := LaurentPolynomial R
  let δ := cocharacterDifference c d (CommAlgCat.of R L) (laurentVariable R 1)
  let q := AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R I)
  have hkill : I ≤ RingHom.ker (algebraMap R (LaurentPolynomial (R ⧸ I))) := by
    intro r hr
    change LaurentPolynomial.C (Ideal.Quotient.mk I r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  have hred : mapAffinePointAlong G q δ = 1 := by
    rw [cocharacterDifference_natural c d q]
    unfold cocharacterDifference
    rw [hcd _ hkill, mul_inv_cancel]
  have hred' : coordSpecMap q ≫ δ = coordSpecMap (laurentConstants R (R ⧸ I)) ≫
      (1 : coordSpec R (R ⧸ I) ⟶ G.X) := hred.trans (MonObj.comp_one _).symm
  obtain ⟨p, hp, hpI⟩ := liftPointToConstantReduction e I hI δ 1 hred'
  let v := averageLaurentPoints G I hI p
  refine ⟨v, hpI, ?_⟩
  intro B t
  let f : R →ₐ[R] B := Algebra.ofId R B
  let J := scalarIdeal I B
  let hJ := scalarIdeal_squareZero I hI (B := B)
  have hf : I ≤ J.comap f.toRingHom := fun _ hr ↦ Ideal.mem_map_of_mem (algebraMap R B) hr
  let b := CommAlgCat.of R B
  let l := CommAlgCat.of R (LaurentPolynomial B)
  let k := Units.map (laurentConstants R B).toMonoidHom
  let z := laurentVariable B 1
  let lift (s : Bˣ) := mapAffinePointAlong G (scaleConstantReduction I J f hf s) p
  let j := mapAffinePointAlong G (inclusionOfConstantReduction (R := R) J)
  let const := mapAffinePointAlong G (constantPointMap (R := R) J)
  have hj_lift (s : Bˣ) : j (lift s) = cocharacterDifference c d l (k s * z) := by
    change mapAffinePointAlong G (inclusionOfConstantReduction (R := R) J)
      (mapAffinePointAlong G (scaleConstantReduction I J f hf s) p) = _
    rw [← mapAffinePointAlong_comp, scaleReduction_val, mapAffinePointAlong_comp]
    change mapAffinePointAlong G (scaleLaurent f s)
      (coordSpecMap (constantReductionAlgebra R I).val ≫ p) = _
    rw [hp, cocharacterDifference_natural, scaleLaurent_var]
  have hj_const (x : affinePoints G b) : j (const x) =
      mapAffinePointAlong G (laurentConstants R B) x := by
    change mapAffinePointAlong G (inclusionOfConstantReduction (R := R) J)
      (mapAffinePointAlong G (constantPointMap (R := R) J) x) = _
    rw [← mapAffinePointAlong_comp, constantPointMap_val]
  have hδ : j (const (cocharacterDifference c d b t)) = cocharacterDifference c d l (k t) := by
    rw [hj_const]
    exact cocharacterDifference_natural c d (laurentConstants R B) t
  have hc : j (const (c.point b t)) = c.point l (k t) := by
    rw [hj_const]
    exact c.natural (CommAlgCat.ofHom (laurentConstants R B)) t
  have h : lift t = const (cocharacterDifference c d b t) * const (c.point b t) *
      lift 1 * (const (c.point b t))⁻¹ := by
    apply mapAffinePoints_injective e (inclusionOfConstantReduction (R := R) J) Subtype.val_injective
    change j (lift t) = j (_ * _ * _ * _)
    simpa only [map_mul, map_inv, hj_lift, hδ, hc, map_one, one_mul] using
      cocharacterDifference_mul c d l (k t) z
  let avg := averageLaurentPoints G J hJ
  let vB := mapAffinePointAlong G f v
  have hav (s : Bˣ) : avg (lift s) = vB := averageLaurentPoints_scale I J hI hJ f hf s p
  have hconst (x : affinePoints G b) : avg (const x) = x := averageLaurentPoints_const J hJ x
  have he : vB = cocharacterDifference c d b t * c.point b t * vB * (c.point b t)⁻¹ := by
    simpa only [map_mul, map_inv, hav, hconst] using congrArg avg h
  have he' : vB = d.point b t * vB * (c.point b t)⁻¹ := by
    calc
      _ = cocharacterDifference c d b t * c.point b t * vB * (c.point b t)⁻¹ := he
      _ = _ := by rw [cocharacterDifference, inv_mul_cancel_right]
  change vB * c.point b t * vB⁻¹ = d.point b t
  calc
    _ = (d.point b t * vB * (c.point b t)⁻¹) * c.point b t * vB⁻¹ :=
      congrArg (fun w ↦ w * c.point b t * vB⁻¹) he'
    _ = _ := by group

end CocharacterConjugation

section LiftIntoSubgroup

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {H G : Grp (Over (ringSpec R))}

/-- A homomorphism of group schemes induces a homomorphism on affine points. -/
private def affinePointHom (i : H ⟶ G) (B : CommAlgCat.{u} R) :
    affinePoints H B →* affinePoints G B where
  toFun x := x ≫ i.hom.hom
  map_one' := MonObj.one_comp i.hom.hom
  map_mul' x y := MonObj.mul_comp x y i.hom.hom

/-- Postcomposition of a cocharacter with a group homomorphism. -/
def UnitCocharacter.mapGroup (c : UnitCocharacter H) (i : H ⟶ G) :
    UnitCocharacter G where
  point B := (affinePointHom i B).comp (c.point B)
  natural {B C} f t := by
    change (algSpec (CommRingCat.of R)).map f.op ≫ c.point B t ≫ i.hom.hom =
      c.point C (Units.map f.hom.toMonoidHom t) ≫ i.hom.hom
    rw [← Category.assoc]
    exact congrArg (· ≫ i.hom.hom) (c.natural f t)

set_option backward.isDefEq.respectTransparency false in
private theorem cocharacterPoint_natural_eval {B : Type u} [CommRing B] [Algebra R B]
    {D : Type u} [CommRing D] [Algebra R D] (c : UnitCocharacter G)
    (f : D →ₐ[R] B) (t : Bˣ) :
    coordSpecMap (laurentEval f t) ≫ c.point (CommAlgCat.of R (LaurentPolynomial D))
      (laurentVariable D 1) = c.point (CommAlgCat.of R B) t := by
  let g := laurentEval f t
  have h : Units.map g.toMonoidHom (laurentVariable D 1) = t := laurentEval_variable f t
  exact (c.natural (CommAlgCat.ofHom g) (laurentVariable D 1)).trans
    (congrArg (c.point (CommAlgCat.of R B)) h)

set_option backward.isDefEq.respectTransparency false in
/-- A cocharacter with a reduced Laurent point in a smooth closed
subgroup lifts to a cocharacter of that subgroup. -/
theorem existsCocharacterLiftOfFactor (e : coordSpec R A ≅ H.X)
    (hs : Smooth H.X.hom) (i : H ⟶ G) [Mono i.hom.hom]
    (I : Ideal R) (hI : I ^ 2 = ⊥) (c : UnitCocharacter G)
    (x : coordSpec R (LaurentPolynomial (R ⧸ I)) ⟶ H.X)
    (hx : x ≫ i.hom.hom =
      c.point (CommAlgCat.of R (LaurentPolynomial (R ⧸ I))) (laurentVariable (R ⧸ I) 1)) :
    ∃ d : UnitCocharacter H, c.AgreeModulo (d.mapGroup i) I := by
  obtain ⟨y, hy⟩ := existsLaurentPointLift e hs I hI x
  let l := UnitPointMap.ofLaurentPoint y
  have hl (B : CommAlgCat.{u} R) (hB : I ≤ RingHom.ker (algebraMap R B)) (t : Bˣ) :
      l.point B t ≫ i.hom.hom = c.point B t := by
    rw [show l.point B t = (UnitPointMap.ofLaurentPoint y).point B t from rfl,
      UnitPointMap.ofLaurentPoint_reduces y B hB t, hy, Category.assoc, hx]
    exact cocharacterPoint_natural_eval c _ t
  have hm : l.IsMultiplicativeModulo I := by
    intro B hB s t
    apply (cancel_mono i.hom.hom).mp
    rw [hl B hB, MonObj.mul_comp, hl B hB, hl B hB, map_mul]
  obtain ⟨d, hd⟩ := l.existsCocharacter I e hI hm
  refine ⟨d, ?_⟩
  intro B hB t
  let J := scalarIdeal I B
  have hJ : J ≤ RingHom.ker (AlgHom.id R B) :=
    Ideal.map_le_iff_le_comap.mpr hB
  let f := Ideal.Quotient.liftₐ J (AlgHom.id R B) hJ
  have hf : f.comp (scalarReduction I (B := B)) = AlgHom.id R B := rfl
  have h := congrArg (mapAffinePointAlong H f) (hd B t)
  rw [← mapAffinePointAlong_comp, ← mapAffinePointAlong_comp, hf,
    mapAffinePointAlong_id, mapAffinePointAlong_id] at h
  change c.point B t = d.point B t ≫ i.hom.hom
  rw [h, hl B hB]

end LiftIntoSubgroup

section PolynomialOrbitRigidity

open private surjective_of_closedSpecMap from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

variable {R : Type u} [CommRing R] {G H : Grp (Over (ringSpec R))}

private theorem orbitPoint_map {B : Type u} [CommRing B] [Algebra R B]
    (c : UnitCocharacter H) (j : H ⟶ G) (g : coordSpec R B ⟶ H.X) :
    orbitPoint (c.mapGroup j) B (g ≫ j.hom.hom) = orbitPoint c B g ≫ j.hom.hom := by
  change (c.point _ (laurentVariable B 1) ≫ j.hom.hom) *
      (coordSpecMap (laurentConstants R B) ≫ (g ≫ j.hom.hom)) *
      (c.point _ (laurentVariable B 1) ≫ j.hom.hom)⁻¹ =
    (c.point _ (laurentVariable B 1) *
      (coordSpecMap (laurentConstants R B) ≫ g) *
      (c.point _ (laurentVariable B 1))⁻¹) ≫ j.hom.hom
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

private theorem HasPolynomialOrbit.mapGroup {B : Type u} [CommRing B] [Algebra R B]
    (c : UnitCocharacter H) (j : H ⟶ G) (g : coordSpec R B ⟶ H.X)
    (h : HasPolynomialOrbit c g) : HasPolynomialOrbit (c.mapGroup j) (g ≫ j.hom.hom) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p ≫ j.hom.hom, by rw [orbitPoint_map, ← Category.assoc, hp]⟩

private theorem pointCoordinates_comp_groupHom {A D B : Type u}
    [CommRing A] [Algebra R A] [CommRing D] [Algebra R D] [CommRing B] [Algebra R B]
    (e : coordSpec R A ≅ G.X) (d : coordSpec R D ≅ H.X) (j : H ⟶ G)
    (g : coordSpec R B ⟶ H.X) :
    pointCoordinates e (g ≫ j.hom.hom) =
      (pointCoordinates d g).comp (pointCoordinates e (d.hom ≫ j.hom.hom)) := by
  rw [← pointCoordinates_natural, ← Category.assoc]
  have h := (pointCoordinates (B := B) d).symm_apply_apply g
  change coordSpecMap (pointCoordinates d g) ≫ d.hom = g at h
  rw [h]

set_option backward.isDefEq.respectTransparency false in
private theorem HasPolynomialOrbit.of_groupHom {A D B : Type u}
    [CommRing A] [Algebra R A] [CommRing D] [Algebra R D] [CommRing B] [Algebra R B]
    (e : coordSpec R A ≅ G.X) (d : coordSpec R D ≅ H.X)
    (c : UnitCocharacter H) (j : H ⟶ G) (hj : IsClosedImmersion j.hom.hom.left)
    (g : coordSpec R B ⟶ H.X) (h : HasPolynomialOrbit (c.mapGroup j) (g ≫ j.hom.hom)) :
    HasPolynomialOrbit c g := by
  let φ := pointCoordinates e (d.hom ≫ j.hom.hom)
  have hφ : Function.Surjective φ := by
    have he : coordSpecMap φ ≫ e.hom = d.hom ≫ j.hom.hom :=
      (pointCoordinates e).symm_apply_apply _
    have h₀ : IsClosedImmersion (d.hom ≫ j.hom.hom).left := by
      have : IsIso d.hom.left := ((CategoryTheory.Over.forget _).mapIso d).isIso_hom
      change IsClosedImmersion (d.hom.left ≫ j.hom.hom.left)
      exact IsClosedImmersion.comp _ _
    have he' : IsIso e.hom.left := ((CategoryTheory.Over.forget _).mapIso e).isIso_hom
    have h₁ : IsClosedImmersion ((coordSpecMap φ).left ≫ e.hom.left) := by
      change IsClosedImmersion (coordSpecMap φ ≫ e.hom).left
      rw [he]
      exact h₀
    have he'' := IsClosedImmersion.of_comp_isClosedImmersion (coordSpecMap φ).left e.hom.left
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := he''
    exact surjective_of_closedSpecMap (CommRingCat.ofHom φ.toRingHom)
  obtain ⟨p, hp⟩ := h
  have hpoly : ∃ f : D →ₐ[R] Polynomial B,
      (toLaurentOver (R := R) (B := B)).comp f = pointCoordinates d (orbitPoint c B g) := by
    apply (polynomialLift_iff _).mpr
    intro x n hn
    obtain ⟨a, rfl⟩ := hφ x
    have hcomp := pointCoordinates_comp_groupHom e d j (orbitPoint c B g)
    rw [← orbitPoint_map] at hcomp
    have hp' : (toLaurentOver (R := R) (B := B)).comp (pointCoordinates e p) =
        pointCoordinates e (orbitPoint (c.mapGroup j) B (g ≫ j.hom.hom)) := by
      rw [← pointCoordinates_natural, hp]
    have hc := (polynomialLift_iff _).mp ⟨_, hp'⟩ a n hn
    rw [hcomp] at hc
    exact hc
  obtain ⟨f, hf⟩ := hpoly
  refine ⟨(pointCoordinates d).symm f, (pointCoordinates d).injective ?_⟩
  rwa [pointCoordinates_natural, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- A square-zero deformation of a group contracted by a cocharacter
has no negative Laurent weights if its reduction has none. -/
theorem polynomialOrbit_of_squareZero {A : Type u} [CommRing A] [Algebra R A]
    (e : coordSpec R A ≅ G.X) (c : UnitCocharacter G) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h : ∀ (B : Type u) [CommRing B] [Algebra R B], I ≤ RingHom.ker (algebraMap R B) →
      ∀ g : coordSpec R B ⟶ G.X, HasPolynomialOrbit c g) :
    ∀ (B : Type u) [CommRing B] [Algebra R B], ∀ g : coordSpec R B ⟶ G.X,
      HasPolynomialOrbit c g := by
  let J := I.map (algebraMap R A)
  let q := Ideal.Quotient.mkₐ R J
  let d := LaurentGrading.ofCocharacter e c
  have hq : I ≤ RingHom.ker (algebraMap R (A ⧸ J)) := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (algebraMap R A) hr)
  have hcoord : pointCoordinates e (coordSpecMap q ≫ e.hom) = q :=
    (pointCoordinates e).apply_symm_apply q
  have hneg : d.negativeIdeal ≤ J := by
    have hp := (hasPolynomialOrbit_iff e c (coordSpecMap q ≫ e.hom)).mp
      (h (A ⧸ J) hq _)
    rw [hcoord] at hp
    change d.negativeIdeal ≤ RingHom.ker (Ideal.Quotient.mk J) at hp
    rwa [Ideal.mk_ker] at hp
  have hz := d.negativeIdeal_eq_bot_of_squareZero I hI hneg
  intro B _ _ g
  apply (hasPolynomialOrbit_iff e c g).mpr
  rw [hz]
  exact bot_le

private theorem HasPolynomialOrbit.cocharacterPoint {B : Type u} [CommRing B] [Algebra R B]
    (c : UnitCocharacter G) (t : Bˣ) : HasPolynomialOrbit c (c.point (CommAlgCat.of R B) t) := by
  let f : B →ₐ[R] Polynomial B := IsScalarTower.toAlgHom R B (Polynomial B)
  have hf : (toLaurentOver (R := R) (B := B)).comp f = laurentConstants R B := by
    ext b : 1
    exact Polynomial.toLaurent_C b
  refine ⟨coordSpecMap f ≫ c.point (CommAlgCat.of R B) t, ?_⟩
  rw [← Category.assoc, ← coordSpecMap_comp, hf]
  let L := CommAlgCat.of R (LaurentPolynomial B)
  let u := laurentVariable B 1
  let t' := Units.map (laurentConstants R B).toMonoidHom t
  change mapAffinePointAlong G (laurentConstants R B) (c.point (CommAlgCat.of R B) t) =
    c.point L u * mapAffinePointAlong G (laurentConstants R B)
      (c.point (CommAlgCat.of R B) t) * (c.point L u)⁻¹
  have h := c.natural (CommAlgCat.ofHom (laurentConstants R B)) t
  change mapAffinePointAlong G (laurentConstants R B) (c.point (CommAlgCat.of R B) t) =
    c.point L t' at h
  rw [h, ← map_mul, mul_comm u t', map_mul, mul_inv_cancel_right]

end PolynomialOrbitRigidity

section RelativeContainment

variable {S : Scheme.{u}} {G B : Grp (Over S)} {T U : Over S}

set_option backward.isDefEq.respectTransparency false in
private theorem familyProductPullback (Q : Family G T) (a : U ⟶ T) :
    IsPullback (Q.pullback a).inclusion.hom.hom.left (pullback.fst Q.group.X.hom a.left)
      (G.X ◁ a).left (familyProductInclusion Q).left := by
  let F := Grp.forget (Over U.left) ⋙ CategoryTheory.Over.forget U.left
  let e := F.mapIso (compareAmbient a G)
  have h := pullbackMapSquare a.left Q.inclusion.hom.hom
  refine h.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change ((changeBase a.left).map Q.inclusion).hom.hom.left ≫ e.inv =
      𝟙 _ ≫ (Q.pullback a).inclusion.hom.hom.left
    rw [Category.id_comp]
    rfl
  · simp
  · change pullback.fst ((changeBase T.hom).obj G).X.hom a.left ≫ 𝟙 _ =
      e.inv ≫ (G.X ◁ a).left
    rw [Category.comp_id, ← compareAmbient_first a G]
    change pullback.fst _ _ = e.inv ≫ e.hom ≫ pullback.fst _ _
    exact (e.inv_hom_id_assoc _).symm
  · simp [familyProductInclusion_left]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- For families with Borel fibres the conjugacy-containment locus is
the scheme of conjugacies, including on nonreduced test schemes. -/
theorem conjugateContained_iff_sameFamily [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (j : B ⟶ G) (hc : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (hB : HasBorelFibres j) (Q : Family G T) (hQ : IsBorelFamily Q)
    (a : U ⟶ T) (g : U ⟶ G.X) :
    ConjugateContained j Q a g ↔ SameFamily (conjugateSubgroupFamily j hc hs g) (Q.pullback a) := by
  let C := conjugateSubgroupFamily j hc hs g
  let D := Q.pullback a
  let b := pullback.fst Q.group.X.hom a.left
  have hpb := familyProductPullback Q a
  have heC : C.inclusion.hom.hom.left = (conjugateOver j g).left :=
    conjugateSubgroupFamily_left j hc hs g
  constructor
  · rintro ⟨w, hw⟩
    have h : C.inclusion.hom.hom.left ≫ (G.X ◁ a).left = w.left ≫ (familyProductInclusion Q).left := by
      rw [heC]
      exact (congrArg CategoryTheory.Over.Hom.left hw).symm
    let z := hpb.lift C.inclusion.hom.hom.left w.left h
    have hz : z ≫ D.inclusion.hom.hom.left = C.inclusion.hom.hom.left :=
      hpb.lift_fst _ _ _
    have hz' : z ≫ D.group.X.hom = C.group.X.hom := by
      rw [← CategoryTheory.Over.w D.inclusion.hom.hom, ← Category.assoc, hz, CategoryTheory.Over.w C.inclusion.hom.hom]
    let f : C.group.X ⟶ D.group.X := CategoryTheory.Over.homMk z hz'
    have hf : f ≫ D.inclusion.hom.hom = C.inclusion.hom.hom := CategoryTheory.Over.OverMorphism.ext hz
    exact sameFamily_of_inclusion (conjugateSubgroupFamily_isBorel j hc hs hB g)
      (isBorelFamily_pullback Q hQ a) f hf
  · rintro ⟨e, he⟩
    have hbase : b ≫ Q.group.X.hom = D.group.X.hom ≫ a.left := pullback.condition
    let w : C.group.X ⟶ D.group.X := e.hom.hom.hom
    have hstr : (e.hom.hom.hom.left ≫ b) ≫ (familyOverBase Q).hom = (B.X ⊗ U).hom := by
      change (w.left ≫ b) ≫ (Q.group.X.hom ≫ T.hom) = _
      simp only [Category.assoc, reassoc_of% hbase, CategoryTheory.Over.w a, CategoryTheory.Over.w_assoc w]
      exact CategoryTheory.Over.w (snd B.X U)
    let f : B.X ⊗ U ⟶ familyOverBase Q := CategoryTheory.Over.homMk (e.hom.hom.hom.left ≫ b) hstr
    use f
    apply CategoryTheory.Over.OverMorphism.ext
    change (e.hom.hom.hom.left ≫ b) ≫ (familyProductInclusion Q).left =
      (conjugateOver j g).left ≫ (G.X ◁ a).left
    have h : w.left ≫ D.inclusion.hom.hom.left = C.inclusion.hom.hom.left :=
      congrArg (fun z ↦ z.hom.hom.left) he
    change (w.left ≫ b) ≫ (familyProductInclusion Q).left =
      (conjugateOver j g).left ≫ (G.X ◁ a).left
    rw [Category.assoc, ← hpb.w, ← Category.assoc, h, heC]

end RelativeContainment

section RelativePoints

variable {S T : Scheme.{u}}

private theorem adjointProductPullback (a : T ⟶ S) (X : Over S) (U : Over T) :
    IsPullback ((fst ((CategoryTheory.Over.pullback a).obj X) U).left ≫ pullback.fst X.hom a)
      (snd ((CategoryTheory.Over.pullback a).obj X) U).left X.hom (U.hom ≫ a) :=
  (IsPullback.of_hasPullback ((CategoryTheory.Over.pullback a).obj X).hom U.hom).paste_horiz
    (IsPullback.of_hasPullback X.hom a)

private def adjointProductIso (a : T ⟶ S) (X : Over S) (U : Over T) :
    (CategoryTheory.Over.map a).obj ((CategoryTheory.Over.pullback a).obj X ⊗ U) ≅ X ⊗ (CategoryTheory.Over.map a).obj U :=
  CategoryTheory.Over.isoMk (adjointProductPullback a X U).isoPullback (by
    let h := adjointProductPullback a X U
    change h.isoPullback.hom ≫ pullback.fst X.hom (U.hom ≫ a) ≫ X.hom =
      pullback.fst ((CategoryTheory.Over.pullback a).obj X).hom U.hom ≫ ((CategoryTheory.Over.pullback a).obj X).hom ≫ a
    rw [← Category.assoc, h.isoPullback_hom_fst, Category.assoc, pullback.condition]
    rfl)

private theorem adjointProductIso_fst (a : T ⟶ S) (X : Over S) (U : Over T) :
    (adjointProductIso a X U).hom.left ≫ (fst X ((CategoryTheory.Over.map a).obj U)).left =
      (fst ((CategoryTheory.Over.pullback a).obj X) U).left ≫ pullback.fst X.hom a :=
  (adjointProductPullback a X U).isoPullback_hom_fst

private theorem adjointProductIso_snd (a : T ⟶ S) (X : Over S) (U : Over T) :
    (adjointProductIso a X U).hom ≫ snd X ((CategoryTheory.Over.map a).obj U) =
      (CategoryTheory.Over.map a).map (snd ((CategoryTheory.Over.pullback a).obj X) U) := by
  apply CategoryTheory.Over.OverMorphism.ext
  exact (adjointProductPullback a X U).isoPullback_hom_snd

private theorem unbasePoint_comp (a : T ⟶ S) {B : Grp (Over S)} {U V : Over T}
    (f : U ⟶ V) (g : V ⟶ ((changeBase a).obj B).X) :
    unbasePoint a U B (f ≫ g) = (CategoryTheory.Over.map a).map f ≫ unbasePoint a V B g :=
  (CategoryTheory.Over.mapPullbackAdj a).homEquiv_naturality_left_symm f g

private theorem unbasePoint_fst (a : T ⟶ S) (B : Grp (Over S)) (U : Over T) :
    unbasePoint a (((changeBase a).obj B).X ⊗ U) B (fst ((changeBase a).obj B).X U) =
      (adjointProductIso a B.X U).hom ≫ fst B.X ((CategoryTheory.Over.map a).obj U) := by
  apply CategoryTheory.Over.OverMorphism.ext
  exact (adjointProductIso_fst a B.X U).symm

section ConjugateMap

variable {G B : Grp (Over S)}

private abbrev conjugateMap (j : B ⟶ G) {V : Over S} (g : V ⟶ G.X) :=
  (snd B.X V ≫ g) * (fst B.X V ≫ j.hom.hom) * (snd B.X V ≫ g)⁻¹

set_option backward.isDefEq.respectTransparency false in
private theorem unbasePoint_conjugateMap (a : T ⟶ S) (j : B ⟶ G)
    {V : Over T} (g : V ⟶ ((changeBase a).obj G).X) :
    unbasePoint a (((changeBase a).obj B).X ⊗ V) G
      (conjugateMap ((changeBase a).map j) g) =
      (adjointProductIso a B.X V).hom ≫ conjugateMap j (unbasePoint a V G g) := by
  let D := ((changeBase a).obj B).X
  let U := (CategoryTheory.Over.map a).obj V
  let e := adjointProductIso a B.X V
  have hf : unbasePoint a (D ⊗ V) G (fst D V ≫ ((changeBase a).map j).hom.hom) =
      e.hom ≫ fst B.X U ≫ j.hom.hom := by
    rw [unbasePoint_map, unbasePoint_fst, Category.assoc]
  have hs : unbasePoint a (D ⊗ V) G (snd D V ≫ g) =
      e.hom ≫ snd B.X U ≫ unbasePoint a V G g := by
    have hw : (CategoryTheory.Over.map a).map (snd D V) = e.hom ≫ snd B.X U :=
      (adjointProductIso_snd a B.X V).symm
    rw [unbasePoint_comp, hw, Category.assoc]
  change unbasePoint a (D ⊗ V) G
      ((snd D V ≫ g) * (fst D V ≫ ((changeBase a).map j).hom.hom) * (snd D V ≫ g)⁻¹) =
    e.hom ≫ ((snd B.X U ≫ unbasePoint a V G g) * (fst B.X U ≫ j.hom.hom) *
       (snd B.X U ≫ unbasePoint a V G g)⁻¹)
  simp only [map_mul, map_inv, MonObj.comp_mul, GrpObj.comp_inv]
  rw [hf, hs]

set_option backward.isDefEq.respectTransparency false in
private theorem conjugationFactors_changeBase (a : T ⟶ S) (j : B ⟶ G)
    {V : Over T} (g : V ⟶ ((changeBase a).obj G).X) :
    (∃ f : ((changeBase a).obj B).X ⊗ V ⟶ ((changeBase a).obj B).X,
      f ≫ ((changeBase a).map j).hom.hom = conjugateMap ((changeBase a).map j) g) ↔
    ∃ f : B.X ⊗ (CategoryTheory.Over.map a).obj V ⟶ B.X,
      f ≫ j.hom.hom = conjugateMap j (unbasePoint a V G g) := by
  let A := ((changeBase a).obj B).X ⊗ V
  let e := adjointProductIso a B.X V
  constructor
  · rintro ⟨f, hf⟩
    have h := congrArg (unbasePoint a A G) hf
    rw [unbasePoint_map, unbasePoint_conjugateMap] at h
    exact ⟨e.inv ≫ unbasePoint a A B f, by rw [Category.assoc, h, e.inv_hom_id_assoc]⟩
  · rintro ⟨f, hf⟩
    refine ⟨(unbasePoint a A B).symm (e.hom ≫ f), (unbasePoint a A G).injective ?_⟩
    rw [unbasePoint_map, MulEquiv.apply_symm_apply, Category.assoc, hf, unbasePoint_conjugateMap]

end ConjugateMap

section FamilySections

variable {G : Grp (Over S)} {X Y Z : Over S}

/-- Points of a family on a test scheme, with the given base and ambient
group components. -/
def familyContainsSection (Q : Family G X) (a : Y ⟶ X) (g : Y ⟶ G.X) : Prop :=
  ∃ w : Y ⟶ familyOverBase Q, w ≫ familyProductInclusion Q = lift g a

private def familyRestriction (Q : Family G X) (a : Y ⟶ X) :
    familyOverBase (Q.pullback a) ⟶ familyOverBase Q :=
  CategoryTheory.Over.homMk (pullback.fst Q.group.X.hom a.left) (by
    change pullback.fst Q.group.X.hom a.left ≫ Q.group.X.hom ≫ X.hom =
      (pullback.snd Q.group.X.hom a.left ≫ Y.hom)
    rw [← Category.assoc, pullback.condition, Category.assoc, CategoryTheory.Over.w a])

private theorem familyProductPullback_over (Q : Family G X) (a : Y ⟶ X) :
    IsPullback (familyProductInclusion (Q.pullback a)) (familyRestriction Q a)
      (G.X ◁ a) (familyProductInclusion Q) := by
  apply IsPullback.of_map_of_faithful (CategoryTheory.Over.forget S)
  change IsPullback (familyProductInclusion (Q.pullback a)).left
    (pullback.fst Q.group.X.hom a.left) (G.X ◁ a).left (familyProductInclusion Q).left
  rw [familyProductInclusion_left]
  exact familyProductPullback Q a

/-- Membership in a family after pullback is computed by composition of
the base point with the pullback morphism. -/
theorem Family.containsSection_pullback_iff (Q : Family G X)
    (a : Y ⟶ X) (b : Z ⟶ Y) (g : Z ⟶ G.X) :
    familyContainsSection (Q.pullback a) b g ↔ familyContainsSection Q (b ≫ a) g := by
  let h := familyProductPullback_over Q a
  have hc : lift g b ≫ (G.X ◁ a) = lift g (b ≫ a) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w ≫ familyRestriction Q a, by rw [Category.assoc, ← h.w, ← Category.assoc, hw, hc]⟩
  · rintro ⟨w, hw⟩
    exact ⟨h.lift (lift g b) w (hc.trans hw.symm), h.lift_fst _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem containsSection_iff_over {X : Over S} (Q : Family G X) (V : Over X.left)
    (g : V ⟶ ((changeBase X.hom).obj G).X) :
    familyContainsSection Q (CategoryTheory.Over.homMk V.hom) (unbasePoint X.hom V G g) ↔
      ∃ y : V ⟶ Q.group.X, y ≫ Q.inclusion.hom.hom = g := by
  constructor
  · rintro ⟨w, hw⟩
    have h := congrArg (fun z ↦ (z ≫ snd G.X X).left) hw
    simp only [Category.assoc, familyProductInclusion, lift_snd] at h
    have hw' : w.left ≫ Q.group.X.hom = V.hom := h
    let y : V ⟶ Q.group.X := CategoryTheory.Over.homMk w.left hw'
    refine ⟨y, ?_⟩
    apply (unbasePoint X.hom V G).injective
    have he := congrArg (· ≫ fst G.X X) hw
    simp only [Category.assoc, familyProductInclusion, lift_fst] at he
    rw [unbasePoint_comp]
    exact he
  · rintro ⟨y, rfl⟩
    refine ⟨(CategoryTheory.Over.map X.hom).map y, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, familyProductInclusion, lift_fst, unbasePoint_comp]
    · simp only [Category.assoc, familyProductInclusion, lift_snd]
      apply CategoryTheory.Over.OverMorphism.ext
      exact CategoryTheory.Over.w y

private def conjugateFamilyProductIso {B : Grp (Over S)} (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (g : X ⟶ G.X) :
    B.X ⊗ X ≅ familyOverBase (conjugateSubgroupFamily j hj hs g) :=
  CategoryTheory.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (pullback.snd B.X.hom X.hom ≫ X.hom) = pullback.fst B.X.hom X.hom ≫ B.X.hom
    rw [Category.id_comp, pullback.condition])

set_option backward.isDefEq.respectTransparency false in
private theorem conjugateFamilyProductIso_comp {B : Grp (Over S)} (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (g : X ⟶ G.X) :
    (conjugateFamilyProductIso j hj hs g).hom ≫ familyProductInclusion (conjugateSubgroupFamily j hj hs g) =
      conjugateOver j g := by
  apply CategoryTheory.Over.OverMorphism.ext
  change 𝟙 _ ≫ (familyProductInclusion (conjugateSubgroupFamily j hj hs g)).left = _
  rw [Category.id_comp, familyProductInclusion_left, conjugateSubgroupFamily_left]

set_option backward.isDefEq.respectTransparency false in
private theorem containsSection_conjugate_iff {B : Grp (Over S)} (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (g : X ⟶ G.X)
    (a : Y ⟶ X) (x : Y ⟶ G.X) :
    familyContainsSection (conjugateSubgroupFamily j hj hs g) a x ↔
      ∃ b : Y ⟶ B.X, (a ≫ g) * (b ≫ j.hom.hom) * (a ≫ g)⁻¹ = x := by
  let e := conjugateFamilyProductIso j hj hs g
  have he := conjugateFamilyProductIso_comp j hj hs g
  have h (w : Y ⟶ B.X ⊗ X) : w ≫ conjugateOver j g = lift x a ↔
      (w ≫ snd B.X X) = a ∧
        (a ≫ g) * ((w ≫ fst B.X X) ≫ j.hom.hom) * (a ≫ g)⁻¹ = x := by
    constructor
    · intro h
      have hsnd := congrArg (· ≫ snd G.X X) h
      simp only [Category.assoc, conjugateOver, lift_snd] at hsnd
      refine ⟨hsnd, ?_⟩
      have hfst := congrArg (· ≫ fst G.X X) h
      simp only [Category.assoc, conjugateOver, lift_fst, MonObj.comp_mul, GrpObj.comp_inv] at hfst
      have hstep : w ≫ snd B.X X ≫ g = a ≫ g := by
        rw [← Category.assoc, hsnd]
      simpa only [hstep, Category.assoc] using hfst
    · rintro ⟨hw, hw'⟩
      have hw'' : w = lift (w ≫ fst B.X X) a := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [hw]
      rw [hw'', lift_comp_conjugateOver, hw']
  constructor
  · rintro ⟨z, hz⟩
    have hfact : (z ≫ e.inv) ≫ conjugateOver j g = lift x a := by
      rw [Category.assoc, ← he, e.inv_hom_id_assoc, hz]
    exact ⟨_, ((h _).mp hfact).2⟩
  · rintro ⟨z, hz⟩
    refine ⟨lift z a ≫ e.hom, ?_⟩
    rw [Category.assoc, he, lift_comp_conjugateOver, hz]

set_option backward.isDefEq.respectTransparency false in
private theorem containsSection_congr_family {B C : Family G X} (h : SameFamily B C)
    (a : Y ⟶ X) (x : Y ⟶ G.X) :
    familyContainsSection B a x ↔ familyContainsSection C a x := by
  obtain ⟨e, he⟩ := h
  let F := Grp.forget (Over X.left) ⋙ CategoryTheory.Over.map X.hom
  let d := F.mapIso e
  have hd : d.hom ≫ familyProductInclusion C = familyProductInclusion B := by
    apply CategoryTheory.Over.OverMorphism.ext
    rw [CategoryTheory.Over.comp_left, familyProductInclusion_left, familyProductInclusion_left]
    exact congrArg (fun z ↦ z.hom.hom.left) he
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b ≫ d.hom, by rw [Category.assoc, hd, hb]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c ≫ d.inv, by rw [Category.assoc, ← hd, d.inv_hom_id_assoc, hc]⟩

end FamilySections

end RelativePoints

section ReductionComparison

variable {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]
variable {G B : Grp (Over (ringSpec R))} {T : Over (ringSpec R)}

private abbrev reduction (I : Ideal D) : coordSpec R (D ⧸ I) ⟶ coordSpec R D :=
  coordSpecMap (Ideal.Quotient.mkₐ R I)

set_option backward.isDefEq.respectTransparency false in
private theorem section_reduction_factors
    {E : Type u} [CommRing E] [Algebra D E] (I : Ideal D)
    (hE : I ≤ RingHom.ker (algebraMap D E)) :
    let V := coordSpec D E
    let U : Over (ringSpec R) := coordSpec R D
    let W := (CategoryTheory.Over.map U.hom).obj V
    ∃ b₀ : W ⟶ coordSpec R (D ⧸ I), b₀ ≫ reduction (R := R) I = CategoryTheory.Over.homMk V.hom := by
  intro V U W
  let q := Ideal.Quotient.liftₐ I (Algebra.ofId D E) hE
  let u := (coordSpecMap q).left
  have hu : u ≫ (reduction (R := R) I).left = V.hom := by
    change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = algebraSpecMap D E
    rw [← Spec.map_comp]
    rfl
  let f : W ⟶ coordSpec R (D ⧸ I) := CategoryTheory.Over.homMk u (by
    change u ≫ (coordSpec R (D ⧸ I)).hom = V.hom ≫ U.hom
    rw [← CategoryTheory.Over.w (reduction (R := R) I), ← Category.assoc, hu])
  exact ⟨f, CategoryTheory.Over.OverMorphism.ext hu⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- After untwisting a lifted conjugating point, the reduced subgroup and
the fixed Borel have the same sections on algebras over the quotient. -/
theorem reducedFamily_factors_iff
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (Q : Family G T) (a : coordSpec R D ⟶ T) (I : Ideal D)
    (g : coordSpec R D ⟶ G.X) (g₀ : coordSpec R (D ⧸ I) ⟶ G.X)
    (hg : reduction (R := R) I ≫ g = g₀)
    (h₀ : SameFamily (conjugateSubgroupFamily j hj hs g₀) (Q.pullback (reduction I ≫ a)))
    (E : Type u) [CommRing E] [Algebra D E] (hE : I ≤ RingHom.ker (algebraMap D E))
    (x : coordSpec D E ⟶ ((changeBase (coordSpec R D).hom).obj G).X) :
    let F := changeBase (coordSpec R D).hom
    let C := Q.pullback a
    let α := innerConjugation (F.obj G) (sectionOfPoint g)
    (∃ y : coordSpec D E ⟶ C.group.X, y ≫ (C.inclusion ≫ α.inv).hom.hom = x) ↔
      ∃ z : coordSpec D E ⟶ (F.obj B).X, z ≫ (F.map j).hom.hom = x := by
  intro F C α
  let U := coordSpec R D
  let V : Over U.left := coordSpec D E
  let W := (CategoryTheory.Over.map U.hom).obj V
  let b : W ⟶ U := CategoryTheory.Over.homMk V.hom
  obtain ⟨b₀, hb₀⟩ := section_reduction_factors (R := R) I hE
  let x' := x ≫ α.hom.hom.hom
  have hi : (∃ y : V ⟶ C.group.X, y ≫ (C.inclusion ≫ α.inv).hom.hom = x) ↔
      ∃ y : V ⟶ C.group.X, y ≫ C.inclusion.hom.hom = x' := by
    let β := (Grp.forget (Over U.left)).mapIso α
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change y ≫ C.inclusion.hom.hom ≫ β.inv = x at hy
      change y ≫ C.inclusion.hom.hom = x ≫ β.hom
      have he := congrArg (· ≫ β.hom) hy
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change y ≫ C.inclusion.hom.hom ≫ β.inv = x
      rw [← Category.assoc, hy]
      change (x ≫ β.hom) ≫ β.inv = x
      simp
  have hcomp : b ≫ a = b₀ ≫ (reduction I ≫ a) := by rw [← Category.assoc, hb₀]
  let u := unbasePoint U.hom V G
  have hg₀ : b₀ ≫ g₀ = b ≫ g := by rw [← hg, ← Category.assoc, hb₀]
  have hx' : u x' = (b ≫ g) * u x * (b ≫ g)⁻¹ := by
    let v : 𝟙_ (Over U.left) ⟶ (F.obj G).X := sectionOfPoint g
    have hx : x' = (toUnit V ≫ v) * x * (toUnit V ≫ v)⁻¹ :=
      comp_innerConjugation (F.obj G) v x
    have hs' : u (toUnit V ≫ v) = b ≫ g := unbasePoint_section g V
    rw [hx, map_mul, map_mul, map_inv, hs']
  rw [hi, ← containsSection_iff_over C V x', Family.containsSection_pullback_iff,
    hcomp, ← Family.containsSection_pullback_iff Q (reduction I ≫ a) b₀,
    ← containsSection_congr_family h₀, containsSection_conjugate_iff,
    hg₀, hx']
  constructor
  · rintro ⟨w, hw⟩
    have hw' : w ≫ j.hom.hom = u x := (mul_left_cancel (mul_right_cancel hw))
    let e := unbasePoint U.hom V B
    refine ⟨e.symm w, u.injective ?_⟩
    change unbasePoint U.hom V G (e.symm w ≫ ((changeBase U.hom).map j).hom.hom) = u x
    rw [unbasePoint_map]
    change e (e.symm w) ≫ j.hom.hom = u x
    rwa [MulEquiv.apply_symm_apply]
  · rintro ⟨w, hw⟩
    let e := unbasePoint U.hom V B
    have he : e w ≫ j.hom.hom = u x := by
      rw [← unbasePoint_map, hw]
    exact ⟨e w, by rw [he]⟩

end ReductionComparison

section RelativeNormalizer

open private finitePresentation_of_closed_over from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {G B : Grp (Over (ringSpec R))}

private def normalizesInFamily {S : Scheme.{u}} {G B : Grp (Over S)}
    (j : B ⟶ G) {T : Over S} (g : T ⟶ G.X) : Prop :=
  (∃ f : B.X ⊗ T ⟶ B.X, f ≫ j.hom.hom = conjugateMap j g) ∧
    ∃ f : B.X ⊗ T ⟶ B.X, f ≫ j.hom.hom = conjugateMap j g⁻¹

set_option backward.isDefEq.respectTransparency false in
private theorem normalizesInFamily_changeBase {S T : Scheme.{u}} {G B : Grp (Over S)}
    (a : T ⟶ S) (j : B ⟶ G) {V : Over T} (g : V ⟶ ((changeBase a).obj G).X) :
    normalizesInFamily ((changeBase a).map j) g ↔
      normalizesInFamily j (unbasePoint a V G g) := by
  unfold normalizesInFamily
  rw [conjugationFactors_changeBase a j g, conjugationFactors_changeBase a j g⁻¹, map_inv]

set_option backward.isDefEq.respectTransparency false in
private theorem subgroupPoint_normalizes {S : Scheme.{u}} {G B : Grp (Over S)}
    (j : B ⟶ G) {T : Over S} (x : T ⟶ B.X) :
    normalizesInFamily j (x ≫ j.hom.hom) := by
  have h (b : T ⟶ B.X) : ∃ f : B.X ⊗ T ⟶ B.X,
      f ≫ j.hom.hom = conjugateMap j (b ≫ j.hom.hom) := by
    refine ⟨(snd _ _ ≫ b) * fst B.X T * (snd _ _ ≫ b)⁻¹, ?_⟩
    simp only [conjugateMap, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]
  exact ⟨h x, (GrpObj.inv_comp x j.hom.hom) ▸ h x⁻¹⟩

set_option backward.isDefEq.respectTransparency false in
private theorem existsConjugationFactorLocus [Module.Free R A] [IsAffine G.X.left]
    [LocallyOfFinitePresentation G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (e : B.X ≅ coordSpec R A) :
    ∃ (N : Over (ringSpec R)) (n : N ⟶ G.X),
      IsClosedImmersion n.left ∧ LocallyOfFinitePresentation n.left ∧
        ∀ (V : Over (ringSpec R)) (g : V ⟶ G.X),
          (∃ f : B.X ⊗ V ⟶ B.X, f ≫ j.hom.hom = conjugateMap j g) ↔
            ∃ w : V ⟶ N, w ≫ n = g := by
  let c := conjugateMap j (𝟙 G.X)
  let D := pullback j.hom.hom c
  let d : D ⟶ B.X ⊗ G.X := pullback.snd j.hom.hom c
  have hh := (IsPullback.of_hasPullback j.hom.hom c).map (CategoryTheory.Over.forget (ringSpec R))
  have hd : IsClosedImmersion d.left := MorphismProperty.of_isPullback hh hj
  have hfp : LocallyOfFinitePresentation j.hom.hom.left := by
    have : LocallyOfFinitePresentation (j.hom.hom.left ≫ G.X.hom) :=
      (CategoryTheory.Over.w j.hom.hom).symm ▸ (inferInstance : LocallyOfFinitePresentation B.X.hom)
    exact finitePresentation_of_closed_over j.hom.hom.left G.X.hom
  have hd' : LocallyOfFinitePresentation d.left := MorphismProperty.of_isPullback hh hfp
  obtain ⟨N, n, hn, hnp, h⟩ := existsClosedFactorizationLocus_of_affine e d hd hd'
  refine ⟨N, n, hn, hnp, fun V g ↦ ?_⟩
  have hc : (B.X ◁ g) ≫ c = conjugateMap j g := by
    simp only [conjugateMap, c, Category.comp_id, MonObj.comp_mul, GrpObj.comp_inv,
      whiskerLeft_fst_assoc, whiskerLeft_snd]
  rw [← h V g]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨pullback.lift f (B.X ◁ g) (hf.trans hc.symm), pullback.lift_snd _ _ _⟩
  · rintro ⟨f, hf⟩
    refine ⟨f ≫ pullback.fst j.hom.hom c, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, show f ≫ d = _ from hf, hc]

set_option backward.isDefEq.respectTransparency false in
private theorem relativeNormalizerLocus [Module.Free R A] [IsAffine G.X.left]
    [LocallyOfFinitePresentation G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (e : B.X ≅ coordSpec R A) :
    ∃ (N : Over (ringSpec R)) (n : N ⟶ G.X),
      IsClosedImmersion n.left ∧ LocallyOfFinitePresentation n.left ∧
        ∀ (V : Over (ringSpec R)) (g : V ⟶ G.X),
          normalizesInFamily j g ↔ ∃ w : V ⟶ N, w ≫ n = g := by
  obtain ⟨M, m, hm, hmp, h⟩ := existsConjugationFactorLocus j hj hs e
  let m' := m ≫ ι[G.X]
  let N := pullback m m'
  let n := pullback.fst m m' ≫ m
  have hinv : IsIso (ι[G.X]).left := (CategoryTheory.Over.forget (ringSpec R)).map_isIso ι[G.X]
  have hm' : IsClosedImmersion m'.left := IsClosedImmersion.comp m.left (ι[G.X]).left
  have hmp' : LocallyOfFinitePresentation m'.left := MorphismProperty.comp_mem _ _ _ hmp inferInstance
  have hh := (IsPullback.of_hasPullback m m').map (CategoryTheory.Over.forget (ringSpec R))
  have hcl : IsClosedImmersion (pullback.fst m m').left :=
    MorphismProperty.of_isPullback hh.flip hm'
  have hfp : LocallyOfFinitePresentation (pullback.fst m m').left :=
    MorphismProperty.of_isPullback hh.flip hmp'
  refine ⟨N, n, IsClosedImmersion.comp _ _, MorphismProperty.comp_mem _ _ _ hfp hmp, ?_⟩
  intro V g
  rw [normalizesInFamily, h V g, h V g⁻¹]
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hq : x ≫ m = y ≫ m' := by
      change x ≫ m = y ≫ m ≫ ι[G.X]
      rw [hx, ← Category.assoc, hy, ← Hom.inv_def, inv_inv]
    exact ⟨pullback.lift x y hq, by simpa [n] using hx⟩
  · rintro ⟨x, hx⟩
    have hf : (x ≫ pullback.fst m m') ≫ m = g := (Category.assoc _ _ _).trans hx
    have hg : (x ≫ pullback.snd m m') ≫ m' = g := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hf]
    have hg' : (x ≫ pullback.snd m m') ≫ m = g⁻¹ := by
      suffices h' : ((x ≫ pullback.snd m m') ≫ m)⁻¹ = g by rw [← h', inv_inv]
      exact (Hom.inv_def _).trans ((Category.assoc _ _ _).trans hg)
    exact ⟨⟨_, hf⟩, ⟨_, hg'⟩⟩

open Specs.GeometricRadicals (IsReductive)
open Specs.GeometricBorelConjugacy (IsKBorel)

set_option backward.isDefEq.respectTransparency false in
private theorem geometricNormalizerFactors {S : Scheme.{u}} {G B : Grp (Over S)}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hB : HasBorelFibres j)
    (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ S)
    (hG : IsReductive (affineFibre (G := G) a))
    (V : Over (ringSpec k)) (g : V ⟶ ((changeBase a).obj G).X) :
    normalizesInFamily ((changeBase a).map j) g ↔
      ∃ y : V ⟶ ((changeBase a).obj B).X, y ≫ ((changeBase a).map j).hom.hom = g := by
  let F := changeBase a
  let A := affineFibre (G := G) a
  obtain ⟨hcl, _⟩ := hB k a
  let C : ClosedSubgroup A.val := ⟨F.obj B, F.map j, hcl⟩
  have hC : IsKBorel C := hasBorelFibres_changeBase hj hB a
    (AlgebraicClosure k) (fieldSpecMap k (AlgebraicClosure k))
  have he := LinearAlgebraicGroups.RootData.BorelNormalizer.groundFieldBorelNormalizer A hG C hC V g
  have hf := LinearAlgebraicGroups.normalizesIff k C.inclusion hcl V g
  exact hf.symm.trans he

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- A smooth closed Borel with free affine coordinates is its own
normalizer if its geometric fibres are Borels in reductive groups. -/
theorem relativeBorelNormalizer [Module.Free R A]
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (e : B.X ≅ coordSpec R A) (hB : HasBorelFibres j)
    (hG : ∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ ringSpec R),
      IsReductive (affineFibre (G := G) a))
    (V : Over (ringSpec R)) (g : V ⟶ G.X) :
    normalizesInFamily j g ↔ ∃ y : V ⟶ B.X, y ≫ j.hom.hom = g := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, n, hn, hnp, hN⟩ := relativeNormalizerLocus j hj hs e
  have hJ := subgroupPoint_normalizes j (𝟙 B.X)
  rw [Category.id_comp] at hJ
  obtain ⟨f, hf⟩ := (hN B.X j.hom.hom).mp hJ
  have hfi : IsClosedImmersion f.left := by
    have : IsClosedImmersion (f.left ≫ n.left) := by
      change IsClosedImmersion (f ≫ n).left
      rwa [hf]
    exact IsClosedImmersion.of_comp_isClosedImmersion f.left n.left
  have hnA : IsAffineHom N.hom := by rw [← CategoryTheory.Over.w n]; infer_instance
  have hnP : LocallyOfFinitePresentation N.hom := by rw [← CategoryTheory.Over.w n]; infer_instance
  have hIso : IsIso f := by
    apply closedImmersion_isIso_of_geometricFibres
    intro k _ _ a
    let F := CategoryTheory.Over.pullback a
    let j' := (changeBase a).map j
    let n' := F.map n
    let f' := F.map f
    have hff : f' ≫ n' = j'.hom.hom := (F.map_comp _ _).symm.trans (congrArg F.map hf)
    let T := F.obj N
    let U := (CategoryTheory.Over.map a).obj T
    let p := unbasePoint a T G n'
    let s := (CategoryTheory.Over.mapPullbackAdj a).homEquiv T N
    have hp : s.symm (𝟙 T) ≫ n = p := by
      rw [← (CategoryTheory.Over.mapPullbackAdj a).homEquiv_naturality_right_symm, Category.id_comp]
      rfl
    have hp' : normalizesInFamily j p := (hN U p).mpr ⟨s.symm (𝟙 T), hp⟩
    have hN' : normalizesInFamily j' n' := (normalizesInFamily_changeBase a j n').mpr hp'
    obtain ⟨d, hd⟩ := (geometricNormalizerFactors j hj hB k a (hG k a) T n').mp hN'
    have hj' : IsClosedImmersion j'.hom.hom.left :=
      MorphismProperty.of_isPullback (pullbackMapSquare a j.hom.hom).flip hj
    have hn' : IsClosedImmersion n'.left := MorphismProperty.of_isPullback (pullbackMapSquare a n).flip hn
    have hjm : Mono j'.hom.hom := CategoryTheory.Over.mono_of_mono_left _
    have hnm : Mono n' := CategoryTheory.Over.mono_of_mono_left _
    refine ⟨d, (cancel_mono j'.hom.hom).mp ?_, (cancel_mono n').mp ?_⟩
    · rw [Category.assoc, hd, hff, Category.id_comp]
    · rw [Category.assoc, hff, hd, Category.id_comp]
  rw [hN V g]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z ≫ inv f, by rw [Category.assoc, ← hf, IsIso.inv_hom_id_assoc, hz]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z ≫ f, by rw [Category.assoc, hf, hz]⟩

end RelativeNormalizer

section GeometricTransporter

variable {S : Scheme.{u}} {G B : Grp (Over S)} {T : Over S}

private def unitOverIso (T : Over S) :
    T ≅ (CategoryTheory.Over.map T.hom).obj (𝟙_ (Over T.left)) :=
  CategoryTheory.Over.isoMk (Iso.refl _) (by
    change 𝟙 T.left ≫ (𝟙 T.left ≫ T.hom) = T.hom
    simp)

private def pointOfSection (g : 𝟙_ (Over T.left) ⟶ ((changeBase T.hom).obj G).X) :
    T ⟶ G.X :=
  (unitOverIso T).hom ≫ unbasePoint T.hom (𝟙_ (Over T.left)) G g

set_option backward.isDefEq.respectTransparency false in
private theorem pointOfSection_left (g : 𝟙_ (Over T.left) ⟶ ((changeBase T.hom).obj G).X) :
    (pointOfSection g).left = g.left ≫ pullback.fst G.X.hom T.hom := by
  change 𝟙 T.left ≫ (unbasePoint T.hom (𝟙_ (Over T.left)) G g).left = _
  rw [Category.id_comp, unbasePoint_left]

set_option backward.isDefEq.respectTransparency false in
private theorem sectionOfPoint_pointOfSection
    (g : 𝟙_ (Over T.left) ⟶ ((changeBase T.hom).obj G).X) :
    sectionOfPoint (pointOfSection g) = g := by
  apply CategoryTheory.Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [sectionOfPoint_fst, pointOfSection_left]
  · exact (CategoryTheory.Over.w (sectionOfPoint (pointOfSection g))).trans (CategoryTheory.Over.w g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pointOfSection_sectionOfPoint (g : T ⟶ G.X) :
    pointOfSection (sectionOfPoint g) = g := by
  apply CategoryTheory.Over.OverMorphism.ext
  rw [pointOfSection_left, sectionOfPoint_fst]

set_option backward.isDefEq.respectTransparency false in
private theorem sectionOfPoint_mul (g h : T ⟶ G.X) :
    sectionOfPoint (g * h) = sectionOfPoint g * sectionOfPoint h := by
  have hpoint (a b : 𝟙_ (Over T.left) ⟶ ((changeBase T.hom).obj G).X) :
      pointOfSection (a * b) = pointOfSection a * pointOfSection b := by
    simp only [pointOfSection, map_mul, MonObj.comp_mul]
  have hh : pointOfSection (sectionOfPoint g * sectionOfPoint h) = g * h := by
    rw [hpoint, pointOfSection_sectionOfPoint, pointOfSection_sectionOfPoint]
  exact (congrArg sectionOfPoint hh).symm.trans (sectionOfPoint_pointOfSection _)

set_option backward.isDefEq.respectTransparency false in
private theorem fieldFamily_isBorel [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] {k : Type u} [Field k] [IsAlgClosed k] {a : ringSpec k ⟶ S}
    (Q : Family G (CategoryTheory.Over.mk a)) (hQ : IsBorelFamily Q) : IsBorel Q.fieldSubgroup := by
  obtain ⟨hc, h⟩ := hQ k (𝟙 (ringSpec k))
  let A := affineFibre (G := G) a
  let d := changeBaseId (ringSpec k)
  exact isBorel_of_isos (G' := A) (d.app A.val) (d.app Q.group)
    (d.hom.naturality Q.inclusion) h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
private theorem geometricBorelFamily_conjugate [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (hB : HasBorelFibres j) (Q : Family G T) (hQ : IsBorelFamily Q)
    {k : Type u} [Field k] [IsAlgClosed k] {a : ringSpec k ⟶ S}
    (x : CategoryTheory.Over.mk a ⟶ T) :
    ∃ g : CategoryTheory.Over.mk a ⟶ G.X, SameFamily (conjugateSubgroupFamily j hj hs g) (Q.pullback x) := by
  let F := changeBase a
  let A := affineFibre (G := G) a
  let C := Q.pullback x
  obtain ⟨hc, hb⟩ := hB k a
  let U : ClosedSubgroup A.val := ⟨F.obj B, F.map j, hc⟩
  let V : ClosedSubgroup A.val := C.fieldSubgroup
  have hV : IsBorel V := fieldFamily_isBorel C (isBorelFamily_pullback Q hQ x)
  have ha : Smooth A.val.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom a))
  have hc' : GeometricallyConnected A.val.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom a))
  have hconn : ConnectedSpace A.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom
  obtain ⟨g, e, he⟩ := GeometricBorelConjugacy.borelsConjugate A ha hconn U V hb hV
  let y : CategoryTheory.Over.mk a ⟶ G.X := pointOfSection g
  refine ⟨y, e, ?_⟩
  apply Grp.hom_ext
  change (e.hom ≫ V.inclusion).hom.hom =
    U.inclusion.hom.hom ≫ (innerConjugationHom (F.obj G) (sectionOfPoint y)).hom.hom
  rw [sectionOfPoint_pointOfSection]
  exact he.trans (comp_innerConjugation A.val g U.inclusion.hom.hom).symm

set_option backward.isDefEq.respectTransparency false in
/-- The affine coefficient locus of conjugacies is surjective. The points over
algebraic closures of residue fields are supplied by geometric conjugacy. -/
theorem existsClosedSurjectiveBorelTransporter {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Free R A]
    {G B : Grp (Over (ringSpec R))} {T : Over (ringSpec R)}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom] [IsAffine T.left]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (hB : HasBorelFibres j) (eB : B.X ≅ coordSpec R A) (Q : Family G T) (hQ : IsBorelFamily Q) :
    ∃ (Z : Over (ringSpec R)) (l : Z ⟶ G.X ⊗ T),
      IsClosedImmersion l.left ∧ LocallyOfFinitePresentation l.left ∧
      Surjective (l ≫ snd G.X T).left ∧
        ∀ (U : Over (ringSpec R)) (a : U ⟶ T) (g : U ⟶ G.X),
          SameFamily (conjugateSubgroupFamily j hj hs g) (Q.pullback a) ↔
            ∃ z : U ⟶ Z, z ≫ l = lift g a := by
  obtain ⟨Z, l, hl, hfp, hZ⟩ := existsConjugateContainmentLocus j eB Q
  have heq (U : Over (ringSpec R)) (a : U ⟶ T) (g : U ⟶ G.X) :
      SameFamily (conjugateSubgroupFamily j hj hs g) (Q.pullback a) ↔
        ∃ z : U ⟶ Z, z ≫ l = lift g a :=
    (conjugateContained_iff_sameFamily j hj hs hB Q hQ a g).symm.trans (hZ U a g)
  refine ⟨Z, l, hl, hfp, ⟨?_⟩, heq⟩
  intro x
  let K := AlgebraicClosure (T.left.residueField x)
  let a := fieldSpecMap (T.left.residueField x) K ≫ T.left.fromSpecResidueField x
  let U := CategoryTheory.Over.mk (a ≫ T.hom)
  let b : U ⟶ T := CategoryTheory.Over.homMk a
  obtain ⟨g, hg⟩ := geometricBorelFamily_conjugate j hj hs hB Q hQ b
  obtain ⟨z, hz⟩ := (heq U b g).mp hg
  have hbase : z ≫ (l ≫ snd G.X T) = b := by rw [← Category.assoc, hz, lift_snd]
  have ha : a (IsLocalRing.closedPoint K) = x := by
    change T.left.fromSpecResidueField x
      ((fieldSpecMap (T.left.residueField x) K) (IsLocalRing.closedPoint K)) = x
    rw [show (fieldSpecMap (T.left.residueField x) K) (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint (T.left.residueField x) from Subsingleton.elim _ _]
    exact Scheme.fromSpecResidueField_apply _ _
  let p : U.left := IsLocalRing.closedPoint K
  refine ⟨z.left p, ?_⟩
  have h := congrArg (fun f : U ⟶ T ↦ f.left p) hbase
  change (z.left ≫ (l ≫ snd G.X T).left) p = b.left p at h
  rw [Scheme.Hom.comp_apply] at h
  exact h.trans ha

end GeometricTransporter

section FamilyComparisonDescent

variable {S : Scheme.{u}} {G : Grp (Over S)} {X Y Z : Over S}

set_option backward.isDefEq.respectTransparency false in
/-- Equality of families as closed subgroup schemes is reflected by a
faithfully flat quasi-compact cover of the test scheme. -/
theorem sameFamily_of_same_pullback (a : Y ⟶ X) [Surjective a.left] [Flat a.left]
    [QuasiCompact a.left] {B C : Family G X}
    (h : SameFamily (B.pullback a) (C.pullback a)) : SameFamily B C := by
  obtain ⟨e, he⟩ := h
  let F := changeBase a.left
  let d := compareAmbient a G
  have he' : (e.hom ≫ F.map C.inclusion) ≫ d.inv = F.map B.inclusion ≫ d.inv := by
    rw [Category.assoc]
    exact he
  have hh : e.hom ≫ F.map C.inclusion = F.map B.inclusion := (cancel_mono d.inv).mp he'
  have hhc : e.inv ≫ F.map B.inclusion = F.map C.inclusion := by
    rw [← hh, e.inv_hom_id_assoc]
  have := B.closed
  have := C.closed
  have hmB : Mono B.inclusion.hom.hom := CategoryTheory.Over.mono_of_mono_left _
  have hmC : Mono C.inclusion.hom.hom := CategoryTheory.Over.mono_of_mono_left _
  obtain ⟨f, hf⟩ := factorsOfFactorsPullback a.left C.inclusion.hom.hom B.inclusion.hom.hom
    ⟨e.hom.hom.hom, congrArg (fun q ↦ q.hom.hom) hh⟩
  obtain ⟨g, hg⟩ := factorsOfFactorsPullback a.left B.inclusion.hom.hom C.inclusion.hom.hom
    ⟨e.inv.hom.hom, congrArg (fun q ↦ q.hom.hom) hhc⟩
  let m : B.group.X ≅ C.group.X :=
    ⟨f, g,
      (cancel_mono B.inclusion.hom.hom).mp (by simp only [Category.assoc, hg, hf, Category.id_comp]),
      (cancel_mono C.inclusion.hom.hom).mp (by simp only [Category.assoc, hf, hg, Category.id_comp])⟩
  exact ⟨subgroupIso B.inclusion C.inclusion m hf, Grp.hom_ext _ _ hf⟩

set_option backward.isDefEq.respectTransparency false in
private theorem sameFamily_of_iso_over_product {B C : Family G X}
    (e : familyOverBase B ≅ familyOverBase C)
    (he : e.hom ≫ familyProductInclusion C = familyProductInclusion B) :
    SameFamily B C := by
  have wp : e.hom.left ≫ C.group.X.hom = B.group.X.hom := by
    have h := congrArg (fun f ↦ (f ≫ snd G.X X).left) he
    simp only [Category.assoc, familyProductInclusion, lift_snd, CategoryTheory.Over.comp_left] at h
    exact h
  let d : B.group.X ≅ C.group.X := CategoryTheory.Over.isoMk ((CategoryTheory.Over.forget S).mapIso e) wp
  have hd : d.hom ≫ C.inclusion.hom.hom = B.inclusion.hom.hom := by
    apply CategoryTheory.Over.OverMorphism.ext
    have h := congrArg CategoryTheory.Over.Hom.left he
    rwa [CategoryTheory.Over.comp_left, familyProductInclusion_left, familyProductInclusion_left] at h
  have := C.closed
  have : Mono C.inclusion.hom.hom := CategoryTheory.Over.mono_of_mono_left _
  exact ⟨subgroupIso B.inclusion C.inclusion d hd, Grp.hom_ext _ _ hd⟩

set_option backward.isDefEq.respectTransparency false in
/-- Successive pullbacks and pullback along the composite give the same
subgroup family. -/
theorem sameFamily_pullback_comp (B : Family G X) (a : Y ⟶ X) (b : Z ⟶ Y) :
    SameFamily ((B.pullback a).pullback b) (B.pullback (b ≫ a)) := by
  have h₁ := (familyProductPullback_over (B.pullback a) b).paste_vert
    (familyProductPullback_over B a)
  rw [← MonoidalCategory.whiskerLeft_comp] at h₁
  have h₂ := familyProductPullback_over B (b ≫ a)
  let e := h₁.isoPullback ≪≫ h₂.isoPullback.symm
  refine sameFamily_of_iso_over_product e ?_
  change (h₁.isoPullback.hom ≫ h₂.isoPullback.inv) ≫ _ = _
  rw [Category.assoc, h₂.isoPullback_inv_fst, h₁.isoPullback_hom_fst]

end FamilyComparisonDescent

section ScalarSection

variable {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}

set_option backward.isDefEq.respectTransparency false in
private def affineSection (v : coordSpec R R ⟶ G.X) : 𝟙_ (Over (ringSpec R)) ⟶ G.X := by
  let F := algSpec (CommRingCat.of R)
  letI : F.Braided := AlgebraicGeometry.braidedAlgSpec
  exact Functor.LaxMonoidal.ε F ≫ v

private theorem affineSection_eval {D : Type u} [CommRing D] [Algebra R D]
    (v : coordSpec R R ⟶ G.X) :
    toUnit (coordSpec R D) ≫ affineSection v =
      mapAffinePointAlong G (Algebra.ofId R D) v := by
  apply CategoryTheory.Over.OverMorphism.ext
  simp only [CategoryTheory.Over.comp_left, affineSection, CategoryTheory.Over.toUnit_left]
  rfl

end ScalarSection

section TwistedBorelPoints

variable {R : Type u} [CommRing R] {G H : Grp (Over (ringSpec R))}

private theorem scalarPoint_reduces_to_one (I : Ideal R)
    (v : coordSpec R R ⟶ G.X) (hv : mapAffinePointAlong G (Ideal.Quotient.mkₐ R I) v = 1)
    (D : Type u) [CommRing D] [Algebra R D] (hD : I ≤ RingHom.ker (algebraMap R D)) :
    mapAffinePointAlong G (Algebra.ofId R D) v = 1 := by
  let b := Ideal.Quotient.liftₐ I (Algebra.ofId R D) hD
  have hb : b.comp (Ideal.Quotient.mkₐ R I) = Algebra.ofId R D := rfl
  calc
    _ = mapAffinePointAlong G (b.comp (Ideal.Quotient.mkₐ R I)) v :=
      congrArg (fun f ↦ mapAffinePointAlong G f v) hb.symm
    _ = mapAffinePointAlong G b (mapAffinePointAlong G (Ideal.Quotient.mkₐ R I) v) :=
      mapAffinePointAlong_comp _ _ _
    _ = 1 := (congrArg (mapAffinePointAlong G b) hv).trans (map_one _)

private theorem comp_inverse_innerConjugation {C : Type*} [Category* C]
    [CartesianMonoidalCategory C] (W : Grp C) (s : 𝟙_ C ⟶ W.X) {X : C} (p : X ⟶ W.X) :
    p ≫ (innerConjugation W s).inv.hom.hom = (toUnit X ≫ s)⁻¹ * p * (toUnit X ≫ s) := by
  change p ≫ (innerConjugationHom W s⁻¹).hom.hom = _
  rw [comp_innerConjugation, GrpObj.comp_inv, inv_inv]

set_option backward.isDefEq.respectTransparency false in
private theorem comp_inverse_conjugation {D : Type u} [CommRing D] [Algebra R D]
    (i : H ⟶ G) (p : coordSpec R D ⟶ H.X) (v : coordSpec R R ⟶ G.X) :
    p ≫ (i ≫ (innerConjugation G (affineSection v)).inv).hom.hom =
      (mapAffinePointAlong G (Algebra.ofId R D) v)⁻¹ * (p ≫ i.hom.hom) *
        mapAffinePointAlong G (Algebra.ofId R D) v := by
  let d := (innerConjugation G (affineSection v)).inv.hom.hom
  change p ≫ i.hom.hom ≫ d = _
  rw [← Category.assoc]
  have hc := comp_inverse_innerConjugation G (affineSection v) (p ≫ i.hom.hom)
  rw [affineSection_eval (D := D) v] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
private theorem polynomialOrbit_congr_of_points {D : Type u} [CommRing D] [Algebra R D]
    {c d : UnitCocharacter G} (h : ∀ (E : CommAlgCat R) (t : Eˣ), c.point E t = d.point E t)
    (p : coordSpec R D ⟶ G.X) :
    HasPolynomialOrbit c p ↔ HasPolynomialOrbit d p := by
  have hh : orbitPoint c D p = orbitPoint d D p := by
    let t := laurentVariable D 1
    let E := CommAlgCat.of R (LaurentPolynomial D)
    let x := mapAffinePointAlong G (laurentConstants R D) p
    change c.point E t * x * (c.point E t)⁻¹ = d.point E t * x * (d.point E t)⁻¹
    rw [h E t]
  unfold HasPolynomialOrbit
  rw [hh]

end TwistedBorelPoints

section SquareZeroConjugacy

variable {R : Type u} [CommRing R] {G H B : Grp (Over (ringSpec R))}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 220000 in
/-- If the reduction of a smooth subgroup is the attracting subgroup of
a cocharacter, conjugation by a section lifting the identity puts the
smooth subgroup inside the attracting subgroup over the original ring. -/
theorem subgroupFactorsAfterSquareZeroConjugation {A D : Type u} [CommRing A] [Algebra R A]
    [CommRing D] [Algebra R D]
    (eG : coordSpec R A ≅ G.X) (eH : coordSpec R D ≅ H.X)
    (i : H ⟶ G) (hi : IsClosedImmersion i.hom.hom.left) (hs : Smooth H.X.hom)
    (j : B ⟶ G) (c : UnitCocharacter G) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hB : ∀ (E : Type u) [CommRing E] [Algebra R E] (g : coordSpec R E ⟶ G.X),
      HasPolynomialOrbit c g ↔ ∃ b : coordSpec R E ⟶ B.X, b ≫ j.hom.hom = g)
    (hred : ∀ (E : Type u) [CommRing E] [Algebra R E], I ≤ RingHom.ker (algebraMap R E) →
      ∀ g : coordSpec R E ⟶ G.X,
        HasPolynomialOrbit c g ↔ ∃ h : coordSpec R E ⟶ H.X, h ≫ i.hom.hom = g) :
    ∃ v : coordSpec R R ⟶ G.X,
      mapAffinePointAlong G (Ideal.Quotient.mkₐ R I) v = 1 ∧
      ∃ f : H.X ⟶ B.X,
        f ≫ j.hom.hom = (i ≫ (innerConjugation G (affineSection v)).inv).hom.hom := by
  have hkill : I ≤ RingHom.ker (algebraMap R (LaurentPolynomial (R ⧸ I))) := by
    intro r hr
    change LaurentPolynomial.C (Ideal.Quotient.mk I r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  let t := laurentVariable (R ⧸ I) 1
  obtain ⟨x, hx⟩ := (hred (LaurentPolynomial (R ⧸ I)) hkill _).mp
    (HasPolynomialOrbit.cocharacterPoint c t)
  have : Mono i.hom.hom := CategoryTheory.Over.mono_of_mono_left _
  obtain ⟨d, hd⟩ := existsCocharacterLiftOfFactor eH hs i I hI c x hx
  obtain ⟨v, hv, hvd⟩ := UnitCocharacter.existsConjugationOfAgreeModulo eG I hI hd
  let i' := i ≫ (innerConjugation G (affineSection v)).inv
  have hi' : IsClosedImmersion i'.hom.hom.left := by
    have : IsIso ((innerConjugation G (affineSection v)).inv.hom.hom.left) :=
      (Grp.forget (Over (ringSpec R)) ⋙ CategoryTheory.Over.forget (ringSpec R)).map_isIso
        (innerConjugation G (affineSection v)).inv
    exact IsClosedImmersion.comp _ _
  have hcochar (E : CommAlgCat R) (u : Eˣ) : (d.mapGroup i').point E u = c.point E u := by
    change d.point E u ≫ i'.hom.hom = c.point E u
    let w : affinePoints G E := mapAffinePointAlong G (Algebra.ofId R E) v
    let z : affinePoints G E := c.point E u
    let y : affinePoints G E := d.point E u ≫ i.hom.hom
    have h : w * z * w⁻¹ = y := hvd E u
    change d.point E u ≫ (i ≫ (innerConjugation G (affineSection v)).inv).hom.hom = z
    rw [comp_inverse_conjugation]
    change w⁻¹ * y * w = z
    calc
      _ = w⁻¹ * (w * z * w⁻¹) * w := congrArg (fun p ↦ w⁻¹ * p * w) h.symm
      _ = _ := by group
  have hH := polynomialOrbit_of_squareZero eH d I hI (fun E _ _ hE p ↦ by
    apply HasPolynomialOrbit.of_groupHom eG eH d i' hi' p
    apply (polynomialOrbit_congr_of_points hcochar (p ≫ i'.hom.hom)).mpr
    have he : mapAffinePointAlong G (Algebra.ofId R E) v = 1 :=
      scalarPoint_reduces_to_one I v hv E hE
    change HasPolynomialOrbit c
      (p ≫ (i ≫ (innerConjugation G (affineSection v)).inv).hom.hom)
    rw [comp_inverse_conjugation, he, inv_one, one_mul, mul_one]
    exact (hred E hE _).mpr ⟨p, rfl⟩)
  have h := HasPolynomialOrbit.mapGroup d i' eH.hom (hH D eH.hom)
  have hw := (polynomialOrbit_congr_of_points hcochar (eH.hom ≫ i'.hom.hom)).mp h
  obtain ⟨b, hb⟩ := (hB D _).mp hw
  exact ⟨v, hv, eH.inv ≫ b, by rw [Category.assoc, hb, eH.inv_hom_id_assoc]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Smooth closed subgroups with Borel fibres that agree on the square-zero
reduction are conjugate by a point reducing to the identity, provided the
fixed Borel is given by the polynomial-orbit condition. -/
theorem borelConjugacyOfSquareZeroReduction {A D : Type u} [CommRing A] [Algebra R A]
    [CommRing D] [Algebra R D] [IsAffineHom G.X.hom]
    (eG : coordSpec R A ≅ G.X) (eH : coordSpec R D ≅ H.X)
    (i : H ⟶ G) (hi : IsClosedImmersion i.hom.hom.left)
    (hsmH : Smooth H.X.hom) (hH : HasBorelFibres i)
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left)
    (hsmB : Smooth B.X.hom) (hB : HasBorelFibres j)
    (c : UnitCocharacter G) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hpoints : ∀ (E : Type u) [CommRing E] [Algebra R E] (g : coordSpec R E ⟶ G.X),
      HasPolynomialOrbit c g ↔ ∃ b : coordSpec R E ⟶ B.X, b ≫ j.hom.hom = g)
    (hred : ∀ (E : Type u) [CommRing E] [Algebra R E], I ≤ RingHom.ker (algebraMap R E) →
      ∀ g : coordSpec R E ⟶ G.X,
        HasPolynomialOrbit c g ↔ ∃ h : coordSpec R E ⟶ H.X, h ≫ i.hom.hom = g) :
    ∃ v : coordSpec R R ⟶ G.X,
      mapAffinePointAlong G (Ideal.Quotient.mkₐ R I) v = 1 ∧
      ∃ e : B ≅ H, e.hom ≫ i = j ≫ (innerConjugation G (affineSection v)).hom := by
  obtain ⟨v, hv, f, hf⟩ :=
    subgroupFactorsAfterSquareZeroConjugation eG eH i hi hsmH j c I hI hpoints hred
  let w := innerConjugation G (affineSection v)
  have : IsIso w.inv.hom.hom.left :=
    (Grp.forget (Over (ringSpec R)) ⋙ CategoryTheory.Over.forget (ringSpec R)).map_isIso w.inv
  have hclosed : IsClosedImmersion (i ≫ w.inv).hom.hom.left :=
    IsClosedImmersion.comp i.hom.hom.left w.inv.hom.hom.left
  have hBorel : HasBorelFibres (i ≫ w.inv) := hasBorelFibres_comp_iso w.symm hH
  obtain ⟨e, he⟩ := subgroupIsoOfBorelInclusion (i ≫ w.inv) j hclosed hj hsmH hsmB hBorel hB f hf
  refine ⟨v, hv, e.symm, ?_⟩
  change e.inv ≫ i = j ≫ w.hom
  have he' : e.hom ≫ j ≫ w.hom = i := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using congrArg (· ≫ w.hom) he
  rw [← he', e.inv_hom_id_assoc]

end SquareZeroConjugacy

section LiftConjugacy
variable {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]
variable {G B : Grp (Over (ringSpec R))} {T : Over (ringSpec R)}

set_option backward.isDefEq.respectTransparency false in
private theorem pointOfSection_reduces_one (I : Ideal D)
    (v : coordSpec D D ⟶ ((changeBase (coordSpec R D).hom).obj G).X)
    (hv : mapAffinePointAlong ((changeBase (coordSpec R D).hom).obj G)
      (Ideal.Quotient.mkₐ D I) v = 1) :
    reduction (R := R) I ≫ pointOfSection (affineSection v) = 1 := by
  let U := coordSpec R D
  let V : Over U.left := coordSpec D (D ⧸ I)
  let U₀ := coordSpec R (D ⧸ I)
  let r := reduction (R := R) I
  let W := (Over.map U.hom).obj V
  let b : W ⟶ U := Over.homMk V.hom
  let g : U ⟶ G.X := pointOfSection (affineSection v)
  have h : toUnit V ≫ sectionOfPoint g = 1 := by
    rw [show g = pointOfSection (affineSection v) from rfl, sectionOfPoint_pointOfSection]
    exact (affineSection_eval (D := D ⧸ I) v).trans hv
  have hg : b ≫ g = 1 := by
    rw [← unbasePoint_section g V, h, map_one]
  let w : U₀ ⟶ W :=
    Over.homMk (𝟙 U₀.left) ((Category.id_comp _).trans (Over.w r))
  have hw : w ≫ b = r := by
    apply Over.OverMorphism.ext
    change 𝟙 U₀.left ≫ r.left = r.left
    exact Category.id_comp _
  change r ≫ g = 1
  rw [← hw, Category.assoc, hg, MonObj.comp_one]


private theorem innerConjugationHom_mul {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    (G : Grp C) (g h : 𝟙_ C ⟶ G.X) :
    innerConjugationHom G h ≫ innerConjugationHom G g =
      innerConjugationHom G (g * h) := by
  apply Grp.hom_ext
  change (innerConjugationHom G h).hom.hom ≫ (innerConjugationHom G g).hom.hom =
    (innerConjugationHom G (g * h)).hom.hom
  have h₀ (p : 𝟙_ C ⟶ G.X) :
      (innerConjugationHom G p).hom.hom = (toUnit G.X ≫ p) * 𝟙 _ * (toUnit G.X ≫ p)⁻¹ := by
    simpa only [Category.id_comp] using comp_innerConjugation G p (𝟙 G.X)
  rw [comp_innerConjugation, h₀ h, h₀ (g * h), MonObj.comp_mul]
  group


end LiftConjugacy

section ConjugateComparison

variable {S : Scheme.{u}} {G B : Grp (Over S)} {T : Over S}

private theorem conjugateSubgroupFamily_inclusion (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (g : T ⟶ G.X) :
    (conjugateSubgroupFamily j hj hs g).inclusion =
      (changeBase T.hom).map j ≫ innerConjugationHom _ (sectionOfPoint g) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sameFamily_after_correction (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (C : Family G T)
    (g : T ⟶ G.X) (t : 𝟙_ (Over T.left) ⟶ ((changeBase T.hom).obj G).X)
    (e : (changeBase T.hom).obj B ≅ C.group)
    (he : e.hom ≫ C.inclusion ≫ (innerConjugation _ (sectionOfPoint g)).inv =
      (changeBase T.hom).map j ≫ innerConjugationHom _ t) :
    SameFamily (conjugateSubgroupFamily j hj hs (g * pointOfSection t)) C := by
  refine ⟨e, ?_⟩
  let A := (changeBase T.hom).obj G
  let s : 𝟙_ (Over T.left) ⟶ A.X := sectionOfPoint g
  let a := innerConjugation A s
  let l := (changeBase T.hom).map j
  have h₁ : e.hom ≫ C.inclusion = (l ≫ innerConjugationHom A t) ≫ a.hom := by
    have he' : (e.hom ≫ C.inclusion) ≫ a.inv = l ≫ innerConjugationHom A t :=
      (Category.assoc _ _ _).trans he
    calc
      e.hom ≫ C.inclusion = ((e.hom ≫ C.inclusion) ≫ a.inv) ≫ a.hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = _ := congrArg (· ≫ a.hom) he'
  have h₂ : sectionOfPoint (g * pointOfSection t) = s * t :=
    (sectionOfPoint_mul g (pointOfSection t)).trans
      (congrArg (s * ·) (sectionOfPoint_pointOfSection t))
  rw [conjugateSubgroupFamily_inclusion, h₂, h₁, Category.assoc]
  exact congrArg (l ≫ ·) (innerConjugationHom_mul A s t)

end ConjugateComparison

open private smoothAffine_lift from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

section LiftConjugacy
variable {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]
variable {G B : Grp (Over (ringSpec R))} {T : Over (ringSpec R)}
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- Conjugating sections lift across a square-zero quotient when the
reference Borel is the attracting subgroup of a cocharacter. -/
theorem liftBorelConjugacy [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hsmB : Smooth B.X.hom)
    (hB : HasBorelFibres j) (c : UnitCocharacter G)
    (hpoints : ∀ (E : Type u) [CommRing E] [Algebra R E] (x : coordSpec R E ⟶ G.X),
      HasPolynomialOrbit c x ↔ ∃ y : coordSpec R E ⟶ B.X, y ≫ j.hom.hom = x)
    (Q : Family G T) (hQ : IsBorelFamily Q) (a : coordSpec R D ⟶ T)
    (I : Ideal D) (hI : I ^ 2 = ⊥) (g₀ : coordSpec R (D ⧸ I) ⟶ G.X)
    (h₀ : SameFamily (conjugateSubgroupFamily j hj hsmB g₀) (Q.pullback (reduction I ≫ a))) :
    ∃ g : coordSpec R D ⟶ G.X, reduction I ≫ g = g₀ ∧
      SameFamily (conjugateSubgroupFamily j hj hsmB g) (Q.pullback a) := by
  have hA : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨g, hg⟩ := smoothAffine_lift (S := CommRingCat.of R)
    (inferInstance : Smooth G.X.hom) (CommAlgCat.of R D) I hI g₀
  change reduction (R := R) I ≫ g = g₀ at hg
  let U := coordSpec R D
  have hU : IsAffine U.left := inferInstanceAs (IsAffine (ringSpec D))
  let F := changeBase U.hom
  let A := F.obj G
  let C := Q.pullback a
  let α := innerConjugation A (sectionOfPoint g)
  let i := C.inclusion ≫ α.inv
  let j' := F.map j
  let c' := c.changeScalars (A := D)
  have hAc : IsAffineHom A.X.hom :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.X.hom U.hom)
      ‹IsAffineHom G.X.hom›
  have hAA : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  have hCA : IsAffine C.group.X.left := by
    have := C.closed
    exact isAffine_of_isAffineHom C.inclusion.hom.hom.left
  have hci : IsClosedImmersion i.hom.hom.left := by
    have := C.closed
    have : IsIso α.inv.hom.hom.left := (Grp.forget (Over U.left) ⋙ Over.forget U.left).map_isIso α.inv
    exact IsClosedImmersion.comp _ _
  have hcj : IsClosedImmersion j'.hom.hom.left :=
    MorphismProperty.of_isPullback (pullbackMapSquare U.hom j.hom.hom).flip hj
  have hFsm : Smooth (F.obj B).X.hom :=
    inferInstanceAs (Smooth (pullback.snd B.X.hom U.hom))
  have hb : HasBorelFibres j' := hasBorelFibres_changeBase hj hB U.hom
  have hc : HasBorelFibres i :=
    hasBorelFibres_comp_iso α.symm (isBorelFamily_pullback Q hQ a)
  obtain ⟨AG, ⟨eG⟩⟩ := (essImage_algSpec (R := CommRingCat.of D)).mpr hAA
  obtain ⟨AH, ⟨eH⟩⟩ := (essImage_algSpec (R := CommRingCat.of D)).mpr hCA
  let eG' : coordSpec D AG.unop ≅ A.X := eG
  let eH' : coordSpec D AH.unop ≅ C.group.X := eH
  have hp (E : Type u) [CommRing E] [Algebra D E] (x : coordSpec D E ⟶ A.X) :
      HasPolynomialOrbit c' x ↔ ∃ y : coordSpec D E ⟶ (F.obj B).X, y ≫ j'.hom.hom = x :=
    attractingSubgroup_changeScalars c j hpoints (CommAlgCat.of D E) x
  have hr (E : Type u) [CommRing E] [Algebra D E] (hE : I ≤ RingHom.ker (algebraMap D E))
      (x : coordSpec D E ⟶ A.X) : HasPolynomialOrbit c' x ↔
        ∃ y : coordSpec D E ⟶ C.group.X, y ≫ i.hom.hom = x :=
    (hp E x).trans (reducedFamily_factors_iff j hj hsmB Q a I g g₀ hg h₀ E hE x).symm
  obtain ⟨v, hv, e, he⟩ :=
    borelConjugacyOfSquareZeroReduction eG' eH' i hci C.smooth hc j' hcj hFsm hb c' I hI hp hr
  let b : U ⟶ G.X := pointOfSection (affineSection v)
  have hb₀ : reduction I ≫ b = 1 := pointOfSection_reduces_one I v hv

  have hgb : reduction I ≫ (g * b) = g₀ := by rw [MonObj.comp_mul, hg, hb₀, mul_one]
  have hsame := sameFamily_after_correction j hj hsmB C g (affineSection v) e
    ((Category.assoc e.hom C.inclusion α.inv).symm.trans he)
  exact ⟨g * b, hgb, hsame⟩


end LiftConjugacy

section SmoothTransporter

open LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter (smooth_of_squareZeroLifting)

variable {R A C : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing C] [Algebra R C]
variable {G B : Grp (Over (ringSpec R))}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
/-- The affine transporter of an attracting Borel to a smooth closed
family with Borel fibres is a smooth faithfully flat cover. -/
theorem existsSmoothBorelTransporter [Module.Free R A] [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hsmB : Smooth B.X.hom)
    (hB : HasBorelFibres j) (eB : B.X ≅ coordSpec R A) (c : UnitCocharacter G)
    (hpoints : ∀ (E : Type u) [CommRing E] [Algebra R E] (x : coordSpec R E ⟶ G.X),
      HasPolynomialOrbit c x ↔ ∃ y : coordSpec R E ⟶ B.X, y ≫ j.hom.hom = x)
    (Q : Family G (coordSpec R C)) (hQ : IsBorelFamily Q) :
    let T := coordSpec R C
    ∃ (Z : Over (ringSpec R)) (l : Z ⟶ G.X ⊗ T),
      IsClosedImmersion l.left ∧ Smooth (l ≫ snd G.X T).left ∧
      Surjective (l ≫ snd G.X T).left ∧ QuasiCompact (l ≫ snd G.X T).left ∧
        ∀ (U : Over (ringSpec R)) (a : U ⟶ T) (g : U ⟶ G.X),
          SameFamily (conjugateSubgroupFamily j hj hsmB g) (Q.pullback a) ↔
            ∃ z : U ⟶ Z, z ≫ l = lift g a := by
  intro T
  have hT : IsAffine T.left := inferInstanceAs (IsAffine (ringSpec C))
  obtain ⟨Z, l, hl, hfp, hsu, hZ⟩ := existsClosedSurjectiveBorelTransporter j hj hsmB hB eB Q hQ
  let f := l ≫ snd G.X T
  have : IsAffine (G.X ⊗ T).left := inferInstanceAs (IsAffine (pullback G.X.hom T.hom))
  have : IsAffine Z.left := isAffine_of_isAffineHom l.left
  have hsp : LocallyOfFinitePresentation (snd G.X T).left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom T.hom))
  have hfp' : LocallyOfFinitePresentation f.left :=
    MorphismProperty.comp_mem _ _ _ hfp hsp
  have hqc : QuasiCompact f.left := by
    have hqp : QuasiCompact (snd G.X T).left :=
      inferInstanceAs (QuasiCompact (pullback.snd G.X.hom T.hom))
    exact MorphismProperty.comp_mem _ _ _ inferInstance hqp
  refine ⟨Z, l, hl, ?_, hsu, hqc, hZ⟩
  apply smooth_of_squareZeroLifting (R := CommRingCat.of C)
  intro D I hI v z hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (v ≫ T.hom)
  let : Algebra R D := φ.hom.toAlgebra
  let S := coordSpec R D
  let r := reduction (R := R) I
  let a : S ⟶ T := Over.homMk v hφ.symm
  let z' : coordSpec R (D ⧸ I) ⟶ Z := Over.homMk z (by
    change z ≫ Z.hom = (coordSpec R (D ⧸ I)).hom
    rw [← Over.w f, ← Category.assoc, ← hz, Category.assoc, ← hφ]
    exact Over.w r)
  have ha : z' ≫ f = r ≫ a := Over.OverMorphism.ext hz.symm
  let g₀ := z' ≫ l ≫ fst G.X T
  have hz' : z' ≫ l = lift g₀ (r ≫ a) := by
    apply CartesianMonoidalCategory.hom_ext
    · exact (Category.assoc z' l (fst G.X T)).trans (lift_fst g₀ (r ≫ a)).symm
    · rw [lift_snd, Category.assoc]
      exact ha
  have h₀ := (hZ (coordSpec R (D ⧸ I)) (r ≫ a) g₀).mpr ⟨z', hz'⟩
  obtain ⟨g, hg, hconj⟩ := liftBorelConjugacy j hj hsmB hB c hpoints Q hQ a I hI g₀ h₀
  obtain ⟨y, hy⟩ := (hZ S a g).mp hconj
  have hya : y ≫ f = a := by rw [← Category.assoc, hy, lift_snd]
  have hmon : Mono l := Over.mono_of_mono_left _
  have hry : r ≫ y = z' := by
    apply (cancel_mono l).mp
    rw [Category.assoc, hy, hz']
    apply CartesianMonoidalCategory.hom_ext
    · change (r ≫ lift g a) ≫ fst G.X T = lift g₀ (r ≫ a) ≫ fst G.X T
      calc
        _ = r ≫ g := (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (lift_fst g a))
        _ = g₀ := hg
        _ = _ := (lift_fst g₀ (r ≫ a)).symm
    · change (r ≫ lift g a) ≫ snd G.X T = lift g₀ (r ≫ a) ≫ snd G.X T
      rw [Category.assoc, lift_snd, lift_snd]
  exact ⟨y.left, congrArg Over.Hom.left hya, congrArg Over.Hom.left hry⟩

end SmoothTransporter

section FamilyCalculus

variable {S : Scheme.{u}} {G B : Grp (Over S)} {T U : Over S}

private theorem sameFamily_refl (Q : Family G T) : SameFamily Q Q :=
  ⟨Iso.refl _, Category.id_comp _⟩

private theorem sameFamily_symm {P Q : Family G T} (h : SameFamily P Q) : SameFamily Q P := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]⟩

private theorem sameFamily_trans {P Q H : Family G T}
    (h : SameFamily P Q) (h' : SameFamily Q H) : SameFamily P H := by
  obtain ⟨e, he⟩ := h
  obtain ⟨f, hf⟩ := h'
  exact ⟨e ≪≫ f, by rw [Iso.trans_hom, Category.assoc, hf, he]⟩

set_option backward.isDefEq.respectTransparency false in
theorem sameFamily_iff_containsSection {P Q : Family G T} :
    SameFamily P Q ↔ ∀ (V : Over S) (a : V ⟶ T) (g : V ⟶ G.X),
      familyContainsSection P a g ↔ familyContainsSection Q a g := by
  refine ⟨fun h _ ↦ containsSection_congr_family h, ?_⟩
  intro h
  let i := familyProductInclusion P
  let j := familyProductInclusion Q
  have hi : IsClosedImmersion i.left := by
    rw [familyProductInclusion_left]
    exact P.closed
  have hj : IsClosedImmersion j.left := by
    rw [familyProductInclusion_left]
    exact Q.closed
  have him : Mono i := Over.mono_of_mono_left i
  have hjm : Mono j := Over.mono_of_mono_left j
  have hP : familyContainsSection P (i ≫ snd G.X T) (i ≫ fst G.X T) :=
    ⟨𝟙 _, (Category.id_comp _).trans (lift_comp_fst_snd i).symm⟩
  have hQ : familyContainsSection Q (j ≫ snd G.X T) (j ≫ fst G.X T) :=
    ⟨𝟙 _, (Category.id_comp _).trans (lift_comp_fst_snd j).symm⟩
  obtain ⟨f, hf⟩ := (h _ _ _).mp hP
  obtain ⟨g, hg⟩ := (h _ _ _).mpr hQ
  change f ≫ j = lift (i ≫ fst G.X T) (i ≫ snd G.X T) at hf
  change g ≫ i = lift (j ≫ fst G.X T) (j ≫ snd G.X T) at hg
  rw [lift_comp_fst_snd] at hf hg
  let e : familyOverBase P ≅ familyOverBase Q :=
    ⟨f, g,
      (cancel_mono i).mp (by rw [Category.assoc, hg, hf, Category.id_comp]),
      (cancel_mono j).mp (by rw [Category.assoc, hf, hg, Category.id_comp])⟩
  exact sameFamily_of_iso_over_product e hf

theorem sameFamily_pullback {P Q : Family G T} (h : SameFamily P Q) (a : U ⟶ T) :
    SameFamily (P.pullback a) (Q.pullback a) := by
  apply sameFamily_iff_containsSection.mpr
  intro V b g
  rw [Family.containsSection_pullback_iff, Family.containsSection_pullback_iff]
  exact containsSection_congr_family h _ _

theorem conjugateSubgroupFamily_pullback (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left)
    (hs : Smooth B.X.hom) (g : T ⟶ G.X) (a : U ⟶ T) :
    SameFamily ((conjugateSubgroupFamily j hj hs g).pullback a)
      (conjugateSubgroupFamily j hj hs (a ≫ g)) := by
  apply sameFamily_iff_containsSection.mpr
  intro V b x
  rw [Family.containsSection_pullback_iff, containsSection_conjugate_iff,
    containsSection_conjugate_iff, Category.assoc]

private theorem sameFamily_pullback_id (P : Family G T) : SameFamily (P.pullback (𝟙 T)) P := by
  apply sameFamily_iff_containsSection.mpr
  intro V b g
  rw [Family.containsSection_pullback_iff, Category.comp_id]

private theorem isBorelFamily_of_sameFamily [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] {P Q : Family G T}
    (h : SameFamily P Q) (hP : IsBorelFamily P) : IsBorelFamily Q := by
  obtain ⟨e, he⟩ := h
  let F := changeBase T.hom
  have : IsAffineHom (F.obj G).X.hom :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.X.hom T.hom)
      ‹IsAffineHom G.X.hom›
  have : LocallyOfFinitePresentation (F.obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom T.hom))
  have : QuasiCompact (F.obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom T.hom))
  exact hasBorelFibres_of_sourceIso Q.closed e he hP

private theorem normalizesInFamily_iff_points (j : B ⟶ G) (x : T ⟶ G.X) :
    normalizesInFamily j x ↔ ∀ (V : Over S) (a : V ⟶ T) (b : V ⟶ B.X),
      (∃ c : V ⟶ B.X, c ≫ j.hom.hom = (a ≫ x) * (b ≫ j.hom.hom) * (a ≫ x)⁻¹) ∧
      (∃ c : V ⟶ B.X, c ≫ j.hom.hom = (a ≫ x)⁻¹ * (b ≫ j.hom.hom) * (a ≫ x)) := by
  have evaluation (V : Over S) (a : V ⟶ T) (b : V ⟶ B.X) (z : T ⟶ G.X) :
      lift b a ≫ conjugateMap j z = (a ≫ z) * (b ≫ j.hom.hom) * (a ≫ z)⁻¹ := by
    simp only [conjugateMap, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc]
  constructor
  · rintro ⟨⟨f, hf⟩, ⟨f', hf'⟩⟩ V a b
    refine ⟨⟨lift b a ≫ f, ?_⟩, ⟨lift b a ≫ f', ?_⟩⟩
    · rw [Category.assoc, hf, evaluation]
    · rw [Category.assoc, hf', evaluation, GrpObj.comp_inv, inv_inv]
  · intro h
    obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := h (B.X ⊗ T) (snd _ _) (fst _ _)
    refine ⟨⟨c, ?_⟩, ⟨c', ?_⟩⟩
    · exact hc
    · simpa only [conjugateMap, GrpObj.comp_inv, inv_inv] using hc'

set_option backward.isDefEq.respectTransparency false in
private theorem sameConjugates_iff_normalizes (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (g h : T ⟶ G.X) :
    SameFamily (conjugateSubgroupFamily j hj hs g) (conjugateSubgroupFamily j hj hs h) ↔
      normalizesInFamily j (g⁻¹ * h) := by
  rw [sameFamily_iff_containsSection, normalizesInFamily_iff_points]
  constructor
  · intro e V a b
    let G₁ := a ≫ g
    let G₂ := a ≫ h
    let z := b ≫ j.hom.hom
    have eq (x : V ⟶ G.X) := (containsSection_conjugate_iff j hj hs g a x).symm.trans
      ((e V a x).trans (containsSection_conjugate_iff j hj hs h a x))
    obtain ⟨c, hc⟩ := (eq (G₂ * z * G₂⁻¹)).mpr ⟨b, rfl⟩
    obtain ⟨d, hd⟩ := (eq (G₁ * z * G₁⁻¹)).mp ⟨b, rfl⟩
    have hh : a ≫ (g⁻¹ * h) = G₁⁻¹ * G₂ := by rw [MonObj.comp_mul, GrpObj.comp_inv]
    rw [hh]
    refine ⟨⟨c, ?_⟩, ⟨d, ?_⟩⟩
    · calc
        _ = G₁⁻¹ * (G₁ * (c ≫ j.hom.hom) * G₁⁻¹) * G₁ := by group
        _ = _ := by rw [show G₁ * (c ≫ j.hom.hom) * G₁⁻¹ = G₂ * z * G₂⁻¹ from hc]; dsimp only [z]; group
    · calc
        _ = G₂⁻¹ * (G₂ * (d ≫ j.hom.hom) * G₂⁻¹) * G₂ := by group
        _ = _ := by rw [show G₂ * (d ≫ j.hom.hom) * G₂⁻¹ = G₁ * z * G₁⁻¹ from hd]; dsimp only [z]; group
  · intro e V a x
    rw [containsSection_conjugate_iff, containsSection_conjugate_iff]
    let G₁ := a ≫ g
    let G₂ := a ≫ h
    have hh : a ≫ (g⁻¹ * h) = G₁⁻¹ * G₂ := by rw [MonObj.comp_mul, GrpObj.comp_inv]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨d, hd⟩ := (e V a b).2
      rw [hh] at hd
      refine ⟨d, ?_⟩
      change G₂ * (d ≫ j.hom.hom) * G₂⁻¹ = x
      rw [hd, ← hb]
      change G₂ * ((G₁⁻¹ * G₂)⁻¹ * (b ≫ j.hom.hom) * (G₁⁻¹ * G₂)) * G₂⁻¹ =
        G₁ * (b ≫ j.hom.hom) * G₁⁻¹
      group
    · rintro ⟨b, hb⟩
      obtain ⟨c, hc⟩ := (e V a b).1
      rw [hh] at hc
      refine ⟨c, ?_⟩
      change G₁ * (c ≫ j.hom.hom) * G₁⁻¹ = x
      rw [hc, ← hb]
      change G₁ * ((G₁⁻¹ * G₂) * (b ≫ j.hom.hom) * (G₁⁻¹ * G₂)⁻¹) * G₁⁻¹ =
        G₂ * (b ≫ j.hom.hom) * G₂⁻¹
      group

end FamilyCalculus

section QuotientClassification

variable {S : Scheme.{u}} {G B : Grp (Over S)} {P : Over S}

private theorem existsOverDesc {W X Y : Over S}
    (f : W ⟶ X) [EffectiveEpi f.left] (q : W ⟶ Y)
    (hq : ∀ (V : Over S) (a b : V ⟶ W), a ≫ f = b ≫ f → a ≫ q = b ≫ q) :
    ∃ x : X ⟶ Y, f ≫ x = q := by
  have heq {V : Scheme} (a b : V ⟶ W.left) (he : a ≫ f.left = b ≫ f.left) :
      a ≫ q.left = b ≫ q.left := by
    let V' : Over S := Over.mk (a ≫ W.hom)
    let a' : V' ⟶ W := Over.homMk a
    let b' : V' ⟶ W := Over.homMk b (by
      rw [← Over.w f, ← Category.assoc, ← he, Category.assoc, Over.w f]; rfl)
    exact congrArg (fun h ↦ h.left) (hq V' a' b' (Over.OverMorphism.ext he))
  let x := EffectiveEpi.desc f.left q.left heq
  have hx : f.left ≫ x = q.left := EffectiveEpi.fac f.left q.left heq
  let x' : X ⟶ Y := Over.homMk x ((cancel_epi f.left).mp (by
    rw [← Category.assoc, hx, Over.w q, Over.w f]))
  exact ⟨x', Over.OverMorphism.ext hx⟩

private theorem pullbackOfUniversalAlongGroup (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    {p : G.X ⟶ P} (C : Family G P)
    (hC : SameFamily (C.pullback p) (conjugateSubgroupFamily j hj hs (𝟙 G.X)))
    {T : Over S} (g : T ⟶ G.X) :
    SameFamily (C.pullback (g ≫ p)) (conjugateSubgroupFamily j hj hs g) := by
  refine sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp C p g))
    (sameFamily_trans (sameFamily_pullback hC g) ?_)
  simpa only [Category.comp_id] using conjugateSubgroupFamily_pullback j hj hs (𝟙 G.X) g

set_option backward.isDefEq.respectTransparency false in
private theorem quotientParameter_injective (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (p : G.X ⟶ P)
    [Smooth p.left] [Surjective p.left] [QuasiCompact p.left] (C : Family G P)
    (hC : SameFamily (C.pullback p) (conjugateSubgroupFamily j hj hs (𝟙 G.X)))
    (hq : ∀ (V : Over S) (g h : V ⟶ G.X),
      g ≫ p = h ≫ p ↔
        SameFamily (conjugateSubgroupFamily j hj hs g) (conjugateSubgroupFamily j hj hs h))
    {T : Over S} (x y : T ⟶ P) (he : SameFamily (C.pullback x) (C.pullback y)) :
    x = y := by
  let a := pullback.fst x p
  let g := pullback.snd x p
  let b := pullback.fst (a ≫ y) p
  let h := pullback.snd (a ≫ y) p
  have ha := (IsPullback.of_hasPullback x p).map (Over.forget S)
  have hb := (IsPullback.of_hasPullback (a ≫ y) p).map (Over.forget S)
  have smA : Smooth a.left := MorphismProperty.of_isPullback ha.flip ‹Smooth p.left›
  have suA : Surjective a.left := MorphismProperty.of_isPullback ha.flip ‹Surjective p.left›
  have qcA : QuasiCompact a.left := MorphismProperty.of_isPullback ha.flip ‹QuasiCompact p.left›
  have smB : Smooth b.left := MorphismProperty.of_isPullback hb.flip ‹Smooth p.left›
  have suB : Surjective b.left := MorphismProperty.of_isPullback hb.flip ‹Surjective p.left›
  have qcB : QuasiCompact b.left := MorphismProperty.of_isPullback hb.flip ‹QuasiCompact p.left›
  have ea : Epi a := Over.epi_of_epi_left a
  have eb : Epi b := Over.epi_of_epi_left b
  have hax : (b ≫ a) ≫ x = (b ≫ g) ≫ p := by
    simp only [Category.assoc, show a ≫ x = g ≫ p from pullback.condition]
  have hby : (b ≫ a) ≫ y = h ≫ p :=
    (Category.assoc b a y).trans pullback.condition
  have hxy : SameFamily (C.pullback ((b ≫ a) ≫ x)) (C.pullback ((b ≫ a) ≫ y)) :=
    sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp C x (b ≫ a)))
      (sameFamily_trans (sameFamily_pullback he (b ≫ a)) (sameFamily_pullback_comp C y (b ≫ a)))
  rw [hax, hby] at hxy
  have hh := (hq _ (b ≫ g) h).mpr
    (sameFamily_trans (sameFamily_symm (pullbackOfUniversalAlongGroup j hj hs C hC (b ≫ g)))
      (sameFamily_trans hxy (pullbackOfUniversalAlongGroup j hj hs C hC h)))
  exact (cancel_epi (b ≫ a)).mp (hax.trans (hh.trans hby.symm))

set_option backward.isDefEq.respectTransparency false in
/-- The coset of a local conjugating section descends to the unique parameter. -/
theorem uniqueParameterOfLocalConjugacy (j : B ⟶ G)
    (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom) (p : G.X ⟶ P)
    [Smooth p.left] [Surjective p.left] [QuasiCompact p.left] (C : Family G P)
    (hC : SameFamily (C.pullback p) (conjugateSubgroupFamily j hj hs (𝟙 G.X)))
    (hq : ∀ (V : Over S) (g h : V ⟶ G.X),
      g ≫ p = h ≫ p ↔
        SameFamily (conjugateSubgroupFamily j hj hs g) (conjugateSubgroupFamily j hj hs h))
    {T Z : Over S} (Q : Family G T) (a : Z ⟶ T)
    [Flat a.left] [Surjective a.left] [QuasiCompact a.left] (s : Z ⟶ G.X)
    (he : SameFamily (conjugateSubgroupFamily j hj hs s) (Q.pullback a)) :
    ∃! x : T ⟶ P, SameFamily (C.pullback x) Q := by
  have hdesc (V : Over S) (f g : V ⟶ Z) (hfg : f ≫ a = g ≫ a) :
      f ≫ (s ≫ p) = g ≫ (s ≫ p) := by
    have h (f : V ⟶ Z) :
        SameFamily (conjugateSubgroupFamily j hj hs (f ≫ s)) (Q.pullback (f ≫ a)) :=
      sameFamily_trans (sameFamily_symm (conjugateSubgroupFamily_pullback j hj hs s f))
        (sameFamily_trans (sameFamily_pullback he f) (sameFamily_pullback_comp Q a f))
    have hf := h f
    rw [hfg] at hf
    have hfg' := (hq V (f ≫ s) (g ≫ s)).mpr (sameFamily_trans hf (sameFamily_symm (h g)))
    simpa only [Category.assoc] using hfg'
  obtain ⟨x, hx⟩ := existsOverDesc a (s ≫ p) hdesc
  have eq : SameFamily (C.pullback x) Q := by
    apply sameFamily_of_same_pullback a
    refine sameFamily_trans (sameFamily_pullback_comp C x a) ?_
    rw [hx]
    exact sameFamily_trans (pullbackOfUniversalAlongGroup j hj hs C hC s) he
  exact ⟨x, eq, fun y hy ↦ quotientParameter_injective j hj hs p C hC hq y x
    (sameFamily_trans hy (sameFamily_symm eq))⟩

end QuotientClassification

section LocalClassification

variable {S : Scheme.{u}} {G : Grp (Over S)} {T U P : Over S}

private abbrev coverObj (c : T.left.OpenCover.{v}) (i : c.I₀) : Over S :=
  Over.mk (c.f i ≫ T.hom)

private def coverHom (c : T.left.OpenCover.{v}) (i : c.I₀) : coverObj c i ⟶ T :=
  Over.homMk (c.f i)

private theorem overHom_ext_of_openCover (c : T.left.OpenCover.{v}) {f g : T ⟶ U}
    (h : ∀ i, coverHom c i ≫ f = coverHom c i ≫ g) : f = g :=
  Over.OverMorphism.ext (c.hom_ext _ _ (fun i ↦ congrArg Over.Hom.left (h i)))

private theorem existsOverGlue (c : T.left.OpenCover.{v}) (f : ∀ i, coverObj c i ⟶ P)
    (h : ∀ i j, pullback.fst (c.f i) (c.f j) ≫ (f i).left =
      pullback.snd (c.f i) (c.f j) ≫ (f j).left) :
    ∃ x : T ⟶ P, ∀ i, coverHom c i ≫ x = f i := by
  let x := c.glueMorphisms (fun i ↦ (f i).left) h
  have hx : ∀ i, c.f i ≫ x = (f i).left := c.ι_glueMorphisms _ _
  have hx' : x ≫ P.hom = T.hom := c.hom_ext _ _ fun i ↦ by
    rw [← Category.assoc, hx, Over.w (f i)]
    rfl
  exact ⟨Over.homMk x hx', fun i ↦ Over.OverMorphism.ext (hx i)⟩

private theorem factorsOfOpenCover {A B : Over S} (c : T.left.OpenCover.{v})
    (i : A ⟶ B) [Mono i.left] (f : T ⟶ B)
    (h : ∀ j, ∃ g : coverObj c j ⟶ A, g ≫ i = coverHom c j ≫ f) :
    ∃ g : T ⟶ A, g ≫ i = f := by
  choose g hg using h
  have he : ∀ j k, pullback.fst (c.f j) (c.f k) ≫ (g j).left =
      pullback.snd (c.f j) (c.f k) ≫ (g k).left := by
    intro j k
    apply (cancel_mono i.left).mp
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hg, hg,
      Over.comp_left, Over.comp_left, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ f.left) pullback.condition
  obtain ⟨a, ha⟩ := existsOverGlue c g he
  exact ⟨a, overHom_ext_of_openCover c fun j ↦ by rw [← Category.assoc, ha, hg]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem containsSection_of_openCover (Q : Family G T) (a : U ⟶ T) (x : U ⟶ G.X)
    (c : U.left.OpenCover.{v})
    (h : ∀ i, familyContainsSection Q (coverHom c i ≫ a) (coverHom c i ≫ x)) :
    familyContainsSection Q a x := by
  have hc : IsClosedImmersion (familyProductInclusion Q).left := by
    rw [familyProductInclusion_left]
    exact Q.closed
  apply factorsOfOpenCover c (familyProductInclusion Q) (lift x a)
  intro i
  obtain ⟨y, hy⟩ := h i
  refine ⟨y, hy.trans ?_⟩
  apply CartesianMonoidalCategory.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Equality of closed subgroup families is Zariski-local on the test scheme. -/
theorem sameFamily_of_openCover (c : T.left.OpenCover.{v}) {B C : Family G T}
    (h : ∀ i, SameFamily (B.pullback (coverHom c i)) (C.pullback (coverHom c i))) :
    SameFamily B C := by
  apply sameFamily_iff_containsSection.mpr
  intro V a x
  let d := c.pullback₁ a.left
  have localEq (i : d.I₀) :
      familyContainsSection B (coverHom d i ≫ a) (coverHom d i ≫ x) ↔
        familyContainsSection C (coverHom d i ≫ a) (coverHom d i ≫ x) := by
    let b : coverObj d i ⟶ coverObj c i := Over.homMk (c.pullbackHom a.left i) (by
      have hh := c.pullbackHom_map a.left i
      change c.pullbackHom a.left i ≫ (c.f i ≫ T.hom) = d.f i ≫ V.hom
      rw [← Category.assoc, hh, Category.assoc, Over.w a])
    have hb : b ≫ coverHom c i = coverHom d i ≫ a :=
      Over.OverMorphism.ext (c.pullbackHom_map a.left i)
    rw [← hb, ← Family.containsSection_pullback_iff, ← Family.containsSection_pullback_iff]
    exact containsSection_congr_family (h i) b _
  constructor
  · intro H
    refine containsSection_of_openCover C a x d fun i ↦ (localEq i).mp ?_
    obtain ⟨y, hy⟩ := H
    refine ⟨coverHom d i ≫ y, ?_⟩
    rw [Category.assoc, hy]
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · intro H
    refine containsSection_of_openCover B a x d fun i ↦ (localEq i).mpr ?_
    obtain ⟨y, hy⟩ := H
    refine ⟨coverHom d i ≫ y, ?_⟩
    rw [Category.assoc, hy]
    apply CartesianMonoidalCategory.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Affine representability, together with uniqueness on test schemes, gives
the parameter for an arbitrary test scheme by gluing. -/
theorem representsBorelFamilies_of_affines [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (C : Family G P)
    (hinj : ∀ {V : Over S} (x y : V ⟶ P), SameFamily (C.pullback x) (C.pullback y) → x = y)
    (hlocal : ∀ (V : Over S) [IsAffine V.left] (B : Family G V), IsBorelFamily B →
      ∃ x : V ⟶ P, SameFamily (C.pullback x) B)
    (B : Family G T) (hB : IsBorelFamily B) :
    ∃! x : T ⟶ P, SameFamily (C.pullback x) B := by
  let c := T.left.affineCover
  let a (i : c.I₀) := coverHom c i
  have hl (i : c.I₀) : ∃ x : coverObj c i ⟶ P, SameFamily (C.pullback x) (B.pullback (a i)) := by
    have : IsAffine (coverObj c i).left := inferInstanceAs (IsAffine (c.X i))
    exact hlocal _ _ (isBorelFamily_pullback B hB (a i))
  choose x hx using hl
  have hg (i j : c.I₀) :
      pullback.fst (c.f i) (c.f j) ≫ (x i).left =
        pullback.snd (c.f i) (c.f j) ≫ (x j).left := by
    let W : Over S := Over.mk (pullback.fst (c.f i) (c.f j) ≫ (coverObj c i).hom)
    let u : W ⟶ coverObj c i := Over.homMk (pullback.fst (c.f i) (c.f j))
    let v : W ⟶ coverObj c j := Over.homMk (pullback.snd (c.f i) (c.f j)) (by
      change pullback.snd (c.f i) (c.f j) ≫ (c.f j ≫ T.hom) =
        pullback.fst (c.f i) (c.f j) ≫ (c.f i ≫ T.hom)
      rw [← Category.assoc, ← Category.assoc, pullback.condition])
    have huv : u ≫ a i = v ≫ a j := Over.OverMorphism.ext pullback.condition
    have hc (l : c.I₀) (f : W ⟶ coverObj c l) :
        SameFamily (C.pullback (f ≫ x l)) (B.pullback (f ≫ a l)) :=
      sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp C (x l) f))
        (sameFamily_trans (sameFamily_pullback (hx l) f) (sameFamily_pullback_comp B (a l) f))
    have hi := hc i u
    rw [huv] at hi
    exact congrArg Over.Hom.left (hinj _ _ (sameFamily_trans hi (sameFamily_symm (hc j v))))
  obtain ⟨p, hp⟩ := existsOverGlue c x hg
  have he : SameFamily (C.pullback p) B := by
    apply sameFamily_of_openCover c
    intro i
    refine sameFamily_trans (sameFamily_pullback_comp C p (a i)) ?_
    rw [show a i ≫ p = x i from hp i]
    exact hx i
  exact ⟨p, he, fun y hy ↦ hinj y p (sameFamily_trans hy (sameFamily_symm he))⟩

end LocalClassification

section ClosedImmersionDescent

variable {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (f : X ⟶ Y)

private theorem quasiCompact_of_flatCover [Surjective a] [QuasiCompact a]
    [QuasiCompact (pullback.snd f a)] : QuasiCompact f := by
  constructor
  intro U hU hc
  have h₁ := QuasiCompact.isCompact_preimage (f := a) U hU hc
  have h₂ := QuasiCompact.isCompact_preimage (f := pullback.snd f a) (a ⁻¹' U)
    (hU.preimage a.continuous) h₁
  have hi := Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback f a).flip (a ⁻¹' U)
  rw [Set.image_preimage_eq _ a.surjective] at hi
  have hk := h₂.image (pullback.fst f a).continuous
  exact hi ▸ hk

set_option backward.isDefEq.respectTransparency false in
/-- A closed immersion is recognized on a faithfully flat quasi-compact cover. -/
theorem isClosedImmersion_of_flatCover [Surjective a] [Flat a] [QuasiCompact a]
    [IsClosedImmersion (pullback.snd f a)] : IsClosedImmersion f := by
  have : QuasiCompact f := quasiCompact_of_flatCover a f
  let j := f.imageι
  let t := f.toImage
  let q := pullback.snd j a
  let m : pullback f a ⟶ pullback j a := pullback.lift (pullback.fst f a ≫ t)
    (pullback.snd f a) (by rw [Category.assoc, Scheme.Hom.toImage_imageι, pullback.condition])
  have hmq : m ≫ q = pullback.snd f a := pullback.lift_snd _ _ _
  have hk : (pullback.snd f a).ker = q.ker := by
    rw [kernelOfFlatPullback f a, show q = pullback.snd j a from rfl,
      kernelOfFlatPullback j a, Scheme.IdealSheafData.ker_subschemeι]
  have hm : IsIso m := IsClosedImmersion.isIso_of_ker_eq _ _ _ hmq hk
  have hp : IsPullback m (pullback.fst f a) (pullback.fst j a) t := by
    have hmf : m ≫ pullback.fst j a = pullback.fst f a ≫ t := pullback.lift_fst _ _ _
    have h := IsPullback.of_hasPullback f a
    have h' : IsPullback (m ≫ q) (pullback.fst f a) a (t ≫ j) := by
      rw [hmq, Scheme.Hom.toImage_imageι]
      exact h.flip
    exact h'.of_right hmf (IsPullback.of_hasPullback j a).flip
  have hf : Flat (pullback.fst j a) := inferInstance
  have hs : Surjective (pullback.fst j a) := inferInstance
  have hq : QuasiCompact (pullback.fst j a) := inferInstance
  have ht : IsIso t := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp ⟨⟨hs, hf⟩, hq⟩ hm
  have hci : IsClosedImmersion (t ≫ j) := inferInstance
  exact f.toImage_imageι ▸ hci

end ClosedImmersionDescent

section SeparatedQuotient

variable {S : Scheme.{u}} {G B : Grp (Over S)} {P : Over S} (p : G.X ⟶ P)
  (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left)

private def quotientDiagonal : P ⟶ P ⊗ P := lift (𝟙 P) (𝟙 P)

private def productProjection : G.X ⊗ G.X ⟶ P ⊗ P :=
  lift (fst G.X G.X ≫ p) (snd G.X G.X ≫ p)

private def quotientRelationInclusion : G.X ⊗ B.X ⟶ G.X ⊗ G.X :=
  lift (fst G.X B.X) (fst G.X B.X * (snd G.X B.X ≫ j.hom.hom))

include hj in
set_option backward.isDefEq.respectTransparency false in
private theorem quotientRelationInclusion_closed : IsClosedImmersion (quotientRelationInclusion j).left := by
  let i := lift (fst G.X B.X) (snd G.X B.X ≫ j.hom.hom)
  let ex : G.X ⊗ G.X ⟶ G.X ⊗ G.X := lift (fst G.X G.X) (fst G.X G.X * snd G.X G.X)
  let invEx : G.X ⊗ G.X ⟶ G.X ⊗ G.X := lift (fst G.X G.X) ((fst G.X G.X)⁻¹ * snd G.X G.X)
  have e : IsIso ex := by
    refine ⟨⟨invEx, ?_, ?_⟩⟩ <;> apply CartesianMonoidalCategory.hom_ext
    · simp only [ex, invEx, Category.assoc, lift_fst, Category.id_comp]
    · simp only [ex, invEx, Category.assoc, lift_snd, MonObj.comp_mul, GrpObj.comp_inv,
        lift_fst, Category.id_comp, inv_mul_cancel_left]
    · simp only [ex, invEx, Category.assoc, lift_fst, Category.id_comp]
    · simp only [ex, invEx, Category.assoc, lift_snd, MonObj.comp_mul,
        lift_fst, Category.id_comp, mul_inv_cancel_left]
  have ec : IsIso ex.left := (Over.forget S).map_isIso ex
  have hc : IsClosedImmersion i.left :=
    MorphismProperty.of_isPullback ((productPullback G.X j.hom.hom).map (Over.forget S)).flip hj
  have eq : i ≫ ex = quotientRelationInclusion j := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [i, ex, quotientRelationInclusion, Category.assoc, lift_fst]
    · simp only [i, ex, quotientRelationInclusion, Category.assoc, lift_snd, MonObj.comp_mul, lift_fst]
  exact congrArg Over.Hom.left eq ▸
    inferInstanceAs (IsClosedImmersion (i.left ≫ ex.left))

include hj in
set_option backward.isDefEq.respectTransparency false in
private theorem quotientRelation_cartesian
    (h : ∀ (T : Over S) (x y : T ⟶ G.X),
      x ≫ p = y ≫ p ↔ ∃ b : T ⟶ B.X, x * (b ≫ j.hom.hom) = y) :
    IsPullback (fst G.X B.X ≫ p) (quotientRelationInclusion j)
      (quotientDiagonal (P := P)) (productProjection p) := by
  let q := quotientRelationInclusion j
  have hq : IsClosedImmersion q.left := quotientRelationInclusion_closed j hj
  have hm : Mono q := Over.mono_of_mono_left _
  refine IsPullback.mk' ?_ (fun T l r _ h₀ ↦ (cancel_mono q).mp h₀) ?_
  · have e := (h (G.X ⊗ B.X) (fst G.X B.X) (fst G.X B.X * (snd _ _ ≫ j.hom.hom))).mpr
      ⟨snd _ _, rfl⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp only [quotientDiagonal, productProjection, quotientRelationInclusion,
        Category.assoc, lift_fst, lift_fst_assoc, Category.comp_id]
    · simp only [quotientDiagonal, productProjection, quotientRelationInclusion,
        Category.assoc, lift_snd, lift_snd_assoc, Category.comp_id]
      exact e
  · intro T q₀ r h₀
    let x := r ≫ fst G.X G.X
    let y := r ≫ snd G.X G.X
    have hx : q₀ = x ≫ p := by
      simpa only [x, quotientDiagonal, productProjection, Category.assoc, lift_fst, lift_fst_assoc,
        Category.comp_id] using congrArg (· ≫ fst P P) h₀
    have hy : q₀ = y ≫ p := by
      simpa only [y, quotientDiagonal, productProjection, Category.assoc, lift_snd, lift_snd_assoc,
        Category.comp_id] using congrArg (· ≫ snd P P) h₀
    obtain ⟨b, hb⟩ := (h T x y).mp (hx.symm.trans hy)
    refine ⟨lift x b, ?_, ?_⟩
    · rw [lift_fst_assoc, ← hx]
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [quotientRelationInclusion, Category.assoc, lift_fst, x]
      · simp only [quotientRelationInclusion, Category.assoc, lift_snd, MonObj.comp_mul, lift_fst, lift_snd_assoc]
        rw [hb]

private theorem tensor_projection_property (F : MorphismProperty Scheme.{u})
    [F.IsStableUnderBaseChange] [F.IsMultiplicative]
    (hp : F p.left) : F (productProjection p).left := by
  let L := G.X ◁ p
  let R := p ▷ P
  have e : L ≫ R = productProjection p := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [L, R, productProjection, Category.assoc, whiskerRight_fst,
        whiskerLeft_fst_assoc, lift_fst]
    · simp only [L, R, productProjection, Category.assoc, whiskerRight_snd, whiskerLeft_snd,
        lift_snd]
  have p₁ : F L.left := MorphismProperty.of_isPullback
    ((productPullback G.X p).map (Over.forget S)).flip hp
  have p₂ : F R.left := by
    let s := productPullback P p
    let r₁ := β_ G.X P
    let r₂ := β_ P P
    have e : r₁.hom ≫ (P ◁ p) = R ≫ r₂.hom := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [r₁, r₂, R]
    have h : IsPullback R (fst G.X P) (fst P P) p :=
      s.of_iso' r₁ r₂ (Iso.refl _) (Iso.refl _) e (by simp [r₁]) (by simp [r₂]) (by simp)
    exact MorphismProperty.of_isPullback (h.map (Over.forget S)).flip hp
  exact congrArg Over.Hom.left e ▸ F.comp_mem L.left R.left p₁ p₂

include hj in
set_option backward.isDefEq.respectTransparency false in
/-- The diagonal of the right quotient is closed because its pullback to
pairs of ambient group points is the right coset relation. -/
theorem separatedRightQuotient [Flat p.left] [Surjective p.left] [QuasiCompact p.left]
    (h : ∀ (T : Over S) (x y : T ⟶ G.X),
      x ≫ p = y ≫ p ↔ ∃ b : T ⟶ B.X, x * (b ≫ j.hom.hom) = y) : IsSeparated P.hom := by
  have hdiag : (quotientDiagonal (P := P)).left = pullback.diagonal P.hom := by
    apply pullback.hom_ext <;> simp [quotientDiagonal]
  let f := (quotientDiagonal (P := P)).left
  let a := (productProjection p).left
  have : Flat a := tensor_projection_property p @Flat inferInstance
  have : Surjective a := tensor_projection_property p @Surjective inferInstance
  have : QuasiCompact a := tensor_projection_property p @QuasiCompact inferInstance
  have hp := (quotientRelation_cartesian p j hj h).map (Over.forget S)
  have hci := quotientRelationInclusion_closed j hj
  have : IsClosedImmersion (pullback.snd f a) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hp.isoPullback.hom _).1
      (hp.isoPullback_hom_snd.symm ▸ hci)
  exact ⟨hdiag ▸ isClosedImmersion_of_flatCover a f⟩

end SeparatedQuotient

section SplitClassification

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.GeometricRadicals (IsReductive)
open private reductive_of_groupIso from LinearAlgebraicGroups.RootData.RankOneFlag

set_option backward.isDefEq.respectTransparency false in
private theorem integralFibre_isReductive {D : BasedRootDatum.{u}} (M : Model D)
    [IsAffineHom M.group.X.hom] [LocallyOfFinitePresentation M.group.X.hom]
    [QuasiCompact M.group.X.hom] (k : Type u) [Field k] (a : ringSpec k ⟶ Base.{u}) :
    IsReductive (affineFibre (G := M.group) a) := by
  rw [integralBaseMap_eq a]
  obtain ⟨L, F, e, _⟩ := M.fieldFibre k
  exact reductive_of_groupIso e.symm F.pinned.pair.reductive

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_eq_iff_sameFamily {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Free R A] {G B : Grp (Over (ringSpec R))}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (eB : B.X ≅ coordSpec R A) (hB : HasBorelFibres j)
    (hG : ∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ ringSpec R),
      IsReductive (affineFibre (G := G) a))
    {P : Over (ringSpec R)} (p : G.X ⟶ P)
    (hq : ∀ (T : Over (ringSpec R)) (g h : T ⟶ G.X),
      g ≫ p = h ≫ p ↔ ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h)
    (T : Over (ringSpec R)) (g h : T ⟶ G.X) :
    g ≫ p = h ≫ p ↔
      SameFamily (conjugateSubgroupFamily j hj hs g) (conjugateSubgroupFamily j hj hs h) := by
  rw [sameConjugates_iff_normalizes, relativeBorelNormalizer j hj hs eB hB hG T, hq]
  exact exists_congr fun b ↦ ⟨fun hb ↦ by rw [← hb, inv_mul_cancel_left],
    fun hb ↦ by rw [hb, mul_inv_cancel_left]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem splitQuotient_represents {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Free R A] {G B : Grp (Over (ringSpec R))}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    (j : B ⟶ G) (hj : IsClosedImmersion j.hom.hom.left) (hs : Smooth B.X.hom)
    (eB : B.X ≅ coordSpec R A) (hB : HasBorelFibres j)
    (hG : ∀ (k : Type u) [Field k] [IsAlgClosed k] (a : ringSpec k ⟶ ringSpec R),
      IsReductive (affineFibre (G := G) a))
    (c : UnitCocharacter G)
    (hpoints : ∀ (E : Type u) [CommRing E] [Algebra R E] (x : coordSpec R E ⟶ G.X),
      HasPolynomialOrbit c x ↔ ∃ y : coordSpec R E ⟶ B.X, y ≫ j.hom.hom = x)
    {P : Over (ringSpec R)} (p : G.X ⟶ P)
    [Smooth p.left] [Surjective p.left] [QuasiCompact p.left] (U : Family G P)
    (hU : SameFamily (U.pullback p) (conjugateSubgroupFamily j hj hs (𝟙 G.X)))
    (hq : ∀ (T : Over (ringSpec R)) (g h : T ⟶ G.X),
      g ≫ p = h ≫ p ↔ ∃ b : T ⟶ B.X, g * (b ≫ j.hom.hom) = h) :
    ∀ (T : Over (ringSpec R)) (Q : Family G T), IsBorelFamily Q →
      ∃! x : T ⟶ P, SameFamily (U.pullback x) Q := by
  have hq' := quotient_eq_iff_sameFamily j hj hs eB hB hG p hq
  intro T Q hQ
  apply representsBorelFamilies_of_affines U (fun x y ↦ quotientParameter_injective j hj hs p U hU hq' x y)
  · intro V _ F hF
    obtain ⟨E, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr (inferInstance : IsAffine V.left)
    let W := coordSpec R E.unop
    let e' : W ≅ V := e
    let F' := F.pullback e'.hom
    have hF' : IsBorelFamily F' := isBorelFamily_pullback F hF e'.hom
    obtain ⟨Z, l, _, hsm, hsurj, hqc, hZ⟩ :=
      existsSmoothBorelTransporter j hj hs hB eB c hpoints F' hF'
    let f := l ≫ snd G.X W
    let g := l ≫ fst G.X W
    have hh : SameFamily (conjugateSubgroupFamily j hj hs g) (F'.pullback f) := by
      apply (hZ Z f g).mpr
      exact ⟨𝟙 Z, by rw [Category.id_comp, lift_comp_fst_snd]⟩
    obtain ⟨x, hx, _⟩ := uniqueParameterOfLocalConjugacy j hj hs p U hU hq' F' f g hh
    refine ⟨e'.inv ≫ x, sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp U x e'.inv))
      (sameFamily_trans (sameFamily_pullback hx e'.inv) ?_)⟩
    have h := sameFamily_pullback_comp F e'.hom e'.inv
    rw [Iso.inv_hom_id] at h
    exact sameFamily_trans h (sameFamily_pullback_id F)
  · exact hQ

set_option backward.isDefEq.respectTransparency false in
/-- The integral split flag and its actual universal Borel represent families
over every test scheme over the integers. -/
private theorem integralBorelRepresentsSeparated {D : BasedRootDatum.{u}} (M : Model D) :
    ∃ (P : IntegralScheme.{u}) (U : Family M.group P),
      Smooth P.hom ∧ IsSeparated P.hom ∧ IsBorelFamily U ∧
      ∀ (T : IntegralScheme.{u}) (Q : Family M.group T), IsBorelFamily Q →
        ∃! x : T ⟶ P, SameFamily (U.pullback x) Q := by
  have : IsAffine M.group.X.left := M.affine
  have : IsAffineHom M.group.X.hom := inferInstance
  have : LocallyOfFinitePresentation M.group.X.hom := M.locallyOfFinitePresentation
  have : QuasiCompact M.group.X.hom := M.quasiCompact
  have : Smooth M.group.X.hom := M.smooth
  have : GeometricallyConnected M.group.X.hom := M.connected
  obtain ⟨B, j, hj, hs, P, p, U, hB, hP, hp, hsP, hqcP, hfree, hU, hUp, hq, c, hc⟩ :=
    integralBorelQuotientWithCocharacter M
  obtain ⟨A, hA, ⟨e⟩⟩ := hfree
  refine ⟨P, U, hP, separatedRightQuotient p j hj hq, hU, ?_⟩
  exact splitQuotient_represents j hj hs e hB (fun k _ _ a ↦ integralFibre_isReductive M k a) c hc p U hUp hq

theorem integralBorelRepresents {D : BasedRootDatum.{u}} (M : Model D) :
    ∃ (P : IntegralScheme.{u}) (U : Family M.group P),
      Smooth P.hom ∧ IsBorelFamily U ∧
      ∀ (T : IntegralScheme.{u}) (Q : Family M.group T), IsBorelFamily Q →
        ∃! x : T ⟶ P, SameFamily (U.pullback x) Q := by
  obtain ⟨P, U, hP, _, hU, hrep⟩ := integralBorelRepresentsSeparated M
  exact ⟨P, U, hP, hU, hrep⟩

end SplitClassification

section FamilyBase

variable {S S' : Scheme.{u}} {G : Grp (Over S)} {T U : Over S}

set_option backward.isDefEq.respectTransparency false in
private theorem familyPullback_first (B : Family G T) (x : U ⟶ T) :
    (B.pullback x).inclusion.hom.hom.left ≫ pullback.fst G.X.hom U.hom =
      pullback.fst B.group.X.hom x.left ≫ B.inclusion.hom.hom.left ≫ pullback.fst G.X.hom T.hom := by
  have h := congrArg (fun f ↦ f ≫ fst G.X T) (familyProductPullback_over B x).w
  simp only [Category.assoc, whiskerLeft_fst] at h
  simp only [familyProductInclusion, lift_fst] at h
  exact congrArg Over.Hom.left h

private theorem closed_comp_groupIso {C : Scheme.{u}} {P Q W : Grp (Over C)}
    (f : P ⟶ Q) (e : Q ≅ W) (h : IsClosedImmersion f.hom.hom.left) :
    IsClosedImmersion (f ≫ e.hom).hom.hom.left := by
  have he : IsIso e.hom.hom.hom.left :=
    (Grp.forget (Over C) ⋙ Over.forget C).map_isIso e.hom
  exact IsClosedImmersion.comp f.hom.hom.left e.hom.hom.hom.left

variable (a : S' ⟶ S)

private def relativeFamily {X : Over S'} (B : Family G ((Over.map a).obj X)) :
    Family ((changeBase a).obj G) X where
  group := B.group
  inclusion := B.inclusion ≫ (changeBaseComp X.hom a).hom.app G
  closed := closed_comp_groupIso B.inclusion ((changeBaseComp X.hom a).app G) B.closed
  smooth := B.smooth

private def absoluteFamily {X : Over S'} (B : Family ((changeBase a).obj G) X) :
    Family G ((Over.map a).obj X) where
  group := B.group
  inclusion := B.inclusion ≫ (changeBaseComp X.hom a).inv.app G
  closed := closed_comp_groupIso B.inclusion ((changeBaseComp X.hom a).symm.app G) B.closed
  smooth := B.smooth

set_option backward.isDefEq.respectTransparency false in
private theorem relativeFamily_isBorel {X : Over S'} (B : Family G ((Over.map a).obj X)) :
    IsBorelFamily (relativeFamily a B) ↔ IsBorelFamily B := by
  let e := (changeBaseComp X.hom a).app G
  change HasBorelFibres (B.inclusion ≫ e.hom) ↔ HasBorelFibres B.inclusion
  constructor
  · intro h
    have h' := hasBorelFibres_comp_iso e.symm h
    change HasBorelFibres ((B.inclusion ≫ e.hom) ≫ e.inv) at h'
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'
  · exact hasBorelFibres_comp_iso e

set_option backward.isDefEq.respectTransparency false in
private theorem absoluteFamily_isBorel {X : Over S'} (B : Family ((changeBase a).obj G) X) :
    IsBorelFamily (absoluteFamily a B) ↔ IsBorelFamily B := by
  let e := (changeBaseComp X.hom a).app G
  change HasBorelFibres (B.inclusion ≫ e.inv) ↔ HasBorelFibres B.inclusion
  constructor
  · intro h
    have h' := hasBorelFibres_comp_iso e h
    change HasBorelFibres ((B.inclusion ≫ e.inv) ≫ e.hom) at h'
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h'
  · exact hasBorelFibres_comp_iso e.symm

private theorem relativeFamily_sameFamily {X : Over S'} {B C : Family G ((Over.map a).obj X)} :
    SameFamily (relativeFamily a B) (relativeFamily a C) ↔ SameFamily B C := by
  let e := (changeBaseComp X.hom a).app G
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, (cancel_mono e.hom).mp ?_⟩
    change f.hom ≫ (C.inclusion ≫ e.hom) = B.inclusion ≫ e.hom at hf
    exact (Category.assoc _ _ _).trans hf
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    change f.hom ≫ (C.inclusion ≫ e.hom) = B.inclusion ≫ e.hom
    rw [← Category.assoc, hf]

private theorem relativeAbsoluteFamily {X : Over S'} (B : Family ((changeBase a).obj G) X) :
    SameFamily (relativeFamily a (absoluteFamily a B)) B := by
  let e := (changeBaseComp X.hom a).app G
  refine ⟨Iso.refl _, ?_⟩
  change 𝟙 _ ≫ B.inclusion = (B.inclusion ≫ e.inv) ≫ e.hom
  rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem relativeFamily_first {X : Over S'} (B : Family G ((Over.map a).obj X)) :
    (relativeFamily a B).inclusion.hom.hom.left ≫
      pullback.fst ((changeBase a).obj G).X.hom X.hom ≫ pullback.fst G.X.hom a =
      B.inclusion.hom.hom.left ≫ pullback.fst G.X.hom (X.hom ≫ a) := by
  change (B.inclusion.hom.hom.left ≫
    ((Over.pullbackComp X.hom a).hom.app G.X).left ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id, Category.assoc]
  exact congrArg (B.inclusion.hom.hom.left ≫ ·) (pullbackComp_first X.hom a G.X)

set_option backward.isDefEq.respectTransparency false in
private theorem relativeFamily_pullback {X Y : Over S'} (B : Family G ((Over.map a).obj X))
    (x : Y ⟶ X) :
    SameFamily ((relativeFamily a B).pullback x)
      (relativeFamily a (B.pullback ((Over.map a).map x))) := by
  let L := (relativeFamily a B).pullback x
  let R := relativeFamily a (B.pullback ((Over.map a).map x))
  have h : L.inclusion = R.inclusion := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · let p := pullback.fst ((changeBase a).obj G).X.hom Y.hom
        let q := pullback.fst G.X.hom a
        change (L.inclusion.hom.hom.left ≫ p) ≫ q = (R.inclusion.hom.hom.left ≫ p) ≫ q
        calc
          _ = (pullback.fst (relativeFamily a B).group.X.hom x.left ≫
              (relativeFamily a B).inclusion.hom.hom.left ≫
              pullback.fst ((changeBase a).obj G).X.hom X.hom) ≫ q :=
            congrArg (· ≫ q) (familyPullback_first (relativeFamily a B) x)
          _ = pullback.fst B.group.X.hom x.left ≫
              ((relativeFamily a B).inclusion.hom.hom.left ≫
                pullback.fst ((changeBase a).obj G).X.hom X.hom ≫ q) := by
            simp only [Category.assoc]
            rfl
          _ = pullback.fst B.group.X.hom x.left ≫
              (B.inclusion.hom.hom.left ≫ pullback.fst G.X.hom (X.hom ≫ a)) :=
            congrArg (pullback.fst B.group.X.hom x.left ≫ ·) (relativeFamily_first a B)
          _ = (B.pullback ((Over.map a).map x)).inclusion.hom.hom.left ≫
              pullback.fst G.X.hom (Y.hom ≫ a) :=
            (familyPullback_first B ((Over.map a).map x)).symm
          _ = _ := (relativeFamily_first a (B.pullback ((Over.map a).map x))).symm.trans
            (Category.assoc _ _ _).symm
      · have hp : pullback.fst ((changeBase a).obj G).X.hom Y.hom ≫ pullback.snd G.X.hom a =
            pullback.snd ((changeBase a).obj G).X.hom Y.hom ≫ Y.hom := pullback.condition
        simp only [Category.assoc, hp]
        have hL := Over.w L.inclusion.hom.hom
        have hR := Over.w R.inclusion.hom.hom
        change L.inclusion.hom.hom.left ≫ pullback.snd ((changeBase a).obj G).X.hom Y.hom =
            L.group.X.hom at hL
        change R.inclusion.hom.hom.left ≫ pullback.snd ((changeBase a).obj G).X.hom Y.hom =
            R.group.X.hom at hR
        rw [← Category.assoc, ← Category.assoc, hL, hR]
        rfl
    · exact (Over.w L.inclusion.hom.hom).trans (Over.w R.inclusion.hom.hom).symm
  exact ⟨Iso.refl _, by rw [Iso.refl_hom, Category.id_comp, h]⟩



/-- The classification map for Borel families is preserved under base change. -/
theorem representsBorelFamilies_pullback [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    {P : Over S} (B : Family G P)
    (h : ∀ (T : Over S) (Q : Family G T), IsBorelFamily Q →
      ∃! x : T ⟶ P, SameFamily (B.pullback x) Q)
    (X : Over S') (Q : Family ((changeBase a).obj G) X) (hQ : IsBorelFamily Q) :
    let c := (Over.mapPullbackAdj a).counit.app P
    ∃! x : X ⟶ (Over.pullback a).obj P, SameFamily ((relativeFamily a (B.pullback c)).pullback x) Q := by
  intro c
  let adj := Over.mapPullbackAdj a
  let E := adj.homEquiv X P
  let Q' := absoluteFamily a Q
  have hQ' : IsBorelFamily Q' := (absoluteFamily_isBorel a Q).mpr hQ
  obtain ⟨y, hy, hyu⟩ := h _ Q' hQ'
  have comp (x : X ⟶ (Over.pullback a).obj P) : (Over.map a).map x ≫ c = E.symm x :=
    adj.homEquiv_counit _ _ _
  have comparison (x : X ⟶ (Over.pullback a).obj P) :
      SameFamily ((relativeFamily a (B.pullback c)).pullback x)
        (relativeFamily a (B.pullback (E.symm x))) := by
    refine sameFamily_trans (relativeFamily_pullback a _ x) ?_
    apply (relativeFamily_sameFamily a).mpr
    rw [← comp]
    exact sameFamily_pullback_comp B c ((Over.map a).map x)
  have hχ (x : X ⟶ (Over.pullback a).obj P) :
      SameFamily ((relativeFamily a (B.pullback c)).pullback x) Q ↔
        SameFamily (B.pullback (E.symm x)) Q' := by
    constructor
    · intro hx
      exact (relativeFamily_sameFamily a).mp
        (sameFamily_trans (sameFamily_symm (comparison x))
          (sameFamily_trans hx (sameFamily_symm (relativeAbsoluteFamily a Q))))
    · intro hx
      exact sameFamily_trans (comparison x)
        (sameFamily_trans ((relativeFamily_sameFamily a).mpr hx) (relativeAbsoluteFamily a Q))
  refine ⟨E y, (hχ _).mpr (by rwa [Equiv.symm_apply_apply]), ?_⟩
  intro v hv
  have hh := hyu (E.symm v) ((hχ v).mp hv)
  rw [← hh, Equiv.apply_symm_apply]

end FamilyBase

section FamilyAmbient

variable {S : Scheme.{u}} {G H : Grp (Over S)} {T U : Over S}

private def changeFamilyGroup (e : G ≅ H) (B : Family G T) : Family H T where
  group := B.group
  inclusion := B.inclusion ≫ ((changeBase T.hom).mapIso e).hom
  closed := closed_comp_groupIso B.inclusion ((changeBase T.hom).mapIso e) B.closed
  smooth := B.smooth

private theorem changeFamilyGroup_isBorel (e : G ≅ H) (B : Family G T) :
    IsBorelFamily (changeFamilyGroup e B) ↔ IsBorelFamily B := by
  let d := (changeBase T.hom).mapIso e
  change HasBorelFibres (B.inclusion ≫ d.hom) ↔ HasBorelFibres B.inclusion
  refine ⟨fun h ↦ ?_, hasBorelFibres_comp_iso d⟩
  have hh := hasBorelFibres_comp_iso d.symm h
  change HasBorelFibres ((B.inclusion ≫ d.hom) ≫ d.inv) at hh
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

private theorem changeFamilyGroup_sameFamily (e : G ≅ H) (B C : Family G T) :
    SameFamily (changeFamilyGroup e B) (changeFamilyGroup e C) ↔ SameFamily B C := by
  let d := (changeBase T.hom).mapIso e
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, (cancel_mono d.hom).mp ?_⟩
    change f.hom ≫ (C.inclusion ≫ d.hom) = B.inclusion ≫ d.hom at hf
    exact (Category.assoc _ _ _).trans hf
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    change f.hom ≫ (C.inclusion ≫ d.hom) = B.inclusion ≫ d.hom
    rw [← Category.assoc, hf]

private theorem changeFamilyGroup_inverse (e : G ≅ H) (B : Family H T) :
    SameFamily (changeFamilyGroup e (changeFamilyGroup e.symm B)) B := by
  let d := (changeBase T.hom).mapIso e
  refine ⟨Iso.refl _, ?_⟩
  change 𝟙 _ ≫ B.inclusion = (B.inclusion ≫ d.inv) ≫ d.hom
  rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem changeBaseCongr_naturality {C S' : Scheme.{u}} {a b : C ⟶ S'}
    (h : a = b) {G' H' : Grp (Over S')} (e : G' ⟶ H') :
    (changeBase a).map e ≫ (changeBaseCongr h H').hom =
      (changeBaseCongr h G').hom ≫ (changeBase b).map e := by
  subst b
  simp [changeBaseCongr]

set_option backward.isDefEq.respectTransparency false in
private theorem changeFamilyGroup_pullback (e : G ≅ H) (B : Family G T) (a : U ⟶ T) :
    SameFamily ((changeFamilyGroup e B).pullback a) (changeFamilyGroup e (B.pullback a)) := by
  let F := changeBase a.left
  let c := changeBaseComp a.left T.hom
  let w := Over.w a
  let d := F.map ((changeBase T.hom).map e.hom)
  let i := F.map B.inclusion
  have hd : d ≫ c.inv.app H = c.inv.app G ≫ (changeBase (a.left ≫ T.hom)).map e.hom :=
    c.inv.naturality e.hom
  have hw := changeBaseCongr_naturality w e.hom
  refine ⟨Iso.refl _, ?_⟩
  change 𝟙 _ ≫ ((i ≫ c.inv.app G ≫ (changeBaseCongr w G).hom) ≫ (changeBase U.hom).map e.hom) =
    F.map (B.inclusion ≫ (changeBase T.hom).map e.hom) ≫ c.inv.app H ≫ (changeBaseCongr w H).hom
  rw [Category.id_comp, F.map_comp]
  change (i ≫ c.inv.app G ≫ (changeBaseCongr w G).hom) ≫ (changeBase U.hom).map e.hom =
    (i ≫ d) ≫ c.inv.app H ≫ (changeBaseCongr w H).hom
  simp only [Category.assoc]
  rw [← hw, ← Category.assoc (c.inv.app G), ← hd, Category.assoc]

/-- An isomorphism of the original ambient groups transports a representing family. -/
theorem representsBorelFamilies_changeGroup (e : G ≅ H) {P : Over S} (B : Family G P)
    (h : ∀ (T : Over S) (Q : Family G T), IsBorelFamily Q →
      ∃! x : T ⟶ P, SameFamily (B.pullback x) Q)
    (T : Over S) (C : Family H T) (hC : IsBorelFamily C) :
    ∃! x : T ⟶ P, SameFamily ((changeFamilyGroup e B).pullback x) C := by
  let C' := changeFamilyGroup e.symm C
  obtain ⟨y, hy, huy⟩ := h T C' ((changeFamilyGroup_isBorel e.symm C).mpr hC)
  have cmp (x : T ⟶ P) : SameFamily ((changeFamilyGroup e B).pullback x) C ↔
      SameFamily (B.pullback x) C' :=
    ⟨fun hx ↦ (changeFamilyGroup_sameFamily e _ _).mp
        (sameFamily_trans (sameFamily_symm (changeFamilyGroup_pullback e B x))
          (sameFamily_trans hx (sameFamily_symm (changeFamilyGroup_inverse e C)))),
      fun hx ↦ sameFamily_trans (changeFamilyGroup_pullback e B x)
        (sameFamily_trans ((changeFamilyGroup_sameFamily e _ _).mpr hx)
          (changeFamilyGroup_inverse e C))⟩
  exact ⟨y, (cmp y).mpr hy, fun x hx ↦ huy x ((cmp x).mp hx)⟩

end FamilyAmbient

section ClosedDescent

variable {V W X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
private theorem injective_app_of_flat_surjective (f : V ⟶ W) [Flat f] [Surjective f] (U : W.Opens) :
    Function.Injective (f.app U) := by
  intro a b h
  apply TopCat.Presheaf.section_ext W.sheaf U
  intro y hy
  obtain ⟨x, rfl⟩ := f.surjective y
  have hflat : RingHom.Flat (f.stalkMap x).hom := Flat.stalkMap f x
  have hlocal : IsLocalHom (f.stalkMap x).hom := f.toLRSHom.prop x
  have hf : (f.stalkMap x).hom.FaithfullyFlat := by
    let := (f.stalkMap x).hom.toAlgebra
    apply RingHom.faithfullyFlat_algebraMap_iff.mpr
    exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (RingHom.flat_algebraMap_iff.mp hflat) hlocal
  apply hf.injective
  change f.stalkMap x (W.presheaf.germ U (f x) hy a) =
    f.stalkMap x (W.presheaf.germ U (f x) hy b)
  rw [f.germ_stalkMap_apply, f.germ_stalkMap_apply, h]

private theorem schemeTheoreticallyDominant_of_flat_surjective (f : V ⟶ W)
    [Flat f] [Surjective f] [QuasiCompact f] : IsSchemeTheoreticallyDominant f := by
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (injective_app_of_flat_surjective f U)

private theorem ker_comp_of_dominant (f : V ⟶ W) (g : W ⟶ X)
    [QuasiCompact f] [QuasiCompact g] [IsSchemeTheoreticallyDominant f] :
    (f ≫ g).ker = g.ker := by
  rw [Scheme.Hom.ker_comp, f.ker_eq_bot, Scheme.IdealSheafData.map_bot]

set_option backward.isDefEq.respectTransparency false in
/-- A closed subscheme invariant on the two pullbacks along a faithfully
flat quasi-compact cover descends as the schematic image in the base. -/
theorem closedImmersionOfDescent (a : V ⟶ W) [Flat a] [Surjective a] [QuasiCompact a]
    (i : X ⟶ V) [IsClosedImmersion i]
    {L M : Scheme.{u}} {p q : L ⟶ V} {s t : M ⟶ X} {b : M ⟶ L}
    (hp : IsPullback p q a a) (hs : IsPullback s b i p) (ht : IsPullback t b i q) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ W), IsClosedImmersion j ∧
      ∃ d : X ≅ pullback j a, d.hom ≫ pullback.snd j a = i := by
  let d := i ≫ a
  let j := d.imageι
  have H : IsPullback s (b ≫ q) d a := hs.paste_vert hp
  have hqF : Flat q := MorphismProperty.of_isPullback hp ‹Flat a›
  have hqS : Surjective q := MorphismProperty.of_isPullback hp ‹Surjective a›
  have hqQ : QuasiCompact q := MorphismProperty.of_isPullback hp ‹QuasiCompact a›
  have htF : Flat t := MorphismProperty.of_isPullback ht.flip hqF
  have htS : Surjective t := MorphismProperty.of_isPullback ht.flip hqS
  have htQ : QuasiCompact t := MorphismProperty.of_isPullback ht.flip hqQ
  have hc : IsSchemeTheoreticallyDominant t := schemeTheoreticallyDominant_of_flat_surjective t
  have hbc' : (b ≫ q).ker = i.ker := by rw [← ht.w, ker_comp_of_dominant]
  have hk : (b ≫ q).ker = d.ker.comap a := by
    rw [← H.isoPullback_hom_snd, ker_comp_of_dominant]
    exact kernelOfFlatPullback d a
  have hj : IsClosedImmersion j := inferInstance
  have hk' : i.ker = (pullback.snd j a).ker := by
    rw [kernelOfFlatPullback j a, Scheme.IdealSheafData.ker_subschemeι]
    exact hbc'.symm.trans hk
  let h := IsClosedImmersion.lift (pullback.snd j a) i hk'.ge
  have hiso : IsIso h := IsClosedImmersion.isIso_lift _ _ hk'.symm
  exact ⟨_, j, hj, asIso h, IsClosedImmersion.lift_fac _ _ _⟩

end ClosedDescent

section FamilyDescent

private theorem whiskerLeft_isPullback {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    (W : C) {L A B X : C} {p : L ⟶ A} {q : L ⟶ B} {f : A ⟶ X} {g : B ⟶ X}
    (h : IsPullback p q f g) : IsPullback (W ◁ p) (W ◁ q) (W ◁ f) (W ◁ g) := by
  refine IsPullback.mk' (by rw [← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp, h.w]) ?_ ?_
  · intro Z r s hr hs
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst W A) hr
    · apply h.hom_ext
      · simpa only [Category.assoc, whiskerLeft_snd] using congrArg (· ≫ snd W A) hr
      · simpa only [Category.assoc, whiskerLeft_snd] using congrArg (· ≫ snd W B) hs
  · intro Z r s he
    have hv : (r ≫ snd W A) ≫ f = (s ≫ snd W B) ≫ g := by
      simpa only [Category.assoc, whiskerLeft_snd] using congrArg (· ≫ snd W X) he
    have hf : r ≫ fst W A = s ≫ fst W B := by
      simpa only [Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst W X) he
    let t := h.lift (r ≫ snd W A) (s ≫ snd W B) hv
    refine ⟨lift (r ≫ fst W A) t, ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, whiskerLeft_fst, lift_fst]
      · simp only [Category.assoc, whiskerLeft_snd, lift_snd_assoc, t, IsPullback.lift_fst]
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, whiskerLeft_fst, lift_fst, hf]
      · simp only [Category.assoc, whiskerLeft_snd, lift_snd_assoc, t, IsPullback.lift_snd]

variable {S : Scheme.{u}} {G : Grp (Over S)} {X Y : Over S}

set_option backward.isDefEq.respectTransparency false in
private theorem descendFamilyOfClosedPullback (a : Y ⟶ X) [Surjective a.left] [Flat a.left]
    [QuasiCompact a.left] (Q : Family G Y) {Z : Scheme.{u}} (k : Z ⟶ (G.X ⊗ X).left)
    (hk : IsClosedImmersion k) (r : Q.group.X.left ⟶ Z)
    (h : IsPullback r (familyProductInclusion Q).left k (G.X ◁ a).left) :
    ∃ B : Family G X, SameFamily (B.pullback a) Q := by
  let A := (changeBase X.hom).obj G
  let Z' : Over X.left := Over.mk (k ≫ (snd G.X X).left)
  let l : Z' ⟶ A.X := Over.homMk k
  have hl : IsClosedImmersion l.left := hk
  have hQi : (familyProductInclusion Q).left ≫ (snd G.X Y).left = Q.group.X.hom := by
    rw [familyProductInclusion_left]
    exact Over.w Q.inclusion.hom.hom
  have hS : IsPullback r Q.group.X.hom Z'.hom a.left := by
    rw [← hQi]
    exact h.paste_vert ((productPullback G.X a).map (Over.forget S))
  let e : Q.group.X ≅ (Over.pullback a.left).obj Z' :=
    Over.isoMk hS.isoPullback hS.isoPullback_hom_snd
  let d := compareAmbient a G
  let m := Q.inclusion ≫ d.hom
  have he : e.hom ≫ (Over.pullback a.left).map l = m.hom.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (e.hom.left ≫ ((Over.pullback a.left).map l).left) ≫ pullback.fst A.X.hom a.left =
        (Q.inclusion.hom.hom.left ≫ d.hom.hom.hom.left) ≫ pullback.fst A.X.hom a.left
      rw [Category.assoc, Category.assoc, compareAmbient_first, (pullbackMapSquare a.left l).w,
        ← Category.assoc, show e.hom.left ≫ pullback.fst Z'.hom a.left = r
          from hS.isoPullback_hom_fst, ← familyProductInclusion_left]
      exact h.w
    · exact (Over.w (e.hom ≫ (Over.pullback a.left).map l)).trans (Over.w m.hom.hom).symm
  obtain ⟨H, j, _, _, hjs, hjc, v, hv⟩ := descendSubgroupFromIso a.left l m Q.smooth e he
  let B : Family G X := ⟨H, j, hjc, hjs⟩
  refine ⟨B, v, ?_⟩
  change v.hom ≫ Q.inclusion = (changeBase a.left).map j ≫ d.inv
  rw [← hv]
  change _ = (v.hom ≫ Q.inclusion ≫ d.hom) ≫ d.inv
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Descent of the universal closed subgroup as a family once its base
scheme has descended. -/
theorem familyOfDescent (a : Y ⟶ X) [Surjective a.left] [Flat a.left] [QuasiCompact a.left]
    (Q : Family G Y)
    (hQ : SameFamily (Q.pullback (pullback.fst a a)) (Q.pullback (pullback.snd a a))) :
    ∃ B : Family G X, SameFamily (B.pullback a) Q := by
  let L := pullback a a
  let p := pullback.fst a a
  let q := pullback.snd a a
  let i := familyProductInclusion Q
  let k₁ := familyProductInclusion (Q.pullback p)
  let k₂ := familyProductInclusion (Q.pullback q)
  let s := familyRestriction Q p
  let t := familyRestriction Q q
  obtain ⟨e, he⟩ := hQ
  let d := (Grp.forget (Over L.left) ⋙ Over.map L.hom).mapIso e
  have hd : d.hom ≫ k₂ = k₁ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, familyProductInclusion_left, familyProductInclusion_left]
    exact congrArg (fun f ↦ f.hom.hom.left) he
  have h1 := (familyProductPullback_over Q p).flip
  have h2 := (familyProductPullback_over Q q).flip
  have h2' : IsPullback (d.hom ≫ t) k₁ i (G.X ◁ q) := by
    apply h2.of_iso' d (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · rw [Iso.refl_hom, Category.comp_id]
    · rw [Iso.refl_hom, Category.comp_id]; exact hd
    · simp [i]
    · simp
  let F := Over.forget S
  have hp := (whiskerLeft_isPullback G.X (IsPullback.of_hasPullback a a)).map F
  have h₀ := (productPullback G.X a).map F
  have hfa : Flat (G.X ◁ a).left := MorphismProperty.of_isPullback h₀.flip ‹Flat a.left›
  have hsu : Surjective (G.X ◁ a).left := MorphismProperty.of_isPullback h₀.flip ‹Surjective a.left›
  have hqc : QuasiCompact (G.X ◁ a).left := MorphismProperty.of_isPullback h₀.flip ‹QuasiCompact a.left›
  have hci : IsClosedImmersion i.left := familyProductInclusion_left Q ▸ Q.closed
  obtain ⟨Z, k, hk, f, hf⟩ := closedImmersionOfDescent (G.X ◁ a).left i.left hp (h1.map F) (h2'.map F)
  let r := f.hom ≫ pullback.fst k (G.X ◁ a).left
  have hr : IsPullback r i.left k (G.X ◁ a).left := by
    apply IsPullback.of_iso_pullback _ f rfl hf
    constructor
    rw [← hf, Category.assoc, pullback.condition, Category.assoc]
  exact descendFamilyOfClosedPullback a Q k hk r hr

/-- Borel fibres descend along a finite faithfully flat cover with the family. -/
theorem borelFamilyOfDescent [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [QuasiCompact G.X.hom] (a : Y ⟶ X) [Surjective a.left] [Flat a.left] [IsFinite a.left]
    (Q : Family G Y) (hB : IsBorelFamily Q)
    (hQ : SameFamily (Q.pullback (pullback.fst a a)) (Q.pullback (pullback.snd a a))) :
    ∃ B : Family G X, IsBorelFamily B ∧ SameFamily (B.pullback a) Q := by
  obtain ⟨B, h⟩ := familyOfDescent a Q hQ
  exact ⟨B, isBorelFamily_of_pullback_pointLifts a (liftAlgebraicallyClosedPoint a.left) B Q h hB, h⟩

end FamilyDescent

section SplitCoverClassification

/-- On the specified finite étale splitting cover, the split parameter scheme
classifies the smooth closed Borel families of the actual group. -/
theorem separatedBorelClassificationOnSplittingCover {R : Type u} [CommRing R]
    {G : Grp (Over (ringSpec R))} (hG : HasSplitModel G) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (_ : Module.Finite R A) (_ : Module.FaithfullyFlat R A) (_ : Algebra.Etale R A)
      (P : Over (ringSpec A)) (U : Family ((changeBase (algebraSpecMap R A)).obj G) P),
      Smooth P.hom ∧ IsSeparated P.hom ∧ IsBorelFamily U ∧
        ∀ (T : Over (ringSpec A)) (B : Family ((changeBase (algebraSpecMap R A)).obj G) T),
          IsBorelFamily B → ∃! x : T ⟶ P, SameFamily (U.pullback x) B := by
  obtain ⟨A, _, _, hfinite, hflat, het, D, _, M, ⟨e⟩⟩ := hG
  obtain ⟨P, U, hP, hsep, hU, hrep⟩ := integralBorelRepresentsSeparated M
  have : IsAffine M.group.X.left := M.affine
  have : IsAffineHom M.group.X.hom := inferInstance
  have : LocallyOfFinitePresentation M.group.X.hom := M.locallyOfFinitePresentation
  have : QuasiCompact M.group.X.hom := M.quasiCompact
  let z := integralSpecMap A
  let P' := (Over.pullback z).obj P
  let c := (Over.mapPullbackAdj z).counit.app P
  let B := relativeFamily z (U.pullback c)
  let B' := changeFamilyGroup e.symm B
  have hB : IsBorelFamily B :=
    (relativeFamily_isBorel z _).mpr (isBorelFamily_pullback U hU c)
  have hB' : IsBorelFamily B' := (changeFamilyGroup_isBorel e.symm B).mpr hB
  have hP' : Smooth P'.hom := inferInstanceAs (Smooth (pullback.snd P.hom z))
  have hsep' : IsSeparated P'.hom := inferInstanceAs (IsSeparated (pullback.snd P.hom z))
  refine ⟨A, _, _, hfinite, hflat, het, P', B', hP', hsep', hB', ?_⟩
  exact representsBorelFamilies_changeGroup e.symm B (representsBorelFamilies_pullback z U hrep)

theorem borelClassificationOnSplittingCover {R : Type u} [CommRing R]
    {G : Grp (Over (ringSpec R))} (hG : HasSplitModel G) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
      (_ : Module.Finite R A) (_ : Module.FaithfullyFlat R A) (_ : Algebra.Etale R A)
      (P : Over (ringSpec A)) (U : Family ((changeBase (algebraSpecMap R A)).obj G) P),
      Smooth P.hom ∧ IsBorelFamily U ∧
        ∀ (T : Over (ringSpec A)) (B : Family ((changeBase (algebraSpecMap R A)).obj G) T),
          IsBorelFamily B → ∃! x : T ⟶ P, SameFamily (U.pullback x) B := by
  obtain ⟨A, _, _, hfin, hflat, het, P, U, hP, _, hU, hrep⟩ :=
    separatedBorelClassificationOnSplittingCover hG
  exact ⟨A, _, _, hfin, hflat, het, P, U, hP, hU, hrep⟩

end SplitCoverClassification

section AbsoluteClassification

variable {S S' : Scheme.{u}} {G : Grp (Over S)} {P X : Over S'}

private theorem absoluteRepresentation (a : S' ⟶ S)
    (B : Family ((changeBase a).obj G) P)
    (h : ∀ (T : Over S') (Q : Family ((changeBase a).obj G) T), IsBorelFamily Q →
      ∃! x : T ⟶ P, SameFamily (B.pullback x) Q)
    (C : Family G ((Over.map a).obj X)) (hC : IsBorelFamily C) :
    ∃! x : X ⟶ P, SameFamily ((absoluteFamily a B).pullback ((Over.map a).map x)) C := by
  have cmp (x : X ⟶ P) :
      SameFamily ((absoluteFamily a B).pullback ((Over.map a).map x)) C ↔
        SameFamily (B.pullback x) (relativeFamily a C) := by
    let A := absoluteFamily a B
    have he : SameFamily (B.pullback x) (relativeFamily a (A.pullback ((Over.map a).map x))) :=
      sameFamily_trans (sameFamily_pullback (sameFamily_symm (relativeAbsoluteFamily a B)) x)
        (relativeFamily_pullback a A x)
    refine (relativeFamily_sameFamily a).symm.trans ⟨?_, ?_⟩
    · exact sameFamily_trans he
    · exact sameFamily_trans (sameFamily_symm he)
  obtain ⟨x, hx, hu⟩ := h X (relativeFamily a C) ((relativeFamily_isBorel a C).mpr hC)
  exact ⟨x, (cmp x).mpr hx, fun y hy ↦ hu y ((cmp y).mp hy)⟩

end AbsoluteClassification

section ClassificationDescent

variable {S S' : Scheme.{u}} {G : Grp (Over S)} {P : Over S}
variable [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- A Borel family on a descended scheme is universal if its pullback is
universal on the faithfully flat quasi-compact cover. -/
theorem representsBorelFamilies_of_cover (a : S' ⟶ S) [Surjective a] [Flat a] [QuasiCompact a]
    (B : Family G P) (hB : IsBorelFamily B)
    (h : ∀ (X : Over S') (Q : Family G ((Over.map a).obj X)), IsBorelFamily Q →
      ∃! x : (Over.map a).obj X ⟶ P, SameFamily (B.pullback x) Q)
    (T : Over S) (Q : Family G T) (hQ : IsBorelFamily Q) :
    ∃! x : T ⟶ P, SameFamily (B.pullback x) Q := by
  let F := Over.pullback a
  let J := Over.map a
  let adj := Over.mapPullbackAdj a
  have hcov (X : Over S) :
      Flat (adj.counit.app X).left ∧ Surjective (adj.counit.app X).left ∧
        QuasiCompact (adj.counit.app X).left := by
    change Flat (pullback.fst X.hom a) ∧ Surjective (pullback.fst X.hom a) ∧
      QuasiCompact (pullback.fst X.hom a)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hinj {X : Over S} (f g : X ⟶ P)
      (he : SameFamily (B.pullback f) (B.pullback g)) : f = g := by
    let p := adj.counit.app X
    obtain ⟨hp, hs, hq⟩ := hcov X
    have : Epi p := Over.epi_of_epi_left p
    let C := (B.pullback g).pullback p
    have hC : IsBorelFamily C :=
      isBorelFamily_pullback _ (isBorelFamily_pullback B hB g) p
    have hpf : SameFamily (B.pullback (p ≫ f)) C :=
      sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp B f p)) (sameFamily_pullback he p)
    have hpg : SameFamily (B.pullback (p ≫ g)) C :=
      sameFamily_symm (sameFamily_pullback_comp B g p)
    exact (cancel_epi p).mp ((h (F.obj X) C hC).unique hpf hpg)
  let p := adj.counit.app T
  obtain ⟨hp, hs, hq⟩ := hcov T
  obtain ⟨f, hf, _⟩ := h (F.obj T) (Q.pullback p) (isBorelFamily_pullback Q hQ p)
  have hdesc (W : Over S) (b c : W ⟶ _) (he : b ≫ p = c ≫ p) : b ≫ f = c ≫ f := by
    have cmp (v : W ⟶ J.obj (F.obj T)) :
        SameFamily (B.pullback (v ≫ f)) (Q.pullback (v ≫ p)) :=
      sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp B f v))
        (sameFamily_trans (sameFamily_pullback hf v) (sameFamily_pullback_comp Q p v))
    have hb := cmp b
    rw [he] at hb
    exact hinj _ _ (sameFamily_trans hb (sameFamily_symm (cmp c)))
  obtain ⟨x, hx⟩ := existsOverDesc p f hdesc
  have hsame : SameFamily (B.pullback x) Q := by
    apply sameFamily_of_same_pullback p
    refine sameFamily_trans (sameFamily_pullback_comp B x p) ?_
    rwa [hx]
  exact ⟨x, hsame, fun y hy ↦ hinj y x (sameFamily_trans hy (sameFamily_symm hsame))⟩

end ClassificationDescent

section DescendedPresentation

variable {S S' : Scheme.{u}} {G : Grp (Over S)} {P : Over S} {P' : Over S'}
variable [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]

set_option backward.isDefEq.respectTransparency false in
private def baseChangeHomEquiv (a : S' ⟶ S) (v : (Over.map a).obj P' ⟶ P)
    (hv : IsPullback v.left P'.hom P.hom a) (X : Over S') :
    (X ⟶ P') ≃ ((Over.map a).obj X ⟶ P) where
  toFun x := (Over.map a).map x ≫ v
  invFun q := Over.homMk (hv.lift q.left X.hom (Over.w q)) (hv.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply hv.hom_ext
    · exact hv.lift_fst _ _ _
    · exact (hv.lift_snd _ _ _).trans (Over.w x).symm
  right_inv q := Over.OverMorphism.ext (hv.lift_fst _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- After effective descent of the parameter scheme, an invariant universal
Borel family descends and retains the representing property. -/
theorem borelClassificationOfDescendedParameter
    (a : S' ⟶ S) [Surjective a] [Flat a] [IsFinite a]
    (v : (Over.map a).obj P' ⟶ P) (hv : IsPullback v.left P'.hom P.hom a)
    (hSmooth : Smooth P'.hom) (B' : Family ((changeBase a).obj G) P')
    (hB' : IsBorelFamily B')
    (hrep : ∀ (X : Over S') (C : Family ((changeBase a).obj G) X), IsBorelFamily C →
      ∃! x : X ⟶ P', SameFamily (B'.pullback x) C)
    (hD : SameFamily ((absoluteFamily a B').pullback (pullback.fst v v))
      ((absoluteFamily a B').pullback (pullback.snd v v))) :
    Smooth P.hom ∧ ∃ B : Family G P, IsBorelFamily B ∧
      ∀ (T : Over S) (C : Family G T), IsBorelFamily C →
        ∃! x : T ⟶ P, SameFamily (B.pullback x) C := by
  have hs : Smooth P.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hv.flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hSmooth
  have hvf : Flat v.left := MorphismProperty.of_isPullback hv.flip ‹Flat a›
  have hvs : Surjective v.left := MorphismProperty.of_isPullback hv.flip ‹Surjective a›
  have hvq : IsFinite v.left := MorphismProperty.of_isPullback hv.flip ‹IsFinite a›
  let B₀ := absoluteFamily a B'
  have hB₀ : IsBorelFamily B₀ := (absoluteFamily_isBorel a B').mpr hB'
  obtain ⟨B, hB, he⟩ := borelFamilyOfDescent v B₀ hB₀ hD
  refine ⟨hs, B, hB, representsBorelFamilies_of_cover a B hB ?_⟩
  intro X C hC
  let E := baseChangeHomEquiv a v hv X
  have cmp (x : X ⟶ P') :
      SameFamily (B.pullback (E x)) ((B₀.pullback ((Over.map a).map x))) :=
    sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp B v ((Over.map a).map x)))
      (sameFamily_pullback he ((Over.map a).map x))
  obtain ⟨x, hx, hu⟩ := absoluteRepresentation a B' hrep C hC
  refine ⟨E x, sameFamily_trans (cmp x) hx, ?_⟩
  intro y hy
  have hy' : SameFamily (B.pullback (E (E.symm y))) C := (E.apply_symm_apply y).symm ▸ hy
  have hh := hu (E.symm y) (sameFamily_trans (sameFamily_symm (cmp (E.symm y))) hy')
  exact (E.apply_symm_apply y).symm.trans (congrArg E hh)

end DescendedPresentation

section ParameterDescent

variable {S : Scheme.{u}} {A V : Over S}

/-- Descent of a scheme over a cover, expressed as transport along a second
map to the covering scheme. -/
structure ParameterDescent (v : V ⟶ A) where
  transport : V ⊗ A ⟶ V
  base : transport ≫ v = snd V A
  identity : lift (𝟙 V) v ≫ transport = 𝟙 V
  composition : ∀ {T : Over S} (x : T ⟶ V) (b c : T ⟶ A),
    lift (lift x b ≫ transport) c ≫ transport = lift x c ≫ transport

namespace ParameterDescent

variable {v : V ⟶ A} (d : ParameterDescent v)

/-- Transport a point of the parameter to a new point of the covering base. -/
def change {T : Over S} (x : T ⟶ V) (b : T ⟶ A) : T ⟶ V :=
  lift x b ≫ d.transport

@[reassoc (attr := simp)]
theorem change_over {T : Over S} (x : T ⟶ V) (b : T ⟶ A) :
    d.change x b ≫ v = b := by simp [change, d.base]

@[simp]
theorem change_identity {T : Over S} (x : T ⟶ V) : d.change x (x ≫ v) = x := by
  have h : x ≫ lift (𝟙 V) v = lift x (x ≫ v) := by simp only [comp_lift, Category.comp_id]
  rw [change, ← h, Category.assoc, d.identity, Category.comp_id]

@[simp]
theorem change_change {T : Over S} (x : T ⟶ V) (b c : T ⟶ A) :
    d.change (d.change x b) c = d.change x c := d.composition x b c

@[simp]
theorem comp_change {T W : Over S} (f : W ⟶ T) (x : T ⟶ V) (b : T ⟶ A) :
    f ≫ d.change x b = d.change (f ≫ x) (f ≫ b) := by
  simp only [change, ← Category.assoc, comp_lift]

end ParameterDescent

variable {S' : Scheme.{u}} {G : Grp (Over S)} {P : Over S'}

/-- The family on the overlap determines descent transport through its unique
classifying map with the new base point. -/
theorem existsParameterDescent (a : S' ⟶ S)
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (B : Family ((changeBase a).obj G) P) (hB : IsBorelFamily B)
    (hrep : ∀ (T : Over S') (C : Family ((changeBase a).obj G) T), IsBorelFamily C →
      ∃! x : T ⟶ P, SameFamily (B.pullback x) C) :
    let V := (Over.map a).obj P
    let v : V ⟶ Over.mk a := Over.homMk P.hom
    ∃ d : ParameterDescent v, ∀ {T : Over S} (x : T ⟶ V) (b : T ⟶ Over.mk a),
      SameFamily ((absoluteFamily a B).pullback (d.change x b)) ((absoluteFamily a B).pullback x) := by
  intro V v
  let A := Over.mk a
  let U := absoluteFamily a B
  have hU : IsBorelFamily U := (absoluteFamily_isBorel a B).mpr hB
  have localTransport {T : Over S} (x : T ⟶ V) (b : T ⟶ A) :
      ∃! y : T ⟶ V, y ≫ v = b ∧ SameFamily (U.pullback y) (U.pullback x) := by
    let X := Over.mk b.left
    let T' := (Over.map a).obj X
    let i : T ≅ T' := Over.isoMk (Iso.refl _) (by exact (Category.id_comp _).trans (CategoryTheory.Over.w b))
    obtain ⟨y, hy, hu⟩ := absoluteRepresentation a B hrep (U.pullback (i.inv ≫ x))
      (isBorelFamily_pullback U hU _)
    let y' := i.hom ≫ (Over.map a).map y
    have hy'b : y' ≫ v = b := by
      apply Over.OverMorphism.ext
      exact (Category.id_comp _).trans (CategoryTheory.Over.w y)
    have hy'U : SameFamily (U.pullback y') (U.pullback x) := by
      refine sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp U _ i.hom))
        (sameFamily_trans (sameFamily_pullback hy i.hom) ?_)
      have h := sameFamily_pullback_comp U (i.inv ≫ x) i.hom
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at h
      exact h
    refine ⟨y', ⟨hy'b, hy'U⟩, ?_⟩
    intro z hz
    let z' : X ⟶ P := Over.homMk z.left (congrArg Over.Hom.left hz.1)
    have hz' : (Over.map a).map z' = i.inv ≫ z := by
      apply Over.OverMorphism.ext
      exact (Category.id_comp _).symm
    have hzu : SameFamily (U.pullback ((Over.map a).map z')) (U.pullback (i.inv ≫ x)) := by
      rw [hz']
      exact sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp U z i.inv))
        (sameFamily_trans (sameFamily_pullback hz.2 i.inv) (sameFamily_pullback_comp U x i.inv))
    have hzy := congrArg ((Over.map a).map) (hu z' hzu)
    rw [hz'] at hzy
    dsimp only [y']
    rw [← hzy, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  obtain ⟨τ, ⟨hτ, hcomp⟩, _⟩ := localTransport (fst V A) (snd V A)
  have hτ' {T : Over S} (x : T ⟶ V) (b : T ⟶ A) :
      SameFamily (U.pullback (lift x b ≫ τ)) (U.pullback x) := by
    have h := sameFamily_pullback hcomp (lift x b)
    refine sameFamily_trans (sameFamily_symm (sameFamily_pullback_comp U τ _))
      (sameFamily_trans h ?_)
    have hh := sameFamily_pullback_comp U (fst V A) (lift x b)
    have he : lift x b ≫ fst V A = x := lift_fst x b
    rw [he] at hh
    exact hh
  have hbase {T : Over S} (x : T ⟶ V) (b : T ⟶ A) : (lift x b ≫ τ) ≫ v = b := by
    rw [Category.assoc, hτ]
    exact lift_snd x b
  refine ⟨⟨τ, hτ, ?_, ?_⟩, hτ'⟩
  · exact (localTransport (𝟙 V) v).unique
      ⟨hbase (𝟙 V) v, hτ' (𝟙 V) v⟩ ⟨Category.id_comp v, sameFamily_refl _⟩
  · intro T x b c
    exact (localTransport x c).unique
      ⟨hbase _ c, sameFamily_trans (hτ' _ c) (hτ' x b)⟩ ⟨hbase x c, hτ' x c⟩

end ParameterDescent

section AffineParameterDescent

open Algebra.TensorProduct

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

private theorem coordSpecMap_injective {f g : A →ₐ[R] B}
    (h : coordSpecMap f = coordSpecMap g) : f = g :=
  congrArg (fun f : op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R A) ↦ f.unop.hom)
    ((algSpec.fullyFaithful (R := CommRingCat.of R)).map_injective h)

private theorem exists_coordSpecMap (f : coordSpec R B ⟶ coordSpec R A) :
    ∃ g : A →ₐ[R] B, coordSpecMap g = f := by
  let e := (algSpec.fullyFaithful (R := CommRingCat.of R)).preimage f
  exact ⟨e.unop.hom, (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage f⟩

private def coordProductIso (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    coordSpec R (A ⊗[R] B) ≅ coordSpec R A ⊗ coordSpec R B :=
  Over.isoMk (pullbackSpecIso R A B).symm (by
    change (pullbackSpecIso R A B).inv ≫
      (pullback.fst (algebraSpecMap R A) (algebraSpecMap R B) ≫ algebraSpecMap R A) =
        algebraSpecMap R (A ⊗[R] B)
    rw [pullbackSpecIso_inv_fst_assoc, ← Spec.map_comp]
    rfl)

@[reassoc]
private theorem coordProductIso_fst :
    (coordProductIso R A B).hom ≫ fst _ _ = coordSpecMap (includeLeft : A →ₐ[R] A ⊗[R] B) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact pullbackSpecIso_inv_fst R A B

@[reassoc]
private theorem coordProductIso_snd :
    (coordProductIso R A B).hom ≫ snd _ _ = coordSpecMap (includeRight : B →ₐ[R] A ⊗[R] B) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact pullbackSpecIso_inv_snd R A B

private theorem lift_coordSpecMap (f : A →ₐ[R] C) (g : B →ₐ[R] C) :
    lift (coordSpecMap f) (coordSpecMap g) =
      coordSpecMap (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)) ≫
        (coordProductIso R A B).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.assoc, coordProductIso_fst, ← coordSpecMap_comp]
    congr 1
    ext a
    simp
  · rw [lift_snd, Category.assoc, coordProductIso_snd, ← coordSpecMap_comp]
    congr 1
    ext b
    simp

section AlgebraDescent

variable [Algebra A B] [IsScalarTower R A B]

private abbrev coordBase (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    coordSpec R B ⟶ coordSpec R A := coordSpecMap ((Algebra.ofId A B).restrictScalars R)

set_option backward.isDefEq.respectTransparency false in
private theorem ParameterDescent.exists_coaction (d : ParameterDescent (coordBase R A B)) :
    ∃ e : AffineDescentData R A B,
      coordSpecMap (e.coaction.restrictScalars R) =
        (coordProductIso R A B).hom ≫ lift (snd _ _) (fst _ _) ≫ d.transport := by
  let w := (coordProductIso R A B).hom
  let v := coordBase R A B
  let l : coordSpec R (A ⊗[R] B) ⟶ coordSpec R B := w ≫ snd _ _
  let r : coordSpec R (A ⊗[R] B) ⟶ coordSpec R A := w ≫ fst _ _
  obtain ⟨f, hf⟩ := exists_coordSpecMap (d.change l r)
  have hfle : f.comp ((Algebra.ofId A B).restrictScalars R) = includeLeft := by
    apply coordSpecMap_injective
    rw [coordSpecMap_comp, hf]
    exact (d.change_over l r).trans coordProductIso_fst
  let α : B →ₐ[A] A ⊗[R] B :=
    { f.toRingHom with commutes' := fun a ↦ congrArg (fun g : A →ₐ[R] A ⊗[R] B ↦ g a) hfle }
  change coordSpecMap (α.restrictScalars R) = _ at hf
  have hl : l = coordSpecMap (includeRight : B →ₐ[R] A ⊗[R] B) := coordProductIso_snd
  have hr : r = coordSpecMap (includeLeft : A →ₐ[R] A ⊗[R] B) := coordProductIso_fst
  have hchange {D : Type u} [CommRing D] [Algebra R D] (p : A →ₐ[R] D) (q : B →ₐ[R] D) :
      d.change (coordSpecMap q) (coordSpecMap p) =
        coordSpecMap ((Algebra.TensorProduct.lift p q (fun _ _ ↦ Commute.all _ _)).comp
          (α.restrictScalars R)) := by
    rw [coordSpecMap_comp, hf, ParameterDescent.comp_change]
    have hh := lift_coordSpecMap p q
    have hp := congrArg (· ≫ fst (coordSpec R A) (coordSpec R B)) hh
    have hq := congrArg (· ≫ snd (coordSpec R A) (coordSpec R B)) hh
    rw [lift_fst, Category.assoc] at hp
    rw [lift_snd, Category.assoc] at hq
    change coordSpecMap p = _ ≫ r at hp
    change coordSpecMap q = _ ≫ l at hq
    rw [← hp, ← hq]
  refine ⟨⟨α, ?_, ?_⟩, hf.trans ?_⟩
  · have h := (d.change_identity (𝟙 (coordSpec R B)))
    have he : coordSpecMap (AlgHom.id R B) = 𝟙 (coordSpec R B) := (ringAlgebraSpec R).map_id _
    change d.change (𝟙 (coordSpec R B)) (𝟙 (coordSpec R B) ≫ v) = _ at h
    rw [Category.id_comp, ← he] at h
    change d.change _ (coordSpecMap ((Algebra.ofId A B).restrictScalars R)) = _ at h
    rw [hchange] at h
    have heq := coordSpecMap_injective h
    intro b
    exact congrArg (fun g : B →ₐ[R] B ↦ g b) heq
  · intro b
    let D := A ⊗[R] (A ⊗[R] B)
    let p : A →ₐ[R] D := includeRight.comp includeLeft
    let q : A →ₐ[R] D := includeLeft
    let x : B →ₐ[R] D := includeRight.comp includeRight
    have h₁ : Algebra.TensorProduct.lift p x (fun _ _ ↦ Commute.all _ _) =
        (includeRight : A ⊗[R] B →ₐ[R] D) := by
      apply Algebra.TensorProduct.ext
      · exact lift_comp_includeLeft _ _ _
      · exact lift_comp_includeRight _ _ _
    have h₂ : Algebra.TensorProduct.lift q (includeRight.comp (α.restrictScalars R))
        (fun _ _ ↦ Commute.all _ _) = map (AlgHom.id R A) (α.restrictScalars R) := by
      apply Algebra.TensorProduct.ext
      · rw [lift_comp_includeLeft, map_comp_includeLeft, AlgHom.comp_id]
      · rw [lift_comp_includeRight, map_restrictScalars_comp_includeRight]
    have h₃ : Algebra.TensorProduct.lift q x (fun _ _ ↦ Commute.all _ _) =
        map (AlgHom.id R A) (includeRight : B →ₐ[R] A ⊗[R] B) := by
      apply Algebra.TensorProduct.ext
      · rw [lift_comp_includeLeft, map_comp_includeLeft, AlgHom.comp_id]
      · rw [lift_comp_includeRight, map_restrictScalars_comp_includeRight]
    have hh := d.change_change (coordSpecMap x) (coordSpecMap p) (coordSpecMap q)
    rw [hchange p x, h₁, hchange, h₂, hchange q x, h₃] at hh
    exact congrArg (fun g : B →ₐ[R] D ↦ g b) (coordSpecMap_injective hh)
  · change lift l r ≫ d.transport = w ≫ lift (snd _ _) (fst _ _) ≫ d.transport
    rw [← Category.assoc, comp_lift]

set_option backward.isDefEq.respectTransparency false in
private theorem affineDescentIso_tmul (d : AffineDescentData R A B) [Module.Flat R A]
    (a : A) (c : d.fixedAlgebra) : d.baseChangeIso (a ⊗ₜ[R] c) = algebraMap A B a * c.val := by
  change (AffineDescentData.coactionEquiv d).symm
      (AlgHom.tensorEqualizerEquiv A A (d.coaction.restrictScalars R) includeRight (a ⊗ₜ[R] c)) = _
  apply (AffineDescentData.coactionEquiv d).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.val_apply]
  change a ⊗ₜ[R] c.val = d.coaction (algebraMap A B a * c.val)
  rw [map_mul, AlgHom.commutes]
  have hc : d.coaction c.val = (1 : A) ⊗ₜ[R] c.val := c.property
  rw [hc]
  change _ = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] c.val)
  rw [tmul_mul_tmul, mul_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Affine descent is obtained by taking the spectrum of the fixed algebra. -/
theorem ParameterDescent.affineEffectivity [Module.Flat R A]
    (d : ParameterDescent (coordBase R A B)) :
    ∃ (W : Over (ringSpec R)) (_ : IsAffine W.left) (r : coordSpec R B ⟶ W),
      IsPullback (coordBase R A B).left r.left (algebraSpecMap R A) W.hom ∧
        d.transport ≫ r = fst (coordSpec R B) (coordSpec R A) ≫ r := by
  obtain ⟨e, he⟩ := d.exists_coaction
  let W := coordSpec R e.fixedAlgebra
  let v := coordBase R A B
  let r : coordSpec R B ⟶ W := coordSpecMap e.fixedAlgebra.val
  let j := Spec.map (CommRingCat.ofHom (e.baseChangeIso.toRingEquiv :
    (A ⊗[R] e.fixedAlgebra) ≃+* B).toRingHom)
  let i := (Scheme.Spec.mapIso (e.baseChangeIso.toRingEquiv.toCommRingCatIso.op))
  have hi : i.hom = j := rfl
  let k := i ≪≫ (pullbackSpecIso R A e.fixedAlgebra).symm
  refine ⟨W, inferInstanceAs (IsAffine (ringSpec e.fixedAlgebra)), r, ?_, ?_⟩
  · apply IsPullback.of_iso_pullback ⟨(CategoryTheory.Over.w v).trans (CategoryTheory.Over.w r).symm⟩ k
    · change (j ≫ (pullbackSpecIso R A e.fixedAlgebra).inv) ≫ pullback.fst _ _ = _
      rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext a
      change e.baseChangeIso (a ⊗ₜ[R] (1 : e.fixedAlgebra)) = algebraMap A B a
      rw [affineDescentIso_tmul]; simp
    · change (j ≫ (pullbackSpecIso R A e.fixedAlgebra).inv) ≫ pullback.snd _ _ = _
      rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext x
      change e.baseChangeIso ((1 : A) ⊗ₜ[R] x) = x.val
      rw [affineDescentIso_tmul]; simp
  · let w := (coordProductIso R A B).hom
    let i : coordSpec R (A ⊗[R] B) ⟶ coordSpec R B ⊗ coordSpec R A :=
      w ≫ lift (snd _ _) (fst _ _)
    have : IsIso (lift (snd (coordSpec R A) (coordSpec R B)) (fst _ _)) :=
      inferInstanceAs (IsIso ((β_ (coordSpec R A) (coordSpec R B)).hom))
    have : Epi i := inferInstanceAs (Epi (w ≫ lift (snd _ _) (fst _ _)))
    apply (cancel_epi i).mp
    rw [← Category.assoc, ← Category.assoc]
    have h₁ : i ≫ d.transport = coordSpecMap (e.coaction.restrictScalars R) := he.symm
    have h₂ : i ≫ fst _ _ = coordSpecMap (includeRight : B →ₐ[R] A ⊗[R] B) := by
      change (w ≫ lift (snd _ _) (fst _ _)) ≫ fst _ _ = _
      rw [Category.assoc, lift_fst]
      exact coordProductIso_snd
    rw [h₁, h₂]
    change coordSpecMap _ ≫ coordSpecMap _ = coordSpecMap _ ≫ coordSpecMap _
    rw [← coordSpecMap_comp, ← coordSpecMap_comp]
    congr 1
    exact AlgHom.ext fun x ↦ x.property

end AlgebraDescent

end AffineParameterDescent

variable {S : Scheme.{u}} {A V : Over S} {v : V ⟶ A}

/-- An effective datum identifies the transported points over the descended
scheme by a cartesian square. -/
def ParameterDescent.IsEffective (d : ParameterDescent v) : Prop :=
  ∃ (W : Over S) (r : V ⟶ W), IsPullback v.left r.left A.hom W.hom ∧
    d.transport ≫ r = fst V A ≫ r

namespace ParameterDescent

variable (d : ParameterDescent v) {W : Over S} {r : V ⟶ W}

@[reassoc]
theorem change_comp_projection (h : d.transport ≫ r = fst V A ≫ r)
    {T : Over S} (x : T ⟶ V) (b : T ⟶ A) :
    d.change x b ≫ r = x ≫ r := by
  unfold change
  rw [Category.assoc, h, ← Category.assoc, lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-- Effective descent identifies two points in the same fibre by transport
along the second point's base map. -/
theorem change_eq_of_projection_eq (hr : IsPullback v.left r.left A.hom W.hom)
    (h : d.transport ≫ r = fst V A ≫ r)
    {T : Over S} (x y : T ⟶ V) (e : x ≫ r = y ≫ r) :
    d.change x (y ≫ v) = y := by
  apply Over.OverMorphism.ext
  apply hr.hom_ext
  · exact congrArg Over.Hom.left (d.change_over x (y ≫ v))
  · exact congrArg Over.Hom.left ((d.change_comp_projection h x (y ≫ v)).trans e)

end ParameterDescent

section PresentationAssembly

variable {S' : Scheme.{u}} {G : Grp (Over S)} {P : Over S'}
variable [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical transport of the Borel family supplies the compatibility on
an effective descent of its parameter scheme. -/
theorem borelClassificationOfEffectiveDescent
    (a : S' ⟶ S) [Surjective a] [Flat a] [IsFinite a]
    (B : Family ((changeBase a).obj G) P) (hP : Smooth P.hom) (hB : IsBorelFamily B)
    (hrep : ∀ (T : Over S') (C : Family ((changeBase a).obj G) T), IsBorelFamily C →
      ∃! x : T ⟶ P, SameFamily (B.pullback x) C)
    (d : ParameterDescent (Over.homMk P.hom : (Over.map a).obj P ⟶ Over.mk a))
    (hd : ∀ {T : Over S} (x : T ⟶ (Over.map a).obj P) (b : T ⟶ Over.mk a),
      SameFamily ((absoluteFamily a B).pullback (d.change x b)) ((absoluteFamily a B).pullback x))
    (heff : d.IsEffective) :
    ∃ (W : Over S) (U : Family G W), Smooth W.hom ∧ IsBorelFamily U ∧
      ∀ (T : Over S) (C : Family G T), IsBorelFamily C →
        ∃! x : T ⟶ W, SameFamily (U.pullback x) C := by
  obtain ⟨W, r, hr, h⟩ := heff
  have hv : IsPullback r.left P.hom W.hom a := hr.flip
  have hne : d.change (pullback.fst r r) (pullback.snd r r ≫ Over.homMk P.hom) =
      pullback.snd r r := d.change_eq_of_projection_eq hr h _ _ pullback.condition
  have hd' := hd (pullback.fst r r) (pullback.snd r r ≫ Over.homMk P.hom)
  rw [hne] at hd'
  obtain ⟨hs, U, hU, hu⟩ :=
    borelClassificationOfDescendedParameter a r hv hP B hB hrep (sameFamily_symm hd')
  exact ⟨W, U, hs, hU, hu⟩

end PresentationAssembly

section Restriction

variable {S : Scheme.{u}} {A V : Over S} {v : V ⟶ A}

namespace ParameterDescent

variable (d : ParameterDescent v)

private theorem change_over_iso {V' : Over S} (e : V' ≅ V) {T : Over S}
    (x : T ⟶ V') (b : T ⟶ A) :
    lift x b ≫ (d.change (fst V' A ≫ e.hom) (snd V' A) ≫ e.inv) =
      d.change (x ≫ e.hom) b ≫ e.inv := by
  rw [← Category.assoc, comp_change, lift_fst_assoc, lift_snd]

private def restrictIso {V' : Over S} (e : V' ≅ V) : ParameterDescent (e.hom ≫ v) where
  transport := d.change (fst V' A ≫ e.hom) (snd V' A) ≫ e.inv
  base := by simp only [Category.assoc, Iso.inv_hom_id_assoc, change_over]
  identity := by rw [change_over_iso, Category.id_comp, change_identity, Iso.hom_inv_id]
  composition := by
    intro T x b c
    simp only [change_over_iso, Category.assoc, Iso.inv_hom_id, Category.comp_id, change_change]

private theorem transport_cast {v w : V ⟶ A} (hv : v = w) (d : ParameterDescent v) :
    (hv ▸ d : ParameterDescent w).transport = d.transport := by
  cases hv
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Affine effectivity in a presentation by an arbitrary affine scheme. -/
theorem affineEffectivityOfIsAffine {R C : Type u} [CommRing R] [CommRing C]
    [Algebra R C] [Module.Flat R C]
    {V : Over (ringSpec R)} (v : V ⟶ coordSpec R C) [IsAffine V.left]
    (d : ParameterDescent v) :
    ∃ (W : Over (ringSpec R)) (r : V ⟶ W), IsAffine W.left ∧
      IsPullback v.left r.left (algebraSpecMap R C) W.hom ∧
      d.transport ≫ r = fst V (coordSpec R C) ≫ r := by
  let V' := Over.mk v.left
  obtain ⟨B, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of C)).mpr
    (inferInstanceAs (IsAffine V.left) : IsAffine V'.left)
  let : Algebra R B.unop := ((algebraMap C B.unop).comp (algebraMap R C)).toAlgebra
  let : IsScalarTower R C B.unop := IsScalarTower.of_algebraMap_eq' rfl
  let t := (restrictSpecIso (R := R) B.unop) ≪≫ (Over.map (algebraSpecMap R C)).mapIso e₀
  let e : coordSpec R B.unop ≅ V := t ≪≫ Over.isoMk (Iso.refl _) (CategoryTheory.Over.w v).symm
  have hb : e.hom ≫ v = coordBase R C B.unop := by
    apply Over.OverMorphism.ext
    change ((𝟙 _ ≫ e₀.hom.left) ≫ 𝟙 _) ≫ v.left = algebraSpecMap C B.unop
    rw [Category.id_comp, Category.comp_id]
    exact CategoryTheory.Over.w e₀.hom
  let hd : ParameterDescent (coordBase R C B.unop) := hb ▸ d.restrictIso e
  have hτ : hd.transport = (d.restrictIso e).transport := transport_cast hb _
  obtain ⟨W, hW, r', hr', heff⟩ := hd.affineEffectivity
  let r := e.inv ≫ r'
  have hhr : IsPullback (e.hom ≫ v).left r'.left (algebraSpecMap R C) W.hom := hb ▸ hr'
  refine ⟨W, r, hW, ?_, ?_⟩
  · refine hhr.of_iso' ((Over.forget (ringSpec R)).mapIso e.symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
      change e.inv.left ≫ (e.hom ≫ v).left = v.left
      exact congrArg Over.Hom.left (by simp : e.inv ≫ e.hom ≫ v = v)
    · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
      rfl
  · let i : coordSpec R B.unop ⊗ coordSpec R C ⟶ V ⊗ coordSpec R C :=
      (e ⊗ᵢ Iso.refl _).hom
    have hi : i = lift (fst _ _ ≫ e.hom) (snd _ _) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [i, tensorIso_hom, tensorHom_fst, lift_fst]
      · simp only [i, tensorIso_hom, tensorHom_snd, lift_snd, Iso.refl_hom, Category.comp_id]
    rw [hτ] at heff
    apply (cancel_epi i).mp
    calc
      i ≫ d.transport ≫ r = (d.restrictIso e).transport ≫ r' := by
        change i ≫ d.transport ≫ e.inv ≫ r' =
          (d.change (fst _ _ ≫ e.hom) (snd _ _) ≫ e.inv) ≫ r'
        rw [hi, change, Category.assoc, Category.assoc]
      _ = fst _ _ ≫ r' := heff
      _ = i ≫ fst _ _ ≫ r := by
        rw [hi, ← Category.assoc, lift_fst]
        change fst _ _ ≫ r' = (fst _ _ ≫ e.hom) ≫ e.inv ≫ r'
        simp only [Category.assoc, Iso.hom_inv_id_assoc]

end ParameterDescent
end Restriction

variable {S : Scheme.{u}} {A V : Over S} {v : V ⟶ A}

namespace ParameterDescent

variable (d : ParameterDescent v)

/-- An open is invariant when the transport and the first projection have the
same inverse image of it. -/
def Invariant (U : V.left.Opens) : Prop :=
  ∀ z : (V ⊗ A).left, d.transport.left z ∈ U ↔ (fst V A).left z ∈ U

private abbrev openOver (U : V.left.Opens) : Over S := Over.mk (U.ι ≫ V.hom)

private def openInclusion (U : V.left.Opens) : openOver U ⟶ V := Over.homMk U.ι

private instance (U : V.left.Opens) : IsOpenImmersion (openInclusion U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

private instance (U : V.left.Opens) : Mono (openInclusion U) := Over.mono_of_mono_left _

private def openHom {U U' : V.left.Opens} (e : U ≤ U') : openOver U ⟶ openOver U' :=
  Over.homMk (V.left.homOfLE e) (by
    change V.left.homOfLE e ≫ U'.ι ≫ V.hom = U.ι ≫ V.hom
    rw [Scheme.homOfLE_ι_assoc])

@[reassoc (attr := simp)]
private theorem openHom_inclusion {U U' : V.left.Opens} (e : U ≤ U') :
    openHom e ≫ openInclusion U' = openInclusion U :=
  Over.OverMorphism.ext (V.left.homOfLE_ι e)

private def openProduct (U : V.left.Opens) : openOver U ⊗ A ⟶ V ⊗ A :=
  lift (fst _ _ ≫ openInclusion U) (snd _ _)

private theorem openProduct_range (U : V.left.Opens) (hU : d.Invariant U) :
    Set.range ((openProduct (A := A) U) ≫ d.transport).left ⊆ Set.range U.ι := by
  rintro _ ⟨z, rfl⟩
  change (d.transport.left ((openProduct (A := A) U).left z)) ∈ Set.range U.ι
  rw [Scheme.Opens.range_ι]
  apply (hU _).mpr
  have h : openProduct (A := A) U ≫ fst V A = fst _ _ ≫ openInclusion U := lift_fst _ _
  have e := congrArg (fun f : openOver U ⊗ A ⟶ V ↦ f.left z) h
  change (fst V A).left ((openProduct (A := A) U).left z) = U.ι ((fst (openOver U) A).left z) at e
  rw [e]
  exact Subtype.property _

set_option backward.isDefEq.respectTransparency false in
private def openTransport (U : V.left.Opens) (hU : d.Invariant U) : openOver U ⊗ A ⟶ openOver U := by
  let m : openOver U ⊗ A ⟶ V := openProduct U ≫ d.transport
  let g : (openOver U ⊗ A).left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι m.left (d.openProduct_range U hU)
  have hg : g ≫ U.ι = m.left := IsOpenImmersion.lift_fac _ _ _
  refine Over.homMk g ?_
  change g ≫ U.ι ≫ V.hom = (openOver U ⊗ A).hom
  rw [← Category.assoc, hg, CategoryTheory.Over.w m]

@[reassoc]
private theorem openTransport_inclusion (U : V.left.Opens) (hU : d.Invariant U) :
    d.openTransport U hU ≫ openInclusion U = openProduct (A := A) U ≫ d.transport :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

private theorem openTransport_eval (U : V.left.Opens) (hU : d.Invariant U)
    {T : Over S} (x : T ⟶ openOver U) (b : T ⟶ A) :
    (lift x b ≫ d.openTransport U hU) ≫ openInclusion U = d.change (x ≫ openInclusion U) b := by
  rw [Category.assoc, openTransport_inclusion, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [openProduct, Category.assoc, lift_fst]
    rw [lift_fst_assoc]
  · simp only [openProduct, Category.assoc, lift_snd]

/-- Transport restricts to the invariant open subscheme with its inherited
map to the covering base. -/
private def restrictOpen (U : V.left.Opens) (hU : d.Invariant U) :
    ParameterDescent (openInclusion U ≫ v) where
  transport := d.openTransport U hU
  base := by
    rw [← Category.assoc, openTransport_inclusion, Category.assoc, d.base]
    exact lift_snd _ _
  identity := by
    apply (cancel_mono (openInclusion U)).mp
    rw [openTransport_eval, Category.id_comp, change_identity]
  composition := by
    intro T x b c
    apply (cancel_mono (openInclusion U)).mp
    rw [openTransport_eval, openTransport_eval, openTransport_eval, change_change]

private theorem restrictOpen_change (U : V.left.Opens) (hU : d.Invariant U)
    {T : Over S} (x : T ⟶ openOver U) (b : T ⟶ A) :
    (d.restrictOpen U hU).change x b ≫ openInclusion U = d.change (x ≫ openInclusion U) b :=
  d.openTransport_eval U hU x b

private theorem invariant_inf {U U' : V.left.Opens} (hU : d.Invariant U) (hU' : d.Invariant U') :
    d.Invariant (U ⊓ U') := fun z ↦ and_congr (hU z) (hU' z)

private abbrev AffineOpen := {U : V.left.Opens // d.Invariant U ∧ IsAffineOpen U}

private structure OpenChart (U : d.AffineOpen) where
  scheme : Over S
  projection : openOver U.val ⟶ scheme
  cartesian : IsPullback (openInclusion U.val ≫ v).left projection.left A.hom scheme.hom
  invariant : (d.restrictOpen U.val U.property.1).transport ≫ projection =
    fst (openOver U.val) A ≫ projection

section Charts

variable {d}
variable [Flat A.hom] [Surjective A.hom] [QuasiCompact A.hom]

private instance chartFlat {U : d.AffineOpen} (C : d.OpenChart U) : Flat C.projection.left :=
  MorphismProperty.of_isPullback C.cartesian ‹Flat A.hom›

private instance chartSurjective {U : d.AffineOpen} (C : d.OpenChart U) : Surjective C.projection.left :=
  MorphismProperty.of_isPullback C.cartesian ‹Surjective A.hom›

private instance chartQuasiCompact {U : d.AffineOpen} (C : d.OpenChart U) : QuasiCompact C.projection.left :=
  MorphismProperty.of_isPullback C.cartesian ‹QuasiCompact A.hom›

private instance chartEpi {U : d.AffineOpen} (C : d.OpenChart U) : Epi C.projection :=
  Over.epi_of_epi_left _

set_option backward.isDefEq.respectTransparency false in
private theorem openChartHom_exists {U W : d.AffineOpen} (h : U ≤ W)
    (C : d.OpenChart U) (D : d.OpenChart W) :
    ∃ f : C.scheme ⟶ D.scheme, C.projection ≫ f = openHom h ≫ D.projection := by
  apply existsOverDesc
  intro T x y e
  let dU := d.restrictOpen U.val U.property.1
  let dW := d.restrictOpen W.val W.property.1
  have hy := dU.change_eq_of_projection_eq C.cartesian C.invariant x y e
  have hcmp : dW.change (x ≫ openHom h) (y ≫ (openInclusion U.val ≫ v)) = y ≫ openHom h := by
    apply (cancel_mono (openInclusion W.val)).mp
    have hx := d.restrictOpen_change U.val U.property.1 x (y ≫ (openInclusion U.val ≫ v))
    have hz := d.restrictOpen_change W.val W.property.1 (x ≫ openHom h)
      (y ≫ (openInclusion U.val ≫ v))
    change dW.change (x ≫ openHom h) _ ≫ openInclusion W.val = _
    rw [hz, Category.assoc, openHom_inclusion, ← hx, hy, Category.assoc, openHom_inclusion]
  rw [← Category.assoc, ← Category.assoc, ← hcmp, dW.change_comp_projection D.invariant]

private def openChartHom {U W : d.AffineOpen} (h : U ≤ W)
    (C : d.OpenChart U) (D : d.OpenChart W) : C.scheme ⟶ D.scheme :=
  (openChartHom_exists h C D).choose

@[reassoc]
private theorem openChartHom_comp {U W : d.AffineOpen} (h : U ≤ W)
    (C : d.OpenChart U) (D : d.OpenChart W) :
    C.projection ≫ openChartHom h C D = openHom h ≫ D.projection :=
  (openChartHom_exists h C D).choose_spec

set_option backward.isDefEq.respectTransparency false in
private theorem openChart_square {U W : d.AffineOpen} (h : U ≤ W)
    (C : d.OpenChart U) (D : d.OpenChart W) :
    IsPullback (openHom h).left C.projection.left D.projection.left (openChartHom h C D).left := by
  have htop : (openHom h).left ≫ (openInclusion W.val ≫ v).left = (openInclusion U.val ≫ v).left :=
    congrArg Over.Hom.left (openHom_inclusion_assoc h v)
  have hbottom : (openChartHom h C D).left ≫ D.scheme.hom = C.scheme.hom := CategoryTheory.Over.w _
  apply IsPullback.of_right (h₁₂ := (openInclusion W.val ≫ v).left) (h₂₂ := D.scheme.hom) (v₁₃ := A.hom)
  · rw [htop, hbottom]
    exact C.cartesian
  · exact (congrArg Over.Hom.left (openChartHom_comp h C D)).symm
  · exact D.cartesian

private instance openChartHom_open {U W : d.AffineOpen} (h : U ≤ W)
    (C : d.OpenChart U) (D : d.OpenChart W) : IsOpenImmersion (openChartHom h C D).left := by
  apply MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (openChart_square h C D)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · change IsOpenImmersion (V.left.homOfLE (show U.val ≤ W.val from h))
    have : IsOpenImmersion (V.left.homOfLE (show U.val ≤ W.val from h) ≫ W.val.ι) := by
      rw [Scheme.homOfLE_ι]
      infer_instance
    exact IsOpenImmersion.of_comp _ W.val.ι

end Charts

set_option backward.isDefEq.respectTransparency false in
private theorem openChart_exists {R C : Type u} [CommRing R] [CommRing C] [Algebra R C] [Module.Flat R C]
    {V : Over (ringSpec R)} {v : V ⟶ coordSpec R C} (d : ParameterDescent v)
    (U : d.AffineOpen) : Nonempty (d.OpenChart U) := by
  let v' := openInclusion U.val ≫ v
  have : IsAffine (openOver U.val).left := U.property.2
  obtain ⟨W, r, _, hr, hτ⟩ := (d.restrictOpen U.val U.property.1).affineEffectivityOfIsAffine v'
  exact ⟨⟨W, r, hr, hτ⟩⟩

end ParameterDescent

section GlueParameter

open TopologicalSpace.Opens

namespace ParameterDescent

variable {S : Scheme.{u}} {A V : Over S} {v : V ⟶ A} {d : ParameterDescent v}
variable [Flat A.hom] [Surjective A.hom] [QuasiCompact A.hom]

private abbrev intersection [V.left.IsSeparated] (U W : (AffineOpen d)) : (AffineOpen d) :=
  ⟨U.val ⊓ W.val, invariant_inf d U.property.1 W.property.1, U.property.2.inf W.property.2⟩

variable (C : ∀ U : (AffineOpen d), OpenChart d U)

set_option backward.isDefEq.respectTransparency false in
private def chartDiagram : (AffineOpen d) ⥤ Scheme.{u} where
  obj U := (C U).scheme.left
  map {U W} f := (openChartHom (leOfHom f) (C U) (C W)).left
  map_id U := by
    suffices e : openChartHom (le_refl U) (C U) (C U) = 𝟙 (C U).scheme from
      congrArg Over.Hom.left e
    apply (cancel_epi (C U).projection).mp
    rw [openChartHom_comp, Category.comp_id]
    have h : openHom (U := U.val) le_rfl = 𝟙 (openOver U.val) :=
      Over.OverMorphism.ext (Scheme.homOfLE_rfl V.left U.val)
    rw [h, Category.id_comp]
  map_comp {U W Z} f g := by
    suffices e : openChartHom (leOfHom (f ≫ g)) (C U) (C Z) =
        openChartHom (leOfHom f) (C U) (C W) ≫ openChartHom (leOfHom g) (C W) (C Z) from
      congrArg Over.Hom.left e
    apply (cancel_epi (C U).projection).mp
    rw [openChartHom_comp, openChartHom_comp_assoc, openChartHom_comp]
    rw [← Category.assoc (openHom _) (openHom _) (C Z).projection]
    congr 1
    apply Over.OverMorphism.ext
    exact (Scheme.homOfLE_homOfLE V.left (show U.val ≤ W.val from leOfHom f)
      (show W.val ≤ Z.val from leOfHom g)).symm

private instance chartDiagram_open {U W : (AffineOpen d)} (f : U ⟶ W) :
    IsOpenImmersion ((chartDiagram C).map f) :=
  inferInstanceAs (IsOpenImmersion (openChartHom (leOfHom f) (C U) (C W)).left)

private theorem chartDiagram_base {U W : (AffineOpen d)} (f : U ⟶ W) :
    (chartDiagram C).map f ≫ (C W).scheme.hom = (C U).scheme.hom :=
  CategoryTheory.Over.w (openChartHom (leOfHom f) (C U) (C W))

set_option backward.isDefEq.respectTransparency false in
private instance chartDiagram_locallyDirected [V.left.IsSeparated] :
    (chartDiagram C ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj he := by
    obtain ⟨w, hw⟩ := (C k).projection.left.surjective ((chartDiagram C).map fi xi)
    have hw' : (C k).projection.left w = (chartDiagram C).map fj xj := hw.trans he
    obtain ⟨u, hu, hux⟩ := Scheme.exists_preimage_of_isPullback
      (openChart_square (leOfHom fi) (C i) (C k)) w xi hw
    obtain ⟨z, hz, hzx⟩ := Scheme.exists_preimage_of_isPullback
      (openChart_square (leOfHom fj) (C j) (C k)) w xj hw'
    change i.val.toScheme at u
    change j.val.toScheme at z
    change k.val.toScheme at w
    have eq : u.val = z.val := by
      have h₁ := congrArg (openInclusion k.val).left hu
      have h₂ := congrArg (openInclusion k.val).left hz
      change (V.left.homOfLE (show i.val ≤ k.val from leOfHom fi) u : k.val.toScheme).val = w.val at h₁
      change (V.left.homOfLE (show j.val ≤ k.val from leOfHom fj) z : k.val.toScheme).val = w.val at h₂
      rw [Scheme.homOfLE_apply] at h₁ h₂
      exact h₁.trans h₂.symm
    let l := intersection i j
    let v₀ : (openOver l.val).left := ⟨u.val, u.property, eq.symm ▸ z.property⟩
    refine ⟨l, homOfLE (show l ≤ i from show l.val ≤ i.val from inf_le_left), homOfLE (show l ≤ j from show l.val ≤ j.val from inf_le_right),
      (C l).projection.left v₀, ?_, ?_⟩
    · change (openChartHom (show l ≤ i from show l.val ≤ i.val from inf_le_left) (C l) (C i)).left ((C l).projection.left v₀) = xi
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, openChartHom_comp, Over.comp_left,
        Scheme.Hom.comp_apply]
      have e : (openHom (show l.val ≤ i.val from inf_le_left)).left v₀ = u := by
        apply Subtype.ext
        change (V.left.homOfLE inf_le_left v₀).val = u.val
        rw [Scheme.homOfLE_apply]
      rw [e]
      exact hux
    · change (openChartHom (show l ≤ j from show l.val ≤ j.val from inf_le_right) (C l) (C j)).left ((C l).projection.left v₀) = xj
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, openChartHom_comp, Over.comp_left,
        Scheme.Hom.comp_apply]
      have e : (openHom (show l.val ≤ j.val from inf_le_right)).left v₀ = z := by
        apply Subtype.ext
        change (V.left.homOfLE inf_le_right v₀).val = z.val
        rw [Scheme.homOfLE_apply]
        exact eq
      rw [e]
      exact hzx

variable [V.left.IsSeparated]

private def gluedScheme : Over S := Over.mk (colimit.desc (chartDiagram C)
  ⟨S, ⟨fun i ↦ (C i).scheme.hom, fun _ _ f ↦ chartDiagram_base C f⟩⟩)

private def gluedChart (i : (AffineOpen d)) : (C i).scheme ⟶ gluedScheme C :=
  Over.homMk (colimit.ι (chartDiagram C) i) (colimit.ι_desc _ _)

private instance gluedChart_open (i : (AffineOpen d)) : IsOpenImmersion (gluedChart C i).left :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (chartDiagram C) i))

private theorem gluedChart_comp {i j : (AffineOpen d)} (h : i ≤ j) :
    openChartHom h (C i) (C j) ≫ gluedChart C j = gluedChart C i :=
  Over.OverMorphism.ext (colimit.w (chartDiagram C) (homOfLE h))

variable (hcov : ∀ x : V.left, ∃ U : (AffineOpen d), x ∈ U.val)

private def invariantOpenCover : V.left.OpenCover :=
  V.left.openCoverOfIsOpenCover (fun U : (AffineOpen d) ↦ U.val) (by
    change iSup (fun U : AffineOpen d ↦ U.val) = ⊤
    rw [eq_top_iff]
    intro x _
    obtain ⟨U, hx⟩ := hcov x
    exact mem_iSup.mpr ⟨U, hx⟩)

set_option backward.isDefEq.respectTransparency false in
private theorem gluedProjections_agree (i j : (AffineOpen d)) :
    pullback.fst i.val.ι j.val.ι ≫ ((C i).projection ≫ gluedChart C i).left =
      pullback.snd i.val.ι j.val.ι ≫ ((C j).projection ≫ gluedChart C j).left := by
  let k := intersection i j
  let fi : openOver k.val ⟶ openOver i.val := openHom inf_le_left
  let fj : openOver k.val ⟶ openOver j.val := openHom inf_le_right
  have : IsOpenImmersion fj.left := by
    have : IsOpenImmersion (fj.left ≫ j.val.ι) := by
      change IsOpenImmersion (V.left.homOfLE inf_le_right ≫ j.val.ι)
      rw [Scheme.homOfLE_ι]
      exact inferInstanceAs (IsOpenImmersion k.val.ι)
    exact IsOpenImmersion.of_comp _ j.val.ι
  have h : IsPullback fi.left fj.left i.val.ι j.val.ι :=
    IsOpenImmersion.isPullback _ _ _ _ (by
      change V.left.homOfLE inf_le_right ≫ j.val.ι = V.left.homOfLE inf_le_left ≫ i.val.ι
      rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]) (by
      change j.val.ι ⁻¹ᵁ i.val.ι.opensRange = (V.left.homOfLE inf_le_right).opensRange
      rw [Scheme.Opens.opensRange_ι, Scheme.opensRange_homOfLE]
      ext x
      change x.val ∈ i.val ↔ x.val ∈ i.val ⊓ j.val
      exact ⟨fun h ↦ ⟨h, x.property⟩, And.left⟩)
  apply (cancel_epi h.isoPullback.hom).mp
  rw [← Category.assoc, ← Category.assoc, h.isoPullback_hom_fst, h.isoPullback_hom_snd]
  rw [← Over.comp_left, ← Over.comp_left]
  apply congrArg Over.Hom.left
  rw [show fi = openHom (show k ≤ i from show k.val ≤ i.val from inf_le_left) from rfl,
    show fj = openHom (show k ≤ j from show k.val ≤ j.val from inf_le_right) from rfl,
    ← openChartHom_comp_assoc, ← openChartHom_comp_assoc, gluedChart_comp, gluedChart_comp]

include hcov in
private def gluedProjection : V ⟶ gluedScheme C := by
  let 𝒰 := invariantOpenCover (d := d) hcov
  let r := 𝒰.glueMorphisms (fun i ↦ ((C i).projection ≫ gluedChart C i).left)
    (gluedProjections_agree C)
  refine Over.homMk r (𝒰.hom_ext _ _ fun i ↦ ?_)
  have e : 𝒰.f i ≫ r = ((C i).projection ≫ gluedChart C i).left := 𝒰.ι_glueMorphisms _ _ i
  rw [← Category.assoc, e]
  exact (CategoryTheory.Over.w _).trans (CategoryTheory.Over.w (openInclusion i.val)).symm

@[reassoc]
private theorem openInclusion_gluedProjection (i : (AffineOpen d)) :
    openInclusion i.val ≫ gluedProjection C hcov = (C i).projection ≫ gluedChart C i :=
  Over.OverMorphism.ext (show (invariantOpenCover hcov).f i ≫
    (invariantOpenCover hcov).glueMorphisms _ (gluedProjections_agree C) = _ from
      (invariantOpenCover hcov).ι_glueMorphisms _ _ i)

set_option backward.isDefEq.respectTransparency false in
private theorem gluedChart_preimage (i : AffineOpen d) :
    (gluedProjection C hcov).left ⁻¹ᵁ (gluedChart C i).left.opensRange = i.val := by
  ext x
  change (gluedProjection C hcov).left x ∈ Set.range (gluedChart C i).left ↔ x ∈ i.val
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨j, hx⟩ := hcov x
    let y : (openOver j.val).left := ⟨x, hx⟩
    have h₁ : (gluedChart C j).left ((C j).projection.left y) = (gluedProjection C hcov).left x :=
      (congrArg (fun f : openOver j.val ⟶ gluedScheme C ↦ f.left y)
        (openInclusion_gluedProjection C hcov j)).symm
    have h₂ : colimit.ι (chartDiagram C) j ((C j).projection.left y) =
        colimit.ι (chartDiagram C) i z := h₁.trans hz.symm
    obtain ⟨k, kj, ki, w, hw, _⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (chartDiagram C)).mp h₂
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
      (openChart_square (leOfHom kj) (C k) (C j)) y w hw.symm
    have ex : t.val = x := by
      have he := congrArg (fun u : (openOver j.val).left ↦ u.val) ht
      change (V.left.homOfLE (leOfHom kj) t).val = x at he
      rw [Scheme.homOfLE_apply] at he
      exact he
    exact ex ▸ (show k.val ≤ i.val from leOfHom ki) t.property
  · intro hx
    let y : (openOver i.val).left := ⟨x, hx⟩
    refine ⟨(C i).projection.left y, ?_⟩
    exact (congrArg (fun f : openOver i.val ⟶ gluedScheme C ↦ f.left y)
      (openInclusion_gluedProjection C hcov i)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem gluedProjection_isPullback_chart (i : AffineOpen d) :
    IsPullback (C i).projection.left (openInclusion i.val).left
      (gluedChart C i).left (gluedProjection C hcov).left := by
  apply IsOpenImmersion.isPullback
  · exact congrArg Over.Hom.left (openInclusion_gluedProjection C hcov i)
  · rw [gluedChart_preimage]
    exact Scheme.Opens.opensRange_ι i.val |>.symm

omit [Flat A.hom] [Surjective A.hom] [QuasiCompact A.hom] in
private theorem productChartPullback {D W : Over S} (c : D ⟶ W) :
    IsPullback (fst D A) (lift (fst D A ≫ c) (snd D A)) c (fst W A) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · exact (lift_fst _ _).symm
  · intro T x y h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · exact h₁
    · simpa only [Category.assoc, lift_snd] using congrArg (· ≫ snd W A) h₂
  · intro T x y he
    refine ⟨lift x (y ≫ snd W A), lift_fst _ _, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst_assoc]
      exact he
    · simp only [Category.assoc, lift_snd]

set_option backward.isDefEq.respectTransparency false in
private theorem gluedProjection_cartesian :
    IsPullback v.left (gluedProjection C hcov).left A.hom (gluedScheme C).hom := by
  let W := gluedScheme C
  let r := gluedProjection C hcov
  let Z := W ⊗ A
  let f : V ⟶ Z := lift r v
  let b (i : AffineOpen d) := lift (fst (C i).scheme A ≫ gluedChart C i) (snd (C i).scheme A)
  have hb (i : AffineOpen d) : IsPullback (fst (C i).scheme A).left (b i).left
      (gluedChart C i).left (fst W A).left := (productChartPullback (gluedChart C i)).map (Over.forget S)
  have hbo (i : AffineOpen d) : IsOpenImmersion (b i).left :=
    MorphismProperty.of_isPullback (hb i) inferInstance
  let OC : Z.left.OpenCover := {
    I₀ := AffineOpen d
    X := fun i ↦ ((C i).scheme ⊗ A).left
    f := fun i ↦ (b i).left
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun z ↦ ?_, hbo⟩
      obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (chartDiagram C) ((fst W A).left z)
      obtain ⟨x, _, hx⟩ := Scheme.exists_preimage_of_isPullback (hb i) y z hy
      exact ⟨i, x, hx⟩ }
  have hf : IsIso f.left := by
    apply (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{u}) OC).mpr
    intro i
    let D := (C i).scheme
    let vᵢ := openInclusion i.val ≫ v
    let k := lift (C i).projection vᵢ
    have hk₁ : k.left ≫ (fst D A).left = (C i).projection.left := congrArg Over.Hom.left (lift_fst _ _)
    have hk₂ : k.left ≫ (snd D A).left = vᵢ.left := congrArg Over.Hom.left (lift_snd _ _)
    have hki : IsIso k.left := by
      have e : k.left = (C i).cartesian.flip.isoPullback.hom := by
        apply pullback.hom_ext
        · exact hk₁.trans (C i).cartesian.flip.isoPullback_hom_fst.symm
        · exact hk₂.trans (C i).cartesian.flip.isoPullback_hom_snd.symm
      rw [e]
      infer_instance
    have hsq : k ≫ b i = openInclusion i.val ≫ f := by
      apply CartesianMonoidalCategory.hom_ext
      · change (k ≫ b i) ≫ fst W A = (openInclusion i.val ≫ f) ≫ fst W A
        rw [Category.assoc, Category.assoc, show b i ≫ fst W A = _ from lift_fst _ _,
          show f ≫ fst W A = r from lift_fst _ _, lift_fst_assoc]
        exact (openInclusion_gluedProjection C hcov i).symm
      · change (k ≫ b i) ≫ snd W A = (openInclusion i.val ≫ f) ≫ snd W A
        rw [Category.assoc, Category.assoc, show b i ≫ snd W A = _ from lift_snd _ _,
          show f ≫ snd W A = v from lift_snd _ _, lift_snd]
    have outer : IsPullback (k.left ≫ (fst D A).left) (openInclusion i.val).left
        (gluedChart C i).left (f.left ≫ (fst W A).left) := by
      rw [hk₁, show f.left ≫ (fst W A).left = r.left from congrArg Over.Hom.left (lift_fst _ _)]
      exact gluedProjection_isPullback_chart C hcov i
    have hp : IsPullback k.left (openInclusion i.val).left (b i).left f.left :=
      outer.of_right (congrArg Over.Hom.left hsq) (hb i)
    change IsIso (pullback.snd f.left (b i).left)
    exact (MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms _) hp.flip.isoPullback.hom _).mp
      (hp.flip.isoPullback_hom_snd.symm ▸ hki)
  refine IsPullback.of_iso_pullback ⟨(CategoryTheory.Over.w v).trans (CategoryTheory.Over.w r).symm⟩
    (asIso f.left ≪≫ pullbackSymmetry W.hom A.hom) ?_ ?_
  · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact congrArg Over.Hom.left (lift_snd _ _)
  · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact congrArg Over.Hom.left (lift_fst _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem gluedProjection_invariant :
    d.transport ≫ gluedProjection C hcov = fst V A ≫ gluedProjection C hcov := by
  let r := gluedProjection C hcov
  let O := invariantOpenCover hcov
  let K : (V ⊗ A).left.OpenCover := O.pullback₁ (fst V A).left
  apply Over.OverMorphism.ext
  apply K.hom_ext
  intro i
  change AffineOpen d at i
  let T : Over S := Over.mk (K.f i ≫ (V ⊗ A).hom)
  let k : T ⟶ V ⊗ A := Over.homMk (K.f i)
  let x : T ⟶ openOver i.val := Over.homMk (pullback.snd _ _) (by
    change pullback.snd (fst V A).left i.val.ι ≫ i.val.ι ≫ V.hom = _
    rw [← pullback.condition_assoc]
    change pullback.fst (fst V A).left i.val.ι ≫ (fst V A).left ≫ V.hom =
      pullback.fst (fst V A).left i.val.ι ≫ (V ⊗ A).hom
    rw [CategoryTheory.Over.w (fst V A)])
  let a := k ≫ snd V A
  have hx : x ≫ openInclusion i.val = k ≫ fst V A :=
    Over.OverMorphism.ext pullback.condition.symm
  have hk : k = lift (x ≫ openInclusion i.val) a := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, hx]
    · exact (lift_snd _ _).symm
  have h := restrictOpen_change d i.val i.property.1 x a
  have h₁ : k ≫ d.transport ≫ r = k ≫ fst V A ≫ r := by
    calc
      k ≫ d.transport ≫ r = d.change (x ≫ openInclusion i.val) a ≫ r := by
        rw [← Category.assoc, hk]; rfl
      _ = (restrictOpen d i.val i.property.1).change x a ≫ ((C i).projection ≫ gluedChart C i) := by
        rw [← h, Category.assoc, openInclusion_gluedProjection]
      _ = x ≫ (C i).projection ≫ gluedChart C i := by
        rw [(restrictOpen d i.val i.property.1).change_comp_projection_assoc (C i).invariant]
      _ = k ≫ fst V A ≫ r := by
        rw [← openInclusion_gluedProjection C hcov i, ← Category.assoc, hx, Category.assoc]
  exact congrArg Over.Hom.left h₁

/-- Invariant affine opens give effective descent of the entire separated
parameter scheme by Zariski gluing. -/
theorem effectiveOfInvariantAffineCover {R C' : Type u} [CommRing R] [CommRing C']
    [Algebra R C'] [Module.Flat R C']
    [Surjective (algebraSpecMap R C')] [Flat (algebraSpecMap R C')]
    {V : Over (ringSpec R)} [V.left.IsSeparated] {v : V ⟶ coordSpec R C'}
    (d : ParameterDescent v)
    (hcov : ∀ x : V.left, ∃ U : V.left.Opens, x ∈ U ∧ d.Invariant U ∧ IsAffineOpen U) :
    d.IsEffective := by
  have : Flat (coordSpec R C').hom := inferInstanceAs (Flat (algebraSpecMap R C'))
  have : Surjective (coordSpec R C').hom := inferInstanceAs (Surjective (algebraSpecMap R C'))
  have : QuasiCompact (coordSpec R C').hom := inferInstanceAs (QuasiCompact (algebraSpecMap R C'))
  have hcov' (x : V.left) : ∃ U : AffineOpen d, x ∈ U.val := by
    obtain ⟨U, hx, hd, ha⟩ := hcov x
    exact ⟨⟨U, hd, ha⟩, hx⟩
  let C (U : AffineOpen d) := (openChart_exists d U).some
  exact ⟨gluedScheme C, gluedProjection C hcov', gluedProjection_cartesian C hcov',
    gluedProjection_invariant C hcov'⟩

end ParameterDescent

end GlueParameter

section ParameterTopologicalDescent

namespace ParameterDescent

variable {S : Scheme.{u}} {A V : Over S} {v : V ⟶ A} (d : ParameterDescent v)

/-- Two parameter points are related if they are the two projections of a
point of the overlap with its descent transport. -/
def Related (x y : V.left) : Prop :=
  ∃ z : (V ⊗ A).left, (fst V A).left z = x ∧ d.transport.left z = y

private def reverse : V ⊗ A ⟶ V ⊗ A := lift d.transport (fst V A ≫ v)

private theorem transport_eq_change : d.change (fst V A) (snd V A) = d.transport := by
  change lift (fst V A) (snd V A) ≫ d.transport = d.transport
  rw [lift_fst_snd, Category.id_comp]

@[reassoc]
private theorem reverse_fst : d.reverse ≫ fst V A = d.transport := lift_fst _ _

@[reassoc]
private theorem reverse_snd : d.reverse ≫ snd V A = fst V A ≫ v := lift_snd _ _

@[reassoc]
private theorem reverse_transport : d.reverse ≫ d.transport = fst V A := by
  change d.change d.transport (fst V A ≫ v) = fst V A
  rw [← d.transport_eq_change, d.change_change, d.change_identity]

private instance reverse_iso : IsIso d.reverse := by
  have h : d.reverse ≫ d.reverse = 𝟙 (V ⊗ A) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, reverse_fst, reverse_transport, Category.id_comp]
    · rw [Category.assoc, reverse_snd, reverse_fst_assoc, d.base, Category.id_comp]
  exact ⟨⟨d.reverse, h, h⟩⟩

theorem related_refl (x : V.left) : d.Related x x := by
  let r := lift (𝟙 V) v
  refine ⟨r.left x, ?_, ?_⟩
  · have h : r ≫ fst V A = 𝟙 V := lift_fst _ _
    exact congrArg (fun f : V ⟶ V ↦ f.left x) h
  · exact congrArg (fun f : V ⟶ V ↦ f.left x) d.identity

theorem related_symm {x y : V.left} (h : d.Related x y) : d.Related y x := by
  obtain ⟨z, hz, hw⟩ := h
  exact ⟨d.reverse.left z, (congrArg (fun f : V ⊗ A ⟶ V ↦ f.left z) d.reverse_fst).trans hw,
    (congrArg (fun f : V ⊗ A ⟶ V ↦ f.left z) d.reverse_transport).trans hz⟩

set_option backward.isDefEq.respectTransparency false in
theorem related_trans {x y z : V.left} (h : d.Related x y) (h' : d.Related y z) : d.Related x z := by
  obtain ⟨w, hw, hw'⟩ := h
  obtain ⟨t, ht, ht'⟩ := h'
  let T := pullback d.transport (fst V A)
  let p : T ⟶ V ⊗ A := pullback.fst _ _
  let q : T ⟶ V ⊗ A := pullback.snd _ _
  have hp := (IsPullback.of_hasPullback d.transport (fst V A)).map (Over.forget S)
  obtain ⟨u, hu₁, hu₂⟩ := Scheme.exists_preimage_of_isPullback hp w t (hw'.trans ht.symm)
  let m := lift (p ≫ fst V A) (q ≫ snd V A)
  refine ⟨m.left u, ?_, ?_⟩
  · have hm : m ≫ fst V A = p ≫ fst V A := lift_fst _ _
    have he := congrArg (fun f : T ⟶ V ↦ f.left u) hm
    change _ = (fst V A).left (p.left u) at he
    exact he.trans ((congrArg (fst V A).left hu₁).trans hw)
  · have hm : m ≫ d.transport = q ≫ d.transport := by
      have he : q ≫ fst V A = p ≫ d.transport := pullback.condition.symm
      change d.change (p ≫ fst V A) (q ≫ snd V A) = q ≫ d.transport
      rw [← d.transport_eq_change, d.comp_change, he, ← d.transport_eq_change, d.comp_change,
        d.change_change]
    have he := congrArg (fun f : T ⟶ V ↦ f.left u) hm
    change _ = d.transport.left (q.left u) at he
    exact he.trans ((congrArg d.transport.left hu₂).trans ht')

variable [IsFinite A.hom]

private instance firstProjection_finite : IsFinite (fst V A).left :=
  inferInstanceAs (IsFinite (pullback.fst V.hom A.hom))

private instance transport_finite : IsFinite d.transport.left := by
  have : IsIso d.reverse.left := (Over.forget S).map_isIso d.reverse
  have h := congrArg Over.Hom.left d.reverse_fst
  exact h ▸ inferInstanceAs (IsFinite (d.reverse.left ≫ (fst V A).left))

/-- The largest invariant open contained in a given open is the complement
of the image of its complement under the two overlap projections. -/
def saturation (U : V.left.Opens) : V.left.Opens :=
  ⟨(d.transport.left '' ((fst V A).left ⁻¹' (U : Set V.left)ᶜ))ᶜ,
    ((d.transport.left).isClosedMap _ (U.isOpen.isClosed_compl.preimage (fst V A).left.continuous)).isOpen_compl⟩

theorem mem_saturation (U : V.left.Opens) (x : V.left) :
    x ∈ d.saturation U ↔ ∀ y, d.Related x y → y ∈ U := by
  classical
  change x ∉ d.transport.left '' ((fst V A).left ⁻¹' (U : Set V.left)ᶜ) ↔ _
  constructor
  · intro h y hy
    by_contra hne
    obtain ⟨z, hz, hz'⟩ := d.related_symm hy
    exact h ⟨z, by change (fst V A).left z ∉ U; rwa [hz], hz'⟩
  · intro h hx
    obtain ⟨z, hz, hz'⟩ := hx
    exact hz (h ((fst V A).left z) (d.related_symm ⟨z, rfl, hz'⟩))

theorem saturation_invariant (U : V.left.Opens) : d.Invariant (d.saturation U) := by
  intro z
  rw [mem_saturation, mem_saturation]
  have h : d.Related ((fst V A).left z) (d.transport.left z) := ⟨z, rfl, rfl⟩
  exact ⟨fun H y hy ↦ H y (d.related_trans (d.related_symm h) hy),
    fun H y hy ↦ H y (d.related_trans h hy)⟩

theorem saturation_le (U : V.left.Opens) : d.saturation U ≤ U :=
  fun x hx ↦ (d.mem_saturation U x).mp hx x (d.related_refl x)

theorem finite_related (x : V.left) : {y | d.Related x y}.Finite := by
  have h := (fst V A).left.finite_preimage_singleton x
  refine (h.image d.transport.left).subset ?_
  rintro y ⟨z, hz, hz'⟩
  exact ⟨z, hz, hz'⟩

end ParameterDescent
end ParameterTopologicalDescent

section SplitParameterSaturation

namespace ParameterDescent

variable {S : Scheme.{u}} {A V : Over S} {v : V ⟶ A} (d : ParameterDescent v)
variable [IsFinite A.hom]

private def sectionProduct (s : 𝟙_ (Over S) ⟶ A) : V ⟶ V ⊗ A :=
  lift (𝟙 V) (toUnit V ≫ s)

omit [IsFinite A.hom] in
private theorem sectionProduct_isPullback (s : 𝟙_ (Over S) ⟶ A) :
    IsPullback (sectionProduct (V := V) s) (toUnit V) (snd V A) s := by
  refine IsPullback.mk' (lift_snd _ _) ?_ ?_
  · intro T x y h _
    have e := congrArg (· ≫ fst V A) h
    simpa only [Category.assoc, sectionProduct, lift_fst, Category.comp_id] using e
  · intro T x y h
    refine ⟨x ≫ fst V A, ?_, toUnit_unique _ _⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp only [sectionProduct, Category.assoc, lift_fst, Category.comp_id]
    · simp only [sectionProduct, Category.assoc, lift_snd]
      have e : (x ≫ fst V A) ≫ toUnit V = y := toUnit_unique _ _
      rw [← Category.assoc x, ← Category.assoc, e, ← h]

omit [IsFinite A.hom] in
private theorem sectionProduct_range (s : 𝟙_ (Over S) ⟶ A) :
    Set.range (sectionProduct (V := V) s).left = (snd V A).left ⁻¹' Set.range s.left := by
  have h := (sectionProduct_isPullback (V := V) s).map (Over.forget S)
  have e := Scheme.image_preimage_eq_of_isPullback h.flip Set.univ
  rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at e
  exact e

private theorem isAffinePreimageTransport (s : 𝟙_ (Over S) ⟶ A) [IsClosedImmersion s.left]
    {U : V.left.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen ((sectionProduct (V := V) s ≫ d.transport).left ⁻¹ᵁ U) := by
  have : IsClosedImmersion (sectionProduct (V := V) s).left := MorphismProperty.of_isPullback
    ((sectionProduct_isPullback (V := V) s).map (Over.forget S)).flip ‹IsClosedImmersion s.left›
  have : IsFinite d.transport.left := transport_finite d
  have : IsAffineHom ((sectionProduct (V := V) s ≫ d.transport).left) := by
    change IsAffineHom ((sectionProduct (V := V) s).left ≫ d.transport.left)
    infer_instance
  exact hU.preimage _

set_option backward.isDefEq.respectTransparency false in
/-- On a finite split cover the invariant open inside an affine open is the
intersection of the inverse images under the finitely many base sections. -/
theorem saturation_affine_of_sections [V.left.IsSeparated] {I : Type u} [Fintype I]
    (s : I → (𝟙_ (Over S) ⟶ A)) [∀ i, IsClosedImmersion (s i).left]
    (hs : ∀ x : A.left, ∃ i, x ∈ Set.range (s i).left)
    {U : V.left.Opens} (hU : IsAffineOpen U) : IsAffineOpen (d.saturation U) := by
  classical
  let W (i : I) := (sectionProduct (V := V) (s i) ≫ d.transport).left ⁻¹ᵁ U
  have hWi (i : I) : IsAffineOpen (W i) := d.isAffinePreimageTransport (s i) hU
  have h : d.saturation U = ⨅ i : Option I, i.elim U W := by
    ext x
    change x ∈ d.saturation U ↔ x ∈ ((⨅ i : Option I, i.elim U W : V.left.Opens) : Set V.left)
    rw [mem_saturation, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    refine ⟨?_, ?_⟩
    · intro H i
      cases i with
      | none => exact H x (d.related_refl x)
      | some i =>
        apply H
        refine ⟨(sectionProduct (V := V) (s i)).left x, ?_, rfl⟩
        have e : sectionProduct (V := V) (s i) ≫ fst V A = 𝟙 V := lift_fst _ _
        exact congrArg (fun f : V ⟶ V ↦ f.left x) e
    · intro H y hy
      obtain ⟨z, hz, hzy⟩ := hy
      obtain ⟨i, hi⟩ := hs ((snd V A).left z)
      have he := sectionProduct_range (V := V) (s i)
      obtain ⟨x', he'⟩ : z ∈ Set.range (sectionProduct (V := V) (s i)).left := he.symm ▸ hi
      have e : sectionProduct (V := V) (s i) ≫ fst V A = 𝟙 V := lift_fst _ _
      have hx' : x' = x := by
        have hh := congrArg (fun f : V ⟶ V ↦ f.left x') e
        change (fst V A).left ((sectionProduct (V := V) (s i)).left x') = x' at hh
        rwa [he', hz, eq_comm] at hh
      subst x'
      have H' : (sectionProduct (V := V) (s i) ≫ d.transport).left x ∈ U := H (some i)
      change d.transport.left ((sectionProduct (V := V) (s i)).left x) ∈ U at H'
      rwa [he', hzy] at H'
  rw [h]
  exact IsAffineOpen.iInf (Option.rec hU hWi)

end ParameterDescent
end SplitParameterSaturation

namespace ParameterDescent

variable {S : Scheme.{u}} (Y A : Over S)

/-- The transport on a base change keeps the point of the original scheme
and replaces the covering coordinate. -/
def canonical : ParameterDescent (snd Y A) where
  transport := lift (fst (Y ⊗ A) A ≫ fst Y A) (snd (Y ⊗ A) A)
  base := lift_snd _ _
  identity := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, Category.id_comp]
    · simp only [Category.assoc, lift_snd, Category.id_comp]
  composition := by
    intro T x b c
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, lift_fst_assoc]
    · simp only [Category.assoc, lift_snd]

private theorem canonical_projection :
    (canonical Y A).transport ≫ fst Y A = fst (Y ⊗ A) A ≫ fst Y A := lift_fst _ _

variable {Y A}

set_option backward.isDefEq.respectTransparency false in
private theorem uniqueEffectiveProjection {V : Over S} {v : V ⟶ A} (d : ParameterDescent v)
    [Flat A.hom] [Surjective A.hom] [QuasiCompact A.hom]
    {W W' : Over S} (r : V ⟶ W) (r' : V ⟶ W')
    (h : IsPullback v.left r.left A.hom W.hom) (h' : IsPullback v.left r'.left A.hom W'.hom)
    (hr : d.transport ≫ r = fst V A ≫ r) (hr' : d.transport ≫ r' = fst V A ≫ r') :
    ∃ e : W ≅ W', r ≫ e.hom = r' := by
  have : Flat r.left := MorphismProperty.of_isPullback h ‹Flat A.hom›
  have : Flat r'.left := MorphismProperty.of_isPullback h' ‹Flat A.hom›
  have : Surjective r.left := MorphismProperty.of_isPullback h ‹Surjective A.hom›
  have : Surjective r'.left := MorphismProperty.of_isPullback h' ‹Surjective A.hom›
  have : QuasiCompact r.left := MorphismProperty.of_isPullback h ‹QuasiCompact A.hom›
  have : QuasiCompact r'.left := MorphismProperty.of_isPullback h' ‹QuasiCompact A.hom›
  obtain ⟨f, hf⟩ : ∃ f : W ⟶ W', r ≫ f = r' := by
    apply existsOverDesc r r'
    intro T x y e
    rw [← d.change_eq_of_projection_eq h hr x y e, d.change_comp_projection hr']
  obtain ⟨g, hg⟩ : ∃ g : W' ⟶ W, r' ≫ g = r := by
    apply existsOverDesc r' r
    intro T x y e
    rw [← d.change_eq_of_projection_eq h' hr' x y e, d.change_comp_projection hr]
  have : Epi r := Over.epi_of_epi_left _
  have : Epi r' := Over.epi_of_epi_left _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · exact (cancel_epi r).mp (by rw [← Category.assoc, hf, hg, Category.comp_id])
  · exact (cancel_epi r').mp (by rw [← Category.assoc, hg, hf, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/-- An existing scheme with affine pullback to a faithfully flat affine cover
of an affine base is affine. -/
theorem isAffineOfAffinePullback {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [Module.Flat R C] [Flat (algebraSpecMap R C)] [Surjective (algebraSpecMap R C)]
    (W : Over (ringSpec R)) (hw : IsAffine (W ⊗ coordSpec R C).left) : IsAffine W.left := by
  let A := coordSpec R C
  let V := W ⊗ A
  let v := snd W A
  let p := fst W A
  let d := canonical W A
  have : IsAffine V.left := hw
  have : Flat A.hom := inferInstanceAs (Flat (algebraSpecMap R C))
  have : Surjective A.hom := inferInstanceAs (Surjective (algebraSpecMap R C))
  have : QuasiCompact A.hom := inferInstanceAs (QuasiCompact (algebraSpecMap R C))
  obtain ⟨W', r, hw', hr, hinv⟩ := d.affineEffectivityOfIsAffine v
  have hp : IsPullback v.left p.left A.hom W.hom := (IsPullback.of_hasPullback W.hom A.hom).flip
  obtain ⟨e, _⟩ := uniqueEffectiveProjection d p r hp hr (canonical_projection W A) hinv
  have : IsAffine ((Over.forget (ringSpec R)).obj W') := hw'
  exact IsAffine.of_isIso ((Over.forget (ringSpec R)).mapIso e).hom

end ParameterDescent

section ParameterBaseChange

namespace ParameterDescent

variable {S S' : Scheme.{u}} (a : S' ⟶ S) {A V : Over S} {v : V ⟶ A}
  (d : ParameterDescent v)

private abbrev F := Over.pullback a
private abbrev J := Over.map a

private def baseChangeTransport : (F a).obj V ⊗ (F a).obj A ⟶ (F a).obj V :=
  Functor.LaxMonoidal.μ (F a) V A ≫ (F a).map d.transport

private abbrev unbase {X : Over S'} {Y : Over S} (x : X ⟶ (F a).obj Y) : (J a).obj X ⟶ Y :=
  ((Over.mapPullbackAdj a).homEquiv X Y).symm x

set_option backward.isDefEq.respectTransparency false in
private theorem unbase_transport {T : Over S'} (x : T ⟶ (F a).obj V) (b : T ⟶ (F a).obj A) :
    unbase a (lift x b ≫ d.baseChangeTransport a) = d.change (unbase a x) (unbase a b) := by
  let E := Over.mapPullbackAdj a
  let comparison := Functor.LaxMonoidal.μ (F a) V A
  let t : T ⟶ (F a).obj (V ⊗ A) := lift x b ≫ comparison
  have ht₁ : t ≫ (F a).map (fst V A) = x := by
    simp only [t, comparison, Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have ht₂ : t ≫ (F a).map (snd V A) = b := by
    simp only [t, comparison, Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
  have ht : unbase a t = lift (unbase a x) (unbase a b) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← E.homEquiv_naturality_right_symm, ht₁]
    · rw [lift_snd, ← E.homEquiv_naturality_right_symm, ht₂]
  change unbase a (lift x b ≫ comparison ≫ (F a).map d.transport) = _
  rw [← Category.assoc]
  change (E.homEquiv _ _).symm (t ≫ (F a).map d.transport) = _
  rw [E.homEquiv_naturality_right_symm]
  change unbase a t ≫ d.transport = _
  rw [ht]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Relative descent transport after any scalar extension. -/
def changeBase : ParameterDescent ((F a).map v) where
  transport := d.baseChangeTransport a
  base := by
    change (Functor.LaxMonoidal.μ (F a) V A ≫ (F a).map d.transport) ≫ (F a).map v = _
    rw [Category.assoc, ← Functor.map_comp, d.base, Functor.Monoidal.μ_snd]
  identity := by
    let E := Over.mapPullbackAdj a
    apply (E.homEquiv ((F a).obj V) V).symm.injective
    change unbase a (lift (𝟙 ((F a).obj V)) ((F a).map v) ≫ d.baseChangeTransport a) =
      unbase a (𝟙 ((F a).obj V))
    rw [unbase_transport]
    have e : unbase a ((F a).map v) = unbase a (𝟙 ((F a).obj V)) ≫ v := by
      have hh := E.homEquiv_naturality_right_symm (𝟙 ((F a).obj V)) v
      rw [Category.id_comp] at hh
      exact hh
    rw [e, d.change_identity]
  composition := by
    intro T x b c
    apply ((Over.mapPullbackAdj a).homEquiv T V).symm.injective
    change unbase a (lift (lift x b ≫ d.baseChangeTransport a) c ≫ d.baseChangeTransport a) =
      unbase a (lift x c ≫ d.baseChangeTransport a)
    rw [unbase_transport, unbase_transport, unbase_transport, d.change_change]

private abbrev toOriginal (X : Over S) : (J a).obj ((F a).obj X) ⟶ X :=
  (Over.mapPullbackAdj a).counit.app X

private instance changeBase_finite [IsFinite A.hom] : IsFinite ((F a).obj A).hom :=
  inferInstanceAs (IsFinite (pullback.snd A.hom a))

set_option backward.isDefEq.respectTransparency false in
/-- Taking the invariant open in an open subscheme commutes with base change. -/
theorem saturation_changeBase [IsFinite A.hom] (U : V.left.Opens) :
    (d.changeBase a).saturation ((toOriginal a V).left ⁻¹ᵁ U) =
      (toOriginal a V).left ⁻¹ᵁ d.saturation U := by
  let p := fst V A
  let f := d.transport
  let E := (F a).obj V ⊗ (F a).obj A
  let comparison : E ⟶ (F a).obj (V ⊗ A) := Functor.LaxMonoidal.μ (F a) V A
  let l := (toOriginal a V).left
  let r := (toOriginal a (V ⊗ A)).left
  let q := ((F a).map f).left
  have : IsIso comparison.left := (Over.forget S').map_isIso comparison
  have h := (pullbackMapSquare a f).flip
  have he : q ≫ l = r ≫ f.left := h.w.symm
  have hμ : comparison.left ≫ r ≫ p.left = (fst ((F a).obj V) ((F a).obj A)).left ≫ l := by
    have h₁ := (pullbackMapSquare a p).w
    change ((F a).map p).left ≫ l = r ≫ p.left at h₁
    rw [← h₁, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_fst]
  let bad : Set (V ⊗ A).left := p.left ⁻¹' (U : Set V.left)ᶜ
  have image : q '' (r ⁻¹' bad) = l ⁻¹' (f.left '' bad) :=
    Scheme.image_preimage_eq_of_isPullback h bad
  have himage : (comparison.left ≫ q) '' ((comparison.left ≫ r) ⁻¹' bad) = l ⁻¹' (f.left '' bad) := by
    change (q ∘ comparison.left) '' ((r ∘ comparison.left) ⁻¹' bad) = _
    rw [Set.image_comp, Set.preimage_comp, Set.image_preimage_eq _ comparison.left.surjective, image]
  ext x
  change x ∈ ((comparison.left ≫ q) '' ((fst ((F a).obj V) ((F a).obj A)).left ⁻¹'
      (l ⁻¹' (U : Set V.left))ᶜ))ᶜ ↔ x ∈ l ⁻¹' (f.left '' bad)ᶜ
  have hbad : (fst ((F a).obj V) ((F a).obj A)).left ⁻¹' (l ⁻¹' (U : Set V.left))ᶜ =
      (comparison.left ≫ r) ⁻¹' bad := by
    ext z
    change ¬ l ((fst ((F a).obj V) ((F a).obj A)).left z) ∈ U ↔
      ¬ p.left ((comparison.left ≫ r) z) ∈ U
    exact not_congr (by
      rw [← Scheme.Hom.comp_apply, Category.assoc, hμ]
      rfl)
  rw [hbad, himage, Set.preimage_compl]

end ParameterDescent
end ParameterBaseChange

namespace ParameterDescent

section SplitSections

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

set_option backward.isDefEq.respectTransparency false in
private theorem existsSections_of_finiteSplit [Algebra.IsFiniteSplit R T] :
    ∃ (I : Type u) (_ : Fintype I) (s : I → (𝟙_ (Over (ringSpec R)) ⟶ coordSpec R T)),
      (∀ i, IsClosedImmersion (s i).left) ∧ ∀ x : (coordSpec R T).left,
        ∃ i, x ∈ Set.range (s i).left := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R T
  let f (i : ULift.{u} (Fin n)) : T →ₐ[R] R := (Pi.evalAlgHom R (fun _ : Fin n ↦ R) i.down).comp e.toAlgHom
  let s (i : ULift.{u} (Fin n)) : 𝟙_ (Over (ringSpec R)) ⟶ coordSpec R T :=
    Over.homMk (Spec.map (CommRingCat.ofHom (f i).toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (f i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) = 𝟙 (ringSpec R)
      rw [← Spec.map_comp]
      have h : CommRingCat.ofHom (algebraMap R T) ≫ CommRingCat.ofHom (f i).toRingHom =
          𝟙 (CommRingCat.of R) := by
        ext x
        exact (f i).commutes x
      rw [h, Spec.map_id])
  refine ⟨_, inferInstance, s, ?_, ?_⟩
  · intro i
    apply IsClosedImmersion.spec_of_surjective
    exact (Function.surjective_eval i.down).comp e.surjective
  · intro x
    change PrimeSpectrum T at x
    let x' := PrimeSpectrum.comap e.symm.toRingHom x
    obtain ⟨i, y, hy⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq x'
    refine ⟨⟨i⟩, y, ?_⟩
    change PrimeSpectrum.comap (f ⟨i⟩).toRingHom y = x
    change PrimeSpectrum.comap ((Pi.evalRingHom (fun _ : Fin n ↦ R) i).comp e.toRingHom) y = _
    rw [PrimeSpectrum.comap_comp_apply, hy]
    change PrimeSpectrum.comap e.toRingHom (PrimeSpectrum.comap e.symm.toRingHom x) = _
    have he : e.symm.toRingEquiv.toRingHom.comp e.toRingEquiv.toRingHom = RingHom.id T :=
      RingHom.ext fun x ↦ e.symm_apply_apply x
    rw [← PrimeSpectrum.comap_comp_apply, he]
    rfl

private theorem existsSections_of_splitPullback {C : Type u} [CommRing C] [Algebra R C]
    [Algebra.IsFiniteSplit C (C ⊗[R] T)] :
    let F := Over.pullback (algebraSpecMap R C)
    ∃ (I : Type u) (_ : Fintype I) (s : I → (𝟙_ (Over (ringSpec C)) ⟶ F.obj (coordSpec R T))),
      (∀ i, IsClosedImmersion (s i).left) ∧ ∀ x : (F.obj (coordSpec R T)).left,
        ∃ i, x ∈ Set.range (s i).left := by
  intro F
  let e : F.obj (coordSpec R T) ≅ coordSpec C (C ⊗[R] T) :=
    Over.isoMk (pullbackSymmetry (algebraSpecMap R T) (algebraSpecMap R C) ≪≫
      pullbackSpecIso R C T) (by
        change ((pullbackSymmetry (algebraSpecMap R T) (algebraSpecMap R C)).hom ≫
          (pullbackSpecIso R C T).hom) ≫ algebraSpecMap C (C ⊗[R] T) =
            pullback.snd (algebraSpecMap R T) (algebraSpecMap R C)
        rw [Category.assoc, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst])
  obtain ⟨I, hI, s, hs, h⟩ := existsSections_of_finiteSplit (R := C) (T := C ⊗[R] T)
  have : IsIso e.inv.left := (Over.forget (ringSpec C)).map_isIso e.inv
  refine ⟨I, hI, fun i ↦ s i ≫ e.inv, fun i ↦ ?_, fun x ↦ ?_⟩
  · have : IsClosedImmersion (s i).left := hs i
    exact IsClosedImmersion.comp (s i).left e.inv.left
  · obtain ⟨i, y, hy⟩ := h (e.hom.left x)
    refine ⟨i, y, ?_⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply, hy]
    have h := congrArg (fun f : F.obj (coordSpec R T) ⟶ F.obj (coordSpec R T) ↦ f.left x) e.hom_inv_id
    exact h

end SplitSections

section AffineOpenReflection

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {V : Over (ringSpec R)}

set_option backward.isDefEq.respectTransparency false in
private theorem isAffineOpenOfAffinePullback [Module.Flat R C]
    [Surjective (algebraSpecMap R C)] [Flat (algebraSpecMap R C)] (U : V.left.Opens)
    (h : IsAffineOpen (pullback.fst V.hom (algebraSpecMap R C) ⁻¹ᵁ U)) : IsAffineOpen U := by
  let a := algebraSpecMap R C
  let l := pullback.fst V.hom a
  let Z := l ⁻¹ᵁ U
  let i := IsOpenImmersion.lift U.ι (Z.ι ≫ l) (by
    simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.image_preimage_subset _ _)
  have hi : IsPullback i Z.ι U.ι l := IsOpenImmersion.isPullback _ _ _ _
    (IsOpenImmersion.lift_fac _ _ _).symm (by rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι])
  let W : Over (ringSpec R) := Over.mk (U.ι ≫ V.hom)
  have hw : IsAffine Z.toScheme := h
  have e : Z.toScheme ≅ (W ⊗ coordSpec R C).left :=
    (hi.paste_vert (IsPullback.of_hasPullback V.hom a)).isoPullback
  have hZW : IsAffine (W ⊗ coordSpec R C).left := IsAffine.of_isIso e.inv
  exact isAffineOfAffinePullback W hZW

end AffineOpenReflection

section InvariantSaturation

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
  [Module.Finite R A] [Algebra.Etale R A] {V : Over (ringSpec R)}
  {v : V ⟶ coordSpec R A} (d : ParameterDescent v)

private instance finiteCoordinateCover : IsFinite (coordSpec R A).hom :=
  (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R A))).mpr
    (RingHom.finite_algebraMap.mpr ‹Module.Finite R A›)

set_option backward.isDefEq.respectTransparency false in
/-- A saturated affine open is affine for finite étale descent on a
separated scheme over an affine base, when the splitting algebra is finite free. -/
theorem saturation_affine [V.left.IsSeparated] {U : V.left.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (d.saturation U) := by
  obtain ⟨C, _, _, hff, _, _, hsplit⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
    (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := A))
  let a := algebraSpecMap R C
  let F := Over.pullback a
  obtain ⟨hs, hf, _, _⟩ := splittingCover R C
  let W := F.obj V
  let l := pullback.fst V.hom a
  let U' := l ⁻¹ᵁ U
  have ha : IsAffineHom a := inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R C))))
  have : IsAffineHom l := MorphismProperty.pullback_fst _ _ ha
  have hu : IsAffineOpen U' := hU.preimage l
  have h : IsSeparated W.hom := inferInstanceAs (IsSeparated (pullback.snd V.hom a))
  have hs' : W.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from W.hom]
    infer_instance
  obtain ⟨I, hI, s, hcs, hcov⟩ := existsSections_of_splitPullback (R := R) (T := A) (C := C)
  have he : IsAffineOpen ((d.changeBase a).saturation U') :=
    (d.changeBase a).saturation_affine_of_sections s hcov hu
  apply isAffineOpenOfAffinePullback (C := C)
  have hSat := d.saturation_changeBase a U
  change (d.changeBase a).saturation U' = l ⁻¹ᵁ d.saturation U at hSat
  exact hSat ▸ he

set_option backward.isDefEq.respectTransparency false in
/-- A common affine neighbourhood of each overlap class supplies invariant
open affines covering the datum. -/
theorem existsInvariantAffineOpen [V.left.IsSeparated] (x : V.left)
    (h : ∃ U : V.left.Opens, IsAffineOpen U ∧ ∀ y, d.Related x y → y ∈ U) :
    ∃ W : V.left.Opens, x ∈ W ∧ d.Invariant W ∧ IsAffineOpen W := by
  obtain ⟨U, hU, hx⟩ := h
  exact ⟨d.saturation U, (d.mem_saturation U x).mpr hx, d.saturation_invariant U,
    d.saturation_affine hU⟩

end InvariantSaturation

section EffectiveRelation

variable {S : Scheme.{u}} {A V W : Over S} {v : V ⟶ A} (d : ParameterDescent v)
  (r : V ⟶ W) (hr : IsPullback v.left r.left A.hom W.hom)
  (h : d.transport ≫ r = fst V A ≫ r)

include hr h in
set_option backward.isDefEq.respectTransparency false in
/-- An effective datum relates precisely points with the same image in the
base of the descent. -/
theorem related_iff_projection_eq (x y : V.left) : d.Related x y ↔ r.left x = r.left y := by
  constructor
  · rintro ⟨z, hx, hy⟩
    have e := congrArg (fun f : V ⊗ A ⟶ W ↦ f.left z) h
    change r.left (d.transport.left z) = r.left ((fst V A).left z) at e
    rw [hx, hy] at e
    exact e.symm
  · intro he
    let T := pullback r r
    let p : T ⟶ V := pullback.fst r r
    let q : T ⟶ V := pullback.snd r r
    have hP := (IsPullback.of_hasPullback r r).map (Over.forget S)
    obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback hP x y he
    let l : T ⟶ V ⊗ A := lift p (q ≫ v)
    refine ⟨l.left z, ?_, ?_⟩
    · exact (congrArg (fun f : T ⟶ V ↦ f.left z) (lift_fst p (q ≫ v))).trans hz
    · have e : l ≫ d.transport = q := d.change_eq_of_projection_eq hr h p q pullback.condition
      exact (congrArg (fun f : T ⟶ V ↦ f.left z) e).trans hz'

end EffectiveRelation

set_option backward.isDefEq.respectTransparency false in
/-- If the inverse image of a set of points has a common affine neighbourhood
on a finite étale cover, the original set has a common affine neighbourhood. -/
theorem affineNeighbourhoodOfFiniteEtaleCover {R C : Type u} [CommRing R] [CommRing C]
    [Algebra R C] [Module.Free R C] [Module.Finite R C] [Module.FaithfullyFlat R C] [Algebra.Etale R C]
    {V : Over (ringSpec R)} [V.left.IsSeparated] (Z : Set V.left)
    (U : (V ⊗ coordSpec R C).left.Opens) (hU : IsAffineOpen U)
    (hZ : ∀ x : (V ⊗ coordSpec R C).left, (fst V (coordSpec R C)).left x ∈ Z → x ∈ U) :
    ∃ O : V.left.Opens, IsAffineOpen O ∧ Z ⊆ O := by
  let A := coordSpec R C
  let W := V ⊗ A
  let a := algebraSpecMap R C
  let p := fst V A
  let v := snd V A
  let d := canonical V A
  obtain ⟨hs, hf, _, he⟩ := splittingCover R C
  have : Surjective A.hom := hs
  have : Flat A.hom := hf
  have : Etale A.hom := he
  have : IsFinite A.hom := finiteCoordinateCover
  have : Surjective p.left := inferInstanceAs (Surjective (pullback.fst V.hom A.hom))
  have : Etale p.left := inferInstanceAs (Etale (pullback.fst V.hom A.hom))
  have : IsSeparated p.left := inferInstanceAs (IsSeparated (pullback.fst V.hom A.hom))
  have : W.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from p.left]
    infer_instance
  let U₀ := d.saturation U
  have hU₀ : IsAffineOpen U₀ := d.saturation_affine hU
  have hc : IsPullback v.left p.left A.hom V.hom := (IsPullback.of_hasPullback V.hom A.hom).flip
  have hrel (x y : W.left) : d.Related x y ↔ p.left x = p.left y :=
    d.related_iff_projection_eq p hc (canonical_projection V A) x y
  let O : V.left.Opens := ⟨p.left '' (U₀ : Set W.left), p.left.isOpenMap _ U₀.isOpen⟩
  have h_eq : p.left ⁻¹ᵁ O = U₀ := by
    ext x
    change (∃ y : W.left, y ∈ U₀ ∧ p.left y = p.left x) ↔ x ∈ U₀
    constructor
    · rintro ⟨y, hy, e⟩
      apply (d.mem_saturation U x).mpr
      intro z hz
      have hxy := (hrel y x).mpr e
      exact (d.mem_saturation U y).mp hy z (d.related_trans hxy hz)
    · intro h
      exact ⟨x, h, rfl⟩
  have hO : IsAffineOpen O := isAffineOpenOfAffinePullback (C := C) O (h_eq.symm ▸ hU₀)
  refine ⟨O, hO, fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := p.left.surjective x
  refine ⟨y, (d.mem_saturation U y).mpr ?_, hy⟩
  intro z hz
  apply hZ z
  rw [← (hrel y z).mp hz, hy]
  exact hx

end ParameterDescent

set_option backward.isDefEq.respectTransparency false in
/-- Common affine neighbourhoods for the finite overlap classes give the
Borel presentation for the original model. -/
theorem presentationOfCommonAffineNeighbourhoods {R A : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    [Module.FaithfullyFlat R A] [Algebra.Etale R A] {G : Grp (Over (ringSpec R))}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSplitModel G) (P : Over (ringSpec A))
    (B : Family ((changeBase (algebraSpecMap R A)).obj G) P)
    (hP : Smooth P.hom) (hS : IsSeparated P.hom) (hB : IsBorelFamily B)
    (hRep : ∀ (T : Over (ringSpec A)) (F : Family ((changeBase (algebraSpecMap R A)).obj G) T),
      IsBorelFamily F → ∃! x : T ⟶ P, SameFamily (B.pullback x) F)
    (hAff : ∀ (Z : Set P.left), Z.Finite →
      (∃ s : ringSpec R, ∀ z ∈ Z, (P.hom ≫ algebraSpecMap R A) z = s) →
        ∃ U : P.left.Opens, IsAffineOpen U ∧ Z ⊆ U) : Nonempty (Presentation G) := by
  let a := algebraSpecMap R A
  let V := (Over.map a).obj P
  let v : V ⟶ coordSpec R A := Over.homMk P.hom
  obtain ⟨hs, hf, _, _⟩ := splittingCover R A
  have : IsFinite a := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R A))).mpr
    (RingHom.finite_algebraMap.mpr ‹Module.Finite R A›)
  have : IsFinite (Over.mk a).hom := ‹IsFinite a›
  obtain ⟨d, hd⟩ := existsParameterDescent a B hB hRep
  have : Module.Free R A := splittingAlgebraFree R A
  have hV : V.left.IsSeparated := by
    constructor
    change IsSeparated (terminal.from P.left)
    rw [← terminal.comp_from P.hom]
    infer_instance
  have hv : IsFinite (coordSpec R A).hom := ParameterDescent.finiteCoordinateCover
  have hcov (x : V.left) : ∃ U : V.left.Opens, x ∈ U ∧ d.Invariant U ∧ IsAffineOpen U := by
    let Z : Set P.left := {y | d.Related x y}
    have hFibre : ∃ s : ringSpec R, ∀ z ∈ Z, (P.hom ≫ a) z = s := by
      refine ⟨V.hom x, fun y hRel ↦ ?_⟩
      obtain ⟨z, hx, hy⟩ := hRel
      have e : (fst V (Over.mk a)).left ≫ V.hom = d.transport.left ≫ V.hom :=
        (CategoryTheory.Over.w (fst V (Over.mk a))).trans (CategoryTheory.Over.w d.transport).symm
      have h := congrArg (fun f : (V ⊗ Over.mk a).left ⟶ ringSpec R ↦ f z) e
      change V.hom ((fst V (Over.mk a)).left z) = V.hom (d.transport.left z) at h
      rw [hx, hy] at h
      exact h.symm
    obtain ⟨U, hU, hZ⟩ := hAff Z (d.finite_related x) hFibre
    exact ParameterDescent.existsInvariantAffineOpen (v := v) d x ⟨U, hU, fun _ hy ↦ hZ hy⟩
  have heff : d.IsEffective := ParameterDescent.effectiveOfInvariantAffineCover (v := v) d hcov
  obtain ⟨W, U, hW, hU, hrep⟩ := borelClassificationOfEffectiveDescent a B hP hB hRep d hd heff
  exact ⟨⟨W, hW, U, hU, fun T x ↦ isBorelFamily_pullback U hU x, hrep,
    fieldClassifiesOfRepresents hG U hrep⟩⟩

section QuotientAction

variable {S : Scheme.{u}} {G B : Grp (Over S)} {P : Over S} (p : G.X ⟶ P) (j : B ⟶ G)
variable [Flat p.left] [Surjective p.left]

set_option backward.isDefEq.respectTransparency false in
/-- Left multiplication descends along the right coset projection. -/
theorem existsRightQuotientAction [QuasiCompact p.left]
    (h : ∀ (T : Over S) (x y : T ⟶ G.X),
      x ≫ p = y ≫ p ↔ ∃ b : T ⟶ B.X, x * (b ≫ j.hom.hom) = y) :
    ∃ m : G.X ⊗ P ⟶ P, ∀ {T : Over S} (g x : T ⟶ G.X),
      lift g (x ≫ p) ≫ m = (g * x) ≫ p := by
  let a := G.X ◁ p
  let b : G.X ⊗ G.X ⟶ P := μ[G.X] ≫ p
  have hpb := ((productPullback G.X p).map (CategoryTheory.Over.forget S)).flip
  have ha₁ : Flat a.left := MorphismProperty.of_isPullback hpb ‹Flat p.left›
  have ha₂ : Surjective a.left := MorphismProperty.of_isPullback hpb ‹Surjective p.left›
  have ha₃ : QuasiCompact a.left := MorphismProperty.of_isPullback hpb ‹QuasiCompact p.left›
  have he : ∀ (T : Over S) (x y : T ⟶ G.X ⊗ G.X), x ≫ a = y ≫ a → x ≫ b = y ≫ b := by
    intro T x y he
    let g := x ≫ fst G.X G.X
    let k := x ≫ snd G.X G.X
    let l := y ≫ snd G.X G.X
    have hg : y ≫ fst G.X G.X = g := by
      have e := congrArg (· ≫ fst G.X P) he.symm
      simpa only [g, Category.assoc, a, whiskerLeft_fst] using e
    have e : k ≫ p = l ≫ p := by
      have e := congrArg (· ≫ snd G.X P) he
      simpa only [k, l, Category.assoc, a, whiskerLeft_snd] using e
    obtain ⟨z, hz⟩ := (h T k l).mp e
    have e' : (g * k) ≫ p = (g * l) ≫ p :=
      (h T (g * k) (g * l)).mpr ⟨z, by rw [mul_assoc, hz]⟩
    change x ≫ μ[G.X] ≫ p = y ≫ μ[G.X] ≫ p
    have hx : lift (x ≫ fst G.X G.X) k = x := by
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
    have hy : lift (y ≫ fst G.X G.X) l = y := by
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
    calc
      x ≫ μ[G.X] ≫ p = (g * k) ≫ p := by rw [← Category.assoc, ← hx]; rfl
      _ = (g * l) ≫ p := e'
      _ = y ≫ μ[G.X] ≫ p := by
        rw [← Category.assoc, ← hy, hg]
        rfl
  obtain ⟨m, hm⟩ := existsOverDesc a b he
  refine ⟨m, fun {T} g x ↦ ?_⟩
  have h : lift g x ≫ a = lift g (x ≫ p) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [a, Category.assoc, whiskerLeft_fst, lift_fst]
    · simp only [a, Category.assoc, whiskerLeft_snd, lift_snd_assoc, lift_snd]
  rw [← h, Category.assoc, hm]
  exact (Category.assoc (lift g x) μ[G.X] p).symm

variable {p}

private theorem afterLocalQuotientLift
    {X Y : Over S} {f : X ⟶ P} {g h : X ⟶ Y}
    (eq : ∀ {T : Over S} (a : T ⟶ X) (x : T ⟶ G.X), x ≫ p = a ≫ f → a ≫ g = a ≫ h) :
    g = h := by
  let a := pullback.snd p f
  let x := pullback.fst p f
  have hp := (IsPullback.of_hasPullback p f).map (CategoryTheory.Over.forget S)
  have hf : Flat a.left := MorphismProperty.of_isPullback hp ‹Flat p.left›
  have hs : Surjective a.left := MorphismProperty.of_isPullback hp ‹Surjective p.left›
  have : Epi a.left := Flat.epi_of_flat_of_surjective a.left
  have ha : Epi a := Over.epi_of_epi_left a
  exact (cancel_epi a).mp (eq a x pullback.condition)

variable (m : G.X ⊗ P ⟶ P)
  (hm : ∀ {T : Over S} (g x : T ⟶ G.X), lift g (x ≫ p) ≫ m = (g * x) ≫ p)

def actRightQuotient {T : Over S} (g : T ⟶ G.X) (y : T ⟶ P) : T ⟶ P := lift g y ≫ m

@[simp]
theorem comp_actRightQuotient {T U : Over S} (a : U ⟶ T) (g : T ⟶ G.X) (y : T ⟶ P) :
    a ≫ actRightQuotient m g y = actRightQuotient m (a ≫ g) (a ≫ y) := by
  simp only [actRightQuotient, ← Category.assoc, comp_lift]

include hm in
set_option backward.isDefEq.respectTransparency false in
theorem actRightQuotient_one {T : Over S} (y : T ⟶ P) :
    actRightQuotient m 1 y = y := by
  apply afterLocalQuotientLift (f := y) (p := p)
  intro W a x hx
  rw [comp_actRightQuotient, MonObj.comp_one, ← hx]
  change lift 1 (x ≫ p) ≫ m = x ≫ p
  rw [hm, one_mul]

include hm in
set_option backward.isDefEq.respectTransparency false in
theorem actRightQuotient_mul {T : Over S} (g h : T ⟶ G.X) (y : T ⟶ P) :
    actRightQuotient m (g * h) y = actRightQuotient m g (actRightQuotient m h y) := by
  apply afterLocalQuotientLift (f := y) (p := p)
  intro W a x hx
  rw [comp_actRightQuotient, comp_actRightQuotient, comp_actRightQuotient, MonObj.comp_mul, ← hx]
  change lift ((a ≫ g) * (a ≫ h)) (x ≫ p) ≫ m =
    lift (a ≫ g) (lift (a ≫ h) (x ≫ p) ≫ m) ≫ m
  rw [hm, hm, hm, mul_assoc]

private def translatedProductMap {A C : Over S} (g : C ⟶ G.X) :
    (P ⊗ A) ⊗ C ⟶ (P ⊗ A) ⊗ C :=
  lift (lift (actRightQuotient m (snd (P ⊗ A) C ≫ g) (fst (P ⊗ A) C ≫ fst P A))
    (fst (P ⊗ A) C ≫ snd P A)) (snd (P ⊗ A) C)

private theorem translatedProductMap_P {A C : Over S} (g : C ⟶ G.X) :
    translatedProductMap m (A := A) g ≫ fst _ _ ≫ fst _ _ =
      actRightQuotient m (snd (P ⊗ A) C ≫ g) (fst (P ⊗ A) C ≫ fst P A) := by
  simp only [translatedProductMap, ← Category.assoc, lift_fst]

private theorem translatedProductMap_A {A C : Over S} (g : C ⟶ G.X) :
    translatedProductMap m (A := A) g ≫ fst _ _ ≫ snd _ _ =
      fst (P ⊗ A) C ≫ snd P A := by
  simp only [translatedProductMap, ← Category.assoc, lift_fst, lift_snd]

private theorem translatedProductMap_C {A C : Over S} (g : C ⟶ G.X) :
    translatedProductMap m (A := A) g ≫ snd _ _ = snd _ _ := lift_snd _ _

include hm in
set_option backward.isDefEq.respectTransparency false in
private theorem translatedProductMap_comp_inv {A C : Over S} (g : C ⟶ G.X) :
    translatedProductMap m (A := A) g ≫ translatedProductMap m g⁻¹ = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, Category.id_comp, translatedProductMap_P,
        comp_actRightQuotient, ← Category.assoc _ (snd (P ⊗ A) C) g⁻¹, translatedProductMap_C]
      rw [GrpObj.comp_inv, ← actRightQuotient_mul m hm, inv_mul_cancel, actRightQuotient_one m hm]
    · simp only [Category.assoc, Category.id_comp, translatedProductMap_A]
  · simp only [Category.assoc, Category.id_comp, translatedProductMap_C]

include hm in
/-- Translation on a base-changed quotient preserves the two base coordinates. -/
private def translatedProductIso {A C : Over S} (g : C ⟶ G.X) :
    (P ⊗ A) ⊗ C ≅ (P ⊗ A) ⊗ C where
  hom := translatedProductMap m g
  inv := translatedProductMap m g⁻¹
  hom_inv_id := translatedProductMap_comp_inv m hm g
  inv_hom_id := by simpa only [inv_inv] using translatedProductMap_comp_inv (A := A) m hm g⁻¹

end QuotientAction

section QuotientBaseChange

variable {S S' : Scheme.{u}} {G B : Grp (Over S)} {P : Over S}

set_option backward.isDefEq.respectTransparency false in
private theorem rightQuotientRelation_pullback (a : S' ⟶ S) (p : G.X ⟶ P) (j : B ⟶ G)
    (h : ∀ (T : Over S) (x y : T ⟶ G.X),
      x ≫ p = y ≫ p ↔ ∃ b : T ⟶ B.X, x * (b ≫ j.hom.hom) = y) :
    ∀ (T : Over S') (x y : T ⟶ ((changeBase a).obj G).X),
      x ≫ (Over.pullback a).map p = y ≫ (Over.pullback a).map p ↔
        ∃ b : T ⟶ ((changeBase a).obj B).X, x * (b ≫ ((changeBase a).map j).hom.hom) = y := by
  intro T x y
  let E := Over.mapPullbackAdj a
  let f := unbasePoint a T G
  let fB := unbasePoint a T B
  constructor
  · intro he
    have hxy := congrArg ((E.homEquiv T P).symm) he
    rw [E.homEquiv_naturality_right_symm, E.homEquiv_naturality_right_symm] at hxy
    obtain ⟨b, hb⟩ := (h _ (f x) (f y)).mp hxy
    refine ⟨fB.symm b, f.injective ?_⟩
    rw [map_mul, unbasePoint_map, show fB (fB.symm b) = b from fB.apply_symm_apply b]
    exact hb
  · rintro ⟨b, hb⟩
    apply (E.homEquiv T P).symm.injective
    rw [E.homEquiv_naturality_right_symm, E.homEquiv_naturality_right_symm]
    apply (h _ (f x) (f y)).mpr
    refine ⟨fB b, ?_⟩
    rw [← unbasePoint_map a j b, ← map_mul, hb]

end QuotientBaseChange

private theorem finiteFieldMapOfClosedPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ ringSpec k) [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x}) :
    IsFinite (X.fromSpecResidueField x ≫ f) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.mp hx
  exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance

/-- A finite map from an irreducible scheme cannot send a proper closed subset onto its image. -/
private theorem finiteImageComplementNonempty {X Y : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Y) [IsFinite f] {W : Set X} (hW : IsClosed W) (hn : Wᶜ.Nonempty) :
    (f '' W)ᶜ.Nonempty := by
  refine ⟨f (genericPoint X), ?_⟩
  rintro ⟨x, hx, he⟩
  have h : genericPoint X = x := (f.isDiscrete_preimage_singleton (f (genericPoint X))).eq_of_specializes
    (genericPoint_specializes x) rfl he
  obtain ⟨w, hw⟩ := hn
  exact hw (((genericPoint_spec X).mem_closed_set_iff hW).mp (h.symm ▸ hx) (Set.mem_univ w))

set_option backward.isDefEq.respectTransparency false in
/-- If a good open in the product meets the fibre over each chosen closed
point, a closed point of the first factor is good on the entire finite set. -/
private theorem existsClosedPointForOpenConditions {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ ringSpec k) (g : Y ⟶ ringSpec k)
    [IrreducibleSpace X] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (hI : ∀ (K : Type u) [Field K] (a : ringSpec K ⟶ ringSpec k),
      IrreducibleSpace (pullback f a : Scheme))
    (U : (pullback f g : Scheme).Opens) (Z : Set Y) (hZ : Z.Finite)
    (hclosed : ∀ z ∈ Z, IsClosed {z})
    (hU : ∀ z ∈ Z, ∃ t : (pullback f g : Scheme), pullback.snd f g t = z ∧ t ∈ U) :
    ∃ x : X, IsClosed {x} ∧ ∀ t : (pullback f g : Scheme),
      pullback.fst f g t = x → pullback.snd f g t ∈ Z → t ∈ U := by
  let q : (pullback f g : Scheme) ⟶ Y := pullback.snd f g
  let p : (pullback f g : Scheme) ⟶ X := pullback.fst f g
  let P (z : Y) := q.fiber z
  let i (z : Y) : P z ⟶ pullback f g := q.fiberι z
  let r (z : Y) : P z ⟶ X := i z ≫ p
  let V (z : Y) : Set X := (r z '' ((i z) ⁻¹' (U : Set (pullback f g : Scheme)))ᶜ)ᶜ
  have hV (z : Y) (hz : z ∈ Z) : IsOpen (V z) ∧ (V z).Nonempty := by
    let a := Y.fromSpecResidueField z ≫ g
    have hpb : IsPullback (r z) (q.fiberToSpecResidueField z) f a :=
      (IsPullback.of_hasPullback q (Y.fromSpecResidueField z)).paste_horiz
        (IsPullback.of_hasPullback f g)
    have : IsFinite a := finiteFieldMapOfClosedPoint g z (hclosed z hz)
    have : IsFinite (r z) := MorphismProperty.of_isPullback hpb.flip ‹IsFinite a›
    have : IrreducibleSpace (pullback f a : Scheme) := hI (Y.residueField z) a
    have : IrreducibleSpace (P z) :=
      hpb.isoPullback.inv.surjective.irreducibleSpace hpb.isoPullback.inv.continuous
    have hB : IsClosed (((i z) ⁻¹' (U : Set (pullback f g : Scheme)))ᶜ) :=
      (U.isOpen.preimage (i z).continuous).isClosed_compl
    refine ⟨((r z).isClosedMap _ hB).isOpen_compl, finiteImageComplementNonempty (r z) hB ?_⟩
    obtain ⟨t, ht, htU⟩ := hU z hz
    have h : t ∈ Set.range (i z) := (q.range_fiberι z).symm ▸ ht
    obtain ⟨s, hs⟩ := h
    refine ⟨s, ?_⟩
    rw [compl_compl]
    change (i z) s ∈ U
    rwa [hs]
  let W : Set X := ⋂ z ∈ Z, V z
  have hW : IsOpen W := hZ.isOpen_biInter fun z hz ↦ (hV z hz).1
  have hη : genericPoint X ∈ W := by
    refine Set.mem_iInter₂.mpr fun z hz ↦ ?_
    exact ((genericPoint_spec X).mem_open_set_iff (hV z hz).1).mpr
      (by simpa only [Set.univ_inter] using (hV z hz).2)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx, hxclosed⟩ := nonempty_inter_closedPoints (Set.nonempty_of_mem hη) hW.isLocallyClosed
  refine ⟨x, hxclosed, fun t ht hz ↦ ?_⟩
  exact by
    by_contra htU
    let z := q t
    have hy : t ∈ Set.range (i z) := (q.range_fiberι z).symm ▸ (show q t ∈ ({z} : Set Y) from rfl)
    obtain ⟨s, hs⟩ := hy
    have hv : x ∈ V z := Set.mem_iInter₂.mp hx z hz
    exact hv ⟨s, (show (i z) s ∉ U by rwa [hs]), by
      change p ((i z) s) = x
      rw [hs]
      exact ht⟩

section FibreTranslation

open private irreducible_of_geometricallyConnected from LinearAlgebraicGroups.Solvable.WordDomainGeometry

variable {S : Scheme.{u}} {G : Grp (Over S)} {P X : Over S}
  (p : G.X ⟶ P) (m : G.X ⊗ P ⟶ P)

private abbrev fibreProjection {S' : Scheme.{u}} (b : S' ⟶ S) (V : Over S) :
    (Over.map b).obj ((Over.pullback b).obj V) ⟶ V :=
  (Over.mapPullbackAdj b).counit.app V

/-- The action applied to the two projections of a product over the field. -/
private def fibreAction {S' : Scheme.{u}} (q : X ⟶ P) (b : S' ⟶ S) :
    (Over.map b).obj (((changeBase b).obj G).X ⊗ (Over.pullback b).obj X) ⟶ P :=
  let G' := ((changeBase b).obj G).X
  let X' := (Over.pullback b).obj X
  let J := Over.map b
  actRightQuotient m (J.map (fst G' X') ≫ fibreProjection b G.X)
    (J.map (snd G' X') ≫ fibreProjection b X ≫ q)

set_option backward.isDefEq.respectTransparency false in
private theorem fibreAction_eval {S' : Scheme.{u}} (q : X ⟶ P) (b : S' ⟶ S)
    {T : Over S'} (g : T ⟶ ((changeBase b).obj G).X) (x : T ⟶ (Over.pullback b).obj X) :
    (Over.map b).map (lift g x) ≫ fibreAction m q b =
      actRightQuotient m (unbasePoint b T G g) ((Over.map b).map x ≫ fibreProjection b X ≫ q) := by
  simp only [fibreAction, comp_actRightQuotient, ← Category.assoc, ← Functor.map_comp, lift_fst, lift_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem quotientFibreIrreducible [GeometricallyConnected G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] {k : Type u} [Field k]
    (b : ringSpec k ⟶ S) :
    IrreducibleSpace (((changeBase b).obj G).X.left) := by
  let H := (changeBase b).obj G
  have : GeometricallyConnected H.X.hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd G.X.hom b))
  have : LocallyOfFiniteType H.X.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have : QuasiCompact H.X.hom := inferInstanceAs
    (QuasiCompact (pullback.snd G.X.hom b))
  exact irreducible_of_geometricallyConnected H

set_option backward.isDefEq.respectTransparency false in
private theorem fibreAction_goodSomewhere [Surjective p.left]
    (hm : ∀ {T : Over S} (g x : T ⟶ G.X), lift g (x ≫ p) ≫ m = (g * x) ≫ p)
    (q : X ⟶ P) {k : Type u} [Field k] (b : ringSpec k ⟶ S)
    (U : P.left.Opens) (hU : (1 ≫ p : 𝟙_ (Over S) ⟶ P).left
      (b (IsLocalRing.closedPoint k)) ∈ U)
    (x : ((Over.pullback b).obj X).left) :
    ∃ t : (((changeBase b).obj G).X ⊗ (Over.pullback b).obj X).left,
      (snd ((changeBase b).obj G).X ((Over.pullback b).obj X)).left t = x ∧ (fibreAction m q b).left t ∈ U := by
  let J := Over.map b
  let F := Over.pullback b
  let E := Over.mapPullbackAdj b
  let L := pullback (F.map p) (F.map q)
  let g : L ⟶ ((changeBase b).obj G).X := pullback.fst _ _
  let r : L ⟶ F.obj X := pullback.snd _ _
  have hp : Surjective (F.map p).left := of_isPullback (pullbackMapSquare b p).flip ‹Surjective p.left›
  have hr : Surjective r.left := of_isPullback ((IsPullback.of_hasPullback (F.map p) (F.map q)).map
    (CategoryTheory.Over.forget _)) hp
  obtain ⟨l, hl⟩ := r.left.surjective x
  let t := lift (g⁻¹) r
  refine ⟨t.left l, ?_, ?_⟩
  · have he := congrArg (fun a : L ⟶ F.obj X ↦ a.left l) (lift_snd (g⁻¹) r)
    exact he.trans hl
  · have h : unbasePoint b L G g ≫ p = (J.map r ≫ fibreProjection b X) ≫ q := by
      have h' := congrArg ((E.homEquiv L P).symm) (pullback.condition (f := F.map p) (g := F.map q))
      rw [E.homEquiv_naturality_right_symm, E.homEquiv_naturality_right_symm] at h'
      exact h'
    rw [Category.assoc] at h
    have ha : J.map t ≫ fibreAction m q b = (1 : J.obj L ⟶ G.X) ≫ p := by
      rw [fibreAction_eval, ← h, map_inv]
      change lift (unbasePoint b L G g)⁻¹ (unbasePoint b L G g ≫ p) ≫ m = _
      rw [hm, inv_mul_cancel]
    have he := congrArg (fun a : J.obj L ⟶ P ↦ a.left l) ha
    change (fibreAction m q b).left (t.left l) = ((1 : J.obj L ⟶ G.X) ≫ p).left l at he
    rw [he]
    have h₁ : (1 : J.obj L ⟶ G.X) = toUnit _ ≫ (1 : 𝟙_ (Over S) ⟶ G.X) :=
      (MonObj.comp_one _).symm
    rw [h₁, Category.assoc, Over.comp_left, Scheme.Hom.comp_apply]
    change ((1 : 𝟙_ (Over S) ⟶ G.X) ≫ p).left (b (L.hom l)) ∈ U
    rw [show L.hom l = IsLocalRing.closedPoint k from Subsingleton.elim _ _]
    exact hU

set_option backward.isDefEq.respectTransparency false in
private theorem existsGoodFibreTranslation [Surjective p.left]
    [GeometricallyConnected G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType X.hom]
    (hm : ∀ {T : Over S} (g x : T ⟶ G.X), lift g (x ≫ p) ≫ m = (g * x) ≫ p)
    (q : X ⟶ P) {k : Type u} [Field k] (b : ringSpec k ⟶ S)
    (U : P.left.Opens) (hU : (1 ≫ p : 𝟙_ (Over S) ⟶ P).left
      (b (IsLocalRing.closedPoint k)) ∈ U)
    (Z : Set ((Over.pullback b).obj X).left) (hZ : Z.Finite) (hZc : ∀ x ∈ Z, IsClosed {x}) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (g : coordSpec k K ⟶ ((changeBase b).obj G).X),
      ∀ t : (((changeBase b).obj G).X ⊗ (Over.pullback b).obj X).left,
        (fst ((changeBase b).obj G).X ((Over.pullback b).obj X)).left t =
          g.left (IsLocalRing.closedPoint K) →
        (snd ((changeBase b).obj G).X ((Over.pullback b).obj X)).left t ∈ Z →
        (fibreAction m q b).left t ∈ U := by
  let H := (changeBase b).obj G
  let Y := (Over.pullback b).obj X
  have : LocallyOfFiniteType H.X.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have : QuasiCompact H.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom b))
  have : GeometricallyConnected H.X.hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd G.X.hom b))
  have : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom b))
  have : IrreducibleSpace H.X.left := quotientFibreIrreducible (G := G) b
  let U' := (fibreAction m q b).left ⁻¹ᵁ U
  obtain ⟨x, hClosed, hx⟩ := existsClosedPointForOpenConditions H.X.hom Y.hom
    (fun K _ a ↦ quotientFibreIrreducible (G := H) a) U' Z hZ hZc
    (fun y _ ↦ fibreAction_goodSomewhere p m hm q b U hU y)
  let K := H.X.left.residueField x
  let h := H.X.left.fromSpecResidueField x
  let a := Spec.preimage (h ≫ H.X.hom)
  have hf : IsFinite (h ≫ H.X.hom) := finiteFieldMapOfClosedPoint H.X.hom x hClosed
  have ha : Spec.map a = h ≫ H.X.hom := Spec.map_preimage _
  let : Algebra k K := a.hom.toAlgebra
  have hF : Module.Finite k K := by
    change a.hom.Finite
    exact (IsFinite.SpecMap_iff a).mp (ha.symm ▸ hf)
  let g : coordSpec k K ⟶ H.X := Over.homMk h ha.symm
  refine ⟨K, _, _, hF, g, fun t ht ht' ↦ hx t ?_ ht'⟩
  exact ht.trans (Scheme.fromSpecResidueField_apply x _)

end FibreTranslation

section TranslatedAffineOpens

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (X : Over S) {L : Over S'} {C : Over S}

private def fibreCoverMap (r : (Over.map b).obj L ⟶ C) :
    (Over.map b).obj ((Over.pullback b).obj X ⊗ L) ⟶ X ⊗ C :=
  lift ((Over.map b).map (fst _ _) ≫ fibreProjection b X)
    ((Over.map b).map (snd _ _) ≫ r)

private theorem fibreCoverMap_fst (r : (Over.map b).obj L ⟶ C) :
    fibreCoverMap b X r ≫ fst _ _ =
      (Over.map b).map (fst ((Over.pullback b).obj X) L) ≫ fibreProjection b X := lift_fst _ _

private theorem fibreCoverMap_snd (r : (Over.map b).obj L ⟶ C) :
    fibreCoverMap b X r ≫ snd _ _ = (Over.map b).map (snd ((Over.pullback b).obj X) L) ≫ r :=
  lift_snd _ _

set_option backward.isDefEq.respectTransparency false in
private theorem fibreCoverMap_isPullback (r : (Over.map b).obj L ⟶ C) :
    IsPullback (fibreCoverMap b X r).left (snd ((Over.pullback b).obj X) L).left
      (snd X C).left r.left := by
  let p := pullback.fst X.hom b
  let q := pullback.snd X.hom b
  let s := (snd ((Over.pullback b).obj X) L).left
  let t := (fst X C).left
  have h₀ : r.left ≫ C.hom = L.hom ≫ b := Over.w r
  have h₁ : (fibreCoverMap b X r).left ≫ t = pullback.fst q L.hom ≫ p :=
    congrArg Over.Hom.left (fibreCoverMap_fst b X r)
  have h₂ : (fibreCoverMap b X r).left ≫ (snd X C).left = s ≫ r.left :=
    congrArg Over.Hom.left (fibreCoverMap_snd b X r)
  have hp := (IsPullback.of_hasPullback q L.hom).paste_horiz (IsPullback.of_hasPullback X.hom b)
  apply IsPullback.of_right (h₁₂ := t) (v₁₃ := X.hom) (h₂₂ := C.hom) ?_ h₂
    (IsPullback.of_hasPullback X.hom C.hom)
  rw [h₁, h₀]
  exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem finiteClosedSpecializationsOnFibre {k : Type u} [Field k] {S : Scheme.{u}}
    (b : ringSpec k ⟶ S) (X : Over S) [LocallyOfFiniteType X.hom] (Z : Set X.left) (hZ : Z.Finite)
    (hZb : Z ⊆ X.hom ⁻¹' Set.range b) :
    ∃ W : Set ((Over.pullback b).obj X).left, W.Finite ∧ (∀ y ∈ W, IsClosed {y}) ∧
      ∀ z ∈ Z, ∃ y ∈ W, z ⤳ (fibreProjection b X).left y := by
  classical
  let Y := (Over.pullback b).obj X
  let j := (fibreProjection b X).left
  have : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd X.hom b))
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have h (z : Z) : ∃ y : Y.left, IsClosed {y} ∧ z.val ⤳ j y := by
    have hz : z.val ∈ Set.range j := (Scheme.Pullback.range_fst (f := X.hom) (g := b)).symm ▸
      hZb z.property
    obtain ⟨x, hx⟩ := hz
    have hn : (closure ({x} : Set Y.left)).Nonempty :=
      ⟨x, subset_closure (Set.mem_singleton x)⟩
    obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hn isClosed_closure.isLocallyClosed
    exact ⟨y, hc, hx ▸ (specializes_iff_mem_closure.mpr hy).map j.continuous⟩
  choose y hyc hy using h
  let : Finite Z := hZ.to_subtype
  refine ⟨Set.range y, Set.finite_range y, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact hyc z
  · intro z hz
    exact ⟨y ⟨z, hz⟩, Set.mem_range_self _, hy ⟨z, hz⟩⟩

variable {G : Grp (Over S)} {P A : Over S} (p : G.X ⟶ P) (m : G.X ⊗ P ⟶ P)
  [Flat p.left] [Surjective p.left]
  (hm : ∀ {T : Over S} (g x : T ⟶ G.X), lift g (x ≫ p) ≫ m = (g * x) ≫ p)

include hm in
set_option backward.isDefEq.respectTransparency false in
private theorem translatedAffineOpenOnCover [IsAffineHom A.hom] [IsAffineHom C.hom]
    {k K : Type u} [Field k] [Field K] [Algebra k K] (b : ringSpec k ⟶ S)
    (g : coordSpec k K ⟶ ((changeBase b).obj G).X)
    (r : (Over.map b).obj (coordSpec k K) ⟶ C) (g' : C ⟶ G.X)
    (hr : r ≫ g' = unbasePoint b _ G g)
    (U : P.left.Opens) (hU : IsAffineOpen U) (Z : Set ((Over.pullback b).obj (P ⊗ A)).left)
    (hgood : ∀ t : (((changeBase b).obj G).X ⊗ (Over.pullback b).obj (P ⊗ A)).left,
      (fst ((changeBase b).obj G).X ((Over.pullback b).obj (P ⊗ A))).left t =
        g.left (IsLocalRing.closedPoint K) →
      (snd ((changeBase b).obj G).X ((Over.pullback b).obj (P ⊗ A))).left t ∈ Z →
      (fibreAction m (fst P A) b).left t ∈ U) :
    ∃ O : ((P ⊗ A) ⊗ C).left.Opens, IsAffineOpen O ∧
      ∀ t : ((Over.pullback b).obj (P ⊗ A) ⊗ coordSpec k K).left,
        (fst ((Over.pullback b).obj (P ⊗ A)) (coordSpec k K)).left t ∈ Z →
          (fibreCoverMap b (P ⊗ A) r).left t ∈ O := by
  let X := P ⊗ A
  let Y := (Over.pullback b).obj X
  let L := coordSpec k K
  let φ := fibreCoverMap b X r
  let f := fst X C ≫ fst P A
  let e := translatedProductIso m hm (A := A) g'
  have : IsAffineHom f.left := by
    change IsAffineHom (pullback.fst X.hom C.hom ≫ pullback.fst P.hom A.hom)
    exact MorphismProperty.comp_mem _ _ _
      (MorphismProperty.pullback_fst _ _ ‹IsAffineHom C.hom›)
      (MorphismProperty.pullback_fst _ _ ‹IsAffineHom A.hom›)
  let U' := e.hom.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  have : IsIso e.hom.left := (CategoryTheory.Over.forget S).map_isIso e.hom
  refine ⟨U', (hU.preimage f.left).preimage_of_isIso e.hom.left, fun t ht ↦ ?_⟩
  let l := lift (snd Y L ≫ g) (fst Y L)
  have hC : φ ≫ snd X C ≫ g' =
      unbasePoint b (Y ⊗ L) G (snd Y L ≫ g) := by
    rw [← Category.assoc, fibreCoverMap_snd, Category.assoc, hr]
    exact ((Over.mapPullbackAdj b).homEquiv_naturality_left_symm (snd Y L) g).symm
  have hP : φ ≫ fst X C ≫ fst P A =
      (Over.map b).map (fst Y L) ≫ fibreProjection b X ≫ fst P A := by
    rw [← Category.assoc, fibreCoverMap_fst, Category.assoc]
  have hact : φ ≫ e.hom ≫ f = (Over.map b).map l ≫ fibreAction m (fst P A) b := by
    change φ ≫ translatedProductMap m g' ≫ fst X C ≫ fst P A = _
    rw [translatedProductMap_P, comp_actRightQuotient, hC, hP, fibreAction_eval]
  have hfst : (fst ((changeBase b).obj G).X Y).left (l.left t) =
      g.left (IsLocalRing.closedPoint K) := by
    have h := congrArg (fun z : Y ⊗ L ⟶ ((changeBase b).obj G).X ↦ z.left t)
      (lift_fst (snd Y L ≫ g) (fst Y L))
    change _ = g.left ((snd Y L).left t) at h
    have he : (snd Y L).left t = IsLocalRing.closedPoint K :=
      @Subsingleton.elim (ringSpec K) inferInstance _ _
    exact h.trans (congrArg g.left he)
  have hsnd : (snd ((changeBase b).obj G).X Y).left (l.left t) ∈ Z := by
    have h := congrArg (fun z : Y ⊗ L ⟶ Y ↦ z.left t) (lift_snd (snd Y L ≫ g) (fst Y L))
    rwa [show (snd ((changeBase b).obj G).X Y).left (l.left t) = (fst Y L).left t from h]
  have hval := congrArg (fun z : (Over.map b).obj (Y ⊗ L) ⟶ P ↦ z.left t) hact
  change f.left (e.hom.left (φ.left t)) = (fibreAction m (fst P A) b).left (l.left t) at hval
  change f.left (e.hom.left (φ.left t)) ∈ U
  rw [hval]
  exact hgood (l.left t) hfst hsnd

end TranslatedAffineOpens

/-- Adic completeness passes from the base to a finite free module by taking limits in a basis. -/
private theorem adicCompleteOfFiniteFree {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete I M := by
  let b := Module.finBasis R M
  have hmem (n : ℕ) (x : M) :
      x ∈ (I ^ n • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I ^ n := by
    constructor
    · intro hx i
      have h := Submodule.smul_top_le_comap_smul_top (I ^ n) (b.coord i) hx
      change b.coord i x ∈ (I ^ n • ⊤ : Submodule R R) at h
      rw [Ideal.smul_eq_mul, Ideal.mul_top] at h
      exact h
    · intro hx
      rw [← b.sum_repr x]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx i) Submodule.mem_top
  have hmod (n : ℕ) (x y : M) :
      x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
        ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    simp only [SModEq.sub_mem, hmem, map_sub, Finsupp.sub_apply, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [isAdicComplete_iff, isHausdorff_iff, isPrecomplete_iff]
  constructor
  · intro x hx
    apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    apply IsHausdorff.haus' (I := I)
    intro n
    simpa only [map_zero, Finsupp.zero_apply] using (hmod n x 0).mp (hx n) i
  · intro f hf
    have hh (i : _) := IsPrecomplete.prec (I := I) (M := R) inferInstance
      (f := fun n ↦ b.repr (f n) i) (fun {m n} h ↦ (hmod m (f m) (f n)).mp (hf h) i)
    choose l hl using hh
    use b.equivFun.symm l
    intro n
    apply (hmod n _ _).mpr
    intro i
    simpa only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hl i n

open Polynomial in
set_option backward.isDefEq.respectTransparency false in
/-- Lift the minimal polynomial of a primitive residue generator to obtain a finite étale algebra. -/
private theorem existsFiniteEtaleResidueLift {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [Module.Finite (IsLocalRing.ResidueField R) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B)
      (_ : Module.Free R B) (_ : Module.Finite R B) (_ : Module.FaithfullyFlat R B)
      (_ : Algebra.Etale R B) (e : (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B)) ≃+* K),
      IsAdicComplete ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) B ∧
        e.toRingHom.comp ((Ideal.Quotient.mk _).comp (algebraMap R B)) =
          (algebraMap (IsLocalRing.ResidueField R) K).comp (IsLocalRing.residue R) := by
  let k := IsLocalRing.ResidueField R
  let I := IsLocalRing.maximalIdeal R
  let := (IsLocalRing.residue R).toAlgebra
  let := ((algebraMap k K).comp (IsLocalRing.residue R)).toAlgebra
  let : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' rfl
  have : PerfectField k := PerfectField.ofFinite
  let pb := Field.powerBasisOfFiniteOfSeparable k K
  let p := minpoly k pb.gen
  have hpMon : p.Monic := minpoly.monic (IsIntegral.of_finite k pb.gen)
  have hpIrr : Irreducible p := minpoly.irreducible (IsIntegral.of_finite k pb.gen)
  obtain ⟨q, hq, hdegree, hqMon⟩ := lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (IsLocalRing.residue_surjective (R := R)) p) hpMon
  let B := AdjoinRoot q
  let J : Ideal B := I.map (algebraMap R B)
  have hBFree : Module.Free R B := hqMon.free_adjoinRoot
  have hBFinite : Module.Finite R B := hqMon.finite_adjoinRoot
  have hdeg : q.degree ≠ 0 := by
    rw [degree_eq_natDegree hqMon.ne_zero, hdegree]
    exact_mod_cast hpIrr.natDegree_pos.ne'
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr
    (AdjoinRoot.of.injective_of_degree_ne_zero hdeg)
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  have hFF : Module.FaithfullyFlat R B :=
    Module.FaithfullyFlat.of_comap_surjective (Algebra.IsIntegral.comap_surjective R B)
  have hpRoot : aeval (AdjoinRoot.root p) (minpoly k pb.gen) = 0 := by rw [← show p = minpoly k pb.gen from rfl, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  let e₁ := AdjoinRoot.equiv' p pb hpRoot (minpoly.aeval k pb.gen)
  let e₀ : (B ⧸ J) ≃ₐ[R] AdjoinRoot p := by
    change (AdjoinRoot q ⧸ I.map (AdjoinRoot.of q)) ≃ₐ[R] AdjoinRoot p
    have heq : q.map (Ideal.Quotient.mk I) = p := hq
    exact (AdjoinRoot.quotEquivQuotMap q I).trans
      (Ideal.quotientEquivAlgOfEq R (congrArg (fun t ↦ Ideal.span {t}) heq))
  let e := e₀.trans (e₁.restrictScalars R)
  let d := AdjoinRoot.mk q q.derivative
  have hd : IsUnit d := by
    by_contra hnu
    obtain ⟨M, hM, hm⟩ := Ideal.exists_le_maximal (Ideal.span {d}) (Ideal.span_singleton_ne_top hnu)
    let qM := Ideal.Quotient.mk M
    let f := qM.comp (algebraMap R B)
    have hker : RingHom.ker f = I := by
      have heq : RingHom.ker f = M.under R := by
        ext x
        exact Ideal.Quotient.eq_zero_iff_mem
      rw [heq]
      exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
        (R := R) (S := B) M)
    let g : k →+* B ⧸ M := Ideal.Quotient.lift I f fun x hx ↦ show x ∈ RingHom.ker f from hker.symm ▸ hx
    have hgf : g.comp (IsLocalRing.residue R) = f := rfl
    have hEval (s : R[X]) : (s.map (IsLocalRing.residue R)).eval₂ g (qM (AdjoinRoot.root q)) =
        qM (AdjoinRoot.mk q s) := by
      rw [eval₂_map, hgf, ← hom_eval₂]
      rw [← aeval_def, AdjoinRoot.aeval_eq]
    have hpt : p.eval₂ g (qM (AdjoinRoot.root q)) = 0 := by
      rw [← hq, hEval, AdjoinRoot.mk_self, map_zero]
    have hne := (PerfectField.separable_of_irreducible hpIrr).eval₂_derivative_ne_zero g hpt
    rw [← hq, derivative_map, hEval] at hne
    exact hne (Ideal.Quotient.eq_zero_iff_mem.mpr (hm (Ideal.subset_span (Set.mem_singleton d))))
  let P : StandardEtalePair R := ⟨q, hqMon, q.derivative, 1, 0, 1, by simp⟩
  have hEt : Algebra.Etale R B := by
    have : IsLocalization.Away d B :=
      IsLocalization.away_of_isUnit_of_bijective B (by simpa using hd) Function.bijective_id
    let l : Localization.Away d ≃ₐ[B] B := IsLocalization.algEquiv (Submonoid.powers d) _ _
    exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans (l.restrictScalars R))
  have hcomp : IsAdicComplete J B :=
    (IsAdicComplete.map_algebraMap_iff I B).mpr (adicCompleteOfFiniteFree I)
  exact ⟨B, _, _, hBFree, hBFinite, hFF, hEt, e.toRingEquiv, hcomp, by ext x; exact e.commutes x⟩

set_option backward.isDefEq.respectTransparency false in
private theorem fractionSpecMap_open {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] : IsOpenImmersion (algebraSpecMap R F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away π F := by
    change IsLocalization (Submonoid.powers π) F
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨x, n, rfl⟩
      exact isUnit_iff_ne_zero.mpr (fun e ↦ pow_ne_zero _ hπ.ne_zero
        ((IsFractionRing.injective R F) (e.trans (map_zero _).symm)))
    · intro z
      obtain ⟨⟨x, y, hy⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (mem_nonZeroDivisors_iff_ne_zero.mp hy) hπ
      refine ⟨⟨x * ↑v⁻¹, ⟨π ^ n, ⟨n, rfl⟩⟩⟩, ?_⟩
      change z * algebraMap R F (π ^ n) = algebraMap R F (x * ↑v⁻¹)
      have he : π ^ n = (↑v * π ^ n) * (↑v⁻¹ : R) := by
        rw [mul_comm (v : R), mul_assoc, Units.mul_inv, mul_one]
      nth_rw 1 [he]
      rw [map_mul, ← mul_assoc, hz, map_mul]
    · intro x y h
      obtain rfl := IsFractionRing.injective R F h
      exact ⟨1, rfl⟩
  exact IsOpenImmersion.of_isLocalization π

section AdicPointLifting

open private smoothAffineCoordinates from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

private theorem liftAffineGroupPointAdically {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {G : Grp (Over (ringSpec R))} [IsAffine G.X.left] [Smooth G.X.hom]
    (I : Ideal B) [IsAdicComplete I B] (x : coordSpec R (B ⧸ I) ⟶ G.X) :
    ∃ g : coordSpec R B ⟶ G.X, coordSpecMap (Ideal.Quotient.mkₐ R I) ≫ g = x := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of R)).mpr
    (inferInstance : IsAffine G.X.left)
  have : Algebra.Smooth R A.unop := smoothAffineCoordinates e ‹Smooth G.X.hom›
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (pointCoordinates e x)
  refine ⟨(pointCoordinates e).symm g, (pointCoordinates e).injective ?_⟩
  rw [pointCoordinates_natural, Equiv.apply_symm_apply, hg]

set_option backward.isDefEq.respectTransparency false in
private theorem liftGroupPointOnResidueCover {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
    {G : Grp (Over (ringSpec R))} [IsAffine G.X.left] [Smooth G.X.hom]
    {K : Type u} [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [Module.Finite (IsLocalRing.ResidueField R) K]
    (g : coordSpec (IsLocalRing.ResidueField R) K ⟶
      ((changeBase (residueSpecMap R)).obj G).X) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Free R C) (_ : Module.Finite R C) (_ : Module.FaithfullyFlat R C)
      (_ : Algebra.Etale R C)
      (r : (Over.map (residueSpecMap R)).obj (coordSpec (IsLocalRing.ResidueField R) K) ⟶ coordSpec R C)
      (g' : coordSpec R C ⟶ G.X),
      r ≫ g' = unbasePoint (residueSpecMap R) _ G g ∧
        ∀ c : ringSpec C, algebraSpecMap R C c = IsLocalRing.closedPoint R → c ∈ Set.range r.left := by
  let k := IsLocalRing.ResidueField R
  let b := residueSpecMap R
  let C₀ := (Over.map b).obj (coordSpec k K)
  obtain ⟨C, _, _, hFree, hFin, hFaith, hEt, e, hc, he⟩ := existsFiniteEtaleResidueLift (R := R) K
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R C)
  let a := algebraSpecMap R C
  let eSpec := Scheme.Spec.mapIso e.toCommRingCatIso.op
  have hea : eSpec.hom ≫ (coordSpec R (C ⧸ I)).hom = C₀.hom := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (C ⧸ I))) = algebraSpecMap k K ≫ b
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext he)
  let α : C₀ ≅ coordSpec R (C ⧸ I) := Over.isoMk eSpec hea
  let red := coordSpecMap (Ideal.Quotient.mkₐ R I)
  let r := α.hom ≫ red
  let x := α.inv ≫ unbasePoint b (coordSpec k K) G g
  have : IsAdicComplete I C := hc
  obtain ⟨g', hg⟩ := liftAffineGroupPointAdically I x
  refine ⟨C, _, _, hFree, hFin, hFaith, hEt, r, g', ?_, ?_⟩
  · change (α.hom ≫ red) ≫ g' = _
    rw [Category.assoc, hg, Iso.hom_inv_id_assoc]
  · intro c h
    have hIc : I ≤ c.asIdeal := by
      apply Ideal.map_le_iff_le_comap.mpr
      exact (congrArg PrimeSpectrum.asIdeal h).ge
    have hr : c ∈ Set.range red.left := by
      change c ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
      exact hIc
    obtain ⟨y, hy⟩ := hr
    have : IsIso α.hom.left := (CategoryTheory.Over.forget _).map_isIso α.hom
    obtain ⟨z, hz⟩ := α.hom.left.surjective y
    exact ⟨z, by change red.left (α.hom.left z) = c; rw [hz, hy]⟩

end AdicPointLifting

section AffineOpenInEachFibre

variable {R : Type u} [CommRing R] {G : Grp (Over (ringSpec R))}
  {P A : Over (ringSpec R)}
  (p : G.X ⟶ P) (m : G.X ⊗ P ⟶ P)
  [Flat p.left] [Surjective p.left]
  (hm : ∀ {T : Over (ringSpec R)} (g x : T ⟶ G.X), lift g (x ≫ p) ≫ m = (g * x) ≫ p)
  [GeometricallyConnected G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
  [IsAffineHom A.hom] [LocallyOfFiniteType (P ⊗ A).hom] [(P ⊗ A).left.IsSeparated]

include hm in
set_option backward.isDefEq.respectTransparency false in
private theorem commonAffineOpenOverGenericFibre [IsDomain R] [IsDiscreteValuationRing R]
    {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
    (Z : Set (P ⊗ A).left) (hZ : Z.Finite)
    (hZb : Z ⊆ (P ⊗ A).hom ⁻¹' Set.range (algebraSpecMap R F)) :
    ∃ U : (P ⊗ A).left.Opens, IsAffineOpen U ∧ Z ⊆ U := by
  let X := P ⊗ A
  let b := algebraSpecMap R F
  let Y := (Over.pullback b).obj X
  let j := (fibreProjection b X).left
  have : IsOpenImmersion b := fractionSpecMap_open
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (pullback.fst X.hom b))
  have : Y.left.IsSeparated := by
    constructor
    have e : j ≫ terminal.from X.left = terminal.from Y.left := terminal.comp_from j
    exact e ▸ MorphismProperty.comp_mem _ _ _ (inferInstance : IsSeparated j)
      (inferInstance : IsSeparated (terminal.from X.left))
  obtain ⟨W, hW, hWc, hZs⟩ := finiteClosedSpecializationsOnFibre b X Z hZ hZb
  obtain ⟨U, hU, hUb, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : P.left.Opens)) (x := (1 ≫ p : 𝟙_ (Over (ringSpec R)) ⟶ P).left
      (b (IsLocalRing.closedPoint F))) (by simp)
  obtain ⟨K, _, _, hK, g, hg⟩ := existsGoodFibreTranslation p m hm (fst P A) b U hUb W hW hWc
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  have : Algebra.Etale F K := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let L := coordSpec F K
  let C := (Over.map b).obj L
  have : IsAffine C.left := inferInstanceAs (IsAffine (ringSpec K))
  have : IsAffineHom C.hom := isAffineHom_of_isAffine _
  let g' := unbasePoint b L G g
  obtain ⟨O, hO, ho⟩ := translatedAffineOpenOnCover p m hm b g (𝟙 C) g' (Category.id_comp _)
    U hU W hg
  let r := fibreCoverMap b X (𝟙 C)
  have : IsIso r.left := (fibreCoverMap_isPullback b X (𝟙 C)).isIso_fst_of_isIso
  obtain ⟨V, hV, hv⟩ := ParameterDescent.affineNeighbourhoodOfFiniteEtaleCover
    (R := F) (C := K) W (r.left ⁻¹ᵁ O) (hO.preimage_of_isIso r.left) ho
  refine ⟨j ''ᵁ V, hV.image_of_isOpenImmersion j, fun z hz ↦ ?_⟩
  obtain ⟨w, hw, hsp⟩ := hZs z hz
  exact hsp.mem_open (j ''ᵁ V).isOpen (show j w ∈ j ''ᵁ V from ⟨w, hv hw, rfl⟩)

include hm in
set_option backward.isDefEq.respectTransparency false in
private theorem commonAffineOpenOverSpecialFibre [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
    [IsAffine G.X.left] [Smooth G.X.hom] (Z : Set (P ⊗ A).left) (hZ : Z.Finite)
    (hZb : Z ⊆ (P ⊗ A).hom ⁻¹' Set.range (residueSpecMap R)) :
    ∃ U : (P ⊗ A).left.Opens, IsAffineOpen U ∧ Z ⊆ U := by
  let X := P ⊗ A
  let k := IsLocalRing.ResidueField R
  let b := residueSpecMap R
  let Y := (Over.pullback b).obj X
  let j := (fibreProjection b X).left
  have : IsClosedImmersion b := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (IsLocalRing.residue R)) (IsLocalRing.residue_surjective (R := R))
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (pullback.fst X.hom b))
  obtain ⟨W, hW, hWc, hZs⟩ := finiteClosedSpecializationsOnFibre b X Z hZ hZb
  obtain ⟨U, hU, hUb, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : P.left.Opens)) (x := (1 ≫ p : 𝟙_ (Over (ringSpec R)) ⟶ P).left
      (b (IsLocalRing.closedPoint k))) (by simp)
  obtain ⟨K, _, _, hK, g, hg⟩ := existsGoodFibreTranslation p m hm (fst P A) b U hUb W hW hWc
  obtain ⟨B, _, _, hFree, hFin, hFaith, hEt, r, g', hr, hRange⟩ := liftGroupPointOnResidueCover g
  let C := coordSpec R B
  let L := coordSpec k K
  have : IsAffine C.left := inferInstanceAs (IsAffine (ringSpec B))
  have : IsAffineHom C.hom := isAffineHom_of_isAffine _
  obtain ⟨O, hO, ho⟩ := translatedAffineOpenOnCover p m hm b g r g' hr U hU W hg
  let φ := fibreCoverMap b X r
  have hO' : ∀ z : (X ⊗ C).left, (fst X C).left z ∈ j '' W → z ∈ O := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hz
    have hbase : C.hom ((snd X C).left z) = IsLocalRing.closedPoint R := by
      have eq := congrArg (fun a : (X ⊗ C).left ⟶ ringSpec R ↦ a z)
        ((Over.w (snd X C)).trans (Over.w (fst X C)).symm)
      change C.hom ((snd X C).left z) = X.hom ((fst X C).left z) at eq
      rw [eq, ← hwz]
      have hwbase := congrArg (fun a : Y.left ⟶ ringSpec R ↦ a w)
        (Over.w (fibreProjection b X))
      change X.hom (j w) = b (Y.hom w) at hwbase
      exact hwbase.trans (IsLocalRing.PrimeSpectrum.comap_residue R (Y.hom w))
    obtain ⟨c, hc⟩ := hRange ((snd X C).left z) hbase
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback
      (fibreCoverMap_isPullback b X r) z c hc.symm
    have hft : j ((fst Y L).left t) = (fst X C).left z := by
      have he := congrArg (fun f : (Over.map b).obj (Y ⊗ L) ⟶ X ↦ f.left t) (fibreCoverMap_fst b X r)
      change (fst X C).left (φ.left t) = j ((fst Y L).left t) at he
      exact he.symm.trans (congrArg (fst X C).left ht)
    have hwt : (fst Y L).left t = w := j.injective (hft.trans hwz.symm)
    exact ht ▸ ho t (hwt.symm ▸ hw)
  obtain ⟨V, hV, hV'⟩ := ParameterDescent.affineNeighbourhoodOfFiniteEtaleCover
    (R := R) (C := B) (j '' W) O hO hO'
  refine ⟨V, hV, fun z hz ↦ ?_⟩
  obtain ⟨w, hw, hsp⟩ := hZs z hz
  exact hsp.mem_open V.isOpen (hV' ⟨w, hw, rfl⟩)

end AffineOpenInEachFibre

set_option backward.isDefEq.respectTransparency false in
private theorem dvrPointInSpecialOrGeneric {R F : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (s : ringSpec R) : s ∈ Set.range (residueSpecMap R) ∨ s ∈ Set.range (algebraSpecMap R F) := by
  by_cases he : s.asIdeal = ⊥
  · refine Or.inr ⟨(⊥ : PrimeSpectrum F), PrimeSpectrum.ext ?_⟩
    change Ideal.comap (algebraMap R F) (⊥ : Ideal F) = s.asIdeal
    rw [he, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R F)
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmax : IsLocalRing.maximalIdeal R ≠ ⊥ := by
      rw [hπ.maximalIdeal_eq]
      intro e
      exact hπ.ne_zero (show π ∈ (⊥ : Ideal R) from e ▸ Ideal.subset_span (Set.mem_singleton π))
    have h := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance).2
    have hS : s.asIdeal = IsLocalRing.maximalIdeal R :=
      h.unique ⟨he, inferInstance⟩ ⟨hmax, inferInstance⟩
    refine Or.inl ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
    change PrimeSpectrum.comap (IsLocalRing.residue R) _ = s
    rw [IsLocalRing.PrimeSpectrum.comap_residue]
    exact PrimeSpectrum.ext hS.symm

section SmoothBorelScheme

open Specs.IntegralSemisimpleModel (Integers integerAlgebra)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
private theorem commonAffineOpenOnSplitFlag {R A F : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
    [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
    [CommRing A] [Algebra R A] [Module.Finite R A] {G B : Grp (Over (ringSpec R))}
    [IsAffine G.X.left] [Smooth G.X.hom] [GeometricallyConnected G.X.hom] [QuasiCompact G.X.hom]
    {P : Over (ringSpec R)} [Smooth P.hom] [IsSeparated P.hom]
    (p : G.X ⟶ P) [Smooth p.left] [Surjective p.left] [QuasiCompact p.left]
    (j : B ⟶ G)
    (hq : ∀ (T : Over (ringSpec R)) (x y : T ⟶ G.X),
      x ≫ p = y ≫ p ↔ ∃ b : T ⟶ B.X, x * (b ≫ j.hom.hom) = y)
    (Z : Set ((Over.pullback (algebraSpecMap R A)).obj P).left) (hZ : Z.Finite)
    (hF : ∃ s : ringSpec R, ∀ z ∈ Z,
      (((Over.pullback (algebraSpecMap R A)).obj P).hom ≫ algebraSpecMap R A) z = s) :
    ∃ U : ((Over.pullback (algebraSpecMap R A)).obj P).left.Opens, IsAffineOpen U ∧ Z ⊆ U := by
  let C := coordSpec R A
  let X := P ⊗ C
  have : IsAffine C.left := inferInstanceAs (IsAffine (ringSpec A))
  have hC : IsAffineHom C.hom := isAffineHom_of_isAffine _
  have hp : IsAffineHom (fst P C).left := MorphismProperty.pullback_fst _ _ hC
  have : Flat p.left := inferInstance
  have hGFT : LocallyOfFiniteType G.X.hom := inferInstance
  let Z₀ : Set X.left := Z
  have hZ₀ : Z₀.Finite := hZ
  change ∃ U : X.left.Opens, IsAffineOpen U ∧ Z₀ ⊆ (U : Set X.left)
  have hFin : IsFinite C.hom := (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R A))).mpr
    (RingHom.finite_algebraMap.mpr ‹Module.Finite R A›)
  have hfin : IsFinite (fst P C).left := MorphismProperty.pullback_fst _ _ hFin
  have hX : LocallyOfFiniteType X.hom :=
    MorphismProperty.comp_mem _ _ _ (inferInstance : LocallyOfFiniteType (fst P C).left)
      (inferInstance : LocallyOfFiniteType P.hom)
  have hsep : IsSeparated X.hom :=
    MorphismProperty.comp_mem _ _ _ (inferInstance : IsSeparated (fst P C).left)
      (inferInstance : IsSeparated P.hom)
  have : X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from X.hom]
    exact MorphismProperty.comp_mem _ _ _ hsep inferInstance
  obtain ⟨s, hs⟩ := hF
  have hw : (pullback.snd P.hom (algebraSpecMap R A) ≫ algebraSpecMap R A) = X.hom :=
    Over.w (snd P C)
  have hbase (z : X.left) (hz : z ∈ Z₀) : X.hom z = s := by
    rw [← hw]
    exact hs z hz
  obtain ⟨m, hm⟩ := existsRightQuotientAction p j hq
  rcases dvrPointInSpecialOrGeneric (F := F) s with h | h
  · have he : Z₀ ⊆ X.hom ⁻¹' Set.range (residueSpecMap R) := by
      intro z hz
      change X.hom z ∈ Set.range (residueSpecMap R)
      rw [hbase z hz]
      exact h
    exact commonAffineOpenOverSpecialFibre (G := G) (P := P) (A := C) p m hm Z₀ hZ₀ he
  · have he : Z₀ ⊆ X.hom ⁻¹' Set.range (algebraSpecMap R F) := by
      intro z hz
      change X.hom z ∈ Set.range (algebraSpecMap R F)
      rw [hbase z hz]
      exact h
    exact commonAffineOpenOverGenericFibre (G := G) (P := P) (A := C) (F := F) p m hm Z₀ hZ₀ he

set_option backward.isDefEq.respectTransparency false in
private theorem integralSpecMap_comp_algebraSpecMap {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] : algebraSpecMap R A ≫ integralSpecMap R = integralSpecMap A := by
  let := integerAlgebra R
  let := integerAlgebra A
  change Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} R)) =
      Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} A))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext x
  exact map_intCast (algebraMap R A) x.down

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
/-- The given integral group has a smooth parameter scheme for its Borel
families, with the universal subgroup in the original model. -/
theorem smoothBorelParameter : Statement.{u} := by
  intro R _ _ _ _ _ F _ _ _ _ G _ _ _ _ _ _ hG
  have hSplit := hG
  obtain ⟨A, _, _, hFinite, hFaith, hEt, D, _, M, ⟨e⟩⟩ := hG
  have : IsAffine M.group.X.left := M.affine
  have : IsAffineHom M.group.X.hom := isAffineHom_of_isAffine _
  have : LocallyOfFinitePresentation M.group.X.hom := M.locallyOfFinitePresentation
  have : QuasiCompact M.group.X.hom := M.quasiCompact
  have : Smooth M.group.X.hom := M.smooth
  have : GeometricallyConnected M.group.X.hom := M.connected
  obtain ⟨B, j, hj, hs, P, p, U, hB, hP, hp, hpSurj, hpQC, hFree, hU, hUp, hq, c, hc⟩ :=
    integralBorelQuotientWithCocharacter M
  obtain ⟨E, hE, ⟨eB⟩⟩ := hFree
  have hrep := splitQuotient_represents j hj hs eB hB
    (fun k _ _ a ↦ integralFibre_isReductive M k a) c hc p U hUp hq
  have hsep : IsSeparated P.hom := separatedRightQuotient p j hj hq
  let z := integralSpecMap R
  let a := algebraSpecMap R A
  let H := (changeBase z).obj M.group
  let P₀ := (Over.pullback z).obj P
  let P' := (Over.pullback a).obj P₀
  let p₀ := (Over.pullback z).map p
  let j₀ := (changeBase z).map j
  have hlft : LocallyOfFinitePresentation H.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd M.group.X.hom z))
  have hQC : QuasiCompact H.X.hom := inferInstanceAs (QuasiCompact (pullback.snd M.group.X.hom z))
  have hSmooth : Smooth H.X.hom := inferInstanceAs (Smooth (pullback.snd M.group.X.hom z))
  have hConn : GeometricallyConnected H.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd M.group.X.hom z))
  have hAff : IsAffineHom H.X.hom := inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom z))
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have hp₀ : Smooth p₀.left := MorphismProperty.of_isPullback (pullbackMapSquare z p).flip hp
  have hp₀S : Surjective p₀.left := MorphismProperty.of_isPullback (pullbackMapSquare z p).flip hpSurj
  have hp₀Q : QuasiCompact p₀.left := MorphismProperty.of_isPullback (pullbackMapSquare z p).flip hpQC
  have hP₀ : Smooth P₀.hom := inferInstanceAs (Smooth (pullback.snd P.hom z))
  have hsep₀ : IsSeparated P₀.hom := inferInstanceAs (IsSeparated (pullback.snd P.hom z))
  have hP' : Smooth P'.hom := inferInstanceAs (Smooth (pullback.snd P₀.hom a))
  have hsep' : IsSeparated P'.hom := inferInstanceAs (IsSeparated (pullback.snd P₀.hom a))
  have hq₀ := rightQuotientRelation_pullback z p j hq
  have hCommon := commonAffineOpenOnSplitFlag (A := A) (F := F)
    (G := H) (B := (changeBase z).obj B) (P := P₀) p₀ j₀ hq₀
  let d := (changeBaseComp a z).symm.app M.group ≪≫
    changeBaseCongr (integralSpecMap_comp_algebraSpecMap (R := R) (A := A)) M.group
  let φ := e ≪≫ d.symm
  let U₀ := relativeFamily z (U.pullback (fibreProjection z P))
  let V := relativeFamily a (U₀.pullback (fibreProjection a P₀))
  have hU₀ : IsBorelFamily U₀ :=
    (relativeFamily_isBorel z _).mpr (isBorelFamily_pullback U hU (fibreProjection z P))
  have hV : IsBorelFamily V :=
    (relativeFamily_isBorel a _).mpr (isBorelFamily_pullback U₀ hU₀ (fibreProjection a P₀))
  let U' := changeFamilyGroup φ.symm V
  have hU' : IsBorelFamily U' := (changeFamilyGroup_isBorel φ.symm V).mpr hV
  have hrep₀ := representsBorelFamilies_pullback z U hrep
  have hrepV := representsBorelFamilies_pullback a U₀ hrep₀
  have hrep' := representsBorelFamilies_changeGroup φ.symm V hrepV
  exact presentationOfCommonAffineNeighbourhoods hSplit P' U' hP' hsep' hU' hrep' hCommon

end SmoothBorelScheme

end

end LinearAlgebraicGroups.Arithmetic.SmoothBorelParameter
