import Specs.LinearAlgebraicGroups.Descent.SmoothTorsors
import LinearAlgebraicGroups.Descent.AffineTorsorDescent
import LinearAlgebraicGroups.Descent.NonabelianCohomology
import LinearAlgebraicGroups.Descent.SmoothPoint
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.RootsOfUnity.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Descent.SmoothTorsors

open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup)
open Specs.Fppf Specs.SmoothTorsors NonabelianCohomology

noncomputable section

open private restriction_ker from LinearAlgebraicGroups.Descent.NonabelianCohomology
open private chart_cover covers_singleton field_extension_fppf fieldHom_left
  from LinearAlgebraicGroups.Descent.AffineTorsorDescent

set_option backward.isDefEq.respectTransparency false

/-- The affine smooth representative acquires a point after extension to a
separable closure. -/
theorem geometricPoint : GeometricPoint.{u} := by
  intro k S _ _ _ _ H P hH
  obtain ⟨X, a, ⟨e⟩, hX, _, _, hqc, hsmooth⟩ :=
    Fppf.affineTorsorRepresentability H P
  let q : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k) := (fieldExtensionTest k S).left.hom
  let f₀ : X.left.left ⟶ Spec (CommRingCat.of k) := X.left.hom
  have hf₀ : X.hom.left = f₀ := fieldHom_left k X
  let : Smooth f₀ := hf₀ ▸ hsmooth hH
  let : QuasiCompact f₀ := hf₀ ▸ hqc
  let : Nonempty X.left.left := hX
  let : IsSepClosed S := IsSepClosure.sep_closed k
  have hpull : Nonempty ↑(pullback f₀ q) := inferInstance
  obtain ⟨s, hs⟩ := exists_rational_point_of_smooth (pullback.snd f₀ q) hpull
  let f : (fieldExtensionTest k S).left ⟶ X.left :=
    Over.homMk (s ≫ pullback.fst f₀ q) (by
      change (s ≫ pullback.fst f₀ q) ≫ f₀ = q
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp])
  let f' : fieldExtensionTest k S ⟶ X :=
    Over.homMk f (Over.mkIdTerminal.hom_ext _ _)
  exact ⟨e.iso.hom.hom.app (op (fieldExtensionTest k S)) ⟨f'⟩⟩

section Cocycles

variable {k S : Type u} [Field k] [Field S] [Algebra k S]
  {H : GroupScheme k} (P : FppfTorsor (fieldBase k) H)

private theorem restrict_comp {U V W : Over (fieldBase k)} (f : V ⟶ U)
    (g : W ⟶ V) (p : P.val.Section U) :
    P.val.res g (P.val.res f p) = P.val.res (g ≫ f) p := by
  symm
  change P.val.sheaf.obj.map (g ≫ f).op p = _
  rw [op_comp, Functor.map_comp]
  rfl

@[simp] private theorem fieldExtensionAut_mul (σ τ : S ≃ₐ[k] S) :
    fieldExtensionAut k S (σ * τ) = fieldExtensionAut k S σ ≫ fieldExtensionAut k S τ := by
  apply Over.OverMorphism.ext
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (σ * τ).toAlgHom).op =
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom τ.toAlgHom).op
  rw [← Functor.map_comp]
  rfl

private theorem res_act (σ : S ≃ₐ[k] S) (p : P.val.Section (fieldExtensionTest k S))
    (b : NonabelianCohomology.Points k S H.X) :
    P.val.res (fieldExtensionAut k S σ) (P.val.act p ⟨b⟩) =
      P.val.act (P.val.res (fieldExtensionAut k S σ) p) ⟨pointAction k S H.X σ b⟩ :=
  P.val.map_act _ _ _

private def displacement (p q : P.val.Section (fieldExtensionTest k S)) : NonabelianCohomology.Points k S H.X :=
  ((Equiv.ofBijective _ (P.property.1 _ p)).symm q).down

private theorem act_displacement (p q : P.val.Section (fieldExtensionTest k S)) :
    P.val.act p ⟨displacement P p q⟩ = q :=
  (Equiv.ofBijective _ (P.property.1 _ p)).apply_symm_apply q

private theorem displacement_cocycle (p : P.val.Section (fieldExtensionTest k S))
    (σ τ : S ≃ₐ[k] S) :
    displacement P p (P.val.res (fieldExtensionAut k S (σ * τ)) p) =
      displacement P p (P.val.res (fieldExtensionAut k S σ) p) *
        pointAction k S H.X σ (displacement P p (P.val.res (fieldExtensionAut k S τ) p)) := by
  apply ULift.up_injective
  apply (P.property.1 _ p).injective
  rw [act_displacement, fieldExtensionAut_mul, ← restrict_comp]
  nth_rw 1 [← act_displacement P p (P.val.res (fieldExtensionAut k S τ) p)]
  rw [res_act]
  nth_rw 1 [← act_displacement P p (P.val.res (fieldExtensionAut k S σ) p)]
  exact P.val.act_mul _ _ _

private theorem cocycle_change_point
    {p q : P.val.Section (fieldExtensionTest k S)} {a b : GaloisCocycle (S := S) H}
    (ha : IsCocycleOf P p a) (hb : IsCocycleOf P q b) :
    ∃ t : NonabelianCohomology.Points k S H.X, ∀ σ, b σ = t⁻¹ * a σ * pointAction k S H.X σ t := by
  let t := displacement P p q
  have hq : P.val.act p ⟨t⟩ = q := act_displacement P p q
  refine ⟨t, fun σ ↦ ?_⟩
  have e := (hb σ).symm
  rw [← hq, res_act, ha σ, P.val.act_mul, P.val.act_mul] at e
  have he : t * b σ = a σ * pointAction k S H.X σ t :=
    congrArg ULift.down ((P.property.1 _ p).injective e)
  calc
    b σ = t⁻¹ * (t * b σ) := by simp
    _ = t⁻¹ * a σ * pointAction k S H.X σ t := by rw [he, mul_assoc]

private theorem equivariant_restrict {Q : SchemeAction (fieldBase k) H}
    (e : RightActionIso Q P.val) {T U : Over (fieldBase k)} (f : U ⟶ T)
    (x : Q.Section T) :
    P.val.res f (e.iso.hom.hom.app (op T) x) =
      e.iso.hom.hom.app (op U) (Q.res f x) := by
  exact (congrArg (fun t : Q.Section T ⟶ P.val.Section U ↦ t x)
    (e.iso.hom.hom.naturality f.op)).symm

/-- Finite type bounds the field of definition of a torsor section. -/
theorem finitePoint : FinitePoint.{u} := by
  classical
  intro k S _ _ _ _ H₀ P₀ p
  obtain ⟨X, a, ⟨e⟩, _, hA, hft, _, _⟩ := Fppf.affineTorsorRepresentability H₀ P₀
  obtain ⟨q, rfl⟩ := (Iso.toEquiv
    ((evaluation _ _).obj (op (fieldExtensionTest k S)) |>.mapIso
      ((sheafToPresheaf _ _).mapIso e.iso))).surjective p
  let : IsAffine X.left.left := hA
  let f₀ : X.left.left ⟶ Spec (CommRingCat.of k) := X.left.hom
  have hf₀ : X.hom.left = f₀ := fieldHom_left k X
  let : LocallyOfFiniteType f₀ := hf₀ ▸ hft
  let A := Γ(X.left.left, ⊤)
  let i : Spec A ≅ X.left.left := X.left.left.isoSpec.symm
  let f : CommRingCat.of k ⟶ A := Spec.preimage (i.hom ≫ f₀)
  have hf : Spec.map f = i.hom ≫ f₀ := Spec.map_preimage _
  let : Algebra k A := f.hom.toAlgebra
  have hfin : Algebra.FiniteType k A := by
    apply RingHom.finiteType_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := f)).mp
    rw [hf]
    infer_instance
  let t : Spec (CommRingCat.of S) ⟶ X.left.left := q.down.left.left
  let φ : A ⟶ CommRingCat.of S := Spec.preimage (t ≫ i.inv)
  have hφ : Spec.map φ ≫ i.hom = t := by rw [Spec.map_preimage, Category.assoc, i.inv_hom_id, Category.comp_id]
  have ht : t ≫ f₀ = Spec.map (CommRingCat.ofHom (algebraMap k S)) := (Over.w q.down.left).trans (algSpec_obj_hom _)
  have hcomp : f ≫ φ = CommRingCat.ofHom (algebraMap k S) := by
    apply Spec.map_inj.mp
    rw [Spec.map_comp, hf, ← Category.assoc, hφ]
    exact ht
  let g : A →ₐ[k] S :=
    { __ := φ.hom
      commutes' := fun x ↦ congrArg (fun t : CommRingCat.of k ⟶ CommRingCat.of S ↦ t x) hcomp }
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  have : Finite (↑(s.image g) : Set S) := (s.image g).finite_toSet.to_subtype
  let L := FiniteGaloisIntermediateField.adjoin k (↑(s.image g) : Set S)
  have hle : Algebra.adjoin k (s : Set A) ≤ L.toIntermediateField.toSubalgebra.comap g := by
    apply Algebra.adjoin_le
    intro x hx
    exact FiniteGaloisIntermediateField.subset_adjoin k (↑(s.image g) : Set S)
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hmem (x : A) : φ x ∈ L.toIntermediateField := by
    apply hle
    rw [hs]
    trivial
  let gL : A →ₐ[k] L := g.codRestrict L.toIntermediateField.toSubalgebra hmem
  let q₀ : (fieldExtensionTest k L).left ⟶ X.left :=
    Over.homMk (Spec.map (CommRingCat.ofHom gL.toRingHom) ≫ i.hom) (by
      change (Spec.map (CommRingCat.ofHom gL.toRingHom) ≫ i.hom) ≫ f₀ =
        Spec.map (CommRingCat.ofHom (algebraMap k L))
      rw [Category.assoc, ← hf, ← Spec.map_comp]
      apply congrArg Spec.map
      ext x
      exact congrArg Subtype.val (gL.commutes x))
  let q' : fieldExtensionTest k L ⟶ X := Over.homMk q₀ (Over.mkIdTerminal.hom_ext _ _)
  let qL : (representedAction a).Section (fieldExtensionTest k L) := ⟨q'⟩
  refine ⟨L, e.iso.hom.hom.app (op (fieldExtensionTest k L)) qL, ?_⟩
  change _ = e.iso.hom.hom.app (op (fieldExtensionTest k S)) q
  rw [equivariant_restrict P₀ e]
  apply congrArg (fun x ↦ e.iso.hom.hom.app (op (fieldExtensionTest k S)) x)
  apply ULift.ext
  apply Over.OverMorphism.ext
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom L.toIntermediateField.val.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom gL.toRingHom) ≫ i.hom) = t
  rw [← Category.assoc, ← Spec.map_comp]
  exact hφ

private theorem fieldExtensionMap_comp {R T B : Type u} [CommRing R] [CommRing T] [CommRing B]
    [Algebra k R] [Algebra k T] [Algebra k B] (f : R →ₐ[k] T) (g : T →ₐ[k] B) :
    fieldExtensionMap (g.comp f) = fieldExtensionMap g ≫ fieldExtensionMap f := by
  apply Over.OverMorphism.ext
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (g.comp f)).op =
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom g).op ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op
  rw [← Functor.map_comp]
  rfl

private def affineSectionEquiv (R A : Type u) [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] :
    (fieldExtensionTest k R ⟶ fieldExtensionTest k A) ≃ (A →ₐ[k] R) where
  toFun t := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage t.left).unop.hom
  invFun := fieldExtensionMap
  left_inv t := by
    apply Over.OverMorphism.ext
    exact (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage t.left
  right_inv φ := by
    let F := algSpec.fullyFaithful (R := CommRingCat.of k)
    exact congrArg (fun ψ ↦ CommAlgCat.Hom.hom ψ.unop)
      (F.preimage_map (CommAlgCat.ofHom φ).op)

private theorem affine_chart {X : Over (fieldBase k)} (hX : IsAffine X.left.left) :
    ∃ (A : CommAlgCat k), Nonempty (fieldExtensionTest k A ≅ X) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).2 hX
  exact ⟨A.unop, ⟨Over.isoMk e (Over.mkIdTerminal.hom_ext _ _)⟩⟩

/-- Restriction to any extension field is injective on torsor points. -/
theorem pointRestrictionInjective : PointRestrictionInjective.{u} := by
  intro k R S _ _ _ _ _ H P f x y hxy
  obtain ⟨X, a, ⟨e⟩, _, hX, _, _, _⟩ := Fppf.affineTorsorRepresentability H P
  obtain ⟨A, ⟨j⟩⟩ := affine_chart hX
  let hR : (representedAction a).Section (fieldExtensionTest k R) ≃
      P.val.Section (fieldExtensionTest k R) :=
    (((evaluation _ _).obj (op (fieldExtensionTest k R))).mapIso
      ((sheafToPresheaf _ _).mapIso e.iso)).toEquiv
  obtain ⟨x', rfl⟩ := hR.surjective x
  obtain ⟨y', rfl⟩ := hR.surjective y
  apply congrArg hR
  apply ULift.ext
  have hh := hxy
  change P.val.res (fieldExtensionMap f) (e.iso.hom.hom.app (op (fieldExtensionTest k R)) x') =
    P.val.res (fieldExtensionMap f) (e.iso.hom.hom.app (op (fieldExtensionTest k R)) y') at hh
  rw [equivariant_restrict P e, equivariant_restrict P e] at hh
  let hS := (((evaluation _ _).obj (op (fieldExtensionTest k S))).mapIso
      ((sheafToPresheaf _ _).mapIso e.iso)).toEquiv
  have hrest : fieldExtensionMap f ≫ x'.down = fieldExtensionMap f ≫ y'.down :=
    congrArg ULift.down (hS.injective hh)
  rw [← cancel_mono j.inv]
  have hrest' := congrArg (· ≫ j.inv) hrest
  rw [Category.assoc, Category.assoc] at hrest'
  let x₀ := affineSectionEquiv R A (x'.down ≫ j.inv)
  let y₀ := affineSectionEquiv R A (y'.down ≫ j.inv)
  have hx₀ : fieldExtensionMap x₀ = x'.down ≫ j.inv :=
    (affineSectionEquiv R A).symm_apply_apply _
  have hy₀ : fieldExtensionMap y₀ = y'.down ≫ j.inv :=
    (affineSectionEquiv R A).symm_apply_apply _
  rw [← hx₀, ← hy₀] at hrest' ⊢
  rw [← fieldExtensionMap_comp, ← fieldExtensionMap_comp] at hrest'
  have hcomp : f.comp x₀ = f.comp y₀ := (affineSectionEquiv S A).symm.injective hrest'
  congr 1
  ext z
  exact f.injective (congrFun (congrArg DFunLike.coe hcomp) z)

/-- A fixed torsor section over a Galois extension is rational. -/
theorem fixedPoint : FixedPoint.{u} := by
  intro k S _ _ _ _ H P p hp
  obtain ⟨X, a, ⟨e⟩, _, hX, _, _, _⟩ := Fppf.affineTorsorRepresentability H P
  obtain ⟨A, ⟨j⟩⟩ := affine_chart hX
  let ee := (((evaluation _ _).obj (op (fieldExtensionTest k S))).mapIso
      ((sheafToPresheaf _ _).mapIso e.iso)).toEquiv
  obtain ⟨q, rfl⟩ := ee.surjective p
  let φ : A →ₐ[k] S := affineSectionEquiv S A (q.down ≫ j.inv)
  have hφ : fieldExtensionMap φ = q.down ≫ j.inv :=
    (affineSectionEquiv S A).symm_apply_apply _
  have hfix (σ : S ≃ₐ[k] S) : σ.toAlgHom.comp φ = φ := by
    apply (affineSectionEquiv S A).symm.injective
    change fieldExtensionMap (σ.toAlgHom.comp φ) = fieldExtensionMap φ
    rw [fieldExtensionMap_comp, hφ, ← Category.assoc]
    have he := hp σ
    change P.val.res (fieldExtensionAut k S σ) (e.iso.hom.hom.app (op (fieldExtensionTest k S)) q) =
      e.iso.hom.hom.app (op (fieldExtensionTest k S)) q at he
    rw [equivariant_restrict P e] at he
    exact congrArg (fun t ↦ t.down ≫ j.inv) (ee.injective he)
  let base : k →ₐ[k] S := Algebra.ofId k S
  let i := AlgEquiv.ofInjective base base.injective
  let φ₀ : A →ₐ[k] k := i.symm.toAlgHom.comp (φ.codRestrict base.range (fun x ↦
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (φ x)).mpr
      (fun σ ↦ congrArg (fun f : A →ₐ[k] S ↦ f x) (hfix σ))))
  let q₀ : (representedAction a).Section (fieldExtensionTest k k) :=
    ⟨fieldExtensionMap φ₀ ≫ j.hom⟩
  refine ⟨e.iso.hom.hom.app (op (fieldExtensionTest k k)) q₀, ?_⟩
  change _ = e.iso.hom.hom.app (op (fieldExtensionTest k S)) q
  rw [equivariant_restrict P e]
  apply congrArg (fun y ↦ e.iso.hom.hom.app (op (fieldExtensionTest k S)) y)
  apply ULift.ext
  change fieldExtensionMap base ≫ (fieldExtensionMap φ₀ ≫ j.hom) = q.down
  rw [← Category.assoc, ← fieldExtensionMap_comp]
  have h : base.comp φ₀ = φ := by
    ext x
    exact congrArg Subtype.val (i.apply_symm_apply _)
  rw [h, hφ, Category.assoc, j.inv_hom_id, Category.comp_id]

private theorem finite_point_stabilizer [IsGalois k S] (H₀ : AffineAlgebraicGroup k)
    (P₀ : FppfTorsor (fieldBase k) H₀.val) (p : P₀.val.Section (fieldExtensionTest k S)) :
    ∃ L : FiniteGaloisIntermediateField k S,
      ∀ σ ∈ (restriction L).ker, P₀.val.res (fieldExtensionAut k S σ) p = p := by
  obtain ⟨L, q, rfl⟩ := finitePoint H₀ P₀ p
  refine ⟨L, fun σ hσ ↦ ?_⟩
  rw [restrict_comp]
  congr 1
  apply Over.OverMorphism.ext
  change (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom L.toIntermediateField.val).op =
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom L.toIntermediateField.val).op
  rw [← Functor.map_comp]
  apply congrArg ((algSpec (CommRingCat.of k)).map)
  apply Quiver.Hom.unop_inj
  ext x
  exact (IntermediateField.mem_fixingSubgroup_iff L.toIntermediateField σ).mp
    (by rwa [← restriction_ker]) x x.property

theorem pointCocycle : PointCocycle.{u} := by
  intro k S _ _ _ _ H P p
  let : TopologicalSpace (NonabelianCohomology.Points k S H.val.X) := ⊥
  let d (σ : S ≃ₐ[k] S) := displacement P p (P.val.res (fieldExtensionAut k S σ) p)
  have hm (σ τ : S ≃ₐ[k] S) :
      d (σ * τ) = d σ * pointAction k S H.val.X σ (d τ) := displacement_cocycle P p σ τ
  refine ⟨⟨d, ?_, hm⟩, fun σ ↦ (act_displacement P p _).symm⟩
  obtain ⟨L, hL⟩ := finite_point_stabilizer H P p
  apply continuous_iff_continuousAt.mpr
  intro σ
  refine (continuousAt_const : ContinuousAt (fun _ : S ≃ₐ[k] S ↦ d σ) σ).congr ?_
  have ho : IsOpen (↑((restriction L).ker) : Set (S ≃ₐ[k] S)) := by
    rw [restriction_ker]
    exact L.toIntermediateField.fixingSubgroup_isOpen
  have hn : (fun τ : S ≃ₐ[k] S ↦ σ⁻¹ * τ) ⁻¹' (↑((restriction L).ker) : Set (S ≃ₐ[k] S))
      ∈ nhds σ := (ho.preimage (continuous_const_mul σ⁻¹)).mem_nhds (by simp)
  filter_upwards [hn] with τ hτ
  change σ⁻¹ * τ ∈ (restriction L).ker at hτ
  have h : d (σ⁻¹ * τ) = 1 := by
    apply ULift.up_injective
    apply (P.property.1 _ p).injective
    rw [act_displacement, hL _ hτ]
    exact (P.val.act_one p).symm
  simpa [h] using (hm σ (σ⁻¹ * τ)).symm

end Cocycles

private theorem transportCocycle {k S : Type u} [Field k] [Field S] [Algebra k S]
    {H : GroupScheme k} {P Q : FppfTorsor (fieldBase k) H}
    (e : RightActionIso P.val Q.val) {p : P.val.Section (fieldExtensionTest k S)}
    {a : GaloisCocycle (S := S) H} (ha : IsCocycleOf P p a) :
    IsCocycleOf Q (e.iso.hom.hom.app (op (fieldExtensionTest k S)) p) a := by
  intro σ
  rw [equivariant_restrict Q e, ha σ, e.equivariant]

theorem changeOfPoint : ChangeOfPoint.{u} := by
  intro k S _ _ _ H P p q a b ha hb
  exact cocycle_change_point P ha hb

private def fieldTestToIdentity (k : Type u) [Field k] :
    fieldTest k ⟶ fieldExtensionTest k k := by
  let q : fieldBase k ⟶ (fieldExtensionTest k k).left :=
    Over.homMk (𝟙 _) (by
      rw [Category.id_comp]
      change ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom = 𝟙 _
      rw [algSpec_obj_hom]
      exact Scheme.Spec.map_id _)
  exact Over.homMk q (Over.mkIdTerminal.hom_ext _ _)

/-- The section cocycle induces a pointed map on right torsor classes. -/
theorem classificationMap : ClassificationMap.{u} := by
  classical
  intro k S _ _ _ _ H hG hH
  let : TopologicalSpace (NonabelianCohomology.Points k S H.val.X) := ⊥
  let ρ := pointAction k S H.val.X
  let getPoint (P : FppfTorsor (fieldBase k) H.val) :=
    (geometricPoint (S := S) H P hH).some
  let getCocycle (P : FppfTorsor (fieldBase k) H.val) :=
    (pointCocycle H P (getPoint P)).choose
  have hP (P : FppfTorsor (fieldBase k) H.val) :
      IsCocycleOf P (getPoint P) (getCocycle P) :=
    (pointCocycle H P (getPoint P)).choose_spec
  let f : H1fppf k H.val → groupH1 k H.val.X S :=
    Quotient.lift (fun P ↦ classOf (getCocycle P)) (by
      intro P Q h
      obtain ⟨e⟩ : Nonempty (RightActionIso P.val Q.val) := h
      apply classOf_eq_iff.mpr
      exact cocycle_change_point Q (transportCocycle e (hP P)) (hP Q))
  have hf (P : FppfTorsor (fieldBase k) H.val) (p : P.val.Section (fieldExtensionTest k S))
      (a : GaloisCocycle (S := S) H.val) (ha : IsCocycleOf P p a) :
      f (Quotient.mk _ P) = classOf a := by
    change classOf (getCocycle P) = classOf a
    exact classOf_eq_iff.mpr (cocycle_change_point P (hP P) ha)
  have hneutral : f (Specs.Fppf.neutralClass hG) = groupBasepoint k H.val.X S := by
    apply hf (regularTorsor hG) (1 : (groupSections (fieldBase k) H.val).obj
      (op (fieldExtensionTest k S))) (trivial ρ)
    intro σ
    change (groupSections (fieldBase k) H.val).map (fieldExtensionAut k S σ).op 1 = 1 * 1
    simp
  refine ⟨f, hneutral, fun P ↦ ⟨?_, ?_⟩, hf⟩
  · intro h
    obtain ⟨b, hb⟩ : Cohomologous (getCocycle P) (trivial ρ) :=
      classOf_eq_iff.mp h
    let q := P.val.act (getPoint P) (ULift.up b)
    have hq (σ : S ≃ₐ[k] S) : P.val.res (fieldExtensionAut k S σ) q = q := by
      have hσ : b⁻¹ * getCocycle P σ * ρ σ b = 1 := (hb σ).symm
      have hσ' : getCocycle P σ * ρ σ b = b := by
        calc
          getCocycle P σ * ρ σ b = b * (b⁻¹ * getCocycle P σ * ρ σ b) := by simp [mul_assoc]
          _ = b := by rw [hσ, mul_one]
      change P.val.res (fieldExtensionAut k S σ) (P.val.act (getPoint P) ⟨b⟩) = q
      rw [res_act, hP P σ, P.val.act_mul]
      exact congrArg (fun z ↦ P.val.act (getPoint P) ⟨z⟩) hσ'
    obtain ⟨x, _⟩ := fixedPoint H P q hq
    exact ⟨P.val.res (fieldTestToIdentity k) x⟩
  · intro h
    rw [(Fppf.rationalPointCriterion hG P).mpr h]
    exact hneutral

section FiniteReduction

variable {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
  {H : GroupScheme k} (P : FppfTorsor (fieldBase k) H)

omit [IsGalois k S] in
private theorem fieldExtensionMap_restriction (L : FiniteGaloisIntermediateField k S)
    (σ : S ≃ₐ[k] S) :
    fieldExtensionAut k S σ ≫ fieldExtensionMap L.toIntermediateField.val =
      fieldExtensionMap L.toIntermediateField.val ≫ fieldExtensionAut k L (restriction L σ) := by
  rw [show fieldExtensionAut k S σ = fieldExtensionMap σ.toAlgHom from rfl,
    show fieldExtensionAut k L (restriction L σ) =
      fieldExtensionMap (restriction L σ).toAlgHom from rfl]
  rw [← fieldExtensionMap_comp, ← fieldExtensionMap_comp]
  apply congrArg fieldExtensionMap
  ext x
  exact (AlgEquiv.restrictNormal_commutes σ L x).symm

omit [IsGalois k S] in
private theorem act_restriction {K : Type u} [Field K] [Algebra k K]
    (f : K →ₐ[k] S) (p : P.val.Section (fieldExtensionTest k K))
    (b : NonabelianCohomology.Points k K H.X) :
    P.val.res (fieldExtensionMap f) (P.val.act p ⟨b⟩) =
      P.val.act (P.val.res (fieldExtensionMap f) p) ⟨pointMap k K H.X f b⟩ :=
  P.val.map_act _ _ _

omit [IsGalois k S] in
private theorem point_cocycle_after_extension (L : FiniteGaloisIntermediateField k S)
    (p : P.val.Section (fieldExtensionTest k L)) (c : GaloisCocycle (S := L) H)
    (a : GaloisCocycle (S := S) H) (hc : IsCocycleOf P p c)
    (he : ∀ σ, pointMap k L H.X L.toIntermediateField.val (c (restriction L σ)) = a σ) :
    IsCocycleOf P (P.val.res (fieldExtensionMap L.toIntermediateField.val) p) a := by
  intro σ
  rw [restrict_comp, fieldExtensionMap_restriction, ← restrict_comp, hc, act_restriction, he]

private theorem realization_at_sepClosure (realize : FiniteRealization.{u})
    (H : AffineAlgebraicGroup k) (a : GaloisCocycle (S := S) H.val) :
    ∃ (P : FppfTorsor (fieldBase k) H.val) (p : P.val.Section (fieldExtensionTest k S)),
      IsCocycleOf P p a := by
  let : TopologicalSpace (NonabelianCohomology.Points k S H.val.X) := ⊥
  let : DiscreteTopology (NonabelianCohomology.Points k S H.val.X) := ⟨rfl⟩
  let ρ := pointAction k S H.val.X
  obtain ⟨L, c, _, ha⟩ := finiteLevel (ρ := ρ) ⊥ a
  let : TopologicalSpace (NonabelianCohomology.Points k L H.val.X) := ⊥
  obtain ⟨e, hcoe, hact⟩ := finitePointsIdentification (H := H.val.X) L
  let c₀ : GaloisCocycle (S := L) H.val :=
    ⟨fun σ ↦ e.symm (c σ), continuous_of_discreteTopology, by
      intro σ τ
      apply e.injective
      rw [map_mul, hact]
      simp only [MulEquiv.apply_symm_apply]
      exact c.property.2 σ τ⟩
  obtain ⟨P, p, hp⟩ := realize H c₀
  refine ⟨P, P.val.res (fieldExtensionMap L.toIntermediateField.val) p,
    point_cocycle_after_extension P L p c₀ a hp (fun σ ↦ ?_)⟩
  have h := (hcoe (e.symm (c (restriction L σ)))).symm
  rw [MulEquiv.apply_symm_apply] at h
  exact h.trans (ha σ)

omit [IsGalois k S] in
private theorem cocycle_slide {p : P.val.Section (fieldExtensionTest k S)}
    {a b : GaloisCocycle (S := S) H}
    (ha : IsCocycleOf P p a) (t : NonabelianCohomology.Points k S H.X)
    (hab : ∀ σ, b σ = t⁻¹ * a σ * pointAction k S H.X σ t) :
    IsCocycleOf P (P.val.act p ⟨t⟩) b := by
  intro σ
  rw [res_act, ha σ, P.val.act_mul, P.val.act_mul]
  apply congrArg (fun v ↦ P.val.act p ⟨v⟩)
  rw [hab σ]
  simp [mul_assoc]

private theorem finite_level_isomorphism (isoAtLevel : FiniteIsomorphism.{u})
    (H : AffineAlgebraicGroup k) (P Q : FppfTorsor (fieldBase k) H.val)
    (p : P.val.Section (fieldExtensionTest k S)) (q : Q.val.Section (fieldExtensionTest k S))
    (a : GaloisCocycle (S := S) H.val) (hp : IsCocycleOf P p a) (hq : IsCocycleOf Q q a) :
    Nonempty (RightActionIso P.val Q.val) := by
  obtain ⟨L₁, p₀, h₁⟩ := finitePoint H P p
  obtain ⟨L₂, q₀, h₂⟩ := finitePoint H Q q
  let L := L₁ ⊔ L₂
  let v := L.toIntermediateField.val
  let j₁ : L₁ →ₐ[k] L := IntermediateField.inclusion (show L₁ ≤ L from le_sup_left)
  let j₂ : L₂ →ₐ[k] L := IntermediateField.inclusion (show L₂ ≤ L from le_sup_right)
  let pL := P.val.res (fieldExtensionMap j₁) p₀
  let qL := Q.val.res (fieldExtensionMap j₂) q₀
  have hpL : P.val.res (fieldExtensionMap v) pL = p := by
    change P.val.res (fieldExtensionMap v) (P.val.res (fieldExtensionMap j₁) p₀) = p
    rw [restrict_comp, ← fieldExtensionMap_comp]
    exact h₁
  have hqL : Q.val.res (fieldExtensionMap v) qL = q := by
    change Q.val.res (fieldExtensionMap v) (Q.val.res (fieldExtensionMap j₂) q₀) = q
    rw [restrict_comp, ← fieldExtensionMap_comp]
    exact h₂
  let : TopologicalSpace (NonabelianCohomology.Points k L H.val.X) := ⊥
  let d (δ : L ≃ₐ[k] L) := displacement P pL (P.val.res (fieldExtensionAut k L δ) pL)
  let c : GaloisCocycle (S := L) H.val :=
    ⟨d, continuous_of_discreteTopology, displacement_cocycle P pL⟩
  have hc : IsCocycleOf P pL c := fun δ ↦ (act_displacement P pL _).symm
  have hrestrict (σ : S ≃ₐ[k] S) :
      pointMap k L H.val.X v (c (restriction L σ)) = a σ := by
    apply ULift.up_injective
    apply (P.property.1 _ p).injective
    rw [← hp σ, ← hpL,
      restrict_comp P (fieldExtensionMap v) (fieldExtensionAut k S σ) pL,
      fieldExtensionMap_restriction,
      ← restrict_comp P (fieldExtensionAut k L (restriction L σ)) (fieldExtensionMap v) pL,
      hc, act_restriction]
  have hcQ : IsCocycleOf Q qL c := by
    intro δ
    obtain ⟨σ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S :
      Function.Surjective (restriction L)) δ
    apply pointRestrictionInjective H Q v
    rw [restrict_comp Q (fieldExtensionAut k L (restriction L σ)) (fieldExtensionMap v) qL,
      ← fieldExtensionMap_restriction,
      ← restrict_comp Q (fieldExtensionMap v) (fieldExtensionAut k S σ) qL, hqL, hq σ,
      act_restriction, hqL, hrestrict]
  exact isoAtLevel H P Q pL qL c hc hcQ

end FiniteReduction

/-- Finite realization and descent of isomorphisms suffice for the
classification over the separable closure. -/
theorem classificationOfFiniteResults (realize : FiniteRealization.{u})
    (isoAtLevel : FiniteIsomorphism.{u}) : Classification.{u} := by
  classical
  intro k S _ _ _ _ H hH
  have hG := Fppf.schemeGroupSectionsAreSheaf (fieldBase k) H.val
  let : TopologicalSpace (NonabelianCohomology.Points k S H.val.X) := ⊥
  obtain ⟨f, hneutral, hfield, hformula⟩ := classificationMap (S := S) H hG hH
  have hinj : Function.Injective f := by
    intro x y h
    obtain ⟨P, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨Q, rfl⟩ := Quotient.mk_surjective y
    obtain ⟨p⟩ := geometricPoint (S := S) H P hH
    obtain ⟨q⟩ := geometricPoint (S := S) H Q hH
    obtain ⟨a, ha⟩ := pointCocycle H P p
    obtain ⟨b, hb⟩ := pointCocycle H Q q
    have hab : classOf a = classOf b :=
      (hformula P p a ha).symm.trans (h.trans (hformula Q q b hb))
    obtain ⟨t, ht⟩ := classOf_eq_iff.mp hab
    exact Quotient.sound (finite_level_isomorphism isoAtLevel H P Q
      (P.val.act p ⟨t⟩) q b (cocycle_slide P ha t ht) hb)
  have hsurj : Function.Surjective f := by
    intro x
    change ∃ y, f y = x
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨P, p, hp⟩ := realization_at_sepClosure realize H a
    exact ⟨Quotient.mk _ P, hformula P p a hp⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ ↦ hneutral,
    fun P ↦ ⟨hfield P, ?_, hformula P⟩⟩
  obtain ⟨p⟩ := geometricPoint (S := S) H P hH
  exact ⟨p, pointCocycle H P p⟩

open Polynomial in
/-- In characteristic p a non-pth power cannot acquire a pth root in a
separable extension. -/
theorem powerFiberNoPoint : PowerFiberNoPoint.{u} := by
  intro k S _ _ _ _ p _ _ a ha
  refine ⟨fun g ↦ ?_⟩
  let f : k[X] := X ^ p - C (a : k)
  let q := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage g.left
  let φ : AdjoinRoot f →ₐ[k] S := q.unop.hom
  let r := φ (AdjoinRoot.root f)
  have hr : aeval r f = 0 := by
    change aeval (φ (AdjoinRoot.root f)) f = 0
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hp : p.Prime := Fact.out
  have hi : Irreducible f := X_pow_sub_C_irreducible_of_prime hp ha
  have hmin : minpoly k r = f :=
    (minpoly.eq_of_irreducible_of_monic hi hr (monic_X_pow_sub_C _ hp.ne_zero)).symm
  have hsep := Algebra.IsSeparable.isSeparable k r
  change (minpoly k r).Separable at hsep
  rw [hmin] at hsep
  exact (X_pow_sub_C_separable_iff hp.pos a.ne_zero).mp hsep (CharP.cast_eq_zero k p)

section DoubleOverlap

open scoped TensorProduct

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

@[simp] private theorem compareTensor_tmul (x y : K) (σ : Gal(K/k)) :
    galoisTensorMap k K (x ⊗ₜ[k] y) σ = x * σ y := rfl

/-- The comparison decomposes the finite Galois double overlap. -/
theorem galoisTensorComparison : GaloisTensorComparison.{u} := by
  classical
  intro k K _ _ _ _ _
  let := Fintype.ofFinite (Gal(K/k))
  let F := galoisTensorMap k K
  have hsep (σ τ : Gal(K/k)) (h : σ ≠ τ) : ∃ x : K, σ x ≠ τ x := by
    by_contra! e
    exact h (AlgEquiv.ext e)
  let x (σ τ : Gal(K/k)) : K := if h : σ ≠ τ then (hsep σ τ h).choose else 0
  have hdiff {σ τ : Gal(K/k)} (h : σ ≠ τ) : σ (x σ τ) ≠ τ (x σ τ) := by
    simp only [x, dite_eq_left h]
    exact (hsep σ τ h).choose_spec
  let z (σ τ : Gal(K/k)) : K ⊗[k] K :=
    (σ (x σ τ) - τ (x σ τ))⁻¹ ⊗ₜ[k] x σ τ -
      ((σ (x σ τ) - τ (x σ τ))⁻¹ * τ (x σ τ)) ⊗ₜ[k] 1
  have hz (σ τ δ : Gal(K/k)) :
      F (z σ τ) δ = (σ (x σ τ) - τ (x σ τ))⁻¹ * (δ (x σ τ) - τ (x σ τ)) := by
    simp [F, z, mul_sub]
  let e (σ : Gal(K/k)) : K ⊗[k] K := ∏ τ ∈ Finset.univ.erase σ, z σ τ
  have hdiag (σ : Gal(K/k)) : F (e σ) σ = 1 := by
    change ((Pi.evalAlgHom K _ σ).comp F) (e σ) = 1
    rw [show e σ = _ from rfl, map_prod]
    apply Finset.prod_eq_one
    intro τ hτ
    change F (z σ τ) σ = 1
    rw [hz, inv_mul_cancel₀ (sub_ne_zero.mpr (hdiff (Ne.symm (Finset.mem_erase.mp hτ).1)))]
  have hoff {σ τ : Gal(K/k)} (h : τ ≠ σ) : F (e σ) τ = 0 := by
    change ((Pi.evalAlgHom K _ τ).comp F) (e σ) = 0
    rw [show e σ = _ from rfl, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
    change F (z σ τ) τ = 0
    rw [hz, sub_self, mul_zero]
  have hs : Function.Surjective F := by
    intro v
    refine ⟨∑ σ : Gal(K/k), algebraMap K (K ⊗[k] K) (v σ) * e σ, funext fun τ ↦ ?_⟩
    change ((Pi.evalAlgHom K _ τ).comp F) _ = _
    rw [map_sum, Finset.sum_eq_single τ]
    · rw [map_mul, AlgHom.commutes]
      change v τ * F (e τ) τ = v τ
      rw [hdiag, mul_one]
    · intro σ _ h
      rw [map_mul]
      change _ * F (e σ) τ = 0
      rw [hoff (Ne.symm h), mul_zero]
    · simp
  have hd : Module.finrank K (K ⊗[k] K) = Module.finrank K (Gal(K/k) → K) := by
    rw [Module.finrank_baseChange, Module.finrank_pi, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
    (f := F.toLinearMap)).mpr hs, hs⟩

end DoubleOverlap

section GaloisOverlap

open scoped TensorProduct

variable {k : Type u} [Field k]

private abbrev FieldSite (k : Type u) [Field k] := Over (fieldBase k)

private abbrev fieldSiteTopology (k : Type u) [Field k] := torsorTopology (fieldBase k)

private abbrev underlyingScheme : FieldSite k ⥤ Scheme.{u} :=
  Over.forget _ ⋙ Over.forget _

private abbrev fieldGroup (H : GroupScheme k) := groupSections (fieldBase k) H

variable {K : Type u} [Field K] [Algebra k K]

private abbrev galoisTest (k K : Type u) [Field k] [Field K] [Algebra k K] := fieldExtensionTest k K

private def galoisGraph (σ : Gal(K/k)) :
    galoisTest k K ⟶ galoisTest k K ⨯ galoisTest k K :=
  prod.lift (𝟙 _) (fieldExtensionAut k K σ)

private def fieldTensorProduct (A B : Type u) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] :
    IsLimit (BinaryFan.mk (fieldExtensionMap
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := B)))
      (fieldExtensionMap (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := B)))) := by
  let F := algSpec (CommRingCat.of k)
  letI : PreservesLimitsOfSize.{0, 0} F :=
    (algΓAlgSpecAdjunction (CommRingCat.of k)).rightAdjoint_preservesLimits
  let h := (BinaryFan.isLimitMapConeEquiv (F := F)).toFun
    (isLimitOfPreserves F (BinaryCofan.IsColimit.op
      (CommAlgCat.binaryCofanIsColimit (CommAlgCat.of k A) (CommAlgCat.of k B))))
  refine BinaryFan.isLimitMk (fun s ↦ Over.homMk (BinaryFan.IsLimit.lift h s.fst.left s.snd.left)
    (Over.mkIdTerminal.hom_ext _ _)) ?_ ?_ ?_
  · intro s
    apply Over.OverMorphism.ext
    exact BinaryFan.IsLimit.lift_fst h s.fst.left s.snd.left
  · intro s
    apply Over.OverMorphism.ext
    exact BinaryFan.IsLimit.lift_snd h s.fst.left s.snd.left
  · intro s m hm₁ hm₂
    apply Over.OverMorphism.ext
    apply BinaryFan.IsLimit.hom_ext h
    · exact (congrArg Over.Hom.left hm₁).trans (BinaryFan.IsLimit.lift_fst h _ _).symm
    · exact (congrArg Over.Hom.left hm₂).trans (BinaryFan.IsLimit.lift_snd h _ _).symm

private def galoisTensorIso :
    fieldExtensionTest k (K ⊗[k] K) ≅ galoisTest k K ⨯ galoisTest k K :=
  IsLimit.conePointUniqueUpToIso (fieldTensorProduct (k := k) K K)
    (limit.isLimit _)

private theorem galoisGraph_eq (σ : Gal(K/k)) :
    fieldExtensionMap (Pi.evalAlgHom k (fun _ : Gal(K/k) ↦ K) σ) ≫
      fieldExtensionMap ((galoisTensorMap k K).restrictScalars k) ≫
      (galoisTensorIso (k := k) (K := K)).hom = galoisGraph σ := by
  have h₁ : (galoisTensorIso (k := k) (K := K)).hom ≫ prod.fst =
      fieldExtensionMap (Algebra.TensorProduct.includeLeft (S := k)) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (fieldTensorProduct (k := k) K K) (limit.isLimit _)
      ⟨WalkingPair.left⟩
  have h₂ : (galoisTensorIso (k := k) (K := K)).hom ≫ prod.snd =
      fieldExtensionMap (Algebra.TensorProduct.includeRight (R := k)) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (fieldTensorProduct (k := k) K K) (limit.isLimit _)
      ⟨WalkingPair.right⟩
  apply prod.hom_ext
  · simp only [Category.assoc, h₁, galoisGraph, prod.lift_fst, ← fieldExtensionMap_comp]
    have he : ((Pi.evalAlgHom k (fun _ : Gal(K/k) ↦ K) σ).comp
        (((galoisTensorMap k K).restrictScalars k).comp
        (Algebra.TensorProduct.includeLeft (S := k)))) = AlgHom.id k K := by
      ext x
      change x * σ 1 = x
      rw [map_one, mul_one]
    rw [he]
    apply Over.OverMorphism.ext
    exact (algSpec (CommRingCat.of k)).map_id _
  · simp only [Category.assoc, h₂, galoisGraph, prod.lift_snd, ← fieldExtensionMap_comp]
    apply congrArg fieldExtensionMap
    ext x
    change 1 * σ x = σ x
    rw [one_mul]

private def galoisGraphsUnderlying [FiniteDimensional k K] [IsGalois k K] :
    IsColimit (Cofan.mk ((underlyingScheme (k := k)).obj (galoisTest k K ⨯ galoisTest k K))
      (fun σ : Gal(K/k) ↦ underlyingScheme.map (galoisGraph σ))) := by
  let R : Gal(K/k) → CommRingCat := fun _ ↦ CommRingCat.of K
  let m := fieldExtensionMap ((galoisTensorMap k K).restrictScalars k)
  have : IsIso m := by
    let e := AlgEquiv.ofBijective _ (galoisTensorComparison k K)
    let i := (CommAlgCat.isoMk (e.restrictScalars k)).op
    have : IsIso ((Over.forget (fieldBase k)).map m) := by
      change IsIso ((algSpec (CommRingCat.of k)).map i.hom)
      infer_instance
    exact isIso_of_reflects_iso m (Over.forget (fieldBase k))
  let i : (∐ fun σ ↦ Spec (R σ)) ≅
      underlyingScheme.obj (galoisTest k K ⨯ galoisTest k K) :=
    asIso (sigmaSpec R) ≪≫
      underlyingScheme.mapIso (asIso m ≪≫ galoisTensorIso (k := k) (K := K))
  apply IsColimit.ofIsoColimit (coproductIsCoproduct (fun σ ↦ Spec (R σ)))
  refine Cofan.ext i (fun σ ↦ ?_)
  change Sigma.ι (fun σ ↦ Spec (R σ)) σ ≫ sigmaSpec R ≫
    underlyingScheme.map (m ≫ (galoisTensorIso (k := k) (K := K)).hom) =
      underlyingScheme.map (galoisGraph σ)
  have hs : Sigma.ι (fun σ ↦ Spec (R σ)) σ ≫ sigmaSpec R =
      underlyingScheme.map (fieldExtensionMap (Pi.evalAlgHom k (fun _ : Gal(K/k) ↦ K) σ)) :=
    ι_sigmaSpec R σ
  calc
    _ = underlyingScheme.map (fieldExtensionMap (Pi.evalAlgHom k (fun _ : Gal(K/k) ↦ K) σ)) ≫
          underlyingScheme.map (m ≫ (galoisTensorIso (k := k) (K := K)).hom) :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hs)
    _ = _ := (Functor.map_comp _ _ _).symm.trans
      (congrArg underlyingScheme.map (galoisGraph_eq σ))

private def galoisGraphsColimit [FiniteDimensional k K] [IsGalois k K] :
    IsColimit (Cofan.mk (galoisTest k K ⨯ galoisTest k K) (galoisGraph (k := k) (K := K))) :=
  isColimitOfReflects (underlyingScheme (k := k))
    ((Cofan.isColimitMapCoconeEquiv _ _ _).symm (galoisGraphsUnderlying (k := k) (K := K)))

private theorem galoisGraphsCover [FiniteDimensional k K] [IsGalois k K] :
    Sieve.ofArrows (fun _ : Gal(K/k) ↦ galoisTest k K) (galoisGraph (k := k) (K := K)) ∈
      fieldSiteTopology k (galoisTest k K ⨯ galoisTest k K) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows,
    GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let f (σ : Gal(K/k)) : Spec (CommRingCat.of K) ⟶
      underlyingScheme.obj (galoisTest k K ⨯ galoisTest k K) :=
    underlyingScheme.map (galoisGraph (k := k) σ)
  change Sieve.ofArrows _ f ∈ Scheme.fppfTopology _
  have : IsIso (Sigma.desc f) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp ⟨galoisGraphsUnderlying (k := k) (K := K)⟩
  let 𝒰 := (sigmaOpenCover (fun _ : Gal(K/k) ↦ Spec (CommRingCat.of K))).pushforwardIso
    (Sigma.desc f)
  have h := 𝒰.mem₀
  change Presieve.ofArrows (fun _ : Gal(K/k) ↦ Spec (CommRingCat.of K))
    (fun σ ↦ Sigma.ι (fun _ : Gal(K/k) ↦ Spec (CommRingCat.of K)) σ ≫ Sigma.desc f) ∈ Scheme.zariskiPrecoverage _ at h
  simp only [Sigma.ι_comp_desc] at h
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ h)

end GaloisOverlap

section FiniteCover
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
local notation "V" => galoisTest k K

private abbrev extendTest (E : FieldSite k) : FieldSite k ⥤ FieldSite k :=
  Over.star E ⋙ Over.forget E

private abbrev coverAut (σ : Gal(K/k)) (U : FieldSite k) : (V ⨯ U) ⟶ (V ⨯ U) :=
  prod.map (fieldExtensionAut k K σ) (𝟙 U)


private abbrev sectionsRes {P : (FieldSite k)ᵒᵖ ⥤ Type (u + 1)} {U W : FieldSite k}
    (f : W ⟶ U) : P.obj (op U) → P.obj (op W) :=
  P.map f.op

private theorem sectionsRes_comp {P : (FieldSite k)ᵒᵖ ⥤ Type (u + 1)}
    {U W Z : FieldSite k} (f : Z ⟶ W) (g : W ⟶ U) (x : P.obj (op U)) :
    sectionsRes (f ≫ g) x = sectionsRes f (sectionsRes g x) := by
  simp only [sectionsRes, op_comp, Functor.map_comp, types_comp_apply]

private theorem coverSnd_cover [FiniteDimensional k K] (U : FieldSite k) :
    Sieve.generate (Presieve.singleton (prod.snd : V ⨯ U ⟶ U)) ∈ fieldSiteTopology k U := by
  have h : IsFppf (V).hom.left := by
    rw [fieldHom_left]
    have h := field_extension_fppf (k := k) K
    rw [fieldHom_left] at h
    exact h
  exact covers_singleton prod.snd (chart_cover (prodIsProd V U) h)

private theorem coverSnd_injective [FiniteDimensional k K] {P : (FieldSite k)ᵒᵖ ⥤ Type (u + 1)}
    (hP : Presieve.IsSheaf (fieldSiteTopology k) P) (U : FieldSite k) :
    Function.Injective (sectionsRes (P := P) (prod.snd : V ⨯ U ⟶ U)) :=
  Presieve.isSeparatedFor_singleton.mp
    ((hP.isSheafFor _ (coverSnd_cover (K := K) U)).isSeparatedFor)

/-- The automorphism graphs detect the Čech compatibility of each section over
the pullback of the finite field cover. -/
private theorem descendInvariant [FiniteDimensional k K] [IsGalois k K]
    {P : (FieldSite k)ᵒᵖ ⥤ Type (u + 1)}
    (hP : Presieve.IsSheaf (fieldSiteTopology k) P) (U : FieldSite k)
    (x : P.obj (op (V ⨯ U))) (hx : ∀ σ, sectionsRes (coverAut σ U) x = x) :
    ∃! y, sectionsRes (prod.snd : V ⨯ U ⟶ U) y = x := by
  apply (Presieve.isSheafFor_singleton.mp (hP.isSheafFor _ (coverSnd_cover (K := K) U))) x
  intro W f g hw
  let d : W ⟶ V ⨯ V := prod.lift (f ≫ prod.fst) (g ≫ prod.fst)
  let R := (Sieve.ofArrows (fun _ : Gal(K/k) ↦ V) (galoisGraph (k := k) (K := K))).pullback d
  have hR : R ∈ fieldSiteTopology k W :=
    (fieldSiteTopology k).pullback_stable d (galoisGraphsCover (k := k) (K := K))
  apply (hP R hR).isSeparatedFor.ext
  intro Z t ht
  change Sieve.ofArrows _ _ (t ≫ d) at ht
  obtain ⟨σ, v, he⟩ := Sieve.ofArrows.exists ht
  symm at he
  have hv₁ : v = t ≫ f ≫ prod.fst := by
    have h := congrArg (· ≫ (prod.fst : V ⨯ V ⟶ V)) he
    simpa [galoisGraph, d, Category.assoc] using h
  have hv₂ : v ≫ fieldExtensionAut k K σ = t ≫ g ≫ prod.fst := by
    have h := congrArg (· ≫ (prod.snd : V ⨯ V ⟶ V)) he
    simpa [galoisGraph, d, Category.assoc] using h
  have hfg : (t ≫ f) ≫ coverAut σ U = t ≫ g := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst]
      calc
        _ = (t ≫ f ≫ prod.fst) ≫ fieldExtensionAut k K σ := by simp only [Category.assoc]
        _ = _ := hv₁ ▸ hv₂
    · simp only [Category.assoc, prod.map_snd, Category.comp_id, hw]
  change sectionsRes t (sectionsRes f x) = sectionsRes t (sectionsRes g x)
  rw [← sectionsRes_comp t f, ← sectionsRes_comp t g, ← hfg,
    sectionsRes_comp (t ≫ f) (coverAut σ U), hx]

end FiniteCover

section FixedPresheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {F : Cᵒᵖ ⥤ Type (u + 1)} {I : Type*} (a : I → (F ⟶ F))

private def fixedPresheaf : Cᵒᵖ ⥤ Type (u + 1) where
  obj U := {x : F.obj U // ∀ i, (a i).app U x = x}
  map f := ↾fun x ↦ ⟨F.map f x.val, fun i ↦ by
    exact ((a i).naturality_apply f x.val).trans (congrArg (F.map f) (x.property i))⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f ↦ f x.val) (F.map_id U)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f ↦ f x.val) (F.map_comp f g)

private theorem fixedPresheaf_isSheaf (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (fixedPresheaf a) := by
  intro U R hR x hx
  let y : Presieve.FamilyOfElements F (R : Presieve U) := fun _ f hf ↦ (x f hf).val
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
    exact congrArg Subtype.val (hx g₁ g₂ hf₁ hf₂ h)
  obtain ⟨s, hs, huniq⟩ := hF R hR y hy
  have ha (i : I) : (a i).app (op U) s = s := by
    apply huniq
    intro Y f hf
    rw [← types_comp_apply, ← (a i).naturality, types_comp_apply, hs f hf]
    exact (x f hf).property i
  refine ⟨⟨s, ha⟩, ?_, ?_⟩
  · intro Y f hf
    apply Subtype.ext
    exact hs f hf
  · intro t ht
    apply Subtype.ext
    apply huniq
    intro Y f hf
    exact congrArg Subtype.val (ht f hf)

end FixedPresheaf

section Twisting

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
local notation "V" => galoisTest k K
variable {H : GroupScheme k}

private abbrev GroupSectionsAt (H : GroupScheme k) (U : FieldSite k) : Type (u + 1) :=
  (fieldGroup H).obj (op U)

private abbrev groupRes {U W : FieldSite k} (f : W ⟶ U) :
    GroupSectionsAt H U → GroupSectionsAt H W :=
  (fieldGroup H).map f.op

private theorem groupRes_id (U : FieldSite k) (x : GroupSectionsAt H U) :
    groupRes (𝟙 U) x = x :=
  congrArg (fun f : (fieldGroup H).obj (op U) ⟶ (fieldGroup H).obj (op U) ↦ f x)
    ((fieldGroup H).map_id (op U))

private theorem groupRes_comp {U W Z : FieldSite k} (f : Z ⟶ W) (g : W ⟶ U)
    (x : (fieldGroup H).obj (op U)) :
    groupRes (f ≫ g) x = groupRes f (groupRes g x) :=
  sectionsRes_comp (P := fieldGroup H ⋙ forget GrpCat) f g x

private theorem groupRes_mul {U W : FieldSite k} (f : W ⟶ U)
    (x y : (fieldGroup H).obj (op U)) :
    groupRes f (x * y) = groupRes f x * groupRes f y :=
  map_mul ((fieldGroup H).map f.op).hom x y

private theorem groupRes_inv {U W : FieldSite k} (f : W ⟶ U)
    (x : (fieldGroup H).obj (op U)) :
    groupRes f x⁻¹ = (groupRes f x)⁻¹ :=
  map_inv ((fieldGroup H).map f.op).hom x

private theorem extendTest_fst {U W : FieldSite k} (f : W ⟶ U) :
    (extendTest V).map f ≫ (prod.fst : V ⨯ U ⟶ V) = prod.fst := by
  change prod.map (𝟙 V) f ≫ prod.fst = prod.fst
  simp

private theorem extendTest_snd {U W : FieldSite k} (f : W ⟶ U) :
    (extendTest V).map f ≫ (prod.snd : V ⨯ U ⟶ U) = prod.snd ≫ f :=
  prod.map_snd _ _

private theorem coverAut_fst (σ : Gal(K/k)) (U : FieldSite k) :
    coverAut σ U ≫ (prod.fst : V ⨯ U ⟶ V) =
      prod.fst ≫ fieldExtensionAut k K σ := prod.map_fst _ _

private theorem coverAut_snd (σ : Gal(K/k)) (U : FieldSite k) :
    coverAut σ U ≫ (prod.snd : V ⨯ U ⟶ U) = prod.snd := by
  simp [coverAut]

private theorem coverAut_natural (σ : Gal(K/k)) {U W : FieldSite k} (f : W ⟶ U) :
    (extendTest V).map f ≫ coverAut σ U = coverAut σ W ≫ (extendTest V).map f := by
  exact prod.map_swap f (fieldExtensionAut k K σ)

private abbrev translatedGroup (H : GroupScheme k) (E : FieldSite k) :=
  (extendTest E).op ⋙ (fieldGroup H ⋙ forget GrpCat)

private abbrev cocycleSection (a : GaloisCocycle (S := K) H) (σ : Gal(K/k)) :
    GroupSectionsAt H V :=
  ⟨a σ⟩

private abbrev pullbackCocycle (a : GaloisCocycle (S := K) H) (σ : Gal(K/k)) (U : FieldSite k) :
    GroupSectionsAt H (V ⨯ U) :=
  groupRes (prod.fst : V ⨯ U ⟶ V) (cocycleSection a σ)

/-- Compose restriction by the Galois automorphism with left translation by
the corresponding cocycle value. -/
private def twistOperator (a : GaloisCocycle (S := K) H) (σ : Gal(K/k)) :
    translatedGroup H V ⟶ translatedGroup H V where
  app U := ↾fun x ↦ pullbackCocycle a σ U.unop *
    groupRes (coverAut σ U.unop) (show GroupSectionsAt H (V ⨯ U.unop) from x)
  naturality U W f := by
    apply ConcreteCategory.hom_ext
    intro x
    change pullbackCocycle a σ W.unop * groupRes (coverAut σ W.unop)
        (groupRes ((extendTest V).map f.unop) x) =
      groupRes ((extendTest V).map f.unop)
        (pullbackCocycle a σ U.unop * groupRes (coverAut σ U.unop) x)
    rw [groupRes_mul, ← groupRes_comp, ← groupRes_comp, ← groupRes_comp,
      extendTest_fst, coverAut_natural]
    rfl

private abbrev twistedSections (a : GaloisCocycle (S := K) H) (U : FieldSite k) :=
  (fixedPresheaf (twistOperator a)).obj (op U)

private abbrev sectionValue {a : GaloisCocycle (S := K) H} {U : FieldSite k}
    (x : twistedSections a U) : GroupSectionsAt H (V ⨯ U) :=
  x.val

private theorem twistedSections_fixed {a : GaloisCocycle (S := K) H} {U : FieldSite k}
    (x : twistedSections a U) (σ : Gal(K/k)) :
    pullbackCocycle a σ U * groupRes (coverAut σ U) (sectionValue x) =
      sectionValue x := x.property σ

private theorem translatedGroup_isSheaf (H : GroupScheme k) :
    Presieve.IsSheaf (fieldSiteTopology k) (translatedGroup H V) := by
  let J := fieldSiteTopology k
  let : (extendTest V).IsContinuous J J :=
    Functor.isContinuous_comp _ _ J (J.over V) J
  exact Functor.op_comp_isSheaf_of_isSheaf_type (extendTest V) J
    (Fppf.schemeGroupSectionsAreSheaf (fieldBase k) H)

private def twistedAction (a : GaloisCocycle (S := K) H) : SchemeAction (fieldBase k) H where
  sheaf := ⟨fixedPresheaf (twistOperator a), (isSheaf_iff_isSheaf_of_type _ _).2
    (fixedPresheaf_isSheaf _ (translatedGroup_isSheaf H))⟩
  act {U} x g := ⟨sectionValue x * groupRes (prod.snd : V ⨯ U ⟶ U) g, fun σ ↦ by
    change pullbackCocycle a σ U * groupRes (coverAut σ U)
      (sectionValue x * groupRes prod.snd g) = _
    rw [groupRes_mul, ← groupRes_comp, coverAut_snd, ← mul_assoc,
      twistedSections_fixed (a := a) x]⟩
  act_one {U} x := by
    apply Subtype.ext
    change sectionValue x * groupRes (prod.snd : V ⨯ U ⟶ U) 1 = sectionValue x
    rw [show groupRes (H := H) (prod.snd : V ⨯ U ⟶ U) 1 = 1 from
      map_one ((fieldGroup H).map prod.snd.op).hom, mul_one]
  act_mul {U} x g h := by
    apply Subtype.ext
    change (sectionValue x * groupRes (prod.snd : V ⨯ U ⟶ U) g) * groupRes prod.snd h =
      sectionValue x * groupRes prod.snd (g * h)
    rw [groupRes_mul, mul_assoc]
  map_act {U W} f x g := by
    apply Subtype.ext
    change groupRes (prod.map (𝟙 V) f)
        (sectionValue x * groupRes (prod.snd : V ⨯ U ⟶ U) g) =
      groupRes (prod.map (𝟙 V) f) (sectionValue x) *
        groupRes (prod.snd : V ⨯ W ⟶ W) (groupRes f g)
    rw [groupRes_mul, ← groupRes_comp (prod.map (𝟙 V) f) (prod.snd : V ⨯ U ⟶ U),
      prod.map_snd, groupRes_comp]

variable [FiniteDimensional k K] [IsGalois k K]

private theorem twistedAction_bijective (a : GaloisCocycle (S := K) H) (U : FieldSite k)
    (x : (twistedAction a).Section U) : Function.Bijective ((twistedAction a).act x) := by
  have hG := Fppf.schemeGroupSectionsAreSheaf (fieldBase k) H
  constructor
  · intro g h he
    apply coverSnd_injective (K := K) hG U
    have h := congrArg (sectionValue (a := a) (U := U)) he
    exact mul_left_cancel h
  · intro y
    let d := (sectionValue x)⁻¹ * sectionValue y
    have hd (σ : Gal(K/k)) : groupRes (coverAut σ U) d = d := by
      have hx := twistedSections_fixed (a := a) x σ
      have hy := twistedSections_fixed (a := a) y σ
      change groupRes (coverAut σ U) ((sectionValue x)⁻¹ * sectionValue y) = (sectionValue x)⁻¹ * sectionValue y
      rw [groupRes_mul, groupRes_inv]
      calc
        _ = (pullbackCocycle a σ U * groupRes (coverAut σ U) (sectionValue x))⁻¹ *
              (pullbackCocycle a σ U * groupRes (coverAut σ U) (sectionValue y)) := by
          rw [mul_inv_rev]
          simp only [mul_assoc, inv_mul_cancel_left]
        _ = _ := by rw [hx, hy]
    obtain ⟨g, hg, _⟩ := descendInvariant hG U d hd
    refine ⟨g, Subtype.ext ?_⟩
    change sectionValue x * groupRes (prod.snd : V ⨯ U ⟶ U) g = sectionValue y
    rw [show groupRes (prod.snd : V ⨯ U ⟶ U) g = d from hg]
    simp [d]

private def gluedGroupSection (a : GaloisCocycle (S := K) H) :
    (fieldGroup H).obj (op (V ⨯ V)) :=
  ⟨Cofan.IsColimit.desc ((Cofan.isColimitMapCoconeEquiv (Over.forget (fieldBase k)) _ _).toFun
    (isColimitOfPreserves _ (galoisGraphsColimit (k := k) (K := K)))) (fun σ ↦ a σ)⟩

private theorem gluedGroupSection_res (a : GaloisCocycle (S := K) H)
    (σ : Gal(K/k)) : groupRes (galoisGraph σ) (gluedGroupSection a) = cocycleSection a σ := by
  apply ULift.ext
  exact Cofan.IsColimit.fac ((Cofan.isColimitMapCoconeEquiv (Over.forget (fieldBase k)) _ _).toFun
    (isColimitOfPreserves _ (galoisGraphsColimit (k := k) (K := K)))) (fun τ ↦ a τ) σ

private theorem eq_of_graphs {x y : (fieldGroup H).obj (op (V ⨯ V))}
    (h : ∀ σ : Gal(K/k), groupRes (galoisGraph σ) x = groupRes (galoisGraph σ) y) : x = y := by
  have hG := Fppf.schemeGroupSectionsAreSheaf (fieldBase k) H
  apply (hG _ (galoisGraphsCover (k := k) (K := K))).isSeparatedFor.ext
  intro W f hf
  obtain ⟨σ, g, rfl⟩ := Sieve.ofArrows.exists hf
  exact congrArg (groupRes g) (h σ)

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem galoisGraph_coverAut (δ σ : Gal(K/k)) :
    galoisGraph δ ≫ coverAut σ V =
      fieldExtensionAut k K σ ≫ galoisGraph (σ⁻¹ * δ) := by
  apply prod.hom_ext
  · simp [galoisGraph]
  · simp only [Category.assoc, galoisGraph, coverAut_snd, prod.lift_snd, ← fieldExtensionAut_mul]
    rw [mul_inv_cancel_left]

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem galoisGraph_extendTest (δ σ : Gal(K/k)) :
    galoisGraph δ ≫ (extendTest V).map (fieldExtensionAut k K σ) = galoisGraph (δ * σ) := by
  apply prod.hom_ext
  · simp [galoisGraph]
  · simp [galoisGraph, fieldExtensionAut_mul]

omit [FiniteDimensional k K] [IsGalois k K] in
private theorem lifted_cocycle (a : GaloisCocycle (S := K) H) (σ τ : Gal(K/k)) :
    cocycleSection a (σ * τ) =
      cocycleSection a σ * groupRes (fieldExtensionAut k K σ) (cocycleSection a τ) :=
  congrArg ULift.up (a.property.2 σ τ)

/-- On the graph of `Spec δ` the chosen section has value `a δ`. -/
private def twistedPoint (a : GaloisCocycle (S := K) H) : (twistedAction a).Section V :=
  ⟨gluedGroupSection a, fun σ ↦ by
    change pullbackCocycle a σ V * groupRes (coverAut σ V) (gluedGroupSection a) =
      gluedGroupSection a
    apply eq_of_graphs
    intro δ
    rw [groupRes_mul, ← groupRes_comp (galoisGraph δ) (prod.fst : V ⨯ V ⟶ V),
      ← groupRes_comp (galoisGraph δ) (coverAut σ V), galoisGraph_coverAut,
      groupRes_comp (fieldExtensionAut k K σ) (galoisGraph (σ⁻¹ * δ)),
      gluedGroupSection_res, gluedGroupSection_res, show galoisGraph δ ≫ prod.fst = 𝟙 V by
        simp [galoisGraph], groupRes_id]
    change cocycleSection a σ *
      groupRes (fieldExtensionAut k K σ) (cocycleSection a (σ⁻¹ * δ)) = cocycleSection a δ
    rw [← lifted_cocycle, mul_inv_cancel_left]⟩

private def twistedTorsor (a : GaloisCocycle (S := K) H) : FppfTorsor (fieldBase k) H :=
  ⟨twistedAction a, twistedAction_bijective a, fun U ↦ by
    refine (fieldSiteTopology k).superset_covering ?_ (coverSnd_cover (K := K) U)
    rintro W f ⟨Y, g, h, hh, _⟩
    cases hh
    exact ⟨(twistedAction a).res (g ≫ prod.fst) (twistedPoint a)⟩⟩

private theorem twistedPoint_isCocycle (a : GaloisCocycle (S := K) H) :
    IsCocycleOf (twistedTorsor a) (twistedPoint a) a := by
  intro σ
  apply Subtype.ext
  change groupRes ((extendTest V).map (fieldExtensionAut k K σ)) (gluedGroupSection a) =
    gluedGroupSection a * groupRes (prod.snd : V ⨯ V ⟶ V) (cocycleSection a σ)
  apply eq_of_graphs
  intro δ
  rw [groupRes_mul, ← groupRes_comp (galoisGraph δ) ((extendTest V).map (fieldExtensionAut k K σ)),
    galoisGraph_extendTest, ← groupRes_comp (galoisGraph δ) (prod.snd : V ⨯ V ⟶ V),
    show galoisGraph δ ≫ prod.snd = fieldExtensionAut k K δ by simp [galoisGraph],
    gluedGroupSection_res, gluedGroupSection_res]
  exact lifted_cocycle a δ σ

/-- The right torsor of twisted invariant sections has an affine representative
with a point realizing the given finite cocycle. -/
theorem finiteRealization : FiniteRealization.{u} := by
  intro k K _ _ _ _ _ H a
  let P := twistedTorsor a
  obtain ⟨X, A, ⟨e⟩, _⟩ := Fppf.affineTorsorRepresentability H P
  let Q : FppfTorsor (fieldBase k) H.val :=
    ⟨representedAction A, (Fppf.torsorInvariantUnderIso e).mpr P.property⟩
  exact ⟨Q, _, transportCocycle (P := P) (Q := Q) e.symm (twistedPoint_isCocycle a)⟩

end Twisting

section DescentOfIsomorphisms

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
local notation "V" => galoisTest k K
variable {H : GroupScheme k} {a : GaloisCocycle (S := K) H}
  (P : FppfTorsor (fieldBase k) H) (p : P.val.Section (fieldExtensionTest k K))
  (hp : IsCocycleOf P p a)

private theorem torsorRes_act {U W : FieldSite k} (f : W ⟶ U) (x : P.val.Section U)
    (g : GroupSectionsAt H U) :
    P.val.res f (P.val.act x g) = P.val.act (P.val.res f x) (groupRes f g) :=
  P.val.map_act f x g

include p hp

private theorem pullbackPoint_aut (U : FieldSite k) (σ : Gal(K/k)) :
    P.val.res (coverAut σ U) (P.val.res (prod.fst : V ⨯ U ⟶ V) p) =
      P.val.act (P.val.res (prod.fst : V ⨯ U ⟶ V) p) (pullbackCocycle a σ U) := by
  rw [restrict_comp, coverAut_fst, ← restrict_comp, hp]
  exact torsorRes_act P _ _ _

variable [FiniteDimensional k K] [IsGalois k K]

/-- Translation by the chosen torsor point converts the twisted fixed-point
condition into the ordinary descent condition for a torsor section. -/
private theorem translate_descends (U : FieldSite k) (x : (twistedAction a).Section U) :
    ∃! t : P.val.Section U, P.val.res (prod.snd : V ⨯ U ⟶ U) t =
      P.val.act (P.val.res (prod.fst : V ⨯ U ⟶ V) p) (sectionValue x) := by
  apply descendInvariant ((isSheaf_iff_isSheaf_of_type _ _).1 P.val.sheaf.property)
  intro σ
  let pU := P.val.res (prod.fst : V ⨯ U ⟶ V) p
  change P.val.res (coverAut σ U) (P.val.act pU (sectionValue x)) =
    P.val.act pU (sectionValue x)
  rw [torsorRes_act P (coverAut σ U) pU (sectionValue x), pullbackPoint_aut P p hp,
    P.val.act_mul]
  exact congrArg (P.val.act pU)
    (twistedSections_fixed (a := a) x σ)

private def translateSection (U : FieldSite k) (x : (twistedAction a).Section U) :
    P.val.Section U :=
  (translate_descends P p hp U x).exists.choose

private theorem translateSection_res (U : FieldSite k) (x : (twistedAction a).Section U) :
    P.val.res (prod.snd : V ⨯ U ⟶ U) (translateSection P p hp U x) =
      P.val.act (P.val.res (prod.fst : V ⨯ U ⟶ V) p) (sectionValue x) :=
  (translate_descends P p hp U x).exists.choose_spec

private theorem translateSection_bijective (U : FieldSite k) :
    Function.Bijective (translateSection P p hp U) := by
  let pU := P.val.res (prod.fst : V ⨯ U ⟶ V) p
  constructor
  · intro x y he
    apply Subtype.ext
    apply (P.property.1 _ pU).injective
    rw [← translateSection_res P p hp, ← translateSection_res P p hp, he]
  · intro t
    obtain ⟨g, hg⟩ := (P.property.1 _ pU).surjective (P.val.res (prod.snd : V ⨯ U ⟶ U) t)
    have hfix (σ : Gal(K/k)) : pullbackCocycle a σ U * groupRes (coverAut σ U) g = g := by
      have h := congrArg (P.val.res (coverAut σ U)) hg
      change P.val.res (coverAut σ U) (P.val.act (P.val.res prod.fst p) g) =
        P.val.res (coverAut σ U) (P.val.res prod.snd t) at h
      rw [torsorRes_act P (coverAut σ U) pU g, pullbackPoint_aut P p hp, P.val.act_mul,
        restrict_comp, coverAut_snd] at h
      exact (P.property.1 _ pU).injective (h.trans hg.symm)
    let x : (twistedAction a).Section U := ⟨g, hfix⟩
    refine ⟨x, ?_⟩
    apply coverSnd_injective (K := K)
      ((isSheaf_iff_isSheaf_of_type _ _).1 P.val.sheaf.property) U
    exact (translateSection_res P p hp U x).trans hg

private theorem translateSection_natural {U W : FieldSite k} (f : W ⟶ U)
    (x : (twistedAction a).Section U) :
    translateSection P p hp W ((twistedAction a).res f x) =
      P.val.res f (translateSection P p hp U x) := by
  apply coverSnd_injective (K := K)
    ((isSheaf_iff_isSheaf_of_type _ _).1 P.val.sheaf.property) W
  change P.val.res prod.snd (translateSection P p hp W ((twistedAction a).res f x)) =
    P.val.res prod.snd (P.val.res f (translateSection P p hp U x))
  rw [translateSection_res, restrict_comp, ← extendTest_snd, ← restrict_comp, translateSection_res]
  symm
  refine (torsorRes_act P ((extendTest V).map f)
    (P.val.res (prod.fst : V ⨯ U ⟶ V) p) (sectionValue x)).trans ?_
  rw [restrict_comp, extendTest_fst]
  rfl

private theorem translateSection_equivariant {U : FieldSite k}
    (x : (twistedAction a).Section U) (g : (fieldGroup H).obj (op U)) :
    translateSection P p hp U ((twistedAction a).act x g) =
      P.val.act (translateSection P p hp U x) g := by
  apply coverSnd_injective (K := K)
    ((isSheaf_iff_isSheaf_of_type _ _).1 P.val.sheaf.property) U
  change P.val.res prod.snd (translateSection P p hp U ((twistedAction a).act x g)) =
    P.val.res prod.snd (P.val.act (translateSection P p hp U x) g)
  rw [translateSection_res, torsorRes_act P (prod.snd : V ⨯ U ⟶ U) _ g,
    translateSection_res, P.val.act_mul]
  rfl

private def twistedActionIso : RightActionIso (twistedAction a) P.val where
  iso := ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U ↦ (Equiv.ofBijective _ (translateSection_bijective P p hp U.unop)).toIso)
    (fun f ↦ by
      apply ConcreteCategory.hom_ext
      intro x
      exact translateSection_natural P p hp f.unop x))
  equivariant := translateSection_equivariant P p hp

end DescentOfIsomorphisms

/-- Matching finite cocycles give an equivariant isomorphism over the base field. -/
theorem finiteIsomorphism : FiniteIsomorphism.{u} := by
  intro k K _ _ _ _ _ H P Q p q a hp hq
  exact ⟨(twistedActionIso (K := K) P p hp).symm.trans (twistedActionIso (K := K) Q q hq)⟩

/-- Right fppf torsors under a smooth affine algebraic group are classified by
continuous Galois cocycles over a separable closure. -/
theorem classification : Classification.{u} :=
  classificationOfFiniteResults finiteRealization finiteIsomorphism

section PowerFibers

open Polynomial

variable {k : Type u} [Field k]

private abbrev functionRestriction {U T : SchemeOver k} (f : U ⟶ T) :
    testFunctions T →ₐ[k] testFunctions U :=
  ((algΓ (CommRingCat.of k)).map f).unop.hom

private theorem rootCoordinate_natural {U T : SchemeOver k} {n : ℕ} {a : kˣ}
    (f : U ⟶ T) (x : T ⟶ (powerFiber n a).left) :
    rootCoordinate (f ≫ x) = functionRestriction f (rootCoordinate x) := by
  unfold rootCoordinate
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

private def rootCoordinateEquiv (n : ℕ) (a : kˣ) (T : SchemeOver k) :
    (T ⟶ (powerFiber n a).left) ≃
      {z : testFunctions T // z ^ n = algebraMap k (testFunctions T) (a : k)} := by
  let f : k[X] := X ^ n - C (a : k)
  let R := testFunctions T
  let A := (algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv T
    (op (CommAlgCat.of k (AdjoinRoot f)))
  refine A.symm.trans ?_
  refine
    { toFun := fun φ ↦ ⟨φ.unop.hom (AdjoinRoot.root f), ?_⟩
      invFun := fun z ↦ (CommAlgCat.ofHom
        (AdjoinRoot.liftAlgHom f (Algebra.ofId k R) z.val (by
          simpa [f, sub_eq_zero] using z.property))).op
      left_inv := ?_
      right_inv := ?_ }
  · have h := congrArg φ.unop.hom (AdjoinRoot.aeval_eq (f := f) f)
    rw [AdjoinRoot.mk_self, map_zero, ← aeval_algHom_apply] at h
    simpa [f, sub_eq_zero] using h
  · intro φ
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  · intro z
    apply Subtype.ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

private abbrev unityRoots (k : Type u) [Field k] (n : ℕ) :
    (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (rootsOfUnity n (testFunctions T.unop))
  map f := GrpCat.ofHom
    (((Units.map (functionRestriction f.unop).toMonoidHom).comp
      (rootsOfUnity n _).subtype).codRestrict _ (fun z ↦
        map_rootsOfUnity (Units.map (functionRestriction f.unop).toMonoidHom) n
          ⟨z.val, z.property, rfl⟩))
  map_id T := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Units.ext
    change functionRestriction (𝟙 T.unop) ↑x.val = ↑x.val
    simp [functionRestriction]
  map_comp f g := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Units.ext
    change functionRestriction (g.unop ≫ f.unop) ↑x.val =
      functionRestriction g.unop (functionRestriction f.unop ↑x.val)
    change ((algΓ (CommRingCat.of k)).map (g.unop ≫ f.unop)).unop.hom ↑x.val = _
    rw [Functor.map_comp]
    rfl

private def unityRepresentation (p : ℕ) [NeZero p] :
    (unityRoots k p ⋙ forget GrpCat).RepresentableBy (powerFiber p (1 : kˣ)).left where
  homEquiv {T} := by
    change (T ⟶ (powerFiber p (1 : kˣ)).left) ≃ rootsOfUnity p (testFunctions T)
    exact (rootCoordinateEquiv p 1 T).trans
      { toFun := fun z ↦ rootsOfUnity.mkOfPowEq z.val (by simpa using z.property)
        invFun := fun z ↦ ⟨z.val, by simpa using (mem_rootsOfUnity' p z.val).mp z.property⟩
        left_inv := fun z ↦ Subtype.ext rfl
        right_inv := fun z ↦ Subtype.ext (Units.ext rfl) }
  homEquiv_comp {U T} f g := by
    apply Subtype.ext
    apply Units.ext
    change rootCoordinate (f ≫ g) = functionRestriction f (rootCoordinate g)
    exact rootCoordinate_natural f g

private def unityGroup (k : Type u) [Field k] (p : ℕ) [NeZero p] : GroupScheme k :=
  letI := GrpObj.ofRepresentableBy _ (unityRoots k p) (unityRepresentation (k := k) p)
  Grp.mk (powerFiber p (1 : kˣ)).left

private def unityGroupPoints (p : ℕ) [NeZero p] (T : SchemeOver k) :
    (T ⟶ (unityGroup k p).X) ≃* rootsOfUnity p (testFunctions T) := by
  let H := unityGroup k p
  exact Iso.groupIsoToMulEquiv ((yonedaGrpObjIsoOfRepresentableBy H.X (unityRoots k p)
    (unityRepresentation (k := k) p)).app (op T))

private theorem unityGroupPoints_coord (p : ℕ) [NeZero p] (T : SchemeOver k)
    (g : T ⟶ (unityGroup k p).X) :
    ((unityGroupPoints p T g).val : testFunctions T) = rootCoordinate g := rfl

private theorem rootCoordinate_pow {n : ℕ} {a : kˣ} {T : SchemeOver k}
    (x : T ⟶ (powerFiber n a).left) :
    rootCoordinate x ^ n = algebraMap k (testFunctions T) (a : k) :=
  (rootCoordinateEquiv n a T x).property

private theorem rootCoordinate_injective {n : ℕ} {a : kˣ} {T : SchemeOver k} :
    Function.Injective (@rootCoordinate k _ n a T) :=
  fun _ _ h ↦ (rootCoordinateEquiv n a T).injective (Subtype.ext h)

private def powerAct (p : ℕ) [NeZero p] (a : kˣ) {T : Over (fieldBase k)}
    (x : T ⟶ powerFiber p a) (g : T.left ⟶ (unityGroup k p).X) : T ⟶ powerFiber p a :=
  Over.homMk ((rootCoordinateEquiv p a T.left).symm
    ⟨rootCoordinate x.left * rootCoordinate g, by
      rw [mul_pow, rootCoordinate_pow x.left, rootCoordinate_pow g, Units.val_one, map_one, mul_one]⟩)
    (Over.mkIdTerminal.hom_ext _ _)

private theorem powerAct_coord (p : ℕ) [NeZero p] (a : kˣ) {T : Over (fieldBase k)}
    (x : T ⟶ powerFiber p a) (g : T.left ⟶ (unityGroup k p).X) :
    rootCoordinate (powerAct p a x g).left = rootCoordinate x.left * rootCoordinate g :=
  congrArg Subtype.val ((rootCoordinateEquiv p a T.left).apply_symm_apply _)

private theorem unity_coord_one (p : ℕ) [NeZero p] (T : SchemeOver k) :
    rootCoordinate (1 : T ⟶ (unityGroup k p).X) = 1 := by
  rw [← unityGroupPoints_coord, map_one]
  rfl

private theorem unity_coord_mul (p : ℕ) [NeZero p] {T : SchemeOver k}
    (g h : T ⟶ (unityGroup k p).X) :
    rootCoordinate (g * h) = rootCoordinate g * rootCoordinate h := by
  rw [← unityGroupPoints_coord p T (g * h), map_mul]
  exact congrArg₂ (· * ·) (unityGroupPoints_coord p T g) (unityGroupPoints_coord p T h)

private def powerRightAction (p : ℕ) [NeZero p] (a : kˣ) :
    SchemeAction (fieldBase k) (unityGroup k p) where
  sheaf := representedSheaf (powerFiber p a)
  act x g := ⟨powerAct p a x.down g.down⟩
  act_one {T} x := by
    change ULift.up (powerAct p a x.down (1 : T.left ⟶ (unityGroup k p).X)) = x
    apply ULift.ext
    apply Over.OverMorphism.ext
    apply rootCoordinate_injective
    rw [powerAct_coord, unity_coord_one, mul_one]
  act_mul x g h := by
    apply ULift.ext
    apply Over.OverMorphism.ext
    apply rootCoordinate_injective
    rw [powerAct_coord, powerAct_coord, powerAct_coord, mul_assoc]
    exact congrArg (rootCoordinate x.down.left * ·) (unity_coord_mul p g.down h.down).symm
  map_act f x g := by
    apply ULift.ext
    apply Over.OverMorphism.ext
    apply rootCoordinate_injective
    change rootCoordinate (f.left ≫ (powerAct p a x.down g.down).left) =
      rootCoordinate (powerAct p a (f ≫ x.down) (f.left ≫ g.down)).left
    rw [rootCoordinate_natural, powerAct_coord, map_mul, powerAct_coord]
    rw [Over.comp_left, rootCoordinate_natural, rootCoordinate_natural]

private theorem powerRightAction_bijective (p : ℕ) [NeZero p] (a : kˣ)
    (T : Over (fieldBase k)) (x : (powerRightAction p a).Section T) :
    Function.Bijective ((powerRightAction p a).act x) := by
  let u := rootCoordinate x.down.left
  have hu : IsUnit u := (isUnit_pow_iff (NeZero.ne p)).mp (by
    change IsUnit (rootCoordinate x.down.left ^ p)
    rw [rootCoordinate_pow]
    exact a.isUnit.map (algebraMap k (testFunctions T.left)))
  constructor
  · intro g h he
    change ULift (T.left ⟶ (unityGroup k p).X) at g h
    have hh := congrArg (fun y : (powerRightAction p a).Section T ↦ rootCoordinate y.down.left) he
    change rootCoordinate (powerAct p a x.down g.down).left =
      rootCoordinate (powerAct p a x.down h.down).left at hh
    rw [powerAct_coord, powerAct_coord] at hh
    exact ULift.ext (rootCoordinate_injective (hu.mul_left_cancel hh))
  · intro y
    let v := rootCoordinate y.down.left
    let r : testFunctions T.left := ↑(hu.unit⁻¹) * v
    have hh : u * r = v := by
      change (↑hu.unit : testFunctions T.left) * (↑(hu.unit⁻¹) * v) = v
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    have hr : r ^ p = 1 := by
      have eq := congrArg (· ^ p) hh
      rw [mul_pow, show u ^ p = _ from rootCoordinate_pow x.down.left,
        show v ^ p = _ from rootCoordinate_pow y.down.left] at eq
      exact (a.isUnit.map (algebraMap k (testFunctions T.left))).mul_left_cancel
        (eq.trans (mul_one _).symm)
    let g : T.left ⟶ (unityGroup k p).X :=
      (rootCoordinateEquiv p 1 T.left).symm ⟨r, by simpa using hr⟩
    refine ⟨⟨g⟩, ULift.ext (Over.OverMorphism.ext (rootCoordinate_injective ?_))⟩
    change rootCoordinate (powerAct p a x.down g).left = v
    rw [powerAct_coord]
    have hg : rootCoordinate g = r :=
      congrArg Subtype.val ((rootCoordinateEquiv p 1 T.left).apply_symm_apply _)
    exact (congrArg (u * ·) hg).trans hh

/-- The finite flat power fiber has the right multiplication action of the
group of pth roots of unity. -/
theorem powerFiberTorsor : PowerFiberTorsor.{u} := by
  intro k _ p _ _ a ha
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  let f : k[X] := X ^ p - C (a : k)
  let : Fact (Irreducible f) := ⟨X_pow_sub_C_irreducible_of_prime hp ha⟩
  let : Module.Finite k (AdjoinRoot f) := (monic_X_pow_sub_C _ hp.ne_zero).finite_adjoinRoot
  let P := powerRightAction p a
  have hP : IsTorsor P := by
    refine ⟨powerRightAction_bijective p a, fun T ↦ ?_⟩
    let q := Over.mkIdTerminal.from (powerFiber p a)
    have hfppf : IsFppf q.left.left := by
      have hq : q.left = (powerFiber p a).hom :=
        Over.mkIdTerminal.hom_ext _ _
      rw [hq, fieldHom_left]
      have h := field_extension_fppf (k := k) (AdjoinRoot f)
      rw [fieldHom_left] at h
      exact h
    refine (torsorTopology (fieldBase k)).superset_covering (S := Sieve.pullback
      (Over.mkIdTerminal.from T) (Sieve.generate (Presieve.singleton q))) ?_
      ((torsorTopology (fieldBase k)).pullback_stable _ (covers_singleton q hfppf))
    rintro U g ⟨V, _, t, h, _⟩
    cases h
    exact ⟨⟨‹U ⟶ powerFiber p a›⟩⟩
  obtain ⟨A, e, he⟩ := Fppf.representSheafAction P (powerFiber p a) (Iso.refl _)
  refine ⟨unityGroup k p, Iso.refl _, A, (Fppf.torsorInvariantUnderIso e).mpr hP, ?_, ?_⟩
  · intro T g h
    simpa using And.intro (unity_coord_one p T) (unity_coord_mul p g h)
  · intro T x g
    have eq := e.equivariant (ULift.up x) g
    rw [he] at eq
    change (ULift.up (actionPair x g.down ≫ A.action) : ULift (T ⟶ powerFiber p a)) =
      ULift.up (powerAct p a x g.down) at eq
    have eq' : actionPair x g.down ≫ A.action = powerAct p a x g.down :=
      congrArg ULift.down eq
    rw [eq', powerAct_coord]
    simp

end PowerFibers

end

end LinearAlgebraicGroups.Descent.SmoothTorsors
