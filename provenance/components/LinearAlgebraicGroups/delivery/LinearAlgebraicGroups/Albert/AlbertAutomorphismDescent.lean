import Specs.LinearAlgebraicGroups.Albert.AlbertAutomorphismDescent
import LinearAlgebraicGroups.Albert.AutomorphismScheme
import LinearAlgebraicGroups.Albert.SplitModel
import LinearAlgebraicGroups.Albert.IntegralSmoothness
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Nullstellensatz

namespace LinearAlgebraicGroups.Albert.AutomorphismDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SplitSpecification IntegralSmoothnessSpecification AutomorphismDescentSpecification
open ShortDirectionSpecification (IntegralPresentation)
open SpinSpecification (SchemePoints)
open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticJordan)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open scoped TensorProduct CategoryTheory.MonObj

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open MonoidalCategory TensorProduct

abbrev baseSpec (R : Type) [CommRing R] := Spec (CommRingCat.of R)
abbrev scalarSpec (R : Type) [CommRing R] := algSpec (CommRingCat.of R)

private abbrev specMap (R S : Type) [CommRing R] [CommRing S] [Algebra R S] :
    baseSpec S ⟶ baseSpec R := Spec.map (CommRingCat.ofHom (algebraMap R S))

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
variable {M : Type} [AddCommGroup M] [Module R M]

open private pullbackPointEquiv pullbackPointEquiv_left pullbackPointEquiv_comp pullbackPointGroupEquiv
  from LinearAlgebraicGroups.Albert.IntegralSmoothness

private def testSpecIso (S : Type) [CommRing S] [Algebra B S]
    [Algebra R S] [IsScalarTower R B S] :
    (scalarSpec R).obj (op (CommAlgCat.of R S)) ≅
      (Over.map (specMap R B)).obj ((scalarSpec B).obj (op (CommAlgCat.of B S))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (specMap B S ≫ specMap R B) = specMap R S
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact (IsScalarTower.algebraMap_apply R B S r).symm)

private def changedPoints (G : SpinSpecification.GroupScheme R) (S : Type) [CommRing S] [Algebra B S]
    [Algebra R S] [IsScalarTower R B S] :
    SchemePoints ((groupChange R B).obj G) (CommAlgCat.of B S) ≃*
      SchemePoints G (CommAlgCat.of R S) :=
  (pullbackPointGroupEquiv (specMap R B) ((scalarSpec B).obj (op (CommAlgCat.of B S))) G).trans
    (((yonedaGrpObj G.X).mapIso (testSpecIso (R := R) (B := B) S).op).groupIsoToMulEquiv)

private theorem changedPoints_left (G : SpinSpecification.GroupScheme R) (S : Type) [CommRing S] [Algebra B S]
    [Algebra R S] [IsScalarTower R B S]
    (p : SchemePoints ((groupChange R B).obj G) (CommAlgCat.of B S)) :
    (changedPoints (B := B) G S p).left = p.left ≫ pullback.fst G.X.hom (specMap R B) := by
  change (𝟙 _ ≫ p.left ≫ pullback.fst G.X.hom (specMap R B)) = _
  exact Category.id_comp _

private theorem changedPoints_natural (G : SpinSpecification.GroupScheme R) {S T : CommAlgCat B}
    [Algebra R S] [Algebra R T] [IsScalarTower R B S] [IsScalarTower R B T] (f : S ⟶ T)
    (p : SchemePoints ((groupChange R B).obj G) S) :
    changedPoints (B := B) G T ((scalarSpec B).map f.op ≫ p) =
      (scalarSpec R).map (CommAlgCat.ofHom (f.hom.restrictScalars R)).op ≫ changedPoints (B := B) G S p := by
  apply Over.OverMorphism.ext
  simp only [changedPoints_left, Over.comp_left]
  exact Category.assoc _ _ _

private def conjugate {S U V : Type} [CommRing S] [AddCommGroup U] [Module S U]
    [AddCommGroup V] [Module S V] (e : U ≃ₗ[S] V) :
    (U ≃ₗ[S] U) ≃* (V ≃ₗ[S] V) where
  toFun g := e.symm.trans (g.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp [LinearEquiv.mul_apply]

private theorem conjugate_apply {S U V : Type} [CommRing S] [AddCommGroup U] [Module S U]
    [AddCommGroup V] [Module S V] (e : U ≃ₗ[S] V) (g : U ≃ₗ[S] U) (x : U) :
    conjugate e g (e x) = e (g x) := by
  change e (g (e.symm (e x))) = _
  rw [e.symm_apply_apply]

open _root_.Specs.LinearAlgebraicGroups.Albert
  (towerAlgebra iteratedTensorEquiv)
open private towerScalars iteratedTensorEquiv_natural
  from Specs.LinearAlgebraicGroups.Albert.QuadraticJordan
open private baseChange_cancel_op from LinearAlgebraicGroups.Albert.IntrinsicCubic

private theorem baseChangeRep (J : ParaQuadratic R M) {G : SpinSpecification.GroupScheme R}
    (h : RepresentsAutomorphisms J G) :
    RepresentsAutomorphisms (J.baseChange B) ((groupChange R B).obj G) := by
  obtain ⟨a, ha, hn⟩ := h
  let a' (S : CommAlgCat B) :
      SchemePoints ((groupChange R B).obj G) S →* (S ⊗[B] (B ⊗[R] M) ≃ₗ[S] S ⊗[B] (B ⊗[R] M)) :=
    letI := towerAlgebra R B S
    letI := towerScalars R B S
    let e := iteratedTensorEquiv (R := R) (S := B) (M := M) S
    (conjugate e.symm).toMonoidHom.comp ((a (CommAlgCat.of R S)).comp (changedPoints (B := B) G S).toMonoidHom)
  refine ⟨a', ?_, ?_⟩
  · intro S
    letI := towerAlgebra R B S
    letI := towerScalars R B S
    let e := iteratedTensorEquiv (R := R) (S := B) (M := M) S
    let t := changedPoints (B := B) G S
    refine ⟨(conjugate e.symm).injective.comp ((ha (CommAlgCat.of R S)).1.comp t.injective), ?_⟩
    have hu : e (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit)) = 1 ⊗ₜ[R] J.unit := by
      simp [e, iteratedTensorEquiv, AlgebraTensorModule.cancelBaseChange_tmul]
    have equiv (g : S ⊗[B] (B ⊗[R] M) ≃ₗ[S] S ⊗[B] (B ⊗[R] M)) :
        (g (1 ⊗ₜ[B] (J.baseChange B).unit) = 1 ⊗ₜ[B] (J.baseChange B).unit ∧
          ∀ x y, g ((J.baseChange B).op S x y) = (J.baseChange B).op S (g x) (g y)) ↔
        (conjugate e g (1 ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] J.unit ∧
          ∀ x y, conjugate e g (J.op S x y) = J.op S (conjugate e g x) (conjugate e g y)) := by
      have hop (x y) : e ((J.baseChange B).op S x y) = J.op S (e x) (e y) :=
        J.extendedOp_apply B S x y
      refine and_congr ?_ ⟨?_, ?_⟩
      · change g (1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit)) = 1 ⊗ₜ[B] (1 ⊗ₜ[R] J.unit) ↔ _
        rw [← hu, conjugate_apply, e.injective.eq_iff]
      · intro hh x y
        obtain ⟨x, rfl⟩ := e.surjective x
        obtain ⟨y, rfl⟩ := e.surjective y
        rw [← hop, conjugate_apply, conjugate_apply, conjugate_apply, hh, hop]
      · intro hh x y
        apply e.injective
        rw [hop, ← conjugate_apply, ← conjugate_apply e g x, ← conjugate_apply e g y, hop, hh]
    have hcancel (g) : conjugate e (conjugate e.symm g) = g := by ext x; simp [conjugate]
    have hcancel' (g) : conjugate e.symm (conjugate e g) = g := by ext x; simp [conjugate]
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      apply (equiv _).2
      change (conjugate e (conjugate e.symm (a _ (t p)))) _ = _ ∧ _
      simp only [show a' S p = conjugate e.symm (a _ (t p)) from rfl, hcancel]
      have hmem : a (CommAlgCat.of R S) (t p) ∈ Set.range (a (CommAlgCat.of R S)) := ⟨_, rfl⟩
      rwa [(ha (CommAlgCat.of R S)).2] at hmem
    · intro hg
      have hmem := (equiv g).1 hg
      have h' : conjugate e g ∈ Set.range (a (CommAlgCat.of R S)) := by
        rw [(ha (CommAlgCat.of R S)).2]
        exact hmem
      obtain ⟨p, hp⟩ := h'
      refine ⟨t.symm p, ?_⟩
      change conjugate e.symm (a _ (t (t.symm p))) = g
      rw [t.apply_symm_apply, hp, hcancel']
  · intro S T f p x
    letI := towerAlgebra R B S
    letI := towerAlgebra R B T
    letI := towerScalars R B S
    letI := towerScalars R B T
    let eS := iteratedTensorEquiv (R := R) (S := B) (M := M) S
    let eT := iteratedTensorEquiv (R := R) (S := B) (M := M) T
    let fr : CommAlgCat.of R S ⟶ CommAlgCat.of R T := CommAlgCat.ofHom (f.hom.restrictScalars R)
    have ht (y : S ⊗[B] (B ⊗[R] M)) :
        eT (f.hom.toLinearMap.rTensor (B ⊗[R] M) y) =
          fr.hom.toLinearMap.rTensor M (eS y) := iteratedTensorEquiv_natural f.hom y
    have act (U : CommAlgCat B) (p : SchemePoints ((groupChange R B).obj G) U)
        (y : U ⊗[B] (B ⊗[R] M)) :
        letI := towerAlgebra R B U
        letI := towerScalars R B U
        let e := iteratedTensorEquiv (R := R) (S := B) (M := M) U
        e (a' U p y) = a (CommAlgCat.of R U) (changedPoints (B := B) G U p) (e y) := by
      letI := towerAlgebra R B U
      letI := towerScalars R B U
      let e := iteratedTensorEquiv (R := R) (S := B) (M := M) U
      change e (e.symm (a (CommAlgCat.of R U) (changedPoints (B := B) G U p) (e y))) = _
      exact e.apply_symm_apply _
    apply eT.injective
    change eT (f.hom.toLinearMap.rTensor _ (a' S p x)) =
      eT (a' T ((scalarSpec B).map f.op ≫ p) (f.hom.toLinearMap.rTensor _ x))
    rw [ht, act S, act T, ht, changedPoints_natural]
    exact hn fr (changedPoints (B := B) G S p) (eS x)

private theorem affineRepresentation (J : ParaQuadratic R M) (h : IsFreudenthal J) :
    ∃ G : SpinSpecification.GroupScheme R, IsAffine G.X.left ∧ RepresentsAutomorphisms J G := by
  have ⟨hf, hp⟩ := freudenthal_finite_projective J h
  letI := hf
  letI := hp
  let q : QuadraticJordan R M :=
    { toQuadraticOperatorLaw := J.toQuadraticOperatorLaw
      unit := J.unit
      op_unit := J.op_unit
      fundamental := fun S _ _ => (freudenthal_is_jordan J h S).1
      commuting := fun S _ _ => (freudenthal_is_jordan J h S).2 }
  obtain ⟨g⟩ := LinearAlgebraicGroups.Albert.Automorphisms.quadraticAutomorphismScheme q
  let a (S : CommAlgCat R) := (LinearMap.GeneralLinearGroup.generalLinearEquiv S _).toMonoidHom.comp
    ((quadraticStabilizer q S).subtype.comp (g.subgroupPoints S).toMonoidHom)
  refine ⟨g.group, g.groupAffine, a, ?_, ?_⟩
  · intro S
    refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv S _).injective.comp
      (Subtype.val_injective.comp (g.subgroupPoints S).injective), ?_⟩
    ext b
    constructor
    · rintro ⟨p, rfl⟩
      exact (mem_quadraticStabilizer _ _ _).1 ((g.subgroupPoints S p).property)
    · intro hb
      let b' := (LinearMap.GeneralLinearGroup.generalLinearEquiv S _).symm b
      have hb' : b' ∈ quadraticStabilizer q S :=
        (mem_quadraticStabilizer _ _ _).2 hb
      refine ⟨(g.subgroupPoints S).symm ⟨b', hb'⟩, ?_⟩
      change (LinearMap.GeneralLinearGroup.generalLinearEquiv S _)
        (g.subgroupPoints S ((g.subgroupPoints S).symm ⟨b', hb'⟩)).val = _
      rw [MulEquiv.apply_symm_apply]
      exact MulEquiv.apply_symm_apply _ _
  · intro S T f p x
    let j := (schemePoints R).map g.inclusion
    have hh := g.scalarChange f (j.app S p) x
    have hh' : ((schemePoints R).obj g.generalLinear).map f (j.app S p) =
        j.app T (((schemePoints R).obj g.group).map f p) :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (j.naturality f)).symm p
    change (g.linearPoints T (((schemePoints R).obj g.generalLinear).map f
        (((schemePoints R).map g.inclusion).app S p))).val _ =
      f.hom.toLinearMap.rTensor M ((g.linearPoints S (((schemePoints R).map g.inclusion).app S p)).val x) at hh
    rw [hh', g.evaluatesInclusion, g.evaluatesInclusion] at hh
    exact hh.symm

private theorem affinePoint_ext {X Y : Over (baseSpec R)} (hX : IsAffine X.left)
    {f g : X ⟶ Y}
    (h : ∀ (S : CommAlgCat R) (p : (scalarSpec R).obj (op S) ⟶ X), p ≫ f = p ≫ g) :
    f = g := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hX
  exact (cancel_epi e.hom).mp (h A.unop e.hom)

open CategoryTheory.CartesianMonoidalCategory in
private theorem affinePoint_iso {G H : SpinSpecification.GroupScheme R}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (a : ∀ S : CommAlgCat R, SchemePoints G S ≃* SchemePoints H S)
    (ha : ∀ {S T : CommAlgCat R} (f : S ⟶ T) (p : SchemePoints G S),
      a T ((scalarSpec R).map f.op ≫ p) = (scalarSpec R).map f.op ≫ a S p) :
    Nonempty (G ≅ H) := by
  have liftMap {E F : SpinSpecification.GroupScheme R} (hE : IsAffine E.X.left)
      (b : ∀ S : CommAlgCat R, SchemePoints E S ≃* SchemePoints F S)
      (hb : ∀ {S T : CommAlgCat R} (f : S ⟶ T) (p : SchemePoints E S),
        b T ((scalarSpec R).map f.op ≫ p) = (scalarSpec R).map f.op ≫ b S p) :
      ∃ j : E ⟶ F, ∀ (S : CommAlgCat R) (p : SchemePoints E S), p ≫ j.hom.hom = b S p := by
    obtain ⟨C, ⟨e⟩⟩ := essImage_algSpec.mpr hE
    let j := e.inv ≫ b C.unop e.hom
    have he (S : CommAlgCat R) (p : SchemePoints E S) : p ≫ j = b S p := by
      let q := p ≫ e.inv
      let f := (algSpec.fullyFaithful (R := CommRingCat.of R)).preimage q
      have hq : (scalarSpec R).map f = q := (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage q
      have hn := (hb f.unop e.hom).symm
      change (scalarSpec R).map f ≫ b C.unop e.hom =
        b S ((scalarSpec R).map f ≫ e.hom) at hn
      simpa only [hq, Category.assoc, Iso.inv_hom_id, Category.comp_id, j, q] using hn
    let j' : E ⟶ F := Grp.homMk'' j (by
      apply affinePoint_ext (X := 𝟙_ (Over (baseSpec R))) (by
        change IsAffine (baseSpec R)
        infer_instance)
      intro S p
      rw [show p = toUnit _ from toUnit_unique _ _, ← Category.assoc]
      exact (he S 1).trans (map_one (b S))) (by
      letI := hE
      apply affinePoint_ext (X := E.X ⊗ E.X) (by
        change IsAffine (pullback E.X.hom E.X.hom)
        infer_instance)
      intro S p
      let x := p ≫ fst E.X E.X
      let y := p ≫ snd E.X E.X
      have hxy : lift x y = p := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
      have hxy' : lift (x ≫ j) (y ≫ j) = p ≫ (j ⊗ₘ j) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
      calc
        p ≫ μ[E.X] ≫ j = (x * y) ≫ j := by rw [CategoryTheory.Hom.mul_def, hxy, Category.assoc]
        _ = (x ≫ j) * (y ≫ j) := by rw [he, map_mul, ← he, ← he]
        _ = p ≫ (j ⊗ₘ j) ≫ μ[F.X] := by rw [CategoryTheory.Hom.mul_def, hxy', Category.assoc])
    exact ⟨j', he⟩
  obtain ⟨j, hj⟩ := liftMap hG a @ha
  obtain ⟨i, hi⟩ := liftMap hH (fun S => (a S).symm) (by
    intro S T f p
    apply (a T).injective
    rw [(a T).apply_symm_apply, ha, (a S).apply_symm_apply])
  refine ⟨⟨j, i, ?_, ?_⟩⟩
  · apply Grp.hom_ext
    apply affinePoint_ext hG
    intro S p
    change p ≫ j.hom.hom ≫ i.hom.hom = p ≫ 𝟙 G.X
    rw [← Category.assoc, hj, hi, (a S).symm_apply_apply, Category.comp_id]
  · apply Grp.hom_ext
    apply affinePoint_ext hH
    intro S p
    change p ≫ i.hom.hom ≫ j.hom.hom = p ≫ 𝟙 H.X
    rw [← Category.assoc, hi, hj, (a S).apply_symm_apply, Category.comp_id]

private theorem tensorGenerator_ext {S U : Type} [CommRing S] [Algebra R S]
    [AddCommGroup U] [Module S U] {f g : S ⊗[R] M →ₗ[S] U}
    (h : ∀ m, f (1 ⊗ₜ[R] m) = g (1 ⊗ₜ[R] m)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul s m =>
    rw [show s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, map_smul, h]

private theorem comparisonIso (J : ParaQuadratic R M) {G H : SpinSpecification.GroupScheme R}
    (hG : IsAffine G.X.left) (hH : IsAffine H.X.left)
    (h : RepresentsAutomorphisms J G) (h' : RepresentsAutomorphisms J H) :
    Nonempty (G ≅ H) := by
  obtain ⟨a, ha, na⟩ := h
  obtain ⟨b, hb, nb⟩ := h'
  let rangeEquiv {U V : Type} [Group U] [Group V] (f : U →* V) (hf : Function.Injective f) :
      U ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
        ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hr (S : CommAlgCat R) : (a S).range = (b S).range :=
    SetLike.coe_injective ((ha S).2.trans (hb S).2.symm)
  let e (S : CommAlgCat R) : SchemePoints G S ≃* SchemePoints H S :=
    (rangeEquiv (a S) (ha S).1).trans
      ((MulEquiv.subgroupCongr (hr S)).trans (rangeEquiv (b S) (hb S).1).symm)
  have he (S : CommAlgCat R) (p : SchemePoints G S) : b S (e S p) = a S p := by
    exact congrArg Subtype.val ((rangeEquiv (b S) (hb S).1).apply_symm_apply
      (MulEquiv.subgroupCongr (hr S) (rangeEquiv (a S) (ha S).1 p)))
  apply affinePoint_iso hG hH e
  intro S T f p
  apply (hb T).1
  rw [he]
  apply LinearEquiv.toLinearMap_injective
  apply tensorGenerator_ext
  intro m
  have hm : f.hom.toLinearMap.rTensor M (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m := by simp
  have h1 := na f p (1 ⊗ₜ[R] m)
  have h2 := nb f (e S p) (1 ⊗ₜ[R] m)
  dsimp only at h1 h2
  rw [hm] at h1 h2
  exact h1.symm.trans ((congrArg (fun g : S ⊗[R] M ≃ₗ[S] S ⊗[R] M =>
    f.hom.toLinearMap.rTensor M (g (1 ⊗ₜ[R] m))) (he S p)).symm.trans h2)

open TrialitySpecification (Model modelOp mapModel modelBaseChange)
open IntrinsicCubicSpecification (SplitChart)
open private extendChart extendChart_apply from LinearAlgebraicGroups.Albert.IntrinsicCubic
open CubicSpecification (cubicUnit)
open LowerRankSpecification (untwisted)
open QuadraticOperatorSpecification (applyOperator)

open private ground_operator from LinearAlgebraicGroups.Albert.QuadraticOperators
open private modelBaseChange_operator modelBaseChange_tmul mapModel_unit
  from LinearAlgebraicGroups.Albert.IntrinsicCubic
open private modelBaseChange_natural from LinearAlgebraicGroups.Albert.ShortDirections
open private changeScalar_linear from LinearAlgebraicGroups.Albert.AutomorphismScheme

set_option maxHeartbeats 900000 in
private theorem splitRep {P : IntegralPresentation} (L : SplitGroup P)
    (J : ParaQuadratic R M) (h : IsSplitModel J .octonion) :
    RepresentsAutomorphisms J ((groupChange ℤ R).obj L.group) := by
  letI (S : CommAlgCat R) : IsScalarTower ℤ R S := IsScalarTower.of_algebraMap_eq'
    (by ext n; exact (map_intCast (algebraMap R S) n).symm)
  obtain ⟨e₀, hu, ho⟩ := h
  let K := ParaQuadratic.ofJordan (weightedHermitianJordan (untwisted R)
    (Composition.Zorn.isOctonion R))
  have he₀ := (J.isIso_iff_ground K e₀).2
    ⟨hu, fun x y => (ho x y).trans (ground_operator _ _ _ _).symm⟩
  let d (S : CommAlgCat R) : SplitChart J S :=
    { coordinates := (e₀.baseChange R S M (Model R)).trans (modelBaseChange R S)
      unit := by
        rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, hu,
          show modelBaseChange R S (1 ⊗ₜ[R] (cubicUnit : Model R)) =
            (1 : S) • mapModel (algebraMap R S) cubicUnit from modelBaseChange_tmul _ _,
          one_smul]
        exact mapModel_unit _
      op := fun x y => by
        simp only [LinearEquiv.trans_apply]
        rw [show e₀.baseChange R S M (Model R) (J.op S x y) =
          K.op S (e₀.baseChange R S M (Model R) x) (e₀.baseChange R S M (Model R) y)
          from he₀.2 S x y]
        exact modelBaseChange_operator _ _ }
  let t (S : CommAlgCat R) :
      SchemePoints ((groupChange ℤ R).obj L.group) S ≃*
        SchemePoints L.group (CommAlgCat.of ℤ S) := changedPoints (B := R) L.group S
  let a (S : CommAlgCat R) :
      SchemePoints ((groupChange ℤ R).obj L.group) S →* (S ⊗[R] M ≃ₗ[S] S ⊗[R] M) :=
    (conjugate (d S).coordinates.symm).toMonoidHom.comp
      ((L.action (CommAlgCat.of ℤ S)).comp (t S).toMonoidHom)
  have act (S : CommAlgCat R) (p : SchemePoints ((groupChange ℤ R).obj L.group) S)
      (x : S ⊗[R] M) :
      (d S).coordinates (a S p x) =
        L.action (CommAlgCat.of ℤ S) (changedPoints (B := R) L.group S p) ((d S).coordinates x) := by
    change (d S).coordinates ((d S).coordinates.symm
      (L.action (CommAlgCat.of ℤ S) (changedPoints (B := R) L.group S p) ((d S).coordinates x))) = _
    exact (d S).coordinates.apply_symm_apply _
  have dn {S T : CommAlgCat R} (f : S ⟶ T) (x : S ⊗[R] M) :
      (d T).coordinates (f.hom.toLinearMap.rTensor M x) =
        mapModel f.hom.toRingHom ((d S).coordinates x) := by
    change modelBaseChange R T (e₀.toLinearMap.baseChange T (f.hom.toLinearMap.rTensor M x)) =
      mapModel f.hom.toRingHom (modelBaseChange R S (e₀.toLinearMap.baseChange S x))
    rw [← changeScalar_linear, modelBaseChange_natural]
  refine ⟨a, ?_, ?_⟩
  · intro S
    let e := d S
    refine ⟨?_, ?_⟩
    · intro p q hpq
      have hs := (conjugate e.coordinates.symm).injective hpq
      exact (t S).injective ((L.injective (CommAlgCat.of ℤ S)) hs)
    have hop (x y : S ⊗[R] M) : e.coordinates (J.op S x y) =
        modelOp (e.coordinates x) (e.coordinates y) := e.op x y
    have equiv (g : S ⊗[R] M ≃ₗ[S] S ⊗[R] M) :
        (g (1 ⊗ₜ[R] J.unit) = 1 ⊗ₜ[R] J.unit ∧
          ∀ x y, g (J.op S x y) = J.op S (g x) (g y)) ↔
        IdempotentSpecification.IsSplitAutomorphism (conjugate e.coordinates g) := by
      unfold IdempotentSpecification.IsSplitAutomorphism
      refine and_congr ?_ ⟨?_, ?_⟩
      · rw [← e.unit, conjugate_apply, e.coordinates.injective.eq_iff]
      · intro hg x y
        obtain ⟨x, rfl⟩ := e.coordinates.surjective x
        obtain ⟨y, rfl⟩ := e.coordinates.surjective y
        rw [← hop, conjugate_apply, conjugate_apply, conjugate_apply, hg, hop]
      · intro hg x y
        apply e.coordinates.injective
        have hh := hg (e.coordinates x) (e.coordinates y)
        rw [conjugate_apply, conjugate_apply] at hh
        rw [← hop, conjugate_apply, ← hop] at hh
        exact hh
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      apply (equiv _).2
      have he : conjugate e.coordinates (a S p) = L.action (CommAlgCat.of ℤ S) (t S p) := by
        apply LinearEquiv.ext
        intro y
        obtain ⟨x, rfl⟩ := e.coordinates.surjective y
        rw [conjugate_apply]
        exact act S p x
      rw [he]
      have hm : L.action (CommAlgCat.of ℤ S) (t S p) ∈ Set.range (L.action (CommAlgCat.of ℤ S)) := ⟨_, rfl⟩
      rwa [L.image] at hm
    · intro hg
      have hm : conjugate e.coordinates g ∈ Set.range (L.action (CommAlgCat.of ℤ S)) := by
        rw [L.image]
        exact (equiv g).1 hg
      obtain ⟨p, hp⟩ := hm
      refine ⟨(t S).symm p, ?_⟩
      apply LinearEquiv.ext
      intro x
      apply e.coordinates.injective
      rw [act]
      change L.action (CommAlgCat.of ℤ S) (t S ((t S).symm p)) _ = _
      rw [(t S).apply_symm_apply, hp, conjugate_apply]
  · intro S T f p x
    apply (d T).coordinates.injective
    change (d T).coordinates (f.hom.toLinearMap.rTensor _ (a S p x)) =
      (d T).coordinates (a T ((scalarSpec R).map f.op ≫ p) (f.hom.toLinearMap.rTensor _ x))
    rw [dn, act, act, dn, changedPoints_natural]
    exact L.natural (CommAlgCat.ofHom (f.hom.restrictScalars ℤ)) _ _

private theorem changeAffine {G : SpinSpecification.GroupScheme R} (hG : IsAffine G.X.left) :
    IsAffine ((groupChange R B).obj G).X.left := by
  letI := hG
  change IsAffine (pullback G.X.hom (specMap R B))
  infer_instance

private theorem splitComparison {P : IntegralPresentation} (L : SplitGroup P)
    {G : SpinSpecification.GroupScheme R} (hG : IsAffine G.X.left) (J : ParaQuadratic R M)
    (h : RepresentsAutomorphisms J G) (hJ : IsSplitModel J .octonion) :
    Nonempty (G ≅ (groupChange ℤ R).obj L.group) :=
  comparisonIso J hG (changeAffine L.affine) h (splitRep L J hJ)

private theorem flatSurjective [Module.FaithfullyFlat R B] :
    Flat (specMap R B) ∧ Surjective (specMap R B) :=
  (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).2
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

private theorem smoothOfIso {G H : SpinSpecification.GroupScheme R} (e : G ≅ H)
    (h : Smooth H.X.hom) : Smooth G.X.hom := by
  let i := ((Over.forget (baseSpec R)).mapIso (Grp.forget _ |>.mapIso e)).hom
  have hi : i ≫ H.X.hom = G.X.hom := Over.w e.hom.hom.hom
  rw [← hi]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) i _).2 h

private theorem connectedOfIso {G H : SpinSpecification.GroupScheme R} (e : G ≅ H)
    (h : GeometricallyConnected H.X.hom) : GeometricallyConnected G.X.hom := by
  let i := ((Over.forget (baseSpec R)).mapIso (Grp.forget _ |>.mapIso e)).hom
  have hi : i ≫ H.X.hom = G.X.hom := Over.w e.hom.hom.hom
  rw [← hi]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected) i _).2 h

private theorem connectedDescent {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hg : Surjective g) (h : GeometricallyConnected (pullback.snd f g)) :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ x
  letI : Surjective (pullback.fst x g) := MorphismProperty.pullback_fst x g hg
  obtain ⟨q, _⟩ := (pullback.fst x g).surjective (IsLocalRing.closedPoint K)
  let L := (pullback x g).residueField q
  let t : Spec (CommRingCat.of L) ⟶ pullback x g := (pullback x g).fromSpecResidueField q
  let k := t ≫ pullback.fst x g
  let b := t ≫ pullback.snd x g
  have eq : k ≫ x = b ≫ g := by simp only [k, b, Category.assoc, pullback.condition]
  haveI : Surjective k := ⟨fun s => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  haveI : ConnectedSpace ↥(pullback (pullback.snd f g) b) :=
    pullback_of_geometrically h.geometrically_connectedSpace L b
  haveI : ConnectedSpace ↥(pullback f (b ≫ g)) :=
    (pullbackLeftPullbackSndIso f g b).hom.homeomorph.connectedSpace_iff.mp inferInstance
  haveI : ConnectedSpace ↥(pullback f (k ≫ x)) := eq ▸ inferInstanceAs (ConnectedSpace ↥(pullback f (b ≫ g)))
  haveI : ConnectedSpace ↥(pullback (pullback.snd f x) k) :=
    (pullbackLeftPullbackSndIso f x k).hom.homeomorph.connectedSpace_iff.mpr inferInstance
  let p := pullback.fst (pullback.snd f x) k
  have hp : Surjective p := MorphismProperty.pullback_fst _ _ inferInstance
  exact hp.surj.connectedSpace p.continuous

private theorem centerlessOfIso {G H : SpinSpecification.GroupScheme R} (e : G ≅ H)
    (h : IsCenterless H) : IsCenterless G := by
  intro X z hz
  let i := e.hom.hom.hom
  let j := e.inv.hom.hom
  have hji : j ≫ i = 𝟙 _ := by
    exact congrArg (fun f : H ⟶ H => f.hom.hom) e.inv_hom_id
  have hc : z ≫ i = 1 := h X (z ≫ i) (by
    intro Y f g
    have he := congrArg (fun p : Y ⟶ G.X => p ≫ i) (hz Y f (g ≫ j))
    simpa only [MonObj.mul_comp, Category.assoc, hji, Category.comp_id, i] using he)
  have hi : IsIso i := by
    change IsIso ((Grp.forget (Over (baseSpec R))).map e.hom)
    infer_instance
  apply (cancel_mono i).mp
  rw [hc]
  exact (MonObj.one_comp i).symm

private theorem centerlessDescent {G : SpinSpecification.GroupScheme R} [Module.FaithfullyFlat R B]
    (h : IsCenterless ((groupChange R B).obj G)) : IsCenterless G := by
  intro X z hz
  let f := specMap R B
  let F := Over.pullback f
  let w : F.obj X ⟶ ((groupChange R B).obj G).X := F.map z
  let d : (Over.map f).obj (F.obj X) ⟶ X := (Over.mapPullbackAdj f).counit.app X
  have hd : d.left = pullback.fst X.hom f := rfl
  have hwp : ∀ (Y : Over (baseSpec B)) (a : Y ⟶ F.obj X),
      pullbackPointGroupEquiv f Y G (a ≫ w) =
        ((Over.map f).map a ≫ d) ≫ z := by
    intro Y a
    apply Over.OverMorphism.ext
    change (pullbackPointEquiv f Y G.X (a ≫ F.map z)).left = _
    rw [pullbackPointEquiv_comp]
    rfl
  have hw : w = 1 := h (F.obj X) w (by
    intro Y a g
    let Q := pullbackPointGroupEquiv f Y G
    apply Q.injective
    rw [map_mul, map_mul, hwp]
    exact hz _ _ (Q g))
  have he := hwp (F.obj X) (𝟙 _)
  simp only [Category.id_comp, hw, map_one] at he
  have hi : (Over.map f).map (𝟙 (F.obj X)) = 𝟙 _ :=
    (Over.map f).map_id (F.obj X)
  rw [hi, Category.id_comp] at he
  letI := (flatSurjective (R := R) (B := B)).1
  letI := (flatSurjective (R := R) (B := B)).2
  haveI : Epi d.left := by
    rw [hd]
    exact Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  apply (cancel_epi d.left).mp
  have he' : d ≫ z = d ≫ (1 : X ⟶ G.X) := by rw [MonObj.comp_one, ← he]
  exact congrArg Over.Hom.left he'

private theorem propertiesFromCover {P : IntegralPresentation} (L : SplitGroup P)
    (J : ParaQuadratic R M) {G : SpinSpecification.GroupScheme R}
    (hG : IsAffine G.X.left) (h : RepresentsAutomorphisms J G)
    [Module.FaithfullyFlat R B] (hJ : OnComponent J B .octonion) :
    (Smooth L.group.X.hom → Smooth G.X.hom) ∧
    (GeometricallyConnected L.group.X.hom → GeometricallyConnected G.X.hom) ∧
    (IsCenterless ((groupChange ℤ B).obj L.group) → IsCenterless G) := by
  obtain ⟨e⟩ := splitComparison L (changeAffine hG) (J.baseChange B) (baseChangeRep J h)
    ((ParaQuadratic.isSplitModel_baseChange_iff J B .octonion).2 hJ)
  have smooth (hL : Smooth L.group.X.hom) : Smooth G.X.hom := by
    have hB : Smooth (pullback.snd L.group.X.hom (specMap ℤ B)) := inferInstance
    have hG' : Smooth (pullback.snd G.X.hom (specMap R B)) :=
      smoothOfIso e hB
    have ⟨hf, hs⟩ := flatSurjective (R := R) (B := B)
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨hs, hf⟩, inferInstance⟩ hG'
  have connected (hL : GeometricallyConnected L.group.X.hom) :
      GeometricallyConnected G.X.hom := by
    have hB : GeometricallyConnected (pullback.snd L.group.X.hom (specMap ℤ B)) := inferInstance
    exact connectedDescent _ _ (flatSurjective (R := R) (B := B)).2 (connectedOfIso e hB)
  exact ⟨smooth, connected, fun hc => centerlessDescent (R := R) (B := B) (centerlessOfIso e hc)⟩

/-- The automorphism scheme is affine and finitely presented over the original base.
On all scalar algebras its action is the base-changed quadratic automorphism action. -/
theorem automorphismRepresentation : RepresentationType := by
  intro R M _ _ _ J hJ
  obtain ⟨G, hG, h⟩ := affineRepresentation J hJ.1
  obtain ⟨B, _, _, hff, hB⟩ := (albert_iff_split_octonion_after_cover J).1 hJ
  obtain ⟨P, L, hL, _, _⟩ := IntegralSmoothness.integralGeometry
  have hS : Smooth G.X.hom :=
    (propertiesFromCover L J hG h hB).1 hL.smooth
  exact ⟨G, hG, inferInstance, h, fun _ _ _ => baseChangeRep J h⟩

private theorem finiteTypePoint (K A : Type) [Field K] [IsAlgClosed K] [CommRing A]
    [Nontrivial A] [Algebra K A] [Algebra.FiniteType K A] : Nonempty (A →ₐ[K] K) := by
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := K) (S := A)).1
    inferInstance
  obtain ⟨m, hm, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal A) bot_ne_top
  let I := Ideal.comap f.toRingHom m
  have hI : I.IsMaximal := Ideal.comap_isMaximal_of_surjective f.toRingHom hf
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hI
  refine ⟨AlgHom.liftOfSurjective f hf (MvPolynomial.aeval x) ?_⟩
  intro p hp
  have hp' : p ∈ I := by
    change f p ∈ m
    rw [show f p = 0 from hp]
    exact m.zero_mem
  rw [hx] at hp'
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff _ _).mp hp'

open private matrixCoordinateEquiv matrixActionEquiv matrixAction_natural basisChange_natural
  from LinearAlgebraicGroups.Albert.AutomorphismScheme

section Specialization

variable {K : Type} [Field K] [IsAlgClosed K]
variable {U V : Type} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
variable [Module.Finite K U] [Module.Finite K V]

/-- The isomorphism equations on a determinant localization have a rational solution
over an algebraically closed field as soon as they have a solution over an extension. -/
private theorem lawIsoOfExtension (J : ParaQuadratic K U) (J' : ParaQuadratic K V)
    (F : Type) [Field F] [Algebra K F]
    (eF : F ⊗[K] U ≃ₗ[F] F ⊗[K] V)
    (hu : eF (1 ⊗ₜ[K] J.unit) = 1 ⊗ₜ[K] J'.unit)
    (hp : ∀ x y, eF (J.op F x y) = J'.op F (eF x) (eF y)) :
    ∃ e : U ≃ₗ[K] V, J.IsGroundIso J' e := by
  classical
  have hd : Module.finrank K U = Module.finrank K V := by
    exact (Module.finrank_baseChange (R := F) (S := K) (M' := U)).symm.trans
      (eF.finrank_eq.trans (Module.finrank_baseChange (R := F) (S := K) (M' := V)))
  let d := LinearEquiv.ofFinrankEq U V hd
  let n := Fin (Module.finrank K U)
  let b : Module.Basis n K U := Module.finBasis K U
  let b' : Module.Basis n K V := b.map d
  let C := MatrixCoordinates K n
  let genericMatrixUnit : Matrix.GeneralLinearGroup n C := matrixCoordinateEquiv (AlgHom.id K C)
  let m (S : Type) [CommRing S] [Algebra K S] :
      Matrix.GeneralLinearGroup n S ≃* (S ⊗[K] U ≃ₗ[S] S ⊗[K] U) :=
    (matrixActionEquiv b S).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv S _)
  let a (S : Type) [CommRing S] [Algebra K S] (g : Matrix.GeneralLinearGroup n S) :=
    (m S g).trans (d.baseChange K S U V)
  have nat {S T : Type} [CommRing S] [CommRing T] [Algebra K S] [Algebra K T] (f : S →ₐ[K] T)
      (g : Matrix.GeneralLinearGroup n S) (x : S ⊗[K] U) :
      f.toLinearMap.rTensor V (a S g x) =
        a T (Matrix.GeneralLinearGroup.map f.toRingHom g) (f.toLinearMap.rTensor U x) := by
    change f.toLinearMap.rTensor V (d.toLinearMap.baseChange S (matrixAction b S g x)) =
      d.toLinearMap.baseChange T (matrixAction b T (Matrix.GeneralLinearGroup.map f.toRingHom g)
        (f.toLinearMap.rTensor U x))
    rw [changeScalar_linear, matrixAction_natural]
  have gen {S : Type} [CommRing S] [Algebra K S] (f : C →ₐ[K] S) :
      Matrix.GeneralLinearGroup.map f.toRingHom genericMatrixUnit = matrixCoordinateEquiv f := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change f ((AlgHom.id K C) (coordinateMatrix (R := K) i j)) = f (coordinateMatrix (R := K) i j)
    rfl
  let eu (S : Type) [CommRing S] [Algebra K S] (g : Matrix.GeneralLinearGroup n S) :=
    a S g (1 ⊗ₜ[K] J.unit) - (1 ⊗ₜ[K] J'.unit : S ⊗[K] V)
  let ep (S : Type) [CommRing S] [Algebra K S] (g : Matrix.GeneralLinearGroup n S) (x y : U) :=
    a S g (J.op S (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y)) -
      J'.op S (a S g (1 ⊗ₜ[K] x)) (a S g (1 ⊗ₜ[K] y))
  have enu {S : Type} [CommRing S] [Algebra K S] (f : C →ₐ[K] S) :
      f.toLinearMap.rTensor V (eu C genericMatrixUnit) = eu S (matrixCoordinateEquiv f) := by
    simp only [eu, map_sub, nat, gen, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  have enp {S : Type} [CommRing S] [Algebra K S] (f : C →ₐ[K] S) (x y : U) :
      f.toLinearMap.rTensor V (ep C genericMatrixUnit x y) = ep S (matrixCoordinateEquiv f) x y := by
    simp only [ep, map_sub, nat, gen, J.natural, J'.natural, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_one]
  let p₀ (i : n) : C := (b'.baseChange C).repr (eu C genericMatrixUnit) i
  let p₁ (z : U × U × n) : C := (b'.baseChange C).repr (ep C genericMatrixUnit z.1 z.2.1) z.2.2
  let I : Ideal C := Ideal.span (Set.range p₀ ∪ Set.range p₁)
  let gF := (m F).symm (eF.trans (d.baseChange K F U V).symm)
  let fF : C →ₐ[K] F := matrixCoordinateEquiv.symm gF
  have hF : a F (matrixCoordinateEquiv fF) = eF := by
    change ((m F) (matrixCoordinateEquiv fF)).trans (d.baseChange K F U V) = _
    rw [show matrixCoordinateEquiv fF = gF from Equiv.apply_symm_apply _ _]
    rw [show m F gF = eF.trans (d.baseChange K F U V).symm from MulEquiv.apply_symm_apply _ _]
    apply LinearEquiv.ext
    intro x
    exact (d.baseChange K F U V).apply_symm_apply (eF x)
  have hfF : I ≤ RingHom.ker fF.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨⟨x, y, i⟩, rfl⟩)
    · change fF (p₀ _) = 0
      rw [show fF (p₀ i) = (b'.baseChange F).repr (eu F (matrixCoordinateEquiv fF)) i by
        change fF ((b'.baseChange C).repr (eu C genericMatrixUnit) i) = _
        rw [← basisChange_natural, enu]]
      simp only [eu, hF, hu, sub_self, map_zero, Finsupp.zero_apply]
    · change fF (p₁ _) = 0
      rw [show fF (p₁ (x,y,i)) = (b'.baseChange F).repr (ep F (matrixCoordinateEquiv fF) x y) i by
        change fF ((b'.baseChange C).repr (ep C genericMatrixUnit x y) i) = _
        rw [← basisChange_natural, enp]]
      simp only [ep, hF, hp, sub_self, map_zero, Finsupp.zero_apply]
  let aF := Ideal.Quotient.liftₐ I fF hfF
  haveI : Nontrivial (C ⧸ I) := aF.domain_nontrivial
  haveI : Algebra.FiniteType K (C ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  obtain ⟨aK⟩ := finiteTypePoint K (C ⧸ I)
  let fK := aK.comp (Ideal.Quotient.mkₐ K I)
  have hfK (p : C) (h : p ∈ I) : fK p = 0 := by
    change aK (Ideal.Quotient.mk I p) = _
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 h, map_zero]
  let gK := matrixCoordinateEquiv fK
  have huK : eu K gK = 0 := by
    apply (b'.baseChange K).repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    change (b'.baseChange K).repr (eu K (matrixCoordinateEquiv fK)) i = _
    rw [← enu, basisChange_natural]
    exact hfK _ (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
  have hpK (x y : U) : ep K gK x y = 0 := by
    apply (b'.baseChange K).repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    change (b'.baseChange K).repr (ep K (matrixCoordinateEquiv fK) x y) i = _
    rw [← enp, basisChange_natural]
    exact hfK _ (Ideal.subset_span (Or.inr ⟨(x,y,i), rfl⟩))
  let e := (TensorProduct.lid K U).symm.trans ((a K gK).trans (TensorProduct.lid K V))
  have lift_e (x : U) : (1 ⊗ₜ[K] e x : K ⊗[K] V) = a K gK (1 ⊗ₜ[K] x) := by
    change (TensorProduct.lid K V).symm ((TensorProduct.lid K V) _) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨e, ?_, fun x y => ?_⟩
  · apply (TensorProduct.lid K V).symm.injective
    change (1 ⊗ₜ[K] e J.unit : K ⊗[K] V) = 1 ⊗ₜ[K] J'.unit
    rw [lift_e]
    exact sub_eq_zero.mp huK
  · apply (TensorProduct.lid K V).symm.injective
    change (1 ⊗ₜ[K] e (J.groundOp x y) : K ⊗[K] V) = 1 ⊗ₜ[K] J'.groundOp (e x) (e y)
    rw [lift_e, ← J.groundOp_lift, ← J'.groundOp_lift, lift_e, lift_e]
    exact sub_eq_zero.mp (hpK x y)

end Specialization

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem chartOverField (J : ParaQuadratic R M) (K : Type) [Field K] [Algebra R K]
    [Module.FaithfullyFlat R B] (hB : OnComponent J B .octonion) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F),
      OnComponent (J.baseChange K) F .octonion := by
  let T := B ⊗[R] K
  haveI : Nontrivial T := Module.FaithfullyFlat.lTensor_nontrivial R B K
  obtain ⟨m, hm, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal T) bot_ne_top
  let F := T ⧸ m
  letI : Field F := Ideal.Quotient.field m
  letI : Algebra K F := Ideal.Quotient.algebra K
  letI : Algebra R F := Ideal.Quotient.algebra R
  letI : IsScalarTower R K F := Ideal.Quotient.isScalarTower R K m
  letI : Algebra B F := Ideal.Quotient.algebra B
  letI : IsScalarTower R B F := Ideal.Quotient.isScalarTower R B m
  let bf : B →ₐ[R] F := IsScalarTower.toAlgHom R B F
  obtain ⟨c, hu, hp⟩ := hB
  let chart : SplitChart J B := ⟨c, hu, hp⟩
  let d := extendChart chart bf
  let E := AlgebraTensorModule.cancelBaseChange R K F F M
  refine ⟨F, inferInstance, inferInstance, E.trans d.coordinates, ?_, ?_⟩
  · change d.coordinates (E (1 ⊗ₜ[K] (1 ⊗ₜ[R] J.unit))) = _
    rw [show E (1 ⊗ₜ[K] (1 ⊗ₜ[R] J.unit)) = 1 ⊗ₜ[R] J.unit by
      rw [AlgebraTensorModule.cancelBaseChange_tmul, one_smul]]
    exact d.unit
  · intro x y
    have hop : E ((J.baseChange K).op F x y) = J.op F (E x) (E y) :=
      baseChange_cancel_op (J := J) x y
    change d.coordinates (E ((J.baseChange K).op F x y)) = _
    rw [hop]
    exact d.op _ _

private theorem splitOfAlgebraicallyClosed (J : ParaQuadratic R M) (hJ : IsAlbert J)
    (K : Type) [Field K] [IsAlgClosed K] [Algebra R K] :
    IsSplitModel (J.baseChange K) .octonion := by
  obtain ⟨B, _, _, hff, hB⟩ := (albert_iff_split_octonion_after_cover J).1 hJ
  obtain ⟨F, _, _, e, hu, hp⟩ := chartOverField J K hB
  haveI : Module.Finite R M := (freudenthal_finite_projective J hJ.1).1
  haveI : Module.Finite K (Model K) := (split_model_rank K .octonion).1
  let Q := ParaQuadratic.ofJordan (weightedHermitianJordan (untwisted K)
    (Composition.Zorn.isOctonion K))
  let E := modelBaseChange K F
  let f := e.trans E.symm
  have hq : E (1 ⊗ₜ[K] Q.unit) = cubicUnit := by
    change modelBaseChange K F (1 ⊗ₜ[K] (cubicUnit : Model K)) = _
    have hh := modelBaseChange_tmul (B := K) (1 : F) (cubicUnit : Model K)
    exact hh.trans ((one_smul _ _).trans (mapModel_unit _))
  have hf : f (1 ⊗ₜ[K] (J.baseChange K).unit) = 1 ⊗ₜ[K] Q.unit := by
    apply E.injective
    change E (E.symm (e _)) = _
    rw [E.apply_symm_apply, hu, hq]
  have hg (x y) :
      f ((J.baseChange K).op F x y) = Q.op F (f x) (f y) := by
    apply E.injective
    have hQ (a b : F ⊗[K] Model K) : E (Q.op F a b) = modelOp (E a) (E b) :=
      modelBaseChange_operator a b
    rw [hQ]
    change E (E.symm (e _)) = modelOp (E (E.symm (e x))) (E (E.symm (e y)))
    simp only [LinearEquiv.apply_symm_apply]
    exact hp x y
  obtain ⟨l, hl, hl'⟩ := lawIsoOfExtension (J.baseChange K) Q F f hf hg
  exact ⟨l, hl, fun x y => (hl' x y).trans (ground_operator _ _ _ _)⟩

/-- The same integral split group controls the split law, the geometric fibres,
and the faithfully flat descent of smoothness, connectedness, and the centre. -/
theorem automorphismDescent : DescentType := by
  intro R M _ _ _ J hJ G hG h P L
  obtain ⟨B, _, _, hff, hB⟩ := (albert_iff_split_octonion_after_cover J).1 hJ
  obtain ⟨hs, hc, hz⟩ := propertiesFromCover L J hG h hB
  refine ⟨?_, splitComparison L hG J h, ⟨hs, hc⟩, fun hZ => hz (hZ B)⟩
  intro K _ _ _
  exact splitComparison L (changeAffine hG) (J.baseChange K) (baseChangeRep J h)
    (splitOfAlgebraicallyClosed J hJ K)

end
end LinearAlgebraicGroups.Albert.AutomorphismDescent
