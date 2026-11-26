import Specs.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
import LinearAlgebraicGroups.Representation.FlagLineBundle
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Topology.Sheaves.Stalks

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonObj Polynomial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.AssociatedFlagLineSheaves

open LinearAlgebraicGroups.Specs Specs.FlagLineBundle Specs.AssociatedFlagLineSheaves Specs.QuotientEmbedding

noncomputable section

variable {k : Type u} [Field k]

@[simp]
private theorem lineCoordinate_comp {T S : SchemeOver k} (f : T ⟶ S)
    (z : S ⟶ affineLine k) :
    lineCoordinate (f ≫ z) = f.left.appTop (lineCoordinate z) :=
  rfl

private def coordinateToLine (T : SchemeOver k) (z : Γ(T.left, ⊤)) :
    T ⟶ affineLine k := by
  let h := CommRingCat.ofHom (Polynomial.eval₂RingHom (groundScalars T).hom z)
  let f := ΓSpec.adjunction.homEquiv T.left (op (CommRingCat.of (Polynomial k))) h.op
  refine Over.homMk f ?_
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))).appTop = groundScalars T
  rw [Scheme.Hom.comp_appTop, ΓSpec_adjunction_homEquiv_eq]
  slice_lhs 2 3 => rw [Scheme.ΓSpecIso_naturality]
  rw [Category.assoc _ _ h, Iso.inv_hom_id_assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.eval₂_C _ _

private theorem lineCoordinate_coordinateToLine (T : SchemeOver k) (z : Γ(T.left, ⊤)) :
    lineCoordinate (coordinateToLine T z) = z := by
  let h : CommRingCat.of (Polynomial k) ⟶ Γ(T.left, ⊤) :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom (groundScalars T).hom z)
  change (((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
    ((ΓSpec.adjunction.homEquiv T.left (op (CommRingCat.of (Polynomial k)))) h.op).appTop)
    Polynomial.X) = z
  rw [ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  exact Polynomial.eval₂_X _ _

open private linePointEquiv linePoint_lineValue lineValue_linePoint characterUnit
  characterUnit_val characterUnit_mul characterUnits characterPoint characterPoint_eq
  torusCoordinate from LinearAlgebraicGroups.Representation.FlagLineBundle

private theorem lineCoordinate_linePoint (R : TestAlgebra k) (z : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (lineCoordinate (linePoint R z)) = z := by
  unfold lineCoordinate
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((Spec.map (CommRingCat.ofHom (Polynomial.aeval z).toRingHom)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X)) = z
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]
  exact Polynomial.aeval_X z

private theorem lineCoordinate_injective (T : SchemeOver k) :
    Function.Injective (lineCoordinate (T := T)) := by
  intro f g h
  apply GrassmannianCharts.hom_ext_on_affines
  intro R x
  obtain ⟨r, hr⟩ := (linePointEquiv R).surjective (x ≫ f)
  obtain ⟨s, hs⟩ := (linePointEquiv R).surjective (x ≫ g)
  change linePoint R r = x ≫ f at hr
  change linePoint R s = x ≫ g at hs
  rw [← hr, ← hs]
  congr 1
  have he := congrArg (fun z : Γ((testSpec k |>.obj (op R)).left, ⊤) ↦ (Scheme.ΓSpecIso (CommRingCat.of R)).hom z)
    (show lineCoordinate (x ≫ f) = lineCoordinate (x ≫ g) by rw [lineCoordinate_comp,
      lineCoordinate_comp, h])
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom (lineCoordinate (x ≫ f)) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (lineCoordinate (x ≫ g)) at he
  rw [← hr, ← hs, lineCoordinate_linePoint, lineCoordinate_linePoint] at he
  exact he

private def lineCoordinateEquiv (T : SchemeOver k) :
    (T ⟶ affineLine k) ≃ Γ(T.left, ⊤) :=
  Equiv.ofBijective _ ⟨lineCoordinate_injective T,
    fun z ↦ ⟨coordinateToLine T z, lineCoordinate_coordinateToLine T z⟩⟩

private theorem regularFunction_ext {T : SchemeOver k} {r s : Γ(T.left, ⊤)}
    (h : ∀ (R : TestAlgebra k) (x : Points T R), x.left.appTop r = x.left.appTop s) :
    r = s := by
  apply (lineCoordinateEquiv T).symm.injective
  apply GrassmannianCharts.hom_ext_on_affines
  intro R x
  apply lineCoordinate_injective
  rw [lineCoordinate_comp, lineCoordinate_comp]
  change x.left.appTop ((lineCoordinateEquiv T) ((lineCoordinateEquiv T).symm r)) =
    x.left.appTop ((lineCoordinateEquiv T) ((lineCoordinateEquiv T).symm s))
  simpa only [Equiv.apply_symm_apply] using h R x

private theorem pullCharacterFunction {H : GroupScheme k} (ψ : CharacterDescent.Character H)
    {T S : SchemeOver k} (f : S ⟶ T) (b : T ⟶ H.X) :
    f.left.appTop (characterFunction ψ b) = characterFunction ψ (f ≫ b) :=
  rfl

private theorem characterFunction_point {M : GroupScheme k} {H : ClosedSubgroup M}
    (ψ : CharacterDescent.Character H.group) (R : TestAlgebra k) (b : Points H.group.X R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (characterFunction ψ b) =
      CharacterPairing.characterValue ψ R b := by
  unfold characterFunction
  rw [← characterPoint_eq ψ R b]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((Spec.map (CommRingCat.ofHom (characterPoint ψ R b).toRingHom)).appTop
      ((Scheme.ΓSpecIso _).inv _)) = _
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]
  exact characterUnit_val ψ R b

private theorem characterFunction_mul {M : GroupScheme k} {H : ClosedSubgroup M}
    (ψ : CharacterDescent.Character H.group) {T : SchemeOver k} (b c : T ⟶ H.group.X) :
    characterFunction ψ (b * c) = characterFunction ψ b * characterFunction ψ c := by
  apply regularFunction_ext
  intro R x
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop _) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop _)
  rw [map_mul (x.left.appTop).hom, map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom,
    pullCharacterFunction, pullCharacterFunction, pullCharacterFunction, MonObj.comp_mul,
    characterFunction_point, characterFunction_point, characterFunction_point]
  exact congrArg Units.val (characterUnit_mul ψ R (x ≫ b) (x ≫ c))

private theorem characterFunction_one {M : GroupScheme k} {H : ClosedSubgroup M}
    (ψ : CharacterDescent.Character H.group) (T : SchemeOver k) :
    characterFunction ψ (1 : T ⟶ H.group.X) = 1 := by
  apply regularFunction_ext
  intro R x
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop _) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop _)
  rw [map_one (x.left.appTop).hom, map_one (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom,
    pullCharacterFunction, MonObj.comp_one, characterFunction_point]
  exact congrArg Units.val ((characterUnits ψ R).map_one)

section DirectImages

variable {X Y Z : Scheme.{u}}

private theorem functionsOver_smul (q : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U))
    (s : Γ(functionsOver q, U)) : r • s = q.app U r * (show Γ(X, q ⁻¹ᵁ U) from s) :=
  rfl

private theorem functionsOver_map (q : X ⟶ Y) {U V : Y.Opens} (i : V ⟶ U)
    (s : Γ(functionsOver q, U)) :
    (functionsOver q).presheaf.map i.op s = X.presheaf.map ((Opens.map q.base).map i).op s :=
  rfl

private theorem pull_app_base {q : X ⟶ Y} {r : Z ⟶ Y} (f : Z ⟶ X) (h : f ≫ q = r)
    (U : Y.Opens) : r ⁻¹ᵁ U ≤ f ⁻¹ᵁ (q ⁻¹ᵁ U) := by
  rw [← h]
  rfl

private def pullApp {q : X ⟶ Y} {r : Z ⟶ Y} (f : Z ⟶ X) (h : f ≫ q = r)
    (U : Y.Opens) : Γ(X, q ⁻¹ᵁ U) ⟶ Γ(Z, r ⁻¹ᵁ U) :=
  f.appLE _ _ (pull_app_base f h U)

private theorem pullApp_base {q : X ⟶ Y} {r : Z ⟶ Y} (f : Z ⟶ X) (h : f ≫ q = r)
    (U : Y.Opens) (a : Γ(Y, U)) : pullApp f h U (q.app U a) = r.app U a := by
  subst r
  change (q.app U ≫ pullApp f rfl U) a = _
  unfold pullApp
  rw [← Scheme.Hom.appLE_eq_app q, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_eq_app]

private def pullFunctions {q : X ⟶ Y} {r : Z ⟶ Y} (f : Z ⟶ X) (h : f ≫ q = r) :
    functionsOver q ⟶ functionsOver r :=
  ⟨PresheafOfModules.homMk
      { app := fun U ↦ AddCommGrpCat.ofHom ((pullApp f h U.unop).hom.toAddMonoidHom)
        naturality := by
          intro U V i
          ext : 1
          apply DFunLike.ext
          intro s
          change pullApp f h V.unop (X.presheaf.map ((Opens.map q.base).map i.unop).op s) =
            Z.presheaf.map ((Opens.map r.base).map i.unop).op (pullApp f h U.unop s)
          simp only [pullApp, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
            Scheme.Hom.appLE_map] }
      (by
        intro U a s
        change pullApp f h U.unop (q.app U.unop a * (show Γ(X, q ⁻¹ᵁ U.unop) from s)) =
          r.app U.unop a * pullApp f h U.unop s
        rw [map_mul, pullApp_base])⟩

private def multiplyFunctions (q : X ⟶ Y) (m : Γ(X, ⊤)) :
    functionsOver q ⟶ functionsOver q :=
  ⟨PresheafOfModules.homMk
      { app := fun U ↦ AddCommGrpCat.ofHom (AddMonoidHom.mulLeft
          (X.presheaf.map (homOfLE (show q ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op m))
        naturality := by
          intro U V i
          ext : 1
          apply DFunLike.ext
          intro s
          change X.presheaf.map (homOfLE le_top).op m *
              X.presheaf.map ((Opens.map q.base).map i.unop).op s =
            X.presheaf.map ((Opens.map q.base).map i.unop).op
              (X.presheaf.map (homOfLE le_top).op m * (show Γ(X, q ⁻¹ᵁ U.unop) from s))
          rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
          rfl }
      (by
        intro U a s
        let s' : Γ(X, q ⁻¹ᵁ U.unop) := s
        change _ * (q.app U.unop a * s') = q.app U.unop a * (_ * s')
        ring)⟩

private def zeroSubsheaf {M N : Y.Modules} (f : M ⟶ N) :
    SheafOfModules.Submodule (M : SheafOfModules Y.ringCatSheaf) where
  obj U := LinearMap.ker (f.val.app U).hom
  map {U V} i s hs := by
    change (f.val.app V).hom (M.val.map i s) = 0
    change (f.val.app V) (M.val.map i s) = 0
    exact (PresheafOfModules.naturality_apply f.val i s).trans
      (by rw [show (f.val.app U) s = 0 from hs, map_zero])
  isSheaf U s hs := by
    change (f.val.app U).hom s = 0
    have hN := (isSheaf_iff_isSheaf_of_type _ _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf :
        Presheaf.IsSheaf (Opens.grothendieckTopology Y)
          (N.presheaf ⋙ CategoryTheory.forget AddCommGrpCat))
    apply (hN.isSeparated _ hs).ext
    intro V i hi
    change N.val.map i.op ((f.val.app U) s) = N.val.map i.op 0
    exact (PresheafOfModules.naturality_apply f.val i.op s).symm.trans
      ((show (f.val.app (op V)) (M.val.map i.op s) = 0 from hi).trans (map_zero _).symm)

private theorem evalOn_comp {T : Scheme.{u}} (f : T ⟶ Z) (g : Z ⟶ X)
    (U : X.Opens) (V : Z.Opens) (hg : V ≤ g ⁻¹ᵁ U) (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ V)
    (hg' : (⊤ : T.Opens) ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(X, U)) :
    evalOn f V hf (g.appLE U V hg s) = evalOn (f ≫ g) U hg' s := by
  unfold evalOn
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

private theorem evalOn_top {T : Scheme.{u}} (f : T ⟶ X) (s : Γ(X, ⊤)) :
    evalOn f ⊤ (by simp) s = f.appTop s := by
  unfold evalOn
  have hf := f.appLE_eq_app (U := (⊤ : X.Opens))
  simpa only [Opens.map_top] using congrArg (fun m : Γ(X, ⊤) ⟶ Γ(T, ⊤) ↦ m s) (by
    exact Eq.trans (by congr 1) hf)

private theorem evalOn_open {U : X.Opens} (s : Γ(X, U)) :
    evalOn U.ι U (by simp) s = U.topIso.inv s := by
  simp only [evalOn, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

private theorem evalOn_restrict {T : Scheme.{u}} (f : T ⟶ X) (U : X.Opens)
    (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U) (s : Γ(X, ⊤)) :
    evalOn f U hf (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) = f.appTop s := by
  unfold evalOn
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact evalOn_top f s

private theorem evalOn_pullApp {q : X ⟶ Y} {r : Z ⟶ Y} (f : Z ⟶ X) (h : f ≫ q = r)
    {T : Scheme.{u}} (t : T ⟶ Z) (U : Y.Opens)
    (ht : (⊤ : T.Opens) ≤ t ⁻¹ᵁ (r ⁻¹ᵁ U))
    (ht' : (⊤ : T.Opens) ≤ (t ≫ f) ⁻¹ᵁ (q ⁻¹ᵁ U))
    (s : Γ(X, q ⁻¹ᵁ U)) :
    evalOn t _ ht (pullApp f h U s) = evalOn (t ≫ f) _ ht' s :=
  evalOn_comp t f _ _ _ _ _ _

private theorem evalOn_congr {T : Scheme.{u}} {f g : T ⟶ X} (h : f = g) (U : X.Opens)
    (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U) (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ U) (s : Γ(X, U)) :
    evalOn f U hf s = evalOn g U hg s := by
  subst h
  rfl

end DirectImages

section Covariance

open CategoryTheory.CartesianMonoidalCategory
open private quotient_right_mul torsorDifference torsorDifference_value
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open Specs.HomogeneousQuotient (rightMultiplication)

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  (Q : Presentation P.negative) (p : BorelProjection P)
  (χ : CharacterDescent.Character P.torus.group)

private abbrev pairProjection :
    G.val.X ⨯ P.negative.group.X ⟶ Q.scheme :=
  prod.fst ≫ Q.projection

private theorem right_over :
    rightMultiplication P.negative ≫ Q.projection = pairProjection Q :=
  (HomogeneousQuotient.quotientPullback Q).w.symm

private def covarianceDifference :
    functionsOver Q.projection.left ⟶ functionsOver (pairProjection Q).left :=
  pullFunctions (rightMultiplication P.negative).left (congrArg Over.Hom.left (right_over Q)) -
    pullFunctions (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ _).left rfl ≫
      multiplyFunctions (pairProjection Q).left
        (characterFunction (p.projection ≫ χ)
          ((prod.snd : G.val.X ⨯ P.negative.group.X ⟶ _)⁻¹))

private theorem covariant_iff_difference (U : Q.scheme.left.Opens)
    (f : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) :
    IsCovariantOn Q p χ U f ↔ (covarianceDifference Q p χ).app U f = 0 := by
  let d := pairProjection Q
  let r := rightMultiplication P.negative
  let l : G.val.X ⨯ P.negative.group.X ⟶ G.val.X := prod.fst
  let m := characterFunction (p.projection ≫ χ)
    ((prod.snd : G.val.X ⨯ P.negative.group.X ⟶ _)⁻¹)
  let mr := d.left
  let V := mr ⁻¹ᵁ U
  let z : Γ((G.val.X ⨯ P.negative.group.X).left, V) :=
    (G.val.X ⨯ P.negative.group.X).left.presheaf.map
      (homOfLE (show V ≤ ⊤ from le_top)).op m
  let hl : l.left ≫ Q.projection.left = d.left := rfl
  let hr : r.left ≫ Q.projection.left = d.left := congrArg Over.Hom.left (right_over Q)
  change IsCovariantOn Q p χ U f ↔ _ 
  have he : (covarianceDifference Q p χ).app U f = 0 ↔
      pullApp r.left hr U f = z * pullApp l.left hl U f := by
    change pullApp r.left hr U f - z * pullApp l.left hl U f = 0 ↔ _
    exact sub_eq_zero
  rw [he]
  have compare (T : SchemeOver k) (g : T ⟶ G.val.X) (b : T ⟶ P.negative.group.X)
      (h : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U))
      (h' : (⊤ : T.left.Opens) ≤
        (g * (b ≫ P.negative.inclusion.hom.hom)).left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U)) :
      let t := prod.lift g b
      let ht : (⊤ : T.left.Opens) ≤ t.left ⁻¹ᵁ V := by
        change (⊤ : T.left.Opens) ≤ (t ≫ l).left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U)
        simpa only [t, l, prod.lift_fst] using h
      evalOn t.left V ht (pullApp r.left hr U f) =
          evalOn t.left V ht (z * pullApp l.left hl U f) ↔
        evalOn (g * (b ≫ P.negative.inclusion.hom.hom)).left _ h' f =
          characterFunction (p.projection ≫ χ) b⁻¹ * evalOn g.left _ h f := by
    dsimp only
    let t := prod.lift g b
    have hl' : t ≫ l = g := prod.lift_fst g b
    have hr' : t ≫ r = g * (b ≫ P.negative.inclusion.hom.hom) := by
      simp only [r, rightMultiplication, MonObj.comp_mul, ← Category.assoc, t,
        prod.lift_fst, prod.lift_snd]
    have ht : (⊤ : T.left.Opens) ≤ t.left ⁻¹ᵁ V := by
      change (⊤ : T.left.Opens) ≤ (t ≫ l).left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U)
      rwa [hl']
    change evalOn t.left V ht _ = evalOn t.left V ht _ ↔ _
    change _ = (t.left.appLE V ⊤ ht).hom (_ * _) ↔ _
    rw [map_mul (t.left.appLE V ⊤ ht).hom]
    change _ = evalOn t.left _ ht z * evalOn t.left _ ht _ ↔ _
    rw [evalOn_pullApp _ _ _ _ _ (by rw [← Over.comp_left, hr']; exact h'),
      evalOn_pullApp _ _ _ _ _ (by rw [← Over.comp_left, hl']; exact h),
      evalOn_congr (show t.left ≫ r.left = _ from congrArg Over.Hom.left hr'),
      evalOn_congr (show t.left ≫ l.left = _ from congrArg Over.Hom.left hl')]
    have hz : evalOn t.left V ht z = characterFunction (p.projection ≫ χ) b⁻¹ := by
      rw [evalOn_restrict, pullCharacterFunction, GrpObj.comp_inv]
      simp only [t, prod.lift_snd]
    rw [hz]
  constructor
  · intro hf
    let T : SchemeOver k := Over.mk (V.ι ≫ (G.val.X ⨯ P.negative.group.X).hom)
    let t : T ⟶ G.val.X ⨯ P.negative.group.X := Over.homMk V.ι
    let g := t ≫ l
    let b := t ≫ prod.snd
    have h : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U) := by
      change (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V
      simp
    have h' : (⊤ : T.left.Opens) ≤
        (g * (b ≫ P.negative.inclusion.hom.hom)).left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U) := by
      have hmul : g * (b ≫ P.negative.inclusion.hom.hom) = t ≫ r := by
        simp only [r, rightMultiplication, MonObj.comp_mul, ← Category.assoc, g, b, l]
      rw [hmul]
      change (⊤ : V.toScheme.Opens) ≤ (t ≫ r ≫ Q.projection).left ⁻¹ᵁ U
      rw [right_over]
      change (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V
      simp
    have hglue : prod.lift g b = t := by
      apply prod.hom_ext <;> simp [g, b, l]
    have hc := (compare T g b h h').mpr (hf T g b h h')
    dsimp only at hc
    have ht : (⊤ : T.left.Opens) ≤ t.left ⁻¹ᵁ V := by change (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V; simp
    have hv (s : Γ((G.val.X ⨯ P.negative.group.X).left, V)) :
        evalOn (prod.lift g b).left V (by
          rw [hglue]; exact ht) s = evalOn V.ι V (by simp) s :=
      evalOn_congr (congrArg Over.Hom.left hglue) _ _ _ _
    rw [hv, hv, evalOn_open, evalOn_open] at hc
    exact (ConcreteCategory.bijective_of_isIso V.topIso.inv).1 hc
  · intro hf T g b h h'
    exact (compare T g b h h').mp (by rw [hf])

end Covariance

section GeometricSections

open private opened openIncl scaleLine scaleLine_eval quotient_right_mul
  torsorDifference torsorDifference_value
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open private descends from LinearAlgebraicGroups.Reductive.BorelProper
open CategoryTheory.CartesianMonoidalCategory

private theorem lineCoordinate_scale {M : GroupScheme k} {H : ClosedSubgroup M}
    (ψ : CharacterDescent.Character H.group)
    {T : SchemeOver k} (b : T ⟶ H.group.X) (z : T ⟶ affineLine k) :
    lineCoordinate (scaleLine ψ b z) = characterFunction ψ b * lineCoordinate z := by
  apply regularFunction_ext
  intro R x
  let e := Scheme.ΓSpecIso (CommRingCat.of R)
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  change e.hom (x.left.appTop _) = e.hom (x.left.appTop _)
  rw [map_mul (x.left.appTop).hom, map_mul e.hom.hom, pullCharacterFunction,
    ← lineCoordinate_comp, ← lineCoordinate_comp]
  have h := linePoint_lineValue R (x ≫ z)
  unfold e
  rw [scaleLine_eval, characterFunction_point, lineCoordinate_linePoint, ← h,
    lineCoordinate_linePoint, lineValue_linePoint, characterUnit_val]

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
  {Q : Presentation P.negative} {p : BorelProjection P}
  {χ : CharacterDescent.Character P.torus.group} {a : ModObj G.val.X Q.scheme}
  (L : AssociatedBundle Q a p χ)

private theorem transition_on_schemes {T : SchemeOver k} (g : T ⟶ G.val.X)
    (b : T ⟶ P.negative.group.X) (z : T ⟶ affineLine k) :
    prod.lift (g * (b ≫ P.negative.inclusion.hom.hom))
      (scaleLine (p.projection ≫ χ) b⁻¹ z) ≫ L.trivialization =
      prod.lift g z ≫ L.trivialization := by
  apply GrassmannianCharts.hom_ext_on_affines
  intro R x
  simp only [← Category.assoc, prod.comp_lift, MonObj.comp_mul, scaleLine_eval,
    GrpObj.comp_inv, characterUnit_val]
  rw [L.transition, linePoint_lineValue]

private abbrev groupOpen (U : Q.scheme.left.Opens) :=
  Q.projection.left ⁻¹ᵁ U

private def openProjection (U : Q.scheme.left.Opens) :
    opened G.val.X (groupOpen (Q := Q) U) ⟶ opened Q.scheme U :=
  Over.homMk (Q.projection.left ∣_ U) (by
    change (Q.projection.left ∣_ U) ≫ U.ι ≫ Q.scheme.hom =
      (groupOpen (Q := Q) U).ι ≫ G.val.X.hom
    rw [morphismRestrict_ι_assoc, Over.w])

private theorem openProjection_surjective (U : Q.scheme.left.Opens) :
    Surjective (Q.projection.left ∣_ U) := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := Q.surjective.surj y.val
  let x' : (groupOpen (Q := Q) U).toScheme := ⟨x, by change Q.projection.left x ∈ U; rw [hx]; exact y.property⟩
  refine ⟨x', Subtype.ext ?_⟩
  have e := congrArg (fun f : (groupOpen (Q := Q) U).toScheme ⟶ Q.scheme.left ↦ f x')
    (morphismRestrict_ι Q.projection.left U)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
  exact e.trans hx

private theorem openProjection_pullback (U : Q.scheme.left.Opens) :
    IsPullback (openIncl G.val.X (groupOpen (Q := Q) U)) (openProjection U)
      Q.projection (openIncl Q.scheme U) := by
  apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of k)))
  exact (isPullback_morphismRestrict Q.projection.left U).flip

private def sectionOver {U : Q.scheme.left.Opens} (s : geometricSections L U) :
    opened Q.scheme U ⟶ L.total :=
  Over.homMk s.val (by
    change s.val ≫ L.total.hom = U.ι ≫ Q.scheme.hom
    rw [← Over.w L.projection, ← Category.assoc, s.property])

private theorem sectionOver_projection {U : Q.scheme.left.Opens} (s : geometricSections L U) :
    sectionOver L s ≫ L.projection = openIncl Q.scheme U :=
  Over.OverMorphism.ext s.property

private def sectionGraphOn {U : Q.scheme.left.Opens} (s : geometricSections L U) :
    opened G.val.X (groupOpen (Q := Q) U) ⟶ G.val.X ⨯ affineLine k :=
  L.trivializes.lift (openIncl G.val.X (groupOpen (Q := Q) U)) (openProjection U ≫ sectionOver L s)
    (by rw [Category.assoc, sectionOver_projection]; exact (openProjection_pullback U).w)

private def sectionFunctionOn {U : Q.scheme.left.Opens} (s : geometricSections L U) :
    Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U) :=
  (groupOpen (Q := Q) U).topIso.hom (lineCoordinate (sectionGraphOn L s ≫ prod.snd))

private theorem sectionGraphOn_factor {U : Q.scheme.left.Opens} (s : geometricSections L U) :
    prod.lift (openIncl G.val.X (groupOpen (Q := Q) U)) (sectionGraphOn L s ≫ prod.snd) ≫
      L.trivialization = openProjection U ≫ sectionOver L s := by
  have hh : prod.lift (openIncl G.val.X (groupOpen (Q := Q) U)) (sectionGraphOn L s ≫ prod.snd) =
      sectionGraphOn L s := by
    apply prod.hom_ext
    · rw [prod.lift_fst]; exact (L.trivializes.lift_fst _ _ _).symm
    · rw [prod.lift_snd]
  rw [hh]
  exact L.trivializes.lift_snd _ _ _

private theorem evaluate_sectionOn {U : Q.scheme.left.Opens} (s : geometricSections L U)
    {T : SchemeOver k} (g : T ⟶ G.val.X) (i : T.left ⟶ U.toScheme)
    (hi : i ≫ U.ι = g.left ≫ Q.projection.left)
    (hg : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U)) :
    let z := coordinateToLine T (evalOn g.left _ hg (sectionFunctionOn L s))
    i ≫ s.val = (prod.lift g z ≫ L.trivialization).left := by
  let i' : T ⟶ opened Q.scheme U := Over.homMk i (by
    change i ≫ U.ι ≫ Q.scheme.hom = T.hom
    rw [← Category.assoc, hi, Category.assoc, Over.w, Over.w])
  have hgi : g ≫ Q.projection = i' ≫ openIncl Q.scheme U :=
    Over.OverMorphism.ext hi.symm
  let t := (openProjection_pullback U).lift g i' hgi
  have ht : t ≫ openIncl G.val.X (groupOpen (Q := Q) U) = g :=
    (openProjection_pullback U).lift_fst _ _ _
  have ht' : t ≫ openProjection U = i' := (openProjection_pullback U).lift_snd _ _ _
  let z' := t ≫ sectionGraphOn L s ≫ prod.snd
  have hz : lineCoordinate z' = evalOn g.left _ hg (sectionFunctionOn L s) := by
    have hcmp : t.left ≫ (groupOpen (Q := Q) U).ι = g.left :=
      congrArg Over.Hom.left ht
    have ht₀ : (⊤ : T.left.Opens) ≤ (t.left ≫ (groupOpen (Q := Q) U).ι) ⁻¹ᵁ
        (groupOpen (Q := Q) U) := by rwa [hcmp]
    have hv := evalOn_comp t.left (groupOpen (Q := Q) U).ι _ ⊤
      (by simp) (by simp) ht₀ (sectionFunctionOn L s)
    have hv' := evalOn_congr hcmp _ ht₀ hg (sectionFunctionOn L s)
    rw [← hv', ← hv, evalOn_top]
    change lineCoordinate z' = t.left.appTop
      (evalOn (groupOpen (Q := Q) U).ι _ (by simp) (sectionFunctionOn L s))
    rw [evalOn_open]
    simp only [sectionFunctionOn, Iso.hom_inv_id_apply, z', lineCoordinate_comp]
  have hz' : z' = coordinateToLine T (evalOn g.left _ hg (sectionFunctionOn L s)) :=
    lineCoordinate_injective T (hz.trans (lineCoordinate_coordinateToLine _ _).symm)
  dsimp only
  rw [← hz']
  have he : i' ≫ sectionOver L s = prod.lift g z' ≫ L.trivialization := by
    rw [← ht', Category.assoc, ← sectionGraphOn_factor, ← Category.assoc, prod.comp_lift, ht]
  exact congrArg Over.Hom.left he

private theorem coordinate_unique {T : SchemeOver k} (g : T ⟶ G.val.X)
    (z z' : T ⟶ affineLine k)
    (e : prod.lift g z ≫ L.trivialization = prod.lift g z' ≫ L.trivialization) :
    z = z' := by
  have h : prod.lift g z = prod.lift g z' :=
    L.trivializes.hom_ext (by simp) e
  simpa only [prod.lift_snd] using congrArg (· ≫ prod.snd) h

private theorem sectionFunctionOn_covariant {U : Q.scheme.left.Opens}
    (s : geometricSections L U) : IsCovariantOn Q p χ U (sectionFunctionOn L s) := by
  intro T g b h h'
  let gb := g * (b ≫ P.negative.inclusion.hom.hom)
  have hgb : gb ≫ Q.projection = g ≫ Q.projection := quotient_right_mul Q g b
  have hi : Set.range (g.left ≫ Q.projection.left) ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨(g.left ≫ Q.projection.left) x, h (Set.mem_univ x)⟩, rfl⟩
  let i := IsOpenImmersion.lift U.ι (g.left ≫ Q.projection.left) hi
  have hi' : i ≫ U.ι = g.left ≫ Q.projection.left := IsOpenImmersion.lift_fac _ _ _
  let z := coordinateToLine T (evalOn g.left _ h (sectionFunctionOn L s))
  let z' := coordinateToLine T (evalOn gb.left _ h' (sectionFunctionOn L s))
  have e₀ : i ≫ s.val = (prod.lift g z ≫ L.trivialization).left :=
    evaluate_sectionOn L s g i hi' h
  have e₁ : i ≫ s.val = (prod.lift gb z' ≫ L.trivialization).left :=
    evaluate_sectionOn L s gb i (hi'.trans (congrArg Over.Hom.left hgb).symm) h'
  have he := coordinate_unique L gb z' (scaleLine (p.projection ≫ χ) b⁻¹ z)
    (Over.OverMorphism.ext (e₁.symm.trans (e₀.trans
      (congrArg Over.Hom.left (transition_on_schemes L g b z)).symm)))
  have hc := congrArg (lineCoordinate (T := T)) he
  simpa only [z, z', lineCoordinate_scale, lineCoordinate_coordinateToLine] using hc

private theorem sectionFunctionOn_injective (U : Q.scheme.left.Opens) :
    Function.Injective (sectionFunctionOn L (U := U)) := by
  intro s t h
  apply Subtype.ext
  haveI := Q.flat
  haveI := Q.finitePresentation
  haveI := Q.surjective
  haveI := openProjection_surjective (Q := Q) U
  haveI : Epi (Q.projection.left ∣_ U) := inferInstance
  apply (cancel_epi (Q.projection.left ∣_ U)).mp
  let V := groupOpen (Q := Q) U
  let g := openIncl G.val.X V
  have e : (Q.projection.left ∣_ U) ≫ U.ι = g.left ≫ Q.projection.left :=
    morphismRestrict_ι _ _
  have hg : (⊤ : V.toScheme.Opens) ≤ g.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U) := by
    change (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V
    simp
  rw [evaluate_sectionOn L s g _ e hg, evaluate_sectionOn L t g _ e hg]
  change (prod.lift g (coordinateToLine _ (evalOn g.left _ hg (sectionFunctionOn L s))) ≫
    L.trivialization).left =
      (prod.lift g (coordinateToLine _ (evalOn g.left _ hg (sectionFunctionOn L t))) ≫
        L.trivialization).left
  rw [h]

private theorem sectionFunctionOn_surjective (U : Q.scheme.left.Opens)
    (f : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) (hf : IsCovariantOn Q p χ U f) :
    ∃ s : geometricSections L U, sectionFunctionOn L s = f := by
  let V := groupOpen (Q := Q) U
  let j := openIncl G.val.X V
  let z := coordinateToLine (opened G.val.X V) (V.topIso.inv f)
  let w := prod.lift j z ≫ L.trivialization
  have hz {T : SchemeOver k} (t : T ⟶ opened G.val.X V)
      (h : (⊤ : T.left.Opens) ≤ (t ≫ j).left ⁻¹ᵁ V) :
      lineCoordinate (t ≫ z) = evalOn (t ≫ j).left V h f := by
    have e := evalOn_comp t.left V.ι V ⊤ (by simp) (by simp) h f
    change lineCoordinate (t ≫ z) = evalOn (t.left ≫ V.ι) V h f
    rw [← e, evalOn_top]
    change lineCoordinate (t ≫ z) = t.left.appTop (evalOn V.ι V (by simp) f)
    rw [evalOn_open, lineCoordinate_comp, lineCoordinate_coordinateToLine]
  have hw : w ≫ L.projection = openProjection U ≫ openIncl Q.scheme U := by
    simp only [w, Category.assoc, ← L.trivializes.w, prod.lift_fst_assoc]
    exact (openProjection_pullback U).w
  haveI := Q.flat
  haveI := Q.finitePresentation
  haveI := Q.surjective
  haveI : Flat (openProjection (Q := Q) U).left := inferInstanceAs
    (Flat (Q.projection.left ∣_ U))
  haveI : Surjective (openProjection (Q := Q) U).left := openProjection_surjective _
  haveI : LocallyOfFinitePresentation (openProjection (Q := Q) U).left := inferInstanceAs
    (LocallyOfFinitePresentation (Q.projection.left ∣_ U))
  obtain ⟨s, hs⟩ := descends (openProjection U) w (fun T t t' ht ↦ by
    let g := t ≫ j
    let g' := t' ≫ j
    have he : g ≫ Q.projection = g' ≫ Q.projection := by
      dsimp only [g, g']
      rw [Category.assoc, Category.assoc, show j ≫ Q.projection =
        openProjection U ≫ openIncl Q.scheme U from (openProjection_pullback U).w,
        ← Category.assoc t, ← Category.assoc t', ht]
    let b := torsorDifference Q g g' he
    have hb : g * (b ≫ P.negative.inclusion.hom.hom) = g' := by
      rw [torsorDifference_value, mul_inv_cancel_left]
    have ht₁ : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ V := by
      change (⊤ : T.left.Opens) ≤ t.left ⁻¹ᵁ (V.ι ⁻¹ᵁ V)
      simp
    have ht₂ : (⊤ : T.left.Opens) ≤ g'.left ⁻¹ᵁ V := by
      change (⊤ : T.left.Opens) ≤ t'.left ⁻¹ᵁ (V.ι ⁻¹ᵁ V)
      simp
    have hc := hf T g b ht₁ (by rwa [hb])
    rw [evalOn_congr (congrArg Over.Hom.left hb) _ _ ht₂, ← hz t' ht₂, ← hz t ht₁] at hc
    have hz' : t' ≫ z = scaleLine (p.projection ≫ χ) b⁻¹ (t ≫ z) :=
      lineCoordinate_injective T (hc.trans (lineCoordinate_scale _ _ _).symm)
    simp only [w, ← Category.assoc, prod.comp_lift]
    change prod.lift g (t ≫ z) ≫ L.trivialization = prod.lift g' (t' ≫ z) ≫ L.trivialization
    rw [hz', ← hb]
    exact (transition_on_schemes L g b (t ≫ z)).symm)
  haveI : Epi (openProjection (Q := Q) U) := Over.epi_of_epi_left _
  have hproj : s ≫ L.projection = openIncl Q.scheme U := by
    apply (cancel_epi (openProjection U)).mp
    rw [← Category.assoc, hs, hw]
  let s' : geometricSections L U := ⟨s.left, congrArg Over.Hom.left hproj⟩
  refine ⟨s', ?_⟩
  have hgraph : sectionGraphOn L s' = prod.lift j z := by
    apply L.trivializes.hom_ext
    · rw [sectionGraphOn, IsPullback.lift_fst, prod.lift_fst]
    · rw [sectionGraphOn, IsPullback.lift_snd]
      exact hs
  rw [sectionFunctionOn, hgraph, prod.lift_snd]
  change V.topIso.hom (lineCoordinate (coordinateToLine (opened G.val.X V) (V.topIso.inv f))) = f
  rw [lineCoordinate_coordinateToLine, Iso.inv_hom_id_apply]

/-- The sheaf of covariant sections, realized on the given associated total space. -/
def realizeSections : SectionRealization L := by
  let N := zeroSubsheaf (covarianceDifference Q p χ)
  let liftSections (U : Q.scheme.left.Opens) :
      geometricSections L U → Γ(N.toSheafOfModules, U) := fun s ↦
    ⟨sectionFunctionOn L s, (covariant_iff_difference Q p χ U _).mp
      (sectionFunctionOn_covariant L s)⟩
  let secEquiv (U : Q.scheme.left.Opens) := Equiv.ofBijective (liftSections U) (by
    constructor
    · intro s t h
      exact sectionFunctionOn_injective L U (congrArg Subtype.val h)
    · intro s
      obtain ⟨t, ht⟩ := sectionFunctionOn_surjective L U s.val
        ((covariant_iff_difference Q p χ U _).mpr s.property)
      exact ⟨t, Subtype.ext ht⟩)
  refine ⟨N.toSheafOfModules, N.ι, fun _ ↦ Subtype.val_injective, ?_,
    fun U ↦ (secEquiv U).symm, ?_⟩
  · intro U f
    constructor
    · rintro ⟨s, rfl⟩
      exact (covariant_iff_difference Q p χ U _).mpr s.property
    · intro hf
      exact ⟨⟨f, (covariant_iff_difference Q p χ U _).mp hf⟩, rfl⟩
  · intro U x T g i hi h
    have e : sectionFunctionOn L ((secEquiv U).symm x) = x.val :=
      congrArg Subtype.val ((secEquiv U).apply_symm_apply x)
    refine ⟨coordinateToLine T (evalOn g.left _ h x.val), lineCoordinate_coordinateToLine _ _, ?_⟩
    rw [← e]
    exact evaluate_sectionOn L _ g i hi h

end GeometricSections


theorem associatedSectionSheaf : AssociatedSectionSheaf.{u} :=
  fun L ↦ ⟨realizeSections L⟩

open private opened openIncl from LinearAlgebraicGroups.Representation.FlagLineBundle in
theorem geometricSectionRestrictions : GeometricSectionRestrictions.{u} := by
  intro k _ G P Q a p χ L M U V h x
  let X := G.val.X.left
  let q := Q.projection.left
  let T := opened G.val.X (q ⁻¹ᵁ V)
  let g := openIncl G.val.X (q ⁻¹ᵁ V)
  let π := q ∣_ V
  let j := Q.scheme.left.homOfLE h
  let y := M.sheaf.presheaf.map (homOfLE h).op x
  have hπ : π ≫ V.ι = g.left ≫ q := morphismRestrict_ι q V
  have hV : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ (q ⁻¹ᵁ V) := by
    change (⊤ : (q ⁻¹ᵁ V).toScheme.Opens) ≤ (q ⁻¹ᵁ V).ι ⁻¹ᵁ (q ⁻¹ᵁ V)
    simp
  let i := (Opens.map q.base).map (homOfLE h)
  have hU : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ (q ⁻¹ᵁ U) :=
    hV.trans (g.left.preimage_mono i.le)
  obtain ⟨z, hz, e⟩ := M.evaluation V y T g π hπ hV
  obtain ⟨z', hz', e'⟩ := M.evaluation U x T g (π ≫ j)
    (by rw [Category.assoc, Scheme.homOfLE_ι]; exact hπ) hU
  have hr : M.functionVal V y = X.presheaf.map i.op (M.functionVal U x) :=
    PresheafOfModules.naturality_apply M.functions.val (homOfLE h).op x
  have hzz : z = z' := by
    apply lineCoordinate_injective T
    rw [hz, hz']
    change evalOn g.left (q ⁻¹ᵁ V) hV (M.functionVal V y) =
      evalOn g.left (q ⁻¹ᵁ U) hU (M.functionVal U x)
    rw [hr]
    unfold evalOn
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  haveI := Q.flat
  haveI := Q.finitePresentation
  haveI := openProjection_surjective (Q := Q) V
  haveI : Epi π := inferInstanceAs (Epi (q ∣_ V))
  apply (cancel_epi π).mp
  change π ≫ (M.sections V y).val = π ≫ j ≫ (M.sections U x).val
  rw [e, ← Category.assoc, e', hzz]

section Charts

open private opened openIncl localSection localSection_proj coversWithSections_of_local
  flagCover_and_polynomialChart torsorDifference torsorDifference_value
  from LinearAlgebraicGroups.Representation.FlagLineBundle

theorem chartCover : ChartCover.{u} := by
  intro k _ G P Q y
  obtain ⟨W, hy⟩ := coversWithSections_of_local Q.projection
    (flagCover_and_polynomialChart Q).1 y
  exact ⟨W.val, hy, ⟨⟨localSection W, congrArg Over.Hom.left (localSection_proj W)⟩⟩⟩

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {p : BorelProjection P}
    {χ : CharacterDescent.Character P.torus.group} {a : ModObj G.val.X Q.scheme}
    {L : AssociatedBundle Q a p χ} (M : SectionRealization L)

private theorem lift_in_open {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    (⊤ : U.toScheme.Opens) ≤ s.lift.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U) := by
  change (⊤ : U.toScheme.Opens) ≤ (s.lift.left ≫ Q.projection.left) ⁻¹ᵁ U
  rw [s.lifts]
  simp

private theorem chartValue_eq {U : Q.scheme.left.Opens} (s : TorsorLift Q U)
    (x : Γ(M.sheaf, U)) :
    U.topIso.inv (chartValue M s x) =
      evalOn s.lift.left _ (lift_in_open s) (M.functions.app U x) :=
  Iso.hom_inv_id_apply U.topIso _

private theorem chartValue_injective {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    Function.Injective (chartValue M s) := by
  intro x y h
  obtain ⟨zx, hzx, hx⟩ := M.evaluation U x (openOver Q.scheme U) s.lift (𝟙 _)
    (by simpa only [Category.id_comp] using s.lifts.symm) (lift_in_open s)
  obtain ⟨zy, hzy, hy⟩ := M.evaluation U y (openOver Q.scheme U) s.lift (𝟙 _)
    (by simpa only [Category.id_comp] using s.lifts.symm) (lift_in_open s)
  have hz : zx = zy := lineCoordinate_injective _ (by
    rw [hzx, hzy, ← chartValue_eq M s, ← chartValue_eq M s, h])
  apply (M.sections U).injective
  apply Subtype.ext
  rw [hz] at hx
  simpa only [Category.id_comp] using hx.trans hy.symm

private theorem chartValue_surjective {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    Function.Surjective (chartValue M s) := by
  intro r
  let z := coordinateToLine (openOver Q.scheme U) (U.topIso.inv r)
  let w := prod.lift s.lift z ≫ L.trivialization
  have hw : w.left ≫ L.projection.left = U.ι := by
    change (w ≫ L.projection).left = U.ι
    rw [show w ≫ L.projection = s.lift ≫ Q.projection by
      simp only [w, Category.assoc, ← L.trivializes.w, prod.lift_fst_assoc]]
    exact s.lifts
  let x := (M.sections U).symm ⟨w.left, hw⟩
  refine ⟨x, ?_⟩
  obtain ⟨z', hz', he⟩ := M.evaluation U x (openOver Q.scheme U) s.lift (𝟙 _)
    (by simpa only [Category.id_comp] using s.lifts.symm) (lift_in_open s)
  have he' : w.left = (prod.lift s.lift z' ≫ L.trivialization).left := by
    simpa only [Category.id_comp, x, Equiv.apply_symm_apply] using he
  have hzz : z = z' := coordinate_unique L s.lift z z'
    (Over.OverMorphism.ext he')
  apply (ConcreteCategory.bijective_of_isIso U.topIso.inv).1
  rw [chartValue_eq, ← hz', ← hzz, lineCoordinate_coordinateToLine]

private def chartLinearMap {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    Γ(M.sheaf, U) →ₗ[Γ(Q.scheme.left, U)] Γ(Q.scheme.left, U) where
  toFun := chartValue M s
  map_add' x y := by
    unfold chartValue evalOn
    simp only [map_add]
  map_smul' r x := by
    change chartValue M s (r • x) = r * chartValue M s x
    unfold chartValue
    rw [Scheme.Modules.Hom.app_smul, functionsOver_smul, evalOn, map_mul, map_mul]
    congr 1
    have h := evalOn_comp s.lift.left Q.projection.left U (Q.projection.left ⁻¹ᵁ U)
      le_rfl (lift_in_open s) (by rw [s.lifts]; simp) r
    rw [Scheme.Hom.appLE_eq_app, evalOn_congr s.lifts _ _ (by simp), evalOn_open] at h
    change U.topIso.hom (evalOn s.lift.left _ (lift_in_open s) (Q.projection.left.app U r)) = r
    rw [h, Iso.inv_hom_id_apply]

/-- Evaluation at the chosen lift is a linear isomorphism on the chart. -/
def chartEquiv {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    Γ(M.sheaf, U) ≃ₗ[Γ(Q.scheme.left, U)] Γ(Q.scheme.left, U) :=
  LinearEquiv.ofBijective (chartLinearMap M s)
    ⟨chartValue_injective M s, chartValue_surjective M s⟩

theorem chartCoordinates : ChartCoordinates.{u} :=
  fun M _ s ↦ ⟨chartEquiv M s, fun _ ↦ rfl⟩

theorem chartTransition : ChartTransition.{u} := by
  intro k _ G P Q a p χ L M U s t
  have h : s.lift ≫ Q.projection = t.lift ≫ Q.projection :=
    Over.OverMorphism.ext (s.lifts.trans t.lifts.symm)
  let b := torsorDifference Q s.lift t.lift h
  have hb : t.lift = s.lift * (b ≫ P.negative.inclusion.hom.hom) := by
    rw [torsorDifference_value, mul_inv_cancel_left]
  refine ⟨b, hb, fun x ↦ ?_⟩
  have hf := (M.functions_range U _).mp ⟨x, rfl⟩
  have e := hf (openOver Q.scheme U) s.lift b (lift_in_open s) (by
    rw [← hb]; exact lift_in_open t)
  rw [evalOn_congr (congrArg Over.Hom.left hb.symm) _ _ (lift_in_open t)] at e
  unfold chartValue
  rw [e, map_mul]

private def restrictLift {U W : Q.scheme.left.Opens} (h : W ≤ U) (s : TorsorLift Q U) :
    TorsorLift Q W where
  lift := Over.homMk (Q.scheme.left.homOfLE h ≫ s.lift.left) (by
    change (Q.scheme.left.homOfLE h ≫ s.lift.left) ≫ G.val.X.hom = W.ι ≫ Q.scheme.hom
    rw [Category.assoc, Over.w]
    change Q.scheme.left.homOfLE h ≫ U.ι ≫ Q.scheme.hom = _
    rw [Scheme.homOfLE_ι_assoc])
  lifts := by
    change (Q.scheme.left.homOfLE h ≫ s.lift.left) ≫ Q.projection.left = W.ι
    rw [Category.assoc, s.lifts, Scheme.homOfLE_ι]

private theorem torsorLift_ext {U : Q.scheme.left.Opens} {s t : TorsorLift Q U}
    (h : s.lift.left = t.lift.left) : s = t := by
  have e : s.lift = t.lift := Over.OverMorphism.ext h
  cases s
  cases t
  cases e
  rfl

private theorem chartValue_natural {U W : Q.scheme.left.Opens} (h : W ≤ U)
    (s : TorsorLift Q U) (x : Γ(M.sheaf, U)) :
    chartValue M (restrictLift h s) (M.sheaf.presheaf.map (homOfLE h).op x) =
      Q.scheme.left.presheaf.map (homOfLE h).op (chartValue M s x) := by
  let Y := Q.scheme.left
  let g := s.lift.left
  let j := Y.homOfLE h
  let t := (restrictLift h s).lift.left
  let f : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U) := M.functions.app U x
  let i : (Q.projection.left ⁻¹ᵁ W) ⟶ (Q.projection.left ⁻¹ᵁ U) := (Opens.map Q.projection.left.base).map (homOfLE h)
  have hf :
      M.functions.app W (M.sheaf.presheaf.map (homOfLE h).op x) =
        G.val.X.left.presheaf.map i.op f :=
    PresheafOfModules.naturality_apply M.functions.val (homOfLE h).op x
  apply (ConcreteCategory.bijective_of_isIso W.topIso.inv).1
  rw [chartValue_eq, hf, ← evalOn_open]
  have ht : (⊤ : W.toScheme.Opens) ≤ t ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ W) :=
    lift_in_open (restrictLift h s)
  have hu : (⊤ : U.toScheme.Opens) ≤ g ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U) := lift_in_open s
  have hw : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ U := by
    intro y _
    exact h y.property
  have hl (r : Γ(Y, U)) :
      evalOn W.ι W (by simp) (Y.presheaf.map (homOfLE h).op r) =
        j.appTop (evalOn U.ι U (by simp) r) := by
    have e₁ : evalOn W.ι W (by simp) (Y.presheaf.map (homOfLE h).op r) =
        evalOn W.ι U hw r := by
      unfold evalOn
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    have e₂ := evalOn_comp j U.ι U ⊤ (by simp) (by simp)
      (by rw [Scheme.homOfLE_ι]; exact hw) r
    rw [evalOn_top] at e₂
    have hc : j ≫ U.ι = W.ι := Scheme.homOfLE_ι Y h
    change _ = evalOn (j ≫ U.ι) U _ r at e₂
    exact e₁.trans ((evalOn_congr hc _ _ hw r).symm.trans e₂.symm)
  rw [hl, evalOn_open, chartValue_eq]
  have e := evalOn_comp j g _ ⊤ hu (by simp)
    (show (⊤ : W.toScheme.Opens) ≤ (j ≫ g) ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U) from
      ht.trans (t.preimage_mono (i.le))) f
  rw [evalOn_top] at e
  change j.appTop (evalOn g _ hu f) = evalOn (j ≫ g) _ _ f at e
  change evalOn t _ ht (G.val.X.left.presheaf.map i.op f) = j.appTop (evalOn g _ hu f)
  rw [e]
  unfold evalOn
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

/-- The coordinate isomorphism over an entire splitting open. -/
def chartIso {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    M.sheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf := by
  let W (V : U.toScheme.Opens) := U.ι ''ᵁ V
  let h (V : U.toScheme.Opens) : W V ≤ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  let e (V : U.toScheme.Opens) := chartEquiv M (restrictLift (h V) s)
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
  · change ((M.sheaf.restrict U.ι).val.obj V) ≅
      ((SheafOfModules.unit U.toScheme.ringCatSheaf).val.obj V)
    let E : Γ(M.sheaf.restrict U.ι, V.unop) ≃ₗ[Γ(U.toScheme, V.unop)] Γ(U.toScheme, V.unop) :=
      { toEquiv := (e V.unop).toEquiv
        map_add' := (e V.unop).map_add
        map_smul' := by
          intro r x
          have hs := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M.sheaf V.unop r x
          change (r • x : Γ(M.sheaf.restrict U.ι, V.unop)) =
            (U.ι.appIso V.unop).inv r • (M.sheaf.restrictAppIso U.ι V.unop).hom x at hs
          rw [Scheme.Opens.ι_appIso] at hs
          let r' : Γ(Q.scheme.left, W V.unop) := r
          change ((e V.unop) (r • x)) = r' * (e V.unop) x
          rw [hs]
          exact (e V.unop).map_smul r' x }
    exact E.toModuleIso
  · intro V V' i
    ext : 1
    apply DFunLike.ext
    intro x
    let h' : W V'.unop ≤ W V.unop := U.ι.image_mono (leOfHom i.unop)
    change chartValue M (restrictLift (h V'.unop) s) (M.sheaf.presheaf.map (homOfLE h').op x) =
      Q.scheme.left.presheaf.map (homOfLE h').op (chartValue M (restrictLift (h V.unop) s) x)
    have hl : restrictLift (h V'.unop) s = restrictLift h' (restrictLift (h V.unop) s) := by
      apply torsorLift_ext
      change _ ≫ s.lift.left = _ ≫ _ ≫ s.lift.left
      rw [← Category.assoc, Scheme.homOfLE_homOfLE]
    rw [hl]
    exact chartValue_natural M h' (restrictLift (h V.unop) s) x

theorem invertibleSectionSheaf : InvertibleSectionSheaf.{u} := by
  intro k _ G P Q a p χ L M y
  obtain ⟨U, hy, ⟨s⟩⟩ := chartCover Q y
  exact ⟨U, hy, ⟨s⟩, ⟨chartIso M s⟩⟩

end Charts

section GlobalSections

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {p : BorelProjection P}
    {χ : CharacterDescent.Character P.torus.group} {a : ModObj G.val.X Q.scheme}
    (L : AssociatedBundle Q a p χ)

private def topSectionEquiv : geometricSections L ⊤ ≃ BundleSection L where
  toFun s := ⟨Over.homMk (Q.scheme.left.topIso.inv ≫ s.val) (by
    rw [← Over.w L.projection, ← Category.assoc, Category.assoc Q.scheme.left.topIso.inv,
      s.property, Scheme.toIso_inv_ι, Category.id_comp]), by
    apply Over.OverMorphism.ext
    change (Q.scheme.left.topIso.inv ≫ s.val) ≫ L.projection.left = 𝟙 _
    rw [Category.assoc, s.property, Scheme.toIso_inv_ι]⟩
  invFun s := ⟨(⊤ : Q.scheme.left.Opens).ι ≫ s.val.left, by
    rw [Category.assoc, show s.val.left ≫ L.projection.left = 𝟙 _ from
      congrArg Over.Hom.left s.property, Category.comp_id]⟩
  left_inv s := by
    apply Subtype.ext
    change (⊤ : Q.scheme.left.Opens).ι ≫ Q.scheme.left.topIso.inv ≫ s.val = s.val
    rw [Scheme.ι_toIso_inv_assoc]
  right_inv s := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    change Q.scheme.left.topIso.inv ≫ (⊤ : Q.scheme.left.Opens).ι ≫ s.val.left = s.val.left
    rw [Scheme.toIso_inv_ι_assoc]

theorem globalCovariantSections : GlobalCovariantSections.{u} := by
  intro k _ G P Q a p χ L M A D e d q φ hq hφ c hc
  letI : Module k Γ(M.sheaf, ⊤) := Module.compHom _ (groundScalars Q.scheme).hom
  obtain ⟨F, hF, hcov⟩ := FlagLineBundle.schemeCovarianceComparison p χ e d q φ hq hφ c hc
  obtain ⟨S, hS⟩ := FlagLineBundle.sectionsAreCovariant L
  let F' : covariantFunctions q c ≃
      {f : G.val.X ⟶ affineLine k // SchemeCovariant p χ f} :=
    F.subtypeEquiv hcov
  let E := (M.sections ⊤).trans ((topSectionEquiv L).trans (S.trans F'.symm))
  have ev (x : Γ(M.sheaf, ⊤)) :
      Q.projection.left ≫ Q.scheme.left.topIso.inv ≫ (M.sections ⊤ x).val =
        (prod.lift (𝟙 G.val.X)
          (e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) (E x : A)) ≫ L.trivialization).left := by
    have h := congrArg Over.Hom.left (hS (topSectionEquiv L (M.sections ⊤ x)))
    have he : F (E x : A) = (S (topSectionEquiv L (M.sections ⊤ x))).val :=
      congrArg Subtype.val (F'.apply_symm_apply _)
    rw [← hF, he]
    exact h
  let T := (specGroup A).X
  let g : T ⟶ G.val.X := e.hom.hom.hom
  let coordIso := Scheme.ΓSpecIso (CommRingCat.of A)
  have coefficient (x : Γ(M.sheaf, ⊤)) :
      (E x : A) = coordIso.hom (g.left.appTop (M.functionVal ⊤ x)) := by
    let i := g.left ≫ Q.projection.left ≫ Q.scheme.left.topIso.inv
    have hi : i ≫ (⊤ : Q.scheme.left.Opens).ι = g.left ≫ Q.projection.left := by
      simp only [i, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
    obtain ⟨z, hz, hz'⟩ := M.evaluation ⊤ x T g i hi (by simp)
    let l := linePoint (CommAlgCat.of k A) (E x : A)
    have hg : g ≫ e.inv.hom.hom = 𝟙 T :=
      congrArg (fun f : specGroup A ⟶ specGroup A ↦ f.hom.hom) e.hom_inv_id
    have he : g ≫ prod.lift (𝟙 G.val.X) (e.inv.hom.hom ≫ l) ≫ L.trivialization =
        prod.lift g l ≫ L.trivialization := by
      rw [← Category.assoc, prod.comp_lift, Category.comp_id, ← Category.assoc g, hg, Category.id_comp]
    have hw := congrArg (fun s : G.val.X.left ⟶ L.total.left ↦ g.left ≫ s) (ev x)
    change g.left ≫ Q.projection.left ≫ Q.scheme.left.topIso.inv ≫ (M.sections ⊤ x).val =
      (g ≫ prod.lift (𝟙 G.val.X) (e.inv.hom.hom ≫ l) ≫ L.trivialization).left at hw
    rw [he, ← Category.assoc, ← Category.assoc] at hw
    have hzl : z = l := coordinate_unique L g z l (Over.OverMorphism.ext (hz'.symm.trans hw))
    change lineCoordinate z = evalOn g.left (⊤ : G.val.X.left.Opens) (by simp)
      (M.functionVal ⊤ x) at hz
    have hh := (lineCoordinate_linePoint (CommAlgCat.of k A) (E x : A)).symm
    change (E x : A) = coordIso.hom (lineCoordinate l) at hh
    rw [← hzl, hz, evalOn_top] at hh
    exact hh
  have hscalar (r : k) :
      coordIso.hom (g.left.appTop (Q.projection.left.appTop (groundScalars Q.scheme r))) =
        algebraMap k A r := by
    have e₁ : groundScalars Q.scheme ≫ Q.projection.left.appTop ≫ g.left.appTop = groundScalars T := by
      simp only [groundScalars, Category.assoc, ← Scheme.Hom.comp_appTop, Over.w]
    have e₂ : groundScalars T ≫ coordIso.hom = CommRingCat.ofHom (algebraMap k A) := by
      change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Spec.map _).appTop ≫ coordIso.hom = _
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
      rfl
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of A ↦ f r)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ coordIso.hom) e₁).trans e₂))
  let Eₗ : Γ(M.sheaf, ⊤) ≃ₗ[k] covariantFunctions q c :=
    { toEquiv := E
      map_add' := fun x y ↦ by
        apply Subtype.ext
        change (E (x + y) : A) = (E x : A) + (E y : A)
        rw [coefficient, coefficient, coefficient]
        simp only [SectionRealization.functionVal, map_add]
      map_smul' := fun r x ↦ by
        apply Subtype.ext
        change (E (r • x) : A) = (RingHom.id k r) • (E x : A)
        rw [RingHom.id_apply, Algebra.smul_def]
        change (E (groundScalars Q.scheme r • x) : A) = algebraMap k A r * (E x : A)
        rw [coefficient, coefficient]
        simp only [SectionRealization.functionVal, Scheme.Modules.Hom.app_smul, functionsOver_smul]
        let value : Γ(G.val.X.left, ⊤) := M.functionVal ⊤ x
        change coordIso.hom (g.left.appTop
          (Q.projection.left.appTop (groundScalars Q.scheme r) * value)) = _
        rw [map_mul, map_mul, hscalar] }
  exact ⟨Eₗ, ev⟩

end GlobalSections

section CharacterOperations

private abbrev Gm (k : Type u) [Field k] :=
  specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)

private def wholeGroup (H : GroupScheme k) : ClosedSubgroup H :=
  ⟨H, 𝟙 _, by
    change IsClosedImmersion (𝟙 H.X.left)
    infer_instance⟩

private theorem characterFunction_product {H : GroupScheme k}
    (χ χ₂ : CharacterDescent.Character H) {T : SchemeOver k} (b : T ⟶ H.X) :
    characterFunction (χ * χ₂) b = characterFunction χ b * characterFunction χ₂ b := by
  change characterFunction (H := Gm k) (𝟙 _) (b ≫ (χ * χ₂).hom.hom) =
    characterFunction (H := Gm k) (𝟙 _) (b ≫ χ.hom.hom) *
      characterFunction (H := Gm k) (𝟙 _) (b ≫ χ₂.hom.hom)
  rw [Grp.Hom.hom_mul, Mon.Hom.hom_mul, MonObj.comp_mul]
  exact characterFunction_mul (H := wholeGroup (Gm k)) (𝟙 _) _ _

private theorem characterFunction_characterComp {H H' : GroupScheme k}
    (f : H ⟶ H') (χ : CharacterDescent.Character H') {T : SchemeOver k} (b : T ⟶ H.X) :
    characterFunction (f ≫ χ) b = characterFunction χ (b ≫ f.hom.hom) := by
  unfold characterFunction
  rw [show (f ≫ χ).hom.hom = f.hom.hom ≫ χ.hom.hom from rfl, Category.assoc]

private theorem characterFunction_projected_product {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (p : BorelProjection P) (χ χ₂ : CharacterDescent.Character P.torus.group)
    {T : SchemeOver k} (b : T ⟶ P.negative.group.X) :
    characterFunction (p.projection ≫ (χ * χ₂)) b =
      characterFunction (p.projection ≫ χ) b * characterFunction (p.projection ≫ χ₂) b := by
  simp only [characterFunction_characterComp, characterFunction_product]

end CharacterOperations

section Tensor

open scoped TensorProduct
variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ χ₂ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} {N : AssociatedBundle Q a p χ₂}
    {K : AssociatedBundle Q a p (χ * χ₂)}
    (M : SectionRealization L) (M' : SectionRealization N) (M'' : SectionRealization K)

private theorem product_covariant {U : Q.scheme.left.Opens}
    {r s : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)}
    (hr : IsCovariantOn Q p χ U r) (hs : IsCovariantOn Q p χ₂ U s) :
    IsCovariantOn Q p (χ * χ₂) U (r * s) := by
  intro T g b h h'
  have e₁ := hr T g b h h'
  have e₂ := hs T g b h h'
  dsimp only [evalOn] at e₁ e₂ ⊢
  rw [map_mul, map_mul, e₁, e₂, characterFunction_projected_product]
  ac_rfl

private def productSection (U : Q.scheme.left.Opens) (x : Γ(M.sheaf, U)) (y : Γ(M'.sheaf, U)) :
    Γ(M''.sheaf, U) :=
  ((M''.functions_range U _).mpr
    (product_covariant ((M.functions_range U _).mp ⟨x, rfl⟩)
      ((M'.functions_range U _).mp ⟨y, rfl⟩))).choose

private theorem productSection_functions (U : Q.scheme.left.Opens)
    (x : Γ(M.sheaf, U)) (y : Γ(M'.sheaf, U)) :
    M''.functions.app U (productSection M M' M'' U x y) =
      M.functionVal U x * M'.functionVal U y :=
  ((M''.functions_range U _).mpr
    (product_covariant ((M.functions_range U _).mp ⟨x, rfl⟩)
      ((M'.functions_range U _).mp ⟨y, rfl⟩))).choose_spec

/-- Multiplication of regular covariants, which is multiplication of the
two coordinates in the common frame. -/
def multiplySections : SectionPairing M.sheaf M'.sheaf M''.sheaf where
  app U :=
    { toFun := fun x ↦
        { toFun := productSection M M' M'' U x
          map_add' y z := by
            apply M''.functions_injective
            simp only [map_add, productSection_functions, mul_add]
          map_smul' r y := by
            apply M''.functions_injective
            simp only [RingHom.id_apply, Scheme.Modules.Hom.app_smul, productSection_functions,
              functionsOver_smul]
            exact mul_left_comm (M.functionVal U x) (Q.projection.left.app U r)
              (M'.functionVal U y) }
      map_add' x y := by
        ext z : 1
        apply M''.functions_injective
        change M''.functions.app U (productSection M M' M'' U (x + y) z) =
          M''.functions.app U (productSection M M' M'' U x z + productSection M M' M'' U y z)
        simp only [map_add, productSection_functions, add_mul]
      map_smul' r x := by
        ext y : 1
        apply M''.functions_injective
        change M''.functions.app U (productSection M M' M'' U (r • x) y) =
          M''.functions.app U (r • productSection M M' M'' U x y)
        simp only [Scheme.Modules.Hom.app_smul, productSection_functions, functionsOver_smul]
        exact mul_assoc (Q.projection.left.app U r) (M.functionVal U x) (M'.functionVal U y) }
  naturality {U V} i x y := by
    apply M''.functions_injective V
    change M''.functionVal V (M''.sheaf.presheaf.map i.op (productSection M M' M'' U x y)) =
      M''.functionVal V (productSection M M' M'' V
        (M.sheaf.presheaf.map i.op x) (M'.sheaf.presheaf.map i.op y))
    let j := ((Opens.map Q.projection.left.base).map i).op
    have h {θ : CharacterDescent.Character P.torus.group} {B : AssociatedBundle Q a p θ}
        (R : SectionRealization B) (z : Γ(R.sheaf, U)) :
        R.functionVal V (R.sheaf.presheaf.map i.op z) =
          G.val.X.left.presheaf.map j (R.functionVal U z) :=
      PresheafOfModules.naturality_apply R.functions.val i.op z
    change _ = _
    rw [h M'', show M''.functionVal U (productSection M M' M'' U x y) = _ from
      productSection_functions M M' M'' U x y, show M''.functionVal V (productSection M M' M'' V
        (M.sheaf.presheaf.map i.op x) (M'.sheaf.presheaf.map i.op y)) = _ from
      productSection_functions M M' M'' V _ _, h M, h M']
    exact map_mul (G.val.X.left.presheaf.map j).hom _ _

theorem multiplySections_formula (U : Q.scheme.left.Opens) (x : Γ(M.sheaf, U))
    (y : Γ(M'.sheaf, U)) :
    M''.functions.app U ((multiplySections M M' M'').app U x y) =
      M.functionVal U x * M'.functionVal U y :=
  productSection_functions M M' M'' U x y

theorem multiplySections_chart {U : Q.scheme.left.Opens} (s : TorsorLift Q U)
    (x : Γ(M.sheaf, U)) (y : Γ(M'.sheaf, U)) :
    chartValue M'' s ((multiplySections M M' M'').app U x y) =
      chartValue M s x * chartValue M' s y := by
  unfold chartValue evalOn
  rw [multiplySections_formula, map_mul, map_mul]

/-- On each common chart the bilinear map exhibits the target sections
as the tensor product of the two modules of sections. -/
def chartTensorEquiv {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    (Γ(M.sheaf, U) ⊗[Γ(Q.scheme.left, U)] Γ(M'.sheaf, U)) ≃ₗ[Γ(Q.scheme.left, U)]
      Γ(M''.sheaf, U) :=
  let R := Γ(Q.scheme.left, U)
  (TensorProduct.congr (chartEquiv M s) (chartEquiv M' s)).trans
    ((TensorProduct.lid R R).trans (chartEquiv M'' s).symm)

theorem chartTensorEquiv_tmul {U : Q.scheme.left.Opens} (s : TorsorLift Q U)
    (x : Γ(M.sheaf, U)) (y : Γ(M'.sheaf, U)) :
    chartTensorEquiv M M' M'' s (x ⊗ₜ y) = (multiplySections M M' M'').app U x y := by
  apply (chartEquiv M'' s).injective
  simp only [chartTensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    TensorProduct.lid_tmul, LinearEquiv.apply_symm_apply]
  exact (multiplySections_chart M M' M'' s x y).symm

private def splittingSieve (U : Q.scheme.left.Opens) : Sieve U where
  arrows W _ := Nonempty (TorsorLift Q W)
  downward_closed := fun ⟨s⟩ j ↦ ⟨restrictLift (leOfHom j) s⟩

private theorem splittingSieve_covers (U : Q.scheme.left.Opens) :
    splittingSieve U ∈ Opens.grothendieckTopology Q.scheme.left U := by
  intro y hy
  obtain ⟨W, hyW, ⟨s⟩⟩ := chartCover Q y
  exact ⟨U ⊓ W, homOfLE inf_le_left, ⟨restrictLift inf_le_right s⟩, ⟨hy, hyW⟩⟩

private theorem sections_are_product {U : Q.scheme.left.Opens} (s : TorsorLift Q U)
    (z : Γ(M''.sheaf, U)) :
    ∃ x y, (multiplySections M M' M'').app U x y = z := by
  let x := (chartEquiv M s).symm (chartEquiv M'' s z)
  let y := (chartEquiv M' s).symm 1
  refine ⟨x, y, (chartEquiv M'' s).injective ?_⟩
  change chartValue M'' s _ = chartEquiv M'' s z
  rw [multiplySections_chart]
  change chartEquiv M s x * chartEquiv M' s y = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, mul_one]

variable {D : Q.scheme.left.Modules}
    (b : SectionPairing M.sheaf M'.sheaf D)

private def factorOnChart {U : Q.scheme.left.Opens} (s : TorsorLift Q U) :
    Γ(M''.sheaf, U) →ₗ[Γ(Q.scheme.left, U)] Γ(D, U) :=
  (TensorProduct.lift (b.app U)).comp (chartTensorEquiv M M' M'' s).symm.toLinearMap

private theorem factorOnChart_mul {U : Q.scheme.left.Opens} (s : TorsorLift Q U)
    (x : Γ(M.sheaf, U)) (y : Γ(M'.sheaf, U)) :
    factorOnChart M M' M'' b s ((multiplySections M M' M'').app U x y) = b.app U x y := by
  rw [← chartTensorEquiv_tmul M M' M'' s]
  change TensorProduct.lift _ ((chartTensorEquiv M M' M'' s).symm
    (chartTensorEquiv M M' M'' s _)) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul]

private theorem factorOnChart_natural {U V : Q.scheme.left.Opens} (i : V ⟶ U)
    (s : TorsorLift Q U) (s' : TorsorLift Q V) (z : Γ(M''.sheaf, U)) :
    D.presheaf.map i.op (factorOnChart M M' M'' b s z) =
      factorOnChart M M' M'' b s' (M''.sheaf.presheaf.map i.op z) := by
  obtain ⟨x, y, rfl⟩ := sections_are_product M M' M'' s z
  rw [factorOnChart_mul, (multiplySections M M' M'').naturality, factorOnChart_mul, b.naturality]

private abbrev sectionTypes (D : Q.scheme.left.Modules) :
    Q.scheme.left.Opensᵒᵖ ⥤ Type u :=
  D.presheaf ⋙ CategoryTheory.forget AddCommGrpCat

private theorem sectionTypes_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology Q.scheme.left) (sectionTypes D) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    (GrothendieckTopology.HasSheafCompose.isSheaf _ D.isSheaf)

private def factorFamily (U : Q.scheme.left.Opens) (z : Γ(M''.sheaf, U)) :
    Presieve.FamilyOfElements (sectionTypes D) (splittingSieve U : Presieve U) :=
  fun _ i hi ↦ factorOnChart M M' M'' b (Classical.choice hi) (M''.sheaf.presheaf.map i.op z)

private theorem factorFamily_compatible (U : Q.scheme.left.Opens) (z : Γ(M''.sheaf, U)) :
    (factorFamily M M' M'' b U z).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro V W i j hi
  dsimp only [factorFamily]
  rw [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply]
  exact (factorOnChart_natural M M' M'' b j _ _ _).symm

private def factorSection (U : Q.scheme.left.Opens) (z : Γ(M''.sheaf, U)) : Γ(D, U) :=
  (sectionTypes_isSheaf (D := D) _ (splittingSieve_covers U)).amalgamate
    (factorFamily M M' M'' b U z) (factorFamily_compatible M M' M'' b U z)

private theorem factorSection_restrict {U V : Q.scheme.left.Opens} (i : V ⟶ U)
    (s : TorsorLift Q V) (z : Γ(M''.sheaf, U)) :
    D.presheaf.map i.op (factorSection M M' M'' b U z) =
      factorOnChart M M' M'' b s (M''.sheaf.presheaf.map i.op z) := by
  have e := (sectionTypes_isSheaf (D := D) _ (splittingSieve_covers U)).valid_glue
    (factorFamily_compatible M M' M'' b U z) i (show (splittingSieve U) i from ⟨s⟩)
  change _ = factorOnChart M M' M'' b (Classical.choice (show Nonempty (TorsorLift Q V)
    from ⟨s⟩)) _ at e
  refine e.trans ?_
  obtain ⟨x, y, hxy⟩ := sections_are_product M M' M'' s (M''.sheaf.presheaf.map i.op z)
  rw [← hxy, factorOnChart_mul, factorOnChart_mul]

private theorem sections_ext_onCharts {U : Q.scheme.left.Opens} {x y : Γ(D, U)}
    (h : ∀ {V : Q.scheme.left.Opens} (i : V ⟶ U), TorsorLift Q V →
      D.presheaf.map i.op x = D.presheaf.map i.op y) : x = y := by
  apply ((sectionTypes_isSheaf (D := D)).isSeparated _ (splittingSieve_covers U)).ext
  rintro V i ⟨s⟩
  exact h i s

private def tensorFactor : M''.sheaf ⟶ D :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := factorSection M M' M'' b U.unop
          map_zero' := by
            apply sections_ext_onCharts
            intro V i s
            rw [factorSection_restrict M M' M'' b i s, map_zero, map_zero, map_zero]
          map_add' := by
            intro x y
            apply sections_ext_onCharts
            intro V i s
            rw [factorSection_restrict M M' M'' b i s, map_add, map_add, map_add,
              factorSection_restrict M M' M'' b i s, factorSection_restrict M M' M'' b i s] }
      naturality := by
        intro U V i
        ext : 1
        apply DFunLike.ext
        intro z
        change factorSection M M' M'' b V.unop (M''.sheaf.presheaf.map i z) =
          D.presheaf.map i (factorSection M M' M'' b U.unop z)
        apply sections_ext_onCharts
        intro W j s
        rw [factorSection_restrict M M' M'' b j s]
        have hd := factorSection_restrict M M' M'' b (j ≫ i.unop) s z
        rw [op_comp, Functor.map_comp, Functor.map_comp] at hd
        exact hd.symm }
    (by
      intro U r z
      let r' : Γ(Q.scheme.left, U.unop) := r
      change factorSection M M' M'' b U.unop (r' • z) =
        r' • factorSection M M' M'' b U.unop z
      apply sections_ext_onCharts
      intro V i s
      rw [factorSection_restrict M M' M'' b i s, M''.sheaf.map_smul i, map_smul,
        D.map_smul i, factorSection_restrict M M' M'' b i s])⟩

theorem multiplySections_isTensorProduct : IsTensorProduct (multiplySections M M' M'') := by
  intro D b
  have h (U : Q.scheme.left.Opens) (x : Γ(M.sheaf, U)) (y : Γ(M'.sheaf, U)) :
      (tensorFactor M M' M'' b).app U ((multiplySections M M' M'').app U x y) =
        b.app U x y := by
    apply sections_ext_onCharts
    intro V i s
    change D.presheaf.map i.op (factorSection M M' M'' b U
      ((multiplySections M M' M'').app U x y)) = _
    rw [factorSection_restrict M M' M'' b i s, (multiplySections M M' M'').naturality,
      factorOnChart_mul, b.naturality]
  refine ⟨tensorFactor M M' M'' b, h, fun f hf ↦ ?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext : 1
  apply DFunLike.ext
  intro z
  apply sections_ext_onCharts
  intro V i s
  have natural (f : M''.sheaf ⟶ D) :
      D.presheaf.map i.op (f.app U z) = f.app V (M''.sheaf.presheaf.map i.op z) :=
    (PresheafOfModules.naturality_apply f.val i.op z).symm
  rw [natural, natural]
  obtain ⟨x, y, hxy⟩ := sections_are_product M M' M'' s (M''.sheaf.presheaf.map i.op z)
  rw [← hxy, hf, h]

theorem characterMultiplication : CharacterMultiplication.{u} := by
  intro k _ G P Q a p χ χ₂ L N K M M' M''
  exact ⟨multiplySections M M' M'', multiplySections_formula M M' M'', fun U s ↦
    ⟨multiplySections_chart M M' M'' s, chartTensorEquiv M M' M'' s,
      chartTensorEquiv_tmul M M' M'' s⟩, multiplySections_isTensorProduct M M' M''⟩

end Tensor

section OpenRestriction

open Scheme.Modules

variable {X Y : Scheme.{u}}

private theorem isIso_of_open_restrictions {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((restrictFunctor U.ι).map φ)) :
    IsIso φ := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hF : IsIso (F.map φ) := by
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    obtain ⟨U, hx, hU⟩ := h x
    let x' : U.toScheme := ⟨x, hx⟩
    let e := restrictStalkNatIso U.ι x'
    have eq := e.hom.naturality φ
    change (TopCat.Presheaf.stalkFunctor _ x').map
        ((toPresheaf U.toScheme).map ((restrictFunctor U.ι).map φ)) ≫ e.hom.app N =
      e.hom.app M ≫ (TopCat.Presheaf.stalkFunctor _ x).map (F.map φ).1 at eq
    haveI : IsIso (e.hom.app M ≫ (TopCat.Presheaf.stalkFunctor _ x).map (F.map φ).1) := by
      rw [← eq]
      infer_instance
    exact IsIso.of_isIso_comp_left (f := e.hom.app M) _
  haveI : IsIso ((toPresheaf X).map φ) :=
    inferInstanceAs (IsIso ((TopCat.Sheaf.forget _ _).map (F.map φ)))
  exact isIso_of_reflects_iso φ (toPresheaf X)

private abbrev structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

private theorem unit_endomorphism_isIso
    (z : structureModule X ⟶ structureModule X)
    (hz : @IsUnit (Γ(X, ⊤) : Type u) _ (z.app ⊤ (1 : Γ(X, ⊤)))) : IsIso z := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  let i : U ⟶ (⊤ : X.Opens) := homOfLE le_top
  have hn := PresheafOfModules.naturality_apply z.val i.op (1 : Γ(X, ⊤))
  change z.app U (X.presheaf.map i.op (1 : Γ(X, ⊤))) =
    X.presheaf.map i.op (z.app ⊤ (1 : Γ(X, ⊤))) at hn
  rw [map_one] at hn
  have hunit : @IsUnit (Γ(X, U) : Type u) _ (z.app U (1 : Γ(X, U))) :=
    hn ▸ hz.map (X.presheaf.map i.op).hom
  apply (ConcreteCategory.isIso_iff_bijective (z.app U)).mpr
  let c : Γ(X, U) := z.app U (1 : Γ(X, U))
  have hmul (r : Γ(X, U)) : z.app U r = r * c := by
    have e := Hom.app_smul z r (1 : Γ(X, U))
    have e' : z.app U (r * (1 : Γ(X, U))) = r * c := e
    simpa only [mul_one] using e'
  change Function.Bijective (fun r : Γ(X, U) ↦ z.app U r)
  rw [show (fun r : Γ(X, U) ↦ z.app U r) = (fun r : Γ(X, U) ↦ r * c) from funext hmul]
  exact IsUnit.isUnit_iff_mulRight_bijective.mp (show IsUnit c from hunit)

private def pushforwardSquare (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) :
    pushforward W.ι ⋙ pushforward f ≅ pushforward (f.resLE U W hW) ⋙ pushforward U.ι :=
  pushforwardComp W.ι f ≪≫ pushforwardCongr (Scheme.Hom.resLE_comp_ι f hW).symm ≪≫
    (pushforwardComp (f.resLE U W hW) U.ι).symm

private def restrictDirectImageHom (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) {N : Y.Modules} {M : X.Modules} (h : N ⟶ (pushforward f).obj M) :
    N.restrict U.ι ⟶ (pushforward (f.resLE U W hW)).obj (M.restrict W.ι) :=
  ((restrictAdjunction U.ι).homEquiv _ _).symm
    (h ≫ (pushforward f).map ((restrictAdjunction W.ι).unit.app M) ≫
      (pushforwardSquare f hW).hom.app _)

/-- The two composites of restriction and inverse image have isomorphic right adjoints
by the square of scheme morphisms. The associated identification preserves the local adjoint. -/
private theorem restrict_adjoint_isIso (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) {N : Y.Modules} {M : X.Modules} (h : N ⟶ (pushforward f).obj M)
    (hh : IsIso (((pullbackPushforwardAdjunction (f.resLE U W hW)).homEquiv _ _).symm
      (restrictDirectImageHom f hW h))) :
    IsIso ((restrictFunctor W.ι).map (((pullbackPushforwardAdjunction f).homEquiv _ _).symm h)) := by
  let adjF := pullbackPushforwardAdjunction f
  let adjW := restrictAdjunction W.ι
  let adjU := restrictAdjunction U.ι
  let adjg := pullbackPushforwardAdjunction (f.resLE U W hW)
  let A := adjF.comp adjW
  let B := adjU.comp adjg
  let I := pushforwardSquare f hW
  let C := A.ofNatIsoRight I
  let e := C.leftAdjointUniq B
  let a := (adjF.homEquiv _ _).symm h
  let b := (adjg.homEquiv _ _).symm (restrictDirectImageHom f hW h)
  have ha : C.homEquiv N (M.restrict W.ι) ((restrictFunctor W.ι).map a) =
      h ≫ (pushforward f).map (adjW.unit.app M) ≫ I.hom.app _ := by
    dsimp only [C, A]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change adjF.homEquiv _ _ (adjW.homEquiv _ _ ((restrictFunctor W.ι).map a)) ≫ _ = _
    have hW' : adjW.homEquiv _ _ ((restrictFunctor W.ι).map a) = a ≫ adjW.unit.app M := by
      rw [Adjunction.homEquiv_unit]
      exact (adjW.unit.naturality a).symm
    rw [hW', adjF.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc]
  have hb : B.homEquiv N (M.restrict W.ι) b =
      h ≫ (pushforward f).map (adjW.unit.app M) ≫ I.hom.app _ := by
    dsimp only [B]
    rw [Adjunction.comp_homEquiv]
    change adjU.homEquiv _ _ (adjg.homEquiv _ _ b) = _
    rw [Equiv.apply_symm_apply]
    exact Equiv.apply_symm_apply _ _
  have he : (restrictFunctor W.ι).map a = e.hom.app N ≫ b := by
    apply (C.homEquiv _ _).injective
    rw [ha, Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [← Adjunction.homEquiv_unit]
    exact hb.symm
  change IsIso ((restrictFunctor W.ι).map a)
  rw [he]
  haveI : IsIso b := hh
  infer_instance

private def restrictTopSections (N : X.Modules) (U : X.Opens) :
    Γ(N.restrict U.ι, ⊤) ≅ Γ(N, U) :=
  N.restrictAppIso U.ι ⊤ ≪≫ N.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

private theorem restrictFunctor_map_app {N M : X.Modules} (h : N ⟶ M) (U : X.Opens)
    (V : U.toScheme.Opens) :
    ((restrictFunctor U.ι).map h).app V = h.app (U.ι ''ᵁ V) := rfl

private theorem restrictDirectImageHom_top (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (hW : W ≤ f ⁻¹ᵁ U) {N : Y.Modules} {M : X.Modules} (h : N ⟶ (pushforward f).obj M)
    (x : Γ(N.restrict U.ι, ⊤)) :
    (restrictTopSections M W).hom ((restrictDirectImageHom f hW h).app ⊤ x) =
      M.presheaf.map (homOfLE hW).op (h.app U ((restrictTopSections N U).hom x)) := by
  rw [restrictDirectImageHom, Adjunction.homEquiv_counit]
  simp only [Hom.comp_app, restrictFunctor_map_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    restrictAdjunction_counit_app_app, ConcreteCategory.comp_apply]
  unfold pushforwardSquare
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Hom.comp_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    pushforwardComp_inv_app_app, Category.comp_id]
  unfold restrictTopSections
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, restrictAppIso,
    Iso.refl_hom, ConcreteCategory.comp_apply]
  let V := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
  let g := f.resLE U W hW
  let A := W.ι ''ᵁ (W.ι ⁻¹ᵁ (f ⁻¹ᵁ V))
  let B := W.ι ''ᵁ (g ⁻¹ᵁ (U.ι ⁻¹ᵁ V))
  let C := W.ι ''ᵁ (⊤ : W.toScheme.Opens)
  have hAB : B = A := by
    change W.ι ''ᵁ ((g ≫ U.ι) ⁻¹ᵁ V) = W.ι ''ᵁ ((W.ι ≫ f) ⁻¹ᵁ V)
    rw [show g ≫ U.ι = W.ι ≫ f from Scheme.Hom.resLE_comp_ι f hW]
  have hBC : C = B := by
    change W.ι ''ᵁ (g ⁻¹ᵁ (⊤ : U.toScheme.Opens)) =
      W.ι ''ᵁ (g ⁻¹ᵁ (U.ι ⁻¹ᵁ V))
    rw [U.ι.preimage_image_eq]
  change M.presheaf.map (eqToHom W.ι_image_top.symm).op
      (M.presheaf.map (eqToHom hBC).op
        (M.presheaf.map (eqToHom hAB).op
          (M.presheaf.map (homOfLE (W.ι.image_preimage_le (f ⁻¹ᵁ V))).op (h.app V x)))) =
    M.presheaf.map (homOfLE hW).op (h.app U (N.presheaf.map (eqToHom U.ι_image_top.symm).op x))
  rw [show h.app U (N.presheaf.map (eqToHom U.ι_image_top.symm).op x) =
    M.presheaf.map ((Opens.map f.base).map (eqToHom U.ι_image_top.symm)).op (h.app _ x) from
      PresheafOfModules.naturality_apply h.val (eqToHom U.ι_image_top.symm).op x]
  have he : eqToHom W.ι_image_top.symm ≫ eqToHom hBC ≫ eqToHom hAB ≫
      homOfLE (W.ι.image_preimage_le (f ⁻¹ᵁ V)) =
      homOfLE hW ≫ (Opens.map f.base).map (eqToHom U.ι_image_top.symm) :=
    Subsingleton.elim _ _
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg (fun i : W ⟶ f ⁻¹ᵁ V ↦ M.presheaf.map i.op (h.app V x)) he

/-- For two free sheaves of rank one, the pullback is an isomorphism when
the image of the target generator is a unit in the source frame. -/
private theorem local_adjoint_isIso {f : X ⟶ Y}
    {N : Y.Modules} {M : X.Modules} (h : N ⟶ (pushforward f).obj M)
    (eN : N ≅ SheafOfModules.unit Y.ringCatSheaf)
    (eM : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (hu : @IsUnit (Γ(X, ⊤) : Type u) _ (eM.hom.app ⊤ (h.app ⊤ (eN.inv.app ⊤ (1 : Γ(Y, ⊤)))))) :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv _ _).symm h) := by
  let adj := pullbackPushforwardAdjunction f
  let v := (adj.homEquiv _ _).symm h
  let c : (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  haveI : IsIso c := inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom))
  let z := inv c ≫ (Scheme.Modules.pullback f).map eN.inv ≫ v ≫ eM.hom
  have hz : c ≫ z = (Scheme.Modules.pullback f).map eN.inv ≫ v ≫ eM.hom := by simp [z]
  have hLeft : adj.homEquiv _ _ (c ≫ z) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ (pushforward f).map z := by
    rw [adj.homEquiv_naturality_right]
    exact congrArg (· ≫ (pushforward f).map z) (Equiv.apply_symm_apply _ _)
  have hRight : adj.homEquiv _ _ ((Scheme.Modules.pullback f).map eN.inv ≫ v ≫ eM.hom) =
      eN.inv ≫ h ≫ (pushforward f).map eM.hom := by
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have he := hLeft.symm.trans ((congrArg (adj.homEquiv _ _) hz).trans hRight)
  have hz1 : z.app ⊤ (1 : Γ(X, ⊤)) =
    eM.hom.app ⊤ (h.app ⊤ (eN.inv.app ⊤ (1 : Γ(Y, ⊤)))) := by
    have h1 := congrArg (fun a : structureModule Y ⟶
        (pushforward f).obj (structureModule X) ↦ a.app ⊤ (1 : Γ(Y, ⊤))) he
    simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at h1
    change z.app ⊤ (f.appTop (1 : Γ(Y, ⊤))) =
      eM.hom.app ⊤ (h.app ⊤ (eN.inv.app ⊤ (1 : Γ(Y, ⊤)))) at h1
    simpa only [map_one] using h1
  haveI : IsIso z := unit_endomorphism_isIso _ (hz1.symm ▸ hu)
  haveI : IsIso ((Scheme.Modules.pullback f).map eN.inv ≫ (v ≫ eM.hom)) := by rw [← hz]; infer_instance
  haveI : IsIso (v ≫ eM.hom) := IsIso.of_isIso_comp_left (f := (Scheme.Modules.pullback f).map eN.inv) _
  exact IsIso.of_isIso_comp_right v eM.hom


end OpenRestriction

section Pullback

open private torsorDifference torsorDifference_value quotient_right_mul
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open private descends from LinearAlgebraicGroups.Reductive.BorelProper

variable {G G' : AffineAlgebraicGroup k} {P : OppositeBorelPair G} {P' : OppositeBorelPair G'}
    {Q : Presentation P.negative} {Q' : Presentation P'.negative}

/-- The quotient map induced by a homomorphism carrying the source Borel
into the target Borel. -/
def inducedQuotientMap (g : G.val ⟶ G'.val) (b : P.negative.group ⟶ P'.negative.group)
    (h : P.negative.inclusion ≫ g = b ≫ P'.negative.inclusion) : QuotientMap Q Q' := by
  haveI := Q.flat
  haveI := Q.surjective
  haveI := Q.finitePresentation
  have hex : ∃ f : Q.scheme ⟶ Q'.scheme, Q.projection ≫ f = g.hom.hom ≫ Q'.projection := by
    apply descends
    intro T r s e
    let d := torsorDifference Q r s e
    have hd : s = r * (d ≫ P.negative.inclusion.hom.hom) := by
      rw [torsorDifference_value, mul_inv_cancel_left]
    have hb : P.negative.inclusion.hom.hom ≫ g.hom.hom =
        b.hom.hom ≫ P'.negative.inclusion.hom.hom :=
      congrArg (fun z : P.negative.group ⟶ G'.val ↦ z.hom.hom) h
    rw [← Category.assoc, ← Category.assoc]
    conv_rhs => rw [hd, MonObj.mul_comp, Category.assoc, hb, ← Category.assoc, quotient_right_mul]
  exact ⟨g, b, hex.choose, h, hex.choose_spec⟩

variable (f : QuotientMap Q Q')
    {p : BorelProjection P} {p' : BorelProjection P'}
    {χ : CharacterDescent.Character P.torus.group} {χ' : CharacterDescent.Character P'.torus.group}
    (hf : CompatibleCharacters f p p' χ χ')

include hf in
private theorem pullFunction_covariant (U : Q'.scheme.left.Opens)
    (r : Γ(G'.val.X.left, Q'.projection.left ⁻¹ᵁ U))
    (hr : IsCovariantOn Q' p' χ' U r) :
    IsCovariantOn Q p χ (f.flag.left ⁻¹ᵁ U) (pullFunction f U r) := by
  intro T g b h h'
  let m := f.group.hom.hom
  let n := f.borel.hom.hom
  let gb := g * (b ≫ P.negative.inclusion.hom.hom)
  have hsq : Q.projection.left ≫ f.flag.left = m.left ≫ Q'.projection.left :=
    congrArg Over.Hom.left f.commutesFlag
  have hmul : gb ≫ m = (g ≫ m) * ((b ≫ n) ≫ P'.negative.inclusion.hom.hom) := by
    have hB : P.negative.inclusion.hom.hom ≫ m = n ≫ P'.negative.inclusion.hom.hom :=
      congrArg (fun a : P.negative.group ⟶ G'.val ↦ a.hom.hom) f.commutesBorel
    simp only [gb, MonObj.mul_comp, Category.assoc, hB]
  have h₀ : (⊤ : T.left.Opens) ≤ (g.left ≫ m.left) ⁻¹ᵁ (Q'.projection.left ⁻¹ᵁ U) := by
    change (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ ((m.left ≫ Q'.projection.left) ⁻¹ᵁ U)
    rw [← hsq]
    exact h
  have h₁ : (⊤ : T.left.Opens) ≤ (gb.left ≫ m.left) ⁻¹ᵁ (Q'.projection.left ⁻¹ᵁ U) := by
    change (⊤ : T.left.Opens) ≤ gb.left ⁻¹ᵁ ((m.left ≫ Q'.projection.left) ⁻¹ᵁ U)
    rw [← hsq]
    exact h'
  change evalOn gb.left _ h' (pullFunction f U r) =
    characterFunction (p.projection ≫ χ) b⁻¹ * evalOn g.left _ h (pullFunction f U r)
  unfold pullFunction
  rw [evalOn_comp gb.left m.left _ _ _ h' h₁, evalOn_comp g.left m.left _ _ _ h h₀]
  have eh : (b⁻¹ : T ⟶ P.negative.group.X) ≫ n = (b ≫ n)⁻¹ := GrpObj.inv_comp b n
  have hc : characterFunction (p.projection ≫ χ) b⁻¹ =
      characterFunction (p'.projection ≫ χ') (b ≫ n)⁻¹ := by
    have hchar : p.projection ≫ χ = f.borel ≫ (p'.projection ≫ χ') := hf
    rw [hchar, characterFunction_characterComp, eh]
  have hm : gb.left ≫ m.left =
      ((g ≫ m) * ((b ≫ n) ≫ P'.negative.inclusion.hom.hom)).left :=
    congrArg Over.Hom.left hmul
  have hh : (⊤ : T.left.Opens) ≤
      ((g ≫ m) * ((b ≫ n) ≫ P'.negative.inclusion.hom.hom)).left ⁻¹ᵁ
      (Q'.projection.left ⁻¹ᵁ U) := by rwa [← hm]
  rw [hc, evalOn_congr hm _ h₁ hh]
  exact hr T (g ≫ m) (b ≫ n) h₀ hh

variable {a : ModObj G.val.X Q.scheme} {a' : ModObj G'.val.X Q'.scheme}
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' χ'}
    (M : SectionRealization L) (M' : SectionRealization L')

private def pullSection (U : Q'.scheme.left.Opens) (x : Γ(M'.sheaf, U)) :
    Γ(M.sheaf, f.flag.left ⁻¹ᵁ U) :=
  ((M.functions_range _ _).mpr (pullFunction_covariant f hf U _
    ((M'.functions_range U _).mp ⟨x, rfl⟩))).choose

private theorem pullSection_function (U : Q'.scheme.left.Opens) (x : Γ(M'.sheaf, U)) :
    M.functionVal (f.flag.left ⁻¹ᵁ U) (pullSection f hf M M' U x) =
      pullFunction f U (M'.functionVal U x) :=
  ((M.functions_range _ _).mpr (pullFunction_covariant f hf U _
    ((M'.functions_range U _).mp ⟨x, rfl⟩))).choose_spec

private theorem pullFunction_scalar (U : Q'.scheme.left.Opens) (r : Γ(Q'.scheme.left, U)) :
    pullFunction f U (Q'.projection.left.app U r) =
      Q.projection.left.app (f.flag.left ⁻¹ᵁ U) (f.flag.left.app U r) := by
  unfold pullFunction
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.appLE_eq_app Q'.projection.left,
    Scheme.Hom.appLE_comp_appLE]
  have hsq : f.group.hom.hom.left ≫ Q'.projection.left = Q.projection.left ≫ f.flag.left :=
    congrArg Over.Hom.left f.commutesFlag.symm
  have hcongr {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g')
      (U : Y.Opens) (V : X.Opens) (h₀ : V ≤ g ⁻¹ᵁ U) (h₁ : V ≤ g' ⁻¹ᵁ U) :
      g.appLE U V h₀ = g'.appLE U V h₁ := by subst h; rfl
  let V := Q.projection.left ⁻¹ᵁ (f.flag.left ⁻¹ᵁ U)
  rw [hcongr hsq U V (by rw [hsq]; exact le_rfl) (show V ≤ _ from le_rfl)]
  have h := Scheme.Hom.appLE_eq_app (Q.projection.left ≫ f.flag.left) (U := U)
  exact congrArg (fun a : Γ(Q'.scheme.left, U) ⟶ Γ(G.val.X.left, V) ↦ a r) h

/-- The direct-image form of pullback on covariant functions. -/
def pullSections : M'.sheaf ⟶ (Scheme.Modules.pushforward f.flag.left).obj M.sheaf :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := pullSection f hf M M' U.unop
          map_zero' := by
            apply M.functions_injective
            change M.functionVal _ (pullSection f hf M M' U.unop 0) = M.functionVal _ 0
            rw [pullSection_function]
            simp only [SectionRealization.functionVal, pullFunction, map_zero]
          map_add' := by
            intro x y
            apply M.functions_injective
            change M.functionVal _ (pullSection f hf M M' U.unop (x + y)) =
              M.functionVal _ (pullSection f hf M M' U.unop x + pullSection f hf M M' U.unop y)
            rw [pullSection_function]
            rw [show M.functionVal _ (pullSection f hf M M' U.unop x + pullSection f hf M M' U.unop y) =
              M.functionVal _ (pullSection f hf M M' U.unop x) +
                M.functionVal _ (pullSection f hf M M' U.unop y) from map_add (M.functions.app _).hom _ _,
              pullSection_function, pullSection_function]
            unfold SectionRealization.functionVal pullFunction
            rw [map_add (M'.functions.app _).hom, map_add] }
      naturality := by
        intro U V i
        ext : 1
        apply DFunLike.ext
        intro x
        let j := ((Opens.map f.flag.left.base).map i.unop).op
        change pullSection f hf M M' V.unop (M'.sheaf.presheaf.map i x) =
          M.sheaf.presheaf.map j (pullSection f hf M M' U.unop x)
        apply M.functions_injective
        have hM := PresheafOfModules.naturality_apply M.functions.val j
          (pullSection f hf M M' U.unop x)
        have hM' := PresheafOfModules.naturality_apply M'.functions.val i x
        change M.functionVal _ (M.sheaf.presheaf.map j _) =
          G.val.X.left.presheaf.map ((Opens.map Q.projection.left.base).map j.unop).op
            (M.functionVal _ _) at hM
        change M'.functionVal _ (M'.sheaf.presheaf.map i x) =
          G'.val.X.left.presheaf.map ((Opens.map Q'.projection.left.base).map i.unop).op
            (M'.functionVal _ x) at hM'
        change M.functionVal _ _ = M.functionVal _ _
        rw [pullSection_function, hM, pullSection_function, hM']
        simp only [pullFunction, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] }
    (by
      intro U r x
      let r' : Γ(Q'.scheme.left, U.unop) := r
      let r'' : Γ(Q.scheme.left, f.flag.left ⁻¹ᵁ U.unop) := f.flag.left.app U.unop r'
      change pullSection f hf M M' U.unop (r' • x) =
        r'' • pullSection f hf M M' U.unop x
      apply M.functions_injective
      have hs : ∀ (z : Γ(M'.sheaf, U.unop)),
          M'.functionVal U.unop (r' • z) =
            Q'.projection.left.app U.unop r' * M'.functionVal U.unop z :=
        fun z ↦ (Scheme.Modules.Hom.app_smul M'.functions r' z).trans
          (functionsOver_smul _ _ _ _)
      change M.functionVal _ _ = M.functionVal _ _
      rw [pullSection_function, hs]
      have ht : ∀ (z : Γ(M.sheaf, f.flag.left ⁻¹ᵁ U.unop)),
          M.functionVal _ (r'' • z) =
            Q.projection.left.app _ r'' * M.functionVal _ z :=
        fun z ↦ (Scheme.Modules.Hom.app_smul M.functions r'' z).trans
          (functionsOver_smul _ _ _ _)
      rw [ht, pullSection_function]
      have hm : ∀ r₁ r₂ : Γ(G'.val.X.left, Q'.projection.left ⁻¹ᵁ U.unop),
          pullFunction f U.unop (r₁ * r₂) = pullFunction f U.unop r₁ * pullFunction f U.unop r₂ :=
        fun r₁ r₂ ↦ map_mul (f.group.hom.hom.left.appLE _ _ _).hom r₁ r₂
      rw [hm, pullFunction_scalar])⟩

theorem covariantPullbackMap : CovariantPullbackMap.{u} := by
  intro k _ G G' P P' Q Q' a a' p p' χ χ' L L' M M' f hf
  exact ⟨pullSections f hf M M', pullSection_function f hf M M'⟩

private theorem characterFunction_isUnit {H : GroupScheme k}
    (ψ : CharacterDescent.Character H) {T : SchemeOver k} (b : T ⟶ H.X) :
    IsUnit (characterFunction ψ b) := by
  have e : characterFunction ψ b * characterFunction ψ b⁻¹ = 1 := by
    rw [← characterFunction_mul (H := wholeGroup H), mul_inv_cancel,
      characterFunction_one (H := wholeGroup H)]
  exact IsUnit.of_mul_eq_one _ e

theorem pullbackChartUnits : PullbackChartUnits.{u} := by
  intro k _ G G' P P' Q Q' a a' p p' χ χ' L L' M M' f hf h hh U s' W s hW x hx
  let j := homOfLE hW
  let i := IsOpenImmersion.lift U.ι (W.ι ≫ f.flag.left) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨(W.ι ≫ f.flag.left) y, hW y.property⟩, rfl⟩)
  have hi : i ≫ U.ι = W.ι ≫ f.flag.left := IsOpenImmersion.lift_fac _ _ _
  let i' : openOver Q.scheme W ⟶ openOver Q'.scheme U :=
    Over.homMk i (by
      change i ≫ U.ι ≫ Q'.scheme.hom = W.ι ≫ Q.scheme.hom
      rw [← Category.assoc, hi, Category.assoc, Over.w])
  let r := i' ≫ s'.lift
  let t := s.lift ≫ f.group.hom.hom
  have ht : t.left ≫ Q'.projection.left = W.ι ≫ f.flag.left := by
    change (s.lift.left ≫ f.group.hom.hom.left) ≫ Q'.projection.left = _
    rw [Category.assoc, ← show Q.projection.left ≫ f.flag.left =
      f.group.hom.hom.left ≫ Q'.projection.left from congrArg Over.Hom.left f.commutesFlag,
      ← Category.assoc, s.lifts]
  have hrt : r ≫ Q'.projection = t ≫ Q'.projection := by
    apply Over.OverMorphism.ext
    change (i ≫ s'.lift.left) ≫ Q'.projection.left = t.left ≫ Q'.projection.left
    rw [Category.assoc, s'.lifts, hi, ht]
  let b := torsorDifference Q' r t hrt
  have hb : t = r * (b ≫ P'.negative.inclusion.hom.hom) := by
    rw [torsorDifference_value, mul_inv_cancel_left]
  let Atr := Q'.projection.left ⁻¹ᵁ U
  let rt : Γ(G'.val.X.left, Atr) := M'.functionVal U x
  have ht' : (⊤ : W.toScheme.Opens) ≤ t.left ⁻¹ᵁ Atr := by
    change (⊤ : W.toScheme.Opens) ≤ (t.left ≫ Q'.projection.left) ⁻¹ᵁ U
    rw [ht]
    intro y _
    exact hW y.property
  have hr' : (⊤ : W.toScheme.Opens) ≤ r.left ⁻¹ᵁ Atr := by
    have e : r.left ≫ Q'.projection.left = t.left ≫ Q'.projection.left :=
      congrArg Over.Hom.left hrt
    change (⊤ : W.toScheme.Opens) ≤ (r.left ≫ Q'.projection.left) ⁻¹ᵁ U
    rw [e]
    exact ht'
  have he : evalOn r.left Atr hr' rt = 1 := by
    have hh' := chartValue_eq M' s' x
    rw [hx, map_one] at hh'
    have er := evalOn_comp i s'.lift.left Atr ⊤ (lift_in_open s') (by simp) hr' rt
    rw [evalOn_top] at er
    change i.appTop (evalOn s'.lift.left Atr (lift_in_open s') rt) = _ at er
    change evalOn (i ≫ s'.lift.left) Atr hr' rt = 1
    rw [← er, ← hh', map_one]
  have hcv := (M'.functions_range U _).mp ⟨x, rfl⟩ (openOver Q.scheme W) r b hr'
    (by rw [← hb]; exact ht')
  have hc : evalOn t.left Atr ht' rt = characterFunction (p'.projection ≫ χ') b⁻¹ := by
    rw [evalOn_congr (congrArg Over.Hom.left hb.symm) _ _ ht', he, mul_one] at hcv
    exact hcv
  let y := M.sheaf.presheaf.map j.op (h.app U x)
  change IsUnit (chartValue M s y)
  have hy := PresheafOfModules.naturality_apply M.functions.val j.op (h.app U x)
  let j' := ((Opens.map Q.projection.left.base).map j).op
  change M.functionVal W y = G.val.X.left.presheaf.map j'
    (M.functionVal (f.flag.left ⁻¹ᵁ U) (h.app U x)) at hy
  rw [hh] at hy
  have heval : evalOn s.lift.left _ (lift_in_open s) (M.functionVal W y) =
      evalOn t.left Atr ht' rt := by
    rw [hy]
    unfold evalOn pullFunction
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE]
    rfl
  unfold chartValue
  change IsUnit (W.topIso.hom (evalOn s.lift.left _ (lift_in_open s) (M.functionVal W y)))
  rw [heval, hc]
  exact (characterFunction_isUnit (p'.projection ≫ χ') b⁻¹).map W.topIso.hom.hom

open Scheme.Modules in
private theorem chartIso_top {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme} {p : BorelProjection P}
    {χ : CharacterDescent.Character P.torus.group} {L : AssociatedBundle Q a p χ}
    (M : SectionRealization L) {U : Q.scheme.left.Opens} (s : TorsorLift Q U)
    (x : Γ(M.sheaf.restrict U.ι, ⊤)) :
    (chartIso M s).hom.app ⊤ x =
      U.topIso.inv (chartValue M s ((restrictTopSections M.sheaf U).hom x)) := by
  let e := U.ι_image_top
  let V := U.ι ''ᵁ (⊤ : U.toScheme.Opens)
  let i : V ⟶ U := homOfLE e.le
  let x' := (restrictTopSections M.sheaf U).hom x
  have hx : M.sheaf.presheaf.map i.op x' = x := by
    change M.sheaf.presheaf.map i.op (M.sheaf.presheaf.map (eqToHom e.symm).op x) = x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have eq : (eqToHom e.symm).op ≫ i.op = 𝟙 _ := Subsingleton.elim _ _
    rw [eq]
    let xV : Γ(M.sheaf, V) := x
    exact congrArg (fun a : Γ(M.sheaf, V) ⟶ Γ(M.sheaf, V) ↦ a xV)
      (M.sheaf.presheaf.map_id (op V))
  change chartValue M (restrictLift e.le s) x = _
  calc
    _ = chartValue M (restrictLift e.le s) (M.sheaf.presheaf.map i.op x') :=
      congrArg _ hx.symm
    _ = Q.scheme.left.presheaf.map i.op (chartValue M s x') := chartValue_natural M e.le s x'
    _ = _ := rfl

open Scheme.Modules in
/-- The canonical pullback of covariant functions gives the associated
line sheaf for the pulled-back character. -/
theorem associatedSheafPullback : AssociatedSheafPullback.{u} := by
  intro k _ G G' P P' Q Q' a a' p p' χ χ' L L' M M' f hf
  let m := f.flag.left
  let h := pullSections f hf M M'
  let adj := pullbackPushforwardAdjunction m
  let v := (adj.homEquiv M'.sheaf M.sheaf).symm h
  haveI : IsIso v := by
    apply isIso_of_open_restrictions
    intro y
    obtain ⟨U, hyU, ⟨s'⟩⟩ := chartCover Q' (m y)
    obtain ⟨V, hyV, ⟨s₀⟩⟩ := chartCover Q y
    let W := V ⊓ m ⁻¹ᵁ U
    let s := restrictLift (W := W) inf_le_left s₀
    have hW : W ≤ m ⁻¹ᵁ U := inf_le_right
    refine ⟨W, ⟨hyV, hyU⟩, restrict_adjoint_isIso m hW h ?_⟩
    let targetChart := chartIso M' s'
    let sourceChart := chartIso M s
    apply local_adjoint_isIso _ targetChart sourceChart
    let x₀ := targetChart.inv.app ⊤ (1 : Γ(U.toScheme, ⊤))
    let x := (restrictTopSections M'.sheaf U).hom x₀
    have hx₀ : targetChart.hom.app ⊤ x₀ = (1 : Γ(U.toScheme, ⊤)) := by
      change (targetChart.inv ≫ targetChart.hom).app ⊤ (1 : Γ(U.toScheme, ⊤)) = _
      rw [Iso.inv_hom_id]
      rfl
    have hx : chartValue M' s' x = 1 := by
      have eq := (chartIso_top M' s' x₀).symm.trans hx₀
      exact (ConcreteCategory.bijective_of_isIso U.topIso.inv).1 (eq.trans (map_one U.topIso.inv.hom).symm)
    have hu := pullbackChartUnits M M' f hf h (pullSection_function f hf M M') U s' W s hW x hx
    change @IsUnit (Γ(W.toScheme, ⊤) : Type u) _
      ((chartIso M s).hom.app ⊤ ((restrictDirectImageHom m hW h).app ⊤ x₀))
    rw [chartIso_top, restrictDirectImageHom_top]
    exact hu.map W.topIso.inv.hom
  refine ⟨asIso v, fun U x ↦ ?_⟩
  change M.functionVal _ ((adj.homEquiv _ _ v).app U x) = _
  rw [Equiv.apply_symm_apply]
  exact pullSection_function f hf M M' U x

/-- The flag map in the pullback comparison is induced by the two group
morphisms and the original quotient projections. -/
theorem inducedAssociatedSheafPullback : InducedAssociatedSheafPullback.{u} := by
  intro k _ G G' P P' Q Q' a a' p p' χ χ' L L' M M' g b hB hχ
  let f : QuotientMap Q Q' := inducedQuotientMap g b hB
  exact ⟨f, rfl, rfl, associatedSheafPullback M M' f hχ⟩

end Pullback

section Frobenius

open RelativeFrobenius (extendAlong scalarTensor)
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private integerHopfHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent

private theorem specCharacter_eq_pow {D : HopfAlgebraCategory k}
    {φ ψ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D}
    (n : ℕ) (h : characterCoordinate ψ = characterCoordinate φ ^ n) :
    (specGroupMap ψ : CharacterDescent.Character (specGroup D)) = specGroupMap φ ^ n := by
  let e := LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv D
  have he (c : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D) :
      e ((integerHopfHomEquiv D).symm c) = specGroupMap c := by
    change specGroupMap ((integerHopfHomEquiv D) ((integerHopfHomEquiv D).symm c)) = _
    rw [Equiv.apply_symm_apply]
  rw [← he ψ, ← he φ, ← map_pow]
  congr 1
  exact GroupLike.val_injective h

private theorem comp_character_pow {H H' : GroupScheme k} (b : H ⟶ H')
    (χ : CharacterDescent.Character H') (n : ℕ) :
    b ≫ χ ^ n = (b ≫ χ) ^ n := by
  apply Grp.hom_ext
  change b.hom.hom ≫ (χ ^ n).hom.hom = ((b ≫ χ) ^ n).hom.hom
  simp only [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  exact MonObj.comp_pow χ.hom.hom n b.hom.hom

/-- Relative Frobenius pulls back the transported flag line by raising
the character to the Frobenius power. -/
theorem frobeniusAssociatedSheafPullback : FrobeniusAssociatedSheafPullback.{u} := by
  intro k _ ℓ r _ _ G G' P P' Q Q' a a' p p' χ χ' L L' M M' A D e d
  dsimp only
  intro e' d' F F_B φ φ' _ hF_B hB hφ hφ' hbase
  let g := e.inv ≫ specGroupMap F ≫ e'.hom
  let b := d.inv ≫ specGroupMap F_B ≫ d'.hom
  have hb : d.hom ≫ b = specGroupMap F_B ≫ d'.hom := by simp [b]
  have hpow : characterCoordinate (φ' ≫ F_B) = characterCoordinate φ ^ (ℓ ^ r) := by
    change F_B.hom (characterCoordinate φ') = _
    rw [hbase, hF_B 1, one_smul]
  refine inducedAssociatedSheafPullback M M' g b hB ?_
  apply (cancel_epi d.hom).mp
  calc
    d.hom ≫ p.projection ≫ χ ^ (ℓ ^ r) = (d.hom ≫ p.projection ≫ χ) ^ (ℓ ^ r) := by
      rw [← Category.assoc, comp_character_pow, Category.assoc]
    _ = specGroupMap (φ' ≫ F_B) := by rw [specCharacter_eq_pow _ hpow, hφ]
    _ = d.hom ≫ b ≫ p'.projection ≫ χ' := by
      rw [specGroupMap_comp, hφ']
      simp only [← Category.assoc, hb]

end Frobenius

end

end LinearAlgebraicGroups.AssociatedFlagLineSheaves
