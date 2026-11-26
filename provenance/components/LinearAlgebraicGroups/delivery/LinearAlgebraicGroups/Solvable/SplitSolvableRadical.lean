import Specs.LinearAlgebraicGroups.Solvable.SplitSolvableRadical
import LinearAlgebraicGroups.Affine.FaithfulLinearization
import LinearAlgebraicGroups.Flag.FlagSchemes
import LinearAlgebraicGroups.Solvable.SplitFixedPoint
import LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.SplitSolvableRadical

open _root_.LinearAlgebraicGroups.Specs
open Specs.SplitSolvableRadical
open Specs.SmoothDiagonalKernel
open Specs.SchemeDerivedGroup
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup IsUnipotent)
open Specs.FlagSchemes

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
set_option maxHeartbeats 450000

variable {k : Type u} [Field k]

open private actionOfSections fixed_iff_sections split_fixed_has_point
  from LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private isoOfPointIso underlyingFunctor from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel

section Flag

set_option backward.isDefEq.respectTransparency.types true

private theorem morphismToBase {X : SchemeOver k}
    (p : X ⟶ (testSpec k).obj (op (CommAlgCat.of k k))) :
    p = toBasePoint X := by
  apply Over.OverMorphism.ext
  change p.left = X.hom
  have hbase : ((testSpec k).obj (op (CommAlgCat.of k k))).hom = 𝟙 (Spec (CommRingCat.of k)) :=
    Spec.map_id (CommRingCat.of k)
  let a : X.left ⟶ Spec (CommRingCat.of k) := p.left
  change a = X.hom
  have hc : a ≫ ((testSpec k).obj (op (CommAlgCat.of k k))).hom = a ≫ 𝟙 _ :=
    congrArg (fun z : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) ↦ a ≫ z) hbase
  exact ((Category.comp_id a).symm.trans hc.symm).trans (Over.w p)

private theorem transitiveOnRationalPoints {F L : SchemeOver k}
    (a : L ⨯ F ⟶ F) (x z : Points F (CommAlgCat.of k k))
    (h : ∃ (R : TestAlgebra k) (p : Points (testSpec k |>.obj (op (CommAlgCat.of k k))) R)
      (g : Points L R), IsOpenImmersion p.left ∧
        Nonempty (testSpec k |>.obj (op R)).left ∧
        prod.lift g (mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) z) ≫ a = p ≫ x) :
    ∃ g : Points L (CommAlgCat.of k k), prod.lift g z ≫ a = x := by
  obtain ⟨R, p, g, hp, hR, eq⟩ := h
  letI := hp
  haveI : Subsingleton ((testSpec k).obj (op (CommAlgCat.of k k))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have hs : Surjective p.left := ⟨fun y ↦
    ⟨Classical.choice hR, Subsingleton.elim _ _⟩⟩
  letI := hs
  letI : IsIso p.left := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hp, hs⟩
  letI : IsIso p := by
    letI : IsIso ((Over.forget _).map p) := inferInstanceAs (IsIso p.left)
    exact isIso_of_reflects_iso p (Over.forget _)
  refine ⟨inv p ≫ g, ?_⟩
  have hz : mapPoints (CommAlgCat.ofHom (Algebra.ofId k R)) z = p ≫ z := by
    change (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k R)).op ≫ z = p ≫ z
    exact congrArg (fun f : _ ⟶ (testSpec k).obj (op (CommAlgCat.of k k)) ↦ f ≫ z)
      ((morphismToBase _).trans (morphismToBase p).symm)
  rw [hz] at eq
  rw [← cancel_epi p, ← Category.assoc, prod.comp_lift, IsIso.hom_inv_id_assoc, eq]

private def conjugateMatrixPoints {n : ℕ}
    (m : Matrix.GeneralLinearGroup (Index.{u} n) k) :
    StandardGroups.generalLinearPoints k (Index.{u} n) ≅
      StandardGroups.generalLinearPoints k (Index.{u} n) := by
  let F := StandardGroups.generalLinearPoints k (Index.{u} n)
  let m₀ : F.obj (CommAlgCat.of k k) := m
  let c (R : TestAlgebra k) : F.obj R :=
    F.map (CommAlgCat.ofHom (Algebra.ofId k R)) m₀
  refine NatIso.ofComponents (fun R ↦ (MulAut.conj (c R)).symm.toGrpIso) ?_
  intro R S f
  have hc : F.map f (c R) = c S := by
    have h : CommAlgCat.ofHom (Algebra.ofId k R) ≫ f =
        CommAlgCat.ofHom (Algebra.ofId k S) := by ext
    change F.map f (F.map (CommAlgCat.ofHom (Algebra.ofId k R)) m₀) = _
    rw [← GrpCat.comp_apply, ← F.map_comp, h]
  apply GrpCat.ext
  intro x
  change (c S)⁻¹ * F.map f x * c S = F.map f ((c R)⁻¹ * x * c R)
  rw [map_mul, map_mul, map_inv, hc]

private theorem fixedPointOfProductAction {G L : GroupScheme k} (X : SchemeOver k)
    (f : G ⟶ L) (a : L.X ⨯ X ⟶ X)
    (h₁ : ∀ (S : SchemeOver k) (x : S ⟶ X), prod.lift (1 : S ⟶ L.X) x ≫ a = x)
    (h₂ : ∀ (S : SchemeOver k) (g h : S ⟶ L.X) (x : S ⟶ X),
      prod.lift (g * h) x ≫ a = prod.lift g (prod.lift h x ≫ a) ≫ a)
    (hsplit : IsSplitSolvable G)
    (hG : IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom)
    (hproper : IsProper X.hom) (z : Points X (CommAlgCat.of k k)) :
    ∃ x : Points X (CommAlgCat.of k k), ∀ (R : TestAlgebra k) (g : Points G.X R),
      let a₀ : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
      let xR := mapPoints a₀ x
      prod.lift (g ≫ f.hom.hom) xR ≫ a = xR := by
  let c : L.X ⊗ X ⟶ L.X ⨯ X := prod.lift (fst L.X X) (snd L.X X)
  have hc {W : SchemeOver k} (g : W ⟶ L.X) (p : W ⟶ X) :
      lift g p ≫ c = prod.lift g p := by simp [c, prod.comp_lift]
  let actL : ModObj L.X X := actionOfSections (c ≫ a)
    (by intro S p; rw [← Category.assoc, hc, h₁])
    (by intro S g h p; simp only [← Category.assoc, hc]; exact h₂ S g h p)
  letI := actL
  let actG : ModObj G.X X := Mod.scalarRestriction f.hom.hom X
  let B : SchemeOver k := (testSpec k).obj (op (CommAlgCat.of k k))
  letI := hproper
  obtain ⟨x, hx⟩ := split_fixed_has_point hsplit hG (act := actG)
    (toBasePoint (𝟙_ (SchemeOver k)) ≫ z)
  refine ⟨toUnit B ≫ x, ?_⟩
  intro R g a₀ xR
  have he := (fixed_iff_sections (H := G) (act := actG) x).mp hx
    (toUnit ((testSpec k).obj (op R))) g
  have eR : xR = toUnit ((testSpec k).obj (op R)) ≫ x := by
    change (testSpec k).map a₀.op ≫ toUnit B ≫ x = _
    rw [comp_toUnit_assoc]
  rw [← eR] at he
  change lift g xR ≫ (f.hom.hom ▷ X) ≫ c ≫ a = xR at he
  rw [← Category.assoc (lift g xR) (f.hom.hom ▷ X), lift_whiskerRight,
    ← Category.assoc, hc] at he
  exact he

private theorem mapConjugation {A B : GrpCat.{u}} (f : A ⟶ B) (g x : A) :
    f (g⁻¹ * x * g) = (f g)⁻¹ * f x * f g := by
  change f.hom (g⁻¹ * x * g) = (f.hom g)⁻¹ * f.hom x * f.hom g
  simp only [map_mul, map_inv]

/-- A rational fixed flag, expressed in an adapted basis, triangularizes a faithful
representation on every test algebra. -/
theorem faithfulTriangularization : FaithfulTriangularization.{u} := by
  intro k _ G hsplit
  classical
  obtain ⟨n, H, ⟨e⟩, j, hj⟩ := faithfulLinearization k G
  let V := Fin n → k
  let β : Module.Basis (Fin n) k V := Pi.basisFun k (Fin n)
  let ranks : Fin n → ℕ := Fin.val
  have hr (i : Fin n) : ranks i ≤ Module.finrank k V := by
    simp [V, ranks, Module.finrank_fintype_fun_eq_card]
  obtain ⟨P, D, L, E, A, _, hpoints, _, hlocal, ⟨proj⟩, ⟨C⟩⟩ :=
    FlagSchemes.flagSchemeGeometry k V n β n ranks (fun _ _ hij ↦ hij) hr
  let w := (groupHomEquiv H.val L H.property.1).symm (e.hom ≫ E.inv)
  have hw : (groupPointsFunctor k).map w = e.hom ≫ E.inv :=
    (groupHomEquiv H.val L H.property.1).apply_symm_apply _
  let f := j ≫ w
  let B := (testSpec k).obj (op (CommAlgCat.of k k))
  obtain ⟨x₀, hx₀⟩ := fixedPointOfProductAction D.scheme f A.onFlags A.one A.mul
    hsplit G.property proj.proper C.point
  obtain ⟨z, hz, ht⟩ := hlocal n β
  have hzC : z = C.point := by
    obtain ⟨Eflag, hEflag, _⟩ := hpoints
    apply (Eflag _).injective
    apply Specs.FlagSchemes.Flag.ext
    intro i
    apply Module.Grassmannian.ext
    rw [hEflag, hEflag, hz, C.point_formula]
  subst z
  obtain ⟨R, a, g, ha, hnon, he⟩ := ht B x₀ (Classical.choice (inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))))
  obtain ⟨g₀, hg₀⟩ := transitiveOnRationalPoints A.onFlags x₀ C.point
    ⟨R, a, g, ha, ⟨hnon.choose⟩, he⟩
  let m : Matrix.GeneralLinearGroup (Index.{u} n) k := E.hom.app _ g₀
  refine ⟨n, H, j, e ≪≫ conjugateMatrixPoints m, hj, ?_⟩
  intro S y
  let a₀ : CommAlgCat.of k k ⟶ S := CommAlgCat.ofHom (Algebra.ofId k S)
  let gS : Points L.X S := mapPoints a₀ g₀
  let zS : Points D.scheme S := mapPoints a₀ C.point
  let xS : Points D.scheme S := mapPoints a₀ x₀
  let yL : Points L.X S := y ≫ f.hom.hom
  have hgS : prod.lift gS zS ≫ A.onFlags = xS := by
    have he := congrArg ((testSpec k).map a₀.op ≫ ·) hg₀
    rw [← Category.assoc, prod.comp_lift] at he
    exact he
  have hyL : prod.lift yL xS ≫ A.onFlags = xS := hx₀ S y
  let h : Points L.X S := gS⁻¹ * yL * gS
  have hfix : prod.lift h zS ≫ A.onFlags = zS := by
    rw [show h = gS⁻¹ * (yL * gS) from mul_assoc .., A.mul, A.mul, hgS, hyL,
      ← hgS, ← A.mul, inv_mul_cancel, A.one]
  have hzS : zS = toBasePoint ((testSpec k).obj (op S)) ≫ C.point := by
    have he : (testSpec k).map a₀.op = toBasePoint ((testSpec k).obj (op S)) :=
      morphismToBase _
    exact congrArg (· ≫ C.point) he
  have hthrough : ∃ q : Points (coordinateFlagLocus k (Index n) (prefixCuts ranks)) S,
      q ≫ (coordinateFlagInclusion k (Index n) (prefixCuts ranks) ≫ C.matrixIso.hom) = h := by
    have eq : h ≫ (prod.lift (𝟙 L.X) (toBasePoint L.X ≫ C.point) ≫ A.onFlags) =
        toBasePoint ((testSpec k).obj (op S)) ≫ C.point := by
      have hh : h ≫ toBasePoint L.X = toBasePoint ((testSpec k).obj (op S)) :=
        morphismToBase _
      rw [← Category.assoc, prod.comp_lift, Category.comp_id, ← Category.assoc, hh, ← hzS]
      exact hfix
    exact ⟨C.stabilizer_pullback.lift _ _ eq, C.stabilizer_pullback.lift_fst _ _ eq⟩
  have htri := (C.full_upper_triangular (fun i _ ↦ ⟨i, rfl⟩) S h).mp hthrough
  have hmatrix : E.hom.app S h = matrixPoint j (e ≪≫ conjugateMatrixPoints m) S y := by
    have heS : E.hom.app S gS = (Specs.StandardGroups.generalLinearPoints k (Index n)).map a₀ m :=
      NatTrans.naturality_apply E.hom a₀ g₀
    have hyS : E.hom.app S yL = e.hom.app S (((groupPointsFunctor k).map j).app S y) := by
      have heq : (groupPointsFunctor k).map f ≫ E.hom =
          (groupPointsFunctor k).map j ≫ e.hom := by simp [f, hw]
      exact congrArg (fun v ↦ v.app S y) heq
    have hm : E.hom.app S h =
        (E.hom.app S gS)⁻¹ * E.hom.app S yL * E.hom.app S gS :=
      mapConjugation (E.hom.app S) gS yL
    rw [hm]
    rw [heS, hyS]
    rfl
  rw [← hmatrix]
  exact fun i j hij ↦ htri i j hij

end Flag

open private extendedPointsIso extendedPointsMap
  from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private baseChangeKernelSquare baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open private extendedSpecIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private smooth_of_smooth_after_fieldExtension isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private groupPresentation quotientRepresentsImage
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private schemeKernel_imageProjection from LinearAlgebraicGroups.Flag.NormalAffineQuotient
open Unipotent (baseChangedAlgebraicGroup)

private theorem connectedOfAlgClosure (G : AffineAlgebraicGroup k)
    (h : ConnectedSpace ((groupBaseChange k (AlgebraicClosure k)).obj G.val).X.left) :
    GeometricallyConnected G.val.X.hom := by
  let K := AlgebraicClosure k
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  let e₀ := (Grp.forget (SchemeOver k)).mapIso e
  let eK := extendedSpecIso K A ≪≫ (baseChange k K).mapIso e₀
  haveI : ConnectedSpace (PrimeSpectrum (K ⊗[k] A)) :=
    eK.hom.left.homeomorph.connectedSpace_iff.mpr h
  have hgeom := geometricallyConnectedSpecOfAlgClosure (k := k) (A := A)
  have hw : e₀.hom.left ≫ G.val.X.hom = Spec.map (CommRingCat.ofHom (algebraMap k A)) :=
    e₀.hom.w
  rw [← hw] at hgeom
  haveI : IsIso e₀.hom.left := (Over.forget _).map_isIso e₀.hom
  exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{u})
    e₀.hom.left G.val.X.hom).mp hgeom

private abbrev Geometry (X : SchemeOver k) := Smooth X.hom ∧ GeometricallyConnected X.hom

private theorem geometryOfIso {X Y : SchemeOver k} (e : X ≅ Y)
    (h : Geometry (X)) : Geometry (Y) := by
  obtain ⟨hs, hc⟩ := h
  change Smooth Y.hom ∧ GeometricallyConnected Y.hom
  have he := Over.w e.inv
  rw [← he]
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso (@Smooth.{u}) _ _).mpr hs,
    (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{u}) _ _).mpr hc⟩

private theorem rankOneGeometry (Q : AffineAlgebraicGroup k)
    (h : Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.additivePoints k) ∨
      Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.multiplicativePoints k)) :
    Geometry (Q.val.X) := by
  let K := AlgebraicClosure k
  let Q' := baseChangedAlgebraicGroup K Q
  have compare (G : AffineAlgebraicGroup K) (e : Q'.val ≅ G.val)
      [IsReduced G.val.X.left] [ConnectedSpace G.val.X.left] :
      Geometry (Q.val.X) := by
    let j : Q'.val.X.left ⟶ G.val.X.left := (underlyingFunctor K).map e.hom
    letI : IsIso j := (underlyingFunctor K).map_isIso e.hom
    letI : IsOpenImmersion j :=
      ((isIso_iff_isOpenImmersion_and_surjective j).mp (inferInstance : IsIso j)).1
    have : IsReduced Q'.val.X.left := isReduced_of_isOpenImmersion j
    letI := Q'.property.2.1
    have hs := smoothOfReducedOverPerfectField K Q'.val inferInstance
    have hc := j.homeomorph.connectedSpace_iff.mpr
      (inferInstance : ConnectedSpace G.val.X.left)
    exact ⟨smooth_of_smooth_after_fieldExtension Q.val.X.hom hs, connectedOfAlgClosure Q hc⟩
  rcases h with h | h
  · obtain ⟨e⟩ := h
    let A := StandardGroups.additiveGroup K
    haveI : IsReduced A.val.X.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (Polynomial K))))
    haveI : ConnectedSpace A.val.X.left := inferInstanceAs (ConnectedSpace (PrimeSpectrum (Polynomial K)))
    exact compare A <| isoOfPointIso Q' A
      (extendedPointsIso K Q.val ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) e ≪≫
        (StandardGroups.additiveGroupPointsIso K).symm)
  · obtain ⟨e⟩ := h
    let A := StandardGroups.multiplicativeGroup K
    haveI : IsReduced A.val.X.left :=
      inferInstanceAs (IsReduced (Spec (CommRingCat.of (LaurentPolynomial K))))
    haveI : ConnectedSpace A.val.X.left :=
      inferInstanceAs (ConnectedSpace (PrimeSpectrum (LaurentPolynomial K)))
    exact compare A <| isoOfPointIso Q' A
      (extendedPointsIso K Q.val ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) e ≪≫
        (StandardGroups.multiplicativeGroupPointsIso K).symm)

private theorem trivialGroupGeometry {G : GroupScheme k}
    (e : G ≅ Grp.trivial (SchemeOver k)) : Geometry (G.X) := by
  haveI : IsIso (Grp.trivial (SchemeOver k)).X.hom := by
    change IsIso (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  have hc : GeometricallyConnected (Grp.trivial (SchemeOver k)).X.hom := by
    constructor
    intro K _ y Z a b h
    haveI : IsIso b := h.isIso_snd_of_isIso
    exact b.homeomorph.connectedSpace_iff.mpr inferInstance
  exact geometryOfIso ((Grp.forget (SchemeOver k)).mapIso e.symm) ⟨inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of k)))), hc⟩

private theorem fppfQuotientOfRepresents {G Q : AffineAlgebraicGroup k}
    (N : ClosedSubgroup G.val) (q : G.val ⟶ Q.val)
    (hn : IsNormalSubgroup N.inclusion) (hq : RepresentsQuotient N q) :
    Unipotent.IsFppfGroupQuotient N q := by
  obtain ⟨L, f, P, p, i, _, hpN, hpi, _, l, hl⟩ := normalAffineQuotient G N hn
  obtain ⟨r, hr⟩ := hq
  let Y := (fppfOver k).uliftYoneda.{u + 1}
  let e : P.val.X ≅ Q.val.X := (fppfOver k).fullyFaithfulUliftYoneda.preimageIso (l.symm ≪≫ r)
  have he : p.hom.hom ≫ e.hom = q.hom.hom := by
    apply Y.map_injective
    rw [Y.map_comp]
    simp only [e, Y, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
    rw [← hl]
    simpa using hr
  have hunit : η[P.val.X] ≫ e.hom = η[Q.val.X] := by
    rw [← IsMonHom.one_hom p.hom.hom, Category.assoc, he, IsMonHom.one_hom q.hom.hom]
  have hk : IsSchemeKernel q N := hpN.of_iso (.refl _) (.refl _) (.refl _) e (by simp)
    (by simp) (by simpa using he) (by simpa using hunit)
  have he' : p.hom.hom.left ≫ e.hom.left = q.hom.hom.left :=
    congrArg (fun a : G.val.X ⟶ Q.val.X ↦ a.left) he
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have ⟨_, hf, hs, hfp, _, _⟩ := hpi
  refine ⟨hk, ?_, ?_, ?_, r, hr⟩
  · rw [← he']
    exact (MorphismProperty.cancel_right_of_respectsIso (@Flat.{u}) _ _).mpr hf
  · rw [← he']
    exact (MorphismProperty.cancel_right_of_respectsIso (@Surjective.{u}) _ _).mpr hs
  · rw [← he']
    exact (MorphismProperty.cancel_right_of_respectsIso (@LocallyOfFinitePresentation.{u}) _ _).mpr hfp

private theorem kernelPair {G Q : GroupScheme k}
    (N : ClosedSubgroup G) (q : G ⟶ Q) (hq : IsSchemeKernel q N) :
    IsPullback (prod.fst : G.X ⨯ N.group.X ⟶ G.X)
      (prod.fst * (prod.snd ≫ N.inclusion.hom.hom)) q.hom.hom q.hom.hom := by
  let δ : G.X ⨯ N.group.X ⟶ G.X := prod.fst * (prod.snd ≫ N.inclusion.hom.hom)
  have hw : prod.fst ≫ q.hom.hom = δ ≫ q.hom.hom := by
    simp [δ, MonObj.mul_comp, Category.assoc, hq.w, Hom.one_def]
  have hD (s : PullbackCone q.hom.hom q.hom.hom) :
      (s.fst⁻¹ * s.snd) ≫ q.hom.hom = 1 := by
    simp only [MonObj.mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel]
  let a (s : PullbackCone q.hom.hom q.hom.hom) := hq.lift (s.fst⁻¹ * s.snd) (toUnit _) (hD s)
  have ha (s : PullbackCone q.hom.hom q.hom.hom) :
      a s ≫ N.inclusion.hom.hom = s.fst⁻¹ * s.snd := hq.lift_fst _ _ _
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s ↦ prod.lift s.fst (a s)) (fun s ↦ prod.lift_fst _ _) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_))
  · change _ ≫ δ = _
    simp [δ, MonObj.comp_mul, ha, mul_inv_cancel_left]
  · apply prod.hom_ext
    · simpa using hm₁
    · rw [prod.lift_snd]
      have : m ≫ prod.snd ≫ N.inclusion.hom.hom = s.fst⁻¹ * s.snd := by
        have he : s.fst * (m ≫ prod.snd ≫ N.inclusion.hom.hom) = s.snd := by
          simpa only [δ, MonObj.comp_mul, hm₁, Category.assoc] using hm₂
        rw [← he, inv_mul_cancel_left]
      exact hq.hom_ext (this.trans (ha s).symm)
        ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)

private theorem geometryOfExtension {G Q : AffineAlgebraicGroup k}
    (N : ClosedSubgroup G.val) (q : G.val ⟶ Q.val)
    (hq : Unipotent.IsFppfGroupQuotient N q)
    (hN : Geometry (N.group.X)) (hQ : Geometry (Q.val.X)) :
    Geometry (G.val.X) := by
  have ⟨hk, hflat, hsurj, _, _⟩ := hq
  letI := G.property.1
  letI := Q.property.1
  letI := hflat
  letI := hsurj
  have hc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      q.hom.hom.left := ⟨⟨hsurj, hflat⟩, inferInstance⟩
  have hp := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.val.X N.group.X)
  have hpair := (kernelPair N q hk).map (Over.forget _)
  have hf : Smooth (prod.fst : G.val.X ⨯ N.group.X ⟶ G.val.X).left :=
    MorphismProperty.of_isPullback (P := @Smooth) hp.flip hN.1
  haveI : Smooth q.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) hpair hc hf
  have hgeom : GeometricallyConnected (prod.fst : G.val.X ⨯ N.group.X ⟶ G.val.X).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp.flip hN.2
  haveI : GeometricallyConnected (pullback.snd q.hom.hom.left q.hom.hom.left) := by
    let a := hpair.flip.isoPullback.hom
    have he : a ≫ pullback.snd q.hom.hom.left q.hom.hom.left =
        (prod.fst : G.val.X ⨯ N.group.X ⟶ G.val.X).left :=
      hpair.flip.isoPullback_hom_snd
    exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected.{u}) a _).mp
      (he.symm ▸ hgeom)
  haveI : GeometricallyConnected q.hom.hom.left :=
    geometricallyConnectedOfSurjectiveBaseChange q.hom.hom.left q.hom.hom.left
  letI := hQ.1
  letI := hQ.2
  change Smooth G.val.X.hom ∧ GeometricallyConnected G.val.X.hom
  rw [← Over.w q.hom.hom]
  exact ⟨smooth_comp _ _, GeometricallyConnected.comp _ _⟩

private theorem splitSolvableGeometry {G : GroupScheme k} (h : IsSplitSolvable G) :
    (IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom) →
      Geometry (G.X) := by
  induction h with
  | trivial e =>
    intro _
    exact trivialGroupGeometry e.some
  | @step H N hn h Q q hq hf ih =>
    intro hH
    let H' : AffineAlgebraicGroup k := ⟨H, hH⟩
    let N' := closedSubgroupAlgebraicGroup (G := H') N
    exact geometryOfExtension (G := H') (Q := Q) N q
      (fppfQuotientOfRepresents (G := H') (Q := Q) N q hn hq) (ih N'.property) (rankOneGeometry Q hf)


open private existsDiagonalMorphism diagonalImageIsSplit reducedImage normalOfSchemeKernel
  unipotentKernel liftToSchemeKernel extendedMatrixPointsIso extendedDiagonalPointsIso
  from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private splitBaseChange from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private reducedOfSmoothHopf noFiniteOrderOfConnectedSplit latticeEquivOfBasis
  from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open Specs.DiagonalizableGroups (groupAlgebra FGAbelianGroup)
open Specs.CharacterDescent (StandardLattice multiplicativeTypeSpecFunctor)

private theorem isSplitTorusOfCoordinates (D : AffineAlgebraicGroup k)
    (M : FGAbelianGroup.{u}) (e : specGroup (groupAlgebra k M.obj) ≅ D.val)
    (hs : Smooth D.val.X.hom) (hc : ConnectedSpace D.val.X.left) : IsSplitTorus D := by
  let A := groupAlgebra k M.obj
  letI := M.property
  let j := ((Grp.forget (SchemeOver k)).mapIso e).hom
  haveI : AlgebraicGeometry.Smooth (specGroup A).X.hom := by
    have hw : j.left ≫ D.val.X.hom = (specGroup A).X.hom := Over.w j
    rw [← hw]
    letI : IsIso j.left := (underlyingFunctor k).map_isIso e.hom
    exact @smooth_comp _ _ j.left _ D.val.X.hom inferInstance hs
  haveI : _root_.IsReduced (MonoidAlgebra k M.obj) := reducedOfSmoothHopf A inferInstance
  haveI : ConnectedSpace (PrimeSpectrum (MonoidAlgebra k M.obj)) :=
    j.left.homeomorph.connectedSpace_iff.mpr hc
  haveI : Module.Finite ℤ (Additive M.obj) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  haveI : Module.IsTorsionFree ℤ (Additive M.obj) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a m hm
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    have hd : (orderOf m.toMul : ℤ) ∣ a := orderOf_dvd_iff_zpow_eq_one.mpr hm
    by_cases hn : 0 < orderOf m.toMul
    · exact noFiniteOrderOfConnectedSplit (k := k) m.toMul hn
    · exact (ha (by simpa [Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hn)] using hd)).elim
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Additive M.obj)
  let v := CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k (latticeEquivOfBasis b))
  let e' : specGroup A ≅ specGroup (groupAlgebra k (StandardLattice.{u} r)) :=
    (hopfSpec (CommRingCat.of k)).mapIso v.symm.op
  obtain ⟨l⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨(groupPointsFunctor k).mapIso (e.symm ≪≫ e' ≪≫ l) ≪≫
    StandardGroups.multiplicativePowerGroupPointsIso k (Index r)⟩⟩

private theorem diagonalGeometry {n : ℕ} {G H T : AffineAlgebraicGroup k}
    (j : G.val ⟶ H.val)
    (e : (groupPointsFunctor k).obj H.val ≅ Specs.StandardGroups.generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} n))
    (hj : IsClosedImmersion j.hom.hom.left) (htri : IsUpperTriangular j e)
    (hg : Geometry (G.val.X)) :
    ∃ (d : G.val ⟶ T.val) (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val)
      (i : D.val ⟶ T.val) (U : ClosedSubgroup G.val), HasDiagonalRadical j e t d D p i U := by
  obtain ⟨d, hd⟩ := existsDiagonalMorphism G H T j e t htri
  obtain ⟨D, p, i, U, hpi, hcan, hU, hrep⟩ := schemeImageQuotient G T d
  have ⟨hcomp, hpf, hps, hpfp, _, hic⟩ := hpi
  have hpU : IsSchemeKernel p U := schemeKernel_imageProjection hcomp hic hU
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  let H' := baseChangedAlgebraicGroup K H
  let T' := baseChangedAlgebraicGroup K T
  let D' := baseChangedAlgebraicGroup K D
  let U' := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup U)
  have hj' : IsClosedImmersion (F.map j).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) j.hom.hom).flip hj
  have hUc' : IsClosedImmersion (F.map U.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) U.inclusion.hom.hom).flip
      U.isClosedImmersion
  let W : ClosedSubgroup G'.val := ⟨U'.val, F.map U.inclusion, hUc'⟩
  let e' := extendedMatrixPointsIso K H.val e
  let t' := extendedDiagonalPointsIso K T.val t
  have entry {J : AffineAlgebraicGroup k} (a : G.val ⟶ J.val)
      {Q : TestAlgebra k ⥤ GrpCat.{u}} (v : (groupPointsFunctor k).obj J.val ≅ Q)
      (R : TestAlgebra K) (x : Points G'.val.X R) :
      ((extendedPointsIso K J.val ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) v).hom.app R)
        (((groupPointsFunctor K).map (F.map a)).app R x) =
      v.hom.app ((restrictTestAlgebra k K).obj R)
        (((groupPointsFunctor k).map a).app _ ((extendedPointsIso K G.val).hom.app R x)) := by
    exact congrArg (v.hom.app ((restrictTestAlgebra k K).obj R))
      (congrArg (fun τ ↦ τ.app R x) (extendedPointsMap K a))
  have htri' : IsUpperTriangular (F.map j) e' := by
    intro R x
    rw [show matrixPoint (F.map j) e' R x = _ from entry j e R x]
    exact htri _ _
  have hd' : IsDiagonalMorphism (F.map j) e' t' (F.map d) := by
    intro R x l
    change (((t'.hom.app R (((groupPointsFunctor K).map (F.map d)).app R x) l : Rˣ) : R)) =
      (matrixPoint (F.map j) e' R x).val l l
    rw [show t'.hom.app R (((groupPointsFunctor K).map (F.map d)).app R x) = _ from entry d t R x,
      show matrixPoint (F.map j) e' R x = _ from entry j e R x]
    exact hd _ _ _
  letI := hg.1
  have hsG' : Smooth G'.val.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  have hcG' : ConnectedSpace G'.val.X.left :=
    hg.2.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  obtain ⟨d', hdiag', DD, pp, ii, UU, _, _, hUU, _, hsUU, hcUU, _, _, _⟩ :=
    SmoothDiagonalKernel.smoothDiagonalKernel n G' H' T' (F.map j) e' t' hj' htri' hsG' hcG'
  have eqD : F.map d = d' := by
    apply (groupHomEquiv G'.val T'.val G'.property.1).injective
    apply NatTrans.ext
    funext R
    apply GrpCat.ext
    intro x
    apply (ConcreteCategory.bijective_of_isIso (t'.hom.app R)).injective
    funext l
    apply Units.ext
    exact (hd' R x l).trans (hdiag' R x l).symm
  have hW : IsSchemeKernel d' W := by
    rw [← eqD]
    exact baseChangeKernelSquare d U.inclusion hU
  let eU := hW.isoPullback ≪≫ hUU.isoPullback.symm
  have hsW : Smooth W.group.X.hom := by
    rw [← Over.w eU.hom]
    letI := hsUU
    exact smooth_comp _ _
  have hsU : Smooth U.group.X.hom := smooth_of_smooth_after_fieldExtension U.group.X.hom hsW
  have hcU : GeometricallyConnected U.group.X.hom :=
    connectedOfAlgClosure (closedSubgroupAlgebraicGroup U)
      (eU.hom.left.homeomorph.connectedSpace_iff.mpr hcUU)
  have hpb := (baseChangeMapPullback (K := K) p.hom.hom).flip
  have hpf' : Flat (F.map p).hom.hom.left := MorphismProperty.of_isPullback hpb hpf
  have hps' : Surjective (F.map p).hom.hom.left := MorphismProperty.of_isPullback hpb hps
  letI := hsG'
  letI := D'.property.2.1
  have hsD' : Smooth D'.val.X.hom :=
    smoothOfReducedOverPerfectField K D'.val
      (reducedImage (G := G') (D := D') (F.map p)
        (isReduced_of_smooth_over_field G'.val.X.hom) hpf' hps')
  have hsD : Smooth D.val.X.hom := smooth_of_smooth_after_fieldExtension D.val.X.hom hsD'
  have hcD : ConnectedSpace D.val.X.left := by
    letI := hg.2
    letI : ConnectedSpace G.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
    exact hps.1.connectedSpace p.hom.hom.left.continuous
  obtain ⟨M, ⟨eM⟩⟩ := diagonalImageIsSplit D T i hic t
  have hM : (multiplicativeTypeSpecFunctor k).essImage D := by
    let A := groupAlgebra k M.obj
    letI := M.property
    have hmt : Specs.CharacterDescent.IsMultiplicativeType A :=
      ⟨k, inferInstance, inferInstance, inferInstance,
        splitBaseChange (K := k) A ⟨M, ⟨Iso.refl _⟩⟩⟩
    exact ⟨op ⟨⟨A, inferInstance⟩, hmt⟩,
      ⟨(fullyFaithfulInducedFunctor Subtype.val).preimageIso eM⟩⟩
  refine ⟨d, D, p, i, U, hd, hpi, hcan, hU, ⟨hpU, hpf, hps, hpfp, hrep⟩,
    isSplitTorusOfCoordinates D M eM hsD hcD, hsU, hcU, normalOfSchemeKernel hU,
    unipotentKernel j e t hj htri hd hU, ?_⟩
  intro V hV
  exact liftToSchemeKernel hpU V.inclusion
    (Unipotent.homFromUnipotentToMultiplicativeType (closedSubgroupAlgebraicGroup V) D
      (V.inclusion ≫ p) hV hM)


open Unipotent (ClosedSeries IsFppfGroupQuotient IsSplitUnipotent)
open Specs.DiagonalizableGroups (IntegerCharacters)
open scoped Polynomial

private theorem multiplicativeTypeOfMultiplicativePoints (Q : AffineAlgebraicGroup k)
    (hq : Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.multiplicativePoints k)) :
    (multiplicativeTypeSpecFunctor k).essImage Q := by
  obtain ⟨e⟩ := DiagonalizableGroups.diagonalInteger k Q hq
  let A := groupAlgebra k IntegerCharacters.{u}
  haveI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := (MulEquiv.ulift.symm :
      Multiplicative ℤ ≃* IntegerCharacters.{u}).toMonoidHom) MulEquiv.ulift.symm.surjective
  have hA : Specs.CharacterDescent.IsMultiplicativeType A :=
    ⟨k, inferInstance, inferInstance, inferInstance, splitBaseChange (K := k) A
      ⟨⟨CommGrpCat.of IntegerCharacters.{u}, inferInstance⟩, ⟨Iso.refl _⟩⟩⟩
  exact ⟨op ⟨⟨A, inferInstance⟩, hA⟩,
    ⟨(fullyFaithfulInducedFunctor Subtype.val).preimageIso e⟩⟩

private theorem imageOfTrivialHom {G I Q : AffineAlgebraicGroup k} {f : G.val ⟶ Q.val}
    {p : G.val ⟶ I.val} {i : I.val ⟶ Q.val}
    (h : IsImageFactorization f p i) (hf : f = 0) :
    Nonempty (I.val ≅ Grp.trivial (SchemeOver k)) := by
  letI := h.2.1
  letI := h.2.2.1
  letI := h.2.2.2.2.2
  letI : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  letI : Epi p.hom.hom := Over.epi_of_epi_left _
  letI : Epi p := (Grp.forget (SchemeOver k)).epi_of_epi_map
    (inferInstanceAs (Epi p.hom.hom))
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  letI : Mono i := (Grp.forget (SchemeOver k)).mono_of_mono_map
    (inferInstanceAs (Mono i.hom.hom))
  have hi : i = 0 := (cancel_epi p).mp (by simp [h.1, hf])
  have hid : 𝟙 I.val = 0 := (cancel_mono i).mp (by rw [hi]; simp)
  exact ⟨((IsZero.iff_id_eq_zero _).mpr hid).iso (Grp.isZero_trivial _)⟩

private theorem imageCoordinatesReducedConnected {G I : AffineAlgebraicGroup k}
    (p : G.val ⟶ I.val) (hp : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left)
    (hG : Geometry G.val.X) :
    AlgebraicGeometry.IsReduced I.val.X.left ∧ ConnectedSpace I.val.X.left := by
  letI := hG.1
  letI := hG.2
  letI : ConnectedSpace G.val.X.left := GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  exact ⟨reducedImage p (isReduced_of_smooth_over_field G.val.X.hom) hp hs,
    hs.1.connectedSpace p.hom.hom.left.continuous⟩

private theorem algebraMapSurjectiveOfProperPolynomialQuotient {A : Type u} [CommRing A] [Algebra k A] [IsReduced A]
    [ConnectedSpace (PrimeSpectrum A)] (p : A →ₐ[k] k) (a : k[X] →ₐ[k] A)
    (hsurj : Function.Surjective a) (h : ¬ Function.Injective a) :
    Function.Surjective (algebraMap k A) := by
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp h
  have hnon : x - y ≠ 0 := sub_ne_zero.mpr hne
  let f : Polynomial k := (x - y) * Polynomial.C (x - y).leadingCoeff⁻¹
  have hmonic : f.Monic := Polynomial.monic_mul_leadingCoeff_inv hnon
  have hf : a f = 0 := by simp [f, hxy]
  let q : (Polynomial k ⧸ Ideal.span {f}) →ₐ[k] A :=
    Ideal.Quotient.liftₐ _ a
      (by
        intro x hx
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hx
        simp [hf])
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := hsurj z
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  haveI : Module.Finite k (Polynomial k ⧸ Ideal.span {f}) := hmonic.finite_quotient
  haveI : Module.Finite k A := Module.Finite.of_surjective q.toLinearMap hq
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  letI : Subsingleton (PrimeSpectrum A) := subsingleton_of_preconnected_totallyDisconnected
  haveI : Nontrivial A := p.toRingHom.domain_nontrivial
  haveI : IsLocalRing A := by
    let m := (Ideal.exists_maximal A).choose
    letI : m.IsMaximal := (Ideal.exists_maximal A).choose_spec
    refine IsLocalRing.of_unique_max_ideal ⟨m, inferInstance, fun j hj ↦ ?_⟩
    exact congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (⟨j, hj.isPrime⟩ : PrimeSpectrum A) ⟨m, inferInstance⟩)
  letI : Field A := (IsArtinianRing.isField_of_isReduced_of_isLocalRing A).toField
  have hinj : Function.Injective p := p.injective
  intro x
  exact ⟨p x, hinj (AlgHom.commutes _ _)⟩

private theorem additiveClosedSubgroup (I Q : AffineAlgebraicGroup k) (i : I.val ⟶ Q.val)
    (hi : IsClosedImmersion i.hom.hom.left)
    (hq : Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.additivePoints k))
    (hred : AlgebraicGeometry.IsReduced I.val.X.left) (hc : ConnectedSpace I.val.X.left) :
    Nonempty (I.val ≅ Grp.trivial (SchemeOver k)) ∨
      Nonempty ((groupPointsFunctor k).obj I.val ≅ Specs.StandardGroups.additivePoints k) := by
  letI := StandardGroups.additiveHopf k
  let B := CommHopfAlgCat.of k (Polynomial k)
  let Q' := StandardGroups.additiveGroup k
  let l := isoOfPointIso Q Q' (hq.some ≪≫ (StandardGroups.additiveGroupPointsIso k).symm)
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation I
  let F := hopfSpec (CommRingCat.of k)
  let a : B ⟶ A := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (e.hom ≫ i ≫ l.hom)).unop
  have ha : specGroupMap a = e.hom ≫ i ≫ l.hom :=
    (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hclosed : IsClosedImmersion (specGroupMap a).hom.hom.left := by
    rw [ha]
    letI := hi
    letI : IsIso e.hom.hom.hom.left := (underlyingFunctor k).map_isIso e.hom
    letI : IsIso l.hom.hom.hom.left := (underlyingFunctor k).map_isIso l.hom
    haveI : IsClosedImmersion (i ≫ l.hom).hom.hom.left :=
      IsClosedImmersion.comp i.hom.hom.left l.hom.hom.hom.left
    exact IsClosedImmersion.comp e.hom.hom.hom.left (i ≫ l.hom).hom.hom.left
  have hsurj := (hopfMapClosedImmersion k a).mp hclosed
  by_cases h : Function.Injective a.hom
  · let ae := AlgEquiv.ofBijective a.hom.toAlgHom ⟨h, hsurj⟩
    letI : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr ⟨h, hsurj⟩
    let j : specGroup A ≅ Q'.val := F.mapIso (asIso a).op
    exact Or.inr ⟨(groupPointsFunctor k).mapIso (e.symm ≪≫ j) ≪≫
      StandardGroups.additiveGroupPointsIso k⟩
  · let j := ((Grp.forget (SchemeOver k)).mapIso e).hom.left
    letI : IsIso j := (underlyingFunctor k).map_isIso e.hom
    have hj : IsOpenImmersion j := ((isIso_iff_isOpenImmersion_and_surjective j).mp
      (inferInstance : IsIso j)).1
    have hAred : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of A)) :=
      @isReduced_of_isOpenImmersion _ _ j hj hred
    letI : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).mp hAred
    letI : ConnectedSpace (PrimeSpectrum A) := j.homeomorph.connectedSpace_iff.mpr hc
    have hground := algebraMapSurjectiveOfProperPolynomialQuotient
      (Bialgebra.counitAlgHom k A) a.hom.toAlgHom hsurj h
    let u : specGroup A ⟶ Grp.trivial (SchemeOver k) := 0
    letI : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
    have hu : IsIso u.hom.hom.left := by
      change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      haveI : IsIso (CommRingCat.ofHom (algebraMap k A)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(algebraMap k A).injective, hground⟩
      infer_instance
    let F := Over.forget (Spec (CommRingCat.of k))
    letI : IsIso (F.map u.hom.hom) := hu
    letI : IsIso u.hom.hom := isIso_of_reflects_iso u.hom.hom F
    let e₀ := Grp.mkIso (asIso u.hom.hom) (IsMonHom.one_hom u.hom.hom)
      (IsMonHom.mul_hom u.hom.hom)
    exact Or.inl ⟨e.symm ≪≫ e₀⟩

private theorem restrictDiagonal {n : ℕ} {G H T : AffineAlgebraicGroup k}
    {j : G.val ⟶ H.val}
    {e : (groupPointsFunctor k).obj H.val ≅ Specs.StandardGroups.generalLinearPoints k (Index.{u} n)}
    {t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} n)}
    {d : G.val ⟶ T.val} (hd : IsDiagonalMorphism j e t d) (N : ClosedSubgroup G.val)
    {dN : N.group ⟶ T.val}
    (hdN : IsDiagonalMorphism (N.inclusion ≫ j) e t dN) :
    dN = N.inclusion ≫ d := by
  let N' := closedSubgroupAlgebraicGroup N
  apply (groupHomEquiv N.group T.val N'.property.1).injective
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  apply (ConcreteCategory.bijective_of_isIso (t.hom.app R)).injective
  funext i
  apply Units.ext
  change (((t.hom.app R) (((groupPointsFunctor k).map dN).app R x) i : Rˣ) : R) =
      (((t.hom.app R) (((groupPointsFunctor k).map (N.inclusion ≫ d)).app R x) i : Rˣ) : R)
  exact (hdN R x i).trans (hd R (((groupPointsFunctor k).map N.inclusion).app R x) i).symm

private theorem restrictedKernel {G Q T : AffineAlgebraicGroup k}
    (d : G.val ⟶ T.val) (q : G.val ⟶ Q.val) (N U : ClosedSubgroup G.val)
    (W : ClosedSubgroup N.group)
    (hq : IsSchemeKernel q N) (hu : IsSchemeKernel d U)
    (hw : IsSchemeKernel (N.inclusion ≫ d) W) :
    ∃ (v : W.group ⟶ U.group) (hv : IsClosedImmersion v.hom.hom.left),
      IsSchemeKernel (U.inclusion ≫ q) (⟨W.group, v, hv⟩ : ClosedSubgroup U.group) := by
  have hkill : (W.inclusion ≫ N.inclusion) ≫ d = 0 := by
    apply Grp.hom_ext
    rw [Category.assoc]
    exact hw.w
  obtain ⟨v, eq⟩ := liftToSchemeKernel hu (W.inclusion ≫ N.inclusion) hkill
  have eq' : v.hom.hom ≫ U.inclusion.hom.hom = W.inclusion.hom.hom ≫ N.inclusion.hom.hom :=
    congrArg (fun f ↦ f.hom.hom) eq
  have hv : IsClosedImmersion v.hom.hom.left := by
    letI := U.isClosedImmersion
    letI := N.isClosedImmersion
    letI := W.isClosedImmersion
    haveI : IsClosedImmersion (v.hom.hom.left ≫ U.inclusion.hom.hom.left) := by
      rw [← Over.comp_left, eq', Over.comp_left]
      infer_instance
    exact IsClosedImmersion.of_comp _ U.inclusion.hom.hom.left
  refine ⟨v, hv, ?_⟩
  have hw' : IsPullback W.inclusion.hom.hom (v.hom.hom ≫ toUnit U.group.X)
      (N.inclusion.hom.hom ≫ d.hom.hom) η[T.val.X] := by
    rw [comp_toUnit]
    exact hw
  have hI := hw'.of_bot eq'.symm hu
  have hJ := hI.flip.paste_vert hq
  change IsPullback v.hom.hom (toUnit W.group.X) (U.inclusion.hom.hom ≫ q.hom.hom) η[Q.val.X]
  simpa only [comp_toUnit] using hJ

private theorem prependSplitSeries {G : AffineAlgebraicGroup k} (N : ClosedSubgroup G.val)
    {Q : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val)
    (hq : IsFppfGroupQuotient N q)
    (hf : Nonempty (Q.val ≅ Grp.trivial (SchemeOver k)) ∨
      Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.additivePoints k))
    (hG : IsUnipotent G) (hN : IsSplitUnipotent (closedSubgroupAlgebraicGroup N)) :
    IsSplitUnipotent G := by
  obtain ⟨_, n, S, hS⟩ := hN
  let E : ClosedSeries G (n + 1) :=
    { term := fun i ↦ Nat.casesOn i G S.term
      top := Iso.refl _
      bottom := S.bottom
      step := fun i ↦ match i with
        | 0 => S.top.hom ≫ N.inclusion
        | j + 1 => S.step j
      closed := by
        intro i
        cases i with
        | zero =>
          change IsClosedImmersion (S.top.hom.hom.hom.left ≫ N.inclusion.hom.hom.left)
          letI : IsIso S.top.hom.hom.hom.left := (underlyingFunctor k).map_isIso S.top.hom
          exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance N.isClosedImmersion
        | succ j => exact S.closed j }
  refine ⟨hG, n + 1, E, ?_⟩
  intro i hi
  cases i with
  | zero =>
    let N₀ : ClosedSubgroup G.val := ⟨(E.term 1).val, E.step 0, E.closed 0⟩
    have hker : IsSchemeKernel q N₀ := by
      apply hq.1.of_iso' ((Grp.forget (SchemeOver k)).mapIso S.top)
        (.refl _) (.refl _) (.refl _)
      · rfl
      · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
      · simp
      · simp
    obtain ⟨_, hqf, hqs, hqfp, _⟩ := hq
    letI := G.property.1
    letI := Q.property.1
    have hi : IsImageFactorization q q (𝟙 Q.val) :=
      ⟨Category.comp_id _, hqf, hqs, hqfp, isAffineHom_of_isAffine _,
        inferInstanceAs (IsClosedImmersion (𝟙 Q.val.X.left))⟩
    exact ⟨Q, q, ⟨hker, hqf, hqs, hqfp, quotientRepresentsImage hi hker⟩, hf⟩
  | succ j => exact hS j (Nat.lt_of_succ_lt_succ hi)

private theorem subgroupOfTrivial {G : GroupScheme k} (U : ClosedSubgroup G)
    (e : G ≅ Grp.trivial (SchemeOver k)) :
    Nonempty (U.group ≅ Grp.trivial (SchemeOver k)) := by
  have he : IsZero G := (Grp.isZero_trivial _).of_iso e
  letI := U.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono U.inclusion := (Grp.forget (SchemeOver k)).mono_of_mono_map
    (inferInstanceAs (Mono U.inclusion.hom.hom))
  have hu : 𝟙 U.group = 0 := (cancel_mono U.inclusion).mp (he.eq_of_tgt _ _)
  exact ⟨((IsZero.iff_id_eq_zero _).mpr hu).iso (Grp.isZero_trivial _)⟩

private theorem splitDiagonalKernel {G : GroupScheme k} (hs : IsSplitSolvable G) :
    ∀ (hG : IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom)
      {n : ℕ} {H T : AffineAlgebraicGroup k} (j : G ⟶ H.val)
      (e : (groupPointsFunctor k).obj H.val ≅ Specs.StandardGroups.generalLinearPoints k (Index.{u} n))
      (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} n))
      (d : G ⟶ T.val) (U : ClosedSubgroup G),
      IsClosedImmersion j.hom.hom.left → IsUpperTriangular j e → IsDiagonalMorphism j e t d →
      IsSchemeKernel d U → Geometry U.group.X → IsSplitUnipotent (closedSubgroupAlgebraicGroup (G := ⟨G, hG⟩) U) := by
  induction hs with
  | trivial iso =>
    intro hG n H T j e t d U hj ht hd hU hUg
    let G' : AffineAlgebraicGroup k := ⟨_, hG⟩
    let U' := closedSubgroupAlgebraicGroup (G := G') U
    let S : ClosedSeries U' 0 :=
      { term := fun _ ↦ U'
        top := Iso.refl _
        bottom := (subgroupOfTrivial U iso.some).some
        step := fun _ ↦ 𝟙 _
        closed := fun _ ↦ inferInstanceAs (IsClosedImmersion (𝟙 U'.val.X.left)) }
    exact ⟨unipotentKernel (G := G') j e t hj ht hd hU, 0, S,
      fun i hi ↦ (Nat.not_lt_zero i hi).elim⟩
  | @step G N hn hN Q q hq hf ih =>
    intro hG n H T j e t d U hj ht hd hU hUg
    let G' : AffineAlgebraicGroup k := ⟨G, hG⟩
    let N' := closedSubgroupAlgebraicGroup (G := G') N
    let U' := closedSubgroupAlgebraicGroup (G := G') U
    have hjN : IsClosedImmersion (N.inclusion ≫ j).hom.hom.left := by
      letI := N.isClosedImmersion
      letI := hj
      exact IsClosedImmersion.comp N.inclusion.hom.hom.left j.hom.hom.left
    have htN : IsUpperTriangular (N.inclusion ≫ j) e := fun R x ↦
      ht R (((groupPointsFunctor k).map N.inclusion).app R x)
    obtain ⟨dN, DN, pN, iN, W, hW⟩ :=
      diagonalGeometry (G := N') (N.inclusion ≫ j) e t hjN htN
        (splitSolvableGeometry hN N'.property)
    have hDN := hW.1
    have hWN : IsSchemeKernel dN W := hW.2.2.2.1
    have hWg : Geometry W.group.X := ⟨hW.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.1⟩
    have hsplit := ih N'.property (N.inclusion ≫ j) e t dN W hjN htN hDN hWN hWg
    have hqN := (fppfQuotientOfRepresents (G := G') N q hn hq).1
    have hWrestricted : IsSchemeKernel (N.inclusion ≫ d) W := by
      rw [← restrictDiagonal (G := G') (H := H) (T := T) hd N hDN]
      exact hWN
    obtain ⟨v, hv, hVU⟩ := restrictedKernel (G := G') (Q := Q) (T := T)
      d q N U W hqN hU hWrestricted
    let V : ClosedSubgroup U'.val := ⟨W.group, v, hv⟩
    have hUun := unipotentKernel (G := G') j e t hj ht hd hU
    obtain ⟨I, p, i, hpi, _, _⟩ := schemeImageFactorization U' Q (U.inclusion ≫ q)
    have hpV := schemeKernel_imageProjection hpi.1 hpi.2.2.2.2.2 hVU
    have hquot : IsFppfGroupQuotient V p :=
      ⟨hpV, hpi.2.1, hpi.2.2.1, hpi.2.2.2.1, quotientRepresentsImage hpi hVU⟩
    apply prependSplitSeries V p hquot _ hUun hsplit
    rcases hf with ha | hm
    · obtain ⟨hred, hconn⟩ := imageCoordinatesReducedConnected p hpi.2.1 hpi.2.2.1 hUg
      exact additiveClosedSubgroup I Q i hpi.2.2.2.2.2 ha hred hconn
    · exact Or.inl (imageOfTrivialHom hpi
        (Unipotent.homFromUnipotentToMultiplicativeType U' Q (U.inclusion ≫ q)
          hUun (multiplicativeTypeOfMultiplicativePoints Q hm)))

/-- The split solvable series restricts to a split unipotent series in the diagonal
kernel. The same kernel contains every unipotent closed subgroup scheme. -/
theorem splitKernelOfTriangularization : SplitKernelOfTriangularization.{u} := by
  intro k _ n G H T j e t hsplit hj ht
  obtain ⟨d, D, p, i, U, hU⟩ := diagonalGeometry j e t hj ht
    (splitSolvableGeometry hsplit G.property)
  exact ⟨d, D, p, i, U, hU, splitDiagonalKernel hsplit G.property j e t d U hj ht
    hU.1 hU.2.2.2.1 ⟨hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.1⟩⟩


end
end LinearAlgebraicGroups.SplitSolvableRadical
