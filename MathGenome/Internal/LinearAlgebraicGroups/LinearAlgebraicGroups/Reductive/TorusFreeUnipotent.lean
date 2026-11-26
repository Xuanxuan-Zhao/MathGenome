import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ChevalleyLine
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Orthogonality
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.TorusFreeUnipotent

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricBorelConjugacy (IsBorel IsSmoothConnectedSolvable subgroupOfSubgroup)
open Specs.GeometricRadicals (IsMaximalTorus IsTorus IsTrivialSubgroup)
open Specs.SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open Specs.Unipotent (IsFppfGroupQuotient IsUnipotent closedSubgroupAlgebraicGroup)
open private factor_closed isIso_of_schemeIso solvable_iff_sections rationalSections rationalMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private exists_borel_above subgroupOf_trans torus_smooth_connected_solvable split_solvable_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private inclusion_mono isTorus_iff_coordinates torus_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private centralizes_iff conjugateLe_iff mono_over
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isMonHom_of_comp_closed schemeKernel_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

open private coordinateLine_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ChevalleyLine
open private pointMatrix pointMatrix_evaluation pointMatrix_isCoactionMatrix
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private weight_of_column_isGroupLike from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
open private groupLike_eq_one_of_invariants from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Orthogonality
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private torus_of_split torus_multiplicativeType
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private extension_smooth_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private isIso_of_trivial_kernel represented_quotient_of_kernel
  affine_quotient_smooth_connected central_normal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private unipotent_iff_exists_embedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations
open private onPoints_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private unitriangular_split_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.Triangularization
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private closed_flag_quotient_proper descends from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper

noncomputable section

set_option maxHeartbeats 2500000
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem centralizer_le_borel [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (T C : ClosedSubgroup G.val) (hT : Specs.GeometricRadicals.IsMaximalTorus T)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes T.inclusion g))
    (hCsol : IsSmoothConnectedSolvable C) (hTC : IsSubgroupOf T C)
    (B : ClosedSubgroup G.val) (hB : IsBorel B) (hTB : IsSubgroupOf T B) :
    IsSubgroupOf C B := by
  obtain ⟨B₀, hB₀, j, hj⟩ := exists_borel_above G C hCsol
  obtain ⟨g, hng, e, he⟩ := MaximalToriConjugate.normalizerTransitiveOnBorels G hs hc
    T hT B B₀ hB hB₀ hTB (subgroupOf_trans hTC ⟨j, hj⟩)
  let c : C.group.X ⟶ G.val.X := C.inclusion.hom.hom
  let gC : C.group.X ⟶ G.val.X := toUnit C.group.X ≫ g
  have hgC : Centralizes T.inclusion (gC * c * gC⁻¹) := by
    rw [centralizes_iff]
    intro U a t
    have hnorm := (normalizesIff k T.inclusion T.isClosedImmersion _ g).mp hng
    obtain ⟨t', ht'⟩ := (conjugateLe_iff _ _).mp hnorm.2 U (toUnit U) t
    have hcomm := (centralizes_iff _ _).mp ((hC _ c).mpr ⟨𝟙 _, Category.id_comp _⟩) U a t'
    have hg : a ≫ gC = toUnit U ≫ g := by simp [gC, ← Category.assoc]
    rw [ht', GrpObj.comp_inv, inv_inv] at hcomm
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hg]
    unfold Commute SemiconjBy at hcomm ⊢
    calc
      (toUnit U ≫ g) * (a ≫ c) * (toUnit U ≫ g)⁻¹ * (t ≫ T.inclusion.hom.hom) =
          (toUnit U ≫ g) * ((a ≫ c) *
            ((toUnit U ≫ g)⁻¹ * (t ≫ T.inclusion.hom.hom) * (toUnit U ≫ g))) *
            (toUnit U ≫ g)⁻¹ := by group
      _ = (toUnit U ≫ g) * (((toUnit U ≫ g)⁻¹ * (t ≫ T.inclusion.hom.hom) *
            (toUnit U ≫ g)) * (a ≫ c)) * (toUnit U ≫ g)⁻¹ := by rw [hcomm]
      _ = (t ≫ T.inclusion.hom.hom) *
          ((toUnit U ≫ g) * (a ≫ c) * (toUnit U ≫ g)⁻¹) := by group
  obtain ⟨l, hl⟩ := (hC _ _).mp hgC
  let m : C.group.X ⟶ B.group.X := l ≫ j.hom.hom ≫ e.inv.hom.hom
  have hcomp : m ≫ B.inclusion.hom.hom = c := by
    have he' : m ≫ (e.hom ≫ B₀.inclusion).hom.hom =
        gC * (m ≫ B.inclusion.hom.hom) * gC⁻¹ := by
      rw [he, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
      rw [← Category.assoc m, comp_toUnit]
    have he'' : m ≫ (e.hom ≫ B₀.inclusion).hom.hom = gC * c * gC⁻¹ := by
      change (l ≫ j.hom.hom ≫ e.inv.hom.hom) ≫ e.hom.hom.hom ≫
        B₀.inclusion.hom.hom = _
      have hInv : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
        (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
      simp only [Category.assoc]
      rw [← Category.assoc e.inv.hom.hom, hInv, Category.id_comp]
      rw [show j.hom.hom ≫ B₀.inclusion.hom.hom = c from
        congrArg (fun f : C.group ⟶ G.val ↦ f.hom.hom) hj, hl]
    exact mul_left_cancel (mul_right_cancel (he'.symm.trans he''))
  have := B.isClosedImmersion
  have hm := isMonHom_of_comp_closed m C.inclusion B.inclusion hcomp
  exact ⟨Grp.homMk m, Grp.hom_ext _ _ hcomp⟩

private theorem unipotent_iso {F H : AffineAlgebraicGroup k}
    (e : F.val ≅ H.val) (h : Specs.Unipotent.IsUnipotent F) :
    Specs.Unipotent.IsUnipotent H := by
  obtain ⟨A, ⟨d⟩, hA⟩ := h
  exact ⟨A, ⟨d ≪≫ e⟩, hA⟩

private theorem one_isIso_of_trivial {D : GroupScheme k}
    (h : Nonempty (D ≅ Grp.trivial (SchemeOver k))) : IsIso (η[D.X]) := by
  obtain ⟨e⟩ := h
  let d := (Grp.forget (SchemeOver k)).mapIso e.symm
  have hd : d.hom = η[D.X] := by
    have h := IsMonHom.one_hom e.inv.hom.hom
    change 𝟙 _ ≫ d.hom = η[D.X] at h
    simpa only [Category.id_comp] using h
  rw [← hd]
  infer_instance

private theorem solvable_torus_free_unipotent [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom)
    (hc : ConnectedSpace G.val.X.left) (hsol : Specs.SchemeDerivedGroup.IsSolvable G.val)
    (hfree : ∀ T : ClosedSubgroup G.val, Specs.GeometricRadicals.IsTorus T.group →
      Specs.GeometricRadicals.IsTrivialSubgroup T) : Specs.Unipotent.IsUnipotent G := by
  obtain ⟨U, D, p, hU, hp, _, ⟨T, hT⟩, h⟩ :=
    GeometricTorusSplitting.splitting G hs hc hsol
  letI : IsIso (T.inclusion ≫ p) := (h T).1.mp hT
  have hD : Nonempty (D.val ≅ Grp.trivial (SchemeOver k)) := by
    obtain ⟨d⟩ := hfree T ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mpr hT.1)
    exact ⟨(asIso (T.inclusion ≫ p)).symm ≪≫ d⟩
  letI := one_isIso_of_trivial hD
  haveI : IsIso U.inclusion.hom.hom :=
    hp.1.isIso_fst_of_isIso
  haveI : IsIso U.inclusion.hom.hom.left := (Over.forget _).map_isIso U.inclusion.hom.hom
  haveI : IsIso U.inclusion := isIso_of_schemeIso U.inclusion
  exact unipotent_iso (asIso U.inclusion) hU.2.2.2.1

private theorem borel_unipotent_of_torus_free [IsAlgClosed k]
    (G : AffineAlgebraicGroup k)
    (hfree : ∀ T : ClosedSubgroup G.val, Specs.GeometricRadicals.IsTorus T.group →
      Specs.GeometricRadicals.IsTrivialSubgroup T)
    (B : ClosedSubgroup G.val) (hB : IsBorel B) :
    Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup B) :=
  solvable_torus_free_unipotent (closedSubgroupAlgebraicGroup B)
    hB.1.1 hB.1.2.1 hB.1.2.2 fun T hT ↦
      hfree (Specs.GeometricBorelConjugacy.subgroupOfSubgroup B T) hT

/-- The ground field exhausts the global functions on a proper scheme whose
ring of global sections is a domain. -/
private theorem proper_constants [IsAlgClosed k] (X : SchemeOver k)
    [IsProper X.hom] [IsDomain Γ(X.left, ⊤)] :
    Function.Surjective (algebraMap k (coordinates X)) := by
  have hi : (algebraMap k (coordinates X)).IsIntegral := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom.IsIntegral
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed X.hom
  letI : IsDomain (coordinates X) := inferInstanceAs (IsDomain Γ(X.left, ⊤))
  letI : Algebra.IsIntegral k (coordinates X) := ⟨hi⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2

private theorem proper_map_eq [IsAlgClosed k] {X : SchemeOver k}
    [IsProper X.hom] [IsDomain Γ(X.left, ⊤)] (A : TestAlgebra k)
    (f : X ⟶ (testSpec k).obj (op A))
    {Y : SchemeOver k} (p q : Y ⟶ X) : p ≫ f = q ≫ f := by
  let α := algΓAlgSpecAdjunction (CommRingCat.of k)
  apply (α.homEquiv Y (op A)).symm.injective
  rw [α.homEquiv_naturality_left_symm, α.homEquiv_naturality_left_symm]
  apply Quiver.Hom.unop_inj
  ext a
  change coordinateMap p (((α.homEquiv X (op A)).symm f).unop.hom a) =
    coordinateMap q (((α.homEquiv X (op A)).symm f).unop.hom a)
  obtain ⟨c, hc⟩ := proper_constants X (((α.homEquiv X (op A)).symm f).unop.hom a)
  rw [← hc, AlgHom.commutes, AlgHom.commutes]

private theorem coordinateMap_injective_of_epi {X Y : SchemeOver k} (f : X ⟶ Y) [Epi f] :
    Function.Injective (coordinateMap f) := by
  intro a b h
  let A : CommAlgCat (CommRingCat.of k) := CommAlgCat.of k (Polynomial k)
  let F := algΓAlgSpecAdjunction (CommRingCat.of k)
  letI : Algebra k (coordinates Y) := (coordinates Y).algebra
  let p : A ⟶ coordinates Y := CommAlgCat.ofHom (R := k) (Y := coordinates Y) (Polynomial.aeval a)
  let q : A ⟶ coordinates Y := CommAlgCat.ofHom (R := k) (Y := coordinates Y) (Polynomial.aeval b)
  have he : (algΓ (CommRingCat.of k)).map f ≫ p.op =
      (algΓ (CommRingCat.of k)).map f ≫ q.op := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply Polynomial.algHom_ext
    simpa [p, q] using h
  have he' : F.homEquiv Y (op A) p.op = F.homEquiv Y (op A) q.op := by
    apply (cancel_epi f).mp
    rw [← F.homEquiv_naturality_left f p.op, ← F.homEquiv_naturality_left f q.op, he]
  have hh := congrArg (fun t : op (coordinates Y) ⟶ op A ↦ t.unop.hom Polynomial.X)
    ((F.homEquiv Y (op A)).injective he')
  change (Polynomial.aeval (R := k) a) Polynomial.X =
    (Polynomial.aeval (R := k) b) Polynomial.X at hh
  rwa [Polynomial.aeval_X, Polynomial.aeval_X] at hh

private theorem affineFunction {X : SchemeOver k} (hX : IsAffine X.left)
    (F : ∀ R : TestAlgebra k, Points X R → R)
    (hF : ∀ (R S : TestAlgebra k) (a : R ⟶ S) (p : Points X R),
      F S ((testSpec k).map a.op ≫ p) = a (F R p)) :
    ∃ f : X ⟶ (testSpec k).obj (op (CommAlgCat.of k (Polynomial k))),
      ∀ (R : TestAlgebra k) (p : Points X R),
        p ≫ f = (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (F R p))).op := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hX
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  refine ⟨e.inv ≫ (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (F A.unop e.hom))).op, ?_⟩
  intro R p
  let a := ff.preimage (p ≫ e.inv)
  have ha : (testSpec k).map a = p ≫ e.inv := ff.map_preimage _
  have hpa : (testSpec k).map a ≫ e.hom = p := by rw [ha, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← ha, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  simpa [hpa] using (hF A.unop R a.unop e.hom).symm

private theorem properQuotient_desc {G : GroupScheme k} {H : ClosedSubgroup G}
    (Q : Specs.QuotientEmbedding.Presentation H) {Y : SchemeOver k} (f : G.X ⟶ Y)
    (hf : (prod.fst : G.X ⨯ H.group.X ⟶ G.X) ≫ f =
      Specs.HomogeneousQuotient.rightMultiplication H ≫ f) :
    ∃ d : Q.scheme ⟶ Y, Q.projection ≫ d = f := by
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  apply descends Q.projection f
  intro Z a b h
  have square := HomogeneousQuotient.quotientPullback Q
  let m := square.lift a b h
  calc
    a ≫ f = (m ≫ (prod.fst : G.X ⨯ H.group.X ⟶ G.X)) ≫ f :=
      congrArg (· ≫ f) (square.lift_fst a b h).symm
    _ = (m ≫ Specs.HomogeneousQuotient.rightMultiplication H) ≫ f := by
      simp only [Category.assoc, hf]
    _ = b ≫ f := congrArg (· ≫ f) (square.lift_snd a b h)

private theorem unipotent_diagonal {G : AffineAlgebraicGroup k}
    (B : ClosedSubgroup G.val) (hU : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup B))
    {I : Type u} [Fintype I] [DecidableEq I] (i : I)
    (β : (groupPointsFunctor k).obj G.val ⟶ Specs.StandardGroups.generalLinearPoints k I)
    (hcol : ∀ (R : TestAlgebra k) (b : Points B.group.X R) (j : I), j ≠ i →
      ((β.app R (b ≫ B.inclusion.hom.hom)).val j i : R) = 0)
    (R : TestAlgebra k) (b : Points B.group.X R) :
    ((β.app R (b ≫ B.inclusion.hom.hom)).val i i : R) = 1 := by
  classical
  obtain ⟨A, ⟨a⟩, hA⟩ := hU
  obtain ⟨E, _, _⟩ := hopfSpecPoints k
  let pointRepresentation := (E A).hom ≫ (groupPointsFunctor k).map (a.hom ≫ B.inclusion) ≫ β
  let M := pointMatrix A pointRepresentation
  have hzer : ∀ j ≠ i, M j i = 0 := by
    intro j hj
    let x := (E A).hom.app (CommAlgCat.of k A) (toConv (AlgHom.id k A))
    exact hcol (CommAlgCat.of k A) (x ≫ a.hom.hom.hom) j hj
  have hgl : IsGroupLikeElem k (M i i) :=
    weight_of_column_isGroupLike (𝟙 A) M (pointMatrix_isCoactionMatrix A pointRepresentation) i hzer
  have h1 : M i i = 1 := groupLike_eq_one_of_invariants hA ⟨M i i, hgl⟩
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso ((E A).hom.app R)).2
    (b ≫ a.inv.hom.hom)
  have he := congrArg (fun D : Matrix I I R ↦ D i i) (pointMatrix_evaluation A pointRepresentation R x)
  change _ = x.ofConv (M i i) at he
  rw [h1, map_one] at he
  change (β.app R ((((E A).hom.app R x) ≫ a.hom.hom.hom) ≫ B.inclusion.hom.hom)).val i i = 1 at he
  have ha : a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 B.group.X :=
    (Grp.forget (SchemeOver k)).congr_map a.inv_hom_id
  have hb : (b ≫ a.inv.hom.hom) ≫ a.hom.hom.hom = b := by
    rw [Category.assoc, ha, Category.comp_id]
  rw [hx, hb] at he
  exact he

private theorem properQuotient_constant [IsAlgClosed k]
    {G : GroupScheme k} (hG : IsAffine G.X.left)
    {B : ClosedSubgroup G} (hB : IsAffine B.group.X.left)
    (Q : Specs.QuotientEmbedding.Presentation B)
    [IsProper Q.scheme.hom] [IsDomain Γ(Q.scheme.left, ⊤)]
    (F : ∀ R : TestAlgebra k, Points G.X R → R)
    (hF : ∀ (R S : TestAlgebra k) (a : R ⟶ S) (p : Points G.X R),
      F S ((testSpec k).map a.op ≫ p) = a (F R p))
    (hinv : ∀ (R : TestAlgebra k) (x : Points G.X R) (y : Points B.group.X R),
      F R (x * (y ≫ B.inclusion.hom.hom)) = F R x)
    (R : TestAlgebra k) (g g' : Points G.X R) : F R g = F R g' := by
  letI := hG
  letI := hB
  obtain ⟨f, hf⟩ := affineFunction hG F hF
  let Y := G.X ⨯ B.group.X
  have hy : IsAffine Y.left := by
    letI : IsAffineHom B.group.X.hom := by
      have : IsAffine (Spec (CommRingCat.of k)) := inferInstance
      infer_instance
    let P := BinaryFan.mk (prod.fst : Y ⟶ G.X) (prod.snd : Y ⟶ B.group.X)
    exact IsAffine.of_isPullback (Over.isPullback_of_binaryFan_isLimit P (prodIsProd _ _))
  obtain ⟨S, ⟨s⟩⟩ := essImage_algSpec.mpr hy
  let fstMap : Y ⟶ G.X := prod.fst
  let right : Y ⟶ G.X := Specs.HomogeneousQuotient.rightMultiplication B
  let x : Points G.X S.unop := s.hom ≫ fstMap
  let y : Points B.group.X S.unop := s.hom ≫ prod.snd
  have hmul : s.hom ≫ right = x * (y ≫ B.inclusion.hom.hom) := by
    change s.hom ≫ (fstMap * (prod.snd ≫ B.inclusion.hom.hom)) = _
    rw [MonObj.comp_mul, Category.assoc s.hom]
  have hr : fstMap ≫ f = right ≫ f := by
    apply (cancel_epi s.hom).mp
    calc
      s.hom ≫ (fstMap ≫ f) = x ≫ f := (Category.assoc _ _ _).symm
      _ = (s.hom ≫ right) ≫ f := by
        rw [hf S.unop x, hf S.unop (s.hom ≫ right), hmul, hinv S.unop x y]
      _ = s.hom ≫ (right ≫ f) := Category.assoc _ _ _
  obtain ⟨d, hd⟩ := properQuotient_desc Q f hr
  have eq : g ≫ f = g' ≫ f := by
    rw [← hd, ← Category.assoc, ← Category.assoc]
    exact proper_map_eq _ d _ _
  rw [hf, hf] at eq
  have eq' := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective eq
  have hval := congrArg (fun v : op R ⟶ op (CommAlgCat.of k (Polynomial k)) ↦
    v.unop.hom Polynomial.X) eq'
  change (Polynomial.aeval (R := k) (F R g)) Polynomial.X =
    (Polynomial.aeval (R := k) (F R g')) Polynomial.X at hval
  rwa [Polynomial.aeval_X, Polynomial.aeval_X] at hval

private theorem properQuotient_unipotent [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (B : ClosedSubgroup G.val) (hU : Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup B))
    (Q : Specs.QuotientEmbedding.Presentation B) (hproper : IsProper Q.scheme.hom) :
    Specs.Unipotent.IsUnipotent G := by
  classical
  letI := G.property.1
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  letI := hproper
  haveI : IsIntegral G.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral G hs hc
  haveI : Epi Q.projection.left := Flat.epi_of_flat_of_surjective _
  haveI : Epi Q.projection := (Over.forget _).epi_of_epi_map (f := Q.projection)
    inferInstanceAs (Epi Q.projection.left)
  haveI : IsDomain (coordinates G.val.X) := inferInstanceAs (IsDomain Γ(G.val.X.left, ⊤))
  haveI : IsDomain Γ(Q.scheme.left, ⊤) :=
    (coordinateMap_injective_of_epi Q.projection).isDomain (coordinateMap Q.projection)
  obtain ⟨I, _, _, i, L, e, ρ, hρ⟩ := chevalleyLine k G B
  let β := (groupPointsFunctor k).map ρ ≫ e.hom
  have hcol (R : TestAlgebra k) (b : Points B.group.X R) :
      ∀ j ≠ i, ((β.app R (b ≫ B.inclusion.hom.hom)).val j i : R) = 0 :=
    (coordinateLine_iff _ _).mp ((hρ R _).mpr ⟨b, rfl⟩)
  have hdiag := unipotent_diagonal B hU i β hcol
  have hinv (R : TestAlgebra k) (g : Points G.val.X R) (b : Points B.group.X R) (j : I) :
      ((β.app R (g * (b ≫ B.inclusion.hom.hom))).val j i : R) =
      ((β.app R g).val j i : R) := by
    rw [map_mul]
    change (∑ l, (β.app R g).val j l *
      (β.app R (b ≫ B.inclusion.hom.hom)).val l i) = _
    rw [Finset.sum_eq_single i]
    · rw [hdiag, mul_one]
    · intro l _ hl
      rw [hcol R b l hl, mul_zero]
    · simp
  have hall (R : TestAlgebra k) (g : Points G.val.X R) (j : I) :
      ((β.app R g).val j i : R) = (1 : Matrix I I R) j i := by
    let F (S : TestAlgebra k) (s : Points G.val.X S) : S := (β.app S s).val j i
    have hF (S S' : TestAlgebra k) (a : S ⟶ S') (p : Points G.val.X S) :
        F S' ((testSpec k).map a.op ≫ p) = a (F S p) := by
      exact congrArg (fun z : Matrix.GeneralLinearGroup I S' ↦ z.val j i)
        (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (β.naturality a)) p)
    have he := properQuotient_constant G.property.1
      (closedSubgroupAlgebraicGroup B).property.1 Q F hF (fun S x y ↦ hinv S x y j) R g 1
    simpa [F, map_one] using he
  have hG (R : TestAlgebra k) (g : Points G.val.X R) : ∃ b : Points B.group.X R,
      b ≫ B.inclusion.hom.hom = g := by
    apply (hρ R g).mp
    apply (coordinateLine_iff _ _).mpr
    intro j hj
    exact (hall R g j).trans (Matrix.one_apply_ne hj)
  obtain ⟨S, ⟨s⟩⟩ := essImage_algSpec.mpr G.property.1
  obtain ⟨b, hb⟩ := hG S.unop s.hom
  letI := B.isClosedImmersion
  have hright : (s.inv ≫ b) ≫ B.inclusion.hom.hom = 𝟙 G.val.X := by
    simp only [Category.assoc, hb, s.inv_hom_id]
  haveI : Mono B.inclusion.hom.hom := mono_over _ B.isClosedImmersion
  letI : IsSplitEpi B.inclusion.hom.hom := IsSplitEpi.mk' ⟨s.inv ≫ b, hright⟩
  haveI : IsIso B.inclusion.hom.hom := isIso_of_mono_of_isSplitEpi _
  haveI : IsIso B.inclusion.hom.hom.left := (Over.forget _).map_isIso B.inclusion.hom.hom
  haveI : IsIso B.inclusion := isIso_of_schemeIso B.inclusion
  exact unipotent_iso (asIso B.inclusion) hU

/-- A smooth connected affine group with no nontrivial geometric torus is unipotent. -/
theorem torusFreeUnipotent : Specs.TorusFreeUnipotent.Unipotence.{u} := by
  intro k _ G hs hc hfree
  let K := AlgebraicClosure k
  let H := Specs.GeometricRadicals.GeometricGroup G
  have hH : Smooth H.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hs
  have hHconn : ConnectedSpace H.val.X.left := by
    letI := hc
    exact pullback_of_geometrically (geometricallyConnected_of_connected G).geometrically_connectedSpace
      K (fieldSpecMap k K)
  obtain ⟨B, hB⟩ := GeometricBorelConjugacy.borelExists H hH hHconn
  obtain ⟨Q⟩ := (HomogeneousQuotient.homogeneousQuotient K H B).1
  exact (Unipotent.unipotenceFieldExtension (K := K) G).mp
    (properQuotient_unipotent H hH hHconn B (borel_unipotent_of_torus_free H hfree B hB)
      Q (BorelProper.geometricBorelQuotientProper G hs hc B hB Q))

private theorem torus_commutative (D : AffineAlgebraicGroup k) (h : IsTorus D.val) :
    IsCommMonObj D.val.X := by
  obtain ⟨A, ⟨e⟩, hA⟩ := (isTorus_iff_coordinates D).mp h
  exact isCommMonObj_of_groupIso e
    (CharacterDescent.multiplicativeTypeProperties A
      (CharacterDescent.torusIsMultiplicativeType A hA)).2

private theorem unipotent_sections_solvable (G : AffineAlgebraicGroup k)
    (h : IsUnipotent G) : Group.IsSolvable (rationalSections G.val) := by
  obtain ⟨n, U, ⟨e⟩, j, hj⟩ := (unipotent_iff_exists_embedding G).mp h
  let R : TestAlgebra k := CommAlgCat.of k k
  let S := (testSpec k).obj (op R)
  let a : S ≅ 𝟙_ (SchemeOver k) :=
    (affineBaseTerminal k).uniqueUpToIso isTerminalTensorUnit
  let restriction : rationalSections G.val →* Points G.val.X R :=
    { toFun := fun x ↦ a.hom ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y ↦ MonObj.comp_mul _ x y }
  letI := split_solvable_points (unitriangular_split_solvable U e) R
  exact Group.isSolvable_of_isSolvable_injective
    (f := (IsMonHom.monoidHom j.hom.hom S).comp restriction)
    ((onPoints_injective j hj R).comp (fun _ _ h ↦ (cancel_epi a.hom).mp h))

private theorem solvable_of_schemeKernel [IsAlgClosed k] {G Q : AffineAlgebraicGroup k}
    {N : ClosedSubgroup G.val} (q : G.val ⟶ Q.val) (hq : IsSchemeKernel q N)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    [Group.IsSolvable (rationalSections N.group)] [Group.IsSolvable (rationalSections Q.val)] :
    IsSolvable G.val :=
  (solvable_iff_sections G hs hc).mpr
    (Group.isSolvable_of_ker_le_range (rationalMap N.inclusion) (rationalMap q)
      (fun g hg ↦ (schemeKernel_sections hq g).mpr hg))

/-- An fppf extension of tori over an algebraically closed field is a torus. -/
private theorem torus_of_torus_extension [IsAlgClosed k] {G Q : AffineAlgebraicGroup k}
    {N : ClosedSubgroup G.val} (q : G.val ⟶ Q.val) (hq : IsFppfGroupQuotient N q)
    (hN : IsTorus N.group) (hQ : IsTorus Q.val) : IsTorus G.val := by
  let A := closedSubgroupAlgebraicGroup N
  obtain ⟨hsN, hcN, hsolN⟩ := torus_smooth_connected_solvable A hN
  obtain ⟨hsQ, hcQ, hsolQ⟩ := torus_smooth_connected_solvable Q hQ
  obtain ⟨hsG, hcG⟩ := extension_smooth_connected G Q N q hq hsQ hcQ hsN hcN
  letI : Group.IsSolvable (rationalSections N.group) :=
    (solvable_iff_sections A hsN hcN).mp hsolN
  letI : Group.IsSolvable (rationalSections Q.val) :=
    (solvable_iff_sections Q hsQ hcQ).mp hsolQ
  obtain ⟨U, D, d, hU, hd, hD, _⟩ := GeometricTorusSplitting.splitting G hsG hcG
    (solvable_of_schemeKernel (G := G) (Q := Q) (N := N) q hq.1 hsG hcG)
  have hUN := hU.2.2.2.1
  have hUQ : U.inclusion ≫ q = 0 := Unipotent.homFromUnipotentToMultiplicativeType
    (closedSubgroupAlgebraicGroup U) Q (U.inclusion ≫ q) hUN
    (torus_multiplicativeType ((isTorus_iff_coordinates Q).mp hQ))
  have hkill : U.inclusion.hom.hom ≫ q.hom.hom = 1 :=
    congrArg (fun f : U.group ⟶ Q.val ↦ f.hom.hom) hUQ
  obtain ⟨l, hl⟩ := (schemeKernel_sections hq.1 U.inclusion.hom.hom).mpr hkill
  letI := N.isClosedImmersion
  letI := isMonHom_of_comp_closed l U.inclusion N.inclusion hl
  let v : U.group ⟶ N.group := Grp.homMk l
  have hv : v ≫ N.inclusion = U.inclusion := Grp.hom_ext _ _ hl
  have hv0 : v = 0 := Unipotent.homFromUnipotentToMultiplicativeType
    (closedSubgroupAlgebraicGroup U) A v hUN
    (torus_multiplicativeType ((isTorus_iff_coordinates A).mp hN))
  letI := inclusion_mono U
  have htriv : IsZero U.group := IsZero.of_mono_eq_zero U.inclusion (by rw [← hv, hv0, zero_comp])
  letI := isIso_of_trivial_kernel (G := G) (Q := D) d U hd ⟨htriv.iso (Grp.isZero_trivial _)⟩
  exact torus_of_iso (asIso d).symm ((isTorus_iff_coordinates D).mpr (torus_of_split hD))

/-- Pulling a torus back to the centralizer gives a torus containing the original
maximal one. Its projection to the quotient torus is therefore trivial. -/
private theorem quotient_tori_trivial [IsAlgClosed k] {G Q : AffineAlgebraicGroup k}
    (T C : ClosedSubgroup G.val) (hT : IsMaximalTorus T)
    (j : T.group ⟶ C.group) (hj : j ≫ C.inclusion = T.inclusion)
    (hjc : IsClosedImmersion j.hom.hom.left) (q : C.group ⟶ Q.val)
    (hq : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup C) ⟨_, j, hjc⟩ q)
    (S : ClosedSubgroup Q.val) (hS : IsTorus S.group) : IsTrivialSubgroup S := by
  let P := pullback q S.inclusion
  let i : P ⟶ C.group := pullback.fst q S.inclusion
  let p : P ⟶ S.group := pullback.snd q S.inclusion
  have square : IsPullback i.hom.hom p.hom.hom q.hom.hom S.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).map_isPullback (.of_hasPullback q S.inclusion)
  have underlying := square.map (Over.forget _)
  have hi : IsClosedImmersion i.hom.hom.left :=
    MorphismProperty.of_isPullback underlying.flip S.isClosedImmersion
  let P' : ClosedSubgroup C.group := ⟨P, i, hi⟩
  let A := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C) P'
  let jP : T.group ⟶ P := pullback.lift j (0 : T.group ⟶ S.group) (by
    rw [zero_comp]
    exact Grp.hom_ext _ _ hq.1.w)
  have hji : jP ≫ i = j := pullback.lift_fst ..
  have hjp : jP ≫ p = 0 := pullback.lift_snd ..
  let N : ClosedSubgroup A.val :=
    ⟨_, jP, factor_closed (H := ⟨T.group, j, hjc⟩) (N := P') hji⟩
  have hker : IsSchemeKernel p N := by
    have hη : η[S.group.X] ≫ S.inclusion.hom.hom = η[Q.val.X] := IsMonHom.one_hom _
    have hwhole : IsPullback (jP.hom.hom ≫ i.hom.hom) (toUnit T.group.X)
        q.hom.hom (η[S.group.X] ≫ S.inclusion.hom.hom) := by
      rw [show jP.hom.hom ≫ i.hom.hom = j.hom.hom from
        congrArg (fun f : T.group ⟶ C.group ↦ f.hom.hom) hji, hη]
      exact hq.1
    exact hwhole.of_right (congrArg (fun f : T.group ⟶ S.group ↦ f.hom.hom) hjp) square
  have hp : IsFppfGroupQuotient (Q := closedSubgroupAlgebraicGroup S) N p :=
    represented_quotient_of_kernel (G := A) (Q := closedSubgroupAlgebraicGroup S) p N hker
      (MorphismProperty.of_isPullback underlying hq.2.1)
      (MorphismProperty.of_isPullback underlying hq.2.2.1)
      (MorphismProperty.of_isPullback underlying hq.2.2.2.1)
  have hA : IsTorus A.val :=
    torus_of_torus_extension (G := A) (Q := closedSubgroupAlgebraicGroup S) p hp hT.1 hS
  let D := subgroupOfSubgroup C P'
  have hTD : jP ≫ D.inclusion = T.inclusion := by
    change jP ≫ (i ≫ C.inclusion) = T.inclusion
    rw [← Category.assoc, hji, hj]
  obtain ⟨r, hr⟩ := hT.2 D hA ⟨jP, hTD⟩
  have hsec : r ≫ jP = 𝟙 P := by
    letI := inclusion_mono D
    apply (cancel_mono D.inclusion).mp
    calc
      (r ≫ jP) ≫ D.inclusion = r ≫ T.inclusion := by rw [Category.assoc, hTD]
      _ = D.inclusion := hr
      _ = (𝟙 D.group) ≫ D.inclusion := (Category.id_comp _).symm
  have hp0 : p = 0 := by
    rw [← Category.id_comp p, ← hsec, Category.assoc, hjp, comp_zero]
  letI := hp.2.1
  letI := hp.2.2.1
  haveI : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  haveI : Epi p.hom.hom := (Over.forget _).epi_of_epi_map (f := p.hom.hom)
    inferInstanceAs (Epi p.hom.hom.left)
  haveI : Epi p := (Grp.forget _).epi_of_epi_map (f := p) inferInstanceAs (Epi p.hom.hom)
  exact ⟨(IsZero.of_epi_eq_zero p hp0).iso (Grp.isZero_trivial _)⟩

private theorem torus_in_centralizer {G : AffineAlgebraicGroup k} {T C : ClosedSubgroup G.val}
    (hT : IsCommMonObj T.group.X)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes T.inclusion g)) :
    ∃ (j : T.group ⟶ C.group), IsClosedImmersion j.hom.hom.left ∧
      j ≫ C.inclusion = T.inclusion ∧ IsNormalSubgroup j := by
  letI := hT
  have hTT : Centralizes T.inclusion T.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro U x y
    exact (show Commute x y from mul_comm x y).map (IsMonHom.monoidHom T.inclusion.hom.hom U)
  obtain ⟨f, hf⟩ := (hC _ _).mp hTT
  letI := C.isClosedImmersion
  letI := isMonHom_of_comp_closed f T.inclusion C.inclusion hf
  let j : T.group ⟶ C.group := Grp.homMk f
  have hj : j ≫ C.inclusion = T.inclusion := Grp.hom_ext _ _ hf
  refine ⟨j, factor_closed hj, hj, ?_⟩
  apply central_normal
  intro U x y
  have hx := (hC U (x ≫ C.inclusion.hom.hom)).mpr ⟨x, rfl⟩
  have hy := (centralizes_iff _ _).mp hx U (𝟙 U) y
  haveI : Mono C.inclusion.hom.hom := mono_over _ C.isClosedImmersion
  apply (cancel_mono C.inclusion.hom.hom).mp
  change (x * (y ≫ f)) ≫ C.inclusion.hom.hom = ((y ≫ f) * x) ≫ C.inclusion.hom.hom
  simp only [MonObj.mul_comp, Category.assoc, hf]
  simpa only [Category.id_comp] using hy.eq

/-- The scheme centralizer of a geometric maximal torus has unipotent right
quotient by the torus and is contained in every Borel containing it. -/
theorem maximalTorusCentralizer : Specs.TorusFreeUnipotent.MaximalTorusCentralizer.{u} := by
  intro k _ _ G hs hc T hT
  letI := hs
  letI := hc
  obtain ⟨C, hC, hsC, hgC⟩ := CocharacterDynamics.connectedTorusCentralizer G T hT.1
  have hcomm : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT.1
  obtain ⟨j, hjc, hj, hn⟩ := torus_in_centralizer (G := G) hcomm hC
  let N : ClosedSubgroup C.group := ⟨T.group, j, hjc⟩
  let A := closedSubgroupAlgebraicGroup C
  obtain ⟨_, _, Q, q, _, _, hk, hfactor, _, hquot⟩ := normalAffineQuotient A N hn
  have hq : IsFppfGroupQuotient N q :=
    ⟨hk, hfactor.2.1, hfactor.2.2.1, hfactor.2.2.2.1, hquot⟩
  letI := hgC
  have hcC : ConnectedSpace C.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C.group.X.hom)
  obtain ⟨hsQ, hcQ⟩ :=
    affine_quotient_smooth_connected (G := A) (Q := Q) q hq.2.1 hq.2.2.1 hsC hcC
  have hfree (S : ClosedSubgroup Q.val) (hS : IsTorus S.group) : IsTrivialSubgroup S :=
    quotient_tori_trivial (G := G) (Q := Q) T C hT j hj hjc q hq S hS
  obtain ⟨B, Y, hB, hY⟩ := closed_flag_quotient_proper GeometricBorelConjugacy.closedFlagOrbitExists
    GeometricBorelConjugacy.closedFlagStabilizerIsBorel Q hsQ hcQ
  have hU := properQuotient_unipotent Q hsQ hcQ B
    (borel_unipotent_of_torus_free Q hfree B hB) Y hY
  letI : Group.IsSolvable (rationalSections Q.val) := unipotent_sections_solvable Q hU
  letI : IsCommMonObj T.group.X := hcomm
  letI : Group.IsSolvable (rationalSections N.group) :=
    Group.isSolvable_of_comm (G := rationalSections T.group) fun x y ↦ mul_comm x y
  have hsol : IsSolvable C.group := solvable_of_schemeKernel (G := A) (Q := Q) (N := N) q hk hsC hcC
  exact ⟨C, hC, hsC, hgC, hsol,
    centralizer_le_borel G hs hc T C hT hC ⟨hsC, hcC, hsol⟩ ⟨j, hj⟩,
    j, hjc, Q, q, hj, hq, hU⟩

end

end LinearAlgebraicGroups.TorusFreeUnipotent
