import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.Valuation.LocalSubring
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology Filter
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open scoped RestrictedProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism

open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (Index)
open Specs.StandardGroups (GLCoordinates universalMatrix)
open AdelicGroups

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open private glEvaluation glEvaluation_entry from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap coordinateMap_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.IntegralModels
open private matrixPresentation continuous_glEvaluation glIntegral_iff glEvaluation_eventually
  eventually_outside from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private compactLocalBasisBox from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

variable {K : Type u} [Field K] {G Q : AffineAlgebraicGroup K}

private structure Presentation (i : MatrixRealization G) where
  A : TestAlgebra K
  iso : (testSpec K).obj (op A) ≅ G.val.X
  coordinates : CommAlgCat.of K (GLCoordinates K (Index.{u} i.size)) ⟶ A
  surjective : Function.Surjective coordinates.hom
  evaluation : ∀ (R : Type u) [CommRing R] [Algebra K R] (g : PointsIn i R),
    glEvaluation (asMatrix i R g) = (coordinates ≫ coordinateMap (g ≫ iso.inv)).hom

private def presentation (i : MatrixRealization G) : Presentation i := Classical.choice (by
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, ha, he⟩ := matrixPresentation B.unop e i
  exact ⟨⟨B.unop, e, a, ha, he⟩⟩)

private def pointEvaluation {i : MatrixRealization G} (P : Presentation i)
    {R : Type u} [CommRing R] [Algebra K R] (g : PointsIn i R) : P.A →ₐ[K] R :=
  (coordinateMap (g ≫ P.iso.inv)).hom

private theorem coordinate_evaluation {i : MatrixRealization G} (P : Presentation i)
    {R : Type u} [CommRing R] [Algebra K R] (g : PointsIn i R) (a) :
    glEvaluation (asMatrix i R g) a = pointEvaluation P g (P.coordinates.hom a) :=
  DFunLike.congr_fun (P.evaluation R g) a

private theorem continuous_pointEvaluation {i : MatrixRealization G} (P : Presentation i)
    {R : Type u} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R] (a : P.A) :
    Continuous (fun g : PointsIn i R => pointEvaluation P g a) := by
  obtain ⟨b, rfl⟩ := P.surjective a
  simp_rw [← coordinate_evaluation P]
  exact (continuous_glEvaluation b).comp continuous_induced_dom

private theorem pointEvaluation_eventually (D : GlobalFieldData.{u, v} K)
    {i : MatrixRealization G} (P : Presentation i) (a : P.A) :
    ∀ᶠ w : D.FinitePlace in cofinite, ∀ g : LocalPoints D i (.inl w),
      g ∈ integralPoints D i w → pointEvaluation P g a ∈ D.integers w := by
  obtain ⟨b, rfl⟩ := P.surjective a
  filter_upwards [glEvaluation_eventually D b] with w hw g hg
  rw [← coordinate_evaluation P]
  exact hw _ hg

private def pullback {i : MatrixRealization G} {j : MatrixRealization Q}
    (P : Presentation i) (T : Presentation j) (q : G.val ⟶ Q.val) : T.A ⟶ P.A :=
  coordinateMap (P.iso.hom ≫ q.hom.hom ≫ T.iso.inv)

private theorem pullback_spec {i : MatrixRealization G} {j : MatrixRealization Q}
    (P : Presentation i) (T : Presentation j) (q : G.val ⟶ Q.val) :
    (testSpec K).map (pullback P T q).op = P.iso.hom ≫ q.hom.hom ≫ T.iso.inv :=
  coordinateMap_spec _

private theorem pointEvaluation_pullback {i : MatrixRealization G} {j : MatrixRealization Q}
    (P : Presentation i) (T : Presentation j) (q : G.val ⟶ Q.val)
    {R : Type u} [CommRing R] [Algebra K R] (g : PointsIn i R) (b : T.A) :
    pointEvaluation P g ((pullback P T q).hom b) = pointEvaluation T (pointsMap q i j R g) b := by
  have he : pullback P T q ≫ coordinateMap (g ≫ P.iso.inv) =
      coordinateMap ((pointsMap q i j R g) ≫ T.iso.inv) := by
    apply Quiver.Hom.op_inj
    apply (algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective
    rw [CategoryTheory.op_comp, Functor.map_comp, coordinateMap_spec, pullback_spec,
      coordinateMap_spec]
    change (g ≫ P.iso.inv) ≫ P.iso.hom ≫ q.hom.hom ≫ T.iso.inv = (g ≫ q.hom.hom) ≫ T.iso.inv
    simp [Category.assoc]
  exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom he) b

private theorem pullback_finite {i : MatrixRealization G} {j : MatrixRealization Q}
    (P : Presentation i) (T : Presentation j) (q : G.val ⟶ Q.val)
    (hq : IsFinite q.hom.hom.left) :
    (pullback P T q).hom.toRingHom.Finite := by
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (pullback P T q).hom.toRingHom)).mp
  change IsFinite ((testSpec K).map (pullback P T q).op).left
  rw [pullback_spec]
  change IsFinite (P.iso.hom.left ≫ q.hom.hom.left ≫ T.iso.inv.left)
  haveI : IsIso P.iso.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.iso.hom))
  haveI : IsIso T.iso.inv.left := inferInstanceAs (IsIso ((Over.forget _).map T.iso.inv))
  infer_instance

private def matrixEntry {i : MatrixRealization G} (P : Presentation i)
    (l m : Index.{u} i.size) : P.A :=
  P.coordinates.hom (universalMatrix K _ l m)

private theorem pointEvaluation_matrixEntry {i : MatrixRealization G} (P : Presentation i)
    {R : Type u} [CommRing R] [Algebra K R] (g : PointsIn i R) (l m : Index.{u} i.size) :
    pointEvaluation P g (matrixEntry P l m) = (asMatrix i R g).val l m := by
  rw [matrixEntry, ← coordinate_evaluation P, glEvaluation_entry]

private theorem map_entry {i : MatrixRealization G} {j : MatrixRealization Q}
    (P : Presentation i) (T : Presentation j) (q : G.val ⟶ Q.val)
    {R : Type u} [CommRing R] [Algebra K R] (g : PointsIn i R) (l m : Index.{u} j.size) :
    pointEvaluation P g ((pullback P T q).hom (matrixEntry T l m)) =
      (asMatrix j R (pointsMap q i j R g)).val l m := by
  rw [pointEvaluation_pullback, pointEvaluation_matrixEntry]

theorem continuous_pointsMap (q : G.val ⟶ Q.val) (i : MatrixRealization G) (j : MatrixRealization Q)
    (R : Type u) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (pointsMap q i j R) := by
  let P := presentation i
  let T := presentation j
  refine (IsInducing.induced (asMatrix j R)).continuous_iff.mpr ?_
  have h : Continuous (fun g => (asMatrix j R (pointsMap q i j R g)).val) := by
    refine continuous_matrix fun l m => ?_
    simp_rw [← map_entry P T q]
    exact continuous_pointEvaluation P _
  refine Units.continuous_iff.mpr ⟨h, ?_⟩
  have hinv : Continuous (fun g : PointsIn i R =>
      (asMatrix j R (pointsMap q i j R g⁻¹)).val) := h.comp continuous_inv
  simpa only [Function.comp_apply, map_inv] using hinv

private theorem integralMap_eventually (D : GlobalFieldData.{u, v} K)
    (q : G.val ⟶ Q.val) (i : MatrixRealization G) (j : MatrixRealization Q) :
    ∀ᶠ w : D.FinitePlace in cofinite,
      Set.MapsTo (pointsMap q i j (D.Completion (.inl w)))
        (integralPoints D i w) (integralPoints D j w) := by
  let P := presentation i
  let T := presentation j
  have h (l m : Index.{u} j.size) : ∀ᶠ w : D.FinitePlace in cofinite,
      ∀ g : LocalPoints D i (.inl w), g ∈ integralPoints D i w →
        (asMatrix j _ (pointsMap q i j _ g)).val l m ∈ D.integers w := by
    filter_upwards [pointEvaluation_eventually D P ((pullback P T q).hom (matrixEntry T l m))]
      with w hw g hg
    rw [← map_entry P T q]
    exact hw g hg
  filter_upwards [eventually_all.mpr fun l => eventually_all.mpr (h l)] with w hw g hg
  change asMatrix j _ (pointsMap q i j _ g) ∈
    (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range
  refine (glIntegral_iff _ _).mpr ⟨fun l m => hw l m g hg, fun l m => ?_⟩
  simpa only [map_inv] using hw l m g⁻¹ ((integralPoints D i w).inv_mem hg)

private theorem subgroupMap_eventually (D : GlobalFieldData.{u, v} K)
    (q : G.val ⟶ Q.val) (i : MatrixRealization G) (j : MatrixRealization Q) :
    ∀ᶠ w : Outside D ∅ in cofinite, Set.MapsTo (pointsMap q i j (D.Completion w.1))
      (localSubgroup D i w.1) (localSubgroup D j w.1) :=
  eventually_outside D ∅ (p := fun w => Set.MapsTo (pointsMap q i j (D.Completion w))
    (localSubgroup D i w) (localSubgroup D j w)) (integralMap_eventually D q i j)
    (fun _ _ _ => Subgroup.mem_top _)

/-- Application of a group scheme homomorphism at every completion. -/
def adelicMap (D : GlobalFieldData.{u, v} K) (q : G.val ⟶ Q.val)
    (i : MatrixRealization G) (j : MatrixRealization Q) : Adeles D i ∅ →* Adeles D j ∅ :=
  RestrictedProduct.mapAlongMonoidHom
    (fun w : Outside D ∅ => LocalPoints D i w.1) (fun w : Outside D ∅ => LocalPoints D j w.1)
    id (tendsto_id : Tendsto (id : Outside D ∅ → Outside D ∅) cofinite cofinite)
    (fun w => pointsMap q i j (D.Completion w.1)) (subgroupMap_eventually D q i j)

@[simp] theorem adelicMap_apply (D : GlobalFieldData.{u, v} K) (q : G.val ⟶ Q.val)
    (i : MatrixRealization G) (j : MatrixRealization Q) (x : Adeles D i ∅) (w : Outside D ∅) :
    adelicMap D q i j x w = pointsMap q i j (D.Completion w.1) (x w) := rfl

theorem continuous_adelicMap (D : GlobalFieldData.{u, v} K) (q : G.val ⟶ Q.val)
    (i : MatrixRealization G) (j : MatrixRealization Q) : Continuous (adelicMap D q i j) :=
  RestrictedProduct.mapAlong_continuous
    (fun w : Outside D ∅ => LocalPoints D i w.1) (fun w : Outside D ∅ => LocalPoints D j w.1)
    id (tendsto_id : Tendsto (id : Outside D ∅ → Outside D ∅) cofinite cofinite)
    (fun w => pointsMap q i j (D.Completion w.1)) (subgroupMap_eventually D q i j)
    (fun w => continuous_pointsMap q i j (D.Completion w.1))

open Polynomial

private theorem pointEvaluation_root {i : MatrixRealization G} {j : MatrixRealization Q}
    (P : Presentation i) (T : Presentation j) (q : G.val ⟶ Q.val)
    (a : P.A) (p : T.A[X])
    (hp : p.eval₂ (pullback P T q).hom.toRingHom a = 0)
    {R : Type u} [CommRing R] [Algebra K R] (g : PointsIn i R) :
    p.eval₂ (pointEvaluation T (pointsMap q i j R g)).toRingHom (pointEvaluation P g a) = 0 := by
  have hcomp : (pointEvaluation P g).toRingHom.comp (pullback P T q).hom.toRingHom =
      (pointEvaluation T (pointsMap q i j R g)).toRingHom := by
    ext b
    exact pointEvaluation_pullback P T q g b
  have hz := Polynomial.hom_eval₂ p (pullback P T q).hom.toRingHom
    (pointEvaluation P g).toRingHom a
  rw [hp, map_zero, hcomp] at hz
  exact hz.symm

private theorem mem_of_monic_root {A L : Type*} [CommRing A] [Field L]
    (O : ValuationSubring L) (f : A →+* L) (p : A[X]) (hp : p.Monic) (x : L)
    (hc : ∀ n ∈ p.support, f (p.coeff n) ∈ O) (hx : p.eval₂ f x = 0) : x ∈ O := by
  classical
  have hlift : p.map f ∈ Polynomial.lifts O.subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts (f := O.subtype) _).mpr
    intro n
    rw [Polynomial.coeff_map]
    suffices h : f (p.coeff n) ∈ O by exact ⟨⟨_, h⟩, rfl⟩
    by_cases hn : n ∈ p.support
    · exact hc n hn
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
      exact O.zero_mem
  obtain ⟨p', he, _, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hp.map f)
  have hroot : p'.eval₂ O.subtype x = 0 := by
    rw [← Polynomial.eval_map, he, Polynomial.eval_map, hx]
  have hi : IsIntegral O x := ⟨p', hm, hroot⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact hy ▸ y.property

private theorem integralPreimage_eventually (D : GlobalFieldData.{u, v} K)
    (q : G.val ⟶ Q.val) (hq : IsFinite q.hom.hom.left)
    (i : MatrixRealization G) (j : MatrixRealization Q) :
    ∀ᶠ w : D.FinitePlace in cofinite, ∀ g : LocalPoints D i (.inl w),
      pointsMap q i j _ g ∈ integralPoints D j w → g ∈ integralPoints D i w := by
  let P := presentation i
  let T := presentation j
  have h (l m : Index.{u} i.size) :
      ∀ᶠ w : D.FinitePlace in cofinite, ∀ g : LocalPoints D i (.inl w),
        pointsMap q i j _ g ∈ integralPoints D j w →
        (asMatrix i _ g).val l m ∈ D.integers w := by
    let a := matrixEntry P l m
    obtain ⟨p, hm, hr⟩ := (pullback_finite P T q hq).to_isIntegral a
    have hc : ∀ᶠ w : D.FinitePlace in cofinite,
        ∀ n : p.support, ∀ g : LocalPoints D j (.inl w),
          g ∈ integralPoints D j w → pointEvaluation T g (p.coeff n) ∈ D.integers w :=
      eventually_all.mpr fun n => pointEvaluation_eventually D T (p.coeff n)
    filter_upwards [hc] with w hc g hg
    rw [← pointEvaluation_matrixEntry P]
    exact mem_of_monic_root (D.integers w) _ p hm _ (fun n hn => hc ⟨n, hn⟩ _ hg)
      (pointEvaluation_root P T q a p hr g)
  filter_upwards [eventually_all.mpr fun l => eventually_all.mpr (h l)] with w hw g hg
  change asMatrix i _ g ∈ (Matrix.GeneralLinearGroup.map (D.integers w).subtype).range
  refine (glIntegral_iff _ _).mpr ⟨fun l m => hw l m g hg, fun l m => ?_⟩
  have hgi : pointsMap q i j _ g⁻¹ ∈ integralPoints D j w := by
    rw [map_inv]
    exact (integralPoints D j w).inv_mem hg
  simpa only [map_inv] using hw l m g⁻¹ hgi

private theorem subgroupPreimage_eventually (D : GlobalFieldData.{u, v} K)
    (q : G.val ⟶ Q.val) (hq : IsFinite q.hom.hom.left)
    (i : MatrixRealization G) (j : MatrixRealization Q) :
    ∀ᶠ w : Outside D ∅ in cofinite, ∀ g : LocalPoints D i w.1,
      pointsMap q i j _ g ∈ localSubgroup D j w.1 → g ∈ localSubgroup D i w.1 :=
  eventually_outside D ∅ (p := fun w => ∀ g : LocalPoints D i w,
    pointsMap q i j _ g ∈ localSubgroup D j w → g ∈ localSubgroup D i w)
    (integralPreimage_eventually D q hq i j) (fun _ _ _ => Subgroup.mem_top _)

/-- At each completion, inversion tends to zero away from compact sets. -/
private theorem completion_inv_at_infinity (D : GlobalFieldData.{u, v} K) (w : D.Place) :
    Tendsto (Inv.inv : D.Completion w → D.Completion w) (cocompact _) (𝓝 0) := by
  cases w with
  | inl w =>
    let L := D.FiniteCompletion w
    change Tendsto (Inv.inv : L → L) (cocompact L) (𝓝 0)
    have := D.finiteCompletion_isLocalField w
    apply (IsValuativeTopology.hasBasis_nhds_zero' L).tendsto_right_iff.mpr
    intro γ hγ
    filter_upwards [(IsNonarchimedeanLocalField.isCompact_closedBall L γ⁻¹).compl_mem_cocompact]
      with x hx
    have hx' : γ⁻¹ < ValuativeRel.valuation L x := lt_of_not_ge hx
    have hpos := lt_of_le_of_lt zero_le hx'
    change ValuativeRel.valuation L x⁻¹ < γ
    rw [map_inv₀, ← inv_inv γ]
    exact (inv_lt_inv₀ hpos (inv_pos.mpr (zero_lt_iff.mpr hγ))).2 hx'
  | inr w =>
    cases D with
    | number h =>
      change Tendsto (Inv.inv : w.Completion → w.Completion) (cocompact _) (𝓝 0)
      have : ProperSpace w.Completion := by
        let e := NumberField.InfinitePlace.Completion.extensionEmbedding w
        have he : Isometry e := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
        refine ⟨fun x r => ?_⟩
        have hc := he.isClosedEmbedding.isCompact_preimage
          (isCompact_closedBall (e x) r)
        convert hc using 1
        ext y
        change dist y x ≤ r ↔ dist (e y) (e x) ≤ r
        rw [he.dist_eq]
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    | function F t => exact w.elim

private theorem exists_compact_of_monic_roots
    {A L Y : Type*} [CommRing A] [Field L] [TopologicalSpace L] [T2Space L]
    [IsTopologicalRing L] [TopologicalSpace Y]
    (hinv : Tendsto (Inv.inv : L → L) (cocompact L) (𝓝 0))
    (f : Y → A →+* L) (hf : ∀ a, Continuous (fun y => f y a))
    (p : A[X]) (hp : p.Monic) (C : Set Y) (hC : IsCompact C) :
    ∃ B : Set L, IsCompact B ∧ ∀ y ∈ C, ∀ x, p.eval₂ (f y) x = 0 → x ∈ B := by
  let F (z : Y × L) := p.reverse.eval₂ (f z.1) z.2
  have hF : Continuous F := by
    simp only [F, Polynomial.eval₂_eq_sum, Polynomial.sum]
    exact continuous_finsetSum _ (fun n _ => ((hf _).comp continuous_fst).mul
      (continuous_snd.pow n))
  let U := {z : Y × L | F z ≠ 0}
  have hU : IsOpen U := (isClosed_singleton.preimage hF).isOpen_compl
  have hz : C ×ˢ ({0} : Set L) ⊆ U := by
    rintro ⟨y, z⟩ ⟨_, hz⟩
    have : z = 0 := hz
    subst z
    simp [U, F, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_reverse, hp]
  obtain ⟨V, W, _, hW, hCV, h0W, hVW⟩ :=
    generalized_tube_lemma hC isCompact_singleton hU hz
  obtain ⟨B, hB, hBW⟩ := mem_cocompact'.mp (hinv (hW.mem_nhds (h0W rfl)))
  refine ⟨B ∪ {0}, hB.union isCompact_singleton, fun y hy x hx => ?_⟩
  by_contra hn
  have hx0 : x ≠ 0 := fun h => hn (Or.inr h)
  letI := invertibleOfNonzero hx0
  have hw : x⁻¹ ∈ W := by
    by_contra hw
    exact hn (Or.inl (hBW hw))
  have hpair : (y, x⁻¹) ∈ U := hVW (Set.mk_mem_prod (hCV hy) hw)
  have hne : p.reverse.eval₂ (f y) x⁻¹ ≠ 0 := hpair
  exact hne (by
    rw [← invOf_eq_inv x, Polynomial.eval₂_reverse_eq_zero_iff]
    exact hx)

private theorem compact_local_preimage (D : GlobalFieldData.{u, v} K) (w : D.Place)
    (q : G.val ⟶ Q.val) (hq : IsFinite q.hom.hom.left)
    (i : MatrixRealization G) (j : MatrixRealization Q)
    (C : Set (LocalPoints D j w)) (hC : IsCompact C) :
    IsCompact (pointsMap q i j (D.Completion w) ⁻¹' C) := by
  let R := D.Completion w
  let f := pointsMap q i j R
  let P := presentation i
  let T := presentation j
  letI : T2Space (LocalPoints D j w) := (localMatrixEmbedding D j w).isEmbedding.t2Space
  have hc : IsClosed (f ⁻¹' C) := hC.isClosed.preimage (continuous_pointsMap q i j R)
  let C' := C ∪ (fun g : LocalPoints D j w => g⁻¹) '' C
  have hC' : IsCompact C' := hC.union (hC.image continuous_inv)
  have hentry (l m : Index.{u} i.size) :
      ∃ B : Set R, IsCompact B ∧
        ∀ g : LocalPoints D i w, f g ∈ C' → (asMatrix i R g).val l m ∈ B := by
    let a := matrixEntry P l m
    obtain ⟨p, hm, hr⟩ := (pullback_finite P T q hq).to_isIntegral a
    obtain ⟨B, hB, hb⟩ := exists_compact_of_monic_roots (completion_inv_at_infinity D w)
      (fun g : LocalPoints D j w => (pointEvaluation T g).toRingHom)
      (continuous_pointEvaluation T) p hm C' hC'
    refine ⟨B, hB, fun g hg => ?_⟩
    rw [← pointEvaluation_matrixEntry P]
    exact hb (f g) hg _ (pointEvaluation_root P T q a p hr g)
  choose B hB hmem using hentry
  let E := ⋃ l, ⋃ m, B l m
  have hE : IsCompact E := isCompact_iUnion fun l => isCompact_iUnion (hB l)
  have hbox := (localMatrixEmbedding D i w).isCompact_preimage (compactLocalBasisBox E hE)
  refine hbox.of_isClosed_subset hc ?_
  intro g hg
  have hmem' (x : LocalPoints D i w) (hx : f x ∈ C') (l m : Index.{u} i.size) :
      (asMatrix i R x).val l m ∈ E :=
    Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨m, hmem l m x hx⟩⟩
  refine ⟨hmem' g (Or.inl hg), fun l m => ?_⟩
  have hin : f (g⁻¹) ∈ C' := Or.inr ⟨f g, hg, (map_inv f g).symm⟩
  simpa only [map_inv] using hmem' g⁻¹ hin l m

private theorem compact_eventually_integral {ι : Type*} {R : ι → Type*}
    [∀ w, TopologicalSpace (R w)]
    (A : ∀ w, Set (R w)) (hA : ∀ w, IsOpen (A w))
    (C : Set (Πʳ w : ι, [R w, A w])) (hC : IsCompact C) :
    ∀ᶠ w : ι in cofinite, ∀ y ∈ C, y w ∈ A w := by
  classical
  let U (T : Finset (ι)) :=
    {y : (Πʳ w : ι, [R w, A w]) | ∀ w, w ∉ T → y w ∈ A w}
  have hU (T : Finset (ι)) : IsOpen (U T) :=
    RestrictedProduct.isOpen_forall_imp_mem hA
  have hcov : C ⊆ ⋃ T, U T := by
    intro y _
    have hy := eventually_cofinite.mp y.eventually
    exact Set.mem_iUnion.mpr ⟨hy.toFinset, fun w hw => by
      simpa only [hy.mem_toFinset, Set.mem_ofPred_eq, not_not] using hw⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩
    · exact fun _ hy w hw => hy w (fun hin => hw (Finset.mem_union_left T hin))
    · exact fun _ hy w hw => hy w (fun hin => hw (Finset.mem_union_right S hin))
  obtain ⟨T, hT⟩ := hC.elim_directed_cover U hU hcov hdir
  filter_upwards [T.eventually_cofinite_notMem] with w hw y hy
  exact hT hy w hw

theorem isCompact_preimage_adelicMap (D : GlobalFieldData.{u, v} K)
    (q : G.val ⟶ Q.val) (hq : IsFinite q.hom.hom.left)
    (i : MatrixRealization G) (j : MatrixRealization Q)
    (C : Set (Adeles D j ∅)) (hC : IsCompact C) :
    IsCompact (adelicMap D q i j ⁻¹' C) := by
  let f := adelicMap D q i j
  letI (w : Outside D ∅) : T2Space (LocalPoints D j w.1) :=
    (localMatrixEmbedding D j w.1).isEmbedding.t2Space
  have hc : IsClosed (f ⁻¹' C) := hC.isClosed.preimage (continuous_adelicMap D q i j)
  let B (w : Outside D ∅) : Set (LocalPoints D i w.1) :=
    pointsMap q i j _ ⁻¹' ((fun y : Adeles D j ∅ => y w) '' C)
  have hB (w : Outside D ∅) : IsCompact (B w) :=
    compact_local_preimage D w.1 q hq i j _ (hC.image (RestrictedProduct.continuous_eval w))
  have hBU : ∀ᶠ w : Outside D ∅ in cofinite, B w ⊆ localSubgroup D i w.1 := by
    have hy := compact_eventually_integral
      (R := fun w : Outside D ∅ => LocalPoints D j w.1)
      (fun w => (localSubgroup D j w.1 : Set (LocalPoints D j w.1)))
      (fun w => localSubgroup_open D j w.1) C hC
    filter_upwards [hy, subgroupPreimage_eventually D q hq i j] with w hw hi g hg
    obtain ⟨y, hy, he⟩ := hg
    exact hi g (he ▸ hw y hy)
  have hbox := AdelicLatticeBounds.compactRestrictedProductBox
    (fun w : Outside D ∅ => (localSubgroup D i w.1 : Set (LocalPoints D i w.1))) B hB hBU
  refine hbox.of_isClosed_subset hc ?_
  intro x hx w
  exact ⟨f x, hx, adelicMap_apply D q i j x w⟩

theorem finiteAdelicMorphism : Specs.FiniteAdelicMorphism.finiteAdelicMorphism.{u, v} := by
  intro K _ h G Q q hq i j
  let D : GlobalFieldData.{u, v} K := .number h
  exact ⟨adelicMap D q i j, adelicMap_apply D q i j, continuous_adelicMap D q i j,
    isCompact_preimage_adelicMap D q hq i j⟩

end LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism
