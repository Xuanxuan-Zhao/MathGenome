import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceReduction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalAuxiliaryTower
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Tactic.Group

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceReduction

open LinearAlgebraicGroups.Specs
open Specs.RamifiedExceptionalFaceReduction
open Specs.RamifiedExceptionalAuxiliaryTower
open Specs.RamifiedExceptionalLocalFaceCoordinates
open CategoryTheory AlgebraicGeometry Opposite IsLocalRing ValuativeRel WithZero
open scoped CategoryTheory.MonObj TensorProduct WithZero Pointwise Classical
open ExceptionalAffineBruhat (FieldPoints LocalComparison FoldedLevel FoldedApartment
  DiagramCompositum RamifiedReference coefficientPoints scalarPoints residue ramifiedPoint)
open ExceptionalAffineBuilding (Building parahoric standardWallSubgroup Weights cotype
  IsBarycenter rationalPoint simplexPoint)
open ExceptionalAffineRootSystems (ApartmentRoots FoldedRootDirection threshold)
open ExceptionalIwahoriCongruence (changeRing changeRingHom integralRingMap integralRing)
open ExceptionalIwahoriImageComparison (residueReduction integralUnitTorus)
open ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open ExceptionalValuedTorusNormalizer (invariantApartment valuationRingInclusion fixedWeylGroup)
open IntegralSemisimpleModel (Model IntegralMarking IntegralGroup IntegralAlgebra IntegralPoints
  Integers integerAlgebra integralPointFunctor integralSpec torusPoint cocharacter TorusValues fibre)
open Pinning (BasedRootDatum BasedIso)
open AdjointRepresentation (GroupPoints)
open ExceptionalMarkedRootDescent (markedWeylWord markedWall)
open RamifiedExceptionalLocalFaceCoordinates (changeRing_injective_of_affine rationalFaceCotype)
open RamifiedExceptionalAuxiliaryTower (uniformizerRootExtension normalizedValuation_surjective)

universe u v

noncomputable section

attribute [local instance] integerAlgebra ExceptionalLocalRootCoordinates.canonicalExtension
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

open private changeRing_comp_apply composeIntegralRingMaps scalarPoints_torus rationalClosedAlcove
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
open private markedTorusPointHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private torusPoint_bijective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private markedWeylWord_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private iwahori_scalar normalizer_torus_word
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedScalarTransport

local notation "Oᵥ[" K "]" => Valuation.valuationSubring (valuation K)
local notation "kᵥ[" K "]" => residue K

/-- A rational cocharacter lies in the localization of the integral
lattice at the positive integers. -/
theorem clearCocharacterDenominators {Y : Type*} [AddCommGroup Y] (x : ℚ ⊗[ℤ] Y) :
    ∃ (d : ℕ) (y : Y), 0 < d ∧ (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y := by
  induction x using TensorProduct.inductionOn with
  | tmul q y =>
    refine ⟨q.den, q.num • y, q.den_pos, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, Rat.mul_den_eq_num,
      ← TensorProduct.smul_tmul (R := ℤ) q.num (1 : ℚ) y]
    simp
  | add x y hx hy =>
    obtain ⟨d, a, hd, ha⟩ := hx
    obtain ⟨e, b, he, hb⟩ := hy
    refine ⟨d * e, e • a + d • b, Nat.mul_pos hd he, ?_⟩
    rw [Nat.cast_mul, smul_add, mul_comm (d : ℚ) (e : ℚ), ← smul_smul, ha,
      mul_comm (e : ℚ) (d : ℚ), ← smul_smul, hb, TensorProduct.tmul_add]
    have h (n : ℕ) (v : Y) : (n : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (n • v) := by
      rw [Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℤ (b := v), TensorProduct.tmul_smul]
      exact (Nat.cast_smul_eq_nsmul ℚ _ _).symm
    rw [h e a, h d b]

theorem ramifiedIwahoriScaling : RamifiedIwahoriScaling.{u} := by
  intro F L k _ _ _ _ _ _ _ _ _ _ _ D M R σ T A X B t x hx π hπ
  have hclosed := rationalClosedAlcove B t x hx
  obtain ⟨d, y, hd, hy⟩ := clearCocharacterDenominators ((2 : ℚ) • x.val)
  have hy' : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y := by
    simpa only [smul_smul, mul_comm] using hy
  let K := T.field
  have hπK : normalizedValuation K (algebraMap L K (π : L)) = exp (-1) :=
    (T.unramified (π : L)).trans hπ
  let U := uniformizerRootExtension d hd (algebraMap L K (π : L)) hπK
  let E := U.field
  let C := X.comparison
  let p : FieldPoints M E :=
    torusPoint D (integralRing E) (cocharacter D y (integralRing E) U.root) ≫ M.torus.hom.hom
  let f : C.I →* FieldPoints M E :=
    (MulAut.conj p).toMonoidHom.comp
      ((scalarPoints M (algebraMap K E)).comp (X.points.comp C.I.subtype))
  let i := ((integralPointFunctor M.group).map (valuationRingInclusion E)).hom
  have hi : Function.Injective i := changeRing_injective_of_affine M.affine _ Subtype.val_injective
  have hInt (g : C.I) : f g ∈ i.range :=
    RamifiedExceptionalLocalFaceCoordinates.scaledFoldedIwahoriPointIntegral X x hclosed
      (algebraMap L K (π : L)) hπK d U.root U.power y hy' g
  let f₀ := f.codRestrict i.range hInt
  let e := MonoidHom.ofInjective hi
  refine ⟨d, y, hd, hy', E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, U.root, U.degree, U.power, U.residue_bijective,
    e.symm.toMonoidHom.comp f₀, ?_⟩
  intro g
  exact congrArg Subtype.val (e.apply_symm_apply (f₀ g))

section StandardFace

variable {K E G H W V : Type u} {B : Type v}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Group G] [Group H] [Group W] [AddCommGroup V] [Module ℚ V]
  {D : BasedRootDatum.{u}} {M : Model D} {j : G →* FieldPoints M K} {j' : H →* FieldPoints M E}
  {A : ApartmentRoots ℚ V B} {p : V}
  (C : LocalComparison (j := j) (Wf := W) A p) (C' : LocalComparison (j := j') (Wf := W) A p)

private theorem sameWallSubgroup (T : Set (A.SimpleWall p)) :
    standardWallSubgroup C.coxeter.coxeter T = standardWallSubgroup C'.coxeter.coxeter T := by
  change Subgroup.closure (C.coxeter.coxeter.simple '' T) =
    Subgroup.closure (C'.coxeter.coxeter.simple '' T)
  simp only [C.coxeter.simple_eq, C'.coxeter.simple_eq]

private theorem unitTorus_le_iwahori : C.T₀ ≤ C.I := by
  change (integralUnitTorus M).comap j ≤ _
  rw [← C.localIwahori.intersection]
  exact inf_le_left

/-- Membership in a standard marked face is reflected by a comparison of
the Iwahoris and of every ordinary affine normalizer label. -/
theorem parahoric_comap (X : Building C) (Y : Building C') {q q' : ℕ} (hB : C.Bruhat q)
    (hB' : C'.Bruhat q') (hG : C.G₀ = ⊤) (s : G →* H) (T : Set (A.SimpleWall p))
    (hI : C'.I.comap s = C.I)
    (hLift : ∀ w, s (C.lift w : G) * (C'.lift w : H)⁻¹ ∈ C'.T₀) :
    (parahoric C' T).comap s = parahoric C T := by
  have hmap (w : A.affineWeylGroup) :
      Set.MapsTo s (C.cell w) (C'.cell w) := by
    intro g hg
    obtain ⟨a, ha, b, hb, he⟩ := DoubleCoset.mem_doubleCoset.mp hg
    have hi (x : G) (hx : x ∈ C.I) : s x ∈ C'.I := by
      change x ∈ C'.I.comap s
      rwa [hI]
    let z := s (C.lift w : G) * (C'.lift w : H)⁻¹
    have hz : z ∈ C'.I := unitTorus_le_iwahori C' (hLift w)
    refine DoubleCoset.mem_doubleCoset.mpr ⟨s a * z, C'.I.mul_mem (hi a ha) hz, s b, hi b hb, ?_⟩
    rw [he, map_mul, map_mul]
    dsimp [z]
    group
  apply le_antisymm
  · intro g hg
    change s g ∈ (parahoric C' T : Set H) at hg
    rw [Y.realization.face_union] at hg
    obtain ⟨w', hw'⟩ := Set.mem_iUnion.mp hg
    have hg₀ : g ∈ ⋃ w, C.cell w := by rw [hB.cover, hG]; exact Subgroup.mem_top _
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg₀
    have hw₀ : w = w'.val := by
      by_contra hne
      exact Set.disjoint_left.mp (hB'.disjoint hne) (hmap w hw) hw'
    have hwT : w ∈ standardWallSubgroup C.coxeter.coxeter T := by
      rw [sameWallSubgroup C C', hw₀]
      exact w'.property
    change g ∈ (parahoric C T : Set G)
    rw [X.realization.face_union]
    exact Set.mem_iUnion.mpr ⟨⟨w, hwT⟩, hw⟩
  · intro g hg
    change g ∈ (parahoric C T : Set G) at hg
    rw [X.realization.face_union] at hg
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
    have hwT : w.val ∈ standardWallSubgroup C'.coxeter.coxeter T := by
      rw [← sameWallSubgroup C C']
      exact w.property
    change s g ∈ (parahoric C' T : Set H)
    rw [Y.realization.face_union]
    exact Set.mem_iUnion.mpr ⟨⟨w, hwT⟩, hmap w.val hw⟩

private theorem rationalPoint_injective (r : ExceptionalAffineBuilding.RealCoordinates V) :
    Function.Injective (rationalPoint r) := by
  intro a b h
  exact (Module.FaithfullyFlat.tensorProduct_mk_injective (A := ℚ) (B := ℝ) V) (r.injective h)

/-- A fixed standard barycenter has the same rational apartment coordinates
in any realization of the marked comparison. -/
theorem standardBarycenter_natural (X : Building C) (Y : Building C')
    (t : Weights (A.SimpleWall p)) (x : V) (ht : IsBarycenter (cotype t) t)
    (hx : rationalPoint X.realization.coordinates x =
      simplexPoint X.realization.coordinates X.realization.vertex t) :
    rationalPoint Y.realization.coordinates x =
      simplexPoint Y.realization.coordinates Y.realization.vertex t := by
  classical
  let _ : Finite (A.SimpleWall p) := X.realization.finite_types
  let _ := Fintype.ofFinite (A.SimpleWall p)
  let c (i : A.SimpleWall p) : ℚ :=
    if i ∈ cotype t then 0 else 1 / (Nat.card {i // i ∉ cotype t} : ℚ)
  have hc (i : A.SimpleWall p) : (c i : ℝ) = t.val i := by
    rw [ht i]
    by_cases hi : i ∈ cotype t <;> simp [c, hi]
  have hsum (r : ExceptionalAffineBuilding.RealCoordinates V) (z : A.SimpleWall p → V) :
      rationalPoint r (∑ i, c i • z i) = simplexPoint r z t := by
    simp only [ExceptionalRealAlcove.rationalPoint, ExceptionalRealAlcove.simplexPoint,
      finsum_eq_sum_of_fintype, TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hc i, ← map_smul, TensorProduct.tmul_smul]
    rfl
  have hv : X.realization.vertex = Y.realization.vertex := by
    funext a
    exact Y.realization.vertex_unique a _ (X.realization.vertex_marked a)
  have he := rationalPoint_injective X.realization.coordinates (hx.trans (hsum _ _).symm)
  rw [he, hv]
  exact hsum _ _

end StandardFace

section Normalizer

open ExceptionalMarkedRootDescent (markedRootPoint orderedRootPoint markedCellPoint weylWordPerm)
open IntegralSemisimpleModel (splitTorus)
open private rootOrderings_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private markedRootPoint_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private weylWord_index from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates

variable {D : BasedRootDatum.{u}} {M : Model D}

private theorem orderedRootPoint_single (R : IntegralAlgebra.{u}) (a : D.I) (z : R)
    (l : List D.I) (hl : l.Nodup) :
    orderedRootPoint M.toIntegralMarking R l (Function.update (fun _ : D.I => (0 : R)) a z) =
      if a ∈ l then markedRootPoint M.toIntegralMarking R a z else 1 := by
  classical
  induction l with
  | nil => simp [orderedRootPoint]
  | cons b l ih =>
    obtain ⟨hb, hnd⟩ := List.nodup_cons.mp hl
    change markedRootPoint M.toIntegralMarking R b (Function.update (fun _ : D.I => (0 : R)) a z b) *
      orderedRootPoint M.toIntegralMarking R l (Function.update (fun _ : D.I => (0 : R)) a z) = _
    rw [ih hnd]
    by_cases he : b = a
    · subst b
      simp [hb]
    · simp [he, Ne.symm he, markedRootPoint_zero]

private theorem markedRootPoint_index (R : IntegralAlgebra.{u}) {i j : D.I} {x y : R}
    (hx : x ≠ 0) (he : markedRootPoint M.toIntegralMarking R i x =
      markedRootPoint M.toIntegralMarking R j y) : i = j := by
  classical
  obtain ⟨neg, pos, hn, hp⟩ := rootOrderings_exist D
  let T : IntegralPoints (splitTorus D) R := 1
  have heval (a : D.I) (z : R) :
      markedCellPoint M.toIntegralMarking R neg pos (Function.update (fun _ : D.I => (0 : R)) a z) T =
        markedRootPoint M.toIntegralMarking R a z := by
    rw [markedCellPoint, orderedRootPoint_single R a z neg hn.1,
      orderedRootPoint_single R a z pos hp.1]
    have hT : T ≫ M.torus.hom.hom = (1 : IntegralPoints M.group R) := MonObj.one_comp _
    rw [hT]
    by_cases hpos : D.base.IsPos a
    · have hn' : a ∉ neg := fun h => ((hn.2 a).mp h) hpos
      have hp' : a ∈ pos := (hp.2 a).mpr hpos
      rw [ite_eq_right hn', ite_eq_left hp', one_mul, one_mul]
    · have hn' : a ∈ neg := (hn.2 a).mpr hpos
      have hp' : a ∉ pos := fun h => hpos ((hp.2 a).mp h)
      rw [ite_eq_left hn', ite_eq_right hp', one_mul, mul_one]
  let f := Function.update (fun _ : D.I => (0 : R)) i x
  let g := Function.update (fun _ : D.I => (0 : R)) j y
  have h : (f, T) = (g, T) :=
    (ExceptionalMarkedRootDescent.markedCellCoordinates M.toIntegralMarking R neg pos hn hp).1
      ((heval i x).trans (he.trans (heval j y).symm))
  have hi : f i = g i := congrFun (congrArg Prod.fst h) i
  by_contra hne
  exact hx (by simpa only [f, g, Function.update_self, Function.update_of_ne hne] using hi)

private theorem wordLabel_eq_of_torusWord_eq {K : Type u} [Field K]
    (had : D.datum.rootSpan ℤ = ⊤) (l m : List D.I) (t v : TorusValues D (integralRing K))
    (h : (torusPoint D _ t ≫ M.torus.hom.hom : FieldPoints M K) *
        markedWeylWord M.toIntegralMarking (integralRing K) l =
      (torusPoint D _ v ≫ M.torus.hom.hom : FieldPoints M K) *
        markedWeylWord M.toIntegralMarking (integralRing K) m) :
    (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod =
      (m.map (RootPairing.weylGroup.ofIdx D.datum)).prod := by
  let R := integralRing K
  let w (l : List D.I) := (l.map (RootPairing.weylGroup.ofIdx D.datum)).prod
  have eqIndex (i : D.I) : weylWordPerm l i = weylWordPerm m i := by
    have conj (l : List D.I) (t : TorusValues D R) :
        ∃ z : K, z ≠ 0 ∧
          MulAut.conj ((torusPoint D R t ≫ M.torus.hom.hom : FieldPoints M K) *
            markedWeylWord M.toIntegralMarking R l) (markedRootPoint M.toIntegralMarking R i 1) =
            markedRootPoint M.toIntegralMarking R (weylWordPerm l i) z := by
      obtain ⟨c, hc⟩ := ExceptionalMarkedRootDescent.integralWeylWordTransport M l i
      let z : K := (t (Multiplicative.ofAdd (D.datum.root (weylWordPerm l i))) : K) *
        algebraMap Integers.{u} K (c : Integers.{u})
      refine ⟨z, mul_ne_zero (Units.ne_zero _) ((c.isUnit.map (algebraMap Integers.{u} K)).ne_zero), ?_⟩
      rw [map_mul, MulAut.mul_apply]
      simp only [MulAut.conj_apply]
      rw [hc R 1, mul_one]
      exact M.conjugation R t _ _
    obtain ⟨a, ha, h₁⟩ := conj l t
    obtain ⟨b, _, h₂⟩ := conj m v
    rw [h] at h₁
    exact markedRootPoint_index R ha (h₁.symm.trans h₂)
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective D.datum
  let b : Module.Basis D.base.support ℤ D.X :=
    Module.Basis.mk D.base.linearIndepOn_root (by
      change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
      rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support]
      exact had.ge)
  apply LinearEquiv.toLinearMap_inj.mp
  apply b.ext
  intro i
  change (w l).val.weightEquiv (b i) = (w m).val.weightEquiv (b i)
  have hb : b i = D.datum.root i.val := Module.Basis.mk_apply _ _ _
  rw [hb]
  calc
    _ = D.datum.root ((w l).val.indexEquiv i.val) :=
      RootPairing.Hom.root_weightMap_apply D.datum D.datum i.val (w l).val.toHom
    _ = D.datum.root ((w m).val.indexEquiv i.val) :=
      congrArg D.datum.root (by simpa only [weylWord_index] using eqIndex i.val)
    _ = _ := (RootPairing.Hom.root_weightMap_apply D.datum D.datum i.val (w m).val.toHom).symm

private theorem logs_eq_of_torusWord_eq {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (l m : List D.I) (t v : TorusValues D (integralRing K))
    (h : (torusPoint D _ t ≫ M.torus.hom.hom : FieldPoints M K) *
        markedWeylWord M.toIntegralMarking (integralRing K) l =
      (torusPoint D _ v ≫ M.torus.hom.hom : FieldPoints M K) *
        markedWeylWord M.toIntegralMarking (integralRing K) m) :
    ∀ χ, WithZero.log (normalizedValuation K (t (Multiplicative.ofAdd χ) : K)) =
      WithZero.log (normalizedValuation K (v (Multiplicative.ofAdd χ) : K)) := by
  let R := integralRing K
  let g : TorusValues D R →* FieldPoints M K :=
    markedTorusPointHom M.toIntegralMarking R
  change g t * _ = g v * _ at h
  let q := t⁻¹ * v
  have hw : (torusPoint D R q ≫ M.torus.hom.hom : FieldPoints M K) =
      markedWeylWord M.toIntegralMarking R l * (markedWeylWord M.toIntegralMarking R m)⁻¹ := by
    change g q = _
    let h₀ := markedWeylWord M.toIntegralMarking R l
    let h₁ := markedWeylWord M.toIntegralMarking R m
    change g t * h₀ = g v * h₁ at h
    change g (t⁻¹ * v) = h₀ * h₁⁻¹
    have hg : g (t⁻¹ * v) = (g t)⁻¹ * g v :=
      (map_mul g t⁻¹ v).trans (congrArg (fun z => z * g v) (map_inv g t))
    rw [hg]
    calc
      _ = (g t)⁻¹ * (g v * h₁) * h₁⁻¹ := by group
      _ = _ := by rw [← h]; group
  letI := D.freeY
  letI := D.finiteY
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ D.Y) := Fintype.ofFinite _
  let B := Module.Free.chooseBasis ℤ D.Y
  have hunit := (ExceptionalValuedTorusNormalizer.markedIntegralTorusKernel D M.toIntegralMarking B q).mpr
    ⟨markedWeylWord M.toIntegralMarking (integralRing Oᵥ[K]) l *
      (markedWeylWord M.toIntegralMarking (integralRing Oᵥ[K]) m)⁻¹, by
        change changeRingHom M.group (valuationRingInclusion K) (_ * _⁻¹) = _
        rw [hw, map_mul, map_inv]
        exact congrArg₂ (fun a b : FieldPoints M K => a * b⁻¹)
          (markedWeylWord_map M.toIntegralMarking (valuationRingInclusion K) l)
          (markedWeylWord_map M.toIntegralMarking (valuationRingInclusion K) m)⟩
  obtain ⟨s, hs⟩ := (ExceptionalValuedTorusNormalizer.integralTorusCoordinates D B q).mp hunit
  intro χ
  have hq : normalizedValuation K (q (Multiplicative.ofAdd χ) : K) = 1 := by
    rw [← hs]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
      (valuation K ((s (Multiplicative.ofAdd χ) : Oᵥ[K]) : K)) = 1
    have hval : valuation K ((s (Multiplicative.ofAdd χ) : Oᵥ[K]) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).valuation_unit (s (Multiplicative.ofAdd χ))
    rw [hval, map_one]
  have hv : normalizedValuation K (t (Multiplicative.ofAdd χ) : K) =
      normalizedValuation K (v (Multiplicative.ofAdd χ) : K) := by
    have he := congrArg (normalizedValuation K) (show
        (t (Multiplicative.ofAdd χ) : K) * (q (Multiplicative.ofAdd χ) : K) =
          (v (Multiplicative.ofAdd χ) : K) by simp [q])
    simpa only [map_mul, hq, mul_one] using he
  exact congrArg WithZero.log hv

end Normalizer
section CoefficientLevels

open ExceptionalAffineBruhat (LocalComparison)
open RamifiedExceptionalLocalFaceCoordinates (integralPointsInField reduceIntegralPoints)

variable {F L k k' : Type u} [Field F] [Field L] [Field k] [Field k'] [Algebra F L]
  [Algebra F k] [Algebra F k'] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  (X : MarkedLevel R σ A k) (Y : MarkedLevel R σ A k')

private theorem coefficientPoints_split (f : k →ₐ[F] k')
    (e : X.compositum.field →ₐ[F] Y.compositum.field)
    (hL : ∀ z : L, e (algebraMap L X.compositum.field z) = algebraMap L Y.compositum.field z)
    (hk : ∀ z : k, e (algebraMap k X.compositum.field z) = algebraMap k' Y.compositum.field (f z))
    (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    Y.folded.points (coefficientPoints R.descent.group.val f g) =
      scalarPoints M e.toRingHom (X.folded.points g) := by
  rw [Y.folded.point_eq, X.folded.point_eq]
  symm
  exact ExceptionalAffineBruhat.ramifiedPoint_natural R
    (IsScalarTower.toAlgHom F L X.compositum.field)
    (IsScalarTower.toAlgHom F k X.compositum.field)
    (IsScalarTower.toAlgHom F L Y.compositum.field)
    (IsScalarTower.toAlgHom F k' Y.compositum.field) f e
    (AlgHom.ext hL) (AlgHom.ext hk) g

private theorem normalizedValuation_eq_one_of_unit {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (b : Oᵥ[K]ˣ) :
    normalizedValuation K (((b : Oᵥ[K]) : K)) = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  change e (valuation K (((b : Oᵥ[K]) : K))) = 1
  exact ((congrArg e ((Valuation.integer.integers (valuation K)).valuation_unit b))).trans (map_one e)

private theorem normalizedValuation_map_of_uniformizer {K E : Type u} [Field K] [Field E]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    {f : K →+* E} (v : Specs.RamifiedExceptionalAuxiliaryTower.ValuedFieldMap f)
    (π : K) (hπ : normalizedValuation K π = exp (-1))
    (hπ' : normalizedValuation E (f π) = exp (-1)) (z : K) :
    normalizedValuation E (f z) = normalizedValuation K z := by
  by_cases hz : z = 0
  · simp [hz]
  have hπne : π ≠ 0 := by
    intro he
    rw [he, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hu (a : K) (ha : normalizedValuation K a = 1) : normalizedValuation E (f a) = 1 := by
    have hi : valuation K a = 1 := by
      apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
      exact ha.trans (map_one _).symm
    let a₀ : Oᵥ[K] := ⟨a, hi.le⟩
    have hb₀ : IsUnit a₀ := (Valuation.integer.integers (valuation K)).isUnit_of_one' hi
    let b := hb₀.unit
    have hcoe : (b : Oᵥ[K]) = a₀ := hb₀.unit_spec
    have hb := normalizedValuation_eq_one_of_unit (Units.map v.integers.toMonoidHom b)
    change normalizedValuation E (↑(v.integers (b : Oᵥ[K])) : E) = 1 at hb
    rw [v.field_eq, hcoe] at hb
    exact hb
  let n := WithZero.log (normalizedValuation K z)
  have h₁ : exp n = normalizedValuation K z :=
    WithZero.exp_log ((map_ne_zero (normalizedValuation K)).2 hz)
  have hpow (m : ℤ) : exp (-1 : ℤ) ^ m = exp (-m) := by
    rw [← exp_zsmul]
    congr 1
    simp
  have hzπ : normalizedValuation K (z * π ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hpow, ← h₁, ← exp_add, add_neg_cancel, exp_zero]
  have hproduct : z * π ^ n * π ^ (-n) = z := by
    rw [mul_assoc, ← zpow_add₀ hπne, add_neg_cancel, zpow_zero, mul_one]
  suffices normalizedValuation E (f (z * π ^ n * π ^ (-n))) = normalizedValuation K z by
    rwa [hproduct] at this
  rw [map_mul f, map_mul, hu _ hzπ, map_zpow₀ f, map_zpow₀, hπ', hpow, neg_neg, one_mul, h₁]

private theorem scalarPoints_comp_apply {K E N : Type u} [Field K] [Field E] [Field N]
    (f : K →+* E) (g : E →+* N) (b : FieldPoints M K) :
    scalarPoints M g (scalarPoints M f b) = scalarPoints M (g.comp f) b := by
  rw [show scalarPoints M g (scalarPoints M f b) =
      changeRingHom M.group (integralRingMap f ≫ integralRingMap g) b from
    changeRing_comp_apply M.group _ _ _, composeIntegralRingMaps]

private theorem affine_label_preserved
    (had : D.datum.rootSpan ℤ = ⊤) (f : k →ₐ[F] k')
    (e : X.compositum.field →ₐ[F] Y.compositum.field)
    (he : ∀ a, normalizedValuation Y.compositum.field (e a) =
      normalizedValuation X.compositum.field a)
    (hL : ∀ z : L, e (algebraMap L X.compositum.field z) = algebraMap L Y.compositum.field z)
    (hk : ∀ z : k, e (algebraMap k X.compositum.field z) = algebraMap k' Y.compositum.field (f z))
    (n : X.folded.comparison.N) (n' : Y.folded.comparison.N)
    (hn' : n'.val = coefficientPoints R.descent.group.val f n.val) :
    Y.folded.comparison.affine n' = X.folded.comparison.affine n := by
  let N := X.folded.comparison.localIwahori.normalizer
  let N' := Y.folded.comparison.localIwahori.normalizer
  let l := N.word (N.label n)
  let m := N'.word (N'.label n')
  obtain ⟨s, hs, hsn⟩ := normalizer_torus_word N n
  obtain ⟨t, ht, htn⟩ := normalizer_torus_word N' n'
  let s' : TorusValues D (integralRing Y.compositum.field) := (Units.map e.toRingHom).comp s
  have hp : Y.folded.points n'.val =
      (torusPoint D _ s' ≫ M.torus.hom.hom : FieldPoints M Y.compositum.field) *
        markedWeylWord M.toIntegralMarking (integralRing Y.compositum.field) l := by
    rw [hn', coefficientPoints_split X Y f e hL hk, hsn, map_mul, scalarPoints_torus]
    exact congrArg (_ * ·) (markedWeylWord_map M.toIntegralMarking (integralRingMap e.toRingHom) l)
  have hp' : Y.folded.points n'.val =
      (torusPoint D _ t ≫ M.torus.hom.hom : FieldPoints M Y.compositum.field) *
        markedWeylWord M.toIntegralMarking (integralRing Y.compositum.field) m := htn
  have hword := wordLabel_eq_of_torusWord_eq (M := M) had l m s' t (hp.symm.trans hp')
  have hlabel : N.label n = N'.label n' := by
    apply Subtype.ext
    exact (X.folded.finite_labels.2.choose_spec.2 _).symm.trans
      (hword.trans (Y.folded.finite_labels.2.choose_spec.2 _))
  have hlogs := logs_eq_of_torusWord_eq (M := M) l m s' t (hp.symm.trans hp')
  have hnν : (N'.translation (N'.torusPart n')).toAdd = (N.translation (N.torusPart n)).toAdd := by
    apply D.datum.toLinearMap.flip.toPerfPair.injective
    ext χ
    change D.datum.toLinearMap χ (N'.translation (N'.torusPart n')).toAdd =
      D.datum.toLinearMap χ (N.translation (N.torusPart n)).toAdd
    rw [N'.characterLog _ _ ht, N.characterLog _ _ hs]
    change WithZero.log (normalizedValuation Y.compositum.field ↑(t (Multiplicative.ofAdd χ))) =
      WithZero.log (normalizedValuation X.compositum.field ↑(s (Multiplicative.ofAdd χ)))
    exact (hlogs χ).symm.trans (congrArg WithZero.log (he _))
  apply AffineEquiv.ext
  intro x
  apply Subtype.ext
  rw [Y.folded.affine, X.folded.affine]
  change (N'.label n').val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
      ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N'.translation (N'.torusPart n')).toAdd) =
    (N.label n).val.val.coweightEquiv.symm.baseChange ℤ ℚ D.Y D.Y x.val +
      ((1 / 2 : ℚ) ⊗ₜ[ℤ] (N.translation (N.torusPart n)).toAdd)
  rw [hlabel, hnν]

private theorem normalizer_mem_scalar (f : k →ₐ[F] k')
    (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    coefficientPoints R.descent.group.val f g ∈ Y.folded.comparison.N ↔ g ∈ X.folded.comparison.N := by
  rw [X.folded.normalizer_torus, Y.folded.normalizer_torus]
  exact (ExceptionalValuedScalarTransport.torusConditionsScalar R.descent.group.val
    R.descent.torus f g).1

end CoefficientLevels

section ScaledTower

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  (X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field)
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}

variable (U : AuxiliaryTower (fun k => (X k).compositum) d (π : L))

abbrev StageScaling (k : UnramifiedLevel F S) :=
  ScaledParahoric (X k) J π d y (localAuxiliary (U.extension k))

include U in
private theorem coefficientComparison (had : D.datum.rootSpan ℤ = ⊤)
    (hπ : normalizedValuation L (π : L) = exp (-1))
    {k k' : UnramifiedLevel F S} (h : k ≤ k') :
    let s := coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)
    let C := (X k).folded.comparison
    let C' := (X k').folded.comparison
    C'.I.comap s = C.I ∧
      (∀ w : A.roots.affineWeylGroup, s (C.lift w).val * (C'.lift w).val⁻¹ ∈ C'.T₀) ∧
      ((X k').parahoric J).comap s = (X k).parahoric J := by
  intro s C C'
  let e := U.transition h
  have hπ₀ : normalizedValuation (X k).compositum.field (algebraMap L _ (π : L)) = exp (-1) :=
    ((X k).compositum.unramified _).trans hπ
  have hπ₁ : normalizedValuation (X k').compositum.field
      (e.diagram (algebraMap L _ (π : L))) = exp (-1) :=
    (congrArg (normalizedValuation (X k').compositum.field) (e.diagram_left _)).trans
      (((X k').compositum.unramified _).trans hπ)
  have he := normalizedValuation_map_of_uniformizer e.diagramValued _ hπ₀ hπ₁
  have hs := coefficientPoints_split (X k) (X k') (UnramifiedLevel.inclusion h)
    e.diagram e.diagram_left e.diagram_right
  have hI : C'.I.comap s = C.I :=
    iwahori_scalar C.localIwahori C'.localIwahori e.diagram.toRingHom s he hs
  have hLift (w : A.roots.affineWeylGroup) : s (C.lift w).val * (C'.lift w).val⁻¹ ∈ C'.T₀ := by
    let n := C.lift w
    let n' : C'.N := ⟨s n.val, (normalizer_mem_scalar (X k) (X k') _ n.val).2 n.property⟩
    have hlabel : C'.affine n' = C.affine n :=
      affine_label_preserved (X k) (X k') had _ e.diagram he e.diagram_left e.diagram_right n n' rfl
    have hword : C'.affine n' = C'.affine (C'.lift w) :=
      hlabel.trans ((C.lift_label w).trans (C'.lift_label w).symm)
    exact ExceptionalAffineBruhat.sameLabel_div_mem_unitTorus C' (n := n') (m := C'.lift w) hword
  exact ⟨hI, hLift, parahoric_comap C C' (X k).building (X k').building
    (X k).folded.bruhat (X k').folded.bruhat
    (ExceptionalAffineBruhat.ordinaryRange_generates C (X k).folded.range) s J hI hLift⟩

private theorem scale_integral_compare
    (p : ∀ k, StageScaling (J := J) (y := y) X U k)
    {k k' : UnramifiedLevel F S} (h : k ≤ k')
    (hface : ((X k').parahoric J).comap
      (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)) = (X k).parahoric J)
    (g : (X k).parahoric J) :
    (p k').integral (faceInclusion X h J hface g) =
      changeRingHom M.group (integralRingMap (U.transition h).valued.integers) ((p k).integral g) := by
  let e := U.transition h
  let E := (U.extension k).field
  let E' := (U.extension k').field
  let i := valuationRingInclusion E
  let i' := valuationRingInclusion E'
  let r : integralRing Oᵥ[E] ⟶ integralRing Oᵥ[E'] := integralRingMap e.valued.integers
  let a : integralRing E ⟶ integralRing E' := integralRingMap e.auxiliary
  have hr : r ≫ i' = i ≫ a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    exact e.valued.field_eq z
  let p₀ : IntegralPoints M.group (integralRing Oᵥ[E]) := (p k).integral g
  let p₁ : IntegralPoints M.group (integralRing Oᵥ[E']) :=
    (p k').integral (faceInclusion X h J hface g)
  apply changeRing_injective_of_affine M.affine i' Subtype.val_injective
  change changeRingHom M.group i' p₁ =
    changeRingHom M.group i' (changeRingHom M.group r p₀)
  have hcomp : changeRingHom M.group i' (changeRingHom M.group r p₀) =
      changeRingHom M.group a (changeRingHom M.group i p₀) :=
    (changeRing_comp_apply M.group r i' p₀).trans
      ((congrArg (fun b => changeRingHom M.group b p₀) hr).trans
        (changeRing_comp_apply M.group i a p₀).symm)
  rw [hcomp]
  have hc₀ : changeRingHom M.group i p₀ =
      scalingConjugation (X k) π d y (localAuxiliary (U.extension k)) g.val :=
    DFunLike.congr_fun (p k).conjugation g
  have hc₁ : changeRingHom M.group i' p₁ =
      scalingConjugation (X k') π d y (localAuxiliary (U.extension k'))
        ((faceInclusion X h J hface g).val) :=
    DFunLike.congr_fun (p k').conjugation (faceInclusion X h J hface g)
  rw [hc₀, hc₁]
  let t : FieldPoints M E :=
    torusPoint D (integralRing E) (cocharacter D y (integralRing E) (U.extension k).root) ≫ M.torus.hom.hom
  let t' : FieldPoints M E' :=
    torusPoint D (integralRing E') (cocharacter D y (integralRing E') (U.extension k').root) ≫ M.torus.hom.hom
  have ht : scalarPoints M e.auxiliary t = t' := by
    change scalarPoints M e.auxiliary (torusPoint D _ _ ≫ M.torus.hom.hom) = _
    rw [scalarPoints_torus]
    apply congrArg (fun v => torusPoint D (integralRing E') v ≫ M.torus.hom.hom)
    apply MonoidHom.ext
    intro χ
    let m := D.datum.toLinearMap χ.toAdd y
    change Units.map e.auxiliary.toMonoidHom ((U.extension k).root ^ m) =
      (U.extension k').root ^ m
    have hroot : Units.map e.auxiliary.toMonoidHom (U.extension k).root =
        (U.extension k').root := Units.ext e.auxiliary_root
    rw [map_zpow, hroot]
  let f := UnramifiedLevel.inclusion h
  change MulAut.conj t' (scalarPoints M (algebraMap (X k').compositum.field E')
      ((X k').folded.points (coefficientPoints R.descent.group.val f g.val))) =
    scalarPoints M e.auxiliary (MulAut.conj t (scalarPoints M (algebraMap (X k).compositum.field E)
      ((X k).folded.points g.val)))
  rw [coefficientPoints_split (X k) (X k') f e.diagram e.diagram_left e.diagram_right]
  simp only [MulAut.conj_apply, map_mul, map_inv, ht, scalarPoints_comp_apply]
  rw [show (algebraMap (X k').compositum.field E').comp e.diagram.toRingHom =
      e.auxiliary.comp (algebraMap (X k).compositum.field E) from RingHom.ext (fun z =>
    (e.auxiliary_diagram z).symm)]
  exact congrArg (fun g : FieldPoints M E' => t' * g * t'⁻¹)
    (scalarPoints_comp_apply (algebraMap (X k).compositum.field E) e.auxiliary
      ((X k).folded.points g.val)).symm

private theorem scale_reduction_compare
    (p : ∀ k, StageScaling (J := J) (y := y) X U k)
    {k k' : UnramifiedLevel F S} (h : k ≤ k')
    (hface : ((X k').parahoric J).comap
      (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)) = (X k).parahoric J)
    (g : (X k).parahoric J) :
    (p k').reduction (faceInclusion X h J hface g) =
      scalarPoints M (U.transition h).valued.residue ((p k).reduction g) := by
  let e := (U.transition h).valued
  let E := (U.extension k).field
  let E' := (U.extension k').field
  let z : IntegralPoints M.group (integralRing Oᵥ[E]) := (p k).integral g
  let z' : IntegralPoints M.group (integralRing Oᵥ[E']) :=
    (p k').integral (faceInclusion X h J hface g)
  let r : integralRing Oᵥ[E] ⟶ integralRing Oᵥ[E'] := integralRingMap e.integers
  let ρ := residueReduction E
  let ρ' := residueReduction E'
  let s : integralRing kᵥ[E] ⟶ integralRing kᵥ[E'] := integralRingMap e.residue
  have hz : z' = changeRingHom M.group r z :=
    scale_integral_compare X U p h hface g
  have hr : r ≫ ρ' = ρ ≫ s := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    exact (IsLocalRing.ResidueField.map_residue e.integers a).symm
  change changeRingHom M.group ρ' z' =
    changeRingHom M.group s (changeRingHom M.group ρ z)
  rw [hz, changeRing_comp_apply M.group r ρ', hr, ← changeRing_comp_apply M.group ρ s]

/-- The integral point maps obtained at the separate levels form a single
scaled tower for the actual standard face. -/
def scaledTowerOfLocalScaling
    (had : D.datum.rootSpan ℤ = ⊤) (hπ : normalizedValuation L (π : L) = exp (-1))
    (p : ∀ k, StageScaling (J := J) (y := y) X U k) : ScaledParahoricTower X J π d y where
  auxiliary := U
  auxiliary_valued := RamifiedExceptionalAuxiliaryTower.ramifiedAuxiliaryValuedCompatibility U
  scale := p
  iwahori_comap h := (coefficientComparison (J := J) X U had hπ h).1
  lift_compare h := (coefficientComparison (J := J) X U had hπ h).2.1
  face_comap h := (coefficientComparison (J := J) X U had hπ h).2.2
  integral_compare h := scale_integral_compare X U p h _
  reduction_compare h := scale_reduction_compare X U p h _

end ScaledTower

section GeometricGroups

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  (P : ScaledParahoricTower X J π d y)

private abbrev geometricPoints := FieldPoints M (AlgebraicClosure kᵥ[F])

private theorem geometricReduction_natural {k k' : UnramifiedLevel F S} (h : k ≤ k')
    (g : (X k).parahoric J) :
    P.geometricReduction k' (faceInclusion X h J (P.face_comap h) g) = P.geometricReduction k g := by
  change scalarPoints M (P.auxiliary.residueEmbedding k')
      ((P.scale k').reduction (faceInclusion X h J (P.face_comap h) g)) = _
  rw [P.reduction_compare, scalarPoints_comp_apply, P.auxiliary.residue_compatible h]
  rfl

private theorem mem_geometricImage
    (U : ∀ k : UnramifiedLevel F S,
      Set (GroupPoints R.descent.group.val (CommAlgCat.of F k.field)))
    (v : geometricPoints (F := F) (M := M)) :
    v ∈ P.geometricImage U ↔
      ∃ (k : UnramifiedLevel F S) (g : (X k).parahoric J),
        g.val ∈ U k ∧ P.geometricReduction k g = v := by
  rw [ScaledParahoricTower.geometricImage, Set.mem_iUnion]
  rfl

private theorem mem_parahoricImage (v : geometricPoints (F := F) (M := M)) :
    v ∈ P.parahoricImage ↔ ∃ (k : UnramifiedLevel F S) (g : (X k).parahoric J),
      P.geometricReduction k g = v := by
  rw [mem_geometricImage]
  simp

private theorem geometricReduction_mem (k : UnramifiedLevel F S) (g : (X k).parahoric J) :
    P.geometricReduction k g ∈ P.parahoricImage :=
  (mem_parahoricImage P _).2 ⟨k, g, rfl⟩

/-- All geometric points in the scaled image can be lifted at one common
coefficient stage whenever only finitely many of them are specified. -/
theorem liftFiniteGeometricPoints {Index : Type u} [Finite Index]
    (v : Index → geometricPoints (F := F) (M := M)) (hv : ∀ i, v i ∈ P.parahoricImage) :
    ∃ (k : UnramifiedLevel F S) (g : Index → (X k).parahoric J),
      ∀ i, P.geometricReduction k (g i) = v i := by
  classical
  choose k g hg using fun i => (mem_parahoricImage P _).1 (hv i)
  have hb (s : Finset Index) : ∃ l : UnramifiedLevel F S, ∀ i ∈ s, k i ≤ l := by
    induction s using Finset.induction_on with
    | empty => exact ⟨P.auxiliary.base, by simp⟩
    | insert i s hi ih =>
      obtain ⟨l, hl⟩ := ih
      obtain ⟨m, him, hlm⟩ := P.auxiliary.directed (k i) l
      refine ⟨m, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact him
      · exact (hl j hj).trans hlm
  let _ := Fintype.ofFinite Index
  obtain ⟨l, hl⟩ := hb Finset.univ
  let h (i : Index) := hl i (Finset.mem_univ i)
  exact ⟨l, fun i => faceInclusion X (h i) J (P.face_comap (h i)) (g i),
    fun i => (geometricReduction_natural P (h i) (g i)).trans (hg i)⟩

/-- The directed geometric image of the actual parahorics is a group. -/
def geometricParahoricSubgroup : Subgroup (geometricPoints (F := F) (M := M)) where
  carrier := P.parahoricImage
  one_mem' := (mem_parahoricImage P _).2 ⟨P.auxiliary.base, 1, map_one _⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨k, g, rfl⟩ := (mem_parahoricImage P a).1 ha
    obtain ⟨l, g', rfl⟩ := (mem_parahoricImage P b).1 hb
    obtain ⟨m, h, h'⟩ := P.auxiliary.directed k l
    refine (mem_parahoricImage P _).2 ⟨m, faceInclusion X h J (P.face_comap h) g *
      faceInclusion X h' J (P.face_comap h') g', ?_⟩
    rw [map_mul, geometricReduction_natural P h, geometricReduction_natural P h']
  inv_mem' := by
    intro a ha
    obtain ⟨k, g, rfl⟩ := (mem_parahoricImage P a).1 ha
    exact (mem_parahoricImage P _).2 ⟨k, g⁻¹, map_inv _ _⟩

private theorem geometricImage_subset_face
    (U : ∀ k : UnramifiedLevel F S,
      Set (GroupPoints R.descent.group.val (CommAlgCat.of F k.field))) :
    P.geometricImage U ⊆ P.parahoricImage := by
  intro v hv
  obtain ⟨k, g, _, rfl⟩ := (mem_geometricImage P U v).1 hv
  exact geometricReduction_mem P k g

private theorem iwahori_le_face (k : UnramifiedLevel F S) :
    (X k).folded.comparison.I ≤ (X k).parahoric J :=
  fun _ h => Subgroup.subset_closure (Or.inl h)

private theorem lift_mem_face (k : UnramifiedLevel F S) (w : faceWeylGroup X (k := k) J) :
    ((X k).folded.comparison.lift w.val).val ∈ (X k).parahoric J := by
  let B := (X k).building
  change ((X k).folded.comparison.lift w.val).val ∈ ((X k).parahoric J : Set _)
  rw [B.realization.face_union]
  exact Set.mem_iUnion.mpr ⟨w, DoubleCoset.mem_doubleCoset_self _ _ _⟩

private abbrev faceRepresentative (k : UnramifiedLevel F S) (w : faceWeylGroup X (k := k) J) :
    (X k).parahoric J :=
  ⟨((X k).folded.comparison.lift w.val).val, lift_mem_face (X := X) k w⟩

private theorem base_le (k : UnramifiedLevel F S) : P.auxiliary.base ≤ k := by
  change P.auxiliary.base.field ≤ k.field
  rw [P.auxiliary.base_eq]
  exact bot_le

private theorem geometricFace_doubleCosets :
    P.parahoricImage =
      ⋃ w : faceWeylGroup X (k := P.auxiliary.base) J,
        P.iwahoriImage * {P.geometricReduction P.auxiliary.base (faceRepresentative (X := X) _ w)} *
          P.iwahoriImage := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨k, g, rfl⟩ := (mem_parahoricImage P _).1 hv
    have hg : g.val ∈ ((X k).parahoric J : Set _) := g.property
    rw [(X k).building.realization.face_union] at hg
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
    obtain ⟨a, ha, b, hb, hmul⟩ := DoubleCoset.mem_doubleCoset.mp hw
    let bot := P.auxiliary.base
    have hw₀ : w.val ∈ faceWeylGroup X (k := bot) J := by
      rw [faceWeylGroup, sameWallSubgroup (X bot).folded.comparison (X k).folded.comparison]
      exact w.property
    let w₀ : faceWeylGroup X (k := bot) J := ⟨w.val, hw₀⟩
    let n := faceRepresentative (X := X) bot w₀
    let p := faceInclusion X (base_le P k) J (P.face_comap (base_le P k)) n
    let n' : (X k).parahoric J := faceRepresentative (X := X) k w
    let u := p * n'⁻¹
    have hu : u.val ∈ (X k).folded.comparison.I :=
      unitTorus_le_iwahori (X k).folded.comparison (P.lift_compare (base_le P k) w.val)
    let a' : (X k).parahoric J := ⟨a, iwahori_le_face (X := X) (J := J) k ha⟩
    let b' : (X k).parahoric J := ⟨b, iwahori_le_face (X := X) (J := J) k hb⟩
    have ha' : (a' * u⁻¹).val ∈ (X k).folded.comparison.I :=
      Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hu)
    have hga : g = (a' * u⁻¹) * p * b' := by
      have hgn : g = a' * n' * b' := Subtype.ext hmul
      rw [hgn]
      dsimp only [u]
      group
    have hred : P.geometricReduction k g =
        P.geometricReduction k (a' * u⁻¹) * P.geometricReduction bot n *
          P.geometricReduction k b' := by
      rw [hga, map_mul, map_mul, geometricReduction_natural P (base_le P k)]
    have hA : P.geometricReduction k (a' * u⁻¹) ∈ P.iwahoriImage :=
      (mem_geometricImage P _ _).2 ⟨k, a' * u⁻¹, ha', rfl⟩
    have hB : P.geometricReduction k b' ∈ P.iwahoriImage :=
      (mem_geometricImage P _ _).2 ⟨k, b', hb, rfl⟩
    exact Set.mem_iUnion.mpr ⟨w₀, Set.mul_mem_mul (Set.mul_mem_mul hA (Set.mem_singleton _)) hB
      |> fun h => hred.symm ▸ h⟩
  · intro hv
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hv
    obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_mul.mp hw
    obtain ⟨a, ha, n, hn, rfl⟩ := Set.mem_mul.mp hp
    rw [Set.mem_singleton_iff] at hn
    subst n
    let H := geometricParahoricSubgroup P
    exact H.mul_mem (H.mul_mem (geometricImage_subset_face P _ ha)
      (geometricReduction_mem P _ _)) (geometricImage_subset_face P _ hb)

end GeometricGroups

section FaceAssembly

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  [FiniteDimensional F L] [IsGalois F L] [IsSepClosed S] [Algebra.IsSeparable F S]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}

open ExceptionalAffineBruhat (ExceptionalNumbering)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalLocalRootCoordinates (ramificationIndex)

/-- The actual scaled point maps and exact signed layer coordinates extend
over the finite unramified coefficient fields of the chosen separable closure. -/
theorem existsScaledFaceTower
    (hdeg : Module.finrank F L = 2) (hσ : σ ≠ 1) (hr : 1 < ramificationIndex F L)
    (numbering : Fin 6 ≃ D.base.support) (hnum : ExceptionalNumbering D 6 numbering)
    (had : D.datum.rootSpan ℤ = ⊤)
    (hτ : ∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i))
    (X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field)
    (k₀ : UnramifiedLevel F S) (t : Weights (A.roots.SimpleWall A.basepoint))
    (x : invariantApartment D (R.diagram σ)) (ht : IsBarycenter (cotype t) t)
    (hx : rationalPoint (X k₀).building.realization.coordinates x =
      simplexPoint (X k₀).building.realization.coordinates (X k₀).building.realization.vertex t)
    (π : Lˣ) (hπ : normalizedValuation L (π : L) = exp (-1)) :
    cotype t = {a | A.roots.wallValue a.val x = 0} ∧ Function.Bijective (residueMap F L) ∧
      ∃ (ϖ : Fˣ) (d : ℕ) (y : D.Y),
        normalizedValuation F (ϖ : F) = exp (-1) ∧ 0 < d ∧
        (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y ∧
        ∃ P : ScaledParahoricTower X (cotype t) π d y,
          Nonempty (∀ k : UnramifiedLevel F S, LocalReductionCoordinates (P.scale k) ϖ x) := by
  have hc := rationalFaceCotype (X k₀).building t x hx
  obtain ⟨b, hb⟩ := normalizedValuation_surjective F (exp (-1))
  have hb₀ : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    exact WithZero.exp_ne_zero hb.symm
  let ϖ := Units.mk0 b hb₀
  obtain ⟨d, y, hd, hy₀⟩ := clearCocharacterDenominators ((2 : ℚ) • x.val)
  have hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y := by
    simpa only [smul_smul, mul_comm] using hy₀
  obtain ⟨U⟩ := RamifiedExceptionalAuxiliaryTower.ramifiedAuxiliaryTower
    (S := S) σ hdeg hσ hr (fun k => (X k).compositum) d hd (π : L) hπ
  have hstage (k : UnramifiedLevel F S) :
      ∃ p : StageScaling (J := cotype t) (y := y) X U k,
        Nonempty (LocalReductionCoordinates p ϖ x) := by
    have hxk := standardBarycenter_natural (X k₀).folded.comparison (X k).folded.comparison
      (X k₀).building (X k).building t x ht hx
    exact (RamifiedExceptionalLocalFaceCoordinates.ramifiedLocalFaceCoordinates σ hdeg hσ hr
      k.unramified R numbering hnum had hτ A (X k) t x ht hxk ϖ π hb hπ d y hd hy
      (localAuxiliary (U.extension k))).2
  let p (k : UnramifiedLevel F S) := (hstage k).choose
  let P := scaledTowerOfLocalScaling X U had hπ p
  exact ⟨hc, U.ramifiedResidue, ϖ, d, y, hb, hd, hy, P,
    ⟨fun k => Classical.choice (hstage k).choose_spec⟩⟩

end FaceAssembly

section LocalImages

open ExceptionalIwahoriCongruence (cellValue)
open RamifiedExceptionalLocalFaceCoordinates
  (rootResiduePoint InvariantTorusValues)

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  (P : ScaledParahoricTower X J π d y)
  {ϖ : Fˣ} {x : invariantApartment D (R.diagram σ)}
  (Q : ∀ k, LocalReductionCoordinates (P.scale k) ϖ x)

open private cellValue_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

private theorem rootLayerAtIwahoriDepth (k : UnramifiedLevel F S)
    (a : FoldedRootDirection × ℤ) (ha : a.2 = threshold (A.roots.root a.1 A.basepoint)) :
    (X k).rootLayer a ⊆ (X k).folded.comparison.I := by
  classical
  let C := (X k).folded.comparison.chart
  rintro g ⟨t, z, ht, hz, h⟩
  let b := Function.update (fun j => (0 : C.parameter j)) a.1 z
  apply ((X k).folded.bruhat.base_chart g).mpr
  have hg : cellValue M.toIntegralMarking (integralRing (X k).compositum.field)
      C.negative C.positive (C.chart.coordinates t b) = (X k).folded.points g := h.symm
  refine ⟨(t, b), ⟨hg, ?_, ?_⟩, ?_⟩
  · intro χ
    rw [ht]
    simp
  · intro j
    by_cases hj : j = a.1
    · subst j
      simpa only [ha, b, Function.update_self] using hz
    · change C.value j (b j) ≤ _
      rw [show b j = 0 from Function.update_of_ne hj _ _, map_zero]
      exact bot_le
  · intro w hw
    have hsurj : Function.Surjective C.direction := by
      rw [(X k).folded.directions]
      exact A.surjective
    exact RamifiedExceptionalLocalFaceCoordinates.localRootChart_injective C hsurj
      (hw.1.trans hg.symm)

private theorem iwahoriRootReduction
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (k : UnramifiedLevel F S) (a : survivingIwahoriRoots A x) :
    (X k).rootLayer a.val ⊆ (X k).folded.comparison.I ∧
    (P.scale k).image ((X k).rootLayer a.val) =
      Set.range (rootResiduePoint (X k) ϖ π a.val ((Q k).leading a.val)
        (residueMap (X k).compositum.field (P.auxiliary.extension k).field)) := by
  have hI := rootLayerAtIwahoriDepth (X := X) k a.val a.property.1
  refine ⟨hI, ?_⟩
  let C := (X k).folded.comparison.chart
  let K := (X k).compositum.field
  let U := localAuxiliary (P.auxiliary.extension k)
  let z : ExceptionalIwahoriCongruence.CellValues D (integralRing K) C.negative C.positive :=
    (0, 1, 0)
  have hz : cellValue M.toIntegralMarking (integralRing K) C.negative C.positive z ∈
      (X k).folded.points.range := by
    rw [show z = (0, 1, 0) from rfl, cellValue_torus]
    use 1
    rw [map_one]
    exact (markedTorusPointHom M.toIntegralMarking (integralRing K)).map_one.symm
  obtain ⟨t, p, h⟩ := (C.rational z).mp hz
  have ht : t.val = 1 := congrArg (fun b => b.2.1) h
  exact RamifiedExceptionalLocalFaceCoordinates.rootLayerReductionImage
    (X k) ϖ π d y U x hy (P.scale k) hπ hd a.val a.property.2
      ((Q k).leading a.val) (hI.trans (iwahori_le_face (X := X) (J := J) k)) t ht

include Q in
private theorem wallLiftGeometricReduction
    (k : UnramifiedLevel F S) (a : A.roots.SimpleWall A.basepoint) (ha : a ∈ J)
    (h : (X k).wallLift a ∈ (X k).parahoric J) :
    P.geometricReduction k ⟨(X k).wallLift a, h⟩ ∈
      Subgroup.closure (P.rootImage a.val ∪ P.rootImage (A.roots.opposite a.val)) := by
  obtain ⟨r, t, _, ⟨p, q, _, _, hp, hq, n, hn, _, hw⟩, _⟩ := (Q k).wall a ha
  let H := Subgroup.closure (P.rootImage a.val ∪ P.rootImage (A.roots.opposite a.val))
  have hp' : P.geometricReduction k p ∈ H :=
    Subgroup.subset_closure (Or.inl ((mem_geometricImage P _ _).2 ⟨k, p, hp, rfl⟩))
  have hq' : P.geometricReduction k q ∈ H :=
    Subgroup.subset_closure (Or.inr ((mem_geometricImage P _ _).2 ⟨k, q, hq, rfl⟩))
  have he : (⟨(X k).wallLift a, h⟩ : (X k).parahoric J) = n := Subtype.ext hn.symm
  rw [he]
  change scalarPoints M (P.auxiliary.residueEmbedding k) ((P.scale k).reduction n) ∈ H
  rw [hw, map_mul, map_mul]
  exact H.mul_mem (H.mul_mem hp' hq') hp'

include Q in
private theorem parahoricImage_generated (hI : P.iwahoriImage ⊆
    (Subgroup.closure (P.torusImage ∪
      ⋃ a : residueRootDirections A J x, P.rootImage a.val) : Set _)) :
    P.parahoricImage =
      (Subgroup.closure (P.torusImage ∪
        ⋃ a : residueRootDirections A J x, P.rootImage a.val) : Set _) := by
  let U := P.torusImage ∪ ⋃ a : residueRootDirections A J x, P.rootImage a.val
  let H := Subgroup.closure U
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨k, g, rfl⟩ := (mem_parahoricImage P _).1 hv
    let B := (X k).parahoric J
    let L := (H.comap (P.geometricReduction k)).map B.subtype
    have hl : B ≤ L := by
      apply (Subgroup.closure_le _).mpr
      rintro b (hi | ⟨a, ha, rfl⟩)
      · let p : B := ⟨b, Subgroup.subset_closure (Or.inl hi)⟩
        exact ⟨p, hI ((mem_geometricImage P _ _).2 ⟨k, p, hi, rfl⟩), rfl⟩
      · let p : B := ⟨(X k).wallLift a, Subgroup.subset_closure (Or.inr ⟨a, ha, rfl⟩)⟩
        refine ⟨p, ?_, rfl⟩
        have hsub : P.rootImage a.val ∪ P.rootImage (A.roots.opposite a.val) ⊆ U := by
          have ha₁ : a.val ∈ residueRootDirections A J x :=
            Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, by simp⟩⟩)
          have ha₂ : A.roots.opposite a.val ∈ residueRootDirections A J x :=
            Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, by simp⟩⟩)
          rintro z (hz | hz)
          · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨_, ha₁⟩, hz⟩)
          · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨_, ha₂⟩, hz⟩)
        exact Subgroup.closure_mono hsub (wallLiftGeometricReduction P Q k a ha p.property)
    obtain ⟨p, hp, he⟩ := hl g.property
    exact (Subtype.ext he : p = g) ▸ hp
  · have hs : U ⊆ geometricParahoricSubgroup P := by
      intro v hv
      rcases hv with hv | hv
      · exact geometricImage_subset_face P _ hv
      · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
        exact geometricImage_subset_face P _ ha
    exact (Subgroup.closure_le (geometricParahoricSubgroup P)).mpr hs

end LocalImages

section GeometricTorus

open RamifiedExceptionalLocalFaceCoordinates (InvariantTorusValues)

variable {D : BasedRootDatum.{u}} {M : Model D}

private def simpleRootBasis (had : D.datum.rootSpan ℤ = ⊤) :
    Module.Basis D.base.support ℤ D.X :=
  Module.Basis.mk D.base.linearIndepOn_root (by
    change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
    rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support]
    exact had.ge)

open private torusValues_ext_basis from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalRationalUnitTorus

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  (P : ScaledParahoricTower X J π d y)
  {ϖ : Fˣ} {x : invariantApartment D (R.diagram σ)}
  (Q : ∀ k, LocalReductionCoordinates (P.scale k) ϖ x)

include Q in
/-- The geometric unit-torus image consists of precisely the invariant
character tuples, with every such tuple liftable at a finite level. -/
theorem geometricTorusCoordinates (had : D.datum.rootSpan ℤ = ⊤) :
    P.torusImage = Set.range (fun t : InvariantTorusValues (R.diagram σ) (AlgebraicClosure kᵥ[F]) =>
      (show FieldPoints M (AlgebraicClosure kᵥ[F]) from
        torusPoint D (integralRing (AlgebraicClosure kᵥ[F])) t.val ≫ M.torus.hom.hom)) := by
  classical
  let κ := AlgebraicClosure kᵥ[F]
  letI : Finite D.I := D.finiteRoots
  ext p
  constructor
  · intro hp
    obtain ⟨k, g, hg, rfl⟩ := (mem_geometricImage P _ p).1 hp
    let K := (X k).compositum.field
    let E := (localAuxiliary (P.auxiliary.extension k)).field
    have hp' : (P.scale k).reduction g ∈ (P.scale k).image ((X k).folded.comparison.T₀ : Set _) :=
      ⟨g, hg, rfl⟩
    rw [(Q k).torus] at hp'
    obtain ⟨t, ht⟩ := hp'
    let f := P.auxiliary.diagramResidueEmbedding k
    let q : TorusValues D (integralRing κ) := (Units.map f).comp t.val
    have hq : ∀ χ : D.X, q (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ)) =
        q (Multiplicative.ofAdd χ) := fun χ => congrArg (Units.map f.toMonoidHom) (t.property χ)
    refine ⟨⟨q, hq⟩, ?_⟩
    change torusPoint D (integralRing κ) q ≫ M.torus.hom.hom =
      scalarPoints M (P.auxiliary.residueEmbedding k) ((P.scale k).reduction g)
    have hc : scalarPoints M (P.auxiliary.residueEmbedding k) ((P.scale k).reduction g) =
        scalarPoints M f (torusPoint D (integralRing kᵥ[K]) t.val ≫ M.torus.hom.hom) :=
      (congrArg (scalarPoints M (P.auxiliary.residueEmbedding k)) ht.symm).trans
        (scalarPoints_comp_apply (residueMap K E) (P.auxiliary.residueEmbedding k) _)
    exact (hc.trans (scalarPoints_torus f t.val)).symm
  · rintro ⟨t, rfl⟩
    let b := simpleRootBasis had
    obtain ⟨k, h, hh⟩ := P.auxiliary.residue_exhaustive
      (fun i : D.base.support => (t.val (Multiplicative.ofAdd (b i)) : κ))
    let K := (X k).compositum.field
    let E := (localAuxiliary (P.auxiliary.extension k)).field
    let f : kᵥ[K] →+* κ := P.auxiliary.diagramResidueEmbedding k
    obtain ⟨z, hz⟩ := Classical.axiomOfChoice
      (fun i : D.base.support => (P.auxiliary.extension k).residue_bijective.2 (h i))
    have hz' (i : D.base.support) : f (z i) = (t.val (Multiplicative.ofAdd (b i)) : κ) := by
      exact (congrArg (P.auxiliary.residueEmbedding k) (hz i)).trans (hh i)
    have hn (i : D.base.support) : z i ≠ 0 := by
      intro h₀
      have h' := hz' i
      rw [h₀, map_zero] at h'
      exact (Units.ne_zero _ h'.symm)
    let v (i : D.base.support) := Units.mk0 (z i) (hn i)
    let l : D.X →ₗ[ℤ] Additive kᵥ[K]ˣ := b.constr ℤ (fun i => Additive.ofMul (v i))
    let q : TorusValues D (integralRing kᵥ[K]) :=
      { toFun := fun χ => (l χ.toAdd).toMul
        map_one' := l.map_zero
        map_mul' := fun χ ψ => l.map_add χ.toAdd ψ.toAdd }
    have hq : (Units.map f).comp q = t.val := by
      apply torusValues_ext_basis b
      intro i
      apply Units.ext
      have hi : l (b i) = Additive.ofMul (v i) := b.constr_basis ℤ _ i
      change f ((l (b i)).toMul : kᵥ[K]) = _
      rw [hi]
      exact hz' i
    have hqInv : ∀ χ : D.X, q (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ)) =
        q (Multiplicative.ofAdd χ) := by
      intro χ
      apply Units.map_injective (f := f.toMonoidHom) f.injective
      exact (DFunLike.congr_fun hq _).trans ((t.property χ).trans (DFunLike.congr_fun hq _).symm)
    have hmem : scalarPoints M (residueMap K E)
        (torusPoint D (integralRing kᵥ[K]) q ≫ M.torus.hom.hom) ∈
        (P.scale k).image ((X k).folded.comparison.T₀ : Set _) := by
      rw [(Q k).torus]
      exact ⟨⟨q, hqInv⟩, rfl⟩
    obtain ⟨g, hg, he⟩ := hmem
    refine (mem_geometricImage P _ _).2 ⟨k, g, hg, ?_⟩
    change scalarPoints M (P.auxiliary.residueEmbedding k) ((P.scale k).reduction g) = _
    have hc := (congrArg (scalarPoints M (P.auxiliary.residueEmbedding k)) he).trans
      (scalarPoints_comp_apply (residueMap K E) (P.auxiliary.residueEmbedding k)
        (torusPoint D (integralRing kᵥ[K]) q ≫ M.torus.hom.hom))
    exact hc.trans ((scalarPoints_torus f q).trans
      (congrArg (fun w => torusPoint D (integralRing κ) w ≫ M.torus.hom.hom) hq))

end GeometricTorus

section ResidueParameters

open CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory
open IntegralSemisimpleModel (forgetFibrePoint)

variable {κ : Type u} [Field κ] {D : BasedRootDatum.{u}} {M : Model D}

open private forgetFibrePoint_mul forgetFibrePoint_natural from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private forgetFibrePoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections

/-- Products of parameter schemes realize products of their geometric point images. -/
def multiplyResidueParameters (f g : ResidueParameterMap M κ) : ResidueParameterMap M κ where
  source := f.source ⊗ g.source
  locallyFiniteType := by
    let _ := f.locallyFiniteType
    let _ := g.locallyFiniteType
    rw [Over.tensorObj_hom]
    infer_instance
  quasiCompact := by
    let _ := f.quasiCompact
    let _ := g.quasiCompact
    rw [Over.tensorObj_hom]
    infer_instance
  morphism := (fst _ _ ≫ f.morphism) * (snd _ _ ≫ g.morphism)

private theorem geometricImage_multiplyResidueParameters (f g : ResidueParameterMap M κ) :
    (multiplyResidueParameters f g).geometricImage = f.geometricImage * g.geometricImage := by
  let K := CommAlgCat.of κ (AlgebraicClosure κ)
  have hmul (s : Points (f.source ⊗ g.source) K) :
      forgetFibrePoint M.group K (s ≫ (multiplyResidueParameters f g).morphism) =
        forgetFibrePoint M.group K ((s ≫ fst _ _) ≫ f.morphism) *
          forgetFibrePoint M.group K ((s ≫ snd _ _) ≫ g.morphism) := by
    simp only [multiplyResidueParameters, MonObj.comp_mul, Category.assoc]
    exact forgetFibrePoint_mul M.group K _ _
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    apply Set.mem_mul.mpr
    exact ⟨_, ⟨s ≫ fst _ _, rfl⟩, _, ⟨s ≫ snd _ _, rfl⟩, (hmul s).symm⟩
  · rintro ⟨a, ⟨s, rfl⟩, b, ⟨t, rfl⟩, rfl⟩
    refine ⟨lift s t, ?_⟩
    exact (hmul (lift s t)).trans (by rw [lift_fst, lift_snd])

/-- The original residue-field point gives a constant parameter map. -/
def constantResidueParameter (g : FieldPoints M κ) : ResidueParameterMap M κ where
  source := 𝟙_ (SchemeOver κ)
  locallyFiniteType := by
    exact MorphismProperty.id_mem (@LocallyOfFiniteType) _
  quasiCompact := by
    exact MorphismProperty.id_mem (@QuasiCompact) _
  morphism := (groundIso (k := κ)).inv ≫ (forgetFibrePoint_surjective M.group
    (CommAlgCat.of κ κ) g).choose

private theorem geometricImage_constantResidueParameter (g : FieldPoints M κ) :
    (constantResidueParameter g).geometricImage =
      {scalarPoints M (algebraMap κ (AlgebraicClosure κ)) g} := by
  let K := CommAlgCat.of κ (AlgebraicClosure κ)
  let k := CommAlgCat.of κ κ
  let f : k ⟶ K := CommAlgCat.ofHom (Algebra.ofId κ (AlgebraicClosure κ))
  let p := (forgetFibrePoint_surjective M.group k g).choose
  have hp : forgetFibrePoint M.group k p = g := (forgetFibrePoint_surjective M.group k g).choose_spec
  have he (s : Points (𝟙_ (SchemeOver κ)) K) :
      s ≫ (constantResidueParameter g).morphism =
        (testSpec κ).map f.op ≫ p := by
    change s ≫ ((groundIso (k := κ)).inv ≫ p) = _
    have hs : s ≫ (groundIso (k := κ)).inv = (testSpec κ).map f.op := by
      apply (cancel_mono (groundIso (k := κ)).hom).mp
      exact Subsingleton.elim _ _
    rw [← Category.assoc, hs]
  have hred (s : Points (𝟙_ (SchemeOver κ)) K) :
      forgetFibrePoint M.group K (s ≫ (constantResidueParameter g).morphism) =
        scalarPoints M (algebraMap κ (AlgebraicClosure κ)) g := by
    rw [he]
    have h := forgetFibrePoint_natural M.group f p
    change forgetFibrePoint M.group K ((testSpec κ).map f.op ≫ p) =
      scalarPoints M (algebraMap κ (AlgebraicClosure κ)) (forgetFibrePoint M.group k p) at h
    exact h.trans (congrArg _ hp)
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact Set.mem_singleton_iff.mpr (hred s)
  · rintro rfl
    exact ⟨toUnit _, hred _⟩

end ResidueParameters

section RootLayerTransport

open ExceptionalAffineRootSystems (IsLongF4Doubled)
open ExceptionalAffineBruhat (LocalRootChart)
open ExceptionalIwahoriCongruence (cellValue CellValues mapCellValues)
open ExceptionalMarkedRootDescent (markedRootPoint)
open IntegralRootRelations (upper)
open private absoluteCell cellValue_supported rootSlot_nonempty foldedSlot_data rationalChart_single from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalOppositeWallLayer
open private markedRootPoint_map from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private cellValue_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private normalizedIntegerUnit from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates

variable {D : BasedRootDatum.{u}} {M : Model D} {τ : BasedIso D D}
  (A : FoldedApartment τ)

private def rootOrbit (a : FoldedRootDirection) : Finset D.I := by
  let _ : Finite D.I := D.finiteRoots
  let _ := Fintype.ofFinite D.I
  exact Finset.univ.filter (fun i => A.direction i = a)

private theorem mem_rootOrbit (a : FoldedRootDirection) (i : D.I) :
    i ∈ rootOrbit A a ↔ A.direction i = a := by
  simp [rootOrbit]

private def orbitRootValue {K : Type u} [Field K] (a : FoldedRootDirection) (z : D.I → K) :
    FieldPoints M K :=
  ((rootOrbit A a).toList.map (fun i => markedRootPoint M.toIntegralMarking (integralRing K) i (z i))).prod

private theorem cellValue_ofOrbit {K : Type u} [Field K]
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (negative positive : List D.I)
    (hn : OrderedRootProducts.Enumerates negative {a | ¬ D.base.IsPos a})
    (hp : OrderedRootProducts.Enumerates positive {a | D.base.IsPos a})
    (a : FoldedRootDirection) (v : D.I → K) (hv : ∀ i, A.direction i ≠ a → v i = 0) :
    cellValue M.toIntegralMarking (integralRing K) negative positive
      (fun i => v negative[i], 1, fun i => v positive[i]) = orbitRootValue (M := M) A a v := by
  classical
  let l := (rootOrbit A a).toList
  have hi (i : D.I) : i ∈ l ↔ A.direction i = a :=
    Finset.mem_toList.trans (mem_rootOrbit A a i)
  apply cellValue_supported M.toIntegralMarking (integralRing K) negative positive l hn hp
    (Finset.nodup_toList _) v
  · intro i hi'
    exact hv i (fun h => hi' ((hi i).mpr h))
  · intro i hi' j hj' hne
    have hpair : D.datum.pairing i j = 0 := by
      rcases (A.orbits i j).mp (((hi i).mp hi').trans ((hi j).mp hj').symm) with h | h
      · exact (hne h.symm).elim
      · subst j
        exact A.orthogonal i hne.symm
    have h := ExceptionalMarkedRootDescent.markedOrthogonalRootCommutation M hsym i j hpair
      K (CommAlgCat.of K K) (upper (v i)) (Or.inl ⟨v i, rfl⟩)
      (upper (v j)) (Or.inl ⟨v j, rfl⟩)
    simpa only [M.rankOneUpper, markedRootPoint] using h

private theorem orbitRootValue_scalar {K E : Type u} [Field K] [Field E] (e : K →+* E)
    (a : FoldedRootDirection) (v : D.I → K) :
    scalarPoints M e (orbitRootValue (M := M) A a v) =
      orbitRootValue (M := M) A a (fun i => e (v i)) := by
  unfold orbitRootValue
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i _
  exact markedRootPoint_map M.toIntegralMarking (integralRingMap e) i (v i)

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {G : Type u} [Group G] {f : G →* FieldPoints M K}
  (C : LocalRootChart (j := f) A.roots A.basepoint)

private theorem cellValues_absolute (b : CellValues D (integralRing K) C.negative C.positive) :
    ∃ v : D.I → K, absoluteCell C v b.2.1 = b := by
  classical
  let v (i : D.I) : K :=
    if hn : i ∈ C.negative then b.1 ⟨C.negative.idxOf i, List.idxOf_lt_length_of_mem hn⟩
    else if hp : i ∈ C.positive then b.2.2 ⟨C.positive.idxOf i, List.idxOf_lt_length_of_mem hp⟩
    else 0
  refine ⟨v, Prod.ext (funext fun i => ?_) (Prod.ext rfl (funext fun i => ?_))⟩
  · have h : C.negative[i] ∈ C.negative := List.getElem_mem i.isLt
    change v C.negative[i] = b.1 i
    simp only [v, dite_eq_left h]
    have he : (⟨C.negative.idxOf C.negative[i], List.idxOf_lt_length_of_mem h⟩ :
        Fin C.negative.length) = i :=
      C.negative_enumerates.1.injective_get (List.getElem_idxOf _)
    exact congrArg b.1 he
  · have h : C.positive[i] ∈ C.positive := List.getElem_mem i.isLt
    have hn : C.positive[i] ∉ C.negative := fun h' => (C.negative_enumerates.2 _).mp h'
      ((C.positive_enumerates.2 _).mp h)
    change v C.positive[i] = b.2.2 i
    simp only [v, dite_eq_right hn, dite_eq_left h]
    have he : (⟨C.positive.idxOf C.positive[i], List.idxOf_lt_length_of_mem h⟩ :
        Fin C.positive.length) = i :=
      C.positive_enumerates.1.injective_get (List.getElem_idxOf _)
    exact congrArg b.2.2 he

private theorem identityChartTorus : ∃ t : C.chart.torus, t.val = 1 := by
  have h : cellValue M.toIntegralMarking (integralRing K) C.negative C.positive (0, 1, 0) ∈
      f.range := by
    rw [cellValue_torus]
    exact ⟨1, (map_one f).trans (markedTorusPointHom M.toIntegralMarking (integralRing K)).map_one.symm⟩
  obtain ⟨t, _, h'⟩ := (C.rational (0, 1, 0)).mp h
  exact ⟨t, congrArg (fun b => b.2.1) h'⟩

end RootLayerTransport

section FoldedRootLayer

open ExceptionalAffineRootSystems (IsLongF4Doubled)
open ExceptionalAffineBruhat (LocalRootChart)
open ExceptionalIwahoriCongruence (cellValue CellValues)
open private absoluteCell rootSlot_nonempty rationalChart_single foldedSlot_data
  RootSlot.read RootSlot.read_absolute RootSlot.read_coordinates RootSlot.unit from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalOppositeWallLayer
open private normalizedIntegerUnit from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates

variable {F L k k' : Type u} [Field F] [Field L] [Field k] [Field k'] [Algebra F L]
  [Algebra F k] [Algebra F k'] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  (X : MarkedLevel R σ A k) (Y : MarkedLevel R σ A k')

private abbrev depthExponent (a : FoldedRootDirection) : ℕ :=
  if IsLongF4Doubled a.val then 2 else 1

private theorem depthExponent_ne_zero (a : FoldedRootDirection) : depthExponent a ≠ 0 := by
  unfold depthExponent
  split <;> decide

/-- A marked root layer can be read using the supported absolute
coordinates in any marked ordering of the split cell. -/
private theorem rootLayer_iff_orbitCoordinates
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i) (a : FoldedRootDirection × ℤ)
    (g : GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    g ∈ X.rootLayer a ↔
      ∃ v : D.I → X.compositum.field, (∀ i, A.direction i ≠ a.1 → v i = 0) ∧
        (∀ i, A.direction i = a.1 → normalizedValuation X.compositum.field (v i) ≤
          (exp (-a.2)) ^ depthExponent a.1) ∧
        X.folded.points g = orbitRootValue (M := M) A a.1 v := by
  classical
  let K := X.compositum.field
  let C := X.folded.comparison.chart
  have hsurj : Function.Surjective C.direction := by
    rw [X.folded.directions]
    exact A.surjective
  have hcell (v : D.I → K) (hv : ∀ i, A.direction i ≠ a.1 → v i = 0) :
      cellValue M.toIntegralMarking (integralRing K) C.negative C.positive (absoluteCell C v 1) =
        orbitRootValue (M := M) A a.1 v :=
    cellValue_ofOrbit A hsym C.negative C.positive C.negative_enumerates C.positive_enumerates a.1 v hv
  have hread (t : C.chart.torus) (z : C.parameter a.1) (v : D.I → K)
      (he : C.chart.coordinates t (Function.update (fun _ => 0) a.1 z) = absoluteCell C v 1)
      (i : D.I) :
      (A.direction i ≠ a.1 → v i = 0) ∧
        (A.direction i = a.1 → normalizedValuation K (v i) = C.value a.1 z ^ depthExponent a.1) := by
    have hi := congrFun X.folded.directions i
    obtain ⟨s⟩ := rootSlot_nonempty C i (A.direction i) hi
    have h := congrArg (RootSlot.read s) he
    rw [RootSlot.read_coordinates s, RootSlot.read_absolute s] at h
    refine ⟨fun hn => ?_, fun hp => ?_⟩
    · rw [Function.update_of_ne hn, map_zero, mul_zero] at h
      exact h.symm
    · have hslot : C.direction i = a.1 := hi.trans hp
      obtain ⟨r⟩ := rootSlot_nonempty C i a.1 hslot
      have q := congrArg (RootSlot.read r) he
      rw [RootSlot.read_coordinates r, RootSlot.read_absolute r, Function.update_self] at q
      rw [← q, map_mul, normalizedIntegerUnit (RootSlot.unit r), one_mul]
      exact (foldedSlot_data X.compositum X.folded i a.1 hp r).2 z
  constructor
  · rintro ⟨t, z, ht, hz, hg⟩
    obtain ⟨v, hv⟩ := cellValues_absolute A C
      (C.chart.coordinates t (Function.update (fun _ => 0) a.1 z))
    have he : C.chart.coordinates t (Function.update (fun _ => 0) a.1 z) = absoluteCell C v 1 := by
      change absoluteCell C v t.val = _ at hv
      rw [ht] at hv
      exact hv.symm
    have hz₀ (i : D.I) := (hread t z v he i).1
    refine ⟨v, hz₀, fun i hi => ?_, ?_⟩
    · rw [(hread t z v he i).2 hi]
      exact pow_le_pow_left₀ bot_le hz _
    · exact hg.trans ((congrArg (cellValue M.toIntegralMarking (integralRing K)
        C.negative C.positive) he).trans (hcell v hz₀))
  · rintro ⟨v, hv₀, hv, hg⟩
    obtain ⟨t, ht⟩ := identityChartTorus A C
    have hmem : cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
        (absoluteCell C v 1) ∈ X.folded.points.range :=
      ⟨g, hg.trans (hcell v hv₀).symm⟩
    obtain ⟨z, hz⟩ := rationalChart_single C hsurj t ht a.1 v
      (fun i hi => hv₀ i (fun h => hi ((congrFun X.folded.directions i).trans h))) hmem
    obtain ⟨i, hi⟩ := A.surjective a.1
    have hv' := hv i hi
    rw [(hread t z v hz i).2 hi] at hv'
    have hz' := (pow_le_pow_iff_left₀ bot_le bot_le (depthExponent_ne_zero a.1)).mp hv'
    exact ⟨t, z, ht, hz', hg.trans ((hcell v hv₀).symm.trans
      (congrArg (cellValue M.toIntegralMarking (integralRing K) C.negative C.positive) hz.symm))⟩

private theorem rootLayer_scalar
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (f : k →ₐ[F] k') (e : X.compositum.field →ₐ[F] Y.compositum.field)
    (he : ∀ a, normalizedValuation Y.compositum.field (e a) =
      normalizedValuation X.compositum.field a)
    (hL : ∀ z : L, e (algebraMap L X.compositum.field z) = algebraMap L Y.compositum.field z)
    (hk : ∀ z : k, e (algebraMap k X.compositum.field z) = algebraMap k' Y.compositum.field (f z))
    (a : FoldedRootDirection × ℤ) :
    Set.MapsTo (coefficientPoints R.descent.group.val f) (X.rootLayer a) (Y.rootLayer a) := by
  intro g hg
  obtain ⟨v, hv₀, hv, hp⟩ := (rootLayer_iff_orbitCoordinates X hsym a g).mp hg
  apply (rootLayer_iff_orbitCoordinates Y hsym a _).mpr
  refine ⟨fun i => e (v i), fun i hi => ?_, fun i hi => ?_, ?_⟩
  · change e (v i) = 0
    rw [hv₀ i hi, map_zero]
  · exact (he (v i)).trans_le (hv i hi)
  · rw [coefficientPoints_split X Y f e hL hk, hp]
    exact orbitRootValue_scalar A e.toRingHom a.1 v

end FoldedRootLayer

section FaceParameterCover

open RamifiedExceptionalAuxiliaryTower (normalizedValuation_le_one)

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  (P : ScaledParahoricTower X J π d y)

private theorem baseResidue_surjective :
    Function.Surjective (residueMap F P.auxiliary.base.field) := by
  let k := P.auxiliary.base
  intro b
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := Oᵥ[k.field]) b
  have hz : ((z : k.field) : S) ∈ (⊥ : IntermediateField F S) := by
    rw [← P.auxiliary.base_eq]
    exact (z : k.field).property
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hz
  have he : algebraMap F k.field a = (z : k.field) := Subtype.ext ha
  have ha₀ : valuation F a ≤ 1 := by
    apply (normalizedValuation_le_one a).mp
    rw [← k.unramified a, he]
    exact (normalizedValuation_le_one (z : k.field)).mpr z.property
  let a₀ : Oᵥ[F] := ⟨a, ha₀⟩
  have hea : algebraMap Oᵥ[F] Oᵥ[k.field] a₀ = z := Subtype.ext he
  refine ⟨IsLocalRing.residue Oᵥ[F] a₀, ?_⟩
  exact (IsLocalRing.ResidueField.map_residue (algebraMap Oᵥ[F] Oᵥ[k.field]) a₀).trans
    (congrArg (IsLocalRing.residue Oᵥ[k.field]) hea)

private theorem scalarPoints_id_apply {K : Type u} [Field K] (g : FieldPoints M K) :
    scalarPoints M (RingHom.id K) g = g := by
  have hi : integralRingMap (RingHom.id K) = 𝟙 (integralRing K) := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  change integralSpec.map (integralRingMap (RingHom.id K)).op ≫ g = g
  simp only [hi, CategoryTheory.op_id, integralSpec.map_id, Category.id_comp]

private theorem baseGeometricReduction_rational (g : (X P.auxiliary.base).parahoric J) :
    ∃ z : FieldPoints M kᵥ[F], scalarPoints M (algebraMap kᵥ[F] (AlgebraicClosure kᵥ[F])) z =
      P.geometricReduction P.auxiliary.base g := by
  let k := P.auxiliary.base
  let K := (X k).compositum.field
  let E := (P.auxiliary.extension k).field
  let b := (residueMap K E).comp ((residueMap k.field K).comp (residueMap F k.field))
  have hb : Function.Bijective b :=
    ⟨b.injective, (P.auxiliary.extension k).residue_bijective.2.comp
      ((P.auxiliary.coefficientResidue_bijective k).2.comp (baseResidue_surjective P))⟩
  let e := RingEquiv.ofBijective b hb
  let p : FieldPoints M kᵥ[E] := (P.scale k).reduction g
  let z := scalarPoints M e.symm.toRingHom p
  have hp : scalarPoints M b z = p := by
    change scalarPoints M b (scalarPoints M e.symm.toRingHom p) = p
    have hcomp : b.comp e.symm.toRingHom = RingHom.id _ :=
      RingHom.ext fun a => e.apply_symm_apply a
    exact (scalarPoints_comp_apply e.symm.toRingHom b p).trans
      ((congrArg (fun f => scalarPoints M f p) hcomp).trans (scalarPoints_id_apply p))
  have h := P.auxiliary.residue_base k
  change (P.auxiliary.residueEmbedding k).comp b =
    algebraMap kᵥ[F] (AlgebraicClosure kᵥ[F]) at h
  refine ⟨z, ?_⟩
  change scalarPoints M (algebraMap kᵥ[F] (AlgebraicClosure kᵥ[F])) z =
    scalarPoints M (P.auxiliary.residueEmbedding k) p
  rw [← hp]
  exact (congrArg (fun f => scalarPoints M f z) h.symm).trans
    (scalarPoints_comp_apply b (P.auxiliary.residueEmbedding k) z).symm

/-- A single residue parameter scheme for the Iwahori gives the finite
family of parameter schemes for the entire geometric face image. -/
theorem faceParameterCover (f : ResidueParameterMap M kᵥ[F])
    (hf : f.geometricImage = P.iwahoriImage) :
    ∃ maps : faceWeylGroup X (k := P.auxiliary.base) J → ResidueParameterMap M kᵥ[F],
      (∀ w, ∃ (n : (X P.auxiliary.base).parahoric J) (g : FieldPoints M kᵥ[F]),
        n.val = ((X P.auxiliary.base).folded.comparison.lift w.val).val ∧
        scalarPoints M (algebraMap kᵥ[F] (AlgebraicClosure kᵥ[F])) g =
          P.geometricReduction P.auxiliary.base n ∧
        (maps w).geometricImage =
          P.iwahoriImage * {P.geometricReduction P.auxiliary.base n} * P.iwahoriImage) ∧
      P.parahoricImage = ⋃ w, (maps w).geometricImage := by
  let BaseW := faceWeylGroup X (k := P.auxiliary.base) J
  let n (w : BaseW) := faceRepresentative (X := X) P.auxiliary.base w
  choose q hq using fun w : BaseW => baseGeometricReduction_rational P (n w)
  let maps (w : BaseW) :=
    multiplyResidueParameters (multiplyResidueParameters f (constantResidueParameter (q w))) f
  have hmaps (w : BaseW) : (maps w).geometricImage =
      P.iwahoriImage * {P.geometricReduction P.auxiliary.base (n w)} * P.iwahoriImage := by
    change (multiplyResidueParameters (multiplyResidueParameters f (constantResidueParameter (q w))) f).geometricImage = _
    rw [geometricImage_multiplyResidueParameters, geometricImage_multiplyResidueParameters,
      geometricImage_constantResidueParameter, hf, hq]
  refine ⟨maps, fun w => ⟨n w, q w, rfl, hq w, hmaps w⟩, ?_⟩
  rw [geometricFace_doubleCosets P]
  exact congrArg Set.iUnion (funext fun w => (hmaps w).symm)

end FaceParameterCover

section ResidueLines

open CategoryTheory.Limits
open IntegralSemisimpleModel (forgetFibrePoint)
open ExceptionalMarkedRootDescent (markedRootPoint)
open IntegralRootRelations (upper)

open private integralAdditiveLineFunctorIso integralAdditivePoints integralAdditivePoints_value
  forgetFibrePoint_comp forgetFibrePoint_mul forgetFibrePoint_injective from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private fibre_isAffine integralAdditiveLine_geometricallyConnected from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

variable {κ : Type u} [Field κ] {D : BasedRootDatum.{u}} {M : Model D} {τ : BasedIso D D}

/-- Multiplication by a scalar on the additive point functor. -/
private def scalarAdditivePoints (c : κ) :
    StandardGroups.additivePoints κ ⟶ StandardGroups.additivePoints κ where
  app R := GrpCat.ofHom
    { toFun := fun z => Multiplicative.ofAdd (algebraMap κ R c * z.toAdd)
      map_one' := by
        change Multiplicative.ofAdd (algebraMap κ R c * (0 : R)) = Multiplicative.ofAdd (0 : R)
        rw [mul_zero]
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd (algebraMap κ R c * (x.toAdd + y.toAdd)) =
          Multiplicative.ofAdd (algebraMap κ R c * x.toAdd + algebraMap κ R c * y.toAdd)
        rw [mul_add] }
  naturality {R S} f := by
    apply GrpCat.ext
    intro z
    let a : R := z.toAdd
    change Multiplicative.ofAdd (algebraMap κ S c * f.hom a) =
      Multiplicative.ofAdd (f.hom (algebraMap κ R c * a))
    exact congrArg (fun z : S => Multiplicative.ofAdd z)
      (((f.hom.map_mul (algebraMap κ R c) a).trans
        (congrArg (fun z : S => z * f.hom a) (f.hom.commutes c))).symm)

private def absoluteRootParameter (i : D.I) (c : κ) :
    StandardGroups.additivePoints κ ⟶ (groupPointsFunctor κ).obj (residueGroup M κ) :=
  scalarAdditivePoints c ≫ (integralAdditiveLineFunctorIso κ M.line).hom ≫
    (groupPointsFunctor κ).map ((fibre κ).map (M.root i))

private theorem absoluteRootParameter_value (i : D.I) (c : κ) (R : TestAlgebra κ) (z : R) :
    forgetFibrePoint M.group R
        ((absoluteRootParameter (M := M) i c).app R (Multiplicative.ofAdd z)) =
      markedRootPoint M.toIntegralMarking (integralRing R) i (algebraMap κ R c * z) := by
  change forgetFibrePoint M.group R
    (integralAdditivePoints κ M.line R (Multiplicative.ofAdd (algebraMap κ R c * z)) ≫
      ((fibre κ).map (M.root i)).hom.hom) = _
  rw [forgetFibrePoint_comp, integralAdditivePoints_value]
  rfl

private theorem absoluteRootParameter_commute
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (i j : D.I) (hij : D.datum.pairing i j = 0)
    (c d : κ) (R : TestAlgebra κ) (a b : Multiplicative R) :
    Commute ((absoluteRootParameter (M := M) i c).app R a)
      ((absoluteRootParameter (M := M) j d).app R b) := by
  let p := (absoluteRootParameter (M := M) i c).app R a
  let q := (absoluteRootParameter (M := M) j d).app R b
  change p * q = q * p
  apply forgetFibrePoint_injective M.group R
  rw [forgetFibrePoint_mul, forgetFibrePoint_mul]
  have hp := absoluteRootParameter_value (M := M) i c R a.toAdd
  have hq := absoluteRootParameter_value (M := M) j d R b.toAdd
  change forgetFibrePoint M.group R p = _ at hp
  change forgetFibrePoint M.group R q = _ at hq
  rw [hp, hq]
  have h := ExceptionalMarkedRootDescent.markedOrthogonalRootCommutation M hsym i j hij κ R
    (upper (algebraMap κ R c * a.toAdd)) (Or.inl ⟨_, rfl⟩)
    (upper (algebraMap κ R d * b.toAdd)) (Or.inl ⟨_, rfl⟩)
  simpa only [M.rankOneUpper, markedRootPoint] using h.eq

private theorem prod_pointFactors_mul {I U V : Type*} [Monoid U] [Monoid V]
    (l : List I) (r : I → U →* V)
    (hc : l.Pairwise (fun i j => ∀ a b, Commute (r i a) (r j b))) (a b : U) :
    (l.map (fun i => r i (a * b))).prod =
      (l.map (fun i => r i a)).prod * (l.map (fun i => r i b)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    obtain ⟨h, ht⟩ := List.pairwise_cons.mp hc
    have he := Commute.list_prod_right (l.map (fun j => r j a)) (r i b) (fun _ hz => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
      exact h _ hj _ _)
    simp only [List.map_cons, List.prod_cons]
    rw [map_mul (r i), ih ht]
    let A := (l.map (fun j => r j a)).prod
    let B := (l.map (fun j => r j b)).prod
    change (r i a * r i b) * (A * B) = (r i a * A) * (r i b * B)
    calc
      _ = r i a * ((r i b * A) * B) := by simp only [mul_assoc]
      _ = _ := by rw [show r i b * A = A * r i b from he.eq]; simp only [mul_assoc]

private def orbitRootParameters (A : FoldedApartment (D := D) τ)
    (a : FoldedRootDirection) (c : D.I → κ)
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i) :
    StandardGroups.additivePoints κ ⟶ (groupPointsFunctor κ).obj (residueGroup M κ) where
  app R := GrpCat.ofHom
    { toFun := fun z => ((rootOrbit A a).toList.map (fun i =>
        (absoluteRootParameter (M := M) i (c i)).app R z)).prod
      map_one' := by
        change ((rootOrbit A a).toList.map (fun i =>
          ((absoluteRootParameter (M := M) i (c i)).app R).hom 1)).prod = _
        simp only [map_one, List.prod_map_one]
      map_mul' := by
        intro v w
        let l := (rootOrbit A a).toList
        let r i := ((absoluteRootParameter (M := M) i (c i)).app R).hom
        have hnd : l.Nodup := Finset.nodup_toList _
        refine prod_pointFactors_mul l r ?_ v w
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        have hi' : A.direction l[i] = a :=
          (mem_rootOrbit A a _).mp (Finset.mem_toList.mp (List.getElem_mem hi))
        have hj' : A.direction l[j] = a :=
          (mem_rootOrbit A a _).mp (Finset.mem_toList.mp (List.getElem_mem hj))
        have hne : l[i] ≠ l[j] := by
          intro h
          exact (Nat.ne_of_lt hij) (congrArg Fin.val (hnd.injective_get h))
        have hp : D.datum.pairing l[i] l[j] = 0 := by
          rcases (A.orbits l[i] l[j]).mp (hi'.trans hj'.symm) with e | e
          · exact (hne e.symm).elim
          · exact e.symm ▸ A.orthogonal l[i] (e ▸ hne.symm)
        exact absoluteRootParameter_commute hsym _ _ hp _ _ R }
  naturality {R S} f := by
    apply GrpCat.ext
    intro z
    change ((rootOrbit A a).toList.map (fun i =>
      (absoluteRootParameter (M := M) i (c i)).app S ((StandardGroups.additivePoints κ).map f z))).prod =
      ((groupPointsFunctor κ).obj (residueGroup M κ)).map f
        (((rootOrbit A a).toList.map (fun i => (absoluteRootParameter (M := M) i (c i)).app R z)).prod)
    rw [show ((groupPointsFunctor κ).obj (residueGroup M κ)).map f
        (((rootOrbit A a).toList.map (fun i => (absoluteRootParameter (M := M) i (c i)).app R z)).prod) =
        (((rootOrbit A a).toList.map (fun i =>
          ((groupPointsFunctor κ).obj (residueGroup M κ)).map f
            ((absoluteRootParameter (M := M) i (c i)).app R z)))).prod by
      exact ((groupPointsFunctor κ).obj (residueGroup M κ)).map f |>.hom.map_list_prod _ |>.trans
        (congrArg List.prod (List.map_map ..))]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    exact ConcreteCategory.congr_hom ((absoluteRootParameter (M := M) i (c i)).naturality f) z

open private fibrePointsEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem residueLine_affine : IsAffine ((fibre κ).obj M.line.group).X.left := by
  let _ : IsAffine M.line.group.X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial Integers.{u}))))
  exact fibre_isAffine M.line.group

private theorem residueLine_connected : GeometricallyConnected ((fibre κ).obj M.line.group).X.hom := by
  let _ := integralAdditiveLine_geometricallyConnected M.line
  change GeometricallyConnected (CategoryTheory.Limits.pullback.snd M.line.group.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} κ))))
  infer_instance

/-- The commuting marked root slots, evaluated at multiples of one
additive parameter, form one additive group homomorphism over the residue field. -/
theorem existsResidueLineMap (A : FoldedApartment τ) (a : FoldedRootDirection) (c : D.I → κ)
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i) :
    ∃ f : (fibre κ).obj M.line.group ⟶ residueGroup M κ,
      geometricImageOfHom M f = Set.range (fun z : AlgebraicClosure κ =>
        orbitRootValue (M := M) A a (fun i => algebraMap κ (AlgebraicClosure κ) (c i) * z)) := by
  let E := (fibre κ).obj M.line.group
  let e := LinearAlgebraicGroups.groupHomEquiv E (residueGroup M κ) residueLine_affine
  let t := (integralAdditiveLineFunctorIso κ M.line).inv ≫
    orbitRootParameters (M := M) A a c hsym
  let f := e.symm t
  let K := AlgebraicClosure κ
  let S := CommAlgCat.of κ K
  have he : (groupPointsFunctor κ).map f = t := e.apply_symm_apply t
  have hp (z : K) : forgetFibrePoint M.group S
      (integralAdditivePoints κ M.line S (Multiplicative.ofAdd z) ≫ f.hom.hom) =
        orbitRootValue (M := M) A a (fun i => algebraMap κ K (c i) * z) := by
    let p := integralAdditivePoints κ M.line S (Multiplicative.ofAdd z)
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app he S) p
    change p ≫ f.hom.hom =
      (orbitRootParameters (M := M) A a c hsym).app S
        ((integralAdditivePoints κ M.line S).symm p) at h
    rw [h, MulEquiv.symm_apply_apply]
    let l := (rootOrbit A a).toList
    let g (i : D.I) := (absoluteRootParameter (M := M) i (c i)).app S (Multiplicative.ofAdd z)
    change fibrePointsEquiv M.group S ((l.map g).prod) =
      (l.map (fun i => markedRootPoint M.toIntegralMarking (integralRing K) i
        (algebraMap κ K (c i) * z))).prod
    rw [map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    exact absoluteRootParameter_value (M := M) i (c i) S z
  refine ⟨f, ?_⟩
  ext w
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨z, rfl⟩ := (integralAdditivePoints κ M.line S).surjective p
    exact ⟨z.toAdd, (hp z.toAdd).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨integralAdditivePoints κ M.line S (Multiplicative.ofAdd z), hp z⟩


end ResidueLines

section ResidueTorus

open ExceptionalAffineRootSystems (e6Partner)
open IntegralSemisimpleModel (forgetFibrePoint)
open scoped Algebra.TensorProduct Matrix

variable {κ : Type u} [Field κ] {D : BasedRootDatum.{u}} {M : Model D}
  (τ : BasedIso D D) (numbering : Fin 6 ≃ D.base.support)
  (had : D.datum.rootSpan ℤ = ⊤)

open private fibrePointIso fibrePointsEquiv restrictToIntegers
  geometricallyConnected_spec_of_tensor_domain from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private splitGroupAlgebra_domain from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private markedTorusPoint_natural torusValues_ext_basis from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalRationalUnitTorus

private abbrev E6SimpleOrbit := ULift.{u} (Fin 4)

private def e6Orbit (i : Fin 6) : Fin 4 := ![0, 1, 2, 3, 2, 0] i

private def e6OrbitRepresentative (i : Fin 4) : Fin 6 := ![0, 1, 2, 3] i

private theorem e6Orbit_partner (i : Fin 6) : e6Orbit (e6Partner i) = e6Orbit i := by
  decide +revert

private theorem e6Orbit_representative (i : Fin 6) :
    e6OrbitRepresentative (e6Orbit i) = i ∨ e6OrbitRepresentative (e6Orbit i) = e6Partner i := by
  decide +revert

private def extendTorusTuple {I : Type u} {S : IntegralAlgebra.{u}}
    (b : Module.Basis I ℤ D.X) (q : I → Sˣ) : TorusValues D S :=
  let f : D.X →ₗ[ℤ] Additive Sˣ := b.constr ℤ (fun i => Additive.ofMul (q i))
  { toFun χ := (f χ.toAdd).toMul
    map_one' := f.map_zero
    map_mul' x y := f.map_add x.toAdd y.toAdd }

private theorem extendTorusTuple_basis {I : Type u} {S : IntegralAlgebra.{u}}
    (b : Module.Basis I ℤ D.X) (q : I → Sˣ) (i : I) :
    extendTorusTuple b q (Multiplicative.ofAdd (b i)) = q i :=
  b.constr_basis ℤ (fun i => Additive.ofMul (q i)) i

private def extendOrbitTuple (S : IntegralAlgebra.{u}) (q : E6SimpleOrbit → Sˣ) :
    TorusValues D S :=
  extendTorusTuple (simpleRootBasis had) (fun i => q ⟨e6Orbit (numbering.symm i)⟩)

private theorem extendOrbitTuple_numbering {S : IntegralAlgebra.{u}} (q : E6SimpleOrbit → Sˣ)
    (i : Fin 6) :
    extendOrbitTuple numbering had S q (Multiplicative.ofAdd (simpleRootBasis had (numbering i))) =
      q ⟨e6Orbit i⟩ := by
  change extendTorusTuple (simpleRootBasis had) (fun j => q ⟨e6Orbit (numbering.symm j)⟩)
    (Multiplicative.ofAdd (simpleRootBasis had (numbering i))) = _
  rw [extendTorusTuple_basis, Equiv.symm_apply_apply]

private theorem extendOrbitTuple_invariant
    (hτ : ∀ i, τ.val.indexEquiv (numbering i) = numbering (e6Partner i))
    {S : IntegralAlgebra.{u}} (q : E6SimpleOrbit → Sˣ) :
    ∀ χ : D.X, extendOrbitTuple numbering had S q (Multiplicative.ofAdd (τ.val.weightEquiv χ)) =
      extendOrbitTuple numbering had S q (Multiplicative.ofAdd χ) := by
  let b := simpleRootBasis had
  let t := extendOrbitTuple numbering had S q
  let f := τ.val.weightEquiv.toLinearMap.toAddMonoidHom.toMultiplicative
  suffices h : t.comp f = t from fun χ => DFunLike.congr_fun h (Multiplicative.ofAdd χ)
  apply torusValues_ext_basis b
  intro j
  obtain ⟨i, rfl⟩ := numbering.surjective j
  change t (Multiplicative.ofAdd (τ.val.weightEquiv (b (numbering i)))) =
    t (Multiplicative.ofAdd (b (numbering i)))
  have he : τ.val.weightEquiv (b (numbering i)) = b (numbering (e6Partner i)) := by
    change τ.val.weightEquiv (simpleRootBasis had (numbering i)) = _
    have hb (j : D.base.support) : b j = D.datum.root j := Module.Basis.mk_apply _ _ _
    change τ.val.weightEquiv (b (numbering i)) = b _
    rw [hb, hb]
    exact (RootPairing.Hom.root_weightMap_apply D.datum D.datum (numbering i) τ.val.toHom).trans
      (congrArg D.datum.root (hτ i))
  rw [he, extendOrbitTuple_numbering, extendOrbitTuple_numbering, e6Orbit_partner]

private theorem invariantTuple_extendOrbitTuple
    (hτ : ∀ i, τ.val.indexEquiv (numbering i) = numbering (e6Partner i))
    {S : IntegralAlgebra.{u}} (t : TorusValues D S)
    (ht : ∀ χ : D.X, t (Multiplicative.ofAdd (τ.val.weightEquiv χ)) = t (Multiplicative.ofAdd χ)) :
    ∃ q : E6SimpleOrbit → Sˣ, extendOrbitTuple numbering had S q = t := by
  let b := simpleRootBasis had
  let q (o : E6SimpleOrbit) :=
    t (Multiplicative.ofAdd (b (numbering (e6OrbitRepresentative o.down))))
  refine ⟨q, ?_⟩
  apply torusValues_ext_basis b
  intro j
  obtain ⟨i, rfl⟩ := numbering.surjective j
  rw [extendOrbitTuple_numbering]
  obtain h | h := e6Orbit_representative i
  · exact congrArg (fun z => t (Multiplicative.ofAdd (b (numbering z)))) h
  · have he : b (numbering (e6Partner i)) = τ.val.weightEquiv (b (numbering i)) := by
      have hb (j : D.base.support) : b j = D.datum.root j := Module.Basis.mk_apply _ _ _
      rw [hb, hb]
      exact ((RootPairing.Hom.root_weightMap_apply D.datum D.datum (numbering i) τ.val.toHom).trans
        (congrArg D.datum.root (hτ i))).symm
    change t (Multiplicative.ofAdd (b (numbering (e6OrbitRepresentative (e6Orbit i))))) = _
    rw [h, he]
    exact ht (b (numbering i))

private def invariantTorusPoints :
    StandardGroups.multiplicativePowerPoints κ E6SimpleOrbit ⟶
      restrictToIntegers κ ⋙ integralPointFunctor M.group where
  app R := GrpCat.ofHom ((markedTorusPointHom M.toIntegralMarking ((restrictToIntegers κ).obj R)).comp
    { toFun := extendOrbitTuple numbering had ((restrictToIntegers κ).obj R)
      map_one' := by
        apply torusValues_ext_basis (simpleRootBasis had)
        intro j
        obtain ⟨i, rfl⟩ := numbering.surjective j
        rw [extendOrbitTuple_numbering]
        rfl
      map_mul' := by
        intro p q
        apply torusValues_ext_basis (simpleRootBasis had)
        intro j
        obtain ⟨i, rfl⟩ := numbering.surjective j
        rw [extendOrbitTuple_numbering]
        show (p * q) ⟨e6Orbit i⟩ = _
        exact (congrArg₂ (· * ·) (extendOrbitTuple_numbering numbering had (S := (restrictToIntegers κ).obj R) p i)
          (extendOrbitTuple_numbering numbering had (S := (restrictToIntegers κ).obj R) q i)).symm })
  naturality {R S} f := by
    apply GrpCat.ext
    intro p
    let e := (restrictToIntegers κ).map f
    let t := extendOrbitTuple numbering had ((restrictToIntegers κ).obj R) p
    let q := fun i : E6SimpleOrbit => Units.map f.hom.toMonoidHom (p i)
    let s := extendOrbitTuple numbering had ((restrictToIntegers κ).obj S) q
    change torusPoint D ((restrictToIntegers κ).obj S) s ≫ M.torus.hom.hom =
      changeRing e (torusPoint D ((restrictToIntegers κ).obj R) t ≫ M.torus.hom.hom)
    symm
    rw [markedTorusPoint_natural]
    apply congrArg (fun v => torusPoint D ((restrictToIntegers κ).obj S) v ≫ M.torus.hom.hom)
    apply torusValues_ext_basis (simpleRootBasis had)
    intro j
    obtain ⟨i, rfl⟩ := numbering.surjective j
    change Units.map e.hom.toRingHom
        (extendOrbitTuple numbering had ((restrictToIntegers κ).obj R) p
          (Multiplicative.ofAdd (simpleRootBasis had (numbering i)))) =
      extendOrbitTuple numbering had ((restrictToIntegers κ).obj S) q
        (Multiplicative.ofAdd (simpleRootBasis had (numbering i)))
    rw [extendOrbitTuple_numbering, extendOrbitTuple_numbering]
    rfl

private theorem residueOrbitTorus_connected :
    GeometricallyConnected (StandardGroups.multiplicativePowerGroup κ E6SimpleOrbit).val.X.hom := by
  let I := E6SimpleOrbit
  let A := AddMonoidAlgebra κ (I → ℤ)
  let X := Multiplicative (I → ℤ)
  change GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap κ A)))
  apply geometricallyConnected_spec_of_tensor_domain
  intro K _ _
  let e₀ := (AddMonoidAlgebra.toMultiplicativeBialgEquiv κ κ (I → ℤ)).toAlgEquiv
  let e := (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e₀).toRingEquiv.trans
    (MonoidAlgebra.scalarTensorEquiv κ K (M := X)).toRingEquiv
  letI : IsDomain (MonoidAlgebra K X) := splitGroupAlgebra_domain
  exact e.injective.isDomain e

include had in
set_option maxHeartbeats 2000000 in
/-- The invariant unit tuples are the image of a morphism from the four
split factors indexed by the simple-root orbits. -/
theorem existsResidueTorusMap
    (hτ : ∀ i, τ.val.indexEquiv (numbering i) = numbering (e6Partner i)) :
    ∃ (T : GroupScheme κ) (f : T ⟶ residueGroup M κ),
      GeometricRadicals.IsSplitTorus T ∧ GeometricallyConnected T.X.hom ∧
      LocallyOfFiniteType T.X.hom ∧ QuasiCompact T.X.hom ∧
      geometricImageOfHom M f =
        Set.range (fun t : InvariantTorusValues τ (AlgebraicClosure κ) =>
          (show FieldPoints M (AlgebraicClosure κ) from
            torusPoint D (integralRing (AlgebraicClosure κ)) t.val ≫ M.torus.hom.hom)) := by
  classical
  let T := StandardGroups.multiplicativePowerGroup κ E6SimpleOrbit
  obtain ⟨_, _, _, _, _, c, _⟩ :=
    LinearAlgebraicGroups.StandardGroups.multiplicativePowerSpecification κ E6SimpleOrbit
  let i := invariantTorusPoints (κ := κ) (M := M) numbering had
  let t := c.hom ≫ i ≫ (fibrePointIso (k := κ) M.group).inv
  let e := LinearAlgebraicGroups.groupHomEquiv T.val (residueGroup M κ) T.property.1
  let f := e.symm t
  refine ⟨T.val, f, ⟨4, ⟨Iso.refl _⟩⟩, residueOrbitTorus_connected,
    T.property.2.1, T.property.2.2, ?_⟩
  let K := AlgebraicClosure κ
  let S := CommAlgCat.of κ K
  let p (s : GroupPoints T.val S) : E6SimpleOrbit → Kˣ := c.hom.app S s
  have h (s : GroupPoints T.val S) :
      forgetFibrePoint M.group S (s ≫ f.hom.hom) =
        (torusPoint D (integralRing K) (extendOrbitTuple numbering had (integralRing K) (p s))
          ≫ M.torus.hom.hom : FieldPoints M K) := by
    have he : (groupPointsFunctor κ).map f = t := e.apply_symm_apply t
    have h' := ConcreteCategory.congr_hom (NatTrans.congr_app he S) s
    change s ≫ f.hom.hom = (fibrePointsEquiv M.group S).symm
      (torusPoint D (integralRing K) (extendOrbitTuple numbering had (integralRing K) (p s)) ≫
        M.torus.hom.hom) at h'
    rw [h']
    exact (fibrePointsEquiv M.group S).apply_symm_apply _
  ext w
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨_, extendOrbitTuple_invariant τ numbering had hτ (S := integralRing K) (p s)⟩, (h s).symm⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨v, hv⟩ := invariantTuple_extendOrbitTuple τ numbering had hτ (S := integralRing K) q.val q.property
    have hsurj : Function.Surjective p := (c.app S).groupIsoToMulEquiv.surjective
    obtain ⟨s, hs⟩ := hsurj v
    refine ⟨s, ?_⟩
    exact (h s).trans (congrArg (fun t => torusPoint D (integralRing K) t ≫ M.torus.hom.hom)
      ((congrArg (extendOrbitTuple numbering had (integralRing K)) hs).trans hv))

end ResidueTorus

section RootResidueCoordinates

open ExceptionalIwahoriCongruence (cellValue)
open RamifiedExceptionalLocalFaceCoordinates (LeadingCoefficients rootResiduePoint)

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  (X : MarkedLevel R σ A k) {ϖ : Fˣ} {π : Lˣ}
  (a : FoldedRootDirection × ℤ) (B : LeadingCoefficients X ϖ π a)

private def absoluteMarkingUnit (i : D.I) : Integers.{u}ˣ :=
  let C := X.folded.comparison.chart
  if hn : i ∈ C.negative then
    C.chart.negUnit ⟨C.negative.idxOf i, List.idxOf_lt_length_of_mem hn⟩
  else if hp : i ∈ C.positive then
    C.chart.posUnit ⟨C.positive.idxOf i, List.idxOf_lt_length_of_mem hp⟩
  else 1

private theorem absoluteMarkingUnit_neg (i : Fin X.folded.comparison.chart.negative.length) :
    absoluteMarkingUnit X X.folded.comparison.chart.negative[i] =
      X.folded.comparison.chart.chart.negUnit i := by
  let C := X.folded.comparison.chart
  have h : C.negative[i] ∈ C.negative := List.getElem_mem i.isLt
  have he : (⟨C.negative.idxOf C.negative[i], List.idxOf_lt_length_of_mem h⟩ :
      Fin C.negative.length) = i :=
    C.negative_enumerates.1.injective_get (List.getElem_idxOf _)
  unfold absoluteMarkingUnit
  dsimp only
  change X.folded.comparison.chart.negative[i] ∈ X.folded.comparison.chart.negative at h
  split
  · exact congrArg C.chart.negUnit he
  next hn => exact (hn h).elim

private theorem absoluteMarkingUnit_pos (i : Fin X.folded.comparison.chart.positive.length) :
    absoluteMarkingUnit X X.folded.comparison.chart.positive[i] =
      X.folded.comparison.chart.chart.posUnit i := by
  let C := X.folded.comparison.chart
  have h : C.positive[i] ∈ C.positive := List.getElem_mem i.isLt
  have hn : C.positive[i] ∉ C.negative := fun h' => (C.negative_enumerates.2 _).mp h'
    ((C.positive_enumerates.2 _).mp h)
  have he : (⟨C.positive.idxOf C.positive[i], List.idxOf_lt_length_of_mem h⟩ :
      Fin C.positive.length) = i :=
    C.positive_enumerates.1.injective_get (List.getElem_idxOf _)
  unfold absoluteMarkingUnit
  dsimp only
  change X.folded.comparison.chart.positive[i] ∉ X.folded.comparison.chart.negative at hn
  change X.folded.comparison.chart.positive[i] ∈ X.folded.comparison.chart.positive at h
  split
  next hm => exact (hn hm).elim
  next _ => exact congrArg C.chart.posUnit he

private def rootResidueVector (i : D.I) : kᵥ[X.compositum.field] :=
  if A.direction i = a.1 then
    algebraMap Integers.{u} _ (absoluteMarkingUnit X i : Integers.{u}) * (B.factor i : kᵥ[X.compositum.field])
  else 0

private theorem rootResidueVector_zero (i : D.I) (hi : A.direction i ≠ a.1) :
    rootResidueVector X a B i = 0 := ite_eq_right hi

private theorem rootResidueVector_ne_zero (i : D.I) (hi : A.direction i = a.1) :
    rootResidueVector X a B i ≠ 0 := by
  rw [rootResidueVector, ite_eq_left hi]
  exact mul_ne_zero (((absoluteMarkingUnit X i).isUnit.map (algebraMap Integers.{u}
    kᵥ[X.compositum.field])).ne_zero) (Units.ne_zero (B.factor i))

private theorem rootResiduePoint_eq_orbit
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    {K : Type u} [Field K] (e : kᵥ[X.compositum.field] →+* K) (z : K) :
    rootResiduePoint X ϖ π a B e z =
      orbitRootValue (M := M) A a.1 (fun i => e (rootResidueVector X a B i) * z) := by
  let C := X.folded.comparison.chart
  let v (i : D.I) := e (rootResidueVector X a B i) * z
  have hv (i : D.I) (hi : A.direction i ≠ a.1) : v i = 0 := by
    unfold v
    rw [rootResidueVector_zero X a B i hi, map_zero, zero_mul]
  rw [← cellValue_ofOrbit A hsym C.negative C.positive C.negative_enumerates
    C.positive_enumerates a.1 v hv]
  have hslot (i : D.I) (w : Integers.{u}ˣ) (hw : absoluteMarkingUnit X i = w) :
      (if A.direction i = a.1 then
        algebraMap Integers.{u} K (w : Integers.{u}) * e (B.factor i) * z else 0) = v i := by
    unfold v rootResidueVector
    by_cases hi : A.direction i = a.1
    · rw [ite_eq_left hi, ite_eq_left hi, hw, map_mul]
      have e₀ (m : Integers.{u}) : e (algebraMap Integers.{u} kᵥ[X.compositum.field] m) =
          algebraMap Integers.{u} K m := map_intCast e m.down
      rw [e₀]
    · rw [ite_eq_right hi, ite_eq_right hi, map_zero, zero_mul]
  unfold rootResiduePoint
  dsimp only
  congr 1
  apply Prod.ext
  · funext i
    exact hslot C.negative[i] (C.chart.negUnit i) (absoluteMarkingUnit_neg X i)
  · apply Prod.ext
    · rfl
    · funext i
      exact hslot C.positive[i] (C.chart.posUnit i) (absoluteMarkingUnit_pos X i)

end RootResidueCoordinates

section RootOrbitInjection

open ExceptionalIwahoriCongruence (cellValue)
open private rootOrderings_exist from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

variable {D : BasedRootDatum.{u}} {M : Model D} {τ : BasedIso D D}
  (A : FoldedApartment τ) {K : Type u} [Field K]

private theorem orbitRootValue_inj
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (a : FoldedRootDirection) {u v : D.I → K}
    (hu : ∀ i, A.direction i ≠ a → u i = 0)
    (hv : ∀ i, A.direction i ≠ a → v i = 0)
    (h : orbitRootValue (M := M) A a u = orbitRootValue (M := M) A a v) :
    u = v := by
  obtain ⟨n, p, hn, hp⟩ := rootOrderings_exist D
  have h₀ := cellValue_ofOrbit (M := M) A hsym n p hn hp a u hu
  have h₁ := cellValue_ofOrbit (M := M) A hsym n p hn hp a v hv
  have he := RamifiedExceptionalLocalFaceCoordinates.cellValue_injective M.toIntegralMarking
    (integralRing K) n p hn hp (h₀.trans (h.trans h₁.symm))
  funext i
  by_cases hi : D.base.IsPos i
  · obtain ⟨j, hj⟩ := List.get_of_mem ((hp.2 i).mpr hi)
    have hq := congrFun (congrArg (fun t => t.2.2) he) j
    change u p[j] = v p[j] at hq
    exact (congrArg u hj).symm.trans (hq.trans (congrArg v hj))
  · obtain ⟨j, hj⟩ := List.get_of_mem ((hn.2 i).mpr hi)
    have hq := congrFun (congrArg Prod.fst he) j
    change u n[j] = v n[j] at hq
    exact (congrArg u hj).symm.trans (hq.trans (congrArg v hj))

end RootOrbitInjection

section GeometricRootLines

open RamifiedExceptionalLocalFaceCoordinates (rootResiduePoint)

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  (P : ScaledParahoricTower X J π d y)
  {ϖ : Fˣ} {x : invariantApartment D (R.diagram σ)}
  (Q : ∀ k, LocalReductionCoordinates (P.scale k) ϖ x)
  (a : residueRootDirections A J x)

private theorem rootReduction_range
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (k : UnramifiedLevel F S) :
    (P.scale k).image ((X k).rootLayer a.val) =
      Set.range (rootResiduePoint (X k) ϖ π a.val ((Q k).leading a.val)
        (residueMap (X k).compositum.field (P.auxiliary.extension k).field)) := by
  rcases a.property with h | h
  · exact (iwahoriRootReduction P Q hy hπ hd k ⟨a.val, h⟩).2
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
    obtain ⟨hb₀, hw⟩ := Set.mem_iUnion.mp hb
    obtain ⟨_, _, _, _, he⟩ := (Q k).wall b hb₀
    exact (he a.val hw).2

private def leadingGeometricVector (k : UnramifiedLevel F S) (i : D.I) :
    AlgebraicClosure kᵥ[F] :=
  (P.auxiliary.diagramResidueEmbedding k) (rootResidueVector (X k) a.val ((Q k).leading a.val) i)

private theorem leadingGeometricVector_zero (k : UnramifiedLevel F S)
    (i : D.I) (hi : A.direction i ≠ a.val.1) :
    leadingGeometricVector P Q a k i = 0 := by
  unfold leadingGeometricVector
  rw [rootResidueVector_zero _ _ _ i hi, map_zero]

private theorem leadingGeometricVector_ne_zero (k : UnramifiedLevel F S)
    (i : D.I) (hi : A.direction i = a.val.1) :
    leadingGeometricVector P Q a k i ≠ 0 :=
  (map_ne_zero (P.auxiliary.diagramResidueEmbedding k)).2 (rootResidueVector_ne_zero _ _ _ i hi)

private theorem geometricRootStage_iff
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (k : UnramifiedLevel F S) (z : FieldPoints M (AlgebraicClosure kᵥ[F])) :
    (∃ g : (X k).parahoric J, g.val ∈ (X k).rootLayer a.val ∧ P.geometricReduction k g = z) ↔
      ∃ v : kᵥ[(P.auxiliary.extension k).field], orbitRootValue (M := M) A a.val.1
        (fun i => leadingGeometricVector P Q a k i * P.auxiliary.residueEmbedding k v) = z := by
  let K := (X k).compositum.field
  let E := (P.auxiliary.extension k).field
  let ρ := residueMap K E
  let e := P.auxiliary.residueEmbedding k
  have h (v : kᵥ[E]) : scalarPoints M e (rootResiduePoint (X k) ϖ π a.val ((Q k).leading a.val) ρ v) =
      orbitRootValue (M := M) A a.val.1
        (fun i => leadingGeometricVector P Q a k i * e v) := by
    rw [rootResiduePoint_eq_orbit _ _ _ hsym, orbitRootValue_scalar]
    apply congrArg (orbitRootValue (M := M) A a.val.1)
    funext i
    exact map_mul e _ _
  have hq := rootReduction_range P Q a hy hπ hd k
  constructor
  · rintro ⟨g, hg, rfl⟩
    have he : (P.scale k).reduction g ∈ (P.scale k).image ((X k).rootLayer a.val) := ⟨g, hg, rfl⟩
    rw [hq] at he
    obtain ⟨v, hv⟩ := he
    exact ⟨v, (h v).symm.trans (congrArg (scalarPoints M e) hv)⟩
  · rintro ⟨v, rfl⟩
    have he : rootResiduePoint (X k) ϖ π a.val ((Q k).leading a.val) ρ v ∈
        (P.scale k).image ((X k).rootLayer a.val) := hq.symm ▸ ⟨v, rfl⟩
    obtain ⟨g, hg, he⟩ := he
    exact ⟨g, hg, (congrArg (scalarPoints M e) he).trans (h v)⟩

private theorem rootVectors_proportional
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (k : UnramifiedLevel F S) :
    ∃ v : kᵥ[(P.auxiliary.extension k).field], v ≠ 0 ∧
      ∀ i, leadingGeometricVector P Q a P.auxiliary.base i =
        leadingGeometricVector P Q a k i * P.auxiliary.residueEmbedding k v := by
  let b := P.auxiliary.base
  let u := leadingGeometricVector P Q a b
  let z := orbitRootValue (M := M) A a.val.1 u
  have hz : ∃ g : (X b).parahoric J, g.val ∈ (X b).rootLayer a.val ∧ P.geometricReduction b g = z := by
    apply (geometricRootStage_iff P Q a hsym hy hπ hd b z).mpr
    refine ⟨1, ?_⟩
    simp only [z, u, map_one, mul_one]
  obtain ⟨g, hg, hg'⟩ := hz
  let h := base_le P k
  let e := P.auxiliary.transition h
  let π₀ := algebraMap L (X b).compositum.field (π : L)
  have hπ₀ : normalizedValuation (X b).compositum.field π₀ = exp (-1) :=
    ((X b).compositum.unramified _).trans hπ
  have hπ₁ : normalizedValuation (X k).compositum.field (e.diagram π₀) = exp (-1) :=
    (congrArg (normalizedValuation (X k).compositum.field) (e.diagram_left _)).trans
      (((X k).compositum.unramified _).trans hπ)
  have hv := normalizedValuation_map_of_uniformizer e.diagramValued _ hπ₀ hπ₁
  let g' := faceInclusion X h J (P.face_comap h) g
  have hLayer : g'.val ∈ (X k).rootLayer a.val :=
    rootLayer_scalar (X b) (X k) hsym _ e.diagram hv e.diagram_left e.diagram_right a.val hg
  have hz' := (geometricRootStage_iff P Q a hsym hy hπ hd k z).mp
    ⟨g', hLayer, (geometricReduction_natural P h g).trans hg'⟩
  obtain ⟨v, hv⟩ := hz'
  have huv := orbitRootValue_inj (M := M) A hsym a.val.1
    (leadingGeometricVector_zero P Q a b)
    (fun i hi => (congrArg (· * P.auxiliary.residueEmbedding k v)
      (leadingGeometricVector_zero P Q a k i hi)).trans (zero_mul _))
    hv.symm
  refine ⟨v, ?_, fun i => congrFun huv i⟩
  intro hv₀
  obtain ⟨i, hi⟩ := A.surjective a.val.1
  apply leadingGeometricVector_ne_zero P Q a b i hi
  simpa only [hv₀, map_zero, mul_zero] using congrFun huv i

private theorem geometricRootImage_as_base_vector
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d) :
    P.rootImage a.val = Set.range (fun z : AlgebraicClosure kᵥ[F] => orbitRootValue (M := M) A a.val.1
      (fun i => leadingGeometricVector P Q a P.auxiliary.base i * z)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨k, g, hg, rfl⟩ := (mem_geometricImage P _ v).1 hv
    obtain ⟨t, ht⟩ := (geometricRootStage_iff P Q a hsym hy hπ hd k _).1 ⟨g, hg, rfl⟩
    obtain ⟨w, hw, hq⟩ := rootVectors_proportional P Q a hsym hy hπ hd k
    let e := P.auxiliary.residueEmbedding k
    refine ⟨e t / e w, ?_⟩
    refine (congrArg (orbitRootValue (M := M) A a.val.1) (funext fun i => ?_)).trans ht
    change leadingGeometricVector P Q a P.auxiliary.base i * (e t / e w) =
      leadingGeometricVector P Q a k i * e t
    rw [hq i, mul_assoc]
    exact congrArg (leadingGeometricVector P Q a k i * ·)
      ((mul_comm (e w) (e t / e w)).trans (div_mul_cancel₀ _ ((map_ne_zero e).2 hw)))
  · rintro ⟨z, rfl⟩
    obtain ⟨k, v, hv⟩ := P.auxiliary.residue_exhaustive (fun _ : PUnit.{u + 1} => z)
    obtain ⟨w, _, hw⟩ := rootVectors_proportional P Q a hsym hy hπ hd k
    apply (mem_geometricImage P _ _).2
    let e := P.auxiliary.residueEmbedding k
    have h (i : D.I) : leadingGeometricVector P Q a k i * e (w * v PUnit.unit) =
        leadingGeometricVector P Q a P.auxiliary.base i * z := by
      rw [map_mul e, show e (v PUnit.unit) = z from hv PUnit.unit, hw i, mul_assoc]
    obtain ⟨g, hg, hred⟩ := (geometricRootStage_iff P Q a hsym hy hπ hd k _).2
      ⟨w * v PUnit.unit, congrArg (orbitRootValue (M := M) A a.val.1) (funext h)⟩
    exact ⟨k, g, hg, hred⟩

include Q in
/-- A surviving Iwahori direction or a signed wall has one geometric
residue line. Its base coefficient vector defines that line over κ. -/
theorem existsGeometricRootMap
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d) :
    ∃ f : (fibre kᵥ[F]).obj M.line.group ⟶ residueGroup M kᵥ[F],
      geometricImageOfHom M f = P.rootImage a.val := by
  let k := P.auxiliary.base
  let K := (X k).compositum.field
  let b := (residueMap k.field K).comp (residueMap F k.field)
  have hb : Function.Bijective b := ⟨b.injective,
    (P.auxiliary.coefficientResidue_bijective k).2.comp (baseResidue_surjective P)⟩
  let e := RingEquiv.ofBijective b hb
  let v := rootResidueVector (X k) a.val ((Q k).leading a.val)
  let c := fun i => e.symm (v i)
  have hc (i : D.I) : algebraMap kᵥ[F] (AlgebraicClosure kᵥ[F]) (c i) =
      leadingGeometricVector P Q a k i := by
    have h := DFunLike.congr_fun (P.auxiliary.residue_base k) (c i)
    change P.auxiliary.diagramResidueEmbedding k (b (c i)) =
      algebraMap kᵥ[F] (AlgebraicClosure kᵥ[F]) (c i) at h
    have he : b (c i) = v i := e.apply_symm_apply _
    exact h.symm.trans (congrArg (P.auxiliary.diagramResidueEmbedding k) he)
  obtain ⟨f, hf⟩ := existsResidueLineMap (M := M) A a.val.1 c hsym
  refine ⟨f, ?_⟩
  rw [hf, geometricRootImage_as_base_vector P Q a hsym hy hπ hd]
  apply congrArg Set.range
  funext z
  exact congrArg (orbitRootValue (M := M) A a.val.1) (funext fun i => congrArg (· * z) (hc i))

end GeometricRootLines



section GroupedIwahori

open ExceptionalAffineBruhat (ExceptionalNumbering)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalFoldedRootChart (OrbitOrdering slotMap slotUnit parameterField)
open ExceptionalMarkedRootDescent (TransportedOrbit transportedLabels markedRootPoint orderedRootPoint pinnedDiagram)
open ExceptionalIwahoriCongruence (CellValues cellValue)
open OrderedRootProducts (Enumerates)
open private FoldedOrdering FoldedOrdering.order FoldedOrdering.nodup FoldedOrdering.simple FoldedOrdering.word
  foldedOrdering foldedCompositumReference
  FoldedCoefficientReference.fibre FoldedCoefficientReference.descent FoldedCoefficientReference.points
  FoldedCoefficientReference.point_eq FoldedCoefficientReference.same_diagram FoldedCoefficientReference.sequence
  foldedSimpleOrbitMatches integralOrbitTransportUnits from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private firstLabel firstLabel_mem blockDirection blocks_nodup cellValue_values from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedRootChart
open private cellValue_supported absoluteCell rationalChart_single from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalOppositeWallLayer
open private iwahori_cell from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedScalarTransport
open private cellValue_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private existsValuationTorus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
open RamifiedExceptionalLocalFaceCoordinates (localRootChart_injective)
open LinearAlgebraicGroups.RamifiedExceptionalRationalUnitTorus (rationalUnitTorusComparison)

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}

private def blockDirectionOf (A : FoldedApartment (D := D) (R.diagram σ)) (b : TransportedOrbit D) :=
  A.direction (firstLabel b)

private theorem order_block_eq (o : OrbitOrdering A.direction) {b : TransportedOrbit D}
    (hb : b ∈ o.negative ++ o.positive) : o.block (blockDirectionOf A b) = b := by
  obtain ⟨a, rfl⟩ := o.ordered b hb
  rw [show blockDirectionOf A (o.block a) = a from blockDirection o a]

private theorem orderedBlocks_support (o : OrbitOrdering A.direction) {b : TransportedOrbit D}
    (hb : b ∈ o.negative ++ o.positive) (i : D.I) :
    i ∈ transportedLabels b ↔ A.direction i = blockDirectionOf A b := by
  conv_lhs => rw [← order_block_eq o hb]
  exact o.fibre _ i

private theorem iwahoriOrbit_mem_rootLayer (X : MarkedLevel R σ A k)
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i)
    (a : FoldedRootDirection) (g : GroupPoints R.descent.group.val (CommAlgCat.of F k))
    (hg : g ∈ X.folded.comparison.I) (v : D.I → X.compositum.field)
    (hv : ∀ i, A.direction i ≠ a → v i = 0)
    (he : X.folded.points g = orbitRootValue (M := M) A a v) :
    g ∈ X.rootLayer (X.iwahoriDepth a) := by
  classical
  let K := X.compositum.field
  let C := X.folded.comparison.chart
  have hc : cellValue M.toIntegralMarking (integralRing K) C.negative C.positive (absoluteCell C v 1) =
      orbitRootValue (M := M) A a v :=
    cellValue_ofOrbit A hsym C.negative C.positive C.negative_enumerates C.positive_enumerates a v hv
  have hsurj : Function.Surjective C.direction := X.folded.directions ▸ A.surjective
  obtain ⟨t, ht⟩ := identityChartTorus A C
  obtain ⟨z, hz⟩ := rationalChart_single C hsurj t ht a v
    (fun i hi => hv i (fun h => hi ((congrFun X.folded.directions i).trans h))) ⟨g, he.trans hc.symm⟩
  have hpoint : X.folded.points g = cellValue M.toIntegralMarking (integralRing K) C.negative C.positive
      (C.chart.coordinates t (Function.update (fun _ => 0) a z)) :=
    (he.trans hc.symm).trans (congrArg (cellValue M.toIntegralMarking _ _ _) hz.symm)
  obtain ⟨w, hw, _⟩ := (X.folded.bruhat.base_chart g).mp hg
  have hcompare : (t, Function.update (fun _ => 0) a z) = w :=
    localRootChart_injective C hsurj (hpoint.symm.trans hw.1.symm)
  have hdepth := congrArg (fun v : C.chart.torus × (∀ i, C.parameter i) => v.2 a) hcompare
  change Function.update (fun _ => 0) a z a = w.2 a at hdepth
  rw [Function.update_self] at hdepth
  exact ⟨t, z, ht, hdepth ▸ hw.2.2 a, hpoint⟩

open scoped CategoryTheory.MonoidalCategory
open Specs.ExceptionalIwahoriImageComparison (pinnedGroundPoint)

set_option maxHeartbeats 2500000 in
private theorem groupedChart_rational (X : MarkedLevel R σ A k)
    (hdeg : Module.finrank F L = 2) (hσ : σ ≠ 1) (had : D.datum.rootSpan ℤ = ⊤)
    (numbering : Fin 6 ≃ D.base.support) (hnum : ExceptionalNumbering D 6 numbering)
    (hτ : ∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i))
    (o : FoldedOrdering A) :
    ∃ u : TransportedOrbit D → D.I → Integers.{u}ˣ,
      let T := X.compositum
      let ord := FoldedOrdering.order o
      ∀ z : CellValues D (integralRing T.field) (ord.negative.flatMap transportedLabels)
          (ord.positive.flatMap transportedLabels),
        cellValue M.toIntegralMarking (integralRing T.field) _ _ z ∈ X.folded.points.range ↔
          ∃ t v, (torusPoint D (integralRing T.field) t ≫ M.torus.hom.hom) ∈
            X.folded.points.range ∧ ord.coordinates u T.diagram t v = z := by
  let T := X.compositum
  let ord := FoldedOrdering.order o
  obtain ⟨C⟩ := foldedCompositumReference R σ hdeg hσ (Or.inr had) T
  let e := FoldedCoefficientReference.points C
  let j := X.folded.points.comp e.symm.toMonoidHom
  have hj (g) : j g = pinnedGroundPoint (FoldedCoefficientReference.fibre C)
      (FoldedCoefficientReference.descent C).data g := by
    have h := (X.folded.point_eq (e.symm g)).trans (FoldedCoefficientReference.point_eq C (e.symm g)).symm
    exact h.trans (congrArg (pinnedGroundPoint (FoldedCoefficientReference.fibre C)
      (FoldedCoefficientReference.descent C).data) (e.apply_symm_apply g))
  have hrange : j.range = X.folded.points.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective, Subgroup.map_top]
  obtain ⟨hInv, _, hSym⟩ := LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat.e6LocalRootSymmetries D numbering (R.diagram σ) hnum hτ
  have hs := foldedSimpleOrbitMatches (FoldedCoefficientReference.fibre C)
    (FoldedCoefficientReference.sequence C) (FoldedCoefficientReference.descent C) T.diagram
  dsimp only at hs
  rw [FoldedCoefficientReference.same_diagram C] at hs
  specialize hs A hInv hSym
  have hmat (b : TransportedOrbit D) (hb : b ∈ ord.negative ++ ord.positive) :
      b.1.Matches (FoldedCoefficientReference.fibre C)
          (pinnedDiagram (FoldedCoefficientReference.descent C).data T.diagram) ∧
      ∀ v ∈ b.2, v.Matches (FoldedCoefficientReference.fibre C)
          (pinnedDiagram (FoldedCoefficientReference.descent C).data T.diagram) := by
    obtain ⟨a, rfl⟩ := ord.ordered b hb
    refine ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := FoldedOrdering.simple o a
      rw [hi]
      exact hs i
    · intro v hv
      obtain ⟨i, rfl⟩ := FoldedOrdering.word o a v hv
      exact hs i
  obtain ⟨units, hu⟩ := integralOrbitTransportUnits M
  refine ⟨units, ?_⟩
  dsimp only
  intro z
  have h := LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedRootChart.foldedOrderedChart
    (FoldedCoefficientReference.fibre C) (FoldedCoefficientReference.descent C).data T.diagram
    T.degree T.diagram_ne hSym A.direction ord hmat units hu j hj z
  rwa [hrange] at h

set_option maxHeartbeats 2100000 in
private theorem blockValue_eq_orbit {K : Type u} [Field K]
    (hsym : ∀ i j, D.datum.pairing i j = D.datum.pairing j i) (o : FoldedOrdering A)
    (b : TransportedOrbit D) (hb : b ∈ (FoldedOrdering.order o).negative ++ (FoldedOrdering.order o).positive)
    (v : D.I → K) :
    orderedRootPoint M.toIntegralMarking (integralRing K) (transportedLabels b) v =
      orbitRootValue (M := M) A (blockDirectionOf A b)
        (fun i => if A.direction i = blockDirectionOf A b then v i else 0) := by
  let ord := FoldedOrdering.order o
  let a := blockDirectionOf A b
  let w := fun i => if A.direction i = a then v i else 0
  have hslot i : i ∈ transportedLabels b ↔ A.direction i = a := orderedBlocks_support ord hb i
  have hw i (hi : A.direction i ≠ a) : w i = 0 := if_neg hi
  have hcell := cellValue_ofOrbit (M := M) A hsym _ _ ord.negative_enumerates
    ord.positive_enumerates a w hw
  have hn : (transportedLabels b).Nodup := (order_block_eq ord hb) ▸ FoldedOrdering.nodup o a
  have hzero (i : D.I) (hi : i ∉ transportedLabels b) : w i = 0 :=
    hw i (fun h => hi ((hslot i).mpr h))
  have hcomm (i : D.I) (hi : i ∈ transportedLabels b) (j : D.I) (hj : j ∈ transportedLabels b)
      (hne : i ≠ j) : Commute
      (markedRootPoint M.toIntegralMarking (integralRing K) i (w i))
      (markedRootPoint M.toIntegralMarking (integralRing K) j (w j)) := by
    have hpair : D.datum.pairing i j = 0 := by
      rcases (A.orbits i j).mp (((hslot i).mp hi).trans ((hslot j).mp hj).symm) with e | e
      · exact (hne e.symm).elim
      · subst j
        exact A.orthogonal i hne.symm
    have h := ExceptionalMarkedRootDescent.markedOrthogonalRootCommutation M hsym i j hpair
      K (CommAlgCat.of K K) (IntegralRootRelations.upper (w i)) (Or.inl ⟨w i, rfl⟩)
      (IntegralRootRelations.upper (w j)) (Or.inl ⟨w j, rfl⟩)
    simpa only [M.rankOneUpper, markedRootPoint] using h
  have h' := cellValue_supported M.toIntegralMarking (integralRing K)
    (ord.negative.flatMap transportedLabels) (ord.positive.flatMap transportedLabels)
    (transportedLabels b) ord.negative_enumerates ord.positive_enumerates hn w hzero hcomm
  refine (Eq.trans ?_ h'.symm).trans hcell
  unfold orderedRootPoint
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  rw [show w i = v i from if_pos ((hslot i).mp hi)]

set_option maxHeartbeats 2200000 in
private theorem groupedIwahori_factor (X : MarkedLevel R σ A k)
    (hdeg : Module.finrank F L = 2) (hσ : σ ≠ 1) (had : D.datum.rootSpan ℤ = ⊤)
    (numbering : Fin 6 ≃ D.base.support) (hnum : ExceptionalNumbering D 6 numbering)
    (hτ : ∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i))
    (o : FoldedOrdering A) (g : X.folded.comparison.I) :
    ∃ (t : X.folded.comparison.T₀)
      (z : FoldedRootDirection → X.folded.comparison.I),
      (∀ a, (z a).val ∈ X.rootLayer (X.iwahoriDepth a)) ∧
      g.val =
        (((FoldedOrdering.order o).negative.map (fun b => (z (blockDirectionOf A b)).val)).prod *
          t.val * (((FoldedOrdering.order o).positive.map
            (fun b => (z (blockDirectionOf A b)).val)).prod)) := by
  let T := X.compositum
  let K := T.field
  let C := X.folded.comparison
  let ord := FoldedOrdering.order o
  let ns := ord.negative.flatMap transportedLabels
  let ps := ord.positive.flatMap transportedLabels
  let cell := cellValue M.toIntegralMarking (integralRing K) ns ps
  obtain ⟨_, _, hSym⟩ := LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat.e6LocalRootSymmetries D numbering (R.diagram σ) hnum hτ
  obtain ⟨units, hChart⟩ := groupedChart_rational X hdeg hσ had numbering hnum hτ o
  obtain ⟨z, hz, ht, hn, hp⟩ := (iwahori_cell C.localIwahori ns ps
      ord.negative_enumerates ord.positive_enumerates g.val).mp g.property
  obtain ⟨t, x, hT, hx⟩ := (hChart z).mp ⟨g.val, hz.symm⟩
  let v (i : D.I) : K :=
    let b := ord.block (A.direction i)
    algebraMap Integers.{u} K (slotUnit units b i : Integers.{u}) *
      slotMap T.diagram b i (x (A.direction i))
  have ht' : ∀ χ, normalizedValuation K (t χ : K) = 1 := fun χ =>
    (congrArg (fun s : TorusValues D (integralRing K) => normalizedValuation K (s χ : K))
      (congrArg (fun w => w.2.1) hx)).trans (ht χ)
  obtain ⟨qt, hqt⟩ := existsValuationTorus X t ht'
  obtain ⟨gt, hgt⟩ := hT
  have hgtT : gt ∈ C.T₀ := (rationalUnitTorusComparison T X.folded).integral gt |>.mpr
    ⟨qt, hgt.trans (congrArg (fun s => torusPoint D (integralRing K) s ≫ M.torus.hom.hom) hqt).symm⟩
  have hf (a : FoldedRootDirection) :
      ∃ g' : C.I, g'.val ∈ X.rootLayer (X.iwahoriDepth a) ∧
        X.folded.points g'.val = orbitRootValue (M := M) A a
          (fun i => if A.direction i = a then v i else 0) := by
    let w (i : D.I) : K := if A.direction i = a then v i else 0
    let z' : CellValues D (integralRing K) ns ps := (fun i => w ns[i], 1, fun i => w ps[i])
    let z0 (i : FoldedRootDirection) : ExceptionalMarkedRootDescent.rationalOrbitParameter k K (ord.block i) := 0
    let z1 := Function.update z0 a (x a)
    have hw (i : D.I) (hi : A.direction i ≠ a) : w i = 0 := if_neg hi
    have hslot (i : D.I) :
        algebraMap Integers.{u} K (slotUnit units (ord.block (A.direction i)) i : Integers.{u}) *
          slotMap T.diagram (ord.block (A.direction i)) i (z1 (A.direction i)) = w i := by
      by_cases hi : A.direction i = a
      · subst a
        simp only [w, v, z1, Function.update_self, ite_eq_left rfl]
      · rw [show z1 (A.direction i) = 0 from Function.update_of_ne hi _ _, map_zero, mul_zero]
        exact (hw i hi).symm
    have hz' : ord.coordinates units T.diagram 1 z1 = z' :=
      Prod.ext (funext fun i => hslot ns[i]) (Prod.ext rfl (funext fun i => hslot ps[i]))
    have hOne : (torusPoint D (integralRing K) 1 ≫ M.torus.hom.hom) ∈ X.folded.points.range :=
      ⟨1, (map_one X.folded.points).trans (markedTorusPointHom M.toIntegralMarking (integralRing K)).map_one.symm⟩
    obtain ⟨g', hg'⟩ := (hChart z').mpr ⟨1, _, hOne, hz'⟩
    have hI : g' ∈ C.I := (iwahori_cell C.localIwahori ns ps
        ord.negative_enumerates ord.positive_enumerates g').mpr
      ⟨z', hg'.symm, fun χ => by change normalizedValuation K 1 = 1; exact map_one _,
        fun i => by
          change normalizedValuation K (w ns[i]) < 1
          by_cases hi : A.direction ns[i] = a
          · rw [show w ns[i] = v ns[i] from if_pos hi, show v ns[i] = z.1 i from congrFun (congrArg Prod.fst hx) i]
            exact hn i
          · rw [hw _ hi, map_zero]; exact zero_lt_one,
        fun i => by
          change normalizedValuation K (w ps[i]) ≤ 1
          by_cases hi : A.direction ps[i] = a
          · rw [show w ps[i] = v ps[i] from if_pos hi,
              show v ps[i] = z.2.2 i from congrFun (congrArg (fun z => z.2.2) hx) i]
            exact hp i
          · rw [hw _ hi, map_zero]; exact zero_le_one⟩
    have he := hg'.trans (cellValue_ofOrbit A hSym ns ps
      ord.negative_enumerates ord.positive_enumerates a w hw)
    exact ⟨⟨g', hI⟩, iwahoriOrbit_mem_rootLayer X hSym a g' hI w hw he, he⟩
  choose f hf hfp using hf
  refine ⟨⟨gt, hgtT⟩, f, hf, C.point_injective ?_⟩
  have hprod (bs : List (TransportedOrbit D))
      (hbs : ∀ b ∈ bs, b ∈ ord.negative ++ ord.positive) :
      X.folded.points ((bs.map (fun b => (f (blockDirectionOf A b)).val)).prod) =
        orderedRootPoint M.toIntegralMarking (integralRing K) (bs.flatMap transportedLabels) v := by
    rw [map_list_prod, List.map_map]
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply, List.flatMap_cons, orderedRootPoint,
        List.map_append, List.prod_append]
      simp only [orderedRootPoint] at ih
      refine congrArg₂ (· * ·) ?_ (ih (fun c hc => hbs c (List.mem_cons_of_mem _ hc)))
      exact (hfp _).trans (blockValue_eq_orbit hSym o b (hbs b List.mem_cons_self) v).symm
  have hcell : cell (ord.coordinates units T.diagram t x) =
      orderedRootPoint M.toIntegralMarking (integralRing K) ns v *
        ((torusPoint D (integralRing K) t ≫ M.torus.hom.hom) *
          orderedRootPoint M.toIntegralMarking (integralRing K) ps v) :=
    cellValue_values M.toIntegralMarking (integralRing K) ns ps v t
  calc
    X.folded.points g.val = cell z := hz.symm
    _ = cell (ord.coordinates units T.diagram t x) := congrArg cell hx.symm
    _ = _ := by
      rw [hcell, map_mul, map_mul, hgt, hprod ord.negative (fun _ h => List.mem_append_left _ h),
        hprod ord.positive (fun _ h => List.mem_append_right _ h), mul_assoc]

end GroupedIwahori


section OrderedImage

open ExceptionalAffineBruhat (ExceptionalNumbering)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalFoldedRootChart (OrbitOrdering)
open ExceptionalMarkedRootDescent (TransportedOrbit transportedLabels)
open ExceptionalIwahoriCongruence (cellValue CellValues)
open OrderedRootProducts (Enumerates)
open Specs.RamifiedExceptionalRationalUnitTorus (genericTorusValues reduceTorusValues)
open RamifiedExceptionalLocalFaceCoordinates (LeadingCoefficients rootSlotLeadingCoefficient iwahoriResidueCell)
open private FoldedOrdering FoldedOrdering.order foldedOrdering from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private firstLabel firstLabel_mem blocks_nodup from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedRootChart
open private reduceIwahoriCell mapTorusValues from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalLocalFaceCoordinates
open private cellValue_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private prod_filter_eq_prod_of_one from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalOppositeWallLayer

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R σ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  (P : ScaledParahoricTower X J π d y)
  {ϖ : Fˣ} {x : invariantApartment D (R.diagram σ)}
  (Q : ∀ k, LocalReductionCoordinates (P.scale k) ϖ x)

private abbrev iwahoriDepth (A : FoldedApartment (R.diagram σ)) (a : FoldedRootDirection) :=
  (a, threshold (A.roots.root a A.basepoint))


private theorem iwahoriResidueCell_eq_one
    {k E : Type u} [Field k] [Algebra F k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field E] (Y : MarkedLevel R σ A k)
    (ϖ : Fˣ) (π : Lˣ) (x : invariantApartment D (R.diagram σ))
    (B : ∀ a, LeadingCoefficients Y ϖ π a) (e : kᵥ[Y.compositum.field] →+* E)
    (t : InvariantTorusValues (R.diagram σ) E) (ht : t.val = 1)
    (z : FoldedRootDirection → E)
    (hz : ∀ a, A.roots.wallValue (Y.iwahoriDepth a) x = 0 → z a = 0) :
    iwahoriResidueCell Y ϖ π x B e t z = 1 := by
  let C := Y.folded.comparison.chart
  let coord (i : D.I) (b : Integers.{u}ˣ) : E :=
    if A.roots.wallValue (Y.iwahoriDepth (A.direction i)) x = 0 then
      algebraMap Integers.{u} E (b : Integers.{u}) *
        e ((B (Y.iwahoriDepth (A.direction i))).factor i) * z (A.direction i)
    else 0
  have hc (i : D.I) (b : Integers.{u}ˣ) : coord i b = 0 := by
    unfold coord
    by_cases hi : A.roots.wallValue (Y.iwahoriDepth (A.direction i)) x = 0
    · rw [ite_eq_left hi, hz _ hi, mul_zero]
    · exact ite_eq_right hi
  let w : CellValues D (integralRing E) C.negative C.positive :=
    (fun i : Fin C.negative.length => coord C.negative[i] (C.chart.negUnit i), t.val,
      fun i : Fin C.positive.length => coord C.positive[i] (C.chart.posUnit i))
  have hw : w = (0, 1, 0) := by
    apply Prod.ext
    · exact funext fun i => hc C.negative[i] (C.chart.negUnit i)
    · exact Prod.ext ht (funext fun i => hc C.positive[i] (C.chart.posUnit i))
  change cellValue M.toIntegralMarking (integralRing E) C.negative C.positive w = 1
  rw [hw, cellValue_torus]
  exact (markedTorusPointHom M.toIntegralMarking (integralRing E)).map_one

include Q in
set_option maxHeartbeats 2000000 in
private theorem killedIwahoriRoot
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (hclosed : ∀ a, A.roots.positive A.basepoint a → 0 ≤ A.roots.wallValue a x)
    (k : UnramifiedLevel F S) (a : FoldedRootDirection)
    (ha : A.roots.wallValue (iwahoriDepth A a) x ≠ 0)
    (g : (X k).parahoric J) (hg : g.val ∈ (X k).rootLayer (iwahoriDepth A a)) :
    P.geometricReduction k g = 1 := by
  let Y := X k
  let C := Y.folded.comparison.chart
  let K := Y.compositum.field
  let U := localAuxiliary (P.auxiliary.extension k)
  let E := U.field
  obtain ⟨t, z, ht, hz, hpoint⟩ := hg
  let v := Function.update (fun i => (0 : C.parameter i)) a z
  let w (i : FoldedRootDirection) : Y.ParametersAtDepth (Y.iwahoriDepth i) :=
    ⟨v i, by
      by_cases hi : i = a
      · subst i
        change C.value a (v a) ≤ exp (-(iwahoriDepth A a).2)
        rw [show v a = z from Function.update_self a z _]
        exact hz
      · change C.value i (v i) ≤ _
        rw [show v i = 0 from Function.update_of_ne hi _ _, map_zero]
        exact bot_le⟩
  have hlead (i : FoldedRootDirection) (hi : i ≠ a) :
      ((Q k).leading (Y.iwahoriDepth i)).leading (w i) = 0 := by
    obtain ⟨j, hj⟩ := A.surjective i
    let B := (Q k).leading (Y.iwahoriDepth i)
    obtain ⟨e, b, _, he, hb⟩ := rootSlotLeadingCoefficient Y ϖ π _ B j hj (w i)
    have hzero : (w i).val = 0 := by
      change v i = 0
      unfold v
      rw [Function.update_of_ne hi]
    rw [hzero, map_zero] at he
    have hb0 : (b : K) = 0 := (mul_eq_zero.mp he.symm).resolve_left
      (zpow_ne_zero _ ((map_ne_zero (algebraMap L K)).2 π.ne_zero))
    have hb' : b = 0 := Subtype.ext hb0
    rw [hb', map_zero] at hb
    exact (mul_eq_zero.mp hb.symm).resolve_left (B.factor j).ne_zero
  let q : TorusValues D (integralRing Oᵥ[K]) := 1
  let tres : InvariantTorusValues (R.diagram σ) kᵥ[E] := ⟨1, fun _ => rfl⟩
  have hq : genericTorusValues q = t.val := by
    rw [ht]
    apply MonoidHom.ext
    intro χ
    change Units.map (valuationRingInclusion K).hom.toRingHom.toMonoidHom (1 : Oᵥ[K]ˣ) = 1
    exact map_one _
  have htres : mapTorusValues (residueMap K E) (reduceTorusValues q) = tres.val := by
    apply MonoidHom.ext
    intro χ
    change Units.map (residueMap K E).toMonoidHom (Units.map (IsLocalRing.residue Oᵥ[K]).toMonoidHom (1 : Oᵥ[K]ˣ)) = 1
    simp only [map_one]
  have hred := reduceIwahoriCell Y π d y U (P.scale k) ϖ x hy hπ hd hclosed
    (Q k).leading g t q hq tres htres w hpoint
  let wres (i : FoldedRootDirection) : kᵥ[E] :=
    residueMap K E (((Q k).leading (Y.iwahoriDepth i)).leading (w i))
  have hwres (i : FoldedRootDirection) (hi : A.roots.wallValue (Y.iwahoriDepth i) x = 0) :
      wres i = 0 := by
    by_cases he : i = a
    · subst i
      exact (ha hi).elim
    · unfold wres
      rw [hlead i he, map_zero]
  have hcell := iwahoriResidueCell_eq_one Y ϖ π x (Q k).leading (residueMap K E) tres rfl wres hwres
  have hresult : (P.scale k).reduction g = 1 := hred.trans hcell
  change scalarPoints M (P.auxiliary.residueEmbedding k) ((P.scale k).reduction g) = 1
  exact (congrArg (scalarPoints M (P.auxiliary.residueEmbedding k)) hresult).trans (map_one _)

private def geometricIwahoriSubgroup : Subgroup (geometricPoints (F := F) (M := M)) where
  carrier := P.iwahoriImage
  one_mem' := (mem_geometricImage P _ _).2 ⟨P.auxiliary.base, 1, Subgroup.one_mem _, map_one _⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨k, g, hg, rfl⟩ := (mem_geometricImage P _ a).1 ha
    obtain ⟨l, g', hg', rfl⟩ := (mem_geometricImage P _ b).1 hb
    obtain ⟨m, h, h'⟩ := P.auxiliary.directed k l
    have hI : (faceInclusion X h J (P.face_comap h) g).val ∈ (X m).folded.comparison.I := by
      change g.val ∈ (X m).folded.comparison.I.comap
        (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h))
      rwa [P.iwahori_comap h]
    have hI' : (faceInclusion X h' J (P.face_comap h') g').val ∈ (X m).folded.comparison.I := by
      change g'.val ∈ (X m).folded.comparison.I.comap
        (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h'))
      rwa [P.iwahori_comap h']
    refine (mem_geometricImage P _ _).2 ⟨m, faceInclusion X h J (P.face_comap h) g *
      faceInclusion X h' J (P.face_comap h') g', Subgroup.mul_mem _ hI hI', ?_⟩
    rw [map_mul, geometricReduction_natural P h, geometricReduction_natural P h']
  inv_mem' := by
    intro a ha
    obtain ⟨k, g, hg, rfl⟩ := (mem_geometricImage P _ a).1 ha
    exact (mem_geometricImage P _ _).2 ⟨k, g⁻¹, Subgroup.inv_mem _ hg, map_inv _ _⟩

private theorem elementProduct_mem {I G : Type*} [Group G] (l : List I) (v : I → G)
    (S : I → Set G) (hv : ∀ i ∈ l, v i ∈ S i) : (l.map v).prod ∈ (l.map S).prod := by
  induction l with
  | nil => exact Set.mem_singleton _
  | cons i l ih =>
    exact Set.mul_mem_mul (hv i List.mem_cons_self) (ih fun j hj => hv j (List.mem_cons_of_mem _ hj))

private theorem product_sets_subset_group {I G : Type*} [Group G] (H : Subgroup G) (l : List I)
    (S : I → Set G) (h : ∀ i ∈ l, S i ⊆ H) : (l.map S).prod ⊆ H := by
  induction l with
  | nil => rintro _ (rfl : _ = 1); exact H.one_mem
  | cons i l ih =>
    intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_mul.mp hz
    exact H.mul_mem (h i List.mem_cons_self hp)
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) hq)

private def survivingInOrder (A : FoldedApartment (R.diagram σ))
    (x : invariantApartment D (R.diagram σ)) (l : List (TransportedOrbit D)) :=
  (l.map (fun b => iwahoriDepth A (blockDirectionOf A b))).filter
    (fun a => decide (A.roots.wallValue a x = 0))

private theorem survivingOrder_nodup (o : OrbitOrdering A.direction) (bs : List (TransportedOrbit D))
    (hd : bs.Nodup) (hb : ∀ b ∈ bs, b ∈ o.negative ++ o.positive) :
    (survivingInOrder A x bs).Nodup := by
  apply (hd.map_on ?_).filter
  intro b h₁ c h₂ he
  have h : blockDirectionOf A b = blockDirectionOf A c := congrArg Prod.fst he
  exact (order_block_eq o (hb b h₁)).symm.trans
    ((congrArg o.block h).trans (order_block_eq o (hb c h₂)))

private theorem survivingNegative_enumerates (o : OrbitOrdering A.direction) :
    Enumerates (survivingInOrder A x o.negative) {a ∈ survivingIwahoriRoots A x |
      ¬ ∃ i, A.direction i = a.1 ∧ D.base.IsPos i} := by
  refine ⟨survivingOrder_nodup o o.negative (List.nodup_append.mp (blocks_nodup o)).1
    (fun _ h => List.mem_append_left _ h), fun a => ?_⟩
  simp only [survivingInOrder, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hw⟩
    refine ⟨⟨rfl, hw⟩, ?_⟩
    rintro ⟨i, hi, hp⟩
    exact (o.negative_enumerates.2 i).mp (List.mem_flatMap.mpr ⟨b, hb,
      (orderedBlocks_support o (List.mem_append_left _ hb) i).mpr hi⟩) hp
  · rintro ⟨⟨hd, hw⟩, hn⟩
    obtain ⟨i, hi⟩ := A.surjective a.1
    have hneg : ¬ D.base.IsPos i := fun hp => hn ⟨i, hi, hp⟩
    obtain ⟨b, hb, hmem⟩ := List.mem_flatMap.mp ((o.negative_enumerates.2 i).mpr hneg)
    have h := (orderedBlocks_support o (List.mem_append_left _ hb) i).mp hmem
    refine ⟨⟨b, hb, Prod.ext (h.symm.trans hi) ?_⟩, hw⟩
    exact (congrArg (fun j => threshold (A.roots.root j A.basepoint)) (h.symm.trans hi)).trans hd.symm

private theorem survivingPositive_enumerates (o : OrbitOrdering A.direction) :
    Enumerates (survivingInOrder A x o.positive) {a ∈ survivingIwahoriRoots A x |
      ∃ i, A.direction i = a.1 ∧ D.base.IsPos i} := by
  refine ⟨survivingOrder_nodup o o.positive (List.nodup_append.mp (blocks_nodup o)).2.1
    (fun _ h => List.mem_append_right _ h), fun a => ?_⟩
  simp only [survivingInOrder, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨b, hb, rfl⟩, hw⟩
    exact ⟨⟨rfl, hw⟩, firstLabel b, rfl, (o.positive_enumerates.2 _).mp
      (List.mem_flatMap.mpr ⟨b, hb, firstLabel_mem b⟩)⟩
  · rintro ⟨⟨hd, hw⟩, i, hi, hp⟩
    obtain ⟨b, hb, hmem⟩ := List.mem_flatMap.mp ((o.positive_enumerates.2 i).mpr hp)
    have h := (orderedBlocks_support o (List.mem_append_right _ hb) i).mp hmem
    refine ⟨⟨b, hb, Prod.ext (h.symm.trans hi) ?_⟩, hw⟩
    exact (congrArg (fun j => threshold (A.roots.root j A.basepoint)) (h.symm.trans hi)).trans hd.symm

include Q in
set_option maxHeartbeats 2400000 in
private theorem geometricIwahori_product
    (hdeg : Module.finrank F L = 2) (hσ : σ ≠ 1) (had : D.datum.rootSpan ℤ = ⊤)
    (numbering : Fin 6 ≃ D.base.support) (hnum : ExceptionalNumbering D 6 numbering)
    (hτ : ∀ i, (R.diagram σ).val.indexEquiv (numbering i) = numbering (e6Partner i))
    (hy : (2 * (d : ℚ)) • x.val = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation L (π : L) = exp (-1)) (hd : 0 < d)
    (hclosed : ∀ a, A.roots.positive A.basepoint a → 0 ≤ A.roots.wallValue a x) :
    ∃ (negative positive : List (FoldedRootDirection × ℤ)),
      Enumerates negative {a ∈ survivingIwahoriRoots A x |
        ¬ ∃ i, A.direction i = a.1 ∧ D.base.IsPos i} ∧
      Enumerates positive {a ∈ survivingIwahoriRoots A x |
        ∃ i, A.direction i = a.1 ∧ D.base.IsPos i} ∧
      P.iwahoriImage = (negative.map P.rootImage).prod * P.torusImage * (positive.map P.rootImage).prod := by
  obtain ⟨o⟩ := foldedOrdering numbering A hnum hτ
  let ord := FoldedOrdering.order o
  let n := survivingInOrder A x ord.negative
  let p := survivingInOrder A x ord.positive
  have hn := survivingNegative_enumerates (x := x) ord
  have hp := survivingPositive_enumerates (x := x) ord
  refine ⟨n, p, hn, hp, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨k, g, hg, rfl⟩ := (mem_geometricImage P _ z).1 hz
    let i := Subgroup.inclusion (iwahori_le_face (X := X) (J := J) k)
    let f := (P.geometricReduction k).comp i
    let gI : (X k).folded.comparison.I := ⟨g.val, hg⟩
    obtain ⟨t, r, hr, hgrp⟩ := groupedIwahori_factor (X k) hdeg hσ had numbering hnum hτ o gI
    let tI : (X k).folded.comparison.I := ⟨t.val, unitTorus_le_iwahori _ t.property⟩
    have hsubprod (bs : List (TransportedOrbit D)) :
        ((bs.map (fun b => r (blockDirectionOf A b))).prod : (X k).folded.comparison.I).val =
          (bs.map (fun b => (r (blockDirectionOf A b)).val)).prod := by
      change (X k).folded.comparison.I.subtype ((bs.map (fun b => r (blockDirectionOf A b))).prod) = _
      rw [map_list_prod, List.map_map] <;> rfl
    have hprod : gI = (ord.negative.map (fun b => r (blockDirectionOf A b))).prod *
        tI * (ord.positive.map (fun b => r (blockDirectionOf A b))).prod := by
      apply Subtype.ext
      change g.val = ((ord.negative.map (fun b => r (blockDirectionOf A b))).prod).val *
        t.val * ((ord.positive.map (fun b => r (blockDirectionOf A b))).prod).val
      rw [hsubprod, hsubprod]
      exact hgrp
    have himage : P.geometricReduction k g =
        (n.map (fun a => f (r a.1))).prod * f tI * (p.map (fun a => f (r a.1))).prod := by
      change f gI = _
      have hpart (bs : List (TransportedOrbit D)) :
          f ((bs.map (fun b => r (blockDirectionOf A b))).prod) =
            ((survivingInOrder A x bs).map (fun a => f (r a.1))).prod := by
        let dl := bs.map (fun b => iwahoriDepth A (blockDirectionOf A b))
        have hk (a : FoldedRootDirection × ℤ) (ha : a ∈ dl)
            (h : decide (A.roots.wallValue a x = 0) = false) : f (r a.1) = 1 := by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          exact killedIwahoriRoot P Q hy hπ hd hclosed k _ (of_decide_eq_false h)
            (i (r (blockDirectionOf A b))) (hr _)
        rw [show survivingInOrder A x bs = dl.filter (fun a => decide (A.roots.wallValue a x = 0)) from rfl,
          prod_filter_eq_prod_of_one _ _ _ hk, map_list_prod] <;>
          (simp only [dl, List.map_map]; rfl)
      rw [hprod, map_mul, map_mul, hpart ord.negative, hpart ord.positive]
    rw [himage]
    have ht : f tI ∈ P.torusImage := (mem_geometricImage P _ _).2 ⟨k, i tI, t.property, rfl⟩
    have hroot (a : FoldedRootDirection × ℤ) (ha : a ∈ survivingIwahoriRoots A x) :
        f (r a.1) ∈ P.rootImage a := by
      refine (mem_geometricImage P _ _).2 ⟨k, i (r a.1), ?_, rfl⟩
      have he : a = iwahoriDepth A a.1 := Prod.ext rfl ha.1
      rw [he]
      exact hr _
    exact Set.mul_mem_mul (Set.mul_mem_mul
      (elementProduct_mem n _ _ (fun a ha => hroot a ((hn.2 a).1 ha).1)) ht)
      (elementProduct_mem p _ _ (fun a ha => hroot a ((hp.2 a).1 ha).1))
  · let H := geometricIwahoriSubgroup P
    have ht : P.torusImage ⊆ H := by
      intro z hz
      obtain ⟨k, g, hg, rfl⟩ := (mem_geometricImage P _ z).1 hz
      exact (mem_geometricImage P _ _).2 ⟨k, g, unitTorus_le_iwahori _ hg, rfl⟩
    have hr (a : FoldedRootDirection × ℤ) (ha : a ∈ survivingIwahoriRoots A x) : P.rootImage a ⊆ H := by
      intro z hz
      obtain ⟨k, g, hg, rfl⟩ := (mem_geometricImage P _ z).1 hz
      exact (mem_geometricImage P _ _).2 ⟨k, g, rootLayerAtIwahoriDepth (X := X) k a ha.1 hg, rfl⟩
    intro z hz
    obtain ⟨s, hs, v, hv, rfl⟩ := Set.mem_mul.mp hz
    obtain ⟨s, hsn, t, hst, rfl⟩ := Set.mem_mul.mp hs
    exact H.mul_mem (H.mul_mem (product_sets_subset_group H n _ (fun a ha => hr a ((hn.2 a).1 ha).1) hsn)
      (ht hst)) (product_sets_subset_group H p _ (fun a ha => hr a ((hp.2 a).1 ha).1) hv)

end OrderedImage

section ParameterProducts

open CategoryTheory.Limits
open OrderedRootProducts (Enumerates)
open ExceptionalAffineBruhat (ExceptionalNumbering)
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalLocalRootCoordinates (ramificationIndex)

variable {κ : Type u} [Field κ] {D : BasedRootDatum.{u}} {M : Model D}

private def residueParametersOfHom {G : GroupScheme κ} (f : G ⟶ residueGroup M κ)
    (hft : LocallyOfFiniteType G.X.hom) (hqc : QuasiCompact G.X.hom) : ResidueParameterMap M κ :=
  ⟨G.X, hft, hqc, f.hom.hom⟩

private theorem polynomialLine_finite_type (B : Type u) [CommRing B] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  change (algebraMap B (Polynomial B)).FiniteType
  apply RingHom.finiteType_algebraMap.mpr
  refine ⟨⟨{Polynomial.X}, ?_⟩⟩
  rw [Finset.coe_singleton, Polynomial.adjoin_X]

private theorem residueLine_finite_type :
    LocallyOfFiniteType ((fibre κ).obj M.line.group).X.hom := by
  have h : LocallyOfFiniteType M.line.group.X.hom := polynomialLine_finite_type Integers.{u}
  change LocallyOfFiniteType (pullback.snd M.line.group.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} κ))))
  exact MorphismProperty.pullback_snd _ _ h

private theorem residueLine_quasiCompact :
    QuasiCompact ((fibre κ).obj M.line.group).X.hom := by
  have h : QuasiCompact M.line.group.X.hom := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (Polynomial Integers.{u}))))
    infer_instance
  change QuasiCompact (pullback.snd M.line.group.X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} κ))))
  infer_instance

private def residueProduct {I : Type*} (f : I → ResidueParameterMap M κ) :
    List I → ResidueParameterMap M κ
  | [] => constantResidueParameter (1 : FieldPoints M κ)
  | i :: l => multiplyResidueParameters (f i) (residueProduct f l)

private theorem residueProduct_image {I : Type*} (f : I → ResidueParameterMap M κ)
    (l : List I) (S : I → Set (FieldPoints M (AlgebraicClosure κ)))
    (h : ∀ i ∈ l, (f i).geometricImage = S i) :
    (residueProduct f l).geometricImage = (l.map S).prod := by
  induction l with
  | nil =>
    change (constantResidueParameter (1 : FieldPoints M κ)).geometricImage = 1
    rw [geometricImage_constantResidueParameter, map_one]
    rfl
  | cons i l ih =>
    change (multiplyResidueParameters (f i) (residueProduct f l)).geometricImage = _
    rw [geometricImage_multiplyResidueParameters, h i List.mem_cons_self,
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    rfl

set_option maxHeartbeats 3000000 in
/-- The actual ramified adjoint face admits compatible integral scalings
and the geometric image has the marked residue parameters over κ. -/
theorem ramifiedParahoricScaling : RamifiedParahoricScaling.{u} := by
  intro F L S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ hdeg hσ hram D M R numbering hnum had hτ
    A X k₀ t x
  dsimp only
  intro ht hx π hπ
  obtain ⟨hc, hres, ϖ, d, y, hϖ, hd, hy, P, ⟨Q⟩⟩ :=
    existsScaledFaceTower hdeg hσ hram numbering hnum had hτ X k₀ t x ht hx π hπ
  have hclosed := rationalClosedAlcove (X k₀).building t x hx
  have hsym := (LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat.e6LocalRootSymmetries
    D numbering (R.diagram σ) hnum hτ).2.2
  have htor := geometricTorusCoordinates P Q had
  obtain ⟨T, Tmap, hTsplit, hTconn, hTft, hTqc, hTimg⟩ :=
    existsResidueTorusMap (κ := kᵥ[F]) (M := M) (R.diagram σ) numbering had hτ
  have htor' : geometricImageOfHom M Tmap = P.torusImage := hTimg.trans htor.symm
  have hr (a : residueRootDirections A (cotype t) x) :
      ∃ f : (fibre kᵥ[F]).obj M.line.group ⟶ residueGroup M kᵥ[F],
        geometricImageOfHom M f = P.rootImage a.val :=
    existsGeometricRootMap P Q a hsym hy hπ hd
  choose r hr using hr
  obtain ⟨n, p, hn, hp, hI⟩ := geometricIwahori_product P Q hdeg hσ had numbering hnum hτ
    hy hπ hd hclosed
  let Tparam := residueParametersOfHom Tmap hTft hTqc
  let rootparam (a : FoldedRootDirection × ℤ) : ResidueParameterMap M kᵥ[F] :=
    if h : a ∈ residueRootDirections A (cotype t) x then
      residueParametersOfHom (r ⟨a, h⟩) residueLine_finite_type residueLine_quasiCompact
    else constantResidueParameter 1
  have hroot (a : FoldedRootDirection × ℤ) (h : a ∈ survivingIwahoriRoots A x) :
      (rootparam a).geometricImage = P.rootImage a := by
    have ha : a ∈ residueRootDirections A (cotype t) x := Or.inl h
    unfold rootparam
    split
    next h => exact hr ⟨a, h⟩
    next h => exact (h ha).elim
  let f := multiplyResidueParameters (multiplyResidueParameters (residueProduct rootparam n) Tparam)
    (residueProduct rootparam p)
  have hf : f.geometricImage = P.iwahoriImage := by
    change (multiplyResidueParameters _ _).geometricImage = _
    rw [geometricImage_multiplyResidueParameters, geometricImage_multiplyResidueParameters,
      residueProduct_image rootparam n P.rootImage (fun a ha => hroot a ((hn.2 a).1 ha).1),
      residueProduct_image rootparam p P.rootImage (fun a ha => hroot a ((hp.2 a).1 ha).1)]
    exact (congrArg (fun U => (n.map P.rootImage).prod * U * (p.map P.rootImage).prod) htor').trans hI.symm
  let H := Subgroup.closure (P.torusImage ∪ ⋃ a : residueRootDirections A (cotype t) x, P.rootImage a.val)
  have hH : P.iwahoriImage ⊆ H := by
    have hT : P.torusImage ⊆ H := fun g hg => Subgroup.subset_closure (Or.inl hg)
    have hl (a : FoldedRootDirection × ℤ) (ha : a ∈ survivingIwahoriRoots A x) : P.rootImage a ⊆ H :=
      fun g hg => Subgroup.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨⟨a, Or.inl ha⟩, hg⟩))
    rw [hI]
    rintro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hz
    obtain ⟨u', hu', q, hq, rfl⟩ := Set.mem_mul.mp hu
    exact H.mul_mem (H.mul_mem (product_sets_subset_group H n _ (fun a ha => hl a ((hn.2 a).1 ha).1) hu')
      (hT hq)) (product_sets_subset_group H p _ (fun a ha => hl a ((hp.2 a).1 ha).1) hv)
  obtain ⟨maps, hmap, hfin⟩ := faceParameterCover P f hf
  refine ⟨hc, hres, ϖ, d, y, hϖ, hd, hy, P, ⟨{
    localCoordinates := Q
    iwahori_root := iwahoriRootReduction P Q hy hπ hd
    torus := T
    torus_split := hTsplit
    torus_connected := hTconn
    torus_finite_type := hTft
    torus_quasiCompact := hTqc
    torusMap := Tmap
    torus_image := htor'
    torus_coordinates := htor
    root_connected := residueLine_connected
    rootMaps := r
    root_image := hr
    iwahori_product := ⟨n, p, hn, hp, hI⟩
    iwahoriMap := f
    iwahori_image := hf
    wall_reduction := wallLiftGeometricReduction P Q
    generation := parahoricImage_generated P Q hH
    finiteWeylGroup := (X P.auxiliary.base).building.realization.finite_wall_group
      (cotype t) (ExceptionalAffineBuilding.cotype_ne_univ t)
    doubleCosetMap := maps
    double_coset := hmap
    finite_image := hfin
    lift_finite := liftFiniteGeometricPoints P
  }⟩⟩

end ParameterProducts

end

end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceReduction
