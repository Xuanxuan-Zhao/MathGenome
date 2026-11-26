import Specs.LinearAlgebraicGroups.Arithmetic.RationalFunctionSLAdelicReduction
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import LinearAlgebraicGroups.Affine.StandardGroups
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Opposite Topology
open scoped BigOperators LaurentSeries Polynomial PowerSeries RatFunc RestrictedProduct Valued

universe u

namespace LinearAlgebraicGroups.Arithmetic.RationalFunctionSLAdelicReduction

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.RationalFunctionSLAdelicReduction
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open Arithmetic.AdelicGroups
open Matrix (GeneralLinearGroup SpecialLinearGroup)

set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

open private StandardGroups.linearOperations_quotient StandardGroups.generalLinearRepresentation
  StandardGroups.specialLinearRepresentation StandardGroups.Representation.convolutionIso
  from LinearAlgebraicGroups.Affine.StandardGroups

/-- The closed realization furnished by the determinant-one Hopf quotient. -/
theorem standardMatrixRealization : StandardMatrixRealization.{u} := by
  intro k _ m
  classical
  let I := Index.{u} m
  let A := Specs.StandardGroups.GLCoordinates k I
  let B := Specs.StandardGroups.SLCoordinates k I
  letI := StandardGroups.generalLinearHopf k I
  letI := StandardGroups.specialLinearHopf k I
  let Aq := CommHopfAlgCat.of k A
  let Bq := CommHopfAlgCat.of k B
  let q := Ideal.Quotient.mkₐ k (Specs.StandardGroups.determinantOneIdeal k I)
  obtain ⟨hΔ, hε, _⟩ := StandardGroups.linearOperations_quotient (k := k) (ι := I)
  let h : Aq ⟶ Bq := CommHopfAlgCat.ofHom (BialgHom.ofAlgHom q hε.symm hΔ)
  let G := StandardGroups.specialLinearGroup k I
  let J := StandardGroups.generalLinearGroup k I
  let f : G.val ⟶ J.val := (hopfSpec (CommRingCat.of k)).map h.op
  let s := StandardGroups.specialLinearGroupPointsIso k I
  let j := StandardGroups.generalLinearGroupPointsIso k I
  refine ⟨⟨G, J, s, j, f, ?_, ?_⟩⟩
  · change IsClosedImmersion (Spec.map (CommRingCat.ofHom q.toRingHom))
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  · intro R x
    let e := hopfSpecPointIso Bq
    let y := e.inv.app R x
    have hy : e.hom.app R y = x := (e.app R).groupIsoToMulEquiv.apply_symm_apply x
    let z := WithConv.toConv (y.ofConv.comp q)
    have hz : (hopfSpecPointIso Aq).hom.app R z =
        ((groupPointsFunctor k).map f).app R x := by
      calc
        _ = ((groupPointsFunctor k).map f).app R (e.hom.app R y) := by
          apply Over.OverMorphism.ext
          exact Spec.map_comp (CommRingCat.ofHom q.toRingHom) (CommRingCat.ofHom y.ofConv.toRingHom)
        _ = _ := congrArg (fun v => ((groupPointsFunctor k).map f).app R v) hy
    have hj : j.hom.app R ((hopfSpecPointIso Aq).hom.app R z) =
        (StandardGroups.Representation.convolutionIso
          (StandardGroups.generalLinearRepresentation (k := k) (ι := I))).hom.app R z := by
      let i := hopfSpecPointIso Aq
      let c := (StandardGroups.Representation.convolutionIso (StandardGroups.generalLinearRepresentation (k := k) (ι := I)))
      change ((i ≪≫ (i.symm ≪≫ c)).hom.app R) z = _
      simp [c]
    have hs : s.hom.app R (e.hom.app R y) =
        (StandardGroups.Representation.convolutionIso
          (StandardGroups.specialLinearRepresentation (k := k) (ι := I))).hom.app R y := by
      let c := (StandardGroups.Representation.convolutionIso (StandardGroups.specialLinearRepresentation (k := k) (ι := I)))
      change ((e ≪≫ (e.symm ≪≫ c)).hom.app R) y = _
      simp [c]
    have hEval : (StandardGroups.Representation.convolutionIso
          (StandardGroups.generalLinearRepresentation (k := k) (ι := I))).hom.app R z =
        SpecialLinearGroup.toGL ((StandardGroups.Representation.convolutionIso
          (StandardGroups.specialLinearRepresentation (k := k) (ι := I))).hom.app R y) := Units.ext rfl
    exact (congrArg (fun v => j.hom.app R v) hz.symm).trans
      (hj.trans (hEval.trans (congrArg SpecialLinearGroup.toGL
        (hs.symm.trans (congrArg (fun v => s.hom.app R v) hy)))))

private theorem rationalMap_eq_id (F : Type u) [Field F] :
    (rationalParameter F).rationalMap.toRingHom = RingHom.id F⟮X⟯ := by
  let f := (rationalParameter F).rationalMap
  have hX : f RatFunc.X = RatFunc.X :=
    RatFunc.algEquivOfTranscendental_X RatFunc.X (rationalParameter F).transcendental
  have hpoly : f.comp (IsScalarTower.toAlgHom F F[X] F⟮X⟯) =
      IsScalarTower.toAlgHom F F[X] F⟮X⟯ := by
    apply Polynomial.algHom_ext
    simpa [RatFunc.algebraMap_X] using hX
  apply IsLocalization.ringHom_ext (nonZeroDivisors F[X])
  exact congrArg AlgHom.toRingHom hpoly

theorem uniquePole : UniquePole.{u} := by
  intro F _ _ w
  have h := (rationalParameter F).comap_eq_infty_iff w
  rw [rationalMap_eq_id F] at h
  have hc : w.val.comap (RingHom.id _) = w.val := by
    ext x
    rfl
  rw [hc] at h
  exact Subtype.ext_iff.trans h

private theorem integralSpecial_iff {ι L : Type*} [Fintype ι] [DecidableEq ι] [CommRing L]
    (O : Subring L) (x : SpecialLinearGroup ι L) :
    x ∈ (SpecialLinearGroup.map O.subtype).range ↔
      SpecialLinearGroup.toGL x ∈ (GeneralLinearGroup.map O.subtype).range := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨SpecialLinearGroup.toGL b, Units.ext rfl⟩
  · rintro ⟨b, hb⟩
    have hd : b.val.det = 1 := by
      apply O.subtype_injective
      rw [O.subtype.map_det, map_one]
      exact (congrArg (fun g : GeneralLinearGroup ι L => g.val.det) hb).trans x.det_coe
    refine ⟨⟨b.val, hd⟩, ?_⟩
    exact Subtype.val_injective (congrArg Units.val hb)

private theorem asMatrix_eq_toGL {k R : Type u} [Field k] [CommRing R] [Algebra k R] {m : ℕ}
    (P : SpecialLinearRealization k m) (x : PointsIn P.realization R) :
    asMatrix P.realization R x =
      SpecialLinearGroup.toGL (P.specialPoints.hom.app (CommAlgCat.of k R) x) :=
  P.matrix_eq _ x

section FunctionField

variable {F : Type u} [Field F] [Finite F] {m : ℕ}

private abbrev D (F : Type u) [Field F] [Finite F] := baseFieldData F

local instance completionField (w : (D F).Place) : Field ((D F).Completion w) :=
  GlobalFieldData.instFieldCompletion (D F) w

local instance completionTopology (w : (D F).Place) : TopologicalSpace ((D F).Completion w) :=
  GlobalFieldData.instTopologicalSpaceCompletion (D F) w

local instance baseCompletionAlgebra (w : (D F).Place) : Algebra F⟮X⟯ ((D F).Completion w) :=
  completionAlgebra (D F) w

private def placeEquiv (F : Type u) [Field F] [Finite F] :
    FunctionPlace F⟮X⟯ ≃ Outside (D F) ∅ where
  toFun := adelicPlace
  invFun w := match w.1 with
    | .inl w => w
    | .inr w => isEmptyElim w
  left_inv _ := rfl
  right_inv := by
    rintro ⟨w, hw⟩
    cases w with
    | inl w => rfl
    | inr w => exact (IsEmpty.false w).elim

private theorem mem_integral_iff (P : SpecialLinearRealization F⟮X⟯ m)
    (g : Adeles (D F) P.realization ∅) (w : FunctionPlace F⟮X⟯) :
    g (adelicPlace w) ∈ localSubgroup (D F) P.realization (.inl w) ↔
      localMatrix P g w ∈ (SpecialLinearGroup.map w.integers.subtype).range := by
  change asMatrix P.realization ((D F).Completion (.inl w)) (g (adelicPlace w)) ∈
    (GeneralLinearGroup.map w.integers.subtype).range ↔ _
  letI : Algebra F⟮X⟯ w.Completion := completionAlgebra (D F) (.inl w)
  have h : asMatrix P.realization w.Completion (g (adelicPlace w)) =
      SpecialLinearGroup.toGL (localMatrix P g w) :=
    asMatrix_eq_toGL P (g (adelicPlace w))
  exact (Iff.of_eq (congrArg (fun x : GeneralLinearGroup (Index.{u} m) w.Completion =>
    x ∈ (GeneralLinearGroup.map w.integers.subtype).range) h)).trans
      (integralSpecial_iff w.integers.toSubring (localMatrix P g w)).symm

private def exponentDiagonal (w : FunctionPlace F⟮X⟯) (a : Index.{u} m → ℤ)
    (hs : ∑ i, a i = 0) : SpecialLinearGroup (Index.{u} m) w.Completion :=
  ⟨Matrix.diagonal (fun i => (w.embedding RatFunc.X) ^ a i), by
    classical
    rw [Matrix.det_diagonal]
    have ht := (map_ne_zero w.embedding).2 (RatFunc.X_ne_zero (K := F))
    have hp (s : Finset (Index.{u} m)) :
        (∏ i ∈ s, (w.embedding RatFunc.X) ^ a i) = (w.embedding RatFunc.X) ^ (∑ i ∈ s, a i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ht]
    rw [hp, hs, zpow_zero]⟩

/-- Integral components form a compact product. Each exponent vector gives a
single right translate, supported at the pole, of this compact product. -/
theorem compactNormalForms : CompactNormalForms.{u} := by
  intro F _ _ m P E hE hsum
  classical
  let X := Adeles (D F) P.realization ∅
  letI : IsTopologicalGroup X := AdelicGroups.adelicTopology (D F) P.realization ∅
  let W := Outside (D F) ∅
  let L (w : W) := LocalPoints (D F) P.realization w.1
  let U (w : W) := localSubgroup (D F) P.realization w.1
  let K : Set X := {g | ∀ w : W, g w ∈ U w}
  have hK : IsCompact K := by
    apply AdelicLatticeBounds.compactRestrictedProductBox
      (fun w => (U w : Set (L w))) (fun w => (U w : Set (L w)))
    · intro w
      obtain ⟨v, rfl⟩ := (placeEquiv F).surjective w
      exact (integralCompactOpen (D F) P.realization v).1
    · exact Eventually.of_forall fun _ => Set.Subset.rfl
  let w₀ := adelicPlace (pole F)
  let A (a : E) : SpecialLinearGroup (Index.{u} m) (pole F).Completion :=
    exponentDiagonal (pole F) a (hsum a a.property)
  let s := P.specialPoints.app (CommAlgCat.of F⟮X⟯ ((D F).Completion w₀.1))
  let b (a : E) : X :=
    RestrictedProduct.mulSingle (G := L) U w₀ (s.inv (A a))
  let C : Set X := ⋃ a : E, (fun x : X => x * b a) '' K
  letI : Finite E := hE.to_subtype
  refine ⟨C, isCompact_iUnion (fun a => hK.image (continuous_mul_const (b a))), ?_⟩
  intro g a ha hg
  let a' : E := ⟨a, ha⟩
  refine Set.mem_iUnion.mpr ⟨a', g * (b a')⁻¹, ?_, inv_mul_cancel_right g _⟩
  intro w
  obtain ⟨v, rfl⟩ := (placeEquiv F).surjective w
  change (g * (b a')⁻¹) (adelicPlace v) ∈ U (adelicPlace v)
  apply (mem_integral_iff P _ v).mpr
  by_cases hv : v = pole F
  · subst v
    obtain ⟨k, hk⟩ := hg.2
    have hb : b a' w₀ = s.inv (A a') := RestrictedProduct.mulSingle_eq_same _ _ _
    have hA : s.hom (b a' w₀) = A a' := by
      rw [hb]
      exact s.groupIsoToMulEquiv.apply_symm_apply _
    have hh : localMatrix P g (pole F) =
        SpecialLinearGroup.map (pole F).integers.subtype k * A a' := Subtype.val_injective hk
    refine ⟨k, ?_⟩
    let φ : L w₀ →* SpecialLinearGroup (Index.{u} m) (pole F).Completion := s.hom.hom
    change _ = φ (g w₀ * (b a' w₀)⁻¹)
    rw [map_mul, map_inv, show φ (b a' w₀) = A a' from hA,
      show φ (g w₀) = localMatrix P g (pole F) from rfl, hh, mul_inv_cancel_right]
  · have hw : adelicPlace v ≠ w₀ := (placeEquiv F).injective.ne hv
    have hb : b a' (adelicPlace v) = 1 := RestrictedProduct.mulSingle_eq_of_ne _ _ hw
    have hh : (g * (b a')⁻¹) (adelicPlace v) = g (adelicPlace v) := by
      change g (adelicPlace v) * (b a' (adelicPlace v))⁻¹ = _
      rw [hb, inv_one, mul_one]
    simpa only [localMatrix, hh] using hg.1 v hv

end FunctionField

section FiniteReduction

open IsDedekindDomain AdelicLatticeBounds

open private isLattice_matrixLattice coe_matrixLattice integralBasis_changeBasis
  from LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

/-- An integral lattice in the rational coordinate space is the column lattice
of an invertible matrix in the standard coordinates. -/
private theorem exists_matrixLattice {R k : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field k] [Algebra R k] [IsFractionRing R k] {n : ℕ}
    (L : Submodule R (Fin n → k)) [Submodule.IsLattice k L] :
    ∃ M : GeneralLinearGroup (Fin n) k, matrixLattice (R := R) M = L := by
  classical
  have hdim : Module.finrank R L = n := by
    calc
      Module.finrank R L = Module.finrank k (Fin n → k) :=
        congrArg Cardinal.toNat (Submodule.IsLattice.rank' k L)
      _ = n := by simp
  let b := Module.finBasisOfFinrankEq R L hdim
  let B := (b.extendOfIsLattice k).equivFun.symm
  let M := GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv B)
  have hM (x : Fin n → k) : M.val.mulVec x = B x := by
    change (GeneralLinearGroup.toLin M).val x = B x
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hB (x : Fin n → R) : B (algebraMap R k ∘ x) = (b.equivFun.symm x : Fin n → k) := by
    simp only [B, Module.Basis.equivFun_symm_apply, Module.Basis.extendOfIsLattice_apply,
      Function.comp_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower, algebraMap_smul]
  refine ⟨M, SetLike.coe_injective ?_⟩
  rw [coe_matrixLattice]
  change Set.range (fun x : Fin n → R => M.val.mulVec (algebraMap R k ∘ x)) = (L : Set (Fin n → k))
  simp only [hM, hB]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (b.equivFun.symm z).property
  · intro hx
    exact ⟨b.equivFun ⟨x, hx⟩, congrArg Subtype.val (b.equivFun.symm_apply_apply ⟨x, hx⟩)⟩

/-- The rational intersection of the inverse images of the local integer
lattices has a determinant-one basis. -/
private theorem finiteReduction {F : Type u} [Field F] {n : ℕ}
    (g : FiniteBasisAdeles F[X] F⟮X⟯ (Fin n)) (hg : ∀ p, (g p).det = 1) :
    ∃ M : GeneralLinearGroup (Fin n) F⟮X⟯, M.det = 1 ∧ FiniteBasisIntegral (fun p => g p) M := by
  classical
  let k := F⟮X⟯
  let R := F[X]
  let L₀ := matrixLattice (R := R) (1 : GeneralLinearGroup (Fin n) k)
  let S (p : HeightOneSpectrum R) : Set (Fin n → p.adicCompletion k) :=
    {x | ∀ i, x i ∈ p.adicCompletionIntegers k}
  let P (p : HeightOneSpectrum R) := matrixLattice (R := p.adicCompletionIntegers k) (g p)⁻¹
  letI := isLattice_matrixLattice (R := R) (1 : GeneralLinearGroup (Fin n) k)
  letI (p : HeightOneSpectrum R) : Submodule.IsLattice (p.adicCompletion k) (P p) :=
    isLattice_matrixLattice (g p)⁻¹
  have hP (p : HeightOneSpectrum R) :
      (P p : Set (Fin n → p.adicCompletion k)) = (g p)⁻¹.val.mulVec '' S p := by
    rw [coe_matrixLattice]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨fun i => (z i : p.adicCompletion k), fun i => (z i).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨fun i => ⟨z i, hz i⟩, rfl⟩
  have hL₀ (p : HeightOneSpectrum R) :
      (completedLattice p L₀ : Set (Fin n → p.adicCompletion k)) = S p := by
    simpa only [map_one, GeneralLinearGroup.coe_one, Matrix.one_mulVec, Set.image_id'] using
      completedBasisLattice (R := R) (1 : GeneralLinearGroup (Fin n) k) p
  have hPfinite : {p | P p ≠ completedLattice p L₀}.Finite := by
    rw [← eventually_cofinite]
    filter_upwards [g.2] with p hp
    apply SetLike.coe_injective
    rw [hP, hL₀]
    exact (integralMatrixIffPreservesBox (p.adicCompletionIntegers k).toSubring (g p)⁻¹).mp
      (Subgroup.inv_mem _ hp)
  let L := rationalLatticeIntersection P
  obtain ⟨_, _, hL, _, _, hcomp⟩ := dedekindLatticeIntersection (B := R) L₀ P hPfinite
  letI : Submodule.IsLattice k L := hL
  obtain ⟨M, hM⟩ := exists_matrixLattice L
  have hI : FiniteBasisIntegral (fun p => g p) M := by
    intro p
    have hEq := completedBasisLattice (R := R) M p
    rw [hM, (hcomp p).2.2.2, hP] at hEq
    apply (integralMatrixIffPreservesBox (p.adicCompletionIntegers k).toSubring _).2
    change ((g p).val * (GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) M).val).mulVec
      '' S p = S p
    let m := GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) M
    have hEq' : m.val.mulVec '' S p = (g p)⁻¹.val.mulVec '' S p := hEq.symm
    have hmul : ((g p).val * m.val).mulVec = (g p).val.mulVec ∘ m.val.mulVec :=
      funext fun x => (Matrix.mulVec_mulVec _ _ _).symm
    change ((g p).val * m.val).mulVec '' S p = S p
    calc
      _ = (g p).val.mulVec '' (m.val.mulVec '' S p) :=
        (congrArg (fun f => f '' S p) hmul).trans (Set.image_comp _ _ _)
      _ = (g p).val.mulVec '' ((g p)⁻¹.val.mulVec '' S p) :=
        congrArg (Set.image (g p).val.mulVec) hEq'
      _ = S p := ?_
    rw [← Set.image_comp]
    have h : (g p).val.mulVec ∘ (g p)⁻¹.val.mulVec = id := by
      funext x
      change (g p).val.mulVec ((g p)⁻¹.val.mulVec x) = x
      rw [Matrix.mulVec_mulVec, show (g p).val * (g p)⁻¹.val = 1 from (g p).val_inv, Matrix.one_mulVec]
    rw [h, Set.image_id]
  obtain ⟨d, hd⟩ := determinantUnitOfLocal M (fun p => g p) hg hI
  obtain ⟨B, hB⟩ := determinantOneBasisCorrection M d hd
  exact ⟨_, hB, integralBasis_changeBasis hI B⟩

end FiniteReduction

section CompletionComparisons

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum LatticeCompletionDecompositionSpec LaurentLattice
open UniformSpace.Completion

variable {F : Type u} [Field F] [Finite F]

private def polynomialPlace (F : Type u) [Field F] (p : HeightOneSpectrum F[X]) :
    FunctionPlace F⟮X⟯ :=
  ⟨(p.valuation F⟮X⟯).valuationSubring, fun h =>
    ((p.valuation F⟮X⟯).valuationSubring_eq_top_iff.mp h) inferInstance⟩

open private exists_adic_of_contains from LinearAlgebraicGroups.Arithmetic.GlobalPlaces

private theorem polynomialPlace_injective (F : Type u) [Field F] :
    Function.Injective (polynomialPlace F) := by
  intro p q hpq
  exact HeightOneSpectrum.valuationSubring_valuation_injective F⟮X⟯ (congrArg Subtype.val hpq)

private theorem polynomialPlace_ne_pole (p : HeightOneSpectrum F[X]) :
    polynomialPlace F p ≠ pole F := by
  intro h
  have hx := ((uniquePole F (polynomialPlace F p)).mp h)
  apply hx
  change (p.valuation F⟮X⟯) RatFunc.X ≤ 1
  rw [← RatFunc.algebraMap_X]
  exact p.valuation_le_one Polynomial.X

private theorem exists_polynomialPlace (w : FunctionPlace F⟮X⟯) (hw : w ≠ pole F) :
    ∃ p : HeightOneSpectrum F[X], polynomialPlace F p = w := by
  classical
  have hX : (RatFunc.X : F⟮X⟯) ∈ w.val := by
    by_contra h
    exact hw ((uniquePole F w).mpr h)
  have hp (f : F[X]) : algebraMap F[X] F⟮X⟯ f ∈ w.val := by
    induction f using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact w.val.toSubring.add_mem hf hg
    | monomial n c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_X]
        apply w.val.toSubring.mul_mem ?_ (w.val.pow_mem hX n)
        change algebraMap F[X] F⟮X⟯ (algebraMap F F[X] c) ∈ w.val
        rw [← IsScalarTower.algebraMap_apply, ← w.val.valuationSubring_valuation]
        exact FiniteField.valuation_algebraMap_le_one w.val.valuation c
  obtain ⟨p, h⟩ := exists_adic_of_contains w hp
  exact ⟨p, Subtype.ext h⟩

private theorem completionValuationEquiv {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (w : FunctionPlace K) (v : Valuation K Γ₀)
    (h : v.valuationSubring = w.val) : w.val.valuation.IsEquiv v :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr (w.val.valuationSubring_valuation.trans h.symm)

private def completionEquivOfSubring {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (w : FunctionPlace K) (v : Valuation K Γ₀)
    (h : v.valuationSubring = w.val) : w.Completion ≃+* v.Completion :=
  let e := completionValuationEquiv w v h
  mapRingEquiv (WithVal.congr _ _ (RingEquiv.refl K))
    e.uniformContinuous_congr.continuous e.symm.uniformContinuous_congr.continuous

private theorem completionEquivOfSubring_embedding {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (w : FunctionPlace K) (v : Valuation K Γ₀)
    (h : v.valuationSubring = w.val) (x : K) :
    completionEquivOfSubring w v h (w.embedding x) =
      (↑((WithVal.equiv v).symm x) : v.Completion) := by
  unfold completionEquivOfSubring FunctionPlace.embedding
  exact mapRingHom_coe (completionValuationEquiv w v h).uniformContinuous_congr.continuous
    ((WithVal.equiv w.val.valuation).symm x)

private theorem completionEquivOfSubring_integral {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (w : FunctionPlace K) (v : Valuation K Γ₀)
    (h : v.valuationSubring = w.val) (x : w.Completion) :
    Valued.v (completionEquivOfSubring w v h x) ≤ 1 ↔ x ∈ w.integers :=
  (completionValuationEquiv w v h).valuedCompletion_le_one_iff.symm

private def polynomialCompletion (p : HeightOneSpectrum F[X]) :
    (polynomialPlace F p).Completion ≃+* p.adicCompletion F⟮X⟯ :=
  (completionEquivOfSubring (polynomialPlace F p) (p.valuation F⟮X⟯) rfl).trans
    (adicCompletion.equiv F⟮X⟯ p).symm

omit [Finite F] in
private theorem polynomialCompletion_embedding (p : HeightOneSpectrum F[X]) (x : F⟮X⟯) :
    polynomialCompletion p ((polynomialPlace F p).embedding x) =
      algebraMap F⟮X⟯ (p.adicCompletion F⟮X⟯) x := by
  change (adicCompletion.equiv F⟮X⟯ p).symm
    (completionEquivOfSubring (polynomialPlace F p) (p.valuation F⟮X⟯) rfl
      ((polynomialPlace F p).embedding x)) = _
  exact congrArg (adicCompletion.equiv F⟮X⟯ p).symm
    (completionEquivOfSubring_embedding (polynomialPlace F p) (p.valuation F⟮X⟯) rfl x)

omit [Finite F] in
private theorem polynomialCompletion_integral (p : HeightOneSpectrum F[X])
    (x : (polynomialPlace F p).Completion) :
    polynomialCompletion p x ∈ p.adicCompletionIntegers F⟮X⟯ ↔ x ∈ (polynomialPlace F p).integers := by
  change Valued.v (polynomialCompletion p x) ≤ 1 ↔ _
  rw [← adicCompletion.valued_toCompletion_apply]
  exact completionEquivOfSubring_integral _ _ rfl x

private theorem absoluteValue_le_one_iff (x : F⸨X⸩) :
    absoluteValue F x ≤ 1 ↔ baseValuation F x ≤ 1 := by
  rw [absoluteValue]
  by_cases h : baseValuation F x = 0
  · simp [h]
  · rw [ite_eq_right h]
    have hq : 1 < (Nat.card F : ℝ) := by exact_mod_cast Finite.one_lt_card (α := F)
    have hval : baseValuation F x ≤ 1 ↔ WithZero.log (baseValuation F x) ≤ 0 := by
      conv_lhs => rw [← WithZero.exp_log h, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp
    rw [hval, ← (zpow_right_strictMono₀ hq).le_iff_le (b := (0 : ℤ)), zpow_zero]

/-- The pole completion and its integer ring in Laurent coordinates, using
the actual rational embedding on polynomial inputs. -/
private theorem exists_laurentComparison (F : Type u) [Field F] [Finite F] :
    ∃ e : (pole F).Completion ≃+* F⸨X⸩,
      (∀ p : F[X], e ((pole F).embedding (algebraMap F[X] F⟮X⟯ p)) = polynomialEmbedding F p) ∧
      (∀ x : (pole F).Completion, baseValuation F (e x) ≤ 1 ↔ x ∈ (pole F).integers) := by
  classical
  let c := completionEquivOfSubring (pole F) (RatFunc.inftyValuation F) rfl
  letI := infinityRankOne F
  letI := infinityNormedField F
  obtain ⟨e, _, _, he, hnorm⟩ := AdelicLatticeBounds.functionInfinityLaurent F
  refine ⟨c.trans e, ?_, ?_⟩
  · intro p
    change e (c ((pole F).embedding (algebraMap F[X] F⟮X⟯ p))) = _
    rw [show c ((pole F).embedding (algebraMap F[X] F⟮X⟯ p)) =
      infinityEmbedding F (algebraMap F[X] F⟮X⟯ p) from completionEquivOfSubring_embedding _ _ rfl _]
    exact he p
  · intro x
    change baseValuation F (e (c x)) ≤ 1 ↔ _
    rw [← absoluteValue_le_one_iff, hnorm, Valued.toNormedField.norm_le_one_iff]
    exact completionEquivOfSubring_integral _ _ rfl x

private theorem polePower_eq_zpow (F : Type u) [Field F] (n : ℤ) :
    polePower F n = polePower F 1 ^ n := by
  let f : Multiplicative ℤ →* F⸨X⸩ˣ :=
    { toFun := fun n => Units.mk0 (polePower F n.toAdd) (polePower_ne_zero _)
      map_one' := Units.ext (polePower_zero (F := F))
      map_mul' := fun a b => Units.ext (polePower_mul (F := F) a.toAdd b.toAdd).symm }
  have h : (Multiplicative.ofAdd 1 : Multiplicative ℤ) ^ n = Multiplicative.ofAdd n := by
    simpa using (ofAdd_zsmul n (1 : ℤ)).symm
  have he := congrArg Units.val (map_zpow f (Multiplicative.ofAdd 1) n)
  rw [h, Units.val_zpow_eq_zpow_val] at he
  exact he

end CompletionComparisons

section OrderedReduction

open IsDedekindDomain LaurentLattice AdelicLatticeBounds

private def reindexGL {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {R : Type*} [CommRing R] (e : I ≃ J) :
    GeneralLinearGroup I R ≃* GeneralLinearGroup J R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

private theorem reindexGL_det {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {R : Type*} [CommRing R] (e : I ≃ J) (g : GeneralLinearGroup I R) :
    (reindexGL e g).det = g.det :=
  Units.ext (Matrix.det_reindex_self e g.val)

private theorem reindexGL_map {I J R S : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [CommRing R] [CommRing S] (e : I ≃ J) (f : R →+* S) (g : GeneralLinearGroup I R) :
    reindexGL e (GeneralLinearGroup.map f g) = GeneralLinearGroup.map f (reindexGL e g) :=
  Units.ext rfl

private theorem reindexGL_integral {I J R : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [CommRing R] (e : I ≃ J) (O : Subring R) (g : GeneralLinearGroup I R) :
    reindexGL e g ∈ (GeneralLinearGroup.map O.subtype).range ↔
      g ∈ (GeneralLinearGroup.map O.subtype).range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(reindexGL e).symm b, (reindexGL e).injective ?_⟩
    rw [reindexGL_map, MulEquiv.apply_symm_apply, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨reindexGL e b, (reindexGL_map e _ _).symm⟩

private theorem mapGL_integral {I R S : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] [CommRing S] (e : R ≃+* S) (O : Subring R) (U : Subring S)
    (h : ∀ x, e x ∈ U ↔ x ∈ O) (g : GeneralLinearGroup I R) :
    GeneralLinearGroup.map e.toRingHom g ∈ (GeneralLinearGroup.map U.subtype).range ↔
      g ∈ (GeneralLinearGroup.map O.subtype).range := by
  let r := e.restrict O U fun x => (h x).symm
  let E : GeneralLinearGroup I R ≃* GeneralLinearGroup I S :=
    Units.mapEquiv (e.mapMatrix.toMulEquiv)
  let B : GeneralLinearGroup I O ≃* GeneralLinearGroup I U :=
    Units.mapEquiv (r.mapMatrix.toMulEquiv)
  change E g ∈ _ ↔ _
  have hc (x : GeneralLinearGroup I O) :
      E (GeneralLinearGroup.map O.subtype x) = GeneralLinearGroup.map U.subtype (B x) :=
    Units.ext rfl
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨B.symm b, E.injective ?_⟩
    rw [hc, MulEquiv.apply_symm_apply, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨B b, (hc b).symm⟩

private def specialOfGeneral {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (g : GeneralLinearGroup I R) (h : g.det = 1) : SpecialLinearGroup I R :=
  ⟨g.val, congrArg Units.val h⟩

private theorem toGL_specialOfGeneral {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (g : GeneralLinearGroup I R) (h : g.det = 1) :
    SpecialLinearGroup.toGL (specialOfGeneral g h) = g :=
  Units.ext rfl

private theorem det_toGL {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (g : SpecialLinearGroup I R) : (SpecialLinearGroup.toGL g).det = 1 :=
  Units.ext g.det_coe

variable {F : Type u} [Field F] [Finite F] {m : ℕ}

private abbrev adelicGL (P : SpecialLinearRealization F⟮X⟯ m)
    (g : Adeles (baseFieldData F) P.realization ∅) (w : FunctionPlace F⟮X⟯) :=
  SpecialLinearGroup.toGL (localMatrix P g w)

private theorem adelicGL_mul_diagonal (P : SpecialLinearRealization F⟮X⟯ m)
    (g : Adeles (baseFieldData F) P.realization ∅)
    (γ : SpecialLinearGroup (Index.{u} m) F⟮X⟯) (w : FunctionPlace F⟮X⟯) :
    adelicGL P (g * diagonal (baseFieldData F) P.realization ∅ (P.rationalPoint γ)) w =
      adelicGL P g w * GeneralLinearGroup.map w.embedding (SpecialLinearGroup.toGL γ) := by
  let D := baseFieldData F
  let w' : D.Place := .inl w
  letI : Field (D.Completion w') := GlobalFieldData.instFieldCompletion D w'
  letI : Algebra F⟮X⟯ (D.Completion w') := completionAlgebra D w'
  let A := asMatrix P.realization (D.Completion w')
  let δ := diagonal D P.realization ∅ (P.rationalPoint γ)
  have h (x : Adeles D P.realization ∅) : A (x (adelicPlace w)) = adelicGL P x w :=
    asMatrix_eq_toGL P _
  let s := P.specialPoints.app (CommAlgCat.of F⟮X⟯ F⟮X⟯)
  have hs : s.hom (P.rationalPoint γ) = γ := s.groupIsoToMulEquiv.apply_symm_apply γ
  have hr : P.realization.onPoints (P.rationalPoint γ) = SpecialLinearGroup.toGL γ :=
    (P.matrix_eq _ _).trans (congrArg SpecialLinearGroup.toGL hs)
  have hδ : A (δ (adelicPlace w)) = GeneralLinearGroup.map w.embedding (SpecialLinearGroup.toGL γ) :=
    (localPoint_matrix D P.realization w' (P.rationalPoint γ)).trans
      (congrArg (GeneralLinearGroup.map w.embedding) hr)
  exact (h (g * δ)).symm.trans
    ((A.map_mul (g (adelicPlace w)) (δ (adelicPlace w))).trans (congrArg₂ (· * ·) (h g) hδ))

private theorem transported_mul_diagonal {L : Type*} [CommRing L]
    (P : SpecialLinearRealization F⟮X⟯ m) (g : Adeles (baseFieldData F) P.realization ∅)
    (γ : SpecialLinearGroup (Index.{u} m) F⟮X⟯) (w : FunctionPlace F⟮X⟯)
    (e : w.Completion →+* L) (i : Index.{u} m ≃ Fin m)
    (M : GeneralLinearGroup (Fin m) F⟮X⟯)
    (h : reindexGL i (SpecialLinearGroup.toGL γ) = M) :
    GeneralLinearGroup.map e
      (reindexGL i (adelicGL P (g * diagonal (baseFieldData F) P.realization ∅ (P.rationalPoint γ)) w)) =
      GeneralLinearGroup.map e (reindexGL i (adelicGL P g w)) *
        GeneralLinearGroup.map (e.comp w.embedding) M := by
  rw [adelicGL_mul_diagonal, map_mul, reindexGL_map, map_mul, h]
  rfl

/-- Choose a rational determinant-one basis from the finite lattices, then
change the polynomial basis to put the pole matrix in ordered form. -/
theorem orderedReduction : OrderedReduction.{u} := by
  intro F _ _ m P g
  classical
  let i : Index.{u} m ≃ Fin m := Equiv.ulift
  let w (p : HeightOneSpectrum F[X]) := polynomialPlace F p
  let A (v : FunctionPlace F⟮X⟯) := reindexGL i (adelicGL P g v)
  let G (p : HeightOneSpectrum F[X]) := GeneralLinearGroup.map (polynomialCompletion p).toRingHom (A (w p))
  have hG (p : HeightOneSpectrum F[X]) : (G p).det = 1 := by
    rw [show G p = GeneralLinearGroup.map (polynomialCompletion p).toRingHom (A (w p)) from rfl,
      GeneralLinearGroup.map_det, reindexGL_det, det_toGL, map_one]
  have hIntegral (p : HeightOneSpectrum F[X]) (x : GeneralLinearGroup (Index.{u} m) (w p).Completion) :
      GeneralLinearGroup.map (polynomialCompletion p).toRingHom (reindexGL i x) ∈
        (GeneralLinearGroup.map (p.adicCompletionIntegers F⟮X⟯).subtype).range ↔
          x ∈ (GeneralLinearGroup.map (w p).integers.subtype).range :=
    (mapGL_integral (polynomialCompletion p) _ _ (polynomialCompletion_integral p) _).trans
      (reindexGL_integral i (w p).integers.toSubring x)
  have hg : ∀ᶠ p : HeightOneSpectrum F[X] in cofinite,
      g (adelicPlace (w p)) ∈ localSubgroup (baseFieldData F) P.realization (.inl (w p)) := by
    rw [eventually_cofinite]
    exact (eventually_cofinite.mp g.2).preimage
      ((placeEquiv F).injective.comp (polynomialPlace_injective F)).injOn
  let Gfin : FiniteBasisAdeles F[X] F⟮X⟯ (Fin m) :=
    ⟨G, hg.mono fun p hp => (hIntegral p _).mpr
      ((integralSpecial_iff (w p).integers.toSubring _).mp ((mem_integral_iff P g (w p)).mp hp))⟩
  obtain ⟨M, hM, hFinite⟩ := finiteReduction Gfin hG
  obtain ⟨e, he, hIntegralInf⟩ := exists_laurentComparison F
  let f : F⟮X⟯ →+* F⸨X⸩ := e.toRingHom.comp (pole F).embedding
  have hf : f.comp (algebraMap F[X] F⟮X⟯) = polynomialEmbedding F :=
    RingHom.ext he
  let Ginf := GeneralLinearGroup.map e.toRingHom (A (pole F))
  have hGinf : Ginf.det = 1 := by
    change (GeneralLinearGroup.map e.toRingHom (reindexGL i (adelicGL P g (pole F)))).det = 1
    rw [GeneralLinearGroup.map_det, reindexGL_det, det_toGL, map_one]
  obtain ⟨M', B, a, hM', hFin, _, ha, hsum, hB, hNormal⟩ :=
    orderedFunctionAdelicBasis m f hf G Ginf M hGinf hM hFinite
  let γ₀ := (reindexGL i).symm M'
  have hγ₀ : reindexGL i γ₀ = M' := MulEquiv.apply_symm_apply _ _
  have hdet : γ₀.det = 1 := (reindexGL_det i γ₀).symm.trans ((congrArg _ hγ₀).trans hM')
  let γ := specialOfGeneral γ₀ hdet
  have hγ : reindexGL i (SpecialLinearGroup.toGL γ) = M' :=
    (congrArg (reindexGL i) (toGL_specialOfGeneral γ₀ hdet)).trans hγ₀
  let δ := diagonal (baseFieldData F) P.realization ∅ (P.rationalPoint γ)
  refine ⟨γ, δ, a ∘ i, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact ha (show i x ≤ i y from hxy)
  · exact (Finset.sum_equiv i (by simp) (by simp [Function.comp_apply])).trans hsum
  · intro v hv
    obtain ⟨p, rfl⟩ := exists_polynomialPlace v hv
    have hemb : (polynomialCompletion p).toRingHom.comp ((w p).embedding) =
        algebraMap F⟮X⟯ (p.adicCompletion F⟮X⟯) :=
      RingHom.ext (polynomialCompletion_embedding p)
    have hh := transported_mul_diagonal P g γ (w p) (polynomialCompletion p).toRingHom i M' hγ
    rw [hemb] at hh
    apply (integralSpecial_iff (w p).integers.toSubring _).mpr
    apply (hIntegral p _).mp
    exact hh.symm ▸ hFin p
  · let r : F⟦X⟧ →+* (pole F).integers :=
      (e.symm.toRingHom.comp (HahnSeries.ofPowerSeries ℤ F)).codRestrict (pole F).integers
        (fun x => (hIntegralInf _).mp (by
          change baseValuation F (e (e.symm (HahnSeries.ofPowerSeries ℤ F x))) ≤ 1
          rw [e.apply_symm_apply]
          exact (integral_ring F _).mpr ⟨x, rfl⟩))
    let b₀ := reindexGL i.symm (GeneralLinearGroup.map r B)
    have hb₀ : b₀.det = 1 := by
      change (reindexGL i.symm (GeneralLinearGroup.map r B)).det = 1
      rw [reindexGL_det, GeneralLinearGroup.map_det, show B.det = 1 from Units.ext hB, map_one]
    let b := specialOfGeneral b₀ hb₀
    refine ⟨b, Matrix.ext fun j k => e.injective ?_⟩
    have hEq : (GeneralLinearGroup.map e.toRingHom (reindexGL i (adelicGL P (g * δ) (pole F)))).val =
        B.val.map (HahnSeries.ofPowerSeries ℤ F) * Matrix.diagonal (polePower F ∘ a) :=
      (congrArg Units.val (transported_mul_diagonal P g γ (pole F) e.toRingHom i M' hγ)).trans hNormal
    have hX : e ((pole F).embedding RatFunc.X) = polePower F 1 := by
      rw [← RatFunc.algebraMap_X, he, polynomialEmbedding_X]
    have hEntry : e (((SpecialLinearGroup.map (pole F).integers.subtype b).val) j k) =
        HahnSeries.ofPowerSeries ℤ F (B.val (i j) (i k)) := by
      change e (e.symm (HahnSeries.ofPowerSeries ℤ F (B.val (i j) (i k)))) = _
      exact e.apply_symm_apply _
    have hh := congrFun (congrFun hEq (i j)) (i k)
    rw [Matrix.mul_diagonal] at hh ⊢
    rw [e.map_mul, hEntry, map_zpow₀, hX, ← polePower_eq_zpow]
    change e ((localMatrix P (g * δ) (pole F)).val (i.symm (i j)) (i.symm (i k))) =
      HahnSeries.ofPowerSeries ℤ F (B.val (i j) (i k)) * polePower F (a (i k)) at hh
    rw [i.symm_apply_apply, i.symm_apply_apply] at hh
    exact hh

end OrderedReduction

/-- An inclusion of restricted products is a closed embedding when each local
map is a closed embedding and pulls back the specified open subgroup exactly. -/
private theorem restrictedProduct_closedEmbedding
    {W : Type*} {L M : W → Type*} [∀ w, Group (L w)] [∀ w, Group (M w)]
    [∀ w, TopologicalSpace (L w)] [∀ w, TopologicalSpace (M w)]
    [∀ w, IsTopologicalGroup (L w)] [∀ w, IsTopologicalGroup (M w)]
    (U : ∀ w, Subgroup (L w)) (V : ∀ w, Subgroup (M w))
    (hu : ∀ w, IsOpen (U w : Set (L w))) (hv : ∀ w, IsOpen (V w : Set (M w)))
    (f : ∀ w, L w →* M w) (hf : ∀ w, IsClosedEmbedding (f w))
    (hi : ∀ w (x : L w), f w x ∈ V w ↔ x ∈ U w) :
    ∃ e : (Πʳ w, [L w, U w]) →* (Πʳ w, [M w, V w]),
      IsClosedEmbedding e ∧ ∀ x w, e x w = f w (x w) := by
  classical
  let X := Πʳ w, [L w, U w]
  let Y := Πʳ w, [M w, V w]
  let e : X →* Y :=
    { toFun := fun x => ⟨fun w => f w (x w), x.2.mono fun w hw => (hi w _).mpr hw⟩
      map_one' := RestrictedProduct.ext _ _ fun w => map_one (f w)
      map_mul' := fun x y => RestrictedProduct.ext _ _ fun w => map_mul (f w) _ _ }
  have he (x : X) (w : W) : e x w = f w (x w) := rfl
  refine ⟨e, ?_, he⟩
  have hInj : Function.Injective e := fun x y h =>
    RestrictedProduct.ext _ _ fun w => (hf w).isEmbedding.injective (congrArg (fun z : Y => z w) h)
  have hRange : Set.range e = ⋂ w, (fun y : Y => y w) ⁻¹' Set.range (f w) := by
    ext y
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨x, rfl⟩ w
      exact ⟨x w, rfl⟩
    · intro hy
      choose x hx using hy
      refine ⟨⟨x, y.2.mono fun w hw => (hi w (x w)).mp (hx w ▸ hw)⟩, ?_⟩
      exact RestrictedProduct.ext _ _ hx
  have hClosed : IsClosed (Set.range e) := by
    rw [hRange]
    exact isClosed_iInter fun w => (hf w).isClosed_range.preimage (RestrictedProduct.continuous_eval w)
  refine ⟨⟨?_, hInj⟩, hClosed⟩
  letI : Fact (∀ w, IsOpen (U w : Set (L w))) := ⟨hu⟩
  letI : Fact (∀ w, IsOpen (V w : Set (M w))) := ⟨hv⟩
  letI : IsTopologicalGroup X := RestrictedProduct.isTopologicalGroup L (B := U)
  letI : IsTopologicalGroup Y := RestrictedProduct.isTopologicalGroup M (B := V)
  apply IsTopologicalGroup.isInducing_iff_nhds_one.mpr
  let a : (∀ w, U w) → X := RestrictedProduct.structureMap L (fun w => (U w : Set (L w))) cofinite
  let b : (∀ w, V w) → Y := RestrictedProduct.structureMap M (fun w => (V w : Set (M w))) cofinite
  let f₀ (w : W) (x : U w) : V w := ⟨f w x, (hi w x).mpr x.property⟩
  let f₁ : (∀ w, U w) → (∀ w, V w) := fun x w => f₀ w (x w)
  have ha : IsOpenEmbedding a := RestrictedProduct.isOpenEmbedding_structureMap hu
  have hb : IsOpenEmbedding b := RestrictedProduct.isOpenEmbedding_structureMap hv
  have hf₀ (w : W) : IsInducing (f₀ w) :=
    ((IsEmbedding.of_comp_iff (f := f₀ w) (g := (Subtype.val : V w → M w))
      IsEmbedding.subtypeVal).mp ((hf w).isEmbedding.comp IsEmbedding.subtypeVal)).isInducing
  have hf₁ : IsInducing f₁ := IsInducing.piMap hf₀
  have h₀ : b (f₁ 1) = (1 : Y) :=
    RestrictedProduct.ext _ _ fun w => map_one (f w)
  have h₁ : a 1 = (1 : X) := rfl
  have hcomm : b ∘ f₁ = e ∘ a := rfl
  have hMem : Set.range a ∈ (𝓝 (1 : Y)).comap e := by
    refine Filter.mem_comap.mpr ⟨Set.range b, hb.isOpen_range.mem_nhds ⟨f₁ 1, h₀⟩, ?_⟩
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hx' (w : W) : x w ∈ U w :=
      (hi w (x w)).mp (show (e x) w ∈ V w from hy ▸ (y w).property)
    exact ⟨fun w => ⟨x w, hx' w⟩, RestrictedProduct.ext _ _ fun _ => rfl⟩
  calc
    𝓝 (1 : X) = (𝓝 (1 : ∀ w, U w)).map a := h₁ ▸ (ha.map_nhds_eq 1).symm
    _ = ((𝓝 (1 : Y)).comap (b ∘ f₁)).map a := by
      rw [← show (b ∘ f₁) (1 : ∀ w, U w) = (1 : Y) from h₀,
        (hb.isInducing.comp hf₁).nhds_eq_comap]
    _ = (((𝓝 (1 : Y)).comap e).comap a).map a := by rw [hcomm, Filter.comap_comap]
    _ = (𝓝 (1 : Y)).comap e := Filter.map_comap_of_mem hMem

/-- The topology on the closed subgroup is the one induced by the same ambient
matrices at each place, and the integral conditions pull back at every place. -/
theorem adelicClosedSubgroupEmbedding : AdelicClosedSubgroupEmbedding.{u} := by
  intro F _ _ m P H
  let D := baseFieldData F
  letI (w : D.Place) : Field (D.Completion w) := GlobalFieldData.instFieldCompletion D w
  letI (w : D.Place) : TopologicalSpace (D.Completion w) := GlobalFieldData.instTopologicalSpaceCompletion D w
  letI (w : D.Place) : Algebra F⟮X⟯ (D.Completion w) := completionAlgebra D w
  letI (w : D.Place) : IsTopologicalDivisionRing (D.Completion w) :=
    AdelicGroups.completionTopologicalDivisionRing D w
  let i := P.subgroupRealization H
  let j := P.realization
  let W := Outside D ∅
  let f (w : W) := P.subgroupLocalPoint H D w.1
  have hm (w : W) (x : LocalPoints D i w.1) :
      asMatrix j (D.Completion w.1) (f w x) = asMatrix i (D.Completion w.1) x := by
    change P.generalPoints.hom.app _ (((groupPointsFunctor F⟮X⟯).map P.inclusion).app _
      (((groupPointsFunctor F⟮X⟯).map H.inclusion).app _ x)) =
      P.generalPoints.hom.app _ (((groupPointsFunctor F⟮X⟯).map (H.inclusion ≫ P.inclusion)).app _ x)
    rw [Functor.map_comp]
    rfl
  have hc (w : W) : IsClosedEmbedding (f w) := by
    apply IsClosedEmbedding.of_comp (localMatrixEmbedding D j w.1).isEmbedding
    rw [show asMatrix j (D.Completion w.1) ∘ f w = asMatrix i (D.Completion w.1) from funext (hm w)]
    exact localMatrixEmbedding D i w.1
  have hi (w : W) (x : LocalPoints D i w.1) :
      f w x ∈ localSubgroup D j w.1 ↔ x ∈ localSubgroup D i w.1 := by
    obtain ⟨v, rfl⟩ := (placeEquiv F).surjective w
    change asMatrix j ((baseFieldData F).Completion (.inl v)) (f (adelicPlace v) x) ∈
        (GeneralLinearGroup.map v.integers.subtype).range ↔
      asMatrix i ((baseFieldData F).Completion (.inl v)) x ∈
        (GeneralLinearGroup.map v.integers.subtype).range
    exact Iff.of_eq (congrArg (fun y : GeneralLinearGroup (Index.{u} m) v.Completion =>
      y ∈ (GeneralLinearGroup.map v.integers.subtype).range) (hm (adelicPlace v) x))
  letI (w : W) : IsTopologicalGroup (LocalPoints D i w.1) :=
    pointsInTopologicalGroup i (D.Completion w.1)
  letI (w : W) : IsTopologicalGroup (LocalPoints D j w.1) :=
    pointsInTopologicalGroup j (D.Completion w.1)
  obtain ⟨e, he, heval⟩ := restrictedProduct_closedEmbedding
    (fun w : W => localSubgroup D i w.1) (fun w : W => localSubgroup D j w.1)
    (fun w => localSubgroup_open D i w.1) (fun w => localSubgroup_open D j w.1) f hc hi
  refine ⟨e, he, heval, ?_⟩
  intro d hd
  ext x : 1
  apply RestrictedProduct.ext
  intro w
  change e (d D i ∅ x) w = d D j ∅ _ w
  rw [heval, hd, hd]
  exact congrArg (fun a => a x)
    (((groupPointsFunctor F⟮X⟯).map H.inclusion).naturality
      (CommAlgCat.ofHom (Algebra.ofId F⟮X⟯ (D.Completion w.1))))

end LinearAlgebraicGroups.Arithmetic.RationalFunctionSLAdelicReduction
