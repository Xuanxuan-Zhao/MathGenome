import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExcessTorEulerExample
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.CompleteIntersectionEuler
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.RegularAcyclicity
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Inverse

noncomputable section

open CategoryTheory
open scoped TensorProduct Pointwise

namespace CommutativeAlgebraNotes.Intersection.ExcessTorEulerExample

open CommutativeAlgebraNotes.Intersection.ExcessTorEulerExample.Specs
open AdvCommAlg.Koszul
open IsolatedTorSupport (Tor koszulHomologyTorEquiv torZeroEquiv tensor_support)
open IsolatedIntersectionEuler (intersectionEuler_eq_cutoff cutoffEuler_eq_of_vanishes_above)

universe u

variable (k : Type u) [Field k]

private def dropFirst (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) k →ₐ[k] MvPowerSeries (Fin n) k :=
  (show PowerSeries (MvPowerSeries (Fin n) k) →ₐ[k] MvPowerSeries (Fin n) k from
    { __ := PowerSeries.constantCoeff
      commutes' a := by simp [PowerSeries.algebraMap_apply] }).comp
    (MvPowerSeries.finSuccEquiv k n).toAlgHom

private theorem dropFirst_surjective (n : ℕ) : Function.Surjective (dropFirst k n) :=
  PowerSeries.constantCoeff_surj.comp (MvPowerSeries.finSuccEquiv k n).surjective

@[simp] private theorem dropFirst_zero (n : ℕ) : dropFirst k n (MvPowerSeries.X 0) = 0 := by
  change PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k n (MvPowerSeries.X 0)) = 0
  rw [MvPowerSeries.finSuccEquiv_X_zero, PowerSeries.constantCoeff_X]

@[simp] private theorem dropFirst_succ (n : ℕ) (i : Fin n) :
    dropFirst k n (MvPowerSeries.X i.succ) = MvPowerSeries.X i := by
  change PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k n (MvPowerSeries.X i.succ)) = _
  rw [MvPowerSeries.finSuccEquiv_X_succ, PowerSeries.constantCoeff_C]

private theorem dropFirst_ker (n : ℕ) :
    RingHom.ker (dropFirst k n).toRingHom = Ideal.span {MvPowerSeries.X 0} := by
  ext p
  change PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k n p) = 0 ↔ _
  rw [Ideal.mem_span_singleton, ← PowerSeries.X_dvd_iff,
    ← MvPowerSeries.finSuccEquiv_X_zero, map_dvd_iff]

private def oneVariable : MvPowerSeries (Fin 1) k ≃ₐ[k] PowerSeries k :=
  MvPowerSeries.renameEquiv k (Equiv.ofUnique (Fin 1) PUnit)

@[simp] private theorem oneVariable_X :
    oneVariable k (MvPowerSeries.X 0) = PowerSeries.X := by
  change MvPowerSeries.rename (Equiv.ofUnique (Fin 1) PUnit) (MvPowerSeries.X 0) = _
  rw [MvPowerSeries.rename_X]
  rfl

private theorem yz_eq :
    yz k = Ideal.span {z k} ⊔ Ideal.span {y k} := by
  rw [← Ideal.span_union, Set.singleton_union, Set.pair_comm]

private def toSeries : Series k →ₐ[k] PowerSeries k :=
  (oneVariable k).toAlgHom.comp ((dropFirst k 1).comp (dropFirst k 2))

private theorem toSeries_surjective : Function.Surjective (toSeries k) :=
  (oneVariable k).surjective.comp ((dropFirst_surjective k 1).comp (dropFirst_surjective k 2))

private theorem toSeries_ker : RingHom.ker (toSeries k).toRingHom = yz k := by
  let f := (dropFirst k 2).toRingHom
  have hy : f (y k) = MvPowerSeries.X 0 := dropFirst_succ k 2 0
  have hmap : (Ideal.span {y k}).map f = Ideal.span {MvPowerSeries.X 0} := by
    rw [Ideal.map_span, Set.image_singleton, hy]
  have h : RingHom.ker (toSeries k).toRingHom =
      Ideal.comap f (RingHom.ker (dropFirst k 1).toRingHom) := by
    ext p
    change oneVariable k (dropFirst k 1 (dropFirst k 2 p)) = 0 ↔
      dropFirst k 1 (dropFirst k 2 p) = 0
    exact map_eq_zero_iff _ (oneVariable k).injective
  rw [h, dropFirst_ker, ← hmap, Ideal.comap_map_of_surjective f (dropFirst_surjective k 2)]
  rw [← RingHom.ker_eq_comap_bot, yz_eq, sup_comm (Ideal.span {z k}), ← dropFirst_ker k 2]

theorem quotientPowerSeries : Specs.quotientPowerSeries.{u} := by
  intro k _
  let e := (Ideal.quotientEquivAlgOfEq k (toSeries_ker k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toSeries_surjective k))
  have he (p : Series k) : e (Ideal.Quotient.mk (yz k) p) = toSeries k p :=
    Ideal.quotientKerAlgEquivOfSurjective_mk (toSeries_surjective k) p
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [he]
    change oneVariable k (dropFirst k 1 (dropFirst k 2 (MvPowerSeries.X ((1 : Fin 2).succ)))) = _
    rw [dropFirst_succ]
    change oneVariable k (dropFirst k 1 (MvPowerSeries.X ((0 : Fin 1).succ))) = _
    rw [dropFirst_succ, oneVariable_X]
  · rw [he]
    change oneVariable k (dropFirst k 1 (dropFirst k 2 (MvPowerSeries.X ((0 : Fin 2).succ)))) = _
    rw [dropFirst_succ, dropFirst_zero, map_zero]
  · rw [he]
    change oneVariable k (dropFirst k 1 (dropFirst k 2 (MvPowerSeries.X 0))) = _
    rw [dropFirst_zero, map_zero, map_zero]

private theorem listIdeal_xy : listIdeal [x k, y k] = xy k := by
  unfold listIdeal xy
  congr 1
  ext r
  simp

private theorem regular_xy : RingTheory.Sequence.IsRegular (Series k) [x k, y k] := by
  let R := Series k
  let e := MvPowerSeries.renameEquiv k (Equiv.swap (2 : Fin 3) 0)
  let f := (dropFirst k 2).comp e.toAlgHom
  have hy : f (y k) = MvPowerSeries.X 0 := by
    change dropFirst k 2 (MvPowerSeries.rename (Equiv.swap (2 : Fin 3) 0) (y k)) =
      MvPowerSeries.X 0
    rw [y, MvPowerSeries.rename_X, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact dropFirst_succ k 2 0
  have hk : RingHom.ker f.toRingHom = Ideal.span {x k} := by
    change Ideal.comap e.toRingHom (RingHom.ker (dropFirst k 2).toRingHom) = _
    rw [dropFirst_ker]
    have hmap : (Ideal.span {x k}).map e.toRingHom = Ideal.span {z k} := by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      change MvPowerSeries.rename (Equiv.swap (2 : Fin 3) 0) (MvPowerSeries.X 2) =
        MvPowerSeries.X 0
      rw [MvPowerSeries.rename_X, Equiv.swap_apply_left]
    change Ideal.comap e.toRingHom (Ideal.span {z k}) = _
    rw [← hmap, Ideal.comap_map_of_surjective e.toRingHom e.surjective,
      ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective, sup_bot_eq]
  have hf : Function.Surjective f := (dropFirst_surjective k 2).comp e.surjective
  let E := (Ideal.quotientEquivAlgOfEq k hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)
  have hE (r : R) : E (Ideal.Quotient.mk (Ideal.span {x k}) r) = f r :=
    Ideal.quotientKerAlgEquivOfSurjective_mk hf r
  have X_ne (n : ℕ) (i : Fin n) : (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ≠ 0 := by
    intro h
    have h' := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
    simp at h'
  have hr : IsSMulRegular R (x k) := fun _ _ hab => mul_left_cancel₀ (X_ne 3 2) hab
  have hr' : IsSMulRegular (R ⧸ Ideal.span {x k}) (Ideal.Quotient.mk (Ideal.span {x k}) (y k)) := by
    intro a b hab
    apply E.injective
    have h := congrArg E hab
    change E (Ideal.Quotient.mk _ (y k) * a) = E (Ideal.Quotient.mk _ (y k) * b) at h
    rw [map_mul, map_mul, hE, hy] at h
    exact mul_left_cancel₀ (X_ne 2 0) h
  have hsmul : (x k) • (⊤ : Submodule R R) = Ideal.span {x k} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map, Algebra.algebraMap_self,
      Ideal.map_id, Submodule.restrictScalars_self]
  have hm := (CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 3).2.2.2.1
  apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R
  · intro r hr
    rw [hm]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Ideal.subset_span ⟨2, rfl⟩
    · exact Ideal.subset_span ⟨1, rfl⟩
  · apply RingTheory.Sequence.IsWeaklyRegular.cons hr
    apply ((Submodule.quotEquivOfEq _ _ hsmul).isWeaklyRegular_congr [y k]).mpr
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr hr'

private theorem sup_eq_maximalIdeal :
    yz k ⊔ Ideal.span {x k} = IsLocalRing.maximalIdeal (Series k) := by
  rw [yz_eq, ← Ideal.span_union, ← Ideal.span_union,
    (CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 3).2.2.2.1]
  congr 1
  ext r
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro ((rfl | rfl) | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl

section Residue

local instance coefficientAlgebra : Algebra (Series k) k := MvPowerSeries.constantCoeff.toAlgebra

private def residueEquiv : IsLocalRing.ResidueField (Series k) ≃ₐ[Series k] k := by
  apply Classical.choice
  obtain ⟨_, _, _, _, _, _, _, e, he⟩ :=
    CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 3
  exact ⟨AlgEquiv.ofRingEquiv (f := e) he⟩

private def singletonHomologyZero : homology (secondModule k) [x k] 0 ≃ₗ[Series k] k := by
  let R := Series k
  let A := R ⧸ yz k
  let I : Ideal R := Ideal.span {x k}
  have hl : listIdeal [x k] = I := Ideal.ofList_singleton _
  have hsmul : listSubmodule (secondModule k) [x k] = (I.map (algebraMap R A)).restrictScalars R := by
    change listIdeal [x k] • (⊤ : Submodule R A) = _
    rw [hl, Ideal.smul_top_eq_map]
  exact (homologyZeroEquiv (secondModule k) [x k]).trans
    ((Submodule.quotEquivOfEq _ _ hsmul).trans
      ((Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R A))).trans
        (((DoubleQuot.quotQuotEquivQuotSupₐ R (yz k) I).trans
          ((Ideal.quotientEquivAlgOfEq R (sup_eq_maximalIdeal k)).trans
            (residueEquiv k))).toLinearEquiv)))

private theorem y_smul_second (a : secondModule k) : y k • a = 0 := by
  change Ideal.Quotient.mk (yz k) (y k) * a = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), zero_mul]

private theorem y_smul_term (n : ℕ) :
    ∀ a : (coefficientComplex (secondModule k) [x k]).X n, y k • a = 0 := by
  change ∀ a : (⋀[Series k]^n (Fin [x k].length → Series k)) ⊗[Series k] secondModule k,
    y k • a = 0
  intro a
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.smul_tmul' (R := Series k) (y k) a b,
      TensorProduct.smul_tmul (R := Series k) (y k) a b, y_smul_second,
      TensorProduct.tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

private theorem append_scalar_zero (n : ℕ) :
    (homologyScalar (coefficientComplex (secondModule k) [x k]) (y k) n).hom = 0 := by
  let C := coefficientComplex (secondModule k) [x k]
  apply LinearMap.ext
  intro h
  obtain ⟨a, ha, rfl⟩ := chainClass_surjective C n h
  change y k • chainClass C n a ha = 0
  rw [← chainClass_smul]
  -- The cycle representative is zero because y annihilates each coefficient term.
  have hz := y_smul_term k n a
  exact (chainClass_eq_zero_iff _ _ _ _).mpr ⟨0, by rw [map_zero]; exact hz.symm⟩

theorem excessTor : Specs.excessTor.{u} := by
  intro k _
  let N := secondModule k
  let C := coefficientComplex N [x k]
  obtain ⟨e, hx, _, _⟩ := quotientPowerSeries k
  have hreg : RingTheory.Sequence.IsWeaklyRegular N [x k] := by
    apply (RingTheory.Sequence.isWeaklyRegular_singleton_iff N (x k)).mpr
    intro a b hab
    apply e.injective
    have h := congrArg e hab
    change e (Ideal.Quotient.mk _ (x k) * a) = e (Ideal.Quotient.mk _ (x k) * b) at h
    rw [map_mul, map_mul, hx] at h
    exact mul_left_cancel₀ PowerSeries.X_ne_zero h
  have hvan (i : ℕ) (hi : 0 < i) : Subsingleton (C.homology i) :=
    weaklyRegular_acyclic N [x k] hreg i hi
  -- Appending y forms the cone of multiplication by y on the x-complex.
  -- Its cross term is zero on these coefficients, leaving the x-complex and its shift.
  let S := koszulAppendConeSequence N [x k] (y k)
  have hproj (n : ℕ) : Function.Injective (S.projection n).hom := by
    have : Subsingleton ((coefficientComplex N [x k]).homology (n + 1)) :=
      hvan (n + 1) (by omega)
    apply (LinearMap.injective_iff_eq_zero_of_exact (S.exact_inclusion_projection n)).mpr
    apply LinearMap.ext
    intro a
    rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  have hincl : Function.Injective
      (HomologicalComplex.homologyMap (appendInclusion N [x k] (y k) S.comparison) 0).hom :=
    (LinearMap.injective_iff_eq_zero_of_exact (S.exact_multiply_inclusion 0)).mpr
      (append_scalar_zero k 0)
  let e0 := LinearEquiv.ofBijective _ ⟨hincl, S.surjective_zero⟩
  have hsur : Function.Surjective (S.projection 0).hom :=
    (LinearMap.surjective_iff_eq_zero_of_exact (S.exact_projection_multiply 0)).mpr
      (append_scalar_zero k 0)
  let e1 := LinearEquiv.ofBijective _ ⟨hproj 0, hsur⟩
  let t (i : ℕ) : homology N [x k, y k] i ≃ₗ[Series k] Tor (firstModule k) N i := by
    change _ ≃ₗ[Series k] Tor (ModuleCat.of _ (Series k ⧸ xy k)) N i
    rw [← listIdeal_xy]
    exact koszulHomologyTorEquiv N [x k, y k] (regular_xy k) i
  refine ⟨⟨(t 0).symm.trans (e0.symm.trans (singletonHomologyZero k))⟩,
    ⟨(t 1).symm.trans (e1.trans (singletonHomologyZero k))⟩, ?_⟩
  intro i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have : Subsingleton (homology N [x k] n) := hvan n (by omega)
  exact ((hproj n).comp (t (n+1)).symm.injective).subsingleton

open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue ringDimensionValue)

theorem excessIntersection : Specs.excessIntersection.{u} := by
  intro k _
  let R := Series k
  let M := firstModule k
  let N := secondModule k
  obtain ⟨_, hreg, _, _, hdim, _, _, _⟩ :=
    CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 3
  let : IsRegularLocalRing R := hreg
  obtain ⟨⟨e0⟩, ⟨e1⟩, hvan⟩ := excessTor k
  let et := (torZeroEquiv M N).symm.trans e0
  have hlen : Module.length R k = 1 := by
    have hsur : Function.Surjective (algebraMap R k) := by
      intro a
      exact ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩
    rw [Module.length_eq_of_surjective hsur]
    exact Module.length_eq_one k k
  have hsupport : Module.support R (M ⊗[R] N) = {IsLocalRing.closedPoint R} := by
    rw [et.support_eq, ← (residueEquiv k).toLinearEquiv.support_eq]
    change Module.support R (R ⧸ IsLocalRing.maximalIdeal R) = _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact PrimeSpectrum.zeroLocus_eq_singleton (IsLocalRing.maximalIdeal R)
  have hdimM : moduleDimensionValue R M = 1 := by
    have hquot := (CompleteIntersectionEuler.quotientDimension [x k, y k] 3 (regular_xy k)
      hdim).2
    rw [listIdeal_xy] at hquot
    unfold moduleDimensionValue ringDimensionValue
    change ringKrullDim (R ⧸ Module.annihilator R (R ⧸ xy k)) = _
    rw [Ideal.annihilator_quotient]
    exact hquot
  have hdimN : moduleDimensionValue R N = 1 := by
    obtain ⟨e, _, _, _⟩ := quotientPowerSeries k
    unfold moduleDimensionValue ringDimensionValue
    change ringKrullDim (R ⧸ Module.annihilator R (R ⧸ yz k)) = _
    rw [Ideal.annihilator_quotient, e.toRingEquiv.ringKrullDim]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one (PowerSeries k)
  have hEuler : IsolatedIntersectionEuler.intersectionEuler M N = 0 := by
    rw [intersectionEuler_eq_cutoff M N 3 hdim,
      cutoffEuler_eq_of_vanishes_above M N 1 3 (by decide) hvan]
    have h0 : Module.length (Series k) (IsolatedTorSupport.Specs.Tor M N 0) = 1 := e0.length_eq.trans hlen
    have h1 : Module.length (Series k) (IsolatedTorSupport.Specs.Tor M N 1) = 1 := e1.length_eq.trans hlen
    simp [IsolatedIntersectionEuler.cutoffEuler, IsolatedIntersectionEuler.Specs.cutoffEuler,
      Finset.sum_range_succ, h0, h1]
  refine ⟨et.length_eq.trans hlen, hsupport, (tensor_support M N).symm.trans hsupport,
    hdimM, hdimN, hdim, ?_, ⟨hreg, hEuler⟩⟩
  rw [hdimM, hdimN, hdim]
  decide

end Residue

end CommutativeAlgebraNotes.Intersection.ExcessTorEulerExample
