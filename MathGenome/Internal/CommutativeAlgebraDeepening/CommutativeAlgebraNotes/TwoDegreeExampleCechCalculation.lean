import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open IsLocalRing

namespace CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation

open Specs.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation

universe u

noncomputable section

variable (k : Type u) [Field k]

private theorem maximalIdealS :
    maximalIdeal (S k) = Ideal.span {SX k, SY k} := by
  have h := (CompleteRegularPowerSeries.overField k 2).2.2.2.1
  rw [h]
  congr 1
  ext a
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨Fin.succ 0, rfl⟩

private theorem maximalIdealR :
    maximalIdeal (R k) = Ideal.span {x k, y k} := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (J k)) Ideal.Quotient.mk_surjective,
    maximalIdealS, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

private theorem x_sq : x k ^ 2 = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert _ _)

private theorem xy_zero : x k * y k = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

@[simp] private theorem project_mk (f : S k) :
    project k (Ideal.Quotient.mk (J k) f) = projectS k f := rfl

@[simp] private theorem project_x : project k (x k) = 0 := projectS_X k

@[simp] private theorem project_y : project k (y k) = PowerSeries.X := projectS_Y k

private theorem oneVariable_injective : Function.Injective (oneVariable k) := by
  intro a b hab
  apply (MvPowerSeries.finSuccEquiv k 0).injective
  exact PowerSeries.map_injective _
    (MvPowerSeries.isEmptyEquiv (Fin 0) k).injective hab

private theorem oneVariable_section (a : A k) :
    oneVariable k (oneVariableInverse k a) = a := by
  change PowerSeries.map MvPowerSeries.constantCoeff
    (MvPowerSeries.finSuccEquiv k 0 ((MvPowerSeries.finSuccEquiv k 0).symm
      (PowerSeries.map MvPowerSeries.C a))) = a
  rw [AlgEquiv.apply_symm_apply]
  ext n
  simp

private theorem project_section (a : A k) : project k (sectionR k a) = a := by
  change oneVariable k (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k 1
    ((MvPowerSeries.finSuccEquiv k 1).symm (PowerSeries.C (oneVariableInverse k a))))) = a
  rw [AlgEquiv.apply_symm_apply, PowerSeries.constantCoeff_C, oneVariable_section]

private theorem section_C (c : k) : sectionR k (PowerSeries.C c) = algebraMap k (R k) c := by
  change Ideal.Quotient.mk (J k) (sectionS k (PowerSeries.C c)) =
    Ideal.Quotient.mk (J k) (MvPowerSeries.C c)
  congr 1
  have h : oneVariableInverse k (PowerSeries.C c) = MvPowerSeries.C c := by
    apply (MvPowerSeries.finSuccEquiv k 0).injective
    change MvPowerSeries.finSuccEquiv k 0 ((MvPowerSeries.finSuccEquiv k 0).symm
      (PowerSeries.map MvPowerSeries.C (PowerSeries.C c))) = _
    rw [AlgEquiv.apply_symm_apply, PowerSeries.map_C, MvPowerSeries.finSuccEquiv_C]
  apply (MvPowerSeries.finSuccEquiv k 1).injective
  change MvPowerSeries.finSuccEquiv k 1 ((MvPowerSeries.finSuccEquiv k 1).symm
    (PowerSeries.C (oneVariableInverse k (PowerSeries.C c)))) = _
  rw [AlgEquiv.apply_symm_apply, h, MvPowerSeries.finSuccEquiv_C]

private theorem projectS_eq_zero_iff (a : S k) : projectS k a = 0 ↔ SX k ∣ a := by
  change oneVariable k (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k 1 a)) = 0 ↔ _
  rw [← map_zero (oneVariable k), (oneVariable_injective k).eq_iff, ← PowerSeries.X_dvd_iff]
  simpa [SX] using
    (map_dvd_iff (MvPowerSeries.finSuccEquiv k 1) (a := SX k) (b := a))

private theorem project_ker : RingHom.ker (project k) = xLine k := by
  ext r
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [RingHom.mem_ker, project_mk, projectS_eq_zero_iff, xLine, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk (J k) b, map_mul ..⟩
  · rintro ⟨b, hb⟩
    apply (projectS_eq_zero_iff k a).mp
    rw [← project_mk, hb, map_mul, project_x, zero_mul]

private theorem mem_maximalIdealS_iff (a : S k) :
    a ∈ maximalIdeal (S k) ↔ MvPowerSeries.constantCoeff a = 0 := by
  change ¬IsUnit a ↔ _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem mul_x_eq_constant (a : S k) :
    Ideal.Quotient.mk (J k) a * x k = (MvPowerSeries.constantCoeff a) • x k := by
  have h : a - MvPowerSeries.C (MvPowerSeries.constantCoeff a) ∈ maximalIdeal (S k) := by
    rw [mem_maximalIdealS_iff]
    simp
  rw [maximalIdealS, Ideal.mem_span_pair] at h
  obtain ⟨b, c, hbc⟩ := h
  have hx := x_sq k
  have hxy := xy_zero k
  have he := congrArg (Ideal.Quotient.mk (J k)) hbc
  simp only [map_add, map_mul, map_sub] at he
  change (Ideal.Quotient.mk (J k) b * x k + Ideal.Quotient.mk (J k) c * y k =
    Ideal.Quotient.mk (J k) a - algebraMap k (R k) (MvPowerSeries.constantCoeff a)) at he
  rw [Algebra.smul_def (R := k) _ (x k), ← sub_eq_zero, ← sub_mul, ← he, add_mul, mul_assoc, ← pow_two, hx,
    mul_zero, mul_assoc, mul_comm (y k), hxy, mul_zero, add_zero]

private theorem smul_x_eq_zero_iff (c : k) : c • x k = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hm : MvPowerSeries.C c * SX k ∈ J k :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by
        rw [map_mul]
        exact (Algebra.smul_def (R := k) c (x k)).symm ▸ h)
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hm
    have hx : SX k ≠ 0 := by
      intro h
      have hh := congrArg (MvPowerSeries.finSuccEquiv k 1) h
      exact PowerSeries.X_ne_zero (R := k) (by simp [SX] at hh)
    have hh : (a * SX k + b * SY k) * SX k = MvPowerSeries.C c * SX k := by
      linear_combination hab
    have hc := congrArg (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k))
      (mul_right_cancel₀ hx hh)
    simpa [SX, SY] using hc.symm
  · rintro rfl
    exact zero_smul _ _

private theorem mem_xLine_iff (r : R k) : r ∈ xLine k ↔ ∃ c : k, r = c • x k := by
  rw [xLine, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨MvPowerSeries.constantCoeff a, (mul_comm _ _).trans (mul_x_eq_constant k a)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨algebraMap k (R k) c, (Algebra.smul_def (R := k) c (x k)).trans (mul_comm _ _)⟩

private def splitMap : A k × k →ₗ[k] R k where
  toFun ac := sectionR k ac.1 + ac.2 • x k
  map_add' a b := by
    change sectionR k (a.1 + b.1) + (a.2 + b.2) • x k = _
    rw [map_add, add_smul]
    abel
  map_smul' c a := by
    change sectionR k (c • a.1) + (c * a.2) • x k = c • (sectionR k a.1 + a.2 • x k)
    rw [smul_add, mul_smul, Algebra.smul_def c a.1, map_mul]
    change sectionR k (PowerSeries.C c) * sectionR k a.1 + _ = _
    rw [section_C, Algebra.smul_def c (sectionR k a.1)]

private theorem project_scalar_x (c : k) : project k (c • x k) = 0 := by
  rw [Algebra.smul_def (R := k) c (x k), map_mul, project_x, mul_zero]

private theorem splitMap_bijective : Function.Bijective (splitMap k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, c⟩ h
    change sectionR k a + c • x k = 0 at h
    have ha : a = 0 := by
      simpa [project_section, project_scalar_x] using congrArg (project k) h
    have hc : c = 0 := (smul_x_eq_zero_iff k c).mp (by simpa [ha] using h)
    simp [ha, hc]
  · intro r
    let a := project k r
    have hr : r - sectionR k a ∈ xLine k := by
      rw [← project_ker, RingHom.mem_ker, map_sub, project_section, sub_self]
    obtain ⟨c, hc⟩ := (mem_xLine_iff k _).mp hr
    exact ⟨(a, c), by change sectionR k a + c • x k = r; rw [← hc]; abel⟩

theorem ringStructure : RingStructure.{u} := by
  intro k _
  exact ⟨maximalIdealR k, x_sq k, xy_zero k, project_ker k, project_y k,
    LinearEquiv.ofBijective (splitMap k) (splitMap_bijective k), fun _ _ => rfl⟩

private theorem y_mul_of_project_zero (r : R k) (hr : project k r = 0) : y k * r = 0 := by
  have hm : r ∈ xLine k := by
    rw [← project_ker, RingHom.mem_ker]
    exact hr
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hm
  rw [← mul_assoc, mul_comm (y k), xy_zero, zero_mul]

private theorem laurent_isLocalization : IsLocalization.Away (y k) (L k) := by
  have hmap : algebraMap (R k) (L k) (y k) =
      algebraMap (A k) (L k) (PowerSeries.X : A k) := by
    change algebraMap (A k) (L k) (project k (y k)) = _
    rw [project_y]
  apply IsLocalization.Away.mk
  · rw [hmap]
    exact IsLocalization.Away.algebraMap_isUnit (S := L k) (PowerSeries.X : A k)
  · intro s
    let T : PowerSeries k := PowerSeries.X
    refine ⟨(IsLocalization.Away.sec T s).2,
      sectionR k (IsLocalization.Away.sec T s).1, ?_⟩
    rw [hmap]
    change _ = algebraMap (A k) (L k) (project k (sectionR k _))
    rw [project_section]
    simpa only [map_pow] using IsLocalization.Away.sec_spec T s
  · intro a b hab
    refine ⟨1, ?_⟩
    simp only [pow_one]
    rw [← sub_eq_zero, ← mul_sub]
    apply y_mul_of_project_zero
    rw [map_sub, sub_eq_zero]
    exact IsFractionRing.injective (A k) (L k) hab

private def awayEquiv : _root_.Localization.Away (y k) ≃ₐ[R k] L k :=
  letI := laurent_isLocalization k
  IsLocalization.algEquiv (Submonoid.powers (y k)) _ _

private theorem awayEquiv_map (r : R k) :
    awayEquiv k (algebraMap (R k) (_root_.Localization.Away (y k)) r) =
      algebraMap (A k) (L k) (project k r) := (awayEquiv k).commutes r

private theorem localization_ker :
    LinearMap.ker (Algebra.linearMap (R k) (_root_.Localization.Away (y k))) = xLine k := by
  rw [← project_ker]
  ext r
  rw [LinearMap.mem_ker, RingHom.mem_ker]
  change algebraMap (R k) (_root_.Localization.Away (y k)) r = 0 ↔ project k r = 0
  rw [← (awayEquiv k).injective.eq_iff, awayEquiv_map, map_zero,
    ← map_zero (algebraMap (A k) (L k)), (IsFractionRing.injective (A k) (L k)).eq_iff]

theorem localization : Localization.{u} := by
  intro k _
  exact ⟨awayEquiv k, awayEquiv_map k, localization_ker k⟩

private theorem away_subsingleton {T : Type u} [CommRing T] (r : T) (hr : r ^ 2 = 0) :
    Subsingleton (_root_.Localization.Away r) := by
  apply subsingleton_of_zero_eq_one
  apply isUnit_zero_iff.mp
  have h := (IsLocalization.Away.algebraMap_isUnit
    (S := _root_.Localization.Away r) r).pow 2
  rwa [← map_pow, hr, map_zero] at h

private def factorIsoUnit {T : Type u} [CommRing T] (r : T) (hr : r ^ 2 = 0) :
    Cech.factor r ≅ tensorUnit (ModuleCat T) (ComplexShape.up ℤ) := by
  have hZ : IsZero (ModuleCat.of T (_root_.Localization.Away r)) :=
    letI := away_subsingleton r hr
    ModuleCat.isZero_of_subsingleton _
  have h₁ : IsZero ((Cech.factor r).X 1) := by
    simpa [Cech.factor, Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor] using hZ
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero ((Cech.factor r).X i) := by
    by_cases h : i = 1
    · rwa [h]
    · exact Cech.factor_isZero r i hi h
  let unitModule : ModuleCat T := 𝟙_ (ModuleCat T)
  change Cech.factor r ≅ (single (ModuleCat T) (ComplexShape.up ℤ) 0).obj unitModule
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · by_cases hi : i = 0
    · subst i
      have h0 : (Cech.factor r).X 0 = unitModule := rfl
      exact eqToIso h0 ≪≫ (singleObjXSelf (ComplexShape.up ℤ) 0 unitModule).symm
    · exact (hz i hi).iso (isZero_single_obj_X _ _ _ _ hi)
  · intro i j hij
    have hd : (Cech.factor r).d i j = 0 := by
      suffices j ≠ 0 ∨ i ≠ 0 by
        rcases this with h | h
        · exact (hz j h).eq_of_tgt _ _
        · exact (hz i h).eq_of_src _ _
      change i + 1 = j at hij
      omega
    rw [single_obj_d, hd, comp_zero, zero_comp]

private def cechIsoFactor :
    cechCoefficients [x k, y k] (ModuleCat.of (R k) (R k)) ≅ Cech.factor (y k) := by
  change HomologicalComplex.tensorObj (HomologicalComplex.tensorObj (Cech.factor (x k))
    (HomologicalComplex.tensorObj (Cech.factor (y k)) (tensorUnit (ModuleCat (R k)) (.up ℤ))))
    (tensorUnit (ModuleCat (R k)) (.up ℤ)) ≅ _
  exact HomologicalComplex.rightUnitor _ ≪≫
    tensorIso (factorIsoUnit _ (x_sq k)) (HomologicalComplex.rightUnitor _) ≪≫
    HomologicalComplex.leftUnitor _

theorem cechReduction : CechReduction.{u} := by
  intro k _
  exact ⟨cechIsoFactor k⟩

private abbrev localizationMap :
    ModuleCat.of (R k) (R k) ⟶ ModuleCat.of (R k) (_root_.Localization.Away (y k)) :=
  ModuleCat.ofHom (Algebra.linearMap (R k) (_root_.Localization.Away (y k)))

private theorem factor_d :
    (Cech.factor (y k)).d 0 1 = localizationMap k := by
  simp [Cech.factor, Specs.CommutativeAlgebraNotes.AugmentedCechComplex.factor]

private def factorHomologyZero :
    (Cech.factor (y k)).homology 0 ≅ ModuleCat.of (R k) (xLine k) := by
  let K := Cech.factor (y k)
  let D := K.sc' (-1) 0 1
  let e : K.sc 0 ≅ D := K.isoSc' (-1) 0 1
    (ComplexShape.prev_eq' (c := .up ℤ) (by decide : (-1 : ℤ) + 1 = 0))
    (ComplexShape.next_eq' (c := .up ℤ) (by decide : (0 : ℤ) + 1 = 1))
  have h : D.f = 0 := by
    change K.d (-1) 0 = 0
    rfl
  exact (ShortComplex.homologyFunctor _).mapIso e ≪≫
    (D.asIsoHomologyπ h).symm ≪≫ D.cyclesIsoKernel ≪≫
    eqToIso (congrArg (fun f : D.X₂ ⟶ D.X₃ => kernel f) (factor_d k)) ≪≫
    ModuleCat.kernelIsoKer (localizationMap k) ≪≫
    eqToIso (congrArg (fun P : Submodule (R k) (R k) => ModuleCat.of (R k) P)
      (localization_ker k))

private theorem laurent_range :
    (localizationMap k).hom.range.map (awayEquiv k).toLinearMap =
      powerSeriesInLaurent k := by
  rw [← LinearMap.range_comp]
  ext s
  change (∃ r : R k, awayEquiv k (algebraMap (R k) (_root_.Localization.Away (y k)) r) = s) ↔
    ∃ a : A k, algebraMap (A k) (L k) a = s
  simp only [awayEquiv_map]
  exact ⟨fun ⟨r, hr⟩ => ⟨project k r, hr⟩,
    fun ⟨a, ha⟩ => ⟨sectionR k a, by rwa [project_section]⟩⟩

private def factorHomologyOne :
    (Cech.factor (y k)).homology 1 ≅ ModuleCat.of (R k) (L k ⧸ powerSeriesInLaurent k) := by
  let K := Cech.factor (y k)
  let D := K.sc' 0 1 2
  let e : K.sc 1 ≅ D := K.isoSc' 0 1 2
    (ComplexShape.prev_eq' (c := .up ℤ) (by decide : (0 : ℤ) + 1 = 1))
    (ComplexShape.next_eq' (c := .up ℤ) (by decide : (1 : ℤ) + 1 = 2))
  have h : D.g = 0 := by
    change K.d 1 2 = 0
    rfl
  exact (ShortComplex.homologyFunctor _).mapIso e ≪≫
    D.asIsoHomologyι h ≪≫ D.opcyclesIsoCokernel ≪≫
    eqToIso (congrArg (fun f : D.X₁ ⟶ D.X₂ => cokernel f) (factor_d k)) ≪≫
    ModuleCat.cokernelIsoRangeQuotient (localizationMap k) ≪≫
    (Submodule.Quotient.equiv _ _ (awayEquiv k).toLinearEquiv (laurent_range k)).toModuleIso

private def comparison (q : ℤ) : cohomology k q ≅ (Cech.factor (y k)).homology q := by
  have hspan : Ideal.span {r | r ∈ [x k, y k]} = maximalIdeal (R k) := by
    rw [maximalIdealR]
    congr 1
    ext r
    simp
  let e := (localCohomologyCechComparison (maximalIdeal (R k)) [x k, y k] hspan q).some
  exact e.app _ ≪≫ (homologyFunctor (ModuleCat (R k)) (.up ℤ) q).mapIso (cechIsoFactor k)

theorem localCohomologyCalculation : LocalCohomology.{u} := by
  intro k _
  exact ⟨⟨comparison k 0 ≪≫ factorHomologyZero k⟩, ⟨comparison k 1 ≪≫ factorHomologyOne k⟩⟩

end
end CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation
