import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.HypersurfaceLocalDualityExample
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CanonicalModuleAndConcentration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyExactSequence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.HypersurfaceExample
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Noetherian

noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open AdvCommAlg.Gorenstein
open Specs.CommutativeAlgebraNotes.HypersurfaceLocalDualityExample
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)

namespace CommutativeAlgebraNotes.HypersurfaceLocalDualityExample

universe u
variable (k : Type u) [Field k]

private theorem equation_mem : equation k ∈ maximalIdeal (Cover k) := by
  change ¬ IsUnit (equation k)
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  simp [equation]

private theorem equation_regular : IsSMulRegular (Cover k) (equation k) := by
  have nonzero (i : Fin 2) : (MvPowerSeries.X i : Cover k) ≠ 0 := by
    intro h
    have := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
    simp at this
  intro a b h
  exact mul_left_cancel₀ (mul_ne_zero (nonzero 0) (nonzero 1)) h

private theorem projection_surjective : Function.Surjective (projection k) :=
  Ideal.Quotient.mk_surjective

private theorem dimension_one : ringKrullDim (Node k) = 1 := by
  obtain ⟨_, hreg, _, _, hd, _⟩ := CompleteRegularPowerSeries.overField k 2
  letI := hreg
  have h := HypersurfaceExample.dimensionDrop (Cover k) (equation k)
    (equation_mem k) (equation_regular k)
  rw [hd] at h
  generalize he : ringKrullDim (Node k) = n at h ⊢
  cases n with
  | bot => simp at h
  | coe n =>
    change (↑(n + 1) : WithBot ℕ∞) = ↑(2 : ℕ∞) at h
    have h' : n + 1 = (2 : ℕ∞) := WithBot.coe_injective h
    have hf : n ≠ ⊤ := by rintro rfl; simp at h'
    lift n to ℕ using hf
    norm_cast at h' ⊢
    omega

private theorem nodeGorenstein : Specs.LocalGorensteinValue (Node k) := by
  letI := (CompleteRegularPowerSeries.overField k 2).2.1
  exact HypersurfaceExample.gorenstein (Cover k) (equation k)
    (equation_mem k) (equation_regular k)

private theorem nodeComplete : IsAdicComplete (maximalIdeal (Node k)) (Node k) := by
  let I := maximalIdeal (Cover k)
  haveI : IsAdicComplete I (Cover k) := (CompleteRegularPowerSeries.overField k 2).2.2.1
  let f : Cover k →ₗ[Cover k] Node k := Algebra.linearMap _ _
  have hf : Function.Surjective f := projection_surjective k
  haveI : IsPrecomplete I (Node k) := by
    apply (AdicCompletion.of_surjective_iff (I := I) (M := Node k)).mp
    intro t
    obtain ⟨s, rfl⟩ := AdicCompletion.map_surjective I hf t
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I (Cover k) s
    exact ⟨f a, (AdicCompletion.map_of _ _ _).symm⟩
  rw [← map_maximalIdeal_of_surjective (projection k) (projection_surjective k)]
  apply (IsAdicComplete.map_algebraMap_iff _ _).mpr
  exact { toIsPrecomplete := inferInstance
          toIsHausdorff := (IsHausdorff.map_algebraMap_iff (I := I)).mp (by
            change IsHausdorff (Ideal.map (projection k) I) (Node k)
            rw [map_maximalIdeal_of_surjective _ (projection_surjective k)]
            infer_instance) }

private theorem span_generators : Ideal.span {a | a ∈ generators k} = maximalIdeal (Node k) := by
  rw [← map_maximalIdeal_of_surjective (projection k) (projection_surjective k),
    (CompleteRegularPowerSeries.overField k 2).2.2.2.1, Ideal.map_span]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, generators, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_image, Set.mem_range]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨0, rfl⟩, rfl⟩
    · exact ⟨_, ⟨1, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i <;> simp

theorem coverExt : CoverExtType.{u} := by
  intro k _
  letI := (CompleteRegularPowerSeries.overField k 2).2.1
  exact HypersurfaceExample.extOne (Cover k) (equation k)
    (equation_mem k) (equation_regular k)

private theorem branch_constants (r : Node k) :
    PowerSeries.constantCoeff (xBranch k r) = PowerSeries.constantCoeff (yBranch k r) := by
  obtain ⟨s, rfl⟩ := projection_surjective k r
  rfl

@[simp] private theorem xBranch_x : xBranch k (x k) = PowerSeries.X := by
  change PowerSeries.map PowerSeries.constantCoeff (iterated k (MvPowerSeries.X 0)) = _
  simp

@[simp] private theorem xBranch_y : xBranch k (y k) = 0 := by
  change PowerSeries.map PowerSeries.constantCoeff (iterated k (MvPowerSeries.X 1)) = _
  simp

@[simp] private theorem yBranch_x : yBranch k (x k) = 0 := by
  change PowerSeries.constantCoeff (iterated k (MvPowerSeries.X 0)) = _
  simp

@[simp] private theorem yBranch_y : yBranch k (y k) = PowerSeries.X := by
  change PowerSeries.constantCoeff (iterated k (MvPowerSeries.X 1)) = _
  simp

private theorem branch_zero_injective {r : Node k}
    (hx : xBranch k r = 0) (hy : yBranch k r = 0) : r = 0 := by
  obtain ⟨s, rfl⟩ := projection_surjective k r
  let f := iterated k s
  change PowerSeries.map PowerSeries.constantCoeff f = 0 at hx
  change PowerSeries.constantCoeff f = 0 at hy
  have hd (n : ℕ) : (PowerSeries.X : PowerSeries k) ∣ PowerSeries.coeff (n+1) f := by
    apply PowerSeries.X_dvd_iff.mpr
    simpa using congrArg (PowerSeries.coeff (n+1)) hx
  choose g hg using hd
  let h : PowerSeries (PowerSeries k) := PowerSeries.mk g
  have hh : f = (PowerSeries.X * PowerSeries.C (PowerSeries.X : PowerSeries k)) * h := by
    apply PowerSeries.ext
    intro n
    rw [mul_right_comm _ _ h, mul_comm PowerSeries.X h]
    cases n with
    | zero =>
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hy
    | succ n =>
      rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X]
      simpa [h, mul_comm] using hg n
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨(iterated k).symm h, (iterated k).injective ?_⟩
  simpa only [map_mul, equation, iterated_X_zero, iterated_X_one, RingEquiv.apply_symm_apply]
    using hh

theorem coordinates : CoordinatesType.{u} := by
  intro k _
  refine ⟨?_, ?_⟩
  · intro r s hrs
    apply sub_eq_zero.mp
    refine branch_zero_injective k ?_ ?_
    · simpa [map_sub, branches] using sub_eq_zero.mpr (congrArg Prod.fst hrs)
    · simpa [map_sub, branches] using sub_eq_zero.mpr (congrArg Prod.snd hrs)
  · intro a b
    constructor
    · rintro ⟨r, hr⟩
      exact (congrArg (fun p : PowerSeries k × PowerSeries k => PowerSeries.constantCoeff p.1) hr).symm.trans
        ((branch_constants k r).trans
          (congrArg (fun p : PowerSeries k × PowerSeries k => PowerSeries.constantCoeff p.2) hr))
    · intro hc
      let f : PowerSeries (PowerSeries k) :=
        PowerSeries.map PowerSeries.C a + PowerSeries.C b -
          PowerSeries.C (PowerSeries.C (PowerSeries.constantCoeff a))
      refine ⟨projection k ((iterated k).symm f), ?_⟩
      ext1
      · change PowerSeries.map PowerSeries.constantCoeff (iterated k ((iterated k).symm f)) = a
        rw [RingEquiv.apply_symm_apply]
        simp only [f, map_sub, map_add, PowerSeries.map_C, PowerSeries.constantCoeff_C]
        have h : PowerSeries.constantCoeff.comp (PowerSeries.C : k →+* PowerSeries k) =
            RingHom.id k := by ext t; simp
        have h' : PowerSeries.map PowerSeries.constantCoeff
            (PowerSeries.map PowerSeries.C a) = a := by
          change ((PowerSeries.map PowerSeries.constantCoeff).comp
            (PowerSeries.map PowerSeries.C)) a = a
          rw [← PowerSeries.map_comp, h, PowerSeries.map_id]
          rfl
        simp [hc, h']
      · change PowerSeries.constantCoeff (iterated k ((iterated k).symm f)) = b
        rw [RingEquiv.apply_symm_apply]
        have h : PowerSeries.constantCoeff (PowerSeries.map (PowerSeries.C : k →+* PowerSeries k) a) =
            PowerSeries.C (PowerSeries.constantCoeff a) := rfl
        simp [f, h]


private theorem cover_constant (f : Cover k) :
    PowerSeries.constantCoeff (xBranchOnCover k f) = MvPowerSeries.constantCoeff f := by
  change PowerSeries.constantCoeff (PowerSeries.constantCoeff (iterated k f)) = _
  have h : ∀ g : MvPowerSeries (Fin 1) k,
      PowerSeries.constantCoeff (variableEquiv k g) = MvPowerSeries.constantCoeff g := by
    intro g
    change MvPowerSeries.constantCoeff (MvPowerSeries.rename _ g) = _
    simp
  change PowerSeries.constantCoeff (variableEquiv k
    (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k 1 f))) = _
  rw [h, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact (MvPowerSeries.coeff_coeff_finSuccEquiv f (k := 0) (x := 0)).trans (by
    rw [Finsupp.cons_zero_zero]
    rfl)

theorem nodeStructure : StructureType.{u} := by
  intro k _
  refine ⟨nodeComplete k, dimension_one k, nodeGorenstein k, span_generators k, ?_⟩
  obtain ⟨e, he⟩ := (CompleteRegularPowerSeries.overField k 2).2.2.2.2.2.2.2
  let f := projection k
  letI : IsLocalHom f := IsLocalHom.of_surjective f (projection_surjective k)
  let g := IsLocalRing.ResidueField.map f
  have hg : Function.Bijective g := by
    constructor
    · exact g.injective
    · intro a
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨s, rfl⟩ := projection_surjective k r
      exact ⟨residue (Cover k) s, IsLocalRing.ResidueField.map_residue f s⟩
  let e' := RingEquiv.ofBijective g hg
  refine ⟨e'.symm.trans e, ?_⟩
  intro r
  obtain ⟨s, rfl⟩ := projection_surjective k r
  have hr : e' (residue (Cover k) s) = residue (Node k) (projection k s) := by
    change g (residue (Cover k) s) = _
    simp [g, f]
  rw [RingEquiv.trans_apply, ← hr, RingEquiv.symm_apply_apply, he]
  exact (cover_constant k s).symm

private theorem seriesLocalization
    (branch : Node k →+* PowerSeries k) (z : Node k)
    (hs : Function.Surjective branch)
    (hz : branch z = PowerSeries.X)
    (hk : ∀ a b, branch a = branch b → z * a = z * b) :
    letI := ((algebraMap (PowerSeries k) (SeriesFraction k)).comp branch).toAlgebra
    IsLocalization.Away z (SeriesFraction k) := by
  let f := (algebraMap (PowerSeries k) (SeriesFraction k)).comp branch
  letI : Algebra (Node k) (SeriesFraction k) := f.toAlgebra
  change IsLocalization.Away z (SeriesFraction k)
  have hmap : algebraMap (Node k) (SeriesFraction k) z =
      algebraMap (PowerSeries k) (SeriesFraction k) PowerSeries.X :=
    congrArg (algebraMap (PowerSeries k) (SeriesFraction k)) hz
  refine IsLocalization.Away.mk z ?_ ?_ ?_
  · rw [hmap]
    exact IsLocalization.Away.algebraMap_isUnit PowerSeries.X
  · intro t
    obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (PowerSeries.X : PowerSeries k) t
    obtain ⟨a, rfl⟩ := hs b
    use n, a
    rw [hmap]
    exact hb
  · intro a b hab
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact hk a b (HahnSeries.ofPowerSeries_injective hab)

theorem branchLocalizations : BranchLocalizationsType.{u} := by
  intro k _
  obtain ⟨hinj, himage⟩ := coordinates k
  constructor
  · refine seriesLocalization k (xBranch k) (x k) ?_ (xBranch_x k) ?_
    · intro a
      obtain ⟨r, hr⟩ := (himage a (PowerSeries.C (PowerSeries.constantCoeff a))).mpr (by simp)
      exact ⟨r, congrArg Prod.fst hr⟩
    · intro a b h
      apply hinj
      apply Prod.ext
      · change xBranch k (x k * a) = xBranch k (x k * b)
        simp [h]
      · change yBranch k (x k * a) = yBranch k (x k * b)
        simp
  · refine seriesLocalization k (yBranch k) (y k) ?_ (yBranch_y k) ?_
    · intro b
      obtain ⟨r, hr⟩ := (himage (PowerSeries.C (PowerSeries.constantCoeff b)) b).mpr (by simp)
      exact ⟨r, congrArg Prod.snd hr⟩
    · intro a b h
      apply hinj
      apply Prod.ext
      · change xBranch k (y k * a) = xBranch k (y k * b)
        simp
      · change yBranch k (y k * a) = yBranch k (y k * b)
        simp [h]

private theorem xy_zero : x k * y k = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

open Specs.CommutativeAlgebraNotes.AugmentedCechComplex
  (Selection headDegree selected preceding product term moduleTerm localizationMap)

private abbrev selections (i : ℤ) := Selection (generators k).length i

private def emptySelection : selections k 0 := ⟨false, false, ⟨by decide⟩⟩
private def xSelection : selections k 1 := ⟨true, false, ⟨by decide⟩⟩
private def ySelection : selections k 1 := ⟨false, true, ⟨by decide⟩⟩

private theorem selection_zero (s : selections k 0) : s = emptySelection k := by
  rcases s with ⟨a, b, ⟨h⟩⟩
  cases a <;> cases b <;> first | rfl | norm_num [headDegree] at h

private theorem selection_one (s : selections k 1) :
    s = xSelection k ∨ s = ySelection k := by
  rcases s with ⟨a, b, ⟨h⟩⟩
  cases a <;> cases b
  · norm_num [headDegree] at h
  · exact Or.inr rfl
  · exact Or.inl rfl
  · norm_num [headDegree] at h

private theorem selection_other (i : ℤ) (hi : i ≠ 0) (hi' : i ≠ 1)
    (s : selections k i) : product (Node k) (generators k) s = 0 := by
  rcases s with ⟨a, b, ⟨h⟩⟩
  cases a <;> cases b
  · simp [headDegree] at h
    contradiction
  · simp [headDegree] at h
    omega
  · simp [headDegree] at h
    omega
  · change x k * (y k * 1) = 0
    rw [mul_one, xy_zero]

private theorem residue_mem_max_x : x k ∈ maximalIdeal (Node k) :=
  (span_generators k) ▸ Ideal.subset_span (by simp [generators])

private theorem residue_mem_max_y : y k ∈ maximalIdeal (Node k) :=
  (span_generators k) ▸ Ideal.subset_span (by simp [generators])

private theorem residue_smul_zero (r : Node k) (hr : r ∈ maximalIdeal (Node k))
    (a : ResidueField (Node k)) : r • a = 0 := by
  change (residue (Node k) r) * a = 0
  have h : residue (Node k) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [h, zero_mul]

private theorem zero_of_zero_summands {ι : Type} {F : ι → ModuleCat.{u} (Node k)}
    {A : ModuleCat.{u} (Node k)} (f : ∀ t, F t ⟶ A)
    (hc : IsColimit (Cofan.mk A f)) (h : ∀ t, IsZero (F t)) : IsZero A := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Cofan.IsColimit.hom_ext hc
  intro t
  exact (h t).eq_of_src _ _

private theorem ringCechZero (i : ℤ) (hi : i ≠ 0) (hi' : i ≠ 1) :
    IsZero ((ringCech k).X i) := by
  apply zero_of_zero_summands k _ (Cech.summandCofanIsColimit (generators k) i)
  intro t
  have ht := selection_other k i hi hi' t
  change IsZero (ModuleCat.of (Node k) (Localization.Away
    (product (Node k) (generators k) t)))
  rw [ht, ModuleCat.isZero_iff_subsingleton]
  exact IsLocalization.subsingleton (M := Submonoid.powers (0 : Node k))
    (S := Localization.Away (0 : Node k)) (by
    exact ⟨1, pow_one _⟩)

private theorem residueCechZero (i : ℤ) (hi : 0 < i) :
    IsZero ((residueCech k).X i) := by
  obtain ⟨e⟩ := Cech.moduleTermFormula (generators k) (residueModule k) i
  refine IsZero.of_iso ?_ e
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  rintro ⟨s⟩
  have hz : IsZero (moduleTerm (Node k) (generators k) (residueModule k) s) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply LocalizedModule.subsingleton_iff.mpr
    intro a
    refine ⟨product (Node k) (generators k) s, ⟨1, pow_one _⟩, ?_⟩
    apply residue_smul_zero
    by_cases h : i = 1
    · subst i
      rcases selection_one k s with rfl | rfl
      · simpa [xSelection] using residue_mem_max_x k
      · simpa [ySelection] using residue_mem_max_y k
    · rw [selection_other k i (ne_of_gt hi) h]
      exact (maximalIdeal _).zero_mem
  exact hz.eq_of_src _ _

private abbrev productTerm (s : selections k 1) :=
  term (Node k) (generators k) s

private abbrev LaurentPair := ModuleCat.of (Node k) (SeriesFraction k × SeriesFraction k)

set_option backward.isDefEq.respectTransparency false in
theorem ringCechCoordinates : RingCechType.{u} := by
  intro k _
  classical
  let R := Node k
  let L := SeriesFraction k
  let rs := generators k
  let T := ringCech k
  let s₀ := emptySelection k
  let sx := xSelection k
  let sy := ySelection k
  let eOne : R ≃ₐ[R] Localization.Away (1 : R) := IsLocalization.atOne _ _
  let e₀' : ringModule k ≅ term R rs s₀ := eOne.toLinearEquiv.toModuleIso
  have hi₀ : IsIso (Cech.summandι rs 0 s₀) := by
    let c := Cofan.mk (term R rs s₀) (fun s =>
      eqToHom (congrArg (fun t => term R rs t) (selection_zero k s)))
    have hc : IsColimit c := by
      refine Cofan.IsColimit.mk _ (fun t => t.inj s₀) ?_ ?_
      · intro t s
        obtain rfl := selection_zero k s
        exact Category.id_comp _
      · intro t f hf
        exact (Category.id_comp f).symm.trans (hf s₀)
    let e := hc.coconePointUniqueUpToIso (Cech.summandCofanIsColimit rs 0)
    have he : e.hom = Cech.summandι rs 0 s₀ := by
      have h := IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (Cech.summandCofanIsColimit rs 0) ⟨s₀⟩
      simpa [c] using h
    rw [← he]
    infer_instance

  let letX := (xFraction k).toAlgebra
  let letY := (yFraction k).toAlgebra
  let hx : @IsLocalization.Away R _ (x k) L _ letX := (branchLocalizations k).1
  let hy : @IsLocalization.Away R _ (y k) L _ letY := (branchLocalizations k).2
  let ex : @AlgEquiv R (Localization.Away (product R rs sx)) L _ _ _ _ letX := by
    letI := letX
    letI : IsLocalization.Away (product R rs sx) L := by
      change IsLocalization.Away (x k * 1) L
      rw [mul_one]
      exact hx
    exact IsLocalization.algEquiv (Submonoid.powers (product R rs sx)) _ _
  let ey : @AlgEquiv R (Localization.Away (product R rs sy)) L _ _ _ _ letY := by
    letI := letY
    letI : IsLocalization.Away (product R rs sy) L := by
      change IsLocalization.Away (y k * 1) L
      rw [mul_one]
      exact hy
    exact IsLocalization.algEquiv (Submonoid.powers (product R rs sy)) _ _
  let exAdd : Localization.Away (product R rs sx) ≃+ L := by
    letI : Algebra R L := letX
    exact ex.toAddEquiv
  let eyAdd : Localization.Away (product R rs sy) ≃+ L := by
    letI : Algebra R L := letY
    exact ey.toAddEquiv
  let ax : productTerm k sx ⟶ LaurentPair k := ModuleCat.ofHom
    { toFun := fun a => (exAdd a, 0)
      map_add' := by intro a b; simp
      map_smul' := by
        intro c a
        apply Prod.ext
        · letI : Algebra R L := letX
          exact ex.toLinearEquiv.map_smul c a
        · change 0 = yFraction k c * 0
          simp }
  let ay : productTerm k sy ⟶ LaurentPair k := ModuleCat.ofHom
    { toFun := fun a => (0, eyAdd a)
      map_add' := by intro a b; simp
      map_smul' := by
        intro c a
        apply Prod.ext
        · change 0 = xFraction k c * 0
          simp
        · letI : Algebra R L := letY
          exact ey.toLinearEquiv.map_smul c a }
  let a : ∀ s : selections k 1, productTerm k s ⟶ LaurentPair k :=
    fun s => if hs : s = sx then eqToHom (congrArg (productTerm k) hs) ≫ ax
      else eqToHom (congrArg (productTerm k) ((selection_one k s).resolve_left hs)) ≫ ay
  have hxs : sx ≠ sy := fun h => Bool.noConfusion (congrArg Sigma.fst h)
  have hax : a sx = ax := by simp [a]
  have hay : a sy = ay := by simp [a, Ne.symm hxs]
  let c := Cofan.mk (LaurentPair k) a
  have hc : IsColimit c := by
    let desc (t : Cofan (productTerm k)) : LaurentPair k ⟶ t.pt := ModuleCat.ofHom
      { toFun := fun z => t.inj sx (exAdd.symm z.1) + t.inj sy (eyAdd.symm z.2)
        map_add' := by intro z w; simp; abel
        map_smul' := by
          intro r z
          have h₁ : exAdd.symm (xFraction k r * z.1) = r • exAdd.symm z.1 := by
            letI : Algebra R L := letX
            exact ex.symm.toLinearEquiv.map_smul r z.1
          have h₂ : eyAdd.symm (yFraction k r * z.2) = r • eyAdd.symm z.2 := by
            letI : Algebra R L := letY
            exact ey.symm.toLinearEquiv.map_smul r z.2
          change t.inj sx (exAdd.symm (xFraction k r * z.1)) +
            t.inj sy (eyAdd.symm (yFraction k r * z.2)) = r • _
          rw [h₁, h₂, smul_add]
          simp }
    refine Cofan.IsColimit.mk _ desc ?_ ?_
    · intro t s
      rcases selection_one k s with rfl | rfl
      · change a sx ≫ desc t = t.inj sx
        rw [hax]
        ext z
        change t.inj sx (exAdd.symm (exAdd z)) + t.inj sy (eyAdd.symm 0) = _
        simp
      · change a sy ≫ desc t = t.inj sy
        rw [hay]
        ext z
        change t.inj sx (exAdd.symm 0) + t.inj sy (eyAdd.symm (eyAdd z)) = _
        simp
    · intro t m hm
      have hmx := hm sx
      have hmy := hm sy
      change a sx ≫ m = _ at hmx
      change a sy ≫ m = _ at hmy
      rw [hax] at hmx
      rw [hay] at hmy
      ext z
      have hx' := ConcreteCategory.congr_hom hmx (exAdd.symm z.1)
      have hy' := ConcreteCategory.congr_hom hmy (eyAdd.symm z.2)
      change m (exAdd (exAdd.symm z.1), 0) = _ at hx'
      change m (0, eyAdd (eyAdd.symm z.2)) = _ at hy'
      simp only [AddEquiv.apply_symm_apply] at hx' hy'
      change m z = t.inj sx (exAdd.symm z.1) + t.inj sy (eyAdd.symm z.2)
      rw [← hx', ← hy', ← map_add]
      congr 1
      exact (Prod.mk_add_mk _ _ _ _).trans (by simp) |>.symm
  let e₁ := (Cech.summandCofanIsColimit rs 1).coconePointUniqueUpToIso hc
  let e₀ : T.X 0 ≅ ringModule k := (e₀' ≪≫ asIso (Cech.summandι rs 0 s₀)).symm
  refine ⟨e₀, e₁, ?_, ringCechZero k⟩
  have hx₁ : Cech.summandι rs (0 + 1) sx ≫ e₁.hom = ax := by
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (Cech.summandCofanIsColimit rs 1) hc ⟨sx⟩).trans hax
  have hy₁ : Cech.summandι rs (0 + 1) sy ≫ e₁.hom = ay := by
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (Cech.summandCofanIsColimit rs 1) hc ⟨sy⟩).trans hay
  obtain ⟨tx, dx, htx, _, hdx⟩ := Cech.summandι_insert_localization rs 0 s₀
    (0 : Fin 2) rfl
  obtain ⟨ty, dy, hty, _, hdy⟩ := Cech.summandι_insert_localization rs 0 s₀
    (1 : Fin 2) rfl
  have htx' : tx = sx := by
    rcases selection_one k tx with h | h
    · exact h
    · have hh := htx (0 : Fin 2)
      rw [h] at hh
      change false = true at hh
      contradiction
  have hty' : ty = sy := by
    rcases selection_one k ty with h | h
    · have hh := hty (1 : Fin 2)
      rw [h] at hh
      change false = true at hh
      contradiction
    · exact h
  subst tx
  subst ty
  have hd : Cech.summandι rs 0 s₀ ≫ T.d 0 1 =
      (Cech.summandι rs 0 s₀ ≫ Cech.insertionMap false rs (0 : Fin 2) 0) +
      (Cech.summandι rs 0 s₀ ≫ Cech.insertionMap false rs (1 : Fin 2) 0) := by
    have h := Cech.summandι_differential rs 0 s₀
    change _ = ∑ a : Fin 2, (preceding s₀ a).negOnePow •
      (Cech.summandι rs 0 s₀ ≫ Cech.insertionMap false rs a 0) at h
    rw [Fin.sum_univ_two] at h
    change _ = (1 : ℤˣ) • _ + (1 : ℤˣ) • _ at h
    simp only [one_smul] at h
    change Cech.summandι rs 0 s₀ ≫ (CechComplex rs).d 0 (0 + 1) = _
    exact h
  apply (cancel_epi e₀.inv).mp
  change (e₀'.hom ≫ Cech.summandι rs 0 s₀) ≫ T.d 0 1 ≫ e₁.hom =
    e₀.inv ≫ e₀.hom ≫ ModuleCat.ofHom (diagonal k)
  rw [Iso.inv_hom_id_assoc, Category.assoc, ← Category.assoc (Cech.summandι rs 0 s₀),
    hd, hdx, hdy, Preadditive.add_comp,
    Category.assoc _ (Cech.summandι rs (0 + 1) sx), hx₁,
    Category.assoc _ (Cech.summandι rs (0 + 1) sy), hy₁]
  have hex : exAdd 1 = 1 := by
    letI : Algebra R L := letX
    exact map_one ex
  have hey : eyAdd 1 = 1 := by
    letI : Algebra R L := letY
    exact map_one ey
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  let eOne' : R ≃ₐ[R] Localization.Away (product R rs s₀) := eOne
  let locX := localizationMap R (product R rs s₀) (product R rs sx) dx
  let locY := localizationMap R (product R rs s₀) (product R rs sy) dy
  change (exAdd (locX (eOne' 1)), (0 : L)) +
    ((0 : L), eyAdd (locY (eOne' 1))) = fractionPair k 1
  rw [map_one eOne', map_one locX, map_one locY, hex, hey, map_one (fractionPair k)]
  exact Prod.ext (add_zero _) (zero_add _)

private theorem diagonal_injective : Function.Injective (diagonal k) := by
  intro r s h
  apply (coordinates k).1
  apply Prod.ext
  · exact HahnSeries.ofPowerSeries_injective (congrArg Prod.fst h)
  · exact HahnSeries.ofPowerSeries_injective (congrArg Prod.snd h)

private def ringCoefficientsIso :
    CechComplex (generators k) ≅
      Specs.CommutativeAlgebraNotes.AugmentedCechComplex.coefficients
        (Node k) (generators k) (ringModule k) :=
  (HomologicalComplex.rightUnitor (ringCech k)).symm

private def localCechIso (i : ℤ) (M : ModuleCat.{u} (Node k)) :
    (cohomology k i).obj M ≅
      (Specs.CommutativeAlgebraNotes.AugmentedCechComplex.coefficients
        (Node k) (generators k) M).homology i :=
  (localCohomologyCechComparison (maximalIdeal (Node k)) (generators k)
    (span_generators k) i).some.app M

private def ringCohomCechIso (i : ℤ) :
    (cohomology k i).obj (ringModule k) ≅ (ringCech k).homology i :=
  localCechIso k i (ringModule k) ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso (ringCoefficientsIso k).symm

private theorem ringCohomologyCoordinates :
    IsZero ((cohomology k 0).obj (ringModule k)) ∧
    Nonempty ((cohomology k 1).obj (ringModule k) ≅ ModuleCat.of (Node k) (ExplicitHull k)) := by
  obtain ⟨e₀, e₁, he, hz⟩ := ringCechCoordinates k
  let C := ringCech k
  refine ⟨?_, ?_⟩
  · refine IsZero.of_iso ?_ (ringCohomCechIso k 0)
    apply HomologicalComplex.ExactAt.isZero_homology
    rw [C.exactAt_iff' (-1) 0 1 (ComplexShape.prev_eq' _ (by decide))
      (ComplexShape.next_eq' _ (by decide))]
    let f := ModuleCat.ofHom (diagonal k)
    haveI : Mono f := (ModuleCat.mono_iff_injective _).mpr (diagonal_injective k)
    have hmComp : Mono ((ringCech k).d 0 1 ≫ e₁.hom) := by
      rw [he]
      infer_instance
    have hm : Mono (C.d 0 1) := mono_of_mono _ e₁.hom
    apply (ShortComplex.exact_iff_mono _ ?_).mpr hm
    exact (hz (-1) (by decide) (by decide)).eq_zero_of_src _
  · have h : C.d 1 2 = 0 := (hz 2 (by decide) (by decide)).eq_zero_of_tgt _
    let d := C.toCycles 0 1
    let e := C.iCyclesIso 1 2 (ComplexShape.next_eq' _ (by decide)) h
    have hd : d ≫ (e ≪≫ e₁).hom = e₀.hom ≫ ModuleCat.ofHom (diagonal k) := by
      rw [Iso.trans_hom, ← Category.assoc, HomologicalComplex.iCyclesIso_hom,
        HomologicalComplex.toCycles_i]
      exact he
    let ce := IsColimit.coconePointUniqueUpToIso (C.homologyIsCokernel 0 1 (ComplexShape.prev_eq' _ (by decide)))
      (colimit.isColimit (parallelPair d 0))
    exact ⟨ringCohomCechIso k 1 ≪≫ ce ≪≫ cokernel.mapIso _ _ e₀ (e ≪≫ e₁) hd ≪≫
      ModuleCat.cokernelIsoRangeQuotient _⟩

private theorem ringCohomologyHull (E : residueFieldEnvelopeValue (Node k)) :
    Nonempty ((cohomology k 1).obj (ringModule k) ≅ ModuleCat.of (Node k) E.carrier) := by
  let A := ModuleCat.{u} (Node k)
  let F : A ⥤ A := Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsionFunctor
    (maximalIdeal (Node k))
  let := HasDerivedCategory.standard A
  obtain ⟨e⟩ := gorenstein_top_localCohomology (nodeGorenstein k) 1 (dimension_one k) E
  let Hd := DerivedCategory.homologyFunctor A 1
  let h := AdvancedHomologicalAlgebra.CechToCohomology.natRightDerivedIso F 1
  let z := ModuleCat.of (Node k) E.carrier
  exact ⟨h.symm.app (ringModule k) ≪≫ Hd.mapIso e ≪≫
    Hd.mapIso (((DerivedCategory.singleFunctors A).shiftIso (-1 : ℤ) 1 0 (by decide)).app z) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A 1).app z⟩

private theorem residueCohomologyZero :
    Nonempty ((cohomology k 0).obj (residueModule k) ≅ residueModule k) := by
  let I := maximalIdeal (Node k)
  let e := (LocalCohomologySequence.degreeZeroIso I).app (residueModule k)
  let A := ResidueField (Node k)
  let J := Specs.CommutativeAlgebraNotes.IdealTorsion.idealTorsion I A
  have hJ : J = ⊤ := by
    apply top_unique
    intro a _
    apply (mem_idealTorsion I a).mpr
    exact ⟨1, le_rfl, fun r hr => residue_smul_zero k r (by rwa [pow_one] at hr) a⟩
  let l : J ≃ₗ[Node k] A := LinearEquiv.ofBijective J.subtype ⟨Subtype.val_injective,
    fun a => ⟨⟨a, by rw [hJ]; exact Submodule.mem_top⟩, rfl⟩⟩
  exact ⟨e ≪≫ l.toModuleIso⟩

theorem localCohomologyCalculation : CohomologyType.{u} := by
  intro k _
  obtain ⟨h₀, h₁⟩ := ringCohomologyCoordinates k
  refine ⟨h₀, h₁, ringCohomologyHull k, residueCechZero k, residueCohomologyZero k, ?_⟩
  refine IsZero.of_iso ?_ (localCechIso k 1 (residueModule k))
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ (residueCechZero k 1 (by decide))

theorem canonicalCalculation : CanonicalType.{u} := by
  intro k _ E
  let S := Cover k
  let R := Node k
  obtain ⟨_, hreg, hcS, _, hdS, _⟩ := CompleteRegularPowerSeries.overField k 2
  letI := hreg
  letI := hcS
  letI := nodeComplete k
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  let f := projection k
  letI : IsLocalHom f := IsLocalHom.of_surjective f (projection_surjective k)
  have hdR : ringKrullDim R = ((1 : ℕ) : WithBot ℕ∞) := dimension_one k
  have hCM := localGorenstein_cohenMacaulay R (nodeGorenstein k)
  have cover : ∀ J : Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel.ShiftedRingResolution S 2,
      Nonempty (canonicalModule
        (Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel.dualizingComplex f J.complex) 1 ≅
          ringModule k) := by
    intro J
    obtain ⟨_, ⟨e⟩, _⟩ := canonicalModuleExt f (projection_surjective k) hdS hdR hCM J
    obtain ⟨g⟩ := coverExt k
    exact ⟨e ≪≫ g.toModuleIso⟩
  refine ⟨?_, cover⟩
  obtain ⟨J, _⟩ := RegularCoverDualizingModel.shiftedRingResolution_exists S 2 hdS
  obtain ⟨e⟩ := cover J
  obtain ⟨_, ⟨e₁, _, _⟩, _⟩ := canonicalModuleForCover f (projection_surjective k) hdS hdR J E
  obtain ⟨_, ⟨e₂, _, _⟩, _⟩ :=
    canonicalModuleAndConcentration R 1 hdR E (generators k) (span_generators k)
  exact ⟨e₂ ≪≫ e₁.symm ≪≫ e⟩

end CommutativeAlgebraNotes.HypersurfaceLocalDualityExample
