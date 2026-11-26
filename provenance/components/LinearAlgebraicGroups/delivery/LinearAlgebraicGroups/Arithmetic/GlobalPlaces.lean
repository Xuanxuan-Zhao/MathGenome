import Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Algebra.Polynomial.Eval.Subring

noncomputable section

open IsDedekindDomain HeightOneSpectrum
open scoped Topology ValuativeRel
open scoped NumberField Polynomial RatFunc WithZero RestrictedProduct

namespace LinearAlgebraicGroups.Arithmetic

section DedekindPlaces

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Reduction of global integers onto the residue field of the completed valuation ring. -/
theorem adicResidue_surjective (v : HeightOneSpectrum R) :
    Function.Surjective ((IsLocalRing.residue (v.adicCompletionIntegers K)).comp
      (algebraMap R (v.adicCompletionIntegers K))) := by
  let C := v.adicCompletion K
  let w : Valuation C ℤᵐ⁰ := Valued.v
  intro b
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K) b
  have hb : {z : C | w (z - x) < 1} ∈ 𝓝 (x : C) := by
    apply Valued.mem_nhds.mpr
    refine ⟨1, ?_⟩
    intro z hz
    change w (z - x) < 1
    simpa [w, ← Valuation.restrict_lt_iff] using hz
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := K)).mem_nhds hb
  change w (algebraMap K C y - x) < 1 at hy
  have hx : w (x : C) ≤ 1 := x.property
  have hy' : w (algebraMap K C y) ≤ 1 := by
    rw [← sub_add_cancel (algebraMap K C y) (x : C)]
    exact (w.map_add _ _).trans (max_le hy.le hx)
  have hyInt : v.valuation K y ≤ 1 := by
    change Valued.v ((y : K) : C) ≤ 1 at hy'
    rwa [valuedAdicCompletion_eq_valuation'] at hy'
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hyInt 1
  have ha' : w (algebraMap R C a - algebraMap K C y) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K C]
    rw [← map_sub]
    change Valued.v (((algebraMap R K a - y : K) : C)) < 1
    simpa only [valuedAdicCompletion_eq_valuation', Units.val_one] using ha
  have hd : w (algebraMap R C a - x) < 1 := by
    rw [← sub_add_sub_cancel (algebraMap R C a) (algebraMap K C y) (x : C)]
    exact (w.map_add _ _).trans_lt (max_lt ha' hy)
  refine ⟨a, ?_⟩
  change IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) a) =
    IsLocalRing.residue _ x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact (Valuation.mem_maximalIdeal_iff (v := w)).2 hd

/-- The residue field of the completed valuation ring is a quotient of the residue ring
at the original prime. -/
theorem adicResidue_finite (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  let f := (IsLocalRing.residue (v.adicCompletionIntegers K)).comp
      (algebraMap R (v.adicCompletionIntegers K))
  have hf : ∀ a ∈ v.asIdeal, f a = 0 := by
    intro a ha
    change IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) a) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).2
    change Valued.v (((algebraMap R K a : K) : v.adicCompletion K)) < 1
    rw [valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem (K := K) a).2 ha
  exact Finite.of_surjective (Ideal.Quotient.lift v.asIdeal f hf)
    (Ideal.Quotient.lift_surjective_of_surjective v.asIdeal hf (adicResidue_surjective (K := K) v))

/-- The adic completion at a prime with finite residue field is a nonarchimedean
local field, for its own valuation relation and topology. -/
theorem adicCompletion_isLocalField (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    IsNonarchimedeanLocalField (v.adicCompletion K) := by
  let C := v.adicCompletion K
  let : (Valued.v : Valuation C ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
  let : Finite (Valued.ResidueField C) := adicResidue_finite (K := K) v
  have : IsDiscreteValuationRing (Valued.integer C) :=
    (Valued.v : Valuation C ℤᵐ⁰).valuationSubring_isDiscreteValuationRing
  let : NormedField C := Valued.toNormedField C ℤᵐ⁰
  let : ProperSpace C :=
    Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  have : ValuativeRel.IsNontrivial C :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (adicCompletion.valuation K v)).2
      (inferInstanceAs ((Valued.v : Valuation C ℤᵐ⁰).IsNontrivial))
  exact ⟨⟩

theorem adicIntegers_isOpen (v : HeightOneSpectrum R) :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

theorem adicIntegers_isCompact (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  let := adicCompletion_isLocalField (K := K) v
  convert IsNonarchimedeanLocalField.isCompact_closedBall (v.adicCompletion K) 1 using 1
  ext x
  exact ((adicCompletion.valuation K v).vle_one_iff (x := x)).symm.trans
    ((ValuativeRel.valuation (v.adicCompletion K)).vle_one_iff (x := x))

end DedekindPlaces

section NumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The scalar embedding into the usual number-field adele ring. -/
abbrev numberDiagonal : K →+* NumberField.AdeleRing (𝓞 K) K := algebraMap _ _

theorem numberDiagonal_injective : Function.Injective (numberDiagonal (K := K)) :=
  NumberField.AdeleRing.algebraMap_injective (𝓞 K) K

theorem numberFiniteCompletion_isLocalField (v : NumberFinitePlace K) :
    IsNonarchimedeanLocalField (v.adicCompletion K) :=
  let := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  adicCompletion_isLocalField v

theorem numberFiniteIntegers_isCompact (v : NumberFinitePlace K) :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  let := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  adicIntegers_isCompact v

theorem number_nonintegral_finite (x : K) :
    {v : NumberFinitePlace K | (algebraMap K (v.adicCompletion K) x) ∉
      v.adicCompletionIntegers K}.Finite := by
  have h := (numberDiagonal (K := K) x).2.cofinite_mem_adicCompletionIntegers
  exact Filter.eventually_cofinite.mp h

omit [NumberField K] in
/-- A real archimedean completion is isomorphic to the real field, isometrically. -/
theorem numberRealCompletion (v : NumberField.InfinitePlace K) (h : v.IsReal) :
    ∃ e : v.Completion ≃+* ℝ, Isometry e :=
  ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal h, NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h⟩

omit [NumberField K] in
/-- A complex archimedean completion is isomorphic to the complex field, isometrically. -/
theorem numberComplexCompletion (v : NumberField.InfinitePlace K) (h : v.IsComplex) :
    ∃ e : v.Completion ≃+* ℂ, Isometry e :=
  ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex h, NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v⟩

end NumberFields

section FunctionFields

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Every nontrivial valuation ring containing a Dedekind domain in its fraction field
is the localization of that domain at a nonzero prime. -/
private theorem exists_adic_of_contains {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (V : FunctionPlace K)
    (h : ∀ r : R, algebraMap R K r ∈ V.1) :
    ∃ v : HeightOneSpectrum R, (v.valuation K).valuationSubring = V.1 := by
  let f : R →+* V.1 := (algebraMap R K).codRestrict V.1 h
  let P := Ideal.comap f (IsLocalRing.maximalIdeal V.1)
  have hunit {d : R} (hd : d ∉ P) : (algebraMap R K d)⁻¹ ∈ V.1 := by
    have hd' : IsUnit (f d) := IsLocalRing.notMem_maximalIdeal.mp hd
    obtain ⟨u, hu⟩ := hd'
    have hmul : algebraMap R K d * ((↑u⁻¹ : V.1) : K) = 1 := by
      change ((f d * (↑u⁻¹ : V.1) : V.1) : K) = 1
      rw [← hu]
      simp
    have he := eq_inv_of_mul_eq_one_right hmul
    simpa only [he] using (↑u⁻¹ : V.1).property
  have hP : P ≠ ⊥ := by
    intro he
    apply V.property
    apply top_unique
    intro x _
    obtain ⟨⟨n, d⟩, heq⟩ := IsLocalization.surj (nonZeroDivisors R) x
    have hd : (d : R) ∉ P := by
      rw [he, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero d.property
    have hdK : algebraMap R K (d : R) ≠ 0 :=
      by simpa only [map_zero] using
        (IsFractionRing.injective R K).ne (nonZeroDivisors.ne_zero d.property)
    have hx : x = algebraMap R K n * (algebraMap R K (d : R))⁻¹ := by
      exact (eq_mul_inv_iff_mul_eq₀ hdK).2 heq
    rw [hx]
    exact mul_mem (h n) (hunit hd)
  let v : HeightOneSpectrum R := ⟨P, Ideal.IsPrime.comap f, hP⟩
  refine ⟨v, (ValuationSubring.eq_of_le_of_ne_top (v.valuation K).valuationSubring ?_ V.property)⟩
  intro x hx
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  have hd : (d : R) ∉ P := d.property
  have hdK : algebraMap R K (d : R) ≠ 0 := by
    rw [← map_zero (algebraMap R K), (IsFractionRing.injective R K).ne_iff]
    intro h0
    exact hd (h0 ▸ P.zero_mem)
  rw [(eq_mul_inv_iff_mul_eq₀ hdK).2 hnd]
  exact mul_mem (h n) (hunit hd)

namespace SeparatingParameter

private theorem integers_contained [Finite F] (t : SeparatingParameter F K)
    (V : FunctionPlace K) (ht : t.element ∈ V.1) :
    ∀ a : t.integerRing, algebraMap t.integerRing K a ∈ V.1 := by
  let f := (algebraMap F K).codRestrict V.1
    (fun c => by
      rw [← V.1.valuationSubring_valuation]
      exact FiniteField.valuation_algebraMap_le_one V.1.valuation c)
  let : Algebra F V.1 := f.toAlgebra
  let : IsScalarTower F V.1 K := IsScalarTower.of_algebraMap_eq' rfl
  let g := (Polynomial.aeval (R := F) (⟨t.element, ht⟩ : V.1)).toRingHom
  let : Algebra F[X] V.1 := g.toAlgebra
  let : Algebra F[X] K := t.polynomialAlgebra
  let : IsScalarTower F[X] V.1 K := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro p
    exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom F V.1 K) (⟨t.element, ht⟩ : V.1) p)
  have : IsIntegrallyClosed V.1 := by
    rw [← ValuationSubring.valuationSubring_valuation V.1]
    exact (Valuation.integer.integers V.1.valuation).isIntegrallyClosed
  intro a
  have ha : IsIntegral F[X] (algebraMap t.integerRing K a) := a.property
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp (ha.tower_top (A := V.1))
  rw [← hb]
  exact b.property

/-- At a prime of the parameter's normalization, the valuation ring defines
an intrinsic place. -/
def placeOfPrime (t : SeparatingParameter F K) (v : HeightOneSpectrum t.integerRing) :
    FunctionPlace K :=
  ⟨(v.valuation K).valuationSubring, fun h =>
    (((v.valuation K).valuationSubring_eq_top_iff).mp h) inferInstance⟩

theorem placeOfPrime_injective (t : SeparatingParameter F K) :
    Function.Injective t.placeOfPrime := by
  intro v w h
  exact HeightOneSpectrum.valuationSubring_valuation_injective K (congrArg Subtype.val h)

theorem range_placeOfPrime [Finite F] (t : SeparatingParameter F K) :
    Set.range t.placeOfPrime = {v : FunctionPlace K | t.element ∈ v.1} := by
  ext V
  constructor
  · rintro ⟨v, rfl⟩
    let : Algebra F[X] K := t.polynomialAlgebra
    have hi : IsIntegral F[X] t.element := by
      have he : algebraMap F[X] K Polynomial.X = t.element := Polynomial.aeval_X _
      rw [← he]
      exact isIntegral_algebraMap
    let a : t.integerRing := ⟨t.element, hi⟩
    exact v.valuation_le_one (K := K) a
  · intro ht
    obtain ⟨v, hv⟩ := exists_adic_of_contains V (t.integers_contained V ht)
    exact ⟨v, Subtype.ext hv⟩

/-- The primes on the affine charts for the parameter and its inverse cover every
intrinsic place. -/
theorem range_placeOfPrime_union_inverse [Finite F] (t : SeparatingParameter F K) :
    Set.range t.placeOfPrime ∪ Set.range t.inverse.placeOfPrime = Set.univ := by
  rw [t.range_placeOfPrime, t.inverse.range_placeOfPrime]
  ext v
  simpa [SeparatingParameter.inverse] using v.1.mem_or_inv_mem t.element

/-- The places above infinity are the intrinsic places at which the parameter has
a pole. They are indexed by those primes of the inverse chart containing its parameter. -/
theorem poles_eq_image (t : SeparatingParameter F K) [Finite F] :
    {v : FunctionPlace K | t.element ∉ v.1} =
      t.inverse.placeOfPrime '' {v | (v.valuation K) t.element⁻¹ < 1} := by
  ext V
  constructor
  · intro h
    have h' : t.inverse.element ∈ V.1 := (V.1.mem_or_inv_mem t.element).resolve_left h
    have hmem : V ∈ Set.range t.inverse.placeOfPrime := by
      rw [t.inverse.range_placeOfPrime]
      exact h'
    obtain ⟨v, rfl⟩ := hmem
    exact ⟨v, by
      change ¬ (v.valuation K) t.element ≤ 1 at h
      change (v.valuation K) t.element⁻¹ < 1
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (lt_of_not_ge h), rfl⟩
  · rintro ⟨v, hv, rfl⟩
    change (v.valuation K) t.element⁻¹ < 1 at hv
    change ¬ (v.valuation K) t.element ≤ 1
    have ht : t.element ≠ 0 := fun h => t.transcendental (h ▸ isAlgebraic_zero)
    rw [map_inv₀, inv_lt_one₀ ((v.valuation K).pos_iff.mpr ht)] at hv
    exact hv.not_ge

open Classical in
/-- The intrinsic places with a pole of the parameter are exactly the extensions
of Mathlib's infinity valuation on the rational function field. -/
theorem comap_eq_infty_iff [Finite F] (t : SeparatingParameter F K) (V : FunctionPlace K) :
    V.1.comap t.rationalMap.toRingHom = (RatFunc.inftyValuation F).valuationSubring ↔
      t.element ∉ V.1 := by
  have hX : t.rationalMap RatFunc.X = t.element :=
    RatFunc.algEquivOfTranscendental_X t.element t.transcendental
  constructor
  · intro h ht
    have hx : (RatFunc.X : F⟮X⟯) ∈ V.1.comap t.rationalMap.toRingHom := by
      change t.rationalMap RatFunc.X ∈ V.1
      rwa [hX]
    rw [h, Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hx
    omega
  · intro ht
    let w := V.1.valuation.comap t.rationalMap.toRingHom
    have hw : 1 < w RatFunc.X := by
      change 1 < V.1.valuation (t.rationalMap RatFunc.X)
      rw [hX]
      exact lt_of_not_ge (fun h => ht (V.1.valuationSubring_valuation ▸ h))
    have hval (p : F[X]) (hp : p ≠ 0) :
        w (algebraMap F[X] F⟮X⟯ p) = w RatFunc.X ^ p.natDegree :=
      Polynomial.valuation_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X F hw hp
    have hring : w.valuationSubring = V.1.comap t.rationalMap.toRingHom := by
      ext x
      change V.1.valuation (t.rationalMap x) ≤ 1 ↔ t.rationalMap x ∈ V.1
      exact Iff.of_eq (congrArg (fun S : ValuationSubring K => t.rationalMap x ∈ S)
        V.1.valuationSubring_valuation)
    rw [← hring]
    ext x
    change w x ≤ 1 ↔ RatFunc.inftyValuation F x ≤ 1
    by_cases hx : x = 0
    · simp [hx]
    trans x.num.natDegree ≤ x.denom.natDegree
    · nth_rw 1 [← x.num_div_denom]
      rw [map_div₀, hval _ (RatFunc.num_ne_zero hx), hval _ x.denom_ne_zero,
        div_le_iff₀ (pow_pos (zero_lt_one.trans hw) _), one_mul]
      exact (pow_right_strictMono₀ hw).le_iff_le
    · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F hx,
        ← WithZero.exp_zero, WithZero.exp_le_exp, RatFunc.intDegree, sub_nonpos]
      exact_mod_cast Iff.rfl

end SeparatingParameter
end FunctionFields

section FunctionCompletions

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

namespace SeparatingParameter

/-- The chosen parameter viewed as an integer of its affine chart. -/
def parameterInteger (t : SeparatingParameter F K) : t.integerRing := by
  let : Algebra F[X] K := t.polynomialAlgebra
  exact algebraMap F[X] t.integerRing Polynomial.X

private theorem parameterInteger_val (t : SeparatingParameter F K) :
    algebraMap t.integerRing K t.parameterInteger = t.element :=
  Polynomial.aeval_X _

/-- Only finitely many places lie above the pole of a separating parameter. -/
theorem finite_poles [Finite F] (t : SeparatingParameter F K) :
    {v : FunctionPlace K | t.element ∉ v.1}.Finite := by
  rw [t.poles_eq_image]
  apply Set.Finite.image
  let a := t.inverse.parameterInteger
  have ha : a ≠ 0 := by
    intro h0
    have hzero := congrArg (algebraMap t.inverse.integerRing K) h0
    rw [map_zero, t.inverse.parameterInteger_val] at hzero
    exact t.inverse.transcendental (hzero ▸ isAlgebraic_zero)
  have hset : {v : HeightOneSpectrum t.inverse.integerRing | (v.valuation K) t.element⁻¹ < 1} =
      {v | v.asIdeal ∣ Ideal.span {a}} := by
    ext v
    change (v.valuation K) t.inverse.element < 1 ↔ v.asIdeal ∣ Ideal.span {a}
    rw [← t.inverse.parameterInteger_val, v.valuation_lt_one_iff_mem (K := K),
      Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [hset]
  exact Ideal.finite_factors (by simpa using ha)

private theorem adicValuationEquiv (t : SeparatingParameter F K) (v : HeightOneSpectrum t.integerRing) :
    (t.placeOfPrime v).1.valuation.IsEquiv (v.valuation K) :=
  ((Valuation.isEquiv_iff_valuationSubring _ _).2
    ((t.placeOfPrime v).1.valuationSubring_valuation))

/-- The canonical completion at the intrinsic place agrees with the adic
completion at a prime of either affine chart. -/
def completionEquiv (t : SeparatingParameter F K) (v : HeightOneSpectrum t.integerRing) :
    (t.placeOfPrime v).Completion ≃+* v.adicCompletion K := by
  let h := t.adicValuationEquiv v
  exact (UniformSpace.Completion.mapRingEquiv (WithVal.congr _ _ (RingEquiv.refl K))
    h.uniformContinuous_congr.continuous h.symm.uniformContinuous_congr.continuous).trans
      (adicCompletion.equiv K v).symm

theorem completionEquiv_isUniformInducing (t : SeparatingParameter F K)
    (v : HeightOneSpectrum t.integerRing) : IsUniformInducing (t.completionEquiv v) :=
  (adicCompletion.uniformEquiv K v).symm.isUniformInducing.comp
    (UniformSpace.Completion.mapEquiv (t.adicValuationEquiv v).uniformEquiv).isUniformInducing

theorem completionEquiv_embedding (t : SeparatingParameter F K)
    (v : HeightOneSpectrum t.integerRing) (x : K) :
    t.completionEquiv v ((t.placeOfPrime v).embedding x) = algebraMap K (v.adicCompletion K) x := by
  let h := t.adicValuationEquiv v
  unfold completionEquiv FunctionPlace.embedding
  change (adicCompletion.equiv K v).symm
    (UniformSpace.Completion.mapRingHom _ h.uniformContinuous_congr.continuous
      (↑((WithVal.equiv (t.placeOfPrime v).1.valuation).symm x) :
        (t.placeOfPrime v).Completion)) = _
  let f := WithVal.congr (t.placeOfPrime v).1.valuation (v.valuation K) (RingEquiv.refl K)
  exact congrArg (adicCompletion.equiv K v).symm
    (UniformSpace.Completion.mapRingHom_coe (f := f.toRingHom)
      h.uniformContinuous_congr.continuous ((WithVal.equiv (t.placeOfPrime v).1.valuation).symm x))

theorem completionEquiv_mem_integers (t : SeparatingParameter F K)
    (v : HeightOneSpectrum t.integerRing) (x : (t.placeOfPrime v).Completion) :
    t.completionEquiv v x ∈ v.adicCompletionIntegers K ↔ x ∈ (t.placeOfPrime v).integers := by
  change Valued.v (t.completionEquiv v x) ≤ 1 ↔ Valued.v x ≤ 1
  rw [← adicCompletion.valued_toCompletion_apply]
  exact (t.adicValuationEquiv v).valuedCompletion_le_one_iff.symm

end SeparatingParameter

private theorem polynomial_hasFiniteQuotients (F : Type*) [Field F] [Finite F] :
    Ring.HasFiniteQuotients F[X] where
  finiteQuotient {I} hI := by
    obtain ⟨p, rfl⟩ := Submodule.IsPrincipal.principal I
    have hp : p ≠ 0 := by
      intro h
      subst p
      exact hI (by simp)
    let : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hp).finite
    exact (Module.finite_of_finite F : Finite (AdjoinRoot p))

namespace SeparatingParameter

theorem integerRing_hasFiniteQuotients [Finite F] (t : SeparatingParameter F K) :
    Ring.HasFiniteQuotients t.integerRing := by
  let : Ring.HasFiniteQuotients F[X] := polynomial_hasFiniteQuotients F
  let : Algebra F[X] K := t.polynomialAlgebra
  let : Algebra F⟮X⟯ K := t.rationalAlgebra
  let : Module.Finite F[X] t.integerRing :=
    (IsIntegralClosure.finite F[X] F⟮X⟯ K (FunctionField.ringOfIntegers F K) :
      Module.Finite F[X] (FunctionField.ringOfIntegers F K))
  exact (Ring.HasFiniteQuotients.of_module_finite F[X] (FunctionField.ringOfIntegers F K) :
    Ring.HasFiniteQuotients (FunctionField.ringOfIntegers F K))

theorem placeOfPrime_completion_comparison (t : SeparatingParameter F K)
    (v : HeightOneSpectrum t.integerRing) :
    ∃ e : (t.placeOfPrime v).Completion ≃+* v.adicCompletion K,
      IsUniformInducing e ∧
      (∀ x : K, e ((t.placeOfPrime v).embedding x) = algebraMap K (v.adicCompletion K) x) ∧
      ∀ x, e x ∈ v.adicCompletionIntegers K ↔ x ∈ (t.placeOfPrime v).integers :=
  ⟨t.completionEquiv v, t.completionEquiv_isUniformInducing v, t.completionEquiv_embedding v,
    t.completionEquiv_mem_integers v⟩

end SeparatingParameter

namespace FunctionPlace

/-- Integrality in the completion restricts to membership in the original valuation ring. -/
theorem embedding_mem_integers (v : FunctionPlace K) (x : K) :
    v.embedding x ∈ v.integers ↔ x ∈ v.1 := by
  change Valued.v (v.embedding x) ≤ 1 ↔ x ∈ v.1
  have h : (v.1.valuation x ≤ 1) ↔ x ∈ v.1 :=
    Iff.of_eq (congrArg (fun V : ValuationSubring K => x ∈ V) v.1.valuationSubring_valuation)
  refine Iff.trans ?_ h
  change Valued.v (↑((WithVal.equiv v.1.valuation).symm x) : v.Completion) ≤ 1 ↔ _
  rw [Valued.valuedCompletion_apply]
  rfl

/-- The extended valuation used to define the local integers is compatible with
the valuative relation on the completion. -/
theorem completionValuation_compatible (v : FunctionPlace K) :
    (Valued.v (R := v.Completion)).Compatible := by
  let old : Valuation v.Completion v.1.ValueGroup := Valued.v
  let new := ValuativeRel.valuation v.Completion
  have heq : old.valuationSubring = new.valuationSubring := by
    ext x
    change old x ≤ 1 ↔ new x ≤ 1
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      have ho : IsClopen (old.valuationSubring : Set v.Completion) :=
        Valued.isClopen_valuationSubring _
      have hn : IsClopen (new.valuationSubring : Set v.Completion) :=
        new.isClopen_valuationSubring
      exact (Homeomorph.refl v.Completion).isClosed_setOfPred_iff ho hn
    | ih x =>
      rw [new.vle_one_iff.symm]
      have hh : (x : v.Completion) ≤ᵥ (1 : v.Completion) ↔ x ≤ᵥ 1 := by
        rw [← UniformSpace.Completion.coe_one]
        exact UniformSpace.Completion.coe_vle_coe_iff
      rw [hh, (WithVal.valuation v.1.valuation).vle_one_iff]
      change Valued.v (x : v.Completion) ≤ 1 ↔ _
      rw [Valued.valuedCompletion_apply]
      rfl
  constructor
  intro a b
  exact new.vle_iff_le.trans
    ((Valuation.isEquiv_iff_valuationSubring old new).2 heq).le_iff_le.symm

theorem completion_isLocalField [Finite F] (t : SeparatingParameter F K) (v : FunctionPlace K) :
    IsNonarchimedeanLocalField v.Completion := by
  have hv : v ∈ Set.range t.placeOfPrime ∪ Set.range t.inverse.placeOfPrime := by
    rw [t.range_placeOfPrime_union_inverse]
    trivial
  have hchart (s : SeparatingParameter F K) (w : HeightOneSpectrum s.integerRing) :
      LocallyCompactSpace (s.placeOfPrime w).Completion := by
    let := s.integerRing_hasFiniteQuotients
    let := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    let : IsNonarchimedeanLocalField (w.adicCompletion K) := adicCompletion_isLocalField w
    let e : (s.placeOfPrime w).Completion ≃ᵤ w.adicCompletion K :=
      (UniformSpace.Completion.mapEquiv (s.adicValuationEquiv w).uniformEquiv).trans
        (adicCompletion.uniformEquiv K w).symm
    exact e.toHomeomorph.locallyCompactSpace_iff.mpr inferInstance
  have : LocallyCompactSpace v.Completion := by
    rcases hv with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact hchart t w
    · exact hchart t.inverse w
  have : ValuativeRel.IsNontrivial v.Completion := by
    have hnt : v.1.valuation.IsNontrivial := by
      by_contra h
      exact v.property (v.1.eq_top_iff.mpr h)
    obtain ⟨x, hx, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := v.1.valuation)
    let y := (WithVal.equiv v.1.valuation).symm x
    have hy : y <ᵥ (1 : WithVal v.1.valuation) := by
      rw [(WithVal.valuation v.1.valuation).vlt_one_iff]
      exact hx1
    have hy' := UniformSpace.Completion.coe_vlt_coe_iff.mpr hy
    have hq : ValuativeRel.valuation v.Completion (↑y : v.Completion) < 1 := by
      apply (ValuativeRel.valuation v.Completion).vlt_one_iff.mp
      simpa only [UniformSpace.Completion.coe_one] using hy'
    refine ⟨ValuativeRel.valuation v.Completion (↑y : v.Completion), ?_, hq.ne⟩
    have hx0 : x ≠ 0 := by simpa using hx
    have hy0 : y ≠ 0 := by simpa [y] using hx0
    simpa using hy0
  exact ⟨⟩

private theorem integers_at_chart (t : SeparatingParameter F K) [Finite F]
    (w : HeightOneSpectrum t.integerRing) :
    IsCompact ((t.placeOfPrime w).integers : Set (t.placeOfPrime w).Completion) ∧
      Finite (IsLocalRing.ResidueField (t.placeOfPrime w).integers) := by
  let := t.integerRing_hasFiniteQuotients
  let := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  let e := t.completionEquiv w
  have he := t.completionEquiv_mem_integers w
  let eh := (e.toEquiv.toUniformEquivOfIsUniformInducing
    (t.completionEquiv_isUniformInducing w)).toHomeomorph
  have hs : ((t.placeOfPrime w).integers : Set (t.placeOfPrime w).Completion) =
      eh ⁻¹' (w.adicCompletionIntegers K : Set (w.adicCompletion K)) := Set.ext fun x => (he x).symm
  refine ⟨hs.symm ▸ eh.isCompact_preimage.mpr (adicIntegers_isCompact w), ?_⟩
  let f : (t.placeOfPrime w).integers →+* w.adicCompletionIntegers K :=
    (e.toRingHom.comp (t.placeOfPrime w).integers.subtype).codRestrict _
      (fun x => (he x).2 x.property)
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := e.surjective y.val
    exact ⟨⟨x, (he x).1 (hx.symm ▸ y.property)⟩, Subtype.ext hx⟩
  let g := RingEquiv.ofBijective f hf
  let := adicResidue_finite (K := K) w
  exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv g).symm.toEquiv

theorem completionIntegers_properties [Finite F] (t : SeparatingParameter F K)
    (v : FunctionPlace K) :
    IsCompact (v.integers : Set v.Completion) ∧ IsOpen (v.integers : Set v.Completion) ∧
      Finite (IsLocalRing.ResidueField v.integers) := by
  have hv : v ∈ Set.range t.placeOfPrime ∪ Set.range t.inverse.placeOfPrime := by
    rw [t.range_placeOfPrime_union_inverse]
    trivial
  have h : IsCompact (v.integers : Set v.Completion) ∧
      Finite (IsLocalRing.ResidueField v.integers) := by
    rcases hv with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact integers_at_chart t w
    · exact integers_at_chart t.inverse w
  exact ⟨h.1, Valued.isOpen_valuationSubring _, h.2⟩

theorem nonintegral_finite [Finite F] (t : SeparatingParameter F K) (x : K) :
    {v : FunctionPlace K | v.embedding x ∉ v.integers}.Finite := by
  have hsubset : {v : FunctionPlace K | v.embedding x ∉ v.integers} ⊆
      t.placeOfPrime '' HeightOneSpectrum.Support t.integerRing x ∪
        {v : FunctionPlace K | t.element ∉ v.1} := by
    intro v hv
    by_cases ht : t.element ∈ v.1
    · have hm : v ∈ Set.range t.placeOfPrime := by rw [t.range_placeOfPrime]; exact ht
      obtain ⟨w, rfl⟩ := hm
      left
      refine ⟨w, ?_, rfl⟩
      change 1 < w.valuation K x
      exact lt_of_not_ge (fun h => hv ((embedding_mem_integers _ _).2 h))
    · exact Or.inr ht
  exact (((HeightOneSpectrum.Support.finite t.integerRing x).image t.placeOfPrime).union
    t.finite_poles).subset hsubset

end FunctionPlace

/-- The scalar diagonal into the full function-field adele ring. -/
def functionDiagonal [Finite F] (t : SeparatingParameter F K) : K →+* FunctionAdeleRing K where
  toFun x := ⟨fun v => v.embedding x,
    Filter.eventually_cofinite.mpr (FunctionPlace.nonintegral_finite t x)⟩
  map_zero' := Subtype.ext (funext fun v => map_zero v.embedding)
  map_one' := Subtype.ext (funext fun v => map_one v.embedding)
  map_add' x y := Subtype.ext (funext fun v => map_add v.embedding x y)
  map_mul' x y := Subtype.ext (funext fun v => map_mul v.embedding x y)

theorem functionDiagonal_apply [Finite F] (t : SeparatingParameter F K) (x : K)
    (v : FunctionPlace K) : functionDiagonal t x v = v.embedding x := rfl

theorem functionDiagonal_independent [Finite F] (s t : SeparatingParameter F K) :
    functionDiagonal s = functionDiagonal t := by
  apply RingHom.ext
  intro x
  exact Subtype.ext rfl

theorem functionDiagonal_unique [Finite F] (t : SeparatingParameter F K) :
    ∃! d : K →+* FunctionAdeleRing K, ∀ (x : K) (v : FunctionPlace K),
      d x v = v.embedding x := by
  refine ⟨functionDiagonal t, functionDiagonal_apply t, ?_⟩
  intro d hd
  apply RingHom.ext
  intro x
  exact Subtype.ext (funext (hd x))

theorem functionDiagonal_injective [Finite F] (t : SeparatingParameter F K) :
    Function.Injective (functionDiagonal t) := by
  let : Algebra F[X] K := t.polynomialAlgebra
  let : Algebra F⟮X⟯ K := t.rationalAlgebra
  have h : ¬IsField t.integerRing := FunctionField.ringOfIntegers.not_isField F K
  obtain ⟨P, hP, hp⟩ := Ring.not_isField_iff_exists_prime.mp h
  let v : HeightOneSpectrum t.integerRing := ⟨P, hp, hP⟩
  intro x y he
  exact (t.placeOfPrime v).embedding.injective (congrArg (fun a : FunctionAdeleRing K =>
    a (t.placeOfPrime v)) he)

end FunctionCompletions


namespace GlobalFieldData

universe u v
variable {K : Type u} [Field K]

/-- The diagonal homomorphism into the scalar adele ring of a global field. -/
def diagonal (D : GlobalFieldData.{u, v} K) : K →+* D.AdeleRing :=
  match D with
  | .number h => letI := h; numberDiagonal
  | @function _ _ _ _ _ _ t => functionDiagonal t

theorem diagonal_injective (D : GlobalFieldData.{u, v} K) :
    Function.Injective D.diagonal := by
  cases D with
  | number h =>
    let := h
    exact numberDiagonal_injective
  | function F t => exact functionDiagonal_injective t

theorem coordinate_diagonal (D : GlobalFieldData.{u, v} K) (w : D.Place) (x : K) :
    D.coordinate w (D.diagonal x) = D.embedding w x := by
  cases D <;> cases w
  · rfl
  · rfl
  · rfl
  · exact PEmpty.elim ‹_›

theorem finite_nonintegral (D : GlobalFieldData.{u, v} K) (x : K) :
    {w : D.FinitePlace | D.embedding (.inl w) x ∉ D.integers w}.Finite := by
  cases D with
  | number h =>
    let := h
    exact number_nonintegral_finite x
  | function F t => exact FunctionPlace.nonintegral_finite t x

instance finiteCompletion_isLocalField (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) :
    IsNonarchimedeanLocalField (D.FiniteCompletion w) := by
  cases D with
  | number h =>
    let := h
    exact numberFiniteCompletion_isLocalField w
  | function F t => exact FunctionPlace.completion_isLocalField t w

theorem integers_properties (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) :
    IsCompact (D.integers w : Set (D.FiniteCompletion w)) ∧
      IsOpen (D.integers w : Set (D.FiniteCompletion w)) ∧
      Finite (IsLocalRing.ResidueField (D.integers w)) := by
  cases D with
  | number h =>
    let := h
    let := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    exact ⟨adicIntegers_isCompact w, adicIntegers_isOpen w, adicResidue_finite w⟩
  | function F t => exact FunctionPlace.completionIntegers_properties t w

/-- The supplied local integers are the unit ball of the completion's own
valuative relation. -/
theorem integers_eq_valuationSubring (D : GlobalFieldData.{u, v} K)
    (w : D.FinitePlace) :
    D.integers w = (ValuativeRel.valuation (D.FiniteCompletion w)).valuationSubring := by
  cases D with
  | number h =>
    let := h
    change (adicCompletion.valuation K w).valuationSubring =
      (ValuativeRel.valuation (w.adicCompletion K)).valuationSubring
    exact (Valuation.isEquiv_iff_valuationSubring _ _).1 (ValuativeRel.isEquiv _ _)
  | function F t =>
    let := FunctionPlace.completionValuation_compatible w
    change (Valued.v (R := w.Completion)).valuationSubring =
      (ValuativeRel.valuation w.Completion).valuationSubring
    exact (Valuation.isEquiv_iff_valuationSubring _ _).1 (ValuativeRel.isEquiv _ _)

instance adele_isTopologicalRing (D : GlobalFieldData.{u, v} K) :
    IsTopologicalRing D.AdeleRing := by
  cases D with
  | number h =>
    let := h
    exact inferInstanceAs (IsTopologicalRing (NumberField.AdeleRing (𝓞 K) K))
  | function F t =>
    let : Fact (∀ w : FunctionPlace K, IsOpen (w.integers : Set w.Completion)) :=
      ⟨fun w => (FunctionPlace.completionIntegers_properties t w).2.1⟩
    exact RestrictedProduct.isTopologicalRing (fun w : FunctionPlace K => w.Completion)

/-- The scalar diagonal is an embedding of fields into their actual adele ring
in the sense of an injective ring homomorphism with the canonical coordinates. -/
theorem exists_diagonal (D : GlobalFieldData.{u, v} K) :
    ∃ d : K →+* D.AdeleRing, Function.Injective d ∧
      ∀ w x, D.coordinate w (d x) = D.embedding w x :=
  ⟨D.diagonal, D.diagonal_injective, D.coordinate_diagonal⟩

end GlobalFieldData

/-- The ring of integers of any nonarchimedean local field is compact and open.
The canonical valuation is discrete and its residue field is finite. -/
theorem localField_properties (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ValuativeRel.IsDiscrete K ∧
      Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).valuationSubring) ∧
      IsCompact ((ValuativeRel.valuation K).valuationSubring : Set K) ∧
      IsOpen ((ValuativeRel.valuation K).valuationSubring : Set K) := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  refine ⟨inferInstance, ?_, IsNonarchimedeanLocalField.isCompact_closedBall K 1, ?_⟩
  · exact IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation K
  · exact Valued.isOpen_valuationSubring K

/-- Completeness holds for the uniformity compatible with the additive topology. -/
theorem localField_complete (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
    [IsUniformAddGroup K] [IsNonarchimedeanLocalField K] : CompleteSpace K :=
  inferInstance

section FiniteExtensions

open ValuativeRel
open scoped NNReal

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A finite extension carries a unique extended valuative relation. Its topology
is the finite-dimensional vector-space topology, and it is again a local field. -/
theorem finiteExtension_localField :
    ∃ r : ValuativeRel L, ∃ T : TopologicalSpace L,
      letI : ValuativeRel L := r
      letI : TopologicalSpace L := T
      ValuativeExtension K L ∧ IsNonarchimedeanLocalField L ∧
        Finite (IsLocalRing.ResidueField (ValuativeRel.valuation L).valuationSubring) ∧
        (∀ b : Module.Basis (Fin (Module.finrank K L)) K L,
          Continuous b.equivFun ∧ Continuous b.equivFun.symm) ∧
        ∀ s : ValuativeRel L, @ValuativeExtension K L _ _ _ s _ → s = r := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  let v := valuation K
  let hv := (inferInstance : IsRankLeOne K).nonempty.some
  let : (Valued.v (R := K)).RankOne :=
    { hom' := hv.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := hv.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  let : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  let w : Valuation L ℝ≥0 := NormedField.valuation
  let r : ValuativeRel L := .ofValuation w
  let : ValuativeRel L := r
  let : w.Compatible := Valuation.Compatible.ofValuation w
  let : Valued L ℝ≥0 := NormedField.toValued
  have : IsValuativeTopology L :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle w (fun {s} =>
      Valued.is_topological_valuation s)
  have : LocallyCompactSpace L := LocallyCompactSpace.of_finiteDimensional_of_complete K L
  have : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial w).2 inferInstance
  have localL : IsNonarchimedeanLocalField L := ⟨⟩
  have extL : ValuativeExtension K L := by
    constructor
    intro x y
    rw [w.vle_iff_le, v.vle_iff_le]
    change ‖algebraMap K L x‖₊ ≤ ‖algebraMap K L y‖₊ ↔ v x ≤ v y
    rw [← NNReal.coe_le_coe]
    change spectralNorm K L (algebraMap K L x) ≤ spectralNorm K L (algebraMap K L y) ↔ _
    rw [spectralNorm_extends, spectralNorm_extends]
    exact Valued.toNormedField.norm_le_iff
  have residueL : Finite (IsLocalRing.ResidueField (valuation L).valuationSubring) := by
    let : IsNonarchimedeanLocalField L := localL
    exact (localField_properties L).2.1
  refine ⟨r, inferInstance, extL, localL, residueL, ?_, ?_⟩
  · intro b
    exact ⟨b.equivFun.toContinuousLinearEquiv.continuous,
      b.equivFun.toContinuousLinearEquiv.symm.continuous⟩
  · intro s hs
    let w' := @valuation L _ s
    have h_cmp (a b : L) : @ValuativeRel.vle L _ s a b ↔ w' a ≤ w' b := by
      let : ValuativeRel L := s
      exact w'.vle_iff_le
    have hvw' : v.HasExtension w' := by
      constructor
      intro x y
      exact v.vle_iff_le.symm.trans
        ((@ValuativeExtension.vle_iff_vle K L _ _ _ s _ hs x y).symm.trans (h_cmp _ _))
    have hproper : w'.valuationSubring ≠ ⊤ := by
      intro he
      have hnt : ¬ w'.IsNontrivial := w'.valuationSubring_eq_top_iff.mp he
      apply hnt
      obtain ⟨x, hx, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := v)
      refine ⟨algebraMap K L x, ?_, (Valuation.HasExtension.val_map_lt_one_iff v w' x |>.2 hx1).ne⟩
      simpa using hx
    have hle : w.valuationSubring ≤ w'.valuationSubring := by
      intro x hx
      have hxnorm : spectralNorm K L x ≤ 1 := by
        change ‖x‖₊ ≤ 1 at hx
        change (↑‖x‖₊ : ℝ) ≤ 1
        exact_mod_cast hx
      have hm : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
      have hcoeff := (spectralValue_le_one_iff hm).mp hxnorm
      have hcoeff' (i : ℕ) : (minpoly K x).coeff i ∈ (algebraMap v.valuationSubring K).range := by
        refine ⟨⟨_, Valued.toNormedField.norm_le_one_iff.mp (hcoeff i)⟩, rfl⟩
      obtain ⟨p, hp⟩ := (Polynomial.mem_map_range (algebraMap v.valuationSubring K)).2 hcoeff'
      change p.map (algebraMap v.valuationSubring K) = minpoly K x at hp
      have hInt : IsIntegral v.valuationSubring x := by
        refine ⟨p, (IsFractionRing.injective v.valuationSubring K).monic_map_iff.mpr ?_, ?_⟩
        · simpa only [hp] using hm
        · change Polynomial.aeval x p = 0
          rw [Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq v.valuationSubring K L).symm, hp]
          exact minpoly.aeval K x
      have hInt' := hInt.tower_top (A := w'.valuationSubring)
      exact (Valuation.integer.integers w').mem_of_integral hInt'
    have : (Valued.v (R := L)).IsNontrivial := inferInstanceAs w.IsNontrivial
    have : CompactSpace (Valued.integer L) := by
      let : ValuativeRel L := r
      let : w.Compatible := Valuation.Compatible.ofValuation w
      let : IsNonarchimedeanLocalField L := localL
      have hc : IsCompact {x : L | valuation L x ≤ 1} :=
        IsNonarchimedeanLocalField.isCompact_closedBall L 1
      have hsets : (Valued.integer L : Set L) = {x : L | valuation L x ≤ 1} := by
        ext x
        change w x ≤ 1 ↔ valuation L x ≤ 1
        exact (w.vle_one_iff (x := x)).symm.trans ((valuation L).vle_one_iff (x := x))
      exact isCompact_iff_compactSpace.mp (hsets.symm ▸ hc)
    have : IsDiscreteValuationRing w.valuationSubring := by
      change IsDiscreteValuationRing (Valued.integer L)
      exact Valued.integer.isDiscreteValuationRing_of_compactSpace
    have heq := ValuationSubring.eq_of_le_of_ne_top w.valuationSubring hle hproper
    have he := (Valuation.isEquiv_iff_valuationSubring w w').2 heq
    apply ValuativeRel.ext
    funext a b
    exact propext ((h_cmp a b).trans he.le_iff_le.symm)

end FiniteExtensions

end LinearAlgebraicGroups.Arithmetic
