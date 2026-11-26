import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.NonexcellentDVRCompletion
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Cardinality

noncomputable section

universe u

open scoped LaurentSeries PowerSeries Polynomial RatFunc WithZero

namespace CommutativeAlgebraNotes.NonexcellentDVRCompletion

export Specs (Completion GenericFiber GenericResidueField genericResidueEquiv)

abbrev rationalEmbedding : Specs.RationalEmbeddingType.{u} := Specs.rationalEmbedding
abbrev rationalField : Specs.RationalFieldType.{u} := Specs.rationalField
abbrev generatedField : Specs.GeneratedFieldType := Specs.generatedField
abbrev restrictedValuation : Specs.RestrictedValuationType.{u} := Specs.restrictedValuation
abbrev valuationRing : Specs.ValuationRingType.{u} := Specs.valuationRing
abbrev powerSeriesInclusion : Specs.PowerSeriesInclusionType.{u} := Specs.powerSeriesInclusion
abbrev polynomialInclusion : Specs.PolynomialInclusionType.{u} := Specs.polynomialInclusion
abbrev uniformizer : Specs.UniformizerType.{u} := Specs.uniformizer
abbrev SeriesTranscendental : Specs.SeriesTranscendentalType.{u} := Specs.SeriesTranscendental

theorem rationalField_le_generatedField : Specs.RationalFieldLeGeneratedField :=
  Specs.rationalField_le_generatedField

theorem pow_mem_generatedField : Specs.GeneratedFieldContainsPower := by
  intro p hp f
  exact (show IntermediateField.adjoin (ZMod p) {((f : LaurentSeries (ZMod p)) ^ p)} ≤
    generatedField p f from le_sup_right)
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))

open Specs (maximalIdeal polynomialIdeal seriesIdeal)
open WithZero
variable {k : Type u} [Field k]
variable (F : IntermediateField k k⸨X⸩) (hF : rationalField k ≤ F)

theorem mem_intersection : Specs.MemIntersection F :=
  fun x => LaurentSeries.val_le_one_iff_eq_coe k (x : k⸨X⸩)

theorem fractionField : Specs.FractionField F :=
  inferInstanceAs (IsFractionRing (valuationRing F) F)

theorem powerSeriesInclusion_coe : Specs.PowerSeriesInclusionCoe F := by
  intro x
  change ((LaurentSeries.powerSeriesEquivSubring k).symm _ : k⸨X⸩) = _
  rw [← LaurentSeries.powerSeriesEquivSubring_coe_apply,
    RingEquiv.apply_symm_apply]
  rfl

theorem powerSeriesInclusion_injective : Function.Injective (powerSeriesInclusion F) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  rw [← powerSeriesInclusion_coe, ← powerSeriesInclusion_coe, h]

theorem polynomialInclusion_apply (g : k[X]) :
    powerSeriesInclusion F (polynomialInclusion F hF g) = (g : k⟦X⟧) := by
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [← LaurentSeries.coe_algebraMap]
  change ((powerSeriesInclusion F (polynomialInclusion F hF g) : k⟦X⟧) : k⸨X⸩) =
    ((g : k⟦X⟧) : k⸨X⸩)
  rw [powerSeriesInclusion_coe]
  exact (RatFunc.coe_coe g).symm

@[simp] theorem uniformizer_inclusion :
    powerSeriesInclusion F (uniformizer F hF) = PowerSeries.X := by
  rw [uniformizer, polynomialInclusion_apply, Polynomial.coe_X]

theorem restrictedValuation_uniformizer :
    restrictedValuation F (uniformizer F hF : F) = exp (-1 : ℤ) := by
  change Valued.v (((uniformizer F hF : valuationRing F) : F) : k⸨X⸩) = _
  rw [← powerSeriesInclusion_coe, uniformizer_inclusion]
  simpa only [pow_one, Nat.cast_one] using LaurentSeries.valuation_X_pow (K := k) 1

theorem restrictedValuation_surjective : Specs.RestrictedValuationSurjective F := by
  intro hF a
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  refine ⟨(uniformizer F hF : F) ^ (- log a), ?_⟩
  rw [map_zpow₀, restrictedValuation_uniformizer, ← exp_zsmul]
  simpa using exp_log ha

theorem discreteValuationRing : Specs.DiscreteValuationRing F := by
  intro hF
  let v := restrictedValuation F
  have hv : Function.Surjective v := restrictedValuation_surjective F hF
  have htop : v.toMonoidWithZeroHom.valueGroup = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    exact MonoidWithZeroHom.mem_valueGroup _ (hv (x : ℤᵐ⁰))
  let : IsCyclic v.toMonoidWithZeroHom.valueGroup := Subgroup.isCyclic _
  let : Nontrivial v.toMonoidWithZeroHom.valueGroup := by
    rw [htop]
    let : Nontrivial (ℤᵐ⁰ˣ) := ⟨⟨Units.mk0 (exp (-1 : ℤ)) (by simp), 1, by
      intro h
      have h' := congrArg (fun x : ℤᵐ⁰ˣ => (x : ℤᵐ⁰)) h
      have : exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by
        rw [← exp_zero, exp_lt_exp]
        decide
      exact this.ne h'⟩⟩
    exact (Subgroup.topEquiv (G := ℤᵐ⁰ˣ)).symm.injective.nontrivial
  exact Valuation.valuationSubring_isDiscreteValuationRing v

private theorem value_le_uniformizer_iff (a : ℤᵐ⁰) :
    a ≤ exp (-1 : ℤ) ↔ a < 1 := by
  by_cases ha : a = 0
  · simp [ha, zero_lt_iff]
  rw [← exp_log ha, ← exp_zero, exp_lt_exp, exp_le_exp]
  omega

theorem maximalIdeal_eq_span : Specs.Uniformizer F := by
  intro hF
  let v := restrictedValuation F
  have hv := Valuation.valuationSubring.integers v
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton, hv.dvd_iff_le,
    hv.isUnit_iff_valuation_eq_one]
  change v (x : F) ≠ 1 ↔ v (x : F) ≤ v (uniformizer F hF : F)
  rw [restrictedValuation_uniformizer, value_le_uniformizer_iff]
  exact ⟨fun h => lt_of_le_of_ne x.property h, ne_of_lt⟩


private theorem powerSeries_integers (k : Type u) [Field k] :
    (Valued.v : Valuation k⸨X⸩ ℤᵐ⁰).Integers k⟦X⟧ where
  hom_inj := HahnSeries.ofPowerSeries_injective
  map_le_one s := (LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨s, rfl⟩
  exists_of_le_one {r} := (LaurentSeries.val_le_one_iff_eq_coe k r).1

private theorem mem_seriesIdeal_pow_iff (n : ℕ) (s : k⟦X⟧) :
    s ∈ seriesIdeal k ^ n ↔ (PowerSeries.X : k⟦X⟧) ^ n ∣ s := by
  rw [seriesIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private theorem comap_seriesIdeal_pow_polynomial (n : ℕ) :
    (seriesIdeal k ^ n).comap (Polynomial.coeToPowerSeries.ringHom : k[X] →+* k⟦X⟧) =
      polynomialIdeal k ^ n := by
  ext g
  rw [Ideal.mem_comap, mem_seriesIdeal_pow_iff, polynomialIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]

private theorem comap_seriesIdeal_pow_valuation (hF : rationalField k ≤ F) (n : ℕ) :
    (seriesIdeal k ^ n).comap (powerSeriesInclusion F) = maximalIdeal F ^ n := by
  ext x
  rw [Ideal.mem_comap, mem_seriesIdeal_pow_iff, maximalIdeal_eq_span F hF,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (powerSeries_integers k).dvd_iff_le,
    (Valuation.valuationSubring.integers (restrictedValuation F)).dvd_iff_le]
  change Valued.v ((powerSeriesInclusion F x : k⟦X⟧) : k⸨X⸩) ≤
    Valued.v (((PowerSeries.X : k⟦X⟧) ^ n : k⟦X⟧) : k⸨X⸩) ↔
    Valued.v ((x : F) : k⸨X⸩) ≤
    Valued.v (((uniformizer F hF ^ n : valuationRing F) : F) : k⸨X⸩)
  rw [← powerSeriesInclusion_coe F (uniformizer F hF ^ n),
    (powerSeriesInclusion F).map_pow, uniformizer_inclusion, powerSeriesInclusion_coe]

private theorem polynomial_approximates (n : ℕ) (s : k⟦X⟧) :
    Ideal.Quotient.mk (seriesIdeal k ^ n) (s.trunc n : k⟦X⟧) =
      Ideal.Quotient.mk (seriesIdeal k ^ n) s := by
  symm
  rw [Ideal.Quotient.eq, mem_seriesIdeal_pow_iff]
  exact PowerSeries.X_pow_dvd_iff.mpr fun m hm => by
    simp [PowerSeries.coeff_coe_trunc_of_lt hm]

private def quotientEquivOfComap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (h : J.comap f = I)
    (hs : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    (R ⧸ I) ≃+* (S ⧸ J) := by
  let g := Ideal.quotientMap J f h.ge
  refine RingEquiv.ofBijective g ⟨?_, ?_⟩
  · intro x y e
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    rw [← h, Ideal.mem_comap, map_sub]
    exact Ideal.Quotient.eq.mp e
  · intro x
    obtain ⟨a, rfl⟩ := hs x
    exact ⟨Ideal.Quotient.mk I a, rfl⟩

private def seriesQuotientFromPolynomial (k : Type u) [Field k] (n : ℕ) :
    (k[X] ⧸ polynomialIdeal k ^ n) ≃+* (k⟦X⟧ ⧸ seriesIdeal k ^ n) :=
  quotientEquivOfComap Polynomial.coeToPowerSeries.ringHom _ _
    (comap_seriesIdeal_pow_polynomial n) fun x => by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨s.trunc n, polynomial_approximates n s⟩

private def seriesQuotientFromValuation (n : ℕ) :
    (valuationRing F ⧸ maximalIdeal F ^ n) ≃+* (k⟦X⟧ ⧸ seriesIdeal k ^ n) :=
  quotientEquivOfComap (powerSeriesInclusion F) _ _
    (comap_seriesIdeal_pow_valuation F hF n) fun x => by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨polynomialInclusion F hF (s.trunc n), ?_⟩
      simpa only [RingHom.comp_apply, polynomialInclusion_apply] using polynomial_approximates n s

@[simp] private theorem seriesQuotientFromValuation_mk (n : ℕ) (x : valuationRing F) :
    seriesQuotientFromValuation F hF n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (powerSeriesInclusion F x) :=
  rfl

private theorem seriesQuotientFromValuation_compatible {m n : ℕ} (hmn : m ≤ n)
    (x : valuationRing F ⧸ maximalIdeal F ^ n) :
    Ideal.Quotient.factorPow (seriesIdeal k) hmn (seriesQuotientFromValuation F hF n x) =
      seriesQuotientFromValuation F hF m (Ideal.Quotient.factorPow (maximalIdeal F) hmn x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem compatibleQuotients : Specs.CompatibleQuotients F := by
  intro hF
  let e := fun n =>
    (seriesQuotientFromPolynomial k n).trans (seriesQuotientFromValuation F hF n).symm
  have he (n : ℕ) (g : k[X]) : e n (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (polynomialInclusion F hF g) := by
    apply (seriesQuotientFromValuation F hF n).injective
    simp only [e, RingEquiv.trans_apply, RingEquiv.apply_symm_apply,
      seriesQuotientFromValuation_mk, polynomialInclusion_apply]
    rfl
  refine ⟨e, he, fun m n h x => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he]
  exact (he m g).symm


private theorem eval_factorPow {R : Type u} [CommRing R] (I : Ideal R)
    {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  have hn : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := le_of_eq (Ideal.mul_top _)
  have hm : (I ^ m • ⊤ : Ideal R) ≤ I ^ m := le_of_eq (Ideal.mul_top _)
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x hn,
    ← AdicCompletion.factor_eval_eq_evalₐ I x hm]
  change _ = Ideal.Quotient.factor hm (x.val m)
  rw [← x.property h]
  change Ideal.Quotient.factorPow I h (Ideal.Quotient.factor hn (x.val n)) =
    Ideal.Quotient.factor hm (AdicCompletion.transitionMap I R h (x.val n))
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (x.val n)
  rw [← hr]
  rfl

/-- The completion isomorphism induced by the inclusion into the power series ring. -/
def completionEquiv : Completion F ≃ₐ[valuationRing F] k⟦X⟧ := by
  let toQuot := fun n => (seriesQuotientFromValuation F hF n).toRingHom.comp
    (AdicCompletion.evalₐ (maximalIdeal F) n).toRingHom
  have toQuot_compatible {m n : ℕ} (h : m ≤ n) :
      (Ideal.Quotient.factorPow (seriesIdeal k) h).comp (toQuot n) = toQuot m := by
    ext x
    change Ideal.Quotient.factorPow (seriesIdeal k) h
      (seriesQuotientFromValuation F hF n (AdicCompletion.evalₐ (maximalIdeal F) n x)) =
      seriesQuotientFromValuation F hF m (AdicCompletion.evalₐ (maximalIdeal F) m x)
    rw [seriesQuotientFromValuation_compatible, eval_factorPow]
  let f := IsAdicComplete.liftRingHom (seriesIdeal k) toQuot toQuot_compatible
  have hf (n : ℕ) (x : Completion F) :
      Ideal.Quotient.mk (seriesIdeal k ^ n) (f x) =
        seriesQuotientFromValuation F hF n (AdicCompletion.evalₐ (maximalIdeal F) n x) :=
    IsAdicComplete.mk_liftRingHom _ _ _ n x
  let fromQuot := fun n => (seriesQuotientFromValuation F hF n).symm.toRingHom.comp
    (Ideal.Quotient.mk (seriesIdeal k ^ n))
  have fromQuot_compatible {m n : ℕ} (h : m ≤ n) :
      (Ideal.Quotient.factorPow (maximalIdeal F) h).comp (fromQuot n) = fromQuot m := by
    ext s
    apply (seriesQuotientFromValuation F hF m).injective
    change seriesQuotientFromValuation F hF m
      (Ideal.Quotient.factorPow (maximalIdeal F) h
        ((seriesQuotientFromValuation F hF n).symm (Ideal.Quotient.mk _ s))) =
      seriesQuotientFromValuation F hF m
        ((seriesQuotientFromValuation F hF m).symm (Ideal.Quotient.mk _ s))
    rw [← seriesQuotientFromValuation_compatible, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]
    rfl
  refine { RingEquiv.ofBijective f ⟨?_, ?_⟩ with commutes' := ?_ }
  · intro x y h
    apply AdicCompletion.ext_evalₐ
    intro n
    apply (seriesQuotientFromValuation F hF n).injective
    rw [← hf, ← hf, h]
  · intro s
    refine ⟨AdicCompletion.liftRingHom (maximalIdeal F) fromQuot fromQuot_compatible s, ?_⟩
    have he := IsHausdorff.funext' (seriesIdeal k)
      (f := fun s => f (AdicCompletion.liftRingHom (maximalIdeal F) fromQuot
        fromQuot_compatible s)) (g := id) (fun n s => by
        rw [hf, AdicCompletion.evalₐ_liftRingHom]
        exact (seriesQuotientFromValuation F hF n).apply_symm_apply _)
    exact congrFun he s
  · intro x
    have he := IsHausdorff.funext' (seriesIdeal k)
      (f := fun x : valuationRing F => f (algebraMap (valuationRing F) (Completion F) x))
      (g := powerSeriesInclusion F) (fun n x => by
        rw [hf]
        change seriesQuotientFromValuation F hF n
          (AdicCompletion.evalₐ (maximalIdeal F) n (AdicCompletion.of _ _ x)) = _
        rw [AdicCompletion.evalₐ_of, seriesQuotientFromValuation_mk])
    exact congrFun he x

theorem completionIdentification : Specs.CompletionIdentification F :=
  fun hF => ⟨completionEquiv F hF⟩

private theorem powerSeries_uncountable (k : Type u) [Field k] : Uncountable k⟦X⟧ := by
  classical
  apply uncountable_iff_forall_not_surjective.mpr
  intro s hs
  obtain ⟨n, hn⟩ := hs (PowerSeries.mk fun m => if PowerSeries.coeff m (s m) = 0 then 1 else 0)
  have h := congrArg (PowerSeries.coeff n) hn
  rw [PowerSeries.coeff_mk] at h
  split at h
  · rename_i he
    exact zero_ne_one (he.symm.trans h)
  · rename_i he
    exact he h

private theorem rationalField_countable (k : Type u) [Field k] [Countable k] :
    Countable (rationalField k) := by
  have hk : Cardinal.mk k ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  let : Countable (RatFunc k) := Cardinal.mk_le_aleph0_iff.mp <| by
    rw [IsFractionRing.cardinalMk k[X] (RatFunc k)]
    exact (Polynomial.cardinalMk_le_max (R := k)).trans (max_le hk le_rfl)
  exact (rationalEmbedding k).equivFieldRange.surjective.countable

theorem existsTranscendentalSeries : Specs.ExistsTranscendentalSeries := by
  intro p hp
  let k := ZMod p
  let : Uncountable k⟦X⟧ := powerSeries_uncountable k
  let : Countable (rationalField k) := rationalField_countable k
  let A := algebraicClosure (rationalField k) (LaurentSeries k)
  let : Countable A := Cardinal.mk_le_aleph0_iff.mp <|
    (Algebra.IsAlgebraic.cardinalMk_le_max (rationalField k) A).trans
      (max_le (Cardinal.mk_le_aleph0_iff.mpr inferInstance) le_rfl)
  by_contra! h
  have hA (s : k⟦X⟧) : (s : k⸨X⸩) ∈ A :=
    mem_algebraicClosure_iff.mpr (not_not.mp (h s))
  let f (s : k⟦X⟧) : A := ⟨s, hA s⟩
  exact not_injective_uncountable_countable f
    (fun s t e => HahnSeries.ofPowerSeries_injective (congrArg Subtype.val e))


open scoped TensorProduct

theorem fractionFieldByInverting : Specs.FractionFieldByInverting F := by
  intro hF
  have ht : algebraMap (valuationRing F) F (uniformizer F hF) ≠ 0 := by
    intro h
    have hv := restrictedValuation_uniformizer F hF
    change restrictedValuation F (algebraMap (valuationRing F) F (uniformizer F hF)) = _ at hv
    rw [h, map_zero] at hv
    exact (exp_ne_zero hv.symm).elim
  have hX : ((uniformizer F hF : F) : k⸨X⸩) = algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X := by
    rw [← powerSeriesInclusion_coe, uniformizer_inclusion]
    rfl
  refine IsLocalization.Away.mk _ (isUnit_iff_ne_zero.mpr ht) (fun z => ?_) (fun a b h => ?_)
  · obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj (PowerSeries.X : k⟦X⟧) (z : k⸨X⸩)
    let a : F := z * (uniformizer F hF : F) ^ n
    have ha : (a : k⸨X⸩) = (s : k⸨X⸩) := by
      change F.val (z * (uniformizer F hF : F) ^ n) = _
      rw [map_mul, map_pow]
      exact (congrArg (fun y => (z : k⸨X⸩) * y ^ n) hX).trans hs
    exact ⟨n, ⟨a, (mem_intersection F a).mpr ⟨s, ha.symm⟩⟩, rfl⟩
  · exact ⟨0, by simpa using IsFractionRing.injective (valuationRing F) F h⟩

private theorem genericResidueByInverting (hF : rationalField k ≤ F) :
    IsLocalization.Away (uniformizer F hF) (GenericResidueField F) := by
  let : IsLocalization.Away (uniformizer F hF) F := fractionFieldByInverting F hF
  exact IsLocalization.isLocalization_of_algEquiv _ (genericResidueEquiv F).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem genericFiberByInverting : Specs.GenericFiberByInverting F := by
  intro hF
  let : IsLocalization.Away (uniformizer F hF) (GenericResidueField F) :=
    genericResidueByInverting F hF
  exact IsLocalization.Away.tensorRight _ _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem genericFiberIdentification : Specs.GenericFiberIdentification F := by
  intro hF
  let V := valuationRing F
  let e := completionEquiv F hF
  let t := algebraMap V (Completion F) (uniformizer F hF)
  let : Algebra (Completion F) k⸨X⸩ :=
    ((algebraMap k⟦X⟧ k⸨X⸩).comp e.toRingEquiv.toRingHom).toAlgebra
  let : IsLocalization.Away t k⸨X⸩ := by
    refine IsLocalization.of_ringEquiv_left e.toRingEquiv (M₂ := Submonoid.powers t)
      (M₁ := Submonoid.powers (PowerSeries.X : k⟦X⟧)) ?_ (fun _ => rfl)
    rw [Submonoid.map_powers]
    congr 1
    change e t = PowerSeries.X
    rw [show e t = algebraMap V k⟦X⟧ (uniformizer F hF) from e.commutes _]
    exact uniformizer_inclusion F hF
  let : IsLocalization.Away t (GenericFiber F) := genericFiberByInverting F hF
  let g := IsLocalization.algEquiv (Submonoid.powers t) (GenericFiber F) (LaurentSeries k)
  have hg (s : Completion F) : g (1 ⊗ₜ[V] s) = (e s : k⸨X⸩) := g.commutes s
  let : IsLocalization.Away (uniformizer F hF) (GenericResidueField F) :=
    genericResidueByInverting F hF
  have hscalar :
      g.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeft : GenericResidueField F →ₐ[V] GenericFiber F).toRingHom =
      F.val.toRingHom.comp (genericResidueEquiv F).toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (uniformizer F hF))
    apply RingHom.ext
    intro x
    change g (algebraMap V (GenericResidueField F) x ⊗ₜ[V] 1) =
      ((genericResidueEquiv F (algebraMap V (GenericResidueField F) x) : F) : k⸨X⸩)
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, hg, e.commutes,
      (genericResidueEquiv F).commutes]
    exact powerSeriesInclusion_coe F x
  let g' : GenericFiber F ≃ₐ[GenericResidueField F] k⸨X⸩ :=
    { g.toRingEquiv with commutes' := fun x => RingHom.congr_fun hscalar x }
  refine ⟨e, g', fun a s => ?_⟩
  change g (a ⊗ₜ[V] s) = _
  have hdecompose : a ⊗ₜ[V] s = (a ⊗ₜ[V] (1 : Completion F)) * (1 ⊗ₜ[V] s) := by
    simp
  rw [hdecompose, map_mul, hg]
  exact congrArg (· * (e s : k⸨X⸩)) (RingHom.congr_fun hscalar a)

/-- The valuation ring, completion, and generic fibre for the fields in Example 5.23. -/
theorem construction : Specs.Construction := by
  intro p hp f
  let F := generatedField p f
  have hF : rationalField (ZMod p) ≤ F := rationalField_le_generatedField p f
  exact ⟨mem_intersection F, fractionField F, restrictedValuation_surjective F hF,
    discreteValuationRing F hF, maximalIdeal_eq_span F hF, compatibleQuotients F,
    completionIdentification F, fractionFieldByInverting F, genericFiberByInverting F,
    genericFiberIdentification F⟩

end CommutativeAlgebraNotes.NonexcellentDVRCompletion
