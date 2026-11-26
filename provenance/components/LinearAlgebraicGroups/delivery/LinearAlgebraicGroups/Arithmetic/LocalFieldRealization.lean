import Specs.LinearAlgebraicGroups.Arithmetic.LocalFieldRealization
import LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import LinearAlgebraicGroups.Arithmetic.LocalPolynomialApproximation
import LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Batteries.Tactic.OpenPrivate

open Filter IsDedekindDomain ValuativeRel
open IsDedekindDomain.HeightOneSpectrum hiding valuation
open scoped RatFunc LaurentSeries WithZero Valued Topology NumberField

noncomputable section

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.LocalFieldRealization

open private exists_adic_of_contains from LinearAlgebraicGroups.Arithmetic.GlobalPlaces

/-- A field isomorphism preserving the valuation comparison is continuous for the
associated valuative topologies. -/
theorem continuous_of_valuationComparison
    {A B : Type*} [Field A] [Field B] [ValuativeRel A] [ValuativeRel B]
    [TopologicalSpace A] [TopologicalSpace B] [IsValuativeTopology A] [IsValuativeTopology B]
    (e : A ≃+* B) (he : ∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) : Continuous e := by
  apply continuous_of_continuousAt_zero e.toAddMonoidHom
  change Tendsto e (nhds 0) (nhds (e 0))
  rw [map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' A).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' B)).2 ?_
  intro b hb
  obtain ⟨y, hy⟩ := valuation_surjective (K := B) b
  rw [← hy] at hb ⊢
  refine ⟨valuation A (e.symm y), ?_, ?_⟩
  · exact (Valuation.ne_zero_iff _).2 (by
      intro h
      have hy0 : y = 0 := by simpa using congrArg e h
      simp [hy0] at hb)
  · intro x hx
    change valuation B (e x) < valuation B y
    change valuation A x < valuation A (e.symm y) at hx
    have hh := he (e.symm y) x
    rw [e.apply_symm_apply, (valuation B).vle_iff_le, (valuation A).vle_iff_le] at hh
    exact lt_of_not_ge fun h => hx.not_ge (hh.mp h)

/-- Preservation of the valuation rings is equivalent to preservation of the
valuation ordering by a field embedding. -/
theorem valuationComparison_of_integerMembership
    {A B : Type*} [Field A] [Field B] [ValuativeRel A] [ValuativeRel B]
    (f : A →+* B)
    (hf : ∀ x, x ∈ (valuation A).valuationSubring ↔ f x ∈ (valuation B).valuationSubring) :
    ∀ x y, f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  have h : ((valuation B).comap f).IsEquiv (valuation A) :=
    Valuation.isEquiv_iff_val_le_one.2 (fun {x} => (hf x).symm)
  intro x y
  rw [(valuation B).vle_iff_le, (valuation A).vle_iff_le]
  exact h.le_iff_le

/-- A valued ring embedding into a local field induces the additive uniformity
when the valuation on its source is nontrivial. -/
theorem isUniformInducing_of_valuationComparison
    {A B : Type*} [Field A] [Field B] [ValuativeRel A] [ValuativeRel B]
    [UniformSpace A] [UniformSpace B] [IsUniformAddGroup A] [IsUniformAddGroup B]
    [IsValuativeTopology A] [IsValuativeTopology B] [ValuativeRel.IsNontrivial A]
    [MulArchimedean (ValueGroupWithZero B)] (f : A →+* B)
    (hf : ∀ x y, f x ≤ᵥ f y ↔ x ≤ᵥ y) : IsUniformInducing f := by
  have hlt (x y : A) : valuation B (f x) < valuation B (f y) ↔
      valuation A x < valuation A y := by
    simpa only [(valuation B).vle_iff_le, (valuation A).vle_iff_le, not_le] using
      not_congr (hf y x)
  let bA := IsValuativeTopology.hasBasis_nhds_zero' A
  let bB := (IsValuativeTopology.hasBasis_nhds_zero' B).comap f
  have hnhds : 𝓝 (0 : A) = Filter.comap f (𝓝 (0 : B)) := by
    apply le_antisymm
    · apply (bA.le_basis_iff bB).2
      intro r hr
      obtain ⟨a, ha, hav⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation A)
      have hfa : valuation B (f a) < 1 := by simpa using (hlt a 1).2 hav
      have hpos : 0 < valuation B (f a) :=
        pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).2 ((map_ne_zero f).mpr ha))
      let q := (valuation B (f a))⁻¹
      have hq : 1 < q := (one_lt_inv₀ hpos).2 hfa
      obtain ⟨m, hm⟩ := MulArchimedean.arch r⁻¹ hq
      have hmq : r⁻¹ < q ^ (m + 1) := hm.trans_lt (by
        simpa only [mul_one, pow_succ] using
          mul_lt_mul_of_pos_left hq (pow_pos (zero_lt_one.trans hq) m))
      have hn : valuation B (f a) ^ (m + 1) < r :=
        (inv_lt_inv₀ (pos_iff_ne_zero.mpr hr) (pow_pos hpos _)).1 (by
          simpa only [q, inv_pow] using hmq)
      let n := m + 1
      refine ⟨valuation A (a ^ n), (Valuation.ne_zero_iff _).2 (pow_ne_zero _ ha), ?_⟩
      intro x hx
      change valuation B (f x) < r
      have h := (hlt x (a ^ n)).2 hx
      exact h.trans (by simpa only [map_pow] using hn)
    · apply (bB.le_basis_iff bA).2
      intro r hr
      obtain ⟨a, ha⟩ := valuation_surjective (K := A) r
      subst r
      refine ⟨valuation B (f a), (Valuation.ne_zero_iff _).2 (by simpa using hr), ?_⟩
      exact fun x hx => (hlt x a).1 hx
  constructor
  rw [uniformity_eq_comap_nhds_zero A, uniformity_eq_comap_nhds_zero B,
    hnhds, Filter.comap_comap, Filter.comap_comap]
  congr 1
  funext z
  exact (map_sub f z.2 z.1).symm

set_option maxHeartbeats 1000000 in
theorem denseNumberFieldCompletion : DenseNumberFieldCompletion.{u, v} := by
  intro F _ _ _ _ K _ _ i hi
  let O := (valuation F).valuationSubring
  let V := O.comap i
  have hproper : V ≠ ⊤ := by
    have ho : IsClosed (O : Set F) := (valuation F).isClosed_valuationSubring
    intro h
    have hsub : Set.range i ⊆ O := by
      rintro _ ⟨x, rfl⟩
      change x ∈ V
      rw [h]
      trivial
    have ht : (Set.univ : Set F) ⊆ O := by
      simpa [hi.closure_range] using closure_minimal hsub ho
    have ht' : O = ⊤ := top_unique fun x _ => ht (Set.mem_univ x)
    exact ((valuation F).valuationSubring_eq_top_iff.mp ht') inferInstance
  have hint (x : 𝓞 K) : algebraMap (𝓞 K) K x ∈ V := by
    let : Algebra ℤ O := Ring.toIntAlgebra O
    have hO : IsIntegrallyClosed O := (Valuation.integer.integers (valuation F)).isIntegrallyClosed
    have hx : IsIntegral ℤ (algebraMap (𝓞 K) K x) := x.property
    have hxi : IsIntegral ℤ (i (algebraMap (𝓞 K) K x)) := hx.map i.toIntAlgHom
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hxi.tower_top (A := O))
    change i (algebraMap (𝓞 K) K x) ∈ O
    rw [← hy]
    exact y.property
  obtain ⟨w, hw⟩ := exists_adic_of_contains (R := 𝓞 K) ⟨V, hproper⟩ hint
  have hv : ((valuation F).comap i).IsEquiv (w.valuation K) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 hw.symm
  let A := WithVal (w.valuation K)
  let f : A →+* F := i.comp (WithVal.equiv (w.valuation K)).toRingHom
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have : ValuativeRel.IsNontrivial A := by
    apply (ValuativeRel.isNontrivial_iff_isNontrivial (WithVal.valuation (w.valuation K))).2
    apply (Valuation.isNontrivial_iff_exists_lt_one _).mpr
    obtain ⟨x, hx, hxv⟩ := Valuation.IsNontrivial.exists_lt_one (v := w.valuation K)
    exact ⟨WithVal.toVal _ x, by simpa using hx, hxv⟩
  have hf : IsUniformInducing f := by
    apply isUniformInducing_of_valuationComparison
    intro x y
    rw [(valuation F).vle_iff_le, (WithVal.valuation (w.valuation K)).vle_iff_le]
    exact hv.le_iff_le
  let j : (w.valuation K).Completion →+* F :=
    UniformSpace.Completion.extensionHom f hf.uniformContinuous.continuous
  have hj : IsUniformInducing j := UniformSpace.Completion.isUniformInducing_extension hf
  have hjdense : DenseRange j := by
    apply hi.mono
    rintro _ ⟨x, rfl⟩
    use (WithVal.toVal (w.valuation K) x : A)
    exact UniformSpace.Completion.extensionHom_coe _ _ _
  have hjbij : Function.Bijective j :=
    ⟨j.injective, by
      rw [← Set.range_eq_univ, ← hj.isComplete_range.isClosed.closure_eq, hjdense.closure_range]⟩
  let e := (adicCompletion.equiv K w).trans (RingEquiv.ofBijective j hjbij)
  have hmj (x : (w.valuation K).Completion) : Valued.v x ≤ (1 : ℤᵐ⁰) ↔ j x ∈ O := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact (Homeomorph.refl _).isClosed_setOfPred_iff
        (Valued.isClopen_valuationSubring _) ((valuation F).isClopen_valuationSubring.preimage hj.uniformContinuous.continuous)
    | ih x =>
      rw [Valued.valuedCompletion_apply, UniformSpace.Completion.extensionHom_coe]
      exact hv.le_one_iff_le_one.symm
  let D : GlobalFieldData.{v, u} K := .number inferInstance
  have hm (x : D.FiniteCompletion w) : x ∈ D.integers w ↔ e x ∈ O := by
    change Valued.v x ≤ 1 ↔ j (adicCompletion.toCompletion x) ∈ O
    rw [← adicCompletion.valued_toCompletion_apply]
    exact hmj _
  have hrel : ∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y :=
    valuationComparison_of_integerMembership e.toRingHom
      (fun x => by rw [← D.integers_eq_valuationSubring]; exact hm x)
  have hinv (x y : F) : e.symm x ≤ᵥ e.symm y ↔ x ≤ᵥ y :=
    (by simpa using hrel (e.symm x) (e.symm y) :
      x ≤ᵥ y ↔ e.symm x ≤ᵥ e.symm y).symm
  refine ⟨w, e, continuous_of_valuationComparison e hrel,
    continuous_of_valuationComparison e.symm hinv, hrel, hm, ?_⟩
  intro x
  change j (↑(WithVal.toVal (w.valuation K) x) : (w.valuation K).Completion) = i x
  exact UniformSpace.Completion.extensionHom_coe _ _ _

private def rationalParameter (k : Type*) [Field k] : SeparatingParameter k k⟮X⟯ where
  element := RatFunc.X
  transcendental := RatFunc.transcendental_X
  finite := by
    let e : (⊤ : IntermediateField k k⟮X⟯) ≃ₐ[k] k⟮X⟯ := IntermediateField.topEquiv
    let i : IntermediateField.adjoin k ({RatFunc.X} : Set k⟮X⟯) ≃ₐ[k] k⟮X⟯ :=
      (IntermediateField.equivOfEq RatFunc.adjoin_X).trans e
    exact Module.Finite.of_equiv_equiv i.symm.toRingEquiv (RingEquiv.refl _) (by
      ext x
      exact i.apply_symm_apply x)
  separable := by
    let e : (⊤ : IntermediateField k k⟮X⟯) ≃ₐ[k] k⟮X⟯ := IntermediateField.topEquiv
    let i : IntermediateField.adjoin k ({RatFunc.X} : Set k⟮X⟯) ≃ₐ[k] k⟮X⟯ :=
      (IntermediateField.equivOfEq RatFunc.adjoin_X).trans e
    exact Algebra.IsSeparable.of_equiv_equiv i.symm.toRingEquiv (RingEquiv.refl _) (by
      ext x
      exact i.apply_symm_apply x)

private def rationalXPlace (k : Type*) [Field k] : FunctionPlace k⟮X⟯ :=
  ⟨(RatFunc.polynomialValuationX k).valuationSubring, fun h =>
    ((RatFunc.polynomialValuationX k).valuationSubring_eq_top_iff.mp h) inferInstance⟩

set_option maxHeartbeats 1200000 in
theorem equalCharacteristic : EqualCharacteristic.{u} := by
  intro F _ _ _ _ p _ _
  let k := IsLocalRing.ResidueField (valuation F).valuationSubring
  let : Finite k :=
      IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation F
  let D : GlobalFieldData.{u, u} k⟮X⟯ := .function k (rationalParameter k)
  let w := rationalXPlace k
  have hw : w.1.valuation.IsEquiv (RatFunc.polynomialValuationX k) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).2 w.1.valuationSubring_valuation
  let ec : w.Completion ≃+* LaurentSeries.RatFuncAdicCompl k :=
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr _ _ (RingEquiv.refl _))
      hw.uniformContinuous_congr.continuous hw.symm.uniformContinuous_congr.continuous).trans
      (adicCompletion.equiv _ _).symm
  have hec (x : w.Completion) :
      Valued.v (ec x) ≤ (1 : ℤᵐ⁰) ↔ x ∈ w.integers := by
    change Valued.v (ec x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [← adicCompletion.valued_toCompletion_apply]
    exact hw.valuedCompletion_le_one_iff.symm
  obtain ⟨_, _, _, eL, _, _, _, hv⟩ := FunctionFieldForms.laurent_presentation F p
  change ∀ a : k⸨X⸩, LocalDivisionAlgebras.baseValue F (eL a) = Valued.v a at hv
  let e : D.FiniteCompletion w ≃+* F :=
    ec.trans ((LaurentSeries.ratfuncAdicComplRingEquiv k).trans eL)
  have hm (x : D.FiniteCompletion w) :
      x ∈ D.integers w ↔ e x ∈ (valuation F).valuationSubring := by
    change x ∈ w.integers ↔ valuation F (e x) ≤ 1
    let E := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
    rw [← E.strictMono.le_iff_le, map_one E]
    change x ∈ w.integers ↔ LocalDivisionAlgebras.baseValue F (e x) ≤ 1
    rw [hec x |>.symm]
    change Valued.v (ec x) ≤ 1 ↔
      LocalDivisionAlgebras.baseValue F (eL (LaurentSeries.ratfuncAdicComplRingEquiv k (ec x))) ≤ 1
    rw [hv, ← LaurentSeries.valuation_compare]
    simp only [RingEquiv.symm_apply_apply]
  have hrel : ∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y :=
    valuationComparison_of_integerMembership e.toRingHom
      (fun x => by rw [← D.integers_eq_valuationSubring]; exact hm x)
  let : IsNonarchimedeanLocalField (D.FiniteCompletion w) :=
    FunctionPlace.completion_isLocalField (rationalParameter k) w
  have hinv (x y : F) : e.symm x ≤ᵥ e.symm y ↔ x ≤ᵥ y :=
    (by simpa using hrel (e.symm x) (e.symm y) :
      x ≤ᵥ y ↔ e.symm x ≤ᵥ e.symm y).symm
  exact ⟨rationalParameter k, w, rfl, rfl,
    e, continuous_of_valuationComparison e hrel, continuous_of_valuationComparison e.symm hinv,
    hrel, hm⟩

set_option maxHeartbeats 1000000 in
theorem padicExtension : PadicExtension.{u} := by
  intro F _ _ _ _ _
  let O := (valuation F).valuationSubring
  let k := IsLocalRing.ResidueField O
  have : Finite k :=
    IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation F
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · have : Finite ℕ := Finite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
    exact (not_finite ℕ).elim
  refine ⟨p, hp, hchar, ?_⟩
  have hdiv (n : ℤ) : valuation F (n : F) < 1 ↔ (p : ℤ) ∣ n := by
    rw [← map_intCast O.subtype n]
    change valuation F ((n : O) : F) < 1 ↔ _
    rw [← Valuation.mem_maximalIdeal_iff F (valuation F),
      ← IsLocalRing.residue_eq_zero_iff, map_intCast, CharP.intCast_eq_zero_iff k p]
  have hint (n : ℤ) : valuation F (n : F) ≤ 1 := by
    rw [← map_intCast O.subtype n]
    exact (n : O).property
  have hle (x : ℚ) : valuation F (x : F) ≤ 1 ↔ Rat.padicValuation p x ≤ 1 := by
    rw [Rat.padicValuation_le_one_iff]
    have hden : (x.den : F) ≠ 0 := Nat.cast_ne_zero.mpr x.den_ne_zero
    nth_rw 1 [← x.num_div_den, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, map_div₀,
      div_le_one₀ (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).2 hden))]
    have hd : valuation F (x.den : F) ≤ 1 := by simpa using hint x.den
    by_cases h : p ∣ x.den
    · have hdlt : valuation F (x.den : F) < 1 := by
        simpa using (hdiv x.den).2 (Int.natCast_dvd_natCast.mpr h)
      have hn : ¬ (p : ℤ) ∣ x.num := by
        intro hdvd
        have hn' : p ∣ x.num.natAbs := Int.natCast_dvd.mp hdvd
        exact Nat.not_coprime_of_dvd_of_dvd hp.out.one_lt h hn' x.reduced.symm
      have hn' : valuation F (x.num : F) = 1 :=
        le_antisymm (hint _) (le_of_not_gt (fun ht => hn ((hdiv _).1 ht)))
      simp [hn', hdlt.not_ge, h]
    · have hd' : valuation F (x.den : F) = 1 :=
        le_antisymm hd (le_of_not_gt (fun ht => h (Int.natCast_dvd_natCast.mp
          ((hdiv x.den).1 (by simpa using ht)))))
      simp [hd', hint, h]
  have hv : ((valuation F).comap (Rat.castHom F)).IsEquiv (Rat.padicValuation p) :=
    Valuation.isEquiv_iff_val_le_one.2 (fun {x} => hle x)
  let A := WithVal (Rat.padicValuation p)
  let i : A →+* F := (Rat.castHom F).comp (WithVal.equiv _).toRingHom
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have : ValuativeRel.IsNontrivial A := by
    apply (ValuativeRel.isNontrivial_iff_isNontrivial (WithVal.valuation (Rat.padicValuation p))).2
    apply (Valuation.isNontrivial_iff_exists_lt_one _).mpr
    refine ⟨WithVal.toVal _ (p : ℚ), by simpa using (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : ℚ) ≠ 0), ?_⟩
    change Rat.padicValuation p (p : ℚ) < 1
    apply hv.lt_one_iff_lt_one.mp
    change valuation F (((p : ℚ) : F)) < 1
    simpa only [Int.cast_natCast, Rat.cast_natCast] using (hdiv p).2 dvd_rfl
  have hi : IsUniformInducing i := by
    apply isUniformInducing_of_valuationComparison
    intro x y
    rw [(valuation F).vle_iff_le, (WithVal.valuation (Rat.padicValuation p)).vle_iff_le]
    exact hv.le_iff_le
  let j : (Rat.padicValuation p).Completion →+* F :=
    UniformSpace.Completion.extensionHom i hi.uniformContinuous.continuous
  have hj : Continuous j := UniformSpace.Completion.continuous_extension
  have hmj (x : (Rat.padicValuation p).Completion) :
      Valued.v x ≤ (1 : ℤᵐ⁰) ↔ valuation F (j x) ≤ 1 := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact (Homeomorph.refl _).isClosed_setOfPred_iff
        (Valued.isClopen_valuationSubring _) ((valuation F).isClopen_valuationSubring.preimage hj)
    | ih x =>
      rw [Valued.valuedCompletion_apply, UniformSpace.Completion.extensionHom_coe]
      exact hv.le_one_iff_le_one.symm
  let f : ℚ_[p] →+* F := j.comp (Padic.withValRingEquiv (p := p)).symm.toRingHom
  have hf : Continuous f := hj.comp Padic.withValUniformEquiv.symm.continuous
  refine ⟨f, hf, ?_, ?_⟩
  · have hmf (x : ℚ_[p]) : valuation F (f x) ≤ 1 ↔ valuation ℚ_[p] x ≤ 1 := by
      change valuation F (j (Padic.withValRingEquiv.symm x)) ≤ 1 ↔ _
      rw [← hmj, ← Padic.withValUniformEquiv_norm_le_one_iff]
      change ‖Padic.withValRingEquiv (Padic.withValRingEquiv.symm x)‖ ≤ 1 ↔ _
      rw [RingEquiv.apply_symm_apply, (ValuativeRel.isEquiv (valuation ℚ_[p]) Padic.mulValuation).le_one_iff_le_one]
      simpa only [not_lt, norm_one, map_one] using
        not_congr (Padic.norm_lt_norm_iff_mulValuation_lt (x := 1) (y := x))
    have heq : ((valuation F).comap f).IsEquiv (valuation ℚ_[p]) :=
      Valuation.isEquiv_iff_val_le_one.2 (fun {x} => hmf x)
    intro x y
    rw [(valuation F).vle_iff_le, (valuation ℚ_[p]).vle_iff_le]
    exact heq.le_iff_le
  · let : Algebra ℚ_[p] F := f.toAlgebra
    have : ContinuousSMul ℚ_[p] F := continuousSMul_of_algebraMap _ _ hf
    exact ⟨this, FiniteDimensional.of_locallyCompactSpace ℚ_[p]⟩

/-- Every nonarchimedean local field is a valued topological completion
of a global field at a finite place. -/
theorem fieldRealization : Statement.{u} := by
  intro F _ _ _ _
  rcases CharP.exists' F with hzero | ⟨p, hp, hchar⟩
  · obtain ⟨p, hp, _, f, _, _, hsmul, hfinite⟩ := padicExtension F
    let : Algebra ℚ_[p] F := f.toAlgebra
    have : ContinuousSMul ℚ_[p] F := hsmul
    have : FiniteDimensional ℚ_[p] F := hfinite
    obtain ⟨K, hK, hNumber, i, hi⟩ := LocalPolynomialApproximation.exists_dense_numberField p F
    obtain ⟨w, e, hf, hinv, hv, hO, _⟩ := denseNumberFieldCompletion F K i hi
    exact ⟨K, hK, .number hNumber, w, e, hf, hinv, hv, hO⟩
  · let k := IsLocalRing.ResidueField (valuation F).valuationSubring
    have : Finite k :=
      IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation F
    obtain ⟨t, w, _, _, h⟩ := equalCharacteristic F p
    exact ⟨k⟮X⟯, inferInstance, .function k t, w, h⟩

section Transport

open LocalAlgebraicTransport LocalQuotientTransport

private theorem quotientTransportAlong {A B : Type u} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B]
    (f : A ≃ₜ* B) : QuotientTransportAlong.{u, w} f := by
  refine ⟨normal_closure_transport f, group_convergence.{u, u, w} f,
    rescaling_convergence.{u, u, w} f, ?_⟩
  intro H
  obtain ⟨hmem, hclosed, hdiscrete⟩ := subgroup_transport f H
  obtain ⟨q, hq, hequiv⟩ := quotient_transport f H
  refine ⟨hmem, hclosed, hdiscrete, q, hq, hequiv, quotient_convergence.{u, u, w} f q hequiv, ?_⟩
  intro μ hμ _ hμne
  obtain ⟨hνfinite, hνne, hν, hmap⟩ := measure_transport f q hequiv μ hμ hμne
  exact ⟨hνfinite, hνne, hν, hmap, representation_transport.{u, u, w} f q hequiv μ hμ hν⟩

private theorem markedGroupTransportAlong {F E : Type u} [Field F] [Field E]
    [ValuativeRel F] [ValuativeRel E] (e : F ≃+* E)
    (he : ∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) : MarkedGroupTransportAlong e := by
  let := scalarStructure e
  refine ⟨uniformizerTransport e he, groupSchemeTransport e, ?_, ?_,
    cocharacterMorphismTransport e, ?_⟩
  · intro X Y f p
    exact pointNaturality e f p
  · intro G P
    exact ⟨parabolicTransport e G P, radicalTransport e G P, rationalSubgroupTransport e P⟩
  · intro G A x
    obtain ⟨param, hparam, hnatural, hadd⟩ := rootMorphismTransport e x
    refine ⟨param, hparam, hnatural, hadd, ?_⟩
    intro a
    exact (rootParameterTransport e x _ a).1 (hparam _ _).2

private theorem matrixModelTopology (F : Type u) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [ContinuousInv₀ F] : MatrixModelTopology F := by
  intro X n _ _ c d _ hgen hdet hinv
  exact matrixTopology X c d hgen hdet hinv

open CliffordAlgebra in
private theorem evenProductAction_of_evenCliffordAction {S V : Type u} [CommRing S]
    [AddCommGroup V] [Module S V] {Q : QuadraticForm S V} {σ : S ≃+* S}
    {s : V → V} {c : Sˣ} {a : even Q ≃+* even Q} (ha : IsEvenCliffordAction Q σ s c a) :
    IsEvenProductAction Q s c a := by
  intro pairs
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, map_mul, ha.2, ih]
    let k : S := ↑c⁻¹
    let x := (even.ι Q).bilin (s p.1) (s p.2)
    let y := (pairs.map (fun p ↦ (even.ι Q).bilin (s p.1) (s p.2))).prod
    let f := algebraMap S (even Q)
    change (f k * x) * (f (k ^ pairs.length) * y) = f (k ^ (pairs.length + 1)) * (x * y)
    rw [pow_succ', map_mul f, mul_assoc (f k), ← mul_assoc x, ← Algebra.commutes _ x]
    simp only [f, mul_assoc]

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem quaternionicSpinTransportAlong {F E : Type u} [Field F] [Field E]
    (e : F ≃+* E) : QuaternionicSpinTransportAlong e := by
  intro B L n m J _ _ _ _ _ _ _ _ G I π D
  let := scalarStructure e
  let C (R : TestAlgebra E) : SpinChartComparisonAlong e D R :=
    Classical.choose (quaternionicSpinCoverTransport e π D R)
  refine ⟨C, ?_⟩
  constructor
  · intro R
    exact Classical.choose_spec (quaternionicSpinCoverTransport e π D R)
  · intro R
    let D₀ := D.chart ((restrictTestAlgebra F E).obj R)
    let D' := (C R).chart
    obtain ⟨_, hmatrix, hrange, hfixed⟩ := quaternionicSpinDescentAlgebraTransport (C R)
    exact ⟨fun a ↦ ⟨evenProductAction_of_evenCliffordAction (D₀.evenAction_formula a),
      evenProductAction_of_evenCliffordAction (D'.evenAction_formula a)⟩, hmatrix, hrange, hfixed⟩
  · intro R a σ
    exact quaternionicSpinGaloisActionTransport e π D R (C R) a σ
  · intro R S a
    exact quaternionicSpinCoverNaturality e π D a (C R) (C S)
  · obtain ⟨hb, ht, hd, _, _, hG, hI⟩ :=
      quaternionicSpinRationalTransport e π D (C (CommAlgCat.of E E))
    exact ⟨hb, ht, hd, hG, hI⟩
  · intro O incl V
    obtain ⟨hfin, hcomp, hcoords⟩ := quaternionicSpinIsometryTransport e π incl D V
    exact ⟨hfin, hcomp, fun R ↦ hcoords R (C R)⟩
  · intro Z U z p unitInclusion h hU hker hscalar
    obtain ⟨hpb, ht, h', hcoord⟩ :=
      quaternionicSpinScalarKernelTransport e π D z p unitInclusion hU hker h hscalar
    exact ⟨hpb, ht, h', fun R q ↦ hcoord R (C R) q⟩
  · intro A x c
    obtain ⟨param, torus, hroot, ht, hmarks⟩ := quaternionicSpinMarkedLiftTransport e π D x c
    exact ⟨param, torus, hroot, ht, fun R ↦ hmarks R (C R)⟩

private theorem modelTransportAlong {F E : Type u} [Field F] [Field E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing F] [IsTopologicalRing E]
    [ContinuousInv₀ F] [ContinuousInv₀ E] (e : F ≃+* E) : ModelTransportAlong e := by
  let := scalarStructure e
  refine ⟨matrixModelTopology F, matrixModelTopology E, ?_, specialUnitaryMatrixTransport e, ?_, ?_,
    quaternionicSpinTransportAlong e⟩
  · intro X n c p
    exact matrixCoordinateTransport e X c p
  · intro A _ _ _ h
    obtain ⟨i, hi, hscalar, htensor⟩ := coefficientAlgebraTransport e A h
    let := transportedInvolution i
    have hstar (a : A) : i (star a) = star (i a) := by
      rw [hi (star a), hi a, htensor]
    refine ⟨i, hi, hscalar, htensor, ?_, ?_⟩
    · intro n _ M H
      exact sesquilinearMatrixTransport i hstar M H
    · intro n _ M H L
      exact quaternionicQuadraticFormTransport e i hscalar hstar M H L
  · intro V _ _ Q
    exact cliffordBaseChangeTransport e Q

open scoped CategoryTheory.MonObj in
private theorem groupTransportAlong {F E : Type u} [Field F] [Field E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing F] [IsTopologicalRing E]
    (e : F ≃+* E) (he : Continuous e) (hinv : Continuous e.symm) :
    GroupTransportAlong.{u, w} e := by
  intro G
  let := scalarStructure e
  let G' := _root_.LinearAlgebraicGroups.Specs.Unipotent.baseChangedAlgebraicGroup E G
  let := pointTopology G.val.X
  let := pointTopology G'.val.X
  obtain ⟨f, hf, hfinv, hpoint⟩ := rationalGroupTransport e he hinv G
  let ftop : RationalPoints G.val.X ≃ₜ* RationalPoints G'.val.X := ⟨f, hf, hfinv⟩
  let hF := rationalPointTopologicalGroup G
  let hE := rationalPointTopologicalGroup G'
  exact ⟨ftop, hpoint, hF, hE, quotientTransportAlong ftop⟩

/-- The realization carries the marked algebraic data and the quotient
representation of any original affine algebraic group to that completion. -/
theorem realizationWithTransport : RealizationWithTransport.{u, w} := by
  intro F _ _ _ _
  obtain ⟨K, hK, D, w, e, he, hinv, hvaluation, hintegers⟩ := fieldRealization F
  have hsymm (x y : F) : e.symm x ≤ᵥ e.symm y ↔ x ≤ᵥ y := by
    simpa using (hvaluation (e.symm x) (e.symm y)).symm
  exact ⟨K, hK, D, w, e, ⟨he, hinv, hvaluation, hintegers⟩,
    markedGroupTransportAlong e.symm hsymm, modelTransportAlong e.symm,
    groupTransportAlong e.symm hinv he⟩

end Transport

end LinearAlgebraicGroups.Arithmetic.LocalFieldRealization
