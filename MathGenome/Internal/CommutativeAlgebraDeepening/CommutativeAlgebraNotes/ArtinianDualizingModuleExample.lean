import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ArtinianDualizingModuleExample
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ArtinianSocleCriterion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteLocalDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.SocleCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.GorensteinExtProfile

noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing AdvCommAlg.Depth
open scoped Pointwise
open Specs.CommutativeAlgebraNotes.ArtinianDualizingModuleExample

namespace CommutativeAlgebraNotes.ArtinianDualizingModuleExample

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u w

variable (k : Type u) [Field k]

private theorem variables_eq_maximal : variableIdeal k = maximalIdeal (Series k) :=
  (CompleteRegularPowerSeries.overField k 2).2.2.2.1.symm

private theorem maximalIdeal_eq : maximalIdeal (QuotientRing k) = Ideal.span (Set.range (coordinate k)) := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (quotientMap k) Ideal.Quotient.mk_surjective,
    ← variables_eq_maximal]
  unfold variableIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

private theorem maximalIdeal_sq : maximalIdeal (QuotientRing k) ^ 2 = ⊥ := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (quotientMap k) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, ← variables_eq_maximal]
  exact Ideal.map_mk_eq_bot_of_le le_rfl

private def exponent : Option (Fin 2) → (Fin 2 →₀ ℕ)
  | none => 0
  | some i => Finsupp.single i 1

private theorem exponent_injective : Function.Injective exponent := by
  intro a b h
  cases a <;> cases b
  · rfl
  · simp [exponent, eq_comm (a := (0 : Fin 2 →₀ ℕ))] at h
  · simp [exponent] at h
  · simpa [exponent, Finsupp.single_left_inj] using h

private theorem degree_exponent (i : Option (Fin 2)) : (exponent i).degree < 2 := by
  cases i <;> simp [exponent]

/-- Modulo the square of the maximal ideal, only degrees zero and one survive. -/
private theorem mem_square_iff (f : Series k) :
    f ∈ variableIdeal k ^ 2 ↔ ∀ i, MvPowerSeries.coeff (exponent i) f = 0 := by
  rw [variables_eq_maximal, CompleteRegularPowerSeries.maximalIdealPower k 2 2]
  rw [show maximalIdeal k = ⊥ from IsLocalRing.maximalIdeal_eq_bot]
  constructor
  · intro h i
    have hp : 2 - (exponent i).degree ≠ 0 := by
      have := degree_exponent i
      omega
    simpa [Ideal.bot_pow hp] using h (exponent i)
  · intro h a
    by_cases ha : 2 ≤ a.degree
    · simp [Nat.sub_eq_zero_of_le ha]
    have hl : a.degree = 0 ∨ a.degree = 1 := by omega
    rcases hl with hl | hl
    · rw [(Finsupp.degree_eq_zero_iff a).mp hl]
      simpa [exponent, Ideal.bot_pow (by decide : (2 : ℕ) ≠ 0)] using h none
    · have hm : a ∈ Set.range (fun i : Fin 2 => Finsupp.single i 1) :=
        Finsupp.range_single_one.symm ▸ (show a ∈ {d | d.degree = 1} from hl)
      obtain ⟨i, rfl⟩ := hm
      simpa [exponent] using h (some i)

private def lowCoeffs : Series k →ₗ[k] (Option (Fin 2) → k) where
  toFun f i := MvPowerSeries.coeff (exponent i) f
  map_add' f g := funext fun i => map_add (MvPowerSeries.coeff (exponent i)) f g
  map_smul' a f := funext fun i => MvPowerSeries.coeff_smul f (exponent i) a

private def coeffs : QuotientRing k →ₗ[k] (Option (Fin 2) → k) :=
  { QuotientAddGroup.lift (variableIdeal k ^ 2).toAddSubgroup (lowCoeffs k).toAddMonoidHom
      (fun f hf => funext ((mem_square_iff k f).mp hf)) with
    map_smul' a r := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
      exact (lowCoeffs k).map_smul a f }

private theorem coeffs_mk (f : Series k) (i : Option (Fin 2)) :
    coeffs k (quotientMap k f) i = MvPowerSeries.coeff (exponent i) f := rfl

private theorem coeffs_injective : Function.Injective (coeffs k) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro r hr
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_square_iff k f).mpr
    (fun i => congrFun (LinearMap.mem_ker.mp hr) i))

private def monomial (i : Option (Fin 2)) : Series k :=
  MvPowerSeries.monomial (exponent i) 1

private theorem coeffs_monomial (i j : Option (Fin 2)) :
    coeffs k (quotientMap k (monomial k i)) j = if j = i then 1 else 0 := by
  classical
  simp [coeffs_mk, monomial, MvPowerSeries.coeff_monomial, exponent_injective.eq_iff, eq_comm]

private theorem coeffs_surjective : Function.Surjective (coeffs k) := by
  classical
  intro a
  refine ⟨∑ i, a i • quotientMap k (monomial k i), ?_⟩
  funext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coeffs_monomial,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private def coeffEquiv : QuotientRing k ≃ₗ[k] (Option (Fin 2) → k) :=
  LinearEquiv.ofBijective (coeffs k) ⟨coeffs_injective k, coeffs_surjective k⟩

private def coordinateBasis : Module.Basis (Option (Fin 2)) k (QuotientRing k) :=
  (Pi.basisFun k _).map (coeffEquiv k).symm

private theorem coordinateBasis_eq (i : Option (Fin 2)) :
    coordinateBasis k i = quotientMap k (monomial k i) := by
  apply (coeffEquiv k).injective
  funext j
  rw [show coeffEquiv k (coordinateBasis k i) = Pi.single i 1 by
    simp [coordinateBasis, Pi.basisFun_apply]]
  change (Pi.single i (1 : k) : Option (Fin 2) → k) j = coeffs k (quotientMap k (monomial k i)) j
  rw [Pi.single_apply, coeffs_monomial]

theorem coordinates : Coordinates.{u} := by
  intro k _
  refine ⟨maximalIdeal_eq k, maximalIdeal_sq k, coordinateBasis k, ?_, ?_⟩
  · simpa [monomial, exponent] using coordinateBasis_eq k none
  · intro i
    exact coordinateBasis_eq k (some i)

private theorem noetherian : IsNoetherianRing (QuotientRing k) := by
  have : IsRegularLocalRing (Series k) := (CompleteRegularPowerSeries.overField k 2).2.1
  infer_instance

private theorem artinian : IsArtinianRing (QuotientRing k) := by
  have := noetherian k
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal (QuotientRing k)).mpr
    ⟨2, (maximalIdeal_sq k).trans Ideal.zero_eq_bot.symm⟩

/-- The adic quotients stabilize at the second power, whose ideal is zero. -/
private theorem complete : IsAdicComplete (maximalIdeal (QuotientRing k)) (QuotientRing k) := by
  let I := maximalIdeal (QuotientRing k)
  have hz (n : ℕ) (hn : 2 ≤ n) : I ^ n • (⊤ : Submodule (QuotientRing k) (QuotientRing k)) = ⊥ := by
    have he : I ^ n = ⊥ := le_antisymm ((Ideal.pow_le_pow_right hn).trans_eq (maximalIdeal_sq k)) bot_le
    simp [he]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h := hx 2
    rw [hz 2 le_rfl, SModEq.bot] at h
    exact h
  · intro f hf
    refine ⟨f 2, fun n => ?_⟩
    by_cases hn : n ≤ 2
    · exact hf hn
    · have he := hf (show 2 ≤ n by omega)
      rw [hz 2 le_rfl, SModEq.bot] at he
      rw [he]
      rfl

theorem ringStructure : RingStructure.{u} :=
  fun k _ => ⟨artinian k, noetherian k, complete k⟩

private def constantMap : Series k →ₐ[k] k :=
  { MvPowerSeries.constantCoeff with
    commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }

private def augmentation : QuotientRing k →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (constantMap k)
    (fun f hf => (show MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) f = 0 from
      (mem_square_iff k f).mp hf none))

private theorem coeffs_none (r : QuotientRing k) : coeffs k r none = augmentation k r := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
  rfl

private theorem mem_maximal (r : QuotientRing k) :
    r ∈ maximalIdeal (QuotientRing k) ↔ augmentation k r = 0 := by
  apply Iff.intro
  · intro hr
    have h : r ^ 2 = 0 := by
      have hr' := Ideal.pow_mem_pow hr 2
      rwa [maximalIdeal_sq, Ideal.mem_bot] at hr'
    simpa using congrArg (augmentation k) h
  · intro h
    exact (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (augmentation k).toRingHom)) h

private def residueEquiv : ResidueField (QuotientRing k) ≃ₐ[k] k := by
  let f : ResidueField (QuotientRing k) →ₐ[k] k :=
    Ideal.Quotient.liftₐ _ (augmentation k) fun a ha => (mem_maximal k a).mp ha
  exact AlgEquiv.ofBijective f ⟨f.injective, fun a => ⟨algebraMap k _ a, f.commutes a⟩⟩

private theorem residueEquiv_apply (r : QuotientRing k) :
    residueEquiv k (residue _ r) = augmentation k r := rfl

private theorem mul_zero_of_mem_maximal {a b : QuotientRing k}
    (ha : a ∈ maximalIdeal (QuotientRing k)) (hb : b ∈ maximalIdeal (QuotientRing k)) :
    a * b = 0 := by
  have h : a * b ∈ maximalIdeal (QuotientRing k) ^ 2 :=
    pow_two (maximalIdeal (QuotientRing k)) ▸ Ideal.mul_mem_mul ha hb
  simpa [maximalIdeal_sq] using h

private theorem coordinate_mem (i : Fin 2) :
    coordinate k i ∈ maximalIdeal (QuotientRing k) := by
  rw [maximalIdeal_eq]
  exact Ideal.subset_span ⟨i, rfl⟩

private theorem mem_ringSocle (r : QuotientRing k) :
    r ∈ Socle (QuotientRing k) (QuotientRing k) ↔ r ∈ maximalIdeal (QuotientRing k) := by
  rw [AdvCommAlg.Gorenstein.mem_socle_iff]
  constructor
  · intro h
    let x := coordinate k 0
    have hxm : x ∈ maximalIdeal (QuotientRing k) := coordinate_mem k 0
    have hx : x ≠ 0 := by
      change coordinate k 0 ≠ 0
      rw [← (coordinates k).2.2.choose_spec.2 0]
      exact (coordinates k).2.2.choose.ne_zero _
    have hd : r - algebraMap k _ (augmentation k r) ∈ maximalIdeal (QuotientRing k) :=
      (mem_maximal k _).mpr (by simp)
    have hp := mul_zero_of_mem_maximal k hxm hd
    rw [mul_sub, show x * r = 0 from h x hxm, zero_sub, neg_eq_zero,
      mul_comm, ← Algebra.smul_def, smul_eq_zero] at hp
    exact (mem_maximal k r).mpr (hp.resolve_right hx)
  · intro hr a ha
    exact mul_zero_of_mem_maximal k ha hr

private theorem ringSocle_eq :
    Socle (QuotientRing k) (QuotientRing k) =
      (maximalIdeal (QuotientRing k) : Submodule (QuotientRing k) (QuotientRing k)) :=
  Submodule.ext (mem_ringSocle k)

private def socleCoords :
    Socle (QuotientRing k) (QuotientRing k) →ₗ[k] (Fin 2 → k) where
  toFun r i := coeffs k r.val (some i)
  map_add' r s := by ext i; exact congrFun ((coeffs k).map_add r.val s.val) _
  map_smul' a r := by ext i; exact congrFun ((coeffs k).map_smul a r.val) _

private theorem socleCoords_bijective : Function.Bijective (socleCoords k) := by
  constructor
  · intro r s h
    apply Subtype.ext
    apply coeffs_injective k
    funext i
    cases i with
    | none =>
      rw [coeffs_none, coeffs_none, (mem_maximal k _).mp ((mem_ringSocle k _).mp r.prop),
        (mem_maximal k _).mp ((mem_ringSocle k _).mp s.prop)]
    | some i => exact congrFun h i
  · intro a
    let b : Option (Fin 2) → k := fun i => i.elim 0 a
    obtain ⟨r, hr⟩ := coeffs_surjective k b
    have hm : r ∈ maximalIdeal (QuotientRing k) := by
      rw [mem_maximal, ← coeffs_none, hr]
      rfl
    exact ⟨⟨r, (mem_ringSocle k r).mpr hm⟩, funext fun i => congrFun hr (some i)⟩

private theorem ringSocle_finrank :
    Module.finrank (ResidueField (QuotientRing k)) (Socle (QuotientRing k) (QuotientRing k)) = 2 := by
  have h : Module.finrank k (ResidueField (QuotientRing k)) = 1 :=
    (residueEquiv k).toLinearEquiv.finrank_eq.trans (Module.finrank_self k)
  have : IsScalarTower k (ResidueField (QuotientRing k)) (Socle (QuotientRing k) (QuotientRing k)) :=
    show IsScalarTower k (QuotientRing k ⧸ maximalIdeal (QuotientRing k))
      (Submodule.torsionBySet (QuotientRing k) (QuotientRing k) (maximalIdeal (QuotientRing k)))
      from inferInstance
  have e := LinearEquiv.ofBijective (socleCoords k) (socleCoords_bijective k)
  simpa [h] using
    (Module.finrank_mul_finrank k (ResidueField (QuotientRing k))
      (Socle (QuotientRing k) (QuotientRing k))).trans e.finrank_eq

theorem dualAction : DualAction.{u} := by
  intro k _ a r φ
  change dualApply k φ (r * a) = dualApply k φ (a * r)
  rw [mul_comm]

private theorem mem_dualSocle (φ : Dual k) :
    φ ∈ Socle (QuotientRing k) (Dual k) ↔
      ∀ a ∈ maximalIdeal (QuotientRing k), dualApply k φ a = 0 := by
  rw [AdvCommAlg.Gorenstein.mem_socle_iff]
  constructor
  · intro h a ha
    have hz := congrArg (fun ψ : Dual k => dualApply k ψ 1) (h a ha)
    change dualApply k φ (1 * a) = (0 : k) at hz
    rwa [one_mul] at hz
  · intro h a ha
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro r
    change QuotientRing k at r
    change dualApply k φ (r * a) = 0
    exact h _ (Ideal.mul_mem_left _ r ha)

private abbrev restrictedResidue :=
  (ModuleCat.restrictScalars (algebraMap k (QuotientRing k))).obj
    (ModuleCat.of (QuotientRing k) (ResidueField (QuotientRing k)))

private def residueLinear : restrictedResidue k ⟶ ModuleCat.of k k :=
  ModuleCat.ofHom (X := restrictedResidue k) (Y := ModuleCat.of k k)
    { toFun := fun a => residueEquiv k a
      map_add' := (residueEquiv k).map_add
      map_smul' a b := by
        change residueEquiv k (algebraMap k (ResidueField (QuotientRing k)) a * (show ResidueField (QuotientRing k) from b)) =
          a * residueEquiv k b
        rw [map_mul, AlgEquiv.commutes, Algebra.algebraMap_self_apply] }

private def residueInclusion : ResidueField (QuotientRing k) →ₗ[QuotientRing k] Dual k :=
  (ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction
    (algebraMap k (QuotientRing k)) (residueLinear k)).hom

private theorem residueInclusion_apply (a : ResidueField (QuotientRing k)) (r : QuotientRing k) :
    dualApply k (residueInclusion k a) r = augmentation k r * residueEquiv k a := by
  change residueEquiv k (residue (QuotientRing k) r * a) = _
  rw [map_mul, residueEquiv_apply]

private theorem dualApply_sub (φ : Dual k) (a b : QuotientRing k) :
    dualApply k φ (a - b) = dualApply k φ a - dualApply k φ b :=
  (ModuleCat.CoextendScalars.equiv (algebraMap k (QuotientRing k)) (ModuleCat.of k k) φ).map_sub a b

private theorem dualApply_algebraMap (φ : Dual k) (a : k) :
    dualApply k φ (algebraMap k (QuotientRing k) a) = a * dualApply k φ 1 := by
  have h := (ModuleCat.CoextendScalars.equiv (algebraMap k (QuotientRing k))
    (ModuleCat.of k k) φ).map_smul a (show QuotientRing k from 1)
  change dualApply k φ (algebraMap k (QuotientRing k) a * 1) = _ at h
  rwa [mul_one] at h

private theorem residueInclusion_injective : Function.Injective (residueInclusion k) := by
  intro a b hab
  apply (residueEquiv k).injective
  simpa [residueInclusion_apply] using congrArg (fun φ : Dual k => dualApply k φ 1) hab

private theorem residueInclusion_range :
    LinearMap.range (residueInclusion k) = Socle (QuotientRing k) (Dual k) := by
  ext φ
  rw [mem_dualSocle]
  constructor
  · rintro ⟨a, rfl⟩ r hr
    simp [residueInclusion_apply, (mem_maximal k r).mp hr]
  · intro h
    refine ⟨(residueEquiv k).symm (dualApply k φ 1), ?_⟩
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro r
    change dualApply k (residueInclusion k ((residueEquiv k).symm (dualApply k φ 1))) r = dualApply k φ r
    change QuotientRing k at r
    rw [residueInclusion_apply, AlgEquiv.apply_symm_apply]
    have hd : r - algebraMap k _ (augmentation k r) ∈ maximalIdeal (QuotientRing k) :=
      (mem_maximal k _).mpr (by simp)
    have hz := h _ hd
    rw [dualApply_sub, dualApply_algebraMap, sub_eq_zero] at hz
    exact hz.symm

/-- Coinduction carries the injective k-module k to an injective R-module. -/
private theorem dual_injective : Module.Injective (QuotientRing k) (Dual k) := by
  apply (Module.injective_iff_injective_object _ _).mpr
  change Injective (Dual k)
  exact (ModuleCat.restrictCoextendScalarsAdj (algebraMap k (QuotientRing k))).map_injective _
    (by
      apply (Module.injective_iff_injective_object k k).mp
      refine ⟨fun {X Y} _ _ _ _ i hi f => ?_⟩
      obtain ⟨g, hg⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
      exact ⟨f.comp g, fun x => DFunLike.congr_arg f (DFunLike.congr_fun hg x)⟩)

private theorem isEnvelope : AdvCommAlg.Gorenstein.IsInjectiveEnvelope (residueInclusion k) := by
  refine ⟨residueInclusion_injective k, dual_injective k, ?_⟩
  intro N hN
  rw [residueInclusion_range]
  apply socle_essential_of_powerTorsion _ N hN
  apply top_unique
  intro φ _
  rw [mem_idealTorsion]
  refine ⟨2, by decide, ?_⟩
  intro a ha
  rw [maximalIdeal_sq, Ideal.mem_bot] at ha
  rw [ha, zero_smul]

theorem dualEnvelope : DualEnvelope.{u} :=
  fun k _ => ⟨residueInclusion k, isEnvelope k, residueInclusion_range k⟩

private theorem dualSocle_finrank :
    Module.finrank (ResidueField (QuotientRing k)) (Socle (QuotientRing k) (Dual k)) = 1 := by
  let f := (residueInclusion k).codRestrict (Socle (QuotientRing k) (Dual k))
    (fun a => residueInclusion_range k ▸ LinearMap.mem_range_self _ a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => residueInclusion_injective k (congrArg Subtype.val h), ?_⟩
    intro a
    have ha : a.val ∈ LinearMap.range (residueInclusion k) := by
      rw [residueInclusion_range]
      exact a.prop
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, Subtype.ext hb⟩
  let e := AdvCommAlg.Depth.residueLinearEquiv (QuotientRing k) (LinearEquiv.ofBijective f hf)
  rw [← e.finrank_eq, Module.finrank_self]

theorem socles : Socles.{u} := by
  intro k _
  exact ⟨⟨residueEquiv k, fun _ => rfl⟩, ringSocle_eq k, mem_dualSocle k,
    ringSocle_finrank k, dualSocle_finrank k⟩

theorem notGorenstein : NotGorenstein.{u} := by
  intro k _ hG
  have := artinian k
  have hd : ringKrullDim (QuotientRing k) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  have hi := (AdvCommAlg.Gorenstein.localGorenstein_injectiveDimension (QuotientRing k) hG).trans hd
  have hself : Module.Injective (QuotientRing k) (QuotientRing k) :=
    (Module.injective_iff_injective_object _ _).mpr
      ((injectiveDimension_eq_zero_iff _).mp (by simpa using hi)).1
  have h := (ringSocle_finrank k).symm.trans
    (AdvCommAlg.Gorenstein.socle_finrank_one_of_selfInjective hself)
  norm_num at h


open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (Complex stalk ShiftedRingResolution)
open Specs.CommutativeAlgebraNotes.CechDualizingComplexModel (cechDual)
open CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)

private def generators : List (QuotientRing k) := [coordinate k 0, coordinate k 1]

private theorem generators_span :
    Ideal.span {r | r ∈ generators k} = maximalIdeal (QuotientRing k) := by
  rw [maximalIdeal_eq]
  congr 1
  ext r
  change r ∈ generators k ↔ r ∈ Set.range (coordinate k)
  simp only [generators, List.mem_cons, List.not_mem_nil, or_false, Set.mem_range]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

private theorem generators_get_mem (i : Fin (generators k).length) :
    (generators k).get i ∈ maximalIdeal (QuotientRing k) := by
  rw [← generators_span]
  exact Ideal.subset_span (List.get_mem _ _)

private theorem localizationAway_subsingleton {R : Type u} [CommRing R] {p : R}
    (hp : IsNilpotent p) : Subsingleton (Localization.Away p) := by
  obtain ⟨n, hn⟩ := hp
  exact IsLocalization.subsingleton (M := Submonoid.powers p) ⟨n, hn⟩

/-- Every summand off degree zero inverts a product containing a nilpotent generator. -/
private theorem cech_isZero (n : ℤ) (hn : n ≠ 0) :
    IsZero ((Specs.CommutativeAlgebraNotes.AugmentedCechComplex.complex
      (QuotientRing k) (generators k)).X n) := by
  classical
  let R := QuotientRing k
  let rs := generators k
  obtain ⟨ι, hι, he, hp, _⟩ := Cech.ringTermFormula rs
  obtain ⟨hc⟩ := hι n
  obtain ⟨e, he⟩ := he n
  have hz (s : Specs.CommutativeAlgebraNotes.AugmentedCechComplex.Selection rs.length n) :
      IsZero (Specs.CommutativeAlgebraNotes.AugmentedCechComplex.term R rs s) := by
    let p := Specs.CommutativeAlgebraNotes.AugmentedCechComplex.product R rs s
    have hm : p ∈ maximalIdeal R := by
      change Specs.CommutativeAlgebraNotes.AugmentedCechComplex.product R rs s ∈ _
      rw [hp]
      have hne : (Finset.univ.filter (fun i => Specs.CommutativeAlgebraNotes.AugmentedCechComplex.selected s i = true)).Nonempty := by
        have hcard := (e s).prop
        rw [he] at hcard
        exact Finset.nonempty_iff_ne_empty.mpr fun h => hn (by simpa [h] using hcard.symm)
      obtain ⟨i, hi⟩ := hne
      exact Ideal.prod_mem _ hi (generators_get_mem k i)
    have hp0 : IsNilpotent p := ⟨2, pow_two p ▸ mul_zero_of_mem_maximal k hm hm⟩
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton (Localization.Away p)
    exact localizationAway_subsingleton hp0
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Cofan.IsColimit.hom_ext hc
  intro s
  exact (hz s).eq_of_src _ _

private def isoStalk {R : Type u} [CommRing R] (K : Complex R) (M : ModuleCat.{u} R)
    (e : K.X 0 ≅ M) (hz : ∀ i : ℤ, i ≠ 0 → IsZero (K.X i)) :
    K ≅ stalk R 0 M := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) (fun i j hij => ?_)
  · by_cases hi : i = 0
    · subst i
      exact e ≪≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm
    · exact (hz i hi).iso (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
  · by_cases hi : i = 0
    · have hj : j ≠ 0 := by
        change i + 1 = j at hij
        omega
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M j hj).eq_of_tgt _ _
    · exact (hz i hi).eq_of_src _ _

private def cechZeroIso :
    (Specs.CommutativeAlgebraNotes.AugmentedCechComplex.complex
      (QuotientRing k) (generators k)).X 0 ≅ ModuleCat.of (QuotientRing k) (QuotientRing k) :=
  Classical.choice (Cech.degreeZeroTerm (generators k))

theorem cechConcentration : CechConcentration.{u} := by
  intro k _
  exact ⟨isoStalk _ _ (cechZeroIso k) (cech_isZero k)⟩

private def dualAsEnvelope : residueFieldEnvelopeValue (QuotientRing k) where
  carrier := Dual k
  inclusion := residueInclusion k
  isEnvelope := isEnvelope k

private def cechDualTermEquiv (n : ℤ) :
    ((cechDual (dualAsEnvelope k) (generators k)).X n) ≃ₗ[QuotientRing k]
      ((Specs.CommutativeAlgebraNotes.AugmentedCechComplex.complex
        (QuotientRing k) (generators k)).X (-n) ⟶ Dual k) :=
  CochainComplex.HomComplex.Cochain.toSingleLinearEquiv (neg_add_cancel n)

private def cechDualStalkIso : cechDual (dualAsEnvelope k) (generators k) ≅
    stalk (QuotientRing k) 0 (Dual k) := by
  apply isoStalk
  · have e := cechDualTermEquiv k 0
    rw [neg_zero] at e
    exact (e.trans (ModuleCat.homLinearEquiv.trans
      ((LinearEquiv.arrowCongr (cechZeroIso k).toLinearEquiv (LinearEquiv.refl _ _)).trans
        (LinearMap.ringLmapEquivSelf _ _ _)))).toModuleIso
  · intro n hn
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun a b => (cechDualTermEquiv k n).injective ?_⟩
    exact (cech_isZero k (-n) (neg_ne_zero.mpr hn)).eq_of_src _ _

theorem dualizingObject : DualizingObject.{u,w} := by
  intro k _ _
  have hS := CompleteRegularPowerSeries.overField k 2
  have : IsRegularLocalRing (Series k) := hS.2.1
  have : IsAdicComplete (maximalIdeal (Series k)) (Series k) := hS.2.2.1
  have : IsAdicComplete (maximalIdeal (QuotientRing k)) (QuotientRing k) := complete k
  have : IsLocalHom (quotientMap k) :=
    IsLocalHom.of_surjective (quotientMap k) Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim (Series k) = (2 : WithBot ℕ∞) := hS.2.2.2.2.1
  obtain ⟨J₀, _, _⟩ :=
    RegularCoverDualizingModel.shiftedRingResolution_exists (Series k) 2 hdim
  refine ⟨⟨J₀⟩, fun J => ?_⟩
  have h := completeLocalDuality (quotientMap k) Ideal.Quotient.mk_surjective hdim J
    (dualAsEnvelope k)
  obtain ⟨e⟩ := h.1 (generators k) (generators_span k)
  exact ⟨e.symm ≪≫ DerivedCategory.Q.mapIso (cechDualStalkIso k)⟩

end CommutativeAlgebraNotes.ArtinianDualizingModuleExample
