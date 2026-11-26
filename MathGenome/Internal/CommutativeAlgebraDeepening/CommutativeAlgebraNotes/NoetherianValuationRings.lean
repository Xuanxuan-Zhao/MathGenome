import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.OrderedValuationGroups
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.NoetherianValuationRings
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Order.Int.LeastGreatest

noncomputable section

namespace CommutativeAlgebraNotes.NoetherianValuationRings

open Additive (ofMul toMul)
open OrderedValuationGroups (ValueGroup value value_nonneg_iff value_surjective)
open scoped WithZero

universe u v

variable {K : Type u} [Field K] (V : ValuationSubring K)

/-- The field case is exactly the case of a trivial intrinsic value group. -/
theorem isField_iff_subsingleton_valueGroup : IsField V ↔ Subsingleton (ValueGroup V) := by
  constructor
  · intro h
    have hs : Function.Surjective (algebraMap V K) :=
      (h.localization_map_bijective (M := nonZeroDivisors V) (by simp)).surjective
    have hnonneg (a : Kˣ) : 0 ≤ value V (ofMul a) := by
      obtain ⟨b, hb⟩ := hs (a : K)
      exact (value_nonneg_iff V a).mpr (hb ▸ b.property)
    have hzero (a : Kˣ) : value V (ofMul a) = 0 := by
      apply le_antisymm _ (hnonneg a)
      have hn : 0 ≤ value V (-ofMul a) := hnonneg a⁻¹
      rwa [map_neg, neg_nonneg] at hn
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨a, rfl⟩ := value_surjective V x
    obtain ⟨b, rfl⟩ := value_surjective V y
    exact (hzero (toMul a)).trans (hzero (toMul b)).symm
  · intro h
    have htop : V = ⊤ := by
      apply top_unique
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · exact (value_nonneg_iff V (Units.mk0 x hx)).mp (h.elim _ _).le
    subst V
    exact Field.toIsField _

private abbrev ringValue (a : V) (ha : a ≠ 0) : ValueGroup V :=
  value V (ofMul (Units.mk0 (a : K) (fun h ↦ ha (Subtype.ext h))))

private theorem principal_of_valueGroup_int (e : ValueGroup V ≃+o ℤ) :
    IsPrincipalIdealRing V where
  principal I := by
    classical
    by_cases hI : I = ⊥
    · subst I
      exact ⟨0, (Ideal.span_singleton_eq_bot.mpr rfl).symm⟩
    have hex : ∃ a : V, a ∈ I ∧ a ≠ 0 := (Submodule.ne_bot_iff I).mp hI
    let P (n : ℤ) : Prop := ∃ a : V, a ∈ I ∧ ∃ ha : a ≠ 0, e (ringValue V a ha) = n
    have hbdd : ∃ b : ℤ, ∀ n, P n → b ≤ n := by
      refine ⟨0, ?_⟩
      rintro _ ⟨a, _, ha, rfl⟩
      rw [← map_zero e, map_le_map_iff e]
      exact (value_nonneg_iff V _).mpr a.property
    have hP : ∃ n, P n := by
      obtain ⟨a, haI, ha⟩ := hex
      exact ⟨_, a, haI, ha, rfl⟩
    obtain ⟨n, ⟨a, haI, ha, han⟩, hmin⟩ := Int.exists_least_of_bdd hbdd hP
    refine ⟨a, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr haI)⟩
    intro b hbI
    by_cases hb : b = 0
    · exact hb.symm ▸ (Ideal.span {a}).zero_mem
    have hle : ringValue V a ha ≤ ringValue V b hb := by
      rw [← map_le_map_iff e, han]
      exact hmin _ ⟨b, hbI, hb, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    apply (ValuationRing.integers V K).dvd_of_le
    exact (Units.val_le_val (α := V.ValueGroup)).mpr hle

/-- Integer values provide a least-value generator for each nonzero ideal. -/
theorem isDiscreteValuationRing_of_valueGroup_int (h : Nonempty (ValueGroup V ≃+o ℤ)) :
    IsDiscreteValuationRing V := by
  obtain ⟨e⟩ := h
  let : IsPrincipalIdealRing V := principal_of_valueGroup_int V e
  refine { not_a_field' := ?_ }
  intro hmax
  have hfield : IsField V := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
  have ht := (isField_iff_subsingleton_valueGroup V).mp hfield
  exact zero_ne_one (e.symm.injective (ht.elim (e.symm 0) (e.symm 1)))

private theorem valueGroup_int_of_dvr [IsDiscreteValuationRing V] :
    Nonempty (ValueGroup V ≃+o ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let πK : Kˣ := Units.mk0 (π : K) (fun h ↦ hπ.ne_zero (Subtype.ext h))
  let γ := value V (ofMul πK)
  have hγ : 0 < γ := by
    have hlt : V.valuation (π : K) < 1 := (V.valuation_lt_one_iff π).mp hπ.not_isUnit
    exact (Units.val_lt_val (α := V.ValueGroup)).mp hlt
  let f := zmultiplesHom (ValueGroup V) γ
  have hf : StrictMono f := zsmul_left_strictMono hγ
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨a, rfl⟩ := value_surjective V g
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := K) hπ (toMul a).ne_zero
    let uK := Units.map (algebraMap V K).toMonoidHom u
    have ha : a = ofMul uK + n • ofMul πK := by
      change toMul a = uK * πK ^ n
      apply Units.ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
      change ((toMul a : Kˣ) : K) = algebraMap V K (u : V) * algebraMap V K π ^ n
      simpa only [Units.smul_def, Algebra.smul_def] using hu
    have hu₀ : value V (ofMul uK) = 0 := Units.ext (V.valuation_unit u)
    refine ⟨n, ?_⟩
    rw [ha, map_add, map_zsmul, hu₀, zero_add]
    rfl
  let e : ℤ ≃+o ValueGroup V :=
    { AddEquiv.ofBijective f ⟨hf.injective, hsurj⟩ with map_le_map_iff' := hf.le_iff_le }
  exact ⟨e.symm⟩

/-- A Noetherian valuation ring is a field or has ordered additive value group `ℤ`. -/
theorem noetherian_iff :
    IsNoetherianRing V ↔ IsField V ∨ Nonempty (ValueGroup V ≃+o ℤ) := by
  constructor
  · intro h
    by_cases hfield : IsField V
    · exact Or.inl hfield
    · let : IsDiscreteValuationRing V :=
        { not_a_field' := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hfield }
      exact Or.inr (valueGroup_int_of_dvr V)
  · rintro (hfield | h)
    · let := hfield.toField
      infer_instance
    · let := isDiscreteValuationRing_of_valueGroup_int V h
      infer_instance

private def reverseValueGroupOrder : ValueGroup V ≃+o Additive V.ValueGroupˣ where
  toAddEquiv := AddEquiv.neg _
  map_le_map_iff' := neg_le_neg_iff

/-- Negation accounts for the reversed order when adjoining zero in the multiplicative convention. -/
theorem valueGroup_int_iff_multiplicative :
    Nonempty (ValueGroup V ≃+o ℤ) ↔ Nonempty (V.ValueGroup ≃*o ℤᵐ⁰) := by
  classical
  constructor
  · rintro ⟨e⟩
    let unitsIso := OrderAddMonoidIso.toMultiplicativeRight ((reverseValueGroupOrder V).symm.trans e)
    exact ⟨OrderMonoidIso.withZeroUnits.symm.trans (OrderMonoidIso.withZero unitsIso)⟩
  · rintro ⟨e⟩
    let unitsIso := e.unitsCongr.trans OrderMonoidIso.unitsWithZero
    exact ⟨(reverseValueGroupOrder V).trans (OrderMonoidIso.toAdditiveLeft unitsIso)⟩

private def valueGroupIsoOfSurjective {F G : Type*} [Field F]
    [LinearOrderedCommGroupWithZero G] (w : Valuation F G) (hw : Function.Surjective w) :
    w.ValueGroup₀ ≃*o G := by
  open MonoidWithZeroHom.ValueGroup₀ in
  let f := embedding (f := w.toMonoidWithZeroHom)
  have hmono : StrictMono f := embedding_strictMono
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨x, rfl⟩ := hw g
    exact ⟨restrict₀ w.toMonoidWithZeroHom x, embedding_restrict₀ x⟩
  exact { MulEquiv.ofBijective f.toMonoidHom ⟨hmono.injective, hsurj⟩ with
    map_le_map_iff' := hmono.le_iff_le }

open Specs.CommutativeAlgebraNotes.NoetherianValuationRings (fractionFieldValueGroup)

/-- The classification for a valuation domain with an arbitrary fraction field. -/
theorem valuationDomain_classification (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F] :
    (IsNoetherianRing R ↔ IsField R ∨ Nonempty (fractionFieldValueGroup R F ≃+o ℤ)) ∧
      (Nonempty (fractionFieldValueGroup R F ≃+o ℤ) → IsDiscreteValuationRing R) := by
  let w := ValuationRing.valuation R F
  let A := w.valuationSubring
  let e : R ≃+* A := ValuationRing.equivInteger R F
  have hw : Function.Surjective w := Quotient.mk_surjective
  let g := (valueGroupIsoOfSurjective w hw).symm.trans
    ((w.isEquiv_valuation_valuationSubring).orderMonoidIso.trans
      (valueGroupIsoOfSurjective A.valuation A.valuation_surjective))
  let gu := OrderMonoidIso.toAdditive g.unitsCongr
  let ψ : fractionFieldValueGroup R F ≃+o ValueGroup A :=
    { gu.toAddEquiv with map_le_map_iff' := gu.map_le_map_iff' }
  have hgroup : Nonempty (ValueGroup A ≃+o ℤ) ↔
      Nonempty (fractionFieldValueGroup R F ≃+o ℤ) :=
    ⟨fun ⟨f⟩ ↦ ⟨ψ.trans f⟩, fun ⟨f⟩ ↦ ⟨ψ.symm.trans f⟩⟩
  have hnoeth : IsNoetherianRing R ↔ IsNoetherianRing A :=
    ⟨fun _ ↦ isNoetherianRing_of_ringEquiv R e, fun _ ↦ isNoetherianRing_of_ringEquiv A e.symm⟩
  refine ⟨hnoeth.trans ((noetherian_iff A).trans (or_congr e.toMulEquiv.isField_congr.symm hgroup)),
    ?_⟩
  intro h
  let : IsDiscreteValuationRing A := isDiscreteValuationRing_of_valueGroup_int A (hgroup.mpr h)
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm

end CommutativeAlgebraNotes.NoetherianValuationRings
