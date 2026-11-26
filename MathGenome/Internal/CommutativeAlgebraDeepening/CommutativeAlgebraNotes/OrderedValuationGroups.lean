import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.OrderedValuationGroups

noncomputable section

namespace CommutativeAlgebraNotes.OrderedValuationGroups

open Function
open Additive (ofMul toMul)
open Specs.CommutativeAlgebraNotes.OrderedValuationGroups (fieldUnitImage)
open scoped Classical

universe u v

variable {K : Type u} [Field K]

/-- The intrinsic value group in the additive sign convention. -/
abbrev ValueGroup (V : ValuationSubring K) : Type u :=
  Specs.CommutativeAlgebraNotes.OrderedValuationGroups.valueGroup V

/-- The intrinsic additive valuation on the nonzero elements of the field. -/
abbrev value (V : ValuationSubring K) : Additive Kˣ →+ ValueGroup V :=
  Specs.CommutativeAlgebraNotes.OrderedValuationGroups.value V

/-- The valuation inequality on nonzero elements with nonzero sum. -/
abbrev AddValuationInequality {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ]
    (f : Additive Kˣ →+ Γ) : Prop :=
  Specs.CommutativeAlgebraNotes.OrderedValuationGroups.AddValuationInequality f

private abbrev unitValue (V : ValuationSubring K) : Kˣ →* V.ValueGroupˣ :=
  Units.map V.valuation.toMonoidWithZeroHom.toMonoidHom

theorem value_surjective (V : ValuationSubring K) : Surjective (value V) := by
  intro g
  let b : V.ValueGroupˣ := toMul g
  obtain ⟨a, ha⟩ := V.valuation_surjective (b : V.ValueGroup)
  have ha₀ : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact b.ne_zero ha.symm
  refine ⟨ofMul (Units.mk0 a ha₀), ?_⟩
  change unitValue V (Units.mk0 a ha₀) = b
  exact Units.ext ha

private theorem unitValue_ker (V : ValuationSubring K) :
    (unitValue V).ker = fieldUnitImage V := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro ha
    have h : V.valuation (a : K) = V.valuation 1 :=
      (congrArg Units.val ha).trans (map_one V.valuation).symm
    obtain ⟨b, hb⟩ := (V.valuation_eq_iff _ _).mp h
    refine ⟨b, Units.ext ?_⟩
    change ((b : V) : K) = (a : K)
    simpa only [mul_one] using hb
  · rintro ⟨b, rfl⟩
    exact Units.ext (V.valuation_unit b)

/-- The additivized quotient of field units by ring units realizes the intrinsic value group. -/
theorem quotient_identification (V : ValuationSubring K) :
    ∃ e : Additive (Kˣ ⧸ fieldUnitImage V) ≃+ ValueGroup V,
      ∀ a : Kˣ, e (ofMul (QuotientGroup.mk' (fieldUnitImage V) a)) = value V (ofMul a) := by
  let e := (QuotientGroup.quotientMulEquivOfEq (unitValue_ker V).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (φ := unitValue V) (value_surjective V))
  exact ⟨e.toAdditive, fun _ ↦ rfl⟩

theorem value_order (V : ValuationSubring K) (x y z : ValueGroup V) :
    (x ≤ y ∨ y ≤ x) ∧ (x + z ≤ y + z ↔ x ≤ y) :=
  ⟨le_total x y, add_le_add_iff_right z⟩

theorem value_le_iff_div_mem (V : ValuationSubring K) (a b : Kˣ) :
    value V (ofMul b) ≤ value V (ofMul a) ↔ (a : K) / (b : K) ∈ V := by
  change unitValue V a ≤ unitValue V b ↔ _
  rw [← Units.val_le_val]
  change V.valuation (a : K) ≤ V.valuation (b : K) ↔ _
  rw [← V.valuation_le_one_iff, map_div₀]
  exact (div_le_one₀ (zero_lt_iff.mpr (b.map V.valuation.toMonoidWithZeroHom.toMonoidHom).ne_zero)).symm

@[simp]
theorem value_nonneg_iff (V : ValuationSubring K) (a : Kˣ) :
    0 ≤ value V (ofMul a) ↔ (a : K) ∈ V := by
  simpa using value_le_iff_div_mem V a 1

theorem value_add_ge_min (V : ValuationSubring K) : AddValuationInequality (value V) := by
  intro a b h
  change unitValue V (Units.mk0 ((a : K) + (b : K)) h) ≤
    max (unitValue V a) (unitValue V b)
  have hmono : Monotone (Units.val : V.ValueGroupˣ → V.ValueGroup) :=
    fun _ _ ↦ Units.val_le_val.mpr
  rw [← Units.val_le_val, hmono.map_max]
  exact V.valuation.map_add _ _

theorem value_add_eq_min (V : ValuationSubring K) (a b : Kˣ)
    (h : (a : K) + (b : K) ≠ 0) (hab : value V (ofMul a) ≠ value V (ofMul b)) :
    value V (ofMul (Units.mk0 ((a : K) + (b : K)) h)) =
      min (value V (ofMul a)) (value V (ofMul b)) := by
  change unitValue V (Units.mk0 ((a : K) + (b : K)) h) =
    max (unitValue V a) (unitValue V b)
  apply Units.ext
  have hmono : Monotone (Units.val : V.ValueGroupˣ → V.ValueGroup) :=
    fun _ _ ↦ Units.val_le_val.mpr
  rw [hmono.map_max]
  exact V.valuation.map_add_of_distinct_val (fun heq ↦ hab (Units.ext heq))

section Converse

variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  (f : Additive Kˣ →+ Γ)

private def withZeroHom : K →*₀ WithZero (Multiplicative Γᵒᵈ) :=
  (WithZero.map' (AddMonoidHom.toMultiplicativeRight f)).comp
    WithZero.withZeroUnitsEquiv.symm.toMonoidWithZeroHom

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem withZeroHom_apply_unit (a : Kˣ) :
    withZeroHom f (a : K) =
      ((Multiplicative.ofAdd (OrderDual.toDual (f (ofMul a))) : Multiplicative Γᵒᵈ) :
        WithZero (Multiplicative Γᵒᵈ)) := by
  change WithZero.map' (AddMonoidHom.toMultiplicativeRight f)
    (WithZero.withZeroUnitsEquiv.symm (a : K)) = _
  rw [WithZero.withZeroUnitsEquiv_symm_apply_coe]
  rfl

private def asValuation (hf : AddValuationInequality f) :
    Valuation K (WithZero (Multiplicative Γᵒᵈ)) where
  __ := withZeroHom f
  map_add_le_max' x y := by
    change withZeroHom f (x + y) ≤ max (withZeroHom f x) (withZeroHom f y)
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hxy : x + y = 0
    · simp [hxy]
    change withZeroHom f (Units.mk0 (x + y) hxy : Kˣ) ≤
      max (withZeroHom f (Units.mk0 x hx : Kˣ)) (withZeroHom f (Units.mk0 y hy : Kˣ))
    rw [withZeroHom_apply_unit, withZeroHom_apply_unit, withZeroHom_apply_unit,
      le_max_iff, WithZero.coe_le_coe, WithZero.coe_le_coe]
    exact min_le_iff.mp (hf (Units.mk0 x hx) (Units.mk0 y hy) hxy)

/-- The valuation subring defined by the nonnegative values of an additive valuation. -/
def valuationSubring (hf : AddValuationInequality f) : ValuationSubring K :=
  (asValuation f hf).valuationSubring

@[simp]
theorem coe_unit_mem_valuationSubring_iff (hf : AddValuationInequality f) (a : Kˣ) :
    (a : K) ∈ valuationSubring f hf ↔ 0 ≤ f (ofMul a) := by
  change withZeroHom f (a : K) ≤ 1 ↔ _
  rw [withZeroHom_apply_unit, WithZero.coe_le_one]
  rfl

theorem mem_valuationSubring_iff (hf : AddValuationInequality f) (x : K) :
    x ∈ valuationSubring f hf ↔ x = 0 ∨ ∃ h : x ≠ 0, 0 ≤ f (ofMul (Units.mk0 x h)) := by
  by_cases hx : x = 0
  · simp [hx]
  · simpa only [hx, false_or, exists_prop_of_true hx, Units.val_mk0] using
      coe_unit_mem_valuationSubring_iff f hf (Units.mk0 x hx)

private theorem compare_values (hf : AddValuationInequality f) (a b : Additive Kˣ) :
    value (valuationSubring f hf) a ≤ value (valuationSubring f hf) b ↔ f a ≤ f b := by
  change value (valuationSubring f hf) (ofMul (toMul a)) ≤
    value (valuationSubring f hf) (ofMul (toMul b)) ↔ _
  rw [value_le_iff_div_mem]
  rw [← Units.val_div_eq_div_val]
  rw [coe_unit_mem_valuationSubring_iff]
  change 0 ≤ f (b - a) ↔ f a ≤ f b
  rw [map_sub, sub_nonneg]

/-- The given additive homomorphism induces an ordered additive isomorphism onto its range. -/
theorem ordered_image (hf : AddValuationInequality f) :
    ∃ e : ValueGroup (valuationSubring f hf) ≃+o f.range,
      ∀ a : Additive Kˣ, e (value (valuationSubring f hf) a) = f.rangeRestrict a := by
  let q := value (valuationSubring f hf)
  have hq : Surjective q := value_surjective _
  have hker : q.ker ≤ f.rangeRestrict.ker := by
    intro a ha
    rw [AddMonoidHom.mem_ker] at ha ⊢
    apply Subtype.ext
    change f a = 0
    have hzero : q a = q 0 := by simpa only [map_zero] using ha
    have heq : f a = f 0 := le_antisymm
      ((compare_values f hf a 0).mp hzero.le) ((compare_values f hf 0 a).mp hzero.ge)
    rw [heq, map_zero]
  let g := q.liftOfSurjective hq ⟨f.rangeRestrict, hker⟩
  have hg (a : Additive Kˣ) : g (q a) = f.rangeRestrict a :=
    q.liftOfRightInverse_comp_apply _ _ _ a
  have horder (x y : ValueGroup (valuationSubring f hf)) : g x ≤ g y ↔ x ≤ y := by
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [hg, hg]
    exact (compare_values f hf a b).symm
  have hgi : Injective g := fun _ _ h ↦
    le_antisymm ((horder _ _).mp h.le) ((horder _ _).mp h.ge)
  have hgs : Surjective g := by
    intro z
    obtain ⟨a, rfl⟩ := f.rangeRestrict_surjective z
    exact ⟨q a, hg a⟩
  exact ⟨{ AddEquiv.ofBijective g ⟨hgi, hgs⟩ with map_le_map_iff' := horder _ _ }, hg⟩

theorem converse (hf : AddValuationInequality f) :
    ∃ V : ValuationSubring K,
      (∀ x : K, x ∈ V ↔ x = 0 ∨ ∃ h : x ≠ 0, 0 ≤ f (ofMul (Units.mk0 x h))) ∧
      ∃ e : ValueGroup V ≃+o f.range, ∀ a : Additive Kˣ, e (value V a) = f.rangeRestrict a :=
  ⟨valuationSubring f hf, mem_valuationSubring_iff f hf, ordered_image f hf⟩

end Converse

end CommutativeAlgebraNotes.OrderedValuationGroups
