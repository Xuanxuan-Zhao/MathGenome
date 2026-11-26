import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.NoetherianValuationRings
import Mathlib.Tactic.FinCases

noncomputable section

namespace CommutativeAlgebraNotes.LexicographicLaurentValuation

open Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation
  (IteratedLaurent LexIntegers seriesValue adicSubring IsSeriesValuation IsLocalizationAndResidue)
open OrderedValuationGroups
open ValuationPrimesAndConvexSubgroups (ConvexAddSubgroup rank_eq_iSup_length)
open Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups (PrimeValues ringValue)
open Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations (residueMap)
open Additive (ofMul toMul)
open HahnSeries
open scoped WithZero

universe u

abbrev vertical : ConvexAddSubgroup LexIntegers :=
  Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation.vertical

private theorem mem_vertical (g : LexIntegers) : g ∈ vertical.1 ↔ (ofLex g).1 = 0 := Iff.rfl

section Valuation

variable (k : Type u) [Field k]

/-- The outer order and the order of the outer leading coefficient. -/
def lexValuation : Additive (IteratedLaurent k)ˣ →+ LexIntegers where
  toFun a := seriesValue (↑(toMul a) : IteratedLaurent k)
  map_zero' := by
    change seriesValue (1 : IteratedLaurent k) = 0
    simp [seriesValue]
  map_add' a b := by
    let x : (IteratedLaurent k)ˣ := toMul a
    let y : (IteratedLaurent k)ˣ := toMul b
    change seriesValue ((x : IteratedLaurent k) * (y : IteratedLaurent k)) =
      seriesValue (x : IteratedLaurent k) + seriesValue (y : IteratedLaurent k)
    simp only [seriesValue, order_mul x.ne_zero y.ne_zero, leadingCoeff_mul,
      order_mul (leadingCoeff_ne_zero.mpr x.ne_zero) (leadingCoeff_ne_zero.mpr y.ne_zero)]
    rfl

private theorem seriesValue_add_eq_left {x y : IteratedLaurent k}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) (h : x.order < y.order) :
    seriesValue (x + y) = seriesValue x := by
  have ht : x.orderTop < y.orderTop := by
    rw [← order_eq_orderTop_of_ne_zero hx, ← order_eq_orderTop_of_ne_zero hy]
    exact WithTop.coe_lt_coe.mpr h
  have ho : (x + y).order = x.order := by
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero hxy, order_eq_orderTop_of_ne_zero hx,
      orderTop_add_eq_left ht]
  simp only [seriesValue, ho, leadingCoeff_add_eq_left ht]

theorem lexValuation_inequality : AddValuationInequality (lexValuation k) := by
  intro a b hab
  let x : IteratedLaurent k := a
  let y : IteratedLaurent k := b
  change min (seriesValue x) (seriesValue y) ≤ seriesValue (x + y)
  rcases lt_trichotomy x.order y.order with h | h | h
  · rw [seriesValue_add_eq_left k a.ne_zero b.ne_zero hab h]
    exact min_le_left _ _
  · have ho := min_order_le_order_add hab
    change min x.order y.order ≤ (x + y).order at ho
    rw [h, min_self] at ho
    rcases ho.eq_or_lt with hs | hs
    · have hc : (x + y).leadingCoeff = x.leadingCoeff + y.leadingCoeff := by
        rw [leadingCoeff_eq, ← hs, coeff_add, ← h]
        rw [← leadingCoeff_eq, h, ← leadingCoeff_eq]
      have hmin := min_order_le_order_add (x := x.leadingCoeff) (y := y.leadingCoeff)
        (hc ▸ leadingCoeff_ne_zero.mpr hab)
      rcases le_total x.leadingCoeff.order y.leadingCoeff.order with hl | hr
      · rw [min_eq_left hl] at hmin
        refine (min_le_left _ _).trans (Prod.Lex.le_iff.mpr (Or.inr ⟨h.trans hs, ?_⟩))
        change x.leadingCoeff.order ≤ (x + y).leadingCoeff.order
        rwa [hc]
      · rw [min_eq_right hr] at hmin
        refine (min_le_right _ _).trans (Prod.Lex.le_iff.mpr (Or.inr ⟨hs, ?_⟩))
        change y.leadingCoeff.order ≤ (x + y).leadingCoeff.order
        rwa [hc]
    · exact (min_le_right _ _).trans (Prod.Lex.le_iff.mpr (Or.inl hs))
  · have hh : y + x ≠ 0 := by simpa [add_comm] using hab
    rw [add_comm x y, seriesValue_add_eq_left k b.ne_zero a.ne_zero hh h]
    exact min_le_right _ _

theorem lexValuation_surjective : Function.Surjective (lexValuation k) := by
  intro g
  let c : LaurentSeries k := single (ofLex g).2 1
  have hc : c ≠ 0 := single_ne_zero one_ne_zero
  let f : IteratedLaurent k := single (ofLex g).1 c
  refine ⟨ofMul (Units.mk0 f (single_ne_zero hc)), ?_⟩
  change seriesValue f = g
  simp [seriesValue, f, c, order_single hc]

theorem series_valuation :
    Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation.SeriesValuation :=
  fun k _ ↦ ⟨lexValuation k, fun _ ↦ rfl, lexValuation_inequality k, lexValuation_surjective k⟩

end Valuation

section ConvexSubgroups

private def bottomConvex (Γ : Type*) [AddGroup Γ] [PartialOrder Γ] :
    ConvexAddSubgroup Γ :=
  ⟨⊥, by
    intro a b c ha hc hab hbc
    rw [AddSubgroup.mem_bot] at ha hc ⊢
    exact le_antisymm (hc ▸ hbc) (ha ▸ hab)⟩

private def topConvex (Γ : Type*) [AddGroup Γ] [Preorder Γ] :
    ConvexAddSubgroup Γ :=
  ⟨⊤, by
    intro a b c _ _ _ _
    exact AddSubgroup.mem_top b⟩

private theorem vertical_ne_bot : vertical.1 ≠ ⊥ := by
  intro h
  have hm := (mem_vertical (toLex (0, 1))).mpr rfl
  rw [h, AddSubgroup.mem_bot] at hm
  have := congrArg (fun g : LexIntegers ↦ (ofLex g).2) hm
  norm_num at this

private theorem vertical_ne_top : vertical.1 ≠ ⊤ := by
  intro h
  have hm : toLex ((1 : ℤ), (0 : ℤ)) ∈ vertical.1 := h ▸ AddSubgroup.mem_top _
  have := (mem_vertical _).mp hm
  change (1 : ℤ) = 0 at this
  omega

private theorem top_of_first_nonzero (H : ConvexAddSubgroup LexIntegers)
    {g : LexIntegers} (hg : g ∈ H.1) (h : (ofLex g).1 ≠ 0) : H.1 = ⊤ := by
  have ⟨p, hp, hp'⟩ : ∃ p : LexIntegers, p ∈ H.1 ∧ 0 < (ofLex p).1 := by
    rcases lt_or_gt_of_ne h with hl | hr
    · exact ⟨-g, H.1.neg_mem hg, by change 0 < -(ofLex g).1; omega⟩
    · exact ⟨g, hg, hr⟩
  have hone : toLex ((1 : ℤ), (0 : ℤ)) ∈ H.1 := by
    refine H.2 H.1.zero_mem (H.1.add_mem hp hp)
      (Prod.Lex.le_iff.mpr (Or.inl (by decide))) (Prod.Lex.le_iff.mpr (Or.inl ?_))
    change 1 < (ofLex p).1 + (ofLex p).1
    omega
  apply top_unique
  intro z _
  let n := |(ofLex z).1| + 1
  refine H.2 (H.1.zsmul_mem hone (-n)) (H.1.zsmul_mem hone n)
    (Prod.Lex.le_iff.mpr (Or.inl ?_)) (Prod.Lex.le_iff.mpr (Or.inl ?_))
  · change (-n) • (1 : ℤ) < (ofLex z).1
    simpa [n, zsmul_eq_mul] using (show -(|(ofLex z).1| + 1) < (ofLex z).1 by
      have := neg_abs_le (ofLex z).1
      omega)
  · change (ofLex z).1 < n • (1 : ℤ)
    simpa [n, zsmul_eq_mul] using (show (ofLex z).1 < |(ofLex z).1| + 1 by
      have := le_abs_self (ofLex z).1
      omega)

private theorem vertical_le_of_nonzero (H : ConvexAddSubgroup LexIntegers) {g : LexIntegers}
    (hg : g ∈ H.1) (h₁ : (ofLex g).1 = 0) (h₂ : g ≠ 0) : vertical.1 ≤ H.1 := by
  have hn : (ofLex g).2 ≠ 0 := by
    intro hn
    exact h₂ (Prod.ext h₁ hn)
  have ⟨p, hp, hp₁, hp₂⟩ : ∃ p : LexIntegers, p ∈ H.1 ∧ (ofLex p).1 = 0 ∧
      0 < (ofLex p).2 := by
    rcases lt_or_gt_of_ne hn with hl | hr
    · refine ⟨-g, H.1.neg_mem hg, ?_, ?_⟩
      · change -(ofLex g).1 = 0
        simp [h₁]
      · change 0 < -(ofLex g).2
        omega
    · exact ⟨g, hg, h₁, hr⟩
  have hone : toLex ((0 : ℤ), (1 : ℤ)) ∈ H.1 := by
    refine H.2 H.1.zero_mem hp (Prod.Lex.le_iff.mpr (Or.inr ⟨rfl, by decide⟩))
      (Prod.Lex.le_iff.mpr (Or.inr ⟨hp₁.symm, ?_⟩))
    change 1 ≤ (ofLex p).2
    omega
  intro z hz
  have h : (ofLex z).2 • toLex ((0 : ℤ), (1 : ℤ)) = z := by
    apply Prod.ext
    · change (ofLex z).2 • (0 : ℤ) = (ofLex z).1
      simp [(mem_vertical _).mp hz]
    · change (ofLex z).2 • (1 : ℤ) = (ofLex z).2
      simp
  rw [← h]
  exact H.1.zsmul_mem hone _

theorem convex_subgroups :
    Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation.ConvexSubgroups := by
  refine ⟨vertical_ne_bot, vertical_ne_top, fun H ↦ ?_⟩
  by_cases ht : H.1 = ⊤
  · exact Or.inr (Or.inr ht)
  by_cases hb : H.1 = ⊥
  · exact Or.inl hb
  have hv : H.1 ≤ vertical.1 := fun g hg ↦
    (mem_vertical g).mpr (by
      by_contra hn
      exact ht (top_of_first_nonzero H hg hn))
  obtain ⟨g, hg, hn⟩ : ∃ g : LexIntegers, g ∈ H.1 ∧ g ≠ 0 := by
    by_contra! h
    exact hb (le_bot_iff.mp (fun g hg ↦ AddSubgroup.mem_bot.mpr (h g hg)))
  exact Or.inr (Or.inl (Subtype.ext (le_antisymm hv
    (vertical_le_of_nonzero H hg ((mem_vertical g).mp (hv hg)) hn))))

private def convexComap {Γ Δ : Type*} [AddCommGroup Γ] [AddCommGroup Δ]
    [PartialOrder Γ] [PartialOrder Δ] (e : Γ ≃+o Δ) (H : ConvexAddSubgroup Δ) :
    ConvexAddSubgroup Γ :=
  ⟨H.1.comap e.toAddMonoidHom, by
    intro a b c ha hc hab hbc
    exact H.2 ha hc (e.toOrderIso.monotone hab) (e.toOrderIso.monotone hbc)⟩

private def convexOrderIso {Γ Δ : Type*} [AddCommGroup Γ] [AddCommGroup Δ]
    [PartialOrder Γ] [PartialOrder Δ] (e : Γ ≃+o Δ) :
    ConvexAddSubgroup Γ ≃o ConvexAddSubgroup Δ where
  toFun := convexComap e.symm
  invFun := convexComap e
  left_inv H := Subtype.ext (AddSubgroup.ext (fun x ↦ by
    change e.symm (e x) ∈ H.1 ↔ x ∈ H.1
    rw [e.symm_apply_apply]))
  right_inv H := Subtype.ext (AddSubgroup.ext (fun x ↦ by
    change e (e.symm x) ∈ H.1 ↔ x ∈ H.1
    rw [e.apply_symm_apply]))
  map_rel_iff' {H J} := by
    change (∀ x : Δ, e.symm x ∈ H.1 → e.symm x ∈ J.1) ↔ H.1 ≤ J.1
    constructor
    · intro h x hx
      have hx' : e.symm (e x) ∈ H.1 := by simpa only [e.symm_apply_apply] using hx
      simpa only [e.symm_apply_apply] using h (e x) hx'
    · exact fun h _ hx ↦ h hx

private theorem lex_krullDim : Order.krullDim (ConvexAddSubgroup LexIntegers) = 2 := by
  classical
  let B := bottomConvex LexIntegers
  let T := topConvex LexIntegers
  let enumerate : Fin 3 → ConvexAddSubgroup LexIntegers := ![B, vertical, T]
  have hsurj : Function.Surjective enumerate := by
    intro H
    rcases convex_subgroups.2.2 H with hb | hv | ht
    · exact ⟨0, Subtype.ext hb.symm⟩
    · exact ⟨1, hv.symm⟩
    · exact ⟨2, Subtype.ext ht.symm⟩
  let := Fintype.ofSurjective enumerate hsurj
  have hcard := Fintype.card_le_of_surjective enumerate hsurj
  rw [Fintype.card_fin] at hcard
  have hBV : B < vertical := lt_of_le_of_ne (show B.1 ≤ vertical.1 from bot_le) (fun h ↦
    vertical_ne_bot (congrArg Subtype.val h).symm)
  have hVT : vertical < T := lt_of_le_of_ne (show vertical.1 ≤ T.1 from le_top) (fun h ↦
    vertical_ne_top (congrArg Subtype.val h))
  let s : LTSeries (ConvexAddSubgroup LexIntegers) :=
    { length := 2
      toFun := enumerate
      step i := by fin_cases i <;> assumption }
  refine le_antisymm ?_ (by simpa [s] using Order.LTSeries.length_le_krullDim s)
  change (⨆ c : LTSeries (ConvexAddSubgroup LexIntegers), (c.length : WithBot ℕ∞)) ≤ 2
  refine iSup_le fun c ↦ ?_
  have hlen := c.length_lt_card
  have htwo : c.length ≤ 2 := by omega
  exact_mod_cast htwo

private theorem int_convex_eq_bot_or_top (H : ConvexAddSubgroup ℤ) : H.1 = ⊥ ∨ H.1 = ⊤ := by
  by_cases hb : H.1 = ⊥
  · exact Or.inl hb
  have ⟨j, hj, hn⟩ : ∃ j : ℤ, j ∈ H.1 ∧ j ≠ 0 := by
    by_contra! h
    exact hb (le_bot_iff.mp (fun j hj ↦ AddSubgroup.mem_bot.mpr (h j hj)))
  have hp : |j| ∈ H.1 := by
    rcases le_total 0 j with h | h
    · simpa only [abs_of_nonneg h] using hj
    · simpa only [abs_of_nonpos h] using H.1.neg_mem hj
  have hone : (1 : ℤ) ∈ H.1 := H.2 H.1.zero_mem hp (by decide)
    (by have := abs_pos.mpr hn; omega)
  exact Or.inr (top_unique fun j _ ↦ by simpa [zsmul_eq_mul] using H.1.zsmul_mem hone j)

private theorem lex_not_int (e : LexIntegers ≃+o ℤ) : False := by
  rcases int_convex_eq_bot_or_top (convexComap e.symm vertical) with h | h
  · apply vertical_ne_bot
    apply le_bot_iff.mp
    intro x hx
    have hm : e x ∈ (convexComap e.symm vertical).1 := by
      change e.symm (e x) ∈ vertical.1
      simpa only [e.symm_apply_apply] using hx
    rw [h, AddSubgroup.mem_bot] at hm
    exact AddSubgroup.mem_bot.mpr (e.injective (hm.trans (map_zero e).symm))
  · apply vertical_ne_top
    apply top_unique
    intro x _
    have hm : e x ∈ (convexComap e.symm vertical).1 := h ▸ AddSubgroup.mem_top _
    change e.symm (e x) ∈ vertical.1 at hm
    simpa only [e.symm_apply_apply] using hm

end ConvexSubgroups

section Realization

private theorem ordered_image_of_surjective
    {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    (f : Additive Kˣ →+ Γ) (hf : AddValuationInequality f) (hs : Function.Surjective f) :
    ∃ e : ValueGroup (valuationSubring f hf) ≃+o Γ,
      ∀ a : Additive Kˣ, e (value (valuationSubring f hf) a) = f a := by
  obtain ⟨e, he⟩ := ordered_image f hf
  let i : f.range ≃+o Γ :=
    { AddEquiv.ofBijective f.range.subtype ⟨Subtype.val_injective, by
        intro g
        obtain ⟨a, rfl⟩ := hs g
        exact ⟨f.rangeRestrict a, rfl⟩⟩ with map_le_map_iff' := Iff.rfl }
  exact ⟨e.trans i, fun a ↦ congrArg Subtype.val (he a)⟩

variable (k : Type u) [Field k]

/-- The subring of the iterated Laurent field defined by the nonnegative pairs. -/
def valuationRing : ValuationSubring (IteratedLaurent k) :=
  valuationSubring (lexValuation k) (lexValuation_inequality k)

theorem mem_valuationRing_iff (x : IteratedLaurent k) :
    x ∈ valuationRing k ↔ x = 0 ∨ 0 ≤ seriesValue x := by
  rw [valuationRing, mem_valuationSubring_iff]
  by_cases hx : x = 0 <;> simp [hx, lexValuation]

theorem valueGroup_equiv :
    ∃ e : ValueGroup (valuationRing k) ≃+o LexIntegers,
      ∀ a : Additive (IteratedLaurent k)ˣ, e (value (valuationRing k) a) = lexValuation k a :=
  ordered_image_of_surjective _ (lexValuation_inequality k) (lexValuation_surjective k)

theorem ringKrullDim_valuationRing : ringKrullDim (valuationRing k) = 2 := by
  obtain ⟨e, _⟩ := valueGroup_equiv k
  exact (ValuationPrimesAndConvexSubgroups.rank_eq_krullDim_convexAddSubgroups _).trans
    ((Order.krullDim_eq_of_orderIso (convexOrderIso e)).trans lex_krullDim)

theorem not_isNoetherianRing_valuationRing : ¬ IsNoetherianRing (valuationRing k) := by
  intro h
  obtain ⟨e, _⟩ := valueGroup_equiv k
  rcases (NoetherianValuationRings.noetherian_iff (valuationRing k)).mp h with hf | hi
  · have := (NoetherianValuationRings.isField_iff_subsingleton_valueGroup _).mp hf
    have heq : (toLex ((1 : ℤ), (0 : ℤ)) : LexIntegers) = 0 :=
      e.symm.injective (Subsingleton.elim _ _)
    have hcoord := congrArg (fun g : LexIntegers ↦ (ofLex g).1) heq
    change (1 : ℤ) = 0 at hcoord
    omega
  · obtain ⟨ei⟩ := hi
    exact lex_not_int (e.symm.trans ei)

end Realization

section Adic

variable (k : Type u) [Field k]

private def orderValuation {F : Type*} [Field F] (r : F ≃+* LaurentSeries k) :
    Additive Fˣ →+ ℤ where
  toFun a := (r (↑(toMul a) : F)).order
  map_zero' := by change (r 1).order = 0; rw [map_one, order_one]
  map_add' a b := by
    let x : Fˣ := toMul a
    let y : Fˣ := toMul b
    change (r ((x : F) * (y : F))).order = (r (x : F)).order + (r (y : F)).order
    rw [map_mul, order_mul ((map_ne_zero r).mpr x.ne_zero) ((map_ne_zero r).mpr y.ne_zero)]

private theorem orderValuation_inequality {F : Type*} [Field F] (r : F ≃+* LaurentSeries k) :
    AddValuationInequality (orderValuation k r) := by
  intro a b h
  change min (r (a : F)).order (r (b : F)).order ≤ (r ((a : F) + (b : F))).order
  rw [map_add]
  apply min_order_le_order_add
  rw [← map_add]
  exact (map_ne_zero r).mpr h

private theorem orderValuation_surjective {F : Type*} [Field F] (r : F ≃+* LaurentSeries k) :
    Function.Surjective (orderValuation k r) := by
  intro n
  let x : LaurentSeries k := single n 1
  have hx : x ≠ 0 := single_ne_zero one_ne_zero
  refine ⟨ofMul (Units.mk0 (r.symm x) ((map_ne_zero r.symm).mpr hx)), ?_⟩
  change (r (r.symm x)).order = n
  rw [r.apply_symm_apply]
  exact order_single one_ne_zero

private theorem adic_mem_iff (x : LaurentSeries k) : x ∈ adicSubring k ↔ 0 ≤ x.order := by
  by_cases hx : x = 0
  · simp [hx]
  rw [HahnSeries.le_order_iff_forall hx]
  change Valued.v x ≤ (1 : ℤᵐ⁰) ↔ _
  simpa using (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero k (f := x) (D := 0))

private theorem mem_transported_adic {F : Type*} [Field F] (r : F ≃+* LaurentSeries k)
    (x : F) :
    x ∈ valuationSubring (orderValuation k r) (orderValuation_inequality k r) ↔
      r x ∈ adicSubring k := by
  rw [adic_mem_iff, mem_valuationSubring_iff]
  by_cases hx : x = 0 <;> simp [hx, orderValuation]

private theorem transported_adic_valueGroup {F : Type*} [Field F]
    (r : F ≃+* LaurentSeries k) :
    ∃ W : ValuationSubring F, (∀ x, x ∈ W ↔ r x ∈ adicSubring k) ∧
      ∃ e : ValueGroup W ≃+o ℤ, ∀ a : Fˣ, e (value W (ofMul a)) = (r (a : F)).order := by
  obtain ⟨e, he⟩ := ordered_image_of_surjective _ (orderValuation_inequality k r)
    (orderValuation_surjective k r)
  exact ⟨_, mem_transported_adic k r, e, fun a ↦ he (ofMul a)⟩

private theorem adic_valueGroup :
    ∃ e : ValueGroup (adicSubring k) ≃+o ℤ,
      ∀ a : (LaurentSeries k)ˣ, e (value (adicSubring k) (ofMul a)) =
        (a : LaurentSeries k).order := by
  obtain ⟨W, hW, e, he⟩ := transported_adic_valueGroup k (RingEquiv.refl (LaurentSeries k))
  have h : W = adicSubring k := ValuationSubring.ext _ _ hW
  subst W
  exact ⟨e, he⟩

private theorem coeff_zero_eq_leading {x : LaurentSeries k} (h : x.order = 0) :
    x.coeff 0 = x.leadingCoeff := by rw [leadingCoeff_eq, h]

private theorem coeff_zero_eq_zero_iff_pos {x : LaurentSeries k}
    (hx : x ≠ 0) (ho : 0 ≤ x.order) : x.coeff 0 = 0 ↔ 0 < x.order := by
  refine ⟨fun h ↦ ?_, coeff_eq_zero_of_lt_order⟩
  rcases ho.eq_or_lt with he | hp
  · exact False.elim ((leadingCoeff_ne_zero.mpr hx) ((coeff_zero_eq_leading k he.symm).symm.trans h))
  · exact hp

/-- The constant coefficient on the adic valuation ring. -/
def adicResidue : adicSubring k →+* k where
  toFun x := (x : LaurentSeries k).coeff 0
  map_zero' := coeff_zero
  map_one' := by change (1 : LaurentSeries k).coeff 0 = 1; simp
  map_add' _ _ := coeff_add
  map_mul' a b := by
    let x : LaurentSeries k := a
    let y : LaurentSeries k := b
    change (x * y).coeff 0 = x.coeff 0 * y.coeff 0
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hxo := (adic_mem_iff k x).mp a.property
    have hyo := (adic_mem_iff k y).mp b.property
    by_cases hsum : x.order + y.order = 0
    · have hx0 : x.order = 0 := by omega
      have hy0 : y.order = 0 := by omega
      simpa only [hsum, ← coeff_zero_eq_leading k hx0, ← coeff_zero_eq_leading k hy0]
        using coeff_mul_order_add_order x y
    · have hp : 0 < (x * y).order := by rw [order_mul hx hy]; omega
      rw [coeff_eq_zero_of_lt_order hp]
      rcases lt_or_ge 0 x.order with h | h
      · rw [coeff_eq_zero_of_lt_order h, zero_mul]
      · have hp' : 0 < y.order := by omega
        rw [coeff_eq_zero_of_lt_order hp', mul_zero]

private theorem adicResidue_surjective : Function.Surjective (adicResidue k) := by
  intro a
  refine ⟨⟨single 0 a, (adic_mem_iff k _).mpr ?_⟩, coeff_single_same 0 a⟩
  by_cases ha : a = 0 <;> simp [ha]

private theorem adicResidue_ker :
    RingHom.ker (adicResidue k) = IsLocalRing.maximalIdeal (adicSubring k) :=
  IsLocalRing.ker_eq_maximalIdeal _ (adicResidue_surjective k)

end Adic

section Composition

variable (k : Type u) [Field k]

theorem valuationRing_le_adic : valuationRing k ≤ adicSubring (LaurentSeries k) := by
  intro x hx
  rw [adic_mem_iff]
  rcases (mem_valuationRing_iff k x).mp hx with rfl | h
  · simp
  · exact Prod.Lex.monotone_fst 0 (seriesValue x) h

/-- The prime cut out by the maximal ideal of the outer adic valuation ring. -/
def coarseningPrime : PrimeSpectrum (valuationRing k) :=
  ⟨ValuationSubring.idealOfLE _ _ (valuationRing_le_adic k), inferInstance⟩

theorem localization_eq_adic :
    (valuationRing k).ofPrime (coarseningPrime k).asIdeal = adicSubring (LaurentSeries k) :=
  ValuationSubring.ofPrime_idealOfLE _ _ (valuationRing_le_adic k)

private def outerResidue : valuationRing k →+* LaurentSeries k :=
  (adicResidue (LaurentSeries k)).comp
    ((valuationRing k).inclusion _ (valuationRing_le_adic k))

theorem mem_coarseningPrime_iff (a : valuationRing k) :
    a ∈ (coarseningPrime k).asIdeal ↔ (a : IteratedLaurent k).coeff 0 = 0 := by
  change (valuationRing k).inclusion _ (valuationRing_le_adic k) a ∈
    IsLocalRing.maximalIdeal (adicSubring (LaurentSeries k)) ↔ _
  rw [← adicResidue_ker (LaurentSeries k)]
  rfl

private theorem outerResidue_mem_adic (a : valuationRing k) :
    outerResidue k a ∈ adicSubring k := by
  let x : IteratedLaurent k := a
  change x.coeff 0 ∈ adicSubring k
  have hv := (mem_valuationRing_iff k x).mp a.property
  rcases hv with hzero | h
  · simp [hzero]
  rw [adic_mem_iff]
  rcases Prod.Lex.le_iff.mp h with h | h
  · change 0 < x.order at h
    simp [coeff_eq_zero_of_lt_order h]
  · have ho : x.order = 0 := h.1.symm
    rw [coeff_zero_eq_leading (LaurentSeries k) ho]
    exact h.2

theorem mem_valuationRing_iff_adic (x : IteratedLaurent k) :
    x ∈ valuationRing k ↔ x ∈ adicSubring (LaurentSeries k) ∧ x.coeff 0 ∈ adicSubring k := by
  refine ⟨fun hx ↦ ⟨valuationRing_le_adic k hx, outerResidue_mem_adic k ⟨x, hx⟩⟩, ?_⟩
  rintro ⟨hy, hx⟩
  rw [mem_valuationRing_iff]
  right
  apply Prod.Lex.le_iff.mpr
  rcases ((adic_mem_iff (LaurentSeries k) x).mp hy).eq_or_lt with h | h
  · right
    refine ⟨h, ?_⟩
    change 0 ≤ x.leadingCoeff.order
    rw [← coeff_zero_eq_leading (LaurentSeries k) h.symm]
    exact (adic_mem_iff k _).mp hx
  · exact Or.inl h

private theorem exists_outerResidue_eq {a : LaurentSeries k} (ha : a ∈ adicSubring k) :
    ∃ x : valuationRing k, outerResidue k x = a := by
  by_cases hzero : a = 0
  · exact ⟨0, (map_zero _).trans hzero.symm⟩
  refine ⟨⟨single 0 a, (mem_valuationRing_iff k _).mpr (Or.inr ?_)⟩, coeff_single_same 0 a⟩
  apply Prod.Lex.le_iff.mpr
  right
  change (0 : ℤ) = (single (0 : ℤ) a).order ∧ 0 ≤ (single (0 : ℤ) a).leadingCoeff.order
  rw [order_single hzero, leadingCoeff_of_single]
  exact ⟨rfl, (adic_mem_iff k a).mp ha⟩

private def residueToLaurent : (coarseningPrime k).asIdeal.ResidueField →+* LaurentSeries k :=
  Ideal.ResidueField.lift _ (outerResidue k)
    (fun _ hx ↦ (mem_coarseningPrime_iff k _).mp hx)
    (fun _ hx ↦ (show IsUnit (outerResidue k _) from
      (show outerResidue k _ ≠ 0 from fun h ↦ hx ((mem_coarseningPrime_iff k _).mpr h)).isUnit))

private theorem residueToLaurent_apply (a : valuationRing k) :
    residueToLaurent k (residueMap (valuationRing k) (coarseningPrime k) a) =
      outerResidue k a :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ a

private theorem residueToLaurent_surjective : Function.Surjective (residueToLaurent k) := by
  intro a
  rcases (adicSubring k).mem_or_inv_mem a with ha | ha
  · obtain ⟨x, hx⟩ := exists_outerResidue_eq k ha
    exact ⟨residueMap _ _ x, (residueToLaurent_apply k x).trans hx⟩
  · obtain ⟨x, hx⟩ := exists_outerResidue_eq k ha
    refine ⟨(residueMap _ _ x)⁻¹, ?_⟩
    rw [map_inv₀, residueToLaurent_apply, hx, inv_inv]

/-- The prime residue field is the inner Laurent field, via the outer constant coefficient. -/
def residueEquiv : (coarseningPrime k).asIdeal.ResidueField ≃+* LaurentSeries k :=
  RingEquiv.ofBijective (residueToLaurent k)
    ⟨(residueToLaurent k).injective, residueToLaurent_surjective k⟩

theorem localization_and_residue : IsLocalizationAndResidue k (valuationRing k) (coarseningPrime k) := by
  have hrange (z : (coarseningPrime k).asIdeal.ResidueField) :
      z ∈ (residueMap (valuationRing k) (coarseningPrime k)).range ↔
        residueEquiv k z ∈ adicSubring k := by
    constructor
    · rintro ⟨a, rfl⟩
      change residueToLaurent k (residueMap _ _ a) ∈ adicSubring k
      rw [residueToLaurent_apply]
      exact outerResidue_mem_adic k a
    · intro hz
      obtain ⟨a, ha⟩ := exists_outerResidue_eq k hz
      refine ⟨a, (residueEquiv k).injective ?_⟩
      exact (residueToLaurent_apply k a).trans ha
  refine ⟨localization_eq_adic k, mem_valuationRing_iff_adic k, ?_,
    residueEquiv k, residueToLaurent_apply k, hrange, ?_, ?_⟩
  · rw [localization_eq_adic k]
    exact adic_valueGroup (LaurentSeries k)
  · intro a ha
    change (residueToLaurent k (residueMap _ _ a)).order = (a : IteratedLaurent k).leadingCoeff.order
    rw [residueToLaurent_apply]
    let x : IteratedLaurent k := a
    change (x.coeff 0).order = x.leadingCoeff.order
    have hc : x.coeff 0 ≠ 0 := fun h ↦ ha ((mem_coarseningPrime_iff k a).mpr h)
    have ho := (adic_mem_iff (LaurentSeries k) x).mp (valuationRing_le_adic k a.property)
    rw [coeff_zero_eq_leading (LaurentSeries k) (le_antisymm (order_le_of_coeff_ne_zero hc) ho)]
  · obtain ⟨W, hW, e, he⟩ := transported_adic_valueGroup k (residueEquiv k)
    exact ⟨W, fun z ↦ (hW z).trans (hrange z).symm, e, he⟩

private theorem outside_prime_iff_outer_order_zero (a : valuationRing k) (ha : a ≠ 0) :
    a ∉ (coarseningPrime k).asIdeal ↔ (a : IteratedLaurent k).order = 0 := by
  let x : IteratedLaurent k := a
  have hx : x ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have ho : 0 ≤ x.order := (adic_mem_iff (LaurentSeries k) x).mp
    (valuationRing_le_adic k a.property)
  change ¬a ∈ (coarseningPrime k).asIdeal ↔ x.order = 0
  rw [mem_coarseningPrime_iff, coeff_zero_eq_zero_iff_pos (LaurentSeries k) hx ho, not_lt]
  exact ⟨fun h ↦ le_antisymm h ho, le_of_eq⟩

theorem coarseningPrime_associated (e : ValueGroup (valuationRing k) ≃+o LexIntegers)
    (he : ∀ a : Additive (IteratedLaurent k)ˣ, e (value (valuationRing k) a) = lexValuation k a)
    (g : ValueGroup (valuationRing k)) (hg : 0 ≤ g) :
    e g ∈ vertical.1 ↔ PrimeValues (valuationRing k) (coarseningPrime k) g := by
  constructor
  · intro hm
    obtain ⟨a, rfl⟩ := value_surjective (valuationRing k) g
    let u := toMul a
    have hu : (u : IteratedLaurent k) ∈ valuationRing k :=
      (value_nonneg_iff (valuationRing k) u).mp hg
    let x : valuationRing k := ⟨u, hu⟩
    have hx : x ≠ 0 := fun h ↦ u.ne_zero (congrArg Subtype.val h)
    refine ⟨x, hx, (outside_prime_iff_outer_order_zero k x hx).mpr ?_, ?_⟩
    · rw [he] at hm
      exact (mem_vertical _).mp hm
    · change value (valuationRing k) (ofMul _) = _
      congr 1
      exact Units.ext rfl
  · rintro ⟨x, hx, hP, rfl⟩
    rw [mem_vertical]
    unfold ringValue
    rw [he]
    exact (outside_prime_iff_outer_order_zero k x hx).mp hP

theorem laurent_example : Specs.CommutativeAlgebraNotes.LexicographicLaurentValuation.LaurentExample := by
  intro k _
  obtain ⟨e, he⟩ := valueGroup_equiv k
  exact ⟨lexValuation k, valuationRing k, coarseningPrime k,
    ⟨fun _ ↦ rfl, lexValuation_inequality k, lexValuation_surjective k⟩,
    mem_valuationRing_iff k, ⟨e, he, coarseningPrime_associated k e he⟩,
    localization_and_residue k, ringKrullDim_valuationRing k,
    not_isNoetherianRing_valuationRing k⟩

end Composition

end CommutativeAlgebraNotes.LexicographicLaurentValuation
