import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.OrderedValuationGroups
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
import Mathlib.Algebra.Order.Group.Abs

noncomputable section

namespace CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups

open Additive (ofMul toMul)
open OrderedValuationGroups (ValueGroup value value_surjective value_nonneg_iff
  value_le_iff_div_mem value_add_ge_min)
open Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups (PrimeValues ringValue)

universe u

/-- Convex additive subgroups ordered by inclusion. -/
abbrev ConvexAddSubgroup (Γ : Type u) [AddGroup Γ] [Preorder Γ] :=
  Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups.convexAddSubgroup Γ

namespace ConvexAddSubgroup

variable {Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem le_of_nonneg {H J : ConvexAddSubgroup Γ}
    (h : ∀ ⦃g : Γ⦄, 0 ≤ g → g ∈ H.1 → g ∈ J.1) : H ≤ J := by
  intro g hg
  obtain hg₀ | hg₀ := le_total 0 g
  · exact h hg₀ hg
  · simpa only [neg_neg] using J.1.neg_mem (h (neg_nonneg.mpr hg₀) (H.1.neg_mem hg))

omit [IsOrderedAddMonoid Γ] in
theorem mem_of_nonneg_of_le (H : ConvexAddSubgroup Γ) {a b : Γ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ H.1) : a ∈ H.1 :=
  H.2 H.1.zero_mem hb ha hab

end ConvexAddSubgroup

variable {K : Type u} [Field K] (V : ValuationSubring K)

private theorem coe_ne_zero {x : V} (hx : x ≠ 0) : (x : K) ≠ 0 :=
  fun h ↦ hx (Subtype.ext h)

theorem ringValue_nonneg (x : V) (hx : x ≠ 0) : 0 ≤ ringValue V x hx :=
  (value_nonneg_iff V _).mpr x.property

private theorem ringValue_one : ringValue V 1 one_ne_zero = 0 := by
  have h : Units.mk0 ((1 : V) : K) (coe_ne_zero V one_ne_zero) = 1 :=
    Units.ext rfl
  change value V (ofMul (Units.mk0 ((1 : V) : K) (coe_ne_zero V one_ne_zero))) = 0
  rw [h]
  exact map_zero (value V)

private theorem ringValue_mul {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ringValue V (x * y) (mul_ne_zero hx hy) = ringValue V x hx + ringValue V y hy := by
  let a := Units.mk0 (x : K) (coe_ne_zero V hx)
  let b := Units.mk0 (y : K) (coe_ne_zero V hy)
  have h : Units.mk0 ((x * y : V) : K) (coe_ne_zero V (mul_ne_zero hx hy)) = a * b :=
    Units.ext rfl
  change value V (ofMul (Units.mk0 ((x * y : V) : K)
    (coe_ne_zero V (mul_ne_zero hx hy)))) = value V (ofMul a) + value V (ofMul b)
  rw [h]
  exact map_add (value V) (ofMul a) (ofMul b)

private theorem ringValue_add_ge_min {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) :
    min (ringValue V x hx) (ringValue V y hy) ≤ ringValue V (x + y) hxy :=
  value_add_ge_min V (Units.mk0 (x : K) (coe_ne_zero V hx))
    (Units.mk0 (y : K) (coe_ne_zero V hy)) (coe_ne_zero V hxy)

theorem exists_ringValue_of_nonneg {g : ValueGroup V} (hg : 0 ≤ g) :
    ∃ (x : V) (hx : x ≠ 0), ringValue V x hx = g := by
  obtain ⟨a, rfl⟩ := value_surjective V g
  let b : Kˣ := toMul a
  let x : V := ⟨(b : K), (value_nonneg_iff V b).mp hg⟩
  have hx : x ≠ 0 := fun h ↦ b.ne_zero (congrArg Subtype.val h)
  refine ⟨x, hx, ?_⟩
  change value V (ofMul (Units.mk0 (b : K) (coe_ne_zero V hx))) = value V (ofMul b)
  exact congrArg (fun c ↦ value V (ofMul c)) (Units.ext rfl)

private theorem dvd_of_ringValue_le {a b : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ringValue V a ha ≤ ringValue V b hb) : a ∣ b := by
  have hdiv : (b : K) / (a : K) ∈ V :=
    (value_le_iff_div_mem V (Units.mk0 (b : K) (coe_ne_zero V hb))
      (Units.mk0 (a : K) (coe_ne_zero V ha))).mp h
  refine ⟨⟨_, hdiv⟩, Subtype.ext ?_⟩
  change (b : K) = (a : K) * ((b : K) / (a : K))
  rw [mul_comm, div_mul_cancel₀ _ (coe_ne_zero V ha)]

variable (P : PrimeSpectrum V)

private theorem primeValues_downward {a b : ValueGroup V}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : PrimeValues V P b) : PrimeValues V P a := by
  obtain ⟨x, hx, hxP, rfl⟩ := hb
  obtain ⟨y, hy, rfl⟩ := exists_ringValue_of_nonneg V ha
  exact ⟨y, hy, fun hyP ↦ hxP (P.asIdeal.mem_of_dvd (dvd_of_ringValue_le V hy hx hab) hyP), rfl⟩

private theorem primeValues_add {a b : ValueGroup V}
    (ha : PrimeValues V P a) (hb : PrimeValues V P b) : PrimeValues V P (a + b) := by
  obtain ⟨x, hx, hxP, rfl⟩ := ha
  obtain ⟨y, hy, hyP, rfl⟩ := hb
  exact ⟨x * y, mul_ne_zero hx hy, P.isPrime.mul_notMem hxP hyP, ringValue_mul V hx hy⟩

private theorem primeValues_ringValue_iff (x : V) (hx : x ≠ 0) :
    PrimeValues V P (ringValue V x hx) ↔ x ∉ P.asIdeal := by
  constructor
  · rintro ⟨y, hy, hyP, he⟩ hxP
    exact hyP (P.asIdeal.mem_of_dvd (dvd_of_ringValue_le V hx hy he.ge) hxP)
  · exact fun hxP ↦ ⟨x, hx, hxP, rfl⟩

/-- The convex subgroup whose nonnegative part consists of the values outside a prime. -/
def primeToConvex : ConvexAddSubgroup (ValueGroup V) := by
  let H : AddSubgroup (ValueGroup V) :=
    { carrier := {g | PrimeValues V P |g|}
      zero_mem' := by
        change PrimeValues V P |0|
        rw [abs_zero]
        exact ⟨1, one_ne_zero, P.isPrime.one_notMem, ringValue_one V⟩
      add_mem' := by
        intro a b ha hb
        exact primeValues_downward V P (abs_nonneg _) (abs_add_le _ _) (primeValues_add V P ha hb)
      neg_mem' := by
        intro a ha
        change PrimeValues V P (|-a|)
        rwa [abs_neg] }
  refine ⟨H, ?_⟩
  intro a b c ha hc hab hbc
  have h : PrimeValues V P (max |a| |c|) := (max_choice |a| |c|).elim
    (fun he ↦ he.symm ▸ ha) (fun he ↦ he.symm ▸ hc)
  exact primeValues_downward V P (abs_nonneg _) (abs_le_max_abs_abs hab hbc) h

theorem mem_primeToConvex_iff {g : ValueGroup V} (hg : 0 ≤ g) :
    g ∈ (primeToConvex V P).1 ↔ PrimeValues V P g := by
  change PrimeValues V P |g| ↔ _
  rw [abs_of_nonneg hg]

variable (H : ConvexAddSubgroup (ValueGroup V))

private def convexIdeal : Ideal V where
  carrier := {x | ∀ hx : x ≠ 0, ringValue V x hx ∉ H.1}
  zero_mem' := fun hx ↦ (hx rfl).elim
  add_mem' := by
    intro x y hx hy hxy
    change ∀ hx₀ : x ≠ 0, ringValue V x hx₀ ∉ H.1 at hx
    change ∀ hy₀ : y ≠ 0, ringValue V y hy₀ ∉ H.1 at hy
    by_cases hx₀ : x = 0
    · subst x
      have hy₀ : y ≠ 0 := by simpa using hxy
      simpa using hy hy₀
    by_cases hy₀ : y = 0
    · subst y
      have hx₁ : x ≠ 0 := by simpa using hxy
      simpa using hx hx₁
    intro hs
    have hmin := H.mem_of_nonneg_of_le (le_min (ringValue_nonneg V x hx₀)
      (ringValue_nonneg V y hy₀)) (ringValue_add_ge_min V hx₀ hy₀ hxy) hs
    rcases min_choice (ringValue V x hx₀) (ringValue V y hy₀) with h | h
    · exact hx hx₀ (h ▸ hmin)
    · exact hy hy₀ (h ▸ hmin)
  smul_mem' := by
    intro a x hx hax
    change a * x ≠ 0 at hax
    change ringValue V (a * x) hax ∉ H.1
    have ha := left_ne_zero_of_mul hax
    have hx₀ := right_ne_zero_of_mul hax
    rw [ringValue_mul V ha hx₀]
    intro hs
    exact hx hx₀ (H.mem_of_nonneg_of_le (ringValue_nonneg V x hx₀)
      (le_add_of_nonneg_left (ringValue_nonneg V a ha)) hs)

private theorem mem_convexIdeal_of_ne_zero {x : V} (hx : x ≠ 0) :
    x ∈ convexIdeal V H ↔ ringValue V x hx ∉ H.1 :=
  ⟨fun h ↦ h hx, fun h _ ↦ h⟩

/-- The prime formed by zero and the integral elements whose value is outside the subgroup. -/
def convexToPrime : PrimeSpectrum V where
  asIdeal := convexIdeal V H
  isPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : 1 ∈ convexIdeal V H := h.symm ▸ (show (1 : V) ∈ (⊤ : Ideal V) from trivial)
      exact ((mem_convexIdeal_of_ne_zero V H one_ne_zero).mp h1)
        (ringValue_one V ▸ H.1.zero_mem)
    · intro x y hxy
      by_cases hx : x ∈ convexIdeal V H
      · exact Or.inl hx
      by_cases hy : y ∈ convexIdeal V H
      · exact Or.inr hy
      have hx₀ : x ≠ 0 := fun h ↦ hx (h.symm ▸ (convexIdeal V H).zero_mem)
      have hy₀ : y ≠ 0 := fun h ↦ hy (h.symm ▸ (convexIdeal V H).zero_mem)
      have hxv := not_not.mp (mt (mem_convexIdeal_of_ne_zero V H hx₀).mpr hx)
      have hyv := not_not.mp (mt (mem_convexIdeal_of_ne_zero V H hy₀).mpr hy)
      have hxyv := (mem_convexIdeal_of_ne_zero V H (mul_ne_zero hx₀ hy₀)).mp hxy
      rw [ringValue_mul V hx₀ hy₀] at hxyv
      exact (hxyv (H.1.add_mem hxv hyv)).elim

theorem mem_convexToPrime_iff_of_ne_zero {x : V} (hx : x ≠ 0) :
    x ∈ (convexToPrime V H).asIdeal ↔ ringValue V x hx ∉ H.1 :=
  mem_convexIdeal_of_ne_zero V H hx

theorem mem_convexToPrime_iff (x : V) :
    x ∈ (convexToPrime V H).asIdeal ↔ x = 0 ∨ ∃ hx : x ≠ 0, ringValue V x hx ∉ H.1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [mem_convexToPrime_iff_of_ne_zero V H hx]
    exact ⟨fun h ↦ Or.inr ⟨hx, h⟩, fun h ↦ (h.resolve_left hx).elim (fun _ h ↦ h)⟩

theorem convexToPrime_primeToConvex :
    convexToPrime V (primeToConvex V P) = P := by
  apply PrimeSpectrum.ext
  ext x
  by_cases hx : x = 0
  · subst x
    simp
  · rw [mem_convexToPrime_iff_of_ne_zero V _ hx,
      mem_primeToConvex_iff V P (ringValue_nonneg V x hx), primeValues_ringValue_iff V P x hx,
      not_not]

theorem primeToConvex_convexToPrime :
    primeToConvex V (convexToPrime V H) = H := by
  have h (g : ValueGroup V) (hg : 0 ≤ g) :
      g ∈ (primeToConvex V (convexToPrime V H)).1 ↔ g ∈ H.1 := by
    obtain ⟨x, hx, rfl⟩ := exists_ringValue_of_nonneg V hg
    rw [mem_primeToConvex_iff V _ hg, primeValues_ringValue_iff V _ x hx,
      mem_convexToPrime_iff_of_ne_zero V H hx, not_not]
  exact le_antisymm (ConvexAddSubgroup.le_of_nonneg fun {g} hg ↦ (h g hg).mp)
    (ConvexAddSubgroup.le_of_nonneg fun {g} hg ↦ (h g hg).mpr)

theorem primeToConvex_antitone : Antitone (primeToConvex V) := by
  intro P Q hPQ
  apply ConvexAddSubgroup.le_of_nonneg
  intro g hg hQ
  rw [mem_primeToConvex_iff V _ hg] at hQ ⊢
  obtain ⟨x, hx, hxQ, rfl⟩ := hQ
  exact ⟨x, hx, fun hxP ↦ hxQ (hPQ hxP), rfl⟩

theorem convexToPrime_antitone : Antitone (convexToPrime V) := by
  intro H J hHJ x hx
  rw [mem_convexToPrime_iff] at hx ⊢
  exact hx.imp_right fun ⟨hx₀, h⟩ ↦ ⟨hx₀, fun hxH ↦ h (hHJ hxH)⟩

/-- The order-reversing bijection between the primes and the convex subgroups. -/
def primeConvexOrderIso : (PrimeSpectrum V)ᵒᵈ ≃o ConvexAddSubgroup (ValueGroup V) where
  toFun P := primeToConvex V (OrderDual.ofDual P)
  invFun H := OrderDual.toDual (convexToPrime V H)
  left_inv P := convexToPrime_primeToConvex V _
  right_inv H := primeToConvex_convexToPrime V H
  map_rel_iff' := by
    intro p q
    change primeToConvex V (OrderDual.ofDual p) ≤ primeToConvex V (OrderDual.ofDual q) ↔
      OrderDual.ofDual q ≤ OrderDual.ofDual p
    refine ⟨fun h ↦ ?_, fun h ↦ primeToConvex_antitone V h⟩
    have hh := convexToPrime_antitone V h
    rwa [convexToPrime_primeToConvex, convexToPrime_primeToConvex] at hh

theorem primeToConvex_bot : (primeToConvex V ⊥).1 = ⊤ := by
  let H : ConvexAddSubgroup (ValueGroup V) :=
    ⟨⊤, fun {_ b _} _ _ _ _ ↦ AddSubgroup.mem_top b⟩
  have h : H ≤ primeToConvex V ⊥ :=
    calc
      H = primeToConvex V (convexToPrime V H) := (primeToConvex_convexToPrime V H).symm
      _ ≤ primeToConvex V ⊥ := primeToConvex_antitone V bot_le
  exact le_antisymm le_top h

theorem primeToConvex_maximalIdeal :
    (primeToConvex V ⟨IsLocalRing.maximalIdeal V, inferInstance⟩).1 = ⊥ := by
  let H : ConvexAddSubgroup (ValueGroup V) := ⟨⊥, by
    intro a b c ha hc hab hbc
    rw [AddSubgroup.mem_bot] at ha hc ⊢
    exact le_antisymm (hbc.trans_eq hc) (ha.symm.trans_le hab)⟩
  let M : PrimeSpectrum V := ⟨IsLocalRing.maximalIdeal V, inferInstance⟩
  have hM : convexToPrime V H ≤ M := IsLocalRing.le_maximalIdeal_of_isPrime _
  have h : primeToConvex V M ≤ H :=
    calc
      primeToConvex V M ≤ primeToConvex V (convexToPrime V H) := primeToConvex_antitone V hM
      _ = H := primeToConvex_convexToPrime V H
  exact le_antisymm h bot_le

theorem prime_convex_correspondence :
    Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups.Correspondence := by
  intro K _ V
  refine ⟨primeConvexOrderIso V, ?_, ?_, primeToConvex_bot V, primeToConvex_maximalIdeal V⟩
  · intro P g
    constructor
    · rintro ⟨hg, h⟩
      exact (mem_primeToConvex_iff V P hg).mp h
    · intro h
      have hg : 0 ≤ g := by
        obtain ⟨x, hx, _, rfl⟩ := h
        exact ringValue_nonneg V x hx
      exact ⟨hg, (mem_primeToConvex_iff V P hg).mpr h⟩
  · intro H x
    refine (mem_convexToPrime_iff V H x).trans ?_
    exact or_congr Iff.rfl (exists_congr fun hx ↦
      ⟨fun h ↦ ⟨ringValue_nonneg V x hx, h⟩, And.right⟩)

/-- The rank of a valuation ring is its Krull dimension. -/
abbrev valuationRank (V : ValuationSubring K) : WithBot ℕ∞ :=
  Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups.valuationRank V

theorem rank_eq_krullDim_convexAddSubgroups :
    valuationRank V = Order.krullDim (ConvexAddSubgroup (ValueGroup V)) :=
  Order.krullDim_orderDual.symm.trans (Order.krullDim_eq_of_orderIso (primeConvexOrderIso V))

theorem rank_eq_iSup_length (V : ValuationSubring K) :
    valuationRank V = ⨆ c : LTSeries (ConvexAddSubgroup (ValueGroup V)), (c.length : WithBot ℕ∞) :=
  rank_eq_krullDim_convexAddSubgroups V

end CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
