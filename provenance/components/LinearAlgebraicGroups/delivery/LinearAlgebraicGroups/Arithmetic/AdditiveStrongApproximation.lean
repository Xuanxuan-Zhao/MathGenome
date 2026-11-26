import Specs.LinearAlgebraicGroups.Arithmetic.AdditiveStrongApproximation
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

open Filter Set Topology Function IsDedekindDomain HeightOneSpectrum
open scoped RestrictedProduct WithZero

namespace LinearAlgebraicGroups.Arithmetic

universe u v

section RestrictedProduct

variable {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)

theorem GlobalFieldData.localIntegerSubring_isOpen (w : D.Place) :
    IsOpen (D.localIntegerSubring w : Set (D.Completion w)) := by
  cases w with
  | inl w => exact (D.integers_properties w).2.1
  | inr w => exact isOpen_univ

theorem GlobalFieldData.eventually_mem_localIntegerSubring (x : K) :
    ∀ᶠ w : D.Place in cofinite, D.embedding w x ∈ D.localIntegerSubring w := by
  rw [eventually_cofinite]
  apply ((D.finite_nonintegral x).image Sum.inl).subset
  rintro (w | w) hw
  · exact ⟨w, hw, rfl⟩
  · exact (hw trivial).elim

/-- The diagonal in the scalar restricted product has the canonical coordinates. -/
def GlobalFieldData.awayDiagonal (S : Set D.Place) : K →+* D.AwayAdeleRing S where
  toFun x := ⟨fun w => D.embedding w.1 x,
    Subtype.val_injective.tendsto_cofinite.eventually (D.eventually_mem_localIntegerSubring x)⟩
  map_one' := Subtype.ext (funext fun w => map_one (D.embedding w.1))
  map_mul' x y := Subtype.ext (funext fun w => map_mul (D.embedding w.1) x y)
  map_zero' := Subtype.ext (funext fun w => map_zero (D.embedding w.1))
  map_add' x y := Subtype.ext (funext fun w => map_add (D.embedding w.1) x y)

@[simp]
theorem GlobalFieldData.awayDiagonal_apply (S : Set D.Place) (x : K) (w : (Sᶜ : Set D.Place)) :
    D.awayDiagonal S x w = D.embedding w.1 x := rfl

theorem GlobalFieldData.range_awayDiagonal (S : Set D.Place) :
    range (D.awayDiagonal S) = D.awayDiagonalRange S := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, fun _ => rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext (funext fun w => (hx w).symm)⟩

theorem GlobalFieldData.awayBox_isOpen (S : Set D.Place)
    (T : Finset (Sᶜ : Set D.Place)) (U : ∀ w : (Sᶜ : Set D.Place), Set (D.Completion w.1))
    (hU : ∀ w ∈ T, IsOpen (U w))
    (hRest : ∀ w ∉ T, U w = D.localIntegerSubring w.1) :
    IsOpen {a : D.AwayAdeleRing S | ∀ w, a w ∈ U w} := by
  have hbox : {a : D.AwayAdeleRing S | ∀ w, a w ∈ U w} =
      ((fun a : D.AwayAdeleRing S => (a : ∀ w : (Sᶜ : Set D.Place), D.Completion w.1)) ⁻¹'
        ((↑T : Set (Sᶜ : Set D.Place)).pi U)) ∩
      {a : D.AwayAdeleRing S | ∀ w, w ∉ T → a w ∈ D.localIntegerSubring w.1} := by
    ext a
    constructor
    · intro ha
      exact ⟨fun w hw => ha w, fun w hw => by
        change a w ∈ (D.localIntegerSubring w.1 : Set (D.Completion w.1))
        rw [← hRest w hw]
        exact ha w⟩
    · rintro ⟨h₁, h₂⟩ w
      by_cases hw : w ∈ T
      · exact h₁ w hw
      · rw [hRest w hw]
        exact h₂ w hw
  rw [hbox]
  apply IsOpen.inter
  · exact (isOpen_set_pi T.finite_toSet hU).preimage RestrictedProduct.continuous_coe
  · exact RestrictedProduct.isOpen_forall_imp_mem
      (fun w => D.localIntegerSubring_isOpen w.1)

theorem GlobalFieldData.finiteTuples_of_singlePlace
    (h : ∀ w : D.Place, Dense (D.awayDiagonalRange {w}))
    (S : Set D.Place) (hS : S.Nonempty)
    (T : Finset (Sᶜ : Set D.Place))
    (U : ∀ w : (↑T : Set (Sᶜ : Set D.Place)), Set (D.Completion w.1.1))
    (hU : ∀ w, IsOpen (U w)) (hNE : ∀ w, (U w).Nonempty) :
    ∃ x : K, (∀ w, D.embedding w.1.1 x ∈ U w) ∧
      ∀ w : (Sᶜ : Set D.Place), w ∉ T → D.embedding w.1 x ∈ D.localIntegerSubring w.1 := by
  classical
  obtain ⟨w₀, hw₀⟩ := hS
  let j : (Sᶜ : Set D.Place) ↪ ({w₀}ᶜ : Set D.Place) :=
    ⟨fun w => ⟨w.1, fun eq => w.2 (mem_singleton_iff.mp eq ▸ hw₀)⟩,
      fun _ _ e => Subtype.ext (congrArg (fun z : ({w₀}ᶜ : Set D.Place) => z.1) e)⟩
  let T' := T.map j
  let V (w : ({w₀}ᶜ : Set D.Place)) : Set (D.Completion w.1) :=
    if hw : w.1 ∉ S then
      if hv : (⟨w.1, hw⟩ : (Sᶜ : Set D.Place)) ∈ T then U ⟨⟨w.1, hw⟩, hv⟩
      else D.localIntegerSubring w.1
    else D.localIntegerSubring w.1
  have hV (w : ({w₀}ᶜ : Set D.Place)) : IsOpen (V w) := by
    unfold V
    by_cases hs : w.1 ∉ S
    · rw [dite_eq_left hs]
      split_ifs with hv
      · exact hU ⟨⟨w.1, hs⟩, hv⟩
      · exact D.localIntegerSubring_isOpen w.1
    · rw [dite_eq_right hs]
      exact D.localIntegerSubring_isOpen w.1
  have hRest (w : ({w₀}ᶜ : Set D.Place)) (hw : w ∉ T') : V w = D.localIntegerSubring w.1 := by
    unfold V
    by_cases hs : w.1 ∉ S
    · rw [dite_eq_left hs]
      by_cases hv : (⟨w.1, hs⟩ : (Sᶜ : Set D.Place)) ∈ T
      · exact False.elim (hw (Finset.mem_map.mpr ⟨⟨w.1, hs⟩, hv, rfl⟩))
      · exact dite_eq_right hv
    · exact dite_eq_right hs
  have hVNE (w : ({w₀}ᶜ : Set D.Place)) : (V w).Nonempty := by
    unfold V
    by_cases hs : w.1 ∉ S
    · rw [dite_eq_left hs]
      split_ifs with hv
      · exact hNE ⟨⟨w.1, hs⟩, hv⟩
      · exact ⟨0, (D.localIntegerSubring w.1).zero_mem⟩
    · rw [dite_eq_right hs]
      exact ⟨0, (D.localIntegerSubring w.1).zero_mem⟩
  choose a ha using hVNE
  let b : D.AwayAdeleRing {w₀} := ⟨a, by
    rw [eventually_cofinite]
    refine T'.finite_toSet.subset ?_
    intro w hw
    by_contra hn
    exact hw (by simpa only [hRest w hn] using ha w)⟩
  have hb : b ∈ {a : D.AwayAdeleRing {w₀} | ∀ w, a w ∈ V w} := ha
  obtain ⟨y, hy, x, hx⟩ :=
    (h w₀).inter_open_nonempty _ (D.awayBox_isOpen _ T' V (fun w _ => hV w) hRest) ⟨b, hb⟩
  refine ⟨x, ?_, ?_⟩
  · intro w
    have hloc := hy (j w.1)
    rw [hx (j w.1)] at hloc
    have heq : V (j w.1) = U w := by
      change (if hw : w.1.1 ∉ S then
        if hv : (⟨w.1.1, hw⟩ : (Sᶜ : Set D.Place)) ∈ T then U ⟨⟨w.1.1, hw⟩, hv⟩
        else (D.localIntegerSubring w.1.1 : Set (D.Completion w.1.1))
        else (D.localIntegerSubring w.1.1 : Set (D.Completion w.1.1))) = _
      rw [dite_eq_left (show w.1.1 ∉ S from w.1.2)]
      rw [dite_eq_left (show (⟨w.1.1, w.1.2⟩ : (Sᶜ : Set D.Place)) ∈ T from w.2)]
    rwa [heq] at hloc
  · intro w hw
    have hloc := hy (j w)
    rw [hx (j w)] at hloc
    have heq : V (j w) = (D.localIntegerSubring w.1 : Set (D.Completion w.1)) := by
      change (if hs : w.1 ∉ S then
        if hv : (⟨w.1, hs⟩ : (Sᶜ : Set D.Place)) ∈ T then U ⟨⟨w.1, hs⟩, hv⟩
        else (D.localIntegerSubring w.1 : Set (D.Completion w.1))
        else (D.localIntegerSubring w.1 : Set (D.Completion w.1))) = _
      rw [dite_eq_left (show w.1 ∉ S from w.2), dite_eq_right hw]
    rwa [heq] at hloc

end RestrictedProduct

section FiniteCongruences

variable {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L]
  [IsFractionRing R L]

private theorem adic_ball_mem_nhds (w : HeightOneSpectrum R)
    (a : w.adicCompletion L) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    {b : w.adicCompletion L | Valued.v (b - a) < γ} ∈ 𝓝 a := by
  let val : Valuation (w.adicCompletion L) ℤᵐ⁰ := Valued.v
  obtain ⟨c, hc⟩ := w.valuedAdicCompletion_surjective L γ
  have hc' : val.restrict c ≠ 0 := fun h => hγ (hc ▸ val.restrict_eq_zero_iff.mp h)
  apply Valued.mem_nhds.mpr
  refine ⟨Units.mk0 _ hc', ?_⟩
  intro b hb
  change val.restrict (b - a) < val.restrict c at hb
  exact hc ▸ val.restrict_lt_iff.mp hb

private theorem exists_integral_approximation (w : HeightOneSpectrum R)
    (a : w.adicCompletion L) (ha : Valued.v a ≤ 1) (γ : (ℤᵐ⁰)ˣ)
    (hγ : (γ : ℤᵐ⁰) ≤ 1) :
    ∃ r : R, Valued.v (algebraMap R (w.adicCompletion L) r - a) < (γ : ℤᵐ⁰) := by
  let C := w.adicCompletion L
  let val : Valuation C ℤᵐ⁰ := Valued.v
  obtain ⟨x, hx⟩ := (w.denseRange_algebraMap (K := L)).mem_nhds
    (adic_ball_mem_nhds w a (Units.ne_zero γ))
  change val (algebraMap L C x - a) < (γ : ℤᵐ⁰) at hx
  have hInt : val (algebraMap L C x) ≤ 1 := by
    rw [← sub_add_cancel (algebraMap L C x) a]
    exact (val.map_add _ _).trans (max_le (hx.le.trans hγ) ha)
  have hxInt : w.valuation L x ≤ 1 := by
    change Valued.v ((x : L) : C) ≤ 1 at hInt
    rwa [valuedAdicCompletion_eq_valuation'] at hInt
  obtain ⟨r, hr⟩ := w.exists_valuation_sub_lt_of_integer hxInt γ
  have hr' : val (algebraMap R C r - algebraMap L C x) < (γ : ℤᵐ⁰) := by
    rw [IsScalarTower.algebraMap_apply R L C, ← map_sub]
    change Valued.v (((algebraMap R L r - x : L) : C)) < _
    rwa [valuedAdicCompletion_eq_valuation']
  refine ⟨r, ?_⟩
  change val (algebraMap R C r - a) < _
  rw [← sub_add_sub_cancel (algebraMap R C r) (algebraMap L C x) a]
  exact (val.map_add _ _).trans_lt (max_lt hr' hx)

/-- Independent finite congruences on completed integral elements of a Dedekind domain. -/
theorem exists_integral_chineseRemainder (T : Finset (HeightOneSpectrum R))
    (a : ∀ w : (↑T : Set (HeightOneSpectrum R)), w.1.adicCompletion L)
    (ha : ∀ w, Valued.v (a w) ≤ 1) (γ : (↑T : Set (HeightOneSpectrum R)) → (ℤᵐ⁰)ˣ)
    (hγ : ∀ w, (γ w : ℤᵐ⁰) ≤ 1) :
    ∃ r : R, ∀ w, Valued.v (algebraMap R (w.1.adicCompletion L) r - a w) <
      (γ w : ℤᵐ⁰) := by
  classical
  choose b hb using fun (w : (↑T : Set (HeightOneSpectrum R))) =>
    exists_integral_approximation w.1 (a w) (ha w) (γ w) (hγ w)
  choose n hn using fun (w : (↑T : Set (HeightOneSpectrum R))) =>
    WithZero.exists_exp_neg_natCast_lt (Units.ne_zero (γ w))
  let I (w : (↑T : Set (HeightOneSpectrum R))) := w.1.asIdeal ^ n w
  have hI : Pairwise (IsCoprime on I) := by
    intro w z hwz
    exact isCoprime_pow_of_ne w.1 z.1 (fun h => hwz (Subtype.ext h)) (n w) (n z)
  obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hI (fun w => Ideal.Quotient.mk (I w) (b w))
  refine ⟨r, fun w => ?_⟩
  have hmem : r - b w ∈ w.1.asIdeal ^ n w := Ideal.Quotient.eq.mp (hr w)
  have hval := (w.1.intValuation_le_pow_iff_mem _ _).mpr hmem
  let C := w.1.adicCompletion L
  let val : Valuation C ℤᵐ⁰ := Valued.v
  have hle : val (algebraMap R C r - algebraMap R C (b w)) ≤ WithZero.exp (-(n w : ℤ)) := by
    rw [← map_sub, IsScalarTower.algebraMap_apply R L C]
    change Valued.v (((algebraMap R L (r - b w) : L) : C)) ≤ _
    rwa [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  change val (algebraMap R C r - a w) < _
  rw [← sub_add_sub_cancel (algebraMap R C r) (algebraMap R C (b w)) (a w)]
  exact (val.map_add _ _).trans_lt (max_lt (hle.trans_lt (hn w)) (hb w))

private theorem exists_small_integer (w : HeightOneSpectrum R)
    (a : w.adicCompletion L) :
    ∃ d : R, d ≠ 0 ∧ Valued.v (algebraMap R (w.adicCompletion L) d * a) ≤ 1 := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hπ₀ : π ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  by_cases ha : a = 0
  · exact ⟨1, one_ne_zero, by simp [ha]⟩
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt (inv_ne_zero hva)
  refine ⟨π ^ n, pow_ne_zero _ hπ₀, ?_⟩
  rw [Valuation.map_mul, map_pow, Valuation.map_pow]
  have heq : Valued.v (algebraMap R (w.adicCompletion L) π) = WithZero.exp (-1 : ℤ) := by
    rw [IsScalarTower.algebraMap_apply R L (w.adicCompletion L)]
    change Valued.v (((algebraMap R L π : L) : w.adicCompletion L)) = _
    rwa [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  rw [heq]
  have hp : WithZero.exp (-1 : ℤ) ^ n = WithZero.exp (-(n : ℤ)) := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, ← WithZero.exp_add]
      congr 1
      push_cast
      omega
  rw [hp]
  exact (le_div_iff₀ (zero_lt_iff.mpr hva)).mp (by simpa using hn.le)

/-- Every finite adele over a Dedekind domain differs from a rational element
by an element integral in every completion. -/
theorem exists_integral_finiteAdele_remainder
    (a : ∀ w : HeightOneSpectrum R, w.adicCompletion L)
    (ha : ∀ᶠ w in cofinite, Valued.v (a w) ≤ 1) :
    ∃ x : L, ∀ w : HeightOneSpectrum R,
      a w - algebraMap L (w.adicCompletion L) x ∈ w.adicCompletionIntegers L := by
  classical
  let B := (eventually_cofinite.mp ha).toFinset
  choose c hc₀ hc using fun w : HeightOneSpectrum R => exists_small_integer w (a w)
  let d := ∏ w ∈ B, c w
  have hd₀ : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => hc₀ w)
  let dval (w : HeightOneSpectrum R) : ℤᵐ⁰ :=
    Valued.v (algebraMap R (w.adicCompletion L) d)
  have hdv (w : HeightOneSpectrum R) : dval w = w.intValuation d := by
    change Valued.v (algebraMap R (w.adicCompletion L) d) = _
    rw [IsScalarTower.algebraMap_apply R L (w.adicCompletion L)]
    change Valued.v (((algebraMap R L d : L) : w.adicCompletion L)) = _
    rw [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  have hdv₀ (w : HeightOneSpectrum R) : dval w ≠ 0 := by
    rw [hdv]
    exact w.intValuation_ne_zero d hd₀
  have hdv₁ (w : HeightOneSpectrum R) : dval w ≤ 1 := by
    rw [hdv]
    exact w.intValuation_le_one d
  have hint (w : HeightOneSpectrum R) :
      Valued.v (algebraMap R (w.adicCompletion L) d * a w) ≤ 1 := by
    by_cases hw : w ∈ B
    · let e := ∏ q ∈ B.erase w, c q
      have he : e * c w = d := Finset.prod_erase_mul B c hw
      rw [← he, map_mul (algebraMap R (w.adicCompletion L)), mul_assoc, Valuation.map_mul]
      have hl : Valued.v (algebraMap R (w.adicCompletion L) e) ≤ 1 := by
        change (algebraMap R (w.adicCompletion L) e) ∈ w.adicCompletionIntegers L
        rw [IsScalarTower.algebraMap_apply R L (w.adicCompletion L)]
        exact w.coe_algebraMap_mem R L e
      exact (mul_le_mul' hl (hc w)).trans_eq (one_mul _)
    · have hwa : Valued.v (a w) ≤ 1 := by
        by_contra h
        exact hw ((eventually_cofinite.mp ha).mem_toFinset.mpr h)
      rw [Valuation.map_mul]
      exact (mul_le_mul' (hdv₁ w) hwa).trans_eq (one_mul _)
  have hf : {w : HeightOneSpectrum R | dval w < 1}.Finite := by
    have heq : {w : HeightOneSpectrum R | dval w < 1} =
        {w | w.asIdeal ∣ Ideal.span {d}} := by
      ext w
      change dval w < 1 ↔ w.asIdeal ∣ Ideal.span {d}
      rw [hdv, intValuation_lt_one_iff_dvd]
    rw [heq]
    exact Ideal.finite_factors (by simpa using hd₀)
  let T := B ∪ hf.toFinset
  let γ (w : (↑T : Set (HeightOneSpectrum R))) : (ℤᵐ⁰)ˣ :=
    Units.mk0 (dval w.1) (hdv₀ w.1)
  obtain ⟨r, hr⟩ := exists_integral_chineseRemainder T
    (fun w => algebraMap R (w.1.adicCompletion L) d * a w.1)
    (fun w => hint w.1) γ (fun w => hdv₁ w.1)
  let x := algebraMap R L r / algebraMap R L d
  refine ⟨x, fun w => ?_⟩
  have hdl : algebraMap R L d ≠ 0 := by
    exact fun h => hd₀ ((IsFractionRing.injective R L) (h.trans (map_zero _).symm))
  have hdc : algebraMap R (w.adicCompletion L) d ≠ 0 := by
    exact fun h => hdv₀ w (by simp [dval, h])
  have herr : Valued.v (algebraMap R (w.adicCompletion L) r -
      algebraMap R (w.adicCompletion L) d * a w) ≤ dval w := by
    by_cases hw : w ∈ T
    · exact (hr ⟨w, hw⟩).le
    · have h₁ : dval w = 1 := by
        refine (hdv₁ w).antisymm (le_of_not_gt fun h => hw ?_)
        exact Finset.mem_union_right _ (hf.mem_toFinset.mpr h)
      rw [h₁]
      apply (Valued.v.map_sub _ _).trans
      refine max_le ?_ (hint w)
      change algebraMap R (w.adicCompletion L) r ∈ w.adicCompletionIntegers L
      rw [IsScalarTower.algebraMap_apply R L (w.adicCompletion L)]
      exact w.coe_algebraMap_mem R L r
  rw [mem_adicCompletionIntegers]
  have hmul : (a w - algebraMap L (w.adicCompletion L) x) *
      algebraMap R (w.adicCompletion L) d =
      algebraMap R (w.adicCompletion L) d * a w - algebraMap R (w.adicCompletion L) r := by
    dsimp only [x]
    rw [sub_mul, mul_comm (a w), map_div₀,
      ← IsScalarTower.algebraMap_apply R L (w.adicCompletion L) r,
      ← IsScalarTower.algebraMap_apply R L (w.adicCompletion L) d,
      div_mul_cancel₀ _ hdc]
  rw [← mul_le_mul_iff_left₀ (zero_lt_iff.mpr (hdv₀ w)), one_mul, ← Valuation.map_mul,
    hmul, Valuation.map_sub_swap]
  exact herr

end FiniteCongruences

section CompactRemainders

variable {A B E K : Type*} [CommRing A] [CommRing B] [Field K]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E] [AddCommGroup E]
  [IsTopologicalRing B] [IsTopologicalAddGroup E]

private theorem exists_nonzero_scalar_in_nhds
    (e : K →+* A) (p : A →+* B) (hp : Continuous p)
    (q : A →+ E) (hq : Continuous q) (j : E → A)
    (hpj : ∀ t, p (j t) = 0) (hqj : ∀ t, q (j t) = t)
    (hE : ¬ IsCompact (univ : Set E)) {C : Set A} (hC : IsCompact C)
    (hrep : ∀ a : A, ∃ x : K, a - e x ∈ C)
    {U : Set B} (hU : U ∈ 𝓝 (0 : B)) :
    ∃ x : K, x ≠ 0 ∧ p (e x) ∈ U := by
  classical
  have hsub : {z : B × B | z.1 - z.2 ∈ U} ∈ 𝓝 (0 : B) ×ˢ 𝓝 (0 : B) := by
    rw [← nhds_prod_eq]
    exact (continuous_fst.sub continuous_snd).continuousAt.preimage_mem_nhds
      (by simpa only [Pi.sub_apply, sub_zero] using hU)
  obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := Filter.mem_prod_iff.mp hsub
  obtain ⟨V, hVsub, hVo, hV⟩ := mem_nhds_iff.mp (inter_mem hV₁ hV₂)
  have hdiff : ∀ b ∈ V, ∀ c ∈ V, b - c ∈ U :=
    fun b hb c hc => hsub (show (b, c) ∈ V₁ ×ˢ V₂ from ⟨(hVsub hb).1, (hVsub hc).2⟩)
  let N (b : B) : Set B := (fun y : B => y - b) ⁻¹' V
  have hcover : p '' C ⊆ ⋃ b, N b := by
    intro b _
    exact mem_iUnion.mpr ⟨b, by simp only [N, mem_preimage, sub_self, hV]⟩
  obtain ⟨T, hT⟩ := (hC.image hp).elim_finite_subcover N
    (fun b => hVo.preimage (continuous_id.sub continuous_const)) hcover
  choose x hx using fun t => hrep (j t)
  let c (t : E) := j t - e (x t)
  have hc (t : E) : c t ∈ C := hx t
  have hpc (t : E) : p (c t) = -p (e (x t)) := by simp [c, hpj]
  have ht (t : E) : ∃ b : (↑T : Set B), p (c t) ∈ N b.1 := by
    obtain ⟨b, hb⟩ := mem_iUnion.mp (hT (mem_image_of_mem p (hc t)))
    obtain ⟨hbT, hbV⟩ := mem_iUnion.mp hb
    exact ⟨⟨b, hbT⟩, hbV⟩
  choose b hb using ht
  by_contra! h
  have heq (t s : E) (hts : b t = b s) : x t = x s := by
    have hs₁ := hb s
    have ht₁ := hb t
    rw [hts] at ht₁
    have hmem : p (e (x t - x s)) ∈ U := by
      have hsmall := hdiff _ hs₁ _ ht₁
      change (p (c s) - (b s).1) - (p (c t) - (b s).1) ∈ U at hsmall
      rw [map_sub, map_sub]
      rw [hpc t, hpc s] at hsmall
      convert hsmall using 1; abel
    exact sub_eq_zero.mp (by_contra fun hne => h (x t - x s) hne hmem)
  let r (i : (↑T : Set B)) : E := if hi : ∃ t, b t = i then hi.choose else 0
  have hr (t : E) : b (r (b t)) = b t := by
    have ht' : ∃ s, b s = b t := ⟨t, rfl⟩
    simpa only [r, dite_eq_left ht'] using ht'.choose_spec
  apply hE
  have hcompact : IsCompact (⋃ i : (↑T : Set B), (fun y : E => q (e (x (r i))) + y) '' (q '' C)) :=
    isCompact_iUnion fun i => (hC.image hq).image (continuous_const.add continuous_id)
  convert hcompact using 1
  ext t
  simp only [mem_univ, true_iff]
  refine mem_iUnion.mpr ⟨b t, q (c t), mem_image_of_mem q (hc t), ?_⟩
  rw [heq _ _ (hr t)]
  simp [c, hqj]

/-- A compact set of adelic representatives implies density after deleting a noncompact
local factor. Scaling by a small nonzero rational element shrinks the projected set of
representatives into any neighborhood of zero. -/
theorem dense_projection_of_compact_representatives
    (e : K →+* A) (p : A →+* B) (hp : Continuous p) (hpSurj : Surjective p)
    (q : A →+ E) (hq : Continuous q) (j : E → A)
    (hpj : ∀ t, p (j t) = 0) (hqj : ∀ t, q (j t) = t)
    (hE : ¬ IsCompact (univ : Set E)) {C : Set A} (hC : IsCompact C)
    (hrep : ∀ a : A, ∃ x : K, a - e x ∈ C) :
    DenseRange (fun x : K => p (e x)) := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨b, hb⟩
  obtain ⟨a, rfl⟩ := hpSurj b
  let W : Set B := (fun y => p a - y) ⁻¹' U
  have hW : W ∈ 𝓝 (0 : B) := by
    apply (hU.preimage (continuous_const.sub continuous_id)).mem_nhds
    simpa [W] using hb
  have hpC := hC.image hp
  have hmul : {z : B × B | z.1 * z.2 ∈ W} ∈ 𝓝 (0 : B) ×ˢ 𝓝ˢ (p '' C) := by
    apply hpC.mem_prod_nhdsSet_of_forall
    intro y _
    rw [← nhds_prod_eq]
    exact (continuous_fst.mul continuous_snd).continuousAt.preimage_mem_nhds
      (by simp only [Pi.mul_apply, zero_mul]; exact hW)
  obtain ⟨V, hV, Z, hZ, hVZ⟩ := Filter.mem_prod_iff.mp hmul
  obtain ⟨s, hs, hVmem⟩ :=
    exists_nonzero_scalar_in_nhds e p hp q hq j hpj hqj hE hC hrep hV
  obtain ⟨x, hx⟩ := hrep (e s⁻¹ * a)
  have hrem := hVZ (show (p (e s), p (e s⁻¹ * a - e x)) ∈ V ×ˢ Z from
    ⟨hVmem, (subset_of_mem_nhdsSet hZ) (mem_image_of_mem p hx)⟩)
  refine ⟨p (e (s * x)), ?_, mem_range_self (s * x)⟩
  change p a - p (e s) * p (e s⁻¹ * a - e x) ∈ U at hrem
  have heq : e s * (e s⁻¹ * a - e x) = a - e (s * x) := by
    rw [mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one, one_mul, map_mul]
  rwa [← map_mul, heq, map_sub, sub_sub_cancel] at hrem

end CompactRemainders

section ScalarAdeles

variable {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)

private abbrev AllAdeles := Πʳ w : D.Place, [D.Completion w, D.localIntegerSubring w]

private def allDiagonal : K →+* AllAdeles D where
  toFun x := ⟨fun w => D.embedding w x, D.eventually_mem_localIntegerSubring x⟩
  map_one' := Subtype.ext (funext fun w => map_one (D.embedding w))
  map_mul' x y := Subtype.ext (funext fun w => map_mul (D.embedding w) x y)
  map_zero' := Subtype.ext (funext fun w => map_zero (D.embedding w))
  map_add' x y := Subtype.ext (funext fun w => map_add (D.embedding w) x y)

private def awayProjection (S : Set D.Place) : AllAdeles D →+* D.AwayAdeleRing S :=
  RestrictedProduct.mapAlongRingHom D.Completion (fun w : (Sᶜ : Set D.Place) => D.Completion w.1)
    Subtype.val Subtype.val_injective.tendsto_cofinite (fun _ => RingHom.id _)
    (Filter.Eventually.of_forall (fun _ _ hx => hx))

private theorem awayProjection_continuous (S : Set D.Place) : Continuous (awayProjection D S) :=
  RestrictedProduct.mapAlong_continuous D.Completion
    (fun w : (Sᶜ : Set D.Place) => D.Completion w.1)
    Subtype.val Subtype.val_injective.tendsto_cofinite (fun _ => id)
    (Filter.Eventually.of_forall (fun _ _ hx => hx)) (fun _ => continuous_id)

private theorem awayProjection_surjective (S : Set D.Place) :
    Surjective (awayProjection D S) := by
  classical
  intro b
  let a (w : D.Place) : D.Completion w := if hw : w ∉ S then b ⟨w, hw⟩ else 0
  have ha : ∀ᶠ w in cofinite, a w ∈ D.localIntegerSubring w := by
    rw [eventually_cofinite]
    refine ((eventually_cofinite.mp b.eventually).image Subtype.val).subset ?_
    intro w hw
    by_cases hs : w ∉ S
    · refine ⟨⟨w, hs⟩, ?_, rfl⟩
      intro ht
      apply hw
      change a w ∈ (D.localIntegerSubring w : Set (D.Completion w))
      rw [show a w = b ⟨w, hs⟩ from dite_eq_left hs]
      exact ht
    · exact False.elim (hw (by simpa only [a, dite_eq_right hs] using
        (D.localIntegerSubring w).zero_mem))
  refine ⟨⟨a, ha⟩, Subtype.ext (funext fun w => ?_)⟩
  change a w.1 = b w
  exact dite_eq_left (show w.1 ∉ S from w.2)

private def singlePlaceAdele (w : D.Place) (t : D.Completion w) : AllAdeles D := by
  classical
  refine ⟨Pi.single w t, ?_⟩
  rw [eventually_cofinite]
  refine (finite_singleton w).subset ?_
  intro z hz
  by_contra hne
  exact hz (by rw [Pi.single_eq_of_ne (fun h => hne (mem_singleton_iff.mpr h))]
               exact (D.localIntegerSubring z).zero_mem)

private theorem compact_adelic_box (T : Finset D.Place)
    (C : ∀ w, Set (D.Completion w)) (hC : ∀ w, IsCompact (C w))
    (hRest : ∀ w ∉ T, C w ⊆ D.localIntegerSubring w) :
    IsCompact {a : AllAdeles D | ∀ w, a w ∈ C w} := by
  let W : Set D.Place := (↑T : Set D.Place)ᶜ
  have hW : cofinite ≤ 𝓟 W := le_principal_iff.mpr
    (by simpa only [W, mem_cofinite, compl_compl] using T.finite_toSet)
  let H := Πʳ w : D.Place, [D.Completion w, D.localIntegerSubring w]_[𝓟 W]
  let f : H → ∀ w, D.Completion w := fun a => a
  have hf : IsEmbedding f := RestrictedProduct.isEmbedding_coe_of_principal
  have hc : IsCompact (univ.pi C) := isCompact_univ_pi hC
  have hRange : univ.pi C ⊆ range f := by
    intro a ha
    refine ⟨⟨a, mem_principal.mpr (fun w hw => hRest w hw (ha w (mem_univ w)))⟩, rfl⟩
  have hPre : IsCompact (f ⁻¹' (univ.pi C)) := (hf.isCompact_preimage_iff hRange).mpr hc
  have hEq : RestrictedProduct.inclusion D.Completion
      (fun w => (D.localIntegerSubring w : Set (D.Completion w))) hW ''
      (f ⁻¹' (univ.pi C)) = {a : AllAdeles D | ∀ w, a w ∈ C w} := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩ w
      exact hb w (mem_univ w)
    · intro ha
      exact ⟨⟨a.1, mem_principal.mpr (fun w hw => hRest w hw (ha w))⟩,
        fun w _ => ha w, Subtype.ext rfl⟩
  rw [← hEq]
  exact hPre.image (RestrictedProduct.continuous_inclusion hW)

private def HasCompactRemainders : Prop :=
  ∃ C : Set (AllAdeles D), IsCompact C ∧
    ∀ a : AllAdeles D, ∃ x : K, a - allDiagonal D x ∈ C

private theorem dense_singlePlace_of_compact (w : D.Place)
    (hTop : ∀ i : D.Place, IsTopologicalRing (D.Completion i))
    (hNoncompact : ¬ IsCompact (univ : Set (D.Completion w)))
    {C : Set (AllAdeles D)} (hC : IsCompact C)
    (hRep : ∀ a : AllAdeles D, ∃ x : K, a - allDiagonal D x ∈ C) :
    Dense (D.awayDiagonalRange {w}) := by
  classical
  let (i : D.Place) := hTop i
  let : Fact (∀ i : ({w}ᶜ : Set D.Place),
      IsOpen (D.localIntegerSubring i.1 : Set (D.Completion i.1))) :=
    ⟨fun i => D.localIntegerSubring_isOpen i.1⟩
  have h := dense_projection_of_compact_representatives
    (allDiagonal D) (awayProjection D {w}) (awayProjection_continuous D {w})
    (awayProjection_surjective D {w})
    (RestrictedProduct.evalAddMonoidHom D.Completion w) (RestrictedProduct.continuous_eval w)
    (singlePlaceAdele D w)
    (fun t => Subtype.ext (funext fun i => by
      change Pi.single w t i.1 = 0
      exact Pi.single_eq_of_ne (fun h => i.2 (mem_singleton_iff.mpr h)) t))
    (fun t => Pi.single_eq_same w t) hNoncompact hC hRep
  rw [← D.range_awayDiagonal]
  exact h

end ScalarAdeles

section NumberFields

open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type u) [Field K] [NumberField K]

private def infiniteAdeleHomeomorph : InfiniteAdeleRing K ≃ₜ mixedEmbedding.mixedSpace K := by
  classical
  exact (Homeomorph.piEquivPiSubtypeProd (fun w : InfinitePlace K => w.IsReal)
    (fun w => w.Completion)).trans
    ((Homeomorph.piCongrRight (fun ⟨_, hw⟩ =>
      (Completion.isometryEquivRealOfIsReal hw).toHomeomorph)).prodCongr
      ((Homeomorph.piCongrRight (fun ⟨_, hw⟩ =>
        (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex)))))

omit [NumberField K] in
private theorem infiniteAdeleHomeomorph_apply (a : InfiniteAdeleRing K) :
    infiniteAdeleHomeomorph K a = InfiniteAdeleRing.ringEquiv_mixedSpace K a := rfl

/-- The archimedean product is covered by the translates of one compact set by the
diagonal image of the ring of integers. -/
theorem numberField_exists_compact_infinite_remainders :
    ∃ C : Set (InfiniteAdeleRing K), IsCompact C ∧
      ∀ a : InfiniteAdeleRing K, ∃ x : 𝓞 K,
        a - algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K x) ∈ C := by
  classical
  let b := mixedEmbedding.latticeBasis K
  let h := infiniteAdeleHomeomorph K
  let C := closure (ZSpan.fundamentalDomain b)
  have hC : IsCompact C := (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  refine ⟨h ⁻¹' C, h.isCompact_preimage.mpr hC, fun a => ?_⟩
  let y := ZSpan.floor b (h a)
  have hy : (y : mixedEmbedding.mixedSpace K) ∈ mixedEmbedding.integerLattice K :=
    (mixedEmbedding.mem_span_latticeBasis K).mp y.property
  obtain ⟨r, hr⟩ := hy
  have hEq : h (algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K r)) = y := by
    rw [infiniteAdeleHomeomorph_apply]
    rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    exact hr
  refine ⟨r, subset_closure ?_⟩
  have hsub : h (a - algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K r)) =
      h a - h (algebraMap K (InfiniteAdeleRing K) (algebraMap (𝓞 K) K r)) := by
    simp only [h, infiniteAdeleHomeomorph_apply, map_sub]
  rw [hsub, hEq, ← ZSpan.fract_apply]
  exact ZSpan.fract_mem_fundamentalDomain b (h a)

omit [NumberField K] in
set_option backward.isDefEq.respectTransparency false in
private theorem numberField_exists_compact_remainders (h : NumberField K) :
    HasCompactRemainders (GlobalFieldData.number (K := K) h : GlobalFieldData.{u, v} K) := by
  classical
  let := h
  let D : GlobalFieldData.{u, v} K := .number h
  obtain ⟨Cinfty, hCinfty, hrep⟩ := numberField_exists_compact_infinite_remainders K
  let C (w : D.Place) : Set (D.Completion w) :=
    match w with
    | .inl w => (D.integers w : Set (D.FiniteCompletion w))
    | .inr w => (fun z : InfiniteAdeleRing K => z w) '' Cinfty
  let T := Finset.univ.map
    (⟨Sum.inr, Sum.inr_injective⟩ : NumberField.InfinitePlace K ↪ D.Place)
  change HasCompactRemainders D
  refine ⟨{a | ∀ w, a w ∈ C w}, compact_adelic_box D T C ?_ ?_, ?_⟩
  · rintro (w | w)
    · exact (D.integers_properties w).1
    · change IsCompact ((fun z : InfiniteAdeleRing K => z w) '' Cinfty)
      exact hCinfty.image (continuous_apply w)
  · rintro (w | w) hw
    · exact subset_rfl
    · exact (hw (Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩)).elim
  · intro a
    let aFinite (w : NumberFinitePlace K) : w.adicCompletion K := a (.inl w)
    let aInfinite (w : NumberField.InfinitePlace K) : w.Completion := a (.inr w)
    have ha : ∀ᶠ w : NumberFinitePlace K in cofinite, Valued.v (aFinite w) ≤ 1 :=
      Sum.inl_injective.tendsto_cofinite.eventually a.eventually
    obtain ⟨x, hx⟩ := exists_integral_finiteAdele_remainder _ ha
    let b : InfiniteAdeleRing K := fun w => aInfinite w - algebraMap K w.Completion x
    obtain ⟨r, hr⟩ := hrep b
    refine ⟨x + algebraMap (𝓞 K) K r, ?_⟩
    rintro (w | w)
    · change aFinite w -
          algebraMap K (w.adicCompletion K) (x + algebraMap (𝓞 K) K r) ∈
        w.adicCompletionIntegers K
      rw [map_add, ← sub_sub]
      exact (D.integers w).sub_mem (hx w) (w.coe_algebraMap_mem (𝓞 K) K r)
    · refine ⟨_, hr, ?_⟩
      change b w - algebraMap K w.Completion (algebraMap (𝓞 K) K r) =
        aInfinite w - algebraMap K w.Completion (x + algebraMap (𝓞 K) K r)
      simp only [b, map_add, sub_sub]

end NumberFields

section FunctionFields

open scoped Polynomial RatFunc nonZeroDivisors

variable {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]

omit [Finite F] in
private theorem parameterInteger_map (t : SeparatingParameter F K) :
    algebraMap t.integerRing K t.parameterInteger = t.element :=
  Polynomial.aeval_X _

private theorem exists_chart_remainder (t : SeparatingParameter F K)
    (a : ∀ w : FunctionPlace K, w.Completion) (ha : ∀ᶠ w in cofinite, a w ∈ w.integers) :
    ∃ x : K, ∀ w : FunctionPlace K, t.element ∈ w.1 → a w - w.embedding x ∈ w.integers := by
  let b (w : HeightOneSpectrum t.integerRing) := t.completionEquiv w (a (t.placeOfPrime w))
  have hb : ∀ᶠ w in cofinite, Valued.v (b w) ≤ 1 :=
    (t.placeOfPrime_injective.tendsto_cofinite.eventually ha).mono
      (fun w hw => (t.completionEquiv_mem_integers w _).mpr hw)
  obtain ⟨x, hx⟩ := exists_integral_finiteAdele_remainder b hb
  refine ⟨x, fun w hw => ?_⟩
  change w ∈ {v : FunctionPlace K | t.element ∈ v.1} at hw
  rw [← t.range_placeOfPrime] at hw
  obtain ⟨q, rfl⟩ := hw
  apply (t.completionEquiv_mem_integers q _).mp
  rw [map_sub, t.completionEquiv_embedding]
  exact hx q

private theorem power_mul_mem_range_of_poles {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (z : R) (x : L)
    (hz : ∀ w : HeightOneSpectrum R, 1 < w.valuation L x → w.intValuation z < 1) :
    ∃ n : ℕ, (algebraMap R L z) ^ n * x ∈ (algebraMap R L).range := by
  classical
  let T := (HeightOneSpectrum.Support.finite R x).toFinset
  have hg (w : HeightOneSpectrum R) (hw : w ∈ T) :
      ∃ n : ℕ, w.intValuation z ^ n * w.valuation L x ≤ 1 := by
    have hx : 1 < w.valuation L x := (HeightOneSpectrum.Support.finite R x).mem_toFinset.mp hw
    have hval : w.intValuation z ≤ WithZero.exp (-1 : ℤ) := by
      rw [← WithZero.lt_mul_exp_iff_le (by simp : WithZero.exp (-1 : ℤ) ≠ 0), ← WithZero.exp_add]
      simpa using hz w hx
    have hxpos : 0 < w.valuation L x := zero_lt_one.trans hx
    obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt (inv_ne_zero hxpos.ne')
    refine ⟨n, ?_⟩
    calc
      _ ≤ WithZero.exp (-1 : ℤ) ^ n * w.valuation L x :=
        mul_le_mul' (pow_le_pow_left' hval n) le_rfl
      _ ≤ 1 := by
        rw [← WithZero.exp_nsmul]
        apply (le_div_iff₀ hxpos).mp
        simpa using hn.le
  choose m hm using hg
  let n := T.attach.sup (fun w => m w.1 w.2)
  refine ⟨n, mem_integers_of_valuation_le_one _ _ (fun w => ?_)⟩
  rw [Valuation.map_mul, Valuation.map_pow, valuation_of_algebraMap]
  by_cases hw : w ∈ T
  · exact (mul_le_mul' (pow_le_pow_of_le_one (zero_le : 0 ≤ w.intValuation z)
      (w.intValuation_le_one z) (Finset.le_sup (f := fun w : T => m w.1 w.2)
        (Finset.mem_attach _ ⟨w, hw⟩))) le_rfl).trans (hm w hw)
  · have hx : w.valuation L x ≤ 1 :=
      le_of_not_gt (fun h => hw ((HeightOneSpectrum.Support.finite R x).mem_toFinset.mpr h))
    exact (mul_le_mul' (pow_le_one₀ zero_le (w.intValuation_le_one z)) hx).trans_eq (one_mul _)

omit [Finite F] in
private theorem eval_inverse_division (t : K) (ht : t ≠ 0) (n : ℕ) (p : F[X]) :
    ∃ a b : F[X], t ^ n * Polynomial.aeval t⁻¹ p =
      Polynomial.aeval t a + Polynomial.aeval t⁻¹ b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, b, h₁⟩ := hp
    obtain ⟨c, d, h₂⟩ := hq
    refine ⟨a + c, b + d, ?_⟩
    simp only [map_add, mul_add, h₁, h₂]
    abel
  | monomial k c =>
    by_cases hn : k ≤ n
    · refine ⟨Polynomial.monomial (n - k) c, 0, ?_⟩
      simp only [Polynomial.aeval_monomial, map_zero, add_zero, inv_pow, pow_sub₀ t ht hn]
      ac_rfl
    · have hk := le_of_not_ge hn
      refine ⟨0, Polynomial.monomial (k - n) c, ?_⟩
      simp only [Polynomial.aeval_monomial, map_zero, zero_add,
        pow_sub₀ t⁻¹ (inv_ne_zero ht) hk, inv_pow, inv_inv]
      ac_rfl

omit [Finite F] in
private theorem split_inverse_lattice (t : SeparatingParameter F K) :
    ∃ d : t.integerRing, d ≠ 0 ∧ ∀ (x : K) (n : ℕ),
      t.element⁻¹ ^ n * x ∈ (algebraMap t.inverse.integerRing K).range →
      ∃ (r : t.integerRing) (s : t.inverse.integerRing),
        x = algebraMap t.integerRing K r / algebraMap t.integerRing K d +
          algebraMap t.inverse.integerRing K s := by
  classical
  let I := t.inverse.integerRing
  let R := t.integerRing
  let iR : R →+* K := algebraMap R K
  let iI : I →+* K := algebraMap I K
  let : Algebra F[X] K := t.inverse.polynomialAlgebra
  let : Algebra F⟮X⟯ K := t.inverse.rationalAlgebra
  let : Module.Finite F[X] I :=
    IsIntegralClosure.finite F[X] F⟮X⟯ K (FunctionField.ringOfIntegers F K)
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := F[X]) (M := I)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite R⁰ (fun j => iI (e j))
  have hd₀ : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hdK : iR (d : R) ≠ 0 := fun h => hd₀
    ((IsFractionRing.injective R K) (h.trans (map_zero iR).symm))
  choose f hf using hd
  have hf' (j : Fin m) : iR (f j) = iR (d : R) * iI (e j) := hf j
  have ht : t.element ≠ 0 := fun h => t.transcendental (h ▸ isAlgebraic_zero)
  refine ⟨d, hd₀, fun x n hx => ?_⟩
  obtain ⟨c, hc⟩ := hx
  have hspan : c ∈ Submodule.span F[X] (range e) := he ▸ Submodule.mem_top
  obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun F[X]).mp hspan
  have hc' : t.element⁻¹ ^ n * x =
      ∑ j, Polynomial.aeval t.element⁻¹ (p j) * iI (e j) := by
    rw [← hc, ← hp, map_sum]
    rfl
  choose a b hab using fun j => eval_inverse_division t.element ht n (p j)
  have hxsum : x = ∑ j, (Polynomial.aeval t.element (a j) +
      Polynomial.aeval t.element⁻¹ (b j)) * iI (e j) := by
    have h := congrArg (t.element ^ n * ·) hc'
    simp only [Finset.mul_sum, ← mul_assoc, hab, ← mul_pow, mul_inv_cancel₀ ht, one_pow,
      one_mul] at h
    exact h
  let r : R := ∑ j, algebraMap F[X] R (a j) * f j
  let s : I := ∑ j, algebraMap F[X] I (b j) * e j
  refine ⟨r, s, ?_⟩
  have hr : iR r = iR (d : R) * (∑ j, Polynomial.aeval t.element (a j) * iI (e j)) := by
    dsimp only [r]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, hf']
    change Polynomial.aeval t.element (a j) * (iR (d : R) * iI (e j)) = _
    ac_rfl
  have hs : iI s = ∑ j, Polynomial.aeval t.element⁻¹ (b j) * iI (e j) := by
    simp only [s, map_sum, map_mul]
    rfl
  change x = iR r / iR (d : R) + iI s
  rw [hr, mul_div_cancel_left₀ _ hdK, hs, ← Finset.sum_add_distrib]
  simpa only [add_mul] using hxsum

private theorem exists_pole_remainder (t : SeparatingParameter F K)
    (a : ∀ w : FunctionPlace K, w.Completion) :
    ∃ x : K,
      (∀ w : FunctionPlace K, t.element ∉ w.1 → a w - w.embedding x ∈ w.integers) ∧
      ∀ q : HeightOneSpectrum t.inverse.integerRing,
        1 < q.valuation K x → q.intValuation t.inverse.parameterInteger < 1 := by
  classical
  let b (w : FunctionPlace K) : w.Completion := if t.element ∉ w.1 then a w else 0
  have hb : ∀ᶠ w in cofinite, b w ∈ w.integers := by
    rw [eventually_cofinite]
    apply t.finite_poles.subset
    intro w hw h
    exact hw (by simp [b, h])
  obtain ⟨x, hx⟩ := exists_chart_remainder t.inverse b hb
  have hval (w : FunctionPlace K) (hw : t.element ∉ w.1) : b w = a w := ite_eq_left hw
  refine ⟨x, fun w hw => ?_, fun q hq => ?_⟩
  · rw [← hval w hw]
    exact hx w (w.1.mem_or_inv_mem t.element |>.resolve_left hw)
  · let w := t.inverse.placeOfPrime q
    have hinv : t.inverse.element ∈ w.1 := by
      change w ∈ {v : FunctionPlace K | t.inverse.element ∈ v.1}
      rw [← t.inverse.range_placeOfPrime]
      exact ⟨q, rfl⟩
    have hbad : w.embedding x ∉ w.integers := by
      intro h
      have h' := (t.inverse.completionEquiv_mem_integers q _).mpr h
      rw [t.inverse.completionEquiv_embedding, mem_adicCompletionIntegers] at h'
      change Valued.v ((x : K) : q.adicCompletion K) ≤ 1 at h'
      rw [valuedAdicCompletion_eq_valuation'] at h'
      exact hq.not_ge h'
    have hpole : t.element ∉ w.1 := by
      intro h
      have h' := hx w hinv
      rw [show b w = 0 from ite_eq_right (not_not_intro h), zero_sub] at h'
      exact hbad (by simpa only [neg_mem_iff] using h')
    rw [← valuation_of_algebraMap (K := K)]
    change (q.valuation K) (algebraMap t.inverse.integerRing K t.inverse.parameterInteger) < 1
    rw [parameterInteger_map]
    change (q.valuation K) t.element⁻¹ < 1
    rw [map_inv₀]
    apply inv_lt_one_of_one_lt₀
    change 1 < (q.valuation K) t.element
    exact lt_of_not_ge hpole

private theorem functionField_exists_compact_remainders (t : SeparatingParameter F K) :
    HasCompactRemainders (GlobalFieldData.function F t) := by
  classical
  let D := GlobalFieldData.function F t
  obtain ⟨d, hd, hsplit⟩ := split_inverse_lattice t
  let dK := algebraMap t.integerRing K d
  have hdK : dK ≠ 0 := fun h => hd ((IsFractionRing.injective t.integerRing K)
    (h.trans (map_zero _).symm))
  let Pole := {w : FunctionPlace K | t.element ∉ w.1}
  have hPole : Pole.Finite := t.finite_poles
  let Bad : Set (FunctionPlace K) := {w | w.embedding dK⁻¹ ∉ w.integers}
  have hBad : Bad.Finite := FunctionPlace.nonintegral_finite t dK⁻¹
  let T : Finset D.Place := (hPole.union hBad).toFinset.map ⟨Sum.inl, Sum.inl_injective⟩
  let C (w : FunctionPlace K) : Set w.Completion :=
    if w ∈ Pole then w.integers
    else (fun z : w.Completion => w.embedding dK⁻¹ * z) '' (w.integers : Set w.Completion)
  let box (w : D.Place) : Set (D.Completion w) := match w with
    | .inl w => C w
    | .inr w => w.elim
  change HasCompactRemainders D
  refine ⟨{a | ∀ w, a w ∈ box w}, compact_adelic_box D T box ?_ ?_, ?_⟩
  · rintro (w | w)
    · change IsCompact (C w)
      have hO := (FunctionPlace.completionIntegers_properties t w).1
      by_cases hw : w ∈ Pole
      · simpa only [C, ite_eq_left hw] using hO
      · simp only [C, ite_eq_right hw]
        exact hO.image (continuous_const.mul continuous_id)
    · exact w.elim
  · rintro (w | w) hw
    · have hgood : w ∉ Pole ∪ Bad := fun h => hw
        (Finset.mem_map.mpr ⟨w, (hPole.union hBad).mem_toFinset.mpr h, rfl⟩)
      have h₁ : w ∉ Pole := fun h => hgood (Or.inl h)
      have h₂ : w.embedding dK⁻¹ ∈ w.integers := not_not.mp (fun h => hgood (Or.inr h))
      change C w ⊆ (w.integers : Set w.Completion)
      simp only [C, ite_eq_right h₁]
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem h₂ hz
    · exact w.elim
  · intro a
    let b (w : FunctionPlace K) : w.Completion := a (.inl w)
    have hb : ∀ᶠ w in cofinite, b w ∈ w.integers :=
      Sum.inl_injective.tendsto_cofinite.eventually a.eventually
    obtain ⟨x, hx⟩ := exists_chart_remainder t b hb
    obtain ⟨y, hy, hyPole⟩ := exists_pole_remainder t (fun w => b w - w.embedding x)
    obtain ⟨n, hn⟩ := power_mul_mem_range_of_poles t.inverse.parameterInteger y hyPole
    rw [parameterInteger_map] at hn
    obtain ⟨r, s, hrs⟩ := hsplit y n hn
    let z := algebraMap t.integerRing K r / dK
    refine ⟨x + z, ?_⟩
    rintro (w | w)
    · change b w - w.embedding (x + z) ∈ C w
      rw [map_add, ← sub_sub]
      by_cases hw : w ∈ Pole
      · simp only [C, ite_eq_left hw]
        have hchart : t.inverse.element ∈ w.1 :=
          (w.1.mem_or_inv_mem t.element).resolve_left hw
        have hsInt : w.embedding (algebraMap t.inverse.integerRing K s) ∈ w.integers := by
          change w ∈ {q : FunctionPlace K | t.inverse.element ∈ q.1} at hchart
          rw [← t.inverse.range_placeOfPrime] at hchart
          obtain ⟨q, rfl⟩ := hchart
          apply (t.inverse.completionEquiv_mem_integers q _).mp
          rw [t.inverse.completionEquiv_embedding]
          exact q.coe_algebraMap_mem t.inverse.integerRing K s
        have heq : b w - w.embedding x - w.embedding z =
            (b w - w.embedding x - w.embedding y) +
              w.embedding (algebraMap t.inverse.integerRing K s) := by
          rw [hrs, map_add]
          change b w - w.embedding x - w.embedding z =
              b w - w.embedding x - (w.embedding z + _) + _
          abel
        rw [heq]
        exact add_mem (hy w hw) hsInt
      · simp only [C, ite_eq_right hw]
        have hxInt := hx w (not_not.mp hw)
        have hchart : t.element ∈ w.1 := not_not.mp hw
        have hmapInt (k : t.integerRing) : w.embedding (algebraMap t.integerRing K k) ∈
            w.integers := by
          change w ∈ {q : FunctionPlace K | t.element ∈ q.1} at hchart
          rw [← t.range_placeOfPrime] at hchart
          obtain ⟨q, rfl⟩ := hchart
          apply (t.completionEquiv_mem_integers q _).mp
          rw [t.completionEquiv_embedding]
          exact q.coe_algebraMap_mem t.integerRing K k
        have hden : w.embedding dK ≠ 0 := fun h => hdK
          (w.embedding.injective (h.trans (map_zero _).symm))
        refine ⟨w.embedding dK * (b w - w.embedding x) -
          w.embedding (algebraMap t.integerRing K r), ?_, ?_⟩
        · exact sub_mem (mul_mem (hmapInt d) hxInt) (hmapInt r)
        · dsimp only [z]
          rw [map_inv₀, mul_sub, ← mul_assoc, inv_mul_cancel₀ hden, one_mul,
            map_div₀, div_eq_mul_inv, mul_comm (w.embedding dK)⁻¹]
    · exact w.elim

end FunctionFields

section LocalTopology

private theorem noncompact_of_nonarchimedean_localField (L : Type*)
    [Field L] [TopologicalSpace L] [ValuativeRel L] [IsNonarchimedeanLocalField L] :
    ¬ IsCompact (univ : Set L) := by
  classical
  let val := ValuativeRel.valuation L
  let O : Set L := val.valuationSubring
  have hO : IsOpen O := Valuation.isOpen_valuationSubring val
  let U (x : L) : Set L := (fun y : L => y - x) ⁻¹' O
  have hCover : (univ : Set L) ⊆ ⋃ x, U x := by
    intro y _
    exact mem_iUnion.mpr ⟨y, by change y - y ∈ O; rw [sub_self]; exact val.valuationSubring.zero_mem⟩
  intro hCompact
  obtain ⟨T, hT⟩ := hCompact.elim_finite_subcover U
    (fun x => hO.preimage (continuous_id.sub continuous_const)) hCover
  let γ := max 1 (T.sup val)
  obtain ⟨r, hr⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨s, hs⟩ := Valuation.IsNontrivial.exists_one_lt (v := val)
  have hγ : 0 < γ := zero_lt_one.trans_le (le_max_left _ _)
  have hlarge : γ < val (r * s) := by
    rw [map_mul, hr]
    exact lt_mul_of_one_lt_right hγ hs
  have hmem := hT (mem_univ (r * s))
  obtain ⟨x, hx⟩ := mem_iUnion.mp hmem
  obtain ⟨hxT, hxU⟩ := mem_iUnion.mp hx
  have hxv : val x ≤ γ := (Finset.le_sup (f := val) hxT).trans (le_max_right _ _)
  have h₁ : val (r * s - x) ≤ 1 := hxU
  apply hlarge.not_ge
  rw [← sub_add_cancel (r * s) x]
  exact (val.map_add _ _).trans (max_le (h₁.trans (le_max_left _ _)) hxv)

private theorem completion_isTopologicalRing {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (w : D.Place) : IsTopologicalRing (D.Completion w) := by
  cases w with
  | inl w =>
    change IsTopologicalRing (D.FiniteCompletion w)
    infer_instance
  | inr w =>
    cases D with
    | number h =>
      change IsTopologicalRing w.Completion
      infer_instance
    | function F t => exact w.elim

private theorem completion_noncompact {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) (w : D.Place) :
    ¬ IsCompact (univ : Set (D.Completion w)) := by
  cases w with
  | inl w =>
    change ¬ IsCompact (univ : Set (D.FiniteCompletion w))
    exact noncompact_of_nonarchimedean_localField _
  | inr w =>
    cases D with
    | number h =>
      change ¬ IsCompact (univ : Set w.Completion)
      intro hc
      rcases em w.IsReal with hw | hw
      · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
        have him := hc.image e.continuous
        rw [image_univ, e.surjective.range_eq] at him
        exact noncompact_univ ℝ him
      · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw)
        have him := hc.image e.continuous
        rw [image_univ, e.surjective.range_eq] at him
        exact noncompact_univ ℂ him
    | function F t => exact w.elim

end LocalTopology

/-- The diagonal of a global field is dense in the scalar adeles outside any one place. -/
theorem additiveStrongApproximation : AdditiveStrongApproximationSpec.singlePlace := by
  intro K _ D w
  have h : HasCompactRemainders D := by
    cases D with
    | number h => exact numberField_exists_compact_remainders K h
    | function F t => exact functionField_exists_compact_remainders t
  obtain ⟨C, hC, hRep⟩ := h
  exact dense_singlePlace_of_compact D w (completion_isTopologicalRing D)
    (completion_noncompact D w) hC hRep

/-- Approximate finitely many targets and remain integral at the other finite places
outside any nonempty set of omitted places. -/
theorem additiveFiniteTuples : AdditiveStrongApproximationSpec.finiteTuples := by
  intro K _ D S hS T U hU hNE
  exact D.finiteTuples_of_singlePlace (additiveStrongApproximation D) S hS T U hU hNE

end LinearAlgebraicGroups.Arithmetic
