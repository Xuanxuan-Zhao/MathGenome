import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.PositiveExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05RealHahnBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Norm
import Mathlib.Tactic.Linarith

/-! Positive extension by the finite sublinear infimum majorant, and the exact
order-unit norm formula (`fa2:p5:positive-extension`). -/

noncomputable section
universe u
namespace ExpandedFA.PartV.PositiveExtension

section Majorant
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  {M : Submodule ℝ E} {f : M →ₗ[ℝ] ℝ}

omit [IsOrderedModule ℝ E] in
lemma positive_monotone (hf : PositiveOn M f) {m n : M} (h : (m : E) ≤ n) :
    f m ≤ f n := by
  have hp := hf (n - m) (sub_nonneg.mpr h)
  simpa only [map_sub, sub_nonneg] using hp

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
lemma majorantValues_nonempty (hM : Majorizing M) (x : E) :
    (MajorantValues M f x).Nonempty := by
  obtain ⟨m, hm⟩ := hM x
  exact ⟨f m, m, hm, rfl⟩

lemma majorantValues_bddBelow (hM : Majorizing M) (hf : PositiveOn M f) (x : E) :
    BddBelow (MajorantValues M f x) := by
  obtain ⟨n, hn⟩ := hM (-x)
  refine ⟨-f n, ?_⟩
  rintro r ⟨m, hm, rfl⟩
  have hnx : ((-n : M) : E) ≤ x := by simpa using neg_le_neg_iff.mpr hn
  have h := positive_monotone hf (m := -n) (n := m) (hnx.trans hm)
  simpa only [map_neg] using h

lemma majorant_le (hM : Majorizing M) (hf : PositiveOn M f)
    {x : E} (m : M) (hm : x ≤ (m : E)) : majorant M f x ≤ f m :=
  csInf_le (majorantValues_bddBelow hM hf x) ⟨m, hm, rfl⟩

lemma majorant_eq (hM : Majorizing M) (hf : PositiveOn M f) (m : M) :
    majorant M f (m : E) = f m := by
  apply le_antisymm (majorant_le hM hf m le_rfl)
  apply le_csInf (majorantValues_nonempty hM _)
  rintro r ⟨n, hn, rfl⟩
  exact positive_monotone hf hn

lemma majorant_add (hM : Majorizing M) (hf : PositiveOn M f) (x y : E) :
    majorant M f (x + y) ≤ majorant M f x + majorant M f y := by
  have hm (m : M) (hx : x ≤ (m : E)) :
      majorant M f (x + y) - f m ≤ majorant M f y := by
    apply le_csInf (majorantValues_nonempty hM _)
    rintro r ⟨n, hn, rfl⟩
    have := majorant_le hM hf (m + n) (add_le_add hx hn)
    rw [map_add] at this
    linarith
  have : majorant M f (x + y) - majorant M f y ≤ majorant M f x := by
    apply le_csInf (majorantValues_nonempty hM _)
    rintro r ⟨m, hx, rfl⟩
    have := hm m hx
    linarith
  linarith

lemma majorant_smul (hM : Majorizing M) (hf : PositiveOn M f)
    (t : ℝ) (ht : 0 ≤ t) (x : E) :
    majorant M f (t • x) = t * majorant M f x := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using majorant_eq hM hf (0 : M)
  apply le_antisymm
  · have : majorant M f (t • x) / t ≤ majorant M f x := by
      apply le_csInf (majorantValues_nonempty hM _)
      rintro r ⟨m, hm, rfl⟩
      apply (div_le_iff₀ ht).mpr
      have h := majorant_le hM hf (t • m) (smul_le_smul_of_nonneg_left hm ht.le)
      simpa only [map_smul, smul_eq_mul, mul_comm] using h
    exact (div_le_iff₀ ht).mp this |>.trans_eq (mul_comm _ _)
  · apply le_csInf (majorantValues_nonempty hM _)
    rintro r ⟨m, hm, rfl⟩
    have hx : x ≤ ((t⁻¹ • m : M) : E) := by
      have := smul_le_smul_of_nonneg_left hm (inv_nonneg.mpr ht.le)
      simpa only [Submodule.coe_smul, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using this
    have h := majorant_le hM hf (t⁻¹ • m) hx
    rw [map_smul, smul_eq_mul] at h
    have := mul_le_mul_of_nonneg_left h ht.le
    simpa only [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] using this

theorem majorant_construction : Spec.MajorantConstruction.{u} := by
  intro E _ _ _ _ _ M hM f hf
  exact ⟨fun x => ⟨majorantValues_nonempty hM x, majorantValues_bddBelow hM hf x⟩,
    ⟨majorant_add hM hf, majorant_smul hM hf⟩, majorant_eq hM hf⟩

theorem positive_extension : Spec.ExtensionTheorem.{u} := by
  intro E _ _ _ _ _ M hM f hf
  obtain ⟨L, hL, hLp⟩ := ExpandedFA.P1.real_hahn_banach M (majorant M f)
    ⟨majorant_add hM hf, majorant_smul hM hf⟩ f
    (fun m => (majorant_eq hM hf m).ge)
  refine ⟨L, hL, ?_, hLp⟩
  intro x hx
  have h := (hLp (-x)).trans (majorant_le hM hf 0 (neg_nonpos.mpr hx))
  simpa only [map_neg, map_zero, neg_nonpos] using h
end Majorant

theorem order_unit_majorizes : Spec.OrderUnitMajorizes.{u} := by
  intro E _ _ _ M e he hu x
  obtain ⟨t, _, _, ht⟩ := hu.2 x
  exact ⟨⟨t • e, M.smul_mem t he⟩, ht⟩

/-- An order unit in the subspace supplies the required majorization. -/
theorem order_unit_positive_extension : Spec.OrderUnitPositiveExtension.{u} := by
  intro E _ _ _ _ _ M e he hu f hf
  obtain ⟨L, hL, hp, _⟩ := positive_extension M (order_unit_majorizes M e he hu) f hf
  exact ⟨L, hL, hp⟩

section Gauge
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  {e : E}

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
lemma unitBounds_nonempty (hu : IsOrderUnit e) (x : E) : (UnitBounds e x).Nonempty :=
  hu.2 x

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
lemma unitBounds_bddBelow (e x : E) : BddBelow (UnitBounds e x) :=
  ⟨0, fun _ ht => ht.1⟩

lemma gauge_nonneg (hu : IsOrderUnit e) (x : E) : 0 ≤ orderUnitGauge e x :=
  le_csInf (unitBounds_nonempty hu x) (fun _ ht => ht.1)

lemma gauge_le {x : E} {t : ℝ} (ht : t ∈ UnitBounds e x) : orderUnitGauge e x ≤ t :=
  csInf_le (unitBounds_bddBelow e x) ht

lemma gauge_zero (hu : IsOrderUnit e) : orderUnitGauge e 0 = 0 := by
  apply le_antisymm _ (gauge_nonneg hu 0)
  exact gauge_le (by simp [UnitBounds])

omit [IsOrderedModule ℝ E] in
lemma unitBounds_neg (e x : E) : UnitBounds e (-x) = UnitBounds e x := by
  ext t
  simp only [UnitBounds, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ht, h₁, h₂⟩
    exact ⟨ht, neg_le.mp h₂, by simpa using le_neg.mp h₁⟩
  · rintro ⟨ht, h₁, h₂⟩
    exact ⟨ht, le_neg.mpr (by simpa using h₂), neg_le.mpr h₁⟩

lemma gauge_neg (e x : E) : orderUnitGauge e (-x) = orderUnitGauge e x := by
  unfold orderUnitGauge
  rw [unitBounds_neg]

omit [IsOrderedModule ℝ E] in
lemma unitBounds_add {x y : E} {s t : ℝ}
    (hs : s ∈ UnitBounds e x) (ht : t ∈ UnitBounds e y) :
    s + t ∈ UnitBounds e (x + y) := by
  refine ⟨add_nonneg hs.1 ht.1, ?_, ?_⟩
  · simpa only [add_smul, neg_add] using add_le_add hs.2.1 ht.2.1
  · simpa only [add_smul] using add_le_add hs.2.2 ht.2.2

lemma gauge_add (hu : IsOrderUnit e) (x y : E) :
    orderUnitGauge e (x + y) ≤ orderUnitGauge e x + orderUnitGauge e y := by
  have hs (s : ℝ) (hx : s ∈ UnitBounds e x) :
      orderUnitGauge e (x + y) - s ≤ orderUnitGauge e y := by
    apply le_csInf (unitBounds_nonempty hu y)
    intro t ht
    have := gauge_le (unitBounds_add hx ht)
    linarith
  have : orderUnitGauge e (x + y) - orderUnitGauge e y ≤ orderUnitGauge e x := by
    apply le_csInf (unitBounds_nonempty hu x)
    intro s hx
    have := hs s hx
    linarith
  linarith

omit [IsOrderedAddMonoid E] in
lemma unitBounds_smul {x : E} {s t : ℝ} (hs : 0 ≤ s)
    (ht : t ∈ UnitBounds e x) : s * t ∈ UnitBounds e (s • x) := by
  refine ⟨mul_nonneg hs ht.1, ?_, ?_⟩
  · simpa only [smul_neg, smul_smul] using
      smul_le_smul_of_nonneg_left ht.2.1 hs
  · simpa only [smul_smul] using smul_le_smul_of_nonneg_left ht.2.2 hs

lemma gauge_smul_nonneg (hu : IsOrderUnit e) (s : ℝ) (hs : 0 ≤ s) (x : E) :
    orderUnitGauge e (s • x) = s * orderUnitGauge e x := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [gauge_zero hu]
  apply le_antisymm
  · have : orderUnitGauge e (s • x) / s ≤ orderUnitGauge e x := by
      apply le_csInf (unitBounds_nonempty hu x)
      intro t ht
      exact (div_le_iff₀ hs).mpr ((gauge_le (unitBounds_smul hs.le ht)).trans_eq
        (mul_comm s t))
    exact ((div_le_iff₀ hs).mp this).trans_eq (mul_comm _ _)
  · apply le_csInf (unitBounds_nonempty hu (s • x))
    intro t ht
    have hinv := unitBounds_smul (inv_nonneg.mpr hs.le) ht
    have hx : s⁻¹ * t ∈ UnitBounds e x := by
      simpa only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using hinv
    have := mul_le_mul_of_nonneg_left (gauge_le hx) hs.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] using this

lemma gauge_smul (hu : IsOrderUnit e) (s : ℝ) (x : E) :
    orderUnitGauge e (s • x) = ‖s‖ * orderUnitGauge e x := by
  rcases le_total 0 s with hs | hs
  · simpa only [Real.norm_eq_abs, abs_of_nonneg hs] using gauge_smul_nonneg hu s hs x
  · have h : s • x = -((-s) • x) := by simp
    rw [h, gauge_neg, gauge_smul_nonneg hu (-s) (neg_nonneg.mpr hs)]
    rw [Real.norm_eq_abs, abs_of_nonpos hs]

end Gauge

section Archimedean
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {e : E}

/-- In an Archimedean order-unit space the gauge vanishes only at zero. -/
lemma gauge_definite (hu : IsOrderUnit e) (ha : ArchimedeanUnit e)
    {x : E} (hx : orderUnitGauge e x = 0) : x = 0 := by
  have hupper (y : E) (hy : orderUnitGauge e y = 0) : y ≤ 0 := by
    apply ha y
    intro ε hε
    obtain ⟨t, ht, htε⟩ := exists_lt_of_csInf_lt (unitBounds_nonempty hu y)
      (show orderUnitGauge e y < ε by rw [hy]; exact hε)
    exact ht.2.2.trans (smul_le_smul_of_nonneg_right htε.le hu.1)
  have hx₁ := hupper x hx
  have hx₂ := hupper (-x) (by rw [gauge_neg, hx])
  exact le_antisymm hx₁ (neg_nonpos.mp hx₂)
end Archimedean

/-- The gauge gives the norm axioms on the original real vector space. -/
theorem order_unit_norm_axioms : Spec.OrderUnitNormAxioms.{u} := by
  intro E _ _ _ _ _ e hu ha
  refine ⟨⟨gauge_nonneg hu, gauge_smul hu, gauge_add hu⟩, ?_⟩
  intro x
  exact ⟨gauge_definite hu ha, fun hx => hx ▸ gauge_zero hu⟩

/-- Install the established gauge as a native norm without changing the vector space. -/
theorem order_unit_space_realization : Spec.OrderUnitSpaceRealization.{u} := by
  intro E _ m _ _ _ e hu ha
  let p : Seminorm ℝ E := Seminorm.of (orderUnitGauge e) (gauge_add hu) (gauge_smul hu)
  have hd : ∀ x, p x = 0 → x = 0 := fun _ hx => gauge_definite hu ha hx
  refine ⟨p, fun _ => rfl, hd, ?_⟩
  have h := ExpandedFA.P1.C01Norm.norm_realization ℝ E p hd
  exact ⟨h.1, h.2.1⟩

theorem order_unit_normalization : Spec.OrderUnitNormalization.{u} := by
  intro E _ _ _ _ _ e hu
  constructor
  · intro he
    subst e
    exact gauge_zero hu
  · intro he
    let : SMulPosStrictMono ℝ E := SMulPosMono.toSMulPosStrictMono
    have hepos : 0 < e := lt_of_le_of_ne hu.1 (Ne.symm he)
    apply le_antisymm
    · apply gauge_le
      refine ⟨zero_le_one, ?_, ?_⟩
      · simpa only [one_smul] using (neg_nonpos.mpr hu.1).trans hu.1
      · simp only [one_smul, le_refl]
    · apply le_csInf (unitBounds_nonempty hu e)
      intro t ht
      exact (le_smul_iff_one_le_left hepos).mp ht.2.2

section Bounds
variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Preorder E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
  {e : E} {L : E →ₗ[ℝ] ℝ}

omit [IsOrderedModule ℝ E] in
lemma positive_linear_monotone (hL : ∀ x, 0 ≤ x → 0 ≤ L x)
    {x y : E} (hxy : x ≤ y) : L x ≤ L y := by
  have := hL (y - x) (sub_nonneg.mpr hxy)
  simpa only [map_sub, sub_nonneg] using this

lemma positive_interval_bound (hL : ∀ x, 0 ≤ x → 0 ≤ L x)
    {x : E} {t : ℝ} (ht : t ∈ UnitBounds e x) : |L x| ≤ t * L e := by
  apply abs_le.mpr
  constructor
  · have := positive_linear_monotone hL ht.2.1
    simpa only [map_neg, map_smul, smul_eq_mul] using this
  · have := positive_linear_monotone hL ht.2.2
    simpa only [map_smul, smul_eq_mul] using this

/-- Positivity gives a bound by the gauge, before any topology is installed. -/
lemma positive_gauge_bound (hu : IsOrderUnit e) (hL : ∀ x, 0 ≤ x → 0 ≤ L x)
    (x : E) : |L x| ≤ L e * orderUnitGauge e x := by
  have hC : 0 ≤ L e := hL e hu.1
  by_cases hzero : L e = 0
  · obtain ⟨t, ht⟩ := unitBounds_nonempty hu x
    simpa only [hzero, mul_zero, zero_mul] using positive_interval_bound hL ht
  · have hpos : 0 < L e := lt_of_le_of_ne hC (Ne.symm hzero)
    have : |L x| / L e ≤ orderUnitGauge e x := by
      apply le_csInf (unitBounds_nonempty hu x)
      intro t ht
      exact (div_le_iff₀ hpos).mpr (positive_interval_bound hL ht)
    exact ((div_le_iff₀ hpos).mp this).trans_eq (mul_comm _ _)
end Bounds

theorem bounded_positive_extension : Spec.BoundedPositiveExtension.{u} := by
  intro E _ _ _ _ _ M e he hu _ha hnorm f hf
  obtain ⟨F, hF, hpos, _⟩ := positive_extension M (order_unit_majorizes M e he hu) f hf
  have hFe : F e = f ⟨e, he⟩ := hF ⟨e, he⟩
  have hbound (x : E) : ‖F x‖ ≤ f ⟨e, he⟩ * ‖x‖ := by
    simpa only [Real.norm_eq_abs, hnorm, hFe] using positive_gauge_bound hu hpos x
  let L : E →L[ℝ] ℝ := F.mkContinuous (f ⟨e, he⟩) hbound
  have hL : L e = f ⟨e, he⟩ := hFe
  have hC : 0 ≤ f ⟨e, he⟩ := hf ⟨e, he⟩ hu.1
  refine ⟨L, hF, hpos, le_antisymm (L.opNorm_le_bound hC hbound) ?_⟩
  by_cases hezero : e = 0
  · have hsub : (⟨e, he⟩ : M) = 0 := Subtype.ext hezero
    simpa only [hsub, map_zero] using norm_nonneg L
  · have hne : ‖e‖ = 1 := (hnorm e).trans ((order_unit_normalization e hu).2 hezero)
    have := L.le_opNorm e
    simpa only [hL, Real.norm_eq_abs, abs_of_nonneg hC, hne, mul_one] using this

end ExpandedFA.PartV.PositiveExtension
