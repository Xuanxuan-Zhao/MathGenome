import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.SemifiniteMultiplierBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.MultiplierKernelsAndRange
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ExpandedFA.Multiplication

variable {Ω : Type*} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bounded measurable multiplier acts on every Lp class. -/
theorem multiplier_memLp_of_bound (a : Ω → 𝕜) (ha : Measurable a)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f : Lp 𝕜 p μ) :
    MemLp (fun x => a x * f x) p μ := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (show AEStronglyMeasurable (fun x => a x * f x) μ from
      ha.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hbound] with x hx
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

/-- An everywhere-defined closed multiplier has a continuous linear realization. -/
def fullMultiplier (a : Ω → 𝕜) (hD : (maximalMultiplier μ p a).domain = ⊤) :
    Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ := by
  let incl : Lp 𝕜 p μ →ₗ[𝕜] (maximalMultiplier μ p a).domain :=
    { toFun := fun f => ⟨f, by rw [hD]; trivial⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 p μ := (maximalMultiplier μ p a).toFun.comp incl
  apply ContinuousLinearMap.ofIsClosedGraph (g := T)
  have hgraph : T.graph = (maximalMultiplier μ p a).graph := by
    ext z
    rw [LinearMap.mem_graph_iff, mem_maximalMultiplier_graph_iff]
    constructor
    · intro hz
      rw [hz]
      exact maximalLpMultiplier_apply μ p a _
    · intro hz
      apply Lp.ext
      exact hz.trans (maximalLpMultiplier_apply μ p a (incl z.1)).symm
  rw [hgraph]
  exact maximalLpMultiplier_isClosed μ p a

theorem fullMultiplier_apply (a : Ω → 𝕜) (hD : (maximalMultiplier μ p a).domain = ⊤)
    (f : Lp 𝕜 p μ) :
    (fullMultiplier a hD f : Ω → 𝕜) =ᵐ[μ] fun x => a x * f x :=
  maximalLpMultiplier_apply μ p a _

/-- A finite positive set gives a nonzero test vector, including on arbitrary
semifinite spaces without any sigma-finiteness assumption. -/
theorem indicator_norm_pos (hp : p ≠ ∞) {F : Set Ω} (hF : MeasurableSet F)
    (hF0 : 0 < μ F) (hFtop : μ F < ∞) :
    0 < ‖indicatorConstLp p hF hFtop.ne (1 : 𝕜)‖ := by
  rw [norm_indicatorConstLp (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp,
    norm_one, one_mul]
  exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hF0.ne' hFtop.ne) _

/-- The finite-set test identifies any Lp multiplier bound with an ordinary
pointwise essential bound. -/
theorem multiplier_bound_test (hμ : Semifinite μ) (hp : p ≠ ∞)
    (a : Ω → 𝕜) (ha : Measurable a)
    (T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)
    (hT : ∀ f : Lp 𝕜 p μ, (T f : Ω → 𝕜) =ᵐ[μ] fun x => a x * f x) :
    ∀ᵐ x ∂μ, ‖a x‖ ≤ ‖T‖ := by
  apply (ae_le_const_iff_forall_gt_measure_zero (fun x => ‖a x‖) ‖T‖).mpr
  intro b hb
  by_contra hpos
  obtain ⟨F, hsub, hF, hF0, hFtop⟩ := hμ {x | b ≤ ‖a x‖}
    (measurableSet_le measurable_const ha.norm) (pos_iff_ne_zero.mpr hpos)
  let f : Lp 𝕜 p μ := indicatorConstLp p hF hFtop.ne 1
  have hf : 0 < ‖f‖ := indicator_norm_pos hp hF hF0 hFtop
  have hb0 : 0 < b := lt_of_le_of_lt (norm_nonneg T) hb
  have hlow : b * ‖f‖ ≤ ‖T f‖ := by
    have h := Lp.norm_le_mul_norm_of_ae_le_mul (c := b⁻¹) (f := f) (g := T f) ?_
    · exact (le_inv_mul_iff₀ hb0).mp h
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hF) (hμs := hFtop.ne)
      (c := (1 : 𝕜)), hT f] with x hfx hTx
    change f x = F.indicator (fun _ => (1 : 𝕜)) x at hfx
    rw [hTx, norm_mul]
    by_cases hx : x ∈ F
    · rw [hfx, Set.indicator_of_mem hx, norm_one, mul_one]
      exact (le_inv_mul_iff₀ hb0).mpr (by simpa using hsub hx)
    · rw [hfx, Set.indicator_of_notMem hx, norm_zero, mul_zero, mul_zero]
  have hup := T.le_opNorm f
  have hbc : b ≤ ‖T‖ := (mul_le_mul_iff_left₀ hf).mp (hlow.trans hup)
  exact (not_le_of_gt hb) hbc

/-- Ordinary L-infinity membership gives a full maximal domain. -/
theorem full_domain_of_memLp_top (a : Ω → 𝕜) (ha : Measurable a)
    (haTop : MemLp a ∞ μ) : (maximalMultiplier μ p a).domain = ⊤ := by
  apply top_unique
  intro f _
  exact multiplier_memLp_of_bound a ha (ae_le_lpNorm_exponent_top haTop) f

theorem memLp_top_of_full_domain (hμ : Semifinite μ) (hp : p ≠ ∞)
    (a : Ω → 𝕜) (ha : Measurable a)
    (hD : (maximalMultiplier μ p a).domain = ⊤) : MemLp a ∞ μ := by
  exact memLp_top_of_bound ha.aestronglyMeasurable ‖fullMultiplier a hD‖
    (multiplier_bound_test hμ hp a ha _ (fullMultiplier_apply a hD))

theorem semifinite_multiplier_full_domain : SemifiniteMultiplierBoundsSpec.FullDomain := by
  intro Ω 𝕜 _ _ _ _ μ hμ p _ _hp1 hp a ha
  exact ⟨memLp_top_of_full_domain hμ hp a ha, full_domain_of_memLp_top a ha⟩

/-- The two inequalities for the operator norm use precisely the ordinary
essential supremum, even when the Lp space vanishes. -/
theorem semifinite_multiplier_norm : SemifiniteMultiplierBoundsSpec.NormEquality := by
  intro Ω 𝕜 _ _ _ _ μ hμ p _ _hp1 hp a ha hD
  let T := fullMultiplier a hD
  have hT := fullMultiplier_apply a hD
  have haTop := memLp_top_of_full_domain hμ hp a ha hD
  refine ⟨T, hT, le_antisymm ?_ ?_⟩
  · apply T.opNorm_le_bound ENNReal.toReal_nonneg
    intro f
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hT f, ae_le_lpNorm_exponent_top haTop] with x hx haC
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right haC (norm_nonneg _)
  · have hsup : eLpNorm a ∞ μ ≤ ENNReal.ofReal ‖T‖ := by
      rw [eLpNorm_exponent_top ha.aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_bound (multiplier_bound_test hμ hp a ha T hT)
    have := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hsup
    simpa only [ENNReal.toReal_ofReal (norm_nonneg T)] using this

/-- Use the accepted range-closure theorem with the canonical conjugate exponent. -/
theorem multiplier_rangeClosure (hp1 : 1 < p) (hp : p ≠ ∞)
    (a : Ω → 𝕜) (ha : Measurable a) :
    closure ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) =
      (supportedLp (𝕜 := 𝕜) μ p (zeroSet a)ᶜ : Set (Lp 𝕜 p μ)) := by
  let q := p.conjExponent
  let : Fact (1 ≤ q) := ⟨by dsimp [q, ENNReal.conjExponent]; exact le_add_of_nonneg_right bot_le⟩
  exact multiplier_range_closure μ p q hp1 hp a ha

/-- The reciprocal product is the masked quotient, since inverse zero is zero. -/
theorem reciprocal_product_eq (a : Ω → 𝕜) (f : Ω → 𝕜) :
    (fun x => (a x)⁻¹ * f x) = (zeroSet a)ᶜ.indicator (fun x => f x / a x) := by
  funext x
  by_cases hx : a x = 0 <;> simp [zeroSet, hx, div_eq_mul_inv, mul_comm]

/-- Closed range means that the reciprocal multiplier has full domain.
This reduction retains the component on the zero set rather than dividing there. -/
theorem closed_range_iff_reciprocal_full (hp1 : 1 < p) (hp : p ≠ ∞)
    (a : Ω → 𝕜) (ha : Measurable a) :
    IsClosed ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) ↔
      (maximalMultiplier μ p (fun x => (a x)⁻¹)).domain = ⊤ := by
  have hZ : MeasurableSet (zeroSet a)ᶜ := (ha (measurableSet_singleton 0)).compl
  have hclosure := multiplier_rangeClosure (μ := μ) hp1 hp a ha
  constructor
  · intro hr
    have hrange : ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) =
        (supportedLp (𝕜 := 𝕜) μ p (zeroSet a)ᶜ : Set (Lp 𝕜 p μ)) := by
      rw [← hclosure, hr.closure_eq]
    apply top_unique
    intro h _
    let hg := (Lp.memLp h).indicator hZ.nullMeasurableSet
    let g : Lp 𝕜 p μ := hg.toLp _
    have hgs : g ∈ supportedLp μ p (zeroSet a)ᶜ := by
      filter_upwards [hg.coeFn_toLp] with x hx hnot
      rw [hx, Set.indicator_of_notMem hnot]
    have hgr : g ∈ (maximalMultiplier μ p a).toFun.range := by
      change g ∈ ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ))
      rw [hrange]
      exact hgs
    have hgquot := (Set.ext_iff.mp (multiplier_exact_range μ p a ha) g).mp hgr |>.2
    change MemLp (fun x => (a x)⁻¹ * h x) p μ
    apply hgquot.ae_eq
    filter_upwards [hg.coeFn_toLp] with x hx
    change g x = (zeroSet a)ᶜ.indicator (fun x => h x) x at hx
    by_cases hz : a x = 0
    · simp [zeroSet, hz]
    · have hxx : g x = h x := by simpa [zeroSet, hz] using hx
      simp [zeroSet, hz, hxx, div_eq_mul_inv, mul_comm]
  · intro hD
    have hrange : ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) =
        (supportedLp (𝕜 := 𝕜) μ p (zeroSet a)ᶜ : Set (Lp 𝕜 p μ)) := by
      ext h
      rw [multiplier_exact_range μ p a ha]
      constructor
      · rintro ⟨hz, _⟩
        filter_upwards [hz] with x hx hnot
        exact hx (by simpa only [Set.mem_compl_iff, not_not] using hnot)
      · intro hs
        refine ⟨?_, ?_⟩
        · filter_upwards [hs] with x hx hz
          exact hx (by simpa only [Set.mem_compl_iff, not_not] using hz)
        · rw [← reciprocal_product_eq]
          have hh : h ∈ (maximalMultiplier μ p (fun x => (a x)⁻¹)).domain := by
            rw [hD]; trivial
          exact hh
    rw [hrange, ← hclosure]
    exact isClosed_closure

/-- Essential boundedness of the reciprocal is exactly a positive essential
lower bound away from the zero set. -/
theorem reciprocal_memLp_top_iff (a : Ω → 𝕜) (ha : Measurable a) :
    MemLp (fun x => (a x)⁻¹) ∞ μ ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂μ, a x ≠ 0 → c ≤ ‖a x‖ := by
  constructor
  · intro hi
    let C := lpNorm (fun x => (a x)⁻¹) ∞ μ + 1
    have hC : 0 < C := add_pos_of_nonneg_of_pos lpNorm_nonneg zero_lt_one
    refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
    filter_upwards [ae_le_lpNorm_exponent_top hi] with x hx hax
    have hx' : ‖a x‖⁻¹ ≤ C := by rw [norm_inv] at hx; dsimp [C]; linarith
    exact (inv_le_comm₀ (norm_pos_iff.mpr hax) hC).mp hx'
  · rintro ⟨c, hc, hbound⟩
    apply memLp_top_of_bound ha.inv.aestronglyMeasurable c⁻¹
    filter_upwards [hbound] with x hx
    change ‖(a x)⁻¹‖ ≤ c⁻¹
    by_cases hax : a x = 0
    · simp [hax, le_of_lt (inv_pos.mpr hc)]
    · rw [norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr hax) hc).mpr (hx hax)

theorem semifinite_multiplier_closed_range : SemifiniteMultiplierBoundsSpec.ClosedRange := by
  intro Ω 𝕜 _ _ _ _ μ hμ p _ hp1 hp a ha
  rw [closed_range_iff_reciprocal_full hp1 hp a ha,
    semifinite_multiplier_full_domain μ hμ p hp1 hp (fun x => (a x)⁻¹) ha.inv]
  exact reciprocal_memLp_top_iff a ha

/-- Surjectivity detects the entire zero level under semifiniteness. -/
theorem multiplier_surjective_nonzero_ae (hμ : Semifinite μ) (_hp : p ≠ ∞)
    (a : Ω → 𝕜) (ha : Measurable a)
    (hs : Function.Surjective (maximalMultiplier μ p a).toFun) :
    ∀ᵐ x ∂μ, a x ≠ 0 := by
  have hz : μ (zeroSet a) = 0 := by
    by_contra hzero
    obtain ⟨F, hsub, hF, hF0, hFtop⟩ := hμ (zeroSet a)
      (ha (measurableSet_singleton 0)) (pos_iff_ne_zero.mpr hzero)
    let h : Lp 𝕜 p μ := indicatorConstLp p hF hFtop.ne 1
    obtain ⟨f, hf⟩ := hs h
    have heq : (h : Ω → 𝕜) =ᵐ[μ] fun x => a x * (f : Lp 𝕜 p μ) x := by
      rw [← hf]
      exact maximalLpMultiplier_apply μ p a f
    have hnull : ∀ᵐ x ∂μ, x ∉ F := by
      filter_upwards [heq, indicatorConstLp_coeFn (p := p) (hs := hF)
        (hμs := hFtop.ne) (c := (1 : 𝕜))] with x hx hi hxF
      change h x = F.indicator (fun _ => (1 : 𝕜)) x at hi
      have hax : a x = 0 := hsub hxF
      rw [hi, Set.indicator_of_mem hxF, hax, zero_mul] at hx
      exact one_ne_zero hx
    have hFzero : μ F = 0 := by simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hnull
    exact hF0.ne' hFzero
  apply ae_iff.mpr
  simpa only [not_not, zeroSet] using hz

/-- An a.e. nonzero multiplier with bounded reciprocal has its actual bounded
inverse. The identities concern the exact maximal domain, not an extension. -/
theorem reciprocal_inverse (a : Ω → 𝕜) (ha : Measurable a)
    (hnz : ∀ᵐ x ∂μ, a x ≠ 0) (hi : MemLp (fun x => (a x)⁻¹) ∞ μ) :
    ∃ B : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ,
      (∀ h : Lp 𝕜 p μ, (B h : Ω → 𝕜) =ᵐ[μ] fun x => (a x)⁻¹ * h x) ∧
      ∃ hB : ∀ h, B h ∈ (maximalMultiplier μ p a).domain,
        (∀ h, maximalMultiplier μ p a ⟨B h, hB h⟩ = h) ∧
        (∀ f : (maximalMultiplier μ p a).domain, B (maximalMultiplier μ p a f) = f) := by
  have hD := full_domain_of_memLp_top (p := p) (fun x => (a x)⁻¹) ha.inv hi
  let B := fullMultiplier (fun x => (a x)⁻¹) hD
  have hBrep : ∀ h : Lp 𝕜 p μ, (B h : Ω → 𝕜) =ᵐ[μ] fun x => (a x)⁻¹ * h x :=
    fullMultiplier_apply _ hD
  have heq (h : Lp 𝕜 p μ) : (h : Ω → 𝕜) =ᵐ[μ] fun x => a x * B h x := by
    filter_upwards [hBrep h, hnz] with x hx hax
    rw [hx, ← mul_assoc, mul_inv_cancel₀ hax, one_mul]
  have hB : ∀ h, B h ∈ (maximalMultiplier μ p a).domain := fun h =>
    (Lp.memLp h).ae_eq (heq h)
  refine ⟨B, hBrep, hB, ?_, ?_⟩
  · intro h
    apply Lp.ext
    exact (maximalLpMultiplier_apply μ p a ⟨B h, hB h⟩).trans (heq h).symm
  · intro f
    apply Lp.ext
    filter_upwards [hBrep (maximalMultiplier μ p a f),
      maximalLpMultiplier_apply μ p a f, hnz] with x hx hy hax
    rw [hx, hy, ← mul_assoc, inv_mul_cancel₀ hax, one_mul]

theorem semifinite_multiplier_surjective : SemifiniteMultiplierBoundsSpec.Surjectivity := by
  intro Ω 𝕜 _ _ _ _ μ hμ p _ hp1 hp a ha
  constructor
  · intro hs
    have hrange : (maximalMultiplier μ p a).toFun.range = ⊤ :=
      LinearMap.range_eq_top.mpr hs
    have hr : IsClosed ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) := by
      rw [hrange]; exact isClosed_univ
    obtain ⟨c, hc, hbound⟩ := (semifinite_multiplier_closed_range μ hμ p hp1 hp a ha).mp hr
    refine ⟨c, hc, ?_⟩
    filter_upwards [hbound, multiplier_surjective_nonzero_ae hμ hp a ha hs] with x hx hax
    exact hx hax
  · rintro ⟨c, hc, hbound⟩
    have hnz : ∀ᵐ x ∂μ, a x ≠ 0 := by
      filter_upwards [hbound] with x hx heq
      rw [heq, norm_zero] at hx
      exact (not_le_of_gt hc) hx
    have hi : MemLp (fun x => (a x)⁻¹) ∞ μ :=
      (reciprocal_memLp_top_iff a ha).mpr ⟨c, hc, hbound.mono fun _ hx _ => hx⟩
    obtain ⟨B, _, hB, hright, _⟩ := reciprocal_inverse (p := p) a ha hnz hi
    intro h
    exact ⟨⟨B h, hB h⟩, hright h⟩

theorem semifinite_multiplier_bounded_inverse : SemifiniteMultiplierBoundsSpec.BoundedInverse := by
  intro Ω 𝕜 _ _ _ _ μ hμ p _ hp1 hp a ha hs
  have hnz := multiplier_surjective_nonzero_ae hμ hp a ha hs
  obtain ⟨c, hc, hbound⟩ := (semifinite_multiplier_surjective μ hμ p hp1 hp a ha).mp hs
  have hi : MemLp (fun x => (a x)⁻¹) ∞ μ :=
    (reciprocal_memLp_top_iff a ha).mpr ⟨c, hc, hbound.mono fun _ hx _ => hx⟩
  obtain ⟨B, hrep, hB, hright, hleft⟩ := reciprocal_inverse (p := p) a ha hnz hi
  refine ⟨?_, B, hrep, hB, hright, hleft⟩
  intro f g hfg
  apply Subtype.ext
  exact (hleft f).symm.trans ((congrArg B hfg).trans (hleft g))

end ExpandedFA.Multiplication
