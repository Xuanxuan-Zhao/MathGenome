import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.TailBounds
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Dirichlet

namespace SingleVariableAnalysis.Riemann.Improper
open Set
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.Dirichlet
open Specs.SingleVariableAnalysis.Ch10.TailBounds

/-- The complex parts formula retains the norm bound of the primitive,
without loss from estimating its real and imaginary components separately. -/
theorem complex_weighted_variation_bound {f : ℝ → ℂ} {g g' : ℝ → ℝ}
    {u v M : ℝ} (huv : u < v) (hf : ComplexIntegrable f u v)
    (hb : ∀ (x : Icc u v) (h : ComplexIntegrable f u x), ‖complexIntegral f h‖ ≤ M)
    (hg : ContinuousOn g (Icc u v)) (hgp : ContinuousOn g' (Icc u v))
    (hd : ∀ x ∈ Ioo u v, HasDerivAt g (g' x) x)
    (hm : AntitoneOn g (Icc u v)) :
    ∃ hfg : ComplexIntegrable (fun x => f x * (g x : ℂ)) u v,
      ‖complexIntegral _ hfg‖ ≤ M * (|g v| + |g v - g u|) := by
  have hgc : ContinuousOn (fun x => (g x : ℂ)) (Icc u v) :=
    Complex.continuous_ofReal.comp_continuousOn hg
  have hgpc : ContinuousOn (fun x => (g' x : ℂ)) (Icc u v) :=
    Complex.continuous_ofReal.comp_continuousOn hgp
  have hdc (x : ℝ) (hx : x ∈ Ioo u v) :
      HasDerivAt (fun t => (g t : ℂ)) (g' x : ℂ) x := by
    apply (SingleVariableAnalysis.complex_hasDerivAt_iff_components _ _ x).mpr
    constructor
    · simpa only [Complex.ofReal_re] using hd x hx
    · simpa only [Complex.ofReal_im] using (hasDerivAt_const x (0 : ℝ))
  obtain ⟨H, F, hF, hfg, hFg, he⟩ :=
    complex_accumulation_parts f (fun x => (g x : ℂ)) (fun x => (g' x : ℂ)) hf hgc hgpc hdc
  have hFb (x : ℝ) (hx : x ∈ Icc u v) : ‖F x‖ ≤ M := by
    rw [hF ⟨x, hx⟩]
    exact hb ⟨x, hx⟩ (H ⟨x, hx⟩)
  obtain ⟨hn, hnval⟩ := integral_abs_derivative huv hg hgp hd (Or.inr hm)
  obtain ⟨hmn, hmnval⟩ := real_mul_value hn M
  obtain ⟨habs, hle, _⟩ := complex_norm_estimate _ hFg
  have horder := realIntegral_mono _ _ habs hmn (fun x hx => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hFb x hx) (abs_nonneg _))
  change realIntegral _ habs ≤ realIntegral _ hmn at horder
  rw [hmnval, hnval] at horder
  have hbound : ‖complexIntegral _ hFg‖ ≤ M * |g v - g u| := hle.trans horder
  refine ⟨hfg, ?_⟩
  change complexIntegral _ hfg = _ at he
  rw [he]
  calc
    ‖F v * (g v : ℂ) - complexIntegral _ hFg‖ ≤
        ‖F v * (g v : ℂ)‖ + ‖complexIntegral _ hFg‖ := norm_sub_le _ _
    _ ≤ M * |g v| + M * |g v - g u| := add_le_add
      (by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hFb v ⟨huv.le, le_rfl⟩) (abs_nonneg _)) hbound
    _ = _ := by ring

/-- Singleton proper integrals have norm zero in either scalar field. -/
theorem scalar_degenerate_norm (k : ScalarKind) (f : ℝ → S.scalarValue k) (u : ℝ)
    (h : I.scalarIntegrableValue k f u u) : ‖I.scalarIntegralValue k f h‖ = 0 := by
  rw [integral_degenerate k f u h]
  cases k <;> exact norm_zero

/-- With a nonnegative decreasing multiplier, variation and the terminal
boundary term add up exactly to the initial multiplier value. -/
theorem weighted_tail_bound_sharp (k : ScalarKind) (f : ℝ → S.scalarValue k)
    (g g' : ℝ → ℝ) {u v M : ℝ} (huv : u ≤ v)
    (hf : I.scalarIntegrableValue k f u v) (hM : 0 ≤ M)
    (hb : ∀ (x : Icc u v) (h : I.scalarIntegrableValue k f u x),
      ‖I.scalarIntegralValue k f h‖ ≤ M)
    (hg : ContinuousOn g (Icc u v)) (hgp : ContinuousOn g' (Icc u v))
    (hd : ∀ x ∈ Ioo u v, HasDerivAt g (g' x) x)
    (hn : ∀ x ∈ Icc u v, 0 ≤ g x) (hm : AntitoneOn g (Icc u v)) :
    ∃ hfg : I.scalarIntegrableValue k (weighted k f g) u v,
      ‖I.scalarIntegralValue k _ hfg‖ ≤ M * g u := by
  rcases lt_or_eq_of_le huv with hlt | rfl
  · have he : |g v| + |g v - g u| = g u := by
      rw [abs_of_nonneg (hn v ⟨huv, le_rfl⟩),
        abs_of_nonpos (sub_nonpos.mpr (hm ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv))]
      ring
    cases k with
    | real =>
      obtain ⟨h, hv⟩ := real_weighted_tail_bound hlt hf hM hb hg hgp hd (Or.inr hm)
      refine ⟨h, ?_⟩
      change |realIntegral _ h| ≤ M * g u
      simpa only [he] using hv
    | complex =>
      obtain ⟨h, hv⟩ := complex_weighted_variation_bound hlt hf hb hg hgp hd hm
      refine ⟨h, ?_⟩
      change ‖complexIntegral _ h‖ ≤ M * g u
      simpa only [he] using hv
  · refine ⟨integrable_degenerate k (weighted k f g) u, ?_⟩
    rw [scalar_degenerate_norm]
    exact mul_nonneg hM (hn u ⟨le_rfl, le_rfl⟩)

/-- A uniform bound on proper truncations passes to their finite improper
limit; the proof uses only the defining epsilon limit and the norm inequality. -/
theorem right_integral_norm_le (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a B : ℝ} (hc : RightConverges k f a ⊤)
    (hb : ∀ S : ℝ, a ≤ S → ∃ h : I.scalarIntegrableValue k f a S,
      ‖I.scalarIntegralValue k f h‖ ≤ B) :
    ‖RightIntegral k f a ⊤ hc‖ ≤ B := by
  obtain ⟨hf, hlim⟩ := right_integral_hasValue k f a ⊤ hc
  by_contra hnot
  have hpos : 0 < ‖RightIntegral k f a ⊤ hc‖ - B := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨r, hr⟩ := hlim (‖RightIntegral k f a ⊤ hc‖ - B) hpos
  obtain ⟨t, hrt, _⟩ := right_later r r
  obtain ⟨ht, hbt⟩ := hb t.val t.property.1.le
  have hclose := hr t hrt
  have hnorm := norm_sub_norm_le (RightIntegral k f a ⊤ hc)
    (RightTruncation k f a ⊤ hf t)
  rw [norm_sub_rev, ← dist_eq_norm] at hnorm
  change ‖RightTruncation k f a ⊤ hf t‖ ≤ B at hbt
  linarith

/-- Sharp proper and infinite bounds for a primitive controlled from R. -/
theorem direct_tail_bounds : directTailBounds := by
  intro k f g g' R hf M hbound hc1 hn hm hzero
  have hM : 0 ≤ M := by
    let t : RightIndex R ⊤ := ⟨R + 1, lt_add_one _, WithTop.coe_lt_top _⟩
    exact (norm_nonneg _).trans (hbound t)
  have hfinite : ∀ v : ℝ, R ≤ v →
      ∃ h : I.scalarIntegrableValue k (weighted k f g) R v,
        ‖I.scalarIntegralValue k _ h‖ ≤ M * g R := by
    intro v hRv
    let t : RightIndex R ⊤ := ⟨v + 1, hRv.trans_lt (lt_add_one _), WithTop.coe_lt_top _⟩
    have hfv := scalar_integrable_subinterval k f (hf.2 t) le_rfl hRv (le_add_of_nonneg_right zero_le_one)
    have hb (x : Icc R v) (h : I.scalarIntegrableValue k f R x) :
        ‖I.scalarIntegralValue k f h‖ ≤ M := by
      rcases x with ⟨x, hxmem⟩
      rcases lt_or_eq_of_le hxmem.1 with hx | hx
      · exact hbound ⟨x, hx, WithTop.coe_lt_top _⟩
      · subst x
        rw [scalar_degenerate_norm]
        exact hM
    exact weighted_tail_bound_sharp k f g g' hRv hfv hM hb
      ((hc1 t).1.mono (Icc_subset_Icc le_rfl (le_add_of_nonneg_right zero_le_one)))
      ((hc1 t).2.1.mono (Icc_subset_Icc le_rfl (le_add_of_nonneg_right zero_le_one)))
      (fun x hx => (hc1 t).2.2 x ⟨hx.1, hx.2.trans (lt_add_one _)⟩)
      (fun x hx => hn x hx.1)
      (hm.mono (fun _ hx => hx.1))
  have hc : RightConverges k (weighted k f g) R ⊤ :=
    right_dirichlet k f g g' R ⊤ hf M hbound hc1
      (Or.inr (hm.mono (fun _ hx => hx.1))) hzero
  exact ⟨hfinite, hc, right_integral_norm_le k _ hc hfinite⟩

/-- The accumulation difference A(x) - A(R) is bounded by 2C. -/
theorem accumulation_tail_bounds : accumulationTailBounds := by
  intro k f g g' a hf C hbound hc1 hn hm hzero
  have hC : 0 ≤ C := by
    let t : RightIndex a ⊤ := ⟨a + 1, lt_add_one _, WithTop.coe_lt_top _⟩
    exact (norm_nonneg _).trans (hbound t)
  refine ⟨right_dirichlet k f g g' a ⊤ hf C hbound hc1
    (Or.inr (hm.mono (fun _ hx => hx.1))) hzero, ?_⟩
  intro R haR
  have hfR : RightRegular k f R ⊤ := by
    refine ⟨WithTop.coe_lt_top _, fun t => ?_⟩
    let ta : RightIndex a ⊤ := ⟨t.val, haR.trans_lt t.property.1, WithTop.coe_lt_top _⟩
    exact scalar_integrable_subinterval k f (hf.2 ta) haR t.property.1.le le_rfl
  let taR : RightIndex a ⊤ := ⟨R + 1, haR.trans_lt (lt_add_one _), WithTop.coe_lt_top _⟩
  have hfaR : I.scalarIntegrableValue k f a R :=
    scalar_integrable_subinterval k f (hf.2 taR) le_rfl haR (le_add_of_nonneg_right zero_le_one)
  have hbar : ‖I.scalarIntegralValue k f hfaR‖ ≤ C := by
    rcases lt_or_eq_of_le haR with haRlt | rfl
    · exact hbound ⟨R, haRlt, WithTop.coe_lt_top _⟩
    · rw [scalar_degenerate_norm]
      exact hC
  have hbR (t : RightIndex R ⊤) : ‖RightTruncation k f R ⊤ hfR t‖ ≤ 2 * C := by
    let ta : RightIndex a ⊤ := ⟨t.val, haR.trans_lt t.property.1, WithTop.coe_lt_top _⟩
    have he := scalar_integral_split k f haR t.property.1.le (hf.2 ta) hfaR (hfR.2 t)
    calc
      ‖RightTruncation k f R ⊤ hfR t‖ =
          ‖RightTruncation k f a ⊤ hf ta - I.scalarIntegralValue k f hfaR‖ := by
        change ‖I.scalarIntegralValue k f (hfR.2 t)‖ =
          ‖I.scalarIntegralValue k f (hf.2 ta) - I.scalarIntegralValue k f hfaR‖
        rw [he, add_sub_cancel_left]
      _ ≤ ‖RightTruncation k f a ⊤ hf ta‖ + ‖I.scalarIntegralValue k f hfaR‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith [hbound ta]
  have hcR : COneOnRay g g' R := by
    intro t
    let ta : RightIndex a ⊤ := ⟨t.val, haR.trans_lt t.property.1, WithTop.coe_lt_top _⟩
    exact ⟨((hc1 ta).1.mono (Icc_subset_Icc haR le_rfl)),
      ((hc1 ta).2.1.mono (Icc_subset_Icc haR le_rfl)),
      fun x hx => (hc1 ta).2.2 x ⟨haR.trans_lt hx.1, hx.2⟩⟩
  have hzR : VanishesOnRay g R := by
    intro ε hε
    obtain ⟨r, hr⟩ := hzero ε hε
    let rR : RightIndex R ⊤ := ⟨max R r.val + 1,
      (le_max_left _ _).trans_lt (lt_add_one _), WithTop.coe_lt_top _⟩
    refine ⟨rR, fun t ht => ?_⟩
    let ta : RightIndex a ⊤ := ⟨t.val, haR.trans_lt t.property.1, WithTop.coe_lt_top _⟩
    exact hr ta (((le_max_right R r.val).trans_lt (lt_add_one _)).trans ht)
  exact direct_tail_bounds k f g g' R hfR (2 * C) hbR hcR
    (fun x hx => hn x (haR.trans hx))
    (hm.mono (fun _ hx => haR.trans hx)) hzR

end SingleVariableAnalysis.Riemann.Improper
