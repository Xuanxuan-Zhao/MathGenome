import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Absolute
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformComparison

/-! Uniform comparison of improper Darboux integrals. The finite norm and
order inequalities control every proper tail. Cauchy completeness supplies
uniform limits; the same finite inequality passes to their endpoint values.
No measure integral or bound on the common initial segment is used. -/
namespace SingleVariableAnalysis.Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch14.UniformComparison
open scoped ENNReal
open private norm_bound_from_approximations from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.Absolute
universe u

/-- Proper domination, valid for both scalar kinds and for degenerate intervals. -/
theorem scalar_integral_norm_le_majorant (k : ScalarKind)
    (f : ℝ → S.scalarValue k) (g : ℝ → ℝ) {a b : ℝ}
    (hf : I.scalarIntegrableValue k f a b) (hg : I.scalarIntegrableValue .real g a b)
    (hfg : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ g x) :
    ‖I.scalarIntegralValue k f hf‖ ≤ I.scalarIntegralValue .real g hg := by
  obtain ⟨hn, hle⟩ := scalar_integral_norm_le k f hf
  exact hle.trans (realIntegral_mono _ _ hn hg hfg)

/-- Moving a regular endpoint towards the singular endpoint preserves local
proper integrability, including when the regular endpoints coincide. -/
theorem right_regular_restrict (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a R : ℝ} {b : WithTop ℝ} (h : RightRegular k f a b)
    (haR : a ≤ R) (hRb : (R : WithTop ℝ) < b) : RightRegular k f R b := by
  refine ⟨hRb, fun t => ?_⟩
  let t' : RightIndex a b := ⟨t.val, haR.trans_lt t.property.1, t.property.2⟩
  exact scalar_integrable_subinterval k f (h.2 t') haR t.property.1.le le_rfl

theorem left_regular_restrict (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {R b : ℝ} (h : LeftRegular k f a b)
    (haR : a < (R : WithBot ℝ)) (hRb : R ≤ b) : LeftRegular k f a R := by
  refine ⟨haR, fun t => ?_⟩
  let t' : LeftIndex a b := ⟨t.val, t.property.1, t.property.2.trans_le hRb⟩
  exact scalar_integrable_subinterval k f (h.2 t') le_rfl t.property.2.le hRb

/-- Convergent majorants have convergent tails at every regular cutoff. -/
theorem right_converges_restrict (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a R : ℝ} {b : WithTop ℝ} (h : RightConverges k f a b)
    (haR : a ≤ R) (hRb : (R : WithTop ℝ) < b) : RightConverges k f R b := by
  obtain ⟨L, hL⟩ := h
  have hr := right_regular_restrict k f hL.1 haR hRb
  apply (right_cauchy_criterion k f R b hr).mpr
  intro ε hε
  obtain ⟨r, hrc⟩ := (right_cauchy_criterion k f a b hL.1).mp ⟨L, hL⟩ ε hε
  obtain ⟨s⟩ := right_index_nonempty hr
  let s' : RightIndex a b := ⟨s.val, haR.trans_lt s.property.1, s.property.2⟩
  obtain ⟨q, hrq, hsq⟩ := right_later r s'
  refine ⟨⟨q.val, s.property.1.trans hsq, q.property.2⟩, fun u v hqu huv => ?_⟩
  exact hrc ⟨u.val, haR.trans_lt u.property.1, u.property.2⟩
    ⟨v.val, haR.trans_lt v.property.1, v.property.2⟩ (hrq.trans hqu) huv

theorem left_converges_restrict (k : ScalarKind) (f : ℝ → S.scalarValue k)
    {a : WithBot ℝ} {R b : ℝ} (h : LeftConverges k f a b)
    (haR : a < (R : WithBot ℝ)) (hRb : R ≤ b) : LeftConverges k f a R := by
  obtain ⟨L, hL⟩ := h
  have hr := left_regular_restrict k f hL.1 haR hRb
  apply (left_cauchy_criterion k f a R hr).mpr
  intro ε hε
  obtain ⟨r, hrc⟩ := (left_cauchy_criterion k f a b hL.1).mp ⟨L, hL⟩ ε hε
  obtain ⟨s⟩ := left_index_nonempty hr
  let s' : LeftIndex a b := ⟨s.val, s.property.1, s.property.2.trans_le hRb⟩
  obtain ⟨q, hqr, hqs⟩ := left_earlier r s'
  refine ⟨⟨q.val, q.property.1, hqs.trans s.property.2⟩, fun u v huv hvq => ?_⟩
  exact hrc ⟨u.val, u.property.1, u.property.2.trans_le hRb⟩
    ⟨v.val, v.property.1, v.property.2.trans_le hRb⟩ huv (hvq.trans hqr)

/-- Cauchy comparison uses only the dominated region [A,b). -/
theorem right_uniform_converges_of_majorant (k : ScalarKind) (T : Type u)
    (f : ℝ → T → S.scalarValue k) (g : ℝ → ℝ) {a A : ℝ} {b : WithTop ℝ}
    (haA : a ≤ A) (hf : RightFamilyRegular k T f a b)
    (hg : RightConverges .real g A b)
    (hdom : ∀ x : ℝ, A ≤ x → (x : WithTop ℝ) < b → ∀ t, ‖f x t‖ ≤ g x) :
    RightUniformConverges k T f a b := by
  apply (right_uniform_cauchy_criterion k T f a b hf).mpr
  intro ε hε
  obtain ⟨G, hG⟩ := hg
  obtain ⟨r, hr⟩ := (right_cauchy_criterion .real g A b hG.1).mp ⟨G, hG⟩ ε hε
  refine ⟨⟨r.val, haA.trans_lt r.property.1, r.property.2⟩, fun t R S hrR hRS => ?_⟩
  let R' : RightIndex A b := ⟨R.val, r.property.1.trans hrR, R.property.2⟩
  let S' : RightIndex A b := ⟨S.val, R'.property.1.trans hRS, S.property.2⟩
  obtain ⟨hgt, hlt⟩ := hr R' S' hrR hRS
  obtain ⟨hft, _⟩ := right_tail_difference k (fun x => f x t) a b (hf.2 t) R S hRS
  refine ⟨hft, (scalar_integral_norm_le_majorant k _ g hft hgt ?_).trans_lt ?_⟩
  · intro x hx
    exact hdom x (R'.property.1.le.trans hx.1)
      ((WithTop.coe_le_coe.mpr hx.2).trans_lt S.property.2) t
  · exact (le_abs_self _).trans_lt hlt

theorem left_uniform_converges_of_majorant (k : ScalarKind) (T : Type u)
    (f : ℝ → T → S.scalarValue k) (g : ℝ → ℝ) {a : WithBot ℝ} {B b : ℝ}
    (hBb : B ≤ b) (hf : LeftFamilyRegular k T f a b)
    (hg : LeftConverges .real g a B)
    (hdom : ∀ x : ℝ, a < (x : WithBot ℝ) → x ≤ B → ∀ t, ‖f x t‖ ≤ g x) :
    LeftUniformConverges k T f a b := by
  apply (left_uniform_cauchy_criterion k T f a b hf).mpr
  intro ε hε
  obtain ⟨G, hG⟩ := hg
  obtain ⟨r, hr⟩ := (left_cauchy_criterion .real g a B hG.1).mp ⟨G, hG⟩ ε hε
  refine ⟨⟨r.val, r.property.1, r.property.2.trans_le hBb⟩, fun t R S hRS hSr => ?_⟩
  let S' : LeftIndex a B := ⟨S.val, S.property.1, hSr.trans r.property.2⟩
  let R' : LeftIndex a B := ⟨R.val, R.property.1, hRS.trans S'.property.2⟩
  obtain ⟨hgt, hlt⟩ := hr R' S' hRS hSr
  obtain ⟨hft, _⟩ := left_tail_difference k (fun x => f x t) a b (hf.2 t) R S hRS
  refine ⟨hft, (scalar_integral_norm_le_majorant k _ g hft hgt ?_).trans_lt ?_⟩
  · intro x hx
    exact hdom x (R.property.1.trans_le (WithBot.coe_le_coe.mpr hx.1))
      (hx.2.trans S'.property.2.le) t
  · exact (le_abs_self _).trans_lt hlt


/-- The quantitative proper comparison passes to a right endpoint limit. -/
theorem right_hasIntegral_norm_le_majorant (k : ScalarKind)
    (f : ℝ → S.scalarValue k) (g : ℝ → ℝ) {a : ℝ} {b : WithTop ℝ}
    {L : S.scalarValue k} {G : ℝ} (hL : RightHasIntegral k f a b L)
    (hG : RightHasIntegral .real g a b G)
    (hdom : ∀ x : ℝ, a ≤ x → (x : WithTop ℝ) < b → ‖f x‖ ≤ g x) : ‖L‖ ≤ G := by
  rcases hL with ⟨hf, hL⟩
  rcases hG with ⟨hg, hG⟩
  by_contra hnot
  have hp : 0 < ‖L‖ - G := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨r, hr⟩ := hL ((‖L‖ - G) / 3) (by positivity)
  obtain ⟨s, hs⟩ := hG ((‖L‖ - G) / 3) (by positivity)
  obtain ⟨t, hrt, hst⟩ := right_later r s
  have hle := scalar_integral_norm_le_majorant k f g (hf.2 t) (hg.2 t)
    (fun x hx => hdom x hx.1 ((WithTop.coe_le_coe.mpr hx.2).trans_lt t.property.2))
  change ‖RightTruncation k f a b hf t‖ ≤ RightTruncation .real g a b hg t at hle
  have h1 := hr t hrt
  have h2 := hs t hst
  change |(show ℝ from RightTruncation .real g a b hg t) - G| < _ at h2
  have hh := norm_bound_from_approximations (RightTruncation k f a b hf t) L
    (show ℝ from RightTruncation .real g a b hg t) G ((‖L‖ - G) / 3) hle h1 h2
  change ‖L‖ < G + 2 * ((‖L‖ - G) / 3) at hh
  linarith only [hh, hp]

theorem left_hasIntegral_norm_le_majorant (k : ScalarKind)
    (f : ℝ → S.scalarValue k) (g : ℝ → ℝ) {a : WithBot ℝ} {b : ℝ}
    {L : S.scalarValue k} {G : ℝ} (hL : LeftHasIntegral k f a b L)
    (hG : LeftHasIntegral .real g a b G)
    (hdom : ∀ x : ℝ, a < (x : WithBot ℝ) → x ≤ b → ‖f x‖ ≤ g x) : ‖L‖ ≤ G := by
  rcases hL with ⟨hf, hL⟩
  rcases hG with ⟨hg, hG⟩
  by_contra hnot
  have hp : 0 < ‖L‖ - G := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨r, hr⟩ := hL ((‖L‖ - G) / 3) (by positivity)
  obtain ⟨s, hs⟩ := hG ((‖L‖ - G) / 3) (by positivity)
  obtain ⟨t, htr, hts⟩ := left_earlier r s
  have hle := scalar_integral_norm_le_majorant k f g (hf.2 t) (hg.2 t)
    (fun x hx => hdom x (t.property.1.trans_le (WithBot.coe_le_coe.mpr hx.1)) hx.2)
  change ‖LeftTruncation k f a b hf t‖ ≤ LeftTruncation .real g a b hg t at hle
  have h1 := hr t htr
  have h2 := hs t hts
  change |(show ℝ from LeftTruncation .real g a b hg t) - G| < _ at h2
  have hh := norm_bound_from_approximations (LeftTruncation k f a b hf t) L
    (show ℝ from LeftTruncation .real g a b hg t) G ((‖L‖ - G) / 3) hle h1 h2
  change ‖L‖ < G + 2 * ((‖L‖ - G) / 3) at hh
  linarith only [hh, hp]

/-- Positivity of a proper real Darboux integral uses actual integrability. -/
theorem real_integral_nonneg_of_nonneg (g : ℝ → ℝ) {a b : ℝ}
    (hg : I.scalarIntegrableValue .real g a b)
    (hpos : ∀ x ∈ Set.Icc a b, 0 ≤ g x) : 0 ≤ (show ℝ from I.scalarIntegralValue .real g hg) := by
  obtain ⟨hz, heq⟩ := real_zero_value (RealIntegrable.ordered hg)
  have hm := realIntegral_mono (fun _ => 0) g hz hg hpos
  change realIntegral (fun _ => 0) hz ≤ realIntegral g hg at hm
  rw [heq] at hm
  exact hm

theorem right_hasIntegral_nonneg (g : ℝ → ℝ) {a : ℝ} {b : WithTop ℝ} {G : ℝ}
    (hG : RightHasIntegral .real g a b G)
    (hpos : ∀ x : ℝ, a ≤ x → (x : WithTop ℝ) < b → 0 ≤ g x) : 0 ≤ G := by
  rcases hG with ⟨hg, hG⟩
  by_contra hn
  have hneg : G < 0 := lt_of_not_ge hn
  obtain ⟨r, hr⟩ := hG (-G / 2) (by linarith)
  obtain ⟨t, hrt, _⟩ := right_later r r
  have hp := real_integral_nonneg_of_nonneg g (hg.2 t)
    (fun x hx => hpos x hx.1 ((WithTop.coe_le_coe.mpr hx.2).trans_lt t.property.2))
  have he := hr t hrt
  change |(show ℝ from RightTruncation .real g a b hg t) - G| < _ at he
  change 0 ≤ (show ℝ from RightTruncation .real g a b hg t) at hp
  have hlo' : -G ≤ (show ℝ from RightTruncation .real g a b hg t) - G := by
    simpa only [zero_sub] using sub_le_sub_right hp G
  have hlo : -G ≤ |(show ℝ from RightTruncation .real g a b hg t) - G| :=
    hlo'.trans (le_abs_self _)
  have hbad : -G < -G / 2 := hlo.trans_lt he
  linarith only [hbad, hneg]

theorem left_hasIntegral_nonneg (g : ℝ → ℝ) {a : WithBot ℝ} {b G : ℝ}
    (hG : LeftHasIntegral .real g a b G)
    (hpos : ∀ x : ℝ, a < (x : WithBot ℝ) → x ≤ b → 0 ≤ g x) : 0 ≤ G := by
  rcases hG with ⟨hg, hG⟩
  by_contra hn
  have hneg : G < 0 := lt_of_not_ge hn
  obtain ⟨r, hr⟩ := hG (-G / 2) (by linarith)
  obtain ⟨t, htr, _⟩ := left_earlier r r
  have hp := real_integral_nonneg_of_nonneg g (hg.2 t)
    (fun x hx => hpos x (t.property.1.trans_le (WithBot.coe_le_coe.mpr hx.1)) hx.2)
  have he := hr t htr
  change |(show ℝ from LeftTruncation .real g a b hg t) - G| < _ at he
  change 0 ≤ (show ℝ from LeftTruncation .real g a b hg t) at hp
  have hlo' : -G ≤ (show ℝ from LeftTruncation .real g a b hg t) - G := by
    simpa only [zero_sub] using sub_le_sub_right hp G
  have hlo : -G ≤ |(show ℝ from LeftTruncation .real g a b hg t) - G| :=
    hlo'.trans (le_abs_self _)
  have hbad : -G < -G / 2 := hlo.trans_lt he
  linarith only [hbad, hneg]

/-- Uniform domination of right tails, including +∞ and finite endpoints. -/
theorem right_uniform_comparison : rightComparison.{u} := by
  intro k T f g a A b haA hAb hf hg hpos hdom
  obtain ⟨F, hF⟩ := right_uniform_converges_of_majorant k T f g haA hf hg hdom
  refine ⟨F, hF, fun R hAR hRb => ?_⟩
  obtain ⟨G, hG⟩ := right_converges_restrict .real g hg hAR hRb
  have hfR : RightFamilyRegular k T f R b :=
    ⟨hRb, fun t => right_regular_restrict k _ (hf.2 t) (haA.trans hAR) hRb⟩
  have hdR : ∀ x : ℝ, R ≤ x → (x : WithTop ℝ) < b → ∀ t, ‖f x t‖ ≤ g x :=
    fun x hx hxb => hdom x (hAR.trans hx) hxb
  obtain ⟨H, hH⟩ := right_uniform_converges_of_majorant k T f g le_rfl hfR ⟨G, hG⟩ hdR
  have hbnd (t : T) : ‖H t‖ ≤ G := right_hasIntegral_norm_le_majorant k _ g
    (right_uniform_pointwise k T f R b H hH t) hG (fun x hx hxb => hdR x hx hxb t)
  refine ⟨G, H, hG, right_hasIntegral_nonneg g hG
    (fun x hx hxb => hpos x (hAR.trans hx) hxb), ?_, ?_⟩
  · exact fun t => ⟨right_uniform_pointwise k T f R b H hH t, hbnd t⟩
  · exact iSup_le (fun t => ENNReal.ofReal_le_ofReal (hbnd t))

/-- Uniform domination of left tails, including -∞ and finite endpoints. -/
theorem left_uniform_comparison : leftComparison.{u} := by
  intro k T f g a B b hBb haB hf hg hpos hdom
  obtain ⟨F, hF⟩ := left_uniform_converges_of_majorant k T f g hBb hf hg hdom
  refine ⟨F, hF, fun R haR hRB => ?_⟩
  obtain ⟨G, hG⟩ := left_converges_restrict .real g hg haR hRB
  have hfR : LeftFamilyRegular k T f a R :=
    ⟨haR, fun t => left_regular_restrict k _ (hf.2 t) haR (hRB.trans hBb)⟩
  have hdR : ∀ x : ℝ, a < (x : WithBot ℝ) → x ≤ R → ∀ t, ‖f x t‖ ≤ g x :=
    fun x hax hx => hdom x hax (hx.trans hRB)
  obtain ⟨H, hH⟩ := left_uniform_converges_of_majorant k T f g le_rfl hfR ⟨G, hG⟩ hdR
  have hbnd (t : T) : ‖H t‖ ≤ G := left_hasIntegral_norm_le_majorant k _ g
    (left_uniform_pointwise k T f a R H hH t) hG (fun x hax hx => hdR x hax hx t)
  refine ⟨G, H, hG, left_hasIntegral_nonneg g hG
    (fun x hax hx => hpos x hax (hx.trans hRB)), ?_, ?_⟩
  · exact fun t => ⟨left_uniform_pointwise k T f a R H hH t, hbnd t⟩
  · exact iSup_le (fun t => ENNReal.ofReal_le_ofReal (hbnd t))

end SingleVariableAnalysis.Riemann.Improper
