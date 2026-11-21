import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.TailBounds
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformDirichlet

namespace SingleVariableAnalysis.Riemann.Improper
open Set
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch10.Dirichlet
open Specs.SingleVariableAnalysis.Ch10.TailBounds
open Specs.SingleVariableAnalysis.Ch14.UniformDirichlet
universe u

/-- Uniformly small quantitative proper tails give uniform improper convergence
and preserve the same bound on each infinite tail. -/
theorem uniform_convergence_of_quantitative_tails (k : ScalarKind) (T : Type u)
    (F : ℝ → T → S.scalarValue k) (a : ℝ) (B : ℝ → T → ℝ)
    (hfinite : ∀ t : T, ∀ R : ℝ, a ≤ R → ∀ S : ℝ, R ≤ S →
      ∃ h : I.scalarIntegrableValue k (fun x => F x t) R S,
        ‖I.scalarIntegralValue k _ h‖ ≤ B R t)
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a ⊤,
      ∀ R : RightIndex a ⊤, r.val < R.val → ∀ t : T, B R.val t < ε) :
    QuantitativeUniformTails k T F a B := by
  have hreg (R : ℝ) (hR : a ≤ R) : RightFamilyRegular k T F R ⊤ :=
    ⟨WithTop.coe_lt_top _, fun t => ⟨WithTop.coe_lt_top _, fun s =>
      (hfinite t R hR s.val s.property.1.le).choose⟩⟩
  constructor
  · apply (right_uniform_cauchy_criterion k T F a ⊤ (hreg a le_rfl)).mpr
    intro ε hε
    obtain ⟨r, hr⟩ := hzero ε hε
    refine ⟨r, fun t R S hrR hRS => ?_⟩
    obtain ⟨h, hb⟩ := hfinite t R.val R.property.1.le S.val hRS.le
    exact ⟨h, hb.trans_lt (hr R hrR t)⟩
  · intro t R hR
    refine ⟨hfinite t R hR, ?_⟩
    have hc : RightConverges k (fun x => F x t) R ⊤ := by
      apply (right_cauchy_criterion k _ R ⊤ ((hreg R hR).2 t)).mpr
      intro ε hε
      obtain ⟨r, hr⟩ := hzero ε hε
      let rR : RightIndex R ⊤ := ⟨max R r.val + 1,
        (le_max_left _ _).trans_lt (lt_add_one _), WithTop.coe_lt_top _⟩
      refine ⟨rR, fun v w hrv hvw => ?_⟩
      let va : RightIndex a ⊤ := ⟨v.val, hR.trans_lt v.property.1, WithTop.coe_lt_top _⟩
      obtain ⟨h, hb⟩ := hfinite t v.val va.property.1.le w.val hvw.le
      exact ⟨h, hb.trans_lt (hr va
        (((le_max_right R r.val).trans_lt (lt_add_one _)).trans hrv) t)⟩
    exact ⟨hc, right_integral_norm_le k _ hc (hfinite t R hR)⟩

/-- Multiplying a uniformly vanishing amplitude by 2C preserves uniform smallness.
Using max C 0 avoids any nonemptiness assumption on the parameter type. -/
private theorem uniform_scaled_amplitude {T : Type u} {g : ℝ → T → ℝ} {a C : ℝ}
    (hz : UniformRayVanishes g a) :
    ∀ ε : ℝ, 0 < ε → ∃ r : RightIndex a ⊤,
      ∀ R : RightIndex a ⊤, r.val < R.val → ∀ t : T, 2 * C * |g R.val t| < ε := by
  intro ε hε
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hd : 0 < 2 * M + 1 := by positivity
  obtain ⟨r, hr⟩ := hz (ε / (2 * M + 1)) (div_pos hε hd)
  refine ⟨r, fun R hrR t => ?_⟩
  have hg := hr R hrR t
  have he : ε / (2 * M + 1) * (2 * M + 1) = ε :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hδ : 0 < ε / (2 * M + 1) := div_pos hε hd
  have hmul := mul_le_mul_of_nonneg_left hg.le (show 0 ≤ 2 * M by positivity)
  have hCM := mul_le_mul_of_nonneg_right (show 2 * C ≤ 2 * M by
    dsimp [M]; linarith [le_max_left C 0]) (abs_nonneg (g R.val t))
  nlinarith

/-- The uniform Dirichlet test, with the same 2C bound in both scalar fields. -/
theorem uniform_dirichlet : uniformDirichlet.{u} := by
  intro k T f g g' a hf C hb hc1 hn hm hz
  have hpoint (t : T) : VanishesOnRay (fun x => g x t) a := by
    intro ε hε
    obtain ⟨r, hr⟩ := hz ε hε
    exact ⟨r, fun R hrR => hr R hrR t⟩
  have htails (t : T) := accumulation_tail_bounds k (fun x => f x t)
    (fun x => g x t) (fun x => g' x t) a (hf.2 t) C (hb t)
    (hc1 t) (hn t) (hm t) (hpoint t)
  apply uniform_convergence_of_quantitative_tails
  · exact fun t R hR => ((htails t).2 R hR).1
  · intro ε hε
    obtain ⟨r, hr⟩ := uniform_scaled_amplitude hz (C := C) ε hε
    refine ⟨r, fun R hrR t => ?_⟩
    simpa only [abs_of_nonneg (hn t R.val R.property.1.le)] using hr R hrR t

/-- Equality on the interval preserves scalar Darboux integrability and value. -/
theorem scalar_integral_congr_on (k : ScalarKind) {f g : ℝ → S.scalarValue k}
    {a b : ℝ} (hf : I.scalarIntegrableValue k f a b)
    (he : ∀ x ∈ Icc a b, f x = g x) :
    ∃ hg : I.scalarIntegrableValue k g a b,
      I.scalarIntegralValue k g hg = I.scalarIntegralValue k f hf := by
  cases k with
  | real => exact realIntegral_congr_on hf he
  | complex =>
    obtain ⟨hr, her⟩ := realIntegral_congr_on hf.1 (fun x hx => congrArg Complex.re (he x hx))
    obtain ⟨hi, hei⟩ := realIntegral_congr_on hf.2 (fun x hx => congrArg Complex.im (he x hx))
    refine ⟨⟨hr, hi⟩, ?_⟩
    change complexIntegral g ⟨hr, hi⟩ = complexIntegral f hf
    apply Complex.ext
    · simpa only [(complexIntegral_components g ⟨hr, hi⟩).1,
        (complexIntegral_components f hf).1] using her
    · simpa only [(complexIntegral_components g ⟨hr, hi⟩).2,
        (complexIntegral_components f hf).2] using hei

/-- Negation of a proper scalar integrand negates its value. -/
theorem scalar_integral_neg (k : ScalarKind) {f : ℝ → S.scalarValue k}
    {a b : ℝ} (hf : I.scalarIntegrableValue k f a b) :
    ∃ hn : I.scalarIntegrableValue k (fun x => -f x) a b,
      I.scalarIntegralValue k _ hn = -I.scalarIntegralValue k f hf := by
  cases k with
  | real =>
    change ℝ → ℝ at f
    change RealIntegrable f a b at hf
    change ∃ hn : RealIntegrable (fun x => -f x) a b,
      realIntegral _ hn = -realIntegral f hf
    simpa only [neg_one_mul] using real_mul_value hf (-1 : ℝ)
  | complex =>
    change ℝ → ℂ at f
    change ComplexIntegrable f a b at hf
    change ∃ hn : ComplexIntegrable (fun x => -f x) a b,
      complexIntegral _ hn = -complexIntegral f hf
    simpa only [neg_one_mul] using complex_mul_value hf (-1 : ℂ)

/-- For a fixed-sign real multiplier, replacing it by its modulus preserves
proper integrability and the norm of the proper integral. -/
theorem weighted_fixed_sign_norm (k : ScalarKind) (f : ℝ → S.scalarValue k)
    (g : ℝ → ℝ) {R S : ℝ}
    (hs : (∀ x ∈ Icc R S, 0 ≤ g x) ∨ (∀ x ∈ Icc R S, g x ≤ 0))
    (hh : I.scalarIntegrableValue k (weighted k f (fun x => |g x|)) R S) :
    ∃ hg : I.scalarIntegrableValue k (weighted k f g) R S,
      ‖I.scalarIntegralValue k _ hg‖ = ‖I.scalarIntegralValue k _ hh‖ := by
  rcases hs with hs | hs
  · obtain ⟨hg, he⟩ := scalar_integral_congr_on k (g := weighted k f g) hh (fun x hx => by
      cases k with
      | real =>
        change ℝ → ℝ at f
        change (f x : ℝ) * |g x| = (f x : ℝ) * g x
        rw [abs_of_nonneg (hs x hx)]
      | complex =>
        change ℝ → ℂ at f
        change (f x : ℂ) * ((|g x| : ℝ) : ℂ) = (f x : ℂ) * (g x : ℂ)
        rw [abs_of_nonneg (hs x hx)])
    exact ⟨hg, congrArg norm he⟩
  · obtain ⟨hn, hen⟩ := scalar_integral_neg k hh
    obtain ⟨hg, heg⟩ := scalar_integral_congr_on k (g := weighted k f g) hn (fun x hx => by
      cases k with
      | real =>
        change ℝ → ℝ at f
        change -((f x : ℝ) * |g x|) = (f x : ℝ) * g x
        rw [abs_of_nonpos (hs x hx), mul_neg, neg_neg]
      | complex =>
        change ℝ → ℂ at f
        change -((f x : ℂ) * ((|g x| : ℝ) : ℂ)) = (f x : ℂ) * (g x : ℂ)
        rw [abs_of_nonpos (hs x hx), Complex.ofReal_neg, mul_neg, neg_neg])
    exact ⟨hg, by rw [heg, hen, norm_neg]⟩

/-- Fixed-sign amplitudes obey the same uniform test and quantitative tails,
with their modulus on the right-hand side. -/
theorem uniform_dirichlet_fixed_sign : uniformDirichletFixedSign.{u} := by
  intro k T f g h' a hf C hb hs hc1 hm hz
  have hzabs : UniformRayVanishes (fun x t => |g x t|) a := by
    simpa only [UniformRayVanishes, abs_abs] using hz
  have hnonneg := uniform_dirichlet k T f (fun x t => |g x t|) h' a hf C hb
    hc1 (fun _ _ _ => abs_nonneg _) hm hzabs
  apply uniform_convergence_of_quantitative_tails
  · intro t R hR S hRS
    obtain ⟨hh, hhb⟩ := (hnonneg.2 t R hR).1 S hRS
    have hsign : (∀ x ∈ Icc R S, 0 ≤ g x t) ∨ (∀ x ∈ Icc R S, g x t ≤ 0) :=
      (hs t).imp (fun hp x hx => hp x (hR.trans hx.1))
        (fun hn x hx => hn x (hR.trans hx.1))
    obtain ⟨hg, he⟩ := weighted_fixed_sign_norm k (fun x => f x t) (fun x => g x t) hsign hh
    exact ⟨hg, he.trans_le hhb⟩
  · exact uniform_scaled_amplitude hz

end SingleVariableAnalysis.Riemann.Improper
