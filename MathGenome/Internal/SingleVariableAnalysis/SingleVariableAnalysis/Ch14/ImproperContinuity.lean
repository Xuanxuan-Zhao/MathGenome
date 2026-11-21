import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ImproperContinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperContinuity

/-! Continuity from uniform improper tails, K03.14.improper_continuity.
Only one sufficiently late truncation is used in the three-error argument.
No absolute convergence or domination hypothesis is introduced.
-/
namespace SingleVariableAnalysis.ParameterIntegral
open scoped Topology
open Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch14.UniformImproper

/-- Uniform approximation on a relative neighborhood transfers continuity at its
base point. The approximating functions need be continuous only at that point. -/
theorem continuousAt_of_uniform_approximation_on_nhds
    {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (N : Set X) (t₀ : N) (hN : N ∈ 𝓝 t₀.val)
    (F : X → Y) (H : ι → N → Y)
    (hcont : ∀ i, ContinuousAt (H i) t₀)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ i, ∀ t : N, dist (H i t) (F t.val) < ε) :
    ContinuousAt F t₀.val := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨i, hi⟩ := happrox (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp (hcont i) (ε / 3) (by positivity)
  obtain ⟨η, hη, hηN⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨min δ η, lt_min hδ hη, fun {t} ht => ?_⟩
  have htN : t ∈ N := hηN (ht.trans_le (min_le_right _ _))
  let u : N := ⟨t, htN⟩
  have hmid : dist (H i u) (H i t₀) < ε / 3 :=
    hc (show dist u t₀ < δ from ht.trans_le (min_le_left _ _))
  have htri := dist_triangle (F t) (H i u) (F t₀.val)
  have htri' := dist_triangle (H i u) (H i t₀) (F t₀.val)
  have hfirst : dist (F t) (H i u) < ε / 3 := by
    simpa only [dist_comm] using hi u
  have hlast := hi t₀
  linarith

theorem right_improper_continuity :
    Specs.SingleVariableAnalysis.Ch14.ImproperContinuity.rightContinuity := by
  intro k T N t₀ hN f a b F h hlim hcont
  apply continuousAt_of_uniform_approximation_on_nhds N t₀ hN F
    (fun R t => RightTruncation k (fun x => f x t.val) a b (h.2 t) R) hcont
  intro ε hε
  obtain ⟨h', hF⟩ := hlim
  obtain ⟨r, hr⟩ := hF ε hε
  obtain ⟨R, hrR, _⟩ := right_later r r
  exact ⟨R, hr R hrR⟩

theorem left_improper_continuity :
    Specs.SingleVariableAnalysis.Ch14.ImproperContinuity.leftContinuity := by
  intro k T N t₀ hN f a b F h hlim hcont
  apply continuousAt_of_uniform_approximation_on_nhds N t₀ hN F
    (fun R t => LeftTruncation k (fun x => f x t.val) a b (h.2 t) R) hcont
  intro ε hε
  obtain ⟨h', hF⟩ := hlim
  obtain ⟨r, hr⟩ := hF ε hε
  obtain ⟨R, hRr, _⟩ := left_earlier r r
  exact ⟨R, hr R hRr⟩

/-- Changing an ambient representative off the integration interval does not
change an existing proper Darboux integral. -/
theorem scalar_integral_congr_on (k : ScalarKind) {a b : ℝ}
    {f g : ℝ → Specs.SingleVariableAnalysis.Ch01.Scalar.scalarValue k}
    (hf : Riemann.Integrable k f a b) (hg : Riemann.Integrable k g a b)
    (heq : ∀ x ∈ Set.Icc a b, f x = g x) :
    Riemann.integral k f hf = Riemann.integral k g hg := by
  cases k with
  | real =>
    change Riemann.realIntegral f hf = Riemann.realIntegral g hg
    have heq : ∀ x ∈ Set.Icc a b, (show ℝ from f x) = (show ℝ from g x) := heq
    exact le_antisymm
      (Riemann.realIntegral_mono f g hf hg (fun x hx => (heq x hx).le))
      (Riemann.realIntegral_mono g f hg hf (fun x hx => (heq x hx).ge))
  | complex =>
    have hre : Riemann.realIntegral (fun x => (f x).re) hf.1 =
        Riemann.realIntegral (fun x => (g x).re) hg.1 :=
      le_antisymm
        (Riemann.realIntegral_mono _ _ hf.1 hg.1 (fun x hx => (congrArg Complex.re (heq x hx)).le))
        (Riemann.realIntegral_mono _ _ hg.1 hf.1 (fun x hx => (congrArg Complex.re (heq x hx)).ge))
    have him : Riemann.realIntegral (fun x => (f x).im) hf.2 =
        Riemann.realIntegral (fun x => (g x).im) hg.2 :=
      le_antisymm
        (Riemann.realIntegral_mono _ _ hf.2 hg.2 (fun x hx => (congrArg Complex.im (heq x hx)).le))
        (Riemann.realIntegral_mono _ _ hg.2 hf.2 (fun x hx => (congrArg Complex.im (heq x hx)).ge))
    change (Riemann.realIntegral _ hf.1 : ℂ) + (Riemann.realIntegral _ hf.2 : ℂ) * Complex.I =
      (Riemann.realIntegral _ hg.1 : ℂ) + (Riemann.realIntegral _ hg.2 : ℂ) * Complex.I
    rw [hre, him]

/-- The proper rectangle theorem applies to the original ambient sections, even
when integrability witnesses are supplied only for a parameter subset. -/
theorem continuous_integral_on_subset_of_rectangle (k : ScalarKind)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ → Set.Icc c d → Specs.SingleVariableAnalysis.Ch01.Scalar.scalarValue k)
    (hf : Continuous (fun p : Set.Icc a b × Set.Icc c d => f p.1.val p.2))
    (N : Set (Set.Icc c d))
    (h : ∀ t : N, Riemann.Integrable k (fun x => f x t.val) a b) :
    Continuous (fun t : N => Riemann.integral k (fun x => f x t.val) (h t)) := by
  cases k with
  | real =>
    let v : Set.Icc a b → Set.Icc c d → ℝ := fun x t => f x.val t
    obtain ⟨hs, hC⟩ := real_rectangle_continuity hab hcd v hf
    apply (hC.comp continuous_subtype_val).congr
    intro t
    exact scalar_integral_congr_on .real (hs t.val) (h t)
      (fun x hx => section_on_interval .real v t.val ⟨x, hx⟩)
  | complex =>
    let v : Set.Icc a b → Set.Icc c d → ℂ := fun x t => f x.val t
    obtain ⟨hs, hC⟩ := complex_rectangle_continuity hab hcd v hf
    apply (hC.comp continuous_subtype_val).congr
    intro t
    exact scalar_integral_congr_on .complex (hs t.val) (h t)
      (fun x hx => section_on_interval .complex v t.val ⟨x, hx⟩)

theorem right_improper_rectangle_continuity :
    Specs.SingleVariableAnalysis.Ch14.ImproperContinuity.rightRectangleContinuity := by
  intro k c d hcd N t₀ hN f a b F hlim hjoint
  obtain ⟨h, hF⟩ := hlim
  apply right_improper_continuity k N t₀ hN f a b F h ⟨h, hF⟩
  intro R
  exact (continuous_integral_on_subset_of_rectangle k R.property.1.le hcd f
    (hjoint R) N (fun t => (h.2 t).2 R)).continuousAt

theorem left_improper_rectangle_continuity :
    Specs.SingleVariableAnalysis.Ch14.ImproperContinuity.leftRectangleContinuity := by
  intro k c d hcd N t₀ hN f a b F hlim hjoint
  obtain ⟨h, hF⟩ := hlim
  apply left_improper_continuity k N t₀ hN f a b F h ⟨h, hF⟩
  intro R
  exact (continuous_integral_on_subset_of_rectangle k R.property.2.le hcd f
    (hjoint R) N (fun t => (h.2 t).2 R)).continuousAt

end SingleVariableAnalysis.ParameterIntegral
