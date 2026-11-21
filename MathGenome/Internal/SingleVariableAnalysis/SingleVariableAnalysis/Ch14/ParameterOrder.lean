import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ParameterOrder
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperOrder
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ImproperContinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.UniformStability

/-! Parameter integration of a uniformly convergent improper Riemann family.
The proof samples cutoffs to obtain integrability of the uniform limit, and
uses a uniform proper-integral error bound for every real cutoff to obtain
the full improper limit. All finite order identities use the upstream
Darboux rectangle theorem, without a measure-integral bridge.
-/
namespace SingleVariableAnalysis.ParameterIntegral
open scoped Topology
open Riemann Riemann.Improper
open Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open Specs.SingleVariableAnalysis.Ch14.UniformImproper
namespace PO
export Specs.SingleVariableAnalysis.Ch14.ParameterOrder
  (truncatedFamily parameterIntegral orderConclusion)
end PO

/-- Uniform approximation of integrable functions gives integrability, even
when the approximants are indexed by arbitrary real cutoffs. -/
theorem scalar_integrable_of_uniform_approximation (k : ScalarKind) {c d : ℝ}
    (hcd : c ≤ d) (F : ℝ → S.scalarValue k)
    (A : ℕ → ℝ → S.scalarValue k)
    (hA : ∀ n, Integrable k (A n) c d)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ t : Set.Icc c d, ‖A n t - F t‖ < ε) : Integrable k F c d := by
  cases k with
  | real => exact (real_uniform_stability A F hcd hA hu).choose
  | complex => exact (complex_uniform_stability A F hcd hA hu).choose

/-- A constant uniform error bounds the difference of proper integrals. -/
theorem scalar_integral_difference_le (k : ScalarKind) {c d M : ℝ}
    {f g : ℝ → S.scalarValue k} (hf : Integrable k f c d) (hg : Integrable k g c d)
    (hb : ∀ t ∈ Set.Icc c d, ‖f t - g t‖ ≤ M) :
    ‖integral k f hf - integral k g hg‖ ≤ (d - c) * M := by
  cases k with
  | real => exact real_integral_difference_le hf hg hb
  | complex =>
    obtain ⟨hd, hv⟩ := complex_sub_value hf hg
    obtain ⟨hn, hnorm, _⟩ := complex_norm_estimate _ hd
    change ‖complexIntegral f hf - complexIntegral g hg‖ ≤ _
    rw [← hv]
    exact hnorm.trans (realIntegral_le_mul_bound hn hb)

/-- The abstract truncation argument requires no absolute convergence. -/
theorem improper_parameter_order_abstract :
    Specs.SingleVariableAnalysis.Ch14.ParameterOrder.abstractOrder := by
  intro k a c d hcd f F h H ht hH hlim hproper
  classical
  obtain ⟨h', hu⟩ := hlim
  choose hFR hHR heq using hproper
  let Rn : ℕ → rightIndexValue a ⊤ := fun n =>
    ⟨a + (n : ℝ) + 1, by linarith [Nat.cast_nonneg (α := ℝ) n], WithTop.coe_lt_top _⟩
  have hseq : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ t : Set.Icc c d,
        ‖PO.truncatedFamily k f h (Rn n) t - O.intervalExtension F t‖ < ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := hu ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (r.val - a)
    refine ⟨N, fun n hn t => ?_⟩
    have hnr : r.val < (Rn n).val := by
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      dsimp [Rn]
      linarith
    have he := hr (Rn n) hnr t
    simpa only [PO.truncatedFamily, intervalExtension_on, dist_eq_norm,
      rightTruncationValue] using he
  have hF : Integrable k (O.intervalExtension F) c d :=
    scalar_integrable_of_uniform_approximation k hcd _ _ (fun n => hFR (Rn n)) hseq
  have hlimH : RightHasIntegral k H a ⊤ (integral k (O.intervalExtension F) hF) := by
    refine ⟨⟨WithTop.coe_lt_top _, hHR⟩, ?_⟩
    intro ε hε
    let η := ε / (d - c + 1)
    have hlen : 0 < d - c + 1 := by linarith
    have hη : 0 < η := div_pos hε hlen
    have hηeq : η * (d - c + 1) = ε := div_mul_cancel₀ _ hlen.ne'
    obtain ⟨r, hr⟩ := hu η hη
    refine ⟨r, fun R hR => ?_⟩
    have hb : ∀ t ∈ Set.Icc c d,
        ‖PO.truncatedFamily k f h R t - O.intervalExtension F t‖ ≤ η := by
      intro t ht
      have he := hr R hR ⟨t, ht⟩
      have hv : PO.truncatedFamily k f h R t =
          rightTruncationValue k (fun x => f x ⟨t, ht⟩) a ⊤ (h.2 ⟨t, ht⟩) R :=
        intervalExtension_on _ ⟨t, ht⟩
      rw [hv, show O.intervalExtension F t = F ⟨t, ht⟩ from intervalExtension_on F ⟨t, ht⟩]
      simpa only [dist_eq_norm, rightTruncationValue] using he.le
    have he := scalar_integral_difference_le k (hFR R) hF hb
    change dist (integral k H (hHR R)) (integral k (O.intervalExtension F) hF) < ε
    change dist (I.scalarIntegralValue k H (hHR R))
      (I.scalarIntegralValue k (O.intervalExtension F) hF) < ε
    rw [heq R, dist_eq_norm]
    have hsmall : (d - c) * η < ε := by nlinarith
    exact he.trans_lt hsmall
  refine ⟨hF, hlimH, ⟨_, hlimH⟩, ?_⟩
  exact (right_integral_eq k H a ⊤ ⟨_, hlimH⟩ _ hlimH).symm

/-- The two scalar cases of proper rectangle continuity share one interface. -/
theorem scalar_rectangle_continuity (k : ScalarKind) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (f : Set.Icc a b → Set.Icc c d → S.scalarValue k)
    (hf : Continuous (Function.uncurry f)) :
    ∃ hx : ∀ t, Integrable k (parameterSection k f t) a b,
      Continuous (fun t => integral k (parameterSection k f t) (hx t)) := by
  cases k with
  | real => exact real_rectangle_continuity hab hcd f hf
  | complex => exact complex_rectangle_continuity hab hcd f hf

/-- The two proper order theorems, expressed with the same scalar API. -/
theorem scalar_rectangle_order (k : ScalarKind) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (f : Set.Icc a b → Set.Icc c d → S.scalarValue k)
    (hf : Continuous (Function.uncurry f)) :
    ∃ (hx : ∀ t, Integrable k (parameterSection k f t) a b)
      (ht : ∀ x, Integrable k (parameterSection k (fun t x => f x t) x) c d),
    ∃ (hA : Integrable k (O.intervalExtension
        (fun t => integral k (parameterSection k f t) (hx t))) c d)
      (hB : Integrable k (O.intervalExtension
        (fun x => integral k (parameterSection k (fun t x => f x t) x) (ht x))) a b),
      integral k _ hA = integral k _ hB := by
  cases k with
  | real => exact real_proper_order hab hcd f hf
  | complex => exact complex_proper_order hab hcd f hf

theorem scalar_integrable_of_continuousOn (k : ScalarKind) {a b : ℝ}
    (hab : a ≤ b) {g : ℝ → S.scalarValue k}
    (hg : ContinuousOn g (Set.Icc a b)) : Integrable k g a b := by
  cases k with
  | real => exact real_integrable_of_continuousOn hab hg
  | complex =>
    exact ⟨real_integrable_of_continuousOn hab (Complex.continuous_re.comp_continuousOn hg),
      real_integrable_of_continuousOn hab (Complex.continuous_im.comp_continuousOn hg)⟩

theorem scalar_intervalExtension_integrable (k : ScalarKind) {a b : ℝ}
    (hab : a ≤ b) {g : Set.Icc a b → S.scalarValue k} (hg : Continuous g) :
    Integrable k (O.intervalExtension g) a b :=
  scalar_integrable_of_continuousOn k hab
    (continuousOn_of_section_agreement hg (intervalExtension_on g))

/-- Joint continuity supplies every proper hypothesis of the abstract result.
In particular the parameter integral is locally properly integrable in x. -/
theorem improper_parameter_order :
    Specs.SingleVariableAnalysis.Ch14.ParameterOrder.continuousOrder := by
  intro k a c d hcd f F hjoint hlim
  classical
  obtain ⟨h, hu⟩ := hlim
  have ht (x : ℝ) (hx : a ≤ x) :
      Integrable k (O.intervalExtension (f x)) c d := by
    let R : rightIndexValue a ⊤ := ⟨x + 1, by linarith, WithTop.coe_lt_top _⟩
    have hc : Continuous (f x) := (hjoint R).comp
      (continuous_const.prodMk continuous_id :
        Continuous (fun t : Set.Icc c d => ((⟨x, hx, by dsimp [R]; linarith⟩ : Set.Icc a R.val), t)))
    exact scalar_intervalExtension_integrable k hcd hc
  let H := PO.parameterIntegral k f ht
  have hH (x : ℝ) (hx : a ≤ x) :
      H x = integral k (O.intervalExtension (f x)) (ht x hx) := by
    dsimp [H, PO.parameterIntegral]
    rw [dite_eq_left hx]
  refine ⟨ht, improper_parameter_order_abstract k hcd f F h H ht hH ⟨h, hu⟩ ?_⟩
  intro R
  let v : Set.Icc a R.val → Set.Icc c d → S.scalarValue k := fun x t => f x.val t
  have hv : Continuous (Function.uncurry v) := hjoint R
  obtain ⟨hxO, htO, hA, hB, horder⟩ :=
    scalar_rectangle_order k R.property.1.le hcd v hv
  obtain ⟨hxC, hAC⟩ := scalar_rectangle_continuity k R.property.1.le hcd v hv
  obtain ⟨htC, hBC⟩ := scalar_rectangle_continuity k hcd R.property.1.le
    (fun t x => v x t) (hv.comp continuous_swap)
  let A := fun t => integral k (parameterSection k v t) (hxO t)
  let B := fun x => integral k (parameterSection k (fun t x => v x t) x) (htO x)
  have hAval (t : Set.Icc c d) :
      A t = rightTruncationValue k (fun x => f x t) a ⊤ (h.2 t) R := by
    exact scalar_integral_congr_on k (hxO t) ((h.2 t).2 R)
      (fun x hx => section_on_interval k v t ⟨x, hx⟩)
  have hBval (x : Set.Icc a R.val) : B x = H x := by
    rw [hH x x.property.1]
    apply scalar_integral_congr_on k (htO x) (ht x x.property.1)
    intro t ht
    rw [show parameterSection k (fun t x => v x t) x t = v x ⟨t, ht⟩ from
      section_on_interval k (fun t x => v x t) x ⟨t, ht⟩,
      show O.intervalExtension (f x.val) t = f x.val ⟨t, ht⟩ from
        intervalExtension_on (f x.val) ⟨t, ht⟩]
  have hFR : Integrable k (PO.truncatedFamily k f h R) c d :=
    scalar_intervalExtension_integrable k hcd (hAC.congr hAval)
  have hHR : Integrable k H a R.val := scalar_integrable_of_continuousOn k
    R.property.1.le (continuousOn_of_section_agreement
      (hBC.congr hBval) (fun _ => rfl))
  refine ⟨hFR, hHR, ?_⟩
  calc
    integral k H hHR = integral k (O.intervalExtension B) hB :=
      scalar_integral_congr_on k hHR hB (fun x hx => by
        rw [show O.intervalExtension B x = B ⟨x, hx⟩ from intervalExtension_on B ⟨x, hx⟩]
        exact (hBval ⟨x, hx⟩).symm)
    _ = integral k (O.intervalExtension A) hA := horder.symm
    _ = integral k (PO.truncatedFamily k f h R) hFR :=
      scalar_integral_congr_on k hA hFR (fun t ht => by
        rw [show O.intervalExtension A t = A ⟨t, ht⟩ from intervalExtension_on A ⟨t, ht⟩,
          show PO.truncatedFamily k f h R t =
            rightTruncationValue k (fun x => f x ⟨t, ht⟩) a ⊤ (h.2 ⟨t, ht⟩) R from
              intervalExtension_on _ ⟨t, ht⟩]
        exact hAval ⟨t, ht⟩)

end SingleVariableAnalysis.ParameterIntegral
