import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.Ekeland
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Ekeland

noncomputable section
open Set Filter
open scoped Topology
universe u
namespace VariationalNotes.Existence
open VariationalNotes.ConvexAnalysis

/-- Inclusion in `EReal` preserves the real-sublevel convention for lower
semicontinuity, including both infinite thresholds. -/
lemma lowerSemicontinuous_toEReal {M : Type u} [TopologicalSpace M]
    (f : M → WithTop ℝ) (hf : IsLowerSemicontinuous f) :
    LowerSemicontinuous (fun x => toEReal (f x)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  induction a with
  | bot =>
    have he : (fun x => toEReal (f x)) ⁻¹' Iic ⊥ = ∅ := by
      ext x
      exact iff_false_intro (WithBot.not_coe_le_bot _)
    rw [he]
    exact isClosed_empty
  | coe r =>
    have he : (fun x => toEReal (f x)) ⁻¹' Iic (r : EReal) = sublevel f r := by
      ext x
      exact WithBot.coe_le_coe
    rw [he]
    exact (lowerSemicontinuous_iff_closed_sublevels f).mp hf r
  | top => simp

/-- Ekeland's principle with both quantitative parameters of Theorem 3.6. -/
theorem ekeland : Specs.ekeland.{u} := by
  intro M _ _ f hp hf hb ε lam hε hlam x₀ hnear
  obtain ⟨b, hb⟩ := hb
  have hbound : ∃ b : ℝ, ∀ x, (b : EReal) ≤ toEReal (f x) :=
    ⟨b, fun x => WithBot.coe_le_coe.mpr (hb x)⟩
  have hproper : ∃ x, toEReal (f x) ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hp
    refine ⟨x, ?_⟩
    intro h
    exact (ne_of_lt hx) (WithBot.coe_injective h)
  change toEReal (f x₀) ≤ (⨅ x, toEReal (f x)) + (ε : EReal) at hnear
  have hmul : ε / lam * lam = ε := div_mul_cancel₀ ε hlam.ne'
  obtain ⟨z, hd, hz, hs⟩ := ExpandedFA.P1.ekeland
    (fun x => toEReal (f x)) (lowerSemicontinuous_toEReal f hf) hbound hproper
    x₀ (ε / lam) lam (div_pos hε hlam) hlam (by simpa only [hmul] using hnear)
  exact ⟨z, WithBot.coe_le_coe.mp hz, by simpa only [dist_comm] using hd, hs⟩

/-- A local one-sided cone bound controls the norm of the derivative. -/
lemma norm_derivative_le_of_lower_cone {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : X → ℝ} {A : X →L[ℝ] ℝ} {x : X} {a : ℝ}
    (ha : 0 ≤ a) (hg : HasFDerivAt g A x)
    (hcone : ∀ᶠ y in 𝓝 x, g x - a * ‖y - x‖ ≤ g y) : ‖A‖ ≤ a := by
  have lower (v : X) : -a * ‖v‖ ≤ A v := by
    have hd : Tendsto (fun t : ℝ => t • v) (𝓝[>] 0) (𝓝 (0 : X)) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
        tendsto_id'.mpr nhdsWithin_le_nhds
      simpa using hid.smul_const v
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    have hcd : Tendsto (fun t : ℝ => t⁻¹ • (t • v)) (𝓝[>] 0) (𝓝 v) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hpos] with t ht
      simp [smul_smul, ht.ne']
    have hlim := (hasFDerivWithinAt_univ.mpr hg).lim hd
      (Eventually.of_forall fun _ => mem_univ _) hcd
    apply ge_of_tendsto hlim
    have hpath : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
      simpa using tendsto_const_nhds.add hd
    filter_upwards [hpath.eventually hcone, hpos] with t ht htp
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htp] at ht
    change -a * ‖v‖ ≤ t⁻¹ * (g (x + t • v) - g x)
    apply (le_inv_mul_iff₀ htp).mpr
    nlinarith
  apply A.opNorm_le_bound ha
  intro v
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · simpa only [neg_mul] using lower v
  · have h := lower (-v)
    simp only [norm_neg, map_neg] at h
    linarith

/-- Approximate stationarity at any point produced by Ekeland's principle. -/
theorem approximate_stationarity : Specs.approximate_stationarity.{u} := by
  intro X _ _ _ f ε lam hε hlam x hs g A heq hg
  apply norm_derivative_le_of_lower_cone (le_of_lt (div_pos hε hlam)) hg
  have hx := heq.self_of_nhds
  filter_upwards [heq] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  · have h := hs y hyx
    change ConvexAnalysis.Specs.toEReal (f x) - _ < ConvexAnalysis.Specs.toEReal (f y) at h
    rw [hx, hy] at h
    change (g x : EReal) - ((ε / lam * dist y x : ℝ) : EReal) < (g y : EReal) at h
    rw [← EReal.coe_sub] at h
    simpa only [dist_eq_norm] using (EReal.coe_lt_coe_iff.mp h).le

end VariationalNotes.Existence
