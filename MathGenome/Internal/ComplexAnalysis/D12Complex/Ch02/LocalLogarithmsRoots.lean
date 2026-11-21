import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.LocalLogarithmsRoots
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PrincipalLogarithm
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.LimitsCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Local branches constructed from the slit logarithm, without the general
inverse function theorem. The normalization sends the base value to one. -/

noncomputable section
open scoped Topology
open Filter

namespace D12Complex.LocalLogarithmsRoots

private theorem one_mem_slit : (1 : ℂ) ∈ PrincipalSlitPlane := by
  exact (PrincipalLogarithm.mem_principalSlitPlane_iff 1).mpr (Or.inl (by norm_num))

/-- The normalized slit-logarithm construction, on an open neighborhood.
Its derivative is the logarithmic derivative of the original function. -/
theorem normalized_logarithm (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ)
    (hf : HolomorphicOn Ω f) (ha : a ∈ Ω) (hne : f a ≠ 0) :
    ∃ U : Set ℂ, a ∈ U ∧ U ⊆ Ω ∧
      HolomorphicOn U (fun z => PrincipalLog (f z / f a)) ∧
      PrincipalLog (f a / f a) = 0 ∧
      (∀ z ∈ U, E (PrincipalLog (f z / f a)) = f z / f a) ∧
      (∀ z ∈ U, HasDerivAt (fun w => PrincipalLog (f w / f a))
        (deriv f z / f z) z) := by
  let U := {z ∈ Ω | f z / f a ∈ PrincipalSlitPlane}
  have hc : ContinuousOn (fun z => f z / f a) Ω :=
    fun z hz => ((hf.2 z hz).continuousAt.div_const (f a)).continuousWithinAt
  have hU : IsOpen U := hc.isOpen_inter_preimage hf.1
    PrincipalLogarithm.isOpen_principalSlitPlane
  have hd : ∀ z ∈ U, HasDerivAt (fun w => PrincipalLog (f w / f a))
      (deriv f z / f z) z := by
    intro z hz
    have hnz : f z ≠ 0 := by
      have := PrincipalLogarithm.principalSlitPlane_ne_zero _ hz.2
      exact fun h => this (by rw [h, zero_div])
    have h := (PrincipalLogarithm.hasDerivAt_principalLog _ hz.2).comp z
      ((hf.2 z hz.1).hasDerivAt.div_const (f a))
    have heq : 1 / (f z / f a) * (deriv f z / f a) = deriv f z / f z := by
      field_simp
    rw [heq] at h
    exact h
  refine ⟨U, ?_, fun _ hz => hz.1, ⟨hU, fun z hz => (hd z hz).differentiableAt⟩,
    ?_, fun z hz => PrincipalLogarithm.E_principalLog _ hz.2, hd⟩
  · exact ⟨ha, by simpa [div_self hne] using one_mem_slit⟩
  · rw [div_self hne]
    exact PrincipalLogarithm.principalLog_one

theorem local_logarithm :
    Specs.D12Complex.Ch02.LocalLogarithmsRoots.local_logarithm_type := by
  intro Ω f a c hf ha hne hc
  obtain ⟨U, haU, hUΩ, hlog, hzero, hE, hd⟩ := normalized_logarithm Ω f a hf ha hne
  refine ⟨U, fun z => c + PrincipalLog (f z / f a), haU, hUΩ,
    ⟨hlog.1, fun z hz => (hlog.2 z hz).const_add c⟩, ?_, ?_, ?_⟩
  · simp only [hzero, add_zero]
  · intro z hz
    rw [Exponential.E_add, hc, hE z hz]
    exact mul_div_cancel₀ (f z) hne
  · intro z hz
    exact (hd z hz).const_add c

theorem local_root :
    Specs.D12Complex.Ch02.LocalLogarithmsRoots.local_root_type := by
  intro Ω f a n c₀ hf ha hne hn hc₀
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  obtain ⟨U, haU, hUΩ, hlog, hzero, hE, _⟩ := normalized_logarithm Ω f a hf ha hne
  refine ⟨U, fun z => c₀ * E (PrincipalLog (f z / f a) / n), haU, hUΩ,
    ⟨hlog.1, ?_⟩, ?_, ?_⟩
  · intro z hz
    exact ((Exponential.hasDerivAt_E _).differentiableAt.comp z
      ((hlog.2 z hz).div_const (n : ℂ))).const_mul c₀
  · change c₀ * E (PrincipalLog (f a / f a) / n) = c₀
    rw [hzero, zero_div, Exponential.E_eq_exp, Complex.exp_zero, mul_one]
  · intro z hz
    rw [mul_pow, hc₀, Exponential.E_eq_exp, ← Complex.exp_nat_mul,
      mul_div_cancel₀ _ hn0, ← Exponential.E_eq_exp, hE z hz]
    exact mul_div_cancel₀ (f z) hne

/-- Turn already proved local inverse identities into neighborhoods on which
the maps are biholomorphic. This is only a shrinking argument in topology. -/
private theorem restrict_inverse (f g : ℂ → ℂ) (a b : ℂ) (V₀ : Set ℂ)
    (hf : ∀ z, DifferentiableAt ℂ f z) (hg : HolomorphicOn V₀ g)
    (hb : b ∈ V₀) (hfa : f a = b) (hgb : g b = a)
    (hr : ∀ y ∈ V₀, f (g y) = y)
    (hl : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    ∃ U V : Set ℂ, a ∈ U ∧ b ∈ V ∧ V ⊆ V₀ ∧ BiholomorphicPair U V f g := by
  obtain ⟨W, hW, hoW, haW⟩ := eventually_nhds_iff.mp hl
  have hgW : g ⁻¹' W ∈ 𝓝 b := by
    have ht : Tendsto g (𝓝 b) (𝓝 (g b)) := (hg.2 b hb).continuousAt
    rw [hgb] at ht
    exact ht (hoW.mem_nhds haW)
  let V := V₀ ∩ interior (g ⁻¹' W)
  have hoV : IsOpen V := hg.1.inter isOpen_interior
  have hbV : b ∈ V := ⟨hb, mem_interior_iff_mem_nhds.mpr hgW⟩
  let U := W ∩ f ⁻¹' V
  have hoU : IsOpen U := hoW.inter (hoV.preimage (continuous_iff_continuousAt.mpr
    (fun z => (hf z).continuousAt)))
  refine ⟨U, V, ⟨haW, by simpa [hfa] using hbV⟩, hbV,
    fun _ hy => hy.1, ⟨⟨hoU, fun z _ => hf z⟩,
    ⟨hoV, fun y hy => hg.2 y hy.1⟩,
    fun _ hx => hx.2, ?_, fun x hx => hW x hx.1, fun y hy => hr y hy.1⟩⟩
  intro y hy
  exact ⟨interior_subset (s := g ⁻¹' W) hy.2,
    by simpa [hr y hy.1] using hy⟩

private theorem zero_mem_strip : (0 : ℂ) ∈ PrincipalStrip := by
  change |(0 : ℂ).im| < Real.pi
  simpa using Real.pi_pos

theorem exponential_local_inverse :
    Specs.D12Complex.Ch02.LocalLogarithmsRoots.exponential_local_inverse_type := by
  intro b c hc
  have hb0 : b ≠ 0 := hc ▸ Exponential.E_ne_zero c
  have hid : HolomorphicOn Set.univ (fun z : ℂ => z) :=
    ⟨isOpen_univ, fun z _ => differentiableAt_id⟩
  obtain ⟨V₀, hb, _, hlog, hzero, hE, hd⟩ :=
    normalized_logarithm Set.univ (fun z => z) b hid (Set.mem_univ _) hb0
  let L := fun w => c + PrincipalLog (w / b)
  have hL : HolomorphicOn V₀ L :=
    ⟨hlog.1, fun w hw => (hlog.2 w hw).const_add c⟩
  have hLb : L b = c := by simp [L, hzero]
  have hr : ∀ w ∈ V₀, E (L w) = w := by
    intro w hw
    dsimp [L]
    rw [Exponential.E_add, hc, hE w hw]
    exact mul_div_cancel₀ w hb0
  have hl : ∀ᶠ z in 𝓝 c, L (E z) = z := by
    have ht : ContinuousAt (fun z : ℂ => z - c) c := continuousAt_id.sub_const c
    have hs : ∀ᶠ z in 𝓝 c, z - c ∈ PrincipalStrip :=
      ht (by simpa using PrincipalLogarithm.isOpen_principalStrip.mem_nhds zero_mem_strip)
    filter_upwards [hs] with z hz
    have he : E z / b = E (z - c) := by
      rw [← hc, Exponential.E_eq_exp, Complex.exp_sub]
    dsimp [L]
    rw [he, PrincipalLogarithm.principalLog_E _ hz]
    ring
  obtain ⟨U, V, hcU, hbV, hVV₀, hpair⟩ := restrict_inverse E L c b V₀
    (fun z => (Exponential.hasDerivAt_E z).differentiableAt) hL hb hc hLb hr hl
  refine ⟨U, V, L, hcU, hbV, hLb, hpair, ?_⟩
  intro w hw
  have hdw := (hd w (hVV₀ hw)).const_add c
  simpa only [deriv_id''] using hdw

theorem power_local_inverse :
    Specs.D12Complex.Ch02.LocalLogarithmsRoots.power_local_inverse_type := by
  intro n c hn hc
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc
  have hid : HolomorphicOn Set.univ (fun z : ℂ => z) :=
    ⟨isOpen_univ, fun z _ => differentiableAt_id⟩
  obtain ⟨V₀, hb, _, hlog, hzero, hE, _⟩ :=
    normalized_logarithm Set.univ (fun z => z) (c ^ n) hid (Set.mem_univ _) hcn
  let g := fun w => c * E (PrincipalLog (w / c ^ n) / n)
  have hg : HolomorphicOn V₀ g := by
    refine ⟨hlog.1, fun w hw => ?_⟩
    exact ((Exponential.hasDerivAt_E _).differentiableAt.comp w
      ((hlog.2 w hw).div_const (n : ℂ))).const_mul c
  have hgb : g (c ^ n) = c := by
    dsimp [g]
    rw [hzero, zero_div, Exponential.E_eq_exp, Complex.exp_zero, mul_one]
  have hr : ∀ w ∈ V₀, (g w) ^ n = w := by
    intro w hw
    dsimp [g]
    rw [mul_pow, Exponential.E_eq_exp, ← Complex.exp_nat_mul,
      mul_div_cancel₀ _ hn0, ← Exponential.E_eq_exp, hE w hw]
    exact mul_div_cancel₀ w hcn
  have hl : ∀ᶠ z in 𝓝 c, g (z ^ n) = z := by
    have hcslit : c / c ∈ PrincipalSlitPlane := by
      simpa only [div_self hc] using one_mem_slit
    have hratio : ContinuousAt (fun z : ℂ => z / c) c := continuousAt_id.div_const c
    have hlogc : ContinuousAt (fun z : ℂ => PrincipalLog (z / c)) c :=
      ContinuousAt.comp (f := fun z : ℂ => z / c) (g := PrincipalLog)
        (PrincipalLogarithm.hasDerivAt_principalLog _ hcslit).continuousAt hratio
    have hstrip : (n : ℂ) * PrincipalLog (c / c) ∈ PrincipalStrip := by
      rw [div_self hc, PrincipalLogarithm.principalLog_one, mul_zero]
      exact zero_mem_strip
    have hs : ∀ᶠ z in 𝓝 c, (n : ℂ) * PrincipalLog (z / c) ∈ PrincipalStrip :=
      (hlogc.const_mul (n : ℂ))
        (PrincipalLogarithm.isOpen_principalStrip.mem_nhds hstrip)
    have hq : ∀ᶠ z in 𝓝 c, z / c ∈ PrincipalSlitPlane :=
      hratio (PrincipalLogarithm.isOpen_principalSlitPlane.mem_nhds hcslit)
    filter_upwards [hs, hq] with z hz hzs
    have he : E ((n : ℂ) * PrincipalLog (z / c)) = (z / c) ^ n := by
      rw [Exponential.E_eq_exp, Complex.exp_nat_mul, ← Exponential.E_eq_exp,
        PrincipalLogarithm.E_principalLog _ hzs]
    have heq : PrincipalLog (z ^ n / c ^ n) = (n : ℂ) * PrincipalLog (z / c) := by
      rw [← div_pow, ← he]
      exact PrincipalLogarithm.principalLog_E _ hz
    dsimp [g]
    rw [heq, mul_div_cancel_left₀ _ hn0, PrincipalLogarithm.E_principalLog _ hzs]
    exact mul_div_cancel₀ z hc
  obtain ⟨U, V, hcU, hbV, _, hpair⟩ := restrict_inverse (fun z => z ^ n) g c (c ^ n) V₀
    (fun z => (hasDerivAt_pow n z).differentiableAt) hg hb rfl hgb hr hl
  exact ⟨U, V, g, hcU, hbV, hgb, hpair⟩

end D12Complex.LocalLogarithmsRoots
