import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.ExtremalOnto
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.ExtremalUnivalent
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.DiskAutomorphisms
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.UnivalentHolomorphicInverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith

/-! The surjectivity step of D12.12.03. An omitted disk value gives a
square-root injection with a larger derivative norm. Schwarz rigidity
makes the improvement strict. Extremality therefore forces surjectivity;
the upstream univalent inverse theorem supplies the holomorphic inverse. -/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.ExtremalOnto

/-- The inverse-square disk map has derivative norm strictly below one
at its fixed origin, because squaring identifies two interior points. -/

lemma inverse_square_strict {α b : ℂ}
    (hα : α ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1)
    (hzero : DiskPhiInv α ((DiskPhiInv b 0)^2) = 0) :
    ‖deriv (fun w => DiskPhiInv α ((DiskPhiInv b w)^2)) 0‖ < 1 := by
  let ψ : ℂ → ℂ := fun w => DiskPhiInv α ((DiskPhiInv b w)^2)
  have hpα := DiskAutomorphisms.phi_biholomorphicPair α hα
  have hpb := DiskAutomorphisms.phi_biholomorphicPair b hb
  have hpow (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : w ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    have hn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg w]
  have hm : MapsTo ψ (ball 0 1) (ball 0 1) := by
    intro w hw
    exact hpα.2.2.2.1 (hpow _ (hpb.2.2.2.1 hw))
  have hh : HolomorphicOn (ball 0 1) ψ := by
    refine ⟨isOpen_ball, fun w hw => ?_⟩
    exact (hpα.2.1.2 _ (hpow _ (hpb.2.2.2.1 hw))).comp w
      ((hpb.2.1.2 w hw).pow 2)
  have hle : ‖deriv ψ 0‖ ≤ 1 := Schwarz.norm_deriv_zero_le_one ψ hh hm hzero
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨c, hc, he⟩ := Schwarz.rotation_of_norm_deriv_eq_one ψ hh hm hzero heq
  have hcn : c ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hinj : InjOn ψ (ball 0 1) := by
    intro z hz w hw hzw
    rw [he z hz, he w hw] at hzw
    exact mul_left_cancel₀ hcn hzw
  have hu : (1 / 2 : ℂ) ∈ ball 0 1 := by
    norm_num [mem_ball_zero_iff, norm_div]
  have hv : (-(1 / 2) : ℂ) ∈ ball 0 1 := by
    simpa using hu
  have hcollision : ψ (DiskPhi b (1/2)) = ψ (DiskPhi b (-(1/2))) := by
    dsimp [ψ]
    rw [hpb.2.2.2.2.1 hu, hpb.2.2.2.2.1 hv, neg_sq]
  have heq' := hinj (hpb.2.2.1 hu) (hpb.2.2.1 hv) hcollision
  have heq'' := congrArg (DiskPhiInv b) heq'
  rw [hpb.2.2.2.2.1 hu, hpb.2.2.2.2.1 hv] at heq''
  norm_num at heq''

lemma derivative_improves_of_factor {Ω : Set ℂ} {z₀ : ℂ} {F H ψ : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω) (hH : HolomorphicOn Ω H)
    (hψ : HolomorphicOn (ball 0 1) ψ) (hH0 : H z₀ = 0)
    (hfactor : EqOn F (ψ ∘ H) Ω)
    (hpositive : 0 < ‖deriv F z₀‖) (hstrict : ‖deriv ψ 0‖ < 1) :
    ‖deriv F z₀‖ < ‖deriv H z₀‖ := by
  have hdψ : HasDerivAt ψ (deriv ψ 0) (H z₀) := by
    simpa only [hH0] using
      (hψ.2 0 (mem_ball_self zero_lt_one)).hasDerivAt
  have hlocal : F =ᶠ[𝓝 z₀] (ψ ∘ H) := by
    filter_upwards [hΩ.mem_nhds hz₀] with z hz
    exact hfactor hz
  have hd : deriv F z₀ = deriv ψ 0 * deriv H z₀ :=
    ((hdψ.comp z₀ (hH.2 z₀ hz₀).hasDerivAt).congr_of_eventuallyEq hlocal).deriv
  have hn : ‖deriv F z₀‖ = ‖deriv ψ 0‖ * ‖deriv H z₀‖ := by rw [hd, norm_mul]
  have hHpos : 0 < ‖deriv H z₀‖ := by
    by_contra h
    have hz : ‖deriv H z₀‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [hz, mul_zero] at hn
    linarith
  rw [hn]
  exact mul_lt_of_lt_one_left hHpos hstrict


/-- An omitted disk value supplies a square-root injection, normalized at the
base point, through which the original disk map factors. -/
lemma omitted_square_root_factorization {Ω : Set ℂ} {z₀ : ℂ} {F : ℂ → ℂ}
    (hroot : ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, (g z) ^ 2 = f z)
    (hz₀ : z₀ ∈ Ω) (hF : HolomorphicOn Ω F)
    (hinj : InjOn F Ω) (hmaps : MapsTo F Ω (Metric.ball 0 1)) (hFzero : F z₀ = 0)
    {α : ℂ} (hα : α ∈ Metric.ball 0 1) (homit : α ∉ F '' Ω) :
    ∃ (b : ℂ) (H : ℂ → ℂ), b ∈ Metric.ball 0 1 ∧
      HolomorphicOn Ω H ∧ InjOn H Ω ∧ MapsTo H Ω (Metric.ball 0 1) ∧ H z₀ = 0 ∧
      HolomorphicOn (Metric.ball 0 1) (fun w => DiskPhiInv α ((DiskPhiInv b w) ^ 2)) ∧
      DiskPhiInv α ((DiskPhiInv b 0) ^ 2) = 0 ∧
      EqOn F (fun z => DiskPhiInv α ((DiskPhiInv b (H z)) ^ 2)) Ω := by
  have hA := DiskAutomorphisms.phi_biholomorphicPair α hα
  have hAF : HolomorphicOn Ω (fun z => DiskPhi α (F z)) :=
    ⟨hF.1, fun z hz => (hA.1.2 _ (hmaps hz)).comp z (hF.2 z hz)⟩
  have hAFzero : ∀ z ∈ Ω, DiskPhi α (F z) ≠ 0 := by
    intro z hz hzero
    have heq : F z = α := by
      have hden := DiskAutomorphisms.denominator_ne_zero α hα (F z) (hmaps hz)
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp hzero).resolve_right hden)
    exact homit ⟨z, hz, heq⟩
  obtain ⟨g, hg, hsq⟩ := hroot _ hAF hAFzero
  have hgmaps : MapsTo g Ω (Metric.ball 0 1) := by
    intro z hz
    have hn : ‖g z‖ ^ 2 < 1 := by
      rw [← norm_pow, hsq z hz]
      exact mem_ball_zero_iff.mp (hA.2.2.1 (hmaps hz))
    exact mem_ball_zero_iff.mpr (by nlinarith [norm_nonneg (g z)])
  have hginj : InjOn g Ω := by
    intro z hz w hw heq
    apply hinj hz hw
    have heq' : DiskPhi α (F z) = DiskPhi α (F w) := by rw [← hsq z hz, ← hsq w hw, heq]
    calc
      F z = DiskPhiInv α (DiskPhi α (F z)) := (hA.2.2.2.2.1 (hmaps hz)).symm
      _ = DiskPhiInv α (DiskPhi α (F w)) := congrArg _ heq'
      _ = F w := hA.2.2.2.2.1 (hmaps hw)
  let b := g z₀
  have hb : b ∈ Metric.ball 0 1 := hgmaps hz₀
  have hB := DiskAutomorphisms.phi_biholomorphicPair b hb
  let H : ℂ → ℂ := fun z => DiskPhi b (g z)
  have hH : HolomorphicOn Ω H :=
    ⟨hg.1, fun z hz => (hB.1.2 _ (hgmaps hz)).comp z (hg.2 z hz)⟩
  have hHinj : InjOn H Ω := by
    intro z hz w hw heq
    apply hginj hz hw
    calc
      g z = DiskPhiInv b (H z) := (hB.2.2.2.2.1 (hgmaps hz)).symm
      _ = DiskPhiInv b (H w) := congrArg _ heq
      _ = g w := hB.2.2.2.2.1 (hgmaps hw)
  have hHzero : H z₀ = 0 := by simp [H, DiskPhi, b]
  have hfactor : EqOn F (fun z => DiskPhiInv α ((DiskPhiInv b (H z)) ^ 2)) Ω := by
    intro z hz
    change F z = DiskPhiInv α ((DiskPhiInv b (DiskPhi b (g z))) ^ 2)
    rw [hB.2.2.2.2.1 (hgmaps hz), hsq z hz, hA.2.2.2.2.1 (hmaps hz)]
  have hpow (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) 1) : w ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    have hn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    nlinarith [norm_nonneg w]
  have hψ : HolomorphicOn (Metric.ball 0 1)
      (fun w => DiskPhiInv α ((DiskPhiInv b w) ^ 2)) := by
    refine ⟨Metric.isOpen_ball, fun w hw => ?_⟩
    exact (hA.2.1.2 _ (hpow _ (hB.2.2.2.1 hw))).comp w
      ((hB.2.1.2 w hw).pow 2)
  refine ⟨b, H, hb, hH, hHinj, (fun z hz => hB.2.2.1 (hgmaps hz)), hHzero, hψ,
    ?_, hfactor⟩
  have hz := hfactor hz₀
  simpa only [hFzero, hHzero] using hz.symm

/-- Taking a square root at an omitted target value strictly increases the
base-point derivative norm, contradicting extremality. -/
lemma omitted_value_improves {Ω : Set ℂ} {z₀ : ℂ} {F : ℂ → ℂ}
    (hroot : ∀ f : ℂ → ℂ, HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) →
      ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, (g z) ^ 2 = f z)
    (hz₀ : z₀ ∈ Ω) (hF : HolomorphicOn Ω F)
    (hinj : InjOn F Ω) (hmaps : MapsTo F Ω (Metric.ball 0 1)) (hFzero : F z₀ = 0)
    (hpositive : 0 < ‖deriv F z₀‖)
    {α : ℂ} (hα : α ∈ Metric.ball 0 1) (homit : α ∉ F '' Ω) :
    ∃ H : ℂ → ℂ, HolomorphicOn Ω H ∧ InjOn H Ω ∧
      MapsTo H Ω (Metric.ball 0 1) ∧ H z₀ = 0 ∧ ‖deriv F z₀‖ < ‖deriv H z₀‖ := by
  obtain ⟨b, H, hb, hH, hHinj, hHmaps, hHzero, hψ, hψzero, hfactor⟩ :=
    omitted_square_root_factorization hroot hz₀ hF hinj hmaps hFzero hα homit
  refine ⟨H, hH, hHinj, hHmaps, hHzero, ?_⟩
  exact derivative_improves_of_factor hF.1 hz₀ hH hψ hHzero hfactor hpositive
    (inverse_square_strict hα hb hψzero)


/-- Every extremal member of the full normalized class fills the disk,
including members whose derivative has not been rotated to be real. -/
theorem extremal_onto : Specs.D12Complex.Ch12.ExtremalOnto.extremal_onto_type := by
  intro Ω hΩ hproper hroot z₀ hz₀ F hF hmax
  change F ∈ ExtremalUnivalent.normalizedFamily Ω z₀ at hF
  change ‖deriv F z₀‖ = ExtremalUnivalent.derivativeSupremum Ω z₀ at hmax
  obtain ⟨_, hbd, hs, _⟩ :=
    ExtremalUnivalent.extremal_univalent Ω hΩ hproper hroot z₀ hz₀
  have hbd' : BddAbove (ExtremalUnivalent.derivativeNorms Ω z₀) := hbd
  have hpositive : 0 < ‖deriv F z₀‖ := by
    rw [hmax]
    exact hs
  have honto : F '' Ω = ball (0 : ℂ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hF.2.2.1 hz
    · intro α hα
      by_contra homit
      obtain ⟨H, hH, hHinj, hHmaps, hHzero, himproves⟩ :=
        omitted_value_improves hroot hz₀ hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
          hpositive hα homit
      have hHfamily : H ∈ ExtremalUnivalent.normalizedFamily Ω z₀ :=
        ⟨hH, hHinj, hHmaps, hHzero⟩
      have hle : ‖deriv H z₀‖ ≤ ExtremalUnivalent.derivativeSupremum Ω z₀ :=
        le_csSup hbd' ⟨H, hHfamily, rfl⟩
      rw [← hmax] at hle
      exact (not_lt_of_ge hle) himproves
  obtain ⟨G, hpair, _⟩ := UnivalentHolomorphicInverse.injective_holomorphic_inverse
    Ω F hΩ hF.1 hF.2.1
  rw [honto] at hpair
  exact ⟨honto, G, hpair⟩

/-- The extremal construction and surjectivity give a normalized
biholomorphism with strictly positive real derivative and a holomorphic
inverse on the entire disk. -/
theorem normalized_biholomorphism :
    Specs.D12Complex.Ch12.ExtremalOnto.normalized_biholomorphism_type := by
  intro Ω hΩ hproper hroot z₀ hz₀
  obtain ⟨_, _, hs, F, hF, hFd⟩ :=
    ExtremalUnivalent.extremal_univalent Ω hΩ hproper hroot z₀ hz₀
  have hnorm : ‖deriv F z₀‖ = ExtremalUnivalent.derivativeSupremum Ω z₀ := by
    rw [hFd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rfl
  obtain ⟨_, G, hpair⟩ := extremal_onto Ω hΩ hproper hroot z₀ hz₀ F hF hnorm
  exact ⟨F, G, hpair, hF.2.2.2,
    ExtremalUnivalent.derivativeSupremum Ω z₀, hs, hFd⟩

end D12Complex.ExtremalOnto
