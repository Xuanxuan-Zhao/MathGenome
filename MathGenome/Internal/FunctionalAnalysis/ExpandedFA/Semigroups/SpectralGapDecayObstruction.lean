import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SpectralGapDecayObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.NormalSemigroups
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.ResolventDecayObstruction

noncomputable section
open MeasureTheory Filter Topology Set

namespace ExpandedFA.Semigroups.SpectralGapDecay
open Unbounded Unbounded.OperatorDomainsSpec Unbounded.HilbertAdjointSpec
open Unbounded.MeasurableSpectralCalculus Unbounded.UnboundedNormalSpectralTheorem
open Unbounded.UnboundedNormalSpectralTheorem.SpectralRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The cutoff inverse used to construct the resolvent also retains the
quantitative bound at the edge of an open spectral gap. -/
theorem resolvent_bound_of_null_ball {E : SpectralMeasure.ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (z : ℂ) (d : ℝ) (hd : 0 < d)
    (hnull : E (Metric.ball z d) = 0) :
    z ∈ resolventSetValue (measurableIntegral C id) ∧
    ‖resolventValue z (measurableIntegral C id)‖ ≤ 1 / d := by
  classical
  have hres := resolvent_of_gap C z d hd hnull
  refine ⟨hres, ?_⟩
  let B := Metric.ball z d
  let g : ℂ → ℂ := Bᶜ.indicator (fun w => (z - w)⁻¹)
  let a : ℂ → ℂ := Bᶜ.indicator (fun _ => 1)
  have hB : MeasurableSet B := measurableSet_ball
  have ha : SpectralMeasure.Spec.IsBoundedMeasurable a :=
    SpectralMeasure.BorelNormSpectrum.bounded_indicator _ hB.compl
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1)
  have hdist (w : ℂ) (hw : w ∉ B) : d ≤ ‖z - w‖ := by
    apply le_of_not_gt
    intro hh
    exact hw (by simpa [B, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hh)
  have hne (w : ℂ) (hw : w ∉ B) : z - w ≠ 0 :=
    norm_pos_iff.mp (hd.trans_le (hdist w hw))
  have hgpoint (w : ℂ) : ‖g w‖ ≤ d⁻¹ := by
    by_cases hw : w ∈ B
    · simp [g, hw, hd.le]
    · simpa [g, hw, norm_inv] using inv_anti₀ hd (hdist w hw)
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g :=
    ⟨(measurable_const.sub measurable_id).inv.indicator hB.compl, d⁻¹, hgpoint⟩
  have hprod : id * g = z • g - a := by
    funext w
    by_cases hw : w ∈ B
    · simp [g, a, hw]
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        g, a, id_eq, Set.indicator_of_mem (mem_compl hw)]
      field_simp [hne w hw]
      ring
  have hfg : SpectralMeasure.Spec.IsBoundedMeasurable (id * g) := by
    rw [hprod]
    exact SpectralMeasure.BorelNormSpectrum.bounded_sub (hg.smul z) ha
  have hia : C.integral a = 1 := by
    rw [integral_eq C _ ha, ← E.spectralIntegral_one]
    exact SpectralMeasure.BorelNormSpectrum.integral_congr_of_null E hB hnull ha
      (SpectralMeasure.BorelNormSpectrum.bounded_const 1) (fun w hw => by simp [a, hw])
  have hifg : C.integral (id * g) = z • C.integral g - 1 := by
    rw [hprod, C.sub _ _ (hg.smul z) ha, C.smul z g hg, hia]
  let A := measurableIntegral C id
  have hgraph (y : H) : (C.integral g y, C.integral (id * g) y) ∈ A.graph :=
    bounded_product_graph C measurable_id hg hfg y
  have hmem (y : H) : C.integral g y ∈ A.domain :=
    LinearPMap.mem_domain_of_mem_graph (hgraph y)
  have heval (y : H) : A ⟨C.integral g y, hmem y⟩ = z • C.integral g y - y := by
    have hh := A.mem_graph_snd_inj (A.mem_graph ⟨_, hmem y⟩) (hgraph y) rfl
    rw [hh, hifg]
    rfl
  have heq : resolventValue z A = C.integral g := by
    ext y
    have hleft := hres.some.left_inverse ⟨C.integral g y, hmem y⟩
    change hres.some.inverse (z • C.integral g y - A ⟨C.integral g y, hmem y⟩) =
      C.integral g y at hleft
    rw [heval] at hleft
    have hi : z • C.integral g y - (z • C.integral g y - y) = y := by module
    rw [hi] at hleft
    unfold resolventValue
    split_ifs with h
    · exact hleft
    · exact (h hres).elim
  rw [heq]
  simpa only [one_div] using C.bound g d⁻¹ hg (inv_nonneg.mpr hd.le) hgpoint

/-- Self-adjointness forces every spectral value to be real, including
when the spectrum is empty. -/
theorem spectrum_real (G : Operator ℂ H H)
    (hd : Dense (G.domain : Set H)) (ha : adjointValue G = G) :
    ∀ z ∈ operatorSpectrum G, z.im = 0 := by
  have hc : G.IsClosed := by
    rw [← ha]
    exact LinearPMap.adjoint_isClosed hd
  have hn : productValue (adjointValue G) G = productValue G (adjointValue G) := by rw [ha]
  obtain ⟨E, hE⟩ := spectral_existence H G hd hc hn
  have hs := (spectral_uniqueness_and_support H G hd hc hn E hE).1
  have hz := real_support_of_selfAdjoint_resolves G ha E hE
  intro z hspec
  by_contra hnot
  have hopen : IsOpen {w : ℂ | w.im ≠ 0} :=
    (isClosed_eq Complex.continuous_im continuous_const).isOpen_compl
  exact hs.2.2 _ hopen ⟨z, hnot, hspec⟩ hz

/-- An open real gap of half-width d leaves every point on its central
vertical line at distance at least d from the self-adjoint spectrum. -/
theorem line_bound_of_gap (G : Operator ℂ H H)
    (hdense : Dense (G.domain : Set H)) (ha : adjointValue G = G)
    (ξ d : ℝ) (hd : 0 < d)
    (hgap : ∀ s : ℝ, s ∈ Ioo (ξ - d) (ξ + d) → (s : ℂ) ∉ operatorSpectrum G) :
    WeightedResolvent.LineBound G ξ d := by
  have hc : G.IsClosed := by
    rw [← ha]
    exact LinearPMap.adjoint_isClosed hdense
  have hn : productValue (adjointValue G) G = productValue G (adjointValue G) := by rw [ha]
  obtain ⟨E, hE⟩ := spectral_existence H G hdense hc hn
  have hs := (spectral_uniqueness_and_support H G hdense hc hn E hE).1
  obtain ⟨C, hC, _⟩ := hE
  refine ⟨hd, fun τ => ?_⟩
  let z : ℂ := ξ + Complex.I * τ
  have hdis : Metric.ball z d ⊆ (operatorSpectrum G)ᶜ := by
    intro w hw hspec
    have hwim := spectrum_real G hdense ha w hspec
    have hnrm : ‖w - z‖ < d := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hre : |w.re - ξ| < d := by
      simpa [z] using (Complex.abs_re_le_norm (w - z)).trans_lt hnrm
    have hI : w.re ∈ Ioo (ξ - d) (ξ + d) := by
      have hh := abs_lt.mp hre
      constructor <;> linarith
    have heq : (w.re : ℂ) = w := by
      apply Complex.ext <;> simp [hwim]
    exact hgap w.re hI (heq.symm ▸ hspec)
  have hnull : E (Metric.ball z d) = 0 := by
    have hinter := E.inter (Metric.ball z d) (operatorSpectrum G)ᶜ
      measurableSet_ball hs.1.measurableSet.compl
    rw [inter_eq_left.mpr hdis, hs.2.1, mul_zero] at hinter
    exact hinter.symm
  have hC' : measurableIntegral C id = G := hC
  have hresult := resolvent_bound_of_null_ball C z d hd hnull
  rw [hC'] at hresult
  exact hresult

theorem generation_and_lines : Spec.GenerationAndLines := by
  intro H _ _ _ G hdense ha hupper ξ hξ d hd hgap
  have hc : G.IsClosed := by
    rw [← ha]
    exact LinearPMap.adjoint_isClosed hdense
  have hn : productValue (adjointValue G) G = productValue G (adjointValue G) := by rw [ha]
  obtain ⟨ω, hω⟩ := hupper
  have hbound : NormalSemigroups.HasSpectralUpperBound G :=
    ⟨ω, NormalSemigroups.spectral_upper_of_numerical G hdense hc hn ω hω⟩
  obtain ⟨T, _, hT, _⟩ := NormalSemigroups.converse H G hdense hc hn hbound
  exact ⟨⟨T, hT.symm⟩, fun n => line_bound_of_gap G hdense ha (ξ n) d hd (hgap n)⟩

theorem spectral_gap_decay_obstruction : Spec.DecayObstruction := by
  intro H _ _ _ G hdense ha hupper ξ hξ d hd hgap
  obtain ⟨⟨T, hT⟩, hlines⟩ := generation_and_lines G hdense ha hupper ξ hξ d hd hgap
  exact ResolventDecay.resolvent_decay_obstruction G T hT ξ hξ d hd hlines

end ExpandedFA.Semigroups.SpectralGapDecay
