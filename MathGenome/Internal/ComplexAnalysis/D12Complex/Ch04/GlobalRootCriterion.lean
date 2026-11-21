import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.GlobalRootCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexProperties
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace D12Complex.GlobalRootCriterion

lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

lemma continuous_log_derivative {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hne : ∀ z ∈ Ω, f z ≠ 0) :
    ContinuousOn (fun z => deriv f z / f z) Ω := by
  have hd := DiskCauchyDerivatives.continuousOn_iteratedDeriv Ω f hf 1
  simp only [iteratedDeriv_one] at hd
  exact hd.div (fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt) hne

/-- Weak holomorphy supplies the real C1 regularity used when mapping a contour. -/
lemma holomorphic_contDiffOn {Ω : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn Ω f) :
    ContDiffOn ℝ 1 f Ω := by
  have hd := DiskCauchyDerivatives.continuousOn_iteratedDeriv Ω f hf 1
  simp only [iteratedDeriv_one] at hd
  have hC : ContDiffOn ℂ 1 f Ω := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen hf.1]
    exact ⟨fun z hz => (hf.2 z hz).differentiableWithinAt, by simp,
      contDiffOn_zero.mpr hd⟩
  exact hC.restrict_scalars ℝ

/-- The actual composed path, with the original parameter interval. -/
def mappedPath {Ω : Set ℂ} (f : ℂ → ℂ) (hf : HolomorphicOn Ω f)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) : PiecewiseC1Path := by
  have hfc : ContinuousOn f Ω := fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt
  let δ : ComplexPath := ⟨γ.path.a, γ.path.b, γ.path.ordered, f ∘ γ,
    hfc.comp γ.path.continuousOn (fun t ht => hγ ⟨t, ht, rfl⟩)⟩
  exact ⟨δ, ⟨{
    count := γ.partition.count
    node := γ.partition.node
    strictMono := γ.partition.strictMono
    first := γ.partition.first
    last := γ.partition.last
    smooth := fun i => (holomorphic_contDiffOn hf).comp (γ.partition.smooth i)
      (fun t ht => hγ ⟨t, γ.partition.piece_subset i ht, rfl⟩)
  }⟩⟩

lemma mappedPath_closed {Ω : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn Ω f)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (hc : γ.IsClosed) :
    (mappedPath f hf γ hγ).IsClosed := congrArg f hc

lemma mappedPath_avoids_zero {Ω : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn Ω f)
    (hne : ∀ z ∈ Ω, f z ≠ 0) (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) :
    (0 : ℂ) ∉ (mappedPath f hf γ hγ).trace := by
  rintro ⟨t, ht, he⟩
  exact hne (γ t) (hγ ⟨t, ht, rfl⟩) he

/-- Change of integrand along a holomorphically mapped piecewise C1 path.
In particular this identifies the logarithmic derivative integral with the
reciprocal integral of its nonzero image path. -/
lemma integral_mappedPath {Ω : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn Ω f)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (q : ℂ → ℂ)
    (hq : ContinuousOn q (mappedPath f hf γ hγ).trace) :
    (mappedPath f hf γ hγ).integral q =
      γ.integral (fun z => q (f z) * deriv f z) := by
  let P := γ.partition
  let δ := mappedPath f hf γ hγ
  let Q : C1Partition δ.path := {
    count := P.count, node := P.node, strictMono := P.strictMono,
    first := P.first, last := P.last,
    smooth := fun i => (holomorphic_contDiffOn hf).comp (P.smooth i)
      (fun t ht => hγ ⟨t, P.piece_subset i ht, rfl⟩) }
  have hqc : ContinuousOn (fun z => q (f z) * deriv f z) γ.trace := by
    have hqf : ContinuousOn (q ∘ f) γ.trace :=
      hq.comp (fun z hz => (hf.2 z (hγ hz)).continuousAt.continuousWithinAt)
        (by rintro z ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩)
    have hd := DiskCauchyDerivatives.continuousOn_iteratedDeriv Ω f hf 1
    simp only [iteratedDeriv_one] at hd
    exact hqf.mul (hd.mono hγ)
  rw [PiecewiseC1Path.integral_eq_partition δ Q q hq,
    PiecewiseC1Path.integral_eq_partition γ P _ hqc]
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ P.pieceSet i := by simpa only [Q, uIcc_of_le (P.piece_lt i).le, C1Partition.pieceSet] using ht
  have hchain := ((hf.2 _ (hγ ⟨t, P.piece_subset i ht', rfl⟩)).hasDerivAt.complexToReal_fderiv).comp_hasDerivWithinAt t
    ((P.smooth i).differentiableOn one_ne_zero t ht').hasDerivWithinAt
  have hd : derivWithin (f ∘ γ) (P.pieceSet i) t =
      deriv f (γ t) * derivWithin γ (P.pieceSet i) t := by
    simpa only [C1Partition.pieceSet, smul_apply,
      one_apply_eq_self, smul_eq_mul] using hchain.derivWithin (uniqueDiffOn_Icc (P.piece_lt i) t ht')
  change q (f (γ t)) * derivWithin (f ∘ γ) (P.pieceSet i) t = _
  rw [hd]
  ring

lemma integral_congr (γ : PiecewiseC1Path) {p q : ℂ → ℂ}
    (hpq : EqOn p q γ.trace) : γ.integral p = γ.integral q := by
  unfold PiecewiseC1Path.integral C1Partition.integral
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hpq ⟨t, γ.partition.piece_subset i (by
    simpa only [uIcc_of_le (γ.partition.piece_lt i).le, C1Partition.pieceSet] using ht), rfl⟩]

lemma integral_const_mul (γ : PiecewiseC1Path) (p : ℂ → ℂ) (c : ℂ) :
    γ.integral (fun z => c * p z) = c * γ.integral p := by
  unfold PiecewiseC1Path.integral C1Partition.integral
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  exact (Finset.mul_sum _ _ _).symm

lemma log_derivative_integral_eq_image {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hne : ∀ z ∈ Ω, f z ≠ 0)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) :
    γ.integral (fun z => deriv f z / f z) =
      (mappedPath f hf γ hγ).integral (fun z => 1 / (z - 0)) := by
  rw [integral_mappedPath hf γ hγ _ (by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro z hz
    simpa using ne_of_mem_of_not_mem hz (mappedPath_avoids_zero hf hne γ hγ))]
  apply integral_congr
  intro z _
  simp [div_eq_mul_inv, mul_comm]

lemma exp_log_derivative_integral {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hne : ∀ z ∈ Ω, f z ≠ 0)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) :
    Complex.exp (γ.integral (fun z => deriv f z / f z)) * f γ.path.source =
      f γ.path.target := by
  rw [log_derivative_integral_eq_image hf hne γ hγ]
  simpa [mappedPath, PiecewiseC1Path.path, ComplexPath.source, ComplexPath.target] using
    IndexProperties.path_exp_reciprocal_integral (mappedPath f hf γ hγ) 0
      (mappedPath_avoids_zero hf hne γ hγ)

lemma log_derivative_integral_integer {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hne : ∀ z ∈ Ω, f z ≠ 0)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (hc : γ.IsClosed) :
    ∃ k : ℤ, γ.integral (fun z => deriv f z / f z) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [log_derivative_integral_eq_image hf hne γ hγ]
  exact IndexProperties.closed_path_integral_integer _ (mappedPath_closed hf γ hγ hc) 0
    (mappedPath_avoids_zero hf hne γ hγ)

/-- Differentiate the actual power identity locally; no derivative identity is
part of the hypotheses on a root. -/
lemma root_log_derivative {Ω : Set ℂ} {f g : ℂ → ℂ} {n : ℕ}
    (hf : HolomorphicOn Ω f) (hg : HolomorphicOn Ω g)
    (hne : ∀ z ∈ Ω, f z ≠ 0) (hn : 0 < n)
    (hpow : ∀ z ∈ Ω, g z ^ n = f z) {z : ℂ} (hz : z ∈ Ω) :
    deriv f z / f z = (n : ℂ) * (deriv g z / g z) := by
  have hgz : g z ≠ 0 := by
    intro h
    exact hne z hz (by rw [← hpow z hz, h, zero_pow (Nat.ne_of_gt hn)])
  have heq : f =ᶠ[𝓝 z] (fun w => g w ^ n) :=
    eventuallyEq_of_mem (hf.1.mem_nhds hz) (fun w hw => (hpow w hw).symm)
  have hd := ((hg.2 z hz).hasDerivAt.pow n).congr_of_eventuallyEq heq
  rw [hd.deriv, ← hpow z hz]
  have hp : g z ^ n = g z ^ (n - 1) * g z := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hp]
  field_simp

/-- A root forces periods in nℤ, using the genuine nonzero image loop. -/
theorem root_periods : Specs.D12Complex.Ch04.GlobalRootCriterion.root_periods_type := by
  intro Ω f g n _hΩ hf hne hn hg hpow γ hγ hc
  have hgn : ∀ z ∈ Ω, g z ≠ 0 := by
    intro z hz h
    exact hne z hz (by rw [← hpow z hz, h, zero_pow (Nat.ne_of_gt hn)])
  obtain ⟨k, hk⟩ := log_derivative_integral_integer hg hgn γ hγ hc
  refine ⟨k, ?_⟩
  rw [integral_congr γ (fun z hz => root_log_derivative hf hg hne hn hpow (hγ hz)),
    integral_const_mul, hk]
  field_simp [two_pi_I_ne_zero]

/-- Closed-period divisibility makes the exponential of a divided integral
independent of the path, although the integrals themselves can differ. -/
lemma exp_integral_independent (Ω : Set ℂ) (p : ℂ → ℂ) (hp : ContinuousOn p Ω)
    (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ κ : PiecewiseC1Path, κ.trace ⊆ Ω → κ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * κ.integral p =
        (n : ℂ) * (k : ℂ))
    (γ η : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (hη : η.trace ⊆ Ω)
    (hs : γ.path.source = η.path.source) (ht : γ.path.target = η.path.target) :
    Complex.exp (γ.integral p / (n : ℂ)) = Complex.exp (η.integral p / (n : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  obtain ⟨ηr, hηr, hrs, hrt, hri⟩ := Primitives.exists_reversed_path_in Ω p η hη hp
  obtain ⟨κ, hκ, hks, hkt, hki⟩ := PrimitiveConstruction.concatenate_in γ ηr hγ hηr
    (ht.trans hrs.symm) p hp
  have hc : κ.IsClosed := hkt.trans (hrt.trans (hs.symm.trans hks.symm))
  obtain ⟨k, hk⟩ := hperiod κ hκ hc
  have hint : κ.integral p = (n : ℂ) * (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    calc
      _ = (2 * (Real.pi : ℂ) * Complex.I) *
          ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * κ.integral p) := by
        field_simp [two_pi_I_ne_zero]
      _ = _ := by rw [hk]; ring
  rw [hki, hri] at hint
  apply Complex.exp_eq_exp_iff_exp_sub_eq_one.mpr
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨k, ?_⟩
  rw [← sub_div]
  have he : γ.integral p - η.integral p =
      (n : ℂ) * (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simpa only [sub_eq_add_neg] using hint
  rw [he]
  field_simp

/-- Choose one admissible path to each point; independence after exponentiation
will identify this total representative with every path formula. -/
def rootPotential (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (p : ℂ → ℂ) (n : ℕ) (c z : ℂ) : ℂ :=
  c * Complex.exp (PrimitiveConstruction.potential Ω hΩ a ha p z / (n : ℂ))

lemma rootPotential_eq_path (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (p : ℂ → ℂ) (hp : ContinuousOn p Ω) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ κ : PiecewiseC1Path, κ.trace ⊆ Ω → κ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * κ.integral p =
        (n : ℂ) * (k : ℂ)) (c : ℂ)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (hs : γ.path.source = a) :
    rootPotential Ω hΩ a ha p n c γ.path.target = c * Complex.exp (γ.integral p / (n : ℂ)) := by
  have hz : γ.path.target ∈ Ω := hγ ⟨γ.path.b, ⟨γ.path.ordered, le_rfl⟩, rfl⟩
  unfold rootPotential PrimitiveConstruction.potential
  rw [dite_eq_left hz]
  congr 1
  have hch := Classical.choose_spec
    (PrimitiveConstruction.exists_path_in Ω hΩ.2.1 hΩ.2.2 a ha γ.path.target hz)
  exact exp_integral_independent Ω p hp n hn hperiod _ γ hch.1 hγ
    (hch.2.1.trans hs.symm) hch.2.2

lemma rootPotential_base (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (p : ℂ → ℂ) (hp : ContinuousOn p Ω) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ κ : PiecewiseC1Path, κ.trace ⊆ Ω → κ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * κ.integral p =
        (n : ℂ) * (k : ℂ)) (c : ℂ) :
    rootPotential Ω hΩ a ha p n c a = c := by
  have hh := rootPotential_eq_path Ω hΩ a ha p hp n hn hperiod c
    (PiecewiseC1Path.const 0 0 le_rfl a) (by rintro z ⟨t, ht, rfl⟩; exact ha) rfl
  change rootPotential Ω hΩ a ha p n c a = _ at hh
  simpa [PiecewiseC1Path.const_integral] using hh

lemma rootPotential_mul_segment (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (p : ℂ → ℂ) (hp : ContinuousOn p Ω) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ κ : PiecewiseC1Path, κ.trace ⊆ Ω → κ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * κ.integral p =
        (n : ℂ) * (k : ℂ)) (c z w : ℂ) (hz : z ∈ Ω)
    (hseg : (PrimitiveConstruction.segmentPath z w).trace ⊆ Ω) :
    rootPotential Ω hΩ a ha p n c w = rootPotential Ω hΩ a ha p n c z *
      Complex.exp ((PrimitiveConstruction.segmentPath z w).integral p / (n : ℂ)) := by
  obtain ⟨γ, hγ, hs, ht⟩ := PrimitiveConstruction.exists_path_in Ω hΩ.2.1 hΩ.2.2 a ha z hz
  obtain ⟨δ, hδ, hds, hdt, hi⟩ := PrimitiveConstruction.concatenate_in γ
    (PrimitiveConstruction.segmentPath z w) hγ hseg (by simpa using ht) p hp
  have he := rootPotential_eq_path Ω hΩ a ha p hp n hn hperiod c δ hδ (hds.trans hs)
  have heγ := rootPotential_eq_path Ω hΩ a ha p hp n hn hperiod c γ hγ hs
  rw [hdt, PrimitiveConstruction.segmentPath_target, hi, add_div, Complex.exp_add] at he
  rw [ht] at heγ
  rw [he, heγ]
  ring

lemma rootPotential_holomorphic (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (f : ℂ → ℂ) (hf : HolomorphicOn Ω f) (hne : ∀ z ∈ Ω, f z ≠ 0)
    (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ κ : PiecewiseC1Path, κ.trace ⊆ Ω → κ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        κ.integral (fun z => deriv f z / f z) = (n : ℂ) * (k : ℂ)) (c : ℂ) :
    HolomorphicOn Ω (rootPotential Ω hΩ a ha (fun z => deriv f z / f z) n c) := by
  let p := fun z => deriv f z / f z
  have hp := continuous_log_derivative hf hne
  refine ⟨hΩ.2.1, fun z hz => ?_⟩
  obtain ⟨U, hzU, hUΩ, hL, hzero, hE, hd⟩ :=
    LocalLogarithmsRoots.normalized_logarithm Ω f z hf hz (hne z hz)
  let L := fun w => PrincipalLog (f w / f z)
  have hLz : L z = 0 := hzero
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hL.1 z hzU
  have he : rootPotential Ω hΩ a ha p n c =ᶠ[𝓝 z]
      (fun w => rootPotential Ω hΩ a ha p n c z * Complex.exp (L w / (n : ℂ))) := by
    apply eventuallyEq_of_mem (Metric.ball_mem_nhds z hr)
    intro w hw
    have hsegU : (PrimitiveConstruction.segmentPath z w).trace ⊆ U :=
      (PrimitiveConstruction.segmentPath_trace_subset z w).trans
        (((convex_ball z r).segment_subset (Metric.mem_ball_self hr) hw).trans hball)
    have hInt := Primitives.piecewise_endpoint U p L (hp.mono hUΩ)
      ⟨hL, fun v hv => (hd v hv).deriv⟩
      (PrimitiveConstruction.segmentPath z w) hsegU
    rw [PrimitiveConstruction.segmentPath_source, PrimitiveConstruction.segmentPath_target,
      hLz, sub_zero] at hInt
    rw [rootPotential_mul_segment Ω hΩ a ha p hp n hn hperiod c z w hz
      (hsegU.trans hUΩ), hInt]
  exact (((hL.2 z hzU).hasDerivAt.div_const (n : ℂ)).cexp.const_mul
    (rootPotential Ω hΩ a ha p n c z)).congr_of_eventuallyEq he |>.differentiableAt

/-- The power identity follows from exponentiating the logarithmic integral
along a path; it does not presuppose a global logarithm. -/
lemma rootPotential_pow (Ω : Set ℂ) (hΩ : IsDomain Ω) (a : ℂ) (ha : a ∈ Ω)
    (f : ℂ → ℂ) (hf : HolomorphicOn Ω f) (hne : ∀ z ∈ Ω, f z ≠ 0)
    (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ κ : PiecewiseC1Path, κ.trace ⊆ Ω → κ.IsClosed →
      ∃ k : ℤ, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        κ.integral (fun z => deriv f z / f z) = (n : ℂ) * (k : ℂ))
    (c : ℂ) (hc : c ^ n = f a) (z : ℂ) (hz : z ∈ Ω) :
    rootPotential Ω hΩ a ha (fun z => deriv f z / f z) n c z ^ n = f z := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  obtain ⟨γ, hγ, hs, ht⟩ := PrimitiveConstruction.exists_path_in Ω hΩ.2.1 hΩ.2.2 a ha z hz
  have he := rootPotential_eq_path Ω hΩ a ha _ (continuous_log_derivative hf hne)
    n hn hperiod c γ hγ hs
  rw [ht] at he
  rw [he, mul_pow, hc, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hn0, mul_comm]
  simpa [hs, ht] using exp_log_derivative_integral hf hne γ hγ

theorem root_construction :
    Specs.D12Complex.Ch04.GlobalRootCriterion.root_construction_type := by
  intro Ω f n hΩ hf hne hn hperiod a ha c hc
  refine ⟨rootPotential Ω hΩ a ha (fun z => deriv f z / f z) n c,
    rootPotential_holomorphic Ω hΩ a ha f hf hne n hn hperiod c,
    rootPotential_base Ω hΩ a ha _ (continuous_log_derivative hf hne) n hn hperiod c,
    rootPotential_pow Ω hΩ a ha f hf hne n hn hperiod c hc, ?_⟩
  intro γ hγ hs
  rw [Exponential.E_eq_exp]
  exact rootPotential_eq_path Ω hΩ a ha _ (continuous_log_derivative hf hne) n hn hperiod c γ hγ hs

theorem root_criterion : Specs.D12Complex.Ch04.GlobalRootCriterion.root_criterion_type := by
  intro Ω f n hΩ hf hne hn
  constructor
  · rintro ⟨g, hg, hpow⟩
    exact root_periods Ω f g n hΩ hf hne hn hg hpow
  · intro hperiod
    obtain ⟨a, ha⟩ := hΩ.1
    let c := Complex.exp (Complex.log (f a) / (n : ℂ))
    have hc : c ^ n = f a := by
      rw [← Complex.exp_nat_mul, mul_div_cancel₀ _
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), Complex.exp_log (hne a ha)]
    obtain ⟨g, hg, _, hpow, _⟩ := root_construction Ω f n hΩ hf hne hn hperiod a ha c hc
    exact ⟨g, hg, hpow⟩

/-- On a connected domain the ratio of two roots has zero derivative.
Its single constant value is an nth root of unity. -/
theorem root_unique : Specs.D12Complex.Ch04.GlobalRootCriterion.root_unique_type := by
  intro Ω f g h n hΩ hf hne hn hg hh hgp hhp
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hgn : ∀ z ∈ Ω, g z ≠ 0 := by
    intro z hz h
    exact hne z hz (by rw [← hgp z hz, h, zero_pow (Nat.ne_of_gt hn)])
  have hhn : ∀ z ∈ Ω, h z ≠ 0 := by
    intro z hz he
    exact hne z hz (by rw [← hhp z hz, he, zero_pow (Nat.ne_of_gt hn)])
  have hq : HolomorphicOn Ω (fun z => g z / h z) :=
    ⟨hΩ.2.1, fun z hz => (hg.2 z hz).div (hh.2 z hz) (hhn z hz)⟩
  have hdq : ∀ z ∈ Ω, deriv (fun w => g w / h w) z = 0 := by
    intro z hz
    have he : deriv g z / g z = deriv h z / h z :=
      mul_left_cancel₀ hn0 ((root_log_derivative hf hg hne hn hgp hz).symm.trans
        (root_log_derivative hf hh hne hn hhp hz))
    have hnum : deriv g z * h z - g z * deriv h z = 0 := by
      apply sub_eq_zero.mpr
      simpa only [mul_comm] using (div_eq_div_iff (hgn z hz) (hhn z hz)).mp he
    change deriv (g / h) z = 0
    rw [((hg.2 z hz).hasDerivAt.div (hh.2 z hz).hasDerivAt (hhn z hz)).deriv,
      hnum, zero_div]
  obtain ⟨ζ, hζ⟩ := Primitives.zero_derivative_constant Ω _ hΩ hq hdq
  refine ⟨ζ, ?_, fun z hz => (div_eq_iff (hhn z hz)).mp (hζ z hz)⟩
  obtain ⟨a, ha⟩ := hΩ.1
  rw [← hζ a ha, div_pow, hgp a ha, hhp a ha, div_self (hne a ha)]

end D12Complex.GlobalRootCriterion
