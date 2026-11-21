import MathGenome.Internal.MultivariableAnalysis.D04.C02.ChainRule
import MathGenome.Internal.MultivariableAnalysis.D04.C02.BilinearRules
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.SegmentFTC
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond

/-! Coordinatewise one-variable Riemann integration and integration along a
segment. Only the scalar Darboux integral and scalar FTC are used. -/
noncomputable section
open Set
open scoped BigOperators
namespace D04
open SingleVariableAnalysis.Riemann

def VectorRiemannIntegrable : Specs.D04.C02.SegmentFTC.VectorRiemannIntegrableType :=
  @Specs.D04.C02.SegmentFTC.VectorRiemannIntegrableValue

def vectorRiemannIntegral : Specs.D04.C02.SegmentFTC.vectorRiemannIntegralType :=
  @Specs.D04.C02.SegmentFTC.vectorRiemannIntegralValue

private theorem scalar_continuous_riemann_integrable (v : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn v (Icc a b)) : RealIntegrable v a b := by
  apply real_continuous_integrable v hab
  intro x hx
  exact (SingleVariableAnalysis.relativeContinuousAt_within_iff v (Icc a b) x).mpr (hc x hx)

theorem continuous_vector_riemann_integrable {m : ℕ} (v : ℝ → E m) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn v (Icc a b)) : VectorRiemannIntegrable v a b := by
  intro i
  apply scalar_continuous_riemann_integrable _ hab
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).continuous.comp_continuousOn hc

theorem vectorRiemannIntegral_apply {m : ℕ} (v : ℝ → E m) {a b : ℝ}
    (hv : VectorRiemannIntegrable v a b) (i : Fin m) :
    vectorRiemannIntegral v hv i = realIntegral (fun t => v t i) (hv i) := rfl

theorem vectorRiemannIntegral_inner {m : ℕ} (v : ℝ → E m) {a b : ℝ}
    (hab : a ≤ b) (hv : VectorRiemannIntegrable v a b) (w : E m) :
    ∃ hw : RealIntegrable (fun t => inner ℝ w (v t)) a b,
      realIntegral _ hw = inner ℝ w (vectorRiemannIntegral v hv) := by
  obtain ⟨hw, he⟩ := real_finite_linearity m (fun i => w i) (fun i t => v t i) hab hv
  simp only [← inner_coordinates] at hw he
  refine ⟨hw, ?_⟩
  rw [inner_coordinates]
  exact he

theorem vectorRiemannIntegral_add {m : ℕ} (v w : ℝ → E m) {a b : ℝ}
    (hv : VectorRiemannIntegrable v a b) (hw : VectorRiemannIntegrable w a b) :
    ∃ h : VectorRiemannIntegrable (fun t => v t + w t) a b,
      vectorRiemannIntegral _ h = vectorRiemannIntegral v hv + vectorRiemannIntegral w hw := by
  have hh := fun i => real_add_value (hv i) (hw i)
  refine ⟨fun i => (hh i).choose, ?_⟩
  ext i
  exact (hh i).choose_spec

theorem vectorRiemannIntegral_smul {m : ℕ} (v : ℝ → E m) {a b : ℝ}
    (hv : VectorRiemannIntegrable v a b) (c : ℝ) :
    ∃ h : VectorRiemannIntegrable (fun t => c • v t) a b,
      vectorRiemannIntegral _ h = c • vectorRiemannIntegral v hv := by
  have hh := fun i => real_mul_value (hv i) c
  refine ⟨fun i => (hh i).choose, ?_⟩
  ext i
  exact (hh i).choose_spec

theorem norm_vectorRiemannIntegral_le {m : ℕ} (v : ℝ → E m) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn v (Icc a b)) (hv : VectorRiemannIntegrable v a b) :
    ∃ hn : RealIntegrable (fun t => ‖v t‖) a b,
      ‖vectorRiemannIntegral v hv‖ ≤ realIntegral _ hn := by
  let z := vectorRiemannIntegral v hv
  have hn := scalar_continuous_riemann_integrable _ hab hc.norm
  refine ⟨hn, ?_⟩
  obtain ⟨hw, he⟩ := vectorRiemannIntegral_inner v hab hv z
  obtain ⟨hb, heb⟩ := real_mul_value hn ‖z‖
  have hm := realIntegral_mono _ _ hw hb (fun t _ => real_inner_le_norm z (v t))
  change realIntegral _ hw ≤ realIntegral _ hb at hm
  rw [he, heb] at hm
  change inner ℝ z z ≤ ‖z‖ * realIntegral _ hn at hm
  rw [real_inner_self_eq_norm_sq] at hm
  by_cases hz : z = 0
  · have hzero := (real_zero_value hab)
    obtain ⟨h0, he0⟩ := hzero
    have hp := realIntegral_mono _ _ h0 hn (fun t _ => norm_nonneg (v t))
    change realIntegral _ h0 ≤ realIntegral _ hn at hp
    rw [he0] at hp
    change ‖z‖ ≤ _
    simpa only [hz, norm_zero] using hp
  · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    change ‖z‖ ≤ _
    nlinarith

theorem segment_integrand_continuous {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (a h : E n) (hf : CrOn 1 U f)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) :
    ContinuousOn (fun t : ℝ => totalDerivative f (a + t • h) h) (Icc 0 1) := by
  have hd : ContinuousOn (totalDerivative f) U := hf.2
  have hl : Continuous (fun t : ℝ => a + t • h) := continuous_const.add (continuous_id.smul continuous_const)
  exact ((hd.comp hl.continuousOn hseg).clm_apply continuousOn_const)

theorem segment_ftc {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (a h : E n) (hU : IsOpen U) (hf : CrOn 1 U f)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • h ∈ U) :
    ∃ hv : VectorRiemannIntegrable (fun t : ℝ => totalDerivative f (a + t • h) h) 0 1,
      f (a + h) - f a = vectorRiemannIntegral _ hv := by
  have hc := segment_integrand_continuous U f a h hf hseg
  have hv := continuous_vector_riemann_integrable _ (by norm_num : (0 : ℝ) ≤ 1) hc
  refine ⟨hv, ?_⟩
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasFDerivAt f (totalDerivative f (a + t • h)) (a + t • h) := by
    obtain ⟨A, hA⟩ := hf.1 _ (hseg t ht)
    rw [totalDerivative_eq U f A _ hA]
    exact (hasTotalDerivative_iff_hasFDerivAt U f A _ hU (hseg t ht)).mp hA
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => a + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add a
  have hpath : ContinuousOn (fun t : ℝ => f (a + t • h)) (Icc 0 1) := by
    intro t ht
    exact ((hd t ht).comp_hasDerivAt t (hline t)).continuousAt.continuousWithinAt
  ext i
  have hcoord : ContinuousOn (fun t : ℝ => f (a + t • h) i) (Icc 0 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).continuous.comp_continuousOn hpath
  have he := real_ftc_second (fun t : ℝ => f (a + t • h) i)
    (fun t : ℝ => totalDerivative f (a + t • h) h i) 0 1 (by norm_num) hcoord
    (fun t ht => by
      have hvect := (hd t ⟨ht.1.le, ht.2.le⟩).comp_hasDerivAt t (hline t)
      exact (PiLp.proj 2 (fun _ : Fin m => ℝ) i).hasFDerivAt.comp_hasDerivAt t hvect)
    (hv i)
  change f (a + h) i - f a i = realIntegral _ (hv i)
  simpa using he.symm

end D04
