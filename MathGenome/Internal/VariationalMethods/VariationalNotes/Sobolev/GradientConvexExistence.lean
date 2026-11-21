import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.GradientConvexExistence
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Structure
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Compactness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.AffineCoercivity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.ReflexiveWeakCompactness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.StrongWeakLowerSemicontinuity
import Mathlib.Topology.Sequences
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology
namespace VariationalNotes.Sobolev

/-- Flattening the matrix fiber changes neither its Euclidean norm nor its
linear topology. -/
def gradientFlatten (m d : ℕ) :
    Gradient m d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m*d)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finProdFinEquiv

/-- Strong convergence of values together with weak convergence of the
Sobolev maps is obtained on a subsequence of every bounded affine sequence. -/
theorem affine_strong_weak_subsequence {d m : ℕ} [NeZero d]
    (Ω : Opens (Domain d)) (p : Exponent) (hp : 1 < p.real)
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (u₀ : W1p Ω m p)
    (u : ℕ → W1p Ω m p) (hu : ∀ n, u n ∈ affineClass Ω m p u₀)
    (hb : Bornology.IsBounded (Set.range u)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ v ∈ affineClass Ω m p u₀,
      Tendsto (fun n => toWeakSpace ℝ _ (u (k n))) atTop (𝓝 (toWeakSpace ℝ _ v)) ∧
      Tendsto (fun n => value Ω m p (u (k n))) atTop (𝓝 (value Ω m p v)) := by
  obtain ⟨k, hk, v, hv⟩ := VariationalNotes.Existence.reflexive_weak_subsequence
    (W1p Ω m p) (reflexive Ω p hp) u hb
  have hclosed := (affine_closed Ω p u₀).2
  have hvclass : v ∈ affineClass Ω m p u₀ := by
    have hh := hclosed.mem_of_tendsto hv (Eventually.of_forall fun n =>
      Set.mem_image_of_mem (toWeakSpace ℝ _) (hu (k n)))
    obtain ⟨w, hw, he⟩ := hh
    exact (toWeakSpace ℝ _).injective he ▸ hw
  have hc := compactness_affine (Nat.pos_of_ne_zero (NeZero.ne d)) Ω hΩ m p u₀
    (Set.range u) hb (by rintro _ ⟨n, rfl⟩; exact hu n)
  obtain ⟨w, _, l, hl, hw⟩ := hc.tendsto_subseq
    (fun n => subset_closure (Set.mem_image_of_mem _ (Set.mem_range_self (k n))))
  have hweak := ((WeakSpace.map (value Ω m p)).continuous.tendsto _).comp hv
  have hweak' := hweak.comp hl.tendsto_atTop
  have hw' := (toWeakSpaceCLM ℝ (ValueLp Ω m p)).continuous.tendsto w |>.comp hw
  have heq : w = value Ω m p v := by
    apply (toWeakSpace ℝ _).injective
    exact tendsto_nhds_unique hw' hweak'
  refine ⟨k ∘ l, hk.comp hl, v, hvclass, hv.comp hl.tendsto_atTop, ?_⟩
  rw [heq] at hw
  exact hw

/-- The supplied mixed-fiber theorem specializes to the matrix-gradient
energy. Only the gradient argument is convex. -/
theorem gradient_energy_liminf_of_strong_weak
    (hLSC : StrongWeakSpecs.strong_weak_lowerSemicontinuity.{0})
    {d m : ℕ} (Ω : Opens (Domain d)) (p q : Exponent)
    (F : Domain d → Vector m → Gradient m d → ℝ) (α C : ℝ) (a : Domain d → ℝ)
    (H : CoercivityHypotheses Ω p q F α C a)
    (hF : ∀ s Z, Measurable (fun x => F x s Z))
    (hconv : ∀ᵐ x ∂domainMeasure Ω, ∀ s, ConvexOn ℝ univ (F x s))
    (u : ℕ → W1p Ω m p) (v : W1p Ω m p)
    (hw : Tendsto (fun n => toWeakSpace ℝ _ (u n)) atTop (𝓝 (toWeakSpace ℝ _ v)))
    (hs : Tendsto (fun n => value Ω m p (u n)) atTop (𝓝 (value Ω m p v))) :
    energy Ω m p F v ≤ liminf (fun n => energy Ω m p F (u n)) atTop := by
  let : IsFiniteMeasure (domainMeasure Ω) :=
    isFiniteMeasure_restrict.mpr H.bounded.measure_lt_top.ne
  let e := gradientFlatten m d
  let L := e.toContinuousLinearMap.compLpL p.ennreal (domainMeasure Ω)
  let G : Domain d → Vector m →
      (Fin 1 → EuclideanSpace ℝ (Fin (m*d))) → ℝ :=
    fun x s z => F x s (e.symm (z 0))
  have hG : CaratheodorySpecs.MixedCaratheodory (domainMeasure Ω) G := by
    constructor
    · intro y
      exact hF y.1 (e.symm (y.2 0))
    · filter_upwards [H.continuous] with x hx
      exact hx.comp (continuous_fst.prodMk
        (e.symm.continuous.comp ((continuous_apply 0).comp continuous_snd)))
  have hcG : ∀ᵐ x ∂domainMeasure Ω, ∀ s, ConvexOn ℝ univ (G x s) := by
    filter_upwards [hconv] with x hx
    intro s
    refine ⟨convex_univ, ?_⟩
    intro z _ w _ a b ha hb hab
    simpa [G, map_add, map_smul] using
      (hx s).2 (Set.mem_univ (e.symm (z 0))) (Set.mem_univ (e.symm (w 0))) ha hb hab
  obtain ⟨B, _, hB⟩ := lower_power_absorption q.pos.le H.exponent_lt (show (0:ℝ) < 1 by norm_num)
  have ha : Integrable (fun x => a x + C*B) (domainMeasure Ω) :=
    H.a_integrable.add (integrable_const _)
  have hlow : ∀ᵐ x ∂domainMeasure Ω, ∀ s z,
      -(a x + C*B) - C*‖s‖ ^ p.ennreal.toReal ≤ G x s z := by
    filter_upwards [H.lower_bound] with x hx
    intro s z
    have hb := mul_le_mul_of_nonneg_left (hB ‖s‖ (norm_nonneg _)) H.C_nonneg
    have hz := mul_nonneg H.alpha_pos.le
      (Real.rpow_nonneg (norm_nonneg (e.symm (z 0))) p.real)
    have hf := hx s (e.symm (z 0))
    simp only [Exponent.toReal, one_mul] at *
    dsimp [G]
    linarith
  let zn : ℕ → Fin 1 → Lp (EuclideanSpace ℝ (Fin (m*d))) p.ennreal (domainMeasure Ω) :=
    fun n _ => L (gradient Ω m p (u n))
  let z : Fin 1 → Lp (EuclideanSpace ℝ (Fin (m*d))) p.ennreal (domainMeasure Ω) :=
    fun _ => L (gradient Ω m p v)
  have hzw : ∀ i, Tendsto (fun n => toWeakSpace ℝ _ (zn n i)) atTop
      (𝓝 (toWeakSpace ℝ _ (z i))) := by
    intro i
    exact ((WeakSpace.map (L.comp (gradient Ω m p))).continuous.tendsto _).comp hw
  have hp : 1 < p.ennreal := by
    simpa only [Exponent.ennreal, ← ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff p.pos).mpr (q.one_le.trans_lt H.exponent_lt)
  have h := hLSC (domainMeasure Ω) p.ennreal (fun _ : Fin 1 => p.ennreal)
    (show 1 ≤ p.ennreal from Fact.out) (by exact ENNReal.ofReal_ne_top) (fun _ => hp)
    (fun _ => ENNReal.ofReal_ne_top) G hG hcG
    (fun x => a x + C*B) ha C H.C_nonneg hlow
    (fun n => value Ω m p (u n)) (value Ω m p v) zn z hs hzw
  have he (w : W1p Ω m p) :
      CaratheodorySpecs.extendedIntegral (domainMeasure Ω)
        (fun x => G x (value Ω m p w x) (fun _ => L (gradient Ω m p w) x)) =
      energy Ω m p F w := by
    apply extendedIntegral_congr_ae
    filter_upwards [e.toContinuousLinearMap.coeFn_compLpL (gradient Ω m p w)] with x hx
    dsimp [G, L] at *
    rw [hx, e.symm_apply_apply]
  change CaratheodorySpecs.extendedIntegral _
      (fun x => G x (value Ω m p v x) (fun _ => L (gradient Ω m p v) x)) ≤
    liminf (fun n => CaratheodorySpecs.extendedIntegral _
      (fun x => G x (value Ω m p (u n) x) (fun _ => L (gradient Ω m p (u n)) x))) atTop at h
  simpa only [he] using h

/-- The direct method for a finite Carathéodory integrand convex only in
its gradient argument, on any bounded open domain. -/
theorem gradient_convex_existence : GradientExistenceExpected.Attainment := by
  intro d m _ _ Ω p q u₀ F α C a H hF hconv hcompetitor
  obtain ⟨I, hI, u, hu, _, hb, henergy⟩ :=
    affine_bounded_minimizing_sequence Ω p q u₀ F α C a H hcompetitor
  obtain ⟨k, hk, v, hv, hw, hs⟩ := affine_strong_weak_subsequence Ω p
    (q.one_le.trans_lt H.exponent_lt) H.bounded u₀ u hu hb
  have hlower := gradient_energy_liminf_of_strong_weak strong_weak_lowerSemicontinuity.{0} Ω p q F α C a H hF hconv
    (fun n => u (k n)) v hw hs
  have he : Tendsto (fun n => energy Ω m p F (u (k n))) atTop (𝓝 (I : EReal)) :=
    henergy.comp hk.tendsto_atTop
  rw [he.liminf_eq] at hlower
  have hupper : (I : EReal) ≤ energy Ω m p F v := by
    rw [← hI]
    exact sInf_le (Set.mem_image_of_mem _ hv)
  have heq : energy Ω m p F v = (I : EReal) := le_antisymm hlower hupper
  refine ⟨v, hv, I, heq, ?_⟩
  intro w hw
  rw [heq, ← hI]
  exact sInf_le (Set.mem_image_of_mem _ hw)

end VariationalNotes.Sobolev
