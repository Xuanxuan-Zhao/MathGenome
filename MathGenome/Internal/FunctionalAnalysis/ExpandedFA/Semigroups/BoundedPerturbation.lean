import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.BoundedPerturbation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.HilleYosida
import Mathlib.Analysis.Normed.Ring.Units

/-! Bounded perturbation on exactly the original generator domain, for arbitrary
real or complex Banach spaces (paper.tex, `fa2:p3:semigroup-perturbation`).

Neumann inversion establishes the resolvent half-line. A weighted orbit gauge
then bounds every perturbed resolvent power with the same prefactor M.
General Hille–Yosida gives the exact generator and prescribed growth estimate.
The previously established Volterra generator-identification helpers are retained.
-/

noncomputable section
open Filter Topology Set
open scoped NNReal

namespace ExpandedFA.Semigroups.BoundedPerturbation

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

open BoundedPerturbationSpec (boundedSum)

@[simp] theorem boundedSum_domain (A : Unbounded.Operator 𝕜 X X) (B : X →L[𝕜] X) :
    (boundedSum A B).domain = A.domain := rfl

@[simp] theorem boundedSum_apply (A : Unbounded.Operator 𝕜 X X) (B : X →L[𝕜] X)
    (x : A.domain) : boundedSum A B x = A x + B x := rfl

/-- Bounded perturbations preserve closedness, with no density assumption. -/
theorem boundedSum_closed (A : Unbounded.Operator 𝕜 X X) (B : X →L[𝕜] X)
    (hA : A.IsClosed) : (boundedSum A B).IsClosed := by
  have heq : ((boundedSum A B).graph : Set (X × X)) =
      (fun p : X × X => (p.1, p.2 - B p.1)) ⁻¹' (A.graph : Set (X × X)) := by
    ext p
    change p ∈ (boundedSum A B).graph ↔ (p.1, p.2 - B p.1) ∈ A.graph
    constructor
    · intro hp
      obtain ⟨hx, hv⟩ := (Unbounded.mem_graph_iff (boundedSum A B) p).mp hp
      exact (Unbounded.mem_graph_iff A _).mpr ⟨hx, eq_sub_of_add_eq hv⟩
    · intro hp
      obtain ⟨hx, hv⟩ := (Unbounded.mem_graph_iff A _).mp hp
      exact (Unbounded.mem_graph_iff (boundedSum A B) p).mpr
        ⟨hx, add_eq_of_eq_sub hv⟩
  change IsClosed ((boundedSum A B).graph : Set (X × X))
  rw [heq]
  exact hA.preimage
    (continuous_fst.prodMk (continuous_snd.sub (B.continuous.comp continuous_fst)))

/-- Density is preserved because the domain is unchanged. -/
theorem boundedSum_dense (A : Unbounded.Operator 𝕜 X X) (B : X →L[𝕜] X)
    (hA : Dense (A.domain : Set X)) : Dense ((boundedSum A B).domain : Set X) := hA

variable [CompleteSpace X]

/-- Neumann factorization on the exact unbounded domain. In particular neither
commutation of B with A nor boundedness of A is required. -/
def perturbedInverse (A : Unbounded.Operator 𝕜 X X) (B : X →L[𝕜] X) (ζ : 𝕜)
    (R : Unbounded.ResolventInverse A ζ) (h : ‖B * R.inverse‖ < 1) :
    Unbounded.ResolventInverse (boundedSum A B) ζ := by
  let U := Units.oneSub (B * R.inverse) h
  let V : X →L[𝕜] X := ↑U⁻¹
  have hright : (1 - B * R.inverse) * V = 1 := U.val_inv
  have hleft : V * (1 - B * R.inverse) = 1 := U.inv_val
  refine
    { inverse := R.inverse * V
      mem_domain := fun y => R.mem_domain (V y)
      right_inverse := ?_
      left_inverse := ?_ }
  · intro y
    have hv := congrArg (fun L : X →L[𝕜] X => L y) hright
    change ζ • R.inverse (V y) -
      (A ⟨R.inverse (V y), R.mem_domain (V y)⟩ + B (R.inverse (V y))) = y
    have hr := R.right_inverse (V y)
    change V y - B (R.inverse (V y)) = y at hv
    rw [sub_add_eq_sub_sub, hr, hv]
  · intro x
    have hv := congrArg (fun L : X →L[𝕜] X => L (ζ • (x : X) - A x)) hleft
    change V ((ζ • (x : X) - A x) -
      B (R.inverse (ζ • (x : X) - A x))) = ζ • (x : X) - A x at hv
    rw [R.left_inverse x] at hv
    change R.inverse (V (ζ • (x : X) - (A x + B x))) = (x : X)
    rw [sub_add_eq_sub_sub, hv, R.left_inverse x]

/-- Existence of the Neumann inverse for every real parameter above the
perturbed growth threshold. This alone is not a generation theorem: for M > 1,
Hille–Yosida requires all powers, not just this first inverse. -/
theorem boundedSum_resolvent (T : C0Semigroup 𝕜 X) (B : X →L[𝕜] X)
    (M ω r : ℝ) (hT : C0SemigroupSpec.exponentialBoundValue T M ω)
    (hr : ω + M * ‖B‖ < r) :
    Nonempty (Unbounded.ResolventInverse
      (boundedSum (C0SemigroupSpec.generatorValue T) B) (algebraMap ℝ 𝕜 r)) := by
  have hM : 0 ≤ M := le_trans (by norm_num) hT.1
  have hω : ω < r := lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg hM (norm_nonneg B))) hr
  let R := LaplaceResolvent.inverse T M ω (algebraMap ℝ 𝕜 r) hT (by simpa using hω)
  have hR : ‖R.inverse‖ ≤ M / (r - ω) := by
    simpa using
      (LaplaceResolvent.resolvent_powers T M ω (algebraMap ℝ 𝕜 r) hT
        (by simpa using hω) R 0).2
  have hsmall : ‖B * R.inverse‖ < 1 := by
    calc
      _ ≤ ‖B‖ * ‖R.inverse‖ := norm_mul_le _ _
      _ ≤ ‖B‖ * (M / (r - ω)) := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
      _ < 1 := by
        rw [← mul_div_assoc, div_lt_one (sub_pos.mpr hω)]
        nlinarith
  exact ⟨perturbedInverse _ B _ R hsmall⟩

/-- Strong continuity and local uniform bounds give joint continuity of the
semigroup action. This does not assert continuity in operator norm. -/
theorem continuous_action (T : C0Semigroup 𝕜 X) :
    Continuous (fun p : ℝ≥0 × X => T.operators p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨C, hC, hbound⟩ := T.bounded_on_interval (p.1 + 1)
  have hb : ∀ᶠ q : ℝ≥0 × X in 𝓝 p, ‖T.operators q.1‖ ≤ C := by
    have ht : ∀ᶠ q : ℝ≥0 × X in 𝓝 p, q.1 < p.1 + 1 :=
      (continuous_fst.tendsto p).eventually (gt_mem_nhds (by simp))
    exact ht.mono (fun q hq => hbound q.1 hq.le)
  have hu : Tendsto (fun q : ℝ≥0 × X => C * ‖q.2 - p.2‖) (𝓝 p) (𝓝 0) := by
    simpa using ((continuous_snd.tendsto p).sub_const p.2).norm.const_mul C
  have hz : Tendsto (fun q : ℝ≥0 × X => T.operators q.1 (q.2 - p.2))
      (𝓝 p) (𝓝 0) := by
    apply squeeze_zero_norm' _ hu
    filter_upwards [hb] with q hq
    exact ((T.operators q.1).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
  have hv := ((T.continuous_orbit p.2).tendsto p.1).comp (continuous_fst.tendsto p)
  change Tendsto (fun q : ℝ≥0 × X => T.operators q.1 q.2) (𝓝 p)
    (𝓝 (T.operators p.1 p.2))
  simpa only [Function.comp_def, map_sub, sub_add_cancel, zero_add] using hz.add hv

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

/-- The short-time Volterra correction divided by time tends to Bx. This is
the local fact needed to identify the *entire* derivative domain of the sum. -/
theorem volterra_average_tendsto (T : C0Semigroup 𝕜 X) (B : X →L[𝕜] X)
    (f : ℝ≥0 → X) (hf : Continuous f) (x : X) (h0 : f 0 = x) :
    Tendsto (fun h : ℝ => h⁻¹ •
      ∫ s in (0 : ℝ)..h, T.operators (h - s).toNNReal (B (f s.toNNReal)))
      (𝓝[>] 0) (𝓝 (B x)) := by
  let g : ℝ → ℝ → X := fun h u =>
    T.operators (h - h * u).toNNReal (B (f (h * u).toNNReal))
  have hg : Continuous g.uncurry := by
    exact (continuous_action T).comp
      ((continuous_real_toNNReal.comp (continuous_fst.sub
      (continuous_fst.mul continuous_snd))).prodMk
      (B.continuous.comp (hf.comp
        (continuous_real_toNNReal.comp (continuous_fst.mul continuous_snd)))))
  have hi : Continuous (fun h => ∫ u in (0 : ℝ)..1, g h u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg 0 1
  have hlim : Tendsto (fun h => ∫ u in (0 : ℝ)..1, g h u)
      (𝓝[>] 0) (𝓝 (B x)) := by
    simpa [g, h0] using (hi.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  simpa only [g, mul_zero, mul_one] using
    (intervalIntegral.integral_comp_mul_left
      (fun s : ℝ => T.operators (h - s).toNNReal (B (f s.toNNReal)))
      (ne_of_gt hh) (a := 0) (b := 1))

/-- A strongly continuous semigroup satisfying the Volterra equation has
generator A+B, including the converse implication for existence of derivatives.
No resolvent calculation or differentiability of the individual integrands
is assumed here. -/
theorem generator_of_volterra (T S : C0Semigroup 𝕜 X) (B : X →L[𝕜] X)
    (hV : ∀ (t : ℝ≥0) (x : X), S.operators t x = T.operators t x +
      ∫ s in (0 : ℝ)..(t : ℝ),
        T.operators ((t : ℝ) - s).toNNReal (B (S.operators s.toNNReal x))) :
    generator S = boundedSum (generator T) B := by
  have hdiff (x : X) : Tendsto
      (fun h : ℝ => differenceQuotient S h x - differenceQuotient T h x)
      (𝓝[>] 0) (𝓝 (B x)) := by
    apply (volterra_average_tendsto T B (fun t => S.operators t x)
      (S.continuous_orbit x) x (S.zero_apply x)).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [S.differenceQuotient_real, T.differenceQuotient_real, ← smul_sub]
    rw [hV h.toNNReal x, Real.coe_toNNReal _ hh.le]
    congr 1
    abel
  have hiff (x y : X) : HasGeneratorLimit S x (y + B x) ↔ HasGeneratorLimit T x y := by
    change Tendsto (fun h => differenceQuotient S h x) (𝓝[>] 0) (𝓝 (y + B x)) ↔
      Tendsto (fun h => differenceQuotient T h x) (𝓝[>] 0) (𝓝 y)
    constructor
    · intro h
      have hl := h.sub (hdiff x)
      simpa only [add_sub_cancel_right, sub_sub_cancel] using hl
    · intro h
      have hl := h.add (hdiff x)
      simpa only [add_sub_cancel] using hl
  apply LinearPMap.ext
  · ext x
    change (∃ y, HasGeneratorLimit S x y) ↔ ∃ y, HasGeneratorLimit T x y
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y - B x, (hiff x (y - B x)).mp (by simpa using hy)⟩
    · rintro ⟨y, hy⟩
      exact ⟨y + B x, (hiff x y).mpr hy⟩
  · intro x hx hy
    exact generator_limit_unique S x _ _
      (generator_has_limit S ⟨x, hx⟩)
      ((hiff x _).mpr (generator_has_limit T ⟨x, hy⟩))

/-- Weighted orbit norm, used only through real inequalities. Keeping the
ambient normed-space instance avoids any change to the canonical generator. -/
def orbitGauge (T : C0Semigroup 𝕜 X) (ω : ℝ) (x : X) : ℝ :=
  ⨆ t : ℝ≥0, Real.exp (-ω * (t : ℝ)) * ‖T.operators t x‖

theorem weighted_orbit_bound (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (x : X) (t : ℝ≥0) :
    Real.exp (-ω * (t : ℝ)) * ‖T.operators t x‖ ≤ M * ‖x‖ := by
  calc
    _ ≤ Real.exp (-ω * (t : ℝ)) * ((M * Real.exp (ω * (t : ℝ))) * ‖x‖) :=
      mul_le_mul_of_nonneg_left
        (((T.operators t).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hT.2 t) (norm_nonneg x))) (Real.exp_pos _).le
    _ = (M * ‖x‖) * (Real.exp (-ω * (t : ℝ)) * Real.exp (ω * (t : ℝ))) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

theorem orbitGauge_bdd (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (x : X) :
    BddAbove (range (fun t : ℝ≥0 => Real.exp (-ω * (t : ℝ)) * ‖T.operators t x‖)) :=
  ⟨M * ‖x‖, by rintro _ ⟨t, rfl⟩; exact weighted_orbit_bound T hT x t⟩

theorem orbitGauge_le (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (x : X) :
    orbitGauge T ω x ≤ M * ‖x‖ :=
  ciSup_le (weighted_orbit_bound T hT x)

theorem norm_le_orbitGauge (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (x : X) :
    ‖x‖ ≤ orbitGauge T ω x := by
  simpa only [orbitGauge, NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul, T.zero_apply] using
    (le_ciSup (orbitGauge_bdd T hT x) 0)

theorem orbitGauge_add_le (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (x y : X) :
    orbitGauge T ω (x + y) ≤ orbitGauge T ω x + orbitGauge T ω y := by
  apply ciSup_le
  intro t
  calc
    _ ≤ Real.exp (-ω * (t : ℝ)) * (‖T.operators t x‖ + ‖T.operators t y‖) := by
      rw [map_add]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (le_ciSup (orbitGauge_bdd T hT x) t)
        (le_ciSup (orbitGauge_bdd T hT y) t)

theorem orbit_le_gauge (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (x : X) (t : ℝ≥0) :
    ‖T.operators t x‖ ≤ Real.exp (ω * (t : ℝ)) * orbitGauge T ω x := by
  have h := mul_le_mul_of_nonneg_left
    (le_ciSup (orbitGauge_bdd T hT x) t) (Real.exp_pos (ω * (t : ℝ))).le
  calc
    _ = Real.exp (ω * (t : ℝ)) *
        (Real.exp (-ω * (t : ℝ)) * ‖T.operators t x‖) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ _ := h

/-- The original resolvent is contractive in the weighted orbit norm with
constant `(r - ω)⁻¹`. The vector integral, rather than an operator integral,
works for arbitrary strongly continuous semigroups. -/
theorem orbitGauge_laplace_le (T : C0Semigroup 𝕜 X) {M ω r : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hr : ω < r) (y : X) :
    orbitGauge T ω ((LaplaceResolvent.inverse T M ω (algebraMap ℝ 𝕜 r)
      hT (by simpa using hr)).inverse y) ≤ orbitGauge T ω y / (r - ω) := by
  open MeasureTheory LaplaceResolventSpec in
  have hR : (LaplaceResolvent.inverse T M ω (algebraMap ℝ 𝕜 r)
      hT (by simpa using hr)).inverse y =
      ∫ s : ℝ in Ioi 0, orbit T (algebraMap ℝ 𝕜 r) y s := by
    simp [LaplaceResolvent.inverse, LaplaceResolvent.integralOperator_apply]
  rw [hR]
  apply ciSup_le
  intro t
  have hf : MeasureTheory.IntegrableOn
      (LaplaceResolventSpec.orbit T (algebraMap ℝ 𝕜 r) y) (Ioi 0) := by
    simpa using (LaplaceResolvent.weighted_integrability T M ω (algebraMap ℝ 𝕜 r)
      hT (by simpa using hr) 0 y)
  have hb : ‖T.operators t (∫ s : ℝ in Ioi 0,
      LaplaceResolventSpec.orbit T (algebraMap ℝ 𝕜 r) y s)‖ ≤
      (Real.exp (ω * (t : ℝ)) * orbitGauge T ω y) / (r - ω) := by
    rw [← (T.operators t).integral_comp_comm hf]
    have hm : MeasureTheory.IntegrableOn (fun s : ℝ =>
        (Real.exp (ω * (t : ℝ)) * orbitGauge T ω y) * Real.exp (-(r - ω) * s))
        (Ioi 0) := by
      simpa only [MeasureTheory.IntegrableOn, pow_zero, one_mul] using
        (LaplaceResolvent.scalar_moment_integrable 0 (sub_pos.mpr hr)).const_mul
          (Real.exp (ω * (t : ℝ)) * orbitGauge T ω y)
    have hi := MeasureTheory.norm_integral_le_of_norm_le hm (f := fun s : ℝ =>
      T.operators t (LaplaceResolventSpec.orbit T (algebraMap ℝ 𝕜 r) y s)) (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
        rw [LaplaceResolventSpec.orbit, map_smul, norm_smul, LaplaceResolvent.norm_kernel,
          ← T.add_apply]
        have hre : RCLike.re (algebraMap ℝ 𝕜 r) = r := by simp
        rw [hre]
        calc
          _ ≤ Real.exp (-r * s) * (Real.exp (ω * ((t + s.toNNReal : ℝ≥0) : ℝ)) *
              orbitGauge T ω y) :=
            mul_le_mul_of_nonneg_left (orbit_le_gauge T hT y _) (Real.exp_pos _).le
          _ = _ := by
            rw [NNReal.coe_add, Real.coe_toNNReal _ hs.le]
            rw [show ω * ((t : ℝ) + s) = ω * (t : ℝ) + ω * s by ring,
              Real.exp_add, show -(r - ω) * s = -r * s + ω * s by ring, Real.exp_add]
            ring)
    have hexp : (∫ s : ℝ in Ioi 0, Real.exp (-(r - ω) * s)) = 1 / (r - ω) := by
      simpa using LaplaceResolvent.scalar_moment_integral 0 (sub_pos.mpr hr)
    simpa only [MeasureTheory.integral_const_mul, hexp, mul_one_div] using hi
  calc
    _ ≤ Real.exp (-ω * (t : ℝ)) *
        ((Real.exp (ω * (t : ℝ)) * orbitGauge T ω y) / (r - ω)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by
      rw [mul_div_assoc, ← mul_assoc, ← Real.exp_add]
      simp

theorem orbitGauge_map_le (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (B : X →L[𝕜] X) (x : X) :
    orbitGauge T ω (B x) ≤ (M * ‖B‖) * orbitGauge T ω x := by
  have hM : 0 ≤ M := le_trans (by norm_num) hT.1
  calc
    _ ≤ M * ‖B x‖ := orbitGauge_le T hT _
    _ ≤ M * (‖B‖ * ‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) hM
    _ = (M * ‖B‖) * ‖x‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_le_orbitGauge T hT x)
      (mul_nonneg hM (norm_nonneg B))

/-- The inverse equation is valid on the precise original generator domain. -/
theorem boundedSum_inverse_equation (T : C0Semigroup 𝕜 X) (B : X →L[𝕜] X)
    (ζ : 𝕜) (R : Unbounded.ResolventInverse (generator T) ζ)
    (Q : Unbounded.ResolventInverse (boundedSum (generator T) B) ζ) (y : X) :
    Q.inverse y = R.inverse (y + B (Q.inverse y)) := by
  have h := R.left_inverse ⟨Q.inverse y, Q.mem_domain y⟩
  have hQ := Q.right_inverse y
  change ζ • Q.inverse y -
    (generator T ⟨Q.inverse y, Q.mem_domain y⟩ + B (Q.inverse y)) = y at hQ
  have he : ζ • Q.inverse y - generator T ⟨Q.inverse y, Q.mem_domain y⟩ =
      y + B (Q.inverse y) := by
    rw [sub_add_eq_sub_sub] at hQ
    exact sub_eq_iff_eq_add.mp hQ
  rw [he] at h
  exact h.symm

/-- Every perturbed inverse contracts the orbit norm with the sharp shifted
constant. Existence comes separately from Neumann inversion. -/
theorem orbitGauge_perturbed_le (T : C0Semigroup 𝕜 X) (B : X →L[𝕜] X)
    {M ω r : ℝ} (hT : C0SemigroupSpec.exponentialBoundValue T M ω)
    (hr : ω + M * ‖B‖ < r)
    (Q : Unbounded.ResolventInverse (boundedSum (generator T) B) (algebraMap ℝ 𝕜 r))
    (y : X) :
    orbitGauge T ω (Q.inverse y) ≤ orbitGauge T ω y / (r - (ω + M * ‖B‖)) := by
  have hM : 0 ≤ M := le_trans (by norm_num) hT.1
  have hω : ω < r := lt_of_le_of_lt
    (le_add_of_nonneg_right (mul_nonneg hM (norm_nonneg B))) hr
  let R := LaplaceResolvent.inverse T M ω (algebraMap ℝ 𝕜 r) hT (by simpa using hω)
  have hbound : orbitGauge T ω (Q.inverse y) ≤
      (orbitGauge T ω y + (M * ‖B‖) * orbitGauge T ω (Q.inverse y)) / (r - ω) := by
    calc
      _ = orbitGauge T ω (R.inverse (y + B (Q.inverse y))) := by
        exact congrArg (orbitGauge T ω) (boundedSum_inverse_equation T B _ R Q y)
      _ ≤ orbitGauge T ω (y + B (Q.inverse y)) / (r - ω) :=
        orbitGauge_laplace_le T hT hω _
      _ ≤ (orbitGauge T ω y + orbitGauge T ω (B (Q.inverse y))) / (r - ω) :=
        div_le_div_of_nonneg_right (orbitGauge_add_le T hT _ _) (sub_pos.mpr hω).le
      _ ≤ _ := div_le_div_of_nonneg_right
        (add_le_add le_rfl (orbitGauge_map_le T hT B (Q.inverse y))) (sub_pos.mpr hω).le
  apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
  have hmul := (le_div_iff₀ (sub_pos.mpr hω)).mp hbound
  nlinarith

/-- Iterating the weighted estimate incurs M only once, when comparing the
orbit norm with the ambient norm, regardless of the resolvent power. -/
theorem boundedSum_resolvent_powers (T : C0Semigroup 𝕜 X) (B : X →L[𝕜] X)
    {M ω r : ℝ} (hT : C0SemigroupSpec.exponentialBoundValue T M ω)
    (hr : ω + M * ‖B‖ < r)
    (Q : Unbounded.ResolventInverse (boundedSum (generator T) B) (algebraMap ℝ 𝕜 r))
    (n : ℕ) : ‖Q.inverse ^ n‖ ≤ M / (r - (ω + M * ‖B‖)) ^ n := by
  let d := r - (ω + M * ‖B‖)
  have hd : 0 < d := sub_pos.mpr hr
  have hM : 0 ≤ M := le_trans (by norm_num) hT.1
  have hpow (x : X) (k : ℕ) : orbitGauge T ω ((Q.inverse ^ k) x) ≤
      orbitGauge T ω x / d ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ']
      change orbitGauge T ω (Q.inverse ((Q.inverse ^ k) x)) ≤ _
      calc
        _ ≤ orbitGauge T ω ((Q.inverse ^ k) x) / d := orbitGauge_perturbed_le T B hT hr Q _
        _ ≤ (orbitGauge T ω x / d ^ k) / d := div_le_div_of_nonneg_right ih hd.le
        _ = _ := by rw [div_div, pow_succ]
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM (pow_nonneg hd.le n))
  intro x
  calc
    _ ≤ orbitGauge T ω ((Q.inverse ^ n) x) := norm_le_orbitGauge T hT _
    _ ≤ orbitGauge T ω x / d ^ n := hpow x n
    _ ≤ (M * ‖x‖) / d ^ n :=
      div_le_div_of_nonneg_right (orbitGauge_le T hT x) (pow_nonneg hd.le n)
    _ = (M / d ^ n) * ‖x‖ := by ring

/-- All Hille–Yosida bounds, with the original common prefactor M. -/
theorem boundedSum_estimates (T : C0Semigroup 𝕜 X) (B : X →L[𝕜] X)
    {M ω : ℝ} (hT : C0SemigroupSpec.exponentialBoundValue T M ω) :
    HilleYosidaSpec.ResolventEstimates (boundedSum (generator T) B) M (ω + M * ‖B‖) := by
  have hres (r : ℝ) (hr : ω + M * ‖B‖ < r) :
      Nonempty (Unbounded.ResolventInverse (boundedSum (generator T) B) (algebraMap ℝ 𝕜 r)) :=
    boundedSum_resolvent T B M ω r hT hr
  refine ⟨hres, ?_⟩
  intro r hr n
  let Q := (hres r hr).some
  have heq : Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 r)
      (boundedSum (generator T) B) = Q.inverse := by
    simp only [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left (hres r hr)]
    exact Unbounded.resolvent_inverse_unique _ _ _ Q
  rw [heq]
  exact boundedSum_resolvent_powers T B hT hr Q (n + 1)

omit [CompleteSpace X] in
/-- Bounded perturbation on exactly D(A), obtained from all resolvent powers
in the weighted orbit norm and general Hille–Yosida. -/
theorem generation : BoundedPerturbationSpec.Generation (𝕜 := 𝕜) (X := X) := by
  intro _ A T B M ω hgen hT
  change A = generator T at hgen
  subst A
  obtain ⟨S, hS, hb⟩ := HilleYosida.sufficient (boundedSum (generator T) B)
    M (ω + M * ‖B‖) hT.1 (boundedSum_dense _ B (T.generator_domain_dense))
    (boundedSum_closed _ B (T.generator_graph_closed)) (boundedSum_estimates T B hT)
  exact ⟨S, hS.symm, hb⟩

end ExpandedFA.Semigroups.BoundedPerturbation
