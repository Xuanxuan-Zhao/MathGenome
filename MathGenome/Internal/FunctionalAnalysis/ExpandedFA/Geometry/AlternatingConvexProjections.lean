import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.AlternatingConvexProjections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Weak convergence of the entire alternating convex projection sequence,
`fa2:p2:alternating-projections`, paper.tex 13117–13148 (convex-set clause).
The variational inequality gives Fejér monotonicity and vanishing steps.
Riesz representation and weak-star compactness, followed by the accepted
Eberlein–Šmulian theorem, provide weakly convergent subsequences. Nearby future
iterates lie in each set, so weak closedness puts their limits in the intersection.
The difference of squared distances proves uniqueness; the subsequence criterion
then yields convergence of every scalar test on the entire sequence.
-/

noncomputable section
open Filter Set
open scoped Topology InnerProductSpace ComplexConjugate
namespace ExpandedFA.Geometry.AlternatingConvexProjections
universe u v

def iterates : Spec.IteratesType.{v} := Spec.IteratesValue

theorem iterates_recurrences : Spec.IteratesRecurrences.{v} := by
  intro H P₁ P₂ x₀
  refine ⟨rfl, fun n => ⟨?_, ?_⟩⟩
  · simp [Spec.iteratesValue]
  · change Spec.iteratesValue P₁ P₂ x₀ ((2 * n + 1) + 1) = _
    simp [Spec.iteratesValue]

section Hilbert
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

abbrev Weakly (x : ℕ → H) (p : H) : Prop :=
  ∀ f : H →L[𝕜] 𝕜, Tendsto (fun n => f (x n)) atTop (𝓝 (f p))

lemma weak_topology_eq : P1.EberleinSmulian.Spec.weakTopology 𝕜 H =
    (instTopologicalSpaceWeakSpace 𝕜 H : TopologicalSpace H) := by
  change TopologicalSpace.induced id _ = _
  exact @induced_id H (instTopologicalSpaceWeakSpace 𝕜 H)

/-- The shared weak topology has exactly the usual scalar tests. -/
lemma weakly_iff (x : ℕ → H) (p : H) : Weakly (𝕜 := 𝕜) x p ↔
    Tendsto x atTop (@nhds H (P1.EberleinSmulian.Spec.weakTopology 𝕜 H) p) := by
  rw [weak_topology_eq]
  change _ ↔ Tendsto (fun n => toWeakSpace 𝕜 H (x n)) atTop
    (𝓝 (toWeakSpace 𝕜 H p))
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto _
    (separatingDual_iff_injective.mp (inferInstance : SeparatingDual 𝕜 H))).symm

/-- Riesz representation transports a weak-star compact ball to H. -/
lemma bounded_weak_subsequence (x : ℕ → H) (R : ℝ) (hR : ∀ n, ‖x n‖ ≤ R) :
    ∃ p r, StrictMono r ∧ Weakly (𝕜 := 𝕜) (x ∘ r) p := by
  let T : WeakDual 𝕜 H → H := fun g => (InnerProductSpace.toDual 𝕜 H).symm g.toStrongDual
  have hT : Continuous (fun g => toWeakSpace 𝕜 H (T g)) := by
    apply WeakBilin.continuous_of_continuous_eval
    intro f
    let y := (InnerProductSpace.toDual 𝕜 H).symm f
    have heq : (fun g : WeakDual 𝕜 H => f (T g)) = (fun g => conj (g y)) := by
      funext g
      have hf : f = InnerProductSpace.toDual 𝕜 H y :=
        ((InnerProductSpace.toDual 𝕜 H).apply_symm_apply f).symm
      have hg : g.toStrongDual = InnerProductSpace.toDual 𝕜 H (T g) :=
        ((InnerProductSpace.toDual 𝕜 H).apply_symm_apply g.toStrongDual).symm
      rw [hf]
      change ⟪y, T g⟫_𝕜 = conj (g.toStrongDual y)
      rw [hg]
      exact (inner_conj_symm (𝕜 := 𝕜) y (T g)).symm
    change Continuous (fun g : WeakDual 𝕜 H => f (T g))
    rw [heq]
    exact (WeakDual.eval_continuous y).star
  let K : Set H := T '' (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : H →L[𝕜] 𝕜) R)
  have hK : @IsCompact H (P1.EberleinSmulian.Spec.weakTopology 𝕜 H) K := by
    rw [weak_topology_eq]
    change @IsCompact (WeakSpace 𝕜 H) _ ((fun g => toWeakSpace 𝕜 H (T g)) '' _)
    exact (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (0 : H →L[𝕜] 𝕜) R).image hT
  have hx : ∀ n, x n ∈ K := by
    intro n
    refine ⟨(InnerProductSpace.toDual 𝕜 H (x n)).toWeakDual, ?_, ?_⟩
    · change dist (InnerProductSpace.toDual 𝕜 H (x n)) 0 ≤ R
      simpa only [dist_zero_right, (InnerProductSpace.toDual 𝕜 H).norm_map] using hR n
    · exact (InnerProductSpace.toDual 𝕜 H).symm_apply_apply (x n)
  have hcl : @IsCompact H (P1.EberleinSmulian.Spec.weakTopology 𝕜 H)
      (@closure H (P1.EberleinSmulian.Spec.weakTopology 𝕜 H) K) := by
    have ht2 : @T2Space H (P1.EberleinSmulian.Spec.weakTopology 𝕜 H) := by
      rw [weak_topology_eq]
      exact inferInstanceAs (T2Space (WeakSpace 𝕜 H))
    letI : TopologicalSpace H := P1.EberleinSmulian.Spec.weakTopology 𝕜 H
    letI : T2Space H := ht2
    simpa only [hK.isClosed.closure_eq] using hK
  obtain ⟨p, r, hr, hp⟩ := P1.EberleinSmulian.compact_implies_subsequences 𝕜 H K hcl x hx
  exact ⟨p, r, hr, (weakly_iff _ _).mpr hp⟩

/-- Squared distance drops by at least the square of the projection step. -/
lemma projection_energy (C : Set H) (hne : C.Nonempty) (hc : IsClosed C)
    (hv : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C)
    (x p : H) (hp : p ∈ C) :
    let q := Hilbert.Projection.convexProjection 𝕜 H C hne hc hv x
    ‖q - p‖ ^ 2 + ‖q - x‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
  dsimp only
  let q := Hilbert.Projection.convexProjection 𝕜 H C hne hc hv x
  have hvar := ((Hilbert.Projection.eq_convexProjection_iff_variational
    𝕜 H C hne hc hv x q).mp rfl).2 p hp
  have hid : x - p = (x - q) + (q - p) := by abel
  have hinner : RCLike.re ⟪x - q, q - p⟫_𝕜 ≥ 0 := by
    have : p - q = -(q - p) := by abel
    simpa only [this, inner_neg_right, map_neg, neg_nonpos] using hvar
  rw [hid, norm_add_sq (𝕜 := 𝕜)]
  rw [norm_sub_rev q x]
  linarith

/-- A decreasing nonnegative real sequence has a finite limit. -/
lemma decreasing_limit (a : ℕ → ℝ) (hn : ∀ n, 0 ≤ a n)
    (hd : ∀ n, a (n+1) ≤ a n) : ∃ l, Tendsto a atTop (𝓝 l) := by
  exact ⟨⨅ n, a n, tendsto_atTop_ciInf (antitone_nat_of_succ_le hd)
    ⟨0, Set.forall_mem_range.mpr hn⟩⟩

/-- No summation convention is needed: convergence of squared distances
forces consecutive steps to vanish. -/
lemma vanishing_steps (x : ℕ → H) (p : H)
    (he : ∀ n, ‖x (n+1) - p‖ ^ 2 + ‖x (n+1) - x n‖ ^ 2 ≤ ‖x n - p‖ ^ 2) :
    Tendsto (fun n => ‖x (n+1) - x n‖) atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := decreasing_limit (fun n => ‖x n - p‖ ^ 2)
    (fun n => sq_nonneg _) (fun n => by nlinarith [he n, sq_nonneg ‖x (n+1) - x n‖])
  have hs : Tendsto (fun n => ‖x (n+1) - x n‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _)
      (fun n => show _ ≤ ‖x n - p‖ ^ 2 - ‖x (n+1) - p‖ ^ 2 by linarith [he n])
    simpa only [sub_self, Function.comp_def] using hl.sub (hl.comp (tendsto_add_atTop_nat 1))
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

/-- Norm-small perturbations preserve weak convergence. -/
lemma weakly_of_perturbation {x y : ℕ → H} {p : H}
    (hx : Weakly (𝕜 := 𝕜) x p)
    (hsmall : Tendsto (fun n => ‖y n - x n‖) atTop (𝓝 0)) :
    Weakly (𝕜 := 𝕜) y p := by
  intro f
  have hzero : Tendsto (fun n => f (y n - x n)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => y n - x n) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hsmall
    simpa only [map_zero, Function.comp_def] using f.continuous.tendsto 0 |>.comp hh
  have := hzero.add (hx f)
  simpa only [map_sub, sub_add_cancel, zero_add] using this

/-- The difference of two squared distances is weakly continuous. -/
lemma distance_difference_weak {x : ℕ → H} {p : H}
    (hx : Weakly (𝕜 := 𝕜) x p) (a b : H) :
    Tendsto (fun n => ‖x n - a‖ ^ 2 - ‖x n - b‖ ^ 2) atTop
      (𝓝 (‖p - a‖ ^ 2 - ‖p - b‖ ^ 2)) := by
  have hid (z : H) : ‖z - a‖ ^ 2 - ‖z - b‖ ^ 2 =
      -2 * RCLike.re ⟪a - b, z⟫_𝕜 + ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜), inner_sub_left, map_sub,
      inner_re_symm z a, inner_re_symm z b]
    ring
  simp_rw [hid]
  exact (((RCLike.continuous_re.tendsto _).comp (hx (innerSL 𝕜 (a-b)))).const_mul (-2)).add_const _ |>.sub_const _

/-- Hilbert-space uniqueness of weak subsequential limits of a Fejér sequence. -/
lemma fejer_weak_limits_unique (x : ℕ → H) (S : Set H)
    (hmono : ∀ p ∈ S, Antitone (fun n => ‖x n - p‖ ^ 2))
    {p q : H} (hp : p ∈ S) (hq : q ∈ S)
    {r s : ℕ → ℕ} (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (hpr : Weakly (𝕜 := 𝕜) (x ∘ r) p) (hqs : Weakly (𝕜 := 𝕜) (x ∘ s) q) :
    p = q := by
  obtain ⟨a, ha⟩ := decreasing_limit (fun n => ‖x n - p‖ ^ 2)
    (fun _ => sq_nonneg _) (fun n => hmono p hp (Nat.le_succ n))
  obtain ⟨b, hb⟩ := decreasing_limit (fun n => ‖x n - q‖ ^ 2)
    (fun _ => sq_nonneg _) (fun n => hmono q hq (Nat.le_succ n))
  have hh := ha.sub hb
  have he₁ := tendsto_nhds_unique (hh.comp hr) (distance_difference_weak hpr p q)
  have he₂ := tendsto_nhds_unique (hh.comp hs) (distance_difference_weak hqs p q)
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_sub, sub_zero] at he₁ he₂
  have he : ‖p - q‖ = 0 := by
    rw [norm_sub_rev q p] at he₂
    nlinarith [norm_nonneg (p-q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

/-- The usual weak Fejér convergence principle, without separability assumptions. -/
lemma fejer_weak_convergence (x : ℕ → H) (S : Set H)
    (hmono : ∀ p ∈ S, Antitone (fun n => ‖x n - p‖ ^ 2))
    (R : ℝ) (hb : ∀ n, ‖x n‖ ≤ R)
    (hlimits : ∀ r : ℕ → ℕ, Tendsto r atTop atTop → ∀ p,
      Weakly (𝕜 := 𝕜) (x ∘ r) p → p ∈ S) :
    ∃ p ∈ S, Weakly (𝕜 := 𝕜) x p := by
  obtain ⟨p, r, hr, hp⟩ := bounded_weak_subsequence (𝕜 := 𝕜) x R hb
  have hpS := hlimits r hr.tendsto_atTop p hp
  refine ⟨p, hpS, fun f => ?_⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨q, s, hs, hq⟩ := bounded_weak_subsequence (𝕜 := 𝕜) (x ∘ ns) R (fun n => hb _)
  have hqS := hlimits (ns ∘ s) (hns.comp hs.tendsto_atTop) q hq
  have hpq := fejer_weak_limits_unique x S hmono hpS hqS hr.tendsto_atTop
    (hns.comp hs.tendsto_atTop) hp hq
  subst q
  exact ⟨s, hq f⟩

/-- Weak limits of sequences approximating a closed convex set belong to it. -/
lemma weak_mem_of_approximation (C : Set H) (hc : IsClosed C)
    (hv : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C)
    {x y : ℕ → H} {p : H} (hx : Weakly (𝕜 := 𝕜) x p)
    (hy : ∀ n, y n ∈ C) (hsmall : Tendsto (fun n => ‖y n - x n‖) atTop (𝓝 0)) :
    p ∈ C := by
  have hclosed := P1.C12ConvexClosure.isWeaklyClosed_of_isClosed_convex 𝕜 H C hv hc
  have hh := (weakly_iff _ _).mp (weakly_of_perturbation hx hsmall)
  letI : TopologicalSpace H := P1.EberleinSmulian.Spec.weakTopology 𝕜 H
  exact hclosed.mem_of_tendsto hh (Eventually.of_forall hy)

/-- Either of the next two iterates is asymptotically the current one. -/
lemma next_two_small (x : ℕ → H) (b : ℕ → Prop) [DecidablePred b]
    (hs : Tendsto (fun n => ‖x (n+1) - x n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(if b n then x (n+1) else x (n+2)) - x n‖) atTop (𝓝 0) := by
  have hub : ∀ n, ‖(if b n then x (n+1) else x (n+2)) - x n‖ ≤
      ‖x (n+1) - x n‖ + ‖x (n+2) - x (n+1)‖ := by
    intro n
    split_ifs
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · have := norm_sub_le_norm_sub_add_norm_sub (x (n+2)) (x (n+1)) (x n)
      linarith
  apply squeeze_zero (fun n => norm_nonneg _) hub
  simpa only [Function.comp_def, Nat.add_assoc, zero_add] using
    hs.add (hs.comp (tendsto_add_atTop_nat 1))

end Hilbert

/-- Alternating nearest-point projections converge weakly for arbitrary
initial vectors and nonempty intersection, over either scalar field. -/
theorem alternating_weak_convergence : Spec.WeakConvergence.{u,v} := by
  intro 𝕜 H _ _ _ _ C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ hinter x₀
  let P₁ := Hilbert.Projection.convexProjection 𝕜 H C₁ hne₁ hc₁ hv₁
  let P₂ := Hilbert.Projection.convexProjection 𝕜 H C₂ hne₂ hc₂ hv₂
  let x := Spec.iteratesValue P₁ P₂ x₀
  have hx (n : ℕ) : x (n+1) = if n % 2 = 0 then P₁ (x n) else P₂ (x n) := rfl
  have hm₁ (z : H) : P₁ z ∈ C₁ :=
    (Hilbert.Projection.convexProjection_spec 𝕜 H C₁ hne₁ hc₁ hv₁ z).1
  have hm₂ (z : H) : P₂ z ∈ C₂ :=
    (Hilbert.Projection.convexProjection_spec 𝕜 H C₂ hne₂ hc₂ hv₂ z).1
  have he (p : H) (hp : p ∈ C₁ ∩ C₂) (n : ℕ) :
      ‖x (n+1) - p‖ ^ 2 + ‖x (n+1) - x n‖ ^ 2 ≤ ‖x n - p‖ ^ 2 := by
    rw [hx n]
    split_ifs
    · exact projection_energy C₁ hne₁ hc₁ hv₁ (x n) p hp.1
    · exact projection_energy C₂ hne₂ hc₂ hv₂ (x n) p hp.2
  have hmono (p : H) (hp : p ∈ C₁ ∩ C₂) : Antitone (fun n => ‖x n - p‖ ^ 2) := by
    apply antitone_nat_of_succ_le
    intro n
    nlinarith [he p hp n, sq_nonneg ‖x (n+1) - x n‖]
  obtain ⟨c, hc⟩ := hinter
  have hstep := vanishing_steps x c (he c hc)
  have hb (n : ℕ) : ‖x n‖ ≤ ‖x₀ - c‖ + ‖c‖ := by
    have hh := hmono c hc (Nat.zero_le n)
    have hdist : ‖x n - c‖ ≤ ‖x₀ - c‖ := by
      change ‖x n - c‖ ^ 2 ≤ ‖x₀ - c‖ ^ 2 at hh
      nlinarith [norm_nonneg (x n - c), norm_nonneg (x₀ - c)]
    calc
      ‖x n‖ = ‖(x n - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖x n - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖x₀ - c‖ + ‖c‖ := by linarith
  let y₁ : ℕ → H := fun n => if n % 2 = 0 then x (n+1) else x (n+2)
  let y₂ : ℕ → H := fun n => if n % 2 ≠ 0 then x (n+1) else x (n+2)
  have hy₁ (n : ℕ) : y₁ n ∈ C₁ := by
    dsimp only [y₁]
    split_ifs with hn
    · rw [hx n, ite_eq_left hn]
      exact hm₁ _
    · have hn' : (n+1) % 2 = 0 := by omega
      rw [show n+2 = (n+1)+1 by omega, hx (n+1), ite_eq_left hn']
      exact hm₁ _
  have hy₂ (n : ℕ) : y₂ n ∈ C₂ := by
    dsimp only [y₂]
    split_ifs with hn
    · rw [hx n, ite_eq_right hn]
      exact hm₂ _
    · have hn' : (n+1) % 2 ≠ 0 := by omega
      rw [show n+2 = (n+1)+1 by omega, hx (n+1), ite_eq_right hn']
      exact hm₂ _
  have hs₁ : Tendsto (fun n => ‖y₁ n - x n‖) atTop (𝓝 0) :=
    next_two_small x (fun n => n % 2 = 0) hstep
  have hs₂ : Tendsto (fun n => ‖y₂ n - x n‖) atTop (𝓝 0) :=
    next_two_small x (fun n => n % 2 ≠ 0) hstep
  have hlimits (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) (p : H)
      (hp : Weakly (𝕜 := 𝕜) (x ∘ r) p) : p ∈ C₁ ∩ C₂ := by
    constructor
    · exact weak_mem_of_approximation C₁ hc₁ hv₁ hp (fun n => hy₁ (r n)) (hs₁.comp hr)
    · exact weak_mem_of_approximation C₂ hc₂ hv₂ hp (fun n => hy₂ (r n)) (hs₂.comp hr)
  exact fejer_weak_convergence x (C₁ ∩ C₂) hmono (‖x₀ - c‖ + ‖c‖) hb hlimits

end ExpandedFA.Geometry.AlternatingConvexProjections
