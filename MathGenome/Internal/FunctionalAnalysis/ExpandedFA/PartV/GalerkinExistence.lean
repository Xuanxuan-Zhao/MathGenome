import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.GalerkinExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

noncomputable section
open Filter
open scoped Topology InnerProductSpace ComplexConjugate
namespace ExpandedFA.PartV.GalerkinExistence
universe u v w
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private theorem zero_of_diagonal_zero (a : Spec.Form 𝕜 H) {c : ℝ}
    (hc : Spec.Coercive 𝕜 H a c) {x : H} (hx : a x x = 0) : x = 0 := by
  have h := hc.2 x
  rw [hx, map_zero] at h
  by_contra hx
  have hp : 0 < c * ‖x‖ ^ 2 := mul_pos hc.1 (sq_pos_of_pos (norm_pos_iff.mpr hx))
  linarith

private theorem solution_unique (a : Spec.Form 𝕜 H) {c : ℝ}
    (hc : Spec.Coercive 𝕜 H a c) (F : Spec.Antidual 𝕜 H)
    {x y : H} (hx : ∀ v, a v x = F v) (hy : ∀ v, a v y = F v) : x = y := by
  apply sub_eq_zero.mp
  apply zero_of_diagonal_zero a hc
  rw [map_sub, hx, hy, sub_self]

private def restrictForm (a : Spec.Form 𝕜 H) (M : Submodule 𝕜 H) :
    Spec.Form 𝕜 M :=
  ((ContinuousLinearMap.compL 𝕜 M H 𝕜).flip M.subtypeL).comp (a.comp M.subtypeL)

private theorem finite_exists (a : Spec.Form 𝕜 H) {c : ℝ}
    (hc : Spec.Coercive 𝕜 H a c) (F : Spec.Antidual 𝕜 H)
    (M : Submodule 𝕜 H) [FiniteDimensional 𝕜 M] :
    ∃ u : M, ∀ v : M, a v u = F v := by
  let b := restrictForm a M
  obtain ⟨A, hA, _, _⟩ := Hilbert.RieszRepresentation.form_representation 𝕜 M b
  have hb (x y : M) : b x y = a x y := rfl
  have hinj : Function.Injective A := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    apply zero_of_diagonal_zero a hc
    change A x = 0 at hx
    rw [← hb, hA, hx, inner_zero_right]
  let G : M →L[𝕜] 𝕜 :=
    (starL 𝕜 : 𝕜 ≃L⋆[𝕜] 𝕜).toContinuousLinearMap.comp (F.comp M.subtypeL)
  let g := (InnerProductSpace.toDual 𝕜 M).symm G
  obtain ⟨u, hu⟩ := (LinearMap.surjective_of_injective (f := A.toLinearMap) hinj) g
  change A u = g at hu
  refine ⟨u, fun v => ?_⟩
  rw [← hb, hA, hu, ← inner_conj_symm v g, InnerProductSpace.toDual_symm_apply]
  change conj (conj (F v)) = F v
  exact star_star _

theorem finite_solvability : Spec.FiniteSolvability 𝕜 H := by
  intro a c hc F M _
  obtain ⟨u, hu⟩ := finite_exists a hc F M
  refine ⟨u, hu, fun z hz => ?_⟩
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply zero_of_diagonal_zero a hc
  rw [map_sub, hz ⟨_, M.sub_mem z.property u.property⟩,
    hu ⟨_, M.sub_mem z.property u.property⟩, sub_self]

theorem uniform_bound : Spec.UniformBound 𝕜 H := by
  intro a c hc F M u hu
  by_cases hz : (u : H) = 0
  · simp only [hz, norm_zero]
    exact div_nonneg (norm_nonneg F) hc.1.le
  have hp := norm_pos_iff.mpr hz
  have h : c * ‖(u : H)‖ ^ 2 ≤ ‖F‖ * ‖(u : H)‖ := calc
    _ ≤ RCLike.re (a u u) := hc.2 u
    _ = RCLike.re (F u) := congrArg _ (hu u)
    _ ≤ ‖F u‖ := RCLike.re_le_norm _
    _ ≤ _ := F.le_opNorm u
  apply (le_div_iff₀ hc.1).mpr
  nlinarith

/-- Riesz identifies the Hilbert ball with a weak-star compact dual ball.
Finite Galerkin solutions give the finite intersection property for the
weakly closed equation sets. This proves existence without an antecedent
solution or a separability assumption. -/
theorem existence_uniqueness : Spec.ExistenceUniqueness 𝕜 H := by
  intro _ a c hc F
  let R := ‖F‖ / c
  let r (v : H) := (InnerProductSpace.toDual 𝕜 H).symm (a v)
  let t (v : H) : Set (WeakDual 𝕜 H) := {f | conj (f (r v)) = F v}
  have ht (v : H) : IsClosed (t v) :=
    isClosed_eq ((WeakDual.eval_continuous (r v)).star) continuous_const
  have hcompact := WeakDual.isCompact_closedBall (𝕜 := 𝕜) (E := H) 0 R
  have hfinite (s : Finset H) :
      ((WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R) ∩ ⋂ v ∈ s, t v).Nonempty := by
    let M := Submodule.span 𝕜 (s : Set H)
    obtain ⟨u, hu⟩ := finite_exists a hc F M
    refine ⟨((InnerProductSpace.toDual 𝕜 H) (u : H)).toWeakDual, ?_, ?_⟩
    · simp only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
        Metric.mem_closedBall, dist_zero_right,
        (InnerProductSpace.toDual 𝕜 H).norm_map]
      exact uniform_bound a c hc F M u hu
    · apply Set.mem_iInter₂.mpr
      intro v hv
      change conj (⟪(u : H), r v⟫_𝕜) = F v
      rw [inner_conj_symm, InnerProductSpace.toDual_symm_apply]
      exact hu ⟨v, Submodule.subset_span hv⟩
  obtain ⟨f, _, hf⟩ := hcompact.inter_iInter_nonempty t ht hfinite
  let u := (InnerProductSpace.toDual 𝕜 H).symm f.toStrongDual
  have hu (v : H) : a v u = F v := by
    have h := Set.mem_iInter.mp hf v
    change conj (f (r v)) = F v at h
    rw [← InnerProductSpace.toDual_symm_apply (y := a v),
      ← inner_conj_symm ((InnerProductSpace.toDual 𝕜 H).symm (a v)) u]
    change conj (⟪u, r v⟫_𝕜) = F v
    rw [InnerProductSpace.toDual_symm_apply]
    exact h
  exact ⟨u, hu, fun z hz => solution_unique a hc F hz hu⟩

/-- The slot calculation behind Céa's lemma. -/
theorem cea_pointwise (a : Spec.Form 𝕜 H) {c : ℝ}
    (hc : Spec.Coercive 𝕜 H a c) (F : Spec.Antidual 𝕜 H)
    (M : Submodule 𝕜 H) (u : H) (uM : M)
    (hu : ∀ v, a v u = F v) (hM : ∀ v : M, a v uM = F v) (w : M) :
    ‖u - (uM : H)‖ ≤ (‖a‖ / c) * ‖u - (w : H)‖ := by
  let e := u - (uM : H)
  have hratio : 0 ≤ ‖a‖ / c := div_nonneg (norm_nonneg a) hc.1.le
  change ‖e‖ ≤ (‖a‖ / c) * ‖u - (w : H)‖
  by_cases he : e = 0
  · simpa only [he, norm_zero] using mul_nonneg hratio (norm_nonneg (u - (w : H)))
  have hp : 0 < ‖e‖ := norm_pos_iff.mpr he
  have horth (v : M) : a v e = 0 := by
    dsimp [e]
    rw [map_sub, hu, hM, sub_self]
  have hz : a ((w : H) - (uM : H)) e = 0 :=
    horth ⟨_, M.sub_mem w.property uM.property⟩
  have heq : a e e = a (u - (w : H)) e := by
    calc
      a e e = a ((u - (w : H)) + ((w : H) - (uM : H))) e := by
        congr 2
        dsimp [e]
        abel
      _ = a (u - (w : H)) e := by
        rw [map_add, add_apply, hz, add_zero]
  have hb : c * ‖e‖ ^ 2 ≤ ‖a‖ * ‖u - (w : H)‖ * ‖e‖ := calc
    _ ≤ RCLike.re (a e e) := hc.2 e
    _ = RCLike.re (a (u - (w : H)) e) := congrArg RCLike.re heq
    _ ≤ ‖a (u - (w : H)) e‖ := RCLike.re_le_norm _
    _ ≤ _ := a.le_opNorm₂ _ _
  have hcancel : c * ‖e‖ ≤ ‖a‖ * ‖u - (w : H)‖ :=
    (mul_le_mul_iff_left₀ hp).mp (by simpa only [pow_two, mul_assoc] using hb)
  calc
    ‖e‖ ≤ (‖a‖ * ‖u - (w : H)‖) / c := (le_div_iff₀' hc.1).mpr hcancel
    _ = (‖a‖ / c) * ‖u - (w : H)‖ := (div_mul_eq_mul_div _ _ _).symm

theorem cea_estimate : Spec.CeaEstimate 𝕜 H := by
  intro a c hc F M u uM hu hM
  have hp := cea_pointwise a hc F M u uM hu hM
  have hn : 0 ≤ ‖a‖ / c := div_nonneg (norm_nonneg a) hc.1.le
  by_cases hz : ‖a‖ / c = 0
  · simpa only [hz, zero_mul] using hp 0
  have hpos : 0 < ‖a‖ / c := lt_of_le_of_ne hn (Ne.symm hz)
  have hinf : ‖u - (uM : H)‖ / (‖a‖ / c) ≤ Metric.infDist u (M : Set H) := by
    apply (Metric.le_infDist ⟨0, M.zero_mem⟩).mpr
    intro v hv
    rw [dist_eq_norm]
    exact (div_le_iff₀' hpos).mpr (hp ⟨v, hv⟩)
  exact (div_le_iff₀' hpos).mp hinf

/-- Increasing dense families approximate every vector eventually. -/
theorem directed_dense_approximation {I : Type w} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (M : I → Submodule 𝕜 H) (hmono : Monotone M)
    (hdense : Dense (⋃ i, (M i : Set H))) (x : H) :
    Tendsto (fun i => Metric.infDist x (M i : Set H)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun i => hb.trans_le Metric.infDist_nonneg
  · intro ε hε
    obtain ⟨y, hy, hxy⟩ := hdense.exists_dist_lt x hε
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
    filter_upwards [eventually_ge_atTop i] with j hij
    exact (Metric.infDist_le_dist_of_mem (hmono hij hyi)).trans_lt hxy

/-- Céa's bound works along every filter admitting eventual approximation. -/
theorem convergence_of_approximation {I : Type w} (l : Filter I)
    (a : Spec.Form 𝕜 H) {c : ℝ} (hc : Spec.Coercive 𝕜 H a c)
    (F : Spec.Antidual 𝕜 H) (M : I → Submodule 𝕜 H) (u : H) (U : ∀ i, M i)
    (hu : ∀ v, a v u = F v) (hU : ∀ i (v : M i), a v (U i) = F v)
    (happ : Tendsto (fun i => Metric.infDist u (M i : Set H)) l (𝓝 0)) :
    Tendsto (fun i => (U i : H)) l (𝓝 u) := by
  have hb (i : I) := cea_estimate a c hc F (M i) u (U i) hu (hU i)
  have hlim : Tendsto (fun i => (‖a‖ / c) * Metric.infDist u (M i : Set H)) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul happ
  have he : Tendsto (fun i => ‖u - (U i : H)‖) l (𝓝 0) :=
    squeeze_zero (fun i => norm_nonneg _) hb hlim
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm, norm_sub_rev] using he

/-- Strong convergence entails weak convergence against the continuous linear dual. -/
theorem weaklyConverges_of_tendsto {I : Type w} {l : Filter I} {U : I → H} {u : H}
    (h : Tendsto U l (𝓝 u)) : Spec.WeaklyConverges 𝕜 H l U u :=
  fun f => (f.continuous.tendsto u).comp h

theorem dense_net : Spec.DenseNet 𝕜 H := by
  classical
  intro _ a c hc F I _ _ _ M _ hmono hdense
  obtain ⟨u, hu, hunique⟩ := existence_uniqueness a c hc F
  have hs (i : I) : ∃ z : M i, ∀ v : M i, a v z = F v := finite_exists a hc F (M i)
  choose U hU using hs
  have hconv := convergence_of_approximation atTop a hc F M u U hu hU
    (directed_dense_approximation M hmono hdense u)
  exact ⟨u, U, hu, hunique, hU,
    fun i => uniform_bound a c hc F (M i) (U i) (hU i),
    hconv, weaklyConverges_of_tendsto hconv⟩

instance finiteTrialNonempty : Nonempty (Spec.FiniteTrial 𝕜 H) :=
  ⟨⟨⊥, inferInstance⟩⟩

instance finiteTrialDirected : IsDirectedOrder (Spec.FiniteTrial 𝕜 H) := by
  constructor
  intro M N
  let : FiniteDimensional 𝕜 M.1 := M.2
  let : FiniteDimensional 𝕜 N.1 := N.2
  exact ⟨⟨M.1 ⊔ N.1, inferInstance⟩,
    (show M.1 ≤ M.1 ⊔ N.1 from le_sup_left),
    (show N.1 ≤ M.1 ⊔ N.1 from le_sup_right)⟩

theorem full_net : Spec.FullNet 𝕜 H := by
  classical
  intro _ a c hc F
  have hdense : Dense (⋃ M : Spec.FiniteTrial 𝕜 H, (M.1 : Set H)) := by
    have heq : (⋃ M : Spec.FiniteTrial 𝕜 H, (M.1 : Set H)) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_iUnion.mpr ⟨⟨𝕜 ∙ x, inferInstance⟩, Submodule.mem_span_singleton_self x⟩
    rw [heq]
    exact dense_univ
  let (M : Spec.FiniteTrial 𝕜 H) : FiniteDimensional 𝕜 M.1 := M.2
  obtain ⟨u, U, hu, huniq, hU, hbound, hstrong, hweak⟩ :=
    dense_net a c hc F (Spec.FiniteTrial 𝕜 H) (fun M => M.1)
      (fun _ _ h => h) hdense
  exact ⟨u, U, hu, huniq, hU, hbound, hweak, hstrong⟩

end ExpandedFA.PartV.GalerkinExistence
