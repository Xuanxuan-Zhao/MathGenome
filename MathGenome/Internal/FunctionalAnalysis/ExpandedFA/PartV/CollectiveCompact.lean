import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.CollectiveCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.CompactUniformConvergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

/-! Collectively compact stability, `paper.tex:22865–22896`.
The collective closure contains every approximating image and the limiting
image of the unit ball. Uniform convergence on that compact set gives both
composition estimates. A left regularizer followed by a Neumann inverse,
then the compact Fredholm alternative, gives actual two-sided inverses
with one bound for all sufficiently large indices.
-/

open Filter
open scoped Topology

namespace ExpandedFA.PartV.CollectiveCompact

universe u v
variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

lemma image_mem_collectiveClosure (Kn : ℕ → X →L[𝕜] X) (n : ℕ)
    {x : X} (hx : ‖x‖ ≤ 1) : Kn n x ∈ Spec.collectiveClosure Kn := by
  apply subset_closure
  exact Set.mem_iUnion.mpr ⟨n, ⟨x, by simpa using hx, rfl⟩⟩

lemma limit_mem_collectiveClosure (Kn : ℕ → X →L[𝕜] X) (K : X → X)
    (hlim : ∀ x, Tendsto (fun n => Kn n x) atTop (𝓝 (K x)))
    {x : X} (hx : ‖x‖ ≤ 1) : K x ∈ Spec.collectiveClosure Kn := by
  exact isClosed_closure.mem_of_tendsto (hlim x)
    (Eventually.of_forall fun n => image_mem_collectiveClosure Kn n hx)

lemma compact_each (Kn : ℕ → X →L[𝕜] X) (hcc : Spec.IsCollectivelyCompact Kn)
    (n : ℕ) : Compactness.IsCompactLinearMap (Kn n).toLinearMap := by
  apply hcc.closure_of_subset
  rintro _ ⟨x, hx, rfl⟩
  exact image_mem_collectiveClosure Kn n (by simpa using hx)

lemma compact_limit (Kn : ℕ → X →L[𝕜] X) (K : X →L[𝕜] X)
    (hcc : Spec.IsCollectivelyCompact Kn)
    (hlim : ∀ x, Tendsto (fun n => Kn n x) atTop (𝓝 (K x))) :
    Compactness.IsCompactLinearMap K.toLinearMap := by
  apply hcc.closure_of_subset
  rintro _ ⟨x, hx, rfl⟩
  exact limit_mem_collectiveClosure Kn K hlim (by simpa using hx)

/-- Uniform convergence on the collective closure controls composition even
when the right factor varies with the index. -/
lemma composition_norm_tendsto (Kn : ℕ → X →L[𝕜] X) (K : X →L[𝕜] X)
    (hunif : TendstoUniformlyOn (fun n x => Kn n x) K atTop (Spec.collectiveClosure Kn))
    (An : ℕ → X →L[𝕜] X)
    (himage : ∀ n x, ‖x‖ ≤ 1 → An n x ∈ Spec.collectiveClosure Kn) :
    Tendsto (fun n => ‖(Kn n - K).comp (An n)‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he := (Metric.tendstoUniformlyOn_iff.mp hunif) (ε / 2) (half_pos hε)
  filter_upwards [he] with n hn
  have hb : ‖(Kn n - K).comp (An n)‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (half_pos hε))
    intro x hx
    have ht := hn (An n x) (himage n x (le_of_eq hx))
    simpa only [ContinuousLinearMap.comp_apply, sub_apply,
      dist_eq_norm, norm_sub_rev] using le_of_lt ht
  simpa only [dist_zero_right, norm_norm] using lt_of_le_of_lt hb (by linarith : ε / 2 < ε)

theorem compactness_and_compositions : Spec.CompactnessAndCompositions := by
  intro 𝕜 X _ _ _ _ Kn K hcc hlim
  obtain ⟨M, hM, hb, L, hL, hLn, hu⟩ :=
    CompactUniformConvergence.banach_pointwise_compact_convergence 𝕜 X X Kn K hlim
  have hlimL : ∀ x, Tendsto (fun n => Kn n x) atTop (𝓝 (L x)) := by
    intro x
    rw [hL x]
    exact hlim x
  have huL : TendstoUniformlyOn (fun n x => Kn n x) L atTop (Spec.collectiveClosure Kn) := by
    have heq : (fun x => L x) = K := funext hL
    simpa only [heq] using hu _ hcc
  exact ⟨compact_each Kn hcc, L, hL, compact_limit Kn L hcc hlimL,
    M, hM, hb, hLn,
    composition_norm_tendsto Kn L huL Kn (fun n x hx => image_mem_collectiveClosure Kn n hx),
    composition_norm_tendsto Kn L huL (fun _ => L)
      (fun _ x hx => limit_mem_collectiveClosure Kn L hlimL hx)⟩

/-- The algebraic regularizer identity needs only the left inverse of I-K. -/
lemma regularizer_identity (K L R : X →L[𝕜] X)
    (hR : R.comp (ContinuousLinearMap.id 𝕜 X - K) = ContinuousLinearMap.id 𝕜 X) :
    (ContinuousLinearMap.id 𝕜 X + R.comp L).comp (ContinuousLinearMap.id 𝕜 X - L) =
      ContinuousLinearMap.id 𝕜 X - R.comp ((L - K).comp L) := by
  have hRI : R = ContinuousLinearMap.id 𝕜 X + R.comp K := by
    exact eq_add_of_sub_eq (by simpa only [ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.comp_id] using hR)
  have hRL : R.comp L = L + R.comp (K.comp L) := by
    calc
      R.comp L = (ContinuousLinearMap.id 𝕜 X + R.comp K).comp L :=
        congrArg (fun Q : X →L[𝕜] X => Q.comp L) hRI
      _ = L + R.comp (K.comp L) := by
        rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.id_comp,
          ContinuousLinearMap.comp_assoc]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
  rw [hRL]
  abel

/-- A uniformly bounded left regularizer and a small compact-composition
error yield uniformly bounded genuine inverses, by the Fredholm alternative. -/
lemma eventual_bounded_inverses [CompleteSpace X]
    (Kn : ℕ → X →L[𝕜] X) (K R : X →L[𝕜] X)
    (hc : ∀ n, Compactness.IsCompactLinearMap (Kn n).toLinearMap)
    (hR : R.comp (ContinuousLinearMap.id 𝕜 X - K) = ContinuousLinearMap.id 𝕜 X)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ n, ‖Kn n‖ ≤ M)
    (he : Tendsto (fun n => ‖(Kn n - K).comp (Kn n)‖) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ Rn : X →L[𝕜] X,
        (ContinuousLinearMap.id 𝕜 X - Kn n).comp Rn = ContinuousLinearMap.id 𝕜 X ∧
        Rn.comp (ContinuousLinearMap.id 𝕜 X - Kn n) = ContinuousLinearMap.id 𝕜 X ∧
        ‖Rn‖ ≤ C := by
  let S (n : ℕ) : X →L[𝕜] X := R.comp ((Kn n - K).comp (Kn n))
  let B (n : ℕ) : X →L[𝕜] X := ContinuousLinearMap.id 𝕜 X + R.comp (Kn n)
  have hs : Tendsto (fun n => ‖S n‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => R.opNorm_comp_le _)
    simpa using tendsto_const_nhds.mul he
  have hsmall : ∀ᶠ n in atTop, ‖S n‖ < (1 / 2 : ℝ) :=
    (tendsto_order.1 hs).2 _ (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨2 * (1 + ‖R‖ * M), by positivity, N, ?_⟩
  intro n hn
  have hsn : ‖S n‖ < 1 / 2 := hN n hn
  obtain ⟨V, _, _, _, _, hVleft, hVnorm, _, _⟩ :=
    ExpandedFA.P1.C03Neumann.neumann_inversion 𝕜 X (S n) (by linarith)
  have hV2 : ‖V‖ ≤ 2 := by
    have hd : 0 < 1 - ‖S n‖ := by linarith
    have hdiv : 1 / (1 - ‖S n‖) ≤ 2 := (div_le_iff₀ hd).2 (by linarith)
    exact hVnorm.trans hdiv
  let Rn : X →L[𝕜] X := V.comp (B n)
  have hleft : Rn.comp (ContinuousLinearMap.id 𝕜 X - Kn n) =
      ContinuousLinearMap.id 𝕜 X := by
    dsimp [Rn]
    rw [ContinuousLinearMap.comp_assoc, regularizer_identity K (Kn n) R hR]
    exact hVleft
  have hinj : Function.Injective (ContinuousLinearMap.id 𝕜 X - Kn n) := by
    intro x y hxy
    have ht := congrArg Rn hxy
    have hx := congrArg (fun Q : X →L[𝕜] X => Q x) hleft
    have hy := congrArg (fun Q : X →L[𝕜] X => Q y) hleft
    change Rn ((ContinuousLinearMap.id 𝕜 X - Kn n) x) = x at hx
    change Rn ((ContinuousLinearMap.id 𝕜 X - Kn n) y) = y at hy
    exact hx.symm.trans (ht.trans hy)
  have hsurj := (Fredholm.riesz_schauder_alternative (Kn n) (hc n)).mp hinj
  have hright : (ContinuousLinearMap.id 𝕜 X - Kn n).comp Rn =
      ContinuousLinearMap.id 𝕜 X := by
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have hx := congrArg (fun Q : X →L[𝕜] X => Q x) hleft
    change Rn ((ContinuousLinearMap.id 𝕜 X - Kn n) x) = x at hx
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hx]
  refine ⟨Rn, hright, hleft, ?_⟩
  have hB : ‖B n‖ ≤ 1 + ‖R‖ * M := by
    calc
      ‖B n‖ ≤ ‖ContinuousLinearMap.id 𝕜 X‖ + ‖R.comp (Kn n)‖ := norm_add_le _ _
      _ ≤ 1 + ‖R‖ * M := add_le_add (ContinuousLinearMap.norm_id_le)
        ((R.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg R)))
  exact (V.opNorm_comp_le _).trans (mul_le_mul hV2 hB (norm_nonneg _) (by norm_num))

theorem stability : Spec.Stability := by
  intro 𝕜 X _ _ _ _ Kn K hcc hlim hinj
  obtain ⟨hc, L, hL, hcompact, M, hM, hb, _, he, _⟩ :=
    compactness_and_compositions 𝕜 X Kn K hcc hlim
  have hinjL : Function.Injective (ContinuousLinearMap.id 𝕜 X - L) := by
    change Function.Injective (fun x => x - L x)
    simpa only [hL] using hinj
  have hsurj := (Fredholm.riesz_schauder_alternative L hcompact).mp hinjL
  obtain ⟨e, heq⟩ := Fredholm.riesz_schauder_bounded_inverse L hcompact ⟨hinjL, hsurj⟩
  let R : X →L[𝕜] X := e.symm.toContinuousLinearMap
  have hright : (ContinuousLinearMap.id 𝕜 X - L).comp R = ContinuousLinearMap.id 𝕜 X := by
    ext x
    exact (heq (e.symm x)).symm.trans (e.apply_symm_apply x)
  have hleft : R.comp (ContinuousLinearMap.id 𝕜 X - L) = ContinuousLinearMap.id 𝕜 X := by
    ext x
    change e.symm ((ContinuousLinearMap.id 𝕜 X - L) x) = x
    rw [← heq x, e.symm_apply_apply]
  obtain ⟨C, hC, N, hN⟩ := eventual_bounded_inverses Kn L R hc hleft M hM hb he
  refine ⟨L, hL, hcompact, R, hright, hleft, C, hC, N, ?_⟩
  intro n hn
  obtain ⟨Rn, hnright, hnleft, hnorm⟩ := hN n hn
  refine ⟨Rn, hnright, hnleft, hnorm, ?_⟩
  intro un u fn f hun hu
  have hres : (ContinuousLinearMap.id 𝕜 X - Kn n) (un - u) =
      (Kn n - L) u + (fn - f) := by
    simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub]
    rw [← hun, ← hu, ← hL u]
    abel
  have hinv := congrArg (fun Q : X →L[𝕜] X => Q (un - u)) hnleft
  change Rn ((ContinuousLinearMap.id 𝕜 X - Kn n) (un - u)) = un - u at hinv
  calc
    ‖un - u‖ = ‖Rn ((Kn n - L) u + (fn - f))‖ := by rw [← hres, hinv]
    _ ≤ C * ‖(Kn n - L) u + (fn - f)‖ := Rn.le_of_opNorm_le hnorm _
    _ ≤ C * (‖(Kn n - L) u‖ + ‖fn - f‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (le_of_lt hC)

end ExpandedFA.PartV.CollectiveCompact
