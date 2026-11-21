import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjointRelativeSum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.OneSidedSubspaceGap
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace ExpandedFA.Unbounded.RelativeSum

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The coordinate in the domain of a graph vector. -/
def graphDomainMap (A : Operator 𝕜 X Y) : A.graph →ₗ[𝕜] A.domain where
  toFun z := ⟨z.val.1, LinearPMap.mem_domain_of_mem_graph z.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma graphDomainMap_apply (A : Operator 𝕜 X Y) (z : A.graph) :
    A (graphDomainMap A z) = z.val.2 := by
  obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp z.property
  exact (congrArg (fun u : A.domain => A u) (Subtype.ext hx.symm)).trans hy

/-- Closedness is stable under a perturbation with relative bound below one.
The perturbation need only be defined on D(A). -/
theorem closed_perturbation [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (b : A.domain →ₗ[𝕜] Y) (hA : A.IsClosed)
    (k C : ℝ) (hk : 0 ≤ k) (hk1 : k < 1) (hC : 0 ≤ C)
    (hb : ∀ x : A.domain, ‖b x‖ ≤ k * ‖A x‖ + C * ‖(x : X)‖) :
    (⟨A.domain, A.toFun + b⟩ : Operator 𝕜 X Y).IsClosed := by
  letI : CompleteSpace A.graph := hA.completeSpace_coe
  let L : A.graph →ₗ[𝕜] X × Y :=
    (A.domain.subtype.comp (graphDomainMap A)).prod
      ((A.toFun + b).comp (graphDomainMap A))
  have hL : ∀ z : A.graph, L z = (z.val.1, z.val.2 + b (graphDomainMap A z)) := by
    intro z
    change (z.val.1, A (graphDomainMap A z) + b (graphDomainMap A z)) = _
    rw [graphDomainMap_apply]
  have hbound : ∀ z, ‖L z‖ ≤ (1 + k + C) * ‖z‖ := by
    intro z
    rw [hL, Prod.norm_def]
    have hx : ‖z.val.1‖ ≤ ‖z‖ := norm_fst_le z.val
    have hy : ‖z.val.2‖ ≤ ‖z‖ := norm_snd_le z.val
    have hbz := hb (graphDomainMap A z)
    simp only [graphDomainMap_apply] at hbz
    change ‖b (graphDomainMap A z)‖ ≤ k * ‖z.val.2‖ + C * ‖z.val.1‖ at hbz
    apply max_le
    · nlinarith [norm_nonneg z, mul_nonneg hk (norm_nonneg z),
        mul_nonneg hC (norm_nonneg z)]
    · have := norm_add_le z.val.2 (b (graphDomainMap A z))
      nlinarith [mul_le_mul_of_nonneg_left hx hC, mul_le_mul_of_nonneg_left hy hk]
  let F : A.graph →L[𝕜] X × Y := L.mkContinuous _ hbound
  have hlow : ∀ z : A.graph, ‖z‖ ≤ ((1 + C) / (1 - k)) * ‖F z‖ := by
    intro z
    have hnorm : ‖F z‖ = max ‖z.val.1‖ ‖z.val.2 + b (graphDomainMap A z)‖ := by
      change ‖L z‖ = _
      rw [hL, Prod.norm_def]
    have hx : ‖z.val.1‖ ≤ ‖F z‖ := by rw [hnorm]; exact le_max_left _ _
    have hs : ‖z.val.2 + b (graphDomainMap A z)‖ ≤ ‖F z‖ := by
      rw [hnorm]; exact le_max_right _ _
    have hbz := hb (graphDomainMap A z)
    simp only [graphDomainMap_apply] at hbz
    change ‖b (graphDomainMap A z)‖ ≤ k * ‖z.val.2‖ + C * ‖z.val.1‖ at hbz
    have hy : ‖z.val.2‖ ≤ ‖z.val.2 + b (graphDomainMap A z)‖ +
        ‖b (graphDomainMap A z)‖ := by
      simpa using norm_sub_le (z.val.2 + b (graphDomainMap A z)) (b (graphDomainMap A z))
    have hpos : 0 < 1 - k := sub_pos.mpr hk1
    have h2 : ‖z.val.2‖ ≤ ((1 + C) / (1 - k)) * ‖F z‖ := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hx hC]
    have h1 : 1 ≤ (1 + C) / (1 - k) := (le_div_iff₀ hpos).mpr (by linarith)
    change max ‖z.val.1‖ ‖z.val.2‖ ≤ _
    exact max_le (hx.trans (le_mul_of_one_le_left (norm_nonneg _) h1)) h2
  have hcoef : 0 ≤ (1 + C) / (1 - k) := by positivity
  have ha : AntilipschitzWith ⟨(1 + C) / (1 - k), hcoef⟩ F :=
    AddMonoidHomClass.antilipschitz_of_bound F hlow
  have hrange : Set.range F =
      ((⟨A.domain, A.toFun + b⟩ : Operator 𝕜 X Y).graph : Set (X × Y)) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact (LinearPMap.mem_graph_iff _).mpr ⟨graphDomainMap A u, rfl, rfl⟩
    · intro hz
      obtain ⟨x, hx, hy⟩ := (LinearPMap.mem_graph_iff _).mp hz
      refine ⟨⟨((x : X), A x), A.mem_graph x⟩, ?_⟩
      change ((x : X), (A.toFun + b) x) = z
      exact Prod.ext hx hy
  change _root_.IsClosed _
  rw [← hrange]
  exact ha.isClosed_range F.uniformContinuous

/-- The graph of the perturbed adjoint is close to the original adjoint graph.
Hahn–Banach is applied on X × Y; coordinate restrictions of an extension have
norm at most its norm, so no identification with a bidual is involved. -/
theorem adjoint_gap (A : Operator 𝕜 X Y) (b : A.domain →ₗ[𝕜] Y)
    (hA : Dense (A.domain : Set X)) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ x : A.domain, ‖b x‖ ≤ ε * max ‖(x : X)‖ ‖A x‖) :
    OneSidedSubspaceGap.gap
      (banachAdjoint (⟨A.domain, A.toFun + b⟩ : Operator 𝕜 X Y)).graph
      (banachAdjoint A).graph ≤ ε := by
  let S : Operator 𝕜 X Y := ⟨A.domain, A.toFun + b⟩
  apply OneSidedSubspaceGap.gap_le
  intro p hp hpn
  have hpval : ∀ x : A.domain, p.2 (x : X) = p.1 (A x + b x) := by
    rw [banachAdjoint_graph S hA] at hp
    exact hp
  let g : (X × Y) →L[𝕜] 𝕜 :=
    p.1.comp (ContinuousLinearMap.snd 𝕜 X Y) -
      p.2.comp (ContinuousLinearMap.fst 𝕜 X Y)
  let f := g.comp A.graph.subtypeL
  have hfn : ‖f‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ hε
    intro z
    have hfz : f z = -p.1 (b (graphDomainMap A z)) := by
      change p.1 z.val.2 - p.2 z.val.1 = _
      have hpz := hpval (graphDomainMap A z)
      rw [graphDomainMap_apply] at hpz
      change p.2 z.val.1 = _ at hpz
      rw [hpz, map_add]
      exact sub_add_cancel_left _ _
    rw [hfz, norm_neg]
    have hq : ‖p.1‖ ≤ 1 := (norm_fst_le p).trans hpn
    have hbz := hb (graphDomainMap A z)
    rw [graphDomainMap_apply] at hbz
    change ‖b (graphDomainMap A z)‖ ≤ ε * ‖z‖ at hbz
    exact (p.1.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hq (norm_nonneg _)).trans
      (by simpa using hbz))
  obtain ⟨F, hF, hFnorm⟩ := exists_extension_norm_eq A.graph f
  let Fx : X →L[𝕜] 𝕜 := F.comp (ContinuousLinearMap.inl 𝕜 X Y)
  let Fy : Y →L[𝕜] 𝕜 := F.comp (ContinuousLinearMap.inr 𝕜 X Y)
  have hFx : ‖Fx‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ hε
    intro x
    have := F.le_opNorm (x, 0)
    change ‖F (x, 0)‖ ≤ _
    simpa using this.trans (mul_le_mul_of_nonneg_right (hFnorm.trans_le hfn) (norm_nonneg (x, (0 : Y))))
  have hFy : ‖Fy‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ hε
    intro y
    have := F.le_opNorm (0, y)
    change ‖F (0, y)‖ ≤ _
    simpa using this.trans (mul_le_mul_of_nonneg_right (hFnorm.trans_le hfn) (norm_nonneg ((0 : X), y)))
  have hmem : (p.1 - Fy, p.2 + Fx) ∈ (banachAdjoint A).graph := by
    rw [banachAdjoint_graph A hA]
    intro x
    have hext := hF ⟨((x : X), A x), A.mem_graph x⟩
    change F ((x : X), A x) = p.1 (A x) - p.2 (x : X) at hext
    have hadd := F.map_add ((x : X), 0) (0, A x)
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hadd
    change p.2 (x : X) + F ((x : X), 0) = p.1 (A x) - F (0, A x)
    linear_combination hext - hadd
  calc
    Metric.infDist p ((banachAdjoint A).graph : Set _) ≤
        dist p (p.1 - Fy, p.2 + Fx) := Metric.infDist_le_dist_of_mem hmem
    _ ≤ ε := by
      rw [dist_eq_norm, Prod.norm_def]
      change max ‖p.1 - (p.1 - Fy)‖ ‖p.2 - (p.2 + Fx)‖ ≤ ε
      simpa using max_le hFy hFx

/-- A graph perturbation can be estimated using the same domain vector. -/
theorem graph_gap (A : Operator 𝕜 X Y) (b : A.domain →ₗ[𝕜] Y)
    (ε : ℝ) (hε : 0 ≤ ε) (hb : ∀ x : A.domain, ‖b x‖ ≤ ε * max ‖(x : X)‖ ‖A x‖) :
    OneSidedSubspaceGap.gap A.graph
      (⟨A.domain, A.toFun + b⟩ : Operator 𝕜 X Y).graph ≤ ε := by
  apply OneSidedSubspaceGap.gap_le
  intro z hz hzn
  obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp hz
  have hmem : ((x : X), A x + b x) ∈
      (⟨A.domain, A.toFun + b⟩ : Operator 𝕜 X Y).graph :=
    (⟨A.domain, A.toFun + b⟩ : Operator 𝕜 X Y).mem_graph x
  calc
    Metric.infDist z _ ≤ dist z ((x : X), A x + b x) := Metric.infDist_le_dist_of_mem hmem
    _ = ‖b x‖ := by
      change dist (z.1, z.2) _ = _
      rw [← hx, ← hy, dist_eq_norm]
      simp
    _ ≤ ε * ‖z‖ := by simpa [← hx, ← hy, Prod.norm_def] using hb x
    _ ≤ ε := by
      simpa using mul_le_mul_of_nonneg_left hzn hε

/-- The small-step domain theorem. The perturbation on the dual domain is
specified through its actual scalar-linear pairing, not an assumed adjoint law. -/
theorem adjoint_perturbation_small
    (A : Operator 𝕜 X Y) (hA : Dense (A.domain : Set X))
    (b : A.domain →ₗ[𝕜] Y)
    (c : (banachAdjoint A).domain →ₗ[𝕜] (X →L[𝕜] 𝕜))
    (hb : ∀ x : A.domain, ‖b x‖ ≤ (1 / 3 : ℝ) * max ‖(x : X)‖ ‖A x‖)
    (hc : ∀ q : (banachAdjoint A).domain,
      ‖c q‖ ≤ (1 / 3 : ℝ) * max ‖(q : Y →L[𝕜] 𝕜)‖ ‖banachAdjoint A q‖)
    (hpair : ∀ (q : (banachAdjoint A).domain) (x : A.domain),
      c q (x : X) = (q : Y →L[𝕜] 𝕜) (b x)) :
    banachAdjoint (⟨A.domain, A.toFun + b⟩ : Operator 𝕜 X Y) =
      ⟨(banachAdjoint A).domain, (banachAdjoint A).toFun + c⟩ := by
  let S : Operator 𝕜 X Y := ⟨A.domain, A.toFun + b⟩
  let T : Operator 𝕜 (Y →L[𝕜] 𝕜) (X →L[𝕜] 𝕜) :=
    ⟨(banachAdjoint A).domain, (banachAdjoint A).toFun + c⟩
  have hT : T.IsClosed := by
    apply closed_perturbation (banachAdjoint A) c (banachAdjoint_closed A hA)
      (1 / 3) (1 / 3) (by norm_num) (by norm_num) (by norm_num)
    intro q
    have := hc q
    have hm := max_le_add_of_nonneg (norm_nonneg (q : Y →L[𝕜] 𝕜))
      (norm_nonneg (banachAdjoint A q))
    nlinarith
  have hle : T.graph ≤ (banachAdjoint S).graph := by
    intro p hp
    obtain ⟨q, hq, hp⟩ := T.mem_graph_iff.mp hp
    change (p.1, p.2) ∈ _
    rw [← hq, ← hp, banachAdjoint_graph S hA]
    intro x
    change (banachAdjoint A q + c q) (x : X) = (q : Y →L[𝕜] 𝕜) (A x + b x)
    rw [_root_.add_apply, map_add, hpair, banachAdjoint_apply A hA]
  have hg1 := adjoint_gap A b hA (1 / 3) (by norm_num) hb
  have hg2 := graph_gap (banachAdjoint A) c (1 / 3) (by norm_num) hc
  have htri := OneSidedSubspaceGap.gap_triangle (banachAdjoint S).graph
    (banachAdjoint A).graph T.graph
  have hglt : OneSidedSubspaceGap.gap (banachAdjoint S).graph T.graph < 1 := by
    have h1 := OneSidedSubspaceGap.gap_nonneg (banachAdjoint S).graph (banachAdjoint A).graph
    have h2 := OneSidedSubspaceGap.gap_nonneg (banachAdjoint A).graph T.graph
    change OneSidedSubspaceGap.gap (banachAdjoint S).graph (banachAdjoint A).graph ≤ 1 / 3 at hg1
    change OneSidedSubspaceGap.gap (banachAdjoint A).graph T.graph ≤ 1 / 3 at hg2
    nlinarith
  apply LinearPMap.eq_of_eq_graph
  change (banachAdjoint S).graph = T.graph
  by_contra hne
  have hlt : T.graph < (banachAdjoint S).graph := lt_of_le_of_ne hle (Ne.symm hne)
  have heq := OneSidedSubspaceGap.gap_eq_one_of_lt (banachAdjoint S).graph T.graph hT hlt
  linarith

/-- A bound uniform along the whole segment of relatively bounded sums. -/
lemma uniform_bound (u v : Y) (r k C t : ℝ)
    (_hr : 0 ≤ r) (hk : 0 ≤ k) (hk1 : k < 1) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hb : ‖v‖ ≤ k * ‖u‖ + C * r) :
    ‖v‖ ≤ ((k + C) / (1 - k)) * max r ‖u + (t : 𝕜) • v‖ := by
  let m := max r ‖u + (t : 𝕜) • v‖
  have hx : r ≤ m := le_max_left _ _
  have hs : ‖u + (t : 𝕜) • v‖ ≤ m := le_max_right _ _
  have hnorm : ‖(t : 𝕜) • v‖ = t * ‖v‖ := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg ht]
  have hu : ‖u‖ ≤ ‖u + (t : 𝕜) • v‖ + t * ‖v‖ := by
    simpa [hnorm] using norm_sub_le (u + (t : 𝕜) • v) ((t : 𝕜) • v)
  have hkt : k * t ≤ k := by nlinarith
  have hest : (1 - k) * ‖v‖ ≤ (k + C) * m := by
    nlinarith [mul_le_mul_of_nonneg_left hx hC,
      mul_le_mul_of_nonneg_left hs hk,
      mul_le_mul_of_nonneg_right hkt (norm_nonneg v)]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sub_pos.mpr hk1)).mpr (by nlinarith)

/-- Operators along the original, fixed domain. -/
abbrev family (A : Operator 𝕜 X Y) (b : A.domain →ₗ[𝕜] Y) (t : ℝ) : Operator 𝕜 X Y :=
  ⟨A.domain, A.toFun + (t : 𝕜) • b⟩

@[simp] lemma family_zero (A : Operator 𝕜 X Y) (b : A.domain →ₗ[𝕜] Y) :
    family A b 0 = A := by
  simp [family]

lemma family_step (A : Operator 𝕜 X Y) (b : A.domain →ₗ[𝕜] Y) (t h : ℝ) :
    (⟨(family A b t).domain, (family A b t).toFun + (h : 𝕜) • b⟩ : Operator 𝕜 X Y) =
      family A b (t + h) := by
  simp only [family, RCLike.ofReal_add, add_smul, add_assoc]

lemma perturbation_congr {U V : Operator 𝕜 X Y} (e : U = V)
    (b : V.domain →ₗ[𝕜] Y) :
    (⟨U.domain, U.toFun + b.comp (Submodule.inclusion (congrArg LinearPMap.domain e).le)⟩ :
      Operator 𝕜 X Y) = ⟨V.domain, V.toFun + b⟩ := by
  subst V
  rfl

lemma apply_congr {U V : Operator 𝕜 X Y} (e : U = V) (x : U.domain) :
    U x = V (Submodule.inclusion (congrArg LinearPMap.domain e).le x) := by
  subst V
  rfl

/-- Finite continuation of the small-step domain theorem along A + t b. -/
theorem family_adjoint (A : Operator 𝕜 X Y) (hA : Dense (A.domain : Set X))
    (b : A.domain →ₗ[𝕜] Y)
    (c : (banachAdjoint A).domain →ₗ[𝕜] (X →L[𝕜] 𝕜))
    (k C k' C' : ℝ) (hk : 0 ≤ k) (hk1 : k < 1) (hC : 0 ≤ C)
    (hk' : 0 ≤ k') (hk1' : k' < 1) (hC' : 0 ≤ C')
    (hb : ∀ x : A.domain, ‖b x‖ ≤ k * ‖A x‖ + C * ‖(x : X)‖)
    (hc : ∀ q : (banachAdjoint A).domain,
      ‖c q‖ ≤ k' * ‖banachAdjoint A q‖ + C' * ‖(q : Y →L[𝕜] 𝕜)‖)
    (hpair : ∀ (q : (banachAdjoint A).domain) (x : A.domain),
      c q (x : X) = (q : Y →L[𝕜] 𝕜) (b x)) :
    banachAdjoint (family A b 1) = family (banachAdjoint A) c 1 := by
  let R := (k + C) / (1 - k)
  let R' := (k' + C') / (1 - k')
  have hR : 0 ≤ R := div_nonneg (add_nonneg hk hC) (sub_pos.mpr hk1).le
  have hR' : 0 ≤ R' := div_nonneg (add_nonneg hk' hC') (sub_pos.mpr hk1').le
  have step : ∀ t h : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ h →
      h * R ≤ 1 / 3 → h * R' ≤ 1 / 3 →
      banachAdjoint (family A b t) = family (banachAdjoint A) c t →
      banachAdjoint (family A b (t + h)) = family (banachAdjoint A) c (t + h) := by
    intro t h ht ht1 hh hsmall hsmall' heq
    let At := family A b t
    let e : (banachAdjoint At).domain →ₗ[𝕜] (banachAdjoint A).domain :=
      Submodule.inclusion (congrArg LinearPMap.domain heq).le
    let d := ((h : 𝕜) • c).comp e
    have hbsmall : ∀ x : At.domain,
        ‖((h : 𝕜) • b) x‖ ≤ (1 / 3 : ℝ) * max ‖(x : X)‖ ‖At x‖ := by
      intro x
      change ‖(h : 𝕜) • b x‖ ≤ _
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hh]
      have hu := uniform_bound (𝕜 := 𝕜) (A x) (b x) ‖(x : X)‖ k C t
        (norm_nonneg _) hk hk1 hC ht ht1 (hb x)
      have hm : 0 ≤ max ‖(x : X)‖ ‖At x‖ := le_max_of_le_left (norm_nonneg _)
      change ‖b x‖ ≤ R * max ‖(x : X)‖ ‖At x‖ at hu
      calc
        h * ‖b x‖ ≤ h * (R * max ‖(x : X)‖ ‖At x‖) := mul_le_mul_of_nonneg_left hu hh
        _ = (h * R) * max ‖(x : X)‖ ‖At x‖ := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hm
    have hcsmall : ∀ q : (banachAdjoint At).domain,
        ‖d q‖ ≤ (1 / 3 : ℝ) * max ‖(q : Y →L[𝕜] 𝕜)‖ ‖banachAdjoint At q‖ := by
      intro q
      have hu := uniform_bound (𝕜 := 𝕜) (banachAdjoint A (e q)) (c (e q))
        ‖(e q : Y →L[𝕜] 𝕜)‖ k' C' t (norm_nonneg _) hk' hk1' hC' ht ht1 (hc (e q))
      have heval := apply_congr heq q
      change banachAdjoint At q = banachAdjoint A (e q) + (t : 𝕜) • c (e q) at heval
      change ‖(h : 𝕜) • c (e q)‖ ≤ _
      rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hh, heval]
      have hm : 0 ≤ max ‖(q : Y →L[𝕜] 𝕜)‖
          ‖banachAdjoint A (e q) + (t : 𝕜) • c (e q)‖ :=
        le_max_of_le_left (norm_nonneg _)
      change ‖c (e q)‖ ≤ R' * max ‖(q : Y →L[𝕜] 𝕜)‖
        ‖banachAdjoint A (e q) + (t : 𝕜) • c (e q)‖ at hu
      calc
        h * ‖c (e q)‖ ≤ h * (R' * max ‖(q : Y →L[𝕜] 𝕜)‖
          ‖banachAdjoint A (e q) + (t : 𝕜) • c (e q)‖) := mul_le_mul_of_nonneg_left hu hh
        _ = (h * R') * max ‖(q : Y →L[𝕜] 𝕜)‖
          ‖banachAdjoint A (e q) + (t : 𝕜) • c (e q)‖ := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hsmall' hm
    have hpairsmall : ∀ (q : (banachAdjoint At).domain) (x : At.domain),
        d q (x : X) = (q : Y →L[𝕜] 𝕜) (((h : 𝕜) • b) x) := by
      intro q x
      change ((h : 𝕜) • c (e q)) (x : X) = (q : Y →L[𝕜] 𝕜) ((h : 𝕜) • b x)
      rw [smul_apply, hpair, map_smul]
      rfl
    have hlocal := adjoint_perturbation_small At hA ((h : 𝕜) • b) d
      hbsmall hcsmall hpairsmall
    rw [family_step A b t h] at hlocal
    exact hlocal.trans ((perturbation_congr heq ((h : 𝕜) • c)).trans
      (family_step (banachAdjoint A) c t h))
  obtain ⟨N, hN⟩ := exists_nat_gt (max (3 * R) (3 * R') + 1)
  have hNpos : 0 < (N : ℝ) := by
    have := le_max_left (3 * R) (3 * R')
    linarith
  have hs : (1 / (N : ℝ)) * R ≤ 1 / 3 := by
    rw [one_div_mul_eq_div, div_le_iff₀ hNpos]
    have := le_max_left (3 * R) (3 * R')
    linarith
  have hs' : (1 / (N : ℝ)) * R' ≤ 1 / 3 := by
    rw [one_div_mul_eq_div, div_le_iff₀ hNpos]
    have := le_max_right (3 * R) (3 * R')
    linarith
  have H : ∀ n : ℕ, n ≤ N →
      banachAdjoint (family A b ((n : ℝ) / N)) =
        family (banachAdjoint A) c ((n : ℝ) / N) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn' : n ≤ N := Nat.le_of_succ_le hn
      have ht : 0 ≤ (n : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNpos.le
      have ht1 : (n : ℝ) / N ≤ 1 := (div_le_one hNpos).mpr (by exact_mod_cast hn')
      have heq := step ((n : ℝ) / N) (1 / N) ht ht1
        (div_nonneg zero_le_one hNpos.le) hs hs' (ih hn')
      simpa only [Nat.cast_add, Nat.cast_one, add_div] using heq
  simpa only [div_self (ne_of_gt hNpos)] using H N le_rfl

end ExpandedFA.Unbounded.RelativeSum

namespace ExpandedFA.Unbounded

/-- The adjoint of a relatively bounded sum, including its exact domain. -/
theorem banach_adjoint_relative_sum : BanachAdjointRelativeSumSpec.RelativeSum := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A B hAcl hBcl hA hB hD hD' k C k' C'
    hk hk1 hC hk' hk1' hC' hb hc
  let b : A.domain →ₗ[𝕜] Y := B.toFun.comp (Submodule.inclusion hD)
  let c : (banachAdjoint A).domain →ₗ[𝕜] (X →L[𝕜] 𝕜) :=
    (banachAdjoint B).toFun.comp (Submodule.inclusion hD')
  have hpair : ∀ (q : (banachAdjoint A).domain) (x : A.domain),
      c q (x : X) = (q : Y →L[𝕜] 𝕜) (b x) := by
    intro q x
    exact banachAdjoint_apply B hB (Submodule.inclusion hD' q) (Submodule.inclusion hD x)
  have hsum : A + B = RelativeSum.family A b 1 := by
    apply LinearPMap.ext (by exact inf_eq_left.mpr hD)
    intro x hx hy
    change A ⟨x, hx.1⟩ + B ⟨x, hx.2⟩ =
      A ⟨x, hy⟩ + ((1 : ℝ) : 𝕜) • B ⟨x, hD hy⟩
    rw [RCLike.ofReal_one, one_smul]
  have hsum' : banachAdjoint A + banachAdjoint B =
      RelativeSum.family (banachAdjoint A) c 1 := by
    apply LinearPMap.ext (by exact inf_eq_left.mpr hD')
    intro q hq hr
    change banachAdjoint A ⟨q, hq.1⟩ + banachAdjoint B ⟨q, hq.2⟩ =
      banachAdjoint A ⟨q, hr⟩ + ((1 : ℝ) : 𝕜) • banachAdjoint B ⟨q, hD' hr⟩
    rw [RCLike.ofReal_one, one_smul]
  have hclosed : (A + B).IsClosed := by
    rw [hsum]
    simpa only [RelativeSum.family, RCLike.ofReal_one, one_smul] using
      RelativeSum.closed_perturbation A b hAcl k C hk hk1 hC hb
  have hadj := RelativeSum.family_adjoint A hA b c k C k' C' hk hk1 hC hk' hk1' hC'
    hb hc hpair
  have heq : banachAdjoint (A + B) = banachAdjoint A + banachAdjoint B := by
    rw [hsum, hsum']
    exact hadj
  refine ⟨inf_eq_left.mpr hD, hclosed, ?_, heq⟩
  change (banachAdjoint (A + B)).domain = (banachAdjoint A).domain
  rw [heq]
  exact inf_eq_left.mpr hD'

end ExpandedFA.Unbounded
