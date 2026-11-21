import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.NodeExample
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric Filter
open scoped Topology
namespace D12Complex.NodeExample

def nodeSet : Set (ℂ × ℂ) := {p | p.2 ^ 2 = p.1 ^ 2 * (p.1 + 1)}
abbrev Node := {p : ℂ × ℂ // p ∈ nodeSet}

def origin : Node := ⟨(0, 0), by simp [nodeSet]⟩

def patch (r : ℝ) : Set Node := {p | p.val.1 ∈ ball 0 r}

def branch (s : ℂ → ℂ) (ε : ℂ) (z : ℂ) : ℂ × ℂ := (z, ε * (z * s z))

def graph (r : ℝ) (s : ℂ → ℂ) (ε : ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 ∈ ball 0 r ∧ p.2 = ε * (p.1 * s p.1)}


/-! The root is obtained from the accepted normalized local-root theorem.
On a punctured node patch, Re(y/(x*s(x))) is the continuous label ±1.
Every neighborhood meets both labels because both graph parameters tend to
(0,0). A chart would pull a small punctured disk back to such a neighborhood,
contradicting its preconnectedness. -/

theorem exists_local_branches :
    Specs.D12Complex.Ch21.NodeExample.exists_local_branches_type := by
  have hf : HolomorphicOn univ (fun z : ℂ => 1 + z) :=
    ⟨isOpen_univ, fun _ _ => differentiableAt_id.const_add 1⟩
  obtain ⟨U, s, h0, _, hs, hs0, hsq⟩ :=
    LocalLogarithmsRoots.local_root univ (fun z : ℂ => 1 + z) 0 2 1 hf
      (mem_univ _) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hs.1 0 h0
  let r := min δ (1/2)
  have hr : 0 < r := lt_min hδ (by norm_num)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : ball (0 : ℂ) r ⊆ U :=
    (ball_subset_ball (min_le_left _ _)).trans hδU
  have hs' : HolomorphicOn (ball 0 r) s := ⟨isOpen_ball, fun z hz => hs.2 z (hsub hz)⟩
  have hn : ∀ z ∈ ball (0 : ℂ) r, s z ≠ 0 := by
    intro z hz he
    have heq := hsq z (hsub hz)
    rw [he, zero_pow (by decide)] at heq
    have hz' : z = -1 := by linear_combination -heq
    have : ‖z‖ < r := mem_ball_zero_iff.mp hz
    rw [hz'] at this
    norm_num at this
    linarith
  refine ⟨r, s, hr, hr1, hs', hs0, fun z hz => ⟨hsq z (hsub hz), hn z hz⟩,
    ⟨isOpen_ball, fun z hz => differentiableAt_id.mul (hs'.2 z hz)⟩,
    ⟨isOpen_ball, fun z hz => (differentiableAt_id.mul (hs'.2 z hz)).neg⟩, ?_, ?_⟩
  · intro x hx y
    change y ^ 2 = x ^ 2 * (x + 1) ↔ _
    have h : (x * s x)^2 = x^2 * (x + 1) := by rw [mul_pow, hsq x (hsub hx)]; ring
    rw [← h, sq_eq_sq_iff_eq_or_eq_neg]
  · intro x hx
    constructor
    · intro h
      have : x * s x = 0 := by linear_combination (1/2 : ℂ) * h
      exact (mul_eq_zero.mp this).resolve_right (hn x hx)
    · intro h; simp [h]

theorem branch_parameter :
    Specs.D12Complex.Ch21.NodeExample.branch_parameter_type := by
  intro r s hs ε
  have hc : ContinuousOn (fun z => ε * (z * s z)) (ball 0 r) :=
    fun z hz => ((differentiableAt_id.mul (hs.2 z hz)).const_mul ε).continuousAt.continuousWithinAt
  refine ⟨?_, ?_, ?_⟩
  · let e : (ball (0 : ℂ) r) ≃ₜ graph r s ε :=
      { toFun := fun z => ⟨branch s ε z, z.property, rfl⟩
        invFun := fun p => ⟨p.val.1, p.property.1⟩
        left_inv := fun _ => rfl
        right_inv := by
          intro p
          apply Subtype.ext
          exact Prod.ext rfl p.property.2.symm
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact continuous_subtype_val.prodMk (hc.domRestrict)
        continuous_invFun := by fun_prop }
    exact ⟨e, fun _ => rfl⟩
  · intro z hz
    exact differentiableAt_id.prodMk ((differentiableAt_id.mul (hs.2 z hz)).const_mul ε)
  · intro z; exact deriv_id z

lemma first_ne_zero {p : Node} (hp : p ≠ origin) : p.val.1 ≠ 0 := by
  intro hx
  have hy : p.val.2 = 0 := by
    have h := p.property
    change p.val.2 ^ 2 = p.val.1 ^ 2 * (p.val.1 + 1) at h
    rw [hx] at h
    simpa using h
  apply hp
  apply Subtype.ext
  exact Prod.ext hx hy

lemma exists_branch_point (r : ℝ) (s : ℂ → ℂ) (hr : 0 < r)
    (hs : HolomorphicOn (ball 0 r) s)
    (hsq : ∀ z ∈ ball 0 r, (s z)^2 = 1 + z)
    (ε : ℂ) (hε : ε^2 = 1) (U : Set Node) (hU : IsOpen U) (h0 : origin ∈ U) :
    ∃ p ∈ U, p ≠ origin ∧ p.val.2 = ε * (p.val.1 * s p.val.1) := by
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype nodeSet origin U).mp (hU.mem_nhds h0)
  have hc : ContinuousAt (branch s ε) 0 :=
    continuousAt_id.prodMk ((continuousAt_id.mul
      (hs.2 0 (mem_ball_self hr)).continuousAt).const_mul ε)
  have hpre : ∀ᶠ t in 𝓝 (0 : ℂ), branch s ε t ∈ V := by
    apply hc
    simpa [branch, origin] using hV
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      t ∈ ball 0 r ∧ t ≠ 0 ∧ branch s ε t ∈ V := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds 0 hr),
      self_mem_nhdsWithin, nhdsWithin_le_nhds hpre] with t ht ht0 htV
    exact ⟨ht, ht0, htV⟩
  obtain ⟨t, ht, ht0, htV⟩ := hev.exists
  have hn : branch s ε t ∈ nodeSet := by
    change (ε * (t * s t))^2 = t^2 * (t + 1)
    rw [mul_pow, hε, one_mul, mul_pow, hsq t ht]
    ring
  refine ⟨⟨branch s ε t, hn⟩, hVU htV, ?_, rfl⟩
  intro he
  exact ht0 (congrArg (fun p : Node => p.val.1) he)

def branchLabel (s : ℂ → ℂ) (p : Node) : ℝ :=
  (p.val.2 / (p.val.1 * s p.val.1)).re

lemma label_eq (s : ℂ → ℂ) {p : Node} (hx : p.val.1 ≠ 0)
    (hs : s p.val.1 ≠ 0) (ε : ℂ)
    (hy : p.val.2 = ε * (p.val.1 * s p.val.1)) : branchLabel s p = ε.re := by
  simp [branchLabel, hy, mul_div_cancel_right₀ _ (mul_ne_zero hx hs)]

lemma neighborhood_puncture_disconnected (r : ℝ) (s : ℂ → ℂ) (hr : 0 < r)
    (hs : HolomorphicOn (ball 0 r) s)
    (hsq : ∀ z ∈ ball 0 r, (s z)^2 = 1 + z)
    (hn : ∀ z ∈ ball 0 r, s z ≠ 0)
    (U : Set Node) (hU : IsOpen U) (h0 : origin ∈ U) (hUr : U ⊆ patch r) :
    ¬ IsPreconnected (U \ {origin}) := by
  let W := U \ {origin}
  have hx : ∀ p ∈ W, p.val.1 ≠ 0 := fun p hp => first_ne_zero hp.2
  have hpball : ∀ p ∈ W, p.val.1 ∈ ball 0 r := fun p hp => hUr hp.1
  have hc : ContinuousOn (branchLabel s) W := by
    apply Complex.continuous_re.comp_continuousOn
    intro p hp
    apply ContinuousWithinAt.div
    · exact (continuous_snd.comp continuous_subtype_val).continuousAt.continuousWithinAt
    · exact ((continuous_fst.comp continuous_subtype_val).continuousAt.mul
        (ContinuousAt.comp (f := fun p : Node => p.val.1) (g := s)
          (hs.2 _ (hpball p hp)).continuousAt
          (continuous_fst.comp continuous_subtype_val).continuousAt)).continuousWithinAt
    · exact mul_ne_zero (hx p hp) (hn _ (hpball p hp))
  have hsign : ∀ p ∈ W, branchLabel s p = 1 ∨ branchLabel s p = -1 := by
    intro p hp
    have heq : p.val.2 ^ 2 = (p.val.1 * s p.val.1)^2 := by
      calc
        p.val.2 ^ 2 = p.val.1 ^ 2 * (p.val.1 + 1) := p.property
        _ = (p.val.1 * s p.val.1)^2 := by rw [mul_pow, hsq _ (hpball p hp)]; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
    · left
      simpa using label_eq s (hx p hp) (hn _ (hpball p hp)) 1 (by simpa using h)
    · right
      simpa using label_eq s (hx p hp) (hn _ (hpball p hp)) (-1) (by simpa using h)
  obtain ⟨p, hpU, hp0, hp⟩ := exists_branch_point r s hr hs hsq 1 (by norm_num) U hU h0
  obtain ⟨q, hqU, hq0, hq⟩ := exists_branch_point r s hr hs hsq (-1) (by norm_num) U hU h0
  have hpW : p ∈ W := ⟨hpU, hp0⟩
  have hqW : q ∈ W := ⟨hqU, hq0⟩
  have hlp : branchLabel s p = 1 := by
    simpa using label_eq s (hx p hpW) (hn _ (hpball p hpW)) 1 hp
  have hlq : branchLabel s q = -1 := by
    simpa using label_eq s (hx q hqW) (hn _ (hpball q hqW)) (-1) hq
  intro hconn
  rcases hconn.mapsTo_Ioi_or_Iio (b := (0 : ℝ)) hc (fun p hp => by rcases hsign p hp with h | h <;> simp [h]) with h | h
  · have hh := h hqW
    change (0 : ℝ) < branchLabel s q at hh
    rw [hlq] at hh
    linarith
  · have hh := h hpW
    change branchLabel s p < (0 : ℝ) at hh
    rw [hlp] at hh
    linarith

theorem puncture_disconnected :
    ∃ r : ℝ, 0 < r ∧ IsOpen (patch r) ∧ origin ∈ patch r ∧
      ∀ U : Set Node, IsOpen U → origin ∈ U → U ⊆ patch r →
        ¬ IsPreconnected (U \ {origin}) := by
  obtain ⟨r, s, hr, _, hs, _, hsq, _⟩ := exists_local_branches
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · exact isOpen_ball.preimage (continuous_fst.comp continuous_subtype_val)
  · exact mem_ball_self hr
  · exact neighborhood_puncture_disconnected r s hr hs (fun z hz => (hsq z hz).1)
      (fun z hz => (hsq z hz).2)

theorem punctured_disk_connected :
    Specs.D12Complex.Ch21.NodeExample.punctured_disk_connected_type := by
  intro c r hr
  let b : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.univBall c r
  have hbsource : b.source = univ := OpenPartialHomeomorph.univBall_source c r
  have hbtarget : b.target = ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hb0 : b 0 = c := OpenPartialHomeomorph.univBall_apply_zero c r
  have hsource : ∀ x, x ∈ b.source := by simp [hbsource]
  have himg : b '' ({0}ᶜ : Set ℂ) = ball c r \ {c} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨by simpa [hbtarget] using b.map_source (hsource x), ?_⟩
      intro he
      exact hx (b.injOn (hsource x) (hsource 0) (he.trans hb0.symm))
    · intro hy
      have hyt : y ∈ b.target := by simpa [hbtarget] using hy.1
      refine ⟨b.symm y, ?_, b.right_inv hyt⟩
      intro he
      have : y = c := by rw [← b.right_inv hyt, he, hb0]
      exact hy.2 this
  have hconn : IsConnected ({0}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 0
  rw [← himg]
  exact hconn.image b (OpenPartialHomeomorph.continuous_univBall c r).continuousOn

theorem no_chart_at_origin :
    ∀ e : OpenPartialHomeomorph Node ℂ, origin ∉ e.source := by
  intro e he
  obtain ⟨r, hr, hpr, h0r, hdisc⟩ := puncture_disconnected
  have ho : IsOpen (e.target ∩ e.symm ⁻¹' patch r) := e.isOpen_inter_preimage_symm hpr
  have hcenter : e origin ∈ e.target ∩ e.symm ⁻¹' patch r :=
    ⟨e.map_source he, by simpa [e.left_inv he] using h0r⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp ho (e origin) hcenter
  let U := e.source ∩ e ⁻¹' ball (e origin) δ
  have hU : IsOpen U := e.isOpen_inter_preimage isOpen_ball
  have h0U : origin ∈ U := ⟨he, mem_ball_self hδ⟩
  have hUr : U ⊆ patch r := by
    intro p hp
    have h := (hδsub hp.2).2
    change e.symm (e p) ∈ patch r at h
    rwa [e.left_inv hp.1] at h
  apply hdisc U hU h0U hUr
  have himg : e.symm '' (ball (e origin) δ \ {e origin}) = U \ {origin} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyt := (hδsub hy.1).1
      refine ⟨⟨e.map_target hyt, ?_⟩, ?_⟩
      · change e (e.symm y) ∈ ball (e origin) δ
        simpa [e.right_inv hyt] using hy.1
      · intro hp
        apply hy.2
        change y = e origin
        rw [← e.right_inv hyt, hp]
    · intro hp
      refine ⟨e p, ⟨hp.1.2, ?_⟩, e.left_inv hp.1.1⟩
      intro hep
      exact hp.2 (e.injOn hp.1.1 he hep)
  rw [← himg]
  exact (punctured_disk_connected (e origin) δ hδ).isPreconnected.image e.symm
    (e.symm.continuousOn.mono (fun y hy => (hδsub hy.1).1))

theorem not_riemann_surface :
    Specs.D12Complex.Ch21.NodeExample.not_riemann_surface_type := by
  rintro ⟨S⟩
  obtain ⟨e, _, he⟩ := S.isAtlas.1 origin
  exact no_chart_at_origin e.val he

end D12Complex.NodeExample
