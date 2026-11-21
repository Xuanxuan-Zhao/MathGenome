import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.Monodromy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.HomotopyInvariance
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PolygonalConnectivity
import Batteries.Tactic.OpenPrivate

open Set Filter
open scoped Topology
noncomputable section
open private germ_eq_propagates from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations
namespace D12Complex.Monodromy

private lemma transport_eq {x a : ℂ} (h : x = a)
    (ξ : HolomorphicGerm x) (φ : HolomorphicGerm a) (he : HEq ξ φ) :
    ξ = h.symm ▸ φ := by
  subst x
  exact eq_of_heq he

private lemma transport_heq {x a : ℂ} (h : x = a) (ξ : HolomorphicGerm x) :
    HEq (Eq.mp (congrArg HolomorphicGerm h) ξ) ξ := by
  subst x
  rfl

private lemma rec_heq {x y : ℂ} (h : x = y) (ξ : HolomorphicGerm x) :
    HEq (Eq.ndrec (motive := HolomorphicGerm) ξ h) ξ := by
  cases h
  rfl

section Terminal
variable {Ω : Set ℂ} {a : ℂ} {φ : HolomorphicGerm a}
variable (hex : ∀ (b : ℂ) (γ : Path a b), (∀ t, γ t ∈ Ω) →
  ∃ Φ : GermFamily γ, IsContinuation Ω γ (γ.source.symm ▸ φ) Φ)

private def chosenFamily {b : ℂ} (γ : Path a b) (hγ : ∀ t, γ t ∈ Ω) : GermFamily γ :=
  (hex b γ hγ).choose

private lemma chosenFamily_cont {b : ℂ} (γ : Path a b) (hγ : ∀ t, γ t ∈ Ω) :
    IsContinuation Ω γ (γ.source.symm ▸ φ) (chosenFamily hex γ hγ) :=
  (hex b γ hγ).choose_spec

private def terminal {b : ℂ} (γ : Path a b) (hγ : ∀ t, γ t ∈ Ω) : HolomorphicGerm b :=
  Eq.mp (congrArg HolomorphicGerm γ.target) (chosenFamily hex γ hγ 1)

private lemma terminal_eq {b : ℂ} (γ : Path a b) (hγ : ∀ t, γ t ∈ Ω)
    (Φ : GermFamily γ) (hΦ : IsContinuation Ω γ (γ.source.symm ▸ φ) Φ) :
    Eq.mp (congrArg HolomorphicGerm γ.target) (Φ 1) = terminal hex γ hγ := by
  exact congrArg (fun ξ => Eq.mp (congrArg HolomorphicGerm γ.target) ξ)
    (ContinuationOperations.continuation_unique Ω γ _ Φ _ hΦ
      (chosenFamily_cont hex γ hγ) 1)

/-- The usual simply connected predicate supplies a homotopy with endpoints
fixed, wholly in Ω. Its square has path time first, as in the upstream theorem. -/
private lemma terminal_independent (hΩ : IsDomain Ω) (hsc : IsSimplyConnected Ω)
    {b : ℂ} (γ δ : Path a b) (hγ : ∀ t, γ t ∈ Ω) (hδ : ∀ t, δ t ∈ Ω) :
    terminal hex γ hγ = terminal hex δ hδ := by
  let aa : Ω := ⟨a, by simpa using hγ 0⟩
  let bb : Ω := ⟨b, by simpa using hγ 1⟩
  let p : Path aa bb := {
    toFun := fun t => ⟨γ t, hγ t⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := Subtype.ext γ.source
    target' := Subtype.ext γ.target }
  let q : Path aa bb := {
    toFun := fun t => ⟨δ t, hδ t⟩
    continuous_toFun := δ.continuous.subtype_mk _
    source' := Subtype.ext δ.source
    target' := Subtype.ext δ.target }
  let : SimplyConnectedSpace Ω := hsc
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic p q
  let slice (s : unitInterval) : Path a b := (F.eval s).map continuous_subtype_val
  have hm (s : unitInterval) (t : unitInterval) : slice s t ∈ Ω := (F (s, t)).property
  have hH : Continuous (fun x : unitInterval × unitInterval => (F (x.2, x.1) : ℂ)) :=
    continuous_subtype_val.comp (F.continuous.comp continuous_swap)
  have hi := HomotopyInvariance.homotopy_invariance Ω a b
    (fun x => (F (x.2, x.1) : ℂ)) hΩ hH (fun x => (F (x.2, x.1)).property)
    (fun s => (slice s).source) (fun s => (slice s).target) φ
    (fun s => ⟨chosenFamily hex (slice s) (hm s), chosenFamily_cont hex (slice s) (hm s)⟩)
    0 1 (chosenFamily hex (slice 0) (hm 0)) (chosenFamily hex (slice 1) (hm 1))
    (chosenFamily_cont hex (slice 0) (hm 0)) (chosenFamily_cont hex (slice 1) (hm 1))
  change terminal hex (slice 0) (hm 0) = terminal hex (slice 1) (hm 1) at hi
  have hp : slice 0 = γ := by ext t; simp [slice, p]
  have hq : slice 1 = δ := by ext t; simp [slice, q]
  simpa only [hp, hq] using hi

/-- Appending a short segment stays in one representative of the terminal germ.
Path independence then identifies that representative at every nearby endpoint. -/
private lemma terminal_local (hΩ : IsDomain Ω) (hsc : IsSimplyConnected Ω)
    {b : ℂ} (γ : Path a b) (hγ : ∀ t, γ t ∈ Ω) :
    ∃ (e : FunctionElement) (U : Set ℂ), IsOpen U ∧ b ∈ U ∧
      ∃ hsub : U ⊆ Ω ∩ e.domain,
        ∀ (w : ℂ) (hw : w ∈ U) (δ : Path a w) (hδ : ∀ t, δ t ∈ Ω),
          terminal hex δ hδ = e.germAt w (hsub hw).2 := by
  obtain ⟨e, he, heq⟩ := exists_functionElement b (terminal hex γ hγ)
  have hb : b ∈ Ω := by simpa using hγ 1
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((hΩ.2.1.inter e.holomorphic.1).mem_nhds ⟨hb, he⟩)
  refine ⟨e, Metric.ball b r, Metric.isOpen_ball, Metric.mem_ball_self hr, hsub, ?_⟩
  intro w hw δ hδ
  let σ : Path b w := Path.segment b w
  have hσ (t : unitInterval) : σ t ∈ Metric.ball b r := by
    apply (convex_ball b r).segment_subset (Metric.mem_ball_self hr) hw
    rw [← Path.range_segment]
    exact ⟨t, rfl⟩
  let Ψ : GermFamily σ := fun t => e.germAt (σ t) (hsub (hσ t)).2
  have hΨ : IsContinuation Ω σ (Ψ 0) Ψ := by
    refine ⟨hΩ, σ.continuous, fun t => (hsub (hσ t)).1, rfl, ?_⟩
    intro s
    exact ⟨e.domain, e.toFun, univ, isOpen_univ, mem_univ s,
      e.holomorphic, fun t _ => ⟨(hsub (hσ t)).2, rfl⟩⟩
  let Φ := chosenFamily hex γ hγ
  have hmatch : HEq (Φ 1) (Ψ 0) := by
    exact (transport_heq γ.target (Φ 1)).symm.trans
      ((heq_of_eq heq.symm).trans
        (ChainStability.germAt_heq e σ.source (hsub (hσ 0)).2 he).symm)
  have hbase : γ 1 = σ 0 := γ.target.trans σ.source.symm
  obtain ⟨hC, hinit, hterm⟩ := ContinuationOperations.continuation_concat
    Ω γ σ _ (Ψ 0) Φ Ψ (chosenFamily_cont hex γ hγ) hΨ hbase hmatch
  let p : Path a w := {
    toFun := ContinuationOperations.concatPath γ σ
    continuous_toFun := hC.2.1
    source' := by
      have hzero : ContinuationOperations.leftParam 0 = 0 := by
        apply Subtype.ext
        norm_num [ContinuationOperations.leftParam, Set.projIcc]
      simp [ContinuationOperations.concatPath, hzero]
    target' := by
      have hone : ContinuationOperations.rightParam 1 = 1 := by
        apply Subtype.ext
        norm_num [ContinuationOperations.rightParam, Set.projIcc]
      change (if (1 : ℝ) ≤ 1 / 2 then _ else _) = w
      rw [ite_eq_right (by norm_num), hone]
      exact σ.target }
  have hp : ∀ t, p t ∈ Ω := hC.2.2.1
  have hC' : IsContinuation Ω p (p.source.symm ▸ φ)
      (ContinuationOperations.concatFamily Φ Ψ) := by
    refine ⟨hC.1, hC.2.1, hp, ?_, hC.2.2.2.2⟩
    apply transport_eq p.source
    exact hinit.trans (rec_heq γ.source.symm φ)
  have ht : terminal hex p hp = e.germAt w (hsub hw).2 := by
    rw [← terminal_eq hex p hp _ hC']
    apply eq_of_heq
    exact (transport_heq p.target _).trans
      (hterm.trans (ChainStability.germAt_heq e σ.target (hsub (hσ 1)).2 (hsub hw).2))
  exact (terminal_independent hex hΩ hsc δ p hδ hp).trans ht

private lemma terminal_refl (hΩ : IsDomain Ω) (ha : a ∈ Ω) :
    terminal hex (Path.refl a) (fun _ => ha) = φ := by
  obtain ⟨e, he, heq⟩ := exists_functionElement a φ
  let Ψ : GermFamily (Path.refl a) := fun _ => φ
  have hΨ : IsContinuation Ω (Path.refl a) φ Ψ := by
    refine ⟨hΩ, continuous_const, fun _ => ha, rfl, ?_⟩
    intro s
    exact ⟨e.domain, e.toFun, univ, isOpen_univ, mem_univ s,
      e.holomorphic, fun _ _ => ⟨he, congrArg Subtype.val heq.symm⟩⟩
  exact (terminal_eq hex (Path.refl a) (fun _ => ha) Ψ hΨ).symm

end Terminal

/-- Monodromy with uniqueness on Ω and identification of all terminal germs. -/
theorem monodromy : Specs.D12Complex.Ch19.Monodromy.monodromy_type := by
  classical
  intro Ω a hΩ ha hsc φ hex
  let reach (z : ℂ) (hz : z ∈ Ω) :=
    joinedIn_of_open_isPreconnected Ω hΩ.2.1 hΩ.2.2 a ha z hz
  let p (z : ℂ) (hz : z ∈ Ω) : Path a z := (reach z hz).somePath
  have hp (z : ℂ) (hz : z ∈ Ω) (t : unitInterval) : p z hz t ∈ Ω :=
    (reach z hz).somePath_mem t
  let f (z : ℂ) : ℂ :=
    if hz : z ∈ Ω then (terminal hex (p z hz) (hp z hz)).value else 0
  have hlocal (z : ℂ) (hz : z ∈ Ω) :
      ∃ (e : FunctionElement) (U : Set ℂ), IsOpen U ∧ z ∈ U ∧
        ∃ hsub : U ⊆ Ω ∩ e.domain,
          Set.EqOn f e.toFun U ∧
          ∀ (w : ℂ) (hw : w ∈ U) (δ : Path a w) (hδ : ∀ t, δ t ∈ Ω),
            terminal hex δ hδ = e.germAt w (hsub hw).2 := by
    obtain ⟨e, U, hU, hzU, hsub, ht⟩ := terminal_local hex hΩ hsc (p z hz) (hp z hz)
    refine ⟨e, U, hU, hzU, hsub, ?_, ht⟩
    intro w hw
    dsimp only [f]
    rw [dite_eq_left (hsub hw).1, ht w hw (p w (hsub hw).1) (hp w (hsub hw).1)]
    rfl
  have hf : HolomorphicOn Ω f := by
    refine ⟨hΩ.2.1, fun z hz => ?_⟩
    obtain ⟨e, U, hU, hzU, hsub, heq, _⟩ := hlocal z hz
    exact (e.holomorphic.2 z (hsub hzU).2).congr_of_eventuallyEq
      (heq.eventuallyEq_of_mem (hU.mem_nhds hzU))
  have hgerm (z : ℂ) (hz : z ∈ Ω) :
      HolomorphicGerm.ofFunction f hf hz = terminal hex (p z hz) (hp z hz) := by
    obtain ⟨e, U, hU, hzU, hsub, heq, ht⟩ := hlocal z hz
    exact (germOfFunction_congr z Ω e.domain f e.toFun hf e.holomorphic hz
      (hsub hzU).2 (heq.eventuallyEq_of_mem (hU.mem_nhds hzU))).trans
      (ht z hzU (p z hz) (hp z hz)).symm
  have hfa : HolomorphicGerm.ofFunction f hf ha = φ :=
    (hgerm a ha).trans ((terminal_independent hex hΩ hsc (p a ha) (Path.refl a)
      (hp a ha) (fun _ => ha)).trans (terminal_refl hex hΩ ha))
  refine ⟨f, hf, hfa, ?_, ?_⟩
  · intro b hb γ hγ Φ hΦ
    exact (terminal_eq hex γ hγ Φ hΦ).trans
      ((terminal_independent hex hΩ hsc γ (p b hb) hγ (hp b hb)).trans (hgerm b hb).symm)
  · intro g hg hga z hz
    have hraw : (g : Germ (𝓝 a) ℂ) = (f : Germ (𝓝 a) ℂ) :=
      congrArg Subtype.val (hga.trans hfa.symm)
    have hzraw := germ_eq_propagates hΩ.2.1 hΩ.2.2 hg hf ha hz hraw
    exact congrArg (fun ξ : Germ (𝓝 z) ℂ => ξ.value) hzraw

end D12Complex.Monodromy
