import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation
import Mathlib.Analysis.Normed.Module.Connected

/-! Neighborhood-equivalence and representative-independence bridges for d12:19-01.
Only elementary quotient, metric and connectedness facts are used here.
The canonical objects are in the independent Spec for use by downstream Specs. -/

open scoped Topology

noncomputable section

namespace D12Complex.GermsContinuation

abbrev FunctionElement : Specs.D12Complex.Ch19.GermsContinuation.FunctionElement_type :=
  _root_.D12Complex.FunctionElement

abbrev SameGermAt : Specs.D12Complex.Ch19.GermsContinuation.SameGermAt_type :=
  _root_.D12Complex.SameGermAt

abbrev IsHolomorphicGerm : Specs.D12Complex.Ch19.GermsContinuation.IsHolomorphicGerm_type :=
  _root_.D12Complex.IsHolomorphicGerm

abbrev HolomorphicGerm : Specs.D12Complex.Ch19.GermsContinuation.HolomorphicGerm_type :=
  _root_.D12Complex.HolomorphicGerm

abbrev germOfFunction : Specs.D12Complex.Ch19.GermsContinuation.germOfFunction_type :=
  @_root_.D12Complex.HolomorphicGerm.ofFunction

abbrev germValue : Specs.D12Complex.Ch19.GermsContinuation.germValue_type :=
  @_root_.D12Complex.HolomorphicGerm.value

abbrev elementGerm : Specs.D12Complex.Ch19.GermsContinuation.elementGerm_type :=
  _root_.D12Complex.FunctionElement.germAt

abbrev GermFamily : Specs.D12Complex.Ch19.GermsContinuation.GermFamily_type :=
  _root_.D12Complex.GermFamily

abbrev RepresentsOn : Specs.D12Complex.Ch19.GermsContinuation.RepresentsOn_type :=
  _root_.D12Complex.RepresentsOn

abbrev LocallyRepresented : Specs.D12Complex.Ch19.GermsContinuation.LocallyRepresented_type :=
  _root_.D12Complex.LocallyRepresented

abbrev IsContinuation : Specs.D12Complex.Ch19.GermsContinuation.IsContinuation_type :=
  _root_.D12Complex.IsContinuation

abbrev Continuation : Specs.D12Complex.Ch19.GermsContinuation.Continuation_type :=
  _root_.D12Complex.Continuation

end D12Complex.GermsContinuation

namespace D12Complex

private theorem eventuallyEq_iff_openNeighborhood {a : ℂ} {U V : Set ℂ}
    {f g : ℂ → ℂ} (hU : IsOpen U) (hV : IsOpen V) (ha : a ∈ U) (hb : a ∈ V) :
    f =ᶠ[𝓝 a] g ↔
      ∃ W : Set ℂ, IsOpen W ∧ a ∈ W ∧ W ⊆ U ∩ V ∧ Set.EqOn f g W := by
  constructor
  · intro h
    have hn : {z | f z = g z} ∩ (U ∩ V) ∈ 𝓝 a :=
      Filter.inter_mem h (Filter.inter_mem (hU.mem_nhds ha) (hV.mem_nhds hb))
    obtain ⟨W, hW, ho, haw⟩ := mem_nhds_iff.mp hn
    exact ⟨W, ho, haw, fun z hz => (hW hz).2, fun z hz => (hW hz).1⟩
  · rintro ⟨W, ho, haw, _, heq⟩
    exact Filter.eventually_of_mem (ho.mem_nhds haw) heq

theorem sameGermAt_iff_eventuallyEq :
    Specs.D12Complex.Ch19.GermsContinuation.sameGermAt_iff_eventuallyEq_type := by
  intro a e d he hd
  exact (eventuallyEq_iff_openNeighborhood e.holomorphic.1 d.holomorphic.1 he hd).symm

theorem sameGermAt_refl :
    Specs.D12Complex.Ch19.GermsContinuation.sameGermAt_refl_type := by
  intro a e ha
  exact (sameGermAt_iff_eventuallyEq a e e ha ha).mpr Filter.EventuallyEq.rfl

theorem sameGermAt_symm :
    Specs.D12Complex.Ch19.GermsContinuation.sameGermAt_symm_type := by
  intro a e d h
  obtain ⟨W, ho, ha, hsub, heq⟩ := h
  exact ⟨W, ho, ha, fun z hz => ⟨(hsub hz).2, (hsub hz).1⟩,
    fun z hz => (heq hz).symm⟩

theorem sameGermAt_trans :
    Specs.D12Complex.Ch19.GermsContinuation.sameGermAt_trans_type := by
  intro a e d k h₁ h₂
  obtain ⟨W, ho, ha, hsub, heq⟩ := h₁
  obtain ⟨V, hvo, hav, hvsub, hveq⟩ := h₂
  refine ⟨W ∩ V, ho.inter hvo, ⟨ha, hav⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨(hsub hz.1).1, (hvsub hz.2).2⟩
  · intro z hz
    exact (heq hz.1).trans (hveq hz.2)

theorem germOfFunction_eq_iff :
    Specs.D12Complex.Ch19.GermsContinuation.germOfFunction_eq_iff_type := by
  intro a U V f g hf hg ha hb
  constructor
  · intro h
    exact (eventuallyEq_iff_openNeighborhood hf.1 hg.1 ha hb).mp
      (Filter.Germ.coe_eq.mp (congrArg Subtype.val h))
  · intro h
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr
      ((eventuallyEq_iff_openNeighborhood hf.1 hg.1 ha hb).mpr h)

theorem elementGerm_eq_iff :
    Specs.D12Complex.Ch19.GermsContinuation.elementGerm_eq_iff_type := by
  intro a e d he hd
  exact germOfFunction_eq_iff a e.domain d.domain e.toFun d.toFun
    e.holomorphic d.holomorphic he hd

theorem germOfFunction_congr :
    Specs.D12Complex.Ch19.GermsContinuation.germOfFunction_congr_type := by
  intro a U V f g hf hg ha hb heq
  apply Subtype.ext
  exact Filter.Germ.coe_eq.mpr heq

theorem germValue_ofFunction :
    Specs.D12Complex.Ch19.GermsContinuation.germValue_ofFunction_type := by
  intro a U f hf ha
  rfl

theorem exists_functionElement :
    Specs.D12Complex.Ch19.GermsContinuation.exists_functionElement_type := by
  intro a g
  obtain ⟨U, f, ha, hf, heq⟩ := g.property
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hf.1.mem_nhds ha)
  let e : FunctionElement :=
    { domain := Metric.ball a r
      isDomain := ⟨⟨a, Metric.mem_ball_self hr⟩, Metric.isOpen_ball, Metric.isPreconnected_ball⟩
      toFun := f
      holomorphic := ⟨Metric.isOpen_ball, fun z hz => hf.2 z (hsub hz)⟩ }
  refine ⟨e, Metric.mem_ball_self hr, ?_⟩
  apply Subtype.ext
  exact heq

theorem holomorphicGerm_ext :
    Specs.D12Complex.Ch19.GermsContinuation.holomorphicGerm_ext_type := by
  intro a g h heq
  exact Subtype.ext heq

theorem representsOn_iff :
    Specs.D12Complex.Ch19.GermsContinuation.representsOn_iff_type := by
  intro γ Φ U f I
  constructor
  · rintro ⟨hf, hrep⟩
    refine ⟨hf, fun t ht => ?_⟩
    obtain ⟨ha, heq⟩ := hrep t ht
    exact ⟨ha, Subtype.ext heq⟩
  · rintro ⟨hf, hrep⟩
    refine ⟨hf, fun t ht => ?_⟩
    obtain ⟨ha, heq⟩ := hrep t ht
    exact ⟨ha, congrArg Subtype.val heq⟩

theorem representsOn_congr :
    Specs.D12Complex.Ch19.GermsContinuation.representsOn_congr_type := by
  intro γ Φ U V f g I hrep hg hV heq
  refine ⟨hg, fun t ht => ⟨hV t ht, ?_⟩⟩
  exact ((hrep.2 t ht).2).trans (Filter.Germ.coe_eq.mpr (heq t ht))

theorem locallyRepresented_iff :
    Specs.D12Complex.Ch19.GermsContinuation.locallyRepresented_iff_type := by
  intro γ Φ
  constructor
  · intro h s
    obtain ⟨U, f, I, ho, hs, hrep⟩ := h s
    obtain ⟨hf, heq⟩ := (representsOn_iff γ Φ U f I).mp hrep
    exact ⟨U, f, hf, Filter.eventually_of_mem (ho.mem_nhds hs) heq⟩
  · intro h s
    obtain ⟨U, f, hf, heq⟩ := h s
    obtain ⟨I, hI, ho, hs⟩ := mem_nhds_iff.mp heq
    exact ⟨U, f, I, ho, hs, (representsOn_iff γ Φ U f I).mpr ⟨hf, hI⟩⟩

theorem isContinuation_iff :
    Specs.D12Complex.Ch19.GermsContinuation.isContinuation_iff_type := by
  intro Ω γ φ Φ
  unfold IsContinuation
  refine and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h s
    obtain ⟨U, f, I, ho, hs, hrep⟩ := h s
    obtain ⟨hf, heq⟩ := (representsOn_iff γ Φ U f I).mp hrep
    exact ⟨U, f, hf, I, ho, hs, heq⟩
  · intro h s
    obtain ⟨U, f, hf, I, ho, hs, heq⟩ := h s
    exact ⟨U, f, I, ho, hs, (representsOn_iff γ Φ U f I).mpr ⟨hf, heq⟩⟩

theorem isContinuation_congr :
    Specs.D12Complex.Ch19.GermsContinuation.isContinuation_congr_type := by
  intro Ω γ φ ψ Φ Ψ hφ hΦ
  have h : Φ = Ψ := funext hΦ
  subst ψ
  subst Ψ
  rfl

end D12Complex
