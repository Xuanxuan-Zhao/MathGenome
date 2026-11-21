import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.FiniteContinuationChains
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.GermTopology
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations
import Mathlib.Topology.LocallyFinite
import Mathlib.Analysis.Normed.Module.Connected
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
noncomputable section

namespace D12Complex.FiniteContinuationChains

abbrev finiteChain : Specs.D12Complex.Ch19.FiniteContinuationChains.Chain_type := Chain

open private analytic_of_holomorphic from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations

/-- Equality of one germ extends to precisely the relevant overlap component. -/
lemma eqOn_overlap_component (e d : FunctionElement) (a : ℂ)
    (he : a ∈ e.domain) (hd : a ∈ d.domain)
    (h : e.germAt a he = d.germAt a hd) :
    EqOn e.toFun d.toFun (connectedComponentIn (e.domain ∩ d.domain) a) := by
  let C := connectedComponentIn (e.domain ∩ d.domain) a
  have hC : IsOpen C := (e.holomorphic.1.inter d.holomorphic.1).connectedComponentIn
  have hsub := connectedComponentIn_subset (e.domain ∩ d.domain) a
  have hf : HolomorphicOn C e.toFun :=
    ⟨hC, fun z hz => e.holomorphic.2 z (hsub hz).1⟩
  have hg : HolomorphicOn C d.toFun :=
    ⟨hC, fun z hz => d.holomorphic.2 z (hsub hz).2⟩
  exact (analytic_of_holomorphic hf).eqOn_of_preconnected_of_eventuallyEq
    (analytic_of_holomorphic hg) isPreconnected_connectedComponentIn
    (mem_connectedComponentIn ⟨he, hd⟩)
    (Germ.coe_eq.mp (congrArg Subtype.val h))

/-- Every point between the first and last partition points lies in a piece. -/
lemma exists_segment {α : Type*} [LinearOrder α] (n : ℕ)
    (τ : Fin (n + 2) → α) (x : α) (h0 : τ 0 ≤ x)
    (h1 : x ≤ τ (Fin.last (n + 1))) :
    ∃ i : Fin (n + 1), x ∈ Icc (τ i.castSucc) (τ i.succ) := by
  induction n with
  | zero => exact ⟨0, h0, h1⟩
  | succ n ih =>
    by_cases h : x ≤ τ (0 : Fin (n + 2)).succ
    · exact ⟨0, h0, h⟩
    · obtain ⟨i, hi⟩ := ih (fun j => τ j.succ) (le_of_not_ge h) h1
      exact ⟨i.succ, hi⟩

/-- A strictly increasing (uniform) partition subordinate to an arbitrary open cover. -/
lemma strict_partition {ι : Type*} (V : ι → Set unitInterval)
    (ho : ∀ i, IsOpen (V i)) (hcov : univ ⊆ ⋃ i, V i) :
    ∃ (n : ℕ) (τ : Fin (n + 2) → unitInterval), StrictMono τ ∧ τ 0 = 0 ∧
      τ (Fin.last (n + 1)) = 1 ∧
      ∀ i : Fin (n + 1), ∃ a, Icc (τ i.castSucc) (τ i.succ) ⊆ V a := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ ho hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hd : (0 : ℝ) < n + 1 := by positivity
  let τ : Fin (n + 2) → unitInterval := fun i =>
    ⟨(i.val : ℝ) / (n + 1), div_nonneg (Nat.cast_nonneg _) hd.le,
      (div_le_one hd).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩
  refine ⟨n, τ, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    change (i.val : ℝ) / (n + 1) < (j.val : ℝ) / (n + 1)
    exact (div_lt_div_iff_of_pos_right hd).mpr (by exact_mod_cast hij)
  · apply Subtype.ext; simp [τ]
  · apply Subtype.ext; simp [τ, ne_of_gt hd]
  · intro i
    obtain ⟨a, ha⟩ := hball (τ i.castSucc) trivial
    refine ⟨a, fun t ht => ha ?_⟩
    have hl : (i.val : ℝ) / (n + 1) ≤ (t : ℝ) := ht.1
    have hu : (t : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) / (n + 1) := ht.2
    have hdist : dist t (τ i.castSucc) = (t : ℝ) - (i.val : ℝ) / (n + 1) := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact abs_of_nonneg (sub_nonneg.mpr hl)
    apply Metric.mem_ball.mpr
    rw [hdist]
    calc
      (t : ℝ) - (i.val : ℝ) / (n + 1) ≤
          ((i.val + 1 : ℕ) : ℝ) / (n + 1) - (i.val : ℝ) / (n + 1) := sub_le_sub_right hu _
      _ = 1 / (n + 1) := by push_cast; ring
      _ < δ := hn

/-- Local representatives may be chosen on disks inside the base domain. -/
lemma locallyRepresented_elements {Ω γ Φ} (hΩ : IsOpen Ω) (hc : Continuous γ)
    (hγ : ∀ t, γ t ∈ Ω) (hloc : LocallyRepresented γ Φ) (s : unitInterval) :
    ∃ (e : FunctionElement) (J : Set unitInterval), e.domain ⊆ Ω ∧
      IsOpen J ∧ s ∈ J ∧ RepresentsOn γ Φ e.domain e.toFun J := by
  obtain ⟨U, f, I, ho, hs, hf, hrep⟩ := hloc s
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((hf.1.inter hΩ).mem_nhds ⟨(hrep s hs).1, hγ s⟩)
  let e : FunctionElement :=
    { domain := Metric.ball (γ s) r
      isDomain := ⟨⟨γ s, Metric.mem_ball_self hr⟩, Metric.isOpen_ball,
        Metric.isPreconnected_ball⟩
      toFun := f
      holomorphic := ⟨Metric.isOpen_ball, fun z hz => hf.2 z (hsub hz).1⟩ }
  refine ⟨e, I ∩ γ ⁻¹' e.domain, fun z hz => (hsub hz).2,
    ho.inter (Metric.isOpen_ball.preimage hc), ⟨hs, Metric.mem_ball_self hr⟩,
    e.holomorphic, ?_⟩
  intro t ht
  exact ⟨ht.2, (hrep t ht.1).2⟩

lemma Chain.covers {Ω γ φ ψ} (c : Chain Ω γ φ ψ) (t : unitInterval) :
    ∃ i : Fin (c.n + 1), t ∈ Icc (c.time i.castSucc) (c.time i.succ) :=
  exists_segment c.n c.time t (c.time_zero.symm ▸ bot_le) (c.time_last.symm ▸ le_top)

/-- Consecutive elements give the same germ at their joint. -/
lemma Chain.joint_germ {Ω γ φ ψ} (c : Chain Ω γ φ ψ) (i : Fin c.n)
    (he : γ (c.time i.succ.castSucc) ∈ (c.element i.castSucc).domain)
    (hd : γ (c.time i.succ.castSucc) ∈ (c.element i.succ).domain) :
    (c.element i.castSucc).germAt _ he = (c.element i.succ).germAt _ hd := by
  apply germOfFunction_congr
  have hC : IsOpen (connectedComponentIn
      ((c.element i.castSucc).domain ∩ (c.element i.succ).domain)
      (γ (c.time i.succ.castSucc))) :=
    ((c.element i.castSucc).holomorphic.1.inter
      (c.element i.succ).holomorphic.1).connectedComponentIn
  exact (c.compatible i).eventuallyEq_of_mem
    (hC.mem_nhds (mem_connectedComponentIn ⟨he, hd⟩))

/-- Two closed pieces overlap only at a joint, unless they are the same piece. -/
lemma Chain.piece_germ {Ω γ φ ψ} (c : Chain Ω γ φ ψ)
    (i j : Fin (c.n + 1)) (t : unitInterval)
    (hi : t ∈ Icc (c.time i.castSucc) (c.time i.succ))
    (hj : t ∈ Icc (c.time j.castSucc) (c.time j.succ)) :
    (c.element i).germAt (γ t) (c.contains i t hi) =
      (c.element j).germAt (γ t) (c.contains j t hj) := by
  wlog hij : i ≤ j generalizing i j
  · exact (this j i hj hi (le_of_not_ge hij)).symm
  by_cases heq : i = j
  · subst j; rfl
  have hlt : i < j := lt_of_le_of_ne hij heq
  have hij' : i.succ ≤ j.castSucc := by simpa using hlt
  have ht : t = c.time j.castSucc :=
    le_antisymm (hi.2.trans (c.strict.monotone hij')) hj.1
  have hindex : i.succ = j.castSucc :=
    c.strict.injective (le_antisymm (c.strict.monotone hij') (hj.1.trans hi.2))
  have hval : i.val + 1 = j.val := congrArg Fin.val hindex
  let k : Fin c.n := ⟨i.val, by omega⟩
  have hi' : i = k.castSucc := Fin.ext rfl
  have hj' : j = k.succ := Fin.ext hval.symm
  have ht' : t = c.time k.succ.castSucc := by simpa only [hj'] using ht
  have hleft : γ t ∈ (c.element k.castSucc).domain := by
    simpa only [hi'] using c.contains i t hi
  have hright : γ t ∈ (c.element k.succ).domain := by
    simpa only [hj'] using c.contains j t hj
  apply Subtype.ext
  change ((c.element i).toFun : Germ (𝓝 (γ t)) ℂ) =
    ((c.element j).toFun : Germ (𝓝 (γ t)) ℂ)
  rw [hi', hj', ht']
  exact congrArg Subtype.val
    (c.joint_germ k (by simpa only [ht'] using hleft)
      (by simpa only [ht'] using hright))

theorem continuation_to_chain :
    Specs.D12Complex.Ch19.FiniteContinuationChains.continuation_to_chain_type := by
  intro Ω γ φ ψ Φ hΦ hterm
  choose e J hsub ho hs hrep using
    locallyRepresented_elements hΦ.1.2.1 hΦ.2.1 hΦ.2.2.1 hΦ.2.2.2.2
  have hcov : univ ⊆ ⋃ s, J s := by
    intro t _; exact mem_iUnion.mpr ⟨t, hs t⟩
  obtain ⟨n, τ, hτ, h0, h1, hcover⟩ := strict_partition J ho hcov
  choose a ha using hcover
  let E := fun i : Fin (n + 1) => e (a i)
  have hR : ∀ i, RepresentsOn γ Φ (E i).domain (E i).toFun
      (Icc (τ i.castSucc) (τ i.succ)) := by
    intro i
    exact ⟨(hrep (a i)).1, fun t ht => (hrep (a i)).2 t (ha i ht)⟩
  have hc : ∀ i t, t ∈ Icc (τ i.castSucc) (τ i.succ) → γ t ∈ (E i).domain :=
    fun i t ht => ((hR i).2 t ht).1
  have hm0 : (0 : unitInterval) ∈ Icc (τ (0 : Fin (n + 1)).castSucc)
      (τ (0 : Fin (n + 1)).succ) := ⟨h0.le, bot_le⟩
  have hm1 : (1 : unitInterval) ∈ Icc (τ (Fin.last n).castSucc)
      (τ (Fin.last n).succ) := ⟨le_top, h1.ge⟩
  refine ⟨{
    n := n
    time := τ
    strict := hτ
    time_zero := h0
    time_last := h1
    element := E
    domain_subset := fun i => hsub (a i)
    contains := hc
    compatible := ?_
    initial_mem := hc 0 0 hm0
    terminal_mem := hc (Fin.last n) 1 hm1
    initial_germ := ?_
    terminal_germ := ?_ }⟩
  · intro i
    have hl : τ i.succ.castSucc ∈ Icc (τ i.castSucc.castSucc) (τ i.castSucc.succ) :=
      ⟨hτ.monotone (by change i.val ≤ i.val + 1; omega), le_rfl⟩
    have hr : τ i.succ.castSucc ∈ Icc (τ i.succ.castSucc) (τ i.succ.succ) :=
      ⟨le_rfl, hτ.monotone (by change i.val + 1 ≤ i.val + 1 + 1; omega)⟩
    apply eqOn_overlap_component _ _ _ (hc i.castSucc _ hl) (hc i.succ _ hr)
    apply Subtype.ext
    exact ((hR i.castSucc).2 _ hl).2.symm.trans ((hR i.succ).2 _ hr).2
  · apply Subtype.ext
    exact (congrArg Subtype.val hΦ.2.2.2.1).symm.trans ((hR 0).2 0 hm0).2
  · apply Subtype.ext
    exact (congrArg Subtype.val hterm).symm.trans ((hR (Fin.last n)).2 1 hm1).2

/-- Glue the sections on the finite closed cover, then use the germ-topology bridge. -/
theorem chain_reconstruction :
    Specs.D12Complex.Ch19.FiniteContinuationChains.chain_reconstruction_type := by
  intro Ω γ φ ψ hΩ hc c
  let S := fun i : Fin (c.n + 1) => Icc (c.time i.castSucc) (c.time i.succ)
  let idx := fun t => (c.covers t).choose
  have hidx : ∀ t, t ∈ S (idx t) := fun t => (c.covers t).choose_spec
  let Φ : GermFamily γ := fun t =>
    (c.element (idx t)).germAt (γ t) (c.contains (idx t) t (hidx t))
  have hrep : ∀ i t (ht : t ∈ S i),
      Φ t = (c.element i).germAt (γ t) (c.contains i t ht) := by
    intro i t ht
    exact c.piece_germ (idx t) i t (hidx t) ht
  have hγ : ∀ t, γ t ∈ Ω := fun t =>
    c.domain_subset (idx t) (c.contains (idx t) t (hidx t))
  have hlift : Continuous (GermTopology.lift γ hγ Φ) := by
    apply (locallyFinite_of_finite S).continuous
    · ext t
      simp only [mem_iUnion, mem_univ, iff_true]
      exact c.covers t
    · intro i; exact isClosed_Icc
    · intro i
      apply continuousOn_iff_continuous_domRestrict.mpr
      let toDomain : S i → (c.element i).domain :=
        fun t => ⟨γ t, c.contains i t t.property⟩
      have hto : Continuous toDomain :=
        (hc.comp continuous_subtype_val).subtype_mk _
      have hs := (GermTopology.continuous_sectionMap Ω (c.element i)
        (c.domain_subset i)).comp hto
      apply hs.congr
      intro t
      change (⟨⟨γ t, _⟩, (c.element i).germAt (γ t) _⟩ : GermTopology.Space Ω) =
        ⟨⟨γ t, _⟩, Φ t⟩
      rw [hrep i t t.property]
  have h0 : (0 : unitInterval) ∈ S 0 := by
    exact ⟨c.time_zero.le, bot_le⟩
  have h1 : (1 : unitInterval) ∈ S (Fin.last c.n) := by
    exact ⟨le_top, c.time_last.ge⟩
  refine ⟨Φ, ⟨hΩ, hc, hγ, (hrep 0 0 h0).trans c.initial_germ.symm,
    (GermTopology.locallyRepresented_iff_continuous_lift Ω hΩ.2.1 γ hc hγ Φ).mpr hlift⟩,
    (hrep (Fin.last c.n) 1 h1).trans c.terminal_germ.symm, ?_⟩
  intro i
  refine ⟨(c.element i).holomorphic, fun t ht => ⟨c.contains i t ht, ?_⟩⟩
  exact congrArg Subtype.val (hrep i t ht)

theorem continuation_iff_chain :
    Specs.D12Complex.Ch19.FiniteContinuationChains.continuation_iff_chain_type := by
  intro Ω γ φ ψ hΩ hc
  constructor
  · rintro ⟨Φ, hΦ, hψ⟩
    exact continuation_to_chain Ω γ φ ψ Φ hΦ hψ
  · rintro ⟨c⟩
    obtain ⟨Φ, hΦ, hψ, _⟩ := chain_reconstruction Ω γ φ ψ hΩ hc c
    exact ⟨Φ, hΦ, hψ⟩

theorem chain_iff_continuous_lift :
    Specs.D12Complex.Ch19.FiniteContinuationChains.chain_iff_continuous_lift_type := by
  intro Ω γ hγ φ ψ hΩ hc
  rw [← continuation_iff_chain Ω γ φ ψ hΩ hc]
  constructor
  · rintro ⟨Φ, hΦ, hψ⟩
    exact ⟨Φ, hΦ.2.2.2.1, hψ,
      (GermTopology.locallyRepresented_iff_continuous_lift Ω hΩ.2.1 γ hc hγ Φ).mp
        hΦ.2.2.2.2⟩
  · rintro ⟨Φ, hφ, hψ, hcont⟩
    exact ⟨Φ, ⟨hΩ, hc, hγ, hφ,
      (GermTopology.locallyRepresented_iff_continuous_lift Ω hΩ.2.1 γ hc hγ Φ).mpr hcont⟩,
      hψ⟩

end D12Complex.FiniteContinuationChains
