import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.ChainStability
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.FiniteContinuationChains
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Finset.Lattice.Fold

open Set Filter
open scoped Topology
noncomputable section
namespace D12Complex.ChainStability
open FiniteContinuationChains

/-- Compact subsets of an open set have a uniform positive metric margin. -/
lemma compact_margin {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ y : ℂ, ‖y - x‖ < r → y ∈ U := by
  obtain ⟨r, hr, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨r, hr, fun x hx y hy => hsub ?_⟩
  exact Metric.mem_thickening_iff.mpr ⟨x, hx, by simpa only [dist_eq_norm] using hy⟩

/-- One bound for both the closed pieces and the finitely many overlap components.
The joint family can be empty, so the index type includes the nonempty piece family. -/
lemma chain_margin {Ω γ φ ψ} (c : Chain Ω γ φ ψ) (hc : Continuous γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : unitInterval → ℂ,
      (∀ t, ‖η t - γ t‖ < δ) →
      (∀ i t, t ∈ Icc (c.time i.castSucc) (c.time i.succ) →
        η t ∈ (c.element i).domain) ∧
      (∀ i : Fin c.n, η (c.time i.succ.castSucc) ∈
        connectedComponentIn ((c.element i.castSucc).domain ∩ (c.element i.succ).domain)
          (γ (c.time i.succ.castSucc))) := by
  have hp : ∀ i : Fin (c.n + 1), ∃ r : ℝ, 0 < r ∧
      ∀ t ∈ Icc (c.time i.castSucc) (c.time i.succ),
        ∀ y : ℂ, ‖y - γ t‖ < r → y ∈ (c.element i).domain := by
    intro i
    obtain ⟨r, hr, hsub⟩ := compact_margin (isCompact_Icc.image hc)
      (c.element i).holomorphic.1 (by rintro _ ⟨t, ht, rfl⟩; exact c.contains i t ht)
    exact ⟨r, hr, fun t ht y hy => hsub (γ t) ⟨t, ht, rfl⟩ y hy⟩
  have hj : ∀ i : Fin c.n, ∃ r : ℝ, 0 < r ∧ ∀ y : ℂ,
      ‖y - γ (c.time i.succ.castSucc)‖ < r → y ∈
        connectedComponentIn ((c.element i.castSucc).domain ∩ (c.element i.succ).domain)
          (γ (c.time i.succ.castSucc)) := by
    intro i
    have hl : c.time i.succ.castSucc ∈
        Icc (c.time i.castSucc.castSucc) (c.time i.castSucc.succ) :=
      ⟨c.strict.monotone (by change i.val ≤ i.val + 1; omega), le_rfl⟩
    have hr : c.time i.succ.castSucc ∈
        Icc (c.time i.succ.castSucc) (c.time i.succ.succ) :=
      ⟨le_rfl, c.strict.monotone (by change i.val + 1 ≤ i.val + 1 + 1; omega)⟩
    have hopen : IsOpen (connectedComponentIn
        ((c.element i.castSucc).domain ∩ (c.element i.succ).domain)
        (γ (c.time i.succ.castSucc))) :=
      ((c.element i.castSucc).holomorphic.1.inter
      (c.element i.succ).holomorphic.1).connectedComponentIn
    obtain ⟨r, hpos, hsub⟩ := Metric.isOpen_iff.mp hopen _
      (mem_connectedComponentIn ⟨c.contains i.castSucc _ hl, c.contains i.succ _ hr⟩)
    exact ⟨r, hpos, fun y hy => hsub (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)⟩
  choose rp hrp hpiece using hp
  choose rj hrj hjoint using hj
  let r : Fin (c.n + 1) ⊕ Fin c.n → ℝ := Sum.elim rp rj
  have hpos : ∀ i, 0 < r i := by
    intro i; cases i with
    | inl i => exact hrp i
    | inr i => exact hrj i
  let δ := Finset.univ.inf' Finset.univ_nonempty r
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr (fun i _ => hpos i)
  have hle : ∀ i, δ ≤ r i := fun i => Finset.inf'_le r (Finset.mem_univ i)
  refine ⟨δ, hδ, fun η hη => ⟨?_, ?_⟩⟩
  · intro i t ht
    exact hpiece i t ht (η t) ((hη t).trans_le (hle (Sum.inl i)))
  · intro i
    exact hjoint i _ ((hη _).trans_le (hle (Sum.inr i)))

lemma germAt_transport (e : FunctionElement) {a b : ℂ} (h : a = b)
    (ha : a ∈ e.domain) (hb : b ∈ e.domain) :
    (h ▸ e.germAt a ha) = e.germAt b hb := by
  subst b
  rfl

lemma germAt_heq (e : FunctionElement) {a b : ℂ} (h : a = b)
    (ha : a ∈ e.domain) (hb : b ∈ e.domain) :
    HEq (e.germAt a ha) (e.germAt b hb) := by
  subst b
  rfl

/-- The same chain is reconstructed after perturbation. Its overlap components
are unchanged because each new joint lies in the old component. -/
theorem chain_stability :
    Specs.D12Complex.Ch19.ChainStability.chain_stability_type := by
  intro Ω γ φ ψ c hΩ hc
  obtain ⟨δ, hδ, hcontrol⟩ := chain_margin c hc
  refine ⟨δ, hδ, ?_⟩
  intro η hcη _hηΩ h0 hclose
  have hb : BddAbove (range (fun t => ‖η t - γ t‖)) :=
    (isCompact_range ((hcη.sub hc).norm)).bddAbove
  have hpoint : ∀ t, ‖η t - γ t‖ < δ :=
    fun t => (le_ciSup hb t).trans_lt hclose
  obtain ⟨hcontains, hjoint⟩ := hcontrol η hpoint
  have hm0 : η 0 ∈ (c.element 0).domain :=
    hcontains 0 0 ⟨c.time_zero.le, bot_le⟩
  have hm1 : η 1 ∈ (c.element (Fin.last c.n)).domain :=
    hcontains (Fin.last c.n) 1 ⟨le_top, c.time_last.ge⟩
  let cη : Chain Ω η (h0.symm ▸ φ)
      ((c.element (Fin.last c.n)).germAt (η 1) hm1) := {
    n := c.n
    time := c.time
    strict := c.strict
    time_zero := c.time_zero
    time_last := c.time_last
    element := c.element
    domain_subset := c.domain_subset
    contains := hcontains
    compatible := fun i => by
      rw [← connectedComponentIn_eq (hjoint i)]
      exact c.compatible i
    initial_mem := hm0
    terminal_mem := hm1
    initial_germ := (congrArg (fun g : HolomorphicGerm (γ 0) => h0.symm ▸ g)
      c.initial_germ).trans (germAt_transport _ h0.symm c.initial_mem hm0)
    terminal_germ := rfl }
  obtain ⟨Ψ, hΨ, hterm, hrep⟩ := chain_reconstruction Ω η _ _ hΩ hcη cη
  refine ⟨Ψ, hΨ, hrep, ⟨hm1, hterm⟩, ?_⟩
  intro h1
  exact (heq_of_eq hterm).trans
    ((germAt_heq _ h1 hm1 c.terminal_mem).trans (heq_of_eq c.terminal_germ.symm))

/-- Extract a finite chain once, then keep all its representatives for every
path within the chosen uniform bound. -/
theorem continuation_chain_stability :
    Specs.D12Complex.Ch19.ChainStability.continuation_chain_stability_type := by
  intro Ω γ φ Φ hΦ
  obtain ⟨c⟩ := continuation_to_chain Ω γ φ (Φ 1) Φ hΦ rfl
  exact ⟨c, chain_stability Ω γ φ (Φ 1) c hΦ.1 hΦ.2.1⟩

theorem continuation_stability_fixed_endpoints :
    Specs.D12Complex.Ch19.ChainStability.continuation_stability_fixed_endpoints_type := by
  intro Ω γ φ Φ hΦ
  obtain ⟨c, δ, hδ, hstable⟩ := continuation_chain_stability Ω γ φ Φ hΦ
  refine ⟨δ, hδ, ?_⟩
  intro η hcη hηΩ h0 h1 hclose
  obtain ⟨Ψ, hΨ, _, _, hterm⟩ := hstable η hcη hηΩ h0 hclose
  exact ⟨Ψ, hΨ, hterm h1⟩

end D12Complex.ChainStability
