import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.HoffmanReduction
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualFoundation
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators Classical
universe u v
namespace P205.Networks.Hoffman
open FiniteCombinatorics.Directed FiniteCombinatorics.Graph.Flows
open HoffmanSpec
noncomputable section

-- Public constructions are the canonical independent definitions.
def shiftCapacity := @HoffmanSpec.shiftCapacity
def shiftBalance := @HoffmanSpec.shiftBalance
def shiftLoad := @HoffmanSpec.shiftLoad
def unshiftLoad := @HoffmanSpec.unshiftLoad
def auxNetwork := @HoffmanSpec.auxNetwork
def shiftedNetwork := @HoffmanSpec.shiftedNetwork
def demand := @HoffmanSpec.demand
def extend := @HoffmanSpec.extend
def restrict := @HoffmanSpec.restrict

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

theorem divergence_sub (G : Digraph V A) (f g : A → ℝ) (x : V) :
    G.divergence (fun a => f a - g a) x = G.divergence f x - G.divergence g x := by
  simp only [Digraph.divergence_eq]
  have h (t : A → V) :
      (∑ a, if t a = x then f a - g a else 0) =
      (∑ a, if t a = x then f a else 0) - ∑ a, if t a = x then g a else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [h, h]
  ring

theorem shift_feasible : HoffmanSpec.shift_feasible.{u,v} := by
  intro V A _ _ G lo hi f b
  change ((∀ a, lo a ≤ f a ∧ f a ≤ hi a) ∧ ∀ x, G.divergence f x = b x) ↔
    ((∀ a, 0 ≤ f a - lo a ∧ f a - lo a ≤ hi a - lo a) ∧
      ∀ x, G.divergence (fun a => f a - lo a) x = b x - G.divergence lo x)
  simp_rw [divergence_sub]
  constructor
  · rintro ⟨h, hb⟩
    exact ⟨fun a => ⟨by linarith [(h a).1], by linarith [(h a).2]⟩,
      fun x => by rw [hb x]⟩
  · rintro ⟨h, hb⟩
    exact ⟨fun a => ⟨by linarith [(h a).1], by linarith [(h a).2]⟩,
      fun x => by linarith [hb x]⟩

theorem unshift_feasible : HoffmanSpec.unshift_feasible.{u,v} := by
  intro V A _ _ G lo hi g b
  have h := shift_feasible G lo hi (HoffmanSpec.unshiftLoad lo g) b
  have he : HoffmanSpec.shiftLoad lo (HoffmanSpec.unshiftLoad lo g) = g := by
    funext a
    simp [HoffmanSpec.shiftLoad, HoffmanSpec.unshiftLoad]
  rw [he] at h
  exact h.symm

theorem shift_cut : HoffmanSpec.shift_cut.{u,v} := by
  intro V A _ _ G lo hi b S
  have hd := cut_divergence G lo S
  have hs : vertexSum (HoffmanSpec.shiftBalance G lo b) S = vertexSum b S -
      (BoundedSpec.arcSum lo (BoundedSpec.outgoing G S) -
        BoundedSpec.arcSum lo (BoundedSpec.incoming G S)) := by
    unfold vertexSum HoffmanSpec.shiftBalance
    rw [Finset.sum_sub_distrib, hd]
  have hc : BoundedSpec.arcSum (HoffmanSpec.shiftCapacity lo hi) (BoundedSpec.outgoing G S) =
      BoundedSpec.arcSum hi (BoundedSpec.outgoing G S) -
      BoundedSpec.arcSum lo (BoundedSpec.outgoing G S) := by
    unfold BoundedSpec.arcSum HoffmanSpec.shiftCapacity
    rw [Finset.sum_sub_distrib]
  rw [hs, hc]
  constructor <;> intro h <;> linarith

theorem shift_balance_sum : HoffmanSpec.shift_balance_sum.{u,v} := by
  intro V A _ _ G lo b hb
  simp only [HoffmanSpec.shiftBalance, Finset.sum_sub_distrib, sum_divergence G lo, hb,
    sub_zero]

/-- A restricted sum can be written as an indicator sum on the full type. -/
theorem sum_subtype_indicator {X : Type*} [Fintype X] (p : X → Prop) (f : X → ℝ) :
    (∑ x : {x // p x}, f x.val) = ∑ x : X, if p x then f x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) f).symm

/-- The sign decomposition also holds after restricting to any vertex subset. -/
theorem balance_decomposition (β : V → ℝ) (S : Set V) :
    vertexSum β S = (∑ x : Positive β, if x.val ∈ S then β x.val else 0) -
      ∑ x : Negative β, if x.val ∈ S then -β x.val else 0 := by
  rw [sum_subtype_indicator (fun x => 0 < β x) (fun x => if x ∈ S then β x else 0),
    sum_subtype_indicator (fun x => β x < 0) (fun x => if x ∈ S then -β x else 0),
    ← Finset.sum_sub_distrib]
  simp only [vertexSum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hS : x ∈ S <;> by_cases hp : 0 < β x <;> by_cases hn : β x < 0 <;>
    simp [hS, hp, hn] <;> linarith

theorem demand_eq : HoffmanSpec.demand_eq.{u} := by
  intro V _ β hβ
  have h := balance_decomposition β Set.univ
  simp only [vertexSum, Set.mem_univ, Finset.filter_true, HoffmanSpec.demand,
    negativeDemand, ↓reduceIte, hβ] at h ⊢
  linarith

/-- Exactly one term can contribute at a specified original vertex. -/
theorem subtype_single {X : Type*} [Fintype X] (p : X → Prop) (f : X → ℝ) (x : X) :
    (∑ y : {y // p y}, if y.val = x then f y.val else 0) = if p x then f x else 0 := by
  rw [sum_subtype_indicator p (fun y => if y = x then f y else 0)]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem source_divergence (G : Digraph V A) (β : V → ℝ) (F : AuxArc A β → ℝ) :
    (auxGraph G β).divergence F source = ∑ x : Positive β, F (.inr (.inl x)) := by
  simp [Digraph.divergence_eq, Fintype.sum_sum_type, auxGraph, source, sink]

theorem sink_divergence (G : Digraph V A) (β : V → ℝ) (F : AuxArc A β → ℝ) :
    (auxGraph G β).divergence F sink = -(∑ x : Negative β, F (.inr (.inr x))) := by
  simp [Digraph.divergence_eq, Fintype.sum_sum_type, auxGraph, source, sink]

theorem extend_divergence (G : Digraph V A) (β : V → ℝ) (g : A → ℝ) (x : V) :
    (auxGraph G β).divergence (HoffmanSpec.extend β g) (.inl x) =
      G.divergence g x - β x := by
  simp only [Digraph.divergence_eq, Fintype.sum_sum_type, auxGraph,
    HoffmanSpec.extend, source, sink, Sum.inl.injEq, Sum.inr_ne_inl, ↓reduceIte,
    Finset.sum_const_zero, add_zero, zero_add]
  rw [subtype_single (fun y => β y < 0) (fun y => -β y) x,
    subtype_single (fun y => 0 < β y) β x]
  by_cases hp : 0 < β x <;> by_cases hn : β x < 0 <;> simp [hp, hn] <;> linarith

theorem extension : HoffmanSpec.extension.{u,v} := by
  intro V A _ _ G c g β hc hg
  refine ⟨⟨?_, ?_⟩, ?_, rfl⟩
  · intro a
    rcases a with a | (x | x)
    · exact hg.1 a
    · exact ⟨le_of_lt x.property, le_rfl⟩
    · exact ⟨le_of_lt (neg_pos.mpr x.property), le_rfl⟩
  · intro x hs ht
    rcases x with x | b
    · change (auxGraph G β).divergence (HoffmanSpec.extend β g) (.inl x) = 0
      rw [extend_divergence, hg.2 x, sub_self]
    · cases b
      · exact False.elim (hs rfl)
      · exact False.elim (ht rfl)
  · change (auxGraph G β).divergence (HoffmanSpec.extend β g) source = _
    rw [source_divergence]
    rfl

/-- Equality of finite sums under coordinatewise upper bounds forces saturation. -/
theorem saturated_of_sum {X : Type*} [Fintype X] (cap f : X → ℝ)
    (hf : ∀ x, f x ≤ cap x) (hs : (∑ x, f x) = ∑ x, cap x) : ∀ x, f x = cap x := by
  have hz : (∑ x, (cap x - f x)) = 0 := by
    rw [Finset.sum_sub_distrib, hs, sub_self]
  have h := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x (_ : x ∈ Finset.univ) => sub_nonneg.mpr (hf x))).mp hz
  intro x
  exact (sub_eq_zero.mp (h x (Finset.mem_univ x))).symm

theorem saturation : HoffmanSpec.saturation.{u,v} := by
  intro V A _ _ G c β hc F hβ hF hv
  have hp : (∑ x : Positive β, F (.inr (.inl x))) = ∑ x : Positive β, β x.val := by
    change (auxGraph G β).divergence F source = _ at hv
    rwa [source_divergence] at hv
  have hn : (∑ x : Negative β, F (.inr (.inr x))) = ∑ x : Negative β, -β x.val := by
    have h := Network.sink_divergence (HoffmanSpec.auxNetwork G c β hc) F hF
    change (auxGraph G β).divergence F sink = _ at h
    rw [sink_divergence, hv] at h
    have he := demand_eq β hβ
    change HoffmanSpec.demand β = negativeDemand β at he
    change _ = negativeDemand β
    linarith
  exact ⟨saturated_of_sum _ _ (fun x => (hF.1 (.inr (.inl x))).2) hp,
    saturated_of_sum _ _ (fun x => (hF.1 (.inr (.inr x))).2) hn⟩

theorem restriction : HoffmanSpec.restriction.{u,v} := by
  intro V A _ _ G c β hc F hβ hF hv
  obtain ⟨hp, hn⟩ := saturation G c β hc F hβ hF hv
  have he : HoffmanSpec.extend β (HoffmanSpec.restrict β F) = F := by
    funext a
    rcases a with a | (x | x)
    · rfl
    · exact (hp x).symm
    · exact (hn x).symm
  refine ⟨⟨fun a => hF.1 (.inl a), ?_⟩, he⟩
  intro x
  have h := hF.2 (.inl x) (by simp [HoffmanSpec.auxNetwork, source])
    (by simp [HoffmanSpec.auxNetwork, sink])
  change (auxGraph G β).divergence F (.inl x) = 0 at h
  rw [← he, extend_divergence] at h
  exact sub_eq_zero.mp h

theorem feasible_iff : HoffmanSpec.feasible_iff.{u,v} := by
  intro V A _ _ G c β hc hβ
  constructor
  · rintro ⟨g, hg⟩
    have h := extension G c g β hc hg
    exact ⟨HoffmanSpec.extend β g, h.1, h.2.1⟩
  · rintro ⟨F, hF, hv⟩
    exact ⟨HoffmanSpec.restrict β F, (restriction G c β hc F hβ hF hv).1⟩

theorem cut_capacity : HoffmanSpec.cut_capacity.{u,v} := by
  intro V A _ _ G c β hc T hT
  change source ∈ T ∧ sink ∉ T at hT
  let S := originalPart T
  have hcap : (HoffmanSpec.auxNetwork G c β hc).cutCapacity T =
      BoundedSpec.arcSum c (BoundedSpec.outgoing G S) +
      (∑ x : Positive β, if x.val ∉ S then β x.val else 0) +
      ∑ x : Negative β, if x.val ∈ S then -β x.val else 0 := by
    rw [Network.cutCapacity_eq_sum]
    simp [HoffmanSpec.auxNetwork, Fintype.sum_sum_type,
      auxGraph, auxCapacity, hT.1, hT.2, S, originalPart, BoundedSpec.arcSum,
      BoundedSpec.outgoing, Finset.sum_filter, add_assoc]
    rfl
  have hp : (∑ x : Positive β, if x.val ∉ S then β x.val else 0) =
      HoffmanSpec.demand β - ∑ x : Positive β, if x.val ∈ S then β x.val else 0 := by
    unfold HoffmanSpec.demand
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x.val ∈ S <;> simp [h]
  change _ = HoffmanSpec.demand β + BoundedSpec.arcSum c (BoundedSpec.outgoing G S) -
    vertexSum β S
  rw [hcap, hp, balance_decomposition]
  ring

theorem cut_inequalities : HoffmanSpec.cut_inequalities.{u,v} := by
  intro V A _ _ G c β hc
  constructor
  · intro h T hT
    rw [cut_capacity G c β hc T hT]
    linarith [h (originalPart T)]
  · intro h S
    have hcut : (HoffmanSpec.auxNetwork G c β hc).IsCut (liftCut S) := by
      constructor <;> simp [HoffmanSpec.auxNetwork, source, sink, liftCut]
    have hcap := cut_capacity G c β hc (liftCut S) hcut
    have he : originalPart (liftCut S) = S := rfl
    rw [he] at hcap
    have hle := h (liftCut S) hcut
    linarith

/-- Finite sums of integer coordinates remain integer coordinates. -/
theorem integral_sum {X : Type*} [Fintype X] (f : X → ℝ) (hf : Integral f) :
    ∃ z : ℤ, (∑ x, f x) = z := by
  choose z hz using hf
  refine ⟨∑ x, z x, ?_⟩
  simp [hz]

omit [Fintype V] [Fintype A] in
theorem integral_sub {X : Type*} (f g : X → ℝ) (hf : Integral f) (hg : Integral g) :
    Integral (fun x => f x - g x) := by
  intro x
  obtain ⟨a, ha⟩ := hf x
  obtain ⟨b, hb⟩ := hg x
  exact ⟨a - b, by simp [ha, hb]⟩

omit [Fintype V] [Fintype A] in
theorem integral_add {X : Type*} (f g : X → ℝ) (hf : Integral f) (hg : Integral g) :
    Integral (fun x => f x + g x) := by
  intro x
  obtain ⟨a, ha⟩ := hf x
  obtain ⟨b, hb⟩ := hg x
  exact ⟨a + b, by simp [ha, hb]⟩

theorem integral_divergence (G : Digraph V A) (f : A → ℝ) (hf : Integral f) :
    Integral (G.divergence f) := by
  intro x
  have hi (t : A → V) : Integral (fun a => if t a = x then f a else 0) := by
    intro a
    by_cases h : t a = x
    · simpa [h] using hf a
    · exact ⟨0, by simp [h]⟩
  obtain ⟨i, ho⟩ := integral_sum _ (hi G.tail)
  obtain ⟨j, hj⟩ := integral_sum _ (hi G.head)
  exact ⟨i - j, by rw [Digraph.divergence_eq, ho, hj, Int.cast_sub]⟩

theorem integral_shift : HoffmanSpec.integral_shift.{u,v} := by
  intro V A _ _ G lo hi f b hlo hhi hb
  refine ⟨integral_sub hi lo hhi hlo,
    integral_sub b (G.divergence lo) hb (integral_divergence G lo hlo), ?_, ?_⟩
  · constructor
    · intro hf
      exact integral_sub f lo hf hlo
    · intro hg
      have h := integral_add (HoffmanSpec.shiftLoad lo f) lo hg hlo
      simpa [HoffmanSpec.shiftLoad] using h
  · constructor
    · intro hf
      exact integral_add f lo hf hlo
    · intro hg
      have h := integral_sub (HoffmanSpec.unshiftLoad lo f) lo hg hlo
      simpa [HoffmanSpec.unshiftLoad] using h

theorem integral_auxiliary : HoffmanSpec.integral_auxiliary.{u,v} := by
  intro V A _ _ c β hc hβ
  have hp : ∀ x : Positive β, ∃ z : ℤ, β x.val = z := fun x => hβ x.val
  have hn : ∀ x : Negative β, ∃ z : ℤ, -β x.val = z := by
    intro x
    obtain ⟨z, hz⟩ := hβ x.val
    exact ⟨-z, by simp [hz]⟩
  refine ⟨?_, integral_sum _ hp, ?_, ?_⟩
  · intro a
    rcases a with a | (x | x)
    · exact hc a
    · exact hp x
    · exact hn x
  · intro g
    constructor
    · intro hg a
      rcases a with a | (x | x)
      · exact hg a
      · exact hp x
      · exact hn x
    · intro h a
      exact h (.inl a)
  · intro F hF a
    exact hF (.inl a)

theorem original_feasible_iff : HoffmanSpec.original_feasible_iff.{u,v} := by
  intro V A _ _ G lo hi b hbounds hb
  let c := HoffmanSpec.shiftCapacity lo hi
  let β := HoffmanSpec.shiftBalance G lo b
  have hc : ∀ a, 0 ≤ c a := fun a => sub_nonneg.mpr (hbounds a)
  have hβ := shift_balance_sum G lo b hb
  change (∃ f, BoundedSpec.Feasible G lo hi b f) ↔
    ∃ F, (HoffmanSpec.auxNetwork G c β hc).Feasible F ∧
      (HoffmanSpec.auxNetwork G c β hc).value F = HoffmanSpec.demand β
  rw [← feasible_iff G c β hc hβ]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨HoffmanSpec.shiftLoad lo f, (shift_feasible G lo hi f b).mp hf⟩
  · rintro ⟨g, hg⟩
    exact ⟨HoffmanSpec.unshiftLoad lo g, (unshift_feasible G lo hi g b).mp hg⟩

theorem original_cut_iff : HoffmanSpec.original_cut_iff.{u,v} := by
  intro V A _ _ G lo hi b hbounds
  let c := HoffmanSpec.shiftCapacity lo hi
  let β := HoffmanSpec.shiftBalance G lo b
  have hc : ∀ a, 0 ≤ c a := fun a => sub_nonneg.mpr (hbounds a)
  change CutCondition G lo hi b ↔
    ∀ T, (HoffmanSpec.auxNetwork G c β hc).IsCut T →
      HoffmanSpec.demand β ≤ (HoffmanSpec.auxNetwork G c β hc).cutCapacity T
  rw [← cut_inequalities G c β hc]
  exact forall_congr' (fun S => shift_cut G lo hi b S)

theorem original_integral_iff : HoffmanSpec.original_integral_iff.{u,v} := by
  intro V A _ _ G lo hi b hbounds hb hlo hhi hbint
  let c := HoffmanSpec.shiftCapacity lo hi
  let β := HoffmanSpec.shiftBalance G lo b
  have hc : ∀ a, 0 ≤ c a := fun a => sub_nonneg.mpr (hbounds a)
  have hβ := shift_balance_sum G lo b hb
  change (∃ f, BoundedSpec.Feasible G lo hi b f ∧ Integral f) ↔
    ∃ F, (HoffmanSpec.auxNetwork G c β hc).Feasible F ∧
      (HoffmanSpec.auxNetwork G c β hc).value F = HoffmanSpec.demand β ∧ Integral F
  constructor
  · rintro ⟨f, hf, hfint⟩
    have hd := integral_shift G lo hi f b hlo hhi hbint
    have hg := (shift_feasible G lo hi f b).mp hf
    have hF := extension G c (HoffmanSpec.shiftLoad lo f) β hc hg
    refine ⟨HoffmanSpec.extend β (HoffmanSpec.shiftLoad lo f), hF.1, hF.2.1, ?_⟩
    exact ((integral_auxiliary c β hd.1 hd.2.1).2.2.1 _).mp (hd.2.2.1.mp hfint)
  · rintro ⟨F, hF, hv, hFint⟩
    have hg := (restriction G c β hc F hβ hF hv).1
    refine ⟨HoffmanSpec.unshiftLoad lo (HoffmanSpec.restrict β F),
      (unshift_feasible G lo hi _ b).mp hg, ?_⟩
    exact integral_add _ lo (fun a => hFint (.inl a)) hlo

end
end P205.Networks.Hoffman
