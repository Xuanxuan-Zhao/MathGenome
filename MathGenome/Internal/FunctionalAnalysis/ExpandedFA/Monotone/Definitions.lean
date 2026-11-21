import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Monotone.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.OperatorDomains

/-! Canonical real monotone graphs and the Minty–Browder hypotheses.
Maximality is among all graphs, not only linear operators. Linear operators
retain their actual subspace domains. Hilbert graphs are transported by Riesz.
No regularity or nonzero-space hypothesis is built into monotonicity. -/
namespace ExpandedFA.Monotone
universe u

def graphOfMap : Spec.MapGraphType.{u} := Spec.MapGraphValue

def Monotone : Spec.MonotoneType.{u} := Spec.MonotoneValue

def MaximalMonotone : Spec.MaximalMonotoneType.{u} := Spec.MaximalMonotoneValue

def MonotoneOn : Spec.MonotoneOnType.{u} := Spec.MonotoneOnValue

def MonotoneMap : Spec.MonotoneMapType.{u} := Spec.MonotoneMapValue

def StrictMonotoneMap : Spec.StrictMonotoneMapType.{u} := Spec.StrictMonotoneMapValue

def BoundedOnBoundedSets : Spec.BoundedOnBoundedSetsType.{u} := Spec.BoundedOnBoundedSetsValue

def Hemicontinuous : Spec.HemicontinuousType.{u} := Spec.HemicontinuousValue

def Coercive : Spec.CoerciveType.{u} := Spec.CoerciveValue

def linearGraph : Spec.LinearGraphType.{u} := Spec.LinearGraphValue

def LinearMonotone : Spec.LinearMonotoneType.{u} := Spec.LinearMonotoneValue

def LinearMaximalMonotone : Spec.LinearMaximalMonotoneType.{u} := Spec.LinearMaximalMonotoneValue

def hilbertGraph : Spec.HilbertGraphType.{u} := Spec.HilbertGraphValue

def subgradientGraph : Spec.SubgradientGraphType.{u} := Spec.SubgradientGraphValue

theorem maximalMonotone_iff_related : Spec.MaximalityLaw.{u} := by
  intro X _ _ A
  constructor
  · rintro ⟨hA, hmax⟩
    refine ⟨hA, ?_⟩
    intro x f hrelated
    have hins : Spec.MonotoneValue X (insert (x, f) A) := by
      intro y z g h hy hz
      rcases hy with hy | hy
      · cases hy
        rcases hz with hz | hz
        · cases hz
          simp
        · exact hrelated z h hz
      · rcases hz with hz | hz
        · cases hz
          have hr := hrelated y g hy
          calc
            0 ≤ (f - g) (x - y) := hr
            _ = (g - f) (y - x) := by
              rw [← neg_sub f g, ← neg_sub x y]
              simp only [neg_apply, map_neg, neg_neg]
        · exact hA hy hz
    have heq := hmax _ hins (Set.subset_insert _ _)
    rw [← heq]
    exact Set.mem_insert _ _
  · rintro ⟨hA, hrelated⟩
    refine ⟨hA, ?_⟩
    intro B hB hAB
    apply Set.Subset.antisymm ?_ hAB
    rintro ⟨x, f⟩ hxf
    exact hrelated x f (fun y g hyg => hB hxf (hAB hyg))

theorem monotone_graphOfMap_iff : Spec.MapGraphLaw.{u} := by
  intro X _ _ A
  constructor
  · intro h x y
    exact h (show (x, A x) ∈ Spec.MapGraphValue X A from rfl)
      (show (y, A y) ∈ Spec.MapGraphValue X A from rfl)
  · intro h x y f g hf hg
    change f = A x at hf
    change g = A y at hg
    subst f
    subst g
    exact h x y

theorem monotoneOn_iff_graph : Spec.MonotoneOnLaw.{u} := by
  intro X _ _ A D
  constructor
  · intro h x y f g hf hg
    change x ∈ D ∧ f = A x at hf
    change y ∈ D ∧ g = A y at hg
    rcases hf with ⟨hx, rfl⟩
    rcases hg with ⟨hy, rfl⟩
    exact h x hx y hy
  · intro h x hx y hy
    exact h ⟨hx, rfl⟩ ⟨hy, rfl⟩

theorem strictMonotoneMap_monotone : Spec.StrictMonotonicityLaw.{u} := by
  intro X _ _ A h x y
  by_cases heq : x = y
  · subst y
    simp
  · exact le_of_lt (h x y heq)

theorem mem_linearGraph : Spec.LinearGraphLaw.{u} := by
  intro X _ _ A x f
  change (x, f) ∈ A.graph ↔ _
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨y, hy, hf⟩
    change (y : X) = x at hy
    change A y = f at hf
    subst x
    exact ⟨y.2, hf⟩
  · rintro ⟨hx, hf⟩
    exact ⟨⟨x, hx⟩, rfl, hf⟩

theorem linearMonotone_iff : Spec.LinearMonotonicityLaw.{u} := by
  intro X _ _ A
  constructor
  · intro h x y
    exact h (A.mem_graph x) (A.mem_graph y)
  · intro h x y f g hf hg
    change (x, f) ∈ A.graph at hf
    change (y, g) ∈ A.graph at hg
    obtain ⟨u, hu, huf⟩ := (LinearPMap.mem_graph_iff A).mp hf
    obtain ⟨v, hv, hvg⟩ := (LinearPMap.mem_graph_iff A).mp hg
    change (u : X) = x at hu
    change (v : X) = y at hv
    change A u = f at huf
    change A v = g at hvg
    subst x
    subst y
    subst f
    subst g
    exact h u v

theorem linearMonotone_iff_positive : Spec.LinearPositivityLaw.{u} := by
  intro X _ _ A
  rw [linearMonotone_iff X A]
  constructor
  · intro h x
    simpa only [Submodule.coe_zero, A.map_zero, sub_zero] using h x 0
  · intro h x y
    have hp := h (x - y)
    simpa only [A.map_sub, Submodule.coe_sub] using hp

theorem coercive_iff : Spec.CoercivityLaw.{u} := by
  intro X _ _ A
  simp only [Spec.CoerciveValue, Filter.tendsto_atTop, Filter.eventually_comap,
    Filter.eventually_atTop]
  constructor
  · intro h M
    obtain ⟨R, hR⟩ := h M
    exact ⟨R, fun x hx => hR ‖x‖ hx x rfl⟩
  · intro h M
    obtain ⟨R, hR⟩ := h M
    exact ⟨R, fun r hr x hx => hR x (hx ▸ hr)⟩

theorem monotone_hilbertGraph_iff : Spec.HilbertMonotonicityLaw.{u} := by
  intro H _ _ A
  constructor
  · intro h x y a b ha hb
    have hp := h ⟨(x, a), ha, rfl⟩ ⟨(y, b), hb, rfl⟩
    simpa only [sub_apply, InnerProductSpace.toDualMap_apply_apply,
      inner_sub_left] using hp
  · intro h x y f g hf hg
    obtain ⟨⟨u, a⟩, hua, heq⟩ := hf
    obtain ⟨⟨v, b⟩, hvb, heq'⟩ := hg
    cases heq
    cases heq'
    simpa only [sub_apply, InnerProductSpace.toDualMap_apply_apply,
      inner_sub_left] using h hua hvb

theorem mem_hilbertGraph_iff : Spec.HilbertRieszLaw.{u} := by
  intro H _ _ _ A x f
  constructor
  · rintro ⟨⟨y, a⟩, hya, heq⟩
    cases heq
    simpa only [← InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      LinearIsometryEquiv.symm_apply_apply] using hya
  · intro h
    refine ⟨(x, (InnerProductSpace.toDual ℝ H).symm f), h, ?_⟩
    simp only [← InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      LinearIsometryEquiv.apply_symm_apply]

theorem maximalMonotone_hilbertGraph_iff : Spec.HilbertMaximalityLaw.{u} := by
  intro H _ _ _ A
  rw [maximalMonotone_iff_related H, monotone_hilbertGraph_iff H]
  apply and_congr_right
  intro _
  constructor
  · intro h x a hrel
    have hm : (x, InnerProductSpace.toDualMap ℝ H a) ∈ Spec.HilbertGraphValue H A := by
      apply h
      intro y g hg
      have hg' := (mem_hilbertGraph_iff H A y g).mp hg
      have hi := hrel y ((InnerProductSpace.toDual ℝ H).symm g) hg'
      simpa only [sub_apply, InnerProductSpace.toDualMap_apply_apply,
        inner_sub_left, InnerProductSpace.toDual_symm_apply] using hi
    have hm' := (mem_hilbertGraph_iff H A x _).mp hm
    simpa only [← InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      LinearIsometryEquiv.symm_apply_apply] using hm'
  · intro h x f hrel
    apply (mem_hilbertGraph_iff H A x f).mpr
    apply h
    intro y b hyb
    have hi := hrel y (InnerProductSpace.toDualMap ℝ H b) ⟨(y, b), hyb, rfl⟩
    simpa only [sub_apply, InnerProductSpace.toDualMap_apply_apply,
      inner_sub_left, InnerProductSpace.toDual_symm_apply] using hi

end ExpandedFA.Monotone
