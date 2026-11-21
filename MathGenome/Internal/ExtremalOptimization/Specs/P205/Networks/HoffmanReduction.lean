import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualFoundation
import Mathlib.Data.Fintype.Sum

/-! Independent specification of the lower-bound shift and the auxiliary
source--sink construction in paper.tex, proof of W38 (1791–1815).
All original vertices/arcs remain labelled, and artificial arcs exist exactly
at strictly positive/negative balances. In particular empty types are allowed. -/
open scoped BigOperators Classical
universe u v
namespace P205.Networks.HoffmanSpec
open FiniteCombinatorics.Directed FiniteCombinatorics.Graph.Flows
noncomputable section
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

def shiftCapacity (lo hi : A → ℝ) := fun a => hi a - lo a
def shiftBalance (G : Digraph V A) (lo : A → ℝ) (b : V → ℝ) :=
  fun x => b x - G.divergence lo x
def shiftLoad (lo f : A → ℝ) := fun a => f a - lo a
def unshiftLoad (lo g : A → ℝ) := fun a => g a + lo a
def vertexSum (b : V → ℝ) (S : Set V) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => x ∈ S), b x
def CutCondition (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) : Prop :=
  ∀ S : Set V, vertexSum b S ≤
    BoundedSpec.arcSum hi (BoundedSpec.outgoing G S) -
    BoundedSpec.arcSum lo (BoundedSpec.incoming G S)
def Integral {X : Type*} (f : X → ℝ) : Prop := ∀ x, ∃ z : ℤ, f x = z

abbrev AuxVertex (V : Type u) := V ⊕ Bool
abbrev Positive (β : V → ℝ) := {x : V // 0 < β x}
abbrev Negative (β : V → ℝ) := {x : V // β x < 0}
abbrev AuxArc (A : Type v) (β : V → ℝ) := A ⊕ (Positive β ⊕ Negative β)
def source : AuxVertex V := .inr false
def sink : AuxVertex V := .inr true

def auxGraph (G : Digraph V A) (β : V → ℝ) : Digraph (AuxVertex V) (AuxArc A β) where
  tail
    | .inl a => .inl (G.tail a)
    | .inr (.inl _) => source
    | .inr (.inr x) => .inl x.val
  head
    | .inl a => .inl (G.head a)
    | .inr (.inl x) => .inl x.val
    | .inr (.inr _) => sink

def auxCapacity (c : A → ℝ) (β : V → ℝ) : AuxArc A β → ℝ
  | .inl a => c a
  | .inr (.inl x) => β x.val
  | .inr (.inr x) => -β x.val

def auxNetwork (G : Digraph V A) (c : A → ℝ) (β : V → ℝ)
    (hc : ∀ a, 0 ≤ c a) : Network (AuxVertex V) (AuxArc A β) where
  graph := auxGraph G β
  capacity := auxCapacity c β
  capacity_nonneg := by
    intro a
    rcases a with a | (x | x)
    · exact hc a
    · exact le_of_lt x.property
    · exact le_of_lt (neg_pos.mpr x.property)
  source := source
  sink := sink
  source_ne_sink := by simp [source, sink]

/-- The auxiliary network for the original lower/upper-bound data. -/
def shiftedNetwork (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ)
    (hbounds : ∀ a, lo a ≤ hi a) :=
  auxNetwork G (shiftCapacity lo hi) (shiftBalance G lo b)
    (fun a => sub_nonneg.mpr (hbounds a))

def demand (β : V → ℝ) : ℝ := ∑ x : Positive β, β x.val
def negativeDemand (β : V → ℝ) : ℝ := ∑ x : Negative β, -β x.val

def extend (β : V → ℝ) (g : A → ℝ) : AuxArc A β → ℝ
  | .inl a => g a
  | .inr (.inl x) => β x.val
  | .inr (.inr x) => -β x.val

def restrict (β : V → ℝ) (F : AuxArc A β → ℝ) : A → ℝ := fun a => F (.inl a)
def originalPart (T : Set (AuxVertex V)) : Set V := {x | Sum.inl x ∈ T}
def liftCut (S : Set V) : Set (AuxVertex V) :=
  {x | match x with | .inl v => v ∈ S | .inr b => b = false}

section Expected
set_option linter.checkUnivs false

def shiftCapacityType := ∀ {A : Type v}, (A → ℝ) → (A → ℝ) → A → ℝ
def shiftBalanceType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Digraph V A → (A → ℝ) → (V → ℝ) → V → ℝ
def shiftLoadType := ∀ {A : Type v}, (A → ℝ) → (A → ℝ) → A → ℝ
def unshiftLoadType := ∀ {A : Type v}, (A → ℝ) → (A → ℝ) → A → ℝ
def auxNetworkType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  (G : Digraph V A) → (c : A → ℝ) → (β : V → ℝ) →
  (∀ a, 0 ≤ c a) → Network (AuxVertex V) (AuxArc A β)
def shiftedNetworkType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  (G : Digraph V A) → (lo hi : A → ℝ) → (b : V → ℝ) →
  (∀ a, lo a ≤ hi a) → Network (AuxVertex V) (AuxArc A (shiftBalance G lo b))
def demandType := ∀ {V : Type u} [Fintype V], (V → ℝ) → ℝ
def extendType := ∀ {V : Type u} {A : Type v}, (β : V → ℝ) → (A → ℝ) → AuxArc A β → ℝ
def restrictType := ∀ {V : Type u} {A : Type v}, (β : V → ℝ) → (AuxArc A β → ℝ) → A → ℝ

def shift_feasible : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (lo hi f : A → ℝ) (b : V → ℝ),
  BoundedSpec.Feasible G lo hi b f ↔
    BoundedSpec.Feasible G (fun _ => 0) (shiftCapacity lo hi)
      (shiftBalance G lo b) (shiftLoad lo f)

def unshift_feasible : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (lo hi g : A → ℝ) (b : V → ℝ),
  BoundedSpec.Feasible G (fun _ => 0) (shiftCapacity lo hi) (shiftBalance G lo b) g ↔
    BoundedSpec.Feasible G lo hi b (unshiftLoad lo g)

def shift_cut : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (S : Set V),
  (vertexSum b S ≤ BoundedSpec.arcSum hi (BoundedSpec.outgoing G S) -
    BoundedSpec.arcSum lo (BoundedSpec.incoming G S)) ↔
  vertexSum (shiftBalance G lo b) S ≤
    BoundedSpec.arcSum (shiftCapacity lo hi) (BoundedSpec.outgoing G S)

def shift_balance_sum : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (lo : A → ℝ) (b : V → ℝ),
  (∑ x, b x) = 0 → (∑ x, shiftBalance G lo b x) = 0

def demand_eq : Prop := ∀ {V : Type u} [Fintype V] (β : V → ℝ),
  (∑ x, β x) = 0 → demand β = negativeDemand β

def extension : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (c g : A → ℝ) (β : V → ℝ) (hc : ∀ a, 0 ≤ c a),
  BoundedSpec.Feasible G (fun _ => 0) c β g →
    (auxNetwork G c β hc).Feasible (extend β g) ∧
    (auxNetwork G c β hc).value (extend β g) = demand β ∧
    restrict β (extend β g) = g

def saturation : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (c : A → ℝ) (β : V → ℝ) (hc : ∀ a, 0 ≤ c a)
  (F : AuxArc A β → ℝ), (∑ x, β x) = 0 →
  (auxNetwork G c β hc).Feasible F → (auxNetwork G c β hc).value F = demand β →
    (∀ x : Positive β, F (.inr (.inl x)) = β x.val) ∧
    (∀ x : Negative β, F (.inr (.inr x)) = -β x.val)

def restriction : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (c : A → ℝ) (β : V → ℝ) (hc : ∀ a, 0 ≤ c a)
  (F : AuxArc A β → ℝ), (∑ x, β x) = 0 →
  (auxNetwork G c β hc).Feasible F → (auxNetwork G c β hc).value F = demand β →
    BoundedSpec.Feasible G (fun _ => 0) c β (restrict β F) ∧
    extend β (restrict β F) = F

def feasible_iff : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (c : A → ℝ) (β : V → ℝ) (hc : ∀ a, 0 ≤ c a),
  (∑ x, β x) = 0 →
  ((∃ g, BoundedSpec.Feasible G (fun _ => 0) c β g) ↔
    ∃ F, (auxNetwork G c β hc).Feasible F ∧ (auxNetwork G c β hc).value F = demand β)

def cut_capacity : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (c : A → ℝ) (β : V → ℝ) (hc : ∀ a, 0 ≤ c a)
  (T : Set (AuxVertex V)), (auxNetwork G c β hc).IsCut T →
  (auxNetwork G c β hc).cutCapacity T = demand β +
    BoundedSpec.arcSum c (BoundedSpec.outgoing G (originalPart T)) -
    vertexSum β (originalPart T)

def cut_inequalities : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (c : A → ℝ) (β : V → ℝ) (hc : ∀ a, 0 ≤ c a),
  (∀ S, vertexSum β S ≤ BoundedSpec.arcSum c (BoundedSpec.outgoing G S)) ↔
    ∀ T, (auxNetwork G c β hc).IsCut T → demand β ≤ (auxNetwork G c β hc).cutCapacity T

/-- Integer data and witnesses are preserved in both directions, including
all artificial capacities. Integer-valued means actual integer coordinates. -/
def integral_shift : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (G : Digraph V A) (lo hi f : A → ℝ) (b : V → ℝ),
  Integral lo → Integral hi → Integral b →
    Integral (shiftCapacity lo hi) ∧ Integral (shiftBalance G lo b) ∧
    (Integral f ↔ Integral (shiftLoad lo f)) ∧
    (Integral f ↔ Integral (unshiftLoad lo f))

def integral_auxiliary : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
  (c : A → ℝ) (β : V → ℝ), Integral c → Integral β →
    Integral (auxCapacity c β) ∧ (∃ z : ℤ, demand β = z) ∧
    (∀ g : A → ℝ, Integral g ↔ Integral (extend β g)) ∧
    (∀ F : AuxArc A β → ℝ, Integral F → Integral (restrict β F))


/-- The full specialization to the original bounded fixed-divergence problem. -/
def original_feasible_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (hbounds : ∀ a, lo a ≤ hi a),
    (∑ x, b x) = 0 →
    ((∃ f, BoundedSpec.Feasible G lo hi b f) ↔
      ∃ F, (shiftedNetwork G lo hi b hbounds).Feasible F ∧
        (shiftedNetwork G lo hi b hbounds).value F = demand (shiftBalance G lo b))

def original_cut_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (hbounds : ∀ a, lo a ≤ hi a),
    CutCondition G lo hi b ↔
      ∀ T, (shiftedNetwork G lo hi b hbounds).IsCut T →
        demand (shiftBalance G lo b) ≤ (shiftedNetwork G lo hi b hbounds).cutCapacity T

def original_integral_iff : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (hbounds : ∀ a, lo a ≤ hi a),
    (∑ x, b x) = 0 → Integral lo → Integral hi → Integral b →
    ((∃ f, BoundedSpec.Feasible G lo hi b f ∧ Integral f) ↔
      ∃ F, (shiftedNetwork G lo hi b hbounds).Feasible F ∧
        (shiftedNetwork G lo hi b hbounds).value F = demand (shiftBalance G lo b) ∧ Integral F)

end Expected
end
end P205.Networks.HoffmanSpec
