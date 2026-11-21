import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Order.Directed

/-! Independent specifications for paper.tex, d10:04:nets,
d10:04:subnet-calculus and d10:04:cluster-subnet.
The order assumptions are preorders, with nonemptiness and upper directedness
stated separately. Neighborhoods have the paper's open-witness meaning. -/

open Set
universe u v w z
namespace Specs.D10Topology.Ch04.NetsAndSubnets

abbrev Net (D : Type v) (X : Type u) := D → X

def EventuallyIn {D : Type v} {X : Type u} [Preorder D]
    (a : Net D X) (A : Set X) : Prop :=
  ∃ d₀, ∀ d, d₀ ≤ d → a d ∈ A

def FrequentlyIn {D : Type v} {X : Type u} [Preorder D]
    (a : Net D X) (A : Set X) : Prop :=
  ∀ d₀, ∃ d, d₀ ≤ d ∧ a d ∈ A

def Converges {D : Type v} {X : Type u} [Preorder D]
    (t : TopologicalSpace X) (a : Net D X) (x : X) : Prop :=
  ∀ N, Ch01.BasesAndNeighborhoods.Neighborhood t x N → EventuallyIn a N

def Clusters {D : Type v} {X : Type u} [Preorder D]
    (t : TopologicalSpace X) (a : Net D X) (x : X) : Prop :=
  ∀ N, Ch01.BasesAndNeighborhoods.Neighborhood t x N → FrequentlyIn a N

/-- A Moore–Smith index map: monotone with cofinal range. -/
def SubnetMap {E : Type w} {D : Type v} [Preorder E] [Preorder D]
    (φ : E → D) : Prop := Monotone φ ∧ ∀ d, ∃ e, d ≤ φ e

def subnet {E : Type w} {D : Type v} {X : Type u}
    (a : Net D X) (φ : E → D) : Net E X := a ∘ φ

/-- All the data of an actual directed index set and subnet, not a filter witness.
The universe max u v accommodates pairs of original indices and subsets of X. -/
def HasConvergentSubnet {D : Type v} {X : Type u} [Preorder D]
    (t : TopologicalSpace X) (a : Net D X) (x : X) : Prop :=
  ∃ (E : Type (max u v)) (p : Preorder E),
    Nonempty E ∧ @IsDirectedOrder E p.toLE ∧
    ∃ φ : E → D, @SubnetMap E D p _ φ ∧ @Converges E X p t (subnet a φ) x

-- Values as well as types are part of the definition contract.
def netType := (D : Type v) → (X : Type u) → Type (max u v)
def netValue : netType := fun D X => D → X

def eventuallyInType := {D : Type v} → {X : Type u} → [Preorder D] →
  Net D X → Set X → Prop
def eventuallyInValue : eventuallyInType := fun {D} {X} [Preorder D] => @EventuallyIn D X _

def frequentlyInType := {D : Type v} → {X : Type u} → [Preorder D] →
  Net D X → Set X → Prop
def frequentlyInValue : frequentlyInType := fun {D} {X} [Preorder D] => @FrequentlyIn D X _

def convergesType := {D : Type v} → {X : Type u} → [Preorder D] →
  TopologicalSpace X → Net D X → X → Prop
def convergesValue : convergesType := fun {D} {X} [Preorder D] => @Converges D X _

def clustersType := {D : Type v} → {X : Type u} → [Preorder D] →
  TopologicalSpace X → Net D X → X → Prop
def clustersValue : clustersType := fun {D} {X} [Preorder D] => @Clusters D X _

def subnetMapType := {E : Type w} → {D : Type v} → [Preorder E] → [Preorder D] →
  (E → D) → Prop
def subnetMapValue : subnetMapType := fun {E} {D} [Preorder E] [Preorder D] =>
  @SubnetMap E D _ _

def subnetType := {E : Type w} → {D : Type v} → {X : Type u} →
  Net D X → (E → D) → Net E X
def subnetValue : subnetType := fun {E} {D} {X} => @subnet E D X

def hasConvergentSubnetType := {D : Type v} → {X : Type u} → [Preorder D] →
  TopologicalSpace X → Net D X → X → Prop
def hasConvergentSubnetValue : hasConvergentSubnetType := fun {D} {X} [Preorder D] => @HasConvergentSubnet D X _

def subnetMap_eventually_above : Prop :=
  ∀ {D : Type v} {E : Type w} [Preorder D] [Preorder E]
    (φ : E → D), SubnetMap φ → ∀ d, ∃ e₀, ∀ e, e₀ ≤ e → d ≤ φ e

def eventuallyIn_subnet : Prop :=
  ∀ {D : Type v} {E : Type w} {X : Type u} [Preorder D] [Preorder E]
    (a : Net D X) (φ : E → D) (A : Set X), SubnetMap φ →
    EventuallyIn a A → EventuallyIn (subnet a φ) A

def converges_subnet : Prop :=
  ∀ {D : Type v} {E : Type w} {X : Type u} [Preorder D] [Preorder E]
    (t : TopologicalSpace X) (a : Net D X) (φ : E → D) (x : X),
    SubnetMap φ → Converges t a x → Converges t (subnet a φ) x

def subnetMap_comp : Prop :=
  ∀ {D : Type v} {E : Type w} {F : Type z} [Preorder D] [Preorder E] [Preorder F]
    (φ : E → D) (ψ : F → E), SubnetMap φ → SubnetMap ψ → SubnetMap (φ ∘ ψ)

def subnet_comp : Prop :=
  ∀ {D : Type v} {E : Type w} {F : Type z} {X : Type u}
    (a : Net D X) (φ : E → D) (ψ : F → E),
    subnet (subnet a φ) ψ = subnet a (φ ∘ ψ)

def frequentlyIn_of_subnet : Prop :=
  ∀ {D : Type v} {E : Type w} {X : Type u} [Preorder D] [Preorder E]
    (a : Net D X) (φ : E → D) (A : Set X), SubnetMap φ →
    FrequentlyIn (subnet a φ) A → FrequentlyIn a A

def clusters_of_subnet : Prop :=
  ∀ {D : Type v} {E : Type w} {X : Type u} [Preorder D] [Preorder E]
    (t : TopologicalSpace X) (a : Net D X) (φ : E → D) (x : X),
    SubnetMap φ → Clusters t (subnet a φ) x → Clusters t a x

def converges_clusters : Prop :=
  ∀ {D : Type v} {X : Type u} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (t : TopologicalSpace X) (a : Net D X) (x : X), Converges t a x → Clusters t a x

def cluster_iff_convergent_subnet : Prop :=
  ∀ {D : Type v} {X : Type u} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (t : TopologicalSpace X) (a : Net D X) (x : X),
    Clusters t a x ↔ HasConvergentSubnet t a x

end Specs.D10Topology.Ch04.NetsAndSubnets
