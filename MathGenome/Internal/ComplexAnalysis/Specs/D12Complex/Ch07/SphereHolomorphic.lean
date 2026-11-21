import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereTopology

/-!
Holomorphic maps into the canonical sphere (paper.tex:1853–1860).
Total representatives are tested only locally at points of the specified open
set. A germ is holomorphic on an actual open neighborhood, using weak complex
differentiability. The two chart choices are exactly the upstream charts.
Continuity is part of the definition; identically infinite maps are allowed.
-/

open scoped Topology
noncomputable section
namespace D12Complex

/-- The two coordinates fixed in the source. -/
inductive SphereCoordinate where
  | finite
  | reciprocal
  deriving DecidableEq

/-- The canonical partial equivalence associated to a coordinate choice. -/
def sphereCoordinate : SphereCoordinate → PartialEquiv RiemannSphere ℂ
  | .finite => finiteChart
  | .reciprocal => infinityChart

/-- Holomorphy on some open neighborhood, without a regularity certificate. -/
def HolomorphicGermAt (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ V : Set ℂ, a ∈ V ∧ HolomorphicOn V f

/-- Holomorphic plane-to-sphere map at a point, in one available target chart. -/
def PlaneSphereHolomorphicAt (F : ℂ → RiemannSphere) (a : ℂ) : Prop :=
  ContinuousAt F a ∧ ∃ d : SphereCoordinate,
    F a ∈ (sphereCoordinate d).source ∧
      HolomorphicGermAt (fun z => sphereCoordinate d (F z)) a

/-- Holomorphic sphere-to-sphere map at a point, in available source and target charts. -/
def SphereHolomorphicAt (F : RiemannSphere → RiemannSphere) (p : RiemannSphere) : Prop :=
  ContinuousAt F p ∧ ∃ c d : SphereCoordinate,
    p ∈ (sphereCoordinate c).source ∧ F p ∈ (sphereCoordinate d).source ∧
      HolomorphicGermAt
        (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
        (sphereCoordinate c p)

/-- Holomorphic map from a plane open set to the sphere, including the empty set. -/
def PlaneSphereHolomorphicOn (Ω : Set ℂ) (F : ℂ → RiemannSphere) : Prop :=
  IsOpen Ω ∧ ∀ a ∈ Ω, PlaneSphereHolomorphicAt F a

/-- Holomorphic map from a sphere open set to the sphere. -/
def SphereHolomorphicOn (Ω : Set RiemannSphere)
    (F : RiemannSphere → RiemannSphere) : Prop :=
  IsOpen Ω ∧ ∀ p ∈ Ω, SphereHolomorphicAt F p

end D12Complex

namespace Specs.D12Complex.Ch07.SphereHolomorphic
open _root_.D12Complex

def SphereCoordinate_type := Type
def SphereCoordinate_value : SphereCoordinate_type := SphereCoordinate

def sphereCoordinate_type := SphereCoordinate → PartialEquiv RiemannSphere ℂ
def sphereCoordinate_value : sphereCoordinate_type
  | .finite => finiteChart
  | .reciprocal => infinityChart

def HolomorphicGermAt_type := (ℂ → ℂ) → ℂ → Prop
def HolomorphicGermAt_value : HolomorphicGermAt_type :=
  fun f a => ∃ V : Set ℂ, a ∈ V ∧ HolomorphicOn V f

def PlaneSphereHolomorphicAt_type := (ℂ → RiemannSphere) → ℂ → Prop
def PlaneSphereHolomorphicAt_value : PlaneSphereHolomorphicAt_type :=
  fun F a => ContinuousAt F a ∧ ∃ d : SphereCoordinate,
    F a ∈ (sphereCoordinate d).source ∧
      HolomorphicGermAt (fun z => sphereCoordinate d (F z)) a

def SphereHolomorphicAt_type := (RiemannSphere → RiemannSphere) → RiemannSphere → Prop
def SphereHolomorphicAt_value : SphereHolomorphicAt_type :=
  fun F p => ContinuousAt F p ∧ ∃ c d : SphereCoordinate,
    p ∈ (sphereCoordinate c).source ∧ F p ∈ (sphereCoordinate d).source ∧
      HolomorphicGermAt
        (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
        (sphereCoordinate c p)

def PlaneSphereHolomorphicOn_type := Set ℂ → (ℂ → RiemannSphere) → Prop
def PlaneSphereHolomorphicOn_value : PlaneSphereHolomorphicOn_type :=
  fun Ω F => IsOpen Ω ∧ ∀ a ∈ Ω, PlaneSphereHolomorphicAt F a

def SphereHolomorphicOn_type := Set RiemannSphere → (RiemannSphere → RiemannSphere) → Prop
def SphereHolomorphicOn_value : SphereHolomorphicOn_type :=
  fun Ω F => IsOpen Ω ∧ ∀ p ∈ Ω, SphereHolomorphicAt F p

/-- Both transition directions, and both identity transitions, are locally holomorphic. -/
def sphereCoordinate_transition_type : Prop :=
  ∀ (c d : SphereCoordinate) (p : RiemannSphere),
    p ∈ (sphereCoordinate c).source → p ∈ (sphereCoordinate d).source →
      HolomorphicGermAt
        (fun z => sphereCoordinate d ((sphereCoordinate c).symm z))
        (sphereCoordinate c p)

/-- Independence of target coordinate for a plane source. -/
def plane_target_chart_independent_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (a : ℂ) (c d : SphereCoordinate),
    ContinuousAt F a → F a ∈ (sphereCoordinate c).source →
    F a ∈ (sphereCoordinate d).source →
    (HolomorphicGermAt (fun z => sphereCoordinate c (F z)) a ↔
      HolomorphicGermAt (fun z => sphereCoordinate d (F z)) a)

/-- Simultaneous independence of both source and target coordinates. -/
def sphere_charts_independent_type : Prop :=
  ∀ (F : RiemannSphere → RiemannSphere) (p : RiemannSphere)
    (c c' d d' : SphereCoordinate), ContinuousAt F p →
    p ∈ (sphereCoordinate c).source → p ∈ (sphereCoordinate c').source →
    F p ∈ (sphereCoordinate d).source → F p ∈ (sphereCoordinate d').source →
    (HolomorphicGermAt
      (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
      (sphereCoordinate c p) ↔
    HolomorphicGermAt
      (fun z => sphereCoordinate d' (F ((sphereCoordinate c').symm z)))
      (sphereCoordinate c' p))

def planeSphereHolomorphicAt_iff_chart_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (a : ℂ) (d : SphereCoordinate),
    F a ∈ (sphereCoordinate d).source →
    (PlaneSphereHolomorphicAt F a ↔ ContinuousAt F a ∧
      HolomorphicGermAt (fun z => sphereCoordinate d (F z)) a)

def sphereHolomorphicAt_iff_charts_type : Prop :=
  ∀ (F : RiemannSphere → RiemannSphere) (p : RiemannSphere)
    (c d : SphereCoordinate), p ∈ (sphereCoordinate c).source →
    F p ∈ (sphereCoordinate d).source →
    (SphereHolomorphicAt F p ↔ ContinuousAt F p ∧
      HolomorphicGermAt
        (fun z => sphereCoordinate d (F ((sphereCoordinate c).symm z)))
        (sphereCoordinate c p))

def planeSphereHolomorphicAt_infty_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (a : ℂ), F a = sphereInfty →
    (PlaneSphereHolomorphicAt F a ↔ ContinuousAt F a ∧
      HolomorphicGermAt (fun z => infinityCoordinate (F z)) a) ∧
      infinityCoordinate (F a) = 0

def sphereHolomorphicAt_infty_target_type : Prop :=
  ∀ (F : RiemannSphere → RiemannSphere) (p : RiemannSphere)
    (c : SphereCoordinate), p ∈ (sphereCoordinate c).source → F p = sphereInfty →
    (SphereHolomorphicAt F p ↔ ContinuousAt F p ∧
      HolomorphicGermAt
        (fun z => infinityCoordinate (F ((sphereCoordinate c).symm z)))
        (sphereCoordinate c p)) ∧ infinityCoordinate (F p) = 0

def planeSphereHolomorphicOn_const_type : Prop :=
  ∀ (Ω : Set ℂ) (q : RiemannSphere), IsOpen Ω →
    PlaneSphereHolomorphicOn Ω (fun _ => q)

def sphereHolomorphicOn_const_type : Prop :=
  ∀ (Ω : Set RiemannSphere) (q : RiemannSphere), IsOpen Ω →
    SphereHolomorphicOn Ω (fun _ => q)

/-- The definitions really supply continuity on the stated open domains. -/
def planeSphereHolomorphicOn_continuousOn_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere),
    PlaneSphereHolomorphicOn Ω F → ContinuousOn F Ω

def sphereHolomorphicOn_continuousOn_type : Prop :=
  ∀ (Ω : Set RiemannSphere) (F : RiemannSphere → RiemannSphere),
    SphereHolomorphicOn Ω F → ContinuousOn F Ω

end Specs.D12Complex.Ch07.SphereHolomorphic
