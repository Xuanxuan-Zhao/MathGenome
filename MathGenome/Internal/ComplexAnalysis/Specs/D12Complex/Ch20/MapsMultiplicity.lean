import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereHolomorphic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Meromorphic

/-! Maps in the explicit-atlas surface interface. Regularity is weak complex
holomorphy on a neighborhood, not an assumed power-series certificate. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Surfaces
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Total coordinate representative, used only near points in both chart domains. -/
def coordinateMap (e : ComplexChart X) (d : ComplexChart Y) (f : X → Y) : ℂ → ℂ :=
  fun z => d.val (f (e.val.symm z))

/-- Holomorphy at a point is tested in one pair of charts from the given atlases. -/
def HolomorphicMapAt (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) (a : X) : Prop :=
  ContinuousAt f a ∧ ∃ e ∈ S.atlas, ∃ d ∈ T.atlas,
    a ∈ e.val.source ∧ f a ∈ d.val.source ∧
      HolomorphicGermAt (coordinateMap e d f) (e.val a)

/-- A holomorphic map is an actual continuous map with holomorphic coordinate germs. -/
def HolomorphicMap (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y) : Prop :=
  ∀ a, HolomorphicMapAt S T f a

/-- Scalar holomorphy on a surface, in its source charts. -/
def ScalarHolomorphic (S : RiemannSurface X) (f : X → ℂ) : Prop :=
  Continuous f ∧ ∀ e ∈ S.atlas, HolomorphicOn e.val.target (f ∘ e.val.symm)

/-- Scalar meromorphy retains finite-order poles and excludes a component
identically equal to infinity, through the canonical plane predicate. -/
def ScalarMeromorphic (S : RiemannSurface X) (F : X → RiemannSphere) : Prop :=
  ∀ e ∈ S.atlas, ScalarMeromorphicOn e.val.target (F ∘ e.val.symm)

/-- Sphere-valued holomorphy includes the constant infinity map. -/
def SphereValuedHolomorphic (S : RiemannSurface X) (F : X → RiemannSphere) : Prop :=
  Continuous F ∧ ∀ e ∈ S.atlas,
    PlaneSphereHolomorphicOn e.val.target (F ∘ e.val.symm)

/-- The coordinate expression is used only where both charts are valid. -/
def coordinateDomain (e : ComplexChart X) (d : ComplexChart Y) (f : X → Y) : Set ℂ :=
  e.val.target ∩ {z | f (e.val.symm z) ∈ d.val.source}

/-- Order of the centered coordinate expression; infinity denotes a zero germ. -/
def coordinateOrder (e : ComplexChart X) (d : ComplexChart Y) (f : X → Y) (a : X) : ℕ∞ :=
  analyticOrderAt (fun z => coordinateMap e d f z - d.val (f a)) (e.val a)

/-- A positive integer agrees with the order in every compatible pair of charts. -/
def HasMultiplicity (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) (a : X) (m : ℕ) : Prop :=
  0 < m ∧ ∀ e ∈ maximalAtlas S.atlas, ∀ d ∈ maximalAtlas T.atlas,
    a ∈ e.val.source → f a ∈ d.val.source → coordinateOrder e d f a = (m : ℕ∞)

/-- Centered biholomorphic coordinates giving a power. The source coordinate
is φ ∘ e with inverse e⁻¹ ∘ ψ; the target is d - d(f(a)). Both are genuine
biholomorphic coordinates, on their stated neighborhoods. -/
def PowerCoordinates (e : ComplexChart X) (d : ComplexChart Y)
    (f : X → Y) (a : X) (m : ℕ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ (U : Set ℂ) (φ ψ : ℂ → ℂ),
    e.val a ∈ U ∧ U ⊆ coordinateDomain e d f ∧
    BiholomorphicPair U (Metric.ball 0 r) φ ψ ∧ φ (e.val a) = 0 ∧
    ∀ z ∈ U, coordinateMap e d f z - d.val (f a) = (φ z)^m

/-- A local inverse in source and target coordinates is an actual local
biholomorphism of surface neighborhoods. -/
def LocallyBiholomorphicAt (S : RiemannSurface X) (T : RiemannSurface Y)
    (f : X → Y) (a : X) : Prop :=
  ∃ e ∈ S.atlas, ∃ d ∈ T.atlas, a ∈ e.val.source ∧ f a ∈ d.val.source ∧
    ∃ (U V : Set ℂ) (g : ℂ → ℂ), e.val a ∈ U ∧
      U ⊆ coordinateDomain e d f ∧ V ⊆ d.val.target ∧
      BiholomorphicPair U V (coordinateMap e d f) g

/-- The part of a coordinate domain lying over an open surface subset. -/
def chartDomain (e : ComplexChart X) (Ω : Set X) : Set ℂ :=
  e.val.target ∩ e.val.symm ⁻¹' Ω

/-- Scalar holomorphy on arbitrary open surface subsets, including disconnected
and empty subsets. -/
def ScalarHolomorphicOnSurface (S : RiemannSurface X) (Ω : Set X) (f : X → ℂ) : Prop :=
  IsOpen Ω ∧ ContinuousOn f Ω ∧ ∀ e ∈ S.atlas,
    HolomorphicOn (chartDomain e Ω) (f ∘ e.val.symm)

/-- Scalar meromorphy on arbitrary open surface subsets; the plane definition
excludes an identically infinite component on every chart overlap. -/
def ScalarMeromorphicOnSurface (S : RiemannSurface X) (Ω : Set X)
    (F : X → RiemannSphere) : Prop :=
  IsOpen Ω ∧ ∀ e ∈ S.atlas,
    ScalarMeromorphicOn (chartDomain e Ω) (F ∘ e.val.symm)

end D12Complex.Surfaces

namespace Specs.D12Complex.Ch20.MapsMultiplicity
open _root_.D12Complex _root_.D12Complex.Surfaces
universe u v

def coordinateMap_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → (e : ComplexChart X) → (d : ComplexChart Y) → (X → Y) → ℂ → ℂ
def coordinateMap_value : coordinateMap_type :=
  fun e d f z => d.val (f (e.val.symm z))

def HolomorphicMapAt_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → RiemannSurface X → RiemannSurface Y → (X → Y) → X → Prop
def HolomorphicMapAt_value : HolomorphicMapAt_type := fun S T f a =>
  ContinuousAt f a ∧ ∃ e ∈ S.atlas, ∃ d ∈ T.atlas,
    a ∈ e.val.source ∧ f a ∈ d.val.source ∧
      HolomorphicGermAt (coordinateMap e d f) (e.val a)

def HolomorphicMap_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → RiemannSurface X → RiemannSurface Y → (X → Y) → Prop
def HolomorphicMap_value : HolomorphicMap_type := fun S T f =>
  ∀ a, HolomorphicMapAt S T f a

def ScalarHolomorphic_type := {X : Type u} → [TopologicalSpace X] → RiemannSurface X → (X → ℂ) → Prop
def ScalarHolomorphic_value : ScalarHolomorphic_type := fun S f =>
  Continuous f ∧ ∀ e ∈ S.atlas, HolomorphicOn e.val.target (f ∘ e.val.symm)

def ScalarMeromorphic_type := {X : Type u} → [TopologicalSpace X] → RiemannSurface X → (X → RiemannSphere) → Prop
def ScalarMeromorphic_value : ScalarMeromorphic_type := fun S F =>
  ∀ e ∈ S.atlas, ScalarMeromorphicOn e.val.target (F ∘ e.val.symm)

def SphereValuedHolomorphic_type := {X : Type u} → [TopologicalSpace X] → RiemannSurface X → (X → RiemannSphere) → Prop
def SphereValuedHolomorphic_value : SphereValuedHolomorphic_type := fun S F =>
  Continuous F ∧ ∀ e ∈ S.atlas, PlaneSphereHolomorphicOn e.val.target (F ∘ e.val.symm)

def coordinateDomain_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → (e : ComplexChart X) → (d : ComplexChart Y) → (X → Y) → Set ℂ
def coordinateDomain_value : coordinateDomain_type := fun e d f =>
  e.val.target ∩ {z | f (e.val.symm z) ∈ d.val.source}

def coordinateOrder_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → (e : ComplexChart X) → (d : ComplexChart Y) → (X → Y) → X → ℕ∞
def coordinateOrder_value : coordinateOrder_type := fun e d f a =>
  analyticOrderAt (fun z => coordinateMap e d f z - d.val (f a)) (e.val a)

def HasMultiplicity_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → RiemannSurface X → RiemannSurface Y → (X → Y) → X → ℕ → Prop
def HasMultiplicity_value : HasMultiplicity_type := fun S T f a m =>
  0 < m ∧ ∀ e ∈ maximalAtlas S.atlas, ∀ d ∈ maximalAtlas T.atlas,
    a ∈ e.val.source → f a ∈ d.val.source → coordinateOrder e d f a = (m : ℕ∞)

def PowerCoordinates_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → ComplexChart X → ComplexChart Y → (X → Y) → X → ℕ → Prop
def PowerCoordinates_value : PowerCoordinates_type := fun e d f a m =>
  ∃ r : ℝ, 0 < r ∧ ∃ (U : Set ℂ) (φ ψ : ℂ → ℂ),
    e.val a ∈ U ∧ U ⊆ coordinateDomain e d f ∧
    BiholomorphicPair U (Metric.ball 0 r) φ ψ ∧ φ (e.val a) = 0 ∧
    ∀ z ∈ U, coordinateMap e d f z - d.val (f a) = (φ z)^m

def LocallyBiholomorphicAt_type := {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] → RiemannSurface X → RiemannSurface Y → (X → Y) → X → Prop
def LocallyBiholomorphicAt_value : LocallyBiholomorphicAt_type := fun S T f a =>
  ∃ e ∈ S.atlas, ∃ d ∈ T.atlas, a ∈ e.val.source ∧ f a ∈ d.val.source ∧
    ∃ (U V : Set ℂ) (g : ℂ → ℂ), e.val a ∈ U ∧
      U ⊆ coordinateDomain e d f ∧ V ⊆ d.val.target ∧
      BiholomorphicPair U V (coordinateMap e d f) g

/-- Any compatible source and target coordinates may replace the original ones. -/
def holomorphicMapAt_chart_independent_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y) (a : X),
    HolomorphicMapAt S T f a →
    ∀ e ∈ maximalAtlas S.atlas, ∀ d ∈ maximalAtlas T.atlas,
      a ∈ e.val.source → f a ∈ d.val.source →
        HolomorphicGermAt (coordinateMap e d f) (e.val a)

def holomorphicMap_continuous_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → Continuous f

/-- Constancy on any nonempty open subset propagates across the connected source. -/
def holomorphicMap_constant_of_open_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → ∀ (U : Set X), IsOpen U → U.Nonempty →
      ∀ c : Y, EqOn f (fun _ => c) U → ∀ x, f x = c

def coordinate_order_chart_independent_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y) (a : X),
    HolomorphicMapAt S T f a →
    ∀ e ∈ maximalAtlas S.atlas, ∀ d ∈ maximalAtlas T.atlas,
    ∀ e' ∈ maximalAtlas S.atlas, ∀ d' ∈ maximalAtlas T.atlas,
      a ∈ e.val.source → f a ∈ d.val.source →
      a ∈ e'.val.source → f a ∈ d'.val.source →
      coordinateOrder e d f a = coordinateOrder e' d' f a

def exists_unique_multiplicity_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
      ∀ a, ∃! m, HasMultiplicity S T f a m

def local_power_form_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
      ∀ (a : X) (m : ℕ), HasMultiplicity S T f a m →
        ∀ e ∈ maximalAtlas S.atlas, ∀ d ∈ maximalAtlas T.atlas,
          a ∈ e.val.source → f a ∈ d.val.source → PowerCoordinates e d f a m

def locally_biholomorphic_iff_multiplicity_one_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y),
    HolomorphicMap S T f → (¬ ∃ c, ∀ x, f x = c) →
      ∀ (a : X) (m : ℕ), HasMultiplicity S T f a m →
        (LocallyBiholomorphicAt S T f a ↔ m = 1)

def scalarMeromorphic_not_constant_infty_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], ∀ (S : RiemannSurface X), ¬ ScalarMeromorphic S (fun _ => sphereInfty)

def holomorphicMapAt_iff_chart_type : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y], ∀ (S : RiemannSurface X) (T : RiemannSurface Y) (f : X → Y) (a : X),
    ∀ e ∈ maximalAtlas S.atlas, ∀ d ∈ maximalAtlas T.atlas,
      a ∈ e.val.source → f a ∈ d.val.source →
      (HolomorphicMapAt S T f a ↔
        ContinuousAt f a ∧ HolomorphicGermAt (coordinateMap e d f) (e.val a))

def scalarHolomorphic_chart_independent_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], ∀ (S : RiemannSurface X) (f : X → ℂ), ScalarHolomorphic S f →
    ∀ e ∈ maximalAtlas S.atlas, HolomorphicOn e.val.target (f ∘ e.val.symm)

def scalarMeromorphic_chart_independent_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], ∀ (S : RiemannSurface X) (F : X → RiemannSphere), ScalarMeromorphic S F →
    ∀ e ∈ maximalAtlas S.atlas, ScalarMeromorphicOn e.val.target (F ∘ e.val.symm)

def scalarMeromorphic_sphereValuedHolomorphic_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], ∀ (S : RiemannSurface X) (F : X → RiemannSphere),
    ScalarMeromorphic S F → SphereValuedHolomorphic S F

def chartDomain_type := {X : Type u} → [TopologicalSpace X] → ComplexChart X → Set X → Set ℂ
def chartDomain_value : chartDomain_type := fun e Ω => e.val.target ∩ e.val.symm ⁻¹' Ω

def ScalarHolomorphicOnSurface_type := {X : Type u} → [TopologicalSpace X] →
  RiemannSurface X → Set X → (X → ℂ) → Prop
def ScalarHolomorphicOnSurface_value : ScalarHolomorphicOnSurface_type := fun S Ω f =>
  IsOpen Ω ∧ ContinuousOn f Ω ∧ ∀ e ∈ S.atlas,
    HolomorphicOn (chartDomain e Ω) (f ∘ e.val.symm)

def ScalarMeromorphicOnSurface_type := {X : Type u} → [TopologicalSpace X] →
  RiemannSurface X → Set X → (X → RiemannSphere) → Prop
def ScalarMeromorphicOnSurface_value : ScalarMeromorphicOnSurface_type := fun S Ω F =>
  IsOpen Ω ∧ ∀ e ∈ S.atlas,
    ScalarMeromorphicOn (chartDomain e Ω) (F ∘ e.val.symm)

def scalarHolomorphicOnSurface_univ_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (S : RiemannSurface X) (f : X → ℂ),
    ScalarHolomorphicOnSurface S univ f ↔ ScalarHolomorphic S f

def scalarMeromorphicOnSurface_univ_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (S : RiemannSurface X) (F : X → RiemannSphere),
    ScalarMeromorphicOnSurface S univ F ↔ ScalarMeromorphic S F

def scalarMeromorphicOnSurface_not_infty_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (S : RiemannSurface X) (Ω : Set X), Ω.Nonempty →
    ¬ ScalarMeromorphicOnSurface S Ω (fun _ => sphereInfty)

def sphereValuedHolomorphic_const_type : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (S : RiemannSurface X) (c : RiemannSphere),
    SphereValuedHolomorphic S (fun _ => c)

end Specs.D12Complex.Ch20.MapsMultiplicity
