import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Sphere
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Meromorphic.Order

/-! Independent definitions and statements for paper.tex:1733–1740, d12:07-04,
with the source-coordinate extension specified at d12:07-05. The local quotient
and arithmetic proposition is a separate obligation. No quotient, sphere-map
bridge, classification, or assumed analytic certificate is part of this definition.
-/
noncomputable section
open Filter Set
open scoped Topology Classical
namespace D12Complex

/-- The ordinary scalar expression; the filler at a pole is ignored in punctured germs. -/
def scalarFinitePart : (ℂ → RiemannSphere) → ℂ → ℂ :=
  fun F z => finiteCoordinate (F z)

/-- The infinity fiber restricted to the given open set. -/
def scalarPoleSet : Set ℂ → (ℂ → RiemannSphere) → Set ℂ :=
  fun Ω F => {z | z ∈ Ω ∧ F z = sphereInfty}

/-- Scalar meromorphy on a possibly empty or disconnected plane open set.
Relative closedness is in Ω; each infinite value is an actual finite-order pole.
The last clause explicitly excludes a component identically equal to infinity. -/
def ScalarMeromorphicOn : Set ℂ → (ℂ → RiemannSphere) → Prop :=
  fun Ω F =>
  IsOpen Ω ∧
  IsClosed {z : Ω | F z = sphereInfty} ∧
  IsDiscrete (scalarPoleSet Ω F) ∧
  HolomorphicOn {z | z ∈ Ω ∧ F z ≠ sphereInfty} (scalarFinitePart F) ∧
  (∀ a ∈ Ω, F a = sphereInfty → PoleAt (scalarFinitePart F) a) ∧
  (∀ a ∈ Ω, ∃ b ∈ connectedComponentIn Ω a, F b ≠ sphereInfty)

/-- The locally identically zero sphere-valued scalar germ, including the center. -/
def scalarZeroGerm : (ℂ → RiemannSphere) → ℂ → Prop :=
  fun F a => ∀ᶠ z in 𝓝 a, F z = sphereFinite 0

/-- Partial signed order. `none` means no finite integer order (the zero germ);
`some k` is an integer order. Its intended domain is scalar meromorphic germs.
The theorems below identify it with analytic multiplicity and exact pole order. -/
def scalarSignedOrder : (ℂ → RiemannSphere) → ℂ → Option ℤ :=
  fun F a => meromorphicOrderAt (scalarFinitePart F) a

/-- The same scalar definition in both source coordinates. At source infinity
the coordinate is w = 1/z, with w = 0 representing infinity. These are source
charts; infinite target values still mean poles, not the constant infinity map. -/
def ScalarMeromorphicOnSphere : Set RiemannSphere → (RiemannSphere → RiemannSphere) → Prop :=
  fun U F => IsOpen U ∧
  ScalarMeromorphicOn (sphereFinite ⁻¹' U) (F ∘ sphereFinite) ∧
  ScalarMeromorphicOn (infinityParametrization ⁻¹' U) (F ∘ infinityParametrization)

/-- Signed order on the sphere using the finite source coordinate or w = 1/z. -/
def sphereScalarSignedOrder : (RiemannSphere → RiemannSphere) → RiemannSphere → Option ℤ :=
  fun F p => if p = sphereInfty then
  scalarSignedOrder (F ∘ infinityParametrization) 0
  else scalarSignedOrder (F ∘ sphereFinite) (finiteCoordinate p)

end D12Complex

namespace Specs.D12Complex.Ch07.Meromorphic
open _root_.D12Complex

def scalarFinitePart_type := (ℂ → RiemannSphere) → ℂ → ℂ
def scalarFinitePart_value : scalarFinitePart_type :=
  fun F z => finiteCoordinate (F z)

def scalarPoleSet_type := Set ℂ → (ℂ → RiemannSphere) → Set ℂ
def scalarPoleSet_value : scalarPoleSet_type :=
  fun Ω F => {z | z ∈ Ω ∧ F z = sphereInfty}

def ScalarMeromorphicOn_type := Set ℂ → (ℂ → RiemannSphere) → Prop
def ScalarMeromorphicOn_value : ScalarMeromorphicOn_type :=
  fun Ω F =>
  IsOpen Ω ∧
  IsClosed {z : Ω | F z = sphereInfty} ∧
  IsDiscrete (scalarPoleSet Ω F) ∧
  HolomorphicOn {z | z ∈ Ω ∧ F z ≠ sphereInfty} (scalarFinitePart F) ∧
  (∀ a ∈ Ω, F a = sphereInfty → PoleAt (scalarFinitePart F) a) ∧
  (∀ a ∈ Ω, ∃ b ∈ connectedComponentIn Ω a, F b ≠ sphereInfty)

def scalarZeroGerm_type := (ℂ → RiemannSphere) → ℂ → Prop
def scalarZeroGerm_value : scalarZeroGerm_type :=
  fun F a => ∀ᶠ z in 𝓝 a, F z = sphereFinite 0

def scalarSignedOrder_type := (ℂ → RiemannSphere) → ℂ → Option ℤ
def scalarSignedOrder_value : scalarSignedOrder_type :=
  fun F a => meromorphicOrderAt (scalarFinitePart F) a

def ScalarMeromorphicOnSphere_type := Set RiemannSphere → (RiemannSphere → RiemannSphere) → Prop
def ScalarMeromorphicOnSphere_value : ScalarMeromorphicOnSphere_type :=
  fun U F => IsOpen U ∧
  ScalarMeromorphicOn (sphereFinite ⁻¹' U) (F ∘ sphereFinite) ∧
  ScalarMeromorphicOn (infinityParametrization ⁻¹' U) (F ∘ infinityParametrization)

def sphereScalarSignedOrder_type := (RiemannSphere → RiemannSphere) → RiemannSphere → Option ℤ
def sphereScalarSignedOrder_value : sphereScalarSignedOrder_type :=
  fun F p => if p = sphereInfty then
  scalarSignedOrder (F ∘ infinityParametrization) 0
  else scalarSignedOrder (F ∘ sphereFinite) (finiteCoordinate p)

def scalarMeromorphicOn_finite_analytic_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, F a ≠ sphereInfty → AnalyticAt ℂ (scalarFinitePart F) a

def scalarMeromorphicOn_not_identicallyInfty_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, ¬ Set.EqOn F (fun _ => sphereInfty) (connectedComponentIn Ω a)

def scalarSignedOrder_finite_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, F a ≠ sphereInfty →
  scalarSignedOrder F a = (analyticOrderAt (scalarFinitePart F) a).map (fun n => (n : ℤ))

def scalarSignedOrder_of_zeroMultiplicity_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, F a ≠ sphereInfty → ∀ m : ℕ,
  Specs.D12Complex.Ch05.LocalZeroFactorization.HasFiniteOrder_value (scalarFinitePart F) a m →
  scalarSignedOrder F a = some (m : ℤ)

def scalarSignedOrder_pole_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (a : ℂ) (m : ℕ),
  PoleOfOrderAt (scalarFinitePart F) a m → scalarSignedOrder F a = some (-(m : ℤ))

def scalarSignedOrder_regular_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, ∀ c : ℂ, F a = sphereFinite c → c ≠ 0 → scalarSignedOrder F a = some 0

def scalarSignedOrder_none_iff_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, scalarSignedOrder F a = none ↔ scalarZeroGerm F a

def scalarSignedOrder_exists_iff_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
  ∀ a ∈ Ω, (∃ k : ℤ, scalarSignedOrder F a = some k) ↔ ¬ scalarZeroGerm F a

def sphereScalarSignedOrder_finite_type : Prop :=
  ∀ (F : RiemannSphere → RiemannSphere) (z : ℂ),
  sphereScalarSignedOrder F (sphereFinite z) = scalarSignedOrder (F ∘ sphereFinite) z

def sphereScalarSignedOrder_infty_type : Prop :=
  ∀ F : RiemannSphere → RiemannSphere,
  sphereScalarSignedOrder F sphereInfty = scalarSignedOrder (F ∘ infinityParametrization) 0

def scalarMeromorphicOnSphere_finite_type : Prop :=
  ∀ (U : Set RiemannSphere) (F : RiemannSphere → RiemannSphere),
  ScalarMeromorphicOnSphere U F → ScalarMeromorphicOn (sphereFinite ⁻¹' U) (F ∘ sphereFinite)

def scalarMeromorphicOnSphere_infty_type : Prop :=
  ∀ (U : Set RiemannSphere) (F : RiemannSphere → RiemannSphere),
  ScalarMeromorphicOnSphere U F →
  ScalarMeromorphicOn (infinityParametrization ⁻¹' U) (F ∘ infinityParametrization)

end Specs.D12Complex.Ch07.Meromorphic
