import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions

/-! Chapter 8, `d04:08:continuity`. The domain and parameter set are actual
subtypes of Euclidean spaces. Integrals are the shared coordinatewise Riemann
integrals of zero extensions. All dimensions, including zero, are allowed.
The joint continuity assertion is stated for arbitrary parameter sets, which
includes both the open and compact parameter cases of the source. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C08.ProperContinuity
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model

def integral_sub_boundType : Prop := ∀ {n k} {S : Set (E n)}, Jordan S →
  ∀ (f g : S → E k), VectorRegionIntegrable f → VectorRegionIntegrable g →
  ‖vectorRegionIntegral f - vectorRegionIntegral g‖ ≤
    volume S * sSup (Set.range (fun x => ‖f x - g x‖))

def parameter_continuityType : Prop := ∀ {n m k} {S : Set (E n)} {P : Set (E m)},
  Jordan S → ∀ (f : S → P → E k), (∀ p, VectorRegionIntegrable (fun x => f x p)) →
  ∀ p₀ : P,
  Tendsto (fun p => sSup (Set.range (fun x => ‖f x p - f x p₀‖))) (𝓝 p₀) (𝓝 0) →
  ContinuousAt (fun p => vectorRegionIntegral (fun x => f x p)) p₀

def joint_continuityType : Prop := ∀ {n m k} {S : Set (E n)} {P : Set (E m)},
  Jordan S → ∀ (f : closure S × P → E k), Continuous f →
  (∀ p : P, VectorRegionIntegrable (fun x : S => f (⟨x, subset_closure x.property⟩, p))) ∧
  Continuous (fun p : P => vectorRegionIntegral
    (fun x : S => f (⟨x, subset_closure x.property⟩, p)))

def uniform_limitsType : Prop := ∀ {n m k} {S : Set (E n)} {P : Set (E m)},
  Jordan S → ∀ (f : ℕ → S → P → E k) (g : S → P → E k),
  (∀ j p, VectorRegionIntegrable (fun x => f j x p)) →
  TendstoUniformly (fun j (z : S × P) => f j z.1 z.2)
    (fun z => g z.1 z.2) atTop →
  (∀ p, VectorRegionIntegrable (fun x => g x p)) ∧
  TendstoUniformly (fun j p => vectorRegionIntegral (fun x => f j x p))
    (fun p => vectorRegionIntegral (fun x => g x p)) atTop

def zero_volumeType : Prop := ∀ {n m k} {S : Set (E n)} {P : Set (E m)},
  Jordan S → volume S = 0 → ∀ (f : S → P → E k),
  (∀ p, VectorRegionIntegrable (fun x => f x p)) →
  (fun p => vectorRegionIntegral (fun x => f x p)) = (fun _ : P => 0)

def emptyType : Prop := ∀ {n m k} {P : Set (E m)}
  (f : (∅ : Set (E n)) → P → E k),
  (∀ p, VectorRegionIntegrable (fun x => f x p)) ∧
  (fun p => vectorRegionIntegral (fun x => f x p)) = (fun _ : P => 0)
end Specs.D04.C08.ProperContinuity
