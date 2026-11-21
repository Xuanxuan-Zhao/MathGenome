import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Full independent statements for `d04:07:localization`.
Supports are closures of nonzero sets on the actual open subtype domain.
Compactness on that domain implies ambient compactness inside the domain.
The integrals below are the existing Riemann/Darboux open-domain integrals.
The local test-function hypothesis uses functions on V whose supports are
contained in a member of the target cover. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C07.Localization
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model

/-- Finite continuous localization, with arbitrary index type and empty cases. -/
def finite_decompositionType : Prop :=
  ∀ {n : ℕ} {ι : Type} (V K : Set (E n)) (W : ι → Set (E n)),
    IsOpen V → IsCompact K → K ⊆ V → (∀ i, IsOpen (W i)) → K ⊆ ⋃ i, W i →
    ∀ f : V → ℝ, Continuous f → tsupport f ⊆ Subtype.val ⁻¹' K →
    ∃ s : Finset ι, ∃ g : s → V → ℝ,
      (∀ i, Continuous (g i) ∧ HasCompactSupport (g i) ∧
        tsupport (g i) ⊆ Subtype.val ⁻¹' W i) ∧
      ∀ x, f x = ∑ i, g i x

def empty_decompositionType : Prop :=
  ∀ {n : ℕ} (V : Set (E n)) (f : V → ℝ),
    tsupport f ⊆ Subtype.val ⁻¹' (∅ : Set (E n)) →
    ∃ g : Fin 0 → V → ℝ, (∀ i, Continuous (g i) ∧ HasCompactSupport (g i)) ∧
      ∀ x, f x = ∑ i, g i x

/-- Continuous functions with compact support have continuous zero extensions
and genuine open-domain Riemann integrals, including in dimension zero. -/
def compact_support_integrableType : Prop :=
  ∀ {n : ℕ} {V : Set (E n)} (f : V → ℝ), IsOpen V → Continuous f →
    HasCompactSupport f → Continuous (zeroExtension f) ∧ OpenIntegrable f

/-- Finite Riemann linearity on open domains, which need not be bounded or Jordan. -/
def open_integral_sumType : Prop :=
  ∀ {n : ℕ} {V : Set (E n)} {ι : Type} [Fintype ι] (g : ι → V → ℝ),
    IsOpen V → (∀ i, Continuous (g i)) → (∀ i, HasCompactSupport (g i)) →
    OpenIntegrable (fun x => ∑ i, g i x) ∧
      openIntegral (fun x => ∑ i, g i x) = ∑ i, openIntegral (g i)

/-- The purely topological support step used by substitution. -/
def pullback_supportType : Prop :=
  ∀ {n : ℕ} {U V : Set (E n)} (e : U ≃ₜ V) (g : V → ℝ) (W : Set (E n)),
    Continuous g → HasCompactSupport g → tsupport g ⊆ Subtype.val ⁻¹' W →
    Continuous (g ∘ e) ∧ HasCompactSupport (g ∘ e) ∧
      tsupport (g ∘ e) ⊆ {x | (e x : E n) ∈ W} ∧
      IsCompact (Subtype.val '' tsupport (g ∘ e))

/-- Localization of a weighted substitution identity. The homeomorphism and
continuous weight version is stronger than the C¹ specialization below.
The conclusion also records the finite decomposition, compact pullback supports
inside the corresponding source sets, and the actual finite integral sums. -/
def weighted_localizationType : Prop :=
  ∀ {n : ℕ} {ι : Type} {U V : Set (E n)} (e : U ≃ₜ V)
    (J : U → ℝ) (W : ι → Set (E n)),
    IsOpen U → IsOpen V → Continuous J → (∀ i, IsOpen (W i)) → V ⊆ ⋃ i, W i →
    (∀ i (g : V → ℝ), Continuous g → HasCompactSupport g →
      tsupport g ⊆ Subtype.val ⁻¹' W i →
      openIntegral g = openIntegral (fun x => g (e x) * J x)) →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
    OpenIntegrable f ∧ OpenIntegrable (fun x => f (e x) * J x) ∧
    openIntegral f = openIntegral (fun x => f (e x) * J x) ∧
    ∃ s : Finset ι, ∃ g : s → V → ℝ,
      (∀ i, Continuous (g i) ∧ HasCompactSupport (g i) ∧
        tsupport (g i) ⊆ Subtype.val ⁻¹' W i ∧
        HasCompactSupport (g i ∘ e) ∧
        tsupport (g i ∘ e) ⊆ {x | (e x : E n) ∈ W i} ∧
        IsCompact (Subtype.val '' tsupport (g i ∘ e))) ∧
      (∀ x, f x = ∑ i, g i x) ∧
      openIntegral f = ∑ i, openIntegral (g i) ∧
      openIntegral (fun x => f (e x) * J x) =
        ∑ i, openIntegral (fun x => g i (e x) * J x)

/-- For a C¹ diffeomorphism the continuous weight is the absolute determinant
of its actual total derivative. An ambient representative φ agrees with e on U;
its values outside U have no role. No stronger regularity is required. -/
def c1_localizationType : Prop :=
  ∀ {n : ℕ} {ι : Type} {U V : Set (E n)} (e : U ≃ₜ V)
    (φ : E n → E n) (W : ι → Set (E n)),
    IsOpen U → IsOpen V → ContDiffOn ℝ 1 φ U →
    (∀ x : U, φ x = e x) → (∀ i, IsOpen (W i)) → V ⊆ ⋃ i, W i →
    (∀ i (g : V → ℝ), Continuous g → HasCompactSupport g →
      tsupport g ⊆ Subtype.val ⁻¹' W i →
      openIntegral g = openIntegral (fun x : U =>
        g (e x) * |(fderiv ℝ φ x).det|)) →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
      OpenIntegrable f ∧
      OpenIntegrable (fun x : U => f (e x) * |(fderiv ℝ φ x).det|) ∧
      openIntegral f = openIntegral (fun x : U =>
        f (e x) * |(fderiv ℝ φ x).det|)

/-- Restricting a compactly supported function to an open set containing its
support preserves its zero extension and hence its Riemann integral. -/
def open_integral_restrictType : Prop :=
  ∀ {n : ℕ} {V W : Set (E n)} (hWV : W ⊆ V) (f : V → ℝ),
    IsOpen V → IsOpen W → Continuous f → HasCompactSupport f →
    tsupport f ⊆ Subtype.val ⁻¹' W →
    let g : W → ℝ := fun x => f ⟨x, hWV x.property⟩
    Continuous g ∧ HasCompactSupport g ∧ OpenIntegrable g ∧
      zeroExtension g = zeroExtension f ∧ openIntegral g = openIntegral f

/-- The local identities can be given on the actual selected target open sets
and their source preimages. The preceding restriction theorem is the bridge
from these integrals to the full-domain test-function formulation. -/
def c1_localization_on_coverType : Prop :=
  ∀ {n : ℕ} {ι : Type} {U V : Set (E n)} (e : U ≃ₜ V)
    (φ : E n → E n) (W : ι → Set (E n)),
    IsOpen U → IsOpen V → ContDiffOn ℝ 1 φ U →
    (∀ x : U, φ x = e x) → (∀ i, IsOpen (W i)) →
    (∀ i, W i ⊆ V) → V ⊆ ⋃ i, W i →
    (∀ i (g : W i → ℝ), Continuous g → HasCompactSupport g →
      openIntegral g = openIntegral (fun x : (U ∩ φ ⁻¹' W i : Set (E n)) =>
        g ⟨φ x, x.property.2⟩ * |(fderiv ℝ φ x).det|)) →
    ∀ f : V → ℝ, Continuous f → HasCompactSupport f →
      OpenIntegrable f ∧
      OpenIntegrable (fun x : U => f (e x) * |(fderiv ℝ φ x).det|) ∧
      openIntegral f = openIntegral (fun x : U =>
        f (e x) * |(fderiv ℝ φ x).det|)
end Specs.D04.C07.Localization
