import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.AreaIntegral
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RegionSubstitution
import Mathlib.Topology.Order.IntermediateValue

/-! Independent propositions for paper.tex d04:10:reparametrize.
The common objects are the upstream Gram density and Darboux region integral.
An OpenPartialHomeomorph with C¹ forward and inverse maps records a genuine
C¹ diffeomorphism on its open source and target. The patch may be noninjective.
Fields are evaluated only on the common image: image_data_extensionType
records the relative-data bridge, including continuity and boundedness.
Sign hypotheses for flux are only on the region under consideration;
component_signType and flux_componentType handle disconnected domains.
-/
noncomputable section
open Set Function Topology
open scoped RealInnerProductSpace Matrix
namespace Specs.D04.C10.Reparametrization
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C10.PatchGeometryGram.Model
open Specs.D04.C10.AreaIntegral.Model
open Specs.D04.C06.JordanRegions.Model

def regular_compType : Prop :=
  ∀ {k n : ℕ} {U : Set (E k)} {φ : E k → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U),
    RegularPatch e.source (φ ∘ e)

def patchGram_compType : Prop :=
  ∀ {k n : ℕ} {U : Set (E k)} {φ : E k → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hU : e.target ⊆ U)
    {x : E k} (hx : x ∈ e.source),
    patchGram (φ ∘ e) x = (matrixOfLinearMap (fderiv ℝ e x).toLinearMap).transpose *
      patchGram φ (e x) * matrixOfLinearMap (fderiv ℝ e x).toLinearMap

def patchJacobian_compType : Prop :=
  ∀ {k n : ℕ} {U : Set (E k)} {φ : E k → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hU : e.target ⊆ U)
    {x : E k} (hx : x ∈ e.source),
    patchJacobian (φ ∘ e) x = |(fderiv ℝ e x).det| * patchJacobian φ (e x)

def areaVector_compType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hU : e.target ⊆ U)
    {x : E 2} (hx : x ∈ e.source),
    areaVector (φ ∘ e) x = (fderiv ℝ e x).det • areaVector φ (e x)

def jordan_imageType : Prop :=
  ∀ (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S) (hSU : S ⊆ e.source),
    IsCompact (e '' S) ∧ Jordan (e '' S)

def area_substitution_boundedType : Prop :=
  ∀ {n : ℕ} {U : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (f : E n → ℝ)
    (hb : RegionBounded (fun y : φ '' (e '' S) => f y)),
    (AreaIntegrable S (φ ∘ e) (fun y => f y) ↔
      AreaIntegrable (e '' S) φ (fun y => f y)) ∧
    ((AreaIntegrable S (φ ∘ e) (fun y => f y) ∨
      AreaIntegrable (e '' S) φ (fun y => f y)) →
      areaIntegral S (φ ∘ e) (fun y => f y) =
        areaIntegral (e '' S) φ (fun y => f y))

def area_substitutionType : Prop :=
  ∀ {n : ℕ} {U : Set (E 2)} {φ : E 2 → E n}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (f : E n → ℝ) (hf : ContinuousOn f (φ '' (e '' S))),
    AreaIntegrable S (φ ∘ e) (fun y => f y) ∧
    AreaIntegrable (e '' S) φ (fun y => f y) ∧
    areaIntegral S (φ ∘ e) (fun y => f y) = areaIntegral (e '' S) φ (fun y => f y)

def determinant_sign_on_connectedType : Prop :=
  ∀ {k : ℕ} (e : OpenPartialHomeomorph (E k) (E k))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {C : Set (E k)} (hC : IsPreconnected C) (hCU : C ⊆ e.source),
    (∀ x ∈ C, 0 < (fderiv ℝ e x).det) ∨ (∀ x ∈ C, (fderiv ℝ e x).det < 0)

def flux_substitution_boundedType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3)
    (hb : RegionBounded (fun y : φ '' (e '' S) => F y))
    (c : ℝ) (hc : c = 1 ∨ c = -1)
    (hsgn : ∀ x ∈ S, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|),
    (FluxIntegrable S (φ ∘ e) (fun y => F y) ↔
      FluxIntegrable (e '' S) φ (fun y => F y)) ∧
    ((FluxIntegrable S (φ ∘ e) (fun y => F y) ∨
      FluxIntegrable (e '' S) φ (fun y => F y)) →
      fluxIntegral S (φ ∘ e) (fun y => F y) =
        c * fluxIntegral (e '' S) φ (fun y => F y))

def flux_substitutionType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S)))
    (c : ℝ) (hc : c = 1 ∨ c = -1)
    (hsgn : ∀ x ∈ S, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|),
    FluxIntegrable S (φ ∘ e) (fun y => F y) ∧
    FluxIntegrable (e '' S) φ (fun y => F y) ∧
    fluxIntegral S (φ ∘ e) (fun y => F y) =
      c * fluxIntegral (e '' S) φ (fun y => F y)

def normal_chart_signsType : Prop :=
  ∀ {U S : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (hSU : S ⊆ U) (F N : E 3 → E 3)
    (hN : ∀ x ∈ S, IsUnitNormal (tangentPlane φ x) (N (φ x))),
    ∃ σ : S → ℝ, (∀ x, σ x = 1 ∨ σ x = -1) ∧
      (∀ x : S, N (φ x) = σ x • unitNormal φ x) ∧
      normalFluxIntegral S φ (fun y => F y) (N ∘ φ) =
        regionIntegral (fun x : S => σ x * fluxIntegrand S φ (fun y => F y) x)

def fixed_normal_fluxType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F N : E 3 → E 3)
    (hF : ContinuousOn F (φ '' (e '' S))) (hN : ContinuousOn N (φ '' (e '' S))),
    RegionIntegrable (fun x : S =>
      ⟪F (φ (e x)), N (φ (e x))⟫ * patchJacobian (φ ∘ e) x) ∧
    RegionIntegrable (fun x : e '' S =>
      ⟪F (φ x), N (φ x)⟫ * patchJacobian φ x) ∧
    normalFluxIntegral S (φ ∘ e) (fun y => F y) (N ∘ (φ ∘ e)) =
      normalFluxIntegral (e '' S) φ (fun y => F y) (N ∘ φ)

def unitNormal_compType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {x : E 2} (hx : x ∈ e.source)
    (c : ℝ) (hsgn : (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|),
    unitNormal (φ ∘ e) x = c • unitNormal φ (e x)

def chart_sign_compType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {x : E 2} (hx : x ∈ e.source)
    (c σ : ℝ) (hc : c = 1 ∨ c = -1)
    (hsgn : (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|)
    (v : E 3) (hv : v = σ • unitNormal φ (e x)),
    v = (σ * c) • unitNormal (φ ∘ e) x

def component_signType : Prop :=
  ∀ (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    {C : Set (E 2)} (hC : IsPreconnected C) (hCU : C ⊆ e.source),
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
      ∀ x ∈ C, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|

def image_data_extensionType : Prop :=
  ∀ {n : ℕ} {A : Set (E n)} {V : Type} [NormedAddCommGroup V]
    (f : A → V),
    (∀ x : A, zeroExtension f x = f x) ∧
    (Continuous f ↔ ContinuousOn (zeroExtension f) A) ∧
    (RegionBounded f ↔ RegionBounded (fun x : A => zeroExtension f x))

def flux_preservingType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S)))
    (hpos : ∀ x ∈ S, 0 < (fderiv ℝ e x).det),
    fluxIntegral S (φ ∘ e) (fun y => F y) = fluxIntegral (e '' S) φ (fun y => F y)

def flux_reversingType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S)
    (hSU : S ⊆ e.source) (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S)))
    (hneg : ∀ x ∈ S, (fderiv ℝ e x).det < 0),
    fluxIntegral S (φ ∘ e) (fun y => F y) = -fluxIntegral (e '' S) φ (fun y => F y)

def flux_componentType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}
    (hφ : RegularPatch U φ) (e : OpenPartialHomeomorph (E 2) (E 2))
    (he : ContDiffOn ℝ 1 e e.source) (hei : ContDiffOn ℝ 1 e.symm e.target)
    (hU : e.target ⊆ U) {C : Set (E 2)} (hC : IsPreconnected C) (hCU : C ⊆ e.source)
    {S : Set (E 2)} (hS : IsCompact S) (hJ : Jordan S) (hSC : S ⊆ C)
    (F : E 3 → E 3) (hF : ContinuousOn F (φ '' (e '' S))),
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
      (∀ x ∈ C, (fderiv ℝ e x).det = c * |(fderiv ℝ e x).det|) ∧
      FluxIntegrable S (φ ∘ e) (fun y => F y) ∧
      FluxIntegrable (e '' S) φ (fun y => F y) ∧
      fluxIntegral S (φ ∘ e) (fun y => F y) =
        c * fluxIntegral (e '' S) φ (fun y => F y)

end Specs.D04.C10.Reparametrization
