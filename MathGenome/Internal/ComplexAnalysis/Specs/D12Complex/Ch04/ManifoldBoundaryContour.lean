import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.ManifoldBoundaryDensity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GreenCirculationAndFlux
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Independent specifications for the manifold boundary dictionary in
paper.tex:1041–1069. The full boundary relation below uses actual signed
integer occurrence counts and the original outward-first orientations.
No integral equality or contour equivalence is assumed for the original cycle.

Seam preimages need not be finite or null: even an entire stationary interval
may map to a seam. It is the velocity on that preimage that vanishes a.e.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators Classical

namespace D12Complex.ManifoldBoundaryContour
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model

/-- The actual geometric input to D04's regular-display theorem in dimension
one. No injectivity on an entire Jordan patch is imposed. -/
abbrev RegularBoundaryDisplay {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) :=
  ManifoldBoundaryDensity.RegularDisplay O M o

/-- Encode each induced sign by its actual integer coefficient. -/
def RegularBoundaryDisplay.patchChain {O M : Set (E 2)}
    {o : PositiveManifoldOrientation 1 1 M} (d : RegularBoundaryDisplay (O := O) o) :
    PatchChain 1 O :=
  ∑ i, Finsupp.single (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
    (if (d.sign i).val = 1 then 1 else -1)

end D12Complex.ManifoldBoundaryContour

namespace Specs.D12Complex.Ch04.ManifoldBoundaryContour
open _root_.D12Complex
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.GeneralizedStokes.Model
open _root_.D12Complex.ManifoldBoundaryContour

def RegularBoundaryDisplay_type :=
  {O M : Set (E 2)} → PositiveManifoldOrientation 1 1 M → Type
def RegularBoundaryDisplay_value : RegularBoundaryDisplay_type := @RegularBoundaryDisplay

def displayPatchChain_type := {O M : Set (E 2)} →
  {o : PositiveManifoldOrientation 1 1 M} → RegularBoundaryDisplay (O := O) o → PatchChain 1 O
def displayPatchChain_value : displayPatchChain_type := @RegularBoundaryDisplay.patchChain

def finite_open_cover_subdivision_type : Prop :=
  ∀ {ι : Type} (γ : PiecewiseC1Path) (U : ι → Set ℂ),
    (∀ i, IsOpen (U i)) → γ.trace ⊆ ⋃ i, U i →
    ∃ (n : ℕ) (node : Fin (n+1) → ℝ) (index : Fin n → ι)
      (arc : Fin n → PiecewiseC1Path),
      Monotone node ∧ node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      (∀ i, (arc i).path.a = node i.castSucc ∧ (arc i).path.b = node i.succ ∧
        EqOn (arc i) γ (Icc (node i.castSucc) (node i.succ)) ∧
        (arc i).trace ⊆ U (index i)) ∧
      ∀ f : ℂ → ℂ, ContinuousOn f γ.trace →
        γ.integral f = ∑ i, (arc i).integral f

def countable_nonzero_derivative_fiber_type : Prop :=
  ∀ (f : ℝ → ℂ) (z : ℂ), {t | f t = z ∧ deriv f t ≠ 0}.Countable

def ae_deriv_zero_on_countable_image_type : Prop :=
  ∀ (f : ℝ → ℂ) (S : Set ℂ), S.Countable →
    ∀ᵐ t ∂(volume : Measure ℝ), f t ∈ S → deriv f t = 0

def planar_boundary_seams_finite_type : Prop :=
  ∀ Z : Seams 2, (∀ i, Z.dim i < 1) → Z.carrier.Finite

def contour_integral_off_countable_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (f : ℂ → ℂ) (S : Set ℂ),
    ContinuousOn f γ.trace → S.Countable →
    γ.integral f = ∫ t in γ.path.a..γ.path.b,
      if γ t ∈ S then 0 else f (γ t) * deriv γ t

def cycle_integral_off_boundary_seams_type : Prop :=
  ∀ (Γ : IntegralCycle) (f : ℂ → ℂ) (Z : Seams 2),
    ContinuousOn f Γ.trace → (∀ i, Z.dim i < 1) →
    Γ.integral f = Γ.chain.sum (fun γ m => (m : ℂ) *
      ∫ t in γ.path.a..γ.path.b,
        if complexCoordinates (γ t) ∈ Z.carrier then 0
        else f (γ t) * deriv γ t)

/-- The pointwise specialization to the actual D04 circulation forms. -/
def patch_complex_coefficient_type : Prop :=
  ∀ {O : Set (E 2)} (C : Patch 1 O) (f : ℂ → ℂ) (u : E 1),
    (coefficient C (circulationForm
      (fun x => (f (complexCoordinates.symm x)).re)
      (fun x => -(f (complexCoordinates.symm x)).im)) u : ℂ) +
    Complex.I * (coefficient C (circulationForm
      (fun x => (f (complexCoordinates.symm x)).im)
      (fun x => (f (complexCoordinates.symm x)).re)) u : ℂ) =
    f (complexCoordinates.symm (C.map u)) *
      complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0))

/-- Arbitrary supplied Jordan displays compare through the actual manifold
integral, rather than through an assumed equivalence with a replacement. -/
def regular_display_has_integral_type : Prop :=
  ∀ {O M : Set (E 2)} (o : PositiveManifoldOrientation 1 1 M),
    IsCompact M → M ⊆ O → ∀ d : RegularBoundaryDisplay (O := O) o,
    ∀ omega : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1,
    Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O omega →
    HasPositiveIntegral o (tangentRestriction 1 1 M omega)
      (patchChainIntegral omega d.patchChain)

def regular_display_independent_type : Prop :=
  ∀ {O M : Set (E 2)} (o : PositiveManifoldOrientation 1 1 M),
    IsCompact M → M ⊆ O → ∀ d e : RegularBoundaryDisplay (O := O) o,
    ∀ omega : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 2 1,
    Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) O omega →
    patchChainIntegral omega d.patchChain = patchChainIntegral omega e.patchChain

def complex_circulation_regular_type : Prop :=
  ∀ (O : Set (E 2)), IsOpen O → ∀ q : ℂ → ℂ,
    ContDiffOn ℝ 1 q (complexCoordinates.symm '' O) →
    Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 1) O
      (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
        (fun x => -(q (complexCoordinates.symm x)).im)) ∧
    Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 1) O
      (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
        (fun x => (q (complexCoordinates.symm x)).re))

def regular_display_complex_independent_type : Prop :=
  ∀ {O M : Set (E 2)} (o : PositiveManifoldOrientation 1 1 M),
    IsOpen O → IsCompact M → M ⊆ O →
    ∀ (d e : RegularBoundaryDisplay (O := O) o) (q : ℂ → ℂ),
    ContDiffOn ℝ 1 q (complexCoordinates.symm '' O) →
    (patchChainIntegral
      (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
        (fun x => -(q (complexCoordinates.symm x)).im)) d.patchChain : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) d.patchChain : ℂ) =
    (patchChainIntegral
      (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
        (fun x => -(q (complexCoordinates.symm x)).im)) e.patchChain : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) e.patchChain : ℂ)

open Specs.D04.C13.NormalizedFormsAndWedge.Model

def patch_complex_integral_type : Prop :=
  ∀ {O : Set (E 2)} (hO : IsOpen O)
    (C : Patch 1 O) (q : ℂ → ℂ)
    (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)),
    Integrable (fun u => if u ∈ C.region then
      q (complexCoordinates.symm (C.map u)) *
        complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0)) else 0) ∧
    (patchIntegral C (fun _ => 1)
      (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
        (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
    Complex.I * (patchIntegral C (fun _ => 1)
      (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
        (fun x => (q (complexCoordinates.symm x)).re)) : ℂ) =
    ∫ u, if u ∈ C.region then
      q (complexCoordinates.symm (C.map u)) *
        complexCoordinates.symm (fderiv ℝ C.map u (standardBasis 1 0)) else 0

def interval_patch_contour_type : Prop :=
  ∀ {O : Set (E 2)} (hO : IsOpen O)
    (C : Patch 1 O) (γ : PiecewiseC1Path)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr ''
      Icc γ.path.a γ.path.b)
    (hmap : ∀ t ∈ Icc γ.path.a γ.path.b,
      complexCoordinates.symm (C.map ((OrthonormalBasis.singleton (Fin 1) ℝ).repr t)) = γ t)
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)),
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ)

def chart_inverse_contDiffOn_type : Prop :=
  ∀ {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    {S : Set ℝ} (f : ℝ → ℂ) (hf : ContDiffOn ℝ 1 f S)
    (hmaps : MapsTo (fun t => complexCoordinates (f t)) S (M ∩ c.ambient)),
    ContDiffOn ℝ 1 (fun t => c.invFun (complexCoordinates (f t))) S

def chart_parameter_piecewiseC1_type : Prop :=
  ∀ {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient)),
    ∃ (n : ℕ) (node : Fin (n+1) → ℝ), StrictMono node ∧
      node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      ∀ i : Fin n, ContDiffOn ℝ 1
        (fun t => (c.invFun (complexCoordinates (γ t))) 0)
        (Icc (node i.castSucc) (node i.succ))

def monotoneOn_finite_partition_type : Prop :=
  ∀ (f : ℝ → ℝ),
    ∀ (n : ℕ) (node : Fin (n+1) → ℝ), Monotone node →
      (∀ i : Fin n, MonotoneOn f (Icc (node i.castSucc) (node i.succ))) →
      MonotoneOn f (Icc (node 0) (node (Fin.last n)))

def piecewiseC1_monotone_of_deriv_nonneg_type : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ)
    (node : Fin (n+1) → ℝ) (hm : Monotone node)
    (hf : ∀ i : Fin n, ContDiffOn ℝ 1 f (Icc (node i.castSucc) (node i.succ)))
    (hn : ∀ i : Fin n, ∀ t ∈ Ioo (node i.castSucc) (node i.succ), 0 ≤ deriv f t),
    MonotoneOn f (Icc (node 0) (node (Fin.last n)))

def chart_parameter_monotone_type : Prop :=
  ∀ {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hnonneg : ∀ t ∈ Ioo γ.path.a γ.path.b,
      0 ≤ deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t),
    MonotoneOn (fun s => (c.invFun (complexCoordinates (γ s))) 0)
      (Icc γ.path.a γ.path.b)

def chart_interval_patch_contour_type : Prop :=
  ∀ {O M : Set (E 2)} (hO : IsOpen O)
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (C : Patch 1 O) (a b : ℝ) (hab : a ≤ b)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr '' Icc a b)
    (hchart : EqOn C.map c.toFun C.region)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hstart : (c.invFun (complexCoordinates (γ γ.path.a))) 0 = a)
    (hend : (c.invFun (complexCoordinates (γ γ.path.b))) 0 = b)
    (hnonneg : ∀ t ∈ Ioo γ.path.a γ.path.b,
      0 ≤ deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t)
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)),
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ)

def boundary_occurrence_cancellation_type : Prop :=
  ∀ {r l p : ℕ} {O : Set (E 2)}
    (B : Fin r → Set (E 2))
    (o : (j : Fin r) → PositiveManifoldOrientation 1 1 (B j))
    (d : (j : Fin r) → RegularBoundaryDisplay (O := O) (o j))
    (a : Fin r → ℤ)
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin r) × Fin (d j).count))
    (Q : Fin l → Patch 1 O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
    (deltaOut : Fin l → ℝ) (hdOut : ∀ t, deltaOut t = 1 ∨ deltaOut t = -1)
    (hOut : (t : Fin l) → LocalReparametrization
      ((d (e (Sum.inl t)).1).patch (e (Sum.inl t)).2).region (Q t).region (deltaOut t))
    (houter : ∀ t,
      EqOn ((d (e (Sum.inl t)).1).patch (e (Sum.inl t)).2).map
        ((Q t).map ∘ (hOut t).map)
        ((d (e (Sum.inl t)).1).patch (e (Sum.inl t)).2).region ∧
      ((d (e (Sum.inl t)).1).sign (e (Sum.inl t)).2).val * deltaOut t = (tSign t).val ∧
      b t = a (e (Sum.inl t)).1)
    (deltaPair : Fin p → ℝ) (hdPair : ∀ i, deltaPair i = 1 ∨ deltaPair i = -1)
    (hPair : (i : Fin p) → LocalReparametrization
      ((d (e (Sum.inr (i,false))).1).patch (e (Sum.inr (i,false))).2).region
      ((d (e (Sum.inr (i,true))).1).patch (e (Sum.inr (i,true))).2).region (deltaPair i))
    (hpair : ∀ i,
      EqOn ((d (e (Sum.inr (i,false))).1).patch (e (Sum.inr (i,false))).2).map
        (((d (e (Sum.inr (i,true))).1).patch (e (Sum.inr (i,true))).2).map ∘ (hPair i).map)
        ((d (e (Sum.inr (i,false))).1).patch (e (Sum.inr (i,false))).2).region ∧
      ((d (e (Sum.inr (i,false))).1).sign (e (Sum.inr (i,false))).2).val * deltaPair i =
        -((d (e (Sum.inr (i,true))).1).sign (e (Sum.inr (i,true))).2).val ∧
      a (e (Sum.inr (i,false))).1 = a (e (Sum.inr (i,true))).1)
    (omega : FormField 2 1) (ho : IsCrForm (some 0) O omega),
    (∑ j, a j • patchChainIntegral omega (d j).patchChain) =
      ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) omega)

def continuous_substitution_piece_type : Prop :=
  ∀ {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : ContDiffOn ℝ 1 φ (Icc a b)) {g : ℝ → ℂ}
    (hg : ContinuousOn g (φ '' Icc a b)),
    IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume a b ∧
      (∫ t in a..b, deriv φ t • g (φ t)) = ∫ s in φ a..φ b, g s

def continuous_substitution_partition_type : Prop :=
  ∀ (φ : ℝ → ℝ) {a b : ℝ} (_hab : a ≤ b)
    (hc : ContinuousOn φ (Icc a b)) (n : ℕ) (node : Fin (n+1) → ℝ)
    (hm : Monotone node) (hfirst : node 0 = a) (hlast : node (Fin.last n) = b)
    (hs : ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
    (g : ℝ → ℂ) (hg : ContinuousOn g (φ '' Icc a b)),
    IntervalIntegrable (fun t => deriv φ t • g (φ t)) volume a b ∧
      (∫ t in a..b, deriv φ t • g (φ t)) = ∫ s in φ a..φ b, g s

def local_coordinate_endpoint_integral_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (U : Set ℝ) (hU : IsOpen U)
    (ψ : ℝ → ℂ) (hψ : ContDiffOn ℝ 1 ψ U)
    (φ : ℝ → ℝ) (hc : ContinuousOn φ (Icc γ.path.a γ.path.b))
    (hmaps : MapsTo φ (Icc γ.path.a γ.path.b) U)
    (n : ℕ) (node : Fin (n+1) → ℝ) (hm : Monotone node)
    (hfirst : node 0 = γ.path.a) (hlast : node (Fin.last n) = γ.path.b)
    (hs : ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
    (heq : ∀ t ∈ Icc γ.path.a γ.path.b, γ t = ψ (φ t))
    (q : ℂ → ℂ) (hq : ContinuousOn q (ψ '' U)),
    γ.integral q = ∫ s in φ γ.path.a..φ γ.path.b, q (ψ s) * deriv ψ s

def interval_patch_parameter_contour_type : Prop :=
  ∀ {O : Set (E 2)} (hO : IsOpen O)
    (C : Patch 1 O) (a b : ℝ) (hab : a ≤ b)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr '' Icc a b)
    (γ : PiecewiseC1Path) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Icc γ.path.a γ.path.b))
    (hmaps : MapsTo φ (Icc γ.path.a γ.path.b) (Icc a b))
    (hstart : φ γ.path.a = a) (hend : φ γ.path.b = b)
    (n : ℕ) (node : Fin (n+1) → ℝ) (hm : Monotone node)
    (hfirst : node 0 = γ.path.a) (hlast : node (Fin.last n) = γ.path.b)
    (hs : ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
    (heq : ∀ t ∈ Icc γ.path.a γ.path.b,
      γ t = complexCoordinates.symm
        (C.map ((OrthonormalBasis.singleton (Fin 1) ℝ).repr (φ t))))
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)),
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ)

def chart_interval_patch_contour_unordered_type : Prop :=
  ∀ {O M : Set (E 2)} (hO : IsOpen O)
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (C : Patch 1 O) (a b : ℝ) (hab : a ≤ b)
    (hregion : C.region = (OrthonormalBasis.singleton (Fin 1) ℝ).repr '' Icc a b)
    (hchart : EqOn C.map c.toFun C.region)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hcoordinate : ∀ t ∈ Icc γ.path.a γ.path.b,
      (c.invFun (complexCoordinates (γ t))) 0 ∈ Icc a b)
    (hstart : (c.invFun (complexCoordinates (γ γ.path.a))) 0 = a)
    (hend : (c.invFun (complexCoordinates (γ γ.path.b))) 0 = b)
    (q : ℂ → ℂ) (hq : ContDiffOn ℝ 1 q (complexCoordinates.symm '' O)),
    γ.integral q =
      (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).re)
          (fun x => -(q (complexCoordinates.symm x)).im)) : ℂ) +
      Complex.I * (patchIntegral C (fun _ => 1)
        (circulationForm (fun x => (q (complexCoordinates.symm x)).im)
          (fun x => (q (complexCoordinates.symm x)).re)) : ℂ)

def manifold_chart_subdivision_type : Prop :=
  ∀ {M : Set (E 2)}
    (hM : Specs.D04.C14.EmbeddedManifoldCharts.Model.IsEmbeddedManifold 1 1 M)
    (γ : PiecewiseC1Path) (htrace : complexCoordinates '' γ.trace ⊆ M),
    ∃ (n : ℕ) (node : Fin (n+1) → ℝ)
      (chart : Fin n → Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
      (arc : Fin n → PiecewiseC1Path),
      Monotone node ∧ node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      (∀ i, (arc i).path.a = node i.castSucc ∧ (arc i).path.b = node i.succ ∧
        EqOn (arc i) γ (Icc (node i.castSucc) (node i.succ)) ∧
        MapsTo (fun t => complexCoordinates (arc i t))
          (Icc (arc i).path.a (arc i).path.b) (M ∩ (chart i).ambient) ∧
        ∃ (k : ℕ) (v : Fin (k+1) → ℝ), StrictMono v ∧
          v 0 = (arc i).path.a ∧ v (Fin.last k) = (arc i).path.b ∧
          ∀ j : Fin k, ContDiffOn ℝ 1
            (fun t => ((chart i).invFun (complexCoordinates (arc i t))) 0)
            (Icc (v j.castSucc) (v j.succ))) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q γ.trace →
        γ.integral q = ∑ i, (arc i).integral q

def chart_coordinate_velocity_type : Prop :=
  ∀ {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    {t : ℝ} (ht : t ∈ Ioo γ.path.a γ.path.b)
    (hd : DifferentiableAt ℝ γ t),
    complexCoordinates (deriv γ t) =
      Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
        (c.invFun (complexCoordinates (γ t)))
        (deriv (fun s => (c.invFun (complexCoordinates (γ s))) 0) t • standardBasis 1 0)

def chart_parameter_monotone_of_tangent_ray_type : Prop :=
  ∀ {M : Set (E 2)}
    (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2 M)
    (γ : PiecewiseC1Path)
    (hmaps : MapsTo (fun t => complexCoordinates (γ t))
      (Icc γ.path.a γ.path.b) (M ∩ c.ambient))
    (hray : ∀ i : Fin γ.partition.count,
      ∀ t ∈ Ioo (γ.partition.node i.castSucc) (γ.partition.node i.succ),
      ∃ r : ℝ, 0 ≤ r ∧ complexCoordinates (deriv γ t) =
        r • Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
          (c.invFun (complexCoordinates (γ t))) (standardBasis 1 0)),
    MonotoneOn (fun s => (c.invFun (complexCoordinates (γ s))) 0)
      (Icc γ.path.a γ.path.b)

end Specs.D12Complex.Ch04.ManifoldBoundaryContour


namespace D12Complex.ManifoldBoundaryContour
open Specs.D04.C01.EuclideanInterfaces.Model
open ManifoldBoundaryDensity SignedCurveMultiplicity

/-- The integer number of occurrences in direction `v`, minus those in the
opposite direction. This counts original parameters, with their original
integer coefficients. It makes no assertion about any integral. -/
def signedIncidence {α : Type} (weight : α → ℤ) (direction : α → ℂ) (v : ℂ) : ℤ :=
  (∑' i, if direction i = v then weight i else 0) -
    ∑' i, if direction i = -v then weight i else 0

/-- All nonstationary occurrences in the original canonical cycle. Endpoints
are omitted only because they are a finite null set of image points. -/
def CycleOccurrence (Γ : IntegralCycle) (z : ℂ) : Type :=
  (γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}) ×
    regularFiber γ.val (Ioo γ.val.path.a γ.val.path.b) z

def cycleOccurrenceWeight (Γ : IntegralCycle) (z : ℂ) (i : CycleOccurrence Γ z) : ℤ :=
  Γ.chain i.1.val

def cycleOccurrenceDirection (Γ : IntegralCycle) (z : ℂ) (i : CycleOccurrence Γ z) : ℂ :=
  unitVelocity i.1.val i.2.val

/-- Actual unpaired occurrences of the ORIGINAL regular Jordan displays in
D04's supplied enumeration, before its outer reparametrizations. -/
def OuterOccurrence {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) (z : ℂ) : Type :=
  (t : Fin l) × regularFiber
    (patchCurve ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2))
    (patchParameters ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2)) z

def outerOccurrenceWeight {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) (i : OuterOccurrence A z) : ℤ :=
  pointSignInt ((A.display (A.enumerate (Sum.inl i.1)).1).sign (A.enumerate (Sum.inl i.1)).2)

def outerOccurrenceDirection {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) (i : OuterOccurrence A z) : ℂ :=
  unitVelocity
    (patchCurve ((A.display (A.enumerate (Sum.inl i.1)).1).patch (A.enumerate (Sum.inl i.1)).2)) i.2.val

/-- Closed geometric outer traces, with no interval normalization of any patch. -/
def outerTrace {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) : Set ℂ :=
  ⋃ t : Fin l, complexCoordinates.symm ''
    (((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2).map ''
      closure ((A.display (A.enumerate (Sum.inl t)).1).patch (A.enumerate (Sum.inl t)).2).region)

def assemblySeams {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) : Set ℂ :=
  complexCoordinates.symm '' (⋃ j, (A.display j).seams.carrier)

/-- The full positive boundary relation is geometric. Its multiplicity is the
actual signed integer count in each unoriented tangent line, with the signs
induced by the supplied outward-first orientations. Negative coefficients and
reversed traversals are accounted for together; cancelling traversals are
allowed. The a.e. clause ignores only geometric length-null exceptional sets,
not stationary parameter intervals. There is no contour comparison or assumed
integral identity. The cycle and all of its parameter intervals are unchanged.

The assembly supplies exactly the geometric Green data. The trace is supported
on its compact carrier and agrees with its outer trace off its finite seams.
Direction counts use the original unpaired displays, never a replacement path.
-/
structure FullPositiveBoundary {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) : Prop where
  carrier : Γ.trace ⊆ complexCoordinates.symm '' (⋃ j, (A.piece j).carrier)
  trace : Γ.trace \ assemblySeams A = outerTrace A \ assemblySeams A
  incidence : ∀ᵐ z ∂(μH[1] : Measure ℂ), ∀ v : ℂ,
    signedIncidence (cycleOccurrenceWeight Γ z) (cycleOccurrenceDirection Γ z) v =
      signedIncidence (outerOccurrenceWeight A z) (outerOccurrenceDirection A z) v

end D12Complex.ManifoldBoundaryContour


namespace Specs.D12Complex.Ch04.ManifoldBoundaryContour
open _root_.D12Complex _root_.D12Complex.ManifoldBoundaryContour
open _root_.D12Complex.ManifoldBoundaryDensity _root_.D12Complex.SignedCurveMultiplicity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

def signedIncidence_type :=
  ∀ {α : Type} (weight : α → ℤ) (direction : α → ℂ) (v : ℂ),
    ℤ
def signedIncidence_value : signedIncidence_type := @_root_.D12Complex.ManifoldBoundaryContour.signedIncidence

def CycleOccurrence_type :=
  ∀ (Γ : IntegralCycle) (z : ℂ),
    Type
def CycleOccurrence_value : CycleOccurrence_type := @_root_.D12Complex.ManifoldBoundaryContour.CycleOccurrence

def cycleOccurrenceWeight_type :=
  ∀ (Γ : IntegralCycle) (z : ℂ) (i : CycleOccurrence Γ z),
    ℤ
def cycleOccurrenceWeight_value : cycleOccurrenceWeight_type := @_root_.D12Complex.ManifoldBoundaryContour.cycleOccurrenceWeight

def cycleOccurrenceDirection_type :=
  ∀ (Γ : IntegralCycle) (z : ℂ) (i : CycleOccurrence Γ z),
    ℂ
def cycleOccurrenceDirection_value : cycleOccurrenceDirection_type := @_root_.D12Complex.ManifoldBoundaryContour.cycleOccurrenceDirection

def OuterOccurrence_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O) (z : ℂ),
    Type
def OuterOccurrence_value : OuterOccurrence_type := @_root_.D12Complex.ManifoldBoundaryContour.OuterOccurrence

def outerOccurrenceWeight_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) (i : OuterOccurrence A z),
    ℤ
def outerOccurrenceWeight_value : outerOccurrenceWeight_type := @_root_.D12Complex.ManifoldBoundaryContour.outerOccurrenceWeight

def outerOccurrenceDirection_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) (i : OuterOccurrence A z),
    ℂ
def outerOccurrenceDirection_value : outerOccurrenceDirection_type := @_root_.D12Complex.ManifoldBoundaryContour.outerOccurrenceDirection

def outerTrace_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    Set ℂ
def outerTrace_value : outerTrace_type := @_root_.D12Complex.ManifoldBoundaryContour.outerTrace

def assemblySeams_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)} (A : PlanarAssembly q l p O),
    Set ℂ
def assemblySeams_value : assemblySeams_type := @_root_.D12Complex.ManifoldBoundaryContour.assemblySeams

def FullPositiveBoundary_type :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle),
    Prop
def FullPositiveBoundary_value : FullPositiveBoundary_type := @_root_.D12Complex.ManifoldBoundaryContour.FullPositiveBoundary

def signedIncidence_moment_type : Prop :=
  ∀ {α : Type} [Fintype α]
    (c : α → ℤ) (d : α → ℂ) (S : Finset ℂ)
    (hpos : ∀ i, d i ∈ S) (hneg : ∀ i, -d i ∈ S),
    (∑ v ∈ S, (signedIncidence c d v : ℂ) * v) =
      2 * ∑ i, (c i : ℂ) * d i

def signedIncidence_vector_type : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β]
    (c : α → ℤ) (d : α → ℂ) (b : β → ℤ) (e : β → ℂ)
    (h : ∀ v, signedIncidence c d v = signedIncidence b e v),
    (∑ i, (c i : ℂ) * d i) = ∑ j, (b j : ℂ) * e j

def cycle_occurrences_finite_type : Prop :=
  ∀ (Γ : IntegralCycle),
    ∀ᵐ z ∂(μH[1] : Measure ℂ), Finite (CycleOccurrence Γ z)

def assembly_seams_finite_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O),
    (assemblySeams A).Finite

def outer_occurrences_finite_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O),
    ∀ᵐ z ∂(μH[1] : Measure ℂ), Finite (OuterOccurrence A z)

def cycle_occurrence_vector_type : Prop :=
  ∀ (Γ : IntegralCycle) (z : ℂ)
    [Finite (CycleOccurrence Γ z)],
    (∑' i : CycleOccurrence Γ z,
      (cycleOccurrenceWeight Γ z i : ℂ) * cycleOccurrenceDirection Γ z i) =
      chainDensity Γ.chain z

def outer_occurrence_vector_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) [Finite (OuterOccurrence A z)],
    (∑' i : OuterOccurrence A z,
      (outerOccurrenceWeight A z i : ℂ) * outerOccurrenceDirection A z i) =
      geometricOuterDensity A z

def full_positive_boundary_density_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ),
    chainDensity Γ.chain =ᵐ[μH[1]] geometricOuterDensity A

def full_positive_boundary_contour_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier))),
    Γ.integral f =
      (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).re)
          (fun x => -(f (complexCoordinates.symm x)).im)) (outerPatchChain A) : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).im)
          (fun x => (f (complexCoordinates.symm x)).re)) (outerPatchChain A) : ℂ)

def full_positive_boundary_contour_c1_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ)
    (U : Set ℂ) (f : ℂ → ℂ) (_hU : IsOpen U)
    (hKU : complexCoordinates.symm '' (⋃ j, (A.piece j).carrier) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U),
    Γ.integral f =
      (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).re)
          (fun x => -(f (complexCoordinates.symm x)).im)) (outerPatchChain A) : ℂ) +
      Complex.I * (patchChainIntegral
        (circulationForm (fun x => (f (complexCoordinates.symm x)).im)
          (fun x => (f (complexCoordinates.symm x)).re)) (outerPatchChain A) : ℂ)

def full_positive_boundary_display_sum_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle) (hΓ : FullPositiveBoundary A Γ)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (complexCoordinates.symm '' (⋃ j, (A.piece j).carrier))),
    Γ.integral f = ∑ j, ∑ t, (((A.display j).sign t).val : ℂ) *
      complexPatchIntegral ((A.display j).patch t) f

def outer_occurrence_orientation_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (z : ℂ) (i : OuterOccurrence A z)
    (hi : scalarCoordinates i.2.val ∈ interior
      ((A.display (A.enumerate (Sum.inl i.1)).1).patch (A.enumerate (Sum.inl i.1)).2).region),
    let j := (A.enumerate (Sum.inl i.1)).1
    let t := (A.enumerate (Sum.inl i.1)).2
    ∃ (c : Specs.D04.C14.EmbeddedManifoldCharts.Model.EmbeddedChart 1 1 2
        (Specs.D04.C14.EmbeddedManifoldCharts.Model.intrinsicBoundary 1 2 (A.piece j).carrier))
      (hu : scalarCoordinates i.2.val ∈ c.source),
      ((A.display j).patch t).map (scalarCoordinates i.2.val) = c.toFun (scalarCoordinates i.2.val) ∧
      Specs.D04.C14.OrientationsAndChartSigns.Model.chartSign
        (A.boundaryOrientation j).atPoint c (scalarCoordinates i.2.val) hu = ((A.display j).sign t).val ∧
      (outerOccurrenceWeight A z i : ℂ) * outerOccurrenceDirection A z i =
        complexCoordinates.symm
          ((((A.display j).sign t).val /
            ‖Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
              (scalarCoordinates i.2.val) (standardBasis 1 0)‖) •
            Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
              (scalarCoordinates i.2.val) (standardBasis 1 0)) ∧
      0 < ((A.boundaryOrientation j).atPoint (c.toFun (scalarCoordinates i.2.val))
        (c.map_source hu).1).someVector
          (fun a => (((A.display j).sign t).val /
            ‖Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential c
              (scalarCoordinates i.2.val) (standardBasis 1 0)‖) •
            Specs.D04.C14.OrientationsAndChartSigns.Model.tangentChartMap c
              (scalarCoordinates i.2.val) hu (standardBasis 1 a))

end Specs.D12Complex.Ch04.ManifoldBoundaryContour
