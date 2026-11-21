import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.GeneralizedStokes
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.LowerDimensionalImagesHaveZeroContent
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteManifoldBoundaryAssembly
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.FiniteGeometricUnionIntegral

/-! Finite piecewise Stokes for cells and compact oriented manifolds.
The geometric interfaces reuse the canonical upstream Jordan patches,
separately local parameter diffeomorphisms, manifold boundary displays and
decomposition-independent geometric union integral. No integral cancellation
or decomposition identity is assumed as geometric data. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Classical
namespace Specs.D04.C15.FinitePiecewiseStokes
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
namespace Model

/-- A C¹ change of cube parameters, defined on open neighborhoods. The
cell itself is still the upstream cell (no chosen extension is added to it).
The sign permits equality with opposite formal coefficients in degree zero,
where a negative determinant cannot occur. -/
structure CubeReparametrization {k n : ℕ} {O : Set (E n)}
    (c d : Cell 1 k O) (s : ℤ) where
  change : OpenPartialHomeomorph (E k) (E k)
  regular : ContDiffOn ℝ 1 change change.source
  inverse_regular : ContDiffOn ℝ 1 change.symm change.target
  domain : cube k ⊆ change.source
  image : change '' cube k = cube k
  unit_sign : s = 1 ∨ s = -1
  sign : ∀ x ∈ cube k, Real.sign ((fderiv ℝ change x).det) = (s : ℝ)
  agrees : ∀ x : cube k, (c.toFun x).val =
    (d.toFun ⟨change x, image.subset (mem_image_of_mem change x.property)⟩).val

/-- Opposite geometric orientations on the same embedded piece. In degree
zero this compares the independent point signs, not empty ordered bases. -/
def oppositeOrientation {r : ℕ∞ω} {n : ℕ} {M : Set (E n)} :
    (k : ℕ) → ManifoldOrientation r k M → ManifoldOrientation r k M → Prop
  | 0, o, p => ∀ x, (p x).val = -(o x).val
  | _+1, o, p => p.atPoint = fun x hx => -o.atPoint x hx

/-- An actual C¹ change of parameters for a subpiece of a cell. Its image
may be a proper subset of the parent's cube. Injectivity is required only
of the parameter change, never of the parent cell. -/
structure CubeParameterPiece {k n : ℕ} {O : Set (E n)}
    (c d : Cell 1 k O) (s : ℤ) where
  change : OpenPartialHomeomorph (E k) (E k)
  regular : ContDiffOn ℝ 1 change change.source
  inverse_regular : ContDiffOn ℝ 1 change.symm change.target
  domain : cube k ⊆ change.source
  range_subset : change '' cube k ⊆ cube k
  unit_sign : s = 1 ∨ s = -1
  sign : ∀ x ∈ cube k, Real.sign ((fderiv ℝ change x).det) = (s : ℝ)
  agrees : ∀ x : cube k, (d.toFun x).val =
    cellExtension c (change x)

/-- Finite geometric changes of a formal chain. Every generator is either
an explicit parameter diffeomorphism or an explicit subdivision; there is
no assumed equation of integrals in this relation. The parameter V records
where the ambient form will be defined. -/
inductive CellAssembly {k n : ℕ} {O : Set (E n)} (V : Set (E n)) :
    Chain 1 k O → Chain 1 k O → Prop
  | refl (C) : CellAssembly V C C
  | symm {C D} : CellAssembly V C D → CellAssembly V D C
  | trans {C D F} : CellAssembly V C D → CellAssembly V D F → CellAssembly V C F
  | add {C D F G} : CellAssembly V C D → CellAssembly V F G →
      CellAssembly V (C + F) (D + G)
  | smul (a : ℤ) {C D} : CellAssembly V C D → CellAssembly V (a • C) (a • D)
  | reparametrize (c d : Cell 1 k O) (s : ℤ)
      (R : CubeReparametrization c d s)
      (hmap : ∀ x : cube k, (d.toFun x).val ∈ V) :
      CellAssembly V (Finsupp.single c 1) (s • Finsupp.single d 1)
  | subdivide {N : ℕ} (hk : 0 < k) (c : Cell 1 k O)
      (d : Fin N → Cell 1 k O) (s : Fin N → ℤ)
      (R : ∀ i, CubeParameterPiece c (d i) (s i)) (seams : Set (E k))
      (hz : Specs.D04.C06.NullCovers.Model.ContentZero seams)
      (cover : (⋃ i, (R i).change '' cube k) = cube k)
      (overlap : ∀ i j, i ≠ j →
        ((R i).change '' cube k) ∩ ((R j).change '' cube k) ⊆ seams)
      (hmap : ∀ x : cube k, (c.toFun x).val ∈ V) :
      CellAssembly V (Finsupp.single c 1) (∑ i, s i • Finsupp.single (d i) 1)

end Model
open Model

namespace Model

/-- A displayed Jordan subregion of a cell is allowed to have any shape.
The Jordan hypothesis belongs to the geometric operations below, rather
than to the data used as generators of the free integer chain. -/
structure CellRegion (k : ℕ) {n : ℕ} (O : Set (E n)) where
  cell : Cell 1 k O
  domain : Set (E k)
  subset_cube : domain ⊆ cube k

def wholeCellRegion {k n : ℕ} {O : Set (E n)} (c : Cell 1 k O) : CellRegion k O :=
  ⟨c, cube k, Subset.rfl⟩

def cellRegionIntegral {k n : ℕ} {O : Set (E n)}
    (c : CellRegion k O) (omega : FormField n k) : ℝ :=
  Specs.D04.C06.JordanRegions.Model.regionIntegral
    (fun x : c.domain => cellCoefficient c.cell omega x)

/-- The maps agree only on the displayed subregion. In particular no
agreement of their derivatives on its frontier is assumed. -/
structure RegionReparametrization {k n : ℕ} {O : Set (E n)}
    (c d : CellRegion k O) (s : ℤ) where
  change : OpenPartialHomeomorph (E k) (E k)
  regular : ContDiffOn ℝ 1 change change.source
  inverse_regular : ContDiffOn ℝ 1 change.symm change.target
  domain : closure c.domain ⊆ change.source
  image : change '' c.domain = d.domain
  unit_sign : s = 1 ∨ s = -1
  sign : ∀ x ∈ c.domain, Real.sign ((fderiv ℝ change x).det) = (s : ℝ)
  agrees : ∀ x ∈ c.domain, cellExtension c.cell x = cellExtension d.cell (change x)

abbrev RegionChain (k : ℕ) {n : ℕ} (O : Set (E n)) := CellRegion k O →₀ ℤ

def regionChainIntegral {k n : ℕ} {O : Set (E n)} (omega : FormField n k) :
    RegionChain k O →+ ℝ :=
  Finsupp.liftAddHom (fun c => ({
    toFun := fun a : ℤ => a • cellRegionIntegral c omega
    map_zero' := by simp
    map_add' := fun a b => by simp [add_mul] } : ℤ →+ ℝ))

def regionBoundary {k n : ℕ} {O : Set (E n)} (c : Cell 1 (k+1) O) :
    RegionChain k O :=
  ∑ i : Fin (k+1), (-1 : ℤ) ^ i.val •
    (Finsupp.single (wholeCellRegion (cellFace c i true)) 1 -
      Finsupp.single (wholeCellRegion (cellFace c i false)) 1)

def RegionChainRegular {k n : ℕ} {O : Set (E n)} (V : Set (E n))
    (C : RegionChain k O) : Prop :=
  ∀ c ∈ C.support, Specs.D04.C06.JordanRegions.Model.Jordan c.domain ∧
    ∀ x ∈ closure c.domain, cellExtension c.cell x ∈ V

/-- A geometric assembly of arbitrary Jordan subregions. The generators
record covers, overlaps, and actual changes of parameters, never identities
of integrals. Degree zero requires no subdivision into smaller pieces. -/
inductive RegionAssembly {k n : ℕ} {O : Set (E n)} (V : Set (E n)) :
    RegionChain k O → RegionChain k O → Prop
  | refl (C) : RegionAssembly V C C
  | symm {C D} : RegionAssembly V C D → RegionAssembly V D C
  | trans {C D F} : RegionAssembly V C D → RegionAssembly V D F → RegionAssembly V C F
  | add {C D F G} : RegionAssembly V C D → RegionAssembly V F G →
      RegionAssembly V (C + F) (D + G)
  | smul (a : ℤ) {C D} : RegionAssembly V C D → RegionAssembly V (a • C) (a • D)
  | reparametrize (c d : CellRegion k O) (s : ℤ)
      (hj : Specs.D04.C06.JordanRegions.Model.Jordan c.domain)
      (R : RegionReparametrization c d s)
      (hmapc : ∀ x ∈ closure c.domain, cellExtension c.cell x ∈ V)
      (hmapd : ∀ x ∈ closure d.domain, cellExtension d.cell x ∈ V) :
      RegionAssembly V (Finsupp.single c 1) (s • Finsupp.single d 1)
  | subdivide {N : ℕ} (hk : 0 < k) (c : CellRegion k O)
      (S : Fin N → Set (E k)) (hS : ∀ i, S i ⊆ c.domain)
      (hj : ∀ i, Specs.D04.C06.JordanRegions.Model.Jordan (S i))
      (seams : Set (E k)) (hz : Specs.D04.C06.NullCovers.Model.ContentZero seams)
      (cover : (⋃ i, S i) = c.domain)
      (overlap : ∀ i j, i ≠ j → S i ∩ S j ⊆ seams)
      (hmap : ∀ x ∈ closure c.domain, cellExtension c.cell x ∈ V) :
      RegionAssembly V (Finsupp.single c 1)
        (∑ i, Finsupp.single (⟨c.cell, S i, (hS i).trans c.subset_cube⟩ : CellRegion k O) 1)

end Model

/-- Reparametrization on arbitrary Jordan parameter subregions, with no
rank or injectivity condition on either ambient cell. -/
def region_reparametrizationType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c d : CellRegion k O) (s : ℤ),
    Specs.D04.C06.JordanRegions.Model.Jordan c.domain →
    RegionReparametrization c d s →
    ∀ (V : Set (E n)) (omega : FormField n k), IsCrForm (some 0) V omega →
    (∀ x ∈ closure c.domain, cellExtension c.cell x ∈ V) →
    (∀ x ∈ closure d.domain, cellExtension d.cell x ∈ V) →
      cellRegionIntegral c omega = (s : ℝ) * cellRegionIntegral d omega

def region_coefficient_integrableType : Prop :=
  ∀ {k n : ℕ} {O V : Set (E n)} (c : CellRegion k O),
    Specs.D04.C06.JordanRegions.Model.Jordan c.domain →
    ∀ omega : FormField n k, IsCrForm (some 0) V omega →
    (∀ x ∈ closure c.domain, cellExtension c.cell x ∈ V) →
      Specs.D04.C06.JordanRegions.Model.RegionIntegrable
        (fun x : c.domain => cellCoefficient c.cell omega x)

/-- The Jordan condition needed for displayed subregions follows from
their stipulated finite lower-dimensional C¹ frontiers. -/
def jordan_regions_of_finite_seamsType : Prop :=
  ∀ {k m N : ℕ}, 0 < k → ∀ (d : Fin m → ℕ)
    (K : ∀ i, Set (E (d i))) (f : ∀ i, E (d i) → E k),
    (∀ i, d i < k) → (∀ i, IsCompact (K i)) →
    (∀ i x, x ∈ K i → ContDiffAt ℝ 1 (f i) x) →
    ∀ S : Fin N → Set (E k), (∀ i, S i ⊆ cube k) →
    (∀ i, frontier (S i) ⊆ ⋃ j, f j '' K j) →
      ∀ i, Specs.D04.C06.JordanRegions.Model.Jordan (S i)

def region_assembly_integralType : Prop :=
  ∀ {k n : ℕ} {O V : Set (E n)} {C D : RegionChain k O}, RegionAssembly V C D →
    ∀ omega : FormField n k, IsCrForm (some 0) V omega →
      regionChainIntegral omega C = regionChainIntegral omega D

/-- Full cell Stokes with displayed Jordan boundary subregions, integer
multiplicities, and paired directed parametrizations. -/
def cell_piecewise_stokes_regionsType : Prop :=
  ∀ {k n N P : ℕ} {O V : Set (E n)} (c : Fin N → Cell 1 (k+1) O)
    (a : Fin N → ℤ) (outer refined : RegionChain k O)
    (left right : Fin P → CellRegion k O) (b s : Fin P → ℤ),
    RegionAssembly V (∑ j, a j • regionBoundary (c j)) refined →
    (∀ i, Specs.D04.C06.JordanRegions.Model.Jordan (left i).domain) →
    (∀ i, RegionReparametrization (left i) (right i) (s i)) →
    refined = outer +
      ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) →
    RegionChainRegular V outer →
    ∀ omega : FormField n k, IsCrForm (some 1) V omega →
    (∀ j (x : cube (k+1)), ((c j).toFun x).val ∈ V) →
    (∀ i x, x ∈ closure (left i).domain → cellExtension (left i).cell x ∈ V) →
    (∀ i x, x ∈ closure (right i).domain → cellExtension (right i).cell x ∈ V) →
      (∀ p ∈ outer.support, Specs.D04.C06.JordanRegions.Model.RegionIntegrable
        (fun x : p.domain => cellCoefficient p.cell omega x)) ∧
      (∑ j, (a j : ℝ) * cellIntegral (c j) (exteriorDerivative omega)) =
        regionChainIntegral omega outer

namespace Model

/-- A genuine chart extension on a closed parameter rectangle. -/
structure ChartRectangle {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart 1 k n M) where
  box : Specs.D04.C06.DarbouxIntegral.Model.Box k
  nondegenerate : Specs.D04.C06.DarbouxIntegral.Model.Nondegenerate box
  source_box : Specs.D04.C06.DarbouxIntegral.Model.carrier box ⊆ c.source
  domain : Set (E k)
  open_domain : IsOpen domain
  domain_box : Specs.D04.C06.DarbouxIntegral.Model.carrier box ⊆ domain
  extension : E k → E n
  regular : ContDiffOn ℝ 1 extension domain
  agrees : EqOn extension c.toFun (c.source ∩ domain)

/-- Finite localization by actual signed charts and smooth ambient weights.
All conditions are geometric; no equation of integrals is stored. -/
structure ManifoldCellDisplay {k n : ℕ} {M : Set (E n)}
    (o : PositiveManifoldOrientation 1 k M) (K : Set M) where
  partition : SignedChartPartition o K
  rectangle : ∀ i, ChartRectangle (partition.chart i)
  coordinates : ∀ i x, x ∈ tsupport (fun y : M => partition.weight i y) →
    (partition.chart i).invFun x ∈
      Specs.D04.C06.DarbouxIntegral.Model.carrier (rectangle i).box

def ManifoldCellDisplay.cell {k n : ℕ} {M : Set (E n)}
    {o : PositiveManifoldOrientation 1 k M} {K : Set M}
    (D : ManifoldCellDisplay o K) (i : Fin D.partition.count) :
    Cell 1 k (univ : Set (E n)) :=
  Specs.D04.C15.LocalStokesWithArtificialFaces.Model.rectangleChartCell
    (D.rectangle i).box (D.rectangle i).extension (D.rectangle i).domain
    (D.rectangle i).open_domain (D.rectangle i).domain_box (D.rectangle i).regular

end Model

def manifold_cell_display_existsType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 (k+1) M)
    (K : Set M), IsCompact K → Nonempty (ManifoldCellDisplay o K)

/-- The existing partition-independent manifold integral equals an actual
finite signed sum of weighted cell integrals. This is a bridge to cells,
not a redefinition of the manifold integral. -/
def manifold_cell_display_integralType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 k M)
    {K : Set M} (D : ManifoldCellDisplay o K) (V : Set (E n))
    (omega : FormField n k), M ⊆ V → IsCrForm (some 0) V omega →
    topSupport (tangentRestriction 1 k M omega) ⊆ K → ∀ I : ℝ,
    HasPositiveIntegral o (tangentRestriction 1 k M omega) I →
      I = ∑ i, (D.partition.sign i).val *
        cellIntegral (D.cell i) (fun x => D.partition.weight i x • omega x)

def compact_manifold_cell_integralType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)} (o : PositiveManifoldOrientation 1 (k+1) M),
    IsCompact M → ∀ (V : Set (E n)) (omega : FormField n (k+1)),
    M ⊆ V → IsCrForm (some 0) V omega →
    ∃ (D : ManifoldCellDisplay o univ) (I : ℝ),
      HasPositiveIntegral o (tangentRestriction 1 (k+1) M omega) I ∧
      I = ∑ i, (D.partition.sign i).val *
        cellIntegral (D.cell i) (fun x => D.partition.weight i x • omega x)

def cell_reparametrizationType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c d : Cell 1 k O) (s : ℤ),
    Nonempty (CubeReparametrization c d s) →
    ∀ (V : Set (E n)) (omega : FormField n k), IsCrForm (some 0) V omega →
    (∀ x : cube k, (d.toFun x).val ∈ V) →
      cellIntegral c omega = (s : ℝ) * cellIntegral d omega

/-- The boundary decomposition is an equality of actual formal chains,
not an equality of integrals. Every seam includes its integer multiplicity.
Outer pieces retain their prescribed coefficients and parametrizations. -/
def cell_piecewise_stokesType : Prop :=
  ∀ {k n N P : ℕ} {O : Set (E n)} (c : Fin N → Cell 1 (k+1) O)
    (a : Fin N → ℤ) (outer : Chain 1 k O)
    (left right : Fin P → Cell 1 k O) (b s : Fin P → ℤ),
    (∀ i, Nonempty (CubeReparametrization (left i) (right i) (s i))) →
    (∑ j, a j • cellBoundary (c j)) = outer +
      ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) →
    ∀ (V : Set (E n)) (omega : FormField n k), IsCrForm (some 1) V omega →
    (∀ j (x : cube (k+1)), ((c j).toFun x).val ∈ V) →
    (∀ i (x : cube k), ((right i).toFun x).val ∈ V) →
      (∑ j, (a j : ℝ) * cellIntegral (c j) (exteriorDerivative omega)) =
        chainIntegral omega outer

/-- Finite integer sums of the actual compact ambient manifold theorem.
Both values are quantified independently in the existential conclusion. -/
def manifold_summandsType : Prop :=
  ∀ {k n N : ℕ} (M : Fin N → Set (E n))
    (o : ∀ j, PositiveManifoldOrientation 1 (k+1) (M j)),
    (∀ j, IsCompact (M j)) → ∀ (a : Fin N → ℤ) (V : Set (E n))
    (omega : FormField n k), (∀ j, M j ⊆ V) → IsCrForm (some 1) V omega →
    ∃ (bO : ∀ j, ManifoldOrientation 1 k (intrinsicBoundary 1 (k+1) (M j)))
      (I J : Fin N → ℝ),
      (∀ j, OutwardFirst k (o j) (bO j) ∧
        HasPositiveIntegral (o j)
          (tangentRestriction 1 (k+1) (M j) (exteriorDerivative omega)) (I j) ∧
        HasManifoldIntegral 1 k (bO j)
          (tangentRestriction 1 k (intrinsicBoundary 1 (k+1) (M j)) omega) (J j)) ∧
      (∑ j, (a j : ℝ) * I j) = ∑ j, (a j : ℝ) * J j

open Specs.D04.C06.DarbouxIntegral.Model hiding E
def finite_seam_invarianceType : Prop :=
  ∀ {k m : ℕ}, 0 < k → ∀ (d : Fin m → ℕ)
    (K : ∀ i, Set (E (d i))) (f : ∀ i, E (d i) → E k),
    (∀ i, d i < k) → (∀ i, IsCompact (K i)) →
    (∀ i x, x ∈ K i → ContDiffAt ℝ 1 (f i) x) →
    ∀ (Q : Box k) (a b : E k → ℝ), Integrable a Q → Bounded b Q →
    (∀ x ∈ carrier Q, x ∉ ⋃ i, f i '' K i → a x = b x) →
      ∃ hb : Integrable b Q, lowerIntegral b Q = lowerIntegral a Q

/-- Pointwise counting away from the displayed seams. This is the
combinatorial part of the geometric multiplicity-one assertion. -/
def multiplicity_one_off_seamsType : Prop :=
  ∀ {n N : ℕ} (pieces : Fin N → Set (E n)) (seams : Set (E n)),
    (∀ i j, i ≠ j → pieces i ∩ pieces j ⊆ seams) →
    ∀ x ∈ (⋃ i, pieces i) \ seams,
      (∑ i, if x ∈ pieces i then (1 : ℕ) else 0) = 1

/-- Once a geometric seam is identified as an embedded piece, opposite
orientations cancel for the actual partition-independent integral. -/
def manifold_opposite_cancelType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (o p : ManifoldOrientation r k M), oppositeOrientation k o p →
    ∀ (eta : TangentTopField r k M) (I J : ℝ),
    HasManifoldIntegral r k o eta I → HasManifoldIntegral r k p eta J → I + J = 0

/-- A geometric coefficient is counted once on a finite union, even when
pieces share lower-dimensional seams. This is an equality of the actual
Jordan integrals, not only a statement about pointwise counting. -/
def integral_union_off_seamsType : Prop :=
  ∀ {k N : ℕ}, 0 < k → ∀ (pieces : Fin N → Set (E k)) (seams : Set (E k)),
    Specs.D04.C06.NullCovers.Model.ContentZero seams →
    (∀ i, Specs.D04.C06.JordanRegions.Model.Jordan (pieces i)) →
    (∀ i j, i ≠ j → pieces i ∩ pieces j ⊆ seams) →
    ∀ f : E k → ℝ,
    (∀ i, Specs.D04.C06.JordanRegions.Model.RegionIntegrable
      (fun x : pieces i => f x)) →
    Specs.D04.C06.JordanRegions.Model.RegionIntegrable
      (fun x : (⋃ i, pieces i) => f x) ∧
    Specs.D04.C06.JordanRegions.Model.regionIntegral
      (fun x : (⋃ i, pieces i) => f x) =
      ∑ i, Specs.D04.C06.JordanRegions.Model.regionIntegral
        (fun x : pieces i => f x)

/-- Directed integration on a single proper parameter subregion, including
nonzero coefficients on all its faces. -/
def cell_parameter_pieceType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c d : Cell 1 k O) (s : ℤ)
    (R : CubeParameterPiece c d s) (V : Set (E n)) (omega : FormField n k),
    IsCrForm (some 0) V omega →
    (∀ x : cube k, (c.toFun x).val ∈ V) →
    Specs.D04.C06.JordanRegions.Model.RegionIntegrable
      (fun x : R.change '' cube k => cellCoefficient c omega x) ∧
    cellIntegral d omega = (s : ℝ) *
      Specs.D04.C06.JordanRegions.Model.regionIntegral
        (fun x : R.change '' cube k => cellCoefficient c omega x)

/-- Subdivision by finitely many parameter diffeomorphisms whose images
cover the parent cube and overlap only on finite-content-zero seams.
The signs retain the directions of all subcell parametrizations. -/
def cell_subdivisionType : Prop :=
  ∀ {k n N : ℕ}, 0 < k → ∀ {O : Set (E n)}
    (c : Cell 1 k O) (d : Fin N → Cell 1 k O) (s : Fin N → ℤ)
    (R : ∀ i, CubeParameterPiece c (d i) (s i)) (seams : Set (E k)),
    Specs.D04.C06.NullCovers.Model.ContentZero seams →
    (⋃ i, (R i).change '' cube k) = cube k →
    (∀ i j, i ≠ j → ((R i).change '' cube k) ∩ ((R j).change '' cube k) ⊆ seams) →
    ∀ (V : Set (E n)) (omega : FormField n k), IsCrForm (some 0) V omega →
    (∀ x : cube k, (c.toFun x).val ∈ V) →
    cellIntegral c omega = ∑ i, (s i : ℝ) * cellIntegral (d i) omega

/-- A C¹ map that is injective with nonsingular derivative on a compact
set restricts to a C¹ diffeomorphism on an open neighborhood of that set.
The produced map is the given representative on all of parameter space. -/
def compact_parameter_extensionType : Prop :=
  ∀ {k : ℕ} (K : Set (E k)) (h : E k → E k) (U : Set (E k)),
    IsCompact K → IsOpen U → K ⊆ U → ContDiffOn ℝ 1 h U → InjOn h K →
    (∀ x ∈ K, (fderiv ℝ h x).det ≠ 0) →
    ∃ e : OpenPartialHomeomorph (E k) (E k), (e : E k → E k) = h ∧
      K ⊆ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target

/-- A signed C¹ diffeomorphism of closed cubes need only be given as a C¹
map on a neighborhood, injective on the cube. An open diffeomorphism
neighborhood is a conclusion, rather than additional assumed data. -/
def cube_reparametrization_from_mapType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c d : Cell 1 k O) (s : ℤ)
    (h : E k → E k) (U : Set (E k)), IsOpen U → cube k ⊆ U →
    ContDiffOn ℝ 1 h U → InjOn h (cube k) → h '' cube k = cube k →
    (s = 1 ∨ s = -1) →
    (∀ x ∈ cube k, Real.sign ((fderiv ℝ h x).det) = (s : ℝ)) →
    (∀ x : cube k, (c.toFun x).val = cellExtension d (h x)) →
    Nonempty (CubeReparametrization c d s)

/-- The actual chain integral respects the finitely generated geometric
assembly relation, for every continuous form near the participating pieces. -/
def cell_assembly_integralType : Prop :=
  ∀ {k n : ℕ} {O V : Set (E n)} {C D : Chain 1 k O}, CellAssembly V C D →
    ∀ omega : FormField n k, IsCrForm (some 0) V omega →
    chainIntegral omega C = chainIntegral omega D

/-- Stokes with boundary pieces that have first undergone explicit finite
subdivision and directed changes of parameters. Pairings and multiplicities
are equations of formal chains; their cancellation is proved by substitution. -/
def cell_piecewise_stokes_refinedType : Prop :=
  ∀ {k n N P : ℕ} {O V : Set (E n)} (c : Fin N → Cell 1 (k+1) O)
    (a : Fin N → ℤ) (outer refined : Chain 1 k O)
    (left right : Fin P → Cell 1 k O) (b s : Fin P → ℤ),
    CellAssembly V (∑ j, a j • cellBoundary (c j)) refined →
    (∀ i, Nonempty (CubeReparametrization (left i) (right i) (s i))) →
    refined = outer +
      ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1) →
    ∀ omega : FormField n k, IsCrForm (some 1) V omega →
    (∀ j (x : cube (k+1)), ((c j).toFun x).val ∈ V) →
    (∀ i (x : cube k), ((right i).toFun x).val ∈ V) →
      (∑ j, (a j : ℝ) * cellIntegral (c j) (exteriorDerivative omega)) =
        chainIntegral omega outer

/-- Separate local C¹ extensions can be glued near any compact parameter set.
No differentiability of the arbitrary off-set representative is required. -/
def compact_local_extensionType : Prop :=
  ∀ {k l : ℕ} (K : Set (E k)) (h : E k → E l), IsCompact K →
    (∀ x ∈ K, ∃ (U : Set (E k)) (g : E k → E l),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (K ∩ U)) →
    ∃ g : E k → E l, ContDiff ℝ 1 g ∧ EqOn g h K

/-- On a parameter set with unique derivatives, local nonsingular extensions
produce an actual diffeomorphism on a neighborhood of the compact set. -/
def compact_local_diffeomorphismType : Prop :=
  ∀ {k : ℕ} (K : Set (E k)) (h : E k → E k),
    IsCompact K → UniqueDiffOn ℝ K → InjOn h K →
    (∀ x ∈ K, ∃ (U : Set (E k)) (g : E k → E k),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (K ∩ U) ∧
      (fderiv ℝ g x).det ≠ 0) →
    ∃ e : OpenPartialHomeomorph (E k) (E k), EqOn e h K ∧ K ⊆ e.source ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target

/-- A signed closed-cube diffeomorphism given only by separate local C¹
extensions suffices for the existing directed reparametrization theorem. -/
def cube_reparametrization_from_localType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c d : Cell 1 k O) (s : ℤ)
    (h : E k → E k), InjOn h (cube k) → h '' cube k = cube k →
    (s = 1 ∨ s = -1) →
    (∀ x ∈ cube k, ∃ (U : Set (E k)) (g : E k → E k),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (cube k ∩ U) ∧
      Real.sign ((fderiv ℝ g x).det) = (s : ℝ)) →
    (∀ x : cube k, (c.toFun x).val = cellExtension d (h x)) →
    Nonempty (CubeReparametrization c d s)

/-! The large manifold and geometric-union statements below unfold to the full
independent upstream Prop types, on the same canonical objects. -/
def patch_local_reparametrizationType : Prop :=
  Specs.D04.C15.FiniteGeometricPatchIntegrals.local_reparametrizationType

def patch_of_local_extensionsType : Prop :=
  Specs.D04.C15.FiniteGeometricPatchIntegrals.patch_of_local_extensionsType

def geometric_assembly_integralType : Prop :=
  Specs.D04.C15.FiniteGeometricPatchIntegrals.geometric_equivalence_soundType

def manifold_boundary_localizationType : Prop :=
  Specs.D04.C15.FiniteManifoldBoundaryAssembly.regular_boundary_localizationType

def manifold_piecewise_stokesType : Prop :=
  Specs.D04.C15.FiniteManifoldBoundaryAssembly.positive_boundary_assemblyType

def manifold_piecewise_stokes_pointsType : Prop :=
  Specs.D04.C15.FiniteManifoldBoundaryAssembly.signed_point_boundary_assemblyType

def geometric_integral_existsType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.geometric_union_integral_existsType

def geometric_integral_eq_sumType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.geometric_union_integral_eq_sumType

def geometric_integral_independentType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.geometric_union_integral_independentType

def regular_cell_geometric_displayType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.cell_family_displayType

def cell_union_from_lower_parametersType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.cell_family_from_lower_parametersType

def cell_union_from_lower_manifoldsType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.cell_family_from_lower_manifoldsType

def manifold_union_from_lower_parametersType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.manifold_family_from_lower_parametersType

def manifold_union_from_lower_manifoldsType : Prop :=
  Specs.D04.C15.FiniteGeometricUnionIntegral.manifold_family_from_lower_manifoldsType


open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model

namespace Model
/-- A patch with its full unweighted coefficient. -/
def plainPatch {k n : ℕ} {O : Set (E n)} (P : Patch k O) : WeightedPatch k O :=
  ⟨P, fun _ => 1, continuousOn_const⟩

/-- The original cubical face signs, with each face displayed as a Jordan patch. -/
def patchBoundary {k n : ℕ} {O : Set (E n)}
    (P : Fin (k+1) → Bool → Patch k O) : PatchChain k O :=
  ∑ i : Fin (k+1), (-1 : ℤ) ^ i.val •
    (Finsupp.single (plainPatch (P i true)) 1 -
      Finsupp.single (plainPatch (P i false)) 1)
end Model

/-- Face patches exist for every cell, without rank or injectivity assumptions. -/
def cell_boundary_patch_displayType : Prop :=
  ∀ {k n N : ℕ} {O : Set (E n)} (c : Fin N → Cell 1 (k+1) O),
    ∃ P : Fin N → Fin (k+1) → Bool → Patch k O,
      ∀ j i e, (P j i e).region = cube k ∧
        EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube k)

/-- Actual patch and cell integrals agree from values on the cube alone. -/
def cell_patch_integralType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c : Cell 1 k O) (P : Patch k O),
    P.region = cube k → EqOn P.map (cellExtension c) (cube k) →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
      patchIntegral P (fun _ => 1) omega = cellIntegral c omega

/-- Complete cell-chain cancellation after arbitrary finite Jordan subdivision,
ambient localization and separately local directed reparametrization. The
assembly relation stores only geometric generators and integer operations. -/
def cell_piecewise_stokes_patchesType : Prop :=
  ∀ {k n N L : ℕ} {O : Set (E n)} (c : Fin N → Cell 1 (k+1) O)
    (a : Fin N → ℤ) (P : Fin N → Fin (k+1) → Bool → Patch k O),
    (∀ j i e, (P j i e).region = cube k ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube k)) →
    ∀ (outer : PatchChain k O) (left right : Fin L → WeightedPatch k O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, a j • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    ∀ omega : FormField n k, IsCrForm (some 1) O omega →
      (∑ j, (a j : ℝ) * cellIntegral (c j) (exteriorDerivative omega)) =
        patchChainIntegral omega outer

/-- Nonsingular separate C¹ extensions supply the actual local diffeomorphisms.
No global differentiability of h or unique derivatives of S are required. -/
def local_reparametrization_from_extensionsType : Prop :=
  ∀ {k : ℕ} (S T : Set (E k)) (h : E k → E k) (sigma : ℝ),
    (sigma = 1 ∨ sigma = -1) → BijOn h S T →
    (∀ x ∈ closure S, ∃ (U : Set (E k)) (g : E k → E k),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (closure S ∩ U) ∧
      Real.sign ((fderiv ℝ g x).det) = sigma) →
    ∃ R : LocalReparametrization S T sigma, R.map = h

/-- Directed patch substitution directly from separate local C¹ extensions. -/
def patch_reparametrization_from_extensionsType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (P Q : Patch k O) (h : E k → E k) (sigma : ℝ),
    (sigma = 1 ∨ sigma = -1) → BijOn h P.region Q.region →
    (∀ x ∈ closure P.region, ∃ (U : Set (E k)) (g : E k → E k),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧ EqOn g h (closure P.region ∩ U) ∧
      Real.sign ((fderiv ℝ g x).det) = sigma) →
    EqOn P.map (Q.map ∘ h) P.region →
    ∀ omega : FormField n k, IsCrForm (some 0) O omega →
    ∀ w : E n → ℝ, ContinuousOn w O →
      patchIntegral P w omega = sigma * patchIntegral Q w omega

/-- When the original cells form one regular geometric region, the Stokes
left side is its decomposition-independent multiplicity-one integral. Actual
cell faces are added to the supplied overlap seams by the display theorem. -/
def geometric_cell_piecewise_stokesType : Prop :=
  ∀ {k n N L : ℕ} {O : Set (E n)} (c : Fin N → Cell 1 (k+1) O)
    (P : Fin N → Fin (k+1) → Bool → Patch k O),
    (∀ j i e, (P j i e).region = cube k ∧
      EqOn (P j i e).map (cellExtension (cellFace (c j) i e)) (cube k)) →
    ∀ (outer : PatchChain k O) (left right : Fin L → WeightedPatch k O)
      (b s : Fin L → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, ∃ h : LocalReparametrization (left i).patch.region (right i).patch.region (s i : ℝ),
      EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region) →
    (∀ i, EqOn (left i).weight (right i).weight ((right i).patch.map '' (right i).patch.region)) →
    GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (P j))
      (outer + ∑ i, b i • (Finsupp.single (left i) 1 - s i • Finsupp.single (right i) 1)) →
    (∀ j, InjOn (cellExtension (c j)) (cube (k+1))) →
    (∀ j x, x ∈ cube (k+1) → Function.Injective (fderiv ℝ (cellExtension (c j)) x)) →
    ∀ Z : AmbientSeams (k+1) n,
    (∀ i j, i ≠ j → (cellExtension (c i) '' cube (k+1)) ∩
      (cellExtension (c j) '' cube (k+1)) ⊆ Z.carrier) →
    ∀ omega : FormField n k, IsCrForm (some 1) O omega →
      ∃ D : GeometricDecomposition (k+1) n O,
        D.carrier = ⋃ j, cellExtension (c j) '' cube (k+1) ∧
        geometricUnionIntegral D (exteriorDerivative omega) = patchChainIntegral omega outer

open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
/-- The manifold Stokes formula on an actual geometric union, with no smooth
manifold structure imposed on the entire union. Bulk multiplicities are one;
all displayed outer orientations and directed internal matchings are retained. -/
def geometric_manifold_piecewise_stokesType : Prop :=
  ∀ {d n q} {O : Set (E n)} (M : Fin q → CompactManifold (d+1) n O)
    (bO : (j : Fin q) → PositiveManifoldOrientation 1 (d+1)
      (intrinsicBoundary 1 (d+2) (M j).carrier)),
    (∀ j, OutwardFirst (d+1) (M j).orientation (bO j)) →
    ∀ (m : Fin q → ℕ) (P : (j : Fin q) → Fin (m j) → Patch (d+1) O)
      (s : (j : Fin q) → Fin (m j) → PointSign),
    (∀ j t, RegularPiece (bO j) (P j t) (s j t)) →
    ∀ Z : Fin q → Seams n, (∀ j i, (Z j).dim i < d+1) →
    (∀ j t u, u ∈ (P j t).region → ∀ v, v ∈ (P j t).region → u ≠ v →
      (P j t).map u = (P j t).map v → (P j t).map u ∈ (Z j).carrier) →
    (∀ j t u, t ≠ u → ((P j t).map '' (P j t).region) ∩
      ((P j u).map '' (P j u).region) ⊆ (Z j).carrier) →
    (∀ j, intrinsicBoundary 1 (d+2) (M j).carrier ⊆
      (⋃ t, (P j t).map '' (P j t).region) ∪ (Z j).carrier) →
    ∀ Zbulk : AmbientSeams (d+2) n,
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Zbulk.carrier) →
    ∀ {l p : ℕ}
      (e : (Fin l ⊕ (Fin p × Bool)) ≃ ((j : Fin q) × Fin (m j)))
      (Q : Fin l → Patch (d+1) O) (tSign : Fin l → PointSign) (b : Fin l → ℤ)
      (deltaOut : Fin l → ℝ),
    (∀ t, deltaOut t = 1 ∨ deltaOut t = -1) →
    ∀ hOut : (t : Fin l) → LocalReparametrization
      (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region (Q t).region (deltaOut t),
    (∀ t, EqOn (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).map
      ((Q t).map ∘ (hOut t).map) (P (e (Sum.inl t)).1 (e (Sum.inl t)).2).region ∧
      (s (e (Sum.inl t)).1 (e (Sum.inl t)).2).val * deltaOut t = (tSign t).val ∧
      b t = 1) →
    ∀ deltaPair : Fin p → ℝ, (∀ i, deltaPair i = 1 ∨ deltaPair i = -1) →
    ∀ hPair : (i : Fin p) → LocalReparametrization
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region
      (P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).region (deltaPair i),
    (∀ i, EqOn (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).map
      ((P (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).map ∘ (hPair i).map)
      (P (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).region ∧
      (s (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val * deltaPair i =
        -(s (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ omega : FormField n (d+1), IsCrForm (some 1) O omega →
    ∃ D : GeometricDecomposition (d+2) n O,
      D.carrier = ⋃ j, (M j).carrier ∧
      geometricUnionIntegral D (exteriorDerivative omega) =
        ∑ t, b t • ((tSign t).val * patchIntegral (Q t) (fun _ => 1) omega)

/-- Dimension-one manifold unions use their prescribed signed point boundary,
with the same actual geometric union value as the higher-dimensional branch. -/
def geometric_manifold_piecewise_stokes_pointsType : Prop :=
  ∀ {n q} {O : Set (E n)} (M : Fin q → CompactManifold 0 n O)
    (bO : (j : Fin q) → ZeroManifoldOrientation (intrinsicBoundary 1 1 (M j).carrier)),
    (∀ j, OutwardFirst 0 (M j).orientation (bO j)) → ∀ {l p : ℕ}
    (e : (Fin l ⊕ (Fin p × Bool)) ≃ (j : Fin q) × intrinsicBoundary 1 1 (M j).carrier)
    (P : Fin l → Patch 0 O) (s : Fin l → PointSign) (c : Fin l → ℤ),
    (∀ t, (0 : E 0) ∈ (P t).region ∧
      (P t).map 0 = (e (Sum.inl t)).2.val ∧
      s t = bO (e (Sum.inl t)).1 (e (Sum.inl t)).2 ∧ c t = 1) →
    (∀ i, (e (Sum.inr (i,false))).2.val = (e (Sum.inr (i,true))).2.val ∧
      (bO (e (Sum.inr (i,false))).1 (e (Sum.inr (i,false))).2).val =
        -(bO (e (Sum.inr (i,true))).1 (e (Sum.inr (i,true))).2).val) →
    ∀ Z : AmbientSeams 1 n,
    (∀ i j, i ≠ j → (M i).carrier ∩ (M j).carrier ⊆ Z.carrier) →
    ∀ omega : FormField n 0, IsCrForm (some 1) O omega →
    ∃ D : GeometricDecomposition 1 n O,
      D.carrier = ⋃ j, (M j).carrier ∧
      geometricUnionIntegral D (exteriorDerivative omega) =
        ∑ t, c t • (s t).val * patchIntegral (P t) (fun _ => 1) omega

/-- The declared cell target may be restricted to any open neighborhood of its
actual image. Its integral, for every ambient coefficient field, is preserved. -/
def cell_retargetType : Prop :=
  ∀ {k n : ℕ} {O : Set (E n)} (c : Cell 1 k O) (V : Set (E n)),
    IsOpen V → (∀ x : cube k, (c.toFun x).val ∈ V) →
    ∃ d : Cell 1 k V,
      (∀ x : cube k, (d.toFun x).val = (c.toFun x).val) ∧
      ∀ omega : FormField n k, cellIntegral d omega = cellIntegral c omega

end Specs.D04.C15.FinitePiecewiseStokes
