import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GreenCirculationAndFlux
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Basic.Real.Sign
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Independent interface for the cell branch of paper.tex:1041–1069.
The objects below use the actual D04 coordinate identification, cells, forms,
and patch chains, and the actual Ch03 paths. The original full-positive condition uses only the actual region, its local
side membership, and the actual signed visits of the original cycle. No
equivalence to a replacement contour is postulated.

Both the ambient-field and carrier-local boundary dictionaries retain arbitrary
supplied D04 displays. The carrier-local statement constructs a global C1
extension agreeing with the original field and its first real derivatives on
an open neighborhood. Both real outer values are extension-independent.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace D12Complex.CellBoundaryContour

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model

/-- The existing D04 scalar point map, packaged as a continuous linear map. -/
def scalarLine : ℝ →L[ℝ] E 1 :=
  (coordinates 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ))

def realForm (q : ℂ → ℂ) : FormField 2 1 :=
  circulationForm (fun x => (q (complexCoordinates.symm x)).re)
    (fun x => -(q (complexCoordinates.symm x)).im)

def imagForm (q : ℂ → ℂ) : FormField 2 1 :=
  circulationForm (fun x => (q (complexCoordinates.symm x)).im)
    (fun x => (q (complexCoordinates.symm x)).re)

def cellCurve {O : Set (E 2)} (c : Cell 1 1 O) (t : ℝ) : ℂ :=
  complexCoordinates.symm (cellExtension c (scalarLine t))

theorem cellCurve_contDiffOn {O : Set (E 2)} (c : Cell 1 1 O) :
    ContDiffOn ℝ 1 (cellCurve c) (Icc 0 1) := by
  have hmaps : MapsTo scalarLine (Icc (0 : ℝ) 1) (extensionDomain c) := by
    intro t ht
    apply (extension_spec c).2.1
    intro i
    exact ht
  exact complexCoordinates.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    ((extension_spec c).2.2.1.comp scalarLine.contDiff.contDiffOn hmaps)

/-- The original unit interval of the real cell is retained. -/
def cellPath {O : Set (E 2)} (c : Cell 1 1 O) : PiecewiseC1Path :=
  ⟨⟨0, 1, zero_le_one, cellCurve c, (cellCurve_contDiffOn c).continuousOn⟩,
    ⟨C1Partition.single _ (cellCurve_contDiffOn c)⟩⟩

/-- Linear realization of a real one-cell chain as actual canonical paths. -/
def cellContour {O : Set (E 2)} : Chain 1 1 O →+ IntegralChain :=
  Finsupp.liftAddHom (fun c =>
    { toFun := fun a => Finsupp.single (cellPath c) a
      map_zero' := Finsupp.single_zero _
      map_add' := fun a b => Finsupp.single_add _ a b })

/-- Exactly the geometric inputs of the positive regular-cell Green branch.
The equivalence is between D04's supplied real face display and its real outer
display. It is not a comparison premise concerning an original Ch03 cycle.
There is no contour integral, index, or analytic identity among the fields. -/
structure PositiveCellData (O : Set (E 2)) where
  open_ambient : IsOpen O
  count : ℕ
  cells : Fin count → Cell 1 2 O
  faces : Fin count → Fin 2 → Bool → Patch 1 O
  faces_agree : ∀ j i e, (faces j i e).region = cube 1 ∧
    EqOn (faces j i e).map (cellExtension (cellFace (cells j) i e)) (cube 1)
  outer : PatchChain 1 O
  pairs : ℕ
  left : Fin pairs → WeightedPatch 1 O
  right : Fin pairs → WeightedPatch 1 O
  multiplicity : Fin pairs → ℤ
  sign : Fin pairs → ℤ
  sign_unit : ∀ i, sign i = 1 ∨ sign i = -1
  pair_maps : ∀ i, ∃ h : LocalReparametrization
      (left i).patch.region (right i).patch.region (sign i : ℝ),
    EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region
  pair_weights : ∀ i, EqOn (left i).weight (right i).weight
    ((right i).patch.map '' (right i).patch.region)
  assembly : GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (faces j))
    (outer + ∑ i, multiplicity i •
      (Finsupp.single (left i) 1 - sign i • Finsupp.single (right i) 1))
  injective : ∀ j, InjOn (cellExtension (cells j)) (cube 2)
  positive : ∀ j x, x ∈ cube 2 → 0 < (fderiv ℝ (cellExtension (cells j)) x).det
  bulkSeams : AmbientSeams 2 2
  bulk_overlap : ∀ i j, i ≠ j →
    (cellExtension (cells i) '' cube 2) ∩ (cellExtension (cells j) '' cube 2) ⊆
      bulkSeams.carrier

def PositiveCellData.faceContour {O : Set (E 2)} (d : PositiveCellData O) : IntegralChain :=
  cellContour (∑ j, (1 : ℤ) • cellBoundary (d.cells j))

/-- The actual closed cell union, in the canonical complex coordinates. -/
def PositiveCellData.carrier {O : Set (E 2)} (d : PositiveCellData O) : Set ℂ :=
  ⋃ j, complexCoordinates.symm '' (cellExtension (d.cells j) '' cube 2)

/-- All actual face traces, before internal cancellation or refinement. -/
def PositiveCellData.faceCarrier {O : Set (E 2)} (d : PositiveCellData O) : Set ℂ :=
  ⋃ j, ⋃ i, ⋃ e, (cellPath (cellFace (d.cells j) i e)).trace

/-- The actual alternating face coefficient, with false denoting the zero
face and true the one face. -/
def cellFaceSign (i : Fin 2) (e : Bool) : ℤ :=
  (-1 : ℤ) ^ i.val * if e then 1 else -1

/-- Image under the actual cell differential of the inward parameter vector.
It points to the interior side at a relative interior face point; at a corner
this is only a vector, with no asserted smooth boundary chart. -/
def cellFaceInward {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool) (t : ℝ) : ℂ :=
  (if e then (-1 : ℝ) else 1) • complexCoordinates.symm
    (fderiv ℝ (cellExtension c) (faceInsertion i e (scalarLine t)) (standardBasis 2 i))

/-- Signed occurrence of a directed parameter interval at a reference value.
The half-open convention makes interval subdivision exact at endpoints. -/
def directedIntervalMultiplicity (a b t : ℝ) : ℤ :=
  (Ioc a b).indicator (fun _ => 1) t - (Ioc b a).indicator (fun _ => 1) t

/-- Scalar parameter of the original path on an injective compact reference
arc. Only its values on the original parameter interval will be used. -/
def arcParameter (g : ℝ → ℂ) (a b : ℝ) (η : PiecewiseC1Path) (t : ℝ) : ℝ :=
  Function.invFunOn g (Icc a b) (η t)

/-- Endpoint-directed local occurrence, after selecting an original subpath
inside one reference arc. This does not define a global boundary relation. -/
def arcTraversalMultiplicity (g : ℝ → ℂ) (a b : ℝ) (η : PiecewiseC1Path)
    (s : ℝ) : ℤ :=
  directedIntervalMultiplicity (arcParameter g a b η η.path.a)
    (arcParameter g a b η η.path.b) s

/-- Actual signed visits of the original parameter interval to a reference
arc point. The sign is measured in the recovered oriented arc coordinate.
At an infinite fiber the totalized value is zero; theorems below prove that
such fibers are exceptional for the regular PC1 traversals under consideration. -/
def arcSignedMultiplicity (g : ℝ → ℂ) (a b : ℝ) (η : PiecewiseC1Path)
    (s : ℝ) : ℤ := by
  classical
  exact if hf : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s}.Finite then
    ∑ t ∈ hf.toFinset, if 0 < deriv (arcParameter g a b η) t then 1
      else if deriv (arcParameter g a b η) t < 0 then -1 else 0
  else 0


/-- Signed visits measured directly from the actual original velocity relative
to a supplied oriented tangent. Infinite fibers are totalized to zero; the
regular-value theorems prove that they are exceptional on regular arcs. -/
def tangentSignedMultiplicity (η : PiecewiseC1Path) (z v : ℂ) : ℤ := by
  classical
  exact if hf : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = z}.Finite then
    ∑ t ∈ hf.toFinset,
      if 0 < (deriv η t / v).re then 1
      else if (deriv η t / v).re < 0 then -1 else 0
  else 0


/-- Sum of actual signed visits with every original integer coefficient. -/
def chainTangentMultiplicity (Γ : IntegralChain) (z v : ℂ) : ℤ :=
  Γ.sum (fun η c => c * tangentSignedMultiplicity η z v)

/-- Original regular times whose values lie on the supplied reference interval.
The original partition nodes and stationary times are kept outside this set;
subsequent integral theorems show their contribution vanishes. -/
def regularArcSource (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) : Set ℝ :=
  {t | t ∈ Icc η.path.a η.path.b ∧ t ∉ Set.range η.partition.node ∧
    deriv η t ≠ 0 ∧ η t ∈ g '' Icc a b}

/-- A derived measurable partition of the actual original coincidence times.
Its fields are geometric/parametric data, with no assumed integral identity.
Each scalar coordinate is injective only on its own open parameter chart. -/
structure ArcCoincidencePartition (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) where
  piece : ℕ → Set ℝ
  chart : ℕ → Set ℝ
  parameter : ℕ → ℝ → ℝ
  measurable : ∀ n, MeasurableSet (piece n)
  disjoint : Pairwise (fun n m => Disjoint (piece n) (piece m))
  cover : (⋃ n, piece n) = regularArcSource η g a b
  chart_open : ∀ n, IsOpen (chart n)
  subset_chart : ∀ n, piece n ⊆ chart n
  path_smooth : ∀ n, ContDiffOn ℝ 1 η (chart n)
  parameter_smooth : ∀ n, ContDiffOn ℝ 1 (parameter n) (chart n)
  parameter_injective : ∀ n, InjOn (parameter n) (chart n)
  parameter_mem : ∀ n, MapsTo (parameter n) (piece n) (Icc a b)
  factorization : ∀ n, EqOn η (g ∘ parameter n) (piece n)

/-- The signed density of one constructed coincidence piece, extended by zero
outside its actual scalar image. -/
def ArcCoincidencePartition.density {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (q : ℂ → ℂ) (n : ℕ) : ℝ → ℂ :=
  (P.parameter n '' P.piece n).indicator (fun s =>
    Real.sign ((deriv η (Function.invFunOn (P.parameter n) (P.piece n) s) /
      deriv g s).re) • (q (g s) * deriv g s))


/-- Local signed membership jump of the actual region across the left normal
of the supplied oriented tangent. This has no contour or integral premise. -/
def GeometricBoundaryJump (K : Set ℂ) (z v : ℂ) (m : ℤ) : Prop :=
  ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
    K.indicator (fun _ => (1 : ℤ)) (z + r • (Complex.I * v)) -
      K.indicator (fun _ => (1 : ℤ)) (z - r • (Complex.I * v)) = m

/-- Geometric full positive boundary condition for the original finite cycle.
The trace covers the actual topological frontier. In every regular injective
reference arc, its actual signed visits equal the region's local left-minus-
right membership jump almost everywhere. This allows signed repetitions,
stationary points, pauses, corners, and exceptional infinite fibers. It does
not refer to a replacement face chain, its integral, or its equivalence class.

The cell-incidence theorem derives the actual alternating face counts from
this condition using local side membership and tangential cancellation. -/
def IsFullPositiveBoundary (K : Set ℂ) (Γ : IntegralCycle) : Prop :=
  Γ.trace = frontier K ∧
    ∀ (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ), IsOpen V → Icc a b ⊆ V →
      ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
      (∀ s ∈ Icc a b, deriv g s ≠ 0) →
      ∀ᵐ s ∂volume.restrict (Icc a b),
        GeometricBoundaryJump K (g s) (deriv g s)
          (chainTangentMultiplicity Γ.chain (g s) (deriv g s))

end D12Complex.CellBoundaryContour

namespace Specs.D12Complex.Ch04.CellBoundaryContour

open _root_.D12Complex _root_.D12Complex.CellBoundaryContour
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

def cube_integral_eq_interval_type : Prop :=
  ∀ (g : E 1 → ℝ), ContinuousOn g (cube 1) →
    Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral g (cubeBox 1) =
      ∫ t in (0 : ℝ)..1, g (scalarLine t)

def cellPath_trace_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 1 O),
    (cellPath c).trace = complexCoordinates.symm '' (cellExtension c '' cube 1)

def cellPath_integral_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 1 O) (q : ℂ → ℂ),
    ContinuousOn q (complexCoordinates ⁻¹' O) →
    (cellPath c).integral q =
      (cellIntegral c (realForm q) : ℂ) + Complex.I * cellIntegral c (imagForm q)

def cellContour_integral_type : Prop :=
  ∀ {O : Set (E 2)} (C : Chain 1 1 O) (q : ℂ → ℂ),
    ContinuousOn q (complexCoordinates ⁻¹' O) →
    (cellContour C).integral q =
      (chainIntegral (realForm q) C : ℂ) + Complex.I * chainIntegral (imagForm q) C

def cellBoundary_integral_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O) (q : ℂ → ℂ),
    ContinuousOn q (complexCoordinates ⁻¹' O) →
    (cellContour (cellBoundary c)).integral q =
      (chainIntegral (realForm q) (cellBoundary c) : ℂ) +
        Complex.I * chainIntegral (imagForm q) (cellBoundary c)

def face_patch_dictionary_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 1 O) (P : Patch 1 O),
    P.region = cube 1 → EqOn P.map (cellExtension c) (cube 1) →
    ∀ (q : ℂ → ℂ), ContinuousOn q (complexCoordinates ⁻¹' O) →
    (cellPath c).integral q =
      (patchIntegral P (fun _ => 1) (realForm q) : ℂ) +
        Complex.I * patchIntegral P (fun _ => 1) (imagForm q)

def cell_assembly_real_boundary_type : Prop :=
  ∀ {O : Set (E 2)} (d : PositiveCellData O) (ω : FormField 2 1),
    IsCrForm (some 0) O ω →
    chainIntegral ω (∑ j, (1 : ℤ) • cellBoundary (d.cells j)) =
      patchChainIntegral ω d.outer

def cell_assembly_dictionary_type : Prop :=
  ∀ {O : Set (E 2)} (d : PositiveCellData O) (q : ℂ → ℂ),
    ContinuousOn q (complexCoordinates ⁻¹' O) →
    d.faceContour.integral q =
      (patchChainIntegral (realForm q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm q) d.outer

def finite_subpath_selection_type : Prop :=
  ∀ (γ : PiecewiseC1Path) {ι : Type} (U : ι → Set ℂ),
    (∀ i, IsOpen (U i)) → γ.trace ⊆ ⋃ i, U i →
    ∃ (n : ℕ) (node : Fin (n + 1) → ℝ) (select : Fin n → ι)
      (δ : Fin n → PiecewiseC1Path),
      Monotone node ∧ node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      (∀ i, (δ i).path.a = node i.castSucc ∧ (δ i).path.b = node i.succ ∧
        EqOn (δ i) γ (Icc (node i.castSucc) (node i.succ)) ∧ (δ i).trace ⊆ U (select i)) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q γ.trace →
        γ.integral q = ∑ i, (δ i).integral q

def finite_subpath_integral_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (n : ℕ) (node : Fin (n + 1) → ℝ),
    Monotone node → node 0 = γ.path.a → node (Fin.last n) = γ.path.b →
    ∀ δ : Fin n → PiecewiseC1Path,
    (∀ i, (δ i).path.a = node i.castSucc ∧ (δ i).path.b = node i.succ ∧
      EqOn (δ i) γ (Icc (node i.castSucc) (node i.succ))) →
    ∀ q : ℂ → ℂ, ContinuousOn q γ.trace →
      γ.integral q = ∑ i, (δ i).integral q

/-- Directed scalar substitution does not require monotonicity. Its smooth
pieces may have zero derivative, plateaus, and arbitrarily many turnarounds. -/
def scalar_piecewise_substitution_type : Prop :=
  ∀ (φ : ℝ → ℝ) (c d a b : ℝ) (n : ℕ) (node : Fin (n + 1) → ℝ),
    StrictMono node → node 0 = c → node (Fin.last n) = d →
    ContinuousOn φ (Icc c d) → MapsTo φ (Icc c d) (Icc a b) →
    (∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ))) →
    ∀ g : ℝ → ℂ, ContinuousOn g (Icc a b) →
    (∑ i : Fin n, ∫ t in node i.castSucc..node i.succ,
      derivWithin φ (Icc (node i.castSucc) (node i.succ)) t • g (φ t)) =
      ∫ s in φ c..φ d, g s

def arc_factorization_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (φ : ℝ → ℝ) (a b : ℝ)
    (V : Set ℝ), IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V →
    ContinuousOn φ (Icc η.path.a η.path.b) →
    MapsTo φ (Icc η.path.a η.path.b) (Icc a b) →
    EqOn η (g ∘ φ) (Icc η.path.a η.path.b) →
    (∀ i : Fin η.partition.count, ContDiffOn ℝ 1 φ (η.partition.pieceSet i)) →
    ∀ q : ℂ → ℂ, ContinuousOn q (g '' Icc a b) →
    η.integral q = ∫ s in φ η.path.a..φ η.path.b, q (g s) * deriv g s

def regular_cell_face_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O),
    InjOn (cellExtension c) (cube 2) →
    (∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det) →
    ∀ (i : Fin 2) (e : Bool),
      InjOn (cellCurve (cellFace c i e)) (Icc 0 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, deriv (cellCurve (cellFace c i e)) t ≠ 0

def regular_curve_coordinate_type : Prop :=
  ∀ (g : ℝ → ℂ) (s : ℝ), ContDiffAt ℝ 1 g s → deriv g s ≠ 0 →
    ∃ ψ : ℂ → ℝ, ContDiffAt ℝ 1 ψ (g s) ∧
      ∀ᶠ t in nhds s, ψ (g t) = t

def recover_parameter_contDiffOn_type : Prop :=
  ∀ (S : Set ℝ) (f g : ℝ → ℂ) (φ : ℝ → ℝ),
    ContDiffOn ℝ 1 f S → ContinuousOn φ S → EqOn f (g ∘ φ) S →
    (∀ t ∈ S, ContDiffAt ℝ 1 g (φ t) ∧ deriv g (φ t) ≠ 0) →
    ContDiffOn ℝ 1 φ S

def regular_arc_factorization_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (φ : ℝ → ℝ) (a b : ℝ)
    (V : Set ℝ), IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) →
    ContinuousOn φ (Icc η.path.a η.path.b) →
    MapsTo φ (Icc η.path.a η.path.b) (Icc a b) →
    EqOn η (g ∘ φ) (Icc η.path.a η.path.b) →
    ∀ q : ℂ → ℂ, ContinuousOn q (g '' Icc a b) →
    η.integral q = ∫ s in φ η.path.a..φ η.path.b, q (g s) * deriv g s

def parameter_on_injective_arc_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ),
    ContinuousOn g (Icc a b) → InjOn g (Icc a b) → η.trace ⊆ g '' Icc a b →
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc a b) ∧
      EqOn η (g ∘ φ) (Icc η.path.a η.path.b)

def trace_regular_arc_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) → η.trace ⊆ g '' Icc a b →
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc a b) ∧
      EqOn η (g ∘ φ) (Icc η.path.a η.path.b) ∧
      (∀ i : Fin η.partition.count, ContDiffOn ℝ 1 φ (η.partition.pieceSet i)) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q (g '' Icc a b) →
        η.integral q = ∫ s in φ η.path.a..φ η.path.b, q (g s) * deriv g s

def cell_face_traversal_integral_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O),
    InjOn (cellExtension c) (cube 2) →
    (∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det) →
    ∀ (i : Fin 2) (e : Bool) (η : PiecewiseC1Path),
    η.trace ⊆ (cellPath (cellFace c i e)).trace →
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc 0 1) ∧
      EqOn η (cellCurve (cellFace c i e) ∘ φ) (Icc η.path.a η.path.b) ∧
      (∀ j : Fin η.partition.count, ContDiffOn ℝ 1 φ (η.partition.pieceSet j)) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q (complexCoordinates ⁻¹' O) →
        η.integral q = ∫ s in φ η.path.a..φ η.path.b,
          q (cellCurve (cellFace c i e) s) * deriv (cellCurve (cellFace c i e)) s

/-- Only the times with nonzero derivative are countable. The whole preimage
of a seam may have positive measure and need not be finite. -/
def nonzero_deriv_countable_preimage_type : Prop :=
  ∀ (f : ℝ → ℂ) (Z : Set ℂ), Z.Countable →
    {t : ℝ | f t ∈ Z ∧ deriv f t ≠ 0}.Countable

def deriv_zero_ae_on_countable_preimage_type : Prop :=
  ∀ (f : ℝ → ℂ) (Z : Set ℂ), Z.Countable →
    ∀ᵐ t : ℝ, f t ∈ Z → deriv f t = 0

/-- Values of an integrand on a countable geometric seam do not affect the
original contour integral; no continuity is required of the changed field. -/
def path_integral_congr_off_countable_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (Z : Set ℂ), Z.Countable →
    ∀ (q r : ℂ → ℂ), EqOn q r (γ.trace \ Z) → γ.integral q = γ.integral r

/-- Dominated convergence for geometric neighborhoods, even if the seam has
infinitely many visits or constant original parameter intervals. -/
def seam_neighborhood_integral_tendsto_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (Z : Set ℂ), Z.Countable →
    ∀ (U : ℕ → Set ℂ), (∀ n, MeasurableSet (U n)) →
      (∀ z ∉ Z, ∀ᶠ n in Filter.atTop, z ∉ U n) →
      ∀ q : ℂ → ℂ, ContinuousOn q γ.trace →
        Filter.Tendsto (fun n => γ.integral ((U n).indicator q))
          Filter.atTop (nhds 0)

def chain_integral_congr_off_countable_type : Prop :=
  ∀ (Γ : IntegralChain) (Z : Set ℂ), Z.Countable →
    ∀ (q r : ℂ → ℂ), EqOn q r (Γ.trace \ Z) →
      Γ.integral q = Γ.integral r

def seam_neighborhood_chain_integral_tendsto_type : Prop :=
  ∀ (Γ : IntegralChain) (Z : Set ℂ), Z.Countable →
    ∀ (U : ℕ → Set ℂ), (∀ n, MeasurableSet (U n)) →
      (∀ z ∉ Z, ∀ᶠ n in Filter.atTop, z ∉ U n) →
      ∀ q : ℂ → ℂ, ContinuousOn q Γ.trace →
        Filter.Tendsto (fun n => Γ.integral ((U n).indicator q))
          Filter.atTop (nhds 0)

/-- In dimension one, the actual D04 ambient seam carrier is countable.
Its definition uses a countable cover; finiteness is not asserted. -/
def ambient_one_seam_countable_type : Prop :=
  ∀ {n : ℕ}
    (Z : Specs.D04.C15.FiniteGeometricUnionIntegral.Model.AmbientSeams 1 n),
    Z.carrier.Countable

/-- Applies to the original chain with all its integer coefficients. The
neighborhood radius need only converge to zero, and may have repeated terms. -/
def ambient_seam_chain_integral_tendsto_type : Prop :=
  ∀ (Γ : IntegralChain)
    (Z : Specs.D04.C15.FiniteGeometricUnionIntegral.Model.AmbientSeams 1 2)
    (ε : ℕ → ℝ), Filter.Tendsto ε Filter.atTop (nhds 0) →
    ∀ q : ℂ → ℂ, ContinuousOn q Γ.trace →
      Filter.Tendsto (fun n => Γ.integral
        ((Metric.thickening (ε n) (complexCoordinates.symm '' Z.carrier)).indicator q))
        Filter.atTop (nhds 0)

/-- Continuous (in particular smooth) cutoff errors are controlled on the
original path. Convergence is only required off the countable seam. -/
def seam_multiplier_integral_tendsto_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (Z : Set ℂ), Z.Countable →
    ∀ A : ℕ → ℂ → ℂ,
      (∀ n, ContinuousOn (A n) γ.trace) →
      (∀ n z, z ∈ γ.trace → ‖A n z‖ ≤ 1) →
      (∀ z ∈ γ.trace \ Z, Filter.Tendsto (fun n => A n z) Filter.atTop (nhds 0)) →
      ∀ q : ℂ → ℂ, ContinuousOn q γ.trace →
        Filter.Tendsto (fun n => γ.integral (fun z => A n z * q z))
          Filter.atTop (nhds 0)

def seam_multiplier_chain_integral_tendsto_type : Prop :=
  ∀ (Γ : IntegralChain) (Z : Set ℂ), Z.Countable →
    ∀ A : ℕ → ℂ → ℂ,
      (∀ n, ContinuousOn (A n) Γ.trace) →
      (∀ n z, z ∈ Γ.trace → ‖A n z‖ ≤ 1) →
      (∀ z ∈ Γ.trace \ Z, Filter.Tendsto (fun n => A n z) Filter.atTop (nhds 0)) →
      ∀ q : ℂ → ℂ, ContinuousOn q Γ.trace →
        Filter.Tendsto (fun n => Γ.integral (fun z => A n z * q z))
          Filter.atTop (nhds 0)

/-- Finite original subpaths are selected from an open cover by regular arc
charts and a seam neighborhood. Subpaths selected in that neighborhood have
zero contribution for fields vanishing there. No seam preimages are counted. -/
def finite_arc_selection_away_seams_type : Prop :=
  ∀ (γ : PiecewiseC1Path) {ι : Type} (V : Set ℂ) (U : ι → Set ℂ)
    (g : ι → ℝ → ℂ) (a b : ι → ℝ) (W : ι → Set ℝ),
    IsOpen V → (∀ j, IsOpen (U j)) → γ.trace ⊆ V ∪ ⋃ j, U j →
    (∀ j, γ.trace ∩ U j ⊆ g j '' Icc (a j) (b j)) →
    (∀ j, IsOpen (W j) ∧ Icc (a j) (b j) ⊆ W j ∧
      ContDiffOn ℝ 1 (g j) (W j) ∧ InjOn (g j) (Icc (a j) (b j)) ∧
      ∀ s ∈ Icc (a j) (b j), deriv (g j) s ≠ 0) →
    ∃ (n : ℕ) (node : Fin (n + 1) → ℝ) (select : Fin n → Option ι)
      (δ : Fin n → PiecewiseC1Path),
      Monotone node ∧ node 0 = γ.path.a ∧ node (Fin.last n) = γ.path.b ∧
      (∀ k, (δ k).path.a = node k.castSucc ∧ (δ k).path.b = node k.succ ∧
        EqOn (δ k) γ (Icc (node k.castSucc) (node k.succ)) ∧ (δ k).trace ⊆ γ.trace) ∧
      (∀ k, select k = none → (δ k).trace ⊆ V) ∧
      (∀ k j, select k = some j → (δ k).trace ⊆ U j ∧
        ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc (δ k).path.a (δ k).path.b) ∧
          MapsTo φ (Icc (δ k).path.a (δ k).path.b) (Icc (a j) (b j)) ∧
          EqOn (δ k) (g j ∘ φ) (Icc (δ k).path.a (δ k).path.b) ∧
          (∀ l : Fin (δ k).partition.count, ContDiffOn ℝ 1 φ ((δ k).partition.pieceSet l)) ∧
          ∀ q : ℂ → ℂ, ContinuousOn q (g j '' Icc (a j) (b j)) →
            (δ k).integral q = ∫ s in φ (δ k).path.a..φ (δ k).path.b,
              q (g j s) * deriv (g j) s) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q γ.trace → EqOn q 0 (γ.trace ∩ V) →
        γ.integral q = ∑ k ∈ Finset.univ.filter (fun k => (select k).isSome),
          (δ k).integral q

open scoped ContDiff

/-- Smooth cutoffs exist for every closed geometric seam, including the empty
set. They are one on an open neighborhood of the seam, and eventually zero
at each point outside it. No finiteness of any parameter preimage is needed. -/
def smooth_seam_cutoffs_type : Prop :=
  ∀ Z : Set ℂ, IsClosed Z →
    ∃ (A : ℕ → ℂ → ℝ) (V : ℕ → Set ℂ),
      (∀ n, ContDiff ℝ ∞ (A n)) ∧
      (∀ n z, A n z ∈ Icc (0 : ℝ) 1) ∧
      (∀ n, IsOpen (V n) ∧ Z ⊆ V n ∧ EqOn (A n) 1 (V n)) ∧
      ∀ z ∉ Z, ∀ᶠ n in Filter.atTop, A n z = 0

/-- Removing smooth neighborhoods of a closed countable seam recovers the
original signed-chain integral for every continuous field on its trace. -/
def smooth_seam_removal_type : Prop :=
  ∀ (Γ : IntegralChain) (Z : Set ℂ), IsClosed Z → Z.Countable →
    ∃ (χ : ℕ → ℂ → ℝ) (V : ℕ → Set ℂ),
      (∀ n, ContDiff ℝ ∞ (χ n)) ∧
      (∀ n z, χ n z ∈ Icc (0 : ℝ) 1) ∧
      (∀ n, IsOpen (V n) ∧ Z ⊆ V n ∧ EqOn (χ n) 0 (V n)) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q Γ.trace →
        Filter.Tendsto (fun n => Γ.integral (fun z => (χ n z : ℂ) * q z))
          Filter.atTop (nhds (Γ.integral q))

/-- An analytic extension lemma, not an original-boundary relation: equality
for seam-avoiding smooth multiples of a fixed field extends to that field.
The geometric comparison supplying the displayed equality is still required. -/
def chain_comparison_of_smooth_seam_removal_type : Prop :=
  ∀ (Γ Δ : IntegralChain) (Z : Set ℂ), IsClosed Z → Z.Countable →
    ∀ q : ℂ → ℂ, ContinuousOn q (Γ.trace ∪ Δ.trace) →
      (∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ →
        (∀ z, χ z ∈ Icc (0 : ℝ) 1) →
        (∃ V : Set ℂ, IsOpen V ∧ Z ⊆ V ∧ EqOn χ 0 V) →
        Γ.integral (fun z => (χ z : ℂ) * q z) =
          Δ.integral (fun z => (χ z : ℂ) * q z)) →
      Γ.integral q = Δ.integral q

/-- A directed interval is integrated with its actual signed incidence. -/
def directed_interval_integral_type : Prop :=
  ∀ (a b u v : ℝ), u ∈ Icc a b → v ∈ Icc a b →
    ∀ g : ℝ → ℂ, ContinuousOn g (Icc a b) →
      (∫ t in a..b, (directedIntervalMultiplicity u v t : ℂ) * g t) =
        ∫ t in u..v, g t

/-- Finite signed occurrence comparison on a reference arc. This is a local
algebra lemma: the occurrence equality is explicit, rather than an integral
certificate, and must still be derived when applied to an original boundary. -/
def finite_directed_incidence_integral_type : Prop :=
  ∀ (a b : ℝ) (n m : ℕ) (u v : Fin n → ℝ) (x y : Fin m → ℝ)
    (c : Fin n → ℤ) (d : Fin m → ℤ),
    (∀ i, u i ∈ Icc a b ∧ v i ∈ Icc a b) →
    (∀ j, x j ∈ Icc a b ∧ y j ∈ Icc a b) →
    (∀ᵐ t ∂volume.restrict (Ioc a b),
      ∑ i, c i * directedIntervalMultiplicity (u i) (v i) t =
        ∑ j, d j * directedIntervalMultiplicity (x j) (y j) t) →
    ∀ g : ℝ → ℂ, ContinuousOn g (Icc a b) →
      (∑ i, (c i : ℂ) * ∫ t in u i..v i, g t) =
        ∑ j, (d j : ℂ) * ∫ t in x j..y j, g t

/-- The canonical inverse parameter, derived from trace containment, computes
the integral of any original traversal of one regular injective arc. -/
def arc_parameter_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) → η.trace ⊆ g '' Icc a b →
    MapsTo (arcParameter g a b η) (Icc η.path.a η.path.b) (Icc a b) ∧
      ∀ q : ℂ → ℂ, ContinuousOn q (g '' Icc a b) →
        η.integral q = ∫ s in arcParameter g a b η η.path.a..
          arcParameter g a b η η.path.b, q (g s) * deriv g s

/-- Local signed-incidence cancellation for finite families of actual original
paths. Parameters are recovered, and may pause or backtrack. The local
occurrence hypothesis remains to be derived from global boundary geometry. -/
def finite_arc_incidence_integral_type : Prop :=
  ∀ (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) →
    ∀ (n m : ℕ) (η : Fin n → PiecewiseC1Path) (θ : Fin m → PiecewiseC1Path)
      (c : Fin n → ℤ) (d : Fin m → ℤ),
      (∀ i, (η i).trace ⊆ g '' Icc a b) →
      (∀ j, (θ j).trace ⊆ g '' Icc a b) →
      (∀ᵐ s ∂volume.restrict (Ioc a b),
        ∑ i, c i * arcTraversalMultiplicity g a b (η i) s =
          ∑ j, d j * arcTraversalMultiplicity g a b (θ j) s) →
      ∀ q : ℂ → ℂ, ContinuousOn q (g '' Icc a b) →
        (∑ i, (c i : ℂ) * (η i).integral q) =
          ∑ j, (d j : ℂ) * (θ j).integral q

/-- Almost every scalar value avoids the countably many exceptional parameters
and all critical values. Its entire original compact-interval fiber is finite.
The exceptional parameter set may include corners and both endpoints. -/
def regular_values_on_interval_type : Prop :=
  ∀ (φ : ℝ → ℝ) (c d : ℝ) (B : Set ℝ), B.Countable →
    ContinuousOn φ (Icc c d) →
    (∀ t ∈ Icc c d \ B, DifferentiableAt ℝ φ t) →
    ∀ᵐ s : ℝ,
      {t : ℝ | t ∈ Icc c d ∧ φ t = s}.Finite ∧
      ∀ t ∈ Icc c d, φ t = s →
        t ∉ B ∧ DifferentiableAt ℝ φ t ∧ deriv φ t ≠ 0

/-- Recovered parameters have the actual original path's piecewise C1
regularity. No regularity or speed condition is imposed on the original path. -/
def arc_parameter_regular_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) → η.trace ⊆ g '' Icc a b →
    ContinuousOn (arcParameter g a b η) (Icc η.path.a η.path.b) ∧
      MapsTo (arcParameter g a b η) (Icc η.path.a η.path.b) (Icc a b) ∧
      EqOn η (g ∘ arcParameter g a b η) (Icc η.path.a η.path.b) ∧
      ∀ i : Fin η.partition.count,
        ContDiffOn ℝ 1 (arcParameter g a b η) (η.partition.pieceSet i)

/-- Almost every point of a regular reference arc has finitely many original
visits, all at interior smooth parameters with nonzero original velocity.
The theorem allows stationary points, pauses, and infinitely many visits at
exceptional arc points; it does not count preimages of a prescribed seam. -/
def arc_regular_values_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) → η.trace ⊆ g '' Icc a b →
    ∀ᵐ s ∂volume.restrict (Icc a b),
      {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s}.Finite ∧
      ∀ t ∈ Icc η.path.a η.path.b, η t = g s →
        t ∈ Ioo η.path.a η.path.b ∧
        t ∉ Set.range η.partition.node ∧
        DifferentiableAt ℝ η t ∧ deriv η t ≠ 0

/-- One-dimensional signed degree is the actual signed number of regular
visits. This lemma does not suppose that the path is monotone. -/
def regular_value_signed_count_type : Prop :=
  ∀ (φ : ℝ → ℝ) (c d s : ℝ), c ≤ d → ContinuousOn φ (Icc c d) →
    φ c ≠ s → φ d ≠ s →
    (∀ t ∈ Icc c d, φ t = s → DifferentiableAt ℝ φ t ∧ deriv φ t ≠ 0) →
    ∀ hf : {t : ℝ | t ∈ Icc c d ∧ φ t = s}.Finite,
      (∑ t ∈ hf.toFinset, if 0 < deriv φ t then (1 : ℤ) else -1) =
        directedIntervalMultiplicity (φ c) (φ d) s

/-- The directed endpoint incidence is derived from actual original signed
visits, for almost every point of the reference arc. -/
def arc_signed_multiplicity_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) → η.trace ⊆ g '' Icc a b →
    ∀ᵐ s ∂volume.restrict (Icc a b),
      arcSignedMultiplicity g a b η s = arcTraversalMultiplicity g a b η s

/-- Signed counting representation for one actual original traversal. The
original path may pause or backtrack arbitrarily within its PC1 regularity. -/
def arc_occurrence_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) → η.trace ⊆ g '' Icc a b →
    ∀ q : ℂ → ℂ, ContinuousOn q (g '' Icc a b) →
      η.integral q = ∫ s in a..b,
        (arcSignedMultiplicity g a b η s : ℂ) * (q (g s) * deriv g s)

/-- Local signed comparison uses actual original visit counts. Equality of
endpoint incidences is a proved consequence, not an additional premise. -/
def finite_arc_occurrence_integral_type : Prop :=
  ∀ (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) →
    ∀ (n m : ℕ) (η : Fin n → PiecewiseC1Path) (θ : Fin m → PiecewiseC1Path)
      (c : Fin n → ℤ) (d : Fin m → ℤ),
      (∀ i, (η i).trace ⊆ g '' Icc a b) →
      (∀ j, (θ j).trace ⊆ g '' Icc a b) →
      (∀ᵐ s ∂volume.restrict (Ioc a b),
        ∑ i, c i * arcSignedMultiplicity g a b (η i) s =
          ∑ j, d j * arcSignedMultiplicity g a b (θ j) s) →
      ∀ q : ℂ → ℂ, ContinuousOn q (g '' Icc a b) →
        (∑ i, (c i : ℂ) * (η i).integral q) =
          ∑ j, (d j : ℂ) * (θ j).integral q

/-- Orientation in the recovered coordinate is the actual original velocity
relative to the chosen reference tangent, including zero original velocity. -/
def arc_velocity_relation_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) → η.trace ⊆ g '' Icc a b →
    ∀ t ∈ Icc η.path.a η.path.b, t ∉ Set.range η.partition.node →
      HasDerivAt η
        (deriv (arcParameter g a b η) t •
          deriv g (arcParameter g a b η t)) t


/-- A null set has null preimage on the noncritical part of a real C1 map; no global injectivity is required. -/
def noncritical_preimage_null_type : Prop :=
  ∀ (f : ℝ → ℝ) (V N : Set ℝ)
    (_hV : IsOpen V) (_hf : ContDiffOn ℝ 1 f V) (_hN : volume N = 0),
    volume {x | x ∈ V ∧ f x ∈ N ∧ deriv f x ≠ 0} = 0

/-- Finite regular original visits almost everywhere on a regular reference curve, without trace containment or global injectivity of that reference curve. -/
def regular_curve_visit_values_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_habV : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0),
    ∀ᵐ s ∂volume.restrict (Icc a b),
      {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s}.Finite ∧
      ∀ t ∈ Icc η.path.a η.path.b, η t = g s →
        t ∈ Ioo η.path.a η.path.b ∧ t ∉ Set.range η.partition.node ∧
        DifferentiableAt ℝ η t ∧ deriv η t ≠ 0

/-- The recovered-coordinate count equals the actual velocity count on a regular injective arc. -/
def arc_tangent_signed_multiplicity_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hinj : InjOn g (Icc a b))
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (_htrace : η.trace ⊆ g '' Icc a b),
    ∀ᵐ s ∂volume.restrict (Icc a b),
      arcSignedMultiplicity g a b η s = tangentSignedMultiplicity η (g s) (deriv g s)

/-- Actual signed visit counts subdivide away from node images whenever the actual original fiber is finite. No finiteness of a prescribed seam preimage is assumed. -/
def tangent_signed_multiplicity_subdivision_type : Prop :=
  ∀ (η : PiecewiseC1Path)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (_hm : Monotone node)
    (_ha : node 0 = η.path.a) (_hb : node (Fin.last n) = η.path.b)
    (δ : Fin n → PiecewiseC1Path)
    (_hδ : ∀ i, (δ i).path.a = node i.castSucc ∧ (δ i).path.b = node i.succ ∧
      EqOn (δ i) η (Icc (node i.castSucc) (node i.succ)))
    (z v : ℂ) (_hz : z ∉ η '' Set.range node)
    (_hf : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = z}.Finite),
    tangentSignedMultiplicity η z v = ∑ i, tangentSignedMultiplicity (δ i) z v

/-- A regular reference curve avoids a countable geometric set almost everywhere in its own reference parameter. -/
def regular_curve_avoids_countable_type : Prop :=
  ∀ (g : ℝ → ℂ) (a b : ℝ)
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (Z : Set ℂ) (_hZ : Z.Countable),
    ∀ᵐ s ∂volume.restrict (Icc a b), g s ∉ Z

/-- Actual signed visit counts subdivide almost everywhere along any regular reference curve, including when the original closed path leaves that curve. -/
def tangent_signed_multiplicity_subdivision_ae_type : Prop :=
  ∀ (η : PiecewiseC1Path)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (_hm : Monotone node)
    (_ha : node 0 = η.path.a) (_hb : node (Fin.last n) = η.path.b)
    (δ : Fin n → PiecewiseC1Path)
    (_hδ : ∀ i, (δ i).path.a = node i.castSucc ∧ (δ i).path.b = node i.succ ∧
      EqOn (δ i) η (Icc (node i.castSucc) (node i.succ)))
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V)
    (_hsub : Icc a b ⊆ V) (_hg : ContDiffOn ℝ 1 g V)
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0),
    ∀ᵐ s ∂volume.restrict (Icc a b),
      tangentSignedMultiplicity η (g s) (deriv g s) =
        ∑ i, tangentSignedMultiplicity (δ i) (g s) (deriv g s)

/-- Integrability and the original local arc integral are computed by actual original velocity counts. -/
def arc_tangent_occurrence_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hinj : InjOn g (Icc a b))
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (_htrace : η.trace ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (_hq : ContinuousOn q (g '' Icc a b)),
    IntervalIntegrable (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) volume a b ∧
    η.integral q = ∫ s in a..b,
      (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)

/-- Ambient localization removes whole-path containment: only the portion inside U must lie in the regular reference arc. The field has closed support in U. -/
def localized_tangent_occurrence_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path)
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V)
    (_hsub : Icc a b ⊆ V) (_hg : ContDiffOn ℝ 1 g V)
    (_hinj : InjOn g (Icc a b)) (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (U : Set ℂ) (_hU : IsOpen U) (_htrace : η.trace ∩ U ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (_hq : ContinuousOn q (η.trace ∪ g '' Icc a b))
    (_hsupp : tsupport q ⊆ U) (_hab : a ≤ b),
    IntervalIntegrable (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) volume a b ∧
    η.integral q = ∫ s in a..b,
      (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)

/-- The local representation retains every original signed-chain coefficient and parameter interval, including an empty chain. -/
def localized_chain_tangent_occurrence_integral_type : Prop :=
  ∀ (Γ : IntegralChain)
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V)
    (_hsub : Icc a b ⊆ V) (_hg : ContDiffOn ℝ 1 g V)
    (_hinj : InjOn g (Icc a b)) (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (U : Set ℂ) (_hU : IsOpen U) (_htrace : Γ.trace ∩ U ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (_hq : ContinuousOn q (Γ.trace ∪ g '' Icc a b))
    (_hsupp : tsupport q ⊆ U) (_hab : a ≤ b),
    Γ.integral q = ∫ s in a..b,
      (chainTangentMultiplicity Γ (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)

/-- Equality of actual original signed visits implies equality of integrals for fields supported in the arc chart. The local arc geometry and count comparison remain explicit hypotheses, not a claimed source boundary relation. -/
def localized_chain_occurrence_comparison_type : Prop :=
  ∀ (Γ Δ : IntegralChain)
    (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V)
    (_hsub : Icc a b ⊆ V) (_hg : ContDiffOn ℝ 1 g V)
    (_hinj : InjOn g (Icc a b)) (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (U : Set ℂ) (_hU : IsOpen U)
    (_htrace : (Γ.trace ∪ Δ.trace) ∩ U ⊆ g '' Icc a b)
    (_hcount : ∀ᵐ s ∂volume.restrict (Ioc a b),
      chainTangentMultiplicity Γ (g s) (deriv g s) =
        chainTangentMultiplicity Δ (g s) (deriv g s))
    (q : ℂ → ℂ) (_hq : ContinuousOn q ((Γ.trace ∪ Δ.trace) ∪ g '' Icc a b))
    (_hsupp : tsupport q ⊆ U) (_hab : a ≤ b),
    Γ.integral q = Δ.integral q

/-- Further partial interfaces for measurable coincidence pieces and their derived charts.
These do not assert the global boundary dictionary. -/
def coincidence_deriv_exception_countable_type : Prop :=
  ∀ (f g : ℝ → ℂ),
    {t : ℝ | f t = g t ∧ DifferentiableAt ℝ f t ∧ DifferentiableAt ℝ g t ∧
      deriv f t ≠ deriv g t}.Countable

def deriv_eq_ae_on_coincidence_type : Prop :=
  ∀ (f g : ℝ → ℂ),
    ∀ᵐ t : ℝ, f t = g t → DifferentiableAt ℝ f t →
      DifferentiableAt ℝ g t → deriv f t = deriv g t

def coincidence_velocity_relation_ae_type : Prop :=
  ∀ (η g : ℝ → ℂ) (φ : ℝ → ℝ)
    (S : Set ℝ) (_hS : MeasurableSet S) (_heq : EqOn η (g ∘ φ) S)
    (_hη : ∀ t ∈ S, DifferentiableAt ℝ η t)
    (_hφ : ∀ t ∈ S, DifferentiableAt ℝ φ t)
    (_hg : ∀ t ∈ S, DifferentiableAt ℝ g (φ t)),
    ∀ᵐ t ∂volume.restrict S, deriv η t = deriv φ t • deriv g (φ t)

def coincidence_change_of_variables_type : Prop :=
  ∀ (η g : ℝ → ℂ) (φ : ℝ → ℝ)
    (S : Set ℝ) (_hS : MeasurableSet S) (_heq : EqOn η (g ∘ φ) S)
    (_hη : ∀ t ∈ S, DifferentiableAt ℝ η t)
    (_hφ : ∀ t ∈ S, DifferentiableAt ℝ φ t)
    (_hg : ∀ t ∈ S, DifferentiableAt ℝ g (φ t))
    (_hinj : InjOn φ S) (q : ℂ → ℂ),
    let F : ℝ → ℂ := fun s =>
      Real.sign (deriv φ (Function.invFunOn φ S s)) • (q (g s) * deriv g s)
    (IntegrableOn (fun t => q (η t) * deriv η t) S ↔ IntegrableOn F (φ '' S)) ∧
      (∫ t in S, q (η t) * deriv η t) = ∫ s in φ '' S, F s

def regular_coincidence_chart_type : Prop :=
  ∀ (f g : ℝ → ℂ) (t s : ℝ)
    (_hf : ContDiffAt ℝ 1 f t) (_hg : ContDiffAt ℝ 1 g s)
    (_hfr : deriv f t ≠ 0) (_hgr : deriv g s ≠ 0) (_he : f t = g s),
    ∃ (U W : Set ℝ) (φ : ℝ → ℝ),
      IsOpen U ∧ t ∈ U ∧ IsOpen W ∧ s ∈ W ∧
      ContDiffOn ℝ 1 f U ∧ ContDiffOn ℝ 1 g W ∧
      ContDiffOn ℝ 1 φ U ∧ InjOn φ U ∧ MapsTo φ U W ∧
      ∀ u ∈ U, ∀ v ∈ W, f u = g v → φ u = v

def countable_regular_coincidence_charts_type : Prop :=
  ∀ (f g : ℝ → ℂ) (C : Set (ℝ × ℝ))
    (_hC : ∀ p ∈ C, ContDiffAt ℝ 1 f p.1 ∧ ContDiffAt ℝ 1 g p.2 ∧
      deriv f p.1 ≠ 0 ∧ deriv g p.2 ≠ 0 ∧ f p.1 = g p.2),
    ∃ (T : Set (ℝ × ℝ)), T.Countable ∧ T ⊆ C ∧
      ∃ (U W : (ℝ × ℝ) → Set ℝ) (φ : (ℝ × ℝ) → ℝ → ℝ),
        (∀ p ∈ T, IsOpen (U p) ∧ p.1 ∈ U p ∧ IsOpen (W p) ∧ p.2 ∈ W p ∧
          ContDiffOn ℝ 1 f (U p) ∧ ContDiffOn ℝ 1 g (W p) ∧
          ContDiffOn ℝ 1 (φ p) (U p) ∧ InjOn (φ p) (U p) ∧ MapsTo (φ p) (U p) (W p) ∧
          ∀ u ∈ U p, ∀ v ∈ W p, f u = g v → φ p u = v) ∧
        C ⊆ ⋃ p ∈ T, (U p) ×ˢ (W p)

def coincidence_chart_integral_type : Prop :=
  ∀ (f g : ℝ → ℂ) (U W : Set ℝ) (φ : ℝ → ℝ)
    (_hU : IsOpen U) (_hW : IsOpen W) (_hf : ContDiffOn ℝ 1 f U)
    (_hg : ContDiffOn ℝ 1 g W) (_hφ : ContDiffOn ℝ 1 φ U)
    (_hinj : InjOn φ U) (_hmaps : MapsTo φ U W)
    (_hmatch : ∀ u ∈ U, ∀ v ∈ W, f u = g v → φ u = v)
    (S : Set ℝ) (_hS : MeasurableSet S) (_hSU : S ⊆ U)
    (_htrace : ∀ u ∈ S, ∃ v ∈ W, f u = g v) (q : ℂ → ℂ),
    let F : ℝ → ℂ := fun s =>
      Real.sign (deriv φ (Function.invFunOn φ S s)) • (q (g s) * deriv g s)
    (IntegrableOn (fun t => q (f t) * deriv f t) S ↔ IntegrableOn F (φ '' S)) ∧
      (∫ t in S, q (f t) * deriv f t) = ∫ s in φ '' S, F s

def coincidence_tangent_change_of_variables_type : Prop :=
  ∀ (η g : ℝ → ℂ) (φ : ℝ → ℝ)
    (S : Set ℝ) (_hS : MeasurableSet S) (_heq : EqOn η (g ∘ φ) S)
    (_hη : ∀ t ∈ S, DifferentiableAt ℝ η t)
    (_hφ : ∀ t ∈ S, DifferentiableAt ℝ φ t)
    (_hg : ∀ t ∈ S, DifferentiableAt ℝ g (φ t))
    (_hreg : ∀ t ∈ S, deriv g (φ t) ≠ 0) (_hinj : InjOn φ S) (q : ℂ → ℂ),
    let F : ℝ → ℂ := fun s =>
      Real.sign ((deriv η (Function.invFunOn φ S s) / deriv g s).re) •
        (q (g s) * deriv g s)
    (IntegrableOn (fun t => q (η t) * deriv η t) S ↔ IntegrableOn F (φ '' S)) ∧
      (∫ t in S, q (η t) * deriv η t) = (∫ s in φ '' S, F s) ∧
      (∫ t in S, ‖q (η t) * deriv η t‖) = ∫ s in φ '' S, ‖F s‖

def pc1_regular_coincidence_charts_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0),
    ∃ (T : Set (ℝ × ℝ)), T.Countable ∧
      ∃ (U W : (ℝ × ℝ) → Set ℝ) (φ : (ℝ × ℝ) → ℝ → ℝ),
        (∀ p ∈ T, IsOpen (U p) ∧ p.1 ∈ U p ∧ IsOpen (W p) ∧ p.2 ∈ W p ∧
          ContDiffOn ℝ 1 η (U p) ∧ ContDiffOn ℝ 1 g (W p) ∧
          ContDiffOn ℝ 1 (φ p) (U p) ∧ InjOn (φ p) (U p) ∧ MapsTo (φ p) (U p) (W p) ∧
          ∀ u ∈ U p, ∀ v ∈ W p, η u = g v → φ p u = v) ∧
        ∀ᵐ s ∂volume.restrict (Icc a b),
          ∀ t ∈ Icc η.path.a η.path.b, η t = g s →
            ∃ p ∈ T, t ∈ U p ∧ s ∈ W p

def tangent_signed_multiplicity_of_injective_type : Prop :=
  ∀ (η : PiecewiseC1Path)
    (_hinj : InjOn η (Icc η.path.a η.path.b)) (t : ℝ)
    (_ht : t ∈ Icc η.path.a η.path.b) (v : ℂ),
    tangentSignedMultiplicity η (η t) v =
      if 0 < (deriv η t / v).re then 1
      else if (deriv η t / v).re < 0 then -1 else 0

def cellContour_tangent_multiplicity_type : Prop :=
  ∀ {O : Set (E 2)} (C : Chain 1 1 O) (z v : ℂ),
    chainTangentMultiplicity (cellContour C) z v =
      C.sum (fun c m => m * tangentSignedMultiplicity (cellPath c) z v)

def cell_assembly_tangent_multiplicity_type : Prop :=
  ∀ {O : Set (E 2)} (d : PositiveCellData O)
    (z v : ℂ),
    chainTangentMultiplicity d.faceContour z v =
      ∑ j, ∑ i : Fin 2, (-1 : ℤ) ^ i.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells j) i true)) z v -
          tangentSignedMultiplicity (cellPath (cellFace (d.cells j) i false)) z v)

/-- Countable disjoint measurable coincidence pieces are constructed from the
original PC1 path and a regular reference. Whole-path containment, regular
original velocity, and an assumed measurable atlas are not hypotheses. -/
def pc1_coincidence_partition_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ),
    IsOpen V → Icc a b ⊆ V → ContDiffOn ℝ 1 g V →
    (∀ s ∈ Icc a b, deriv g s ≠ 0) →
    Nonempty (ArcCoincidencePartition η g a b)

/-- Further proved partial interfaces: measurable many-to-one transport and
finite regular-carrier comparison. These do not define a full positive boundary
or assert its induced geometric cell incidence. -/
def regularArcSource_measurable_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (_hg : ContinuousOn g (Icc a b)),
    MeasurableSet (regularArcSource η g a b)


def coincidence_partition_transport_type : Prop :=
  ∀ {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (V : Set ℝ) (_hV : IsOpen V)
    (_hsub : Icc a b ⊆ V) (_hg : ContDiffOn ℝ 1 g V)
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (q : ℂ → ℂ) (n : ℕ),
    (IntegrableOn (fun t => q (η t) * deriv η t) (P.piece n) ↔
      Integrable (P.density q n)) ∧
    (∫ t in P.piece n, q (η t) * deriv η t) = ∫ s, P.density q n s ∧
    (∫ t in P.piece n, ‖q (η t) * deriv η t‖) = ∫ s, ‖P.density q n s‖

def coincidence_partition_hasSum_transport_type : Prop :=
  ∀ {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (V : Set ℝ) (_hV : IsOpen V)
    (_hsub : Icc a b ⊆ V) (_hg : ContDiffOn ℝ 1 g V)
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0) (q : ℂ → ℂ)
    (_hq : IntegrableOn (fun t => q (η t) * deriv η t) (regularArcSource η g a b)),
    (∀ n, Integrable (P.density q n)) ∧
    HasSum (fun n => ∫ s, P.density q n s)
      (∫ t in regularArcSource η g a b, q (η t) * deriv η t) ∧
    HasSum (fun n => ∫ s, ‖P.density q n s‖)
      (∫ t in regularArcSource η g a b, ‖q (η t) * deriv η t‖)

def coincidence_partition_density_sum_type : Prop :=
  ∀ {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (_hinj : InjOn g (Icc a b))
    (s : ℝ) (_hs : s ∈ Icc a b)
    (_hf : {t : ℝ | t ∈ Icc η.path.a η.path.b ∧ η t = g s}.Finite)
    (_hgood : ∀ t ∈ Icc η.path.a η.path.b, η t = g s →
      t ∉ Set.range η.partition.node ∧ deriv η t ≠ 0)
    (q : ℂ → ℂ),
    (∑' n, P.density q n s) =
      (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)

def coincidence_partition_occurrence_integral_type : Prop :=
  ∀ {η : PiecewiseC1Path} {g : ℝ → ℂ} {a b : ℝ}
    (P : ArcCoincidencePartition η g a b) (V : Set ℝ) (_hV : IsOpen V)
    (_hsub : Icc a b ⊆ V) (_hg : ContDiffOn ℝ 1 g V)
    (_hinj : InjOn g (Icc a b)) (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (q : ℂ → ℂ)
    (_hq : IntegrableOn (fun t => q (η t) * deriv η t) (regularArcSource η g a b)),
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) (Icc a b) ∧
    (∫ t in regularArcSource η g a b, q (η t) * deriv η t) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)

def path_arc_indicator_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (_hg : ContinuousOn g (Icc a b))
    (q : ℂ → ℂ)
    (_hq : IntegrableOn (fun t => q (η t) * deriv η t) (Icc η.path.a η.path.b)),
    η.integral ((g '' Icc a b).indicator q) =
      ∫ t in regularArcSource η g a b, q (η t) * deriv η t

def pc1_arc_coincidence_integral_of_integrable_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hinj : InjOn g (Icc a b))
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (q : ℂ → ℂ)
    (_hparam : IntegrableOn (fun t => q (η t) * deriv η t) (Icc η.path.a η.path.b)),
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) (Icc a b) ∧
    η.integral ((g '' Icc a b).indicator q) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)

def pc1_arc_coincidence_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hinj : InjOn g (Icc a b))
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (q : ℂ → ℂ) (_hq : ContinuousOn q η.trace),
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (q (g s) * deriv g s)) (Icc a b) ∧
    η.integral ((g '' Icc a b).indicator q) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) * (q (g s) * deriv g s)

def pc1_arc_subset_integral_type : Prop :=
  ∀ (η : PiecewiseC1Path) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hinj : InjOn g (Icc a b))
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (S : Set ℂ) (_hS : MeasurableSet S) (_hSK : S ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (_hq : ContinuousOn q η.trace),
    IntegrableOn (fun s => (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
      (S.indicator q (g s) * deriv g s)) (Icc a b) ∧
    η.integral (S.indicator q) =
      ∫ s in Icc a b,
        (tangentSignedMultiplicity η (g s) (deriv g s) : ℂ) *
          (S.indicator q (g s) * deriv g s)

def chain_arc_subset_integral_type : Prop :=
  ∀ (Γ : IntegralChain) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hinj : InjOn g (Icc a b))
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (S : Set ℂ) (_hS : MeasurableSet S) (_hSK : S ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (_hq : ContinuousOn q Γ.trace),
    IntegrableOn (fun s => (chainTangentMultiplicity Γ (g s) (deriv g s) : ℂ) *
      (S.indicator q (g s) * deriv g s)) (Icc a b) ∧
    Γ.integral (S.indicator q) =
      ∫ s in Icc a b,
        (chainTangentMultiplicity Γ (g s) (deriv g s) : ℂ) *
          (S.indicator q (g s) * deriv g s)

def chain_arc_subset_comparison_type : Prop :=
  ∀ (Γ Δ : IntegralChain) (g : ℝ → ℂ)
    (a b : ℝ) (V : Set ℝ) (_hV : IsOpen V) (_hsub : Icc a b ⊆ V)
    (_hg : ContDiffOn ℝ 1 g V) (_hinj : InjOn g (Icc a b))
    (_hreg : ∀ s ∈ Icc a b, deriv g s ≠ 0)
    (_hcount : ∀ᵐ s ∂volume.restrict (Icc a b),
      chainTangentMultiplicity Γ (g s) (deriv g s) =
        chainTangentMultiplicity Δ (g s) (deriv g s))
    (S : Set ℂ) (_hS : MeasurableSet S) (_hSK : S ⊆ g '' Icc a b)
    (q : ℂ → ℂ) (_hq : ContinuousOn q (Γ.trace ∪ Δ.trace)),
    Γ.integral (S.indicator q) = Δ.integral (S.indicator q)

def path_integral_indicator_iUnion_type : Prop :=
  ∀ (η : PiecewiseC1Path) {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (_hS : ∀ i, MeasurableSet (S i))
    (_hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (q : ℂ → ℂ) (_hq : ContinuousOn q η.trace),
    η.integral ((⋃ i, S i).indicator q) = ∑ i, η.integral ((S i).indicator q)

def chain_integral_indicator_iUnion_type : Prop :=
  ∀ (Γ : IntegralChain) {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (_hS : ∀ i, MeasurableSet (S i))
    (_hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (q : ℂ → ℂ) (_hq : ContinuousOn q Γ.trace),
    Γ.integral ((⋃ i, S i).indicator q) = ∑ i, Γ.integral ((S i).indicator q)

def finite_regular_arc_comparison_type : Prop :=
  ∀ (Γ Δ : IntegralChain)
    (n : ℕ) (g : Fin n → ℝ → ℂ) (a b : Fin n → ℝ) (V : Fin n → Set ℝ)
    (_hV : ∀ i, IsOpen (V i)) (_hsub : ∀ i, Icc (a i) (b i) ⊆ V i)
    (_hg : ∀ i, ContDiffOn ℝ 1 (g i) (V i))
    (_hinj : ∀ i, InjOn (g i) (Icc (a i) (b i)))
    (_hreg : ∀ i s, s ∈ Icc (a i) (b i) → deriv (g i) s ≠ 0)
    (Z : Set ℂ) (_hZ : Z.Countable)
    (_hcover : Γ.trace ∪ Δ.trace ⊆ Z ∪ ⋃ i, g i '' Icc (a i) (b i))
    (_hcount : ∀ i, ∀ᵐ s ∂volume.restrict (Icc (a i) (b i)),
      chainTangentMultiplicity Γ (g i s) (deriv (g i) s) =
        chainTangentMultiplicity Δ (g i s) (deriv (g i) s))
    (q : ℂ → ℂ) (_hq : ContinuousOn q (Γ.trace ∪ Δ.trace)),
    Γ.integral q = Δ.integral q

/-- Additional partial geometry and cell-specialized comparison interfaces.
The two face-incidence theorems explicitly retain the original cycle's
signed-incidence hypothesis. They do not define or prove admission of a full
positive boundary and are not the final source-facing theorem. -/
def cell_interior_image_mem_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    {x : E 2} (_hx : x ∈ interior (cube 2)),
    cellExtension c x ∈ interior (cellExtension c '' cube 2)

def cell_image_frontier_subset_faces_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det),
    frontier (cellExtension c '' cube 2) ⊆
      ⋃ i : Fin 2, ⋃ e : Bool, cellExtension (cellFace c i e) '' cube 1

def cell_data_carrier_compact_type : Prop :=
  ∀ {O : Set (E 2)} (d : PositiveCellData O),
    IsCompact d.carrier

def cell_data_frontier_subset_faceCarrier_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O),
    frontier d.carrier ⊆ d.faceCarrier

def finite_regular_arc_comparison_fintype_type : Prop :=
  ∀ (Γ Δ : IntegralChain)
    {ι : Type*} [Fintype ι] (g : ι → ℝ → ℂ) (a b : ι → ℝ) (V : ι → Set ℝ)
    (_hV : ∀ i, IsOpen (V i)) (_hsub : ∀ i, Icc (a i) (b i) ⊆ V i)
    (_hg : ∀ i, ContDiffOn ℝ 1 (g i) (V i))
    (_hinj : ∀ i, InjOn (g i) (Icc (a i) (b i)))
    (_hreg : ∀ i s, s ∈ Icc (a i) (b i) → deriv (g i) s ≠ 0)
    (Z : Set ℂ) (_hZ : Z.Countable)
    (_hcover : Γ.trace ∪ Δ.trace ⊆ Z ∪ ⋃ i, g i '' Icc (a i) (b i))
    (_hcount : ∀ i, ∀ᵐ s ∂volume.restrict (Icc (a i) (b i)),
      chainTangentMultiplicity Γ (g i s) (deriv (g i) s) =
        chainTangentMultiplicity Δ (g i s) (deriv (g i) s))
    (q : ℂ → ℂ) (_hq : ContinuousOn q (Γ.trace ∪ Δ.trace)),
    Γ.integral q = Δ.integral q

def cell_data_faceContour_trace_subset_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O),
    d.faceContour.trace ⊆ d.faceCarrier

def cell_data_faceCarrier_subset_ambient_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O),
    d.faceCarrier ⊆ complexCoordinates ⁻¹' O

def cell_comparison_of_face_incidence_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralChain)
    (_hboundary : Γ.trace ⊆ frontier d.carrier)
    (_hcount : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      chainTangentMultiplicity Γ (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s) =
      ∑ k, ∑ l : Fin 2, (-1 : ℤ) ^ l.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l true))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s) -
        tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l false))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (_hq : ContinuousOn q (complexCoordinates ⁻¹' O)),
    Γ.integral q = d.faceContour.integral q

def cell_dictionary_of_face_incidence_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralChain)
    (_hboundary : Γ.trace ⊆ frontier d.carrier)
    (_hcount : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      chainTangentMultiplicity Γ (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s) =
      ∑ k, ∑ l : Fin 2, (-1 : ℤ) ^ l.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l true))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s) -
        tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l false))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (_hq : ContinuousOn q (complexCoordinates ⁻¹' O)),
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer

def determinant_coordinates_type : Prop :=
  ∀ (A : E 2 →L[ℝ] E 2),
    A.det =
      (A (standardBasis 2 0)) 0 * (A (standardBasis 2 1)) 1 -
        (A (standardBasis 2 1)) 0 * (A (standardBasis 2 0)) 1

def cell_face_orientation_det_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1),
    ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) *
        (cellFaceInward c i e t).im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) *
        (cellFaceInward c i e t).re =
      (fderiv ℝ (cellExtension c) (faceInsertion i e (scalarLine t))).det

def cell_face_induced_orientation_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1),
    0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) *
        (cellFaceInward c i e t).im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) *
        (cellFaceInward c i e t).re

def cell_data_cell_interior_image_disjoint_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (i j : Fin d.count) (_hij : i ≠ j),
    Disjoint (cellExtension (d.cells i) '' interior (cube 2))
      (interior (cellExtension (d.cells j) '' cube 2))

def ambient_seams_null_type : Prop :=
  ∀ {k n : ℕ}
    (s : Specs.D04.C15.FiniteGeometricUnionIntegral.Model.AmbientSeams k n)
    (_hkn : k ≤ n),
    volume s.carrier = 0

def cell_data_cell_interiors_disjoint_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O),
    Pairwise (fun i j => Disjoint (interior (cellExtension (d.cells i) '' cube 2))
      (interior (cellExtension (d.cells j) '' cube 2)))

def cell_local_membership_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hinj : InjOn (cellExtension c) (cube 2))
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (x : E 2) (_hx : x ∈ cube 2),
    ∃ (e : OpenPartialHomeomorph (E 2) (E 2)) (W : Set (E 2)),
      (e : E 2 → E 2) = cellExtension c ∧ x ∈ e.source ∧
      ContDiffAt ℝ 1 e.symm (cellExtension c x) ∧
      IsOpen W ∧ cellExtension c x ∈ W ∧ W ⊆ e.target ∧
      ∀ y ∈ W, (y ∈ cellExtension c '' cube 2 ↔ e.symm y ∈ cube 2)

def cell_face_local_halfspace_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hinj : InjOn (cellExtension c) (cube 2))
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 1),
    let z := cellExtension c (faceInsertion i e (scalarLine t))
    ∃ (W : Set (E 2)) (φ : E 2 → ℝ), IsOpen W ∧ z ∈ W ∧
      ContDiffAt ℝ 1 φ z ∧ φ z = 0 ∧
      fderiv ℝ φ z (complexCoordinates (cellFaceInward c i e t)) = 1 ∧
      fderiv ℝ φ z (complexCoordinates (deriv (cellCurve (cellFace c i e)) t)) = 0 ∧
      ∀ y ∈ W, (y ∈ cellExtension c '' cube 2 ↔ 0 ≤ φ y)

def cell_face_inward_sides_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hinj : InjOn (cellExtension c) (cube 2))
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 1),
    let z := cellExtension c (faceInsertion i e (scalarLine t))
    let v := complexCoordinates (cellFaceInward c i e t)
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • v ∈ interior (cellExtension c '' cube 2) ∧
      z - r • v ∉ cellExtension c '' cube 2


/-- Further local geometric support. No original-boundary relation is assumed. -/
def cellCurve_face_value_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1),
    cellCurve (cellFace c i e) t =
      complexCoordinates.symm (cellExtension c (faceInsertion i e (scalarLine t)))

def linear_functional_area_type : Prop :=
  ∀ (L : ℂ →L[ℝ] ℝ) (v n w : ℂ),
    L w * (v.re * n.im - v.im * n.re) =
      L n * (v.re * w.im - v.im * w.re) -
        L v * (n.re * w.im - n.im * w.re)

def halfspace_transverse_sides_type : Prop :=
  ∀ (K W : Set (E 2)) (φ : E 2 → ℝ)
    (z w : E 2) (_hW : IsOpen W) (_hzW : z ∈ W)
    (_hφ : ContDiffAt ℝ 1 φ z) (_hzero : φ z = 0)
    (_hmem : ∀ y ∈ W, (y ∈ K ↔ 0 ≤ φ y))
    (_hpositive : 0 < fderiv ℝ φ z w),
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • w ∈ interior K ∧ z - r • w ∉ K

def cell_face_transverse_sides_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hinj : InjOn (cellExtension c) (cube 2))
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 1)
    (w : ℂ)
    (_hleft : 0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) * w.im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) * w.re),
    let z := cellExtension c (faceInsertion i e (scalarLine t))
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • complexCoordinates w ∈ interior (cellExtension c '' cube 2) ∧
      z - r • complexCoordinates w ∉ cellExtension c '' cube 2

def disjoint_cell_face_orientation_type : Prop :=
  ∀ {O : Set (E 2)} (c d : Cell 1 2 O)
    (_hc : InjOn (cellExtension c) (cube 2))
    (_hd : InjOn (cellExtension d) (cube 2))
    (_hpc : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (_hpd : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension d) x).det)
    (_hdisjoint : Disjoint (interior (cellExtension c '' cube 2))
      (interior (cellExtension d '' cube 2)))
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (_hs : s ∈ Ioo (0 : ℝ) 1)
    (_hpoint : cellCurve (cellFace c i e) t = cellCurve (cellFace d j f) s)
    (_htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace c i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace d j f)) s)),
    a < 0

def regular_curve_coincidence_tangents_type : Prop :=
  ∀ (f g : ℝ → ℂ) (U V : Set ℝ)
    (_hf : ∀ t ∈ U, ContDiffAt ℝ 1 f t) (_hg : ∀ s ∈ V, ContDiffAt ℝ 1 g s)
    (_hfr : ∀ t ∈ U, deriv f t ≠ 0) (_hgr : ∀ s ∈ V, deriv g s ≠ 0),
    ∀ᵐ t : ℝ, t ∈ U → ∀ s ∈ V, f t = g s →
      ∃ a : ℝ, a ≠ 0 ∧ deriv f t = a • deriv g s

def cell_data_contact_orientation_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (_hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (_hs : s ∈ Ioo (0 : ℝ) 1)
    (_hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (_htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s)),
    a < 0

def cell_data_contact_orientation_ae_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (_hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool),
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      t ∈ Ioo (0 : ℝ) 1 → ∀ s ∈ Ioo (0 : ℝ) 1,
        cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
        ∃ a : ℝ, a < 0 ∧
          (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
            a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s)

def cell_data_no_three_parallel_contacts_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l m : Fin d.count)
    (_hkl : k ≠ l) (_hkm : k ≠ m) (_hlm : l ≠ m)
    (i j q : Fin 2) (e f h : Bool) (t s u a b : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (_hs : s ∈ Ioo (0 : ℝ) 1)
    (_hu : u ∈ Ioo (0 : ℝ) 1)
    (_hpointl : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (_hpointm : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells m) q h) u)
    (_htangentl : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s))
    (_htangentm : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      b • ((cellFaceSign q h : ℝ) • deriv (cellCurve (cellFace (d.cells m) q h)) u)),
    False

def cell_data_at_most_two_face_contacts_ae_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool),
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      t ∈ Ioo (0 : ℝ) 1 → ∀ (l m : Fin d.count), k ≠ l → k ≠ m →
        ∀ (j q : Fin 2) (f h : Bool) (s u : ℝ),
          s ∈ Ioo (0 : ℝ) 1 → u ∈ Ioo (0 : ℝ) 1 →
          cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
          cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells m) q h) u →
          l = m

def cell_data_contact_cancellation_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (_hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (_hs : s ∈ Ioo (0 : ℝ) 1)
    (_hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (_htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s))
    (v : ℂ),
    cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
        (cellCurve (cellFace (d.cells k) i e) t) v +
      cellFaceSign j f * tangentSignedMultiplicity (cellPath (cellFace (d.cells l) j f))
        (cellCurve (cellFace (d.cells k) i e) t) v = 0

def cell_data_contact_cancellation_ae_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (_hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool),
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      t ∈ Ioo (0 : ℝ) 1 → ∀ s ∈ Ioo (0 : ℝ) 1,
        cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s →
        ∀ v : ℂ,
          cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
              (cellCurve (cellFace (d.cells k) i e) t) v +
            cellFaceSign j f * tangentSignedMultiplicity (cellPath (cellFace (d.cells l) j f))
              (cellCurve (cellFace (d.cells k) i e) t) v = 0

def cell_data_contact_two_sides_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (_hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (_ht : t ∈ Ioo (0 : ℝ) 1) (_hs : s ∈ Ioo (0 : ℝ) 1)
    (_hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s)
    (_htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s)),
    let z := cellExtension (d.cells k) (faceInsertion i e (scalarLine t))
    let w := complexCoordinates (cellFaceInward (d.cells k) i e t)
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • w ∈ interior (cellExtension (d.cells k) '' cube 2) ∧
      z - r • w ∈ interior (cellExtension (d.cells l) '' cube 2)

def geometric_boundary_jump_unique_type : Prop :=
  ∀ {K : Set ℂ} {z v : ℂ} {m n : ℤ}
    (_hm : GeometricBoundaryJump K z v m) (_hn : GeometricBoundaryJump K z v n),
    m = n

def cell_dictionary_of_boundary_jumps_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (_hΓ : IsFullPositiveBoundary d.carrier Γ)
    (_hfaces : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s)
        (chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (_hq : ContinuousOn q (complexCoordinates ⁻¹' O)),
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer

def cell_face_mem_closure_interior_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (_hinj : InjOn (cellExtension c) (cube 2))
    (_hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 1),
    cellExtension c (faceInsertion i e (scalarLine t)) ∈
      closure (interior (cellExtension c '' cube 2))

def cell_data_face_not_mem_other_interior_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (_hkl : k ≠ l)
    (i : Fin 2) (e : Bool) (t : ℝ) (_ht : t ∈ Ioo (0 : ℝ) 1),
    cellExtension (d.cells k) (faceInsertion i e (scalarLine t)) ∉
      interior (cellExtension (d.cells l) '' cube 2)

def geometric_boundary_jump_type := Set ℂ → ℂ → ℂ → ℤ → Prop

def geometric_boundary_jump_value : geometric_boundary_jump_type :=
  fun K z v m => ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
    K.indicator (fun _ => (1 : ℤ)) (z + r • (Complex.I * v)) -
      K.indicator (fun _ => (1 : ℤ)) (z - r • (Complex.I * v)) = m

def is_full_positive_boundary_type := Set ℂ → IntegralCycle → Prop

def is_full_positive_boundary_value : is_full_positive_boundary_type :=
  fun K Γ => Γ.trace = frontier K ∧
    ∀ (g : ℝ → ℂ) (a b : ℝ) (V : Set ℝ), IsOpen V → Icc a b ⊆ V →
      ContDiffOn ℝ 1 g V → InjOn g (Icc a b) →
      (∀ s ∈ Icc a b, deriv g s ≠ 0) →
      ∀ᵐ s ∂volume.restrict (Icc a b),
        GeometricBoundaryJump K (g s) (deriv g s)
          (chainTangentMultiplicity Γ.chain (g s) (deriv g s))


set_option linter.unusedVariables false

def faceInsertion_unique_type : Prop :=
  ∀ (i j : Fin 2) (e f : Bool) (t s : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (heq : faceInsertion i e (scalarLine t) = faceInsertion j f (scalarLine s)),
    i = j ∧ e = f ∧ t = s

def cell_face_value_unique_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (i j : Fin 2) (e f : Bool) (t s : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (heq : cellCurve (cellFace c i e) t = cellCurve (cellFace c j f) s),
    i = j ∧ e = f ∧ t = s

def cell_face_transverse_sides_complex_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (w : ℂ)
    (hleft : 0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).re) * w.im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace c i e)) t).im) * w.re),
    let z := cellCurve (cellFace c i e) t
    let K := complexCoordinates.symm '' (cellExtension c '' cube 2)
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      z + r • w ∈ K ∧ z - r • w ∉ K

def cell_face_normal_jump_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (hpos : ∀ x ∈ cube 2, 0 < (fderiv ℝ (cellExtension c) x).det)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1),
    GeometricBoundaryJump (complexCoordinates.symm '' (cellExtension c '' cube 2))
      (cellCurve (cellFace c i e) t) (deriv (cellCurve (cellFace c i e)) t)
      (cellFaceSign i e)

def jump_of_eventually_same_type : Prop :=
  ∀ {K L : Set ℂ} {z v : ℂ} {m : ℤ}
    (h : GeometricBoundaryJump L z v m)
    (hlocal : ∀ᶠ y in nhds z, (y ∈ K ↔ y ∈ L)),
    GeometricBoundaryJump K z v m

def cell_data_isolated_jump_type : Prop :=
  ∀ {O : Set (E 2)} (d : PositiveCellData O)
    (k : Fin d.count) (i : Fin 2) (e : Bool) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hisolated : ∀ l : Fin d.count, l ≠ k →
      cellCurve (cellFace (d.cells k) i e) t ∉
        complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)),
    GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells k) i e) t)
      (deriv (cellCurve (cellFace (d.cells k) i e)) t) (cellFaceSign i e)

def cell_data_contact_transverse_type : Prop :=
  ∀ {O : Set (E 2)} (d : PositiveCellData O)
    (k l : Fin d.count) (hkl : k ≠ l) (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s))
    (w : ℂ)
    (hleft : 0 < ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace (d.cells k) i e)) t).re) * w.im -
      ((cellFaceSign i e : ℝ) * (deriv (cellCurve (cellFace (d.cells k) i e)) t).im) * w.re),
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      cellCurve (cellFace (d.cells k) i e) t + r • w ∈ d.carrier ∧
      cellCurve (cellFace (d.cells k) i e) t - r • w ∈ d.carrier

def cell_data_contact_jump_type : Prop :=
  ∀ {O : Set (E 2)} (d : PositiveCellData O)
    (k l : Fin d.count) (hkl : k ≠ l) (i j : Fin 2) (e f : Bool) (t s a : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s)
    (htangent : (cellFaceSign i e : ℝ) • deriv (cellCurve (cellFace (d.cells k) i e)) t =
      a • ((cellFaceSign j f : ℝ) • deriv (cellCurve (cellFace (d.cells l) j f)) s)),
    GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells k) i e) t)
      (deriv (cellCurve (cellFace (d.cells k) i e)) t) 0

def path_integral_field_congr_type : Prop :=
  ∀ (η : PiecewiseC1Path) (q Q : ℂ → ℂ)
    (h : EqOn q Q η.trace),
    η.integral q = η.integral Q

def chain_integral_field_congr_type : Prop :=
  ∀ (Γ : IntegralChain) (q Q : ℂ → ℂ)
    (h : EqOn q Q Γ.trace),
    Γ.integral q = Γ.integral Q

def patch_integral_form_congr_weighted_type : Prop :=
  ∀ {k n} {O : Set (E n)}
    (P : Patch k O) (w : E n → ℝ) (omega Omega : FormField n k)
    (h : ∀ y ∈ P.map '' P.region, w y ≠ 0 → omega y = Omega y),
    patchIntegral P w omega = patchIntegral P w Omega

def patchChain_integral_form_congr_weighted_type : Prop :=
  ∀ {k n} {O : Set (E n)}
    (C : PatchChain k O) (omega Omega : FormField n k)
    (h : ∀ p ∈ C.support, ∀ y ∈ p.patch.map '' p.patch.region,
      p.weight y ≠ 0 → omega y = Omega y),
    patchChainIntegral omega C = patchChainIntegral Omega C

def complex_field_C1_extension_type : Prop :=
  ∀ (K : Set ℂ) (hK : IsCompact K)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hq : ContDiffOn ℝ 1 q U),
    ∃ Q : ℂ → ℂ, ContDiff ℝ 1 Q ∧
      ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn Q q V

def cell_comparison_of_face_incidence_on_faces_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralChain)
    (hboundary : Γ.trace ⊆ frontier d.carrier)
    (hcount : ∀ j i e, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      chainTangentMultiplicity Γ (cellCurve (cellFace (d.cells j) i e) s)
        (deriv (cellCurve (cellFace (d.cells j) i e)) s) =
      ∑ k, ∑ l : Fin 2, (-1 : ℤ) ^ l.val *
        (tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l true))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s) -
        tangentSignedMultiplicity (cellPath (cellFace (d.cells k) l false))
          (cellCurve (cellFace (d.cells j) i e) s)
          (deriv (cellCurve (cellFace (d.cells j) i e)) s)))
    (q : ℂ → ℂ) (hq : ContinuousOn q d.faceCarrier),
    Γ.integral q = d.faceContour.integral q

def PositiveCellData_faceCarrier_subset_carrier_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O),
    d.faceCarrier ⊆ d.carrier

def cell_assembly_dictionary_near_carrier_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O)
    (hsupport : ∀ p ∈ d.outer.support,
      ∀ y ∈ p.patch.map '' p.patch.region, p.weight y ≠ 0 →
        complexCoordinates.symm y ∈ d.carrier)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U),
    d.faceContour.integral q =
      (patchChainIntegral (realForm q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm q) d.outer

def tangentSignedMultiplicity_eq_zero_of_not_mem_trace_type : Prop :=
  ∀ (η : PiecewiseC1Path) (z v : ℂ) (hz : z ∉ η.trace),
    tangentSignedMultiplicity η z v = 0

def cell_face_multiplicity_other_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (i j : Fin 2) (e f : Bool) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hface : i ≠ j ∨ e ≠ f) (v : ℂ),
    tangentSignedMultiplicity (cellPath (cellFace c j f))
      (cellCurve (cellFace c i e) t) v = 0

def PositiveCellData_face_avoids_endpoints_ae_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool),
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ∀ (l : Fin d.count) (j : Fin 2) (f : Bool),
        cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 0 ∧
        cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 1

def face_parameter_interior_of_not_endpoints_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 1 O)
    (z : ℂ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (heq : cellCurve c s = z)
    (hzero : z ≠ cellCurve c 0) (hone : z ≠ cellCurve c 1),
    s ∈ Ioo (0 : ℝ) 1

def cell_faces_multiplicity_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (hinj : InjOn (cellExtension c) (cube 2))
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (v : ℂ),
    (∑ j : Fin 2, ∑ f : Bool, cellFaceSign j f *
      tangentSignedMultiplicity (cellPath (cellFace c j f))
        (cellCurve (cellFace c i e) t) v) =
    cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace c i e))
      (cellCurve (cellFace c i e) t) v

def cell_assembly_tangent_multiplicity_faces_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (z v : ℂ),
    chainTangentMultiplicity d.faceContour z v =
      ∑ k : Fin d.count, ∑ i : Fin 2, ∑ e : Bool,
        cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e)) z v

def PositiveCellData_multiplicity_of_single_contact_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (v : ℂ)
    (habsent : ∀ l : Fin d.count, l ≠ k → ∀ j : Fin 2, ∀ f : Bool,
      cellCurve (cellFace (d.cells k) i e) t ∉ (cellPath (cellFace (d.cells l) j f)).trace),
    chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells k) i e) t) v =
      cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
        (cellCurve (cellFace (d.cells k) i e) t) v

def PositiveCellData_multiplicity_of_two_contacts_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i j : Fin 2) (e f : Bool) (t s : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hpoint : cellCurve (cellFace (d.cells k) i e) t =
      cellCurve (cellFace (d.cells l) j f) s) (v : ℂ)
    (habsent : ∀ m : Fin d.count, m ≠ k → m ≠ l → ∀ q : Fin 2, ∀ h : Bool,
      cellCurve (cellFace (d.cells k) i e) t ∉ (cellPath (cellFace (d.cells m) q h)).trace),
    chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells k) i e) t) v =
      cellFaceSign i e * tangentSignedMultiplicity (cellPath (cellFace (d.cells k) i e))
        (cellCurve (cellFace (d.cells k) i e) t) v +
      cellFaceSign j f * tangentSignedMultiplicity (cellPath (cellFace (d.cells l) j f))
        (cellCurve (cellFace (d.cells k) i e) t) v

def PositiveCellData_other_cell_contact_is_face_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hmem : cellCurve (cellFace (d.cells k) i e) t ∈
      complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)),
    ∃ (j : Fin 2) (f : Bool) (s : ℝ), s ∈ Icc (0 : ℝ) 1 ∧
      cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s

def PositiveCellData_other_cell_contact_is_interior_face_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k l : Fin d.count) (hkl : k ≠ l)
    (i : Fin 2) (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcorner : ∀ (j : Fin 2) (f : Bool),
      cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 0 ∧
      cellCurve (cellFace (d.cells k) i e) t ≠ cellCurve (cellFace (d.cells l) j f) 1)
    (hmem : cellCurve (cellFace (d.cells k) i e) t ∈
      complexCoordinates.symm '' (cellExtension (d.cells l) '' cube 2)),
    ∃ (j : Fin 2) (f : Bool) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 ∧
      cellCurve (cellFace (d.cells k) i e) t = cellCurve (cellFace (d.cells l) j f) s

def cell_face_trace_subset_cell_image_type : Prop :=
  ∀ {O : Set (E 2)} (c : Cell 1 2 O)
    (i : Fin 2) (e : Bool),
    (cellPath (cellFace c i e)).trace ⊆
      complexCoordinates.symm '' (cellExtension c '' cube 2)

def PositiveCellData_face_boundary_jump_ae_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (k : Fin d.count) (i : Fin 2) (e : Bool),
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      GeometricBoundaryJump d.carrier (cellCurve (cellFace (d.cells k) i e) t)
        (deriv (cellCurve (cellFace (d.cells k) i e)) t)
        (chainTangentMultiplicity d.faceContour (cellCurve (cellFace (d.cells k) i e) t)
          (deriv (cellCurve (cellFace (d.cells k) i e)) t))

def cell_boundary_comparison_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (hq : ContinuousOn q d.carrier),
    Γ.integral q = d.faceContour.integral q

def cell_boundary_dictionary_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (hq : ContinuousOn q (complexCoordinates ⁻¹' O)),
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer

def cell_boundary_dictionary_near_carrier_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (hsupport : ∀ p ∈ d.outer.support,
      ∀ y ∈ p.patch.map '' p.patch.region, p.weight y ≠ 0 →
        complexCoordinates.symm y ∈ d.carrier)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U),
    Γ.integral q = (patchChainIntegral (realForm q) d.outer : ℂ) +
      Complex.I * patchChainIntegral (imagForm q) d.outer

def cell_boundary_dictionary_extension_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U),
    ∃ (Q : ℂ → ℂ) (V : Set ℂ), ContDiff ℝ 1 Q ∧ IsOpen V ∧
      d.carrier ⊆ V ∧ V ⊆ U ∧ EqOn Q q V ∧
      Γ.integral q = (patchChainIntegral (realForm Q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm Q) d.outer

def cell_boundary_extension_independent_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (q Q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates ⁻¹' O))
    (hQ : ContinuousOn Q (complexCoordinates ⁻¹' O))
    (heq : EqOn q Q d.carrier),
    (patchChainIntegral (realForm q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm q) d.outer =
      (patchChainIntegral (realForm Q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm Q) d.outer

def cell_boundary_extension_real_independent_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (q Q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates ⁻¹' O))
    (hQ : ContinuousOn Q (complexCoordinates ⁻¹' O))
    (heq : EqOn q Q d.carrier),
    patchChainIntegral (realForm q) d.outer =
      patchChainIntegral (realForm Q) d.outer

def cell_boundary_extension_imag_independent_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (q Q : ℂ → ℂ)
    (hq : ContinuousOn q (complexCoordinates ⁻¹' O))
    (hQ : ContinuousOn Q (complexCoordinates ⁻¹' O))
    (heq : EqOn q Q d.carrier),
    patchChainIntegral (imagForm q) d.outer =
      patchChainIntegral (imagForm Q) d.outer

def field_fderiv_eqOn_open_type : Prop :=
  ∀ (Q q : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (heq : EqOn Q q V),
    EqOn (fderiv ℝ Q) (fderiv ℝ q) V

def cell_boundary_dictionary_extension_with_derivatives_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U),
    ∃ (Q : ℂ → ℂ) (V : Set ℂ), ContDiff ℝ 1 Q ∧ IsOpen V ∧
      d.carrier ⊆ V ∧ V ⊆ U ∧ EqOn Q q V ∧
      EqOn (fderiv ℝ Q) (fderiv ℝ q) V ∧
      Γ.integral q = (patchChainIntegral (realForm Q) d.outer : ℂ) +
        Complex.I * patchChainIntegral (imagForm Q) d.outer ∧
      (Γ.integral q).re = patchChainIntegral (realForm Q) d.outer ∧
      (Γ.integral q).im = patchChainIntegral (imagForm Q) d.outer

end Specs.D12Complex.Ch04.CellBoundaryContour
