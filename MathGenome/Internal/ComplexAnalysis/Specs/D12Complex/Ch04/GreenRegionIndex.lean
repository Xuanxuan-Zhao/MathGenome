import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.ManifoldBoundaryContour
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.CellBoundaryContour
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.WindingIndex
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyFormula
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.RealComplexDifferential
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GreenCirculationAndFlux

/-!
Independent specifications for d12:04:green-index (paper.tex:1041–1069).
The analytic dictionary and geometric construction helpers from the earlier
continuation are retained. The source-facing declarations at the end use the
canonical manifold and cell geometry and their original full positive boundary
relations, without a boundary-comparison premise. Fields are C1 only near the
compact integration carrier; the cell extension preserves the original field
and first real derivatives there while admitting arbitrary supplied outer displays.
-/
noncomputable section
open Set
open scoped BigOperators

namespace D12Complex.GreenRegionIndex
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

/-- The actual D04 real coordinate equivalence, made continuous by finite dimension. -/
def planeCoordinates : ℂ ≃L[ℝ] E 2 := complexCoordinates.toContinuousLinearEquiv

/-- No parametrization or orientation is changed by the coordinate conversion. -/
def realPath (γ : ComplexPath) : IntervalPath 2 γ.a γ.b where
  ordered := γ.ordered
  toFun := fun t => planeCoordinates (γ t)
  continuousOn := planeCoordinates.continuous.comp_continuousOn γ.continuousOn

def realPartition {γ : ComplexPath} (P : C1Partition γ) :
    SingleVariableAnalysis.Riemann.PartitionData γ.a γ.b :=
  ⟨P.count, P.node, P.strictMono, P.first, P.last⟩

/-- Canonical D04 velocity data on exactly the same closed smooth pieces.
This uses one-sided derivatives at joins, as both original path theories do. -/
def realData {γ : ComplexPath} (P : C1Partition γ) : PiecewiseC1Data (realPath γ) where
  partition := realPartition P
  velocity := fun i t => planeCoordinates (derivWithin γ (P.pieceSet i) t)
  smooth := by
    intro i
    change Fin P.count at i
    change Specs.D04.C09.PathsLength.Model.C1Piece (realPath γ)
      (fun t => planeCoordinates (derivWithin γ (P.pieceSet i) t))
      (P.node i.castSucc) (P.node i.succ)
    have hlt : P.node i.castSucc < P.node i.succ := P.strictMono (by simp)
    have hC := (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hlt)).mp (P.smooth i)
    refine ⟨planeCoordinates.continuous.comp_continuousOn hC.2, ?_⟩
    intro t ht
    exact planeCoordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
      (hC.1 t ht).hasDerivWithinAt

/-- Coefficients of Re(q dz) and Im(q dz) in D04 coordinates. -/
def realForm (q : ℂ → ℂ) :=
  circulationForm (fun x => (q (planeCoordinates.symm x)).re)
    (fun x => -(q (planeCoordinates.symm x)).im)

def imagForm (q : ℂ → ℂ) :=
  circulationForm (fun x => (q (planeCoordinates.symm x)).im)
    (fun x => (q (planeCoordinates.symm x)).re)

open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C06.DarbouxIntegral.Model hiding E

/-- Geometric representatives of the canonical smooth pieces. The fields
prescribe only parameter regions and maps, and assume no integral identity. -/
structure PathPatchData (O : Set (E 2)) (γ : PiecewiseC1Path) where
  patch : Fin γ.partition.count → Patch 1 O
  region : ∀ i, (patch i).region = carrier
    (intervalBox (γ.partition.node i.castSucc) (γ.partition.node i.succ)
      (γ.partition.strictMono (by simp)).le)
  map : ∀ i t, t ∈ γ.partition.pieceSet i →
    (patch i).map (scalarPoint t) = planeCoordinates (γ t)

/-- Finite signed path enumeration together with actual parameter patches.
Repeated and zero-coefficient paths are permitted. -/
structure ContourPatchData (O : Set (E 2)) (Γ : IntegralChain) where
  count : ℕ
  path : Fin count → PiecewiseC1Path
  multiplicity : Fin count → ℤ
  chain_eq : Γ = ∑ j, Finsupp.single (path j) (multiplicity j)
  pieces : ∀ j, PathPatchData O (path j)

/-- The signs of the integer contour are retained in its patch chain. -/
def ContourPatchData.patchChain {O : Set (E 2)} {Γ : IntegralChain}
    (d : ContourPatchData O Γ) : PatchChain 1 O :=
  ∑ j, (d.multiplicity j) • ∑ i, Finsupp.single
    (⟨(d.pieces j).patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1

open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C15.GeneralizedStokes.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C12.RegularDomainRiemannManifoldBridge.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C15.FiniteGeometricUnionIntegral.Model

/-- The actual geometric inputs of the prior finite-manifold Green theorem.
All fields concern regions, charts, orientations, seams, and reparametrizations.
No formula for an integral or index is a field. -/
structure ManifoldGreenData (O : Set (E 2)) where
  count : ℕ
  piece : Fin count → CompactManifold 1 2 O
  ambient : ∀ j, IsAmbientOrientation (piece j).orientation
  boundaryOrientation : (j : Fin count) → PositiveManifoldOrientation 1 1
    (intrinsicBoundary 1 2 (piece j).carrier)
  outward : ∀ j, OutwardFirst 1 (piece j).orientation (boundaryOrientation j)
  patchCount : Fin count → ℕ
  patch : (j : Fin count) → Fin (patchCount j) → Patch 1 O
  sign : (j : Fin count) → Fin (patchCount j) → PointSign
  regular : ∀ j t, RegularPiece (boundaryOrientation j) (patch j t) (sign j t)
  seams : Fin count → Seams 2
  seamsDim : ∀ j i, (seams j).dim i < 1
  repeats : ∀ j t u, u ∈ (patch j t).region → ∀ v, v ∈ (patch j t).region →
    u ≠ v → (patch j t).map u = (patch j t).map v →
    (patch j t).map u ∈ (seams j).carrier
  overlap : ∀ j t u, t ≠ u → ((patch j t).map '' (patch j t).region) ∩
    ((patch j u).map '' (patch j u).region) ⊆ (seams j).carrier
  cover : ∀ j, intrinsicBoundary 1 2 (piece j).carrier ⊆
    (⋃ t, (patch j t).map '' (patch j t).region) ∪ (seams j).carrier
  bulkSeams : AmbientSeams 2 2
  bulkOverlap : ∀ i j, i ≠ j → (piece i).carrier ∩ (piece j).carrier ⊆ bulkSeams.carrier
  outerCount : ℕ
  pairCount : ℕ
  occurrence : (Fin outerCount ⊕ (Fin pairCount × Bool)) ≃
    ((j : Fin count) × Fin (patchCount j))
  outer : Fin outerCount → Patch 1 O
  outerSign : Fin outerCount → PointSign
  outerDirection : Fin outerCount → ℝ
  outerDirection_sign : ∀ t, outerDirection t = 1 ∨ outerDirection t = -1
  outerReparam : (t : Fin outerCount) → LocalReparametrization
    (patch (occurrence (Sum.inl t)).1 (occurrence (Sum.inl t)).2).region
    (outer t).region (outerDirection t)
  outerMatch : ∀ t,
    EqOn (patch (occurrence (Sum.inl t)).1 (occurrence (Sum.inl t)).2).map
      ((outer t).map ∘ (outerReparam t).map)
      (patch (occurrence (Sum.inl t)).1 (occurrence (Sum.inl t)).2).region ∧
    (sign (occurrence (Sum.inl t)).1 (occurrence (Sum.inl t)).2).val * outerDirection t =
      (outerSign t).val
  pairDirection : Fin pairCount → ℝ
  pairDirection_sign : ∀ i, pairDirection i = 1 ∨ pairDirection i = -1
  pairReparam : (i : Fin pairCount) → LocalReparametrization
    (patch (occurrence (Sum.inr (i,false))).1 (occurrence (Sum.inr (i,false))).2).region
    (patch (occurrence (Sum.inr (i,true))).1 (occurrence (Sum.inr (i,true))).2).region
    (pairDirection i)
  pairMatch : ∀ i,
    EqOn (patch (occurrence (Sum.inr (i,false))).1 (occurrence (Sum.inr (i,false))).2).map
      ((patch (occurrence (Sum.inr (i,true))).1 (occurrence (Sum.inr (i,true))).2).map ∘
        (pairReparam i).map)
      (patch (occurrence (Sum.inr (i,false))).1 (occurrence (Sum.inr (i,false))).2).region ∧
    (sign (occurrence (Sum.inr (i,false))).1 (occurrence (Sum.inr (i,false))).2).val *
      pairDirection i =
      -(sign (occurrence (Sum.inr (i,true))).1 (occurrence (Sum.inr (i,true))).2).val

/-- The actual compact integration region. -/
def ManifoldGreenData.carrier {O : Set (E 2)} (d : ManifoldGreenData O) : Set (E 2) :=
  ⋃ j, (d.piece j).carrier

/-- Integer encoding of an induced orientation sign. -/
def orientationInteger (s : PointSign) : ℤ := if s.val = 1 then 1 else -1

def ManifoldGreenData.outerChain {O : Set (E 2)} (d : ManifoldGreenData O) : PatchChain 1 O :=
  ∑ t, Finsupp.single
    (⟨d.outer t, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
    (orientationInteger (d.outerSign t))


/-- A supplied geometric Green decomposition whose signed outer patches
represent the specified contour. Region equality is geometric; no Green
identity or boundary index is assumed. -/
structure ManifoldBoundaryRepresentation (U K : Set ℂ) (Γ : IntegralChain) where
  geometry : ManifoldGreenData (planeCoordinates.symm ⁻¹' U)
  carrier_eq : geometry.carrier = planeCoordinates '' K
  contour : ContourPatchData (planeCoordinates.symm ⁻¹' U) Γ
  contour_in : ∀ j, (contour.path j).trace ⊆ U
  represents : GeometricEquivalent geometry.outerChain contour.patchChain

/-- The supplied regular-region/decomposition data may be used with C1
fields on any open neighborhood of this closed integration region. -/
def HasManifoldGreenBoundary (K : Set ℂ) (Γ : IntegralChain) : Prop :=
  ∀ U : Set ℂ, IsOpen U → K ⊆ U → Nonempty (ManifoldBoundaryRepresentation U K Γ)

/-- The disk-deleted boundary is the full original positive boundary minus
one positively traversed circle, with its original parametrization. -/
def deletedDiskBoundary (Γ : IntegralCycle) (a : ℂ) (r : ℝ) : IntegralChain :=
  Γ.chain - Finsupp.single (Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_value a r) 1

/-- The manifold-represented branch of an already specified bounded open region,
with its actual full oriented
boundary and the real Green geometric data, also after deleting a sufficiently
small closed interior disk. No Jordan interior is postulated. -/
structure ManifoldGreenRegularRegion (D : Set ℂ) (Γ : IntegralCycle) : Prop where
  isOpen : IsOpen D
  bounded : Bornology.IsBounded D
  boundary_trace : Γ.trace ⊆ frontier D
  whole : HasManifoldGreenBoundary (closure D) Γ.chain
  deleted : ∀ a ∈ D, ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ D ∧
    HasManifoldGreenBoundary (closure (D \ Metric.closedBall a r)) (deletedDiskBoundary Γ a r)

open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

/-- Positive regular cells with the actual prior face assembly and seam data.
The boundary is a geometric patch chain, never an integral certificate. -/
structure CellGreenData (O : Set (E 2)) where
  count : ℕ
  pairCount : ℕ
  cell : Fin count → Cell 1 2 O
  face : Fin count → Fin 2 → Bool → Patch 1 O
  faces : ∀ j i e, (face j i e).region = cube 1 ∧
    EqOn (face j i e).map (cellExtension (cellFace (cell j) i e)) (cube 1)
  outerChain : PatchChain 1 O
  left : Fin pairCount → WeightedPatch 1 O
  right : Fin pairCount → WeightedPatch 1 O
  multiplicity : Fin pairCount → ℤ
  direction : Fin pairCount → ℤ
  direction_sign : ∀ i, direction i = 1 ∨ direction i = -1
  reparam : ∀ i, ∃ h : LocalReparametrization (left i).patch.region
    (right i).patch.region (direction i : ℝ),
    EqOn (left i).patch.map ((right i).patch.map ∘ h.map) (left i).patch.region
  weights : ∀ i, EqOn (left i).weight (right i).weight
    ((right i).patch.map '' (right i).patch.region)
  assembly : GeometricEquivalent (∑ j, (1 : ℤ) • patchBoundary (face j))
    (outerChain + ∑ i, multiplicity i •
      (Finsupp.single (left i) 1 - direction i • Finsupp.single (right i) 1))
  injective : ∀ j, InjOn (cellExtension (cell j)) (cube 2)
  positive : ∀ j x, x ∈ cube 2 → 0 < (fderiv ℝ (cellExtension (cell j)) x).det
  seams : AmbientSeams 2 2
  overlap : ∀ i j, i ≠ j → (cellExtension (cell i) '' cube 2) ∩
    (cellExtension (cell j) '' cube 2) ⊆ seams.carrier

def CellGreenData.carrier {O : Set (E 2)} (d : CellGreenData O) : Set (E 2) :=
  ⋃ j, cellExtension (d.cell j) '' cube 2

/-- The two supplied geometric branches of the prior Green theorem. -/
inductive FiniteGreenData (O : Set (E 2))
  | manifold : ManifoldGreenData O → FiniteGreenData O
  | cells : CellGreenData O → FiniteGreenData O

def FiniteGreenData.carrier {O : Set (E 2)} : FiniteGreenData O → Set (E 2)
  | .manifold d => d.carrier
  | .cells d => d.carrier

def FiniteGreenData.outerChain {O : Set (E 2)} : FiniteGreenData O → PatchChain 1 O
  | .manifold d => d.outerChain
  | .cells d => d.outerChain

/-- Subdivision and directed monotone changes of actual traversals. Each
constructor has geometric parameter hypotheses; none assumes integral equality.
Flat parameter pieces and zero velocities are allowed. -/
inductive ContourEquivalentOn (U : Set ℂ) : IntegralChain → IntegralChain → Prop
  | constant (γ : PiecewiseC1Path) (z : ℂ)
      (map : ∀ t ∈ Icc γ.path.a γ.path.b, γ t = z) :
      ContourEquivalentOn U (Finsupp.single γ 1) 0
  | refl (C) : ContourEquivalentOn U C C
  | symm {C D} : ContourEquivalentOn U C D → ContourEquivalentOn U D C
  | trans {C D F} : ContourEquivalentOn U C D → ContourEquivalentOn U D F →
      ContourEquivalentOn U C F
  | add {C D F G} : ContourEquivalentOn U C D → ContourEquivalentOn U F G →
      ContourEquivalentOn U (C + F) (D + G)
  | zsmul (m : ℤ) {C D} : ContourEquivalentOn U C D →
      ContourEquivalentOn U (m • C) (m • D)
  | monotone (γ η : PiecewiseC1Path) (φ : ℝ → ℝ)
      (inside : γ.trace ⊆ U)
      (continuous : ContinuousOn φ (Icc η.path.a η.path.b))
      (monotone : MonotoneOn φ (Icc η.path.a η.path.b))
      (maps : MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
      (onto : SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
      (smooth : ∃ (n : ℕ) (node : Fin (n + 1) → ℝ), StrictMono node ∧
        node 0 = η.path.a ∧ node (Fin.last n) = η.path.b ∧
        ∀ i : Fin n, ContDiffOn ℝ 1 φ (Icc (node i.castSucc) (node i.succ)))
      (map : EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b)) :
      ContourEquivalentOn U (Finsupp.single η 1) (Finsupp.single γ 1)
  | subdivision (γ γ₁ γ₂ : PiecewiseC1Path) (c : ℝ)
      (inside : γ.trace ⊆ U) (cut : c ∈ Icc γ.path.a γ.path.b)
      (first : γ₁.path.a = γ.path.a) (join₁ : γ₁.path.b = c)
      (join₂ : γ₂.path.a = c) (last : γ₂.path.b = γ.path.b)
      (map₁ : EqOn γ₁ γ (Icc γ₁.path.a γ₁.path.b))
      (map₂ : EqOn γ₂ γ (Icc γ₂.path.a γ₂.path.b)) :
      ContourEquivalentOn U (Finsupp.single γ 1)
        (Finsupp.single γ₁ 1 + Finsupp.single γ₂ 1)
  | reversal (γ η : PiecewiseC1Path) (inside : γ.trace ⊆ U)
      (first : η.path.a = γ.path.a) (last : η.path.b = γ.path.b)
      (map : EqOn η (fun t => γ (γ.path.a + γ.path.b - t))
        (Icc η.path.a η.path.b)) :
      ContourEquivalentOn U (Finsupp.single η 1) (-Finsupp.single γ 1)

/-- An actual regular display of one supplied oriented boundary manifold.
Jordan subsets, induced chart signs, multiplicity away from seams, and coverage
are geometric data. No integral or index value occurs here. -/
structure RegularBoundaryDisplay {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) where
  count : ℕ
  patch : Fin count → Patch 1 O
  sign : Fin count → PointSign
  regular : ∀ i, RegularPiece o (patch i) (sign i)
  seams : Seams 2
  seamsDim : ∀ i, seams.dim i < 1
  repeats : ∀ i u, u ∈ (patch i).region → ∀ v, v ∈ (patch i).region →
    u ≠ v → (patch i).map u = (patch i).map v → (patch i).map u ∈ seams.carrier
  overlap : ∀ i j, i ≠ j → ((patch i).map '' (patch i).region) ∩
    ((patch j).map '' (patch j).region) ⊆ seams.carrier
  cover : M ⊆ (⋃ i, (patch i).map '' (patch i).region) ∪ seams.carrier

/-- The full signed display, retaining each induced orientation. -/
def RegularBoundaryDisplay.patchChain {O M : Set (E 2)}
    {o : PositiveManifoldOrientation 1 1 M} (d : RegularBoundaryDisplay (O := O) o) :
    PatchChain 1 O :=
  ∑ i, Finsupp.single
    (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O)
    (orientationInteger (d.sign i))

/-- The regular boundary displays already present in the supplied Green data. -/
def ManifoldGreenData.boundaryDisplay {O : Set (E 2)} (d : ManifoldGreenData O)
    (j : Fin d.count) : RegularBoundaryDisplay (O := O) (d.boundaryOrientation j) where
  count := d.patchCount j
  patch := d.patch j
  sign := d.sign j
  regular := d.regular j
  seams := d.seams j
  seamsDim := d.seamsDim j
  repeats := d.repeats j
  overlap := d.overlap j
  cover := d.cover j

/-- Geometric patch comparison permitting arbitrary regular display changes
and omission and overlap at finitely many parameter points. The generators specify maps and regions, never integral values. -/
inductive PatchEquivalentOffFinite {O : Set (E 2)} :
    PatchChain 1 O → PatchChain 1 O → Prop
  | geometric {C D} : GeometricEquivalent C D → PatchEquivalentOffFinite C D
  | display {M : Set (E 2)} (o : PositiveManifoldOrientation 1 1 M)
      (compact : IsCompact M) (inside : M ⊆ O)
      (d e : RegularBoundaryDisplay (O := O) o) :
      PatchEquivalentOffFinite d.patchChain e.patchChain
  | cover (p : WeightedPatch 1 O) (m : ℕ) (R : Fin m → Set (E 1))
      (hR : ∀ i, Specs.D04.C06.JordanRegions.Model.Jordan (R i))
      (hsub : ∀ i, R i ⊆ p.patch.region) (Z : Set (E 1)) (hZ : Z.Finite)
      (hcover : p.patch.region \ Z ⊆ ⋃ i, R i)
      (hpair : ∀ i j, i ≠ j → R i ∩ R j ⊆ Z) :
      PatchEquivalentOffFinite (Finsupp.single p 1)
        (∑ i, Finsupp.single (restrictWeighted p (R i) (hR i) (hsub i)) 1)
  | refl (C) : PatchEquivalentOffFinite C C
  | symm {C D} : PatchEquivalentOffFinite C D → PatchEquivalentOffFinite D C
  | trans {C D F} : PatchEquivalentOffFinite C D → PatchEquivalentOffFinite D F →
      PatchEquivalentOffFinite C F
  | add {C D F G} : PatchEquivalentOffFinite C D → PatchEquivalentOffFinite F G →
      PatchEquivalentOffFinite (C + F) (D + G)
  | zsmul (a : ℤ) {C D} : PatchEquivalentOffFinite C D →
      PatchEquivalentOffFinite (a • C) (a • D)

/-- A finite Green assembly together with its boundary traversals. The contour
may first be subdivided and monotonically reparametrized. -/
structure FiniteBoundaryRepresentation (U K : Set ℂ) (Γ : IntegralChain) where
  geometry : FiniteGreenData (planeCoordinates.symm ⁻¹' U)
  carrier_eq : geometry.carrier = planeCoordinates '' K
  representedChain : IntegralChain
  traversal : ContourEquivalentOn U Γ representedChain
  contour : ContourPatchData (planeCoordinates.symm ⁻¹' U) representedChain
  contour_in : ∀ j, (contour.path j).trace ⊆ U
  represents : PatchEquivalentOffFinite geometry.outerChain contour.patchChain

def HasFiniteGreenBoundary (K : Set ℂ) (Γ : IntegralChain) : Prop :=
  ∀ U : Set ℂ, IsOpen U → K ⊆ U → Nonempty (FiniteBoundaryRepresentation U K Γ)

structure FiniteGreenRegularRegion (D : Set ℂ) (Γ : IntegralCycle) : Prop where
  isOpen : IsOpen D
  bounded : Bornology.IsBounded D
  boundary_trace : Γ.trace ⊆ frontier D
  whole : HasFiniteGreenBoundary (closure D) Γ.chain
  deleted : ∀ a ∈ D, ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ D ∧
    HasFiniteGreenBoundary (closure (D \ Metric.closedBall a r)) (deletedDiskBoundary Γ a r)

/-- A single supplied geometric assembly in one ambient open set. Smooth
localization of the reciprocal will remove the need to reconstruct it in
arbitrary smaller neighborhoods. -/
def HasFixedFiniteGreenBoundary (K : Set ℂ) (Γ : IntegralChain) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ Nonempty (FiniteBoundaryRepresentation U K Γ)

/-- An already specified bounded region with supplied positive Green boundary
assemblies, before and after deleting a small closed interior disk. -/
structure FixedFiniteGreenRegularRegion (D : Set ℂ) (Γ : IntegralCycle) : Prop where
  isOpen : IsOpen D
  bounded : Bornology.IsBounded D
  boundary_trace : Γ.trace ⊆ frontier D
  whole : HasFixedFiniteGreenBoundary (closure D) Γ.chain
  deleted : ∀ a ∈ D, ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ D ∧
    HasFixedFiniteGreenBoundary (closure (D \ Metric.closedBall a r)) (deletedDiskBoundary Γ a r)

end D12Complex.GreenRegionIndex

namespace Specs.D12Complex.Ch04.GreenRegionIndex
open _root_.D12Complex
open _root_.D12Complex.GreenRegionIndex
open Specs.D04.C09.LineIntegrals.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model

/-- This is a dictionary between the actual integrals, with existence included. -/
def path_real_green_dictionary_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (q : ℂ → ℂ), ContinuousOn q γ.trace →
    ∃ (hr : OneFormIntegrable (realData γ.partition) (realForm q))
      (hi : OneFormIntegrable (realData γ.partition) (imagForm q)),
    γ.integral q =
      (oneFormIntegral (realData γ.partition) (realForm q) hr : ℂ) +
      Complex.I * (oneFormIntegral (realData γ.partition) (imagForm q) hi : ℂ)

/-- Algebraic form identification at arbitrary directed velocities. -/
def realForm_apply_type : Prop :=
  ∀ (q : ℂ → ℂ) (z v : ℂ),
    realForm q (planeCoordinates z) (fun _ => planeCoordinates v) = (q z * v).re ∧
    imagForm q (planeCoordinates z) (fun _ => planeCoordinates v) = (q z * v).im

/-- The two scalar curls of a holomorphic C1 field vanish pointwise.
C1 is needed by Green on a neighborhood, not by this pointwise CR statement. -/
def green_densities_zero_type : Prop :=
  ∀ (q : ℂ → ℂ) (z : ℂ), DifferentiableAt ℂ q z →
    circulationDensity (fun x => (q (planeCoordinates.symm x)).re)
      (fun x => -(q (planeCoordinates.symm x)).im) (planeCoordinates z) = 0 ∧
    circulationDensity (fun x => (q (planeCoordinates.symm x)).im)
      (fun x => (q (planeCoordinates.symm x)).re) (planeCoordinates z) = 0

/-- C1 fields on a complex open neighborhood give the exact D04 regularity
hypotheses on its real coordinate neighborhood. -/
def green_fields_regular_type : Prop :=
  ∀ (U : Set ℂ) (q : ℂ → ℂ), IsOpen U → ContDiffOn ℝ 1 q U →
    Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1
      (planeCoordinates.symm ⁻¹' U) (fun x => (q (planeCoordinates.symm x)).re) ∧
    Specs.D04.C02.DerivativeInterfaces.Model.CrOn 1
      (planeCoordinates.symm ⁻¹' U) (fun x => (q (planeCoordinates.symm x)).im)

/-- The field used on both the unpunctured and the disk-deleted region. -/
def reciprocal_regular_type : Prop :=
  ∀ (a : ℂ), ContDiffOn ℝ 1 (fun z : ℂ => 1 / (z - a)) ({a}ᶜ) ∧
    ∀ z ≠ a, DifferentiableAt ℂ (fun w : ℂ => 1 / (w - a)) z

/-- The remaining index normalization after a geometric Green calculation.
Neither direction supplies the missing geometric integral calculation. -/
def cycle_index_zero_iff_type : Prop :=
  ∀ (Γ : IntegralCycle) (a : ℂ), a ∉ Γ.trace →
    (Γ.index a = 0 ↔ Γ.integral (fun z => 1 / (z - a)) = 0)

def cycle_index_one_iff_type : Prop :=
  ∀ (Γ : IntegralCycle) (a : ℂ), a ∉ Γ.trace →
    (Γ.index a = 1 ↔ Γ.integral (fun z => 1 / (z - a)) =
      2 * (Real.pi : ℂ) * Complex.I)

open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model

/-- Dictionary for actual interval patches, independent of their off-region
representatives. The C0 form hypotheses are precisely those used by the prior
patch integral theory. -/
def path_patch_green_dictionary_type : Prop :=
  ∀ (O : Set (E 2)) (γ : PiecewiseC1Path) (d : PathPatchData O γ)
    (q : ℂ → ℂ), ContinuousOn q γ.trace →
    IsCrForm (some 0) O (realForm q) → IsCrForm (some 0) O (imagForm q) →
    γ.integral q =
      ((∑ i, patchIntegral (d.patch i) (fun _ => 1) (realForm q) : ℝ) : ℂ) +
      Complex.I * ((∑ i, patchIntegral (d.patch i) (fun _ => 1) (imagForm q) : ℝ) : ℂ)

/-- Signed finite assemblies and genuine geometric reparametrizations preserve
the dictionary. Geometric equivalence carries no assumed integral equality. -/
def assembled_patch_green_dictionary_type : Prop :=
  ∀ (O : Set (E 2)) (Γ : IntegralChain) (d : ContourPatchData O Γ)
    (C : PatchChain 1 O), GeometricEquivalent C d.patchChain →
    ∀ q : ℂ → ℂ, (∀ j, ContinuousOn q (d.path j).trace) →
    IsCrForm (some 0) O (realForm q) → IsCrForm (some 0) O (imagForm q) →
    Γ.integral q = (patchChainIntegral (realForm q) C : ℂ) +
      Complex.I * (patchChainIntegral (imagForm q) C : ℂ)

/-- Actual application of real Green and CR on the supplied geometric union.
It does not presume any value of the boundary integral. -/
def manifold_green_zero_type : Prop :=
  ∀ (U : Set ℂ) (q : ℂ → ℂ), IsOpen U → ContDiffOn ℝ 1 q U →
    (∀ z ∈ U, DifferentiableAt ℂ q z) →
    ∀ d : ManifoldGreenData (planeCoordinates.symm ⁻¹' U),
    patchChainIntegral (realForm q) d.outerChain = 0 ∧
    patchChainIntegral (imagForm q) d.outerChain = 0

def green_contour_zero_type : Prop :=
  ∀ (U K : Set ℂ) (Γ : IntegralChain) (_d : ManifoldBoundaryRepresentation U K Γ)
    (q : ℂ → ℂ), IsOpen U → ContDiffOn ℝ 1 q U →
    (∀ z ∈ U, DifferentiableAt ℂ q z) → Γ.integral q = 0

/-- Index of the specified positive boundary in the region and in every
no-pole complementary region. The same exterior assertion includes holes. -/
def specified_manifold_region_index_type : Prop :=
  ∀ (D : Set ℂ) (Γ : IntegralCycle), ManifoldGreenRegularRegion D Γ →
    (∀ a ∈ D, Γ.index a = 1) ∧ (∀ a ∉ closure D, Γ.index a = 0)

/-- Soundness of the explicit traversal operations for continuous fields. -/
def contour_equivalent_integral_type : Prop :=
  ∀ (U : Set ℂ) (C D : IntegralChain), ContourEquivalentOn U C D →
    ∀ q : ℂ → ℂ, ContinuousOn q U → C.integral q = D.integral q

def finite_green_zero_type : Prop :=
  ∀ (U : Set ℂ) (q : ℂ → ℂ), IsOpen U → ContDiffOn ℝ 1 q U →
    (∀ z ∈ U, DifferentiableAt ℂ q z) →
    ∀ d : FiniteGreenData (planeCoordinates.symm ⁻¹' U),
    patchChainIntegral (realForm q) d.outerChain = 0 ∧
    patchChainIntegral (imagForm q) d.outerChain = 0

def finite_green_contour_zero_type : Prop :=
  ∀ (U K : Set ℂ) (Γ : IntegralChain) (_d : FiniteBoundaryRepresentation U K Γ)
    (q : ℂ → ℂ), IsOpen U → ContDiffOn ℝ 1 q U →
    (∀ z ∈ U, DifferentiableAt ℂ q z) → Γ.integral q = 0

def specified_finite_region_index_type : Prop :=
  ∀ (D : Set ℂ) (Γ : IntegralCycle), FiniteGreenRegularRegion D Γ →
    (∀ a ∈ D, Γ.index a = 1) ∧ (∀ a ∉ closure D, Γ.index a = 0)

def path_patch_exists_type : Prop :=
  ∀ (U : Set ℂ) (γ : PiecewiseC1Path), IsOpen U → γ.trace ⊆ U →
    Nonempty (PathPatchData (planeCoordinates.symm ⁻¹' U) γ)

def reciprocal_smooth_extension_type : Prop :=
  ∀ (K : Set ℂ), IsClosed K → ∀ a : ℂ, a ∉ K →
    ∃ q : ℂ → ℂ, ContDiff ℝ 1 q ∧ ∀ z ∈ K,
      Filter.EventuallyEq (nhds z) q (fun w => 1 / (w - a))

def finite_green_contour_zero_on_type : Prop :=
  ∀ (U K : Set ℂ) (Γ : IntegralChain) (_d : FiniteBoundaryRepresentation U K Γ)
    (q : ℂ → ℂ), IsOpen U → ContDiffOn ℝ 1 q U →
    (∀ z ∈ K, DifferentiableAt ℂ q z) → Γ.integral q = 0

def reciprocal_fixed_boundary_zero_type : Prop :=
  ∀ (U K : Set ℂ) (Γ : IntegralChain), FiniteBoundaryRepresentation U K Γ →
    IsOpen U → IsClosed K → ∀ a : ℂ, a ∉ K → a ∉ Γ.trace →
    Γ.integral (fun z => 1 / (z - a)) = 0

def specified_fixed_region_index_type : Prop :=
  ∀ (D : Set ℂ) (Γ : IntegralCycle), FixedFiniteGreenRegularRegion D Γ →
    (∀ a ∈ D, Γ.index a = 1) ∧ (∀ a ∉ closure D, Γ.index a = 0)

/-! Local regular-arc and finite-subdivision realization lemmas. -/

def regular_curve_local_coordinate_type : Prop :=
  ∀ (g : ℝ → ℂ) (s : ℝ)
    (_hg : ContDiffAt ℝ 1 g s) (_hv : deriv g s ≠ 0),
    ∃ ψ : ℂ → ℝ, ContDiffAt ℝ 1 ψ (g s) ∧
      ∀ᶠ t in nhds s, ψ (g t) = t

def recover_parameter_contDiffOn_type : Prop :=
  ∀ (f g : ℝ → ℂ) (φ : ℝ → ℝ) (S : Set ℝ)
    (_hf : ContDiffOn ℝ 1 f S) (_hφ : ContinuousOn φ S)
    (_hg : ∀ t ∈ S, ContDiffAt ℝ 1 g (φ t))
    (_hv : ∀ t ∈ S, deriv g (φ t) ≠ 0)
    (_he : EqOn f (fun t => g (φ t)) S),
    ContDiffOn ℝ 1 φ S

def regular_monotone_contour_equivalent_type : Prop :=
  ∀ (U : Set ℂ)
    (γ η : PiecewiseC1Path) (φ : ℝ → ℝ) (g : ℝ → ℂ)
    (_hin : γ.trace ⊆ U)
    (_hc : ContinuousOn φ (Icc η.path.a η.path.b))
    (_hm : MonotoneOn φ (Icc η.path.a η.path.b))
    (_hmap : MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
    (_hsurj : SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b))
    (_hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (_hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (_hγ : EqOn γ g (Icc γ.path.a γ.path.b))
    (_he : EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b)),
    ContourEquivalentOn U (Finsupp.single η 1) (Finsupp.single γ 1)

def ordered_arc_parameter_exists_type : Prop :=
  ∀ (γ η : PiecewiseC1Path)
    (_hinj : InjOn γ (Icc γ.path.a γ.path.b)) (_htrace : η.trace = γ.trace)
    (_horder : ∀ x ∈ Icc η.path.a η.path.b, ∀ y ∈ Icc η.path.a η.path.b,
      x ≤ y → ∀ s ∈ Icc γ.path.a γ.path.b, ∀ t ∈ Icc γ.path.a γ.path.b,
        γ s = η x → γ t = η y → s ≤ t),
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MonotoneOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b)

def ordered_regular_arc_contour_equivalent_type : Prop :=
  ∀ (U : Set ℂ)
    (γ η : PiecewiseC1Path) (g : ℝ → ℂ) (_hin : γ.trace ⊆ U)
    (_hinj : InjOn γ (Icc γ.path.a γ.path.b)) (_htrace : η.trace = γ.trace)
    (_horder : ∀ x ∈ Icc η.path.a η.path.b, ∀ y ∈ Icc η.path.a η.path.b,
      x ≤ y → ∀ s ∈ Icc γ.path.a γ.path.b, ∀ t ∈ Icc γ.path.a γ.path.b,
        γ s = η x → γ t = η y → s ≤ t)
    (_hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (_hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (_hγ : EqOn γ g (Icc γ.path.a γ.path.b)),
    ContourEquivalentOn U (Finsupp.single η 1) (Finsupp.single γ 1)

def contour_patch_exists_type : Prop :=
  ∀ (U : Set ℂ) (Γ : IntegralChain)
    (_hU : IsOpen U) (_hin : Γ.trace ⊆ U),
    ∃ d : ContourPatchData (planeCoordinates.symm ⁻¹' U) Γ,
      ∀ j, (d.path j).trace ⊆ U

def path_patch_representatives_type : Prop :=
  ∀ {O : Set (E 2)} (γ : PiecewiseC1Path)
    (d e : PathPatchData O γ),
    GeometricEquivalent
      (∑ i, Finsupp.single
        (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
      (∑ i, Finsupp.single
        (⟨e.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)

def finite_subdivision_contour_equivalent_type : Prop :=
  ∀ (U : Set ℂ)
    (γ : PiecewiseC1Path) (n : ℕ) (node : Fin (n + 1) → ℝ)
    (_hmono : Monotone node) (_hfirst : node 0 = γ.path.a)
    (_hlast : node (Fin.last n) = γ.path.b)
    (parts : Fin n → PiecewiseC1Path)
    (_hleft : ∀ i, (parts i).path.a = node i.castSucc)
    (_hright : ∀ i, (parts i).path.b = node i.succ)
    (_he : ∀ i, EqOn (parts i) γ (Icc (parts i).path.a (parts i).path.b))
    (_hin : γ.trace ⊆ U),
    ContourEquivalentOn U (Finsupp.single γ 1)
      (∑ i, Finsupp.single (parts i) 1)

def finite_subdivision_exists_type : Prop :=
  ∀ (U : Set ℂ) (γ : PiecewiseC1Path)
    (n : ℕ) (node : Fin (n + 1) → ℝ) (_hmono : Monotone node)
    (_hfirst : node 0 = γ.path.a) (_hlast : node (Fin.last n) = γ.path.b)
    (_hin : γ.trace ⊆ U),
    ∃ parts : Fin n → PiecewiseC1Path,
      (∀ i, (parts i).path.a = node i.castSucc) ∧
      (∀ i, (parts i).path.b = node i.succ) ∧
      (∀ i, EqOn (parts i) γ (Icc (parts i).path.a (parts i).path.b)) ∧
      ContourEquivalentOn U (Finsupp.single γ 1) (∑ i, Finsupp.single (parts i) 1)

def subdivision_subordinate_open_cover_type : Prop :=
  ∀ (U : Set ℂ) (γ : PiecewiseC1Path)
    {ι : Type*} (V : ι → Set ℂ) (_hV : ∀ j, IsOpen (V j))
    (_hcover : γ.trace ⊆ ⋃ j, V j) (_hin : γ.trace ⊆ U),
    ∃ (n : ℕ) (parts : Fin n → PiecewiseC1Path),
      ContourEquivalentOn U (Finsupp.single γ 1) (∑ i, Finsupp.single (parts i) 1) ∧
      (∀ i, ∃ j, (parts i).trace ⊆ V j)

/-! Consequences of the actual arbitrary-Jordan regular-piece interface. -/
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C15.FiniteManifoldBoundaryAssembly.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.DarbouxIntegral.Model hiding E

def boundary_seams_finite_type : Prop :=
  ∀ (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1),
    Z.carrier.Finite

def regular_piece_local_extension_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (u : E 1) (hu : u ∈ closure P.region),
    ∃ (V : Set (E 1)) (g : E 1 → E 2),
      IsOpen V ∧ u ∈ V ∧ ContDiffOn ℝ 1 g V ∧
      EqOn P.map g (closure P.region ∩ V) ∧
      ∀ v ∈ V, Function.Injective (fderiv ℝ g v)

def regular_piece_local_curve_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (u : E 1) (hu : u ∈ closure P.region),
    ∃ (V : Set ℝ) (g : ℝ → ℂ),
      IsOpen V ∧ u 0 ∈ V ∧ ContDiffOn ℝ 1 g V ∧
      (∀ t ∈ V, deriv g t ≠ 0) ∧
      ∀ t ∈ V, scalarPoint t ∈ closure P.region →
        planeCoordinates.symm (P.map (scalarPoint t)) = g t

def regular_piece_local_coordinate_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (u : E 1) (hu : u ∈ closure P.region),
    ∃ (V : Set ℝ) (ψ : ℂ → ℝ), IsOpen V ∧ u 0 ∈ V ∧
      ContDiffAt ℝ 1 ψ (planeCoordinates.symm (P.map u)) ∧
      ∀ t ∈ V, scalarPoint t ∈ closure P.region →
        ψ (planeCoordinates.symm (P.map (scalarPoint t))) = t

def regular_piece_fiber_finite_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (z : E 2),
    (closure P.region ∩ P.map ⁻¹' {z}).Finite

def regular_piece_seam_parameters_finite_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1),
    (closure P.region ∩ P.map ⁻¹' Z.carrier).Finite

def regular_piece_localized_curves_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s),
    ∃ (m : ℕ) (R : Fin m → Set (E 1)) (V : Fin m → Set ℝ) (g : Fin m → ℝ → ℂ),
      (∀ i, Jordan (R i)) ∧ (∀ i, R i ⊆ P.region) ∧
      (Pairwise fun i j => Disjoint (R i) (R j)) ∧ P.region = ⋃ i, R i ∧
      (∀ i, IsOpen (V i)) ∧ (∀ i, (fun u : E 1 => u 0) '' closure (R i) ⊆ V i) ∧
      (∀ i, ContDiffOn ℝ 1 (g i) (V i)) ∧
      (∀ i t, t ∈ V i → deriv (g i) t ≠ 0) ∧
      ∀ i u, u ∈ closure (R i) → planeCoordinates.symm (P.map u) = g i (u 0)

def regular_piece_regular_representatives_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hO : IsOpen O) (hP : RegularPiece o P s),
    ∃ (m : ℕ) (Q : Fin m → Patch 1 O) (V : Fin m → Set ℝ) (g : Fin m → ℝ → ℂ),
      P.region = ⋃ i, (Q i).region ∧
      (Pairwise fun i j => Disjoint (Q i).region (Q j).region) ∧
      (∀ i, IsOpen (V i)) ∧ (∀ i, ContDiffOn ℝ 1 (g i) (V i)) ∧
      (∀ i t, t ∈ V i → deriv (g i) t ≠ 0) ∧
      (∀ i u, u ∈ closure (Q i).region → u 0 ∈ V i) ∧
      (∀ i u, (Q i).map u = planeCoordinates (g i (u 0))) ∧
      (∀ i, EqOn P.map (Q i).map (closure (Q i).region)) ∧
      GeometricEquivalent
        (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
        (∑ i, Finsupp.single
          (⟨Q i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)

def regular_piece_recover_parameter_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (f : ℝ → ℂ) (φ : ℝ → E 1) (S : Set ℝ)
    (hf : ContDiffOn ℝ 1 f S) (hφ : ContinuousOn φ S)
    (hmap : MapsTo φ S (closure P.region))
    (he : EqOn f (fun t => planeCoordinates.symm (P.map (φ t))) S),
    ContDiffOn ℝ 1 φ S

def finite_parameter_patch_integral_zero_type : Prop :=
  ∀ {O : Set (E 2)} (P : Patch 1 O)
    (hfinite : P.region.Finite) (w : E 2 → ℝ) (hw : ContinuousOn w O)
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω),
    patchIntegral P w ω = 0

def patch_integral_finite_cover_off_finite_type : Prop :=
  ∀ {O : Set (E 2)} (P : Patch 1 O)
    (m : ℕ) (R : Fin m → Set (E 1)) (hR : ∀ i, Jordan (R i))
    (hsub : ∀ i, R i ⊆ P.region) (Z : Set (E 1)) (hZ : Z.Finite)
    (hcover : P.region \ Z ⊆ ⋃ i, R i)
    (hpair : ∀ i j, i ≠ j → R i ∩ R j ⊆ Z)
    (w : E 2 → ℝ) (hw : ContinuousOn w O)
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω),
    patchIntegral P w ω =
      ∑ i, patchIntegral (restrictPatch P (R i) (hR i) (hsub i)) w ω


/-! Finite-seam, display-independence, and oriented-assembly continuation. -/

def regular_boundary_display_independent_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (hM : IsCompact M) (hMO : M ⊆ O)
    (d e : RegularBoundaryDisplay (O := O) o)
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω),
    patchChainIntegral ω d.patchChain = patchChainIntegral ω e.patchChain

def patch_equivalent_off_finite_integral_type : Prop :=
  ∀ {O : Set (E 2)}
    (ω : FormField 2 1) (hω : IsCrForm (some 0) O ω)
    (C D : PatchChain 1 O) (h : PatchEquivalentOffFinite C D),
    patchChainIntegral ω C = patchChainIntegral ω D

def assembled_patch_green_dictionary_off_finite_type : Prop :=
  ∀ (O : Set (E 2)) (Γ : IntegralChain) (d : ContourPatchData O Γ)
    (C : PatchChain 1 O) (hC : PatchEquivalentOffFinite C d.patchChain)
    (q : ℂ → ℂ) (hq : ∀ j, ContinuousOn q (d.path j).trace)
    (hr : IsCrForm (some 0) O (realForm q))
    (hi : IsCrForm (some 0) O (imagForm q)),
    Γ.integral q = (patchChainIntegral (realForm q) C : ℂ) +
      Complex.I * (patchChainIntegral (imagForm q) C : ℂ)

def patch_chart_cover_equivalent_type : Prop :=
  ∀ {O : Set (E 2)}
    (p : WeightedPatch 1 O) (m : ℕ) (Q : Fin m → WeightedPatch 1 O)
    (e : Fin m → OpenPartialHomeomorph (E 1) (E 1))
    (he : ∀ i, ContDiffOn ℝ 1 (e i) (e i).source)
    (hei : ∀ i, ContDiffOn ℝ 1 (e i).symm (e i).target)
    (hsource : ∀ i, closure (Q i).patch.region ⊆ (e i).source)
    (hsub : ∀ i, (e i) '' (Q i).patch.region ⊆ p.patch.region)
    (δ : Fin m → ℤ) (hδ : ∀ i, δ i = 1 ∨ δ i = -1)
    (hsign : ∀ i x, x ∈ (e i).source →
      Real.sign ((fderiv ℝ (e i) x).det) = (δ i : ℝ))
    (hmap : ∀ i, EqOn (Q i).patch.map (p.patch.map ∘ (e i)) (Q i).patch.region)
    (hweight : ∀ i, EqOn (Q i).weight p.weight
      (p.patch.map '' ((e i) '' (Q i).patch.region)))
    (Z : Set (E 1)) (hZ : Z.Finite)
    (hcover : p.patch.region \ Z ⊆ ⋃ i, (e i) '' (Q i).patch.region)
    (hpair : ∀ i j, i ≠ j →
      ((e i) '' (Q i).patch.region) ∩ ((e j) '' (Q j).patch.region) ⊆ Z),
    PatchEquivalentOffFinite (Finsupp.single p 1)
      (∑ i, δ i • Finsupp.single (Q i) 1)

def manifold_boundary_assembly_equivalent_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : ManifoldGreenData O),
    PatchEquivalentOffFinite (∑ j, (d.boundaryDisplay j).patchChain) d.outerChain

def manifold_boundary_displays_equivalent_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : ManifoldGreenData O)
    (e : (j : Fin d.count) → RegularBoundaryDisplay (O := O) (d.boundaryOrientation j)),
    PatchEquivalentOffFinite d.outerChain (∑ j, (e j).patchChain)

def regular_arc_representative_exists_type : Prop :=
  ∀ (U : Set ℂ) (γ : PiecewiseC1Path)
    (φ : ℝ → ℝ) (g : ℝ → ℂ)
    (hc : ContinuousOn φ (Icc γ.path.a γ.path.b))
    (hm : MonotoneOn φ (Icc γ.path.a γ.path.b))
    (hg : ∀ t ∈ Icc (φ γ.path.a) (φ γ.path.b), ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc (φ γ.path.a) (φ γ.path.b), deriv g t ≠ 0)
    (he : EqOn γ (fun t => g (φ t)) (Icc γ.path.a γ.path.b))
    (hin : γ.trace ⊆ U),
    ∃ η : PiecewiseC1Path, η.path.a = φ γ.path.a ∧ η.path.b = φ γ.path.b ∧
      EqOn η g (Icc η.path.a η.path.b) ∧ η.trace = γ.trace ∧
      ContourEquivalentOn U (Finsupp.single γ 1) (Finsupp.single η 1)

def regular_piece_closed_restriction_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P Q : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (hsub : closure Q.region ⊆ closure P.region)
    (he : EqOn Q.map P.map (closure Q.region)),
    RegularPiece o Q s

def finite_boundary_representation_of_displays_type : Prop :=
  ∀ (U K : Set ℂ) (Γ : IntegralChain)
    (d : ManifoldGreenData (planeCoordinates.symm ⁻¹' U))
    (hcarrier : d.carrier = planeCoordinates '' K)
    (C : IntegralChain) (htraversal : ContourEquivalentOn U Γ C)
    (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C)
    (hc : ∀ j, (c.path j).trace ⊆ U)
    (e : (j : Fin d.count) → RegularBoundaryDisplay
      (O := planeCoordinates.symm ⁻¹' U) (d.boundaryOrientation j))
    (he : (∑ j, (e j).patchChain) = c.patchChain),
    Nonempty (FiniteBoundaryRepresentation U K Γ)

def path_patches_regular_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path) (d : PathPatchData O γ)
    (hparameter : MapsTo scalarPoint (Icc γ.path.a γ.path.b) (closure P.region))
    (hmap : ∀ t ∈ Icc γ.path.a γ.path.b,
      planeCoordinates (γ t) = P.map (scalarPoint t)),
    ∀ i, RegularPiece o (d.patch i) s


/-! Recover parameters and compare actual interval displays without fixing a partition. -/

def patch_parameter_exists_type : Prop :=
  ∀ {O : Set (E 2)} (P : Patch 1 O)
    (γ : PiecewiseC1Path) (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region),
    ∃ φ : ℝ → E 1, ContinuousOn φ (Icc γ.path.a γ.path.b) ∧
      MapsTo φ (Icc γ.path.a γ.path.b) (closure P.region) ∧
      ∀ t ∈ Icc γ.path.a γ.path.b, P.map (φ t) = planeCoordinates (γ t)

def ordered_regular_piece_parameter_exists_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (horder : ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b,
      x ≤ y → ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0),
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc γ.path.a γ.path.b) ∧
      MonotoneOn φ (Icc γ.path.a γ.path.b) ∧
      MapsTo (fun t => scalarPoint (φ t)) (Icc γ.path.a γ.path.b) (closure P.region) ∧
      (∀ t ∈ Icc γ.path.a γ.path.b,
        planeCoordinates.symm (P.map (scalarPoint (φ t))) = γ t) ∧
      ∀ i, ContDiffOn ℝ 1 φ (γ.partition.pieceSet i)

def regular_piece_interval_curve_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (a b : ℝ) (hab : a < b)
    (hin : MapsTo scalarPoint (Icc a b) (closure P.region)),
    ∀ t ∈ Icc a b,
      ContDiffAt ℝ 1 (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t ∧
      deriv (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t ≠ 0

def ordered_regular_piece_representative_exists_type : Prop :=
  ∀ {O M : Set (E 2)}
    (U : Set ℂ) (o : PositiveManifoldOrientation 1 1 M)
    (P : Patch 1 O) (s : PointSign) (hP : RegularPiece o P s)
    (γ : PiecewiseC1Path) (hU : γ.trace ⊆ U)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (horder : ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b,
      x ≤ y → ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0),
    ∃ (φ : ℝ → ℝ) (η : PiecewiseC1Path),
      ContinuousOn φ (Icc γ.path.a γ.path.b) ∧
      MonotoneOn φ (Icc γ.path.a γ.path.b) ∧
      η.path.a = φ γ.path.a ∧ η.path.b = φ γ.path.b ∧
      EqOn η (fun t => planeCoordinates.symm (P.map (scalarPoint t)))
        (Icc η.path.a η.path.b) ∧
      η.trace = γ.trace ∧
      ContourEquivalentOn U (Finsupp.single γ 1) (Finsupp.single η 1) ∧
      (∀ d : PathPatchData O η, ∀ i, RegularPiece o (d.patch i) s) ∧
      (η.path.a < η.path.b → ∀ t ∈ Icc η.path.a η.path.b,
        deriv (fun u => planeCoordinates.symm (P.map (scalarPoint u))) t ≠ 0)

def path_patch_interval_equivalent_type : Prop :=
  ∀ {O : Set (E 2)}
    (P : Patch 1 O) (γ : PiecewiseC1Path) (d : PathPatchData O γ)
    (hregion : P.region = carrier (intervalBox γ.path.a γ.path.b γ.path.ordered))
    (hmap : ∀ t ∈ Icc γ.path.a γ.path.b, P.map (scalarPoint t) = planeCoordinates (γ t)),
    PatchEquivalentOffFinite
      (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
      (∑ i, Finsupp.single
        (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)

open Specs.D04.C15.FinitePiecewiseStokes.Model

def cell_boundary_assembly_equivalent_type : Prop :=
  ∀ {O : Set (E 2)} (d : CellGreenData O),
    PatchEquivalentOffFinite (∑ j, patchBoundary (d.face j)) d.outerChain

def interval_patch_path_exists_type : Prop :=
  ∀ (U : Set ℂ)
    (P : Patch 1 (planeCoordinates.symm ⁻¹' U))
    (a b : ℝ) (hab : a ≤ b)
    (hregion : P.region = carrier (intervalBox a b hab)),
    ∃ γ : PiecewiseC1Path, γ.path.a = a ∧ γ.path.b = b ∧
      (∀ t ∈ Icc a b, γ t = planeCoordinates.symm (P.map (scalarPoint t))) ∧
      γ.trace ⊆ U ∧
      ∀ d : PathPatchData (planeCoordinates.symm ⁻¹' U) γ,
        PatchEquivalentOffFinite
          (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
            (planeCoordinates.symm ⁻¹' U)) 1)
          (∑ i, Finsupp.single
            (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
              (planeCoordinates.symm ⁻¹' U)) 1)

def cell_boundary_contour_exists_type : Prop :=
  ∀ (U : Set ℂ) (hU : IsOpen U)
    (d : CellGreenData (planeCoordinates.symm ⁻¹' U)),
    ∃ (C : IntegralChain) (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C),
      (∀ k, (c.path k).trace ⊆ U) ∧
      PatchEquivalentOffFinite d.outerChain c.patchChain

/-! Derived directed order, allowing stationary traversals. -/

def monotoneOn_of_finite_pieces_type : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ)
    (node : Fin (n + 1) → ℝ) (hnode : Monotone node)
    (hpieces : ∀ i : Fin n, MonotoneOn f (Icc (node i.castSucc) (node i.succ))),
    MonotoneOn f (Icc (node 0) (node (Fin.last n)))

def parameter_monotone_of_deriv_nonneg_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (φ : ℝ → ℝ)
    (hsmooth : ∀ i : Fin γ.partition.count, ContDiffOn ℝ 1 φ (γ.partition.pieceSet i))
    (hpositive : ∀ i : Fin γ.partition.count, ∀ t ∈ Ioo (γ.partition.node i.castSucc)
      (γ.partition.node i.succ), 0 ≤ deriv φ t),
    MonotoneOn φ (Icc γ.path.a γ.path.b)

def arc_parameter_exists_type : Prop :=
  ∀ (γ η : PiecewiseC1Path)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace),
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b)

def directed_regular_arc_parameter_exists_type : Prop :=
  ∀
    (γ η : PiecewiseC1Path) (g : ℝ → ℂ)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace)
    (hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (hγ : EqOn γ g (Icc γ.path.a γ.path.b))
    (hdirection : ∀ i : Fin η.partition.count, ∀ t ∈ Ioo (η.partition.node i.castSucc)
      (η.partition.node i.succ), ∀ s ∈ Icc γ.path.a γ.path.b,
        γ s = η t → ∃ c : ℝ, 0 ≤ c ∧ deriv η t = c • deriv g s),
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc η.path.a η.path.b) ∧
      MonotoneOn φ (Icc η.path.a η.path.b) ∧
      MapsTo φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      SurjOn φ (Icc η.path.a η.path.b) (Icc γ.path.a γ.path.b) ∧
      EqOn η (fun t => γ (φ t)) (Icc η.path.a η.path.b)

def directed_regular_arc_contour_equivalent_type : Prop :=
  ∀ (U : Set ℂ)
    (γ η : PiecewiseC1Path) (g : ℝ → ℂ) (hin : γ.trace ⊆ U)
    (hinj : InjOn γ (Icc γ.path.a γ.path.b)) (htrace : η.trace = γ.trace)
    (hg : ∀ t ∈ Icc γ.path.a γ.path.b, ContDiffAt ℝ 1 g t)
    (hv : ∀ t ∈ Icc γ.path.a γ.path.b, deriv g t ≠ 0)
    (hγ : EqOn γ g (Icc γ.path.a γ.path.b))
    (hdirection : ∀ i : Fin η.partition.count, ∀ t ∈ Ioo (η.partition.node i.castSucc)
      (η.partition.node i.succ), ∀ s ∈ Icc γ.path.a γ.path.b,
        γ s = η t → ∃ c : ℝ, 0 ≤ c ∧ deriv η t = c • deriv g s),
    ContourEquivalentOn U (Finsupp.single η 1) (Finsupp.single γ 1)

/-! Construct displays from finite original chart traversals. -/

def ordered_regular_piece_interval_display_type : Prop :=
  ∀ {M : Set (E 2)}
    (U : Set ℂ) (o : PositiveManifoldOrientation 1 1 M)
    (P : Patch 1 (planeCoordinates.symm ⁻¹' U)) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (horder : ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b,
      x ≤ y → ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0),
    ∃ (η : PiecewiseC1Path) (Q : Patch 1 (planeCoordinates.symm ⁻¹' U)),
      ContourEquivalentOn U (Finsupp.single γ 1) (Finsupp.single η 1) ∧
      η.trace ⊆ U ∧ RegularPiece o Q s ∧ InjOn Q.map Q.region ∧
      Q.map '' Q.region = planeCoordinates '' γ.trace ∧
      ∀ d : PathPatchData (planeCoordinates.symm ⁻¹' U) η,
        PatchEquivalentOffFinite
          (Finsupp.single (⟨Q, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
            (planeCoordinates.symm ⁻¹' U)) 1)
          (∑ i, Finsupp.single
            (⟨d.patch i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1
              (planeCoordinates.symm ⁻¹' U)) 1)

def regular_boundary_display_of_ordered_arcs_type : Prop :=
  ∀ {M : Set (E 2)}
    (U : Set ℂ) (hU : IsOpen U) (o : PositiveManifoldOrientation 1 1 M)
    (n : ℕ) (γ : Fin n → PiecewiseC1Path)
    (P : Fin n → Patch 1 (planeCoordinates.symm ⁻¹' U)) (s : Fin n → PointSign)
    (hP : ∀ i, RegularPiece o (P i) (s i))
    (hinj : ∀ i, InjOn (P i).map (closure (P i).region))
    (hin : ∀ i, planeCoordinates '' (γ i).trace ⊆ (P i).map '' closure (P i).region)
    (horder : ∀ i, ∀ x ∈ Icc (γ i).path.a (γ i).path.b,
      ∀ y ∈ Icc (γ i).path.a (γ i).path.b, x ≤ y →
      ∀ u ∈ closure (P i).region, ∀ v ∈ closure (P i).region,
        (P i).map u = planeCoordinates (γ i x) →
        (P i).map v = planeCoordinates (γ i y) → u 0 ≤ v 0)
    (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1)
    (hoverlap : ∀ i j, i ≠ j →
      (planeCoordinates '' (γ i).trace) ∩ (planeCoordinates '' (γ j).trace) ⊆ Z.carrier)
    (hcover : M ⊆ (⋃ i, planeCoordinates '' (γ i).trace) ∪ Z.carrier),
    ∃ (e : RegularBoundaryDisplay (O := planeCoordinates.symm ⁻¹' U) o)
      (C : IntegralChain) (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C),
      ContourEquivalentOn U (∑ i, (orientationInteger (s i)) • Finsupp.single (γ i) 1) C ∧
      (∀ i, (c.path i).trace ⊆ U) ∧
      PatchEquivalentOffFinite e.patchChain c.patchChain

/-! Directed chart normalization without supplied visit order. -/

def regular_piece_order_of_tangent_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s) (γ : PiecewiseC1Path)
    (hinj : InjOn P.map (closure P.region))
    (hin : planeCoordinates '' γ.trace ⊆ P.map '' closure P.region)
    (hdirection : ∀ i : Fin γ.partition.count,
      ∀ t ∈ Ioo (γ.partition.node i.castSucc) (γ.partition.node i.succ),
      ∀ u ∈ closure P.region, P.map u = planeCoordinates (γ t) →
        ∃ c : ℝ, 0 ≤ c ∧ deriv γ t =
          c • deriv (fun v => planeCoordinates.symm (P.map (scalarPoint v))) (u 0)),
    ∀ x ∈ Icc γ.path.a γ.path.b, ∀ y ∈ Icc γ.path.a γ.path.b, x ≤ y →
      ∀ u ∈ closure P.region, ∀ v ∈ closure P.region,
        P.map u = planeCoordinates (γ x) → P.map v = planeCoordinates (γ y) →
        u 0 ≤ v 0

def regular_boundary_display_of_directed_arcs_type : Prop :=
  ∀ {M : Set (E 2)}
    (U : Set ℂ) (hU : IsOpen U) (o : PositiveManifoldOrientation 1 1 M)
    (n : ℕ) (γ : Fin n → PiecewiseC1Path)
    (P : Fin n → Patch 1 (planeCoordinates.symm ⁻¹' U)) (s : Fin n → PointSign)
    (hP : ∀ i, RegularPiece o (P i) (s i))
    (hinj : ∀ i, InjOn (P i).map (closure (P i).region))
    (hin : ∀ i, planeCoordinates '' (γ i).trace ⊆ (P i).map '' closure (P i).region)
    (hdirection : ∀ j, ∀ i : Fin (γ j).partition.count,
      ∀ t ∈ Ioo ((γ j).partition.node i.castSucc) ((γ j).partition.node i.succ),
      ∀ u ∈ closure (P j).region, (P j).map u = planeCoordinates (γ j t) →
        ∃ c : ℝ, 0 ≤ c ∧ deriv (γ j) t = c • deriv
          (fun v => planeCoordinates.symm ((P j).map (scalarPoint v))) (u 0))
    (Z : Seams 2) (hdim : ∀ i, Z.dim i < 1)
    (hoverlap : ∀ i j, i ≠ j →
      (planeCoordinates '' (γ i).trace) ∩ (planeCoordinates '' (γ j).trace) ⊆ Z.carrier)
    (hcover : M ⊆ (⋃ i, planeCoordinates '' (γ i).trace) ∪ Z.carrier),
    ∃ (e : RegularBoundaryDisplay (O := planeCoordinates.symm ⁻¹' U) o)
      (C : IntegralChain) (c : ContourPatchData (planeCoordinates.symm ⁻¹' U) C),
      ContourEquivalentOn U (∑ i, (orientationInteger (s i)) • Finsupp.single (γ i) 1) C ∧
      (∀ i, (c.path i).trace ⊆ U) ∧
      PatchEquivalentOffFinite e.patchChain c.patchChain

/-- Every regular Jordan patch has a finite disjoint localization in actual
embedded charts. Injectivity holds on the CLOSED localized sets; neither global
injectivity of the original patch nor interval-shaped Jordan sets is assumed. -/
def regular_piece_injective_localization_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M) (P : Patch 1 O) (s : PointSign)
    (hP : RegularPiece o P s),
    ∃ (m : ℕ) (Q : Fin m → Patch 1 O)
      (c : Fin m → EmbeddedChart 1 1 2 M),
      P.region = ⋃ i, (Q i).region ∧
      (Pairwise fun i j => Disjoint (Q i).region (Q j).region) ∧
      (∀ i, (Q i).region ⊆ P.region) ∧
      (∀ i, EqOn (Q i).map P.map (closure (Q i).region)) ∧
      (∀ i, RegularPiece o (Q i) s) ∧
      (∀ i, closure (Q i).region ⊆ (c i).source) ∧
      (∀ i, EqOn (Q i).map (c i).toFun (closure (Q i).region)) ∧
      (∀ i, ∀ v : (c i).source,
        chartSign o.atPoint (c i) v v.property = s.val) ∧
      (∀ i, InjOn (Q i).map (closure (Q i).region)) ∧
      GeometricEquivalent
        (Finsupp.single (⟨P, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)
        (∑ i, Finsupp.single
          (⟨Q i, fun _ => 1, continuousOn_const⟩ : WeightedPatch 1 O) 1)

/-- Construct a finite injective chart display from any supplied regular
boundary display, retaining its original seams and signed geometric chain. -/
def regular_boundary_injective_display_type : Prop :=
  ∀ {O M : Set (E 2)}
    (o : PositiveManifoldOrientation 1 1 M)
    (d : RegularBoundaryDisplay (O := O) o),
    ∃ (e : RegularBoundaryDisplay (O := O) o)
      (c : Fin e.count → EmbeddedChart 1 1 2 M),
      e.seams = d.seams ∧
      (∀ i, closure (e.patch i).region ⊆ (c i).source) ∧
      (∀ i, EqOn (e.patch i).map (c i).toFun (closure (e.patch i).region)) ∧
      (∀ i, ∀ v : (c i).source,
        chartSign o.atPoint (c i) v v.property = (e.sign i).val) ∧
      (∀ i, InjOn (e.patch i).map (closure (e.patch i).region)) ∧
      GeometricEquivalent d.patchChain e.patchChain

end Specs.D12Complex.Ch04.GreenRegionIndex


namespace D12Complex.GreenRegionIndex
open Specs.D04.C01.EuclideanInterfaces.Model

/-- The original cycle minus the original positive small-circle traversal.
Closedness follows from the supplied cycle and the periodic circle map. -/
def deletedDiskCycle (Γ : IntegralCycle) (a : ℂ) (r : ℝ) : IntegralCycle :=
  ⟨deletedDiskBoundary Γ a r, by
    intro γ hγ
    by_cases he : γ = Specs.D12Complex.Ch04.DiskCauchyFormula.circlePath_value a r
    · subst γ
      change circleMap a r (2 * Real.pi) = circleMap a r 0
      simpa using (periodic_circleMap a r) 0
    · apply Γ.property γ
      apply Finsupp.mem_support_iff.mpr
      change Γ.chain γ ≠ 0
      have hn := Finsupp.mem_support_iff.mp hγ
      simpa [deletedDiskBoundary, Finsupp.single_apply, Ne.symm he] using hn⟩

/-- Supplied real Green geometry and the full positive geometric boundary
relation for the ORIGINAL cycle. The two constructors retain arbitrary actual
D04 manifold displays and cell assemblies. Neither constructor assumes a
contour comparison, Green identity, holomorphic field, or index value. -/
inductive SpecifiedGreenBoundary (K : Set ℂ) (Γ : IntegralCycle) : Prop
  | manifold {q l p : ℕ} {O : Set (E 2)} (open_ambient : IsOpen O)
      (assembly : ManifoldBoundaryDensity.PlanarAssembly q l p O)
      (carrier_eq : complexCoordinates.symm '' (⋃ j, (assembly.piece j).carrier) = K)
      (boundary : ManifoldBoundaryContour.FullPositiveBoundary assembly Γ) :
      SpecifiedGreenBoundary K Γ
  | cells {O : Set (E 2)} (data : CellBoundaryContour.PositiveCellData O)
      (carrier_eq : data.carrier = K)
      (boundary : CellBoundaryContour.IsFullPositiveBoundary data.carrier Γ) :
      SpecifiedGreenBoundary K Γ

/-- A specified bounded open region with the original full oriented boundary,
and supplied real Green geometry before and after a sufficiently small
interior disk is removed. No interior of an arbitrary trace is asserted. -/
structure SpecifiedGreenRegularRegion (D : Set ℂ) (Γ : IntegralCycle) : Prop where
  isOpen : IsOpen D
  bounded : Bornology.IsBounded D
  boundary_trace : Γ.trace ⊆ frontier D
  whole : SpecifiedGreenBoundary (closure D) Γ
  deleted : ∀ a ∈ D, ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ D ∧
    SpecifiedGreenBoundary (closure (D \ Metric.closedBall a r)) (deletedDiskCycle Γ a r)

end D12Complex.GreenRegionIndex

namespace Specs.D12Complex.Ch04.GreenRegionIndex
open _root_.D12Complex _root_.D12Complex.GreenRegionIndex

/-- Green's theorem for the original cycle and fields C1 and holomorphic on
an arbitrary neighborhood of the compact integration carrier. -/
def specified_green_boundary_zero_type : Prop :=
  ∀ (K : Set ℂ) (Γ : IntegralCycle), SpecifiedGreenBoundary K Γ →
    ∀ (U : Set ℂ) (q : ℂ → ℂ), IsOpen U → K ⊆ U →
      ContDiffOn ℝ 1 q U → (∀ z ∈ U, DifferentiableAt ℂ q z) → Γ.integral q = 0

/-- The reciprocal may have its pole elsewhere in the supplied ambient set.
Only absence of the pole on the compact integration carrier is required. -/
def specified_green_reciprocal_zero_type : Prop :=
  ∀ (K : Set ℂ) (Γ : IntegralCycle), SpecifiedGreenBoundary K Γ →
    ∀ a : ℂ, a ∉ K → Γ.integral (fun z => 1 / (z - a)) = 0

def specified_green_boundary_trace_subset_type : Prop :=
  ∀ (K : Set ℂ) (Γ : IntegralCycle), SpecifiedGreenBoundary K Γ → Γ.trace ⊆ K

/-- This pointwise no-pole statement includes every complementary component,
including holes, where the same specified Green calculation applies. -/
def specified_green_boundary_index_zero_type : Prop :=
  ∀ (K : Set ℂ) (Γ : IntegralCycle), SpecifiedGreenBoundary K Γ →
    ∀ a : ℂ, a ∉ K → Γ.index a = 0

/-- The complete source corollary, for both actual Green branches. -/
def specified_green_region_index_type : Prop :=
  ∀ (D : Set ℂ) (Γ : IntegralCycle), SpecifiedGreenRegularRegion D Γ →
    (∀ a ∈ D, Γ.index a = 1) ∧ (∀ a, a ∉ closure D → Γ.index a = 0)

end Specs.D12Complex.Ch04.GreenRegionIndex

namespace Specs.D12Complex.Ch04.GreenRegionIndex
open _root_.D12Complex
open _root_.D12Complex.ManifoldBoundaryDensity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
def planar_assembly_circulation_zero_on_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (f g : E 2 → ℝ) (hO : IsOpen O)
    (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hz : ∀ x ∈ ⋃ j, (A.piece j).carrier, circulationDensity f g x = 0),
    patchChainIntegral (circulationForm f g) (outerPatchChain A) = 0

def planar_assembly_contour_zero_on_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle)
    (hΓ : ManifoldBoundaryContour.FullPositiveBoundary A Γ)
    (Q : ℂ → ℂ) (hQ : ContDiff ℝ 1 Q) (hO : IsOpen O)
    (hhol : ∀ z ∈ complexCoordinates.symm '' (⋃ j, (A.piece j).carrier),
      DifferentiableAt ℂ Q z),
    Γ.integral Q = 0

def planar_assembly_contour_zero_near_type : Prop :=
  ∀ {q l p : ℕ} {O : Set (E 2)}
    (A : PlanarAssembly q l p O) (Γ : IntegralCycle)
    (hΓ : ManifoldBoundaryContour.FullPositiveBoundary A Γ) (hO : IsOpen O)
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : complexCoordinates.symm '' (⋃ j, (A.piece j).carrier) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hhol : ∀ z ∈ U, DifferentiableAt ℂ f z),
    Γ.integral f = 0
end Specs.D12Complex.Ch04.GreenRegionIndex

open scoped Topology
namespace Specs.D12Complex.Ch04.GreenRegionIndex
open _root_.D12Complex
open _root_.D12Complex.GreenRegionIndex
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C12.GreenCirculationAndFlux.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
open Specs.D04.C15.FiniteGeometricPatchIntegrals.Model
open Specs.D04.C15.FinitePiecewiseStokes.Model

def green_densities_eq_of_eventuallyEq_type : Prop :=
  ∀ (Q q : ℂ → ℂ) (z : ℂ)
    (heq : Q =ᶠ[𝓝 z] q),
    fderiv ℝ Q z = fderiv ℝ q z ∧
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
      (fun x => -(Q (planeCoordinates.symm x)).im) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).re)
        (fun x => -(q (planeCoordinates.symm x)).im) (planeCoordinates z) ∧
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
      (fun x => (Q (planeCoordinates.symm x)).re) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).im)
        (fun x => (q (planeCoordinates.symm x)).re) (planeCoordinates z)

def green_densities_eq_of_fderiv_eq_type : Prop :=
  ∀ (Q q : ℂ → ℂ) (z : ℂ)
    (hQ : DifferentiableAt ℝ Q z) (hq : DifferentiableAt ℝ q z)
    (hfd : fderiv ℝ Q z = fderiv ℝ q z),
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
      (fun x => -(Q (planeCoordinates.symm x)).im) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).re)
        (fun x => -(q (planeCoordinates.symm x)).im) (planeCoordinates z) ∧
    circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
      (fun x => (Q (planeCoordinates.symm x)).re) (planeCoordinates z) =
      circulationDensity (fun x => (q (planeCoordinates.symm x)).im)
        (fun x => (q (planeCoordinates.symm x)).re) (planeCoordinates z)

def positive_cell_circulation_zero_on_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (f g : E 2 → ℝ)
    (hf : CrOn 1 O f) (hg : CrOn 1 O g)
    (hzero : ∀ x ∈ (⋃ j, cellExtension (d.cells j) '' cube 2),
      circulationDensity f g x = 0),
    patchChainIntegral (circulationForm f g) d.outer = 0

def positive_cell_green_zero_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (Q : ℂ → ℂ)
    (hQ : ContDiff ℝ 1 Q)
    (hzero : ∀ z ∈ d.carrier,
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).re)
        (fun x => -(Q (planeCoordinates.symm x)).im) (planeCoordinates z) = 0 ∧
      circulationDensity (fun x => (Q (planeCoordinates.symm x)).im)
        (fun x => (Q (planeCoordinates.symm x)).re) (planeCoordinates z) = 0),
    patchChainIntegral (CellBoundaryContour.realForm Q) d.outer = 0 ∧
    patchChainIntegral (CellBoundaryContour.imagForm Q) d.outer = 0

def positive_cell_contour_zero_near_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : CellBoundaryContour.IsFullPositiveBoundary d.carrier Γ)
    (q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hKU : d.carrier ⊆ U)
    (hq : ContDiffOn ℝ 1 q U)
    (hhol : ∀ z ∈ d.carrier, DifferentiableAt ℂ q z),
    Γ.integral q = 0

def positive_cell_reciprocal_boundary_zero_type : Prop :=
  ∀ {O : Set (E 2)}
    (d : CellBoundaryContour.PositiveCellData O) (Γ : IntegralCycle)
    (hΓ : CellBoundaryContour.IsFullPositiveBoundary d.carrier Γ)
    (a : ℂ) (ha : a ∉ d.carrier),
    Γ.integral (fun z => 1 / (z - a)) = 0

end Specs.D12Complex.Ch04.GreenRegionIndex
