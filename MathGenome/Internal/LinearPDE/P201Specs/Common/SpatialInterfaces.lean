import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTraceMap
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Fourier.FourierTransform

/-! Shared spatial conventions for the adopted P201 manuscript.
No solvability, trace, regularity, or energy theorem is a field of these data.
Dimensions are natural numbers; theorem hypotheses impose `1 ≤ n`.
The extra zero dimensional objects make restrictions and coordinate charts uniform.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open Set TopologicalSpace MeasureTheory Metric
open scoped ENNReal ContDiff InnerProductSpace
namespace P201Specs

abbrev SpaceType := ℕ → Type
abbrev Space : SpaceType := fun n => EuclideanSpace ℝ (Fin n)

abbrev DomainType := ℕ → Type
abbrev Domain : DomainType := fun n => Opens (Space n)

/-- Lebesgue measure from the Euclidean inner product. -/
abbrev spatialMeasureType := (n : ℕ) → Measure (Space n)
abbrev spatialMeasure : spatialMeasureType := fun _ => volume

abbrev domainMeasureType := {n : ℕ} → Domain n → Measure (Space n)
abbrev domainMeasure : domainMeasureType := fun Ω => volume.restrict (Ω : Set (Space _))

abbrev TestType := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → Domain n → Type
abbrev Test : TestType := fun 𝕜 _ Ω => P102.U4.TestSpace 𝕜 Ω

/-- Scalar-linear distributional dual; complex distribution tests use no conjugation. -/
abbrev DistributionType := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → Domain n → Type
abbrev Distribution : DistributionType := fun 𝕜 _ Ω => Test 𝕜 Ω →L[𝕜] 𝕜

abbrev MultiIndexType := ℕ → Type
abbrev MultiIndex : MultiIndexType := fun n => P102.U4.MultiIndex n

abbrev coordinateType := (n : ℕ) → Fin n → Space n
abbrev coordinate : coordinateType := P102.U4.coordinateVector

abbrev multiPartialType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Space n → 𝕜) → MultiIndex n → Space n → 𝕜
abbrev multiPartial : multiPartialType := @P102.U4.multiPartial

abbrev distributionDerivativeType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Domain n} → MultiIndex n → Distribution 𝕜 Ω → Distribution 𝕜 Ω
abbrev distributionDerivative : distributionDerivativeType := @P102.U4.distributionPartial

/-- On locally integrable functions this is the integral against a test; that hypothesis is required in applications. -/
abbrev regularDistributionType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Ω : Domain n) → (Space n → 𝕜) → Distribution 𝕜 Ω
abbrev regularDistribution : regularDistributionType := @P102.U4.regularDistribution

abbrev LpType := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → Domain n → ℝ≥0∞ → Type
abbrev Lp : LpType := fun 𝕜 _ Ω p => MeasureTheory.Lp 𝕜 p (domainMeasure Ω)

/-- Canonical distribution-defined W^{k,p}, including p=1 and infinity; its norm is the sum of all derivative norms. -/
abbrev WType := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → Domain n → ℕ → (p : ℝ≥0∞) → [Fact (1 ≤ p)] → Type
abbrev W : WType := fun 𝕜 _ Ω k p _ => P102.U4.Sobolev 𝕜 Ω k p

/-- Change only the finite product norm, preserving every weak derivative. -/
def hilbertTupleToSum {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) (k : ℕ) :
    PiLp 2 (fun _ : P102.U4.SobolevIndex n k => Lp 𝕜 Ω 2) ≃L[𝕜]
      P102.U4.SobolevTuple 𝕜 Ω k 2 :=
  (PiLp.continuousLinearEquiv 2 𝕜 _).trans
    (PiLp.continuousLinearEquiv 1 𝕜 _).symm

/-- The closed weak derivative graph with the L² product norm. -/
def hilbertSubmodule {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) (k : ℕ) :
    Submodule 𝕜 (PiLp 2 (fun _ : P102.U4.SobolevIndex n k => Lp 𝕜 Ω 2)) :=
  (P102.U4.sobolevSubmodule 𝕜 Ω k 2).comap (hilbertTupleToSum 𝕜 Ω k).toLinearMap

/-- H^k = W^{k,2} with the full Hilbert norm: the square root of the sum of squared L² norms of ALL derivatives, including order zero. -/
abbrev HType := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → Domain n → ℕ → Type
abbrev H : HType := fun 𝕜 _ Ω k => ↥(hilbertSubmodule 𝕜 Ω k)

instance {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) (k : ℕ) :
    CompleteSpace (H 𝕜 Ω k) :=
  (P102.U4.sobolevSubmodule_isClosed (Ω := Ω) (m := k) (p := 2)).preimage
    (hilbertTupleToSum 𝕜 Ω k).continuous |>.completeSpace_coe

/-- Exact topological linear identification, with all derivative coordinates unchanged. -/
def hToW {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) (k : ℕ) :
    H 𝕜 Ω k ≃L[𝕜] W 𝕜 Ω k 2 where
  toFun u := ⟨hilbertTupleToSum 𝕜 Ω k u.val, u.property⟩
  invFun u := ⟨(hilbertTupleToSum 𝕜 Ω k).symm u.val, by
    change hilbertTupleToSum 𝕜 Ω k ((hilbertTupleToSum 𝕜 Ω k).symm u.val) ∈ P102.U4.sobolevSubmodule 𝕜 Ω k 2
    simp⟩
  left_inv u := by apply Subtype.ext; exact (hilbertTupleToSum 𝕜 Ω k).symm_apply_apply u.val
  right_inv u := by apply Subtype.ext; exact (hilbertTupleToSum 𝕜 Ω k).apply_symm_apply u.val
  map_add' u v := by apply Subtype.ext; exact (hilbertTupleToSum 𝕜 Ω k).map_add _ _
  map_smul' c u := by apply Subtype.ext; exact (hilbertTupleToSum 𝕜 Ω k).map_smul _ _
  continuous_toFun := (hilbertTupleToSum 𝕜 Ω k).continuous.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (hilbertTupleToSum 𝕜 Ω k).symm.continuous.comp continuous_subtype_val |>.subtype_mk _

/-- The actual full-H¹ closure of compact smooth tests. -/
def hZeroSubmodule {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) :
    Submodule 𝕜 (H 𝕜 Ω 1) :=
  ((P102.U4.smoothSobolevSubmodule 𝕜 Ω 1 2).comap
    (hToW 𝕜 Ω 1).toLinearMap).topologicalClosure

abbrev H10Type := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → Domain n → Type
abbrev H10 : H10Type := fun 𝕜 _ Ω => ↥(hZeroSubmodule 𝕜 Ω)

instance {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n) :
    CompleteSpace (H10 𝕜 Ω) := by
  unfold H10 hZeroSubmodule
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The continuous dual with the full-H¹ closure norm. Weak PDE arguments use 𝕜 = ℝ. -/
abbrev Hminus1Type := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → Domain n → Type
abbrev Hminus1 : Hminus1Type := fun 𝕜 _ Ω => H10 𝕜 Ω →L[𝕜] 𝕜

def hUnderlying {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (k : ℕ) :
    H 𝕜 Ω k →L[𝕜] Lp 𝕜 Ω 2 :=
  (PiLp.proj 2 _ (P102.U4.zeroSobolevIndex n k)).comp
    (hilbertSubmodule 𝕜 Ω k).subtypeL

def hZeroUnderlying {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) :
    H10 𝕜 Ω →L[𝕜] Lp 𝕜 Ω 2 := (hUnderlying Ω 1).comp (hZeroSubmodule 𝕜 Ω).subtypeL

/-- The L² pivot: pivot(f)(v) = (f,v)_{L²}; real duality throughout weak PDE arguments. -/
abbrev pivotType := {n : ℕ} → (Ω : Domain n) → Lp ℝ Ω 2 →L[ℝ] Hminus1 ℝ Ω
abbrev pivot : pivotType := fun Ω =>
  { toFun := fun f => (innerSL ℝ f).comp (hZeroUnderlying Ω)
    map_add' := by intro f g; ext v; simp
    map_smul' := by intro c f; ext v; simp
    cont := (innerSL ℝ (E := Lp ℝ Ω 2)).continuous.clm_comp_const (hZeroUnderlying Ω) }

abbrev laplacianType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Space n → 𝕜) → Space n → 𝕜
abbrev laplacian : laplacianType := fun u x => ∑ i : Fin _, multiPartial u ({i, i} : MultiIndex _) x

abbrev distributionLaplacianType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Domain n} → Distribution 𝕜 Ω → Distribution 𝕜 Ω
abbrev distributionLaplacian : distributionLaplacianType := fun u => ∑ i : Fin _, distributionDerivative ({i, i} : MultiIndex _) u

abbrev gradientType := {n : ℕ} → (Space n → ℝ) → Space n → Space n
abbrev gradient : gradientType := fun u x => WithLp.toLp 2 (fun i => fderiv ℝ u x (coordinate _ i))

abbrev divergenceType := {n : ℕ} → (Space n → Space n) → Space n → ℝ
abbrev divergence : divergenceType := fun F x => ∑ i : Fin _, fderiv ℝ (fun y => F y i) x (coordinate _ i)

/-- The classical sign is -div(A grad u). -/
abbrev positiveDivergenceType := {n : ℕ} → (Space n → Space n →L[ℝ] Space n) → (Space n → ℝ) → Space n → ℝ
abbrev positiveDivergence : positiveDivergenceType := fun A u x => -divergence (fun y => A y (gradient u y)) x

/-- Distributional convention on locally integrable fields; no unjustified continuity certificate is assumed. -/
abbrev weakNegativeDivergenceType := {n : ℕ} → (Ω : Domain n) → (Space n → Space n) → Test ℝ Ω → ℝ
abbrev weakNegativeDivergence : weakNegativeDivergenceType := fun Ω F φ => ∫ x in Ω, inner ℝ (F x) (gradient φ x)

abbrev fourierPhaseType := {n : ℕ} → Space n → Space n → ℂ
abbrev fourierPhase : fourierPhaseType := fun x ξ => Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ))

/-- Integral Fourier convention; integral identities require integrability in their own hypotheses. -/
abbrev fourierIntegralType := {n : ℕ} → (Space n → ℂ) → Space n → ℂ
abbrev fourierIntegral : fourierIntegralType := fun f ξ => ∫ x, fourierPhase x ξ * f x

abbrev hFirstDerivativeType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Domain n} → H 𝕜 Ω 1 → Fin n → Lp 𝕜 Ω 2
abbrev hFirstDerivative : hFirstDerivativeType := fun {n} {𝕜} _ {Ω} u j => P102.U4.sobolevDerivative (hToW 𝕜 Ω 1 u) ⟨{j}, by simp⟩

abbrev hGradientType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Domain n} → H 𝕜 Ω 1 → MeasureTheory.Lp (EuclideanSpace 𝕜 (Fin n)) 2 (domainMeasure Ω)
abbrev hGradient : hGradientType := fun u => (MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp (hFirstDerivative u j))).toLp (fun x => WithLp.toLp 2 (fun j => hFirstDerivative u j x))

/-- Source energy convention: linear in u, conjugate-linear in the second test v. No symmetry of A is required; bounded measurable coefficients are supplied in theorems about this form. -/
abbrev ellipticEnergyFormType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Ω : Domain n) → (Space n → Matrix (Fin n) (Fin n) 𝕜) → H 𝕜 Ω 1 → H 𝕜 Ω 1 → 𝕜
abbrev ellipticEnergyForm : ellipticEnergyFormType := fun Ω A u v => ∫ x in Ω, ∑ i, ∑ j, A x i j * hFirstDerivative u j x * star (hFirstDerivative v i x)

/-- The actual scalar-linear distribution -div F, obtained by transposition. Its integral convention applies to locally integrable F. -/
abbrev negativeDivergenceDistributionType := {n : ℕ} → (Ω : Domain n) → (Space n → Space n) → Distribution ℝ Ω
abbrev negativeDivergenceDistribution : negativeDivergenceDistributionType := fun Ω F => -∑ i : Fin _, distributionDerivative ({i} : MultiIndex _) (regularDistribution Ω (fun x => F x i))

/-- Canonical Euclidean graph-coordinate isometry, including m=0. Geometry predicates use this fixed frame, without adding a coordinate-frame hypothesis. -/
abbrev graphFrameType := (m : ℕ) → P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1)
abbrev graphFrame : graphFrameType := fun m =>
  { toLinearEquiv := (P102.Trace.Ordinary.alignedCoordinates m).symm.toLinearEquiv
    norm_map' := by
      intro z
      change ‖(P102.Trace.Ordinary.alignedCoordinates m).symm z‖ = ‖z‖
      let x := (P102.Trace.Ordinary.alignedCoordinates m).symm z
      have hx : ‖P102.Trace.Ordinary.alignedCoordinates m x‖ = ‖x‖ := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        change (∑ i, ‖(P102.Trace.Ordinary.alignedCoordinates m x).ofLp.1 i‖ ^ 2) +
          ‖(P102.Trace.Ordinary.alignedCoordinates m x).ofLp.2‖ ^ 2 = ∑ i, ‖x i‖ ^ 2
        simp only [P102.Trace.Ordinary.alignedCoordinates_horizontal,
          P102.Trace.Ordinary.alignedCoordinates_height]
        exact (Fin.sum_univ_castSucc (fun i => ‖x i‖ ^ 2)).symm
      simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hx.symm }

/-- The pinned graph-chart condition includes boundedness but does not impose connectedness or nonemptiness. The isometry just chooses Euclidean graph coordinates; m=0 is allowed. -/
abbrev IsBoundedLipschitzOpenType := {m : ℕ} → Domain (m + 1) → Prop
abbrev IsBoundedLipschitzOpen : IsBoundedLipschitzOpenType := fun {m} Ω => P102.Sobolev.Geometry.IsLipschitzOpen (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (P102.U4.GraphPieces.Ambient m))

/-- Local one-sided C^k graph boundary; no global boundedness is built in. -/
abbrev HasCkBoundaryType := {m : ℕ} → Domain (m + 1) → ℕ∞ → Prop
abbrev HasCkBoundary : HasCkBoundaryType := fun {m} Ω k => ∀ p ∈ frontier (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (P102.U4.GraphPieces.Ambient m)), ∃ C : P102.Sobolev.Geometry.BoundaryChart (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (P102.U4.GraphPieces.Ambient m)), C.frame (P102.U4.GraphPieces.graph C.graphFunction C.center) = p ∧ ContDiffOn ℝ k C.graphFunction (ball C.center C.radius)

/-- C^{1,1}: a C¹ graph with Lipschitz first derivative in each local chart. -/
abbrev HasC11BoundaryType := {m : ℕ} → Domain (m + 1) → Prop
abbrev HasC11Boundary : HasC11BoundaryType := fun {m} Ω => ∀ p ∈ frontier (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (P102.U4.GraphPieces.Ambient m)), ∃ C : P102.Sobolev.Geometry.BoundaryChart (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω : Set (P102.U4.GraphPieces.Ambient m)), C.frame (P102.U4.GraphPieces.graph C.graphFunction C.center) = p ∧ ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius) ∧ ∃ L, LipschitzOnWith L (fderiv ℝ C.graphFunction) (ball C.center C.radius)

/-- Euclidean-normalized Hausdorff measure restricted to the boundary. In dimension one this is H^0, i.e. counting measure. -/
abbrev boundaryMeasureType := {m : ℕ} → Domain (m + 1) → Measure (Space (m + 1))
abbrev boundaryMeasure : boundaryMeasureType := @P102.Trace.Ordinary.boundaryMeasure

/-- Euclidean spherical surface measure via polar cones (n times the volume of the unit truncated cone). In dimension one it is explicitly the two endpoint Dirac masses, each of weight one. -/
abbrev unitSurfaceType := (n : ℕ) → Measure (Space n)
abbrev unitSurface : unitSurfaceType := fun n => if n = 1 then Measure.dirac (WithLp.toLp 2 (fun _ => (1 : ℝ))) + Measure.dirac (WithLp.toLp 2 (fun _ => (-1 : ℝ))) else Measure.map (fun θ : sphere (0 : Space n) 1 => (θ : Space n)) (volume : Measure (Space n)).toSphere

/-- omega n denotes the manuscript’s omega_{n-1}. -/
abbrev omegaType := ℕ → ℝ
abbrev omega : omegaType := fun n => (unitSurface n).real univ

/-- Surface measure on a sphere of positive radius r; applications impose 0<r. This is the pushforward of unit surface measure times r^{n-1}. -/
abbrev sphereSurfaceType := {n : ℕ} → Space n → ℝ → Measure (Space n)
abbrev sphereSurface : sphereSurfaceType := fun {n} a r => ENNReal.ofReal (r ^ (n - 1)) • Measure.map (fun θ => a + r • θ) (unitSurface n)

abbrev ballAverageType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Space n → 𝕜) → Space n → ℝ → 𝕜
abbrev ballAverage : ballAverageType := fun f a r => (volume.real (ball a r))⁻¹ • ∫ x in ball a r, f x

/-- Normalized by the actual surface mass. Formulas for averages require integrability and positive radius. -/
abbrev sphereAverageType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Space n → 𝕜) → Space n → ℝ → 𝕜
abbrev sphereAverage : sphereAverageType := fun f a r => ((sphereSurface a r).real univ)⁻¹ • ∫ x, f x ∂sphereSurface a r

/-- Classical interior divergence equation; boundary conditions are separate data. -/
abbrev IsClassicalEllipticSolutionType := {n : ℕ} → (Ω : Domain n) → (Space n → Space n →L[ℝ] Space n) → (Space n → ℝ) → (Space n → ℝ) → Prop
abbrev IsClassicalEllipticSolution : IsClassicalEllipticSolutionType := fun Ω A f u => ContDiffOn ℝ 1 A Ω ∧ ContDiffOn ℝ 2 u Ω ∧ ContinuousOn f Ω ∧ ∀ x ∈ Ω, positiveDivergence A u x = f x

/-- Interior tests impose no boundary value; F is the flux, e.g. A grad u. -/
abbrev IsDistributionalEllipticSolutionType := {n : ℕ} → (Ω : Domain n) → (Space n → Space n) → (Space n → ℝ) → Prop
abbrev IsDistributionalEllipticSolution : IsDistributionalEllipticSolutionType := fun Ω F f => LocallyIntegrableOn F Ω volume ∧ LocallyIntegrableOn f Ω volume ∧ ∀ φ : Test ℝ Ω, weakNegativeDivergence Ω F φ = ∫ x in Ω, f x * φ x

/-- The variational realization A is supplied as a continuous form operator on the actual H¹ closure, not an assumed PDE solver. -/
abbrev IsWeakDirichletSolutionType := {n : ℕ} → (Ω : Domain n) → (H10 ℝ Ω →L[ℝ] Hminus1 ℝ Ω) → Hminus1 ℝ Ω → H10 ℝ Ω → Prop
abbrev IsWeakDirichletSolution : IsWeakDirichletSolutionType := fun _ A f u => A u = f

/-- For a C₀ semigroup S, this is the Duhamel solution class; its forcing takes values in X, not automatically in the energy dual. -/
abbrev IsMildSolutionType := (X : Type) → [NormedAddCommGroup X] → [NormedSpace ℝ X] → [CompleteSpace X] → (ℝ → X →L[ℝ] X) → ℝ → X → (ℝ → X) → (ℝ → X) → Prop
abbrev IsMildSolution : IsMildSolutionType := fun _ _ _ _ S T u₀ f u => IntegrableOn f (Ioo 0 T) ∧ ContinuousOn u (Icc 0 T) ∧ ∀ t ∈ Icc 0 T, u t = S t u₀ + ∫ s in Icc 0 t, S (t-s) (f s)

/-- Distributional time derivative in (H¹₀)′ using the L² pivot and compact smooth scalar time tests. Applications require T>0. -/
abbrev HasEnergyTimeDerivativeType := {n : ℕ} → (Ω : Domain n) → ℝ → (ℝ → H10 ℝ Ω) → (ℝ → Hminus1 ℝ Ω) → Prop
abbrev HasEnergyTimeDerivative : HasEnergyTimeDerivativeType := fun Ω T u du => MemLp u 2 (volume.restrict (Ioo 0 T)) ∧ MemLp du 2 (volume.restrict (Ioo 0 T)) ∧ ∀ v : H10 ℝ Ω, ∀ φ : TestFunction (⟨Ioo 0 T, isOpen_Ioo⟩ : Opens ℝ) ℝ ⊤, (∫ t in Ioo 0 T, deriv φ t * inner ℝ (hZeroUnderlying Ω (u t)) (hZeroUnderlying Ω v)) = -(∫ t in Ioo 0 T, φ t * du t v)

/-- Homogeneous Dirichlet evolution in the energy class with its separate continuous L² representative. No existence or energy identity is assumed. -/
abbrev IsDirichletEnergySolutionType := {n : ℕ} → (Ω : Domain n) → ℝ → (H10 ℝ Ω →L[ℝ] Hminus1 ℝ Ω) → Lp ℝ Ω 2 → (ℝ → Hminus1 ℝ Ω) → (ℝ → H10 ℝ Ω) → (ℝ → Hminus1 ℝ Ω) → (ℝ → Lp ℝ Ω 2) → Prop
abbrev IsDirichletEnergySolution : IsDirichletEnergySolutionType := fun Ω T A u₀ f u du U => HasEnergyTimeDerivative Ω T u du ∧ ContinuousOn U (Icc 0 T) ∧ U 0 = u₀ ∧ (∀ᵐ t ∂volume.restrict (Ioo 0 T), U t = hZeroUnderlying Ω (u t)) ∧ (∀ᵐ t ∂volume.restrict (Ioo 0 T), du t + A (u t) = f t)


open scoped Pointwise
instance (n : ℕ) : IsFiniteMeasure (unitSurface n) := by
  unfold unitSurface
  split_ifs <;> infer_instance

instance {n : ℕ} (a : Space n) (r : ℝ) : IsFiniteMeasure (sphereSurface a r) := by
  constructor
  change ENNReal.ofReal (r ^ (n - 1)) * _ < ⊤
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

abbrev hToWExportType := {n : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → (Ω : Domain n) → (k : ℕ) → H 𝕜 Ω k ≃L[𝕜] W 𝕜 Ω k 2

abbrev hUnderlyingExportType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Ω : Domain n) → (k : ℕ) → H 𝕜 Ω k →L[𝕜] Lp 𝕜 Ω 2

abbrev hZeroUnderlyingExportType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Ω : Domain n) → H10 𝕜 Ω →L[𝕜] Lp 𝕜 Ω 2

def fullHilbertNormStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (k : ℕ) (u : H 𝕜 Ω k),
    ‖u‖ ^ 2 = ∑ α : P102.U4.SobolevIndex n k, ‖P102.U4.sobolevDerivative (hToW 𝕜 Ω k u) α‖ ^ 2

def hilbertDerivativeDistributionStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (k : ℕ) (u : H 𝕜 Ω k)
    (α : P102.U4.SobolevIndex n k),
    distributionDerivative α.val (regularDistribution Ω (hUnderlying Ω k u)) =
      regularDistribution Ω (P102.U4.sobolevDerivative (hToW 𝕜 Ω k u) α)

def hilbertUnderlyingInjectiveStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (k : ℕ),
    Function.Injective (hUnderlying (𝕜 := 𝕜) Ω k)

def hZeroClosureBridgeStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Domain n),
    hZeroSubmodule 𝕜 Ω = (P102.U4.sobolevZeroSubmodule 𝕜 Ω 1 2).comap
      (hToW 𝕜 Ω 1).toLinearMap

def pivotPairingStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (f : Lp ℝ Ω 2) (v : H10 ℝ Ω),
    pivot Ω f v = ∫ x in Ω, f x * hZeroUnderlying Ω v x

def boundaryCountingMeasureStatement : Prop :=
  ∀ Ω : Domain 1, boundaryMeasure Ω =
    Measure.count.restrict (frontier (Ω : Set (Space 1)))

def fourierNormalizationStatement : Prop :=
  ∀ {n : ℕ} (f : Space n → ℂ) (ξ : Space n),
    fourierIntegral f ξ = FourierTransform.fourier f ξ

def unitSurfaceDimensionOneStatement : Prop :=
  unitSurface 1 =
    Measure.dirac (P102.Trace.Ordinary.linePoint 1) +
      Measure.dirac (P102.Trace.Ordinary.linePoint (-1))

def endpointPositiveMassStatement : Prop :=
  unitSurface 1 {P102.Trace.Ordinary.linePoint 1} = 1

def endpointNegativeMassStatement : Prop :=
  unitSurface 1 {P102.Trace.Ordinary.linePoint (-1)} = 1

def oneDimensionalBallVolumeStatement : Prop :=
  (volume : Measure (Space 1)).real (ball 0 1) = 2

def unitSurfaceMassStatement : Prop :=
  ∀ n : ℕ, (unitSurface n).real univ = (n : ℝ) * (volume : Measure (Space n)).real (ball 0 1)

def ballVolumeNormalizationStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (a : Space n) (r : ℝ), 0 ≤ r →
    (volume : Measure (Space n)).real (ball a r) = omega n * r ^ n / (n : ℝ)

def sphereSurfaceMassStatement : Prop :=
  ∀ {n : ℕ} (a : Space n) (r : ℝ), 0 ≤ r →
    (sphereSurface a r).real univ = omega n * r ^ (n - 1)

def unitSurfaceConeStatement : Prop :=
  ∀ {n : ℕ}, n ≠ 1 → ∀ s : Set (sphere (0 : Space n) 1), MeasurableSet s →
    unitSurface n ((Subtype.val : sphere (0 : Space n) 1 → Space n) '' s) =
      (n : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 • ((Subtype.val : sphere (0 : Space n) 1 → Space n) '' s))

end P201Specs
