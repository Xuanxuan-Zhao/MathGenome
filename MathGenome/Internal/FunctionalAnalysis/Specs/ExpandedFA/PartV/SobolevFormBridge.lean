import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevCompleteness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.GalerkinExistence
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! The gradient realization changes the norm, not the Sobolev elements or
boundary condition. Its closedness/completeness and its equivalence to W₀ are
conclusions below. There is no gradient norm on nonempty dimension-zero W₀. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace ExpandedFA.PartV.SobolevFormBridge
open ExpandedFA.Sobolev ExpandedFA.Sobolev.NegativeSobolev ExpandedFA.Distributions

abbrev W (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  W0 𝕜 Ω 2 (by norm_num)
abbrev Vector (𝕜 : Type) (d : ℕ) := EuclideanSpace 𝕜 (Fin d)
abbrev VectorL2 (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  Lp (Vector 𝕜 d) 2 (volume.restrict (Ω : Set (Domain d)))

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- The actual weak gradient as a vector-valued a.e. class. -/
theorem gradientMemLp (u : W 𝕜 Ω) :
    MemLp (gradientFunction u.val) 2 (volume.restrict (Ω : Set (Domain d))) :=
  MemLp.of_eval_piLp fun i => Lp.memLp (u.val.val (coordinateIndex i))

def gradientL2 (u : W 𝕜 Ω) : VectorL2 𝕜 Ω :=
  (gradientMemLp u).toLp (gradientFunction u.val)

/-- This formula is independent of any candidate implementation. -/
def gradientMap : W 𝕜 Ω →ₗ[𝕜] VectorL2 𝕜 Ω where
  toFun := gradientL2
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(gradientMemLp (u + v)).coeFn_toLp,
      (gradientMemLp u).coeFn_toLp, (gradientMemLp v).coeFn_toLp,
      Lp.coeFn_add (gradientL2 u) (gradientL2 v),
      ae_all_iff.mpr (fun i : Fin d =>
        Lp.coeFn_add (u.val.val (coordinateIndex i)) (v.val.val (coordinateIndex i)))]
      with x huv hu hv hadd hc
    simp only [gradientL2] at *
    rw [huv, hadd, Pi.add_apply, hu, hv]
    ext i
    exact hc i
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(gradientMemLp (c • u)).coeFn_toLp,
      (gradientMemLp u).coeFn_toLp, Lp.coeFn_smul c (gradientL2 u),
      ae_all_iff.mpr (fun i : Fin d =>
        Lp.coeFn_smul c (u.val.val (coordinateIndex i)))]
      with x hcu hu hsmul hc
    simp only [gradientL2, RingHom.id_apply] at *
    rw [hcu, hsmul, Pi.smul_apply, hu]
    ext i
    exact hc i

abbrev Energy (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  LinearMap.range (gradientMap (𝕜 := 𝕜) (Ω := Ω))

/-- The corrected energy-space scope; no boundary regularity is needed for
these stronger assertions, so bounded C¹ domains are included. -/
def EnergyScope (Ω : Opens (Domain d)) : Prop :=
  Bornology.IsBounded (Ω : Set (Domain d)) ∧
    (0 < d ∨ (Ω : Set (Domain d)) = ∅)

/-- Ordinary scalar matrices acting on the Euclidean gradient coordinates. -/
def matrixOperatorEquiv (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    Matrix (Fin d) (Fin d) 𝕜 ≃ₗ[𝕜] (Vector 𝕜 d →L[𝕜] Vector 𝕜 d) :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

namespace Spec

def GradientNorm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (u : W 𝕜 Ω),
  ‖gradientMap u‖ = gradientLpNorm u.val ∧
  ‖gradientMap u‖ ^ 2 = ∑ i : Fin d, ‖u.val.val (coordinateIndex i)‖ ^ 2

def HilbertRealization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), EnergyScope Ω →
  CompleteSpace (Energy 𝕜 Ω) ∧
  ∃ e : W 𝕜 Ω ≃L[𝕜] Energy 𝕜 Ω,
    (∀ u, (e u).val = gradientMap u) ∧
    (∀ u, ‖e u‖ = gradientLpNorm u.val) ∧
    (∀ u v, ⟪e u, e v⟫_𝕜 =
      ∫ x, ⟪gradientFunction u.val x, gradientFunction v.val x⟫_𝕜
        ∂(volume.restrict (Ω : Set (Domain d))))

def EmptySpace : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), (Ω : Set (Domain d)) = ∅ →
  Subsingleton (W 𝕜 Ω) ∧ Subsingleton (Energy 𝕜 Ω)

def Solvability : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), EnergyScope Ω →
  ∀ (a : Hilbert.Conventions.Spec.BoundedSesquilinearFormValue 𝕜 (Energy 𝕜 Ω) (Energy 𝕜 Ω))
    (c : ℝ), Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 (Energy 𝕜 Ω) a c →
  ∀ F : Energy 𝕜 Ω →L⋆[𝕜] 𝕜, ∃! u, ∀ v, a v u = F v

/-- The coercive form gives a scalar-linear isomorphism onto the antidual
with its pointwise scalar structure. -/
def CoerciveIsomorphism : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), EnergyScope Ω →
  ∀ (a : Hilbert.Conventions.Spec.BoundedSesquilinearFormValue 𝕜 (Energy 𝕜 Ω) (Energy 𝕜 Ω))
    (c : ℝ), Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 (Energy 𝕜 Ω) a c →
  ∃ e : Energy 𝕜 Ω ≃L[𝕜] (Energy 𝕜 Ω →L⋆[𝕜] 𝕜),
    ∀ u v, e u v = a v u

/-- Every full-norm scalar-linear datum becomes an energy antidual datum by
conjugating its values; every energy antidual arises this way. The recovered
negative-Sobolev coefficients use the canonical full Sobolev norm. -/
def NegativeSobolevBridge : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), EnergyScope Ω →
  ∃ e : W 𝕜 Ω ≃L[𝕜] Energy 𝕜 Ω,
    (∀ u, (e u).val = gradientMap u) ∧
    ∀ F : Energy 𝕜 Ω →L⋆[𝕜] 𝕜,
      ∃ (G : W 𝕜 Ω →L[𝕜] 𝕜) (f : Option (Fin d) → DomainLp 𝕜 Ω 2),
        (∀ u, F (e u) = conj (G u)) ∧
        (∀ u, G u = ∫ x, u.val.val (zeroIndex d 1) x * f none x
          ∂(volume.restrict (Ω : Set (Domain d))) +
          ∑ i : Fin d, ∫ x, u.val.val (coordinateIndex i) x * f (some i) x
            ∂(volume.restrict (Ω : Set (Domain d)))) ∧
        ‖f‖ = ‖G‖ ∧
        (∀ (φ : Tests 𝕜 Ω) (u : W 𝕜 Ω),
          u.val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] φ →
          F (e u) = conj (coefficientDistribution f φ))

/-- Conjugation of values interchanges the scalar dual and antidual,
with exactly the same operator norm, in both directions. -/
def DatumConjugation : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E],
  (∀ G : E →L[𝕜] 𝕜, ∃ F : E →L⋆[𝕜] 𝕜,
    (∀ x, F x = conj (G x)) ∧ ‖F‖ = ‖G‖) ∧
  (∀ F : E →L⋆[𝕜] 𝕜, ∃ G : E →L[𝕜] 𝕜,
    (∀ x, G x = conj (F x)) ∧ ‖G‖ = ‖F‖)

def DerivativeData : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), EnergyScope Ω →
  ∃ e : W 𝕜 Ω ≃L[𝕜] Energy 𝕜 Ω,
    (∀ u, (e u).val = gradientMap u) ∧
    ∀ F : Energy 𝕜 Ω →L⋆[𝕜] 𝕜,
      ∃ f : Fin d → DomainLp 𝕜 Ω 2, ∀ u,
        F (e u) = conj (∑ i : Fin d,
          ∫ x, u.val.val (coordinateIndex i) x * f i x
            ∂(volume.restrict (Ω : Set (Domain d))))

/-- Finite-dimensional bounded measurable matrices, represented equivalently
as linear operators on the Euclidean coordinate vector. No symmetry required. -/
def MatrixSolvability : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), EnergyScope Ω →
  ∀ (A : Domain d → Vector 𝕜 d →L[𝕜] Vector 𝕜 d) (M c : ℝ),
    AEStronglyMeasurable A (volume.restrict (Ω : Set (Domain d))) →
    0 ≤ M → (∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), ‖A x‖ ≤ M) →
    0 < c →
    (∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      ∀ ξ, c * ‖ξ‖ ^ 2 ≤ RCLike.re ⟪ξ, A x ξ⟫_𝕜) →
    ∃ a : Hilbert.Conventions.Spec.BoundedSesquilinearFormValue 𝕜 (Energy 𝕜 Ω) (Energy 𝕜 Ω),
      (∀ v u, a v u = ∫ x, ⟪v.val x, A x (u.val x)⟫_𝕜
        ∂(volume.restrict (Ω : Set (Domain d)))) ∧
      ‖a‖ ≤ M ∧
      Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 (Energy 𝕜 Ω) a c ∧
      ∀ F : Energy 𝕜 Ω →L⋆[𝕜] 𝕜, ∃! u, ∀ v, a v u = F v

/-- The source's displayed matrix formula, now with scalar entries.
Boundedness is stated in its Euclidean operator norm. -/
def MatrixEntries : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), EnergyScope Ω →
  ∀ (A : Domain d → Matrix (Fin d) (Fin d) 𝕜) (M c : ℝ),
    AEStronglyMeasurable A (volume.restrict (Ω : Set (Domain d))) →
    0 ≤ M →
    (∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), ‖matrixOperatorEquiv 𝕜 d (A x)‖ ≤ M) →
    0 < c →
    (∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      ∀ ξ : Vector 𝕜 d, c * ‖ξ‖ ^ 2 ≤
        RCLike.re (∑ i, conj (ξ i) * ∑ j, A x i j * ξ j)) →
    ∃ a : Hilbert.Conventions.Spec.BoundedSesquilinearFormValue 𝕜 (Energy 𝕜 Ω) (Energy 𝕜 Ω),
      (∀ v u, a v u = ∫ x, ∑ i, conj (v.val x i) * ∑ j, A x i j * u.val x j
        ∂(volume.restrict (Ω : Set (Domain d)))) ∧
      ‖a‖ ≤ M ∧
      Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 (Energy 𝕜 Ω) a c ∧
      ∀ F : Energy 𝕜 Ω →L⋆[𝕜] 𝕜, ∃! u, ∀ v, a v u = F v

def AntidualBanach : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)),
    CompleteSpace (Energy 𝕜 Ω →L⋆[𝕜] 𝕜) ∧
    (∀ (F G : Energy 𝕜 Ω →L⋆[𝕜] 𝕜) (c : 𝕜) (v : Energy 𝕜 Ω),
      (F + G) v = F v + G v ∧ (c • F) v = c * F v)

end Spec
end ExpandedFA.PartV.SobolevFormBridge
