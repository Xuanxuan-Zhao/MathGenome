import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.Plancherel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierInversion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.Analysis.Distribution.FourierMultiplier

/-! Independent specification of the assigned four clauses of
`fa2:p4:sobolev-hilbert`. Hs uses weighted Fourier coordinates in L². The
realization and exact image statements below are essential: the L² model alone
is not a definition of the required space of tempered distributions.
All dimensions, including zero, and all real orders are retained. -/

noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

/-- The manuscript's exact squared frequency weight. -/
def frequencyWeight {d : ℕ} (ξ : Euclidean d) : ℝ :=
  1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

/-- Half of the order occurs here because the defining norm is squared. -/
def weight {d : ℕ} (s : ℝ) (ξ : Euclidean d) : ℝ :=
  (frequencyWeight ξ) ^ (s / 2)

def complexWeight {d : ℕ} (s : ℝ) (ξ : Euclidean d) : ℂ := weight s ξ

/-- Abstract weighted Fourier coordinates. The embedding below specifies which
actual tempered distribution each element represents. -/
def Hs (d : ℕ) (_s : ℝ) : Type := L2 d

instance (d : ℕ) (s : ℝ) : NormedAddCommGroup (Hs d s) :=
  inferInstanceAs (NormedAddCommGroup (L2 d))
instance (d : ℕ) (s : ℝ) : InnerProductSpace ℂ (Hs d s) :=
  inferInstanceAs (InnerProductSpace ℂ (L2 d))
instance (d : ℕ) (s : ℝ) : CompleteSpace (Hs d s) :=
  inferInstanceAs (CompleteSpace (L2 d))

/-- Weighted Fourier coordinates, with the L² norm. -/
def coordinates (d : ℕ) (s : ℝ) : Hs d s ≃ₗᵢ[ℂ] L2 d :=
  LinearIsometryEquiv.refl ℂ _

/-- The Fourier density represented by an abstract Hs element. -/
def fourierDensity {d : ℕ} {s : ℝ} (u : Hs d s) (ξ : Euclidean d) : ℂ :=
  complexWeight (-s) ξ * coordinates d s u ξ

/-- Realization by inverse Fourier transform of the weighted L² density.
The native pointwise-dual topology does not change the underlying continuous
scalar-linear functional used by the manuscript's Tempered interface. -/
def realization {d : ℕ} {s : ℝ} (u : Hs d s) : Tempered ℂ d :=
  𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (complexWeight (-s))
    (Lp.toTemperedDistribution (coordinates d s u)))

/-- A regular Fourier density is paired bilinearly with Schwartz tests. Local
integrability excludes spurious densities caused by the total integral. -/
def HasFourierDensity {d : ℕ} (T : Tempered ℂ d) (f : Euclidean d → ℂ) : Prop :=
  LocallyIntegrable f volume ∧ ∀ φ : Schwartz ℂ d,
    Integrable (fun ξ => φ ξ * f ξ) ∧
    temperedFourier T φ = ∫ ξ, φ ξ * f ξ

/-- The original, unbundled definition of H^s as tempered distributions. -/
def MemHs {d : ℕ} (s : ℝ) (T : Tempered ℂ d) : Prop :=
  ∃ f : Euclidean d → ℂ, HasFourierDensity T f ∧
    MemLp (fun ξ => complexWeight s ξ * f ξ) 2 volume

/-- The exact Bessel operator (I-Δ)^(t/2), using the 2π convention. -/
def besselOperator {d : ℕ} (t : ℝ) (T : Tempered ℂ d) : Tempered ℂ d :=
  TemperedDistribution.fourierMultiplierCLM ℂ (complexWeight t) T

/-- In weighted coordinates a Bessel isometry preserves the coordinate. -/
def besselIsometry (d : ℕ) (s t : ℝ) : Hs d s ≃ₗᵢ[ℂ] Hs d (s - t) :=
  LinearIsometryEquiv.refl ℂ _

/-- The reflected bilinear Fourier pairing: there is no complex conjugation. -/
def dualPairing {d : ℕ} {s : ℝ} (u : Hs d s) (v : Hs d (-s)) : ℂ :=
  ∫ ξ, fourierDensity u ξ * fourierDensity v (-ξ)

/-- The already allocated integer Sobolev graph on all of Euclidean space. -/
abbrev IntegerSobolev (d m : ℕ) :=
  Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue ℂ d ⊤ m 2

end ExpandedFA.Sobolev.FourierScale

namespace Specs.ExpandedFA.Sobolev.FourierHilbertScale
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Sobolev.FourierScale

def spaceType := ∀ (d : ℕ) (s : ℝ), Type
noncomputable def spaceValue : spaceType := Hs

def realizationType := ∀ {d : ℕ} {s : ℝ}, Hs d s → Tempered ℂ d
noncomputable def realizationValue : realizationType := @realization

def hilbertType : Prop := ∀ (d : ℕ) (s : ℝ), CompleteSpace (Hs d s)

def realizationLinearType : Prop := ∀ (d : ℕ) (s : ℝ),
  (∀ u v : Hs d s, realization (u + v) = realization u + realization v) ∧
  (∀ (c : ℂ) (u : Hs d s), realization (c • u) = c • realization u)

def realizationInjectiveType : Prop := ∀ (d : ℕ) (s : ℝ),
  Function.Injective (@realization d s)

def realizationImageType : Prop := ∀ (d : ℕ) (s : ℝ) (T : Tempered ℂ d),
  (∃ u : Hs d s, realization u = T) ↔ MemHs s T

def densityType : Prop := ∀ (d : ℕ) (s : ℝ) (u : Hs d s),
  HasFourierDensity (realization u) (fourierDensity u)

def normType : Prop := ∀ (d : ℕ) (s : ℝ) (u : Hs d s),
  Integrable (fun ξ => frequencyWeight ξ ^ s * ‖fourierDensity u ξ‖ ^ 2) ∧
  ‖u‖ ^ 2 = ∫ ξ, frequencyWeight ξ ^ s * ‖fourierDensity u ξ‖ ^ 2

/-- Actual Schwartz inclusion in the abstract model, identified as a regular
distribution; this also fixes the meaning of extending the classical pairing. -/
def schwartzInclusionType : Prop := ∀ (d : ℕ) (s : ℝ) (f : Schwartz ℂ d),
  ∃ u : Hs d s, realization u = schwartzRegularDistribution f

def dualType : Prop := ∀ (d : ℕ) (s : ℝ),
  ∃ e : Hs d (-s) ≃ₗᵢ[ℂ] (Hs d s →L[ℂ] ℂ),
    ∀ u v, e v u = dualPairing u v

def pairingIntegrableType : Prop := ∀ (d : ℕ) (s : ℝ)
    (u : Hs d s) (v : Hs d (-s)),
  Integrable (fun ξ => fourierDensity u ξ * fourierDensity v (-ξ))

def pairingExtendsType : Prop := ∀ (d : ℕ) (s : ℝ) (f g : Schwartz ℂ d)
    (u : Hs d s) (v : Hs d (-s)),
  realization u = schwartzRegularDistribution f →
  realization v = schwartzRegularDistribution g →
  dualPairing u v = ∫ x, f x * g x

/-- Compatibility with the action of every represented distribution on tests. -/
def pairingTestType : Prop := ∀ (d : ℕ) (s : ℝ) (u : Hs d s)
    (g : Schwartz ℂ d) (v : Hs d (-s)),
  realization v = schwartzRegularDistribution g →
  dualPairing u v = realization u g

def besselType : Prop := ∀ (d : ℕ) (s t : ℝ) (u : Hs d s),
  realization (besselIsometry d s t u) = besselOperator t (realization u)

/-- Equivalent norms and identification of the actual underlying functions as
regular distributions, rather than an arbitrary abstract space isomorphism. -/
def integerType : Prop := ∀ (d m : ℕ),
  ∃ e : Hs d (m : ℝ) ≃L[ℂ] IntegerSobolev d m,
    ∀ (u : Hs d (m : ℝ)) (φ : Schwartz ℂ d),
      realization u φ = ∫ x, φ x *
        ((e u).val (_root_.ExpandedFA.Sobolev.zeroIndex d m)) x

/-- The zero-order case retains the exact L² norm and actual realization. -/
def integerZeroType : Prop := ∀ d : ℕ,
  ∃ e : Hs d 0 ≃ₗᵢ[ℂ] IntegerSobolev d 0,
    ∀ (u : Hs d 0) (φ : Schwartz ℂ d),
      realization u φ = ∫ x, φ x *
        ((e u).val (_root_.ExpandedFA.Sobolev.zeroIndex d 0)) x

def schwartzDenseType : Prop := ∀ (d : ℕ) (s : ℝ),
  Dense {u : Hs d s | ∃ f : Schwartz ℂ d,
    realization u = schwartzRegularDistribution f}

end Specs.ExpandedFA.Sobolev.FourierHilbertScale

noncomputable section
open MeasureTheory
namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

/-- Conjugation on the underlying real Hilbert space L². -/
def realConjugationL2 (d : ℕ) : L2 d →ₗᵢ[ℝ] L2 d where
  toLinearMap := Complex.conjCLE.toContinuousLinearMap.compLpₗ 2 volume
  norm_map' f := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [ContinuousLinearMap.coeFn_compLp Complex.conjCLE.toContinuousLinearMap f] with ξ hξ
    simp [hξ]

/-- Conjugation followed by reflection, a real-linear isometry. -/
def realConjugateReflectionL2 (d : ℕ) : L2 d →ₗᵢ[ℝ] L2 d :=
  (realConjugationL2 d).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (fun ξ : Euclidean d => -ξ)
      (Measure.measurePreserving_neg volume))

/-- Hermitian Fourier coordinates: the real form of complex L². -/
def hermitianL2 (d : ℕ) : Submodule ℝ (L2 d) :=
  ((realConjugateReflectionL2 d).toContinuousLinearMap -
    ContinuousLinearMap.id ℝ (L2 d)).ker

/-- Weighted Fourier coordinates of the real Sobolev scale. -/
def RealHs (d : ℕ) (_s : ℝ) : Type := hermitianL2 d

instance (d : ℕ) (s : ℝ) : NormedAddCommGroup (RealHs d s) :=
  inferInstanceAs (NormedAddCommGroup (hermitianL2 d))
instance (d : ℕ) (s : ℝ) : InnerProductSpace ℝ (RealHs d s) :=
  inferInstanceAs (InnerProductSpace ℝ (hermitianL2 d))
instance (d : ℕ) (s : ℝ) : CompleteSpace (RealHs d s) :=
  (ContinuousLinearMap.isClosed_ker _).completeSpace_coe

/-- The inclusion of real weighted coordinates into complex L². -/
def realCoordinates (d : ℕ) (s : ℝ) : RealHs d s →ₗᵢ[ℝ] L2 d :=
  (hermitianL2 d).subtypeₗᵢ

/-- Bessel operators preserve these weighted Fourier coordinates. -/
def realBesselIsometry (d : ℕ) (s t : ℝ) :
    RealHs d s ≃ₗᵢ[ℝ] RealHs d (s - t) :=
  LinearIsometryEquiv.refl ℝ _

end ExpandedFA.Sobolev.FourierScale

set_option backward.isDefEq.respectTransparency false
namespace ExpandedFA.Sobolev.FourierScale
open ExpandedFA.Fourier

def complexifySchwartz {d : ℕ} : Schwartz ℝ d →L[ℝ] Schwartz ℂ d :=
  SchwartzMap.postcompCLM Complex.ofRealCLM

def reSchwartz {d : ℕ} : Schwartz ℂ d →L[ℝ] Schwartz ℝ d :=
  SchwartzMap.postcompCLM Complex.reCLM

def imSchwartz {d : ℕ} : Schwartz ℂ d →L[ℝ] Schwartz ℝ d :=
  SchwartzMap.postcompCLM Complex.imCLM

lemma reSchwartz_smul {d : ℕ} (c : ℂ) (φ : Schwartz ℂ d) :
    reSchwartz (c • φ) = c.re • reSchwartz φ - c.im • imSchwartz φ := by
  ext x
  simp [reSchwartz, imSchwartz, Complex.mul_re, smul_eq_mul]
lemma imSchwartz_smul {d : ℕ} (c : ℂ) (φ : Schwartz ℂ d) :
    imSchwartz (c • φ) = c.re • imSchwartz φ + c.im • reSchwartz φ := by
  ext x
  simp [reSchwartz, imSchwartz, Complex.mul_im, smul_eq_mul]

def complexifyTempered {d : ℕ} (T : Tempered ℝ d) : Tempered ℂ d where
  toFun φ := (T (reSchwartz φ) : ℂ) + Complex.I * (T (imSchwartz φ) : ℂ)
  map_add' φ ψ := by simp [map_add, mul_add]; ring
  map_smul' c φ := by
    rw [reSchwartz_smul, imSchwartz_smul]
    simp only [map_sub, map_add, map_smul, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul, smul_eq_mul, RingHom.id_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  cont := by
    exact ((Complex.ofRealCLM.comp (T.comp reSchwartz)).continuous).add
      (continuous_const.mul (Complex.ofRealCLM.comp (T.comp imSchwartz)).continuous)

def restrictTempered {d : ℕ} (T : Tempered ℂ d) : Tempered ℝ d :=
  Complex.reCLM.comp ((T.restrictScalars ℝ).comp complexifySchwartz)

@[simp] lemma complexifyTempered_apply_complexifySchwartz {d : ℕ} (T : Tempered ℝ d)
    (φ : Schwartz ℝ d) : complexifyTempered T (complexifySchwartz φ) = (T φ : ℂ) := by
  have hr : reSchwartz (complexifySchwartz φ) = φ := by ext x; simp [reSchwartz, complexifySchwartz]
  have hi : imSchwartz (complexifySchwartz φ) = 0 := by ext x; simp [imSchwartz, complexifySchwartz]
  change (T (reSchwartz (complexifySchwartz φ)) : ℂ) + Complex.I *
    (T (imSchwartz (complexifySchwartz φ)) : ℂ) = _
  rw [hr, hi, map_zero]
  simp

@[simp] lemma restrict_complexifyTempered {d : ℕ} (T : Tempered ℝ d) :
    restrictTempered (complexifyTempered T) = T := by
  ext φ
  change (complexifyTempered T (complexifySchwartz φ)).re = _
  simp

lemma complexifyTempered_injective (d : ℕ) : Function.Injective (@complexifyTempered d) := by
  intro T U h
  have := congrArg restrictTempered h
  simpa using this

def conjSchwartz {d : ℕ} : Schwartz ℂ d →L[ℝ] Schwartz ℂ d :=
  SchwartzMap.postcompCLM (Complex.conjCLE.toContinuousLinearEquiv.restrictScalars ℝ).toContinuousLinearMap


@[simp] lemma conjSchwartz_apply {d : ℕ} (φ : Schwartz ℂ d) (x : Euclidean d) :
    conjSchwartz φ x = star (φ x) := rfl

lemma schwartz_decompose {d : ℕ} (φ : Schwartz ℂ d) :
    φ = complexifySchwartz (reSchwartz φ) +
      Complex.I • complexifySchwartz (imSchwartz φ) := by
  ext x
  apply Complex.ext <;> simp [complexifySchwartz, reSchwartz, imSchwartz, smul_eq_mul]

lemma complexify_restrict_of_real {d : ℕ} (T : Tempered ℂ d)
    (hT : ∀ φ : Schwartz ℝ d, (T (complexifySchwartz φ)).im = 0) :
    complexifyTempered (restrictTempered T) = T := by
  ext φ
  change ((T (complexifySchwartz (reSchwartz φ))).re : ℂ) +
    Complex.I * ((T (complexifySchwartz (imSchwartz φ))).re : ℂ) = T φ
  have hre (ψ : Schwartz ℝ d) : ((T (complexifySchwartz ψ)).re : ℂ) =
      T (complexifySchwartz ψ) := by
    exact Complex.ext (by simp) (by simp [hT ψ])
  rw [hre, hre]
  conv_rhs => rw [schwartz_decompose φ, map_add, map_smul]
  rfl

def realSchwartzRegularDistribution {d : ℕ} (f : Schwartz ℝ d) : Tempered ℝ d :=
  (SchwartzMap.integralCLM ℝ (volume : Measure (Euclidean d))).comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f)

def realRealization {d : ℕ} {s : ℝ} (u : RealHs d s) : Tempered ℝ d :=
  restrictTempered (@realization d s (realCoordinates d s u))

def realFourierDensity {d : ℕ} {s : ℝ} (u : RealHs d s) : Euclidean d → ℂ :=
  @fourierDensity d s (realCoordinates d s u)

/-- The real distribution pairing, obtained from the Hermitian Fourier form. -/
def realDualPairing {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)) : ℝ :=
  (@dualPairing d s (realCoordinates d s u) (realCoordinates d (-s) v)).re


/-- Real tempered distributions belong to H^s precisely when their canonical
complexification has the manuscript's weighted Fourier density. -/
def realMemHs {d : ℕ} (s : ℝ) (T : Tempered ℝ d) : Prop :=
  MemHs s (complexifyTempered T)

/-- The real Bessel operator is the restriction of its Fourier multiplier
on the canonical complexification. Its compatibility is proved below. -/
def realBesselOperator {d : ℕ} (t : ℝ) (T : Tempered ℝ d) : Tempered ℝ d :=
  restrictTempered (besselOperator t (complexifyTempered T))

abbrev RealIntegerSobolev (d m : ℕ) :=
  Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue ℝ d ⊤ m 2

end ExpandedFA.Sobolev.FourierScale

namespace Specs.ExpandedFA.Sobolev.FourierHilbertScale
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Sobolev.FourierScale

/-- The real scale uses the Hermitian subspace, rather than the underlying
real vector space of all complex distributions. -/
def realSpaceType := ∀ (d : ℕ) (s : ℝ), Type
def realSpaceValue : realSpaceType := RealHs

def realRealizationType := ∀ {d : ℕ} {s : ℝ}, RealHs d s → Tempered ℝ d
def realRealizationValue : realRealizationType := @realRealization

def realHilbertType : Prop := ∀ (d : ℕ) (s : ℝ), CompleteSpace (RealHs d s)

def realRealizationLinearType : Prop := ∀ (d : ℕ) (s : ℝ),
  (∀ u v : RealHs d s, realRealization (u + v) = realRealization u + realRealization v) ∧
  (∀ (c : ℝ) (u : RealHs d s), realRealization (c • u) = c • realRealization u)

def realRealizationInjectiveType : Prop := ∀ (d : ℕ) (s : ℝ),
  Function.Injective (@realRealization d s)

/-- This is the unbundled real distribution definition, with Fourier transform
taken after the canonical complexification of a real scalar-linear functional. -/
def realRealizationImageType : Prop := ∀ (d : ℕ) (s : ℝ) (T : Tempered ℝ d),
  (∃ u : RealHs d s, realRealization u = T) ↔ realMemHs s T

/-- The inclusion into the complex scale is the actual complexification. -/
def realComplexificationType : Prop := ∀ {d : ℕ} {s : ℝ} (u : RealHs d s),
  complexifyTempered (realRealization u) = @realization d s (realCoordinates d s u)

/-- Hermitian Fourier coordinates are equivalent to physical real-valuedness. -/
def realFormIdentificationType : Prop := ∀ {d : ℕ} {s : ℝ} (u : Hs d s),
  u ∈ hermitianL2 d ↔
    ∀ φ : Schwartz ℝ d, (realization u (complexifySchwartz φ)).im = 0

def realDensityType : Prop := ∀ {d : ℕ} {s : ℝ} (u : RealHs d s),
  HasFourierDensity (complexifyTempered (realRealization u)) (realFourierDensity u)

def realFourierSymmetryType : Prop := ∀ {d : ℕ} {s : ℝ} (u : RealHs d s),
  ∀ᵐ ξ ∂volume, realFourierDensity u (-ξ) = star (realFourierDensity u ξ)

def realNormType : Prop := ∀ {d : ℕ} {s : ℝ} (u : RealHs d s),
  Integrable (fun ξ => frequencyWeight ξ ^ s * ‖realFourierDensity u ξ‖ ^ 2) ∧
  ‖u‖ ^ 2 = ∫ ξ, frequencyWeight ξ ^ s * ‖realFourierDensity u ξ‖ ^ 2

def realSchwartzInclusionType : Prop := ∀ (d : ℕ) (s : ℝ) (f : Schwartz ℝ d),
  ∃ u : RealHs d s, realRealization u = realSchwartzRegularDistribution f

def realSchwartzDenseType : Prop := ∀ (d : ℕ) (s : ℝ),
  Dense {u : RealHs d s | ∃ f : Schwartz ℝ d,
    realRealization u = realSchwartzRegularDistribution f}

def realDualType : Prop := ∀ (d : ℕ) (s : ℝ),
  ∃ e : RealHs d (-s) ≃ₗᵢ[ℝ] (RealHs d s →L[ℝ] ℝ),
    ∀ u v, e v u = realDualPairing u v

/-- The real pairing is exactly the same bilinear Fourier integral: taking its
real part in the definition does not discard an imaginary component. -/
def realPairingRealityType : Prop := ∀ {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)),
  (realDualPairing u v : ℂ) =
    ∫ ξ, realFourierDensity u ξ * realFourierDensity v (-ξ)

def realPairingIntegrableType : Prop := ∀ {d : ℕ} {s : ℝ}
    (u : RealHs d s) (v : RealHs d (-s)),
  Integrable (fun ξ => realFourierDensity u ξ * realFourierDensity v (-ξ))

def realPairingTestType : Prop := ∀ {d : ℕ} {s : ℝ} (u : RealHs d s)
    (g : Schwartz ℝ d) (v : RealHs d (-s)),
  realRealization v = realSchwartzRegularDistribution g →
  realDualPairing u v = realRealization u g

def realPairingExtendsType : Prop := ∀ {d : ℕ} {s : ℝ} (f g : Schwartz ℝ d)
    (u : RealHs d s) (v : RealHs d (-s)),
  realRealization u = realSchwartzRegularDistribution f →
  realRealization v = realSchwartzRegularDistribution g →
  realDualPairing u v = ∫ x, f x * g x

def realBesselType : Prop := ∀ {d : ℕ} {s : ℝ} (t : ℝ) (u : RealHs d s),
  realRealization (realBesselIsometry d s t u) = realBesselOperator t (realRealization u)

/-- The isometric Bessel map is the original Fourier multiplier on the actual
complexification of a real distribution. -/
def realBesselComplexificationType : Prop := ∀ {d : ℕ} (s t : ℝ) (u : RealHs d s),
  complexifyTempered (realBesselOperator t (realRealization u)) =
    besselOperator t (complexifyTempered (realRealization u))

def realIntegerType : Prop := ∀ (d m : ℕ),
  ∃ e : RealHs d (m : ℝ) ≃L[ℝ] RealIntegerSobolev d m,
    ∀ (u : RealHs d (m : ℝ)) (φ : Schwartz ℝ d),
      realRealization u φ = ∫ x, φ x *
        ((e u).val (_root_.ExpandedFA.Sobolev.zeroIndex d m)) x

end Specs.ExpandedFA.Sobolev.FourierHilbertScale
