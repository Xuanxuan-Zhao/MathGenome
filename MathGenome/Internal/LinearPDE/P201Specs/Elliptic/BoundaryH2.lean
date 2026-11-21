import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.InteriorH2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatTrace
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.BiLipschitzPullback

/-! Boundary H², paper.tex:1586–1647. These independent specifications expose
the local physical boundary estimate and the Sobolev coordinate bridge for
global patching, together with the supporting difference and product rules.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped InnerProductSpace NNReal ENNReal ContDiff
namespace P201Specs.BoundaryH2

/-- The actual physical intersection with an ambient ball. Its closure need
not lie in Ω: this is a boundary neighborhood. -/
def neighborhood {n : ℕ} (Ω : Domain n) (p : Space n) (r : ℝ) : Domain n :=
  ⟨(Ω : Set (Space n)) ∩ ball p r, Ω.isOpen.inter isOpen_ball⟩

/-- Matrix symmetry in the Euclidean inner product. -/
def SymmetricOn {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) : Prop :=
  ∀ x ∈ Ω, ∀ ξ ζ : Space n, inner ℝ (A x ξ) ζ = inner ℝ ξ (A x ζ)

/-- Local full-norm boundary estimate, with the constant chosen before the
coefficient and solution. The outer H¹ and L² classes are genuine restrictions,
not assumed extension or regularity certificates. Dimension is m+1, so m=0
includes the one-dimensional endpoint case. -/
def localBoundaryEstimateStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasC11Boundary Ω →
    ∀ p ∈ frontier (Ω : Set (Space (m + 1))),
    ∀ (M L : ℝ≥0) (theta : ℝ), 0 < theta →
    ∃ (R r C : ℝ), 0 < r ∧ r < R ∧ 0 < C ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      InteriorH2.CoefficientBounds Ω A M L theta → SymmetricOn Ω A →
      ∀ (u : H10 ℝ Ω) (f : Lp ℝ Ω 2),
      InteriorH2.WeakEquation Ω A u.val f →
      ∃ (v : H ℝ (neighborhood Ω p R) 1)
        (g : Lp ℝ (neighborhood Ω p R) 2)
        (w : H ℝ (neighborhood Ω p r) 2),
        (hUnderlying (neighborhood Ω p R) 1 v : Space (m + 1) → ℝ)
          =ᵐ[domainMeasure (neighborhood Ω p R)] hZeroUnderlying Ω u ∧
        (g : Space (m + 1) → ℝ) =ᵐ[domainMeasure (neighborhood Ω p R)] f ∧
        (hUnderlying (neighborhood Ω p r) 2 w : Space (m + 1) → ℝ)
          =ᵐ[domainMeasure (neighborhood Ω p r)] hZeroUnderlying Ω u ∧
        ‖w‖ ≤ C * (‖v‖ + ‖g‖)

/-- If J is the inverse differential of a flattening, this is precisely
J A Jᵀ. The adjoint is with respect to the Euclidean inner product. -/
def conjugateCoefficient {n : ℕ} (J A : Space n →L[ℝ] Space n) :
    Space n →L[ℝ] Space n :=
  J.comp (A.comp (ContinuousLinearMap.adjoint J))

abbrev conjugateCoefficientType := {n : ℕ} →
  (Space n →L[ℝ] Space n) → (Space n →L[ℝ] Space n) →
    (Space n →L[ℝ] Space n)

def conjugatePairingStatement : Prop :=
  ∀ {n : ℕ} (J A : Space n →L[ℝ] Space n) (ξ ζ : Space n),
    inner ℝ (conjugateCoefficient J A ξ) ζ =
      inner ℝ (A (ContinuousLinearMap.adjoint J ξ))
        (ContinuousLinearMap.adjoint J ζ)

def conjugateNormStatement : Prop :=
  ∀ {n : ℕ} (J A : Space n →L[ℝ] Space n),
    ‖conjugateCoefficient J A‖ ≤ ‖J‖ ^ 2 * ‖A‖

def conjugateSymmetryStatement : Prop :=
  ∀ {n : ℕ} (J A : Space n →L[ℝ] Space n),
    (∀ ξ ζ : Space n, inner ℝ (A ξ) ζ = inner ℝ ξ (A ζ)) →
    ∀ ξ ζ : Space n, inner ℝ (conjugateCoefficient J A ξ) ζ =
      inner ℝ ξ (conjugateCoefficient J A ζ)

def inverseAdjointBoundStatement : Prop :=
  ∀ {n : ℕ} (J E : Space n →L[ℝ] Space n),
    J.comp E = ContinuousLinearMap.id ℝ (Space n) →
    ∀ ξ : Space n, ‖ξ‖ ≤ ‖E‖ * ‖ContinuousLinearMap.adjoint J ξ‖

/-- Algebraic difference bound used to control the Lipschitz norm of B. -/
def conjugateDifferenceStatement : Prop :=
  ∀ {n : ℕ} (J K A D : Space n →L[ℝ] Space n) (N M : ℝ),
    0 ≤ N → 0 ≤ M → ‖J‖ ≤ N → ‖K‖ ≤ N → ‖A‖ ≤ M → ‖D‖ ≤ M →
    ‖conjugateCoefficient J A - conjugateCoefficient K D‖ ≤
      2 * N * M * ‖J - K‖ + N ^ 2 * ‖A - D‖

/-- The inverse-differential and original-coefficient Lipschitz estimates are
separate inputs. Composition with F is handled by multiplying constants. -/
def conjugateLipschitzStatement : Prop :=
  ∀ {n : ℕ} (S : Set (Space n))
    (J A : Space n → Space n →L[ℝ] Space n) (N M LJ LA : ℝ≥0),
    (∀ x ∈ S, ‖J x‖ ≤ N) → (∀ x ∈ S, ‖A x‖ ≤ M) →
    LipschitzOnWith LJ J S → LipschitzOnWith LA A S →
    LipschitzOnWith (2 * N * M * LJ + N ^ 2 * LA)
      (fun x => conjugateCoefficient (J x) (A x)) S

/-- Quantitative congruence of ellipticity. The inverse-differential lower
bound here is algebraic input to this helper, not an extra hypothesis in the
local boundary theorem. A coordinate bridge must establish it for actual DF. -/
def conjugateEllipticityStatement : Prop :=
  ∀ {n : ℕ} (J A : Space n →L[ℝ] Space n) (theta K : ℝ),
    0 < theta → 0 < K →
    (∀ ξ : Space n, theta * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) →
    (∀ ξ : Space n, ‖ξ‖ ≤ K * ‖ContinuousLinearMap.adjoint J ξ‖) →
    ∀ ξ : Space n, theta / K ^ 2 * ‖ξ‖ ^ 2 ≤
      inner ℝ (conjugateCoefficient J A ξ) ξ

/-- The remaining normal entry is positive, including in dimension one. -/
def normalCoefficientStatement : Prop :=
  ∀ {m : ℕ} (B : Space (m + 1) →L[ℝ] Space (m + 1)) (theta : ℝ),
    (∀ ξ : Space (m + 1), theta * ‖ξ‖ ^ 2 ≤ inner ℝ (B ξ) ξ) →
    theta ≤ inner ℝ (B (coordinate (m + 1) (Fin.last m)))
      (coordinate (m + 1) (Fin.last m))

/-- Reconstruction on an arbitrary smaller open set, which may reach the
boundary. Unlike the quotient converse, this interface requires no relative
compactness in the larger open set. All supplied derivatives are actual
distributional identities. -/
def h2RestrictionStatement : Prop :=
  ∀ {n : ℕ} (V U : Domain n), U ≤ V →
    ∀ (v : H ℝ V 1) (g : Fin n → Fin n → Lp ℝ U 2) (B : ℝ),
    0 ≤ B →
    (∀ j k, distributionDerivative {k} (regularDistribution U (hFirstDerivative v j)) =
      regularDistribution U (g j k)) →
    (∀ j k, ‖g j k‖ ≤ B) →
    ∃ w : H ℝ U 2,
      (hUnderlying U 2 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex n 2) : ℝ) * (‖v‖ + B)

/-- Directional weak product rule. Only the displayed products need be locally
integrable; neither factor nor its derivative is required to be bounded. -/
def directionalProductStatement : Prop :=
  ∀ {n : ℕ} (U : Domain n) (j : Fin n) (a da u du : Space n → ℝ),
    LocallyIntegrableOn a U volume → LocallyIntegrableOn da U volume →
    LocallyIntegrableOn u U volume → LocallyIntegrableOn du U volume →
    distributionDerivative {j} (regularDistribution U a) = regularDistribution U da →
    distributionDerivative {j} (regularDistribution U u) = regularDistribution U du →
    LocallyIntegrableOn (fun x => a x * u x) U volume →
    LocallyIntegrableOn (fun x => a x * du x + da x * u x) U volume →
    distributionDerivative {j} (regularDistribution U (fun x => a x * u x)) =
      regularDistribution U (fun x => a x * du x + da x * u x)

/-- Normal recovery in any one coordinate direction. This is applied with
`b = B_nn`, `v = ∂n w`, and the L² right-hand side after the tangential terms
have been removed. It applies also in dimension one and requires no other
weak derivative of v, no boundary smoothness, and no trace assumption. -/
def normalRecoveryStatement : Prop :=
  ∀ {n : ℕ} (U : Domain n) (j : Fin n) (b : Space n → ℝ)
    (M L : ℝ≥0) (theta : ℝ), 0 < theta →
    LipschitzOnWith L b U → (∀ x ∈ U, theta ≤ b x) →
    (∀ x ∈ U, |b x| ≤ M) →
    ∀ v R : Lp ℝ U 2,
    distributionDerivative {j} (regularDistribution U (fun x => b x * v x)) =
      regularDistribution U R →
    ∃ d : Lp ℝ U 2,
      distributionDerivative {j} (regularDistribution U v) = regularDistribution U d ∧
      (d : Space n → ℝ) =ᵐ[domainMeasure U]
        (fun x => (R x - fderiv ℝ b x (coordinate n j) * v x) / b x) ∧
      ‖d‖ ≤ theta⁻¹ * (‖R‖ + (L : ℝ) * ‖v‖)

/-- In dimension one there are no tangential terms. The weak equation itself
therefore yields the complete H² estimate on the open domain. No boundary
condition is needed for this stronger one-dimensional assertion. -/
def dimensionOneEstimateStatement : Prop :=
  ∀ (U : Domain 1) (M L : ℝ≥0) (theta : ℝ), 0 < theta →
    ∃ C : ℝ, 0 < C ∧
    ∀ A : Space 1 → Space 1 →L[ℝ] Space 1,
    InteriorH2.CoefficientBounds U A M L theta →
    ∀ (v : H ℝ U 1) (f : Lp ℝ U 2), InteriorH2.WeakEquation U A v f →
    ∃ w : H ℝ U 2, hUnderlying U 2 w = hUnderlying U 1 v ∧
      ‖w‖ ≤ C * (‖v‖ + ‖f‖)

/-- A bounded Lipschitz multiplier preserves a single L² weak derivative,
with explicit representatives and norm bounds. The differentiated L² function
is not required to be essentially bounded. -/
def directionalLipschitzMultiplierStatement : Prop :=
  ∀ {n : ℕ} (U : Domain n) (j : Fin n) (a : Space n → ℝ) (M L : ℝ≥0),
    LipschitzOnWith L a U → (∀ x ∈ U, |a x| ≤ M) →
    ∀ v dv : Lp ℝ U 2,
    distributionDerivative {j} (regularDistribution U v) = regularDistribution U dv →
    ∃ w d : Lp ℝ U 2,
      (w : Space n → ℝ) =ᵐ[domainMeasure U] (fun x => a x * v x) ∧
      (d : Space n → ℝ) =ᵐ[domainMeasure U]
        (fun x => a x * dv x + fderiv ℝ a x (coordinate n j) * v x) ∧
      distributionDerivative {j} (regularDistribution U w) = regularDistribution U d ∧
      ‖w‖ ≤ (M : ℝ) * ‖v‖ ∧ ‖d‖ ≤ (M : ℝ) * ‖dv‖ + (L : ℝ) * ‖v‖

/-- The actual H¹ coordinate pullback and weak chain rule in the common full
Hilbert norms. A chart contains only inverse maps and geometric Lipschitz
bounds; Sobolev regularity is a conclusion here. -/
def coordinateH1PullbackStatement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (U V : Domain n) (L M : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V L M),
    ∃ T : H ℝ U 1 →L[ℝ] H ℝ V 1,
      (∀ u, (hUnderlying V 1 (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => hUnderlying U 1 u (F.toFun x))) ∧
      (∀ u j, (hFirstDerivative (T u) j : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => ∑ i : Fin n,
          fderiv ℝ F.toFun x (coordinate n j) i *
            hFirstDerivative u i (F.toFun x))) ∧
      ‖T‖ ≤ (Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) *
        P102.U4.pullbackSobolevBound n 2 L M

/-- H² transport under a geometric bi-Lipschitz chart with Lipschitz actual
first differential. The estimate holds in the full Hilbert norm, and its
constant is chosen before the Sobolev function. Applying the same statement
to the inverse chart gives transport in the other direction. -/
def coordinateH2PullbackStatement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (U V : Domain n) (L M Hder : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V L M),
    LipschitzOnWith Hder (fderiv ℝ F.toFun) V →
    ∃ C : ℝ, 0 < C ∧ ∀ u : H ℝ U 2,
      ∃ w : H ℝ V 2,
        (hUnderlying V 2 w : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => hUnderlying U 2 u (F.toFun x)) ∧ ‖w‖ ≤ C * ‖u‖

/-- H¹ restriction without compact containment, in the full Hilbert norm. -/
def h1RestrictionStatement : Prop :=
  ∀ {n : ℕ} (V U : Domain n), U ≤ V → ∀ v : H ℝ V 1,
    ∃ w : H ℝ U 1,
      (hUnderlying U 1 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
      (∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure U]
        hFirstDerivative v j) ∧ ‖w‖ ≤ (1 + (n : ℝ)) * ‖v‖

/-- Weak equations restrict to all smaller open sets, including boundary
neighborhoods, using the actual weak derivatives of the restricted class. -/
def weakEquationRestrictionStatement : Prop :=
  ∀ {n : ℕ} (V U : Domain n), U ≤ V →
    ∀ (A : Space n → Space n →L[ℝ] Space n) (v : H ℝ V 1) (w : H ℝ U 1)
      (f g : Space n → ℝ),
    (∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure U]
      hFirstDerivative v j) →
    g =ᵐ[domainMeasure U] f → InteriorH2.WeakEquation V A v f →
    InteriorH2.WeakEquation U A w g

/-- Complete local boundary conclusion in dimension one. In this dimension
the assertion holds on every open set, with no geometry assumption. -/
def localBoundaryEstimateOneStatement : Prop :=
  ∀ (Ω : Domain 1) (p : Space 1) (M L : ℝ≥0) (theta : ℝ), 0 < theta →
    ∃ (R r C : ℝ), 0 < r ∧ r < R ∧ 0 < C ∧
      ∀ A : Space 1 → Space 1 →L[ℝ] Space 1,
      InteriorH2.CoefficientBounds Ω A M L theta →
      ∀ (u : H10 ℝ Ω) (f : Lp ℝ Ω 2),
      InteriorH2.WeakEquation Ω A u.val f →
      ∃ (v : H ℝ (neighborhood Ω p R) 1)
        (g : Lp ℝ (neighborhood Ω p R) 2)
        (w : H ℝ (neighborhood Ω p r) 2),
        (hUnderlying (neighborhood Ω p R) 1 v : Space 1 → ℝ)
          =ᵐ[domainMeasure (neighborhood Ω p R)] hZeroUnderlying Ω u ∧
        (g : Space 1 → ℝ) =ᵐ[domainMeasure (neighborhood Ω p R)] f ∧
        (hUnderlying (neighborhood Ω p r) 2 w : Space 1 → ℝ)
          =ᵐ[domainMeasure (neighborhood Ω p r)] hZeroUnderlying Ω u ∧
        ‖w‖ ≤ C * (‖v‖ + ‖g‖)

/-- Uniform quotients on any smaller open set determine its L² derivative.
There is no compact-containment requirement on that open set. -/
def derivativeFromBoundaryQuotientsStatement : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (U V : Domain n), U ≤ V →
    ∀ (u : Lp ℝ V 2) (j : Fin n) (B : ℝ≥0),
    (∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
      MemLp (differenceQuotient u j h) 2 (domainMeasure U) ∧
      eLpNorm (differenceQuotient u j h) 2 (domainMeasure U) ≤ B) →
    ∃ d : Lp ℝ U 2,
      distributionDerivative {j} (regularDistribution U u) =
        regularDistribution U d ∧ ‖d‖ ≤ B

/-- Vanishing of a whole-space H¹ representative below a flat face gives
membership in the actual H¹₀ closure on the upper half-space. -/
def zeroBelowMemHZeroStatement : Prop :=
  ∀ {m : ℕ} (z : H ℝ (⊤ : Domain (m + 1)) 1),
    (∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0) →
    ∀ v : H ℝ (P102.Trace.halfSpace m) 1,
    (hUnderlying (P102.Trace.halfSpace m) 1 v : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure (P102.Trace.halfSpace m)] hUnderlying ⊤ 1 z →
    v ∈ hZeroSubmodule ℝ (P102.Trace.halfSpace m)

/-- Actual H¹₀ tests obtained from tangential differences of a zero extension. -/
def tangentialQuotientTestStatement : Prop :=
  ∀ {m : ℕ} (z : H ℝ (⊤ : Domain (m + 1)) 1),
    (∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0) →
    ∀ k : Fin (m + 1), k ≠ Fin.last m → ∀ h : ℝ,
    ∃ t : H10 ℝ (P102.Trace.halfSpace m),
      (hZeroUnderlying (P102.Trace.halfSpace m) t : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)]
          differenceQuotient (hUnderlying ⊤ 1 z) k h ∧
      ∀ j, (hFirstDerivative t.val j : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)]
          differenceQuotient (hFirstDerivative z j) k h

/-- Discrete energy identity for a weak equation on the entire half-space. -/
def halfSpaceDiscreteEnergyStatement : Prop :=
  ∀ {m : ℕ}
    (F : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure (P102.Trace.halfSpace m)))
    (f : Lp ℝ (P102.Trace.halfSpace m) 2),
    (∀ φ : Test ℝ (P102.Trace.halfSpace m),
      (∫ x in P102.Trace.halfSpace m, inner ℝ (F x) (gradient φ x)) =
        ∫ x in P102.Trace.halfSpace m, f x * φ x) →
    ∀ z : H ℝ (⊤ : Domain (m + 1)) 1,
    (∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0) →
    ∀ k : Fin (m + 1), k ≠ Fin.last m → ∀ h : ℝ, h ≠ 0 →
    (∑ j : Fin (m + 1), ∫ x,
      differenceQuotient (P102.U4.lpZeroExtension (P102.Trace.halfSpace m) 2
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) j).compLp F)) k h x *
          hFirstDerivative z j x) =
      -(∫ x in P102.Trace.halfSpace m,
        f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x)

/-- The normal recovery/reconstruction stage after the tangential derivatives
have been obtained. This is a supporting implication, not a certificate assumed
by the original local boundary estimate. No relative compactness, boundary
smoothness, symmetry or trace is required for this stage alone. -/
def normalAssemblyStatement : Prop :=
  ∀ {m : ℕ} (U : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (M L : ℝ≥0) (theta : ℝ) (htheta : 0 < theta)
    (hA : P201Specs.InteriorH2.CoefficientBounds U A M L theta)
    (v : H ℝ U 1) (f : Lp ℝ U 2)
    (heq : P201Specs.InteriorH2.WeakEquation U A v f)
    (g : Fin (m + 1) → Fin (m + 1) → Lp ℝ U 2) (K : ℝ) (hK : 0 ≤ K)
    (hg : ∀ j i, (i, j) ≠ (Fin.last m, Fin.last m) →
      distributionDerivative {i} (regularDistribution U (hFirstDerivative v j)) =
        regularDistribution U (g j i))
    (hgB : ∀ j i, (i, j) ≠ (Fin.last m, Fin.last m) → ‖g j i‖ ≤ K),
    ∃ w : H ℝ U 2, hUnderlying U 2 w = hUnderlying U 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex (m + 1) 2) : ℝ) *
        (‖v‖ + K + theta⁻¹ * (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
          ((M : ℝ) * K + (L : ℝ) * ‖v‖) + (L : ℝ) * ‖v‖))

/-- Tangential derivatives, followed by distribution commutation and the weak
normal equation, give the full H² bound. These are supporting implications;
the original boundary theorem must still establish their tangential inputs. -/
def h2FromTangentialDerivativesStatement : Prop :=
  ∀ {m : ℕ} (U : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (M L : ℝ≥0) (theta : ℝ) (htheta : 0 < theta)
    (hA : P201Specs.InteriorH2.CoefficientBounds U A M L theta)
    (v : H ℝ U 1) (f : Lp ℝ U 2)
    (heq : P201Specs.InteriorH2.WeakEquation U A v f)
    (g : Fin (m + 1) → Fin (m + 1) → Lp ℝ U 2) (B : ℝ≥0)
    (hg : ∀ j k, k ≠ Fin.last m →
      distributionDerivative {k} (regularDistribution U (hFirstDerivative v j)) =
        regularDistribution U (g j k))
    (hgB : ∀ j k, k ≠ Fin.last m → ‖g j k‖ ≤ B),
    ∃ w : H ℝ U 2, hUnderlying U 2 w = hUnderlying U 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex (m + 1) 2) : ℝ) *
        (‖v‖ + B + theta⁻¹ * (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
          ((M : ℝ) * B + (L : ℝ) * ‖v‖) + (L : ℝ) * ‖v‖))

/-- H² reconstruction from common tangential quotient bounds on an arbitrary
open restriction, without relative compactness. The original H¹/L² data and
weak equation live on V; the conclusion and all quotient bounds live on U. -/
def h2FromTangentialQuotientsStatement : Prop :=
  ∀ {m : ℕ} (U V : Domain (m + 1)) (hUV : U ≤ V)
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (M L : ℝ≥0) (theta : ℝ) (htheta : 0 < theta)
    (hA : P201Specs.InteriorH2.CoefficientBounds V A M L theta)
    (v : H ℝ V 1) (f : Lp ℝ V 2)
    (heq : P201Specs.InteriorH2.WeakEquation V A v f) (B : ℝ≥0)
    (hb : ∀ j k : Fin (m + 1), k ≠ Fin.last m →
      ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
        MemLp (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ∧
        eLpNorm (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ≤ B),
    ∃ w : H ℝ U 2,
      (hUnderlying U 2 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex (m + 1) 2) : ℝ) *
        ((1 + ((m + 1 : ℕ) : ℝ)) * ‖v‖ + B + theta⁻¹ *
          (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 * ((M : ℝ) * B +
            (L : ℝ) * ((1 + ((m + 1 : ℕ) : ℝ)) * ‖v‖)) +
            (L : ℝ) * ((1 + ((m + 1 : ℕ) : ℝ)) * ‖v‖)))

/-- The actual inverse differential produces the transformed bounded,
Lipschitz and elliptic coefficient field with explicit constants. -/
def coordinateCoefficientBoundsStatement : Prop :=
  ∀ {n : ℕ} (U V : Domain n) (LF LG HG : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V LF LG),
    DifferentiableOn ℝ F.toFun V → DifferentiableOn ℝ F.invFun U →
    LipschitzOnWith HG (fderiv ℝ F.invFun) U →
    ∀ (A : Space n → Space n →L[ℝ] Space n) (M LA : ℝ≥0) (theta : ℝ),
    0 < theta → InteriorH2.CoefficientBounds U A M LA theta →
    InteriorH2.CoefficientBounds V
      (fun y => conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y)))
      (LG ^ 2 * M) (2 * LG * M * (HG * LF) + LG ^ 2 * (LA * LF))
      (theta / (max 1 (LF : ℝ)) ^ 2)


def flatLocalized_mem_hZeroStatement : Prop :=
  ∀ {m : ℕ} (U : Domain (m + 1))
    (χ : Test ℝ (⊤ : Domain (m + 1)))
    (hχU : tsupport χ ∩ (P102.Trace.halfSpace m : Set (Space (m + 1))) ⊆ U)
    (z : H ℝ (⊤ : Domain (m + 1)) 1)
    (hz : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (v : H ℝ U 1)
    (hv : (hUnderlying U 1 v : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
      (fun x => χ x * hUnderlying ⊤ 1 z x)),
    v ∈ P201Specs.hZeroSubmodule ℝ U

def localTangentialQuotientTestStatement : Prop :=
  ∀ {m : ℕ} (W U : Domain (m + 1))
    (hWU : (W : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ U)
    (z : H ℝ (⊤ : Domain (m + 1)) 1) (K : Compacts (Space (m + 1)))
    (hKW : (K : Set (Space (m + 1))) ⊆ W)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (hz : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ)
    (ha : ∀ x ∈ K, x - h • coordinate (m + 1) k ∈ W),
    ∃ t : H10 ℝ U,
      (hZeroUnderlying U t : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
        differenceQuotient (hUnderlying ⊤ 1 z) k h ∧
      ∀ j, (hFirstDerivative t.val j : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
        differenceQuotient (hFirstDerivative z j) k h

def localBoundary_discrete_energy_identityStatement : Prop :=
  ∀ {m : ℕ}
    (W V : Domain (m + 1))
    (hWV : (W : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (F : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure V))
    (f : Lp ℝ V 2)
    (heq : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x)
    (z : H ℝ (⊤ : Domain (m + 1)) 1) (K : Compacts (Space (m + 1)))
    (hKW : (K : Set (Space (m + 1))) ⊆ W)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (hzbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ K, x + h • coordinate (m + 1) k ∈ W),
    (∑ j : Fin (m + 1), ∫ x,
      differenceQuotient (P102.U4.lpZeroExtension V 2
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m + 1) => ℝ) j).compLp F)) k h x * hFirstDerivative z j x) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x)


end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

def physicalGraphH2TransportStatement : Prop :=
  ∀ {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] P201Specs.Space (m+1)) (Ω : P201Specs.Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (Hder : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius)),
    ∃ (Cpull Cpush : ℝ), 0 < Cpull ∧ 0 < Cpush ∧
      (∀ u : P201Specs.H ℝ (physicalChartOpen e Ω C) 2,
        ∃ w : P201Specs.H ℝ (flatChartOpen q C.center C.radius C.height) 2,
          (P201Specs.hUnderlying _ 2 w : P201Specs.Space (m+1) → ℝ) =ᵐ[P201Specs.domainMeasure (flatChartOpen q C.center C.radius C.height)]
            (fun x => P201Specs.hUnderlying _ 2 u ((physicalChartMap e q Ω C).toFun x)) ∧
          ‖w‖ ≤ Cpull * ‖u‖) ∧
      (∀ w : P201Specs.H ℝ (flatChartOpen q C.center C.radius C.height) 2,
        ∃ u : P201Specs.H ℝ (physicalChartOpen e Ω C) 2,
          (P201Specs.hUnderlying _ 2 u : P201Specs.Space (m+1) → ℝ) =ᵐ[P201Specs.domainMeasure (physicalChartOpen e Ω C)]
            (fun x => P201Specs.hUnderlying _ 2 w ((physicalChartMap e q Ω C).invFun x)) ∧
          ‖u‖ ≤ Cpush * ‖w‖) 

end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

def flattenH10SupportedStatement : Prop :=
  ∀ {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] P201Specs.Space (m+1)) (Ω : P201Specs.Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (K : Compacts (P201Specs.Space (m+1))) (hK : (K : Set (P201Specs.Space (m+1))) ⊆ fullPhysicalChartOpen e C),
    ∃ Cflat : ℝ, 0 < Cflat ∧
      ∀ u : P201Specs.H10 ℝ Ω,
      (∀ᵐ x ∂P201Specs.domainMeasure Ω, x ∉ K → P201Specs.hZeroUnderlying Ω u x = 0) →
      ∃ w : P201Specs.H10 ℝ (P102.Trace.halfSpace m),
        P102.Trace.FlatZeroTraceExpected.HasFlatZeroExtension
          (P201Specs.hToW ℝ (P102.Trace.halfSpace m) 1 w.val) ∧
        (P201Specs.hZeroUnderlying (P102.Trace.halfSpace m) w : P201Specs.Space (m+1) → ℝ)
          =ᵐ[P201Specs.domainMeasure (flatChartOpen (flatCoordinates m) C.center C.radius C.height)]
          (fun x => P201Specs.hZeroUnderlying Ω u ((physicalChartMap e (flatCoordinates m) Ω C).toFun x)) ∧
        (∀ᵐ x ∂P201Specs.domainMeasure (P102.Trace.halfSpace m),
          x ∉ fullChartPullbackCompact e (flatCoordinates m) C K hK →
            P201Specs.hZeroUnderlying (P102.Trace.halfSpace m) w x = 0) ∧
        ‖w‖ ≤ Cflat * ‖u‖

def physicalGraphCoefficientBoundsStatement : Prop :=
  ∀ {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (Hder : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius))
    (M LA : ℝ≥0) (theta : ℝ) (htheta : 0 < theta),
    ∃ (M' L' : ℝ≥0) (theta' : ℝ), 0 < theta' ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      P201Specs.InteriorH2.CoefficientBounds (physicalChartOpen e Ω C) A M LA theta →
      P201Specs.InteriorH2.CoefficientBounds (flatChartOpen q C.center C.radius C.height)
        (fun y => conjugateCoefficient
          (fderiv ℝ (physicalChartMap e q Ω C).invFun ((physicalChartMap e q Ω C).toFun y))
          (A ((physicalChartMap e q Ω C).toFun y))) M' L' theta' ∧
      (P201Specs.BoundaryH2.SymmetricOn (physicalChartOpen e Ω C) A →
        P201Specs.BoundaryH2.SymmetricOn (flatChartOpen q C.center C.radius C.height)
          (fun y => conjugateCoefficient
            (fderiv ℝ (physicalChartMap e q Ω C).invFun ((physicalChartMap e q Ω C).toFun y))
            (A ((physicalChartMap e q Ω C).toFun y)))) 

/-- Independent statement of the derived coordinate/volume bridge. -/
def weakEquation_coordinatePullbackStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n)
    (U V : Domain n) (LF LG : ℝ≥0) (F : P102.U4.BiLipschitzChart U V LF LG)
    (hvol : Measure.map F.toFun (domainMeasure V) = domainMeasure U)
    (A : Space n → Space n →L[ℝ] Space n)
    (hA : ContinuousOn A U) {M : ℝ} (hM : ∀ x ∈ U, ‖A x‖ ≤ M)
    (u : H ℝ U 1) (f : Lp ℝ U 2)
    (heq : P201Specs.InteriorH2.WeakEquation U A u f),
    ∃ (w : H ℝ V 1) (g : Lp ℝ V 2),
      (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun y => hUnderlying U 1 u (F.toFun y)) ∧
      (g : Space n → ℝ) =ᵐ[domainMeasure V] (fun y => f (F.toFun y)) ∧
      P201Specs.InteriorH2.WeakEquation V
        (fun y => conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y))) w g ∧
      ‖w‖ ≤ ((Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) *
        P102.U4.pullbackSobolevBound n 2 LF LG) * ‖u‖ ∧
      ‖g‖ ≤ P102.U4.pullbackLpBound n 2 LG * ‖f‖

/-- Independent statement of the derived coordinate/volume bridge. -/
def physicalChartMap_inverse_volumeStatement : Prop :=
  ∀ {m : ℕ}
    (e q : P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Domain (m + 1))
    (C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient m)))
    (S : Set (Space (m + 1))) (hS : S ⊆ P102.Trace.Ordinary.physicalChartOpen e Ω C),
    volume ((P102.Trace.Ordinary.physicalChartMap e q Ω C).invFun '' S) = volume S

/-- Independent statement of the derived coordinate/volume bridge. -/
def physicalChartMap_map_volumeStatement : Prop :=
  ∀ {m : ℕ}
    (e q : P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Domain (m + 1))
    (C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient m))),
    Measure.map (P102.Trace.Ordinary.physicalChartMap e q Ω C).toFun
      (domainMeasure (P102.Trace.Ordinary.flatChartOpen q C.center C.radius C.height)) =
        domainMeasure (P102.Trace.Ordinary.physicalChartOpen e Ω C)

/-- Independent statement of the derived coordinate/volume bridge. -/
def physicalGraphWeakEquationStatement : Prop :=
  ∀ {m : ℕ}
    (e q : P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Domain (m + 1))
    (C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient m)))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (hA : ContinuousOn A (P102.Trace.Ordinary.physicalChartOpen e Ω C))
    {M : ℝ} (hM : ∀ x ∈ P102.Trace.Ordinary.physicalChartOpen e Ω C, ‖A x‖ ≤ M)
    (u : H ℝ (P102.Trace.Ordinary.physicalChartOpen e Ω C) 1)
    (f : Lp ℝ (P102.Trace.Ordinary.physicalChartOpen e Ω C) 2)
    (heq : P201Specs.InteriorH2.WeakEquation
      (P102.Trace.Ordinary.physicalChartOpen e Ω C) A u f),
    let F := P102.Trace.Ordinary.physicalChartMap e q Ω C
    let U := P102.Trace.Ordinary.physicalChartOpen e Ω C
    let V := P102.Trace.Ordinary.flatChartOpen q C.center C.radius C.height
    ∃ (w : H ℝ V 1) (g : Lp ℝ V 2),
      (hUnderlying V 1 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure V]
        (fun y => hUnderlying U 1 u (F.toFun y)) ∧
      (g : Space (m + 1) → ℝ) =ᵐ[domainMeasure V] (fun y => f (F.toFun y)) ∧
      P201Specs.InteriorH2.WeakEquation V
        (fun y => conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y))) w g ∧
      ‖w‖ ≤ ((Fintype.card (P102.U4.SobolevIndex (m + 1) 1) : ℝ) *
        P102.U4.pullbackSobolevBound (m + 1) 2 (P102.Sobolev.Geometry.shearConstant C.constant)
          (P102.Sobolev.Geometry.shearConstant C.constant)) * ‖u‖ ∧
      ‖g‖ ≤ P102.U4.pullbackLpBound (m + 1) 2
        (P102.Sobolev.Geometry.shearConstant C.constant) * ‖f‖

end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

def selectBoundaryChartNeighborhoodStatement : Prop :=
  ∀ {m : ℕ} (Ω : P201Specs.Domain (m+1))
    (hΩ : P201Specs.HasC11Boundary Ω) (p : P201Specs.Space (m+1))
    (hp : p ∈ frontier (Ω : Set (P201Specs.Space (m+1)))),
    ∃ (C : BoundaryChart (geometricOpen (P201Specs.graphFrame m) Ω : Set (Ambient m)))
      (Hder : ℝ≥0) (R r : ℝ) (χ : P201Specs.Test ℝ (⊤ : P201Specs.Domain (m+1))),
      (P201Specs.graphFrame m) (C.frame (graph C.graphFunction C.center)) = p ∧
      ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius) ∧
      LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius) ∧
      0 < r ∧ r < R ∧
      ball p R ⊆ fullPhysicalChartOpen (P201Specs.graphFrame m) C ∧
      P201Specs.BoundaryH2.neighborhood Ω p R ≤ physicalChartOpen (P201Specs.graphFrame m) Ω C ∧
      tsupport χ ⊆ ball p R ∧
      (∀ x ∈ ball p r, χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) 

end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

def selectNestedFlatCutoffStatement : Prop :=
  ∀ {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] P201Specs.Space (m+1)) (Ω : P201Specs.Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : P201Specs.Space (m+1))
    (hcenter : e (C.frame (graph C.graphFunction C.center)) = p)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hchart : ball p ρ ⊆ fullPhysicalChartOpen e C),
    let y0 := flatCoordinates m (WithLp.toLp 2 (C.center,(0:ℝ)))
    ∃ (a s : ℝ) (η : P201Specs.Test ℝ (⊤ : P201Specs.Domain (m+1))),
      0 < a ∧ 0 < s ∧ s < ρ ∧
      ball y0 (2*a) ⊆ (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (P201Specs.Space (m+1))) ∩
        (fullChartMap e (flatCoordinates m) C).toFun ⁻¹' ball p ρ ∧
      tsupport η ⊆ ball y0 (2*a) ∧
      tsupport η ⊆ closedBall y0 (3*a/2) ∧
      (∀ y ∈ ball y0 a, η y = 1) ∧
      (∀ y, 0 ≤ η y ∧ η y ≤ 1) ∧
      (∀ x ∈ P201Specs.BoundaryH2.neighborhood Ω p s,
        (physicalChartMap e (flatCoordinates m) Ω C).invFun x ∈
          ball y0 a ∩ (P102.Trace.halfSpace m : Set (P201Specs.Space (m+1))))
end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P201Specs.InteriorH2
def boundaryWeightedFluxIntegralStatement : Prop :=
  ∀ {n : ℕ} (W V : Domain n) (hWV : W ≤ V)
    (η : Space n → ℝ) (geta : Space n → Space n)
    (A : Space n → Space n →L[ℝ] Space n)
    (g F : MeasureTheory.Lp (Space n) 2 (domainMeasure V))
    (hF : (F : Space n → Space n) =ᵐ[domainMeasure V] (fun x => A x (g x)))
    (z : H ℝ (⊤ : Domain n) 1) (q : Space n → ℝ) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (hgz : (hGradient z : Space n → Space n) =ᵐ[domainMeasure W]
      (fun x => η x ^ 2 • (h⁻¹ • (g (x + h • coordinate n k) - g x)) +
        (2 * η x * q x) • geta x))
    (hzoff : ∀ᵐ x ∂volume, x ∉ W → hGradient z x = 0),
    (∫ x, inner ℝ
      (h⁻¹ • (((V : Set (Space n)).indicator (F : Space n → Space n))
          (x + h • coordinate n k) -
        ((V : Set (Space n)).indicator (F : Space n → Space n)) x)) (hGradient z x)) =
      ∫ x in W, inner ℝ
        (A (x + h • coordinate n k) (η x • (h⁻¹ • (g (x + h • coordinate n k) - g x))) +
          η x • ((h⁻¹ • (A (x + h • coordinate n k) - A x)) (g x)))
        (η x • (h⁻¹ • (g (x + h • coordinate n k) - g x)) +
          (2 * q x) • geta x)

def localBoundary_discrete_energy_identity_vectorStatement : Prop :=
  ∀ {m : ℕ}
    (W V : Domain (m + 1))
    (hWV : (W : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (F : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure V))
    (f : Lp ℝ V 2)
    (heq : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x)
    (z : H ℝ (⊤ : Domain (m + 1)) 1) (K : Compacts (Space (m + 1)))
    (hKW : (K : Set (Space (m + 1))) ⊆ W)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (hzbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ K, x + h • coordinate (m + 1) k ∈ W),
    (∫ x, inner ℝ
      (h⁻¹ • (((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1)))
          (x + h • coordinate (m + 1) k) -
        ((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1))) x))
      (hGradient z x)) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x)

def boundaryGradientQuotient_step_boundStatement : Prop :=
  ∀ {m : ℕ}
    (S W V O : Domain (m + 1)) [IsFiniteMeasure (domainMeasure S)]
    (hSW : S ≤ W) (hWV : W ≤ V)
    (hOV : (O : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (η : Test ℝ (⊤ : Domain (m + 1)))
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηO : tsupport η ⊆ O)
    (hηS : tsupport η ∩ (P102.Trace.halfSpace m : Set (Space (m + 1))) ⊆ S)
    (G M L Cz : ℝ≥0) (theta : ℝ) (ht : 0 < theta)
    (hG : ∀ x, ‖gradient η x‖ ≤ G)
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (hA : CoefficientBounds V A M L theta)
    (v : H ℝ V 1) (f : Lp ℝ V 2) (heq : WeakEquation V A v f)
    (Z : H ℝ (⊤ : Domain (m + 1)) 1)
    (hZgrad : (hGradient Z : Space (m + 1) → Space (m + 1))
      =ᵐ[domainMeasure W] hGradient v)
    (hZzero : ∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
      hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0)
    (hZn : ‖Z‖ ≤ Cz * ‖v‖)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) (hh : h ≠ 0)
    (hdint : Integrable (hFirstDerivative Z k : Space (m + 1) → ℝ) volume)
    (haS : ∀ x ∈ S, x + h • coordinate (m + 1) k ∈ W)
    (haO : ∀ x ∈ tsupport η, x + h • coordinate (m + 1) k ∈ O),
    ∃ p : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure S),
      ((p : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S] fun x =>
        η x • (h⁻¹ • (hGradient v (x + h • coordinate (m + 1) k) - hGradient v x))) ∧
      ‖p‖ ≤ (1 + 2 * (1 + L + 2 * M * G + 2 * L * G + 2 * G) / theta) *
        ((1 + Cz) * ‖v‖ + ‖f‖)

def boundaryScalarQuotientStatement : Prop :=
  ∀ {n : ℕ} {U W V : Domain n}
    (hUW : U ≤ W) (hWV : W ≤ V) (η : Space n → ℝ)
    (hηU : ∀ x ∈ U, η x = 1) (v : H ℝ V 1) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (p : MeasureTheory.Lp (Space n) 2 (domainMeasure W))
    (hp : (p : Space n → Space n) =ᵐ[domainMeasure W]
      (fun x => η x • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x))))
    (j : Fin n),
    MemLp (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ∧
      eLpNorm (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ≤ ‖p‖₊

def flatBoundaryEstimate_with_extensionStatement : Prop :=
  ∀ {m : ℕ}
    (U S W V O : Domain (m + 1)) [IsFiniteMeasure (domainMeasure S)]
    (hUS : U ≤ S) (hSW : S ≤ W) (hWV : W ≤ V)
    (hOV : (O : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (η : Test ℝ (⊤ : Domain (m + 1)))
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηO : tsupport η ⊆ O)
    (hηS : tsupport η ∩ (P102.Trace.halfSpace m : Set (Space (m + 1))) ⊆ S)
    (hηU : ∀ x ∈ U, η x = 1)
    (G M L Cz : ℝ≥0) (theta : ℝ) (ht : 0 < theta)
    (hG : ∀ x, ‖gradient η x‖ ≤ G)
    (δ : ℝ) (hδ : 0 < δ)
    (haS : ∀ (k : Fin (m + 1)), k ≠ Fin.last m →
      ∀ h : ℝ, |h| < δ → ∀ x ∈ S, x + h • coordinate (m + 1) k ∈ W)
    (haO : ∀ (k : Fin (m + 1)), k ≠ Fin.last m →
      ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport η, x + h • coordinate (m + 1) k ∈ O),
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      CoefficientBounds V A M L theta →
      ∀ (v : H ℝ V 1) (f : Lp ℝ V 2), WeakEquation V A v f →
      ∀ Z : H ℝ (⊤ : Domain (m + 1)) 1,
      ((hGradient Z : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure W] hGradient v) →
      (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
        hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) →
      ‖Z‖ ≤ Cz * ‖v‖ →
      (∀ k : Fin (m + 1), k ≠ Fin.last m →
        Integrable (hFirstDerivative Z k : Space (m + 1) → ℝ) volume) →
      ∃ w : H ℝ U 2,
        (hUnderlying U 2 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
        ‖w‖ ≤ C * (‖v‖ + ‖f‖)


end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open scoped ContDiff

/-- Independent statement of canonical cutoff multiplication/local control. -/
def hZeroLipschitzMultiplierStatement : Prop :=
  ∀ {n : ℕ} (V : Domain n) (a : Space n → ℝ)
    (M L : ℝ≥0) (haL : LipschitzOnWith L a V) (haM : ∀ x ∈ V, |a x| ≤ M),
    ∃ T : H10 ℝ V →L[ℝ] H10 ℝ V,
      (∀ u, (hZeroUnderlying V (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => a x * hZeroUnderlying V u x)) ∧
      (∀ u j, (hFirstDerivative (T u).val j : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => a x * hFirstDerivative u.val j x +
          fderiv ℝ a x (coordinate n j) * hZeroUnderlying V u x)) ∧
      ∀ u, ‖T u‖ ≤ ((1 + (n : ℝ)) * ((M : ℝ) + L)) * ‖u‖

/-- Independent statement of canonical cutoff multiplication/local control. -/
def hZeroSmoothCutoffStatement : Prop :=
  ∀ {n : ℕ} (V : Domain n) (χ : Space n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    ∃ C : ℝ, 0 < C ∧ ∃ T : H10 ℝ V →L[ℝ] H10 ℝ V,
      ∀ u,
        (hZeroUnderlying V (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hZeroUnderlying V u x) ∧
        (∀ j, (hFirstDerivative (T u).val j : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hFirstDerivative u.val j x +
            fderiv ℝ χ x (coordinate n j) * hZeroUnderlying V u x)) ∧
        (∀ᵐ x ∂domainMeasure V, x ∉ tsupport χ → hZeroUnderlying V (T u) x = 0) ∧
        ‖T u‖ ≤ C * ‖u‖

/-- Independent statement of canonical cutoff multiplication/local control. -/
def h1CutoffLocalBoundStatement : Prop :=
  ∀ {n : ℕ} (V U : Domain n) (hUV : U ≤ V)
    (χ : Space n → ℝ) (hχ : Continuous χ) (M L : ℝ≥0)
    (hχM : ∀ x ∈ V, |χ x| ≤ M)
    (hχD : ∀ x ∈ V, ‖fderiv ℝ χ x‖ ≤ L)
    (hχU : tsupport χ ∩ (V : Set (Space n)) ⊆ U)
    (u w : H ℝ V 1) (v : H ℝ U 1)
    (hv : (hUnderlying U 1 v : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 u)
    (hvd : ∀ j, (hFirstDerivative v j : Space n → ℝ) =ᵐ[domainMeasure U] hFirstDerivative u j)
    (hw : (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun x => χ x * hUnderlying V 1 u x))
    (hwd : ∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun x => χ x * hFirstDerivative u j x +
        fderiv ℝ χ x (coordinate n j) * hUnderlying V 1 u x)),
    ‖w‖ ≤ ((1 + (n : ℝ)) * ((M : ℝ) + L)) * ‖v‖

/-- Independent statement of canonical cutoff multiplication/local control. -/
def hZeroSmoothCutoffLocalStatement : Prop :=
  ∀ {n : ℕ} (V : Domain n) (χ : Space n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ),
    ∃ C : ℝ, 0 < C ∧ ∃ T : H10 ℝ V →L[ℝ] H10 ℝ V,
      (∀ u,
        (hZeroUnderlying V (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hZeroUnderlying V u x) ∧
        (∀ j, (hFirstDerivative (T u).val j : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hFirstDerivative u.val j x +
            fderiv ℝ χ x (coordinate n j) * hZeroUnderlying V u x)) ∧
        (∀ᵐ x ∂domainMeasure V, x ∉ tsupport χ → hZeroUnderlying V (T u) x = 0)) ∧
      ∀ (U : Domain n), U ≤ V → tsupport χ ∩ (V : Set (Space n)) ⊆ U →
        ∀ (u : H10 ℝ V) (v : H ℝ U 1),
        (hUnderlying U 1 v : Space n → ℝ) =ᵐ[domainMeasure U] hZeroUnderlying V u →
        (∀ j, (hFirstDerivative v j : Space n → ℝ) =ᵐ[domainMeasure U] hFirstDerivative u.val j) →
        ‖T u‖ ≤ C * ‖v‖

end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
def h10ZeroExtensionStatement : Prop :=
  ∀ {n : ℕ} (V : Domain n) (w : H10 ℝ V),
    ∃ Z : H ℝ (⊤ : Domain n) 1,
      hUnderlying ⊤ 1 Z = P102.U4.lpZeroExtension V 2 (hZeroUnderlying V w) ∧
      (∀ j, hFirstDerivative Z j = P102.U4.lpZeroExtension V 2 (hFirstDerivative w.val j)) ∧
      ‖Z‖ = ‖w‖

def h10ZeroExtension_gradientStatement : Prop :=
  ∀ {n : ℕ} (V : Domain n) (w : H10 ℝ V)
    (Z : H ℝ (⊤ : Domain n) 1)
    (hZd : ∀ j, hFirstDerivative Z j = P102.U4.lpZeroExtension V 2 (hFirstDerivative w.val j)),
    (hGradient Z : Space n → Space n) =ᵐ[volume]
      (V : Set (Space n)).indicator (hGradient w.val)

def zeroExtension_derivative_integrableStatement : Prop :=
  ∀ {n : ℕ} (V : Domain n) (w : H10 ℝ V)
    (K : Compacts (Space n))
    (hK : ∀ᵐ x ∂domainMeasure V, x ∉ K → hZeroUnderlying V w x = 0)
    (Z : H ℝ (⊤ : Domain n) 1)
    (hZu : hUnderlying ⊤ 1 Z = P102.U4.lpZeroExtension V 2 (hZeroUnderlying V w)),
    ∀ j, Integrable (hFirstDerivative Z j : Space n → ℝ) volume

def halfSpaceZeroExtensionStatement : Prop :=
  ∀ {m : ℕ} (w : H10 ℝ (P102.Trace.halfSpace m))
    (K : Compacts (Space (m + 1)))
    (hK : ∀ᵐ x ∂domainMeasure (P102.Trace.halfSpace m),
      x ∉ K → hZeroUnderlying (P102.Trace.halfSpace m) w x = 0),
    ∃ Z : H ℝ (⊤ : Domain (m + 1)) 1,
      (hUnderlying ⊤ 1 Z : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)] hZeroUnderlying (P102.Trace.halfSpace m) w ∧
      (hGradient Z : Space (m + 1) → Space (m + 1))
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)] hGradient w.val ∧
      (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
        hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) ∧
      ‖Z‖ = ‖w‖ ∧
      (∀ j, Integrable (hFirstDerivative Z j : Space (m + 1) → ℝ) volume)

def h1Gradient_congr_onStatement : Prop :=
  ∀ {n : ℕ} (U V W : Domain n)
    (hUV : U ≤ V) (hUW : U ≤ W) (v : H ℝ V 1) (w : H ℝ W 1)
    (hvw : (hUnderlying V 1 v : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying W 1 w),
    (hGradient v : Space n → Space n) =ᵐ[domainMeasure U] hGradient w


end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
def coordinateH1InverseBoundStatement : Prop :=
  ∀ {n : ℕ} (hn : 0 < n)
    (U V : Domain n) (LF LG : ℝ≥0) (F : P102.U4.BiLipschitzChart U V LF LG)
    (u : H ℝ U 1) (w : H ℝ V 1)
    (hw : (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun y => hUnderlying U 1 u (F.toFun y))),
    ‖u‖ ≤ ((Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) *
      P102.U4.pullbackSobolevBound n 2 LG LF) * ‖w‖ 
end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

def h2OpenRestrictionStatement : Prop :=
  ∀ {n : ℕ} (V U : Domain n) (hUV : U ≤ V),
    ∃ C : ℝ, 0 < C ∧ ∀ u : H ℝ V 2,
      ∃ w : H ℝ U 2,
        (hUnderlying U 2 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 2 u ∧
        ‖w‖ ≤ C * ‖u‖ 

def physicalGraphH2RestrictionToOpenStatement : Prop :=
  ∀ {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (Ω : Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (Hder : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius))
    (U : Domain (m+1)) (hU : U ≤ physicalChartOpen e Ω C)
    (V : Domain (m+1))
    (hpre : (physicalChartMap e q Ω C).preimageOpen U ≤ V),
    ∃ K : ℝ, 0 < K ∧ ∀ w : H ℝ V 2,
      ∃ u : H ℝ U 2,
        (hUnderlying U 2 u : Space (m+1) → ℝ) =ᵐ[domainMeasure U]
          (fun x => hUnderlying V 2 w ((physicalChartMap e q Ω C).invFun x)) ∧
        ‖u‖ ≤ K * ‖w‖ 
end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
def coordinateVolume_restrictStatement : Prop :=
  ∀ {n : ℕ} (U V : Domain n) (LF LG : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V LF LG)
    (hvol : Measure.map F.toFun (domainMeasure V) = domainMeasure U)
    (P : Domain n) (hPU : P ≤ U),
    Measure.map (F.restrict P hPU).toFun (domainMeasure (F.preimageOpen P)) =
      domainMeasure P 
end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

/-- Independent statement of localization, geometric flattening and actual
whole-space H¹ zero extension, with the outer local H¹ norm. -/
def localizedCoordinateZeroExtensionStatement : Prop :=
  ∀ {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (χ : Space (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχK : tsupport χ ⊆ K)
    (O : Domain (m + 1)) (hOΩ : O ≤ Ω)
    (hχO : tsupport χ ∩ (Ω : Set (Space (m + 1))) ⊆ O)
    (W : Domain (m + 1))
    (hWF : W ≤ flatChartOpen (flatCoordinates m) C.center C.radius C.height)
    (hOne : ∀ y ∈ W, χ ((physicalChartMap e (flatCoordinates m) Ω C).toFun y) = 1),
    ∃ Cext : ℝ, 0 < Cext ∧
      ∀ (u : H10 ℝ Ω) (v : H ℝ O 1),
      (hUnderlying O 1 v : Space (m + 1) → ℝ) =ᵐ[domainMeasure O] hZeroUnderlying Ω u →
      (∀ j, (hFirstDerivative v j : Space (m + 1) → ℝ) =ᵐ[domainMeasure O] hFirstDerivative u.val j) →
      ∃ Z : H ℝ (⊤ : Domain (m + 1)) 1,
        (hUnderlying ⊤ 1 Z : Space (m + 1) → ℝ) =ᵐ[domainMeasure W]
          (fun y => hZeroUnderlying Ω u ((physicalChartMap e (flatCoordinates m) Ω C).toFun y)) ∧
        (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
          hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) ∧
        (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
          ∀ j, hFirstDerivative Z j x = 0) ∧
        (∀ j, Integrable (hFirstDerivative Z j : Space (m + 1) → ℝ) volume) ∧
        (∀ᵐ x ∂volume, x ∉ fullChartPullbackCompact e (flatCoordinates m) C K hK →
          hUnderlying ⊤ 1 Z x = 0) ∧
        ‖Z‖ ≤ Cext * ‖v‖

end P201Specs.BoundaryH2

namespace P201Specs.BoundaryH2
open P201Specs.InteriorH2
def flatBallBoundaryEstimateStatement : Prop :=
  ∀ {m : ℕ} (y0 : Space (m+1)) (a : ℝ) (ha : 0 < a)
    (V : Domain (m+1))
    (hOV : ball y0 (2*a) ∩ (P102.Trace.halfSpace m : Set (Space (m+1))) ⊆ V)
    (η : Test ℝ (⊤ : Domain (m+1)))
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηsupp : tsupport η ⊆ closedBall y0 (3*a/2))
    (hηone : ∀ y ∈ ball y0 a, η y = 1)
    (M L Cz : ℝ≥0) (theta : ℝ) (ht : 0 < theta),
    let U : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 a,isOpen_ball⟩
    let W : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 (2*a),isOpen_ball⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Space (m+1) → Space (m+1) →L[ℝ] Space (m+1),
      P201Specs.InteriorH2.CoefficientBounds V A M L theta →
      ∀ (v : H ℝ V 1) (f : Lp ℝ V 2), P201Specs.InteriorH2.WeakEquation V A v f →
      ∀ Z : H ℝ (⊤ : Domain (m+1)) 1,
      ((hGradient Z : Space (m+1) → Space (m+1)) =ᵐ[domainMeasure W] hGradient v) →
      (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
        hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) →
      ‖Z‖ ≤ Cz * ‖v‖ →
      (∀ k : Fin (m+1), k ≠ Fin.last m →
        Integrable (hFirstDerivative Z k : Space (m+1) → ℝ) volume) →
      ∃ w : H ℝ U 2,
        (hUnderlying U 2 w : Space (m+1) → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
        ‖w‖ ≤ C * (‖v‖ + ‖f‖) 
end P201Specs.BoundaryH2
