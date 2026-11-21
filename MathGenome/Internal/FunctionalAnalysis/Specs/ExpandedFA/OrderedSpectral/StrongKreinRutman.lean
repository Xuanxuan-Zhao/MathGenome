import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OrderedSpectral.KreinRutmanExistence
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! Independent specifications for the remaining strong Krein--Rutman
clauses, paper.tex:11778–11860. No normality assumption is imposed. -/
namespace ExpandedFA.OrderedSpectral.StrongKreinRutman

/-- A concrete complexification of a real normed space. An element f represents
f(1) + i f(i); the operator norm is equivalent to the real product norm.
Complex scalars act by precomposition with multiplication by their conjugate.
The norm is the supremum of ‖a x + b y‖ for a²+b² ≤ 1. -/
def Complexification (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] := ℂ →L[ℝ] X

namespace Complexification
noncomputable section
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

instance : NormedAddCommGroup (Complexification X) := inferInstanceAs (NormedAddCommGroup (ℂ →L[ℝ] X))
instance : NormedSpace ℝ (Complexification X) := inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] X))
instance [CompleteSpace X] : CompleteSpace (Complexification X) := inferInstanceAs (CompleteSpace (ℂ →L[ℝ] X))

instance : CoeFun (Complexification X) (fun _ => ℂ → X) := ⟨fun f => DFunLike.coe (F := ℂ →L[ℝ] X) f⟩

@[ext] theorem ext {f g : Complexification X} (h : ∀ z : ℂ, f z = g z) : f = g :=
  ContinuousLinearMap.ext h

@[simp] theorem add_apply (f g : Complexification X) (z : ℂ) : (f + g) z = f z + g z := rfl
@[simp] theorem zero_apply (z : ℂ) : (0 : Complexification X) z = 0 := rfl
@[simp] theorem real_smul_apply (a : ℝ) (f : Complexification X) (z : ℂ) :
    (a • f) z = a • f z := rfl
@[simp] theorem apply_add (f : Complexification X) (z w : ℂ) : f (z + w) = f z + f w :=
  (show ℂ →L[ℝ] X from f).map_add z w
@[simp] theorem apply_zero (f : Complexification X) : f 0 = 0 :=
  (show ℂ →L[ℝ] X from f).map_zero
@[simp] theorem apply_real_smul (f : Complexification X) (a : ℝ) (z : ℂ) :
    f (a • z) = a • f z := (show ℂ →L[ℝ] X from f).map_smul a z

instance : SMul ℂ (Complexification X) where
  smul c f := (f : ℂ →L[ℝ] X).comp (ContinuousLinearMap.mul ℝ ℂ (star c))

@[simp] theorem complex_smul_apply (c : ℂ) (f : Complexification X) (z : ℂ) :
    (c • f : Complexification X) z = f (star c * z) := rfl

instance : Module ℂ (Complexification X) where
  one_smul f := by ext z; simp
  mul_smul a b f := by ext z; simp [mul_assoc, mul_comm a b, mul_left_comm]
  smul_zero a := by ext z; simp
  smul_add a f g := by ext z; simp
  add_smul a b f := by ext z; simp [add_mul]
  zero_smul f := by ext z; simp

instance : NormedSpace ℂ (Complexification X) where
  norm_smul_le c f := by
    change ‖(f : ℂ →L[ℝ] X).comp (ContinuousLinearMap.mul ℝ ℂ (star c))‖ ≤ ‖c‖ * ‖f‖
    calc
      _ ≤ ‖f‖ * ‖ContinuousLinearMap.mul ℝ ℂ (star c)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖c‖ * ‖f‖ := by simp [mul_comm]

instance : IsScalarTower ℝ ℂ (Complexification X) where
  smul_assoc a c f := by
    ext z
    change f (star (a • c) * z) = a • f (star c * z)
    simpa only [star_smul, star_trivial, smul_mul_assoc] using apply_real_smul f a (star c * z)

/-- Real coordinates of the concrete complexification. -/
def realPart (f : Complexification X) : X := f 1
/-- Imaginary coordinates of the concrete complexification. -/
def imagPart (f : Complexification X) : X := f Complex.I
/-- The canonical real embedding. -/
def ofReal (x : X) : Complexification X := Complex.reCLM.smulRight x

@[simp] theorem realPart_ofReal (x : X) : realPart (ofReal x) = x := by
  simp [realPart, ofReal]
@[simp] theorem imagPart_ofReal (x : X) : imagPart (ofReal x) = 0 := by
  simp [imagPart, ofReal]

@[simp] theorem ofReal_apply (x : X) (z : ℂ) : ofReal x z = z.re • x := rfl
@[simp] theorem sub_apply (f g : Complexification X) (z : ℂ) : (f - g) z = f z - g z := rfl
@[simp] theorem ofReal_smul_apply (a : ℝ) (f : Complexification X) (z : ℂ) :
    ((a : ℂ) • f) z = a • f z := by
  rw [complex_smul_apply]
  simp only [Complex.star_def, Complex.conj_ofReal]
  change f (a • z) = a • f z
  exact apply_real_smul f a z

/-- Complex-linear extension of a bounded real operator. -/
def extend (T : X →L[ℝ] X) : Complexification X →L[ℂ] Complexification X where
  toFun f := T.comp (show ℂ →L[ℝ] X from f)
  map_add' f g := by
    ext z
    change T (f z + g z) = T (f z) + T (g z)
    exact T.map_add _ _
  map_smul' c f := by ext z; rfl
  cont := (ContinuousLinearMap.compL ℝ ℂ X X T).continuous

@[simp] theorem extend_apply (T : X →L[ℝ] X) (f : Complexification X) (z : ℂ) :
    extend T f z = T (f z) := rfl

/-- Real-coordinate equivalence, recording that this is the ordinary
complexification of X and has exactly the product topology. -/
def equivRealProd : Complexification X ≃L[ℝ] X × X where
  toFun f := (f 1, f Complex.I)
  invFun p := Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2
  left_inv f := by
    apply ext
    intro z
    change z.re • f 1 + z.im • f Complex.I = f z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by simp
    calc
      _ = f (z.re • (1 : ℂ) + z.im • Complex.I) := by
        rw [apply_add, apply_real_smul, apply_real_smul]
      _ = f z := congrArg f hz.symm
  right_inv p := by ext <;> simp
  map_add' f g := rfl
  map_smul' a f := rfl
  continuous_toFun := (ContinuousLinearMap.apply ℝ X (1 : ℂ)).continuous.prodMk
    (ContinuousLinearMap.apply ℝ X Complex.I).continuous
  continuous_invFun := by
    exact ((ContinuousLinearMap.smulRightL ℝ ℂ X Complex.reCLM).continuous.comp continuous_fst).add
      ((ContinuousLinearMap.smulRightL ℝ ℂ X Complex.imCLM).continuous.comp continuous_snd)

end
end Complexification
end ExpandedFA.OrderedSpectral.StrongKreinRutman

namespace ExpandedFA.OrderedSpectral.StrongKreinRutman.Spec
universe u

/-- There is no length-two Jordan chain ending at an interior positive
μ-eigenvector. Compactness and completeness are unnecessary for this fact. -/
def NoJordanChain : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) → (P : Set X) ≠ Set.univ →
    ∀ (T : X →ₗ[ℝ] X),
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∀ (μ : ℝ) (u : X), 0 < μ → u ∈ interior (P : Set X) →
        T u = μ • u → ¬ ∃ w : X, T w - μ • w = u

/-- Every positive power kernel of T-μI is exactly the real eigenline.
This is algebraic simplicity, rather than geometric simplicity alone. -/
def RealGeneralizedSimplicity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) → (P : Set X) ≠ Set.univ →
    ∀ (T : X →ₗ[ℝ] X),
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∀ (μ : ℝ) (u : X), 0 < μ → u ∈ interior (P : Set X) →
        u ≠ 0 → T u = μ • u →
        ∀ n : ℕ, 1 ≤ n →
          LinearMap.ker ((T - μ • LinearMap.id) ^ n) = Submodule.span ℝ {u}

/-- Compactness is preserved by the concrete complexification in its actual
Banach norm, with no reference to an order norm. -/
def ComplexificationCompact : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : X →L[ℝ] X), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
      Compactness.DefinitionsSpec.IsCompactLinearMapValue (Complexification.extend T).toLinearMap

/-- Algebraic simplicity on the complexification, including every positive
power kernel. -/
def ComplexGeneralizedSimplicity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) → (P : Set X) ≠ Set.univ →
    ∀ (T : X →L[ℝ] X),
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∀ (μ : ℝ) (u : X), 0 < μ → u ∈ interior (P : Set X) →
        u ≠ 0 → T u = μ • u → ∀ n : ℕ, 1 ≤ n →
          LinearMap.ker (((Complexification.extend T).toLinearMap -
            (μ : ℂ) • LinearMap.id) ^ n) =
            Submodule.span ℂ {Complexification.ofReal u}

/-- Eigenvalue comparison in real coordinates. These two equations mean
that x+i y is a complex eigenvector, including real eigenvalues and all
possible dependencies between x and y. This assertion is to be proved,
not an additional hypothesis of the source theorem. -/
def CoordinateSpectralGap : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) → (P : Set X) ≠ Set.univ →
    ∀ (T : X →L[ℝ] X), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∀ (μ : ℝ) (u : X), 0 < μ → u ∈ interior (P : Set X) →
        u ≠ 0 → T u = μ • u → ∀ (ζ : ℂ) (x y : X),
          (x ≠ 0 ∨ y ≠ 0) →
          T x = ζ.re • x - ζ.im • y → T y = ζ.im • x + ζ.re • y →
          ζ ≠ 0 → ζ ≠ (μ : ℂ) → ‖ζ‖ < μ

/-- The eigenplane comparison, restricted to genuinely nonreal
eigenvalues. All real eigenvalues are covered separately. -/
def NonrealCoordinateSpectralGap : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) → (P : Set X) ≠ Set.univ →
    ∀ (T : X →L[ℝ] X), Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∀ (μ : ℝ) (u : X), 0 < μ → u ∈ interior (P : Set X) →
        u ≠ 0 → T u = μ • u → ∀ (ζ : ℂ) (x y : X), ζ.im ≠ 0 →
          (x ≠ 0 ∨ y ≠ 0) →
          T x = ζ.re • x - ζ.im • y → T y = ζ.im • x + ζ.re • y → ‖ζ‖ < μ

/-- The full conclusion at the principal eigenpair, over the explicit
complex Banach complexification. -/
def Conclusion {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : ConvexCone ℝ X) (T : X →L[ℝ] X) (μ : ℝ) (u : X) : Prop :=
  0 < μ ∧ u ∈ interior (P : Set X) ∧ u ≠ 0 ∧ T u = μ • u ∧
    (∀ (ν : ℝ) (x : X), x ∈ P → x ≠ 0 → T x = ν • x →
      ν = μ ∧ ∃ a : ℝ, 0 < a ∧ x = a • u) ∧
    (∀ n : ℕ, 1 ≤ n →
      LinearMap.ker (((Complexification.extend T).toLinearMap -
        (μ : ℂ) • LinearMap.id) ^ n) = Submodule.span ℂ {Complexification.ofReal u}) ∧
    (∀ ζ : ℂ, ζ ≠ 0 → ζ ≠ (μ : ℂ) →
      (∃ z : Complexification X, z ≠ 0 ∧ Complexification.extend T z = ζ • z) →
        ‖ζ‖ < μ) ∧
    spectralRadius ℂ (Complexification.extend T) = ENNReal.ofReal μ

/-- The unchanged source theorem. Compact algebraic operators are automatically
bounded; the bounded representative is required to be the very same map.
Salience is derived upstream, never added as an assumption. -/
def FullTheorem : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (P : ConvexCone ℝ X), IsClosed (P : Set X) →
    (interior (P : Set X)).Nonempty → (P : Set X) ≠ Set.univ →
    ∀ (T : X →ₗ[ℝ] X), Compactness.DefinitionsSpec.IsCompactLinearMapValue T →
      (∀ x ∈ P, x ≠ 0 → T x ∈ interior (P : Set X)) →
      ∃ Tb : X →L[ℝ] X, Tb.toLinearMap = T ∧
        Compactness.DefinitionsSpec.IsCompactLinearMapValue (Complexification.extend Tb).toLinearMap ∧
        ∃ (μ : ℝ) (u : X), Conclusion P Tb μ u

/-- Assembly obligation once the independent real-coordinate eigenvalue
comparison is available. The source theorem itself remains unconditional. -/
def GapImpliesFullTheorem : Prop := CoordinateSpectralGap.{u} → FullTheorem.{u}
/-- A proved reduction of the remaining work to nonreal eigenvalues. -/
def NonrealGapImpliesGap : Prop := NonrealCoordinateSpectralGap.{u} → CoordinateSpectralGap.{u}
/-- Assembly of the full theorem from the nonreal eigenplane comparison. -/
def NonrealGapImpliesFullTheorem : Prop := NonrealCoordinateSpectralGap.{u} → FullTheorem.{u}
end ExpandedFA.OrderedSpectral.StrongKreinRutman.Spec
