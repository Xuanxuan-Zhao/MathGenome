import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Characters
import Mathlib.Topology.ContinuousMap.Ideals
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.MvPolynomial.Eval

/-! Independent specifications for the compact and disk/polydisk parts of
paper.tex, fa2:p2:function-algebra-characters (9958–10004). Characters remain
the shared algebraic nonzero multiplicative linear maps; the topology is the
initial topology of all evaluations. No nonempty-space assumption is imposed
on compact K. Holomorphic function algebras and polynomial uniform closures
are distinct definitions with an explicit, unassumed bridge. -/
noncomputable section
namespace Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters
open Conventions
universe u

abbrev Character (A : Type u) [NormedCommRing A] [NormedAlgebra ℂ A] :=
  CharacterValue ℂ A

def CompactEvaluationHomeomorphism : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K],
    letI := Characters.CharacterTopologyValue C(K, ℂ)
    ∃ e : K ≃ₜ Character C(K, ℂ),
      ∀ (x : K) (f : C(K, ℂ)), (e x).val f = f x

def CompactCharactersAreEvaluations : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (χ : Character C(K, ℂ)), ∃! x : K, ∀ f : C(K, ℂ), χ.val f = f x

def EmptyCompactCase : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] [IsEmpty K],
    Subsingleton C(K, ℂ) ∧ IsEmpty (Character C(K, ℂ))

/-- The ambient finite product has its usual maximum norm, including n = 0. -/
abbrev ClosedPolydisk (n : ℕ) :=
  ↥(Metric.closedBall (0 : Fin n → ℂ) 1)

instance (n : ℕ) : Inhabited (ClosedPolydisk n) :=
  ⟨⟨0, by simp⟩⟩

def polydiskCoordinate (n : ℕ) (j : Fin n) : C(ClosedPolydisk n, ℂ) :=
  ⟨fun z => z.val j, (continuous_apply j).comp continuous_subtype_val⟩

/-- All complex polynomials in the coordinates, with no conjugate coordinates. -/
def polydiskPolynomialFunctions (n : ℕ) : Subalgebra ℂ C(ClosedPolydisk n, ℂ) :=
  Algebra.adjoin ℂ (Set.range (polydiskCoordinate n))

/-- This auxiliary Banach algebra is not used as the definition of the
holomorphic polydisk algebra: the bridge between them is a separate obligation. -/
def polynomialUniformAlgebra (n : ℕ) : Subalgebra ℂ C(ClosedPolydisk n, ℂ) :=
  (polydiskPolynomialFunctions n).topologicalClosure

instance (n : ℕ) : CompleteSpace (polynomialUniformAlgebra n) :=
  (polydiskPolynomialFunctions n).isClosed_topologicalClosure.completeSpace_coe

def polynomialCoordinate (n : ℕ) (j : Fin n) : polynomialUniformAlgebra n :=
  ⟨polydiskCoordinate n j, (polydiskPolynomialFunctions n).le_topologicalClosure
    (Algebra.subset_adjoin (Set.mem_range_self j))⟩

/-- The actual polydisk algebra consists of continuous functions on the closed
polydisk holomorphic on its open interior. The extension is unrestricted off
the closed polydisk, so it imposes no extra boundary regularity. -/
def holomorphicPolydiskAlgebra (n : ℕ) : Subalgebra ℂ C(ClosedPolydisk n, ℂ) where
  carrier := {f | ∃ F : (Fin n → ℂ) → ℂ,
    DifferentiableOn ℂ F (Metric.ball 0 1) ∧ ∀ z : ClosedPolydisk n, F z.val = f z}
  algebraMap_mem' c := ⟨fun _ => c, differentiableOn_const _, fun _ => rfl⟩
  zero_mem' := ⟨fun _ => 0, differentiableOn_const _, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨F, hF, eF⟩ ⟨G, hG, eG⟩
    exact ⟨F + G, hF.add hG, fun z => congrArg₂ (· + ·) (eF z) (eG z)⟩
  mul_mem' := by
    rintro f g ⟨F, hF, eF⟩ ⟨G, hG, eG⟩
    exact ⟨F * G, hF.mul hG, fun z => congrArg₂ (· * ·) (eF z) (eG z)⟩

/-- Standalone analytic approximation obligation, suited to an independent
proof without imports from the candidate implementation. -/
def AmbientPolynomialApproximation : Prop :=
  ∀ (n : ℕ) (F : (Fin n → ℂ) → ℂ),
    ContinuousOn F (Metric.closedBall 0 1) →
    DifferentiableOn ℂ F (Metric.ball 0 1) →
    ∀ ε : ℝ, 0 < ε → ∃ p : MvPolynomial (Fin n) ℂ,
      ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) 1,
        ‖F z - MvPolynomial.eval z p‖ < ε

/-- The reverse analytic direction: polynomial uniform limits are holomorphic.
No differentiability or analytic certificate is assumed of the limit. -/
def AmbientPolynomialUniformLimit : Prop :=
  ∀ (n : ℕ) (F : (Fin n → ℂ) → ℂ),
    ContinuousOn F (Metric.closedBall 0 1) →
    (∀ ε : ℝ, 0 < ε → ∃ p : MvPolynomial (Fin n) ℂ,
      ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) 1,
        ‖F z - MvPolynomial.eval z p‖ < ε) →
    DifferentiableOn ℂ F (Metric.ball 0 1)

/-- Exact identification with the uniform closure, including the holomorphic
uniform-limit direction. This is not an assumed certificate. -/
def HolomorphicPolynomialDensity : Prop :=
  ∀ n : ℕ, holomorphicPolydiskAlgebra n = polynomialUniformAlgebra n

def HolomorphicPolynomialApproximation : Prop :=
  ∀ (n : ℕ) (f : holomorphicPolydiskAlgebra n) (ε : ℝ), 0 < ε →
    ∃ p : MvPolynomial (Fin n) ℂ,
      ‖f.val - MvPolynomial.aeval (polydiskCoordinate n) p‖ < ε

def UniformPolydiskCharacters : Prop :=
  ∀ (n : ℕ) (χ : Character (polynomialUniformAlgebra n)),
    ∃! z : ClosedPolydisk n, ∀ f : polynomialUniformAlgebra n, χ.val f = f.val z

def UniformPolydiskHomeomorphism : Prop :=
  ∀ n : ℕ,
    letI := Characters.CharacterTopologyValue (polynomialUniformAlgebra n)
    ∃ e : ClosedPolydisk n ≃ₜ Character (polynomialUniformAlgebra n),
      ∀ (z : ClosedPolydisk n) (f : polynomialUniformAlgebra n), (e z).val f = f.val z

def HolomorphicPolydiskCharacters : Prop :=
  ∀ (n : ℕ) (χ : Character (holomorphicPolydiskAlgebra n)),
    ∃! z : ClosedPolydisk n, ∀ f : holomorphicPolydiskAlgebra n, χ.val f = f.val z

def HolomorphicPolydiskHomeomorphism : Prop :=
  ∀ n : ℕ,
    letI := Characters.CharacterTopologyValue (holomorphicPolydiskAlgebra n)
    ∃ e : ClosedPolydisk n ≃ₜ Character (holomorphicPolydiskAlgebra n),
      ∀ (z : ClosedPolydisk n) (f : holomorphicPolydiskAlgebra n), (e z).val f = f.val z

/-- The one-dimensional disk is the n = 1 instance, retaining its actual
holomorphic function algebra rather than silently replacing it by a closure. -/
def DiskCharacters : Prop :=
  ∀ χ : Character (holomorphicPolydiskAlgebra 1),
    ∃! z : ClosedPolydisk 1, ∀ f : holomorphicPolydiskAlgebra 1, χ.val f = f.val z

end Specs.ExpandedFA.BanachAlgebra.ContinuousFunctionCharacters
