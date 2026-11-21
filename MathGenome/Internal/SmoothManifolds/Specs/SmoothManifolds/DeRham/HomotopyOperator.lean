import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.Cartan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent draft for the smooth homotopy operator in M11.02.
The cylinder uses simultaneous local ambient extensions in the spatial and time
variables. In particular a half-space source has corner cylinder charts.
No operator, smoothness certificate, or chain identity is assumed of a homotopy.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.HomotopyData
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData Set Filter
open scoped Topology
universe u

abbrev UnitInterval := Icc (0 : ℝ) 1

def initialTime : UnitInterval := ⟨0, by constructor <;> norm_num⟩
def finalTime : UnitInterval := ⟨1, by constructor <;> norm_num⟩

/-- A total extension of the parameter for writing within-interval derivatives
and integrals. Only its values on the closed unit interval are used. -/
def intervalTime (t : ℝ) : UnitInterval :=
  ⟨max 0 (min 1 t), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Smoothness on the actual cylinder, using the manuscript's extension
convention at every spatial face and at both time endpoints. -/
def IsSmoothHomotopy {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (F : M × UnitInterval → N) : Prop :=
  Continuous F ∧
  ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val),
    LocallyContDiffAlong (⊤ : ℕ∞)
      (fun z : {q : M × UnitInterval | q.1 ∈ c.source ∧ F q ∈ d.source} =>
        Fin.snoc (c z.val.1).val z.val.2.val)
      (fun z => (d (F z.val)).val)

/-- Genuine spatial differential and positive-time velocity. Their existence
is part of the operator theorem, rather than an extra hypothesis on F. -/
structure HomotopyDifferentials {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (F : M × UnitInterval → N) where
  spatial : ∀ t p, TangentSpace S p →ₗ[ℝ] TangentSpace T (F (p,t))
  spatial_correct : ∀ t p, IsDifferential S T (fun q => F (q,t)) p (spatial t p)
  velocity : ∀ p t, TangentSpace T (F (p,t))
  velocity_correct : ∀ p t (g : SmoothGerm T (F (p,t))) (r : N → ℝ),
    Germ.ofFun r = g.val →
    HasDerivWithinAt (fun s => r (F (p, intervalTime s))) ((velocity p t).val g)
      (Icc 0 1) t.val

section Forms
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- The horizontal part i_t^*F^*ω. -/
def alpha (D : HomotopyDifferentials S T F) {k : ℕ} (ω : Field T k)
    (t : UnitInterval) : Field S k :=
  FormPullbackData.pullbackField S T (fun p => F (p,t)) (D.spatial t) ω

/-- The dt-first component, obtained by inserting the time velocity in the
first slot before applying the spatial differential to the remaining slots. -/
def beta (C : CotangentBundle S) (D : HomotopyDifferentials S T F)
    {k : ℕ} (ω : Field T (k+1)) (t : UnitInterval) : Field S k :=
  fun p => (CartanData.evaluationEquiv C.tangent.fiberCoordinates p k).symm
    (((evaluate (TangentSpace T (F (p,t))) (k+1) (ω (F (p,t)))).curryLeft
      (D.velocity p t)).compLinearMap (D.spatial t p))

/-- Evaluation of the cylinder pullback on spatial-plus-time tangent vectors.
The factor (-1)^i expresses that dt is placed first. -/
def HasDtFirstDecomposition (C : CotangentBundle S)
    (D : HomotopyDifferentials S T F) {k : ℕ} (ω : Field T (k+1))
    (t : UnitInterval) (p : M) (β : Fiber (TangentSpace S p) k) : Prop :=
  ∀ z : Fin (k+1) → TangentSpace S p × ℝ,
    evaluate (TangentSpace T (F (p,t))) (k+1) (ω (F (p,t)))
      (fun i => D.spatial t p (z i).1 + (z i).2 • D.velocity p t) =
    evaluate (TangentSpace S p) (k+1) (alpha D ω t p) (fun i => (z i).1) +
    ∑ i : Fin (k+1), (-1 : ℝ)^i.val * (z i).2 *
      evaluate (TangentSpace S p) k β (fun j => (z (i.succAbove j)).1)

variable {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {A : CotangentBundle T} {E : ∀ k, FormBundle A k}

/-- Exact coefficientwise integral in every source chart; this also requires
integrability, so the totalized Bochner integral cannot supply a false witness. -/
def IsCoefficientIntegral (K : Calculus C B) (J : Calculus A E)
    (D : HomotopyDifferentials S T F)
    (op : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k) : Prop :=
  ∀ k (ω : J.forms (k+1)) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k),
    IntervalIntegrable
      (fun t => coefficients C k c hc (beta C D ω.val (intervalTime t)) p I)
      MeasureTheory.volume 0 1 ∧
    coefficients C k c hc (op k ω).val p I =
      ∫ t in (0 : ℝ)..1, coefficients C k c hc (beta C D ω.val (intervalTime t)) p I

/-- The full chain identity, with its distinct degree-zero formula. Smoothness
and real linearity are expressed by the domain and codomain of the linear maps. -/
def IsChainHomotopy (K : Calculus C B) (J : Calculus A E)
    (D : HomotopyDifferentials S T F)
    (op : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k) : Prop :=
  (∀ k (ω : J.forms (k+1)),
    (K.d k (op k ω)).val + (op (k+1) (J.d (k+1) ω)).val =
      alpha D ω.val finalTime - alpha D ω.val initialTime) ∧
  (∀ ω : J.forms 0, (op 0 (J.d 0 ω)).val =
    alpha D ω.val finalTime - alpha D ω.val initialTime)

end Forms
end SmoothManifolds.HomotopyData

namespace Specs.SmoothManifolds.DeRham.HomotopyOperator
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.DeRhamData
  _root_.SmoothManifolds.HomotopyData
universe u

/-- The original smooth operator obligation. No extra conditional premises are
part of this independent proposition. All degrees k+1 and degree zero occur;
negative-degree source components are the zero spaces of Calculus.FormsZ. -/
def homotopy_operatorType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (F : M × UnitInterval → N), IsSmoothHomotopy S T F →
    ∃ (D : HomotopyDifferentials S T F)
      (op : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k),
      IsCoefficientIntegral K J D op ∧ IsChainHomotopy K J D op ∧
      ∀ k (ω : J.forms (k+1)) (t : UnitInterval) (p : M),
        HasDtFirstDecomposition C D ω.val t p (beta C D ω.val t p) ∧
        ∀ β : Fiber (TangentSpace S p) k,
          HasDtFirstDecomposition C D ω.val t p β → β = beta C D ω.val t p

end Specs.SmoothManifolds.DeRham.HomotopyOperator
