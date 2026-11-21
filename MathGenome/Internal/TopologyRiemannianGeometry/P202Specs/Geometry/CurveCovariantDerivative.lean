import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PiecewiseCurves
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Covariant differentiation of C¹ fields in the original bundle fibers.
Within derivatives are used at endpoints. Uniqueness is asserted only on
parameter germs with unique differentiation; no derivative is determined by
the trace on an isolated singleton. No extension into the manifold is used. -/
set_option autoImplicit false
namespace P202.CurveConnectionData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.ConnectionData P202.MetricData
open Set Filter
open scoped Topology
universe u v w
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]

/-- An intrinsic within velocity, specified in one actual chart. -/
def HasVelocityWithinAt (S : SmoothManifold n a M) (c : ℝ → M)
    (J : Set ℝ) (t : ℝ) (V : TangentSpace S (c t)) : Prop :=
  ContinuousWithinAt c J t ∧ ∃ e, ∃ he : e ∈ S.smoothStructure.val,
    ∃ hp : c t ∈ e.source,
      HasDerivWithinAt (fun s => (e (c s)).val)
        ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp V) J t

/-- Coefficients of an arbitrary actual field along a curve, with irrelevant
zero values outside the open frame domain. -/
noncomputable def coefficientsAlong {B : SmoothVectorBundle S r ι E}
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) : Euclidean r := by
  classical
  exact if h : c t ∈ U then (b.basis ⟨c t, h⟩).equivFun (f t) else 0

/-- An actual field represented by the local row-frame expansion e(γ(t))v(t).
Its zero values outside the frame domain do not affect the local assertion. -/
noncomputable def frameFieldAlong {B : SmoothVectorBundle S r ι E}
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (v : ℝ → Euclidean r) (t : ℝ) : E (c t) := by
  classical
  exact if h : c t ∈ U then (b.basis ⟨c t, h⟩).equivFun.symm (v t) else 0

/-- The displayed formula e(v' + Γ(γ')v), an element of E_(γ(t)). -/
noncomputable def frameDerivative {B : SmoothVectorBundle S r ι E}
    (C : Connection B) {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) (hp : c t ∈ U)
    (V : TangentSpace S (c t)) (v' : Euclidean r) : E (c t) :=
  (b.basis ⟨c t, hp⟩).equivFun.symm
    (v' + (connectionMatrix C b ⟨c t, hp⟩ V).mulVec (coefficientsAlong b c f t))

/-- A field is C¹ on a parameter set if its coefficients in a local smooth
frame have ambient Euclidean C¹ extensions at each point of that set. -/
def C1FieldOn {B : SmoothVectorBundle S r ι E}
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ (U : Set M) (hU : IsOpen U) (b : LocalFrame B U hU),
    c t ∈ U ∧ ∃ v : ℝ → Euclidean r, ContDiffAt ℝ 1 v t ∧
      coefficientsAlong b c f t = v t ∧ coefficientsAlong b c f =ᶠ[𝓝[J] t] v

/-- The local construction. Its independence of the witness frame and of
coordinate charts is a theorem, and is not part of this definition. -/
def HasCovariantDerivativeWithinAt {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t))
    (J : Set ℝ) (t : ℝ) (D : E (c t)) : Prop :=
  ∃ V : TangentSpace S (c t), HasVelocityWithinAt S c J t V ∧
    ∃ (U : Set M) (hU : IsOpen U) (b : LocalFrame B U hU) (hp : c t ∈ U)
      (v' : Euclidean r), HasDerivWithinAt (coefficientsAlong b c f) v' J t ∧
        D = frameDerivative C b c f t hp V v'

/-- The derivative as an actual field along c, zero where there is no local
within derivative. On C¹ domains it is characterized by the local formula. -/
noncomputable def covariantDerivativeWithin {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t))
    (J : Set ℝ) (t : ℝ) : E (c t) := by
  classical
  exact if h : ∃ D, HasCovariantDerivativeWithinAt C c f J t D then
    Classical.choose h else 0

abbrev HasCovariantDerivativeAt {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) (D : E (c t)) :=
  HasCovariantDerivativeWithinAt C c f univ t D

noncomputable abbrev covariantDerivative {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) :=
  covariantDerivativeWithin C c f univ t

end P202.CurveConnectionData

namespace P202Specs.Geometry.CurveCovariantDerivative
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.MapData SmoothManifolds.FrameData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
open Set Filter
open scoped Topology
universe u v w

def HasVelocityWithinAtType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n a M) (c : ℝ → M)
    (J : Set ℝ) (t : ℝ) (V : TangentSpace S (c t)), Prop

noncomputable def HasVelocityWithinAtValue : HasVelocityWithinAtType := @P202.CurveConnectionData.HasVelocityWithinAt

def coefficientsAlongType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ), Euclidean r

noncomputable def coefficientsAlongValue : coefficientsAlongType := @P202.CurveConnectionData.coefficientsAlong

def frameFieldAlongType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (v : ℝ → Euclidean r) (t : ℝ), E (c t)

noncomputable def frameFieldAlongValue : frameFieldAlongType := @P202.CurveConnectionData.frameFieldAlong

def frameDerivativeType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    (C : Connection B) {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) (hp : c t ∈ U)
    (V : TangentSpace S (c t)) (v' : Euclidean r), E (c t)

noncomputable def frameDerivativeValue : frameDerivativeType := @P202.CurveConnectionData.frameDerivative

def C1FieldOnType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    (c : ℝ → M) (f : (t : ℝ) → E (c t)) (J : Set ℝ), Prop

noncomputable def C1FieldOnValue : C1FieldOnType := @P202.CurveConnectionData.C1FieldOn

def HasCovariantDerivativeWithinAtType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t))
    (J : Set ℝ) (t : ℝ) (D : E (c t)), Prop

noncomputable def HasCovariantDerivativeWithinAtValue : HasCovariantDerivativeWithinAtType := @P202.CurveConnectionData.HasCovariantDerivativeWithinAt

def covariantDerivativeWithinType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t))
    (J : Set ℝ) (t : ℝ), E (c t)

noncomputable def covariantDerivativeWithinValue : covariantDerivativeWithinType := @P202.CurveConnectionData.covariantDerivativeWithin

def HasCovariantDerivativeAtType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ) (D : E (c t)), Prop

noncomputable def HasCovariantDerivativeAtValue : HasCovariantDerivativeAtType := @P202.CurveConnectionData.HasCovariantDerivativeAt

def covariantDerivativeType :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)],
  ∀ {B : SmoothVectorBundle S r ι E}
    (C : Connection B) (c : ℝ → M) (f : (t : ℝ) → E (c t)) (t : ℝ), E (c t)

noncomputable def covariantDerivativeValue : covariantDerivativeType := @P202.CurveConnectionData.covariantDerivative

def frameDerivative_independentType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ {U W : Set M} {hU : IsOpen U} {hW : IsOpen W}
    (C : Connection B) (b : LocalFrame B U hU) (d : LocalFrame B W hW)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) (hp : c t ∈ U) (hq : c t ∈ W)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    {v' w' : Euclidean r}
    (hv : HasDerivWithinAt (coefficientsAlong b c f) v' J t)
    (hw : HasDerivWithinAt (coefficientsAlong d c f) w' J t),
    frameDerivative C b c f t hp V v' = frameDerivative C d c f t hq V w'

def covariantDerivative_uniqueType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D F : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    (hF : HasCovariantDerivativeWithinAt C c f J t F),
    D = F

def exists_coefficients_derivType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (hp : c t ∈ U),
    ∃ v', HasDerivWithinAt (coefficientsAlong b c f) v' J t

def local_formulaType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V)
    {v' : Euclidean r} (hv : HasDerivWithinAt (coefficientsAlong b c f) v' J t),
    D = frameDerivative C b c f t hp V v'

def exists_covariantDerivativeType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hc : P202.CurveData.CoordinateC1On S c J) (hc' : ContinuousOn c J)
    (hf : C1FieldOn (B := B) c f J),
    ∃ D, HasCovariantDerivativeWithinAt C c f J t D

def covariantDerivativeWithin_specType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (hex : ∃ D, HasCovariantDerivativeWithinAt C c f J t D),
    HasCovariantDerivativeWithinAt C c f J t (covariantDerivativeWithin C c f J t)

def covariantDerivativeWithin_eqType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D),
    covariantDerivativeWithin C c f J t = D

def segment_derivativeType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {l q : ℝ} (hlq : l < q)
    (hc : P202.CurveData.CoordinateC1On S c (Icc l q)) (hc' : ContinuousOn c (Icc l q))
    (hf : C1FieldOn (B := B) c f (Icc l q)) {t : ℝ} (ht : t ∈ Icc l q),
    HasCovariantDerivativeWithinAt C c f (Icc l q) t
      (covariantDerivativeWithin C c f (Icc l q) t) ∧
    ∀ D, HasCovariantDerivativeWithinAt C c f (Icc l q) t D →
      D = covariantDerivativeWithin C c f (Icc l q) t

def derivative_addType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f g : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D F : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    (hF : HasCovariantDerivativeWithinAt C c g J t F),
    HasCovariantDerivativeWithinAt C c (fun t => f t + g t) J t (D + F)

def derivative_smulType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    {D : E (c t)} (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {k : ℝ → ℝ} {k' : ℝ} (hk : HasDerivWithinAt k k' J t),
    HasCovariantDerivativeWithinAt C c (fun t => k t • f t) J t
      (k' • f t + k t • D)

def derivative_reparamType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ}
    {I J : Set ℝ} {s : ℝ} {k : ℝ} {D : E (c (φ s))}
    (hD : HasCovariantDerivativeWithinAt C c f J (φ s) D)
    (hφ : HasDerivWithinAt φ k I s) (hmaps : MapsTo φ I J),
    HasCovariantDerivativeWithinAt C (c ∘ φ) (fun s => f (φ s)) I s (k • D)

def covariantDerivativeWithin_reparamType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ}
    {I J : Set ℝ} {s : ℝ} {k : ℝ}
    (hs : s ∈ I) (hI : UniqueDiffWithinAt ℝ I s)
    (ht : φ s ∈ J) (hJ : UniqueDiffWithinAt ℝ J (φ s))
    {D : E (c (φ s))} (hD : HasCovariantDerivativeWithinAt C c f J (φ s) D)
    (hφ : HasDerivWithinAt φ k I s) (hmaps : MapsTo φ I J),
    covariantDerivativeWithin C (c ∘ φ) (fun s => f (φ s)) I s =
      k • covariantDerivativeWithin C c f J (φ s)

def ordinary_reparamType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B)
    {c : ℝ → M} {f : (t : ℝ) → E (c t)} {φ : ℝ → ℝ}
    {s k : ℝ} {D : E (c (φ s))}
    (hD : HasCovariantDerivativeAt C c f (φ s) D) (hφ : HasDerivAt φ k s),
    HasCovariantDerivativeAt C (c ∘ φ) (fun s => f (φ s)) s (k • D)

def derivative_local_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU) (z : LocalSection B U hU)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hp : c t ∈ U)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V),
    HasCovariantDerivativeWithinAt C c
      (fun s => SmoothManifolds.SectionExtension.totalSection z.val (c s)) J t
      (pointDerivative C (SmoothManifolds.SectionExtension.totalSection z.val) (c t) V)

def derivative_sectionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) (z : Section B)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    {V : TangentSpace S (c t)} (hV : HasVelocityWithinAt S c J t V),
    HasCovariantDerivativeWithinAt C c (fun s => z.val (c s)) J t
      (pointDerivative C z.val (c t) V)

def derivative_section_fieldType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) (z : Section B) (X : Field S)
    {c : ℝ → M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hV : HasVelocityWithinAt S c J t (X.val (c t))),
    HasCovariantDerivativeWithinAt C c (fun s => z.val (c s)) J t
      ((C.cov X z).val (c t))

def derivative_frame_expansionType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame B U hU)
    {c : ℝ → M} {v : ℝ → Euclidean r} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hp : c t ∈ U) {V : TangentSpace S (c t)}
    (hV : HasVelocityWithinAt S c J t V) {v' : Euclidean r}
    (hv : HasDerivWithinAt v v' J t),
    HasCovariantDerivativeWithinAt C c (frameFieldAlong b c v) J t
      ((b.basis ⟨c t, hp⟩).equivFun.symm
        (v' + (connectionMatrix C b ⟨c t, hp⟩ V).mulVec (v t)))

def derivative_const_smulType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ} {D : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D) (k : ℝ),
    HasCovariantDerivativeWithinAt C c (fun t => k • f t) J t (k • D)

def covariantDerivativeWithin_addType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f g : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D F : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    (hF : HasCovariantDerivativeWithinAt C c g J t F),
    covariantDerivativeWithin C c (fun t => f t + g t) J t =
      covariantDerivativeWithin C c f J t + covariantDerivativeWithin C c g J t

def covariantDerivativeWithin_smulType : Prop :=
  ∀ {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    {B : SmoothVectorBundle S r ι E},
  ∀ (C : Connection B) {c : ℝ → M}
    {f : (t : ℝ) → E (c t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {D : E (c t)}
    (hD : HasCovariantDerivativeWithinAt C c f J t D)
    {k : ℝ → ℝ} {k' : ℝ} (hk : HasDerivWithinAt k k' J t),
    covariantDerivativeWithin C c (fun t => k t • f t) J t =
      k' • f t + k t • covariantDerivativeWithin C c f J t

end P202Specs.Geometry.CurveCovariantDerivative
