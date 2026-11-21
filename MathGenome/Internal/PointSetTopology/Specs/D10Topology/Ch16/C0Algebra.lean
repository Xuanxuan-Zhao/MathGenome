import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.OnePointConstruction
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.SupNormAlgebras
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! Source interfaces for d10:16:c0 and d10:16:c0-extension.
`IsC0` is exactly continuity and compact positive norm-level sets.
The bundled library representation is related to it by the explicit theorems
below. `RCLike` includes both real and complex scalars. No noncompactness or
nonemptiness assumption is imposed, and the extra point is always retained. -/
noncomputable section
open Set Filter
open scoped Topology
universe u v w
namespace Specs.D10Topology.Ch16.C0Algebra

/-- The source definition, for raw functions. -/
def IsC0 {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (f : X → 𝕜) : Prop :=
  Continuous f ∧ ∀ ε : ℝ, 0 < ε → IsCompact {x | ε ≤ ‖f x‖}

abbrev C0 (X : Type u) (𝕜 : Type v) [TopologicalSpace X] [RCLike 𝕜] :=
  ZeroAtInftyContinuousMap X 𝕜
abbrev RealC0 (X : Type u) [TopologicalSpace X] := C0 X ℝ
abbrev ComplexC0 (X : Type u) [TopologicalSpace X] := C0 X ℂ

def zeroExtension {X : Type u} {𝕜 : Type v} [Zero 𝕜] (f : X → 𝕜) : OnePoint X → 𝕜 :=
  fun z => z.elim 0 f

def isC0Type := {X : Type u} → {𝕜 : Type v} → [TopologicalSpace X] → [RCLike 𝕜] →
  (X → 𝕜) → Prop
def c0Type := (X : Type u) → (𝕜 : Type v) → [TopologicalSpace X] → [RCLike 𝕜] → Type (max u v)
def realC0Type := (X : Type u) → [TopologicalSpace X] → Type u
def complexC0Type := (X : Type u) → [TopologicalSpace X] → Type u
def zeroExtensionType := {X : Type u} → {𝕜 : Type v} → [Zero 𝕜] →
  (X → 𝕜) → OnePoint X → 𝕜

def c0_iff_cocompact : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] (f : X → 𝕜),
    IsC0 f ↔ Continuous f ∧ Tendsto f (cocompact X) (𝓝 0)

def c0_real_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (f : X → ℝ),
    IsC0 f ↔ Continuous f ∧ ∀ ε : ℝ, 0 < ε → IsCompact {x | ε ≤ |f x|}

def c0_bundled_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] (f : X → 𝕜),
    IsC0 f ↔ ∃ g : C0 X 𝕜, (g : X → 𝕜) = f

def zeroExtension_values : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [Zero 𝕜] (f : X → 𝕜),
    zeroExtension f OnePoint.infty = 0 ∧ ∀ x, zeroExtension f (OnePoint.some x) = f x

def c0_iff_continuous_extension : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜],
    Specs.D10Topology.Ch11.LocalCompactConventions.LCH X → ∀ f : X → 𝕜,
    IsC0 f ↔ Continuous (zeroExtension f)

def c0_bounded : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] (f : X → 𝕜),
    IsC0 f → ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M

def c0_zero : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜], IsC0 (0 : X → 𝕜)
def c0_add : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] (f g : X → 𝕜),
    IsC0 f → IsC0 g → IsC0 (f + g)
def c0_mul : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] (f g : X → 𝕜),
    IsC0 f → IsC0 g → IsC0 (f * g)
def c0_smul : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] (c : 𝕜) (f : X → 𝕜),
    IsC0 f → IsC0 (c • f)
def c0_conjugate : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (f : X → ℂ), IsC0 f → IsC0 (star f)

def c0_uniform_limit : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] {I : Type w}
    (l : Filter I) [l.NeBot] (F : I → X → 𝕜) (f : X → 𝕜),
    (∀ i, IsC0 (F i)) → TendstoUniformly F f l → IsC0 f

def c0_compact_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] [CompactSpace X]
    (f : X → 𝕜), IsC0 f ↔ Continuous f

def c0_empty : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜] [IsEmpty X]
    (f : X → 𝕜), IsC0 f

/-- Carrier of a nonunital function algebra, without a hypothesis containing constants. -/
def c0_algebra : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜],
    ∃ A : Specs.D10Topology.Ch16.SupNormAlgebras.FunctionSubalgebra X 𝕜,
      ∀ f : C(X, 𝕜), f ∈ A ↔ IsC0 (f : X → 𝕜)

/-- The canonical zero-extension homomorphism. Continuity here follows
from the library's one-point mapping criterion, independently of the candidate. -/
def c0ExtensionHom {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (hX : Specs.D10Topology.Ch11.LocalCompactConventions.LCH X) :
    C0 X 𝕜 →ₙₐ[𝕜] C(OnePoint X, 𝕜) where
  toFun f := OnePoint.continuousMapMk f.toContinuousMap 0 (by
    let : T2Space X := hX.2
    simpa only [coclosedCompact_eq_cocompact,
      ZeroAtInftyContinuousMap.coe_toContinuousMap] using zero_at_infty f)
  map_zero' := by
    ext z
    induction z using OnePoint.rec <;> rfl
  map_add' f g := by
    ext z
    induction z using OnePoint.rec with
    | infty => exact (zero_add _).symm
    | coe x => rfl
  map_mul' f g := by
    ext z
    induction z using OnePoint.rec with
    | infty => exact (zero_mul _).symm
    | coe x => rfl
  map_smul' c f := by
    ext z
    induction z using OnePoint.rec with
    | infty => exact (smul_zero c).symm
    | coe x => rfl

def c0ExtensionHomType := {X : Type u} → {𝕜 : Type v} → [TopologicalSpace X] → [RCLike 𝕜] →
  Specs.D10Topology.Ch11.LocalCompactConventions.LCH X →
  C0 X 𝕜 →ₙₐ[𝕜] C(OnePoint X, 𝕜)

def zeroExtension_conjugate : Prop :=
  ∀ {X : Type u} (f : X → ℂ), zeroExtension (star f) = star (zeroExtension f)

/-- Bundled zero extension is an injective algebra map onto exactly the
continuous functions on the source one-point space with value zero at infinity.
The norm statement uses the untruncated supremum norm, also on empty X. -/
def c0_extension_algebra_bridge : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜],
    Specs.D10Topology.Ch11.LocalCompactConventions.LCH X →
    ∃ E : C0 X 𝕜 →ₙₐ[𝕜] C(OnePoint X, 𝕜),
      (∀ f, (E f : OnePoint X → 𝕜) = zeroExtension (f : X → 𝕜)) ∧
      Function.Injective E ∧
      (∀ g : C(OnePoint X, 𝕜), g ∈ range E ↔ g OnePoint.infty = 0) ∧
      ∀ f, ‖E f‖ = ‖f‖

/-- Uniform convergence is preserved and reflected by zero extension. -/
def zeroExtension_uniform_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type v} [RCLike 𝕜] {I : Type w}
    (l : Filter I) (F : I → X → 𝕜) (f : X → 𝕜),
    TendstoUniformly (fun i => zeroExtension (F i)) (zeroExtension f) l ↔
      TendstoUniformly F f l

end Specs.D10Topology.Ch16.C0Algebra
