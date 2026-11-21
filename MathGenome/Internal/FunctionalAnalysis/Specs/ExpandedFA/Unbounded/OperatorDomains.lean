import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
Domain-carrying operators for Part III, paper.tex 13489–13497 and its subsequent
uses of graphs, closures, graph norms, cores and resolvents. These definitions
make no density or closedness assumption on an arbitrary operator.

The canonical representation is Mathlib's partial linear map. In particular its
ordinary equality includes the domain. `GraphDomain A` is a separate type with
the sum graph norm; the subtype `A.domain` retains the ambient norm.
-/

noncomputable section

namespace ExpandedFA.Unbounded

/-- A linear operator includes a linear subspace domain and a map on that domain.
The field may be real or complex; the algebraic representation works over any ring. -/
abbrev Operator (𝕜 : Type*) [Ring 𝕜] (X Y : Type*)
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y] := X →ₗ.[𝕜] Y

section Normed
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A copy of the operator domain, to be equipped with its graph norm. -/
def GraphDomain (A : Operator 𝕜 X Y) : Type _ := A.domain

namespace GraphDomain
variable (A : Operator 𝕜 X Y)

instance : AddCommGroup (GraphDomain A) := inferInstanceAs (AddCommGroup A.domain)
instance : Module 𝕜 (GraphDomain A) := inferInstanceAs (Module 𝕜 A.domain)

/-- The domain coordinate; no change is made to the underlying vectors. -/
def toDomain (x : GraphDomain A) : A.domain := x

/-- The sum graph norm, as an additive group norm. -/
def addGroupNorm : AddGroupNorm (GraphDomain A) where
  toFun x := ‖(toDomain A x : X)‖ + ‖A (toDomain A x)‖
  map_zero' := by
    change ‖(0 : X)‖ + ‖A (0 : A.domain)‖ = 0
    rw [A.map_zero]
    simp
  add_le' x y := by
    change ‖(toDomain A x : X) + (toDomain A y : X)‖ +
      ‖A (toDomain A x + toDomain A y)‖ ≤ _
    rw [A.map_add]
    exact (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans_eq
      (by ac_rfl)
  neg' x := by
    change ‖-(toDomain A x : X)‖ + ‖A (-toDomain A x)‖ = _
    rw [A.map_neg, norm_neg, norm_neg]
  eq_zero_of_map_eq_zero' x hx := by
    have h : ‖(toDomain A x : X)‖ = 0 :=
      (add_eq_zero_iff_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp hx |>.1
    exact Subtype.ext (norm_eq_zero.mp h)

instance : NormedAddCommGroup (GraphDomain A) := (addGroupNorm A).toNormedAddCommGroup
instance : NormedSpace 𝕜 (GraphDomain A) where
  norm_smul_le c x := by
    show (addGroupNorm A) (c • x) ≤ ‖c‖ * (addGroupNorm A) x
    change ‖c • (toDomain A x : X)‖ + ‖A (c • toDomain A x)‖ ≤
      ‖c‖ * (‖(toDomain A x : X)‖ + ‖A (toDomain A x)‖)
    rw [A.map_smul, norm_smul, norm_smul, mul_add]

@[simp] theorem norm_eq (x : GraphDomain A) :
    ‖x‖ = ‖(toDomain A x : X)‖ + ‖A (toDomain A x)‖ := rfl

end GraphDomain

/-- Data certifying that ζI − A has a bounded, everywhere defined inverse.
The inverse is bounded in the ambient norm, lands in D(A), and satisfies both
inverse identities. Existence of these data is a definition, not an assumption
attached to every operator. -/
structure ResolventInverse (A : Operator 𝕜 X X) (ζ : 𝕜) where
  inverse : X →L[𝕜] X
  mem_domain : ∀ y, inverse y ∈ A.domain
  right_inverse : ∀ y, ζ • inverse y - A ⟨inverse y, mem_domain y⟩ = y
  left_inverse : ∀ x : A.domain, inverse (ζ • (x : X) - A x) = (x : X)

end Normed

namespace ResolventInverse
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {A : Operator 𝕜 X X} {ζ : 𝕜}

/-- The inverse viewed as a linear map into the graph-norm domain. -/
def graphLinear (R : ResolventInverse A ζ) : X →ₗ[𝕜] GraphDomain A where
  toFun y := (⟨R.inverse y, R.mem_domain y⟩ : A.domain)
  map_add' x y := by
    apply Subtype.ext
    exact R.inverse.map_add x y
  map_smul' c x := by
    apply Subtype.ext
    exact R.inverse.map_smul c x

/-- Both graph coordinates are bounded, using A R = ζ R − I. -/
theorem graphLinear_bound (R : ResolventInverse A ζ) (y : X) :
    ‖R.graphLinear y‖ ≤ ((1 + ‖ζ‖) * ‖R.inverse‖ + 1) * ‖y‖ := by
  have hA : A ⟨R.inverse y, R.mem_domain y⟩ = ζ • R.inverse y - y := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp (R.right_inverse y)).symm
  change ‖R.inverse y‖ + ‖A ⟨R.inverse y, R.mem_domain y⟩‖ ≤ _
  calc
    _ ≤ ‖R.inverse y‖ + (‖ζ‖ * ‖R.inverse y‖ + ‖y‖) := by
      rw [hA]
      exact add_le_add le_rfl (by
        simpa only [norm_smul] using norm_sub_le (ζ • R.inverse y) y)
    _ = (1 + ‖ζ‖) * ‖R.inverse y‖ + ‖y‖ := by
      rw [add_mul, one_mul, add_assoc]
    _ ≤ (1 + ‖ζ‖) * (‖R.inverse‖ * ‖y‖) + ‖y‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (R.inverse.le_opNorm y)
          (add_nonneg zero_le_one (norm_nonneg ζ))) le_rfl
    _ = ((1 + ‖ζ‖) * ‖R.inverse‖ + 1) * ‖y‖ := by
      simp only [add_mul, mul_assoc, one_mul]

/-- The inverse is bounded also for the sum graph norm. -/
def toGraphDomain (R : ResolventInverse A ζ) : X →L[𝕜] GraphDomain A :=
  R.graphLinear.mkContinuous _ R.graphLinear_bound

end ResolventInverse

namespace OperatorDomainsSpec

section Algebra
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
  [AddCommGroup Z] [Module 𝕜 Z]

def MakeType := (D : Submodule 𝕜 X) → (D →ₗ[𝕜] Y) → Operator 𝕜 X Y
def makeValue : MakeType (𝕜 := 𝕜) (X := X) (Y := Y) := fun D f => ⟨D, f⟩

def DomainType := Operator 𝕜 X Y → Submodule 𝕜 X
def domainValue : DomainType (𝕜 := 𝕜) (X := X) (Y := Y) := LinearPMap.domain

def InclusionType := Operator 𝕜 X Y → Operator 𝕜 X Y → Prop
def inclusionValue : InclusionType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A B => A ≤ B

def EqualityType := Operator 𝕜 X Y → Operator 𝕜 X Y → Prop
def equalityValue : EqualityType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A B => A = B

def GraphType := Operator 𝕜 X Y → Submodule 𝕜 (X × Y)
def graphValue : GraphType (𝕜 := 𝕜) (X := X) (Y := Y) := LinearPMap.graph

def KernelType := Operator 𝕜 X Y → Submodule 𝕜 X
def kernelValue : KernelType (𝕜 := 𝕜) (X := X) (Y := Y) := LinearPMap.ker

def RangeType := Operator 𝕜 X Y → Submodule 𝕜 Y
def rangeValue : RangeType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A => A.toFun.range

def RestrictType := Operator 𝕜 X Y → Submodule 𝕜 X → Operator 𝕜 X Y
def restrictValue : RestrictType (𝕜 := 𝕜) (X := X) (Y := Y) := LinearPMap.domRestrict

def SumType := Operator 𝕜 X Y → Operator 𝕜 X Y → Operator 𝕜 X Y
def sumValue : SumType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A B => A + B

def ScalarType := 𝕜 → Operator 𝕜 X Y → Operator 𝕜 X Y
def scalarValue : ScalarType (𝕜 := 𝕜) (X := X) (Y := Y) := fun c A => c • A

/-- The product AB is defined exactly where B is defined and Bx belongs to D(A). -/
def ProductDomainType := Operator 𝕜 Y Z → Operator 𝕜 X Y → Submodule 𝕜 X
def productDomainValue : ProductDomainType (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) :=
  fun A B =>
  { carrier := {x | ∃ hx : x ∈ B.domain, B ⟨x, hx⟩ ∈ A.domain}
    zero_mem' := ⟨B.domain.zero_mem, by
      change B (0 : B.domain) ∈ A.domain
      rw [B.map_zero]
      exact A.domain.zero_mem⟩
    add_mem' := by
      rintro x y ⟨hx, hAx⟩ ⟨hy, hAy⟩
      refine ⟨B.domain.add_mem hx hy, ?_⟩
      change B ((⟨x, hx⟩ : B.domain) + ⟨y, hy⟩) ∈ A.domain
      rw [B.map_add]
      exact A.domain.add_mem hAx hAy
    smul_mem' := by
      rintro c x ⟨hx, hAx⟩
      refine ⟨B.domain.smul_mem c hx, ?_⟩
      change B (c • (⟨x, hx⟩ : B.domain)) ∈ A.domain
      rw [B.map_smul]
      exact A.domain.smul_mem c hAx }

def ProductType := Operator 𝕜 Y Z → Operator 𝕜 X Y → Operator 𝕜 X Z
def productValue : ProductType (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) := fun A B =>
  { domain := productDomainValue A B
    toFun :=
      { toFun := fun x => A ⟨B ⟨x, x.2.choose⟩, x.2.choose_spec⟩
        map_add' := by
          intro x y
          rw [← A.map_add]
          congr 1
          apply Subtype.ext
          change B ((⟨x, x.2.choose⟩ : B.domain) + ⟨y, y.2.choose⟩) = _
          exact B.map_add _ _
        map_smul' := by
          intro c x
          change A _ = c • A _
          rw [← A.map_smul]
          congr 1
          apply Subtype.ext
          change B (c • (⟨x, x.2.choose⟩ : B.domain)) = _
          exact B.map_smul _ _ } }

def IdentityType := Operator 𝕜 X X
def identityValue : IdentityType (𝕜 := 𝕜) (X := X) := (LinearMap.id : X →ₗ[𝕜] X).toPMap ⊤

def PowerType := Operator 𝕜 X X → ℕ → Operator 𝕜 X X
def powerValue : PowerType (𝕜 := 𝕜) (X := X) := fun A n =>
  Nat.rec identityValue (fun _ B => productValue A B) n

/-- ζI − A on exactly D(A). -/
def ShiftType := 𝕜 → Operator 𝕜 X X → Operator 𝕜 X X
def shiftValue : ShiftType (𝕜 := 𝕜) (X := X) := fun ζ A =>
  { domain := A.domain
    toFun := ζ • A.domain.subtype - A.toFun }

end Algebra

section Normed
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def DenseType := Operator 𝕜 X Y → Prop
def denseValue : DenseType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A => Dense (A.domain : Set X)

def ClosedType := Operator 𝕜 X Y → Prop
def closedValue : ClosedType (𝕜 := 𝕜) (X := X) (Y := Y) := LinearPMap.IsClosed

def ClosableType := Operator 𝕜 X Y → Prop
def closableValue : ClosableType (𝕜 := 𝕜) (X := X) (Y := Y) := LinearPMap.IsClosable

/-- Closure is used only for a closable operator, avoiding an assertion about
Mathlib's arbitrary fallback value when the graph closure is multivalued. -/
def ClosureType := (A : Operator 𝕜 X Y) → A.IsClosable → Operator 𝕜 X Y
def closureValue : ClosureType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A _ => A.closure

def GraphNormType := (A : Operator 𝕜 X Y) → A.domain → ℝ
def graphNormValue : GraphNormType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A x => ‖(x : X)‖ + ‖A x‖

/-- A core is a subspace of D(A) whose restricted graph is dense in the graph
of A. Equality of the ambient graph closures expresses that density even if A
is not closed; for closed A it equals G(A). -/
def CoreType := Operator 𝕜 X Y → Submodule 𝕜 X → Prop
def coreValue : CoreType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A S =>
  S ≤ A.domain ∧ (A.domRestrict S).graph.topologicalClosure = A.graph.topologicalClosure

def ResolventSetType := Operator 𝕜 X X → Set 𝕜
def resolventSetValue : ResolventSetType (𝕜 := 𝕜) (X := X) := fun A =>
  {ζ | Nonempty (ResolventInverse A ζ)}

/-- The resolvent is totalized by zero off ρ(A). All inverse assertions below
require membership in ρ(A). No existence of a resolvent point is presumed. -/
def ResolventType := 𝕜 → Operator 𝕜 X X → (X →L[𝕜] X)
open scoped Classical in
def resolventValue : ResolventType (𝕜 := 𝕜) (X := X) := fun ζ A =>
  if h : Nonempty (ResolventInverse A ζ) then h.some.inverse else 0

/-- The same everywhere defined bounded inverse, with codomain D(A) equipped
with its ambient subspace norm. -/
def ResolventToDomainType := (ζ : 𝕜) → (A : Operator 𝕜 X X) →
  Nonempty (ResolventInverse A ζ) → (X →L[𝕜] A.domain)
def resolventToDomainValue : ResolventToDomainType (𝕜 := 𝕜) (X := X) := fun _ _ h =>
  h.some.inverse.codRestrict _ h.some.mem_domain

def ResolventToGraphDomainType := (ζ : 𝕜) → (A : Operator 𝕜 X X) →
  Nonempty (ResolventInverse A ζ) → (X →L[𝕜] GraphDomain A)
def resolventToGraphDomainValue : ResolventToGraphDomainType (𝕜 := 𝕜) (X := X) :=
  fun _ _ h => h.some.toGraphDomain

end Normed
section AlgebraLaws
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
  [AddCommGroup Z] [Module 𝕜 Z]

def InclusionLaw : Prop := ∀ A B : Operator 𝕜 X Y,
  inclusionValue A B ↔ A.domain ≤ B.domain ∧
    ∀ (x : A.domain) (y : B.domain), (x : X) = y → A x = B y

def EqualityLaw : Prop := ∀ A B : Operator 𝕜 X Y,
  equalityValue A B ↔ A.domain = B.domain ∧
    ∀ (x : X) (hx : x ∈ A.domain) (hy : x ∈ B.domain), A ⟨x, hx⟩ = B ⟨x, hy⟩

def GraphLaw : Prop := ∀ (A : Operator 𝕜 X Y) (z : X × Y),
  z ∈ graphValue A ↔ ∃ hx : z.1 ∈ A.domain, A ⟨z.1, hx⟩ = z.2

def KernelLaw : Prop := ∀ (A : Operator 𝕜 X Y) (x : X),
  x ∈ kernelValue A ↔ ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = 0

def RangeLaw : Prop := ∀ (A : Operator 𝕜 X Y) (y : Y),
  y ∈ rangeValue A ↔ ∃ x : A.domain, A x = y

def SumDomainLaw : Prop := ∀ A B : Operator 𝕜 X Y,
  (sumValue A B).domain = A.domain ⊓ B.domain

def SumEvaluationLaw : Prop := ∀ (A B : Operator 𝕜 X Y) (x : (sumValue A B).domain),
  sumValue A B x = A ⟨x, x.2.1⟩ + B ⟨x, x.2.2⟩

def ProductDomainLaw : Prop := ∀ (A : Operator 𝕜 Y Z) (B : Operator 𝕜 X Y) (x : X),
  x ∈ (productValue A B).domain ↔ ∃ hx : x ∈ B.domain, B ⟨x, hx⟩ ∈ A.domain

def ProductEvaluationLaw : Prop := ∀ (A : Operator 𝕜 Y Z) (B : Operator 𝕜 X Y)
    (x : B.domain) (hx : B x ∈ A.domain),
  productValue A B ⟨x, ⟨x.2, hx⟩⟩ = A ⟨B x, hx⟩

def PowerZeroLaw : Prop := ∀ A : Operator 𝕜 X X, powerValue A 0 = identityValue

def PowerSuccessorLaw : Prop := ∀ (A : Operator 𝕜 X X) (n : ℕ),
  powerValue A (n + 1) = productValue A (powerValue A n)

def ShiftLaw : Prop := ∀ (ζ : 𝕜) (A : Operator 𝕜 X X),
  (shiftValue ζ A).domain = A.domain ∧
    ∀ x : A.domain, shiftValue ζ A x = ζ • (x : X) - A x

end AlgebraLaws

section NormedLaws
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def ClosedLaw : Prop := ∀ A : Operator 𝕜 X Y,
  closedValue A ↔ _root_.IsClosed (A.graph : Set (X × Y))

def ClosableLaw : Prop := ∀ A : Operator 𝕜 X Y,
  closableValue A ↔ ∃ B : Operator 𝕜 X Y, B.IsClosed ∧ A ≤ B

def ClosureLaw : Prop := ∀ (A : Operator 𝕜 X Y) (h : A.IsClosable),
  (closureValue A h).graph = A.graph.topologicalClosure ∧
    (closureValue A h).IsClosed ∧ A ≤ closureValue A h

def CoreClosedLaw : Prop := ∀ (A : Operator 𝕜 X Y) (_h : A.IsClosed) (S : Submodule 𝕜 X),
  coreValue A S ↔ S ≤ A.domain ∧ (A.domRestrict S).graph.topologicalClosure = A.graph

def GraphNormLaw : Prop := ∀ (A : Operator 𝕜 X Y) (x : GraphDomain A),
  ‖x‖ = graphNormValue A (GraphDomain.toDomain A x)

def GraphNormBoundsLaw : Prop := ∀ (A : Operator 𝕜 X Y) (x : A.domain),
  ‖(x : X)‖ ≤ graphNormValue A x ∧ ‖A x‖ ≤ graphNormValue A x

def ResolventDomainLaw : Prop := ∀ (ζ : 𝕜) (A : Operator 𝕜 X X)
    (h : Nonempty (ResolventInverse A ζ)) (y : X),
  (resolventToDomainValue ζ A h y : X) = resolventValue ζ A y

def ResolventRightLaw : Prop := ∀ (ζ : 𝕜) (A : Operator 𝕜 X X)
    (h : Nonempty (ResolventInverse A ζ)) (y : X),
  ζ • (resolventToDomainValue ζ A h y : X) - A (resolventToDomainValue ζ A h y) = y

def ResolventLeftLaw : Prop := ∀ (ζ : 𝕜) (A : Operator 𝕜 X X)
    (h : Nonempty (ResolventInverse A ζ)) (x : A.domain),
  (resolventToDomainValue ζ A h (ζ • (x : X) - A x) : X) = (x : X)

def ResolventUniqueLaw : Prop := ∀ (ζ : 𝕜) (A : Operator 𝕜 X X)
    (R S : ResolventInverse A ζ), R.inverse = S.inverse

end NormedLaws


/-! Fully quantified expected declaration types for native binding checks.
Their universe parameters intentionally occur under one quantified type. -/
set_option linter.checkUnivs false

def MakeTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    MakeType (𝕜 := 𝕜) (X := X) (Y := Y)

def DomainTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    DomainType (𝕜 := 𝕜) (X := X) (Y := Y)

def InclusionTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    InclusionType (𝕜 := 𝕜) (X := X) (Y := Y)

def EqualityTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    EqualityType (𝕜 := 𝕜) (X := X) (Y := Y)

def GraphTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    GraphType (𝕜 := 𝕜) (X := X) (Y := Y)

def KernelTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    KernelType (𝕜 := 𝕜) (X := X) (Y := Y)

def RangeTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    RangeType (𝕜 := 𝕜) (X := X) (Y := Y)

def RestrictTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    RestrictType (𝕜 := 𝕜) (X := X) (Y := Y)

def SumTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    SumType (𝕜 := 𝕜) (X := X) (Y := Y)

def ScalarTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    ScalarType (𝕜 := 𝕜) (X := X) (Y := Y)

def ProductDomainTypeExpected :=
  ∀ {𝕜 X Y Z : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z],
    ProductDomainType (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z)

def ProductTypeExpected :=
  ∀ {𝕜 X Y Z : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z],
    ProductType (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z)

def IdentityTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X],
    IdentityType (𝕜 := 𝕜) (X := X)

def PowerTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X],
    PowerType (𝕜 := 𝕜) (X := X)

def ShiftTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X],
    ShiftType (𝕜 := 𝕜) (X := X)

def DenseTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    DenseType (𝕜 := 𝕜) (X := X) (Y := Y)

def ClosedTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ClosedType (𝕜 := 𝕜) (X := X) (Y := Y)

def ClosableTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ClosableType (𝕜 := 𝕜) (X := X) (Y := Y)

def ClosureTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ClosureType (𝕜 := 𝕜) (X := X) (Y := Y)

def GraphNormTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    GraphNormType (𝕜 := 𝕜) (X := X) (Y := Y)

def CoreTypeExpected :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    CoreType (𝕜 := 𝕜) (X := X) (Y := Y)

def ResolventSetTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventSetType (𝕜 := 𝕜) (X := X)

def ResolventTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventType (𝕜 := 𝕜) (X := X)

def ResolventToDomainTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventToDomainType (𝕜 := 𝕜) (X := X)

def InclusionLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    InclusionLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def EqualityLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    EqualityLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def GraphLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    GraphLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def KernelLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    KernelLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def RangeLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    RangeLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def SumDomainLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    SumDomainLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def SumEvaluationLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y],
    SumEvaluationLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def ProductDomainLawExpected : Prop :=
  ∀ {𝕜 X Y Z : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z],
    ProductDomainLaw (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z)

def ProductEvaluationLawExpected : Prop :=
  ∀ {𝕜 X Y Z : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup Z] [Module 𝕜 Z],
    ProductEvaluationLaw (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z)

def PowerZeroLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X],
    PowerZeroLaw (𝕜 := 𝕜) (X := X)

def PowerSuccessorLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X],
    PowerSuccessorLaw (𝕜 := 𝕜) (X := X)

def ShiftLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X],
    ShiftLaw (𝕜 := 𝕜) (X := X)

def ClosedLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ClosedLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def ClosableLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ClosableLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def ClosureLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    ClosureLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def CoreClosedLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    CoreClosedLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def GraphNormLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    GraphNormLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def GraphNormBoundsLawExpected : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    GraphNormBoundsLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def ResolventDomainLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventDomainLaw (𝕜 := 𝕜) (X := X)

def ResolventRightLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventRightLaw (𝕜 := 𝕜) (X := X)

def ResolventLeftLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventLeftLaw (𝕜 := 𝕜) (X := X)

def ResolventUniqueLawExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventUniqueLaw (𝕜 := 𝕜) (X := X)

def ResolventToGraphDomainTypeExpected :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X],
    ResolventToGraphDomainType (𝕜 := 𝕜) (X := X)

def ResolventGraphDomainLaw : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (ζ : 𝕜) (A : Operator 𝕜 X X) (h : Nonempty (ResolventInverse A ζ)) (y : X),
    GraphDomain.toDomain A (resolventToGraphDomainValue ζ A h y) =
      resolventToDomainValue ζ A h y

end OperatorDomainsSpec
end ExpandedFA.Unbounded
