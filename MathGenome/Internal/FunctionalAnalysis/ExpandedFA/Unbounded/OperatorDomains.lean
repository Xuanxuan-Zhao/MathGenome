import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains

/-! Canonical operators and their exact-domain calculus, following Part III.
Definitions have independent expected values in the imported Specs. The lemmas
below expose their domain, graph, closure, and two-sided inverse semantics. -/

noncomputable section
namespace ExpandedFA.Unbounded

section Algebra
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
  [AddCommGroup Z] [Module 𝕜 Z]

def mkOperator : OperatorDomainsSpec.MakeType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.makeValue

def domain : OperatorDomainsSpec.DomainType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.domainValue

def IsIncluded : OperatorDomainsSpec.InclusionType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.inclusionValue

def SameOperator : OperatorDomainsSpec.EqualityType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.equalityValue

def graph : OperatorDomainsSpec.GraphType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.graphValue

def kernel : OperatorDomainsSpec.KernelType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.kernelValue

def range : OperatorDomainsSpec.RangeType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.rangeValue

def restrict : OperatorDomainsSpec.RestrictType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.restrictValue

def add : OperatorDomainsSpec.SumType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.sumValue

def smul : OperatorDomainsSpec.ScalarType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.scalarValue

def productDomain : OperatorDomainsSpec.ProductDomainType (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) :=
  OperatorDomainsSpec.productDomainValue

def product : OperatorDomainsSpec.ProductType (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) :=
  OperatorDomainsSpec.productValue

def identity : OperatorDomainsSpec.IdentityType (𝕜 := 𝕜) (X := X) :=
  OperatorDomainsSpec.identityValue

def power : OperatorDomainsSpec.PowerType (𝕜 := 𝕜) (X := X) :=
  OperatorDomainsSpec.powerValue

def shift : OperatorDomainsSpec.ShiftType (𝕜 := 𝕜) (X := X) :=
  OperatorDomainsSpec.shiftValue

end Algebra

section Normed
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def DenselyDefined : OperatorDomainsSpec.DenseType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.denseValue

def IsClosed : OperatorDomainsSpec.ClosedType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.closedValue

def IsClosable : OperatorDomainsSpec.ClosableType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.closableValue

def closure : OperatorDomainsSpec.ClosureType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.closureValue

def graphNorm : OperatorDomainsSpec.GraphNormType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.graphNormValue

def IsCore : OperatorDomainsSpec.CoreType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  OperatorDomainsSpec.coreValue

def resolventSet : OperatorDomainsSpec.ResolventSetType (𝕜 := 𝕜) (X := X) :=
  OperatorDomainsSpec.resolventSetValue

def resolvent : OperatorDomainsSpec.ResolventType (𝕜 := 𝕜) (X := X) :=
  OperatorDomainsSpec.resolventValue

def resolventToDomain : OperatorDomainsSpec.ResolventToDomainType (𝕜 := 𝕜) (X := X) :=
  OperatorDomainsSpec.resolventToDomainValue

end Normed

section AlgebraLaws
variable {𝕜 X Y Z : Type*} [RCLike 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
  [AddCommGroup Z] [Module 𝕜 Z]

theorem inclusion_iff : OperatorDomainsSpec.InclusionLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A B
  rfl

theorem equality_iff : OperatorDomainsSpec.EqualityLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A B
  exact LinearPMap.ext_iff

theorem mem_graph_iff : OperatorDomainsSpec.GraphLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  rintro A ⟨z₁, z₂⟩
  constructor
  · intro h
    rcases A.mem_graph_iff.mp h with ⟨x, hx, hy⟩
    dsimp only at hx
    subst z₁
    exact ⟨x.2, hy⟩
  · rintro ⟨hx, hy⟩
    exact A.mem_graph_iff.mpr ⟨⟨z₁, hx⟩, rfl, hy⟩

theorem mem_kernel_iff : OperatorDomainsSpec.KernelLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A x
  constructor
  · intro h
    rcases LinearPMap.mem_ker_iff.mp h with ⟨y, rfl, hy⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hy⟩
    exact LinearPMap.mem_ker_iff.mpr ⟨⟨x, hx⟩, rfl, hy⟩

theorem mem_range_iff : OperatorDomainsSpec.RangeLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A y
  exact LinearMap.mem_range

theorem add_domain : OperatorDomainsSpec.SumDomainLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A B
  rfl

theorem add_apply : OperatorDomainsSpec.SumEvaluationLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A B x
  rfl

theorem mem_product_domain_iff :
    OperatorDomainsSpec.ProductDomainLaw (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) := by
  intro A B x
  rfl

theorem product_apply :
    OperatorDomainsSpec.ProductEvaluationLaw (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) := by
  intro A B x hx
  rfl

theorem power_zero : OperatorDomainsSpec.PowerZeroLaw (𝕜 := 𝕜) (X := X) := by
  intro A
  rfl

theorem power_succ : OperatorDomainsSpec.PowerSuccessorLaw (𝕜 := 𝕜) (X := X) := by
  intro A n
  rfl

theorem shift_domain_apply : OperatorDomainsSpec.ShiftLaw (𝕜 := 𝕜) (X := X) := by
  intro ζ A
  exact ⟨rfl, fun _ => rfl⟩

end AlgebraLaws

section NormedLaws
variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem isClosed_iff : OperatorDomainsSpec.ClosedLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A
  rfl

theorem isClosable_iff : OperatorDomainsSpec.ClosableLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A
  exact LinearPMap.isClosable_iff_exists_closed_extension

theorem closure_graph_closed_extends :
    OperatorDomainsSpec.ClosureLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A h
  exact ⟨h.graph_closure_eq_closure_graph.symm, h.closure_isClosed, A.le_closure⟩

theorem isCore_iff_of_closed :
    OperatorDomainsSpec.CoreClosedLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A h S
  change (S ≤ A.domain ∧ _) ↔ _
  rw [h.submodule_topologicalClosure_eq]

theorem graphDomain_norm : OperatorDomainsSpec.GraphNormLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A x
  rfl

theorem graphNorm_bounds : OperatorDomainsSpec.GraphNormBoundsLaw (𝕜 := 𝕜) (X := X) (Y := Y) := by
  intro A x
  exact ⟨le_add_of_nonneg_right (norm_nonneg _), le_add_of_nonneg_left (norm_nonneg _)⟩

theorem resolventToDomain_coe : OperatorDomainsSpec.ResolventDomainLaw (𝕜 := 𝕜) (X := X) := by
  intro ζ A h y
  simp only [OperatorDomainsSpec.resolventToDomainValue, OperatorDomainsSpec.resolventValue, dite_eq_left h]
  rfl

theorem resolvent_right_inverse : OperatorDomainsSpec.ResolventRightLaw (𝕜 := 𝕜) (X := X) := by
  intro ζ A h y
  exact h.some.right_inverse y

theorem resolvent_left_inverse : OperatorDomainsSpec.ResolventLeftLaw (𝕜 := 𝕜) (X := X) := by
  intro ζ A h x
  exact h.some.left_inverse x

theorem resolvent_inverse_unique : OperatorDomainsSpec.ResolventUniqueLaw (𝕜 := 𝕜) (X := X) := by
  intro ζ A R S
  ext y
  have h := R.left_inverse ⟨S.inverse y, S.mem_domain y⟩
  rw [S.right_inverse y] at h
  exact h

end NormedLaws

/-- The bounded inverse with values in the graph-norm domain. -/
def resolventToGraphDomain {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] :
    OperatorDomainsSpec.ResolventToGraphDomainType (𝕜 := 𝕜) (X := X) :=
  OperatorDomainsSpec.resolventToGraphDomainValue

theorem resolventToGraphDomain_toDomain : OperatorDomainsSpec.ResolventGraphDomainLaw := by
  intro 𝕜 X _ _ _ ζ A h y
  rfl

end ExpandedFA.Unbounded
