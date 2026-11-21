import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.IntegrationCochain

/-! The comparison paragraph, paper.tex:2777–2797, is a statement, not an axiom.
The continuous singular complex below uses *all* continuous maps from the same
ordered geometric simplex as the smooth complex. The choice definitions of
induced maps are characterized on representatives; existence and uniqueness
are proved in the implementation before they are used as induced maps.
No comparison equivalence is supplied or assumed in these constructions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SmoothManifolds.ContinuousSingularData
open SmoothSingularData
universe u v
variable (M : Type u) [TopologicalSpace M]

abbrev SingularSimplex (q : ℕ) := {f : Simplex q → M // Continuous f}
abbrev Chains (q : ℕ) := SingularSimplex M q →₀ ℝ

def generate {q : ℕ} (f : Simplex q → M) : Chains M q :=
  if h : Continuous f then Finsupp.single ⟨f,h⟩ 1 else 0

def boundary (q : ℕ) : Chains M (q+1) →ₗ[ℝ] Chains M q :=
  Finsupp.linearCombination ℝ (fun σ =>
    ∑ j : Fin (q+2), (-1 : ℝ)^j.val • generate M (σ.val ∘ face j))

def boundaryZero : Chains M 0 →ₗ[ℝ] (Fin 0 → ℝ) := 0
abbrev Cochains (q : ℕ) := Chains M q →ₗ[ℝ] ℝ

def coboundary (q : ℕ) : Cochains M q →ₗ[ℝ] Cochains M (q+1) where
  toFun c := c.comp (boundary M q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cocycles (q : ℕ) : Submodule ℝ (Cochains M q) :=
  LinearMap.ker (coboundary M q)

def previousCoboundary : (q : ℕ) → Cochains M (q-1) →ₗ[ℝ] Cochains M q
  | 0 => 0
  | q+1 => coboundary M q

def coboundaries (q : ℕ) : Submodule ℝ (cocycles M q) :=
  (LinearMap.range (previousCoboundary M q)).comap (cocycles M q).subtype

instance cocyclesAddCommGroup (q : ℕ) : AddCommGroup (cocycles M q) :=
  @Submodule.addCommGroup ℝ (Cochains M q) inferInstance inferInstance inferInstance (cocycles M q)

instance cocyclesModule (q : ℕ) : Module ℝ (cocycles M q) :=
  @Submodule.module ℝ (Cochains M q) inferInstance inferInstance inferInstance (cocycles M q)

abbrev Cohomology (q : ℕ) := (cocycles M q) ⧸ coboundaries M q

instance cohomologyAddCommGroup (q : ℕ) : AddCommGroup (Cohomology M q) :=
  @Submodule.Quotient.addCommGroup ℝ (cocycles M q) inferInstance
    (cocyclesAddCommGroup M q) (cocyclesModule M q) (coboundaries M q)

instance cohomologyModule (q : ℕ) : Module ℝ (Cohomology M q) :=
  @Submodule.Quotient.module ℝ (cocycles M q) inferInstance
    (cocyclesAddCommGroup M q) (cocyclesModule M q) (coboundaries M q)

def classOf (q : ℕ) : cocycles M q →ₗ[ℝ] Cohomology M q := (coboundaries M q).mkQ

variable {M} {N : Type v} [TopologicalSpace N]

def chainMap (f : M → N) (q : ℕ) : Chains M q →ₗ[ℝ] Chains N q :=
  Finsupp.linearCombination ℝ (fun σ => generate N (f ∘ σ.val))

def cochainMap (f : M → N) (q : ℕ) : Cochains N q →ₗ[ℝ] Cochains M q where
  toFun c := c.comp (chainMap f q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Specification on every representative, without any quotient certificate. -/
def IsPullback (f : M → N) (q : ℕ) (F : Cohomology N q →ₗ[ℝ] Cohomology M q) : Prop :=
  ∀ c : cocycles N q, ∃ d : cocycles M q,
    d.val = cochainMap f q c.val ∧ F (classOf N q c) = classOf M q d

/-- Choice is total; `cohomologyPullback_spec` proves it is the induced map
for continuous f, and uniqueness makes the choice immaterial. -/
def cohomologyPullback (f : M → N) (q : ℕ) : Cohomology N q →ₗ[ℝ] Cohomology M q :=
  Classical.epsilon (IsPullback f q)
end SmoothManifolds.ContinuousSingularData

namespace SmoothManifolds.ComparisonData
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData IntegrationCochainData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

/-- Forget smoothness, retaining the very same geometric simplex and map. -/
def forgetSimplex {q : ℕ} (σ : SmoothSingularData.SingularSimplex S q) :
    ContinuousSingularData.SingularSimplex M q := ⟨σ.val, σ.property.1⟩

def inclusion (q : ℕ) : SmoothSingularData.Chains S q →ₗ[ℝ]
    ContinuousSingularData.Chains M q :=
  Finsupp.linearCombination ℝ (fun σ => Finsupp.single (forgetSimplex S σ) 1)

/-- Restrict a continuous singular cochain by precomposing with chain inclusion. -/
def restriction (q : ℕ) : ContinuousSingularData.Cochains M q →ₗ[ℝ]
    SmoothSingularData.Cochains S q where
  toFun c := c.comp (inclusion S q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def IsRestriction (q : ℕ) (F : ContinuousSingularData.Cohomology M q →ₗ[ℝ]
    SmoothSingularData.Cohomology S q) : Prop :=
  ∀ c : ContinuousSingularData.cocycles M q, ∃ d : SmoothSingularData.cocycles S q,
    d.val = restriction S q c.val ∧
    F (ContinuousSingularData.classOf M q c) = singularClass S q d

def restrictionCohomology (q : ℕ) : ContinuousSingularData.Cohomology M q →ₗ[ℝ]
    SmoothSingularData.Cohomology S q := Classical.epsilon (IsRestriction S q)

/-- A family over every manifold, including the empty space, boundary and degree zero. -/
def RestrictionEquivalences :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ),
    ContinuousSingularData.Cohomology M q ≃ₗ[ℝ] SmoothSingularData.Cohomology S q

/-- Both comparison assertions in a single proposition. R realizes the actual
restriction map; precisely its inverse is used in the de Rham assertion.
The representative conditions for I, F and P use the existing integration and
intrinsic pullback interfaces, whose existence is already an upstream theorem.
They are not hypotheses asserting either comparison theorem. -/
def ComparisonStatement : Prop :=
  ∃ R : RestrictionEquivalences.{u},
    (∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
      (S : SmoothManifold n a M) (q : ℕ),
      (R S q).toLinearMap = restrictionCohomology S q) ∧
    (∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
      [TopologicalSpace M] [TopologicalSpace N]
      (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
      MapData.IsSmoothMap S T f →
      ∀ (Q : ∀ q, SmoothSingularData.Cohomology T q →ₗ[ℝ]
        SmoothSingularData.Cohomology S q), IsSingularCohomologyPullback S T f Q →
      ∀ q (x : ContinuousSingularData.Cohomology N q),
        R S q (ContinuousSingularData.cohomologyPullback f q x) = Q q (R T q x)) ∧
    (∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
      (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (I : IntegrationMap S K)
      (F : ∀ q, K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q),
      IsInduced S I F → ∀ q,
        ∃ D : K.Cohomology q ≃ₗ[ℝ] ContinuousSingularData.Cohomology M q,
          D.toLinearMap = (R S q).symm.toLinearMap.comp (F q)) ∧
    (∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
      [TopologicalSpace M] [TopologicalSpace N]
      (S : SmoothManifold n a M) (T : SmoothManifold m b N)
      (C : CotangentBundle S) (A : CotangentBundle T)
      (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
      (K : Calculus C B) (J : Calculus A E)
      (I : IntegrationMap S K) (H : IntegrationMap T J)
      (F : ∀ q, K.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology S q)
      (G : ∀ q, J.Cohomology q →ₗ[ℝ] SmoothSingularData.Cohomology T q),
      IsInduced S I F → IsInduced T H G →
      ∀ (f : M → N), MapData.IsSmoothMap S T f →
      ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
      (∀ p, DifferentialData.IsDifferential S T f p (L p)) →
      ∀ (P : ∀ q, J.Cohomology q →ₗ[ℝ] K.Cohomology q),
      IsCohomologyPullback C B K J f L P →
      ∀ q (x : J.Cohomology q),
        (R S q).symm (F q (P q x)) =
          ContinuousSingularData.cohomologyPullback f q ((R T q).symm (G q x)))
end SmoothManifolds.ComparisonData

namespace Specs.SmoothManifolds.Comparison.StatementInterface
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.ComparisonData
  _root_.SmoothManifolds.IntegrationCochainData
universe u v w

def continuousSingularSimplexType := (M : Type u) → [TopologicalSpace M] → ℕ → Type u
noncomputable def continuousSingularSimplexValue : continuousSingularSimplexType := @ContinuousSingularData.SingularSimplex

def continuousChainsType := (M : Type u) → [TopologicalSpace M] → ℕ → Type u
noncomputable def continuousChainsValue : continuousChainsType := @ContinuousSingularData.Chains

def continuousCochainsType := (M : Type u) → [TopologicalSpace M] → ℕ → Type u
noncomputable def continuousCochainsValue : continuousCochainsType := @ContinuousSingularData.Cochains

def continuousCohomologyType := (M : Type u) → [TopologicalSpace M] → ℕ → Type u
noncomputable def continuousCohomologyValue : continuousCohomologyType := @ContinuousSingularData.Cohomology

def continuousGenerateType := (M : Type u) → [TopologicalSpace M] → {q : ℕ} → (SmoothSingularData.Simplex q → M) → ContinuousSingularData.Chains M q
noncomputable def continuousGenerateValue : continuousGenerateType := @ContinuousSingularData.generate

def continuousBoundaryType := (M : Type u) → [TopologicalSpace M] → (q : ℕ) → ContinuousSingularData.Chains M (q+1) →ₗ[ℝ] ContinuousSingularData.Chains M q
noncomputable def continuousBoundaryValue : continuousBoundaryType := @ContinuousSingularData.boundary

def continuousBoundaryZeroType := (M : Type u) → [TopologicalSpace M] → ContinuousSingularData.Chains M 0 →ₗ[ℝ] (Fin 0 → ℝ)
noncomputable def continuousBoundaryZeroValue : continuousBoundaryZeroType := @ContinuousSingularData.boundaryZero

def continuousCoboundaryType := (M : Type u) → [TopologicalSpace M] → (q : ℕ) → ContinuousSingularData.Cochains M q →ₗ[ℝ] ContinuousSingularData.Cochains M (q+1)
noncomputable def continuousCoboundaryValue : continuousCoboundaryType := @ContinuousSingularData.coboundary

def continuousCocyclesType := (M : Type u) → [TopologicalSpace M] → (q : ℕ) → Submodule ℝ (ContinuousSingularData.Cochains M q)
noncomputable def continuousCocyclesValue : continuousCocyclesType := @ContinuousSingularData.cocycles

def continuousPreviousCoboundaryType := (M : Type u) → [TopologicalSpace M] → (q : ℕ) → ContinuousSingularData.Cochains M (q-1) →ₗ[ℝ] ContinuousSingularData.Cochains M q
noncomputable def continuousPreviousCoboundaryValue : continuousPreviousCoboundaryType := @ContinuousSingularData.previousCoboundary

def continuousCoboundariesType := (M : Type u) → [TopologicalSpace M] → (q : ℕ) → Submodule ℝ (ContinuousSingularData.cocycles M q)
noncomputable def continuousCoboundariesValue : continuousCoboundariesType := @ContinuousSingularData.coboundaries

def continuousClassOfType := (M : Type u) → [TopologicalSpace M] → (q : ℕ) → ContinuousSingularData.cocycles M q →ₗ[ℝ] ContinuousSingularData.Cohomology M q
noncomputable def continuousClassOfValue : continuousClassOfType := @ContinuousSingularData.classOf

def continuousChainMapType := {M : Type u} → [TopologicalSpace M] → {N : Type v} → [TopologicalSpace N] → (M → N) → (q : ℕ) → ContinuousSingularData.Chains M q →ₗ[ℝ] ContinuousSingularData.Chains N q
noncomputable def continuousChainMapValue : continuousChainMapType := @ContinuousSingularData.chainMap

def continuousCochainMapType := {M : Type u} → [TopologicalSpace M] → {N : Type v} → [TopologicalSpace N] → (M → N) → (q : ℕ) → ContinuousSingularData.Cochains N q →ₗ[ℝ] ContinuousSingularData.Cochains M q
noncomputable def continuousCochainMapValue : continuousCochainMapType := @ContinuousSingularData.cochainMap

def continuousCohomologyPullbackType := {M : Type u} → [TopologicalSpace M] → {N : Type v} → [TopologicalSpace N] → (M → N) → (q : ℕ) → ContinuousSingularData.Cohomology N q →ₗ[ℝ] ContinuousSingularData.Cohomology M q
noncomputable def continuousCohomologyPullbackValue : continuousCohomologyPullbackType := @ContinuousSingularData.cohomologyPullback

def forgetSimplexType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → {q : ℕ} → SmoothSingularData.SingularSimplex S q → ContinuousSingularData.SingularSimplex M q
noncomputable def forgetSimplexValue : forgetSimplexType := @ComparisonData.forgetSimplex

def inclusionType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) → SmoothSingularData.Chains S q →ₗ[ℝ] ContinuousSingularData.Chains M q
noncomputable def inclusionValue : inclusionType := @ComparisonData.inclusion

def restrictionType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) → ContinuousSingularData.Cochains M q →ₗ[ℝ] SmoothSingularData.Cochains S q
noncomputable def restrictionValue : restrictionType := @ComparisonData.restriction

def restrictionCohomologyType := {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] → (S : SmoothManifold n a M) → (q : ℕ) → ContinuousSingularData.Cohomology M q →ₗ[ℝ] SmoothSingularData.Cohomology S q
noncomputable def restrictionCohomologyValue : restrictionCohomologyType := @ComparisonData.restrictionCohomology

def comparisonStatementType := Prop
noncomputable def comparisonStatementValue : comparisonStatementType := ComparisonData.ComparisonStatement.{u}

/-- Square zero and the full incoming image, including the degree-zero convention. -/
def continuousComplexType : Prop :=
  ∀ (M : Type u) [TopologicalSpace M],
    (∀ q, (ContinuousSingularData.boundary M q).comp (ContinuousSingularData.boundary M (q+1)) = 0) ∧
    (ContinuousSingularData.boundaryZero M = 0) ∧
    (∀ q, (ContinuousSingularData.coboundary M (q+1)).comp (ContinuousSingularData.coboundary M q) = 0) ∧
    (∀ q, LinearMap.range (ContinuousSingularData.previousCoboundary M q) ≤ ContinuousSingularData.cocycles M q) ∧
    (ContinuousSingularData.coboundaries M 0 = ⊥)

/-- Continuous maps give the usual chain maps and induced cohomology pullbacks. -/
def continuousPullbackType : Prop :=
  ∀ {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (f : M → N), Continuous f → ∀ q,
    ((ContinuousSingularData.boundary N q).comp (ContinuousSingularData.chainMap f (q+1)) =
      (ContinuousSingularData.chainMap f q).comp (ContinuousSingularData.boundary M q)) ∧
    (∃! F : ContinuousSingularData.Cohomology N q →ₗ[ℝ] ContinuousSingularData.Cohomology M q,
      ContinuousSingularData.IsPullback f q F) ∧
    ContinuousSingularData.IsPullback f q (ContinuousSingularData.cohomologyPullback f q)

/-- The constructed restriction cochain map and its actual uniquely induced r*. -/
def restrictionConstructionType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (q : ℕ),
    ((SmoothSingularData.coboundary S q).comp (restriction S q) =
      (restriction S (q+1)).comp (ContinuousSingularData.coboundary M q)) ∧
    (∃! F : ContinuousSingularData.Cohomology M q →ₗ[ℝ] SmoothSingularData.Cohomology S q,
      IsRestriction S q F) ∧
    IsRestriction S q (restrictionCohomology S q)

/-- Naturality with respect to smooth maps, without assuming either isomorphism. -/
def restrictionNaturalityType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (f : M → N),
    MapData.IsSmoothMap S T f →
    ∀ (Q : ∀ q, SmoothSingularData.Cohomology T q →ₗ[ℝ] SmoothSingularData.Cohomology S q),
    IsSingularCohomologyPullback S T f Q → ∀ q (x : ContinuousSingularData.Cohomology N q),
      restrictionCohomology S q (ContinuousSingularData.cohomologyPullback f q x) =
        Q q (restrictionCohomology T q x)

end Specs.SmoothManifolds.Comparison.StatementInterface
