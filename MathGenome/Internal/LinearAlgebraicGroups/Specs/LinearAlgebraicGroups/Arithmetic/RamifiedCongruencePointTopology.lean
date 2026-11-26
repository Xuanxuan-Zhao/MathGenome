import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding

/-! Topologies on marked points and on the actual finite-level face subgroups. -/

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj WithZero

namespace LinearAlgebraicGroups.Specs.RamifiedCongruencePointTopology

open IntegralSemisimpleModel ExceptionalIwahoriCongruence
open ExceptionalAffineBruhat ExceptionalAffineBuilding
open ExceptionalAffineRootSystems (ApartmentRoots)
open ExceptionalLocalRootCoordinates (normalizedValuation)
open Pinning (BasedRootDatum)
open ValuativeRel

universe u v

/-- The topology given by evaluating marked field points is independent of the
affine presentation used for the same integral scheme. -/
def PresentationIndependent : Prop :=
  ∀ {X : IntegralScheme.{u}} (B B' : IntegralAlgebra.{u})
    (e : integralSpec.obj (op B) ≅ X) (e' : integralSpec.obj (op B') ≅ X)
    (K : Type u) [Field K] [TopologicalSpace K],
    markedPointTopology B e K = markedPointTopology B' e' K

/-- Finite-type coordinates on the actual integral marking. -/
abbrev FiniteTypePresentation : Prop := IntegralAffinePresentation.{u}

/-- Pointwise evaluation gives a topological group for each affine presentation. -/
def MarkedPointGroup : Prop :=
  ∀ {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (H : IntegralGroup.{u}) (B : IntegralAlgebra.{u})
    (e : integralSpec.obj (op B) ≅ H.X),
    letI : TopologicalSpace (IntegralPoints H (integralRing K)) := markedPointTopology B e K
    IsTopologicalGroup (IntegralPoints H (integralRing K))

/-- Continuous scalar change for marked points, including morphisms having
a positive-power relation between the normalized valuations. -/
def MarkedScalarContinuity : Prop :=
  (∀ {K E : Type u} [Field K] [Field E] [TopologicalSpace K] [TopologicalSpace E]
    (f : K →+* E), Continuous f → ∀ {X : IntegralScheme.{u}} (B : IntegralAlgebra.{u})
    (e : integralSpec.obj (op B) ≅ X),
    letI := markedPointTopology B e K
    letI := markedPointTopology B e E
    Continuous (changeRing (integralRingMap f) (X := X))) ∧
  (∀ {K E : Type u} [Field K] [Field E] [ValuativeRel K] [ValuativeRel E]
    [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
    (f : K →+* E) (d : ℕ), 0 < d →
    (∀ x, normalizedValuation E (f x) = normalizedValuation K x ^ d) → Continuous f)

/-- The topology on the rational point group is induced by its actual
marked point homomorphism. The actual face subgroup is compact and
inherits continuous group operations. -/
def CompactParahoric : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G Wf V : Type u} {J : Type v} [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
    {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
    {C : LocalComparison (j := j) (Wf := Wf) A p} (_Y : Building C)
    (T : Set (A.SimpleWall p)) (_hT : T ≠ Set.univ)
    (B : IntegralAlgebra.{u}) (e : integralSpec.obj (op B) ≅ M.group.X),
    letI : TopologicalSpace G := TopologicalSpace.induced j (markedPointTopology B e K)
    IsTopologicalGroup G ∧ IsCompact (parahoric C T : Set G) ∧
      IsTopologicalGroup (parahoric C T) ∧ CompactSpace (parahoric C T)

/-- Closed kernels for reduction of actual integral parahoric points, when
the point map after inclusion into the auxiliary field is scaled scalar
extension in the given affine presentation. -/
def ClosedParahoricReductionKernel : Prop :=
  ∀ {K E : Type u} [Field K] [Field E] [ValuativeRel K] [ValuativeRel E]
    [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
    {D : BasedRootDatum.{u}} {M : Model D}
    {G Wf V : Type u} {J : Type v} [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
    {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (j := j) (Wf := Wf) A p) (T : Set (A.SimpleWall p))
    (B : IntegralAlgebra.{u}) (e : integralSpec.obj (op B) ≅ M.group.X)
    (ξ : (valuation E).valuationSubring) (_hξ : (valuation E).IsUniformizer (ξ : E))
    (f : K →+* E) (_hf : Continuous f) (s : FieldPoints M E)
    (q : parahoric C T →* IntegralPoints M.group (localIntegers E))
    (_hq : ∀ g : parahoric C T,
      changeRingHom M.group (localIntegersInclusion E) (q g) =
        MulAut.conj s (scalarPoints M f (j g))),
    letI : TopologicalSpace G := TopologicalSpace.induced j (markedPointTopology B e K)
    ∀ n : ℕ, IsClosed
      (((changeRingHom M.group (congruenceHom (localIntegers E) n)).comp q).ker :
        Set (parahoric C T))

/-- Coefficient automorphisms are continuous when they intertwine on the
actual field points. -/
def ParahoricCoefficientContinuity : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G Wf V : Type u} {J : Type v} [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
    {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (j := j) (Wf := Wf) A p) (T : Set (A.SimpleWall p))
    (B : IntegralAlgebra.{u}) (e : integralSpec.obj (op B) ≅ M.group.X)
    (σ : K ≃+* K) (_hσ : Continuous σ) (τ : MulAut (parahoric C T))
    (_hτ : ∀ g : parahoric C T, j (τ g) = scalarPoints M σ.toRingHom (j g)),
    letI : TopologicalSpace G := TopologicalSpace.induced j (markedPointTopology B e K)
    Continuous (τ : parahoric C T → parahoric C T)


end LinearAlgebraicGroups.Specs.RamifiedCongruencePointTopology
