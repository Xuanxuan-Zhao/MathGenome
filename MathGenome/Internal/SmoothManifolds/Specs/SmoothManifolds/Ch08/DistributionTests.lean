import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.InvariantExteriorFormula
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Independent objects and statements for paper.tex 1613--1633, M08.01.

Local fields are ambient sections smooth only on an open domain. Values outside
that domain are immaterial. Local brackets use the original intrinsic coordinate
commutator, with existence of the coordinate derivatives explicitly required.
The local exterior derivative uses the original coordinate characterization.
No bracket closure, annihilator smoothness, or integrability theorem is a field
of the distribution data. The base is boundaryless, with no positivity restriction
on its dimension or on the rank of a distribution.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.DistributionData
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData FiniteRegularityData BundleData BundleOperationsData ConstantRankData FrameData
  CovectorData ExteriorData ExteriorDerivativeData VectorFieldData LieBracketData
  Set Filter
open scoped Topology
universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A rank-k smooth subbundle of the original tangent bundle. -/
structure SmoothDistribution (C : CotangentBundle S) (k : ℕ) where
  fiber : (p : M) → Submodule ℝ (TangentSpace S p)
  smooth : letI := C.realization.space.topology
    IsSmoothSubbundle C.realization.space.bundle k fiber

variable {C : CotangentBundle S} {k : ℕ}

/-- Actual local smoothness into the intrinsic tangent total space. -/
def IsLocalField (B : TangentBundleStructure S) (U : Set M) (X : Section S) : Prop :=
  letI := B.topology
  ManifoldSmoothOn S.smoothStructure.val B.manifold.smoothStructure.val
    (fun p => (⟨p, X p⟩ : TangentBundleData.TotalSpace S)) U

def ValuesIn (D : SmoothDistribution C k) (U : Set M) (X : Section S) : Prop :=
  ∀ p ∈ U, X p ∈ D.fiber p

/-- Coordinate characterization of the local commutator, restricted to U.
The first clause prevents a vacuous characterization by nonexistent derivatives. -/
def HasLocalBracket (B : TangentBundleStructure S) (U : Set M)
    (X Y Z : Section S) : Prop :=
  (∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (p : M), p ∈ U → p ∈ e.source →
      ∃ L K : Euclidean n →L[ℝ] Euclidean n,
        HasCoordinateDerivative e (LieBracketData.coefficients B X e he) p L ∧
        HasCoordinateDerivative e (LieBracketData.coefficients B Y e he) p K) ∧
  ∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (p : M), p ∈ U → p ∈ e.source →
    ∀ (L K : Euclidean n →L[ℝ] Euclidean n),
      HasCoordinateDerivative e (LieBracketData.coefficients B X e he) p L →
      HasCoordinateDerivative e (LieBracketData.coefficients B Y e he) p K →
      ∀ j, LieBracketData.coefficients B Z e he p j = ∑ i,
        (LieBracketData.coefficients B X e he p i * K (Pi.single i 1) j -
          LieBracketData.coefficients B Y e he p i * L (Pi.single i 1) j)

/-- Closure for all local sections on every open domain. -/
def IsInvolutive (D : SmoothDistribution C k) : Prop :=
  ∀ (U : Set M), IsOpen U → ∀ X Y Z : Section S,
    IsLocalField C.tangent U X → IsLocalField C.tangent U Y →
    HasLocalBracket C.tangent U X Y Z → ValuesIn D U X → ValuesIn D U Y →
    ValuesIn D U Z

/-- Involutivity on an open region tests every smaller open domain. -/
def IsInvolutiveOn (D : SmoothDistribution C k) (V : Set M) : Prop :=
  ∀ (U : Set M), IsOpen U → U ⊆ V → ∀ X Y Z : Section S,
    IsLocalField C.tangent U X → IsLocalField C.tangent U Y →
    HasLocalBracket C.tangent U X Y Z → ValuesIn D U X → ValuesIn D U Y →
    ValuesIn D U Z

/-- The integral manifold has its own topology, which need not be the subspace
 topology. Its dimension is k and the actual tangent differential has image D. -/
def IsIntegralSubmanifold (D : SmoothDistribution C k) (A : Set M) : Prop :=
  ∃ t : TopologicalSpace A, ∃ T : @SmoothManifold k .euclidean A t,
    @IsSmoothMap k n .euclidean .euclidean A M t _ T S Subtype.val ∧
    @MapClassData.IsImmersion k n .euclidean .euclidean A M t _ T S Subtype.val ∧
    ∃ L : (p : A) → @TangentSpace k .euclidean A t T p →ₗ[ℝ] TangentSpace S p.val,
      (∀ p, @IsDifferential k n .euclidean .euclidean A M t _ T S
        Subtype.val p (L p)) ∧ ∀ p, LinearMap.range (L p) = D.fiber p.val

def IsIntegrable (D : SmoothDistribution C k) : Prop :=
  ∀ p : M, ∃ A : Set M, p ∈ A ∧ IsIntegralSubmanifold D A

/-- The actual annihilator, with no chosen metric or complementary space. -/
def annihilator (D : SmoothDistribution C k) (p : M) :
    Submodule ℝ (CotangentFiber S p) := (D.fiber p).dualAnnihilator

/-- Smooth local basis of D, viewed in the ambient tangent bundle. -/
structure DistributionFrame (D : SmoothDistribution C k) (U : Set M) (hU : IsOpen U) where
  basis : (p : U) → Module.Basis (Fin k) ℝ (D.fiber p.val)
  smooth : letI := C.tangent.topology
    ∀ i, ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      C.tangent.manifold.smoothStructure.val
      (fun p : U => (⟨p.val, (basis p i).val⟩ : TangentBundleData.TotalSpace S))

/-- Totalization by zero adds no condition outside the open frame domain. -/
def frameSection {D : SmoothDistribution C k} {U : Set M} {hU : IsOpen U}
    (F : DistributionFrame D U hU) (i : Fin k) : Section S := by
  classical
  exact fun p => if hp : p ∈ U then (F.basis ⟨p, hp⟩ i).val else 0

def FrameBracketClosed {D : SmoothDistribution C k} {U : Set M} {hU : IsOpen U}
    (F : DistributionFrame D U hU) : Prop :=
  ∀ i j (Z : Section S),
    HasLocalBracket C.tangent U (frameSection F i) (frameSection F j) Z → ValuesIn D U Z

/-- Local smooth form, retaining the original exterior fibers and total space. -/
def IsLocalForm {j : ℕ} (B : FormBundle C j) (U : Set M) (ω : Field S j) : Prop :=
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  ManifoldSmoothOn S.smoothStructure.val B.space.bundle.totalManifold.smoothStructure.val
    (fun p => (⟨p, ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose j))
      (fun q => ExteriorData.Fiber (TangentSpace S q) j))) U

def HasLocalExteriorDerivative (U : Set M) {j : ℕ}
    (ω : Field S j) (η : Field S (j+1)) : Prop :=
  ∀ (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (p : M), p ∈ U → ∀ hp : p ∈ c.source,
      η p = coordinateDerivative C j c hc ω p hp

/-- The degree-j part of the vanishing ideal, including degree zero.
For j=0 the unique empty tuple is tested, so its vanishing part is zero. -/
def VanishesOn (D : SmoothDistribution C k) (U : Set M) {j : ℕ}
    (ω : Field S j) : Prop :=
  ∀ p ∈ U, ∀ v : Fin j → TangentSpace S p,
    (∀ i, v i ∈ D.fiber p) → evaluate (TangentSpace S p) j (ω p) v = 0

/-- All local annihilator sections, tested on every pair of vectors in D. -/
def LocalAnnihilatorTest (D : SmoothDistribution C k) (B : FormBundle C 1) : Prop :=
  ∀ (U : Set M), IsOpen U → ∀ (θ : Field S 1) (η : Field S 2),
    IsLocalForm B U θ → HasLocalExteriorDerivative (C := C) U θ η → VanishesOn D U θ →
    VanishesOn D U η

/-- Stability for global smooth forms, without any unlisted assumed derivative
family. The derivative is the actual shared coordinate derivative. -/
def GlobalIdealStable (D : SmoothDistribution C k) (B : ∀ j, FormBundle C j) : Prop :=
  ∀ j (ω : Field S j) (η : Field S (j+1)),
    IsForm (B j) ω → HasExteriorDerivative C ω η →
    VanishesOn D univ ω → VanishesOn D univ η

end SmoothManifolds.DistributionData

namespace Specs.SmoothManifolds.Ch08.DistributionTests
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.ConstantRankData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.ExteriorDerivativeData _root_.SmoothManifolds.DistributionData
  _root_.SmoothManifolds.VectorFieldData _root_.SmoothManifolds.LieBracketData Set
universe u

/-- Independent type/value bindings for the primary public objects. -/
def SmoothDistributionType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → CotangentBundle S → ℕ → Type u
def SmoothDistributionValue : SmoothDistributionType := @DistributionData.SmoothDistribution

def IsInvolutiveType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → {C : CotangentBundle S} → {k : ℕ} →
    SmoothDistribution C k → Prop
def IsInvolutiveValue : IsInvolutiveType := @DistributionData.IsInvolutive
def IsIntegralSubmanifoldType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → {C : CotangentBundle S} → {k : ℕ} →
    SmoothDistribution C k → Set M → Prop
def IsIntegralSubmanifoldValue : IsIntegralSubmanifoldType := @DistributionData.IsIntegralSubmanifold

def IsIntegrableType := IsInvolutiveType
def IsIntegrableValue : IsIntegrableType := @DistributionData.IsIntegrable

def annihilatorType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → {C : CotangentBundle S} → {k : ℕ} →
    SmoothDistribution C k → (p : M) → Submodule ℝ (CotangentFiber S p)
def annihilatorValue : annihilatorType := @DistributionData.annihilator

section Base
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}

/-- Local existence and uniqueness on U of the coordinate bracket, rather than
uniqueness of irrelevant values outside U. -/
def local_bracket_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : CotangentBundle S)
    (U : Set M), IsOpen U → ∀ X Y : Section S,
    IsLocalField C.tangent U X → IsLocalField C.tangent U Y →
    ∃ Z : Section S, IsLocalField C.tangent U Z ∧ HasLocalBracket C.tangent U X Y Z ∧
      ∀ W, HasLocalBracket C.tangent U X Y W → ∀ p ∈ U, W p = Z p

/-- The local derivative in the annihilator test exists and stays smooth;
this bridge cannot be replaced by quantification over a nonexistent derivative. -/
def local_derivative_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : CotangentBundle S)
    (j : ℕ) (B : FormBundle C j) (E : FormBundle C (j+1))
    (U : Set M), IsOpen U → ∀ ω : Field S j, IsLocalForm B U ω →
    ∃ η : Field S (j+1), IsLocalForm E U η ∧ HasLocalExteriorDerivative (C := C) U ω η

def integrable_involutiveType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k), IsIntegrable D → IsInvolutive D

/-- The frame criterion for any specified smooth frame, not just a chosen
adapted frame from the smooth-subbundle certificate. -/
def frame_testType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (U : Set M) (hU : IsOpen U)
    (F : DistributionFrame D U hU),
    IsInvolutiveOn D U ↔ FrameBracketClosed F

def annihilator_subbundleType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k),
    letI := (cotangentSpace C).topology
    IsSmoothSubbundle (cotangentSpace C).bundle (n-k) (annihilator D)

def annihilator_testType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (B : FormBundle C 1),
    IsInvolutive D ↔ LocalAnnihilatorTest D B

/-- Global ideal preservation must imply all the local tests. In particular no
assumption that local annihilator sections are already global is permitted. -/
def ideal_testType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (B : ∀ j, FormBundle C j),
    IsInvolutive D ↔ GlobalIdealStable D B

/-- Pointwise separation by the actual annihilator, with no dimension premise. -/
def annihilator_separatesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (p : M) (v : TangentSpace S p),
    v ∈ D.fiber p ↔ ∀ θ ∈ annihilator D p, θ v = 0

def fiber_ranksType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (p : M),
    k ≤ n ∧ Module.finrank ℝ (D.fiber p) = k ∧
      Module.finrank ℝ (annihilator D p) = n-k

/-- The vanishing spaces are actual real vector subspaces in each degree. -/
def vanishing_linearType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (U : Set M) (j : ℕ),
    VanishesOn D U (0 : Field S j) ∧
    (∀ α β : Field S j, VanishesOn D U α → VanishesOn D U β → VanishesOn D U (α+β)) ∧
    (∀ (r : ℝ) (α : Field S j), VanishesOn D U α → VanishesOn D U (r • α))

/-- Exterior ideal property, without a positive-degree restriction. -/
def vanishing_wedgeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (U : Set M) (j l : ℕ)
    (α : Field S j) (β : Field S l),
    VanishesOn D U α → VanishesOn D U (fieldWedge α β)

/-- A useful fully intrinsic restricted-global version of the local one-form
calculation, with X and Y arbitrary ambient global fields whose values lie in
D only on U. This is a helper, not a replacement for the local equivalence. -/
def annihilator_bracket_identityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (B : FormBundle C 1)
    (U : Set M), IsOpen U → ∀ (θ : Field S 1) (η : Field S 2),
    IsForm B θ → HasExteriorDerivative C θ η → VanishesOn D U θ →
    ∀ (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent),
      BracketOperation b → ∀ X Y : SmoothField C.tangent,
      ValuesIn D U X.val → ValuesIn D U Y.val → ∀ p ∈ U,
      evaluate (TangentSpace S p) 2 (η p) ![X.val p, Y.val p] =
        -evaluate (TangentSpace S p) 1 (θ p) ![(b X Y).val p]

/-- Smooth frames exist locally at every point, with all zero-rank cases. -/
def local_frame_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k) (p : M),
    ∃ (U : Set M) (hU : IsOpen U), p ∈ U ∧ Nonempty (DistributionFrame D U hU)

def local_bracket_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
    (U : Set M) (X Y Z W : Section S),
    HasLocalBracket C.tangent U X Y Z → HasLocalBracket C.tangent U X Y W →
    ∀ p ∈ U, Z p = W p

def involutive_frame_testType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k), IsInvolutive D →
    ∀ (U : Set M) (hU : IsOpen U) (F : DistributionFrame D U hU), FrameBracketClosed F

def extreme_ranksType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S},
    (∀ D : SmoothDistribution C 0, IsInvolutive D ∧ ∀ p, D.fiber p = ⊥) ∧
    (∀ D : SmoothDistribution C n, IsInvolutive D ∧ ∀ p, D.fiber p = ⊤)

/-- All-degree invariant-formula consequence, before the local extension of
arbitrary fiber tuples to smooth fields. -/
def involutive_derivative_on_fieldsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : CotangentBundle S} {k : ℕ}
    (D : SmoothDistribution C k), IsInvolutive D →
    ∀ (U : Set M), IsOpen U → ∀ (j : ℕ) (B : FormBundle C j)
      (ω : Field S j) (η : Field S (j+1)),
    IsForm B ω → HasExteriorDerivative C ω η → VanishesOn D U ω →
    ∀ (b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent),
      BracketOperation b → ∀ (X : Fin (j+1) → SmoothField C.tangent),
      (∀ i, ValuesIn D U (X i).val) → ∀ p ∈ U,
      evaluate (TangentSpace S p) (j+1) (η p) (fun i => (X i).val p) = 0

end Base
end Specs.SmoothManifolds.Ch08.DistributionTests
