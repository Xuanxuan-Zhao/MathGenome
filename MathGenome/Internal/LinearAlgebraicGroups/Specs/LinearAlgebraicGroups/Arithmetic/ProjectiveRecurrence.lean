import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AbsoluteSimpleLocalLie
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Quotient

noncomputable section

open Set Filter MeasureTheory Topology
open scoped LinearAlgebra.Projectivization

namespace LinearAlgebraicGroups.Specs.Arithmetic.ProjectiveRecurrence

/-- The ordinary projective topology, the quotient of the punctured vector space. -/
scoped instance projectiveTopology {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [TopologicalSpace V] : TopologicalSpace (ℙ K V) :=
  TopologicalSpace.coinduced (Projectivization.mk' K) inferInstance

/-- The usual projective topology is Hausdorff in coordinates. -/
def ProjectiveHausdorff : Prop :=
  ∀ {K V ι : Type*} [NormedField K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    (b : V ≃ₗ[K] (ι → K)), Continuous b → Continuous b.symm → T2Space (ℙ K V)

/-- The union of the projective eigenspaces of a linear automorphism. -/
def weightLines {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : V ≃ₗ[K] V) : Set (ℙ K V) :=
  {x | ∃ c : K, a x.rep = c • x.rep}

/-- A finite invariant projective measure is supported on the projective eigenspaces when
eigenvalues on distinct weights have distinct absolute values. Coordinates may be taken in
any continuous eigenbasis, including a basis of the exterior power for the Plücker orbit. -/
def SupportInWeightLines : Prop :=
  ∀ {K V ι : Type*} [NormedField K] [AddCommGroup V] [Module K V]
    [TopologicalSpace V] [MeasurableSpace (ℙ K V)] [BorelSpace (ℙ K V)]
    (b : V ≃ₗ[K] (ι → K)) (_hb : Continuous b)
    (a : V ≃ₗ[K] V) (d : ι → K)
    (_hdiag : ∀ v i, b (a v) i = d i * b v i)
    (_hsep : ∀ i j, ‖d i‖ = ‖d j‖ → d i = d j)
    (μ : Measure (ℙ K V)) [IsFiniteMeasure μ],
    MeasurePreserving (a • ·) μ μ → μ.support ⊆ weightLines a

/-- The action of a linear automorphism on the exterior power. -/
def exteriorEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (a : V ≃ₗ[K] V) : (⋀[K]^n V) ≃ₗ[K] (⋀[K]^n V) :=
  LinearEquiv.ofLinearMap (exteriorPower.map n a.toLinearMap) (exteriorPower.map n a.symm.toLinearMap)
    (by rw [← exteriorPower.map_comp, LinearEquiv.comp_symm, exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp, LinearEquiv.symm_comp, exteriorPower.map_id])

/-- The exterior representation obtained from a linear representation. -/
def exteriorRepresentation {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (ρ : G →* (V ≃ₗ[K] V)) : G →* ((⋀[K]^n V) ≃ₗ[K] (⋀[K]^n V)) where
  toFun g := exteriorEquiv n (ρ g)
  map_one' := by
    rw [map_one]
    apply LinearEquiv.ext
    intro v
    change exteriorPower.map n LinearMap.id v = v
    rw [exteriorPower.map_id]
    rfl
  map_mul' g h := by
    rw [map_mul]
    apply LinearEquiv.ext
    intro v
    change exteriorPower.map n ((ρ g).toLinearMap.comp (ρ h).toLinearMap) v = _
    rw [exteriorPower.map_comp]
    rfl

/-- The Plücker line of an independent family exists, and a linear automorphism
preserves that line exactly when it preserves the span of the family. -/
def ExteriorLinePreservation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (v : Fin n → V), LinearIndependent K v →
    ∃ h : exteriorPower.ιMulti K n v ≠ 0,
      ∀ a : V ≃ₗ[K] V,
        exteriorEquiv n a • Projectivization.mk K (exteriorPower.ιMulti K n v) h =
          Projectivization.mk K (exteriorPower.ιMulti K n v) h ↔
        ∀ z ∈ Submodule.span K (Set.range v), a z ∈ Submodule.span K (Set.range v)

/-- A lattice-fixed line gives an equivariant orbit map from the space of cosets. -/
def orbitMap {P J K V : Type*} [Group P] [Group J] [Field K] [AddCommGroup V] [Module K V]
    (L : Subgroup P) (q : P →* J) (ρ : J →* (V ≃ₗ[K] V)) (x : ℙ K V)
    (hx : ∀ p ∈ L, ρ (q p) • x = x) : P ⧸ L → ℙ K V :=
  Quotient.lift (fun p ↦ ρ (q p) • x) (by
    intro p r h
    have hm : p⁻¹ * r ∈ L := QuotientGroup.leftRel_apply.mp h
    have hr := hx (p⁻¹ * r) hm
    calc
      ρ (q p) • x = ρ (q p) • (ρ (q (p⁻¹ * r)) • x) := by rw [hr]
      _ = ρ (q r) • x := by rw [← mul_smul, ← map_mul, ← map_mul, mul_inv_cancel_left])

/-- The projective orbit map from a finite invariant quotient pushes its measure
forward to a finite invariant measure containing the whole orbit in its support. -/
def ProjectiveOrbitMeasure : Prop :=
  ∀ {P J K V : Type*} [Group P] [Group J] [Field K] [AddCommGroup V] [Module K V]
    [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace V]
    [MeasurableSpace (ℙ K V)] [BorelSpace (ℙ K V)]
    (L : Subgroup P) (q : P →* J) (_hq : Function.Surjective q)
    (ρ : J →* (V ≃ₗ[K] V)) (x : ℙ K V)
    (_hx : ∀ p ∈ L, ρ (q p) • x = x)
    (_hcont : Continuous (fun p : P ↦ ρ (q p) • x))
    (_hact : ∀ j : J, Continuous (ρ j : V → V)),
    LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure L →
    ∃ ν : Measure (ℙ K V), IsFiniteMeasure ν ∧
      (∀ j : J, MeasurePreserving (ρ j • ·) ν ν) ∧
      ν.support = closure (Set.range fun j : J ↦ ρ j • x) ∧
      (CompactSpace (P ⧸ L) → T2Space (ℙ K V) → ν.support = Set.range fun j : J ↦ ρ j • x)

/-- Every conjugate of an evaluation of the indicated weight type fixes the
lattice-fixed line. The representation here can be the exterior representation. -/
def ConjugatesFixOrbitLine : Prop :=
  ∀ {P J K V ι : Type*} [Group P] [Group J] [NormedField K] [AddCommGroup V] [Module K V]
    [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace V]
    (L : Subgroup P) (q : P →* J) (_hq : Function.Surjective q)
    (ρ : J →* (V ≃ₗ[K] V)) (x : ℙ K V)
    (_hx : ∀ p ∈ L, ρ (q p) • x = x)
    (_hcont : Continuous (fun p : P ↦ ρ (q p) • x))
    (_hact : ∀ j : J, Continuous (ρ j : V → V)),
    LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure L →
    ∀ (a : J) (b : V ≃ₗ[K] (ι → K)), Continuous b →
    ∀ d : ι → K, (∀ v i, b (ρ a v) i = d i * b v i) →
    (∀ i j, ‖d i‖ = ‖d j‖ → d i = d j) →
    ∀ g : J, ρ (g * a * g⁻¹) • x = x

/-- Cocharacter conjugates and the elements they contract preserve a subspace fixed by the
projected lattice.
Weights on the exterior power are the sums of the original weights. -/
def ConjugatesPreserveSubspace : Prop :=
  ∀ {P J K V ι : Type*} [Group P] [Group J] [NormedField K] [AddCommGroup V] [Module K V]
    [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace J] [IsTopologicalGroup J]
    [Fintype ι] [LinearOrder ι]
    (L : Subgroup P) (q : P →* J), Function.Surjective q → Continuous q →
    (∀ ρ : J →* (V ≃ₗ[K] V), ∀ b : Module.Basis ι K V,
      (∀ v i, Continuous (fun j : J ↦ b.coord i (ρ j v))) →
      ∀ W : Submodule K V, (∀ p ∈ L, ∀ v ∈ W, ρ (q p) v ∈ W) →
      LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure L →
      ∀ (a : J) (t : K), t ≠ 0 → ‖t‖ ≠ 1 →
      ∀ w : ι → ℤ, (∀ i, ρ a (b i) = t ^ (w i) • b i) →
      (∀ g : J, ∀ v ∈ W, ρ (g * a * g⁻¹) v ∈ W) ∧
      (∀ g u : J, Tendsto (fun n : ℕ ↦ (g * a * g⁻¹) ^ n * u * ((g * a * g⁻¹) ^ n)⁻¹)
        atTop (𝓝 1) → ∀ v ∈ W, ρ u v ∈ W))

/-- If all conjugates preserve a projective line, the stabilizer of the line
contains every element contracted by the given evaluations. -/
def ContractedElementsFixLine : Prop :=
  ∀ {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [T1Space X] [MulAction G X]
    (x : X) (_hcont : Continuous (fun g : G ↦ g • x))
    (A : Set G) (_h : ∀ a ∈ A, ∀ g : G, (g * a * g⁻¹) • x = x)
    {a u : G}, a ∈ A →
      Tendsto (fun n : ℕ ↦ a ^ n * u * (a ^ n)⁻¹) atTop (𝓝 1) → u • x = x

/-- A closed normal subgroup containing an element also contains every element it contracts. -/
def ContainsContractedElements : Prop :=
  ∀ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (_hN : IsClosed (N : Set G)) {a u : G},
    a ∈ N → Tendsto (fun n : ℕ ↦ a ^ n * u * (a ^ n)⁻¹) atTop (𝓝 1) → u ∈ N

/-- The closure of the normal subgroup generated by the evaluations contains
every element contracted by one of them. -/
def NormalClosureContainsContracted : Prop :=
  ∀ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Set G)
    {a u : G}, a ∈ A →
      Tendsto (fun n : ℕ ↦ a ^ n * u * (a ^ n)⁻¹) atTop (𝓝 1) →
      u ∈ (Subgroup.normalClosure A).topologicalClosure

/-- Simplicity of a nonabelian Lie algebra survives restriction of scalars.
The two Lie algebra structures use the same underlying Lie ring. -/
def SimpleAfterRestriction : Prop :=
  ∀ {F E L : Type*} [Field F] [Field E] [LieRing L]
    [LieAlgebra F L] [LieAlgebra E L], LieAlgebra.IsSimple E L → LieAlgebra.IsSimple F L

/-- An open cocompact subgroup contains every element contracted to the identity
by positive powers of any element of the ambient group. -/
def CocompactOpenContainsContracted : Prop :=
  ∀ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [CompactSpace (G ⧸ H)], IsOpen (H : Set G) →
    ∀ {a u : G},
      Tendsto (fun n : ℕ ↦ a ^ n * u * (a ^ n)⁻¹) atTop (𝓝 1) → u ∈ H

/-- A cocompact open subgroup has finite index and contains each subgroup whose elements
have roots of all positive integer orders. -/
def ContainsDivisibleSubgroups : Prop :=
  ∀ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) [CompactSpace (G ⧸ H)] (_hH : IsOpen (H : Set G)),
    H.FiniteIndex ∧ ∀ U : Subgroup G, (∀ u : U, ∀ n : ℕ, 0 < n → ∃ v : U, v ^ n = u) → U ≤ H

section LocalProjections

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData NumberFinitePlace)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups
open LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization RationalPoints)
open LinearAlgebraicGroups.Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsUnipotentRadical)
open LinearAlgebraicGroups.Specs.CharacterDescent (Cocharacter)

universe u

/-- The union in the rational point group of the images of all rational parabolic
unipotent radicals. -/
def parabolicRadicalPoints {F : Type u} [Field F] (G : AffineAlgebraicGroup F) :
    Set (RationalPoints G) :=
  {g | ∃ (P : ClosedSubgroup G.val), BorelProper.IsParabolic G P ∧
      ∃ U : ClosedSubgroup P.group, IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U ∧
        g ∈ ((((groupPointsFunctor F).map (U.inclusion ≫ P.inclusion)).app
          (CommAlgCat.of F F)).hom).range}

/-- The union of the rational points of the contracting subgroups of rational
cocharacters. -/
def cocharacterRadicalPoints {F : Type u} [Field F] (G : AffineAlgebraicGroup F) :
    Set (RationalPoints G) :=
  {g | ∃ (c : Cocharacter G.val) (D : LimitDecomposition c),
    g ∈ ((((groupPointsFunctor F).map D.contracting.inclusion).app
      (CommAlgCat.of F F)).hom).range}

/-- A nondiscrete closed subgroup of finite covolume in an isotropic absolutely almost
simple p-adic group is open. If it is cocompact, it has finite index and contains the
subgroup generated by the local parabolic radicals. -/
def PadicProjection : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {F : Type u} [NormedField F] [CharZero F] [NormedAlgebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] (G : AffineAlgebraicGroup F) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → 0 < RelativeRank.relativeRank G →
    ∀ (H : Subgroup (PointsIn i F)), IsClosed (H : Set (PointsIn i F)) →
      ¬ DiscreteTopology H →
      LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure H →
      IsOpen (H : Set (PointsIn i F)) ∧
      (CompactSpace (PointsIn i F ⧸ H) →
        H.FiniteIndex ∧ Subgroup.closure (parabolicRadicalPoints G) ≤ H ∧
        (Dense (↑(Subgroup.closure (G := PointsIn i F) (parabolicRadicalPoints G)) :
          Set (PointsIn i F)) → H = ⊤))

/-- Interpret points of the scalar-extended scheme as points at the original
completion, by forgetting the factorization through the extension field. -/
def localPointSet {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place)
    (A : Set (RationalPoints (baseChangedAlgebraicGroup (D.Completion w) G))) :
    Set (LocalPoints D i w) :=
  {g | ∃ p ∈ A,
    (show Points G.val.X (CommAlgCat.of K (D.Completion w)) from g).left =
      (baseChangePoint K (D.Completion w) G.val.X (CommAlgCat.of (D.Completion w) (D.Completion w))
        p).left}

/-- The projection of the finite product to the indicated place. -/
def evaluatePlace {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) {T : Finset D.Place} {w : D.Place}
    (h : w ∈ T) : FinitePoints D i T →* LocalPoints D i w where
  toFun g := g ⟨w, h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The nondiscrete cocompact lattice projection to an isotropic finite
place is open and contains the subgroup generated by all parabolic radicals. -/
def PadicLatticeProjection : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (D : GlobalFieldData.{u, u} K), D = .number inferInstance →
    ∀ (w : D.FinitePlace) (S T : Finset D.Place) (U : Subgroup (Adeles D i T)),
      S ⊆ T → Sum.inl w ∉ S → ∀ hv : Sum.inl w ∈ T,
      CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) →
      ¬ CompactSpace (FinitePoints D i S) →
      IsCompact (U : Set (Adeles D i T)) → IsOpen (U : Set (Adeles D i T)) →
      IsAbsolutelyAlmostSimple G →
      0 < RelativeRank.relativeRank (baseChangedAlgebraicGroup (D.Completion (.inl w)) G) →
      let L := lattice D i T U
      let A := Subgroup.closure (localPointSet D i (.inl w) (parabolicRadicalPoints
        (baseChangedAlgebraicGroup (D.Completion (.inl w)) G)))
      ∃ H : Subgroup (LocalPoints D i (.inl w)),
        (H : Set (LocalPoints D i (.inl w))) =
          closure ((L.map (evaluatePlace D i hv) : Subgroup _) : Set _) ∧
        IsOpen (H : Set (LocalPoints D i (.inl w))) ∧ H.FiniteIndex ∧ A ≤ H ∧
        (Dense (A : Set (LocalPoints D i (.inl w))) → H = ⊤)

/-- Project onto the selected archimedean places. -/
def evaluateArchimedean {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) {T : Finset D.Place}
    (A : Finset D.InfinitePlace) (h : ∀ w : ↑A, Sum.inr w.val ∈ T) :
    FinitePoints D i T →* (∀ w : ↑A, LocalPoints D i (.inr w.val)) where
  toFun g w := g ⟨.inr w.val, h w⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- For the nonempty archimedean product, dense generation of the factors by
the contracted radicals gives density of the lattice projection. -/
def ArchimedeanLatticeProjection : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (D : GlobalFieldData.{u, u} K), D = .number inferInstance →
    ∀ (S T : Finset D.Place) (A : Finset D.InfinitePlace) (U : Subgroup (Adeles D i T)),
      S ⊆ T → A.Nonempty → (∀ w : ↑A, Sum.inr w.val ∉ S) →
      ∀ hA : ∀ w : ↑A, Sum.inr w.val ∈ T,
      CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) →
      ¬ CompactSpace (FinitePoints D i S) →
      IsCompact (U : Set (Adeles D i T)) → IsOpen (U : Set (Adeles D i T)) →
      IsAbsolutelyAlmostSimple G →
      (∀ w : ↑A, Dense (↑(Subgroup.closure
        (localPointSet D i (.inr w.val)
          (cocharacterRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inr w.val)) G)))) :
        Set (LocalPoints D i (.inr w.val)))) →
      Dense (↑((lattice D i T U).map (evaluateArchimedean D i A hA)) :
        Set (∀ w : ↑A, LocalPoints D i (.inr w.val)))

end LocalProjections

end LinearAlgebraicGroups.Specs.Arithmetic.ProjectiveRecurrence
