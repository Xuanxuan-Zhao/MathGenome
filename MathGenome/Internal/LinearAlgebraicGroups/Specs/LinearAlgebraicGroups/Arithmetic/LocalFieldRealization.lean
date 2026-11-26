import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.Padics.LocalField

open AlgebraicGeometry CategoryTheory Filter MeasureTheory
open scoped InnerProductSpace Matrix RatFunc TensorProduct Topology Valued

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.LocalFieldRealization

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.RootGroups (AdditiveLine rootPoint)
open CocharacterDynamics (cocharacterPoint unitPoint)
open LocalAlgebraicTransport (RationalPoints originalPoint pointTopology scalarStructure
  transportedSubgroup IsUniformizingUnit coordinatePullback coordinateAlgebra evaluation
  transportedInvolution PreservesQuaternionicQuadraticForm IsCliffordTransport)
open LocalQuotientTransport (Equivariant RightCosets coset rightTranslate imageSubgroup
  RightInvariant L2 rightOperator closedNormalClosure)

/-- Compatibility of a chosen completion isomorphism with the two given topologies
and valuations. -/
def IsRealization {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {K : Type v} [Field K] (D : GlobalFieldData.{v, u} K) (w : D.FinitePlace)
    (e : D.FiniteCompletion w ≃+* F) : Prop :=
  Continuous e ∧ Continuous e.symm ∧
    (∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) ∧
    ∀ x, x ∈ D.integers w ↔ e x ∈ (ValuativeRel.valuation F).valuationSubring

/-- Realization at a designated finite place with its canonical completion topology
and valuation relation. -/
def Realizes (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    {K : Type v} [Field K] (D : GlobalFieldData.{v, u} K) (w : D.FinitePlace) : Prop :=
  ∃ e : D.FiniteCompletion w ≃+* F, IsRealization D w e

/-- A dense embedded number field realizes the given local field at a finite place.
The completion isomorphism extends the specified embedding of global scalars. -/
def DenseNumberFieldCompletion : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (K : Type v) [Field K] [NumberField K]
    (i : K →+* F), DenseRange i →
    let D : GlobalFieldData.{v, u} K := .number inferInstance
    ∃ (w : D.FinitePlace) (e : D.FiniteCompletion w ≃+* F),
      Continuous e ∧ Continuous e.symm ∧
      (∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) ∧
      (∀ x, x ∈ D.integers w ↔ e x ∈ (ValuativeRel.valuation F).valuationSubring) ∧
      ∀ x, e (D.embedding (.inl w) x) = i x

/-- The finite-place realization of an arbitrary nonarchimedean local field. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    ∃ (K : Type u) (_ : Field K) (D : GlobalFieldData.{u, u} K) (w : D.FinitePlace),
      Realizes F D w

/-- In positive characteristic the global model uses the actual residue field as constants
and the (X)-adic place of its rational function field. -/
def EqualCharacteristic : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [CharP F p],
    let k := IsLocalRing.ResidueField (ValuativeRel.valuation F).valuationSubring
    letI : Finite k :=
      IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation F
    ∃ (t : SeparatingParameter k k⟮X⟯) (w : FunctionPlace k⟮X⟯),
      t.element = RatFunc.X ∧ w.1 = (RatFunc.polynomialValuationX k).valuationSubring ∧
        Realizes F (GlobalFieldData.function k t) w

/-- The characteristic-zero local field is a finite extension of the (p)-adic
field for its residue characteristic, with the original topology and valuation. -/
def PadicExtension : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    ∃ (p : ℕ) (hp : Fact p.Prime),
      letI := hp
      CharP (IsLocalRing.ResidueField (ValuativeRel.valuation F).valuationSubring) p ∧
      ∃ f : ℚ_[p] →+* F,
        letI := f.toAlgebra
        Continuous f ∧ (∀ x y, f x ≤ᵥ f y ↔ x ≤ᵥ y) ∧
          ContinuousSMul ℚ_[p] F ∧ FiniteDimensional ℚ_[p] F

/-- Comparison of the right-translation representations for a chosen quotient
map and its pushforward measure. -/
def RepresentationAlong {A B : Type u} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B]
    (f : A ≃ₜ* B) {H : Subgroup A} {H' : Subgroup B} (q : RightCosets H ≃ₜ RightCosets H')
    (μ : Measure (RightCosets H)) (hμ : RightInvariant μ) (hν : RightInvariant (μ.map q)) : Prop :=
  ∃ U : L2 μ ≃ₗᵢ[ℂ] L2 (μ.map q),
    (∀ v : L2 μ, (U v : RightCosets H' → ℂ) =ᵐ[μ.map q] (v ∘ q.symm)) ∧
    (∀ v : L2 (μ.map q), (U.symm v : RightCosets H → ℂ) =ᵐ[μ] (v ∘ q)) ∧
    (∀ (a : A) (v : L2 μ), U (rightOperator hμ a v) = rightOperator hν (f a) (U v)) ∧
    (∀ (a : A) (v z : L2 μ),
      ⟪rightOperator hν (f a) (U v), U z⟫_ℂ = ⟪rightOperator hμ a v, z⟫_ℂ) ∧
    (∀ {ι : Type w} (l : Filter ι) (a : ι → A) (v z : L2 μ) (c : ℂ),
      Tendsto (fun i => ⟪rightOperator hν (f (a i)) (U v), U z⟫_ℂ) l (𝓝 c) ↔
        Tendsto (fun i => ⟪rightOperator hμ (a i) v, z⟫_ℂ) l (𝓝 c)) ∧
    (∀ (c : ℂ) (v : L2 μ), (U v : RightCosets H' → ℂ) =ᵐ[μ.map q] (fun _ => c) ↔
      (v : RightCosets H → ℂ) =ᵐ[μ] (fun _ => c)) ∧
    (∀ v : L2 μ, Continuous (fun b : B => rightOperator hν b (U v)) ↔
      Continuous (fun a : A => rightOperator hμ a v)) ∧
    (∀ {ι : Type w} (l : Filter ι) (a : ι → A) (T : L2 μ →WOT[ℂ] L2 μ),
      let V := U.toContinuousLinearEquiv
      let T' := ContinuousLinearMapWOT.ofCLM
        (V.toContinuousLinearMap.comp (T.toCLM.comp V.symm.toContinuousLinearMap))
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM
        (rightOperator hν (f (a i))).toContinuousLinearMap) l (𝓝 T') ↔
        Tendsto (fun i => ContinuousLinearMapWOT.ofCLM
          (rightOperator hμ (a i)).toContinuousLinearMap) l (𝓝 T))

/-- Subgroup, quotient, measure, and limit comparisons for a single isomorphism
of topological groups. -/
def QuotientTransportAlong {A B : Type u} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B]
    (f : A ≃ₜ* B) : Prop :=
  (∀ s : Set A, imageSubgroup f (closedNormalClosure s) = closedNormalClosure (f '' s)) ∧
  (∀ {ι : Type w} (l : Filter ι) (g : ι → A) (x : A),
    Tendsto (f ∘ g) l (𝓝 (f x)) ↔ Tendsto g l (𝓝 x)) ∧
  (∀ {ι : Type w} (l : Filter ι) (a : A) (n : ι → ℕ) (y h : ι → A) (r : A),
    Tendsto (fun i => (f a ^ n i)⁻¹ * (f (y i))⁻¹ * f (h i) * f (y i) * f a ^ n i)
      l (𝓝 (f r)) ↔
      Tendsto (fun i => (a ^ n i)⁻¹ * (y i)⁻¹ * h i * y i * a ^ n i) l (𝓝 r)) ∧
  ∀ H : Subgroup A,
    let H' := imageSubgroup f H
    (∀ a : A, f a ∈ H' ↔ a ∈ H) ∧
    (IsClosed (H : Set A) ↔ IsClosed (H' : Set B)) ∧
    (DiscreteTopology H ↔ DiscreteTopology H') ∧
    ∃ q : RightCosets H ≃ₜ RightCosets H',
      (∀ a : A, q (coset H a) = coset H' (f a)) ∧ Equivariant f q ∧
      (∀ {ι : Type w} (l : Filter ι) (g : ι → RightCosets H) (x : RightCosets H),
        (Tendsto (q ∘ g) l (𝓝 (q x)) ↔ Tendsto g l (𝓝 x)) ∧
        ∀ a : ι → A,
          Tendsto (fun i => rightTranslate (f (a i)) (q (g i))) l (𝓝 (q x)) ↔
            Tendsto (fun i => rightTranslate (a i) (g i)) l (𝓝 x)) ∧
      ∀ (μ : Measure (RightCosets H)) (hμ : RightInvariant μ) [IsFiniteMeasure μ], μ ≠ 0 →
        IsFiniteMeasure (μ.map q) ∧ μ.map q ≠ 0 ∧
        ∃ hν : RightInvariant (μ.map q),
          (∀ s : Set (RightCosets H'), (μ.map q) s = μ (q ⁻¹' s)) ∧
          RepresentationAlong.{u, w} f q μ hμ hν

/-- Compatibility of the canonical base change of the marked algebraic data
with the field isomorphism. -/
def MarkedGroupTransportAlong {F E : Type u} [Field F] [Field E]
    [ValuativeRel F] [ValuativeRel E] (e : F ≃+* E) : Prop :=
  letI := scalarStructure e
  (∀ π : Fˣ, IsUniformizingUnit (Units.map e.toMonoidHom π) ↔ IsUniformizingUnit π) ∧
  ((groupBaseChange F E).IsEquivalence ∧
    ∀ {G J : GroupScheme F} (f : G ⟶ J),
      IsClosedImmersion ((groupBaseChange F E).map f).hom.hom.left ↔
        IsClosedImmersion f.hom.hom.left) ∧
  (∀ {X Y : SchemeOver F} (f : X ⟶ Y) (p : RationalPoints ((baseChange F E).obj X)),
    originalPoint e Y (p ≫ (baseChange F E).map f) = originalPoint e X p ≫ f) ∧
  (∀ (G : AffineAlgebraicGroup F) (P : ClosedSubgroup G.val),
    let G' := Specs.Unipotent.baseChangedAlgebraicGroup E G
    let P' := transportedSubgroup F E P
    (Specs.BorelProper.IsParabolic G' P' ↔ Specs.BorelProper.IsParabolic G P) ∧
    (Specs.GeometricRadicals.IsUnipotentRadical G' P' ↔
      Specs.GeometricRadicals.IsUnipotentRadical G P) ∧
    ∀ p : RationalPoints G'.val.X,
      (∃ q : RationalPoints P'.group.X, q ≫ P'.inclusion.hom.hom = p) ↔
      (∃ q : RationalPoints P.group.X, q ≫ P.inclusion.hom.hom = originalPoint e G.val.X p)) ∧
  (∀ {G : GroupScheme F} (c : Cocharacter G),
    let M := specGroup (groupAlgebra F IntegerCharacters)
    ∃ i : specGroup (groupAlgebra E IntegerCharacters) ≅ (groupBaseChange F E).obj M,
      (∀ (R : TestAlgebra E) (s : Rˣ),
        baseChangePoint F E M.X R (unitPoint R s ≫ i.hom.hom.hom) =
          unitPoint ((restrictTestAlgebra F E).obj R) s) ∧
      let c' : Cocharacter ((groupBaseChange F E).obj G) := i.hom ≫ (groupBaseChange F E).map c
      ∀ s : Fˣ,
        originalPoint e G.X (cocharacterPoint c' (CommAlgCat.of E E) (Units.map e.toMonoidHom s)) =
          cocharacterPoint c (CommAlgCat.of F F) s) ∧
  ∀ {G : GroupScheme F} {A : AdditiveLine F} (x : A.group ⟶ G),
    ∃ param : ∀ R : TestAlgebra E, R ≃ GroupPoints ((groupBaseChange F E).obj A.group) R,
      (∀ (R : TestAlgebra E) (a : R),
        baseChangePoint F E A.group.X R (param R a) =
          rootPoint (𝟙 A.group) ((restrictTestAlgebra F E).obj R) a ∧
        baseChangePoint F E G.X R (param R a ≫ ((groupBaseChange F E).map x).hom.hom) =
          rootPoint x ((restrictTestAlgebra F E).obj R) a) ∧
      (∀ {R S : TestAlgebra E} (f : R ⟶ S) (a : R),
        mapPoints f (param R a) = param S (f.hom a)) ∧
      (∀ (R : TestAlgebra E) (a b : R), param R (a + b) = param R a * param R b) ∧
      ∀ a : F,
        originalPoint e G.X
          (param (CommAlgCat.of E E) (e a) ≫ ((groupBaseChange F E).map x).hom.hom) =
          rootPoint x (CommAlgCat.of F F) a

/-- The entrywise topology for a matrix presentation with the inverse
determinant among its affine coordinates. -/
def MatrixModelTopology (F : Type u) [Field F] [TopologicalSpace F] : Prop :=
  ∀ (X : SchemeOver F) {n : Type u} [Fintype n] [DecidableEq n]
    (c : Matrix n n Γ(X.left, ⊤)) (d : Γ(X.left, ⊤)),
    letI := coordinateAlgebra X
    let m := fun p : RationalPoints X ↦ c.map (evaluation p)
    Algebra.adjoin F (insert d (Set.range fun ij : n × n ↦ c ij.1 ij.2)) = ⊤ →
      (∀ p, (m p).det ≠ 0) →
      (∀ p, evaluation p d = (m p).det⁻¹) →
      pointTopology X = TopologicalSpace.induced m inferInstance

section QuaternionicSpin

open CategoryTheory.Limits CliffordAlgebra LocalAlgebraicTransport
open Specs.DiagonalizableGroups (rootsOfUnityPoints)
open scoped CategoryTheory.MonObj

/-- The action on an ordered list of pairs of vectors has one inverse multiplier per
pair. Pairing consecutive vectors represents any even product. -/
def IsEvenProductAction {S V : Type u} [CommRing S] [AddCommGroup V] [Module S V]
    (Q : QuadraticForm S V) (s : V → V) (c : Sˣ) (a : even Q ≃+* even Q) : Prop :=
  ∀ pairs : List (V × V),
    a (pairs.map (fun p ↦ (even.ι Q).bilin p.1 p.2)).prod =
      algebraMap S (even Q) ((↑c⁻¹ : S) ^ pairs.length) *
        (pairs.map (fun p ↦ (even.ι Q).bilin (s p.1) (s p.2))).prod

noncomputable section

variable {F E B L n m J : Type u} [Field F] [Field E] [Ring B] [Algebra F B]
  [Field L] [Algebra F L] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {G I : GroupScheme F} {π : G ⟶ I}
  (e : F ≃+* E) (D : QuaternionicSpinCoverPresentation F B L n m J π)

set_option backward.isDefEq.respectTransparency false in
/-- The two charts use the same test algebra, with the quaternionic and splitting
coefficients extended directly from the original field and through the new base field. -/
abbrev SpinChartComparisonAlong (R : TestAlgebra E) :=
  letI := scalarStructure e
  let R₀ := (restrictTestAlgebra F E).obj R
  QuaternionicSpinChartComparison (S := R₀ ⊗[F] L) (T := R ⊗[E] (E ⊗[F] L))
    (testAlgebraRebase e R B) (testAlgebraRebase e R L) (D.chart R₀)

set_option backward.isDefEq.respectTransparency false in
/-- The covering coordinates of a point of the actual base-changed group. -/
abbrev spinPointAlong {R : TestAlgebra E} (C : SpinChartComparisonAlong e D R) :
    letI := scalarStructure e
    GroupPoints ((groupBaseChange F E).obj G) R → C.chart.CoverPoints :=
  letI := scalarStructure e
  fun p ↦ C.cover (D.spin ((restrictTestAlgebra F E).obj R) (baseChangePoint F E G.X R p))

set_option backward.isDefEq.respectTransparency false in
/-- The quaternionic matrix of a point of the actual base-changed vector group. -/
abbrev vectorPointAlong (R : TestAlgebra E) :
    letI := scalarStructure e
    GroupPoints ((groupBaseChange F E).obj I) R → (Matrix n n (R ⊗[E] (E ⊗[F] B)))ˣ :=
  letI := scalarStructure e
  fun p ↦ Units.map ((testAlgebraRebase e R B).toRingEquiv.mapMatrix (m := n)).toMonoidHom
    (D.vector ((restrictTestAlgebra F E).obj R) (baseChangePoint F E I.X R p))

/-- A test-algebra scalar inside the even Clifford units of a split chart. -/
abbrev scalarCliffordUnit {R S V : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module S V] (Q : QuadraticForm S V) (z : Rˣ) : (even Q)ˣ :=
  Units.map ((algebraMap S (even Q)).comp (algebraMap R S)) z

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison with the spin cover of the transported coefficients. All
parts use the same point comparison and the same split charts on test algebras. -/
structure IsQuaternionicSpinTransport (C : ∀ R : TestAlgebra E, SpinChartComparisonAlong e D R) :
    Prop where
  cover (R : TestAlgebra E) :
    letI := scalarStructure e
    let K := groupBaseChange F E
    ∃ spin : GroupPoints (K.obj G) R ≃ (C R).chart.CoverPoints,
      (∀ p, spin p = spinPointAlong e D (C R) p) ∧
      (∀ p q, (spin (p * q)).val = (spin p).val * (spin q).val) ∧
    ∃ vector : GroupPoints (K.obj I) R →* (Matrix n n (R ⊗[E] (E ⊗[F] B)))ˣ,
      Function.Injective vector ∧ (∀ p, vector p = vectorPointAlong e D R p) ∧
      (∀ p, vector (p ≫ (K.map π).hom.hom) = (spin p).val.1) ∧
      (∀ p, (p ≫ (K.map π).hom.hom : GroupPoints (K.obj I) R) = 1 ↔ (spin p).val.1 = 1) ∧
      (∀ p, (p ≫ (K.map π).hom.hom : GroupPoints (K.obj I) R) = 1 ↔
        ∃ z : rootsOfUnity 2 R, (spin p).val.2 = scalarCliffordUnit (C R).chart.form z.val) ∧
      (∀ p q, (p ≫ (K.map π).hom.hom : GroupPoints (K.obj I) R) = 1 → Commute p q) ∧
      ∀ {U : GroupScheme F} (x : U ⟶ G) (p : GroupPoints (K.obj U) R),
        spin (p ≫ (K.map x).hom.hom) =
          (C R).cover (D.spin ((restrictTestAlgebra F E).obj R)
            (baseChangePoint F E U.X R p ≫ x.hom.hom))
  descent (R : TestAlgebra E) :
    letI := scalarStructure e
    let D₀ := D.chart ((restrictTestAlgebra F E).obj R)
    let D' := (C R).chart
    let j := testAlgebraRebase e R L
    (∀ a, IsEvenProductAction D₀.form (D₀.vectorAction a) (D₀.multiplier a) (D₀.evenAction a) ∧
      IsEvenProductAction D'.form (D'.vectorAction a) (D'.multiplier a) (D'.evenAction a)) ∧
    (∀ M, D'.IsFixedSplitMatrix (M.map j) ↔ D₀.IsFixedSplitMatrix M) ∧
    (Set.range D'.splitMatrix = {M | D'.IsFixedSplitMatrix M} ↔
      Set.range D₀.splitMatrix = {M | D₀.IsFixedSplitMatrix M}) ∧
    ∃ d : D₀.fixedEven ≃+* D'.fixedEven, ∀ x, (d x).val = (C R).evenEquiv x.val
  galoisAction (R : TestAlgebra E) (a : J) (σ : L ≃ₐ[F] L) :
    letI := scalarStructure e
    let R₀ := (restrictTestAlgebra F E).obj R
    (∀ (r : R₀) (t : L), (D.chart R₀).scalarAction a (r ⊗ₜ[F] t) = r ⊗ₜ[F] σ t) →
    ∀ (r : R) (s : E) (t : L),
      (C R).chart.scalarAction a (r ⊗ₜ[E] (s ⊗ₜ[F] t)) = r ⊗ₜ[E] (s ⊗ₜ[F] σ t)
  naturality {R S : TestAlgebra E} (a : R ⟶ S) :
    letI := scalarStructure e
    let K := groupBaseChange F E
    let a₀ := (restrictTestAlgebra F E).map a
    let f := (C S).evenEquiv.toRingHom.comp ((D.cliffordMap a₀).comp (C R).evenEquiv.symm.toRingHom)
    let g := extendTestCoefficients a (E ⊗[F] L)
    let b := extendTestCoefficients a (E ⊗[F] B)
    (∀ t : R ⊗[E] (E ⊗[F] L), f (algebraMap _ (even (C R).chart.form) t) =
      algebraMap _ (even (C S).chart.form) (g t)) ∧
    (∀ v w : m → R ⊗[E] (E ⊗[F] L), f ((even.ι (C R).chart.form).bilin v w) =
      (even.ι (C S).chart.form).bilin (g ∘ v) (g ∘ w)) ∧
    (∀ p : GroupPoints (K.obj G) R,
      let pR := spinPointAlong e D (C R) p
      let pS := spinPointAlong e D (C S) (mapPoints a p)
      pS.val.1 = Units.map (b.toRingHom.mapMatrix (m := n)).toMonoidHom pR.val.1 ∧
        pS.val.2 = Units.map f pR.val.2) ∧
    ∀ p : GroupPoints (K.obj I) R,
      vectorPointAlong e D S (mapPoints a p) =
        Units.map (b.toRingHom.mapMatrix (m := n)).toMonoidHom (vectorPointAlong e D R p)
  rational :
    letI := scalarStructure e
    let K := groupBaseChange F E
    let R := CommAlgCat.of E E
    let R₀ := (restrictTestAlgebra F E).obj R
    let R_F := CommAlgCat.of F F
    let a : R_F ⟶ R₀ := CommAlgCat.ofHom
      { toRingHom := e.toRingHom, commutes' := fun _ ↦ rfl }
    let lid := (Algebra.TensorProduct.lid E (E ⊗[F] B)).toRingHom
    let b := lid.comp ((testAlgebraRebase e R B).toRingHom.comp (extendTestCoefficients a B).toRingHom)
    let t := (testAlgebraRebase e R L).toRingHom.comp (extendTestCoefficients a L).toRingHom
    let d := (C R).evenEquiv.toRingHom.comp (D.cliffordMap a)
    (∀ (r : F) (z : B), b (r ⊗ₜ[F] z) = e r ⊗ₜ[F] z) ∧
    (∀ (r : F) (z : L), t (r ⊗ₜ[F] z) = e r ⊗ₜ[E] ((1 : E) ⊗ₜ[F] z)) ∧
    Function.Bijective d ∧
    (∀ p : RationalPoints (K.obj G).X,
      let x := spinPointAlong e D (C R) p
      let y := D.spin R_F (originalPoint e G.X p)
      Units.map lid.mapMatrix.toMonoidHom x.val.1 = Units.map (b.mapMatrix (m := n)).toMonoidHom y.val.1 ∧
        x.val.2 = Units.map d y.val.2) ∧
    ∀ p : RationalPoints (K.obj I).X,
      Units.map lid.mapMatrix.toMonoidHom (vectorPointAlong e D R p) =
        Units.map (b.mapMatrix (m := n)).toMonoidHom (D.vector R_F (originalPoint e I.X p))
  isometry {O : GroupScheme F} (incl : I ⟶ O)
      (V : QuaternionicSpinIsometryPresentation F B L n m J D incl) :
    letI := scalarStructure e
    let K := groupBaseChange F E
    let incl' := K.map incl
    let π' := (K.map π).hom.hom.left
    ((IsFinite π' ∧ Flat π' ∧ Surjective π') ↔
      (IsFinite π.hom.hom.left ∧ Flat π.hom.hom.left ∧ Surjective π.hom.hom.left)) ∧
    (IsOpenImmersion incl'.hom.hom.left ∧
      Set.range incl'.hom.hom.left = connectedComponent (identitySchemePoint (K.obj O)) ↔
      IsOpenImmersion incl.hom.hom.left ∧
      Set.range incl.hom.hom.left = connectedComponent (identitySchemePoint O)) ∧
    ∀ R : TestAlgebra E,
      let R₀ := (restrictTestAlgebra F E).obj R
      let f := (testAlgebraRebase e R B).mapMatrix (m := n)
      let σ' := f ∘ V.adjoint R₀ ∘ f.symm
      let ℓ' := (V.semitrace R₀).map f
      ∃ coordinates : GroupPoints (K.obj O) R →* (Matrix n n (R ⊗[E] (E ⊗[F] B)))ˣ,
        Function.Injective coordinates ∧
        (∀ p, coordinates p = Units.map f.toMonoidHom
          (V.coordinates R₀ (baseChangePoint F E O.X R p))) ∧
        (C R).chart.IsAdjoint σ' ∧
        (∀ ℓ, ℓ' = some ℓ → (C R).chart.IsSemitraceRepresentative ℓ) ∧
        (∀ M, M ∈ Set.range coordinates ↔ (C R).chart.IsIsometry σ' ℓ' M) ∧
        ∀ p : GroupPoints (K.obj G) R,
          coordinates ((p ≫ (K.map π).hom.hom) ≫ incl'.hom.hom) =
            (spinPointAlong e D (C R) p).val.1
  scalarKernel {Z U : GroupScheme F} (z : Z ⟶ G) (p : Z ⟶ U) (unitInclusion : U ⟶ I)
      (h : (groupPointsFunctor F).obj Z ≅ rootsOfUnityPoints F 2) :
    IsTerminal U → IsPullback z p π unitInclusion →
    (∀ (R : TestAlgebra F) (q : GroupPoints Z R),
      let x := D.spin R (q ≫ z.hom.hom)
      x.val.1 = 1 ∧ x.val.2 = scalarCliffordUnit (D.chart R).form (h.hom.app R q).val) →
    letI := scalarStructure e
    let K := groupBaseChange F E
    IsPullback (K.map z) (K.map p) (K.map π) (K.map unitInclusion) ∧
      Nonempty (IsTerminal (K.obj U)) ∧
    ∃ h' : (groupPointsFunctor E).obj (K.obj Z) ≅ rootsOfUnityPoints E 2,
      ∀ (R : TestAlgebra E) (q : GroupPoints (K.obj Z) R),
        let R₀ := (restrictTestAlgebra F E).obj R
        let x := spinPointAlong e D (C R) (q ≫ (K.map z).hom.hom)
        h'.hom.app R q = h.hom.app R₀ (baseChangePoint F E Z.X R q) ∧ x.val.1 = 1 ∧
          x.val.2 = scalarCliffordUnit (C R).chart.form (h'.hom.app R q).val
  marked {A : AdditiveLine F} (x : A.group ⟶ G) (c : Cocharacter G) :
    letI := scalarStructure e
    let K := groupBaseChange F E
    let M := specGroup (groupAlgebra F IntegerCharacters)
    ∃ param : ∀ R : TestAlgebra E, R ≃ GroupPoints (K.obj A.group) R,
      ∃ torus : specGroup (groupAlgebra E IntegerCharacters) ≅ K.obj M,
        let c' : Cocharacter (K.obj G) := torus.hom ≫ K.map c
        (∀ a : F, originalPoint e G.X
          (param (CommAlgCat.of E E) (e a) ≫ (K.map x).hom.hom) =
            rootPoint x (CommAlgCat.of F F) a) ∧
        (∀ s : Fˣ, originalPoint e G.X
          (cocharacterPoint c' (CommAlgCat.of E E) (Units.map e.toMonoidHom s)) =
            cocharacterPoint c (CommAlgCat.of F F) s) ∧
        ∀ R : TestAlgebra E,
          let R₀ := (restrictTestAlgebra F E).obj R
          (∀ a : R, spinPointAlong e D (C R) (param R a ≫ (K.map x).hom.hom) =
            (C R).cover (D.spin R₀ (rootPoint x R₀ a))) ∧
          ∀ s : Rˣ, spinPointAlong e D (C R) (cocharacterPoint c' R s) =
            (C R).cover (D.spin R₀ (cocharacterPoint c R₀ s))

end

/-- Transport the marked quaternionic spin cover along the specified field
isomorphism, including its vector target, scalar scheme kernel and lifted maps. -/
def QuaternionicSpinTransportAlong {F E : Type u} [Field F] [Field E] (e : F ≃+* E) : Prop :=
  ∀ {B L n m J : Type u} [Ring B] [Algebra F B] [Field L] [Algebra F L]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {G I : GroupScheme F} {π : G ⟶ I} (D : QuaternionicSpinCoverPresentation F B L n m J π),
    ∃ C : ∀ R : TestAlgebra E, SpinChartComparisonAlong e D R, IsQuaternionicSpinTransport e D C

end QuaternionicSpin

/-- Coordinate and equation comparisons in the actual scalar extensions of the
matrix and Clifford models. -/
def ModelTransportAlong {F E : Type u} [Field F] [Field E]
    [TopologicalSpace F] [TopologicalSpace E] (e : F ≃+* E) : Prop :=
  letI := scalarStructure e
  MatrixModelTopology F ∧ MatrixModelTopology E ∧
  (∀ (X : SchemeOver F) {n : Type u} (c : Matrix n n Γ(X.left, ⊤))
      (p : RationalPoints ((baseChange F E).obj X)),
    (c.map (coordinatePullback e X)).map (evaluation p) =
      (c.map (evaluation (originalPoint e X p))).map e) ∧
  (∀ (A : Type u) [CommRing A] [Algebra F A] [StarRing A],
    (∀ r : F, star (algebraMap F A r) = algebraMap F A r) →
    ∃ i : A ≃+* E ⊗[F] A,
      (∀ a, i a = (1 : E) ⊗ₜ[F] a) ∧
      letI := transportedInvolution i
      ∀ {n : Type u} [Fintype n] [DecidableEq n] (M H : Matrix n n A),
        ((M.map i)ᴴ * H.map i * M.map i = H.map i ∧ (M.map i).det = 1) ↔
          (Mᴴ * H * M = H ∧ M.det = 1)) ∧
  (∀ (A : Type u) [Ring A] [Algebra F A] [StarRing A],
    (∀ r : F, star (algebraMap F A r) = algebraMap F A r) →
    ∃ i : A ≃+* E ⊗[F] A,
      (∀ a, i a = (1 : E) ⊗ₜ[F] a) ∧
      (∀ r : F, i (algebraMap F A r) = algebraMap E (E ⊗[F] A) (e r)) ∧
      letI := transportedInvolution i
      (∀ (t : E) (a : A), star (t ⊗ₜ[F] a) = t ⊗ₜ[F] star a) ∧
      (∀ {n : Type u} [Fintype n] (M H : Matrix n n A),
        (M.map i)ᴴ * H.map i * M.map i = H.map i ↔ Mᴴ * H * M = H) ∧
      ∀ {n : Type u} [Fintype n] (M H L : Matrix n n A),
        PreservesQuaternionicQuadraticForm E (M.map i) (H.map i) (L.map i) ↔
          PreservesQuaternionicQuadraticForm F M H L) ∧
  (∀ {V : Type u} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V),
    ∃ P : QuadraticForm E (E ⊗[F] V),
      (∀ v, P ((1 : E) ⊗ₜ[F] v) = e (Q v)) ∧
      ∃ b : CliffordAlgebra Q ≃+* CliffordAlgebra P,
        IsCliffordTransport e (fun v ↦ (1 : E) ⊗ₜ[F] v) Q P b) ∧
  QuaternionicSpinTransportAlong e

open scoped CategoryTheory.MonObj in
/-- Along the chosen field isomorphism, use the coordinate topologies and the
canonical rational-point map of the actual base-changed group. -/
def GroupTransportAlong {F E : Type u} [Field F] [Field E]
    [TopologicalSpace F] [TopologicalSpace E] (e : F ≃+* E) : Prop :=
  ∀ G : AffineAlgebraicGroup F,
    letI := scalarStructure e
    let G' := Specs.Unipotent.baseChangedAlgebraicGroup E G
    letI := pointTopology G.val.X
    letI := pointTopology G'.val.X
    ∃ f : RationalPoints G.val.X ≃ₜ* RationalPoints G'.val.X,
      (∀ p, f.symm p = originalPoint e G.val.X p) ∧
      ∃ (h : IsTopologicalGroup (RationalPoints G.val.X))
        (h' : IsTopologicalGroup (RationalPoints G'.val.X)),
        letI := h
        letI := h'
        QuotientTransportAlong.{u, w} f

/-- Realization of the local field, with the original group and its marked
data transported to that same completion along the inverse isomorphism. -/
def RealizationWithTransport : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    ∃ (K : Type u) (_ : Field K) (D : GlobalFieldData.{u, u} K) (w : D.FinitePlace)
      (e : D.FiniteCompletion w ≃+* F),
      IsRealization D w e ∧
      MarkedGroupTransportAlong e.symm ∧ ModelTransportAlong e.symm ∧
      GroupTransportAlong.{u, w} e.symm

end LinearAlgebraicGroups.Arithmetic.LocalFieldRealization
