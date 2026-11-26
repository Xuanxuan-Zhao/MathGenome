import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.AdjointRepresentation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Analysis.Normed.Algebra.Logarithm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

noncomputable section

open NormedSpace Set Topology Filter
open scoped ENNReal Topology

namespace LinearAlgebraicGroups.Specs.PadicLogarithmChart

/-- A positive convergence radius for the matrix exponential, in any complete normed
algebra over the p-adic field. The bound also applies at p = 2. -/
def ExponentialRadius : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A],
    (‖(p : ℚ_[p])‖₊ : ℝ≥0∞) ≤ (expSeries ℚ_[p] A).radius

/-- The ordinary logarithm converges on a neighborhood of the identity in the ambient
algebra. This lower bound on the radius need not be sharp. -/
def LogarithmRadius : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A],
    (‖(p : ℚ_[p])‖₊ : ℝ≥0∞) ≤ (logSeries ℚ_[p] A).radius

/-- The ordinary matrix logarithm is a left inverse to the matrix exponential
on a neighborhood of zero. -/
def LogarithmExponentialGerm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A]
    [CompleteSpace A], ∀ᶠ X : A in 𝓝 0, log (exp X) = X

/-- The exponential is a local homeomorphism between neighborhoods of zero and one in
a complete normed algebra over the p-adic field. -/
def AmbientExponentialChart : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A]
    [CompleteSpace A],
    ∃ e : OpenPartialHomeomorph A A, 0 ∈ e.source ∧
      (e : A → A) = exp ∧ e 0 = 1

/-- The strict derivative of ambient conjugation, parameterized by the small
exponential chart, is the matrix commutator. -/
def ConjugationDerivative : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A]
    [CompleteSpace A] (Y : A),
    HasStrictFDerivAt (fun X : A => exp X * Y * exp (-X))
      (ContinuousLinearMap.mulLeftRight ℚ_[p] A 1 Y -
        ContinuousLinearMap.mulLeftRight ℚ_[p] A Y 1) 0


section Subgroups

variable (p : ℕ) [Fact p.Prime] {A E J : Type*}
  [NormedRing A] [NormedAlgebra ℚ_[p] A]
  [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
  [Group J] [TopologicalSpace J]

/-- The relation between a local exponential chart and a matrix realization. The
source is a ball small enough for the ambient exponential series. -/
structure ExponentialChart (m : J →* Aˣ) (j : E →L[ℚ_[p]] A) where
  chart : OpenPartialHomeomorph E J
  radius : ℝ
  radius_pos : 0 < radius
  source_eq : chart.source = Metric.ball 0 radius
  at_zero : chart 0 = 1
  matrix_exp : ∀ x ∈ chart.source, (m (chart x) : A) = exp (j x)
  converges : ∀ x ∈ chart.source, j x ∈ Metric.eball 0 (expSeries ℚ_[p] A).radius
  matrix_log : ∀ g ∈ chart.target, j (chart.symm g) = log (m g : A)

variable {p} {m : J →* Aˣ} {j : E →L[ℚ_[p]] A}

/-- The restricted scalar span of the logarithms of the subgroup in the chart. -/
def smallLogarithmSpan (c : ExponentialChart p m j) (H : Subgroup J) :
    Submodule ℚ_[p] E :=
  Submodule.span ℚ_[p] (c.chart.symm '' ((H : Set J) ∩ c.chart.target))

/-- Closedness extends the integer exponential powers to all p-adic integer
parameters. -/
def PadicIntegerLines : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A E J : Type*)
    [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [Group J] [TopologicalSpace J]
    {m : J →* Aˣ} {j : E →L[ℚ_[p]] A} (c : ExponentialChart p m j)
    (_hm : Function.Injective m) (H : Subgroup J) (_hH : IsClosed (H : Set J))
    (x : E), x ∈ c.chart.source → c.chart x ∈ H →
      ∀ s : ℤ_[p], c.chart ((s : ℚ_[p]) • x) ∈ H

/-- The ambient exponential chart restricts to the group when the local
preimage of the matrix points under the exponential is the tangent subspace. -/
def RestrictExponentialChart : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A E J : Type*)
    [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A] [FiniteDimensional ℚ_[p] A]
    [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [Group J] [TopologicalSpace J]
    (m : J →* Aˣ) (j : E →L[ℚ_[p]] A)
    (_hm : IsEmbedding (fun g : J => (m g : A))) (_hj : Function.Injective j),
    (∀ᶠ x : A in 𝓝 0, exp x ∈ Set.range (fun g : J => (m g : A)) ↔
      x ∈ Set.range j) →
    Nonempty (ExponentialChart p m j)

/-- A closed matrix subgroup contains the entire p-adic integer line through a
sufficiently small exponential point. This uses the ambient exponential only. -/
def AmbientPadicIntegerLines : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A]
    [CompleteSpace A] (H : Subgroup Aˣ) (_hH : IsClosed (H : Set Aˣ)) (X : A),
    X ∈ Metric.eball 0 (expSeries ℚ_[p] A).radius →
    exp X ∈ (fun u : Aˣ => (u : A)) '' (H : Set Aˣ) →
    ∀ s : ℤ_[p], exp ((s : ℚ_[p]) • X) ∈ (fun u : Aˣ => (u : A)) '' (H : Set Aˣ)

/-- Every differentiable equation for a closed matrix subgroup has zero
directional derivative on a small ambient logarithm of that subgroup. -/
def DerivativeAnnihilatesLogarithm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A V : Type*) [NormedRing A] [NormedAlgebra ℚ_[p] A]
    [CompleteSpace A] [NormedAddCommGroup V] [NormedSpace ℚ_[p] V]
    (H : Subgroup Aˣ) (_hH : IsClosed (H : Set Aˣ)) (X : A)
    (f : A → V) (d : A →L[ℚ_[p]] V), HasFDerivAt f d 1 →
    (∀ u : H, f (u.val : A) = 0) →
    X ∈ Metric.eball 0 (expSeries ℚ_[p] A).radius →
    exp X ∈ (fun u : Aˣ => (u : A)) '' (H : Set Aˣ) → d X = 0

/-- A nondiscrete subgroup has a nonzero logarithm in each such chart. -/
def NonzeroLogarithmSpan : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A E J : Type*)
    [NormedRing A] [NormedAlgebra ℚ_[p] A] [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    {m : J →* Aˣ} {j : E →L[ℚ_[p]] A} (c : ExponentialChart p m j)
    (H : Subgroup J), ¬ DiscreteTopology H → smallLogarithmSpan c H ≠ ⊥

/-- A full logarithm span implies openness in the point group. -/
def OpennessOfFullSpan : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A E J : Type*)
    [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A] [FiniteDimensional ℚ_[p] A]
    [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    {m : J →* Aˣ} {j : E →L[ℚ_[p]] A} (c : ExponentialChart p m j)
    (_hm : Function.Injective m) (_hj : Function.Injective j)
    (H : Subgroup J) (_hH : IsClosed (H : Set J)),
    smallLogarithmSpan c H = ⊤ → IsOpen (H : Set J)

/-- The subgroup's adjoint operators preserve the span of its small logarithms. -/
def InvarianceOfLogarithmSpan : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A E J : Type*)
    [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [Group J] [TopologicalSpace J]
    {m : J →* Aˣ} {j : E →L[ℚ_[p]] A} (c : ExponentialChart p m j)
    (_hm : Function.Injective m) (H : Subgroup J) (a : H)
    (ad : E →L[ℚ_[p]] E)
    (_had : ∀ x, j (ad x) = (m a : A) * j x * (↑((m a)⁻¹) : A)),
    ∀ x ∈ smallLogarithmSpan c H, ad x ∈ smallLogarithmSpan c H

end Subgroups

/-- In any matrix exponential chart, conjugation has the ambient commutator derivative.
This can be used with the chart on a subgroup, keeping the vector being conjugated in
the ambient matrix algebra. -/
def ChartConjugationDerivative : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A E J : Type*)
    [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [Group J] [TopologicalSpace J]
    {m : J →* Aˣ} {j : E →L[ℚ_[p]] A} (c : ExponentialChart p m j) (Y : A),
    HasStrictFDerivAt (fun x => (m (c.chart x) : A) * Y * (↑((m (c.chart x))⁻¹) : A))
      ((ContinuousLinearMap.mulLeftRight ℚ_[p] A 1 Y -
        ContinuousLinearMap.mulLeftRight ℚ_[p] A Y 1).comp j) 0

/-- Differentiating invariance under the point group gives commutator invariance
under its chart directions. -/
def DifferentiatedInvariance : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A E J : Type*)
    [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]
    [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [Group J] [TopologicalSpace J]
    {m : J →* Aˣ} {j : E →L[ℚ_[p]] A} (_c : ExponentialChart p m j)
    (W : Submodule ℚ_[p] A) (_hW : IsClosed (W : Set A))
    (_h : ∀ (a : J) (Y : A), Y ∈ W → (m a : A) * Y * (↑((m a)⁻¹) : A) ∈ W),
    ∀ (x : E) (Y : A), Y ∈ W → j x * Y - Y * j x ∈ W

/-- Polynomial evaluation over the dual numbers, with (x) as constant coefficient
and (v) as coefficient of the square-zero variable. -/
def polynomialDualEvaluation {F I : Type*} [Field F] (x v : I → F) :
    MvPolynomial I F →ₐ[F] DualNumber F :=
  MvPolynomial.aeval (S₁ := DualNumber F) (fun i => (x i, v i))

/-- The coefficient of the dual-number variable in a polynomial evaluation
is its analytic derivative in the same direction, even after restricting scalars. -/
def PolynomialDerivative : Prop :=
  ∀ (k F I : Type*) [NontriviallyNormedField k] [NormedField F] [NormedAlgebra k F]
    [Fintype I] (P : MvPolynomial I F) (x : I → F),
    ∃ d : (I → F) →L[k] F,
      HasStrictFDerivAt (fun y : I → F => MvPolynomial.aeval y P) d x ∧
      ∀ v : I → F, TrivSqZeroExt.snd (polynomialDualEvaluation x v P) = d v

section Scheme

open AlgebraicGeometry CategoryTheory
open Arithmetic.AdelicGroups IntegralModels InfinitesimalCommutator
universe u

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- Conjugation on the identity tangent by the constant dual-number lift of a point. -/
def schemeConjugation (g : RationalPoints G) (Y : Lie k G.val) : Lie k G.val :=
  ⟨AdjointRepresentation.conjugate (R := CommAlgCat.of k k) g Y, by
    let F := (groupPointsFunctor k).obj G.val
    let a := (F.map (AdjointRepresentation.constants (CommAlgCat.of k k))).hom g
    change (F.map (dualReduction k)).hom (a * Y.toMul.val * a⁻¹) = 1
    rw [map_mul, map_mul, map_inv, Y.toMul.property, mul_one, mul_inv_cancel]⟩

/-- The actual scheme tangent embeds linearly in the chosen matrix algebra. Under this
embedding, the point action is conjugation and the scheme bracket is the matrix commutator. -/
def MatrixLieComparison : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k)
    (i : MatrixRealization G) (s : IdentityLieStructure G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ j : Lie k G.val →ₗ[k] Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) k,
      Function.Injective j ∧
      (∀ X, j X = matrixDifferential i.embedding i.matrix X) ∧
      (∀ (g : PointsIn i k) (Y : Lie k G.val),
        j (schemeConjugation g Y) = (asMatrix i k g).val * j Y * (asMatrix i k g)⁻¹.val) ∧
      ∀ X Y, j ⁅X, Y⁆ = j X * j Y - j Y * j X

open scoped Matrix.Norms.Operator

/-- The identity chart of the actual points of a smooth affine algebraic group over
a finite p-adic extension, in the matrix topology. The modeled vector space is
the image of the scheme differential with its matrix norm and restricted scalars. -/
def SchemeExponentialChart : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type u) [NormedField F] [NormedAlgebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] (G : AffineAlgebraicGroup F) (i : MatrixRealization G),
    Smooth G.val.X.hom →
    ∃ L : Submodule F (Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) F),
       (L : Set _) = Set.range (matrixDifferential i.embedding i.matrix) ∧
       Nonempty (ExponentialChart p (asMatrix i F) (L.restrictScalars ℚ_[p]).subtypeL)


/-- The small logarithms of a closed subgroup of the actual matrix point group,
with the adjoint action expressed in the matrix tangent subspace. -/
def SchemeLogarithmSpan : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type u) [NormedField F] [NormedAlgebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (L : Submodule F (Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) F))
    (_hL : (L : Set _) = Set.range (matrixDifferential i.embedding i.matrix))
    (c : ExponentialChart p (asMatrix i F) (L.restrictScalars ℚ_[p]).subtypeL)
    (H : Subgroup (PointsIn i F)) (_hH : IsClosed (H : Set (PointsIn i F))),
    (¬ DiscreteTopology H → smallLogarithmSpan c H ≠ ⊥) ∧
    (∀ a : H, ∀ x ∈ smallLogarithmSpan c H,
      (asMatrix i F a).val * (x : Matrix _ _ F) * (asMatrix i F a)⁻¹.val ∈
        (smallLogarithmSpan c H).map (L.restrictScalars ℚ_[p]).subtype) ∧
    (smallLogarithmSpan c H = ⊤ → IsOpen (H : Set (PointsIn i F)))

end Scheme

section NumberPlaces

open Arithmetic Arithmetic.AdelicGroups IntegralModels
open IsDedekindDomain HeightOneSpectrum AlgebraicGeometry CategoryTheory
open scoped WithZero NumberField NNReal Matrix.Norms.Operator

universe v

/-- The height-one prime of the rational integers associated to the rational prime p. -/
def rationalPrime (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum ℤ :=
  .ofPrime (Ideal.prime_of_isPrime (by simpa using hp.out.ne_zero)
    (Ideal.isPrime_span_singleton_of_prime (Nat.prime_iff_prime_int.mp hp.out)))

variable (p : ℕ) [hp : Fact p.Prime] {K : Type u} [Field K] [NumberField K]
  (w : NumberFinitePlace K) [w.asIdeal.LiesOver (rationalPrime p).asIdeal]

/-- The positive base for the normalized discrete valuation norm. -/
def completionNormBase : ℝ≥0 :=
  (p : ℝ≥0) ^ ((w.asIdeal.ramificationIdx ℤ : ℝ)⁻¹)

theorem completionNormBase_gt_one : 1 < completionNormBase p w := by
  apply NNReal.one_lt_rpow (by exact_mod_cast hp.out.one_lt)
  exact inv_pos.mpr (by exact_mod_cast
    Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal (rationalPrime p).ne_bot)

/-- Normalize the norm on the adopted completion so that its restriction to
the rationals is the p-adic norm. The valued uniformity is the original one. -/
@[instance_reducible]
def completionNormedField : NormedField (w.adicCompletion K) :=
  letI := Valuation.IsRankOneDiscrete.rankOne
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) (completionNormBase_gt_one p w)
  Valued.toNormedField (w.adicCompletion K) ℤᵐ⁰

/-- Every finite place of a number field lies above a rational prime. -/
def NumberPlacePrime : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (w : NumberFinitePlace K),
    ∃ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      w.asIdeal.LiesOver (rationalPrime p).asIdeal

/-- The completion of a number field at a place over p is finite over the
isometrically embedded p-adic field. -/
def NumberCompletionPadic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    (w : NumberFinitePlace K) [w.asIdeal.LiesOver (rationalPrime p).asIdeal],
    letI := completionNormedField p w
    ∃ a : NormedAlgebra ℚ_[p] (w.adicCompletion K),
      letI := a
      FiniteDimensional ℚ_[p] (w.adicCompletion K)

/-- Read the matrix differential of the scalar-extended scheme on its actual
dual-number points, using the original realization and the base change point map. -/
def scalarExtendedDifferential {k E : Type u} [Field k] [Field E] [Algebra k E]
    {G : AffineAlgebraicGroup k} (i : MatrixRealization G)
    (Y : Lie E ((groupBaseChange k E).obj G.val)) :
    Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) E :=
  let T := CommAlgCat.of E (DualNumber E)
  let R := (restrictTestAlgebra k E).obj T
  let g := baseChangePoint k E G.val.X T Y.toMul.val
  let M := (i.matrix.hom.app R).hom (((groupPointsFunctor k).map i.embedding).app R g)
  fun a b => (M.val a b).snd

/-- The identity chart on the points at the adopted number-field place, with the
tangent of the scalar-extended group and the inherited adelic matrix topology. -/
def NumberPlaceSchemeExponentialChart : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
    (w : NumberFinitePlace K) [w.asIdeal.LiesOver (rationalPrime p).asIdeal]
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G),
    Smooth G.val.X.hom →
    let D : GlobalFieldData.{u, v} K := .number inferInstance
    let F := D.Completion (.inl w)
    letI : NormedField F := completionNormedField p w
    letI : Algebra K F := completionAlgebra D (.inl w)
    ∃ a : NormedAlgebra ℚ_[p] F,
      letI := a
      FiniteDimensional ℚ_[p] F ∧
      ∃ L : Submodule F (Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) F),
        (L : Set _) = Set.range (scalarExtendedDifferential (E := F) i) ∧
        Nonempty (ExponentialChart p (asMatrix i F) (L.restrictScalars ℚ_[p]).subtypeL)

end NumberPlaces

end LinearAlgebraicGroups.Specs.PadicLogarithmChart
