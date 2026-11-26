import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Int.WithZero

noncomputable section

open scoped TensorProduct BigOperators Polynomial RatFunc

namespace LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecompositionSpec

open NumberField

/-- The diagonal into the actual archimedean completions of a number field. -/
def numberArchimedean : Prop :=
  ∀ (K : Type*) [Field K] [NumberField K],
    ∃ (a : ∀ w : InfinitePlace K, Algebra ℝ w.Completion),
      letI := a
      ∃ e : ℝ ⊗[ℚ] K ≃ₐ[ℝ] (∀ w : InfinitePlace K, w.Completion),
        (∀ w : InfinitePlace K, FiniteDimensional ℝ w.Completion) ∧
        (∀ w : InfinitePlace K, Continuous (algebraMap ℝ w.Completion)) ∧
        ∀ (r : ℝ) (x : K) (w : InfinitePlace K),
          e (r ⊗ₜ[ℚ] x) w = algebraMap ℝ w.Completion r * algebraMap K w.Completion x

/-- The absolute norm counts one copy of a real factor and two of a complex one. -/
def numberArchimedeanNorm : Prop :=
  ∀ (K : Type*) [Field K] [NumberField K] (x : K),
    |(Algebra.norm ℚ x : ℝ)| =
      ∏ w : InfinitePlace K, ‖algebraMap K w.Completion x‖ ^ w.mult

/-- The determinant of the product operator is the product of local field norms. -/
def productDeterminant : Prop :=
  ∀ {B ι : Type*} [Field B] [Fintype ι]
    {C M : ι → Type*} [∀ i, Field (C i)] [∀ i, Algebra B (C i)]
    [∀ i, FiniteDimensional B (C i)] [∀ i, AddCommGroup (M i)]
    [∀ i, Module B (M i)] [∀ i, Module (C i) (M i)]
    [∀ i, IsScalarTower B (C i) (M i)] [∀ i, FiniteDimensional (C i) (M i)]
    (f : ∀ i, M i →ₗ[C i] M i),
    (LinearMap.pi (fun i ↦ ((f i).restrictScalars B).comp (LinearMap.proj i))).det =
      ∏ i, Algebra.norm B (f i).det

/-- Norms commute with completion and decompose along the factors once the canonical
algebra comparison has been constructed. -/
def baseChangeNorm : Prop :=
  ∀ {k K B ι : Type*} [Field k] [Field K] [Field B] [Algebra k K] [Algebra k B]
    [FiniteDimensional k K] [Fintype ι]
    {C : ι → Type*} [∀ i, Field (C i)] [∀ i, Algebra B (C i)]
    [∀ i, FiniteDimensional B (C i)]
    (e : B ⊗[k] K ≃ₐ[B] (∀ i, C i)) (x : K),
    algebraMap k B (Algebra.norm k x) = ∏ i, Algebra.norm B (e (1 ⊗ₜ[k] x) i)

/-- A linear comparison of finite-dimensional spaces is a homeomorphism in their
Hausdorff topological vector-space topologies. -/
def linearTopology : Prop :=
  ∀ {B M N : Type*} [NontriviallyNormedField B] [CompleteSpace B]
    [AddCommGroup M] [Module B M] [TopologicalSpace M] [T2Space M]
    [IsTopologicalAddGroup M] [ContinuousSMul B M] [FiniteDimensional B M]
    [AddCommGroup N] [Module B N] [TopologicalSpace N] [T2Space N]
    [IsTopologicalAddGroup N] [ContinuousSMul B N] [FiniteDimensional B N]
    (e : M ≃ₗ[B] N), Continuous e ∧ Continuous e.symm

/-- Extend the comparison to scalar extensions of every finite-dimensional space. -/
def spaceComparison : Prop :=
  ∀ {k K B ι : Type*} [Field k] [Field K] [Field B] [Algebra k K] [Algebra k B]
    [Fintype ι] {C : ι → Type*} [∀ i, Field (C i)] [∀ i, Algebra B (C i)]
    [∀ i, Algebra K (C i)] (e : B ⊗[k] K ≃ₐ[B] (∀ i, C i))
    (_he : ∀ x : K, ∀ i, e (1 ⊗ₜ[k] x) i = algebraMap K (C i) x)
    (V : Type*) [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower k K V]
    [FiniteDimensional K V],
    ∃ E : B ⊗[k] V ≃ₗ[B] (∀ i, C i ⊗[K] V),
      ∀ (r : B) (v : V) (i : ι), E (r ⊗ₜ[k] v) i = algebraMap B (C i) r ⊗ₜ[K] v

/-- With the finite-dimensional module topologies the scalar-extension
comparison is a continuous linear equivalence. -/
def continuousSpaceComparison : Prop :=
  ∀ {k K B ι : Type*} [Field k] [Field K] [NontriviallyNormedField B] [CompleteSpace B]
    [Algebra k K] [Algebra k B] [Fintype ι]
    {C : ι → Type*} [∀ i, Field (C i)] [∀ i, Algebra B (C i)] [∀ i, Algebra K (C i)]
    [∀ i, TopologicalSpace (C i)] [∀ i, IsTopologicalRing (C i)] [∀ i, T2Space (C i)]
    [∀ i, FiniteDimensional B (C i)]
    (_hc : ∀ i, Continuous (algebraMap B (C i)))
    (e : B ⊗[k] K ≃ₐ[B] (∀ i, C i))
    (_he : ∀ x : K, ∀ i, e (1 ⊗ₜ[k] x) i = algebraMap K (C i) x)
    (V : Type*) [AddCommGroup V] [Module k V] [Module K V] [IsScalarTower k K V]
    [FiniteDimensional K V],
    letI := moduleTopology B (B ⊗[k] V)
    letI (i : ι) := moduleTopology (C i) (C i ⊗[K] V)
    ∃ E : B ⊗[k] V ≃L[B] (∀ i, C i ⊗[K] V),
      ∀ (r : B) (v : V) (i : ι), E (r ⊗ₜ[k] v) i = algebraMap B (C i) r ⊗ₜ[K] v

/-- The completion of an arbitrary module at a product of powers of coprime primes
is the product of the completions at those primes. The comparison uses the
canonical maps on the original module. -/
def moduleAdicComparison : Prop :=
  ∀ {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    (I : Ideal A) (P : ι → Ideal A) (e : ι → ℕ),
    Pairwise (Function.onFun IsCoprime P) → (∀ i, 0 < e i) →
    I = ∏ i, (P i) ^ (e i) →
    ∃ E : AdicCompletion I M ≃ₗ[A] (∀ i, AdicCompletion (P i) M),
      ∀ (x : M) (i : ι), E (AdicCompletion.of I M x) i = AdicCompletion.of (P i) M x


/-- The actual embedding of base local fields at a prime and a prime above it. -/
def completionEmbedding : Prop :=
  ∀ {R A k K : Type*} [CommRing R] [IsDedekindDomain R] [CommRing A] [IsDedekindDomain A]
    [Algebra R A] [Module.IsTorsionFree R A]
    [Field k] [Field K] [Algebra k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K]
    (p : IsDedekindDomain.HeightOneSpectrum R) (w : IsDedekindDomain.HeightOneSpectrum A)
    [w.asIdeal.LiesOver p.asIdeal],
    ∃ f : p.adicCompletion k →+* w.adicCompletion K, Continuous f ∧
      ∀ x : k, f (algebraMap k (p.adicCompletion k) x) =
        algebraMap K (w.adicCompletion K) (algebraMap k K x)

/-- For normalized extensions of the base norm, the weight of a local field
is its degree over the completed base. -/
def normWeight : Prop :=
  ∀ {B C : Type*} [NontriviallyNormedField B] [IsUltrametricDist B] [CompleteSpace B]
    [NormedField C] [NormedAlgebra B C] [FiniteDimensional B C] (x : C),
    ‖Algebra.norm B x‖ = ‖x‖ ^ Module.finrank B C


/-- At a base prime the factors of the completed module are the completions
at the actual primes of the integer ring above it. This applies in particular
to a full lattice that need not be free over the integer ring. -/
def latticeAtBasePrime : Prop :=
  ∀ {R A M : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [AddCommGroup M] [Module A M]
    (p : IsDedekindDomain.HeightOneSpectrum R),
    let I := p.asIdeal.map (algebraMap R A)
    ∃ E : AdicCompletion I M ≃ₗ[A]
        (∀ w : p.asIdeal.primesOver A, AdicCompletion w.val M),
      ∀ (x : M) (w : p.asIdeal.primesOver A),
        E (AdicCompletion.of I M x) w = AdicCompletion.of w.val M x


/-- The same lattice comparison starting with its completion as a module
over the base integer ring. -/
def latticeCompletionAtBasePrime : Prop :=
  ∀ {R A M : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (p : IsDedekindDomain.HeightOneSpectrum R),
    ∃ E : AdicCompletion p.asIdeal M ≃ₗ[R]
        (∀ w : p.asIdeal.primesOver A, AdicCompletion w.val M),
      ∀ (x : M) (w : p.asIdeal.primesOver A),
        E (AdicCompletion.of p.asIdeal M x) w = AdicCompletion.of w.val M x


section FinitePlaces

open IsDedekindDomain
open scoped NumberField Polynomial RatFunc

/-- A prime over a nonzero base prime, viewed as a point of the height-one spectrum. -/
def primeAbove {R A : Type*} [CommRing R] [IsDedekindDomain R] [CommRing A] [IsDedekindDomain A]
    [Algebra R A] [Module.IsTorsionFree R A] (p : HeightOneSpectrum R) (w : p.asIdeal.primesOver A) :
    HeightOneSpectrum A :=
  ⟨w.val, w.property.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot w.property⟩

/-- The finite local vector-space comparison identifies the closure of a lattice
over the base with the product of its closures at the actual primes above it. -/
def latticeClosureComparison : Prop :=
  ∀ {R A k K : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Field k] [Field K] [Algebra k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K]
    (p : HeightOneSpectrum R),
    let P := p.asIdeal.primesOver A
    let B := p.adicCompletion k
    let C (w : P) := (primeAbove p w).adicCompletion K
    ∀ (a : ∀ w : P, Algebra B (C w)),
      letI := a
      ∀ (V : Type*) [AddCommGroup V] [Module k V] [Module K V] [Module A V]
      [IsScalarTower k K V] [IsScalarTower A K V] [FiniteDimensional K V],
      letI := moduleTopology B (B ⊗[k] V)
      letI (w : P) := moduleTopology (C w) (C w ⊗[K] V)
    ∀ (e : B ⊗[k] V ≃L[B] (∀ w : P, C w ⊗[K] V)),
    (∀ (v : V) (w : P), e (1 ⊗ₜ[k] v) w = 1 ⊗ₜ[K] v) →
    ∀ L : Submodule A V,
      e '' closure (Set.range fun x : L ↦ (1 : B) ⊗ₜ[k] (x : V)) =
        Set.pi Set.univ (fun w : P ↦ closure (Set.range fun x : L ↦ (1 : C w) ⊗ₜ[K] (x : V)))

/-- The comparison ring and the original scalar embeddings at a finite base prime. -/
def AdicComparison {R A : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K]
    (p : HeightOneSpectrum R) : Prop :=
  let B := p.adicCompletion k
  let C (w : p.asIdeal.primesOver A) := (primeAbove p w).adicCompletion K
  ∃ (a : ∀ w, Algebra B (C w)),
    letI := a
    ∃ e : B ⊗[k] K ≃ₐ[B] (∀ w, C w),
      (∀ w, FiniteDimensional B (C w)) ∧
      (∀ w, Continuous (algebraMap B (C w))) ∧
      ∀ (r : B) (x : K) (w : p.asIdeal.primesOver A),
        e (r ⊗ₜ[k] x) w = algebraMap B (C w) r * algebraMap K (C w) x

/-- The finite-prime comparison for a finite separable field extension, with
Dedekind domains as integral models. -/
def adicFieldComparison : Prop :=
  ∀ {R A k K : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K] (p : HeightOneSpectrum R),
    AdicComparison (A := A) k K p

def numberFiniteComparison : Prop :=
  ∀ (K : Type*) [Field K] [NumberField K] (p : HeightOneSpectrum ℤ),
    AdicComparison (A := 𝓞 K) ℚ K p

theorem parameterIntegerRing_torsionFree {F K : Type*} [Field F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) : Module.IsTorsionFree F[X] t.integerRing := by
  let := t.polynomialAlgebra
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  intro x y h
  exact (transcendental_iff_injective.mp t.transcendental) (congrArg Subtype.val h)


def functionFiniteComparison : Prop :=
  ∀ {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (p : HeightOneSpectrum F[X]),
    letI := t.rationalAlgebra
    letI := t.polynomialAlgebra
    letI := parameterIntegerRing_torsionFree t
    AdicComparison (A := t.integerRing) F⟮X⟯ K p

open Classical in
/-- The completion for the infinity valuation on the original rational function field. -/
abbrev infinityField (F : Type*) [Field F] := (RatFunc.inftyValuation F).Completion

open Classical in
/-- The canonical embedding into the infinity completion. -/
def infinityEmbedding (F : Type*) [Field F] : F⟮X⟯ →+* infinityField F :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (RatFunc.inftyValuation F)).symm.toRingHom

/-- The canonical comparison with the intrinsic local fields in a specified set of places. -/
def IntrinsicComparison {k K B : Type*} [Field k] [Field K] [Field B] [Algebra k B]
    [Algebra k K] [TopologicalSpace B] (S : Set (FunctionPlace K)) : Prop :=
  ∃ (_idx : Fintype S) (a : ∀ w : S, Algebra B w.val.Completion),
    letI := a
    ∃ e : B ⊗[k] K ≃ₐ[B] (∀ w : S, w.val.Completion),
      (∀ w : S, FiniteDimensional B w.val.Completion) ∧
      (∀ w : S, Continuous (algebraMap B w.val.Completion)) ∧
      ∀ (r : B) (x : K) (w : S),
        e (r ⊗ₜ[k] x) w = algebraMap B w.val.Completion r * w.val.embedding x

/-- At a finite place of the rational function field the factors are the
intrinsic places restricting to the given base place. -/
def functionFiniteIntrinsicComparison : Prop :=
  ∀ {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (p : HeightOneSpectrum F[X]),
    letI := t.rationalAlgebra
    IntrinsicComparison (k := F⟮X⟯) (B := p.adicCompletion F⟮X⟯)
      {v : FunctionPlace K |
        v.val.comap t.rationalMap.toRingHom = (p.valuation F⟮X⟯).valuationSubring}

/-- The distinguished completion includes exactly the intrinsic places at which
the original separating parameter has a pole. -/
def functionInfinityComparison : Prop :=
  ∀ {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K),
    letI := t.rationalAlgebra
    letI := (infinityEmbedding F).toAlgebra
    IntrinsicComparison (k := F⟮X⟯) (B := infinityField F) {v : FunctionPlace K | t.element ∉ v.val}


end FinitePlaces

section InfinityNorm

open scoped Valued NNReal

/-- The real-valued normalization of the infinity valuation with `|X| = #F`. -/
@[instance_reducible]
def infinityRankOne (F : Type*) [Field F] [Finite F] :
    (Valued.v (R := infinityField F) (Γ₀ := WithZero (Multiplicative ℤ))).RankOne := by
  classical
  let v : Valuation (infinityField F) (WithZero (Multiplicative ℤ)) := Valued.v
  let q : ℝ≥0 := Nat.card F
  have hq : 1 < q := by
    change (1 : ℝ≥0) < (Nat.card F : ℝ≥0)
    exact_mod_cast Finite.one_lt_card (α := F)
  refine
    { hom' := (WithZeroMulInt.toNNReal hq.ne_zero).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := (WithZeroMulInt.toNNReal_strictMono hq).comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      exists_val_nontrivial := ⟨infinityEmbedding F RatFunc.X, ?_⟩ }
  have hX : v (infinityEmbedding F RatFunc.X) = WithZero.exp 1 := by
    change Valued.v (↑(WithVal.toVal (RatFunc.inftyValuation F) RatFunc.X) : infinityField F) = _
    rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, RatFunc.inftyValuation.X]
  change v (infinityEmbedding F RatFunc.X) ≠ 0 ∧ v (infinityEmbedding F RatFunc.X) ≠ 1
  rw [hX, ← WithZero.exp_zero]
  simp

/-- The infinity completion with the absolute value of the finite constant field normalization. -/
@[instance_reducible]
def infinityNormedField (F : Type*) [Field F] [Finite F] : NontriviallyNormedField (infinityField F) :=
  letI := infinityRankOne F
  Valued.toNontriviallyNormedField (infinityField F) (WithZero (Multiplicative ℤ))

/-- On the embedded rational function field the usual degree gives the exponent. -/
def functionInfinityBaseNorm : Prop :=
  ∀ (F : Type*) [Field F] [Finite F],
    letI := infinityNormedField F
    ∀ (x : F⟮X⟯), x ≠ 0 → ‖infinityEmbedding F x‖ = (Nat.card F : ℝ) ^ x.intDegree

/-- The factors carry the unique relative absolute values extending the base
normalization, with their original completion topologies and integer rings. -/
def functionInfinityNormCompatibility : Prop :=
  ∀ {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K),
    let B := infinityField F
    letI := infinityNormedField F
    let P := {v : FunctionPlace K // t.element ∉ v.val}
    ∀ (a : ∀ w : P, Algebra B w.val.Completion),
      letI := a
      ∀ (d : ∀ w : P, FiniteDimensional B w.val.Completion),
        letI := d
        (∀ w : P, Continuous (algebraMap B w.val.Completion)) →
        ∀ w : P,
          ((spectralNorm.normedField B w.val.Completion).toMetricSpace.toUniformSpace.toTopologicalSpace =
            (inferInstance : TopologicalSpace w.val.Completion)) ∧
          (∀ b : B, (spectralNorm B w.val.Completion (algebraMap B w.val.Completion b) : ℝ) = ‖b‖) ∧
          (∀ z : w.val.Completion, (spectralNorm B w.val.Completion z : ℝ) ≤ 1 ↔ z ∈ w.val.integers)

/-- With the extended base absolute values, the infinity norm of the original
field norm counts every local factor with its degree over the completed base. -/
def functionInfinityNorm : Prop :=
  ∀ {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K),
    let B := infinityField F
    letI := t.rationalAlgebra
    letI := (infinityEmbedding F).toAlgebra
    letI := infinityNormedField F
    let P := {v : FunctionPlace K // t.element ∉ v.val}
    ∀ (idx : Fintype P) (a : ∀ w : P, Algebra B w.val.Completion),
      letI := idx
      letI := a
      ∀ (d : ∀ w : P, FiniteDimensional B w.val.Completion),
        letI := d
        ∀ (e : B ⊗[F⟮X⟯] K ≃ₐ[B] (∀ w : P, w.val.Completion)),
          (∀ (x : K) (w : P), e (1 ⊗ₜ[F⟮X⟯] x) w = w.val.embedding x) →
          ∀ x : K, ‖infinityEmbedding F (Algebra.norm F⟮X⟯ x)‖ =
            ∏ w : P, (spectralNorm B w.val.Completion (w.val.embedding x) : ℝ) ^
              Module.finrank B w.val.Completion

end InfinityNorm

end LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecompositionSpec
