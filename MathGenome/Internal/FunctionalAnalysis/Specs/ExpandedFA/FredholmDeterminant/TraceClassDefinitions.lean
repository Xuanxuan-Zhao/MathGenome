import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.Data.Set.PowersetCard
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Independent specification of the complex Hilbert exterior-series
Fredholm determinant. The exterior coordinate model is a complete Hilbert
space with normalized subset wedges. The implementation proves its Gram
identity, constructs the continuous exterior functor, establishes trace class
and the factorial trace-norm bound, and identifies its trace with the
principal-minor coefficients. No eigenvalue product is used as a definition. -/
noncomputable section
universe u v w z
namespace ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec

namespace ExteriorCoordinates

open scoped lp Classical

lemma summable_fin_prod {α : Type*} (n : ℕ) (f : Fin n → α → ℝ)
    (hf : ∀ i a, 0 ≤ f i a) (hs : ∀ i, Summable (f i)) :
    Summable (fun a : Fin n → α => ∏ i, f i (a i)) := by
  induction n with
  | zero =>
      exact hasSum_fintype _ |>.summable
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n+1) => α)
      have htail := ih (fun i => f i.succ) (fun i => hf i.succ) (fun i => hs i.succ)
      have hprod := (hs 0).mul_of_nonneg htail (hf 0)
        (fun a => Finset.prod_nonneg (fun i _ => hf i.succ (a i)))
      apply e.summable_iff.mp
      simpa [e, Fin.prod_univ_succ, Fin.consEquiv] using hprod.congr (fun a => by simp)

variable {α : Type*} {n : ℕ}

def enumeration (s : Set.powersetCard α n) : Fin n ↪ α :=
  (Finset.equivFinOfCardEq s.property).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

lemma enumeration_range (s : Set.powersetCard α n) :
    Set.range (enumeration s) = s := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Finset.equivFinOfCardEq s.property).symm i).property
  · intro ha
    refine ⟨(Finset.equivFinOfCardEq s.property) ⟨a, ha⟩, ?_⟩
    simp [enumeration]

lemma enumeration_injective : Function.Injective (fun s : Set.powersetCard α n =>
    (enumeration s : Fin n → α)) := by
  intro s t h
  apply SetLike.coe_injective
  rw [← enumeration_range, ← enumeration_range]
  exact congrArg Set.range h

lemma memℓp_tuple_prod (f : Fin n → ℓ²(α, ℂ)) :
    Memℓp (fun a : Fin n → α => ∏ i, f i (a i)) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_prod, ← Finset.prod_pow]
  apply summable_fin_prod n (fun i a => ‖f i a‖ ^ 2)
  · intro i a; positivity
  · intro i
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (f i).property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

lemma memℓp_det_coordinates (f : Fin n → ℓ²(α, ℂ)) :
    Memℓp (fun s : Set.powersetCard α n =>
      Matrix.det (fun i j : Fin n => f j (enumeration s i))) 2 := by
  have hterm (σ : Equiv.Perm (Fin n)) :
      Memℓp (fun s : Set.powersetCard α n =>
        ∏ i, f i (enumeration s (σ i))) 2 := by
    have h := memℓp_tuple_prod f
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs := h.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    apply hs.comp_injective
    intro s t hst
    apply enumeration_injective
    funext i
    have hh := congrFun hst (σ.symm i)
    simpa using hh
  have hsum := Memℓp.finsetSum Finset.univ
    (fun σ _ => (hterm σ).const_mul ((Equiv.Perm.sign σ : ℤ) : ℂ))
  convert hsum using 1
  funext s
  exact Matrix.det_apply' _


abbrev Space (α : Type*) (n : ℕ) := ℓ²(Set.powersetCard α n, ℂ)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finiteCoordinates (b : HilbertBasis α ℂ H) (s : Set.powersetCard α n) :
    H →ₗ[ℂ] (Fin n → ℂ) where
  toFun x j := b.repr x (enumeration s j)
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp

def wedgeAlternating (b : HilbertBasis α ℂ H) : H [⋀^Fin n]→ₗ[ℂ] Space α n :=
  (AlternatingMap.pi (fun s : Set.powersetCard α n =>
    Matrix.detRowAlternating.compLinearMap (finiteCoordinates b s))).codRestrict
      (lpSubmodule ℂ (fun _ : Set.powersetCard α n => ℂ) 2) (fun x => by
        change Memℓp (fun s : Set.powersetCard α n =>
          Matrix.det (fun i j : Fin n => b.repr (x i) (enumeration s j))) 2
        have h := memℓp_det_coordinates (fun j => b.repr (x j))
        convert h using 1
        funext s
        exact Matrix.det_transpose _)

@[simp] lemma wedgeAlternating_apply (b : HilbertBasis α ℂ H) (x : Fin n → H)
    (s : Set.powersetCard α n) :
    wedgeAlternating b x s = Matrix.det (fun i j : Fin n => b.repr (x i) (enumeration s j)) := rfl

def embed (b : HilbertBasis α ℂ H) : ⋀[ℂ]^n H →ₗ[ℂ] Space α n :=
  exteriorPower.alternatingMapLinearEquiv (wedgeAlternating b)

def basis (α : Type*) (n : ℕ) : HilbertBasis (Set.powersetCard α n) ℂ (Space α n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

end ExteriorCoordinates

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual algebraic exterior functor, before Hilbert completion. -/
def AlgebraicExteriorMapValue (n : ℕ) (T : H →L[ℂ] H) :
    ⋀[ℂ]^n H →ₗ[ℂ] ⋀[ℂ]^n H := exteriorPower.map n T.toLinearMap

def AlgebraicExteriorMapType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H], (n : ℕ) → (H →L[ℂ] H) →
    (⋀[ℂ]^n H →ₗ[ℂ] ⋀[ℂ]^n H)

/-- A principal minor uses the finite set itself as its matrix index, avoiding
an arbitrary ordering or an enumeration of an uncountable Hilbert basis. -/
def PrincipalMinorValue {ι : Type w} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (s : Finset ι) : ℂ := by
  classical
  exact Matrix.det (fun i j : s => inner ℂ (b i.val) (T (b j.val)))

def PrincipalMinorType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {ι : Type w}, HilbertBasis ι ℂ H →
    (H →L[ℂ] H) → Finset ι → ℂ

variable [CompleteSpace H]

/-- Principal-minor formula for `Tr (∧ⁿ T)`. For trace-class T the
implementation proves absolute convergence and equality with the actual trace
of the completed exterior operator. -/
def ExteriorTraceValue (T : H →L[ℂ] H) (n : ℕ) : ℂ :=
  ∑' s : Set.powersetCard (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
      (𝕜 := ℂ) (H := H)) n,
    PrincipalMinorValue (TraceIdeals.TraceClassDefinitions.Spec.chosenBasis
      (𝕜 := ℂ) (H := H)) T s.val

def ExteriorTraceType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H], (H →L[ℂ] H) → ℕ → ℂ

/-- The exterior coefficient series. Its absolute convergence for every
complex parameter and its exterior trace interpretation are proved below. -/
def FredholmDeterminantValue (T : H →L[ℂ] H) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n * ExteriorTraceValue T n

def FredholmDeterminantType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H], (H →L[ℂ] H) → ℂ → ℂ

/-- Zeroth exterior functor is the identity on scalars, including when H = 0. -/
def ExteriorZeroScalarIdentity : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (T : H →L[ℂ] H),
  (exteriorPower.zeroEquiv ℂ H).toLinearMap.comp (AlgebraicExteriorMapValue 0 T) =
    (exteriorPower.zeroEquiv ℂ H).toLinearMap

def ExteriorOneIdentity : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (T : H →L[ℂ] H),
  (exteriorPower.oneEquiv ℂ H).toLinearMap.comp (AlgebraicExteriorMapValue 1 T) =
    T.toLinearMap.comp (exteriorPower.oneEquiv ℂ H).toLinearMap

/-- Pairing with decomposable exterior vectors yields the expected complex
matrix determinant; inner products are conjugate-linear in the first slot. -/
def ExteriorMatrixCoefficient : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (n : ℕ) (T : H →L[ℂ] H) (x y : Fin n → H),
  exteriorPower.pairingDual ℂ H n
      (exteriorPower.ιMulti ℂ n (fun i => (innerSL ℂ (x i)).toLinearMap))
      (AlgebraicExteriorMapValue n T (exteriorPower.ιMulti ℂ n y)) =
    Matrix.det (fun i j => inner ℂ (x i) (T (y j)))

/-- The n=0 operator transported to scalars has scalar trace one. -/
def ScalarIdentityTrace : Prop :=
  TraceIdeals.TraceClassDefinitions.Spec.TraceValue (ContinuousLinearMap.id ℂ ℂ) = 1

def ExteriorTraceZero : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H),
    ExteriorTraceValue T 0 = 1

def ExteriorTraceOne : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H),
    ExteriorTraceValue T 1 = TraceIdeals.TraceClassDefinitions.Spec.TraceValue T

def DeterminantAtZero : Prop := ∀ (H : Type v) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H),
    FredholmDeterminantValue T 0 = 1

/-- Scalar assembly lemma. The required factorial coefficient estimate is
also established for actual trace-class operators. -/
def FactorialSeriesMajorant : Prop :=
  ∀ (a : ℕ → ℂ) (C : ℝ), 0 ≤ C →
    (∀ n, ‖a n‖ ≤ C ^ n / (n.factorial : ℝ)) → ∀ z : ℂ,
      Summable (fun n : ℕ => ‖z ^ n * a n‖) ∧
        ‖∑' n : ℕ, z ^ n * a n‖ ≤ Real.exp (‖z‖ * C)

/-- A summable expansion by unit rank-one factors constructs trace class and
bounds its canonical trace norm. Compactness is a conclusion. -/
def NuclearExpansionCriterion : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] {I : Type z}
    (a : I → ℝ), (∀ j, 0 ≤ a j) → Summable a →
    ∀ (e : I → E) (f : I → F), (∀ j, ‖e j‖ = 1) → (∀ j, ‖f j‖ = 1) →
    ∀ (T : E →L[𝕜] F),
    (∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x)) →
      TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ≤ ∑' j, a j

/-- Orthonormal rank-one factors give the exact canonical trace norm, with
zero weights and arbitrary index types allowed. -/
def OrthonormalExpansionTraceNorm : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] {I : Type z}
    (a : I → ℝ), (∀ j, 0 ≤ a j) → Summable a →
    ∀ (e : I → E) (f : I → F), Orthonormal 𝕜 e → Orthonormal 𝕜 f →
    ∀ (T : E →L[𝕜] F),
    (∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x)) →
      TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T = ∑' j, a j

/-- The positive singular directions characterize the canonical trace-class
condition once compactness is known; the norm includes every multiplicity. -/
def TraceClassSingularCriterion : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H K T,
    Summable S.sigma →
      TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T = ∑' j, S.sigma j

/-- Full Hilbert bases extending both positive singular families. Every added
direction lies in the respective full kernel; no separability of either kernel
is assumed. These bases will be used to transport the exterior expansion. -/
def SingularBasisExtensions : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H K T),
    ∃ (W : Set H) (b : HilbertBasis W ℂ H) (e : S.Index ↪ W)
      (V : Set K) (c : HilbertBasis V ℂ K) (f : S.Index ↪ V),
      (∀ j, b (e j) = S.rightVector j) ∧
      (∀ j, c (f j) = S.leftVector j) ∧
      (∀ k, k ∉ Set.range e → T (b k) = 0) ∧
      (∀ k, k ∉ Set.range f → ContinuousLinearMap.adjoint T (c k) = 0)

/-- The algebraic exterior functor transports every tuple of positive right
singular directions to the corresponding left tuple with the product weight. -/
def AlgebraicSingularTransport : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H K T)
    (n : ℕ) (j : Fin n → S.Index),
    exteriorPower.map n T.toLinearMap
      (exteriorPower.ιMulti ℂ n (fun i => S.rightVector (j i))) =
        ((∏ i, S.sigma (j i) : ℝ) : ℂ) •
          exteriorPower.ιMulti ℂ n (fun i => S.leftVector (j i))

/-- The analogous transport for the Hilbert adjoint. -/
def AlgebraicAdjointSingularTransport : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K)
    (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H K T)
    (n : ℕ) (j : Fin n → S.Index),
    exteriorPower.map n T.adjoint.toLinearMap
      (exteriorPower.ιMulti ℂ n (fun i => S.leftVector (j i))) =
        ((∏ i, S.sigma (j i) : ℝ) : ℂ) •
          exteriorPower.ιMulti ℂ n (fun i => S.rightVector (j i))

/-- The scalar estimate to be applied to products of exterior singular values.
This does not assume an exterior operator has already been constructed. -/
def SubsetProductBound : Prop :=
  ∀ (α : Type w) (f : α → ℝ), (∀ i, 0 ≤ f i) → Summable f → ∀ n : ℕ,
    Summable (fun s : Set.powersetCard α n => ∏ i ∈ s.val, f i) ∧
      (∑' s : Set.powersetCard α n, ∏ i ∈ s.val, f i) ≤
        (∑' i, f i) ^ n / (n.factorial : ℝ)

/-- The total sum of finite products, including the empty product, is
summable and bounded by the exponential of the scalar sum. -/
def SubsetGeneratingBound : Prop :=
  ∀ (α : Type w) (f : α → ℝ), (∀ i, 0 ≤ f i) → Summable f →
    ∀ (r : ℝ), 0 ≤ r →
      Summable (fun s : Finset α => ∏ i ∈ s, r * f i) ∧
      (∑' s : Finset α, ∏ i ∈ s, r * f i) ≤ Real.exp (r * ∑' i, f i)

/-- Every Hilbert basis gives absolutely summable degree-n principal minors
with the sharp factorial trace-norm bound. -/
def PrincipalMinorTraceNormBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ {ι : Type w} (b : HilbertBasis ι ℂ H) (n : ℕ),
    Summable (fun s : Set.powersetCard ι n => ‖PrincipalMinorValue b T s.val‖) ∧
      (∑' s : Set.powersetCard ι n, ‖PrincipalMinorValue b T s.val‖) ≤
        TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ)

/-- The actual coordinate coefficients satisfy the factorial bound. -/
def ExteriorTraceFactorialBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ n : ℕ, ‖ExteriorTraceValue T n‖ ≤
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ)

/-- Absolute convergence of the defining series and its exponential bound
for every complex parameter. -/
def FredholmSeriesBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ z : ℂ, Summable (fun n : ℕ => ‖z ^ n * ExteriorTraceValue T n‖) ∧
      ‖FredholmDeterminantValue T z‖ ≤ Real.exp
        (‖z‖ * TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T)

/-- The completed coordinate model, with normalized subset wedges. -/
abbrev CoordinateSpaceValue (ι : Type w) (n : ℕ) : Type w := ExteriorCoordinates.Space ι n

def CoordinateSpaceType := (ι : Type w) → ℕ → Type w

def CoordinateWedgeValue {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type w} (b : HilbertBasis ι ℂ H) (n : ℕ) :
    H [⋀^Fin n]→ₗ[ℂ] CoordinateSpaceValue ι n := ExteriorCoordinates.wedgeAlternating b

def CoordinateWedgeType := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type w}, HilbertBasis ι ℂ H → (n : ℕ) → (H [⋀^Fin n]→ₗ[ℂ] CoordinateSpaceValue ι n)

def CoordinateEmbeddingValue {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type w} (b : HilbertBasis ι ℂ H) (n : ℕ) :
    ⋀[ℂ]^n H →ₗ[ℂ] CoordinateSpaceValue ι n := ExteriorCoordinates.embed b

def CoordinateEmbeddingType := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type w}, HilbertBasis ι ℂ H → (n : ℕ) → (⋀[ℂ]^n H →ₗ[ℂ] CoordinateSpaceValue ι n)

/-- This is the Gram determinant normalization, for complex spaces of arbitrary
Hilbert dimension, including degree zero. -/
def CoordinateWedgeGram : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type w}
    (b : HilbertBasis ι ℂ H) (n : ℕ) (x y : Fin n → H),
    inner ℂ (CoordinateWedgeValue b n x) (CoordinateWedgeValue b n y) =
      Matrix.det (fun i j => inner ℂ (x i) (y j))

def CoordinateWedgeDense : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type w}
    (b : HilbertBasis ι ℂ H) (n : ℕ),
    (Submodule.span ℂ (Set.range (fun x : Fin n → H => CoordinateWedgeValue b n x))).topologicalClosure = ⊤

def CoordinateWedgeContinuous : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type w}
    (b : HilbertBasis ι ℂ H) (n : ℕ), Continuous (CoordinateWedgeValue b n)

/-- A total rank-one-series construction; its summability, compactness and
trace-ideal properties are proved for summable nonnegative weights. -/
def RankOneSeriesValue {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y] {I : Type z}
    (a : I → ℝ) (e : I → X) (f : I → Y) : X →L[𝕜] Y :=
  ∑' j, (a j : 𝕜) • InnerProductSpace.rankOne 𝕜 (f j) (e j)

def RankOneSeriesType := ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [InnerProductSpace 𝕜 X] [InnerProductSpace 𝕜 Y] {I : Type z},
  (I → ℝ) → (I → X) → (I → Y) → (X →L[𝕜] Y)

/-- Canonical trace formula obtained from actual summable expansion data. -/
def NuclearExpansionTrace : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X] {I : Type z}
    (a : I → ℝ), (∀ j, 0 ≤ a j) → Summable a →
    ∀ (e f : I → X), (∀ j, ‖e j‖ = 1) → (∀ j, ‖f j‖ = 1) →
    ∀ (T : X →L[𝕜] X),
    (∀ x, HasSum (fun j => ((a j : 𝕜) * inner 𝕜 (e j) x) • f j) (T x)) →
    TraceIdeals.TraceClassDefinitions.Spec.TraceValue T =
      ∑' j, (a j : 𝕜) * inner 𝕜 (e j) (f j)

/-- The unique continuous extension of the exterior functor when it exists.
Existence for trace-class operators is constructed, rather than assumed, in
the implementation. The fallback makes the definition total. -/
def CoordinateOperatorValue {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    {α : Type u} {β : Type z} (b : HilbertBasis α ℂ H) (d : HilbertBasis β ℂ K)
    (T : H →L[ℂ] K) (n : ℕ) : CoordinateSpaceValue α n →L[ℂ] CoordinateSpaceValue β n := by
  classical
  exact if h : ∃ A : CoordinateSpaceValue α n →L[ℂ] CoordinateSpaceValue β n,
      ∀ x : Fin n → H, A (CoordinateWedgeValue b n x) =
        CoordinateWedgeValue d n (T ∘ x)
    then Classical.choose h else 0

def CoordinateOperatorType := ∀ {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
  {α : Type u} {β : Type z}, HilbertBasis α ℂ H → HilbertBasis β ℂ K →
  (H →L[ℂ] K) → (n : ℕ) → (CoordinateSpaceValue α n →L[ℂ] CoordinateSpaceValue β n)

/-- The Hilbert exterior operator on the canonical completed exterior space. -/
def ExteriorOperatorValue {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (n : ℕ) :
    CoordinateSpaceValue (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
      (𝕜 := ℂ) (H := H)) n →L[ℂ]
    CoordinateSpaceValue (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
      (𝕜 := ℂ) (H := H)) n :=
  CoordinateOperatorValue TraceIdeals.TraceClassDefinitions.Spec.chosenBasis
    TraceIdeals.TraceClassDefinitions.Spec.chosenBasis T n

def ExteriorOperatorType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H], (H →L[ℂ] H) → (n : ℕ) →
  (CoordinateSpaceValue (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
    (𝕜 := ℂ) (H := H)) n →L[ℂ]
   CoordinateSpaceValue (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
    (𝕜 := ℂ) (H := H)) n)

/-- Constructed exterior powers are trace class, have the factorial trace-norm
bound, and their actual trace equals the principal-minor coefficient. -/
def ExteriorConstruction : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ n : ℕ,
    (∀ x : Fin n → H, ExteriorOperatorValue T n
      (CoordinateWedgeValue TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n x) =
      CoordinateWedgeValue TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n (T ∘ x)) ∧
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (ExteriorOperatorValue T n) ∧
    TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (ExteriorOperatorValue T n) ≤
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ) ∧
    TraceIdeals.TraceClassDefinitions.Spec.TraceValue (ExteriorOperatorValue T n) = ExteriorTraceValue T n

/-- Every positive singular system gives the exact trace norm on the exterior
power, retaining all multiplicities and the empty product in degree zero. -/
def ExteriorSingularTraceNorm : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ (S : CompactSpectral.SingularExpansion.Spec.SingularSystem ℂ H H T) (n : ℕ),
    TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (ExteriorOperatorValue T n) =
      ∑' s : Set.powersetCard S.Index n, ∏ j ∈ s.val, S.sigma j

/-- The completed degree-zero functor is the scalar identity, with vacuum
wedge equal to 1, and the completed degree-one functor is T itself under the
natural linear isometric identifications. -/
def ExteriorLowDegrees : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    (∃ e : CoordinateSpaceValue (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
        (𝕜 := ℂ) (H := H)) 0 ≃ₗᵢ[ℂ] ℂ,
      (∀ x : Fin 0 → H, e (CoordinateWedgeValue
        TraceIdeals.TraceClassDefinitions.Spec.chosenBasis 0 x) = 1) ∧
      ∀ z : ℂ, e (ExteriorOperatorValue T 0 (e.symm z)) = z) ∧
    (∃ e : CoordinateSpaceValue (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
        (𝕜 := ℂ) (H := H)) 1 ≃ₗᵢ[ℂ] H,
      (∀ x : H, e (CoordinateWedgeValue
        TraceIdeals.TraceClassDefinitions.Spec.chosenBasis 1 (fun _ : Fin 1 => x)) = x) ∧
      ∀ x : H, e (ExteriorOperatorValue T 1 (e.symm x)) = T x)

/-- The constructed continuous exterior functor agrees with the original
algebraic exterior functor under the canonical wedge map. -/
def ExteriorAlgebraicCompatibility : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ n : ℕ,
    (ExteriorOperatorValue T n).toLinearMap.comp
      (CoordinateEmbeddingValue TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n) =
    (CoordinateEmbeddingValue TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n).comp
      (AlgebraicExteriorMapValue n T)

end ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec
