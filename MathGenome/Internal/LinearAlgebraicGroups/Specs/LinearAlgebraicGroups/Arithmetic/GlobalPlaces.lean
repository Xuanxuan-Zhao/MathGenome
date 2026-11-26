import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Valuation.Integral

noncomputable section

open IsDedekindDomain
open scoped NumberField Polynomial RatFunc WithZero

namespace LinearAlgebraicGroups.Arithmetic

/-- A global function field over a finite field of constants can be presented by a
transcendental element over which the extension is finite and separable. -/
structure SeparatingParameter (F K : Type*) [Field F] [Field K] [Algebra F K] where
  element : K
  transcendental : Transcendental F element
  finite : Module.Finite (IntermediateField.adjoin F {element}) K
  separable : Algebra.IsSeparable (IntermediateField.adjoin F {element}) K

namespace SeparatingParameter

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The embedding of the rational function field determined by the parameter. -/
def rationalMap (t : SeparatingParameter F K) : F⟮X⟯ →ₐ[F] K :=
  (IntermediateField.adjoin F {t.element}).val.comp
    (RatFunc.algEquivOfTranscendental t.element t.transcendental).toAlgHom

/-- The polynomial embedding sending the variable to the parameter. -/
@[instance_reducible]
def polynomialAlgebra (t : SeparatingParameter F K) : Algebra F[X] K :=
  ((Polynomial.aeval t.element).toRingHom).toAlgebra

/-- The rational function field acts through the chosen parameter. -/
@[instance_reducible]
def rationalAlgebra (t : SeparatingParameter F K) : Algebra F⟮X⟯ K :=
  t.rationalMap.toRingHom.toAlgebra

/-- The normalization of the affine line in the function field for this parameter. -/
def integerSubalgebra (t : SeparatingParameter F K) : @Subalgebra F[X] K _ _ t.polynomialAlgebra :=
  @integralClosure F[X] K _ _ t.polynomialAlgebra

/-- The carrier of the normalization. -/
abbrev integerRing (t : SeparatingParameter F K) := ↥t.integerSubalgebra

/-- The inverse parameter describes the affine chart at the pole of the original parameter. -/
def inverse (t : SeparatingParameter F K) : SeparatingParameter F K := by
  have h := t.transcendental
  have heq : IntermediateField.adjoin F {t.element⁻¹} = IntermediateField.adjoin F {t.element} := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr
        (inv_mem (IntermediateField.mem_adjoin_simple_self F t.element))
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      simpa only [inv_inv] using
        inv_mem (IntermediateField.mem_adjoin_simple_self F t.element⁻¹)
  refine ⟨t.element⁻¹, ?_, heq ▸ t.finite, heq ▸ t.separable⟩
  intro hi
  exact h (by simpa only [inv_inv] using hi.inv)

instance (t : SeparatingParameter F K) :
    @IsScalarTower F[X] F⟮X⟯ K _ t.rationalAlgebra.toSMul t.polynomialAlgebra.toSMul := by
  let := t.polynomialAlgebra
  let := t.rationalAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro p
  change Polynomial.aeval t.element p = t.rationalMap (algebraMap F[X] F⟮X⟯ p)
  simp [rationalMap]

instance (t : SeparatingParameter F K) : @Module.Finite F⟮X⟯ K _ _ t.rationalAlgebra.toModule := by
  let := t.rationalAlgebra
  let := t.finite
  refine Module.Finite.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental t.element t.transcendental).symm.toRingEquiv
    (RingEquiv.refl K) ?_
  ext x
  exact congrArg Subtype.val
    ((RatFunc.algEquivOfTranscendental t.element t.transcendental).apply_symm_apply x)

instance (t : SeparatingParameter F K) : @Algebra.IsSeparable F⟮X⟯ K _ _ t.rationalAlgebra := by
  let := t.rationalAlgebra
  let := t.separable
  refine Algebra.IsSeparable.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental t.element t.transcendental).symm.toRingEquiv
    (RingEquiv.refl K) ?_
  ext x
  exact congrArg Subtype.val
    ((RatFunc.algEquivOfTranscendental t.element t.transcendental).apply_symm_apply x)

instance (t : SeparatingParameter F K) : IsFractionRing t.integerRing K := by
  let := t.polynomialAlgebra
  let := t.rationalAlgebra
  exact inferInstanceAs (IsFractionRing (FunctionField.ringOfIntegers F K) K)

instance (t : SeparatingParameter F K) : IsDedekindDomain t.integerRing := by
  let := t.polynomialAlgebra
  let := t.rationalAlgebra
  exact inferInstanceAs (IsDedekindDomain (FunctionField.ringOfIntegers F K))

end SeparatingParameter

/-- Finite places of a number field in the indexing used by the Mathlib adele ring. -/
abbrev NumberFinitePlace (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (𝓞 K)

/-- All places of a number field. -/
abbrev NumberPlace (K : Type*) [Field K] [NumberField K] :=
  NumberFinitePlace K ⊕ NumberField.InfinitePlace K

/-- All places of a global function field, intrinsically as nontrivial valuation rings.
A finite constant subfield is contained in every such ring. -/
abbrev FunctionPlace (K : Type*) [Field K] :=
  {V : ValuationSubring K // V ≠ ⊤}

namespace FunctionPlace

variable {K : Type*} [Field K]

/-- The local field, defined using the canonical valuation of the valuation ring. -/
abbrev Completion (v : FunctionPlace K) := v.1.valuation.Completion

/-- The ring of integers for the extended valuation. -/
def integers (v : FunctionPlace K) : ValuationSubring v.Completion :=
  (Valued.v (R := v.Completion)).valuationSubring

/-- The dense scalar embedding into the completion. -/
def embedding (v : FunctionPlace K) : K →+* v.Completion :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv v.1.valuation).symm.toRingHom

end FunctionPlace

namespace NumberPlace

variable {K : Type*} [Field K] [NumberField K]

/-- The field at a number-field place. -/
abbrev Completion : NumberPlace K → Type _
  | .inl v => v.adicCompletion K
  | .inr v => v.Completion

instance (v : NumberPlace K) : Field v.Completion :=
  match v with
  | .inl w => inferInstanceAs (Field (w.adicCompletion K))
  | .inr w => inferInstanceAs (Field w.Completion)

instance (v : NumberPlace K) : TopologicalSpace v.Completion :=
  match v with
  | .inl w => inferInstanceAs (TopologicalSpace (w.adicCompletion K))
  | .inr w => inferInstanceAs (TopologicalSpace w.Completion)

/-- The canonical scalar embedding associated to a number-field place. -/
def embedding (v : NumberPlace K) : K →+* v.Completion :=
  match v with
  | .inl w => algebraMap K (w.adicCompletion K)
  | .inr w => algebraMap K w.Completion

end NumberPlace

/-- The full function-field adele ring, including all places over the pole of any
chosen parameter. -/
abbrev FunctionAdeleRing (K : Type*) [Field K] :=
  open scoped RestrictedProduct in
    Πʳ v : FunctionPlace K, [v.Completion, v.integers]

universe u v

/-- A description of a global field. The parameter in the function-field case
is used to prove properties of the places, whose definition is intrinsic. -/
inductive GlobalFieldData (K : Type u) [Field K] : Type (max u (v + 1))
  | number (numberField : NumberField K)
  | function (F : Type v) [Field F] [Finite F] [Algebra F K]
      (parameter : SeparatingParameter F K)

namespace GlobalFieldData

variable {K : Type u} [Field K]

/-- All nonarchimedean places of the global field. -/
abbrev FinitePlace : GlobalFieldData.{u, v} K → Type u
  | .number h => letI := h; NumberFinitePlace K
  | @function _ _ _ _ _ _ _ => FunctionPlace K

/-- Archimedean places, present only in the number-field case. -/
abbrev InfinitePlace : GlobalFieldData.{u, v} K → Type u
  | .number _ => NumberField.InfinitePlace K
  | @function _ _ _ _ _ _ _ => PEmpty

/-- All places, with their archimedean or nonarchimedean designation. -/
abbrev Place (D : GlobalFieldData.{u, v} K) := D.FinitePlace ⊕ D.InfinitePlace

/-- Completion at a nonarchimedean place. -/
abbrev FiniteCompletion (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) : Type u :=
  match D, w with
  | .number h, w => letI := h; w.adicCompletion K
  | @function _ _ _ _ _ _ _, w => w.Completion

instance (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) : Field (D.FiniteCompletion w) :=
  match D, w with
  | .number h, w => letI := h; inferInstanceAs (Field (w.adicCompletion K))
  | @function _ _ _ _ _ _ _, w => inferInstanceAs (Field w.Completion)

instance (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) :
    TopologicalSpace (D.FiniteCompletion w) :=
  match D, w with
  | .number h, w => letI := h; inferInstanceAs (TopologicalSpace (w.adicCompletion K))
  | @function _ _ _ _ _ _ _, w => inferInstanceAs (TopologicalSpace w.Completion)

instance (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) :
    ValuativeRel (D.FiniteCompletion w) :=
  match D, w with
  | .number h, w => letI := h; inferInstanceAs (ValuativeRel (w.adicCompletion K))
  | @function _ _ _ _ _ _ _, w => inferInstanceAs (ValuativeRel w.Completion)

/-- The completion at an archimedean place. -/
abbrev InfiniteCompletion (D : GlobalFieldData.{u, v} K) (w : D.InfinitePlace) : Type u :=
  match D, w with
  | .number _, w => w.Completion
  | @function _ _ _ _ _ _ _, w => w.elim

/-- The field at an arbitrary place. -/
abbrev Completion (D : GlobalFieldData.{u, v} K) (w : D.Place) : Type u :=
  w.elim D.FiniteCompletion D.InfiniteCompletion

instance (D : GlobalFieldData.{u, v} K) (w : D.Place) : Field (D.Completion w) :=
  match D, w with
  | D, .inl w => inferInstanceAs (Field (D.FiniteCompletion w))
  | .number _, .inr w => inferInstanceAs (Field w.Completion)
  | @function _ _ _ _ _ _ _, .inr w => w.elim

instance (D : GlobalFieldData.{u, v} K) (w : D.Place) : TopologicalSpace (D.Completion w) :=
  match D, w with
  | D, .inl w => inferInstanceAs (TopologicalSpace (D.FiniteCompletion w))
  | .number _, .inr w => inferInstanceAs (TopologicalSpace w.Completion)
  | @function _ _ _ _ _ _ _, .inr w => w.elim

/-- The canonical embedding of the global field into a completion. -/
def embedding (D : GlobalFieldData.{u, v} K) (w : D.Place) : K →+* D.Completion w :=
  match D, w with
  | .number h, .inl w => letI := h; algebraMap K (w.adicCompletion K)
  | .number _, .inr w => algebraMap K w.Completion
  | @function _ _ _ _ _ _ _, .inl w => w.embedding
  | @function _ _ _ _ _ _ _, .inr w => w.elim

/-- The ring of integers at a nonarchimedean place. -/
def integers (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace) :
    ValuationSubring (D.FiniteCompletion w) :=
  match D, w with
  | .number h, w => letI := h; w.adicCompletionIntegers K
  | @function _ _ _ _ _ _ _, w => w.integers

/-- The scalar adele ring, with the ordinary infinite factors and the restricted
product at the finite places. -/
abbrev AdeleRing : GlobalFieldData.{u, v} K → Type u
  | .number h => letI := h; NumberField.AdeleRing (𝓞 K) K
  | @function _ _ _ _ _ _ _ => FunctionAdeleRing K

instance (D : GlobalFieldData.{u, v} K) : CommRing D.AdeleRing :=
  match D with
  | .number h => letI := h; inferInstanceAs (CommRing (NumberField.AdeleRing (𝓞 K) K))
  | @function _ _ _ _ _ _ _ => inferInstanceAs (CommRing (FunctionAdeleRing K))

instance (D : GlobalFieldData.{u, v} K) : TopologicalSpace D.AdeleRing :=
  match D with
  | .number h => letI := h; inferInstanceAs (TopologicalSpace (NumberField.AdeleRing (𝓞 K) K))
  | @function _ _ _ _ _ _ _ => inferInstanceAs (TopologicalSpace (FunctionAdeleRing K))

/-- The coordinate of an adele at a chosen place. -/
def coordinate (D : GlobalFieldData.{u, v} K) (w : D.Place)
    (a : D.AdeleRing) : D.Completion w :=
  match D, w, a with
  | .number _, .inl w, a => a.2 w
  | .number _, .inr w, a => a.1 w
  | @function _ _ _ _ _ _ _, .inl w, a => a w
  | @function _ _ _ _ _ _ _, .inr w, _ => w.elim

end GlobalFieldData

namespace GlobalPlacesSpec

set_option linter.checkUnivs false in
def placeOfPrimeType :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K), HeightOneSpectrum t.integerRing → FunctionPlace K

def placeOfPrimeValue {F K : Type*} [Field F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (v : HeightOneSpectrum t.integerRing) : FunctionPlace K :=
  ⟨(v.valuation K).valuationSubring, fun h =>
    ((v.valuation K).valuationSubring_eq_top_iff.mp h) inferInstance⟩

def numberDiagonalType :=
  ∀ {K : Type*} [Field K] [NumberField K], K →+* NumberField.AdeleRing (𝓞 K) K

def numberDiagonalValue {K : Type*} [Field K] [NumberField K] :
    K →+* NumberField.AdeleRing (𝓞 K) K := algebraMap K _

def realCompletion : Prop :=
  ∀ {K : Type*} [Field K] (v : NumberField.InfinitePlace K), v.IsReal →
    ∃ e : v.Completion ≃+* ℝ, Isometry e

def complexCompletion : Prop :=
  ∀ {K : Type*} [Field K] (v : NumberField.InfinitePlace K), v.IsComplex →
    ∃ e : v.Completion ≃+* ℂ, Isometry e

def primePlaceInjective : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] (t : SeparatingParameter F K),
    Function.Injective (placeOfPrimeValue t)

def primePlaceRange : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (t : SeparatingParameter F K),
    Set.range (placeOfPrimeValue t) = {v : FunctionPlace K | t.element ∈ v.1}

def placesCovered : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (t : SeparatingParameter F K),
    Set.range (placeOfPrimeValue t) ∪ Set.range (placeOfPrimeValue t.inverse) = Set.univ

def polesFromInverseChart : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] (t : SeparatingParameter F K) [Finite F],
    {v : FunctionPlace K | t.element ∉ v.1} =
      placeOfPrimeValue t.inverse '' {w | w.valuation K t.element⁻¹ < 1}

open Classical in
def infinityFromParameter : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (t : SeparatingParameter F K) (V : FunctionPlace K),
    V.1.comap t.rationalMap.toRingHom = (RatFunc.inftyValuation F).valuationSubring ↔
      t.element ∉ V.1

def polesFinite : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (t : SeparatingParameter F K), {v : FunctionPlace K | t.element ∉ v.1}.Finite

def compareCompletions : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] (t : SeparatingParameter F K)
    (w : HeightOneSpectrum t.integerRing),
    ∃ e : (placeOfPrimeValue t w).Completion ≃+* w.adicCompletion K,
      IsUniformInducing e ∧
      (∀ x : K, e ((placeOfPrimeValue t w).embedding x) = algebraMap K (w.adicCompletion K) x) ∧
      ∀ x, e x ∈ w.adicCompletionIntegers K ↔ x ∈ (placeOfPrimeValue t w).integers

def adicLocalField : Prop :=
  ∀ {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (w : HeightOneSpectrum R) [Finite (R ⧸ w.asIdeal)],
    IsNonarchimedeanLocalField (w.adicCompletion K)

def finiteLocalFields : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace),
    IsNonarchimedeanLocalField (D.FiniteCompletion w)

def finiteIntegersProperties : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace),
    IsCompact (D.integers w : Set (D.FiniteCompletion w)) ∧
      IsOpen (D.integers w : Set (D.FiniteCompletion w)) ∧
      Finite (IsLocalRing.ResidueField (D.integers w))

def integersAreUnitBall : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K) (w : D.FinitePlace),
    D.integers w = (ValuativeRel.valuation (D.FiniteCompletion w)).valuationSubring

def functionScalarDiagonalUnique : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite F]
    (_t : SeparatingParameter F K),
    ∃! d : K →+* FunctionAdeleRing K, ∀ (x : K) (v : FunctionPlace K),
      d x v = v.embedding x

def almostEverywhereIntegral : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K) (x : K),
    {w : D.FinitePlace | D.embedding (.inl w) x ∉ D.integers w}.Finite

def adeleTopology : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K), IsTopologicalRing D.AdeleRing

def scalarDiagonal : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K),
    ∃ d : K →+* D.AdeleRing, Function.Injective d ∧
      ∀ w x, D.coordinate w (d x) = D.embedding w x

def localProperties : Prop :=
  ∀ (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
    ValuativeRel.IsDiscrete K ∧
      Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).valuationSubring) ∧
      IsCompact ((ValuativeRel.valuation K).valuationSubring : Set K) ∧
      IsOpen ((ValuativeRel.valuation K).valuationSubring : Set K)

def localComplete : Prop :=
  ∀ (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsNonarchimedeanLocalField K], CompleteSpace K

def finiteExtension : Prop :=
  ∀ {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [Algebra K L] [FiniteDimensional K L],
    ∃ r : ValuativeRel L, ∃ T : TopologicalSpace L,
      letI : ValuativeRel L := r
      letI : TopologicalSpace L := T
      ValuativeExtension K L ∧ IsNonarchimedeanLocalField L ∧
        Finite (IsLocalRing.ResidueField (ValuativeRel.valuation L).valuationSubring) ∧
        (∀ b : Module.Basis (Fin (Module.finrank K L)) K L,
          Continuous b.equivFun ∧ Continuous b.equivFun.symm) ∧
        ∀ s : ValuativeRel L, @ValuativeExtension K L _ _ _ s _ → s = r

end GlobalPlacesSpec

end LinearAlgebraicGroups.Arithmetic
