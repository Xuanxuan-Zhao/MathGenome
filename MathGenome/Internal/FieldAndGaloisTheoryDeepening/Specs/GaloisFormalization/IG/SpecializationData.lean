import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.Algebra.Polynomial.Roots

/-!
# Specialization data over a rational function field

The variable of `RatFunc k` is the parameter `t`. The variable of a polynomial over
`RatFunc k` is the independent variable `X`, and the series variable is `u`.
-/

open scoped Polynomial nonZeroDivisors

namespace Specs.GaloisFormalization.IG.SpecializationData

noncomputable section

variable {k : Type*} [Field k]

/-- A rational function is regular at `a` if its reduced denominator is nonzero there. -/
def RegularAt (a : k) (x : RatFunc k) : Prop :=
  x.denom.eval a ≠ 0

/-- Coefficientwise regularity at the specified point. -/
def PolynomialRegularAt (a : k) (f : (RatFunc k)[X]) : Prop :=
  ∀ n : ℕ, RegularAt a (f.coeff n)

private theorem eval_ne_zero_of_dvd {a : k} {p q : k[X]}
    (h : p ∣ q) (hq : q.eval a ≠ 0) : p.eval a ≠ 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [Polynomial.eval_mul] at hq
  exact left_ne_zero_of_mul hq

/-- The subring of rational functions regular at the point. -/
def regularCoefficients (a : k) : Subring (RatFunc k) where
  carrier := {x | RegularAt a x}
  zero_mem' := by simp [RegularAt]
  one_mem' := by simp [RegularAt]
  add_mem' {x y} hx hy :=
    eval_ne_zero_of_dvd (RatFunc.denom_add_dvd x y)
      (by simpa only [Polynomial.eval_mul] using mul_ne_zero hx hy)
  mul_mem' {x y} hx hy :=
    eval_ne_zero_of_dvd (RatFunc.denom_mul_dvd x y)
      (by simpa only [Polynomial.eval_mul] using mul_ne_zero hx hy)
  neg_mem' {x} hx := by
    have hd : (-x).denom ∣ x.denom := (RatFunc.denom_dvd x.denom_ne_zero).2
      ⟨-x.num, by rw [map_neg, neg_div, RatFunc.num_div_denom]⟩
    exact eval_ne_zero_of_dvd hd hx

/-- Ordinary evaluation on the regular coefficient subring. -/
def evalRegular (a : k) : regularCoefficients a →+* k where
  toFun x := RatFunc.eval (RingHom.id k) a x
  map_zero' := RatFunc.eval_zero _ _
  map_one' := RatFunc.eval_one _ _
  map_add' x y := RatFunc.eval_add (RingHom.id k) a
    (by rw [Polynomial.eval₂_id]; exact x.property)
    (by rw [Polynomial.eval₂_id]; exact y.property)
  map_mul' x y := RatFunc.eval_mul (RingHom.id k) a
    (by rw [Polynomial.eval₂_id]; exact x.property)
    (by rw [Polynomial.eval₂_id]; exact y.property)

/-- View a coefficientwise regular polynomial as a polynomial over the regular subring. -/
def regularPolynomial (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f) :
    (regularCoefficients a)[X] :=
  f.toSubring (regularCoefficients a) (by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact hf n)

/-- The fibre polynomial `f(a,X)`. -/
def specialize (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f) : k[X] :=
  (regularPolynomial a f hf).map (evalRegular a)

variable (ℓ : Type*) [Field ℓ]

/-- The Laurent monomial `u`. -/
def uniformizer : LaurentSeries ℓ :=
  HahnSeries.single 1 1

/-- The embedding extending a power series by zero in negative degrees. -/
def powerToLaurent : PowerSeries ℓ →+* LaurentSeries ℓ :=
  HahnSeries.ofPowerSeries ℤ ℓ

section Substitution

variable [Algebra k ℓ]

/-- Taylor translation followed by inclusion in power series over the coefficient field. -/
def polynomialSeries (a : k) : k[X] →ₐ[k] PowerSeries ℓ :=
  (Polynomial.coeToPowerSeries.algHom ℓ).comp (Polynomial.taylorAlgHom a)

/-- Substitute the translated parameter into Laurent series. -/
def polynomialLaurent (a : k) : k[X] →ₐ[k] LaurentSeries ℓ where
  toRingHom := (powerToLaurent ℓ).comp (polynomialSeries ℓ a).toRingHom
  commutes' c := by
    change powerToLaurent ℓ (polynomialSeries ℓ a (algebraMap k k[X] c)) = _
    rw [AlgHom.commutes]
    rfl

private theorem polynomialLaurent_injective (a : k) :
    Function.Injective (polynomialLaurent ℓ a) := by
  exact (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℓ)).comp
    ((PowerSeries.map_injective _ (algebraMap k ℓ).injective).comp
      ((Polynomial.coe_injective k).comp (Polynomial.taylor_injective a)))

/-- The fraction-field extension of `t ↦ a + u`. -/
def substitution (a : k) : RatFunc k →ₐ[k] LaurentSeries ℓ :=
  RatFunc.liftAlgHom (polynomialLaurent ℓ a)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polynomialLaurent_injective ℓ a))

/-- The `k(t)`-algebra structure on the Laurent field at the specified point. -/
abbrev substitutionAlgebra (a : k) : Algebra (RatFunc k) (LaurentSeries ℓ) :=
  (substitution ℓ a).toRingHom.toAlgebra

end Substitution

/-- Least exponent of a Laurent series, with `⊤` at zero. -/
def seriesOrder (x : LaurentSeries ℓ) : WithTop ℤ :=
  x.orderTop

variable {ℓ}

/-- The additive valuation of the Laurent field, pulled back to `L`. -/
def inducedOrder {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ) :
    AddValuation L (WithTop ℤ) :=
  (HahnSeries.addVal ℤ ℓ).comap i

/-- Elements of nonnegative order for the pulled-back valuation. -/
def valuationRing {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ) : ValuationSubring L :=
  (AddValuation.toValuation (inducedOrder i)).valuationSubring

/-- The maximal ideal, consisting of elements of strictly positive order. -/
def positiveIdeal {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ) :
    Ideal (valuationRing i) :=
  IsLocalRing.maximalIdeal (valuationRing i)

/-- The residue field is the quotient of the valuation ring by its maximal ideal. -/
abbrev residueField {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ) : Type _ :=
  IsLocalRing.ResidueField (valuationRing i)

/-- Nonnegative Laurent order is equivalent to lying in the power-series image. -/
theorem nonnegative_iff_powerSeries (x : LaurentSeries ℓ) :
    0 ≤ seriesOrder ℓ x ↔ ∃ F : PowerSeries ℓ, powerToLaurent ℓ F = x := by
  change 0 ≤ x.orderTop ↔ ∃ F : PowerSeries ℓ, (F : LaurentSeries ℓ) = x
  rw [← LaurentSeries.val_le_one_iff_eq_coe ℓ x]
  have hv := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero ℓ (D := 0) (f := x)
  rw [neg_zero, WithZero.exp_zero] at hv
  rw [hv]
  simp only [← WithTop.coe_zero, HahnSeries.le_orderTop_iff_forall, WithTop.coe_lt_coe]

private def powerSeriesEquiv :
    PowerSeries ℓ ≃+* valuationRing (RingHom.id (LaurentSeries ℓ)) :=
  RingEquiv.ofBijective
    ((powerToLaurent ℓ).codRestrict _ fun F =>
      (nonnegative_iff_powerSeries _).2 ⟨F, rfl⟩)
    ⟨fun _ _ h => HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨F, hF⟩ := (nonnegative_iff_powerSeries _).1 x.property
        exact ⟨F, Subtype.ext hF⟩⟩

/-- The image of an element of the valuation ring, regarded as a power series in `u`. -/
def integralSeries {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ) :
    valuationRing i →+* PowerSeries ℓ :=
  powerSeriesEquiv.symm.toRingHom.comp
    ((i.comp (valuationRing i).subtype).codRestrict _ fun x => x.property)

theorem powerToLaurent_integralSeries {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ)
    (x : valuationRing i) : powerToLaurent ℓ (integralSeries i x) = i x :=
  congrArg Subtype.val (powerSeriesEquiv.apply_symm_apply ⟨i x, x.property⟩)

/-- The constant coefficient of an element in the valuation ring. -/
def reduction {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ) :
    valuationRing i →+* ℓ :=
  PowerSeries.constantCoeff.comp (integralSeries i)

theorem reduction_apply {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ)
    (x : valuationRing i) : reduction i x = (i x).coeff 0 := by
  have hcoeff := LaurentSeries.coeff_coe_powerSeries (integralSeries i x) 0
  rw [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hcoeff
  exact hcoeff.symm.trans (congrArg (fun y : LaurentSeries ℓ => y.coeff 0)
    (powerToLaurent_integralSeries i x))

private theorem reduction_eq_zero_iff {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ)
    (x : valuationRing i) : reduction i x = 0 ↔ x ∈ positiveIdeal i := by
  rw [reduction_apply]
  have hideal : x ∈ positiveIdeal i ↔ 0 < (i x).orderTop :=
    (AddValuation.toValuation (inducedOrder i)).mem_maximalIdeal_iff
  rw [hideal]
  change (i x).coeff 0 = 0 ↔ 0 < (i x).orderTop
  have hx : 0 ≤ (i x).orderTop := x.property
  refine ⟨fun h => lt_of_le_of_ne hx (fun he => ?_), HahnSeries.coeff_eq_zero_of_lt_orderTop⟩
  exact HahnSeries.coeff_orderTop_ne (by simpa using he.symm) h

/-- The map from the actual residue quotient obtained by taking constant coefficients. -/
def residueEmbedding {L : Type*} [Field L] (i : L →+* LaurentSeries ℓ) :
    residueField i →+* ℓ :=
  Ideal.Quotient.lift (positiveIdeal i) (reduction i)
    (fun x hx => (reduction_eq_zero_iff i x).2 hx)

section Embeddings

variable [Algebra k ℓ] (a : k) (L : Type*) [Field L] [Algebra (RatFunc k) L]

/-- Field embeddings over the `k(t)`-algebra structure defined by the point. -/
abbrev PointEmbedding : Type _ :=
  letI := substitutionAlgebra ℓ a
  L →ₐ[RatFunc k] LaurentSeries ℓ

variable {a L}

/-- Forget the scalar structure of the point embedding. -/
abbrev PointEmbedding.toRingHom (i : PointEmbedding (ℓ := ℓ) a L) :
    L →+* LaurentSeries ℓ :=
  letI := substitutionAlgebra ℓ a
  AlgHom.toRingHom i

/-- The decomposition subgroup of the order induced by the given embedding. -/
def decompositionGroup (i : PointEmbedding (ℓ := ℓ) a L) : Subgroup (L ≃ₐ[RatFunc k] L) where
  carrier := {σ | ∀ x : L, x ≠ 0 →
    inducedOrder i.toRingHom (σ x) = inducedOrder i.toRingHom x}
  one_mem' := by intro x hx; rfl
  mul_mem' {σ τ} hσ hτ := by
    intro x hx
    change inducedOrder i.toRingHom (σ (τ x)) = inducedOrder i.toRingHom x
    rw [hσ (τ x) ((map_ne_zero τ).mpr hx), hτ x hx]
  inv_mem' {σ} hσ := by
    intro x hx
    change inducedOrder i.toRingHom (σ.symm x) = inducedOrder i.toRingHom x
    simpa using (hσ (σ.symm x) ((map_ne_zero σ.symm).mpr hx)).symm

/-- All generic roots are power series under the embedding, and their constant coefficients
give a bijection with the distinct roots of the fibre polynomial. -/
def MatchesRoots (i : PointEmbedding (ℓ := ℓ) a L) (f : (RatFunc k)[X])
    (hf : PolynomialRegularAt a f) : Prop :=
  (∀ x ∈ f.rootSet L, ∃ F : PowerSeries ℓ, powerToLaurent ℓ F = i x) ∧
    Set.BijOn (fun x : L => (i x).coeff 0) (f.rootSet L) ((specialize a f hf).rootSet ℓ)

end Embeddings

section ExpectedTypes

set_option linter.checkUnivs false

universe uk uℓ uL

def RegularAtType := ∀ {k : Type uk} [Field k], k → RatFunc k → Prop

def PolynomialRegularAtType := ∀ {k : Type uk} [Field k], k → (RatFunc k)[X] → Prop

def RegularCoefficientsType := ∀ {k : Type uk} [Field k], k → Subring (RatFunc k)

def EvalRegularType := ∀ {k : Type uk} [Field k] (a : k), regularCoefficients a →+* k

def RegularPolynomialType := ∀ {k : Type uk} [Field k] (a : k) (f : (RatFunc k)[X]),
  PolynomialRegularAt a f → (regularCoefficients a)[X]

def SpecializeType := ∀ {k : Type uk} [Field k] (a : k) (f : (RatFunc k)[X]),
  PolynomialRegularAt a f → k[X]

def UniformizerType := ∀ (ℓ : Type uℓ) [Field ℓ], LaurentSeries ℓ

def PowerToLaurentType := ∀ (ℓ : Type uℓ) [Field ℓ], PowerSeries ℓ →+* LaurentSeries ℓ

def PolynomialSeriesType := ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ],
  k → k[X] →ₐ[k] PowerSeries ℓ

def PolynomialLaurentType := ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ],
  k → k[X] →ₐ[k] LaurentSeries ℓ

def SubstitutionType := ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ],
  k → RatFunc k →ₐ[k] LaurentSeries ℓ

def SubstitutionAlgebraType := ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ],
  k → Algebra (RatFunc k) (LaurentSeries ℓ)

def SeriesOrderType := ∀ (ℓ : Type uℓ) [Field ℓ], LaurentSeries ℓ → WithTop ℤ

def InducedOrderType := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L],
  (L →+* LaurentSeries ℓ) → AddValuation L (WithTop ℤ)

def ValuationRingType := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L],
  (L →+* LaurentSeries ℓ) → ValuationSubring L

def PositiveIdealType := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ), Ideal (valuationRing i)

def ResidueFieldType := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L],
  (L →+* LaurentSeries ℓ) → Type uL

def IntegralSeriesType := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ), valuationRing i →+* PowerSeries ℓ

def ReductionType := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ), valuationRing i →+* ℓ

def ResidueEmbeddingType := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ), residueField i →+* ℓ

def PointEmbeddingType := ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
  (_a : k) (L : Type uL) [Field L] [Algebra (RatFunc k) L], Type (max uL uℓ)

def PointEmbeddingToRingHomType := ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ]
  [Algebra k ℓ] {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L],
  PointEmbedding (ℓ := ℓ) a L → (L →+* LaurentSeries ℓ)

def DecompositionGroupType := ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
  {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L],
  PointEmbedding (ℓ := ℓ) a L → Subgroup (L ≃ₐ[RatFunc k] L)

def MatchesRootsType := ∀ {k : Type uk} [Field k] {ℓ : Type uℓ} [Field ℓ] [Algebra k ℓ]
  {a : k} {L : Type uL} [Field L] [Algebra (RatFunc k) L],
  PointEmbedding (ℓ := ℓ) a L → ∀ f : (RatFunc k)[X], PolynomialRegularAt a f → Prop

abbrev PowerToLaurentX : Prop := ∀ (ℓ : Type uℓ) [Field ℓ],
  powerToLaurent ℓ PowerSeries.X = uniformizer ℓ

abbrev SpecializeCoeff : Prop := ∀ {k : Type uk} [Field k] (a : k) (f : (RatFunc k)[X])
  (hf : PolynomialRegularAt a f) (n : ℕ),
  (specialize a f hf).coeff n = RatFunc.eval (RingHom.id k) a (f.coeff n)

abbrev ValuationRingMembership : Prop := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ) (x : L), x ∈ valuationRing i ↔ 0 ≤ seriesOrder ℓ (i x)

abbrev NonnegativeIffPowerSeries : Prop := ∀ {ℓ : Type uℓ} [Field ℓ] (x : LaurentSeries ℓ),
  0 ≤ seriesOrder ℓ x ↔ ∃ F : PowerSeries ℓ, powerToLaurent ℓ F = x

abbrev PowerToLaurentIntegralSeries : Prop := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ) (x : valuationRing i), powerToLaurent ℓ (integralSeries i x) = i x

abbrev PositiveIdealMembership : Prop := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ) (x : valuationRing i),
  x ∈ positiveIdeal i ↔ 0 < seriesOrder ℓ (i x)

abbrev ReductionApply : Prop := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ) (x : valuationRing i), reduction i x = (i x).coeff 0

abbrev ResidueEmbeddingApply : Prop := ∀ {ℓ : Type uℓ} [Field ℓ] {L : Type uL} [Field L]
  (i : L →+* LaurentSeries ℓ) (x : valuationRing i),
  residueEmbedding i (IsLocalRing.residue (valuationRing i) x) = (i x).coeff 0

end ExpectedTypes

end

end Specs.GaloisFormalization.IG.SpecializationData
