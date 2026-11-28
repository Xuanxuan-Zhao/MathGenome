import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

open scoped PowerSeries.WithPiTopology TensorProduct

namespace LieNotes.BialgebraDeformation

open PowerSeries

noncomputable section

abbrev PlaneTensorZero (k : Type*) := k

/-- The coefficient algebra of the deformation. -/
abbrev Plane (k : Type*) [CommSemiring k] := MvPolynomial (Fin 2) k

abbrev PlaneTensorSquare (k : Type*) [CommSemiring k] := Plane k ⊗[k] Plane k

abbrev PlaneTensorCube (k : Type*) [CommSemiring k] := PlaneTensorSquare k ⊗[k] Plane k

abbrev PlaneTensorCubeRight (k : Type*) [CommSemiring k] := Plane k ⊗[k] PlaneTensorSquare k

-- Use the standard tensor semiring operations in both bracketings. Giving Lean the
-- coefficient instance directly keeps formal scalar inference from rebuilding the nested
-- tensor module structure inside the power-series instance search.
instance (k : Type*) [CommSemiring k] : CommSemiring (PlaneTensorCube k) :=
  Algebra.TensorProduct.instCommSemiring (R := k) (A := PlaneTensorSquare k) (B := Plane k)

instance (k : Type*) [CommSemiring k] : CommSemiring (PlaneTensorCubeRight k) :=
  Algebra.TensorProduct.instCommSemiring (R := k) (A := Plane k) (B := PlaneTensorSquare k)

/-- The coefficientwise topology with discrete coefficients. -/
abbrev seriesTopology (A : Type*) : TopologicalSpace (PowerSeries A) :=
  letI : TopologicalSpace A := ⊥
  inferInstance

def SeriesContinuous {A B : Type*} (f : PowerSeries A → PowerSeries B) : Prop :=
  @Continuous _ _ (seriesTopology A) (seriesTopology B) f

def seriesConstants (k A : Type*) [CommSemiring k] [CommSemiring A] [Algebra k A] :
    A →ₐ[k] PowerSeries A where
  __ := PowerSeries.C
  commutes' _ := PowerSeries.algebraMap_apply.symm

/-- Extension of the coefficient map, including its normalization on the formal variable. -/
def ExtendsSeriesMap {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (a : A →ₐ[k] PowerSeries B)
    (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B) : Prop :=
  SeriesContinuous F ∧ F PowerSeries.X = PowerSeries.X ∧
    ∀ x, F (PowerSeries.C x) = a x

def SeriesExtensionSpec : Prop :=
  ∀ {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (a : A →ₐ[k] PowerSeries B),
    ∃ F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B,
      ExtendsSeriesMap a F ∧
      (∀ G, ExtendsSeriesMap a G → G = F) ∧
      ∀ (p : PowerSeries A) (n : ℕ),
        PowerSeries.coeff n (F p) =
          ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff (n - j) (a (PowerSeries.coeff j p))

section Algebra

variable {k A B D E : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing D] [CommRing E]
variable [Algebra k A] [Algebra k B] [Algebra k D] [Algebra k E]

/-- Apply a coefficient homomorphism term by term over the formal scalar ring. -/
def seriesMap (f : A →ₐ[k] B) : PowerSeries A →ₐ[PowerSeries k] PowerSeries B where
  toRingHom := PowerSeries.map f.toRingHom
  commutes' p := by
    change PowerSeries.map f.toRingHom (PowerSeries.map (algebraMap k A) p) =
      PowerSeries.map (algebraMap k B) p
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map]
    exact f.commutes (coeff n p)

theorem scalarSeries_C (x : k) :
    algebraMap (PowerSeries k) (PowerSeries A) (C x) = algebraMap k (PowerSeries A) x := by
  rw [PowerSeries.algebraMap_apply'', PowerSeries.map_C, PowerSeries.algebraMap_apply]

/-- Regard a homomorphism of formal scalar algebras as a homomorphism over the ground ring. -/
def restrictSeriesMap (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B) :
    PowerSeries A →ₐ[k] PowerSeries B where
  toRingHom := F.toRingHom
  commutes' x := by
    change F (algebraMap k (PowerSeries A) x) = algebraMap k (PowerSeries B) x
    simpa only [scalarSeries_C] using F.commutes (C x)

/-- Apply an extended map to the series values of a coefficient map. -/
def composeSeriesCoefficient (F : PowerSeries B →ₐ[PowerSeries k] PowerSeries D)
    (a : A →ₐ[k] PowerSeries B) : A →ₐ[k] PowerSeries D :=
  (restrictSeriesMap F).comp a

/-- The coefficient map for tensoring two maps that take their values in series. -/
def tensorSeriesCoefficient (a : A →ₐ[k] PowerSeries D) (b : B →ₐ[k] PowerSeries E) :
    A ⊗[k] B →ₐ[k] PowerSeries (D ⊗[k] E) :=
  Algebra.TensorProduct.productMap
    ((PowerSeries.mapAlgHom Algebra.TensorProduct.includeLeft).comp a)
    ((PowerSeries.mapAlgHom Algebra.TensorProduct.includeRight).comp b)

/-- The canonical image of a pair of power series in series on the ordinary tensor product. -/
def seriesTensorPair (p : PowerSeries A) (q : PowerSeries B) : PowerSeries (A ⊗[k] B) :=
  seriesMap (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B) p *
    seriesMap (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B) q

/-- The algebraic tensor product maps to series on the ordinary tensor product. -/
def seriesTensorComparison :
    PowerSeries A ⊗[PowerSeries k] PowerSeries B →ₐ[PowerSeries k] PowerSeries (A ⊗[k] B) :=
  Algebra.TensorProduct.productMap
    (seriesMap (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B))
    (seriesMap (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B))

end Algebra

def SeriesCompositionSpec : Prop :=
  ∀ {k A B D : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing D]
    [Algebra k A] [Algebra k B] [Algebra k D]
    (a : A →ₐ[k] PowerSeries B) (b : B →ₐ[k] PowerSeries D)
    (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B)
    (G : PowerSeries B →ₐ[PowerSeries k] PowerSeries D),
    ExtendsSeriesMap a F → ExtendsSeriesMap b G →
    ExtendsSeriesMap (composeSeriesCoefficient G a) (G.comp F)

def SeriesCoefficientMapSpec : Prop :=
  ∀ {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B),
    ExtendsSeriesMap ((seriesConstants k B).comp f) (seriesMap f) ∧
      ∀ p n, coeff n (seriesMap f p) = f (coeff n p)

def SeriesPolynomialExtSpec : Prop :=
  ∀ {k D : Type*} {ι : Type*} [CommRing k] [CommRing D] [Algebra k D]
    (F G : PowerSeries (MvPolynomial ι k) →ₐ[PowerSeries k] PowerSeries D),
    SeriesContinuous F → SeriesContinuous G →
    (∀ i, F (C (MvPolynomial.X i)) = G (C (MvPolynomial.X i))) → F = G

def SeriesTensorExtSpec : Prop :=
  ∀ {k A B D : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing D]
    [Algebra k A] [Algebra k B] [Algebra k D]
    (F G : PowerSeries (A ⊗[k] B) →ₐ[PowerSeries k] PowerSeries D),
    SeriesContinuous F → SeriesContinuous G →
    (∀ x : A, F (C (x ⊗ₜ[k] (1 : B))) = G (C (x ⊗ₜ[k] (1 : B)))) →
    (∀ y : B, F (C ((1 : A) ⊗ₜ[k] y)) = G (C ((1 : A) ⊗ₜ[k] y))) → F = G

/-- Tensoring the completed maps is induced by tensoring their restrictions to constants.
The pairing is taken over the formal scalar ring, with the two series multiplied in the
appropriate completed target. The statement applies to further tensor legs by iteration. -/
def SeriesTensorMapsSpec : Prop :=
  ∀ {k A B D E : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing D] [CommRing E]
    [Algebra k A] [Algebra k B] [Algebra k D] [Algebra k E]
    (a : A →ₐ[k] PowerSeries D) (b : B →ₐ[k] PowerSeries E)
    (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries D)
    (G : PowerSeries B →ₐ[PowerSeries k] PowerSeries E)
    (H : PowerSeries (A ⊗[k] B) →ₐ[PowerSeries k] PowerSeries (D ⊗[k] E)),
    ExtendsSeriesMap a F → ExtendsSeriesMap b G → ExtendsSeriesMap (tensorSeriesCoefficient a b) H →
    ∀ p q, H (seriesTensorPair (k := k) p q) = seriesTensorPair (k := k) (F p) (G q)

/-- The ordinary tensor associator takes the left-associated pairing to the
right-associated pairing in the completions. -/
def SeriesTensorAssociativitySpec : Prop :=
  ∀ {k A B D : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing D]
    [Algebra k A] [Algebra k B] [Algebra k D]
    (p : PowerSeries A) (q : PowerSeries B) (r : PowerSeries D),
    seriesMap (Algebra.TensorProduct.assoc k k k A B D).toAlgHom
        (seriesTensorPair (k := k) (seriesTensorPair (k := k) p q) r) =
      seriesTensorPair (k := k) p (seriesTensorPair (k := k) q r)

/-- The ideal of the formal variable in the coefficient algebra's power series ring. -/
def seriesVariableIdeal (A : Type*) [CommRing A] : Ideal (PowerSeries A) :=
  Ideal.span {X}

def polynomialVariableIdeal (A : Type*) [CommRing A] : Ideal (Polynomial A) :=
  Ideal.span {Polynomial.X}

def SeriesAdicTopologySpec : Prop :=
  ∀ (A : Type*) [CommRing A],
    @IsAdic (PowerSeries A) _ (seriesTopology A) (seriesVariableIdeal A) ∧
    IsAdicComplete (seriesVariableIdeal A) (PowerSeries A)

/-- The identification of the inverse limit of polynomial truncations with power series is
canonical on polynomials. -/
def PolynomialCompletionSpec : Prop :=
  ∀ (A : Type*) [CommRing A],
    ∃ e : PowerSeries A ≃+* AdicCompletion (polynomialVariableIdeal A) (Polynomial A),
      ∀ p : Polynomial A, e (p : PowerSeries A) =
        AdicCompletion.of (polynomialVariableIdeal A) (Polynomial A) p

section TensorCompletion

variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The parameter ideal on the algebraic tensor product over the formal scalar ring. -/
def tensorVariableIdeal : Ideal (PowerSeries A ⊗[PowerSeries k] PowerSeries B) :=
  Ideal.span {algebraMap (PowerSeries k) (PowerSeries A ⊗[PowerSeries k] PowerSeries B) X}

end TensorCompletion

/-- At each finite level the comparison of the two tensor products is induced by the
coefficientwise inclusions. This compares the actual algebraic tensor product over k[[t]]
modulo the parameter with the prescribed finite truncation. -/
def TensorTruncationSpec : Prop :=
  ∀ (k A B : Type*) [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (n : ℕ),
    ∃ e : ((PowerSeries A ⊗[PowerSeries k] PowerSeries B) ⧸ tensorVariableIdeal k A B ^ n)
        ≃ₐ[PowerSeries k]
        (PowerSeries (A ⊗[k] B) ⧸ seriesVariableIdeal (A ⊗[k] B) ^ n),
      ∀ p : PowerSeries A ⊗[PowerSeries k] PowerSeries B,
        e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (seriesTensorComparison p)

/-- The completion of the algebraic tensor product over k[[t]] has the prescribed canonical
model. Iteration gives the square and either bracketing of the cube. -/
def TensorCompletionSpec : Prop :=
  ∀ (k A B : Type*) [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B],
    ∃ e : AdicCompletion (tensorVariableIdeal k A B)
        (PowerSeries A ⊗[PowerSeries k] PowerSeries B) ≃ₐ[PowerSeries k] PowerSeries (A ⊗[k] B),
      ∀ p : PowerSeries A ⊗[PowerSeries k] PowerSeries B,
        e (AdicCompletion.of (tensorVariableIdeal k A B) _ p) = seriesTensorComparison p

end

end LieNotes.BialgebraDeformation
