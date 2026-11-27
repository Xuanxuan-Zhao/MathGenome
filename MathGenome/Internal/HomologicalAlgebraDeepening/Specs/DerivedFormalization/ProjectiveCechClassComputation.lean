import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.LaurentCechCohomology

noncomputable section

open CategoryTheory CategoryTheory.Limits
open DerivedFormalization.ProjectiveTwists (Index Polynomials ChartLocalization)
open DerivedFormalization.LaurentCechCohomology

namespace Specs.DerivedFormalization.ProjectiveCechClassComputation

universe u v

/-- The cohomology identifications and their representatives under a comparison of
cycles, homology classes, and chart values with the ordered Laurent complex. -/
def transportedCechClassesType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n → ∀ (m : ℤ)
    (sq : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0),
    let K := orderedComplex k n m sq
    ∀ (e : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p),
      (∀ (p : ℤ) (x : Term k n m p) (J : Faces n p) (a : Exponents n m),
        (chartToLaurent k n J.val (e p x J).val).coeff a.val = (x a).val J.val) →
      ∀ (C : CochainComplex (ModuleCat.{u} k) ℕ) (H : ℕ → ModuleCat.{u} k)
        (δ : ∀ q : ℕ, C.homology q ≅ H q)
        (β : ∀ q : ℕ, K.homology (q : ℤ) ≅ C.homology q)
        (g : ∀ q : ℕ, K.cycles (q : ℤ) ⟶ C.cycles q),
        (∀ (q : ℕ) (z : K.cycles (q : ℤ)),
          (β q).hom (K.homologyπ (q : ℤ) z) = C.homologyπ q (g q z)) →
        ∀ (I : ℕ → Type v) (V : ∀ q : ℕ, I q → Finset (Index n))
          (hV : ∀ q t, (V q t).Nonempty) (hcard : ∀ q t, (V q t).card = q + 1),
          let face (q : ℕ) (t : I q) : Faces n (q : ℤ) :=
            ⟨V q t, by exact_mod_cast hcard q t, hV q t⟩
          ∀ (ρ : ∀ (q : ℕ) (_ : C.cycles q) (t : I q), ChartLocalization k n (V q t)),
            (∀ (q : ℕ) (z : K.cycles (q : ℤ)) (t : I q),
              chartToLaurent k n (V q t) (ρ q (g q z) t) =
                chartToLaurent k n (V q t)
                  (e (q : ℤ) (show Term k n m (q : ℤ) from K.iCycles (q : ℤ) z)
                    (face q t)).val) →
            (∃ E : polynomialDegree k n m ≃ₗ[k] H 0,
              ∀ f, ∃ z : C.cycles 0,
                (δ 0).hom (C.homologyπ 0 z) = E f ∧
                ∀ t : I 0, ρ 0 z t =
                  algebraMap (Polynomials k n) (ChartLocalization k n (V 0 t)) f.val) ∧
            (∃ E : (TopExponents n m →₀ k) ≃ₗ[k] H n,
              ∀ f, ∃ z : C.cycles n,
                (δ n).hom (C.homologyπ n z) = E f ∧
                ∀ t : I n, chartToLaurent k n (V n t) (ρ n z t) =
                  AddMonoidAlgebra.ofCoeff
                    (Finsupp.mapDomain (fun a : TopExponents n m ↦ a.val.val) f)) ∧
            (∀ q : ℕ, 0 < q → q ≠ n → IsZero (H q)) ∧
            (m < 0 → polynomialDegree k n m = ⊥ ∧ IsZero (H 0)) ∧
            (IsEmpty (TopExponents n m) → IsZero (H n))

end Specs.DerivedFormalization.ProjectiveCechClassComputation
