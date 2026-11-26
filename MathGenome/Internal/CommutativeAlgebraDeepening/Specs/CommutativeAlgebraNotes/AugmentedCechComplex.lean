import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.RingTheory.Flat.Localization

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Specs.CommutativeAlgebraNotes.AugmentedCechComplex

universe u

variable (R : Type u) [CommRing R]

abbrev Complex := CochainComplex (ModuleCat.{u} R) ℤ

/-- A single Čech factor with its localization map in degrees zero and one. -/
@[reducible] noncomputable def factor (r : R) : Complex R where
  X i := if i = 0 then ModuleCat.of R R else
    if i = 1 then ModuleCat.of R (Localization.Away r) else ModuleCat.of R PUnit
  d i j := if hi : i = 0 then if hj : j = 1 then
    eqToHom (by simp [hi]) ≫ ModuleCat.ofHom (Algebra.linearMap R (Localization.Away r)) ≫
      eqToHom (by simp [hj]) else 0 else 0
  shape i j hij := by
    by_cases hi : i = 0 <;> by_cases hj : j = 1
    · exact (hij (by subst i; subst j; rfl)).elim
    all_goals simp [hi, hj]
  d_comp_d' i j k _ _ := by
    by_cases hi : i = 0 <;> by_cases hj : j = 1
    · simp [hi, hj]
    all_goals simp [hi, hj]

/-- The ordered tensor product of the two-term localization complexes. -/
@[reducible] noncomputable def complex : List R → Complex R
  | [] => HomologicalComplex.tensorUnit (ModuleCat R) (.up ℤ)
  | r :: rs => HomologicalComplex.tensorObj (factor R r) (complex rs)

/-- Tensoring on the left by the augmented Čech complex. -/
noncomputable def tensorFunctor (rs : List R) : Complex R ⥤ Complex R :=
  ((curriedTensor (ModuleCat R)).map₂CochainComplex).obj (complex R rs)

/-- The Čech complex with coefficients in a module placed in degree zero. -/
noncomputable def coefficients (rs : List R) (M : ModuleCat.{u} R) : Complex R :=
  (tensorFunctor R rs).obj ((HomologicalComplex.single (ModuleCat R) (.up ℤ) 0).obj M)

/-- The degree selected in a single factor. -/
@[reducible] def headDegree : Bool → ℤ
  | false => 0
  | true => 1

/-- Subsets of the ordered positions, encoded by membership bits whose sum is q. -/
@[reducible] def Selection : ℕ → ℤ → Type
  | 0, q => PLift (q = 0)
  | n + 1, q => Σ b : Bool, Selection n (q - headDegree b)

/-- The product of the elements at the selected positions. -/
@[reducible] def product : (rs : List R) → {q : ℤ} → Selection rs.length q → R
  | [], _, _ => 1
  | _ :: rs, _, ⟨false, s⟩ => product rs s
  | r :: rs, _, ⟨true, s⟩ => r * product rs s

/-- A summand in the complex with ring coefficients. -/
abbrev term (rs : List R) {q : ℤ} (s : Selection rs.length q) : ModuleCat.{u} R :=
  ModuleCat.of R (Localization.Away (product R rs s))

/-- A summand in the complex with module coefficients. -/
abbrev moduleTerm (rs : List R) (M : ModuleCat.{u} R) {q : ℤ} (s : Selection rs.length q) :
    ModuleCat.{u} R :=
  ModuleCat.of R (LocalizedModule.Away (product R rs s) M)

/-- The membership function of the selected positions. -/
def selected : {n : ℕ} → {q : ℤ} → Selection n q → Fin n → Bool
  | 0, _, _, a => Fin.elim0 a
  | _ + 1, _, s, a => Fin.cases s.1 (fun i => selected s.2 i) a

/-- The number of occupied positions preceding an index. -/
def preceding : {n : ℕ} → {q : ℤ} → Selection n q → Fin n → ℤ
  | 0, _, _, a => Fin.elim0 a
  | _ + 1, _, s, a => Fin.cases 0 (fun i => headDegree s.1 + preceding s.2 i) a

/-- The canonical map of principal localizations when the denominator divides the new one. -/
noncomputable def localizationMap (p q : R) (h : p ∣ q) :
    Localization.Away p →ₐ[R] Localization.Away q :=
  IsLocalization.Away.liftAlgHom p (f := Algebra.ofId R (Localization.Away q))
    (IsLocalization.Away.isUnit_of_dvd q h)

abbrev ComplexType := ∀ {R : Type u} [CommRing R], List R → Complex R
noncomputable def complexValue : ComplexType.{u} := @complex

abbrev TensorFunctorType := ∀ {R : Type u} [CommRing R], List R → (Complex R ⥤ Complex R)
noncomputable def tensorFunctorValue : TensorFunctorType.{u} := @tensorFunctor

abbrev CoefficientsType := ∀ {R : Type u} [CommRing R], List R → ModuleCat.{u} R → Complex R
noncomputable def coefficientsValue : CoefficientsType.{u} := @coefficients

/-- The terms are flat, including in the empty-list case. -/
def FlatTerms : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R) (k : ℤ), Module.Flat R ((complex R rs).X k)

/-- Only degrees from zero through the length of the list can be nonzero. -/
def BoundedSupport : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R) (k : ℤ),
    k < 0 ∨ (rs.length : ℤ) < k → IsZero ((complex R rs).X k)

/-- The direct-sum terms and the signed localization maps of the augmented Čech complex. -/
def RingTermFormula : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R),
    ∃ ι : ∀ (k : ℤ) (s : Selection rs.length k), term R rs s ⟶ (complex R rs).X k,
      (∀ k, Nonempty (IsColimit (Cofan.mk ((complex R rs).X k) (ι k)))) ∧
      (∀ k, ∃ e : Selection rs.length k ≃ {J : Finset (Fin rs.length) // (J.card : ℤ) = k},
        ∀ s, (e s).val = Finset.univ.filter fun a => selected s a = true) ∧
      (∀ k (s : Selection rs.length k),
        product R rs s = ∏ a ∈ Finset.univ.filter (fun a => selected s a = true), rs.get a) ∧
      ∀ k (s : Selection rs.length k),
        ∃ δ : Fin rs.length → (term R rs s ⟶ (complex R rs).X (k + 1)),
          ι k s ≫ (complex R rs).d k (k + 1) =
            ∑ a : Fin rs.length,
              ((Finset.univ.filter fun j => selected s j = true ∧ j < a).card : ℤ).negOnePow • δ a ∧
          (∀ a, selected s a = true → δ a = 0) ∧
          ∀ a, selected s a = false →
            ∃ (t : Selection rs.length (k + 1)) (h : product R rs s ∣ product R rs t),
              (∀ j, selected t j = (decide (j = a) || selected s j)) ∧
              product R rs t = rs.get a * product R rs s ∧
              δ a = ModuleCat.ofHom (localizationMap R (product R rs s) (product R rs t) h).toLinearMap ≫
                ι (k + 1) t

/-- With module coefficients the summands are the corresponding localizations of the module. -/
def ModuleTermFormula : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R) (M : ModuleCat.{u} R) (k : ℤ),
    Nonempty ((coefficients R rs M).X k ≅
      ∐ (fun s : Selection rs.length k => moduleTerm R rs M s))

/-- With ring coefficients, the degree-zero term is a copy of the base ring. -/
def DegreeZeroTerm : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R), Nonempty ((complex R rs).X 0 ≅ ModuleCat.of R R)

end Specs.CommutativeAlgebraNotes.AugmentedCechComplex
