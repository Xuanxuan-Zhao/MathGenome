import MathGenome.Internal.MultivariableAnalysis.D04.C02.ContinuousPartials
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.CrCalculus
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

noncomputable section
open Set
open scoped ContDiff BigOperators
namespace D04

def iteratedPartial : Specs.D04.C02.CrCalculus.iteratedPartialType :=
  @Specs.D04.C02.CrCalculus.iteratedPartialValue

def HasContinuousOrderedPartials : Specs.D04.C02.CrCalculus.HasContinuousOrderedPartialsType :=
  @Specs.D04.C02.CrCalculus.HasContinuousOrderedPartialsValue

section Generic
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem crOn_sum (r : ℕ) {ι : Type} (s : Finset ι) (U : Set X) (f : ι → X → Y)
    (hU : IsOpen U) (hf : ∀ i ∈ s, CrOn r U (f i)) :
    CrOn r U (fun x => ∑ i ∈ s, f i x) := by
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  exact ContDiffOn.sum fun i hi => (crOn_iff_contDiffOn r U _ hU).mp (hf i hi)

theorem crOn_const_smul (r : ℕ) (U : Set X) (f : X → Y) (c : ℝ)
    (hU : IsOpen U) (hf : CrOn r U f) : CrOn r U (fun x => c • f x) := by
  exact (crOn_iff_contDiffOn r U _ hU).mpr
    (((crOn_iff_contDiffOn r U _ hU).mp hf).const_smul c)

theorem crOn_comp (r : ℕ) (U : Set X) (V : Set Y) (f : X → Y) (g : Y → Z)
    (hU : IsOpen U) (hV : IsOpen V) (hmap : MapsTo f U V)
    (hf : CrOn r U f) (hg : CrOn r V g) : CrOn r U (g ∘ f) := by
  exact (crOn_iff_contDiffOn r U _ hU).mpr
    (((crOn_iff_contDiffOn r V _ hV).mp hg).comp
      ((crOn_iff_contDiffOn r U _ hU).mp hf) hmap)

theorem crOn_reciprocal (r : ℕ) (U : Set X) (q : X → ℝ)
    (hU : IsOpen U) (hq : CrOn r U q) (hne : ∀ x ∈ U, q x ≠ 0) :
    CrOn r U (fun x => (q x)⁻¹) := by
  exact (crOn_iff_contDiffOn r U _ hU).mpr
    (((crOn_iff_contDiffOn r U _ hU).mp hq).inv hne)

theorem crOn_quotient (r : ℕ) (U : Set X) (f : X → Y) (q : X → ℝ)
    (hU : IsOpen U) (hf : CrOn r U f) (hq : CrOn r U q) (hne : ∀ x ∈ U, q x ≠ 0) :
    CrOn r U (fun x => (q x)⁻¹ • f x) := by
  exact (crOn_iff_contDiffOn r U _ hU).mpr
    ((((crOn_iff_contDiffOn r U _ hU).mp hq).inv hne).smul
      ((crOn_iff_contDiffOn r U _ hU).mp hf))

theorem smoothOn_sum {ι : Type} (s : Finset ι) (U : Set X) (f : ι → X → Y)
    (hU : IsOpen U) (hf : ∀ i ∈ s, SmoothOn U (f i)) :
    SmoothOn U (fun x => ∑ i ∈ s, f i x) := by
  change ∀ r : ℕ, CrOn r U _
  intro r
  exact crOn_sum r s U f hU (fun i hi => hf i hi r)

theorem smoothOn_const_smul (U : Set X) (f : X → Y) (c : ℝ)
    (hU : IsOpen U) (hf : SmoothOn U f) : SmoothOn U (fun x => c • f x) := by
  change ∀ r : ℕ, CrOn r U _
  intro r
  exact crOn_const_smul r U f c hU (hf r)

theorem smoothOn_comp (U : Set X) (V : Set Y) (f : X → Y) (g : Y → Z)
    (hU : IsOpen U) (hV : IsOpen V) (hmap : MapsTo f U V)
    (hf : SmoothOn U f) (hg : SmoothOn V g) : SmoothOn U (g ∘ f) := by
  change ∀ r : ℕ, CrOn r U _
  intro r
  exact crOn_comp r U V f g hU hV hmap (hf r) (hg r)

theorem smoothOn_reciprocal (U : Set X) (q : X → ℝ)
    (hU : IsOpen U) (hq : SmoothOn U q) (hne : ∀ x ∈ U, q x ≠ 0) :
    SmoothOn U (fun x => (q x)⁻¹) := by
  change ∀ r : ℕ, CrOn r U _
  intro r
  exact crOn_reciprocal r U q hU (hq r) hne

theorem smoothOn_quotient (U : Set X) (f : X → Y) (q : X → ℝ)
    (hU : IsOpen U) (hf : SmoothOn U f) (hq : SmoothOn U q)
    (hne : ∀ x ∈ U, q x ≠ 0) : SmoothOn U (fun x => (q x)⁻¹ • f x) := by
  change ∀ r : ℕ, CrOn r U _
  intro r
  exact crOn_quotient r U f q hU (hf r) (hq r) hne

end Generic

@[simp] theorem iteratedPartial_nil {n m : ℕ} (f : E n → E m) :
    iteratedPartial f [] = f := rfl

@[simp] theorem iteratedPartial_cons {n m : ℕ} (f : E n → E m)
    (j : Fin n) (js : List (Fin n)) :
    iteratedPartial f (j :: js) = iteratedPartial (fun x => partialDerivative f x j) js := rfl

theorem hasContinuousOrderedPartials_zero {n m : ℕ} (U : Set (E n)) (f : E n → E m) :
    HasContinuousOrderedPartials 0 U f ↔ ContinuousOn f U := by
  change ((∀ js : List (Fin n), js.length ≤ 0 → ContinuousOn (iteratedPartial f js) U) ∧
    (∀ js : List (Fin n), js.length < 0 → ∀ x ∈ U, ∀ j : Fin n,
      ∃ d, HasPartialDerivative (iteratedPartial f js) x j d)) ↔ _
  constructor
  · intro h
    exact h.1 [] (by simp)
  · intro h
    refine ⟨?_, fun js hjs => (Nat.not_lt_zero _ hjs).elim⟩
    intro js hjs
    have he : js = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hjs)
    simpa only [he, iteratedPartial_nil] using h

theorem hasContinuousOrderedPartials_succ {n m : ℕ} (r : ℕ)
    (U : Set (E n)) (f : E n → E m) :
    HasContinuousOrderedPartials (r + 1) U f ↔
      ContinuousOn f U ∧
      (∀ x ∈ U, ∀ j : Fin n, ∃ d, HasPartialDerivative f x j d) ∧
      (∀ j : Fin n, HasContinuousOrderedPartials r U (fun x => partialDerivative f x j)) := by
  change ((∀ js : List (Fin n), js.length ≤ r + 1 → ContinuousOn (iteratedPartial f js) U) ∧
    (∀ js : List (Fin n), js.length < r + 1 → ∀ x ∈ U, ∀ j : Fin n,
      ∃ d, HasPartialDerivative (iteratedPartial f js) x j d)) ↔ _
  constructor
  · intro h
    refine ⟨h.1 [] (by simp), h.2 [] (by simp), ?_⟩
    intro j
    change (∀ js : List (Fin n), js.length ≤ r → ContinuousOn (iteratedPartial _ js) U) ∧
      (∀ js : List (Fin n), js.length < r → ∀ x ∈ U, ∀ i : Fin n,
        ∃ d, HasPartialDerivative (iteratedPartial _ js) x i d)
    exact ⟨fun js hjs => h.1 (j :: js) (by simpa using Nat.succ_le_succ hjs),
      fun js hjs => h.2 (j :: js) (by simpa using Nat.succ_lt_succ hjs)⟩
  · rintro ⟨hc, hd, hp⟩
    constructor
    · intro js hjs
      cases js with
      | nil => exact hc
      | cons j js =>
        exact (hp j).1 js (by simpa using hjs)
    · intro js hjs
      cases js with
      | nil => exact hd
      | cons j js =>
        exact (hp j).2 js (by simpa using hjs)

/-- Operator regularity can be checked on the fixed coordinate basis; the
reverse implication uses only the finite linear expansion, not symmetry. -/
theorem contDiffOn_clm_iff_basis {n m : ℕ} (r : ℕ) (U : Set (E n))
    (A : E n → E n →L[ℝ] E m) :
    ContDiffOn ℝ (r : ℕ∞ω) A U ↔
      ∀ j : Fin n, ContDiffOn ℝ (r : ℕ∞ω) (fun x => A x (standardBasis n j)) U := by
  constructor
  · intro h j
    exact h.clm_apply contDiffOn_const
  · intro h
    apply contDiffOn_clm_apply.mpr
    intro v
    have hv : v = ∑ j : Fin n, v j • standardBasis n j := by
      simpa [standardBasis, EuclideanSpace.basisFun_repr] using
        ((standardBasis n).sum_repr v).symm
    have hexp (x : E n) : A x v = ∑ j : Fin n, v j • A x (standardBasis n j) := by
      conv_lhs => rw [hv]
      simp
    simpa only [← hexp] using
      (ContDiffOn.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => (h j).const_smul (v j)))

/-- This successor criterion stays in the original Euclidean target, allowing
induction without assuming commutation of the coordinate derivatives. -/
theorem crOn_succ_iff_partials {n m : ℕ} (r : ℕ) (U : Set (E n))
    (f : E n → E m) (hU : IsOpen U) :
    CrOn (r + 1) U f ↔
      (∀ x ∈ U, ∀ j : Fin n, ∃ d, HasPartialDerivative f x j d) ∧
      (∀ j : Fin n, CrOn r U (fun x => partialDerivative f x j)) := by
  have hsel (hd : TotalDifferentiableOn U f) (a : E n) (ha : a ∈ U) :
      HasTotalDerivative U f (totalDerivative f a) a := by
    obtain ⟨A, hA⟩ := hd a ha
    rwa [totalDerivative_eq U f A a hA]
  constructor
  · intro hf
    change TotalDifferentiableOn U f ∧ CrOn r U (totalDerivative f) at hf
    refine ⟨fun x hx j => ⟨_, totalDerivative_hasPartialDerivative U f x _ (hsel hf.1 x hx) j⟩, ?_⟩
    intro j
    apply (crOn_iff_contDiffOn r U _ hU).mpr
    exact (((crOn_iff_contDiffOn r U _ hU).mp hf.2).clm_apply contDiffOn_const).congr
      (fun x hx => totalDerivative_partialDerivative U f x _ (hsel hf.1 x hx) j)
  · rintro ⟨hd, hp⟩
    have hc (j : Fin n) : ContinuousOn (fun x => partialDerivative f x j) U :=
      ((crOn_iff_contDiffOn r U _ hU).mp (hp j)).continuousOn
    have hdiff := (continuous_partials_continuous_totalDerivative U f hU hd hc).1
    change TotalDifferentiableOn U f ∧ CrOn r U (totalDerivative f)
    refine ⟨hdiff, (crOn_iff_contDiffOn r U _ hU).mpr ?_⟩
    apply (contDiffOn_clm_iff_basis r U (totalDerivative f)).mpr
    intro j
    exact ((crOn_iff_contDiffOn r U _ hU).mp (hp j)).congr
      (fun x hx => (totalDerivative_partialDerivative U f x _ (hsel hdiff x hx) j).symm)

/-- All ordered lists are quantified. In particular no use is made of
Schwarz symmetry, which belongs to the following chapter. -/
theorem crOn_iff_ordered_partials {n m : ℕ} (r : ℕ) (U : Set (E n))
    (f : E n → E m) (hU : IsOpen U) :
    CrOn r U f ↔ HasContinuousOrderedPartials r U f := by
  induction r generalizing f with
  | zero => exact (hasContinuousOrderedPartials_zero U f).symm
  | succ r ih =>
    rw [hasContinuousOrderedPartials_succ]
    constructor
    · intro hf
      obtain ⟨hd, hp⟩ := (crOn_succ_iff_partials r U f hU).mp hf
      exact ⟨((crOn_iff_contDiffOn (r + 1) U f hU).mp hf).continuousOn,
        hd, fun j => (ih _).mp (hp j)⟩
    · rintro ⟨_, hd, hp⟩
      exact (crOn_succ_iff_partials r U f hU).mpr ⟨hd, fun j => (ih _).mpr (hp j)⟩

section Multilinear
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Finite basis expansion proves continuity of an algebraic multilinear
operation, including empty arity and zero-dimensional factors. -/
theorem finiteDimensional_multilinear_continuous (k : ℕ) (V : Fin k → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)] (B : MultilinearMap ℝ V Y) : Continuous B := by
  classical
  let b := fun i => Module.finBasis ℝ (V i)
  have hexp (v : (i : Fin k) → V i) :
      B v = ∑ j : (i : Fin k) → Fin (Module.finrank ℝ (V i)),
        (∏ i, (b i).repr (v i) (j i)) • B (fun i => b i (j i)) := by
    have hv (i : Fin k) : v i = ∑ j, (b i).repr (v i) j • b i j :=
      ((b i).sum_repr (v i)).symm
    conv_lhs => rw [show v = (fun i => ∑ j, (b i).repr (v i) j • b i j) from funext hv]
    rw [B.map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact B.map_smul_univ _ _
  have he : (B : ((i : Fin k) → V i) → Y) =
      (fun v => ∑ j : (i : Fin k) → Fin (Module.finrank ℝ (V i)),
        (∏ i, (b i).repr (v i) (j i)) • B (fun i => b i (j i))) := funext hexp
  rw [he]
  apply continuous_finsetSum
  intro j _
  apply Continuous.smul ?_ continuous_const
  apply continuous_finsetProd
  intro i _
  exact ((b i).coord (j i)).continuous_of_finiteDimensional.comp (continuous_apply i)

theorem crOn_multilinear (r k : ℕ) (V : Fin k → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    (B : MultilinearMap ℝ V Y) (U : Set X) (f : (i : Fin k) → X → V i)
    (hU : IsOpen U) (hf : ∀ i, CrOn r U (f i)) :
    CrOn r U (fun x => B (fun i => f i x)) := by
  let C : ContinuousMultilinearMap ℝ V Y :=
    ⟨B, finiteDimensional_multilinear_continuous k V B⟩
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  exact C.contDiff.comp_contDiffOn (contDiffOn_pi.mpr
    (fun i => (crOn_iff_contDiffOn r U _ hU).mp (hf i)))

theorem smoothOn_multilinear (k : ℕ) (V : Fin k → Type)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    [∀ i, FiniteDimensional ℝ (V i)]
    (B : MultilinearMap ℝ V Y) (U : Set X) (f : (i : Fin k) → X → V i)
    (hU : IsOpen U) (hf : ∀ i, SmoothOn U (f i)) :
    SmoothOn U (fun x => B (fun i => f i x)) := by
  change ∀ r : ℕ, CrOn r U _
  intro r
  exact crOn_multilinear r k V B U f hU (fun i => hf i r)

end Multilinear

end D04
