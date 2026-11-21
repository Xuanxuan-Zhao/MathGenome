import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Higher differentials and multi-index notation on the canonical Euclidean spaces.
The independent Model supplies canonical definitions; all existence, recurrence,
coordinate reconstruction, and boundary-case assertions are proved below. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04
abbrev Differential : Specs.D04.C03.HigherInterfaces.DifferentialType :=
  @Specs.D04.C03.HigherInterfaces.Model.Differential

abbrev differentialSuccEquiv : Specs.D04.C03.HigherInterfaces.differentialSuccEquivType :=
  @Specs.D04.C03.HigherInterfaces.Model.differentialSuccEquiv

abbrev differentialCoefficients : Specs.D04.C03.HigherInterfaces.differentialCoefficientsType :=
  @Specs.D04.C03.HigherInterfaces.Model.differentialCoefficients

abbrev higherDifferential : Specs.D04.C03.HigherInterfaces.higherDifferentialType :=
  @Specs.D04.C03.HigherInterfaces.Model.higherDifferential

abbrev TimesDifferentiableAt : Specs.D04.C03.HigherInterfaces.TimesDifferentiableAtType :=
  @Specs.D04.C03.HigherInterfaces.Model.TimesDifferentiableAt

abbrev differentialDiagonal : Specs.D04.C03.HigherInterfaces.differentialDiagonalType :=
  @Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal

abbrev DerivativeMultiIndex : Specs.D04.C03.HigherInterfaces.MultiIndexType :=
  @Specs.D04.C03.HigherInterfaces.Model.MultiIndex

abbrev multiIndexDegree : Specs.D04.C03.HigherInterfaces.multiIndexDegreeType :=
  @Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree

abbrev multiIndexFactorial : Specs.D04.C03.HigherInterfaces.multiIndexFactorialType :=
  @Specs.D04.C03.HigherInterfaces.Model.multiIndexFactorial

abbrev multiIndexMonomial : Specs.D04.C03.HigherInterfaces.multiIndexMonomialType :=
  @Specs.D04.C03.HigherInterfaces.Model.multiIndexMonomial

abbrev multiIndexWord : Specs.D04.C03.HigherInterfaces.multiIndexWordType :=
  @Specs.D04.C03.HigherInterfaces.Model.multiIndexWord

abbrev orderedPartial : Specs.D04.C03.HigherInterfaces.orderedPartialType :=
  @Specs.D04.C03.HigherInterfaces.Model.orderedPartial

abbrev multiIndexPartial : Specs.D04.C03.HigherInterfaces.multiIndexPartialType :=
  @Specs.D04.C03.HigherInterfaces.Model.multiIndexPartial

abbrev taylorPolynomial : Specs.D04.C03.HigherInterfaces.taylorPolynomialType :=
  @Specs.D04.C03.HigherInterfaces.Model.taylorPolynomial

abbrev taylorRemainder : Specs.D04.C03.HigherInterfaces.taylorRemainderType :=
  @Specs.D04.C03.HigherInterfaces.Model.taylorRemainder

section Generic
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

 theorem differentialSuccEquiv_apply (k : ℕ) (A : X →L[ℝ] Differential X Y k)
    (v : Fin (k + 1) → X) :
    differentialSuccEquiv X Y k A v = A (v 0) (Fin.tail v) := rfl

 theorem differentialSuccEquiv_symm_apply (k : ℕ) (T : Differential X Y (k + 1))
    (v : X) (vs : Fin k → X) :
    (differentialSuccEquiv X Y k).symm T v vs = T (Fin.cons v vs) := rfl

 theorem higherDifferential_zero (f : X → Y) (a : X) (v : Fin 0 → X) :
    higherDifferential 0 f a v = f a := rfl

 theorem higherDifferential_succ (k : ℕ) (f : X → Y) (a : X) :
    higherDifferential (k+1) f a =
      differentialSuccEquiv X Y k (totalDerivative (higherDifferential k f) a) := rfl

 theorem higherDifferential_succ_apply (k : ℕ) (f : X → Y) (a v : X)
    (vs : Fin k → X) :
    higherDifferential (k+1) f a (Fin.cons v vs) =
      totalDerivative (higherDifferential k f) a v vs := by
  rfl

 theorem differentialDiagonal_zero (T : Differential X Y 0) (h : X) :
    differentialDiagonal T h = T (fun i => Fin.elim0 i) := by
  exact congrArg T (Subsingleton.elim _ _)

 theorem timesDifferentiableAt_zero (U : Set X) (f : X → Y) (a : X) :
    TimesDifferentiableAt 0 U f a ↔ IsOpen U ∧ a ∈ U := Iff.rfl

 theorem timesDifferentiableAt_succ (k : ℕ) (U : Set X) (f : X → Y) (a : X) :
    TimesDifferentiableAt (k+1) U f a ↔
      ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
        (∀ x ∈ V, TimesDifferentiableAt k U f x) ∧
        TotalDifferentiableAt V (higherDifferential k f) a := Iff.rfl

 theorem timesDifferentiableAt_domain (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt k U f a) : IsOpen U ∧ a ∈ U := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    obtain ⟨V, _, ha, _, hlow, _⟩ := hf
    exact ih (hlow a ha)

 theorem timesDifferentiableAt_lower (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a) : TimesDifferentiableAt k U f a := by
  obtain ⟨V, _, ha, _, hlow, _⟩ := hf
  exact hlow a ha

/-- The final derivative exists at the base point; its continuity nearby is not a premise. -/
 theorem timesDifferentiableAt_hasFDerivAt (k : ℕ) (U : Set X) (f : X → Y) (a : X)
    (hf : TimesDifferentiableAt (k+1) U f a) :
    HasFDerivAt (higherDifferential k f)
      ((differentialSuccEquiv X Y k).symm (higherDifferential (k+1) f a)) a := by
  obtain ⟨V, hV, ha, _, _, hd⟩ := hf
  have hh := (totalDifferentiableAt_iff_differentiableAt V _ a hV ha).mp hd
  simpa only [higherDifferential_succ, ContinuousLinearEquiv.symm_apply_apply] using! hh.hasFDerivAt

 theorem timesDifferentiableAt_one (U : Set X) (f : X → Y) (a : X) :
    TimesDifferentiableAt 1 U f a ↔ TotalDifferentiableAt U f a := by
  have he : DifferentiableAt ℝ (higherDifferential 0 f) a ↔ DifferentiableAt ℝ f a :=
    (continuousMultilinearCurryFin0 ℝ X Y).symm.comp_differentiableAt_iff
  constructor
  · intro hf
    have hdom := timesDifferentiableAt_domain 1 U f a hf
    obtain ⟨V, hV, ha, _, _, hd⟩ := hf
    apply (totalDifferentiableAt_iff_differentiableAt U f a hdom.1 hdom.2).mpr
    exact he.mp ((totalDifferentiableAt_iff_differentiableAt V _ a hV ha).mp hd)
  · intro hf
    obtain ⟨A, hA⟩ := hf
    have hdom := hA
    change IsOpen U ∧ a ∈ U ∧ _ at hdom
    refine ⟨U, hdom.1, hdom.2.1, Subset.rfl, ?_, ?_⟩
    · intro x hx; exact ⟨hdom.1, hx⟩
    · apply (totalDifferentiableAt_iff_differentiableAt U _ a hdom.1 hdom.2.1).mpr
      exact he.mpr ((hasTotalDerivative_iff_hasFDerivAt U _ _ a hdom.1 hdom.2.1).mp hA).differentiableAt

/-- Restricting an ambient extension to U loses none of the higher derivatives on U. -/
 theorem higherDifferential_congr (k : ℕ) (U : Set X) (f g : X → Y)
    (hU : IsOpen U) (hfg : EqOn f g U) :
    EqOn (higherDifferential k f) (higherDifferential k g) U := by
  intro a ha
  have he : f =ᶠ[𝓝 a] g := Filter.eventuallyEq_of_mem (hU.mem_nhds ha) hfg
  exact (he.iteratedFDeriv ℝ k).eq_of_nhds

 theorem timesDifferentiableAt_congr (k : ℕ) (U : Set X) (f g : X → Y) (a : X)
    (hU : IsOpen U) (hfg : EqOn f g U) :
    TimesDifferentiableAt k U f a ↔ TimesDifferentiableAt k U g a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [timesDifferentiableAt_succ, timesDifferentiableAt_succ]
    apply exists_congr
    intro V
    apply and_congr_right; intro hV
    apply and_congr_right; intro haV
    apply and_congr_right; intro hVU
    apply and_congr
    · exact forall_congr' fun x => forall_congr' fun _ =>
        ih x
    · change (∃ A, HasTotalDerivative V (higherDifferential k f) A a) ↔
        (∃ A, HasTotalDerivative V (higherDifferential k g) A a)
      exact exists_congr fun A => hasTotalDerivative_congr V _ A a _ haV
        ((higherDifferential_congr k U f g hU hfg).mono hVU)

 theorem taylorPolynomial_zero (f : X → Y) (a h : X) :
    taylorPolynomial 0 f a h = f a := by
  simp [taylorPolynomial, Specs.D04.C03.HigherInterfaces.Model.taylorPolynomial,
    Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal,
    Specs.D04.C03.HigherInterfaces.Model.higherDifferential]

 theorem taylorPolynomial_congr (k : ℕ) (U : Set X) (f g : X → Y) (a h : X)
    (hU : IsOpen U) (ha : a ∈ U) (hfg : EqOn f g U) :
    taylorPolynomial k f a h = taylorPolynomial k g a h := by
  apply Finset.sum_congr rfl
  intro j _
  change ((j.factorial : ℝ)⁻¹) • differentialDiagonal (higherDifferential j f a) h =
    ((j.factorial : ℝ)⁻¹) • differentialDiagonal (higherDifferential j g a) h
  rw [(higherDifferential_congr j U f g hU hfg) ha]

 theorem taylorPolynomial_zero_increment (k : ℕ) (f : X → Y) (a : X) :
    taylorPolynomial k f a 0 = f a := by
  induction k with
  | zero => exact taylorPolynomial_zero f a 0
  | succ k ih =>
    change (∑ j ∈ Finset.range (k+1+1), _) = _
    rw [Finset.sum_range_succ]
    change taylorPolynomial k f a 0 + _ = _
    rw [ih]
    have hz : differentialDiagonal (higherDifferential (k+1) f a) 0 = 0 :=
      (higherDifferential (k+1) f a).toMultilinearMap.map_coord_zero 0 rfl
    change f a + ((k+1).factorial : ℝ)⁻¹ • differentialDiagonal _ 0 = f a
    rw [hz, smul_zero, add_zero]

 theorem taylorRemainder_zero_increment (k : ℕ) (f : X → Y) (a : X) :
    taylorRemainder k f a 0 = 0 := by
  change f (a+0) - taylorPolynomial k f a 0 = 0
  rw [taylorPolynomial_zero_increment, add_zero, sub_self]

 theorem taylorRemainder_expansion (k : ℕ) (f : X → Y) (a h : X) :
    f (a+h) = taylorPolynomial k f a h + taylorRemainder k f a h := by
  exact (add_sub_cancel _ _).symm

end Generic

section Coordinates
variable {n k : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

 theorem differentialCoefficients_apply (T : Differential (E n) Y k) (j : Fin k → Fin n) :
    differentialCoefficients k T j = T (fun r => standardBasis n (j r)) := rfl

/-- Every tensor is reconstructed by the finite expansion in basis tuples. -/
 theorem differential_expansion (T : Differential (E n) Y k) (v : Fin k → E n) :
    T v = ∑ j : Fin k → Fin n, (∏ r, v r (j r)) • differentialCoefficients k T j := by
  classical
  have hv (r : Fin k) : v r = ∑ j : Fin n, v r j • standardBasis n j := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using
      ((standardBasis n).sum_repr (v r)).symm
  conv_lhs => rw [show v = (fun r => ∑ j : Fin n, v r j • standardBasis n j) from funext hv]
  change T.toMultilinearMap (fun r => ∑ j : Fin n, v r j • standardBasis n j) = _
  rw [T.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact T.toMultilinearMap.map_smul_univ _ _

 theorem differentialCoefficients_injective :
    Function.Injective (differentialCoefficients (n := n) (Y := Y) k) := by
  intro T S h
  have he : T.toMultilinearMap = S.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ => standardBasis n) fun j => congrFun h j
  exact ContinuousMultilinearMap.toMultilinearMap_injective he

/-- Every family of basis-tuple coefficients is realized by a tensor.
The construction is the finite sum of products of coordinate projections. -/
 theorem differentialCoefficients_surjective :
    Function.Surjective (differentialCoefficients (n := n) (Y := Y) k) := by
  classical
  intro c
  let T : Differential (E n) Y k := ∑ j : Fin k → Fin n,
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (c j)).compContinuousLinearMap
      (fun r => PiLp.proj 2 (fun _ : Fin n => ℝ) (j r))
  refine ⟨T, ?_⟩
  funext j
  rw [differentialCoefficients_apply]
  simp only [T, sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, PiLp.proj_apply,
    standardBasis_apply]
  have he (i : Fin k → Fin n) :
      (∏ r : Fin k, (if i r = j r then (1 : ℝ) else 0)) = if i = j then 1 else 0 := by
    rw [Fintype.prod_boole]
    by_cases hij : i = j
    · subst i; simp
    · have hn : ¬ ∀ r, i r = j r := fun h => hij (funext h)
      simp [hij, hn]
  simp_rw [he, ite_smul, one_smul, zero_smul]
  simp

/-- In the finite-dimensional case the basis-tuple identification and its
inverse are continuous for the operator norm and the finite coordinate norm. -/
 theorem differentialCoefficients_continuousLinearEquiv (n m k : ℕ) :
    ∃ e : Differential (E n) (E m) k ≃L[ℝ] ((Fin k → Fin n) → E m),
      ∀ T j, e T j = T (fun r => standardBasis n (j r)) := by
  let c := differentialCoefficients (n := n) (Y := E m) k
  have hi : Function.Injective c := differentialCoefficients_injective
  have hs : Function.Surjective c := differentialCoefficients_surjective
  let : FiniteDimensional ℝ (Differential (E n) (E m) k) :=
    FiniteDimensional.of_injective c.toLinearMap hi
  let e := (LinearEquiv.ofBijective c.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv
  exact ⟨e, fun _ _ => rfl⟩

/-- Currying is precisely the regrouping of the finite basis-tuple coefficients. -/
 theorem differentialSuccEquiv_basis (A : E n →L[ℝ] Differential (E n) Y k)
    (j : Fin (k+1) → Fin n) :
    differentialCoefficients (k+1) (differentialSuccEquiv (E n) Y k A) j =
      differentialCoefficients k (A (standardBasis n (j 0))) (Fin.tail j) := rfl

 theorem multiIndexWord_length (α : DerivativeMultiIndex n) :
    (multiIndexWord α).length = multiIndexDegree α := by
  simp [multiIndexWord, Specs.D04.C03.HigherInterfaces.Model.multiIndexWord,
    multiIndexDegree, Specs.D04.C03.HigherInterfaces.Model.multiIndexDegree,
    List.length_flatten, List.map_ofFn, List.sum_ofFn]

 theorem multiIndexWord_count (α : DerivativeMultiIndex n) (i : Fin n) :
    (multiIndexWord α).count i = α i := by
  simp [multiIndexWord, Specs.D04.C03.HigherInterfaces.Model.multiIndexWord,
    List.count_flatten, List.map_ofFn, List.sum_ofFn, List.count_replicate]

 theorem orderedPartial_nil (f : E n → Y) : orderedPartial [] f = f := rfl

 theorem orderedPartial_cons (i : Fin n) (is : List (Fin n)) (f : E n → Y) (a : E n) :
    orderedPartial (i :: is) f a = directionalDerivative (orderedPartial is f) a (standardBasis n i) := rfl

 theorem multiIndexPartial_eq (α : DerivativeMultiIndex n) (f : E n → Y) :
    multiIndexPartial α f = orderedPartial (multiIndexWord α) f := rfl

end Coordinates

section DimensionZero

 theorem multiIndex_dimension_zero_unique (α β : DerivativeMultiIndex 0) : α = β := Subsingleton.elim _ _

 theorem multiIndexDegree_dimension_zero (α : DerivativeMultiIndex 0) : multiIndexDegree α = 0 := rfl

 theorem multiIndexFactorial_dimension_zero (α : DerivativeMultiIndex 0) : multiIndexFactorial α = 1 := rfl

 theorem multiIndexMonomial_dimension_zero (α : DerivativeMultiIndex 0) (h : E 0) :
    multiIndexMonomial α h = 1 := rfl

 theorem multiIndexPartial_dimension_zero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (α : DerivativeMultiIndex 0) (f : E 0 → Y) : multiIndexPartial α f = f := rfl

 theorem higherDifferential_dimension_zero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (hk : 0 < k) (f : E 0 → Y) (a : E 0) : higherDifferential k f a = 0 := by
  ext v
  exact (higherDifferential k f a).toMultilinearMap.map_coord_zero ⟨0, hk⟩ (vector_dimension_zero _)

 theorem taylorPolynomial_dimension_zero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (f : E 0 → Y) (a h : E 0) : taylorPolynomial k f a h = f a := by
  induction k with
  | zero => exact taylorPolynomial_zero f a h
  | succ k ih =>
    change (∑ j ∈ Finset.range (k+1+1), _) = _
    rw [Finset.sum_range_succ]
    change taylorPolynomial k f a h + _ = _
    rw [ih]
    have hz := higherDifferential_dimension_zero (k+1) (Nat.succ_pos k) f a
    simp [hz, Specs.D04.C03.HigherInterfaces.Model.differentialDiagonal]

 theorem taylorRemainder_dimension_zero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (f : E 0 → Y) (a h : E 0) : taylorRemainder k f a h = 0 := by
  change f (a+h) - taylorPolynomial k f a h = 0
  rw [taylorPolynomial_dimension_zero]
  have hh : a+h = a := Subsingleton.elim _ _
  rw [hh, sub_self]

end DimensionZero
end D04
