import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Tori
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.HomotopyOperator
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.PathIntegration
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Work on the torus algebra calculation. The original target is declared
only once the full geometric and algebraic construction has been proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 4000000
noncomputable section

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData SphereTorusData TorusDeRhamData

/-- The specified coordinate paths are loops in the actual quotient. -/
theorem coordinateLoop_closed {r : ℕ} (j : Fin r) :
    coordinateLoop j 0 = coordinateLoop j 1 := by
  classical
  funext i
  by_cases h : i = j
  · subst i
    simp [coordinateLoop, SphereTorusData.quotientProjection, AddCircle.coe_period]
  · simp [coordinateLoop, SphereTorusData.quotientProjection, Pi.single_apply, h]

section Classes
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

/-- Equality of classes is exactly exactness of the difference. This is useful
for the endpoint and averaging identities, without assuming the desired equality
of cohomology classes as input. -/
theorem class_eq_iff_difference_exact {k : ℕ} (α β : K.closed k) :
    K.classOf k α = K.classOf k β ↔ α.val - β.val ∈ K.exact k := by
  rw [← sub_eq_zero, ← map_sub, DeRhamResults.class_zero_iff_exact K k (α - β)]
  rfl

/-- The positive-degree part of a chain homotopy gives equality of classes.
The witness is the actual smooth primitive in the source complex. -/
theorem class_eq_of_derivative_difference {k : ℕ} (α β : K.closed (k+1))
    (η : K.forms k) (hη : K.d k η = α.val - β.val) :
    K.classOf (k+1) α = K.classOf (k+1) β := by
  apply (class_eq_iff_difference_exact K α β).mpr
  exact ⟨η, hη⟩

/-- A closed form is cohomologous to its chain-homotopic image. -/
theorem class_eq_of_chain_identity
    (A : ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (H : ∀ k, K.forms (k+1) →ₗ[ℝ] K.forms k)
    (hchain : ∀ k ω, K.d k (A k ω) = A (k+1) (K.d k ω))
    (hidentity : ∀ k ω, K.d k (H k ω) + H (k+1) (K.d (k+1) ω) =
      A (k+1) ω - ω)
    (k : ℕ) (ω : K.closed (k+1)) :
    K.classOf (k+1)
      ⟨A (k+1) ω.val, by
        change K.d (k+1) (A (k+1) ω.val) = 0
        have hω : K.d (k+1) ω.val = 0 := ω.property
        rw [hchain, hω, map_zero]⟩ =
        K.classOf (k+1) ω := by
  apply class_eq_of_derivative_difference K _ ω (H k ω.val)
  have hω : K.d (k+1) ω.val = 0 := ω.property
  simpa only [hω, map_zero, add_zero] using hidentity k ω.val

/-- Algebraic end of the averaging argument: a retraction onto a zero-
differential model, together with actual exact errors, gives an isomorphism.
This lemma does not assert that the required geometric retraction exists. -/
def cohomologyEquivOfRetraction (k : ℕ) (V : Type u) [AddCommGroup V] [Module ℝ V]
    (E : V →ₗ[ℝ] K.closed k) (Q : K.forms k →ₗ[ℝ] V)
    (hQE : ∀ x, Q (E x).val = x)
    (hQexact : ∀ η, η ∈ K.exact k → Q η = 0)
    (herror : ∀ ω : K.closed k, (E (Q ω.val)).val - ω.val ∈ K.exact k) :
    V ≃ₗ[ℝ] K.Cohomology k :=
  LinearEquiv.ofBijective ((K.classOf k).comp E) ⟨by
    intro x y hxy
    have he := hQexact _ ((class_eq_iff_difference_exact K (E x) (E y)).mp hxy)
    have hsub : x - y = 0 := by
      rw [map_sub Q, hQE, hQE] at he
      exact he
    exact sub_eq_zero.mp hsub,
    by
      intro c
      obtain ⟨ω, rfl⟩ := (K.boundaries k).mkQ_surjective c
      exact ⟨Q ω.val, (class_eq_iff_difference_exact K _ ω).mpr (herror ω)⟩⟩

end Classes

section ExtremeDegrees

/-- Evaluation at the identity identifies locally constant torus functions
with real scalars; connectedness comes from the actual quotient topology. -/
def torusLocallyConstantEquiv (r : ℕ) : LocallyConstant (FlatTorus r) ℝ ≃ₗ[ℝ] ℝ where
  toFun f := f 0
  invFun t := LocallyConstant.const _ t
  left_inv f := by
    apply LocallyConstant.ext
    intro p
    exact f.apply_eq_of_preconnectedSpace 0 p
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The scalar-unit normalization in degree zero for every torus. -/
theorem torus_degreeZero (r : ℕ)
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P) :
    ∃ e : ExteriorModel r 0 ≃ₗ[ℝ] K.Cohomology 0,
      e ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1) = P.one := by
  obtain ⟨e, he⟩ := DeRhamResults.h0_locally_constant K
  let g : ExteriorModel r 0 ≃ₗ[ℝ] K.Cohomology 0 :=
    (exteriorPower.zeroEquiv ℝ (Euclidean r)).trans
      ((torusLocallyConstantEquiv r).symm.trans e.symm)
  refine ⟨g, ?_⟩
  obtain ⟨ε, hε, hunit⟩ := hP.2.2.2.2.2.1
  apply e.injective
  apply LocallyConstant.ext
  intro p
  rw [hunit, he ε p]
  change (e (e.symm ((torusLocallyConstantEquiv r).symm
    ((exteriorPower.zeroEquiv ℝ (Euclidean r))
      ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1))))) p = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hε]
  change (1 : ℝ) =
    (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p)))
      ((exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm 1)
  exact ((exteriorPower.zeroEquiv ℝ _).apply_symm_apply 1).symm

/-- Both sides of the proposed algebra presentation vanish above dimension. -/
theorem torus_above_dimension_equiv (r : ℕ)
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (k : ℕ) (hk : r < k) :
    Nonempty (ExteriorModel r k ≃ₗ[ℝ] K.Cohomology k) := by
  letI := DeRhamResults.above_dimension K k hk
  have hz : Module.finrank ℝ (ExteriorModel r k) = 0 := by
    simp only [ExteriorModel, exteriorPower.finrank_eq, Module.finrank_pi,
      Fintype.card_fin]
    exact Nat.choose_eq_zero_of_lt hk
  letI := (Module.finrank_zero_iff (R := ℝ)).mp hz
  exact ⟨LinearEquiv.ofSubsingleton _ _⟩

end ExtremeDegrees

section EmptyProduct

/-- Positive-degree parts of the proposed exterior model vanish also at r=0. -/
theorem emptyTorusExterior_subsingleton (k : ℕ) :
    Subsingleton (ExteriorModel 0 (k+1)) := by
  apply (Module.finrank_zero_iff (R := ℝ)).mp
  simp [ExteriorModel, exteriorPower.finrank_eq]

/-- Degree-zero wedge has the actual exterior-algebra unit, with no arbitrary
choice of scalar normalization. -/
theorem exteriorModel_zero_unit (r : ℕ) :
    exteriorPower.wedge ℝ (Euclidean r) 0 0
      ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1)
      ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1) =
    (exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1 := by
  apply Subtype.ext
  simp [exteriorPower.zeroEquiv_symm_apply]

/-- The unit determines the scalar algebra isomorphism for the empty torus. -/
theorem emptyTorus_degreeZero
    (S : SmoothManifold 0 .euclidean (FlatTorus 0))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P) :
    ∃ e : ExteriorModel 0 0 ≃ₗ[ℝ] K.Cohomology 0,
      e ((exteriorPower.zeroEquiv ℝ (Euclidean 0)).symm 1) = P.one := by
  exact torus_degreeZero 0 S C B K P hP

/-- Full graded-algebra presentation for r=0, including multiplication. -/
theorem emptyTorus_presentation
    (S : SmoothManifold 0 .euclidean (FlatTorus 0))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P) :
    Nonempty (Presentation K P) := by
  obtain ⟨e0, he0⟩ := emptyTorus_degreeZero S C B K P hP
  let e (k : ℕ) : ExteriorModel 0 k ≃ₗ[ℝ] K.Cohomology k :=
    match k with
    | 0 => e0
    | k+1 => by
      letI := emptyTorusExterior_subsingleton k
      letI := DeRhamResults.above_dimension K (k+1) (Nat.zero_lt_succ k)
      exact LinearEquiv.ofSubsingleton _ _
  refine ⟨{
    theta := Fin.elim0
    coordinate := fun i => Fin.elim0 i
    loop_smooth := fun i => Fin.elim0 i
    loop_closed := fun i => Fin.elim0 i
    period := fun i => Fin.elim0 i
    equiv := e
    generator := fun i => Fin.elim0 i
    one := he0
    mul := ?_ }⟩
  intro k l x y
  cases k with
  | zero =>
    cases l with
    | zero =>
      change e0 (exteriorPower.wedge ℝ (Euclidean 0) 0 0 x y) =
        P.mul 0 0 (e0 x) (e0 y)
      let u := (exteriorPower.zeroEquiv ℝ (Euclidean 0)).symm 1
      have hx : x = (exteriorPower.zeroEquiv ℝ (Euclidean 0) x) • u := by
        apply (exteriorPower.zeroEquiv ℝ (Euclidean 0)).injective
        simp [u]
      have hy : y = (exteriorPower.zeroEquiv ℝ (Euclidean 0) y) • u := by
        apply (exteriorPower.zeroEquiv ℝ (Euclidean 0)).injective
        simp [u]
      have hu : exteriorPower.wedge ℝ (Euclidean 0) 0 0 u u = u :=
        exteriorModel_zero_unit 0
      have hPP : P.mul 0 0 P.one P.one = P.one := by
        simpa using hP.2.2.2.2.2.2.2.2.1 0 P.one
      rw [hx, hy]
      simp only [map_smul, LinearMap.smul_apply]
      rw [hu]
      change _ = P.mul 0 0
        ((exteriorPower.zeroEquiv ℝ (Euclidean 0) x) • e0 u)
        ((exteriorPower.zeroEquiv ℝ (Euclidean 0) y) • e0 u)
      rw [hP.2.2.1, hP.2.2.2.1, he0, hPP]
      exact smul_comm _ _ _
    | succ l =>
      letI := DeRhamResults.above_dimension K (0+(l+1)) (by simp)
      exact Subsingleton.elim _ _
  | succ k =>
    letI := DeRhamResults.above_dimension K (k+1+l)
      (lt_of_lt_of_le (Nat.zero_lt_succ k) (Nat.le_add_right _ _))
    exact Subsingleton.elim _ _

end EmptyProduct

section AlgebraAssembly
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

/-- The quotient product agrees with wedge whenever its closed representative
has been explicitly identified. -/
theorem product_class_eq_of_wedge (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    {k l : ℕ} (α : K.closed k) (β : K.closed l) (γ : K.closed (k+l))
    (hγ : γ.val.val = fieldWedge α.val.val β.val.val) :
    P.mul k l (K.classOf k α) (K.classOf l β) = K.classOf (k+l) γ := by
  obtain ⟨δ, hδ, hmul⟩ := hP.2.2.2.2.1 k l α β
  have heq : δ = γ := Subtype.ext (Subtype.ext (hδ.trans hγ.symm))
  simpa only [heq] using hmul

end AlgebraAssembly

section TorusAssembly

/-- The final algebraic assembly uses a genuine inclusion of constant forms
and a coefficient retraction. Multiplicativity is required only of the inclusion;
the averaging projection need not preserve products. All geometric data in this
helper must be constructed before it proves any instance of the torus result. -/
def presentationOfRetraction {r : ℕ}
    {S : SmoothManifold r .euclidean (FlatTorus r)}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    (θ : Fin r → K.closed 1)
    (hcoordinate : ∀ i, IsCoordinateForm C i (θ i).val.val)
    (hloop : ∀ j : Fin r, PathIntegrationData.PiecewiseSmoothOn S (coordinateLoop j) 0 1)
    (hperiod : ∀ i j : Fin r,
      PathIntegrationData.pathIntegral S (covectorField (θ i).val.val) (coordinateLoop j) 0 1 =
        if i = j then 1 else 0)
    (E : ∀ k, ExteriorModel r k →ₗ[ℝ] K.closed k)
    (Q : ∀ k, K.forms k →ₗ[ℝ] ExteriorModel r k)
    (hQE : ∀ k x, Q k (E k x).val = x)
    (hQexact : ∀ k η, η ∈ K.exact k → Q k η = 0)
    (herror : ∀ k (ω : K.closed k), (E k (Q k ω.val)).val - ω.val ∈ K.exact k)
    (hgenerator : ∀ i, E 1 ((exteriorPower.oneEquiv ℝ (Euclidean r)).symm
      (Pi.single i 1)) = θ i)
    (hunit : K.classOf 0 (E 0 ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1)) = P.one)
    (hwedge : ∀ k l (x : ExteriorModel r k) (y : ExteriorModel r l),
      (E (k+l) (exteriorPower.wedge ℝ (Euclidean r) k l x y)).val.val =
        fieldWedge (E k x).val.val (E l y).val.val) : Presentation K P where
  theta := θ
  coordinate := hcoordinate
  loop_smooth := hloop
  loop_closed := coordinateLoop_closed
  period := hperiod
  equiv k := cohomologyEquivOfRetraction K k (ExteriorModel r k)
    (E k) (Q k) (hQE k) (hQexact k) (herror k)
  generator i := congrArg (K.classOf 1) (hgenerator i)
  one := hunit
  mul k l x y := (product_class_eq_of_wedge K P hP (E k x) (E l y)
    (E (k+l) (exteriorPower.wedge ℝ (Euclidean r) k l x y)) (hwedge k l x y)).symm

end TorusAssembly

section ChainProjection
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

/-- Restriction of a chain map to its closed forms. -/
def mapClosed (A : ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (hchain : ∀ k ω, K.d k (A k ω) = A (k+1) (K.d k ω)) (k : ℕ) :
    K.closed k →ₗ[ℝ] K.closed k where
  toFun ω := ⟨A k ω.val, by
    change K.d k (A k ω.val) = 0
    rw [hchain, show K.d k ω.val = 0 from ω.property, map_zero]⟩
  map_add' α β := Subtype.ext (map_add (A k) α.val β.val)
  map_smul' c α := Subtype.ext (map_smul (A k) c α.val)

/-- The full chain identity gives the equality of classes in every degree,
including degree zero, where no degree-minus-one primitive is introduced. -/
theorem class_eq_of_full_chain_identity
    (A : ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (H : ∀ k, K.forms (k+1) →ₗ[ℝ] K.forms k)
    (hchain : ∀ k ω, K.d k (A k ω) = A (k+1) (K.d k ω))
    (hpositive : ∀ k ω, K.d k (H k ω) + H (k+1) (K.d (k+1) ω) =
      A (k+1) ω - ω)
    (hzero : ∀ ω, H 0 (K.d 0 ω) = A 0 ω - ω)
    (k : ℕ) (ω : K.closed k) :
    K.classOf k (mapClosed K A hchain k ω) = K.classOf k ω := by
  cases k with
  | zero =>
    have hω : K.d 0 ω.val = 0 := ω.property
    have he : A 0 ω.val = ω.val := by
      have h := hzero ω.val
      rw [hω, map_zero] at h
      exact sub_eq_zero.mp h.symm
    apply congrArg (K.classOf 0)
    exact Subtype.ext he
  | succ k =>
    exact class_eq_of_chain_identity K A H hchain hpositive k ω

/-- Finite compositions preserve the original cohomology class. This is the
algebraic induction used when averaging one coordinate circle at a time. -/
theorem class_eq_of_fold_closed_maps {k : ℕ} {ι : Type*}
    (A : ι → K.closed k →ₗ[ℝ] K.closed k)
    (hA : ∀ i ω, K.classOf k (A i ω) = K.classOf k ω)
    (is : List ι) (ω : K.closed k) :
    K.classOf k (is.foldl (fun η i => A i η) ω) = K.classOf k ω := by
  induction is generalizing ω with
  | nil => rfl
  | cons i is ih =>
    exact (ih (A i ω)).trans (hA i ω)

end ChainProjection

section Homotopy
universe u
open HomotopyData

/-- The supplied operator hypothesis is used in its full, unspecialized form.
For each actual smooth homotopy it supplies a smooth primitive for the difference
of any closed endpoint pullbacks. No cohomology equality is assumed. -/
theorem homotopy_class_eq_conditional
    (hop : Specs.SmoothManifolds.DeRham.HomotopyOperator.homotopy_operatorType.{u})
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (F : M × UnitInterval → N) (hF : IsSmoothHomotopy S T F) :
    ∃ (D : HomotopyDifferentials S T F)
      (op : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k),
      IsCoefficientIntegral K J D op ∧ IsChainHomotopy K J D op ∧
      ∀ (k : ℕ) (ω : J.closed (k+1)) (η₁ η₀ : K.closed (k+1)),
        η₁.val.val = alpha D ω.val.val finalTime →
        η₀.val.val = alpha D ω.val.val initialTime →
        K.classOf (k+1) η₁ = K.classOf (k+1) η₀ := by
  obtain ⟨D, op, hcoeff, hchain, _⟩ := hop S T C B A E K J F hF
  refine ⟨D, op, hcoeff, hchain, ?_⟩
  intro k ω η₁ η₀ h₁ h₀
  apply class_eq_of_derivative_difference K η₁ η₀ (op k ω.val)
  apply Subtype.ext
  have hω : J.d (k+1) ω.val = 0 := ω.property
  have hid := hchain.1 k ω.val
  rw [hω, map_zero] at hid
  simp only [ZeroMemClass.coe_zero, add_zero] at hid
  change (K.d k (op k ω.val)).val = η₁.val.val - η₀.val.val
  rw [h₁, h₀]
  exact hid

/-- Endpoint class equality using the current proved upstream homotopy operator. -/
theorem homotopy_class_eq
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (F : M × UnitInterval → N) (hF : IsSmoothHomotopy S T F) :
    ∃ (D : HomotopyDifferentials S T F)
      (op : ∀ k, J.forms (k+1) →ₗ[ℝ] K.forms k),
      IsCoefficientIntegral K J D op ∧ IsChainHomotopy K J D op ∧
      ∀ (k : ℕ) (ω : J.closed (k+1)) (η₁ η₀ : K.closed (k+1)),
        η₁.val.val = alpha D ω.val.val finalTime →
        η₀.val.val = alpha D ω.val.val initialTime →
        K.classOf (k+1) η₁ = K.classOf (k+1) η₀ := by
  exact homotopy_class_eq_conditional HomotopyResults.homotopy_operator
    S T C B A E K J F hF

end Homotopy

end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusAveraging
/-! Analytic full-period invariance for the coefficient averaging used in the
geometric construction. These statements concern actual integrals on ℝ/ℤ. -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def circleAverage (f : AddCircle (1 : ℝ) → E) : E :=
  ∫ t in (0 : ℝ)..1, f (t : AddCircle (1 : ℝ))
theorem circleAverage_translate (f : AddCircle (1 : ℝ) → E) (s : AddCircle (1 : ℝ)) :
    circleAverage (fun t => f (t+s)) = circleAverage f := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective s
  let g : ℝ → E := fun t => f (t : AddCircle (1 : ℝ))
  have hg : Function.Periodic g 1 := by
    intro t
    simp only [g, AddCircle.coe_add_period]
  change (∫ t in (0 : ℝ)..1, f ((t : AddCircle (1 : ℝ)) + (r : AddCircle (1 : ℝ)))) = _
  simp_rw [← AddCircle.coe_add]
  change (∫ t in (0 : ℝ)..1, g (t+r)) = circleAverage f
  rw [intervalIntegral.integral_comp_add_right g r]
  simpa only [zero_add, add_comm 1 r, circleAverage, g] using hg.intervalIntegral_add_eq r 0

theorem circleAverage_const [CompleteSpace E] (v : E) : circleAverage (fun _ => v) = v := by
  simpa only [circleAverage, sub_zero, one_smul] using (intervalIntegral.integral_const (a := (0 : ℝ)) (b := 1) v)

theorem circleAverage_add (f g : AddCircle (1 : ℝ) → E)
    (hf : Continuous f) (hg : Continuous g) :
    circleAverage (f+g) = circleAverage f + circleAverage g := by
  apply intervalIntegral.integral_add
  · exact (hf.comp (AddCircle.continuous_mk' (1 : ℝ))).intervalIntegrable 0 1
  · exact (hg.comp (AddCircle.continuous_mk' (1 : ℝ))).intervalIntegrable 0 1

theorem circleAverage_smul (c : ℝ) (f : AddCircle (1 : ℝ) → E) :
    circleAverage (c • f) = c • circleAverage f := by
  exact intervalIntegral.integral_smul c _


section Primitives
open MeasureTheory
variable [CompleteSpace E]

/-! For a periodic coefficient the centered primitive is itself periodic,
including at the seam, and descends to ℝ/ℤ. The smoothness theorem is global
on the real lift; the intrinsic form/atlas bridge remains to be constructed. -/
def periodMean (f : ℝ → E) : E := ∫ t in (0 : ℝ)..1, f t
def centeredPrimitive (f : ℝ → E) (x : ℝ) : E :=
  ∫ t in (0 : ℝ)..x, (f t - periodMean f)

theorem hasDerivAt_centeredPrimitive (f : ℝ → E) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (centeredPrimitive f) (f x - periodMean f) x := by
  have hc : Continuous (fun t => f t - periodMean f) := hf.sub continuous_const
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem centeredPrimitive_periodic (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f 1) : Function.Periodic (centeredPrimitive f) 1 := by
  let g : ℝ → E := fun t => f t - periodMean f
  have hc : Continuous g := hf.sub continuous_const
  have hp : Function.Periodic g 1 := by intro t; simp only [g, hper t]
  have hmean : (∫ t in (0 : ℝ)..1, g t) = 0 := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)]
    simp [periodMean]
  intro x
  change (∫ t in (0 : ℝ)..x+1, g t) = ∫ t in (0 : ℝ)..x, g t
  rw [hp.intervalIntegral_add_eq_add 0 x (fun a b => hc.intervalIntegrable a b)]
  simp only [zero_add, hmean, add_zero]

theorem centeredPrimitive_smooth (f : ℝ → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (centeredPrimitive f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_centeredPrimitive f hf.continuous x).differentiableAt, ?_⟩
  have hd : deriv (centeredPrimitive f) = fun t => f t - periodMean f := by
    funext x
    exact (hasDerivAt_centeredPrimitive f hf.continuous x).deriv
  rw [hd]
  exact hf.sub contDiff_const

theorem periodMean_derivative_zero (f f' : ℝ → E)
    (hper : Function.Periodic f 1)
    (hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume 0 1) : periodMean f' = 0 := by
  change (∫ t in (0 : ℝ)..1, f' t) = 0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  have h01 : f 1 = f 0 := by simpa only [zero_add] using hper 0
  exact sub_eq_zero.mpr h01

def circlePrimitive (f : ℝ → E) (hf : Continuous f) (hper : Function.Periodic f 1) :
    AddCircle (1 : ℝ) → E := (centeredPrimitive_periodic f hf hper).lift

@[simp] theorem circlePrimitive_coe (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f 1) (x : ℝ) :
    circlePrimitive f hf hper (x : AddCircle (1 : ℝ)) = centeredPrimitive f x :=
  (centeredPrimitive_periodic f hf hper).lift_coe x

theorem circlePrimitive_continuous (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f 1) : Continuous (circlePrimitive f hf hper) := by
  apply continuous_quot_lift
  have hd : Differentiable ℝ (centeredPrimitive f) :=
    fun x => (hasDerivAt_centeredPrimitive f hf x).differentiableAt
  exact hd.continuous

theorem periodic_primitive_iff_mean_zero (f : ℝ → E) (hf : Continuous f)
    (hper : Function.Periodic f 1) :
    (∃ F : ℝ → E, Function.Periodic F 1 ∧ ∀ x, HasDerivAt F (f x) x) ↔
      periodMean f = 0 := by
  constructor
  · rintro ⟨F, hF, hder⟩
    exact periodMean_derivative_zero F f hF (fun x _ => hder x) (hf.intervalIntegrable 0 1)
  · intro hmean
    refine ⟨centeredPrimitive f, centeredPrimitive_periodic f hf hper, ?_⟩
    intro x
    simpa only [hmean, sub_zero] using hasDerivAt_centeredPrimitive f hf x

end Primitives

end SmoothManifolds.TorusAveraging



namespace SmoothManifolds.TorusCoordinates
open ModelData AtlasData TangentData TangentBundleData BundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  Set Filter
open scoped Topology

/-- Two local lifts of the quotient differ by one constant translation near
any point of overlap. This stronger version of angleChart_germ records the
actual affine ambient representative. -/
theorem angleChart_shift {r : ℕ} {a b : Euclidean r} {ε δ : ℝ}
    {c d : ModelChart r .euclidean (FlatTorus r)}
    (hc : IsAngleChart a ε c) (hd : IsAngleChart b δ d)
    (p : FlatTorus r) (hp : p ∈ c.source) (hp' : p ∈ d.source) :
    (fun q => (d q).val) =ᶠ[𝓝 p]
      (fun q => (c q).val + ((d p).val - (c p).val)) := by
  let u := (c p).val
  let v := (d p).val
  let F : Euclidean r → Euclidean r := fun y => y + (v - u)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by dsimp [F]; fun_prop
  have hccont := continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have hdcont := continuous_subtype_val.continuousAt.comp (d.continuousAt hp')
  have hFcont : ContinuousAt (fun q => F (c q).val) p := hF.continuous.continuousAt.comp hccont
  have hFp : F (c p).val = v := by dsimp [F, u, v]; abel
  have hproj : quotientProjection r (v - u) = 0 := by
    change (fun j => ((v j - u j : ℝ) : AddCircle (1 : ℝ))) = 0
    have hv := SphereTorus.angleChart_projection hd hp'
    have hu := SphereTorus.angleChart_projection hc hp
    funext j
    change (v j : AddCircle (1 : ℝ)) - (u j : AddCircle (1 : ℝ)) = 0
    exact sub_eq_zero.mpr (by exact congrFun (hv.trans hu.symm) j)
  have hbox := (SphereTorus.isOpen_angleBox v (1 / 4)).mem_nhds
    (SphereTorus.mem_angleBox_center v (by norm_num))
  have hFbox : ∀ᶠ q in 𝓝 p, F (c q).val ∈ angleBox v (1 / 4) := by
    exact hFcont.preimage_mem_nhds (by simpa [hFp] using hbox)
  have hdbox : ∀ᶠ q in 𝓝 p, (d q).val ∈ angleBox v (1 / 4) := hdcont.preimage_mem_nhds hbox
  filter_upwards [c.open_source.mem_nhds hp, d.open_source.mem_nhds hp', hFbox, hdbox]
    with q hqc hqd hqF hqdv
  apply Eq.symm
  apply SphereTorus.quotientProjection_injOn_box v
    (by norm_num : (1 : ℝ) / 4 < 1 / 2) hqF hqdv
  have he : quotientProjection r (F (c q).val) = quotientProjection r (c q).val := by
    funext j
    change ((c q).val j : AddCircle (1 : ℝ)) + ((v j - u j : ℝ) : AddCircle (1 : ℝ)) = _
    have hzero := congrFun hproj j
    change ((v j - u j : ℝ) : AddCircle (1 : ℝ)) = 0 at hzero
    rw [hzero, add_zero]
    rfl
  exact he.trans ((SphereTorus.angleChart_projection hc hqc).trans
    (SphereTorus.angleChart_projection hd hqd).symm)

/-- The intrinsic cotangent dx^i is independent of the chosen angle lift. -/
theorem angle_coordinateCovector_eq {r : ℕ}
    {S : SmoothManifold r .euclidean (FlatTorus r)}
    (C : CotangentBundle S) {a b : Euclidean r} {ε δ : ℝ}
    {c d : ModelChart r .euclidean (FlatTorus r)}
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hac : IsAngleChart a ε c) (had : IsAngleChart b δ d)
    (p : FlatTorus r) (hp : p ∈ c.source) (hpd : p ∈ d.source) (i : Fin r) :
    coordinateCovector C.tangent.fiberCoordinates c hc p hp i =
      coordinateCovector C.tangent.fiberCoordinates d hd p hpd i := by
  let xc := coordinateGerm S p c hc hp i
  let xd := coordinateGerm S p d hd hpd i
  have hshift : xd = xc + algebraMap ℝ (SmoothGerm S p)
      ((d p).val i - (c p).val i) := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [angleChart_shift hac had p hp hpd] with q hq
    exact congrFun hq i
  rw [← Covectors.coordinateCovector_germ C.tangent.fiberCoordinates c hc p hp i xc rfl,
    ← Covectors.coordinateCovector_germ C.tangent.fiberCoordinates d hd p hpd i xd rfl]
  apply LinearMap.ext
  intro v
  change v.val xc = v.val xd
  rw [hshift, map_add, derivation_kills_constants, add_zero]

/-- The nonmaximal angle atlas remains a subatlas of the specified standard
smooth structure. -/
theorem angleAtlas_subset {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r)) :
    angleAtlas r ⊆ S.smoothStructure.val := by
  rw [hS]
  exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas r)

/-- A genuine angle chart through every point. -/
theorem exists_angle_chart {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (p : FlatTorus r) :
    ∃ c : ModelChart r .euclidean (FlatTorus r),
      c ∈ S.smoothStructure.val ∧ p ∈ c.source ∧ c ∈ angleAtlas r := by
  obtain ⟨c, hc, hp⟩ := (SphereTorus.angleAtlas_isContDiffAtlas r).1 p
  exact ⟨c, angleAtlas_subset S hS hc, hp, hc⟩

/-- The coordinate covector field is chosen pointwise, with its choice
independence proved by the overlap lemma. -/
def angleCovector {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i : Fin r) : CovectorField S := fun p =>
  let hc := Classical.choose_spec (exists_angle_chart S hS p)
  coordinateCovector C.tangent.fiberCoordinates
    (Classical.choose (exists_angle_chart S hS p)) hc.1 p hc.2.1 i

theorem angleCovector_on_chart {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i : Fin r)
    (c : ModelChart r .euclidean (FlatTorus r)) (hc : c ∈ S.smoothStructure.val)
    {a : Euclidean r} {ε : ℝ} (hac : IsAngleChart a ε c)
    (p : FlatTorus r) (hp : p ∈ c.source) :
    angleCovector S hS C i p =
      coordinateCovector C.tangent.fiberCoordinates c hc p hp i := by
  let d := Classical.choose (exists_angle_chart S hS p)
  have hd := Classical.choose_spec (exists_angle_chart S hS p)
  obtain ⟨b, δ, hδ, hδ', had⟩ := hd.2.2
  exact angle_coordinateCovector_eq C hd.1 hc had hac p hd.2.1 hp i

/-- Every coordinate covector is locally the differential of a genuine global
smooth real function. -/
theorem angleCovector_locally_exact {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i : Fin r) (p : FlatTorus r) :
    ∃ (f : FlatTorus r → ℝ) (hf : PartitionData.ScalarSmooth S.smoothStructure.val f),
      ∀ᶠ q in 𝓝 p, angleCovector S hS C i q = dFunction S f hf q := by
  obtain ⟨c, hc, hp, a, ε, hε, hε', hac⟩ := exists_angle_chart S hS p
  obtain ⟨f, hf, he, hde⟩ :=
    ExteriorDerivativeResults.scalar_globalize_coordinate_differential C c hc p hp i
  refine ⟨f, hf, ?_⟩
  filter_upwards [c.open_source.mem_nhds hp, hde] with q hqc hdq
  rw [angleCovector_on_chart S hS C i c hc hac q hqc]
  exact (hdq hqc).symm

theorem angleCovector_smooth {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i : Fin r) :
    IsOneForm C (angleCovector S hS C i) := by
  letI := (cotangentSpace C).topology
  intro p
  obtain ⟨f, hf, he⟩ := angleCovector_locally_exact S hS C i p
  apply manifoldContDiffAt_congr ((Covectors.differential_smooth S C f hf) p)
  filter_upwards [he] with q hq
  exact congrArg (fun v => (⟨q, v⟩ : Bundle.TotalSpace (Euclidean r) (CotangentFiber S))) hq.symm

/-- The intrinsic exterior one-form descended from dx^i. -/
def angleForm {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i : Fin r) : Field S 1 :=
  fun p => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
    (angleCovector S hS C i p)

theorem angleForm_smooth {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (B : FormBundle C 1) (i : Fin r) :
    IsForm B (angleForm S hS C i) :=
  ExteriorDerivativeResults.oneForm_isForm C B _ (angleCovector_smooth S hS C i)

theorem angleForm_isCoordinateForm {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i : Fin r) :
    IsCoordinateForm C i (angleForm S hS C i) := by
  intro c hc a ε hε hε' hac p hp
  change (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p)))
    ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
      (angleCovector S hS C i p)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact angleCovector_on_chart S hS C i c hc hac p hp

/-- The chart condition fixes the descended form uniquely. -/
theorem coordinateForm_unique {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i : Fin r) (ω : Field S 1)
    (hω : IsCoordinateForm C i ω) : ω = angleForm S hS C i := by
  funext p
  obtain ⟨c, hc, hp, a, ε, hε, hε', hac⟩ := exists_angle_chart S hS p
  apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  change covectorField ω p = _
  rw [hω c hc a ε hε hε' hac p hp]
  exact (angleForm_isCoordinateForm S hS C i c hc a ε hε hε' hac p hp).symm

theorem angleForm_closed {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (i : Fin r) :
    K.D 1 (angleForm S hS C i) = 0 := by
  funext p
  obtain ⟨f, hf, he⟩ := angleCovector_locally_exact S hS C i p
  let df : Field S 1 := fun q =>
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S q))).symm (dFunction S f hf q)
  have hdf : IsForm (B 1) df :=
    ExteriorDerivativeResults.oneForm_isForm C (B 1) _ (Covectors.differential_smooth S C f hf)
  have hlocal : ∀ᶠ q in 𝓝 p, angleForm S hS C i q = df q := by
    filter_upwards [he] with q hq
    exact congrArg (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S q))).symm hq
  rw [ExteriorDerivativeResults.axioms_locality C B K.D K.axioms 1
    (angleForm S hS C i) df (angleForm_smooth S hS C (B 1) i) hdf p hlocal]
  have hz := ExteriorDerivativeResults.axioms_exact_closed C B K.D K.axioms f hf
  exact congrFun hz p

def closedAngleForm {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (i : Fin r) : K.closed 1 :=
  ⟨⟨angleForm S hS C i, (K.mem_forms 1 _).mpr (angleForm_smooth S hS C (B 1) i)⟩,
    by
      apply Subtype.ext
      exact angleForm_closed S hS C B K i⟩

end SmoothManifolds.TorusCoordinates

namespace SmoothManifolds.TorusCoordinates
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  Set Filter
open scoped Topology

section ConstantFields
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  (C : CotangentBundle S)

/-- The global parallel coframe as an actual linear equivalence. -/
def angleDualEquiv (p : FlatTorus r) : Euclidean r ≃ₗ[ℝ] CotangentFiber S p :=
  let hc := Classical.choose_spec (exists_angle_chart S hS p)
  ((Pi.basisFun ℝ (Fin r)).map
    (C.tangent.fiberCoordinates.equiv (Classical.choose (exists_angle_chart S hS p))
      hc.1 p hc.2.1).symm).dualBasis.equivFun.symm

@[simp] theorem angleDualEquiv_single (p : FlatTorus r) (i : Fin r) :
    angleDualEquiv S hS C p (Pi.single i 1) = angleCovector S hS C i p := by
  let hc := Classical.choose_spec (exists_angle_chart S hS p)
  change ((Pi.basisFun ℝ (Fin r)).map
    (C.tangent.fiberCoordinates.equiv (Classical.choose (exists_angle_chart S hS p))
      hc.1 p hc.2.1).symm).dualBasis.equivFun.symm (Pi.single i 1) = _
  rw [show ((Pi.basisFun ℝ (Fin r)).map
    (C.tangent.fiberCoordinates.equiv (Classical.choose (exists_angle_chart S hS p))
      hc.1 p hc.2.1).symm).dualBasis.equivFun.symm (Pi.single i 1) =
      ((Pi.basisFun ℝ (Fin r)).map
        (C.tangent.fiberCoordinates.equiv (Classical.choose (exists_angle_chart S hS p))
          hc.1 p hc.2.1).symm).dualBasis i by simp [Basis.equivFun_symm_apply]]
  exact ExteriorAlgebraResults.coordinate_dualBasis C.tangent.fiberCoordinates
    (Classical.choose (exists_angle_chart S hS p)) hc.1 p hc.2.1 i

theorem angleDualEquiv_expansion (p : FlatTorus r) (a : Euclidean r) :
    angleDualEquiv S hS C p a = ∑ i : Fin r, a i • angleCovector S hS C i p := by
  classical
  have ha : a = ∑ i : Fin r, a i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [ha, map_sum]
  simp only [map_smul, angleDualEquiv_single]

def constantField (k : ℕ) : ExteriorModel r k →ₗ[ℝ] Field S k where
  toFun x p := exteriorPower.map k (angleDualEquiv S hS C p).toLinearMap x
  map_add' x y := by funext p; exact map_add _ x y
  map_smul' c x := by funext p; exact map_smul _ c x

@[simp] theorem constantField_wedge (k l : ℕ) (x : ExteriorModel r k) (y : ExteriorModel r l) :
    constantField S hS C (k+l) (exteriorPower.wedge ℝ (Euclidean r) k l x y) =
      fieldWedge (constantField S hS C k x) (constantField S hS C l y) := by
  funext p
  exact ExteriorAlgebraResults.map_wedge (angleDualEquiv S hS C p).toLinearMap x y

@[simp] theorem constantField_one :
    constantField S hS C 0 ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1) =
      FormPullbackData.scalarField S (fun _ => 1) := by
  funext p
  apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  have ht := LinearMap.congr_fun
    (exteriorPower.zeroEquiv_naturality (R := ℝ) (angleDualEquiv S hS C p).toLinearMap)
    ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1)
  simpa [constantField, FormPullbackData.scalarField] using ht

@[simp] theorem constantField_generator (i : Fin r) :
    constantField S hS C 1
      ((exteriorPower.oneEquiv ℝ (Euclidean r)).symm (Pi.single i 1)) =
      angleForm S hS C i := by
  funext p
  apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  have ht := LinearMap.congr_fun
    (exteriorPower.oneEquiv_naturality (R := ℝ) (angleDualEquiv S hS C p).toLinearMap)
    ((exteriorPower.oneEquiv ℝ (Euclidean r)).symm (Pi.single i 1))
  simpa only [constantField, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, angleDualEquiv_single,
    angleForm] using ht

end ConstantFields
end SmoothManifolds.TorusCoordinates

namespace SmoothManifolds.TorusCoordinates
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  Set Filter
open scoped Topology

/-- Wedges of arbitrary closed one-forms are closed smooth forms. -/
theorem closed_oneForm_wedges {r : ℕ}
    {S : SmoothManifold r .euclidean (FlatTorus r)}
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (k : ℕ) (α : Fin k → CovectorField S)
    (hα : ∀ i, IsForm (B 1) (fun p =>
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (α i p)))
    (hDα : ∀ i, K.D 1 (fun p =>
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (α i p)) = 0) :
    IsForm (B k) (fun p => exteriorPower.ιMulti ℝ k (fun i => α i p)) ∧
    K.D k (fun p => exteriorPower.ιMulti ℝ k (fun i => α i p)) = 0 := by
  induction k with
  | zero =>
      have heq : (fun p => exteriorPower.ιMulti ℝ 0 (fun i => α i p)) =
          FormPullbackData.scalarField S (fun _ => 1) := by
        funext p
        apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
        simp [FormPullbackData.scalarField]
      rw [heq]
      exact ⟨ExteriorDerivativeResults.scalarField_form C (B 0) _
        (scalarContDiff_const ⊤ _ 1),
        ExteriorDerivativeResults.axioms_constant C B K.D K.axioms 1⟩
  | succ k ih =>
      let β : Field S k := fun p => exteriorPower.ιMulti ℝ k
        (fun i => α i.castSucc p)
      let γ : Field S 1 := fun p =>
        (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (α (Fin.last k) p)
      have hβ := ih (fun i => α i.castSucc) (fun i => hα i.castSucc) (fun i => hDα i.castSucc)
      have hβD : K.D k β = 0 := hβ.2
      have hγ : IsForm (B 1) γ := hα (Fin.last k)
      have hγD : K.D 1 γ = 0 := hDα (Fin.last k)
      have heq : fieldWedge β γ =
          (fun p => exteriorPower.ιMulti ℝ (k+1) (fun i => α i p)) := by
        funext p
        apply Subtype.ext
        change ExteriorAlgebra.ιMulti ℝ k (fun i => α i.castSucc p) *
          ExteriorAlgebra.ιMulti ℝ 1 (fun _ => α (Fin.last k) p) = _
        rw [ExteriorAlgebra.ιMulti_mul_ιMulti, Fin.append_right_eq_snoc]
        congr 1
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp
      rw [← heq]
      refine ⟨ExteriorAlgebraResults.wedge_smooth C k 1 (B k) (B 1) (B (k+1)) β γ hβ.1 hγ, ?_⟩
      funext p
      apply Subtype.val_injective
      have hh := K.axioms.leibniz k 1 β γ hβ.1 hγ p
      simpa only [hβD, hγD, Pi.zero_apply, map_zero, LinearMap.zero_apply,
        ZeroMemClass.coe_zero, smul_zero, add_zero] using hh

section ClosedConstantFields
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)

/-- A general constant linear combination of the closed coordinate forms. -/
def angleLinearOne (a : Euclidean r) : K.closed 1 :=
  ∑ i : Fin r, a i • closedAngleForm S hS C B K i

theorem angleLinearOne_field (a : Euclidean r) (p : FlatTorus r) :
    (angleLinearOne S hS C B K a).val.val p =
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
        (angleDualEquiv S hS C p a) := by
  classical
  rw [angleDualEquiv_expansion, map_sum]
  simp [angleLinearOne, closedAngleForm, angleForm]

/-- Every decomposable constant exterior field is smooth and closed. -/
theorem constantField_ιMulti_closed (k : ℕ) (a : Fin k → Euclidean r) :
    IsForm (B k) (constantField S hS C k (exteriorPower.ιMulti ℝ k a)) ∧
      K.D k (constantField S hS C k (exteriorPower.ιMulti ℝ k a)) = 0 := by
  have heq : constantField S hS C k (exteriorPower.ιMulti ℝ k a) =
      fun p => exteriorPower.ιMulti ℝ k (fun i => angleDualEquiv S hS C p (a i)) := by
    funext p
    exact exteriorPower.map_apply_ιMulti _ _
  rw [heq]
  apply closed_oneForm_wedges C B K k
  · intro i
    have he : (fun p =>
        (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (angleDualEquiv S hS C p (a i))) = (angleLinearOne S hS C B K (a i)).val.val := by
      funext p
      exact (angleLinearOne_field S hS C B K (a i) p).symm
    rw [he]
    exact (K.mem_forms 1 _).mp (angleLinearOne S hS C B K (a i)).val.property
  · intro i
    have he : (fun p =>
        (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (angleDualEquiv S hS C p (a i))) = (angleLinearOne S hS C B K (a i)).val.val := by
      funext p
      exact (angleLinearOne_field S hS C B K (a i) p).symm
    rw [he]
    exact congrArg Subtype.val (angleLinearOne S hS C B K (a i)).property

end ClosedConstantFields
end SmoothManifolds.TorusCoordinates

namespace SmoothManifolds.TorusCoordinates
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  Set Filter
open scoped Topology
section ConstantInclusion
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)

/-- All constant parallel exterior fields are actual closed smooth forms. -/
theorem constantField_exists_closed (k : ℕ) (x : ExteriorModel r k) :
    ∃ ω : K.closed k, ω.val.val = constantField S hS C k x := by
  let V : Submodule ℝ (ExteriorModel r k) :=
    ((K.closed k).map (K.forms k).subtype).comap (constantField S hS C k)
  have ht : V = ⊤ := by
    apply top_unique
    rw [← exteriorPower.ιMulti_span ℝ k (Euclidean r)]
    apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    obtain ⟨hs, hD⟩ := constantField_ιMulti_closed S hS C B K k a
    let η : K.forms k := ⟨constantField S hS C k (exteriorPower.ιMulti ℝ k a),
      (K.mem_forms k _).mpr hs⟩
    have hη : η ∈ K.closed k := by
      change K.d k η = 0
      apply Subtype.ext
      exact hD
    exact ⟨η, hη, rfl⟩
  have hx : x ∈ V := by rw [ht]; trivial
  obtain ⟨η, hη, hfield⟩ := hx
  exact ⟨⟨η, hη⟩, hfield⟩

/-- The canonical inclusion of the exterior algebra into the de Rham complex. -/
def constantClosed (k : ℕ) : ExteriorModel r k →ₗ[ℝ] K.closed k where
  toFun x := Classical.choose (constantField_exists_closed S hS C B K k x)
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    have hx := Classical.choose_spec (constantField_exists_closed S hS C B K k x)
    have hy := Classical.choose_spec (constantField_exists_closed S hS C B K k y)
    have hxy := Classical.choose_spec (constantField_exists_closed S hS C B K k (x+y))
    exact hxy.trans ((map_add (constantField S hS C k) x y).trans
      (congrArg₂ (· + ·) hx.symm hy.symm))
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    have hx := Classical.choose_spec (constantField_exists_closed S hS C B K k x)
    have hax := Classical.choose_spec (constantField_exists_closed S hS C B K k (a • x))
    exact hax.trans ((map_smul (constantField S hS C k) a x).trans
      (congrArg (a • ·) hx.symm))

@[simp] theorem constantClosed_field (k : ℕ) (x : ExteriorModel r k) :
    (constantClosed S hS C B K k x).val.val = constantField S hS C k x :=
  Classical.choose_spec (constantField_exists_closed S hS C B K k x)

@[simp] theorem constantClosed_generator (i : Fin r) :
    constantClosed S hS C B K 1
      ((exteriorPower.oneEquiv ℝ (Euclidean r)).symm (Pi.single i 1)) =
      closedAngleForm S hS C B K i := by
  apply Subtype.ext
  apply Subtype.ext
  rw [constantClosed_field, constantField_generator]
  rfl

end ConstantInclusion
end SmoothManifolds.TorusCoordinates

namespace SmoothManifolds.TorusCoordinates
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  Set Filter
open scoped Topology
section FiberCoordinates
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  (C : CotangentBundle S)

/-- In every angle chart the global coframe is the actual coordinate coframe. -/
theorem angleDualEquiv_on_chart
    (c : ModelChart r .euclidean (FlatTorus r)) (hc : c ∈ S.smoothStructure.val)
    {a : Euclidean r} {ε : ℝ} (hac : IsAngleChart a ε c)
    (p : FlatTorus r) (hp : p ∈ c.source) :
    angleDualEquiv S hS C p = ((Pi.basisFun ℝ (Fin r)).map
      (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.equivFun.symm := by
  classical
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℝ (Fin r)).ext
  intro i
  simp only [Pi.basisFun_apply]
  change angleDualEquiv S hS C p (Pi.single i 1) = _
  rw [angleDualEquiv_single]
  calc
    angleCovector S hS C i p = coordinateCovector C.tangent.fiberCoordinates c hc p hp i :=
      angleCovector_on_chart S hS C i c hc hac p hp
    _ = ((Pi.basisFun ℝ (Fin r)).map
        (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis i :=
      (ExteriorAlgebraResults.coordinate_dualBasis C.tangent.fiberCoordinates c hc p hp i).symm
    _ = ((Pi.basisFun ℝ (Fin r)).map
        (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.equivFun.symm
          (Pi.single i 1) := by simp [Basis.equivFun_symm_apply]

/-- The parallel coframe trivializes every actual exterior fiber. -/
def flatExteriorEquiv (k : ℕ) (p : FlatTorus r) :
    ExteriorModel r k ≃ₗ[ℝ] Fiber (TangentSpace S p) k :=
  BundleOperations.exteriorEquiv k (angleDualEquiv S hS C p)

@[simp] theorem flatExteriorEquiv_apply (k : ℕ) (p : FlatTorus r) (x : ExteriorModel r k) :
    flatExteriorEquiv S hS C k p x = constantField S hS C k x p := rfl

/-- The parallel coefficient field of an arbitrary intrinsic exterior field. -/
def parallelCoefficients (k : ℕ) : Field S k →ₗ[ℝ] (FlatTorus r → ExteriorModel r k) where
  toFun ω p := (flatExteriorEquiv S hS C k p).symm (ω p)
  map_add' ω η := by funext p; exact map_add _ _ _
  map_smul' a ω := by
    funext p
    exact (flatExteriorEquiv S hS C k p).symm.map_smul a (ω p)

@[simp] theorem parallelCoefficients_constantField (k : ℕ) (x : ExteriorModel r k) :
    parallelCoefficients S hS C k (constantField S hS C k x) = fun _ => x := by
  funext p
  exact (flatExteriorEquiv S hS C k p).symm_apply_apply x

theorem field_eq_parallel_synthesis (k : ℕ) (ω : Field S k) (p : FlatTorus r) :
    ω p = flatExteriorEquiv S hS C k p (parallelCoefficients S hS C k ω p) :=
  ((flatExteriorEquiv S hS C k p).apply_symm_apply (ω p)).symm

@[simp] theorem constantField_injective (k : ℕ) :
    Function.Injective (constantField S hS C k) := by
  intro x y hxy
  exact (flatExteriorEquiv S hS C k 0).injective (congrFun hxy 0)

theorem field_constant_iff_parallelCoefficients (k : ℕ) (ω : Field S k)
    (x : ExteriorModel r k) :
    ω = constantField S hS C k x ↔ parallelCoefficients S hS C k ω = fun _ => x := by
  constructor
  · rintro rfl
    exact parallelCoefficients_constantField S hS C k x
  · intro h
    funext p
    rw [field_eq_parallel_synthesis S hS C k ω p]
    exact congrArg (flatExteriorEquiv S hS C k p) (congrFun h p)

end FiberCoordinates
end SmoothManifolds.TorusCoordinates


namespace SmoothManifolds.TorusLoopPeriods
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData SphereTorusData TorusDeRhamData PathIntegrationData Set Filter
open scoped Topology

lemma loopLine_contDiff {r : ℕ} (j : Fin r) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun h : ℝ => (Pi.single j (t+h) : Euclidean r)) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = j
  · subst i; simpa using contDiff_const.add contDiff_id
  · simpa [Pi.single_apply, hi] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℝ)))

lemma loop_continuous {r : ℕ} (j : Fin r) : Continuous (coordinateLoop j) := by
  apply (SphereTorus.quotientProjection_isOpenQuotientMap r).continuous.comp
  simpa only [zero_add] using (loopLine_contDiff j 0).continuous

lemma loop_lift {r : ℕ} (j : Fin r) (t : ℝ) (ε : ℝ) (hε : 0 < ε)
    (c : ModelChart r .euclidean (FlatTorus r))
    (hc : IsAngleChart (Pi.single j t) ε c) :
    coordinateLoop j t ∈ c.source ∧
      (fun h : ℝ => (c (coordinateLoop j (t+h))).val) =ᶠ[𝓝 0]
        (fun h : ℝ => (Pi.single j (t+h) : Euclidean r)) := by
  have hcenter : (Pi.single j t : Euclidean r) ∈ angleBox (Pi.single j t) ε :=
    SphereTorus.mem_angleBox_center _ hε
  constructor
  · rw [hc.1]
    exact ⟨Pi.single j t, hcenter, rfl⟩
  · have hevent : ∀ᶠ h : ℝ in 𝓝 0,
        (Pi.single j (t+h) : Euclidean r) ∈ angleBox (Pi.single j t) ε := by
      apply (loopLine_contDiff j t).continuous.continuousAt.preimage_mem_nhds
      simpa only [add_zero] using (SphereTorus.isOpen_angleBox (Pi.single j t) ε).mem_nhds hcenter
    filter_upwards [hevent] with h hh
    exact hc.2.2.1 _ hh

lemma loop_curveSmooth {r : ℕ} (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (j : Fin r) (t : ℝ) (side : CurveSide) :
    CurveSmoothAt S (coordinateLoop j t) side (fun h => coordinateLoop j (t+h)) := by
  let c := SphereTorus.angleChart (Pi.single j t) (1/8) (by norm_num)
  have hc : IsAngleChart (Pi.single j t) (1/8) c := SphereTorus.angleChart_spec _ _ _
  have hcS : c ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas r)
      ⟨Pi.single j t, 1/8, by norm_num, by norm_num, hc⟩
  obtain ⟨hp, hlift⟩ := loop_lift j t (1/8) (by norm_num) c hc
  have hcont : Continuous (fun h : ℝ => coordinateLoop j (t+h)) :=
    (loop_continuous j).comp (continuous_const.add continuous_id)
  have htend : Tendsto (fun h : ℝ => coordinateLoop j (t+h))
      (𝓝[curveParameterSet side] 0) (𝓝 (coordinateLoop j t)) := by
    simpa only [add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  refine ⟨by simp, hcont.continuousAt.continuousWithinAt, ?_⟩
  intro d hd hpd
  have hcompat := S.smoothStructure.property.1.2 c hcS d hd
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := chartContDiffAt_of_compatible hcompat hp hpd
  let L : ℝ → Euclidean r := fun h => Pi.single j (t+h)
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := loopLine_contDiff j t
  have hL0 : L 0 = (c (coordinateLoop j t)).val := by
    simpa only [L, add_zero] using hlift.eq_of_nhds.symm
  refine ⟨L ⁻¹' U, hU.preimage hL.continuous, ?_, F ∘ L,
    hF.comp hL.contDiffOn (fun _ hh => hh), ?_⟩
  · change L 0 ∈ U
    rwa [hL0]
  · exact (heF.comp_tendsto htend).symm.trans
      ((hlift.filter_mono nhdsWithin_le_nhds).fun_comp F)

lemma loop_piecewiseSmooth {r : ℕ} (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (j : Fin r) : PiecewiseSmoothOn S (coordinateLoop j) 0 1 := by
  have hs : SmoothOnInterval S (coordinateLoop j) 0 1 := by
    exact ⟨by norm_num, (loop_continuous j).continuousOn,
      fun t _ _ => loop_curveSmooth S hS j t _⟩
  refine ⟨by norm_num, (loop_continuous j).continuousOn, ?_⟩
  let s : Subdivision 0 1 := {
    count := 1
    point := fun i => (i : ℝ)
    first := by simp
    last := by simp
    increasing := by
      intro a _ b _ hab
      change (a : ℝ) < (b : ℝ)
      exact_mod_cast hab }
  refine ⟨s, ?_⟩
  intro i hi
  have hi0 : i = 0 := by change i < 1 at hi; omega
  subst i
  simpa [s] using hs

lemma loop_coefficient {r : ℕ} (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i j : Fin r) (ω : Field S 1)
    (hω : IsCoordinateForm C i ω) (t : ℝ) :
    coefficient S (covectorField ω) (coordinateLoop j) t = if i = j then 1 else 0 := by
  classical
  let c := SphereTorus.angleChart (Pi.single j t) (1/8) (by norm_num)
  have hc : IsAngleChart (Pi.single j t) (1/8) c := SphereTorus.angleChart_spec _ _ _
  have hcS : c ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas r)
      ⟨Pi.single j t, 1/8, by norm_num, by norm_num, hc⟩
  obtain ⟨hp, hlift⟩ := loop_lift j t (1/8) (by norm_num) c hc
  obtain ⟨xs, hxs, hx⟩ := C.tangent.fiberCoordinates.isCoordinates c hcS _ hp
  rw [coefficient, hω c hcS _ (1/8) (by norm_num) (by norm_num) hc _ hp]
  change C.tangent.fiberCoordinates.equiv c hcS _ hp (velocity S (coordinateLoop j) .twoSided t) i = _
  rw [hx]
  have hdL : HasDerivAt (fun h : ℝ => (Pi.single j (t+h) : Euclidean r))
      (Pi.single j 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro a
    by_cases ha : a = j
    · subst a
      simpa using (hasDerivAt_id (0 : ℝ)).const_add t
    · simpa [Pi.single_apply, ha] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hd : HasDerivAt (fun h : ℝ => (c (coordinateLoop j (t+h))).val i)
      ((Pi.single j 1 : Euclidean r) i) 0 :=
    (hasDerivAt_pi.mp (hdL.congr_of_eventuallyEq hlift) i)
  have hrep := (PathIntegration.velocity_spec S (coordinateLoop j) .twoSided t
    (loop_curveSmooth S hS j t .twoSided)).2 (xs i) (fun p => (c p).val i) (hxs i).symm
  have hder : HasDerivAt (fun h => (c (coordinateLoop j (t+h))).val i)
      ((velocity S (coordinateLoop j) .twoSided t).val (xs i)) 0 := by
    change HasDerivWithinAt (fun h => (c (coordinateLoop j (t+h))).val i)
      ((velocity S (coordinateLoop j) .twoSided t).val (xs i)) univ 0 at hrep
    exact hrep.hasDerivAt (by simp)
  rw [hder.unique hd]
  simp [Pi.single_apply]

lemma loop_period {r : ℕ} (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (i j : Fin r) (ω : Field S 1)
    (hω : IsCoordinateForm C i ω) :
    pathIntegral S (covectorField ω) (coordinateLoop j) 0 1 = if i = j then 1 else 0 := by
  classical
  unfold pathIntegral
  simp_rw [loop_coefficient S hS C i j ω hω]
  simp

open private zeroCoefficient zeroCoefficient_smooth from MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra

lemma exactForm_period_zero {r : ℕ} (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (η : K.forms 0) (j : Fin r) :
    pathIntegral S (covectorField (K.d 0 η).val) (coordinateLoop j) 0 1 = 0 := by
  let f := zeroCoefficient η.val
  have hf : PartitionData.ScalarSmooth S.smoothStructure.val f :=
    zeroCoefficient_smooth η.val ((K.mem_forms _ _).mp η.property)
  have hη : FormPullbackData.scalarField S f = η.val := by
    funext p
    exact (exteriorPower.zeroEquiv ℝ _).symm_apply_apply _
  have hdf : covectorField (K.d 0 η).val = dFunction S f hf := by
    funext p
    change exteriorPower.oneEquiv ℝ _ (K.D 0 η.val p) = _
    rw [← hη, K.axioms.function_rule f hf p, LinearEquiv.apply_symm_apply]
  rw [hdf, PathIntegration.integral_dFunction S f hf _ 0 1
    (loop_piecewiseSmooth S hS j)]
  have hclosed : coordinateLoop j 0 = coordinateLoop j 1 := by
    classical
    funext i
    by_cases h : i = j
    · subst i
      simp [coordinateLoop, SphereTorusData.quotientProjection, AddCircle.coe_period]
    · simp [coordinateLoop, SphereTorusData.quotientProjection, Pi.single_apply, h]
  rw [hclosed, sub_self]

/-- Evaluation of the canonical path integrand is linear in a closed one-form. -/
def closedCoefficient {r : ℕ} {S : SmoothManifold r .euclidean (FlatTorus r)}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (γ : ℝ → FlatTorus r) (t : ℝ) : K.closed 1 →ₗ[ℝ] ℝ :=
  (Module.Dual.eval ℝ (TangentSpace S (γ t)) (velocity S γ .twoSided t)).comp
    ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S (γ t)))).toLinearMap.comp
      ((LinearMap.proj (γ t)).comp ((K.forms 1).subtype.comp (K.closed 1).subtype)))

lemma coordinateClasses_relation {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (θ : Fin r → K.closed 1) (hθ : ∀ i, IsCoordinateForm C i (θ i).val.val)
    (c : Euclidean r) (hrel : ∑ i, c i • K.classOf 1 (θ i) = 0) :
    ∀ j, c j = 0 := by
  classical
  let ω : K.closed 1 := ∑ i, c i • θ i
  have hclass : K.classOf 1 ω = 0 := by
    simpa only [ω, map_sum, map_smul] using hrel
  have hex := (DeRhamResults.class_zero_iff_exact K 1 ω).mp hclass
  obtain ⟨η, hη⟩ := hex
  intro j
  have hzero : pathIntegral S (covectorField ω.val.val) (coordinateLoop j) 0 1 = 0 := by
    rw [← hη]
    exact exactForm_period_zero S hS K η j
  have hc : ∀ t, coefficient S (covectorField ω.val.val) (coordinateLoop j) t = c j := by
    intro t
    change closedCoefficient K (coordinateLoop j) t ω = c j
    dsimp only [ω]
    rw [map_sum]
    simp_rw [map_smul]
    change (∑ i, c i • coefficient S (covectorField (θ i).val.val) (coordinateLoop j) t) = _
    simp_rw [loop_coefficient S hS C _ j _ (hθ _) t]
    simp
  rw [pathIntegral] at hzero
  simp_rw [hc] at hzero
  simpa using hzero

lemma coordinateClasses_linearIndependent {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (θ : Fin r → K.closed 1) (hθ : ∀ i, IsCoordinateForm C i (θ i).val.val) :
    LinearIndependent ℝ (fun i => K.classOf 1 (θ i)) := by
  apply Fintype.linearIndependent_iff.mpr
  exact coordinateClasses_relation S hS K θ hθ

def coordinateClassMap {r : ℕ} {S : SmoothManifold r .euclidean (FlatTorus r)}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (θ : Fin r → K.closed 1) : Euclidean r →ₗ[ℝ] K.Cohomology 1 :=
  Fintype.linearCombination ℝ (fun i => K.classOf 1 (θ i))

lemma coordinateClassMap_injective {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (θ : Fin r → K.closed 1) (hθ : ∀ i, IsCoordinateForm C i (θ i).val.val) :
    Function.Injective (coordinateClassMap K θ) :=
  (coordinateClasses_linearIndependent S hS K θ hθ).fintypeLinearCombination_injective

end SmoothManifolds.TorusLoopPeriods


namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData SphereTorusData TorusDeRhamData PathIntegrationData

/-- The actual normalized closed coordinate forms on every standard torus. -/
theorem normalized_coordinate_forms (r : ℕ)
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    ∃ θ : Fin r → K.closed 1,
      (∀ i, IsCoordinateForm C i (θ i).val.val) ∧
      (∀ j : Fin r, PiecewiseSmoothOn S (coordinateLoop j) 0 1) ∧
      (∀ j : Fin r, coordinateLoop j 0 = coordinateLoop j 1) ∧
      ∀ i j : Fin r, pathIntegral S (covectorField (θ i).val.val) (coordinateLoop j) 0 1 =
        if i = j then 1 else 0 := by
  let θ := TorusCoordinates.closedAngleForm S hS C B K
  have hθ : ∀ i, IsCoordinateForm C i (θ i).val.val :=
    TorusCoordinates.angleForm_isCoordinateForm S hS C
  exact ⟨θ, hθ, TorusLoopPeriods.loop_piecewiseSmooth S hS,
    coordinateLoop_closed, fun i j => TorusLoopPeriods.loop_period S hS C i j _ (hθ i)⟩

end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData DeRhamData HomotopyData HomotopyIntegration
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- Every horizontal pullback family has jointly smooth coefficients. -/
theorem alpha_jointSmooth (hF : IsSmoothHomotopy S T F)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (D : HomotopyDifferentials S T F) {k : ℕ} (ω : Field T k)
    (B : FormBundle A k) (hω : IsForm B ω) :
    JointSmoothCoefficients C k (fun t => alpha D ω t) := by
  intro c hc I q
  obtain ⟨U, hU, hqU, G, hG, he⟩ :=
    alpha_coefficients_locally_smooth hF C A D ω B hω c hc q
  refine ⟨U, hU, hqU, (fun x => G x I), ?_, ?_⟩
  · exact contDiffOn_pi.mp hG I
  · intro y hy
    exact congrFun (he y hy) I

/-- The affine weight in time preserves the actual joint coefficient
smoothness convention, including at the time endpoints. -/
theorem jointSmooth_weighted {C : CotangentBundle S} {k : ℕ}
    (f : UnitInterval → Field S k) (hf : JointSmoothCoefficients C k f) :
    JointSmoothCoefficients C k (fun t => (1-t.val) • f t) := by
  intro c hc I q
  obtain ⟨U, hU, hqU, G, hG, he⟩ := hf c hc I q
  refine ⟨U, hU, hqU, (fun x => (1-x (Fin.last n)) * G x), ?_, ?_⟩
  · exact (contDiffOn_const.sub
      (contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) (Fin.last n)).contDiffOn).mul hG
  · intro y hy
    dsimp only
    rw [Fin.snoc_last, he y hy]
    simp only [coefficients, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]

end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusAveraging
open Set MeasureTheory

/-- The weighted homotopy formula giving averaging minus the identity from
one translation isotopy. No integration in a cohomology quotient occurs. -/
theorem weighted_derivative_integral (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1))
    (hg : IntervalIntegrable g volume 0 1)
    (hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g t) t) :
    (∫ t in (0 : ℝ)..1, (1-t) * g t) = (∫ t in (0 : ℝ)..1, f t) - f 0 := by
  have hh : ∫ t in (0 : ℝ)..1, (1-t) * g t =
      (1-(1:ℝ))*f 1 - (1-(0:ℝ))*f 0 - ∫ t in (0:ℝ)..1, (-1:ℝ)*f t := by
    apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    · exact (continuous_const.sub continuous_id).continuousOn
    · simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hf
    · intro t ht
      simpa only [Pi.sub_apply, id_eq, zero_sub] using
        (hasDerivAt_id t).const_sub (1:ℝ)
    · simpa using hder
    · exact intervalIntegrable_const
    · exact hg
  simpa [intervalIntegral.integral_neg, sub_eq_add_neg, add_comm] using hh
end SmoothManifolds.TorusAveraging


namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData DeRhamData HomotopyData HomotopyIntegration
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- One smooth homotopy gives an actual primitive of its averaged pullback
minus its initial pullback. The affine time weight avoids choosing a separate
homotopy operator for each translation parameter. -/
theorem averaged_pullback_difference_exact
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hF : IsSmoothHomotopy S T F) (D : HomotopyDifferentials S T F)
    (k : ℕ) (ω : J.closed (k+1)) :
    ∃ η : K.forms k,
      (K.d k η).val =
        integralField C (k+1) (fun t => alpha D ω.val.val (intervalTime t)) -
          alpha D ω.val.val initialTime := by
  have hω : IsForm (E (k+1)) ω.val.val := (J.mem_forms _ _).mp ω.val.property
  let β : UnitInterval → Field S k := fun t => beta C D ω.val.val t
  have hβ : JointSmoothCoefficients C k β := beta_jointSmooth hF C A D ω.val.val (E (k+1)) hω
  let weightedβ : UnitInterval → Field S k := fun t => (1-t.val) • β t
  have hwβ : JointSmoothCoefficients C k weightedβ := jointSmooth_weighted β hβ
  let η : K.forms k := ⟨integralField C k (fun t => weightedβ (intervalTime t)),
    (K.mem_forms k _).mpr (isForm_integralField_of_jointSmooth C k (B k) weightedβ hwβ)⟩
  refine ⟨η, ?_⟩
  change K.D k (integralField C k (fun t => weightedβ (intervalTime t))) = _
  rw [derivative_integralField K k weightedβ hwβ]
  apply HomotopyResults.field_eq_of_coefficients C
  intro c hc p I
  have hα : JointSmoothCoefficients C (k+1) (fun t => alpha D ω.val.val t) :=
    alpha_jointSmooth hF C A D ω.val.val (E (k+1)) hω
  rw [coefficients_integralField C (k+1) _
    (jointSmooth_derivative_coefficientsIntervalIntegrable K k weightedβ hwβ)]
  have hcoeffsub (f g : Field S (k+1)) : coefficients C (k+1) c hc (f-g) p I =
      coefficients C (k+1) c hc f p I - coefficients C (k+1) c hc g p I := by
    simp only [coefficients, Pi.sub_apply, map_sub, Finsupp.sub_apply]
  rw [hcoeffsub, coefficients_integralField C (k+1) _
    (jointSmooth_coefficientsIntervalIntegrable C (k+1) _ hα)]
  let f : ℝ → ℝ := fun t => coefficients C (k+1) c hc (alpha D ω.val.val (intervalTime t)) p I
  let g : ℝ → ℝ := fun t => coefficients C (k+1) c hc (K.D k (β (intervalTime t))) p I
  have hfg : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (g t) t := by
    intro t ht
    let q : UnitInterval := ⟨t, ht.1.le, ht.2.le⟩
    have hq : intervalTime t = q := HomotopyData.intervalTime_coe q
    have hβform : IsForm (B k) (β q) := jointSmooth_isForm C k (B k) β hβ q
    have hdω : J.d (k+1) ω.val = 0 := ω.property
    have hzero : (J.d (k+1) ω.val).val = 0 := congrArg Subtype.val hdω
    have hβzero : beta C D (J.d (k+1) ω.val).val q = 0 := by
      rw [hzero]
      simpa only [zero_smul] using
        (HomotopyResults.beta_smul C D (k := k+1) 0 (0 : Field T (k+2)) q)
    have hd := positive_coefficient_relation hF C A D ω.val.val
      (J.d (k+1) ω.val).val (E (k+1)) hω (J.coordinates _ _ hω)
      c hc p q ht (K.D k (β q)) (K.coordinates _ _ hβform) I
    rw [hβzero] at hd
    simpa only [coefficients, Pi.zero_apply, map_zero, Finsupp.zero_apply, add_zero,
      f, g, hq] using hd
  have hfi : ContinuousOn f (Set.Icc 0 1) :=
    alpha_coefficients_continuousOn hF C A D ω.val.val (E (k+1)) hω c hc p I
  have hgi : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    jointSmooth_derivative_coefficientsIntervalIntegrable K k β hβ c hc p I
  have hw : ∫ t in (0:ℝ)..1,
      coefficients C (k+1) c hc (K.D k (weightedβ (intervalTime t))) p I =
      ∫ t in (0:ℝ)..1, (1-t) * g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa using ht
    have hclamp : (intervalTime t).val = t := by
      exact congrArg Subtype.val (HomotopyData.intervalTime_coe ⟨t,ht'⟩)
    change coefficients C (k+1) c hc (K.D k ((1-(intervalTime t).val) • β (intervalTime t))) p I = _
    rw [K.axioms.smul k _ _ (jointSmooth_isForm C k (B k) β hβ (intervalTime t))]
    simp only [coefficients, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
      g, hclamp]
  rw [hw, TorusAveraging.weighted_derivative_integral f g hfi hgi hfg]
  congr 1
  exact congrArg (fun t => coefficients C (k+1) c hc (alpha D ω.val.val t) p I)
    (HomotopyData.intervalTime_coe initialTime)

end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData DeRhamData HomotopyData HomotopyIntegration
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- The degree-zero part of the averaging homotopy fixes every closed function,
with equality before passing to cohomology. -/
theorem averaged_pullback_degreeZero
    (C : CotangentBundle S) {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (hF : IsSmoothHomotopy S T F)
    (D : HomotopyDifferentials S T F) (ω : J.closed 0) :
    integralField C 0 (fun t => alpha D ω.val.val (intervalTime t)) =
      alpha D ω.val.val initialTime := by
  apply HomotopyResults.field_eq_of_coefficients C
  intro c hc p I
  have hω : IsForm (E 0) ω.val.val := (J.mem_forms _ _).mp ω.val.property
  have hα : JointSmoothCoefficients C 0 (fun t => alpha D ω.val.val t) :=
    alpha_jointSmooth hF C A D ω.val.val (E 0) hω
  rw [coefficients_integralField C 0 _
    (jointSmooth_coefficientsIntervalIntegrable C 0 _ hα)]
  let f : ℝ → ℝ := fun t => coefficients C 0 c hc (alpha D ω.val.val (intervalTime t)) p I
  have hrel := HomotopyResults.degreeZero_coefficient_relation (C := C) J hF D ω.val c hc p I
  have hdω : J.d 0 ω.val = 0 := ω.property
  have hzero : (J.d 0 ω.val).val = 0 := congrArg Subtype.val hdω
  have hβzero (t : UnitInterval) : beta C D (0 : Field T 1) t = 0 := by
    simpa only [zero_smul] using (HomotopyResults.beta_smul C D (k := 0) 0 (0 : Field T 1) t)
  have hder : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f 0 t := by
    intro t ht
    have hdt := hrel.2 t ht
    rw [hzero, hβzero] at hdt
    simpa only [coefficients, Pi.zero_apply, map_zero, Finsupp.zero_apply, f] using hdt
  have hmean := TorusAveraging.weighted_derivative_integral f (fun _ => 0)
    hrel.1 intervalIntegrable_const hder
  simp only [mul_zero, intervalIntegral.integral_zero] at hmean
  calc
    _ = f 0 := sub_eq_zero.mp hmean.symm
    _ = _ := congrArg (fun t => coefficients C 0 c hc (alpha D ω.val.val t) p I)
      (HomotopyData.intervalTime_coe initialTime)
end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData DeRhamData HomotopyData DifferentialData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem pullback_eq_self_of_eq_id (f : M → M) (hf : f = id)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace S (f p))
    (hL : ∀ p, IsDifferential S S f p (L p)) (k : ℕ) (ω : Field S k) :
    FormPullbackData.pullbackField S S f L ω = ω := by
  subst f
  exact FormPullbackResults.pullback_id S L hL k ω

theorem alpha_eq_self_of_slice_eq_id {F : M × UnitInterval → M}
    (D : HomotopyDifferentials S S F) (t : UnitInterval)
    (h : (fun p => F (p,t)) = id) {k : ℕ} (ω : Field S k) :
    alpha D ω t = ω :=
  pullback_eq_self_of_eq_id (fun p => F (p,t)) h (D.spatial t) (D.spatial_correct t) k ω
end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData MapData HomotopyData Set Filter
open scoped Topology
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- A spatial chart transition lifts to the cylinder by preserving time. -/
theorem localCoordinateExtension_snoc
    {ι f : M → Euclidean n} {p : M} (h : LocalCoordinateExtension (⊤ : ℕ∞) ι f p)
    (t : UnitInterval) :
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun q : M × UnitInterval => Fin.snoc (ι q.1) q.2.val)
      (fun q => Fin.snoc (f q.1) q.2.val) (p,t) := by
  obtain ⟨U,hU,hpU,G,hG,he⟩ := h
  let init : Euclidean (n+1) → Euclidean n := Fin.init
  have hinit : ContDiff ℝ (⊤ : ℕ∞) init := by
    apply contDiff_pi.mpr
    intro i
    exact contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) i.castSucc
  let H : Euclidean (n+1) → Euclidean (n+1) :=
    fun z => Fin.snoc (G (init z)) (z (Fin.last n))
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H (init ⁻¹' U) := by
    apply contDiffOn_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [H, Fin.snoc_last] using
        (contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) (Fin.last n)).contDiffOn
    · simp only [H, Fin.snoc_castSucc]
      exact (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).contDiffOn.comp
        (hG.comp hinit.contDiffOn (fun _ hz => hz)) (fun _ _ => Set.mem_univ _)
  refine ⟨init ⁻¹' U, hU.preimage hinit.continuous, by simpa [init] using hpU, H, hH, ?_⟩
  have hep := he.comp_tendsto (continuous_fst.continuousAt :
    ContinuousAt (fun q : M × UnitInterval => q.1) (p,t))
  filter_upwards [hep] with q hq
  change G (ι q.1) = f q.1 at hq
  simp only [H, init, Fin.init_snoc, Fin.snoc_last, hq]

/-- A local germ criterion upgrades to the strong all-points agreement used by
IsSmoothHomotopy, because the source chart cylinder is embedded. -/
theorem isSmoothHomotopy_of_chart_germs (hF : Continuous F)
    (h : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
      (p : M) (t : UnitInterval), p ∈ c.source → F (p,t) ∈ d.source →
      LocalCoordinateExtension (⊤ : ℕ∞)
        (fun q : M × UnitInterval => Fin.snoc (c q.1).val q.2.val)
        (fun q => (d (F q)).val) (p,t)) : IsSmoothHomotopy S T F := by
  refine ⟨hF, ?_⟩
  intro c hc d hd q
  obtain ⟨U,hU,hqU,G,hG,he⟩ := h c hc d hd q.val.1 q.val.2 q.property.1 q.property.2
  obtain ⟨O,hOsub,hO,hqO⟩ := mem_nhds_iff.mp he
  obtain ⟨V,hV,hqV,hVO⟩ := HomotopyResults.cylinder_chart_neighborhood c id continuous_id
    O hO ⟨q.val.1,q.property.1⟩ q.val.2 hqO
  refine ⟨U ∩ V,hU.inter hV,⟨hqU,hqV⟩,G,hG.mono inter_subset_left,?_⟩
  intro y hy
  exact hOsub (hVO ⟨y.val.1,y.property.1⟩ y.val.2 hy.2)

/-- For a continuous homotopy it is enough to exhibit one pair of genuine
smooth charts and one ordinary coordinate germ at each point. -/
theorem isSmoothHomotopy_of_one_chart_germ (hF : Continuous F)
    (h : ∀ (p : M) (t : UnitInterval),
      ∃ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
        (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val),
        p ∈ c.source ∧ F (p,t) ∈ d.source ∧
        LocalCoordinateExtension (⊤ : ℕ∞)
          (fun q : M × UnitInterval => Fin.snoc (c q.1).val q.2.val)
          (fun q => (d (F q)).val) (p,t)) : IsSmoothHomotopy S T F := by
  apply isSmoothHomotopy_of_chart_germs hF
  intro c hc d hd p t hp hpt
  obtain ⟨e,he,f,hf,hpe,hpf,hlocal⟩ := h p t
  have hs := localCoordinateExtension_snoc
    (SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 c hc e he) hp hpe) t
  have ht := LocalCoordinateExtension.precomp
    (SmoothManifolds.chartContDiffAt_of_compatible
      (T.smoothStructure.property.1.2 f hf d hd) hpf hpt) hF.continuousAt rfl
  exact LocalCoordinateExtension.comp ht (LocalCoordinateExtension.comp hlocal hs)

end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusTranslations
open ModelData AtlasData MapData SphereTorusData Set Filter

/-- Translation in a single period-one coordinate circle. -/
def translate {r : ℕ} (j : Fin r) (s : ℝ) (p : FlatTorus r) : FlatTorus r :=
  p + SphereTorusData.quotientProjection r (Pi.single j s)

@[simp] theorem translate_zero {r : ℕ} (j : Fin r) (p : FlatTorus r) :
    translate j 0 p = p := by
  funext i
  simp [translate, SphereTorusData.quotientProjection]

theorem translate_quotient {r : ℕ} (j : Fin r) (s : ℝ) (x : Euclidean r) :
    translate j s (SphereTorusData.quotientProjection r x) =
      SphereTorusData.quotientProjection r (x + Pi.single j s) := by
  funext i
  simp [translate, SphereTorusData.quotientProjection, AddCircle.coe_add]

@[simp] theorem translate_one {r : ℕ} (j : Fin r) (p : FlatTorus r) :
    translate j 1 p = p := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [translate, SphereTorusData.quotientProjection, AddCircle.coe_period]
  · simp [translate, SphereTorusData.quotientProjection, Pi.single_apply, hi]

theorem translate_add {r : ℕ} (j : Fin r) (s t : ℝ) (p : FlatTorus r) :
    translate j (s+t) p = translate j s (translate j t p) := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [translate, SphereTorusData.quotientProjection, AddCircle.coe_add, add_assoc, add_comm s t]
  · simp [translate, SphereTorusData.quotientProjection, Pi.single_apply, hi]

theorem translate_commute {r : ℕ} (i j : Fin r) (s t : ℝ) (p : FlatTorus r) :
    translate i s (translate j t p) = translate j t (translate i s p) := by
  dsimp [translate]
  abel

theorem translate_periodic {r : ℕ} (j : Fin r) (p : FlatTorus r) :
    Function.Periodic (fun s => translate j s p) 1 := by
  intro s
  change translate j (s+1) p = translate j s p
  rw [translate_add, translate_one]

theorem translate_continuous {r : ℕ} (j : Fin r) :
    Continuous (fun z : FlatTorus r × ℝ => translate j z.2 z.1) := by
  apply continuous_fst.add
  apply (SphereTorus.quotientProjection_isOpenQuotientMap r).continuous.comp
  apply continuous_pi
  intro i
  by_cases hi : i = j
  · subst i
    simpa using (continuous_snd : Continuous (Prod.snd : FlatTorus r × ℝ → ℝ))
  · simpa [Pi.single_apply, hi] using
      (continuous_const : Continuous (fun _ : FlatTorus r × ℝ => (0 : ℝ)))

theorem translate_angleBox {r : ℕ} (j : Fin r) (s : ℝ) {a x : Euclidean r}
    {ε : ℝ} (hx : x ∈ angleBox a ε) :
    x + Pi.single j s ∈ angleBox (a + Pi.single j s) ε := by
  intro i
  simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using hx i

/-- Matched angle charts turn circle translation into its genuine affine lift. -/
theorem translate_angleChart {r : ℕ} (j : Fin r) (s : ℝ) {a : Euclidean r} {ε : ℝ}
    {c d : ModelChart r .euclidean (FlatTorus r)}
    (hc : IsAngleChart a ε c) (hd : IsAngleChart (a + Pi.single j s) ε d)
    (p : FlatTorus r) (hp : p ∈ c.source) :
    translate j s p ∈ d.source ∧
      (d (translate j s p)).val = (c p).val + Pi.single j s := by
  have hcp : (c p).val ∈ angleBox a ε := by
    have ht := c.map_source hp
    rwa [hc.2.1] at ht
  have hmove := translate_angleBox j s hcp
  have hpq := SphereTorus.angleChart_projection hc hp
  have hquot : translate j s p =
      SphereTorusData.quotientProjection r ((c p).val + Pi.single j s) := by
    rw [← hpq, translate_quotient]
    rw [hpq]
  constructor
  · rw [hd.1, hquot]
    exact ⟨_, hmove, rfl⟩
  · rw [hquot]
    exact hd.2.2.1 _ hmove

/-- Every real circle translation is smooth in the standard angle structure. -/
theorem translate_smooth {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (j : Fin r) (s : ℝ) : IsSmoothMap S S (translate j s) := by
  intro p
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 S.smoothStructure.property.1 (translate j s) p).mpr
  have hcont : Continuous (translate j s) :=
    (translate_continuous j).comp (continuous_id.prodMk continuous_const)
  obtain ⟨c, ⟨a, ε, hε, hε', hc⟩, hp⟩ := (SphereTorus.angleAtlas_isContDiffAtlas r).1 p
  let d := SphereTorus.angleChart (a + Pi.single j s) ε (by linarith : ε < 1/2)
  have hd : IsAngleChart (a + Pi.single j s) ε d := SphereTorus.angleChart_spec _ _ _
  have hcS : c ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas r)
      ⟨a, ε, hε, hε', hc⟩
  have hdS : d ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas r)
      ⟨a + Pi.single j s, ε, hε, hε', hd⟩
  refine ⟨hcont.continuousAt, c, hcS, d, hdS, hp, (translate_angleChart j s hc hd p hp).1,
    univ, isOpen_univ, mem_univ _, (fun x => x + Pi.single j s), ?_, ?_⟩
  · exact (contDiff_id.add contDiff_const).contDiffOn
  · filter_upwards [c.open_source.mem_nhds hp] with q hq
    exact (translate_angleChart j s hc hd q hq).2.symm

end SmoothManifolds.TorusTranslations

namespace SmoothManifolds.TorusTranslations
open ModelData AtlasData MapData SphereTorusData HomotopyData Set Filter
open scoped Topology

/-- Unit-speed circle translation is a genuine jointly smooth homotopy in
the standard maximal angle structure. -/
theorem translate_homotopy_smooth {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (j : Fin r) :
    IsSmoothHomotopy S S (fun q : FlatTorus r × UnitInterval => translate j q.2.val q.1) := by
  have hcont : Continuous (fun q : FlatTorus r × UnitInterval => translate j q.2.val q.1) :=
    (translate_continuous j).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply TorusDeRhamResults.isSmoothHomotopy_of_one_chart_germ hcont
  intro p t
  obtain ⟨c, ⟨a, ε, hε, hε', hc⟩, hp⟩ := (SphereTorus.angleAtlas_isContDiffAtlas r).1 p
  let b := (c p).val + Pi.single j t.val
  let d := SphereTorus.angleChart b (1/8) (by norm_num)
  have hd : IsAngleChart b (1/8) d := SphereTorus.angleChart_spec _ _ _
  have hcS : c ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas r)
      ⟨a, ε, hε, hε', hc⟩
  have hdS : d ∈ S.smoothStructure.val := by
    rw [hS]
    exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas r)
      ⟨b, 1/8, by norm_num, by norm_num, hd⟩
  have hquot (q : FlatTorus r) (s : ℝ) (hq : q ∈ c.source) :
      translate j s q = SphereTorusData.quotientProjection r ((c q).val + Pi.single j s) := by
    calc
      _ = translate j s (SphereTorusData.quotientProjection r (c q).val) :=
        congrArg (translate j s) (SphereTorus.angleChart_projection hc hq).symm
      _ = _ := translate_quotient j s (c q).val
  have hb : b ∈ angleBox b (1/8) := SphereTorus.mem_angleBox_center b (by norm_num)
  have hpd : translate j t.val p ∈ d.source := by
    rw [hd.1, hquot p t.val hp]
    exact ⟨b, hb, rfl⟩
  let H : Euclidean (r+1) → Euclidean r :=
    fun z => Fin.init z + Pi.single j (z (Fin.last r))
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
    apply contDiff_pi.mpr
    intro i
    by_cases hi : i = j
    · subst i
      simpa [H, Pi.single_apply, Fin.init] using
        (contDiff_apply ℝ (fun _ : Fin (r+1) => ℝ) j.castSucc).add
          (contDiff_apply ℝ (fun _ : Fin (r+1) => ℝ) (Fin.last r))
    · simpa [H, Pi.single_apply, hi, Fin.init] using
        (contDiff_apply ℝ (fun _ : Fin (r+1) => ℝ) i.castSucc)
  have hsp : ContinuousAt (fun q : FlatTorus r × UnitInterval => (c q.1).val) (p,t) :=
    continuous_subtype_val.continuousAt.comp ((c.continuousAt hp).comp continuous_fst.continuousAt)
  have hsnoc : ContinuousAt (fun q : FlatTorus r × UnitInterval =>
      (Fin.snoc (c q.1).val q.2.val : Euclidean (r+1))) (p,t) := by
    apply continuousAt_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simpa only [Fin.snoc_last, Function.comp_def] using
        ((continuous_subtype_val.comp continuous_snd).continuousAt :
          ContinuousAt (fun q : FlatTorus r × UnitInterval => q.2.val) (p,t))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using (continuous_apply l).continuousAt.comp hsp
  have hbox : ∀ᶠ q : FlatTorus r × UnitInterval in 𝓝 (p,t),
      (c q.1).val + Pi.single j q.2.val ∈ angleBox b (1/8) := by
    have hs := (hH.continuous.continuousAt.comp hsnoc).preimage_mem_nhds
      ((SphereTorus.isOpen_angleBox b (1/8)).mem_nhds (by simpa [H,b] using hb))
    filter_upwards [hs] with q hq
    simpa only [Set.mem_preimage, H, Function.comp_def, Fin.init_snoc, Fin.snoc_last] using hq
  refine ⟨c,hcS,d,hdS,hp,hpd,univ,isOpen_univ,mem_univ _,H,hH.contDiffOn,?_⟩
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hp), hbox]
    with q hqc hqb
  simp only [H, Fin.init_snoc, Fin.snoc_last]
  rw [hquot q.1 q.2.val hqc]
  exact (hd.2.2.1 _ hqb).symm

end SmoothManifolds.TorusTranslations

namespace SmoothManifolds.TorusTranslations
open ModelData AtlasData MapData TangentData TangentBundleData BundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  DifferentialData TorusCoordinates FormPullbackData Set Filter
open scoped Topology

section Differential
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  (C : CotangentBundle S) (j : Fin r) (s : ℝ)
  (L : (p : FlatTorus r) → TangentSpace S p →ₗ[ℝ] TangentSpace S (translate j s p))
  (hL : ∀ p, IsDifferential S S (translate j s) p (L p))

include hS hL

theorem translate_tangent_coordinates {a : Euclidean r} {ε : ℝ}
    {c d : ModelChart r .euclidean (FlatTorus r)}
    (hcS : c ∈ S.smoothStructure.val) (hdS : d ∈ S.smoothStructure.val)
    (hc : IsAngleChart a ε c) (hd : IsAngleChart (a + Pi.single j s) ε d)
    (p : FlatTorus r) (hp : p ∈ c.source)
    (v : TangentSpace S p) :
    C.tangent.fiberCoordinates.equiv d hdS (translate j s p)
      (translate_angleChart j s hc hd p hp).1 (L p v) =
      C.tangent.fiberCoordinates.equiv c hcS p hp v := by
  have hev : (fun q => (c q).val + Pi.single j s) =ᶠ[𝓝 p]
      (fun q => (d (translate j s q)).val) := by
    filter_upwards [c.open_source.mem_nhds hp] with q hq
    exact (translate_angleChart j s hc hd q hq).2.symm
  have hJ := differential_jacobian S S (translate j s) (translate_smooth S hS j s)
    p (L p) (hL p) c d hcS hdS hp (translate_angleChart j s hc hd p hp).1
    (C.tangent.fiberCoordinates.equiv c hcS p hp)
    (C.tangent.fiberCoordinates.equiv d hdS (translate j s p)
      (translate_angleChart j s hc hd p hp).1)
    (C.tangent.fiberCoordinates.isCoordinates c hcS p hp)
    (C.tangent.fiberCoordinates.isCoordinates d hdS (translate j s p)
      (translate_angleChart j s hc hd p hp).1)
    univ (fun y => y + Pi.single j s) isOpen_univ (mem_univ _)
    (contDiff_id.add contDiff_const).contDiffOn hev v
  simpa only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply] using hJ

theorem translate_coordinateCovector {a : Euclidean r} {ε : ℝ}
    {c d : ModelChart r .euclidean (FlatTorus r)}
    (hcS : c ∈ S.smoothStructure.val) (hdS : d ∈ S.smoothStructure.val)
    (hc : IsAngleChart a ε c) (hd : IsAngleChart (a + Pi.single j s) ε d)
    (p : FlatTorus r) (hp : p ∈ c.source) (i : Fin r) :
    (L p).dualMap (coordinateCovector C.tangent.fiberCoordinates d hdS (translate j s p)
      (translate_angleChart j s hc hd p hp).1 i) =
      coordinateCovector C.tangent.fiberCoordinates c hcS p hp i := by
  apply LinearMap.ext
  intro v
  exact congrFun (translate_tangent_coordinates S hS C j s L hL hcS hdS hc hd p hp v) i

theorem translate_angleCovector (p : FlatTorus r) (i : Fin r) :
    (L p).dualMap (angleCovector S hS C i (translate j s p)) = angleCovector S hS C i p := by
  obtain ⟨c, hcS, hp, a, ε, hε, hε', hc⟩ := exists_angle_chart S hS p
  let d := SphereTorus.angleChart (a + Pi.single j s) ε (by linarith : ε < 1/2)
  have hd : IsAngleChart (a + Pi.single j s) ε d := SphereTorus.angleChart_spec _ _ _
  have hdS : d ∈ S.smoothStructure.val := angleAtlas_subset S hS
    ⟨a + Pi.single j s, ε, hε, hε', hd⟩
  rw [angleCovector_on_chart S hS C i d hdS hd _ (translate_angleChart j s hc hd p hp).1,
    angleCovector_on_chart S hS C i c hcS hc p hp]
  exact translate_coordinateCovector S hS C j s L hL hcS hdS hc hd p hp i

theorem translate_angleDualEquiv (p : FlatTorus r) :
    (L p).dualMap.comp (angleDualEquiv S hS C (translate j s p)).toLinearMap =
      (angleDualEquiv S hS C p).toLinearMap := by
  apply (Pi.basisFun ℝ (Fin r)).ext
  intro i
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (L p).dualMap (angleDualEquiv S hS C (translate j s p) (Pi.single i 1)) =
    angleDualEquiv S hS C p (Pi.single i 1)
  rw [angleDualEquiv_single, angleDualEquiv_single]
  exact translate_angleCovector S hS C j s L hL p i

theorem translate_constantField (k : ℕ) (x : ExteriorModel r k) :
    pullbackField S S (translate j s) L (constantField S hS C k x) =
      constantField S hS C k x := by
  funext p
  change ((exteriorPower.map k (L p).dualMap).comp
    (exteriorPower.map k (angleDualEquiv S hS C (translate j s p)).toLinearMap)) x = _
  rw [← exteriorPower.map_comp, translate_angleDualEquiv S hS C j s L hL p]
  rfl

/-- In the global parallel coframe, pullback by translation composes the coefficient function. -/
theorem translate_parallelField (k : ℕ) (f : FlatTorus r → ExteriorModel r k) :
    pullbackField S S (translate j s) L
      (fun q => exteriorPower.map k (angleDualEquiv S hS C q).toLinearMap (f q)) =
      (fun p => exteriorPower.map k (angleDualEquiv S hS C p).toLinearMap
        (f (translate j s p))) := by
  funext p
  change ((exteriorPower.map k (L p).dualMap).comp
    (exteriorPower.map k (angleDualEquiv S hS C (translate j s p)).toLinearMap))
    (f (translate j s p)) = _
  rw [← exteriorPower.map_comp, translate_angleDualEquiv S hS C j s L hL p]

/-- The intrinsic coefficient field transforms by ordinary composition with translation. -/
theorem translate_parallelCoefficients (k : ℕ) (ω : Field S k) :
    parallelCoefficients S hS C k (pullbackField S S (translate j s) L ω) =
      fun p => parallelCoefficients S hS C k ω (translate j s p) := by
  funext p
  have hω : (fun q => exteriorPower.map k (angleDualEquiv S hS C q).toLinearMap
      (parallelCoefficients S hS C k ω q)) = ω := by
    funext q
    exact (field_eq_parallel_synthesis S hS C k ω q).symm
  have hp := congrFun (translate_parallelField S hS C j s L hL k
    (parallelCoefficients S hS C k ω)) p
  rw [hω] at hp
  change pullbackField S S (translate j s) L ω p =
    flatExteriorEquiv S hS C k p (parallelCoefficients S hS C k ω (translate j s p)) at hp
  change (flatExteriorEquiv S hS C k p).symm (pullbackField S S (translate j s) L ω p) = _
  rw [hp, LinearEquiv.symm_apply_apply]


omit hL

/-- The pullback invariance applies to the already constructed intrinsic differential. -/
theorem translate_constantField_differential (k : ℕ) (x : ExteriorModel r k) :
    pullbackField S S (translate j s)
      (differential S S (translate j s) (translate_smooth S hS j s))
      (constantField S hS C k x) = constantField S hS C k x :=
  translate_constantField S hS C j s
    (differential S S (translate j s) (translate_smooth S hS j s))
    (differential_spec S S (translate j s) (translate_smooth S hS j s)) k x

end Differential
end SmoothManifolds.TorusTranslations


namespace SmoothManifolds.TorusTranslations
open ModelData AtlasData SphereTorusData Set Filter

/-- Single-coordinate real translations generate all translations of the
actual period-one quotient torus, so a field of arbitrary values fixed by
every such translation is constant. -/
theorem invariant_function_constant {r : ℕ} {V : Type*}
    (f : FlatTorus r → V)
    (hf : ∀ (j : Fin r) (s : ℝ) (p : FlatTorus r), f (translate j s p) = f p)
    (q : FlatTorus r) : f q = f 0 := by
  classical
  have hsingle (j : Fin r) (s : AddCircle (1 : ℝ)) (p : FlatTorus r) :
      f (p + Pi.single j s) = f p := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective s
    have hproj : quotientProjection r (Pi.single j t) =
        Pi.single j (t : AddCircle (1 : ℝ)) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [SphereTorusData.quotientProjection]
      · simp [SphereTorusData.quotientProjection, Pi.single_apply, hi]
    simpa only [translate, hproj] using hf j t p
  have hsum (t : Finset (Fin r)) (p : FlatTorus r) :
      f (p + ∑ j ∈ t, Pi.single j (q j)) = f p := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
      rw [Finset.sum_insert hj]
      calc
        f (p + (Pi.single j (q j) + ∑ i ∈ t, Pi.single i (q i))) =
            f ((p + ∑ i ∈ t, Pi.single i (q i)) + Pi.single j (q j)) := by
          congr 1
          abel
        _ = f (p + ∑ i ∈ t, Pi.single i (q i)) := hsingle j (q j) _
        _ = f p := ih
  have hq : (∑ j : Fin r, Pi.single j (q j)) = q := by
    funext i
    simp [Pi.single_apply]
  simpa only [hq, zero_add] using hsum Finset.univ 0

end SmoothManifolds.TorusTranslations

namespace SmoothManifolds.TorusAveraging
open HomotopyIntegration MeasureTheory Module
open scoped BigOperators
universe u v w x
variable {V : Type u} [AddCommGroup V] [Module ℝ V]
  {W : Type v} [AddCommGroup W] [Module ℝ W]
  {ι : Type w} [Fintype ι] {κ : Type x} [Fintype κ]

/-- Integration in a finite basis commutes with an arbitrary real linear map.
The hypothesis is ordinary scalar integrability; no topology on an abstract
intrinsic exterior fiber or on its cohomology quotient is introduced. -/
theorem basisIntegral_linearMap (b : Basis ι ℝ V) (c : Basis κ ℝ W)
    (f : ℝ → V)
    (hf : ∀ i, IntervalIntegrable (fun t => b.repr (f t) i) volume 0 1)
    (L : V →ₗ[ℝ] W) :
    L (basisIntegral b f) = basisIntegral c (fun t => L (f t)) := by
  classical
  apply c.repr.injective
  ext i
  change (c.coord i).comp L (basisIntegral b f) = _
  rw [basisIntegral_map b f hf ((c.coord i).comp L)]
  simp [basisIntegral, map_sum, map_smul, Finsupp.single_apply]

end SmoothManifolds.TorusAveraging

namespace SmoothManifolds.TorusAveraging
open SphereTorusData TorusTranslations

/-- The scalar mean in one coordinate circle, using its period-one parameter. -/
def coordinateMean {r : ℕ} (j : Fin r) (f : FlatTorus r → ℝ) (p : FlatTorus r) : ℝ :=
  ∫ t in (0 : ℝ)..1, f (translate j t p)

def CoordinateInvariant {r : ℕ} (j : Fin r) (f : FlatTorus r → ℝ) : Prop :=
  ∀ s p, f (translate j s p) = f p

/-- Averaging in a coordinate produces invariance in that coordinate. -/
theorem coordinateMean_invariant {r : ℕ} (j : Fin r) (f : FlatTorus r → ℝ) :
    CoordinateInvariant j (coordinateMean j f) := by
  intro s p
  let g : ℝ → ℝ := fun t => f (translate j t p)
  have hper : Function.Periodic g 1 := by
    intro t
    exact congrArg f (translate_periodic j p t)
  change (∫ t in (0 : ℝ)..1, f (translate j t (translate j s p))) = _
  simp_rw [← translate_add]
  change (∫ t in (0 : ℝ)..1, g (t+s)) = coordinateMean j f p
  rw [intervalIntegral.integral_comp_add_right g s]
  simpa only [zero_add, add_comm 1 s, coordinateMean, g] using hper.intervalIntegral_add_eq s 0

/-- A coordinate mean preserves invariance under every other coordinate. -/
theorem coordinateMean_preserves_invariant {r : ℕ} (i j : Fin r)
    (f : FlatTorus r → ℝ) (hf : CoordinateInvariant j f) :
    CoordinateInvariant j (coordinateMean i f) := by
  intro s p
  unfold coordinateMean
  apply intervalIntegral.integral_congr
  intro t _
  change f (translate i t (translate j s p)) = f (translate i t p)
  rw [translate_commute i j t s p, hf]

/-- Iterate the actual scalar coordinate means in the specified order. -/
def coordinateMeans {r : ℕ} (is : List (Fin r)) (f : FlatTorus r → ℝ) : FlatTorus r → ℝ :=
  is.foldl (fun g j => coordinateMean j g) f

theorem coordinateMeans_preserves_invariant {r : ℕ} (is : List (Fin r)) (j : Fin r)
    (f : FlatTorus r → ℝ) (hf : CoordinateInvariant j f) :
    CoordinateInvariant j (coordinateMeans is f) := by
  induction is generalizing f with
  | nil => exact hf
  | cons i is ih =>
    exact ih (coordinateMean i f) (coordinateMean_preserves_invariant i j f hf)

/-- After a list of averages the coefficients are invariant under all
coordinates that have occurred, without invoking Fubini or a Künneth theorem. -/
theorem coordinateMeans_invariant {r : ℕ} (is : List (Fin r))
    (j : Fin r) (hj : j ∈ is) (f : FlatTorus r → ℝ) :
    CoordinateInvariant j (coordinateMeans is f) := by
  induction is generalizing f with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact coordinateMeans_preserves_invariant is i (coordinateMean i f)
        (coordinateMean_invariant i f)
    · exact ih hj (coordinateMean i f)

end SmoothManifolds.TorusAveraging

namespace SmoothManifolds.TorusCoordinates
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  Set Filter
open scoped Topology

theorem class_unit_eq_of_scalar {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    (η : K.closed 0) (hη : η.val.val = FormPullbackData.scalarField S (fun _ => 1)) :
    K.classOf 0 η = P.one := by
  obtain ⟨ε, hε, hunit⟩ := hP.2.2.2.2.2.1
  have heq : η = ε := Subtype.ext (Subtype.ext (hη.trans hε.symm))
  rw [heq]
  exact hunit.symm

theorem constantClosed_class_one {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (P : K.GradedProduct) (hP : K.IsGradedProduct P) :
    K.classOf 0 (constantClosed S hS C B K 0
      ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1)) = P.one := by
  apply class_unit_eq_of_scalar K P hP
  rw [constantClosed_field, constantField_one]

end SmoothManifolds.TorusCoordinates

namespace SmoothManifolds.TorusCoordinates
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  HomotopyIntegration MeasureTheory Set Filter
open scoped Topology

section ParallelIntegration
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  (C : CotangentBundle S)

/-- Every scalar linear projection of parallel coefficients commutes with the actual fiber integral. -/
theorem parallelCoefficients_integralField_apply (k : ℕ) (f : ℝ → Field S k)
    (hf : CoefficientsIntervalIntegrable C k f) (p : FlatTorus r)
    (φ : ExteriorModel r k →ₗ[ℝ] ℝ) :
    φ (parallelCoefficients S hS C k (integralField C k f) p) =
      ∫ t in (0 : ℝ)..1, φ (parallelCoefficients S hS C k (f t) p) := by
  exact basisIntegral_map (pointExteriorBasis C k p) (fun t => f t p)
    (pointExteriorBasis_integrable C k f hf p)
    (φ.comp (flatExteriorEquiv S hS C k p).symm.toLinearMap)

/-- In particular each model exterior-basis coefficient commutes with the fiber integral. -/
theorem parallelCoefficients_integralField (k : ℕ) (f : ℝ → Field S k)
    (hf : CoefficientsIntervalIntegrable C k f) (p : FlatTorus r)
    (I : Index r k) :
    ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr
      (parallelCoefficients S hS C k (integralField C k f) p) I =
      ∫ t in (0 : ℝ)..1, ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr
        (parallelCoefficients S hS C k (f t) p) I := by
  exact parallelCoefficients_integralField_apply S hS C k f hf p
    (((Pi.basisFun ℝ (Fin r)).exteriorPower k).coord I)

end ParallelIntegration
end SmoothManifolds.TorusCoordinates

namespace SmoothManifolds.TorusTranslations
open ModelData AtlasData TangentData TangentBundleData BundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  DifferentialData TorusCoordinates FormPullbackData Set Filter
open scoped Topology

/-- A field fixed by all genuine coordinate-translation pullbacks has constant parallel coefficients. -/
theorem invariant_field_constant {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (k : ℕ) (ω : Field S k)
    (hω : ∀ (j : Fin r) (s : ℝ),
      pullbackField S S (translate j s)
        (differential S S (translate j s) (translate_smooth S hS j s)) ω = ω) :
    ω = constantField S hS C k (parallelCoefficients S hS C k ω 0) := by
  apply (field_constant_iff_parallelCoefficients S hS C k ω _).mpr
  funext p
  apply invariant_function_constant (parallelCoefficients S hS C k ω) _ p
  intro j s q
  have heq := translate_parallelCoefficients S hS C j s
    (differential S S (translate j s) (translate_smooth S hS j s))
    (differential_spec S S (translate j s) (translate_smooth S hS j s)) k ω
  rw [hω j s] at heq
  exact (congrFun heq q).symm

end SmoothManifolds.TorusTranslations

namespace SmoothManifolds.TorusAveraging
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  TorusCoordinates Set Filter
open scoped Topology

section IteratedForms
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

/-- Apply coordinate averages in list order: first the head, then the tail. -/
def iteratedForms (A : Fin n → ∀ k, K.forms k →ₗ[ℝ] K.forms k) :
    List (Fin n) → ∀ k, K.forms k →ₗ[ℝ] K.forms k
  | [], k => LinearMap.id
  | j :: js, k => (iteratedForms A js k).comp (A j k)

end IteratedForms

section Range
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)

/-- A scalar coordinate of the actual parallel exterior coefficient field. -/
def parallelCoefficient (k : ℕ) (ω : Field S k) (I : Index r k) : FlatTorus r → ℝ :=
  fun p => ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr
    (parallelCoefficients S hS C k ω p) I

/-- Iteration of the form averages induces the same iteration of every
scalar coefficient. This does not assume that averaging preserves wedge. -/
theorem iteratedForms_coefficient
    (A : Fin r → ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (hA : ∀ (j : Fin r) (k : ℕ) (ω : K.forms k) (I : Index r k) (p : FlatTorus r),
      parallelCoefficient S hS C k (A j k ω).val I p =
        coordinateMean j (parallelCoefficient S hS C k ω.val I) p)
    (is : List (Fin r)) (k : ℕ) (ω : K.forms k) (I : Index r k) :
    parallelCoefficient S hS C k (iteratedForms K A is k ω).val I =
      coordinateMeans is (parallelCoefficient S hS C k ω.val I) := by
  induction is generalizing ω with
  | nil => rfl
  | cons j js ih =>
    change parallelCoefficient S hS C k (iteratedForms K A js k (A j k ω)).val I =
      coordinateMeans js (coordinateMean j (parallelCoefficient S hS C k ω.val I))
    rw [ih]
    have he : parallelCoefficient S hS C k (A j k ω).val I =
        coordinateMean j (parallelCoefficient S hS C k ω.val I) := by
      funext p
      exact hA j k ω I p
    rw [he]

/-- Once every coordinate has been averaged, the result is exactly the
constant field whose coefficient is its value at the identity. -/
theorem iteratedForms_constant
    (A : Fin r → ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (hA : ∀ (j : Fin r) (k : ℕ) (ω : K.forms k) (I : Index r k) (p : FlatTorus r),
      parallelCoefficient S hS C k (A j k ω).val I p =
        coordinateMean j (parallelCoefficient S hS C k ω.val I) p)
    (is : List (Fin r)) (his : ∀ j : Fin r, j ∈ is) (k : ℕ) (ω : K.forms k) :
    (iteratedForms K A is k ω).val = constantField S hS C k
      (parallelCoefficients S hS C k (iteratedForms K A is k ω).val 0) := by
  apply (field_constant_iff_parallelCoefficients S hS C k _ _).mpr
  funext p
  apply ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr.injective
  ext I
  change parallelCoefficient S hS C k (iteratedForms K A is k ω).val I p =
    parallelCoefficient S hS C k (iteratedForms K A is k ω).val I 0
  rw [iteratedForms_coefficient S hS C B K A hA is k ω I]
  apply TorusTranslations.invariant_function_constant
  intro j s q
  exact coordinateMeans_invariant is j (his j)
    (parallelCoefficient S hS C k ω.val I) s q

end Range
end SmoothManifolds.TorusAveraging

namespace SmoothManifolds.TorusAveraging
open ModelData AtlasData TangentData TangentBundleData BundleData Module
  BundleOperationsData CovectorData ExteriorData DeRhamData SphereTorusData TorusDeRhamData
  TorusCoordinates TorusDeRhamResults Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  (K : Calculus C B)

/-- A finite ordered composition of chain maps is a chain map. -/
theorem iteratedForms_chain
    (A : Fin n → ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (hA : ∀ (j : Fin n) k ω, K.d k (A j k ω) = A j (k+1) (K.d k ω))
    (is : List (Fin n)) (k : ℕ) (ω : K.forms k) :
    K.d k (iteratedForms K A is k ω) =
      iteratedForms K A is (k+1) (K.d k ω) := by
  induction is generalizing ω with
  | nil => rfl
  | cons j js ih =>
    exact (ih (A j k ω)).trans
      (congrArg (iteratedForms K A js (k+1)) (hA j k ω))

/-- A common fixed form remains fixed under every finite sequence of averages. -/
theorem iteratedForms_fixed
    (A : Fin n → ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (is : List (Fin n)) (k : ℕ) (ω : K.forms k)
    (hω : ∀ j : Fin n, A j k ω = ω) :
    iteratedForms K A is k ω = ω := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    change iteratedForms K A js k (A j k ω) = ω
    rw [hω j]
    exact ih

/-- The composition of coordinate averages preserves each closed form's
cohomology class when the individual averages do. -/
theorem iteratedForms_class
    (A : Fin n → ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (hchain : ∀ (j : Fin n) k ω, K.d k (A j k ω) = A j (k+1) (K.d k ω))
    (hclass : ∀ (j : Fin n) (k : ℕ) (ω : K.closed k),
      K.classOf k (mapClosed K (A j) (hchain j) k ω) = K.classOf k ω)
    (is : List (Fin n)) (k : ℕ) (ω : K.closed k) :
    K.classOf k (mapClosed K (iteratedForms K A is)
      (iteratedForms_chain K A hchain is) k ω) = K.classOf k ω := by
  induction is generalizing ω with
  | nil => rfl
  | cons j js ih =>
    let η : K.closed k := mapClosed K (A j) (hchain j) k ω
    have heq : mapClosed K (iteratedForms K A (j :: js))
        (iteratedForms_chain K A hchain (j :: js)) k ω =
        mapClosed K (iteratedForms K A js)
          (iteratedForms_chain K A hchain js) k η := by
      apply Subtype.ext
      rfl
    exact (congrArg (K.classOf k) heq).trans ((ih η).trans (hclass j k ω))

end SmoothManifolds.TorusAveraging

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData DeRhamData HomotopyData HomotopyIntegration
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M × UnitInterval → N}

/-- Horizontal pullback is linear before integrating the time parameter. -/
def alphaFamilyLinearMap {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (J : Calculus A E) (D : HomotopyDifferentials S T F) (k : ℕ) :
    J.forms k →ₗ[ℝ] (ℝ → Field S k) where
  toFun ω t := alpha D ω.val (intervalTime t)
  map_add' ω η := by
    funext t p
    exact map_add (FormPullbackData.fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (F (p, intervalTime t))) k (D.spatial (intervalTime t) p))
      (ω.val (F (p, intervalTime t))) (η.val (F (p, intervalTime t)))
  map_smul' c ω := by
    funext t p
    exact map_smul (FormPullbackData.fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (F (p, intervalTime t))) k (D.spatial (intervalTime t) p))
      c (ω.val (F (p, intervalTime t)))

/-- Averaged pullback is a linear map on the full intrinsic smooth-form spaces. -/
def homotopyAverage {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hF : IsSmoothHomotopy S T F) (D : HomotopyDifferentials S T F) (k : ℕ) :
    J.forms k →ₗ[ℝ] K.forms k where
  toFun ω := by
    have hα : JointSmoothCoefficients C k (fun t => alpha D ω.val t) :=
      alpha_jointSmooth hF C A D ω.val (E k) ((J.mem_forms _ _).mp ω.property)
    have hform : IsForm (B k)
        (integralField C k (fun t => alpha D ω.val (intervalTime t))) :=
      isForm_integralField_of_jointSmooth C k (B k) _ hα
    exact ⟨integralField C k (fun t => alpha D ω.val (intervalTime t)),
      (K.mem_forms k _).mpr hform⟩
  map_add' ω η := by
    apply Subtype.ext
    have hω := jointSmooth_coefficientsIntervalIntegrable C k _
      (alpha_jointSmooth hF C A D ω.val (E k) ((J.mem_forms _ _).mp ω.property))
    have hη := jointSmooth_coefficientsIntervalIntegrable C k _
      (alpha_jointSmooth hF C A D η.val (E k) ((J.mem_forms _ _).mp η.property))
    exact (congrArg (integralField C k) ((alphaFamilyLinearMap J D k).map_add ω η)).trans
      (integralField_add C k ((alphaFamilyLinearMap J D k) ω)
        ((alphaFamilyLinearMap J D k) η) hω hη)
  map_smul' c ω := by
    apply Subtype.ext
    exact (congrArg (integralField C k) ((alphaFamilyLinearMap J D k).map_smul c ω)).trans
      (integralField_smul C k c ((alphaFamilyLinearMap J D k) ω))

@[simp] theorem homotopyAverage_val {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hF : IsSmoothHomotopy S T F) (D : HomotopyDifferentials S T F)
    (k : ℕ) (ω : J.forms k) :
    (homotopyAverage K J hF D k ω).val =
      integralField C k (fun t => alpha D ω.val (intervalTime t)) := rfl

/-- Averaging commutes with the genuine de Rham differentials. -/
theorem homotopyAverage_chain {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle T} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hF : IsSmoothHomotopy S T F) (D : HomotopyDifferentials S T F)
    (k : ℕ) (ω : J.forms k) :
    K.d k (homotopyAverage K J hF D k ω) =
      homotopyAverage K J hF D (k+1) (J.d k ω) := by
  apply Subtype.ext
  change K.D k (integralField C k (fun t => alpha D ω.val (intervalTime t))) = _
  rw [derivative_integralField K k _
    (alpha_jointSmooth hF C A D ω.val (E k) ((J.mem_forms _ _).mp ω.property))]
  apply congrArg (integralField C (k+1))
  funext t
  exact (ExteriorDerivativeResults.smooth_naturality S T C A B E K.D J.D K.axioms J.axioms
    (fun p => F (p,intervalTime t)) (hF.slice_smooth (intervalTime t))
    (D.spatial (intervalTime t)) (D.spatial_correct (intervalTime t)) k ω.val
    ((J.mem_forms _ _).mp ω.property)).symm

end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData SphereTorusData TorusDeRhamData TorusCoordinates

/-- A chain projection with exactly the constant-coefficient image yields the
specified torus ring presentation. Every geometric property is explicit, and
the final torus theorem must construct this projection. -/
def presentationOfConstantProjection {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (P : K.GradedProduct) (hP : K.IsGradedProduct P)
    (F : ∀ k, K.forms k →ₗ[ℝ] K.forms k)
    (hchain : ∀ k ω, K.d k (F k ω) = F (k+1) (K.d k ω))
    (hconstant : ∀ k ω, (F k ω).val = constantField S hS C k
      (parallelCoefficients S hS C k (F k ω).val 0))
    (hfix : ∀ k x, F k (constantClosed S hS C B K k x).val =
      (constantClosed S hS C B K k x).val)
    (hclass : ∀ k (ω : K.closed k),
      K.classOf k (mapClosed K F hchain k ω) = K.classOf k ω) : Presentation K P := by
  let E := constantClosed S hS C B K
  let Q (k : ℕ) : K.forms k →ₗ[ℝ] ExteriorModel r k :=
    (LinearMap.proj (0 : FlatTorus r)).comp
      ((parallelCoefficients S hS C k).comp ((K.forms k).subtype.comp (F k)))
  have hQE (k : ℕ) (x : ExteriorModel r k) : Q k (E k x).val = x := by
    change parallelCoefficients S hS C k (F k (E k x).val).val 0 = x
    rw [hfix, constantClosed_field, parallelCoefficients_constantField]
  have hQexact (k : ℕ) (η : K.forms k) (hη : η ∈ K.exact k) : Q k η = 0 := by
    cases k with
    | zero =>
      have hzero : η = 0 := (Submodule.mem_bot ℝ).mp hη
      rw [hzero, map_zero]
    | succ k =>
      obtain ⟨ξ, rfl⟩ := hη
      have heq : F k ξ = (E k (Q k ξ)).val := by
        apply Subtype.ext
        change (F k ξ).val = (constantClosed S hS C B K k (Q k ξ)).val.val
        rw [constantClosed_field]
        exact hconstant k ξ
      have hd : K.d k (F k ξ) = 0 := by
        rw [heq]
        exact (E k (Q k ξ)).property
      change parallelCoefficients S hS C (k+1) (F (k+1) (K.d k ξ)).val 0 = 0
      rw [← hchain, hd]
      exact congrFun (map_zero (parallelCoefficients S hS C (k+1))) 0
  have herror (k : ℕ) (ω : K.closed k) : (E k (Q k ω.val)).val - ω.val ∈ K.exact k := by
    apply (class_eq_iff_difference_exact K (E k (Q k ω.val)) ω).mp
    have heq : E k (Q k ω.val) = mapClosed K F hchain k ω := by
      apply Subtype.ext
      apply Subtype.ext
      change (constantClosed S hS C B K k (Q k ω.val)).val.val = (F k ω.val).val
      rw [constantClosed_field]
      exact (hconstant k ω.val).symm
    exact (congrArg (K.classOf k) heq).trans (hclass k ω)
  exact presentationOfRetraction K P hP (closedAngleForm S hS C B K)
    (angleForm_isCoordinateForm S hS C)
    (TorusLoopPeriods.loop_piecewiseSmooth S hS)
    (fun i j => TorusLoopPeriods.loop_period S hS C i j _
      (angleForm_isCoordinateForm S hS C i))
    E Q hQE hQexact herror (constantClosed_generator S hS C B K)
    (constantClosed_class_one S hS C B K P hP)
    (fun k l x y => by simp only [E, constantClosed_field, constantField_wedge])

end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData DeRhamData HomotopyData HomotopyIntegration
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {F : M × UnitInterval → M}

/-- A smooth self-homotopy starting at the identity gives an average that
preserves every de Rham class, in every degree. -/
theorem homotopyAverage_class {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (hF : IsSmoothHomotopy S S F)
    (D : HomotopyDifferentials S S F)
    (hzero : (fun p => F (p,initialTime)) = id) (k : ℕ) (ω : K.closed k) :
    K.classOf k
      (mapClosed K (fun k => homotopyAverage K K hF D k)
        (fun k ω => homotopyAverage_chain K K hF D k ω) k ω) = K.classOf k ω := by
  cases k with
  | zero =>
    apply congrArg (K.classOf 0)
    apply Subtype.ext
    apply Subtype.ext
    exact (homotopyAverage_val K K hF D 0 ω.val).trans
      ((averaged_pullback_degreeZero C K hF D ω).trans
        (alpha_eq_self_of_slice_eq_id D initialTime hzero ω.val.val))
  | succ k =>
    have hex : ∃ η : K.forms k,
        (K.d k η).val = integralField C (k+1)
          (fun t => alpha D ω.val.val (intervalTime t)) - alpha D ω.val.val initialTime :=
      averaged_pullback_difference_exact (S := S) (T := S) (C := C) (B := B) (A := C) (E := B)
        K K hF D k ω
    obtain ⟨η,hη⟩ := hex
    apply class_eq_of_derivative_difference K _ ω η
    apply Subtype.ext
    exact hη.trans (congrArg₂ (fun x y : Field S (k+1) => x-y)
      (homotopyAverage_val K K hF D (k+1) ω.val).symm
      (alpha_eq_self_of_slice_eq_id D initialTime hzero ω.val.val))
end SmoothManifolds.TorusDeRhamResults

namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData DeRhamData HomotopyData HomotopyIntegration SphereTorusData TorusDeRhamData
  TorusCoordinates TorusTranslations TorusAveraging Set Filter
open scoped Topology

section CoordinateAverage
variable {r : ℕ}
  (S : SmoothManifold r .euclidean (FlatTorus r))
  (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
  {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)

/-- The actual average of intrinsic pullbacks over one full coordinate period. -/
def coordinateAverage (j : Fin r) (k : ℕ) : K.forms k →ₗ[ℝ] K.forms k :=
  homotopyAverage K K (translate_homotopy_smooth S hS j)
    (translate_homotopy_smooth S hS j).differentials k

@[simp] theorem coordinateAverage_val (j : Fin r) (k : ℕ) (ω : K.forms k) :
    (coordinateAverage S hS K j k ω).val = integralField C k (fun t =>
      alpha (translate_homotopy_smooth S hS j).differentials ω.val (intervalTime t)) := rfl

theorem coordinateAverage_chain (j : Fin r) (k : ℕ) (ω : K.forms k) :
    K.d k (coordinateAverage S hS K j k ω) =
      coordinateAverage S hS K j (k+1) (K.d k ω) :=
  homotopyAverage_chain K K (translate_homotopy_smooth S hS j)
    (translate_homotopy_smooth S hS j).differentials k ω

/-- The horizontal part of the translation homotopy has the genuine translated coefficients. -/
theorem translate_alpha_parallelCoefficients (j : Fin r)
    (D : HomotopyDifferentials S S
      (fun q : FlatTorus r × UnitInterval => translate j q.2.val q.1))
    (k : ℕ) (ω : Field S k) (u : UnitInterval) :
    parallelCoefficients S hS C k (alpha D ω u) =
      fun p => parallelCoefficients S hS C k ω (translate j u.val p) :=
  translate_parallelCoefficients S hS C j u.val (D.spatial u) (D.spatial_correct u) k ω

/-- Every ordered exterior coordinate of the actual average is the scalar full-period mean. -/
theorem coordinateAverage_coefficient (j : Fin r) (k : ℕ) (ω : K.forms k)
    (p : FlatTorus r) (I : Index r k) :
    ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr
      (parallelCoefficients S hS C k (coordinateAverage S hS K j k ω).val p) I =
      coordinateMean j (fun q => ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr
        (parallelCoefficients S hS C k ω.val q) I) p := by
  let hF := translate_homotopy_smooth S hS j
  let D := hF.differentials
  have hα : JointSmoothCoefficients C k (fun t => alpha D ω.val t) :=
    alpha_jointSmooth hF C C D ω.val (B k) ((K.mem_forms _ _).mp ω.property)
  rw [coordinateAverage_val, parallelCoefficients_integralField S hS C k _
    (jointSmooth_coefficientsIntervalIntegrable C k _ hα)]
  unfold coordinateMean
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have hclamp : (intervalTime t).val = t :=
    congrArg Subtype.val (intervalTime_coe ⟨t, ht'⟩)
  have heq := congrFun (translate_alpha_parallelCoefficients S hS (C := C) j D k ω.val
    (intervalTime t)) p
  change ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr
    (parallelCoefficients S hS C k (alpha D ω.val (intervalTime t)) p) I =
    ((Pi.basisFun ℝ (Fin r)).exteriorPower k).repr
      (parallelCoefficients S hS C k ω.val (translate j t p)) I
  rw [heq, hclamp]

/-- Every coordinate average fixes all genuine constant closed exterior forms. -/
theorem coordinateAverage_constantClosed (j : Fin r) (k : ℕ) (x : ExteriorModel r k) :
    coordinateAverage S hS K j k (constantClosed S hS C B K k x).val =
      (constantClosed S hS C B K k x).val := by
  apply Subtype.ext
  rw [coordinateAverage_val]
  let D := (translate_homotopy_smooth S hS j).differentials
  have hα : ∀ t : ℝ,
      alpha D (constantClosed S hS C B K k x).val.val (intervalTime t) =
        constantField S hS C k x := by
    intro t
    exact (congrArg (fun ω : Field S k => alpha D ω (intervalTime t))
      (constantClosed_field S hS C B K k x)).trans
      (translate_constantField S hS C j (intervalTime t).val (D.spatial (intervalTime t))
        (D.spatial_correct (intervalTime t)) k x)
  have hconst : integralField C k (fun _ : ℝ => constantField S hS C k x) =
      constantField S hS C k x := by
    funext p
    change basisIntegral (pointExteriorBasis C k p) (fun _ => constantField S hS C k x p) = _
    simpa only [basisIntegral, intervalIntegral.integral_const, sub_zero, one_smul] using
      (pointExteriorBasis C k p).sum_repr (constantField S hS C k x p)
  exact (congrArg (integralField C k) (funext hα)).trans
    (hconst.trans (constantClosed_field S hS C B K k x).symm)

end CoordinateAverage
end SmoothManifolds.TorusDeRhamResults


namespace SmoothManifolds.TorusDeRhamResults
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  DeRhamData SphereTorusData TorusDeRhamData TorusCoordinates TorusAveraging
  TorusTranslations HomotopyData

/-- Each full-period coordinate average preserves all cohomology classes. -/
theorem coordinateAverage_class {r : ℕ}
    (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (j : Fin r) (k : ℕ) (ω : K.closed k) :
    K.classOf k (mapClosed K (coordinateAverage S hS K j)
      (coordinateAverage_chain S hS K j) k ω) = K.classOf k ω := by
  exact homotopyAverage_class K (translate_homotopy_smooth S hS j)
    (translate_homotopy_smooth S hS j).differentials
    (by funext p; exact translate_zero j p) k ω

/-- The real graded de Rham algebra of the standard torus is the exterior
algebra on its normalized coordinate classes, in every dimension and degree. -/
theorem torus_algebra : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType := by
  intro r S hS C B K P hP
  let A : Fin r → ∀ k, K.forms k →ₗ[ℝ] K.forms k := coordinateAverage S hS K
  let is : List (Fin r) := List.finRange r
  have hchain : ∀ j k ω, K.d k (A j k ω) = A j (k+1) (K.d k ω) :=
    coordinateAverage_chain S hS K
  have hcoeff : ∀ j k (ω : K.forms k) (I : Index r k) p,
      parallelCoefficient S hS C k (A j k ω).val I p =
        coordinateMean j (parallelCoefficient S hS C k ω.val I) p := by
    intro j k ω I p
    exact coordinateAverage_coefficient S hS K j k ω p I
  refine ⟨presentationOfConstantProjection S hS C B K P hP
    (iteratedForms K A is) (iteratedForms_chain K A hchain is) ?_ ?_ ?_⟩
  · intro k ω
    exact iteratedForms_constant S hS C B K A hcoeff is
      (fun j => by simp [is]) k ω
  · intro k x
    exact iteratedForms_fixed K A is k (constantClosed S hS C B K k x).val
      (fun j => coordinateAverage_constantClosed S hS K j k x)
  · exact iteratedForms_class K A hchain (coordinateAverage_class S hS K) is

end SmoothManifolds.TorusDeRhamResults
