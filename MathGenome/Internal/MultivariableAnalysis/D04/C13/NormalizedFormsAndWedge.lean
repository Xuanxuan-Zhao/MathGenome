import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.NormalizedFormsAndWedge
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import MathGenome.Internal.D05.M15.ExteriorPairing.AlternatingForms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped BigOperators TensorProduct Classical
open Module
namespace D04
universe u
abbrev Covector := Specs.D04.C13.NormalizedFormsAndWedge.Model.Covector
abbrev MultiIndex := Specs.D04.C13.NormalizedFormsAndWedge.Model.MultiIndex
abbrev indexTuple := @Specs.D04.C13.NormalizedFormsAndWedge.Model.indexTuple
abbrev scalarCovector := @Specs.D04.C13.NormalizedFormsAndWedge.Model.scalarCovector
abbrev covectorBasis := @Specs.D04.C13.NormalizedFormsAndWedge.Model.covectorBasis
abbrev dx := @Specs.D04.C13.NormalizedFormsAndWedge.Model.dx
abbrev coefficient := @Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient
abbrev covectorTensor := @Specs.D04.C13.NormalizedFormsAndWedge.Model.covectorTensor
abbrev averageAlternation := @Specs.D04.C13.NormalizedFormsAndWedge.Model.averageAlternation
abbrev wedge := @Specs.D04.C13.NormalizedFormsAndWedge.Model.wedge
abbrev linearCovector := @Specs.D04.C13.NormalizedFormsAndWedge.Model.linearCovector
abbrev wedgeList := @Specs.D04.C13.NormalizedFormsAndWedge.Model.wedgeList
abbrev IsShuffle := Specs.D04.C13.NormalizedFormsAndWedge.Model.IsShuffle
abbrev shuffleProduct := @Specs.D04.C13.NormalizedFormsAndWedge.Model.shuffleProduct
abbrev castCovector := @Specs.D04.C13.NormalizedFormsAndWedge.Model.castCovector
abbrev FormField := Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField
abbrev IsCrForm := Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm

section Algebra
variable {V : Type u} [AddCommGroup V] [Module ℝ V]
variable {n k p q : ℕ}

@[simp] theorem scalarCovector_apply (a : ℝ) (v : Fin 0 → V) :
    scalarCovector (V := V) a v = a := rfl

@[simp] theorem scalarCovector_symm_apply (ω : Covector V 0) :
    scalarCovector.symm ω = ω 0 := rfl

theorem covector_swap (ω : Covector V k) (v : Fin k → V)
    {i j : Fin k} (hij : i ≠ j) : ω (v ∘ Equiv.swap i j) = -ω v :=
  ω.map_swap v hij

/-- Determinant of coordinates, in the row/column order of the manuscript. -/
theorem dx_apply (b : Basis (Fin n) ℝ V) (I : MultiIndex n k) (v : Fin k → V) :
    dx b I v = Matrix.det (fun i j => b.repr (v j) (indexTuple I i)) := by
  change (exteriorPower.alternatingMapLinearEquiv (R := ℝ) (n := k)).symm
    ((b.exteriorPower k).dualBasis I) v = _
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  change (b.exteriorPower k).dualBasis I (exteriorPower.ιMulti ℝ k v) = _
  rw [Basis.dualBasis_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  exact Matrix.det_transpose _

theorem coefficient_eq_repr (b : Basis (Fin n) ℝ V) (ω : Covector V k)
    (I : MultiIndex n k) : coefficient b ω I = (covectorBasis b k).repr ω I := by
  change ω (fun j => b (indexTuple I j)) = _
  change _ = (b.exteriorPower k).dualBasis.repr
    (exteriorPower.alternatingMapLinearEquiv ω) I
  rw [Basis.dualBasis_repr, exteriorPower.basis_apply]
  exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).symm

theorem covector_expansion (b : Basis (Fin n) ℝ V) (ω : Covector V k) :
    ω = ∑ I : MultiIndex n k, coefficient b ω I • dx b I := by
  classical
  simp_rw [coefficient_eq_repr]
  exact ((covectorBasis b k).sum_repr ω).symm

theorem covector_expansion_unique (b : Basis (Fin n) ℝ V) (ω : Covector V k)
    (a : MultiIndex n k → ℝ) :
    (ω = ∑ I, a I • dx b I) ↔ a = coefficient b ω := by
  classical
  constructor
  · intro h
    funext I
    rw [coefficient_eq_repr, h]
    simp [dx, Specs.D04.C13.NormalizedFormsAndWedge.Model.dx, Finsupp.single_apply]
  · intro h
    subst a
    exact covector_expansion b ω

@[simp] theorem coefficient_dx (b : Basis (Fin n) ℝ V) (I J : MultiIndex n k) :
    coefficient b (dx b I) J = if I = J then 1 else 0 := by
  classical
  rw [coefficient_eq_repr]
  exact (covectorBasis b k).repr_self_apply I J

theorem dx_degree_zero (b : Basis (Fin n) ℝ V) (I : MultiIndex n 0)
    (v : Fin 0 → V) : dx b I v = 1 := by
  rw [dx_apply]
  exact Matrix.det_isEmpty

theorem covector_eq_zero_above_dimension [FiniteDimensional ℝ V]
    (hk : Module.finrank ℝ V < k) (ω : Covector V k) : ω = 0 := by
  ext v
  apply ω.map_linearDependent
  intro hi
  have h := hi.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h
  exact (not_le_of_gt hk) h

theorem covectorTensor_apply (α : Covector V p) (β : Covector V q)
    (v : Fin (p + q) → V) :
    covectorTensor α β v =
      α (fun i => v (Fin.castAdd q i)) * β (fun j => v (Fin.natAdd p j)) := by
  simp [covectorTensor, Specs.D04.C13.NormalizedFormsAndWedge.Model.covectorTensor]

theorem wedge_apply (α : Covector V p) (β : Covector V q) (v : Fin (p + q) → V) :
    wedge α β v = ((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹ *
      ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
        (α (fun i => v (σ (Fin.castAdd q i))) *
          β (fun j => v (σ (Fin.natAdd p j)))) := by
  simp only [wedge, Specs.D04.C13.NormalizedFormsAndWedge.Model.wedge,
    smul_apply, smul_eq_mul, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, covectorTensor_apply]

theorem wedge_add_left (α α' : Covector V p) (β : Covector V q) :
    wedge (α + α') β = wedge α β + wedge α' β := by
  ext v
  simp only [wedge_apply, add_apply, add_mul, smul_add,
    Finset.sum_add_distrib, mul_add]

theorem wedge_add_right (α : Covector V p) (β β' : Covector V q) :
    wedge α (β + β') = wedge α β + wedge α β' := by
  ext v
  simp only [wedge_apply, add_apply, mul_add, smul_add,
    Finset.sum_add_distrib]

theorem wedge_smul_left (c : ℝ) (α : Covector V p) (β : Covector V q) :
    wedge (c • α) β = c • wedge α β := by
  ext v
  simp only [wedge_apply, smul_apply, smul_eq_mul, mul_assoc]
  simp_rw [← smul_eq_mul c, smul_comm (Equiv.Perm.sign _) c]
  rw [← Finset.smul_sum]
  simp only [smul_eq_mul]
  ring

theorem wedge_smul_right (c : ℝ) (α : Covector V p) (β : Covector V q) :
    wedge α (c • β) = c • wedge α β := by
  ext v
  simp only [wedge_apply, smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm _ c, ← smul_eq_mul c, smul_comm (Equiv.Perm.sign _) c]
  rw [← Finset.smul_sum]
  simp only [smul_eq_mul]
  ring

/-- The exact factorial multiplying averaged alternation in the source. -/
theorem wedge_eq_average (α : Covector V p) (β : Covector V q) :
    wedge α β =
      (((p + q).factorial : ℝ) / ((p.factorial : ℝ) * (q.factorial : ℝ))) •
        averageAlternation (covectorTensor α β) := by
  unfold wedge Specs.D04.C13.NormalizedFormsAndWedge.Model.wedge
    averageAlternation Specs.D04.C13.NormalizedFormsAndWedge.Model.averageAlternation
  rw [smul_smul]
  congr 1
  have h : ((p + q).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- Averaging, rather than summing, fixes an already alternating map. -/
theorem averageAlternation_covector (ω : Covector V k) :
    averageAlternation ω.toMultilinearMap = ω := by
  unfold averageAlternation Specs.D04.C13.NormalizedFormsAndWedge.Model.averageAlternation
  rw [AlternatingMap.coe_alternatization]
  simp only [Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_smul]

theorem wedge_scalar_right (c : ℝ) (α : Covector V p) :
    wedge α (scalarCovector c) = c • α := by
  have ht : Specs.D04.C13.NormalizedFormsAndWedge.Model.covectorTensor α (scalarCovector c) = (c • α).toMultilinearMap := by
    ext v
    change α (fun i => v (Fin.castAdd 0 i)) * c = c * α v
    simp [mul_comm]
  unfold wedge Specs.D04.C13.NormalizedFormsAndWedge.Model.wedge
  rw [ht, AlternatingMap.coe_alternatization]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp only [Nat.add_zero, ← mul_assoc]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_mul]

/-- Bridge to the division-free product in the algebra foundation. -/
theorem wedge_eq_library (α : Covector V p) (β : Covector V q) :
    wedge α β = D05.M15.ExteriorPairing.AlternatingForms.shuffleProduct ℝ V α β := by
  have ht : Specs.D04.C13.NormalizedFormsAndWedge.Model.covectorTensor α β =
      (Specs.D05.M15.ExteriorPairing.AlternatingForms.tensorForm α β).domDomCongr
        finSumFinEquiv := by
    ext v
    rfl
  unfold wedge Specs.D04.C13.NormalizedFormsAndWedge.Model.wedge
  rw [ht, D05.M15.ExteriorPairing.AlternatingForms.alternatization_domDomCongr,
    D05.M15.ExteriorPairing.AlternatingForms.tensorForm_alternatization]
  rw [smul_smul, Nat.cast_mul,
    inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))), one_smul]

theorem castCovector_eq_domDomCongr {r s : ℕ} (h : r = s) (ω : Covector V r) :
    castCovector h ω = ω.domDomCongr (finCongr h) := by
  subst s
  rfl

theorem wedge_assoc [FiniteDimensional ℝ V] {r : ℕ}
    (α : Covector V p) (β : Covector V q) (γ : Covector V r) :
    castCovector (Nat.add_assoc p q r) (wedge (wedge α β) γ) = wedge α (wedge β γ) := by
  rw [castCovector_eq_domDomCongr]
  simpa only [wedge_eq_library] using
    D05.M15.ExteriorPairing.AlternatingForms.associativity p q r α β γ

theorem wedge_comm [FiniteDimensional ℝ V] (α : Covector V p) (β : Covector V q) :
    wedge α β = (-1 : ℝ) ^ (p * q) • castCovector (Nat.add_comm q p) (wedge β α) := by
  rw [castCovector_eq_domDomCongr]
  simpa only [wedge_eq_library] using
    D05.M15.ExteriorPairing.AlternatingForms.graded_commutativity p q α β

theorem wedge_shuffle_sum (α : Covector V p) (β : Covector V q)
    (v : Fin (p + q) → V) :
    wedge α β v = ∑ σ : {σ : Equiv.Perm (Fin (p + q)) // IsShuffle p q σ},
      Equiv.Perm.sign σ.val •
        (α (fun i => v (σ.val (Fin.castAdd q i))) *
          β (fun j => v (σ.val (Fin.natAdd p j)))) := by
  rw [wedge_eq_library]
  exact D05.M15.ExteriorPairing.AlternatingForms.shuffle_formula p q α β v


theorem wedge_shuffleProduct (α : Covector V p) (β : Covector V q)
    (v : Fin (p + q) → V) : wedge α β v = shuffleProduct α β v :=
  wedge_shuffle_sum α β v

theorem castCovector_trans {a b c : ℕ} (h : a = b) (h' : b = c) (ω : Covector V a) :
    castCovector h' (castCovector h ω) = castCovector (h.trans h') ω := by
  subst b
  subst c
  rfl

theorem wedge_scalar_left [FiniteDimensional ℝ V] (c : ℝ) (β : Covector V q) :
    castCovector (Nat.zero_add q) (wedge (scalarCovector c) β) = c • β := by
  rw [wedge_comm, Nat.zero_mul, pow_zero, one_smul, wedge_scalar_right]
  rw [castCovector_trans]
  rfl

/-- Canonical identification with the exterior power of the dual, over ℝ. -/
theorem covector_exterior_dual_equiv [FiniteDimensional ℝ V] (k : ℕ) :
    ∃ e : (⋀[ℝ]^k (Module.Dual ℝ V)) ≃ₗ[ℝ] Covector V k,
      ∀ a v, e a v = exteriorPower.pairingDual ℝ V k a (exteriorPower.ιMulti ℝ k v) := by
  obtain ⟨e, he⟩ := D05.M15.ExteriorPairing.AlternatingForms.identification
    (K := ℝ) (V := V) k
  refine ⟨e, fun a v => ?_⟩
  change e.toLinearMap a v = _
  rw [he]
  exact D05.M15.ExteriorPairing.AlternatingForms.evaluation k a v

theorem linearCovector_apply (f : Module.Dual ℝ V) (v : Fin 1 → V) :
    linearCovector f v = f (v 0) := rfl

theorem linearCovector_eq_toForm (f : Module.Dual ℝ V) :
    linearCovector f = D05.M15.ExteriorPairing.AlternatingForms.toForm ℝ V 1
      (exteriorPower.ιMulti ℝ 1 (fun _ => f)) := by
  ext v
  rw [linearCovector_apply, D05.M15.ExteriorPairing.AlternatingForms.elementary]
  simp

theorem wedgeList_eq_toForm (k : ℕ) (f : Fin k → Module.Dual ℝ V) :
    wedgeList k f = D05.M15.ExteriorPairing.AlternatingForms.toForm ℝ V k
      (exteriorPower.ιMulti ℝ k f) := by
  induction k with
  | zero =>
    ext v
    rw [D05.M15.ExteriorPairing.AlternatingForms.elementary]
    exact Matrix.det_isEmpty.symm
  | succ k ih =>
    change wedge (wedgeList k (Fin.init f)) (linearCovector (f (Fin.last k))) = _
    rw [wedge_eq_library, ih, linearCovector_eq_toForm,
      ← D05.M15.ExteriorPairing.AlternatingForms.multiplication_elementary]
    congr 1
    apply Subtype.ext
    change _root_.ExteriorAlgebra.ιMulti ℝ k (Fin.init f) *
      _root_.ExteriorAlgebra.ιMulti ℝ 1 (fun _ => f (Fin.last k)) =
        _root_.ExteriorAlgebra.ιMulti ℝ (k + 1) f
    rw [_root_.ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 1
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [Fin.append_right]
      rfl

theorem wedgeList_apply (k : ℕ) (f : Fin k → Module.Dual ℝ V) (v : Fin k → V) :
    wedgeList k f v = Matrix.det (fun i j => f i (v j)) := by
  rw [wedgeList_eq_toForm, D05.M15.ExteriorPairing.AlternatingForms.elementary]

theorem coordinate_wedge (b : Basis (Fin n) ℝ V) (I : MultiIndex n k) :
    wedgeList k (fun i => b.coord (indexTuple I i)) = dx b I := by
  ext v
  rw [wedgeList_apply, dx_apply]
  rfl

end Algebra

/-- The coefficient definition uses the previously fixed recursive Cʳ convention. -/
theorem isCrForm_finite_iff {n k : ℕ} (r : ℕ) (U : Set (E n)) (ω : FormField n k) :
    IsCrForm (some r) U ω ↔ IsOpen U ∧
      ∀ I : MultiIndex n k, CrOn r U (fun x => coefficient (standardBasis n) (ω x) I) :=
  Iff.rfl

theorem isCrForm_smooth_iff {n k : ℕ} (U : Set (E n)) (ω : FormField n k) :
    IsCrForm none U ω ↔ IsOpen U ∧
      ∀ I : MultiIndex n k, SmoothOn U (fun x => coefficient (standardBasis n) (ω x) I) :=
  Iff.rfl

theorem isCrForm_finite_contDiffOn {n k : ℕ} (r : ℕ) (U : Set (E n))
    (ω : FormField n k) (hU : IsOpen U) :
    IsCrForm (some r) U ω ↔
      ∀ I : MultiIndex n k, ContDiffOn ℝ (r : WithTop ℕ∞)
        (fun x => coefficient (standardBasis n) (ω x) I) U := by
  rw [isCrForm_finite_iff]
  simp only [hU, true_and]
  exact forall_congr' fun I => crOn_iff_contDiffOn r U _ hU

/-- In degree zero, the regularity condition is exactly regularity of a function. -/
theorem isCrForm_zero_iff {n : ℕ} (r : Option ℕ) (U : Set (E n)) (f : E n → ℝ) :
    IsCrForm r U (fun x => scalarCovector (V := E n) (f x)) ↔
      IsOpen U ∧ match r with
        | some s => CrOn s U f
        | none => SmoothOn U f := by
  change (IsOpen U ∧ ∀ I : MultiIndex n 0, _) ↔ _
  have hi : Nonempty (MultiIndex n 0) := ⟨⟨∅, Finset.card_empty⟩⟩
  cases r <;>
    simp only [Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient,
      scalarCovector_apply, forall_const]
    <;> rfl

end D04
