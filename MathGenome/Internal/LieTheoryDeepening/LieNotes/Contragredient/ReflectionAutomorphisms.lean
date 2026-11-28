import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.AdjointNilpotence
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.LocallyNilpotentExponential
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.ReflectionAutomorphisms
import Batteries.Tactic.OpenPrivate

namespace LieNotes.Contragredient.ReflectionAutomorphisms

open CartanQuotient LocallyNilpotentExponential

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

abbrev cartanReflection (R : Realization A H) (i : I) : H →ₗ[ℂ] H :=
  Specs.LieNotes.Contragredient.ReflectionAutomorphisms.cartanReflection R i

abbrev IsReflectionAutomorphism (R : Realization A H) (i : I)
    (r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R) : Prop :=
  Specs.LieNotes.Contragredient.ReflectionAutomorphisms.IsReflectionAutomorphism R i r

theorem cartanReflection_apply (R : Realization A H) (i : I) (h : H) :
    cartanReflection R i h = h - R.α i h • R.h i :=
  rfl

private theorem diagonal_pairing (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) : R.α i (R.h i) = 2 := by
  simp [R.pairing, hA.1 i]

theorem cartanReflection_involutive (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) : Function.Involutive (cartanReflection R i) := by
  intro h
  have hα : R.α i (cartanReflection R i h) = -R.α i h := by
    simp only [cartanReflection_apply, map_sub, map_smul, smul_eq_mul, diagonal_pairing hA R i]
    ring
  rw [cartanReflection_apply, hα, cartanReflection_apply, neg_smul, sub_neg_eq_add, sub_add_cancel]

private abbrev ad (R : Realization A H) := LieAlgebra.ad ℂ (Algebra R)

private theorem neg_f_ad_locally_nilpotent (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) : LocallyNilpotent (ad R (-f R i)) := by
  rw [map_neg]
  exact (show LocallyNilpotent (ad R (f R i)) from
    AdjointNilpotence.ad_f_locally_nilpotent hA R i).neg

/-- The simple Lie automorphism obtained by exponentiating the two simple adjoints. -/
def reflectionAutomorphism (hA : IsGeneralizedCartanMatrix A) (R : Realization A H)
    (i : I) : Algebra R ≃ₗ⁅ℂ⁆ Algebra R :=
  let E := adjointExp (e R i) (AdjointNilpotence.ad_e_locally_nilpotent hA R i)
  let F := adjointExp (-f R i) (neg_f_ad_locally_nilpotent hA R i)
  (E.trans F).trans E

private theorem exp_congr {V : Type*} [AddCommGroup V] [Module ℂ V]
    {D F : Module.End ℂ V} (hD : LocallyNilpotent D) (hF : LocallyNilpotent F) (h : D = F) :
    exp D hD = exp F hF := by
  subst F
  rfl

theorem reflectionAutomorphism_spec (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) :
    IsReflectionAutomorphism R i (reflectionAutomorphism hA R i) := by
  let hE : LocallyNilpotent (ad R (e R i)) := AdjointNilpotence.ad_e_locally_nilpotent hA R i
  let hF : LocallyNilpotent (ad R (f R i)) := AdjointNilpotence.ad_f_locally_nilpotent hA R i
  let hNegF := neg_f_ad_locally_nilpotent hA R i
  have hneg : exp (ad R (-f R i)) hNegF = exp (-ad R (f R i)) hF.neg :=
    exp_congr hNegF hF.neg (map_neg (ad R) (f R i))
  refine ⟨hE, hF, fun x ↦ ?_⟩
  change adjointExp (e R i) hE (adjointExp (-f R i) hNegF (adjointExp (e R i) hE x)) =
    exp (ad R (e R i)) hE (exp (-ad R (f R i)) hF.neg (exp (ad R (e R i)) hE x))
  simp only [adjointExp_apply, hneg]

theorem reflectionAutomorphism_existsUnique (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) :
    ∃! r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R, IsReflectionAutomorphism R i r := by
  refine ⟨reflectionAutomorphism hA R i, reflectionAutomorphism_spec hA R i, ?_⟩
  rintro r ⟨_, _, hr⟩
  obtain ⟨_, _, hcanonical⟩ := reflectionAutomorphism_spec hA R i
  ext x
  exact (hr x).trans (hcanonical x).symm

section ExponentialCalculations

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (D : Module.End ℂ V) (hD : LocallyNilpotent D) {x : V}

private theorem exp_eq_of_apply_eq_zero (hx : D x = 0) : exp D hD x = x := by
  rw [exp_apply D hD (n := 1) (by simpa only [pow_one] using hx)]
  simp

private theorem exp_eq_of_sq_apply_eq_zero (hx : D (D x) = 0) :
    exp D hD x = x + D x := by
  rw [exp_apply D hD (n := 2) (by simpa only [pow_succ', pow_zero, Module.End.mul_apply,
    Module.End.one_apply] using hx)]
  simp [Finset.sum_range_succ]

private theorem exp_eq_of_cube_apply_eq_zero (hx : D (D (D x)) = 0) :
    exp D hD x = x + D x + (2 : ℂ)⁻¹ • D (D x) := by
  rw [exp_apply D hD (n := 3) (by simpa only [pow_succ', pow_zero, Module.End.mul_apply,
    Module.End.one_apply] using hx)]
  norm_num [Finset.sum_range_succ, Nat.factorial, pow_succ', Module.End.mul_apply]

end ExponentialCalculations

theorem reflectionAutomorphism_onCartan (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) {r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R}
    (hr : IsReflectionAutomorphism R i r) (h : H) :
    r (cartan R h) = cartan R (cartanReflection R i h) := by
  obtain ⟨he, hf, hformula⟩ := hr
  let E : Module.End ℂ (Algebra R) := ad R (e R i)
  let G : Module.End ℂ (Algebra R) := -ad R (f R i)
  have hE : LocallyNilpotent E := he
  have hG : LocallyNilpotent G := hf.neg
  change ∀ x, r x = exp E hE (exp G hG (exp E hE x)) at hformula
  have E_e : E (e R i) = 0 := by
    change ⁅e R i, e R i⁆ = _
    rw [lie_self]
  have E_h (k : H) : E (cartan R k) = -(R.α i k • e R i) := by
    change ⁅e R i, cartan R k⁆ = _
    rw [← lie_skew, (definingRelations R).cartan_e]
  have G_h (k : H) : G (cartan R k) = -(R.α i k • f R i) := by
    change -⁅f R i, cartan R k⁆ = _
    rw [← lie_skew, neg_neg, (definingRelations R).cartan_f]
  have G_f : G (f R i) = 0 := by
    change -⁅f R i, f R i⁆ = _
    rw [lie_self, neg_zero]
  have G_e : G (e R i) = cartan R (R.h i) := by
    classical
    change -⁅f R i, e R i⁆ = _
    rw [← lie_skew, neg_neg]
    simpa using (definingRelations R).e_f i i
  have expE_h (k : H) : exp E hE (cartan R k) = cartan R k - R.α i k • e R i := by
    rw [exp_eq_of_sq_apply_eq_zero E hE (by rw [E_h, map_neg, map_smul, E_e, smul_zero,
      neg_zero]), E_h, sub_eq_add_neg]
  have expG_h (k : H) : exp G hG (cartan R k) = cartan R k - R.α i k • f R i := by
    rw [exp_eq_of_sq_apply_eq_zero G hG (by rw [G_h, map_neg, map_smul, G_f, smul_zero,
      neg_zero]), G_h, sub_eq_add_neg]
  have expG_e : exp G hG (e R i) = e R i + cartan R (R.h i) - f R i := by
    rw [exp_eq_of_cube_apply_eq_zero G hG (by rw [G_e, G_h, map_neg, map_smul, G_f, smul_zero,
      neg_zero]), G_e, G_h, diagonal_pairing hA R i, smul_neg, smul_smul,
      inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul, sub_eq_add_neg]
  have middle :
      exp G hG (cartan R h - R.α i h • e R i) =
        cartan R h - R.α i h • e R i - R.α i h • cartan R (R.h i) := by
    rw [map_sub, map_smul, expG_h, expG_e, smul_sub, smul_add]
    abel
  rw [hformula, expE_h, middle, map_sub, map_sub, map_smul, map_smul,
    exp_eq_of_apply_eq_zero E hE E_e, expE_h, expE_h, diagonal_pairing hA R i,
    cartanReflection_apply, map_sub, map_smul, smul_sub, smul_smul, mul_two, add_smul]
  abel

private theorem weightReflection_apply_cartan (R : Realization A H) (i : I)
    (β : Module.Dual ℂ H) (h : H) :
    R.weightReflection i β h = β (cartanReflection R i h) := by
  rw [Realization.weightReflection_apply, cartanReflection_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, smul_eq_mul, mul_comm (β (R.h i))]

theorem reflectionAutomorphism_onWeightSpaces (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) {r : Algebra R ≃ₗ⁅ℂ⁆ Algebra R}
    (hr : IsReflectionAutomorphism R i r) (β : Module.Dual ℂ H) :
    (weightSpace (cartanAdjoint R) β).map r.toLinearEquiv.toLinearMap =
      weightSpace (cartanAdjoint R) (R.weightReflection i β) := by
  have transport (s : Algebra R ≃ₗ⁅ℂ⁆ Algebra R)
      (hs : ∀ h, s (cartan R h) = cartan R (cartanReflection R i h))
      {γ : Module.Dual ℂ H} {x : Algebra R} (hx : x ∈ weightSpace (cartanAdjoint R) γ) :
      s x ∈ weightSpace (cartanAdjoint R) (R.weightReflection i γ) := by
    intro h
    change ⁅cartan R h, s x⁆ = R.weightReflection i γ h • s x
    have hx' : ⁅cartan R (cartanReflection R i h), x⁆ = γ (cartanReflection R i h) • x :=
      hx (cartanReflection R i h)
    have hcartan := hs (cartanReflection R i h)
    rw [cartanReflection_involutive hA R i h] at hcartan
    rw [← hcartan, ← LieEquiv.map_lie, hx', map_smul, weightReflection_apply_cartan]
  have hrCartan := reflectionAutomorphism_onCartan hA R i hr
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact transport r hrCartan hx
  · intro y hy
    have hrSymmCartan (h : H) : r.symm (cartan R h) = cartan R (cartanReflection R i h) := by
      apply r.injective
      change r (r.symm (cartan R h)) = r (cartan R (cartanReflection R i h))
      rw [LieEquiv.apply_symm_apply, hrCartan, cartanReflection_involutive hA R i h]
    refine ⟨r.symm y, ?_, r.apply_symm_apply y⟩
    change r.symm y ∈ weightSpace (cartanAdjoint R) β
    simpa only [Realization.weightReflection_involutive R hA i β] using
      transport r.symm hrSymmCartan hy

theorem rootLattice_preserved (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (i : I) :
    R.weightReflection i '' Set.range R.rootWeight = Set.range R.rootWeight := by
  ext μ
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨rootReflection A i q, Realization.rootWeight_rootReflection R i q⟩
  · rintro ⟨q, rfl⟩
    refine ⟨R.rootWeight (rootReflection A i q), Set.mem_range_self _, ?_⟩
    rw [← Realization.rootWeight_rootReflection, rootReflection_involutive hA i q]

section SimpleRootSpace

open private simpleDegree_positive positiveDegree_add from MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.TriangularGrading

omit [Finite I] in
private theorem positive_add_ne_simpleDegree (i : I) {q p : Q I}
    (hq : PositiveDegree q) (hp : PositiveDegree p) : q + p ≠ simpleDegree i := by
  intro heq
  have hoff (j : I) (hj : j ≠ i) : q j = 0 ∧ p j = 0 := by
    have h := DFunLike.congr_fun heq j
    change (q + p) j = Finsupp.single i (1 : ℤ) j at h
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hj] at h
    exact ⟨by have := hq.2 j; have := hp.2 j; omega,
      by have := hq.2 j; have := hp.2 j; omega⟩
  have hqi : q i ≠ 0 := by
    intro hz
    apply hq.1
    ext j
    simp only [Finsupp.zero_apply]
    by_cases hj : j = i
    · rwa [hj]
    · exact (hoff j hj).1
  have hpi : p i ≠ 0 := by
    intro hz
    apply hp.1
    ext j
    simp only [Finsupp.zero_apply]
    by_cases hj : j = i
    · rwa [hj]
    · exact (hoff j hj).2
  have h := DFunLike.congr_fun heq i
  change (q + p) i = Finsupp.single i (1 : ℤ) i at h
  rw [Finsupp.add_apply, Finsupp.single_eq_same] at h
  have hqi₀ := hq.2 i
  have hpi₀ := hp.2 i
  omega

private theorem positive_eq_lieSpan (R : Realization A H) :
    positive R = LieSubalgebra.lieSpan ℂ (Algebra R) (Set.range (e R)) := by
  change (LieSubalgebra.lieSpan ℂ (Presentation.Algebra R) (Set.range (Presentation.e R))).map
    (quotientMap R) = _
  rw [LieSubalgebra.map_lieSpan, ← Set.range_comp]
  rfl

/-- The homogeneous component of a simple root is the line through its generator. -/
theorem simpleRootSpace_eq_span (R : Realization A H) (i : I) :
    grade R (simpleDegree i) = ℂ ∙ e R i := by
  let S := {q : Q I | PositiveDegree q ∧ q ≠ simpleDegree i}
  let W : Submodule ℂ (Algebra R) := ⨆ q ∈ S, grade R q
  let T : Submodule ℂ (Algebra R) := ℂ ∙ e R i
  have grade_le_W {q : Q I} (hq : q ∈ S) : grade R q ≤ W :=
    le_iSup_of_le q (le_iSup (fun _ : q ∈ S ↦ grade R q) hq)
  have grade_le_positive {q : Q I} (hq : PositiveDegree q) :
      grade R q ≤ (positive R).toSubmodule := by
    rw [← iSup_positive_grade]
    exact le_iSup_of_le q (le_iSup (fun _ : PositiveDegree q ↦ grade R q) hq)
  have extend (a b : Algebra R) (hb : b ∈ (positive R).toSubmodule)
      (h : ∀ q, PositiveDegree q → ∀ z ∈ grade R q, ⁅a, z⁆ ∈ W) : ⁅a, b⁆ ∈ W := by
    have hle : (positive R).toSubmodule ≤ W.comap (ad R a) := by
      rw [← iSup_positive_grade]
      exact iSup_le fun q ↦ iSup_le fun hq ↦ fun z hz ↦ h q hq z hz
    exact hle hb
  have bracket_mem {x y : Algebra R} (hx : x ∈ (positive R).toSubmodule)
      (hy : y ∈ (positive R).toSubmodule) : ⁅x, y⁆ ∈ W := by
    apply extend x y hy
    intro p hp z hz
    rw [← lie_skew]
    apply W.neg_mem
    apply extend z x hx
    intro q hq v hv
    exact grade_le_W ⟨positiveDegree_add hp hq, positive_add_ne_simpleDegree i hp hq⟩
      (lie_mem_grade R hz hv)
  have hT : T ≤ grade R (simpleDegree i) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (e_mem_grade R i))
  have hspan : T ⊔ W ≤ (positive R).toSubmodule :=
    sup_le (hT.trans (grade_le_positive (simpleDegree_positive i)))
      (iSup_le fun q ↦ iSup_le fun hq ↦ grade_le_positive hq.1)
  let K : LieSubalgebra ℂ (Algebra R) :=
    { T ⊔ W with
      lie_mem' := fun hx hy ↦ Submodule.mem_sup_right (bracket_mem (hspan hx) (hspan hy)) }
  have hpos : positive R ≤ K := by
    rw [positive_eq_lieSpan]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨j, rfl⟩
    change e R j ∈ T ⊔ W
    classical
    by_cases hj : j = i
    · subst j
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · apply Submodule.mem_sup_right
      refine grade_le_W ⟨simpleDegree_positive j, fun hj' ↦ hj ?_⟩ (e_mem_grade R j)
      exact Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) hj'
  have hdisj : Disjoint (grade R (simpleDegree i)) W :=
    (grade_iSupIndep R).disjoint_biSup (show simpleDegree i ∉ S from fun h ↦ h.2 rfl)
  have hle : grade R (simpleDegree i) ≤ T ⊔ W :=
    (grade_le_positive (simpleDegree_positive i)).trans (show (positive R).toSubmodule ≤ T ⊔ W
      from hpos)
  change grade R (simpleDegree i) = T
  calc
    grade R (simpleDegree i) = grade R (simpleDegree i) ⊓ (T ⊔ W) :=
      (inf_eq_left.mpr hle).symm
    _ = T ⊔ (grade R (simpleDegree i) ⊓ W) := by
      rw [sup_comm T W, sup_comm T (grade R (simpleDegree i) ⊓ W)]
      exact (inf_sup_assoc_of_le W hT).symm
    _ = T := by rw [hdisj.eq_bot, sup_bot_eq]

private theorem simpleRootSpace_rank (R : Realization A H) (i : I) :
    Module.rank ℂ (weightSpace (cartanAdjoint R) (R.α i)) = 1 := by
  rw [← Realization.rootWeight_simple R i]
  change Module.rank ℂ (grade R (simpleDegree i)) = 1
  rw [simpleRootSpace_eq_span]
  refine rank_eq_one ⟨e R i, Submodule.mem_span_singleton_self _⟩ ?_ ?_
  · intro h
    exact e_ne_zero R i (congrArg Subtype.val h)
  · intro x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.property
    exact ⟨c, Subtype.ext hc⟩

end SimpleRootSpace

theorem realRoot_multiplicity (hA : IsGeneralizedCartanMatrix A)
    (R : Realization A H) (j : I) (w : List I) :
    Module.rank ℂ (weightSpace (cartanAdjoint R)
      (w.foldr (fun i β ↦ R.weightReflection i β) (R.α j))) = 1 := by
  induction w with
  | nil => exact simpleRootSpace_rank R j
  | cons i w ih =>
    let β : Module.Dual ℂ H := w.foldr (fun k γ ↦ R.weightReflection k γ) (R.α j)
    let r := reflectionAutomorphism hA R i
    have hm := reflectionAutomorphism_onWeightSpaces hA R i
      (reflectionAutomorphism_spec hA R i) β
    let E := r.toLinearEquiv.ofSubmodules (weightSpace (cartanAdjoint R) β)
      (weightSpace (cartanAdjoint R) (R.weightReflection i β)) hm
    exact E.rank_eq.symm.trans ih

end
end LieNotes.Contragredient.ReflectionAutomorphisms
