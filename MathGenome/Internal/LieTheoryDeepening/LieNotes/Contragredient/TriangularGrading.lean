import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanFreeness
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.WeightExtraction
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.TriangularGrading

/-! Triangular decomposition and root-lattice grading before the Cartan-disjoint quotient. -/

namespace LieNotes.Contragredient.Presentation

open scoped DirectSum

noncomputable section

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

abbrev cartanAdjoint (R : Realization A H) : H →ₗ[ℂ] Module.End ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.TriangularGrading.cartanAdjoint R

abbrev grade (R : Realization A H) (q : Q I) : Submodule ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.TriangularGrading.grade R q

abbrev triangularAdd (R : Realization A H) :
    (negative R × H × positive R) →ₗ[ℂ] Algebra R :=
  Specs.LieNotes.Contragredient.TriangularGrading.triangularAdd R

variable (R : Realization A H)

@[simp]
theorem cartanAdjoint_apply (h : H) (x : Algebra R) :
    cartanAdjoint R h x = ⁅cartan R h, x⁆ := rfl

theorem mem_grade {q : Q I} {x : Algebra R} :
    x ∈ grade R q ↔ ∀ h : H, ⁅cartan R h, x⁆ = R.rootWeight q h • x :=
  Iff.rfl

theorem cartan_mem_grade (h : H) : cartan R h ∈ grade R 0 := by
  rw [mem_grade]
  intro k
  simp

theorem e_mem_grade (i : I) : e R i ∈ grade R (simpleDegree i) := by
  apply (mem_grade R).mpr
  intro h
  rw [Realization.rootWeight_simple, lie_cartan_e]

theorem f_mem_grade (i : I) : f R i ∈ grade R (-simpleDegree i) := by
  apply (mem_grade R).mpr
  intro h
  rw [map_neg, Realization.rootWeight_simple, LinearMap.neg_apply, neg_smul, lie_cartan_f]

theorem lie_mem_grade {q p : Q I} {x y : Algebra R}
    (hx : x ∈ grade R q) (hy : y ∈ grade R p) :
    ⁅x, y⁆ ∈ grade R (q + p) := by
  apply (mem_grade R).mpr
  intro h
  rw [leibniz_lie, (mem_grade R).mp hx h, (mem_grade R).mp hy h,
    lie_smul, smul_lie, ← add_smul, map_add, LinearMap.add_apply]

section

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

private theorem lie_mem_flip {W : Submodule ℂ L} {x y : L} (h : ⁅x, y⁆ ∈ W) : ⁅y, x⁆ ∈ W := by
  rw [← lie_skew]
  exact W.neg_mem h

private theorem lie_lieSpan_mem {s : Set L} {W : Submodule ℂ L} {a x : L}
    (hgen : ∀ b ∈ s, ⁅a, b⁆ ∈ W)
    (hstable : ∀ {b c}, b ∈ LieSubalgebra.lieSpan ℂ L s → c ∈ W → ⁅b, c⁆ ∈ W)
    (hx : x ∈ LieSubalgebra.lieSpan ℂ L s) : ⁅a, x⁆ ∈ W := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem b hb => exact hgen b hb
  | zero => simpa only [lie_zero] using W.zero_mem
  | add b c _ _ hb hc => simpa only [lie_add] using W.add_mem hb hc
  | smul t b _ hb => simpa only [lie_smul] using W.smul_mem t hb
  | lie b c hb hc ihb ihc =>
      rw [leibniz_lie]
      exact W.add_mem (lie_mem_flip (hstable hc ihb)) (hstable hb ihc)

private theorem lie_sup_mem {T U W : Submodule ℂ L} {a x : L}
    (hT : ∀ b ∈ T, ⁅a, b⁆ ∈ W) (hU : ∀ b ∈ U, ⁅a, b⁆ ∈ W)
    (hx : x ∈ T ⊔ U) : ⁅a, x⁆ ∈ W := by
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  rw [lie_add]
  exact W.add_mem (hT b hb) (hU c hc)

/-- The elements whose adjoints preserve a submodule form a Lie subalgebra. -/
private def adjointStabilizer (W : Submodule ℂ L) : LieSubalgebra ℂ L where
  carrier := {a | ∀ b ∈ W, ⁅a, b⁆ ∈ W}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb c hc
    rw [add_lie]
    exact W.add_mem (ha c hc) (hb c hc)
  smul_mem' := by
    intro t a ha b hb
    rw [smul_lie]
    exact W.smul_mem t (ha b hb)
  lie_mem' := by
    intro a b ha hb c hc
    rw [lie_lie]
    exact W.sub_mem (ha _ (hb _ hc)) (hb _ (ha _ hc))

end

private theorem e_mem_positive (i : I) : e R i ∈ positive R :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self i)

private theorem f_mem_negative (i : I) : f R i ∈ negative R :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self i)

private theorem lie_cartan_positive (h : H) {x : Algebra R} (hx : x ∈ positive R) :
    ⁅cartan R h, x⁆ ∈ positive R := by
  apply lie_lieSpan_mem _ (fun hb hc ↦ (positive R).lie_mem hb hc) hx
  rintro _ ⟨i, rfl⟩
  rw [lie_cartan_e]
  exact (positive R).smul_mem _ (e_mem_positive R i)

private theorem lie_cartan_negative (h : H) {x : Algebra R} (hx : x ∈ negative R) :
    ⁅cartan R h, x⁆ ∈ negative R := by
  apply lie_lieSpan_mem _ (fun hb hc ↦ (negative R).lie_mem hb hc) hx
  rintro _ ⟨i, rfl⟩
  rw [lie_cartan_f]
  exact (negative R).neg_mem ((negative R).smul_mem _ (f_mem_negative R i))

private theorem lie_e_negative (i : I) {x : Algebra R} (hx : x ∈ negative R) :
    ⁅e R i, x⁆ ∈ (negative R).toSubmodule ⊔ (cartan R).range := by
  classical
  apply lie_lieSpan_mem _ (fun hb hc ↦ ?_) hx
  · rintro _ ⟨j, rfl⟩
    rw [lie_e_f]
    split_ifs
    · exact Submodule.mem_sup_right (LinearMap.mem_range_self _ _)
    · exact Submodule.zero_mem _
  · refine lie_sup_mem (fun _ hy ↦ Submodule.mem_sup_left ((negative R).lie_mem hb hy)) ?_ hc
    rintro _ ⟨h, rfl⟩
    exact Submodule.mem_sup_left (lie_mem_flip (lie_cartan_negative R h hb))

private theorem lie_f_positive (i : I) {x : Algebra R} (hx : x ∈ positive R) :
    ⁅f R i, x⁆ ∈ (cartan R).range ⊔ (positive R).toSubmodule := by
  classical
  apply lie_lieSpan_mem _ (fun hb hc ↦ ?_) hx
  · rintro _ ⟨j, rfl⟩
    apply lie_mem_flip
    rw [lie_e_f]
    split_ifs
    · exact Submodule.mem_sup_left (LinearMap.mem_range_self _ _)
    · exact Submodule.zero_mem _
  · refine lie_sup_mem ?_ (fun _ hy ↦ Submodule.mem_sup_right ((positive R).lie_mem hb hy)) hc
    rintro _ ⟨h, rfl⟩
    exact Submodule.mem_sup_right (lie_mem_flip (lie_cartan_positive R h hb))

private abbrev triangularSpan : Submodule ℂ (Algebra R) :=
  (negative R).toSubmodule ⊔ ((cartan R).range ⊔ (positive R).toSubmodule)

private theorem triangularSpan_eq_top : triangularSpan R = ⊤ := by
  let W := triangularSpan R
  have hN : (negative R).toSubmodule ≤ W := le_sup_left
  have hH : (cartan R).range ≤ W := le_sup_left.trans le_sup_right
  have hP : (positive R).toSubmodule ≤ W := le_sup_right.trans le_sup_right
  have hstab : adjointStabilizer W = ⊤ := by
    apply top_unique
    rw [← generated R]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ((⟨h, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) x hx
    · apply lie_sup_mem (fun _ hy ↦ hN (lie_cartan_negative R h hy)) _ hx
      intro b hb
      apply lie_sup_mem _ (fun _ hy ↦ hP (lie_cartan_positive R h hy)) hb
      rintro _ ⟨k, rfl⟩
      simpa only [lie_cartan_cartan] using W.zero_mem
    · apply lie_sup_mem (fun _ hy ↦ sup_le hN hH (lie_e_negative R i hy)) _ hx
      intro b hb
      apply lie_sup_mem _ (fun _ hy ↦ hP ((positive R).lie_mem (e_mem_positive R i) hy)) hb
      rintro _ ⟨h, rfl⟩
      exact hP (lie_mem_flip (lie_cartan_positive R h (e_mem_positive R i)))
    · apply lie_sup_mem (fun _ hy ↦ hN ((negative R).lie_mem (f_mem_negative R i) hy)) _ hx
      intro b hb
      apply lie_sup_mem _ (fun _ hy ↦ sup_le hH hP (lie_f_positive R i hy)) hb
      rintro _ ⟨h, rfl⟩
      exact hN (lie_mem_flip (lie_cartan_negative R h (f_mem_negative R i)))
  let K : LieSubalgebra ℂ (Algebra R) :=
    { W with
      lie_mem' := fun {x y} _ hy ↦
        (show x ∈ adjointStabilizer W by rw [hstab]; trivial) y hy }
  have hK : K = ⊤ := by
    apply top_unique
    rw [← generated R]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ((⟨h, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact hH (LinearMap.mem_range_self _ _)
    · exact hP (e_mem_positive R i)
    · exact hN (f_mem_negative R i)
  exact congrArg LieSubalgebra.toSubmodule hK

/-- The span of the homogeneous components in a specified set of degrees. -/
private def gradeSpan (s : Set (Q I)) : Submodule ℂ (Algebra R) :=
  ⨆ q ∈ s, grade R q

private theorem grade_le_gradeSpan {s : Set (Q I)} {q : Q I} (hq : q ∈ s) :
    grade R q ≤ gradeSpan R s :=
  le_iSup_of_le q (le_iSup (fun _ : q ∈ s ↦ grade R q) hq)

private theorem gradeSpan_mono {s t : Set (Q I)} (h : s ⊆ t) :
    gradeSpan R s ≤ gradeSpan R t :=
  iSup_le fun _ ↦ iSup_le fun hq ↦ grade_le_gradeSpan R (h hq)

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem lie_mem_gradeSpan_right {s : Set (Q I)} {x y : Algebra R}
    (hy : y ∈ gradeSpan R s)
    (h : ∀ q ∈ s, ∀ z ∈ grade R q, ⁅x, z⁆ ∈ gradeSpan R s) :
    ⁅x, y⁆ ∈ gradeSpan R s := by
  let T := (LieAlgebra.ad ℂ (Algebra R) x)
  have hle : gradeSpan R s ≤ (gradeSpan R s).comap T :=
    iSup_le fun q ↦ iSup_le fun hq z hz ↦ h q hq z hz
  exact hle hy

private def gradedSubalgebra (s : Set (Q I))
    (hadd : ∀ {q p : Q I}, q ∈ s → p ∈ s → q + p ∈ s) :
    LieSubalgebra ℂ (Algebra R) where
  __ := gradeSpan R s
  lie_mem' := by
    intro x y hx hy
    apply lie_mem_gradeSpan_right R hy
    intro p hp v hv
    apply lie_mem_flip
    apply lie_mem_gradeSpan_right R hx
    intro q hq u hu
    exact grade_le_gradeSpan R (hadd hp hq) (lie_mem_grade R hv hu)

omit [Finite I] in
private theorem simpleDegree_positive (i : I) : PositiveDegree (simpleDegree i) := by
  change Finsupp.single i (1 : ℤ) ≠ 0 ∧ ∀ j, 0 ≤ Finsupp.single i (1 : ℤ) j
  refine ⟨Finsupp.single_ne_zero.mpr one_ne_zero, fun j ↦ ?_⟩
  by_cases h : j = i
  · subst j
    simp
  · rw [Finsupp.single_eq_of_ne h]

omit [Finite I] in
private theorem positiveDegree_add {q p : Q I} (hq : PositiveDegree q) (hp : PositiveDegree p) :
    PositiveDegree (q + p) := by
  refine ⟨?_, fun i ↦ by rw [Finsupp.add_apply]; exact add_nonneg (hq.2 i) (hp.2 i)⟩
  intro hzero
  apply hq.1
  apply Finsupp.ext
  intro i
  have h := DFunLike.congr_fun hzero i
  rw [Finsupp.add_apply, Finsupp.zero_apply] at h
  rw [Finsupp.zero_apply]
  have hq' := hq.2 i
  have hp' := hp.2 i
  omega

omit [Finite I] in
private theorem negativeDegree_add {q p : Q I} (hq : NegativeDegree q) (hp : NegativeDegree p) :
    NegativeDegree (q + p) := by
  change PositiveDegree (-(q + p))
  rw [neg_add]
  exact positiveDegree_add hq hp

private theorem positive_le_gradeSpan :
    (positive R).toSubmodule ≤ gradeSpan R {q | PositiveDegree q} := by
  change positive R ≤ gradedSubalgebra R {q | PositiveDegree q} (fun hq hp ↦ positiveDegree_add hq hp)
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨i, rfl⟩
  exact grade_le_gradeSpan R (s := {q | PositiveDegree q}) (simpleDegree_positive i) (e_mem_grade R i)

private theorem negative_le_gradeSpan :
    (negative R).toSubmodule ≤ gradeSpan R {q | NegativeDegree q} := by
  change negative R ≤ gradedSubalgebra R {q | NegativeDegree q} (fun hq hp ↦ negativeDegree_add hq hp)
  apply LieSubalgebra.lieSpan_le.mpr
  rintro _ ⟨i, rfl⟩
  have hi : NegativeDegree (-simpleDegree i) := by
    change PositiveDegree (- -simpleDegree i)
    rw [neg_neg]
    exact simpleDegree_positive i
  exact grade_le_gradeSpan R (s := {q | NegativeDegree q}) hi (f_mem_grade R i)

private theorem cartan_range_le_grade_zero : (cartan R).range ≤ grade R 0 := by
  rintro _ ⟨h, rfl⟩
  exact cartan_mem_grade R h

/-- All the lattice weight spaces together span the presented algebra. -/
theorem iSup_grade_eq_top : (⨆ q, grade R q) = ⊤ := by
  have hspan (s : Set (Q I)) : gradeSpan R s ≤ ⨆ q, grade R q :=
    iSup_le fun q ↦ iSup_le fun _ ↦ le_iSup (grade R) q
  apply top_unique
  rw [← triangularSpan_eq_top R]
  exact sup_le ((negative_le_gradeSpan R).trans (hspan _)) <|
    sup_le ((cartan_range_le_grade_zero R).trans (le_iSup (grade R) 0))
      ((positive_le_gradeSpan R).trans (hspan _))

/-- The simple roots are independent, so distinct degrees label independent spaces. -/
theorem grade_iSupIndep : iSupIndep (grade R) :=
  (weightSpace_iSupIndep (cartanAdjoint R)).comp (Realization.rootWeight_injective R)

theorem grade_isInternal [DecidableEq (Q I)] (R : Realization A H) : DirectSum.IsInternal (grade R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (grade_iSupIndep R) (iSup_grade_eq_top R)

/-- Mathlib's graded Lie algebra structure on the root-lattice components. -/
@[instance_reducible]
def gradedLieAlgebra [DecidableEq (Q I)] (R : Realization A H) : GradedLieAlgebra (grade R) where
  toDecomposition := (grade_isInternal R).chooseDecomposition
  bracket_mem := by
    intro q p x y hx hy
    exact lie_mem_grade R hx hy

/-- Recomposition by addition of the finitely many homogeneous components. -/
def gradeAdditionEquiv [DecidableEq (Q I)] (R : Realization A H) :
    (⨁ q, grade R q) ≃ₗ[ℂ] Algebra R :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (grade R)) (grade_isInternal R)

theorem exists_gradeAdditionEquiv [DecidableEq (Q I)] (R : Realization A H) :
    ∃ E : (⨁ q, grade R q) ≃ₗ[ℂ] Algebra R,
      E.toLinearMap = DirectSum.coeLinearMap (grade R) :=
  ⟨gradeAdditionEquiv R, rfl⟩

theorem weightSpace_eq_bot_of_notMem_range (μ : Module.Dual ℂ H)
    (hμ : μ ∉ Set.range R.rootWeight) :
    weightSpace (cartanAdjoint R) μ = ⊥ := by
  have hd := (weightSpace_iSupIndep (cartanAdjoint R)).disjoint_biSup hμ
  rw [iSup_range] at hd
  change Disjoint (weightSpace (cartanAdjoint R) μ) (⨆ q, grade R q) at hd
  rw [iSup_grade_eq_top, disjoint_top] at hd
  exact hd

omit [Finite I] in
private theorem not_negativeDegree_of_positive {q : Q I} (hq : PositiveDegree q) :
    ¬ NegativeDegree q := by
  intro hn
  apply hq.1
  apply Finsupp.ext
  intro i
  have hi := hn.2 i
  rw [Finsupp.neg_apply] at hi
  exact le_antisymm (neg_nonneg.mp hi) (hq.2 i)

omit [Finite I] in
private theorem negativeDegree_ne_zero {q : Q I} (hq : NegativeDegree q) : q ≠ 0 := by
  rintro rfl
  exact hq.1 (neg_zero : -(0 : Q I) = 0)

private theorem gradeSpan_disjoint_compl (s : Set (Q I)) :
    Disjoint (gradeSpan R s) (gradeSpan R sᶜ) :=
  (grade_iSupIndep R).disjoint_biSup_biSup disjoint_compl_right

private theorem cartan_le_gradeSpan {s : Set (Q I)} (h : 0 ∈ s) :
    (cartan R).range ≤ gradeSpan R s :=
  (cartan_range_le_grade_zero R).trans (grade_le_gradeSpan R h)

private theorem gradeSpan_eq_of_sup_eq_top {s : Set (Q I)} {T U : Submodule ℂ (Algebra R)}
    (hT : T ≤ gradeSpan R s) (hU : U ≤ gradeSpan R sᶜ) (hspan : T ⊔ U = ⊤) :
    gradeSpan R s = T := by
  have hd := (gradeSpan_disjoint_compl R s).mono_right hU
  calc
    gradeSpan R s = gradeSpan R s ⊓ (T ⊔ U) := by rw [hspan, inf_top_eq]
    _ = T ⊔ (gradeSpan R s ⊓ U) := by
      simpa only [sup_comm] using (inf_sup_assoc_of_le U hT).symm
    _ = T := by rw [hd.eq_bot, sup_bot_eq]

private theorem cartan_sup_positive_le_negative_compl :
    (cartan R).range ⊔ (positive R).toSubmodule ≤ gradeSpan R {q | NegativeDegree q}ᶜ := by
  apply sup_le
  · exact cartan_le_gradeSpan R (fun h ↦ negativeDegree_ne_zero h rfl)
  · exact (positive_le_gradeSpan R).trans
      (gradeSpan_mono R (fun _ h ↦ not_negativeDegree_of_positive h))

private theorem negative_sup_positive_le_zero_compl :
    (negative R).toSubmodule ⊔ (positive R).toSubmodule ≤ gradeSpan R ({0} : Set (Q I))ᶜ :=
  sup_le
    ((negative_le_gradeSpan R).trans (gradeSpan_mono R fun _ h ↦ negativeDegree_ne_zero h))
    ((positive_le_gradeSpan R).trans (gradeSpan_mono R fun _ h ↦ h.1))

theorem grade_zero : grade R 0 = (cartan R).range := by
  have hcartan : (cartan R).range ≤ gradeSpan R ({0} : Set (Q I)) :=
    cartan_le_gradeSpan R (Set.mem_singleton 0)
  have hspan : (cartan R).range ⊔ ((negative R).toSubmodule ⊔ (positive R).toSubmodule) = ⊤ := by
    rw [sup_left_comm]
    exact triangularSpan_eq_top R
  have heq := gradeSpan_eq_of_sup_eq_top R hcartan (negative_sup_positive_le_zero_compl R) hspan
  simpa only [gradeSpan, iSup_singleton] using heq

theorem iSup_negative_grade :
    (⨆ q, ⨆ (_ : NegativeDegree q), grade R q) = (negative R).toSubmodule :=
  gradeSpan_eq_of_sup_eq_top R (negative_le_gradeSpan R)
    (cartan_sup_positive_le_negative_compl R) (triangularSpan_eq_top R)

theorem iSup_positive_grade :
    (⨆ q, ⨆ (_ : PositiveDegree q), grade R q) = (positive R).toSubmodule := by
  have hle : (negative R).toSubmodule ⊔ (cartan R).range ≤ gradeSpan R {q | PositiveDegree q}ᶜ := by
    apply sup_le
    · exact (negative_le_gradeSpan R).trans
        (gradeSpan_mono R (fun _ hn hp ↦ not_negativeDegree_of_positive hp hn))
    · exact cartan_le_gradeSpan R (fun h ↦ h.1 rfl)
  have hspan : (positive R).toSubmodule ⊔ ((negative R).toSubmodule ⊔ (cartan R).range) = ⊤ := by
    rw [sup_comm (positive R).toSubmodule, sup_assoc]
    exact triangularSpan_eq_top R
  exact gradeSpan_eq_of_sup_eq_top R (positive_le_gradeSpan R) hle hspan

theorem grade_eq_bot_of_not_positive_or_negative (q : Q I)
    (hq : q ≠ 0) (hp : ¬ PositiveDegree q) (hn : ¬ NegativeDegree q) : grade R q = ⊥ := by
  have hspan : triangularSpan R ≤ gradeSpan R {p | p ≠ q} :=
    sup_le ((negative_le_gradeSpan R).trans (gradeSpan_mono R fun _ h e ↦ hn (e ▸ h))) <|
      sup_le (cartan_le_gradeSpan R (Ne.symm hq))
        ((positive_le_gradeSpan R).trans (gradeSpan_mono R fun _ h e ↦ hp (e ▸ h)))
  have hd : Disjoint (grade R q) (gradeSpan R {p | p ≠ q}) :=
    (grade_iSupIndep R).disjoint_biSup (not_not_intro rfl : q ∉ {p | p ≠ q})
  have hd' := hd.mono_right hspan
  rw [triangularSpan_eq_top, disjoint_top] at hd'
  exact hd'

theorem triangularAdd_apply (x : negative R) (h : H) (y : positive R) :
    triangularAdd R (x, h, y) = (x : Algebra R) + (cartan R h + (y : Algebra R)) :=
  rfl

theorem triangularAdd_bijective : Function.Bijective (triangularAdd R) := by
  let N := (negative R).toSubmodule
  let P := (positive R).toSubmodule
  have hNP : Disjoint N ((cartan R).range ⊔ P) :=
    (gradeSpan_disjoint_compl R {q | NegativeDegree q}).mono
      (negative_le_gradeSpan R) (cartan_sup_positive_le_negative_compl R)
  have hHP : Disjoint (cartan R).range P :=
    (gradeSpan_disjoint_compl R ({0} : Set (Q I))).mono
      (cartan_le_gradeSpan R (Set.mem_singleton 0))
      (le_sup_right.trans (negative_sup_positive_le_zero_compl R))
  change Function.Bijective (N.subtype.coprod ((cartan R).coprod P.subtype))
  constructor
  · have hOuter : Disjoint N.subtype.range ((cartan R).coprod P.subtype).range := by
      simpa only [Submodule.range_subtype, LinearMap.range_coprod] using hNP
    have hInner : Disjoint (cartan R).range P.subtype.range := by
      simpa only [Submodule.range_subtype] using hHP
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hOuter,
      LinearMap.ker_coprod_of_disjoint_range _ _ hInner, Submodule.ker_subtype,
      Submodule.ker_subtype, LinearMap.ker_eq_bot.mpr (cartan_injective R), Submodule.prod_bot,
      Submodule.prod_bot]
  · rw [← LinearMap.range_eq_top, LinearMap.range_coprod, LinearMap.range_coprod,
      Submodule.range_subtype, Submodule.range_subtype]
    exact triangularSpan_eq_top R

/-- Add the three triangular components, using the Cartan embedding in the middle. -/
def triangularAdditionEquiv : (negative R × H × positive R) ≃ₗ[ℂ] Algebra R :=
  LinearEquiv.ofBijective (triangularAdd R) (triangularAdd_bijective R)

theorem exists_triangularAdditionEquiv :
    ∃ E : (negative R × H × positive R) ≃ₗ[ℂ] Algebra R,
      E.toLinearMap = triangularAdd R :=
  ⟨triangularAdditionEquiv R, rfl⟩

end

end LieNotes.Contragredient.Presentation
