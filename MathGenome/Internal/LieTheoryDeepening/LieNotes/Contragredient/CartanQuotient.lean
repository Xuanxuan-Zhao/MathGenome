import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.TriangularGrading
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanQuotient

namespace LieNotes.Contragredient.CartanQuotient

open scoped DirectSum

noncomputable section

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

abbrev cartanDisjointIdeal (R : Realization A H) : LieIdeal ℂ (Presentation.Algebra R) :=
  Specs.LieNotes.Contragredient.CartanQuotient.cartanDisjointIdeal R

abbrev Algebra (R : Realization A H) := Specs.LieNotes.Contragredient.CartanQuotient.Algebra R

abbrev quotientMap (R : Realization A H) : Presentation.Algebra R →ₗ⁅ℂ⁆ Algebra R :=
  Specs.LieNotes.Contragredient.CartanQuotient.quotientMap R

abbrev cartan (R : Realization A H) : H →ₗ[ℂ] Algebra R :=
  Specs.LieNotes.Contragredient.CartanQuotient.cartan R

abbrev e (R : Realization A H) (i : I) : Algebra R :=
  Specs.LieNotes.Contragredient.CartanQuotient.e R i

abbrev f (R : Realization A H) (i : I) : Algebra R :=
  Specs.LieNotes.Contragredient.CartanQuotient.f R i

abbrev negative (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.CartanQuotient.negative R

abbrev positive (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.CartanQuotient.positive R

abbrev cartanAdjoint (R : Realization A H) : H →ₗ[ℂ] Module.End ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.CartanQuotient.cartanAdjoint R

abbrev grade (R : Realization A H) (q : Q I) : Submodule ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.CartanQuotient.grade R q

abbrev triangularAdd (R : Realization A H) :
    (negative R × H × positive R) →ₗ[ℂ] Algebra R :=
  Specs.LieNotes.Contragredient.CartanQuotient.triangularAdd R


variable (R : Realization A H)

private theorem ideal_le_nonzero_grades (J : LieIdeal ℂ (Presentation.Algebra R))
    (hJ : Disjoint J.toSubmodule (Presentation.cartan R).range) :
    J.toSubmodule ≤ ⨆ (q : Q I) (_ : q ≠ 0), Presentation.grade R q := by
  have hsplit :
      (⨆ q, J.toSubmodule ⊓ Presentation.grade R q) = J.toSubmodule :=
    iSup_inf_weightSpace_eq (Presentation.cartanAdjoint R) J.toSubmodule
      (fun h _ hx ↦ J.lie_mem (x := Presentation.cartan R h) hx)
      R.rootWeight (Realization.rootWeight_injective R) (Presentation.iSup_grade_eq_top R)
  rw [← hsplit]
  refine iSup_le fun q ↦ ?_
  by_cases hq : q = 0
  · subst q
    rw [Presentation.grade_zero, hJ.eq_bot]
    exact bot_le
  · exact inf_le_right.trans (le_iSup_of_le q (le_iSup (fun _ : q ≠ 0 ↦
      Presentation.grade R q) hq))

theorem cartanDisjointIdeal_isGreatest :
    IsGreatest {J : LieIdeal ℂ (Presentation.Algebra R) |
      Disjoint J.toSubmodule (Presentation.cartan R).range} (cartanDisjointIdeal R) := by
  have hd : Disjoint (Presentation.grade R 0)
      (⨆ (q : Q I) (_ : q ≠ 0), Presentation.grade R q) :=
    (Presentation.grade_iSupIndep R).disjoint_biSup
      (show (0 : Q I) ∉ {q | q ≠ 0} from fun h ↦ h rfl)
  refine ⟨?_, ?_⟩
  · change Disjoint (cartanDisjointIdeal R).toSubmodule (Presentation.cartan R).range
    rw [← Presentation.grade_zero]
    apply hd.symm.mono_left
    simp only [cartanDisjointIdeal, Specs.LieNotes.Contragredient.CartanQuotient.cartanDisjointIdeal,
      LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun J ↦ iSup_le fun hJ ↦ ideal_le_nonzero_grades R J hJ
  · intro J hJ
    exact le_iSup_of_le J (le_iSup (fun _ : Disjoint J.toSubmodule
      (Presentation.cartan R).range ↦ J) hJ)

theorem quotientMap_surjective : Function.Surjective (quotientMap R) :=
  Quot.mk_surjective

@[simp]
theorem quotientMap_ker : (quotientMap R).ker = cartanDisjointIdeal R := by
  apply LieSubmodule.toSubmodule_injective
  rw [LieHom.ker_toSubmodule]
  exact Submodule.ker_mkQ _

theorem cartan_injective : Function.Injective (cartan R) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  have hker : Presentation.cartan R h ∈ (quotientMap R).ker := LieHom.mem_ker.mpr hh
  rw [quotientMap_ker] at hker
  have hz := Submodule.disjoint_def.mp (cartanDisjointIdeal_isGreatest R).1
    (Presentation.cartan R h) hker ⟨h, rfl⟩
  exact Presentation.cartan_injective R (hz.trans (map_zero _).symm)

theorem definingRelations : Presentation.Relations R (cartan R) (e R) (f R) := by
  classical
  constructor
  · intro h k
    change ⁅quotientMap R (Presentation.cartan R h), quotientMap R (Presentation.cartan R k)⁆ = 0
    rw [← LieHom.map_lie, Presentation.lie_cartan_cartan, map_zero]
  · intro h i
    change ⁅quotientMap R (Presentation.cartan R h), quotientMap R (Presentation.e R i)⁆ =
      R.α i h • quotientMap R (Presentation.e R i)
    rw [← LieHom.map_lie, Presentation.lie_cartan_e, map_smul]
  · intro h i
    change ⁅quotientMap R (Presentation.cartan R h), quotientMap R (Presentation.f R i)⁆ =
      -(R.α i h • quotientMap R (Presentation.f R i))
    rw [← LieHom.map_lie, Presentation.lie_cartan_f, map_neg, map_smul]
  · intro i j
    change ⁅quotientMap R (Presentation.e R i), quotientMap R (Presentation.f R j)⁆ =
      if i = j then quotientMap R (Presentation.cartan R (R.h i)) else 0
    rw [← LieHom.map_lie, Presentation.lie_e_f]
    split_ifs <;> simp only [map_zero]

private theorem lie_e_f_same (i : I) : ⁅e R i, f R i⁆ = cartan R (R.h i) := by
  classical
  simpa using (definingRelations R).e_f i i

private theorem simpleCoroot_ne_zero (i : I) : cartan R (R.h i) ≠ 0 := by
  intro h
  apply R.h_independent.ne_zero i
  exact cartan_injective R (h.trans (map_zero _).symm)

theorem e_ne_zero (i : I) : e R i ≠ 0 := by
  intro he
  exact simpleCoroot_ne_zero R i (by simpa [he] using (lie_e_f_same R i).symm)

theorem f_ne_zero (i : I) : f R i ≠ 0 := by
  intro hf
  exact simpleCoroot_ne_zero R i (by simpa [hf] using (lie_e_f_same R i).symm)

theorem generated :
    LieSubalgebra.lieSpan ℂ (Algebra R)
      (Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R)) = ⊤ := by
  have himage : (quotientMap R) ''
      (Set.range (Presentation.cartan R) ∪ Set.range (Presentation.e R) ∪
        Set.range (Presentation.f R)) =
      Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R) := by
    simp only [Set.image_union, ← Set.range_comp]
    rfl
  rw [← himage, ← LieSubalgebra.map_lieSpan, Presentation.generated, ← LieSubalgebra.map_top,
    LieHom.range_eq_top]
  exact quotientMap_surjective R

@[simp]
theorem cartanAdjoint_apply (h : H) (x : Algebra R) :
    cartanAdjoint R h x = ⁅cartan R h, x⁆ := rfl

theorem mem_grade {q : Q I} {x : Algebra R} :
    x ∈ grade R q ↔ ∀ h : H, ⁅cartan R h, x⁆ = R.rootWeight q h • x :=
  Iff.rfl

private theorem map_grade_le (q : Q I) :
    (Presentation.grade R q).map (quotientMap R).toLinearMap ≤ grade R q := by
  rintro _ ⟨x, hx, rfl⟩
  apply (mem_grade R).mpr
  intro h
  change ⁅quotientMap R (Presentation.cartan R h), quotientMap R x⁆ =
    R.rootWeight q h • quotientMap R x
  rw [← LieHom.map_lie, (Presentation.mem_grade R).mp hx h, map_smul]

private theorem iSup_grade_images_eq_top :
    (⨆ q, (Presentation.grade R q).map (quotientMap R).toLinearMap) = ⊤ := by
  rw [← Submodule.map_iSup, Presentation.iSup_grade_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (quotientMap_surjective R)

theorem iSup_grade_eq_top : (⨆ q, grade R q) = ⊤ :=
  top_unique ((iSup_grade_images_eq_top R).ge.trans (iSup_mono (map_grade_le R)))

theorem grade_iSupIndep : iSupIndep (grade R) :=
  (weightSpace_iSupIndep (cartanAdjoint R)).comp (Realization.rootWeight_injective R)

theorem grade_eq_map (q : Q I) :
    grade R q = (Presentation.grade R q).map (quotientMap R).toLinearMap := by
  let T := fun p ↦ (Presentation.grade R p).map (quotientMap R).toLinearMap
  change grade R q = T q
  have hdisj : Disjoint (grade R q) (⨆ p, ⨆ (_ : p ≠ q), T p) :=
    ((grade_iSupIndep R).disjoint_biSup (show q ∉ {p | p ≠ q} from fun h ↦ h rfl)).mono_right
      (iSup_mono fun p ↦ iSup_mono fun _ ↦ map_grade_le R p)
  have hspan : T q ⊔ (⨆ p, ⨆ (_ : p ≠ q), T p) = ⊤ := by
    rw [← iSup_split_single]
    exact iSup_grade_images_eq_top R
  have hle : T q ≤ grade R q := map_grade_le R q
  calc
    grade R q = grade R q ⊓ (T q ⊔ ⨆ p, ⨆ (_ : p ≠ q), T p) := by rw [hspan, inf_top_eq]
    _ = (grade R q ⊓ ⨆ p, ⨆ (_ : p ≠ q), T p) ⊔ T q := by
      rw [sup_comm, ← inf_sup_assoc_of_le _ hle]
    _ = T q := by rw [hdisj.eq_bot, bot_sup_eq]

theorem cartan_mem_grade (h : H) : cartan R h ∈ grade R 0 :=
  map_grade_le R 0 ⟨Presentation.cartan R h, Presentation.cartan_mem_grade R h, rfl⟩

theorem e_mem_grade (i : I) : e R i ∈ grade R (simpleDegree i) :=
  map_grade_le R _ ⟨Presentation.e R i, Presentation.e_mem_grade R i, rfl⟩

theorem f_mem_grade (i : I) : f R i ∈ grade R (-simpleDegree i) :=
  map_grade_le R _ ⟨Presentation.f R i, Presentation.f_mem_grade R i, rfl⟩

theorem lie_mem_grade {q p : Q I} {x y : Algebra R}
    (hx : x ∈ grade R q) (hy : y ∈ grade R p) :
    ⁅x, y⁆ ∈ grade R (q + p) := by
  rw [grade_eq_map] at hx hy ⊢
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact ⟨⁅x, y⁆, Presentation.lie_mem_grade R hx hy, (quotientMap R).map_lie x y⟩

theorem grade_isInternal [DecidableEq (Q I)] (R : Realization A H) :
    DirectSum.IsInternal (grade R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (grade_iSupIndep R) (iSup_grade_eq_top R)

theorem weightSpace_eq_bot_of_notMem_range (μ : Module.Dual ℂ H)
    (hμ : μ ∉ Set.range R.rootWeight) :
    weightSpace (cartanAdjoint R) μ = ⊥ := by
  have hd := (weightSpace_iSupIndep (cartanAdjoint R)).disjoint_biSup hμ
  rw [iSup_range] at hd
  change Disjoint (weightSpace (cartanAdjoint R) μ) (⨆ q, grade R q) at hd
  rw [iSup_grade_eq_top, disjoint_top] at hd
  exact hd

theorem grade_zero : grade R 0 = (cartan R).range := by
  rw [grade_eq_map, Presentation.grade_zero]
  exact (LinearMap.range_comp _ _).symm

theorem iSup_negative_grade :
    (⨆ q, ⨆ (_ : NegativeDegree q), grade R q) = (negative R).toSubmodule := by
  simp only [grade_eq_map, ← Submodule.map_iSup, Presentation.iSup_negative_grade]
  rfl

theorem iSup_positive_grade :
    (⨆ q, ⨆ (_ : PositiveDegree q), grade R q) = (positive R).toSubmodule := by
  simp only [grade_eq_map, ← Submodule.map_iSup, Presentation.iSup_positive_grade]
  rfl

theorem grade_eq_bot_of_not_positive_or_negative (q : Q I)
    (hq : q ≠ 0) (hp : ¬ PositiveDegree q) (hn : ¬ NegativeDegree q) :
    grade R q = ⊥ := by
  rw [grade_eq_map, Presentation.grade_eq_bot_of_not_positive_or_negative R q hq hp hn,
    Submodule.map_bot]

theorem triangularAdd_apply (x : negative R) (h : H) (y : positive R) :
    triangularAdd R (x, h, y) = (x : Algebra R) + (cartan R h + (y : Algebra R)) := rfl

private theorem cartan_sup_positive_le_nonnegative_grades :
    (cartan R).range ⊔ (positive R).toSubmodule ≤
      ⨆ q, ⨆ (_ : ¬ NegativeDegree q), grade R q := by
  rw [← grade_zero, ← iSup_positive_grade]
  refine sup_le (le_iSup_of_le 0 (le_iSup (fun _ : ¬ NegativeDegree (0 : Q I) ↦
    grade R 0) ?_)) (iSup_le fun q ↦ iSup_le fun hp ↦ ?_)
  · intro hn
    exact hn.1 (neg_zero : -(0 : Q I) = 0)
  · refine le_iSup_of_le q (le_iSup (fun _ : ¬ NegativeDegree q ↦ grade R q) ?_)
    intro hn
    apply hp.1
    apply Finsupp.ext
    intro i
    have hpos := hp.2 i
    have hneg : q i ≤ 0 := by
      simpa only [Finsupp.neg_apply, neg_nonneg] using hn.2 i
    exact le_antisymm hneg hpos

private theorem negative_disjoint_cartan_sup_positive :
    Disjoint (negative R).toSubmodule ((cartan R).range ⊔ (positive R).toSubmodule) := by
  rw [← iSup_negative_grade]
  have hd := (grade_iSupIndep R).disjoint_biSup_biSup
    (disjoint_compl_right : Disjoint {q : Q I | NegativeDegree q} {q | NegativeDegree q}ᶜ)
  exact hd.mono_right (cartan_sup_positive_le_nonnegative_grades R)

private theorem triangularAdd_surjective : Function.Surjective (triangularAdd R) := by
  intro y
  obtain ⟨x, rfl⟩ := quotientMap_surjective R y
  obtain ⟨⟨a, h, b⟩, rfl⟩ := (Presentation.triangularAdd_bijective R).2 x
  let a' : negative R := ⟨quotientMap R a, ⟨a, a.property, rfl⟩⟩
  let b' : positive R := ⟨quotientMap R b, ⟨b, b.property, rfl⟩⟩
  refine ⟨(a', h, b'), ?_⟩
  rw [triangularAdd_apply, Presentation.triangularAdd_apply, map_add, map_add]
  rfl

/-- The negative side complements the Cartan-plus-positive subspace. -/
theorem isCompl_negative_cartan_sup_positive :
    IsCompl (negative R).toSubmodule ((cartan R).range ⊔ (positive R).toSubmodule) := by
  refine ⟨negative_disjoint_cartan_sup_positive R, codisjoint_iff.mpr ?_⟩
  have hspan := LinearMap.range_eq_top.mpr (triangularAdd_surjective R)
  change ((negative R).toSubmodule.subtype.coprod
    ((cartan R).coprod (positive R).toSubmodule.subtype)).range = ⊤ at hspan
  simpa only [LinearMap.range_coprod, Submodule.range_subtype] using hspan

theorem triangularAdd_bijective : Function.Bijective (triangularAdd R) := by
  refine ⟨?_, triangularAdd_surjective R⟩
  have hHP : Disjoint (cartan R).range (positive R).toSubmodule := by
    rw [← grade_zero, ← iSup_positive_grade]
    exact (grade_iSupIndep R).disjoint_biSup
      (show (0 : Q I) ∉ {q | PositiveDegree q} from fun h ↦ h.1 rfl)
  change Function.Injective ((negative R).toSubmodule.subtype.coprod
    ((cartan R).coprod (positive R).toSubmodule.subtype))
  have hOut : Disjoint (negative R).toSubmodule.subtype.range
      ((cartan R).coprod (positive R).toSubmodule.subtype).range := by
    simpa only [Submodule.range_subtype, LinearMap.range_coprod] using
      negative_disjoint_cartan_sup_positive R
  have hIn : Disjoint (cartan R).range (positive R).toSubmodule.subtype.range := by
    simpa only [Submodule.range_subtype] using hHP
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hOut,
    LinearMap.ker_coprod_of_disjoint_range _ _ hIn, Submodule.ker_subtype,
    Submodule.ker_subtype, LinearMap.ker_eq_bot.mpr (cartan_injective R), Submodule.prod_bot,
    Submodule.prod_bot]

/-- The canonical triangular decomposition, with its original Cartan space. -/
def triangularAdditionEquiv : (negative R × H × positive R) ≃ₗ[ℂ] Algebra R :=
  LinearEquiv.ofBijective (triangularAdd R) (triangularAdd_bijective R)

/-- The root-lattice grading on the canonical quotient. -/
@[instance_reducible]
def gradedLieAlgebra [DecidableEq (Q I)] : GradedLieAlgebra (grade R) where
  toDecomposition := (grade_isInternal R).chooseDecomposition
  bracket_mem := by
    intro q p x y hx hy
    exact lie_mem_grade R hx hy

theorem eq_bot_of_disjoint_cartan (J : LieIdeal ℂ (Algebra R))
    (hJ : Disjoint J.toSubmodule (cartan R).range) : J = ⊥ := by
  have hpre : Disjoint (J.comap (quotientMap R)).toSubmodule (Presentation.cartan R).range := by
    rw [Submodule.disjoint_def]
    rintro _ hx ⟨h, rfl⟩
    have hz := Submodule.disjoint_def.mp hJ (cartan R h) hx ⟨h, rfl⟩
    have hh : h = 0 := cartan_injective R (hz.trans (map_zero _).symm)
    rw [hh, map_zero]
  have hle : J.comap (quotientMap R) ≤ cartanDisjointIdeal R :=
    (cartanDisjointIdeal_isGreatest R).2 hpre
  apply le_antisymm ?_ bot_le
  intro y hy
  obtain ⟨x, rfl⟩ := quotientMap_surjective R y
  have hx : x ∈ cartanDisjointIdeal R := hle hy
  rw [← quotientMap_ker R] at hx
  exact LieHom.mem_ker.mp hx

theorem interchange_descends
    (σ : Presentation.Algebra R ≃ₗ⁅ℂ⁆ Presentation.Algebra R)
    (hσ : Specs.LieNotes.Contragredient.Presentation.IsInterchange R σ) :
    ∃ τ : Algebra R ≃ₗ⁅ℂ⁆ Algebra R,
      Function.Involutive τ ∧ ∀ x, τ (quotientMap R x) = quotientMap R (σ x) := by
  let J := cartanDisjointIdeal R
  have hpre : Disjoint (J.comap σ.toLieHom).toSubmodule (Presentation.cartan R).range := by
    rw [Submodule.disjoint_def]
    rintro _ hx ⟨h, rfl⟩
    change σ (Presentation.cartan R h) ∈ J at hx
    rw [hσ.2.1 h] at hx
    have hm : -Presentation.cartan R h ∈ (Presentation.cartan R).range :=
      Submodule.neg_mem _ ⟨h, rfl⟩
    have hz := Submodule.disjoint_def.mp (cartanDisjointIdeal_isGreatest R).1 _ hx hm
    exact neg_eq_zero.mp hz
  have hle : J.comap σ.toLieHom ≤ J := (cartanDisjointIdeal_isGreatest R).2 hpre
  have hstable : J ≤ J.comap σ.toLieHom := by
    intro x hx
    change σ x ∈ J
    apply hle
    change σ (σ x) ∈ J
    simpa only [hσ.1 x] using hx
  let τ : Algebra R →ₗ⁅ℂ⁆ Algebra R :=
    { J.toSubmodule.mapQ J.toSubmodule σ.toLinearEquiv.toLinearMap hstable with
      map_lie' := by
        intro x y
        obtain ⟨x, rfl⟩ := quotientMap_surjective R x
        obtain ⟨y, rfl⟩ := quotientMap_surjective R y
        change quotientMap R (σ ⁅x, y⁆) = ⁅quotientMap R (σ x), quotientMap R (σ y)⁆
        rw [LieEquiv.map_lie, LieHom.map_lie] }
  have happly (x : Presentation.Algebra R) : τ (quotientMap R x) = quotientMap R (σ x) := rfl
  have hinv : Function.Involutive τ := by
    intro x
    obtain ⟨x, rfl⟩ := quotientMap_surjective R x
    rw [happly, happly, hσ.1 x]
  exact ⟨LieEquiv.ofBijective τ ⟨hinv.injective, hinv.surjective⟩, hinv, happly⟩

theorem hasInterchange :
    ∃ τ : Algebra R ≃ₗ⁅ℂ⁆ Algebra R,
      Function.Involutive τ ∧
      (∀ h, τ (cartan R h) = -cartan R h) ∧
      (∀ i, τ (e R i) = f R i) ∧
      (∀ i, τ (f R i) = e R i) := by
  obtain ⟨σ, hσ⟩ := Presentation.hasInterchange R
  obtain ⟨τ, hinv, hτ⟩ := interchange_descends R σ hσ
  refine ⟨τ, hinv, ?_, ?_, ?_⟩
  · intro h
    change τ (quotientMap R (Presentation.cartan R h)) = -quotientMap R (Presentation.cartan R h)
    rw [hτ, hσ.2.1, map_neg]
  · intro i
    change τ (quotientMap R (Presentation.e R i)) = quotientMap R (Presentation.f R i)
    rw [hτ, hσ.2.2.1]
  · intro i
    change τ (quotientMap R (Presentation.f R i)) = quotientMap R (Presentation.e R i)
    rw [hτ, hσ.2.2.2]

end

end LieNotes.Contragredient.CartanQuotient
