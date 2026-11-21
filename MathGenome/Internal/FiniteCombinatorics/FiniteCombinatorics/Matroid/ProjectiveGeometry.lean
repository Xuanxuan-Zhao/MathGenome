import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ParallelClasses
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ProjectiveGeometry

namespace FiniteCombinatorics.Matroid
open Set Submodule
universe u v

def ProjectiveRepresentative (K : Type u) [Field K] (V : Type v)
    [AddCommGroup V] [Module K V] (v : Projectivization K V → V) : Prop :=
  ∀ p, ∃ h : v p ≠ 0, Projectivization.mk K (v p) h = p

def projectiveMatroid (K : Type u) [Field K] (V : Type v)
    [AddCommGroup V] [Module K V] [Finite V]
    (v : Projectivization K V → V) : _root_.Matroid (Projectivization K V) :=
  vectorMatroid K univ (Set.toFinite _) v

instance (K : Type u) [Field K] (V : Type v)
    [AddCommGroup V] [Module K V] [Finite V] (v : Projectivization K V → V) :
    (projectiveMatroid K V v).Finite := inferInstanceAs (vectorMatroid K _ _ _).Finite

def projectivePointsIn {K : Type u} [Field K] {V : Type v}
    [AddCommGroup V] [Module K V] (U : Submodule K V) : Set (Projectivization K V) :=
  {p | p.submodule ≤ U}

section General
variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- Nonzero membership in a point's subspace is exactly being a representative. -/
lemma projective_mk_eq_iff (p : Projectivization K V) (x : V) :
    (x ≠ 0 ∧ x ∈ p.submodule) ↔ ∃ h : x ≠ 0, Projectivization.mk K x h = p := by
  constructor
  · rintro ⟨hx, hmem⟩
    rw [p.submodule_eq, mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨hx, ?_⟩
    rw [← p.mk_rep, Projectivization.mk_eq_mk_iff']
    exact ⟨c, hc⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, mem_span_singleton_self x⟩

lemma ProjectiveRepresentative.nonzero {v : Projectivization K V → V}
    (hv : ProjectiveRepresentative K V v) (p : Projectivization K V) : v p ≠ 0 :=
  (hv p).choose

lemma ProjectiveRepresentative.span_singleton {v : Projectivization K V → V}
    (hv : ProjectiveRepresentative K V v) (p : Projectivization K V) :
    span K {v p} = p.submodule := by
  obtain ⟨h, hp⟩ := hv p
  exact (Projectivization.submodule_mk (v p) h).symm.trans (congrArg Projectivization.submodule hp)

lemma ProjectiveRepresentative.mem_submodule {v : Projectivization K V → V}
    (hv : ProjectiveRepresentative K V v) (p : Projectivization K V) : v p ∈ p.submodule := by
  rw [← hv.span_singleton p]
  exact mem_span_singleton_self _

lemma ProjectiveRepresentative.indep_iff {v : Projectivization K V → V}
    (hv : ProjectiveRepresentative K V v) (I : Set (Projectivization K V)) :
    LinearIndepOn K v I ↔ LinearIndepOn K Projectivization.rep I := by
  have hm (p : Projectivization K V) :
      ∃ a : Kˣ, a • p.rep = v p := by
    apply (Projectivization.mk_eq_mk_iff K _ _ (hv.nonzero p) p.rep_nonzero).mp
    rw [Projectivization.mk_rep]
    exact (hv p).choose_spec
  choose a ha using hm
  change LinearIndependent K (fun p : I => v p.val) ↔ _
  simp_rw [← ha]
  exact LinearIndependent.units_smul_iff _ _

/-- The chosen columns in each subspace span that entire subspace. -/
lemma projective_span {v : Projectivization K V → V}
    (hv : ProjectiveRepresentative K V v) (U : Submodule K V) :
    span K (v '' projectivePointsIn U) = U := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact hp (hv.mem_submodule p)
  · intro x hx
    by_cases hzero : x = 0
    · simp [hzero]
    let p := Projectivization.mk K x hzero
    have hp : p ∈ projectivePointsIn U := (span_singleton_le_iff_mem _ _).mpr hx
    have hle : p.submodule ≤ span K (v '' projectivePointsIn U) := by
      rw [← hv.span_singleton p]
      exact (span_singleton_le_iff_mem _ _).mpr (subset_span ⟨p, hp, rfl⟩)
    exact hle (mem_span_singleton_self x)

/-- Points of U are exactly its intrinsic projective points, via inclusion. -/
noncomputable def projectivePointsInEquiv (U : Submodule K V) :
    Projectivization K U ≃ projectivePointsIn U := by
  let f := Projectivization.map U.subtype U.subtype_injective
  have hf : ∀ p, f p ∈ projectivePointsIn U := by
    intro p
    induction p using Projectivization.ind with
    | h x hx =>
      change span K {(x : V)} ≤ U
      exact (span_singleton_le_iff_mem _ _).mpr x.property
  apply Equiv.ofBijective (fun p => (⟨f p, hf p⟩ : projectivePointsIn U))
  constructor
  · intro p q hpq
    exact Projectivization.map_injective U.subtype U.subtype_injective (congrArg Subtype.val hpq)
  · rintro ⟨p, hp⟩
    have hrep : p.rep ∈ U := hp (by rw [p.submodule_eq]; exact mem_span_singleton_self _)
    let x : U := ⟨p.rep, hrep⟩
    have hx : x ≠ 0 := fun h => p.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K x hx, Subtype.ext ?_⟩
    exact p.mk_rep

end General

theorem projectiveSubspaceBridge : Expected.projectiveSubspaceBridge := by
  intro K _ V _ _
  refine ⟨⟨Projectivization.equivSubmodule K V, fun _ => rfl⟩, ?_⟩
  exact projective_mk_eq_iff

theorem projectiveReindexBridge : Expected.projectiveReindexBridge := by
  intro K _ V _ _ _ v hv
  let e := Projectivization.equivSubmodule K V
  constructor
  · intro p
    apply (projective_mk_eq_iff p (v (e p))).mp
    exact hv (e p)
  · intro I
    change (I ⊆ univ ∧ LinearIndepOn K (v ∘ e) I) ↔
      (e '' I ⊆ e '' univ ∧ LinearIndepOn K v (e '' I))
    simp only [subset_univ, true_and]
    exact ⟨fun hi => ⟨image_mono (subset_univ _), (linearIndepOn_equiv e).mp hi⟩,
      fun hi => (linearIndepOn_equiv e).mpr hi.2⟩

theorem projectiveRepValid : Expected.projectiveRepValid := by
  intro K _ V _ _ p
  exact ⟨p.rep_nonzero, p.mk_rep⟩

theorem projectiveChoiceIndependent : Expected.projectiveChoiceIndependent := by
  intro K _ V _ _ _ v w hv hw
  refine _root_.Matroid.ext_indep (M₁ := Expected.projectiveMatroid K V v)
    (M₂ := Expected.projectiveMatroid K V w) rfl ?_
  intro I _
  change (I ⊆ univ ∧ LinearIndepOn K v I) ↔ (I ⊆ univ ∧ LinearIndepOn K w I)
  exact and_congr_right (fun _ => (ProjectiveRepresentative.indep_iff hv I).trans
    (ProjectiveRepresentative.indep_iff hw I).symm)

theorem projectiveSimple : Expected.projectiveSimple := by
  intro K _ V _ _ _ v hv
  constructor
  · intro p
    exact ⟨subset_univ _, (linearIndepOn_singleton_iff K).mpr (ProjectiveRepresentative.nonzero hv p)⟩
  · intro p q hpq
    refine ⟨subset_univ _, ?_⟩
    rw [ProjectiveRepresentative.indep_iff hv]
    rw [linearIndepOn_pair_iff _ hpq p.rep_nonzero]
    intro c hc
    apply hpq.symm
    rw [← p.mk_rep, ← q.mk_rep, Projectivization.mk_eq_mk_iff']
    exact ⟨c, hc⟩

theorem projectiveGround : Expected.projectiveGround := by
  intro K _ V _ _ _ v
  rfl

theorem projectiveRank : Expected.projectiveRank := by
  intro K _ _ r _ v hv
  change rank (vectorMatroid K univ (Set.toFinite _) v) univ = (r : ℤ)
  have hr := vectorRank K univ (Set.toFinite _) v univ (subset_univ _)
  change rank (vectorMatroid K univ (Set.toFinite _) v) univ = _ at hr
  rw [hr]
  have hs := projective_span hv (⊤ : Submodule K (Fin r → K))
  simp only [projectivePointsIn, le_top, ofPred_true] at hs
  rw [hs]
  simp

theorem projectiveCardinality : Expected.projectiveCardinality := by
  intro K _ _ r _ v
  change univ.ncard = _
  rw [Set.ncard_univ, Projectivization.card'']
  simp [Nat.card_fun]

theorem projectiveDimensionOne : Expected.projectiveDimensionOne := by
  intro K _ _
  simpa using Projectivization.card_of_finrank K (Fin 1 → K) (by simp : Module.finrank K (Fin 1 → K) = 1)

theorem projectiveFieldSize : Expected.projectiveFieldSize := by
  intro K _ _
  exact Finite.one_lt_card

section Finite
variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] [Finite V]

lemma projective_rank_subspace {v : Projectivization K V → V}
    (hv : ProjectiveRepresentative K V v) (U : Submodule K V) :
    rank (projectiveMatroid K V v) (projectivePointsIn U) = (Module.finrank K U : ℤ) := by
  change rank (vectorMatroid K univ (Set.toFinite _) v) _ = _
  have hr := vectorRank K univ (Set.toFinite _) v (projectivePointsIn U) (subset_univ _)
  change rank (vectorMatroid K univ (Set.toFinite _) v) (projectivePointsIn U) = _ at hr
  rw [hr, projective_span hv U]

lemma projective_flat_subspace {v : Projectivization K V → V}
    (hv : ProjectiveRepresentative K V v) (U : Submodule K V) :
    (projectiveMatroid K V v).IsFlat (projectivePointsIn U) := by
  let M := projectiveMatroid K V v
  let L := projectivePointsIn U
  apply _root_.Matroid.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm ?_ (M.subset_closure _ (subset_univ _))
  intro p hp
  have hr := (closureRank M L (subset_univ _) p (mem_univ _)).mp hp
  have hi := vectorRank K univ (Set.toFinite _) v (insert p L) (subset_univ _)
  have hL := projective_rank_subspace hv U
  change rank M (insert p L) = _ at hi
  change rank M L = _ at hL
  rw [hi, hL] at hr
  have hd : Module.finrank K (span K (v '' insert p L)) = Module.finrank K U := by
    exact_mod_cast hr
  have hle : U ≤ span K (v '' insert p L) := by
    rw [← projective_span hv U]
    exact span_mono (image_mono (subset_insert p L))
  have heq := Submodule.eq_of_le_of_finrank_eq hle hd.symm
  change p.submodule ≤ U
  rw [← hv.span_singleton p]
  apply (span_singleton_le_iff_mem _ _).mpr
  rw [heq]
  exact subset_span ⟨p, mem_insert p L, rfl⟩

end Finite

theorem projectiveLine : Expected.projectiveLine := by
  intro K _ _ r _ v hv U hU
  refine ⟨projective_flat_subspace hv U, ?_, ?_⟩
  · change rank (projectiveMatroid K (Fin r → K) v) (projectivePointsIn U) = 2
    rw [projective_rank_subspace hv U, hU]
    rfl
  · change (projectivePointsIn U).ncard = _
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr (projectivePointsInEquiv U)]
    exact Projectivization.card_of_finrank_two K U hU

end FiniteCombinatorics.Matroid
