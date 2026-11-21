import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Engel

/-! Engel's theorem over arbitrary fields (LA-B01). -/

universe u v w
namespace LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

theorem common_kernel {k : Type u} [Field k] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (A : LieSubalgebra k (Module.End k V))
    (hA : ∀ x : A, IsNilpotent (x : Module.End k V)) :
    ∃ v : V, v ≠ 0 ∧ ∀ x : A, (x : Module.End k V) v = 0 := by
  have hn : LieModule.IsNilpotent A V :=
    (LieModule.isNilpotent_iff_forall' (R := k)).mpr hA
  have := LieModule.nontrivial_max_triv_of_isNilpotent k A V
  obtain ⟨v, hv⟩ := exists_ne (0 : LieModule.maxTrivSubmodule k A V)
  refine ⟨v, ?_, ?_⟩
  · exact fun h => hv (Subtype.ext h)
  · exact (LieModule.mem_maxTrivSubmodule k A V v).mp v.property

theorem engel_criterion (k : Type u) [Field k] (G : Type v)
    [LieRing G] [LieAlgebra k G] [FiniteDimensional k G] :
    LieRing.IsNilpotent G ↔ ∀ x : G, IsNilpotent (LieAlgebra.ad k G x) :=
  LieAlgebra.isNilpotent_iff_forall

/-- A nilpotent action admits a basis that it strictly lowers. We induct on
dimension, choosing a hyperplane containing the span of all action values. -/
private theorem exists_lowering_basis {k : Type u} [Field k]
    {L : Type v} [LieRing L] [LieAlgebra k L]
    (V : Type w) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule L V] [LieModule k L V] [LieModule.IsNilpotent L V] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V),
      ∀ (x : L) (j : Fin n),
        ⁅x, b j⁆ ∈ Submodule.span k (b '' {i | i < j}) := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, Module.Basis.empty V, fun _ j => Fin.elim0 j⟩
  have hproper : (LieModule.lowerCentralSeries k L V 1).toSubmodule ≠ ⊤ := by
    intro h
    have h1 : LieModule.lowerCentralSeries k L V 1 = ⊤ :=
      (LieSubmodule.toSubmodule_inj _ _).mp h
    have hall (m : ℕ) : LieModule.lowerCentralSeries k L V m = ⊤ := by
      induction m with
      | zero => rfl
      | succ m hm =>
        simpa only [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero, hm]
          using h1
    obtain ⟨m, hm⟩ := LieModule.IsNilpotent.nilpotent k L V
    have hh : (⊤ : LieSubmodule k L V) = ⊥ := (hall m).symm.trans hm
    have hv (v : V) : v = 0 := by
      exact (LieSubmodule.mem_bot v).mp (hh ▸ LieSubmodule.mem_top v)
    exact (exists_ne (0 : V)).elim (fun v hv' => hv' (hv v))
  obtain ⟨W, hW, hCW⟩ :=
    (eq_top_or_exists_le_coatom (LieModule.lowerCentralSeries k L V 1).toSubmodule).resolve_left
      hproper
  have haction (x : L) (v : V) : ⁅x, v⁆ ∈ W := by
    apply hCW
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top v)
  let N : LieSubmodule k L V :=
    { toSubmodule := W
      lie_mem := fun {x v} _ => haction x v }
  have : LieModule.IsNilpotent L N :=
    (show Function.Injective N.toSubmodule.subtype from Subtype.val_injective).lieModuleIsNilpotent
      (f := LieHom.id) (fun _ _ => rfl)
  obtain ⟨n, b, hb⟩ := exists_lowering_basis (k := k) (L := L) N
  obtain ⟨y, _, hy⟩ := IsConcreteLE.exists_of_lt hW.lt_top
  have hcompl := Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hW hy
  have hli (c : k) (z : V) (hz : z ∈ W) (heq : c • y + z = 0) : c = 0 := by
    by_contra hc
    apply hy
    apply (W.smul_mem_iff hc).mp
    rw [eq_neg_of_add_eq_zero_left heq]
    exact W.neg_mem hz
  have hsp (z : V) : ∃ c : k, z + c • y ∈ W := by
    have hz : z ∈ W ⊔ k ∙ y := hcompl.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    exact ⟨-c, by simpa using hw⟩
  let b' := Module.Basis.mkFinSnoc b y hli hsp
  have hb' (j : Fin n) : b' j.castSucc = (b j : V) := by
    simp [b', Module.Basis.coe_mkFinSnoc]
  refine ⟨n + 1, b', fun x j => ?_⟩
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hw : ⁅x, b' (Fin.last n)⁆ ∈ W := haction _ _
    have hspan : W = Submodule.span k (Set.range fun i => (b i : V)) := by
      rw [← Submodule.map_subtype_top W, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hspan] at hw
    apply Submodule.span_mono (s := Set.range fun i => (b i : V)) ?_ hw
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, by simp, hb' i⟩
  · have hh := Submodule.mem_map_of_mem (f := W.subtype) (hb x j)
    rw [Submodule.map_span] at hh
    rw [hb']
    apply Submodule.span_mono (s := W.subtype '' (b '' {i | i < j})) ?_ hh
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i.castSucc, hi, hb' i⟩
termination_by Module.finrank k V
decreasing_by
  exact Submodule.finrank_lt hW.ne_top

theorem strict_upper_triangular_basis {k : Type u} [Field k] {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (A : LieSubalgebra k (Module.End k V))
    (hA : ∀ x : A, IsNilpotent (x : Module.End k V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V),
      ∀ (x : A) (i j : Fin n), j ≤ i → b.repr ((x : Module.End k V) (b j)) i = 0 := by
  have hn : LieModule.IsNilpotent A V :=
    (LieModule.isNilpotent_iff_forall' (R := k)).mpr hA
  obtain ⟨n, b, hb⟩ := exists_lowering_basis (k := k) (L := A) V
  refine ⟨n, b, fun x i j hji => ?_⟩
  have hs := b.mem_span_image.mp (hb x j)
  by_contra h
  exact (not_lt_of_ge hji) (hs (Finsupp.mem_support_iff.mpr h))

end LieAlgebrasAndRepresentations
