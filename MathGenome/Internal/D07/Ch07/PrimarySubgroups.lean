import MathGenome.Internal.Specs.D07.Ch07.PrimarySubgroups

/-!
Torsion and primary subgroups of arbitrary abelian groups
(K07.07.primary_subgroups, paper.tex:3391–3410).

The library subgroups are defined by finite additive order and annihilation
by a power of p, respectively. The torsion membership lemma explicitly
converts the natural annihilator to the source's positive integer one.
Automorphisms preserve annihilators, proving characteristicity. Every
p-subgroup lies in the primary component; its own elements are killed by
p-powers. These two facts give Sylow maximality and uniqueness directly.
-/
namespace D07.Ch07.PrimarySubgroups

universe u

/-- The torsion subgroup, with its inherited additive operations. -/
def torsionSubgroup (A : Type u) [AddCommGroup A] : AddSubgroup A :=
  Specs.D07.Ch07.PrimarySubgroups.torsionSubgroupValue A

/-- The subgroup annihilated elementwise by powers of p. -/
def primarySubgroup (A : Type u) [AddCommGroup A] (p : ℕ) : AddSubgroup A :=
  Specs.D07.Ch07.PrimarySubgroups.primarySubgroupValue A p

theorem mem_torsion (A : Type u) [AddCommGroup A] (a : A) :
    a ∈ torsionSubgroup A ↔ ∃ n : ℤ, 0 < n ∧ n • a = 0 := by
  change IsOfFinAddOrder a ↔ _
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  constructor
  · rintro ⟨n, hn, ha⟩
    exact ⟨(n : ℤ), Int.natCast_pos.mpr hn, by simpa using ha⟩
  · rintro ⟨n, hn, ha⟩
    lift n to ℕ using hn.le
    exact ⟨n, Int.natCast_pos.mp hn, by simpa using ha⟩

theorem torsion_characteristic (A : Type u) [AddCommGroup A] :
    (torsionSubgroup A).Characteristic := by
  apply AddSubgroup.characteristic_iff_le_comap.mpr
  intro f a ha
  obtain ⟨n, hn, hna⟩ := (mem_torsion A a).mp ha
  exact (mem_torsion A (f a)).mpr
    ⟨n, hn, by rw [← map_zsmul, hna, map_zero]⟩

theorem mem_primary (A : Type u) [AddCommGroup A] (p : ℕ) (_hp : p.Prime) (a : A) :
    a ∈ primarySubgroup A p ↔ ∃ k : ℕ, (p ^ k) • a = 0 := Iff.rfl

theorem primary_characteristic (A : Type u) [AddCommGroup A] (p : ℕ)
    (_hp : p.Prime) : (primarySubgroup A p).Characteristic := by
  apply AddSubgroup.characteristic_iff_le_comap.mpr
  intro f a ha
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

/-- Any p-subgroup is contained in the intrinsic primary component. -/
theorem p_subgroup_le_primary (A : Type u) [AddCommGroup A] (p : ℕ)
    (Q : Subgroup (Multiplicative A)) (hQ : IsPGroup p Q) :
    Q ≤ (primarySubgroup A p).toSubgroup := by
  intro x hx
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  refine ⟨k, ?_⟩
  exact congrArg (fun y : Q => Multiplicative.toAdd (y : Multiplicative A)) hk

/-- The primary component itself satisfies the elementwise p-group condition. -/
theorem primary_isPGroup (A : Type u) [AddCommGroup A] (p : ℕ) :
    IsPGroup p (primarySubgroup A p).toSubgroup := by
  intro x
  obtain ⟨k, hk⟩ := x.property
  exact ⟨k, Subtype.ext hk⟩

theorem primary_unique_sylow (A : Type u) [AddCommGroup A] [Finite A]
    (p : ℕ) (_hp : p.Prime) :
    ∃ S : Sylow p (Multiplicative A),
      S.toSubgroup = (primarySubgroup A p).toSubgroup ∧
      ∀ Q : Sylow p (Multiplicative A), Q = S := by
  let S : Sylow p (Multiplicative A) :=
    { toSubgroup := (primarySubgroup A p).toSubgroup
      isPGroup' := primary_isPGroup A p
      is_maximal' := fun {Q} hQ hPQ =>
        le_antisymm (p_subgroup_le_primary A p Q hQ) hPQ }
  refine ⟨S, rfl, ?_⟩
  intro Q
  apply Sylow.ext
  exact (Q.is_maximal' (primary_isPGroup A p)
    (p_subgroup_le_primary A p Q.toSubgroup Q.isPGroup')).symm

end D07.Ch07.PrimarySubgroups
