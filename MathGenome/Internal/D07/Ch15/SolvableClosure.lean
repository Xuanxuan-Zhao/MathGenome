import MathGenome.Internal.Specs.D07.Ch15.SolvableClosure

/-!
Subgroups, quotients and extensions of solvable groups.
The imported library uses exactly the source's derived-series definition.
The quantitative extension proof places the `r`th term in the projection
kernel, then takes `s` further commutators. The final induction applies
extension closure inside each member of a subnormal chain.
-/

namespace D07.Ch15.SolvableClosure

universe u v

theorem subgroup_derived_le (G : Type u) [Group G] (H : Subgroup G) (n : ℕ) :
    (derivedSeries H n).map H.subtype ≤ derivedSeries G n :=
  map_derivedSeries_le_derivedSeries H.subtype n

theorem surjective_derived_eq (G : Type u) (Q : Type v) [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (n : ℕ) :
    (derivedSeries G n).map q = derivedSeries Q n :=
  map_derivedSeries_eq hq n

theorem subgroup_solvable (G : Type u) [Group G] (H : Subgroup G)
    (hG : Group.IsSolvable G) : Group.IsSolvable H := by
  have := hG
  exact Group.isSolvable_of_isSolvable_injective H.subtype_injective

theorem quotient_solvable (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (hG : Group.IsSolvable G) : Group.IsSolvable (G ⧸ N) := by
  have := hG
  exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N)

theorem extension_derived_length (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (r s : ℕ) (hr : derivedSeries (G ⧸ N) r = ⊥) (hs : derivedSeries N s = ⊥) :
    derivedSeries G (r + s) = ⊥ := by
  have hbase : derivedSeries G r ≤ N := by
    have hmap : (derivedSeries G r).map (QuotientGroup.mk' N) = ⊥ := by
      rw [surjective_derived_eq G (G ⧸ N) (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N), hr]
    simpa only [QuotientGroup.ker_mk'] using
      ((derivedSeries G r).map_eq_bot_iff.mp hmap)
  have hbound (k : ℕ) :
      derivedSeries G (r + k) ≤ (derivedSeries N k).map N.subtype := by
    induction k with
    | zero =>
      simpa only [Nat.add_zero, derivedSeries_zero, Subgroup.map_top,
        Subgroup.range_subtype] using hbase
    | succ k ih =>
      simpa only [Nat.add_succ, derivedSeries_succ] using
        (Subgroup.commutator_le_map_commutator ih ih)
  apply le_bot_iff.mp
  simpa only [hs, Subgroup.map_bot] using hbound s

theorem extension_solvable (G : Type u) [Group G] (N : Subgroup G) [N.Normal]
    (hN : Group.IsSolvable N) (hQ : Group.IsSolvable (G ⧸ N)) :
    Group.IsSolvable G := by
  have := hN
  have := hQ
  exact Group.isSolvable_of_subgroup_quotient N

theorem subnormal_series_solvable (G : Type u) [Group G] (n : ℕ)
    (H : ℕ → Subgroup G) (h0 : H 0 = ⊥) (hn : H n = ⊤)
    (hinc : ∀ i < n, H i ≤ H (i + 1))
    (hNormal : ∀ i < n, ((H i).subgroupOf (H (i + 1))).Normal)
    (hfactor : ∀ (i : ℕ) (hi : i < n),
      letI := hNormal i hi
      Group.IsSolvable (H (i + 1) ⧸ (H i).subgroupOf (H (i + 1)))) :
    Group.IsSolvable G := by
  have hterms : ∀ k, k ≤ n → Group.IsSolvable (H k) := by
    intro k hk
    induction k with
    | zero =>
      rw [h0]
      infer_instance
    | succ k ih =>
      have hkn : k < n := Nat.lt_of_succ_le hk
      have := ih (Nat.le_of_lt hkn)
      have := hNormal k hkn
      have := hfactor k hkn
      let e := Subgroup.subgroupOfEquivOfLe (hinc k hkn)
      have : Group.IsSolvable ((H k).subgroupOf (H (k + 1))) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact extension_solvable (H (k + 1)) ((H k).subgroupOf (H (k + 1)))
        inferInstance inferInstance
  have htop : Group.IsSolvable (⊤ : Subgroup G) := hn ▸ hterms n le_rfl
  have := htop
  exact Group.isSolvable_of_surjective
    (MonoidHom.range_eq_top.mp (Subgroup.range_subtype ⊤))

end D07.Ch15.SolvableClosure
