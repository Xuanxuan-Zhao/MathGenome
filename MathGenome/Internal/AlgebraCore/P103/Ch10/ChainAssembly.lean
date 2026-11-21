import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexConstruction
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.ChainAssembly

namespace P103.Ch10.TotalComplexAssembly
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
variable {R : Type u} [Ring R]

/-- Element form of the two-input coordinate formula. -/
private theorem chain_coordinate_d (K : ChainBicomplex.{u,v} R) (p q n : ℤ)
    (h : p + q = n - 1) (x : (total K).X n) :
    (totalProjection K p q (n - 1) h).hom ((total K).d n (n - 1) x) =
      (K.d (p + 1) p).f q ((totalProjection K (p + 1) q n (by omega)).hom x) +
      p.negOnePow • ((K.X p).d (q + 1) q
        ((totalProjection K p (q + 1) n (by omega)).hom x)) := by
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (chain_totalProjection_d K p q n h)) x

/-- The same formula with explicit adjacent indices avoids transports of
coordinate types during the element chase. -/
private theorem chain_coordinate_d_at (K : ChainBicomplex.{u,v} R)
    (p p' q q' n m : ℤ) (hp : p' = p + 1) (hq : q' = q + 1)
    (hm : m = n - 1) (h : p + q = m) (x : (total K).X n) :
    (totalProjection K p q m h).hom ((total K).d n m x) =
      (K.d p' p).f q ((totalProjection K p' q n (by omega)).hom x) +
      p.negOnePow • ((K.X p).d q' q
        ((totalProjection K p q' n (by omega)).hom x)) := by
  subst p' q' m
  exact chain_coordinate_d K p q n h x

/-- A single included element has no coordinate at a distinct horizontal index. -/
private theorem projection_inclusion_ne (K : ChainBicomplex.{u,v} R)
    (p q i j n : ℤ) (h : p + q = n) (h' : i + j = n) (hne : p ≠ i)
    (w : (K.X p).X q) :
    (totalProjection K i j n h').hom ((totalInclusion K p q n h).hom w) = 0 := by
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (totalInclusion_projection_ne K p q i j n h h' (Or.inl hne))) w

private theorem projection_inclusion_self (K : ChainBicomplex.{u,v} R)
    (p q n : ℤ) (h : p + q = n) (w : (K.X p).X q) :
    (totalProjection K p q n h).hom ((totalInclusion K p q n h).hom w) = w := by
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (totalInclusion_projection_self K p q n h)) w

/-- Remove the highest possible horizontal component of a total cycle.
Only the component immediately to its left can be introduced. -/
private theorem chain_peel (K : ChainBicomplex.{u,v} R)
    (hcol : ColumnsAcyclic K) (p q n : ℤ) (hpq : p + q = n)
    (z : (total K).X n) (hz : (total K).d n (n - 1) z = 0)
    (hmax : ∀ i j (hij : i + j = n), p < i →
      (totalProjection K i j n hij).hom z = 0) :
    ∃ y : (total K).X (n + 1),
      ∀ i j (hij : i + j = n), p ≤ i →
        (totalProjection K i j n hij).hom (z - (total K).d (n + 1) n y) = 0 := by
  let t := (totalProjection K p q n hpq).hom z
  have htop : p.negOnePow • ((K.X p).d q (q - 1) t) = 0 := by
    have hd := chain_coordinate_d_at K p (p + 1) (q - 1) q n (n - 1)
      rfl (by omega) rfl (by omega) z
    rw [hz, map_zero, hmax (p + 1) (q - 1) (by omega) (by omega), map_zero,
      zero_add] at hd
    exact hd.symm
  have hc : t ∈ Complexes.cycles (signedColumn (K.X p) p.negOnePow) q := by
    rw [signedColumn_cycles, Complexes.cycles_chain]
    exact (smul_eq_zero_iff_eq p.negOnePow).mp htop
  have ha := (signedColumn_acyclic_iff (K.X p) p.negOnePow).mpr (hcol p)
  rw [← (Complexes.acyclic_iff _).mp ha q, Complexes.boundaries_chain] at hc
  obtain ⟨w, hw⟩ := hc
  change p.negOnePow • ((K.X p).d (q + 1) q w) = t at hw
  let y := (totalInclusion K p (q + 1) (n + 1) (by omega)).hom w
  refine ⟨y, ?_⟩
  intro i j hij hi
  have hd : (totalProjection K i j n hij).hom ((total K).d (n + 1) n y) =
      (K.d (i + 1) i).f j ((totalProjection K (i + 1) j (n + 1) (by omega)).hom y) +
      i.negOnePow • ((K.X i).d (j + 1) j
        ((totalProjection K i (j + 1) (n + 1) (by omega)).hom y)) := by
    exact chain_coordinate_d_at K i (i + 1) j (j + 1) (n + 1) n
      rfl rfl (by omega) hij y
  have hy₁ : (totalProjection K (i + 1) j (n + 1) (by omega)).hom y = 0 :=
    projection_inclusion_ne K p (q + 1) (i + 1) j (n + 1) _ _ (by omega) w
  rw [hy₁, map_zero, zero_add] at hd
  rw [map_sub, hd]
  by_cases hip : i = p
  · subst i
    have hjq : j = q := by omega
    subst j
    rw [show (totalProjection K p (q + 1) (n + 1) (by omega)).hom y = w from
      projection_inclusion_self K p (q + 1) (n + 1) _ w, hw]
    exact sub_self t
  · rw [show (totalProjection K i (j + 1) (n + 1) (by omega)).hom y = 0 from
      projection_inclusion_ne K p (q + 1) i (j + 1) (n + 1) _ _ (Ne.symm hip) w]
    rw [map_zero, smul_zero, sub_zero, hmax i j hij (by omega)]

/-- Finite descent of the horizontal support of a cycle. The integer lower
bound is fixed, and no choice of a linear contracting homotopy is used. -/
private theorem chain_cycle_boundary_bounded (K : ChainBicomplex.{u,v} R) (a : ℤ)
    (hs : ∀ p q, p < a → Subsingleton ((K.X p).X q))
    (hcol : ColumnsAcyclic K) (n : ℤ) (k : ℕ)
    (z : (total K).X n) (hz : (total K).d n (n - 1) z = 0)
    (hb : ∀ p q (hpq : p + q = n), a + (k : ℤ) ≤ p →
      (totalProjection K p q n hpq).hom z = 0) :
    ∃ y : (total K).X (n + 1), (total K).d (n + 1) n y = z := by
  induction k generalizing z with
  | zero =>
    have hz0 : z = 0 := by
      apply total_ext K n
      intro p q hpq
      rw [map_zero]
      by_cases hp : p < a
      · have := hs p q hp
        exact Subsingleton.elim _ _
      · exact hb p q hpq (by simpa using (le_of_not_gt hp))
    exact ⟨0, by rw [map_zero, hz0]⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := chain_peel K hcol (a + (k : ℤ)) (n - (a + (k : ℤ))) n
      (by omega) z hz (by
        intro i j hij hi
        exact hb i j hij (by omega))
    have hsq : (total K).d n (n - 1) ((total K).d (n + 1) n w) = 0 :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        ((total K).d_comp_d (n + 1) n (n - 1))) w
    have hr : (total K).d n (n - 1) (z - (total K).d (n + 1) n w) = 0 := by
      rw [map_sub, hz, hsq, sub_self]
    obtain ⟨y, hy⟩ := ih (z - (total K).d (n + 1) n w) hr hw
    refine ⟨y + w, ?_⟩
    rw [map_add, hy, sub_add_cancel]

/-- Chain first-quadrant assembly from acyclic original vertical columns. -/
theorem chain_columns_acyclic (K : ChainBicomplex.{u,v} R) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (hc : ColumnsAcyclic K) :
    Complexes.Acyclic (total K) := by
  apply (Complexes.acyclic_iff _).mpr
  intro n
  apply le_antisymm (Complexes.boundaries_le_cycles (total K) n)
  intro z hz
  rw [Complexes.cycles_chain] at hz
  rw [Complexes.boundaries_chain]
  apply chain_cycle_boundary_bounded K a (fun p q hp => hs p q (Or.inl hp)) hc n
    (n - b - a + 1).toNat z hz
  intro p q hpq hp
  have hk := Int.self_le_toNat (n - b - a + 1)
  have := hs p q (Or.inr (by omega))
  exact Subsingleton.elim _ _

/-- Signed interchange gives chain assembly from acyclic original rows. -/
theorem chain_rows_acyclic (K : ChainBicomplex.{u,v} R) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (hr : RowsAcyclic K) :
    Complexes.Acyclic (total K) := by
  apply acyclic_of_iso (signedInterchange K)
  apply chain_columns_acyclic K.flip b a
  · intro p q hpq
    exact hs q p hpq.symm
  · exact hr

/-- For anticommuting columns the canonical total differential is dh+dv. -/
theorem anticommuting_chain_columns_acyclic
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.down ℤ)) (a b : ℤ)
    (hs : ∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q))
    (hc : ∀ p, Complexes.Acyclic (A.column p)) :
    Complexes.Acyclic (anticommutingTotal A) := by
  exact chain_columns_acyclic (anticommutingToCommuting A) a b hs
    ((anticommuting_columns_acyclic_iff A).mpr hc)

/-- For anticommuting rows the same ordinary-sum total is acyclic. -/
theorem anticommuting_chain_rows_acyclic
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.down ℤ)) (a b : ℤ)
    (hs : ∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q))
    (hr : ∀ q, Complexes.Acyclic (A.row q)) :
    Complexes.Acyclic (anticommutingTotal A) := by
  exact chain_rows_acyclic (anticommutingToCommuting A) a b hs
    ((anticommuting_rows_acyclic_iff A).mpr hr)

end
end P103.Ch10.TotalComplexAssembly
