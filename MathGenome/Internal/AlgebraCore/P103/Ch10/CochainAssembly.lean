import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexConstruction
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.CochainAssembly

/-!
Cochain first-quadrant assembly, paper.tex 2377–2414. Rings are arbitrary
unital rings, including the zero ring; right modules are represented over the
opposite ring. The canonical direct-sum total and all sign bridges are shared
with the construction module.
-/
namespace P103.Ch10.TotalComplexAssembly
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
variable {R : Type u} [Ring R]

/-- Coordinates of a total coboundary, in element form. -/
lemma cochain_coordinate_d (K : CochainBicomplex.{u,v} R) (n p q : ℤ)
    (h : p + q = n + 1) (x : (total K).X n) :
    (totalProjection K p q (n + 1) h).hom (((total K).d n (n + 1)).hom x) =
      ((K.d (p - 1) p).f q).hom
        ((totalProjection K (p - 1) q n (by omega)).hom x) +
      p.negOnePow • ((K.X p).d (q - 1) q).hom
        ((totalProjection K p (q - 1) n (by omega)).hom x) := by
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (cochain_totalProjection_d K p q n h)) x

/-- A version with explicit equal degree indices avoids dependent transports. -/
lemma cochain_coordinate_d' (K : CochainBicomplex.{u,v} R) (n m p q i j : ℤ)
    (hn : n + 1 = m) (hi : p - 1 = i) (hj : q - 1 = j)
    (h : p + q = m) (x : (total K).X n) :
    (totalProjection K p q m h).hom (((total K).d n m).hom x) =
      ((K.d i p).f q).hom ((totalProjection K i q n (by omega)).hom x) +
      p.negOnePow • ((K.X p).d j q).hom
        ((totalProjection K p j n (by omega)).hom x) := by
  subst m i j
  exact cochain_coordinate_d K n p q h x

lemma inclusion_coordinate_self (K : CochainBicomplex.{u,v} R) (p q n : ℤ)
    (h : p + q = n) (w : (K.X p).X q) :
    (totalProjection K p q n h).hom ((totalInclusion K p q n h).hom w) = w :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (totalInclusion_projection_self K p q n h)) w

lemma inclusion_coordinate_ne (K : CochainBicomplex.{u,v} R) (p q i j n : ℤ)
    (h : p + q = n) (h' : i + j = n) (hne : p ≠ i ∨ q ≠ j) (w : (K.X p).X q) :
    (totalProjection K i j n h').hom ((totalInclusion K p q n h).hom w) = 0 :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (totalInclusion_projection_ne K p q i j n h h' hne)) w

/-- Lifting the first nonzero coordinate requires only column exactness. -/
lemma cochain_lift_first (K : CochainBicomplex.{u,v} R) (hc : ColumnsAcyclic K)
    (n P : ℤ) (z : (total K).X n)
    (hz : ((total K).d n (n + 1)).hom z = 0)
    (hbelow : ∀ p q (h : p + q = n), p < P → (totalProjection K p q n h).hom z = 0) :
    ∃ w : (K.X P).X (n - P - 1),
      P.negOnePow • ((K.X P).d (n - P - 1) (n - P)).hom w =
        (totalProjection K P (n - P) n (by omega)).hom z := by
  have he := cochain_coordinate_d' K n (n + 1) P (n - P + 1) (P - 1) (n - P)
    rfl rfl (by omega) (by omega) z
  rw [hz, map_zero, hbelow (P - 1) (n - P + 1) (by omega) (by omega),
    map_zero, zero_add] at he
  have hv : ((K.X P).d (n - P) (n - P + 1)).hom
      ((totalProjection K P (n - P) n (by omega)).hom z) = 0 := by
    have : P.negOnePow • ((K.X P).d (n - P) (n - P + 1)).hom
      ((totalProjection K P (n - P) n (by omega)).hom z) = 0 := by
      exact he.symm
    exact (smul_eq_zero_iff_eq _).mp this
  have hex := (Complexes.acyclic_iff (K.X P)).mp (hc P) (n - P)
  rw [Complexes.boundaries_cochain, Complexes.cycles_cochain] at hex
  have hm : (totalProjection K P (n - P) n (by omega)).hom z ∈
      LinearMap.range ((K.X P).d (n - P - 1) (n - P)).hom := by
    rw [hex]
    exact hv
  obtain ⟨w, hw⟩ := hm
  refine ⟨P.negOnePow • w, ?_⟩
  change P.negOnePow • (((K.X P).d (n - P - 1) (n - P)).hom
    ((P.negOnePow : ℤ) • w)) = _
  rw [map_zsmul]
  rw [hw]
  change P.negOnePow • (P.negOnePow • ((totalProjection K P (n - P) n (by omega)).hom z)) = _
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- The coboundary of a single lift has no coordinates left of its column. -/
lemma cochain_lift_d_below (K : CochainBicomplex.{u,v} R) (n P p q : ℤ)
    (hpq : p + q = n) (hp : p < P) (w : (K.X P).X (n - P - 1)) :
    (totalProjection K p q n hpq).hom
      (((total K).d (n - 1) n).hom
        ((totalInclusion K P (n - P - 1) (n - 1) (by omega)).hom w)) = 0 := by
  have hd := cochain_coordinate_d' K (n - 1) n p q (p - 1) (q - 1)
    (by omega) rfl rfl hpq
    ((totalInclusion K P (n - P - 1) (n - 1) (by omega)).hom w)
  rw [hd, inclusion_coordinate_ne K P (n - P - 1) (p - 1) q (n - 1) _ _
      (Or.inl (by omega)),
    inclusion_coordinate_ne K P (n - P - 1) p (q - 1) (n - 1) _ _
      (Or.inl (by omega)), map_zero, map_zero, smul_zero, add_zero]

/-- At its own column the coboundary of a lift is its signed vertical image. -/
lemma cochain_lift_d_self (K : CochainBicomplex.{u,v} R) (n P : ℤ)
    (w : (K.X P).X (n - P - 1)) :
    (totalProjection K P (n - P) n (by omega)).hom
      (((total K).d (n - 1) n).hom
        ((totalInclusion K P (n - P - 1) (n - 1) (by omega)).hom w)) =
      P.negOnePow • ((K.X P).d (n - P - 1) (n - P)).hom w := by
  have hd := cochain_coordinate_d' K (n - 1) n P (n - P) (P - 1) (n - P - 1)
    (by omega) rfl rfl (by omega)
    ((totalInclusion K P (n - P - 1) (n - 1) (by omega)).hom w)
  rw [hd, inclusion_coordinate_ne K P (n - P - 1) (P - 1) (n - P) (n - 1) _ _
      (Or.inl (by omega)),
    inclusion_coordinate_self, map_zero, zero_add]

/-- Every coboundary is a cocycle, at literal integer cochain indices. -/
lemma cochain_d_d_apply (K : CochainBicomplex.{u,v} R) (n : ℤ)
    (w : (total K).X (n - 1)) :
    ((total K).d n (n + 1)).hom (((total K).d (n - 1) n).hom w) = 0 :=
  DFunLike.congr_fun (Complexes.differential_squared (total K) (n - 1) n (n + 1)) w

/-- Finite elimination on a diagonal, with a moving lower horizontal bound. -/
lemma cochain_boundary_of_lower_bound (K : CochainBicomplex.{u,v} R) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (hc : ColumnsAcyclic K) (n : ℤ) (k : ℕ) :
    ∀ (P : ℤ) (z : (total K).X n),
      ((total K).d n (n + 1)).hom z = 0 →
      (∀ p q (h : p + q = n), p < P → (totalProjection K p q n h).hom z = 0) →
      n - b < P + k →
      ∃ y : (total K).X (n - 1), ((total K).d (n - 1) n).hom y = z := by
  induction k with
  | zero =>
    intro P z hz hbelow hbound
    have hzero : z = 0 := by
      apply total_ext K n
      intro p q hpq
      rw [map_zero]
      by_cases hp : p < P
      · exact hbelow p q hpq hp
      · have := hs p q (Or.inr (by omega))
        exact Subsingleton.elim _ _
    exact ⟨0, (map_zero _).trans hzero.symm⟩
  | succ k ih =>
    intro P z hz hbelow hbound
    obtain ⟨w, hw⟩ := cochain_lift_first K hc n P z hz hbelow
    let t : (total K).X (n - 1) :=
      (totalInclusion K P (n - P - 1) (n - 1) (by omega)).hom w
    let z' := z - ((total K).d (n - 1) n).hom t
    have hz' : ((total K).d n (n + 1)).hom z' = 0 := by
      dsimp only [z']
      rw [map_sub, hz, cochain_d_d_apply, sub_self]
    have hbelow' : ∀ p q (h : p + q = n), p < P + 1 →
        (totalProjection K p q n h).hom z' = 0 := by
      intro p q hpq hp
      dsimp only [z']
      rw [map_sub]
      by_cases hp' : p < P
      · rw [hbelow p q hpq hp', cochain_lift_d_below K n P p q hpq hp' w, sub_self]
      · have hpP : p = P := by omega
        subst p
        have hq : q = n - P := by omega
        subst q
        rw [cochain_lift_d_self K n P w, hw, sub_self]
    obtain ⟨y, hy⟩ := ih (P + 1) z' hz' hbelow' (by omega)
    refine ⟨y + t, ?_⟩
    rw [map_add, hy]
    exact sub_add_cancel z _

/-- Acyclic columns assemble to an acyclic direct-sum cochain total. -/
theorem cochain_columns_acyclic (K : CochainBicomplex.{u,v} R) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (hc : ColumnsAcyclic K) :
    Complexes.Acyclic (total K) := by
  apply (Complexes.acyclic_iff (total K)).mpr
  intro n
  apply le_antisymm (Complexes.boundaries_le_cycles (total K) n)
  intro z hz
  rw [Complexes.cycles_cochain] at hz
  rw [Complexes.boundaries_cochain]
  apply cochain_boundary_of_lower_bound K a b hs hc n (n - b - a + 1).toNat a z hz
  · intro p q hpq hp
    have := hs p q (Or.inl hp)
    exact Subsingleton.elim _ _
  · have := Int.self_le_toNat (n - b - a + 1)
    omega

/-- The signed interchange transfers column assembly to original rows. -/
theorem cochain_rows_acyclic (K : CochainBicomplex.{u,v} R) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (hr : RowsAcyclic K) :
    Complexes.Acyclic (total K) := by
  apply acyclic_of_iso (signedInterchange K)
  apply cochain_columns_acyclic K.flip b a
  · intro p q h
    exact hs q p (h.elim Or.inr Or.inl)
  · exact hr

/-- Original anticommuting columns, with the ordinary differential dh+dv. -/
theorem anticommuting_cochain_columns_acyclic
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.up ℤ)) (a b : ℤ)
    (hs : ∀ p q, p < a ∨ q < b → Subsingleton ((A.column p).X q))
    (hc : ∀ p, Complexes.Acyclic (A.column p)) : Complexes.Acyclic A.total := by
  exact cochain_columns_acyclic A.toCommuting a b hs
    ((anticommuting_columns_acyclic_iff A).mpr hc)

/-- Original anticommuting rows, with the ordinary differential dh+dv. -/
theorem anticommuting_cochain_rows_acyclic
    (A : AnticommutingBicomplex.{u,v} R (ComplexShape.up ℤ)) (a b : ℤ)
    (hs : SupportedQuadrant A.toCommuting a b)
    (hr : ∀ q, Complexes.Acyclic (A.row q)) : Complexes.Acyclic A.total := by
  exact cochain_rows_acyclic A.toCommuting a b hs
    ((anticommuting_rows_acyclic_iff A).mpr hr)

end
end P103.Ch10.TotalComplexAssembly
