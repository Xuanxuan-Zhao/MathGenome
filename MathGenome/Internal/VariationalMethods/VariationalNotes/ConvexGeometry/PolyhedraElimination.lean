import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedraElimination
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Pi

open Set
noncomputable section
universe u v w
namespace VariationalNotes.ConvexGeometry

def IsPolyhedron {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) : Prop :=
  Specs.IsPolyhedron C

theorem affine_equality_two_inequalities : Specs.affine_equality_two_inequalities := by
  intro E _ _ a b
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff]
  exact ⟨fun h => ⟨h.le, neg_le_neg h.ge⟩, fun h => le_antisymm h.1 (neg_le_neg_iff.mp h.2)⟩

theorem polyhedron_empty_univ : Specs.polyhedron_empty_univ := by
  intro E _ _
  constructor
  · refine ⟨{AffineMap.const ℝ E 1}, ?_⟩
    ext x
    simp
  · refine ⟨∅, ?_⟩
    ext x
    simp

theorem polyhedron_affine_preimage : Specs.polyhedron_affine_preimage := by
  intro E F _ _ _ _ f C hC
  classical
  obtain ⟨s, rfl⟩ := hC
  refine ⟨s.image (fun a => a.comp f), ?_⟩
  ext x
  simp

/-- Feasibility of finite lower and upper lists, with all four empty-list cases. -/
lemma finite_bounds (L U : Finset ℝ) :
    (∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u) ↔
      ∀ l ∈ L, ∀ u ∈ U, l ≤ u := by
  classical
  constructor
  · rintro ⟨t, htL, htU⟩ l hl u hu
    exact (htL l hl).trans (htU u hu)
  · intro h
    by_cases hL : L.Nonempty
    · exact ⟨L.max' hL, fun l hl => Finset.le_max' L l hl,
        fun u hu => h _ (Finset.max'_mem L hL) u hu⟩
    · by_cases hU : U.Nonempty
      · exact ⟨U.min' hU, fun l hl => (hL ⟨l, hl⟩).elim,
          fun u hu => Finset.min'_le U u hu⟩
      · exact ⟨0, fun l hl => (hL ⟨l, hl⟩).elim,
          fun u hu => (hU ⟨u, hu⟩).elim⟩

section ScalarElimination
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- The coefficient of the coordinate being eliminated. -/
def scalarCoefficient (a : (ℝ × E) →ᵃ[ℝ] ℝ) : ℝ := a.linear (1, 0)

/-- The residual affine row, obtained by setting that coordinate to zero. -/
def scalarResidual (a : (ℝ × E) →ᵃ[ℝ] ℝ) : E →ᵃ[ℝ] ℝ :=
  a.comp (LinearMap.inr ℝ ℝ E).toAffineMap

/-- The affine upper or lower bound from a row with nonzero coefficient. -/
def scalarBound (a : (ℝ × E) →ᵃ[ℝ] ℝ) : E →ᵃ[ℝ] ℝ :=
  (-(scalarCoefficient a)⁻¹) • scalarResidual a

lemma scalar_decomposition (a : (ℝ × E) →ᵃ[ℝ] ℝ) (t : ℝ) (x : E) :
    a (t, x) = scalarCoefficient a * t + scalarResidual a x := by
  have hp : (t, x) = t • ((1 : ℝ), (0 : E)) +ᵥ ((0 : ℝ), x) := by simp
  rw [hp, a.map_vadd]
  simpa [scalarCoefficient, scalarResidual, mul_comm] using
    a.linear.map_smul t ((1 : ℝ), (0 : E))

lemma scalar_positive (a : (ℝ × E) →ᵃ[ℝ] ℝ) (h : 0 < scalarCoefficient a)
    (t : ℝ) (x : E) : a (t,x) ≤ 0 ↔ t ≤ scalarBound a x := by
  rw [scalar_decomposition]
  change scalarCoefficient a * t + scalarResidual a x ≤ 0 ↔
    t ≤ -(scalarCoefficient a)⁻¹ * scalarResidual a x
  rw [show -(scalarCoefficient a)⁻¹ * scalarResidual a x =
      -(scalarResidual a x) / scalarCoefficient a by simp [div_eq_mul_inv, mul_comm]]
  rw [le_div_iff₀ h]
  constructor <;> intro ht <;> nlinarith

lemma scalar_negative (a : (ℝ × E) →ᵃ[ℝ] ℝ) (h : scalarCoefficient a < 0)
    (t : ℝ) (x : E) : a (t,x) ≤ 0 ↔ scalarBound a x ≤ t := by
  rw [scalar_decomposition]
  change scalarCoefficient a * t + scalarResidual a x ≤ 0 ↔
    -(scalarCoefficient a)⁻¹ * scalarResidual a x ≤ t
  rw [show -(scalarCoefficient a)⁻¹ * scalarResidual a x =
      -(scalarResidual a x) / scalarCoefficient a by simp [div_eq_mul_inv, mul_comm]]
  rw [div_le_iff_of_neg h]
  constructor <;> intro ht <;> nlinarith

/-- One complete Fourier--Motzkin step. -/
def eliminatedRows (s : Finset ((ℝ × E) →ᵃ[ℝ] ℝ)) : Finset (E →ᵃ[ℝ] ℝ) := by
  classical
  exact (s.filter (fun a => scalarCoefficient a = 0)).image scalarResidual ∪
    ((s.filter (fun a => scalarCoefficient a < 0)) ×ˢ
      (s.filter (fun a => 0 < scalarCoefficient a))).image
        (fun p => scalarBound p.1 - scalarBound p.2)

lemma eliminatedRows_iff (s : Finset ((ℝ × E) →ᵃ[ℝ] ℝ)) (x : E) :
    (∀ b ∈ eliminatedRows s, b x ≤ 0) ↔
      ∃ t : ℝ, ∀ a ∈ s, a (t,x) ≤ 0 := by
  classical
  have hc : (∀ b ∈ eliminatedRows s, b x ≤ 0) ↔
      (∀ a ∈ s, scalarCoefficient a = 0 → scalarResidual a x ≤ 0) ∧
      (∀ a ∈ s, scalarCoefficient a < 0 → ∀ b ∈ s,
        0 < scalarCoefficient b → scalarBound a x ≤ scalarBound b x) := by
    constructor
    · intro h
      constructor
      · intro a ha hz
        exact h _ (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨a, Finset.mem_filter.mpr ⟨ha, hz⟩, rfl⟩))
      · intro a ha hn b hb hp
        have hh := h (scalarBound a - scalarBound b)
          (Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨(a,b), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha,hn⟩,
              Finset.mem_filter.mpr ⟨hb,hp⟩⟩, rfl⟩))
        change scalarBound a x - scalarBound b x ≤ 0 at hh
        exact sub_nonpos.mp hh
    · rintro ⟨hz, hp⟩ b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact hz a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      · obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
        exact sub_nonpos.mpr (hp a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
          b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2)
  rw [hc]
  constructor
  · rintro ⟨hzero, hpairs⟩
    have hbetween : ∃ t : ℝ,
        (∀ a ∈ s, scalarCoefficient a < 0 → scalarBound a x ≤ t) ∧
        (∀ a ∈ s, 0 < scalarCoefficient a → t ≤ scalarBound a x) := by
      let L := (s.filter (fun a => scalarCoefficient a < 0)).image (fun a => scalarBound a x)
      let U := (s.filter (fun a => 0 < scalarCoefficient a)).image (fun a => scalarBound a x)
      have hh : ∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ ∀ u ∈ U, t ≤ u :=
        (finite_bounds L U).mpr (by
          intro l hl u hu
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
          exact hpairs a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
            b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2)
      obtain ⟨t, htL, htU⟩ := hh
      exact ⟨t, fun a ha hn => htL _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hn⟩, rfl⟩),
        fun a ha hp => htU _ (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨ha, hp⟩, rfl⟩)⟩
    obtain ⟨t, htL, htU⟩ := hbetween
    refine ⟨t, fun a ha => ?_⟩
    rcases lt_trichotomy (scalarCoefficient a) 0 with hn | hz | hp
    · exact (scalar_negative a hn t x).mpr (htL a ha hn)
    · simpa [scalar_decomposition, hz] using hzero a ha hz
    · exact (scalar_positive a hp t x).mpr (htU a ha hp)
  · rintro ⟨t, ht⟩
    constructor
    · intro a ha hz
      simpa [scalar_decomposition, hz] using ht a ha
    · intro a ha hn b hb hp
      exact ((scalar_negative a hn t x).mp (ht a ha)).trans
        ((scalar_positive b hp t x).mp (ht b hb))

end ScalarElimination

theorem polyhedron_scalar_projection : Specs.polyhedron_scalar_projection := by
  intro E _ _ C hC
  obtain ⟨s, rfl⟩ := hC
  refine ⟨eliminatedRows s, ?_⟩
  ext x
  change (∃ p, (∀ a ∈ s, a p ≤ 0) ∧ p.2 = x) ↔ (∀ b ∈ eliminatedRows s, b x ≤ 0)
  rw [eliminatedRows_iff]
  constructor
  · rintro ⟨⟨t, y⟩, ht, rfl⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨(t,x), ht, rfl⟩

/-- Eliminate a whole finite coordinate block, by repeated scalar elimination. -/
lemma polyhedron_fin_projection {F : Type v} [AddCommGroup F] [Module ℝ F]
    (n : ℕ) (C : Set ((Fin n → ℝ) × F)) (hC : IsPolyhedron C) :
    IsPolyhedron (Prod.snd '' C) := by
  induction n with
  | zero =>
    have hh := polyhedron_affine_preimage
      (LinearMap.inr ℝ (Fin 0 → ℝ) F).toAffineMap C hC
    change IsPolyhedron _ at hh
    convert hh using 1
    ext y
    constructor
    · rintro ⟨⟨x,z⟩, hx, rfl⟩
      have hx0 : x = 0 := Subsingleton.elim _ _
      simpa [hx0] using hx
    · intro hy
      exact ⟨(0,y), hy, rfl⟩
  | succ n ih =>
    let g : (ℝ × ((Fin n → ℝ) × F)) →ₗ[ℝ] ((Fin (n+1) → ℝ) × F) :=
      ((Fin.consLinearEquiv ℝ (fun _ : Fin (n+1) => ℝ)).toLinearMap.prodMap
        (LinearMap.id : F →ₗ[ℝ] F)).comp
          (LinearEquiv.prodAssoc ℝ ℝ (Fin n → ℝ) F).symm.toLinearMap
    have hpre := polyhedron_affine_preimage g.toAffineMap C hC
    have hone := polyhedron_scalar_projection _ hpre
    have hall := ih _ hone
    convert hall using 1
    ext y
    constructor
    · rintro ⟨⟨x,z⟩, hx, rfl⟩
      refine ⟨(Fin.tail x,z), ?_, rfl⟩
      refine ⟨(x 0,(Fin.tail x,z)), ?_, rfl⟩
      change (Fin.cons (x 0) (Fin.tail x), z) ∈ C
      simpa using hx
    · rintro ⟨⟨x,z⟩, ⟨⟨t,p⟩, hp, heq⟩, rfl⟩
      cases heq
      exact ⟨(Fin.cons t x,z), hp, rfl⟩

theorem polyhedron_projection : Specs.polyhedron_projection := by
  intro E F _ _ _ _ _ C hC
  change IsPolyhedron (Prod.snd '' C)
  let e := (Module.finBasis ℝ E).equivFun
  let g := e.symm.toLinearMap.prodMap (LinearMap.id : F →ₗ[ℝ] F)
  have hh := polyhedron_fin_projection _ _
    (polyhedron_affine_preimage g.toAffineMap C hC)
  convert hh using 1
  ext y
  constructor
  · rintro ⟨⟨x,z⟩, hx, rfl⟩
    exact ⟨(e x,z), by simpa [g] using hx, rfl⟩
  · rintro ⟨⟨x,z⟩, hx, rfl⟩
    exact ⟨(e.symm x,z), hx, rfl⟩

lemma polyhedron_inter {E : Type u} [AddCommGroup E] [Module ℝ E]
    {C D : Set E} (hC : IsPolyhedron C) (hD : IsPolyhedron D) : IsPolyhedron (C ∩ D) := by
  classical
  obtain ⟨s,rfl⟩ := hC
  obtain ⟨t,rfl⟩ := hD
  refine ⟨s ∪ t, ?_⟩
  ext x
  simp [or_imp, forall_and]

/-- The singleton is the intersection of the two inequalities for each coordinate.
This also applies to the zero-dimensional space, where the row family is empty. -/
lemma polyhedron_zero {E : Type u} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] : IsPolyhedron ({0} : Set E) := by
  classical
  let b := Module.finBasis ℝ E
  let a : Fin (Module.finrank ℝ E) → (E →ᵃ[ℝ] ℝ) := fun i => (b.coord i).toAffineMap
  refine ⟨Finset.univ.image a ∪ Finset.univ.image (fun i => -a i), ?_⟩
  ext x
  constructor
  · rintro rfl
    intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      simp [a]
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      change -(b.coord i) 0 ≤ 0
      simp
  · intro hx
    have hx0 : b.equivFun x = b.equivFun 0 := by
      ext i
      have hp := hx (a i) (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, rfl⟩))
      have hn := hx (-a i) (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, rfl⟩))
      change b.coord i x ≤ 0 at hp
      change -b.coord i x ≤ 0 at hn
      have hz : b.coord i x = 0 := by linarith
      simpa [Module.Basis.equivFun_apply] using hz
    exact b.equivFun.injective hx0

/-- The graph of an affine map restricted to a polyhedron is a polyhedron. -/
lemma polyhedron_graph {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (f : E →ᵃ[ℝ] F) (C : Set E) (hC : IsPolyhedron C) :
    IsPolyhedron {p : E × F | p.1 ∈ C ∧ f p.1 = p.2} := by
  have h₁ := polyhedron_affine_preimage (AffineMap.fst : E × F →ᵃ[ℝ] E) C hC
  have h₂ := polyhedron_affine_preimage
    (f.comp AffineMap.fst - (AffineMap.snd : E × F →ᵃ[ℝ] F)) {0} polyhedron_zero
  convert polyhedron_inter h₁ h₂ using 1
  ext p
  change (p.1 ∈ C ∧ f p.1 = p.2) ↔ (p.1 ∈ C ∧ f p.1 - p.2 = 0)
  rw [sub_eq_zero]

theorem polyhedron_affine_image : Specs.polyhedron_affine_image := by
  intro E F _ _ _ _ _ _ f C hC
  have hh := polyhedron_projection _ (polyhedron_graph f C hC)
  convert hh using 1
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(x,f x), ⟨hx,rfl⟩, rfl⟩
  · rintro ⟨⟨x,z⟩, ⟨hx,hf⟩, rfl⟩
    exact ⟨x,hx,hf⟩

theorem polyhedron_coordinate_projection : Specs.polyhedron_coordinate_projection := by
  intro ι κ _ _ p C hC
  let f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun x => x ∘ p
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact polyhedron_affine_image f.toAffineMap C hC

theorem polyhedron_isClosed : Specs.polyhedron_isClosed := by
  intro E _ _ _ _ _ _ _ C hC
  obtain ⟨s,rfl⟩ := hC
  have ha (a : E →ᵃ[ℝ] ℝ) : Continuous a := by
    have hh : Continuous (fun x => a.linear x + a 0) :=
      a.linear.continuous_of_finiteDimensional.add continuous_const
    have heq : (a : E → ℝ) = (fun x => a.linear x + a 0) := a.decomp
    rw [heq]
    exact hh
  have heq : {x | ∀ a ∈ s, a x ≤ 0} = ⋂ a ∈ s, {x | a x ≤ 0} := by ext; simp
  rw [heq]
  exact isClosed_biInter (fun a _ => isClosed_le (ha a) continuous_const)

theorem polyhedron_affine_image_isClosed : Specs.polyhedron_affine_image_isClosed := by
  intro E F _ _ _ _ _ _ _ _ _ _ f C hC
  exact polyhedron_isClosed _ (polyhedron_affine_image f C hC)

end VariationalNotes.ConvexGeometry
