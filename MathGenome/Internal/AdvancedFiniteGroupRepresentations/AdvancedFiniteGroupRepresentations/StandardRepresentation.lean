import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.SpechtModules
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardRepresentation
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations
open private standardDiagram standardDiagram_rows from MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardRepresentation
abbrev standardPartition := Specs.AdvancedFiniteGroupRepresentations.standardPartition
abbrev PointModule := Specs.AdvancedFiniteGroupRepresentations.PointModule
abbrev pointVector := @Specs.AdvancedFiniteGroupRepresentations.pointVector
abbrev pointRepresentation := Specs.AdvancedFiniteGroupRepresentations.pointRepresentation
abbrev pointSum := Specs.AdvancedFiniteGroupRepresentations.pointSum
abbrev sumZero := Specs.AdvancedFiniteGroupRepresentations.sumZero

variable {n : ℕ} (h : 2 ≤ n)

theorem standardPartition_parts : parts (standardPartition n h) = [n - 1, 1] := by
  change (YoungDiagram.ofPartition ((standardDiagram n h).toPartition _)).rowLens = _
  rw [YoungDiagram.ofPartition_toPartition, standardDiagram_rows]

theorem standard_cell_iff (r c : ℕ) :
    (r,c) ∈ cells (standardPartition n h) ↔
      (r = 0 ∧ c < n - 1) ∨ (r = 1 ∧ c = 0) := by
  rw [cell_iff, rowLength_eq_getD, standardPartition_parts]
  cases r with
  | zero => simp
  | succ r => cases r with
    | zero => simp
    | succ r => simp

def standardBottom : Cell (standardPartition n h) :=
  ⟨(1,0), (standard_cell_iff h 1 0).mpr (Or.inr ⟨rfl,rfl⟩)⟩

def standardTop : Cell (standardPartition n h) :=
  ⟨(0,0), (standard_cell_iff h 0 0).mpr (Or.inl ⟨rfl, by omega⟩)⟩

theorem standardBottom_ne_top : standardBottom h ≠ standardTop h := by
  intro he
  have := congrArg (fun c : Cell (standardPartition n h) => c.val.1) he
  simp [standardBottom, standardTop] at this

/-- Exactly one cell is in the second row. -/
theorem standard_row (t : Tableau (standardPartition n h)) (a : Fin n) :
    labelRow t a = if a = t (standardBottom h) then 1 else 0 := by
  have hc := (standard_cell_iff h _ _).mp (t.symm a).property
  by_cases ha : a = t (standardBottom h)
  · subst a
    simp [labelRow, Specs.AdvancedFiniteGroupRepresentations.labelRow, standardBottom]
  · rw [ite_eq_right ha]
    rcases hc with hc | hc
    · exact hc.1
    · exfalso
      apply ha
      have he : t.symm a = standardBottom h := Subtype.ext (Prod.ext hc.1 hc.2)
      simpa using congrArg t he

def bottomLabel : Tabloid (standardPartition n h) → Fin n :=
  Quotient.lift (fun t => t (standardBottom h)) (by
    intro t u htu
    change labelRow t = labelRow u at htu
    have he := congrFun htu (t (standardBottom h))
    rw [standard_row h, standard_row h] at he
    simpa using he)

@[simp] theorem bottomLabel_tabloid (t : Tableau (standardPartition n h)) :
    bottomLabel h (tabloid t) = t (standardBottom h) := rfl

theorem bottomLabel_injective : Function.Injective (bottomLabel h) := by
  intro q r
  induction q using Quotient.inductionOn with | _ t =>
    induction r using Quotient.inductionOn with | _ u =>
      intro he
      apply Quotient.sound
      change labelRow t = labelRow u
      funext a
      simp only [standard_row h]
      change t (standardBottom h) = u (standardBottom h) at he
      simp only [he]

theorem bottomLabel_surjective : Function.Surjective (bottomLabel h) := by
  intro a
  let t := canonicalTableau (standardPartition n h)
  let g := Equiv.swap (t (standardBottom h)) a
  exact ⟨tabloid (g • t), by simp [g]⟩

def bottomEquiv : Tabloid (standardPartition n h) ≃ Fin n :=
  Equiv.ofBijective (bottomLabel h) ⟨bottomLabel_injective h, bottomLabel_surjective h⟩

def standardPointEquiv : PermutationModule (standardPartition n h) ≃ₗ[ℂ] PointModule n :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).trans
    ((Finsupp.domLCongr (bottomEquiv h)).trans (MonoidAlgebra.coeffLinearEquiv ℂ).symm)

@[simp] theorem standardPointEquiv_single (q : Tabloid (standardPartition n h)) (z : ℂ) :
    standardPointEquiv h (MonoidAlgebra.single q z) =
      MonoidAlgebra.single (bottomLabel h q) z := by
  simp [standardPointEquiv, bottomEquiv]
  rfl

@[simp] theorem standardPointEquiv_tabloid (t : Tableau (standardPartition n h)) (z : ℂ) :
    standardPointEquiv h (MonoidAlgebra.single (tabloid t) z) =
      z • pointVector (t (standardBottom h)) := by
  simp [pointVector, Specs.AdvancedFiniteGroupRepresentations.pointVector,
    MonoidAlgebra.smul_single]

theorem standardPointEquiv_equivariant (g : SymmetricGroup n)
    (v : PermutationModule (standardPartition n h)) :
    standardPointEquiv h (permutationRepresentation _ g v) =
      pointRepresentation n g (standardPointEquiv h v) := by
  have he : (standardPointEquiv h).toLinearMap ∘ₗ permutationRepresentation _ g =
      pointRepresentation n g ∘ₗ (standardPointEquiv h).toLinearMap := by
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro z
    induction q using Quotient.inductionOn with | _ t =>
      simp [LinearMap.comp_apply, permutationRepresentation_basis,
        pointRepresentation, Specs.AdvancedFiniteGroupRepresentations.pointRepresentation,
        Representation.ofMulAction_single]
      rfl
  exact LinearMap.congr_fun he v


variable (t : Tableau (standardPartition n h))

@[simp] theorem standardColumn_top : labelColumn t (t (standardTop h)) = 0 := by
  simp [labelColumn, Specs.AdvancedFiniteGroupRepresentations.labelColumn, standardTop]

@[simp] theorem standardColumn_bottom : labelColumn t (t (standardBottom h)) = 0 := by
  simp [labelColumn, Specs.AdvancedFiniteGroupRepresentations.labelColumn, standardBottom]

def standardSwap : SymmetricGroup n := Equiv.swap (t (standardTop h)) (t (standardBottom h))

theorem standardSwap_mem : standardSwap h t ∈ columnSubgroup t := by
  intro a
  change labelColumn t (Equiv.swap (t (standardTop h)) (t (standardBottom h)) a) = _
  by_cases ha : a = t (standardTop h)
  · subst a; simp
  · by_cases hb : a = t (standardBottom h)
    · subst a; simp
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem standardSwap_ne_one : standardSwap h t ≠ 1 := by
  intro he
  have he' := Equiv.congr_fun he (t (standardTop h))
  have hn := t.injective.ne (standardBottom_ne_top h)
  exact hn (by simpa [standardSwap] using he')

theorem standardColumn_fix_bottom (g : columnSubgroup t)
    (hg : g.val (t (standardBottom h)) = t (standardBottom h)) : g.val = 1 := by
  have hr : g.val ∈ rowSubgroup t := by
    intro a
    change labelRow t (g.val a) = labelRow t a
    simp only [standard_row h]
    have he : g.val a = t (standardBottom h) ↔ a = t (standardBottom h) := by
      constructor
      · intro he
        exact g.val.injective (he.trans hg.symm)
      · rintro rfl
        exact hg
    simp only [he]
  have hm : g.val ∈ rowSubgroup t ⊓ columnSubgroup t := ⟨hr, g.property⟩
  rw [row_column_inf] at hm
  exact hm

theorem standardColumn_cases (g : columnSubgroup t) :
    g.val = 1 ∨ g.val = standardSwap h t := by
  by_cases hg : g.val (t (standardBottom h)) = t (standardBottom h)
  · exact Or.inl (standardColumn_fix_bottom h t g hg)
  · have hc := g.property (t (standardBottom h))
    change labelColumn t (g.val (t (standardBottom h))) = labelColumn t (t (standardBottom h)) at hc
    rw [standardColumn_bottom] at hc
    let c := t.symm (g.val (t (standardBottom h)))
    have hcc : c.val.2 = 0 := hc
    have hs := (standard_cell_iff h _ _).mp c.property
    have ht : g.val (t (standardBottom h)) = t (standardTop h) := by
      rcases hs with hs | hs
      · have he : c = standardTop h := Subtype.ext (Prod.ext hs.1 hcc)
        simpa [c] using congrArg t he
      · have he : c = standardBottom h := Subtype.ext (Prod.ext hs.1 hs.2)
        exact False.elim (hg (by simpa [c] using congrArg t he))
    have hf := standardColumn_fix_bottom h t
      (⟨standardSwap h t * g.val, (columnSubgroup t).mul_mem (standardSwap_mem h t) g.property⟩)
      (by change standardSwap h t (g.val (t (standardBottom h))) = _; rw [ht]; simp [standardSwap])
    right
    have he := congrArg (fun k : SymmetricGroup n => standardSwap h t * k) hf
    simpa [standardSwap, mul_assoc] using he

theorem standard_polytabloid :
    polytabloid t = MonoidAlgebra.single (tabloid t) 1 -
      MonoidAlgebra.single (tabloid (standardSwap h t • t)) 1 := by
  classical
  let s : columnSubgroup t := ⟨standardSwap h t, standardSwap_mem h t⟩
  have hs : s ≠ 1 := fun he => standardSwap_ne_one h t (congrArg Subtype.val he)
  have hu : (Finset.univ : Finset (columnSubgroup t)) = {1, s} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases standardColumn_cases h t g with hg | hg
    · exact Or.inl (Subtype.ext hg)
    · exact Or.inr (Subtype.ext hg)
  rw [polytabloid_sum, hu, Finset.sum_pair (Ne.symm hs)]
  simp [s, permutationSign,
    Specs.AdvancedFiniteGroupRepresentations.permutationSign, standardSwap,
    Equiv.Perm.sign_swap (t.injective.ne (Ne.symm (standardBottom_ne_top h))),
    sub_eq_add_neg, ← MonoidAlgebra.single_neg]

theorem standardPointEquiv_polytabloid :
    standardPointEquiv h (polytabloid t) =
      pointVector (t (standardBottom h)) - pointVector (t (standardTop h)) := by
  rw [standard_polytabloid h t, map_sub]
  simp [standardSwap]
  rfl


/-- Any ordered pair of distinct labels occurs in the first column. -/
theorem standardTableau_pair (a b : Fin n) (hab : a ≠ b) :
    ∃ t : Tableau (standardPartition n h),
      t (standardBottom h) = b ∧ t (standardTop h) = a := by
  let t₀ := canonicalTableau (standardPartition n h)
  let t₁ := Equiv.swap (t₀ (standardBottom h)) b • t₀
  have hb : t₁ (standardBottom h) = b := by simp [t₁]
  have hc : t₁ (standardTop h) ≠ b := by
    rw [← hb]
    exact t₁.injective.ne (Ne.symm (standardBottom_ne_top h))
  refine ⟨Equiv.swap (t₁ (standardTop h)) a • t₁, ?_, ?_⟩
  · change Equiv.swap (t₁ (standardTop h)) a (t₁ (standardBottom h)) = b
    rw [hb, Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) (Ne.symm hab)]
  · simp

@[simp] theorem pointSum_single (a : Fin n) (z : ℂ) :
    pointSum n (MonoidAlgebra.single a z) = z := by
  classical
  change (∑ b : Fin n, (MonoidAlgebra.single a z).coeff b) = z
  simp

@[simp] theorem pointSum_vector (a : Fin n) : pointSum n (pointVector a) = 1 :=
  pointSum_single a 1

theorem point_expansion (v : PointModule n) :
    ∑ a : Fin n, v.coeff a • pointVector a = v := by
  classical
  ext a
  simp [pointVector, Specs.AdvancedFiniteGroupRepresentations.pointVector,
    MonoidAlgebra.coeff_sum, MonoidAlgebra.smul_single]

theorem pointSum_equivariant (g : SymmetricGroup n) (v : PointModule n) :
    pointSum n (pointRepresentation n g v) = pointSum n v := by
  have he : pointSum n ∘ₗ pointRepresentation n g = pointSum n := by
    apply MonoidAlgebra.lhom_ext'
    intro a
    apply LinearMap.ext
    intro z
    simp [LinearMap.comp_apply,
      pointRepresentation, Specs.AdvancedFiniteGroupRepresentations.pointRepresentation,
      Representation.ofMulAction_single]
  exact LinearMap.congr_fun he v

theorem sumZero_stable (g : SymmetricGroup n) (v : PointModule n)
    (hv : v ∈ sumZero n) : pointRepresentation n g v ∈ sumZero n := by
  change pointSum n _ = 0
  rw [pointSum_equivariant]
  exact hv

theorem standard_specht_eq_sumZero :
    Submodule.map (standardPointEquiv h).toLinearMap (spechtSpan (standardPartition n h)) =
      sumZero n := by
  classical
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro v ⟨t, rfl⟩
    change pointSum n (standardPointEquiv h (polytabloid t)) = 0
    rw [standardPointEquiv_polytabloid, map_sub, pointSum_vector, pointSum_vector, sub_self]
  · intro v hv
    let b : Fin n := ⟨0, by omega⟩
    have hd : ∀ a : Fin n, pointVector a - pointVector b ∈
        Submodule.map (standardPointEquiv h).toLinearMap (spechtSpan (standardPartition n h)) := by
      intro a
      by_cases hab : a = b
      · subst a; simp
      · obtain ⟨t, ht, hb⟩ := standardTableau_pair h b a (Ne.symm hab)
        rw [← ht, ← hb, ← standardPointEquiv_polytabloid]
        exact Submodule.mem_map.mpr ⟨polytabloid t, polytabloid_mem_specht t, rfl⟩
    have he : ∑ a : Fin n, v.coeff a • (pointVector a - pointVector b) = v := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, point_expansion]
      change v - (pointSum n v) • pointVector b = v
      change pointSum n v = 0 at hv
      rw [hv, zero_smul, sub_zero]
    rw [← he]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (hd a))

theorem point_finrank (n : ℕ) : Module.finrank ℂ (PointModule n) = n := by
  rw [(Specs.AdvancedFiniteGroupRepresentations.pointCoordinates n).finrank_eq]
  exact Module.finrank_fin_fun ℂ

include h in
theorem sumZero_finrank : Module.finrank ℂ (sumZero n) = n - 1 := by
  let : FiniteDimensional ℂ (PointModule n) :=
    Module.Finite.equiv (Specs.AdvancedFiniteGroupRepresentations.pointCoordinates n).symm
  have hn : pointSum n ≠ 0 := by
    intro he
    have hh := pointSum_vector (⟨0, by omega⟩ : Fin n)
    rw [he, LinearMap.zero_apply] at hh
    exact zero_ne_one hh
  have he := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  rw [point_finrank] at he
  change Module.finrank ℂ (pointSum n).ker = n - 1
  omega

theorem standard_specht_finrank :
    Module.finrank ℂ (SpechtModule (standardPartition n h)) = n - 1 := by
  rw [← (standardPointEquiv h).finrank_map_eq, standard_specht_eq_sumZero, sumZero_finrank h]

/-- FR B09: an equivariant identification, with the original basis and polytabloids. -/
theorem standard_representation : Specs.AdvancedFiniteGroupRepresentations.standard_representationType := by
  intro n h
  refine ⟨standardPartition_parts h, standardBottom h, standardTop h,
    standardPointEquiv h, rfl, rfl, standardPointEquiv_tabloid h,
    standardPointEquiv_equivariant h, standardPointEquiv_polytabloid h,
    standard_specht_eq_sumZero h, sumZero_stable, standard_specht_finrank h⟩

theorem point_coordinates : Specs.AdvancedFiniteGroupRepresentations.point_coordinatesType := by
  refine ⟨fun _ _ _ => rfl, ?_, fun _ _ => rfl⟩
  intro n g x a
  exact Representation.coeff_ofMulAction g x a

/-- The sum-zero standard representation of S₃ is two dimensional. -/
theorem standard_S3 : Specs.AdvancedFiniteGroupRepresentations.standard_S3Type := by
  exact ⟨standardPartition_parts (by decide), standard_specht_finrank (by decide)⟩

end AdvancedFiniteGroupRepresentations
