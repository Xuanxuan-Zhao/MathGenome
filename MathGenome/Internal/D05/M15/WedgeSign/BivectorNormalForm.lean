import MathGenome.Internal.Specs.D05.M15.WedgeSign.BivectorNormalForm
import MathGenome.Internal.D05.M15.ExteriorPairing
import MathGenome.Internal.D05.M11.SymplecticBlocks
import MathGenome.Internal.D05.M07.Biddual
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

noncomputable section
namespace D05.M15.WedgeSign.BivectorNormalForm
open Module Matrix
open Specs.D05.M15.WedgeSign.BivectorNormalForm
open scoped BigOperators
universe u v w
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[simp] lemma form_apply (z : ⋀[K]^2 V) (phi psi : Dual K V) :
    form z phi psi = ExteriorPairing.pairing K V 2 (wedge phi psi) z := rfl

theorem elementary : Specs.D05.M15.WedgeSign.BivectorNormalForm.elementary := by
  intro K V _ _ _ u v phi psi
  rw [form_apply, wedge, wedge, ExteriorPairing.elementary]
  erw [Matrix.det_fin_two]
  rfl

theorem alternating : Specs.D05.M15.WedgeSign.BivectorNormalForm.alternating := by
  intro K V _ _ _ z phi
  rw [form_apply]
  have hz : wedge (K := K) phi phi = 0 :=
    (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![phi, phi] (i := 0) (j := 1)
      rfl (by decide)
  rw [hz, map_zero, LinearMap.zero_apply]

/-- Elementary covector wedges separate bivectors in finite dimension. -/
lemma ext_pairing [FiniteDimensional K V] {z t : ⋀[K]^2 V}
    (h : ∀ phi psi, form z phi psi = form t phi psi) : z = t := by
  have he : (ExteriorPairing.pairing K V 2).flip z =
      (ExteriorPairing.pairing K V 2).flip t := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    have hf : f = ![f 0, f 1] := by ext i; fin_cases i <;> rfl
    rw [hf]
    exact h (f 0) (f 1)
  apply D05.M07.Biddual.evaluation_injective (K := K)
  ext L
  obtain ⟨e, he'⟩ := ExteriorPairing.perfect (K := K) (V := V) 2
  obtain ⟨a, rfl⟩ := e.surjective L
  have ha := LinearMap.congr_fun he a
  change (e a) z = (e a) t
  change Specs.D05.M15.ExteriorPairing.pairing_value K V 2 a z =
    Specs.D05.M15.ExteriorPairing.pairing_value K V 2 a t at ha
  rw [← he'] at ha
  exact ha

lemma form_sum {I : Type*} (s : Finset I) (z : I → ⋀[K]^2 V)
    (phi psi : Dual K V) : form (∑ i ∈ s, z i) phi psi = ∑ i ∈ s, form (z i) phi psi := by
  simp only [form_apply, map_sum]

lemma form_smul (a : K) (z : ⋀[K]^2 V) (phi psi : Dual K V) :
    form (a • z) phi psi = a * form z phi psi := by
  simp only [form_apply, map_smul, smul_eq_mul]

theorem matrix_entries : Specs.D05.M15.WedgeSign.BivectorNormalForm.matrix_entries := by
  intro K V _ _ _ n b a
  classical
  dsimp only
  intro i j
  simp only [matrix]
  simp_rw [form_sum, form_smul]
  have hel (k l : Fin n) :
      form (wedge (b k) (b l)) (b.coord i) (b.coord j) =
        (if k = i then 1 else 0) * (if l = j then 1 else 0) -
        (if l = i then 1 else 0) * (if k = j then 1 else 0) := by
    rw [elementary]
    simp [Basis.coord_apply, Finsupp.single_apply]
  trans ∑ k, ∑ l ∈ Finset.univ.filter (fun l => k < l),
    a k l * ((if k = i then 1 else 0) * (if l = j then 1 else 0) -
      (if l = i then 1 else 0) * (if k = j then 1 else 0))
  · apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    exact congrArg (fun t : K => a k l * t) (hel k l)
  · have hh (x : Fin n) : (if x < j then (if x = i then a x j else 0) else 0) =
        (if x = i then (if i < j then a i j else 0) else 0) := by
      by_cases hx : x = i <;> simp [hx]
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    by_cases hij : i < j
    · simp [hij, not_lt_of_ge hij.le, hh]
    · by_cases hji : j < i
      · simp [hij, hji, hh]
      · simp [hij, hji, hh]

/-- Matrix rank is the intrinsic rank of the curried alternating form. -/
theorem matrix_rank : Specs.D05.M15.WedgeSign.BivectorNormalForm.matrix_rank := by
  intro K V _ _ _ I _ b z
  classical
  have hm : (matrix b z)ᵀ = LinearMap.toMatrix b.dualBasis b.dualBasis.dualBasis (form z) := by
    ext i j
    simp [matrix, LinearMap.toMatrix_apply, Basis.coe_dualBasis]
  rw [← Matrix.rank_transpose, hm,
    Matrix.rank_eq_finrank_range_toLin _ b.dualBasis.dualBasis b.dualBasis,
    Matrix.toLin_toMatrix]

/-- A normal basis for the alternating form becomes a basis of vectors by
finite biduality. Testing on the original covector basis fixes all signs. -/
theorem normal_form : Specs.D05.M15.WedgeSign.BivectorNormalForm.normal_form := by
  intro K V _ _ _ _ z
  classical
  obtain ⟨r, s, b, hb, hd, hr, hrad⟩ :=
    D05.M11.SymplecticBlocks.normal_basis (form z) (alternating z)
  obtain ⟨e, he, _⟩ := D05.M07.Biddual.canonical_isomorphism (K := K) (V := V)
  let c := b.dualBasis.map e.symm
  have hc (i j : Specs.D05.M11.SymplecticBlocks.BlockIndex r s) :
      b i (c j) = if i = j then 1 else 0 := by
    rw [← he]
    simp only [c, Basis.map_apply, e.apply_symm_apply]
    exact b.dualBasis_apply_self j i
  have hb' (a d : Specs.D05.M11.SymplecticBlocks.BlockIndex r s) :
      form z (b a) (b d) =
        match a, d with
        | .inl (i, j), .inl (k, l) =>
          if i = k then (if j = 0 then (if l = 0 then 0 else 1)
            else (if l = 0 then -1 else 0)) else 0
        | _, _ => 0 := by
    rw [hb]
    rcases a with ⟨i, j⟩ | a <;> rcases d with ⟨k, l⟩ | d
    · fin_cases j <;> fin_cases l <;> rfl
    · rfl
    · rfl
    · rfl
  let u : Fin r → V := fun i => c (.inl (i, 0))
  let v : Fin r → V := fun i => c (.inl (i, 1))
  have hi : LinearIndependent K (fun ij : Fin r × Fin 2 =>
      if ij.2 = 0 then u ij.1 else v ij.1) := by
    have hfun : (fun ij : Fin r × Fin 2 => if ij.2 = 0 then u ij.1 else v ij.1) =
        c ∘ Sum.inl := by
      funext ⟨i, j⟩
      fin_cases j <;> simp [u, v]
    rw [hfun]
    exact c.linearIndependent.comp _ Sum.inl_injective
  refine ⟨r, u, v, hi, ?_, hr, fun b' => (matrix_rank b' z).trans hr⟩
  apply ext_pairing
  suffices hB : form z = form (∑ i, wedge (u i) (v i)) by
    intro phi psi; exact LinearMap.congr_fun (LinearMap.congr_fun hB phi) psi
  apply b.ext
  intro a
  apply b.ext
  intro d
  change form z (b a) (b d) = form (∑ i, wedge (u i) (v i)) (b a) (b d)
  have hs : form (∑ i, wedge (u i) (v i)) (b a) (b d) =
      ∑ i, (b a (u i) * b d (v i) - b a (v i) * b d (u i)) := by
    simp only [form_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact elementary (u i) (v i) (b a) (b d)
  rw [hs, hb']
  rcases a with ⟨i, j⟩ | a <;> rcases d with ⟨k, l⟩ | d
  · fin_cases j <;> fin_cases l <;> by_cases hik : i = k <;>
      simp [u, v, hc, eq_comm, hik]
  · fin_cases j <;>
      simp [u, v, hc]
  · fin_cases l <;>
      simp [u, v, hc]
  · simp [u, v, hc]

/-- A single wedge has image contained in the span of its two evaluation maps. -/
lemma decomposable_rank_le_two [FiniteDimensional K V] (u v : V) :
    Module.finrank K (LinearMap.range (form (wedge (K := K) u v))) ≤ 2 := by
  classical
  let U : Submodule K (Dual K (Dual K V)) :=
    Submodule.span K {Dual.eval K V u, Dual.eval K V v}
  have hle : LinearMap.range (form (wedge (K := K) u v)) ≤ U := by
    rintro _ ⟨phi, rfl⟩
    have hm : form (wedge (K := K) u v) phi =
        phi u • Dual.eval K V v - phi v • Dual.eval K V u := by
      ext psi
      rw [elementary]
      simp
    rw [hm]
    exact U.sub_mem
      (U.smul_mem _ (Submodule.subset_span (by simp)))
      (U.smul_mem _ (Submodule.subset_span (by simp)))
  calc
    Module.finrank K (LinearMap.range (form (wedge (K := K) u v))) ≤
        Module.finrank K U := Submodule.finrank_mono hle
    _ ≤ 2 := by
      let S : Set (Dual K (Dual K V)) := {Dual.eval K V u, Dual.eval K V v}
      have h := finrank_span_le_card (R := K) S
      have hs : S.toFinset = {Dual.eval K V u, Dual.eval K V v} := by
        ext x
        simp [S]
      rw [hs] at h
      exact h.trans Finset.card_le_two

theorem nonzero_decomposable_rank :
    Specs.D05.M15.WedgeSign.BivectorNormalForm.nonzero_decomposable_rank := by
  intro K V _ _ _ _ u v hz
  obtain ⟨r, us, vs, hi, heq, hr, hm⟩ := normal_form (wedge (K := K) u v)
  have hn : r ≠ 0 := by
    intro he
    subst r
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at heq
    exact hz heq
  have hle := decomposable_rank_le_two (K := K) u v
  omega

end D05.M15.WedgeSign.BivectorNormalForm
