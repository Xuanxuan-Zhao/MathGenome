import MathGenome.Internal.D07.Ch14.IndependentEmbeddings
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace GaloisFormalization.PV

open Matrix Module

/-- A matrix cocycle over a finite Galois extension is a right coboundary.
The proof uses sums over the Galois group and works in arbitrary characteristic. -/
theorem finiteSemilinearDescent (k E : Type*) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] (m : ℕ)
    (a : Gal(E/k) → GeneralLinearGroup (Fin m) E)
    (ha : ∀ γ η, a (γ * η) = a γ * GeneralLinearGroup.map γ.toRingEquiv.toRingHom (a η)) :
    ∃ B : GeneralLinearGroup (Fin m) E,
      ∀ γ, GeneralLinearGroup.map γ.toRingEquiv.toRingHom B = B * a γ := by
  classical
  let T (γ : Gal(E/k)) : (Fin m → E) →+ (Fin m → E) :=
    { toFun := fun v => (fun i => γ (v i)) ᵥ* (↑((a γ)⁻¹) : Matrix (Fin m) (Fin m) E)
      map_zero' := by
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.zero_vecMul _
      map_add' := by
        intro v w
        simp only [Pi.add_apply, map_add, ← Pi.add_def, Matrix.add_vecMul] }
  have hT_mul (γ η : Gal(E/k)) (v : Fin m → E) : T γ (T η v) = T (γ * η) v := by
    have hmap : (fun i => γ (T η v i)) =
        (fun i => (γ * η) (v i)) ᵥ*
          (↑(GeneralLinearGroup.map γ.toRingEquiv.toRingHom ((a η)⁻¹)) :
            Matrix (Fin m) (Fin m) E) := by
      funext i
      exact γ.toRingEquiv.toRingHom.map_vecMul
        (↑((a η)⁻¹) : Matrix (Fin m) (Fin m) E) (fun j => η (v j)) i
    have hinv : GeneralLinearGroup.map γ.toRingEquiv.toRingHom ((a η)⁻¹) * (a γ)⁻¹ =
        (a (γ * η))⁻¹ := by
      rw [ha, _root_.mul_inv_rev, map_inv]
    change (fun i => γ (T η v i)) ᵥ* _ = (fun i => (γ * η) (v i)) ᵥ* _
    rw [hmap, Matrix.vecMul_vecMul, ← Units.val_mul, hinv]
  have ha_one : a (1 : Gal(E/k)) = 1 := by
    have h := ha 1 1
    change a (1 * 1) = a 1 * GeneralLinearGroup.map (RingHom.id E) (a 1) at h
    simpa using (mul_left_cancel (show a 1 * 1 = a 1 * a 1 by simpa using h)).symm
  have hT_one (v : Fin m → E) : T 1 v = v := by
    change v ᵥ* (↑((a 1)⁻¹) : Matrix (Fin m) (Fin m) E) = v
    rw [ha_one, inv_one, Units.val_one, Matrix.vecMul_one]
  have hT_smul (γ : Gal(E/k)) (x : E) (v : Fin m → E) :
      T γ (x • v) = γ x • T γ v := by
    change (fun i => γ (x * v i)) ᵥ* (↑((a γ)⁻¹) : Matrix (Fin m) (Fin m) E) = _
    simp only [map_mul]
    exact Matrix.smul_vecMul (γ x) (fun i => γ (v i))
      (↑((a γ)⁻¹) : Matrix (Fin m) (Fin m) E)
  let P (v : Fin m → E) : Fin m → E := ∑ γ : Gal(E/k), T γ v
  have hP_fixed (γ : Gal(E/k)) (v : Fin m → E) : T γ (P v) = P v := by
    simp only [P, map_sum, hT_mul]
    exact Equiv.sum_comp (Equiv.mulLeft γ) (fun η => T η v)
  -- A linear functional vanishing on the orbit sums vanishes on every row.
  have hspan : Submodule.span E (Set.range P) = ⊤ := by
    by_contra h
    obtain ⟨l, hl, hker⟩ := (Submodule.span E (Set.range P)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr h)
    have hz (v : Fin m → E) : l (P v) = 0 :=
      hker (Submodule.subset_span (Set.mem_range_self v))
    have hlin : LinearIndependent E (fun γ : Gal(E/k) => (γ : E → E)) :=
      D07.Ch14.IndependentEmbeddings.embeddings_linearIndependent E E Gal(E/k)
        (fun γ => γ.toRingEquiv.toRingHom)
        (fun σ τ h => AlgEquiv.ext fun x => DFunLike.congr_fun
          (show σ.toRingEquiv.toRingHom = τ.toRingEquiv.toRingHom from h) x)
    apply hl
    apply LinearMap.ext
    intro v
    change l v = 0
    have hrel : (∑ γ : Gal(E/k), l (T γ v) • (fun x => γ x)) = 0 := by
      funext x
      simpa only [P, map_sum, hT_smul, map_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, mul_comm] using hz (x • v)
    simpa only [hT_one] using (Fintype.linearIndependent_iff.mp hlin) _ hrel 1
  -- Select a basis from the orbit sums and put its vectors in the rows.
  obtain ⟨s, hsubset, hsp, hli⟩ := exists_linearIndependent E (Set.range P)
  let b : Basis s E (Fin m → E) := Basis.mk hli (by rw [Subtype.range_coe, hsp, hspan])
  let e := b.indexEquiv (Pi.basisFun E (Fin m))
  let rows := b.reindex e
  have hrows (i : Fin m) : rows i ∈ Set.range P := by
    rw [show rows i = (e.symm i : Fin m → E) by simp [rows, b]]
    exact hsubset (e.symm i).property
  let M : Matrix (Fin m) (Fin m) E := Matrix.of fun i => rows i
  obtain ⟨B, hB⟩ : IsUnit M := Matrix.linearIndependent_row_iff_isUnit.mp rows.linearIndependent
  refine ⟨B, fun γ => GeneralLinearGroup.ext fun i j => ?_⟩
  obtain ⟨v, hv⟩ := hrows i
  have hfixed : T γ (rows i) = rows i := by rw [← hv, hP_fixed]
  have hrow : (fun j => γ (rows i j)) = rows i ᵥ* (↑(a γ) : Matrix (Fin m) (Fin m) E) := by
    have hmul := congrArg (fun w => w ᵥ* (↑(a γ) : Matrix (Fin m) (Fin m) E)) hfixed
    change ((fun j => γ (rows i j)) ᵥ* (↑((a γ)⁻¹) : Matrix (Fin m) (Fin m) E)) ᵥ*
      (↑(a γ) : Matrix (Fin m) (Fin m) E) = _ at hmul
    simpa only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.vecMul_one] using hmul
  change γ ((↑B : Matrix (Fin m) (Fin m) E) i j) =
    ((↑B : Matrix (Fin m) (Fin m) E) * (↑(a γ) : Matrix (Fin m) (Fin m) E)) i j
  rw [hB]
  exact congrFun hrow j

end GaloisFormalization.PV
