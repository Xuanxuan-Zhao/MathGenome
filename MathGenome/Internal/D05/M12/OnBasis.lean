import MathGenome.Internal.Specs.D05.M12.OnBasis
import MathGenome.Internal.D05.M02.BasisExtension
import MathGenome.Internal.D05.M12.GramSchmidt

/-! K05.12.on_basis: existence and extension, including the empty basis. -/

noncomputable section

namespace D05.M12.OnBasis

theorem exists_orthonormal_basis : Specs.D05.M12.OnBasis.exists_orthonormal_basis := by
  intro F V _ _ _ _
  let b := stdOrthonormalBasis F V
  exact ⟨b.toBasis,
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal⟩

/-- Fill the unprescribed positions by zero only to invoke Mathlib's partial
family extension theorem. Orthonormality is required solely on the prescribed
initial segment; the resulting full basis has no such zero entries. -/
theorem extend_orthonormal_list : Specs.D05.M12.OnBasis.extend_orthonormal_list := by
  intro F V _ _ _ _ m e he
  classical
  have ho : Orthonormal F e :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib e).mp he
  have hm : m ≤ Module.finrank F V := by
    simpa using ho.linearIndependent.fintype_card_le_finrank
  let s : Set (Fin (Module.finrank F V)) := {j | j.val < m}
  let v : Fin (Module.finrank F V) → V :=
    fun j => if hj : j.val < m then e ⟨j.val, hj⟩ else 0
  let f : s → Fin m := fun j => ⟨j.val.val, j.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun a : Fin m => a.val) hij
  have hs : Orthonormal F (s.domRestrict v) := by
    convert ho.comp f hf using 1
    funext j
    have hj : j.val.val < m := j.property
    simp [Set.domRestrict, v, f, hj]
  obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨hm, b.toBasis,
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal, ?_⟩
  intro i
  have hi : Fin.castLE hm i ∈ s := i.isLt
  simpa [v, Fin.castLE, i.isLt] using hb (Fin.castLE hm i) hi

theorem empty_basis : Specs.D05.M12.OnBasis.empty_basis := by
  intro F V _ _ _ _ h
  let b := (stdOrthonormalBasis F V).reindex (finCongr h)
  exact ⟨b.toBasis,
    (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr b.orthonormal⟩

end D05.M12.OnBasis
