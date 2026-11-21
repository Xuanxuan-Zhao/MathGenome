import MathGenome.Internal.Specs.D05.M14.Svd.PairedVectors
import MathGenome.Internal.D05.M12.Orthonormal
import MathGenome.Internal.D05.M03.Image

noncomputable section
namespace D05.M14.Svd.PairedVectors

universe u v w
variable {F : Type u} {V : Type v} {W : Type w} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

theorem image_inner : Specs.D05.M14.Svd.PairedVectors.image_inner := by
  intro F V W _ _ _ _ _ _ _ T n e s he i j
  classical
  change inner F (T (e j)) (T (e i)) = _
  rw [← LinearMap.adjoint_inner_left, he, inner_smul_left]
  simp [orthonormal_iff_ite.mp e.orthonormal, eq_comm]

theorem zero_image : Specs.D05.M14.Svd.PairedVectors.zero_image := by
  intro F V W _ _ _ _ _ _ _ T n e s he i hi
  apply (inner_self_eq_zero (𝕜 := F)).mp
  simpa [D05.firstInner, hi] using image_inner T e s he i i

theorem paired_orthonormal : Specs.D05.M14.Svd.PairedVectors.paired_orthonormal := by
  intro F V W _ _ _ _ _ _ _ T n e s he r hr hp
  classical
  apply (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr
  rw [orthonormal_iff_ite]
  intro i j
  have hij := image_inner T e s he (Fin.castLE hr j) (Fin.castLE hr i)
  change inner F (T (e (Fin.castLE hr i))) (T (e (Fin.castLE hr j))) = _ at hij
  simp only [inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_ofReal]
  rw [hij]
  by_cases h : i = j
  · subst j
    have hs : (s (Fin.castLE hr i) : F) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hp i))
    simp only [ite_true, mul_one, RCLike.ofReal_pow]
    field_simp
  · have hc : Fin.castLE hr j ≠ Fin.castLE hr i := by
      intro hc
      exact h (Fin.ext (congrArg Fin.val hc).symm)
    simp [h, hc]

/-- Nonzero rescaling transports independence back to the original images. -/
theorem image_independent : Specs.D05.M14.Svd.PairedVectors.image_independent := by
  intro F V W _ _ _ _ _ _ _ T n e s he r hr hp
  have hn := (D05.M12.Orthonormal.orthonormal_iff_mathlib _).mp
    (paired_orthonormal T e s he hr hp)
  have hs : ∀ i : Fin r, (s (Fin.castLE hr i) : F) ≠ 0 := by
    intro i
    exact_mod_cast (ne_of_gt (hp i))
  have h := hn.linearIndependent.units_smul
    (fun i => Units.mk0 (s (Fin.castLE hr i) : F) (hs i))
  simpa only [Pi.smul_def', Units.smul_def, Units.val_mk0, smul_smul, mul_inv_cancel₀ (hs _),
    one_smul] using h

/-- All domain basis images are in the span of the positive ones; the other
images vanish. Applying the image-of-span theorem proves spanning of range T. -/
theorem image_span : Specs.D05.M14.Svd.PairedVectors.image_span := by
  intro F V W _ _ _ _ _ _ _ T n e s he r hr hp hz
  let U := Submodule.span F (Set.range (fun i : Fin r => T (e (Fin.castLE hr i))))
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro y ⟨i, rfl⟩
      exact LinearMap.mem_range_self T _)
  · have hfull := D05.M03.Image.span_image_eq T (fun i => e i) e.toBasis.span_eq
    rw [← hfull]
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    by_cases hi : i.val < r
    · exact Submodule.subset_span ⟨⟨i.val, hi⟩, by rfl⟩
    · change T (e i) ∈ U
      rw [zero_image T e s he i (hz i (Nat.le_of_not_lt hi))]
      exact U.zero_mem

/-- The basis lives in the actual image subspace, with its inclusion into W
recorded explicitly. -/
theorem image_basis : Specs.D05.M14.Svd.PairedVectors.image_basis := by
  intro F V W _ _ _ _ _ _ _ T n e s he r hr hp hz
  let a : Fin r → LinearMap.range T :=
    fun i => ⟨T (e (Fin.castLE hr i)), LinearMap.mem_range_self T _⟩
  have hi : LinearIndependent F a := by
    apply LinearIndependent.of_comp (LinearMap.range T).subtype
    exact image_independent T e s he hr hp
  have hsp : Submodule.span F (Set.range a) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff (LinearMap.range T)
      (fun i => LinearMap.mem_range_self T (e (Fin.castLE hr i)))).mpr
      (image_span T e s he hr hp hz)
  refine ⟨Module.Basis.mk hi hsp.ge, ?_⟩
  intro i
  simp only [Module.Basis.coe_mk]
  rfl

theorem rank_eq : Specs.D05.M14.Svd.PairedVectors.rank_eq := by
  intro F V W _ _ _ _ _ _ _ T n e s he r hr hp hz
  obtain ⟨b, hb⟩ := image_basis T e s he hr hp hz
  simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm

theorem rank_bound : Specs.D05.M14.Svd.PairedVectors.rank_bound := by
  intro F V W _ _ _ _ _ _ _ T n e s he r hr hp hz
  rw [rank_eq T e s he hr hp hz]
  exact le_min T.finrank_range_le (Submodule.finrank_le _)

/-- In particular r = 0 forces the zero map. This basis argument also covers
an empty domain basis, without choosing any index from it. -/
theorem zero_rank : Specs.D05.M14.Svd.PairedVectors.zero_rank := by
  intro F V W _ _ _ _ _ _ _ T n e s he hz
  apply e.toBasis.ext
  intro i
  simpa only [LinearMap.zero_apply, OrthonormalBasis.coe_toBasis] using zero_image T e s he i (hz i)

end D05.M14.Svd.PairedVectors
