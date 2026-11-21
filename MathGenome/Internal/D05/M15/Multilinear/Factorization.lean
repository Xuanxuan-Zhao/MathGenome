import MathGenome.Internal.Specs.D05.M15.Multilinear.Factorization
import MathGenome.Internal.D05.M15.TensorUniversal
import MathGenome.Internal.D05.M03.FirstIso
import MathGenome.Internal.D05.M06.QuotientLift
import MathGenome.Internal.D05.M06.Complement
import MathGenome.Internal.D05.M02.BasisExtension.Choice
import MathGenome.Internal.D05.M11.Radicals
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
The correct factorization test (K05.15.multilinear, paper.tex:2708–2709).
Existence uses the first isomorphism theorem followed by extension from a
subspace. Mathlib's `LinearMap.exists_extend` uses unrestricted classical basis
extension, the choice principle explicitly declared in K05.02.basis_extension;
no dimension restriction or radical criterion is substituted for the kernel test.
-/
namespace D05.M15.Multilinear.Factorization

open scoped TensorProduct
open Specs.D05.M15.Multilinear.Factorization (Factors solutions vanishing exampleB exampleC)

section General
variable {K V W G H : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup G] [Module K G] [AddCommGroup H] [Module K H]

theorem linearization_composition :
    Specs.D05.M15.Multilinear.Factorization.linearization_composition := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c f
  constructor
  · intro h
    apply TensorProduct.ext'
    intro v w
    exact h v w
  · intro h v w
    exact LinearMap.congr_fun h (v ⊗ₜ[K] w)

theorem image_factorization :
    Specs.D05.M15.Multilinear.Factorization.image_factorization := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c h
  let B := TensorProduct.lift b
  let C := TensorProduct.lift c
  let f₀ := (B.ker.liftQ C h).comp B.quotKerEquivRange.symm.toLinearMap
  have hf₀ : ∀ t, f₀ (B.rangeRestrict t) = C t := by
    intro t
    change B.ker.liftQ C h (B.quotKerEquivRange.symm (B.rangeRestrict t)) = C t
    have heq : B.quotKerEquivRange.symm (B.rangeRestrict t) = B.ker.mkQ t :=
      B.quotKerEquivRange_symm_apply_image t _
    rw [heq]
    rfl
  refine ⟨f₀, hf₀, ?_⟩
  intro g hg
  ext y
  obtain ⟨t, ht⟩ := y.property
  have hy : B.rangeRestrict t = y := Subtype.ext ht
  rw [← hy, hg t, hf₀ t]

theorem factorization_iff_kernel :
    Specs.D05.M15.Multilinear.Factorization.factorization_iff_kernel := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c
  constructor
  · rintro ⟨f, hf⟩ t ht
    have heq := (linearization_composition b c f).mp hf
    change TensorProduct.lift c t = 0
    rw [← heq, LinearMap.comp_apply, LinearMap.mem_ker.mp ht, f.map_zero]
  · intro h
    obtain ⟨f₀, hf₀, _⟩ := image_factorization b c h
    obtain ⟨f, hf⟩ := f₀.exists_extend
    refine ⟨f, (linearization_composition b c f).mpr ?_⟩
    apply LinearMap.ext
    intro t
    calc
      f (TensorProduct.lift b t) =
          f₀ ((TensorProduct.lift b).rangeRestrict t) :=
        LinearMap.congr_fun hf ((TensorProduct.lift b).rangeRestrict t)
      _ = TensorProduct.lift c t := hf₀ t

/-- A homogeneous difference kills the entire tensor image, not only
individual values. This is the needed bridge to the quotient universal property. -/
theorem range_le_ker_iff (b : V →ₗ[K] W →ₗ[K] G) (d : G →ₗ[K] H) :
    LinearMap.range (TensorProduct.lift b) ≤ d.ker ↔ ∀ v w, d (b v w) = 0 := by
  constructor
  · intro h v w
    exact h ⟨v ⊗ₜ[K] w, rfl⟩
  · intro h y hy
    obtain ⟨t, rfl⟩ := hy
    have hz : d.comp (TensorProduct.lift b) = 0 := by
      apply TensorProduct.ext'
      intro v w
      exact h v w
    exact LinearMap.congr_fun hz t

/-- Pullback along a quotient map is injective because that quotient map is onto. -/
theorem quotient_pullback_injective (S : Submodule K G) :
    Function.Injective (fun d : (G ⧸ S) →ₗ[K] H => d.comp S.mkQ) := by
  intro d e h
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := S.mkQ_surjective q
  exact LinearMap.congr_fun h x

theorem difference_quotient :
    Specs.D05.M15.Multilinear.Factorization.difference_quotient := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c f₀ hf₀ f
  let S := LinearMap.range (TensorProduct.lift b)
  constructor
  · intro hf
    have hd : S ≤ (f - f₀).ker := (range_le_ker_iff b (f - f₀)).mpr (by
      intro v w
      change f (b v w) - f₀ (b v w) = 0
      rw [hf v w, hf₀ v w, sub_self])
    refine ⟨S.liftQ (f - f₀) hd, ?_, ?_⟩
    · change f = f₀ + (S.liftQ (f - f₀) hd).comp S.mkQ
      rw [S.liftQ_mkQ]
      abel
    · intro d hd'
      apply quotient_pullback_injective S
      change d.comp S.mkQ = (S.liftQ (f - f₀) hd).comp S.mkQ
      rw [S.liftQ_mkQ]
      exact eq_sub_iff_add_eq.mpr (by rw [add_comm, ← hd'])
  · rintro ⟨d, rfl, _⟩ v w
    change f₀ (b v w) + d (S.mkQ (b v w)) = c v w
    rw [hf₀ v w]
    have hq : S.mkQ (b v w) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr
      ⟨v ⊗ₜ[K] w, rfl⟩
    rw [hq, d.map_zero, add_zero]

theorem solution_direction :
    Specs.D05.M15.Multilinear.Factorization.solution_direction := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c f₀ hf₀
  ext d
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right (s := solutions b c) hf₀]
  constructor
  · rintro ⟨f, hf, rfl⟩ v w
    change f (b v w) - f₀ (b v w) = 0
    rw [hf v w, hf₀ v w, sub_self]
  · intro hd
    refine ⟨d + f₀, ?_, ?_⟩
    · intro v w
      change d (b v w) + f₀ (b v w) = c v w
      rw [hd v w, hf₀ v w, zero_add]
    · change d = d + f₀ - f₀
      rw [add_sub_cancel_right]

theorem quotient_model :
    Specs.D05.M15.Multilinear.Factorization.quotient_model := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b
  let S := LinearMap.range (TensorProduct.lift b)
  let L : ((G ⧸ S) →ₗ[K] H) →ₗ[K] vanishing (H := H) b :=
    { toFun := fun d => ⟨d.comp S.mkQ, by
        intro v w
        change d (S.mkQ (b v w)) = 0
        have hq : S.mkQ (b v w) = 0 :=
          (Submodule.Quotient.mk_eq_zero S).mpr ⟨v ⊗ₜ[K] w, rfl⟩
        rw [hq, d.map_zero]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective L := by
    intro d e h
    exact quotient_pullback_injective S (congrArg Subtype.val h)
  have hsurj : Function.Surjective L := by
    intro d
    have hd : S ≤ (d : G →ₗ[K] H).ker := (range_le_ker_iff b (d : G →ₗ[K] H)).mpr
      (show ∀ v w, (d : G →ₗ[K] H) (b v w) = 0 from d.property)
    refine ⟨S.liftQ (d : G →ₗ[K] H) hd, ?_⟩
    apply Subtype.ext
    exact S.liftQ_mkQ (d : G →ₗ[K] H) hd
  exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem affine_parametrization :
    Specs.D05.M15.Multilinear.Factorization.affine_parametrization := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c f₀ hf₀
  let S := LinearMap.range (TensorProduct.lift b)
  let F : ((G ⧸ S) →ₗ[K] H) → solutions b c := fun d =>
    ⟨f₀ + d.comp S.mkQ, (difference_quotient b c f₀ hf₀ _).mpr
      ⟨d, rfl, fun e he => quotient_pullback_injective S (add_left_cancel he.symm)⟩⟩
  have hinj : Function.Injective F := by
    intro d e h
    exact quotient_pullback_injective S (add_left_cancel (congrArg Subtype.val h))
  have hsurj : Function.Surjective F := by
    intro f
    obtain ⟨d, hd, _⟩ := (difference_quotient b c f₀ hf₀ f).mp f.property
    exact ⟨d, Subtype.ext hd.symm⟩
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun _ => rfl, ?_⟩
  intro d e
  change f₀ + (d + e).comp S.mkQ = (f₀ + d.comp S.mkQ) + e.comp S.mkQ
  rw [LinearMap.add_comp, add_assoc]

theorem affine_equivalence :
    Specs.D05.M15.Multilinear.Factorization.affine_equivalence := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c f₀ hf₀
  let : Nonempty (solutions b c) := ⟨⟨f₀, hf₀⟩⟩
  obtain ⟨E, hE, _⟩ := affine_parametrization b c f₀ hf₀
  obtain ⟨L, hL⟩ := quotient_model (H := H) b
  let A := L.trans (LinearEquiv.ofEq _ _ (solution_direction b c f₀ hf₀).symm)
  have hA : ∀ d, (A d : G →ₗ[K] H) =
      d.comp (LinearMap.range (TensorProduct.lift b)).mkQ := hL
  let F : ((G ⧸ LinearMap.range (TensorProduct.lift b)) →ₗ[K] H) ≃ᵃ[K]
      solutions b c :=
    { toEquiv := E
      linear := A
      map_vadd' := by
        intro d e
        apply Subtype.ext
        change (E (e + d) : G →ₗ[K] H) = (A e : G →ₗ[K] H) + (E d : G →ₗ[K] H)
        rw [hE, hA, hE, LinearMap.add_comp]
        abel }
  exact ⟨F, hE, hA⟩

theorem uniqueness_iff_model_zero :
    Specs.D05.M15.Multilinear.Factorization.uniqueness_iff_model_zero := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c f₀ hf₀
  obtain ⟨E, hE, _⟩ := affine_parametrization b c f₀ hf₀
  constructor
  · intro h d
    apply E.injective
    apply Subtype.ext
    exact (h (E d) (E d).property).trans (by simpa using (hE 0).symm)
  · intro h f hf
    have hex := E.surjective ⟨f, hf⟩
    obtain ⟨d, hd⟩ := hex
    have hv := congrArg Subtype.val hd
    rw [h d] at hv
    simpa [hE 0] using hv.symm

theorem unique_factorization_iff :
    Specs.D05.M15.Multilinear.Factorization.unique_factorization_iff := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c
  constructor
  · rintro ⟨f₀, hf₀, huniq⟩
    exact ⟨(factorization_iff_kernel b c).mp ⟨f₀, hf₀⟩,
      (uniqueness_iff_model_zero b c f₀ hf₀).mp huniq⟩
  · rintro ⟨hker, hmodel⟩
    obtain ⟨f₀, hf₀⟩ := (factorization_iff_kernel b c).mpr hker
    exact ⟨f₀, hf₀, (uniqueness_iff_model_zero b c f₀ hf₀).mpr hmodel⟩

theorem zero_solution_iff :
    Specs.D05.M15.Multilinear.Factorization.zero_solution_iff := by
  intro K V W G H _ _ _ _ _ _ _ _ _
  intro b c
  constructor
  · intro h
    ext v w
    exact (h v w).symm
  · rintro rfl
    intro v w
    rfl
end General

theorem example_evaluation : Specs.D05.M15.Multilinear.Factorization.example_evaluation := by
  intro x y
  constructor
  · simp [exampleB, Matrix.toBilin'_apply, Fin.sum_univ_two]
  · simp [exampleC, Matrix.toBilin'_apply, Fin.sum_univ_two]
    ring

private theorem diagonal_radicals (B : LinearMap.BilinForm ℝ (Fin 2 → ℝ))
    (a : ℝ) (ha : a ≠ 0)
    (hB : ∀ x y, B x y = x 0 * y 0 + a * (x 1 * y 1)) :
    Specs.D05.M11.Radicals.leftRadical_value B = ⊥ ∧
      Specs.D05.M11.Radicals.rightRadical_value B = ⊥ := by
  have hs : B.IsSymm := by
    constructor
    intro x y
    rw [hB x y, hB y x]
    ring
  have hl : Specs.D05.M11.Radicals.leftRadical_value B = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' := (D05.M11.Radicals.mem_leftRadical B x).mp hx
    have h₀ := hx' (Pi.single (0 : Fin 2) (1 : ℝ))
    have h₁ := hx' (Pi.single (1 : Fin 2) (1 : ℝ))
    rw [hB] at h₀ h₁
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one, mul_zero, zero_add,
      add_zero] at h₀ h₁
    have hx₁ : x 1 = 0 := (mul_eq_zero.mp h₁).resolve_left ha
    change x = 0
    funext i
    fin_cases i <;> assumption
  exact ⟨hl, (D05.M11.Radicals.radicals_eq_of_symmetric B hs).symm.trans hl⟩

theorem radical_counterexample : Specs.D05.M15.Multilinear.Factorization.radical_counterexample := by
  have hb := diagonal_radicals exampleB 1 one_ne_zero (by
    intro x y
    simpa using (example_evaluation x y).1)
  have hc := diagonal_radicals exampleC 2 (by norm_num) (fun x y => (example_evaluation x y).2)
  refine ⟨hb.1, hb.2, hc.1, hc.2, ?_⟩
  rintro ⟨f, hf⟩
  have h₀ := hf (Pi.single (0 : Fin 2) (1 : ℝ)) (Pi.single (0 : Fin 2) (1 : ℝ))
  have h₁ := hf (Pi.single (1 : Fin 2) (1 : ℝ)) (Pi.single (1 : Fin 2) (1 : ℝ))
  rw [(example_evaluation _ _).1, (example_evaluation _ _).2] at h₀ h₁
  norm_num [Pi.single_apply] at h₀ h₁
  exact (by norm_num : (1 : ℝ) ≠ 2) (h₀.symm.trans h₁)

end D05.M15.Multilinear.Factorization
