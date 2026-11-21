import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.CrossedProduct
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.IntegralBar
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.FreeGroupVanishing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open CategoryTheory Finsupp

universe u v

namespace ALG02GroupTheory.IntegralBar

noncomputable section

private theorem exists_cochain_of_normalized_cocycle
    {F : Type u} [Group F] [IsFreeGroup F] {A : Type v} [AddCommGroup A]
    (c : F → F → A) (hleft : ∀ g, c 1 g = 0) (hright : ∀ g, c g 1 = 0)
    (hc : ∀ g h k, c g h + c (g * h) k = c h k + c g (h * k)) :
    ∃ a : F → A, ∀ g h, c g h = a h - a (g * h) + a g := by
  let D : Extensions.FactorSystem (Multiplicative A) F :=
    { alpha := fun _ => 1
      factor := fun g h => Multiplicative.ofAdd (c g h)
      alpha_one := rfl
      factor_one_left := hleft
      factor_one_right := hright
      alpha_mul := by
        intro g h
        ext x
        simp [MulAut.conj_apply, mul_comm]
      factor_assoc := hc }
  -- Lift each free generator through the canonical section of the crossed product.
  let s : F →* Extensions.CrossedProduct D :=
    IsFreeGroup.lift (fun x => ⟨1, IsFreeGroup.of x⟩)
  have hs : (Extensions.crossedProductExtension D).rightHom.comp s = MonoidHom.id F := by
    apply IsFreeGroup.ext_hom
    intro x
    change (s (IsFreeGroup.of x)).right = IsFreeGroup.of x
    dsimp only [s]
    rw [IsFreeGroup.lift_of]
  have hs' (g : F) : (s g).right = g :=
    DFunLike.congr_fun hs g
  refine ⟨fun g => -(s g).left.toAdd, fun g h => ?_⟩
  have hmul := congrArg (fun z : Extensions.CrossedProduct D => z.left.toAdd) (map_mul s g h)
  change (s (g * h)).left.toAdd =
    (s g).left.toAdd + (s h).left.toAdd + c (s g).right (s h).right at hmul
  rw [hs', hs'] at hmul
  dsimp only
  rw [hmul]
  abel

private theorem secondBarExact (F : Type u) [Group F] [IsFreeGroup F] :
    (chains F).ExactAt 2 := by
  classical
  let B := LinearMap.range ((chains F).d 3 2).hom
  let q := B.mkQ
  let c : F → F → ((chains F).X 2 ⧸ B) := fun g h => q (bar 2 ![g, h])
  have hc (g h k : F) : c g h + c (g * h) k = c h k + c g (h * k) := by
    have hz : q ((chains F).d 3 2 (bar 3 ![g, h, k])) = 0 :=
      (Submodule.Quotient.mk_eq_zero B).mpr ⟨bar 3 ![g, h, k], rfl⟩
    rw [bar_d_three, map_sub, map_add, map_sub] at hz
    change c h k - c (g * h) k + c g (h * k) - c g h = 0 at hz
    calc
      c g h + c (g * h) k =
          c g h + c (g * h) k + (c h k - c (g * h) k + c g (h * k) - c g h) := by
            rw [hz, add_zero]
      _ = c h k + c g (h * k) := by abel
  -- The coboundary of the constant cochain with value c 1 1 normalizes c.
  let c₀ : F → F → ((chains F).X 2 ⧸ B) := fun g h => c g h - c 1 1
  have hleft (g : F) : c₀ 1 g = 0 := by
    have h : c 1 g = c 1 1 := by
      simpa only [one_mul, add_left_inj] using (hc 1 1 g).symm
    exact sub_eq_zero.mpr h
  have hright (g : F) : c₀ g 1 = 0 := by
    have h : c g 1 = c 1 1 := by
      simpa only [mul_one, add_left_inj] using hc g 1 1
    exact sub_eq_zero.mpr h
  have hc₀ (g h k : F) : c₀ g h + c₀ (g * h) k = c₀ h k + c₀ g (h * k) := by
    dsimp only [c₀]
    simpa only [sub_add_sub_comm] using
      congrArg (fun x => x - (c 1 1 + c 1 1)) (hc g h k)
  obtain ⟨a₀, ha₀⟩ := exists_cochain_of_normalized_cocycle c₀ hleft hright hc₀
  let a := fun g => a₀ g + c 1 1
  have ha (g h : F) : c g h = a h - a (g * h) + a g := by
    have h := congrArg (fun x => x + c 1 1) (ha₀ g h)
    dsimp only [c₀] at h
    rw [sub_add_cancel] at h
    dsimp only [a]
    rw [h]
    abel
  let L : (chains F).X 1 →ₗ[Integers.{u}] ((chains F).X 2 ⧸ B) :=
    Finsupp.linearCombination Integers.{u} (fun g : Fin 1 → F => a (g 0))
  have hL (g : F) : L (bar 1 ![g]) = a g := by
    change Finsupp.linearCombination Integers.{u} (fun g : Fin 1 → F => a (g 0))
      (Finsupp.single ![g] 1) = a g
    rw [Finsupp.linearCombination_single, one_smul]
    rfl
  -- On bar generators the coboundary formula is exactly the factorization of q through d₂.
  have hq : q = L.comp ((chains F).d 2 1).hom := by
    apply Finsupp.lhom_ext
    intro g r
    have hg : g = ![g 0, g 1] := by
      funext i
      fin_cases i <;> rfl
    have hsingle : Finsupp.single g r = r • bar 2 g := by
      exact (Finsupp.smul_single_one g r).symm
    rw [hsingle, map_smul, map_smul]
    congr 1
    rw [hg]
    change c (g 0) (g 1) = L ((chains F).d 2 1 (bar 2 ![g 0, g 1]))
    rw [bar_d_two, map_add, map_sub, hL, hL, hL, ha]
  apply ShortComplex.exact_of_iso
    ((chains F).isoSc' 3 2 1 (ChainComplex.prev ℕ _) (ChainComplex.next_nat_succ _)).symm
  apply ModuleCat.shortComplex_exact
  intro z
  change (chains F).d 2 1 z = 0 ↔ z ∈ Set.range ((chains F).d 3 2)
  constructor
  · intro hz
    have h : q z = 0 := by
      rw [hq]
      change L ((chains F).d 2 1 z) = 0
      rw [hz, map_zero]
    exact (Submodule.Quotient.mk_eq_zero B).mp h
  · rintro ⟨y, rfl⟩
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((chains F).d_comp_d 3 2 1)) y

/-- A free group has zero integral homology in degree two. -/
theorem freeGroup_h2_isZero (F : Type u) [Group F] [IsFreeGroup F] :
    Limits.IsZero (homology F 2) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (secondBarExact F)

end

end ALG02GroupTheory.IntegralBar
