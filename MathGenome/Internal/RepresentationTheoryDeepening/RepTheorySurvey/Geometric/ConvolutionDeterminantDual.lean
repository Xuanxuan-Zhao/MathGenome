import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionDeterminantDual
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace RepTheorySurvey.Geometric.ConvolutionDeterminantDual

open ConvolutionDeterminantDualSpecs

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The coordinate determinant, linear in the second vector and then in the first. -/
private def determinant (c : M ≃ₗ[R] (Fin 2 → R)) : M →ₗ[R] Module.Dual R M where
  toFun y :=
    c y 1 • ((LinearMap.proj 0).comp c.toLinearMap) -
      c y 0 • ((LinearMap.proj 1).comp c.toLinearMap)
  map_add' y z := by
    apply LinearMap.ext
    intro x
    simp [mul_comm]
    ring
  map_smul' a y := by
    apply LinearMap.ext
    intro x
    simp [mul_comm]
    ring

private theorem determinant_apply (c : M ≃ₗ[R] (Fin 2 → R)) (x y : M) :
    determinant c y x = c x 0 * c y 1 - c x 1 * c y 0 := by
  change c y 1 * c x 0 - c y 0 * c x 1 = _
  ring

private theorem determinant_bijective (c : M ≃ₗ[R] (Fin 2 → R)) :
    Function.Bijective (determinant c) := by
  let b := (Pi.basisFun R (Fin 2)).map c.symm
  have hcoord (i j : Fin 2) : c (b i) j = if i = j then 1 else 0 := by
    simp [b, Pi.single_apply, eq_comm]
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    have h : determinant c y = 0 := hy
    have h0 := congrArg (fun f : Module.Dual R M => f (b 0)) h
    have h1 := congrArg (fun f : Module.Dual R M => f (b 1)) h
    simp [determinant_apply, hcoord] at h0 h1
    apply c.injective
    ext i
    fin_cases i
    · simpa using h1
    · simpa using h0
  · intro f
    refine ⟨c.symm ![-f (b 1), f (b 0)], ?_⟩
    apply b.ext
    intro i
    fin_cases i <;> simp [determinant_apply, hcoord]

/-- The determinant of two linear forms on a locally free line vanishes. -/
private theorem forms_det_eq_zero [Module.Finite R M] [Module.Flat R M]
    (hrank : ∀ p, Module.rankAtStalk (R := R) M p = 1)
    (f g : Module.Dual R M) (x y : M) :
    f x * g y - g x * f y = 0 := by
  apply (PrimeSpectrum.toPiLocalization_injective R)
  rw [map_zero]
  funext p
  let P := p.asIdeal.primeCompl
  let A := Localization.AtPrime p.asIdeal
  let loc := LocalizedModule.mkLinearMap P M
  let fA := IsLocalizedModule.mapExtendScalars P loc (Algebra.linearMap R A) A f
  let gA := IsLocalizedModule.mapExtendScalars P loc (Algebra.linearMap R A) A g
  have hloc (h : Module.Dual R M) (z : M) :
      IsLocalizedModule.mapExtendScalars P loc (Algebra.linearMap R A) A h (loc z) =
        algebraMap R A (h z) := by
    exact IsLocalizedModule.map_apply P loc (Algebra.linearMap R A) h z
  let : Module.Free A (LocalizedModule P M) := Module.free_of_flat_of_isLocalRing
  have hdim : Module.finrank A (LocalizedModule P M) = 1 := hrank p
  obtain ⟨v, _, hv⟩ := finrank_eq_one_iff'.mp hdim
  change algebraMap R A (f x * g y - g x * f y) = 0
  simp only [map_sub, map_mul, ← hloc]
  change fA (loc x) * gA (loc y) - gA (loc x) * fA (loc y) = 0
  obtain ⟨a, ha⟩ := hv (loc x)
  obtain ⟨b, hb⟩ := hv (loc y)
  rw [← ha, ← hb]
  simp only [map_smul, smul_eq_mul]
  ring

theorem determinantDual : DeterminantDual.{u, v} := by
  intro R _ M _ _ c L S
  let Q := M ⧸ S
  obtain ⟨s, hs⟩ := S.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr S.mkQ_surjective)
  have hsection (q : Q) : S.mkQ (s q) = q := DFunLike.congr_fun hs q
  let r : M →ₗ[R] S :=
    (LinearMap.id - s.comp S.mkQ).codRestrict S (fun y => by
      rw [← Submodule.Quotient.mk_eq_zero]
      change S.mkQ (y - s (S.mkQ y)) = 0
      rw [map_sub, hsection, sub_self])
  have hr (y : M) : (r y : M) = y - s (S.mkQ y) := rfl
  have hretract (x : S) : r x.val = x := by
    apply Subtype.ext
    rw [hr, show S.mkQ x.val = 0 from (Submodule.Quotient.mk_eq_zero (p := S)).mpr x.property,
      map_zero, sub_zero]
  have hdecomp (y : M) : (r y : M) + s (S.mkQ y) = y := by
    rw [hr, sub_add_cancel]
  let split : M ≃ₗ[R] S × Q :=
    LinearEquiv.ofLinearMap (r.prod S.mkQ) (S.subtype.coprod s)
      (by
        apply LinearMap.ext
        rintro ⟨x, q⟩
        have hx : S.mkQ x.val = 0 := (Submodule.Quotient.mk_eq_zero (p := S)).mpr x.property
        have hrq : r (s q) = 0 := by
          apply Subtype.ext
          change (r (s q) : M) = 0
          rw [hr, hsection, sub_self]
        change (r (x.val + s q), S.mkQ (x.val + s q)) = (x, q)
        rw [map_add, map_add, hretract, hrq, hx, hsection, add_zero, zero_add])
      (LinearMap.ext hdecomp)
  let : Module.Free R M := Module.Free.of_equiv c.symm
  let : Module.Finite R M := Module.Finite.of_surjective c.symm.toLinearMap c.symm.surjective
  let : Module.Projective R S :=
    Module.Projective.of_split S.subtype r (LinearMap.ext hretract)
  let : Module.Finite R S := Module.Finite.of_surjective r (fun x => ⟨x.val, hretract x⟩)
  have hQ (p : PrimeSpectrum R) : Module.rankAtStalk (R := R) Q p = 1 :=
    L.rankAtStalk_eq p
  have hS (p : PrimeSpectrum R) : Module.rankAtStalk (R := R) S p = 1 := by
    have : Nontrivial R := p.nontrivial
    have hM : Module.rankAtStalk (R := R) M p = 2 := by
      rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, c.finrank_eq,
        Module.finrank_pi, Fintype.card_fin]
      rfl
    have h := congrFun (Module.rankAtStalk_eq_of_equiv split) p
    rw [Module.rankAtStalk_prod, Pi.add_apply, hQ, hM] at h
    omega
  let coord (i : Fin 2) : M →ₗ[R] R := (LinearMap.proj i).comp c.toLinearMap
  have hSS (x y : S) : determinant c y.val x.val = 0 := by
    rw [determinant_apply]
    exact forms_det_eq_zero hS ((coord 0).comp S.subtype) ((coord 1).comp S.subtype) x y
  have hQQ (x y : Q) : determinant c (s y) (s x) = 0 := by
    rw [determinant_apply]
    exact forms_det_eq_zero hQ ((coord 0).comp s) ((coord 1).comp s) x y
  let pair : M →ₗ[R] Module.Dual R S := (S.subtype.dualMap).comp (determinant c)
  have hpair (y : M) (x : S) : pair y x = determinant c y x.val := rfl
  have hker : S = LinearMap.ker pair := by
    ext y
    rw [LinearMap.mem_ker]
    constructor
    · intro hy
      exact LinearMap.ext (fun x => hSS x ⟨y, hy⟩)
    · intro hy
      have hzero : determinant c (s (S.mkQ y)) = 0 := by
        apply LinearMap.ext
        intro z
        change determinant c (s (S.mkQ y)) z = 0
        conv_lhs => rw [← hdecomp z]
        rw [map_add, hQQ, add_zero]
        have h := DFunLike.congr_fun hy (r z)
        rw [hpair] at h
        conv at h => lhs; rw [← hdecomp y]
        simpa [hSS] using h
      have hz : s (S.mkQ y) = 0 :=
        (determinant_bijective c).injective (hzero.trans (map_zero _).symm)
      have hqy : S.mkQ y = 0 := by
        rw [← hsection (S.mkQ y), hz, map_zero]
      exact (Submodule.Quotient.mk_eq_zero (p := S)).mp hqy
  have hsurj : Function.Surjective pair := by
    intro f
    obtain ⟨y, hy⟩ := (determinant_bijective c).surjective (f.comp r)
    refine ⟨y, LinearMap.ext (fun x => ?_)⟩
    rw [hpair, hy, LinearMap.comp_apply, hretract]
  let f := S.liftQ pair hker.le
  have hbij : Function.Bijective f := by
    constructor
    · exact LinearMap.ker_eq_bot.mp (S.ker_liftQ_eq_bot' pair hker)
    · intro g
      obtain ⟨y, rfl⟩ := hsurj g
      exact ⟨S.mkQ y, rfl⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun x y => determinant_apply c x.val y⟩

end RepTheorySurvey.Geometric.ConvolutionDeterminantDual
