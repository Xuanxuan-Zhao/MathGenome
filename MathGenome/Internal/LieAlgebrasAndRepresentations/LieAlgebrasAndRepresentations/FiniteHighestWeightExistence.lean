import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LongestElementRho
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClebschGordan
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebrasAndRepresentations.FiniteHighestWeightExistence

open Specs.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.HighestWeightData
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSpace_value rootSet_value)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Module LieModule
open scoped BigOperators DirectSum

universe u v

section RankOne

open Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F)
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The standard matrices act through the three elements of the given triple. -/
private theorem triple_map {h e f : L} (t : IsSl2Triple h e f) (K : LieSubalgebra ℂ L)
    (he : e ∈ K) (hf : f ∈ K) (hh : h ∈ K) :
    ∃ ι : Model ℂ →ₗ⁅ℂ⁆ K,
      ι (E ℂ) = ⟨e, he⟩ ∧ ι (F ℂ) = ⟨f, hf⟩ ∧
      ι (Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ) = ⟨h, hh⟩ := by
  obtain ⟨b, bE, bF, bH⟩ := sl2_basis ℂ
  change b 0 = E ℂ at bE
  change b 1 = F ℂ at bF
  change b 2 = Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ at bH
  let g : Model ℂ →ₗ[ℂ] K := b.constr ℂ ![⟨e, he⟩, ⟨f, hf⟩, ⟨h, hh⟩]
  have hgE : g (E ℂ) = ⟨e, he⟩ := by rw [← bE]; exact b.constr_basis ℂ _ 0
  have hgF : g (F ℂ) = ⟨f, hf⟩ := by rw [← bF]; exact b.constr_basis ℂ _ 1
  have hgH : g (Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ) = ⟨h, hh⟩ := by
    rw [← bH]; exact b.constr_basis ℂ _ 2
  refine ⟨{ g with map_lie' := ?_ }, hgE, hgF, hgH⟩
  let A : Model ℂ →ₗ[ℂ] Model ℂ →ₗ[ℂ] K :=
    (LinearMap.llcomp ℂ (Model ℂ) (Model ℂ) K g).comp (LieAlgebra.ad ℂ (Model ℂ)).toLinearMap
  let B : Model ℂ →ₗ[ℂ] Model ℂ →ₗ[ℂ] K :=
    ((LieAlgebra.ad ℂ K).toLinearMap.compl₂ g).comp g
  let h₀ := Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ
  let hK : K := ⟨h, hh⟩
  let eK : K := ⟨e, he⟩
  let fK : K := ⟨f, hf⟩
  have hEF : ⁅E ℂ, F ℂ⁆ = h₀ := (sl2_relations ℂ).2.2
  have hHE : ⁅h₀, E ℂ⁆ = (2 : ℂ) • E ℂ := (sl2_relations ℂ).1
  have hHF : ⁅h₀, F ℂ⁆ = (-2 : ℂ) • F ℂ := (sl2_relations ℂ).2.1
  have hEF' : ⁅eK, fK⁆ = hK := Subtype.ext t.lie_e_f
  have hHE' : ⁅hK, eK⁆ = (2 : ℂ) • eK := Subtype.ext (t.lie_h_e_smul ℂ)
  have hHF' : ⁅hK, fK⁆ = (-2 : ℂ) • fK :=
    Subtype.ext (by rw [neg_smul]; exact t.lie_lie_smul_f ℂ)
  have hFE : ⁅F ℂ, E ℂ⁆ = -h₀ := by rw [← lie_skew, hEF]
  have hEH : ⁅E ℂ, h₀⁆ = -((2 : ℂ) • E ℂ) := by rw [← lie_skew, hHE]
  have hFH : ⁅F ℂ, h₀⁆ = -((-2 : ℂ) • F ℂ) := by rw [← lie_skew, hHF]
  have hFE' : ⁅fK, eK⁆ = -hK := by rw [← lie_skew, hEF']
  have hEH' : ⁅eK, hK⁆ = -((2 : ℂ) • eK) := by rw [← lie_skew, hHE']
  have hFH' : ⁅fK, hK⁆ = -((-2 : ℂ) • fK) := by rw [← lie_skew, hHF']
  change g (E ℂ) = eK at hgE
  change g (F ℂ) = fK at hgF
  change g h₀ = hK at hgH
  have bE' : b ⟨0, by decide⟩ = E ℂ := bE
  have bF' : b ⟨1, by decide⟩ = F ℂ := bF
  have bH' : b ⟨2, by decide⟩ = h₀ := bH
  have hab : A = B := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change g ⁅b i, b j⁆ = ⁅g (b i), g (b j)⁆
    fin_cases i <;> fin_cases j <;>
      simp only [bE', bF', bH', lie_self, map_zero, hEF, hHE, hHF, hFE, hEH, hFH,
        map_neg, map_smul, hgE, hgF, hgH, hEF', hHE', hHF', hFE', hEH', hFH']
  intro x y
  exact congrArg (fun a : Model ℂ →ₗ[ℂ] Model ℂ →ₗ[ℂ] K => a x y) hab

section MatrixModule

local notation "S2" => Model ℂ
local notation "h₂" => Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ
local notation "f₂" => F ℂ

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule S2 V] [LieModule ℂ S2 V]

private theorem lower_basis {n : ℕ} {b : Basis (Fin (n + 1)) ℂ V} (hb : IsStandardBasis b)
    (j : Fin (n + 1)) (p : ℕ) (hp : j.val + p < n + 1) :
    (toEnd ℂ S2 V f₂ ^ p) (b j) = b ⟨j.val + p, hp⟩ := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, ih (by omega), toEnd_apply_apply]
    simpa [basisVector, hp, Nat.add_assoc] using (hb ⟨j.val + p, by omega⟩).2.1

private theorem lower_standard_injective {n : ℕ} {b : Basis (Fin (n + 1)) ℂ V}
    (hb : IsStandardBasis b) (m : ℕ) (x : V)
    (hx : ⁅h₂, x⁆ = (m : ℂ) • x) (hz : (toEnd ℂ S2 V f₂ ^ m) x = 0) : x = 0 := by
  classical
  by_contra hne
  have hcoord (i : Fin (n + 1)) :
      b.repr x i ≠ 0 → (n : ℂ) - 2 * (i.val : ℂ) = (m : ℂ) := by
    intro hi
    have hlin : (b.coord i).comp (toEnd ℂ S2 V h₂) =
        ((n : ℂ) - 2 * (i.val : ℂ)) • b.coord i := by
      apply b.ext
      intro j
      change b.repr (⁅h₂, b j⁆) i =
        ((n : ℂ) - 2 * (i.val : ℂ)) * b.repr (b j) i
      rw [(hb j).1, map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self]
      by_cases h : j = i
      · subst j
        rfl
      · rw [Finsupp.single_eq_of_ne (Ne.symm h)]; simp
    have h := DFunLike.congr_fun hlin x
    change b.repr (⁅h₂, x⁆) i = ((n : ℂ) - 2 * (i.val : ℂ)) * b.repr x i at h
    rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    exact (mul_right_cancel₀ hi h).symm
  have hex : ∃ i, b.repr x i ≠ 0 := by
    by_contra! h
    exact hne (b.repr.injective (by ext i; simpa using h i))
  obtain ⟨i, hi⟩ := hex
  have hii : (n : ℤ) - 2 * (i.val : ℤ) = (m : ℤ) := by
    exact_mod_cast hcoord i hi
  have hline : x = b.repr x i • b i := by
    apply b.repr.injective
    ext j
    rw [map_smul, Finsupp.smul_apply, b.repr_self]
    by_cases hij : j = i
    · subst j
      simp
    · have hj : b.repr x j = 0 := by
        by_contra hnj
        have hjj : (n : ℤ) - 2 * (j.val : ℤ) = (m : ℤ) := by
          exact_mod_cast hcoord j hnj
        exact hij (Fin.ext (by omega))
      rw [hj, Finsupp.single_eq_of_ne hij, smul_zero]
  rw [hline, map_smul, lower_basis hb i m (by omega)] at hz
  exact (smul_ne_zero hi (b.ne_zero _)) hz

/-- Every standard summand detects the kernel of the lowering power on the
nonnegative eigenspace. This is applied only to the finite rank-one submodules. -/
private theorem lower_finite_injective [FiniteDimensional ℂ V] (m : ℕ) (x : V)
    (hx : ⁅h₂, x⁆ = (m : ℂ) • x) (hz : (toEnd ℂ S2 V f₂ ^ m) x = 0) : x = 0 := by
  classical
  obtain ⟨A, _, hA, hb⟩ := ClebschGordan.finite_standard_decomposition ℂ V
  let B (i : A) := i.val.toSubmodule
  let equiv := LinearEquiv.ofBijective (DirectSum.coeLinearMap B) hA
  let p (i : A) : V →ₗ[ℂ] i.val :=
    (DirectSum.component ℂ A (fun j => B j) i).comp equiv.symm.toLinearMap
  have hproj (i : A) (a : S2) (y : V) : p i ⁅a, y⁆ = ⁅a, p i y⁆ := by
    suffices heq : ((p i).comp (toEnd ℂ S2 V a)).comp equiv.toLinearMap =
        ((toEnd ℂ S2 i.val a).comp (p i)).comp equiv.toLinearMap by
      have hh := DFunLike.congr_fun heq (equiv.symm y)
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        toEnd_apply_apply] using hh
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change p i ⁅a, DirectSum.coeLinearMap B (DirectSum.lof ℂ A (fun j => B j) j z)⁆ =
      ⁅a, p i (DirectSum.coeLinearMap B (DirectSum.lof ℂ A (fun j => B j) j z))⁆
    rw [DirectSum.coeLinearMap_lof]
    by_cases hij : j = i
    · subst j
      have hpz : p i (z : V) = z := hA.ofBijective_coeLinearMap_same z
      have hpaz : p i ((⁅a, z⁆ : i.val) : V) = (⁅a, z⁆ : i.val) :=
        hA.ofBijective_coeLinearMap_same (⁅a, z⁆ : i.val)
      rw [hpz]
      exact hpaz
    · have hpz : p i (z : V) = 0 := hA.ofBijective_coeLinearMap_of_ne hij z
      have hpaz : p i ((⁅a, z⁆ : j.val) : V) = 0 :=
        hA.ofBijective_coeLinearMap_of_ne hij (⁅a, z⁆ : j.val)
      rw [hpz, lie_zero]
      exact hpaz
  have hpPow (i : A) (p' : ℕ) : p i ((toEnd ℂ S2 V f₂ ^ p') x) =
      (toEnd ℂ S2 i.val f₂ ^ p') (p i x) := by
    induction p' with
    | zero => simp
    | succ p' ih =>
      simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply, hproj, ih]
  apply equiv.symm.injective
  rw [map_zero]
  apply DFinsupp.ext
  intro i
  change p i x = 0
  obtain ⟨n, b, hb⟩ := hb i i.property
  apply lower_standard_injective hb m
  · rw [← hproj, hx, map_smul]
  · rw [← hpPow, hz, map_zero]

end MatrixModule

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

private theorem lower_locally {h e f : L} (t : IsSl2Triple h e f) (K : LieSubalgebra ℂ L)
    (he : e ∈ K) (hf : f ∈ K) (hh : h ∈ K)
    (hlocal : ∀ x : V, ∃ S : LieSubmodule ℂ K V, x ∈ S ∧ FiniteDimensional ℂ S)
    (m : ℕ) (x : V) (hx : ⁅h, x⁆ = (m : ℂ) • x)
    (hz : (toEnd ℂ L V f ^ m) x = 0) : x = 0 := by
  obtain ⟨g, _, hgF, hgH⟩ := triple_map t K he hf hh
  obtain ⟨S, hxS, hfin⟩ := hlocal x
  letI := hfin
  letI := LieRingModule.compLieHom S g
  letI := LieModule.compLieHom S g
  let y : S := ⟨x, hxS⟩
  have hy : ⁅Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ, y⁆ = (m : ℂ) • y := by
    change ⁅g (Specs.LieAlgebrasAndRepresentations.Sl2Model.H ℂ), y⁆ = _
    rw [hgH]
    exact Subtype.ext hx
  have hp (k : ℕ) :
      ((toEnd ℂ (Model ℂ) S (F ℂ) ^ k) y : V) = (toEnd ℂ L V f ^ k) x := by
    induction k with
    | zero => simp [y]
    | succ k ih =>
      simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
      change ⁅((g (F ℂ) : K) : L), ((toEnd ℂ (Model ℂ) S (F ℂ) ^ k) y : V)⁆ = _
      rw [hgF, ih]
  have hy0 := lower_finite_injective m y hy (Subtype.ext ((hp m).trans hz))
  exact congrArg Subtype.val hy0

end RankOne

section Quotient

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)
  {lam : Module.Dual ℂ H} (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)
  (hd : IsDominant H φ lam) (f : simple H φ → L)

local instance : LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance : LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

local notation "M" => induced_value H φ χ
local notation "Q" => quotient_value H φ χ hd f
local notation "N" => relationSubmodule_value H φ χ hd f
local notation "W" => weightSpace_value Q H

private theorem quotient_weights (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (hχ : IsWeightCharacter H φ lam χ) :
    (∀ μ, FiniteDimensional ℂ (W μ)) ∧
      ∀ μ, W μ ≠ ⊥ → lam - μ ∈ positiveRootCone_value (fun i : simple H φ => i.val) := by
  letI : IsLieAbelian H := (RealRootSpace.cartan_isMaximalToral hss H).1.1
  have hV := VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ
  have hquot := WeightSubmodules.weight_submodules ((N).restr H) hV.1
  have hsurj (μ : Module.Dual ℂ H) :
      ∃ p : weightSpace_value M H μ →ₗ[ℂ] W μ, Function.Surjective p := by
    obtain ⟨g, _⟩ := hquot.2.2 μ
    exact ⟨g.toLinearMap.comp (((N).restr H).toSubmodule.comap
      (weightSpace_value M H μ).subtype).mkQ,
      g.surjective.comp (Submodule.mkQ_surjective _)⟩
  constructor
  · intro μ
    letI := hV.2.1 μ
    obtain ⟨p, hp⟩ := hsurj μ
    exact FiniteDimensional.of_surjective p hp
  · intro μ hμ
    apply (hV.2.2.1 μ).mp
    intro hb
    obtain ⟨p, hp⟩ := hsurj μ
    apply hμ
    apply bot_unique
    intro x hx
    obtain ⟨y, hy⟩ := hp ⟨x, hx⟩
    have h0 : y = 0 := Subtype.ext (by simpa [hb] using y.property)
    rw [h0, map_zero] at hy
    simpa using congrArg Subtype.val hy.symm

private theorem quotient_weights_integral (hss : IsSemisimple_value ℂ L)
    (hbelow : ∀ μ, W μ ≠ ⊥ →
      lam - μ ∈ positiveRootCone_value (fun i : simple H φ => i.val)) :
    ∀ μ, W μ ≠ ⊥ → μ ∈ integralWeights_value (coroots H φ) := by
  let P := integralWeights_value (coroots H φ)
  have hcone : (positiveRootCone_value (fun i : simple H φ => i.val)) ≤
      P.restrictScalars ℕ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩ j
    exact (RootStrings.coroot_pairing_integral hss H
      (RealRootSpace.cartan_isMaximalToral hss H)
      j.val i.val j.property.1.1 i.property.1.1).imp fun _ hz => hz.1
  have hlam : lam ∈ P := fun i => by
    obtain ⟨n, hn⟩ := hd i
    exact ⟨n, by simpa using hn⟩
  intro μ hμ
  have hh := P.sub_mem hlam (hcone (hbelow μ hμ))
  rwa [sub_sub_cancel] at hh

open private coroot_eval pow_shift from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient

private theorem simple_multiplicity (hss : IsSemisimple_value ℂ L)
    (e : simple H φ → L) (hef : Normalized H φ e f)
    (hlocal : ∀ i (x : Q), ∃ S : LieSubmodule ℂ (rankOne_value H φ e f i) Q,
      x ∈ S ∧ FiniteDimensional ℂ S)
    (hfin : ∀ μ, FiniteDimensional ℂ (W μ))
    (hint : ∀ μ, W μ ≠ ⊥ → μ ∈ integralWeights_value (coroots H φ))
    (i : simple H φ) (μ : Module.Dual ℂ H) :
    finrank ℂ (W (RootStrings.rootReflection H i.val μ)) = finrank ℂ (W μ) := by
  let r := RootStrings.rootReflection H i.val
  let h := coroots H φ i
  let α := i.val
  let K := rankOne_value H φ e f i
  have he : e i ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have hf : f i ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have hh : (h : L) ∈ K := LieSubalgebra.subset_lieSpan (by simp [h])
  have ht := IntegrableHighestWeightQuotient.isSl2Triple H φ hss hef i
  have hr (ν : Module.Dual ℂ H) : r ν = ν - ν h • α := rfl
  have hi : α h = 2 := coroot_eval H φ hss i
  have hrr (ν : Module.Dual ℂ H) : r (r ν) = ν := by
    have hre : r ν h = -(ν h) := by
      rw [hr, LinearMap.sub_apply, LinearMap.smul_apply, hi, smul_eq_mul]
      ring
    rw [hr (r ν), hre, hr ν]
    module
  have hle (ν : Module.Dual ℂ H) : finrank ℂ (W ν) ≤ finrank ℂ (W (r ν)) := by
    letI := hfin ν
    letI := hfin (r ν)
    by_cases hb : W ν = ⊥
    · rw [hb, finrank_bot]
      exact Nat.zero_le _
    obtain ⟨z, hz⟩ := hint ν hb i
    by_cases hpos : 0 ≤ z
    · lift z to ℕ using hpos with m
      have hz' : ν h = (m : ℂ) := by simpa [h] using hz
      let A := (toEnd ℂ L Q (f i) ^ m)
      have hmap {x : Q} (hx : x ∈ W ν) : A x ∈ W (r ν) := by
        rw [hr, hz']
        simpa only [α, sub_eq_add_neg, smul_neg, Nat.cast_smul_eq_nsmul] using
          pow_shift H (hef i).2.1 hx m
      let b := (A.comp (W ν).subtype).codRestrict (W (r ν)) (fun x => hmap x.property)
      refine LinearMap.finrank_le_finrank_of_injective (f := b) ((injective_iff_map_eq_zero b).2 ?_)
      intro x hx
      apply Subtype.ext
      exact lower_locally ht K he hf hh (hlocal i) m (x : Q)
        (by rw [← hz']; exact (HighestWeight.mem_weightSpace Q H ν x).mp x.property h)
        (congrArg Subtype.val hx)
    · let m := z.natAbs
      have hm : z = -(m : ℤ) := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hpos)
      have hz' : ν h = -(m : ℂ) := by rw [show ν h = (z : ℂ) from hz, hm]; simp
      let A := (toEnd ℂ L Q (e i) ^ m)
      have hmap {x : Q} (hx : x ∈ W ν) : A x ∈ W (r ν) := by
        rw [hr, hz', neg_smul, sub_neg_eq_add]
        simpa only [α, Nat.cast_smul_eq_nsmul] using pow_shift H (hef i).1 hx m
      let b := (A.comp (W ν).subtype).codRestrict (W (r ν)) (fun x => hmap x.property)
      refine LinearMap.finrank_le_finrank_of_injective (f := b) ((injective_iff_map_eq_zero b).2 ?_)
      intro x hx
      apply Subtype.ext
      exact lower_locally ht.symm K hf he (K.neg_mem hh) (hlocal i) m (x : Q)
        (by rw [neg_lie, (HighestWeight.mem_weightSpace Q H ν x).mp x.property h,
          hz', neg_smul, neg_neg])
        (congrArg Subtype.val hx)
  have hrev := hle (r μ)
  rw [hrr μ] at hrev
  exact le_antisymm hrev (hle μ)

end Quotient

section DominantWeights

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inner_corootRho_nonneg {R : Set E} (hR : IsRootSystem R) (v : E) {x : E}
    (hx : x ∈ closedSimpleChamber R v) : 0 ≤ inner ℝ x (corootRho R v) := by
  classical
  have hroot (a : E) (ha : a ∈ positiveRoots R v) : 0 ≤ inner ℝ x a := by
    refine AddSubmonoid.closure_induction (fun y hy => hx y hy) (by simp)
      (fun y z _ _ hy hz => by rw [inner_add_right]; exact add_nonneg hy hz)
      (positive_mem_closure_simple hR.toRootAxioms v ha)
  rw [corootRho, finsum_mem_eq_finite_toFinset_sum _ (positiveRoots_finite hR.toRootAxioms v),
    real_inner_smul_right, inner_sum]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro a ha
  rw [Set.Finite.mem_toFinset] at ha
  rw [coroot, real_inner_smul_right]
  exact mul_nonneg (div_nonneg (by norm_num) real_inner_self_nonneg) (hroot a ha)

/-- Pairing the difference with the half-sum of positive coroots bounds
each simple-root coefficient of the difference. -/
private theorem finite_dominant_below {R : Set E} (hR : IsRootSystem R)
    {v : E} [Fintype (simpleRoots R v)] (hv : RootRegular R v) (x : E) :
    {y | y ∈ closedSimpleChamber R v ∧
      ∃ n : simpleRoots R v → ℕ, x - y = ∑ i, n i • (i : E)}.Finite := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (inner ℝ x (corootRho R v))
  let S := {n : simpleRoots R v → ℕ | ∀ i, n i ≤ N}
  have hS : S.Finite := by
    apply (Set.Finite.pi (ι := simpleRoots R v) (fun _ => Set.finite_Iic N)).subset
    intro n hn
    exact fun i _ => hn i
  apply (hS.image fun n => x - ∑ i : simpleRoots R v, n i • (i : E)).subset
  rintro y ⟨hy, n, hn⟩
  have hsum : inner ℝ (x - y) (corootRho R v) = ∑ i, (n i : ℝ) := by
    rw [hn, sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left,
      simple_root_corootRho_pairing R hR v hv i i.property, mul_one]
  refine ⟨n, ?_, ?_⟩
  · intro i
    have hle : (n i : ℝ) ≤ ∑ j, (n j : ℝ) :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg (n j)) (Finset.mem_univ i)
    rw [← hsum, inner_sub_left] at hle
    have hn' := inner_corootRho_nonneg hR v hy
    exact_mod_cast (show (n i : ℝ) ≤ (N : ℝ) by linarith)
  · change x - (∑ i : simpleRoots R v, n i • (i : E)) = y
    rw [← hn, sub_sub_cancel]

end DominantWeights

section RealWeights

open Specs.LieAlgebrasAndRepresentations.RealRootSpace (E Realization realRoots rootRestriction)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    {H : LieSubalgebra ℂ L} (d : Realization H) (φ : Direction H)

variable [Fact (Realization H)]

local instance : NormedAddCommGroup (E H) := (Fact.out : Realization H).normedAddCommGroup
local instance : InnerProductSpace ℝ (E H) := (Fact.out : Realization H).innerProductSpace

omit [Fact (Realization H)] in
private theorem extension_injective : Function.Injective d.j := by
  intro x y hxy
  ext z
  have h (w : E H) : d.j w z = (w z : ℂ) := by simpa using d.extension_formula w z 0
  have hz := congrArg (fun a : Module.Dual ℂ H => a z) hxy
  rw [h, h] at hz
  exact Complex.ofReal_injective hz

private theorem direction_vector : ∃ v : E H, ∀ x, φ (d.j x) = inner ℝ v x := by
  let g := (φ.comp d.j).toContinuousLinearMap
  let v := (InnerProductSpace.toDual ℝ (E H)).symm g
  refine ⟨v, fun x => ?_⟩
  change g x = inner ℝ v x
  rw [← InnerProductSpace.toDual_apply_apply]
  exact (DFunLike.congr_fun ((InnerProductSpace.toDual ℝ (E H)).apply_symm_apply g) x).symm

private theorem simple_equiv {v : E H} (hv : ∀ x, φ (d.j x) = inner ℝ v x) :
    ∃ s : simple H φ ≃ simpleRoots (realRoots H) v, ∀ i, d.j (s i : E H) = i.val := by
  have hpos (a : E H) : a ∈ positiveRoots (realRoots H) v ↔
      d.j a ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ := by
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, hp⟩
      exact ⟨by simpa only [d.extension_root b hb] using hb, by rwa [hv]⟩
    · intro ha
      exact ⟨⟨d.j a, ha.1, extension_injective d (d.extension_root _ ha.1)⟩, by
        rw [← hv]; exact ha.2⟩
  have hs (a : E H) : a ∈ simpleRoots (realRoots H) v ↔ d.j a ∈ simple H φ := by
    constructor
    · intro ha
      refine ⟨(hpos a).mp ha.1, ?_⟩
      intro b hb c hc h
      let b' := rootRestriction H b
      let c' := rootRestriction H c
      have hb' : d.j b' = b := d.extension_root _ hb.1
      have hc' : d.j c' = c := d.extension_root _ hc.1
      exact ha.2 b' ((hpos b').mpr (hb' ▸ hb)) c' ((hpos c').mpr (hc' ▸ hc))
        (extension_injective d (by rwa [map_add, hb', hc']))
    · intro ha
      refine ⟨(hpos a).mpr ha.1, ?_⟩
      intro b hb c hc h
      exact ha.2 _ ((hpos b).mp hb) _ ((hpos c).mp hc) (by rw [h, map_add])
  let j (a : simpleRoots (realRoots H) v) : simple H φ := ⟨d.j a, (hs a).mp a.property⟩
  have hj : Function.Bijective j := by
    constructor
    · intro a b hab
      exact Subtype.ext (extension_injective d (congrArg Subtype.val hab))
    · intro a
      have h : d.j (rootRestriction H a.val) = a.val := d.extension_root a a.property.1.1
      have ha : d.j (rootRestriction H a.val) ∈ simple H φ := by rw [h]; exact a.property
      exact ⟨⟨rootRestriction H a.val, (hs _).mpr ha⟩, Subtype.ext h⟩
  let e := Equiv.ofBijective j hj
  exact ⟨e.symm, fun i => congrArg Subtype.val (e.apply_symm_apply i)⟩

private theorem reflection_extension {v : E H} {a : E H} (ha : a ∈ simpleRoots (realRoots H) v)
    (x : E H) :
    d.j (rootReflectionEquiv a x) = RootStrings.rootReflection H (d.j a) (d.j x) := by
  obtain ⟨b, hb, rfl⟩ := ha.1.1
  rw [rootReflectionEquiv_apply, rootReflection, map_sub, map_smul, d.extension_root b hb]
  have he := d.coroot_evaluation x b hb
  rw [inner_coroot, rootCartan] at he
  change _ = d.j x - d.j x (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H b) • b
  rw [he]
  rfl

private theorem vector_regular {v : E H} (hv : ∀ x, φ (d.j x) = inner ℝ v x)
    (hφ : Regular H φ) : RootRegular (realRoots H) v := by
  rintro a ⟨b, hb, rfl⟩
  rw [← hv, d.extension_root _ hb]
  exact hφ b hb

private theorem weyl_invariance {v : E H} (hv : RootRegular (realRoots H) v)
    (m : Module.Dual ℂ H → ℕ)
    (hs : ∀ i : simple H φ, ∀ μ, m (RootStrings.rootReflection H i.val μ) = m μ)
    (s : simple H φ ≃ simpleRoots (realRoots H) v)
    (hjs : ∀ i, d.j (s i : E H) = i.val)
    (w : rootWeylGroup (realRoots H)) (x : E H) :
    m (d.j (w.val x)) = m (d.j x) := by
  obtain ⟨l, hl⟩ := exists_weylWord d.root_system hv w
  rw [← hl]
  clear hl w
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [weylWordProduct_cons]
    change m (d.j (rootReflectionEquiv (a : E H) (weylWordProduct l x))) = _
    have hj : d.j (a : E H) = (s.symm a).val := by
      simpa only [Equiv.apply_symm_apply] using hjs (s.symm a)
    rw [reflection_extension d a.property, hj, hs]
    exact ih

open private cartan_lattice_comparison_of_realization from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData

private theorem finite_spectrum {lam : Module.Dual ℂ H}
    (hd : IsDominant H φ lam) {v : E H}
    (hv : RootRegular (realRoots H) v)
    (s : simple H φ ≃ simpleRoots (realRoots H) v)
    (hjs : ∀ i, d.j (s i : E H) = i.val)
    (T : Set (Module.Dual ℂ H))
    (hint : ∀ μ ∈ T, μ ∈ integralWeights_value (coroots H φ))
    (hbelow : ∀ μ ∈ T, lam - μ ∈ positiveRootCone_value (fun i : simple H φ => i.val))
    (hw : ∀ (w : rootWeylGroup (realRoots H)) (x : E H), d.j (w.val x) ∈ T ↔ d.j x ∈ T) :
    T.Finite := by
  classical
  letI : Finite (simpleRoots (realRoots H) v) :=
    (simpleRoots_finite d.root_system.toRootAxioms v).to_subtype
  letI : Fintype (simpleRoots (realRoots H) v) := Fintype.ofFinite _
  letI : Fintype (simple H φ) := Fintype.ofEquiv _ s.symm
  have hcomp := cartan_lattice_comparison_of_realization d v hv s
  dsimp only at hcomp
  simp only [hjs] at hcomp
  obtain ⟨_, _, _, _, _, _, hj, _, _, _, _, hreal, _⟩ := hcomp
  have hlam : lam ∈ integralWeights_value (coroots H φ) := by
    intro i
    obtain ⟨n, hn⟩ := hd i
    exact ⟨n, by simpa using hn⟩
  obtain ⟨x, _, hx, _⟩ := hreal lam hlam
  let D := {y | y ∈ closedSimpleChamber (realRoots H) v ∧
    ∃ n : simpleRoots (realRoots H) v → ℕ, x - y = ∑ i, n i • (i : E H)}
  have hD : D.Finite := finite_dominant_below d.root_system hv x
  letI := rootWeylGroup_finite d.root_system
  let G := rootWeylGroup (realRoots H)
  have hW : (Set.univ : Set G).Finite := Set.finite_univ
  apply ((hW.prod hD).image (fun p : G × E H => d.j (p.1.val p.2))).subset
  intro μ hμ
  obtain ⟨y, _, hy, _⟩ := hreal μ (hint μ hμ)
  obtain ⟨w, hwdom⟩ := exists_weyl_into_closedSimpleChamber d.root_system v y
  have hwy : d.j (w.val y) ∈ T := (hw w y).2 (hy ▸ hμ)
  obtain ⟨n, hn⟩ := (HighestWeight.mem_positiveRootCone_iff _ _).mp (hbelow _ hwy)
  have hsum : x - w.val y = ∑ i : simpleRoots (realRoots H) v, n (s.symm i) • (i : E H) := by
    apply hj
    rw [map_sub, hx, map_sum]
    simp only [map_nsmul]
    rw [← hn]
    apply Fintype.sum_equiv s
      (fun i : simple H φ => n i • (i.val : Module.Dual ℂ H))
      (fun i : simpleRoots (realRoots H) v => n (s.symm i) • d.j (i : E H))
    intro i
    rw [Equiv.symm_apply_apply, hjs]
  exact ⟨(w⁻¹, w.val y), ⟨Set.mem_univ _, hwdom, _, hsum⟩, by
    change d.j (w.val.symm (w.val y)) = μ
    rw [LinearEquiv.symm_apply_apply, hy]⟩

end RealWeights

private theorem finite_of_finite_weight_support {V I : Type*} [AddCommGroup V] [Module ℂ V]
    [DecidableEq I]
    (W : I → Submodule ℂ V) (hsum : DirectSum.IsInternal W)
    (hfin : ∀ i, FiniteDimensional ℂ (W i)) (hT : {i | W i ≠ ⊥}.Finite) :
    FiniteDimensional ℂ V := by
  classical
  let T := {i | W i ≠ ⊥}
  letI : Finite T := hT.to_subtype
  letI (i : T) : FiniteDimensional ℂ (W i) := hfin i
  have heq : (⨆ i : T, W i) = ⊤ := by
    apply top_unique
    rw [← hsum.submodule_iSup_eq_top]
    refine iSup_le (fun i => ?_)
    by_cases hi : W i = ⊥
    · rw [hi]
      exact bot_le
    · exact le_iSup (fun j : T => W j) ⟨i, hi⟩
  let g : V →ₗ[ℂ] (⨆ i : T, W i : Submodule ℂ V) :=
    LinearMap.codRestrict _ LinearMap.id (fun x => by simp [heq])
  exact FiniteDimensional.of_injective g (fun x y h => congrArg Subtype.val h)

theorem finite_highest_weight_existence : finite_highest_weight_existence_type.{u} := by
  classical
  intro L _ _ _ hss H _ φ hφ lam χ hχ hd e f hef
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let Q := quotient_value H φ χ hd f
  let W := weightSpace_value Q H
  let N := relationSubmodule_value H φ χ hd f
  let J := maximalSubmodule_value H φ χ
  obtain ⟨hv, _, hsum, _, hlocal⟩ :=
    IntegrableHighestWeightQuotient.quotient_integrable hss H φ hφ lam χ hχ hd e f hef
  obtain ⟨hfin, hbelow⟩ := quotient_weights H φ χ hd f hss hφ hχ
  have hint := quotient_weights_integral H φ χ hd f hss hbelow
  have hs := simple_multiplicity H φ χ hd f hss e hef hlocal hfin hint
  have hweyl (d : Specs.LieAlgebrasAndRepresentations.RealRootSpace.Realization H) :
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      ∀ (w : rootWeylGroup (Specs.LieAlgebrasAndRepresentations.RealRootSpace.realRoots H)) x,
        finrank ℂ (W (d.j (w.val x))) = finrank ℂ (W (d.j x)) := by
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    letI : Fact (Specs.LieAlgebrasAndRepresentations.RealRootSpace.Realization H) := ⟨d⟩
    obtain ⟨v, hv⟩ := direction_vector d φ
    obtain ⟨s, hjs⟩ := simple_equiv d φ hv
    exact weyl_invariance d φ (vector_regular d φ hv hφ) (fun μ => finrank ℂ (W μ)) hs s hjs
  have hQ : FiniteDimensional ℂ Q := by
    let d := RealRootSpace.realization hss H
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    letI : Fact (Specs.LieAlgebrasAndRepresentations.RealRootSpace.Realization H) := ⟨d⟩
    obtain ⟨v, hv⟩ := direction_vector d φ
    obtain ⟨s, hjs⟩ := simple_equiv d φ hv
    let T := {μ | W μ ≠ ⊥}
    have hT : T.Finite := by
      apply finite_spectrum d φ hd (vector_regular d φ hv hφ) s hjs T hint hbelow
      intro w x
      have hsupp (μ : Module.Dual ℂ H) : W μ ≠ ⊥ ↔ finrank ℂ (W μ) ≠ 0 := by
        letI : FiniteDimensional ℂ (W μ) := hfin μ
        exact not_congr (Submodule.finrank_eq_zero (S := W μ)).symm
      change W (d.j (w.val x)) ≠ ⊥ ↔ W (d.j x) ≠ ⊥
      rw [hsupp, hsupp, hweyl d w x]
    exact finite_of_finite_weight_support W hsum hfin hT
  have hNJ : N ≤ J := by
    have hN : N ≠ ⊤ := by
      intro ht
      apply hv
      apply (LieSubmodule.Quotient.mk_eq_zero N).mpr
      rw [ht]
      exact LieSubmodule.mem_top _
    exact (SimpleHighestWeightQuotient.maximal_submodule hss H φ hφ lam χ hχ).2 hN
  let p : Q →ₗ[ℂ] simpleQuotient_value H φ χ :=
    Submodule.factor (show N.toSubmodule ≤ J.toSubmodule from hNJ)
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J y
    exact ⟨LieSubmodule.Quotient.mk' N x, rfl⟩
  letI := hQ
  exact ⟨hQ, hint, hweyl, FiniteDimensional.of_surjective p hp⟩

end LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
