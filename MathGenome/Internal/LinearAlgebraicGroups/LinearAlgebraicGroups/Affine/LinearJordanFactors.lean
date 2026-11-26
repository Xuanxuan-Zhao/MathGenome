import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LinearJordanFactors
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.TensorProduct.Maps

open Algebra Module Polynomial
open scoped TensorProduct

namespace LinearAlgebraicGroups.Affine

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

private theorem additive_of_multiplicative {f s u : End k V}
    (h : IsMultiplicativeJordanDecomposition f s u) :
    IsNilpotent (s * (u - 1)) ∧ Commute (s * (u - 1)) s ∧
      f = s * (u - 1) + s := by
  obtain ⟨hprod, hcomm, _, hnil, _, _⟩ := h
  have hc : Commute s (u - 1) := hcomm.sub_right (Commute.one_right s)
  exact ⟨hc.isNilpotent_mul_left hnil, (Commute.refl s).mul_left hc.symm,
    by rw [hprod, mul_sub, mul_one, sub_add_cancel]⟩

private theorem multiplicative_factors_eq [PerfectField k] [FiniteDimensional k V]
    {f s u t v : End k V} (h : IsMultiplicativeJordanDecomposition f s u)
    (h' : IsMultiplicativeJordanDecomposition f t v) : s = t ∧ u = v := by
  obtain ⟨hn, hc, he⟩ := additive_of_multiplicative h
  obtain ⟨hn', hc', he'⟩ := additive_of_multiplicative h'
  have hst := (End.isNilpotent_isSemisimple_unique hn h.semisimple hn' h'.semisimple
    hc hc' (he.symm.trans he')).2
  exact ⟨hst, h.isUnit_semisimple.mul_right_inj.mp (h.eq_mul.symm.trans (hst ▸ h'.eq_mul))⟩

/-- An invertible linear map has unique commuting semisimple and unipotent factors. -/
theorem multiplicativeJordanDecomposition : JordanFactorsSpec.existenceAndUniqueness := by
  intro k V _ _ _ _ _ f hf
  obtain ⟨n, hnmem, s, hsmem, hn, hs, he⟩ := f.exists_isNilpotent_isSemisimple
  have hc : Commute s n :=
    commute_of_mem_adjoin_singleton_of_commute hnmem
      (commute_of_mem_adjoin_self hsmem).symm
  have hnf : Commute n f := (commute_of_mem_adjoin_self hnmem).symm
  have hunit : IsUnit s := by
    have h := hn.neg.isUnit_add_right_of_commute hf hnf.neg_left
    rwa [he, ← add_assoc, neg_add_cancel, zero_add] at h
  obtain ⟨a, rfl⟩ := hunit
  let u := (↑a⁻¹ : End k V) * f
  have hsub : u - 1 = ↑a⁻¹ * n := by
    dsimp [u]
    rw [he, mul_add, Units.inv_mul, add_sub_cancel_right]
  have hu : IsNilpotent (u - 1) :=
    hsub ▸ hc.units_inv_left.isNilpotent_mul_left hn
  have hcomm : Commute (↑a : End k V) u :=
    (Commute.refl (↑a : End k V)).units_inv_right.mul_right
      (commute_of_mem_adjoin_self hsmem).symm
  have hdec : IsMultiplicativeJordanDecomposition f a u :=
    ⟨by simp [u, ← mul_assoc], hcomm, hs, hu, a.isUnit, a⁻¹.isUnit.mul hf⟩
  refine ⟨(↑a, u), hdec, ?_⟩
  rintro ⟨t, v⟩ ht
  obtain ⟨hst, huv⟩ := multiplicative_factors_eq ht hdec
  exact Prod.ext hst huv

private theorem isSemisimple_baseChange [PerfectField k] [FiniteDimensional k V]
    {K : Type*} [Field K] [Algebra k K] {f : End k V} (hf : f.IsSemisimple) :
    End.IsSemisimple (f.baseChange K) := by
  apply End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (minpoly k f).map (algebraMap k K))
  · exact (PerfectField.separable_iff_squarefree.mpr hf.minpoly_squarefree).map.squarefree
  · rw [aeval_map_algebraMap K]
    change aeval (End.baseChangeHom k K V f) (minpoly k f) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]

private theorem additive_intertwining_over_algClosed [IsAlgClosed k] [FiniteDimensional k V]
    {f s : End k V} {g t : End k W} (h : V →ₗ[k] W)
    (hs : s.IsSemisimple) (ht : t.IsSemisimple) (hfs : Commute f s) (hgt : Commute g t)
    (hfn : IsNilpotent (f - s)) (hgn : IsNilpotent (g - t))
    (hh : h.comp f = g.comp h) : h.comp s = t.comp h := by
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← End.iSup_maxGenEigenspace_eq_top f]
  refine iSup_le fun c x hx => ?_
  have hy := End.mapsTo_genEigenspace_of_comp h hh.symm c ⊤ hx
  have hxs := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
    hx hfs hs.isFinitelySemisimple hfn
  have hyt := End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
    hy hgt ht.isFinitelySemisimple hgn
  simp [LinearMap.mem_ker, hxs, hyt]

/-- Every linear intertwiner respects both factors. -/
theorem multiplicativeJordanIntertwining : JordanFactorsSpec.intertwining := by
  intro k V W _ _ _ _ _ _ _ _ f s u g t v h hf hg hh
  obtain ⟨hn, hc, he⟩ := additive_of_multiplicative hf
  obtain ⟨hm, hc', he'⟩ := additive_of_multiplicative hg
  have hfs : Commute f s := he ▸ hc.add_left (Commute.refl s)
  have hgt : Commute g t := he' ▸ hc'.add_left (Commute.refl t)
  have hfn : IsNilpotent (f - s) := by rwa [he, add_sub_cancel_right]
  have hgn : IsNilpotent (g - t) := by rwa [he', add_sub_cancel_right]
  let K := AlgebraicClosure k
  let φ := End.baseChangeHom k K V
  let ψ := End.baseChangeHom k K W
  have hhh : (h.baseChange K).comp (φ f) = (ψ g).comp (h.baseChange K) := by
    change (h.baseChange K).comp (f.baseChange K) = (g.baseChange K).comp (h.baseChange K)
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange K) hh
  have hs' := additive_intertwining_over_algClosed
    (s := φ s) (t := ψ t) (h.baseChange K)
    (isSemisimple_baseChange hf.semisimple) (isSemisimple_baseChange hg.semisimple)
    (hfs.map φ) (hgt.map ψ)
    (by simpa only [map_sub] using hfn.map φ)
    (by simpa only [map_sub] using hgn.map ψ) hhh
  have hs : h.comp s = t.comp h := by
    apply LinearMap.baseChangeHom_injective k V (N := W) K
    change (h.comp s).baseChange K = (t.comp h).baseChange K
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    exact hs'
  have hmultiplicative : t.comp (h.comp u) = t.comp (v.comp h) := by
    rw [← LinearMap.comp_assoc, ← hs, LinearMap.comp_assoc]
    simpa only [hf.eq_mul, hg.eq_mul, End.mul_eq_comp, LinearMap.comp_assoc] using hh
  refine ⟨hs, LinearMap.ext fun x => ?_⟩
  have ht := ((End.isUnit_iff t).mp hg.isUnit_semisimple).1
  exact ht (LinearMap.congr_fun hmultiplicative x)

private theorem isSemisimple_algHom [FiniteDimensional k V] {s : End k V}
    {Y : Type*} [AddCommGroup Y] [Module k Y] (φ : End k V →ₐ[k] End k Y)
    (hs : s.IsSemisimple) : (φ s).IsSemisimple := by
  apply End.isSemisimple_of_squarefree_aeval_eq_zero hs.minpoly_squarefree
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

private theorem tensor_factors_commute (a : End k V) (b : End k W) :
    Commute (TensorProduct.map a (1 : End k W)) (TensorProduct.map (1 : End k V) b) := by
  show _ * _ = _ * _
  rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
  simp

/-- The Jordan factors of a tensor product are the tensor products of the factors. -/
theorem multiplicativeJordanTensor : JordanFactorsSpec.tensorCompatibility := by
  intro k V W _ _ _ _ _ _ _ _ f s u g t v hf hg
  obtain ⟨hf, hsc, hs, hu, hsu, huu⟩ := hf
  obtain ⟨hg, htc, ht, hv, htu, hvu⟩ := hg
  let L := End.rTensorAlgHom k V W
  let R := End.lTensorAlgHom k W V
  have hmul (a : End k V) (b : End k W) :
      L a * R b = TensorProduct.map a b := by
    change TensorProduct.map a 1 * TensorProduct.map 1 b = _
    rw [← TensorProduct.map_mul, mul_one, one_mul]
  have hcomm (a : End k V) (b : End k W) : Commute (L a) (R b) :=
    tensor_factors_commute a b
  have hn (a b : End k (V ⊗[k] W)) (hc : Commute a b)
      (ha : IsNilpotent (a - 1)) (hb : IsNilpotent (b - 1)) : IsNilpotent (a * b - 1) := by
    have hc' : Commute (a - 1) b := hc.sub_left (Commute.one_left b)
    have he : a * b - 1 = (a - 1) * b + (b - 1) := by
      rw [sub_mul, one_mul]
      abel
    rw [he]
    exact ((hc'.mul_left (Commute.refl b)).sub_right (Commute.one_right _)).isNilpotent_add
      (hc'.isNilpotent_mul_right ha) hb
  refine ⟨by rw [hf, hg, TensorProduct.map_mul], ?_, ?_, ?_, ?_, ?_⟩
  · show _ * _ = _ * _
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hsc.eq, htc.eq]
  · rw [← hmul]
    exact End.IsSemisimple.mul_of_commute (hcomm s t)
      (isSemisimple_algHom L hs) (isSemisimple_algHom R ht)
  · rw [← hmul]
    exact hn _ _ (hcomm u v) (by simpa only [map_sub, map_one] using hu.map L)
      (by simpa only [map_sub, map_one] using hv.map R)
  · rw [← hmul]
    exact (hsu.map L).mul (htu.map R)
  · rw [← hmul]
    exact (huu.map L).mul (hvu.map R)

private theorem eigenbasis_of_isSemisimple {K U : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {f : End K U} (hf : f.IsSemisimple) :
    ∃ (b : Basis (Fin (finrank K U)) K U) (eigenvalue : Fin (finrank K U) → K),
      ∀ i, f (b i) = eigenvalue i • b i := by
  classical
  let S := ⋃ c : K, (f.eigenspace c : Set U)
  have hS : Submodule.span K S = ⊤ := by
    simpa only [S, Submodule.span_iUnion, Submodule.span_eq] using hf.iSup_eigenspace_eq_top
  obtain ⟨T, hTS, hspan, hind⟩ := exists_linearIndependent K S
  have htop : Submodule.span K (Set.range ((↑) : T → U)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hspan.trans hS
  let b : Basis T K U := Basis.mk hind htop.ge
  let := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  have he (i : T) : ∃ c : K, f (b i) = c • b i := by
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hTS i.property)
    exact ⟨c, by simpa only [b, Basis.mk_apply] using End.mem_eigenspace_iff.mp hc⟩
  choose c hc using he
  exact ⟨b.reindex e, c ∘ e.symm, fun i => by simpa using hc (e.symm i)⟩

private theorem isSemisimple_of_eigenbasis {K U ι : Type*} [Field K] [PerfectField K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    {f : End K U} (b : Basis ι K U) (eigenvalue : ι → K)
    (hb : ∀ i, f (b i) = eigenvalue i • b i) : f.IsSemisimple := by
  obtain ⟨n, hnmem, s, hsmem, hn, hs, he⟩ := f.exists_isNilpotent_isSemisimple
  have hfs : Commute f s := commute_of_mem_adjoin_self hsmem
  have hnil : IsNilpotent (f - s) := by rwa [he, add_sub_cancel_right]
  have hsf : s = f := by
    apply b.ext
    intro i
    have hi : b i ∈ f.genEigenspace (eigenvalue i) 1 := End.mem_genEigenspace_one.mpr (hb i)
    exact (End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hi hfs hs.isFinitelySemisimple hnil).trans (hb i).symm
  exact hsf ▸ hs

/-- Semisimplicity over a perfect field is equivalent to diagonalizability over its closure. -/
theorem semisimple_iff_geometricallyDiagonalizable : JordanFactorsSpec.semisimpleGeometric := by
  intro k V _ _ _ _ _ f
  let K := AlgebraicClosure k
  refine ⟨fun hf => eigenbasis_of_isSemisimple (isSemisimple_baseChange (K := K) hf), ?_⟩
  rintro ⟨b, eigenvalue, hb⟩
  let φ := End.baseChangeHom k K V
  have hφf : (φ f).IsSemisimple := isSemisimple_of_eigenbasis b eigenvalue hb
  obtain ⟨n, hnmem, s, hsmem, hn, hs, he⟩ := f.exists_isNilpotent_isSemisimple
  have hns : Commute n s :=
    commute_of_mem_adjoin_singleton_of_commute hsmem (commute_of_mem_adjoin_self hnmem).symm
  have hφs : (φ s).IsSemisimple := isSemisimple_baseChange hs
  have he' : φ n + φ s = 0 + φ f := by rw [← map_add, ← he, zero_add]
  have h := (End.isNilpotent_isSemisimple_unique (hn.map φ) hφs IsNilpotent.zero hφf
    (hns.map φ) (Commute.zero_left _) he').2
  have hinj : Function.Injective φ := LinearMap.baseChangeHom_injective k V (N := V) K
  exact hinj h ▸ hs

private theorem isNilpotent_sub_one_iff_charpoly {K U : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U] (f : End K U) :
    IsNilpotent (f - 1) ↔ f.charpoly = (X - 1) ^ finrank K U := by
  have hshift : (f - 1).charpoly = f.charpoly.comp (X + 1) := by
    simpa using LinearMap.charpoly_sub_smul f (1 : K)
  rw [LinearMap.isNilpotent_iff_charpoly, hshift]
  constructor
  · intro h
    have hc : (X + 1 : K[X]).comp (X - 1) = X := by
      simp [Polynomial.add_comp, Polynomial.one_comp, sub_add_cancel]
    have hh := congrArg (fun p : K[X] => p.comp (X - 1)) h
    change (f.charpoly.comp (X + 1)).comp (X - 1) = (X ^ finrank K U).comp (X - 1) at hh
    rwa [Polynomial.comp_assoc, hc, Polynomial.comp_X, Polynomial.X_pow_comp] at hh
  · intro h
    rw [h, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp,
      add_sub_cancel_right]

/-- Unipotence is detected by the characteristic polynomial over the algebraic closure. -/
theorem unipotent_iff_geometricCharpoly : JordanFactorsSpec.unipotentGeometric := by
  intro k V _ _ _ _ f
  let K := AlgebraicClosure k
  let φ := End.baseChangeHom k K V
  have hinj : Function.Injective φ := LinearMap.baseChangeHom_injective k V (N := V) K
  have hnil := IsNilpotent.map_iff (r := f - 1) hinj
  rw [map_sub, map_one] at hnil
  exact hnil.symm.trans (isNilpotent_sub_one_iff_charpoly (φ f))

end LinearAlgebraicGroups.Affine
