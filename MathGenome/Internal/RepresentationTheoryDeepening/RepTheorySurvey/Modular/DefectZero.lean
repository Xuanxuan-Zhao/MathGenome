import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.DefectZero
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.PrincipalBlockDefect
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplitMatrixColumns
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Artinian.Module

namespace RepTheorySurvey.Modular.DefectZero

open RelativeTrace CentralTraceIdeals DefectGroups
open scoped MonoidAlgebra

universe u v
variable {k : Type u} [Field k] {G : Type v} [Group G]

private noncomputable abbrev basisElement (k : Type u) [Field k] (g : G) : k[G] :=
  MonoidAlgebra.single g 1

private theorem conj_eq_basis_mul (g : G) (a : k[G]) :
    conjugation k g a = basisElement k g * a * basisElement k g⁻¹ := by
  classical
  ext x
  change (RelativeTraceSpec.conjugation k g a).coeff x = _
  rw [CentralTraceIdealsSpec.coeff_conjugation]
  simp [mul_assoc]

private noncomputable def totalTrace [Fintype G] (a : k[G]) : k[G] :=
  ∑ g : G, conjugation k g a

private theorem totalTrace_eq_relative [Fintype G]
    (a : fixedSubalgebra k (⊥ : Subgroup G)) :
    totalTrace a.val = (relativeTrace k (show (⊥ : Subgroup G) ≤ ⊤ from bot_le) a : k[G]) := by
  classical
  let e : LeftCosets (⊥ : Subgroup G) ⊤ ≃ G :=
    (Quotient.congr (Equiv.refl (⊤ : Subgroup G)) (by
      intro x y
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.bot_subgroupOf]
      rfl)).trans
      (QuotientGroup.quotientBot.toEquiv.trans Subgroup.topEquiv.toEquiv)
  have he (g : (⊤ : Subgroup G)) : e (QuotientGroup.mk g) = g := rfl
  let : Fintype (LeftCosets (⊥ : Subgroup G) ⊤) := Fintype.ofFinite _
  rw [relativeTrace_apply]
  refine Fintype.sum_equiv e.symm (fun g => conjugation k g a.val) (cosetConjugate k a) ?_
  intro g
  let gg : (⊤ : Subgroup G) := ⟨g, Subgroup.mem_top g⟩
  have hg : e.symm g = QuotientGroup.mk gg :=
    e.symm_apply_eq.mpr (he gg).symm
  rw [hg, cosetConjugate_mk]

private noncomputable def botInvariant (a : k[G]) : fixedSubalgebra k (⊥ : Subgroup G) :=
  ⟨a, fun g => by
    have hg : (g : G) = 1 := g.property
    simp [hg]⟩

private theorem mem_traceIdeal_bot [Fintype G] (z : Subalgebra.center k k[G]) :
    z ∈ traceIdeal k (⊥ : Subgroup G) ↔ ∃ a : k[G], totalTrace a = z.val := by
  rw [mem_traceIdeal_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, (totalTrace_eq_relative a).trans ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨botInvariant a, (totalTrace_eq_relative (botInvariant a)).symm.trans ha⟩

private theorem trivial_defect_iff_trace [Finite G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (b : BlockIdempotent k G) :
    (∀ D : Subgroup G, isDefectGroup p b D → D = ⊥) ↔
      b.val ∈ traceIdeal k (⊥ : Subgroup G) := by
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨x, S, hx, htrace, hD, hBr, _⟩ := exists_support_sylow p b
  constructor
  · intro h
    rwa [← h _ hD]
  · intro h D hdef
    obtain ⟨T, g, hg⟩ := sylowConjugateInto_of_mem_traceIdeal (k := k) p (⊥ : Subgroup G)
      (IsPGroup.of_bot) x b.val h hx
    have hT : DefectGroupsSpec.sylowImage T = ⊥ := by
      apply le_antisymm _ bot_le
      intro y hy
      have hg' : MulAut.conj g y = 1 := hg ⟨y, hy, rfl⟩
      exact (MulAut.conj g).injective (hg'.trans (map_one _).symm)
    have hTS : T.toSubgroup ≤ S.toSubgroup := by
      intro y hy
      have hyImage : (y : G) ∈ DefectGroupsSpec.sylowImage T := ⟨y, hy, rfl⟩
      rw [hT] at hyImage
      have hyOne : y = 1 := Subtype.ext hyImage
      rw [hyOne]
      exact S.one_mem
    have hS : S.toSubgroup = T.toSubgroup :=
      T.is_maximal' S.isPGroup' hTS
    have hbot : DefectGroupsSpec.sylowImage S = ⊥ :=
      (congrArg (fun H : Subgroup (Subgroup.centralizer ({x} : Set G)) =>
        H.map (Subgroup.centralizer ({x} : Set G)).subtype) hS).trans hT
    obtain ⟨g, hg⟩ := (hBr D hdef.1.1).mp hdef.1.2
    exact le_antisymm (by simpa [hbot] using hg) bot_le

private theorem coeff_one_mul_comm (x y : k[G]) :
    (x * y).coeff 1 = (y * x).coeff 1 := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_left, MonoidAlgebra.coeff_mul_apply_right]
  simp only [mul_one, one_mul]
  exact Finsupp.sum_congr (fun g _ => mul_comm (x.coeff g) (y.coeff g⁻¹))

/-- The coefficient at `1` of `x * totalTrace a` is the linear trace
of the operator `y ↦ x * y * a` in the group basis. -/
private theorem coeff_totalTrace [Fintype G] (x a : k[G]) :
    (x * totalTrace a).coeff 1 =
      LinearMap.trace k k[G] (LinearMap.mulLeftRight k (x, a)) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k)]
  simp only [totalTrace, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Matrix.trace]
  apply Finset.sum_congr rfl
  intro g _
  rw [conj_eq_basis_mul, ← mul_assoc, ← mul_assoc]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (x * basisElement k g * a * basisElement k g⁻¹).coeff 1 =
    (x * basisElement k g * a).coeff g
  simp

private theorem projection_kills_radical_of_trace [Fintype G] (b : BlockIdempotent k G)
    {a : k[G]} (ha : totalTrace a = b.element) :
    ∀ x ∈ Ring.jacobson k[G], b.projection x = 0 := by
  let : IsArtinianRing k[G] := IsArtinianRing.of_finite k _
  have hcoeff (x : k[G]) (hx : x ∈ Ring.jacobson k[G]) :
      (x * b.element).coeff 1 = 0 := by
    obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := k[G])
    have hxnil : IsNilpotent x := ⟨n, by
      simpa [hn] using Ideal.pow_mem_pow hx n⟩
    have hcomm : Commute (Algebra.lmul k k[G] x) (LinearMap.mulRight k a) :=
      LinearMap.ext fun y => (mul_assoc x y a).symm
    rw [← ha, coeff_totalTrace]
    change LinearMap.trace k k[G] (LinearMap.mulRight k a * Algebra.lmul k k[G] x) = 0
    rw [← hcomm.eq]
    exact (LinearMap.isNilpotent_trace_of_isNilpotent
      (hcomm.isNilpotent_mul_right (hxnil.map (Algebra.lmul k k[G])))).eq_zero
  intro x hx
  apply Subtype.ext
  ext g
  change (x * b.element).coeff g = (0 : k[G]).coeff g
  simpa [mul_assoc, basisElement] using
    hcoeff (basisElement k g⁻¹ * x) (Ideal.mul_mem_left _ _ hx)

private theorem semisimple_of_trace [Fintype G] (b : BlockIdempotent k G)
    {a : k[G]} (ha : totalTrace a = b.element) : IsSemisimpleRing b.Algebra := by
  let : IsArtinianRing k[G] := IsArtinianRing.of_finite k _
  exact RingHom.isSemisimpleRing_of_surjective
    (Ideal.Quotient.lift _ b.projection (projection_kills_radical_of_trace b ha))
    (Ideal.Quotient.lift_surjective_of_surjective _ _ b.projection_surjective)

private theorem block_injective_mod_radical (b : BlockIdempotent k G)
    [IsSemisimpleRing b.Algebra] {r : ℕ} {d : Fin r → ℕ}
    (e : GroupAlgebraRadicalQuotient k G ≃ₐ[k]
       ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) k))
    {x y : k[G]} (hx : x * b.element = x) (hy : y * b.element = y)
    (h : modularColumnMap e x = modularColumnMap e y) : x = y := by
  have hd : x - y ∈ Ring.jacobson k[G] := by
    rw [← modularColumnMap_ker e, RingHom.mem_ker]
    change modularColumnMap e (x - y) = 0
    rw [map_sub, h, sub_self]
  let : RingHomSurjective b.projection := ⟨b.projection_surjective⟩
  have hz : b.projection (x - y) ∈ Ring.jacobson b.Algebra :=
    Ring.le_comap_jacobson b.projection hd
  rw [IsSemisimpleRing.jacobson_eq_bot] at hz
  have hz' : b.projection (x - y) = (0 : b.Algebra) := Ideal.mem_bot.mp hz
  have he := congrArg (fun z : b.Algebra => z.val) hz'
  change (x - y) * b.element = 0 at he
  rwa [sub_mul, hx, hy, sub_eq_zero] at he

private theorem totalTrace_sum [Fintype G] {ι : Type*} (s : Finset ι) (a : ι → k[G]) :
    totalTrace (∑ i ∈ s, a i) = ∑ i ∈ s, totalTrace (a i) := by
  simp only [totalTrace, map_sum]
  exact Finset.sum_comm

private theorem totalTrace_mul_block [Fintype G] (b : BlockIdempotent k G)
    (a : k[G]) : totalTrace (a * b.element) = totalTrace a * b.element := by
  simp only [totalTrace, map_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun g _ => congrArg (conjugation k g a * ·)
    (CentralTraceIdealsSpec.conjugation_center k g b.val)

private theorem totalTrace_central [Fintype G] (a : k[G]) :
    IsMulCentral (totalTrace a) := by
  change IsMulCentral (totalTrace (botInvariant a).val)
  rw [totalTrace_eq_relative]
  exact trace_mem_center k ⊥ (botInvariant a)

-- Expanding the idempotent in the group basis computes the conjugation trace
-- on its column ideal. The one-dimensional corner identifies the coefficients.
private theorem totalTrace_mul_idempotent [Fintype G] (E : k[G])
    (hE : IsIdempotentElem E)
    (hcorner : ∀ x : k[G], ∃ c : k, E * x * E = c • E) :
    totalTrace (E.coeff 1 • E) * E = E := by
  classical
  have hcoeff (g : G) :
      E.coeff 1 • (E * basisElement k g⁻¹ * E) = E.coeff g • E := by
    obtain ⟨c, hc⟩ := hcorner (basisElement k g⁻¹)
    have ht : (E * basisElement k g⁻¹ * E).coeff 1 = E.coeff g := by
      rw [coeff_one_mul_comm (E * basisElement k g⁻¹) E, ← mul_assoc, hE.eq]
      simp [basisElement]
    rw [hc] at ht ⊢
    rw [smul_smul, mul_comm]
    exact congrArg (fun t : k => t • E) ht
  calc
    totalTrace (E.coeff 1 • E) * E =
        ∑ g : G, basisElement k g * (E.coeff 1 • (E * basisElement k g⁻¹ * E)) := by
      simp only [totalTrace, Finset.sum_mul, conj_eq_basis_mul, mul_smul_comm,
        smul_mul_assoc, mul_assoc]
    _ = ∑ g : G, E.coeff g • (basisElement k g * E) := by
      simp only [hcoeff, mul_smul_comm]
    _ = (∑ g : G, E.coeff g • basisElement k g) * E := by
      simp only [Finset.sum_mul, smul_mul_assoc]
    _ = E := by
      have hsum : (∑ g : G, E.coeff g • basisElement k g) = E := by
        ext g
        simp [basisElement, MonoidAlgebra.coeff_single]
      rw [hsum, hE.eq]

private theorem trace_of_semisimple [Fintype G] (b : BlockIdempotent k G)
    [IsSemisimpleRing b.Algebra] (hsplit : IsSplitMatrixAlgebra k (GroupAlgebraRadicalQuotient k G)) :
    ∃ a : k[G], totalTrace a = b.element := by
  classical
  obtain ⟨r, d, hd, ⟨e⟩⟩ := hsplit
  let q := modularColumnMap e
  have hq : Function.Surjective q := modularColumnMap_surjective e
  let s (i : Fin r) : Fin (d i) := ⟨0, hd i⟩
  let M (i : Fin r) : Matrix (Fin (d i)) (Fin (d i)) k := Matrix.single (s i) (s i) 1
  have scalars (i : Fin r) {x : k[G]} (hx : IsMulCentral x) :
      ∃ c : k, Matrix.scalar (Fin (d i)) c = q x i := by
    let qi := (Pi.evalAlgHom k (fun j => Matrix (Fin (d j)) (Fin (d j)) k) i).comp q
    have hqi : Function.Surjective qi := fun z => by
      obtain ⟨y, hy⟩ := hq (Pi.single i z)
      exact ⟨y, by change q y i = z; simp [hy]⟩
    have hm : q x i ∈ Set.center (Matrix (Fin (d i)) (Fin (d i)) k) := hx.map hqi
    rwa [Matrix.center_eq_range] at hm
  have hb (i : Fin r) : q b.element i = 0 ∨ q b.element i = 1 := by
    obtain ⟨c, hc⟩ := scalars i b.central
    have hi : IsIdempotentElem (q b.element i) := by
      exact b.idempotent.map ((Pi.evalAlgHom k (fun j =>
        Matrix (Fin (d j)) (Fin (d j)) k) i).comp q)
    have hscalar : Function.Injective (Matrix.scalar (Fin (d i)) (α := k)) := by
      intro c₁ c₂ heq
      simpa [Matrix.scalar_apply] using congrFun (congrFun heq (s i)) (s i)
    have hcidem : IsIdempotentElem c := hscalar (by rw [map_mul, hc, hi.eq])
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcidem with rfl | rfl
    · exact Or.inl (by simpa using hc.symm)
    · exact Or.inr (by simpa using hc.symm)
  -- Lift one diagonal matrix unit per factor and project the lifts into the block.
  choose pre hpre using fun i => hq (Pi.single i (M i))
  let E (i : Fin r) : k[G] := pre i * b.element
  have hEfix (i : Fin r) : E i * b.element = E i := by
    simp [E, mul_assoc, b.idempotent.eq]
  have hEcoord (i j : Fin r) : q (E i) j = (Pi.single i (M i)) j * q b.element j := by
    simp [E, map_mul, hpre]
  have hEone (i : Fin r) (hi : q b.element i = 1) : q (E i) = Pi.single i (M i) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [hEcoord, hi]
    · simp [hEcoord, Pi.single_eq_of_ne hj]
  have htrace (i : Fin r) (hi : q b.element i = 1) :
      q (totalTrace ((E i).coeff 1 • E i)) i = 1 := by
    have hEidem : IsIdempotentElem (E i) := by
      change E i * E i = E i
      refine block_injective_mod_radical b e ?_ (hEfix i) ?_
      · rw [mul_assoc, hEfix]
      · change q (E i * E i) = q (E i)
        rw [map_mul, hEone i hi, ← Pi.single_mul]
        simp [M]
    have hEcorner (x : k[G]) : ∃ c : k, E i * x * E i = c • E i := by
      refine ⟨q x i (s i) (s i), block_injective_mod_radical b e ?_ ?_ ?_⟩
      · rw [mul_assoc (E i * x), hEfix]
      · rw [smul_mul_assoc, hEfix]
      · change q (E i * x * E i) = q (q x i (s i) (s i) • E i)
        simp only [map_mul, map_smul, hEone i hi]
        funext j
        by_cases hj : j = i
        · subst j
          simp [M, Matrix.smul_single]
        · simp [Pi.single_eq_of_ne hj]
    let z := totalTrace ((E i).coeff 1 • E i)
    have hz : q z i * M i = M i := by
      have heq := congrArg (fun a : k[G] => q a i)
        (totalTrace_mul_idempotent (E i) hEidem hEcorner)
      simpa [z, hEone i hi] using heq
    obtain ⟨c, hc⟩ := scalars i (totalTrace_central ((E i).coeff 1 • E i))
    have hc' : c = 1 := by
      change Matrix.scalar (Fin (d i)) c = q z i at hc
      rw [← hc] at hz
      simpa [M, Matrix.scalar_apply] using congrFun (congrFun hz (s i)) (s i)
    simpa [hc'] using hc.symm
  have htraceZero (i : Fin r) (x : k[G]) (hx : q x i = 0) :
      q (totalTrace x) i = 0 := by
    simp [totalTrace, conj_eq_basis_mul, map_sum, map_mul, hx]
  let a : k[G] := ∑ i : Fin r, (E i).coeff 1 • E i
  have hafix : a * b.element = a := by
    simp [a, Finset.sum_mul, hEfix]
  refine ⟨a, block_injective_mod_radical b e ?_ b.idempotent.eq ?_⟩
  · rw [← totalTrace_mul_block, hafix]
  · change q (totalTrace a) = q b.element
    funext i
    simp only [a, totalTrace_sum, map_sum, Finset.sum_apply]
    rcases hb i with hi | hi
    · rw [hi]
      apply Finset.sum_eq_zero
      intro j _
      apply htraceZero
      simp [hEcoord, hi]
    · rw [Finset.sum_eq_single i]
      · exact (htrace i hi).trans hi.symm
      · intro j _ hj
        apply htraceZero
        simp [hEcoord, Pi.single_eq_of_ne hj.symm]
      · simp

/-- A block has trivial defect groups exactly when its block algebra is semisimple. -/
theorem defect_zero_iff [Finite G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hsplit : IsSplitMatrixAlgebra k (GroupAlgebraRadicalQuotient k G))
    (b : BlockIdempotent k G) :
    (∀ D : Subgroup G, isDefectGroup p b D → D = ⊥) ↔ IsSemisimpleRing b.Algebra := by
  let : Fintype G := Fintype.ofFinite G
  rw [trivial_defect_iff_trace p b, mem_traceIdeal_bot]
  constructor
  · rintro ⟨a, ha⟩
    exact semisimple_of_trace b ha
  · intro h
    let := h
    exact trace_of_semisimple b hsplit

/-- The principal-block and defect-zero assertions of MR13. -/
theorem principal_blocks_and_defect_zero : DefectZeroSpec.principalBlocksAndDefectZeroType.{u, v} := by
  refine ⟨PrincipalBlockDefect.principal_block_defect_iff, ?_⟩
  intro k _ G _ _ p _ _ hsplit b
  exact defect_zero_iff p hsplit b

end RepTheorySurvey.Modular.DefectZero
