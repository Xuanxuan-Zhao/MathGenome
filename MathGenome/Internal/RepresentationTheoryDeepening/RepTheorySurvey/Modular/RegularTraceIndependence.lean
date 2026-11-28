import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.SplitMatrixColumns
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.RegularTraceIndependence
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Int.GCD

/-! Residue-field trace independence on the `p`-regular set. -/

namespace RepTheorySurvey.Modular

universe uG uO uK uI uV uF

private theorem regularPart_exists {G : Type uG} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (g : G) :
    ∃ (a : ℕ) (u : G) (v : PRegular G p), g = v.val * u ∧ Commute v.val u ∧ u ^ (p ^ a) = 1 := by
  let n := orderOf g
  let a := n.factorization p
  let m := ordCompl[p] n
  let b := p ^ a
  have hn : n ≠ 0 := (orderOf_pos g).ne'
  have hb : b * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hm : m.Coprime p := (Nat.coprime_ordCompl hp hn).symm
  have hcop : b.Coprime m := hm.symm.pow_left a
  have hbez : (1 : ℤ) = (b : ℤ) * b.gcdA m + (m : ℤ) * b.gcdB m := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using Nat.gcd_eq_gcd_ab b m
  have hpow : g ^ ((b : ℤ) * (m : ℤ)) = 1 := by
    rw [← Nat.cast_mul, zpow_natCast, hb, pow_orderOf_eq_one]
  let x := (b : ℤ) * b.gcdA m
  let y := (m : ℤ) * b.gcdB m
  have hv : (g ^ x) ^ m = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have he : x * (m : ℤ) = ((b : ℤ) * (m : ℤ)) * b.gcdA m := by
      dsimp [x]
      ac_rfl
    rw [he, zpow_mul, hpow, one_zpow]
  refine ⟨a, g ^ y, ⟨g ^ x, hm.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hv)⟩,
    ?_, Commute.zpow_zpow_self g x y, ?_⟩
  · change g = g ^ x * g ^ y
    rw [← zpow_add, ← hbez, zpow_one]
  · change (g ^ y) ^ b = 1
    rw [← zpow_natCast, ← zpow_mul]
    have he : y * (b : ℤ) = ((b : ℤ) * (m : ℤ)) * b.gcdB m := by
      dsimp [y]
      ac_rfl
    rw [he, zpow_mul, hpow, one_zpow]

section

variable {F : Type uF} [Field F] {G : Type uG} [Group G]

private theorem trace_eq_of_regularPart {p a : ℕ} [Fact p.Prime] [CharP F p]
    {V : Type uV} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    {v u : G} (hcomm : Commute v u) (hu : u ^ (p ^ a) = 1) :
    LinearMap.trace F V (ρ (v * u)) = LinearMap.trace F V (ρ v) := by
  -- Prove nilpotence in the group algebra so this also applies to the zero module.
  let : CharP (MonoidAlgebra F G) p :=
    charP_of_injective_algebraMap (algebraMap F (MonoidAlgebra F G)).injective p
  let w := MonoidAlgebra.of F G u
  have hw : IsNilpotent (w - 1) := by
    refine ⟨p ^ a, ?_⟩
    rw [sub_pow_char_pow_of_commute p a (Commute.one_right w), one_pow,
      ← map_pow (MonoidAlgebra.of F G), hu, map_one, sub_self]
  have hnil : IsNilpotent (ρ u - 1) := by
    simpa only [w, map_sub, map_one, Representation.asAlgebraHom_of] using
      hw.map ρ.asAlgebraHom
  simpa only [map_mul, Module.End.mul_eq_comp, map_one, one_mul] using
    LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (1 : F) (hcomm.map ρ)
      (by rwa [map_one])

set_option backward.isDefEq.respectTransparency false in
private theorem trace_eq_columnTrace {r : ℕ} {d : Fin r → ℕ}
    {q : MonoidAlgebra F G →ₐ[F] ((j : Fin r) → Matrix (Fin (d j)) (Fin (d j)) F)}
    {M : ModuleCat.{uV} (MonoidAlgebra F G)} {j : Fin r}
    (e : M ≃ₗ[MonoidAlgebra F G] columnModule q j) (a : MonoidAlgebra F G) :
    LinearMap.trace F _ ((moduleRepresentation F G M).asAlgebraHom a) =
      LinearMap.trace F (Fin (d j) → F) (columnAction q j a) := by
  let E : RestrictScalars F (MonoidAlgebra F G) M ≃ₗ[F] columnModule q j :=
    { (RestrictScalars.addEquiv F (MonoidAlgebra F G) M).trans e.toAddEquiv with
      map_smul' := fun c x => by
        change e (algebraMap F (MonoidAlgebra F G) c •
          RestrictScalars.addEquiv F (MonoidAlgebra F G) M x) = c • e (RestrictScalars.addEquiv F (MonoidAlgebra F G) M x)
        rw [e.map_smul, algebraMap_smul] }
  have hconj : E.conj ((moduleRepresentation F G M).asAlgebraHom a) =
      (columnAction q j a : Module.End F (columnModule q j)) := by
    ext x
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Representation.ofModule_asAlgebraHom_apply_apply]
    change e (a • e.symm x) = a • x
    rw [e.map_smul, e.apply_symm_apply]
  exact (LinearMap.trace_conj' (R := F) ((moduleRepresentation F G M).asAlgebraHom a) E).symm.trans
    (congrArg (LinearMap.trace F (columnModule q j)) hconj)

end

set_option backward.isDefEq.respectTransparency false in
/-- Over the residue field of the splitting system, the simple traces on the
`p`-regular elements are linearly independent. -/
theorem regularTrace_linearIndependent
    {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (system : SplittingSystem G p O K)
    {ι : Type uI} (S : ι → ModuleCat.{uV} (MonoidAlgebra (IsLocalRing.ResidueField O) G))
    (hS : IsSimpleRepresentativeFamily S) :
    LinearIndependent (IsLocalRing.ResidueField O)
      (fun i (g : PRegular G p) =>
        LinearMap.trace (IsLocalRing.ResidueField O) _
          (moduleRepresentation (IsLocalRing.ResidueField O) G (S i) g.val)) := by
  classical
  let k := IsLocalRing.ResidueField O
  let : Fact p.Prime := ⟨system.prime⟩
  let : CharP k p := system.residueChar
  let τ (i : ι) : MonoidAlgebra k G →ₗ[k] k :=
    (LinearMap.trace k _).comp ((moduleRepresentation k G (S i)).asAlgebraHom.toLinearMap)
  have hτ (i : ι) (g : G) :
      τ i (MonoidAlgebra.of k G g) = LinearMap.trace k _ (moduleRepresentation k G (S i) g) := by
    simp [τ]
  rw [linearIndependent_iff']
  intro s c hr i hi
  let L : MonoidAlgebra k G →ₗ[k] k := ∑ j ∈ s, c j • τ j
  have hL : ∀ a : MonoidAlgebra k G, L a = 0 := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      obtain ⟨a, u, v, hg, hcomm, hu⟩ := regularPart_exists system.prime g
      have htrace (j : ι) := trace_eq_of_regularPart (F := k) (p := p)
        (V := RestrictScalars k (MonoidAlgebra k G) (S j))
        (moduleRepresentation k G (S j)) hcomm hu
      simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, hτ, hg, htrace]
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using congrFun hr v
    | add a b ha hb => rw [map_add, ha, hb, add_zero]
    | smul c a ha => rw [map_smul, ha, smul_zero]
  obtain ⟨r, d, hd, ⟨e⟩⟩ := system.modularSplit
  let q := modularColumnMap e
  choose f ef using fun j => column_exhaustive q hd (modularColumnMap_surjective e)
    (modularColumnMap_ker e).le (S j) (hS.simple j)
  have hf : Function.Injective f := by
    intro j l h
    obtain ⟨ej⟩ := ef j
    obtain ⟨el⟩ := ef l
    rw [← h] at el
    exact hS.eq_of_iso ⟨ej.trans el.symm⟩
  obtain ⟨a, -, ha⟩ := column_trace_test q (modularColumnMap_surjective e) (f i) ⟨0, hd (f i)⟩
  have ht (j : ι) : τ j a = if j = i then 1 else 0 := by
    obtain ⟨ej⟩ := ef j
    change LinearMap.trace k _ ((moduleRepresentation k G (S j)).asAlgebraHom a) = _
    rw [trace_eq_columnTrace ej, ha]
    simp only [hf.eq_iff]
  simpa [L, LinearMap.sum_apply, LinearMap.smul_apply, ht, smul_eq_mul, mul_ite, hi] using hL a

end RepTheorySurvey.Modular
