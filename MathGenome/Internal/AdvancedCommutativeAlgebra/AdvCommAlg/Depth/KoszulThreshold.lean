import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.KoszulThreshold
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.SelfDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.NullHomotopy
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.CoefficientExactness

/-! DP-09 (paper.tex:2925–2972). The proof uses the determinant trick in the
acyclic case, maximal regular lists and coefficient long exact sequences in
the finite case, and the canonical oriented self-duality for the last
homological degree. No regularity of the generating list is assumed. -/

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise TensorProduct
noncomputable section
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace AdvCommAlg.Depth
open Koszul
variable {R : Type u} [CommRing R]

/-- The first nonvanishing degree of Hom_R(K(a), M), with infimum ∅ = ∞. -/
def koszulCohomologyThreshold {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (a : List R) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : Nontrivial (Koszul.SelfDuality.cohomology M a i)), (i : ℕ∞)

/-- n minus the largest nonvanishing homology degree, or ∞ if acyclic. -/
def koszulHomologyThreshold {R : Type u} [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] (a : List R) : ℕ∞ := by
  classical
  exact if ∃ j : ℕ, Nontrivial (Koszul.homology M a j) then
    (a.length : ℕ∞) - ⨆ (j : ℕ) (_ : Nontrivial (Koszul.homology M a j)), (j : ℕ∞)
  else ⊤


/-- Compare the explicit Hom complex used for coefficient sequences and the
contravariant-Hom construction used by self-duality. The maps are identity
linear maps in each exterior degree. -/
def koszulCochainIso (M : ModuleCat.{u} R) (a : List R) :
    Koszul.cochainComplex M a ≅ SelfDuality.cochainComplex M a :=
  HomologicalComplex.Hom.isoOfComponents (fun q => (LinearEquiv.refl R _).toModuleIso) (by
    intro i j hij
    change i+1=j at hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    simp [SelfDuality.cochainComplex, SelfDuality.homCoefficient,
      Koszul.cochainComplex, Koszul.cochainDifferential, listComplex, complex,
      LinearEquiv.toModuleIso, LinearMap.lcomp_apply'])


/-- IM=M forces acyclicity by the determinant trick and the ideal homotopy. -/
theorem koszul_acyclic_of_smul_eq_top (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (a : List R)
    (hI : listIdeal a • (⊤ : Submodule R M) = ⊤) :
    (∀ q, Subsingleton (homology M a q)) ∧
      (∀ q, Subsingleton (SelfDuality.cohomology M a q)) := by
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    (listIdeal a) (⊤ : Submodule R M) Module.Finite.fg_top (le_of_eq hI.symm)
  have hid : r • 𝟙 (coefficientComplex M a) = 𝟙 _ := by
    ext n : 2
    apply TensorProduct.ext
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro m
    change r • (w ⊗ₜ[R] m) = w ⊗ₜ[R] m
    rw [← TensorProduct.tmul_smul, hrM m Submodule.mem_top]
  have hz (q : ℕ) (z : homology M a q) : z = 0 := by
    obtain ⟨h⟩ := coefficient_nullHomotopy M a r hr
    have he := h.homologyMap_eq q
    rw [hid, HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at he
    exact congrArg (fun f : homology M a q ⟶ homology M a q => f z) he
  refine ⟨fun q => ⟨fun z w => (hz q z).trans (hz q w).symm⟩, ?_⟩
  intro q
  by_cases hq : q ≤ a.length
  · letI : Subsingleton (homology M a (a.length-q)) :=
      ⟨fun z w => (hz _ z).trans (hz _ w).symm⟩
    exact (SelfDuality.cohomologyDualityEquiv M a q (a.length-q) (by omega)).injective.subsingleton
  · exact SelfDuality.cohomology_vanish M a q (by omega)

private lemma up_prev_zero : (ComplexShape.up ℕ).prev 0 = 0 :=
  ComplexShape.prev_eq_self' _ _ (by intro i hi; change i+1=0 at hi; omega)

/-- A nonzero element annihilated by the generating ideal gives a nonzero
class in cohomological degree zero. There are no incoming boundaries. -/
lemma koszul_cohomology_zero_nontrivial (M : Type u) [AddCommGroup M] [Module R M]
    (a : List R) (m : M) (hm : m ≠ 0)
    (hIm : ∀ r ∈ listIdeal a, r • m = 0) :
    Nontrivial (Koszul.cohomology M a 0) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hz
  let C := Koszul.cochainComplex M a
  have he : (C.sc' 0 0 1).Exact :=
    (C.exactAt_iff' 0 0 1 up_prev_zero (ComplexShape.next_eq' _ rfl)).mp
      ((C.exactAt_iff_isZero_homology 0).mpr
        (ModuleCat.isZero_iff_subsingleton.mpr hz))
  let f : (⋀[R]^0 (Fin a.length → R)) →ₗ[R] M :=
    (exteriorPower.zeroEquiv R (Fin a.length → R)).toLinearMap.smulRight m
  have hf : (C.sc' 0 0 1).g f = 0 := by
    change f.comp (differential (listForm a) 0) = 0
    apply LinearMap.ext
    intro w
    change exteriorPower.zeroEquiv R _ (differential (listForm a) 0 w) • m = 0
    rw [differential_one]
    exact hIm _ (listForm_mem a _)
  obtain ⟨g, hg⟩ := (ShortComplex.moduleCat_exact_iff _).mp he f hf
  have hd : (C.sc' 0 0 1).f = 0 := C.shape 0 0 (by simp)
  rw [hd] at hg
  have hfg : f = 0 := hg.symm
  have h := LinearMap.congr_fun hfg ((exteriorPower.zeroEquiv R (Fin a.length → R)).symm 1)
  apply hm
  simpa [f] using h

lemma koszulCochainMap_smul (M : ModuleCat.{u} R) (a : List R) (r : R) :
    CoefficientSequences.coefficientCochainMap a (r • 𝟙 M) =
      r • 𝟙 (CoefficientSequences.coefficientCochainComplex M a) := by
  ext n : 2
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro w
  rfl

lemma koszulCochainMap_smul_homology_zero (M : ModuleCat.{u} R) (a : List R)
    (r : R) (hr : r ∈ listIdeal a) (q : ℕ) :
    HomologicalComplex.homologyMap
      (CoefficientSequences.coefficientCochainMap a (r • 𝟙 M)) q = 0 := by
  rw [koszulCochainMap_smul]
  obtain ⟨h⟩ := cochain_nullHomotopy M a r hr
  exact h.homologyMap_eq q |>.trans (HomologicalComplex.homologyMap_zero _ _ _)

/-- Killing a regular element of the generating ideal shifts the first
nonvanishing cohomology degree by one. -/
lemma koszul_cohomology_regular_step (M : ModuleCat.{u} R) (a : List R)
    (x : R) (hx : x ∈ listIdeal a) (hreg : IsSMulRegular M x) (n : ℕ)
    (hnt : Nontrivial (Koszul.cohomology (QuotSMulTop x M) a n))
    (hv : ∀ i < n, Subsingleton (Koszul.cohomology (QuotSMulTop x M) a i)) :
    Nontrivial (Koszul.cohomology M a (n+1)) ∧
      ∀ i < n+1, Subsingleton (Koszul.cohomology M a i) := by
  let T := (M.smulShortComplex x).map (CoefficientSequences.coefficientCochainFunctor a)
  have hT : T.ShortExact := cochainCoefficient_shortExact a _ hreg.smulShortComplex_shortExact
  have hzero (i : ℕ) : HomologicalComplex.homologyMap T.f i = 0 :=
    koszulCochainMap_smul_homology_zero M a x hx i
  have hvan : ∀ i < n+1, Subsingleton (Koszul.cohomology M a i) := by
    intro i hi
    cases i with
    | zero =>
      have : Mono (HomologicalComplex.homologyMap T.f 0) := by
        have := hT.mono_f
        apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
        intro i hi
        change i+1=0 at hi
        omega
      exact ModuleCat.isZero_iff_subsingleton.mp
        (IsZero.of_mono_eq_zero _ (hzero 0))
    | succ i =>
      have : Epi (hT.δ i (i+1) rfl) := (hT.homology_exact₁ i (i+1) rfl).epi_f (hzero _)
      have hq : IsZero (T.X₃.homology i) :=
        ModuleCat.isZero_iff_subsingleton.mpr (hv i (by omega))
      exact ModuleCat.isZero_iff_subsingleton.mp
        (IsZero.of_epi_eq_zero (hT.δ i (i+1) rfl) (hq.eq_zero_of_src _))
  refine ⟨?_, hvan⟩
  have hz : IsZero (T.X₂.homology n) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hvan n (by omega))
  have : Mono (hT.δ n (n+1) rfl) := hT.mono_δ n (n+1) rfl hz
  letI : Nontrivial (T.X₃.homology n) := hnt
  exact @Function.Injective.nontrivial _ _ hnt (hT.δ n (n+1) rfl)
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- The length of a maximal regular list is the first nonzero cohomology
degree, proved by successive regular quotients. -/
lemma maximalRegular_koszul_cohomology [IsNoetherianRing R]
    (I : Ideal R) (a : List R) (ha : listIdeal a = I)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (xs : List R)
    (hmax : MaximalRegular I M xs) :
    Nontrivial (Koszul.cohomology M a xs.length) ∧
      ∀ i < xs.length, Subsingleton (Koszul.cohomology M a i) := by
  induction xs generalizing M with
  | nil =>
    have hg : grade I M = 0 := by
      simpa using (maximalRegular_length_eq_grade I M hI [] hmax).symm
    obtain ⟨m, hm, hm0⟩ := (Submodule.ne_bot_iff _).mp
      ((grade_zero_iff_annihilator_ne_bot I M hI).mp hg)
    refine ⟨koszul_cohomology_zero_nontrivial M a m hm0 ?_, by simp⟩
    intro r hr
    exact (Submodule.mem_torsionBySet_iff _ _).mp hm ⟨r, ha ▸ hr⟩
  | cons x xs ih =>
    have hreg := (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hmax.1
    have hx : x ∈ I := hmax.2.1 x (by simp)
    have hqI := ideal_smul_quotSMulTop_ne_top I M x hx hI
    have htail : MaximalRegular I (QuotSMulTop x M) xs := by
      refine ⟨hreg.2, fun y hy => hmax.2.1 y (by simp [hy]), ?_⟩
      intro y hy hbad
      exact hmax.2.2 y hy
        ((RingTheory.Sequence.isRegular_cons_iff M x (xs ++ [y])).mpr ⟨hreg.1, hbad⟩)
    obtain ⟨hnt, hv⟩ := ih (QuotSMulTop x M) hqI htail
    simpa only [List.length_cons] using
      koszul_cohomology_regular_step (ModuleCat.of R M) a x (ha.symm ▸ hx)
        hreg.1 xs.length hnt hv

/-- The finite-grade case records both the first nonzero degree and all
preceding vanishing groups. -/
lemma exists_first_koszul_cohomology [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R) (ha : listIdeal a = I)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    ∃ n : ℕ, grade I M = n ∧ Nontrivial (Koszul.cohomology M a n) ∧
      ∀ i < n, Subsingleton (Koszul.cohomology M a i) := by
  haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp (by
    intro h
    letI := h
    exact hI (Subsingleton.elim _ _))
  obtain ⟨xs, hxs⟩ := exists_maximalRegular_extension I M hI []
    ((RegularSequence.regular_nil_iff M).mpr inferInstance) (by simp)
  simp only [List.nil_append] at hxs
  exact ⟨xs.length, (maximalRegular_length_eq_grade I M hI xs hxs).symm,
    maximalRegular_koszul_cohomology I a ha M hI xs hxs⟩

/-- The two upstream presentations have canonically isomorphic cohomology. -/
def koszulCohomologyIso (M : Type u) [AddCommGroup M] [Module R M]
    (a : List R) (q : ℕ) :
    Koszul.cohomology M a q ≅ SelfDuality.cohomology M a q :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).mapIso
    (koszulCochainIso (ModuleCat.of R M) a)

private lemma firstDegree_eq_nat (F : ℕ → Type u) (n : ℕ)
    (hnt : Nontrivial (F n)) (hv : ∀ i < n, Subsingleton (F i)) :
    (⨅ (i : ℕ) (_ : Nontrivial (F i)), (i : ℕ∞)) = n := by
  apply le_antisymm
  · exact iInf_le_of_le n (iInf_le_of_le hnt le_rfl)
  · apply le_iInf
    intro i
    apply le_iInf
    intro hi
    have hni : n ≤ i := by
      by_contra h
      exact (not_nontrivial_iff_subsingleton.mpr (hv i (by omega))) hi
    exact_mod_cast hni

theorem grade_eq_koszulCohomologyThreshold [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R) (ha : listIdeal a = I) :
    grade I M = koszulCohomologyThreshold M a := by
  classical
  by_cases hI : I • (⊤ : Submodule R M) = ⊤
  · rw [grade_of_smul_eq_top I M hI]
    have hv := (koszul_acyclic_of_smul_eq_top M a (ha.symm ▸ hI)).2
    apply le_antisymm ?_ le_top
    apply le_iInf
    intro i
    apply le_iInf
    intro hi
    exact False.elim (not_nontrivial_iff_subsingleton.mpr (hv i) hi)
  · obtain ⟨n, hg, hn, hv⟩ := exists_first_koszul_cohomology I M a ha hI
    rw [hg]
    apply Eq.symm
    apply firstDegree_eq_nat
    · exact (koszulCohomologyIso M a n).toLinearEquiv.toEquiv.nontrivial_congr.mp hn
    · intro i hi
      exact (koszulCohomologyIso M a i).toLinearEquiv.toEquiv.subsingleton_congr.mp (hv i hi)

theorem grade_le_generating_length [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R) (ha : listIdeal a = I)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) : grade I M ≤ a.length := by
  obtain ⟨n, hg, hn, _⟩ := exists_first_koszul_cohomology I M a ha hI
  have hnt := (koszulCohomologyIso M a n).toLinearEquiv.toEquiv.nontrivial_congr.mp hn
  have hle : n ≤ a.length := by
    by_contra h
    exact not_nontrivial_iff_subsingleton.mpr
      (SelfDuality.cohomology_vanish M a n (by omega)) hnt
  rw [hg]
  exact_mod_cast hle

theorem koszulThreshold_independent [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a b : List R) (hab : listIdeal a = listIdeal b) :
    koszulCohomologyThreshold M a = koszulCohomologyThreshold M b := by
  rw [← grade_eq_koszulCohomologyThreshold (listIdeal b) M a hab,
    grade_eq_koszulCohomologyThreshold (listIdeal b) M b rfl]

lemma koszul_homology_vanish_above (M : Type u) [AddCommGroup M] [Module R M]
    (a : List R) (q : ℕ) (hq : a.length < q) : Subsingleton (homology M a q) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact HomologicalComplex.ExactAt.isZero_homology
    (HomologicalComplex.ExactAt.of_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr (coefficientComplex_vanish M a q hq)))

/-- Reversing a finite Koszul complex converts the first nonzero cohomology
degree to its length minus the last nonzero homology degree. -/
theorem koszulThreshold_selfDuality
    (M : Type u) [AddCommGroup M] [Module R M] (a : List R) :
    koszulCohomologyThreshold M a = koszulHomologyThreshold M a := by
  classical
  by_cases he : ∃ j : ℕ, Nontrivial (homology M a j)
  · have hc : ∃ i : ℕ, Nontrivial (SelfDuality.cohomology M a i) := by
      obtain ⟨j, hj⟩ := he
      have hjle : j ≤ a.length := by
        by_contra h
        exact not_nontrivial_iff_subsingleton.mpr
          (koszul_homology_vanish_above M a j (by omega)) hj
      exact ⟨a.length-j,
        (SelfDuality.cohomologyDualityEquiv M a (a.length-j) j (by omega)).toEquiv.nontrivial_congr.mpr hj⟩
    let n := Nat.find hc
    have hn : Nontrivial (SelfDuality.cohomology M a n) := Nat.find_spec hc
    have hle : n ≤ a.length := by
      by_contra h
      exact not_nontrivial_iff_subsingleton.mpr
        (SelfDuality.cohomology_vanish M a n (by omega)) hn
    have hfirst : koszulCohomologyThreshold M a = n :=
      firstDegree_eq_nat _ n hn (fun i hi =>
        not_nontrivial_iff_subsingleton.mp (Nat.find_min hc hi))
    have hlast : (⨆ (j : ℕ) (_ : Nontrivial (homology M a j)), (j : ℕ∞)) =
        ((a.length-n : ℕ) : ℕ∞) := by
      apply le_antisymm
      · apply iSup_le
        intro j
        apply iSup_le
        intro hj
        have hjle : j ≤ a.length := by
          by_contra h
          exact not_nontrivial_iff_subsingleton.mpr
            (koszul_homology_vanish_above M a j (by omega)) hj
        have hco : Nontrivial (SelfDuality.cohomology M a (a.length-j)) :=
          (SelfDuality.cohomologyDualityEquiv M a (a.length-j) j (by omega)).toEquiv.nontrivial_congr.mpr hj
        have hmin : n ≤ a.length-j := Nat.find_min' hc hco
        exact_mod_cast (show j ≤ a.length-n by omega)
      · have hj : Nontrivial (homology M a (a.length-n)) :=
          (SelfDuality.cohomologyDualityEquiv M a n (a.length-n) (by omega)).toEquiv.nontrivial_congr.mp hn
        exact le_iSup_of_le (a.length-n) (le_iSup_of_le hj le_rfl)
    rw [hfirst, koszulHomologyThreshold, ite_eq_left he, hlast, ← ENat.natCast_sub]
    congr 1
    omega
  · have hv (q : ℕ) : Subsingleton (SelfDuality.cohomology M a q) := by
      by_cases hq : q ≤ a.length
      · have hz : Subsingleton (homology M a (a.length-q)) :=
          not_nontrivial_iff_subsingleton.mp (fun h => he ⟨_, h⟩)
        exact (SelfDuality.cohomologyDualityEquiv M a q (a.length-q) (by omega)).toEquiv.subsingleton_congr.mpr hz
      · exact SelfDuality.cohomology_vanish M a q (by omega)
    rw [koszulHomologyThreshold, ite_eq_right he]
    apply top_unique
    apply le_iInf
    intro i
    apply le_iInf
    intro hi
    exact False.elim (not_nontrivial_iff_subsingleton.mpr (hv i) hi)

theorem grade_eq_koszulHomologyThreshold [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (a : List R) (ha : listIdeal a = I) :
    grade I M = koszulHomologyThreshold M a := by
  rw [grade_eq_koszulCohomologyThreshold I M a ha, koszulThreshold_selfDuality]

/-- The infinite branch of DP-09, including proper ideals with IM=M. -/
theorem koszulThreshold_of_smul_eq_top (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (a : List R)
    (hI : listIdeal a • (⊤ : Submodule R M) = ⊤) :
    koszulCohomologyThreshold M a = ⊤ ∧ koszulHomologyThreshold M a = ⊤ := by
  have hv := (koszul_acyclic_of_smul_eq_top M a hI).2
  have h : koszulCohomologyThreshold M a = ⊤ := by
    apply top_unique
    apply le_iInf
    intro i
    apply le_iInf
    intro hi
    exact False.elim (not_nontrivial_iff_subsingleton.mpr (hv i) hi)
  exact ⟨h, (koszulThreshold_selfDuality M a).symm.trans h⟩

/-- The zero module has infinite thresholds for every list, including []. -/
theorem koszulThreshold_subsingleton (M : Type u) [AddCommGroup M]
    [Module R M] [Subsingleton M] (a : List R) :
    koszulCohomologyThreshold M a = ⊤ ∧ koszulHomologyThreshold M a = ⊤ := by
  exact koszulThreshold_of_smul_eq_top M a (Subsingleton.elim _ _)

/-- In length zero a nonzero coefficient module first occurs in degree zero. -/
theorem koszulThreshold_empty (M : Type u) [AddCommGroup M]
    [Module R M] [Nontrivial M] :
    koszulCohomologyThreshold M ([] : List R) = 0 ∧
      koszulHomologyThreshold M ([] : List R) = 0 := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hn := koszul_cohomology_zero_nontrivial M ([] : List R) m hm (by
    intro r hr
    have hr0 : r = 0 := by simpa [listIdeal] using hr
    simp [hr0])
  have h : koszulCohomologyThreshold M ([] : List R) = 0 := by
    apply firstDegree_eq_nat _ 0
    · exact (koszulCohomologyIso M [] 0).toLinearEquiv.toEquiv.nontrivial_congr.mp hn
    · simp
  exact ⟨h, (koszulThreshold_selfDuality M []).symm.trans h⟩

/-- The unit ideal gives infinite thresholds; the zero ring is allowed. -/
theorem koszulThreshold_unitIdeal (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (a : List R) (ha : listIdeal a = ⊤) :
    koszulCohomologyThreshold M a = ⊤ ∧ koszulHomologyThreshold M a = ⊤ := by
  apply koszulThreshold_of_smul_eq_top
  simp [ha]

end AdvCommAlg.Depth
