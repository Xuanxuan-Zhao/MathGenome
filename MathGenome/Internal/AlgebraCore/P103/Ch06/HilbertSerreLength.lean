import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.P103.Ch06.GradedInterfaces
import MathGenome.Internal.AlgebraCore.P103.Ch03.HopkinsLevitzki
import MathGenome.Internal.AlgebraCore.P103.Ch05.NoetherianFiniteness
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace P103.HilbertSerreLength
open P103.Graded Polynomial

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem hilbertFunction_eq_zero_of_piece_eq_bot (G : NonnegativeGrading A)
    (U : ModuleGrading G M) (j : ℤ) (hj : U.piece j = ⊥) :
    hilbertFunction G U j = 0 := by
  have hsub : Subsingleton (component G U j) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : M) = 0 := by simpa [component, hj] using x.2
    have hy : (y : M) = 0 := by simpa [component, hj] using y.2
    exact hx.trans hy.symm
  simp [hilbertFunction]

theorem bounded_below : Specs.P103.HilbertSerreLength.boundedBelowType := by
  intro A M _ _ _ G U _
  obtain ⟨b, hb⟩ := P103.Graded.bounded_below G U
  exact ⟨b, fun j hj => hilbertFunction_eq_zero_of_piece_eq_bot G U j (hb j hj)⟩

theorem zero : Specs.P103.HilbertSerreLength.zeroType := by
  intro A M _ _ _ G U _
  funext j
  simp [hilbertFunction]

/-- Projection of multiplication by a homogeneous scalar. -/
theorem decompose_homogeneous_smul (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (i j : ℤ) (a : G.piece i) (m : M) :
    (DirectSum.decompose U.piece ((a : A) • m) j : M) =
      (a : A) • (DirectSum.decompose U.piece m (j - i) : M) := by
  classical
  induction m using DirectSum.Decomposition.inductionOn U.piece with
  | zero => simp
  | add m n hm hn =>
    simp only [smul_add, DirectSum.decompose_add]
    change (DirectSum.decompose U.piece ((a : A) • m) j : M) +
      (DirectSum.decompose U.piece ((a : A) • n) j : M) =
      (a : A) • ((DirectSum.decompose U.piece m (j - i) : M) +
        (DirectSum.decompose U.piece n (j - i) : M))
    rw [smul_add, hm, hn]
  | @homogeneous k m =>
    have ha : (a : A) • (m : M) ∈ U.piece (i + k) :=
      SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) a.2 m.2
    by_cases hk : i + k = j
    · have hk' : k = j - i := by omega
      rw [hk] at ha
      rw [DirectSum.decompose_of_mem_same U.piece ha,
        DirectSum.decompose_of_mem_same U.piece (hk' ▸ m.2)]
    · rw [DirectSum.decompose_of_mem_ne U.piece ha hk,
        DirectSum.decompose_of_mem_ne U.piece m.2 (by omega), smul_zero]

/-- On the bottom nonzero degree of a truncation, only the degree-zero
component of the scalar acts. -/
theorem decompose_smul_on_truncation (G : NonnegativeGrading A)
    (U : ModuleGrading G M) (j : ℤ) (a : A) (m : M)
    (hm : m ∈ P103.Graded.supportedAbove U j) :
    (DirectSum.decompose U.piece (a • m) j : M) =
      (DirectSum.decompose G.piece a 0 : A) •
        (DirectSum.decompose U.piece m j : M) := by
  classical
  induction a using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | add a b ha hb =>
    simp only [add_smul, DirectSum.decompose_add]
    change (DirectSum.decompose U.piece (a • m) j : M) +
      (DirectSum.decompose U.piece (b • m) j : M) =
      ((DirectSum.decompose G.piece a 0 : A) +
        (DirectSum.decompose G.piece b 0 : A)) •
          (DirectSum.decompose U.piece m j : M)
    rw [add_smul, ha, hb]
  | @homogeneous i a =>
    by_cases hi : i < 0
    · have hz : (a : A) = 0 := by simpa [G.negative i hi] using a.2
      simp [hz]
    · by_cases hi0 : i = 0
      · subst i
        rw [DirectSum.decompose_of_mem_same G.piece a.2,
          decompose_homogeneous_smul G U, sub_zero]
      · rw [DirectSum.decompose_of_mem_ne G.piece a.2 hi0, zero_smul,
          decompose_homogeneous_smul G U, hm (j - i) (by omega), smul_zero]

/-- A Noetherian module over a nonnegative graded algebra has finite
homogeneous pieces over A₀. This does not require standardness. -/
theorem component_finite_of_noetherian (G : NonnegativeGrading A)
    (U : ModuleGrading G M) [IsNoetherian A M] (j : ℤ) :
    Module.Finite (Base G) (component G U j) := by
  classical
  let T := P103.Graded.aboveSubmodule G U j
  let proj : T → component G U j :=
    fun m => ⟨(DirectSum.decompose U.piece (m : M) j : M),
      (DirectSum.decompose U.piece (m : M) j).2⟩
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := A) (M := T))
  have hspan : Submodule.span (Base G) (s.image proj : Set (component G U j)) = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : M) ∈ T :=
      P103.Graded.homogeneous_supportedAbove U x.2 le_rfl
    let xT : T := ⟨x, hx⟩
    have hgen : ∀ m : T, proj m ∈
        Submodule.span (Base G) (s.image proj : Set (component G U j)) := by
      intro m
      have hm : m ∈ Submodule.span A (s : Set T) := by rw [hs]; trivial
      induction hm using Submodule.span_induction with
      | mem y hy =>
        exact Submodule.subset_span (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      | zero =>
        have hz : proj 0 = 0 := by apply Subtype.ext; simp [proj]
        rw [hz]
        exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
        convert Submodule.add_mem _ hy hz using 1
        apply Subtype.ext
        simp [proj, DirectSum.decompose_add]
      | smul a y _ hy =>
        convert Submodule.smul_mem _ (DirectSum.decompose G.piece a 0) hy using 1
        apply Subtype.ext
        exact decompose_smul_on_truncation G U j a y y.2
    have hproj : proj xT = x := by
      apply Subtype.ext
      exact DirectSum.decompose_of_mem_same U.piece x.2
    rw [← hproj]
    exact hgen xT
  exact Module.Finite.of_fg_top ⟨s.image proj, hspan⟩

/-- Standardness and an Artinian degree-zero ring supply the needed
Noetherian hypotheses without a nontriviality assumption. -/
theorem finite_length : Specs.P103.HilbertSerreLength.finiteLengthType := by
  intro A M _ _ _ G U _ _ hstandard j
  let : IsNoetherianRing (Base G) := P103.Ch03.HopkinsLevitzki.left_noetherian (Base G)
  obtain ⟨s, _, hs⟩ := hstandard
  let : Algebra.FiniteType (Base G) A := ⟨⟨s, hs⟩⟩
  let : IsNoetherianRing A :=
    P103.Ch05.NoetherianFiniteness.finiteType_noetherian (Base G) A
  have : IsNoetherian A M := inferInstance
  have : Module.Finite (Base G) (component G U j) :=
    component_finite_of_noetherian G U j
  have hn : IsNoetherian (Base G) (component G U j) :=
    isNoetherian_of_isNoetherianRing_of_finite (Base G) (component G U j)
  have ha : IsArtinian (Base G) (component G U j) :=
    isArtinian_of_fg_of_artinian' (R := Base G) (M := component G U j)
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨hn, ha⟩

/-- Finite base modules have only finitely many nonzero homogeneous pieces. -/
theorem bounded_above_of_finite_base (G : NonnegativeGrading A)
    (U : ModuleGrading G M) [Module.Finite (Base G) M] :
    ∃ b : ℤ, ∀ j ≥ b, U.piece j = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Base G) (M := M)
  let degrees := s.biUnion (fun m => (DirectSum.decompose U.piece m).support)
  obtain ⟨b, hb⟩ := degrees.finite_toSet.bddAbove
  let T : Submodule (Base G) M :=
    { carrier := {m | ∀ j ≥ b + 1, (DirectSum.decompose U.piece m j : M) = 0}
      zero_mem' := by simp
      add_mem' := by
        intro m n hm hn j hj
        rw [DirectSum.decompose_add]
        change (DirectSum.decompose U.piece m j : M) +
          (DirectSum.decompose U.piece n j : M) = 0
        rw [hm j hj, hn j hj, add_zero]
      smul_mem' := by
        intro a m hm j hj
        change (DirectSum.decompose U.piece ((a : A) • m) j : M) = 0
        rw [decompose_homogeneous_smul G U 0 j a, sub_zero, hm j hj, smul_zero] }
  have hT : T = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro m hm j hj
    have hnot : j ∉ (DirectSum.decompose U.piece m).support := by
      intro hjmem
      have hle := hb (Finset.mem_biUnion.mpr ⟨m, hm, hjmem⟩)
      omega
    have hz := DFinsupp.notMem_support_iff.mp hnot
    exact congrArg (fun x : U.piece j => (x : M)) hz
  refine ⟨b + 1, fun j hj => le_antisymm ?_ bot_le⟩
  intro m hm
  have hmT : m ∈ T := by rw [hT]; trivial
  have hz := hmT j hj
  rwa [DirectSum.decompose_of_mem_same U.piece hm] at hz

/-- When there are no degree-one algebra generators, finite generation over
A is already finite generation over the degree-zero ring. -/
theorem finite_base_of_no_generators (G : NonnegativeGrading A)
    [Module.Finite A M] (h : Algebra.adjoin (Base G) (∅ : Set A) = ⊤) :
    Module.Finite (Base G) M := by
  have hs : Function.Surjective (algebraMap (Base G) A) := by
    intro a
    have ha : a ∈ (⊥ : Subalgebra (Base G) A) := by
      rw [← Algebra.adjoin_empty, h]
      trivial
    exact Algebra.mem_bot.mp ha
  classical
  obtain ⟨s, hsA⟩ := Module.Finite.fg_top (R := A) (M := M)
  apply Module.Finite.of_fg_top
  refine ⟨s, top_unique ?_⟩
  intro m htop
  clear htop
  have hm : m ∈ Submodule.span A (s : Set M) := by rw [hsA]; trivial
  induction hm using Submodule.span_induction with
  | mem m hm => exact Submodule.subset_span hm
  | zero => exact Submodule.zero_mem _
  | add m n _ _ hm hn => exact Submodule.add_mem _ hm hn
  | smul a m _ hm =>
    obtain ⟨b, hb⟩ := hs a
    have hsm := Submodule.smul_mem (Submodule.span (Base G) (s : Set M)) b hm
    change ((algebraMap (Base G) A b) • m) ∈ _ at hsm
    rwa [hb] at hsm

/-- Finite support gives a Laurent polynomial with denominator exponent zero. -/
theorem rationalPresentation_of_finite_support (h : ℤ → ℤ) (b c : ℤ)
    (hb : ∀ j < b, h j = 0) (hc : ∀ j ≥ c, h j = 0) :
    ∃ p : Polynomial ℤ, RationalPresentation h b p 0 := by
  let S := shiftedSeries h b
  let n := (c - b).toNat
  refine ⟨PowerSeries.trunc n S, hb, ?_⟩
  simp only [pow_zero, mul_one]
  apply PowerSeries.ext
  intro i
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hi : i < n
  · simp [hi, S]
  · simp only [hi, ite_false]
    simp only [shiftedSeries, PowerSeries.coeff_mk]
    exact hc _ (by dsimp [n] at hi; omega)

/-- The empty-generator boundary case of Hilbert–Serre. -/
theorem rational_no_generators (G : NonnegativeGrading A) (U : ModuleGrading G M)
    [Module.Finite A M] (h : Algebra.adjoin (Base G) (∅ : Set A) = ⊤) :
    ∃ (b : ℤ) (p : Polynomial ℤ), RationalPresentation (hilbertFunction G U) b p 0 := by
  have := finite_base_of_no_generators (M := M) G h
  obtain ⟨b, hb⟩ := bounded_below G U
  obtain ⟨c, hc⟩ := bounded_above_of_finite_base G U
  obtain ⟨p, hp⟩ := rationalPresentation_of_finite_support (hilbertFunction G U) b c hb
    (fun j hj => hilbertFunction_eq_zero_of_piece_eq_bot G U j (hc j hj))
  exact ⟨b, p, hp⟩

theorem zero_base (G : NonnegativeGrading A) (U : ModuleGrading G M)
    [Subsingleton (Base G)] : hilbertFunction G U = 0 := by
  have : Subsingleton A := Algebra.subsingleton (Base G) A
  have : Subsingleton M := Module.subsingleton A M
  exact zero G U

/-- Pass from the denominator identity over Z to the corresponding rational
power-series coefficient formula. -/
theorem rationalPresentation_coeff (h : ℤ → ℤ) (b : ℤ) (p : Polynomial ℤ) (e : ℕ)
    (hp : RationalPresentation h b p e) (n : ℕ) :
    (h (b + n) : ℚ) = PowerSeries.coeff n
      ((p.map (Int.castRingHom ℚ) : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ e : PowerSeries ℚ)) := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hp.2
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X,
    ← Polynomial.polynomial_map_coe] at hmap
  have hinv : (1 - PowerSeries.X : PowerSeries ℚ) ^ e *
      (PowerSeries.invOneSubPow ℚ e : PowerSeries ℚ) = 1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℚ e).inv_val
  have hs : PowerSeries.map (Int.castRingHom ℚ) (shiftedSeries h b) =
      (p.map (Int.castRingHom ℚ) : PowerSeries ℚ) * PowerSeries.invOneSubPow ℚ e := by
    rw [← hmap, mul_assoc, hinv, mul_one]
  have hc := congrArg (PowerSeries.coeff n) hs
  simpa [shiftedSeries] using hc

/-- Polynomial in the original integer degree after undoing the shift b. -/
noncomputable def presentationPolynomial (b : ℤ) (p : Polynomial ℤ) (e : ℕ) :
    Polynomial ℚ :=
  (hilbertPoly (p.map (Int.castRingHom ℚ)) e).comp (X - C (b : ℚ))

theorem rationalPresentation_eventually (h : ℤ → ℤ) (b : ℤ) (p : Polynomial ℤ) (e : ℕ)
    (hp : RationalPresentation h b p e) :
    EventuallyPolynomial h (presentationPolynomial b p e) := by
  let P := p.map (Int.castRingHom ℚ)
  refine ⟨b + P.natDegree + 1, ?_⟩
  intro j hj
  have hb : 0 ≤ j - b := by omega
  have hn : P.natDegree < (j - b).toNat := by omega
  have hjn : b + ((j - b).toNat : ℤ) = j := by omega
  have hcoeff := rationalPresentation_coeff h b p e hp (j - b).toNat
  rw [hjn] at hcoeff
  rw [hcoeff, Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval e hn]
  simp only [presentationPolynomial, eval_comp, eval_sub, eval_X, eval_C]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg hb

/-- Top coefficient of the unreduced Hilbert polynomial. -/
theorem hilbertPoly_coeff_pred (P : Polynomial ℚ) (d : ℕ) :
    (hilbertPoly P (d + 1)).coeff d = P.eval 1 / (d.factorial : ℚ) := by
  rw [hilbertPoly_succ]
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_preHilbertPoly_self]
  rw [← Finset.sum_mul]
  congr 1
  simp [Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- Degree and leading coefficient when the denominator has no cancellation. -/
theorem presentationPolynomial_degree (b : ℤ) (p : Polynomial ℤ) (e : ℕ)
    (he : 0 < e) (hp : p.eval 1 ≠ 0) :
    (presentationPolynomial b p e) ≠ 0 ∧
    (presentationPolynomial b p e).natDegree = e - 1 ∧
    (presentationPolynomial b p e).leadingCoeff =
      ((p.eval 1 : ℤ) : ℚ) / ((e - 1).factorial : ℚ) := by
  let P := p.map (Int.castRingHom ℚ)
  have hP : P.eval 1 = ((p.eval 1 : ℤ) : ℚ) := by
    simp [P, Polynomial.eval_map]
  have hP1 : P.eval 1 ≠ 0 := by rw [hP]; exact_mod_cast hp
  have hP0 : P ≠ 0 := by intro hz; simp [hz] at hP1
  have hr : P.rootMultiplicity 1 = 0 :=
    Polynomial.rootMultiplicity_eq_zero hP1
  have hd : (hilbertPoly P e).natDegree = e - 1 := by
    simpa [hr] using
      Polynomial.natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt hP0
        (show P.rootMultiplicity 1 < e by omega)
  have hc : (hilbertPoly P e).coeff (e - 1) =
      P.eval 1 / ((e - 1).factorial : ℚ) := by
    simpa only [Nat.sub_add_cancel he] using hilbertPoly_coeff_pred P (e - 1)
  have hlc : (hilbertPoly P e).leadingCoeff =
      P.eval 1 / ((e - 1).factorial : ℚ) := by
    rw [Polynomial.leadingCoeff, hd, hc]
  have hq0 : hilbertPoly P e ≠ 0 := by
    intro hz
    have hne : P.eval 1 / ((e - 1).factorial : ℚ) ≠ 0 :=
      div_ne_zero hP1 (by exact_mod_cast Nat.factorial_ne_zero (e - 1))
    exact hne (hlc.symm.trans (by simp [hz]))
  change ((hilbertPoly P e).comp (X - C (b : ℚ))) ≠ 0 ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_eq_add_neg, ← C_neg]
    exact Polynomial.comp_X_add_C_ne_zero_iff.mpr hq0
  · simp only [presentationPolynomial, natDegree_comp, natDegree_X_sub_C, mul_one]
    exact hd
  · rw [presentationPolynomial, leadingCoeff_comp (by rw [natDegree_X_sub_C]; decide), (monic_X_sub_C (b : ℚ)).leadingCoeff,
      one_pow, mul_one]
    exact hlc.trans (by rw [hP])

theorem coefficients : Specs.P103.HilbertSerreLength.coefficientTheoremType := by
  intro h b p e hp
  refine ⟨presentationPolynomial b p e, rationalPresentation_eventually h b p e hp, ?_, ?_⟩
  · intro he
    have hq : presentationPolynomial b p e = 0 := by
      simp [he, presentationPolynomial, Polynomial.hilbertPoly_zero_right]
    refine ⟨hq, ?_⟩
    obtain ⟨J, hJ⟩ := rationalPresentation_eventually h b p e hp
    refine ⟨J, fun j hj => ?_⟩
    have hz := hJ j hj
    rw [hq, Polynomial.eval_zero] at hz
    exact_mod_cast hz
  · exact presentationPolynomial_degree b p e

open DirectSum in
/-- A homogeneous submodule inherits the internal grading. -/
noncomputable def submoduleGrading (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (P : Submodule A M)
    (hP : ∀ j m, m ∈ P → (DirectSum.decompose U.piece m j : M) ∈ P) :
    ModuleGrading G P := by
  classical
  let V : ℤ → AddSubgroup P := fun j => (U.piece j).comap P.subtype.toAddMonoidHom
  let d : P →+ ⨁ j, V j :=
    { toFun := fun m =>
        ⟨fun j => ⟨⟨(decompose U.piece (m : M) j : M), hP j m m.2⟩,
          (decompose U.piece (m : M) j).2⟩,
         (decompose U.piece (m : M)).support'.map fun s =>
           ⟨s.1, fun j => (s.2 j).imp_right fun hz => by
             apply Subtype.ext; apply Subtype.ext
             exact congrArg (fun z : U.piece j => (z : M)) hz⟩⟩
      map_zero' := by apply DFinsupp.ext; intro j; apply Subtype.ext; apply Subtype.ext; simp
      map_add' := by intro m n; apply DFinsupp.ext; intro j; apply Subtype.ext; apply Subtype.ext; simp }
  have hd (m : P) (j : ℤ) : ((d m j : P) : M) = (decompose U.piece (m : M) j : M) := rfl
  have hr : d.comp (DirectSum.coeAddMonoidHom V) = .id _ := by
    apply DirectSum.addHom_ext
    intro j m
    apply DFinsupp.ext
    intro k
    apply Subtype.ext; apply Subtype.ext
    change ((d (DirectSum.coeAddMonoidHom V (DirectSum.of _ j m)) k : P) : M) = _
    rw [DirectSum.coeAddMonoidHom_of, hd]
    rw [decompose_of_mem U.piece (show ((m : P) : M) ∈ U.piece j from m.2)]
    simp only [AddMonoidHom.id_apply, DirectSum.coe_of_apply]
    split_ifs <;> rfl
  have hl : (DirectSum.coeAddMonoidHom V).comp d = .id _ := by
    apply AddMonoidHom.ext
    intro m
    apply Subtype.ext
    let f : (⨁ j, V j) →+ ⨁ j, U.piece j := DirectSum.map fun j =>
      { toFun := fun v : V j => (⟨((v : P) : M), v.2⟩ : U.piece j)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hc : P.subtype.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom V) =
        (DirectSum.coeAddMonoidHom U.piece).comp f := by
      apply DirectSum.addHom_ext
      intro j m
      simp [f]
    have hf : f (d m) = decompose U.piece (m : M) := by
      apply DFinsupp.ext
      intro j
      rfl
    have hc' := DFunLike.congr_fun hc (d m)
    change ((DirectSum.coeAddMonoidHom V (d m) : P) : M) = (m : M)
    exact hc'.trans ((congrArg (DirectSum.coeAddMonoidHom U.piece) hf).trans
      ((decompose U.piece).left_inv m))
  exact
    { piece := V
      decomposition := DirectSum.Decomposition.ofAddHom (ℳ := V) d hl hr
      compatible := ⟨fun i j a m ha hm =>
        SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) ha hm⟩ }

open DirectSum in
/-- A quotient by a homogeneous submodule inherits the internal grading. -/
noncomputable def quotientGrading (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (P : Submodule A M)
    (hP : ∀ j m, m ∈ P → (DirectSum.decompose U.piece m j : M) ∈ P) :
    ModuleGrading G (M ⧸ P) := by
  classical
  let V : ℤ → AddSubgroup (M ⧸ P) := fun j => (U.piece j).map P.mkQ.toAddMonoidHom
  let f : (⨁ j, U.piece j) →+ ⨁ j, V j :=
    DirectSum.map fun j =>
      { toFun := fun m => ⟨P.mkQ m, ⟨m, m.2, rfl⟩⟩
        map_zero' := by apply Subtype.ext; exact map_zero _
        map_add' := by intro _ _; apply Subtype.ext; exact map_add _ _ _ }
  let d₀ := f.comp (decomposeAddEquiv U.piece).toAddMonoidHom
  have hz : P.toAddSubgroup ≤ d₀.ker := by
    intro m hm
    change d₀ m = 0
    apply DFinsupp.ext
    intro j
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hP j m hm)
  let d : (M ⧸ P) →+ ⨁ j, V j := QuotientAddGroup.lift P.toAddSubgroup d₀ hz
  have hd (m : M) : d (P.mkQ m) = f (decompose U.piece m) := rfl
  have hl : (DirectSum.coeAddMonoidHom V).comp d = .id _ := by
    apply AddMonoidHom.ext
    intro m
    obtain ⟨m, rfl⟩ := P.mkQ_surjective m
    change DirectSum.coeAddMonoidHom V (d (P.mkQ m)) = P.mkQ m
    rw [hd]
    have hc : (DirectSum.coeAddMonoidHom V).comp f =
        P.mkQ.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom U.piece) := by
      apply DirectSum.addHom_ext
      intro j m
      simp [f]
    exact (DFunLike.congr_fun hc (decompose U.piece m)).trans
      (congrArg P.mkQ ((decompose U.piece).left_inv m))
  have hr : d.comp (DirectSum.coeAddMonoidHom V) = .id _ := by
    apply DirectSum.addHom_ext
    intro j m
    obtain ⟨n, hn, he⟩ := m.2
    have hm : m = ⟨P.mkQ n, ⟨n, hn, rfl⟩⟩ := Subtype.ext he.symm
    subst m
    change d (DirectSum.coeAddMonoidHom V (DirectSum.of _ j _)) = _
    rw [DirectSum.coeAddMonoidHom_of, hd, decompose_of_mem U.piece hn]
    simp [f]
  exact
    { piece := V
      decomposition := DirectSum.Decomposition.ofAddHom (ℳ := V) d hl hr
      compatible := by
        constructor
        intro i j a m ha hm
        obtain ⟨n, hn, rfl⟩ := hm
        exact ⟨a • n, SetLike.GradedSMul.smul_mem ha hn, P.mkQ.map_smul a n⟩ }

/-- Multiplication by a scalar, as an endomorphism over the commutative algebra. -/
def scalarMap (x : A) : M →ₗ[A] M where
  toFun := fun m => x • m
  map_add' := smul_add x
  map_smul' := fun a m => smul_comm x a m

/-- The chosen scalar annihilates its multiplication kernel. -/
theorem scalarMap_ker_smul_zero (x : A)
    (m : LinearMap.ker (scalarMap (M := M) x)) : x • m = 0 := by
  apply Subtype.ext
  exact m.2

/-- The chosen scalar annihilates its multiplication cokernel. -/
theorem scalarMap_cokernel_smul_zero (x : A)
    (m : M ⧸ LinearMap.range (scalarMap (M := M) x)) : x • m = 0 := by
  let I := LinearMap.range (scalarMap (M := M) x)
  obtain ⟨n, rfl⟩ := I.mkQ_surjective m
  change I.mkQ (x • n) = 0
  exact (Submodule.Quotient.mk_eq_zero I).mpr ⟨n, rfl⟩

/-- An annihilator of the module also annihilates a multiplication kernel. -/
theorem scalarMap_ker_smul_zero_of_annihilates (x y : A)
    (hy : ∀ m : M, y • m = 0)
    (m : LinearMap.ker (scalarMap (M := M) x)) : y • m = 0 := by
  apply Subtype.ext
  exact hy m

/-- An annihilator of the module also annihilates a multiplication cokernel. -/
theorem scalarMap_cokernel_smul_zero_of_annihilates (x y : A)
    (hy : ∀ m : M, y • m = 0)
    (m : M ⧸ LinearMap.range (scalarMap (M := M) x)) : y • m = 0 := by
  let I := LinearMap.range (scalarMap (M := M) x)
  obtain ⟨n, rfl⟩ := I.mkQ_surjective m
  change I.mkQ (y • n) = 0
  rw [hy n, map_zero]

theorem scalarMap_ker_homogeneous (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (x : A) (hx : x ∈ G.piece 1) :
    ∀ j m, m ∈ LinearMap.ker (scalarMap (M := M) x) →
      (DirectSum.decompose U.piece m j : M) ∈ LinearMap.ker (scalarMap x) := by
  intro j m hm
  change x • (DirectSum.decompose U.piece m j : M) = 0
  have he := decompose_homogeneous_smul G U 1 (1 + j) ⟨x, hx⟩ m
  have hz : x • m = 0 := hm
  change (DirectSum.decompose U.piece (x • m) (1 + j) : M) =
    x • (DirectSum.decompose U.piece m (1 + j - 1) : M) at he
  rw [show (1 : ℤ) + j - 1 = j by omega, hz] at he
  simpa using he.symm

theorem scalarMap_range_homogeneous (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (x : A) (hx : x ∈ G.piece 1) :
    ∀ j m, m ∈ LinearMap.range (scalarMap (M := M) x) →
      (DirectSum.decompose U.piece m j : M) ∈ LinearMap.range (scalarMap x) := by
  rintro j m ⟨n, rfl⟩
  refine ⟨(DirectSum.decompose U.piece n (j - 1) : M), ?_⟩
  exact (decompose_homogeneous_smul G U 1 j ⟨x, hx⟩ n).symm

noncomputable def kernelGrading (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (x : A) (hx : x ∈ G.piece 1) :
    ModuleGrading G (LinearMap.ker (scalarMap (M := M) x)) :=
  submoduleGrading G U _ (scalarMap_ker_homogeneous G U x hx)

noncomputable def cokernelGrading (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (x : A) (hx : x ∈ G.piece 1) :
    ModuleGrading G (M ⧸ LinearMap.range (scalarMap (M := M) x)) :=
  quotientGrading G U _ (scalarMap_range_homogeneous G U x hx)

/-- The four-term multiplication sequence is exact in each integer degree.
The kernel and cokernel carry their inherited gradings. -/
theorem multiplication_length_recurrence (G : NonnegativeGrading A)
    (U : ModuleGrading G M) [IsArtinianRing (Base G)] [Module.Finite A M]
    (hs : Specs.P103.Graded.standardValue G) (x : A) (hx : x ∈ G.piece 1) (j : ℤ) :
    hilbertFunction G U j + hilbertFunction G (kernelGrading G U x hx) (j - 1) =
      hilbertFunction G U (j - 1) + hilbertFunction G (cokernelGrading G U x hx) j := by
  let : CommRing (Base G) := inferInstance
  let (i : ℤ) : AddCommGroup (component G U i) := Submodule.addCommGroup _
  let K := LinearMap.ker (scalarMap (M := M) x)
  let I := LinearMap.range (scalarMap (M := M) x)
  let UK := kernelGrading G U x hx
  let UC := cokernelGrading G U x hx
  let f : component G U (j - 1) →ₗ[Base G] component G U j :=
    { toFun := fun m => ⟨x • (m : M), by
        have h := SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) hx m.2
        change x • (m : M) ∈ U.piece j
        simpa using h⟩
      map_add' := by intro _ _; apply Subtype.ext; exact smul_add _ _ _
      map_smul' := by
        intro b m
        apply Subtype.ext
        change x • ((b : A) • (m : M)) = (b : A) • (x • (m : M))
        exact smul_comm _ _ _ }
  let k : component G UK (j - 1) →ₗ[Base G] component G U (j - 1) :=
    { toFun := fun m => ⟨((m : K) : M), m.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q : component G U j →ₗ[Base G] component G UC j :=
    { toFun := fun m => ⟨I.mkQ m, ⟨m, m.2, rfl⟩⟩
      map_add' := by intro _ _; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro b m; apply Subtype.ext; exact I.mkQ.map_smul (b : A) m }
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun m : component G U (j - 1) => (m : M)) hab
  have hq : Function.Surjective q := by
    intro c
    obtain ⟨m, hm, he⟩ := c.2
    exact ⟨⟨m, hm⟩, Subtype.ext he⟩
  have hleft : Function.Exact k f.rangeRestrict := by
    intro m
    constructor
    · intro hm
      have hz : x • (m : M) = 0 :=
        congrArg (fun z : LinearMap.range f => ((z : component G U j) : M)) hm
      exact ⟨⟨⟨m, hz⟩, m.2⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      apply Subtype.ext; apply Subtype.ext
      exact (a : K).2
  have hright : Function.Exact (LinearMap.range f).subtype q := by
    intro m
    constructor
    · intro hm
      have hz : I.mkQ (m : M) = 0 := congrArg (fun c : component G UC j => (c : M ⧸ I)) hm
      obtain ⟨n, hn⟩ := (Submodule.Quotient.mk_eq_zero I).mp hz
      have he := decompose_homogeneous_smul G U 1 j ⟨x, hx⟩ n
      have hxn : x • n = (m : M) := hn
      have hfn : f ⟨(DirectSum.decompose U.piece n (j - 1) : M),
          (DirectSum.decompose U.piece n (j - 1)).2⟩ = m := by
        apply Subtype.ext
        exact he.symm.trans (by rw [hxn, DirectSum.decompose_of_mem_same U.piece m.2])
      exact ⟨⟨m, ⟨_, hfn⟩⟩, rfl⟩
    · rintro ⟨⟨n, a, rfl⟩, rfl⟩
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero I).mpr ⟨(a : M), rfl⟩
  have hlen₁ : Module.length (Base G) (component G U (j - 1)) =
      Module.length (Base G) (component G UK (j - 1)) +
        Module.length (Base G) (LinearMap.range f) := by
    apply Module.length_eq_add_of_exact k f.rangeRestrict hk f.surjective_rangeRestrict
    exact hleft
  have hlen₂ := Module.length_eq_add_of_exact (R := Base G) (LinearMap.range f).subtype q
    (Submodule.subtype_injective _) hq hright
  have hfinite : IsFiniteLength (Base G) (component G U (j - 1)) := finite_length G U hs _
  have hfinite' : IsFiniteLength (Base G) (component G U j) := finite_length G U hs _
  have hK := IsFiniteLength.of_injective (f := k) hfinite hk
  have hI := IsFiniteLength.of_surjective (f := f.rangeRestrict) hfinite f.surjective_rangeRestrict
  have hC := IsFiniteLength.of_surjective (f := q) hfinite' hq
  have hn₁ := congrArg ENat.toNat hlen₁
  have hn₂ := congrArg ENat.toNat hlen₂
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hK)
    (Module.length_ne_top_iff.mpr hI)] at hn₁
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hI)
    (Module.length_ne_top_iff.mpr hC)] at hn₂
  unfold hilbertFunction
  change ((Module.length (Base G) (component G U j)).toNat : ℤ) +
    ((Module.length (Base G) (component G UK (j - 1))).toNat : ℤ) =
    ((Module.length (Base G) (component G U (j - 1))).toNat : ℤ) +
    ((Module.length (Base G) (component G UC j)).toNat : ℤ)
  omega

/-- If the algebra generators act by zero, finite generation descends to A₀. -/
theorem finite_base_of_generators_killed (G : NonnegativeGrading A)
    [Module.Finite A M] (s : Finset A)
    (hs : Algebra.adjoin (Base G) (s : Set A) = ⊤)
    (hz : ∀ x ∈ s, ∀ m : M, x • m = 0) : Module.Finite (Base G) M := by
  classical
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := A) (M := M)
  let T := Submodule.span (Base G) (F : Set M)
  have hstable : ∀ a : A, ∀ m ∈ T, a • m ∈ T := by
    intro a
    have ha : a ∈ Algebra.adjoin (Base G) (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => intro m _; rw [hz x hx m]; exact T.zero_mem
    | algebraMap b => intro m hm; exact T.smul_mem b hm
    | add a b _ _ ha hb =>
      intro m hm; rw [add_smul]; exact T.add_mem (ha m hm) (hb m hm)
    | mul a b _ _ ha hb =>
      intro m hm; rw [mul_smul]; exact ha _ (hb m hm)
  apply Module.Finite.of_fg_top
  refine ⟨F, top_unique ?_⟩
  intro m htop
  clear htop
  have hm : m ∈ Submodule.span A (F : Set M) := by rw [hF]; trivial
  induction hm using Submodule.span_induction with
  | mem m hm => exact Submodule.subset_span hm
  | zero => exact T.zero_mem
  | add m n _ _ hm hn => exact T.add_mem hm hn
  | smul a m _ hm => exact hstable a m hm

/-- The coefficientwise four-term exact sequence gives the power series identity
at any common lower bound. -/
theorem shiftedSeries_recurrence (h k c : ℤ → ℤ) (b : ℤ)
    (hb : h (b - 1) = 0) (hbk : k (b - 1) = 0)
    (hr : ∀ j, h j + k (j - 1) = h (j - 1) + c j) :
    shiftedSeries h b * (1 - PowerSeries.X) =
      shiftedSeries c b - PowerSeries.X * shiftedSeries k b := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [mul_sub, mul_one, map_sub, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, sub_zero]
    have he := hr b
    simpa [shiftedSeries, hb, hbk] using he
  | succ n =>
    simp only [mul_sub, mul_one, map_sub, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, shiftedSeries]
    have he := hr (b + (n + 1 : ℕ))
    simp only [Nat.cast_add, Nat.cast_one] at he
    have hi : b + ((n : ℤ) + 1) - 1 = b + n := by omega
    rw [hi] at he
    simp only [Nat.cast_add, Nat.cast_one]
    omega

/-- Rationality is closed under the multiplication-sequence recurrence. -/
theorem rationalPresentation_of_recurrence (h k c : ℤ → ℤ) (b : ℤ)
    (hb : ∀ j < b, h j = 0) (pk pc : Polynomial ℤ) (ek ec : ℕ)
    (hk : RationalPresentation k b pk ek) (hc : RationalPresentation c b pc ec)
    (hr : ∀ j, h j + k (j - 1) = h (j - 1) + c j) :
    ∃ (p : Polynomial ℤ) (e : ℕ), RationalPresentation h b p e := by
  let D : PowerSeries ℤ := 1 - PowerSeries.X
  refine ⟨pc * (1 - X) ^ ek - X * pk * (1 - X) ^ ec, ek + ec + 1, hb, ?_⟩
  have he := shiftedSeries_recurrence h k c b (hb _ (by omega)) (hk.1 _ (by omega)) hr
  have hk' : shiftedSeries k b * D ^ ek = (pk : PowerSeries ℤ) := hk.2
  have hc' : shiftedSeries c b * D ^ ec = (pc : PowerSeries ℤ) := hc.2
  change shiftedSeries h b * D ^ (ek + ec + 1) = _
  rw [pow_succ, mul_comm (D ^ (ek + ec)), ← mul_assoc]
  change (shiftedSeries h b * (1 - PowerSeries.X)) * D ^ (ek + ec) = _
  rw [he, sub_mul]
  have h₁ : shiftedSeries c b * D ^ (ek + ec) = (pc : PowerSeries ℤ) * D ^ ek := by
    rw [add_comm ek ec, pow_add, ← mul_assoc, hc']
  have h₂ : PowerSeries.X * shiftedSeries k b * D ^ (ek + ec) =
      PowerSeries.X * (pk : PowerSeries ℤ) * D ^ ec := by
    rw [pow_add, ← mul_assoc, mul_assoc PowerSeries.X, hk']
  rw [h₁, h₂]
  simp [D]

/-- A rational Laurent presentation remains valid after decreasing its lower bound. -/
theorem rationalPresentation_lower_bound (h : ℤ → ℤ) (a b : ℤ)
    (p : Polynomial ℤ) (e : ℕ) (hp : RationalPresentation h b p e) (hab : a ≤ b) :
    ∃ p' : Polynomial ℤ, RationalPresentation h a p' e := by
  let d := (b - a).toNat
  have hd : (d : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have he : shiftedSeries h a = PowerSeries.X ^ d * shiftedSeries h b := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_X_pow_mul']
    simp only [shiftedSeries, PowerSeries.coeff_mk]
    split_ifs with hn
    · congr 1
      have hcast : ((n - d : ℕ) : ℤ) = (n : ℤ) - d := Int.natCast_sub hn
      rw [hcast]
      omega
    · exact hp.1 _ (by omega)
  refine ⟨X ^ d * p, (fun j hj => hp.1 j (lt_of_lt_of_le hj hab)), ?_⟩
  rw [he, mul_assoc, hp.2]
  simp

/-- Cancel all factors of 1-t from a rational presentation. -/
theorem rationalPresentation_reduce (h : ℤ → ℤ) (b : ℤ) (p : Polynomial ℤ) (e : ℕ)
    (hp : RationalPresentation h b p e) :
    ∃ (q : Polynomial ℤ) (d : ℕ), RationalPresentation h b q d ∧
      (d = 0 ∨ q.eval 1 ≠ 0) := by
  induction e generalizing p with
  | zero => exact ⟨p, 0, hp, Or.inl rfl⟩
  | succ e ih =>
    by_cases hroot : p.eval 1 = 0
    · obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot (a := (1 : ℤ)) (p := p)).mpr hroot
      have hfactor : p = (1 - X) * (-q) := by rw [hq]; simp only [map_one]; ring
      have hD : IsUnit (1 - PowerSeries.X : PowerSeries ℤ) := by
        apply PowerSeries.isUnit_iff_constantCoeff.mpr
        simp
      have hpres : RationalPresentation h b (-q) e := by
        refine ⟨hp.1, ?_⟩
        apply hD.mul_right_cancel
        rw [mul_assoc, ← pow_succ, hp.2, hfactor]
        simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, Polynomial.coe_neg]
        exact mul_comm _ _
      exact ih _ hpres
    · exact ⟨p, e + 1, hp, Or.inr hroot⟩

/-- Hilbert rationality with only a chosen subset of algebra generators active.
This formulation keeps the algebra and its degree-zero ring fixed throughout
Noetherian induction on the number of active generators. -/
theorem rational_of_killed_generators (G : NonnegativeGrading A)
    [IsArtinianRing (Base G)] [IsNoetherianRing A]
    (s : Finset A) (hs : Algebra.adjoin (Base G) (s : Set A) = ⊤)
    (hsdegree : ∀ x ∈ s, x ∈ G.piece 1) :
    ∀ t : Finset A, t ⊆ s →
      ∀ {N : Type*} [AddCommGroup N] [Module A N]
        (V : ModuleGrading G N) [Module.Finite A N],
        (∀ x ∈ s, x ∉ t → ∀ n : N, x • n = 0) →
        ∃ (b : ℤ) (p : Polynomial ℤ) (e : ℕ),
          RationalPresentation (hilbertFunction G V) b p e := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty =>
    intro _ N _ _ V _ hz
    have : Module.Finite (Base G) N := finite_base_of_generators_killed G s hs
      (fun x hx => hz x hx (by simp))
    obtain ⟨b, hb⟩ := bounded_below G V
    obtain ⟨c, hc⟩ := bounded_above_of_finite_base G V
    obtain ⟨p, hp⟩ := rationalPresentation_of_finite_support (hilbertFunction G V) b c hb
      (fun j hj => hilbertFunction_eq_zero_of_piece_eq_bot G V j (hc j hj))
    exact ⟨b, p, 0, hp⟩
  | @insert x t hxt ih =>
    intro hts N _ _ V _ hz
    have hxs : x ∈ s := hts (Finset.mem_insert_self x t)
    have hx : x ∈ G.piece 1 := hsdegree x hxs
    have hts' : t ⊆ s := Finset.Subset.trans (Finset.subset_insert x t) hts
    let K := LinearMap.ker (scalarMap (M := N) x)
    let C := N ⧸ LinearMap.range (scalarMap (M := N) x)
    let VK : ModuleGrading G K := kernelGrading G V x hx
    let VC : ModuleGrading G C := cokernelGrading G V x hx
    have : Module.Finite A K := inferInstance
    have : Module.Finite A C := inferInstance
    have hzK : ∀ y ∈ s, y ∉ t → ∀ n : K, y • n = 0 := by
      intro y hys hyt n
      by_cases hyx : y = x
      · subst y
        exact scalarMap_ker_smul_zero x n
      · exact scalarMap_ker_smul_zero_of_annihilates x y
          (hz y hys (by simp [Finset.mem_insert, hyx, hyt])) n
    have hzC : ∀ y ∈ s, y ∉ t → ∀ n : C, y • n = 0 := by
      intro y hys hyt n
      by_cases hyx : y = x
      · subst y
        exact scalarMap_cokernel_smul_zero x n
      · exact scalarMap_cokernel_smul_zero_of_annihilates x y
          (hz y hys (by simp [Finset.mem_insert, hyx, hyt])) n
    obtain ⟨bk, pk, ek, hk⟩ := ih hts' VK hzK
    obtain ⟨bc, pc, ec, hc⟩ := ih hts' VC hzC
    obtain ⟨bm, hm⟩ := bounded_below G V
    let b := min bm (min bk bc)
    have hb : ∀ j < b, hilbertFunction G V j = 0 := by
      intro j hj
      apply hm j
      dsimp [b] at hj
      omega
    obtain ⟨pk', hk'⟩ := rationalPresentation_lower_bound
      (hilbertFunction G VK) b bk pk ek hk (by dsimp [b]; omega)
    obtain ⟨pc', hc'⟩ := rationalPresentation_lower_bound
      (hilbertFunction G VC) b bc pc ec hc (by dsimp [b]; omega)
    obtain ⟨p, e, hp⟩ := rationalPresentation_of_recurrence
      (hilbertFunction G V) (hilbertFunction G VK) (hilbertFunction G VC) b hb
      pk' pc' ek ec hk' hc'
      (multiplication_length_recurrence G V ⟨s, hsdegree, hs⟩ x hx)
    exact ⟨b, p, e, hp⟩

/-- Hilbert--Serre rationality, including zero and negatively shifted modules. -/
theorem rational : Specs.P103.HilbertSerreLength.rationalType := by
  intro A M _ _ _ G U _ _ hstandard
  classical
  let : IsNoetherianRing (Base G) := P103.Ch03.HopkinsLevitzki.left_noetherian (Base G)
  obtain ⟨s, hsdegree, hs⟩ := hstandard
  let : Algebra.FiniteType (Base G) A := ⟨⟨s, hs⟩⟩
  let : IsNoetherianRing A :=
    P103.Ch05.NoetherianFiniteness.finiteType_noetherian (Base G) A
  exact rational_of_killed_generators G s hs hsdegree s (Finset.Subset.refl s) U
    (fun x hx hnot => False.elim (hnot hx))

/-- Hilbert--Serre with finite lengths, a reduced Laurent presentation,
and the degree and leading coefficient of its eventual polynomial. -/
theorem hilbert_serre : Specs.P103.HilbertSerreLength.hilbertSerreType := by
  intro A M _ _ _ G U _ _ hstandard
  refine ⟨finite_length G U hstandard, ?_⟩
  obtain ⟨b, p, e, hp⟩ := rational G U hstandard
  obtain ⟨p', e', hp', hreduced⟩ := rationalPresentation_reduce
    (hilbertFunction G U) b p e hp
  obtain ⟨q, hq, hzero, hdegree⟩ := coefficients (hilbertFunction G U) b p' e' hp'
  refine ⟨b, p', e', q, hp', hreduced, hq, hzero, ?_⟩
  intro he
  apply hdegree he
  rcases hreduced with hz | hn
  · omega
  · exact hn

end P103.HilbertSerreLength
