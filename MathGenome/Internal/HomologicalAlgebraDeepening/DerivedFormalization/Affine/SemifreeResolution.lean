import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeResolution
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.SetTheory.Cardinal.Finsupp

open CategoryTheory Cardinal

universe u v

namespace DerivedFormalization.Affine.Semifree

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable (A B : NonpositiveCDGA.{u,v} k)

private abbrev GradedElements (C : NonpositiveCDGA.{u,v} k) := Σ i : ℤ, C.complex.X i

/-- A common label type for all stages. Using the same polynomial algebra
throughout keeps the monomial order fixed. -/
private abbrev Labels := ℕ × GradedElements A × GradedElements B

private abbrev NonpositiveDegree := {i : ℤ // i ≤ 0}

private abbrev Generator (W : Type v) := ℕ × NonpositiveDegree × W

private abbrev resolutionVariables (W : Type v) : Variables.{v} where
  Index := Generator W
  degree x := x.2.1.val
  nonpositive x := x.2.1.property

private def resolutionStages (W : Type v) : Stages (resolutionVariables W) where
  Stage := ULift.{v} ℕ
  order := inferInstance
  wellFounded := wellFounded_lt
  stage x := ⟨x.1⟩

private theorem polynomial_cardinal_bound (i : ℤ) :
    #(Polynomial A (resolutionVariables (Labels A B)) i) ≤ #(Labels A B) := by
  classical
  let W := Labels A B
  let V := resolutionVariables W
  let : Nonempty (GradedElements A) := ⟨⟨0, 0⟩⟩
  let : Nonempty (GradedElements B) := ⟨⟨0, 0⟩⟩
  let : Infinite W := inferInstanceAs (Infinite (ℕ × GradedElements A × GradedElements B))
  let : Nonempty V.Index := ⟨(0, ⟨0, le_rfl⟩, 0, ⟨0, 0⟩, ⟨0, 0⟩)⟩
  have hW : ℵ₀ ≤ #W := aleph0_le_mk W
  have hdegree : Cardinal.lift.{v} #NonpositiveDegree ≤ #W := calc
    _ ≤ Cardinal.lift.{v} #ℤ := Cardinal.lift_le.mpr (mk_subtype_le _)
    _ = ℵ₀ := by simp
    _ ≤ #W := hW
  have hV : #V.Index ≤ #W := by
    change #(ℕ × NonpositiveDegree × W) ≤ #W
    simpa [mk_prod] using mul_le_of_le hW hW (mul_le_of_le hW hdegree le_rfl)
  have hm : #V.Monomial ≤ #W := by
    refine (mk_subtype_le _).trans ?_
    change #(V.Index →₀ ℕ) ≤ #W
    rw [mk_finsupp_nat]
    exact max_le hV hW
  have helem : #(GradedElements A) ≤ #W :=
    mk_le_of_injective (f := fun a : GradedElements A => (0, a, (⟨0, 0⟩ : GradedElements B)))
      (fun _ _ h => congrArg (fun w : W => w.2.1) h)
  have hcoeff : #(WithZero (GradedElements A)) ≤ #W := by
    change #(Option (GradedElements A)) ≤ #W
    rw [mk_option]
    exact add_le_of_le hW helem (one_le_aleph0.trans hW)
  let encode (m : V.Monomial) (a : Coefficient A V i m) : WithZero (GradedElements A) :=
    if a = 0 then 0 else (some ⟨_, a⟩ : Option (GradedElements A))
  have hzero (m : V.Monomial) : encode m 0 = 0 := by simp [encode]
  have hinj (m : V.Monomial) : Function.Injective (encode m) := by
    intro x y h
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · exact hx.trans hy.symm
    · exfalso
      simp [encode, hx, hy] at h
    · exfalso
      simp [encode, hx, hy] at h
    · simp only [encode, hx, hy] at h
      exact Sigma.mk.inj_iff.1 (Option.some.inj h) |>.2 |> eq_of_heq
  let : Nonempty V.Monomial := ⟨V.constant⟩
  let : Infinite (WithZero (GradedElements A)) := Infinite.of_injective
    (fun j : ℤ => (some ⟨j, 0⟩ : Option (GradedElements A)))
    (fun _ _ h => congrArg Sigma.fst (Option.some.inj h))
  calc
    #(Polynomial A V i) ≤ #(V.Monomial →₀ WithZero (GradedElements A)) :=
      mk_le_of_injective (finsuppEquivDFinsupp.symm.injective.comp
        ((DFinsupp.mapRange_injective encode hzero).2 hinj))
    _ = max #V.Monomial #(WithZero (GradedElements A)) :=
      mk_finsupp_of_infinite' _ _
    _ ≤ #W := max_le hm hcoeff

private def enumerate {W M : Type v} [Nonempty M] (h : #M ≤ #W) : W → M :=
  Function.invFun (Classical.choice ((Cardinal.le_def M W).mp h) : M ↪ W)

private theorem enumerate_surjective {W M : Type v} [Nonempty M] (h : #M ≤ #W) :
    Function.Surjective (enumerate h) :=
  Function.invFun_surjective (Classical.choice ((Cardinal.le_def M W).mp h)).injective

private abbrev DegreeCycles (i : ℤ) :=
  {b : B.complex.X i // B.complex.d i (i+1) b = 0}

private theorem target_cardinal_bound (i : ℤ) : #(B.complex.X i) ≤ #(Labels A B) :=
  mk_le_of_injective (f := fun b : B.complex.X i =>
      (0, (⟨0, 0⟩ : GradedElements A), (⟨i, b⟩ : GradedElements B)))
    (fun _ _ h => by simpa using congrArg (fun x : Labels A B => x.2.2) h)

private def targetElement (i : ℤ) : Labels A B → B.complex.X i :=
  enumerate (target_cardinal_bound A B i)

private theorem targetElement_surjective (i : ℤ) :
    Function.Surjective (targetElement A B i) :=
  enumerate_surjective (target_cardinal_bound A B i)

private def targetCycle (i : ℤ) : Labels A B → DegreeCycles B i :=
  haveI : Nonempty (DegreeCycles B i) := ⟨⟨0, map_zero _⟩⟩
  enumerate ((mk_subtype_le _).trans (target_cardinal_bound A B i))

private theorem targetCycle_surjective (i : ℤ) :
    Function.Surjective (targetCycle A B i) := by
  let : Nonempty (DegreeCycles B i) := ⟨⟨0, map_zero _⟩⟩
  exact enumerate_surjective ((mk_subtype_le _).trans (target_cardinal_bound A B i))

private abbrev V := resolutionVariables (Labels A B)

/-- Stage zero maps onto target cycles, stage one maps onto all target
elements, and later generators map to zero. -/
private def generatorImage (x : (V A B).Index) : B.complex.X ((V A B).degree x) :=
  match x.1 with
  | 0 => (targetCycle A B x.2.1.val x.2.2).val
  | 1 => targetElement A B x.2.1.val x.2.2
  | _+2 => 0

private def evaluation (f : A ⟶ B) :
    GradedLift A (V A B) B.toCommDGAlgebra (fun i => (f.chainMap.f i).hom)
      (generatorImage A B) :=
  (Classical.choice (gradedUniversalProperty A (V A B) B.toCommDGAlgebra
    (fun i => (f.chainMap.f i).hom) f.map_one f.map_mul (generatorImage A B))).default

private abbrev Assignment (W : Type v) :=
  ∀ x : Generator W, Polynomial A (resolutionVariables W) (x.2.1.val + 1)

/-- Assign all values at the next stage simultaneously. Later assignments
leave the current values at earlier stages intact. -/
private def approximations {W : Type v} (step : ℕ → Assignment A W → Assignment A W) :
    ℕ → Assignment A W
  | 0 => fun _ => 0
  | n+1 => fun x => if x.1 = n then step n (approximations step n) x
      else approximations step n x

private def prescribed {W : Type v} (step : ℕ → Assignment A W → Assignment A W) :
    Assignment A W :=
  fun x => step x.1 (approximations A step x.1) x

private theorem approximations_agree {W : Type v} (step : ℕ → Assignment A W → Assignment A W)
    (n : ℕ) (x : Generator W) (hx : x.1 < n) :
    approximations A step n x = prescribed A step x := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [approximations]
    by_cases h : x.1 = n
    · simp [h, prescribed]
    · simpa only [ite_eq_right h] using ih (by omega)

private theorem target_d_squared (i : ℤ) (b : B.complex.X i) :
    B.complex.d (i+1) (i+1+1) (B.complex.d i (i+1) b) = 0 := by
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (B.complex.d_comp_d i (i+1) (i+1+1))) b
  exact h

private def predecessorCycle (i : ℤ) (a : Labels A B) : DegreeCycles B (i+1) :=
  ⟨B.complex.d i (i+1) (targetElement A B i a), target_d_squared B i _⟩

private abbrev cycleGenerator (i : NonpositiveDegree) (b : DegreeCycles B i.val) :
    (V A B).Index :=
  (0, i, Function.surjInv (targetCycle_surjective A B i.val) b)

private theorem cycleGenerator_image (i : NonpositiveDegree) (b : DegreeCycles B i.val) :
    generatorImage A B (cycleGenerator A B i b) = b.val := by
  exact congrArg Subtype.val (Function.surjInv_eq (targetCycle_surjective A B i.val) b)

private def killCandidate (i : ℤ) : Labels A B → Polynomial A (V A B) i :=
  enumerate (polynomial_cardinal_bound A B i)

private theorem killCandidate_surjective (i : ℤ) :
    Function.Surjective (killCandidate A B i) :=
  enumerate_surjective (polynomial_cardinal_bound A B i)

private abbrev SupportedBefore (n : ℕ) {i : ℤ} (p : Polynomial A (V A B) i) :=
  UsesOnly A (V A B) ((resolutionStages (Labels A B)).before ⟨n⟩) p

/-- In stage one, lift the target differential to a variable from stage zero.
In degree zero the target differential already vanishes. -/
private def firstDifferential (x : (V A B).Index) :
    Polynomial A (V A B) ((V A B).degree x+1) :=
  if h : x.2.1.val+1 ≤ 0 then
    variableTerm A (V A B) (cycleGenerator A B ⟨_, h⟩ (predecessorCycle A B _ x.2.2))
  else 0

/-- The stage only uses cycles from the subalgebra on earlier variables. -/
private def killable (f : A ⟶ B) (n : ℕ) (prev : Assignment A (Labels A B))
    (i : ℤ) (z : Polynomial A (V A B) i) : Prop :=
  SupportedBefore A B n z ∧ (evaluation A B f).component i z = 0 ∧
    (extendDerivation prev).d i z = 0

private def killingDifferential (f : A ⟶ B) (n : ℕ) (prev : Assignment A (Labels A B))
    (x : (V A B).Index) : Polynomial A (V A B) ((V A B).degree x+1) := by
  classical
  let i := (V A B).degree x+1
  let z := killCandidate A B i x.2.2
  exact if killable A B f n prev i z then z else 0

private def resolutionStep (f : A ⟶ B) :
    ℕ → Assignment A (Labels A B) → Assignment A (Labels A B)
  | 0, _ => fun _ => 0
  | 1, _ => firstDifferential A B
  | n+2, prev => killingDifferential A B f (n+2) prev

private abbrev resolutionDifferential (f : A ⟶ B) := prescribed A (resolutionStep A B f)

private theorem firstDifferential_supported (x : (V A B).Index) :
    SupportedBefore A B 1 (firstDifferential A B x) := by
  by_cases h : x.2.1.val+1 ≤ 0
  · rw [firstDifferential, dite_eq_left h]
    apply variable_usesOnly
    exact Nat.zero_lt_succ 0
  · rw [firstDifferential, dite_eq_right h]
    apply UsesOnly.zero

private theorem killingDifferential_supported (f : A ⟶ B) (n : ℕ)
    (prev : Assignment A (Labels A B)) (x : (V A B).Index) :
    SupportedBefore A B n (killingDifferential A B f n prev x) := by
  by_cases h : killable A B f n prev (x.2.1.val+1) (killCandidate A B _ x.2.2)
  · rw [killingDifferential, ite_eq_left h]
    exact h.1
  · rw [killingDifferential, ite_eq_right h]
    apply UsesOnly.zero

private theorem resolutionDifferential_supported (f : A ⟶ B) (x : (V A B).Index) :
    SupportedBefore A B x.1 (resolutionDifferential A B f x) := by
  unfold resolutionDifferential prescribed
  rcases h : x.1 with _ | _ | n
  · rw [resolutionStep]
    apply UsesOnly.zero
  · rw [resolutionStep]
    apply firstDifferential_supported
  · rw [resolutionStep]
    apply killingDifferential_supported

private theorem resolutionDifferential_cycles (f : A ⟶ B) :
    EarlierCycles A (V A B) (resolutionStages (Labels A B)) (resolutionDifferential A B f) := by
  intro x dy D hdy
  have hAgree (y : (V A B).Index) (hy : y.1 < x.1) :
      dy y = approximations A (resolutionStep A B f) x.1 y :=
    (hdy y hy).trans (approximations_agree A _ _ y hy).symm
  have hLocal := derivationLocality A (V A B)
    ((resolutionStages (Labels A B)).before ⟨x.1⟩) dy
    (approximations A (resolutionStep A B f) x.1) D (extendDerivation _) hAgree _
    (resolutionDifferential A B f x) (resolutionDifferential_supported A B f x)
  rw [hLocal]
  unfold resolutionDifferential prescribed
  rcases h : x.1 with _ | _ | n
  · rw [resolutionStep, map_zero]
  · rw [resolutionStep]
    by_cases hdeg : x.2.1.val+1 ≤ 0
    · rw [firstDifferential, dite_eq_left hdeg]
      let y := cycleGenerator A B ⟨x.2.1.val+1, hdeg⟩ (predecessorCycle A B _ x.2.2)
      let D' : Derivation A (V A B) (approximations A (resolutionStep A B f) 1) :=
        extendDerivation (A := A) (V := V A B) (approximations A (resolutionStep A B f) 1)
      exact (D'.on_var y).trans (by rfl)
    · rw [firstDifferential, dite_eq_right hdeg, map_zero]
  · rw [resolutionStep]
    by_cases hz : killable A B f (n+1+1)
        (approximations A (resolutionStep A B f) (n+1+1)) (x.2.1.val+1)
        (killCandidate A B _ x.2.2)
    · rw [killingDifferential, ite_eq_left hz]
      exact hz.2.2
    · rw [killingDifferential, ite_eq_right hz, map_zero]

private theorem evaluation_on_differential (f : A ⟶ B) (x : (V A B).Index) :
    (evaluation A B f).component ((V A B).degree x+1)
        (resolutionDifferential A B f x) =
      B.complex.d ((V A B).degree x) ((V A B).degree x+1) (generatorImage A B x) := by
  unfold resolutionDifferential prescribed
  rcases h : x.1 with _ | _ | n
  · rw [resolutionStep, map_zero]
    simpa only [generatorImage, h] using (targetCycle A B x.2.1.val x.2.2).property.symm
  · rw [resolutionStep]
    by_cases hdegree : x.2.1.val+1 ≤ 0
    · rw [firstDifferential, dite_eq_left hdegree]
      let i : NonpositiveDegree := ⟨x.2.1.val+1, hdegree⟩
      let b := predecessorCycle A B x.2.1.val x.2.2
      refine ((evaluation A B f).map_var (cycleGenerator A B i b)).trans ?_
      simpa only [generatorImage, h, predecessorCycle, b] using cycleGenerator_image A B i b
    · rw [firstDifferential, dite_eq_right hdegree]
      exact (B.nonpositive _ (lt_of_not_ge hdegree)).elim _ _
  · rw [resolutionStep]
    by_cases hz : killable A B f (n+1+1)
        (approximations A (resolutionStep A B f) (n+1+1)) (x.2.1.val+1)
        (killCandidate A B _ x.2.2)
    · rw [killingDifferential, ite_eq_left hz]
      simpa only [generatorImage, h, map_zero] using hz.2.1
    · simp only [killingDifferential, ite_eq_right hz, generatorImage, h, map_zero]

private abbrev resolutionDerivation (f : A ⟶ B) :
    Derivation A (V A B) (resolutionDifferential A B f) :=
  extendDerivation (A := A) (V := V A B) (resolutionDifferential A B f)

private theorem resolutionDerivation_cycles (f : A ⟶ B) (x : (V A B).Index) :
    (resolutionDerivation A B f).d ((V A B).degree x+1) (resolutionDifferential A B f x) = 0 :=
  resolutionDifferential_cycles A B f x _ _ (fun _ _ => rfl)

private theorem evaluation_commutes (f : A ⟶ B) (i : ℤ) (z : Polynomial A (V A B) i) :
    (evaluation A B f).component (i+1) ((resolutionDerivation A B f).d i z) =
      B.complex.d i (i+1) ((evaluation A B f).component i z) := by
  let E := evaluation A B f
  let D := resolutionDerivation A B f
  let dB (j : ℤ) := (B.complex.d j (j+1)).hom
  change E.component (i+1) (D.d i z) = dB i (E.component i z)
  apply polynomial_generated A (V A B)
    (fun i z => E.component (i+1) (D.d i z) = dB i (E.component i z)) _ _ _ _ _ _ i z
  · intro i
    simp only [map_zero]
  · intro i a b ha hb
    simp only [map_add, ha, hb]
  · intro i s a ha
    simp only [LinearMap.map_smul_of_tower, ha]
  · intro i a
    rw [D.on_base, E.map_base, E.map_base]
    exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.chainMap.comm i (i+1))) a).symm
  · intro x
    rw [D.on_var, E.map_var]
    exact evaluation_on_differential A B f x
  · intro i j n h a b ha hb
    rw [D.leibniz, map_add, LinearMap.map_smul_of_tower, E.map_mul, E.map_mul, E.map_mul,
      ha, hb]
    exact (B.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h
      (E.component i a) (E.component j b)).symm

private abbrev resolutionAlgebra (f : A ⟶ B) :=
  stagedAlgebra (resolutionStages (Labels A B)) (resolutionDifferential A B f)
    (resolutionDifferential_cycles A B f)

private def augmentation (f : A ⟶ B) : resolutionAlgebra A B f ⟶ B where
  chainMap :=
    { f := fun i => ModuleCat.ofHom ((evaluation A B f).component i)
      comm' := by
        intro i j hij
        change i+1 = j at hij
        subst j
        change ModuleCat.ofHom ((evaluation A B f).component i) ≫
            B.complex.d i (i+1) =
          (polynomialComplex (resolutionDerivation A B f)
            (resolutionDerivation_cycles A B f)).d i (i+1) ≫
            ModuleCat.ofHom ((evaluation A B f).component (i+1))
        rw [polynomialComplex_d]
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun z => (evaluation_commutes A B f i z).symm }
  map_one := ((evaluation A B f).map_base 0 A.one).trans f.map_one
  map_mul := (evaluation A B f).map_mul

private theorem augmentation_surjective (f : A ⟶ B) :
    NonpositiveCDGA.DegreewiseSurjective (augmentation A B f) := by
  intro i b
  by_cases hi : i ≤ 0
  · obtain ⟨a, ha⟩ := targetElement_surjective A B i b
    refine ⟨variableTerm A (V A B) (1, ⟨i, hi⟩, a), ?_⟩
    change (evaluation A B f).component i (variableTerm A (V A B) (1, ⟨i, hi⟩, a)) = b
    exact ((evaluation A B f).map_var (1, ⟨i, hi⟩, a)).trans ha
  · exact ⟨0, (B.nonpositive i (lt_of_not_ge hi)).elim _ _⟩

private theorem exists_stage {i : ℤ} (p : Polynomial A (V A B) i) :
    ∃ n : ℕ, 2 ≤ n ∧ SupportedBefore A B n p := by
  classical
  let bound := p.support.sup (fun m => m.val.support.sup Prod.fst)
  refine ⟨bound+2, by omega, ?_⟩
  intro m hm x hx
  have h₁ := Finset.le_sup (f := Prod.fst) hx
  have h₂ := Finset.le_sup (f := fun m => m.val.support.sup Prod.fst)
    (DFinsupp.mem_support_iff.mpr hm)
  change x.1 < bound+2
  exact (h₁.trans h₂).trans_lt (by omega)

/-- Choose a stage beyond the support of the cycle, where locality identifies
the provisional differential with the final one. -/
private theorem kernel_cycles_bound (f : A ⟶ B) (j : ℤ)
    (z : Polynomial A (V A B) (j+1))
    (hz : (evaluation A B f).component (j+1) z = 0)
    (hclosed : (resolutionDerivation A B f).d (j+1) z = 0) :
    ∃ y : Polynomial A (V A B) j, (evaluation A B f).component j y = 0 ∧
      (resolutionDerivation A B f).d j y = z := by
  by_cases hj : j ≤ 0
  · obtain ⟨n, hn, hs⟩ := exists_stage A B z
    obtain ⟨a, ha⟩ := killCandidate_surjective A B (j+1) z
    let x : (V A B).Index := (n, ⟨j, hj⟩, a)
    refine ⟨variableTerm A (V A B) x, ?_, ?_⟩
    · refine ((evaluation A B f).map_var x).trans ?_
      cases n with
      | zero => omega
      | succ m =>
        cases m with
        | zero => omega
        | succ m => rfl
    · refine ((resolutionDerivation A B f).on_var x).trans ?_
      change resolutionStep A B f n (approximations A (resolutionStep A B f) n) x = z
      have hAgree (y : (V A B).Index) (hy : y.1 < n) :
          approximations A (resolutionStep A B f) n y = resolutionDifferential A B f y :=
        approximations_agree A _ n y hy
      have hlocal := derivationLocality A (V A B)
        ((resolutionStages (Labels A B)).before ⟨n⟩)
        (approximations A (resolutionStep A B f) n) (resolutionDifferential A B f)
        (extendDerivation _) (extendDerivation _) hAgree (j+1) z hs
      have hkill : killable A B f n (approximations A (resolutionStep A B f) n)
          (j+1) (killCandidate A B (j+1) a) := by
        rw [ha]
        exact ⟨hs, hz, hlocal.trans hclosed⟩
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m+2 := ⟨n-2, by omega⟩
      rw [resolutionStep, killingDifferential, ite_eq_left hkill]
      exact ha
  · have hzero := (polynomial_nonpositive A (V A B) (j+1) (by omega)).elim z 0
    exact ⟨0, map_zero _, (map_zero _).trans hzero.symm⟩

omit [CharZero k] in
private theorem quasiIso_of_surjective_of_kernel_acyclic
    {C D : ModuleCochain.{u,v} k} (g : C ⟶ D)
    (surj : ∀ i, Function.Surjective (g.f i))
    (primitives : ∀ (j : ℤ) (z : C.X (j+1)), g.f (j+1) z = 0 →
      C.d (j+1) (j+1+1) z = 0 →
        ∃ y : C.X j, g.f j y = 0 ∧ C.d j (j+1) y = z) :
    QuasiIso g := by
  let KX (i : ℤ) := ModuleCat.of k (LinearMap.ker (g.f i).hom)
  let kd (i : ℤ) : KX i ⟶ KX (i+1) :=
    ModuleCat.ofHom (((C.d i (i+1)).hom.comp (LinearMap.ker (g.f i).hom).subtype).codRestrict
      (LinearMap.ker (g.f (i+1)).hom) (fun y => by
        change g.f (i+1) (C.d i (i+1) y.val) = 0
        have eg := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (g.comm i (i+1))) y.val
        change D.d i (i+1) (g.f i y.val) = g.f (i+1) (C.d i (i+1) y.val) at eg
        rw [← eg, show g.f i y.val = 0 from y.property, map_zero]))
  let K : ModuleCochain.{u,v} k := CochainComplex.of KX kd (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (C.d_comp_d i (i+1) (i+1+1))) y.val)
  let inc : K ⟶ C :=
    { f := fun i => ModuleCat.ofHom (LinearMap.ker (g.f i).hom).subtype
      comm' := by
        intro i j hij
        change i+1 = j at hij
        subst j
        change ModuleCat.ofHom (LinearMap.ker (g.f i).hom).subtype ≫ C.d i (i+1) =
          CochainComplex.of.d KX kd i (i+1) ≫
            ModuleCat.ofHom (LinearMap.ker (g.f (i+1)).hom).subtype
        rw [CochainComplex.of_d]
        rfl }
  let S := ShortComplex.mk inc g (by
    ext i y
    exact y.property)
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (fun i => LinearMap.shortExact_shortComplexKer (surj i))
  have hK (i : ℤ) : Limits.IsZero (K.homology i) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j+1 := ⟨i-1, by omega⟩
    have hprev : (ComplexShape.up ℤ).prev (j+1) = j :=
      (ComplexShape.up ℤ).prev_eq' (show j+1 = j+1 from rfl)
    have hnext : (ComplexShape.up ℤ).next (j+1) = j+1+1 :=
      (ComplexShape.up ℤ).next_eq' (show j+1+1 = j+1+1 from rfl)
    apply (K.exactAt_iff' j (j+1) (j+1+1) hprev hnext).mpr
    apply ModuleCat.shortComplex_exact
    intro z
    change CochainComplex.of.d KX kd (j+1) (j+1+1) z = 0 ↔
      ∃ y : KX j, CochainComplex.of.d KX kd j (j+1) y = z
    rw [CochainComplex.of_d, CochainComplex.of_d]
    constructor
    · intro hz
      obtain ⟨y, hy, he⟩ := primitives j z.val z.property (congrArg Subtype.val hz)
      exact ⟨⟨y, hy⟩, Subtype.ext he⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (C.d_comp_d j (j+1) (j+1+1))) y.val
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₂ : Mono (HomologicalComplex.homologyMap g i) :=
    (hS.homology_exact₂ i).mono_g ((hK i).eq_of_src _ _)
  have h₃ : Epi (HomologicalComplex.homologyMap g i) :=
    (hS.homology_exact₃ i (i+1) (show i+1 = i+1 from rfl)).epi_f
      ((hK (i+1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Every specified map of nonpositive cdgas over a characteristic-zero field
factors as a semifree extension followed by a degreewise surjective quasi-isomorphism. -/
theorem _root_.DerivedFormalization.semifreeResolution :
    Specs.DerivedFormalization.Affine.SemifreeResolution.Factorization.{u,v} := by
  intro k _ _ A B f
  let S := resolutionStages (Labels A B)
  let dx := resolutionDifferential A B f
  let cycles := resolutionDifferential_cycles A B f
  let i := stagedBase S dx cycles
  let p := augmentation A B f
  refine ⟨resolutionAlgebra A B f, i, p, ?_, ?_, augmentation_surjective A B f, ?_⟩
  · apply CommDGAlgebra.Hom.ext_chainMap
    ext j a
    exact (evaluation A B f).map_base j a
  · exact staged_isSemifree S dx (resolutionDifferential_supported A B f) cycles
  · change QuasiIso p.chainMap
    apply quasiIso_of_surjective_of_kernel_acyclic p.chainMap (augmentation_surjective A B f)
    intro j z hz hd
    change (evaluation A B f).component (j+1) z = 0 at hz
    change (polynomialComplex (resolutionDerivation A B f)
      (resolutionDerivation_cycles A B f)).d (j+1) (j+1+1) z = 0 at hd
    rw [polynomialComplex_d] at hd
    obtain ⟨y, hy, hdy⟩ := kernel_cycles_bound A B f j z hz hd
    refine ⟨y, hy, ?_⟩
    change (polynomialComplex (resolutionDerivation A B f)
      (resolutionDerivation_cycles A B f)).d j (j+1) y = z
    rw [polynomialComplex_d]
    exact hdy

end
end DerivedFormalization.Affine.Semifree
