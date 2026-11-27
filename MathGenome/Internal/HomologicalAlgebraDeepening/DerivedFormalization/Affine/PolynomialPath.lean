import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.PolynomialPath
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.DirectSum.Finsupp

open CategoryTheory

universe u v

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace DerivedFormalization.Affine.PolynomialPath

open Specs.DerivedFormalization.Affine.PolynomialPath
  (Coefficients mapCoefficients derivative primitive evaluate term polynomial form
    transport differential constant endpoint contraction integral convolution)

variable {k : Type u} [Field k] [CharZero k]

abbrev polynomialDerivative := @derivative
abbrev polynomialPrimitive := @primitive
abbrev polynomialEvaluation := @evaluate

section Coefficients

variable {V W Y : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup Y] [Module k Y]

@[simp] theorem mapCoefficients_single (f : V →ₗ[k] W) (n : ℕ) (x : V) :
    mapCoefficients f (Finsupp.single n x) = Finsupp.single n (f x) :=
  Finsupp.lsum_single _ _ _ _

@[simp] theorem derivative_single_zero (x : V) :
    derivative (k := k) (Finsupp.single 0 x) = 0 :=
  Finsupp.lsum_single _ _ _ _

@[simp] theorem derivative_single_succ (n : ℕ) (x : V) :
    derivative (k := k) (Finsupp.single (n+1) x) = Finsupp.single n (((n+1 : ℕ) : k) • x) := by
  rw [derivative, Finsupp.lsum_single]
  exact (Finsupp.lsingle (R := k) n).map_smul _ _ |>.symm

@[simp] theorem primitive_single (n : ℕ) (x : V) :
    primitive (k := k) (Finsupp.single n x) = Finsupp.single (n+1) ((((n+1 : ℕ) : k)⁻¹) • x) := by
  rw [primitive, Finsupp.lsum_single]
  exact (Finsupp.lsingle (R := k) (n+1)).map_smul _ _ |>.symm

@[simp] theorem evaluate_single (c : k) (n : ℕ) (x : V) :
    evaluate c (Finsupp.single n x) = c ^ n • x :=
  Finsupp.lsum_single _ _ _ _

theorem derivative_primitive_apply (p : Coefficients V) :
    derivative (k := k) (primitive (k := k) p) = p := by
  suffices (derivative.comp primitive : Coefficients V →ₗ[k] Coefficients V) =
      LinearMap.id from LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro n x
  have hn : (n : k) + 1 ≠ 0 := by
    simpa only [Nat.cast_succ] using (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) :
      ((n+1 : ℕ) : k) ≠ 0)
  simp [smul_smul, hn]

theorem primitive_derivative_apply (p : Coefficients V) :
    primitive (k := k) (derivative (k := k) p) = p - Finsupp.single 0 (evaluate (0 : k) p) := by
  suffices (primitive.comp derivative : Coefficients V →ₗ[k] Coefficients V) =
      LinearMap.id - (Finsupp.lsingle 0).comp (evaluate (0 : k)) from
    LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  rintro (_ | n) x
  · simp
  · have hn : (n : k) + 1 ≠ 0 := by
      simpa only [Nat.cast_succ] using (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) :
        ((n+1 : ℕ) : k) ≠ 0)
    simp [smul_smul, hn]

@[simp] theorem evaluate_zero_primitive (p : Coefficients V) :
    evaluate (0 : k) (primitive (k := k) p) = 0 := by
  suffices ((evaluate (0 : k)).comp primitive : Coefficients V →ₗ[k] V) = 0 from
    LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro n x
  simp

theorem fundamental_identities :
    Specs.DerivedFormalization.Affine.PolynomialPath.FundamentalIdentities.{u,v} := by
  intro k _ _ V _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact LinearMap.ext fun p => derivative_primitive_apply (k := k) p
  · exact LinearMap.ext fun p => primitive_derivative_apply (k := k) p
  · exact LinearMap.ext fun p => evaluate_zero_primitive (k := k) p
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, primitive_derivative_apply, map_sub,
    evaluate_single, pow_zero, one_smul]

theorem mapCoefficients_comp_apply (g : W →ₗ[k] Y) (f : V →ₗ[k] W) (p : Coefficients V) :
    mapCoefficients g (mapCoefficients f p) = mapCoefficients (g.comp f) p := by
  suffices (mapCoefficients g).comp (mapCoefficients f) = mapCoefficients (g.comp f) from
    LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro n x
  simp

@[simp] theorem mapCoefficients_id_apply (p : Coefficients V) :
    mapCoefficients (LinearMap.id (R := k)) p = p := by
  suffices mapCoefficients (LinearMap.id (R := k) (M := V)) = LinearMap.id from
    LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro n x
  simp

@[simp] theorem mapCoefficients_zero_apply (p : Coefficients V) :
    mapCoefficients (0 : V →ₗ[k] W) p = 0 := by
  suffices mapCoefficients (0 : V →ₗ[k] W) = 0 from LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro n x
  simp

theorem derivative_mapCoefficients (f : V →ₗ[k] W) (p : Coefficients V) :
    derivative (k := k) (mapCoefficients f p) = mapCoefficients f (derivative (k := k) p) := by
  suffices derivative.comp (mapCoefficients f) = (mapCoefficients f).comp derivative from
    LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  rintro (_ | n) x <;> simp

theorem primitive_mapCoefficients (f : V →ₗ[k] W) (p : Coefficients V) :
    primitive (k := k) (mapCoefficients f p) = mapCoefficients f (primitive (k := k) p) := by
  suffices primitive.comp (mapCoefficients f) = (mapCoefficients f).comp primitive from
    LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro n x
  simp

theorem evaluate_mapCoefficients (f : V →ₗ[k] W) (c : k) (p : Coefficients V) :
    evaluate c (mapCoefficients f p) = f (evaluate c p) := by
  suffices (evaluate c).comp (mapCoefficients f) = f.comp (evaluate c) from
    LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro n x
  simp

end Coefficients

section Complex

variable (X : ModuleCochain.{u,v} k)

@[simp] theorem transport_refl (i : ℤ) : transport X i i rfl = LinearMap.id := by
  rfl

theorem transport_d (i j i' j' : ℤ) (e : i=i') (f : j=j') :
    (transport X j j' f).comp (X.d i j).hom =
      (X.d i' j').hom.comp (transport X i i' e) := by
  subst i' j'
  simp

private theorem coefficients_d_d (i j l : ℤ) (p : Coefficients (X.X i)) :
    mapCoefficients (X.d j l).hom (mapCoefficients (X.d i j).hom p) = 0 := by
  rw [mapCoefficients_comp_apply]
  have hh : (X.d j l).hom.comp (X.d i j).hom = 0 :=
    congrArg ModuleCat.Hom.hom (X.d_comp_d i j l)
  rw [hh, mapCoefficients_zero_apply]

theorem differential_coordinates (i j : ℤ) (e : i+1=j)
    (p : Coefficients (X.X i)) (q : Coefficients (X.X (i-1))) :
    differential X i j e (p,q) =
      (mapCoefficients (X.d i j).hom p,
        mapCoefficients (X.d (i-1) (j-1)).hom q +
          i.negOnePow • mapCoefficients (transport X i (j-1) (by omega))
            (derivative (k := k) p)) := rfl

theorem contraction_coordinates (i j : ℤ) (e : i-1=j)
    (p : Coefficients (X.X i)) (q : Coefficients (X.X (i-1))) :
    contraction X i j e (p,q) =
      (j.negOnePow • mapCoefficients (transport X (i-1) j e) (primitive (k := k) q), 0) := by
  change (j.negOnePow • mapCoefficients (transport X (i-1) j e) (primitive (k := k) q),
    j.negOnePow • (0 : Coefficients (X.X (j-1)))) = _
  rw [smul_zero]

theorem differential_square :
    Specs.DerivedFormalization.Affine.PolynomialPath.DifferentialSquare.{u,v} := by
  intro k _ _ X i j l e f
  apply LinearMap.ext
  rintro ⟨p,q⟩
  rw [LinearMap.comp_apply, differential_coordinates X i j e p q,
    differential_coordinates X j l f]
  simp only [map_add, Units.smul_def,
    map_zsmul, coefficients_d_d, zero_add, derivative_mapCoefficients]
  rw [mapCoefficients_comp_apply, mapCoefficients_comp_apply,
    transport_d X i j (j-1) (l-1) (by omega) (by omega)]
  subst j
  rw [Int.negOnePow_succ, Units.val_neg, neg_smul, add_neg_cancel]
  rfl

/-- The signed polynomial path complex of an arbitrary coefficient complex. -/
def pathComplex : ModuleCochain.{u,v} k :=
  CochainComplex.of (term X)
    (fun n => ModuleCat.ofHom (differential X n (n+1) rfl))
    (by
      intro n
      apply ModuleCat.hom_ext
      exact differential_square X n (n+1) (n+1+1) rfl rfl)

@[simp] theorem pathComplex_d (i j : ℤ) (e : i+1=j) :
    (pathComplex X).d i j = ModuleCat.ofHom (differential X i j e) := by
  subst j
  unfold pathComplex
  apply CochainComplex.of_d

def constantMap : X ⟶ pathComplex X :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (constant X n)) (by
    intro n
    rw [pathComplex_d X n (n+1) rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change differential X n (n+1) rfl (Finsupp.single 0 x, 0) =
      (Finsupp.single 0 ((X.d n (n+1)).hom x), 0)
    rw [differential_coordinates X n (n+1) rfl]
    simp only [mapCoefficients_single, map_zero, derivative_single_zero,
      smul_zero, add_zero])

def endpointMap (c : k) : pathComplex X ⟶ X :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (endpoint X c n)) (by
    intro n
    rw [pathComplex_d X n (n+1) rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨p,q⟩
    change X.d n (n+1) (evaluate c p) =
      evaluate c (mapCoefficients (X.d n (n+1)).hom p)
    exact (evaluate_mapCoefficients (X.d n (n+1)).hom c p).symm)

@[simp] theorem constant_endpoint (c : k) : constantMap X ≫ endpointMap X c = 𝟙 X := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change evaluate c (Finsupp.single 0 x) = x
  simp

theorem contraction_equation :
    Specs.DerivedFormalization.Affine.PolynomialPath.ContractionEquation.{u,v} := by
  intro k _ _ X i j l e f
  have eji : j = i-1 := by omega
  subst j
  apply LinearMap.ext
  rintro ⟨p,q⟩
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    contraction_coordinates X i (i-1) rfl p q, differential_coordinates X (i-1) i e,
    differential_coordinates X i l f p q, contraction_coordinates X l i (by omega)]
  simp only [transport_refl, mapCoefficients_id_apply, Units.smul_def,
    map_zsmul, map_zero, zero_add, map_add, smul_add,
    primitive_mapCoefficients, primitive_derivative_apply, derivative_primitive_apply]
  have sign : (i-1).negOnePow = -i.negOnePow := by
    rw [show i-1=i+(-1) by omega, Int.negOnePow_add]
    simp [Int.negOnePow_neg]
  have hd : (mapCoefficients (transport X (l-1) i (by omega))).comp
      (mapCoefficients (X.d (i-1) (l-1)).hom) =
      mapCoefficients (X.d (i-1) i).hom := by
    apply Finsupp.lhom_ext
    intro n x
    simp only [LinearMap.comp_apply, mapCoefficients_single]
    congr 1
    have hh := LinearMap.congr_fun
      (transport_d X (i-1) (l-1) (i-1) i rfl (by omega)) x
    simpa using hh
  have hc : (mapCoefficients (transport X (l-1) i (by omega))).comp
      (mapCoefficients (transport X i (l-1) (by omega))) = LinearMap.id := by
    have hh : l-1 = i := by omega
    have he : ∀ (a b : ℤ) (h : a=b),
        (mapCoefficients (transport X b a h.symm)).comp
          (mapCoefficients (transport X a b h)) = LinearMap.id := by
      intro a b h
      subst b
      apply LinearMap.ext
      intro x
      simp
    exact he i (l-1) hh.symm
  rw [← LinearMap.comp_apply (mapCoefficients (transport X (l-1) i (by omega)))
      (mapCoefficients (X.d (i-1) (l-1)).hom), hd]
  rw [← LinearMap.comp_apply (mapCoefficients (transport X (l-1) i (by omega)))
      (mapCoefficients (transport X i (l-1) (by omega))), hc]
  have hs (x : Coefficients (X.X i)) : i.negOnePow • (i.negOnePow • x) = x := by
    rw [smul_smul, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, one_smul]
  apply Prod.ext
  · change ((i-1).negOnePow : ℤ) • mapCoefficients (X.d (i-1) i).hom (primitive (k := k) q) +
      ((i.negOnePow : ℤ) • mapCoefficients (X.d (i-1) i).hom (primitive (k := k) q) +
      (i.negOnePow : ℤ) • ((i.negOnePow : ℤ) •
        (p - Finsupp.single 0 (evaluate (0 : k) p)))) =
      p - Finsupp.single 0 (evaluate (0 : k) p)
    rw [sign, Units.val_neg, neg_smul, ← add_assoc, neg_add_cancel, zero_add]
    exact hs _
  · change ((i-1).negOnePow : ℤ) • (((i-1).negOnePow : ℤ) • q) + 0 = q - 0
    rw [add_zero, sub_zero, ← Units.smul_def, ← Units.smul_def, smul_smul, ← Int.negOnePow_add,
      ← two_mul, Int.negOnePow_two_mul, one_smul]

theorem integral_equation :
    Specs.DerivedFormalization.Affine.PolynomialPath.IntegralEquation.{u,v} := by
  intro k _ _ X i j l e f
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun (contraction_equation X i j l e f) z
  have hh := congrArg (endpoint X 1 i) h
  have hcomm (w : (pathComplex X).X j) :
      endpoint X 1 i (differential X j i e w) = (X.d j i).hom (endpoint X 1 j w) := by
    have ev := CategoryTheory.congr_fun ((endpointMap X 1).comm j i) w
    rw [pathComplex_d X j i e] at ev
    exact ev.symm
  have hconst (x : X.X i) : endpoint X 1 i (constant X i x) = x := by
    change evaluate (1 : k) (Finsupp.single 0 x) = x
    simp
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, map_sub,
    LinearMap.sub_apply, LinearMap.id_apply, hconst] at hh
  rw [hcomm ((contraction X i j (by omega)) z)] at hh
  exact hh

end Complex

section Action

open Specs.DerivedFormalization.Affine.Tensor (act term)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component HomotopyEquation)
open CochainComplex.HomComplex (Cochain)

private def coefficientsLinear {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] :
    (V →ₗ[k] W) →ₗ[k] (Coefficients V →ₗ[k] Coefficients W) where
  toFun := mapCoefficients
  map_add' f g := by
    apply Finsupp.lhom_ext
    intro n x
    simp
  map_smul' a f := by
    apply Finsupp.lhom_ext
    intro n x
    simp

variable {A : Affine.CommDGAlgebra.{u,v} k} (M : A.Module)

local notation "X" => M.complex ()

private abbrev coeffAct (i j n : ℤ) (h : i+j=n) (b : A.complex.X j) :
    ((X).X i) →ₗ[k] ((X).X n) := (act M i j n h).flip b

/-- A homogeneous coefficient of degree j passes the form part with sign (-1)^j. -/
def action (i j n : ℤ) (h : i+j=n) :
    Specs.DerivedFormalization.Affine.PolynomialPath.term X i →ₗ[k]
      A.complex.X j →ₗ[k] Specs.DerivedFormalization.Affine.PolynomialPath.term X n :=
  LinearMap.flip
    { toFun := fun b =>
        ((mapCoefficients (coeffAct M i j n h b)).comp (LinearMap.fst k _ _)).prod
        (j.negOnePow •
          ((mapCoefficients (coeffAct M (i-1) j (n-1) (by omega) b)).comp
            (LinearMap.snd k _ _)))
      map_add' b c := by
        apply LinearMap.ext
        intro z
        apply Prod.ext
        · change (coefficientsLinear.comp (act M i j n h).flip) (b+c) z.1 = _
          rw [map_add]
          rfl
        · change j.negOnePow •
            (coefficientsLinear.comp (act M (i-1) j (n-1) (by omega)).flip) (b+c) z.2 = _
          rw [map_add, LinearMap.add_apply, smul_add]
          rfl
      map_smul' a b := by
        apply LinearMap.ext
        intro z
        apply Prod.ext
        · change (coefficientsLinear.comp (act M i j n h).flip) (a • b) z.1 = _
          rw [map_smul]
          rfl
        · change j.negOnePow •
            (coefficientsLinear.comp (act M (i-1) j (n-1) (by omega)).flip) (a • b) z.2 = _
          rw [map_smul, LinearMap.smul_apply, smul_comm]
          rfl }

theorem action_coordinates (i j n : ℤ) (h : i+j=n)
    (p : Coefficients ((X).X i)) (q : Coefficients ((X).X (i-1))) (b : A.complex.X j) :
    action M i j n h (p,q) b =
      (mapCoefficients (coeffAct M i j n h b) p,
        j.negOnePow • mapCoefficients (coeffAct M (i-1) j (n-1) (by omega) b) q) := rfl

private theorem coeffAct_one (i : ℤ) : coeffAct M i 0 i (add_zero i) A.one = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact M.act_id () i x

private theorem coeffAct_assoc (i j l ij jl n : ℤ)
    (hij : i+j=ij) (hjl : j+l=jl) (hn : ij+l=n)
    (b : A.complex.X j) (c : A.complex.X l) :
    (coeffAct M ij l n hn c).comp (coeffAct M i j ij hij b) =
      coeffAct M i jl n (by omega) (A.mul j l jl hjl b c) := by
  apply LinearMap.ext
  intro x
  exact Specs.DerivedFormalization.Affine.Tensor.act_assoc_at M i j l ij jl n hij hjl hn x b c

theorem action_one (i : ℤ) (z : (pathComplex X).X i) :
    action M i 0 i (add_zero i) z A.one = z := by
  obtain ⟨p,q⟩ := z
  rw [action_coordinates M i 0 i (add_zero i) p q]
  simp only [coeffAct_one, mapCoefficients_id_apply, Int.negOnePow_zero, one_smul]

theorem action_assoc (i j l ij jl n : ℤ)
    (hij : i+j=ij) (hjl : j+l=jl) (hn : ij+l=n)
    (z : (pathComplex X).X i) (b : A.complex.X j) (c : A.complex.X l) :
    action M ij l n hn (action M i j ij hij z b) c =
      action M i jl n (by omega) z (A.mul j l jl hjl b c) := by
  obtain ⟨p,q⟩ := z
  subst jl
  rw [action_coordinates M i j ij hij p q, action_coordinates M ij l n hn,
    action_coordinates M i (j+l) n (by omega) p q]
  simp only [Units.smul_def, map_zsmul, mapCoefficients_comp_apply, coeffAct_assoc]
  rw [← Units.smul_def, ← Units.smul_def, smul_smul, ← Int.negOnePow_add, add_comm l j]
  rfl

private theorem coefficients_add_apply {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f g : V →ₗ[k] W) (p : Coefficients V) :
    mapCoefficients (f+g) p = mapCoefficients f p + mapCoefficients g p := by
  exact LinearMap.congr_fun (coefficientsLinear.map_add f g) p

private theorem coefficients_zsmul_apply {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (a : ℤ) (f : V →ₗ[k] W) (p : Coefficients V) :
    mapCoefficients (a • f) p = a • mapCoefficients f p := by
  exact LinearMap.congr_fun (map_zsmul coefficientsLinear a f) p

private theorem coeffAct_transport (i j n i' n' : ℤ) (h : i+j=n) (h' : i'+j=n')
    (e : i=i') (f : n=n') (b : A.complex.X j) :
    (transport X n n' f).comp (coeffAct M i j n h b) =
      (coeffAct M i' j n' h' b).comp (transport X i i' e) := by
  subst i' n'
  simp

private theorem coeffAct_d (i j n i' j' n' : ℤ)
    (h : i+j=n) (hi : i+1=i') (hj : j+1=j') (hn : n+1=n') (b : A.complex.X j) :
    ((X).d n n').hom.comp (coeffAct M i j n h b) =
      (coeffAct M i' j n' (by omega) b).comp ((X).d i i').hom +
        (i.negOnePow : ℤ) • coeffAct M i j' n' (by omega) (A.complex.d j j' b) := by
  subst i' j' n'
  apply LinearMap.ext
  intro x
  exact M.leibniz (a := ()) (b := ()) i j n h x b

set_option maxHeartbeats 1200000 in
theorem action_leibniz (i j n i' j' n' : ℤ)
    (h : i+j=n) (hi : i+1=i') (hj : j+1=j') (hn : n+1=n')
    (z : (pathComplex X).X i) (b : A.complex.X j) :
    differential X n n' hn (action M i j n h z b) =
      action M i' j n' (by omega) (differential X i i' hi z) b +
        i.negOnePow • action M i j' n' (by omega) z (A.complex.d j j' b) := by
  obtain ⟨p,q⟩ := z
  rw [action_coordinates M i j n h p q, differential_coordinates X n n' hn,
    differential_coordinates X i i' hi p q, action_coordinates M i' j n' (by omega),
    action_coordinates M i j' n' (by omega)]
  simp only [Units.smul_def, map_zsmul, map_add, smul_add]
  rw [derivative_mapCoefficients (coeffAct M i j n h b)]
  rw [mapCoefficients_comp_apply (transport X n (n'-1) (by omega)),
    coeffAct_transport M i j n (i'-1) (n'-1) h (by omega) (by omega) (by omega) b]
  rw [← mapCoefficients_comp_apply]
  rw [mapCoefficients_comp_apply ((X).d n n').hom, coeffAct_d M i j n i' j' n' h hi hj hn,
    mapCoefficients_comp_apply ((X).d (n-1) (n'-1)).hom,
    coeffAct_d M (i-1) j (n-1) (i'-1) j' (n'-1) (by omega) (by omega) hj (by omega)]
  simp only [coefficients_add_apply, coefficients_zsmul_apply, ← mapCoefficients_comp_apply,
    smul_add]
  apply Prod.ext
  · rfl
  · let x := mapCoefficients (coeffAct M (i'-1) j (n'-1) (by omega) b)
        (mapCoefficients ((X).d (i-1) (i'-1)).hom q)
    let y := mapCoefficients (coeffAct M (i-1) j' (n'-1) (by omega) (A.complex.d j j' b)) q
    let z := mapCoefficients (coeffAct M (i'-1) j (n'-1) (by omega) b)
        (mapCoefficients (transport X i (i'-1) (by omega)) (derivative (k := k) p))
    change (j.negOnePow : ℤ) • x + (j.negOnePow : ℤ) • (((i-1).negOnePow : ℤ) • y) +
      (n.negOnePow : ℤ) • z =
      (j.negOnePow : ℤ) • x + (j.negOnePow : ℤ) • ((i.negOnePow : ℤ) • z) +
      (i.negOnePow : ℤ) • ((j'.negOnePow : ℤ) • y)
    have hs : j + (i-1) = i + j' + 2*(-1) := by omega
    have hp : (j + (i-1)).negOnePow = (i + j').negOnePow := by
      rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
    simp only [smul_smul, ← Units.val_mul, ← Int.negOnePow_add, hp, show j+i=n by omega]
    abel_nf

/-- The signed polynomial path module over the original coefficient algebra. -/
def pathModule : A.Module where
  complex _ := pathComplex X
  act := action M
  act_id _ := action_one M
  act_assoc := by
    intros
    apply action_assoc M
  leibniz := by
    intro a b i j n h z x
    rw [pathComplex_d X n (n+1) rfl, pathComplex_d X i (i+1) rfl]
    exact action_leibniz M i j n (i+1) (j+1) (n+1) h rfl rfl rfl z x

/-- The constant polynomial is a strict module map. -/
def constantModule : M ⟶ pathModule M where
  app _ := constantMap X
  comm_act := by
    intro a b i j n h x c
    change (Finsupp.single 0 (coeffAct M i j n h c x), 0) =
      action M i j n h (Finsupp.single 0 x, 0) c
    rw [action_coordinates M i j n h]
    simp

/-- Evaluation discards the form part and evaluates the polynomial part. -/
def endpointModule (r : k) : pathModule M ⟶ M where
  app _ := endpointMap X r
  comm_act := by
    intro a b i j n h z c
    obtain ⟨p,q⟩ := z
    change evaluate r (action M i j n h (p,q) c).1 = coeffAct M i j n h c (evaluate r p)
    rw [action_coordinates M i j n h p q, evaluate_mapCoefficients]

theorem contraction_action (i j n ir nr : ℤ) (h : i+j=n) (e : i-1=ir) (f : n-1=nr)
    (z : (pathComplex X).X i) (c : A.complex.X j) :
    contraction X n nr f (action M i j n h z c) =
      action M ir j nr (by omega) (contraction X i ir e z) c := by
  subst ir nr
  obtain ⟨p,q⟩ := z
  rw [action_coordinates M i j n h p q, contraction_coordinates X n (n-1) rfl,
    contraction_coordinates X i (i-1) rfl p q, action_coordinates M (i-1) j (n-1) (by omega)]
  simp only [transport_refl, mapCoefficients_id_apply, Units.smul_def, map_zsmul,
    primitive_mapCoefficients, map_zero, smul_zero, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  have hs : n-1+j = (i-1)+2*j := by omega
  rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- The primitive from zero to t in the sign-free right-linear graded Hom. -/
def gradedContraction : gradedHom (pathModule M) (pathModule M) (-1) :=
  ⟨fun _ => Cochain.mk fun i j e => ModuleCat.ofHom (contraction X i j (by omega)), by
    intro a b i j n ir nr h hi hn z c
    change contraction X n nr (by omega) (action M i j n h z c) =
      action M ir j nr (by omega) (contraction X i ir (by omega) z) c
    exact contraction_action M i j n ir nr h (by omega) (by omega) z c⟩

/-- The definite integral in the sign-free right-linear graded Hom. -/
def gradedIntegral : gradedHom (pathModule M) M (-1) :=
  ⟨fun _ => Cochain.mk fun i j e => ModuleCat.ofHom (integral X i j (by omega)), by
    intro a b i j n ir nr h hi hn z c
    change (endpoint X 1 nr) (contraction X n nr (by omega) (action M i j n h z c)) =
      coeffAct M ir j nr (by omega) c ((endpoint X 1 ir) (contraction X i ir (by omega) z))
    rw [contraction_action M i j n ir nr h (by omega) (by omega) z c]
    exact (endpointModule M 1).comm_act (a := ()) (b := ()) ir j nr (by omega)
      (contraction X i ir (by omega) z) c⟩

theorem gradedIntegral_homotopy :
    HomotopyEquation (endpointModule M 1) (endpointModule M 0) (gradedIntegral M) := by
  intro a i z
  cases a
  change endpoint X 1 i z - endpoint X 0 i z =
    ((X).d (i-1) i).hom (integral X i (i-1) rfl z) +
      integral X (i+1) i (by omega) ((pathComplex X).d i (i+1) z)
  rw [pathComplex_d X i (i+1) rfl]
  exact (LinearMap.congr_fun (integral_equation X i (i-1) (i+1) (by omega) rfl) z).symm

theorem gradedContraction_homotopy :
    HomotopyEquation (𝟙 (pathModule M)) (endpointModule M 0 ≫ constantModule M)
      (gradedContraction M) := by
  intro a i z
  cases a
  change (show Specs.DerivedFormalization.Affine.PolynomialPath.term X i from z) - constant X i (endpoint X 0 i z) =
    (show Specs.DerivedFormalization.Affine.PolynomialPath.term X i from
      ((pathComplex X).d (i-1) i) (contraction X i (i-1) rfl z)) +
      contraction X (i+1) i (by omega) ((pathComplex X).d i (i+1) z)
  rw [pathComplex_d X (i-1) i (by omega), pathComplex_d X i (i+1) rfl]
  exact (LinearMap.congr_fun (contraction_equation X i (i-1) (i+1) (by omega) rfl) z).symm

end Action

section Convolution

variable {V W Y U V' W' : Type*}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup Y] [Module k Y] [AddCommGroup U] [Module k U]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

/-- Multiply polynomial coefficients by extending the bilinear map on monomials. -/
abbrev convolve (m : V →ₗ[k] W →ₗ[k] Y) :
    Coefficients V →ₗ[k] Coefficients W →ₗ[k] Coefficients Y :=
  convolution m

@[simp] theorem convolve_single (m : V →ₗ[k] W →ₗ[k] Y) (a b : ℕ) (x : V) (y : W) :
    convolve m (Finsupp.single a x) (Finsupp.single b y) =
      Finsupp.single (a+b) (m x y) := by
  unfold convolve convolution
  rw [Finsupp.lsum_single]
  exact Finsupp.lsum_single k
    (fun b => (m.compr₂ (Finsupp.lsingle (a+b))) x) b y

private theorem convolve_ext {f g : Coefficients V →ₗ[k] Coefficients W →ₗ[k] Y}
    (h : ∀ a b x y, f (Finsupp.single a x) (Finsupp.single b y) =
      g (Finsupp.single a x) (Finsupp.single b y)) : f = g := by
  apply Finsupp.lhom_ext
  intro a x
  apply Finsupp.lhom_ext
  intro b y
  exact h a b x y

theorem convolve_map_left (m : V' →ₗ[k] W →ₗ[k] Y) (f : V →ₗ[k] V')
    (p : Coefficients V) (q : Coefficients W) :
    convolve m (mapCoefficients f p) q = convolve (m.comp f) p q := by
  suffices (convolve m).comp (mapCoefficients f) = convolve (m.comp f) by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  intro a b x y
  simp

theorem convolve_map_right (m : V →ₗ[k] W' →ₗ[k] Y) (f : W →ₗ[k] W')
    (p : Coefficients V) (q : Coefficients W) :
    convolve m p (mapCoefficients f q) = convolve (m.compl₂ f) p q := by
  suffices (convolve m).compl₂ (mapCoefficients f) = convolve (m.compl₂ f) by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  intro a b x y
  simp [LinearMap.compl₂_apply]

theorem map_convolve (m : V →ₗ[k] W →ₗ[k] Y) (f : Y →ₗ[k] U)
    (p : Coefficients V) (q : Coefficients W) :
    mapCoefficients f (convolve m p q) = convolve (m.compr₂ f) p q := by
  suffices (convolve m).compr₂ (mapCoefficients f) = convolve (m.compr₂ f) by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  intro a b x y
  simp [LinearMap.compr₂_apply]

theorem convolve_add (m m' : V →ₗ[k] W →ₗ[k] Y)
    (p : Coefficients V) (q : Coefficients W) :
    convolve (m+m') p q = convolve m p q + convolve m' p q := by
  suffices convolve (m+m') = convolve m + convolve m' by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  intro a b x y
  simp

theorem convolve_zsmul (m : V →ₗ[k] W →ₗ[k] Y) (s : ℤ)
    (p : Coefficients V) (q : Coefficients W) :
    convolve (s • m) p q = s • convolve m p q := by
  suffices convolve (s • m) = s • convolve m by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  intro a b x y
  simp

theorem convolve_single_right (m : V →ₗ[k] W →ₗ[k] Y) (p : Coefficients V) (y : W) :
    convolve m p (Finsupp.single 0 y) = mapCoefficients (m.flip y) p := by
  suffices (convolve m).flip (Finsupp.single 0 y) = mapCoefficients (m.flip y) by
    exact LinearMap.congr_fun this p
  apply Finsupp.lhom_ext
  intro a x
  simp

theorem convolve_single_left (m : V →ₗ[k] W →ₗ[k] Y) (x : V) (q : Coefficients W) :
    convolve m (Finsupp.single 0 x) q = mapCoefficients (m x) q := by
  suffices convolve m (Finsupp.single 0 x) = mapCoefficients (m x) by
    exact LinearMap.congr_fun this q
  apply Finsupp.lhom_ext
  intro a y
  simp

theorem convolve_flip (m : V →ₗ[k] W →ₗ[k] Y)
    (p : Coefficients V) (q : Coefficients W) :
    convolve m.flip q p = convolve m p q := by
  suffices (convolve m.flip).flip = convolve m by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  intro a b x y
  simp [add_comm a b]

theorem convolve_derivative (m : V →ₗ[k] W →ₗ[k] Y)
    (p : Coefficients V) (q : Coefficients W) :
    derivative (k := k) (convolve m p q) =
      convolve m (derivative (k := k) p) q + convolve m p (derivative (k := k) q) := by
  suffices (convolve m).compr₂ derivative =
      (convolve m).comp derivative + (convolve m).compl₂ derivative by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  rintro (_ | a) (_ | b) x y
  · simp [LinearMap.compr₂_apply, LinearMap.compl₂_apply]
  · simp [LinearMap.compr₂_apply, LinearMap.compl₂_apply]
  · simp [LinearMap.compr₂_apply, LinearMap.compl₂_apply]
  · simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.add_apply,
      LinearMap.comp_apply, convolve_single, show a+1+(b+1)=(a+b+1)+1 by omega,
      derivative_single_succ, map_smul, LinearMap.smul_apply]
    rw [show a+(b+1) = a+b+1 by omega, show a+1+b=a+b+1 by omega]
    rw [← Finsupp.single_add]
    congr 1
    rw [← add_smul]
    congr 1
    push_cast
    ring

theorem convolve_evaluate (m : V →ₗ[k] W →ₗ[k] Y) (c : k)
    (p : Coefficients V) (q : Coefficients W) :
    evaluate c (convolve m p q) = m (evaluate c p) (evaluate c q) := by
  suffices (convolve m).compr₂ (evaluate c) =
      (m.comp (evaluate c)).compl₂ (evaluate c) by
    exact LinearMap.congr_fun (LinearMap.congr_fun this p) q
  apply convolve_ext
  intro a b x y
  simp [LinearMap.compr₂_apply, LinearMap.compl₂_apply, smul_smul, pow_add, mul_comm (c ^ a) (c ^ b)]

end Convolution

section Algebra

private theorem snd_zsmul {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (z : ℤ) (x : V × W) : (z • x).2 = z • x.2 := rfl

variable (A : Affine.CommDGAlgebra.{u,v} k)

local notation "Y" => A.complex

def pathMul (i j n : ℤ) (h : i+j=n) : term Y i →ₗ[k] term Y j →ₗ[k] term Y n :=
  let p := ((convolve (A.mul i j n h)).comp (LinearMap.fst k _ _)).compl₂
    (LinearMap.fst k _ _)
  let q := ((convolve (A.mul i (j-1) (n-1) (by omega))).comp (LinearMap.fst k _ _)).compl₂
    (LinearMap.snd k _ _)
  let r := ((convolve (A.mul (i-1) j (n-1) (by omega))).comp (LinearMap.snd k _ _)).compl₂
    (LinearMap.fst k _ _)
  p.compr₂ (polynomial Y n) + q.compr₂ (form Y n) +
    j.negOnePow • r.compr₂ (form Y n)

theorem pathMul_coordinates (i j n : ℤ) (h : i+j=n)
    (p : Coefficients ((Y).X i)) (q : Coefficients ((Y).X (i-1)))
    (r : Coefficients ((Y).X j)) (s : Coefficients ((Y).X (j-1))) :
    pathMul A i j n h (p,q) (r,s) =
      (convolve (A.mul i j n h) p r,
        convolve (A.mul i (j-1) (n-1) (by omega)) p s +
          j.negOnePow • convolve (A.mul (i-1) j (n-1) (by omega)) q r) := by
  apply Prod.ext
  · change convolve (A.mul i j n h) p r + 0 +
      j.negOnePow • (0 : Coefficients ((Y).X n)) = _
    rw [smul_zero, add_zero, add_zero]
  · change 0 + convolve (A.mul i (j-1) (n-1) (by omega)) p s +
      j.negOnePow • convolve (A.mul (i-1) j (n-1) (by omega)) q r = _
    rw [zero_add]

private theorem mul_unit_left (i : ℤ) : A.mul 0 i i (zero_add i) A.one = LinearMap.id :=
  LinearMap.ext (A.toDGAlgebra.id_comp (a := ()) (b := ()) i)

private theorem mul_unit_right (i : ℤ) : (A.mul i 0 i (add_zero i)).flip A.one = LinearMap.id :=
  LinearMap.ext (A.toDGAlgebra.comp_id (a := ()) (b := ()) i)

theorem pathMul_unit_left (i : ℤ) (z : term Y i) :
    pathMul A 0 i i (zero_add i) (constant Y 0 A.one) z = z := by
  obtain ⟨p,q⟩ := z
  change pathMul A 0 i i (zero_add i) (Finsupp.single 0 A.one, 0) (p,q) = (p,q)
  rw [pathMul_coordinates A 0 i i (zero_add i)]
  simp only [convolve_single_left, mul_unit_left, mapCoefficients_id_apply, map_zero,
    LinearMap.zero_apply, smul_zero, add_zero]

theorem pathMul_unit_right (i : ℤ) (z : term Y i) :
    pathMul A i 0 i (add_zero i) z (constant Y 0 A.one) = z := by
  obtain ⟨p,q⟩ := z
  change pathMul A i 0 i (add_zero i) (p,q) (Finsupp.single 0 A.one, 0) = (p,q)
  rw [pathMul_coordinates A i 0 i (add_zero i)]
  simp only [convolve_single_right, mul_unit_right, mapCoefficients_id_apply, map_zero,
    Int.negOnePow_zero, one_smul, zero_add]

private theorem mul_assoc_at (i j l ij jl n : ℤ)
    (e : i+j=ij) (f : j+l=jl) (h : ij+l=n)
    (x : (Y).X i) (y : (Y).X j) (z : (Y).X l) :
    A.mul ij l n h (A.mul i j ij e x y) z =
      A.mul i jl n (by omega) x (A.mul j l jl f y z) := by
  subst ij jl n
  exact A.toDGAlgebra.assoc (a := ()) (b := ()) (c := ()) (e := ()) i j l x y z

private theorem convolve_mul_assoc (i j l ij jl n : ℤ)
    (e : i+j=ij) (f : j+l=jl) (h : ij+l=n)
    (p : Coefficients ((Y).X i)) (q : Coefficients ((Y).X j))
    (r : Coefficients ((Y).X l)) :
    convolve (A.mul ij l n h) (convolve (A.mul i j ij e) p q) r =
      convolve (A.mul i jl n (by omega)) p (convolve (A.mul j l jl f) q r) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p p' hp hp' =>
    simp only [map_add, LinearMap.add_apply, hp, hp']
  | single a x =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' =>
      simp only [map_add, LinearMap.add_apply, hq, hq']
    | single b y =>
      induction r using Finsupp.induction_linear with
      | zero => simp
      | add r r' hr hr' => simp only [map_add, hr, hr']
      | single c z => simp only [convolve_single, add_assoc, mul_assoc_at A i j l ij jl n e f h]

set_option maxHeartbeats 1200000 in
theorem pathMul_assoc (i j l ij jl n : ℤ)
    (e : i+j=ij) (f : j+l=jl) (h : ij+l=n)
    (x : term Y i) (y : term Y j) (z : term Y l) :
    pathMul A ij l n h (pathMul A i j ij e x y) z =
      pathMul A i jl n (by omega) x (pathMul A j l jl f y z) := by
  obtain ⟨p,q⟩ := x
  obtain ⟨r,s⟩ := y
  obtain ⟨t,w⟩ := z
  rw [pathMul_coordinates A i j ij e, pathMul_coordinates A j l jl f,
    pathMul_coordinates A ij l n h, pathMul_coordinates A i jl n (by omega)]
  simp only [map_add, LinearMap.add_apply, Units.smul_def, map_zsmul,
    LinearMap.smul_apply, smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  rw [convolve_mul_assoc A i j l ij jl n e f h,
    convolve_mul_assoc A i j (l-1) ij (jl-1) (n-1) e (by omega) (by omega),
    convolve_mul_assoc A i (j-1) l (ij-1) (jl-1) (n-1) (by omega) (by omega) (by omega),
    convolve_mul_assoc A (i-1) j l (ij-1) jl (n-1) (by omega) f (by omega)]
  have hs : l+j=jl := by omega
  rw [hs]
  abel_nf

private theorem mul_comm_at (i j n : ℤ) (h : i+j=n) :
    A.mul i j n h = (i*j).negOnePow • (A.mul j i n (by omega)).flip := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact A.graded_comm i j n h x y

private theorem convolve_mul_comm (i j n : ℤ) (h : i+j=n)
    (p : Coefficients ((Y).X i)) (q : Coefficients ((Y).X j)) :
    convolve (A.mul i j n h) p q =
      ((i*j).negOnePow : ℤ) • convolve (A.mul j i n (by omega)) q p := by
  rw [mul_comm_at A i j n h, Units.smul_def, convolve_zsmul, ← convolve_flip]
  rfl

set_option maxHeartbeats 1200000 in
theorem pathMul_comm (i j n : ℤ) (h : i+j=n) (x : term Y i) (y : term Y j) :
    pathMul A i j n h x y = (i*j).negOnePow • pathMul A j i n (by omega) y x := by
  obtain ⟨p,q⟩ := x
  obtain ⟨r,s⟩ := y
  rw [pathMul_coordinates A i j n h, pathMul_coordinates A j i n (by omega),
    convolve_mul_comm A i j n h, convolve_mul_comm A i (j-1) (n-1) (by omega),
    convolve_mul_comm A (i-1) j (n-1) (by omega)]
  apply Prod.ext
  · rfl
  · let z := convolve (A.mul (j-1) i (n-1) (by omega)) s p
    let w := convolve (A.mul j (i-1) (n-1) (by omega)) r q
    change ((i*(j-1)).negOnePow : ℤ) • z +
        (j.negOnePow : ℤ) • ((((i-1)*j).negOnePow : ℤ) • w) =
      ((i*j).negOnePow : ℤ) • (w + (i.negOnePow : ℤ) • z)
    rw [smul_add]
    simp only [smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    have e₁ : j+(i-1)*j=i*j := by ring
    have e₂ : i*j+i=i*(j-1)+2*i := by ring
    rw [e₁, e₂, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
    abel_nf

private theorem mul_d_at (i j n i' j' n' : ℤ)
    (h : i+j=n) (hi : i+1=i') (hj : j+1=j') (hn : n+1=n') :
    (A.mul i j n h).compr₂ ((Y).d n n').hom =
      (A.mul i' j n' (by omega)).comp ((Y).d i i').hom +
        (i.negOnePow : ℤ) • (A.mul i j' n' (by omega)).compl₂ ((Y).d j j').hom := by
  subst i' j' n'
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact A.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h x y

private theorem convolve_mul_d (i j n i' j' n' : ℤ)
    (h : i+j=n) (hi : i+1=i') (hj : j+1=j') (hn : n+1=n')
    (p : Coefficients ((Y).X i)) (q : Coefficients ((Y).X j)) :
    mapCoefficients ((Y).d n n').hom (convolve (A.mul i j n h) p q) =
      convolve (A.mul i' j n' (by omega)) (mapCoefficients ((Y).d i i').hom p) q +
        (i.negOnePow : ℤ) •
          convolve (A.mul i j' n' (by omega)) p (mapCoefficients ((Y).d j j').hom q) := by
  rw [map_convolve, mul_d_at A i j n i' j' n' h hi hj hn,
    convolve_add, convolve_zsmul, convolve_map_left, convolve_map_right]

private theorem mul_transport_left (i j n i' n' : ℤ)
    (h : i+j=n) (e : i=i') (f : n=n') (p : Coefficients ((Y).X i))
    (q : Coefficients ((Y).X j)) :
    mapCoefficients (transport Y n n' f) (convolve (A.mul i j n h) p q) =
      convolve (A.mul i' j n' (by omega)) (mapCoefficients (transport Y i i' e) p) q := by
  subst i' n'
  simp

private theorem mul_transport_right (i j n j' n' : ℤ)
    (h : i+j=n) (e : j=j') (f : n=n') (p : Coefficients ((Y).X i))
    (q : Coefficients ((Y).X j)) :
    mapCoefficients (transport Y n n' f) (convolve (A.mul i j n h) p q) =
      convolve (A.mul i j' n' (by omega)) p (mapCoefficients (transport Y j j' e) q) := by
  subst j' n'
  simp

set_option maxHeartbeats 1800000 in
theorem pathMul_leibniz (i j n i' j' n' : ℤ)
    (h : i+j=n) (hi : i+1=i') (hj : j+1=j') (hn : n+1=n')
    (x : term Y i) (y : term Y j) :
    differential Y n n' hn (pathMul A i j n h x y) =
      pathMul A i' j n' (by omega) (differential Y i i' hi x) y +
        i.negOnePow • pathMul A i j' n' (by omega) x (differential Y j j' hj y) := by
  obtain ⟨p,q⟩ := x
  obtain ⟨r,s⟩ := y
  rw [pathMul_coordinates A i j n h, differential_coordinates Y n n' hn,
    differential_coordinates Y i i' hi, differential_coordinates Y j j' hj,
    pathMul_coordinates A i' j n' (by omega), pathMul_coordinates A i j' n' (by omega)]
  simp only [Units.smul_def, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_add]
  rw [convolve_mul_d A i j n i' j' n' h hi hj hn,
    convolve_mul_d A i (j-1) (n-1) i' (j'-1) (n'-1) (by omega) hi (by omega) (by omega),
    convolve_mul_d A (i-1) j (n-1) (i'-1) j' (n'-1) (by omega) (by omega) hj (by omega),
    convolve_derivative, map_add,
    mul_transport_left A i j n (i'-1) (n'-1) h (by omega) (by omega),
    mul_transport_right A i j n (j'-1) (n'-1) h (by omega) (by omega)]
  apply Prod.ext
  · rfl
  · simp only [Prod.snd_add, snd_zsmul, smul_add, smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
    have hp : (j+(i-1)).negOnePow = (i+j').negOnePow := by
      rw [show j+(i-1)=i+j'+2*(-1) by omega, Int.negOnePow_add,
        Int.negOnePow_two_mul, mul_one]
    rw [hp, show j+i=n by omega, congrArg Int.negOnePow h]
    abel_nf

/-- The untruncated cdga (A[t,dt]) with (dt^2=0). -/
def pathAlgebra : Affine.CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => pathComplex Y
      comp := pathMul A
      id := fun _ => constant Y 0 A.one
      d_id := fun _ => by
        have h := CategoryTheory.congr_fun ((constantMap Y).comm 0 1) A.one
        change (pathComplex Y).d 0 1 (constant Y 0 A.one) =
          constant Y 1 ((Y).d 0 1 A.one) at h
        rw [A.toDGAlgebra.d_id (), map_zero] at h
        exact h
      id_comp := fun i x => pathMul_unit_left A i x
      comp_id := fun i x => pathMul_unit_right A i x
      assoc := fun i j l x y z => pathMul_assoc A i j l (i+j) (j+l) (i+j+l) rfl rfl rfl x y z
      leibniz := fun i j n h x y => by
        rw [pathComplex_d Y n (n+1) rfl, pathComplex_d Y i (i+1) rfl, pathComplex_d Y j (j+1) rfl]
        exact pathMul_leibniz A i j n (i+1) (j+1) (n+1) h rfl rfl rfl x y }
  graded_comm := pathMul_comm A

def constantAlgebra : A ⟶ pathAlgebra A where
  chainMap := constantMap Y
  map_one := rfl
  map_mul i j n h x y := by
    change (Finsupp.single 0 (A.mul i j n h x y), 0) =
      pathMul A i j n h (Finsupp.single 0 x, 0) (Finsupp.single 0 y, 0)
    rw [pathMul_coordinates A i j n h]
    simp

def endpointAlgebra (c : k) : pathAlgebra A ⟶ A where
  chainMap := endpointMap Y c
  map_one := by
    change evaluate c (Finsupp.single 0 A.one) = A.one
    simp
  map_mul i j n h x y := by
    obtain ⟨p,q⟩ := x
    obtain ⟨r,s⟩ := y
    change evaluate c (pathMul A i j n h (p,q) (r,s)).1 =
      A.mul i j n h (evaluate c p) (evaluate c r)
    rw [pathMul_coordinates A i j n h, convolve_evaluate]

@[simp] theorem constant_endpointAlgebra (c : k) :
    constantAlgebra A ≫ endpointAlgebra A c = 𝟙 A :=
  Affine.CommDGAlgebra.Hom.ext_chainMap (constant_endpoint Y c)

end Algebra

section Maps

variable {X Y : ModuleCochain.{u,v} k}

def mapDegree (f : X ⟶ Y) (n : ℤ) : term X n →ₗ[k] term Y n :=
  LinearMap.prodMap (mapCoefficients (f.f n).hom) (mapCoefficients (f.f (n-1)).hom)

theorem mapDegree_coordinates (f : X ⟶ Y) (n : ℤ)
    (p : Coefficients (X.X n)) (q : Coefficients (X.X (n-1))) :
    mapDegree f n (p,q) =
      (mapCoefficients (f.f n).hom p, mapCoefficients (f.f (n-1)).hom q) := rfl

private theorem map_d (f : X ⟶ Y) (i j : ℤ) (p : Coefficients (X.X i)) :
    mapCoefficients (f.f j).hom (mapCoefficients (X.d i j).hom p) =
      mapCoefficients (Y.d i j).hom (mapCoefficients (f.f i).hom p) := by
  rw [mapCoefficients_comp_apply, mapCoefficients_comp_apply]
  exact congrArg (fun h => mapCoefficients h p)
    (congrArg ModuleCat.Hom.hom (f.comm i j)).symm

private theorem map_transport (f : X ⟶ Y) (i j : ℤ) (e : i=j) (p : Coefficients (X.X i)) :
    mapCoefficients (f.f j).hom (mapCoefficients (transport X i j e) p) =
      mapCoefficients (transport Y i j e) (mapCoefficients (f.f i).hom p) := by
  subst j
  simp

def pathMap (f : X ⟶ Y) : pathComplex X ⟶ pathComplex Y :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (mapDegree f n)) (by
    intro i
    rw [pathComplex_d X i (i+1) rfl, pathComplex_d Y i (i+1) rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨p,q⟩
    change differential Y i (i+1) rfl (mapDegree f i (p,q)) =
      mapDegree f (i+1) (differential X i (i+1) rfl (p,q))
    rw [mapDegree_coordinates f i, differential_coordinates Y i (i+1) rfl,
      differential_coordinates X i (i+1) rfl, mapDegree_coordinates f (i+1)]
    simp only [map_add, Units.smul_def, map_zsmul, map_d, map_transport,
      derivative_mapCoefficients])

theorem constant_natural (f : X ⟶ Y) :
    constantMap X ≫ pathMap f = f ≫ constantMap Y := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change mapDegree f i (Finsupp.single 0 x, 0) =
    (Finsupp.single 0 ((f.f i).hom x), 0)
  rw [mapDegree_coordinates f i, mapCoefficients_single, map_zero]

theorem endpoint_natural (f : X ⟶ Y) (c : k) :
    pathMap f ≫ endpointMap Y c = endpointMap X c ≫ f := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨p,q⟩
  change evaluate c (mapDegree f i (p,q)).1 = (f.f i).hom (evaluate c p)
  rw [mapDegree_coordinates f i, evaluate_mapCoefficients]

theorem contraction_natural (f : X ⟶ Y) (i j : ℤ) (e : i-1=j)
    (z : term X i) :
    mapDegree f j (contraction X i j e z) = contraction Y i j e (mapDegree f i z) := by
  subst j
  obtain ⟨p,q⟩ := z
  rw [contraction_coordinates X i (i-1) rfl, mapDegree_coordinates f (i-1),
    mapDegree_coordinates f i, contraction_coordinates Y i (i-1) rfl]
  simp only [transport_refl, mapCoefficients_id_apply, Units.smul_def, map_zsmul,
    primitive_mapCoefficients, map_zero]

theorem endpoint_zero_contraction (i j : ℤ) (e : i-1=j) (z : term X i) :
    endpoint X 0 j (contraction X i j e z) = 0 := by
  subst j
  obtain ⟨p,q⟩ := z
  rw [contraction_coordinates X i (i-1) rfl, transport_refl, mapCoefficients_id_apply]
  change evaluate (0 : k) ((i-1).negOnePow • primitive (k := k) q) = 0
  simp [Units.smul_def, map_zsmul]

@[simp] theorem contraction_constant (i j : ℤ) (e : i-1=j) (x : X.X i) :
    contraction X i j e (constant X i x) = 0 := by
  change contraction X i j e (Finsupp.single 0 x, 0) = 0
  rw [contraction_coordinates X i j e]
  simp only [map_zero, smul_zero]
  rfl

end Maps

section AlgebraMaps

variable {A B : Affine.CommDGAlgebra.{u,v} k} (f : A ⟶ B)

private theorem map_convolve_mul (i j n : ℤ) (h : i+j=n)
    (p : Coefficients (A.complex.X i)) (q : Coefficients (A.complex.X j)) :
    mapCoefficients (f.chainMap.f n).hom (convolve (A.mul i j n h) p q) =
      convolve (B.mul i j n h) (mapCoefficients (f.chainMap.f i).hom p)
        (mapCoefficients (f.chainMap.f j).hom q) := by
  rw [map_convolve, convolve_map_left, convolve_map_right]
  suffices (A.mul i j n h).compr₂ (f.chainMap.f n).hom =
      ((B.mul i j n h).comp (f.chainMap.f i).hom).compl₂ (f.chainMap.f j).hom by rw [this]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact f.map_mul i j n h x y

def pathAlgebraMap : pathAlgebra A ⟶ pathAlgebra B where
  chainMap := pathMap f.chainMap
  map_one := by
    change mapDegree f.chainMap 0 (Finsupp.single 0 A.one, 0) =
      (Finsupp.single 0 B.one, 0)
    rw [mapDegree_coordinates, mapCoefficients_single, map_zero]
    exact congrArg (fun x => (Finsupp.single 0 x, 0)) f.map_one
  map_mul i j n h x y := by
    obtain ⟨p,q⟩ := x
    obtain ⟨r,s⟩ := y
    change mapDegree f.chainMap n (pathMul A i j n h (p,q) (r,s)) =
      pathMul B i j n h (mapDegree f.chainMap i (p,q)) (mapDegree f.chainMap j (r,s))
    rw [pathMul_coordinates A i j n h, mapDegree_coordinates f.chainMap n,
      mapDegree_coordinates f.chainMap i, mapDegree_coordinates f.chainMap j,
      pathMul_coordinates B i j n h]
    simp only [map_add, Units.smul_def, map_zsmul, map_convolve_mul]

theorem constantAlgebra_natural :
    constantAlgebra A ≫ pathAlgebraMap f = f ≫ constantAlgebra B :=
  Affine.CommDGAlgebra.Hom.ext_chainMap (constant_natural f.chainMap)

theorem endpointAlgebra_natural (c : k) :
    pathAlgebraMap f ≫ endpointAlgebra B c = endpointAlgebra A c ≫ f :=
  Affine.CommDGAlgebra.Hom.ext_chainMap (endpoint_natural f.chainMap c)

end AlgebraMaps

section Subcomplex

variable {X Y : ModuleCochain.{u,v} k}

structure ClosedTerms (X : ModuleCochain.{u,v} k) where
  term : (n : ℤ) → Submodule k (X.X n)
  d_mem (i j : ℤ) {x : X.X i} : x ∈ term i → X.d i j x ∈ term j

namespace ClosedTerms

variable (S : ClosedTerms X)

abbrev degree (i : ℤ) := ModuleCat.of k (S.term i)

def d (i j : ℤ) : S.degree i ⟶ S.degree j :=
  ModuleCat.ofHom (((X.d i j).hom.comp (S.term i).subtype).codRestrict
    (S.term j) (fun x => S.d_mem i j x.property))

def complex : ModuleCochain.{u,v} k where
  X := S.degree
  d := S.d
  shape i j h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (X.d i j).hom x.val = 0
    rw [X.shape i j h]
    rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact CategoryTheory.congr_fun (X.d_comp_d i j l) x.val

def inclusion : S.complex ⟶ X where
  f i := ModuleCat.ofHom (S.term i).subtype
  comm' _ _ _ := rfl

def factor (f : Y ⟶ X) (h : ∀ i (x : Y.X i), f.f i x ∈ S.term i) : Y ⟶ S.complex where
  f i := ModuleCat.ofHom ((f.f i).hom.codRestrict (S.term i) (h i))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact CategoryTheory.congr_fun (f.comm i j) x

@[simp] theorem factor_inclusion (f : Y ⟶ X) (h : ∀ i (x : Y.X i), f.f i x ∈ S.term i) :
    S.factor f h ≫ S.inclusion = f := by
  ext1 i
  rfl

end ClosedTerms

def kernelTerms (f : X ⟶ Y) : ClosedTerms X where
  term i := LinearMap.ker (f.f i).hom
  d_mem i j {x} hx := by
    change (f.f j).hom ((X.d i j).hom x) = 0
    have e : (f.f j).hom ((X.d i j).hom x) = (Y.d i j).hom ((f.f i).hom x) :=
      (CategoryTheory.congr_fun (f.comm i j) x).symm
    rw [e, LinearMap.mem_ker.mp hx, map_zero]

def equalizerTerms (f g : X ⟶ Y) : ClosedTerms X := kernelTerms (f-g)

theorem mem_equalizerTerms (f g : X ⟶ Y) (i : ℤ) (x : X.X i) :
    x ∈ (equalizerTerms f g).term i ↔ f.f i x = g.f i x := by
  change (f.f i).hom x - (g.f i).hom x = 0 ↔ _
  exact sub_eq_zero

end Subcomplex

section Subalgebra

variable {A B : Affine.CommDGAlgebra.{u,v} k}

structure ClosedAlgebraTerms (A : Affine.CommDGAlgebra.{u,v} k) extends ClosedTerms A.complex where
  one_mem : A.one ∈ toClosedTerms.term 0
  mul_mem (i j n : ℤ) (h : i+j=n) {x : A.complex.X i} {y : A.complex.X j} :
    x ∈ toClosedTerms.term i → y ∈ toClosedTerms.term j → A.mul i j n h x y ∈ toClosedTerms.term n

namespace ClosedAlgebraTerms

variable (S : ClosedAlgebraTerms A)

def mul (i j n : ℤ) (h : i+j=n) :
    S.toClosedTerms.degree i →ₗ[k] S.toClosedTerms.degree j →ₗ[k] S.toClosedTerms.degree n where
  toFun x :=
    ((A.mul i j n h x.val).comp (S.toClosedTerms.term j).subtype).codRestrict
      (S.toClosedTerms.term n) (fun y => S.mul_mem i j n h x.property y.property)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change A.mul i j n h (x.val+y.val) z.val = _
    rw [map_add, LinearMap.add_apply]
    rfl
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change A.mul i j n h (c • x.val) z.val = _
    rw [map_smul, LinearMap.smul_apply]
    rfl

def algebra : Affine.CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => S.toClosedTerms.complex
      comp := S.mul
      id := fun _ => ⟨A.one, S.one_mem⟩
      d_id := fun _ => Subtype.ext (A.toDGAlgebra.d_id ())
      id_comp := fun i x => Subtype.ext (A.toDGAlgebra.id_comp (a := ()) (b := ()) i x.val)
      comp_id := fun i x => Subtype.ext (A.toDGAlgebra.comp_id (a := ()) (b := ()) i x.val)
      assoc := fun i j l x y z => Subtype.ext
        (A.toDGAlgebra.assoc (a := ()) (b := ()) (c := ()) (e := ()) i j l x.val y.val z.val)
      leibniz := fun i j n h x y => Subtype.ext
        (A.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h x.val y.val) }
  graded_comm i j n h x y := Subtype.ext (A.graded_comm i j n h x.val y.val)

def inclusion : S.algebra ⟶ A where
  chainMap := S.toClosedTerms.inclusion
  map_one := rfl
  map_mul _ _ _ _ _ _ := rfl

def factor (f : B ⟶ A) (h : ∀ i (x : B.complex.X i), f.chainMap.f i x ∈ S.toClosedTerms.term i) :
    B ⟶ S.algebra where
  chainMap := S.toClosedTerms.factor f.chainMap h
  map_one := Subtype.ext f.map_one
  map_mul i j n h x y := Subtype.ext (f.map_mul i j n h x y)

@[simp] theorem factor_inclusion (f : B ⟶ A)
    (h : ∀ i (x : B.complex.X i), f.chainMap.f i x ∈ S.toClosedTerms.term i) :
    S.factor f h ≫ S.inclusion = f :=
  Affine.CommDGAlgebra.Hom.ext_chainMap (S.toClosedTerms.factor_inclusion f.chainMap h)

theorem inclusion_cancel {f g : B ⟶ S.algebra} (h : f ≫ S.inclusion = g ≫ S.inclusion) : f = g := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact CategoryTheory.congr_fun (congrArg (fun a => a.chainMap.f i) h) x

end ClosedAlgebraTerms

def algebraEqualizer (f g : A ⟶ B) : ClosedAlgebraTerms A where
  toClosedTerms := equalizerTerms f.chainMap g.chainMap
  one_mem := (mem_equalizerTerms _ _ _ _).2 (f.map_one.trans g.map_one.symm)
  mul_mem i j n h {x y} hx hy := by
    rw [mem_equalizerTerms] at hx hy ⊢
    rw [f.map_mul, g.map_mul, hx, hy]

end Subalgebra

section Truncation

variable (A : Affine.CommDGAlgebra.{u,v} k)

def truncationDegree (i : ℤ) : Submodule k (A.complex.X i) :=
  if i < 0 then ⊤ else if i = 0 then LinearMap.ker (A.complex.d i (i+1)).hom else ⊥

theorem mem_truncationDegree (i : ℤ) (x : A.complex.X i) :
    x ∈ truncationDegree A i ↔
      (0 < i → x = 0) ∧ (i = 0 → A.complex.d i (i+1) x = 0) := by
  rcases lt_trichotomy i 0 with h | rfl | h
  · simp [truncationDegree, h, not_lt.mpr h.le, h.ne]
  · simp [truncationDegree, LinearMap.mem_ker]
  · simp [truncationDegree, not_lt.mpr h.le, h.ne', h]

def truncationTerms : ClosedAlgebraTerms A where
  term := truncationDegree A
  d_mem i j {x} hx := by
    rw [mem_truncationDegree] at hx ⊢
    by_cases e : i+1=j
    · subst j
      constructor
      · intro hj
        by_cases hi : i=0
        · exact hx.2 hi
        · rw [hx.1 (by omega), map_zero]
      · intro _
        exact CategoryTheory.congr_fun (A.complex.d_comp_d i (i+1) (i+1+1)) x
    · rw [A.complex.shape i j e]
      exact ⟨fun _ => rfl, fun _ => map_zero _⟩
  one_mem := (mem_truncationDegree A 0 A.one).2
    ⟨fun h => (lt_irrefl _ h).elim, fun _ => A.toDGAlgebra.d_id ()⟩
  mul_mem i j n h {x y} hx hy := by
    rw [mem_truncationDegree] at hx hy ⊢
    by_cases hi : 0 < i
    · rw [hx.1 hi, map_zero, LinearMap.zero_apply]
      exact ⟨fun _ => rfl, fun _ => map_zero _⟩
    by_cases hj : 0 < j
    · rw [hy.1 hj, map_zero]
      exact ⟨fun _ => rfl, fun _ => map_zero _⟩
    refine ⟨fun hn => (show False by omega).elim, ?_⟩
    intro hn
    have ei : i=0 := by omega
    have ej : j=0 := by omega
    rw [A.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h x y,
      hx.2 ei, hy.2 ej, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero]

def truncation : Affine.NonpositiveCDGA.{u,v} k where
  toCommDGAlgebra := (truncationTerms A).algebra
  nonpositive i hi := ⟨fun x y => by
    have hx : x.val ∈ truncationDegree A i := x.property
    have hy : y.val ∈ truncationDegree A i := y.property
    apply Subtype.ext
    exact ((mem_truncationDegree A i x.val).1 hx).1 hi |>.trans
      (((mem_truncationDegree A i y.val).1 hy).1 hi).symm⟩

def truncationInclusion : (truncation A).toCommDGAlgebra ⟶ A :=
  (truncationTerms A).inclusion

end Truncation

section Relative

variable {Q B : Affine.NonpositiveCDGA.{u,v} k} (f : Q ⟶ B)

local notation "Q₀" => Q.toCommDGAlgebra
local notation "B₀" => B.toCommDGAlgebra

/-- The pullback along the inclusion of constant B-polynomials. The B-coordinate
is recovered by evaluation at zero followed by f. -/
def relativeTerms : ClosedAlgebraTerms (pathAlgebra Q₀) :=
  algebraEqualizer (pathAlgebraMap (show Q₀ ⟶ B₀ from f))
    (endpointAlgebra Q₀ 0 ≫ (show Q₀ ⟶ B₀ from f) ≫ constantAlgebra B₀)

abbrev relativeAlgebra := (relativeTerms f).algebra
abbrev relativeInclusion := (relativeTerms f).inclusion

theorem mem_relativeTerms (i : ℤ) (z : term Q.complex i) :
    z ∈ (relativeTerms f).toClosedTerms.term i ↔
      mapDegree f.chainMap i z = constant B.complex i ((f.chainMap.f i).hom
        (endpoint Q.complex 0 i z)) :=
  mem_equalizerTerms _ _ _ _

def relativeEvaluation (c : k) : relativeAlgebra f ⟶ Q₀ :=
  relativeInclusion f ≫ endpointAlgebra Q₀ c

def relativeConstant : Q₀ ⟶ relativeAlgebra f :=
  (relativeTerms f).factor (constantAlgebra Q₀) (by
    intro i x
    have hm := (mem_relativeTerms f i (constant Q.complex i x)).2
    apply hm
    change mapDegree f.chainMap i (Finsupp.single 0 x, 0) =
      constant B.complex i ((f.chainMap.f i).hom (evaluate (0 : k) (Finsupp.single 0 x)))
    rw [mapDegree_coordinates, mapCoefficients_single, map_zero, evaluate_single, pow_zero, one_smul]
    rfl)

@[simp] theorem relativeConstant_eval (c : k) :
    relativeConstant f ≫ relativeEvaluation f c = 𝟙 Q₀ := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change evaluate c (Finsupp.single 0 x) = x
  simp

theorem relative_eval_over (c : k) :
    relativeEvaluation f c ≫ (show Q₀ ⟶ B₀ from f) =
      relativeEvaluation f 0 ≫ (show Q₀ ⟶ B₀ from f) := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz := (mem_relativeTerms f i z.val).1 z.property
  have h := congrArg (endpoint B.complex c i) hz
  change (f.chainMap.f i).hom (endpoint Q.complex c i z.val) =
    (f.chainMap.f i).hom (endpoint Q.complex 0 i z.val)
  generalize z.val = w at h ⊢
  obtain ⟨p,q⟩ := w
  change (f.chainMap.f i).hom (evaluate c p) =
    (f.chainMap.f i).hom (evaluate (0 : k) p)
  change evaluate c (mapDegree f.chainMap i (p,q)).1 =
    evaluate c (Finsupp.single 0 ((f.chainMap.f i).hom (evaluate (0 : k) p))) at h
  rw [mapDegree_coordinates, evaluate_mapCoefficients, evaluate_single, pow_zero, one_smul] at h
  exact h

def relativePath : Affine.NonpositiveCDGA.{u,v} k := truncation (relativeAlgebra f)

abbrev relativePathInclusion : (relativePath f).toCommDGAlgebra ⟶ relativeAlgebra f :=
  truncationInclusion (relativeAlgebra f)

def evaluation (c : k) : relativePath f ⟶ Q :=
  (relativePathInclusion f ≫ relativeEvaluation f c :
    (relativePath f).toCommDGAlgebra ⟶ Q₀)

def constants : Q ⟶ relativePath f :=
  (truncationTerms (relativeAlgebra f)).factor (relativeConstant f) (by
    intro i x
    apply (mem_truncationDegree (relativeAlgebra f) i ((relativeConstant f).chainMap.f i x)).2
    constructor
    · intro hi
      rw [(Q.nonpositive i hi).elim x 0, map_zero]
    · rintro rfl
      exact ((CategoryTheory.congr_fun ((relativeConstant f).chainMap.comm 0 1) x).trans
        (by rw [ModuleCat.comp_apply, Affine.NonpositiveCDGA.d_zero_apply, map_zero])))

@[simp] theorem constants_evaluation (c : k) :
    constants f ≫ evaluation f c = 𝟙 Q := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change evaluate c (Finsupp.single 0 x) = x
  simp

end Relative

private def homotopyFromComponents {X Y : ModuleCochain.{u,v} k} (g p : X ⟶ Y)
    (h : ∀ i j : ℤ, i-1=j → X.X i →ₗ[k] Y.X j)
    (eq : ∀ (i : ℤ) (z : X.X i),
      (Y.d (i-1) i).hom (h i (i-1) rfl z) +
        h (i+1) i (by omega) ((X.d i (i+1)).hom z) = (g.f i).hom z - (p.f i).hom z) :
    Homotopy g p where
  hom i j := if e : i-1=j then ModuleCat.ofHom (h i j e) else 0
  zero i j e := dite_eq_right (by
    intro h
    apply e
    exact show j+1=i by omega)
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i-1) i from (show i-1+1=i by omega))]
    simp only [dite_eq_left (show i+1-1=i by omega)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (g.f i).hom z =
      h (i+1) i (by omega) ((X.d i (i+1)).hom z) +
        (Y.d (i-1) i).hom (h i (i-1) rfl z) + (p.f i).hom z
    rw [add_comm (h (i+1) i (by omega) ((X.d i (i+1)).hom z)), eq, sub_add_cancel]

private def homotopyOfContraction {X : ModuleCochain.{u,v} k} (p : X ⟶ X)
    (h : ∀ i j : ℤ, i-1=j → X.X i →ₗ[k] X.X j)
    (eq : ∀ (i : ℤ) (z : X.X i),
      (X.d (i-1) i).hom (h i (i-1) rfl z) +
        h (i+1) i (by omega) ((X.d i (i+1)).hom z) = z - (p.f i).hom z) :
    Homotopy (𝟙 X) p :=
  homotopyFromComponents (𝟙 X) p h eq

/-- Polynomial integration with constants as a strict inverse in one direction. -/
def endpointZeroEquiv (X : ModuleCochain.{u,v} k) : HomotopyEquiv (pathComplex X) X where
  hom := endpointMap X 0
  inv := constantMap X
  homotopyHomInvId := (homotopyOfContraction _ (contraction X) (by
    intro i z
    rw [pathComplex_d X (i-1) i (by omega), pathComplex_d X i (i+1) rfl]
    exact LinearMap.congr_fun (contraction_equation X i (i-1) (i+1) (by omega) rfl) z)).symm
  homotopyInvHomId := Homotopy.ofEq (constant_endpoint X 0)

def endpointHomotopy (X : ModuleCochain.{u,v} k) :
    Homotopy (endpointMap X 1) (endpointMap X 0) :=
  homotopyFromComponents (endpointMap X 1) (endpointMap X 0) (integral X) (by
    intro i z
    rw [pathComplex_d X i (i+1) rfl]
    exact LinearMap.congr_fun (integral_equation X i (i-1) (i+1) (by omega) rfl) z)

/-- Evaluation at one has the same constants as homotopy inverse. -/
def endpointOneEquiv (X : ModuleCochain.{u,v} k) : HomotopyEquiv (pathComplex X) X where
  hom := endpointMap X 1
  inv := constantMap X
  homotopyHomInvId :=
    ((endpointHomotopy X).compRight (constantMap X)).trans (endpointZeroEquiv X).homotopyHomInvId
  homotopyInvHomId := Homotopy.ofEq (constant_endpoint X 1)

section RelativeContraction

variable {Q B : Affine.NonpositiveCDGA.{u,v} k} (f : Q ⟶ B)

def relativeContraction (i j : ℤ) (e : i-1=j) :
    (relativeAlgebra f).complex.X i →ₗ[k] (relativeAlgebra f).complex.X j :=
  ((contraction Q.complex i j e).comp ((relativeTerms f).term i).subtype).codRestrict
    ((relativeTerms f).term j) (by
      intro z
      apply (mem_relativeTerms f j _).2
      let w : term Q.complex i := z.val
      have hw := (mem_relativeTerms f i w).1 z.property
      change mapDegree f.chainMap j (contraction Q.complex i j e w) =
        constant B.complex j ((f.chainMap.f j).hom
          (endpoint Q.complex 0 j (contraction Q.complex i j e w)))
      rw [contraction_natural f.chainMap i j e w, hw,
        contraction_constant (X := B.complex) i j e, endpoint_zero_contraction (X := Q.complex) i j e w,
        map_zero, map_zero])

def truncatedContraction (i j : ℤ) (e : i-1=j) :
    (relativePath f).complex.X i →ₗ[k] (relativePath f).complex.X j :=
  ((relativeContraction f i j e).comp (truncationDegree (relativeAlgebra f) i).subtype).codRestrict
    (truncationDegree (relativeAlgebra f) j) (by
      intro z
      apply (mem_truncationDegree _ _ _).2
      have h (hij : 0 ≤ j) : z.val = 0 :=
        ((mem_truncationDegree _ _ _).1 z.property).1 (by omega)
      refine ⟨fun hj => ?_, fun hj => ?_⟩
      · change relativeContraction f i j e z.val = 0
        rw [h hj.le, map_zero]
      · change (relativeAlgebra f).complex.d j (j+1) (relativeContraction f i j e z.val) = 0
        rw [h (by omega), map_zero, map_zero])

set_option maxHeartbeats 1200000 in
private theorem relativeContraction_equation (i : ℤ) (z : (relativeAlgebra f).complex.X i) :
    ((relativeAlgebra f).complex.d (i-1) i).hom (relativeContraction f i (i-1) rfl z) +
      relativeContraction f (i+1) i (by omega) (((relativeAlgebra f).complex.d i (i+1)).hom z) =
      z - (((relativeEvaluation f 0).chainMap ≫ (relativeConstant f).chainMap).f i).hom z := by
  apply Subtype.ext
  let w : term Q.complex i := z.val
  change (show term Q.complex i from
      (pathComplex Q.complex).d (i-1) i (contraction Q.complex i (i-1) rfl w)) +
    contraction Q.complex (i+1) i (by omega) ((pathComplex Q.complex).d i (i+1) w) =
      w - constant Q.complex i (endpoint Q.complex 0 i w)
  rw [pathComplex_d Q.complex (i-1) i (by omega), pathComplex_d Q.complex i (i+1) rfl]
  exact LinearMap.congr_fun (contraction_equation Q.complex i (i-1) (i+1) (by omega) rfl) w

/-- Evaluation at zero has the constant section before good truncation. -/
def relativeHomotopyEquiv : HomotopyEquiv (relativeAlgebra f).complex Q.complex where
  hom := (relativeEvaluation f 0).chainMap
  inv := (relativeConstant f).chainMap
  homotopyHomInvId :=
    (homotopyOfContraction _ (relativeContraction f) (relativeContraction_equation f)).symm
  homotopyInvHomId := Homotopy.ofEq
    (congrArg Affine.CommDGAlgebra.Hom.chainMap (relativeConstant_eval f 0))

set_option maxHeartbeats 1200000 in
/-- The same contraction restricts to the good truncation. -/
def truncatedHomotopyEquiv : HomotopyEquiv (relativePath f).complex Q.complex where
  hom := (evaluation f 0).chainMap
  inv := (constants f).chainMap
  homotopyHomInvId := (homotopyOfContraction _ (truncatedContraction f) (by
    intro i z
    apply Subtype.ext
    exact relativeContraction_equation f i z.val)).symm
  homotopyInvHomId := Homotopy.ofEq
    (congrArg Affine.CommDGAlgebra.Hom.chainMap (constants_evaluation f 0))

theorem relative_evaluation_quasiIso : QuasiIso (relativeEvaluation f 0).chainMap :=
  (relativeHomotopyEquiv f).quasiIso_hom

theorem truncated_evaluation_quasiIso : Affine.NonpositiveCDGA.IsQuasiIso (evaluation f 0) :=
  (truncatedHomotopyEquiv f).quasiIso_hom

/-- The kernel of evaluation at zero in the untruncated relative path. -/
abbrev relativeKernel :=
  (kernelTerms (relativeEvaluation f 0).chainMap).complex

private theorem relativeContraction_in_kernel (i j : ℤ) (e : i-1=j)
    (x : (relativeAlgebra f).complex.X i) :
    (relativeEvaluation f 0).chainMap.f j (relativeContraction f i j e x) = 0 :=
  endpoint_zero_contraction (X := Q.complex) i j e x.val

private def contractRelativeKernel (i j : ℤ) (e : i-1=j) :
    (relativeKernel f).X i →ₗ[k] (relativeKernel f).X j :=
  ((relativeContraction f i j e).comp
    ((kernelTerms (relativeEvaluation f 0).chainMap).term i).subtype).codRestrict
      ((kernelTerms (relativeEvaluation f 0).chainMap).term j)
      (fun x => relativeContraction_in_kernel f i j e x.val)

set_option maxHeartbeats 1200000 in
/-- Integration from zero to t contracts the kernel of evaluation at zero. -/
def relativeKernelHomotopy : Homotopy (𝟙 (relativeKernel f)) 0 :=
  homotopyOfContraction 0 (contractRelativeKernel f) (by
    intro i x
    apply Subtype.ext
    have h := relativeContraction_equation f i x.val
    have hz : (relativeEvaluation f 0).chainMap.f i x.val = 0 := x.property
    change _ = x.val - (0 : (relativeAlgebra f).complex.X i)
    change _ = x.val - ((relativeConstant f).chainMap.f i).hom
      (((relativeEvaluation f 0).chainMap.f i).hom x.val) at h
    rw [show ((relativeEvaluation f 0).chainMap.f i).hom x.val = 0 from hz, map_zero] at h
    exact h)

end RelativeContraction

section FiberProduct

variable {U V : Affine.CommDGAlgebra.{u,v} k} (A C : Affine.CommDGAlgebra.{u,v} k)

private abbrev productDegree (i : ℤ) := ModuleCat.of k (A.complex.X i × C.complex.X i)

@[reducible] private def productComplex : ModuleCochain.{u,v} k where
  X := productDegree A C
  d i j := ModuleCat.ofHom (LinearMap.prodMap (A.complex.d i j).hom (C.complex.d i j).hom)
  shape i j h := by
    rw [A.complex.shape i j h, C.complex.shape i j h]
    apply ModuleCat.hom_ext
    rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x,y⟩
    exact Prod.ext (CategoryTheory.congr_fun (A.complex.d_comp_d i j l) x)
      (CategoryTheory.congr_fun (C.complex.d_comp_d i j l) y)

private def productMul (i j n : ℤ) (h : i+j=n) :
    productDegree A C i →ₗ[k] productDegree A C j →ₗ[k] productDegree A C n :=
  (((A.mul i j n h).comp (LinearMap.fst k _ _)).compl₂
    (LinearMap.fst k _ _)).compr₂ (LinearMap.inl k _ _) +
  (((C.mul i j n h).comp (LinearMap.snd k _ _)).compl₂
    (LinearMap.snd k _ _)).compr₂ (LinearMap.inr k _ _)

private theorem productMul_coordinates (i j n : ℤ) (h : i+j=n)
    (x : productDegree A C i) (y : productDegree A C j) :
    productMul A C i j n h x y =
      (A.mul i j n h x.1 y.1, C.mul i j n h x.2 y.2) := by
  exact Prod.ext (add_zero _) (zero_add _)

private theorem productMul_comm (i j n : ℤ) (h : i+j=n)
    (x : productDegree A C i) (y : productDegree A C j) :
    productMul A C i j n h x y = (i*j).negOnePow • productMul A C j i n (by omega) y x := by
  rw [productMul_coordinates A C i j n h, productMul_coordinates A C j i n (by omega)]
  exact Prod.ext (A.graded_comm i j n h x.1 y.1) (C.graded_comm i j n h x.2 y.2)

set_option maxHeartbeats 1200000 in
@[reducible] private def productAlgebra : Affine.CommDGAlgebra.{u,v} k where
  toDGAlgebra :=
    { hom := fun _ _ => productComplex A C
      comp := productMul A C
      id := fun _ => (A.one,C.one)
      d_id := fun _ => Prod.ext (A.toDGAlgebra.d_id ()) (C.toDGAlgebra.d_id ())
      id_comp := fun i x => by
        rw [productMul_coordinates]
        exact Prod.ext (A.toDGAlgebra.id_comp (a := ()) (b := ()) i x.1)
          (C.toDGAlgebra.id_comp (a := ()) (b := ()) i x.2)
      comp_id := fun i x => by
        rw [productMul_coordinates]
        exact Prod.ext (A.toDGAlgebra.comp_id (a := ()) (b := ()) i x.1)
          (C.toDGAlgebra.comp_id (a := ()) (b := ()) i x.2)
      assoc := fun i j l x y z => by
        rw [productMul_coordinates A C i j (i+j) rfl,
          productMul_coordinates A C j l (j+l) rfl,
          productMul_coordinates A C (i+j) l (i+j+l) rfl,
          productMul_coordinates A C i (j+l) (i+j+l) (by omega)]
        exact Prod.ext (A.toDGAlgebra.assoc (a := ()) (b := ()) (c := ()) (e := ()) i j l x.1 y.1 z.1)
          (C.toDGAlgebra.assoc (a := ()) (b := ()) (c := ()) (e := ()) i j l x.2 y.2 z.2)
      leibniz := fun i j n h x y => by
        rw [productMul_coordinates A C i j n h,
          productMul_coordinates A C (i+1) j (n+1) (by omega),
          productMul_coordinates A C i (j+1) (n+1) (by omega)]
        exact Prod.ext (A.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h x.1 y.1)
          (C.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) i j n h x.2 y.2) }
  graded_comm := productMul_comm A C

private def productFst : productAlgebra A C ⟶ A where
  chainMap := ⟨fun _ => ModuleCat.ofHom (LinearMap.fst k _ _), fun _ _ _ => rfl⟩
  map_one := rfl
  map_mul i j n h x y := congrArg Prod.fst (productMul_coordinates A C i j n h x y)

private def productSnd : productAlgebra A C ⟶ C where
  chainMap := ⟨fun _ => ModuleCat.ofHom (LinearMap.snd k _ _), fun _ _ _ => rfl⟩
  map_one := rfl
  map_mul i j n h x y := congrArg Prod.snd (productMul_coordinates A C i j n h x y)

private def productPair (a : U ⟶ A) (c : U ⟶ C) : U ⟶ productAlgebra A C where
  chainMap :=
    { f := fun i => ModuleCat.ofHom ((a.chainMap.f i).hom.prod (c.chainMap.f i).hom)
      comm' := fun i j _ => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Prod.ext (CategoryTheory.congr_fun (a.chainMap.comm i j) x)
          (CategoryTheory.congr_fun (c.chainMap.comm i j) x) }
  map_one := Prod.ext a.map_one c.map_one
  map_mul i j n h x y := by
    change ((a.chainMap.f n).hom (U.mul i j n h x y),
      (c.chainMap.f n).hom (U.mul i j n h x y)) =
      productMul A C i j n h ((a.chainMap.f i).hom x, (c.chainMap.f i).hom x)
        ((a.chainMap.f j).hom y, (c.chainMap.f j).hom y)
    rw [productMul_coordinates A C i j n h]
    exact Prod.ext (a.map_mul i j n h x y) (c.map_mul i j n h x y)

variable {A C} (a : A ⟶ V) (c : C ⟶ V)

private def fiberTerms : ClosedAlgebraTerms (productAlgebra A C) :=
  algebraEqualizer (productFst A C ≫ a) (productSnd A C ≫ c)

private theorem mem_fiberTerms (i : ℤ) (p : productDegree A C i) :
    p ∈ (fiberTerms a c).term i ↔ a.chainMap.f i p.1 = c.chainMap.f i p.2 :=
  mem_equalizerTerms _ _ _ _

private def fiberPair (f : U ⟶ A) (g : U ⟶ C) (e : f ≫ a = g ≫ c) :
    U ⟶ (fiberTerms a c).algebra :=
  (fiberTerms a c).factor (productPair A C f g) (by
    intro i x
    apply (mem_fiberTerms a c i _).2
    exact CategoryTheory.congr_fun (congrArg (fun z => z.chainMap.f i) e) x)

variable {Q B : Affine.NonpositiveCDGA.{u,v} k} (f : Q ⟶ B)

local notation "f₀" => (f : Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra)

def endpointTarget : Affine.NonpositiveCDGA.{u,v} k where
  toCommDGAlgebra := (fiberTerms f₀ f₀).algebra
  nonpositive i hi := ⟨fun x y => Subtype.ext
    (Prod.ext ((Q.nonpositive i hi).elim x.val.1 y.val.1)
      ((Q.nonpositive i hi).elim x.val.2 y.val.2))⟩

def firstEndpoint : endpointTarget f ⟶ Q :=
  ((fiberTerms f₀ f₀).inclusion ≫ productFst Q.toCommDGAlgebra Q.toCommDGAlgebra :
    (endpointTarget f).toCommDGAlgebra ⟶ Q.toCommDGAlgebra)

def secondEndpoint : endpointTarget f ⟶ Q :=
  ((fiberTerms f₀ f₀).inclusion ≫ productSnd Q.toCommDGAlgebra Q.toCommDGAlgebra :
    (endpointTarget f).toCommDGAlgebra ⟶ Q.toCommDGAlgebra)

def endpoints : relativePath f ⟶ endpointTarget f :=
  fiberPair f₀ f₀ (evaluation f 0) (evaluation f 1) (by
    change ((relativePathInclusion f ≫ relativeEvaluation f 0) ≫ f₀) =
      (relativePathInclusion f ≫ relativeEvaluation f 1) ≫ f₀
    rw [Category.assoc, Category.assoc, relative_eval_over f 1])

@[simp] theorem endpoints_first : endpoints f ≫ firstEndpoint f = evaluation f 0 := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  rfl

@[simp] theorem endpoints_second : endpoints f ≫ secondEndpoint f = evaluation f 1 := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  rfl

end FiberProduct

section Comparison

open HomologicalComplex

variable {Q B : Affine.NonpositiveCDGA.{u,v} k} (f : Q ⟶ B)

private def kernelSequence : ShortComplex (ModuleCochain.{u,v} k) :=
  ShortComplex.mk (kernelTerms f.chainMap).inclusion f.chainMap (by
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact x.property)

private theorem kernel_acyclic (h : Affine.NonpositiveCDGA.DegreewiseSurjective f)
    (hq : Affine.NonpositiveCDGA.IsQuasiIso f) : (kernelTerms f.chainMap).complex.Acyclic := by
  have hs : (kernelSequence f).ShortExact := by
    apply shortExact_of_degreewise_shortExact
    intro i
    exact LinearMap.shortExact_shortComplexKer (h i)
  exact hs.acyclic_X₁ hq

private theorem kernel_primitive_zero (h : Affine.NonpositiveCDGA.DegreewiseSurjective f)
    (hq : Affine.NonpositiveCDGA.IsQuasiIso f) {w : Q.complex.X 0}
    (hw : f.chainMap.f 0 w = 0) :
    ∃ z : Q.complex.X (-1), f.chainMap.f (-1) z = 0 ∧ Q.complex.d (-1) 0 z = w := by
  let K := (kernelTerms f.chainMap).complex
  let x : K.X 0 := ⟨w, hw⟩
  have hx : K.d 0 1 x = 0 := Subtype.ext (Q.d_zero_apply w)
  have hh : (K.sc' (-1) 0 1).Exact :=
    (K.exactAt_iff' (-1) 0 1 (by simp) (by simp)).1 (kernel_acyclic f h hq 0)
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff (K.sc' (-1) 0 1)).1 hh x hx
  exact ⟨z.val, z.property, congrArg Subtype.val hz⟩

private def kernelToEndpointTarget :
    (kernelTerms f.chainMap).complex ⟶ (endpointTarget f).complex :=
  CochainComplex.ofHom (fun i =>
    ModuleCat.ofHom
      (((LinearMap.inr k (Q.complex.X i) (Q.complex.X i)).comp
        ((kernelTerms f.chainMap).term i).subtype).codRestrict
        ((fiberTerms (f : Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra) f).term i) (by
          intro x
          apply (mem_fiberTerms _ _ i (0,x.val)).2
          rw [map_zero]
          exact x.property.symm))) (by
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (map_zero (Q.complex.d i (i+1)).hom) rfl)

private def endpointSequence : ShortComplex (ModuleCochain.{u,v} k) :=
  ShortComplex.mk (kernelToEndpointTarget f) (firstEndpoint f).chainMap (by
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

private theorem endpointSequence_shortExact : (endpointSequence f).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  apply ModuleCat.shortComplex_shortExact
  · intro z
    constructor
    · intro hz
      have h0 : z.val.1 = 0 := hz
      have hq := (mem_fiberTerms _ _ i z.val).1 z.property
      change f.chainMap.f i z.val.1 = f.chainMap.f i z.val.2 at hq
      rw [h0, map_zero] at hq
      exact ⟨⟨z.val.2, hq.symm⟩, Subtype.ext (Prod.ext h0.symm rfl)⟩
    · rintro ⟨x,rfl⟩
      rfl
  · intro x y e
    exact Subtype.ext (congrArg (fun z => z.val.2) e)
  · intro x
    exact ⟨⟨(x,x), (mem_fiberTerms _ _ i (x,x)).2 rfl⟩, rfl⟩

theorem firstEndpoint_quasiIso (h : Affine.NonpositiveCDGA.DegreewiseSurjective f)
    (hq : Affine.NonpositiveCDGA.IsQuasiIso f) :
    Affine.NonpositiveCDGA.IsQuasiIso (firstEndpoint f) := by
  change QuasiIso (endpointSequence f).g
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hs := endpointSequence_shortExact f
  have hk := kernel_acyclic f h hq
  have hm : Mono (homologyMap (endpointSequence f).g i) :=
    (hs.homology_exact₂ i).mono_g
      ((((endpointSequence f).X₁.exactAt_iff_isZero_homology i).1 (hk i)).eq_of_src _ _)
  have he : Epi (homologyMap (endpointSequence f).g i) :=
    (hs.homology_exact₃ i (i+1) rfl).epi_f
      ((((endpointSequence f).X₁.exactAt_iff_isZero_homology (i+1)).1 (hk (i+1))).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

theorem endpoints_quasiIso (h : Affine.NonpositiveCDGA.DegreewiseSurjective f)
    (hq : Affine.NonpositiveCDGA.IsQuasiIso f) :
    Affine.NonpositiveCDGA.IsQuasiIso (endpoints f) := by
  change QuasiIso (endpoints f).chainMap
  have h1 : QuasiIso (firstEndpoint f).chainMap := firstEndpoint_quasiIso f h hq
  apply (quasiIso_iff_comp_right (endpoints f).chainMap (firstEndpoint f).chainMap).1
  have he : (endpoints f).chainMap ≫ (firstEndpoint f).chainMap = (evaluation f 0).chainMap :=
    congrArg Affine.CommDGAlgebra.Hom.chainMap (endpoints_first f)
  rw [he]
  exact truncated_evaluation_quasiIso f

private def interpolation (i : ℤ) (x y : Q.complex.X i) (z : Coefficients (Q.complex.X (i-1))) :
    term Q.complex i :=
  (Finsupp.single 0 x + Finsupp.single 1 (y-x), z)

private theorem interpolation_eval (i : ℤ) (x y : Q.complex.X i)
    (z : Coefficients (Q.complex.X (i-1))) :
    endpoint Q.complex 0 i (interpolation i x y z) = x ∧
      endpoint Q.complex 1 i (interpolation i x y z) = y := by
  change evaluate (0 : k) (Finsupp.single 0 x + Finsupp.single 1 (y-x)) = x ∧
    evaluate (1 : k) (Finsupp.single 0 x + Finsupp.single 1 (y-x)) = y
  simp [add_sub_cancel]

private def interpolationLift (i : ℤ) (hi : i≤0) (x y : Q.complex.X i)
    (z : Coefficients (Q.complex.X (i-1))) (h : f.chainMap.f i x = f.chainMap.f i y)
    (hz : mapCoefficients (f.chainMap.f (i-1)).hom z = 0)
    (hd : i = 0 → differential Q.complex i (i+1) rfl (interpolation i x y z) = 0) :
    (relativePath f).complex.X i := by
  have hmem : interpolation i x y z ∈ (relativeTerms f).term i := by
    apply (mem_relativeTerms f i _).2
    rw [(interpolation_eval i x y z).1, interpolation, mapDegree_coordinates, hz, map_add,
      mapCoefficients_single, mapCoefficients_single, map_sub, h, sub_self, Finsupp.single_zero,
      add_zero]
    rfl
  refine ⟨⟨interpolation i x y z, hmem⟩, ?_⟩
  apply (mem_truncationDegree _ _ _).2
  refine ⟨fun hh => (not_lt_of_ge hi hh).elim, fun hh => ?_⟩
  apply Subtype.ext
  change (pathComplex Q.complex).d i (i+1) (interpolation i x y z) = 0
  rw [pathComplex_d Q.complex i (i+1) rfl]
  exact hd hh

private theorem interpolationLift_endpoints (i : ℤ) (hi : i≤0) (x y : Q.complex.X i)
    (z : Coefficients (Q.complex.X (i-1))) (h : f.chainMap.f i x = f.chainMap.f i y)
    (hz : mapCoefficients (f.chainMap.f (i-1)).hom z = 0)
    (hd : i = 0 → differential Q.complex i (i+1) rfl (interpolation i x y z) = 0) :
    ((endpoints f).chainMap.f i (interpolationLift f i hi x y z h hz hd)).val = (x,y) :=
  Prod.ext (interpolation_eval i x y z).1 (interpolation_eval i x y z).2

set_option maxHeartbeats 1200000 in
theorem endpoints_surjective (h : Affine.NonpositiveCDGA.DegreewiseSurjective f)
    (hq : Affine.NonpositiveCDGA.IsQuasiIso f) :
    Affine.NonpositiveCDGA.DegreewiseSurjective (endpoints f) := by
  intro i a
  change ∃ x : (relativePath f).complex.X i, (endpoints f).chainMap.f i x = a
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have ha := (mem_fiberTerms _ _ i a.val).1 a.property
    refine ⟨interpolationLift f i hi.le a.val.1 a.val.2 0 ha (map_zero _) (fun e => (hi.ne e).elim), ?_⟩
    exact Subtype.ext (interpolationLift_endpoints f i hi.le a.val.1 a.val.2 0 ha _ _)
  · have ha := (mem_fiberTerms _ _ 0 a.val).1 a.property
    let x := a.val.1
    let y := a.val.2
    change f.chainMap.f 0 x = f.chainMap.f 0 y at ha
    obtain ⟨z, hz, hd⟩ := kernel_primitive_zero f h hq
      (w := y-x) (by rw [map_sub, ha, sub_self])
    let q : Coefficients (Q.complex.X (0-1)) := Finsupp.single 0 (-z)
    have hq0 : mapCoefficients (f.chainMap.f (0-1)).hom q = 0 := by
      change mapCoefficients (f.chainMap.f (-1)).hom (Finsupp.single 0 (-z)) = 0
      rw [mapCoefficients_single, map_neg]
      change Finsupp.single 0 (-(f.chainMap.f (-1) z)) = 0
      simp [hz]
    have hc : differential Q.complex 0 (0+1) rfl (interpolation 0 x y q) = 0 := by
      rw [interpolation, differential_coordinates Q.complex 0 (0+1) rfl]
      have hd0 : (Q.complex.d 0 (0+1)).hom = 0 := LinearMap.ext fun a => Q.d_zero_apply a
      change (_, _) = (0,0)
      simp only [hd0, mapCoefficients_zero_apply, map_add, derivative_single_zero,
        derivative_single_succ, Nat.cast_one, one_smul, zero_add, Int.negOnePow_zero]
      have ht : transport Q.complex 0 (0+1-1) (by decide) = LinearMap.id :=
        transport_refl Q.complex 0
      rw [ht, mapCoefficients_id_apply]
      have hd1 : mapCoefficients (Q.complex.d (0-1) (0+1-1)).hom q =
          Finsupp.single 0 (-(y-x)) := by
        change mapCoefficients (Q.complex.d (-1) 0).hom (Finsupp.single 0 (-z)) = _
        rw [mapCoefficients_single, map_neg]
        exact congrArg (fun a => Finsupp.single 0 (-a)) hd
      rw [hd1, ← Finsupp.single_add, neg_add_cancel, Finsupp.single_zero]
    refine ⟨interpolationLift f 0 le_rfl x y q ha hq0 (fun _ => hc), ?_⟩
    exact Subtype.ext (interpolationLift_endpoints f 0 le_rfl x y q ha hq0 _)
  · refine ⟨0, (endpointTarget f).nonpositive i hi |>.elim _ _⟩

end Comparison

section Models

open Specs.DerivedFormalization.Affine.PolynomialPath
  (AlgebraPathModel ModulePathModel RelativePathModel ground)

def modulePathModel {A : Affine.CommDGAlgebra.{u,v} k} (M : A.Module) :
    ModulePathModel M where
  obj := pathModule M
  coordinates _ := LinearEquiv.refl _ _
  constantMap := constantModule M
  evaluation := endpointModule M
  homotopy := gradedIntegral M
  primitiveHomotopy := gradedContraction M
  d_coordinates i j e x := by
    change (pathComplex (M.complex ())).d i j x = _
    rw [pathComplex_d (M.complex ()) i j e]
    rfl
  action_coordinates i j n h x a := by
    obtain ⟨p,q⟩ := x
    exact action_coordinates M i j n h p q a
  constant_coordinates _ _ := rfl
  evaluation_coordinates _ _ _ := rfl
  integral_coordinates _ _ _ _ := rfl
  primitive_coordinates _ _ _ _ := rfl
  endpoints_homotopic := gradedIntegral_homotopy M
  contraction_at_zero := gradedContraction_homotopy M

theorem module_path_construction :
    Specs.DerivedFormalization.Affine.PolynomialPath.ModulePathConstruction.{u,v} :=
  fun M => ⟨modulePathModel M⟩

def algebraPathModel (A : Affine.CommDGAlgebra.{u,v} k) : AlgebraPathModel A where
  obj := pathAlgebra A
  coordinates _ := LinearEquiv.refl _ _
  constantMap := constantAlgebra A
  evaluation := endpointAlgebra A
  d_coordinates i j e x := by
    change (pathComplex A.complex).d i j x = _
    rw [pathComplex_d A.complex i j e]
    rfl
  multiplication i j n h x y := by
    obtain ⟨p,q⟩ := x
    obtain ⟨r,s⟩ := y
    exact pathMul_coordinates A i j n h p q r s
  constant_coordinates _ _ := rfl
  evaluation_coordinates _ _ _ := rfl
  constant_evaluation := constant_endpointAlgebra A

theorem algebra_path_construction :
    Specs.DerivedFormalization.Affine.PolynomialPath.AlgebraPathConstruction.{u,v} :=
  fun A => ⟨algebraPathModel A⟩

theorem tensor_coordinates :
    Specs.DerivedFormalization.Affine.PolynomialPath.TensorCoordinates.{u,v} := by
  intro k _ V _ _
  exact ⟨TensorProduct.finsuppScalarRight k k V ℕ, fun x p n =>
    TensorProduct.finsuppScalarRight_apply_tmul_apply x p n⟩

/-- Polynomial differential forms on the affine line. -/
def deRham (k : Type u) [Field k] [CharZero k] :
    Affine.CommDGAlgebra.{u,u} k := pathAlgebra (ground k).toCommDGAlgebra

def t (k : Type u) [Field k] [CharZero k] : (deRham k).complex.X 0 :=
  (Finsupp.single 1 (ground k).one, 0)

def dt (k : Type u) [Field k] [CharZero k] : (deRham k).complex.X 1 :=
  (0, Finsupp.single 0 (ground k).one)

private theorem ground_vanishes (k : Type u) [Field k] [CharZero k] (i : ℤ) (h : i ≠ 0) :
    Subsingleton ((ground k).complex.X i) :=
  ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k k) i h)

/-- The degree-zero forms, written as polynomials. -/
def deRhamDegreeZero (k : Type u) [Field k] [CharZero k] :
    (deRham k).complex.X 0 ≃ₗ[k] Coefficients k := by
  let := ground_vanishes k (-1) (by decide)
  change (Coefficients k × Coefficients ((ground k).complex.X (-1))) ≃ₗ[k] Coefficients k
  refine LinearEquiv.ofLinearMap (LinearMap.fst k _ _) (LinearMap.inl k _ _) rfl ?_
  apply LinearMap.ext
  rintro ⟨p,q⟩
  exact Prod.ext rfl (Finsupp.ext fun _ => Subsingleton.elim _ _)

/-- The degree-one forms, written as polynomial coefficients of dt. -/
def deRhamDegreeOne (k : Type u) [Field k] [CharZero k] :
    (deRham k).complex.X 1 ≃ₗ[k] Coefficients k := by
  let := ground_vanishes k 1 (by decide)
  change (Coefficients ((ground k).complex.X 1) × Coefficients k) ≃ₗ[k] Coefficients k
  refine LinearEquiv.ofLinearMap (LinearMap.snd k _ _) (LinearMap.inr k _ _) rfl ?_
  apply LinearMap.ext
  rintro ⟨p,q⟩
  exact Prod.ext (Finsupp.ext fun _ => Subsingleton.elim _ _) rfl

private theorem deRham_vanishes (k : Type u) [Field k] [CharZero k] (i : ℤ)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : Subsingleton ((deRham k).complex.X i) := by
  let := ground_vanishes k i h0
  let := ground_vanishes k (i-1) (by omega)
  exact ⟨fun x y => Prod.ext
    (Finsupp.ext fun _ => Subsingleton.elim _ _) (Finsupp.ext fun _ => Subsingleton.elim _ _)⟩

/-- The two nonzero form degrees give these polynomial and one-form coordinates
on each homogeneous term of the tensor product. -/
def tensorPathDegree (X : ModuleCochain.{u,v} k) (n : ℤ) :
    (TensorProduct k (X.X n) ((deRham k).complex.X 0) ×
      TensorProduct k (X.X (n-1)) ((deRham k).complex.X 1)) ≃ₗ[k] term X n :=
  ((TensorProduct.congr (LinearEquiv.refl k (X.X n)) (deRhamDegreeZero k)).trans
    (TensorProduct.finsuppScalarRight k k _ ℕ)).prodCongr
      ((TensorProduct.congr (LinearEquiv.refl k (X.X (n-1))) (deRhamDegreeOne k)).trans
        (TensorProduct.finsuppScalarRight k k _ ℕ))

theorem de_rham_tensor_coordinates :
    Specs.DerivedFormalization.Affine.PolynomialPath.DeRhamTensorCoordinates.{u,v} := by
  intro k _ _
  refine ⟨algebraPathModel (ground k).toCommDGAlgebra, deRham_vanishes k, ?_⟩
  intro X n
  refine ⟨tensorPathDegree X n, ?_, ?_⟩
  · intro x p a
    let e := TensorProduct.finsuppScalarRight k k (X.X n) ℕ
    let E := TensorProduct.congr (LinearEquiv.refl k (X.X n)) (deRhamDegreeZero k)
    change e (E (TensorProduct.tmul k x p)) a = _
    exact (congrArg (fun z => e z a)
      (TensorProduct.congr_tmul (LinearEquiv.refl k (X.X n)) (deRhamDegreeZero k) x p)).trans
        (TensorProduct.finsuppScalarRight_apply_tmul_apply x (deRhamDegreeZero k p) a)
  · intro x q a
    let e := TensorProduct.finsuppScalarRight k k (X.X (n-1)) ℕ
    let E := TensorProduct.congr (LinearEquiv.refl k (X.X (n-1))) (deRhamDegreeOne k)
    change e (E (TensorProduct.tmul k x q)) a = _
    exact (congrArg (fun z => e z a)
      (TensorProduct.congr_tmul (LinearEquiv.refl k (X.X (n-1))) (deRhamDegreeOne k) x q)).trans
        (TensorProduct.finsuppScalarRight_apply_tmul_apply x (deRhamDegreeOne k q) a)

theorem de_rham_algebra : Specs.DerivedFormalization.Affine.PolynomialPath.DeRhamAlgebra.{u} := by
  intro k _ _
  let R := (ground k).toCommDGAlgebra
  refine ⟨algebraPathModel R, t k, dt k, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change (pathComplex R.complex).d 0 1 (Finsupp.single 1 (ground k).one, 0) = _
    rw [pathComplex_d R.complex 0 1 (by decide)]
    change differential R.complex 0 1 (by decide) (Finsupp.single 1 (ground k).one, 0) =
      (0, Finsupp.single 0 (ground k).one)
    rw [differential_coordinates R.complex 0 1 (by decide)]
    have he : (R.complex.d 0 1).hom (ground k).one = 0 := R.toDGAlgebra.d_id ()
    simp only [mapCoefficients_single, he, Finsupp.single_zero, map_zero, zero_add,
      Int.negOnePow_zero, one_smul]
    have ht : transport R.complex 0 (1-1) (by decide) = LinearMap.id := transport_refl _ 0
    rw [ht, mapCoefficients_id_apply, derivative_single_succ, Nat.cast_one, one_smul]
  · change (pathComplex R.complex).d 1 2 (0, Finsupp.single 0 (ground k).one) = 0
    rw [pathComplex_d R.complex 1 2 (by decide)]
    change differential R.complex 1 2 (by decide) (0, Finsupp.single 0 (ground k).one) = (0,0)
    rw [differential_coordinates R.complex 1 2 (by decide)]
    have he : (R.complex.d (1-1) (2-1)).hom (ground k).one = 0 := R.toDGAlgebra.d_id ()
    simp only [map_zero, mapCoefficients_single, he, Finsupp.single_zero, smul_zero, add_zero]
  · change pathMul R 1 1 2 rfl (0, Finsupp.single 0 (ground k).one)
      (0, Finsupp.single 0 (ground k).one) = 0
    rw [pathMul_coordinates R 1 1 2 rfl]
    simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add]
    rfl
  · exact deRham_vanishes k
  · intro c
    change evaluate c (Finsupp.single 1 (ground k).one) = c • (ground k).one ∧
      evaluate c (0 : Coefficients (R.complex.X 1)) = 0
    simp

end Models

section UniversalProperties

variable {Q B : Affine.NonpositiveCDGA.{u,v} k} (f : Q ⟶ B)

local notation "Q₀" => Q.toCommDGAlgebra
local notation "B₀" => B.toCommDGAlgebra
local notation "f₀" => (f : Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra)

/-- The common value in B of a relative polynomial path. -/
def relativeAugmentation : relativeAlgebra f ⟶ B₀ :=
  relativeEvaluation f 0 ≫ f₀

theorem relative_square :
    relativeInclusion f ≫ pathAlgebraMap f₀ = relativeAugmentation f ≫ constantAlgebra B₀ := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (mem_relativeTerms f i z.val).1 z.property

theorem relative_pullback (D : Affine.CommDGAlgebra.{u,v} k) (a : D ⟶ pathAlgebra Q₀)
    (b : D ⟶ B₀) (h : a ≫ pathAlgebraMap f₀ = b ≫ constantAlgebra B₀) :
    ∃! g : D ⟶ relativeAlgebra f,
      g ≫ relativeInclusion f = a ∧ g ≫ relativeAugmentation f = b := by
  have hb : a ≫ endpointAlgebra Q₀ 0 ≫ f₀ = b := calc
    _ = (a ≫ pathAlgebraMap f₀) ≫ endpointAlgebra B₀ 0 := by
      rw [Category.assoc, endpointAlgebra_natural f₀ 0]
    _ = b := by
      rw [h, Category.assoc, constant_endpointAlgebra, Category.comp_id]
  have hm (i : ℤ) (x : D.complex.X i) :
      a.chainMap.f i x ∈ (relativeTerms f).term i := by
    have he : a ≫ pathAlgebraMap f₀ = a ≫ endpointAlgebra Q₀ 0 ≫ f₀ ≫ constantAlgebra B₀ := by
      rw [← Category.assoc (endpointAlgebra Q₀ 0), ← Category.assoc a, hb, h]
    exact (mem_relativeTerms f i (a.chainMap.f i x)).2
      (CategoryTheory.congr_fun (congrArg (fun g => g.chainMap.f i) he) x)
  let g := (relativeTerms f).factor a hm
  have hg : g ≫ relativeInclusion f = a := (relativeTerms f).factor_inclusion a hm
  refine ⟨g, ⟨hg, ?_⟩, ?_⟩
  · unfold relativeAugmentation relativeEvaluation
    rw [Category.assoc, ← Category.assoc g, hg, hb]
  · intro g' hg'
    exact (relativeTerms f).inclusion_cancel (hg'.1.trans hg.symm)

theorem endpointTarget_square : firstEndpoint f ≫ f = secondEndpoint f ≫ f := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (mem_fiberTerms f₀ f₀ i z.val).1 z.property

/-- The map into (Q	imes_B Q) of two maps with common augmentation. -/
def toEndpointTarget {D : Affine.NonpositiveCDGA.{u,v} k} (a b : D ⟶ Q)
    (h : a ≫ f = b ≫ f) : D ⟶ endpointTarget f :=
  fiberPair f₀ f₀ a b (show
    (a : D.toCommDGAlgebra ⟶ Q₀) ≫ f₀ = (b : D.toCommDGAlgebra ⟶ Q₀) ≫ f₀ from h)

@[simp] theorem toEndpointTarget_first {D : Affine.NonpositiveCDGA.{u,v} k} (a b : D ⟶ Q)
    (h : a ≫ f = b ≫ f) : toEndpointTarget f a b h ≫ firstEndpoint f = a := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  rfl

@[simp] theorem toEndpointTarget_second {D : Affine.NonpositiveCDGA.{u,v} k} (a b : D ⟶ Q)
    (h : a ≫ f = b ≫ f) : toEndpointTarget f a b h ≫ secondEndpoint f = b := by
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  rfl

theorem endpointTarget_pullback (D : Affine.NonpositiveCDGA.{u,v} k) (a b : D ⟶ Q)
    (h : a ≫ f = b ≫ f) :
    ∃! g : D ⟶ endpointTarget f, g ≫ firstEndpoint f = a ∧ g ≫ secondEndpoint f = b := by
  refine ⟨toEndpointTarget f a b h, ⟨toEndpointTarget_first f a b h,
    toEndpointTarget_second f a b h⟩, ?_⟩
  intro g hg
  apply Affine.CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact CategoryTheory.congr_fun (congrArg (fun g => g.chainMap.f i) hg.1) x
  · exact CategoryTheory.congr_fun (congrArg (fun g => g.chainMap.f i) hg.2) x

/-- The relative path under A uses the same constant map as the endpoint section. -/
def under {A : Affine.NonpositiveCDGA.{u,v} k} (a : A ⟶ Q) : CategoryTheory.Under A :=
  CategoryTheory.Under.mk (a ≫ constants f)

theorem under_evaluation {A : Affine.NonpositiveCDGA.{u,v} k} (a : A ⟶ Q) (c : k) :
    (under f a).hom ≫ evaluation f c = a := by
  change (a ≫ constants f) ≫ evaluation f c = a
  rw [Category.assoc, constants_evaluation, Category.comp_id]

end UniversalProperties

section RelativeModel

open Specs.DerivedFormalization.Affine.PolynomialPath (RelativePathModel)

variable {Q B : Affine.NonpositiveCDGA.{u,v} k} (f : Q ⟶ B)

set_option maxHeartbeats 1500000 in
def relativePathModel : RelativePathModel f (algebraPathModel Q.toCommDGAlgebra)
    (algebraPathModel B.toCommDGAlgebra) where
  coefficientMap := pathAlgebraMap (f : Q.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
  map_coordinates _ _ := rfl
  relative := relativeAlgebra f
  includeRelative := relativeInclusion f
  augmentRelative := relativeAugmentation f
  relative_square := relative_square f
  relative_pullback := relative_pullback f
  relativeConstant := relativeConstant f
  relative_constant := (relativeTerms f).factor_inclusion _ _
  relative_section := relativeConstant_eval f 0
  contractingHomotopy := relativeContraction f
  contraction_coordinates _ _ _ _ := rfl
  contraction_in_kernel i j e x :=
    endpoint_zero_contraction (X := Q.complex) i j e x.val
  contraction_equation := relativeContraction_equation f
  truncated := relativePath f
  includeTruncation := relativePathInclusion f
  truncation_injective _ := Subtype.val_injective
  truncation_range i x := by
    change (∃ y : truncationDegree (relativeAlgebra f) i, y.val = x) ↔ _
    exact (show (∃ y : truncationDegree (relativeAlgebra f) i, y.val = x) ↔
      x ∈ truncationDegree (relativeAlgebra f) i from
        ⟨fun ⟨y,h⟩ => h ▸ y.property, fun h => ⟨⟨x,h⟩,rfl⟩⟩).trans
          (mem_truncationDegree (relativeAlgebra f) i x)
  constants := constants f
  constants_truncate := (truncationTerms (relativeAlgebra f)).factor_inclusion _ _
  inclusion_comparison := by
    let : QuasiIso (relativeEvaluation f 0).chainMap := relative_evaluation_quasiIso f
    exact (quasiIso_iff_comp_right (relativePathInclusion f).chainMap
      (relativeEvaluation f 0).chainMap).1 (truncated_evaluation_quasiIso f)
  truncated_comparison := truncated_evaluation_quasiIso f
  target := endpointTarget f
  first := firstEndpoint f
  second := secondEndpoint f
  same_augmentation := endpointTarget_square f
  target_pullback := endpointTarget_pullback f
  endpoints := endpoints f
  first_eval := congrArg Affine.CommDGAlgebra.Hom.chainMap (endpoints_first f)
  second_eval := congrArg Affine.CommDGAlgebra.Hom.chainMap (endpoints_second f)
  constant_first := (congrArg (fun e => constants f ≫ e) (endpoints_first f)).trans
    (constants_evaluation f 0)
  constant_second := (congrArg (fun e => constants f ≫ e) (endpoints_second f)).trans
    (constants_evaluation f 1)
  trivial_fibration h hq := ⟨endpoints_surjective f h hq, endpoints_quasiIso f h hq⟩

theorem relative_path_construction :
    Specs.DerivedFormalization.Affine.PolynomialPath.RelativePathConstruction.{u,v} :=
  fun f => ⟨algebraPathModel _, algebraPathModel _, ⟨relativePathModel f⟩⟩

end RelativeModel

end DerivedFormalization.Affine.PolynomialPath
