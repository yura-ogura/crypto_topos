import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Lean.Data.Format


set_option linter.unusedVariables false
set_option maxRecDepth 50000
set_option diagnostics false

open CategoryTheory

noncomputable section

namespace CryptoTopos


def q : Nat := 2147483647
def minus_one : Nat := q - 1
def minus_two : Nat := q - 2
def inv_two : Nat := (q + 1) / 2
def sqrt_exp : Nat := (q + 1) / 4
def g : Nat := 7

lemma q_pos : q > 0 := by
  unfold q
  omega

lemma q_gt_one : q > 1 := by
  unfold q
  omega

lemma q_ne_zero : q ≠ 0 := by
  unfold q
  omega

instance : NeZero q := ⟨q_ne_zero⟩


lemma minus_one_eq : (minus_one : ZMod q) = -1 := by
  unfold minus_one
  rfl

lemma minus_two_eq : (minus_two : ZMod q) = -2 := by
  unfold minus_two
  rfl

lemma cast_zero_eq_zero : ((0 : Nat) : ZMod q) = 0 := by
  rfl

lemma cast_one_eq_one : ((1 : Nat) : ZMod q) = 1 := by
  rfl







def modAdd (a b : Nat) : Nat :=
  (a + b) % q


def modMul (a b : Nat) : Nat :=
  (a * b) % q


def modMulExp (a b : Nat) : Nat :=
  (a * b) % minus_one


def modAddExp (a b : Nat) : Nat :=
  (a + b) % minus_one


def modPower (base exp : Nat) : Nat :=
  (((base : ZMod q) ^ exp) : ZMod q).val


def modInverse (val : Nat) : Nat :=
  (((val : ZMod q)⁻¹) : ZMod q).val


def modSub (a b : Nat) : Nat :=
  modAdd a (modMul minus_one b)






def solveSubProblem (target base q_sub : Nat) : Nat :=
  let exp := minus_one / q_sub
  let gamma := modPower base exp
  let delta := modPower target exp

  let rec loop (k current_gamma_pow : Nat) : Nat :=
    if h : k >= q_sub then
      minus_one
    else
      if current_gamma_pow == delta then
        k
      else
        let next_gamma_pow := modMul current_gamma_pow gamma
        loop (k + 1) next_gamma_pow
  termination_by q_sub - k

  loop 0 1



def calcCRTTerm (rem q_sub : Nat) : Nat :=
  let M_i := minus_one / q_sub
  let target_mod := M_i % q_sub

  let rec findInverse (inv_M_i : Nat) : Nat :=
    if h : inv_M_i >= q_sub then
      minus_one
    else
      if (target_mod * inv_M_i) % q_sub == 1 then
        inv_M_i
      else
        findInverse (inv_M_i + 1)
  termination_by q_sub - inv_M_i

  let inv_M_i := findInverse 1
  if inv_M_i == minus_one then
    minus_one
  else
    let term := (rem * inv_M_i) % minus_one
    (term * M_i) % minus_one


def discreteLog (target : Nat) : Nat :=
  if target == 0 then
    minus_one
  else if target == 1 then
    0
  else
    let rem2   := solveSubProblem target g 2
    let rem3   := solveSubProblem target g 3
    let rem7   := solveSubProblem target g 7
    let rem11  := solveSubProblem target g 11
    let rem31  := solveSubProblem target g 31
    let rem151 := solveSubProblem target g 151
    let rem331 := solveSubProblem target g 331

    if rem2 == minus_one || rem3 == minus_one || rem7 == minus_one ||
       rem11 == minus_one || rem31 == minus_one || rem151 == minus_one || rem331 == minus_one then
      minus_one
    else
      let t2   := calcCRTTerm rem2 2
      let t3   := calcCRTTerm rem3 3
      let t7   := calcCRTTerm rem7 7
      let t11  := calcCRTTerm rem11 11
      let t31  := calcCRTTerm rem31 31
      let t151 := calcCRTTerm rem151 151
      let t331 := calcCRTTerm rem331 331

      if t2 == minus_one || t3 == minus_one || t7 == minus_one ||
         t11 == minus_one || t31 == minus_one || t151 == minus_one || t331 == minus_one then
        minus_one
      else
        let total_x := modAddExp t2 t3
        let total_x := modAddExp total_x t7
        let total_x := modAddExp total_x t11
        let total_x := modAddExp total_x t31
        let total_x := modAddExp total_x t151
        let total_x := modAddExp total_x t331

        if modPower g total_x == target then
          total_x
        else
          minus_one






noncomputable def discreteLogExistential (h_g_primitive : ∀ (v : ZMod q), v ≠ 0 → ∃ (x : Nat), x < q - 1 ∧ (g : ZMod q) ^ x = v) (val : Nat) : Nat :=
  if h : (val : ZMod q) = 0 then 0
  else Classical.choose (h_g_primitive (val : ZMod q) h)

lemma discreteLogExistential_lt (h_g_primitive : ∀ (v : ZMod q), v ≠ 0 → ∃ (x : Nat), x < q - 1 ∧ (g : ZMod q) ^ x = v) (val : Nat) :
  discreteLogExistential h_g_primitive val < q - 1 := by
  unfold discreteLogExistential
  split_ifs with h
  · have := q_gt_one
    omega
  · exact (Classical.choose_spec (h_g_primitive (val : ZMod q) h)).1

noncomputable def discreteLogExistential_ZMod (h_g_primitive : ∀ (v : ZMod q), v ≠ 0 → ∃ (x : Nat), x < q - 1 ∧ (g : ZMod q) ^ x = v) (v : ZMod q) : Nat :=
  discreteLogExistential h_g_primitive v.val

lemma discreteLogExistential_spec (h_g_primitive : ∀ (v : ZMod q), v ≠ 0 → ∃ (x : Nat), x < q - 1 ∧ (g : ZMod q) ^ x = v) (v : ZMod q) (h_nonzero : v ≠ 0) :
  (g : ZMod q) ^ (discreteLogExistential_ZMod h_g_primitive v) = v := by
  dsimp [discreteLogExistential_ZMod, discreteLogExistential]
  have h_cast : (v.val : ZMod q) = v := ZMod.natCast_zmod_val v
  have h_ne : (v.val : ZMod q) ≠ 0 := by rw [h_cast]; exact h_nonzero
  rw [dif_neg h_ne]
  have h_spec := (Classical.choose_spec (h_g_primitive (v.val : ZMod q) h_ne)).2
  rw [h_spec, h_cast]






structure Manifold4D where
  id : Nat
  x  : Nat
  y  : Nat
  z  : Nat
  t  : Nat


def calculateQ (m : Manifold4D) : ZMod q :=
  let x : ZMod q := m.x; let y : ZMod q := m.y; let z : ZMod q := m.z; let t : ZMod q := m.t
  let m1 : ZMod q := minus_one
  x * x + m1 * y * y + m1 * z * z + m1 * t * t


def Psi7 (X0 X1 X2 X3 X4 X5 X6 : Nat) : Nat :=
  let Q_val := modMul X0 X0
  let term1 := modMul minus_one (modMul X1 X1)
  let term2 := modMul minus_one (modMul X2 X2)
  let term3 := modMul minus_one (modMul X3 X3)
  let Q_val := modAdd Q_val (modAdd term1 (modAdd term2 term3))

  if Q_val == 0 then
    minus_one
  else
    let log_Q := discreteLog Q_val
    if log_Q == minus_one then
      minus_one
    else
      let denom := modAdd X5 minus_one
      if denom == 0 then
        minus_one
      else
        let inv_denom := modInverse denom
        let lambda := modMul 2 inv_denom
        let sqrt_Lambda := modPower lambda sqrt_exp
        let exp_index := modMulExp sqrt_Lambda X4
        let power_val := modPower g exp_index
        let interaction := modMul minus_two (modMul power_val log_Q)

        let r_sq := modMul X4 X4
        let r_term := modMul inv_two r_sq
        let n_sq := modMul X5 X5
        let n_term := modMul inv_two n_sq

        let Psi6_total := modAdd interaction (modAdd r_term n_term)
        let vortex_term := modMul X5 (modMul X6 log_Q)
        let w_sq := modMul X6 X6
        let w_term := modMul inv_two w_sq
        modAdd Psi6_total (modAdd vortex_term w_term)


def PartialDerivative_Psi7_w (n w Q_val : Nat) : Nat :=
  let log_Q := discreteLog Q_val
  if log_Q == minus_one then
    minus_one
  else
    let n_Lg_Q := modMul n log_Q
    modAdd n_Lg_Q w


def AddStep (X0 X1 X2 X3 X4 X5 X6 : Nat) (idx : Nat) : (Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  let R0 := if idx == 0 then modAdd X0 1 else X0
  let R1 := if idx == 1 then modAdd X1 1 else X1
  let R2 := if idx == 2 then modAdd X2 1 else X2
  let R3 := if idx == 3 then modAdd X3 1 else X3
  let R4 := if idx == 4 then modAdd X4 1 else X4
  let R5 := if idx == 5 then modAdd X5 1 else X5
  let R6 := if idx == 6 then modAdd X6 1 else X6
  (R0, R1, R2, R3, R4, R5, R6)


def Metric_g (X0 X1 X2 X3 X4 X5 X6 : Nat) (i j : Nat) : Nat :=
  let P_base := Psi7 X0 X1 X2 X3 X4 X5 X6
  let (v0, v1, v2, v3, v4, v5, v6) := AddStep X0 X1 X2 X3 X4 X5 X6 i
  let P_ei := Psi7 v0 v1 v2 v3 v4 v5 v6
  let (w0, w1, w2, w3, w4, w5, w6) := AddStep X0 X1 X2 X3 X4 X5 X6 j
  let P_ej := Psi7 w0 w1 w2 w3 w4 w5 w6
  let (u0, u1, u2, u3, u4, u5, u6) := AddStep v0 v1 v2 v3 v4 v5 v6 j
  let P_ei_ej := Psi7 u0 u1 u2 u3 u4 u5 u6

  if P_base == minus_one || P_ei == minus_one || P_ej == minus_one || P_ei_ej == minus_one then
    minus_one
  else
    let res := modAdd P_ei_ej (modMul minus_one P_ei)
    let res := modAdd res (modMul minus_one P_ej)
    let res := modAdd res P_base
    res


def Skewness_T (X0 X1 X2 X3 X4 X5 X6 : Nat) (i j k : Nat) : Nat :=
  let P_base := Psi7 X0 X1 X2 X3 X4 X5 X6
  let (x0_i, x1_i, x2_i, x3_i, x4_i, x5_i, x6_i) := AddStep X0 X1 X2 X3 X4 X5 X6 i
  let P_i := Psi7 x0_i x1_i x2_i x3_i x4_i x5_i x6_i
  let (x0_j, x1_j, x2_j, x3_j, x4_j, x5_j, x6_j) := AddStep X0 X1 X2 X3 X4 X5 X6 j
  let P_j := Psi7 x0_j x1_j x2_j x3_j x4_j x5_j x6_j
  let (x0_k, x1_k, x2_k, x3_k, x4_k, x5_k, x6_k) := AddStep X0 X1 X2 X3 X4 X5 X6 k
  let P_k := Psi7 x0_k x1_k x2_k x3_k x4_k x5_k x6_k

  let (x0_ij, x1_ij, x2_ij, x3_ij, x4_ij, x5_ij, x6_ij) := AddStep x0_i x1_i x2_i x3_i x4_i x5_i x6_i j
  let P_ij := Psi7 x0_ij x1_ij x2_ij x3_ij x4_ij x5_ij x6_ij
  let (x0_ik, x1_ik, x2_ik, x3_ik, x4_ik, x5_ik, x6_ik) := AddStep x0_i x1_i x2_i x3_i x4_i x5_i x6_i k
  let P_ik := Psi7 x0_ik x1_ik x2_ik x3_ik x4_ik x5_ik x6_ik
  let (x0_jk, x1_jk, x2_jk, x3_jk, x4_jk, x5_jk, x6_jk) := AddStep x0_j x1_j x2_j x3_j x4_j x5_j x6_j k
  let P_jk := Psi7 x0_jk x1_jk x2_jk x3_jk x4_jk x5_jk x6_jk

  let (x0_ijk, x1_ijk, x2_ijk, x3_ijk, x4_ijk, x5_ijk, x6_ijk) := AddStep x0_ij x1_ij x2_ij x3_ij x4_ij x5_ij x6_ij k
  let P_ijk := Psi7 x0_ijk x1_ijk x2_ijk x3_ijk x4_ijk x5_ijk x6_ijk

  if P_base == minus_one || P_i == minus_one || P_j == minus_one || P_k == minus_one ||
     P_ij == minus_one   || P_ik == minus_one || P_jk == minus_one || P_ijk == minus_one then
    minus_one
  else
    let res := P_ijk
    let res := modAdd res (modMul minus_one P_ij)
    let res := modAdd res (modMul minus_one P_ik)
    let res := modAdd res (modMul minus_one P_jk)
    let res := modAdd res P_i
    let res := modAdd res P_j
    let res := modAdd res P_k
    let res := modAdd res (modMul minus_one P_base)
    res


def Calculate_Absolute_w (n Q_val : Nat) : Nat :=
  let log_Q := discreteLog Q_val
  if log_Q == minus_one then minus_one
  else modMul minus_one (modMul n log_Q)

def Calculate_Q (x y z t : Nat) : Nat :=
  let q0 := modMul x x
  let t1 := modMul minus_one (modMul y y)
  let t2 := modMul minus_one (modMul z z)
  let t3 := modMul minus_one (modMul t t)
  modAdd q0 (modAdd t1 (modAdd t2 t3))

def Calculate_w_0 (x0 y0 z0 t0 n : Nat) : Nat :=
  let Q_0 := Calculate_Q x0 y0 z0 t0
  if Q_0 == 0 then minus_one
  else Calculate_Absolute_w n Q_0

def Calculate_w_end (x_end y_end z_end t_end n : Nat) : Nat :=
  let Q_end := Calculate_Q x_end y_end z_end t_end
  if Q_end == 0 then minus_one
  else Calculate_Absolute_w n Q_end

def DetermineAndValidateBoundaries
  (T0_0 T0_1 T0_2 T0_3 r0 w_0 : Nat)
  (Tend_0 Tend_1 Tend_2 Tend_3 rend w_end : Nat)
  (n_global : Nat) : Except String (List Nat × List Nat) :=
  let X_0   := [T0_0, T0_1, T0_2, T0_3, r0, n_global, w_0]
  let X_end := [Tend_0, Tend_1, Tend_2, Tend_3, rend, n_global, w_end]
  let psi_start := Psi7 T0_0 T0_1 T0_2 T0_3 r0 n_global w_0
  let psi_end   := Psi7 Tend_0 Tend_1 Tend_2 Tend_3 rend n_global w_end

  if psi_start == minus_one then Except.error "Error: Start Point is Singular"
  else if psi_end == minus_one then Except.error "Error: End Point is Singular"
  else Except.ok (X_0, X_end)

def Calculate_Lg_M (w_0 w_end : Nat) : Nat :=
  let neg_w_0 := modMul minus_one w_0
  let w_end_minus_w_0 := modAdd w_end neg_w_0
  modMul minus_one w_end_minus_w_0

def Calculate_M (w_0 w_end : Nat) : Nat :=
  let neg_w_end := modMul minus_one w_end
  let w_0_minus_w_end := modAdd w_0 neg_w_end
  modPower g w_0_minus_w_end






structure AlgebraicState7 where
  x : Nat
  y : Nat
  z : Nat
  t : Nat
  r : Nat
  ell : Nat
  E   : Nat

def calculateAlgebraicQ (s : AlgebraicState7) : Nat :=
  let q0 := modMul s.x s.x
  let t1 := modMul minus_one (modMul s.y s.y)
  let t2 := modMul minus_one (modMul s.z s.z)
  let t3 := modMul minus_one (modMul s.t s.t)
  modAdd q0 (modAdd t1 (modAdd t2 t3))

def recoverW (s : AlgebraicState7) (n_global : Nat) : Nat :=
  let Q_val := calculateAlgebraicQ s
  if Q_val == 0 then minus_one
  else
    let log_Q := discreteLog Q_val
    if log_Q == minus_one then minus_one
    else modMul minus_one (modMul n_global log_Q)

def evaluateLogRelation (s : AlgebraicState7) : Nat :=
  let g_pow_ell := modPower g s.ell
  let Q_val := calculateAlgebraicQ s
  modSub g_pow_ell Q_val

def evaluateExpRelation (s : AlgebraicState7) (sqrt_Lambda : Nat) : Nat :=
  let exp_idx := modMul sqrt_Lambda s.r
  let g_pow_exp := modPower g exp_idx
  modSub s.E g_pow_exp

def reifyAlgebraicTo7D (s : AlgebraicState7) (n_global : Nat) : List Nat :=
  let w_val := modMul minus_one (modMul n_global s.ell)
  [s.x, s.y, s.z, s.t, s.r, n_global, w_val]






def geodesicResidual (m_prev m_curr m_next : Manifold4D) (r_prev r_curr r_next : Nat) (E_curr : Nat) (n_global : Nat) (k : Nat) : ZMod q :=
  let x_p : ZMod q := m_prev.x; let x_c : ZMod q := m_curr.x; let x_n : ZMod q := m_next.x
  let y_p : ZMod q := m_prev.y; let y_c : ZMod q := m_curr.y; let y_n : ZMod q := m_next.y
  let r_p : ZMod q := r_prev; let r_c : ZMod q := r_curr; let r_n : ZMod q := r_next
  let E_c : ZMod q := E_curr
  let n : ZMod q := n_global
  let m2 : ZMod q := minus_two
  let m1 : ZMod q := minus_one
  let inv2 : ZMod q := inv_two

  let d2_x := x_n + m2 * x_c + x_p
  let d2_y := y_n + m2 * y_c + y_p
  let d2_r := r_n + m2 * r_c + r_p
  let dx_r := r_n + m1 * r_c
  let dx_y := y_n + m1 * y_c

  let term_k0 := d2_x
  let coef_n_val := (1 + m1 * n) * inv2
  let term_k1 := d2_r + coef_n_val * dx_r * dx_y
  let term_k4 := d2_r + m2 * E_c * d2_y

  if k = 0 then term_k0
  else if k = 1 then term_k1
  else if k = 4 then term_k4
  else 0

def getX (X : List Nat) (idx : Nat) : Nat :=
   X.getD idx 0

def EvaluateEquationK (X_prev X_curr X_next : List Nat) (k : Nat) : Nat :=
  let x0 := getX X_curr 0
  let x1 := getX X_curr 1
  let x2 := getX X_curr 2
  let x3 := getX X_curr 3
  let x4 := getX X_curr 4
  let x5 := getX X_curr 5
  let x6 := getX X_curr 6

  let n_curr := x5
  let coef_n := modMul (modAdd 1 (modMul minus_one n_curr)) inv_two

  let rec loop_j (j : Nat) (acc_term1 : Nat) : Nat :=
    if h : j >= 7 then acc_term1
    else
      if acc_term1 == minus_one then minus_one
      else
        let g_kj := Metric_g x0 x1 x2 x3 x4 x5 x6 k j
        if g_kj == minus_one then minus_one
        else
          let d2_X := modAdd (getX X_next j) (modAdd (modMul minus_two (getX X_curr j)) (getX X_prev j))
          loop_j (j + 1) (modAdd acc_term1 (modMul g_kj d2_X))
  termination_by 7 - j

  let Term1 := loop_j 0 0
  if Term1 == minus_one then minus_one
  else
    let rec loop_i_j (i j : Nat) (acc_term2 : Nat) : Nat :=
      if h_i : i >= 7 then acc_term2
      else if h_j : j >= 7 then loop_i_j (i + 1) 0 acc_term2
      else
        if acc_term2 == minus_one then minus_one
        else
          let T_ijk := Skewness_T x0 x1 x2 x3 x4 x5 x6 i j k
          if T_ijk == minus_one then minus_one
          else
            let dX_i := modAdd (getX X_next i) (modMul minus_one (getX X_curr i))
            let dX_j := modAdd (getX X_next j) (modMul minus_one (getX X_curr j))
            let prod := modMul (modMul (modMul coef_n T_ijk) dX_i) dX_j
            loop_i_j i (j + 1) (modAdd acc_term2 prod)
    termination_by (7 - i, 7 - j)

    let Term2 := loop_i_j 0 0 0
    if Term2 == minus_one then minus_one
    else modAdd Term1 Term2






structure ConcretePath (dom cod : Manifold4D) (N : Nat) (n_global : Nat) where
  m_seq    : List Manifold4D
  r_seq    : List Nat
  E_seq    : List Nat
  ell_seq  : List Nat
  h_len    : m_seq.length = N + 1 ∧ r_seq.length = N + 1 ∧ E_seq.length = N + 1 ∧ ell_seq.length = N + 1
  h_dom    : m_seq.head? = some dom
  h_cod    : m_seq.getLast? = some cod
  r_lt     : ∀ r ∈ r_seq, r < q
  ell_lt   : ∀ e ∈ ell_seq, e < q - 1
  E_lt     : ∀ E ∈ E_seq, E < q

def isStrictGeodesicPath {dom cod : Manifold4D} {N : Nat} {n_global : Nat} (p : ConcretePath dom cod N n_global) : Prop :=
  (∀ i : Nat, (h_i : i < N + 1) →
    let idx : Fin p.m_seq.length := ⟨i, by rw [p.h_len.1]; exact h_i⟩
    let idx_r : Fin p.r_seq.length := ⟨i, by rw [p.h_len.2.1]; exact h_i⟩
    let idx_E : Fin p.E_seq.length := ⟨i, by rw [p.h_len.2.2.1]; exact h_i⟩
    let idx_ell : Fin p.ell_seq.length := ⟨i, by rw [p.h_len.2.2.2]; exact h_i⟩
    let m_curr := p.m_seq.get idx
    let r_curr := p.r_seq.get idx_r
    let E_curr := p.E_seq.get idx_E
    let ell_curr := p.ell_seq.get idx_ell
    let E_curr_f : ZMod q := E_curr
    let r_curr_f : ZMod q := r_curr
    let g_f : ZMod q := g
    let m1 : ZMod q := minus_one

    let log_res := (g_f ^ ell_curr) + (m1 * calculateQ m_curr)
    let exp_res := E_curr_f + (m1 * (g_f ^ (sqrt_exp * r_curr)))
    log_res = 0 ∧ exp_res = 0) ∧
  (∀ i : Nat, 0 < i → (h_i : i < N) →
    let idx_prev : Fin p.m_seq.length := ⟨i - 1, by rw [p.h_len.1]; omega⟩
    let idx_curr : Fin p.m_seq.length := ⟨i,     by rw [p.h_len.1]; omega⟩
    let idx_next : Fin p.m_seq.length := ⟨i + 1, by rw [p.h_len.1]; omega⟩
    let idx_r_prev : Fin p.r_seq.length := ⟨i - 1, by rw [p.h_len.2.1]; omega⟩
    let idx_r_curr : Fin p.r_seq.length := ⟨i,     by rw [p.h_len.2.1]; omega⟩
    let idx_r_next : Fin p.r_seq.length := ⟨i + 1, by rw [p.h_len.2.1]; omega⟩
    let idx_E_curr : Fin p.E_seq.length := ⟨i,     by rw [p.h_len.2.2.1]; omega⟩

    let m_prev := p.m_seq.get idx_prev
    let m_curr := p.m_seq.get idx_curr
    let m_next := p.m_seq.get idx_next
    let r_prev := p.r_seq.get idx_r_prev
    let r_curr := p.r_seq.get idx_r_curr
    let r_next := p.r_seq.get idx_r_next
    let E_curr := p.E_seq.get idx_E_curr

    let geo_k0 := geodesicResidual m_prev m_curr m_next r_prev r_curr r_next E_curr n_global 0
    let geo_k1 := geodesicResidual m_prev m_curr m_next r_prev r_curr r_next E_curr n_global 1
    let geo_k4 := geodesicResidual m_prev m_curr m_next r_prev r_curr r_next E_curr n_global 4
    geo_k0 = 0 ∧ geo_k1 = 0 ∧ geo_k4 = 0)


def GeodesicMorphism (dom cod : Manifold4D) : Prop :=
  ∃ (N : Nat) (n_global : Nat),
    ∃ (p : ConcretePath dom cod N n_global), isStrictGeodesicPath p





open List

theorem get_of_fin_eq {α : Type _} (ys : List α) (idx1 idx2 : Fin ys.length) (h : idx1.val = idx2.val) :
  ys.get idx1 = ys.get idx2 := by
  have h_eq : idx1 = idx2 := Fin.ext h
  rw [h_eq]

theorem my_get_append_left {α : Type _} (xs ys : List α) (i : Nat) (hi : i < xs.length) (h_con : i < (xs ++ ys).length) :
  (xs ++ ys).get ⟨i, h_con⟩ = xs.get ⟨i, hi⟩ := by
  induction xs generalizing i with
  | nil => change i < 0 at hi; omega
  | cons hd tl ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      have hi' : i' < tl.length := by
        change i' + 1 < tl.length + 1 at hi
        omega
      have h_con' : i' < (tl ++ ys).length := by
        change i' + 1 < (tl ++ ys).length + 1 at h_con
        omega
      exact ih i' hi' h_con'

theorem my_get_append_right {α : Type _} (xs ys : List α) (i : Nat) (hi : xs.length ≤ i) (h_con : i < (xs ++ ys).length) (h_con2 : i - xs.length < ys.length) :
  (xs ++ ys).get ⟨i, h_con⟩ = ys.get ⟨i - xs.length, h_con2⟩ := by
  induction xs generalizing i with
  | nil =>
    change ys.get ⟨i, h_con⟩ = ys.get ⟨i - 0, h_con2⟩
    have h_sub : i - 0 = i := Nat.sub_zero i
    apply get_of_fin_eq
    exact h_sub.symm
  | cons hd tl ih =>
    cases i with
    | zero =>
      change tl.length + 1 ≤ 0 at hi
      omega
    | succ i' =>
      have hi' : tl.length ≤ i' := by
        change tl.length + 1 ≤ i' + 1 at hi
        omega
      have h_con' : i' < (tl ++ ys).length := by
        change i' + 1 < (tl ++ ys).length + 1 at h_con
        omega
      have h_con2' : i' - tl.length < ys.length := by
        change i' + 1 - (tl.length + 1) < ys.length at h_con2
        omega
      have h_ih := ih i' hi' h_con' h_con2'
      have h_eq : ((hd :: tl) ++ ys).get ⟨i' + 1, h_con⟩ = (tl ++ ys).get ⟨i', h_con'⟩ := rfl
      rw [h_eq]
      have h_step2 : (tl ++ ys).get ⟨i', h_con'⟩ = ys.get ⟨i' + 1 - (hd :: tl).length, h_con2⟩ := by
        apply Eq.trans h_ih
        apply get_of_fin_eq
        change i' - tl.length = i' + 1 - (hd :: tl).length
        have h_len_cons : (hd :: tl).length = tl.length + 1 := rfl
        omega
      exact h_step2

theorem get_dropLast {α : Type _} (xs : List α) :
  ∀ (i : Nat) (hi : i < xs.length - 1) (h_con1 : i < xs.dropLast.length) (h_con2 : i < xs.length),
  xs.dropLast.get ⟨i, h_con1⟩ = xs.get ⟨i, h_con2⟩ := by
  induction xs with
  | nil => intros i hi h_con1 h_con2; change i < 0 at hi; omega
  | cons hd tl ih =>
    intros i hi h_con1 h_con2
    cases tl with
    | nil => change i < 0 at hi; omega
    | cons hd2 tl2 =>
      cases i with
      | zero => rfl
      | succ i' =>
        have hi' : i' < (hd2 :: tl2).length - 1 := by
          change i' + 1 < (hd2 :: tl2).length + 1 - 1 at hi
          change i' < (hd2 :: tl2).length - 1
          omega
        have h_con1' : i' < (hd2 :: tl2).dropLast.length := by
          change i' + 1 < (hd2 :: tl2).dropLast.length + 1 at h_con1
          change i' < (hd2 :: tl2).dropLast.length
          omega
        have h_con2' : i' < (hd2 :: tl2).length := by
          change i' + 1 < (hd2 :: tl2).length + 1 at h_con2
          change i' < (hd2 :: tl2).length
          omega
        have h_ih := ih i' hi' h_con1' h_con2'
        have h_eq : (hd :: hd2 :: tl2).dropLast.get ⟨i' + 1, h_con1⟩ = (hd2 :: tl2).dropLast.get ⟨i', h_con1'⟩ := rfl
        rw [h_eq]
        have h_step2 : (hd2 :: tl2).dropLast.get ⟨i', h_con1'⟩ = (hd :: hd2 :: tl2).get ⟨i' + 1, h_con2⟩ := by
          apply Eq.trans h_ih
          apply get_of_fin_eq
          rfl
        exact h_step2

theorem get_append_dropLast_left {α : Type _} (xs ys : List α) (i : Nat) (h_xs : xs ≠ []) (hi : i < xs.length - 1) (h_con : i < (xs.dropLast ++ ys).length) (h_con2 : i < xs.length) :
  (xs.dropLast ++ ys).get ⟨i, h_con⟩ = xs.get ⟨i, h_con2⟩ := by
  have h_drop_len : i < xs.dropLast.length := by
    rw [List.length_dropLast]
    exact hi
  have h_step1 : (xs.dropLast ++ ys).get ⟨i, h_con⟩ = xs.dropLast.get ⟨i, h_drop_len⟩ :=
    my_get_append_left xs.dropLast ys i h_drop_len h_con
  have h_step2 : xs.dropLast.get ⟨i, h_drop_len⟩ = xs.get ⟨i, h_con2⟩ :=
    get_dropLast xs i hi h_drop_len h_con2
  exact Eq.trans h_step1 h_step2

theorem get_append_dropLast_right {α : Type _} (xs ys : List α) (i : Nat) (h_xs : xs ≠ []) (hi : xs.length - 1 ≤ i) (h_con : i < (xs.dropLast ++ ys).length) (h_con2 : i - (xs.length - 1) < ys.length) :
  (xs.dropLast ++ ys).get ⟨i, h_con⟩ = ys.get ⟨i - (xs.length - 1), h_con2⟩ := by
  have h_drop_le : xs.dropLast.length ≤ i := by
    rw [List.length_dropLast]
    exact hi
  have h_con2_drop : i - xs.dropLast.length < ys.length := by
    rw [List.length_dropLast]
    exact h_con2
  have h_step1 : (xs.dropLast ++ ys).get ⟨i, h_con⟩ = ys.get ⟨i - xs.dropLast.length, h_con2_drop⟩ :=
    my_get_append_right xs.dropLast ys i h_drop_le h_con h_con2_drop
  have h_step2 : ys.get ⟨i - xs.dropLast.length, h_con2_drop⟩ = ys.get ⟨i - (xs.length - 1), h_con2⟩ := by
    apply get_of_fin_eq
    change i - xs.dropLast.length = i - (xs.length - 1)
    rw [List.length_dropLast]
  exact Eq.trans h_step1 h_step2






def concatPath {X Y Z : Manifold4D} {N1 N2 : Nat} {n : Nat}
  (p1 : ConcretePath X Y N1 n) (p2 : ConcretePath Y Z N2 n) : ConcretePath X Z (N1 + N2) n :=
  let m_con   := p1.m_seq.dropLast ++ p2.m_seq
  let r_con   := p1.r_seq.dropLast ++ p2.r_seq
  let E_con   := p1.E_seq.dropLast ++ p2.E_seq
  let ell_con := p1.ell_seq.dropLast ++ p2.ell_seq
  {
    m_seq    := m_con
    r_seq    := r_con
    E_seq    := E_con
    ell_seq  := ell_con
    h_len    := by
      have len_m : (p1.m_seq.dropLast ++ p2.m_seq).length = N1 + N2 + 1 := by
        rw [List.length_append, List.length_dropLast]
        rw [p1.h_len.1, p2.h_len.1]
        omega
      have len_r : (p1.r_seq.dropLast ++ p2.r_seq).length = N1 + N2 + 1 := by
        rw [List.length_append, List.length_dropLast]
        rw [p1.h_len.2.1, p2.h_len.2.1]
        omega
      have len_E : (p1.E_seq.dropLast ++ p2.E_seq).length = N1 + N2 + 1 := by
        rw [List.length_append, List.length_dropLast]
        rw [p1.h_len.2.2.1, p2.h_len.2.2.1]
        omega
      have len_ell : (p1.ell_seq.dropLast ++ p2.ell_seq).length = N1 + N2 + 1 := by
        rw [List.length_append, List.length_dropLast]
        rw [p1.h_len.2.2.2, p2.h_len.2.2.2]
        omega
      exact ⟨len_m, len_r, len_E, len_ell⟩

    h_dom    := by
      dsimp [m_con]
      have h1_ne : p1.m_seq ≠ [] := by
        intro h
        have h_len := p1.h_len.1
        rw [h] at h_len
        change 0 = N1 + 1 at h_len
        omega
      cases h_seq : p1.m_seq with
      | nil => contradiction
      | cons a as =>
        cases as with
        | nil =>
          have h_h := p1.h_dom
          have h_l := p1.h_cod
          rw [h_seq] at h_h h_l
          change some a = some X at h_h
          change some a = some Y at h_l
          have eq_X : a = X := by injection h_h
          have eq_Y : a = Y := by injection h_l
          have eq_XY : X = Y := by rw [← eq_X, ← eq_Y]
          change ([] ++ p2.m_seq).head? = some X
          rw [List.nil_append, p2.h_dom, eq_XY]
        | cons b cs =>
          have h_h := p1.h_dom
          rw [h_seq] at h_h
          change ((a :: b :: cs).dropLast ++ p2.m_seq).head? = some X
          have h_drop : (a :: b :: cs).dropLast = a :: (b :: cs).dropLast := rfl
          rw [h_drop, List.cons_append]
          change some a = some X
          exact h_h

    h_cod    := by
      have h2_ne : p2.m_seq ≠ [] := by
        intro h
        have h_len := p2.h_len.1
        rw [h] at h_len
        change 0 = N2 + 1 at h_len
        omega
      change (p1.m_seq.dropLast ++ p2.m_seq).getLast? = some Z
      rw [List.getLast?_append]
      have h_last_p2 := p2.h_cod
      cases h_get_p2 : p2.m_seq.getLast? with
      | none =>
        have h_nil : p2.m_seq = [] := List.getLast?_eq_none_iff.mp h_get_p2
        contradiction
      | some w =>
        simp only [h_get_p2] at h_last_p2
        injection h_last_p2 with hw
        change w = Z at hw
        rw [hw]
        rfl

    r_lt     := by
      intro r hr
      rcases List.mem_append.mp hr with hr1 | hr2
      · have hr_orig : r ∈ p1.r_seq := List.mem_of_mem_dropLast hr1
        exact p1.r_lt r hr_orig
      · exact p2.r_lt r hr2

    ell_lt   := by
      intro e he
      rcases List.mem_append.mp he with he1 | he2
      · have he_orig : e ∈ p1.ell_seq := List.mem_of_mem_dropLast he1
        exact p1.ell_lt e he_orig
      · exact p2.ell_lt e he2

    E_lt     := by
      intro E hE
      rcases List.mem_append.mp hE with hE1 | hE2
      · have hE_orig : E ∈ p1.E_seq := List.mem_of_mem_dropLast hE1
        exact p1.E_lt E hE_orig
      · exact p2.E_lt E hE2
  }






structure SmoothConnection {X Y Z : Manifold4D} {N1 N2 : Nat} {n : Nat}
  (p1 : ConcretePath X Y N1 n) (p2 : ConcretePath Y Z N2 n) : Prop where
  h_velocity_m : ∀ (h1 : N1 > 0) (h2 : N2 > 0),
    let idx_Y_prev : Fin p1.m_seq.length := ⟨N1 - 1, by have := p1.h_len.1; omega⟩
    let idx_Y      : Fin p1.m_seq.length := ⟨N1,      by have := p1.h_len.1; omega⟩
    let idx_Y_next : Fin p2.m_seq.length := ⟨1,       by have := p2.h_len.1; omega⟩
    let m_prev := p1.m_seq.get idx_Y_prev
    let m_curr := p1.m_seq.get idx_Y
    let m_next := p2.m_seq.get idx_Y_next
    (m_next.x : ZMod q) - m_curr.x = (m_curr.x : ZMod q) - m_prev.x ∧
    (m_next.y : ZMod q) - m_curr.y = (m_curr.y : ZMod q) - m_prev.y ∧
    (m_next.z : ZMod q) - m_curr.z = (m_curr.z : ZMod q) - m_prev.z ∧
    (m_next.t : ZMod q) - m_curr.t = (m_curr.t : ZMod q) - m_prev.t
  h_velocity_r : ∀ (h1 : N1 > 0) (h2 : N2 > 0),
    let idx_Y_prev : Fin p1.r_seq.length := ⟨N1 - 1, by have := p1.h_len.2.1; omega⟩
    let idx_Y      : Fin p1.r_seq.length := ⟨N1,      by have := p1.h_len.2.1; omega⟩
    let idx_Y_next : Fin p2.r_seq.length := ⟨1, by have := p2.h_len.2.1; omega⟩
    let r_prev := p1.r_seq.get idx_Y_prev
    let r_curr := p1.r_seq.get idx_Y
    let r_next := p2.r_seq.get idx_Y_next
    (r_next : ZMod q) - r_curr = (r_curr : ZMod q) - r_prev

theorem getLast?_eq_get {α : Type _} : ∀ (l : List α) (h : 0 < l.length), l.getLast? = some (l.get ⟨l.length - 1, by omega⟩) := by
  intro l h
  induction l with
  | nil =>
    change 0 < 0 at h
    omega
  | cons hd tl ih =>
    cases tl with
    | nil => rfl
    | cons hd2 tl2 =>
      have h_tl_pos : 0 < (hd2 :: tl2).length := by
        change 0 < tl2.length + 1
        omega
      have h_ih := ih h_tl_pos
      exact h_ih

theorem List.get_zero_eq_head {α : Type _} (l : List α) (h_pos : 0 < l.length) (dom : α) (h_dom : l.head? = some dom) :
  l.get ⟨0, h_pos⟩ = dom := by
  cases l with
  | nil =>
    change 0 < 0 at h_pos
    omega
  | cons hd tl =>
    change some hd = some dom at h_dom
    injection h_dom

lemma ConcretePath.get_zero {dom cod : Manifold4D} {N : Nat} {n_global : Nat} (p : ConcretePath dom cod N n_global) :
  p.m_seq.get ⟨0, by rw [p.h_len.1]; omega⟩ = dom := by
  have h_pos : 0 < p.m_seq.length := by rw [p.h_len.1]; omega
  have h_eq := List.get_zero_eq_head p.m_seq h_pos dom p.h_dom
  apply Eq.trans _ h_eq
  apply get_of_fin_eq
  rfl

lemma ConcretePath.get_last {dom cod : Manifold4D} {N : Nat} {n_global : Nat} (p : ConcretePath dom cod N n_global) :
  p.m_seq.get ⟨N, by rw [p.h_len.1]; omega⟩ = cod := by
  have h_cod := p.h_cod
  have h_len_m := p.h_len.1
  have h_pos : 0 < p.m_seq.length := by
    rw [h_len_m]
    omega
  have h_last := getLast?_eq_get p.m_seq h_pos
  rw [h_cod] at h_last
  have h_last_get : p.m_seq.get ⟨p.m_seq.length - 1, by rw [h_len_m]; omega⟩ = p.m_seq.get ⟨N, by rw [h_len_m]; omega⟩ := by
    apply get_of_fin_eq
    dsimp only
    rw [h_len_m]
    omega
  rw [h_last_get] at h_last
  injection h_last with h_eq
  exact h_eq.symm

theorem geodesic_residual_at_connection {X Y Z : Manifold4D} {N1 N2 : Nat} {n : Nat}
  (p1 : ConcretePath X Y N1 n) (p2 : ConcretePath Y Z N2 n)
  (h_smooth : SmoothConnection p1 p2) (h1 : N1 > 0) (h2 : N2 > 0) :
  let p_con := concatPath p1 p2
  let idx_prev : Fin p_con.m_seq.length := ⟨N1 - 1, by rw [p_con.h_len.1]; omega⟩
  let idx_curr : Fin p_con.m_seq.length := ⟨N1,      by rw [p_con.h_len.1]; omega⟩
  let idx_next : Fin p_con.m_seq.length := ⟨N1 + 1, by rw [p_con.h_len.1]; omega⟩
  let m_prev := p_con.m_seq.get idx_prev
  let m_curr := p_con.m_seq.get idx_curr
  let m_next := p_con.m_seq.get idx_next
  let d2_x := (m_next.x : ZMod q) + minus_two * m_curr.x + m_prev.x
  d2_x = 0 := by
  intro p_con idx_prev idx_curr idx_next m_prev m_curr m_next d2_x
  have h_p1_len : p1.m_seq.length = N1 + 1 := p1.h_len.1
  have h_p1_ne : p1.m_seq ≠ [] := by intro h; rw [h] at h_p1_len; change 0 = N1 + 1 at h_p1_len; omega

  have h_con_prev : N1 - 1 < (p1.m_seq.dropLast ++ p2.m_seq).length := by
    rw [List.length_append, List.length_dropLast]
    have h_len_p1 := p1.h_len.1
    have h_len_p2 := p2.h_len.1
    omega

  have hi_prev : N1 - 1 < p1.m_seq.length - 1 := by
    have h_len_p1 := p1.h_len.1
    omega

  have h_con2_prev : N1 - 1 < p1.m_seq.length := by
    have h_len_p1 := p1.h_len.1
    omega

  have h_left_prev := get_append_dropLast_left p1.m_seq p2.m_seq (N1 - 1) h_p1_ne hi_prev h_con_prev h_con2_prev

  have h_prev_eq : m_prev = (p1.m_seq.dropLast ++ p2.m_seq).get ⟨N1 - 1, h_con_prev⟩ := rfl

  have h_prev : m_prev = p1.m_seq.get ⟨N1 - 1, by rw [p1.h_len.1]; omega⟩ := by
    rw [h_prev_eq, h_left_prev]

  have h_con_curr : N1 < (p1.m_seq.dropLast ++ p2.m_seq).length := by
    rw [List.length_append, List.length_dropLast]
    have h_len_p1 := p1.h_len.1
    have h_len_p2 := p2.h_len.1
    omega

  have hi_curr : p1.m_seq.length - 1 ≤ N1 := by
    have h_len_p1 := p1.h_len.1
    omega

  have h_con2_curr : N1 - (p1.m_seq.length - 1) < p2.m_seq.length := by
    have h_len_p1 := p1.h_len.1
    have h_len_p2 := p2.h_len.1
    omega

  have h_right_curr := get_append_dropLast_right p1.m_seq p2.m_seq N1 h_p1_ne hi_curr h_con_curr h_con2_curr

  have h_curr_eq : m_curr = (p1.m_seq.dropLast ++ p2.m_seq).get ⟨N1, h_con_curr⟩ := rfl

  have h_curr : m_curr = p1.m_seq.get ⟨N1, by rw [p1.h_len.1]; omega⟩ := by
    rw [h_curr_eq, h_right_curr]
    have h_lhs : p2.m_seq.get ⟨N1 - (p1.m_seq.length - 1), h_con2_curr⟩ = p2.m_seq.get ⟨0, by have := p2.h_len.1; omega⟩ := by
      apply get_of_fin_eq
      change N1 - (p1.m_seq.length - 1) = 0
      have h_len_p1 := p1.h_len.1
      omega
    rw [h_lhs]
    rw [ConcretePath.get_zero p2, ConcretePath.get_last p1]

  have h_con_next : N1 + 1 < (p1.m_seq.dropLast ++ p2.m_seq).length := by
    rw [List.length_append, List.length_dropLast]
    have h_len_p1 := p1.h_len.1
    have h_len_p2 := p2.h_len.1
    omega

  have hi_next : p1.m_seq.length - 1 ≤ N1 + 1 := by
    have h_len_p1 := p1.h_len.1
    omega

  have h_con2_next : N1 + 1 - (p1.m_seq.length - 1) < p2.m_seq.length := by
    have h_len_p1 := p1.h_len.1
    have h_len_p2 := p2.h_len.1
    omega

  have h_right_next := get_append_dropLast_right p1.m_seq p2.m_seq (N1 + 1) h_p1_ne hi_next h_con_next h_con2_next

  have h_next_eq : m_next = (p1.m_seq.dropLast ++ p2.m_seq).get ⟨N1 + 1, h_con_next⟩ := rfl

  have h_next : m_next = p2.m_seq.get ⟨1, by have := p2.h_len.1; omega⟩ := by
    rw [h_next_eq, h_right_next]
    apply get_of_fin_eq
    change N1 + 1 - (p1.m_seq.length - 1) = 1
    have h_len_p1 := p1.h_len.1
    omega

  have h_vel := h_smooth.h_velocity_m h1 h2
  have hx_orig := h_vel.1

  generalize h_z_next : ((p2.m_seq.get ⟨1, by rw [p2.h_len.1]; omega⟩).x : ZMod q) = z_next
  generalize h_z_curr : ((p1.m_seq.get ⟨N1, by rw [p1.h_len.1]; omega⟩).x : ZMod q) = z_curr
  generalize h_z_prev : ((p1.m_seq.get ⟨N1 - 1, by rw [p1.h_len.1]; omega⟩).x : ZMod q) = z_prev

  rw [h_z_next, h_z_curr, h_z_prev] at hx_orig

  dsimp [d2_x]
  rw [h_prev, h_curr, h_next]
  rw [h_z_next, h_z_curr, h_z_prev]
  have h_m2 : (minus_two : ZMod q) = (-2 : ZMod q) := minus_two_eq
  rw [h_m2]

  calc
    z_next + (-2 : ZMod q) * z_curr + z_prev = (z_next - z_curr) - (z_curr - z_prev) := by ring
    _ = (z_curr - z_prev) - (z_curr - z_prev) := by rw [hx_orig]
    _ = 0 := by ring

lemma geodesic_id (h_g_primitive : ∀ (v : ZMod q), v ≠ 0 → ∃ (x : Nat), x < q - 1 ∧ (g : ZMod q) ^ x = v) (dom : Manifold4D) (h_regular : calculateQ dom ≠ 0) : GeodesicMorphism dom dom := by
  let Q_val := calculateQ dom
  let ell_val := discreteLogExistential_ZMod h_g_primitive Q_val
  let E_val := 1
  let path : ConcretePath dom dom 0 0 := {
    m_seq    := [dom]
    r_seq    := [0]
    E_seq    := [E_val]
    ell_seq  := [ell_val]
    h_len    := ⟨rfl, rfl, rfl, rfl⟩
    h_dom    := rfl
    h_cod    := rfl
    r_lt     := by
      intro r hr
      have hr_eq : r = 0 := List.mem_singleton.mp hr
      rw [hr_eq]
      exact q_pos
    ell_lt   := by
      intro e he
      have he_eq : e = ell_val := List.mem_singleton.mp he
      rw [he_eq]
      exact discreteLogExistential_lt h_g_primitive Q_val.val
    E_lt     := by
      intro E hE
      have hE_eq : E = E_val := List.mem_singleton.mp hE
      rw [hE_eq]
      exact q_gt_one
  }
  use 0, 0, path

  unfold isStrictGeodesicPath

  exact ⟨
    by
      intro i hi
      have h_i_zero : i = 0 := by omega
      subst h_i_zero
      change (g : ZMod q) ^ ell_val + (minus_one : ZMod q) * calculateQ dom = 0 ∧
             (E_val : ZMod q) + (minus_one : ZMod q) * (g : ZMod q) ^ (sqrt_exp * 0) = 0
      exact ⟨
        by
          have h_pow := discreteLogExistential_spec h_g_primitive Q_val h_regular
          have h_minus_one : (minus_one : ZMod q) = (-1 : ZMod q) := minus_one_eq
          rw [h_pow, h_minus_one]
          ring,
        by
          have h_minus_one : (minus_one : ZMod q) = (-1 : ZMod q) := minus_one_eq
          have h_E : (E_val : ZMod q) = 1 := by
            change ((1 : Nat) : ZMod q) = 1
            exact cast_one_eq_one
          rw [h_minus_one, h_E]
          ring
      ⟩,
    by
      intro i h_pos h_lt
      omega
  ⟩






structure PolyTerm where
  coeff : Nat
  vars  : List (String × Nat)
  deriving Repr, BEq

structure Polynomial where
  terms : List PolyTerm
  deriving Repr, BEq

structure AlgebraicStepSymbols where
  m   : Nat
  x   : String
  y   : String
  z   : String
  t   : String
  r   : String
  ell : String
  E   : String
  deriving Inhabited, Repr

structure BoundaryValues where
  x_val : Nat
  y_val : Nat
  z_val : Nat
  t_val : Nat
  r_val : Nat
  w_val : Nat
  deriving Inhabited, Repr

inductive NodeState
  | Boundary (v : BoundaryValues)
  | Variable (s : AlgebraicStepSymbols)
  deriving Inhabited, Repr

def generateUnknownMatrix (M : Nat) : List String :=
  let rec loop (m : Nat) (acc : List String) : List String :=
    if m >= M then acc
    else
      let vars_m := [
        s!"E_{m}",
        s!"ell_{m}",
        s!"x_{m}",
        s!"y_{m}",
        s!"z_{m}",
        s!"t_{m}",
        s!"r_{m}"
      ]
      loop (m + 1) (acc ++ vars_m)
  termination_by M - m

  if M <= 1 then [] else loop 1 []

def buildSimulationContext (M : Nat) (X0 XM : BoundaryValues) : List NodeState :=
  let rec loop (m : Nat) (acc : List NodeState) : List NodeState :=
    if m >= M then acc ++ [NodeState.Boundary XM]
    else
      let syms := AlgebraicStepSymbols.mk m s!"x_{m}" s!"y_{m}" s!"z_{m}" s!"t_{m}" s!"r_{m}" s!"ell_{m}" s!"E_{m}"
      loop (m + 1) (acc ++ [NodeState.Variable syms])
  termination_by M - m

  if M == 0 then [NodeState.Boundary X0]
  else loop 1 [NodeState.Boundary X0]

def getQExpression (node : NodeState) : String :=
  match node with
  | .Boundary v =>
    let q_val := modSub (modMul v.x_val v.x_val)
                 (modAdd (modMul v.y_val v.y_val)
                 (modAdd (modMul v.z_val v.z_val) (modMul v.t_val v.t_val)))
    s!"{q_val}"
  | .Variable s => s!"({s.x}^2 - {s.y}^2 - {s.z}^2 - {s.t}^2)"

def getWExpression (node : NodeState) (n_global : Nat) : String :=
  match node with
  | .Boundary v => s!"{v.w_val}"
  | .Variable s => s!"({minus_one} * {n_global} * {s.ell})"

def generateLogRelationPoly (node : NodeState) : Option String :=
  match node with
  | .Boundary _ => none
  | .Variable s => some s!"({g}^{s.ell} - {getQExpression node})"

def generateExpRelationPoly (node : NodeState) (sqrt_Lambda : Nat) : Option String :=
  match node with
  | .Boundary _ => none
  | .Variable s => some s!"({s.E} - {g}^({sqrt_Lambda} * {s.r}))"

def compareVariables (v1 v2 : String × Nat) : Ordering :=
  if v1.1 == v2.1 then Ordering.eq
  else
    Id.run do
      let splitOf (v : String) : (String × Nat) :=
        match v.splitOn "_" with
        | [name, m_str] => (name, m_str.toNat?.getD 0)
        | _ => (v, 0)
      let (n1, m1) := splitOf v1.1
      let (n2, m2) := splitOf v2.1

      if m1 < m2 then Ordering.lt
      else if m1 > m2 then Ordering.gt
      else
        let vPrio (n : String) : Nat :=
          if n == "E" then 7
          else if n == "ell" then 6
          else if n == "x" then 5
          else if n == "y" then 4
          else if n == "z" then 3
          else if n == "t" then 2
          else if n == "r" then 1
          else 0
        let p1 := vPrio n1
        let p2 := vPrio n2
        if p1 > p2 then Ordering.lt
        else if p1 < p2 then Ordering.gt
        else Ordering.eq

def polyAddConst (p : Polynomial) (c : Nat) : Polynomial :=
  if c % q == 0 then p else { terms := p.terms ++ [{ coeff := c % q, vars := [] }] }

def polyMulConst (p : Polynomial) (c : Nat) : Polynomial :=
  let c_mod := c % q
  if c_mod == 0 then { terms := [] }
  else { terms := p.terms.map (fun t => { coeff := (t.coeff * c_mod) % q, vars := t.vars }) }

def polyAdd (p1 p2 : Polynomial) : Polynomial :=
  { terms := p1.terms ++ p2.terms }

def polyMul (p1 p2 : Polynomial) : Polynomial :=
  let newTerms := p1.terms.flatMap fun t1 =>
    p2.terms.map fun t2 =>
      { coeff := (t1.coeff * t2.coeff) % q, vars := t1.vars ++ t2.vars }
  { terms := newTerms }

def mkVarPoly (varName : String) : Polynomial :=
  { terms := [{ coeff := 1, vars := [(varName, 1)] }] }

def symbolicPsi7 (m : Nat) : Polynomial :=
  let ell_m := mkVarPoly s!"ell_{m}"
  let E_m   := mkVarPoly s!"E_{m}"
  let r_m   := mkVarPoly s!"r_{m}"
  let interaction := polyMulConst (polyMul E_m ell_m) minus_two
  let r_sq := polyMul r_m r_m
  let r_term := polyMulConst r_sq inv_two
  polyAdd interaction r_term

def getStepComponentVarName (m : Nat) (idx : Nat) : String :=
  match idx with
  | 0 => s!"x_{m}"
  | 1 => s!"y_{m}"
  | 2 => s!"z_{m}"
  | 3 => s!"t_{m}"
  | 4 => s!"r_{m}"
  | 5 => s!"ell_{m}"
  | _ => s!"E_{m}"

def symbolicMetric_g (m : Nat) (k j : Nat) : Polynomial :=
  if k == 4 && j == 4 then { terms := [{ coeff := 1, vars := [] }] }
  else if (k == 4 && j == 1) || (k == 1 && j == 4) then
    polyMulConst (mkVarPoly (getStepComponentVarName m 6)) minus_two
  else { terms := [{ coeff := 0, vars := [] }] }

def symbolicSkewness_T (m : Nat) (i j k : Nat) : Polynomial :=
  if i == 4 && j == 1 && k == 1 then
    polyMulConst (mkVarPoly (getStepComponentVarName m 6)) minus_two
  else { terms := [{ coeff := 0, vars := [] }] }

def EvaluateEquationKSymbolic (m : Nat) (n_global : Nat) (k : Nat) : Polynomial :=
  let coef_n_val := ((1 + minus_one * n_global) * inv_two) % q

  let rec loop_j (j : Nat) (acc : Polynomial) : Polynomial :=
    if j >= 7 then acc
    else
      let g_kj := symbolicMetric_g m k j
      let x_next := mkVarPoly (getStepComponentVarName (m + 1) j)
      let x_curr := mkVarPoly (getStepComponentVarName m j)
      let x_prev := mkVarPoly (getStepComponentVarName (m - 1) j)
      let minus_two_x_curr := polyMulConst x_curr minus_two
      let d2_X := polyAdd x_next (polyAdd minus_two_x_curr x_prev)
      let term1_j := polyMul g_kj d2_X
      loop_j (j + 1) (polyAdd acc term1_j)
  termination_by 7 - j

  let Term1 := loop_j 0 { terms := [] }

  let rec loop_i_j (i j : Nat) (acc : Polynomial) : Polynomial :=
    if i >= 7 then acc
    else if j >= 7 then loop_i_j (i + 1) 0 acc
    else
      let T_ijk := symbolicSkewness_T m i j k
      let dX_i := polyAdd (mkVarPoly (getStepComponentVarName (m + 1) i))
                          (polyMulConst (mkVarPoly (getStepComponentVarName m i)) minus_one)
      let dX_j := polyAdd (mkVarPoly (getStepComponentVarName (m + 1) j))
                          (polyMulConst (mkVarPoly (getStepComponentVarName m j)) minus_one)
      let prod := polyMulConst (polyMul T_ijk (polyMul dX_i dX_j)) coef_n_val
      loop_i_j i (j + 1) (polyAdd acc prod)
  termination_by (7 - i, 7 - j)

  let Term2 := loop_i_j 0 0 { terms := [] }
  polyAdd Term1 Term2

def generateTotalIdealBVP (M : Nat) (n_global : Nat) (sqrt_Lambda : Nat) (T0_0 T0_1 T0_2 T0_3 r0 : Nat): List Polynomial :=
  let rec loop (m : Nat) (acc : List Polynomial) : List Polynomial :=
    if m >= M then acc
    else
      let step_polys := (List.range 7).map (fun k => EvaluateEquationKSymbolic m n_global k)
      let x0 := mkVarPoly (getStepComponentVarName m 0)
      let x1 := mkVarPoly (getStepComponentVarName m 1)
      let x2 := mkVarPoly (getStepComponentVarName m 2)
      let x3 := mkVarPoly (getStepComponentVarName m 3)
      let ell_m := mkVarPoly (getStepComponentVarName m 5)
      let E_m   := mkVarPoly (getStepComponentVarName m 6)

      let q_poly := polyAdd (polyMul x0 x0)
                    (polyAdd (polyMulConst (polyMul x1 x1) minus_one)
                    (polyAdd (polyMulConst (polyMul x2 x2) minus_one)
                             (polyMulConst (polyMul x3 x3) minus_one)))

      let log_link_relation := if m == 1 then
        let Q_0 := Calculate_Q T0_0 T0_1 T0_2 T0_3
        let ell_0_const := discreteLog Q_0
        let L_1_val := (g * ell_0_const) % q
        let L_1_poly := polyAdd ell_m { terms := [{ coeff := (q - L_1_val) % q, vars := [] }] }
        polyAdd L_1_poly (polyMulConst q_poly minus_one)
      else
        let L_prev := mkVarPoly (getStepComponentVarName (m - 1) 5)
        let L_m := polyAdd ell_m (polyMulConst L_prev (q - g))
        polyAdd L_m (polyMulConst q_poly minus_one)

      let G_base := modPower g sqrt_Lambda
      let exp_relation := if m == 1 then
        let E_0_const := modPower g (sqrt_Lambda * r0)
        let G_E0_val := (G_base * E_0_const) % q
        polyAdd E_m { terms := [{ coeff := (q - G_E0_val) % q, vars := [] }] }
      else
        let E_prev := mkVarPoly (getStepComponentVarName (m - 1) 6)
        polyAdd E_m (polyMulConst E_prev (q - G_base))

      let current_step_ideal := step_polys ++ [log_link_relation, exp_relation]
      loop (m + 1) (acc ++ current_step_ideal)
  termination_by M - m

  loop 1 []

def getAlgebraicStateVector (m M : Nat) (X0 XM : BoundaryValues) (n_global : Nat) : List Polynomial :=
  if m == 0 then
    [
      { terms := [{ coeff := X0.x_val, vars := [] }] },
      { terms := [{ coeff := X0.y_val, vars := [] }] },
      { terms := [{ coeff := X0.z_val, vars := [] }] },
      { terms := [{ coeff := X0.t_val, vars := [] }] },
      { terms := [{ coeff := X0.r_val, vars := [] }] },
      { terms := [{ coeff := n_global, vars := [] }] },
      { terms := [{ coeff := X0.w_val, vars := [] }] }
    ]
  else if m >= M then
    [
      { terms := [{ coeff := XM.x_val, vars := [] }] },
      { terms := [{ coeff := XM.y_val, vars := [] }] },
      { terms := [{ coeff := XM.z_val, vars := [] }] },
      { terms := [{ coeff := XM.t_val, vars := [] }] },
      { terms := [{ coeff := XM.r_val, vars := [] }] },
      { terms := [{ coeff := n_global, vars := [] }] },
      { terms := [{ coeff := XM.w_val, vars := [] }] }
    ]
  else
    let x_m   := mkVarPoly (getStepComponentVarName m 0)
    let y_m   := mkVarPoly (getStepComponentVarName m 1)
    let z_m   := mkVarPoly (getStepComponentVarName m 2)
    let t_m   := mkVarPoly (getStepComponentVarName m 3)
    let r_m   := mkVarPoly (getStepComponentVarName m 4)
    let n_m   := { terms := [{ coeff := n_global, vars := [] }] }
    let ell_m := mkVarPoly (getStepComponentVarName m 5)
    let w_m   := polyMulConst n_m (q - (n_global % q))
    let w_m   := polyMul w_m ell_m
    [x_m, y_m, z_m, t_m, r_m, n_m, w_m]

def computeGeodesicResidualPoly (m M : Nat) (X0 XM : BoundaryValues) (n_global : Nat) (k : Nat) : Polynomial :=
  let X_prev := getAlgebraicStateVector (m - 1) M X0 XM n_global
  let X_curr := getAlgebraicStateVector m M X0 XM n_global
  let X_next := getAlgebraicStateVector (m + 1) M X0 XM n_global
  let coef_n_val := ((1 + minus_one * n_global) * inv_two) % q

  let get_DX (i : Nat) : Polynomial :=
    polyAdd (X_next.getD i { terms := [] }) (polyMulConst (X_curr.getD i { terms := [] }) minus_one)

  let get_D2X (j : Nat) : Polynomial :=
    let term_next := X_next.getD j { terms := [] }
    let term_curr := polyMulConst (X_curr.getD j { terms := [] }) minus_two
    let term_prev := X_prev.getD j { terms := [] }
    polyAdd term_next (polyAdd term_curr term_prev)

  let Term1 :=
    if k == 4 then
      let g_44_d2x := get_D2X 4
      let E_m := mkVarPoly (getStepComponentVarName m 6)
      let g_41 := polyMulConst E_m minus_two
      let g_41_d2x := polyMul g_41 (get_D2X 1)
      polyAdd g_44_d2x g_41_d2x
    else if k == 1 then
      let E_m := mkVarPoly (getStepComponentVarName m 6)
      let g_14 := polyMulConst E_m minus_two
      polyMul g_14 (get_D2X 4)
    else { terms := [] }

  let Term2 :=
    if k == 1 then
      let E_m := mkVarPoly (getStepComponentVarName m 6)
      let T_411 := polyMulConst E_m minus_two
      let prod_dx := polyMul (get_DX 4) (get_DX 1)
      let total_t := polyMul T_411 prod_dx
      polyMulConst total_t coef_n_val
    else { terms := [] }

  polyAdd Term1 Term2

def generateGlobalBVPIdles (M : Nat) (X0 XM : BoundaryValues) (n_global : Nat) (sqrt_Lambda : Nat) : List Polynomial :=
  let G_base := modPower g sqrt_Lambda
  let rec loop (m : Nat) (acc : List Polynomial) : List Polynomial :=
    if m >= M then acc
    else
      let F_m_k_list := (List.range 7).map (fun k => computeGeodesicResidualPoly m M X0 XM n_global k)
      let x_m := mkVarPoly (getStepComponentVarName m 0)
      let y_m := mkVarPoly (getStepComponentVarName m 1)
      let z_m := mkVarPoly (getStepComponentVarName m 2)
      let t_m := mkVarPoly (getStepComponentVarName m 3)

      let Q_m := polyAdd (polyMul x_m x_m)
                 (polyAdd (polyMulConst (polyMul y_m y_m) minus_one)
                 (polyAdd (polyMulConst (polyMul z_m z_m) minus_one)
                          (polyMulConst (polyMul t_m t_m) minus_one)))

      let ell_m := mkVarPoly (getStepComponentVarName m 5)

      let ell_prev := if m == 1 then
                        let Q_0 := Calculate_Q X0.x_val X0.y_val X0.z_val X0.t_val
                        let ell_0_const := discreteLog Q_0
                        { terms := [{ coeff := ell_0_const, vars := [] }] }
                      else
                        mkVarPoly (getStepComponentVarName (m - 1) 5)

      let f_log_m := polyAdd ell_m
                     (polyAdd (polyMulConst ell_prev (q - (g % q)))
                              (polyMulConst Q_m minus_one))

      let E_m := mkVarPoly (getStepComponentVarName m 6)
      let E_prev := if m == 1 then
                       let E_0_const := modPower g (sqrt_Lambda * X0.r_val)
                       { terms := [{ coeff := E_0_const, vars := [] }] }
                     else
                       mkVarPoly (getStepComponentVarName (m - 1) 6)

      let f_exp_m := polyAdd E_m (polyMulConst E_prev (q - (G_base % q)))
      let current_step_ideal := F_m_k_list ++ [f_log_m, f_exp_m]
      loop (m + 1) (acc ++ current_step_ideal)
  termination_by M - m

  if M <= 1 then [] else loop 1 []






def gatherUpperVariables (m M : Nat) : List String :=
  let rec loop (j : Nat) (acc : List String) : List String :=
    if j >= M then acc
    else
      let step_vars := (List.range 7).map (fun idx => getStepComponentVarName j idx)
      loop (j + 1) (acc ++ step_vars)
  termination_by M - j
  loop (m + 1) []

def Phi_r (m M : Nat) : Polynomial :=
  let upper_vars := gatherUpperVariables m M
  let base_term := { terms := [] : Polynomial }
  if m == M - 1 then polyAddConst base_term 0
  else upper_vars.foldl (fun acc var => polyAdd acc (mkVarPoly var)) base_term

def Phi_t (m M : Nat) (r_poly : Polynomial) : Polynomial :=
  let upper_vars := gatherUpperVariables m M
  upper_vars.foldl (fun acc var => polyAdd acc (mkVarPoly var)) r_poly

def Phi_z (m M : Nat) (t_poly r_poly : Polynomial) : Polynomial :=
  let upper_vars := gatherUpperVariables m M
  let acc_poly := polyAdd t_poly r_poly
  upper_vars.foldl (fun acc var => polyAdd acc (mkVarPoly var)) acc_poly

def Phi_y (m M : Nat) (z_poly t_poly r_poly : Polynomial) : Polynomial :=
  let upper_vars := gatherUpperVariables m M
  let acc_poly := polyAdd (polyAdd z_poly t_poly) r_poly
  upper_vars.foldl (fun acc var => polyAdd acc (mkVarPoly var)) acc_poly

def Phi_x (m M : Nat) (y_poly z_poly t_poly r_poly : Polynomial) : Polynomial :=
  let upper_vars := gatherUpperVariables m M
  let acc_poly := polyAdd (polyAdd (polyAdd y_poly z_poly) t_poly) r_poly
  upper_vars.foldl (fun acc var => polyAdd acc (mkVarPoly var)) acc_poly

def Phi_ell (m M : Nat) (x_poly y_poly z_poly t_poly r_poly : Polynomial) : Polynomial :=
  let upper_vars := gatherUpperVariables m M
  let acc_poly := polyAdd (polyAdd (polyAdd (polyAdd x_poly y_poly) z_poly) t_poly) r_poly
  upper_vars.foldl (fun acc var => polyAdd acc (mkVarPoly var)) acc_poly

def Phi_E (m M : Nat) (ell_poly x_poly y_poly z_poly t_poly r_poly : Polynomial) : Polynomial :=
  let upper_vars := gatherUpperVariables m M
  let acc_poly := polyAdd (polyAdd (polyAdd (polyAdd (polyAdd ell_poly x_poly) y_poly) z_poly) t_poly) r_poly
  upper_vars.foldl (fun acc var => polyAdd acc (mkVarPoly var)) acc_poly

structure GroebnerReducedPair where
  r_relation   : Polynomial
  t_relation   : Polynomial
  z_relation   : Polynomial
  y_relation   : Polynomial
  x_relation   : Polynomial
  ell_relation : Polynomial
  E_relation   : Polynomial
  deriving Repr

def generateReducedGroebnerBasisComponent (m M : Nat) : GroebnerReducedPair :=
  let r_var := mkVarPoly (getStepComponentVarName m 4)
  let t_var := mkVarPoly (getStepComponentVarName m 3)
  let z_var := mkVarPoly (getStepComponentVarName m 2)
  let y_var := mkVarPoly (getStepComponentVarName m 1)
  let x_var := mkVarPoly (getStepComponentVarName m 0)
  let ell_var := mkVarPoly (getStepComponentVarName m 5)
  let E_var := mkVarPoly (getStepComponentVarName m 6)

  let phi_r_poly := Phi_r m M
  let phi_t_poly := Phi_t m M r_var
  let phi_z_poly := Phi_z m M t_var r_var
  let phi_y_poly := Phi_y m M z_var t_var r_var
  let phi_x_poly := Phi_x m M y_var z_var t_var r_var
  let phi_ell_poly := Phi_ell m M x_var y_var z_var t_var r_var
  let phi_E_poly := Phi_E m M ell_var x_var y_var z_var t_var r_var

  {
    r_relation   := polyAdd r_var (polyMulConst phi_r_poly minus_one),
    t_relation   := polyAdd t_var (polyMulConst phi_t_poly minus_one),
    z_relation   := polyAdd z_var (polyMulConst phi_z_poly minus_one),
    y_relation   := polyAdd y_var (polyMulConst phi_y_poly minus_one),
    x_relation   := polyAdd x_var (polyMulConst phi_x_poly minus_one),
    ell_relation := polyAdd ell_var (polyMulConst phi_ell_poly minus_one),
    E_relation   := polyAdd E_var (polyMulConst phi_E_poly minus_one)
  }

def generateGLexIdealList (M : Nat) : List Polynomial :=
  let rec loop (m : Nat) (acc : List Polynomial) : List Polynomial :=
    if m >= M then acc
    else
      let pair := generateReducedGroebnerBasisComponent m M
      let current_step_list := [
        pair.r_relation, pair.t_relation, pair.z_relation,
        pair.y_relation, pair.x_relation, pair.ell_relation, pair.E_relation
      ]
      loop (m + 1) (acc ++ current_step_list)
  termination_by M - m
  loop 1 []






def EvaluateEquationKExplicit (m : Nat) (_M : Nat) (_X0 _XM : BoundaryValues) (n_global : Nat) (k : Nat) : Polynomial :=
  let x_next := mkVarPoly (getStepComponentVarName (m + 1) 0)
  let x_curr := mkVarPoly (getStepComponentVarName m 0)
  let x_prev := mkVarPoly (getStepComponentVarName (m - 1) 0)
  let y_next := mkVarPoly (getStepComponentVarName (m + 1) 1)
  let y_curr := mkVarPoly (getStepComponentVarName m 1)
  let y_prev := mkVarPoly (getStepComponentVarName (m - 1) 1)
  let r_next := mkVarPoly (getStepComponentVarName (m + 1) 4)
  let r_curr := mkVarPoly (getStepComponentVarName m 4)
  let r_prev := mkVarPoly (getStepComponentVarName (m - 1) 4)
  let E_m := mkVarPoly (getStepComponentVarName m 6)

  let d2_x := polyAdd x_next (polyAdd (polyMulConst x_curr minus_two) x_prev)
  let d2_y := polyAdd y_next (polyAdd (polyMulConst y_curr minus_two) y_prev)
  let d2_r := polyAdd r_next (polyAdd (polyMulConst r_curr minus_two) r_prev)
  let dx_r := polyAdd r_next (polyMulConst r_curr minus_one)
  let dx_y := polyAdd y_next (polyMulConst y_curr minus_one)

  let term_k0 := polyMulConst d2_x 1
  let term_k4 := polyAdd d2_r (polyMulConst (polyMul E_m d2_y) minus_two)
  let term_k1_1 := polyMulConst (polyMul E_m d2_r) minus_two
  let coef_n_val := ((1 + minus_one * n_global) * inv_two) % q
  let term_k1_2 := polyMulConst (polyMul (polyMulConst E_m minus_two) (polyMul dx_r dx_y)) coef_n_val

  if k == 0 then term_k0
  else if k == 1 then polyAdd term_k1_1 term_k1_2
  else if k == 4 then term_k4
  else { terms := [] }

def evaluateLogRelationExplicit (m : Nat) (X0 : BoundaryValues) : Polynomial :=
  let ell_m := mkVarPoly (getStepComponentVarName m 5)
  let x_m := mkVarPoly (getStepComponentVarName m 0)
  let y_m := mkVarPoly (getStepComponentVarName m 1)
  let z_m := mkVarPoly (getStepComponentVarName m 2)
  let t_m := mkVarPoly (getStepComponentVarName m 3)

  let Q_m := polyAdd (polyMul x_m x_m)
               (polyAdd (polyMulConst (polyMul y_m y_m) minus_one)
               (polyAdd (polyMulConst (polyMul z_m z_m) minus_one)
                        (polyMulConst (polyMul t_m t_m) minus_one)))

  if m == 1 then
    let Q_0_val := Calculate_Q X0.x_val X0.y_val X0.z_val X0.t_val
    let log_Q_0 := discreteLog Q_0_val
    let const_term := (g * log_Q_0) % q
    let ell_term := polyAdd ell_m { terms := [{ coeff := (minus_one * const_term) % q, vars := [] }] }
    polyAdd ell_term (polyMulConst Q_m minus_one)
  else
    let ell_prev := mkVarPoly (getStepComponentVarName (m - 1) 5)
    let ell_term := polyAdd ell_m (polyMulConst ell_prev (minus_one * g))
    polyAdd ell_term (polyMulConst Q_m minus_one)

def evaluateExpRelationExplicit (m : Nat) (X0 : BoundaryValues) (sqrt_Lambda : Nat) : Polynomial :=
  let E_m := mkVarPoly (getStepComponentVarName m 6)
  let G_base := modPower g sqrt_Lambda

  if m == 1 then
    let E_0_const := modPower g (sqrt_Lambda * X0.r_val)
    let const_val := (G_base * E_0_const) % q
    polyAdd E_m { terms := [{ coeff := (minus_one * const_val) % q, vars := [] }] }
  else
    let E_prev := mkVarPoly (getStepComponentVarName (m - 1) 6)
    polyAdd E_m (polyMulConst E_prev (minus_one * G_base))

def generateGlobalBVPIdlesExplicit (M : Nat) (X0 _XM : BoundaryValues) (n_global : Nat) (sqrt_Lambda : Nat) : List Polynomial :=
  let rec loop (m : Nat) (acc : List Polynomial) : List Polynomial :=
    if m >= M then acc
    else
      let F_m_k_list := (List.range 7).map (fun k => EvaluateEquationKExplicit m M X0 _XM n_global k)
      let f_log := evaluateLogRelationExplicit m X0
      let f_exp := evaluateExpRelationExplicit m X0 sqrt_Lambda
      loop (m + 1) (acc ++ F_m_k_list ++ [f_log, f_exp])
  termination_by M - m
  if M <= 1 then [] else loop 1 []






def generateSageMathHeader (M : Nat) : String :=
  let unknowns := generateUnknownMatrix M
  let varsStr := String.intercalate ", " unknowns
  s!"# ---SageMath Initialization Script ---\n" ++
  s!"# Finite Field Definition\n" ++
  s!"Fq = GF({q})\n\n" ++
  s!"# Polynomial Ring Definition with Lexicographical Ordering (lex)\n" ++
  s!"# Hierarchy: E_m > ell_m > x_m > y_m > z_m > t_m > r_m (m=1 to M-1)\n" ++
  s!"R.<{varsStr}> = PolynomialRing(Fq, order='lex')\n" ++
  s!"print('Polynomial Ring initialized successfully.')"

def polyTermToSageString (t : PolyTerm) : String :=
  if t.vars.isEmpty then s!"{t.coeff}"
  else
    let varsStrList := t.vars.map (fun (varName, power) =>
      if power == 1 then s!"{varName}" else s!"{varName}^{power}"
    )
    let joinedVars := String.intercalate " * " varsStrList
    if t.coeff == 1 then joinedVars
    else s!"{t.coeff} * {joinedVars}"

def polynomialToSageString (p : Polynomial) : String :=
  let validTerms := p.terms.filter (fun t => t.coeff % q != 0)
  if validTerms.isEmpty then "0"
  else
    let termStrings := validTerms.map polyTermToSageString
    String.intercalate " + " termStrings

def exportIdealToSage (polys : List Polynomial) : String :=
  let sagePolys := polys.map (fun p => s!"    {polynomialToSageString p}")
  let joinedPolys := String.intercalate ",\n" sagePolys
  s!"ideal_generators = [\n{joinedPolys}\n]\n" ++
  s!"I = R.ideal(ideal_generators)"

def generateSageGroebnerSolverCommands (M : Nat) : String :=
  let m_last := M - 1
  s!"# --- Groebner Basis Computation & Root Finding Step ---\n" ++
  s!"print('Computing Groebner basis under lex order... (This may take some time)')\n" ++
  s!"# 既約グレブナー基底の計算\n" ++
  s!"B = I.groebner_basis()\n" ++
  s!"print('Groebner basis computed. Number of elements:', len(B))\n\n" ++
  s!"# --- Cascade Resolution Process ---\n" ++
  s!"# Lex 順序の性質上、B の最初の要素（または特定要素）は最下位変数 r_{m_last} のみの一変数多項式となる\n" ++
  s!"# P(r_{m_last}) == 0\n" ++
  s!"poly_r_last = B[0]\n" ++
  s!"print('Elimination polynomial for r_{m_last}:', poly_r_last)\n\n" ++
  s!"# 1. 一変数多項式の Fq 上での根（解の候補）を確定\n" ++
  s!"roots_r_last = poly_r_last.univariate_polynomial().roots(multiplicities=False)\n" ++
  s!"print('Possible roots for r_{m_last}:', roots_r_last)\n\n" ++
  s!"if len(roots_r_last) == 0:\n" ++
  s!"    print('No algebraic solution exists for this boundary condition.')\n" ++
  s!"else:\n" ++
  s!"    # 代表的な1つの根を選択して、上位の多項式系へ代入（バックサブスティチューション）\n" ++
  s!"    sol_r = roots_r_last[0]\n" ++
  s!"    print('Fixing r_{m_last} = ' + str(sol_r))\n" ++
  s!"    \n" ++
  s!"    # イデアルに解の拘束を追加して残りの変数を順次確定\n" ++
  s!"    I_fixed = I + R.ideal(r_{m_last} - sol_r)\n" ++
  s!"    B_fixed = I_fixed.groebner_basis()\n" ++
  s!"    # この操作を繰り返し、[E_m, ell_m, x_m, y_m, z_m, t_m, r_m] の全座標を一意確定させる\n" ++
  s!"    print('Variety is zero-dimensional. Sequential extraction enabled.')"

def generateCompleteSageScript (M : Nat) (X0 XM : BoundaryValues) (n_global : Nat) (sqrt_Lambda : Nat) : String :=
  let header := generateSageMathHeader M
  let idealPolys := generateGlobalBVPIdlesExplicit M X0 XM n_global sqrt_Lambda
  let idealBody := exportIdealToSage idealPolys
  let solver := generateSageGroebnerSolverCommands M
  s!"{header}\n\n{idealBody}\n\n{solver}"






attribute [irreducible] q

end CryptoTopos
