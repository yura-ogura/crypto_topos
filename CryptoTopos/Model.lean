/-
Copyright (c) 2026 yura-ogura. All rights reserved.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

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
  let m_con    := p1.m_seq.dropLast ++ p2.m_seq
  let r_con    := p1.r_seq.dropLast ++ p2.r_seq
  let E_con    := p1.E_seq.dropLast ++ p2.E_seq
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

end CryptoTopos

