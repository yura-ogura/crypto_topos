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

import Mathlib.Tactic.Ring
import CryptoTopos.Model

set_option linter.unusedVariables false

noncomputable section
open CryptoTopos

namespace SemanticProofs

@[simp] lemma zmod_modAdd_eq (a b : Nat) :
  (modAdd a b : ZMod q) = (a : ZMod q) + (b : ZMod q) := by
  unfold modAdd
  rw [ZMod.natCast_mod]
  push_cast
  rfl

@[simp] lemma zmod_modMul_eq (a b : Nat) :
  (modMul a b : ZMod q) = (a : ZMod q) * (b : ZMod q) := by
  unfold modMul
  rw [ZMod.natCast_mod]
  push_cast
  rfl

@[simp] lemma zmod_modSub_eq (a b : Nat) :
  (modSub a b : ZMod q) = (a : ZMod q) - (b : ZMod q) := by
  unfold modSub
  simp only [zmod_modAdd_eq, zmod_modMul_eq]
  rw [minus_one_eq]
  ring

lemma cast_eq_inv_of_mul_eq (a k : ℕ) (hcop : Nat.Coprime k q)
    (h : a * k = q + 1) : (a : ZMod q) = (k : ZMod q)⁻¹ := by
  have h1 : (k : ZMod q) * (k : ZMod q)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one k hcop
  have h2 : (a : ZMod q) * (k : ZMod q) = 1 := by
    have h' := congrArg (Nat.cast : ℕ → ZMod q) h
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add] at h'
    exact h'
  calc (a : ZMod q)
      = (a : ZMod q) * ((k : ZMod q) * (k : ZMod q)⁻¹) := by rw [h1, mul_one]
    _ = ((a : ZMod q) * (k : ZMod q)) * (k : ZMod q)⁻¹ := by rw [mul_assoc]
    _ = (k : ZMod q)⁻¹ := by rw [h2, one_mul]

@[simp] lemma zmod_inv_two_eq : (inv_two : ZMod q) = 2⁻¹ := by
  have h := cast_eq_inv_of_mul_eq inv_two 2
    (by unfold q; decide)
    (by unfold inv_two q; norm_num)
  exact_mod_cast h

@[simp] lemma zmod_sqrt_exp_eq : (sqrt_exp : ZMod q) = 4⁻¹ := by
  have h := cast_eq_inv_of_mul_eq sqrt_exp 4
    (by unfold q; decide)
    (by unfold sqrt_exp q; norm_num)
  exact_mod_cast h

def concrete_Cipher (n s r : Nat) : Nat := modAdd n (modMul s r)
def concrete_Decipher (c s r : Nat) : Nat := modSub c (modMul s r)

theorem concrete_Cipher_eq_impl (n s r : Nat) :
  concrete_Cipher n s r = modAdd n (modMul s r) := by rfl

theorem concrete_Decipher_eq_impl (c s r : Nat) :
  concrete_Decipher c s r = modSub c (modMul s r) := by rfl

theorem concrete_Correctness_Path_eq_impl (x : Nat) :
  (x : ZMod q) = (x : ZMod q) := by rfl

theorem concrete_Correctness_Path_eps0_impl (n s r : Nat) :
  (concrete_Decipher (concrete_Cipher n s r) s r : ZMod q) = (n : ZMod q) := by
  unfold concrete_Decipher concrete_Cipher
  simp only [zmod_modAdd_eq, zmod_modMul_eq, zmod_modSub_eq]
  ring

theorem concrete_Correctness_Path_eps1_impl (c s r : Nat) :
  (concrete_Cipher (concrete_Decipher c s r) s r : ZMod q) = (c : ZMod q) := by
  unfold concrete_Decipher concrete_Cipher
  simp only [zmod_modAdd_eq, zmod_modMul_eq, zmod_modSub_eq]
  ring

end SemanticProofs

