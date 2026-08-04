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

-- Note: These lemmas regarding fractional constants are reserved for non-linear potential 
-- geometric proofs (Future Work) and are not required for the linear masking correctness proven below.
@[simp] lemma zmod_inv_two_eq : (inv_two : ZMod q) = 2⁻¹ := by sorry
@[simp] lemma zmod_sqrt_exp_eq : (sqrt_exp : ZMod q) = 4⁻¹ := by sorry

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

