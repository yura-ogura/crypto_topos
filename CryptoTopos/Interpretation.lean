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

import HoTTLean.Model.Natural.Interpretation
import Lean
import CryptoTopos.SemanticProofs

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

noncomputable section

open CategoryTheory
open SynthLean
open NaturalModel.Universe
open SemanticProofs

universe u v

variable {P_cat : Type u} [Category.{v, u} P_cat] [SmallCategory P_cat] [ChosenTerminal P_cat]

class CryptoSemanticModel (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] where
  CryptoIdentity_type : SynthLean.Expr Lean.Name
  CryptoIdentity_type_closed : SynthLean.Expr.isClosed 0 CryptoIdentity_type = true
  sem_CryptoIdentity_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_CryptoIdentity_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_CryptoIdentity_tp_comm {h0 : 0 < seq.length + 1} : sem_CryptoIdentity_obj ≫ (seq.objs 0 h0).tp = sem_CryptoIdentity_Ty
  CryptoIdentity_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_CryptoIdentity_Ty = I.ofType seq.nilCObj 0 CryptoIdentity_type h0

  Empty_obj_type : SynthLean.Expr Lean.Name
  Empty_obj_type_closed : SynthLean.Expr.isClosed 0 Empty_obj_type = true
  sem_Empty_obj_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Empty_obj_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Empty_obj_tp_comm {h0 : 0 < seq.length + 1} : sem_Empty_obj_obj ≫ (seq.objs 0 h0).tp = sem_Empty_obj_Ty
  Empty_obj_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Empty_obj_Ty = I.ofType seq.nilCObj 0 Empty_obj_type h0

  Unit_obj_type : SynthLean.Expr Lean.Name
  Unit_obj_type_closed : SynthLean.Expr.isClosed 0 Unit_obj_type = true
  sem_Unit_obj_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Unit_obj_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Unit_obj_tp_comm {h0 : 0 < seq.length + 1} : sem_Unit_obj_obj ≫ (seq.objs 0 h0).tp = sem_Unit_obj_Ty
  Unit_obj_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Unit_obj_Ty = I.ofType seq.nilCObj 0 Unit_obj_type h0

  Coprod_type : SynthLean.Expr Lean.Name
  Coprod_type_closed : SynthLean.Expr.isClosed 0 Coprod_type = true
  sem_Coprod_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Coprod_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Coprod_tp_comm {h0 : 0 < seq.length + 1} : sem_Coprod_obj ≫ (seq.objs 0 h0).tp = sem_Coprod_Ty
  Coprod_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Coprod_Ty = I.ofType seq.nilCObj 0 Coprod_type h0

  Category_type : SynthLean.Expr Lean.Name
  Category_type_closed : SynthLean.Expr.isClosed 0 Category_type = true
  sem_Category_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Category_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Category_tp_comm {h0 : 0 < seq.length + 1} : sem_Category_obj ≫ (seq.objs 0 h0).tp = sem_Category_Ty
  Category_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Category_Ty = I.ofType seq.nilCObj 0 Category_type h0

  Presheaf_type : SynthLean.Expr Lean.Name
  Presheaf_type_closed : SynthLean.Expr.isClosed 0 Presheaf_type = true
  sem_Presheaf_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Presheaf_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Presheaf_tp_comm {h0 : 0 < seq.length + 1} : sem_Presheaf_obj ≫ (seq.objs 0 h0).tp = sem_Presheaf_Ty
  Presheaf_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Presheaf_Ty = I.ofType seq.nilCObj 0 Presheaf_type h0

  NatTrans_type : SynthLean.Expr Lean.Name
  NatTrans_type_closed : SynthLean.Expr.isClosed 0 NatTrans_type = true
  sem_NatTrans_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_NatTrans_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_NatTrans_tp_comm {h0 : 0 < seq.length + 1} : sem_NatTrans_obj ≫ (seq.objs 0 h0).tp = sem_NatTrans_Ty
  NatTrans_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_NatTrans_Ty = I.ofType seq.nilCObj 0 NatTrans_type h0

  PresheafIso_type : SynthLean.Expr Lean.Name
  PresheafIso_type_closed : SynthLean.Expr.isClosed 0 PresheafIso_type = true
  sem_PresheafIso_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_PresheafIso_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_PresheafIso_tp_comm {h0 : 0 < seq.length + 1} : sem_PresheafIso_obj ≫ (seq.objs 0 h0).tp = sem_PresheafIso_Ty
  PresheafIso_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_PresheafIso_Ty = I.ofType seq.nilCObj 0 PresheafIso_type h0

  yObj_type : SynthLean.Expr Lean.Name
  yObj_type_closed : SynthLean.Expr.isClosed 0 yObj_type = true
  sem_yObj_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_yObj_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_yObj_tp_comm {h0 : 0 < seq.length + 1} : sem_yObj_obj ≫ (seq.objs 0 h0).tp = sem_yObj_Ty
  yObj_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_yObj_Ty = I.ofType seq.nilCObj 0 yObj_type h0

  IsEffObject_type : SynthLean.Expr Lean.Name
  IsEffObject_type_closed : SynthLean.Expr.isClosed 0 IsEffObject_type = true
  sem_IsEffObject_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_IsEffObject_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_IsEffObject_tp_comm {h0 : 0 < seq.length + 1} : sem_IsEffObject_obj ≫ (seq.objs 0 h0).tp = sem_IsEffObject_Ty
  IsEffObject_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_IsEffObject_Ty = I.ofType seq.nilCObj 0 IsEffObject_type h0

  InternalGroupoid_type : SynthLean.Expr Lean.Name
  InternalGroupoid_type_closed : SynthLean.Expr.isClosed 0 InternalGroupoid_type = true
  sem_InternalGroupoid_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_InternalGroupoid_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_InternalGroupoid_tp_comm {h0 : 0 < seq.length + 1} : sem_InternalGroupoid_obj ≫ (seq.objs 0 h0).tp = sem_InternalGroupoid_Ty
  InternalGroupoid_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_InternalGroupoid_Ty = I.ofType seq.nilCObj 0 InternalGroupoid_type h0

  CryptoContext_type : SynthLean.Expr Lean.Name
  CryptoContext_type_closed : SynthLean.Expr.isClosed 0 CryptoContext_type = true
  sem_CryptoContext_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_CryptoContext_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_CryptoContext_tp_comm {h0 : 0 < seq.length + 1} : sem_CryptoContext_obj ≫ (seq.objs 0 h0).tp = sem_CryptoContext_Ty
  CryptoContext_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_CryptoContext_Ty = I.ofType seq.nilCObj 0 CryptoContext_type h0

  Cipher_type : SynthLean.Expr Lean.Name
  Cipher_type_closed : SynthLean.Expr.isClosed 0 Cipher_type = true
  sem_Cipher_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Cipher_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Cipher_tp_comm {h0 : 0 < seq.length + 1} : sem_Cipher_obj ≫ (seq.objs 0 h0).tp = sem_Cipher_Ty
  Cipher_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Cipher_Ty = I.ofType seq.nilCObj 0 Cipher_type h0

  Decipher_type : SynthLean.Expr Lean.Name
  Decipher_type_closed : SynthLean.Expr.isClosed 0 Decipher_type = true
  sem_Decipher_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Decipher_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Decipher_tp_comm {h0 : 0 < seq.length + 1} : sem_Decipher_obj ≫ (seq.objs 0 h0).tp = sem_Decipher_Ty
  Decipher_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Decipher_Ty = I.ofType seq.nilCObj 0 Decipher_type h0

  Theorem_Correctness_Path_type : SynthLean.Expr Lean.Name
  Theorem_Correctness_Path_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_type = true
  sem_Theorem_Correctness_Path_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  sem_Theorem_Correctness_Path_obj {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  sem_Theorem_Correctness_Path_tp_comm {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_obj ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_Ty
  Theorem_Correctness_Path_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_Ty = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_type h0

  lift_eq_proof_obj {h0 : 0 < seq.length + 1} (Ty : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty) : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
  lift_eq_proof_tp_comm {h0 : 0 < seq.length + 1} (Ty : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty) : lift_eq_proof_obj Ty ≫ (seq.objs 0 h0).tp = Ty

  Cipher_eq_type : SynthLean.Expr Lean.Name
  Cipher_eq_type_closed : SynthLean.Expr.isClosed 0 Cipher_eq_type = true
  sem_Cipher_eq_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  Cipher_eq_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Cipher_eq_Ty = I.ofType seq.nilCObj 0 Cipher_eq_type h0

  Decipher_eq_type : SynthLean.Expr Lean.Name
  Decipher_eq_type_closed : SynthLean.Expr.isClosed 0 Decipher_eq_type = true
  sem_Decipher_eq_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  Decipher_eq_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Decipher_eq_Ty = I.ofType seq.nilCObj 0 Decipher_eq_type h0

  Theorem_Correctness_Path_eq_type : SynthLean.Expr Lean.Name
  Theorem_Correctness_Path_eq_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_eq_type = true
  sem_Theorem_Correctness_Path_eq_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  Theorem_Correctness_Path_eq_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_eq_Ty = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_eq_type h0

  Theorem_Correctness_Path_eps0_type : SynthLean.Expr Lean.Name
  Theorem_Correctness_Path_eps0_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_eps0_type = true
  sem_Theorem_Correctness_Path_eps0_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  Theorem_Correctness_Path_eps0_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_eps0_Ty = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_eps0_type h0

  Theorem_Correctness_Path_eps1_type : SynthLean.Expr Lean.Name
  Theorem_Correctness_Path_eps1_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_eps1_type = true
  sem_Theorem_Correctness_Path_eps1_Ty {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
  Theorem_Correctness_Path_eps1_ofType (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_eps1_Ty = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_eps1_type h0

export CryptoSemanticModel (
  CryptoIdentity_type CryptoIdentity_type_closed sem_CryptoIdentity_Ty sem_CryptoIdentity_obj sem_CryptoIdentity_tp_comm CryptoIdentity_ofType
  Empty_obj_type Empty_obj_type_closed sem_Empty_obj_Ty sem_Empty_obj_obj sem_Empty_obj_tp_comm Empty_obj_ofType
  Unit_obj_type Unit_obj_type_closed sem_Unit_obj_Ty sem_Unit_obj_obj sem_Unit_obj_tp_comm Unit_obj_ofType
  Coprod_type Coprod_type_closed sem_Coprod_Ty sem_Coprod_obj sem_Coprod_tp_comm Coprod_ofType
  Category_type Category_type_closed sem_Category_Ty sem_Category_obj sem_Category_tp_comm Category_ofType
  Presheaf_type Presheaf_type_closed sem_Presheaf_Ty sem_Presheaf_obj sem_Presheaf_tp_comm Presheaf_ofType
  NatTrans_type NatTrans_type_closed sem_NatTrans_Ty sem_NatTrans_obj sem_NatTrans_tp_comm NatTrans_ofType
  PresheafIso_type PresheafIso_type_closed sem_PresheafIso_Ty sem_PresheafIso_obj sem_PresheafIso_tp_comm PresheafIso_ofType
  yObj_type yObj_type_closed sem_yObj_Ty sem_yObj_obj sem_yObj_tp_comm yObj_ofType
  IsEffObject_type IsEffObject_type_closed sem_IsEffObject_Ty sem_IsEffObject_obj sem_IsEffObject_tp_comm IsEffObject_ofType
  InternalGroupoid_type InternalGroupoid_type_closed sem_InternalGroupoid_Ty sem_InternalGroupoid_obj sem_InternalGroupoid_tp_comm InternalGroupoid_ofType
  CryptoContext_type CryptoContext_type_closed sem_CryptoContext_Ty sem_CryptoContext_obj sem_CryptoContext_tp_comm CryptoContext_ofType
  Cipher_type Cipher_type_closed sem_Cipher_Ty sem_Cipher_obj sem_Cipher_tp_comm Cipher_ofType
  Decipher_type Decipher_type_closed sem_Decipher_Ty sem_Decipher_obj sem_Decipher_tp_comm Decipher_ofType
  Theorem_Correctness_Path_type Theorem_Correctness_Path_type_closed sem_Theorem_Correctness_Path_Ty sem_Theorem_Correctness_Path_obj sem_Theorem_Correctness_Path_tp_comm Theorem_Correctness_Path_ofType
  lift_eq_proof_obj lift_eq_proof_tp_comm
  Cipher_eq_type Cipher_eq_type_closed sem_Cipher_eq_Ty Cipher_eq_ofType
  Decipher_eq_type Decipher_eq_type_closed sem_Decipher_eq_Ty Decipher_eq_ofType
  Theorem_Correctness_Path_eq_type Theorem_Correctness_Path_eq_type_closed sem_Theorem_Correctness_Path_eq_Ty Theorem_Correctness_Path_eq_ofType
  Theorem_Correctness_Path_eps0_type Theorem_Correctness_Path_eps0_type_closed sem_Theorem_Correctness_Path_eps0_Ty Theorem_Correctness_Path_eps0_ofType
  Theorem_Correctness_Path_eps1_type Theorem_Correctness_Path_eps1_type_closed sem_Theorem_Correctness_Path_eps1_Ty Theorem_Correctness_Path_eps1_ofType
)

def sem_Cipher_eq_obj {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Cipher_eq_impl 0 0 0
  lift_eq_proof_obj (sem_Cipher_eq_Ty (h0 := h0))

theorem sem_Cipher_eq_tp_comm {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} :
  sem_Cipher_eq_obj ≫ (seq.objs 0 h0).tp = sem_Cipher_eq_Ty := by
  dsimp [sem_Cipher_eq_obj]
  exact lift_eq_proof_tp_comm (sem_Cipher_eq_Ty (h0 := h0))

def sem_Decipher_eq_obj {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Decipher_eq_impl 0 0 0
  lift_eq_proof_obj (sem_Decipher_eq_Ty (h0 := h0))

theorem sem_Decipher_eq_tp_comm {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} :
  sem_Decipher_eq_obj ≫ (seq.objs 0 h0).tp = sem_Decipher_eq_Ty := by
  dsimp [sem_Decipher_eq_obj]
  exact lift_eq_proof_tp_comm (sem_Decipher_eq_Ty (h0 := h0))

def sem_Theorem_Correctness_Path_eq_obj {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Correctness_Path_eq_impl 0
  lift_eq_proof_obj (sem_Theorem_Correctness_Path_eq_Ty (h0 := h0))

theorem sem_Theorem_Correctness_Path_eq_tp_comm {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} :
  sem_Theorem_Correctness_Path_eq_obj ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_eq_Ty := by
  dsimp [sem_Theorem_Correctness_Path_eq_obj]
  exact lift_eq_proof_tp_comm (sem_Theorem_Correctness_Path_eq_Ty (h0 := h0))

def sem_Theorem_Correctness_Path_eps0_obj {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Correctness_Path_eps0_impl 0 0 0
  lift_eq_proof_obj (sem_Theorem_Correctness_Path_eps0_Ty (h0 := h0))

theorem sem_Theorem_Correctness_Path_eps0_tp_comm {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} :
  sem_Theorem_Correctness_Path_eps0_obj ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_eps0_Ty := by
  dsimp [sem_Theorem_Correctness_Path_eps0_obj]
  exact lift_eq_proof_tp_comm (sem_Theorem_Correctness_Path_eps0_Ty (h0 := h0))

def sem_Theorem_Correctness_Path_eps1_obj {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Correctness_Path_eps1_impl 0 0 0
  lift_eq_proof_obj (sem_Theorem_Correctness_Path_eps1_Ty (h0 := h0))

theorem sem_Theorem_Correctness_Path_eps1_tp_comm {seq : UHomSeq P_cat} [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] {h0 : 0 < seq.length + 1} :
  sem_Theorem_Correctness_Path_eps1_obj ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_eps1_Ty := by
  dsimp [sem_Theorem_Correctness_Path_eps1_obj]
  exact lift_eq_proof_tp_comm (sem_Theorem_Correctness_Path_eps1_Ty (h0 := h0))

def cast_sem_to_I (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq]
  {l : Nat} {hl : l < seq.length + 1} {h0 : 0 < seq.length + 1} (h_eq : 0 = l)
  (sem : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm) :
  yoneda.obj seq.nilCObj.fst ⟶ (seq.objs l hl).Tm :=
  sem ≫ CategoryTheory.eqToHom (by subst h_eq; rfl)

def crypto_topos_interpretation (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] :
  Interpretation Lean.Name seq where
  ax c l hl :=
    if hl0 : l = 0 then
      have h0 : 0 < seq.length + 1 := by omega
      if c = `CryptoIdentity then some (cast_sem_to_I seq hl0.symm (sem_CryptoIdentity_obj (h0 := h0)))
      else if c = `Empty_obj then some (cast_sem_to_I seq hl0.symm (sem_Empty_obj_obj (h0 := h0)))
      else if c = `Unit_obj then some (cast_sem_to_I seq hl0.symm (sem_Unit_obj_obj (h0 := h0)))
      else if c = `Coprod then some (cast_sem_to_I seq hl0.symm (sem_Coprod_obj (h0 := h0)))
      else if c = `Category then some (cast_sem_to_I seq hl0.symm (sem_Category_obj (h0 := h0)))
      else if c = `Presheaf then some (cast_sem_to_I seq hl0.symm (sem_Presheaf_obj (h0 := h0)))
      else if c = `NatTrans then some (cast_sem_to_I seq hl0.symm (sem_NatTrans_obj (h0 := h0)))
      else if c = `PresheafIso then some (cast_sem_to_I seq hl0.symm (sem_PresheafIso_obj (h0 := h0)))
      else if c = `yObj then some (cast_sem_to_I seq hl0.symm (sem_yObj_obj (h0 := h0)))
      else if c = `IsEffObject then some (cast_sem_to_I seq hl0.symm (sem_IsEffObject_obj (h0 := h0)))
      else if c = `InternalGroupoid then some (cast_sem_to_I seq hl0.symm (sem_InternalGroupoid_obj (h0 := h0)))
      else if c = `CryptoContext then some (cast_sem_to_I seq hl0.symm (sem_CryptoContext_obj (h0 := h0)))
      else if c = `Cipher then some (cast_sem_to_I seq hl0.symm (sem_Cipher_obj (h0 := h0)))
      else if c = `Decipher then some (cast_sem_to_I seq hl0.symm (sem_Decipher_obj (h0 := h0)))
      else if c = `Theorem_Correctness_Path then some (cast_sem_to_I seq hl0.symm (sem_Theorem_Correctness_Path_obj (h0 := h0)))
      else if c = `Cipher_eq then some (cast_sem_to_I seq hl0.symm (sem_Cipher_eq_obj (h0 := h0)))
      else if c = `Decipher_eq then some (cast_sem_to_I seq hl0.symm (sem_Decipher_eq_obj (h0 := h0)))
      else if c = `Theorem_Correctness_Path_eq then some (cast_sem_to_I seq hl0.symm (sem_Theorem_Correctness_Path_eq_obj (h0 := h0)))
      else if c = `Theorem_Correctness_Path_eps0 then some (cast_sem_to_I seq hl0.symm (sem_Theorem_Correctness_Path_eps0_obj (h0 := h0)))
      else if c = `Theorem_Correctness_Path_eps1 then some (cast_sem_to_I seq hl0.symm (sem_Theorem_Correctness_Path_eps1_obj (h0 := h0)))
      else none
    else none

def crypto_topos_axioms (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq] : SynthLean.Axioms Lean.Name :=
  fun c =>
    if c = `CryptoIdentity then some ⟨(CryptoIdentity_type seq, 0), by exact ⟨CryptoIdentity_type_closed, Nat.zero_le _⟩⟩
    else if c = `Empty_obj then some ⟨(Empty_obj_type seq, 0), by exact ⟨Empty_obj_type_closed, Nat.zero_le _⟩⟩
    else if c = `Unit_obj then some ⟨(Unit_obj_type seq, 0), by exact ⟨Unit_obj_type_closed, Nat.zero_le _⟩⟩
    else if c = `Coprod then some ⟨(Coprod_type seq, 0), by exact ⟨Coprod_type_closed, Nat.zero_le _⟩⟩
    else if c = `Category then some ⟨(Category_type seq, 0), by exact ⟨Category_type_closed, Nat.zero_le _⟩⟩
    else if c = `Presheaf then some ⟨(Presheaf_type seq, 0), by exact ⟨Presheaf_type_closed, Nat.zero_le _⟩⟩
    else if c = `NatTrans then some ⟨(NatTrans_type seq, 0), by exact ⟨NatTrans_type_closed, Nat.zero_le _⟩⟩
    else if c = `PresheafIso then some ⟨(PresheafIso_type seq, 0), by exact ⟨PresheafIso_type_closed, Nat.zero_le _⟩⟩
    else if c = `yObj then some ⟨(yObj_type seq, 0), by exact ⟨yObj_type_closed, Nat.zero_le _⟩⟩
    else if c = `IsEffObject then some ⟨(IsEffObject_type seq, 0), by exact ⟨IsEffObject_type_closed, Nat.zero_le _⟩⟩
    else if c = `InternalGroupoid then some ⟨(InternalGroupoid_type seq, 0), by exact ⟨InternalGroupoid_type_closed, Nat.zero_le _⟩⟩
    else if c = `CryptoContext then some ⟨(CryptoContext_type seq, 0), by exact ⟨CryptoContext_type_closed, Nat.zero_le _⟩⟩
    else if c = `Cipher then some ⟨(Cipher_type seq, 0), by exact ⟨Cipher_type_closed, Nat.zero_le _⟩⟩
    else if c = `Decipher then some ⟨(Decipher_type seq, 0), by exact ⟨Decipher_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path then some ⟨(Theorem_Correctness_Path_type seq, 0), by exact ⟨Theorem_Correctness_Path_type_closed, Nat.zero_le _⟩⟩
    else if c = `Cipher_eq then some ⟨(Cipher_eq_type seq, 0), by exact ⟨Cipher_eq_type_closed, Nat.zero_le _⟩⟩
    else if c = `Decipher_eq then some ⟨(Decipher_eq_type seq, 0), by exact ⟨Decipher_eq_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path_eq then some ⟨(Theorem_Correctness_Path_eq_type seq, 0), by exact ⟨Theorem_Correctness_Path_eq_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path_eps0 then some ⟨(Theorem_Correctness_Path_eps0_type seq, 0), by exact ⟨Theorem_Correctness_Path_eps0_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path_eps1 then some ⟨(Theorem_Correctness_Path_eps1_type seq, 0), by exact ⟨Theorem_Correctness_Path_eps1_type_closed, Nat.zero_le _⟩⟩
    else none

syntax "prove_interpretation_branch " term:max term:max term:max term:max term:max : tactic

macro_rules
  | `(tactic| prove_interpretation_branch $seq $sem_obj $sem_Ty $tp_comm $of_type) =>
    `(tactic| (
      refine Exists.intro (cast_sem_to_I ($seq) rfl ($sem_obj)) (And.intro ?_ ?_)
      · first
          | rfl
          | (unfold crypto_topos_interpretation; simp)
      · refine Exists.intro ($sem_Ty) (And.intro ?_ ?_)
        · have h_of := $of_type
          try dsimp only
          rw [← h_of]
          first
            | exact rfl
            | simp
        · unfold cast_sem_to_I
          simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Category.comp_id,
            CategoryTheory.Category.id_comp, CategoryTheory.Category.assoc]
          exact ($tp_comm)))

instance crypto_topos_interpretation_wf (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq]
  [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq]
  (hlmax : SynthLean.univMax ≤ seq.length) :
  Interpretation.Wf hlmax (crypto_topos_interpretation seq) (crypto_topos_axioms seq) where
  ax := fun {c} {Al} h_ax => by
    cases Al with | mk val h_prop => cases val with | mk A l =>
    unfold crypto_topos_axioms at h_ax
    by_cases hc1 : c = `CryptoIdentity
    { simp only [if_pos hc1] at h_ax
      have h_val : (CryptoIdentity_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
      have hA : A = CryptoIdentity_type seq := (congrArg Prod.fst h_val).symm
      have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
      subst hA; subst hl_eq; subst hc1
      have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
      prove_interpretation_branch seq
        (sem_CryptoIdentity_obj (h0:=h0))
        (sem_CryptoIdentity_Ty (h0:=h0))
        (sem_CryptoIdentity_tp_comm (h0:=h0))
        (CryptoIdentity_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
    { by_cases hc2 : c = `Empty_obj
      { simp only [if_neg hc1, if_pos hc2] at h_ax
        have h_val : (Empty_obj_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
        have hA : A = Empty_obj_type seq := (congrArg Prod.fst h_val).symm
        have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
        subst hA; subst hl_eq; subst hc2
        have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
        prove_interpretation_branch seq
          (sem_Empty_obj_obj (h0:=h0))
          (sem_Empty_obj_Ty (h0:=h0))
          (sem_Empty_obj_tp_comm (h0:=h0))
          (Empty_obj_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
      { by_cases hc3 : c = `Unit_obj
        { simp only [if_neg hc1, if_neg hc2, if_pos hc3] at h_ax
          have h_val : (Unit_obj_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
          have hA : A = Unit_obj_type seq := (congrArg Prod.fst h_val).symm
          have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
          subst hA; subst hl_eq; subst hc3
          have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
          prove_interpretation_branch seq
            (sem_Unit_obj_obj (h0:=h0))
            (sem_Unit_obj_Ty (h0:=h0))
            (sem_Unit_obj_tp_comm (h0:=h0))
            (Unit_obj_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
        { by_cases hc4 : c = `Coprod
          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_pos hc4] at h_ax
            have h_val : (Coprod_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
            have hA : A = Coprod_type seq := (congrArg Prod.fst h_val).symm
            have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
            subst hA; subst hl_eq; subst hc4
            have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
            prove_interpretation_branch seq
              (sem_Coprod_obj (h0:=h0))
              (sem_Coprod_Ty (h0:=h0))
              (sem_Coprod_tp_comm (h0:=h0))
              (Coprod_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
          { by_cases hc5 : c = `Category
            { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_pos hc5] at h_ax
              have h_val : (Category_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
              have hA : A = Category_type seq := (congrArg Prod.fst h_val).symm
              have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
              subst hA; subst hl_eq; subst hc5
              have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
              prove_interpretation_branch seq
                (sem_Category_obj (h0:=h0))
                (sem_Category_Ty (h0:=h0))
                (sem_Category_tp_comm (h0:=h0))
                (Category_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
            { by_cases hc6 : c = `Presheaf
              { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_pos hc6] at h_ax
                have h_val : (Presheaf_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                have hA : A = Presheaf_type seq := (congrArg Prod.fst h_val).symm
                have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                subst hA; subst hl_eq; subst hc6
                have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                prove_interpretation_branch seq
                  (sem_Presheaf_obj (h0:=h0))
                  (sem_Presheaf_Ty (h0:=h0))
                  (sem_Presheaf_tp_comm (h0:=h0))
                  (Presheaf_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
              { by_cases hc7 : c = `NatTrans
                { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_pos hc7] at h_ax
                  have h_val : (NatTrans_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                  have hA : A = NatTrans_type seq := (congrArg Prod.fst h_val).symm
                  have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                  subst hA; subst hl_eq; subst hc7
                  have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                  prove_interpretation_branch seq
                    (sem_NatTrans_obj (h0:=h0))
                    (sem_NatTrans_Ty (h0:=h0))
                    (sem_NatTrans_tp_comm (h0:=h0))
                    (NatTrans_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                { by_cases hc8 : c = `PresheafIso
                  { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_pos hc8] at h_ax
                    have h_val : (PresheafIso_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                    have hA : A = PresheafIso_type seq := (congrArg Prod.fst h_val).symm
                    have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                    subst hA; subst hl_eq; subst hc8
                    have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                    prove_interpretation_branch seq
                      (sem_PresheafIso_obj (h0:=h0))
                      (sem_PresheafIso_Ty (h0:=h0))
                      (sem_PresheafIso_tp_comm (h0:=h0))
                      (PresheafIso_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                  { by_cases hc9 : c = `yObj
                    { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_pos hc9] at h_ax
                      have h_val : (yObj_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                      have hA : A = yObj_type seq := (congrArg Prod.fst h_val).symm
                      have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                      subst hA; subst hl_eq; subst hc9
                      have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                      prove_interpretation_branch seq
                        (sem_yObj_obj (h0:=h0))
                        (sem_yObj_Ty (h0:=h0))
                        (sem_yObj_tp_comm (h0:=h0))
                        (yObj_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                    { by_cases hc10 : c = `IsEffObject
                      { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_pos hc10] at h_ax
                        have h_val : (IsEffObject_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                        have hA : A = IsEffObject_type seq := (congrArg Prod.fst h_val).symm
                        have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                        subst hA; subst hl_eq; subst hc10
                        have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                        prove_interpretation_branch seq
                          (sem_IsEffObject_obj (h0:=h0))
                          (sem_IsEffObject_Ty (h0:=h0))
                          (sem_IsEffObject_tp_comm (h0:=h0))
                          (IsEffObject_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                      { by_cases hc11 : c = `InternalGroupoid
                        { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_pos hc11] at h_ax
                          have h_val : (InternalGroupoid_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                          have hA : A = InternalGroupoid_type seq := (congrArg Prod.fst h_val).symm
                          have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                          subst hA; subst hl_eq; subst hc11
                          have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                          prove_interpretation_branch seq
                            (sem_InternalGroupoid_obj (h0:=h0))
                            (sem_InternalGroupoid_Ty (h0:=h0))
                            (sem_InternalGroupoid_tp_comm (h0:=h0))
                            (InternalGroupoid_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                        { by_cases hc12 : c = `CryptoContext
                          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_pos hc12] at h_ax
                            have h_val : (CryptoContext_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                            have hA : A = CryptoContext_type seq := (congrArg Prod.fst h_val).symm
                            have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                            subst hA; subst hl_eq; subst hc12
                            have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                            prove_interpretation_branch seq
                              (sem_CryptoContext_obj (h0:=h0))
                              (sem_CryptoContext_Ty (h0:=h0))
                              (sem_CryptoContext_tp_comm (h0:=h0))
                              (CryptoContext_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                          { by_cases hc13 : c = `Cipher
                            { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_pos hc13] at h_ax
                              have h_val : (Cipher_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                              have hA : A = Cipher_type seq := (congrArg Prod.fst h_val).symm
                              have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                              subst hA; subst hl_eq; subst hc13
                              have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                              prove_interpretation_branch seq
                                (sem_Cipher_obj (h0:=h0))
                                (sem_Cipher_Ty (h0:=h0))
                                (sem_Cipher_tp_comm (h0:=h0))
                                (Cipher_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                            { by_cases hc14 : c = `Decipher
                              { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_pos hc14] at h_ax
                                have h_val : (Decipher_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                have hA : A = Decipher_type seq := (congrArg Prod.fst h_val).symm
                                have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                                subst hA; subst hl_eq; subst hc14
                                have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                                prove_interpretation_branch seq
                                  (sem_Decipher_obj (h0:=h0))
                                  (sem_Decipher_Ty (h0:=h0))
                                  (sem_Decipher_tp_comm (h0:=h0))
                                  (Decipher_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                              { by_cases hc15 : c = `Theorem_Correctness_Path
                                { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_pos hc15] at h_ax
                                  have h_val : (Theorem_Correctness_Path_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                  have hA : A = Theorem_Correctness_Path_type seq := (congrArg Prod.fst h_val).symm
                                  have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                                  subst hA; subst hl_eq; subst hc15
                                  have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                                  prove_interpretation_branch seq
                                    (sem_Theorem_Correctness_Path_obj (h0:=h0))
                                    (sem_Theorem_Correctness_Path_Ty (h0:=h0))
                                    (sem_Theorem_Correctness_Path_tp_comm (h0:=h0))
                                    (Theorem_Correctness_Path_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                                { by_cases hc16 : c = `Cipher_eq
                                  { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_pos hc16] at h_ax
                                    have h_val : (Cipher_eq_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                    have hA : A = Cipher_eq_type seq := (congrArg Prod.fst h_val).symm
                                    have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                                    subst hA; subst hl_eq; subst hc16
                                    have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                                    prove_interpretation_branch seq
                                      (sem_Cipher_eq_obj (h0:=h0))
                                      (sem_Cipher_eq_Ty (h0:=h0))
                                      (sem_Cipher_eq_tp_comm (h0:=h0))
                                      (Cipher_eq_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                                  { by_cases hc17 : c = `Decipher_eq
                                    { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_pos hc17] at h_ax
                                      have h_val : (Decipher_eq_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                      have hA : A = Decipher_eq_type seq := (congrArg Prod.fst h_val).symm
                                      have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                                      subst hA; subst hl_eq; subst hc17
                                      have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                                      prove_interpretation_branch seq
                                        (sem_Decipher_eq_obj (h0:=h0))
                                        (sem_Decipher_eq_Ty (h0:=h0))
                                        (sem_Decipher_eq_tp_comm (h0:=h0))
                                        (Decipher_eq_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                                    { by_cases hc18 : c = `Theorem_Correctness_Path_eq
                                      { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_pos hc18] at h_ax
                                        have h_val : (Theorem_Correctness_Path_eq_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                        have hA : A = Theorem_Correctness_Path_eq_type seq := (congrArg Prod.fst h_val).symm
                                        have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                                        subst hA; subst hl_eq; subst hc18
                                        have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                                        prove_interpretation_branch seq
                                          (sem_Theorem_Correctness_Path_eq_obj (h0:=h0))
                                          (sem_Theorem_Correctness_Path_eq_Ty (h0:=h0))
                                          (sem_Theorem_Correctness_Path_eq_tp_comm (h0:=h0))
                                          (Theorem_Correctness_Path_eq_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                                      { by_cases hc19 : c = `Theorem_Correctness_Path_eps0
                                        { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_neg hc18, if_pos hc19] at h_ax
                                          have h_val : (Theorem_Correctness_Path_eps0_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                          have hA : A = Theorem_Correctness_Path_eps0_type seq := (congrArg Prod.fst h_val).symm
                                          have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                                          subst hA; subst hl_eq; subst hc19
                                          have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                                          prove_interpretation_branch seq
                                            (sem_Theorem_Correctness_Path_eps0_obj (h0:=h0))
                                            (sem_Theorem_Correctness_Path_eps0_Ty (h0:=h0))
                                            (sem_Theorem_Correctness_Path_eps0_tp_comm (h0:=h0))
                                            (Theorem_Correctness_Path_eps0_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                                        { by_cases hc20 : c = `Theorem_Correctness_Path_eps1
                                          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_neg hc18, if_neg hc19, if_pos hc20] at h_ax
                                            have h_val : (Theorem_Correctness_Path_eps1_type seq, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                            have hA : A = Theorem_Correctness_Path_eps1_type seq := (congrArg Prod.fst h_val).symm
                                            have hl_eq : l = 0 := (congrArg Prod.snd h_val).symm
                                            subst hA; subst hl_eq; subst hc20
                                            have h0 : 0 < seq.length + 1 := Nat.zero_lt_succ _
                                            prove_interpretation_branch seq
                                              (sem_Theorem_Correctness_Path_eps1_obj (h0:=h0))
                                              (sem_Theorem_Correctness_Path_eps1_Ty (h0:=h0))
                                              (sem_Theorem_Correctness_Path_eps1_tp_comm (h0:=h0))
                                              (Theorem_Correctness_Path_eps1_ofType (crypto_topos_interpretation seq) (h0:=h0)) }
                                          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_neg hc18, if_neg hc19, if_neg hc20] at h_ax
                                            contradiction } } } } } } } } } } } } } } } } } } } }

set_option linter.unusedSectionVars false

instance crypto_topos_wf_fact (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq]
  {hlmax : SynthLean.univMax ≤ seq.length} :
  Fact (Interpretation.Wf hlmax (crypto_topos_interpretation seq) (crypto_topos_axioms seq)) :=
  ⟨crypto_topos_interpretation_wf seq hlmax⟩

theorem crypto_absolute_soundness
  (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq]
  {hlmax : SynthLean.univMax ≤ seq.length}
  {Γ : SynthLean.Ctx Lean.Name} {t A : SynthLean.Expr Lean.Name} {l : Nat}
  (deriv : (crypto_topos_axioms seq) ∣ Γ ⊢[l] t : A) :
  (crypto_topos_interpretation seq).interpTm (slen := hlmax) deriv ≫ (seq.objs l (deriv.lt_slen hlmax)).tp =
  (crypto_topos_interpretation seq).interpTy (slen := hlmax) deriv.wf_tp :=
  Interpretation.interpTm_tp (slen := hlmax) deriv

theorem crypto_absolute_eq_soundness
  (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] [CryptoSemanticModel seq]
  {hlmax : SynthLean.univMax ≤ seq.length}
  {Γ : SynthLean.Ctx Lean.Name} {t u A : SynthLean.Expr Lean.Name} {l : Nat}
  (deriv : (crypto_topos_axioms seq) ∣ Γ ⊢[l] t ≡ u : A) :
  (crypto_topos_interpretation seq).interpTm (slen := hlmax) deriv.wf_left =
  (crypto_topos_interpretation seq).interpTm (slen := hlmax) deriv.wf_right :=
  Interpretation.interpTm_eq (slen := hlmax) deriv

end
