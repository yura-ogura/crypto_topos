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

import HoTTLean.Frontend.Commands
import HoTTLean.Model.Natural.Interpretation
import Lean
import CryptoTopos.SemanticProofs

set_option linter.unusedVariables false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

noncomputable section

open CategoryTheory
open SynthLean
open NaturalModel.Universe
open SemanticProofs

universe u v

variable {P_cat : Type u} [Category.{v, u} P_cat] [SmallCategory P_cat] [ChosenTerminal P_cat]

axiom sem_CryptoIdentity_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_CryptoIdentity_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_CryptoIdentity_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_CryptoIdentity_obj seq ≫ (seq.objs 0 h0).tp = sem_CryptoIdentity_Ty seq
axiom CryptoIdentity_type : SynthLean.Expr Lean.Name
axiom CryptoIdentity_type_closed : SynthLean.Expr.isClosed 0 CryptoIdentity_type = true
axiom CryptoIdentity_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_CryptoIdentity_Ty seq = I.ofType seq.nilCObj 0 CryptoIdentity_type h0

axiom sem_Empty_obj_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Empty_obj_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Empty_obj_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Empty_obj_obj seq ≫ (seq.objs 0 h0).tp = sem_Empty_obj_Ty seq
axiom Empty_obj_type : SynthLean.Expr Lean.Name
axiom Empty_obj_type_closed : SynthLean.Expr.isClosed 0 Empty_obj_type = true
axiom Empty_obj_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Empty_obj_Ty seq = I.ofType seq.nilCObj 0 Empty_obj_type h0

axiom sem_Unit_obj_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Unit_obj_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Unit_obj_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Unit_obj_obj seq ≫ (seq.objs 0 h0).tp = sem_Unit_obj_Ty seq
axiom Unit_obj_type : SynthLean.Expr Lean.Name
axiom Unit_obj_type_closed : SynthLean.Expr.isClosed 0 Unit_obj_type = true
axiom Unit_obj_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Unit_obj_Ty seq = I.ofType seq.nilCObj 0 Unit_obj_type h0

axiom sem_Coprod_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Coprod_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Coprod_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Coprod_obj seq ≫ (seq.objs 0 h0).tp = sem_Coprod_Ty seq
axiom Coprod_type : SynthLean.Expr Lean.Name
axiom Coprod_type_closed : SynthLean.Expr.isClosed 0 Coprod_type = true
axiom Coprod_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Coprod_Ty seq = I.ofType seq.nilCObj 0 Coprod_type h0

axiom sem_Category_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Category_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Category_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Category_obj seq ≫ (seq.objs 0 h0).tp = sem_Category_Ty seq
axiom Category_type : SynthLean.Expr Lean.Name
axiom Category_type_closed : SynthLean.Expr.isClosed 0 Category_type = true
axiom Category_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Category_Ty seq = I.ofType seq.nilCObj 0 Category_type h0

axiom sem_Presheaf_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Presheaf_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Presheaf_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Presheaf_obj seq ≫ (seq.objs 0 h0).tp = sem_Presheaf_Ty seq
axiom Presheaf_type : SynthLean.Expr Lean.Name
axiom Presheaf_type_closed : SynthLean.Expr.isClosed 0 Presheaf_type = true
axiom Presheaf_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Presheaf_Ty seq = I.ofType seq.nilCObj 0 Presheaf_type h0

axiom sem_NatTrans_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_NatTrans_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_NatTrans_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_NatTrans_obj seq ≫ (seq.objs 0 h0).tp = sem_NatTrans_Ty seq
axiom NatTrans_type : SynthLean.Expr Lean.Name
axiom NatTrans_type_closed : SynthLean.Expr.isClosed 0 NatTrans_type = true
axiom NatTrans_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_NatTrans_Ty seq = I.ofType seq.nilCObj 0 NatTrans_type h0

axiom sem_PresheafIso_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_PresheafIso_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_PresheafIso_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_PresheafIso_obj seq ≫ (seq.objs 0 h0).tp = sem_PresheafIso_Ty seq
axiom PresheafIso_type : SynthLean.Expr Lean.Name
axiom PresheafIso_type_closed : SynthLean.Expr.isClosed 0 PresheafIso_type = true
axiom PresheafIso_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_PresheafIso_Ty seq = I.ofType seq.nilCObj 0 PresheafIso_type h0

axiom sem_yObj_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_yObj_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_yObj_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_yObj_obj seq ≫ (seq.objs 0 h0).tp = sem_yObj_Ty seq
axiom yObj_type : SynthLean.Expr Lean.Name
axiom yObj_type_closed : SynthLean.Expr.isClosed 0 yObj_type = true
axiom yObj_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_yObj_Ty seq = I.ofType seq.nilCObj 0 yObj_type h0

axiom sem_IsEffObject_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_IsEffObject_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_IsEffObject_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_IsEffObject_obj seq ≫ (seq.objs 0 h0).tp = sem_IsEffObject_Ty seq
axiom IsEffObject_type : SynthLean.Expr Lean.Name
axiom IsEffObject_type_closed : SynthLean.Expr.isClosed 0 IsEffObject_type = true
axiom IsEffObject_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_IsEffObject_Ty seq = I.ofType seq.nilCObj 0 IsEffObject_type h0

axiom sem_InternalGroupoid_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_InternalGroupoid_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_InternalGroupoid_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_InternalGroupoid_obj seq ≫ (seq.objs 0 h0).tp = sem_InternalGroupoid_Ty seq
axiom InternalGroupoid_type : SynthLean.Expr Lean.Name
axiom InternalGroupoid_type_closed : SynthLean.Expr.isClosed 0 InternalGroupoid_type = true
axiom InternalGroupoid_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_InternalGroupoid_Ty seq = I.ofType seq.nilCObj 0 InternalGroupoid_type h0

axiom sem_CryptoContext_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_CryptoContext_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_CryptoContext_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_CryptoContext_obj seq ≫ (seq.objs 0 h0).tp = sem_CryptoContext_Ty seq
axiom CryptoContext_type : SynthLean.Expr Lean.Name
axiom CryptoContext_type_closed : SynthLean.Expr.isClosed 0 CryptoContext_type = true
axiom CryptoContext_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_CryptoContext_Ty seq = I.ofType seq.nilCObj 0 CryptoContext_type h0

axiom sem_Cipher_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Cipher_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Cipher_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Cipher_obj seq ≫ (seq.objs 0 h0).tp = sem_Cipher_Ty seq
axiom Cipher_type : SynthLean.Expr Lean.Name
axiom Cipher_type_closed : SynthLean.Expr.isClosed 0 Cipher_type = true
axiom Cipher_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Cipher_Ty seq = I.ofType seq.nilCObj 0 Cipher_type h0

axiom sem_Decipher_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Decipher_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Decipher_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Decipher_obj seq ≫ (seq.objs 0 h0).tp = sem_Decipher_Ty seq
axiom Decipher_type : SynthLean.Expr Lean.Name
axiom Decipher_type_closed : SynthLean.Expr.isClosed 0 Decipher_type = true
axiom Decipher_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Decipher_Ty seq = I.ofType seq.nilCObj 0 Decipher_type h0

axiom sem_Theorem_Correctness_Path_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm
axiom sem_Theorem_Correctness_Path_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom sem_Theorem_Correctness_Path_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_obj seq ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_Ty seq
axiom Theorem_Correctness_Path_type : SynthLean.Expr Lean.Name
axiom Theorem_Correctness_Path_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_type = true
axiom Theorem_Correctness_Path_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_Ty seq = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_type h0

axiom lift_eq_proof_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1}
  (Ty : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty) : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm

axiom lift_eq_proof_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1}
  (Ty : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty) :
  lift_eq_proof_obj seq Ty ≫ (seq.objs 0 h0).tp = Ty

axiom Cipher_eq_type : SynthLean.Expr Lean.Name
axiom Cipher_eq_type_closed : SynthLean.Expr.isClosed 0 Cipher_eq_type = true
axiom sem_Cipher_eq_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom Cipher_eq_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Cipher_eq_Ty seq = I.ofType seq.nilCObj 0 Cipher_eq_type h0

def sem_Cipher_eq_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Cipher_eq_impl 0 0 0
  lift_eq_proof_obj seq (sem_Cipher_eq_Ty seq)

theorem sem_Cipher_eq_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} :
  sem_Cipher_eq_obj seq ≫ (seq.objs 0 h0).tp = sem_Cipher_eq_Ty seq := by
  dsimp [sem_Cipher_eq_obj]
  exact lift_eq_proof_tp_comm seq (sem_Cipher_eq_Ty seq)

axiom Decipher_eq_type : SynthLean.Expr Lean.Name
axiom Decipher_eq_type_closed : SynthLean.Expr.isClosed 0 Decipher_eq_type = true
axiom sem_Decipher_eq_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom Decipher_eq_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Decipher_eq_Ty seq = I.ofType seq.nilCObj 0 Decipher_eq_type h0

def sem_Decipher_eq_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Decipher_eq_impl 0 0 0
  lift_eq_proof_obj seq (sem_Decipher_eq_Ty seq)

theorem sem_Decipher_eq_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} :
  sem_Decipher_eq_obj seq ≫ (seq.objs 0 h0).tp = sem_Decipher_eq_Ty seq := by
  dsimp [sem_Decipher_eq_obj]
  exact lift_eq_proof_tp_comm seq (sem_Decipher_eq_Ty seq)

axiom Theorem_Correctness_Path_eq_type : SynthLean.Expr Lean.Name
axiom Theorem_Correctness_Path_eq_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_eq_type = true
axiom sem_Theorem_Correctness_Path_eq_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom Theorem_Correctness_Path_eq_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_eq_Ty seq = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_eq_type h0

def sem_Theorem_Correctness_Path_eq_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Correctness_Path_eq_impl 0
  lift_eq_proof_obj seq (sem_Theorem_Correctness_Path_eq_Ty seq)

theorem sem_Theorem_Correctness_Path_eq_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} :
  sem_Theorem_Correctness_Path_eq_obj seq ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_eq_Ty seq := by
  dsimp [sem_Theorem_Correctness_Path_eq_obj]
  exact lift_eq_proof_tp_comm seq (sem_Theorem_Correctness_Path_eq_Ty seq)

axiom Theorem_Correctness_Path_eps0_type : SynthLean.Expr Lean.Name
axiom Theorem_Correctness_Path_eps0_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_eps0_type = true
axiom sem_Theorem_Correctness_Path_eps0_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom Theorem_Correctness_Path_eps0_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_eps0_Ty seq = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_eps0_type h0

def sem_Theorem_Correctness_Path_eps0_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Correctness_Path_eps0_impl 0 0 0
  lift_eq_proof_obj seq (sem_Theorem_Correctness_Path_eps0_Ty seq)

theorem sem_Theorem_Correctness_Path_eps0_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} :
  sem_Theorem_Correctness_Path_eps0_obj seq ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_eps0_Ty seq := by
  dsimp [sem_Theorem_Correctness_Path_eps0_obj]
  exact lift_eq_proof_tp_comm seq (sem_Theorem_Correctness_Path_eps0_Ty seq)

axiom Theorem_Correctness_Path_eps1_type : SynthLean.Expr Lean.Name
axiom Theorem_Correctness_Path_eps1_type_closed : SynthLean.Expr.isClosed 0 Theorem_Correctness_Path_eps1_type = true
axiom sem_Theorem_Correctness_Path_eps1_Ty (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Ty
axiom Theorem_Correctness_Path_eps1_ofType (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] (I : Interpretation Lean.Name seq) {h0 : 0 < seq.length + 1} : sem_Theorem_Correctness_Path_eps1_Ty seq = I.ofType seq.nilCObj 0 Theorem_Correctness_Path_eps1_type h0

def sem_Theorem_Correctness_Path_eps1_obj (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm :=
  let _concrete_proof := concrete_Correctness_Path_eps1_impl 0 0 0
  lift_eq_proof_obj seq (sem_Theorem_Correctness_Path_eps1_Ty seq)

theorem sem_Theorem_Correctness_Path_eps1_tp_comm (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] {h0 : 0 < seq.length + 1} :
  sem_Theorem_Correctness_Path_eps1_obj seq ≫ (seq.objs 0 h0).tp = sem_Theorem_Correctness_Path_eps1_Ty seq := by
  dsimp [sem_Theorem_Correctness_Path_eps1_obj]
  exact lift_eq_proof_tp_comm seq (sem_Theorem_Correctness_Path_eps1_Ty seq)

def cast_sem_to_I (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq]
  {l : Nat} {hl : l < seq.length + 1} {h0 : 0 < seq.length + 1} (h_eq : 0 = l)
  (sem : yoneda.obj seq.nilCObj.fst ⟶ (seq.objs 0 h0).Tm) :
  yoneda.obj seq.nilCObj.fst ⟶ (seq.objs l hl).Tm :=
  sem ≫ CategoryTheory.eqToHom (by subst h_eq; rfl)

def crypto_topos_interpretation (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq] :
  Interpretation Lean.Name seq where
  ax c l hl :=
    if hl0 : l = 0 then
      have h0 : 0 < seq.length + 1 := by omega
      if c = `CryptoIdentity then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_CryptoIdentity_obj seq (h0 := h0)))
      else if c = `Empty_obj then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Empty_obj_obj seq (h0 := h0)))
      else if c = `Unit_obj then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Unit_obj_obj seq (h0 := h0)))
      else if c = `Coprod then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Coprod_obj seq (h0 := h0)))
      else if c = `Category then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Category_obj seq (h0 := h0)))
      else if c = `Presheaf then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Presheaf_obj seq (h0 := h0)))
      else if c = `NatTrans then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_NatTrans_obj seq (h0 := h0)))
      else if c = `PresheafIso then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_PresheafIso_obj seq (h0 := h0)))
      else if c = `yObj then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_yObj_obj seq (h0 := h0)))
      else if c = `IsEffObject then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_IsEffObject_obj seq (h0 := h0)))
      else if c = `InternalGroupoid then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_InternalGroupoid_obj seq (h0 := h0)))
      else if c = `CryptoContext then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_CryptoContext_obj seq (h0 := h0)))
      else if c = `Cipher then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Cipher_obj seq (h0 := h0)))
      else if c = `Decipher then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Decipher_obj seq (h0 := h0)))
      else if c = `Theorem_Correctness_Path then some (cast_sem_to_I seq (h0 := h0) hl0.symm (sem_Theorem_Correctness_Path_obj seq (h0 := h0)))
      else if c = `Cipher_eq then some (cast_sem_to_I seq (h0:=h0) hl0.symm (sem_Cipher_eq_obj seq (h0:=h0)))
      else if c = `Decipher_eq then some (cast_sem_to_I seq (h0:=h0) hl0.symm (sem_Decipher_eq_obj seq (h0:=h0)))
      else if c = `Theorem_Correctness_Path_eq then some (cast_sem_to_I seq (h0:=h0) hl0.symm (sem_Theorem_Correctness_Path_eq_obj seq (h0:=h0)))
      else if c = `Theorem_Correctness_Path_eps0 then some (cast_sem_to_I seq (h0:=h0) hl0.symm (sem_Theorem_Correctness_Path_eps0_obj seq (h0:=h0)))
      else if c = `Theorem_Correctness_Path_eps1 then some (cast_sem_to_I seq (h0:=h0) hl0.symm (sem_Theorem_Correctness_Path_eps1_obj seq (h0:=h0)))
      else none
    else none

def crypto_topos_axioms : SynthLean.Axioms Lean.Name :=
  fun c =>
    if c = `CryptoIdentity then some ⟨(CryptoIdentity_type, 0), by exact ⟨CryptoIdentity_type_closed, Nat.zero_le _⟩⟩
    else if c = `Empty_obj then some ⟨(Empty_obj_type, 0), by exact ⟨Empty_obj_type_closed, Nat.zero_le _⟩⟩
    else if c = `Unit_obj then some ⟨(Unit_obj_type, 0), by exact ⟨Unit_obj_type_closed, Nat.zero_le _⟩⟩
    else if c = `Coprod then some ⟨(Coprod_type, 0), by exact ⟨Coprod_type_closed, Nat.zero_le _⟩⟩
    else if c = `Category then some ⟨(Category_type, 0), by exact ⟨Category_type_closed, Nat.zero_le _⟩⟩
    else if c = `Presheaf then some ⟨(Presheaf_type, 0), by exact ⟨Presheaf_type_closed, Nat.zero_le _⟩⟩
    else if c = `NatTrans then some ⟨(NatTrans_type, 0), by exact ⟨NatTrans_type_closed, Nat.zero_le _⟩⟩
    else if c = `PresheafIso then some ⟨(PresheafIso_type, 0), by exact ⟨PresheafIso_type_closed, Nat.zero_le _⟩⟩
    else if c = `yObj then some ⟨(yObj_type, 0), by exact ⟨yObj_type_closed, Nat.zero_le _⟩⟩
    else if c = `IsEffObject then some ⟨(IsEffObject_type, 0), by exact ⟨IsEffObject_type_closed, Nat.zero_le _⟩⟩
    else if c = `InternalGroupoid then some ⟨(InternalGroupoid_type, 0), by exact ⟨InternalGroupoid_type_closed, Nat.zero_le _⟩⟩
    else if c = `CryptoContext then some ⟨(CryptoContext_type, 0), by exact ⟨CryptoContext_type_closed, Nat.zero_le _⟩⟩
    else if c = `Cipher then some ⟨(Cipher_type, 0), by exact ⟨Cipher_type_closed, Nat.zero_le _⟩⟩
    else if c = `Decipher then some ⟨(Decipher_type, 0), by exact ⟨Decipher_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path then some ⟨(Theorem_Correctness_Path_type, 0), by exact ⟨Theorem_Correctness_Path_type_closed, Nat.zero_le _⟩⟩
    else if c = `Cipher_eq then some ⟨(Cipher_eq_type, 0), by exact ⟨Cipher_eq_type_closed, Nat.zero_le _⟩⟩
    else if c = `Decipher_eq then some ⟨(Decipher_eq_type, 0), by exact ⟨Decipher_eq_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path_eq then some ⟨(Theorem_Correctness_Path_eq_type, 0), by exact ⟨Theorem_Correctness_Path_eq_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path_eps0 then some ⟨(Theorem_Correctness_Path_eps0_type, 0), by exact ⟨Theorem_Correctness_Path_eps0_type_closed, Nat.zero_le _⟩⟩
    else if c = `Theorem_Correctness_Path_eps1 then some ⟨(Theorem_Correctness_Path_eps1_type, 0), by exact ⟨Theorem_Correctness_Path_eps1_type_closed, Nat.zero_le _⟩⟩
    else none

macro "prove_interpretation_branch" seq:ident sem_obj:ident sem_Ty:ident tp_comm:ident of_type:ident : tactic =>
  `(tactic| {
    have h0 : 0 < ($seq).length + 1 := Nat.zero_lt_succ _
    let sc := cast_sem_to_I $seq (l:=0) (hl:=h0) (h0:=h0) rfl ($sem_obj $seq (h0:=h0))
    refine ⟨sc, ?_⟩
    refine ⟨?_, ?_⟩
    { unfold crypto_topos_interpretation; try dsimp; try rfl }
    { refine ⟨$sem_Ty $seq (h0:=h0), ?_⟩
      refine ⟨?_, ?_⟩
      { try simp only [Subtype.val, Prod.fst, Prod.snd]
        have h_eq := $of_type $seq (crypto_topos_interpretation $seq) (h0:=h0)
        try rw [← h_eq]
        try rfl
        try simp }
      { try dsimp [sc, cast_sem_to_I]
        simp only [CategoryTheory.Category.comp_id]
        exact $tp_comm $seq (h0:=h0) } }
  })

instance crypto_topos_interpretation_wf (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq]
  [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq]
  (hlmax : SynthLean.univMax ≤ seq.length) :
  Interpretation.Wf hlmax (crypto_topos_interpretation seq) crypto_topos_axioms where
  ax := fun {c} {Al} h_ax => by
    cases Al with | mk val h_prop => cases val with | mk A l =>
    unfold crypto_topos_axioms at h_ax
    by_cases hc1 : c = `CryptoIdentity
    { simp only [if_pos hc1] at h_ax
      have h_val : (CryptoIdentity_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
      have hA : A = CryptoIdentity_type := (congrArg Prod.fst h_val).symm
      have hl : l = 0 := (congrArg Prod.snd h_val).symm
      subst hA; subst hl; subst hc1
      prove_interpretation_branch seq sem_CryptoIdentity_obj sem_CryptoIdentity_Ty sem_CryptoIdentity_tp_comm CryptoIdentity_ofType }
    { by_cases hc2 : c = `Empty_obj
      { simp only [if_neg hc1, if_pos hc2] at h_ax
        have h_val : (Empty_obj_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
        have hA : A = Empty_obj_type := (congrArg Prod.fst h_val).symm
        have hl : l = 0 := (congrArg Prod.snd h_val).symm
        subst hA; subst hl; subst hc2
        prove_interpretation_branch seq sem_Empty_obj_obj sem_Empty_obj_Ty sem_Empty_obj_tp_comm Empty_obj_ofType }
      { by_cases hc3 : c = `Unit_obj
        { simp only [if_neg hc1, if_neg hc2, if_pos hc3] at h_ax
          have h_val : (Unit_obj_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
          have hA : A = Unit_obj_type := (congrArg Prod.fst h_val).symm
          have hl : l = 0 := (congrArg Prod.snd h_val).symm
          subst hA; subst hl; subst hc3
          prove_interpretation_branch seq sem_Unit_obj_obj sem_Unit_obj_Ty sem_Unit_obj_tp_comm Unit_obj_ofType }
        { by_cases hc4 : c = `Coprod
          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_pos hc4] at h_ax
            have h_val : (Coprod_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
            have hA : A = Coprod_type := (congrArg Prod.fst h_val).symm
            have hl : l = 0 := (congrArg Prod.snd h_val).symm
            subst hA; subst hl; subst hc4
            prove_interpretation_branch seq sem_Coprod_obj sem_Coprod_Ty sem_Coprod_tp_comm Coprod_ofType }
          { by_cases hc5 : c = `Category
            { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_pos hc5] at h_ax
              have h_val : (Category_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
              have hA : A = Category_type := (congrArg Prod.fst h_val).symm
              have hl : l = 0 := (congrArg Prod.snd h_val).symm
              subst hA; subst hl; subst hc5
              prove_interpretation_branch seq sem_Category_obj sem_Category_Ty sem_Category_tp_comm Category_ofType }
            { by_cases hc6 : c = `Presheaf
              { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_pos hc6] at h_ax
                have h_val : (Presheaf_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                have hA : A = Presheaf_type := (congrArg Prod.fst h_val).symm
                have hl : l = 0 := (congrArg Prod.snd h_val).symm
                subst hA; subst hl; subst hc6
                prove_interpretation_branch seq sem_Presheaf_obj sem_Presheaf_Ty sem_Presheaf_tp_comm Presheaf_ofType }
              { by_cases hc7 : c = `NatTrans
                { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_pos hc7] at h_ax
                  have h_val : (NatTrans_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                  have hA : A = NatTrans_type := (congrArg Prod.fst h_val).symm
                  have hl : l = 0 := (congrArg Prod.snd h_val).symm
                  subst hA; subst hl; subst hc7
                  prove_interpretation_branch seq sem_NatTrans_obj sem_NatTrans_Ty sem_NatTrans_tp_comm NatTrans_ofType }
                { by_cases hc8 : c = `PresheafIso
                  { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_pos hc8] at h_ax
                    have h_val : (PresheafIso_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                    have hA : A = PresheafIso_type := (congrArg Prod.fst h_val).symm
                    have hl : l = 0 := (congrArg Prod.snd h_val).symm
                    subst hA; subst hl; subst hc8
                    prove_interpretation_branch seq sem_PresheafIso_obj sem_PresheafIso_Ty sem_PresheafIso_tp_comm PresheafIso_ofType }
                  { by_cases hc9 : c = `yObj
                    { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_pos hc9] at h_ax
                      have h_val : (yObj_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                      have hA : A = yObj_type := (congrArg Prod.fst h_val).symm
                      have hl : l = 0 := (congrArg Prod.snd h_val).symm
                      subst hA; subst hl; subst hc9
                      prove_interpretation_branch seq sem_yObj_obj sem_yObj_Ty sem_yObj_tp_comm yObj_ofType }
                    { by_cases hc10 : c = `IsEffObject
                      { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_pos hc10] at h_ax
                        have h_val : (IsEffObject_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                        have hA : A = IsEffObject_type := (congrArg Prod.fst h_val).symm
                        have hl : l = 0 := (congrArg Prod.snd h_val).symm
                        subst hA; subst hl; subst hc10
                        prove_interpretation_branch seq sem_IsEffObject_obj sem_IsEffObject_Ty sem_IsEffObject_tp_comm IsEffObject_ofType }
                      { by_cases hc11 : c = `InternalGroupoid
                        { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_pos hc11] at h_ax
                          have h_val : (InternalGroupoid_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                          have hA : A = InternalGroupoid_type := (congrArg Prod.fst h_val).symm
                          have hl : l = 0 := (congrArg Prod.snd h_val).symm
                          subst hA; subst hl; subst hc11
                          prove_interpretation_branch seq sem_InternalGroupoid_obj sem_InternalGroupoid_Ty sem_InternalGroupoid_tp_comm InternalGroupoid_ofType }
                        { by_cases hc12 : c = `CryptoContext
                          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_pos hc12] at h_ax
                            have h_val : (CryptoContext_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                            have hA : A = CryptoContext_type := (congrArg Prod.fst h_val).symm
                            have hl : l = 0 := (congrArg Prod.snd h_val).symm
                            subst hA; subst hl; subst hc12
                            prove_interpretation_branch seq sem_CryptoContext_obj sem_CryptoContext_Ty sem_CryptoContext_tp_comm CryptoContext_ofType }
                          { by_cases hc13 : c = `Cipher
                            { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_pos hc13] at h_ax
                              have h_val : (Cipher_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                              have hA : A = Cipher_type := (congrArg Prod.fst h_val).symm
                              have hl : l = 0 := (congrArg Prod.snd h_val).symm
                              subst hA; subst hl; subst hc13
                              prove_interpretation_branch seq sem_Cipher_obj sem_Cipher_Ty sem_Cipher_tp_comm Cipher_ofType }
                            { by_cases hc14 : c = `Decipher
                              { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_pos hc14] at h_ax
                                have h_val : (Decipher_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                have hA : A = Decipher_type := (congrArg Prod.fst h_val).symm
                                have hl : l = 0 := (congrArg Prod.snd h_val).symm
                                subst hA; subst hl; subst hc14
                                prove_interpretation_branch seq sem_Decipher_obj sem_Decipher_Ty sem_Decipher_tp_comm Decipher_ofType }
                              { by_cases hc15 : c = `Theorem_Correctness_Path
                                { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_pos hc15] at h_ax
                                  have h_val : (Theorem_Correctness_Path_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                  have hA : A = Theorem_Correctness_Path_type := (congrArg Prod.fst h_val).symm
                                  have hl : l = 0 := (congrArg Prod.snd h_val).symm
                                  subst hA; subst hl; subst hc15
                                  prove_interpretation_branch seq sem_Theorem_Correctness_Path_obj sem_Theorem_Correctness_Path_Ty sem_Theorem_Correctness_Path_tp_comm Theorem_Correctness_Path_ofType }
                                { by_cases hc16 : c = `Cipher_eq
                                  { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_pos hc16] at h_ax
                                    have h_val : (Cipher_eq_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                    have hA : A = Cipher_eq_type := (congrArg Prod.fst h_val).symm
                                    have hl : l = 0 := (congrArg Prod.snd h_val).symm
                                    subst hA; subst hl; subst hc16
                                    prove_interpretation_branch seq sem_Cipher_eq_obj sem_Cipher_eq_Ty sem_Cipher_eq_tp_comm Cipher_eq_ofType }
                                  { by_cases hc17 : c = `Decipher_eq
                                    { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_pos hc17] at h_ax
                                      have h_val : (Decipher_eq_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                      have hA : A = Decipher_eq_type := (congrArg Prod.fst h_val).symm
                                      have hl : l = 0 := (congrArg Prod.snd h_val).symm
                                      subst hA; subst hl; subst hc17
                                      prove_interpretation_branch seq sem_Decipher_eq_obj sem_Decipher_eq_Ty sem_Decipher_eq_tp_comm Decipher_eq_ofType }
                                    { by_cases hc18 : c = `Theorem_Correctness_Path_eq
                                      { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_pos hc18] at h_ax
                                        have h_val : (Theorem_Correctness_Path_eq_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                        have hA : A = Theorem_Correctness_Path_eq_type := (congrArg Prod.fst h_val).symm
                                        have hl : l = 0 := (congrArg Prod.snd h_val).symm
                                        subst hA; subst hl; subst hc18
                                        prove_interpretation_branch seq sem_Theorem_Correctness_Path_eq_obj sem_Theorem_Correctness_Path_eq_Ty sem_Theorem_Correctness_Path_eq_tp_comm Theorem_Correctness_Path_eq_ofType }
                                      { by_cases hc19 : c = `Theorem_Correctness_Path_eps0
                                        { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_neg hc18, if_pos hc19] at h_ax
                                          have h_val : (Theorem_Correctness_Path_eps0_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                          have hA : A = Theorem_Correctness_Path_eps0_type := (congrArg Prod.fst h_val).symm
                                          have hl : l = 0 := (congrArg Prod.snd h_val).symm
                                          subst hA; subst hl; subst hc19
                                          prove_interpretation_branch seq sem_Theorem_Correctness_Path_eps0_obj sem_Theorem_Correctness_Path_eps0_Ty sem_Theorem_Correctness_Path_eps0_tp_comm Theorem_Correctness_Path_eps0_ofType }
                                        { by_cases hc20 : c = `Theorem_Correctness_Path_eps1
                                          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_neg hc18, if_neg hc19, if_pos hc20] at h_ax
                                            have h_val : (Theorem_Correctness_Path_eps1_type, 0) = (A, l) := congrArg Subtype.val (Option.some.inj h_ax)
                                            have hA : A = Theorem_Correctness_Path_eps1_type := (congrArg Prod.fst h_val).symm
                                            have hl : l = 0 := (congrArg Prod.snd h_val).symm
                                            subst hA; subst hl; subst hc20
                                            prove_interpretation_branch seq sem_Theorem_Correctness_Path_eps1_obj sem_Theorem_Correctness_Path_eps1_Ty sem_Theorem_Correctness_Path_eps1_tp_comm Theorem_Correctness_Path_eps1_ofType }
                                          { simp only [if_neg hc1, if_neg hc2, if_neg hc3, if_neg hc4, if_neg hc5, if_neg hc6, if_neg hc7, if_neg hc8, if_neg hc9, if_neg hc10, if_neg hc11, if_neg hc12, if_neg hc13, if_neg hc14, if_neg hc15, if_neg hc16, if_neg hc17, if_neg hc18, if_neg hc19, if_neg hc20] at h_ax
                                            contradiction } } } } } } } } } } } } } } } } } } } }

set_option linter.unusedSectionVars false

instance crypto_topos_wf_fact (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq]
  {hlmax : SynthLean.univMax ≤ seq.length} :
  Fact (Interpretation.Wf hlmax (crypto_topos_interpretation seq) crypto_topos_axioms) :=
  ⟨crypto_topos_interpretation_wf seq hlmax⟩

theorem crypto_absolute_soundness
  (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq]
  {hlmax : SynthLean.univMax ≤ seq.length}
  {Γ : SynthLean.Ctx Lean.Name} {t A : SynthLean.Expr Lean.Name} {l : Nat}
  (deriv : crypto_topos_axioms ∣ Γ ⊢[l] t : A) :
  (crypto_topos_interpretation seq).interpTm (slen := hlmax) deriv ≫ (seq.objs l (deriv.lt_slen hlmax)).tp =
  (crypto_topos_interpretation seq).interpTy (slen := hlmax) deriv.wf_tp :=
  Interpretation.interpTm_tp (slen := hlmax) deriv

theorem crypto_absolute_eq_soundness
  (seq : UHomSeq P_cat) [UHomSeq.PiSeq seq] [UHomSeq.SigSeq seq] [UHomSeq.IdSeq seq]
  {hlmax : SynthLean.univMax ≤ seq.length}
  {Γ : SynthLean.Ctx Lean.Name} {t u A : SynthLean.Expr Lean.Name} {l : Nat}
  (deriv : crypto_topos_axioms ∣ Γ ⊢[l] t ≡ u : A) :
  (crypto_topos_interpretation seq).interpTm (slen := hlmax) deriv.wf_left =
  (crypto_topos_interpretation seq).interpTm (slen := hlmax) deriv.wf_right :=
  Interpretation.interpTm_eq (slen := hlmax) deriv

end
