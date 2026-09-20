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
import HoTTLean.Model.Natural.NaturalModel
import HoTTLean.Model.Natural.UHom
import HoTTLean.Model.Natural.Interpretation
import CryptoTopos.Frontend
import CryptoTopos.Model
import CryptoTopos.Interpretation

set_option linter.unusedVariables false
set_option maxHeartbeats 0

noncomputable section

open CategoryTheory
open SynthLean
open NaturalModel
open NaturalModel.Universe

universe u v

variable {P_cat : Type u} [CategoryTheory.Category.{v, u} P_cat] [SmallCategory P_cat] [ChosenTerminal P_cat]

#check Cipher
#check Decipher
#check Theorem_Correctness_Path
#check Theorem_Correctness_Path_eps0

theorem crypto_topos_absolute_soundness
    (seq : UHomSeq P_cat)
    [UHomSeq.PiSeq seq]
    [UHomSeq.SigSeq seq]
    [UHomSeq.IdSeq seq]
    [CryptoSemanticModel seq]
    (hlmax : SynthLean.univMax ≤ seq.length)
    {Γ : Ctx Lean.Name} {t A : Expr Lean.Name} {l : Nat}
    (sΓ : seq.CObj)
    (h_ctx_sem : sΓ ∈ (crypto_topos_interpretation seq).ofCtx Γ)
    (h_typing : (crypto_topos_axioms seq) ∣ Γ ⊢[l] t : A) : -- ★ 修正2: seq を渡す
    ∃ (t_sem : yoneda.obj sΓ.1 ⟶ (seq.objs l (h_typing.lt_slen hlmax)).Tm)
      (A_sem : yoneda.obj sΓ.1 ⟶ (seq.objs l (h_typing.lt_slen hlmax)).Ty),
      t_sem ≫ (seq.objs l (h_typing.lt_slen hlmax)).tp = A_sem := by
  
  haveI : Fact ((crypto_topos_interpretation seq).Wf hlmax (crypto_topos_axioms seq)) :=
    ⟨crypto_topos_interpretation_wf seq hlmax⟩

  have sound_tm := (Interpretation.ofType_ofTerm_sound (s := seq) (I := crypto_topos_interpretation seq) (slen := hlmax)).2.2.2.1 h_typing

  rcases sound_tm with ⟨sΓ', hΓ_mem, llen, sA, hA_mem, st, ht_mem, st_tp⟩

  have h_eq : sΓ' = sΓ := Part.mem_unique hΓ_mem h_ctx_sem
  subst h_eq

  exact ⟨st, sA, st_tp⟩

end

