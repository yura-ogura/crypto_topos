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

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 0
declare_theory crypto_topos

crypto_topos axiom CryptoIdentity : {A : Type} → A → A → Type
crypto_topos axiom Id_refl : {A : Type} → (a : A) → CryptoIdentity a a
crypto_topos axiom Id_symm : {A : Type} → {a b : A} → CryptoIdentity a b → CryptoIdentity b a
crypto_topos axiom Id_trans : {A : Type} → {a b c : A} → CryptoIdentity a b → CryptoIdentity b c → CryptoIdentity a c
crypto_topos axiom Id_congr : {A B : Type} → (f : A → B) → {a b : A} → CryptoIdentity a b → CryptoIdentity (f a) (f b)

crypto_topos axiom crypto_funext : {A B : Type} → {f g : A → B} →
  ((x : A) → CryptoIdentity (f x) (g x)) → CryptoIdentity f g

crypto_topos axiom Empty_obj : Type
crypto_topos axiom Empty_rec : {A : Type} → Empty_obj → A

crypto_topos axiom Unit_obj : Type
crypto_topos axiom unit_star : Unit_obj

crypto_topos axiom Coprod : Type → Type → Type
crypto_topos axiom Coprod.inl : {A B : Type} → A → Coprod A B
crypto_topos axiom Coprod.inr : {A B : Type} → B → Coprod A B
crypto_topos axiom Coprod.casesOn : {A B C : Type} → (A → C) → (B → C) → Coprod A B → C

crypto_topos def Prod_obj (A B : Type) : Type :=
  Sigma (fun (_ : A) => B)

crypto_topos def pair_obj {A B : Type} (a : A) (b : B) : Prod_obj A B :=
  ⟨a, b⟩

crypto_topos def fst_obj {A B : Type} (p : Prod_obj A B) : A :=
  p.1

crypto_topos def snd_obj {A B : Type} (p : Prod_obj A B) : B :=
  p.2

crypto_topos def IsSet (A : Type) : Type :=
  (x y : A) → (p q : CryptoIdentity x y) → CryptoIdentity p q

crypto_topos def pempty_is_set : IsSet Empty_obj :=
  fun (x y : Empty_obj) (p q : CryptoIdentity x y) =>
    @Empty_rec (CryptoIdentity p q) x

crypto_topos axiom prod_is_set : {A B : Type} → IsSet A → IsSet B → IsSet (Prod_obj A B)

crypto_topos #print CryptoIdentity
crypto_topos #print IsSet
crypto_topos #print pempty_is_set
crypto_topos #print prod_is_set

crypto_topos axiom Category : Type → Type 1

crypto_topos axiom Cat_Hom : {P : Type} → Category P → P → P → Type
crypto_topos axiom Cat_hom_is_set : {P : Type} → (C : Category P) → (X Y : P) → IsSet (Cat_Hom C X Y)
crypto_topos axiom Cat_id : {P : Type} → (C : Category P) → (X : P) → Cat_Hom C X X
crypto_topos axiom Cat_comp : {P : Type} → (C : Category P) → {X Y Z : P} → Cat_Hom C X Y → Cat_Hom C Y Z → Cat_Hom C X Z
crypto_topos axiom Cat_id_comp : {P : Type} → (C : Category P) → {X Y : P} → (f : Cat_Hom C X Y) → CryptoIdentity (Cat_comp C (Cat_id C X) f) f
crypto_topos axiom Cat_comp_id : {P : Type} → (C : Category P) → {X Y : P} → (f : Cat_Hom C X Y) → CryptoIdentity (Cat_comp C f (Cat_id C Y)) f
crypto_topos axiom Cat_assoc : {P : Type} → (C : Category P) → {W X Y Z : P} → (f : Cat_Hom C W X) → (g : Cat_Hom C X Y) → (h : Cat_Hom C Y Z) → CryptoIdentity (Cat_comp C (Cat_comp C f g) h) (Cat_comp C f (Cat_comp C g h))

crypto_topos axiom Presheaf : (P : Type) → Category P → Type 1

crypto_topos axiom Psh_obj : {P : Type} → {C : Category P} → Presheaf P C → P → Type
crypto_topos axiom Psh_is_set : {P : Type} → {C : Category P} → (F : Presheaf P C) → (X : P) → IsSet (Psh_obj F X)
crypto_topos axiom Psh_map : {P : Type} → {C : Category P} → (F : Presheaf P C) → {X Y : P} → Cat_Hom C X Y → Psh_obj F Y → Psh_obj F X
crypto_topos axiom Psh_map_id : {P : Type} → {C : Category P} → (F : Presheaf P C) → (X : P) → (x : Psh_obj F X) → CryptoIdentity (Psh_map F (Cat_id C X) x) x
crypto_topos axiom Psh_map_comp : {P : Type} → {C : Category P} → (F : Presheaf P C) → {X Y Z : P} → (f : Cat_Hom C X Y) → (g : Cat_Hom C Y Z) → (x : Psh_obj F Z) → CryptoIdentity (Psh_map F (Cat_comp C f g) x) (Psh_map F f (Psh_map F g x))

crypto_topos axiom NatTrans : {P : Type} → {C : Category P} → (A B : Presheaf P C) → Type

crypto_topos axiom NT_app : {P : Type} → {C : Category P} → {A B : Presheaf P C} → NatTrans A B → (X : P) → Psh_obj A X → Psh_obj B X
crypto_topos axiom NT_nat : {P : Type} → {C : Category P} → {A B : Presheaf P C} → (F : NatTrans A B) → {X Y : P} → (f : Cat_Hom C X Y) → (x : Psh_obj A Y) → CryptoIdentity (Psh_map B f (NT_app F Y x)) (NT_app F X (Psh_map A f x))
crypto_topos axiom NT_ext : {P : Type} → {C : Category P} → {A B : Presheaf P C} → {f g : NatTrans A B} → ((X : P) → (x : Psh_obj A X) → CryptoIdentity (NT_app f X x) (NT_app g X x)) → CryptoIdentity f g

crypto_topos axiom NT_id : {P : Type} → {C : Category P} → (A : Presheaf P C) → NatTrans A A
crypto_topos axiom NT_id_app : {P : Type} → {C : Category P} → (A : Presheaf P C) → (X : P) → (x : Psh_obj A X) → CryptoIdentity (NT_app (NT_id A) X x) x

crypto_topos axiom NT_comp : {P : Type} → {C : Category P} → {A B D : Presheaf P C} → NatTrans A B → NatTrans B D → NatTrans A D
crypto_topos axiom NT_comp_app : {P : Type} → {C : Category P} → {A B D : Presheaf P C} → (f : NatTrans A B) → (g : NatTrans B D) → (X : P) → (x : Psh_obj A X) → CryptoIdentity (NT_app (NT_comp f g) X x) (NT_app g X (NT_app f X x))

crypto_topos axiom NT_id_comp : {P : Type} → {C : Category P} → {A B : Presheaf P C} → (f : NatTrans A B) → CryptoIdentity (NT_comp (NT_id A) f) f
crypto_topos axiom NT_comp_id : {P : Type} → {C : Category P} → {A B : Presheaf P C} → (f : NatTrans A B) → CryptoIdentity (NT_comp f (NT_id B)) f
crypto_topos axiom NT_assoc : {P : Type} → {C : Category P} → {A B D E : Presheaf P C} → (f : NatTrans A B) → (g : NatTrans B D) → (h : NatTrans D E) → CryptoIdentity (NT_comp (NT_comp f g) h) (NT_comp f (NT_comp g h))

crypto_topos axiom PresheafIso : {P : Type} → {C : Category P} → (A B : Presheaf P C) → Type

crypto_topos axiom Iso_hom : {P : Type} → {C : Category P} → {A B : Presheaf P C} → PresheafIso A B → NatTrans A B
crypto_topos axiom Iso_inv : {P : Type} → {C : Category P} → {A B : Presheaf P C} → PresheafIso A B → NatTrans B A
crypto_topos axiom Iso_hom_inv_id : {P : Type} → {C : Category P} → {A B : Presheaf P C} → (I : PresheafIso A B) → CryptoIdentity (NT_comp (Iso_hom I) (Iso_inv I)) (NT_id A)
crypto_topos axiom Iso_inv_hom_id : {P : Type} → {C : Category P} → {A B : Presheaf P C} → (I : PresheafIso A B) → CryptoIdentity (NT_comp (Iso_inv I) (Iso_hom I)) (NT_id B)

crypto_topos axiom Iso_symm : {P : Type} → {C : Category P} → {A B : Presheaf P C} → PresheafIso A B → PresheafIso B A
crypto_topos axiom Iso_trans : {P : Type} → {C : Category P} → {A B D : Presheaf P C} → PresheafIso A B → PresheafIso B D → PresheafIso A D

crypto_topos axiom yObj : {P : Type} → (C : Category P) → P → Presheaf P C

crypto_topos axiom yObj_obj_fwd : {P : Type} → (C : Category P) → (P_obj Q : P) →
  Psh_obj (yObj C P_obj) Q → Cat_Hom C Q P_obj

crypto_topos axiom yObj_obj_rev : {P : Type} → (C : Category P) → (P_obj Q : P) →
  Cat_Hom C Q P_obj → Psh_obj (yObj C P_obj) Q

crypto_topos #print Category
crypto_topos #print Presheaf
crypto_topos #print NatTrans
crypto_topos #print NT_comp
crypto_topos #print yObj

crypto_topos def IsMonomorphism {P : Type} {C : Category P} {A B : Presheaf P C} (f : NatTrans A B) : Type 1 :=
  {D : Presheaf P C} → (g h : NatTrans D A) → CryptoIdentity (NT_comp g f) (NT_comp h f) → CryptoIdentity g h

crypto_topos axiom pzero : {P : Type} → (C : Category P) → Presheaf P C

crypto_topos def IsInitial {P : Type} {C : Category P} (I : Presheaf P C) : Type 1 :=
  @Sigma.{1, 1} ((X : Presheaf P C) → NatTrans I X) (fun to =>
    (X : Presheaf P C) → (f : NatTrans I X) → CryptoIdentity f (to X)
  )

crypto_topos def IsEpimorphism {P : Type} {C : Category P} {A B : Presheaf P C} (f : NatTrans A B) : Type 1 :=
  @Sigma.{1, 0} ({D : Presheaf P C} → (g h : NatTrans B D) → CryptoIdentity (NT_comp f g) (NT_comp f h) → CryptoIdentity g h) (fun _ =>
    (P_obj : P) → (b : Psh_obj B P_obj) → @Sigma.{0, 0} (Psh_obj A P_obj) (fun a =>
      CryptoIdentity (NT_app f P_obj a) b
    )
  )

crypto_topos axiom yonedaElemToMorphism : {P : Type} → {C : Category P} → {P_obj : P} → {A : Presheaf P C} → (a : Psh_obj A P_obj) → NatTrans (yObj C P_obj) A

crypto_topos def IsRepresentable {P : Type} {C : Category P} (X : Presheaf P C) : Type :=
  @Sigma.{0, 0} P (fun P_obj => PresheafIso X (yObj C P_obj))

crypto_topos def IsAssembly {P : Type} {C : Category P} (X : Presheaf P C) : Type 1 :=
  @Sigma.{0, 1} P (fun P_obj =>
    @Sigma.{0, 1} P (fun Q_obj =>
      @Sigma.{0, 1} (NatTrans (yObj C P_obj) (yObj C Q_obj)) (fun f =>
        @Sigma.{0, 1} (NatTrans (yObj C P_obj) X) (fun e =>
          @Sigma.{0, 1} (NatTrans X (yObj C Q_obj)) (fun m =>
            @Sigma.{0, 1} (CryptoIdentity f (NT_comp e m)) (fun _ =>
              @Sigma.{1, 1} (IsEpimorphism e) (fun _ =>
                IsMonomorphism m
              )
            )
          )
        )
      )
    )
  )

crypto_topos axiom presheafProd : {P : Type} → (C : Category P) → (A B : Presheaf P C) → Presheaf P C
crypto_topos axiom presheafLift : {P : Type} → (C : Category P) → (T A B : Presheaf P C) → NatTrans T A → NatTrans T B → NatTrans T (presheafProd C A B)

crypto_topos def IsInternalEquivalenceRelation {P : Type} {C : Category P} {A E : Presheaf P C} (q1 q2 : NatTrans E A) : Type 1 :=
  @Sigma.{1, 1} (IsMonomorphism (presheafLift C E A A q1 q2)) (fun _ =>
    @Sigma.{0, 1} ((r : NatTrans A E) → Prod_obj (CryptoIdentity (NT_comp r q1) (NT_id A)) (CryptoIdentity (NT_comp r q2) (NT_id A))) (fun _ =>
      @Sigma.{0, 1} ((s : NatTrans E E) → Prod_obj (CryptoIdentity (NT_comp s q1) q2) (CryptoIdentity (NT_comp s q2) q1)) (fun _ =>
        (T : Presheaf P C) → (x y z : NatTrans T A) → (e1 e2 : NatTrans T E) →
          Prod_obj (CryptoIdentity (NT_comp e1 q1) x) (
          Prod_obj (CryptoIdentity (NT_comp e1 q2) y) (
          Prod_obj (CryptoIdentity (NT_comp e2 q1) y) (
          CryptoIdentity (NT_comp e2 q2) z))) →
            @Sigma.{0, 0} (NatTrans T E) (fun e3 =>
              Prod_obj (CryptoIdentity (NT_comp e3 q1) x) (CryptoIdentity (NT_comp e3 q2) z)
            )
      )
    )
  )

crypto_topos def IsCoequalizer {P : Type} {C : Category P} {A B C_presheaf : Presheaf P C} (f g : NatTrans A B) (p : NatTrans B C_presheaf) : Type 1 :=
  @Sigma.{0, 1} (CryptoIdentity (NT_comp f p) (NT_comp g p)) (fun _ =>
    (D : Presheaf P C) → (h : NatTrans B D) → CryptoIdentity (NT_comp f h) (NT_comp g h) →
      @Sigma.{0, 0} (NatTrans C_presheaf D) (fun k =>
        Prod_obj (CryptoIdentity (NT_comp p k) h) ((k' : NatTrans C_presheaf D) → CryptoIdentity (NT_comp p k') h → CryptoIdentity k' k)
      )
  )

crypto_topos def IsEffObject {P : Type} {C : Category P} (X : Presheaf P C) : Type 1 :=
  @Sigma.{1, 1} (Presheaf P C) (fun A =>
    @Sigma.{1, 1} (Presheaf P C) (fun E =>
      @Sigma.{0, 1} (NatTrans E A) (fun q1 =>
        @Sigma.{0, 1} (NatTrans E A) (fun q2 =>
          @Sigma.{0, 1} (NatTrans A X) (fun p =>
            @Sigma.{1, 1} (IsAssembly A) (fun _ =>
              @Sigma.{1, 1} (IsAssembly E) (fun _ =>
                @Sigma.{1, 1} (IsInternalEquivalenceRelation q1 q2) (fun _ =>
                  IsCoequalizer q1 q2 p
                )
              )
            )
          )
        )
      )
    )
  )

crypto_topos axiom rep_is_asm : {P : Type} → {C : Category P} → (X : Presheaf P C) → IsRepresentable X → IsAssembly X
crypto_topos axiom asm_is_eff : {P : Type} → {C : Category P} → (X : Presheaf P C) → IsAssembly X → IsEffObject X

crypto_topos #print IsMonomorphism
crypto_topos #print IsAssembly
crypto_topos #print IsInternalEquivalenceRelation
crypto_topos #print IsEffObject

crypto_topos axiom IsPullbackSquare : {P : Type} → {C : Category P} → {K Y X K' : Presheaf P C} → NatTrans K' K → NatTrans K' Y → NatTrans K X → NatTrans Y X → Type 1

crypto_topos axiom IsCompactObject : {P : Type} → {C : Category P} → Presheaf P C → Type 1

crypto_topos def IsCompactMorphism {P : Type} {C : Category P} {Y X : Presheaf P C} (f : NatTrans Y X) : Type 1 :=
  (K : Presheaf P C) → IsCompactObject K → (g : NatTrans K X) →
  (K' : Presheaf P C) → (fst : NatTrans K' K) → (snd : NatTrans K' Y) →
  IsPullbackSquare fst snd g f → IsCompactObject K'

crypto_topos axiom IsCoherentObject : {P : Type} → {C : Category P} → Presheaf P C → Type 1

crypto_topos axiom InternalGroupoid : {P : Type} → Category P → Type 1

crypto_topos axiom IG_G0 : {P : Type} → {C : Category P} → InternalGroupoid C → Presheaf P C
crypto_topos axiom IG_G1 : {P : Type} → {C : Category P} → InternalGroupoid C → Presheaf P C
crypto_topos axiom IG_dom : {P : Type} → {C : Category P} → (G : InternalGroupoid C) → NatTrans (IG_G1 G) (IG_G0 G)
crypto_topos axiom IG_cod : {P : Type} → {C : Category P} → (G : InternalGroupoid C) → NatTrans (IG_G1 G) (IG_G0 G)
crypto_topos axiom IG_id_map : {P : Type} → {C : Category P} → (G : InternalGroupoid C) → NatTrans (IG_G0 G) (IG_G1 G)

crypto_topos axiom GroupoidMorphism : {P : Type} → {C : Category P} → InternalGroupoid C → InternalGroupoid C → Type 1
crypto_topos axiom GM_f0 : {P : Type} → {C : Category P} → (G H : InternalGroupoid C) → GroupoidMorphism G H → NatTrans (IG_G0 G) (IG_G0 H)
crypto_topos axiom GM_f1 : {P : Type} → {C : Category P} → (G H : InternalGroupoid C) → GroupoidMorphism G H → NatTrans (IG_G1 G) (IG_G1 H)

crypto_topos axiom GroupoidProduct : {P : Type} → {C : Category P} → InternalGroupoid C → InternalGroupoid C → Type 1
crypto_topos axiom GP_prod : {P : Type} → {C : Category P} → {G H : InternalGroupoid C} → GroupoidProduct G H → InternalGroupoid C

crypto_topos def GroupoidDiagonal {P : Type} {C : Category P} (G : InternalGroupoid C) (GxG : GroupoidProduct G G) : Type 1 :=
  GroupoidMorphism G (GP_prod GxG)

crypto_topos axiom GD_diag : {P : Type} → {C : Category P} → {G : InternalGroupoid C} → {GxG : GroupoidProduct G G} → GroupoidDiagonal G GxG → GroupoidMorphism G (GP_prod GxG)

crypto_topos def GroupoidSecondDiagonal {P : Type} {C : Category P} (G : InternalGroupoid C) (GxG : GroupoidProduct G G) (Diag : GroupoidDiagonal G GxG) : Type :=
  NatTrans (IG_G0 G) (IG_G0 (GP_prod GxG))

crypto_topos axiom IsPseudoCompact : {P : Type} → {C : Category P} → InternalGroupoid C → Type 1
crypto_topos axiom IsCoherentGroupoid : {P : Type} → {C : Category P} → (G : InternalGroupoid C) → (GxG : GroupoidProduct G G) → (Diag : GroupoidDiagonal G GxG) → GroupoidSecondDiagonal G GxG Diag → Type 1
crypto_topos axiom IsWeakEquivalence : {P : Type} → {C : Category P} → {G H : InternalGroupoid C} → GroupoidMorphism G H → Type 1

crypto_topos def IsCofibration {P : Type} {C : Category P} {G H : InternalGroupoid C} (f : GroupoidMorphism G H) : Type 1 :=
  IsMonomorphism (GM_f0 G H f)

crypto_topos axiom IsFibrantGroupoid : {P : Type} → {C : Category P} → InternalGroupoid C → Type 1

crypto_topos def IsHomotopyMonomorphism {P : Type} {C : Category P} {G H : InternalGroupoid C} (f : GroupoidMorphism G H) : Type :=
  Unit_obj

crypto_topos axiom IsZeroType : {P : Type} → {C : Category P} → (G : InternalGroupoid C) → (GxG : GroupoidProduct G G) → GroupoidDiagonal G GxG → Type 1

crypto_topos axiom Theorem_CohZeroType_Eq_CohObject : {P : Type} → {C : Category P} → Type 1

crypto_topos axiom CryptoContext : (P : Type) → (C : Category P) → @Theorem_CohZeroType_Eq_CohObject P C → Type 1

crypto_topos axiom Ctx_M : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → CryptoContext P C trunc → Presheaf P C
crypto_topos axiom Ctx_S : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → CryptoContext P C trunc → Presheaf P C
crypto_topos axiom Ctx_R : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → CryptoContext P C trunc → Presheaf P C
crypto_topos axiom Ctx_G_0 : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → CryptoContext P C trunc → Presheaf P C

crypto_topos axiom PathSpace_P_presheaf : {P : Type} → {C : Category P} → {X M : Presheaf P C} → Type
crypto_topos axiom PathSpace_eps0 : {P : Type} → {C : Category P} → {X M : Presheaf P C} → PathSpace_P_presheaf (X := X) (M := M) → NatTrans X M
crypto_topos axiom PathSpace_eps1 : {P : Type} → {C : Category P} → {X M : Presheaf P C} → PathSpace_P_presheaf (X := X) (M := M) → NatTrans X M

crypto_topos axiom Ctx_q_map : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → NatTrans X (Ctx_G_0 ctx) → NatTrans X (Ctx_M ctx)
crypto_topos axiom Ctx_Phi : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → NatTrans X (Ctx_M ctx) → NatTrans X (Ctx_S ctx) → NatTrans X (Ctx_G_0 ctx)
crypto_topos axiom Ctx_Phi_inv : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → NatTrans X (Ctx_G_0 ctx) → NatTrans X (Ctx_S ctx) → NatTrans X (Ctx_M ctx)

crypto_topos axiom Ctx_f_r : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → NatTrans X (Ctx_R ctx) → NatTrans X (Ctx_G_0 ctx) → NatTrans X (Ctx_G_0 ctx)
crypto_topos axiom Ctx_f_r_inv : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → NatTrans X (Ctx_R ctx) → NatTrans X (Ctx_G_0 ctx) → NatTrans X (Ctx_G_0 ctx)

crypto_topos axiom Ctx_e_r : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → (r : NatTrans X (Ctx_R ctx)) → (x : NatTrans X (Ctx_G_0 ctx)) → CryptoIdentity (Ctx_f_r_inv ctx r (Ctx_f_r ctx r x)) x

crypto_topos axiom sec_path : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → PathSpace_P_presheaf (X := X) (M := Ctx_M ctx)
crypto_topos axiom sec_path_eps0 : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → CryptoIdentity (PathSpace_eps0 (sec_path ctx n s)) (Ctx_Phi_inv ctx (Ctx_Phi ctx n s) s)
crypto_topos axiom sec_path_eps1 : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → {X : Presheaf P C} → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → CryptoIdentity (PathSpace_eps1 (sec_path ctx n s)) n

crypto_topos axiom Cipher : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) → NatTrans X (Ctx_G_0 ctx)

crypto_topos axiom Decipher : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (p_cipher : NatTrans X (Ctx_G_0 ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) → NatTrans X (Ctx_M ctx)

crypto_topos axiom Cipher_eq : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) →
  CryptoIdentity (@Cipher P C trunc ctx X n s r) (@Ctx_f_r P C trunc ctx X r (@Ctx_Phi P C trunc ctx X n s))

crypto_topos axiom Decipher_eq : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (p_cipher : NatTrans X (Ctx_G_0 ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) →
  CryptoIdentity (@Decipher P C trunc ctx X p_cipher s r) (@Ctx_Phi_inv P C trunc ctx X (@Ctx_f_r_inv P C trunc ctx X r p_cipher) s)

crypto_topos axiom Theorem_Correctness_Path : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) → PathSpace_P_presheaf (X := X) (M := Ctx_M ctx)

crypto_topos axiom Theorem_Correctness_Path_eq : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) →
  CryptoIdentity (@Theorem_Correctness_Path P C trunc ctx X n s r) (@sec_path P C trunc ctx X n s)

crypto_topos axiom Theorem_Correctness_Path_eps0 : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) →
  CryptoIdentity (@PathSpace_eps0 P C X (Ctx_M ctx) (@Theorem_Correctness_Path P C trunc ctx X n s r)) (@Decipher P C trunc ctx X (@Cipher P C trunc ctx X n s r) s r)

crypto_topos axiom Theorem_Correctness_Path_eps1 : {P : Type} → {C : Category P} → {trunc : @Theorem_CohZeroType_Eq_CohObject P C} → (ctx : CryptoContext P C trunc) → (X : Presheaf P C) → (n : NatTrans X (Ctx_M ctx)) → (s : NatTrans X (Ctx_S ctx)) → (r : NatTrans X (Ctx_R ctx)) →
  CryptoIdentity (@PathSpace_eps1 P C X (Ctx_M ctx) (@Theorem_Correctness_Path P C trunc ctx X n s r)) n

crypto_topos #print Cipher
crypto_topos #print Decipher
crypto_topos #print Theorem_Correctness_Path_eps0

crypto_topos #print InternalGroupoid
crypto_topos #print Theorem_CohZeroType_Eq_CohObject
crypto_topos #print CryptoContext
