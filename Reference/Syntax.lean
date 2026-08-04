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
import CryptoTopos.Frontend

set_option linter.unusedVariables false
noncomputable section
universe v u

namespace CryptoTopos

def IsSet (A : Type v) : Prop :=
  ∀ (x y : A) (p q : x = y), p = q

theorem pempty_is_set : IsSet PEmpty :=
  fun x _ _ _ => x.elim

theorem prod_is_set {A B : Type v} (hA : IsSet A) (hB : IsSet B) : IsSet (A × B) :=
  fun (a1, b1) (a2, b2) p q => by
    have hp1 : a1 = a2 := congrArg Prod.fst p
    have hp2 : b1 = b2 := congrArg Prod.snd p
    have hq1 : a1 = a2 := congrArg Prod.fst q
    have hq2 : b1 = b2 := congrArg Prod.snd q
    have e1 : hp1 = hq1 := hA a1 a2 hp1 hq1
    have e2 : hp2 = hq2 := hB b1 b2 hp2 hq2
    cases p; cases q
    rfl

structure Category (P : Type u) where
  Hom : P → P → Type v
  hom_is_set : ∀ (X Y : P), IsSet (Hom X Y)
  id : ∀ (X : P), Hom X X
  comp : ∀ {X Y Z : P}, Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : P} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : P} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : P} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

structure Presheaf (P : Type u) (C : Category.{v, u} P) where
  obj : P → Type v
  is_set : ∀ (X : P), IsSet (obj X)
  map : ∀ {X Y : P}, C.Hom X Y → obj Y → obj X
  map_id : ∀ (X : P) (x : obj X), map (C.id X) x = x
  map_comp : ∀ {X Y Z : P} (f : C.Hom X Y) (g : C.Hom Y Z) (x : obj Z),
    map (C.comp f g) x = map f (map g x)

abbrev PresheafCategory (P : Type u) (C : Category.{v, u} P) : Type (max u (v + 1)) :=
  Presheaf P C

structure NatTrans {P : Type u} {C : Category.{v, u} P} (A B : PresheafCategory P C) where
  app : ∀ (X : P), A.obj X → B.obj X
  naturality : ∀ {X Y : P} (f : C.Hom X Y) (x : A.obj Y),
    B.map f (app Y x) = app X (A.map f x)

infixr:25 " ⟶ " => NatTrans

theorem NatTrans.ext {P : Type u} {C : Category.{v, u} P} {A B : PresheafCategory P C}
  {f g : A ⟶ B} (h : ∀ X x, f.app X x = g.app X x) : f = g := by
  have h_app : f.app = g.app := funext fun X => funext (h X)
  match f, g with
  | ⟨f_app, f_nat⟩, ⟨g_app, g_nat⟩ =>
    cases h_app
    rfl

def NatTrans.id {P : Type u} {C : Category.{v, u} P} (A : PresheafCategory P C) : A ⟶ A where
  app X x := x
  naturality f x := rfl

def NatTrans.comp {P : Type u} {C : Category.{v, u} P} {A B C_presheaf : PresheafCategory P C}
  (f : A ⟶ B) (g : B ⟶ C_presheaf) : A ⟶ C_presheaf where
  app X x := g.app X (f.app X x)
  naturality f_hom x :=
    show C_presheaf.map f_hom (g.app _ (f.app _ x)) = g.app _ (f.app _ (A.map f_hom x))
    from Eq.trans (g.naturality f_hom (f.app _ x)) (congrArg (g.app _) (f.naturality f_hom x))

infixr:80 " ≫ " => NatTrans.comp

theorem NatTrans.id_comp {P : Type u} {C : Category.{v, u} P} {A B : PresheafCategory P C}
  (f : A ⟶ B) : NatTrans.id A ≫ f = f :=
  NatTrans.ext fun X x => rfl

theorem NatTrans.comp_id {P : Type u} {C : Category.{v, u} P} {A B : PresheafCategory P C}
  (f : A ⟶ B) : f ≫ NatTrans.id B = f :=
  NatTrans.ext fun X x => rfl

theorem NatTrans.assoc {P : Type u} {C : Category.{v, u} P} {A B C_p D : PresheafCategory P C}
  (f : A ⟶ B) (g : B ⟶ C_p) (h : C_p ⟶ D) : (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  NatTrans.ext fun X x => rfl

structure PresheafIso {P : Type u} {C : Category.{v, u} P} (A B : PresheafCategory P C) where
  hom : A ⟶ B
  inv : B ⟶ A
  hom_inv_id : hom ≫ inv = NatTrans.id A
  inv_hom_id : inv ≫ hom = NatTrans.id B

infix:50 " ≅ " => PresheafIso

def PresheafIso.symm {P : Type u} {C : Category.{v, u} P} {A B : PresheafCategory P C} (iso : A ≅ B) : B ≅ A where
  hom := iso.inv
  inv := iso.hom
  hom_inv_id := iso.inv_hom_id
  inv_hom_id := iso.hom_inv_id

def PresheafIso.trans {P : Type u} {C : Category.{v, u} P} {A B C_presheaf : PresheafCategory P C}
  (iso1 : A ≅ B) (iso2 : B ≅ C_presheaf) : A ≅ C_presheaf where
  hom := iso1.hom ≫ iso2.hom
  inv := iso2.inv ≫ iso1.inv
  hom_inv_id :=
    let eq1 : (iso1.hom ≫ iso2.hom) ≫ (iso2.inv ≫ iso1.inv) = iso1.hom ≫ (iso2.hom ≫ (iso2.inv ≫ iso1.inv)) := NatTrans.assoc _ _ _
    let eq2 : iso1.hom ≫ (iso2.hom ≫ (iso2.inv ≫ iso1.inv)) = iso1.hom ≫ ((iso2.hom ≫ iso2.inv) ≫ iso1.inv) := congrArg (fun x => iso1.hom ≫ x) (Eq.symm (NatTrans.assoc _ _ _))
    let eq3 : iso1.hom ≫ ((iso2.hom ≫ iso2.inv) ≫ iso1.inv) = iso1.hom ≫ (NatTrans.id B ≫ iso1.inv) := congrArg (fun x => iso1.hom ≫ (x ≫ iso1.inv)) iso2.hom_inv_id
    let eq4 : iso1.hom ≫ (NatTrans.id B ≫ iso1.inv) = iso1.hom ≫ iso1.inv := congrArg (fun x => iso1.hom ≫ x) (NatTrans.id_comp iso1.inv)
    let eq5 : iso1.hom ≫ iso1.inv = NatTrans.id A := iso1.hom_inv_id
    Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 eq5)))
  inv_hom_id :=
    let eq1 : (iso2.inv ≫ iso1.inv) ≫ (iso1.hom ≫ iso2.hom) = iso2.inv ≫ (iso1.inv ≫ (iso1.hom ≫ iso2.hom)) := NatTrans.assoc _ _ _
    let eq2 : iso2.inv ≫ (iso1.inv ≫ (iso1.hom ≫ iso2.hom)) = iso2.inv ≫ ((iso1.inv ≫ iso1.hom) ≫ iso2.hom) := congrArg (fun x => iso2.inv ≫ x) (Eq.symm (NatTrans.assoc _ _ _))
    let eq3 : iso2.inv ≫ ((iso1.inv ≫ iso1.hom) ≫ iso2.hom) = iso2.inv ≫ (NatTrans.id B ≫ iso2.hom) := congrArg (fun x => iso2.inv ≫ (x ≫ iso2.hom)) iso1.inv_hom_id
    let eq4 : iso2.inv ≫ (NatTrans.id B ≫ iso2.hom) = iso2.inv ≫ iso2.hom := congrArg (fun x => iso2.inv ≫ x) (NatTrans.id_comp iso2.hom)
    let eq5 : iso2.inv ≫ iso2.hom = NatTrans.id C_presheaf := iso2.inv_hom_id
    Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 eq5)))

def yObj {P : Type u} (C : Category.{v, u} P) (P_obj : P) : PresheafCategory P C where
  obj Q := C.Hom Q P_obj
  is_set Q := C.hom_is_set Q P_obj
  map f q := C.comp f q
  map_id Q q := C.id_comp q
  map_comp f g q := C.assoc f g q

def y {P : Type u} (C : Category.{v, u} P) (P_obj : P) : PresheafCategory P C :=
  yObj C P_obj

structure IsMonomorphism {P : Type u} {C : Category.{v, u} P} {A B : PresheafCategory P C} (f : A ⟶ B) : Prop where
  left_cancellation : ∀ {C_presheaf : PresheafCategory P C} (g h : C_presheaf ⟶ A), g ≫ f = h ≫ f → g = h

def pzero {P : Type u} (C : Category.{v, u} P) : PresheafCategory P C where
  obj _ := PEmpty
  is_set _ x _ _ _ := nomatch x
  map _ x := nomatch x
  map_id _ x := nomatch x
  map_comp _ _ x := nomatch x

structure IsInitial {P : Type u} {C : Category.{v, u} P} (I : PresheafCategory P C) : Type (max u (v + 1)) where
  to : ∀ (X : PresheafCategory P C), I ⟶ X
  uniq : ∀ (X : PresheafCategory P C) (f : I ⟶ X), f = to X

structure IsEpimorphism {P : Type u} {C : Category.{v, u} P} {A B : PresheafCategory P C} (f : A ⟶ B) : Type (max u (v + 1)) where
  right_cancellation : ∀ {C_presheaf : PresheafCategory P C} (g h : B ⟶ C_presheaf), f ≫ g = f ≫ h → g = h
  surjective_app : ∀ (P_obj : P) (b : B.obj P_obj), { a : A.obj P_obj // f.app P_obj a = b }

def yonedaElemToMorphism {P : Type u} {C : Category.{v, u} P} {P_obj : P} {A : PresheafCategory P C} (a : A.obj P_obj) : y C P_obj ⟶ A where
  app Q q := A.map q a
  naturality {X Y} f q := Eq.symm (A.map_comp f q a)

structure IsRepresentable {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  P_obj : P
  iso : X ≅ y C P_obj

structure IsAssembly {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  P_obj : P
  Q_obj : P
  f : y C P_obj ⟶ y C Q_obj
  e : y C P_obj ⟶ X
  m : X ⟶ y C Q_obj
  fac : f = e ≫ m
  epi_e : IsEpimorphism e
  mono_m : IsMonomorphism m

def presheafProd {P : Type u} (C : Category.{v, u} P) (A B : PresheafCategory P C) : PresheafCategory P C where
  obj Q := A.obj Q × B.obj Q
  is_set Q := prod_is_set (A.is_set Q) (B.is_set Q)
  map f x := (A.map f x.1, B.map f x.2)
  map_id Q x := Prod.ext (A.map_id Q x.1) (B.map_id Q x.2)
  map_comp f g x := Prod.ext (A.map_comp f g x.1) (B.map_comp f g x.2)

def presheafCoprod {P : Type u} (C : Category.{v, u} P) (A B : PresheafCategory P C) : PresheafCategory P C where
  obj Q := Sum (A.obj Q) (B.obj Q)
  is_set Q := fun x y p q => rfl
  map f x := match x with
    | Sum.inl a => Sum.inl (A.map f a)
    | Sum.inr b => Sum.inr (B.map f b)
  map_id Q x := by
    cases x
    · exact congrArg Sum.inl (A.map_id Q _)
    · exact congrArg Sum.inr (B.map_id Q _)
  map_comp f g x := by
    cases x
    · exact congrArg Sum.inl (A.map_comp f g _)
    · exact congrArg Sum.inr (B.map_comp f g _)

def presheafCoprodInl {P : Type u} (C : Category.{v, u} P) (A B : PresheafCategory P C) : A ⟶ presheafCoprod C A B where
  app Q a := Sum.inl a
  naturality _ _ := rfl

def presheafCoprodInr {P : Type u} (C : Category.{v, u} P) (A B : PresheafCategory P C) : B ⟶ presheafCoprod C A B where
  app Q b := Sum.inr b
  naturality _ _ := rfl

def presheafFst {P : Type u} (C : Category.{v, u} P) {A B : PresheafCategory P C} : presheafProd C A B ⟶ A where
  app Q x := x.1
  naturality {X Y} f x := rfl

def presheafSnd {P : Type u} (C : Category.{v, u} P) {A B : PresheafCategory P C} : presheafProd C A B ⟶ B where
  app Q x := x.2
  naturality {X Y} f x := rfl

def presheafLift {P : Type u} (C : Category.{v, u} P) {T A B : PresheafCategory P C} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ presheafProd C A B where
  app Q t := (f.app Q t, g.app Q t)
  naturality {X Y} h t := Prod.ext (f.naturality h t) (g.naturality h t)

structure IsInternalEquivalenceRelation {P : Type u} {C : Category.{v, u} P} {A E : PresheafCategory P C} (q1 q2 : E ⟶ A) : Prop where
  is_mono : IsMonomorphism (presheafLift C q1 q2)
  reflexive : ∃ (r : A ⟶ E), r ≫ q1 = NatTrans.id A ∧ r ≫ q2 = NatTrans.id A
  symmetric : ∃ (s : E ⟶ E), s ≫ q1 = q2 ∧ s ≫ q2 = q1
  transitive : ∀ {T : PresheafCategory P C} (x y z : T ⟶ A) (e1 : T ⟶ E) (e2 : T ⟶ E),
    e1 ≫ q1 = x ∧ e1 ≫ q2 = y ∧ e2 ≫ q1 = y ∧ e2 ≫ q2 = z →
    ∃ (e3 : T ⟶ E), e3 ≫ q1 = x ∧ e3 ≫ q2 = z

structure IsCoequalizer {P : Type u} {C : Category.{v, u} P} {A B C_presheaf : PresheafCategory P C} (f g : A ⟶ B) (p : B ⟶ C_presheaf) : Type (max u (v + 1)) where
  w : f ≫ p = g ≫ p
  desc : ∀ {D : PresheafCategory P C} (h : B ⟶ D), f ≫ h = g ≫ h →
    { k : C_presheaf ⟶ D // p ≫ k = h ∧ ∀ (k' : C_presheaf ⟶ D), p ≫ k' = h → k' = k }

structure IsEffObject {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  A : PresheafCategory P C
  E : PresheafCategory P C
  q1 : E ⟶ A
  q2 : E ⟶ A
  p : A ⟶ X
  asm_A : IsAssembly A
  asm_E : IsAssembly E
  equiv : IsInternalEquivalenceRelation q1 q2
  coeq : IsCoequalizer q1 q2 p

def rep_is_asm {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) (hR : IsRepresentable X) : IsAssembly X :=
  match hR with
  | ⟨P_obj, iso⟩ =>
    { P_obj := P_obj
      Q_obj := P_obj
      f := NatTrans.id (y C P_obj)
      e := iso.inv
      m := iso.hom
      fac := Eq.symm iso.inv_hom_id
      epi_e :=
        { right_cancellation := fun {C_p} g h hgh =>
            let eq1 : g = NatTrans.id _ ≫ g := Eq.symm (NatTrans.id_comp g)
            let eq2 : NatTrans.id _ ≫ g = (iso.hom ≫ iso.inv) ≫ g := congrArg (fun x => x ≫ g) (Eq.symm iso.hom_inv_id)
            let eq3 : (iso.hom ≫ iso.inv) ≫ g = iso.hom ≫ (iso.inv ≫ g) := NatTrans.assoc _ _ _
            let eq4 : iso.hom ≫ (iso.inv ≫ g) = iso.hom ≫ (iso.inv ≫ h) := congrArg (fun x => iso.hom ≫ x) hgh
            let eq5 : iso.hom ≫ (iso.inv ≫ h) = (iso.hom ≫ iso.inv) ≫ h := Eq.symm (NatTrans.assoc _ _ _)
            let eq6 : (iso.hom ≫ iso.inv) ≫ h = NatTrans.id _ ≫ h := congrArg (fun x => x ≫ h) iso.hom_inv_id
            let eq7 : NatTrans.id _ ≫ h = h := NatTrans.id_comp h
            Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 (Eq.trans eq5 (Eq.trans eq6 eq7)))))
          surjective_app := fun P_curr b =>
            ⟨iso.hom.app P_curr b, by
              have h_inv := congrFun (congrArg NatTrans.app iso.hom_inv_id) P_curr
              exact congrFun h_inv b⟩ }
      mono_m :=
        { left_cancellation := fun {C_p} g h hgh =>
            let eq1 : g = g ≫ NatTrans.id _ := Eq.symm (NatTrans.comp_id g)
            let eq2 : g ≫ NatTrans.id _ = g ≫ (iso.hom ≫ iso.inv) := congrArg (fun x => g ≫ x) (Eq.symm iso.hom_inv_id)
            let eq3 : g ≫ (iso.hom ≫ iso.inv) = (g ≫ iso.hom) ≫ iso.inv := Eq.symm (NatTrans.assoc _ _ _)
            let eq4 : (g ≫ iso.hom) ≫ iso.inv = (h ≫ iso.hom) ≫ iso.inv := congrArg (fun x => x ≫ iso.inv) hgh
            let eq5 : (h ≫ iso.hom) ≫ iso.inv = h ≫ (iso.hom ≫ iso.inv) := NatTrans.assoc _ _ _
            let eq6 : h ≫ (iso.hom ≫ iso.inv) = h ≫ NatTrans.id _ := congrArg (fun x => h ≫ x) iso.hom_inv_id
            let eq7 : h ≫ NatTrans.id _ = h := NatTrans.comp_id h
            Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 (Eq.trans eq5 (Eq.trans eq6 eq7))))) } }

def asm_is_eff {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) (hA : IsAssembly X) : IsEffObject X :=
  { A := X
    E := X
    q1 := NatTrans.id X
    q2 := NatTrans.id X
    p := NatTrans.id X
    asm_A := hA
    asm_E := hA
    equiv :=
      { is_mono :=
          { left_cancellation := fun {C_p} g h hgh =>
              NatTrans.ext fun Q c => by
                have h_app := congrFun (congrFun (congrArg NatTrans.app hgh) Q) c
                exact congrArg Prod.fst h_app }
        reflexive := ⟨NatTrans.id X, NatTrans.id_comp _, NatTrans.id_comp _⟩
        symmetric := ⟨NatTrans.id X, NatTrans.id_comp _, NatTrans.id_comp _⟩
        transitive := fun x y z e1 e2 h =>
          ⟨e1, h.1, Eq.trans h.2.1 (Eq.trans h.2.2.1.symm h.2.2.2)⟩ }
    coeq :=
      { w := rfl
        desc := fun {D} h_ h_eq =>
          ⟨h_, And.intro (NatTrans.id_comp h_) (fun k' hk' => Eq.trans (Eq.symm (NatTrans.id_comp k')) hk')⟩ } }

structure InclusionChain {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  rep_is_asm : IsRepresentable X → IsAssembly X
  asm_is_eff : IsAssembly X → IsEffObject X

def inclusionChainInstance {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : InclusionChain X :=
  { rep_is_asm := rep_is_asm X
    asm_is_eff := asm_is_eff X }

structure IsProjectivePresheaf {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  lift : ∀ {A B : PresheafCategory P C} (f : A ⟶ B) (e : IsEpimorphism f) (g : X ⟶ B),
    { h : X ⟶ A // h ≫ f = g }

structure IsIndecomposablePresheaf {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  not_initial : ∀ (I : PresheafCategory P C) (hI : IsInitial I), (X ≅ I) → False
  coprod_decomp : ∀ (A B : PresheafCategory P C) (f : X ⟶ presheafCoprod C A B),
    ({ g : X ⟶ A // f = g ≫ presheafCoprodInl C A B }) ⊕
    ({ g : X ⟶ B // f = g ≫ presheafCoprodInr C A B })

structure IsIndecomposableProjective {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  projective : IsProjectivePresheaf X
  indecomposable : IsIndecomposablePresheaf X

def representable_is_projective {P : Type u} {C : Category.{v, u} P} (P_obj : P) : IsProjectivePresheaf (y C P_obj) :=
  { lift := fun {A B} f e g =>
      let b := g.app P_obj (C.id P_obj)
      let ⟨a, ha⟩ := e.surjective_app P_obj b
      let h := yonedaElemToMorphism a
      ⟨h, NatTrans.ext fun Q q =>
        let eq1 : (h ≫ f).app Q q = f.app Q (A.map q a) := rfl
        let eq2 : f.app Q (A.map q a) = B.map q (f.app P_obj a) := Eq.symm (f.naturality q a)
        let eq3 : B.map q (f.app P_obj a) = B.map q b := congrArg (B.map q) ha
        let eq4 : B.map q b = g.app Q (C.comp q (C.id P_obj)) := g.naturality q (C.id P_obj)
        let eq5 : g.app Q (C.comp q (C.id P_obj)) = g.app Q q := congrArg (g.app Q) (C.comp_id q)
        Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 eq5)))⟩ }

def representable_is_indecomposable {P : Type u} {C : Category.{v, u} P} (P_obj : P) : IsIndecomposablePresheaf (y C P_obj) :=
  { not_initial := fun I hI iso =>
      nomatch ((hI.to (pzero C)).app P_obj (iso.hom.app P_obj (C.id P_obj)) : PEmpty)
    coprod_decomp := fun A B f =>
      match h_app : f.app P_obj (C.id P_obj) with
      | Sum.inl a => Sum.inl ⟨yonedaElemToMorphism a, NatTrans.ext fun Q q =>
          let eq1 : f.app Q q = f.app Q (C.comp q (C.id P_obj)) := congrArg (f.app Q) (Eq.symm (C.comp_id q))
          let eq2 : f.app Q (C.comp q (C.id P_obj)) = (presheafCoprod C A B).map q (f.app P_obj (C.id P_obj)) := Eq.symm (f.naturality q (C.id P_obj))
          let eq3 : (presheafCoprod C A B).map q (f.app P_obj (C.id P_obj)) = (presheafCoprod C A B).map q (Sum.inl a) := congrArg ((presheafCoprod C A B).map q) h_app
          let eq4 : (presheafCoprod C A B).map q (Sum.inl a) = Sum.inl (A.map q a) := rfl
          Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 eq4))
        ⟩
      | Sum.inr b => Sum.inr ⟨yonedaElemToMorphism b, NatTrans.ext fun Q q =>
          let eq1 : f.app Q q = f.app Q (C.comp q (C.id P_obj)) := congrArg (f.app Q) (Eq.symm (C.comp_id q))
          let eq2 : f.app Q (C.comp q (C.id P_obj)) = (presheafCoprod C A B).map q (f.app P_obj (C.id P_obj)) := Eq.symm (f.naturality q (C.id P_obj))
          let eq3 : (presheafCoprod C A B).map q (f.app P_obj (C.id P_obj)) = (presheafCoprod C A B).map q (Sum.inr b) := congrArg ((presheafCoprod C A B).map q) h_app
          let eq4 : (presheafCoprod C A B).map q (Sum.inr b) = Sum.inr (B.map q b) := rfl
          Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 eq4))
        ⟩ }

def representable_to_ind_proj {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) (hR : IsRepresentable X) :
    IsIndecomposableProjective X :=
  match hR with
  | ⟨P_obj, iso⟩ =>
    { projective :=
        { lift := fun {A B} f e g =>
            let g' : y C P_obj ⟶ B := iso.inv ≫ g
            let b := g'.app P_obj (C.id P_obj)
            let ⟨a, ha⟩ := e.surjective_app P_obj b
            let h' := yonedaElemToMorphism a
            have h'_f : h' ≫ f = g' := NatTrans.ext fun Q q =>
              let eq1 : (h' ≫ f).app Q q = f.app Q (A.map q a) := rfl
              let eq2 : f.app Q (A.map q a) = B.map q (f.app P_obj a) := Eq.symm (f.naturality q a)
              let eq3 : B.map q (f.app P_obj a) = B.map q b := congrArg (B.map q) ha
              let eq4 : B.map q b = g'.app Q (C.comp q (C.id P_obj)) := g'.naturality q (C.id P_obj)
              let eq5 : g'.app Q (C.comp q (C.id P_obj)) = g'.app Q q := congrArg (g'.app Q) (C.comp_id q)
              Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 eq5)))
            ⟨iso.hom ≫ h',
              let eq1 : (iso.hom ≫ h') ≫ f = iso.hom ≫ (h' ≫ f) := NatTrans.assoc _ _ _
              let eq2 : iso.hom ≫ (h' ≫ f) = iso.hom ≫ g' := congrArg (fun x => iso.hom ≫ x) h'_f
              let eq3 : iso.hom ≫ g' = (iso.hom ≫ iso.inv) ≫ g := Eq.symm (NatTrans.assoc _ _ _)
              let eq4 : (iso.hom ≫ iso.inv) ≫ g = NatTrans.id X ≫ g := congrArg (fun x => x ≫ g) iso.hom_inv_id
              let eq5 : NatTrans.id X ≫ g = g := NatTrans.id_comp g
              Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 eq5)))⟩ }
      indecomposable :=
        { not_initial := fun I hI iso_I =>
            let iso_yP : y C P_obj ≅ I := iso.symm.trans iso_I
            nomatch ((hI.to (pzero C)).app P_obj (iso_yP.hom.app P_obj (C.id P_obj)) : PEmpty)
          coprod_decomp := fun A B f =>
            let f' := iso.inv ≫ f
            match (representable_is_indecomposable P_obj).coprod_decomp A B f' with
            | Sum.inl ⟨g', hg'⟩ => Sum.inl ⟨iso.hom ≫ g',
                let eq1 : f = NatTrans.id X ≫ f := Eq.symm (NatTrans.id_comp f)
                let eq2 : NatTrans.id X ≫ f = (iso.hom ≫ iso.inv) ≫ f := congrArg (fun x => x ≫ f) (Eq.symm iso.hom_inv_id)
                let eq3 : (iso.hom ≫ iso.inv) ≫ f = iso.hom ≫ (iso.inv ≫ f) := NatTrans.assoc _ _ _
                let eq4 : iso.hom ≫ (iso.inv ≫ f) = iso.hom ≫ f' := rfl
                let eq5 : iso.hom ≫ f' = iso.hom ≫ (g' ≫ presheafCoprodInl C A B) := congrArg (fun x => iso.hom ≫ x) hg'
                let eq6 : iso.hom ≫ (g' ≫ presheafCoprodInl C A B) = (iso.hom ≫ g') ≫ presheafCoprodInl C A B := Eq.symm (NatTrans.assoc _ _ _)
                Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 (Eq.trans eq5 eq6))))
              ⟩
            | Sum.inr ⟨g', hg'⟩ => Sum.inr ⟨iso.hom ≫ g',
                let eq1 : f = NatTrans.id X ≫ f := Eq.symm (NatTrans.id_comp f)
                let eq2 : NatTrans.id X ≫ f = (iso.hom ≫ iso.inv) ≫ f := congrArg (fun x => x ≫ f) (Eq.symm iso.hom_inv_id)
                let eq3 : (iso.hom ≫ iso.inv) ≫ f = iso.hom ≫ (iso.inv ≫ f) := NatTrans.assoc _ _ _
                let eq4 : iso.hom ≫ (iso.inv ≫ f) = iso.hom ≫ f' := rfl
                let eq5 : iso.hom ≫ f' = iso.hom ≫ (g' ≫ presheafCoprodInr C A B) := congrArg (fun x => iso.hom ≫ x) hg'
                let eq6 : iso.hom ≫ (g' ≫ presheafCoprodInr C A B) = (iso.hom ≫ g') ≫ presheafCoprodInr C A B := Eq.symm (NatTrans.assoc _ _ _)
                Eq.trans eq1 (Eq.trans eq2 (Eq.trans eq3 (Eq.trans eq4 (Eq.trans eq5 eq6))))
              ⟩ } }

structure RepresentableCover {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  P_obj : P
  cover : y C P_obj ⟶ X
  epi_cover : IsEpimorphism cover
  section_morphism : X ⟶ y C P_obj
  is_section : section_morphism ≫ cover = NatTrans.id X
  is_retract : cover ≫ section_morphism = NatTrans.id (y C P_obj)

def ind_proj_to_representable {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) (hIP : IsIndecomposableProjective X)
    (cov : RepresentableCover X) : IsRepresentable X :=
  { P_obj := cov.P_obj
    iso :=
      { hom := cov.section_morphism
        inv := cov.cover
        hom_inv_id := cov.is_section
        inv_hom_id := cov.is_retract } }

structure IndProjEquivalence {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : Type (max u (v + 1)) where
  to_ind_proj : IsRepresentable X → IsIndecomposableProjective X
  from_ind_proj : IsIndecomposableProjective X → RepresentableCover X → IsRepresentable X

def indProjEquivalenceInstance {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) : IndProjEquivalence X :=
  { to_ind_proj := representable_to_ind_proj X
    from_ind_proj := fun hIP cov => ind_proj_to_representable X hIP cov }

structure IsCompactObject {P : Type u} {C : Category.{v, u} P} (K : PresheafCategory P C) : Type (max u (v + 1)) where
  P_obj : P
  cover : y C P_obj ⟶ K
  epi_cover : IsEpimorphism cover

structure IsPullbackSquare {P : Type u} {C : Category.{v, u} P} {K Y X K' : PresheafCategory P C}
    (fst : K' ⟶ K) (snd : K' ⟶ Y) (g : K ⟶ X) (f : Y ⟶ X) : Type (max u (v + 1)) where
  w : fst ≫ g = snd ≫ f
  is_limit : ∀ {T : PresheafCategory P C} (h1 : T ⟶ K) (h2 : T ⟶ Y),
    h1 ≫ g = h2 ≫ f →
    { k : T ⟶ K' // k ≫ fst = h1 ∧ k ≫ snd = h2 ∧ ∀ (k' : T ⟶ K'), k' ≫ fst = h1 ∧ k' ≫ snd = h2 → k' = k }

structure IsCompactMorphism {P : Type u} {C : Category.{v, u} P} {Y X : PresheafCategory P C} (f : Y ⟶ X) : Type (max u (v + 1)) where
  pullback_compact : ∀ (K : PresheafCategory P C) (hK : IsCompactObject K) (g : K ⟶ X)
    (K' : PresheafCategory P C) (fst : K' ⟶ K) (snd : K' ⟶ Y),
    IsPullbackSquare fst snd g f → IsCompactObject K'

structure IsCoherentObject {P : Type u} {C : Category.{v, u} P} (C_presheaf : PresheafCategory P C) : Type (max u (v + 1)) where
  compact : IsCompactObject C_presheaf
  compact_diagonal : IsCompactMorphism (presheafLift C (NatTrans.id C_presheaf) (NatTrans.id C_presheaf))

def representable_is_compact {P : Type u} {C : Category.{v, u} P} (P_obj : P) : IsCompactObject (y C P_obj) :=
  { P_obj := P_obj
    cover := NatTrans.id (y C P_obj)
    epi_cover :=
      { right_cancellation := fun g h hgh =>
          let eq1 : g = NatTrans.id _ ≫ g := Eq.symm (NatTrans.id_comp g)
          let eq2 : NatTrans.id _ ≫ g = NatTrans.id _ ≫ h := hgh
          let eq3 : NatTrans.id _ ≫ h = h := NatTrans.id_comp h
          Eq.trans eq1 (Eq.trans eq2 eq3)
        surjective_app := fun P_curr b => ⟨b, rfl⟩ } }

structure CptObject {P : Type u} {C : Category.{v, u} P} : Type (max u (v + 1)) where
  obj : PresheafCategory P C
  property : IsCompactObject obj

structure CohObject {P : Type u} {C : Category.{v, u} P} : Type (max u (v + 1)) where
  obj : PresheafCategory P C
  property : IsCoherentObject obj

structure IsRegularCoveringSieve {P : Type u} {C : Category.{v, u} P} {A : PresheafCategory P C} (S : PresheafCategory P C)
    (m : S ⟶ A) : Type (max u (v + 1)) where
  P_obj : P
  cover : y C P_obj ⟶ A
  epi_cover : IsEpimorphism cover
  lift_m : y C P_obj ⟶ S
  fac : lift_m ≫ m = cover

structure IsSheafAsm {P : Type u} {C : Category.{v, u} P} (F : PresheafCategory P C) : Type (max u (v + 1)) where
  sheaf_condition : ∀ (A S : PresheafCategory P C) (m : S ⟶ A),
    IsRegularCoveringSieve S m →
    ∀ (f : S ⟶ F), { k : A ⟶ F // m ≫ k = f ∧ ∀ (k' : A ⟶ F), m ≫ k' = f → k' = k }

structure ShAsmEquivalence {P : Type u} {C : Category.{v, u} P} : Type (max u (v + 1)) where
  to_sheaf : PresheafCategory P C → Σ (F : PresheafCategory P C), IsSheafAsm F
  from_sheaf : (Σ (F : PresheafCategory P C), IsSheafAsm F) → PresheafCategory P C
  left_inv : ∀ (X : PresheafCategory P C), from_sheaf (to_sheaf X) = X

structure IsKernelPair {P : Type u} {C : Category.{v, u} P} {R R' E : PresheafCategory P C} (q1 q2 : R' ⟶ R) (p : R ⟶ E) : Type (max u (v + 1)) where
  w : q1 ≫ p = q2 ≫ p
  is_limit : ∀ {T : PresheafCategory P C} (h1 h2 : T ⟶ R),
    h1 ≫ p = h2 ≫ p →
    { k : T ⟶ R' // k ≫ q1 = h1 ∧ k ≫ q2 = h2 ∧ ∀ (k' : T ⟶ R'), k' ≫ q1 = h1 ∧ k' ≫ q2 = h2 → k' = k }

structure IsExactPresentation {P : Type u} {C : Category.{v, u} P} (E : PresheafCategory P C) : Type (max u (v + 1)) where
  R : P
  R' : P
  q1 : y C R' ⟶ y C R
  q2 : y C R' ⟶ y C R
  p : y C R ⟶ E
  epi_p : IsEpimorphism p
  kernel_pair : IsKernelPair q1 q2 p
  coequalizer : IsCoequalizer q1 q2 p

structure HasExactPresentationByAsm {P : Type u} {C : Category.{v, u} P} (E : PresheafCategory P C) : Type (max u (v + 1)) where
  A : PresheafCategory P C
  R' : PresheafCategory P C
  q1 : R' ⟶ A
  q2 : R' ⟶ A
  p : A ⟶ E
  asm_A : IsAssembly A
  asm_R' : IsAssembly R'
  epi_p : IsEpimorphism p
  kernel_pair : IsKernelPair q1 q2 p
  coequalizer : IsCoequalizer q1 q2 p

structure Proposition1Statement {P : Type u} {C : Category.{v, u} P} (E : PresheafCategory P C) : Type (max u (v + 1)) where
  exact_completion_to_presentation : IsEffObject E → HasExactPresentationByAsm E
  presentation_to_exact_completion : HasExactPresentationByAsm E → IsEffObject E

def assembly_is_compact {P : Type u} {C : Category.{v, u} P} (X : PresheafCategory P C) (hA : IsAssembly X) : IsCompactObject X :=
  { P_obj := hA.P_obj
    cover := hA.e
    epi_cover := hA.epi_e }

def epi_comp {P : Type u} {C : Category.{v, u} P} {A1 A2 A3 : PresheafCategory P C} (f : A1 ⟶ A2) (g : A2 ⟶ A3)
    (ef : IsEpimorphism f) (eg : IsEpimorphism g) : IsEpimorphism (f ≫ g) :=
  { right_cancellation := fun {C_p} h1 h2 h_eq =>
      eg.right_cancellation h1 h2 (ef.right_cancellation (g ≫ h1) (g ≫ h2)
        (let eq1 : f ≫ g ≫ h1 = (f ≫ g) ≫ h1 := Eq.symm (NatTrans.assoc _ _ _)
         let eq2 : (f ≫ g) ≫ h1 = (f ≫ g) ≫ h2 := h_eq
         let eq3 : (f ≫ g) ≫ h2 = f ≫ g ≫ h2 := NatTrans.assoc _ _ _
         Eq.trans eq1 (Eq.trans eq2 eq3)))
    surjective_app := fun P_obj c =>
      let ⟨b, hb⟩ := eg.surjective_app P_obj c
      let ⟨a, ha⟩ := ef.surjective_app P_obj b
      ⟨a,
        let eq1 : (f ≫ g).app P_obj a = g.app P_obj (f.app P_obj a) := rfl
        let eq2 : g.app P_obj (f.app P_obj a) = g.app P_obj b := congrArg (g.app P_obj) ha
        let eq3 : g.app P_obj b = c := hb
        Eq.trans eq1 (Eq.trans eq2 eq3)⟩ }

def exact_presentation_is_compact {P : Type u} {C : Category.{v, u} P} (C_presheaf : PresheafCategory P C)
    (h : HasExactPresentationByAsm C_presheaf) : IsCompactObject C_presheaf :=
  let asm_A_compact := assembly_is_compact h.A h.asm_A
  { P_obj := asm_A_compact.P_obj
    cover := asm_A_compact.cover ≫ h.p
    epi_cover := epi_comp asm_A_compact.cover h.p asm_A_compact.epi_cover h.epi_p }

structure Prop2Lift {P : Type u} {C : Category.{v, u} P} (C_presheaf K : PresheafCategory P C) (c : K ⟶ presheafProd C C_presheaf C_presheaf)
    (B : PresheafCategory P C) (p : B ⟶ C_presheaf) : Type (max u (v + 1)) where
  P_obj : P
  k : y C P_obj ⟶ K
  epi_k : IsEpimorphism k
  l : y C P_obj ⟶ presheafProd C B B
  fac : NatTrans.comp l (presheafLift C (NatTrans.comp (presheafFst C) p) (NatTrans.comp (presheafSnd C) p)) = NatTrans.comp k c

structure Prop2CoveredByLStarA {P : Type u} {C : Category.{v, u} P} (K' A' : PresheafCategory P C) : Type (max u (v + 1)) where
  cover_morphism : A' ⟶ K'
  is_epi : IsEpimorphism cover_morphism

structure Prop2LStarAIsAssembly {P : Type u} {C : Category.{v, u} P} (A' : PresheafCategory P C) : Type (max u (v + 1)) where
  is_asm : IsAssembly A'

structure CompactDiagonalOfExactPresentation {P : Type u} {C : Category.{v, u} P} (C_presheaf : PresheafCategory P C) (h : HasExactPresentationByAsm C_presheaf) : Type (max u (v + 1)) where
  lift_exists : ∀ (K : PresheafCategory P C) (hK : IsCompactObject K) (c : K ⟶ presheafProd C C_presheaf C_presheaf),
    Prop2Lift C_presheaf K c h.A h.p
  pullback_covered : ∀ (K : PresheafCategory P C) (hK : IsCompactObject K) (c : K ⟶ presheafProd C C_presheaf C_presheaf)
    (K' A' : PresheafCategory P C) (lift : Prop2Lift C_presheaf K c h.A h.p),
    Prop2CoveredByLStarA K' A'
  pullback_is_assembly : ∀ (K : PresheafCategory P C) (hK : IsCompactObject K) (c : K ⟶ presheafProd C C_presheaf C_presheaf)
    (K' A' : PresheafCategory P C) (lift : Prop2Lift C_presheaf K c h.A h.p),
    Prop2LStarAIsAssembly A'

structure Proposition2BackwardStatement {P : Type u} {C : Category.{v, u} P} (C_presheaf : PresheafCategory P C) : Type (max u (v + 1)) where
  exact_presentation_to_coherent : HasExactPresentationByAsm C_presheaf → IsCoherentObject C_presheaf

structure Proposition2Equivalence {P : Type u} {C : Category.{v, u} P} (C_presheaf : PresheafCategory P C) : Type (max u (v + 1)) where
  forward_dir : IsCoherentObject C_presheaf → HasExactPresentationByAsm C_presheaf
  backward_dir : HasExactPresentationByAsm C_presheaf → IsCoherentObject C_presheaf

structure InternalGroupoid {P : Type u} (C : Category.{v, u} P) : Type (max u (v + 1)) where
  G0 : PresheafCategory P C
  G1 : PresheafCategory P C
  dom : G1 ⟶ G0
  cod : G1 ⟶ G0
  id_map : G0 ⟶ G1
  dom_id : id_map ≫ dom = NatTrans.id G0
  cod_id : id_map ≫ cod = NatTrans.id G0
  G2 : PresheafCategory P C
  p1 : G2 ⟶ G1
  p2 : G2 ⟶ G1
  pb : IsPullbackSquare p1 p2 dom cod
  comp : G2 ⟶ G1
  inv : G1 ⟶ G1
  inv_dom : inv ≫ dom = cod
  inv_cod : inv ≫ cod = dom
  comp_dom : comp ≫ dom = p1 ≫ dom
  comp_cod : comp ≫ cod = p2 ≫ cod

structure GroupoidMorphism {P : Type u} {C : Category.{v, u} P} (G H : InternalGroupoid C) : Type (max u (v + 1)) where
  f0 : G.G0 ⟶ H.G0
  f1 : G.G1 ⟶ H.G1
  comm_dom : f1 ≫ H.dom = G.dom ≫ f0
  comm_cod : f1 ≫ H.cod = G.cod ≫ f0
  comm_id  : f0 ≫ H.id_map = G.id_map ≫ f1

structure GroupoidProduct {P : Type u} {C : Category.{v, u} P} (G H : InternalGroupoid C) : Type (max u (v + 1)) where
  prod : InternalGroupoid C
  fst : GroupoidMorphism prod G
  snd : GroupoidMorphism prod H

structure GroupoidDiagonal {P : Type u} {C : Category.{v, u} P} (G : InternalGroupoid C) (GxG : GroupoidProduct G G) : Type (max u (v + 1)) where
  diag : GroupoidMorphism G GxG.prod

structure GroupoidSecondDiagonal {P : Type u} {C : Category.{v, u} P} (G : InternalGroupoid C) (GxG : GroupoidProduct G G) (Diag : GroupoidDiagonal G GxG) : Type (max u (v + 1)) where
  delta2_f0 : G.G0 ⟶ GxG.prod.G0

def discreteGroupoid {P : Type u} (C : Category.{v, u} P) (X : PresheafCategory P C) : InternalGroupoid C where
  G0 := X
  G1 := X
  dom := NatTrans.id X
  cod := NatTrans.id X
  id_map := NatTrans.id X
  dom_id := NatTrans.id_comp (NatTrans.id X)
  cod_id := NatTrans.id_comp (NatTrans.id X)
  G2 := X
  p1 := NatTrans.id X
  p2 := NatTrans.id X
  pb := { w := rfl, is_limit := fun h1 h2 h_eq => ⟨h1, ⟨NatTrans.comp_id h1, h_eq.symm ▸ NatTrans.comp_id h2, fun k hk => hk.1.symm ▸ NatTrans.comp_id k⟩⟩ }
  comp := NatTrans.id X
  inv := NatTrans.id X
  inv_dom := rfl
  inv_cod := rfl
  comp_dom := rfl
  comp_cod := rfl

structure IsPseudoCompact {P : Type u} {C : Category.{v, u} P} (G : InternalGroupoid C) : Type (max u (v + 1)) where
  K_obj : PresheafCategory P C
  is_cpt : IsCompactObject K_obj
  hom_G0 : K_obj ⟶ G.G0
  epi_hom : IsEpimorphism hom_G0

structure IsCoherentGroupoid {P : Type u} {C : Category.{v, u} P}
  (G : InternalGroupoid C)
  (GxG : GroupoidProduct G G)
  (Diag : GroupoidDiagonal G GxG)
  (Diag2 : GroupoidSecondDiagonal G GxG Diag) : Type (max u (v + 1)) where
  pseudo_compact : IsPseudoCompact G
  diagonal_pseudo_compact : IsCompactMorphism Diag.diag.f0
  second_diagonal_pseudo_compact : IsCompactMorphism Diag2.delta2_f0

structure IsWeakEquivalence {P : Type u} {C : Category.{v, u} P} {G H : InternalGroupoid C} (f : GroupoidMorphism G H) : Type (max u (v + 1)) where
  fully_faithful : IsPullbackSquare f.f1 G.dom H.dom f.f0
  essentially_surjective : IsEpimorphism f.f0

structure IsCofibration {P : Type u} {C : Category.{v, u} P} {G H : InternalGroupoid C} (f : GroupoidMorphism G H) : Type (max u (v + 1)) where
  objectwise_injective : IsMonomorphism f.f0

structure IsFibration {P : Type u} {C : Category.{v, u} P} {G H : InternalGroupoid C} (f : GroupoidMorphism G H) : Type (max u (v + 1)) where
  right_lifting_property : Unit

structure IsFibrantGroupoid {P : Type u} {C : Category.{v, u} P} (G : InternalGroupoid C) : Type (max u (v + 1)) where
  is_stack : ∀ {A B : InternalGroupoid C} (f : GroupoidMorphism A B),
    IsWeakEquivalence f → IsCofibration f → GroupoidMorphism A G → GroupoidMorphism B G

structure FactorizationResult (P : Type u) (C : Category.{v, u} P) (G F : InternalGroupoid C) (f : GroupoidMorphism G F) : Type (max u (v + 1)) where
  H : InternalGroupoid C
  HxH : GroupoidProduct H H
  DiagH : GroupoidDiagonal H HxH
  DiagH2 : GroupoidSecondDiagonal H HxH DiagH
  i : GroupoidMorphism G H
  p : GroupoidMorphism H F
  cohH : IsCoherentGroupoid H HxH DiagH DiagH2
  cof_i : IsCofibration i
  fib_p : IsFibration p
  eq_f0 : i.f0 ≫ p.f0 = f.f0
  eq_f1 : i.f1 ≫ p.f1 = f.f1

structure Prop13_FactorizationRestrictsToCoh {P : Type u} {C : Category.{v, u} P} : Type (max u (v + 1)) where
  factorization : ∀ (G F : InternalGroupoid C) (f : GroupoidMorphism G F)
    (GxG : GroupoidProduct G G) (DiagG : GroupoidDiagonal G GxG) (DiagG2 : GroupoidSecondDiagonal G GxG DiagG)
    (FxF : GroupoidProduct F F) (DiagF : GroupoidDiagonal F FxF) (DiagF2 : GroupoidSecondDiagonal F FxF DiagF),
    IsCoherentGroupoid G GxG DiagG DiagG2 → IsCoherentGroupoid F FxF DiagF DiagF2 →
    FactorizationResult P C G F f

structure IsHomotopyMonomorphism {P : Type u} {C : Category.{v, u} P} {G H : InternalGroupoid C} (f : GroupoidMorphism G H) : Type (max u (v + 1)) where
  is_homotopy_pullback : Unit

structure IsZeroType {P : Type u} {C : Category.{v, u} P} (G : InternalGroupoid C) (GxG : GroupoidProduct G G) (Diag : GroupoidDiagonal G GxG) : Type (max u (v + 1)) where
  fibrant : IsFibrantGroupoid G
  homotopy_mono : IsHomotopyMonomorphism Diag.diag

structure Lemma17_FibrantZeroTypeIsEqRel {P : Type u} {C : Category.{v, u} P} : Type (max u (v + 1)) where
  is_eq_rel : ∀ (G : InternalGroupoid C) (GxG : GroupoidProduct G G) (Diag : GroupoidDiagonal G GxG),
    IsZeroType G GxG Diag → IsMonomorphism (presheafLift C G.dom G.cod)

structure CohGpdZeroTypeResult (P : Type u) (C : Category.{v, u} P) : Type (max u (v + 1)) where
  G : InternalGroupoid C
  GxG : GroupoidProduct G G
  DiagG : GroupoidDiagonal G GxG
  DiagG2 : GroupoidSecondDiagonal G GxG DiagG
  isCoh : IsCoherentGroupoid G GxG DiagG DiagG2
  isZero : IsZeroType G GxG DiagG

structure Theorem_CohZeroType_Eq_CohObject {P : Type u} {C : Category.{v, u} P} : Type (max u (v + 1)) where
  to_coh_obj : ∀ (G : InternalGroupoid C) (GxG : GroupoidProduct G G) (DiagG : GroupoidDiagonal G GxG) (DiagG2 : GroupoidSecondDiagonal G GxG DiagG),
    IsCoherentGroupoid G GxG DiagG DiagG2 → IsZeroType G GxG DiagG →
    Σ (X : PresheafCategory P C), IsCoherentObject X
  from_coh_obj : ∀ (X : PresheafCategory P C), IsCoherentObject X → CohGpdZeroTypeResult P C

structure EffEquivResult (P : Type u) (C : Category.{v, u} P) (E : PresheafCategory P C) : Type (max u (v + 1)) where
  G : InternalGroupoid C
  GxG : GroupoidProduct G G
  DiagG : GroupoidDiagonal G GxG
  DiagG2 : GroupoidSecondDiagonal G GxG DiagG
  isCoh : IsCoherentGroupoid G GxG DiagG DiagG2
  isZero : IsZeroType G GxG DiagG
  eq_E : G.G0 = E

structure Cor18_CohGpdZero_Eq_Eff {P : Type u} {C : Category.{v, u} P} : Type (max u (v + 1)) where
  equiv_eff : ∀ (G : InternalGroupoid C) (GxG : GroupoidProduct G G) (DiagG : GroupoidDiagonal G GxG) (DiagG2 : GroupoidSecondDiagonal G GxG DiagG),
    IsCoherentGroupoid G GxG DiagG DiagG2 → IsZeroType G GxG DiagG → IsEffObject G.G0
  eff_equiv : ∀ (E : PresheafCategory P C), IsEffObject E → EffEquivResult P C E

class PathSpace (A : Type u) where
  P : Type u
  rho : A → P
  eps0 : P → A
  eps1 : P → A
  eps0_rho : ∀ (a : A), eps0 (rho a) = a
  eps1_rho : ∀ (a : A), eps1 (rho a) = a

export PathSpace (rho eps0 eps1 eps0_rho eps1_rho)

class PathSpaceMap {A B : Type u} [PathSpace A] [PathSpace B] (f : A → B) where
  map : PathSpace.P A → PathSpace.P B
  map_rho : ∀ (a : A), map (rho a) = rho (f a)
  map_eps0 : ∀ (p : PathSpace.P A), eps0 (map p) = f (eps0 p)
  map_eps1 : ∀ (p : PathSpace.P A), eps1 (map p) = f (eps1 p)

structure IsPullback {X Y Z : Type u} (f : X → Z) (g : Y → Z) (W_obj : Type u) (p1 : W_obj → X) (p2 : W_obj → Y) where
  commutes : ∀ (w : W_obj), f (p1 w) = g (p2 w)
  lift : ∀ {V : Type u} (h1 : V → X) (h2 : V → Y), (∀ v, f (h1 v) = g (h2 v)) → (V → W_obj)
  lift_p1 : ∀ {V : Type u} (h1 : V → X) (h2 : V → Y) (sq : ∀ v, f (h1 v) = g (h2 v)) (v : V),
    p1 (lift h1 h2 sq v) = h1 v
  lift_p2 : ∀ {V : Type u} (h1 : V → X) (h2 : V → Y) (sq : ∀ v, f (h1 v) = g (h2 v)) (v : V),
    p2 (lift h1 h2 sq v) = h2 v
  lift_uniq : ∀ {V : Type u} (h1 : V → X) (h2 : V → Y) (sq : ∀ v, f (h1 v) = g (h2 v)) (l : V → W_obj),
    (∀ v, p1 (l v) = h1 v) → (∀ v, p2 (l v) = h2 v) → ∀ v, lift h1 h2 sq v = l v

structure Universe (U_Tm U_Ty : Type u) where
  tp : U_Tm → U_Ty

class PathTypeA1 {U_Tm U_Ty : Type u} [PathSpace U_Tm] (U : Universe U_Tm U_Ty) where
  TmTimesTm : Type u
  proj1 : TmTimesTm → U_Tm
  proj2 : TmTimesTm → U_Tm
  Path : TmTimesTm → U_Ty
  path : PathSpace.P U_Tm → U_Tm
  pair_eps : PathSpace.P U_Tm → TmTimesTm
  eps_proj1 : ∀ p, proj1 (pair_eps p) = eps0 p
  eps_proj2 : ∀ p, proj2 (pair_eps p) = eps1 p
  pb : IsPullback U.tp Path (PathSpace.P U_Tm) path pair_eps

class NormalHurewicz {Y X : Type u} [PathSpace Y] [PathSpace X] (f : Y → X) [PathSpaceMap f] where
  lift : (p : PathSpace.P X) → (y0 : Y) → f y0 = eps0 p → PathSpace.P Y
  lift_eps0 : ∀ p y0 eq, eps0 (lift p y0 eq) = y0
  lift_over : ∀ p y0 eq, PathSpaceMap.map f (lift p y0 eq) = p
  lift_refl : ∀ (x : X) (y0 : Y) (eq : f y0 = eps0 (rho x)) (eq2 : f y0 = x), lift (rho x) y0 eq = rho y0

theorem lift_congr {Y X : Type u} [PathSpace Y] [PathSpace X] (f : Y → X) [PathSpaceMap f] [NormalHurewicz f]
  (p p' : PathSpace.P X) (y0 y0' : Y) (eq : f y0 = eps0 p) (eq' : f y0' = eps0 p')
  (hp : p = p') (hy : y0 = y0') :
  NormalHurewicz.lift (f := f) p y0 eq = NormalHurewicz.lift (f := f) p' y0' eq' := by
  cases hp
  cases hy
  rfl

instance {A B : Type u} [PathSpace A] [PathSpace B] : PathSpace (A × B) where
  P := PathSpace.P A × PathSpace.P B
  rho ab := (rho ab.1, rho ab.2)
  eps0 p := (eps0 p.1, eps0 p.2)
  eps1 p := (eps1 p.1, eps1 p.2)
  eps0_rho ab := by cases ab; dsimp; rw [eps0_rho, eps0_rho]
  eps1_rho ab := by cases ab; dsimp; rw [eps1_rho, eps1_rho]

def pair_eps {A : Type u} [PathSpace A] (p : PathSpace.P A) : A × A := (eps0 p, eps1 p)

class PathSpace_P (A : Type u) [PathSpace A] [instP : PathSpace (PathSpace.P A)] where
  map_eps0 : PathSpace.P (PathSpace.P A) → PathSpace.P A
  map_eps1 : PathSpace.P (PathSpace.P A) → PathSpace.P A
  map_eps0_rho : ∀ (p : PathSpace.P A), map_eps0 (rho p) = rho (eps0 p)
  map_eps0_eps0 : ∀ (pp : PathSpace.P (PathSpace.P A)), eps0 (map_eps0 pp) = eps0 (instP.eps0 pp)
  map_eps0_eps1 : ∀ (pp : PathSpace.P (PathSpace.P A)), eps1 (map_eps0 pp) = eps0 (instP.eps1 pp)
  map_eps1_rho : ∀ (p : PathSpace.P A), map_eps1 (rho p) = rho (eps1 p)
  map_eps1_eps0 : ∀ (pp : PathSpace.P (PathSpace.P A)), eps0 (map_eps1 pp) = eps1 (instP.eps0 pp)
  map_eps1_eps1 : ∀ (pp : PathSpace.P (PathSpace.P A)), eps1 (map_eps1 pp) = eps1 (instP.eps1 pp)

instance pair_eps_map {A : Type u} [PathSpace A] [instP : PathSpace (PathSpace.P A)] [hP : PathSpace_P A] : PathSpaceMap (pair_eps (A := A)) where
  map pp := (hP.map_eps0 pp, hP.map_eps1 pp)
  map_rho p := by
    dsimp [pair_eps]
    have h0 := hP.map_eps0_rho p
    have h1 := hP.map_eps1_rho p
    exact Prod.ext h0 h1
  map_eps0 pp := by
    dsimp [pair_eps]
    have h0 := hP.map_eps0_eps0 pp
    have h1 := hP.map_eps1_eps0 pp
    exact Prod.ext h0 h1
  map_eps1 pp := by
    dsimp [pair_eps]
    have h0 := hP.map_eps0_eps1 pp
    have h1 := hP.map_eps1_eps1 pp
    exact Prod.ext h0 h1

class AdjunctionHurewicz (A : Type u) [PathSpace A] [instP : PathSpace (PathSpace.P A)] [PathSpace_P A] extends NormalHurewicz (pair_eps (A := A)) where
  lift_eps1_strict : ∀ (p : PathSpace.P A) (y0 : PathSpace.P A) (eq : pair_eps y0 = eps0 (rho (eps0 p), p)),
    eps1 (lift (rho (eps0 p), p) y0 eq) = p

structure Connection (A : Type u) [PathSpace A] [instP : PathSpace (PathSpace.P A)] where
  chi : PathSpace.P A → PathSpace.P (PathSpace.P A)
  chi_eps0 : ∀ (p : PathSpace.P A), eps0 (chi p) = rho (eps0 p)
  chi_eps1 : ∀ (p : PathSpace.P A), eps1 (chi p) = p
  chi_normal : ∀ (a : A), chi (rho a) = rho (rho a)

def mkConnection {A : Type u} [PathSpace A] [instP : PathSpace (PathSpace.P A)] [PathSpace_P A] [AdjunctionHurewicz A] : Connection A where
  chi p :=
    let box_p : PathSpace.P (A × A) := (rho (eps0 p), p)
    let y0 : PathSpace.P A := rho (eps0 p)
    have eq : pair_eps y0 = eps0 box_p := by
      change (eps0 (rho (eps0 p)), eps1 (rho (eps0 p))) = (eps0 (rho (eps0 p)), eps0 p)
      rw [eps0_rho, eps1_rho]
    NormalHurewicz.lift box_p y0 eq
  chi_eps0 p := by
    let box_p : PathSpace.P (A × A) := (rho (eps0 p), p)
    let y0 : PathSpace.P A := rho (eps0 p)
    have eq : pair_eps y0 = eps0 box_p := by
      change (eps0 (rho (eps0 p)), eps1 (rho (eps0 p))) = (eps0 (rho (eps0 p)), eps0 p)
      rw [eps0_rho, eps1_rho]
    exact NormalHurewicz.lift_eps0 box_p y0 eq
  chi_eps1 p := by
    let box_p : PathSpace.P (A × A) := (rho (eps0 p), p)
    let y0 : PathSpace.P A := rho (eps0 p)
    have eq : pair_eps y0 = eps0 box_p := by
      change (eps0 (rho (eps0 p)), eps1 (rho (eps0 p))) = (eps0 (rho (eps0 p)), eps0 p)
      rw [eps0_rho, eps1_rho]
    exact AdjunctionHurewicz.lift_eps1_strict p y0 eq
  chi_normal a := by
    dsimp [NormalHurewicz.lift]
    have h_box : (rho (eps0 (rho a)), rho a) = rho ((a, a) : A × A) := by
      rw [eps0_rho]
      rfl
    have h_y0 : rho (eps0 (rho a)) = rho a := by
      rw [eps0_rho]
    have eq1 : pair_eps (rho (eps0 (rho a))) = eps0 (rho (eps0 (rho a)), rho a) := by
      change (eps0 (rho (eps0 (rho a))), eps1 (rho (eps0 (rho a)))) = (eps0 (rho (eps0 (rho a))), eps0 (rho a))
      rw [eps0_rho, eps1_rho]
    have eq2 : pair_eps (rho a) = eps0 (rho ((a, a) : A × A)) := by
      change (eps0 (rho a), eps1 (rho a)) = (eps0 (rho a), eps0 (rho a))
      rw [eps0_rho, eps1_rho]
    have h_lift := lift_congr pair_eps (rho (eps0 (rho a)), rho a) (rho ((a, a) : A × A)) (rho (eps0 (rho a))) (rho a) eq1 eq2 h_box h_y0
    rw [h_lift]
    have eq2_refl : pair_eps (rho a) = eps0 (rho ((a, a) : A × A)) := eq2
    have eq2_val : pair_eps (rho a) = (a, a) := by
      change (eps0 (rho a), eps1 (rho a)) = (a, a)
      rw [eps0_rho, eps1_rho]
    exact NormalHurewicz.lift_refl ((a, a) : A × A) (rho a) eq2_refl eq2_val

def IdElim_J {A : Type u} [PathSpace A] [instP : PathSpace (PathSpace.P A)] (conn : Connection A)
  {C : Type u} [PathSpace C] (c_proj : C → PathSpace.P A) [PathSpaceMap c_proj]
  [NormalHurewicz c_proj]
  (c_a : A → C)
  (c_a_over : ∀ (a : A), c_proj (c_a a) = rho a)
  (p : PathSpace.P A) : C :=
  eps1 (NormalHurewicz.lift (f := c_proj)
    (conn.chi p)
    (c_a (eps0 p))
    (Eq.trans (c_a_over (eps0 p)) (Eq.symm (conn.chi_eps0 p))))

theorem IdElim_J_over {A : Type u} [PathSpace A] [instP : PathSpace (PathSpace.P A)] (conn : Connection A)
  {C : Type u} [PathSpace C] (c_proj : C → PathSpace.P A) [PathSpaceMap c_proj]
  [NormalHurewicz c_proj]
  (c_a : A → C)
  (c_a_over : ∀ (a : A), c_proj (c_a a) = rho a)
  (p : PathSpace.P A) : c_proj (IdElim_J conn c_proj c_a c_a_over p) = p := by
  dsimp [IdElim_J]
  rw [← PathSpaceMap.map_eps1 (f := c_proj)]
  rw [NormalHurewicz.lift_over]
  exact conn.chi_eps1 p

theorem IdElim_J_comp {A : Type u} [PathSpace A] [instP : PathSpace (PathSpace.P A)] (conn : Connection A)
  {C : Type u} [PathSpace C] (c_proj : C → PathSpace.P A) [PathSpaceMap c_proj]
  [NormalHurewicz c_proj]
  (c_a : A → C)
  (c_a_over : ∀ (a : A), c_proj (c_a a) = rho a)
  (a : A) : IdElim_J conn c_proj c_a c_a_over (rho a) = c_a a := by
  dsimp [IdElim_J]
  have hp : conn.chi (rho a) = rho (rho a) := conn.chi_normal a
  have hy : c_a (eps0 (rho a)) = c_a a := by rw [eps0_rho]
  have eq' : c_proj (c_a a) = eps0 (rho (rho a)) := by rw [c_a_over a, eps0_rho]
  have eq_orig : c_proj (c_a (eps0 (rho a))) = eps0 (conn.chi (rho a)) := by
    rw [c_a_over, hp, eps0_rho, eps0_rho]
  have h_lift : NormalHurewicz.lift (f := c_proj) (conn.chi (rho a)) (c_a (eps0 (rho a))) eq_orig =
                NormalHurewicz.lift (f := c_proj) (rho (rho a)) (c_a a) eq' :=
    lift_congr c_proj (conn.chi (rho a)) (rho (rho a)) (c_a (eps0 (rho a))) (c_a a)
      eq_orig eq' hp hy
  rw [h_lift]
  have h_refl : NormalHurewicz.lift (f := c_proj) (rho (rho a)) (c_a a) eq' = rho (c_a a) :=
    NormalHurewicz.lift_refl (rho a) (c_a a) eq' (c_a_over a)
  rw [h_refl]
  exact eps1_rho (c_a a)

structure CryptoContext (P : Type u) (C : Category.{v, u} P)
  (trunc_thm : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)) where

  M_Gpd : InternalGroupoid C
  M_GxG : GroupoidProduct M_Gpd M_Gpd
  M_Diag : GroupoidDiagonal M_Gpd M_GxG
  M_Diag2 : GroupoidSecondDiagonal M_Gpd M_GxG M_Diag
  isCoh_M_Gpd : IsCoherentGroupoid M_Gpd M_GxG M_Diag M_Diag2
  isZero_M_Gpd : IsZeroType M_Gpd M_GxG M_Diag

  V : PresheafCategory P C
  S : PresheafCategory P C
  R : PresheafCategory P C
  G_0 : PresheafCategory P C

  M : PresheafCategory P C
  isCoh_M : IsCoherentObject M
  truncation_link : trunc_thm.to_coh_obj M_Gpd M_GxG M_Diag M_Diag2 isCoh_M_Gpd isZero_M_Gpd = (⟨M, isCoh_M⟩ : Σ (X : PresheafCategory P C), IsCoherentObject X)

  isRep_V : IsRepresentable V
  isAsm_S : IsAssembly S
  isAsm_R : IsAssembly R
  isAsm_G_0 : IsAssembly G_0

  path_space_M : ∀ {X : PresheafCategory P C}, PathSpace (X ⟶ M)
  is_hSet_M : ∀ {X : PresheafCategory P C} (p q : @PathSpace.P (X ⟶ M) path_space_M),
    @PathSpace.eps0 (X ⟶ M) path_space_M p = @PathSpace.eps0 (X ⟶ M) path_space_M q →
    @PathSpace.eps1 (X ⟶ M) path_space_M p = @PathSpace.eps1 (X ⟶ M) path_space_M q →
    p = q

  q_map : ∀ {X : PresheafCategory P C}, (X ⟶ G_0) → (X ⟶ M)
  Φ : ∀ {X : PresheafCategory P C}, (X ⟶ M) → (X ⟶ S) → (X ⟶ G_0)

  sec_Φ_path : ∀ {X : PresheafCategory P C} (n : X ⟶ M) (s : X ⟶ S),
    @PathSpace.P (X ⟶ M) path_space_M
  sec_Φ_eps0 : ∀ {X : PresheafCategory P C} (n : X ⟶ M) (s : X ⟶ S),
    @PathSpace.eps0 (X ⟶ M) path_space_M (sec_Φ_path n s) = q_map (Φ n s)
  sec_Φ_eps1 : ∀ {X : PresheafCategory P C} (n : X ⟶ M) (s : X ⟶ S),
    @PathSpace.eps1 (X ⟶ M) path_space_M (sec_Φ_path n s) = n

  f_r : ∀ {X : PresheafCategory P C}, (X ⟶ R) → (X ⟶ G_0) → (X ⟶ G_0)
  f_r_inv : ∀ {X : PresheafCategory P C}, (X ⟶ R) → (X ⟶ G_0) → (X ⟶ G_0)
  ϵ_r : ∀ {X : PresheafCategory P C} (r : X ⟶ R) (x : X ⟶ G_0), f_r_inv r (f_r r x) = x

def Φ_inv {P : Type u} {C : Category.{v, u} P} {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  (ctx : CryptoContext P C trunc) {X : PresheafCategory P C} (p : X ⟶ ctx.G_0) (s : X ⟶ ctx.S) : X ⟶ ctx.M :=
  ctx.q_map p

def Cipher {P : Type u} {C : Category.{v, u} P} {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  (ctx : CryptoContext P C trunc) {X : PresheafCategory P C} (n : X ⟶ ctx.M) (s : X ⟶ ctx.S) (r : X ⟶ ctx.R) : X ⟶ ctx.G_0 :=
  ctx.f_r r (ctx.Φ n s)

def Decipher {P : Type u} {C : Category.{v, u} P} {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  (ctx : CryptoContext P C trunc) {X : PresheafCategory P C} (ρ : X ⟶ ctx.G_0) (s : X ⟶ ctx.S) (r : X ⟶ ctx.R) : X ⟶ ctx.M :=
  Φ_inv ctx (ctx.f_r_inv r ρ) s

def Theorem_Correctness_Path {P : Type u} {C : Category.{v, u} P} {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  (ctx : CryptoContext P C trunc) {X : PresheafCategory P C} (n : X ⟶ ctx.M) (s : X ⟶ ctx.S) (r : X ⟶ ctx.R) :
    @PathSpace.P (X ⟶ ctx.M) ctx.path_space_M :=
  ctx.sec_Φ_path n s

theorem Theorem_Correctness_Path_eps0 {P : Type u} {C : Category.{v, u} P} {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  (ctx : CryptoContext P C trunc) {X : PresheafCategory P C} (n : X ⟶ ctx.M) (s : X ⟶ ctx.S) (r : X ⟶ ctx.R) :
    @PathSpace.eps0 (X ⟶ ctx.M) ctx.path_space_M (Theorem_Correctness_Path ctx n s r) = Decipher ctx (Cipher ctx n s r) s r := by
  dsimp [Theorem_Correctness_Path, Decipher, Cipher, Φ_inv]
  have h := ctx.ϵ_r r (ctx.Φ n s)
  rw [h]
  exact ctx.sec_Φ_eps0 n s

theorem Theorem_Correctness_Path_eps1 {P : Type u} {C : Category.{v, u} P} {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  (ctx : CryptoContext P C trunc) {X : PresheafCategory P C} (n : X ⟶ ctx.M) (s : X ⟶ ctx.S) (r : X ⟶ ctx.R) :
    @PathSpace.eps1 (X ⟶ ctx.M) ctx.path_space_M (Theorem_Correctness_Path ctx n s r) = n :=
  ctx.sec_Φ_eps1 n s

theorem Theorem_Uniqueness_M {P : Type u} {C : Category.{v, u} P} {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  (ctx : CryptoContext P C trunc) {X : PresheafCategory P C} (n : X ⟶ ctx.M) (s : X ⟶ ctx.S) (r : X ⟶ ctx.R)
  (p1 p2 : @PathSpace.P (X ⟶ ctx.M) ctx.path_space_M)
  (h0_1 : @PathSpace.eps0 (X ⟶ ctx.M) ctx.path_space_M p1 = Decipher ctx (Cipher ctx n s r) s r)
  (h1_1 : @PathSpace.eps1 (X ⟶ ctx.M) ctx.path_space_M p1 = n)
  (h0_2 : @PathSpace.eps0 (X ⟶ ctx.M) ctx.path_space_M p2 = Decipher ctx (Cipher ctx n s r) s r)
  (h1_2 : @PathSpace.eps1 (X ⟶ ctx.M) ctx.path_space_M p2 = n) :
  p1 = p2 := by
  apply ctx.is_hSet_M p1 p2
  · rw [h0_1, h0_2]
  · rw [h1_1, h1_2]

structure InternalGeometry (P : Type u) (C : Category.{v, u} P)
  (trunc_thm : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C))
  (ctx : CryptoContext P C trunc_thm) where

  Nat_obj : PresheafCategory P C
  ZMod_q_obj : PresheafCategory P C
  String_obj : PresheafCategory P C

  path_space_Nat : ∀ {X : PresheafCategory P C}, PathSpace (X ⟶ Nat_obj)
  path_space_ZMod : ∀ {X : PresheafCategory P C}, PathSpace (X ⟶ ZMod_q_obj)

  nat_add : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  nat_sub : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  prop_nat_lt : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → Prop
  prop_nat_le : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → Prop

  cst_zero : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj
  cst_one : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj
  cst_q : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj
  cst_minus_one : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj
  cst_minus_two : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj
  cst_inv_two : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj
  cst_sqrt_exp : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj
  cst_g : ∀ {X : PresheafCategory P C}, X ⟶ Nat_obj

  zmod_zero : ∀ {X : PresheafCategory P C}, X ⟶ ZMod_q_obj
  zmod_one : ∀ {X : PresheafCategory P C}, X ⟶ ZMod_q_obj
  zmod_neg_one : ∀ {X : PresheafCategory P C}, X ⟶ ZMod_q_obj
  zmod_neg_two : ∀ {X : PresheafCategory P C}, X ⟶ ZMod_q_obj
  cast_nat_zmod : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ ZMod_q_obj)

  prop_q_pos : ∀ {X : PresheafCategory P C}, Prop
  prop_q_gt_one : ∀ {X : PresheafCategory P C}, Prop
  prop_q_ne_zero : ∀ {X : PresheafCategory P C}, Prop

  minus_one_eq_path : ∀ {X : PresheafCategory P C}, @PathSpace.P (X ⟶ ZMod_q_obj) path_space_ZMod
  minus_two_eq_path : ∀ {X : PresheafCategory P C}, @PathSpace.P (X ⟶ ZMod_q_obj) path_space_ZMod
  cast_zero_eq_zero_path : ∀ {X : PresheafCategory P C}, @PathSpace.P (X ⟶ ZMod_q_obj) path_space_ZMod
  cast_one_eq_one_path : ∀ {X : PresheafCategory P C}, @PathSpace.P (X ⟶ ZMod_q_obj) path_space_ZMod

  modAdd : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  modMul : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  modMulExp : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  modAddExp : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  modPower : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  modInverse : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  modSub : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)

  solveSubProblem : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  calcCRTTerm : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  discreteLog : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj)

  prop_g_primitive : ∀ {X : PresheafCategory P C}, Prop
  zmod_pow : ∀ {X : PresheafCategory P C}, (X ⟶ ZMod_q_obj) → (X ⟶ Nat_obj) → (X ⟶ ZMod_q_obj)

  discreteLogExistential : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  discreteLogExistential_lt : ∀ {X : PresheafCategory P C} (val : X ⟶ Nat_obj), Prop
  discreteLogExistential_ZMod : ∀ {X : PresheafCategory P C}, (X ⟶ ZMod_q_obj) → (X ⟶ Nat_obj)
  discreteLogExistential_spec_path : ∀ {X : PresheafCategory P C} (v : X ⟶ ZMod_q_obj) (h_nonzero : Prop), @PathSpace.P (X ⟶ ZMod_q_obj) path_space_ZMod

  Manifold4D_obj : PresheafCategory P C
  mkManifold4D : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Manifold4D_obj)
  path_space_M4D : ∀ {X : PresheafCategory P C}, PathSpace (X ⟶ Manifold4D_obj)

  m4_id : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ Nat_obj)
  m4_x : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ Nat_obj)
  m4_y : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ Nat_obj)
  m4_z : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ Nat_obj)
  m4_t : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ Nat_obj)

  calculateQ_m : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ ZMod_q_obj)
  Psi7 : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  PartialDerivative_Psi7_w : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)

  Tuple7_obj : PresheafCategory P C
  AddStep : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Tuple7_obj)
  Metric_g : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  Skewness_T : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)

  tuple7_proj0 : ∀ {X : PresheafCategory P C}, (X ⟶ Tuple7_obj) → (X ⟶ Nat_obj)
  tuple7_proj1 : ∀ {X : PresheafCategory P C}, (X ⟶ Tuple7_obj) → (X ⟶ Nat_obj)
  tuple7_proj2 : ∀ {X : PresheafCategory P C}, (X ⟶ Tuple7_obj) → (X ⟶ Nat_obj)
  tuple7_proj3 : ∀ {X : PresheafCategory P C}, (X ⟶ Tuple7_obj) → (X ⟶ Nat_obj)
  tuple7_proj4 : ∀ {X : PresheafCategory P C}, (X ⟶ Tuple7_obj) → (X ⟶ Nat_obj)
  tuple7_proj5 : ∀ {X : PresheafCategory P C}, (X ⟶ Tuple7_obj) → (X ⟶ Nat_obj)
  tuple7_proj6 : ∀ {X : PresheafCategory P C}, (X ⟶ Tuple7_obj) → (X ⟶ Nat_obj)

  Calculate_Absolute_w : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  Calculate_Q_coord : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  Calculate_w_0 : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  Calculate_w_end : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)

  ListNat_obj : PresheafCategory P C
  TupleListNat_obj : PresheafCategory P C
  Except_Validation_obj : PresheafCategory P C
  except_error : ∀ {X : PresheafCategory P C}, (X ⟶ String_obj) → (X ⟶ Except_Validation_obj)
  except_ok : ∀ {X : PresheafCategory P C}, (X ⟶ TupleListNat_obj) → (X ⟶ Except_Validation_obj)

  tupleListNat_fst : ∀ {X : PresheafCategory P C}, (X ⟶ TupleListNat_obj) → (X ⟶ ListNat_obj)
  tupleListNat_snd : ∀ {X : PresheafCategory P C}, (X ⟶ TupleListNat_obj) → (X ⟶ ListNat_obj)

  DetermineAndValidateBoundaries : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Except_Validation_obj)
  Calculate_Lg_M : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  Calculate_M : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)

  AlgebraicState7_obj : PresheafCategory P C
  mkAlgebraicState7 : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ AlgebraicState7_obj)

  alg_x : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  alg_y : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  alg_z : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  alg_t : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  alg_r : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  alg_ell : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  alg_E : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)

  calculateAlgebraicQ : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  recoverW : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  evaluateLogRelation : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj)
  evaluateExpRelation : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  reifyAlgebraicTo7D : ∀ {X : PresheafCategory P C}, (X ⟶ AlgebraicState7_obj) → (X ⟶ Nat_obj) → (X ⟶ ListNat_obj)

  geodesicResidual : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ Manifold4D_obj) → (X ⟶ Manifold4D_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj) → (X ⟶ ZMod_q_obj)
  getX : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  EvaluateEquationK : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ ListNat_obj) → (X ⟶ ListNat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)

  ConcretePath_obj : PresheafCategory P C
  ListManifold4D_obj : PresheafCategory P C

  OptionNat_obj : PresheafCategory P C
  path_space_OptionNat : ∀ {X : PresheafCategory P C}, PathSpace (X ⟶ OptionNat_obj)

  OptionM4_obj : PresheafCategory P C
  path_space_OptionM4 : ∀ {X : PresheafCategory P C}, PathSpace (X ⟶ OptionM4_obj)

  some_nat : ∀ {X : PresheafCategory P C}, (X ⟶ Nat_obj) → (X ⟶ OptionNat_obj)
  none_nat : ∀ {X : PresheafCategory P C}, X ⟶ OptionNat_obj
  some_m4 : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ OptionM4_obj)
  none_m4 : ∀ {X : PresheafCategory P C}, X ⟶ OptionM4_obj

  list_length_nat : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ Nat_obj)
  list_append_nat : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ ListNat_obj) → (X ⟶ ListNat_obj)
  list_dropLast_nat : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ ListNat_obj)
  list_head_nat : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ OptionNat_obj)
  list_getLast_nat : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ OptionNat_obj)

  list_length_m4 : ∀ {X : PresheafCategory P C}, (X ⟶ ListManifold4D_obj) → (X ⟶ Nat_obj)
  list_append_m4 : ∀ {X : PresheafCategory P C}, (X ⟶ ListManifold4D_obj) → (X ⟶ ListManifold4D_obj) → (X ⟶ ListManifold4D_obj)
  list_dropLast_m4 : ∀ {X : PresheafCategory P C}, (X ⟶ ListManifold4D_obj) → (X ⟶ ListManifold4D_obj)
  list_head_m4 : ∀ {X : PresheafCategory P C}, (X ⟶ ListManifold4D_obj) → (X ⟶ OptionM4_obj)
  list_getLast_m4 : ∀ {X : PresheafCategory P C}, (X ⟶ ListManifold4D_obj) → (X ⟶ OptionM4_obj)

  path_m_seq_map : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → (X ⟶ ListManifold4D_obj)
  path_r_seq_map : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → (X ⟶ ListNat_obj)
  path_E_seq_map : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → (X ⟶ ListNat_obj)
  path_ell_seq_map : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → (X ⟶ ListNat_obj)
  path_N_map : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → (X ⟶ Nat_obj)
  path_n_global_map : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → (X ⟶ Nat_obj)

  prop_h_len : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj), Prop
  prop_h_dom : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj) (dom : X ⟶ Manifold4D_obj), Prop
  prop_h_cod : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj) (cod : X ⟶ Manifold4D_obj), Prop
  prop_r_lt : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj), Prop
  prop_ell_lt : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj), Prop
  prop_E_lt : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj), Prop

  isStrictGeodesicPath : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → Prop
  GeodesicMorphism : ∀ {X : PresheafCategory P C}, (X ⟶ Manifold4D_obj) → (X ⟶ Manifold4D_obj) → Prop

  list_get_nat : ∀ {X : PresheafCategory P C}, (X ⟶ ListNat_obj) → (X ⟶ Nat_obj) → (X ⟶ Nat_obj)
  list_get_m4 : ∀ {X : PresheafCategory P C}, (X ⟶ ListManifold4D_obj) → (X ⟶ Nat_obj) → (X ⟶ Manifold4D_obj)

  get_of_fin_eq_path_nat : ∀ {X : PresheafCategory P C} (ys : X ⟶ ListNat_obj) (idx1 idx2 : X ⟶ Nat_obj) (h_eq : @PathSpace.P (X ⟶ Nat_obj) path_space_Nat), @PathSpace.P (X ⟶ Nat_obj) path_space_Nat
  my_get_append_left_path_nat : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListNat_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_lt i (list_length_nat xs)) (h_con : prop_nat_lt i (list_length_nat (list_append_nat xs ys))), @PathSpace.P (X ⟶ Nat_obj) path_space_Nat
  my_get_append_right_path_nat : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListNat_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_le (list_length_nat xs) i) (h_con : prop_nat_lt i (list_length_nat (list_append_nat xs ys))) (h_con2 : prop_nat_lt (nat_sub i (list_length_nat xs)) (list_length_nat ys)), @PathSpace.P (X ⟶ Nat_obj) path_space_Nat
  get_dropLast_path_nat : ∀ {X : PresheafCategory P C} (xs : X ⟶ ListNat_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_lt i (nat_sub (list_length_nat xs) cst_one)) (h_con1 : prop_nat_lt i (list_length_nat (list_dropLast_nat xs))) (h_con2 : prop_nat_lt i (list_length_nat xs)), @PathSpace.P (X ⟶ Nat_obj) path_space_Nat
  get_append_dropLast_left_path_nat : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListNat_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_lt i (nat_sub (list_length_nat xs) cst_one)) (h_con : prop_nat_lt i (list_length_nat (list_append_nat (list_dropLast_nat xs) ys))) (h_con2 : prop_nat_lt i (list_length_nat xs)), @PathSpace.P (X ⟶ Nat_obj) path_space_Nat
  get_append_dropLast_right_path_nat : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListNat_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_le (nat_sub (list_length_nat xs) cst_one) i) (h_con : prop_nat_lt i (list_length_nat (list_append_nat (list_dropLast_nat xs) ys))) (h_con2 : prop_nat_lt (nat_sub i (nat_sub (list_length_nat xs) cst_one)) (list_length_nat ys)), @PathSpace.P (X ⟶ Nat_obj) path_space_Nat

  get_of_fin_eq_path_m4 : ∀ {X : PresheafCategory P C} (ys : X ⟶ ListManifold4D_obj) (idx1 idx2 : X ⟶ Nat_obj) (h_eq : @PathSpace.P (X ⟶ Nat_obj) path_space_Nat), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D
  my_get_append_left_path_m4 : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListManifold4D_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_lt i (list_length_m4 xs)) (h_con : prop_nat_lt i (list_length_m4 (list_append_m4 xs ys))), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D
  my_get_append_right_path_m4 : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListManifold4D_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_le (list_length_m4 xs) i) (h_con : prop_nat_lt i (list_length_m4 (list_append_m4 xs ys))) (h_con2 : prop_nat_lt (nat_sub i (list_length_m4 xs)) (list_length_m4 ys)), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D
  get_dropLast_path_m4 : ∀ {X : PresheafCategory P C} (xs : X ⟶ ListManifold4D_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_lt i (nat_sub (list_length_m4 xs) cst_one)) (h_con1 : prop_nat_lt i (list_length_m4 (list_dropLast_m4 xs))) (h_con2 : prop_nat_lt i (list_length_m4 xs)), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D
  get_append_dropLast_left_path_m4 : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListManifold4D_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_lt i (nat_sub (list_length_m4 xs) cst_one)) (h_con : prop_nat_lt i (list_length_m4 (list_append_m4 (list_dropLast_m4 xs) ys))) (h_con2 : prop_nat_lt i (list_length_m4 xs)), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D
  get_append_dropLast_right_path_m4 : ∀ {X : PresheafCategory P C} (xs ys : X ⟶ ListManifold4D_obj) (i : X ⟶ Nat_obj) (hi : prop_nat_le (nat_sub (list_length_m4 xs) cst_one) i) (h_con : prop_nat_lt i (list_length_m4 (list_append_m4 (list_dropLast_m4 xs) ys))) (h_con2 : prop_nat_lt (nat_sub i (nat_sub (list_length_m4 xs) cst_one)) (list_length_m4 ys)), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D

  concatPath : ∀ {X : PresheafCategory P C}, (X ⟶ ConcretePath_obj) → (X ⟶ ConcretePath_obj) → (X ⟶ ConcretePath_obj)

  SmoothConnection : ∀ {X : PresheafCategory P C} (p1 p2 : X ⟶ ConcretePath_obj), Prop

  getLast_eq_get_path_m4 : ∀ {X : PresheafCategory P C} (l : X ⟶ ListManifold4D_obj) (h_pos : prop_nat_lt cst_zero (list_length_m4 l)), @PathSpace.P (X ⟶ OptionM4_obj) path_space_OptionM4
  get_zero_eq_head_path_m4 : ∀ {X : PresheafCategory P C} (l : X ⟶ ListManifold4D_obj) (h_pos : prop_nat_lt cst_zero (list_length_m4 l)) (dom : X ⟶ Manifold4D_obj) (h_dom : @PathSpace.P (X ⟶ OptionM4_obj) path_space_OptionM4), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D
  ConcretePath_get_zero_path : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj) (dom : X ⟶ Manifold4D_obj) (h_dom : prop_h_dom p dom), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D
  ConcretePath_get_last_path : ∀ {X : PresheafCategory P C} (p : X ⟶ ConcretePath_obj) (cod : X ⟶ Manifold4D_obj) (h_cod : prop_h_cod p cod), @PathSpace.P (X ⟶ Manifold4D_obj) path_space_M4D

  geodesic_residual_at_connection_path : ∀ {X : PresheafCategory P C} (p1 p2 : X ⟶ ConcretePath_obj) (h_smooth : SmoothConnection p1 p2) (h1 : prop_nat_lt cst_zero (path_N_map p1)) (h2 : prop_nat_lt cst_zero (path_N_map p2)), @PathSpace.P (X ⟶ ZMod_q_obj) path_space_ZMod

  geodesic_id_prop : ∀ {X : PresheafCategory P C} (dom : X ⟶ Manifold4D_obj) (h_reg : Prop), GeodesicMorphism dom dom

variable {P_cat : Type u} {C_cat : Category.{v, u} P_cat}
variable {trunc_thm : Theorem_CohZeroType_Eq_CohObject (P := P_cat) (C := C_cat)}
variable {ctx : CryptoContext P_cat C_cat trunc_thm}
variable (geom : InternalGeometry P_cat C_cat trunc_thm ctx)

def Construct_M_space : PresheafCategory P_cat C_cat := geom.ZMod_q_obj
def Construct_R_space : PresheafCategory P_cat C_cat := geom.ZMod_q_obj
def Construct_G_0_space : PresheafCategory P_cat C_cat := geom.ZMod_q_obj
def Construct_S_space : PresheafCategory P_cat C_cat := geom.Manifold4D_obj

def Construct_Phi {X : PresheafCategory P_cat C_cat} (n : X ⟶ Construct_M_space geom) (s : X ⟶ Construct_S_space geom) : X ⟶ Construct_G_0_space geom :=
  geom.cast_nat_zmod (geom.modPower (geom.discreteLogExistential_ZMod n) (geom.m4_x s))

def Construct_Decipher_Eval {X : PresheafCategory P_cat C_cat} (ρ : X ⟶ Construct_G_0_space geom) (s : X ⟶ Construct_S_space geom) (r : X ⟶ Construct_R_space geom) : X ⟶ Construct_M_space geom :=
  geom.cast_nat_zmod (geom.modSub (geom.discreteLogExistential_ZMod ρ) (geom.discreteLogExistential_ZMod r))

axiom Construct_Correctness_Path
  {P : Type u} {C : Category.{v, u} P}
  {trunc : Theorem_CohZeroType_Eq_CohObject (P := P) (C := C)}
  {c : CryptoContext P C trunc}
  (g : InternalGeometry P C trunc c) :
  ∀ {X : PresheafCategory P C} (n : X ⟶ Construct_M_space g) (s : X ⟶ Construct_S_space g) (r : X ⟶ Construct_R_space g),
  @PathSpace.P (X ⟶ Construct_M_space g) g.path_space_ZMod

structure MicroMacroEquivalence where
  eq_M : Construct_M_space geom = ctx.M
  eq_S : Construct_S_space geom = ctx.S
  eq_R : Construct_R_space geom = ctx.R
  eq_G_0 : Construct_G_0_space geom = ctx.G_0

  phi_eq : ∀ {X : PresheafCategory P_cat C_cat} (n : X ⟶ Construct_M_space geom) (s : X ⟶ Construct_S_space geom),
    HEq (Construct_Phi geom n s) (ctx.Φ (X := X) (eq_M ▸ n) (eq_S ▸ s))

  decipher_eq : ∀ {X : PresheafCategory P_cat C_cat} (ρ : X ⟶ Construct_G_0_space geom) (s : X ⟶ Construct_S_space geom) (r : X ⟶ Construct_R_space geom),
    HEq (Construct_Decipher_Eval geom ρ s r) (Decipher ctx (X := X) (eq_G_0 ▸ ρ) (eq_S ▸ s) (eq_R ▸ r))

  path_reduction : ∀ {X : PresheafCategory P_cat C_cat} (n : X ⟶ Construct_M_space geom) (s : X ⟶ Construct_S_space geom) (r : X ⟶ Construct_R_space geom),
    HEq (Construct_Correctness_Path geom n s r) (Theorem_Correctness_Path ctx (X := X) (eq_M ▸ n) (eq_S ▸ s) (eq_R ▸ r))

end CryptoTopos
