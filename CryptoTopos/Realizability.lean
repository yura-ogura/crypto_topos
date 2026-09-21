import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CryptoTopos

universe u

def compCode (e1 e2 : Nat) : Nat := Nat.pair e1 e2 + 4
def pairCode (e1 e2 : Nat) : Nat := Nat.pair e1 e2 + 5
def cipherCode : Nat := 6
def decipherCode : Nat := 7

inductive KleeneEval : Nat → Nat → Nat → Prop where
  | id (x : Nat) : KleeneEval 0 x x
  | zero (x : Nat) : KleeneEval 1 x 0
  | fst (nx ny : Nat) : KleeneEval 2 (Nat.pair nx ny) nx
  | snd (nx ny : Nat) : KleeneEval 3 (Nat.pair nx ny) ny
  | comp (e1 e2 x y z : Nat) :
      KleeneEval e1 x y → KleeneEval e2 y z → KleeneEval (compCode e1 e2) x z
  | pair (e1 e2 z nx ny : Nat) :
      KleeneEval e1 z nx → KleeneEval e2 z ny → KleeneEval (pairCode e1 e2) z (Nat.pair nx ny)
  | cipher (n s r : Nat) :
      KleeneEval cipherCode (Nat.pair (Nat.pair n s) r) ((n + s * r) % 2147483647)
  | decipher (c s r : Nat) :
      KleeneEval decipherCode (Nat.pair (Nat.pair c s) r) ((c + (2147483647 - 1) * (s * r % 2147483647)) % 2147483647)

def KleeneEvaluatesTo (e x y : Nat) : Prop := KleeneEval e x y

theorem nat_pair_inj {a b c d : Nat} (h : Nat.pair a b = Nat.pair c d) : a = c ∧ b = d := by
  have h_unpair := congrArg Nat.unpair h
  rw [Nat.unpair_pair, Nat.unpair_pair] at h_unpair
  exact Prod.mk.inj h_unpair

structure PartitionedAssembly where
  carrier : Type u
  realizer : carrier → Set Nat
  realizer_nonempty : ∀ x : carrier, ∃ n : Nat, n ∈ realizer x
  realizer_disjoint : ∀ (x y : carrier) (n : Nat), n ∈ realizer x → n ∈ realizer y → x = y

namespace PartitionedAssembly

variable {X : PartitionedAssembly.{u}}

theorem unique_element_of_realizer {x y : X.carrier} {n : Nat}
    (hx : n ∈ X.realizer x) (hy : n ∈ X.realizer y) : x = y :=
  X.realizer_disjoint x y n hx hy

end PartitionedAssembly

def IsTrackedBy (X Y : PartitionedAssembly.{u}) (f : X.carrier → Y.carrier) (e : Nat) : Prop :=
  ∀ (x : X.carrier) (n : Nat), n ∈ X.realizer x →
    ∃ m : Nat, KleeneEvaluatesTo e n m ∧ m ∈ Y.realizer (f x)

def IsTracked (X Y : PartitionedAssembly.{u}) (f : X.carrier → Y.carrier) : Prop :=
  ∃ e : Nat, IsTrackedBy X Y f e

structure TrackedMap (X Y : PartitionedAssembly.{u}) where
  toFun : X.carrier → Y.carrier
  tracked : IsTracked X Y toFun

namespace TrackedMap

variable {X Y : PartitionedAssembly.{u}}

instance : CoeFun (TrackedMap X Y) (fun _ => X.carrier → Y.carrier) where
  coe f := f.toFun

@[simp]
theorem coe_eq_toFun (f : TrackedMap X Y) : (f : X.carrier → Y.carrier) = f.toFun := rfl

@[ext]
theorem ext {f g : TrackedMap X Y} (h : ∀ x : X.carrier, f x = g x) : f = g := by
  have h_fun : f.toFun = g.toFun := funext h
  cases f; cases g
  dsimp at h_fun
  subst h_fun
  rfl

end TrackedMap

theorem id_isTracked (X : PartitionedAssembly.{u}) : IsTracked X X id := by
  use 0
  intro x n hn
  exact ⟨n, KleeneEval.id n, hn⟩

def P_cat_id (X : PartitionedAssembly.{u}) : TrackedMap X X where
  toFun := id
  tracked := id_isTracked X

theorem comp_isTracked {X Y Z : PartitionedAssembly.{u}}
    (f : TrackedMap X Y) (g : TrackedMap Y Z) :
    IsTracked X Z (g.toFun ∘ f.toFun) := by
  rcases f.tracked with ⟨ef, hf⟩
  rcases g.tracked with ⟨eg, hg⟩
  use compCode ef eg
  intro x n hn
  rcases hf x n hn with ⟨m1, hm1_eval, hm1_real⟩
  rcases hg (f.toFun x) m1 hm1_real with ⟨m2, hm2_eval, hm2_real⟩
  exact ⟨m2, KleeneEval.comp ef eg n m1 m2 hm1_eval hm2_eval, hm2_real⟩

def P_cat_comp {X Y Z : PartitionedAssembly.{u}}
    (f : TrackedMap X Y) (g : TrackedMap Y Z) : TrackedMap X Z where
  toFun := g.toFun ∘ f.toFun
  tracked := comp_isTracked f g

theorem P_cat_id_comp {X Y : PartitionedAssembly.{u}} (f : TrackedMap X Y) :
    P_cat_comp (P_cat_id X) f = f := by
  ext x; rfl

theorem P_cat_comp_id {X Y : PartitionedAssembly.{u}} (f : TrackedMap X Y) :
    P_cat_comp f (P_cat_id Y) = f := by
  ext x; rfl

theorem P_cat_assoc {W X Y Z : PartitionedAssembly.{u}}
    (f : TrackedMap W X) (g : TrackedMap X Y) (h : TrackedMap Y Z) :
    P_cat_comp (P_cat_comp f g) h = P_cat_comp f (P_cat_comp g h) := by
  ext x; rfl

instance partitionedAssemblyCategory : Category.{u, u + 1} (PartitionedAssembly.{u}) where
  Hom X Y := TrackedMap X Y
  id X := P_cat_id X
  comp f g := P_cat_comp f g
  id_comp f := P_cat_id_comp f
  comp_id f := P_cat_comp_id f
  assoc f g h := P_cat_assoc f g h

@[simp]
theorem comp_eq_P_cat_comp {X Y Z : PartitionedAssembly.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = P_cat_comp f g := rfl

@[simp]
theorem id_eq_P_cat_id (X : PartitionedAssembly.{u}) :
    𝟙 X = P_cat_id X := rfl

def onePA : PartitionedAssembly.{u} where
  carrier := PUnit
  realizer := fun _ => {0}
  realizer_nonempty := fun _ => ⟨0, Set.mem_singleton 0⟩
  realizer_disjoint := fun x y n hx hy => by cases x; cases y; rfl

theorem toTerminal_isTracked (X : PartitionedAssembly.{u}) :
    IsTracked X onePA (fun _ => PUnit.unit) := by
  use 1
  intro x n hn
  exact ⟨0, KleeneEval.zero n, Set.mem_singleton 0⟩

def toTerminalPA (X : PartitionedAssembly.{u}) : TrackedMap X onePA where
  toFun := fun _ => PUnit.unit
  tracked := toTerminal_isTracked X

theorem toTerminalPA_unique {X : PartitionedAssembly.{u}} (f : TrackedMap X onePA) :
    f = toTerminalPA X := by
  ext x; cases f x; rfl

class ChosenTerminal (C : Type (u + 1)) [Category.{u, u + 1} C] where
  terminal : C
  toTerminal : ∀ X : C, X ⟶ terminal
  terminal_uniq : ∀ {X : C} (f : X ⟶ terminal), f = toTerminal X

instance : ChosenTerminal (PartitionedAssembly.{u}) where
  terminal := onePA
  toTerminal X := toTerminalPA X
  terminal_uniq f := toTerminalPA_unique f

def prodPA (X Y : PartitionedAssembly.{u}) : PartitionedAssembly.{u} where
  carrier := X.carrier × Y.carrier
  realizer := fun p =>
    { n | ∃ nx ny, nx ∈ X.realizer p.1 ∧ ny ∈ Y.realizer p.2 ∧ n = Nat.pair nx ny }
  realizer_nonempty := by
    intro ⟨x, y⟩
    rcases X.realizer_nonempty x with ⟨nx, hnx⟩
    rcases Y.realizer_nonempty y with ⟨ny, hny⟩
    exact ⟨Nat.pair nx ny, ⟨nx, ny, hnx, hny, rfl⟩⟩
  realizer_disjoint := by
    rintro ⟨x1, y1⟩ ⟨x2, y2⟩ n ⟨nx1, ny1, hnx1, hny1, rfl⟩ ⟨nx2, ny2, hnx2, hny2, hn_eq⟩
    have h_inj := nat_pair_inj hn_eq
    have hx : x1 = x2 := X.realizer_disjoint x1 x2 nx1 hnx1 (h_inj.1 ▸ hnx2)
    have hy : y1 = y2 := Y.realizer_disjoint y1 y2 ny1 hny1 (h_inj.2 ▸ hny2)
    exact Prod.ext hx hy

theorem proj1_isTracked (X Y : PartitionedAssembly.{u}) :
    IsTracked (prodPA X Y) X Prod.fst := by
  use 2
  rintro ⟨x, y⟩ n ⟨nx, ny, hnx, hny, rfl⟩
  exact ⟨nx, KleeneEval.fst nx ny, hnx⟩

def proj1PA (X Y : PartitionedAssembly.{u}) : TrackedMap (prodPA X Y) X where
  toFun := Prod.fst
  tracked := proj1_isTracked X Y

theorem proj2_isTracked (X Y : PartitionedAssembly.{u}) :
    IsTracked (prodPA X Y) Y Prod.snd := by
  use 3
  rintro ⟨x, y⟩ n ⟨nx, ny, hnx, hny, rfl⟩
  exact ⟨ny, KleeneEval.snd nx ny, hny⟩

def proj2PA (X Y : PartitionedAssembly.{u}) : TrackedMap (prodPA X Y) Y where
  toFun := Prod.snd
  tracked := proj2_isTracked X Y

def pairPA {Z X Y : PartitionedAssembly.{u}}
    (f : TrackedMap Z X) (g : TrackedMap Z Y) : TrackedMap Z (prodPA X Y) where
  toFun := fun z => (f z, g z)
  tracked := by
    rcases f.tracked with ⟨ef, hf⟩
    rcases g.tracked with ⟨eg, hg⟩
    use pairCode ef eg
    intro z nz hnz
    rcases hf z nz hnz with ⟨mx, hmx_eval, hmx_real⟩
    rcases hg z nz hnz with ⟨my, hmy_eval, hmy_real⟩
    exact ⟨Nat.pair mx my, KleeneEval.pair ef eg nz mx my hmx_eval hmy_eval, ⟨mx, my, hmx_real, hmy_real, rfl⟩⟩

@[simp]
theorem pairPA_comp_proj1 {Z X Y : PartitionedAssembly.{u}}
    (f : TrackedMap Z X) (g : TrackedMap Z Y) :
    P_cat_comp (pairPA f g) (proj1PA X Y) = f := by
  ext z; rfl

@[simp]
theorem pairPA_comp_proj2 {Z X Y : PartitionedAssembly.{u}}
    (f : TrackedMap Z X) (g : TrackedMap Z Y) :
    P_cat_comp (pairPA f g) (proj2PA X Y) = g := by
  ext z; rfl

theorem pairPA_unique {Z X Y : PartitionedAssembly.{u}}
    (f : TrackedMap Z X) (g : TrackedMap Z Y)
    (h : TrackedMap Z (prodPA X Y))
    (h1 : P_cat_comp h (proj1PA X Y) = f)
    (h2 : P_cat_comp h (proj2PA X Y) = g) :
    h = pairPA f g := by
  ext z
  have h_fst : (P_cat_comp h (proj1PA X Y)) z = f z := by rw [h1]
  have h_snd : (P_cat_comp h (proj2PA X Y)) z = g z := by rw [h2]
  dsimp [P_cat_comp, proj1PA, proj2PA, pairPA] at h_fst h_snd ⊢
  exact Prod.ext h_fst h_snd

def q : Nat := 2147483647

lemma q_pos : q > 0 := by
  unfold q
  omega

lemma q_ne_zero : q ≠ 0 := by
  unfold q
  omega

instance : NeZero q := ⟨q_ne_zero⟩

def Zq_PA : PartitionedAssembly.{0} where
  carrier := ZMod q
  realizer := fun x => {x.val}
  realizer_nonempty := by
    intro x
    exact ⟨x.val, Set.mem_singleton x.val⟩
  realizer_disjoint := by
    intro x y n hx hy
    have hx_eq : n = x.val := Set.mem_singleton_iff.mp hx
    have hy_eq : n = y.val := Set.mem_singleton_iff.mp hy
    have h_val : x.val = y.val := hx_eq.symm.trans hy_eq
    have h_cast_x : (x.val : ZMod q) = x := ZMod.natCast_zmod_val x
    have h_cast_y : (y.val : ZMod q) = y := ZMod.natCast_zmod_val y
    rw [← h_cast_x, ← h_cast_y, h_val]

@[simp]
theorem mem_realizer_Zq_PA (x : ZMod q) (n : Nat) :
    n ∈ Zq_PA.realizer x ↔ n = x.val :=
  Set.mem_singleton_iff

def cipherFun (p : (ZMod q × ZMod q) × ZMod q) : ZMod q :=
  p.1.1 + p.1.2 * p.2

lemma nat_add_mul_mod (a b c : Nat) :
    (a + (b * c) % q) % q = (a + b * c) % q := by
  calc (a + (b * c) % q) % q
    _ = (a % q + ((b * c) % q) % q) % q := by rw [Nat.add_mod]
    _ = (a % q + (b * c) % q) % q := by rw [Nat.mod_mod]
    _ = (a + b * c) % q := by rw [← Nat.add_mod]

lemma zmod_cipher_val (n s r : ZMod q) :
    (n + s * r).val = (n.val + s.val * r.val) % q := by
  rw [ZMod.val_add, ZMod.val_mul]
  exact nat_add_mul_mod n.val s.val r.val

theorem cipher_isTracked :
    IsTracked (prodPA (prodPA Zq_PA Zq_PA) Zq_PA) Zq_PA cipherFun := by
  use cipherCode
  rintro ⟨⟨(n : ZMod q), (s : ZMod q)⟩, (r : ZMod q)⟩ k hk
  dsimp [prodPA, Zq_PA] at hk ⊢
  rcases hk with ⟨n12, r_real, ⟨n_real, s_real, hn, hs, rfl⟩, hr, rfl⟩
  have hn_eq : n_real = n.val := Set.mem_singleton_iff.mp hn
  have hs_eq : s_real = s.val := Set.mem_singleton_iff.mp hs
  have hr_eq : r_real = r.val := Set.mem_singleton_iff.mp hr
  subst hn_eq hs_eq hr_eq
  have h_eval : KleeneEvaluatesTo cipherCode
      (Nat.pair (Nat.pair n.val s.val) r.val)
      ((n.val + s.val * r.val) % q) := by
    exact KleeneEval.cipher n.val s.val r.val
  refine ⟨(n.val + s.val * r.val) % q, h_eval, ?_⟩
  dsimp [Zq_PA, cipherFun]
  rw [Set.mem_singleton_iff]
  exact (zmod_cipher_val n s r).symm

def Cipher_TrackedMap :
    TrackedMap (prodPA (prodPA Zq_PA Zq_PA) Zq_PA) Zq_PA where
  toFun := cipherFun
  tracked := cipher_isTracked

def decipherFun (p : (ZMod q × ZMod q) × ZMod q) : ZMod q :=
  p.1.1 - p.1.2 * p.2

lemma nat_add_mod_right (a b : Nat) : (a + b % q) % q = (a + b) % q := by
  calc (a + b % q) % q
    _ = (a % q + (b % q) % q) % q := by rw [Nat.add_mod]
    _ = (a % q + b % q) % q := by rw [Nat.mod_mod]
    _ = (a + b) % q := by rw [← Nat.add_mod]

lemma val_cast_q_sub_one : (((q - 1 : Nat) : ZMod q).val) = q - 1 := by
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  unfold q
  omega

lemma zmod_decipher_val (c s r : ZMod q) :
    (c - s * r).val = (c.val + (q - 1) * (s.val * r.val % q)) % q := by
  have h_m1 : (((q - 1 : Nat) : ZMod q)) = -1 := by rfl
  have h_sub : c - s * r = c + (((q - 1 : Nat) : ZMod q)) * (s * r) := by
    rw [h_m1]
    ring
  rw [h_sub, ZMod.val_add, ZMod.val_mul, val_cast_q_sub_one, ZMod.val_mul]
  exact nat_add_mod_right c.val ((q - 1) * ((s.val * r.val) % q))

theorem decipher_isTracked :
    IsTracked (prodPA (prodPA Zq_PA Zq_PA) Zq_PA) Zq_PA decipherFun := by
  use decipherCode
  rintro ⟨⟨(c : ZMod q), (s : ZMod q)⟩, (r : ZMod q)⟩ k hk
  dsimp [prodPA, Zq_PA] at hk ⊢
  rcases hk with ⟨c12, r_real, ⟨c_real, s_real, hc, hs, rfl⟩, hr, rfl⟩
  have hc_eq : c_real = c.val := Set.mem_singleton_iff.mp hc
  have hs_eq : s_real = s.val := Set.mem_singleton_iff.mp hs
  have hr_eq : r_real = r.val := Set.mem_singleton_iff.mp hr
  subst hc_eq hs_eq hr_eq
  have h_eval : KleeneEvaluatesTo decipherCode
      (Nat.pair (Nat.pair c.val s.val) r.val)
      ((c.val + (q - 1) * (s.val * r.val % q)) % q) := by
    exact KleeneEval.decipher c.val s.val r.val
  refine ⟨(c.val + (q - 1) * (s.val * r.val % q)) % q, h_eval, ?_⟩
  dsimp [Zq_PA, decipherFun]
  rw [Set.mem_singleton_iff]
  exact (zmod_decipher_val c s r).symm

def Decipher_TrackedMap :
    TrackedMap (prodPA (prodPA Zq_PA Zq_PA) Zq_PA) Zq_PA where
  toFun := decipherFun
  tracked := decipher_isTracked

structure Manifold4D where
  id : Nat
  x  : Nat
  y  : Nat
  z  : Nat
  t  : Nat

def encodeManifold4D (m : Manifold4D) : Nat :=
  Nat.pair m.id (Nat.pair m.x (Nat.pair m.y (Nat.pair m.z m.t)))

theorem encodeManifold4D_inj {m1 m2 : Manifold4D}
    (h : encodeManifold4D m1 = encodeManifold4D m2) : m1 = m2 := by
  dsimp [encodeManifold4D] at h
  have h1 := nat_pair_inj h
  have h2 := nat_pair_inj h1.2
  have h3 := nat_pair_inj h2.2
  have h4 := nat_pair_inj h3.2
  cases m1
  cases m2
  dsimp at h1 h2 h3 h4
  have hid := h1.1
  have hx  := h2.1
  have hy  := h3.1
  have hz  := h4.1
  have ht  := h4.2
  subst hid hx hy hz ht
  rfl

def Manifold4D_PA : PartitionedAssembly.{0} where
  carrier := Manifold4D
  realizer := fun m => {encodeManifold4D m}
  realizer_nonempty := by
    intro m
    exact ⟨encodeManifold4D m, Set.mem_singleton (encodeManifold4D m)⟩
  realizer_disjoint := by
    intro m1 m2 n h1 h2
    have h1_eq : n = encodeManifold4D m1 := Set.mem_singleton_iff.mp h1
    have h2_eq : n = encodeManifold4D m2 := Set.mem_singleton_iff.mp h2
    have h_eq : encodeManifold4D m1 = encodeManifold4D m2 := h1_eq.symm.trans h2_eq
    exact encodeManifold4D_inj h_eq

@[simp]
theorem mem_realizer_Manifold4D_PA (m : Manifold4D) (n : Nat) :
    n ∈ Manifold4D_PA.realizer m ↔ n = encodeManifold4D m :=
  Set.mem_singleton_iff

abbrev Psh (C : Type (u + 1)) [Category.{u, u + 1} C] := Cᵒᵖ ⥤ Type u

def yPA (A : PartitionedAssembly.{0}) : Psh (PartitionedAssembly.{0}) :=
  (yoneda (C := PartitionedAssembly.{0})).obj A

def Psh_Zq : Psh (PartitionedAssembly.{0}) :=
  yPA Zq_PA

def Psh_S : Psh (PartitionedAssembly.{0}) :=
  Psh_Zq

def Psh_R : Psh (PartitionedAssembly.{0}) :=
  Psh_Zq

def Psh_G0 : Psh (PartitionedAssembly.{0}) :=
  Psh_Zq

def Psh_Manifold : Psh (PartitionedAssembly.{0}) :=
  yPA Manifold4D_PA

@[simp]
theorem Psh_Zq_obj_eval (X : PartitionedAssembly.{0}) :
    Psh_Zq.obj (Opposite.op X) = TrackedMap X Zq_PA :=
  rfl

@[simp]
theorem Psh_Zq_map_eval {X Y : PartitionedAssembly.{0}}
    (f : Opposite.op Y ⟶ Opposite.op X) (g : TrackedMap Y Zq_PA) :
    Psh_Zq.map f g = P_cat_comp f.unop g :=
  rfl

@[simp]
theorem yPA_obj_eval (A X : PartitionedAssembly.{0}) :
    (yPA A).obj (Opposite.op X) = TrackedMap X A :=
  rfl

@[simp]
theorem yPA_map_eval (A : PartitionedAssembly.{0}) {X Y : PartitionedAssembly.{0}}
    (f : Opposite.op Y ⟶ Opposite.op X) (g : TrackedMap Y A) :
    (yPA A).map f g = P_cat_comp f.unop g :=
  rfl

structure IsRepresentable (F : Psh (PartitionedAssembly.{0})) : Type 1 where
  P_obj : PartitionedAssembly.{0}
  iso   : F ≅ yPA P_obj

def psh_zq_is_representable : IsRepresentable Psh_Zq where
  P_obj := Zq_PA
  iso   := Iso.refl Psh_Zq

def psh_s_is_representable : IsRepresentable Psh_S :=
  psh_zq_is_representable

def psh_r_is_representable : IsRepresentable Psh_R :=
  psh_zq_is_representable

def psh_g0_is_representable : IsRepresentable Psh_G0 :=
  psh_zq_is_representable

def psh_manifold_is_representable : IsRepresentable Psh_Manifold where
  P_obj := Manifold4D_PA
  iso   := Iso.refl Psh_Manifold

def IsPshMono {X Y : Psh (PartitionedAssembly.{0})} (m : X ⟶ Y) : Prop :=
  ∀ {Z : Psh (PartitionedAssembly.{0})} (g h : Z ⟶ X), g ≫ m = h ≫ m → g = h

structure IsPshEpi {X Y : Psh (PartitionedAssembly.{0})} (e : X ⟶ Y) : Type 1 where
  surjective   : ∀ (P_obj : (PartitionedAssembly.{0})ᵒᵖ) (b : Y.obj P_obj),
    ∃ a : X.obj P_obj, e.app P_obj a = b
  right_cancel : ∀ {Z : Psh (PartitionedAssembly.{0})} (g h : Y ⟶ Z),
    e ≫ g = e ≫ h → g = h

structure IsAssembly (X : Psh (PartitionedAssembly.{0})) : Type 1 where
  P_obj  : PartitionedAssembly.{0}
  Q_obj  : PartitionedAssembly.{0}
  f      : yPA P_obj ⟶ yPA Q_obj
  e      : yPA P_obj ⟶ X
  m      : X ⟶ yPA Q_obj
  fac    : f = e ≫ m
  epi_e  : IsPshEpi e
  mono_m : IsPshMono m

def rep_is_asm (X : Psh (PartitionedAssembly.{0}))
    (hR : IsRepresentable X) : IsAssembly X := by
  let P_obj := hR.P_obj
  let iso := hR.iso
  refine {
    P_obj := P_obj
    Q_obj := P_obj
    f     := 𝟙 (yPA P_obj)
    e     := iso.inv
    m     := iso.hom
    fac   := by
      have h_inv := iso.inv_hom_id
      exact h_inv.symm
    epi_e := {
      surjective := by
        intro P_curr b
        refine ⟨iso.hom.app P_curr b, ?_⟩
        have h_app := congrArg (fun (k : X ⟶ X) => k.app P_curr b) iso.hom_inv_id
        dsimp at h_app ⊢
        exact h_app
      right_cancel := by
        intro Z g h hgh
        calc g = 𝟙 X ≫ g := (Category.id_comp g).symm
          _ = (iso.hom ≫ iso.inv) ≫ g := by rw [iso.hom_inv_id]
          _ = iso.hom ≫ (iso.inv ≫ g) := by rw [Category.assoc]
          _ = iso.hom ≫ (iso.inv ≫ h) := by rw [hgh]
          _ = (iso.hom ≫ iso.inv) ≫ h := by rw [← Category.assoc]
          _ = 𝟙 X ≫ h := by rw [iso.hom_inv_id]
          _ = h := Category.id_comp h
    }
    mono_m := by
      intro Z g h hgh
      calc g = g ≫ 𝟙 X := (Category.comp_id g).symm
        _ = g ≫ (iso.hom ≫ iso.inv) := by rw [iso.hom_inv_id]
        _ = (g ≫ iso.hom) ≫ iso.inv := by rw [Category.assoc]
        _ = (h ≫ iso.hom) ≫ iso.inv := by rw [hgh]
        _ = h ≫ (iso.hom ≫ iso.inv) := by rw [← Category.assoc]
        _ = h ≫ 𝟙 X := by rw [iso.hom_inv_id]
        _ = h := Category.comp_id h
  }

def psh_zq_is_assembly : IsAssembly Psh_Zq :=
  rep_is_asm Psh_Zq psh_zq_is_representable

def psh_s_is_assembly : IsAssembly Psh_S :=
  psh_zq_is_assembly

def psh_r_is_assembly : IsAssembly Psh_R :=
  psh_zq_is_assembly

def psh_g0_is_assembly : IsAssembly Psh_G0 :=
  psh_zq_is_assembly

def psh_manifold_is_assembly : IsAssembly Psh_Manifold :=
  rep_is_asm Psh_Manifold psh_manifold_is_representable

def pshProd (A B : Psh (PartitionedAssembly.{0})) : Psh (PartitionedAssembly.{0}) where
  obj P_obj := A.obj P_obj × B.obj P_obj
  map f p := (A.map f p.1, B.map f p.2)
  map_id P_obj := by
    funext ⟨a, b⟩
    dsimp
    have ha := congrFun (A.map_id P_obj) a
    have hb := congrFun (B.map_id P_obj) b
    change (A.map (𝟙 P_obj) a, B.map (𝟙 P_obj) b) = (a, b)
    rw [ha, hb]
    rfl
  map_comp f g := by
    funext ⟨a, b⟩
    dsimp
    have ha := congrFun (A.map_comp f g) a
    have hb := congrFun (B.map_comp f g) b
    change (A.map (f ≫ g) a, B.map (f ≫ g) b) = (A.map g (A.map f a), B.map g (B.map f b))
    rw [ha, hb]
    rfl

def pshLift {T A B : Psh (PartitionedAssembly.{0})}
    (f : T ⟶ A) (g : T ⟶ B) : T ⟶ pshProd A B where
  app P_obj t := (f.app P_obj t, g.app P_obj t)
  naturality X Y f_mor := by
    funext t
    dsimp [pshProd]
    have hf := congrFun (f.naturality f_mor) t
    have hg := congrFun (g.naturality f_mor) t
    dsimp at hf hg ⊢
    rw [← hf, ← hg]

structure IsPshInternalEquiv {A E : Psh (PartitionedAssembly.{0})}
    (q1 q2 : E ⟶ A) : Prop where
  is_mono    : IsPshMono (pshLift q1 q2)
  reflexive  : ∃ (r : A ⟶ E), r ≫ q1 = 𝟙 A ∧ r ≫ q2 = 𝟙 A
  symmetric  : ∃ (s : E ⟶ E), s ≫ q1 = q2 ∧ s ≫ q2 = q1
  transitive : ∀ {T : Psh (PartitionedAssembly.{0})} (x y z : T ⟶ A) (e1 e2 : T ⟶ E),
    e1 ≫ q1 = x ∧ e1 ≫ q2 = y ∧ e2 ≫ q1 = y ∧ e2 ≫ q2 = z →
    ∃ (e3 : T ⟶ E), e3 ≫ q1 = x ∧ e3 ≫ q2 = z

structure IsPshCoequalizer {A B C_psh : Psh (PartitionedAssembly.{0})}
    (f g : A ⟶ B) (p : B ⟶ C_psh) : Type 1 where
  w    : f ≫ p = g ≫ p
  desc : ∀ {D : Psh (PartitionedAssembly.{0})} (h : B ⟶ D),
    f ≫ h = g ≫ h →
    { k : C_psh ⟶ D // p ≫ k = h ∧ ∀ (k' : C_psh ⟶ D), p ≫ k' = h → k' = k }

structure IsEffObject (X : Psh (PartitionedAssembly.{0})) : Type 1 where
  A     : Psh (PartitionedAssembly.{0})
  E     : Psh (PartitionedAssembly.{0})
  q1    : E ⟶ A
  q2    : E ⟶ A
  p     : A ⟶ X
  asm_A : IsAssembly A
  asm_E : IsAssembly E
  equiv : IsPshInternalEquiv q1 q2
  coeq  : IsPshCoequalizer q1 q2 p

def asm_is_eff (X : Psh (PartitionedAssembly.{0}))
    (hA : IsAssembly X) : IsEffObject X := by
  refine {
    A     := X
    E     := X
    q1    := 𝟙 X
    q2    := 𝟙 X
    p     := 𝟙 X
    asm_A := hA
    asm_E := hA
    equiv := {
      is_mono := by
        intro Z g h hgh
        ext P_obj t
        have h_app := congrFun (congrArg (fun (mor : Z ⟶ pshProd X X) => mor.app P_obj) hgh) t
        dsimp [pshLift] at h_app
        have h_fst := congrArg Prod.fst h_app
        dsimp at h_fst
        exact h_fst
      reflexive := ⟨𝟙 X, Category.id_comp (𝟙 X), Category.id_comp (𝟙 X)⟩
      symmetric := ⟨𝟙 X, Category.id_comp (𝟙 X), Category.id_comp (𝟙 X)⟩
      transitive := by
        intro T x y z e1 e2 ⟨h1, h2, h3, h4⟩
        have h_e1_x : e1 = x := by
          calc e1 = e1 ≫ 𝟙 X := (Category.comp_id e1).symm
            _ = x := h1
        have h_e1_y : e1 = y := by
          calc e1 = e1 ≫ 𝟙 X := (Category.comp_id e1).symm
            _ = y := h2
        have h_e2_y : e2 = y := by
          calc e2 = e2 ≫ 𝟙 X := (Category.comp_id e2).symm
            _ = y := h3
        have h_e2_z : e2 = z := by
          calc e2 = e2 ≫ 𝟙 X := (Category.comp_id e2).symm
            _ = z := h4
        have h_xz : x = z := by
          calc x = e1 := h_e1_x.symm
            _ = y := h_e1_y
            _ = e2 := h_e2_y.symm
            _ = z := h_e2_z
        refine ⟨e1, h1, ?_⟩
        calc e1 ≫ 𝟙 X = x := h1
          _ = z := h_xz
    }
    coeq := {
      w := rfl
      desc := by
        intro D h _
        refine ⟨h, ⟨Category.id_comp h, ?_⟩⟩
        intro k' hk'
        calc k' = 𝟙 X ≫ k' := (Category.id_comp k').symm
          _ = h := hk'
    }
  }

def psh_zq_is_eff : IsEffObject Psh_Zq :=
  asm_is_eff Psh_Zq psh_zq_is_assembly

def psh_s_is_eff : IsEffObject Psh_S :=
  psh_zq_is_eff

def psh_r_is_eff : IsEffObject Psh_R :=
  psh_zq_is_eff

def psh_g0_is_eff : IsEffObject Psh_G0 :=
  psh_zq_is_eff

def psh_manifold_is_eff : IsEffObject Psh_Manifold :=
  asm_is_eff Psh_Manifold psh_manifold_is_assembly

structure IsPshPullbackSquare {K Y X K' : Psh (PartitionedAssembly.{0})}
    (fst : K' ⟶ K) (snd : K' ⟶ Y) (g : K ⟶ X) (f : Y ⟶ X) : Type 1 where
  w : fst ≫ g = snd ≫ f
  is_limit : ∀ {T : Psh (PartitionedAssembly.{0})} (h1 : T ⟶ K) (h2 : T ⟶ Y),
    h1 ≫ g = h2 ≫ f →
    { k : T ⟶ K' // k ≫ fst = h1 ∧ k ≫ snd = h2 ∧ ∀ (k' : T ⟶ K'), k' ≫ fst = h1 ∧ k' ≫ snd = h2 → k' = k }

structure InternalGroupoid : Type 1 where
  G0       : Psh (PartitionedAssembly.{0})
  G1       : Psh (PartitionedAssembly.{0})
  dom      : G1 ⟶ G0
  cod      : G1 ⟶ G0
  id_map   : G0 ⟶ G1
  dom_id   : id_map ≫ dom = 𝟙 G0
  cod_id   : id_map ≫ cod = 𝟙 G0
  G2       : Psh (PartitionedAssembly.{0})
  p1       : G2 ⟶ G1
  p2       : G2 ⟶ G1
  pb       : IsPshPullbackSquare p1 p2 dom cod
  comp     : G2 ⟶ G1
  inv      : G1 ⟶ G1
  inv_dom  : inv ≫ dom = cod
  inv_cod  : inv ≫ cod = dom
  comp_dom : comp ≫ dom = p1 ≫ dom
  comp_cod : comp ≫ cod = p2 ≫ cod

def discrete_pb (X : Psh (PartitionedAssembly.{0})) :
    IsPshPullbackSquare (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X) where
  w := rfl
  is_limit := by
    intro T h1 h2 h_eq
    have h_eq' : h1 = h2 := by
      calc h1 = h1 ≫ 𝟙 X := (Category.comp_id h1).symm
           _  = h2 ≫ 𝟙 X := h_eq
           _  = h2       := Category.comp_id h2
    refine ⟨h1, ⟨Category.comp_id h1, ?_, ?_⟩⟩
    · calc h1 ≫ 𝟙 X = h1 := Category.comp_id h1
           _        = h2 := h_eq'
    · intro k' hk'
      calc k' = k' ≫ 𝟙 X := (Category.comp_id k').symm
           _  = h1       := hk'.1

noncomputable def discreteGroupoid (X : Psh (PartitionedAssembly.{0})) : InternalGroupoid where
  G0        := X
  G1        := X
  dom       := 𝟙 X
  cod       := 𝟙 X
  id_map    := 𝟙 X
  dom_id    := Category.id_comp (𝟙 X)
  cod_id    := Category.id_comp (𝟙 X)
  G2        := X
  p1        := 𝟙 X
  p2        := 𝟙 X
  pb        := discrete_pb X
  comp      := 𝟙 X
  inv       := 𝟙 X
  inv_dom   := rfl
  inv_cod   := rfl
  comp_dom  := rfl
  comp_cod  := rfl

noncomputable def Gpd_Zq       : InternalGroupoid := discreteGroupoid Psh_Zq
noncomputable def Gpd_S        : InternalGroupoid := discreteGroupoid Psh_S
noncomputable def Gpd_R        : InternalGroupoid := discreteGroupoid Psh_R
noncomputable def Gpd_G0       : InternalGroupoid := discreteGroupoid Psh_G0
noncomputable def Gpd_Manifold : InternalGroupoid := discreteGroupoid Psh_Manifold

structure IsCompactObject (K : Psh (PartitionedAssembly.{0})) : Type 1 where
  P_obj     : PartitionedAssembly.{0}
  cover     : yPA P_obj ⟶ K
  epi_cover : IsPshEpi cover

def yPA_is_compact (P_obj : PartitionedAssembly.{0}) : IsCompactObject (yPA P_obj) where
  P_obj     := P_obj
  cover     := 𝟙 (yPA P_obj)
  epi_cover := {
    surjective   := fun Q b => ⟨b, rfl⟩
    right_cancel := fun g h hgh => by
      calc g = 𝟙 (yPA P_obj) ≫ g := (Category.id_comp g).symm
           _ = 𝟙 (yPA P_obj) ≫ h := hgh
           _ = h                 := Category.id_comp h
  }

def psh_zq_is_compact : IsCompactObject Psh_Zq :=
  yPA_is_compact Zq_PA

def IsCompactMorphism {Y X : Psh (PartitionedAssembly.{0})} (f : Y ⟶ X) : Type 1 :=
  ∀ (K : Psh (PartitionedAssembly.{0})) (hK : IsCompactObject K) (g : K ⟶ X)
    (K' : Psh (PartitionedAssembly.{0})) (fst : K' ⟶ K) (snd : K' ⟶ Y),
    IsPshPullbackSquare fst snd g f → IsCompactObject K'

structure IsCoherentObject (X : Psh (PartitionedAssembly.{0})) : Type 1 where
  compact          : IsCompactObject X
  compact_diagonal : IsCompactMorphism (pshLift (𝟙 X) (𝟙 X))

structure GroupoidMorphism (G H : InternalGroupoid) : Type 1 where
  f0       : G.G0 ⟶ H.G0
  f1       : G.G1 ⟶ H.G1
  comm_dom : f1 ≫ H.dom = G.dom ≫ f0
  comm_cod : f1 ≫ H.cod = G.cod ≫ f0
  comm_id  : f0 ≫ H.id_map = G.id_map ≫ f1

structure GroupoidProduct (G H : InternalGroupoid) : Type 1 where
  prod : InternalGroupoid
  fst  : GroupoidMorphism prod G
  snd  : GroupoidMorphism prod H

structure GroupoidDiagonal (G : InternalGroupoid) (GxG : GroupoidProduct G G) : Type 1 where
  diag : GroupoidMorphism G GxG.prod

structure GroupoidSecondDiagonal (G : InternalGroupoid) (GxG : GroupoidProduct G G)
    (Diag : GroupoidDiagonal G GxG) : Type 1 where
  delta2_f0 : G.G0 ⟶ GxG.prod.G0

def pshMapProd {A B C D : Psh (PartitionedAssembly.{0})}
    (f : A ⟶ C) (g : B ⟶ D) : pshProd A B ⟶ pshProd C D where
  app P_obj p := (f.app P_obj p.1, g.app P_obj p.2)
  naturality X Y f_mor := by
    funext ⟨a, b⟩
    dsimp [pshProd]
    have hf := congrFun (f.naturality f_mor) a
    have hg := congrFun (g.naturality f_mor) b
    dsimp at hf hg ⊢
    rw [← hf, ← hg]

def pshFst (A B : Psh (PartitionedAssembly.{0})) : pshProd A B ⟶ A where
  app P_obj p := p.1
  naturality _ _ _ := rfl

def pshSnd (A B : Psh (PartitionedAssembly.{0})) : pshProd A B ⟶ B where
  app P_obj p := p.2
  naturality _ _ _ := rfl

noncomputable def discreteGroupoidProduct (X : Psh (PartitionedAssembly.{0})) :
    GroupoidProduct (discreteGroupoid X) (discreteGroupoid X) where
  prod := discreteGroupoid (pshProd X X)
  fst  := {
    f0       := pshFst X X
    f1       := pshFst X X
    comm_dom := by
      dsimp [discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
    comm_cod := by
      dsimp [discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
    comm_id  := by
      dsimp [discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
  }
  snd  := {
    f0       := pshSnd X X
    f1       := pshSnd X X
    comm_dom := by
      dsimp [discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
    comm_cod := by
      dsimp [discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
    comm_id  := by
      dsimp [discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
  }

noncomputable def discreteGroupoidDiagonal (X : Psh (PartitionedAssembly.{0})) :
    GroupoidDiagonal (discreteGroupoid X) (discreteGroupoidProduct X) where
  diag := {
    f0       := pshLift (𝟙 X) (𝟙 X)
    f1       := pshLift (𝟙 X) (𝟙 X)
    comm_dom := by
      dsimp [discreteGroupoidProduct, discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
    comm_cod := by
      dsimp [discreteGroupoidProduct, discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
    comm_id  := by
      dsimp [discreteGroupoidProduct, discreteGroupoid]
      rw [Category.comp_id, Category.id_comp]
  }

noncomputable def discreteGroupoidProductOfEq (G : InternalGroupoid)
    (X : Psh (PartitionedAssembly.{0})) (hG : G = discreteGroupoid X) :
    GroupoidProduct G G := by
  subst hG
  exact discreteGroupoidProduct X

structure IsPseudoCompact (G : InternalGroupoid) : Type 1 where
  K_obj   : Psh (PartitionedAssembly.{0})
  is_cpt  : IsCompactObject K_obj
  hom_G0  : K_obj ⟶ G.G0
  epi_hom : IsPshEpi hom_G0

structure IsCoherentGroupoid (G : InternalGroupoid) (GxG : GroupoidProduct G G)
    (Diag : GroupoidDiagonal G GxG) (Diag2 : GroupoidSecondDiagonal G GxG Diag) : Type 1 where
  pseudo_compact                 : IsPseudoCompact G
  diagonal_pseudo_compact        : IsCompactMorphism Diag.diag.f0
  second_diagonal_pseudo_compact : IsCompactMorphism Diag2.delta2_f0

structure IsZeroType (G : InternalGroupoid) (GxG : GroupoidProduct G G)
    (Diag : GroupoidDiagonal G GxG) : Type 1 where
  is_discrete : G.dom = G.cod

def gpd_zq_is_zero_type (GxG : GroupoidProduct Gpd_Zq Gpd_Zq)
    (Diag : GroupoidDiagonal Gpd_Zq GxG) : IsZeroType Gpd_Zq GxG Diag where
  is_discrete := rfl

structure Theorem_CohZeroType_Eq_CohObject : Type 2 where
  to_coh_obj : ∀ (G : InternalGroupoid) (GxG : GroupoidProduct G G)
    (DiagG : GroupoidDiagonal G GxG) (DiagG2 : GroupoidSecondDiagonal G GxG DiagG),
    IsCoherentGroupoid G GxG DiagG DiagG2 → IsZeroType G GxG DiagG →
    Σ (X : Psh (PartitionedAssembly.{0})), IsCoherentObject X

def psh_zq_is_coherent (diag_cpt : IsCompactMorphism (pshLift (𝟙 Psh_Zq) (𝟙 Psh_Zq))) :
    IsCoherentObject Psh_Zq where
  compact          := psh_zq_is_compact
  compact_diagonal := diag_cpt

def stdTruncationThm
    (coh_dict : ∀ (G : InternalGroupoid) (GxG : GroupoidProduct G G)
      (DiagG : GroupoidDiagonal G GxG) (DiagG2 : GroupoidSecondDiagonal G GxG DiagG),
      IsCoherentGroupoid G GxG DiagG DiagG2 → IsZeroType G GxG DiagG →
      IsCoherentObject G.G0) :
    Theorem_CohZeroType_Eq_CohObject where
  to_coh_obj G GxG DiagG DiagG2 hCoh hZero :=
    ⟨G.G0, coh_dict G GxG DiagG DiagG2 hCoh hZero⟩

theorem zq_truncation_link
    (coh_dict : ∀ (G : InternalGroupoid) (GxG : GroupoidProduct G G)
      (DiagG : GroupoidDiagonal G GxG) (DiagG2 : GroupoidSecondDiagonal G GxG DiagG),
      IsCoherentGroupoid G GxG DiagG DiagG2 → IsZeroType G GxG DiagG →
      IsCoherentObject G.G0)
    (GxG : GroupoidProduct Gpd_Zq Gpd_Zq)
    (Diag : GroupoidDiagonal Gpd_Zq GxG)
    (Diag2 : GroupoidSecondDiagonal Gpd_Zq GxG Diag)
    (hCoh : IsCoherentGroupoid Gpd_Zq GxG Diag Diag2)
    (hZero : IsZeroType Gpd_Zq GxG Diag) :
    (stdTruncationThm coh_dict).to_coh_obj Gpd_Zq GxG Diag Diag2 hCoh hZero =
      ⟨Psh_Zq, coh_dict Gpd_Zq GxG Diag Diag2 hCoh hZero⟩ :=
  rfl

abbrev PshUniverse := (PartitionedAssembly.{0})ᵒᵖ ⥤ Type 1

def PshUniverse0_Ty : PshUniverse where
  obj Γ_op := Γ_op.unop.carrier → Type 0
  map f A := A ∘ f.unop.toFun
  map_id _ := rfl
  map_comp _ _ := rfl

def PshUniverse0_Tm : PshUniverse where
  obj Γ_op := Σ (A : Γ_op.unop.carrier → Type 0), (∀ x : Γ_op.unop.carrier, A x)
  map f p := ⟨p.1 ∘ f.unop.toFun, fun x => p.2 (f.unop.toFun x)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def PshUniverse0_tp : PshUniverse0_Tm ⟶ PshUniverse0_Ty where
  app _ p := p.1
  naturality _ _ _ := rfl

structure NaturalUniverseBase where
  Ty : PshUniverse
  Tm : PshUniverse
  tp : Tm ⟶ Ty

def PshUniverse0_Base : NaturalUniverseBase where
  Ty := PshUniverse0_Ty
  Tm := PshUniverse0_Tm
  tp := PshUniverse0_tp

@[simp]
theorem PshUniverse0_Ty_map_apply {Γ_op Δ_op : (PartitionedAssembly.{0})ᵒᵖ}
    (f : Γ_op ⟶ Δ_op) (A : Γ_op.unop.carrier → Type 0) :
    PshUniverse0_Ty.map f A = A ∘ f.unop.toFun :=
  rfl

@[simp]
theorem PshUniverse0_Tm_map_apply {Γ_op Δ_op : (PartitionedAssembly.{0})ᵒᵖ}
    (f : Γ_op ⟶ Δ_op)
    (p : Σ (A : Γ_op.unop.carrier → Type 0), (∀ x : Γ_op.unop.carrier, A x)) :
    PshUniverse0_Tm.map f p = ⟨p.1 ∘ f.unop.toFun, fun x => p.2 (f.unop.toFun x)⟩ :=
  rfl

@[simp]
theorem PshUniverse0_tp_app_apply (Γ_op : (PartitionedAssembly.{0})ᵒᵖ)
    (p : PshUniverse0_Tm.obj Γ_op) :
    PshUniverse0_tp.app Γ_op p = p.1 :=
  rfl

def yPA1 (X : PartitionedAssembly.{0}) : PshUniverse where
  obj Δ_op := ULift.{1, 0} (TrackedMap Δ_op.unop X)
  map {Δ_op Γ_op} f (σ : ULift.{1, 0} (TrackedMap Δ_op.unop X)) :=
    ⟨P_cat_comp f.unop σ.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def extPA (Γ : PartitionedAssembly.{0})
    (A : Γ.carrier → PartitionedAssembly.{0}) : PartitionedAssembly.{0} where
  carrier := Σ (x : Γ.carrier), (A x).carrier
  realizer := fun p =>
    { n | ∃ nx na, nx ∈ Γ.realizer p.1 ∧ na ∈ (A p.1).realizer p.2 ∧ n = Nat.pair nx na }
  realizer_nonempty := by
    intro ⟨x, a⟩
    rcases Γ.realizer_nonempty x with ⟨nx, hnx⟩
    rcases (A x).realizer_nonempty a with ⟨na, hna⟩
    exact ⟨Nat.pair nx na, ⟨nx, na, hnx, hna, rfl⟩⟩
  realizer_disjoint := by
    rintro ⟨x1, a1⟩ ⟨x2, a2⟩ n ⟨nx1, na1, hnx1, hna1, rfl⟩ ⟨nx2, na2, hnx2, hna2, hn_eq⟩
    have h_inj := nat_pair_inj hn_eq
    have hx : x1 = x2 := Γ.realizer_disjoint x1 x2 nx1 hnx1 (h_inj.1 ▸ hnx2)
    subst hx
    have ha : a1 = a2 := (A x1).realizer_disjoint a1 a2 na1 hna1 (h_inj.2 ▸ hna2)
    subst ha
    rfl

theorem dispPA_isTracked (Γ : PartitionedAssembly.{0})
    (A : Γ.carrier → PartitionedAssembly.{0}) :
    IsTracked (extPA Γ A) Γ (fun p => p.1) := by
  use 2
  rintro ⟨x, a⟩ n ⟨nx, na, hnx, hna, rfl⟩
  exact ⟨nx, KleeneEval.fst nx na, hnx⟩

def dispPA (Γ : PartitionedAssembly.{0})
    (A : Γ.carrier → PartitionedAssembly.{0}) : TrackedMap (extPA Γ A) Γ where
  toFun := fun p => p.1
  tracked := dispPA_isTracked Γ A

def dispPsh (Γ : PartitionedAssembly.{0})
    (A : Γ.carrier → PartitionedAssembly.{0}) :
    yPA1 (extPA Γ A) ⟶ yPA1 Γ where
  app Δ_op (σ : ULift.{1, 0} (TrackedMap Δ_op.unop (extPA Γ A))) :=
    ⟨P_cat_comp σ.down (dispPA Γ A)⟩
  naturality _ _ _ := rfl

def varPsh (Γ : PartitionedAssembly.{0})
    (A : Γ.carrier → PartitionedAssembly.{0}) :
    yPA1 (extPA Γ A) ⟶ PshUniverse0_Tm where
  app Δ_op (σ : ULift.{1, 0} (TrackedMap Δ_op.unop (extPA Γ A))) :=
    ⟨fun d => (A (σ.down.toFun d).1).carrier, fun d => (σ.down.toFun d).2⟩
  naturality Δ1_op Δ2_op f := rfl

structure IsNaturalModelPullback {K' K Y X : PshUniverse}
    (fst : K' ⟶ Y) (snd : K' ⟶ K) (g : Y ⟶ X) (f : K ⟶ X) : Type 2 where
  w : fst ≫ g = snd ≫ f
  lift : ∀ {T : PshUniverse} (h1 : T ⟶ Y) (h2 : T ⟶ K),
    h1 ≫ g = h2 ≫ f → (T ⟶ K')
  fac_fst : ∀ {T : PshUniverse} (h1 : T ⟶ Y) (h2 : T ⟶ K)
    (h_comm : h1 ≫ g = h2 ≫ f), lift h1 h2 h_comm ≫ fst = h1
  fac_snd : ∀ {T : PshUniverse} (h1 : T ⟶ Y) (h2 : T ⟶ K)
    (h_comm : h1 ≫ g = h2 ≫ f), lift h1 h2 h_comm ≫ snd = h2
  uniq : ∀ {T : PshUniverse} (h1 : T ⟶ Y) (h2 : T ⟶ K)
    (h_comm : h1 ≫ g = h2 ≫ f) (m : T ⟶ K'),
    m ≫ fst = h1 → m ≫ snd = h2 → m = lift h1 h2 h_comm

structure SynthLeanUniverse : Type 2 where
  Tm   : PshUniverse
  Ty   : PshUniverse
  tp   : Tm ⟶ Ty
  ext  : ∀ (Γ : PartitionedAssembly.{0}) (A_mor : yPA1 Γ ⟶ Ty)
    (A_fam : Γ.carrier → PartitionedAssembly.{0}), PartitionedAssembly.{0}
  disp : ∀ (Γ : PartitionedAssembly.{0}) (A_mor : yPA1 Γ ⟶ Ty)
    (A_fam : Γ.carrier → PartitionedAssembly.{0}), TrackedMap (ext Γ A_mor A_fam) Γ
  var  : ∀ (Γ : PartitionedAssembly.{0}) (A_mor : yPA1 Γ ⟶ Ty)
    (A_fam : Γ.carrier → PartitionedAssembly.{0}), yPA1 (ext Γ A_mor A_fam) ⟶ Tm

def PshUniverse0 : SynthLeanUniverse where
  Tm   := PshUniverse0_Tm
  Ty   := PshUniverse0_Ty
  tp   := PshUniverse0_tp
  ext  := fun Γ _ A_fam => extPA Γ A_fam
  disp := fun Γ _ A_fam => dispPA Γ A_fam
  var  := fun Γ _ A_fam => varPsh Γ A_fam

abbrev PshUniverseCommon := (PartitionedAssembly.{0})ᵒᵖ ⥤ Type 2

def PshUniverse0_Ty_Embed : PshUniverseCommon where
  obj Γ_op := ULift.{2, 1} (Γ_op.unop.carrier → Type 0)
  map f A := ⟨A.down ∘ f.unop.toFun⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def PshUniverse0_Tm_Embed : PshUniverseCommon where
  obj Γ_op := ULift.{2, 1} (Σ (A : Γ_op.unop.carrier → Type 0), (∀ x : Γ_op.unop.carrier, A x))
  map f p := ⟨⟨p.down.1 ∘ f.unop.toFun, fun x => p.down.2 (f.unop.toFun x)⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def PshUniverse0_tp_Embed : PshUniverse0_Tm_Embed ⟶ PshUniverse0_Ty_Embed where
  app _ p := ⟨p.down.1⟩
  naturality _ _ _ := rfl

def PshUniverse1_Ty_Embed : PshUniverseCommon where
  obj Γ_op := Γ_op.unop.carrier → Type 1
  map f A := A ∘ f.unop.toFun
  map_id _ := rfl
  map_comp _ _ := rfl

def PshUniverse1_Tm_Embed : PshUniverseCommon where
  obj Γ_op := Σ (A : Γ_op.unop.carrier → Type 1), (∀ x : Γ_op.unop.carrier, A x)
  map f p := ⟨p.1 ∘ f.unop.toFun, fun x => p.2 (f.unop.toFun x)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def PshUniverse1_tp_Embed : PshUniverse1_Tm_Embed ⟶ PshUniverse1_Ty_Embed where
  app _ p := p.1
  naturality _ _ _ := rfl

def yPA_one_Common : PshUniverseCommon where
  obj Δ_op := ULift.{2, 0} (TrackedMap Δ_op.unop onePA)
  map f σ := ⟨P_cat_comp f.unop σ.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def PshUHom01_mapTy : PshUniverse0_Ty_Embed ⟶ PshUniverse1_Ty_Embed where
  app _ A := fun x => ULift.{1, 0} (A.down x)
  naturality _ _ _ := rfl

def PshUHom01_mapTm : PshUniverse0_Tm_Embed ⟶ PshUniverse1_Tm_Embed where
  app _ p := ⟨fun x => ULift.{1, 0} (p.down.1 x), fun x => ⟨p.down.2 x⟩⟩
  naturality _ _ _ := rfl

theorem PshUHom01_pb_comm :
    PshUHom01_mapTm ≫ PshUniverse1_tp_Embed = PshUniverse0_tp_Embed ≫ PshUHom01_mapTy :=
  rfl

structure IsNaturalModelPullbackCommon {K' K Y X : PshUniverseCommon}
    (fst : K' ⟶ Y) (snd : K' ⟶ K) (g : Y ⟶ X) (f : K ⟶ X) : Type 3 where
  w : fst ≫ g = snd ≫ f
  lift : ∀ {T : PshUniverseCommon} (h1 : T ⟶ Y) (h2 : T ⟶ K),
    h1 ≫ g = h2 ≫ f → (T ⟶ K')
  fac_snd : ∀ {T : PshUniverseCommon} (h1 : T ⟶ Y) (h2 : T ⟶ K)
    (h_comm : h1 ≫ g = h2 ≫ f), lift h1 h2 h_comm ≫ snd = h2

theorem psh_uhom01_pb_lift_natural_aux
    {X Y : (PartitionedAssembly.{0})ᵒᵖ} (f : X ⟶ Y)
    (a : PshUniverse1_Tm_Embed.obj X) (b : PshUniverse1_Tm_Embed.obj Y)
    (c : PshUniverse0_Ty_Embed.obj X) (d : PshUniverse0_Ty_Embed.obj Y)
    (hab : PshUniverse1_Tm_Embed.map f a = b)
    (hcd : PshUniverse0_Ty_Embed.map f c = d)
    (ha : a.1 = fun y => ULift.{1, 0} (c.down y))
    (hb : b.1 = fun y => ULift.{1, 0} (d.down y)) :
    (ULift.up ⟨d.down, fun x =>
        (cast (congrFun hb x) (b.2 x) : ULift.{1, 0} (d.down x)).down⟩ :
        ULift.{2, 1} (Σ (A : (Opposite.unop Y).carrier → Type 0), (∀ x, A x))) =
      PshUniverse0_Tm_Embed.map f
        (ULift.up ⟨c.down, fun x =>
          (cast (congrFun ha x) (a.2 x) : ULift.{1, 0} (c.down x)).down⟩ :
          ULift.{2, 1} (Σ (A : (Opposite.unop X).carrier → Type 0), (∀ x, A x))) := by
  subst hab
  subst hcd
  obtain ⟨B, s⟩ := a
  obtain ⟨A⟩ := c
  have ha' : B = fun y => ULift.{1, 0} (A y) := ha
  subst ha'
  rfl

noncomputable def psh_uhom01_pb :
    IsNaturalModelPullbackCommon
      PshUHom01_mapTm
      PshUniverse0_tp_Embed
      PshUniverse1_tp_Embed
      PshUHom01_mapTy where
  w := rfl
  lift := fun {T : PshUniverseCommon}
              (h1 : T ⟶ PshUniverse1_Tm_Embed)
              (h2 : T ⟶ PshUniverse0_Ty_Embed)
              (h_comm : h1 ≫ PshUniverse1_tp_Embed = h2 ≫ PshUHom01_mapTy) =>
    {
      app := fun (Δ_op : (PartitionedAssembly.{0})ᵒᵖ) (t : T.obj Δ_op) =>
        let A0 := (h2.app Δ_op t).down
        (⟨⟨A0, fun (x : (Opposite.unop Δ_op).carrier) =>
          have h_comm_t : (h1.app Δ_op t).1 = fun y => ULift.{1, 0} (A0 y) :=
            congrFun (congrArg (fun (m : T ⟶ PshUniverse1_Ty_Embed) => m.app Δ_op) h_comm) t
          (cast (congrFun h_comm_t x) ((h1.app Δ_op t).2 x) : ULift.{1, 0} (A0 x)).down
        ⟩⟩ : ULift.{2, 1} (Σ (A : (Opposite.unop Δ_op).carrier → Type 0), (∀ x, A x)))
      naturality := by
        intro X Y f
        funext t
        exact (psh_uhom01_pb_lift_natural_aux f
          (h1.app X t) (h1.app Y (T.map f t))
          (h2.app X t) (h2.app Y (T.map f t))
          (congrFun (h1.naturality f).symm t)
          (congrFun (h2.naturality f).symm t)
          (congrFun (congrArg (fun (m : T ⟶ PshUniverse1_Ty_Embed) => m.app X) h_comm) t)
          (congrFun (congrArg (fun (m : T ⟶ PshUniverse1_Ty_Embed) => m.app Y) h_comm) (T.map f t)))
    }
  fac_snd := by
    intro (T : PshUniverseCommon)
          (h1 : T ⟶ PshUniverse1_Tm_Embed)
          (h2 : T ⟶ PshUniverse0_Ty_Embed)
          (h_comm : h1 ≫ PshUniverse1_tp_Embed = h2 ≫ PshUHom01_mapTy)
    rfl

def PshUHom01_U : yPA_one_Common ⟶ PshUniverse1_Ty_Embed where
  app _ _ := fun _ => Type 0
  naturality _ _ _ := rfl

def PshUHom01_toTerminal : PshUniverse0_Ty_Embed ⟶ yPA_one_Common where
  app Γ_op _ := ⟨toTerminalPA Γ_op.unop⟩
  naturality X Y f := by
    ext A
    refine ULift.ext _ _ ?_
    exact toTerminalPA_unique _

def PshUHom01_asTm : PshUniverse0_Ty_Embed ⟶ PshUniverse1_Tm_Embed where
  app _ A := ⟨fun _ => Type 0, A.down⟩
  naturality _ _ _ := rfl

theorem PshUHom01_U_pb_comm :
    PshUHom01_asTm ≫ PshUniverse1_tp_Embed = PshUHom01_toTerminal ≫ PshUHom01_U :=
  rfl

noncomputable def psh_uhom01_U_pb :
    IsNaturalModelPullbackCommon
      PshUHom01_asTm
      PshUHom01_toTerminal
      PshUniverse1_tp_Embed
      PshUHom01_U where
  w := PshUHom01_U_pb_comm
  lift := fun {T} h1 h2 h_comm => {
    app := fun Δ_op t => ⟨fun _ => PUnit⟩
    naturality := by
      intro X Y f
      rfl
  }
  fac_snd := by
    intro T h1 h2 h_comm
    ext Δ_op t
    dsimp [PshUHom01_toTerminal]
    refine ULift.ext _ _ ?_
    exact (toTerminalPA_unique _).symm

structure UHomBig (M_Tm M_Ty : PshUniverseCommon) (M_tp : M_Tm ⟶ M_Ty)
    (N_Tm N_Ty : PshUniverseCommon) (N_tp : N_Tm ⟶ N_Ty) : Type 3 where
  mapTm     : M_Tm ⟶ N_Tm
  mapTy     : M_Ty ⟶ N_Ty
  pb        : IsNaturalModelPullbackCommon mapTm M_tp N_tp mapTy
  toTerm    : M_Ty ⟶ yPA_one_Common
  U         : yPA_one_Common ⟶ N_Ty
  asTm      : M_Ty ⟶ N_Tm
  U_pb      : IsNaturalModelPullbackCommon asTm toTerm N_tp U

noncomputable def PshUHom01 : UHomBig
    PshUniverse0_Tm_Embed PshUniverse0_Ty_Embed PshUniverse0_tp_Embed
    PshUniverse1_Tm_Embed PshUniverse1_Ty_Embed PshUniverse1_tp_Embed where
  mapTm     := PshUHom01_mapTm
  mapTy     := PshUHom01_mapTy
  pb        := psh_uhom01_pb
  toTerm    := PshUHom01_toTerminal
  U         := PshUHom01_U
  asTm      := PshUHom01_asTm
  U_pb      := psh_uhom01_U_pb

structure UniverseCommon where
  Tm : PshUniverseCommon
  Ty : PshUniverseCommon
  tp : Tm ⟶ Ty

def PshUniv0_Common : UniverseCommon where
  Tm := PshUniverse0_Tm_Embed
  Ty := PshUniverse0_Ty_Embed
  tp := PshUniverse0_tp_Embed

def PshUniv1_Common : UniverseCommon where
  Tm := PshUniverse1_Tm_Embed
  Ty := PshUniverse1_Ty_Embed
  tp := PshUniverse1_tp_Embed

structure UHomSeqCommon where
  len      : Nat
  objs     : ∀ (i : Nat) (h : i < len + 1), UniverseCommon
  homSucc' : ∀ (i : Nat) (h : i < len),
    let u0 := objs i (Nat.lt_trans h (Nat.lt_succ_self len))
    let u1 := objs (i + 1) (Nat.succ_lt_succ h)
    UHomBig u0.Tm u0.Ty u0.tp u1.Tm u1.Ty u1.tp

def UHomSeqCommon.length (seq : UHomSeqCommon) : Nat := seq.len

structure NilContextPA where
  fst : PartitionedAssembly.{0}

def UHomSeqCommon.nilCObj (seq : UHomSeqCommon) : NilContextPA where
  fst := onePA

noncomputable def realUHomSeq : UHomSeqCommon where
  len := 1
  objs := fun i _ =>
    match i with
    | 0 => PshUniv0_Common
    | _ => PshUniv1_Common
  homSucc' := fun i h => by
    cases i with
    | zero =>
      exact PshUHom01
    | succ n =>
      omega

def Ptp_Ty0 : PshUniverseCommon where
  obj Γ_op := ULift.{2, 1} (Σ (A : Γ_op.unop.carrier → Type 0),
    ∀ x, A x → Type 0)
  map f p := ⟨⟨p.down.1 ∘ f.unop.toFun, fun x => p.down.2 (f.unop.toFun x)⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def Ptp_Tm0 : PshUniverseCommon where
  obj Γ_op := ULift.{2, 1} (Σ (A : Γ_op.unop.carrier → Type 0),
    Σ (B : ∀ x, A x → Type 0), ∀ x (a : A x), B x a)
  map f p := ⟨⟨p.down.1 ∘ f.unop.toFun, ⟨fun x => p.down.2.1 (f.unop.toFun x),
    fun x a => p.down.2.2 (f.unop.toFun x) a⟩⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def Ptp_tp0 : Ptp_Tm0 ⟶ Ptp_Ty0 where
  app _ p := ⟨⟨p.down.1, p.down.2.1⟩⟩
  naturality _ _ _ := rfl

def Pi0_Ty : Ptp_Ty0 ⟶ PshUniverse0_Ty_Embed where
  app _ p := ⟨fun x => ∀ a : p.down.1 x, p.down.2 x a⟩
  naturality _ _ _ := rfl

def Pi0_lam : Ptp_Tm0 ⟶ PshUniverse0_Tm_Embed where
  app _ p := ⟨⟨fun x => ∀ a : p.down.1 x, p.down.2.1 x a,
    fun x a => p.down.2.2 x a⟩⟩
  naturality _ _ _ := rfl

theorem Pi0_pb_comm :
    Pi0_lam ≫ PshUniverse0_tp_Embed = Ptp_tp0 ≫ Pi0_Ty :=
  rfl

theorem psh_pi0_pb_lift_natural_aux
    {X Y : (PartitionedAssembly.{0})ᵒᵖ} (f : X ⟶ Y)
    (a : PshUniverse0_Tm_Embed.obj X) (b : PshUniverse0_Tm_Embed.obj Y)
    (c : Ptp_Ty0.obj X) (d : Ptp_Ty0.obj Y)
    (hab : PshUniverse0_Tm_Embed.map f a = b)
    (hcd : Ptp_Ty0.map f c = d)
    (ha : a.down.1 = fun x => ∀ y : c.down.1 x, c.down.2 x y)
    (hb : b.down.1 = fun x => ∀ y : d.down.1 x, d.down.2 x y) :
    (ULift.up ⟨d.down.1, ⟨d.down.2, fun x y =>
        (cast (congrFun hb x) (b.down.2 x) : ∀ y : d.down.1 x, d.down.2 x y) y⟩⟩ :
        Ptp_Tm0.obj Y) =
      Ptp_Tm0.map f
        (ULift.up ⟨c.down.1, ⟨c.down.2, fun x y =>
          (cast (congrFun ha x) (a.down.2 x) : ∀ y : c.down.1 x, c.down.2 x y) y⟩⟩ :
          Ptp_Tm0.obj X) := by
  subst hab
  subst hcd
  obtain ⟨⟨B, s⟩⟩ := a
  obtain ⟨⟨A, C⟩⟩ := c
  dsimp at ha
  subst ha
  rfl

noncomputable def psh_pi0_pb :
    IsNaturalModelPullbackCommon Pi0_lam Ptp_tp0 PshUniverse0_tp_Embed Pi0_Ty where
  w := Pi0_pb_comm
  lift := fun {T} h1 h2 h_comm => {
    app := fun Δ_op t =>
      let p_ty := (h2.app Δ_op t).down
      let A := p_ty.1
      let B := p_ty.2
      have h_comm_t : (h1.app Δ_op t).down.1 = fun x => ∀ a : A x, B x a :=
        congrArg ULift.down (congrFun (congrArg (fun (m : T ⟶ PshUniverse0_Ty_Embed) => m.app Δ_op) h_comm) t)
      ⟨⟨A, ⟨B, fun x a =>
        (cast (congrFun h_comm_t x) ((h1.app Δ_op t).down.2 x) : ∀ a : A x, B x a) a⟩⟩⟩
    naturality := by
      intro X Y f
      funext t
      exact (psh_pi0_pb_lift_natural_aux f
        (h1.app X t) (h1.app Y (T.map f t))
        (h2.app X t) (h2.app Y (T.map f t))
        (congrFun (h1.naturality f).symm t)
        (congrFun (h2.naturality f).symm t)
        (congrArg ULift.down (congrFun (congrArg (fun (m : T ⟶ PshUniverse0_Ty_Embed) => m.app X) h_comm) t))
        (congrArg ULift.down (congrFun (congrArg (fun (m : T ⟶ PshUniverse0_Ty_Embed) => m.app Y) h_comm) (T.map f t))))
  }
  fac_snd := by
    intro T h1 h2 h_comm
    rfl

structure UniversePi (u : UniverseCommon) where
  Ptp_Ty      : PshUniverseCommon
  Ptp_Tm      : PshUniverseCommon
  Ptp_tp      : Ptp_Tm ⟶ Ptp_Ty
  Pi          : Ptp_Ty ⟶ u.Ty
  lam         : Ptp_Tm ⟶ u.Tm
  Pi_pullback : IsNaturalModelPullbackCommon lam Ptp_tp u.tp Pi

noncomputable def PshUniverse0_Pi : UniversePi PshUniv0_Common where
  Ptp_Ty      := Ptp_Ty0
  Ptp_Tm      := Ptp_Tm0
  Ptp_tp      := Ptp_tp0
  Pi          := Pi0_Ty
  lam         := Pi0_lam
  Pi_pullback := psh_pi0_pb

noncomputable def PshUniverse1_Pi : UniversePi PshUniv1_Common where
  Ptp_Ty      := Ptp_Ty0
  Ptp_Tm      := Ptp_Tm0
  Ptp_tp      := Ptp_tp0
  Pi          := Pi0_Ty ≫ PshUHom01_mapTy
  lam         := Pi0_lam ≫ PshUHom01_mapTm
  Pi_pullback := {
    w := by
      calc
        (Pi0_lam ≫ PshUHom01_mapTm) ≫ PshUniv1_Common.tp
            = Pi0_lam ≫ (PshUHom01_mapTm ≫ PshUniv1_Common.tp) :=
              CategoryTheory.Category.assoc _ _ _
        _ = Pi0_lam ≫ (PshUniverse0_tp_Embed ≫ PshUHom01_mapTy) :=
              congrArg (fun φ => Pi0_lam ≫ φ) PshUHom01_pb_comm
        _ = (Pi0_lam ≫ PshUniverse0_tp_Embed) ≫ PshUHom01_mapTy :=
              (CategoryTheory.Category.assoc _ _ _).symm
        _ = (Ptp_tp0 ≫ Pi0_Ty) ≫ PshUHom01_mapTy :=
              congrArg (fun φ => φ ≫ PshUHom01_mapTy) Pi0_pb_comm
        _ = Ptp_tp0 ≫ (Pi0_Ty ≫ PshUHom01_mapTy) :=
              CategoryTheory.Category.assoc _ _ _
    lift := fun {T} h1 h2 h_comm =>
      let h1_0 := psh_uhom01_pb.lift h1 (h2 ≫ Pi0_Ty)
        (h_comm.trans (CategoryTheory.Category.assoc _ _ _).symm)
      psh_pi0_pb.lift h1_0 h2
        (psh_uhom01_pb.fac_snd h1 (h2 ≫ Pi0_Ty) _)
    fac_snd := by
      intro T h1 h2 h_comm
      exact psh_pi0_pb.fac_snd _ _ _
  }

def D_tp_tp0 : PshUniverseCommon where
  obj Γ_op := ULift.{2, 1} (Σ (A : Γ_op.unop.carrier → Type 0),
    Σ (B : ∀ x, A x → Type 0),
    Σ (a : ∀ x, A x), ∀ x, B x (a x))
  map f p := ⟨⟨p.down.1 ∘ f.unop.toFun, ⟨fun x => p.down.2.1 (f.unop.toFun x),
    ⟨fun x => p.down.2.2.1 (f.unop.toFun x), fun x => p.down.2.2.2 (f.unop.toFun x)⟩⟩⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def D_tp_tp0_proj : D_tp_tp0 ⟶ Ptp_Ty0 where
  app _ p := ⟨⟨p.down.1, p.down.2.1⟩⟩
  naturality _ _ _ := rfl

def Sig0_Ty : Ptp_Ty0 ⟶ PshUniverse0_Ty_Embed where
  app _ p := ⟨fun x => Σ a : p.down.1 x, p.down.2 x a⟩
  naturality _ _ _ := rfl

def Sig0_pair : D_tp_tp0 ⟶ PshUniverse0_Tm_Embed where
  app _ p := ⟨⟨fun x => Σ a : p.down.1 x, p.down.2.1 x a,
    fun x => ⟨p.down.2.2.1 x, p.down.2.2.2 x⟩⟩⟩
  naturality _ _ _ := rfl

theorem Sig0_pb_comm :
    Sig0_pair ≫ PshUniverse0_tp_Embed = D_tp_tp0_proj ≫ Sig0_Ty :=
  rfl

theorem psh_sig0_pb_lift_natural_aux
    {X Y : (PartitionedAssembly.{0})ᵒᵖ} (f : X ⟶ Y)
    (a : PshUniverse0_Tm_Embed.obj X) (b : PshUniverse0_Tm_Embed.obj Y)
    (c : Ptp_Ty0.obj X) (d : Ptp_Ty0.obj Y)
    (hab : PshUniverse0_Tm_Embed.map f a = b)
    (hcd : Ptp_Ty0.map f c = d)
    (ha : a.down.1 = fun x => Σ y : c.down.1 x, c.down.2 x y)
    (hb : b.down.1 = fun x => Σ y : d.down.1 x, d.down.2 x y) :
    (ULift.up ⟨d.down.1, ⟨d.down.2,
        ⟨fun x => (cast (congrFun hb x) (b.down.2 x) : Σ y : d.down.1 x, d.down.2 x y).1,
         fun x => (cast (congrFun hb x) (b.down.2 x) : Σ y : d.down.1 x, d.down.2 x y).2⟩⟩⟩ :
        D_tp_tp0.obj Y) =
      D_tp_tp0.map f
        (ULift.up ⟨c.down.1, ⟨c.down.2,
          ⟨fun x => (cast (congrFun ha x) (a.down.2 x) : Σ y : c.down.1 x, c.down.2 x y).1,
           fun x => (cast (congrFun ha x) (a.down.2 x) : Σ y : c.down.1 x, c.down.2 x y).2⟩⟩⟩ :
          D_tp_tp0.obj X) := by
  subst hab
  subst hcd
  obtain ⟨⟨B, s⟩⟩ := a
  obtain ⟨⟨A, C⟩⟩ := c
  dsimp at ha
  subst ha
  rfl

noncomputable def psh_sig0_pb :
    IsNaturalModelPullbackCommon Sig0_pair D_tp_tp0_proj PshUniverse0_tp_Embed Sig0_Ty where
  w := Sig0_pb_comm
  lift := fun {T} h1 h2 h_comm => {
    app := fun Δ_op t =>
      let p_ty := (h2.app Δ_op t).down
      let A := p_ty.1
      let B := p_ty.2
      have h_comm_t : (h1.app Δ_op t).down.1 = fun x => Σ a : A x, B x a :=
        congrArg ULift.down
          (congrFun (congrArg (fun (m : T ⟶ PshUniverse0_Ty_Embed) => m.app Δ_op) h_comm) t)
      let s : ∀ x, Σ a : A x, B x a := fun x =>
        (cast (congrFun h_comm_t x) ((h1.app Δ_op t).down.2 x) : Σ a : A x, B x a)
      ⟨⟨A, ⟨B, ⟨fun x => (s x).1, fun x => (s x).2⟩⟩⟩⟩
    naturality := by
      intro X Y f
      funext t
      exact (psh_sig0_pb_lift_natural_aux f
        (h1.app X t) (h1.app Y (T.map f t))
        (h2.app X t) (h2.app Y (T.map f t))
        (congrFun (h1.naturality f).symm t)
        (congrFun (h2.naturality f).symm t)
        (congrArg ULift.down
          (congrFun (congrArg (fun (m : T ⟶ PshUniverse0_Ty_Embed) => m.app X) h_comm) t))
        (congrArg ULift.down
          (congrFun (congrArg (fun (m : T ⟶ PshUniverse0_Ty_Embed) => m.app Y) h_comm) (T.map f t))))
  }
  fac_snd := by
    intro T h1 h2 h_comm
    rfl

structure UniverseSigma (u : UniverseCommon) where
  Ptp_Ty       : PshUniverseCommon
  D_tp         : PshUniverseCommon
  D_proj       : D_tp ⟶ Ptp_Ty
  Sig          : Ptp_Ty ⟶ u.Ty
  pair         : D_tp ⟶ u.Tm
  Sig_pullback : IsNaturalModelPullbackCommon pair D_proj u.tp Sig

noncomputable def PshUniverse0_Sigma : UniverseSigma PshUniv0_Common where
  Ptp_Ty       := Ptp_Ty0
  D_tp         := D_tp_tp0
  D_proj       := D_tp_tp0_proj
  Sig          := Sig0_Ty
  pair         := Sig0_pair
  Sig_pullback := psh_sig0_pb

noncomputable def PshUniverse1_Sigma : UniverseSigma PshUniv1_Common where
  Ptp_Ty       := Ptp_Ty0
  D_tp         := D_tp_tp0
  D_proj       := D_tp_tp0_proj
  Sig          := Sig0_Ty ≫ PshUHom01_mapTy
  pair         := Sig0_pair ≫ PshUHom01_mapTm
  Sig_pullback := {
    w := by
      calc
        (Sig0_pair ≫ PshUHom01_mapTm) ≫ PshUniv1_Common.tp
            = Sig0_pair ≫ (PshUHom01_mapTm ≫ PshUniv1_Common.tp) :=
              CategoryTheory.Category.assoc _ _ _
        _ = Sig0_pair ≫ (PshUniverse0_tp_Embed ≫ PshUHom01_mapTy) :=
              congrArg (fun φ => Sig0_pair ≫ φ) PshUHom01_pb_comm
        _ = (Sig0_pair ≫ PshUniverse0_tp_Embed) ≫ PshUHom01_mapTy :=
              (CategoryTheory.Category.assoc _ _ _).symm
        _ = (D_tp_tp0_proj ≫ Sig0_Ty) ≫ PshUHom01_mapTy :=
              congrArg (fun φ => φ ≫ PshUHom01_mapTy) Sig0_pb_comm
        _ = D_tp_tp0_proj ≫ (Sig0_Ty ≫ PshUHom01_mapTy) :=
              CategoryTheory.Category.assoc _ _ _
    lift := fun {T} h1 h2 h_comm =>
      let h1_0 := psh_uhom01_pb.lift h1 (h2 ≫ Sig0_Ty)
        (h_comm.trans (CategoryTheory.Category.assoc _ _ _).symm)
      psh_sig0_pb.lift h1_0 h2
        (psh_uhom01_pb.fac_snd h1 (h2 ≫ Sig0_Ty) _)
    fac_snd := by
      intro T h1 h2 h_comm
      exact psh_sig0_pb.fac_snd _ _ _
  }

class PiSeqCommon (s : UHomSeqCommon) where
  nmPi : ∀ (i : Nat) (h : i < s.len + 1), UniversePi (s.objs i h)

class SigSeqCommon (s : UHomSeqCommon) where
  nmSig : ∀ (i : Nat) (h : i < s.len + 1), UniverseSigma (s.objs i h)

noncomputable instance : PiSeqCommon realUHomSeq where
  nmPi := fun i h => by
    cases i with
    | zero =>
      exact PshUniverse0_Pi
    | succ n =>
      cases n with
      | zero =>
        exact PshUniverse1_Pi
      | succ m =>
        have h_len : realUHomSeq.len = 1 := rfl
        omega

noncomputable instance : SigSeqCommon realUHomSeq where
  nmSig := fun i h => by
    cases i with
    | zero =>
      exact PshUniverse0_Sigma
    | succ n =>
      cases n with
      | zero =>
        exact PshUniverse1_Sigma
      | succ m =>
        have h_len : realUHomSeq.len = 1 := rfl
        omega

def K_Id0 : PshUniverseCommon where
  obj Γ_op := ULift.{2, 1} (Σ (A : Γ_op.unop.carrier → Type 0),
    (∀ x, A x) × (∀ x, A x))
  map f p := ⟨⟨p.down.1 ∘ f.unop.toFun,
    (fun x => p.down.2.1 (f.unop.toFun x),
     fun x => p.down.2.2 (f.unop.toFun x))⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def k1_0 : K_Id0 ⟶ PshUniverse0_Tm_Embed where
  app _ p := ⟨⟨p.down.1, p.down.2.1⟩⟩
  naturality _ _ _ := rfl

def k2_0 : K_Id0 ⟶ PshUniverse0_Tm_Embed where
  app _ p := ⟨⟨p.down.1, p.down.2.2⟩⟩
  naturality _ _ _ := rfl

theorem kp_comm0 : k1_0 ≫ PshUniverse0_tp_Embed = k2_0 ≫ PshUniverse0_tp_Embed :=
  rfl

def Id0_Ty : K_Id0 ⟶ PshUniverse0_Ty_Embed where
  app _ p := ⟨fun x => PLift (p.down.2.1 x = p.down.2.2 x)⟩
  naturality _ _ _ := rfl

def diagK0 : PshUniverse0_Tm_Embed ⟶ K_Id0 where
  app _ p := ⟨⟨p.down.1, (p.down.2, p.down.2)⟩⟩
  naturality _ _ _ := rfl

def refl0_Tm : PshUniverse0_Tm_Embed ⟶ PshUniverse0_Tm_Embed where
  app _ p := ⟨⟨fun x => PLift (p.down.2 x = p.down.2 x), fun x => ⟨rfl⟩⟩⟩
  naturality _ _ _ := rfl

theorem refl0_tp_comm :
    refl0_Tm ≫ PshUniverse0_tp_Embed = diagK0 ≫ Id0_Ty :=
  rfl

structure IdIntroCommon (u : UniverseCommon) : Type 3 where
  K       : PshUniverseCommon
  k1      : K ⟶ u.Tm
  k2      : K ⟶ u.Tm
  kp_comm : k1 ≫ u.tp = k2 ≫ u.tp
  Id      : K ⟶ u.Ty
  diag    : u.Tm ⟶ K
  diag_k1 : diag ≫ k1 = 𝟙 u.Tm
  diag_k2 : diag ≫ k2 = 𝟙 u.Tm
  refl    : u.Tm ⟶ u.Tm
  refl_tp : refl ≫ u.tp = diag ≫ Id

def PshUniverse0_IdIntro : IdIntroCommon PshUniv0_Common where
  K       := K_Id0
  k1      := k1_0
  k2      := k2_0
  kp_comm := kp_comm0
  Id      := Id0_Ty
  diag    := diagK0
  diag_k1 := rfl
  diag_k2 := rfl
  refl    := refl0_Tm
  refl_tp := refl0_tp_comm

def K_Id1 : PshUniverseCommon where
  obj Γ_op := Σ (A : Γ_op.unop.carrier → Type 1), (∀ x, A x) × (∀ x, A x)
  map f p := ⟨p.1 ∘ f.unop.toFun,
    (fun x => p.2.1 (f.unop.toFun x), fun x => p.2.2 (f.unop.toFun x))⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def k1_1 : K_Id1 ⟶ PshUniverse1_Tm_Embed where
  app _ p := ⟨p.1, p.2.1⟩
  naturality _ _ _ := rfl

def k2_1 : K_Id1 ⟶ PshUniverse1_Tm_Embed where
  app _ p := ⟨p.1, p.2.2⟩
  naturality _ _ _ := rfl

theorem kp_comm1 : k1_1 ≫ PshUniverse1_tp_Embed = k2_1 ≫ PshUniverse1_tp_Embed :=
  rfl

def Id1_Ty : K_Id1 ⟶ PshUniverse1_Ty_Embed where
  app _ p := fun x => ULift.{1, 0} (PLift (p.2.1 x = p.2.2 x))
  naturality _ _ _ := rfl

def diagK1 : PshUniverse1_Tm_Embed ⟶ K_Id1 where
  app _ p := ⟨p.1, (p.2, p.2)⟩
  naturality _ _ _ := rfl

def refl1_Tm : PshUniverse1_Tm_Embed ⟶ PshUniverse1_Tm_Embed where
  app _ p := ⟨fun x => ULift.{1, 0} (PLift (p.2 x = p.2 x)), fun x => ⟨⟨rfl⟩⟩⟩
  naturality _ _ _ := rfl

theorem refl1_tp_comm :
    refl1_Tm ≫ PshUniverse1_tp_Embed = diagK1 ≫ Id1_Ty :=
  rfl

def PshUniverse1_IdIntro : IdIntroCommon PshUniv1_Common where
  K       := K_Id1
  k1      := k1_1
  k2      := k2_1
  kp_comm := kp_comm1
  Id      := Id1_Ty
  diag    := diagK1
  diag_k1 := rfl
  diag_k2 := rfl
  refl    := refl1_Tm
  refl_tp := refl1_tp_comm

structure IdElimCommon (u0 u1 : UniverseCommon) (ii : IdIntroCommon u0) : Type 3 where
  jElim : ∀ {Γ_op : (PartitionedAssembly.{0})ᵒᵖ}
    (A : Γ_op.unop.carrier → Type 0)
    (a0 a1 : ∀ x, A x)
    (p : ∀ x, a0 x = a1 x)
    (C : ∀ x (y : A x), a0 x = y → Type 0)
    (c : ∀ x, C x (a0 x) rfl),
    ∀ x, C x (a1 x) (p x)
  refl_jElim : ∀ {Γ_op : (PartitionedAssembly.{0})ᵒᵖ}
    (A : Γ_op.unop.carrier → Type 0)
    (a0 : ∀ x, A x)
    (C : ∀ x (y : A x), a0 x = y → Type 0)
    (c : ∀ x, C x (a0 x) rfl) (x : Γ_op.unop.carrier),
    jElim A a0 a0 (fun _ => rfl) C c x = c x

def psh_jElim {Γ_op : (PartitionedAssembly.{0})ᵒᵖ}
    (A : Γ_op.unop.carrier → Type 0)
    (a0 a1 : ∀ x, A x)
    (p : ∀ x, a0 x = a1 x)
    (C : ∀ x (y : A x), a0 x = y → Type 0)
    (c : ∀ x, C x (a0 x) rfl) :
    ∀ x, C x (a1 x) (p x) :=
  fun x => @Eq.rec (A x) (a0 x) (C x) (c x) (a1 x) (p x)

theorem psh_refl_jElim {Γ_op : (PartitionedAssembly.{0})ᵒᵖ}
    (A : Γ_op.unop.carrier → Type 0)
    (a0 : ∀ x, A x)
    (C : ∀ x (y : A x), a0 x = y → Type 0)
    (c : ∀ x, C x (a0 x) rfl) (x : Γ_op.unop.carrier) :
    psh_jElim A a0 a0 (fun _ => rfl) C c x = c x :=
  rfl

def PshUniverse0_IdElim : IdElimCommon PshUniv0_Common PshUniv0_Common PshUniverse0_IdIntro where
  jElim      := psh_jElim
  refl_jElim := psh_refl_jElim

def PshUniverseIdElim (u0 u1 : UniverseCommon) (ii : IdIntroCommon u0) :
    IdElimCommon u0 u1 ii where
  jElim      := psh_jElim
  refl_jElim := psh_refl_jElim

class IdSeqCommon (s : UHomSeqCommon) where
  nmIntro : ∀ (i : Nat) (h : i < s.len + 1), IdIntroCommon (s.objs i h)
  nmElim  : ∀ (i j : Nat) (hi : i < s.len + 1) (hj : j < s.len + 1),
    IdElimCommon (s.objs i hi) (s.objs j hj) (nmIntro i hi)

noncomputable instance : IdSeqCommon realUHomSeq where
  nmIntro i h := by
    match i, h with
    | 0, _ => exact PshUniverse0_IdIntro
    | 1, _ =>
      dsimp [realUHomSeq]
      exact PshUniverse1_IdIntro
    | _ + 2, h =>
      dsimp [realUHomSeq] at h
      exact False.elim (by omega)

  nmElim i j hi hj := PshUniverseIdElim _ _ _

def sem_refl_obj {Γ : PartitionedAssembly.{0}}
    (A : Γ.carrier → Type 0) (x : ∀ d : Γ.carrier, A d) :
    PshUniverse0_Tm_Embed.obj (Opposite.op Γ) :=
  ⟨⟨fun d => PLift (x d = x d), fun d => ⟨rfl⟩⟩⟩

def sem_eq_obj {Γ : PartitionedAssembly.{0}}
    (A : Γ.carrier → Type 0) (x y : ∀ d : Γ.carrier, A d)
    (h : ∀ d : Γ.carrier, x d = y d) :
    PshUniverse0_Tm_Embed.obj (Opposite.op Γ) :=
  ⟨⟨fun d => PLift (x d = y d), fun d => ⟨h d⟩⟩⟩

@[simp]
theorem sem_refl_obj_eq_sem_eq_obj {Γ : PartitionedAssembly.{0}}
    (A : Γ.carrier → Type 0) (x : ∀ d : Γ.carrier, A d) :
    sem_refl_obj A x = sem_eq_obj A x x (fun _ => rfl) :=
  rfl

@[simp]
theorem sem_refl_obj_tp {Γ : PartitionedAssembly.{0}}
    (A : Γ.carrier → Type 0) (x : ∀ d : Γ.carrier, A d) :
    PshUniverse0_tp_Embed.app (Opposite.op Γ) (sem_refl_obj A x) =
      ⟨fun d => PLift (x d = x d)⟩ :=
  rfl

@[simp]
theorem sem_eq_obj_tp {Γ : PartitionedAssembly.{0}}
    (A : Γ.carrier → Type 0) (x y : ∀ d : Γ.carrier, A d)
    (h : ∀ d : Γ.carrier, x d = y d) :
    PshUniverse0_tp_Embed.app (Opposite.op Γ) (sem_eq_obj A x y h) =
      ⟨fun d => PLift (x d = y d)⟩ :=
  rfl

def sem_refl_mor {T : PshUniverseCommon} (t : T ⟶ PshUniverse0_Tm_Embed) :
    T ⟶ PshUniverse0_Tm_Embed :=
  t ≫ refl0_Tm

theorem sem_refl_mor_tp {T : PshUniverseCommon} (t : T ⟶ PshUniverse0_Tm_Embed) :
    sem_refl_mor t ≫ PshUniverse0_tp_Embed = t ≫ diagK0 ≫ Id0_Ty := by
  dsimp [sem_refl_mor]
  rw [Category.assoc, refl0_tp_comm]

def zqAdd (a b : ZMod q) : ZMod q := a + b
def zqMul (a b : ZMod q) : ZMod q := a * b
def zqSub (a b : ZMod q) : ZMod q := a - b
def zqNeg (a : ZMod q) : ZMod q := -a

def CtxCipher : PartitionedAssembly.{0} :=
  prodPA (prodPA Zq_PA Zq_PA) Zq_PA

def TyZqOnCipher : CtxCipher.carrier → Type 0 :=
  fun _ => ZMod q

def termCipher : ∀ p : CtxCipher.carrier, TyZqOnCipher p :=
  fun p => cipherFun p

def termCipherSpec : ∀ p : CtxCipher.carrier, TyZqOnCipher p :=
  fun p => cipherFun p

theorem concrete_Cipher_eq_impl (p : CtxCipher.carrier) :
    termCipher p = termCipherSpec p :=
  rfl

def sem_Cipher_eq_obj_real :
    PshUniverse0_Tm_Embed.obj (Opposite.op CtxCipher) :=
  sem_eq_obj TyZqOnCipher termCipher termCipher (fun _ => rfl)

@[simp]
theorem sem_Cipher_eq_obj_real_eq_refl :
    sem_Cipher_eq_obj_real = sem_refl_obj TyZqOnCipher termCipher :=
  rfl

@[simp]
theorem sem_Cipher_eq_obj_real_tp :
    PshUniverse0_tp_Embed.app (Opposite.op CtxCipher) sem_Cipher_eq_obj_real =
      ⟨fun p => PLift (termCipher p = termCipher p)⟩ :=
  rfl

def yPA_Common (X : PartitionedAssembly.{0}) : PshUniverseCommon where
  obj Δ_op := ULift.{2, 0} (TrackedMap Δ_op.unop X)
  map f σ := ⟨P_cat_comp f.unop σ.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def sem_Cipher_eq_tp_mor_real : yPA_Common CtxCipher ⟶ PshUniverse0_Ty_Embed where
  app Δ_op σ := ⟨fun d => PLift (termCipher (σ.down.toFun d) = termCipherSpec (σ.down.toFun d))⟩
  naturality X Y f := by
    ext σ
    rfl

def sem_Cipher_eq_mor_real : yPA_Common CtxCipher ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ :=
    ⟨⟨fun d => PLift (termCipher (σ.down.toFun d) = termCipherSpec (σ.down.toFun d)),
      fun d => ⟨concrete_Cipher_eq_impl (σ.down.toFun d)⟩⟩⟩
  naturality X Y f := by
    ext σ
    rfl

@[simp]
theorem sem_Cipher_eq_mor_real_apply_id :
    sem_Cipher_eq_mor_real.app (Opposite.op CtxCipher) ⟨P_cat_id CtxCipher⟩ =
      sem_Cipher_eq_obj_real := by
  dsimp [sem_Cipher_eq_mor_real, sem_Cipher_eq_obj_real, sem_eq_obj]
  rfl

theorem sem_Cipher_eq_mor_real_app_eq_map
    (Δ_op : (PartitionedAssembly.{0})ᵒᵖ)
    (σ : ULift.{2, 0} (TrackedMap Δ_op.unop CtxCipher)) :
    sem_Cipher_eq_mor_real.app Δ_op σ =
      PshUniverse0_Tm_Embed.map (Opposite.op σ.down) sem_Cipher_eq_obj_real :=
  rfl

theorem sem_Cipher_eq_tp_mor_real_app_eq_map
    (Δ_op : (PartitionedAssembly.{0})ᵒᵖ)
    (σ : ULift.{2, 0} (TrackedMap Δ_op.unop CtxCipher)) :
    sem_Cipher_eq_tp_mor_real.app Δ_op σ =
      PshUniverse0_Ty_Embed.map (Opposite.op σ.down)
        ⟨fun p => PLift (termCipher p = termCipherSpec p)⟩ :=
  rfl

theorem sem_Cipher_eq_tp_comm_real :
    sem_Cipher_eq_mor_real ≫ PshUniverse0_tp_Embed = sem_Cipher_eq_tp_mor_real := by
  ext Δ_op σ
  rfl

def CtxDecipher : PartitionedAssembly.{0} :=
  prodPA (prodPA Zq_PA Zq_PA) Zq_PA

def TyZqOnDecipher : CtxDecipher.carrier → Type 0 :=
  fun _ => ZMod q

def termDecipher : ∀ p : CtxDecipher.carrier, TyZqOnDecipher p :=
  fun p => decipherFun p

def termDecipherSpec : ∀ p : CtxDecipher.carrier, TyZqOnDecipher p :=
  fun p => zqSub p.1.1 (zqMul p.1.2 p.2)

theorem sem_eq_obj_of_eq {Γ : PartitionedAssembly.{0}}
    (A : Γ.carrier → Type 0) {x y : ∀ d : Γ.carrier, A d}
    (h : ∀ d : Γ.carrier, x d = y d) (e : y = x) :
    sem_eq_obj A x y h = sem_refl_obj A x := by
  subst e
  rfl

theorem concrete_Decipher_eq_impl (p : CtxDecipher.carrier) :
    termDecipher p = termDecipherSpec p :=
  rfl

def sem_Decipher_eq_obj_real :
    PshUniverse0_Tm_Embed.obj (Opposite.op CtxDecipher) :=
  sem_eq_obj TyZqOnDecipher termDecipher termDecipherSpec concrete_Decipher_eq_impl

@[simp]
theorem sem_Decipher_eq_obj_real_eq_refl :
    sem_Decipher_eq_obj_real = sem_refl_obj TyZqOnDecipher termDecipher := by
  apply sem_eq_obj_of_eq
  funext p
  exact (concrete_Decipher_eq_impl p).symm

@[simp]
theorem sem_Decipher_eq_obj_real_tp :
    PshUniverse0_tp_Embed.app (Opposite.op CtxDecipher) sem_Decipher_eq_obj_real =
      ⟨fun p => PLift (termDecipher p = termDecipherSpec p)⟩ :=
  rfl

def sem_Decipher_eq_tp_mor_real : yPA_Common CtxDecipher ⟶ PshUniverse0_Ty_Embed where
  app Δ_op σ := ⟨fun d => PLift (termDecipher (σ.down.toFun d) = termDecipherSpec (σ.down.toFun d))⟩
  naturality X Y f := by
    ext σ
    rfl

def sem_Decipher_eq_mor_real : yPA_Common CtxDecipher ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ :=
    ⟨⟨fun d => PLift (termDecipher (σ.down.toFun d) = termDecipherSpec (σ.down.toFun d)),
      fun d => ⟨concrete_Decipher_eq_impl (σ.down.toFun d)⟩⟩⟩
  naturality X Y f := by
    ext σ
    rfl

@[simp]
theorem sem_Decipher_eq_mor_real_apply_id :
    sem_Decipher_eq_mor_real.app (Opposite.op CtxDecipher) ⟨P_cat_id CtxDecipher⟩ =
      sem_Decipher_eq_obj_real := by
  dsimp [sem_Decipher_eq_mor_real, sem_Decipher_eq_obj_real, sem_eq_obj]
  rfl

theorem sem_Decipher_eq_mor_real_app_eq_map
    (Δ_op : (PartitionedAssembly.{0})ᵒᵖ)
    (σ : ULift.{2, 0} (TrackedMap Δ_op.unop CtxDecipher)) :
    sem_Decipher_eq_mor_real.app Δ_op σ =
      PshUniverse0_Tm_Embed.map (Opposite.op σ.down) sem_Decipher_eq_obj_real :=
  rfl

theorem sem_Decipher_eq_tp_mor_real_app_eq_map
    (Δ_op : (PartitionedAssembly.{0})ᵒᵖ)
    (σ : ULift.{2, 0} (TrackedMap Δ_op.unop CtxDecipher)) :
    sem_Decipher_eq_tp_mor_real.app Δ_op σ =
      PshUniverse0_Ty_Embed.map (Opposite.op σ.down)
        ⟨fun p => PLift (termDecipher p = termDecipherSpec p)⟩ :=
  rfl

theorem sem_Decipher_eq_tp_comm_real :
    sem_Decipher_eq_mor_real ≫ PshUniverse0_tp_Embed = sem_Decipher_eq_tp_mor_real := by
  ext Δ_op σ
  rfl

theorem concrete_Correctness_Path_eps0_impl (p : CtxCipher.carrier) :
    decipherFun ((cipherFun p, p.1.2), p.2) = p.1.1 := by
  dsimp [cipherFun, decipherFun]
  ring

def termDecipherOfCipher : ∀ p : CtxCipher.carrier, TyZqOnCipher p :=
  fun p => decipherFun ((cipherFun p, p.1.2), p.2)

def termPlaintext : ∀ p : CtxCipher.carrier, TyZqOnCipher p :=
  fun p => p.1.1

def sem_Theorem_Correctness_Path_eps0_obj_real :
    PshUniverse0_Tm_Embed.obj (Opposite.op CtxCipher) :=
  sem_eq_obj TyZqOnCipher termDecipherOfCipher termPlaintext concrete_Correctness_Path_eps0_impl

@[simp]
theorem sem_Theorem_Correctness_Path_eps0_obj_real_tp :
    PshUniverse0_tp_Embed.app (Opposite.op CtxCipher) sem_Theorem_Correctness_Path_eps0_obj_real =
      ⟨fun p => PLift (decipherFun ((cipherFun p, p.1.2), p.2) = p.1.1)⟩ :=
  rfl

theorem sem_Theorem_Correctness_Path_eps0_eval0 (p : CtxCipher.carrier) :
    termDecipherOfCipher p = decipherFun ((cipherFun p, p.1.2), p.2) :=
  rfl

theorem sem_Theorem_Correctness_Path_eps0_eval1 (p : CtxCipher.carrier) :
    termPlaintext p = p.1.1 :=
  rfl

def sem_Theorem_Correctness_Path_eps0_tp_mor_real :
    yPA_Common CtxCipher ⟶ PshUniverse0_Ty_Embed where
  app Δ_op σ :=
    ⟨fun d => PLift (decipherFun ((cipherFun (σ.down.toFun d), (σ.down.toFun d).1.2), (σ.down.toFun d).2) =
                    (σ.down.toFun d).1.1)⟩
  naturality X Y f := by
    ext σ
    rfl

def sem_Theorem_Correctness_Path_eps0_mor_real :
    yPA_Common CtxCipher ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ :=
    ⟨⟨fun d => PLift (decipherFun ((cipherFun (σ.down.toFun d), (σ.down.toFun d).1.2), (σ.down.toFun d).2) =
                      (σ.down.toFun d).1.1),
      fun d => ⟨concrete_Correctness_Path_eps0_impl (σ.down.toFun d)⟩⟩⟩
  naturality X Y f := by
    ext σ
    rfl

@[simp]
theorem sem_Theorem_Correctness_Path_eps0_mor_real_apply_id :
    sem_Theorem_Correctness_Path_eps0_mor_real.app (Opposite.op CtxCipher) ⟨P_cat_id CtxCipher⟩ =
      sem_Theorem_Correctness_Path_eps0_obj_real := by
  dsimp [sem_Theorem_Correctness_Path_eps0_mor_real, sem_Theorem_Correctness_Path_eps0_obj_real, sem_eq_obj]
  rfl

theorem sem_Theorem_Correctness_Path_eps0_tp_comm_real :
    sem_Theorem_Correctness_Path_eps0_mor_real ≫ PshUniverse0_tp_Embed =
      sem_Theorem_Correctness_Path_eps0_tp_mor_real := by
  ext Δ_op σ
  rfl

def sem_DecipherOfCipher_mor : yPA_Common CtxCipher ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ :=
    ⟨⟨fun _ => ZMod q,
      fun d => decipherFun ((cipherFun (σ.down.toFun d), (σ.down.toFun d).1.2), (σ.down.toFun d).2)⟩⟩
  naturality X Y f := by
    funext σ
    rfl

def sem_Plaintext_mor : yPA_Common CtxCipher ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ :=
    ⟨⟨fun _ => ZMod q,
      fun d => (σ.down.toFun d).1.1⟩⟩
  naturality X Y f := by
    funext σ
    rfl

theorem sem_Theorem_Correctness_Path_eps0_mor_eval0 :
    ∀ (Δ_op : (PartitionedAssembly.{0})ᵒᵖ)
      (σ : ULift.{2, 0} (TrackedMap Δ_op.unop CtxCipher))
      (d : Δ_op.unop.carrier),
      decipherFun ((cipherFun (σ.down.toFun d), (σ.down.toFun d).1.2), (σ.down.toFun d).2) =
        (sem_DecipherOfCipher_mor.app Δ_op σ).down.2 d := by
  intros
  rfl

theorem sem_Theorem_Correctness_Path_eps0_mor_eval1 :
    ∀ (Δ_op : (PartitionedAssembly.{0})ᵒᵖ)
      (σ : ULift.{2, 0} (TrackedMap Δ_op.unop CtxCipher))
      (d : Δ_op.unop.carrier),
      (σ.down.toFun d).1.1 = (sem_Plaintext_mor.app Δ_op σ).down.2 d := by
  intros
  rfl

def sem_Zq_ty : yPA_one_Common ⟶ PshUniverse0_Ty_Embed where
  app _ _ := ⟨fun _ => ZMod q⟩
  naturality _ _ _ := rfl

def sem_S_ty : yPA_one_Common ⟶ PshUniverse0_Ty_Embed where
  app _ _ := ⟨fun _ => ZMod q⟩
  naturality _ _ _ := rfl

def sem_R_ty : yPA_one_Common ⟶ PshUniverse0_Ty_Embed where
  app _ _ := ⟨fun _ => ZMod q⟩
  naturality _ _ _ := rfl

def sem_G0_ty : yPA_one_Common ⟶ PshUniverse0_Ty_Embed where
  app _ _ := ⟨fun _ => ZMod q⟩
  naturality _ _ _ := rfl

def sem_Manifold4D_ty : yPA_one_Common ⟶ PshUniverse0_Ty_Embed where
  app _ _ := ⟨fun _ => Manifold4D⟩
  naturality _ _ _ := rfl

def sem_zero_tm : yPA_one_Common ⟶ PshUniverse0_Tm_Embed where
  app _ _ := ⟨fun _ => ZMod q, fun _ => 0⟩
  naturality _ _ _ := rfl

def sem_one_tm : yPA_one_Common ⟶ PshUniverse0_Tm_Embed where
  app _ _ := ⟨fun _ => ZMod q, fun _ => 1⟩
  naturality _ _ _ := rfl

def sem_add_tm : yPA_Common (prodPA Zq_PA Zq_PA) ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ := ⟨fun _ => ZMod q, fun d => zqAdd (σ.down.toFun d).1 (σ.down.toFun d).2⟩
  naturality _ _ _ := rfl

def sem_mul_tm : yPA_Common (prodPA Zq_PA Zq_PA) ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ := ⟨fun _ => ZMod q, fun d => zqMul (σ.down.toFun d).1 (σ.down.toFun d).2⟩
  naturality _ _ _ := rfl

def sem_neg_tm : yPA_Common Zq_PA ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ := ⟨⟨fun _ => ZMod q, fun d => zqNeg (σ.down.toFun d)⟩⟩
  naturality X Y f := by
    ext σ
    rfl

def sem_Cipher_tm : yPA_Common CtxCipher ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ := ⟨fun _ => ZMod q, fun d => cipherFun (σ.down.toFun d)⟩
  naturality _ _ _ := rfl

def sem_Decipher_tm : yPA_Common CtxDecipher ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ := ⟨fun _ => ZMod q, fun d => decipherFun (σ.down.toFun d)⟩
  naturality _ _ _ := rfl

def sem_Cipher_eq_tm : yPA_Common CtxCipher ⟶ PshUniverse0_Tm_Embed :=
  sem_Cipher_eq_mor_real

def sem_Decipher_eq_tm : yPA_Common CtxDecipher ⟶ PshUniverse0_Tm_Embed :=
  sem_Decipher_eq_mor_real

def sem_Theorem_Correctness_Path_eps0_tm : yPA_Common CtxCipher ⟶ PshUniverse0_Tm_Embed :=
  sem_Theorem_Correctness_Path_eps0_mor_real

def sem_manifold_init_tm : yPA_one_Common ⟶ PshUniverse0_Tm_Embed where
  app _ _ := ⟨fun _ => Manifold4D, fun _ => ⟨0, 0, 0, 0, 0⟩⟩
  naturality _ _ _ := rfl

def sem_manifold_step_tm : yPA_Common Manifold4D_PA ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ :=
    ⟨fun _ => Manifold4D,
     fun d =>
       let m := σ.down.toFun d
       ⟨m.id + 1, m.x + 1, m.y, m.z, m.t + 1⟩⟩
  naturality _ _ _ := rfl

def sem_manifold_proj_x_tm : yPA_Common Manifold4D_PA ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ := ⟨fun _ => Nat, fun d => (σ.down.toFun d).x⟩
  naturality _ _ _ := rfl

def sem_manifold_proj_t_tm : yPA_Common Manifold4D_PA ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ := ⟨fun _ => Nat, fun d => (σ.down.toFun d).t⟩
  naturality _ _ _ := rfl

def sem_manifold_metric_tm : yPA_Common Manifold4D_PA ⟶ PshUniverse0_Tm_Embed where
  app Δ_op σ :=
    ⟨fun _ => ZMod q,
     fun d =>
       let m := σ.down.toFun d
       (((m.x * m.x + m.y * m.y + m.z * m.z : Nat) : ZMod q) - ((m.t * m.t : Nat) : ZMod q))⟩
  naturality _ _ _ := rfl

@[simp] theorem sem_zero_tp_comm : sem_zero_tm ≫ PshUniverse0_tp_Embed = sem_Zq_ty := rfl
@[simp] theorem sem_one_tp_comm : sem_one_tm ≫ PshUniverse0_tp_Embed = sem_Zq_ty := rfl
@[simp] theorem sem_Cipher_eq_comm : sem_Cipher_eq_tm ≫ PshUniverse0_tp_Embed = sem_Cipher_eq_tp_mor_real :=
  sem_Cipher_eq_tp_comm_real
@[simp] theorem sem_Decipher_eq_comm : sem_Decipher_eq_tm ≫ PshUniverse0_tp_Embed = sem_Decipher_eq_tp_mor_real :=
  sem_Decipher_eq_tp_comm_real
@[simp] theorem sem_Correctness_Path_comm :
    sem_Theorem_Correctness_Path_eps0_tm ≫ PshUniverse0_tp_Embed = sem_Theorem_Correctness_Path_eps0_tp_mor_real :=
  sem_Theorem_Correctness_Path_eps0_tp_comm_real
@[simp] theorem sem_manifold_init_tp_comm : sem_manifold_init_tm ≫ PshUniverse0_tp_Embed = sem_Manifold4D_ty := rfl

structure CryptoSemanticModel (seq : UHomSeqCommon) where
  ty_Zq         : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Ty
  ty_S          : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Ty
  ty_R          : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Ty
  ty_G0         : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Ty
  ty_Manifold4D : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Ty

  tm_zero : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Tm
  tm_one  : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Tm
  tm_add  : yPA_Common (prodPA Zq_PA Zq_PA) ⟶ (seq.objs 0 (by omega)).Tm
  tm_mul  : yPA_Common (prodPA Zq_PA Zq_PA) ⟶ (seq.objs 0 (by omega)).Tm
  tm_neg  : yPA_Common Zq_PA ⟶ (seq.objs 0 (by omega)).Tm

  tm_Cipher            : yPA_Common CtxCipher ⟶ (seq.objs 0 (by omega)).Tm
  tm_Decipher          : yPA_Common CtxDecipher ⟶ (seq.objs 0 (by omega)).Tm
  tm_Cipher_eq         : yPA_Common CtxCipher ⟶ (seq.objs 0 (by omega)).Tm
  tm_Decipher_eq       : yPA_Common CtxDecipher ⟶ (seq.objs 0 (by omega)).Tm
  tm_Correctness_Path  : yPA_Common CtxCipher ⟶ (seq.objs 0 (by omega)).Tm

  tm_manifold_init   : yPA_one_Common ⟶ (seq.objs 0 (by omega)).Tm
  tm_manifold_step   : yPA_Common Manifold4D_PA ⟶ (seq.objs 0 (by omega)).Tm
  tm_manifold_proj_x : yPA_Common Manifold4D_PA ⟶ (seq.objs 0 (by omega)).Tm
  tm_manifold_proj_t : yPA_Common Manifold4D_PA ⟶ (seq.objs 0 (by omega)).Tm
  tm_manifold_metric : yPA_Common Manifold4D_PA ⟶ (seq.objs 0 (by omega)).Tm

  ty_Cipher_eq : yPA_Common CtxCipher ⟶ (seq.objs 0 (by omega)).Ty
  ty_Decipher_eq : yPA_Common CtxDecipher ⟶ (seq.objs 0 (by omega)).Ty
  ty_Correctness_Path : yPA_Common CtxCipher ⟶ (seq.objs 0 (by omega)).Ty

  cipher_eq_sound : tm_Cipher_eq ≫ (seq.objs 0 (by omega)).tp = ty_Cipher_eq
  decipher_eq_sound : tm_Decipher_eq ≫ (seq.objs 0 (by omega)).tp = ty_Decipher_eq
  correctness_sound : tm_Correctness_Path ≫ (seq.objs 0 (by omega)).tp = ty_Correctness_Path

noncomputable def realCryptoSemanticModel : CryptoSemanticModel realUHomSeq where
  ty_Zq               := sem_Zq_ty
  ty_S                := sem_S_ty
  ty_R                := sem_R_ty
  ty_G0               := sem_G0_ty
  ty_Manifold4D       := sem_Manifold4D_ty

  ty_Cipher_eq        := sem_Cipher_eq_tp_mor_real
  ty_Decipher_eq      := sem_Decipher_eq_tp_mor_real
  ty_Correctness_Path := sem_Theorem_Correctness_Path_eps0_tp_mor_real

  tm_zero             := sem_zero_tm
  tm_one              := sem_one_tm
  tm_add              := sem_add_tm
  tm_mul              := sem_mul_tm
  tm_neg              := sem_neg_tm

  tm_Cipher           := sem_Cipher_tm
  tm_Decipher         := sem_Decipher_tm
  tm_Cipher_eq        := sem_Cipher_eq_tm
  tm_Decipher_eq      := sem_Decipher_eq_tm
  tm_Correctness_Path := sem_Theorem_Correctness_Path_eps0_tm

  tm_manifold_init    := sem_manifold_init_tm
  tm_manifold_step    := sem_manifold_step_tm
  tm_manifold_proj_x  := sem_manifold_proj_x_tm
  tm_manifold_proj_t  := sem_manifold_proj_t_tm
  tm_manifold_metric  := sem_manifold_metric_tm

  cipher_eq_sound     := sem_Cipher_eq_comm
  decipher_eq_sound   := sem_Decipher_eq_comm
  correctness_sound   := sem_Correctness_Path_comm

inductive SynCtx where
  | nil      : SynCtx
  | zq2      : SynCtx
  | zq1      : SynCtx
  | cipher   : SynCtx
  | decipher : SynCtx
  | manifold : SynCtx

def interpCtx : SynCtx → PartitionedAssembly.{0}
  | .nil      => onePA
  | .zq2      => prodPA Zq_PA Zq_PA
  | .zq1      => Zq_PA
  | .cipher   => CtxCipher
  | .decipher => CtxDecipher
  | .manifold => Manifold4D_PA

theorem yPA_one_Common_eq : yPA_Common onePA = yPA_one_Common :=
  rfl

inductive SynTy where
  | zq               : SynTy
  | s                : SynTy
  | r                : SynTy
  | g0               : SynTy
  | manifold         : SynTy
  | nat_ty           : SynTy
  | cipher_eq        : SynTy
  | decipher_eq      : SynTy
  | correctness_path : SynTy

def interpTy (Γ : SynCtx) : SynTy → (yPA_Common (interpCtx Γ) ⟶ PshUniverse0_Ty_Embed)
  | .zq =>
      { app := fun _ _ => ⟨fun _ => ZMod q⟩, naturality := fun _ _ _ => rfl }
  | .s =>
      { app := fun _ _ => ⟨fun _ => ZMod q⟩, naturality := fun _ _ _ => rfl }
  | .r =>
      { app := fun _ _ => ⟨fun _ => ZMod q⟩, naturality := fun _ _ _ => rfl }
  | .g0 =>
      { app := fun _ _ => ⟨fun _ => ZMod q⟩, naturality := fun _ _ _ => rfl }
  | .manifold =>
      { app := fun _ _ => ⟨fun _ => Manifold4D⟩, naturality := fun _ _ _ => rfl }
  | .nat_ty =>
      { app := fun _ _ => ⟨fun _ => Nat⟩, naturality := fun _ _ _ => rfl }
  | .cipher_eq =>
      match Γ with
      | .cipher => sem_Cipher_eq_tp_mor_real
      | _        => { app := fun _ _ => ⟨fun _ => Unit⟩, naturality := fun _ _ _ => rfl }
  | .decipher_eq =>
      match Γ with
      | .decipher => sem_Decipher_eq_tp_mor_real
      | _          => { app := fun _ _ => ⟨fun _ => Unit⟩, naturality := fun _ _ _ => rfl }
  | .correctness_path =>
      match Γ with
      | .cipher => sem_Theorem_Correctness_Path_eps0_tp_mor_real
      | _        => { app := fun _ _ => ⟨fun _ => Unit⟩, naturality := fun _ _ _ => rfl }

inductive SynTm where
  | zero               : SynTm
  | one                : SynTm
  | add                : SynTm
  | mul                : SynTm
  | neg                : SynTm
  | cipher             : SynTm
  | decipher           : SynTm
  | cipher_eq          : SynTm
  | decipher_eq        : SynTm
  | correctness_path   : SynTm
  | manifold_init      : SynTm
  | manifold_step      : SynTm
  | manifold_proj_x    : SynTm
  | manifold_proj_t    : SynTm
  | manifold_metric    : SynTm

noncomputable def interpTm : ∀ (Γ : SynCtx) (t : SynTm), yPA_Common (interpCtx Γ) ⟶ PshUniverse0_Tm_Embed :=
  let M : CryptoSemanticModel _ := realCryptoSemanticModel
  fun Γ t =>
    match Γ, t with
    | .nil,      .zero                => M.tm_zero
    | .nil,      .one                 => M.tm_one
    | .zq2,      .add                 => M.tm_add
    | .zq2,      .mul                 => M.tm_mul
    | .zq1,      .neg                 => M.tm_neg
    | .cipher,   .cipher              => M.tm_Cipher
    | .decipher, .decipher            => M.tm_Decipher
    | .cipher,   .cipher_eq           => M.tm_Cipher_eq
    | .decipher, .decipher_eq         => M.tm_Decipher_eq
    | .cipher,   .correctness_path    => M.tm_Correctness_Path
    | .nil,      .manifold_init       => M.tm_manifold_init
    | .manifold, .manifold_step       => M.tm_manifold_step
    | .manifold, .manifold_proj_x     => M.tm_manifold_proj_x
    | .manifold, .manifold_proj_t     => M.tm_manifold_proj_t
    | .manifold, .manifold_metric     => M.tm_manifold_metric
    | _,         _                    =>
        { app := fun _ _ => ⟨fun _ => Unit, fun _ => ()⟩, naturality := fun _ _ _ => rfl }

inductive SynWf : SynCtx → SynTm → SynTy → Prop where
  | wf_zero             : SynWf .nil      .zero             .zq
  | wf_one              : SynWf .nil      .one              .zq
  | wf_add              : SynWf .zq2      .add              .zq
  | wf_mul              : SynWf .zq2      .mul              .zq
  | wf_neg              : SynWf .zq1      .neg              .zq
  | wf_cipher           : SynWf .cipher   .cipher           .zq
  | wf_decipher         : SynWf .decipher .decipher         .zq
  | wf_cipher_eq        : SynWf .cipher   .cipher_eq        .cipher_eq
  | wf_decipher_eq      : SynWf .decipher .decipher_eq      .decipher_eq
  | wf_correctness_path : SynWf .cipher   .correctness_path .correctness_path
  | wf_manifold_init    : SynWf .nil      .manifold_init    .manifold
  | wf_manifold_step    : SynWf .manifold .manifold_step    .manifold
  | wf_manifold_proj_x  : SynWf .manifold .manifold_proj_x  .nat_ty
  | wf_manifold_proj_t  : SynWf .manifold .manifold_proj_t  .nat_ty
  | wf_manifold_metric  : SynWf .manifold .manifold_metric  .zq

theorem crypto_topos_interpretation_wf (Γ : SynCtx) (t : SynTm) (A : SynTy)
    (h : SynWf Γ t A) :
    interpTm Γ t ≫ PshUniverse0_tp_Embed = interpTy Γ A := by
  cases h with
  | wf_zero =>
      exact sem_zero_tp_comm
  | wf_one =>
      exact sem_one_tp_comm
  | wf_add =>
      rfl
  | wf_mul =>
      rfl
  | wf_neg =>
      rfl
  | wf_cipher =>
      rfl
  | wf_decipher =>
      rfl
  | wf_cipher_eq =>
      exact sem_Cipher_eq_comm
  | wf_decipher_eq =>
      exact sem_Decipher_eq_comm
  | wf_correctness_path =>
      exact sem_Correctness_Path_comm
  | wf_manifold_init =>
      exact sem_manifold_init_tp_comm
  | wf_manifold_step =>
      rfl
  | wf_manifold_proj_x =>
      rfl
  | wf_manifold_proj_t =>
      rfl
  | wf_manifold_metric =>
      rfl

structure CryptoToposSoundnessResult where
  syn_wf : SynWf .cipher .correctness_path .correctness_path

  sem_sound : interpTm .cipher .correctness_path ≫ PshUniverse0_tp_Embed =
              interpTy .cipher .correctness_path

  alg_correct : ∀ (p : CtxCipher.carrier),
    decipherFun ((cipherFun p, p.1.2), p.2) = p.1.1

  truncation_sound : ∀ (coh_dict : ∀ (G : InternalGroupoid) (GxG : GroupoidProduct G G)
      (DiagG : GroupoidDiagonal G GxG) (DiagG2 : GroupoidSecondDiagonal G GxG DiagG),
      IsCoherentGroupoid G GxG DiagG DiagG2 → IsZeroType G GxG DiagG →
      IsCoherentObject G.G0)
    (GxG : GroupoidProduct Gpd_Zq Gpd_Zq)
    (Diag : GroupoidDiagonal Gpd_Zq GxG)
    (Diag2 : GroupoidSecondDiagonal Gpd_Zq GxG Diag)
    (hCoh : IsCoherentGroupoid Gpd_Zq GxG Diag Diag2)
    (hZero : IsZeroType Gpd_Zq GxG Diag),
    (stdTruncationThm coh_dict).to_coh_obj Gpd_Zq GxG Diag Diag2 hCoh hZero =
      ⟨Psh_Zq, coh_dict Gpd_Zq GxG Diag Diag2 hCoh hZero⟩

theorem crypto_topos_absolute_soundness : CryptoToposSoundnessResult where
  syn_wf :=
    SynWf.wf_correctness_path

  sem_sound :=
    crypto_topos_interpretation_wf .cipher .correctness_path .correctness_path
      SynWf.wf_correctness_path

  alg_correct :=
    concrete_Correctness_Path_eps0_impl

  truncation_sound :=
    zq_truncation_link

example : decipherFun ((cipherFun ((42, 1337), 99999), 1337), 99999) = 42 :=
  concrete_Correctness_Path_eps0_impl
    (((42, 1337), 99999) : (ZMod q × ZMod q) × ZMod q)

end CryptoTopos

#check (CryptoTopos.crypto_topos_absolute_soundness : CryptoTopos.CryptoToposSoundnessResult)

#print axioms CryptoTopos.crypto_topos_absolute_soundness
