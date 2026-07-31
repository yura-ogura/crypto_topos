import HoTTLean.Frontend.Commands
import HoTTLean.Model.Natural.Interpretation
import CryptoTopos.Model
import CryptoTopos.Syntax

open CategoryTheory
open SynthLean
open NaturalModel.Universe

namespace CryptoTopos


def S_concrete : Type := Unit
def q_map_concrete (c : ZMod q) : ZMod q := c
def Φ_concrete (m : ZMod q) (_s : S_concrete) : ZMod q := m
def f_r_concrete (r : ZMod q) (x : ZMod q) : ZMod q := x + r
def f_r_inv_concrete (r : ZMod q) (x : ZMod q) : ZMod q := x - r


theorem sec_Φ_concrete_proof (n : ZMod q) (s : S_concrete) :
  q_map_concrete (Φ_concrete n s) = n := rfl

theorem ϵ_r_concrete_proof (r : ZMod q) (x : ZMod q) :
  f_r_inv_concrete r (f_r_concrete r x) = x := by
  dsimp [f_r_inv_concrete, f_r_concrete]
  ring

theorem isMonic_Δ_concrete_proof (x y : ZMod q) (p q : x = y) : p = q := rfl


variable {ℳ : Type _} [SmallCategory ℳ] [ChosenTerminal ℳ] (s : UHomSeq ℳ)
variable [s.PiSeq] [s.SigSeq] [s.IdSeq]


def crypto_topos_interpretation : Interpretation Lean.Name s where
  ax := fun c _ _ =>

    if c = V.name then none
    else if c = M.name then none
    else if c = R.name then none
    else if c = S.name then none
    else if c = G₀.name then none
    else if c = q_map.name then none
    else if c = Φ.name then none
    else if c = f_r.name then none
    else if c = f_r_inv.name then none
    else if c = sec_Φ.name then none
    else if c = ϵ_r.name then none
    else if c = isMonic_Δ.name then none
    else none

end CryptoTopos
