import HoTTLean.Frontend.Commands

noncomputable section

/-- Theory of the cryptographic topos. -/
declare_theory crypto_topos

namespace CryptoTopos

/-! ### Base types and axioms (Parts I - V) -/

crypto_topos axiom V : Type
crypto_topos axiom M : Type
crypto_topos axiom R : Type
crypto_topos axiom S : Type
crypto_topos axiom G₀ : Type

/-- Axiom [Part I.7]: The message space `M` is 0-truncated (a Set). -/
crypto_topos axiom isMonic_Δ (x y : M) (p q : Identity x y) : Identity p q

/-- [Part IV] Adjunction maps. -/
crypto_topos axiom q_map : G₀ → M
crypto_topos axiom Φ : M → S → G₀

/-- Adjunction core identity (foundation for `Theorem_iso_Φ`). -/
crypto_topos axiom sec_Φ (n : M) (s : S) : Identity (q_map (Φ n s)) n

/-- [Part IV.2-3] Decoding map. -/
crypto_topos def Φ_inv (ρ : G₀) (_s : S) : M := q_map ρ

/-- Isomorphism proof showing that `Φ_inv` is a retraction of `Φ`. -/
crypto_topos def Theorem_iso_Φ (n : M) (s : S) : Identity (Φ_inv (Φ n s) s) n :=
  sec_Φ n s

/-- [Part V] Key-based encryption/decryption actions. -/
crypto_topos axiom f_r : R → G₀ → G₀
crypto_topos axiom f_r_inv : R → G₀ → G₀

/-- Encryption algorithm. -/
crypto_topos def Cipher (n : M) (s : S) (r : R) : G₀ :=
  f_r r (Φ n s)

/-- Decryption algorithm. -/
crypto_topos def Decipher (ρ : G₀) (s : S) (r : R) : M :=
  Φ_inv (f_r_inv r ρ) s


/-! ### Part VI: Homotopical Correctness and Identity Proofs -/

/-- Retraction path of the key action (ϵ_r). -/
crypto_topos axiom ϵ_r (r : R) (x : G₀) : Identity (f_r_inv r (f_r r x)) x

/-- Proof of cryptographic correctness (Theorem_Correctness).
    Transports the retraction path along `q_map` using `Identity.rec` with an
    explicit motive, then composes it with `Theorem_iso_Φ` via trans₀. -/
crypto_topos def Theorem_Correctness (n : M) (s : S) (r : R) :
  Identity (Decipher (Cipher n s r) s r) n :=
  (@Identity.rec
    G₀
    (f_r_inv r (f_r r (Φ n s)))
    (fun (x : G₀) (_ : Identity (f_r_inv r (f_r r (Φ n s))) x) =>
      Identity (q_map (f_r_inv r (f_r r (Φ n s)))) (q_map x))
    (Identity.refl (q_map (f_r_inv r (f_r r (Φ n s)))))
    (Φ n s)
    (ϵ_r r (Φ n s))
  ).trans₀ (Theorem_iso_Φ n s)

/-- Uniqueness of correctness proofs (Theorem_Uniqueness_M).
    Any two correctness proofs `p` and `q` are equal since `M` is a 0-type. -/
crypto_topos def Theorem_Uniqueness_M (n : M) (s : S) (r : R)
  (p q : Identity (Decipher (Cipher n s r) s r) n) : Identity p q :=
  isMonic_Δ
    (Decipher (Cipher n s r) s r)
    n
    p
    q

end CryptoTopos
