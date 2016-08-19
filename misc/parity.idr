import Language.Reflection.Elab
import Pruviloj

data Parity : Nat -> Type where
    Even : Parity (n + n)
    Odd  : Parity (S (n + n))

parity'_lemma : (rec : Parity ((k + (S acc)) + (S acc))) -> Parity (S (S (plus (plus k acc) acc)))
parity'_lemma {k} {acc} rec =
    rewrite plusSuccRightSucc (S (plus k acc)) acc in
    rewrite plusCommutative (plus k acc) (S acc) in
    rewrite plusSuccRightSucc (S acc) (plus k acc) in
    rewrite plusSuccRightSucc k acc in
    rewrite plusCommutative (S acc) (plus k (S acc)) in
    rec

parity' : (n : Nat) -> (acc : Nat) -> Parity (n + acc + acc)
parity' Z acc = Even {n=acc}
parity' (S Z) acc = Odd {n=acc}
parity' (S (S k)) acc = parity'_lemma $ parity' k (S acc)

-- plus_z_right_neutral : (n : Nat) -> plus n 0 = n
-- plus_z_right_neutral Z = Refl
-- plus_z_right_neutral (S k) = ?zrn
