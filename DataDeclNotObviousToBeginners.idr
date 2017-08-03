data Tree a
  = Lf
  | Br (Tree a) a (Tree a)

data Trie : c : Type -> Type where
  Lv : Trie c
  Bv : {b : Type} -> Trie a -> a -> Trie a -> Trie a

x : Trie Int
x = Br $ Lv 1 Lf
