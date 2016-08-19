{- Syntactic conveniences (a la OCaml)

 - Optional first bar after `data` declaration?
 - Especially since we can't put them in between `TyVar` and `=` `Cons`
 - And doc comments for datatypes is also awful to set out
 - And converting from ADT to GADT syntax is also awful
 - Solution? get rid of/make the bars completely optional
 - and allow naming argument in short hand syntax as well plz

 - Or patterns!

 - case and with: similar concepts but wildly different syntax

 - Optional comma after last element in a list?

 - Modify behaviour of name directive to include something like
 - %name Shape shape{_%COUNT} or have it default to that

 - system: make idr~ files "hidden" by default on Windows

 -}

{- Errors in TDD
 - Source code listing at the end of C4 is inconsistent with previous
 -}
module Main

%default total

natEnumFromThenTo : Nat -> Nat -> Nat -> List Nat
natEnumFromThenTo n inc m =
    case cmp n m of
         CmpLT k =>
            map (plus n . (* (S inc))) (natRange (S (divNatNZ (S k) (S inc) SIsNotZ)))

         CmpEq =>
            []

         CmpGT k =>
            map (minus m . (* (S inc))) (natRange (S (divNatNZ (S k) (S inc) SIsNotZ)))

natEnumFromThen' : (start : Nat) -> (inc : Nat -> Nat) -> Stream Nat
natEnumFromThen' start inc = start :: natEnumFromThen' (inc start) inc

natEnumFromThen : Nat -> Nat -> Stream Nat
natEnumFromThen x y =
    case cmp x y of
        CmpLT k =>
            natEnumFromThen' x (+ (S k))

        CmpEQ =>
            natEnumFromThen' x id

        CmpGT k =>
            natEnumFromThen' (y + S k) (\n => minus n (S k))


{-
syntax "[" [start] "," [next] ".." "]" =
  Main.natEnumFromThen start next
-}

test : Nat -> Nat -> Nat -> List Nat
test = Main.natEnumFromThenTo
