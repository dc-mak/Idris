%default total

-- Nats in the PLC
PLCNat : Type
PLCNat = (a : Type) -> (x : a) -> (f : a -> a) -> a

zero : PLCNat
zero a x f = x

succ' : PLCNat -> PLCNat
succ' y b x f = f (y b x f)

iter' : (a : Type) -> (x : a) -> (f : a -> a) -> (n : PLCNat) -> a
iter' a x f n = n a x f

add : PLCNat -> PLCNat -> PLCNat
add m n = iter' PLCNat m succ' n

multiply : PLCNat -> PLCNat -> PLCNat
multiply m n = iter' PLCNat zero (add m) n

Show PLCNat where
  show n = show $ n Int 0 (+1)

-- Leibniz Equality
Prop : Type
Prop = Type

Conj : (p:Prop) -> (q:Prop) -> Type
Conj p q = (r:Prop) -> (p -> q -> r) -> r

Bimp : (p:Prop) -> (q:Prop) -> Type
Bimp p q = Conj (p -> q) (q -> p)

LeibEq : (A:Type) -> (x:A) -> (y:A) -> Type
LeibEq A x y = (P : A -> Prop) -> Bimp (P x) (P y)

LEq' : (A:Type) -> (x:A) -> (y:A) -> Type
LEq' A x y = (P : A -> Prop) -> (P x) -> (P y)

F : (A:Type) -> (x:A) -> (y:A) -> (LeibEq A x y) -> (LEq' A x y)
F A x y eq = \p => \px => eq p (p x -> p y) (\p,q => p) px

G : (A:Type) -> (x:A) -> (y:A) -> (LEq' A x y) -> (LeibEq A x y)
G A x y eq = \p => \r => \f => f (eq p) (eq (\z => p z -> p x) id)

-- Existentials
ExistsFor : (T : Type -> Type) -> Type
ExistsFor T = (b:Type) -> ((a:Type) -> T a -> b) -> b

pack : (T : Type -> Type) ->
       (a : Type) ->
       (m : T a) ->
       ExistsFor T
pack T a m = \b => \f => f a m

unpack : (T : Type -> Type) ->
         (exists : ExistsFor T) ->
         (b : Type) ->
         ((a : Type) -> (x : T a) -> b) ->
         b
unpack T exists b f = exists b f

-- Dependent Records aka ML-style Modules
record Equals a where
  constructor MkEquals
  eq : a -> a -> bool

eqInt : Equals Int
eqInt = MkEquals (==)

record Set a where
  constructor MkSet
  eq : Equals a
  t : Type -> Type
  empty : t a
  insert : t a -> t a -> t a
  remove : t a -> t a -> t a
  union : t a -> t a -> t a
  powerset : t a -> t a

