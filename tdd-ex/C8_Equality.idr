import Data.Vect

%default total

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
    Same : (num : Nat) -> EqNat num num


sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS j j (Same j) = Same (S j)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) =
    case checkEqNat k j of
        Nothing => Nothing
        (Just eq) => Just (sameS _ _ eq)

exactLen : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLen {m} len input =
    case checkEqNat m len of
        Nothing =>
            Nothing

        Just (Same len) =>
            Just input

-- 8.1.7: Ex 1 
same_cons : {xs : List a} -> {ys : List a} -> (xs = ys) -> (x :: xs = x :: ys)
same_cons prf = cong prf

-- Ex 2
same_lists : {xs : List a} -> {ys : List a} -> (x = y) -> (xs = ys) -> (x :: xs = y :: ys)
same_lists {x} {y} {xs} {ys} prf_hd prf_tl =
    trans (cong {f = (:: xs)} prf_hd) (cong {f = (y ::)} prf_tl)

-- Ex 3
data ID : Type -> Type where
    I : (a : ty) -> ID ty

-- Ex 3:
data ThreeEq : (a : t) -> (b : t) -> (c : t) -> Type where
    AllEq : (x : t) -> ThreeEq x x x

-- Ex 4: Maybe the type should carry a proof? Or is that for a user to do?
allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (AllEq z) = AllEq (S z)

where
    reverseProof : Vect (k + 1) elem -> Vect (S k) elem
    reverseProof {k} result =
        rewrite plusCommutative 1 k in
        result

-- 8.2.6 Ex 1
my_plusCommutes : (n : Nat) -> (m : Nat) -> (n + m = m + n)
my_plusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
my_plusCommutes (S k) m =
    let rec = my_plusCommutes k m in
    rewrite sym $ plusSuccRightSucc m k in
    cong rec

-- Ex 2
my_reverse : Vect n a -> Vect n a
my_reverse xs = reverse' [] xs
where
    reverse' : Vect n a -> Vect m a -> Vect (n + m) a
    reverse' {n} {m = Z} acc [] = rewrite plusZeroRightNeutral n in acc
    reverse' {n} {m = S k} acc (x :: xs) =
        rewrite sym $ plusSuccRightSucc n k in
        reverse' (x :: acc) xs

--  8.3.4 Ex 1
head_unequal : DecEq a =>
    {xs : Vect n a} -> {ys : Vect n a } ->
    (contra_xy  : (x = y) -> Void) ->
    (x :: xs = y :: ys) -> Void

head_unequal contra_xy prf =
    contra_xy $ cong {f = Vect.head} prf

tail_unequal : DecEq a =>
    {xs : Vect n a} -> {ys : Vect n a} ->
    (contra_xys : (xs = ys) -> Void) ->
    (x :: xs = y :: ys) -> Void

tail_unequal contra_xys prf =
    contra_xys $ cong {f = Vect.tail} prf

-- Ex 2
eq_vectors : DecEq a => (x1 : Vect n a) -> (x2 : Vect n a) -> Dec (x1 = x2)
eq_vectors [] [] = Yes Refl
eq_vectors (x :: xs) (y :: ys) =
    case eq_vectors xs ys of
        No contra_tl =>
            No (tail_unequal contra_tl)

        Yes prf_tl =>
            case decEq x y of
                Yes prf_xy =>
                    let prf_xs = cong {f = (x ::)} prf_tl
                        prf_y  = cong {f = (:: ys)} prf_xy in
                    Yes (trans prf_xs prf_y)

                No contra_xy =>
                    No (head_unequal contra_xy)

-- 9.1.6 Ex 1
data MyElem : a -> List a -> Type where
    MyHere : MyElem x (x :: xs)
    MyThere : (later : MyElem x xs) -> MyElem x (y :: xs)

-- Ex 2: Simply doesn't work nicely without auto prf for LastOne

data Last : List a -> a -> Type where
    LastOne : {auto prf : lst = value} -> Last [lst] value
    LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] a) where
    uninhabited LastOne impossible
    uninhabited (LastCons _) impossible

lastNotEq : (x = value -> Void) -> Last [x] value -> Void
lastNotEq contra (LastOne {prf}) = contra prf
lastNotEq _ (LastCons LastOne) impossible
lastNotEq _ (LastCons (LastCons _)) impossible

notLast : (Last (y :: ys) value -> Void) -> Last (x :: y :: ys) value -> Void
notLast contra (LastCons prf) = contra prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No uninhabited
isLast [x] value =
    case decEq x value of
        Yes prf => Yes LastOne 
        No contra => No (lastNotEq contra)

isLast (x :: y :: ys) value =
    case isLast (y :: ys) value of
        Yes prf => Yes (LastCons prf) 
        No contra => No (notLast contra)
