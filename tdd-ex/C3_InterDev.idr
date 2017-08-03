import Data.Vect

xor : Bool -> Bool -> Bool
xor False y = y
xor True y = not y

mutual
  isEven : Nat -> Bool
  isEven Z = True
  isEven (S k) = isOdd k

  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S k) = isEven k

word_lengths : Vect len String -> Vect len Nat
word_lengths [] = []
word_lengths (word :: words) = length word :: word_lengths words

insert : Ord elem => (x : elem) -> (xs_sorted : Vect k elem) -> Vect (S k) elem
insert x [] = [x]
insert x (y :: xs) =
  case x < y of
       False => y :: insert x xs
       True => x :: y :: xs

ins_sort : Ord elem => Vect n elem -> Vect n elem
ins_sort [] = []
ins_sort (x :: xs) =
  let xs_sorted = ins_sort xs in
  insert x xs_sorted

list_len : List a -> Nat
list_len [] = 0
list_len (x :: xs) = 1 + list_len xs

-- 3.2.4: Ex
list_rev : List a -> List a
list_rev [] = []
list_rev (x :: xs) = list_rev xs ++ [x]

list_map : (a -> b) -> List a -> List b
list_map f [] = []
list_map f (x :: xs) = f x :: map f xs

vect_map: (a -> b) -> Vect n a -> Vect n b
vect_map f [] = []
vect_map f (x :: xs) = f x :: vect_map f xs

tanspose_helper : (x : Vect n elem) -> (xs_trans : Vect n (Vect k elem)) -> Vect n (Vect (S k) elem)
tanspose_helper [] [] = []
tanspose_helper (x :: xs) (y :: ys) = (x :: y) :: tanspose_helper xs ys

create_empties : Vect n (Vect 0 elem)
create_empties = replicate _ []

-- 3.3.3: Ex 3.1
transpose_mat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose_mat [] = create_empties
transpose_mat (x :: xs) =
  let xs_trans = transpose_mat xs in
  zipWith (::) x xs_trans

-- Ex 3.2
addMatrix :
  Num num =>
  Vect rows (Vect cols num) ->
  Vect rows (Vect cols num) ->
  Vect rows (Vect cols num)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

-- Ex 3.3: I read ahead a bit
Matrix : Nat -> Nat -> (elem : Type) -> Type
Matrix rows cols elem = Vect rows (Vect cols elem)

mult_row : Num num => (x : Matrix n m num) -> (y : Vect m num) -> Vect n num
mult_row x y = map (sum . zipWith (*) y) x

mult_rows :
  Num num =>
  (x : Matrix n m num) ->
  (y_trans : Matrix p m num) ->
  Matrix n p num

mult_rows x [] = create_empties
mult_rows x (y :: xs) =
  let rest = mult_rows x xs in
  zipWith (::) (mult_row x y) rest

multMatrix :
  Num num =>
  Matrix n m num ->
  Matrix m p num ->
  Matrix n p num
multMatrix x y =
  let y_trans = transpose_mat y in
  mult_rows x y_trans

create_empties' : Vect n (Vect 0 a)
create_empties' {n = Z} = []
create_empties' {n = (S k)} = [] :: create_empties'
