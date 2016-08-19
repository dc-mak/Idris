data Shape : Type where
    Triangle : (base : Double) -> (height : Double) -> Shape
    Rectangle : (base : Double) -> (height : Double) -> Shape
    Circle : (radius : Double) -> Shape

area : (shape : Shape) -> Double
area (Triangle x y) = 0.5 * x * y
area (Rectangle x y) = x * y
area (Circle r) = pi * r * r

Eq Shape where
    (==) a b = area a == area b

Ord Shape where
    compare a b = compare (area a) (area b)

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)

Num ty => Num (Expr ty) where
    (+) = Add
    (*) = Mul
    fromInteger = Val . fromInteger
    
Neg ty => Neg (Expr ty) where
    negate x = 0 - x
    (-) = Sub
    abs = Abs

-- 7.2.4: Ex 1
Show ty => Show (Expr ty) where 
    show (Val x) = show x
    show (Add x y) = show x ++ " + " ++ show y
    show (Sub x y) = show x ++ " + " ++ show y
    show (Mul x y) = show x ++ " + " ++ show y
    show (Div x y) = show x ++ " + " ++ show y
    show (Abs x) = " | " ++ show x ++ " | "

-- Ex 2
(Eq ty, Neg ty, Integral ty) => Eq (Expr ty) where
    (==) a b = eval a == eval b

-- Ex 3
(Neg ty, Integral ty) => Cast (Expr ty) ty where
    cast = eval

-- 7.3.4: Ex 1
Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add x y) = Add (map f x) (map f y)
  map f (Sub x y) = Sub (map f x) (map f y)
  map f (Mul x y) = Mul (map f x) (map f y)
  map f (Div x y) = Div (map f x) (map f y)
  map f (Abs x) = Abs (map f x)

-- Ex 2
data MyVect : (k : Nat) -> (elem : ty) -> Type where
    Nil : MyVect Z a
    (::) : ty -> MyVect k ty -> MyVect (S k) ty

Eq ty => Eq (MyVect k ty) where
    (==) [] [] = True
    (==) (x :: xs) (y :: ys) = x == y && xs == ys

Foldable (MyVect k) where
    foldl func acc [] = acc
    foldl func acc (x :: xs) = foldl func (func acc x) xs

    foldr func acc [] = acc
    foldr func acc (x :: xs) = func x (foldr func acc xs)
