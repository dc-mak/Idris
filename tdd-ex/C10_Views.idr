import TDD.Chapter10.DataStore
import TDD.Chapter10.Shape
import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views

-- Ex 10.1.6: 1
data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) =
  case takeN k xs of
      Fewer => Fewer
      Exact n_xs => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (groupByN (length xs `div` 2) xs)
  halves xs | [] = ([], []) -- tried to say `impossible` but compiler
  halves xs | [y] = (y, []) -- wasn't too happy about it
  halves xs | (l :: r :: _) = (l, r)

-- Ex 10.2.5: 1) equal suffixes
total
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix as bs with (snocList as)
  equalSuffix [] bs | Ytpme = []
  equalSuffix (xs ++ [x]) bs | (Snoc xsrec) with (snocList bs)
    equalSuffix (xs ++ [x]) [] | (Snoc xsrec) | Ytpme = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      if x == y then equalSuffix xs ys | xsrec | ysrec ++ [x] else []

-- 2) mergeSort
total
mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec) =
    merge (mergeSort ys | lrec) (mergeSort zs | rrec)

-- 3) toBinary
total
toBinary : Nat -> String
toBinary n with (halfRec n)
  toBinary Z | HalfRecZ = ""
  toBinary (x + x) | (HalfRecEven rec) = toBinary x | rec ++ "0"
  toBinary (S (x + x)) | (HalfRecOdd rec) = toBinary x | rec ++ "1"

-- 4) palindrome
palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) =
    x == y && palindrome ys | rec

-- Ex 10.3.4: 1) getValues
getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues store with (storeView store)
  getValues _ | SNil = []
  getValues (addToStore (_, v) store) | (SAdd rec) = v :: getValues store | rec

-- 2)
triangle : Double -> Double -> Shape
triangle = Triangle

rectangle : Double -> Double -> Shape
rectangle = Rectangle

circle : Double -> Shape
circle = Circle

data ShapeView : Shape -> Type where
  STriangle : ShapeView (triangle base height)
  SRectangle : ShapeView (rectangle width height)
  SCircle : ShapeView (circle radius)

shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle

area : Shape -> Double
area x with (shapeView x)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius
