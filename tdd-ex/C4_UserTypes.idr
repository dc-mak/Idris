import Data.Vect

%default total

data Direction
    = North
    | East
    | South
    | West

turn_clockwise : Direction -> Direction
turn_clockwise North = East
turn_clockwise East = South
turn_clockwise South = West
turn_clockwise West = North

||| Represents a shape
data Shape =
    ||| Triangle with base and height
    Triangle Double Double
  | ||| Rectangle with width and height
    Rectangle Double Double
  | ||| A circle with its radius
    Circle Double

%name Shape shape, shape_1, shape_2

data Picture =
    Primitive Shape

  | Combine Picture Picture

  | Rotate Double Picture

  | Translate Double Double Picture

%name Picture pic, pic_1, pic_2

rect : Picture
rect = Primitive (Rectangle 20 10)

circle : Picture
circle = Primitive (Circle 5)

tri : Picture
tri = Primitive (Triangle 10 10)

test_picture : Picture
test_picture =
  Combine
    (Translate 5 5 rect)
    (Combine
      (Translate 35 5 circle)
      (Translate 15 25tri))

area : (shape : Shape) -> Double
area (Triangle x y) = 0.5 * x * y
area (Rectangle x y) = x * y
area (Circle r) = pi * r * r

picture_area : Picture -> Double
picture_area (Primitive shape) = area shape
picture_area (Combine pic pic_1) = picture_area pic + picture_area pic_1
picture_area (Rotate x pic) = picture_area pic
picture_area (Translate x y pic) =  picture_area pic

data BSTree : Type -> Type where
     Empty :
        Ord elem =>
        BSTree elem

     Node :
        Ord elem =>
        (left : BSTree elem) ->
        (val : elem) ->
        (right : BSTree elem) ->
        BSTree elem

%name BSTree tree, tree1

insert : Ord elem => elem -> BSTree elem -> BSTree elem
insert x Empty = Node Empty x Empty
insert x t@(Node left val right) =
    case compare x val of
         LT => Node (insert x left) val right
         EQ => t
         GT => Node left val (insert x right)

-- 4.1.5: Ex 1
listToTree : Ord a => List a -> BSTree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

-- Ex 2
treeToList : BSTree a -> List a
treeToList Empty = []
treeToList (Node left val right) =
    treeToList left ++ [val] ++ treeToList right

-- Ex 3
data Expr =
    Gnd Int
  | Pls Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr

-- Ex 4
eval : Expr -> Int
eval (Gnd x) = x
eval (Pls x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x - eval y

-- Ex 5
maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
-- maxMaybe x y = [| max x y |] -- a nice little trick
maxMaybe Nothing y = y
maxMaybe x Nothing = x
maxMaybe (Just x) (Just y) = Just (max x y)

-- Ex 6
triArea : (shape : Shape) -> Maybe Double
triArea t@(Triangle x y) = Just (area t)
triArea _ = Nothing

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive shape) = triArea shape
biggestTriangle (Combine pic pic_1) = maxMaybe (biggestTriangle pic) (biggestTriangle pic_1)
biggestTriangle (Rotate x pic) = biggestTriangle pic
biggestTriangle (Translate x y pic) = biggestTriangle pic

-- 4.2.4: Ex 1 and 2
data PowerSource = Petrol | Pedal | Electric

data Vehicle : PowerSource -> Type where
    Bicycle : Vehicle Pedal
    Unicycle : Vehicle Pedal
    Motorcycle : (fuel : Nat) -> Vehicle Petrol
    Car : (fuel : Nat) -> Vehicle Petrol
    Bus : (fuel : Nat) -> Vehicle Petrol
    Tram : Vehicle Electric
    ElCar : Vehicle Electric

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels Unicycle = 1
wheels (Motorcycle fuel) = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Tram = 10
wheels ElCar = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 50
refuel Unicycle impossible
refuel Bicycle impossible
refuel Tram impossible
refuel ElCar impossible

-- Examples
app_vect: Vect n a -> Vect m a -> Vect (n + m) a
app_vect [] ys = ys
app_vect (x :: xs) ys = x :: app_vect xs ys

zip_vect: Vect n a -> Vect n b -> Vect n (a, b)
zip_vect[] [] = []
zip_vect(x :: xs) (y :: ys) = (x, y) :: zip_vect xs ys

-- *Has* to be n from the type level, not `length xs`
tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs =
    case integerToFin i n of
      Nothing => Nothing
      Just idx => Just (index idx xs)

   -- do idx <- integerToFin i n
   --    pure (index idx xs)

   -- map (\idx => index idx xs) $ integerToFin i n

-- Ex 3 and 4: proof search did most of the work, although it won't accept
-- take_vect (FS _) [] impossible
-- directly: I suspect because it using an inductive proof
take_vect : (m : Fin (S n)) -> Vect n a  -> Vect (cast m) a
take_vect FZ _ = []
take_vect (FS x) (y :: xs) = y :: take_vect x xs
take_vect (FS FZ) [] impossible
take_vect (FS (FS _)) [] impossible

-- Ex 5
sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys =
    case integerToFin pos n of
         Nothing => Nothing
         Just x => Just (index x xs + index x ys)

-- Interactive Data Store
-- 4.3.5:
-- Ex 1: Add size command
-- Ex 2: Add search command
-- Ex 3: which also prints
data Command =
    Add String
  | Get Integer
  | Size
  | Search String
  | Quit

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "search" substr = Just (Search substr)
parseCommand "get" val =
    case all isDigit (unpack val) of
        False => Nothing
        True => Just (Get (cast val))

parseCommand "quit" "" = Just Quit
parseCommand "size" "" = Just Size
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input =
    case span (/= ' ') input of
         (cmd, args) => parseCommand cmd (ltrim args)

data DataStore : Type where
    MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' _) = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData _ items') = items'


addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (items ++ [newitem])

getEntry : (pos : Integer) -> (store : DataStore) -> (input : String) -> Maybe (String, DataStore)
getEntry pos store input =
    let store_items = items store in
    case integerToFin pos (size store) of
        Nothing => Just ("Out of range\n", store)
        Just id => Just (index id store_items ++ "\n", store)

getSubstrs : String -> DataStore -> List (Nat, String)
getSubstrs substr (MkData _ items) =
    filter (\(_, str) => isInfixOf substr str) (indices 0 items)
    where
        indices : Nat -> Vect n a -> List (Nat, a)
        indices _ [] = []
        indices acc (x :: xs) = (acc, x) :: indices (S acc) xs


processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
    case parse input of
        Nothing => Just ("Invalid Command\n", store)
        Just (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
        Just (Get pos) => getEntry pos store input
        Just Quit => Nothing
        Just Size => Just (show  (size store) ++ "\n", store)
        Just (Search substr) => Just (show (getSubstrs substr store) ++ "\n", store)

partial main : IO ()
main = replWith (MkData _ []) "Command: " processInput
