%default total

MyReader : Type -> Type -> Type
MyReader a b = a -> b

rmap : (a -> b) -> MyReader c a -> MyReader c b
rmap = (.)

n_just : Bool -> MyReader Bool a -> Maybe a
n_just x f = Just $ f x

n1 : MyReader Bool a -> Maybe a
n1 = n_just True

proof_n1 : Eq a =>
           (x : MyReader Bool a) ->
           (g : a -> b) ->
           map g (n1 x) = n1 (rmap g x)
proof_n1 x g = Refl

n2 : MyReader Bool a -> Maybe a
n2 = n_just False

proof_n2 : Eq a =>
           (x : MyReader Bool a) ->
           (g : a -> b) ->
           map g (n2 x) = n2 (rmap g x)
proof_n2 x g = Refl

n3 : MyReader Bool a -> Maybe a
n3 _ = Nothing

proof_n3 : Eq a =>
           (x : MyReader Bool a) ->
           (g : a -> b) ->
           map g (n3 x) = n3 (rmap g x)
proof_n3 x g = Refl

-- Horizontal composition of natural transformations

maybeToList : Maybe a -> List a
maybeToList Nothing = []
maybeToList (Just x) = [x]

-- Maybe (MyReader Bool a) -> List (Maybe a)

maybe_rmap : (a -> b) -> List (Maybe a) -> List (Maybe b)
maybe_rmap = map . map

other_rmap : (a -> b) -> Maybe (MyReader Bool a) -> Maybe (MyReader Bool b)
other_rmap f (Just g) = Just $ f . g
other_rmap f Nothing = Nothing

comp : (f : Maybe a -> List a) -> 
       (g: MyReader Bool a -> Maybe a) ->
       Maybe (MyReader Bool a) -> List (Maybe a)
comp f g (Just h) = [g h]
comp f g Nothing = []

proof_comp : (x : Maybe (MyReader Bool a)) ->
             (f : a -> b) ->
             maybe_rmap f ((maybeToList `comp` n1) x) =
               (maybeToList `comp` n1) (other_rmap f x)
