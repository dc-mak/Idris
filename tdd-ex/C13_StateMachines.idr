import Data.Vect

%default total

-- Given code
data DoorState = DoorOpen | DoorClosed

data DoorCmd : Type -> DoorState -> DoorState -> Type where
     Open : DoorCmd () DoorClosed DoorOpen
     Close : DoorCmd () DoorOpen DoorClosed 
     RingBell : DoorCmd () any any -- 13.1.5

--      Pure : ty -> DoorCmd ty state state
--      (>>=) : DoorCmd a state1 state2 ->
--              (a -> DoorCmd b state2 state3) ->
--              DoorCmd b state1 state3
--
-- doorProg : DoorCmd () DoorClosed DoorClosed
-- doorProg = do RingBell
--               Open
--               RingBell
--               Close

-- 13.5.2
data GuessCmd : Type -> Nat -> Nat -> Type where
  Try : Integer -> GuessCmd Ordering (S guesses) guesses
  -- Pure : ty -> GuessCmd ty state state
  -- (>>=) : GuessCmd a state1 state2
  --         -> (a -> GuessCmd b state2 state3)
  --         -> GuessCmd b state1 state3

-- 13.5.3
data Matter = Solid | Liquid | Gas

-- data MatterCmd : Type -> Matter -> Matter -> Type where
--   Melt : MatterCmd () Solid Liquid
--   Boil : MatterCmd () Liquid Gas
--   Condense : MatterCmd () Gas Liquid
--   Freeze : MatterCmd () Liquid Solid
--
--   (>>=) : MatterCmd a s1 s2 -> (a -> MatterCmd b s2 s3) -> MatterCmd b s1 s3
--
-- iceSteam : MatterCmd () Solid Gas
-- iceSteam = do Melt
--               Boil
--
-- steamIce : MatterCmd () Gas Solid
-- steamIce = do Condense
--               Freeze

-- overMelt : MatterCmd () Solid Gas
-- overMelt = do Melt
--               Melt

-- 13.2.4: 1
data StackCmd : Type -> Nat -> Nat -> Type where
     Push : Integer -> StackCmd () height (S height)
     Pop : StackCmd Integer (S height) height
     Top : StackCmd Integer (S height) (S height)

     GetStr : StackCmd String height height
     PutStr : String -> StackCmd () height height

     Pure : ty -> StackCmd ty height height
     (>>=) : StackCmd a height1 height2 ->
             (a -> StackCmd b height2 height3) ->
             StackCmd b height1 height3

runStack : (stk : Vect inHeight Integer) ->
           StackCmd ty inHeight outHeight -> IO (ty, Vect outHeight Integer)
runStack stk (Push val) = pure ((), val :: stk)
runStack (val :: stk) Pop = pure (val, stk)
runStack (val :: stk) Top = pure (val, val :: stk)
runStack stk GetStr = do x <- getLine
                         pure (x, stk)
runStack stk (PutStr x) = do putStr x
                             pure ((), stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do (x', newStk) <- runStack stk x
                            runStack newStk (f x')

testAdd : StackCmd () 0 0
testAdd = do Push 10
             x <- GetStr
             Push (cast x)
             val1 <- Pop
             val2 <- Pop
             PutStr (show (val1 + val2) ++ "\n")

data StackIO : Nat -> Type where
     Do : StackCmd a height1 height2 -> 
          (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
     (>>=) : StackCmd a height1 height2 -> 
             (a -> Inf (StackIO height2)) -> StackIO height1
     (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run (More fuel) stk (Do c f) 
     = do (res, newStk) <- runStack stk c
          run fuel newStk (f res)
run Dry stk p = pure ()

doBinary : (Integer -> Integer -> Integer) -> StackCmd () (S (S height)) (S height)
doBinary f = Push (f !Pop !Pop)

doNegate : StackCmd () (S height) (S height)
doNegate = Push (negate !Pop)

mutual
  tryBinary : (Integer -> Integer -> Integer) -> StackIO height
  tryBinary f {height = (S (S h))} = do
    doBinary f
    PutStr (show !Top ++ "\n")
    stackCalc

  tryBinary _ = do
    PutStr "Fewer than two items on the stack\n"
    stackCalc

  tryNegate : StackIO height
  tryNegate {height = (S h)} = do
    doNegate
    PutStr (show !Top ++ "\n")
    stackCalc

  tryNegate = do
    PutStr "Fewer than two items on the stack\n"
    stackCalc

  discard : StackIO height
  discard {height = S h} = do
    PutStr ("Discarded " ++ show !Top ++ "\n")
    Pop
    stackCalc

  discard = do
    PutStr "Empty stack\n"
    stackCalc

  duplicate : StackIO height
  duplicate {height = S h} = do
    x <- Top
    Push x
    stackCalc

  duplicate = do
    PutStr "Empty stack\n"
    stackCalc

  data StkInput = Number Integer | Add | Subtract | Multiply | Discard | Negate | Duplicate

  strToInput : String -> Maybe StkInput
  strToInput "add" = Just Add
  strToInput "subtract" = Just Subtract
  strToInput "multiply" = Just Multiply
  strToInput "negate" = Just Negate
  strToInput "discard" = Just Discard
  strToInput "duplicate" = Just Duplicate
  strToInput x = if all isDigit (unpack x) 
                    then Just (Number (cast x))
                    else Nothing

  stackCalc : StackIO height
  stackCalc = do
    PutStr "> "
    input <- GetStr
    case strToInput input of
         Nothing => do {PutStr "Invalid input\n"; stackCalc}
         Just (Number x) => do {Push x; stackCalc}
         Just Add => tryBinary (+)
         Just Subtract => tryBinary (-)
         Just Multiply => tryBinary (*)
         Just Negate => tryNegate
         Just Discard => discard
         Just Duplicate => duplicate

partial
main : IO ()
main = run forever [] stackCalc
