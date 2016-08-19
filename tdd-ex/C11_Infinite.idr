import Data.Primitives.Views
import System

%default total
-- Ex 11.1.7: 1
every_other : Stream a -> Stream a
every_other (_ :: x :: xs) = x :: every_other xs

-- 2
[myFunctor] Functor Stream where
    map f (x :: xs) = f x :: map f xs

-- 3
data Face = Heads | Tails

-- NOTE: divides uses believe_me to generate the proofs, since it is working with
-- primitives. This means, missing or unreachable patterns go through to the first
-- case, but exact matches are treated correctly.
-- Also means NO EXHAUSTIVENESS CHECKS
getFace : Int -> Face
getFace n with (divides n 2)
  getFace (2 * _ + 0) | (DivBy _) = Heads
  getFace (2 * _ + 1) | (DivBy _) = Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count xs = take count (map getFace xs)

-- 4
square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx =
  let approx' = (approx + (number / approx)) / 2 in
  approx :: (square_root_approx number approx')

-- 5
square_root_bound : (max : Nat) ->
                    (number : Double) ->
                    (bound : Double) ->
                    (approxs : Stream Double) ->
                    Double
square_root_bound Z _ _ (value :: _) = value
square_root_bound (S k) number bound (value :: xs) =
  if abs (number - value * value) < bound then value else 
    square_root_bound k number bound xs

square_root : (number : Double) -> Double
square_root number =
  square_root_bound 100 number 0.00000000001
                    (square_root_approx number number)

-- 11.2.7
namespace InfIO

    data InfIO : Type where
      Do : IO a -> (a -> Inf InfIO) -> InfIO

    (>>=) : IO a -> (a -> Inf InfIO) -> InfIO
    (>>=) = Do

    totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
    totalREPL prompt action = 
      do  putStrLn prompt
          putStrLn (action !getLine)
          totalREPL prompt action

-- 11.3.4, 1/2
data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String

     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

     ReadFile : String -> Command (Either FileError String)
     WriteFile : String -> String -> Command (Either FileError ())

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure val) = pure val
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)
runCommand (ReadFile f) = readFile f
runCommand (WriteFile f s) = writeFile f s

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run fuel (Quit val) = do pure (Just val)
run (More fuel) (Do c f) = do res <- runCommand c
                              run fuel (f res)
run Dry p = pure Nothing

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

mutual
  correct : Stream Int -> (score : Nat) -> (tot : Nat) -> ConsoleIO (Nat, Nat)
  correct nums score tot
          = do PutStr "Correct!\n"
               quiz nums (score + 1) (tot + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> (tot : Nat) -> ConsoleIO (Nat, Nat)
  wrong nums ans score tot
        = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
             quiz nums score (tot + 1)

  data Input = Answer Int
             | QuitCmd

  readInput : (prompt : String) -> Command Input
  readInput prompt 
     = do PutStr prompt
          answer <- GetLine
          if toLower answer == "quit" 
             then Pure QuitCmd 
             else Pure (Answer (cast answer))

  quiz : Stream Int -> (score : Nat) -> (tot : Nat) -> ConsoleIO (Nat, Nat)
  quiz (num1 :: num2 :: nums) score tot
     = do PutStr ("Score so far: " ++ show score ++ " / " ++ show tot ++ "\n")
          input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
          case input of
               Answer answer => if answer == num1 * num2 
                                   then correct nums score tot
                                   else wrong nums (num1 * num2) score tot
               QuitCmd => Quit (score, tot)

partial
forever : Fuel
forever = More forever

partial
main : IO ()
main = do seed <- time
          Just (score, tot) <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
               | Nothing => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show score ++ " / " ++ show tot)

-- 3
mutual

    actionCat : (file : String) -> Command ()
    actionCat file = do
        case !(ReadFile file) of 
            (Right r) => do PutStr (r ++ "\n"); Pure ()
            (Left _) => do PutStr ("Error\n"); Pure ()

    actionCopy : (from : String) -> (to : String) -> Command ()
    actionCopy from to =
      do  Right contents <- ReadFile from
              | Left _ => do PutStr "Error reading\n"; Pure ()
          Right _ <- WriteFile to contents
              | Left _ => do PutStr "Error writing\n"; Pure ()
          Pure ()

    data Action
      = Cat String
      | Copy String String
      | Exit

    getAction : Command (Maybe Action)
    getAction = do
        case words !GetLine of 
            "cat" :: filename :: _ =>
                Pure (Just $ Cat filename)

            "copy" :: source :: dest :: _ =>
                 Pure (Just $ Copy source dest)

            ["exit"] =>
                 Pure (Just Exit)

            _ =>
                  Pure Nothing

    shell : ConsoleIO ()
    shell = do  PutStr ("$ " )
                case !getAction of
                    Nothing => do PutStr ("Unrecognized command\n"); shell
                    (Just (Cat file)) => do actionCat file; shell
                    (Just (Copy from to)) => do actionCopy from to; shell
                    (Just Exit) => Quit ()

partial
runShell : ConsoleIO () -> IO ()
runShell (Quit ()) = do  pure ()
runShell (Do c f) = do  res <- runCommand c
                        runShell (f res)

