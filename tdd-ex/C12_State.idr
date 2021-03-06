import Control.Monad.State
import Data.Primitives.Views
import System

%default total

-- 12.1.5: 1
update : (stateType -> stateType) -> State stateType ()
update f = put $ f !get
-- update = (get >>=) . (put .)

increase : Nat -> State Nat ()
increase x = update (+x)

-- 12.1.5: 2
data Tree a = Empty | Node (Tree a) a (Tree a)
countEmpty : Tree a -> State Nat ()
countEmpty Empty = increase 1
countEmpty (Node l _ r) = do countEmpty l
                             countEmpty r

testTree : Tree Int
testTree = Node (Node (Node Empty 0 Empty) 1 (Node Empty 2 Empty))
                3
                (Node (Node Empty 4 Empty) 5 (Node Empty 6 Empty))

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update $ \(e,n) => (e+1,n)
countEmptyNode (Node l _ r) = do countEmptyNode l
                                 update $ \(e,n) => (e,n+1)
                                 countEmptyNode r

-- Given Code
record Score where
       constructor MkScore
       correct : Nat
       attempted : Nat

record GameState where
       constructor MkGameState
       score : Score
       difficulty : Int

Show GameState where
    show st = show (correct (score st)) ++ "/"
              ++ show (attempted (score st)) ++ "\n"
              ++ "Difficulty: " ++ show (difficulty st)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1) }

addCorrect : GameState -> GameState
addCorrect = record { score->correct $= (+1),
                      score->attempted $= (+1) }

setDifficulty : Int -> GameState -> GameState
setDifficulty newDiff state = record { difficulty = newDiff } state

data Command : Type -> Type where
     PutStr : String -> Command ()
     GetLine : Command String

     GetRandom : Command Int
     GetGameState : Command GameState
     PutGameState : GameState -> Command ()

     Pure : ty -> Command ty
     Bind : Command a -> (a -> Command b) -> Command b

-- 12.3.7: 2 
Functor Command where
  map f x = Bind x $ \x => Pure $ f x
  -- map f x = pure $ f !x   -- This gets an internal compiler error
  -- map f x = do y <- x     -- This has totality issues
  --              pure $ f y

Applicative Command where
  pure = Pure
  (<*>) f x = Bind f $ \f => Bind x $ \x => Pure $ f x
  -- (<*>) f a = pure $ !f !a  -- This gets an internal compiler error
  -- (<*>) f a = do g <- f     -- This has totality issues
  --                b <- a
  --                pure $ g b

Monad Command where
  (>>=) = Bind

data ConsoleIO : Type -> Type where
     Quit : a -> ConsoleIO a
     Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                   (seed' `shiftR` 2) :: randoms seed'


runCommand : Stream Int -> GameState -> Command a -> 
             IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do putStr x
                                      pure ((), rnds, state)
runCommand rnds state GetLine = do str <- getLine
                                   pure (str, rnds, state)

runCommand (val :: rnds) state GetRandom
      = pure (getRandom val (difficulty state), rnds, state)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1
runCommand rnds state GetGameState 
      = pure (state, rnds, state)
runCommand rnds state (PutGameState newState) 
      = pure ((), rnds, newState)

runCommand rnds state (Pure val)
      = pure (val, rnds, state)
runCommand rnds state (Bind c f)
      = do (res, newRnds, newState) <- runCommand rnds state c
           runCommand newRnds newState (f res)

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> 
      IO (Maybe a, Stream Int, GameState)
run fuel rnds state (Quit val) = do pure (Just val, rnds, state)
run (More fuel) rnds state (Do c f) 
     = do (res, newRnds, newState) <- runCommand rnds state c
          run fuel newRnds newState (f res)
run Dry rnds state p = pure (Nothing, rnds, state)

-- 12.3.7: 1
updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = PutGameState $ f !GetGameState
-- updateGameState = (GetGameState >>=) . (PutGameState .)

mutual
  correct : ConsoleIO GameState
  correct = do PutStr "Correct!\n"
               updateGameState addCorrect
               quiz 

  wrong : Int -> ConsoleIO GameState
  wrong ans 
        = do PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
             updateGameState addWrong
             quiz 
  
  data Input = Answer Int
             | QuitCmd

  readInput : (prompt : String) -> Command Input
  readInput prompt 
     = do PutStr prompt
          answer <- GetLine
          if toLower answer == "quit" 
             then Pure QuitCmd 
             else Pure (Answer (cast answer))

  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            st <- GetGameState
            PutStr (show st ++ "\n")

            input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
            case input of
               Answer answer => if answer == num1 * num2 
                                   then correct
                                   else wrong (num1 * num2) 
               QuitCmd => Quit st

partial
main : IO ()
main = do seed <- time
          (Just score, _, state) <- 
              run forever (randoms (fromInteger seed)) initState quiz
                  | _ => putStrLn "Ran out of fuel"
          putStrLn ("Final score: " ++ show state)

-- 12.3.7: 3
record Votes where
  constructor MkVotes
  upvotes : Integer
  downvotes : Integer

record Article where
  constructor MkArticle
  title : String
  url : String
  score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)
-- initPage = ((flip apply $ MkVotes 0 0) .) . MkArticle
-- initPage = flip flip (MkVotes 0 0) . MkArticle

getScore : Article -> Integer
getScore article = (upvotes $ score $ article) - (downvotes $ score $ article)

addUpvote : Article -> Article
addUpvote = record { score->upvotes $= (+1) }

addDownvote : Article -> Article
addDownvote = record { score->downvotes $= (+1) }
