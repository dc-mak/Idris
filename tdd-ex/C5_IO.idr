import System
import Data.Vect

%default total

print_length : IO ()
print_length =
    putStr "Input string: " >>= \_ =>
    getLine >>= \input =>
    let len = length input in
    putStrLn (show len)

-- 5.1.4: Ex 1 (skipped 2)
readTwoThenLonger : IO ()
readTwoThenLonger = do
    x1 <- getLine
    x2 <- getLine
    let len = max (length x1) (length x2) -- no `in` required
    printLn len

readNumber : IO (Maybe Nat)
readNumber = do
    input <- getLine
    if all isDigit (unpack input) then
        pure (Just (cast input))
    else
        pure Nothing

readNumbers : IO (Maybe (Nat, Nat))
readNumbers = do
    Just num1 <- readNumber | Nothing => pure Nothing
    Just num2 <- readNumber | Nothing => pure Nothing
    pure $ Just (num1, num2)

-- After a couple of hours of messing around and a few internal errors
readPair : IO (Maybe (Nat, Nat))
readPair = pure ([| MkPair !readNumber !readNumber |])
-- !(!x) or nested [||] don't work - usually just expects the same type constructors
-- e.g. IO (IO a) or Maybe (Maybe a)... should that be an error/bug?
-- It would be nice to do pure $ Just $ (!!readNumber, !!readNumber) but I don't
-- think that type checks the way I want it to.


-- 5.2.4: Ex 1/3
partial guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
     putStr ("Enter a guess (" ++ show guesses ++ ") - ")
     case [| (compare target) !readNumber |] of
        Nothing =>
          tryAgain "Enter a valid number"

        (Just LT) =>
          tryAgain "Too high"

        (Just GT) =>
          tryAgain "Too low"

        (Just EQ) => do
          putStrLn "Correct!"
          pure ()

where
    partial tryAgain : String -> IO ()
    tryAgain str = do
        putStrLn str
        guess target guesses

-- Ex 2
partial main : IO ()
main = do
    guess (cast (!time `mod` 101)) 0

-- Ex 4
partial repl' : (prompt : String) -> (func : String -> String) -> IO ()
repl' prompt func = do
    putStr prompt
    putStr (func !getLine)
    repl' prompt func

-- 5.3.5: Ex 1
partial readToBlank : IO (List String)
readToBlank = do
    case !getLine of
        "" => pure []
        str => [| (str :: ) readToBlank |]

-- Ex 2
partial readAndSave : IO ()
readAndSave = do
    input <- readToBlank
    Right () <- writeFile (!getLine) (foldr (\elem,acc => " " ++ elem ++ acc) "" input)
      | Left (GenericFileError x) => putStrLn ("Error code: " ++ show x)
      | Left FileReadError => putStrLn "Error: reading file"
      | Left FileWriteError => putStrLn "Error: writing file"
      | Left FileNotFound => putStrLn "Error: finding file"
      | Left PermissionDenied => putStrLn "Error: permission denied"
    pure ()

-- Ex 3: Doesn't seem to work at the REPL just yet
readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
    Right handle <- openFile filename Read
      | Left _ => pure (Z ** [])
    read_vect_from handle

where
    read_vect_from : File -> IO (n ** Vect n String)
    read_vect_from f =
        if !(fEOF f) then
            pure (Z ** [])
        else do
            Right x <- fGetLine f
              | Left _ => pure (Z ** [])
            (k ** xs) <- assert_total (read_vect_from f)
            pure (S k ** x :: xs)

testReadVectFile : IO ()
testReadVectFile = do
    (k ** xs) <- readVectFile "test.txt"
    printLn xs
