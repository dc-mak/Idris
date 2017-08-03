module Main

%default total

||| Caluculate the average length of words in a string
||| @str a string containing words separated by whitespace
average : (str : String) -> Double
average str =
    let num_words = word_count str
        total_len = sum (word_lengths (words str)) in

    cast total_len / cast num_words

    where
        word_count : String -> Nat
        word_count str = length (words str)

        word_lengths : List String -> List Nat
        word_lengths strs = map length strs

showAverage : String -> String
showAverage str = "The average world length is: " ++ show (average str) ++ "\n"

partial main : IO ()
main = repl "Enter a string: " showAverage

-- Type constraints: interfaces
double : Num ty => ty -> ty
double x = x * x

twice : (a -> a) -> a -> a
twice f x = f (f x)

Shape : Type
rotate : Shape -> Shape

quadruple : Num a => a -> a
quadruple = twice double

turn_around : Shape -> Shape
turn_around = twice rotate

-- Exercises

{- Ex 1: Types
    1 - (String, String, String)
    2 - List String
    3 - ((Char, String), Char)
-}

-- Ex 2-5: Palindrome checker
palindrome : Nat -> String -> Bool
palindrome n x =
  length x > n && let x' = toLower x in x' == reverse x'

-- Ex 6: Word and letter counter
counts : String -> (Nat, Nat)
counts str =
  let wrd = words str in
  (length wrd, sum (map length wrd))

-- Ex 7: Top ten
top_ten : Ord a => List a -> List a
top_ten xs = take 10 (sort xs)

-- Ex 8: How many strings over a certain length?
over_length : Nat -> List String -> Nat
over_length n xs = length $ filter ((> n) . Strings.length) xs


-- Ex 9: Complete programs for palindrome and counts
parse_palindrome : String -> String
parse_palindrome x =
  let (num, palin) = span (/= ' ') x in
  if palindrome (cast num) (trim palin) then
    "YES\n"
  else
    "NO\n"

partial
interactive_palindrome : IO ()
interactive_palindrome = repl "Enter a string: " parse_palindrome

parse_counts : String -> String
parse_counts str =
  let (words, letters) = counts str in
  "Words: " ++ c2 words ++ " | Letters: " ++ c2 letters ++ "\n"

  where
      c2 : Nat -> String
      c2 = cast . cast {to=Int}

partial
interactive_counts : IO ()
interactive_counts = repl "Enter a string: " parse_counts
