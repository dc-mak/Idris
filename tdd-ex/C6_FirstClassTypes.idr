import Data.Vect

%default total

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True  = Int

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True x = cast x

AdderType : (numargs : Nat) -> Type -> Type
AdderType Z t = t
AdderType (S k) t = (next : t) -> AdderType k t

adder : Num numT => (numargs : Nat) -> (acc : numT) -> AdderType numargs numT
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

data Format = 
    Num Format
  | Str Format
  | Lit String Format
  | End
  | Chr Format
  | Dbl Format

-- 6.2.3: Ex 2 (See before for Ex 1)
PrintfType : Format -> Type
PrintfType (Num fmt) = (i : Int) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Chr fmt) = (chr : Char) -> PrintfType fmt
PrintfType (Dbl fmt) = (i : Double) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Num fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Chr fmt) acc = \chr => printfFmt fmt (acc ++ show chr)
printfFmt (Dbl fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \str => printfFmt fmt (acc ++ str)
printfFmt (Lit str fmt) acc = printfFmt fmt (acc ++ str)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Num (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dbl (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) =
    case toFormat chars of
        Lit lit chars' =>
            Lit (strCons c lit) chars'

        fmt @ (Num _) =>
            Lit (cast c) fmt

        fmt @ (Str _) =>
            Lit (cast c) fmt

        fmt @ (Chr _) =>
            Lit (cast c) fmt

        fmt @ (Dbl _) =>
            Lit (cast c) fmt

        fmt @ End =>
            Lit (cast c) fmt

TupleVect : (n : Nat) -> (ty : Type) -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1,2,3,4,())

-- Refining the DataStore
infixr 5 .+.

data Schema =
    SString
  | SChar
  | SInt
  | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

-- PARSING: Do notation ftw!
parseSchema : List String -> Maybe Schema
parseSchema [ "String" ] = Just SString
parseSchema [ "Int" ] = Just SInt
parseSchema [ "Char" ] = Just SChar
parseSchema ( "String" :: xs) =  (SString .+.) <$> parseSchema xs 
parseSchema ( "Int" :: xs) = (SInt .+.) <$> parseSchema xs
parseSchema ( "Char" :: xs) = (SChar .+.) <$> parseSchema xs
parseSchema  _ = Nothing

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input =
    case unpack input of 
         Nil => Nothing
         ('"' :: quote) => getQuote quote
         ( _ :: _ ) => Nothing

    where
        getQuote : List Char -> Maybe (String, String)
        getQuote quote =
            case span (/= '"') quote of
                (quoted, '"' :: rest) => Just (pack quoted, pack rest) 
                _                     => Nothing

parsePrefix SInt input =
    case span isDigit input of 
        ("", rest) => Nothing
        (num, rest) => Just (cast num, ltrim rest)

parsePrefix SChar input =
    case unpack input of
         [] => Nothing
         c :: cs => Just (c, ltrim $ pack cs)

parsePrefix (left .+. right) input = do
    (l, input) <- parsePrefix left input
    (r, input) <- parsePrefix right input
    pure ((l,r), input)

parseBySchema : (schema : Schema) -> (rest : String) -> Maybe (SchemaType schema)
parseBySchema schema rest = 
    case parsePrefix schema rest of
        Just (res, "") => Just res
        Just _ => Nothing
        Nothing => Nothing

data Command : Schema -> Type where
    SetSchema : (newschema : Schema) -> Command schema
    Add : SchemaType schema -> Command schema
    Get : Maybe Integer -> Command schema
    Quit : Command schema

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" rest = Add <$> parseBySchema schema rest
parseCommand schema "get" "" = Just (Get Nothing)
parseCommand schema "get" val =
    case all isDigit (unpack val) of
        False => Nothing
        True => Just . Get . Just $ cast val

parseCommand schema "quit" "" = Just Quit
parseCommand schema "schema" rest = SetSchema <$> parseSchema (words rest)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema) 
parse schema input =
    let (cmd, args) = span (/= ' ') input in
    parseCommand schema cmd (ltrim args)

-- STORE
record DataStore where
    constructor MkData
    schema : Schema
    size : Nat
    items : Vect size (SchemaType schema)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema =
    case size store of
        Z => Just (MkData schema _ [])
        S k => Nothing

addToStore : (store : DataStore) ->  SchemaType (schema store) -> DataStore
addToStore (store@(MkData _ _ items')) newitem =
    MkData _ _ (items' ++ [newitem])

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (x .+. y)} (a, b) = display a ++ ", " ++ display b

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
    let store_items = items store in
    case integerToFin pos (size store) of
        Nothing => Just ("Out of range\n", store)
        Just id => Just (display (index id store_items) ++ "\n", store)

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
    case parse (schema store) input of
        Nothing => Just ("Invalid Command\n", store)

        Just (Add item) =>
            Just ("ID " ++ show (size store) ++ "\n", addToStore store item)

        Just (Get (Just pos)) => getEntry pos store

        Just (Get Nothing) =>
            Just (foldl (++) "" $ map ((++ "\n") . display) $ items store, store)
            
        Just Quit => Nothing

        Just (SetSchema schema') =>
            case setSchema store schema' of
                Nothing => Just ("Can't update schema\n", store)
                Just store' => Just ("OK\n", store')

partial main : IO ()
main =
    let default_schema = SString .+. SString .+. SInt in
    replWith (MkData default_schema _ []) "Command: " processInput
