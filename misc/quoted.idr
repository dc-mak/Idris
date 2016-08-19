
restQuoted : (input : List Char) -> Maybe (String, String)
restQuoted input with (span (/= '"') input)
    | (quoted, '"'::rest) =
        Just (pack quoted, pack rest)

    | _ =
        Nothing


getQuoted : String -> Maybe (String, String)
getQuoted input with (unpack input)
    | Nil =
        Nothing

    | ('"' :: rest) with (span (/= '"') rest)
        | (quoted, '"'::rest) =
            Just (pack quoted, pack rest)

        | _ =
            Nothing

    | (_ :: _) =
        Nothing
