structure tigertips = struct
    datatype TIntRW = RO | RW

    type unique = unit ref

    datatype Tipo = TUnit
                  | TNil
                  | TInt of TIntRW 
                  | TString
                  | TArray of Tipo ref  * unique
                  | TRecord of (string * Tipo ref * int) list * unique
                  | TTipo of string
end
