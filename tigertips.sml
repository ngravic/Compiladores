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

    fun toString TUnit              = "Unit"
      | toString TNil               = "Nil"
      | toString (TInt _)           = "Int"
      | toString (TString)          = "String"
      | toString (TArray (t, _))    = "Array of " ^ (toString (!t))
      | toString (TRecord (lst, _)) = "Record of " ^  concat (map (fn (_,t,_) => toString (!t)) lst)
      | toString (TTipo t)          = t

    fun printIType TUnit              = print "TUnit"
      | printIType TNil               = print "TNil"
      | printIType (TInt _)           = print "TInt"
      | printIType TString            = print "TString"
      | printIType (TArray (t, _))    = (print "TArray "; printIType (!t))
      | printIType (TRecord (lst, _)) = (print "TRecord"; map (fn (_, t, _) => printIType (!t)) lst; ())
      | printIType (TTipo t)          = print t
end
