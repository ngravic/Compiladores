structure tigermuestratipos:> tigermuestratipos = struct

open tigertips

fun buscaRecordArray unique lenv =
    let fun aux (_, TArray (_, u)) = u = unique
          | aux (_, TRecord (_, u)) = u = unique
          | aux _ = false
        val (k, _) = getOpt (List.find aux lenv, raise Fail "error interno76543")
    in k end

fun printTipo n t lenv = let
    fun prnt TUnit = "TUnit\n"
      | prnt TNil = "TNil\n"
      | prnt (TInt _) = "TInt\n"
      | prnt TString = "TString\n"
      | prnt (TArray (ref t, _)) = "TArray of " ^ prnt t
      | prnt (TTipo s) = "TTipo " ^ s
      | prnt (TRecord (l, u)) =
                let fun aux [] = ""
                      | aux ((_, ref (TTipo tr), ir)::_) = "TRecord(TTipo " ^
                                                           tr ^ " " ^
                                                           Int.toString (ir) ^
                                                           ")\n"
                      | aux ((_, ref (TRecord(_, u)), ir)::t) = (buscaRecordArray u lenv) ^
                                                                " " ^ Int.toString ir
                                                                ^ " " ^ aux t
                      | aux ((_, ref (TArray(_, u)), ir)::t) = (buscaRecordArray u lenv) ^
                                                               " " ^ Int.toString ir ^
                                                               " " ^ aux t
                      | aux ((_, ref tr, ir)::t) = prnt tr ^  " " ^
                                                   Int.toString ir ^ " " ^ aux t
                in "TRecord[" ^ (aux l) ^ "]\n" end
    in print (n ^ " = " ^ prnt t) end

fun printTTipos tips = List.app (fn (s, t) => printTipo s t tips) tips

end
