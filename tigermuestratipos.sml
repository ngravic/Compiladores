structure tigermuestratipos:> tigermuestratipos = struct

open tigertips
open tigererrors

fun buscaRecordArray unique lenv =
    let fun aux (_, TArray (_, u)) = u = unique
          | aux (_, TRecord (_, u)) = u = unique
          | aux _ = false
        val (k, _) = getOptn (List.find aux lenv) ErrorInterno "muestratipos10" ~1
    in k end

fun printTipo n t lenv = let
    fun prnt TUnit = "TUnit\n"
      | prnt TNil = "TNil\n"
      | prnt (TInt RO) = "TInt RO\n"
      | prnt (TInt RW) = "TInt RW\n"
      | prnt TString = "TString\n"
      | prnt (TArray (ref t, _)) = "TArray of " ^ prnt t
      | prnt (TTipo s) = "TTipo " ^ s
      | prnt (TRecord (l, u)) =
                let fun aux [] = ""
                      | aux ((_, ref (TTipo tr), ir)::_) = "TRecord (TTipo " ^
                                                           tr ^ " " ^
                                                           Int.toString (ir) ^
                                                           ")\n"
                      | aux ((_, ref (TRecord (_, u)), ir)::t) = (buscaRecordArray u lenv) ^
                                                                 " " ^ Int.toString ir
                                                                 ^ " " ^ aux t
                      | aux ((_, ref (TArray (_, u)), ir)::t) = (buscaRecordArray u lenv) ^
                                                                " " ^ Int.toString ir ^
                                                                " " ^ aux t
                      | aux ((_, ref tr, ir)::t) = prnt tr ^  " " ^
                                                   Int.toString ir ^ " " ^ aux t
                in "TRecord [\n" ^ (aux l) ^ "]\n" end
    in print (n ^ " = " ^ prnt t ^ "\n") end

fun printTTipos tips = List.app (fn (s, t) => printTipo s t tips) tips

end
