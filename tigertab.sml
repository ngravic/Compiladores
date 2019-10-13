structure tigertab :> tigertab = struct

open Polyhash

type ('a, 'b) Tabla = ('a, 'b) hash_table

exception yaExiste of string
exception noExiste
exception noExisteS of string

fun tabNueva () = mkPolyTable (100, noExiste)

fun fromTab t = let val t' = tabNueva ()
                in apply (fn x => insert t' x) t; t' end

fun name x = x

fun tabEsta (s, t) = isSome (peek t s)

fun tabInserta (s, e, t) = let val t' = copy t in (peekInsert t' (s, e); t') end

fun tabRInserta s e t = let val t' = copy t in (insert t' (s, e); t') end

fun tabBusca s t = peek t s

fun tabSaca (s, t) = valOf (tabBusca s t)

fun tabAplica (f, t) = map (f o #2) t

fun tabAAplica (f, g, t) = let val l' = listItems t
                               val t' = mkPolyTable (100, noExiste)
                           in
                               List.app (insert t')
                               (List.map (fn (k, e) => (f k, g e)) l');
                               t'
                           end

fun tabRAAplica (f, g, t) = let val l' = rev (listItems t)
                                val t' = mkPolyTable (100, noExiste)
                            in
                                List.app (insert t')
                                (List.map (fn (k, e) => (f k, g e)) l');
                                t'
                            end

fun tabInserList (t, l) = let val t' = copy t in (List.app (insert t') l; t') end

fun tabAList t = listItems t

fun tabFiltra (f, t) = let val l = listItems t
                           val t' = mkPolyTable (100, noExiste)
                       in List.app (insert t') (List.filter (f o #2) l); t' end

fun tabPrimer (f, t) = hd (List.filter (f o #2) (listItems t))

fun tabClaves t = List.map #1 (listItems t)

fun tabImprime t = List.app print (List.map #1 (listItems t))

end
