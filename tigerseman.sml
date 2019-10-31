structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans
open tigertopsort
open tigertemp
open tigererrors
open List

type expty = {exp: exp, ty: Tipo}

fun inside x (y::ys) = if x = y then true else inside x ys
  | inside x [] = false

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList (tabNueva (),
                                       [("int", TInt RW), ("string", TString)])

fun rectype (TArray (t, _)) = rectype (!t)
  | rectype t = t

val tab_vars : (string, EnvEntry) Tabla = tabInserList(tabNueva (),
    [("print", Func {level = mainLevel, label = "print",
        formals= [TString], result = TUnit, extern = true}),
    ("flush", Func {level = mainLevel, label = "flush",
        formals = [], result = TUnit, extern = true}),
    ("getchar", Func {level = mainLevel, label = "getstr",
        formals = [], result = TString, extern = true}),
    ("ord", Func {level = mainLevel, label = "ord",
        formals = [TString], result = TInt RW, extern = true}),
    ("chr", Func {level = mainLevel, label = "chr",
        formals = [TInt RW], result = TString, extern = true}),
    ("size", Func {level = mainLevel, label = "size",
        formals = [TString], result = TInt RW, extern = true}),
    ("substring", Func {level = mainLevel, label = "substring",
        formals = [TString, TInt RW, TInt RW], result = TString, extern = true}),
    ("concat", Func {level = mainLevel, label = "concat",
        formals = [TString, TString], result = TString, extern = true}),
    ("not", Func {level = mainLevel, label = "not",
        formals = [TInt RW], result = TInt RW, extern = true}),
    ("exit", Func {level = mainLevel, label = "exit",
        formals = [TInt RW], result = TUnit, extern = true})
    ])

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = u1 = u2
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = u1 = u2
  | tiposIguales (TInt _) (TInt _) = true
  | tiposIguales a b = a = b

fun transExp (venv, tenv) =
    let fun trexp (VarExp v) = trvar v
          | trexp (UnitExp _) = {exp = SCAF, ty = TUnit}
          | trexp (NilExp _) = {exp = SCAF, ty = TNil}
          | trexp (IntExp _) = {exp = SCAF, ty = TInt RW}
          | trexp (StringExp _) = {exp = SCAF, ty = TString}
          | trexp (CallExp ({func, args}, nl)) =
              let fun argsIguales (x::xs) (y::ys) = tiposIguales x y
                                                    andalso argsIguales xs ys
                    | argsIguales [] [] = true
                    | argsIguales _ _ = error CantidadArgumentos "seman66" nl
              in case getOptn (tabBusca func venv) (FNoDeclarada func) "seman66" nl of
                      Func ({formals, result, ...}) =>
                                if argsIguales formals (map (#ty o trexp) args)
                                then {exp = SCAF, ty= result}
                                else error (TiposArgumentos func) "seman71" nl
                    | _ => error (NoFuncion func) "seman72" nl
              end
          | trexp (OpExp ({left, oper, right}, nl)) =
                let val {exp = _, ty = tyl} = trexp left
                    val {exp = _, ty = tyr} = trexp right
                    val _ = (print "TYL: "; printIType tyl; print " TYR: "; printIType tyr)
                in checkError [tiposIguales tyl tyr] OperandosDistintos "seman78'" nl;
                   if inside oper [EqOp, NeqOp]
                   then checkError [tyl <> TUnit, tyl <> TNil orelse tyr <> TNil]
                                   TiposNoComparables "seman81" nl
                   else if inside oper [PlusOp, MinusOp, TimesOp, DivideOp]
                        then checkError [tiposIguales tyl (TInt RW)] TiposNoOperables "seman83" nl
                        else checkError [tyl = TInt RW orelse tyl = TString]
                                        TiposNoComparables "seman85" nl;
                   {exp = SCAF, ty = TInt RW} end
          | trexp (RecordExp ({fields, typ}, nl)) =
              let
                  (* Traducir cada expresión de fields *)
                  val tfields = map (fn (sy, ex) => (sy, trexp ex)) fields
                  (* Buscar el tipo *)
                  val (tyr, cs) = case getOptn (tabBusca typ tenv)
                                               (TipoInexistente typ) "seman93" nl of
                                  TRecord (cs, u) => (TRecord (cs, u), cs)
                                | _ => error (NoRecord typ) "seman95" nl
                  (* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
                  fun verificar [] [] = ()
                    | verificar ((s, t, _)::cs) ((sy, {exp, ty})::ds) =
                          (checkError [s = sy] CamposDistintos "seman99" nl;
                           checkError [tiposIguales ty (!t)] (TipoCampo s) "seman100" nl;
                           verificar cs ds)
                    | verificar _ _ = error CantidadArgumentos "seman102" nl
                  val _ = verificar cs tfields
              in {exp = SCAF, ty = tyr} end
          | trexp (SeqExp (s, nl)) = {exp = SCAF, ty = #ty (hd (rev (map trexp s)))}
          | trexp (AssignExp ({var = SimpleVar s, exp}, nl)) =
                (case getOptn (tabBusca s venv)
                              (VNoDeclarada s) "seman108" nl of
                     Var {ty = TInt RO} => error SoloLectura "seman109" nl
                   | Func _ => error NoVariable "seman110" nl
                   | VIntro => error Completar "seman111" nl
                   | Var {ty = t} => checkError [tiposIguales t (#ty (trexp exp))]
                                           AsignacionIncorrecta "seman113" nl;
                          {exp = SCAF, ty = TUnit})
          | trexp (AssignExp ({var = (fv as FieldVar (v, s)), exp}, nl)) =
                          let val tipov = #ty (trvar (fv, nl))
                              val tipoexp = #ty (trexp exp)
                          in checkError [tiposIguales tipov tipoexp]
                                        AsignacionIncorrecta "seman119" nl;
                             {exp = SCAF, ty = tipov} end
          (* v es el "identificador" del arreglo, e es el indice, exp es la expresion a asignar *)
          | trexp (AssignExp ({var = (sv as SubscriptVar (v, e)), exp}, nl)) =
                          let val tipoexp = #ty (trexp exp)
                              val tipov = #ty (trvar (sv, nl))
                              val tipoe = #ty (trexp e)
                          in checkError [tiposIguales tipov tipoexp] AsignacionIncorrecta "seman126" nl;
                             checkError [tiposIguales tipoe (TInt RW)] IndiceIncorrecto "seman127" nl;
                             {exp = SCAF, ty = tipov} end
          | trexp (IfExp ({test, then', else'}, nl)) =
                let val {exp = testexp, ty = tytest} = trexp test
                    val {exp = thenexp, ty = tythen} = trexp then'
                    val {exp = elseexp, ty = tyelse} = trexp (getOpt (else', UnitExp ~1))
                in checkError [tytest = TInt RW] CondicionIncorrecta "seman133" nl;
                   checkError [tiposIguales tythen tyelse] IfDiferentes "seman134" nl;
                   {exp = SCAF, ty = tyelse} end
          | trexp (WhileExp ({test, body}, nl)) =
              let
                  val ttest = #ty (trexp test)
                  val tbody = #ty (trexp body)
              in checkError [ttest = TInt RW] CondicionIncorrecta "seman140" nl;
                 checkError [tbody = TUnit] CuerpoIncorrecto "seman141" nl;
                 {exp = SCAF, ty = TUnit} end
          | trexp (ForExp ({var, escape, lo, hi, body}, nl)) =
              let val newvenv = tabRInserta var (Var {ty = TInt RO}) venv (*Defino un nuevo entorno de trabajo que incluye el iterador declarado*)
                  val {exp = explo, ty = tylo} = trexp lo
                  val {exp = explhi, ty = tyhi} = trexp hi
                  val {exp = expbody, ty = tybody} = transExp (newvenv, tenv) body (*Tipado del body con el nuevo entorno de varables, incluye iterador*)
              in checkError [tiposIguales tylo (TInt RW), tiposIguales tyhi tylo]
                            ExtremosIncorrectos "seman149" nl;
                 checkError [tiposIguales tybody TUnit] CuerpoIncorrecto "seman150" nl;
                 {exp = SCAF, ty = TUnit} end
          | trexp (LetExp ({decs, body}, _)) =
              let val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec (v, t) d)
                                                     (venv, tenv, []) decs
                  val {exp = expbody, ty = tybody} = transExp (venv', tenv') body
              in {exp = SCAF, ty = tybody} end
          | trexp (BreakExp nl) = {exp = SCAF, ty = TUnit}
          | trexp (ArrayExp ({typ, size, init}, nl)) =
              let val {exp = sizexp, ty = tysize} = trexp size
                  val tytyp = getOptn (tabBusca typ tenv) (TNoDeclarado typ) "seman160" nl
                  val tyarr = (case tytyp of (TArray (t,_)) => (!t)
                                           | _ => error NoArray "seman162'" nl)
                  val {exp = initxp, ty = tyinit} = trexp init
                  val _ = (print "TYARR: "; printIType tyarr; print "\nTYINIT: "; printIType tyinit; print "\n")
              in checkError [tiposIguales tysize (TInt RO)] TamanoIncorrecto "seman165" nl;
                 checkError [tiposIguales tyarr tyinit] InitIncorrecto "seman166" nl;
                 {exp = SCAF, ty = tytyp} end
        and trvar (SimpleVar s, nl) =
                (case getOptn (tabBusca s venv) (VNoDeclarada s) "seman169" nl of
                      (Var x) => {exp = SCAF, ty = #ty x}
                    | _ => error (NoFuncion s) "seman171" nl)
          | trvar (FieldVar (v, s), nl) =
                let fun recBusca s ((x,y,z)::xs) nv = if s = x then {exp=SCAF, ty= !y}
                                                               else recBusca s xs nv
                      | recBusca s [] nv = error CampoInexistente "seman175" nv
                in (case #ty (trvar (v, nl)) of
                    TRecord (tv, _) => recBusca s tv nl
                    | _ => error (NoRecord "") "seman178" nl)
                end
          | trvar (SubscriptVar (v, e), nl) =
              let val tye = #ty (trexp e)
                  val tyv = #ty (trvar (v, nl))
              in checkError [tiposIguales tye (TInt RO)] IndiceIncorrecto "seman183" nl;
                 (case tyv of TArray (t, _) => {exp = SCAF, ty = !t}
                            | _ => error NoArray "seman185" nl) end
      and trdec (venv, tenv) (VarDec ({name, escape, typ, init}, pos)) =
              let val tyinit = #ty (transExp (venv, tenv) init)
                  val tytyp = getOpt ((tabBusca (getOpt (typ, "")) tenv), TUnit) (* VERIFICAR TUNIT *)
              in if isSome typ
                 then (checkError [tiposIguales tyinit tytyp] InitIncorrecto "seman193" pos;
                                  ((tabRInserta name (Var {ty = tytyp}) venv), tenv, []))
                 else (checkError [not (tyinit = TNil)] AsignacionNil "seman195" pos;
                                  ((tabRInserta name (Var {ty = tyinit}) venv), tenv, []))
              end
        | trdec (venv, tenv) (FunctionDec fs) =
            let
                fun aux1 (({name, params : field list, result, body}, pos), venv) = (* NOMBRE DE FUNCION *)
                     let
                         fun tabBuscaF x y = tabBusca y x
                         val typlist = map (fn (NameTy x) => x) (map #typ params) (* WARNING *)
                         val tysearched = map (tabBuscaF tenv) typlist
                         fun getOptnF e c nl opt = getOptn opt e c nl
                         val tyfound = map (getOptnF Completar "seman206" pos) tysearched
                         val tyresult = getOpt (result, "")
                         val damian = getOpt ((tabBusca tyresult tenv), TNil) (* NOMBRE DE VARIABLE *)
                         val tableentry = Func {level = (),
                                                label = tigertemp.newlabel() ^ name ^ (makestring pos),
                                                formals = tyfound,
                                                result = damian,
                                                extern = false}
                         in tabRInserta name tableentry venv end
                (* DADA UNA FUNCION, AGREGA SUS PARAMETROS AL ENTORNO *)
                fun aux2 ({name, params : field list, result, body}, pos) venv =
                     let fun aux3 {name, typ = (NameTy x), escape} = (name, getOptn (tabBusca x tenv) (* WARNING *)
                                                                            Completar "" pos)
                         val paramlist = map aux3 params
                     in foldl (fn ((s, t), y : (string, Tipo) tigertab.Tabla)
                               => tabRInserta s t y) tenv paramlist
                     end
               val venvxfunction = ListPair.zip (fs, (map aux2 fs))
               val _ = map (fn (varenv, func) => transExp (varenv, tenv) func)
            in (foldr aux1 venv fs, tenv, [])
            end (*
                    (*fs tiene la sigueinte estructura:
                    Lista de:
                            Tuplas:
                                    Primer elemento: Record con la declaración de UNA función
                                                                     Los elementos de ese record son:
                                                                            name: symbol 
                                                                            params: field list
                                                                                            -Cada field de la lista de parámetros tiene:
                                                                                                    name: symbol
                                                                                                    escape: bool ref
                                                                                                    typ: ty
                                                                            result: symbol option
                                                                            body: exp
                                    Segundo elmento: Variable de número de línea. -USAR PARA DEBUG DE error(...)
            TO DO:
            +Primer paso: ARMADO DE LAS INTERFACES DE LAS FUNCIONES:
                    -Hacer una función aux. que construya la interfaz de UNA función dada UNA entrada de la lista fs.
                     Para ello:
                    [*] 1)Descartar la segunda componente de la tupla (proyección)
                    [*] 2)Del RECORD con la delcaración de esa función descartar body (aún no nos sirve)
                    [*] 3)Obtener el nombre (obtención de un campo de un record)
                    [*] 4)Buscar los parámetros en el entorno de tipos
                               Para ello:
                                         [*] -De la field (un field es un record) list obtener los campos typ (usar un map)
                                         [*] -De la lista obtenida en el paso anterior, buscar todos los elementos en el
                                              entorno de tipos (usar tabBusca)
                                              Si alguno no se encuentra lanzar una excepción, si no, conservar esta lista (typ list)
                    [*] 5)Obtener el tipo de retorno de la función. (obtención de un campo de un record)
                     Con lo obtenido en (3), (4) y (5) construir una entrada de la tabla de entorno de variables, es decir
                     (string, EnvEntry)
                     Tiene la siguiente forma:
                             Func {level:(), label: tigertemp.label()^name^pos,formals: tl , result: res, extern: false}
                                     donde:
                                             tl se obtiene de (4)
                                             res se obtiene de (5)
                     Agregar esta entrada al entorno (usar tabRinserta).

                    -Usar un fold con la función anterior sobre fs para agregar todas las interfaces del batch al entorno.

            +Segundo paso:TIPADO DE LOS BODY's DE LAS FUNCIONES.
                    -Hacer una función que
*)
         *)
        | trdec (venv, tenv) (TypeDec ts) = (venv, fijaTipos (map #1 ts) tenv, [])
                                            handle Ciclo => error TipoCiclico "seman261" ~1
                                              | noExiste => error CicloInterrumpido "seman262" ~1
    in trexp end

fun transProg ex =
    let val main =
                LetExp ({decs = [FunctionDec [({name="_tigermain", params = [],
                                 result = NONE, body = ex}, 0)]],
                         body = UnitExp 0}, 0)
        (*val _ = transExp (tab_vars, tab_tipos) main*)
        val _ = transExp (tab_vars, tab_tipos) ex
    in print "bien!\n" end
end
