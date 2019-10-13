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

fun inside x (y::ys) = if x = y then true else inside y ys
  | inside x [] = false

fun recBusca s ((x,y,z)::xs) nv = if s = x then {exp=SCAF, ty= !y}
                                  else recBusca s xs nv
  | recBusca s [] nv = error "COMPLETAR" nv

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList (tabNueva (),
                                       [("int", TInt RW), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList( tabNueva(),
    [("print", Func{level=mainLevel, label="print",
        formals=[TString], result=TUnit, extern=true}),
    ("flush", Func{level=mainLevel, label="flush",
        formals=[], result=TUnit, extern=true}),
    ("getchar", Func{level=mainLevel, label="getstr",
        formals=[], result=TString, extern=true}),
    ("ord", Func{level=mainLevel, label="ord",
        formals=[TString], result=TInt RW, extern=true}),
    ("chr", Func{level=mainLevel, label="chr",
        formals=[TInt RW], result=TString, extern=true}),
    ("size", Func{level=mainLevel, label="size",
        formals=[TString], result=TInt RW, extern=true}),
    ("substring", Func{level=mainLevel, label="substring",
        formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
    ("concat", Func{level=mainLevel, label="concat",
        formals=[TString, TString], result=TString, extern=true}),
    ("not", Func{level=mainLevel, label="not",
        formals=[TInt RW], result=TInt RW, extern=true}),
    ("exit", Func{level=mainLevel, label="exit",
        formals=[TInt RW], result=TUnit, extern=true})
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
                    | argsIguales _ _ = error "No coinciden la cantidad de argumentos" nl
              in case getOptn (tabBusca func venv) (func ^ " no fue declarada") nl of
                      Func ({formals, result, ...}) =>
                                if argsIguales formals (map (#ty o trexp) args)
                                then {exp = SCAF, ty= result}
                                else error ("No coinciden los tipos de los argumentos de " ^ func) nl
                    | _ => error (func ^  " no es una funcion") nl
              end
          | trexp (OpExp ({left, oper, right}, nl)) =
                let val {exp = _, ty = tyl} = trexp left
                    val {exp = _, ty = tyr} = trexp right
                in checkError [tiposIguales tyl tyr] "Error de tipos" nl;
                   checkError [tyl = TUnit orelse (tyl = TNil andalso tyr = TNil),
                               inside oper [EqOp, NeqOp]] "Error de tipos" nl;
                   checkError [inside oper [PlusOp, MinusOp, TimesOp, DivideOp],
                               tyl <> TInt RW] "Error de tipos" nl;
                   checkError [inside oper [LtOp, LeOp, GtOp, GeOp],
                               tyl <> TInt RW andalso tyl <> TString] "Error de tipos" nl;
                   {exp = SCAF, ty = TInt RW} end
          | trexp (RecordExp ({fields, typ}, nl)) =
              let
                  (* Traducir cada expresión de fields *)
                  val tfields = map (fn (sy, ex) => (sy, trexp ex)) fields
                  (* Buscar el tipo *)
                  val (tyr, cs) = case getOptn (tabBusca typ tenv)
                                               ("Tipo inexistente (" ^ typ ^ ")") nl of
                                  TRecord (cs, u) => (TRecord (cs, u), cs)
                                | _ => error (typ ^ " no es de tipo record") nl
                  (* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
                  fun verificar [] [] = ()
                    | verificar (c::cs) [] = error "Faltan campos" nl
                    | verificar [] (c::cs) = error "Sobran campos" nl
                    | verificar ((s, t, _)::cs) ((sy, {exp, ty})::ds) =
                          (checkError [s = sy] "Error de campo" nl;
                           checkError [tiposIguales ty (!t)] ("Error de tipo del campo " ^ s) nl;
                           verificar cs ds)
                  val _ = verificar cs tfields
              in {exp = SCAF, ty = tyr} end
          | trexp (SeqExp (s, nl)) = {exp = SCAF, ty = #ty (hd (rev (map trexp s)))}
          | trexp (AssignExp ({var = SimpleVar s, exp}, nl)) =
                (case getOptn (tabBusca s tenv)
                              ("La variable" ^ s ^ " no fue declarada") nl of
                     TInt RO => error "Intento de asignacion a variable RO" nl
                   | t => checkError [tiposIguales t (#ty (trexp exp))]
                                     "Error de tipado en asignacion de variable" nl;
                          {exp = SCAF, ty = TUnit})
          | trexp (AssignExp ({var = (fv as FieldVar (v, s)), exp}, nl)) =
                          let val tipov = #ty (trvar (fv, nl))
                              val tipoexp = #ty (trexp exp)
                          in checkError [tiposIguales tipov tipoexp]
                                        "Error de tipado de variable" nl;
                             {exp = SCAF, ty = tipov} end
          (* v es el "identificador" del arreglo, e es el indice, exp es la expresion a asignar *)
          | trexp (AssignExp ({var = (sv as SubscriptVar (v, e)), exp}, nl)) =
                          let val tipoexp = #ty (trexp exp)
                              val tipov = #ty (trvar (sv, nl))
                              val tipoe = #ty (trexp e)
                          in checkError [tiposIguales tipov tipoexp, tiposIguales tipoe (TInt RW)]
                                        "Error de asignación de tipo al elemento del arreglo" nl;
                             {exp = SCAF, ty = tipov} end
          | trexp (IfExp ({test, then', else'}, nl)) =
                let val {exp = testexp, ty = tytest} = trexp test
                    val {exp = thenexp, ty = tythen} = trexp then'
                    val {exp = elseexp, ty = tyelse} = trexp (getOpt (else', UnitExp ~1))
                in checkError [tytest = TInt RW, tiposIguales tythen tyelse] "Error de tipos en if" nl;
                   {exp = SCAF, ty = tyelse} end
          | trexp (WhileExp ({test, body}, nl)) =
              let
                  val ttest = #ty (trexp test)
                  val tbody = #ty (trexp body)
              in checkError [ttest = TInt RW] "Error de tipo en la condicion" nl;
                 checkError [tbody = TUnit] "El cuerpo de un while no puede devolver un valor" nl;
                 {exp = SCAF, ty = TUnit} end
          | trexp (ForExp ({var, escape, lo, hi, body}, nl)) =
              let val newvenv = tabRInserta var (Var {ty = TInt RO}) venv (*Defino un nuevo entorno de trabajo que incluye el iterador declarado*)
                  val {exp = explo,ty = tylo} = trexp lo
                  val {exp = explhi, ty = tyhi} = trexp hi
                  val {exp = expbody, ty = tybody} = transExp (newvenv, tenv) body (*Tipado del body con el nuevo entorno de varables, incluye iterador*)
              in checkError [tiposIguales tylo (TInt RW),
                             tiposIguales tyhi tylo] "Tipos de extremos del for no enteros" nl;
                 checkError [tiposIguales tybody TUnit] "Error de tipado en cuerpo del for" nl;
                 {exp = SCAF, ty = TUnit} end
          | trexp (LetExp ({decs, body}, _)) =
              let val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec (v, t) d)
                                                     (venv, tenv, []) decs
                  val {exp = expbody, ty = tybody} = transExp (venv', tenv') body
              in {exp = SCAF, ty = tybody} end
          | trexp (BreakExp nl) = {exp = SCAF, ty = TUnit}
          | trexp (ArrayExp ({typ, size, init}, nl)) =
              let val {exp = sizexp, ty = tysize} = trexp size
                  val tytyp = getOptn (tabBusca typ tenv)
                                      "El tipo que define el arreglo no fue declarado" nl
                  val {exp = initxp, ty = tyinit} = trexp init
              in checkError [tiposIguales tysize (TInt RO)] "El declarador de tamaño de arreglo no es Entero" nl;
                 checkError [tiposIguales tytyp tyinit] "El tipo del valor inicial no coincide con el del arreglo" nl;
                 {exp = SCAF, ty = TUnit} end
        and trvar (SimpleVar s, nl) =
                (case getOptn (tabBusca s venv) "Variable Simple no declarada" nl of
                      (Var x) => {exp = SCAF, ty = #ty x}
                    | _ => error "No se trata de una variable sino de una función" nl)
          | trvar (FieldVar(v, s), nl) =
              (case #ty (trvar (v, nl)) of
                    TRecord (tv, _) => recBusca s tv nl
                    | _ => error "Intentando acceder a un registro de algo que no es record" nl)
        | trvar (SubscriptVar (v, e), nl) =
            let val tye = #ty (trexp e)
                val tyv = #ty (trvar (v, nl))
            in checkError [tiposIguales tye (TInt RO)] "El indice del arreglo no evalúa a un entero" nl;
               (case tyv of TArray (t, _) => {exp = SCAF, ty = !t}
                          | _ => error "Intento de acceso a algo que no es un array" nl) end
      and trdec (venv, tenv) (VarDec ({name, escape, typ, init}, pos)) =
              let val tyinit = #ty (trexp init)
                  val tytyp = tabBusca (getOpt (typ, "")) tenv
                  val _= if isSome typ
                         then checkError [tiposIguales tyinit (getOptn tytyp "No existe el tipo que se intenta declarar" pos)]
                                         "El valor que quiere asignar no coincide con el tipo de la variable" pos
                         else checkError [tiposIguales tyinit TNil]
                                         "No se puede asignar Nil a una variable sin especificar su tipo" pos
              in (tabRInserta name (Var {ty = tyinit}) venv, tenv, []) end
        | trdec (venv, tenv) (FunctionDec fs) = (venv, tenv, []) (* COMPLETAR *)
        | trdec (venv, tenv) (TypeDec ts) = (venv, tenv, []) (* COMPLETAR *)
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
