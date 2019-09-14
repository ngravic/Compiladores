structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans
open ListPair
open List

type expty = {exp: exp, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt RW), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
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
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TInt _) (TInt _)= true
  | tiposIguales a b = (a=b)

fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")

fun igualesArgs(formals, args, nl) = 
  (filter (fn (x, y) => (not (tiposIguales x y))) (zipEq (formals,args))) = []
  handle UnequalLengths => error("No coinciden la cantidad de argumentos",nl)

fun transExp(venv, tenv) =
		let fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=SCAF, ty=TUnit}
		| trexp(NilExp _)= {exp=SCAF, ty=TNil}
		| trexp(IntExp(i, _)) = {exp=SCAF, ty=TInt RW}
		| trexp(StringExp(s, _)) = {exp=SCAF, ty=TString}
		| trexp(CallExp({func, args}, nl)) =
      (case tabBusca(func, venv) of
          NONE    => error(func^" no fue declarada ",nl)
        | SOME (Func({formals, result,...})) => 
          if not (igualesArgs(formals, (map (fn x=> #ty x) (map trexp args)), nl)) then 
            error("No coinciden los tipos de los argumentos de " ^ func, nl)
          else {exp=SCAF, ty=result}
        | SOME _ => error(func ^ " no es una funcion", nl))
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) = 
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| MinusOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| TimesOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| DivideOp => if tyl=TInt RW then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| LtOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| LeOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| GtOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| GeOp => if tyl=TInt RW orelse tyl=TString then {exp=SCAF,ty=TInt RW} else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case t of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)
				
				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar [] [] = ()
				  | verificar (c::cs) [] = error("Faltan campos", nl)
				  | verificar [] (c::cs) = error("Sobran campos", nl)
				  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty (!t) then verificar cs ds
							 else error("Error de tipo del campo "^s, nl)
				val _ = verificar cs tfields
			in
				{exp=SCAF, ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=SCAF, ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
      (case tabBusca(s, tenv) of
        SOME (TInt RO) => error("Error de intento de asignacion de valor a variable RO",nl)
        |SOME x         => if not (tiposIguales x (#ty (trexp exp)) )
                          then error("Error de tipado asignación de variable",nl)
                          else {exp=SCAF, ty=TUnit}
        |_              => error("La variable" ^ s ^ "no fue declarada", nl)
      ) 

		| trexp(AssignExp({var= (fv as FieldVar (v,s)), exp}, nl)) =
				let val tipov = (#ty (trvar (fv,nl)))
					val tipoexp = (#ty (trexp exp))
				in
					if tiposIguales (tipov)(tipoexp)
					then {exp = SCAF, ty = tipov}
					else error("Error de tipado de variable",nl)
				end
		| trexp(AssignExp({var=(sv as SubscriptVar (v,e)),exp},nl)) =  (*v es el "identificador" del arreglo, e es el indice, exp es la expresion a asignar*)
				let val tipoexp = (#ty (trexp exp))
					val tipov = (#ty (trvar (sv,nl)))
					val tipoe = (#ty (trexp e))
				in
					if tiposIguales (tipov)(tipoexp) andalso tiposIguales (tipoe) (TInt RW)
					then {exp = SCAF, ty = tipov }
					else error("Error de asignación de tipo al elemento del arreglo",nl)
				end			
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if tytest=TInt RW andalso tiposIguales tythen tyelse then {exp=SCAF, ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if tytest=TInt RW andalso tythen=TUnit then {exp=SCAF, ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val tbody = trexp body
			in
				if (#ty ttest) = TInt RW andalso #ty tbody = TUnit then {exp=SCAF, ty=TUnit}
				else if (#ty ttest) <> TInt RW then error("Error de tipo en la condición", nl)
				else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
			let val newvenv = tabRInserta(var,Var{ty = TInt RO},venv)		(*Defino un nuevo entorno de trabajo que incluye el iterador declarado*)
		    	val {exp = explo,ty = tylo } = trexp lo
				val {exp = explhi,ty = tyhi} = trexp hi
				val {exp = expbody,ty = tybody} = transExp(newvenv,tenv) (body) (*Tipado del body con el nuevo entorno de varables, incluye iterador*)
				
			in
				if tiposIguales (tylo)(TInt RW) andalso tiposIguales (tyhi)(TInt RW)
				then (if tiposIguales (tybody) (TUnit) 
					then {exp = SCAF, ty = TUnit}
					else error("Error de tipado en cuerpo del for",nl))
				else error("Tipo de extremos del for no Enteros",nl)
			end
		| trexp(LetExp({decs, body}, _)) =
			let
				val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in 
				{exp=SCAF, ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=SCAF, ty=TUnit}
		| trexp(ArrayExp({typ, size, init}, nl)) =
			let val {exp = sizexp, ty = tysize} = trexp(size)
                val tytyp = tabBusca(typ,tenv)
                val {exp =initxp, ty = tyinit } = trexp(init)
            in if tiposIguales(tysize)(TInt RO)
               then (
                    case tytyp of 
                    NONE => error("El tipo que define el arreglo no fue declarado",nl)
                    | SOME x => if tiposIguales(x)(tyinit)
                              then {exp=SCAF , ty= TUnit}
                              else error("El tipo del valor inicial no coincide con el del arreglo",nl)
               )
               else error("El declarador de tamaño de arreglo no es Entero",nl)

            end
		and trvar(SimpleVar s, nl) =
			{exp=SCAF, ty=TUnit} (*COMPLETAR*)
		| trvar(FieldVar(v, s), nl) =
			{exp=SCAF, ty=TUnit} (*COMPLETAR*)
		| trvar(SubscriptVar(v, e), nl) =
			{exp=SCAF, ty=TUnit} (*COMPLETAR*)
		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
			(venv, tenv, []) (*COMPLETAR*)
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
			(venv, tenv, []) (*COMPLETAR*)
		| trdec (venv,tenv) (FunctionDec fs) =
			(venv, tenv, []) (*COMPLETAR*)
		| trdec (venv,tenv) (TypeDec ts) =
			(venv, tenv, []) (*COMPLETAR*)
	in trexp end
fun transProg ex =
	let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=NONE, body=ex}, 0)]],
						body=UnitExp 0}, 0)
		(*val _ = transExp(tab_vars, tab_tipos) main*)
    val _ = transExp(tab_vars, tab_tipos) ex

	in	print "bien!\n" end
end
