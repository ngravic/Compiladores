structure tigerseman :> tigerseman = struct

open tigersres
open tigertrans
open tigertopsort
open tigererrors
open ListPair
open List

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : tenv = tabInserList (tabNueva ())
                                    [("int", TInt RW), ("string", TString)]

val tab_vars : venv = tabInserList (tabNueva ())
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
    ]

fun uncurry f (x, y) = f x y

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = u1 = u2
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = u1 = u2
  | tiposIguales (TInt _) (TInt _) = true
  | tiposIguales a b = a = b

fun trexp venv tenv exp = let

fun getAnot typ tenv default = getOpt ((tabBusca (getOpt (typ, "")) tenv), default)

fun trvar (SimpleVar s) nl =
    (case getOptn (tabBusca s venv) (VNoDeclarada s) "seman53" nl of
        (Var x) => {exp = SCAF, ty = #ty x}
       | _      => error (NoFuncion s) "seman55" nl)
  | trvar (FieldVar (v, s)) nl = (case #ty (trvar v nl) of
        TRecord (tv, _) => let val (_,y,_) = (getOptn (find (fn x => s = #1 x) tv)
                                              CampoInexistente "seman58" nl)
                           in {exp = SCAF, ty = !y} end
       | _              => error (NoRecord "") "seman60" nl)
  | trvar (SubscriptVar (v, e)) nl =
      let val tye = #ty (trexp venv tenv e)
          val tyv = #ty (trvar v nl)
      in assert [tiposIguales tye (TInt RO)] IndiceIncorrecto "seman64" nl;
         case tyv of TArray (t, _) => {exp = SCAF, ty = !t}
                    | _            => error NoArray "seman66" nl
      end

fun trdec venv tenv (VarDec ({name, typ, init, ...}, nl)) =
    let val tyinit = #ty ((trexp venv tenv) init)
        val tytyp = getAnot typ tenv tyinit
    in if isSome typ
       then (assert [tiposIguales tyinit tytyp] InitIncorrecto "seman73" nl;
             ((tabRInserta name (Var {ty = tytyp}) venv), tenv, []))
       else (assert [not (tyinit = TNil)] AsignacionNil "seman75" nl;
             ((tabRInserta name (Var {ty = tyinit}) venv), tenv, []))
    end
  | trdec venv tenv (TypeDec ts) = ((venv, fijaTipos (map #1 ts) tenv, [])
                                    handle Ciclo => error TipoCiclico "seman79" ~1
                                      | noExiste => error CicloInterrumpido "seman80" ~1)
  | trdec venv tenv (FunctionDec fs) =
      let fun namety (NameTy x) = x
              | namety _ = error ErrorInterno "seman81" ~1
          fun addFun ({name, params, result, body}, nl) venv = (* Agrega una funcion al entorno *)
              let val tynames = map (namety o #typ) params
                  val tylist = map ((fn x => getOptn x COMPLETAR "seman86" nl) o
                                    (fn x => tabBusca x tenv)) tynames
                  val tyresult = getAnot result tenv TUnit
                  val func = Func {label = tigertemp.newlabel () ^ name ^ (makestring nl),
                                   formals = tylist, result = tyresult,
                                   level = (), extern = false}
              in tabRInserta name func venv end
          val newvenv = foldr (uncurry addFun) venv fs

          fun makeEnv ({params, ...}, nl) = (* Fabrica el entorno de una funcion *)
              let fun makeEntry {name, typ, ...} = (name, Var {ty = (getOptn (tabBusca (namety typ) tenv)
                                                                     (TipoInexistente (namety typ)) "seman97" nl)})
              in foldl (uncurry (uncurry tabRInserta)) newvenv (map makeEntry params) end
          val bodys = map (#body o #1) fs
          val envs = map makeEnv fs
          val results = map (#result o #1) fs
          val tybodys = mapEq (fn (b, e) => #ty ((trexp e tenv) b)) (bodys, envs)
          val tyresults = map (fn r => getAnot r tenv TUnit) results
      in assert [allEq (uncurry tiposIguales) (tybodys, tyresults)]
                RetornoIncorrecto "seman105" ((#2 o hd) fs);
         (newvenv, tenv, []) end

in case exp of
    (VarExp (v, nl)) => trvar v nl
  | (UnitExp _) => {exp = SCAF, ty = TUnit}
  | (NilExp _) => {exp = SCAF, ty = TNil}
  | (IntExp _) => {exp = SCAF, ty = TInt RW}
  | (StringExp _) => {exp = SCAF, ty = TString}
  | (CallExp ({func, args}, nl)) => (
      case getOptn (tabBusca func venv) (FNoDeclarada func) "seman115" nl of
          Func ({formals, result, ...}) =>
              let val pairs = zipEq (formals, (map (#ty o trexp venv tenv) args))
                              handle UnequalLengths => error CantidadArgumentos "seman118" nl
              in assert [all (uncurry tiposIguales) pairs] (TiposArgumentos func) "seman119" nl;
                        {exp = SCAF, ty = result}
              end
             | _ => error (NoFuncion func) "seman122" nl)
  | (OpExp ({left, oper, right}, nl)) =>
      let val {exp = _, ty = tyl} = trexp venv tenv left
          val {exp = _, ty = tyr} = trexp venv tenv right
      in assert [tiposIguales tyl tyr] OperandosDistintos "seman126" nl;
         if exists (fn x => x = oper) [EqOp, NeqOp]
         then assert [tyl <> TUnit, tyl <> TNil orelse tyr <> TNil]
                     TiposNoComparables "seman129" nl
         else if exists (fn x => x = oper) [PlusOp, MinusOp, TimesOp, DivideOp]
              then assert [tiposIguales tyl (TInt RW)] TiposNoOperables "seman131" nl
              else assert [tyl = TInt RW orelse tyl = TString] TiposNoComparables "seman132" nl;
         {exp = SCAF, ty = TInt RW}
      end
  | (RecordExp ({fields, typ}, nl)) =>
      let (* Traducir cada expresión de fields *)
          val tfields = map (fn (sy, ex) => (sy, trexp venv tenv ex)) fields
          (* Buscar el tipo *)
          val (tyr, cs) = case getOptn (tabBusca typ tenv) (TipoInexistente typ) "seman139" nl of
                          TRecord (cs, u) => (TRecord (cs, u), cs)
                        | _ => error (NoRecord typ) "seman141" nl
          (* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
          fun verificar [] [] = ()
            | verificar ((s, t, _) :: cs) ((sy, {exp, ty}) :: ds) =
                  (assert [s = sy] CamposDistintos "seman145" nl;
                   assert [tiposIguales ty (!t)] (TipoCampo s) "seman146" nl;
                   verificar cs ds)
            | verificar _ _ = error CantidadArgumentos "seman148" nl
      in verificar cs tfields; {exp = SCAF, ty = tyr} end
  | (SeqExp (s, nl)) => {exp = SCAF, ty = #ty (hd (rev (map (trexp venv tenv) s)))}
  | (AssignExp ({var = SimpleVar s, exp}, nl)) =>
      (case getOptn (tabBusca s venv) (VNoDeclarada s) "seman152" nl of
           Func _ => error NoVariable "seman153" nl
         | VIntro => error ErrorInterno "seman154" nl
         | Var {ty = TInt RO} => error SoloLectura "seman155" nl
         | Var {ty = t} => assert [tiposIguales t (#ty (trexp venv tenv exp))]
                                  AsignacionIncorrecta "seman157" nl;
                           {exp = SCAF, ty = TUnit})
  | (AssignExp ({var = (fv as FieldVar (v, s)), exp}, nl)) =>
      let val tyv = #ty (trvar fv nl)
          val tyexp = #ty (trexp venv tenv exp)
      in assert [tiposIguales tyv tyexp] AsignacionIncorrecta "seman162" nl;
         {exp = SCAF, ty = tyv} end
  | (AssignExp ({var = (sv as SubscriptVar (v, idx)), exp}, nl)) =>
      let val tyexp = #ty (trexp venv tenv exp)
          val tyv = #ty (trvar sv nl)
          val tyidx = #ty (trexp venv tenv idx)
      in assert [tiposIguales tyv tyexp] AsignacionIncorrecta "seman168" nl;
         assert [tiposIguales tyidx (TInt RW)] IndiceIncorrecto "seman169" nl;
         {exp = SCAF, ty = tyv} end
  | (IfExp ({test, then', else'}, nl)) =>
      let val {exp = testexp, ty = tytest} = trexp venv tenv test
          val {exp = thenexp, ty = tythen} = trexp venv tenv then'
          val {exp = elseexp, ty = tyelse} = trexp venv tenv (getOpt (else', UnitExp nl))
      in assert [tytest = TInt RW] CondicionIncorrecta "seman175" nl;
         assert [tiposIguales tythen tyelse] IfDiferentes "seman176" nl;
         {exp = SCAF, ty = tyelse} end
  | (WhileExp ({test, body}, nl)) =>
      let val ttest = #ty (trexp venv tenv test)
          val tbody = #ty (trexp venv tenv body)
      in assert [ttest = TInt RW] CondicionIncorrecta "seman181" nl;
         assert [tbody = TUnit] CuerpoIncorrecto "seman182" nl;
         {exp = SCAF, ty = TUnit} end
  | (ForExp ({var, escape, lo, hi, body}, nl)) =>
      let val newvenv = tabRInserta var (Var {ty = TInt RO}) venv
          val {exp = explo, ty = tylo} = trexp venv tenv lo
          val {exp = explhi, ty = tyhi} = trexp venv tenv hi
          val {exp = expbody, ty = tybody} = (trexp newvenv tenv) body
      in assert [tiposIguales tylo (TInt RW), tiposIguales tyhi tylo]
                ExtremosIncorrectos "seman190" nl;
         assert [tiposIguales tybody TUnit] CuerpoIncorrecto "seman191" nl;
         {exp = SCAF, ty = TUnit} end
  | (LetExp ({decs, body}, _)) =>
      let val (venv', tenv', _) = foldl (fn (d, (v, t, _)) => trdec v t d) (venv, tenv, []) decs
          val {exp = expbody, ty = tybody} = (trexp venv' tenv') body
      in {exp = SCAF, ty = tybody} end
  | (BreakExp nl) => {exp = SCAF, ty = TUnit}
  | (ArrayExp ({typ, size, init}, nl)) =>
      let val {exp = sizexp, ty = tysize} = trexp venv tenv size
          val tytyp = getOptn (tabBusca typ tenv) (TNoDeclarado typ) "seman200" nl
          val tyarr = (case tytyp of (TArray (t,_)) => (!t)
                                   | _ => error NoArray "seman202'" nl)
          val {exp = initxp, ty = tyinit} = trexp venv tenv init
      in assert [tiposIguales tysize (TInt RO)] TamanoIncorrecto "seman204" nl;
         assert [tiposIguales tyarr tyinit] InitIncorrecto "seman205" nl;
         {exp = SCAF, ty = tytyp} end
end


fun transProg ex =
    let val main =
                LetExp ({decs = [FunctionDec [({name="_tigermain", params = [],
                                 result = NONE, body = ex}, 0)]],
                         body = UnitExp 0}, 0)
        val _ = (trexp tab_vars tab_tipos) ex (* main *)
    in print "bien!\n" end
end
