open List

datatype Error = Escape of string
               | Completar
               | CantidadArgumentos
               | TiposArgumentos of string
               | FNoDeclarada of string
               | NoFuncion of string
               | OperandosDistintos
               | TiposNoComparables
               | TiposNoOperables
               | TipoInexistente of string
               | NoRecord of string
               | CamposDistintos
               | TipoCampo of string
               | VNoDeclarada of string
               | SoloLectura
               | AsignacionIncorrecta
               | IndiceIncorrecto
               | IfDiferentes
               | CondicionIncorrecta
               | CuerpoIncorrecto
               | ExtremosIncorrectos
               | TNoDeclarado of string
               | TamanoIncorrecto
               | InitIncorrecto
               | AsignacionNil
               | ErrorInterno
               | NoExiste of string

fun mensaje c = case c of
                Escape e => "Escape " ^ e ^ " inexistente."
              | Completar => "COMPLETAR."
              | CantidadArgumentos => "No coinciden la cantidad de argumentos."
              | TiposArgumentos f => "No coinciden los tipos de los argumentos de " ^ f ^ "."
              | FNoDeclarada f => "La funcion " ^ f ^ " no fue declarada."
              | NoFuncion f => f ^ " no es una funcion."
              | OperandosDistintos => "Los tipos de los operandos son diferentes."
              | TiposNoComparables => "Los tipos no son comparables."
              | TiposNoOperables => "Los tipos no son operables."
              | TipoInexistente t => "No existe el tipo '" ^ t ^ "'."
              | NoRecord t => "El tipo " ^ t ^ " no es un record."
              | CamposDistintos => "No coinciden los campos."
              | TipoCampo c => "Tipo incorrecto del campo " ^ c ^ "."
              | VNoDeclarada v => "La variable " ^ v ^ " no fue declarada."
              | SoloLectura => "Intento de asignacion a variable de solo lectura."
              | AsignacionIncorrecta => "El tipo de la variable no coincide con el de la expresion."
              | IndiceIncorrecto => "El tipo del indice debe ser int."
              | IfDiferentes => "Las ramas del if tienen diferentes tipos."
              | CondicionIncorrecta => "El tipo de la condicion debe ser int."
              | CuerpoIncorrecto => "El tipo del cuerpo debe ser unit."
              | ExtremosIncorrectos => "Los tipos de los extremos deben ser int."
              | TNoDeclarado t => "El tipo " ^ t ^ " no fue declarado."
              | TamanoIncorrecto => "El tipo del tamaño debe ser int."
              | InitIncorrecto => "No coincide el tipo del valor inicial con el del arreglo."
              | AsignacionNil => "No se puede asignar Nil a una variable sin especificar el tipo."
              | ErrorInterno => "Error interno."
              | NoExiste h => h ^ " **no existe!!!"

fun error e c nl = raise Fail ("\nError en linea " ^ (Int.toString nl) ^
                               ": " ^ (mensaje e) ^ "\nCodigo de error: " ^ c)

fun checkError bs e c nl =
    if foldl (fn (x, y) => x andalso y) true bs then () else error e c nl

fun getOptn opt e c nl = case opt of NONE => error e c nl
                                   | SOME x => x
