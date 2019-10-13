structure tigertemp :> tigertemp = struct
    type label = string
    type temp = string

    fun makeString s = s

    local
        val i = ref 0
        val j = ref 0
    in
        fun newtemp () = (i := !i + 1;
                          "T" ^ Int.toString (!i))
        fun newlabel () = (j := !j + 1;
                           "L" ^ Int.toString (!j))
    end
end
