open Il;;

val tp0trans : Lfpl.tp0 -> tp
val tp1trans : Lfpl.tp1 -> tp

val translate0 : Lfpl.exp -> Lfpl.tp0 -> exp Tclfpl.tcM 
val translate1 : Lfpl.prog -> exp
    
