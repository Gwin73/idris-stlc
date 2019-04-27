import STLC

namespace Example
    nat : Typ
    nat = Arrow (Arrow Base Base) (Arrow Base Base)

    zero : Term
    zero = Abs "s" (Arrow Base Base) 
            (Abs "z" Base 
                (Var "z"))
                
    suc : Term
    suc = Abs "n" nat
            (Abs "s" (Arrow Base Base) 
                (Abs "z" Base 
                    (App (Var "s") 
                        (App (App (Var "n") 
                                (Var "s")) 
                            (Var "z")))))

    one : Term
    one = App suc zero

    plus : Term
    plus = 
        Abs "m" nat
            (Abs "n" nat
                (Abs "s" (Arrow Base Base) 
                    (Abs "z" Base 
                        (App (App  (Var "m") 
                                (Var "s")) 
                            (App (App (Var "n") 
                                    (Var "s")) 
                                (Var "z"))))))
    example : Term
    example = App (App plus one) one
