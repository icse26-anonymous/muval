;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Num_num_fun$ 0 )
(declare-datatypes ()((Num$ (one$ )(bit0$ (select$ Num$ ))(bit1$ (selecta$ Num$ )))))
(declare-fun n$ ()Nat$ )
(declare-fun div$ (Nat$ Nat$ )Nat$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun times$ (Nat$ Nat$ )Nat$ )
(declare-fun times$a (Num$ )Num_num_fun$ )
(declare-fun fun_app$ (Num_num_fun$ Num$ )Num$ )
(declare-fun numeral$ (Num$ )Nat$ )
(assert (! (not (= (div$ (suc$ (times$ (numeral$ (bit0$ one$ ))n$ ))(numeral$ (bit0$ one$ )))n$ )):named a0 ))
(assert (! (forall ((?v0 Nat$ ))(= (div$ (suc$ (suc$ ?v0 ))(numeral$ (bit0$ one$ )))(suc$ (div$ ?v0 (numeral$ (bit0$ one$ )))))):named a1 ))
(assert (! (forall ((?v0 Num$ ))(= (= (bit0$ ?v0 )one$ )false )):named a2 ))
(assert (! (forall ((?v0 Num$ ))(= (= one$ (bit0$ ?v0 ))false )):named a3 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ )(?v2 Nat$ ))(= (times$ (numeral$ ?v0 )(times$ (numeral$ ?v1 )?v2 ))(times$ (numeral$ (fun_app$ (times$a ?v0 )?v1 ))?v2 ))):named a4 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (times$ (numeral$ ?v0 )(numeral$ ?v1 ))(numeral$ (fun_app$ (times$a ?v0 )?v1 )))):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ (numeral$ one$ )?v0 )?v0 )):named a6 ))
(assert (! (forall ((?v0 Nat$ ))(= (times$ ?v0 (numeral$ one$ ))?v0 )):named a7 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit0$ ?v0 )(bit0$ ?v1 ))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit0$ ?v0 )(bit0$ ?v1 ))(= ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (suc$ ?v0 )(suc$ ?v1 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (numeral$ ?v0 )(numeral$ ?v1 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(! (= (fun_app$ (times$a (bit0$ ?v0 ))(bit0$ ?v1 ))(bit0$ (bit0$ (fun_app$ (times$a ?v0 )?v1 )))):pattern ((fun_app$ (times$a (bit0$ ?v0 ))(bit0$ ?v1 ))))):named a13 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (times$a one$ )?v0 )?v0 ):pattern ((fun_app$ (times$a one$ )?v0 )))):named a14 ))
(assert (! (forall ((?v0 Num$ ))(! (= (fun_app$ (times$a ?v0 )one$ )?v0 ):pattern ((times$a ?v0 )))):named a15 ))
(check-sat )
;(get-unsat-core )
