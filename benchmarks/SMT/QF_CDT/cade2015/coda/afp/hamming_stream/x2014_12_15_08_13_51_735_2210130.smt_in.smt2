;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Nat_set$ 0 )
(declare-codatatypes ()((Nat_llist$ (lNil$ )(lCons$ (lhd$ Nat$ )(ltl$ Nat_llist$ )))))
(declare-sort Num$ 0)
(declare-fun one$ ()Num$)
(declare-fun select$ (Num$)Num$)
(declare-fun bit0$ (Num$ )Num$)
(declare-fun selecta$ (Num$)Num$)
(declare-fun bit1$ (Num$ )Num$)
(declare-fun n$ ()Nat$ )
(declare-fun p$ ()Nat$ )
(declare-fun n$a ()Nat$ )
(declare-fun na$ ()Nat$ )
(declare-fun dvd$ (Nat$ Nat$ )Bool )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun less$ (Nat$ Nat$ )Bool )
(declare-fun lset$ (Nat_llist$ )Nat_set$ )
(declare-fun one$a ()Nat$ )
(declare-fun zero$ ()Nat$ )
(declare-fun prime$ (Nat$ )Bool )
(declare-fun times$ (Nat$ Nat$ )Nat$ )
(declare-fun member$ (Nat$ Nat_set$ )Bool )
(declare-fun smooth$ (Nat$ )Bool )
(declare-fun hamming$ ()Nat_llist$ )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(declare-fun numeral$ (Num$ )Nat$ )
(assert (! (not (smooth$ n$ )):named a0 ))
(assert (! (smooth$ na$ ):named a1 ))
(assert (! (smooth$ n$a ):named a2 ))
(assert (! (= na$ (times$ p$ n$ )):named a3 ))
(assert (! (=> (forall ((?v0 Nat$ ))(=> (= na$ (times$ p$ ?v0 ))false ))false ):named a4 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (smooth$ (times$ ?v0 ?v1 ))(and (smooth$ ?v0 )(smooth$ ?v1 )))):named a5 ))
(assert (! (dvd$ p$ na$ ):named a6 ))
(assert (! (not (smooth$ zero$ )):named a7 ))
(assert (! (forall ((?v0 Nat$ ))(=> (smooth$ ?v0 )(less$ zero$ ?v0 ))):named a8 ))
(assert (! (smooth$ (suc$ zero$ )):named a9 ))
(assert (! (forall ((?v0 Nat$ ))(=> (and (less$ ?v0 na$ )(smooth$ ?v0 ))(member$ ?v0 (lset$ hamming$ )))):named a10 ))
(assert (! (forall ((?v0 Nat$ ))(=> (smooth$ ?v0 )(less_eq$ (suc$ zero$ )?v0 ))):named a11 ))
(assert (! (smooth$ (numeral$ (bit0$ one$ ))):named a12 ))
(assert (! (prime$ p$ ):named a13 ))
(assert (! (exists ((?v0 Nat$ ))(and (prime$ ?v0 )(dvd$ ?v0 na$ ))):named a14 ))
(assert (! (less$ one$a na$ ):named a15 ))
(assert (! (less_eq$ p$ (numeral$ (bit1$ (bit0$ one$ )))):named a16 ))
(assert (! (forall ((?v0 Nat$ ))(= (dvd$ (numeral$ (bit0$ one$ ))(suc$ (suc$ ?v0 )))(dvd$ (numeral$ (bit0$ one$ ))?v0 ))):named a17 ))
(check-sat )
;(get-unsat-core )
