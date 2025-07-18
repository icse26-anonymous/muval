;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Num$ 0)
(declare-sort Nibble$ 0)
(declare-fun one$ ()Num$)
(declare-fun select$ (Num$)Num$)
(declare-fun bit0$ (Num$ )Num$)
(declare-fun selecta$ (Num$)Num$)
(declare-fun bit1$ (Num$ )Num$)
(declare-fun nibble0$ ()Nibble$)
(declare-fun nibble1$ ()Nibble$)
(declare-fun nibble2$ ()Nibble$)
(declare-fun nibble3$ ()Nibble$)
(declare-fun nibble4$ ()Nibble$)
(declare-fun nibble5$ ()Nibble$)
(declare-fun nibble6$ ()Nibble$)
(declare-fun nibble7$ ()Nibble$)
(declare-fun nibble8$ ()Nibble$)
(declare-fun nibble9$ ()Nibble$)
(declare-fun nibbleA$ ()Nibble$)
(declare-fun nibbleB$ ()Nibble$)
(declare-fun nibbleC$ ()Nibble$)
(declare-fun nibbleD$ ()Nibble$)
(declare-fun nibbleE$ ()Nibble$)
(declare-fun nibbleF$ ()Nibble$)
(declare-fun times$ (Nat$ Nat$ )Nat$ )
(declare-fun smooth$ (Nat$ )Bool )
(declare-fun times$a (Num$ Num$ )Num$ )
(declare-fun numeral$ (Num$ )Nat$ )
(declare-fun nibble_of_nat$ (Nat$ )Nibble$ )
(assert (! (not (smooth$ (numeral$ (bit1$ one$ )))):named a0 ))
(assert (! (forall ((?v0 Num$ ))(= (= (bit1$ ?v0 )one$ )false )):named a1 ))
(assert (! (forall ((?v0 Num$ ))(= (= one$ (bit1$ ?v0 ))false )):named a2 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit1$ ?v0 )(bit1$ ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit1$ ?v0 )(bit1$ ?v1 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (numeral$ ?v0 )(numeral$ ?v1 ))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 Num$ ))(not (= one$ (bit1$ ?v0 )))):named a6 ))
(assert (! (smooth$ (numeral$ (bit0$ one$ ))):named a7 ))
(assert (! (= (= one$ one$ )true ):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (smooth$ (times$ ?v0 ?v1 ))(and (smooth$ ?v0 )(smooth$ ?v1 )))):named a9 ))
(assert (! (= (nibble_of_nat$ (numeral$ (bit1$ (bit1$ (bit1$ one$ )))))nibbleF$ ):named a10 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit0$ ?v0 )(bit0$ ?v1 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (= (bit0$ ?v0 )(bit0$ ?v1 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ )(?v2 Nat$ ))(= (times$ (numeral$ ?v0 )(times$ (numeral$ ?v1 )?v2 ))(times$ (numeral$ (times$a ?v0 ?v1 ))?v2 ))):named a13 ))
(assert (! (forall ((?v0 Num$ )(?v1 Num$ ))(= (times$ (numeral$ ?v0 )(numeral$ ?v1 ))(numeral$ (times$a ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 Num$ ))(= (= one$ (bit0$ ?v0 ))false )):named a15 ))
(check-sat )
;(get-unsat-core )
