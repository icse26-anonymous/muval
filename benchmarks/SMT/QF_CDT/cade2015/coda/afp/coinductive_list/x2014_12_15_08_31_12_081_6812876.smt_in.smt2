;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-sort Nibble$ 0)
(declare-sort Char$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
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
(declare-fun select$ (Char$)Nibble$)
(declare-fun selecta$ (Char$)Nibble$)
(declare-fun char$ (Nibble$ Nibble$ )Char$)
(declare-fun a$ ()A$ )
(declare-fun m$ ()Nat$ )
(declare-fun ma$ ()Nat$ )
(declare-fun mb$ ()Nat$ )
(declare-fun na$ ()Nat$ )
(declare-fun suc$ (Nat$ )Nat$ )
(declare-fun xsa$ ()A_llist$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun less$ (Enat$ Enat$ )Bool )
(declare-fun lnth$ (A_llist$ Nat$ )A$ )
(declare-fun zero$ ()Nat$ )
(declare-fun fun_app$ (Nat_bool_fun$ Nat$ )Bool )
(declare-fun less_eq$ (Nat$ )Nat_bool_fun$ )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun size_bool$ (Bool )Nat$ )
(declare-fun size_char$ (Char$ )Nat$ )
(assert (! (not (= mb$ zero$ )):named a0 ))
(assert (! (= (lnth$ xsa$ zero$ )a$ ):named a1 ))
(assert (! (less$ (enat$ zero$ )(llength$ xsa$ )):named a2 ))
(assert (! (= mb$ (suc$ m$ )):named a3 ))
(assert (! (= (lnth$ xsa$ mb$ )a$ ):named a4 ))
(assert (! (fun_app$ (less_eq$ zero$ )mb$ ):named a5 ))
(assert (! (less$ (enat$ mb$ )(llength$ xsa$ )):named a6 ))
(assert (! (fun_app$ (less_eq$ na$ )ma$ ):named a7 ))
(assert (! (= zero$ zero$ ):named a8 ))
(assert (! (forall ((?v0 Nat$ ))(=> (and (=> (= ?v0 zero$ )false )(=> (not (= ?v0 zero$ ))false ))false )):named a9 ))
(assert (! (forall ((?v0 Nat$ ))(= (= zero$ ?v0 )(= ?v0 zero$ ))):named a10 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (less_eq$ ?v0 )zero$ )(= ?v0 zero$ )):pattern ((less_eq$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 Nat$ ))(fun_app$ (less_eq$ zero$ )?v0 )):named a12 ))
(assert (! (forall ((?v0 Char$ ))(! (= (size_char$ ?v0 )zero$ ):pattern ((size_char$ ?v0 )))):named a13 ))
(assert (! (= (size_bool$ true )zero$ ):named a14 ))
(assert (! (= (size_bool$ false )zero$ ):named a15 ))
(check-sat )
;(get-unsat-core )
