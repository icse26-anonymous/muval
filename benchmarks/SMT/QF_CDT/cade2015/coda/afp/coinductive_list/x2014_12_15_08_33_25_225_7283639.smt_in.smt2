;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort Nat_nat_bool_fun_fun$ 0 )
(declare-sort Nibble$ 0)
(declare-sort Char$ 0)
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
(declare-fun m$ ()Nat$ )
(declare-fun less$ (Nat$ )Nat_bool_fun$ )
(declare-fun zero$ ()Nat$ )
(declare-fun fun_app$ (Nat_bool_fun$ Nat$ )Bool )
(declare-fun fun_app$a (Nat_nat_bool_fun_fun$ Nat$ )Nat_bool_fun$ )
(declare-fun size_bool$ (Bool )Nat$ )
(declare-fun size_char$ (Char$ )Nat$ )
(assert (! (not (= m$ zero$ )):named a0 ))
(assert (! (not (fun_app$ (less$ zero$ )m$ )):named a1 ))
(assert (! (= zero$ zero$ ):named a2 ))
(assert (! (forall ((?v0 Nat$ ))(=> (and (=> (= ?v0 zero$ )false )(=> (not (= ?v0 zero$ ))false ))false )):named a3 ))
(assert (! (forall ((?v0 Nat$ ))(= (= zero$ ?v0 )(= ?v0 zero$ ))):named a4 ))
(assert (! (forall ((?v0 Nat$ ))(= (not (= ?v0 zero$ ))(fun_app$ (less$ zero$ )?v0 ))):named a5 ))
(assert (! (forall ((?v0 Nat$ ))(= (not (fun_app$ (less$ zero$ )?v0 ))(= ?v0 zero$ ))):named a6 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (less$ ?v0 )zero$ )false ):pattern ((less$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 Char$ ))(! (= (size_char$ ?v0 )zero$ ):pattern ((size_char$ ?v0 )))):named a8 ))
(assert (! (= (size_bool$ true )zero$ ):named a9 ))
(assert (! (= (size_bool$ false )zero$ ):named a10 ))
(assert (! (forall ((?v0 Nat$ ))(=> (=> (= ?v0 zero$ )false )(fun_app$ (less$ zero$ )?v0 ))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (not (= ?v0 ?v1 ))(or (fun_app$ (less$ ?v0 )?v1 )(fun_app$ (less$ ?v1 )?v0 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat_nat_bool_fun_fun$ ))(=> (and (=> (fun_app$ (less$ ?v0 )?v1 )(fun_app$ (fun_app$a ?v2 ?v1 )?v0 ))(and (=> (= ?v0 ?v1 )(fun_app$ (fun_app$a ?v2 ?v1 )?v0 ))(=> (fun_app$ (less$ ?v1 )?v0 )(fun_app$ (fun_app$a ?v2 ?v1 )?v0 ))))(fun_app$ (fun_app$a ?v2 ?v1 )?v0 ))):named a13 ))
(check-sat )
;(get-unsat-core )
