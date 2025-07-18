;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Nat_nat_fun$ 0 )
(declare-sort Enat_nat_fun$ 0 )
(declare-sort Nat_bool_fun$ 0 )
(declare-sort Nat_enat_fun$ 0 )
(declare-sort Enat_bool_fun$ 0 )
(declare-sort Enat_enat_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort Nat_nat_bool_fun_fun$ 0 )
(declare-sort Enat_enat_bool_fun_fun$ 0 )
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun i$ ()Nat$ )
(declare-fun p$ ()A_stream_bool_fun$ )
(declare-fun enat$ (Nat$ )Enat$ )
(declare-fun omega$ ()A_stream$ )
(declare-fun sdrop$ (Nat$ A_stream$ )A_stream$ )
(declare-fun sfirst$ (A_stream_bool_fun$ A_stream$ )Enat$ )
(declare-fun fun_app$ (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun less_eq$ (Enat$ Enat$ )Bool )
(declare-fun fun_app$a (Enat_bool_fun$ Enat$ )Bool )
(declare-fun fun_app$b (Enat_enat_bool_fun_fun$ Enat$ )Enat_bool_fun$ )
(declare-fun fun_app$c (Nat_bool_fun$ Nat$ )Bool )
(declare-fun fun_app$d (Nat_nat_bool_fun_fun$ Nat$ )Nat_bool_fun$ )
(declare-fun fun_app$e (Enat_enat_fun$ Enat$ )Enat$ )
(declare-fun fun_app$f (Enat_nat_fun$ Enat$ )Nat$ )
(declare-fun fun_app$g (Nat_enat_fun$ Nat$ )Enat$ )
(declare-fun fun_app$h (Nat_nat_fun$ Nat$ )Nat$ )
(declare-fun less_eq$a (Nat$ Nat$ )Bool )
(assert (! (not (less_eq$ (sfirst$ p$ omega$ )(enat$ i$ ))):named a0 ))
(assert (! (fun_app$ p$ (sdrop$ i$ omega$ )):named a1 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= (enat$ ?v0 )(enat$ ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Enat$ ))(less_eq$ ?v0 ?v0 )):named a3 ))
(assert (! (forall ((?v0 Nat$ ))(less_eq$a ?v0 ?v0 )):named a4 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat$ ))(=> (less_eq$ ?v0 (enat$ ?v1 ))(exists ((?v2 Nat$ ))(= ?v0 (enat$ ?v2 ))))):named a5 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 )))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (= ?v0 ?v1 )(and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 )))):named a7 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(=> (and (=> (less_eq$ ?v0 ?v1 )false )(=> (less_eq$ ?v1 ?v0 )false ))false )):named a8 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (and (=> (less_eq$a ?v0 ?v1 )false )(=> (less_eq$a ?v1 ?v0 )false ))false )):named a9 ))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (less_eq$ ?v3 ?v4 )(fun_app$a (fun_app$b ?v0 ?v3 )?v4 )))(=> (fun_app$a (fun_app$b ?v0 ?v1 )?v2 )(fun_app$a (fun_app$b ?v0 ?v2 )?v1 )))(fun_app$a (fun_app$b ?v0 ?v2 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 Nat_nat_bool_fun_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ )(?v4 Nat$ ))(=> (less_eq$a ?v3 ?v4 )(fun_app$c (fun_app$d ?v0 ?v3 )?v4 )))(=> (fun_app$c (fun_app$d ?v0 ?v1 )?v2 )(fun_app$c (fun_app$d ?v0 ?v2 )?v1 )))(fun_app$c (fun_app$d ?v0 ?v2 )?v1 ))):named a11 ))
(assert (! (forall ((?v0 Enat_enat_bool_fun_fun$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (less_eq$ ?v3 ?v4 )(fun_app$a (fun_app$b ?v0 ?v3 )?v4 )))(forall ((?v3 Enat$ )(?v4 Enat$ ))(=> (fun_app$a (fun_app$b ?v0 ?v4 )?v3 )(fun_app$a (fun_app$b ?v0 ?v3 )?v4 ))))(fun_app$a (fun_app$b ?v0 ?v1 )?v2 ))):named a12 ))
(assert (! (forall ((?v0 Nat_nat_bool_fun_fun$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (forall ((?v3 Nat$ )(?v4 Nat$ ))(=> (less_eq$a ?v3 ?v4 )(fun_app$c (fun_app$d ?v0 ?v3 )?v4 )))(forall ((?v3 Nat$ )(?v4 Nat$ ))(=> (fun_app$c (fun_app$d ?v0 ?v4 )?v3 )(fun_app$c (fun_app$d ?v0 ?v3 )?v4 ))))(fun_app$c (fun_app$d ?v0 ?v1 )?v2 ))):named a13 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat_enat_fun$ )(?v2 Enat$ )(?v3 Enat$ ))(=> (and (= ?v0 (fun_app$e ?v1 ?v2 ))(and (less_eq$ ?v2 ?v3 )(forall ((?v4 Enat$ )(?v5 Enat$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$ (fun_app$e ?v1 ?v4 )(fun_app$e ?v1 ?v5 ))))))(less_eq$ ?v0 (fun_app$e ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Enat_nat_fun$ )(?v2 Enat$ )(?v3 Enat$ ))(=> (and (= ?v0 (fun_app$f ?v1 ?v2 ))(and (less_eq$ ?v2 ?v3 )(forall ((?v4 Enat$ )(?v5 Enat$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$a (fun_app$f ?v1 ?v4 )(fun_app$f ?v1 ?v5 ))))))(less_eq$a ?v0 (fun_app$f ?v1 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Nat_enat_fun$ )(?v2 Nat$ )(?v3 Nat$ ))(=> (and (= ?v0 (fun_app$g ?v1 ?v2 ))(and (less_eq$a ?v2 ?v3 )(forall ((?v4 Nat$ )(?v5 Nat$ ))(=> (less_eq$a ?v4 ?v5 )(less_eq$ (fun_app$g ?v1 ?v4 )(fun_app$g ?v1 ?v5 ))))))(less_eq$ ?v0 (fun_app$g ?v1 ?v3 )))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_nat_fun$ )(?v2 Nat$ )(?v3 Nat$ ))(=> (and (= ?v0 (fun_app$h ?v1 ?v2 ))(and (less_eq$a ?v2 ?v3 )(forall ((?v4 Nat$ )(?v5 Nat$ ))(=> (less_eq$a ?v4 ?v5 )(less_eq$a (fun_app$h ?v1 ?v4 )(fun_app$h ?v1 ?v5 ))))))(less_eq$a ?v0 (fun_app$h ?v1 ?v3 )))):named a17 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ )(?v2 Enat$ ))(=> (and (= ?v0 ?v1 )(less_eq$ ?v1 ?v2 ))(less_eq$ ?v0 ?v2 ))):named a18 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (= ?v0 ?v1 )(less_eq$a ?v1 ?v2 ))(less_eq$a ?v0 ?v2 ))):named a19 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(=> (= ?v0 ?v1 )(less_eq$ ?v0 ?v1 ))):named a20 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (= ?v0 ?v1 )(less_eq$a ?v0 ?v1 ))):named a21 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(! (= (less_eq$ (enat$ ?v0 )(enat$ ?v1 ))(less_eq$a ?v0 ?v1 )):pattern ((less_eq$ (enat$ ?v0 )(enat$ ?v1 ))))):named a22 ))
(assert (! (forall ((?v0 Enat$ ))(less_eq$ ?v0 ?v0 )):named a23 ))
(assert (! (forall ((?v0 Nat$ ))(less_eq$a ?v0 ?v0 )):named a24 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(or (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))):named a25 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(or (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))):named a26 ))
(check-sat )
;(get-unsat-core )
