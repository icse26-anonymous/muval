;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort Enat_set$ 0 )
(declare-sort Enat_bool_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort Nat_option$ 0)
(declare-sort Enat$ 0)
(declare-fun none$ ()Nat_option$)
(declare-fun the$ (Nat_option$)Nat$)
(declare-fun some$ (Nat$ )Nat_option$)
(declare-fun rep_enat$ (Enat$)Nat_option$)
(declare-fun abs_enat$ (Nat_option$ )Enat$)
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun p$ ()A_stream_bool_fun$ )
(declare-fun eSuc$ (Enat$ )Enat$ )
(declare-fun zero$ ()Enat$ )
(declare-fun omega$ ()A_stream$ )
(declare-fun member$ (Enat$ Enat_set$ )Bool )
(declare-fun scount$ (A_stream_bool_fun$ A_stream$ )Enat$ )
(declare-fun sfirst$ (A_stream_bool_fun$ A_stream$ )Enat$ )
(declare-fun fun_app$ (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun enat_set$ ()Enat_set$ )
(declare-fun fun_app$a (Enat_bool_fun$ Enat$ )Bool )
(assert (! (not (= (sfirst$ p$ omega$ )(eSuc$ (sfirst$ p$ (stl$ omega$ ))))):named a0 ))
(assert (! (not (fun_app$ p$ omega$ )):named a1 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= (eSuc$ ?v0 )(eSuc$ ?v1 ))(= ?v0 ?v1 ))):named a2 ))
(assert (! (forall ((?v0 Enat$ )(?v1 Enat$ ))(= (= (eSuc$ ?v0 )(eSuc$ ?v1 ))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(= (sfirst$ ?v0 ?v1 )(ite (fun_app$ ?v0 ?v1 )zero$ (eSuc$ (sfirst$ ?v0 (stl$ ?v1 )))))):named a4 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(= (scount$ ?v0 ?v1 )(ite (fun_app$ ?v0 ?v1 )(eSuc$ (scount$ ?v0 (stl$ ?v1 )))(scount$ ?v0 (stl$ ?v1 ))))):named a5 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (fun_app$ ?v0 ?v1 )(= (scount$ ?v0 ?v1 )(eSuc$ (scount$ ?v0 (stl$ ?v1 )))))):named a6 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(! (=> (fun_app$ ?v0 ?v1 )(= (sfirst$ ?v0 ?v1 )zero$ )):pattern ((sfirst$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(= (= (sfirst$ ?v0 ?v1 )zero$ )(fun_app$ ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (not (fun_app$ ?v0 ?v1 ))(= (scount$ ?v0 ?v1 )(scount$ ?v0 (stl$ ?v1 ))))):named a9 ))
(assert (! (forall ((?v0 Enat$ ))(=> (member$ ?v0 enat_set$ )(member$ (eSuc$ ?v0 )enat_set$ ))):named a10 ))
(assert (! (forall ((?v0 Enat$ ))(=> (and (=> (= ?v0 zero$ )false )(=> (not (= ?v0 zero$ ))false ))false )):named a11 ))
(assert (! (member$ zero$ enat_set$ ):named a12 ))
(assert (! (forall ((?v0 Enat_bool_fun$ )(?v1 Enat$ ))(=> (and (fun_app$a ?v0 ?v1 )(forall ((?v2 Enat$ ))(=> (fun_app$a ?v0 ?v2 )(or (= ?v2 zero$ )(exists ((?v3 Enat$ ))(and (= ?v2 (eSuc$ ?v3 ))(or (fun_app$a ?v0 ?v3 )(member$ ?v3 enat_set$ ))))))))(member$ ?v1 enat_set$ ))):named a13 ))
(assert (! (forall ((?v0 Enat$ ))(=> (and (member$ ?v0 enat_set$ )(and (=> (= ?v0 zero$ )false )(forall ((?v1 Enat$ ))(=> (and (= ?v0 (eSuc$ ?v1 ))(member$ ?v1 enat_set$ ))false ))))false )):named a14 ))
(assert (! (forall ((?v0 Enat$ ))(= (member$ ?v0 enat_set$ )(or (= ?v0 zero$ )(exists ((?v1 Enat$ ))(and (= ?v0 (eSuc$ ?v1 ))(member$ ?v1 enat_set$ )))))):named a15 ))
(check-sat )
;(get-unsat-core )
