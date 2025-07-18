;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_stream_a_stream_fun$ 0 )
(declare-sort A_stream_bool_fun_a_stream_bool_fun_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-fun p$ ()A_stream_bool_fun$ )
(declare-fun uu$ ()A_stream_bool_fun$ )
(declare-fun alw$ (A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun uua$ (A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun uub$ (A_stream_a_stream_fun$ )A_stream_bool_fun_a_stream_bool_fun_fun$ )
(declare-fun uuc$ (A_stream_bool_fun$ )A_stream_bool_fun_a_stream_bool_fun_fun$ )
(declare-fun uud$ ()A_stream_bool_fun$ )
(declare-fun eSuc$ (Enat$ )Enat$ )
(declare-fun zero$ ()Enat$ )
(declare-fun omega$ ()A_stream$ )
(declare-fun scount$ (A_stream_bool_fun$ A_stream$ )Enat$ )
(declare-fun fun_app$ (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$a (A_stream_bool_fun_a_stream_bool_fun_fun$ A_stream_bool_fun$ )A_stream_bool_fun$ )
(declare-fun fun_app$b (A_stream_a_stream_fun$ A_stream$ )A_stream$ )
(assert (! (forall ((?v0 A_stream$ ))(! (= (fun_app$ uu$ ?v0 )(not (fun_app$ p$ ?v0 ))):pattern ((fun_app$ uu$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(! (= (fun_app$ (uua$ ?v0 )?v1 )(not (fun_app$ ?v0 ?v1 ))):pattern ((fun_app$ (uua$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream_bool_fun$ )(?v2 A_stream$ ))(! (= (fun_app$ (fun_app$a (uuc$ ?v0 )?v1 )?v2 )(and (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$a (uuc$ ?v0 )?v1 )?v2 )))):named a2 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream_bool_fun$ )(?v2 A_stream$ ))(! (= (fun_app$ (fun_app$a (uub$ ?v0 )?v1 )?v2 )(fun_app$ ?v1 (fun_app$b ?v0 ?v2 ))):pattern ((fun_app$ (fun_app$a (uub$ ?v0 )?v1 )?v2 )))):named a3 ))
(assert (! (forall ((?v0 A_stream$ ))(! (= (fun_app$ uud$ ?v0 )false ):pattern ((fun_app$ uud$ ?v0 )))):named a4 ))
(assert (! (not (exists ((?v0 A_stream$ ))(and (= omega$ ?v0 )(and (not (fun_app$ p$ ?v0 ))(or (= (scount$ p$ (stl$ ?v0 ))zero$ )(fun_app$ (alw$ uu$ )(stl$ ?v0 ))))))):named a5 ))
(assert (! (= (scount$ p$ omega$ )zero$ ):named a6 ))
(assert (! (= (scount$ p$ omega$ )(ite (fun_app$ p$ omega$ )(eSuc$ (scount$ p$ (stl$ omega$ )))(scount$ p$ (stl$ omega$ )))):named a7 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(! (=> (fun_app$ (alw$ (uua$ ?v0 ))?v1 )(= (scount$ ?v0 ?v1 )zero$ )):pattern ((scount$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (not (fun_app$ ?v0 ?v1 ))(= (scount$ ?v0 ?v1 )(scount$ ?v0 (stl$ ?v1 ))))):named a9 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(= (scount$ ?v0 ?v1 )(ite (fun_app$ ?v0 ?v1 )(eSuc$ (scount$ ?v0 (stl$ ?v1 )))(scount$ ?v0 (stl$ ?v1 ))))):named a10 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (fun_app$ ?v0 ?v1 )(= (scount$ ?v0 ?v1 )(eSuc$ (scount$ ?v0 (stl$ ?v1 )))))):named a11 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ ))(= (alw$ (alw$ ?v0 ))(alw$ ?v0 ))):named a12 ))
(assert (! (forall ((?v0 A_stream_a_stream_fun$ )(?v1 A_stream_bool_fun$ )(?v2 A_stream$ ))(=> (forall ((?v3 A_stream$ ))(= (fun_app$b ?v0 (stl$ ?v3 ))(stl$ (fun_app$b ?v0 ?v3 ))))(= (fun_app$ (alw$ ?v1 )(fun_app$b ?v0 ?v2 ))(fun_app$ (alw$ (fun_app$a (uub$ ?v0 )?v1 ))?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(= (fun_app$ (alw$ ?v0 )?v1 )(exists ((?v2 A_stream$ ))(and (= ?v1 ?v2 )(and (fun_app$ ?v0 ?v2 )(fun_app$ (alw$ ?v0 )(stl$ ?v2 ))))))):named a14 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (and (fun_app$ (alw$ ?v0 )?v1 )(forall ((?v2 A_stream$ ))(=> (and (= ?v1 ?v2 )(and (fun_app$ ?v0 ?v2 )(fun_app$ (alw$ ?v0 )(stl$ ?v2 ))))false )))false )):named a15 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ )(?v2 A_stream_bool_fun$ ))(=> (and (fun_app$ ?v0 ?v1 )(and (forall ((?v3 A_stream$ ))(=> (fun_app$ ?v0 ?v3 )(fun_app$ ?v2 ?v3 )))(forall ((?v3 A_stream$ ))(=> (and (fun_app$ ?v0 ?v3 )(not (fun_app$ (alw$ ?v2 )(stl$ ?v3 ))))(fun_app$ ?v0 (stl$ ?v3 ))))))(fun_app$ (alw$ ?v2 )?v1 ))):named a16 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ )(?v2 A_stream_bool_fun$ ))(=> (and (fun_app$ ?v0 ?v1 )(forall ((?v3 A_stream$ ))(=> (fun_app$ ?v0 ?v3 )(exists ((?v4 A_stream$ ))(and (= ?v3 ?v4 )(and (fun_app$ ?v2 ?v4 )(or (fun_app$ ?v0 (stl$ ?v4 ))(fun_app$ (alw$ ?v2 )(stl$ ?v4 )))))))))(fun_app$ (alw$ ?v2 )?v1 ))):named a17 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream$ ))(=> (and (fun_app$ ?v0 ?v1 )(fun_app$ (alw$ ?v0 )(stl$ ?v1 )))(fun_app$ (alw$ ?v0 )?v1 ))):named a18 ))
(assert (! (forall ((?v0 A_stream_bool_fun$ )(?v1 A_stream_bool_fun$ )(?v2 A_stream$ ))(= (fun_app$ (alw$ (fun_app$a (uuc$ ?v0 )?v1 ))?v2 )(and (fun_app$ (alw$ ?v0 )?v2 )(fun_app$ (alw$ ?v1 )?v2 )))):named a19 ))
(assert (! (forall ((?v0 A_stream$ ))(= (fun_app$ (alw$ uud$ )?v0 )false )):named a20 ))
(assert (! (forall ((?v0 Enat$ ))(= (= zero$ ?v0 )(= ?v0 zero$ ))):named a21 ))
(check-sat )
;(get-unsat-core )
