;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_list_fun$ 0 )
(declare-sort A_list_nat_fun$ 0 )
(declare-sort A_list_bool_fun$ 0 )
(declare-sort A_list_a_list_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-datatypes ()((A_list$ (nil$ )(cons$ (hd$ A$ )(tl$ A_list$ )))))
(declare-fun u$ ()A_list$ )
(declare-fun bind$ (A_list$ A_a_list_fun$ )A_list$ )
(declare-fun maps$ (A_a_list_fun$ )A_list_a_list_fun$ )
(declare-fun null$ (A_list$ )Bool )
(declare-fun cycle$ (A_list$ )A_stream$ )
(declare-fun shift$ (A_list$ A_stream$ )A_stream$ )
(declare-fun append$ (A_list$ A_list$ )A_list$ )
(declare-fun member$ (A_list$ )A_bool_fun$ )
(declare-fun splice$ (A_list$ )A_list_a_list_fun$ )
(declare-fun fun_app$ (A_list_bool_fun$ A_list$ )Bool )
(declare-fun fun_app$a (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$b (A_list_nat_fun$ A_list$ )Nat$ )
(declare-fun fun_app$c (A_list_a_list_fun$ A_list$ )A_list$ )
(declare-fun list_ex1$ (A_bool_fun$ )A_list_bool_fun$ )
(declare-fun pred_list$ (A_bool_fun$ A_list$ )Bool )
(declare-fun gen_length$ (Nat$ )A_list_nat_fun$ )
(declare-fun stream_all$ (A_bool_fun$ A_stream$ )Bool )
(assert (! (not (= (cycle$ u$ )(shift$ u$ (cycle$ u$ )))):named a0 ))
(assert (! (not (= u$ nil$ )):named a1 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (= (shift$ ?v0 ?v1 )(shift$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a2 ))
(assert (! (forall ((?v0 A_stream$ ))(! (= (shift$ nil$ ?v0 )?v0 ):pattern ((shift$ nil$ ?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_list$ ))(=> (and (=> (= ?v0 nil$ )false )(=> (not (= ?v0 nil$ ))false ))false )):named a4 ))
(assert (! (forall ((?v0 A_a_list_fun$ ))(! (= (bind$ nil$ ?v0 )nil$ ):pattern ((bind$ nil$ ?v0 )))):named a5 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_stream$ ))(= (shift$ (append$ ?v0 ?v1 )?v2 )(shift$ ?v0 (shift$ ?v1 ?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(! (= (fun_app$ (list_ex1$ ?v0 )nil$ )false ):pattern ((list_ex1$ ?v0 )))):named a7 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_stream$ ))(= (shd$ (shift$ ?v0 ?v1 ))(ite (= ?v0 nil$ )(shd$ ?v1 )(hd$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$a (member$ nil$ )?v0 )false ):pattern ((fun_app$a (member$ nil$ )?v0 )))):named a9 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_stream$ ))(= (stl$ (shift$ ?v0 ?v1 ))(ite (= ?v0 nil$ )(stl$ ?v1 )(shift$ (tl$ ?v0 )?v1 )))):named a10 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_list$ )(?v2 A_stream$ ))(= (stream_all$ ?v0 (shift$ ?v1 ?v2 ))(and (pred_list$ ?v0 ?v1 )(stream_all$ ?v0 ?v2 )))):named a11 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$b (gen_length$ ?v0 )nil$ )?v0 ):pattern ((gen_length$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_list$ ))(! (= (fun_app$c (splice$ ?v0 )nil$ )?v0 ):pattern ((splice$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_a_list_fun$ ))(! (= (fun_app$c (maps$ ?v0 )nil$ )nil$ ):pattern ((maps$ ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_list$ ))(= (= ?v0 nil$ )(null$ ?v0 ))):named a15 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (append$ ?v0 ?v1 )(append$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a16 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (append$ ?v0 ?v1 )(append$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a17 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (append$ (append$ ?v0 ?v1 )?v2 )(append$ ?v0 (append$ ?v1 ?v2 )))):named a18 ))
(check-sat )
;(get-unsat-core )
