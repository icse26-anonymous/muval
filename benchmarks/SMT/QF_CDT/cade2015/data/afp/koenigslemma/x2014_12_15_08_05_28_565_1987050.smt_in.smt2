;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-datatypes ()((A_list$ (nil$ )(cons$ (hd$ A$ )(tl$ A_list$ )))))
(declare-fun n$ ()A$ )
(declare-fun x$ ()A$ )
(declare-fun xs$ ()A_list$ )
(declare-fun set$ (A_list$ )A_set$ )
(declare-fun append$ (A_list$ A_list$ )A_list$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun thesis$ ()Bool )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(assert (! (not thesis$ ):named a0 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (and (= xs$ (append$ ?v0 (cons$ n$ ?v1 )))(not (member$ n$ (set$ ?v1 ))))thesis$ )):named a1 ))
(assert (! (not (= n$ x$ )):named a2 ))
(assert (! (exists ((?v0 A_list$ )(?v1 A_list$ ))(and (= xs$ (append$ ?v0 (cons$ n$ ?v1 )))(not (member$ n$ (set$ ?v1 ))))):named a3 ))
(assert (! (member$ n$ (set$ xs$ )):named a4 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(= (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(exists ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(and (fun_app$ ?v1 ?v3 )(forall ((?v5 A$ ))(=> (member$ ?v5 (set$ ?v2 ))(not (fun_app$ ?v1 ?v5 ))))))))):named a5 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(= (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(exists ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(and (fun_app$ ?v1 ?v3 )(forall ((?v5 A$ ))(=> (member$ ?v5 (set$ ?v4 ))(not (fun_app$ ?v1 ?v5 ))))))))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ ))(= (member$ ?v0 (set$ ?v1 ))(exists ((?v2 A_list$ )(?v3 A_list$ ))(and (= ?v1 (append$ ?v2 (cons$ ?v0 ?v3 )))(not (member$ ?v0 (set$ ?v2 ))))))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ ))(= (member$ ?v0 (set$ ?v1 ))(exists ((?v2 A_list$ )(?v3 A_list$ ))(and (= ?v1 (append$ ?v2 (cons$ ?v0 ?v3 )))(not (member$ ?v0 (set$ ?v3 ))))))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ ))(= (member$ ?v0 (set$ ?v1 ))(exists ((?v2 A_list$ )(?v3 A_list$ ))(= ?v1 (append$ ?v2 (cons$ ?v0 ?v3 )))))):named a9 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(=> (and (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(forall ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(=> (and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(and (fun_app$ ?v1 ?v3 )(forall ((?v5 A$ ))(=> (member$ ?v5 (set$ ?v2 ))(not (fun_app$ ?v1 ?v5 ))))))false )))false )):named a10 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(=> (and (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(forall ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(=> (and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(and (fun_app$ ?v1 ?v3 )(forall ((?v5 A$ ))(=> (member$ ?v5 (set$ ?v4 ))(not (fun_app$ ?v1 ?v5 ))))))false )))false )):named a11 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(=> (and (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(forall ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(=> (and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(fun_app$ ?v1 ?v3 ))false )))false )):named a12 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(=> (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(exists ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(and (fun_app$ ?v1 ?v3 )(forall ((?v5 A$ ))(=> (member$ ?v5 (set$ ?v2 ))(not (fun_app$ ?v1 ?v5 ))))))))):named a13 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(=> (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(exists ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(and (fun_app$ ?v1 ?v3 )(forall ((?v5 A$ ))(=> (member$ ?v5 (set$ ?v4 ))(not (fun_app$ ?v1 ?v5 ))))))))):named a14 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(=> (exists ((?v2 A$ ))(and (member$ ?v2 (set$ ?v0 ))(fun_app$ ?v1 ?v2 )))(exists ((?v2 A_list$ )(?v3 A$ )(?v4 A_list$ ))(and (= ?v0 (append$ ?v2 (cons$ ?v3 ?v4 )))(fun_app$ ?v1 ?v3 ))))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ ))(=> (member$ ?v0 (set$ ?v1 ))(exists ((?v2 A_list$ )(?v3 A_list$ ))(and (= ?v1 (append$ ?v2 (cons$ ?v0 ?v3 )))(not (member$ ?v0 (set$ ?v2 ))))))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_list$ )(?v2 A$ )(?v3 A_list$ ))(= (= (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a17 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (append$ (append$ ?v0 ?v1 )?v2 )(append$ ?v0 (append$ ?v1 ?v2 )))):named a18 ))
(check-sat )
;(get-unsat-core )
