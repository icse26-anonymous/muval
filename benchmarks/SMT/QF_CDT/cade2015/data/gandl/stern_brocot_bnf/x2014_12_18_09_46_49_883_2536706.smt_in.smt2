;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Dir_list_bool_fun$ 0 )
(declare-sort Dir_list_dir_list_fun$ 0 )
(declare-datatypes ()((Dir$ (l$ )(r$ ))(Dir_list$ (nil$ )(cons$ (hd$ Dir$ )(tl$ Dir_list$ )))))
(declare-fun path$ ()Dir_list$ )
(declare-fun path$a ()Dir_list$ )
(declare-fun append$ (Dir_list$ )Dir_list_dir_list_fun$ )
(declare-fun prefix$ (Dir_list$ )Dir_list_bool_fun$ )
(declare-fun thesis$ ()Bool )
(declare-fun fun_app$ (Dir_list_dir_list_fun$ Dir_list$ )Dir_list$ )
(declare-fun fun_app$a (Dir_list_bool_fun$ Dir_list$ )Bool )
(assert (! (not thesis$ ):named a0 ))
(assert (! (forall ((?v0 Dir$ )(?v1 Dir_list$ ))(=> (= path$ (fun_app$ (append$ path$a )(fun_app$ (append$ (cons$ ?v0 nil$ ))?v1 )))thesis$ )):named a1 ))
(assert (! (fun_app$a (prefix$ path$a )path$ ):named a2 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir$ )(?v2 Dir_list$ )(?v3 Dir$ ))(= (= (fun_app$ (append$ ?v0 )(cons$ ?v1 nil$ ))(fun_app$ (append$ ?v2 )(cons$ ?v3 nil$ )))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a3 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )?v1 )(= ?v0 nil$ ))):named a4 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )?v0 )(= ?v1 nil$ ))):named a5 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ ))(= (= ?v0 (fun_app$ (append$ ?v1 )?v0 ))(= ?v1 nil$ ))):named a6 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ ))(= (= ?v0 (fun_app$ (append$ ?v0 )?v1 ))(= ?v1 nil$ ))):named a7 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ ))(= (= nil$ (fun_app$ (append$ ?v0 )?v1 ))(and (= ?v0 nil$ )(= ?v1 nil$ )))):named a8 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )nil$ )(and (= ?v0 nil$ )(= ?v1 nil$ )))):named a9 ))
(assert (! (forall ((?v0 Dir_list$ ))(! (= (fun_app$ (append$ ?v0 )nil$ )?v0 ):pattern ((append$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ )(?v2 Dir$ )(?v3 Dir_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(cons$ ?v2 ?v3 ))(or (and (= ?v0 nil$ )(= ?v1 (cons$ ?v2 ?v3 )))(exists ((?v4 Dir_list$ ))(and (= ?v0 (cons$ ?v2 ?v4 ))(= (fun_app$ (append$ ?v4 )?v1 )?v3 )))))):named a11 ))
(assert (! (forall ((?v0 Dir$ )(?v1 Dir_list$ )(?v2 Dir_list$ )(?v3 Dir_list$ ))(= (= (cons$ ?v0 ?v1 )(fun_app$ (append$ ?v2 )?v3 ))(or (and (= ?v2 nil$ )(= (cons$ ?v0 ?v1 )?v3 ))(exists ((?v4 Dir_list$ ))(and (= (cons$ ?v0 ?v4 )?v2 )(= ?v1 (fun_app$ (append$ ?v4 )?v3 ))))))):named a12 ))
(assert (! (forall ((?v0 Dir_list$ ))(=> (and (=> (= ?v0 nil$ )false )(forall ((?v1 Dir_list$ )(?v2 Dir$ ))(=> (= ?v0 (fun_app$ (append$ ?v1 )(cons$ ?v2 nil$ )))false )))false )):named a13 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list_bool_fun$ ))(=> (and (not (= ?v0 nil$ ))(and (forall ((?v2 Dir$ ))(fun_app$a ?v1 (cons$ ?v2 nil$ )))(forall ((?v2 Dir$ )(?v3 Dir_list$ ))(=> (and (not (= ?v3 nil$ ))(fun_app$a ?v1 ?v3 ))(fun_app$a ?v1 (fun_app$ (append$ ?v3 )(cons$ ?v2 nil$ )))))))(fun_app$a ?v1 ?v0 ))):named a14 ))
(assert (! (forall ((?v0 Dir$ )(?v1 Dir_list$ )(?v2 Dir$ )(?v3 Dir_list$ ))(= (= (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ )(?v2 Dir_list$ ))(= (fun_app$ (append$ (fun_app$ (append$ ?v0 )?v1 ))?v2 )(fun_app$ (append$ ?v0 )(fun_app$ (append$ ?v1 )?v2 )))):named a16 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ )(?v2 Dir_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(fun_app$ (append$ ?v2 )?v1 ))(= ?v0 ?v2 ))):named a17 ))
(assert (! (forall ((?v0 Dir_list$ )(?v1 Dir_list$ )(?v2 Dir_list$ ))(= (= (fun_app$ (append$ ?v0 )?v1 )(fun_app$ (append$ ?v0 )?v2 ))(= ?v1 ?v2 ))):named a18 ))
(check-sat )
;(get-unsat-core )
