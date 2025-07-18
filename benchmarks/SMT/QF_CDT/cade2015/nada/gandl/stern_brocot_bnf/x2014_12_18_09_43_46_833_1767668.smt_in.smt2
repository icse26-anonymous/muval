;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_tree_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_tree_a_tree_bool_fun_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-fun root$ (A_tree$)A$)
(declare-fun left$ (A_tree$)A_tree$)
(declare-fun right$ (A_tree$)A_tree$)
(declare-fun node$ (A$ A_tree$ A_tree$ )A_tree$)
(declare-fun p$ (A$ A_tree$ )Bool )
(declare-fun t$ ()A_tree$ )
(declare-fun x$ ()A$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_tree_bool_fun$ A_tree$ )Bool )
(declare-fun fun_app$a (A_tree_a_tree_bool_fun_fun$ A_tree$ )A_tree_bool_fun$ )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$c (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun rel_tree$ (A_a_bool_fun_fun$ A_tree$ )A_tree_bool_fun$ )
(declare-fun set_tree$ (A_tree$ )A_set$ )
(assert (! (not (p$ x$ t$ )):named a0 ))
(assert (! (member$ x$ (set_tree$ t$ )):named a1 ))
(assert (! (forall ((?v0 A_tree$ ))(p$ (root$ ?v0 )?v0 )):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(=> (and (member$ ?v0 (set_tree$ (left$ ?v1 )))(p$ ?v0 (left$ ?v1 )))(p$ ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(=> (and (member$ ?v0 (set_tree$ (right$ ?v1 )))(p$ ?v0 (right$ ?v1 )))(p$ ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ ))(=> (and (= (root$ ?v0 )(root$ ?v1 ))(and (= (left$ ?v0 )(left$ ?v1 ))(= (right$ ?v0 )(right$ ?v1 ))))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(=> (member$ ?v0 (set_tree$ (left$ ?v1 )))(member$ ?v0 (set_tree$ ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(=> (member$ ?v0 (set_tree$ (right$ ?v1 )))(member$ ?v0 (set_tree$ ?v1 )))):named a7 ))
(assert (! (forall ((?v0 A_tree_a_tree_bool_fun_fun$ )(?v1 A_tree$ )(?v2 A_tree$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(forall ((?v3 A_tree$ )(?v4 A_tree$ ))(=> (fun_app$ (fun_app$a ?v0 ?v3 )?v4 )(and (= (root$ ?v3 )(root$ ?v4 ))(and (or (fun_app$ (fun_app$a ?v0 (left$ ?v3 ))(left$ ?v4 ))(= (left$ ?v3 )(left$ ?v4 )))(or (fun_app$ (fun_app$a ?v0 (right$ ?v3 ))(right$ ?v4 ))(= (right$ ?v3 )(right$ ?v4 ))))))))(= ?v1 ?v2 ))):named a8 ))
(assert (! (forall ((?v0 A_tree_a_tree_bool_fun_fun$ )(?v1 A_tree$ )(?v2 A_tree$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(forall ((?v3 A_tree$ )(?v4 A_tree$ ))(=> (fun_app$ (fun_app$a ?v0 ?v3 )?v4 )(and (= (root$ ?v3 )(root$ ?v4 ))(and (fun_app$ (fun_app$a ?v0 (left$ ?v3 ))(left$ ?v4 ))(fun_app$ (fun_app$a ?v0 (right$ ?v3 ))(right$ ?v4 )))))))(= ?v1 ?v2 ))):named a9 ))
(assert (! (forall ((?v0 A_tree$ ))(member$ (root$ ?v0 )(set_tree$ ?v0 ))):named a10 ))
(assert (! (forall ((?v0 A_tree$ ))(= (node$ (root$ ?v0 )(left$ ?v0 )(right$ ?v0 ))?v0 )):named a11 ))
(assert (! (forall ((?v0 A_tree$ ))(=> (=> (= ?v0 (node$ (root$ ?v0 )(left$ ?v0 )(right$ ?v0 )))false )false )):named a12 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A_tree$ )(?v2 A_tree$ ))(= (fun_app$ (rel_tree$ ?v0 ?v1 )?v2 )(and (fun_app$b (fun_app$c ?v0 (root$ ?v1 ))(root$ ?v2 ))(and (fun_app$ (rel_tree$ ?v0 (left$ ?v1 ))(left$ ?v2 ))(fun_app$ (rel_tree$ ?v0 (right$ ?v1 ))(right$ ?v2 )))))):named a13 ))
(assert (! (forall ((?v0 A_tree_a_tree_bool_fun_fun$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A_a_bool_fun_fun$ ))(=> (and (fun_app$ (fun_app$a ?v0 ?v1 )?v2 )(forall ((?v4 A_tree$ )(?v5 A_tree$ ))(=> (fun_app$ (fun_app$a ?v0 ?v4 )?v5 )(and (fun_app$b (fun_app$c ?v3 (root$ ?v4 ))(root$ ?v5 ))(and (fun_app$ (fun_app$a ?v0 (left$ ?v4 ))(left$ ?v5 ))(fun_app$ (fun_app$a ?v0 (right$ ?v4 ))(right$ ?v5 )))))))(fun_app$ (rel_tree$ ?v3 ?v1 )?v2 ))):named a14 ))
(check-sat )
;(get-unsat-core )
