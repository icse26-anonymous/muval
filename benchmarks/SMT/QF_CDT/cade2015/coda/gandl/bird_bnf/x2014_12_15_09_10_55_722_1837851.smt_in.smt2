;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_tree_a_tree_fun$ 0 )
(declare-codatatypes ()((A_tree$ (node$ (root$ A$ )(left$ A_tree$ )(right$ A_tree$ )))))
(declare-fun t$ ()A_tree$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun mirror$ (A_tree$ )A_tree$ )
(declare-fun fun_app$ (A_tree_a_tree_fun$ A_tree$ )A_tree$ )
(declare-fun fun_app$a (A_a_fun$ A$ )A$ )
(declare-fun map_tree$ (A_a_fun$ A_tree$ )A_tree$ )
(declare-fun set_tree$ (A_tree$ )A_set$ )
(declare-fun tree_pure$ (A$ )A_tree$ )
(declare-fun even_mirror$ ()A_tree_a_tree_fun$ )
(declare-fun tree_iterate$ (A_a_fun$ A_a_fun$ A$ )A_tree$ )
(declare-fun even_odd_mirror$ (Bool )A_tree_a_tree_fun$ )
(assert (! (not (= (root$ (fun_app$ even_mirror$ t$ ))(root$ t$ ))):named a0 ))
(assert (! (= even_mirror$ (even_odd_mirror$ true )):named a1 ))
(assert (! (forall ((?v0 Bool )(?v1 A_tree$ ))(= (root$ (fun_app$ (even_odd_mirror$ ?v0 )?v1 ))(root$ ?v1 ))):named a2 ))
(assert (! (forall ((?v0 A_tree$ ))(= (root$ (mirror$ ?v0 ))(root$ ?v0 ))):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun$ )(?v2 A$ ))(= (root$ (tree_iterate$ ?v0 ?v1 ?v2 ))?v2 )):named a4 ))
(assert (! (forall ((?v0 A$ ))(= (root$ (tree_pure$ ?v0 ))?v0 )):named a5 ))
(assert (! (forall ((?v0 A_tree$ ))(member$ (root$ ?v0 )(set_tree$ ?v0 ))):named a6 ))
(assert (! (forall ((?v0 A_tree$ ))(member$ (root$ ?v0 )(set_tree$ ?v0 ))):named a7 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$a ?v0 (root$ ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_tree$ ))(= (root$ (map_tree$ ?v0 ?v1 ))(fun_app$a ?v0 (root$ ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (root$ (node$ ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a11 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (map_tree$ ?v0 (tree_pure$ ?v1 ))(tree_pure$ (fun_app$a ?v0 ?v1 )))):named a12 ))
(check-sat )
;(get-unsat-core )
