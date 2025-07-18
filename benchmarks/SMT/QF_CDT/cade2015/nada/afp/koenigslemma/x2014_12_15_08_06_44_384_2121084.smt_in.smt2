;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Node$ 0 )
(declare-sort Node_set$ 0 )
(declare-sort Node_bool_fun$ 0 )
(declare-sort Node_node_bool_fun_fun$ 0 )
(declare-sort Node_set_node_bool_fun_fun$ 0 )
(declare-sort Node_bool_fun_node_bool_fun_fun$ 0 )
(declare-sort Node_node_set_node_bool_fun_fun_fun$ 0 )
(declare-sort Node_node_set_prod_node_bool_fun_fun$ 0 )
(declare-sort Node_node_set_prod$ 0)
(declare-fun fst$ (Node_node_set_prod$)Node$)
(declare-fun snd$ (Node_node_set_prod$)Node_set$)
(declare-fun pair$ (Node$ Node_set$ )Node_node_set_prod$)
(declare-fun x$ ()Node$ )
(declare-fun na$ ()Node$ )
(declare-fun nb$ ()Node$ )
(declare-fun ns$ ()Node_set$ )
(declare-fun uu$ ()Node_node_set_node_bool_fun_fun_fun$ )
(declare-fun x$a ()Node$ )
(declare-fun bot$ ()Node_set$ )
(declare-fun nsa$ ()Node_set$ )
(declare-fun nsb$ ()Node_set$ )
(declare-fun top$ ()Node_set$ )
(declare-fun uua$ (Node_bool_fun$ )Node_bool_fun_node_bool_fun_fun$ )
(declare-fun uub$ (Node_bool_fun$ )Node_bool_fun_node_bool_fun_fun$ )
(declare-fun graph$ ()Node_node_bool_fun_fun$ )
(declare-fun finite$ (Node_set$ )Bool )
(declare-fun insert$ (Node$ Node_set$ )Node_set$ )
(declare-fun member$ (Node$ Node_set$ )Bool )
(declare-fun uminus$ (Node_set$ )Node_set$ )
(declare-fun collect$ (Node_bool_fun$ )Node_set$ )
(declare-fun fun_app$ (Node_bool_fun$ Node$ )Bool )
(declare-fun fun_app$a (Node_set_node_bool_fun_fun$ Node_set$ )Node_bool_fun$ )
(declare-fun fun_app$b (Node_node_set_node_bool_fun_fun_fun$ Node$ )Node_set_node_bool_fun_fun$ )
(declare-fun fun_app$c (Node_node_bool_fun_fun$ Node$ )Node_bool_fun$ )
(declare-fun fun_app$d (Node_bool_fun_node_bool_fun_fun$ Node_bool_fun$ )Node_bool_fun$ )
(declare-fun fun_app$e (Node_node_set_prod_node_bool_fun_fun$ Node_node_set_prod$ )Node_bool_fun$ )
(declare-fun case_prod$ (Node_node_set_node_bool_fun_fun_fun$ )Node_node_set_prod_node_bool_fun_fun$ )
(declare-fun connected$ (Node_node_bool_fun_fun$ )Bool )
(declare-fun reachable_via$ (Node_node_bool_fun_fun$ Node_set$ Node$ )Node_set$ )
(assert (! (forall ((?v0 Node$ )(?v1 Node_set$ )(?v2 Node$ ))(! (= (fun_app$ (fun_app$a (fun_app$b uu$ ?v0 )?v1 )?v2 )(and (fun_app$ (fun_app$c graph$ ?v0 )?v2 )(and (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 (insert$ ?v2 ?v1 )))?v2 )))(not (member$ ?v2 (insert$ ?v0 ?v1 )))))):pattern ((fun_app$ (fun_app$a (fun_app$b uu$ ?v0 )?v1 )?v2 )))):named a0 ))
(assert (! (forall ((?v0 Node_bool_fun$ )(?v1 Node_bool_fun$ )(?v2 Node$ ))(! (= (fun_app$ (fun_app$d (uua$ ?v0 )?v1 )?v2 )(or (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$d (uua$ ?v0 )?v1 )?v2 )))):named a1 ))
(assert (! (forall ((?v0 Node_bool_fun$ )(?v1 Node_bool_fun$ )(?v2 Node$ ))(! (= (fun_app$ (fun_app$d (uub$ ?v0 )?v1 )?v2 )(and (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 ))):pattern ((fun_app$ (fun_app$d (uub$ ?v0 )?v1 )?v2 )))):named a2 ))
(assert (! (not (exists ((?v0 Node$ ))(fun_app$ (fun_app$e (case_prod$ uu$ )(pair$ nb$ nsb$ ))?v0 ))):named a3 ))
(assert (! (finite$ nsa$ ):named a4 ))
(assert (! (connected$ graph$ ):named a5 ))
(assert (! (finite$ nsb$ ):named a6 ))
(assert (! (not (member$ nb$ nsb$ )):named a7 ))
(assert (! (not (= x$ x$a )):named a8 ))
(assert (! (not (member$ na$ nsa$ )):named a9 ))
(assert (! (forall ((?v0 Node$ ))(finite$ (collect$ (fun_app$c graph$ ?v0 )))):named a10 ))
(assert (! (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ nb$ nsb$ ))nb$ ))):named a11 ))
(assert (! (not (finite$ top$ )):named a12 ))
(assert (! (forall ((?v0 Node$ )(?v1 Node_set$ ))(=> (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ ?v0 ?v1 ))?v0 )))(exists ((?v2 Node$ ))(fun_app$ (fun_app$e (case_prod$ uu$ )(pair$ ?v0 ?v1 ))?v2 )))):named a13 ))
(assert (! (not (finite$ (reachable_via$ graph$ (uminus$ (insert$ na$ nsa$ ))na$ ))):named a14 ))
(assert (! (forall ((?v0 Node_node_set_prod$ )(?v1 Node_node_set_node_bool_fun_fun_fun$ )(?v2 Node$ ))(=> (forall ((?v3 Node$ )(?v4 Node_set$ ))(=> (= (pair$ ?v3 ?v4 )?v0 )(fun_app$ (fun_app$a (fun_app$b ?v1 ?v3 )?v4 )?v2 )))(fun_app$ (fun_app$e (case_prod$ ?v1 )?v0 )?v2 ))):named a15 ))
(assert (! (forall ((?v0 Node$ )(?v1 Node_set$ ))(= (finite$ (insert$ ?v0 ?v1 ))(finite$ ?v1 ))):named a16 ))
(assert (! (= ns$ bot$ ):named a17 ))
(assert (! (forall ((?v0 Node_bool_fun$ )(?v1 Node_bool_fun$ ))(= (finite$ (collect$ (fun_app$d (uua$ ?v0 )?v1 )))(and (finite$ (collect$ ?v0 ))(finite$ (collect$ ?v1 ))))):named a18 ))
(assert (! (forall ((?v0 Node_bool_fun$ )(?v1 Node_bool_fun$ ))(=> (or (finite$ (collect$ ?v0 ))(finite$ (collect$ ?v1 )))(finite$ (collect$ (fun_app$d (uub$ ?v0 )?v1 ))))):named a19 ))
(assert (! (forall ((?v0 Node_set$ )(?v1 Node_set$ ))(= (= (uminus$ ?v0 )(uminus$ ?v1 ))(= ?v0 ?v1 ))):named a20 ))
(check-sat )
;(get-unsat-core )
