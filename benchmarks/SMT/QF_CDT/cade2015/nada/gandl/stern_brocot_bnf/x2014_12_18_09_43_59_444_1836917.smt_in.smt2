;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort B_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_b_fun$ 0 )
(declare-sort B_a_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort A_a_fun_set$ 0 )
(declare-sort A_b_fun_set$ 0 )
(declare-sort B_a_fun_set$ 0 )
(declare-sort A_a_a_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun$ 0 )
(declare-sort B_a_a_fun_fun$ 0 )
(declare-sort B_a_fun_a_fun$ 0 )
(declare-sort B_a_fun_b_fun$ 0 )
(declare-sort B_b_a_fun_fun$ 0 )
(declare-sort A_tree_bool_fun$ 0 )
(declare-sort B_tree_bool_fun$ 0 )
(declare-sort A_a_fun_bool_fun$ 0 )
(declare-sort A_b_fun_bool_fun$ 0 )
(declare-sort B_a_fun_bool_fun$ 0 )
(declare-sort A_b_a_fun_fun_set$ 0 )
(declare-sort B_a_fun_b_a_fun_fun$ 0 )
(declare-sort A_a_fun_tree_bool_fun$ 0 )
(declare-sort A_a_tree_bool_fun_fun$ 0 )
(declare-sort A_b_fun_tree_bool_fun$ 0 )
(declare-sort B_a_fun_tree_bool_fun$ 0 )
(declare-sort B_b_tree_bool_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun_bool_fun$ 0 )
(declare-sort A_b_a_fun_fun_tree_bool_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_tree_bool_fun_fun$ 0 )
(declare-sort A_b_fun_a_b_fun_tree_bool_fun_fun$ 0 )
(declare-sort B_a_fun_b_a_fun_tree_bool_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun_a_b_a_fun_fun_tree_bool_fun_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-sort B_a_fun_tree$ 0)
(declare-sort B_tree$ 0)
(declare-sort A_a_fun_tree$ 0)
(declare-sort A_b_fun_tree$ 0)
(declare-sort A_b_a_fun_fun_tree$ 0)
(declare-sort B_b_fun_tree$ 0)
(declare-sort B_a_fun_b_fun_tree$ 0)
(declare-sort B_a_fun_a_fun_tree$ 0)
(declare-sort B_b_a_fun_fun_tree$ 0)
(declare-sort B_a_fun_b_a_fun_fun_tree$ 0)
(declare-sort B_a_a_fun_fun_tree$ 0)
(declare-sort A_a_a_fun_fun_tree$ 0)
(declare-fun root$ (A_tree$)A$)
(declare-fun left$ (A_tree$)A_tree$)
(declare-fun right$ (A_tree$)A_tree$)
(declare-fun node$ (A$ A_tree$ A_tree$ )A_tree$)
(declare-fun select$ (B_a_fun_tree$)B_a_fun$)
(declare-fun selecta$ (B_a_fun_tree$)B_a_fun_tree$)
(declare-fun selectb$ (B_a_fun_tree$)B_a_fun_tree$)
(declare-fun node$a (B_a_fun$ B_a_fun_tree$ B_a_fun_tree$ )B_a_fun_tree$)
(declare-fun root$a (B_tree$)B$)
(declare-fun left$a (B_tree$)B_tree$)
(declare-fun right$a (B_tree$)B_tree$)
(declare-fun node$b (B$ B_tree$ B_tree$ )B_tree$)
(declare-fun selectc$ (A_a_fun_tree$)A_a_fun$)
(declare-fun selectd$ (A_a_fun_tree$)A_a_fun_tree$)
(declare-fun selecte$ (A_a_fun_tree$)A_a_fun_tree$)
(declare-fun node$c (A_a_fun$ A_a_fun_tree$ A_a_fun_tree$ )A_a_fun_tree$)
(declare-fun selectf$ (A_b_fun_tree$)A_b_fun$)
(declare-fun selectg$ (A_b_fun_tree$)A_b_fun_tree$)
(declare-fun selecth$ (A_b_fun_tree$)A_b_fun_tree$)
(declare-fun node$d (A_b_fun$ A_b_fun_tree$ A_b_fun_tree$ )A_b_fun_tree$)
(declare-fun selecti$ (A_b_a_fun_fun_tree$)A_b_a_fun_fun$)
(declare-fun selectj$ (A_b_a_fun_fun_tree$)A_b_a_fun_fun_tree$)
(declare-fun selectk$ (A_b_a_fun_fun_tree$)A_b_a_fun_fun_tree$)
(declare-fun node$e (A_b_a_fun_fun$ A_b_a_fun_fun_tree$ A_b_a_fun_fun_tree$ )A_b_a_fun_fun_tree$)
(declare-fun selectl$ (B_b_fun_tree$)B_b_fun$)
(declare-fun selectm$ (B_b_fun_tree$)B_b_fun_tree$)
(declare-fun selectn$ (B_b_fun_tree$)B_b_fun_tree$)
(declare-fun node$f (B_b_fun$ B_b_fun_tree$ B_b_fun_tree$ )B_b_fun_tree$)
(declare-fun selecto$ (B_a_fun_b_fun_tree$)B_a_fun_b_fun$)
(declare-fun selectp$ (B_a_fun_b_fun_tree$)B_a_fun_b_fun_tree$)
(declare-fun selectq$ (B_a_fun_b_fun_tree$)B_a_fun_b_fun_tree$)
(declare-fun node$g (B_a_fun_b_fun$ B_a_fun_b_fun_tree$ B_a_fun_b_fun_tree$ )B_a_fun_b_fun_tree$)
(declare-fun selectr$ (B_a_fun_a_fun_tree$)B_a_fun_a_fun$)
(declare-fun selects$ (B_a_fun_a_fun_tree$)B_a_fun_a_fun_tree$)
(declare-fun selectt$ (B_a_fun_a_fun_tree$)B_a_fun_a_fun_tree$)
(declare-fun node$h (B_a_fun_a_fun$ B_a_fun_a_fun_tree$ B_a_fun_a_fun_tree$ )B_a_fun_a_fun_tree$)
(declare-fun selectu$ (B_b_a_fun_fun_tree$)B_b_a_fun_fun$)
(declare-fun selectv$ (B_b_a_fun_fun_tree$)B_b_a_fun_fun_tree$)
(declare-fun selectw$ (B_b_a_fun_fun_tree$)B_b_a_fun_fun_tree$)
(declare-fun node$i (B_b_a_fun_fun$ B_b_a_fun_fun_tree$ B_b_a_fun_fun_tree$ )B_b_a_fun_fun_tree$)
(declare-fun selectx$ (B_a_fun_b_a_fun_fun_tree$)B_a_fun_b_a_fun_fun$)
(declare-fun selecty$ (B_a_fun_b_a_fun_fun_tree$)B_a_fun_b_a_fun_fun_tree$)
(declare-fun selectz$ (B_a_fun_b_a_fun_fun_tree$)B_a_fun_b_a_fun_fun_tree$)
(declare-fun node$j (B_a_fun_b_a_fun_fun$ B_a_fun_b_a_fun_fun_tree$ B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun_tree$)
(declare-fun selecua$ (B_a_a_fun_fun_tree$)B_a_a_fun_fun$)
(declare-fun selecub$ (B_a_a_fun_fun_tree$)B_a_a_fun_fun_tree$)
(declare-fun selecuc$ (B_a_a_fun_fun_tree$)B_a_a_fun_fun_tree$)
(declare-fun node$k (B_a_a_fun_fun$ B_a_a_fun_fun_tree$ B_a_a_fun_fun_tree$ )B_a_a_fun_fun_tree$)
(declare-fun selecud$ (A_a_a_fun_fun_tree$)A_a_a_fun_fun$)
(declare-fun selecue$ (A_a_a_fun_fun_tree$)A_a_a_fun_fun_tree$)
(declare-fun selecuf$ (A_a_a_fun_fun_tree$)A_a_a_fun_fun_tree$)
(declare-fun node$l (A_a_a_fun_fun$ A_a_a_fun_fun_tree$ A_a_a_fun_fun_tree$ )A_a_a_fun_fun_tree$)
(declare-fun f$ ()B_a_fun$ )
(declare-fun l$ ()B_tree$ )
(declare-fun r$ ()B_tree$ )
(declare-fun x$ ()B$ )
(declare-fun fl$ ()B_a_fun_tree$ )
(declare-fun fr$ ()B_a_fun_tree$ )
(declare-fun left$b (B_b_a_fun_fun_tree$ )B_b_a_fun_fun_tree$ )
(declare-fun left$c (B_b_fun_tree$ )B_b_fun_tree$ )
(declare-fun left$d (A_b_a_fun_fun_tree$ )A_b_a_fun_fun_tree$ )
(declare-fun left$e (A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun left$f (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun left$g (B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun left$h (B_a_fun_b_fun_tree$ )B_a_fun_b_fun_tree$ )
(declare-fun left$i (B_a_fun_a_fun_tree$ )B_a_fun_a_fun_tree$ )
(declare-fun left$j (B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun_tree$ )
(declare-fun left$k (A_a_a_fun_fun_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun root$b (B_b_a_fun_fun_tree$ )B_b_a_fun_fun$ )
(declare-fun root$c (B_b_fun_tree$ )B_b_fun$ )
(declare-fun root$d (A_b_a_fun_fun_tree$ )A_b_a_fun_fun$ )
(declare-fun root$e (A_b_fun_tree$ )A_b_fun$ )
(declare-fun root$f (A_a_fun_tree$ )A_a_fun$ )
(declare-fun root$g (B_a_fun_tree$ )B_a_fun$ )
(declare-fun root$h (B_a_fun_b_fun_tree$ )B_a_fun_b_fun$ )
(declare-fun root$i (B_a_fun_a_fun_tree$ )B_a_fun_a_fun$ )
(declare-fun root$j (B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun$ )
(declare-fun root$k (A_a_a_fun_fun_tree$ )A_a_a_fun_fun$ )
(declare-fun member$ (A_a_fun$ A_a_fun_set$ )Bool )
(declare-fun right$b (B_b_a_fun_fun_tree$ )B_b_a_fun_fun_tree$ )
(declare-fun right$c (B_b_fun_tree$ )B_b_fun_tree$ )
(declare-fun right$d (A_b_a_fun_fun_tree$ )A_b_a_fun_fun_tree$ )
(declare-fun right$e (A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun right$f (A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun right$g (B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun right$h (B_a_fun_b_fun_tree$ )B_a_fun_b_fun_tree$ )
(declare-fun right$i (B_a_fun_a_fun_tree$ )B_a_fun_a_fun_tree$ )
(declare-fun right$j (B_a_fun_b_a_fun_fun_tree$ )B_a_fun_b_a_fun_fun_tree$ )
(declare-fun right$k (A_a_a_fun_fun_tree$ )A_a_a_fun_fun_tree$ )
(declare-fun fun_app$ (B_a_fun$ B$ )A$ )
(declare-fun member$a (A_b_fun$ A_b_fun_set$ )Bool )
(declare-fun member$b (A_b_a_fun_fun$ A_b_a_fun_fun_set$ )Bool )
(declare-fun member$c (B_a_fun$ B_a_fun_set$ )Bool )
(declare-fun member$d (B$ B_set$ )Bool )
(declare-fun member$e (A$ A_set$ )Bool )
(declare-fun tree_ap$ (B_a_fun_tree$ B_tree$ )A_tree$ )
(declare-fun fun_app$a (B_b_fun$ B$ )B$ )
(declare-fun fun_app$b (A_b_fun$ A$ )B$ )
(declare-fun fun_app$c (A_a_fun$ A$ )A$ )
(declare-fun fun_app$d (B_a_fun_b_fun$ B_a_fun$ )B$ )
(declare-fun fun_app$e (B_a_fun_a_fun$ B_a_fun$ )A$ )
(declare-fun fun_app$f (B_b_a_fun_fun$ B$ )B_a_fun$ )
(declare-fun fun_app$g (A_b_a_fun_fun$ A$ )B_a_fun$ )
(declare-fun fun_app$h (B_a_fun_b_a_fun_fun$ B_a_fun$ )B_a_fun$ )
(declare-fun fun_app$i (B_a_a_fun_fun$ B$ )A_a_fun$ )
(declare-fun fun_app$j (A_a_fun_bool_fun$ A_a_fun$ )Bool )
(declare-fun fun_app$k (A_b_fun_bool_fun$ A_b_fun$ )Bool )
(declare-fun fun_app$l (A_b_a_fun_fun_bool_fun$ A_b_a_fun_fun$ )Bool )
(declare-fun fun_app$m (B_a_fun_bool_fun$ B_a_fun$ )Bool )
(declare-fun fun_app$n (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$o (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$p (A_a_fun_tree_bool_fun$ A_a_fun_tree$ )Bool )
(declare-fun fun_app$q (A_a_fun_a_a_fun_tree_bool_fun_fun$ A_a_fun$ )A_a_fun_tree_bool_fun$ )
(declare-fun fun_app$r (A_b_fun_tree_bool_fun$ A_b_fun_tree$ )Bool )
(declare-fun fun_app$s (A_b_fun_a_b_fun_tree_bool_fun_fun$ A_b_fun$ )A_b_fun_tree_bool_fun$ )
(declare-fun fun_app$t (A_b_a_fun_fun_tree_bool_fun$ A_b_a_fun_fun_tree$ )Bool )
(declare-fun fun_app$u (A_b_a_fun_fun_a_b_a_fun_fun_tree_bool_fun_fun$ A_b_a_fun_fun$ )A_b_a_fun_fun_tree_bool_fun$ )
(declare-fun fun_app$v (B_a_fun_tree_bool_fun$ B_a_fun_tree$ )Bool )
(declare-fun fun_app$w (B_a_fun_b_a_fun_tree_bool_fun_fun$ B_a_fun$ )B_a_fun_tree_bool_fun$ )
(declare-fun fun_app$x (B_tree_bool_fun$ B_tree$ )Bool )
(declare-fun fun_app$y (B_b_tree_bool_fun_fun$ B$ )B_tree_bool_fun$ )
(declare-fun fun_app$z (A_tree_bool_fun$ A_tree$ )Bool )
(declare-fun set_tree$ (A_a_fun_tree$ )A_a_fun_set$ )
(declare-fun tree_ap$a (B_b_fun_tree$ B_tree$ )B_tree$ )
(declare-fun tree_ap$b (A_b_fun_tree$ A_tree$ )B_tree$ )
(declare-fun tree_ap$c (A_a_fun_tree$ A_tree$ )A_tree$ )
(declare-fun tree_ap$d (B_a_fun_b_fun_tree$ B_a_fun_tree$ )B_tree$ )
(declare-fun tree_ap$e (B_a_fun_a_fun_tree$ B_a_fun_tree$ )A_tree$ )
(declare-fun tree_ap$f (B_b_a_fun_fun_tree$ B_tree$ )B_a_fun_tree$ )
(declare-fun tree_ap$g (A_b_a_fun_fun_tree$ A_tree$ )B_a_fun_tree$ )
(declare-fun tree_ap$h (B_a_fun_b_a_fun_fun_tree$ B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun tree_ap$i (B_a_a_fun_fun_tree$ B_tree$ )A_a_fun_tree$ )
(declare-fun tree_ap$j (A_a_a_fun_fun_tree$ A_tree$ )A_a_fun_tree$ )
(declare-fun fun_app$aa (A_a_tree_bool_fun_fun$ A$ )A_tree_bool_fun$ )
(declare-fun fun_app$ab (A_a_a_fun_fun$ A$ )A_a_fun$ )
(declare-fun pred_tree$ (A_a_fun_bool_fun$ A_a_fun_tree$ )Bool )
(declare-fun set_tree$a (A_b_fun_tree$ )A_b_fun_set$ )
(declare-fun set_tree$b (A_b_a_fun_fun_tree$ )A_b_a_fun_fun_set$ )
(declare-fun set_tree$c (B_a_fun_tree$ )B_a_fun_set$ )
(declare-fun set_tree$d (B_tree$ )B_set$ )
(declare-fun set_tree$e (A_tree$ )A_set$ )
(declare-fun tree_pure$ (B_b_fun$ )B_b_fun_tree$ )
(declare-fun pred_tree$a (A_b_fun_bool_fun$ A_b_fun_tree$ )Bool )
(declare-fun pred_tree$b (A_b_a_fun_fun_bool_fun$ A_b_a_fun_fun_tree$ )Bool )
(declare-fun pred_tree$c (B_a_fun_bool_fun$ B_a_fun_tree$ )Bool )
(declare-fun pred_tree$d (B_bool_fun$ B_tree$ )Bool )
(declare-fun pred_tree$e (A_bool_fun$ A_tree$ )Bool )
(declare-fun tree_pure$a (B_a_fun$ )B_a_fun_tree$ )
(declare-fun tree_pure$b (A_b_fun$ )A_b_fun_tree$ )
(declare-fun tree_pure$c (A_a_fun$ )A_a_fun_tree$ )
(declare-fun tree_pure$d (B_a_fun_b_fun$ )B_a_fun_b_fun_tree$ )
(declare-fun tree_pure$e (B_a_fun_a_fun$ )B_a_fun_a_fun_tree$ )
(declare-fun tree_pure$f (B_b_a_fun_fun$ )B_b_a_fun_fun_tree$ )
(declare-fun tree_pure$g (A_b_a_fun_fun$ )A_b_a_fun_fun_tree$ )
(declare-fun tree_pure$h (B_a_fun_b_a_fun_fun$ )B_a_fun_b_a_fun_fun_tree$ )
(declare-fun tree_pure$i (B_a_a_fun_fun$ )B_a_a_fun_fun_tree$ )
(declare-fun tree_pure$j (B$ )B_tree$ )
(declare-fun tree_pure$k (A$ )A_tree$ )
(assert (! (not (= (tree_ap$ (node$a f$ fl$ fr$ )(node$b x$ l$ r$ ))(node$ (fun_app$ f$ x$ )(tree_ap$ fl$ l$ )(tree_ap$ fr$ r$ )))):named a0 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ )(?v3 A_a_fun$ )(?v4 A_a_fun_tree$ )(?v5 A_a_fun_tree$ ))(= (= (node$c ?v0 ?v1 ?v2 )(node$c ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a1 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_tree$ )(?v3 A_b_fun$ )(?v4 A_b_fun_tree$ )(?v5 A_b_fun_tree$ ))(= (= (node$d ?v0 ?v1 ?v2 )(node$d ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a2 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ )(?v2 A_b_a_fun_fun_tree$ )(?v3 A_b_a_fun_fun$ )(?v4 A_b_a_fun_fun_tree$ )(?v5 A_b_a_fun_fun_tree$ ))(= (= (node$e ?v0 ?v1 ?v2 )(node$e ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a3 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ ))(= (= (node$a ?v0 ?v1 ?v2 )(node$a ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a4 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ )(?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(= (= (node$b ?v0 ?v1 ?v2 )(node$b ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ )(?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a6 ))
(assert (! (forall ((?v0 A_a_fun_tree$ ))(=> (forall ((?v1 A_a_fun$ )(?v2 A_a_fun_tree$ )(?v3 A_a_fun_tree$ ))(=> (= ?v0 (node$c ?v1 ?v2 ?v3 ))false ))false )):named a7 ))
(assert (! (forall ((?v0 A_b_fun_tree$ ))(=> (forall ((?v1 A_b_fun$ )(?v2 A_b_fun_tree$ )(?v3 A_b_fun_tree$ ))(=> (= ?v0 (node$d ?v1 ?v2 ?v3 ))false ))false )):named a8 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_tree$ ))(=> (forall ((?v1 A_b_a_fun_fun$ )(?v2 A_b_a_fun_fun_tree$ )(?v3 A_b_a_fun_fun_tree$ ))(=> (= ?v0 (node$e ?v1 ?v2 ?v3 ))false ))false )):named a9 ))
(assert (! (forall ((?v0 B_a_fun_tree$ ))(=> (forall ((?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(=> (= ?v0 (node$a ?v1 ?v2 ?v3 ))false ))false )):named a10 ))
(assert (! (forall ((?v0 B_tree$ ))(=> (forall ((?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(=> (= ?v0 (node$b ?v1 ?v2 ?v3 ))false ))false )):named a11 ))
(assert (! (forall ((?v0 A_tree$ ))(=> (forall ((?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(=> (= ?v0 (node$ ?v1 ?v2 ?v3 ))false ))false )):named a12 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$a (tree_pure$ ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$b (fun_app$a ?v0 ?v1 )(tree_ap$a (tree_pure$ ?v0 )?v2 )(tree_ap$a (tree_pure$ ?v0 )?v3 )))):named a13 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$ (tree_pure$a ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$ (fun_app$ ?v0 ?v1 )(tree_ap$ (tree_pure$a ?v0 )?v2 )(tree_ap$ (tree_pure$a ?v0 )?v3 )))):named a14 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(= (tree_ap$b (tree_pure$b ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$b (fun_app$b ?v0 ?v1 )(tree_ap$b (tree_pure$b ?v0 )?v2 )(tree_ap$b (tree_pure$b ?v0 )?v3 )))):named a15 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(= (tree_ap$c (tree_pure$c ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$ (fun_app$c ?v0 ?v1 )(tree_ap$c (tree_pure$c ?v0 )?v2 )(tree_ap$c (tree_pure$c ?v0 )?v3 )))):named a16 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(= (tree_ap$d (tree_pure$d ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$b (fun_app$d ?v0 ?v1 )(tree_ap$d (tree_pure$d ?v0 )?v2 )(tree_ap$d (tree_pure$d ?v0 )?v3 )))):named a17 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(= (tree_ap$e (tree_pure$e ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$ (fun_app$e ?v0 ?v1 )(tree_ap$e (tree_pure$e ?v0 )?v2 )(tree_ap$e (tree_pure$e ?v0 )?v3 )))):named a18 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$f (tree_pure$f ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$a (fun_app$f ?v0 ?v1 )(tree_ap$f (tree_pure$f ?v0 )?v2 )(tree_ap$f (tree_pure$f ?v0 )?v3 )))):named a19 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(= (tree_ap$g (tree_pure$g ?v0 )(node$ ?v1 ?v2 ?v3 ))(node$a (fun_app$g ?v0 ?v1 )(tree_ap$g (tree_pure$g ?v0 )?v2 )(tree_ap$g (tree_pure$g ?v0 )?v3 )))):named a20 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(= (tree_ap$h (tree_pure$h ?v0 )(node$a ?v1 ?v2 ?v3 ))(node$a (fun_app$h ?v0 ?v1 )(tree_ap$h (tree_pure$h ?v0 )?v2 )(tree_ap$h (tree_pure$h ?v0 )?v3 )))):named a21 ))
(assert (! (forall ((?v0 B_a_a_fun_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(= (tree_ap$i (tree_pure$i ?v0 )(node$b ?v1 ?v2 ?v3 ))(node$c (fun_app$i ?v0 ?v1 )(tree_ap$i (tree_pure$i ?v0 )?v2 )(tree_ap$i (tree_pure$i ?v0 )?v3 )))):named a22 ))
(assert (! (forall ((?v0 A_a_fun_bool_fun$ )(?v1 A_a_fun$ )(?v2 A_a_fun_tree$ )(?v3 A_a_fun_tree$ ))(! (= (pred_tree$ ?v0 (node$c ?v1 ?v2 ?v3 ))(and (fun_app$j ?v0 ?v1 )(and (pred_tree$ ?v0 ?v2 )(pred_tree$ ?v0 ?v3 )))):pattern ((pred_tree$ ?v0 (node$c ?v1 ?v2 ?v3 ))))):named a23 ))
(assert (! (forall ((?v0 A_b_fun_bool_fun$ )(?v1 A_b_fun$ )(?v2 A_b_fun_tree$ )(?v3 A_b_fun_tree$ ))(! (= (pred_tree$a ?v0 (node$d ?v1 ?v2 ?v3 ))(and (fun_app$k ?v0 ?v1 )(and (pred_tree$a ?v0 ?v2 )(pred_tree$a ?v0 ?v3 )))):pattern ((pred_tree$a ?v0 (node$d ?v1 ?v2 ?v3 ))))):named a24 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_bool_fun$ )(?v1 A_b_a_fun_fun$ )(?v2 A_b_a_fun_fun_tree$ )(?v3 A_b_a_fun_fun_tree$ ))(! (= (pred_tree$b ?v0 (node$e ?v1 ?v2 ?v3 ))(and (fun_app$l ?v0 ?v1 )(and (pred_tree$b ?v0 ?v2 )(pred_tree$b ?v0 ?v3 )))):pattern ((pred_tree$b ?v0 (node$e ?v1 ?v2 ?v3 ))))):named a25 ))
(assert (! (forall ((?v0 B_a_fun_bool_fun$ )(?v1 B_a_fun$ )(?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(! (= (pred_tree$c ?v0 (node$a ?v1 ?v2 ?v3 ))(and (fun_app$m ?v0 ?v1 )(and (pred_tree$c ?v0 ?v2 )(pred_tree$c ?v0 ?v3 )))):pattern ((pred_tree$c ?v0 (node$a ?v1 ?v2 ?v3 ))))):named a26 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_tree$ )(?v3 B_tree$ ))(! (= (pred_tree$d ?v0 (node$b ?v1 ?v2 ?v3 ))(and (fun_app$n ?v0 ?v1 )(and (pred_tree$d ?v0 ?v2 )(pred_tree$d ?v0 ?v3 )))):pattern ((pred_tree$d ?v0 (node$b ?v1 ?v2 ?v3 ))))):named a27 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_tree$ )(?v3 A_tree$ ))(! (= (pred_tree$e ?v0 (node$ ?v1 ?v2 ?v3 ))(and (fun_app$o ?v0 ?v1 )(and (pred_tree$e ?v0 ?v2 )(pred_tree$e ?v0 ?v3 )))):pattern ((pred_tree$e ?v0 (node$ ?v1 ?v2 ?v3 ))))):named a28 ))
(assert (! (forall ((?v0 B_b_fun$ ))(! (= (tree_pure$ ?v0 )(node$f ?v0 (tree_pure$ ?v0 )(tree_pure$ ?v0 ))):pattern ((tree_pure$ ?v0 )))):named a29 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ ))(! (= (tree_pure$f ?v0 )(node$i ?v0 (tree_pure$f ?v0 )(tree_pure$f ?v0 ))):pattern ((tree_pure$f ?v0 )))):named a30 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ ))(! (= (tree_pure$g ?v0 )(node$e ?v0 (tree_pure$g ?v0 )(tree_pure$g ?v0 ))):pattern ((tree_pure$g ?v0 )))):named a31 ))
(assert (! (forall ((?v0 A_b_fun$ ))(! (= (tree_pure$b ?v0 )(node$d ?v0 (tree_pure$b ?v0 )(tree_pure$b ?v0 ))):pattern ((tree_pure$b ?v0 )))):named a32 ))
(assert (! (forall ((?v0 A_a_fun$ ))(! (= (tree_pure$c ?v0 )(node$c ?v0 (tree_pure$c ?v0 )(tree_pure$c ?v0 ))):pattern ((tree_pure$c ?v0 )))):named a33 ))
(assert (! (forall ((?v0 B_a_fun$ ))(! (= (tree_pure$a ?v0 )(node$a ?v0 (tree_pure$a ?v0 )(tree_pure$a ?v0 ))):pattern ((tree_pure$a ?v0 )))):named a34 ))
(assert (! (forall ((?v0 B$ ))(! (= (tree_pure$j ?v0 )(node$b ?v0 (tree_pure$j ?v0 )(tree_pure$j ?v0 ))):pattern ((tree_pure$j ?v0 )))):named a35 ))
(assert (! (forall ((?v0 A$ ))(! (= (tree_pure$k ?v0 )(node$ ?v0 (tree_pure$k ?v0 )(tree_pure$k ?v0 ))):pattern ((tree_pure$k ?v0 )))):named a36 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_b_a_fun_fun_tree$ )(?v2 B_b_a_fun_fun_tree$ ))(! (= (root$b (node$i ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$i ?v0 ?v1 ?v2 )))):named a37 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_tree$ )(?v2 B_b_fun_tree$ ))(! (= (root$c (node$f ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$f ?v0 ?v1 ?v2 )))):named a38 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ )(?v2 A_b_a_fun_fun_tree$ ))(! (= (root$d (node$e ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$e ?v0 ?v1 ?v2 )))):named a39 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_tree$ ))(! (= (root$e (node$d ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$d ?v0 ?v1 ?v2 )))):named a40 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ ))(! (= (root$f (node$c ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$c ?v0 ?v1 ?v2 )))):named a41 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun_tree$ ))(! (= (root$g (node$a ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a42 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (root$a (node$b ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$b ?v0 ?v1 ?v2 )))):named a43 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (root$ (node$ ?v0 ?v1 ?v2 ))?v0 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a44 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_b_a_fun_fun_tree$ )(?v2 B_b_a_fun_fun_tree$ ))(! (= (left$b (node$i ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$i ?v0 ?v1 ?v2 )))):named a45 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_tree$ )(?v2 B_b_fun_tree$ ))(! (= (left$c (node$f ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$f ?v0 ?v1 ?v2 )))):named a46 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ )(?v2 A_b_a_fun_fun_tree$ ))(! (= (left$d (node$e ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$e ?v0 ?v1 ?v2 )))):named a47 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_tree$ ))(! (= (left$e (node$d ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$d ?v0 ?v1 ?v2 )))):named a48 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ ))(! (= (left$f (node$c ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$c ?v0 ?v1 ?v2 )))):named a49 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun_tree$ ))(! (= (left$g (node$a ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a50 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (left$a (node$b ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$b ?v0 ?v1 ?v2 )))):named a51 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (left$ (node$ ?v0 ?v1 ?v2 ))?v1 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a52 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_b_a_fun_fun_tree$ )(?v2 B_b_a_fun_fun_tree$ ))(! (= (right$b (node$i ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$i ?v0 ?v1 ?v2 )))):named a53 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_tree$ )(?v2 B_b_fun_tree$ ))(! (= (right$c (node$f ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$f ?v0 ?v1 ?v2 )))):named a54 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ )(?v2 A_b_a_fun_fun_tree$ ))(! (= (right$d (node$e ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$e ?v0 ?v1 ?v2 )))):named a55 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_tree$ ))(! (= (right$e (node$d ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$d ?v0 ?v1 ?v2 )))):named a56 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_tree$ ))(! (= (right$f (node$c ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$c ?v0 ?v1 ?v2 )))):named a57 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun_tree$ ))(! (= (right$g (node$a ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$a ?v0 ?v1 ?v2 )))):named a58 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_tree$ ))(! (= (right$a (node$b ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$b ?v0 ?v1 ?v2 )))):named a59 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_tree$ ))(! (= (right$ (node$ ?v0 ?v1 ?v2 ))?v2 ):pattern ((node$ ?v0 ?v1 ?v2 )))):named a60 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun_a_a_fun_tree_bool_fun_fun$ ))(=> (and (member$ ?v0 (set_tree$ ?v1 ))(and (forall ((?v3 A_a_fun$ )(?v4 A_a_fun_tree$ )(?v5 A_a_fun_tree$ ))(fun_app$p (fun_app$q ?v2 ?v3 )(node$c ?v3 ?v4 ?v5 )))(and (forall ((?v3 A_a_fun$ )(?v4 A_a_fun_tree$ )(?v5 A_a_fun_tree$ )(?v6 A_a_fun$ ))(=> (and (member$ ?v6 (set_tree$ ?v4 ))(fun_app$p (fun_app$q ?v2 ?v6 )?v4 ))(fun_app$p (fun_app$q ?v2 ?v6 )(node$c ?v3 ?v4 ?v5 ))))(forall ((?v3 A_a_fun$ )(?v4 A_a_fun_tree$ )(?v5 A_a_fun_tree$ )(?v6 A_a_fun$ ))(=> (and (member$ ?v6 (set_tree$ ?v5 ))(fun_app$p (fun_app$q ?v2 ?v6 )?v5 ))(fun_app$p (fun_app$q ?v2 ?v6 )(node$c ?v3 ?v4 ?v5 )))))))(fun_app$p (fun_app$q ?v2 ?v0 )?v1 ))):named a61 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun_a_b_fun_tree_bool_fun_fun$ ))(=> (and (member$a ?v0 (set_tree$a ?v1 ))(and (forall ((?v3 A_b_fun$ )(?v4 A_b_fun_tree$ )(?v5 A_b_fun_tree$ ))(fun_app$r (fun_app$s ?v2 ?v3 )(node$d ?v3 ?v4 ?v5 )))(and (forall ((?v3 A_b_fun$ )(?v4 A_b_fun_tree$ )(?v5 A_b_fun_tree$ )(?v6 A_b_fun$ ))(=> (and (member$a ?v6 (set_tree$a ?v4 ))(fun_app$r (fun_app$s ?v2 ?v6 )?v4 ))(fun_app$r (fun_app$s ?v2 ?v6 )(node$d ?v3 ?v4 ?v5 ))))(forall ((?v3 A_b_fun$ )(?v4 A_b_fun_tree$ )(?v5 A_b_fun_tree$ )(?v6 A_b_fun$ ))(=> (and (member$a ?v6 (set_tree$a ?v5 ))(fun_app$r (fun_app$s ?v2 ?v6 )?v5 ))(fun_app$r (fun_app$s ?v2 ?v6 )(node$d ?v3 ?v4 ?v5 )))))))(fun_app$r (fun_app$s ?v2 ?v0 )?v1 ))):named a62 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ )(?v2 A_b_a_fun_fun_a_b_a_fun_fun_tree_bool_fun_fun$ ))(=> (and (member$b ?v0 (set_tree$b ?v1 ))(and (forall ((?v3 A_b_a_fun_fun$ )(?v4 A_b_a_fun_fun_tree$ )(?v5 A_b_a_fun_fun_tree$ ))(fun_app$t (fun_app$u ?v2 ?v3 )(node$e ?v3 ?v4 ?v5 )))(and (forall ((?v3 A_b_a_fun_fun$ )(?v4 A_b_a_fun_fun_tree$ )(?v5 A_b_a_fun_fun_tree$ )(?v6 A_b_a_fun_fun$ ))(=> (and (member$b ?v6 (set_tree$b ?v4 ))(fun_app$t (fun_app$u ?v2 ?v6 )?v4 ))(fun_app$t (fun_app$u ?v2 ?v6 )(node$e ?v3 ?v4 ?v5 ))))(forall ((?v3 A_b_a_fun_fun$ )(?v4 A_b_a_fun_fun_tree$ )(?v5 A_b_a_fun_fun_tree$ )(?v6 A_b_a_fun_fun$ ))(=> (and (member$b ?v6 (set_tree$b ?v5 ))(fun_app$t (fun_app$u ?v2 ?v6 )?v5 ))(fun_app$t (fun_app$u ?v2 ?v6 )(node$e ?v3 ?v4 ?v5 )))))))(fun_app$t (fun_app$u ?v2 ?v0 )?v1 ))):named a63 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun_b_a_fun_tree_bool_fun_fun$ ))(=> (and (member$c ?v0 (set_tree$c ?v1 ))(and (forall ((?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ ))(fun_app$v (fun_app$w ?v2 ?v3 )(node$a ?v3 ?v4 ?v5 )))(and (forall ((?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ )(?v6 B_a_fun$ ))(=> (and (member$c ?v6 (set_tree$c ?v4 ))(fun_app$v (fun_app$w ?v2 ?v6 )?v4 ))(fun_app$v (fun_app$w ?v2 ?v6 )(node$a ?v3 ?v4 ?v5 ))))(forall ((?v3 B_a_fun$ )(?v4 B_a_fun_tree$ )(?v5 B_a_fun_tree$ )(?v6 B_a_fun$ ))(=> (and (member$c ?v6 (set_tree$c ?v5 ))(fun_app$v (fun_app$w ?v2 ?v6 )?v5 ))(fun_app$v (fun_app$w ?v2 ?v6 )(node$a ?v3 ?v4 ?v5 )))))))(fun_app$v (fun_app$w ?v2 ?v0 )?v1 ))):named a64 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B_b_tree_bool_fun_fun$ ))(=> (and (member$d ?v0 (set_tree$d ?v1 ))(and (forall ((?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ ))(fun_app$x (fun_app$y ?v2 ?v3 )(node$b ?v3 ?v4 ?v5 )))(and (forall ((?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ )(?v6 B$ ))(=> (and (member$d ?v6 (set_tree$d ?v4 ))(fun_app$x (fun_app$y ?v2 ?v6 )?v4 ))(fun_app$x (fun_app$y ?v2 ?v6 )(node$b ?v3 ?v4 ?v5 ))))(forall ((?v3 B$ )(?v4 B_tree$ )(?v5 B_tree$ )(?v6 B$ ))(=> (and (member$d ?v6 (set_tree$d ?v5 ))(fun_app$x (fun_app$y ?v2 ?v6 )?v5 ))(fun_app$x (fun_app$y ?v2 ?v6 )(node$b ?v3 ?v4 ?v5 )))))))(fun_app$x (fun_app$y ?v2 ?v0 )?v1 ))):named a65 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A_a_tree_bool_fun_fun$ ))(=> (and (member$e ?v0 (set_tree$e ?v1 ))(and (forall ((?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ ))(fun_app$z (fun_app$aa ?v2 ?v3 )(node$ ?v3 ?v4 ?v5 )))(and (forall ((?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ )(?v6 A$ ))(=> (and (member$e ?v6 (set_tree$e ?v4 ))(fun_app$z (fun_app$aa ?v2 ?v6 )?v4 ))(fun_app$z (fun_app$aa ?v2 ?v6 )(node$ ?v3 ?v4 ?v5 ))))(forall ((?v3 A$ )(?v4 A_tree$ )(?v5 A_tree$ )(?v6 A$ ))(=> (and (member$e ?v6 (set_tree$e ?v5 ))(fun_app$z (fun_app$aa ?v2 ?v6 )?v5 ))(fun_app$z (fun_app$aa ?v2 ?v6 )(node$ ?v3 ?v4 ?v5 )))))))(fun_app$z (fun_app$aa ?v2 ?v0 )?v1 ))):named a66 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ ))(=> (and (member$ ?v0 (set_tree$ ?v1 ))(and (forall ((?v2 A_a_fun_tree$ )(?v3 A_a_fun_tree$ ))(=> (= ?v1 (node$c ?v0 ?v2 ?v3 ))false ))(and (forall ((?v2 A_a_fun$ )(?v3 A_a_fun_tree$ )(?v4 A_a_fun_tree$ ))(=> (and (= ?v1 (node$c ?v2 ?v3 ?v4 ))(member$ ?v0 (set_tree$ ?v3 )))false ))(forall ((?v2 A_a_fun$ )(?v3 A_a_fun_tree$ )(?v4 A_a_fun_tree$ ))(=> (and (= ?v1 (node$c ?v2 ?v3 ?v4 ))(member$ ?v0 (set_tree$ ?v4 )))false )))))false )):named a67 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ ))(=> (and (member$a ?v0 (set_tree$a ?v1 ))(and (forall ((?v2 A_b_fun_tree$ )(?v3 A_b_fun_tree$ ))(=> (= ?v1 (node$d ?v0 ?v2 ?v3 ))false ))(and (forall ((?v2 A_b_fun$ )(?v3 A_b_fun_tree$ )(?v4 A_b_fun_tree$ ))(=> (and (= ?v1 (node$d ?v2 ?v3 ?v4 ))(member$a ?v0 (set_tree$a ?v3 )))false ))(forall ((?v2 A_b_fun$ )(?v3 A_b_fun_tree$ )(?v4 A_b_fun_tree$ ))(=> (and (= ?v1 (node$d ?v2 ?v3 ?v4 ))(member$a ?v0 (set_tree$a ?v4 )))false )))))false )):named a68 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ ))(=> (and (member$b ?v0 (set_tree$b ?v1 ))(and (forall ((?v2 A_b_a_fun_fun_tree$ )(?v3 A_b_a_fun_fun_tree$ ))(=> (= ?v1 (node$e ?v0 ?v2 ?v3 ))false ))(and (forall ((?v2 A_b_a_fun_fun$ )(?v3 A_b_a_fun_fun_tree$ )(?v4 A_b_a_fun_fun_tree$ ))(=> (and (= ?v1 (node$e ?v2 ?v3 ?v4 ))(member$b ?v0 (set_tree$b ?v3 )))false ))(forall ((?v2 A_b_a_fun_fun$ )(?v3 A_b_a_fun_fun_tree$ )(?v4 A_b_a_fun_fun_tree$ ))(=> (and (= ?v1 (node$e ?v2 ?v3 ?v4 ))(member$b ?v0 (set_tree$b ?v4 )))false )))))false )):named a69 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ ))(=> (and (member$c ?v0 (set_tree$c ?v1 ))(and (forall ((?v2 B_a_fun_tree$ )(?v3 B_a_fun_tree$ ))(=> (= ?v1 (node$a ?v0 ?v2 ?v3 ))false ))(and (forall ((?v2 B_a_fun$ )(?v3 B_a_fun_tree$ )(?v4 B_a_fun_tree$ ))(=> (and (= ?v1 (node$a ?v2 ?v3 ?v4 ))(member$c ?v0 (set_tree$c ?v3 )))false ))(forall ((?v2 B_a_fun$ )(?v3 B_a_fun_tree$ )(?v4 B_a_fun_tree$ ))(=> (and (= ?v1 (node$a ?v2 ?v3 ?v4 ))(member$c ?v0 (set_tree$c ?v4 )))false )))))false )):named a70 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ ))(=> (and (member$d ?v0 (set_tree$d ?v1 ))(and (forall ((?v2 B_tree$ )(?v3 B_tree$ ))(=> (= ?v1 (node$b ?v0 ?v2 ?v3 ))false ))(and (forall ((?v2 B$ )(?v3 B_tree$ )(?v4 B_tree$ ))(=> (and (= ?v1 (node$b ?v2 ?v3 ?v4 ))(member$d ?v0 (set_tree$d ?v3 )))false ))(forall ((?v2 B$ )(?v3 B_tree$ )(?v4 B_tree$ ))(=> (and (= ?v1 (node$b ?v2 ?v3 ?v4 ))(member$d ?v0 (set_tree$d ?v4 )))false )))))false )):named a71 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(=> (and (member$e ?v0 (set_tree$e ?v1 ))(and (forall ((?v2 A_tree$ )(?v3 A_tree$ ))(=> (= ?v1 (node$ ?v0 ?v2 ?v3 ))false ))(and (forall ((?v2 A$ )(?v3 A_tree$ )(?v4 A_tree$ ))(=> (and (= ?v1 (node$ ?v2 ?v3 ?v4 ))(member$e ?v0 (set_tree$e ?v3 )))false ))(forall ((?v2 A$ )(?v3 A_tree$ )(?v4 A_tree$ ))(=> (and (= ?v1 (node$ ?v2 ?v3 ?v4 ))(member$e ?v0 (set_tree$e ?v4 )))false )))))false )):named a72 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_tree$ )(?v2 A_a_fun$ )(?v3 A_a_fun_tree$ ))(=> (member$ ?v0 (set_tree$ ?v1 ))(member$ ?v0 (set_tree$ (node$c ?v2 ?v1 ?v3 ))))):named a73 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_tree$ )(?v2 A_b_fun$ )(?v3 A_b_fun_tree$ ))(=> (member$a ?v0 (set_tree$a ?v1 ))(member$a ?v0 (set_tree$a (node$d ?v2 ?v1 ?v3 ))))):named a74 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_tree$ )(?v2 A_b_a_fun_fun$ )(?v3 A_b_a_fun_fun_tree$ ))(=> (member$b ?v0 (set_tree$b ?v1 ))(member$b ?v0 (set_tree$b (node$e ?v2 ?v1 ?v3 ))))):named a75 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_tree$ )(?v2 B_a_fun$ )(?v3 B_a_fun_tree$ ))(=> (member$c ?v0 (set_tree$c ?v1 ))(member$c ?v0 (set_tree$c (node$a ?v2 ?v1 ?v3 ))))):named a76 ))
(assert (! (forall ((?v0 B$ )(?v1 B_tree$ )(?v2 B$ )(?v3 B_tree$ ))(=> (member$d ?v0 (set_tree$d ?v1 ))(member$d ?v0 (set_tree$d (node$b ?v2 ?v1 ?v3 ))))):named a77 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ )(?v2 A$ )(?v3 A_tree$ ))(=> (member$e ?v0 (set_tree$e ?v1 ))(member$e ?v0 (set_tree$e (node$ ?v2 ?v1 ?v3 ))))):named a78 ))
(assert (! (forall ((?v0 B_b_a_fun_fun_tree$ ))(= (node$i (root$b ?v0 )(left$b ?v0 )(right$b ?v0 ))?v0 )):named a79 ))
(assert (! (forall ((?v0 B_b_fun_tree$ ))(= (node$f (root$c ?v0 )(left$c ?v0 )(right$c ?v0 ))?v0 )):named a80 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_tree$ ))(= (node$e (root$d ?v0 )(left$d ?v0 )(right$d ?v0 ))?v0 )):named a81 ))
(assert (! (forall ((?v0 A_b_fun_tree$ ))(= (node$d (root$e ?v0 )(left$e ?v0 )(right$e ?v0 ))?v0 )):named a82 ))
(assert (! (forall ((?v0 A_a_fun_tree$ ))(= (node$c (root$f ?v0 )(left$f ?v0 )(right$f ?v0 ))?v0 )):named a83 ))
(assert (! (forall ((?v0 B_a_fun_tree$ ))(= (node$a (root$g ?v0 )(left$g ?v0 )(right$g ?v0 ))?v0 )):named a84 ))
(assert (! (forall ((?v0 B_tree$ ))(= (node$b (root$a ?v0 )(left$a ?v0 )(right$a ?v0 ))?v0 )):named a85 ))
(assert (! (forall ((?v0 A_tree$ ))(= (node$ (root$ ?v0 )(left$ ?v0 )(right$ ?v0 ))?v0 )):named a86 ))
(assert (! (forall ((?v0 B_a_fun_tree$ )(?v1 B_tree$ ))(= (tree_ap$ ?v0 ?v1 )(node$ (fun_app$ (root$g ?v0 )(root$a ?v1 ))(tree_ap$ (left$g ?v0 )(left$a ?v1 ))(tree_ap$ (right$g ?v0 )(right$a ?v1 ))))):named a87 ))
(assert (! (forall ((?v0 A_b_fun_tree$ )(?v1 A_tree$ ))(= (tree_ap$b ?v0 ?v1 )(node$b (fun_app$b (root$e ?v0 )(root$ ?v1 ))(tree_ap$b (left$e ?v0 )(left$ ?v1 ))(tree_ap$b (right$e ?v0 )(right$ ?v1 ))))):named a88 ))
(assert (! (forall ((?v0 A_a_fun_tree$ )(?v1 A_tree$ ))(= (tree_ap$c ?v0 ?v1 )(node$ (fun_app$c (root$f ?v0 )(root$ ?v1 ))(tree_ap$c (left$f ?v0 )(left$ ?v1 ))(tree_ap$c (right$f ?v0 )(right$ ?v1 ))))):named a89 ))
(assert (! (forall ((?v0 B_b_fun_tree$ )(?v1 B_tree$ ))(= (tree_ap$a ?v0 ?v1 )(node$b (fun_app$a (root$c ?v0 )(root$a ?v1 ))(tree_ap$a (left$c ?v0 )(left$a ?v1 ))(tree_ap$a (right$c ?v0 )(right$a ?v1 ))))):named a90 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_tree$ )(?v1 A_tree$ ))(= (tree_ap$g ?v0 ?v1 )(node$a (fun_app$g (root$d ?v0 )(root$ ?v1 ))(tree_ap$g (left$d ?v0 )(left$ ?v1 ))(tree_ap$g (right$d ?v0 )(right$ ?v1 ))))):named a91 ))
(assert (! (forall ((?v0 B_b_a_fun_fun_tree$ )(?v1 B_tree$ ))(= (tree_ap$f ?v0 ?v1 )(node$a (fun_app$f (root$b ?v0 )(root$a ?v1 ))(tree_ap$f (left$b ?v0 )(left$a ?v1 ))(tree_ap$f (right$b ?v0 )(right$a ?v1 ))))):named a92 ))
(assert (! (forall ((?v0 B_a_fun_b_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (tree_ap$d ?v0 ?v1 )(node$b (fun_app$d (root$h ?v0 )(root$g ?v1 ))(tree_ap$d (left$h ?v0 )(left$g ?v1 ))(tree_ap$d (right$h ?v0 )(right$g ?v1 ))))):named a93 ))
(assert (! (forall ((?v0 B_a_fun_a_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (tree_ap$e ?v0 ?v1 )(node$ (fun_app$e (root$i ?v0 )(root$g ?v1 ))(tree_ap$e (left$i ?v0 )(left$g ?v1 ))(tree_ap$e (right$i ?v0 )(right$g ?v1 ))))):named a94 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun_tree$ )(?v1 B_a_fun_tree$ ))(= (tree_ap$h ?v0 ?v1 )(node$a (fun_app$h (root$j ?v0 )(root$g ?v1 ))(tree_ap$h (left$j ?v0 )(left$g ?v1 ))(tree_ap$h (right$j ?v0 )(right$g ?v1 ))))):named a95 ))
(assert (! (forall ((?v0 A_a_a_fun_fun_tree$ )(?v1 A_tree$ ))(= (tree_ap$j ?v0 ?v1 )(node$c (fun_app$ab (root$k ?v0 )(root$ ?v1 ))(tree_ap$j (left$k ?v0 )(left$ ?v1 ))(tree_ap$j (right$k ?v0 )(right$ ?v1 ))))):named a96 ))
(check-sat )
;(get-unsat-core )
