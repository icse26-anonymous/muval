; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --random-seed=1 --lang=smt2 --tlimit 447
;(set-option :produce-unsat-cores true)
(set-logic ALL_SUPPORTED)
(declare-sort A$ 0)
(declare-sort B$ 0)
(declare-sort A_set$ 0)
(declare-sort B_set$ 0)
(declare-sort A_a_fun$ 0)
(declare-sort A_b_fun$ 0)
(declare-sort B_a_fun$ 0)
(declare-sort B_b_fun$ 0)
(declare-sort B_a_fun_set$ 0)
(declare-sort B_b_fun_set$ 0)
(declare-sort A_stream_set$ 0)
(declare-sort B_stream_set$ 0)
(declare-sort B_a_fun_a_fun$ 0)
(declare-sort B_b_a_fun_fun$ 0)
(declare-sort B_b_b_fun_fun$ 0)
(declare-sort B_b_fun_b_fun$ 0)
(declare-sort A_tree_a_tree_fun$ 0)
(declare-sort B_a_fun_a_fun_set$ 0)
(declare-sort B_tree_b_tree_fun$ 0)
(declare-sort B_a_fun_stream_set$ 0)
(declare-sort B_b_fun_stream_set$ 0)
(declare-sort A_a_fun_a_a_fun_fun$ 0)
(declare-sort A_b_fun_a_b_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_b_fun$ 0)
(declare-sort B_a_fun_b_a_fun_fun$ 0)
(declare-sort B_b_a_fun_a_fun_fun$ 0)
(declare-sort B_b_fun_b_b_fun_fun$ 0)
(declare-sort B_stream_stream_set$ 0)
(declare-sort B_stream_b_stream_fun$ 0)
(declare-sort B_a_fun_a_fun_b_fun_set$ 0)
(declare-sort B_b_a_fun_a_fun_fun_set$ 0)
(declare-sort B_a_fun_a_fun_stream_set$ 0)
(declare-sort B_a_fun_tree_b_a_fun_tree_fun$ 0)
(declare-sort B_b_fun_tree_b_b_fun_tree_fun$ 0)
(declare-sort B_a_fun_a_fun_b_fun_stream_set$ 0)
(declare-sort B_b_a_fun_a_fun_fun_stream_set$ 0)
(declare-sort A_a_fun_a_a_fun_a_a_fun_fun_fun$ 0)
(declare-sort A_a_fun_b_a_fun_b_a_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_b_a_fun_a_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_stream_stream_set$ 0)
(declare-sort B_b_a_fun_fun_b_b_a_fun_fun_fun$ 0)
(declare-sort B_b_b_fun_fun_b_b_b_fun_fun_fun$ 0)
(declare-sort B_b_fun_a_b_fun_a_b_fun_fun_fun$ 0)
(declare-sort B_b_fun_b_b_fun_b_b_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_tree_b_a_fun_a_fun_tree_fun$ 0)
(declare-sort A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ 0)
(declare-sort A_a_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ 0)
(declare-sort A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$ 0)
(declare-sort B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ 0)
(declare-sort B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$ 0)
(declare-sort B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_stream_b_a_fun_a_fun_stream_fun$ 0)
(declare-sort B_a_fun_a_fun_b_fun_tree_b_a_fun_a_fun_b_fun_tree_fun$ 0)
(declare-sort B_b_a_fun_a_fun_fun_tree_b_b_a_fun_a_fun_fun_tree_fun$ 0)
(declare-sort B_a_fun_b_a_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ 0)
(declare-sort B_b_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$ 0)
(declare-sort B_b_fun_b_b_fun_fun_b_b_b_fun_fun_b_b_b_fun_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$ 0)
(declare-sort B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$ 0)
(declare-sort B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun_fun$ 0)
(declare-codatatypes () ((A_stream$ (sCons$ (shd$ A$) (stl$ A_stream$)))
  (B_a_fun_stream$ (sCons$a (select$ B_a_fun$) (selecta$ B_a_fun_stream$)))
  (B_stream$ (sCons$b (shd$a B$) (stl$a B_stream$)))
  (B_a_fun_a_fun_stream$ (sCons$c (selectb$ B_a_fun_a_fun$) (selectc$ B_a_fun_a_fun_stream$)))
  (B_b_fun_stream$ (sCons$d (selectd$ B_b_fun$) (selecte$ B_b_fun_stream$)))
  (B_b_a_fun_a_fun_fun_stream$ (sCons$e (selectf$ B_b_a_fun_a_fun_fun$) (selectg$ B_b_a_fun_a_fun_fun_stream$)))
  (B_a_fun_a_fun_b_fun_stream$ (sCons$f (selecth$ B_a_fun_a_fun_b_fun$) (selecti$ B_a_fun_a_fun_b_fun_stream$)))
  (B_a_fun_a_fun_b_a_fun_a_fun_fun_stream$ (sCons$g (selectj$ B_a_fun_a_fun_b_a_fun_a_fun_fun$) (selectk$ B_a_fun_a_fun_b_a_fun_a_fun_fun_stream$)))
  (A_b_fun_stream$ (sCons$h (selectl$ A_b_fun$) (selectm$ A_b_fun_stream$)))
  (A_a_fun_stream$ (sCons$i (selectn$ A_a_fun$) (selecto$ A_a_fun_stream$)))
  (B_b_b_fun_fun_stream$ (sCons$j (selectp$ B_b_b_fun_fun$) (selectq$ B_b_b_fun_fun_stream$)))
  (B_b_a_fun_fun_stream$ (sCons$k (selectr$ B_b_a_fun_fun$) (selects$ B_b_a_fun_fun_stream$)))
  (A_b_fun_a_b_fun_fun_stream$ (sCons$l (selectt$ A_b_fun_a_b_fun_fun$) (selectu$ A_b_fun_a_b_fun_fun_stream$)))
  (A_a_fun_a_a_fun_fun_stream$ (sCons$m (selectv$ A_a_fun_a_a_fun_fun$) (selectw$ A_a_fun_a_a_fun_fun_stream$)))
  (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_stream$ (sCons$n (selectx$ B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$) (selecty$ B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_stream$)))
  (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_stream$ (sCons$o (selectz$ B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$) (selecua$ B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_stream$)))
  (B_b_fun_b_b_fun_fun_stream$ (sCons$p (selecub$ B_b_fun_b_b_fun_fun$) (selecuc$ B_b_fun_b_b_fun_fun_stream$)))
  (B_a_fun_b_a_fun_fun_stream$ (sCons$q (selecud$ B_a_fun_b_a_fun_fun$) (selecue$ B_a_fun_b_a_fun_fun_stream$)))
  (B_a_fun_a_fun_stream_stream$ (sCons$r (shd$b B_a_fun_a_fun_stream$) (stl$b B_a_fun_a_fun_stream_stream$)))
  (B_stream_stream$ (sCons$s (shd$c B_stream$) (stl$c B_stream_stream$)))
  (B_a_fun_a_fun_b_fun_tree$ (node$ (selecuf$ B_a_fun_a_fun_b_fun$) (selecug$ B_a_fun_a_fun_b_fun_tree$) (selecuh$ B_a_fun_a_fun_b_fun_tree$)))
  (B_b_a_fun_a_fun_fun_tree$ (node$a (selecui$ B_b_a_fun_a_fun_fun$) (selecuj$ B_b_a_fun_a_fun_fun_tree$) (selecuk$ B_b_a_fun_a_fun_fun_tree$)))
  (B_b_fun_tree$ (node$b (selecul$ B_b_fun$) (selecum$ B_b_fun_tree$) (selecun$ B_b_fun_tree$)))
  (B_a_fun_tree$ (node$c (selecuo$ B_a_fun$) (selecup$ B_a_fun_tree$) (selecuq$ B_a_fun_tree$)))
  (A_tree$ (node$d (root$ A$) (left$ A_tree$) (right$ A_tree$)))
  (B_tree$ (node$e (root$a B$) (left$a B_tree$) (right$a B_tree$)))
  (B_a_fun_a_fun_tree$ (node$f (selecur$ B_a_fun_a_fun$) (selecus$ B_a_fun_a_fun_tree$) (selecut$ B_a_fun_a_fun_tree$)))))
(declare-fun t$ () B_a_fun_stream$)
(declare-fun x$ () B$)
(declare-fun id$ () B_b_fun$)
(declare-fun uu$ () B_a_fun_a_fun$)
(declare-fun id$a () B_a_fun_a_fun_b_a_fun_a_fun_fun$)
(declare-fun id$b () B_b_fun_b_b_fun_fun$)
(declare-fun id$c () B_a_fun_b_a_fun_fun$)
(declare-fun id$d () A_a_fun$)
(declare-fun id$e () B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$)
(declare-fun id$f () B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$)
(declare-fun id$g () B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$)
(declare-fun id$h () A_b_fun_a_b_fun_fun$)
(declare-fun id$i () A_a_fun_a_a_fun_fun$)
(declare-fun id$j () B_b_b_fun_fun_b_b_b_fun_fun_fun$)
(declare-fun id$k () B_b_a_fun_fun_b_b_a_fun_fun_fun$)
(declare-fun id$l () A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$)
(declare-fun id$m () A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$)
(declare-fun id$n () B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$)
(declare-fun id$o () B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$)
(declare-fun id$p () B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$)
(declare-fun id$q () B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$)
(declare-fun id$r () B_a_fun_a_fun_stream_b_a_fun_a_fun_stream_fun$)
(declare-fun id$s () B_stream_b_stream_fun$)
(declare-fun id$t () B_a_fun_a_fun_b_fun_tree_b_a_fun_a_fun_b_fun_tree_fun$)
(declare-fun id$u () B_b_a_fun_a_fun_fun_tree_b_b_a_fun_a_fun_fun_tree_fun$)
(declare-fun id$v () B_b_fun_tree_b_b_fun_tree_fun$)
(declare-fun id$w () B_a_fun_tree_b_a_fun_tree_fun$)
(declare-fun id$x () A_tree_a_tree_fun$)
(declare-fun id$y () B_tree_b_tree_fun$)
(declare-fun id$z () B_a_fun_a_fun_tree_b_a_fun_a_fun_tree_fun$)
(declare-fun uua$ () A_a_fun$)
(declare-fun uub$ () B_a_fun_a_fun_b_a_fun_a_fun_fun$)
(declare-fun uuc$ () B_b_fun$)
(declare-fun uud$ () B_a_fun_b_a_fun_fun$)
(declare-fun comp$ (B_b_fun$) B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$)
(declare-fun smap$ (B_b_fun$ B_stream$) B_stream$)
(declare-fun comp$a (B_b_fun$) B_b_fun_b_b_fun_fun$)
(declare-fun comp$b (B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$)
(declare-fun comp$c (A_a_fun$) B_a_fun_b_a_fun_fun$)
(declare-fun comp$d (A_a_fun$) B_a_fun_a_fun_b_a_fun_a_fun_fun$)
(declare-fun smap$a (B_b_a_fun_a_fun_fun$ B_stream$) B_a_fun_a_fun_stream$)
(declare-fun smap$b (B_a_fun_a_fun_b_fun$ B_a_fun_a_fun_stream$) B_stream$)
(declare-fun smap$c (B_a_fun_a_fun_b_a_fun_a_fun_fun$ B_a_fun_a_fun_stream$) B_a_fun_a_fun_stream$)
(declare-fun smap$d (B_a_fun$ B_stream$) A_stream$)
(declare-fun smap$e (A_b_fun$ A_stream$) B_stream$)
(declare-fun smap$f (A_a_fun$ A_stream$) A_stream$)
(declare-fun smap$g (B_b_b_fun_fun$ B_stream$) B_b_fun_stream$)
(declare-fun smap$h (B_b_a_fun_fun$ B_stream$) B_a_fun_stream$)
(declare-fun smap$i (B_b_fun_b_fun$ B_b_fun_stream$) B_stream$)
(declare-fun smap$j (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$ B_a_fun_a_fun_b_fun_stream$) B_a_fun_a_fun_b_fun_stream$)
(declare-fun smap$k (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$ B_b_a_fun_a_fun_fun_stream$) B_b_a_fun_a_fun_fun_stream$)
(declare-fun smap$l (B_b_fun_b_b_fun_fun$ B_b_fun_stream$) B_b_fun_stream$)
(declare-fun smap$m (B_a_fun_b_a_fun_fun$ B_a_fun_stream$) B_a_fun_stream$)
(declare-fun st_ap$ (B_a_fun_stream$ B_stream$) A_stream$)
(declare-fun member$ (B_a_fun_a_fun_stream$ B_a_fun_a_fun_stream_set$) Bool)
(declare-fun st_ap$a (B_a_fun_a_fun_stream$ B_a_fun_stream$) A_stream$)
(declare-fun st_ap$b (B_b_fun_stream$ B_stream$) B_stream$)
(declare-fun st_ap$c (B_b_a_fun_a_fun_fun_stream$ B_stream$) B_a_fun_a_fun_stream$)
(declare-fun st_ap$d (B_a_fun_a_fun_b_fun_stream$ B_a_fun_a_fun_stream$) B_stream$)
(declare-fun st_ap$e (B_a_fun_a_fun_b_a_fun_a_fun_fun_stream$ B_a_fun_a_fun_stream$) B_a_fun_a_fun_stream$)
(declare-fun st_ap$f (A_b_fun_stream$ A_stream$) B_stream$)
(declare-fun st_ap$g (A_a_fun_stream$ A_stream$) A_stream$)
(declare-fun st_ap$h (B_b_b_fun_fun_stream$ B_stream$) B_b_fun_stream$)
(declare-fun st_ap$i (B_b_a_fun_fun_stream$ B_stream$) B_a_fun_stream$)
(declare-fun st_ap$j (A_b_fun_a_b_fun_fun_stream$ A_b_fun_stream$) A_b_fun_stream$)
(declare-fun st_ap$k (A_a_fun_a_a_fun_fun_stream$ A_a_fun_stream$) A_a_fun_stream$)
(declare-fun st_ap$l (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_stream$ B_a_fun_a_fun_b_fun_stream$) B_a_fun_a_fun_b_fun_stream$)
(declare-fun st_ap$m (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_stream$ B_b_a_fun_a_fun_fun_stream$) B_b_a_fun_a_fun_fun_stream$)
(declare-fun st_ap$n (B_b_fun_b_b_fun_fun_stream$ B_b_fun_stream$) B_b_fun_stream$)
(declare-fun st_ap$o (B_a_fun_b_a_fun_fun_stream$ B_a_fun_stream$) B_a_fun_stream$)
(declare-fun fun_app$ (B_a_fun_a_fun$ B_a_fun$) A$)
(declare-fun map_fun$ (B_b_fun$) B_b_fun_b_b_fun_b_b_fun_fun_fun$)
(declare-fun member$a (B_a_fun_a_fun_stream_stream$ B_a_fun_a_fun_stream_stream_set$) Bool)
(declare-fun member$b (B_stream$ B_stream_set$) Bool)
(declare-fun member$c (B_stream_stream$ B_stream_stream_set$) Bool)
(declare-fun member$d (B_a_fun_a_fun_b_fun$ B_a_fun_a_fun_b_fun_set$) Bool)
(declare-fun member$e (B_a_fun_a_fun_b_fun_stream$ B_a_fun_a_fun_b_fun_stream_set$) Bool)
(declare-fun member$f (B_b_a_fun_a_fun_fun$ B_b_a_fun_a_fun_fun_set$) Bool)
(declare-fun member$g (B_b_a_fun_a_fun_fun_stream$ B_b_a_fun_a_fun_fun_stream_set$) Bool)
(declare-fun member$h (B_b_fun$ B_b_fun_set$) Bool)
(declare-fun member$i (B_b_fun_stream$ B_b_fun_stream_set$) Bool)
(declare-fun member$j (B_a_fun$ B_a_fun_set$) Bool)
(declare-fun member$k (B_a_fun_stream$ B_a_fun_stream_set$) Bool)
(declare-fun member$l (A$ A_set$) Bool)
(declare-fun member$m (A_stream$ A_stream_set$) Bool)
(declare-fun member$n (B$ B_set$) Bool)
(declare-fun member$o (B_a_fun_a_fun$ B_a_fun_a_fun_set$) Bool)
(declare-fun streams$ (B_a_fun_a_fun_stream_set$) B_a_fun_a_fun_stream_stream_set$)
(declare-fun fun_app$a (B_a_fun$ B$) A$)
(declare-fun fun_app$b (B_a_fun_a_fun_b_a_fun_a_fun_fun$ B_a_fun_a_fun$) B_a_fun_a_fun$)
(declare-fun fun_app$c (B_a_fun_b_a_fun_fun$ B_a_fun$) B_a_fun$)
(declare-fun fun_app$d (B_b_fun$ B$) B$)
(declare-fun fun_app$e (A_a_fun$ A$) A$)
(declare-fun fun_app$f (B_b_a_fun_a_fun_fun$ B$) B_a_fun_a_fun$)
(declare-fun fun_app$g (B_a_fun_a_fun_b_fun$ B_a_fun_a_fun$) B$)
(declare-fun fun_app$h (A_b_fun$ A$) B$)
(declare-fun fun_app$i (B_b_b_fun_fun$ B$) B_b_fun$)
(declare-fun fun_app$j (B_b_a_fun_fun$ B$) B_a_fun$)
(declare-fun fun_app$k (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$ B_a_fun_a_fun_b_fun$) B_a_fun_a_fun_b_fun$)
(declare-fun fun_app$l (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$ B_b_a_fun_a_fun_fun$) B_b_a_fun_a_fun_fun$)
(declare-fun fun_app$m (B_b_fun_b_b_fun_fun$ B_b_fun$) B_b_fun$)
(declare-fun fun_app$n (B_b_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun$) B_b_fun_b_b_fun_fun$)
(declare-fun fun_app$o (A_a_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ A_a_fun$) B_a_fun_a_fun_b_a_fun_a_fun_fun$)
(declare-fun fun_app$p (B_a_fun_a_fun_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$ B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$)
(declare-fun fun_app$q (B_b_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$ B_b_fun$) B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$)
(declare-fun fun_app$r (B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun_fun$ B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$)
(declare-fun fun_app$s (A_a_fun_b_a_fun_b_a_fun_fun_fun$ A_a_fun$) B_a_fun_b_a_fun_fun$)
(declare-fun fun_app$t (B_b_fun_a_b_fun_a_b_fun_fun_fun$ B_b_fun$) A_b_fun_a_b_fun_fun$)
(declare-fun fun_app$u (A_a_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun$) A_a_fun_a_a_fun_fun$)
(declare-fun fun_app$v (B_b_fun_b_b_fun_fun_b_b_b_fun_fun_b_b_b_fun_fun_fun_fun$ B_b_fun_b_b_fun_fun$) B_b_b_fun_fun_b_b_b_fun_fun_fun$)
(declare-fun fun_app$w (B_a_fun_b_a_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ B_a_fun_b_a_fun_fun$) B_b_a_fun_fun_b_b_a_fun_fun_fun$)
(declare-fun fun_app$x (B_b_fun_b_fun$ B_b_fun$) B$)
(declare-fun fun_app$y (B_a_fun_a_fun_b_fun_tree_b_a_fun_a_fun_b_fun_tree_fun$ B_a_fun_a_fun_b_fun_tree$) B_a_fun_a_fun_b_fun_tree$)
(declare-fun fun_app$z (B_b_a_fun_a_fun_fun_tree_b_b_a_fun_a_fun_fun_tree_fun$ B_b_a_fun_a_fun_fun_tree$) B_b_a_fun_a_fun_fun_tree$)
(declare-fun map_fun$a (B_a_fun_b_a_fun_fun$) A_a_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$)
(declare-fun map_fun$b (B_b_fun$) B_a_fun_a_fun_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$)
(declare-fun map_fun$c (B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_b_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$)
(declare-fun map_fun$d (B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun_fun$)
(declare-fun map_fun$e (B_b_fun$) A_a_fun_b_a_fun_b_a_fun_fun_fun$)
(declare-fun map_fun$f (A_a_fun$) B_b_fun_a_b_fun_a_b_fun_fun_fun$)
(declare-fun map_fun$g (A_a_fun$) A_a_fun_a_a_fun_a_a_fun_fun_fun$)
(declare-fun map_fun$h (B_b_fun$) B_b_fun_b_b_fun_fun_b_b_b_fun_fun_b_b_b_fun_fun_fun_fun$)
(declare-fun map_fun$i (B_b_fun$) B_a_fun_b_a_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$)
(declare-fun map_tree$ (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$) B_a_fun_a_fun_b_fun_tree_b_a_fun_a_fun_b_fun_tree_fun$)
(declare-fun siterate$ (B_b_fun$ B$) B_stream$)
(declare-fun streams$a (B_stream_set$) B_stream_stream_set$)
(declare-fun streams$b (B_a_fun_a_fun_b_fun_set$) B_a_fun_a_fun_b_fun_stream_set$)
(declare-fun streams$c (B_b_a_fun_a_fun_fun_set$) B_b_a_fun_a_fun_fun_stream_set$)
(declare-fun streams$d (B_b_fun_set$) B_b_fun_stream_set$)
(declare-fun streams$e (B_a_fun_set$) B_a_fun_stream_set$)
(declare-fun streams$f (A_set$) A_stream_set$)
(declare-fun streams$g (B_set$) B_stream_set$)
(declare-fun streams$h (B_a_fun_a_fun_set$) B_a_fun_a_fun_stream_set$)
(declare-fun fun_app$aa (B_b_fun_tree_b_b_fun_tree_fun$ B_b_fun_tree$) B_b_fun_tree$)
(declare-fun fun_app$ab (B_a_fun_tree_b_a_fun_tree_fun$ B_a_fun_tree$) B_a_fun_tree$)
(declare-fun fun_app$ac (A_tree_a_tree_fun$ A_tree$) A_tree$)
(declare-fun fun_app$ad (B_tree_b_tree_fun$ B_tree$) B_tree$)
(declare-fun fun_app$ae (B_a_fun_a_fun_tree_b_a_fun_a_fun_tree_fun$ B_a_fun_a_fun_tree$) B_a_fun_a_fun_tree$)
(declare-fun fun_app$af (B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_a_fun_a_fun_b_a_fun_a_fun_fun$)
(declare-fun map_tree$a (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$) B_b_a_fun_a_fun_fun_tree_b_b_a_fun_a_fun_fun_tree_fun$)
(declare-fun map_tree$b (B_b_fun_b_b_fun_fun$) B_b_fun_tree_b_b_fun_tree_fun$)
(declare-fun map_tree$c (B_a_fun_b_a_fun_fun$) B_a_fun_tree_b_a_fun_tree_fun$)
(declare-fun map_tree$d (A_a_fun$) A_tree_a_tree_fun$)
(declare-fun map_tree$e (B_b_fun$) B_tree_b_tree_fun$)
(declare-fun map_tree$f (B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_a_fun_a_fun_tree_b_a_fun_a_fun_tree_fun$)
(declare-fun siterate$a (B_a_fun_a_fun_b_a_fun_a_fun_fun$ B_a_fun_a_fun$) B_a_fun_a_fun_stream$)
(declare-fun siterate$b (B_b_fun_b_b_fun_fun$ B_b_fun$) B_b_fun_stream$)
(declare-fun siterate$c (B_a_fun_b_a_fun_fun$ B_a_fun$) B_a_fun_stream$)
(declare-fun siterate$d (A_a_fun$ A$) A_stream$)
(declare-fun siterate$e (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$ B_b_a_fun_a_fun_fun$) B_b_a_fun_a_fun_fun_stream$)
(declare-fun siterate$f (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$ B_a_fun_a_fun_b_fun$) B_a_fun_a_fun_b_fun_stream$)
(declare-fun siterate$g (B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ B_a_fun_a_fun_b_a_fun_a_fun_fun$) B_a_fun_a_fun_b_a_fun_a_fun_fun_stream$)
(declare-fun siterate$h (A_b_fun_a_b_fun_fun$ A_b_fun$) A_b_fun_stream$)
(declare-fun siterate$i (A_a_fun_a_a_fun_fun$ A_a_fun$) A_a_fun_stream$)
(declare-fun siterate$j (B_b_b_fun_fun_b_b_b_fun_fun_fun$ B_b_b_fun_fun$) B_b_b_fun_fun_stream$)
(declare-fun siterate$k (B_b_a_fun_fun_b_b_a_fun_fun_fun$ B_b_a_fun_fun$) B_b_a_fun_fun_stream$)
(declare-fun siterate$l (A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$ A_b_fun_a_b_fun_fun$) A_b_fun_a_b_fun_fun_stream$)
(declare-fun siterate$m (A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun$) A_a_fun_a_a_fun_fun_stream$)
(declare-fun siterate$n (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$ B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$) B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_stream$)
(declare-fun siterate$o (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$ B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$) B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_stream$)
(declare-fun siterate$p (B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun_b_b_fun_fun$) B_b_fun_b_b_fun_fun_stream$)
(declare-fun siterate$q (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun$) B_a_fun_b_a_fun_fun_stream$)
(declare-fun siterate$r (B_a_fun_a_fun_stream_b_a_fun_a_fun_stream_fun$ B_a_fun_a_fun_stream$) B_a_fun_a_fun_stream_stream$)
(declare-fun siterate$s (B_stream_b_stream_fun$ B_stream$) B_stream_stream$)
(declare-fun iso_tuple_update_accessor_eq_assist$ (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$ B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$ B_a_fun_a_fun_b_fun$ B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$ B_a_fun_a_fun_b_fun$ B_a_fun_a_fun_b_fun$) Bool)
(declare-fun iso_tuple_update_accessor_eq_assist$a (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$ B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$ B_b_a_fun_a_fun_fun$ B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$ B_b_a_fun_a_fun_fun$ B_b_a_fun_a_fun_fun$) Bool)
(declare-fun iso_tuple_update_accessor_eq_assist$b (B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun_b_b_fun_fun$ B_b_fun$ B_b_fun_b_b_fun_fun$ B_b_fun$ B_b_fun$) Bool)
(declare-fun iso_tuple_update_accessor_eq_assist$c (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun$ B_a_fun$ B_a_fun_b_a_fun_fun$ B_a_fun$ B_a_fun$) Bool)
(declare-fun iso_tuple_update_accessor_eq_assist$d (A_a_fun_a_a_fun_fun$ A_a_fun$ A$ A_a_fun$ A$ A$) Bool)
(declare-fun iso_tuple_update_accessor_eq_assist$e (B_b_fun_b_b_fun_fun$ B_b_fun$ B$ B_b_fun$ B$ B$) Bool)
(declare-fun iso_tuple_update_accessor_eq_assist$f (B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ B_a_fun_a_fun_b_a_fun_a_fun_fun$ B_a_fun_a_fun$ B_a_fun_a_fun_b_a_fun_a_fun_fun$ B_a_fun_a_fun$ B_a_fun_a_fun$) Bool)
(declare-fun iso_tuple_update_accessor_cong_assist$ (B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_b_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun_fun$ B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$) Bool)
(declare-fun iso_tuple_update_accessor_cong_assist$a (B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_b_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun_fun$ B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$) Bool)
(declare-fun iso_tuple_update_accessor_cong_assist$b (B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun_b_b_fun_fun$) Bool)
(declare-fun iso_tuple_update_accessor_cong_assist$c (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun$) Bool)
(declare-fun iso_tuple_update_accessor_cong_assist$d (A_a_fun_a_a_fun_fun$ A_a_fun$) Bool)
(declare-fun iso_tuple_update_accessor_cong_assist$e (B_b_fun_b_b_fun_fun$ B_b_fun$) Bool)
(declare-fun iso_tuple_update_accessor_cong_assist$f (B_a_fun_a_fun_b_a_fun_a_fun_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ B_a_fun_a_fun_b_a_fun_a_fun_fun$) Bool)
(assert (! (forall ((?v0 B_a_fun$)) (! (= (fun_app$ uu$ ?v0) (fun_app$a ?v0 x$)) :pattern ((fun_app$ uu$ ?v0)))) :named a0))
(assert (! (forall ((?v0 B_a_fun_a_fun$)) (! (= (fun_app$b uub$ ?v0) ?v0) :pattern ((fun_app$b uub$ ?v0)))) :named a1))
(assert (! (forall ((?v0 B_a_fun$)) (! (= (fun_app$c uud$ ?v0) ?v0) :pattern ((fun_app$c uud$ ?v0)))) :named a2))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$d uuc$ ?v0) ?v0) :pattern ((fun_app$d uuc$ ?v0)))) :named a3))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$e uua$ ?v0) ?v0) :pattern ((fun_app$e uua$ ?v0)))) :named a4))
(assert (! (not (= (st_ap$ t$ (siterate$ id$ x$)) (st_ap$a (siterate$a id$a uu$) t$))) :named a5))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B$)) (= (st_ap$b (siterate$b id$b ?v0) (siterate$ id$ ?v1)) (siterate$ id$ (fun_app$d ?v0 ?v1)))) :named a6))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B$)) (= (st_ap$ (siterate$c id$c ?v0) (siterate$ id$ ?v1)) (siterate$d id$d (fun_app$a ?v0 ?v1)))) :named a7))
(assert (! (forall ((?v0 B_a_fun_a_fun$) (?v1 B_a_fun$)) (= (st_ap$a (siterate$a id$a ?v0) (siterate$c id$c ?v1)) (siterate$d id$d (fun_app$ ?v0 ?v1)))) :named a8))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun$) (?v1 B$)) (= (st_ap$c (siterate$e id$e ?v0) (siterate$ id$ ?v1)) (siterate$a id$a (fun_app$f ?v0 ?v1)))) :named a9))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun$) (?v1 B_a_fun_a_fun$)) (= (st_ap$d (siterate$f id$f ?v0) (siterate$a id$a ?v1)) (siterate$ id$ (fun_app$g ?v0 ?v1)))) :named a10))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v1 B_a_fun_a_fun$)) (= (st_ap$e (siterate$g id$g ?v0) (siterate$a id$a ?v1)) (siterate$a id$a (fun_app$b ?v0 ?v1)))) :named a11))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A$)) (= (st_ap$f (siterate$h id$h ?v0) (siterate$d id$d ?v1)) (siterate$ id$ (fun_app$h ?v0 ?v1)))) :named a12))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (st_ap$g (siterate$i id$i ?v0) (siterate$d id$d ?v1)) (siterate$d id$d (fun_app$e ?v0 ?v1)))) :named a13))
(assert (! (forall ((?v0 B_b_b_fun_fun$) (?v1 B$)) (= (st_ap$h (siterate$j id$j ?v0) (siterate$ id$ ?v1)) (siterate$b id$b (fun_app$i ?v0 ?v1)))) :named a14))
(assert (! (forall ((?v0 B_b_a_fun_fun$) (?v1 B$)) (= (st_ap$i (siterate$k id$k ?v0) (siterate$ id$ ?v1)) (siterate$c id$c (fun_app$j ?v0 ?v1)))) :named a15))
(assert (! (forall ((?v0 A_stream$)) (= (st_ap$g (siterate$i id$i uua$) ?v0) ?v0)) :named a16))
(assert (! (forall ((?v0 B_a_fun_a_fun_stream$)) (= (st_ap$e (siterate$g id$g uub$) ?v0) ?v0)) :named a17))
(assert (! (forall ((?v0 B_stream$)) (= (st_ap$b (siterate$b id$b uuc$) ?v0) ?v0)) :named a18))
(assert (! (forall ((?v0 A_b_fun_stream$)) (= (st_ap$j (siterate$l id$l id$h) ?v0) ?v0)) :named a19))
(assert (! (forall ((?v0 A_a_fun_stream$)) (= (st_ap$k (siterate$m id$m id$i) ?v0) ?v0)) :named a20))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun_stream$)) (= (st_ap$l (siterate$n id$n id$f) ?v0) ?v0)) :named a21))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun_stream$)) (= (st_ap$m (siterate$o id$o id$e) ?v0) ?v0)) :named a22))
(assert (! (forall ((?v0 B_b_fun_stream$)) (= (st_ap$n (siterate$p id$p id$b) ?v0) ?v0)) :named a23))
(assert (! (forall ((?v0 B_a_fun_stream$)) (= (st_ap$o (siterate$q id$q id$c) ?v0) ?v0)) :named a24))
(assert (! (forall ((?v0 A_stream$)) (= (st_ap$g (siterate$i id$i id$d) ?v0) ?v0)) :named a25))
(assert (! (forall ((?v0 B_stream$)) (= (st_ap$b (siterate$b id$b id$) ?v0) ?v0)) :named a26))
(assert (! (forall ((?v0 B_a_fun_a_fun_stream$)) (= (st_ap$e (siterate$g id$g id$a) ?v0) ?v0)) :named a27))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun$)) (! (= (fun_app$k id$f ?v0) ?v0) :pattern ((fun_app$k id$f ?v0)))) :named a28))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun$)) (! (= (fun_app$l id$e ?v0) ?v0) :pattern ((fun_app$l id$e ?v0)))) :named a29))
(assert (! (forall ((?v0 B_b_fun$)) (! (= (fun_app$m id$b ?v0) ?v0) :pattern ((fun_app$m id$b ?v0)))) :named a30))
(assert (! (forall ((?v0 B_a_fun$)) (! (= (fun_app$c id$c ?v0) ?v0) :pattern ((fun_app$c id$c ?v0)))) :named a31))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$e id$d ?v0) ?v0) :pattern ((fun_app$e id$d ?v0)))) :named a32))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$d id$ ?v0) ?v0) :pattern ((fun_app$d id$ ?v0)))) :named a33))
(assert (! (forall ((?v0 B_a_fun_a_fun$)) (! (= (fun_app$b id$a ?v0) ?v0) :pattern ((fun_app$b id$a ?v0)))) :named a34))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun$)) (! (= (fun_app$k id$f ?v0) ?v0) :pattern ((fun_app$k id$f ?v0)))) :named a35))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun$)) (! (= (fun_app$l id$e ?v0) ?v0) :pattern ((fun_app$l id$e ?v0)))) :named a36))
(assert (! (forall ((?v0 B_b_fun$)) (! (= (fun_app$m id$b ?v0) ?v0) :pattern ((fun_app$m id$b ?v0)))) :named a37))
(assert (! (forall ((?v0 B_a_fun$)) (! (= (fun_app$c id$c ?v0) ?v0) :pattern ((fun_app$c id$c ?v0)))) :named a38))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$e id$d ?v0) ?v0) :pattern ((fun_app$e id$d ?v0)))) :named a39))
(assert (! (forall ((?v0 B$)) (! (= (fun_app$d id$ ?v0) ?v0) :pattern ((fun_app$d id$ ?v0)))) :named a40))
(assert (! (forall ((?v0 B_a_fun_a_fun$)) (! (= (fun_app$b id$a ?v0) ?v0) :pattern ((fun_app$b id$a ?v0)))) :named a41))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun$) (?v1 B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$) (?v2 B_a_fun_a_fun_b_fun$)) (=> (= ?v0 (fun_app$k ?v1 ?v2)) (iso_tuple_update_accessor_eq_assist$ id$n id$f ?v2 ?v1 ?v0 ?v2))) :named a42))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun$) (?v1 B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$) (?v2 B_b_a_fun_a_fun_fun$)) (=> (= ?v0 (fun_app$l ?v1 ?v2)) (iso_tuple_update_accessor_eq_assist$a id$o id$e ?v2 ?v1 ?v0 ?v2))) :named a43))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_b_fun_b_b_fun_fun$) (?v2 B_b_fun$)) (=> (= ?v0 (fun_app$m ?v1 ?v2)) (iso_tuple_update_accessor_eq_assist$b id$p id$b ?v2 ?v1 ?v0 ?v2))) :named a44))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_a_fun_b_a_fun_fun$) (?v2 B_a_fun$)) (=> (= ?v0 (fun_app$c ?v1 ?v2)) (iso_tuple_update_accessor_eq_assist$c id$q id$c ?v2 ?v1 ?v0 ?v2))) :named a45))
(assert (! (forall ((?v0 A$) (?v1 A_a_fun$) (?v2 A$)) (=> (= ?v0 (fun_app$e ?v1 ?v2)) (iso_tuple_update_accessor_eq_assist$d id$i id$d ?v2 ?v1 ?v0 ?v2))) :named a46))
(assert (! (forall ((?v0 B$) (?v1 B_b_fun$) (?v2 B$)) (=> (= ?v0 (fun_app$d ?v1 ?v2)) (iso_tuple_update_accessor_eq_assist$e id$b id$ ?v2 ?v1 ?v0 ?v2))) :named a47))
(assert (! (forall ((?v0 B_a_fun_a_fun$) (?v1 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v2 B_a_fun_a_fun$)) (=> (= ?v0 (fun_app$b ?v1 ?v2)) (iso_tuple_update_accessor_eq_assist$f id$g id$a ?v2 ?v1 ?v0 ?v2))) :named a48))
(assert (! (iso_tuple_update_accessor_cong_assist$ id$n id$f) :named a49))
(assert (! (iso_tuple_update_accessor_cong_assist$a id$o id$e) :named a50))
(assert (! (iso_tuple_update_accessor_cong_assist$b id$p id$b) :named a51))
(assert (! (iso_tuple_update_accessor_cong_assist$c id$q id$c) :named a52))
(assert (! (iso_tuple_update_accessor_cong_assist$d id$i id$d) :named a53))
(assert (! (iso_tuple_update_accessor_cong_assist$e id$b id$) :named a54))
(assert (! (iso_tuple_update_accessor_cong_assist$f id$g id$a) :named a55))
(assert (! (= (fun_app$n (map_fun$ id$) id$) id$b) :named a56))
(assert (! (= (fun_app$o (map_fun$a id$c) id$d) id$a) :named a57))
(assert (! (= (fun_app$p (map_fun$b id$) id$a) id$e) :named a58))
(assert (! (= (fun_app$q (map_fun$c id$a) id$) id$f) :named a59))
(assert (! (= (fun_app$r (map_fun$d id$a) id$a) id$g) :named a60))
(assert (! (= (fun_app$s (map_fun$e id$) id$d) id$c) :named a61))
(assert (! (= (fun_app$t (map_fun$f id$d) id$) id$h) :named a62))
(assert (! (= (fun_app$u (map_fun$g id$d) id$d) id$i) :named a63))
(assert (! (= (fun_app$v (map_fun$h id$) id$b) id$j) :named a64))
(assert (! (= (fun_app$w (map_fun$i id$) id$c) id$k) :named a65))
(assert (! (forall ((?v0 B_a_fun_a_fun_stream$) (?v1 B_a_fun_a_fun_stream_set$)) (=> (member$ ?v0 ?v1) (member$a (siterate$r id$r ?v0) (streams$ ?v1)))) :named a66))
(assert (! (forall ((?v0 B_stream$) (?v1 B_stream_set$)) (=> (member$b ?v0 ?v1) (member$c (siterate$s id$s ?v0) (streams$a ?v1)))) :named a67))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun$) (?v1 B_a_fun_a_fun_b_fun_set$)) (=> (member$d ?v0 ?v1) (member$e (siterate$f id$f ?v0) (streams$b ?v1)))) :named a68))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun$) (?v1 B_b_a_fun_a_fun_fun_set$)) (=> (member$f ?v0 ?v1) (member$g (siterate$e id$e ?v0) (streams$c ?v1)))) :named a69))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_b_fun_set$)) (=> (member$h ?v0 ?v1) (member$i (siterate$b id$b ?v0) (streams$d ?v1)))) :named a70))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B_a_fun_set$)) (=> (member$j ?v0 ?v1) (member$k (siterate$c id$c ?v0) (streams$e ?v1)))) :named a71))
(assert (! (forall ((?v0 A$) (?v1 A_set$)) (=> (member$l ?v0 ?v1) (member$m (siterate$d id$d ?v0) (streams$f ?v1)))) :named a72))
(assert (! (forall ((?v0 B$) (?v1 B_set$)) (=> (member$n ?v0 ?v1) (member$b (siterate$ id$ ?v0) (streams$g ?v1)))) :named a73))
(assert (! (forall ((?v0 B_a_fun_a_fun$) (?v1 B_a_fun_a_fun_set$)) (=> (member$o ?v0 ?v1) (member$ (siterate$a id$a ?v0) (streams$h ?v1)))) :named a74))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B$)) (= (smap$ ?v0 (siterate$ id$ ?v1)) (siterate$ id$ (fun_app$d ?v0 ?v1)))) :named a75))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun$) (?v1 B$)) (= (smap$a ?v0 (siterate$ id$ ?v1)) (siterate$a id$a (fun_app$f ?v0 ?v1)))) :named a76))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun$) (?v1 B_a_fun_a_fun$)) (= (smap$b ?v0 (siterate$a id$a ?v1)) (siterate$ id$ (fun_app$g ?v0 ?v1)))) :named a77))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v1 B_a_fun_a_fun$)) (= (smap$c ?v0 (siterate$a id$a ?v1)) (siterate$a id$a (fun_app$b ?v0 ?v1)))) :named a78))
(assert (! (forall ((?v0 B_a_fun$) (?v1 B$)) (= (smap$d ?v0 (siterate$ id$ ?v1)) (siterate$d id$d (fun_app$a ?v0 ?v1)))) :named a79))
(assert (! (forall ((?v0 A_b_fun$) (?v1 A$)) (= (smap$e ?v0 (siterate$d id$d ?v1)) (siterate$ id$ (fun_app$h ?v0 ?v1)))) :named a80))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (smap$f ?v0 (siterate$d id$d ?v1)) (siterate$d id$d (fun_app$e ?v0 ?v1)))) :named a81))
(assert (! (forall ((?v0 B_b_b_fun_fun$) (?v1 B$)) (= (smap$g ?v0 (siterate$ id$ ?v1)) (siterate$b id$b (fun_app$i ?v0 ?v1)))) :named a82))
(assert (! (forall ((?v0 B_b_a_fun_fun$) (?v1 B$)) (= (smap$h ?v0 (siterate$ id$ ?v1)) (siterate$c id$c (fun_app$j ?v0 ?v1)))) :named a83))
(assert (! (forall ((?v0 B_b_fun_b_fun$) (?v1 B_b_fun$)) (= (smap$i ?v0 (siterate$b id$b ?v1)) (siterate$ id$ (fun_app$x ?v0 ?v1)))) :named a84))
(assert (! (= (comp$ id$) id$f) :named a85))
(assert (! (= (comp$a id$) id$b) :named a86))
(assert (! (= (comp$b id$a) id$e) :named a87))
(assert (! (= (comp$c id$d) id$c) :named a88))
(assert (! (= (comp$d id$d) id$a) :named a89))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun_b_a_fun_a_fun_b_fun_fun$) (?v1 B_a_fun_a_fun_b_fun$)) (= (smap$j ?v0 (siterate$f ?v0 ?v1)) (siterate$f ?v0 (fun_app$k ?v0 ?v1)))) :named a90))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun_b_b_a_fun_a_fun_fun_fun$) (?v1 B_b_a_fun_a_fun_fun$)) (= (smap$k ?v0 (siterate$e ?v0 ?v1)) (siterate$e ?v0 (fun_app$l ?v0 ?v1)))) :named a91))
(assert (! (forall ((?v0 B_b_fun_b_b_fun_fun$) (?v1 B_b_fun$)) (= (smap$l ?v0 (siterate$b ?v0 ?v1)) (siterate$b ?v0 (fun_app$m ?v0 ?v1)))) :named a92))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$) (?v1 B_a_fun$)) (= (smap$m ?v0 (siterate$c ?v0 ?v1)) (siterate$c ?v0 (fun_app$c ?v0 ?v1)))) :named a93))
(assert (! (forall ((?v0 A_a_fun$) (?v1 A$)) (= (smap$f ?v0 (siterate$d ?v0 ?v1)) (siterate$d ?v0 (fun_app$e ?v0 ?v1)))) :named a94))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B$)) (= (smap$ ?v0 (siterate$ ?v0 ?v1)) (siterate$ ?v0 (fun_app$d ?v0 ?v1)))) :named a95))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v1 B_a_fun_a_fun$)) (= (smap$c ?v0 (siterate$a ?v0 ?v1)) (siterate$a ?v0 (fun_app$b ?v0 ?v1)))) :named a96))
(assert (! (= (fun_app$s (map_fun$e uuc$) uua$) id$c) :named a97))
(assert (! (= (fun_app$r (map_fun$d uub$) uub$) id$g) :named a98))
(assert (! (= (fun_app$q (map_fun$c uub$) uuc$) id$f) :named a99))
(assert (! (= (fun_app$p (map_fun$b uuc$) uub$) id$e) :named a100))
(assert (! (= (fun_app$n (map_fun$ uuc$) uuc$) id$b) :named a101))
(assert (! (= (fun_app$o (map_fun$a uud$) uua$) id$a) :named a102))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_fun_tree$)) (= (fun_app$y (map_tree$ id$f) ?v0) ?v0)) :named a103))
(assert (! (forall ((?v0 B_b_a_fun_a_fun_fun_tree$)) (= (fun_app$z (map_tree$a id$e) ?v0) ?v0)) :named a104))
(assert (! (forall ((?v0 B_b_fun_tree$)) (= (fun_app$aa (map_tree$b id$b) ?v0) ?v0)) :named a105))
(assert (! (forall ((?v0 B_a_fun_tree$)) (= (fun_app$ab (map_tree$c id$c) ?v0) ?v0)) :named a106))
(assert (! (forall ((?v0 A_tree$)) (= (fun_app$ac (map_tree$d id$d) ?v0) ?v0)) :named a107))
(assert (! (forall ((?v0 B_tree$)) (= (fun_app$ad (map_tree$e id$) ?v0) ?v0)) :named a108))
(assert (! (forall ((?v0 B_a_fun_a_fun_tree$)) (= (fun_app$ae (map_tree$f id$a) ?v0) ?v0)) :named a109))
(assert (! (= (map_tree$ id$f) id$t) :named a110))
(assert (! (= (map_tree$a id$e) id$u) :named a111))
(assert (! (= (map_tree$b id$b) id$v) :named a112))
(assert (! (= (map_tree$c id$c) id$w) :named a113))
(assert (! (= (map_tree$d id$d) id$x) :named a114))
(assert (! (= (map_tree$e id$) id$y) :named a115))
(assert (! (= (map_tree$f id$a) id$z) :named a116))
(assert (! (forall ((?v0 A_a_fun$) (?v1 B_a_fun_a_fun$) (?v2 B_a_fun$)) (! (= (fun_app$ (fun_app$b (comp$d ?v0) ?v1) ?v2) (fun_app$e ?v0 (fun_app$ ?v1 ?v2))) :pattern ((fun_app$ (fun_app$b (comp$d ?v0) ?v1) ?v2)))) :named a117))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v1 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v2 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v3 B_a_fun_a_fun$)) (! (= (fun_app$b (fun_app$af (fun_app$r (map_fun$d ?v0) ?v1) ?v2) ?v3) (fun_app$b ?v1 (fun_app$b ?v2 (fun_app$b ?v0 ?v3)))) :pattern ((fun_app$b (fun_app$af (fun_app$r (map_fun$d ?v0) ?v1) ?v2) ?v3)))) :named a118))
(assert (! (forall ((?v0 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v1 B_b_fun$) (?v2 B_a_fun_a_fun_b_fun$) (?v3 B_a_fun_a_fun$)) (! (= (fun_app$g (fun_app$k (fun_app$q (map_fun$c ?v0) ?v1) ?v2) ?v3) (fun_app$d ?v1 (fun_app$g ?v2 (fun_app$b ?v0 ?v3)))) :pattern ((fun_app$g (fun_app$k (fun_app$q (map_fun$c ?v0) ?v1) ?v2) ?v3)))) :named a119))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_a_fun_a_fun_b_a_fun_a_fun_fun$) (?v2 B_b_a_fun_a_fun_fun$) (?v3 B$)) (! (= (fun_app$f (fun_app$l (fun_app$p (map_fun$b ?v0) ?v1) ?v2) ?v3) (fun_app$b ?v1 (fun_app$f ?v2 (fun_app$d ?v0 ?v3)))) :pattern ((fun_app$f (fun_app$l (fun_app$p (map_fun$b ?v0) ?v1) ?v2) ?v3)))) :named a120))
(assert (! (forall ((?v0 B_b_fun$) (?v1 B_b_fun$) (?v2 B_b_fun$) (?v3 B$)) (! (= (fun_app$d (fun_app$m (fun_app$n (map_fun$ ?v0) ?v1) ?v2) ?v3) (fun_app$d ?v1 (fun_app$d ?v2 (fun_app$d ?v0 ?v3)))) :pattern ((fun_app$d (fun_app$m (fun_app$n (map_fun$ ?v0) ?v1) ?v2) ?v3)))) :named a121))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$) (?v1 A_a_fun$) (?v2 B_a_fun_a_fun$) (?v3 B_a_fun$)) (! (= (fun_app$ (fun_app$b (fun_app$o (map_fun$a ?v0) ?v1) ?v2) ?v3) (fun_app$e ?v1 (fun_app$ ?v2 (fun_app$c ?v0 ?v3)))) :pattern ((fun_app$ (fun_app$b (fun_app$o (map_fun$a ?v0) ?v1) ?v2) ?v3)))) :named a122))
(check-sat)
;(get-unsat-core)
