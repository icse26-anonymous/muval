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
(declare-sort A_a_fun_set$ 0 )
(declare-sort A_b_fun_set$ 0 )
(declare-sort B_a_fun_set$ 0 )
(declare-sort B_b_fun_set$ 0 )
(declare-sort A_stream_set$ 0 )
(declare-sort B_stream_set$ 0 )
(declare-sort A_a_a_fun_fun$ 0 )
(declare-sort A_a_b_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun$ 0 )
(declare-sort A_b_b_fun_fun$ 0 )
(declare-sort A_b_fun_b_fun$ 0 )
(declare-sort B_a_fun_a_fun$ 0 )
(declare-sort B_a_fun_b_fun$ 0 )
(declare-sort B_b_a_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun_set$ 0 )
(declare-sort A_tree_a_tree_fun$ 0 )
(declare-sort B_b_a_fun_fun_set$ 0 )
(declare-sort B_tree_b_tree_fun$ 0 )
(declare-sort A_a_fun_stream_set$ 0 )
(declare-sort A_b_fun_stream_set$ 0 )
(declare-sort B_a_fun_stream_set$ 0 )
(declare-sort B_b_fun_stream_set$ 0 )
(declare-sort A_a_fun_a_a_fun_fun$ 0 )
(declare-sort A_b_fun_a_b_fun_fun$ 0 )
(declare-sort A_stream_stream_set$ 0 )
(declare-sort B_a_fun_b_a_fun_fun$ 0 )
(declare-sort B_b_fun_b_b_fun_fun$ 0 )
(declare-sort B_stream_stream_set$ 0 )
(declare-sort A_stream_a_stream_fun$ 0 )
(declare-sort B_stream_b_stream_fun$ 0 )
(declare-sort A_b_a_fun_fun_stream_set$ 0 )
(declare-sort B_b_a_fun_fun_stream_set$ 0 )
(declare-sort A_a_fun_tree_a_a_fun_tree_fun$ 0 )
(declare-sort A_b_fun_tree_a_b_fun_tree_fun$ 0 )
(declare-sort B_a_fun_tree_b_a_fun_tree_fun$ 0 )
(declare-sort B_b_fun_tree_b_b_fun_tree_fun$ 0 )
(declare-sort A_a_a_fun_fun_a_a_a_fun_fun_fun$ 0 )
(declare-sort A_a_b_fun_fun_a_a_b_fun_fun_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_a_a_fun_fun_fun$ 0 )
(declare-sort A_a_fun_b_a_fun_b_a_fun_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun_a_b_a_fun_fun_fun$ 0 )
(declare-sort A_b_b_fun_fun_a_b_b_fun_fun_fun$ 0 )
(declare-sort B_a_fun_a_fun_b_a_fun_a_fun_fun$ 0 )
(declare-sort B_a_fun_b_fun_b_a_fun_b_fun_fun$ 0 )
(declare-sort B_b_a_fun_fun_b_b_a_fun_fun_fun$ 0 )
(declare-sort B_b_b_fun_fun_b_b_b_fun_fun_fun$ 0 )
(declare-sort B_b_fun_a_b_fun_a_b_fun_fun_fun$ 0 )
(declare-sort B_b_fun_b_b_fun_b_b_fun_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun_tree_a_b_a_fun_fun_tree_fun$ 0 )
(declare-sort B_b_a_fun_fun_tree_b_b_a_fun_fun_tree_fun$ 0 )
(declare-sort A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ 0 )
(declare-sort A_a_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ 0 )
(declare-sort A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$ 0 )
(declare-sort B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ 0 )
(declare-sort B_b_fun_b_a_fun_b_fun_b_a_fun_b_fun_fun_fun$ 0 )
(declare-sort B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ 0 )
(declare-sort B_a_fun_b_a_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ 0 )
(declare-sort B_a_fun_b_a_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ 0 )
(declare-sort B_b_fun_b_b_fun_fun_b_b_b_fun_fun_b_b_b_fun_fun_fun_fun$ 0 )
(declare-sort A_a_a_fun_fun_a_a_a_fun_fun_fun_a_a_a_fun_fun_a_a_a_fun_fun_fun_fun$ 0 )
(declare-sort A_a_b_fun_fun_a_a_b_fun_fun_fun_a_a_b_fun_fun_a_a_b_fun_fun_fun_fun$ 0 )
(declare-sort A_b_a_fun_fun_a_b_a_fun_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ 0 )
(declare-sort A_b_b_fun_fun_a_b_b_fun_fun_fun_a_b_b_fun_fun_a_b_b_fun_fun_fun_fun$ 0 )
(declare-sort B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun_fun$ 0 )
(declare-sort B_b_a_fun_fun_b_b_a_fun_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ 0 )
(declare-codatatypes ()((A_stream$ (sCons$ (shd$ A$ )(stl$ A_stream$ )))(B_a_fun_stream$ (sCons$a (select$ B_a_fun$ )(selecta$ B_a_fun_stream$ )))(B_stream$ (sCons$b (shd$a B$ )(stl$a B_stream$ )))(B_b_fun_stream$ (sCons$c (selectb$ B_b_fun$ )(selectc$ B_b_fun_stream$ )))(A_a_fun_stream$ (sCons$d (selectd$ A_a_fun$ )(selecte$ A_a_fun_stream$ )))(B_a_fun_b_a_fun_fun_stream$ (sCons$e (selectf$ B_a_fun_b_a_fun_fun$ )(selectg$ B_a_fun_b_a_fun_fun_stream$ )))(B_b_fun_b_b_fun_fun_stream$ (sCons$f (selecth$ B_b_fun_b_b_fun_fun$ )(selecti$ B_b_fun_b_b_fun_fun_stream$ )))(A_b_fun_stream$ (sCons$g (selectj$ A_b_fun$ )(selectk$ A_b_fun_stream$ )))(A_b_fun_a_b_fun_fun_stream$ (sCons$h (selectl$ A_b_fun_a_b_fun_fun$ )(selectm$ A_b_fun_a_b_fun_fun_stream$ )))(A_a_fun_a_a_fun_fun_stream$ (sCons$i (selectn$ A_a_fun_a_a_fun_fun$ )(selecto$ A_a_fun_a_a_fun_fun_stream$ )))(B_b_a_fun_fun_stream$ (sCons$j (selectp$ B_b_a_fun_fun$ )(selectq$ B_b_a_fun_fun_stream$ )))(B_b_a_fun_fun_b_b_a_fun_fun_fun_stream$ (sCons$k (selectr$ B_b_a_fun_fun_b_b_a_fun_fun_fun$ )(selects$ B_b_a_fun_fun_b_b_a_fun_fun_fun_stream$ )))(A_b_a_fun_fun_stream$ (sCons$l (selectt$ A_b_a_fun_fun$ )(selectu$ A_b_a_fun_fun_stream$ )))(A_b_a_fun_fun_a_b_a_fun_fun_fun_stream$ (sCons$m (selectv$ A_b_a_fun_fun_a_b_a_fun_fun_fun$ )(selectw$ A_b_a_fun_fun_a_b_a_fun_fun_fun_stream$ )))(A_b_b_fun_fun_stream$ (sCons$n (selectx$ A_b_b_fun_fun$ )(selecty$ A_b_b_fun_fun_stream$ )))(A_b_b_fun_fun_a_b_b_fun_fun_fun_stream$ (sCons$o (selectz$ A_b_b_fun_fun_a_b_b_fun_fun_fun$ )(selecua$ A_b_b_fun_fun_a_b_b_fun_fun_fun_stream$ )))(A_a_b_fun_fun_stream$ (sCons$p (selecub$ A_a_b_fun_fun$ )(selecuc$ A_a_b_fun_fun_stream$ )))(A_a_b_fun_fun_a_a_b_fun_fun_fun_stream$ (sCons$q (selecud$ A_a_b_fun_fun_a_a_b_fun_fun_fun$ )(selecue$ A_a_b_fun_fun_a_a_b_fun_fun_fun_stream$ )))(B_stream_stream$ (sCons$r (shd$b B_stream$ )(stl$b B_stream_stream$ )))(A_stream_stream$ (sCons$s (shd$c A_stream$ )(stl$c A_stream_stream$ )))(B_b_a_fun_fun_tree$ (node$ (selecuf$ B_b_a_fun_fun$ )(selecug$ B_b_a_fun_fun_tree$ )(selecuh$ B_b_a_fun_fun_tree$ )))(B_b_fun_tree$ (node$a (selecui$ B_b_fun$ )(selecuj$ B_b_fun_tree$ )(selecuk$ B_b_fun_tree$ )))(A_b_a_fun_fun_tree$ (node$b (selecul$ A_b_a_fun_fun$ )(selecum$ A_b_a_fun_fun_tree$ )(selecun$ A_b_a_fun_fun_tree$ )))(A_b_fun_tree$ (node$c (selecuo$ A_b_fun$ )(selecup$ A_b_fun_tree$ )(selecuq$ A_b_fun_tree$ )))(A_a_fun_tree$ (node$d (selecur$ A_a_fun$ )(selecus$ A_a_fun_tree$ )(selecut$ A_a_fun_tree$ )))(B_a_fun_tree$ (node$e (selecuu$ B_a_fun$ )(selecuv$ B_a_fun_tree$ )(selecuw$ B_a_fun_tree$ )))(B_tree$ (node$f (root$ B$ )(left$ B_tree$ )(right$ B_tree$ )))(A_tree$ (node$g (root$a A$ )(left$a A_tree$ )(right$a A_tree$ )))))
(declare-fun f$ ()B_a_fun$ )
(declare-fun x$ ()B$ )
(declare-fun id$ ()B_a_fun_b_a_fun_fun$ )
(declare-fun uu$ ()A_a_fun$ )
(declare-fun id$a ()B_b_fun$ )
(declare-fun id$b ()A_a_fun$ )
(declare-fun id$c ()B_b_fun_b_b_fun_fun$ )
(declare-fun id$d ()A_a_fun_a_a_fun_fun$ )
(declare-fun id$e ()B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ )
(declare-fun id$f ()B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ )
(declare-fun id$g ()A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$ )
(declare-fun id$h ()A_b_fun_a_b_fun_fun$ )
(declare-fun id$i ()A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ )
(declare-fun id$j ()B_b_a_fun_fun_b_b_a_fun_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ )
(declare-fun id$k ()B_b_a_fun_fun_b_b_a_fun_fun_fun$ )
(declare-fun id$l ()A_b_a_fun_fun_a_b_a_fun_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ )
(declare-fun id$m ()A_b_a_fun_fun_a_b_a_fun_fun_fun$ )
(declare-fun id$n ()A_b_b_fun_fun_a_b_b_fun_fun_fun_a_b_b_fun_fun_a_b_b_fun_fun_fun_fun$ )
(declare-fun id$o ()A_b_b_fun_fun_a_b_b_fun_fun_fun$ )
(declare-fun id$p ()A_a_b_fun_fun_a_a_b_fun_fun_fun_a_a_b_fun_fun_a_a_b_fun_fun_fun_fun$ )
(declare-fun id$q ()A_a_b_fun_fun_a_a_b_fun_fun_fun$ )
(declare-fun id$r ()A_a_a_fun_fun_a_a_a_fun_fun_fun_a_a_a_fun_fun_a_a_a_fun_fun_fun_fun$ )
(declare-fun id$s ()A_a_a_fun_fun_a_a_a_fun_fun_fun$ )
(declare-fun id$t ()B_a_fun_b_fun_b_a_fun_b_fun_fun$ )
(declare-fun id$u ()B_a_fun_a_fun_b_a_fun_a_fun_fun$ )
(declare-fun id$v ()B_b_b_fun_fun_b_b_b_fun_fun_fun$ )
(declare-fun id$w ()B_stream_b_stream_fun$ )
(declare-fun id$x ()A_stream_a_stream_fun$ )
(declare-fun id$y ()B_b_a_fun_fun_tree_b_b_a_fun_fun_tree_fun$ )
(declare-fun id$z ()B_b_fun_tree_b_b_fun_tree_fun$ )
(declare-fun uua$ ()B_b_fun$ )
(declare-fun uub$ ()B_a_fun_b_a_fun_fun$ )
(declare-fun comp$ (B_a_fun_b_a_fun_fun$ )B_b_a_fun_fun_b_b_a_fun_fun_fun$ )
(declare-fun id$aa ()A_b_a_fun_fun_tree_a_b_a_fun_fun_tree_fun$ )
(declare-fun id$ab ()A_b_fun_tree_a_b_fun_tree_fun$ )
(declare-fun id$ac ()A_a_fun_tree_a_a_fun_tree_fun$ )
(declare-fun id$ad ()B_a_fun_tree_b_a_fun_tree_fun$ )
(declare-fun id$ae ()B_tree_b_tree_fun$ )
(declare-fun id$af ()A_tree_a_tree_fun$ )
(declare-fun smap$ (B_b_fun$ B_stream$ )B_stream$ )
(declare-fun comp$a (B_a_fun_b_a_fun_fun$ )A_b_a_fun_fun_a_b_a_fun_fun_fun$ )
(declare-fun comp$b (B_b_fun$ )B_b_fun_b_b_fun_fun$ )
(declare-fun comp$c (B_b_fun$ )A_b_fun_a_b_fun_fun$ )
(declare-fun comp$d (A_a_fun$ )A_a_fun_a_a_fun_fun$ )
(declare-fun comp$e (A_a_fun$ )B_a_fun_b_a_fun_fun$ )
(declare-fun smap$a (B_a_fun$ B_stream$ )A_stream$ )
(declare-fun smap$b (A_b_fun$ A_stream$ )B_stream$ )
(declare-fun smap$c (A_a_fun$ A_stream$ )A_stream$ )
(declare-fun smap$d (B_a_fun_b_fun$ B_a_fun_stream$ )B_stream$ )
(declare-fun smap$e (B_a_fun_a_fun$ B_a_fun_stream$ )A_stream$ )
(declare-fun smap$f (B_b_a_fun_fun$ B_stream$ )B_a_fun_stream$ )
(declare-fun smap$g (A_b_a_fun_fun$ A_stream$ )B_a_fun_stream$ )
(declare-fun smap$h (B_a_fun_b_a_fun_fun$ B_a_fun_stream$ )B_a_fun_stream$ )
(declare-fun smap$i (A_b_fun_b_fun$ A_b_fun_stream$ )B_stream$ )
(declare-fun smap$j (A_a_fun_a_a_fun_fun$ A_a_fun_stream$ )A_a_fun_stream$ )
(declare-fun smap$k (B_b_fun_b_b_fun_fun$ B_b_fun_stream$ )B_b_fun_stream$ )
(declare-fun smap$l (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun_stream$ )B_a_fun_b_a_fun_fun_stream$ )
(declare-fun st_ap$ (B_a_fun_stream$ B_stream$ )A_stream$ )
(declare-fun member$ (B$ B_set$ )Bool )
(declare-fun st_ap$a (B_b_fun_stream$ B_stream$ )B_stream$ )
(declare-fun st_ap$b (A_a_fun_stream$ A_stream$ )A_stream$ )
(declare-fun st_ap$c (B_a_fun_b_a_fun_fun_stream$ B_a_fun_stream$ )B_a_fun_stream$ )
(declare-fun st_ap$d (B_b_fun_b_b_fun_fun_stream$ B_b_fun_stream$ )B_b_fun_stream$ )
(declare-fun st_ap$e (A_b_fun_a_b_fun_fun_stream$ A_b_fun_stream$ )A_b_fun_stream$ )
(declare-fun st_ap$f (A_a_fun_a_a_fun_fun_stream$ A_a_fun_stream$ )A_a_fun_stream$ )
(declare-fun st_ap$g (B_b_a_fun_fun_b_b_a_fun_fun_fun_stream$ B_b_a_fun_fun_stream$ )B_b_a_fun_fun_stream$ )
(declare-fun st_ap$h (A_b_a_fun_fun_a_b_a_fun_fun_fun_stream$ A_b_a_fun_fun_stream$ )A_b_a_fun_fun_stream$ )
(declare-fun st_ap$i (A_b_b_fun_fun_a_b_b_fun_fun_fun_stream$ A_b_b_fun_fun_stream$ )A_b_b_fun_fun_stream$ )
(declare-fun st_ap$j (A_a_b_fun_fun_a_a_b_fun_fun_fun_stream$ A_a_b_fun_fun_stream$ )A_a_b_fun_fun_stream$ )
(declare-fun fun_app$ (B_a_fun_b_a_fun_fun$ B_a_fun$ )B_a_fun$ )
(declare-fun map_fun$ (B_b_fun$ )B_b_fun_b_b_fun_b_b_fun_fun_fun$ )
(declare-fun member$a (B_stream$ B_stream_set$ )Bool )
(declare-fun member$b (A$ A_set$ )Bool )
(declare-fun member$c (A_stream$ A_stream_set$ )Bool )
(declare-fun member$d (B_a_fun$ B_a_fun_set$ )Bool )
(declare-fun member$e (B_a_fun_stream$ B_a_fun_stream_set$ )Bool )
(declare-fun member$f (B_stream_stream$ B_stream_stream_set$ )Bool )
(declare-fun member$g (A_stream_stream$ A_stream_stream_set$ )Bool )
(declare-fun member$h (A_b_fun$ A_b_fun_set$ )Bool )
(declare-fun member$i (A_b_fun_stream$ A_b_fun_stream_set$ )Bool )
(declare-fun member$j (A_a_fun$ A_a_fun_set$ )Bool )
(declare-fun member$k (A_a_fun_stream$ A_a_fun_stream_set$ )Bool )
(declare-fun member$l (B_b_fun$ B_b_fun_set$ )Bool )
(declare-fun member$m (B_b_fun_stream$ B_b_fun_stream_set$ )Bool )
(declare-fun member$n (B_b_a_fun_fun$ B_b_a_fun_fun_set$ )Bool )
(declare-fun member$o (B_b_a_fun_fun_stream$ B_b_a_fun_fun_stream_set$ )Bool )
(declare-fun member$p (A_b_a_fun_fun$ A_b_a_fun_fun_set$ )Bool )
(declare-fun member$q (A_b_a_fun_fun_stream$ A_b_a_fun_fun_stream_set$ )Bool )
(declare-fun streams$ (B_set$ )B_stream_set$ )
(declare-fun fun_app$a (B_b_fun$ B$ )B$ )
(declare-fun fun_app$b (A_a_fun$ A$ )A$ )
(declare-fun fun_app$c (B_a_fun$ B$ )A$ )
(declare-fun fun_app$d (B_b_fun_b_b_fun_fun$ B_b_fun$ )B_b_fun$ )
(declare-fun fun_app$e (A_b_fun_a_b_fun_fun$ A_b_fun$ )A_b_fun$ )
(declare-fun fun_app$f (A_a_fun_a_a_fun_fun$ A_a_fun$ )A_a_fun$ )
(declare-fun fun_app$g (B_b_a_fun_fun_b_b_a_fun_fun_fun$ B_b_a_fun_fun$ )B_b_a_fun_fun$ )
(declare-fun fun_app$h (A_b_a_fun_fun_a_b_a_fun_fun_fun$ A_b_a_fun_fun$ )A_b_a_fun_fun$ )
(declare-fun fun_app$i (A_b_b_fun_fun_a_b_b_fun_fun_fun$ A_b_b_fun_fun$ )A_b_b_fun_fun$ )
(declare-fun fun_app$j (A_a_b_fun_fun_a_a_b_fun_fun_fun$ A_a_b_fun_fun$ )A_a_b_fun_fun$ )
(declare-fun fun_app$k (A_a_a_fun_fun_a_a_a_fun_fun_fun$ A_a_a_fun_fun$ )A_a_a_fun_fun$ )
(declare-fun fun_app$l (B_b_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun$ )B_b_fun_b_b_fun_fun$ )
(declare-fun fun_app$m (A_a_fun_b_a_fun_b_a_fun_fun_fun$ A_a_fun$ )B_a_fun_b_a_fun_fun$ )
(declare-fun fun_app$n (B_b_fun_a_b_fun_a_b_fun_fun_fun$ B_b_fun$ )A_b_fun_a_b_fun_fun$ )
(declare-fun fun_app$o (A_a_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun$ )A_a_fun_a_a_fun_fun$ )
(declare-fun fun_app$p (B_b_fun_b_a_fun_b_fun_b_a_fun_b_fun_fun_fun$ B_b_fun$ )B_a_fun_b_fun_b_a_fun_b_fun_fun$ )
(declare-fun fun_app$q (A_a_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ A_a_fun$ )B_a_fun_a_fun_b_a_fun_a_fun_fun$ )
(declare-fun fun_app$r (B_a_fun_b_a_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ B_a_fun_b_a_fun_fun$ )B_b_a_fun_fun_b_b_a_fun_fun_fun$ )
(declare-fun fun_app$s (B_a_fun_b_a_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ B_a_fun_b_a_fun_fun$ )A_b_a_fun_fun_a_b_a_fun_fun_fun$ )
(declare-fun fun_app$t (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun_fun$ B_a_fun_b_a_fun_fun$ )B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ )
(declare-fun fun_app$u (B_b_fun_b_b_fun_fun_b_b_b_fun_fun_b_b_b_fun_fun_fun_fun$ B_b_fun_b_b_fun_fun$ )B_b_b_fun_fun_b_b_b_fun_fun_fun$ )
(declare-fun fun_app$v (A_b_fun$ A$ )B$ )
(declare-fun fun_app$w (B_a_fun_b_fun$ B_a_fun$ )B$ )
(declare-fun fun_app$x (B_a_fun_a_fun$ B_a_fun$ )A$ )
(declare-fun fun_app$y (B_b_a_fun_fun$ B$ )B_a_fun$ )
(declare-fun fun_app$z (A_b_a_fun_fun$ A$ )B_a_fun$ )
(declare-fun map_fun$a (B_b_fun$ )A_a_fun_b_a_fun_b_a_fun_fun_fun$ )
(declare-fun map_fun$b (A_a_fun$ )B_b_fun_a_b_fun_a_b_fun_fun_fun$ )
(declare-fun map_fun$c (A_a_fun$ )A_a_fun_a_a_fun_a_a_fun_fun_fun$ )
(declare-fun map_fun$d (B_a_fun_b_a_fun_fun$ )B_b_fun_b_a_fun_b_fun_b_a_fun_b_fun_fun_fun$ )
(declare-fun map_fun$e (B_a_fun_b_a_fun_fun$ )A_a_fun_b_a_fun_a_fun_b_a_fun_a_fun_fun_fun$ )
(declare-fun map_fun$f (B_b_fun$ )B_a_fun_b_a_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ )
(declare-fun map_fun$g (A_a_fun$ )B_a_fun_b_a_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ )
(declare-fun map_fun$h (B_a_fun_b_a_fun_fun$ )B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun_fun$ )
(declare-fun map_fun$i (B_b_fun$ )B_b_fun_b_b_fun_fun_b_b_b_fun_fun_b_b_b_fun_fun_fun_fun$ )
(declare-fun map_tree$ (B_b_a_fun_fun_b_b_a_fun_fun_fun$ )B_b_a_fun_fun_tree_b_b_a_fun_fun_tree_fun$ )
(declare-fun siterate$ (B_a_fun_b_a_fun_fun$ B_a_fun$ )B_a_fun_stream$ )
(declare-fun streams$a (A_set$ )A_stream_set$ )
(declare-fun streams$b (B_a_fun_set$ )B_a_fun_stream_set$ )
(declare-fun streams$c (B_stream_set$ )B_stream_stream_set$ )
(declare-fun streams$d (A_stream_set$ )A_stream_stream_set$ )
(declare-fun streams$e (A_b_fun_set$ )A_b_fun_stream_set$ )
(declare-fun streams$f (A_a_fun_set$ )A_a_fun_stream_set$ )
(declare-fun streams$g (B_b_fun_set$ )B_b_fun_stream_set$ )
(declare-fun streams$h (B_b_a_fun_fun_set$ )B_b_a_fun_fun_stream_set$ )
(declare-fun streams$i (A_b_a_fun_fun_set$ )A_b_a_fun_fun_stream_set$ )
(declare-fun fun_app$aa (A_b_fun_b_fun$ A_b_fun$ )B$ )
(declare-fun fun_app$ab (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun$ )B_a_fun_b_a_fun_fun$ )
(declare-fun fun_app$ac (B_b_a_fun_fun_tree_b_b_a_fun_fun_tree_fun$ B_b_a_fun_fun_tree$ )B_b_a_fun_fun_tree$ )
(declare-fun fun_app$ad (B_b_fun_tree_b_b_fun_tree_fun$ B_b_fun_tree$ )B_b_fun_tree$ )
(declare-fun fun_app$ae (A_b_a_fun_fun_tree_a_b_a_fun_fun_tree_fun$ A_b_a_fun_fun_tree$ )A_b_a_fun_fun_tree$ )
(declare-fun fun_app$af (A_b_fun_tree_a_b_fun_tree_fun$ A_b_fun_tree$ )A_b_fun_tree$ )
(declare-fun fun_app$ag (A_a_fun_tree_a_a_fun_tree_fun$ A_a_fun_tree$ )A_a_fun_tree$ )
(declare-fun fun_app$ah (B_a_fun_tree_b_a_fun_tree_fun$ B_a_fun_tree$ )B_a_fun_tree$ )
(declare-fun fun_app$ai (B_tree_b_tree_fun$ B_tree$ )B_tree$ )
(declare-fun fun_app$aj (A_tree_a_tree_fun$ A_tree$ )A_tree$ )
(declare-fun map_tree$a (B_b_fun_b_b_fun_fun$ )B_b_fun_tree_b_b_fun_tree_fun$ )
(declare-fun map_tree$b (A_b_a_fun_fun_a_b_a_fun_fun_fun$ )A_b_a_fun_fun_tree_a_b_a_fun_fun_tree_fun$ )
(declare-fun map_tree$c (A_b_fun_a_b_fun_fun$ )A_b_fun_tree_a_b_fun_tree_fun$ )
(declare-fun map_tree$d (A_a_fun_a_a_fun_fun$ )A_a_fun_tree_a_a_fun_tree_fun$ )
(declare-fun map_tree$e (B_a_fun_b_a_fun_fun$ )B_a_fun_tree_b_a_fun_tree_fun$ )
(declare-fun map_tree$f (B_b_fun$ )B_tree_b_tree_fun$ )
(declare-fun map_tree$g (A_a_fun$ )A_tree_a_tree_fun$ )
(declare-fun siterate$a (B_b_fun$ B$ )B_stream$ )
(declare-fun siterate$b (A_a_fun$ A$ )A_stream$ )
(declare-fun siterate$c (B_b_fun_b_b_fun_fun$ B_b_fun$ )B_b_fun_stream$ )
(declare-fun siterate$d (A_a_fun_a_a_fun_fun$ A_a_fun$ )A_a_fun_stream$ )
(declare-fun siterate$e (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun$ )B_a_fun_b_a_fun_fun_stream$ )
(declare-fun siterate$f (B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun_b_b_fun_fun$ )B_b_fun_b_b_fun_fun_stream$ )
(declare-fun siterate$g (A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$ A_b_fun_a_b_fun_fun$ )A_b_fun_a_b_fun_fun_stream$ )
(declare-fun siterate$h (A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun$ )A_a_fun_a_a_fun_fun_stream$ )
(declare-fun siterate$i (B_b_a_fun_fun_b_b_a_fun_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ B_b_a_fun_fun_b_b_a_fun_fun_fun$ )B_b_a_fun_fun_b_b_a_fun_fun_fun_stream$ )
(declare-fun siterate$j (A_b_a_fun_fun_a_b_a_fun_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ A_b_a_fun_fun_a_b_a_fun_fun_fun$ )A_b_a_fun_fun_a_b_a_fun_fun_fun_stream$ )
(declare-fun siterate$k (A_b_b_fun_fun_a_b_b_fun_fun_fun_a_b_b_fun_fun_a_b_b_fun_fun_fun_fun$ A_b_b_fun_fun_a_b_b_fun_fun_fun$ )A_b_b_fun_fun_a_b_b_fun_fun_fun_stream$ )
(declare-fun siterate$l (A_a_b_fun_fun_a_a_b_fun_fun_fun_a_a_b_fun_fun_a_a_b_fun_fun_fun_fun$ A_a_b_fun_fun_a_a_b_fun_fun_fun$ )A_a_b_fun_fun_a_a_b_fun_fun_fun_stream$ )
(declare-fun siterate$m (B_stream_b_stream_fun$ B_stream$ )B_stream_stream$ )
(declare-fun siterate$n (A_stream_a_stream_fun$ A_stream$ )A_stream_stream$ )
(declare-fun siterate$o (A_b_fun_a_b_fun_fun$ A_b_fun$ )A_b_fun_stream$ )
(declare-fun siterate$p (B_b_a_fun_fun_b_b_a_fun_fun_fun$ B_b_a_fun_fun$ )B_b_a_fun_fun_stream$ )
(declare-fun siterate$q (A_b_a_fun_fun_a_b_a_fun_fun_fun$ A_b_a_fun_fun$ )A_b_a_fun_fun_stream$ )
(declare-fun iso_tuple_update_accessor_eq_assist$ (A_a_b_fun_fun_a_a_b_fun_fun_fun_a_a_b_fun_fun_a_a_b_fun_fun_fun_fun$ A_a_b_fun_fun_a_a_b_fun_fun_fun$ A_a_b_fun_fun$ A_a_b_fun_fun_a_a_b_fun_fun_fun$ A_a_b_fun_fun$ A_a_b_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$a (A_a_a_fun_fun_a_a_a_fun_fun_fun_a_a_a_fun_fun_a_a_a_fun_fun_fun_fun$ A_a_a_fun_fun_a_a_a_fun_fun_fun$ A_a_a_fun_fun$ A_a_a_fun_fun_a_a_a_fun_fun_fun$ A_a_a_fun_fun$ A_a_a_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$b (B_b_a_fun_fun_b_b_a_fun_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ B_b_a_fun_fun_b_b_a_fun_fun_fun$ B_b_a_fun_fun$ B_b_a_fun_fun_b_b_a_fun_fun_fun$ B_b_a_fun_fun$ B_b_a_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$c (B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun_b_b_fun_fun$ B_b_fun$ B_b_fun_b_b_fun_fun$ B_b_fun$ B_b_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$d (A_b_a_fun_fun_a_b_a_fun_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ A_b_a_fun_fun_a_b_a_fun_fun_fun$ A_b_a_fun_fun$ A_b_a_fun_fun_a_b_a_fun_fun_fun$ A_b_a_fun_fun$ A_b_a_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$e (A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$ A_b_fun_a_b_fun_fun$ A_b_fun$ A_b_fun_a_b_fun_fun$ A_b_fun$ A_b_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$f (A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun$ A_a_fun$ A_a_fun_a_a_fun_fun$ A_a_fun$ A_a_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$g (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun$ B_a_fun$ B_a_fun_b_a_fun_fun$ B_a_fun$ B_a_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$h (B_b_fun_b_b_fun_fun$ B_b_fun$ B$ B_b_fun$ B$ B$ )Bool )
(declare-fun iso_tuple_update_accessor_eq_assist$i (A_a_fun_a_a_fun_fun$ A_a_fun$ A$ A_a_fun$ A$ A$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$ (B_b_a_fun_fun_b_b_a_fun_fun_fun_b_b_a_fun_fun_b_b_a_fun_fun_fun_fun$ B_b_a_fun_fun_b_b_a_fun_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$a (B_b_fun_b_b_fun_fun_b_b_fun_b_b_fun_fun_fun$ B_b_fun_b_b_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$b (A_b_a_fun_fun_a_b_a_fun_fun_fun_a_b_a_fun_fun_a_b_a_fun_fun_fun_fun$ A_b_a_fun_fun_a_b_a_fun_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$c (A_b_fun_a_b_fun_fun_a_b_fun_a_b_fun_fun_fun$ A_b_fun_a_b_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$d (A_a_fun_a_a_fun_fun_a_a_fun_a_a_fun_fun_fun$ A_a_fun_a_a_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$e (B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ B_a_fun_b_a_fun_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$f (B_b_fun_b_b_fun_fun$ B_b_fun$ )Bool )
(declare-fun iso_tuple_update_accessor_cong_assist$g (A_a_fun_a_a_fun_fun$ A_a_fun$ )Bool )
(assert (! (forall ((?v0 B_a_fun$ ))(! (= (fun_app$ uub$ ?v0 )?v0 ):pattern ((fun_app$ uub$ ?v0 )))):named a0 ))
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$a uua$ ?v0 )?v0 ):pattern ((fun_app$a uua$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$b uu$ ?v0 )?v0 ):pattern ((fun_app$b uu$ ?v0 )))):named a2 ))
(assert (! (not (= (st_ap$ (siterate$ id$ f$ )(siterate$a id$a x$ ))(siterate$b id$b (fun_app$c f$ x$ )))):named a3 ))
(assert (! (forall ((?v0 B_stream$ ))(= (st_ap$a (siterate$c id$c id$a )?v0 )?v0 )):named a4 ))
(assert (! (forall ((?v0 A_stream$ ))(= (st_ap$b (siterate$d id$d id$b )?v0 )?v0 )):named a5 ))
(assert (! (forall ((?v0 B_a_fun_stream$ ))(= (st_ap$c (siterate$e id$e id$ )?v0 )?v0 )):named a6 ))
(assert (! (forall ((?v0 B_b_fun_stream$ ))(= (st_ap$d (siterate$f id$f id$c )?v0 )?v0 )):named a7 ))
(assert (! (forall ((?v0 A_b_fun_stream$ ))(= (st_ap$e (siterate$g id$g id$h )?v0 )?v0 )):named a8 ))
(assert (! (forall ((?v0 A_a_fun_stream$ ))(= (st_ap$f (siterate$h id$i id$d )?v0 )?v0 )):named a9 ))
(assert (! (forall ((?v0 B_b_a_fun_fun_stream$ ))(= (st_ap$g (siterate$i id$j id$k )?v0 )?v0 )):named a10 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_stream$ ))(= (st_ap$h (siterate$j id$l id$m )?v0 )?v0 )):named a11 ))
(assert (! (forall ((?v0 A_b_b_fun_fun_stream$ ))(= (st_ap$i (siterate$k id$n id$o )?v0 )?v0 )):named a12 ))
(assert (! (forall ((?v0 A_a_b_fun_fun_stream$ ))(= (st_ap$j (siterate$l id$p id$q )?v0 )?v0 )):named a13 ))
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$a id$a ?v0 )?v0 ):pattern ((fun_app$a id$a ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$b id$b ?v0 )?v0 ):pattern ((fun_app$b id$b ?v0 )))):named a15 ))
(assert (! (forall ((?v0 B_a_fun$ ))(! (= (fun_app$ id$ ?v0 )?v0 ):pattern ((fun_app$ id$ ?v0 )))):named a16 ))
(assert (! (forall ((?v0 B_b_fun$ ))(! (= (fun_app$d id$c ?v0 )?v0 ):pattern ((fun_app$d id$c ?v0 )))):named a17 ))
(assert (! (forall ((?v0 A_b_fun$ ))(! (= (fun_app$e id$h ?v0 )?v0 ):pattern ((fun_app$e id$h ?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_a_fun$ ))(! (= (fun_app$f id$d ?v0 )?v0 ):pattern ((fun_app$f id$d ?v0 )))):named a19 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ ))(! (= (fun_app$g id$k ?v0 )?v0 ):pattern ((fun_app$g id$k ?v0 )))):named a20 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ ))(! (= (fun_app$h id$m ?v0 )?v0 ):pattern ((fun_app$h id$m ?v0 )))):named a21 ))
(assert (! (forall ((?v0 A_b_b_fun_fun$ ))(! (= (fun_app$i id$o ?v0 )?v0 ):pattern ((fun_app$i id$o ?v0 )))):named a22 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ ))(! (= (fun_app$j id$q ?v0 )?v0 ):pattern ((fun_app$j id$q ?v0 )))):named a23 ))
(assert (! (forall ((?v0 B$ ))(! (= (fun_app$a id$a ?v0 )?v0 ):pattern ((fun_app$a id$a ?v0 )))):named a24 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$b id$b ?v0 )?v0 ):pattern ((fun_app$b id$b ?v0 )))):named a25 ))
(assert (! (forall ((?v0 B_a_fun$ ))(! (= (fun_app$ id$ ?v0 )?v0 ):pattern ((fun_app$ id$ ?v0 )))):named a26 ))
(assert (! (forall ((?v0 B_b_fun$ ))(! (= (fun_app$d id$c ?v0 )?v0 ):pattern ((fun_app$d id$c ?v0 )))):named a27 ))
(assert (! (forall ((?v0 A_b_fun$ ))(! (= (fun_app$e id$h ?v0 )?v0 ):pattern ((fun_app$e id$h ?v0 )))):named a28 ))
(assert (! (forall ((?v0 A_a_fun$ ))(! (= (fun_app$f id$d ?v0 )?v0 ):pattern ((fun_app$f id$d ?v0 )))):named a29 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ ))(! (= (fun_app$g id$k ?v0 )?v0 ):pattern ((fun_app$g id$k ?v0 )))):named a30 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ ))(! (= (fun_app$h id$m ?v0 )?v0 ):pattern ((fun_app$h id$m ?v0 )))):named a31 ))
(assert (! (forall ((?v0 A_b_b_fun_fun$ ))(! (= (fun_app$i id$o ?v0 )?v0 ):pattern ((fun_app$i id$o ?v0 )))):named a32 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ ))(! (= (fun_app$j id$q ?v0 )?v0 ):pattern ((fun_app$j id$q ?v0 )))):named a33 ))
(assert (! (forall ((?v0 A_a_b_fun_fun$ )(?v1 A_a_b_fun_fun_a_a_b_fun_fun_fun$ )(?v2 A_a_b_fun_fun$ ))(=> (= ?v0 (fun_app$j ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$ id$p id$q ?v2 ?v1 ?v0 ?v2 ))):named a34 ))
(assert (! (forall ((?v0 A_a_a_fun_fun$ )(?v1 A_a_a_fun_fun_a_a_a_fun_fun_fun$ )(?v2 A_a_a_fun_fun$ ))(=> (= ?v0 (fun_app$k ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$a id$r id$s ?v2 ?v1 ?v0 ?v2 ))):named a35 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_b_a_fun_fun_b_b_a_fun_fun_fun$ )(?v2 B_b_a_fun_fun$ ))(=> (= ?v0 (fun_app$g ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$b id$j id$k ?v2 ?v1 ?v0 ?v2 ))):named a36 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_b_b_fun_fun$ )(?v2 B_b_fun$ ))(=> (= ?v0 (fun_app$d ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$c id$f id$c ?v2 ?v1 ?v0 ?v2 ))):named a37 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_a_b_a_fun_fun_fun$ )(?v2 A_b_a_fun_fun$ ))(=> (= ?v0 (fun_app$h ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$d id$l id$m ?v2 ?v1 ?v0 ?v2 ))):named a38 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_a_b_fun_fun$ )(?v2 A_b_fun$ ))(=> (= ?v0 (fun_app$e ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$e id$g id$h ?v2 ?v1 ?v0 ?v2 ))):named a39 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_a_a_fun_fun$ )(?v2 A_a_fun$ ))(=> (= ?v0 (fun_app$f ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$f id$i id$d ?v2 ?v1 ?v0 ?v2 ))):named a40 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_b_a_fun_fun$ )(?v2 B_a_fun$ ))(=> (= ?v0 (fun_app$ ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$g id$e id$ ?v2 ?v1 ?v0 ?v2 ))):named a41 ))
(assert (! (forall ((?v0 B$ )(?v1 B_b_fun$ )(?v2 B$ ))(=> (= ?v0 (fun_app$a ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$h id$c id$a ?v2 ?v1 ?v0 ?v2 ))):named a42 ))
(assert (! (forall ((?v0 A$ )(?v1 A_a_fun$ )(?v2 A$ ))(=> (= ?v0 (fun_app$b ?v1 ?v2 ))(iso_tuple_update_accessor_eq_assist$i id$d id$b ?v2 ?v1 ?v0 ?v2 ))):named a43 ))
(assert (! (iso_tuple_update_accessor_cong_assist$ id$j id$k ):named a44 ))
(assert (! (iso_tuple_update_accessor_cong_assist$a id$f id$c ):named a45 ))
(assert (! (iso_tuple_update_accessor_cong_assist$b id$l id$m ):named a46 ))
(assert (! (iso_tuple_update_accessor_cong_assist$c id$g id$h ):named a47 ))
(assert (! (iso_tuple_update_accessor_cong_assist$d id$i id$d ):named a48 ))
(assert (! (iso_tuple_update_accessor_cong_assist$e id$e id$ ):named a49 ))
(assert (! (iso_tuple_update_accessor_cong_assist$f id$c id$a ):named a50 ))
(assert (! (iso_tuple_update_accessor_cong_assist$g id$d id$b ):named a51 ))
(assert (! (forall ((?v0 A_stream$ ))(= (st_ap$b (siterate$d id$d uu$ )?v0 )?v0 )):named a52 ))
(assert (! (forall ((?v0 B_stream$ ))(= (st_ap$a (siterate$c id$c uua$ )?v0 )?v0 )):named a53 ))
(assert (! (forall ((?v0 B_a_fun_stream$ ))(= (st_ap$c (siterate$e id$e uub$ )?v0 )?v0 )):named a54 ))
(assert (! (= (fun_app$l (map_fun$ id$a )id$a )id$c ):named a55 ))
(assert (! (= (fun_app$m (map_fun$a id$a )id$b )id$ ):named a56 ))
(assert (! (= (fun_app$n (map_fun$b id$b )id$a )id$h ):named a57 ))
(assert (! (= (fun_app$o (map_fun$c id$b )id$b )id$d ):named a58 ))
(assert (! (= (fun_app$p (map_fun$d id$ )id$a )id$t ):named a59 ))
(assert (! (= (fun_app$q (map_fun$e id$ )id$b )id$u ):named a60 ))
(assert (! (= (fun_app$r (map_fun$f id$a )id$ )id$k ):named a61 ))
(assert (! (= (fun_app$s (map_fun$g id$b )id$ )id$m ):named a62 ))
(assert (! (= (fun_app$t (map_fun$h id$ )id$ )id$e ):named a63 ))
(assert (! (= (fun_app$u (map_fun$i id$a )id$c )id$v ):named a64 ))
(assert (! (forall ((?v0 B$ )(?v1 B_set$ ))(=> (member$ ?v0 ?v1 )(member$a (siterate$a id$a ?v0 )(streams$ ?v1 )))):named a65 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ ))(=> (member$b ?v0 ?v1 )(member$c (siterate$b id$b ?v0 )(streams$a ?v1 )))):named a66 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B_a_fun_set$ ))(=> (member$d ?v0 ?v1 )(member$e (siterate$ id$ ?v0 )(streams$b ?v1 )))):named a67 ))
(assert (! (forall ((?v0 B_stream$ )(?v1 B_stream_set$ ))(=> (member$a ?v0 ?v1 )(member$f (siterate$m id$w ?v0 )(streams$c ?v1 )))):named a68 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream_set$ ))(=> (member$c ?v0 ?v1 )(member$g (siterate$n id$x ?v0 )(streams$d ?v1 )))):named a69 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A_b_fun_set$ ))(=> (member$h ?v0 ?v1 )(member$i (siterate$o id$h ?v0 )(streams$e ?v1 )))):named a70 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun_set$ ))(=> (member$j ?v0 ?v1 )(member$k (siterate$d id$d ?v0 )(streams$f ?v1 )))):named a71 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun_set$ ))(=> (member$l ?v0 ?v1 )(member$m (siterate$c id$c ?v0 )(streams$g ?v1 )))):named a72 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B_b_a_fun_fun_set$ ))(=> (member$n ?v0 ?v1 )(member$o (siterate$p id$k ?v0 )(streams$h ?v1 )))):named a73 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A_b_a_fun_fun_set$ ))(=> (member$p ?v0 ?v1 )(member$q (siterate$q id$m ?v0 )(streams$i ?v1 )))):named a74 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(= (smap$ ?v0 (siterate$a id$a ?v1 ))(siterate$a id$a (fun_app$a ?v0 ?v1 )))):named a75 ))
(assert (! (forall ((?v0 B_a_fun$ )(?v1 B$ ))(= (smap$a ?v0 (siterate$a id$a ?v1 ))(siterate$b id$b (fun_app$c ?v0 ?v1 )))):named a76 ))
(assert (! (forall ((?v0 A_b_fun$ )(?v1 A$ ))(= (smap$b ?v0 (siterate$b id$b ?v1 ))(siterate$a id$a (fun_app$v ?v0 ?v1 )))):named a77 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (smap$c ?v0 (siterate$b id$b ?v1 ))(siterate$b id$b (fun_app$b ?v0 ?v1 )))):named a78 ))
(assert (! (forall ((?v0 B_a_fun_b_fun$ )(?v1 B_a_fun$ ))(= (smap$d ?v0 (siterate$ id$ ?v1 ))(siterate$a id$a (fun_app$w ?v0 ?v1 )))):named a79 ))
(assert (! (forall ((?v0 B_a_fun_a_fun$ )(?v1 B_a_fun$ ))(= (smap$e ?v0 (siterate$ id$ ?v1 ))(siterate$b id$b (fun_app$x ?v0 ?v1 )))):named a80 ))
(assert (! (forall ((?v0 B_b_a_fun_fun$ )(?v1 B$ ))(= (smap$f ?v0 (siterate$a id$a ?v1 ))(siterate$ id$ (fun_app$y ?v0 ?v1 )))):named a81 ))
(assert (! (forall ((?v0 A_b_a_fun_fun$ )(?v1 A$ ))(= (smap$g ?v0 (siterate$b id$b ?v1 ))(siterate$ id$ (fun_app$z ?v0 ?v1 )))):named a82 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun$ ))(= (smap$h ?v0 (siterate$ id$ ?v1 ))(siterate$ id$ (fun_app$ ?v0 ?v1 )))):named a83 ))
(assert (! (forall ((?v0 A_b_fun_b_fun$ )(?v1 A_b_fun$ ))(= (smap$i ?v0 (siterate$o id$h ?v1 ))(siterate$a id$a (fun_app$aa ?v0 ?v1 )))):named a84 ))
(assert (! (= (comp$ id$ )id$k ):named a85 ))
(assert (! (= (comp$a id$ )id$m ):named a86 ))
(assert (! (= (comp$b id$a )id$c ):named a87 ))
(assert (! (= (comp$c id$a )id$h ):named a88 ))
(assert (! (= (comp$d id$b )id$d ):named a89 ))
(assert (! (= (comp$e id$b )id$ ):named a90 ))
(assert (! (forall ((?v0 A_a_fun_a_a_fun_fun$ )(?v1 A_a_fun$ ))(= (smap$j ?v0 (siterate$d ?v0 ?v1 ))(siterate$d ?v0 (fun_app$f ?v0 ?v1 )))):named a91 ))
(assert (! (forall ((?v0 B_b_fun_b_b_fun_fun$ )(?v1 B_b_fun$ ))(= (smap$k ?v0 (siterate$c ?v0 ?v1 ))(siterate$c ?v0 (fun_app$d ?v0 ?v1 )))):named a92 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun_b_a_fun_b_a_fun_fun_fun$ )(?v1 B_a_fun_b_a_fun_fun$ ))(= (smap$l ?v0 (siterate$e ?v0 ?v1 ))(siterate$e ?v0 (fun_app$ab ?v0 ?v1 )))):named a93 ))
(assert (! (forall ((?v0 B_a_fun_b_a_fun_fun$ )(?v1 B_a_fun$ ))(= (smap$h ?v0 (siterate$ ?v0 ?v1 ))(siterate$ ?v0 (fun_app$ ?v0 ?v1 )))):named a94 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B$ ))(= (smap$ ?v0 (siterate$a ?v0 ?v1 ))(siterate$a ?v0 (fun_app$a ?v0 ?v1 )))):named a95 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (smap$c ?v0 (siterate$b ?v0 ?v1 ))(siterate$b ?v0 (fun_app$b ?v0 ?v1 )))):named a96 ))
(assert (! (forall ((?v0 B_b_a_fun_fun_tree$ ))(= (fun_app$ac (map_tree$ id$k )?v0 )?v0 )):named a97 ))
(assert (! (forall ((?v0 B_b_fun_tree$ ))(= (fun_app$ad (map_tree$a id$c )?v0 )?v0 )):named a98 ))
(assert (! (forall ((?v0 A_b_a_fun_fun_tree$ ))(= (fun_app$ae (map_tree$b id$m )?v0 )?v0 )):named a99 ))
(assert (! (forall ((?v0 A_b_fun_tree$ ))(= (fun_app$af (map_tree$c id$h )?v0 )?v0 )):named a100 ))
(assert (! (forall ((?v0 A_a_fun_tree$ ))(= (fun_app$ag (map_tree$d id$d )?v0 )?v0 )):named a101 ))
(assert (! (forall ((?v0 B_a_fun_tree$ ))(= (fun_app$ah (map_tree$e id$ )?v0 )?v0 )):named a102 ))
(assert (! (forall ((?v0 B_tree$ ))(= (fun_app$ai (map_tree$f id$a )?v0 )?v0 )):named a103 ))
(assert (! (forall ((?v0 A_tree$ ))(= (fun_app$aj (map_tree$g id$b )?v0 )?v0 )):named a104 ))
(assert (! (= (map_tree$ id$k )id$y ):named a105 ))
(assert (! (= (map_tree$a id$c )id$z ):named a106 ))
(assert (! (= (map_tree$b id$m )id$aa ):named a107 ))
(assert (! (= (map_tree$c id$h )id$ab ):named a108 ))
(assert (! (= (map_tree$d id$d )id$ac ):named a109 ))
(assert (! (= (map_tree$e id$ )id$ad ):named a110 ))
(assert (! (= (map_tree$f id$a )id$ae ):named a111 ))
(assert (! (= (map_tree$g id$b )id$af ):named a112 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_a_fun$ )(?v2 B$ ))(! (= (fun_app$c (fun_app$ (comp$e ?v0 )?v1 )?v2 )(fun_app$b ?v0 (fun_app$c ?v1 ?v2 ))):pattern ((fun_app$c (fun_app$ (comp$e ?v0 )?v1 )?v2 )))):named a113 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 B_b_fun$ )(?v2 B_b_fun$ )(?v3 B$ ))(! (= (fun_app$a (fun_app$d (fun_app$l (map_fun$ ?v0 )?v1 )?v2 )?v3 )(fun_app$a ?v1 (fun_app$a ?v2 (fun_app$a ?v0 ?v3 )))):pattern ((fun_app$a (fun_app$d (fun_app$l (map_fun$ ?v0 )?v1 )?v2 )?v3 )))):named a114 ))
(assert (! (forall ((?v0 B_b_fun$ )(?v1 A_a_fun$ )(?v2 B_a_fun$ )(?v3 B$ ))(! (= (fun_app$c (fun_app$ (fun_app$m (map_fun$a ?v0 )?v1 )?v2 )?v3 )(fun_app$b ?v1 (fun_app$c ?v2 (fun_app$a ?v0 ?v3 )))):pattern ((fun_app$c (fun_app$ (fun_app$m (map_fun$a ?v0 )?v1 )?v2 )?v3 )))):named a115 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_a_fun_b_a_fun_fun$ )(?v2 A_b_a_fun_fun$ )(?v3 A$ ))(! (= (fun_app$z (fun_app$h (fun_app$s (map_fun$g ?v0 )?v1 )?v2 )?v3 )(fun_app$ ?v1 (fun_app$z ?v2 (fun_app$b ?v0 ?v3 )))):pattern ((fun_app$z (fun_app$h (fun_app$s (map_fun$g ?v0 )?v1 )?v2 )?v3 )))):named a116 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 B_b_fun$ )(?v2 A_b_fun$ )(?v3 A$ ))(! (= (fun_app$v (fun_app$e (fun_app$n (map_fun$b ?v0 )?v1 )?v2 )?v3 )(fun_app$a ?v1 (fun_app$v ?v2 (fun_app$b ?v0 ?v3 )))):pattern ((fun_app$v (fun_app$e (fun_app$n (map_fun$b ?v0 )?v1 )?v2 )?v3 )))):named a117 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_a_fun$ )(?v2 A_a_fun$ )(?v3 A$ ))(! (= (fun_app$b (fun_app$f (fun_app$o (map_fun$c ?v0 )?v1 )?v2 )?v3 )(fun_app$b ?v1 (fun_app$b ?v2 (fun_app$b ?v0 ?v3 )))):pattern ((fun_app$b (fun_app$f (fun_app$o (map_fun$c ?v0 )?v1 )?v2 )?v3 )))):named a118 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (fun_app$ (comp$e id$b )?v0 )?v0 )):named a119 ))
(assert (! (forall ((?v0 B_a_fun$ ))(= (fun_app$ (comp$e id$b )?v0 )?v0 )):named a120 ))
(check-sat )
;(get-unsat-core )
