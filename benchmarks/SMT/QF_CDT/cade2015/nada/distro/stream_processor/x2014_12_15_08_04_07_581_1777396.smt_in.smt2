;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort C$ 0 )
(declare-sort A_b_sp_nu$ 0 )
(declare-sort A_c_sp_nu$ 0 )
(declare-sort C_b_sp_nu$ 0 )
(declare-sort B_stream$ 0)
(declare-sort A_stream$ 0)
(declare-sort C_stream$ 0)
(declare-fun shd$ (B_stream$)B$)
(declare-fun stl$ (B_stream$)B_stream$)
(declare-fun sCons$ (B$ B_stream$ )B_stream$)
(declare-fun shd$a (A_stream$)A$)
(declare-fun stl$a (A_stream$)A_stream$)
(declare-fun sCons$a (A$ A_stream$ )A_stream$)
(declare-fun shd$b (C_stream$)C$)
(declare-fun stl$b (C_stream$)C_stream$)
(declare-fun sCons$b (C$ C_stream$ )C_stream$)
(declare-fun s$ ()A_stream$ )
(declare-fun sp$ ()C_b_sp_nu$ )
(declare-fun sp$a ()A_c_sp_nu$ )
(declare-fun run_nu$ (A_b_sp_nu$ A_stream$ )B_stream$ )
(declare-fun run_nu$a (C_b_sp_nu$ C_stream$ )B_stream$ )
(declare-fun run_nu$b (A_c_sp_nu$ A_stream$ )C_stream$ )
(declare-fun sp_nu_comp$ (C_b_sp_nu$ A_c_sp_nu$ )A_b_sp_nu$ )
(assert (! (not (= (run_nu$ (sp_nu_comp$ sp$ sp$a )s$ )(run_nu$a sp$ (run_nu$b sp$a s$ )))):named a0 ))
(check-sat )
;(get-unsat-core )
