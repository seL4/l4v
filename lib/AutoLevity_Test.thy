theory AutoLevity_Test
imports AutoLevity_Base AutoLevity_Hooks
begin
locale foo = fixes z assumes Z:"z" begin
ML \<open>Method.finish_text\<close>
lemma 
X:
"(z \<and> z) \<and> (z \<and> z)"
apply (insert mp) apply (insert conjE)
apply (rule conjI)
subgoal
  apply (rule 
conjI)
  by
(rule
Z)
(rule

Z)
subgoal apply (rule conjI)
  subgoal
    subgoal
      subgoal apply (insert impE) by (rule
Z)
      done
   done
   proof -
    show "z"
      apply 
(rule
 Z)
      done   
   qed
done

end

interpretation foo "True" by (unfold_locales;
simp)
        
  

end